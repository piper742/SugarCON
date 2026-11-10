#!/usr/bin/env python3

# SPDX-License-Identifier: GPL-3.0-or-later
"""
CON Sugar Transpiler – Final Corrected Open‑Source Edition
===========================================================
Syntactic sugar for EDuke32 CON scripting.

Features:
  - let / const local variables with automatic temporary reuse
  - algebraic expressions, arrays (1D/2D), compound assignments
  - state parameters, @return, @inline, @namespace decorators
  - abs (using ifl), min, max, clamp through user utilities
  - peephole optimizer: dead‑store elimination, empty‑brace -> nullop,
    constant mul/div by power‑of‑2 → shift
  - line‑number error reporting, warnings for temp pool usage
  - externs file support (auto‑generation & conflict avoidance)
  - per‑state temporary variable exclusion (no clobbering)
  - multi‑error collection: errors are gathered, processing continues
  - inlined states as pseudo macros allowing passing of strings (via
    ! parameter prefix) and variable amount of parameters (with ... syntax)
  - ranged case decleration expansion via ... syntax (eg. case 1 ... 10)
  - namespaced states (really namespaces the used temp variables)
    meant to resolve issues with onevent/appendevent hooks disrupting
    execution flow

Usage:
  # Transpile a file
  sugarcon input.scon -o output.con

  # Generate externs for a single file
  sugarcon --generate-externs input.scon -o input.ext

  # Utilize generated externs
  sugarcon --externs *.ext input.scon -o output.con
"""

import re, sys, argparse, os, bisect, hashlib
from typing import List, Dict, Set, Tuple

# ======================================================================
# Globals
# ======================================================================

# TODO: Bump these since the introduction of namespaces!
# Old values present here were tuned for back when we had
# only 2 pools to draw from!!!
GLOBAL_TEMP_COUNT = 128
ACTOR_TEMP_COUNT  = 128
CURRENT_LINE      = 0
ERROR_LIST        = []
WARNINGS_ENABLED  = True

KNOWN_STATES        = set()
RETURN_STATES       = set()
INLINE_STATES       = {}
EXTERN_TEMP_USAGE   = {}
EXTERN_PARAMS       = {}
EXTERN_SOURCES      = {}

DEFINES             = {}
LOCAL_DEFINES       = {}
LOCAL_INLINE_STATES = {}
LOCAL_RETURN_STATES = set()
LOCAL_ONLY_INLINE   = set()
LOCAL_ARRAYS        = {}

MAX_VARNAME = 25
MAX_NS_LEN = 16   # MAX_VARNAME - len("__ns_") - 1 - 3
HASH_LEN = 4          # 4 hex chars = 16-bit hash → collision-free for <~100 namespaces
STATE_NAMESPACE     = {}
NS_KIND             = {'global': 'global', 'actor': 'actor'}
EVENT_NAMESPACES = set()
POOLS               = {}

_CURRENT_NAMESPACE    = 'global'
_NS_ALIAS             = {}
_CURRENT_LET_EXCLUDED = {}
_TOTAL_TEMP_USAGE     = {}
_CALLS_FOR_EXT        = {}


def warn(msg):
    if WARNINGS_ENABLED:
        sys.stderr.write(f"Warning: {msg}\n")


def add_error(msg):
    ERROR_LIST.append(msg)


class SugarError(Exception):
    pass


def set_current_line(n):
    global CURRENT_LINE
    CURRENT_LINE = n


def get_current_line():
    return CURRENT_LINE


def report_error(msg):
    full_msg = f"Line {get_current_line()}: {msg}"
    add_error(full_msg)
    raise SugarError(full_msg)


def is_event_namespace(ns):
    return ns in EVENT_NAMESPACES


def shorten_namespace(name):
    if len(name) <= MAX_NS_LEN:
        return name
    h = hashlib.sha256(name.encode()).hexdigest()[:HASH_LEN]
    prefix = name[:MAX_NS_LEN - HASH_LEN - 1]
    return f"{prefix}{h}" # Removed _ because it was annoying me


def register_namespace(name, kind):
    if not name:
        report_error("Namespace name cannot be empty")
    if kind not in ('global', 'actor'):
        report_error(f"Namespace kind must be 'global' or 'actor', got '{kind}'")
    if name in ('global', 'actor') and kind != name:
        report_error(f"Built-in namespace '{name}' must have kind '{name}'")

    short = shorten_namespace(name)
    if short in NS_KIND and NS_KIND[short] != kind:
        report_error(f"Namespace '{name}' (shortened to '{short}') conflicts with "
                     f"existing namespace of kind '{NS_KIND[short]}'")
    NS_KIND[short] = kind
    if short != name:
        _NS_ALIAS[name] = short
        warn(f"Namespace '{name}' shortened to '{short}' "
             f"(EDuke32 MAXVARLABEL=26)")


def get_pool(namespace):
    short = _NS_ALIAS.get(namespace, namespace)
    if short not in POOLS:
        kind = NS_KIND.get(short, 'global')
        count = ACTOR_TEMP_COUNT if kind == 'actor' else GLOBAL_TEMP_COUNT
        POOLS[short] = TempPool(short, kind, count)
    return POOLS[short]


# ======================================================================
# Tokenizer & AST
# ======================================================================

class Token:
    __slots__ = ('type', 'value')
    def __init__(self, t, v):
        self.type, self.value = t, v


    def __repr__(self):
        return f"Token({self.type}:{self.value!r})"


def tokenize(s: str) -> List[Token]:
    toks = []
    pattern = re.compile(
        r'\s*(<<=|>>=|<<|>>|\+\+|--|[+\-*/%&|^]=?|[()\[\],=\.]|\d+|[a-zA-Z_]\w*)'
    )
    for m in pattern.finditer(s):
        v = m.group(1)
        if re.match(r'^\d+$', v):
            toks.append(Token('NUM', v))
        elif v in ('++', '--', '<<=', '>>=', '<<', '>>', '+=', '-=', '*=',
                   '/=', '%=', '&=', '|=', '^=', 'and', 'or', 'xor', '.'):
            toks.append(Token('SYM', v))
        elif v in '+-*/%&|^()[],=':
            toks.append(Token('SYM', v))
        else:
            toks.append(Token('ID', v))
    return toks


class Expr: pass
class Const(Expr):
    def __init__(self, v): self.val = v
class Var(Expr):
    def __init__(self, n): self.name = n
class ArrayRead(Expr):
    def __init__(self, a, idx): self.array, self.indices = a, idx
class RawArrayRead(Expr):
    def __init__(self, a, idx): self.array, self.index = a, idx
class FlattenExpr(Expr):
    def __init__(self, a, idx): self.array, self.indices = a, idx
class DimsExpr(Expr):
    def __init__(self, a): self.array = a
class DimSizeExpr(Expr):
    def __init__(self, a, idx): self.array, self.index = a, idx
class MemberAccess(Expr):
    def __init__(self, obj, member): self.obj, self.member = obj, member
class BinOp(Expr):
    def __init__(self, o, l, r): self.op, self.left, self.right = o, l, r
class Unary(Expr):
    def __init__(self, o, a): self.op, self.arg = o, a
class PreInc(Expr):
    def __init__(self, arg): self.arg = arg
class PostInc(Expr):
    def __init__(self, arg): self.arg = arg
class PreDec(Expr):
    def __init__(self, arg): self.arg = arg
class PostDec(Expr):
    def __init__(self, arg): self.arg = arg
class AbsExpr(Expr):
    def __init__(self, arg): self.arg = arg


def fold(node):
    if isinstance(node, Const):   return node
    if isinstance(node, Var):     return node
    if isinstance(node, MemberAccess): return node
    if isinstance(node, RawArrayRead):
        return RawArrayRead(node.array, fold(node.index))
    if isinstance(node, FlattenExpr):
        return FlattenExpr(node.array, [fold(i) for i in node.indices])
    if isinstance(node, DimsExpr):
        info = arrays.get(node.array)
        if info and (info.get('static') or len(info['dims']) == 1):
            return Const(len(info['dims']))
        return node
    if isinstance(node, DimSizeExpr):
        idx = fold(node.index)
        info = arrays.get(node.array)
        if info and isinstance(idx, Const):
            i = idx.val
            if info.get('static'):
                if 0 <= i < len(info['dims']):
                    return Const(info['dims'][i])
            elif len(info['dims']) == 1 and i == 0:
                return Const(info['size'])
        return DimSizeExpr(node.array, idx)
    if isinstance(node, ArrayRead):
        return ArrayRead(node.array, [fold(i) for i in node.indices])
    if isinstance(node, Unary) and node.op == '-':
        a = fold(node.arg)
        return Const(-a.val) if isinstance(a, Const) else Unary('-', a)
    if isinstance(node, BinOp):
        l, r = fold(node.left), fold(node.right)
        if isinstance(l, Const) and isinstance(r, Const):
            a, b = l.val, r.val
            try:
                if node.op in ('+', 'add'):     return Const(a + b)
                if node.op in ('-', 'sub'):     return Const(a - b)
                if node.op in ('*', 'mul'):     return Const(a * b)
                if node.op in ('/', 'div'):     return Const(a // b)
                if node.op in ('%', 'mod'):     return Const(a % b)
                if node.op in ('&', 'and'):     return Const(a & b)
                if node.op in ('|', 'or'):      return Const(a | b)
                if node.op in ('^', 'xor'):     return Const(a ^ b)
                if node.op in ('<<', 'shiftl'): return Const(a << b)
                if node.op in ('>>', 'shiftr'): return Const(a >> b)
            except Exception:
                pass
        return BinOp(node.op, l, r)
    return node


class Parser:
    def __init__(self, toks): self.tokens, self.pos = toks, 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else Token('EOF', '')

    def consume(self, t=None, v=None):
        tk = self.peek()
        if (t and tk.type != t) or (v and tk.value != v):
            raise SyntaxError(f"Expected {t or v}, got {tk}")
        self.pos += 1
        return tk

    def parse_expr(self): return self.parse_or()

    def parse_or(self):
        e = self.parse_xor()
        while self.peek().value in ('|', 'or'):
            op = self.consume().value; e = BinOp(op, e, self.parse_xor())
        return e

    def parse_xor(self):
        e = self.parse_and()
        while self.peek().value in ('^', 'xor'):
            op = self.consume().value; e = BinOp(op, e, self.parse_and())
        return e

    def parse_and(self):
        e = self.parse_shift()
        while self.peek().value in ('&', 'and'):
            op = self.consume().value; e = BinOp(op, e, self.parse_shift())
        return e

    def parse_shift(self):
        e = self.parse_add()
        while self.peek().value in ('<<', '>>'):
            op = self.consume().value; e = BinOp(op, e, self.parse_add())
        return e

    def parse_add(self):
        e = self.parse_mul()
        while self.peek().value in ('+', '-'):
            op = self.consume().value; e = BinOp(op, e, self.parse_mul())
        return e

    def parse_mul(self):
        e = self.parse_unary()
        while self.peek().value in ('*', '/', '%'):
            op = self.consume().value; e = BinOp(op, e, self.parse_unary())
        return e

    def parse_unary(self):
        if self.peek().value == '-':
            self.consume(); return Unary('-', self.parse_unary())
        if self.peek().value in ('++', '--'):
            op = self.consume().value
            arg = self.parse_unary()
            return PreInc(arg) if op == '++' else PreDec(arg)
        return self.parse_postfix()

    def parse_postfix(self):
        e = self.parse_primary()
        while self.peek().value in ('[', '.', '++', '--'):
            if self.peek().value == '[':
                self.consume(); idx = self.parse_expr(); self.consume('SYM', ']')
                if isinstance(e, Var):
                    e = ArrayRead(e.name, [idx])
                elif isinstance(e, ArrayRead):
                    e.indices.append(idx)
                else:
                    raise SyntaxError("Array access requires a variable")
            elif self.peek().value == '.':
                self.consume(); member = self.consume('ID').value
                e = MemberAccess(e, member)
            else:
                op = self.consume().value
                e = PostInc(e) if op == '++' else PostDec(e)
        return e

    def parse_primary(self):
        tk = self.peek()
        if tk.type == 'NUM':
            self.consume(); return Const(int(tk.value))
        if tk.type == 'ID':
            name = self.consume().value
            if name == 'abs' and self.peek().value == '(':
                self.consume(); arg = self.parse_expr(); self.consume('SYM', ')')
                return AbsExpr(arg)
            if name == 'flatten' and self.peek().value == '(':
                self.consume()
                arr_name = self.consume('ID').value
                indices = []
                while self.peek().value == ',':
                    self.consume(); indices.append(self.parse_expr())
                self.consume('SYM', ')')
                return FlattenExpr(arr_name, indices)
            if name == 'dims' and self.peek().value == '(':
                self.consume()
                arr_id = self.consume('ID').value
                self.consume('SYM', ')')
                return DimsExpr(arr_id)
            if name == 'dimsize' and self.peek().value == '(':
                self.consume()
                arr_id = self.consume('ID').value
                self.consume('SYM', ',')
                dim_idx = self.parse_expr()
                self.consume('SYM', ')')
                return DimSizeExpr(arr_id, dim_idx)
            if self.peek().value == '[':
                indices = []
                while self.peek().value == '[':
                    self.consume(); indices.append(self.parse_expr()); self.consume('SYM', ']')
                return ArrayRead(name, indices)
            return Var(name)
        if tk.value == '(':
            self.consume(); e = self.parse_expr(); self.consume('SYM', ')')
            return e
        raise SyntaxError(f"Unexpected {tk}")


# ======================================================================
# TempPool
# ======================================================================

class TempPool:
    def __init__(self, namespace, kind, count):
        self.namespace = namespace
        self.kind = kind
        self.max = count
        self.prefix = f"__ns_{namespace}"
        self.flag = 0 if kind == 'global' else 2
        self.free_ids = list(range(count))
        self.used = {}
        self.high = 0
        self.excluded = set()

    def reset(self):
        self.free_ids = list(range(self.max))
        self.used = {}
        self.high = 0
        self.excluded = set()

    def name_for(self, idx):
        return f"{self.prefix}_{idx}"

    def declare(self):
        return [f"var {self.prefix}_{i} 0 {self.flag}" for i in range(self.high)]

    def set_excluded(self, indices): self.excluded = set(indices)
    def clear_excluded(self): self.excluded.clear()

    def alloc(self):
        for i in range(len(self.free_ids)):
            idx = self.free_ids[i]
            if idx not in self.excluded:
                del self.free_ids[i]
                self.high = max(self.high, idx + 1)
                name = self.name_for(idx)
                if len(name) > MAX_VARNAME:
                    report_error(
                        f"Generated temp name '{name}' is {len(name)} characters; "
                        f"EDuke32 MAXVARLABEL=26 permits at most {MAX_VARNAME}. "
                        f"Shorten the namespace."
                    )
                self.used[name] = idx
                return name
        raise RuntimeError(f"Temporary pool '{self.namespace}' exhausted (max {self.max})")

    def free(self, name):
        if name not in self.used:
            raise RuntimeError(f"Double free of temporary {name}")
        idx = self.used.pop(name)
        bisect.insort(self.free_ids, idx)

    def reserve(self, count):
        out = []
        for _ in range(count): out.append(self.alloc())
        return out

    def release(self, names):
        for n in names: self.free(n)


# ======================================================================
# Arrays, types, defines
# ======================================================================

arrays = {}

TYPE_FLAGS = {
    'int32':   0,
    'int16':   16384,
    'int8':    32768,
    'uint32':  65536,
    'uint16':  16384 + 65536,
    'uint8':   32768 + 65536,
    'boolean': 1048576,
}

ALIAS = {
    'i32': 'int32', 'i16': 'int16', 'i8': 'int8',
    'u32': 'uint32', 'u16': 'uint16', 'u8': 'uint8', 'bool': 'boolean',
}


def resolve_type(t):
    return ALIAS.get(t, t)


def resolve_label(tok, visited=None):
    if visited is None:
        visited = set()
    tok = tok.strip()
    if not tok:
        return None
    try:
        return int(tok, 0)
    except ValueError:
        pass
    if tok in visited:
        return None
    visited.add(tok)
    if tok in DEFINES:
        val = DEFINES[tok].strip()
        try:
            return int(val, 0)
        except ValueError:
            return resolve_label(val, visited)
    return None


def _check_header_fits(arr, dims, flag):
    N = len(dims)
    if N <= 1: return
    is_unsigned = bool(flag & 0x10000)
    base = flag & ~0x10000
    if base == 1048576:   max_val = 1
    elif base == 32768:   max_val = 255 if is_unsigned else 127
    elif base == 16384:   max_val = 65535 if is_unsigned else 32767
    elif base == 0:       max_val = 0xFFFFFFFF if is_unsigned else 0x7FFFFFFF
    else:                 max_val = 0x7FFFFFFF
    if N > max_val:
        report_error(f"Array '{arr}': {N} dimensions exceeds header max {max_val}")
    for i, d in enumerate(dims):
        if d > max_val:
            report_error(
                f"Array '{arr}': dimension {i}={d} exceeds header max "
                f"{max_val} for this element type"
            )


# ======================================================================
# Code generator
# ======================================================================

op_map = {
    '+': 'add', '-': 'sub', '*': 'mul', '/': 'div', '%': 'mod',
    '&': 'and', '|': 'or',  '^': 'xor', 'and': 'and', 'or': 'or', 'xor': 'xor',
    '<<': 'shiftl', '>>': 'shiftr',
}


class CodeGen:
    def __init__(self, pool, var_map, consts=None):
        self.pool = pool
        self.var = var_map
        self.consts = consts if consts is not None else set()
        self.out = []
        self.used_temps = []
        self.const_cache = {}
        self.temp_values = {}
        self.cached_dims = {}

    def emit(self, s, indent=''): self.out.append(indent + s)

    def alloc(self):
        t = self.pool.alloc(); self.used_temps.append(t); return t

    def free(self, t):
        self.pool.free(t)
        if t in self.used_temps: self.used_temps.remove(t)
        self._invalidate(t)

    def release_all(self):
        for t in list(self.used_temps):
            try: self.pool.free(t)
            except Exception: pass
        self.used_temps.clear()
        self.const_cache.clear()
        self.temp_values.clear()

    def _record_const(self, temp, value):
        self.temp_values[temp] = value
        self.const_cache[value] = temp

    def _invalidate(self, temp):
        if temp in self.temp_values:
            old = self.temp_values.pop(temp)
            if old is not None and self.const_cache.get(old) == temp:
                del self.const_cache[old]

    def emit_set_const(self, target, value, indent=''):
        if self.temp_values.get(target) == value: return
        self._invalidate(target)
        if value in self.const_cache:
            src = self.const_cache[value]
            if target != src: self.emit(f"set {target} {src}", indent)
        else:
            self.emit(f"set {target} {value}", indent)
        self._record_const(target, value)

    def emit_op(self, op, target, src, indent=''):
        self._invalidate(target)
        self.emit(f"{op} {target} {src}", indent)

    def _check_var(self, name):
        if name.startswith('__ns_') and name not in self.var:
            report_error(f"Undefined temporary variable '{name}'")

    def index_name(self, flat):
        if isinstance(flat, Const): return str(flat.val)
        if isinstance(flat, Var):
            self._check_var(flat.name)
            return self.var.get(flat.name, flat.name)
        t = self.alloc(); self.gen_expr(flat, t); return t

    def gen_expr(self, node, target, indent=''):
        node = fold(node)
        if isinstance(node, Const):
            self.emit_set_const(target, node.val, indent)
        elif isinstance(node, Var):
            self._check_var(node.name)
            src = self.var.get(node.name, node.name)
            if target != src: self.emit(f"set {target} {src}", indent)
            self._invalidate(target)
        elif isinstance(node, MemberAccess):
            self.emit(f"set {target} {self._unparse(node)}", indent)
            self._invalidate(target)
        elif isinstance(node, RawArrayRead):
            idx = self.index_name(node.index)
            self.emit(f"set {target} {node.array}[{idx}]", indent)
            if not isinstance(node.index, (Const, Var)): self.free(idx)
        elif isinstance(node, FlattenExpr):
            flat = fold(self._flatten(node.array, node.indices))
            self.gen_expr(flat, target, indent)
        elif isinstance(node, DimsExpr):
            info = arrays.get(node.array)
            if not info: report_error(f"dims() on unknown array '{node.array}'")
            if info.get('static') or len(info['dims']) == 1:
                self.emit_set_const(target, len(info['dims']), indent)
            else:
                self.gen_expr(RawArrayRead(node.array, Const(0)), target, indent)
        elif isinstance(node, DimSizeExpr):
            info = arrays.get(node.array)
            if not info: report_error(f"dimsize() on unknown array '{node.array}'")
            N = len(info['dims'])
            idx_folded = fold(node.index)
            if info.get('static'):
                if not isinstance(idx_folded, Const):
                    report_error(f"dimsize() on static array '{node.array}' requires constant index")
                i = idx_folded.val
                if i < 0 or i >= N:
                    report_error(f"dimsize() index {i} out of range for '{node.array}'")
                self.emit_set_const(target, info['dims'][i], indent)
            elif N == 1:
                if isinstance(idx_folded, Const) and idx_folded.val != 0:
                    report_error(f"dimsize() index {idx_folded.val} out of range for 1D array '{node.array}'")
                warn(f"dimsize() on 1D dynamic array '{node.array}' returns declared size {info['size']}")
                self.emit_set_const(target, info['size'], indent)
            else:
                if isinstance(idx_folded, Const):
                    i = idx_folded.val
                    if i < 0 or i >= N:
                        report_error(f"dimsize() index {i} out of range for '{node.array}'")
                    if i == 0:
                        self.gen_expr(RawArrayRead(node.array, Const(1)), target, indent)
                    else:
                        cached = self.cached_dims.get(node.array)
                        if cached and (i - 1) < len(cached):
                            src = cached[i - 1]
                            if target != src: self.emit(f"set {target} {src}", indent)
                        else:
                            self.gen_expr(RawArrayRead(node.array, Const(i + 1)), target, indent)
                else:
                    offset = BinOp('+', node.index, Const(1))
                    self.gen_expr(RawArrayRead(node.array, offset), target, indent)
        elif isinstance(node, Unary) and node.op == '-':
            self.gen_expr(node.arg, target, indent)
            t = self.alloc()
            self.emit(f"set {t} {target}", indent)
            self.emit(f"set {target} 0", indent)
            self.emit_op('sub', target, t, indent)
            self.free(t)
        elif isinstance(node, PreInc):
            self._modify_var(node.arg, 1, indent); self.gen_expr(node.arg, target, indent)
        elif isinstance(node, PreDec):
            self._modify_var(node.arg, -1, indent); self.gen_expr(node.arg, target, indent)
        elif isinstance(node, PostInc):
            self.gen_expr(node.arg, target, indent); self._modify_var(node.arg, 1, indent)
        elif isinstance(node, PostDec):
            self.gen_expr(node.arg, target, indent); self._modify_var(node.arg, -1, indent)
        elif isinstance(node, AbsExpr):
            self.gen_expr(node.arg, target, indent)
            self.emit(f"abs {target}", indent)
        elif isinstance(node, BinOp):
            self.gen_expr(node.left, target, indent)
            self._emit_right(node.op, node.right, target, indent)
        elif isinstance(node, ArrayRead):
            flat = fold(self._flatten(node.array, node.indices))
            idx = self.index_name(flat)
            self.emit(f"set {target} {node.array}[{idx}]", indent)
            if not isinstance(flat, (Const, Var)): self.free(idx)
        else:
            raise NotImplementedError(f"Unknown expression {node}")

    def _modify_var(self, node, delta, indent):
        if isinstance(node, Var):
            self._check_var(node.name)
            name = self.var.get(node.name, node.name)
            if name in self.consts:
                report_error(f"Cannot modify constant '{node.name}'")
            self.emit(f"{'add' if delta == 1 else 'sub'} {name} 1", indent)
        elif isinstance(node, ArrayRead):
            flat = fold(self._flatten(node.array, node.indices))
            idx = self.index_name(flat)
            cur = self.alloc()
            self.emit(f"set {cur} {node.array}[{idx}]", indent)
            self.emit(f"{'add' if delta == 1 else 'sub'} {cur} 1", indent)
            self.emit(f"setarray {node.array}[{idx}] {cur}", indent)
            self.free(cur)
            if not isinstance(flat, (Const, Var)): self.free(idx)
        else:
            raise NotImplementedError("Can only increment/decrement variables or array elements")

    def _emit_right(self, op, right_node, target, indent=''):
        right = fold(right_node)
        if isinstance(right, Const):
            self.emit_op(op_map[op], target, str(right.val), indent)
        elif isinstance(right, (Var, MemberAccess)):
            if isinstance(right, Var): self._check_var(right.name)
            self.emit_op(op_map[op], target, self._unparse(right), indent)
        elif isinstance(right, RawArrayRead):
            if isinstance(right.index, Const):
                self.emit_op(op_map[op], target, f"{right.array}[{right.index.val}]", indent)
            elif isinstance(right.index, Var):
                self._check_var(right.index.name)
                src = self.var.get(right.index.name, right.index.name)
                self.emit_op(op_map[op], target, f"{right.array}[{src}]", indent)
            else:
                idx = self.alloc(); self.gen_expr(right.index, idx, indent)
                self.emit_op(op_map[op], target, f"{right.array}[{idx}]", indent)
                self.free(idx)
        elif isinstance(right, ArrayRead):
            flat = fold(self._flatten(right.array, right.indices))
            if isinstance(flat, Const):
                self.emit_op(op_map[op], target, f"{right.array}[{flat.val}]", indent)
            elif isinstance(flat, Var):
                src = self.var.get(flat.name, flat.name)
                self.emit_op(op_map[op], target, f"{right.array}[{src}]", indent)
            else:
                idx = self.alloc(); self.gen_expr(flat, idx, indent)
                self.emit_op(op_map[op], target, f"{right.array}[{idx}]", indent)
                self.free(idx)
        else:
            r = self.alloc(); self.gen_expr(right, r, indent)
            self.emit_op(op_map[op], target, r, indent)
            self.free(r)

    def _flatten(self, arr, idxs):
        info = arrays.get(arr)
        if not info:
            if len(idxs) == 1: return idxs[0]
            report_error(f"Unknown array '{arr}' used with {len(idxs)} indices")
        dims = info['dims']; N = len(dims)
        if N == 1:
            if len(idxs) != 1:
                raise SyntaxError(f"1D array '{arr}' requires 1 index, got {len(idxs)}")
            return idxs[0]
        if len(idxs) == 1:
            return idxs[0]
        if len(idxs) != N:
            raise SyntaxError(f"Array '{arr}' expects {N} indices, got {len(idxs)}")
        if info.get('static'):
            e = idxs[0]
            for d, idx in zip(dims[1:], idxs[1:]):
                e = BinOp('+', BinOp('*', e, Const(d)), idx)
            return e
        cached = self.cached_dims.get(arr)
        if cached:
            e = idxs[0]
            for k in range(1, N):
                e = BinOp('+', BinOp('*', e, Var(cached[k - 1])), idxs[k])
            return BinOp('+', e, Const(N + 1))
        e = idxs[0]
        for k in range(1, N):
            e = BinOp('+', BinOp('*', e, RawArrayRead(arr, Const(k + 1))), idxs[k])
        return BinOp('+', e, Const(N + 1))

    def _unparse(self, node):
        if isinstance(node, Const): return str(node.val)
        if isinstance(node, Var):
            self._check_var(node.name)
            return self.var.get(node.name, node.name)
        if isinstance(node, MemberAccess):
            return f"{self._unparse(node.obj)}.{node.member}"
        if isinstance(node, RawArrayRead):
            return f"{node.array}[{self._unparse(node.index)}]"
        if isinstance(node, ArrayRead):
            idx = self._unparse(node.indices[0]) if node.indices else ''
            return f"{node.array}[{idx}]"
        if isinstance(node, (DimsExpr, DimSizeExpr, FlattenExpr)):
            raise NotImplementedError(f"Internal: {type(node).__name__} cannot be unparsed")
        return str(node)

    def write_array(self, arr, flat_idx, val, indent=''):
        flat = fold(flat_idx)
        idx_name = self.index_name(flat)
        if isinstance(val, Const): v = str(val.val)
        elif isinstance(val, (Var, MemberAccess)): v = self._unparse(val)
        else:
            v = self.alloc(); self.gen_expr(val, v, indent)
        self.emit(f"setarray {arr}[{idx_name}] {v}", indent)
        if not isinstance(flat, (Const, Var)): self.free(idx_name)
        if not isinstance(val, (Const, Var, MemberAccess)): self.free(v)


# ======================================================================
# Scope helpers
# ======================================================================

def brace_pairs(lines):
    pairs, stack = {}, []
    for i, ln in enumerate(lines):
        s = ln.strip()
        if s == '{': stack.append(i)
        elif s == '}':
            if stack: pairs[stack.pop()] = i
    return pairs


def scope_end(line, pairs, total):
    best = total - 1
    for o, c in pairs.items():
        if o < line < c and o > best: best = c
    return best


_lvalue_re = re.compile(r'^(\w+(?:\[[^\]]+\])*)\s*')


# ======================================================================
# Peephole optimizer
# ======================================================================

def peephole_optimize(lines):
    lines = list(lines); dead = set(); live = set()
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i].strip()
        if not line or line.startswith('//') or line.startswith('#'):
            continue
        uses = set(re.findall(r'\b(__ns_\w+)\b', line))
        m = re.match(r'^\s*(set|add|sub|mul|div|mod|and|or|xor|shiftl|shiftr)\s+(\w+)\s+(.+)', line)
        if m:
            target = m.group(2)
            if target.startswith('__ns_'):
                if target not in live: dead.add(i)
                else:
                    live.discard(target); live.update(uses)
            else:
                live.update(uses)
        else:
            live.update(uses)

    new_lines = []
    for idx, line in enumerate(lines):
        if idx in dead: continue
        stripped = line.strip()
        if re.match(r'^\{\s*\}\s*$', stripped):
            indent = line[:len(line) - len(stripped)]
            line = indent + 'nullop'
        m = re.match(r'^(\s*)(mul|div)\s+(\S+)\s+(\d+)\s*$', line)
        if m:
            indent, op, target, const_str = m.groups()
            const = int(const_str)
            if const > 0 and (const & (const - 1)) == 0:
                shift = const.bit_length() - 1
                line = (f"{indent}shiftl {target} {shift}" if op == 'mul'
                        else f"{indent}shiftr {target} {shift}")
        new_lines.append(line)
    return new_lines


# ======================================================================
# Text helpers
# ======================================================================

def strip_comment(line):
    if '//' in line: return line.split('//')[0].rstrip()
    return line


def line_without_comment(line): return strip_comment(line)


def extract_comment(line):
    if '//' in line: return '//' + line.split('//', 1)[1]
    return ''


def strip_block_comments(lines):
    out = []; in_block = False
    for line in lines:
        buf = []; i = 0
        while i < len(line):
            if in_block:
                j = line.find('*/', i)
                if j == -1: i = len(line)
                else: in_block = False; i = j + 2
            else:
                j = line.find('/*', i)
                if j == -1: buf.append(line[i:]); i = len(line)
                else: buf.append(line[i:j]); in_block = True; i = j + 2
        out.append(''.join(buf))
    return out


def strip_comments_for_scan(lines):
    for line in strip_block_comments(lines):
        yield strip_comment(line)


def is_raw_con_line(line):
    s = line_without_comment(line).strip()
    if not s: return True
    call_match = re.match(r'^(?:state\s+)?(\w+)\s*\(', s)
    if call_match and call_match.group(1) in KNOWN_STATES: return False
    if re.match(r'^(let|const|state|defstate|if|for|while|switch)', s): return False
    if '=' in s and re.match(_lvalue_re, s): return False
    if re.match(r'^(\w+(?:\[[^\]]+\])*)\s*(\+\+|--)$', s): return False
    if re.match(r'^(\+\+|--)\s*(\w+(?:\[[^\]]+\])*)$', s): return False
    if (s.startswith('zero(') or s.startswith('zero ') or
            re.match(r'^resize(2d|3d|Nd)\s*\(', s) or
            re.match(r'^abs\s*\(', s)):
        return False
    return True


# ======================================================================
# Argument helpers
# ======================================================================

def split_args_raw(args_str):
    if not args_str or not args_str.strip(): return []
    args, cur, depth = [], [], 0
    in_string, escape = False, False
    for ch in args_str:
        if escape: cur.append(ch); escape = False; continue
        if in_string and ch == '\\': cur.append(ch); escape = True; continue
        if ch == '"': in_string = not in_string; cur.append(ch); continue
        if in_string: cur.append(ch); continue
        if ch in '([': depth += 1
        elif ch in ')]': depth -= 1
        elif ch == ',' and depth == 0:
            args.append(''.join(cur).strip()); cur = []; continue
        cur.append(ch)
    if cur: args.append(''.join(cur).strip())
    return args


def substitute_variadic_and_strings(line, variadic_temps, string_params, count):
    for sname, sval in string_params.items():
        line = re.sub(r'!' + re.escape(sname) + r'!', lambda m, v=sval: '"' + v + '"', line)
        line = re.sub(r'!' + re.escape(sname) + r'(?![!\w])', lambda m, v=sval: v, line)
    if re.match(r'^\s*case\s+\S+\s+\.\.\.\s+\S+\s*(//.*)?$', line): return [line]
    stripped = line.strip()
    if (stripped.startswith('if') or stripped.startswith('switch')) and '...' in line:
        return [line.replace('...', str(count))]
    if ',,,' in line: line = line.replace(',,,', ', '.join(variadic_temps))
    if '...' in line: line = line.replace('...', ' '.join(variadic_temps))
    return [line]


# ======================================================================
# Array helpers
# ======================================================================

def emit_array_zero(arr, indent, code):
    info = arrays[arr]
    dims = info['dims']
    N = len(dims)

    if info.get('static'):
        # Static: dimensions are baked at transpile time and never change.
        code.emit(f"resizearray {arr} 0", indent)
        code.emit(f"resizearray {arr} {info['size']}", indent)
        return

    if N == 1:
        # Dynamic 1-D: no header; declared size is authoritative (updated by
        # resizeNd). Raw `resizearray` on 1-D does not update metadata —
        # documented limitation, already warned at the call site.
        code.emit(f"resizearray {arr} 0", indent)
        code.emit(f"resizearray {arr} {info['size']}", indent)
        return

    # Dynamic multi-D: derive total size from the runtime header.
    # hdr_t  = N + 1                (base offset / header size)
    # total_t = D0 * D1 * ... * D(N-1) + hdr_t
    hdr_t   = code.alloc()
    total_t = code.alloc()

    code.emit(f"set {hdr_t} {arr}[0]", indent)
    code.emit(f"add {hdr_t} 1", indent)

    code.emit(f"set {total_t} {arr}[1]", indent)
    for k in range(2, N + 1):
        code.emit(f"mul {total_t} {arr}[{k}]", indent)
    code.emit(f"add {total_t} {hdr_t}", indent)

    # Shrink to just the header (truncates data, preserves arr[0..N])
    code.emit(f"resizearray {arr} {hdr_t}", indent)
    # Regrow to current total (new slots zero-initialized by CON)
    code.emit(f"resizearray {arr} {total_t}", indent)

    code.free(hdr_t)
    code.free(total_t)


def emit_array_resize(arr, dim_names, dim_consts, indent, code):
    """dim_names: list of str (literals as strings, or temp names)
       dim_consts: parallel list of ints, or None for dynamic entries."""
    info = arrays[arr]
    if info.get('static'):
        report_error(f"Cannot resize static array '{arr}'")
    old_N = len(info['dims'])
    new_N = len(dim_names)
    if old_N != new_N:
        report_error(f"Cannot change dimensionality of '{arr}' from {old_N}D to {new_N}D")

    all_const = all(c is not None for c in dim_consts)

    if all_const and new_N > 1:
        _check_header_fits(arr, dim_consts, info['flag'])

    if new_N == 1:
        code.emit(f"resizearray {arr} 0", indent)
        code.emit(f"resizearray {arr} {dim_names[0]}", indent)
    else:
        if all_const:
            prod = 1
            for c in dim_consts: prod *= c
            total = (new_N + 1) + prod
            code.emit(f"resizearray {arr} 0", indent)
            code.emit(f"resizearray {arr} {total}", indent)
        else:
            prod_t = code.alloc()
            code.emit(f"set {prod_t} {dim_names[0]}", indent)
            for i in range(1, new_N):
                code.emit(f"mul {prod_t} {dim_names[i]}", indent)
            code.emit(f"add {prod_t} {new_N + 1}", indent)
            code.emit(f"resizearray {arr} 0", indent)
            code.emit(f"resizearray {arr} {prod_t}", indent)
            code.free(prod_t)
        code.emit(f"setarray {arr}[0] {new_N}", indent)
        for i, d in enumerate(dim_names):
            code.emit(f"setarray {arr}[{i+1}] {d}", indent)

    if all_const:
        data_size = 1
        for c in dim_consts: data_size *= c
        arrays[arr] = {'dims': dim_consts, 'size': data_size,
                       'flag': info['flag'], 'N': new_N}
    else:
        warn(f"resize on '{arr}' with non-constant dimensions; "
             f"transpiler metadata not updated for this array")


def _resolve_dim_or_eval(dim_str, code, indent):
    """Resolve a dimension string to one of:
       (str(const), int, None) — a compile-time constant
       (temp_name, None, temp_name) — an expression evaluated at runtime
    """
    r = resolve_label(dim_str)
    if r is not None:
        return str(r), r, None
    try:
        ast = fold(Parser(tokenize(dim_str)).parse_expr())
    except SyntaxError as e:
        report_error(f"Cannot parse dimension '{dim_str}': {e}")
    t = code.alloc()
    code.gen_expr(ast, t, indent)
    return t, None, t


def _handle_resize(s, indent, code, pool):
    """Handle resize2d / resize3d / resizeNd. Accepts literals, defines,
    and arbitrary expressions. Returns True if the line was handled."""
    for name, arity in (('resize2d', 2), ('resize3d', 3)):
        m = re.match(rf'^{name}\s*\((.*)\)\s*$', s)
        if m:
            parts = split_args_raw(m.group(1))
            if len(parts) != arity + 1:
                report_error(f"{name} requires exactly {arity} dimension argument(s), got {len(parts) - 1}")
            arr = parts[0].strip()
            if not re.fullmatch(r'[A-Za-z_]\w*', arr):
                report_error(f"{name}: first argument must be a bare array name")
            if arr not in arrays:
                return False
            dim_names, dim_consts, alloc_temps = [], [], []
            for d in parts[1:]:
                n, c, t = _resolve_dim_or_eval(d, code, indent)
                dim_names.append(n); dim_consts.append(c)
                if t: alloc_temps.append(t)
            emit_array_resize(arr, dim_names, dim_consts, indent, code)
            for t in alloc_temps: code.free(t)
            return True

    m = re.match(r'^resizeNd\s*\((.*)\)\s*$', s)
    if m:
        parts = split_args_raw(m.group(1))
        if len(parts) < 2:
            report_error("resizeNd requires an array name and at least one dimension")
        arr = parts[0].strip()
        if not re.fullmatch(r'[A-Za-z_]\w*', arr):
            report_error("resizeNd: first argument must be a bare array name")
        if arr not in arrays:
            return False
        dim_names, dim_consts, alloc_temps = [], [], []
        for d in parts[1:]:
            n, c, t = _resolve_dim_or_eval(d, code, indent)
            dim_names.append(n); dim_consts.append(c)
            if t: alloc_temps.append(t)
        emit_array_resize(arr, dim_names, dim_consts, indent, code)
        for t in alloc_temps: code.free(t)
        return True

    return False


def _state_resizes_array(body, arr_name, visited=None):
    if visited is None: visited = set()
    for bline in body:
        s = line_without_comment(bline).strip()
        if re.match(r'resizearray\s+' + re.escape(arr_name) + r'\b', s): return True
        if re.match(r'(resize2d|resize3d|resizeNd|zero)\s*\(\s*' + re.escape(arr_name) + r'\b', s): return True
        cm = re.match(r'^(?:state\s+)?(\w+)\s*\(', s)
        if cm:
            callee = cm.group(1)
            if callee in INLINE_STATES and callee not in visited:
                visited.add(callee)
                _, ibody, _, _ = INLINE_STATES[callee]
                if _state_resizes_array(ibody, arr_name, visited): return True
    return False


def _prescan_arrays(lines):
    """Register array declarations before call-graph building so that
    process_state's array accesses resolve correctly. Does NOT emit output."""
    i = 0
    in_block = False
    while i < len(lines):
        line = lines[i].rstrip('\n')
        s = line_without_comment(line).strip()
        if in_block:
            if '*/' in line: in_block = False
            i += 1; continue
        if '/*' in line:
            in_block = True; i += 1; continue
        if not s or s.startswith('//') or s.startswith('#'):
            i += 1; continue

        sm = re.match(r'^(static_array|static_gamearray)\s+(.+)$', s)
        if sm:
            rest = sm.group(2).strip()
            modern = re.match(r'^(\w+)\s+(\w+)\s*((?:\[\w+\])+)$', rest)
            if modern:
                type_raw, arr_name = modern.group(1), modern.group(2)
                canonical = resolve_type(type_raw)
                if canonical in TYPE_FLAGS:
                    flag = TYPE_FLAGS[canonical]
                    raw_dims = re.findall(r'\[(\w+)\]', modern.group(3))
                    dims = []
                    for d in raw_dims:
                        if d.isdigit(): dims.append(int(d))
                        else:
                            r = resolve_label(d)
                            if r is not None: dims.append(r)
                    if len(dims) == len(raw_dims):
                        total = 1
                        for d in dims: total *= d
                        N = len(dims)
                        arrays[arr_name] = {'dims': dims, 'size': total,
                                            'flag': flag, 'N': N, 'static': True}
                        LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
                i += 1; continue
            parts = rest.split()
            if len(parts) >= 3:
                arr_name = parts[0]
                try: flag = int(parts[-1])
                except ValueError:
                    r = resolve_label(parts[-1]); flag = r if r is not None else 0
                dims = []
                for tok in parts[1:-1]:
                    if tok.isdigit(): dims.append(int(tok))
                    else:
                        r = resolve_label(tok)
                        if r is not None: dims.append(r)
                if len(dims) == len(parts) - 2:
                    total = 1
                    for d in dims: total *= d
                    N = len(dims)
                    arrays[arr_name] = {'dims': dims, 'size': total,
                                        'flag': flag, 'N': N, 'static': True}
                    LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
            i += 1; continue

        tm = re.match(r'^(\w+)\s+', s)
        if tm and resolve_type(tm.group(1)) in TYPE_FLAGS:
            canon = resolve_type(tm.group(1))
            rest = s[tm.end():].strip()
            m2 = re.match(r'(\w+)\s*((?:\[\w+\])+)', rest)
            if m2:
                nm = m2.group(1)
                raw_dims = re.findall(r'\[(\w+)\]', m2.group(2))
                dims = []
                for d in raw_dims:
                    if d.isdigit(): dims.append(int(d))
                    else:
                        r = resolve_label(d)
                        if r is not None: dims.append(r)
                if len(dims) == len(raw_dims):
                    N = len(dims)
                    data_size = 1
                    for d in dims: data_size *= d
                    if N == 1:
                        arrays[nm] = {'dims': dims, 'size': data_size,
                                      'flag': TYPE_FLAGS[canon], 'N': 1}
                    else:
                        arrays[nm] = {'dims': dims, 'size': data_size,
                                      'flag': TYPE_FLAGS[canon], 'N': N}
                    LOCAL_ARRAYS[nm] = dict(arrays[nm])
            i += 1; continue

        i += 1


# ======================================================================
# Raw multi-D array rewriter
# ======================================================================

def rewrite_multi_array_reads(line, code, indent):
    result, temps_to_free = [], []
    i = 0
    while i < len(line):
        ds_match = re.match(r'dimsize\s*\(\s*(\w+)\s*,\s*(\d+)\s*\)', line[i:])
        if ds_match:
            arr = ds_match.group(1); iv = int(ds_match.group(2))
            if arr in arrays:
                info = arrays[arr]
                if info.get('static') or len(info['dims']) == 1:
                    if len(info['dims']) == 1:
                        if iv == 0:
                            result.append(str(info['size']))
                            i += len(ds_match.group(0)); continue
                    elif 0 <= iv < len(info['dims']):
                        result.append(str(info['dims'][iv]))
                        i += len(ds_match.group(0)); continue
                else:
                    if 0 <= iv < len(info['dims']):
                        t = code.alloc(); temps_to_free.append(t)
                        code.emit(f"set {t} {arr}[{iv + 1}]", indent)
                        result.append(t)
                        i += len(ds_match.group(0)); continue
        dm_match = re.match(r'dims\s*\(\s*(\w+)\s*\)', line[i:])
        if dm_match:
            arr = dm_match.group(1)
            if arr in arrays:
                info = arrays[arr]
                if info.get('static') or len(info['dims']) == 1:
                    result.append(str(len(info['dims'])))
                    i += len(dm_match.group(0)); continue
                else:
                    t = code.alloc(); temps_to_free.append(t)
                    code.emit(f"set {t} {arr}[0]", indent)
                    result.append(t)
                    i += len(dm_match.group(0)); continue

        m = re.match(r'[A-Za-z_]\w*', line[i:])
        if not m:
            result.append(line[i]); i += 1; continue
        word = m.group(0)
        j = i + len(word)

        if word in arrays:
            dims = arrays[word]['dims']
            # Extract bracket groups (respecting nesting)
            indices = []
            k = j
            while k < len(line) and line[k] == '[':
                depth = 1
                end = k + 1
                while end < len(line) and depth > 0:
                    if line[end] == '[': depth += 1
                    elif line[end] == ']': depth -= 1
                    end += 1
                if depth != 0:
                    break
                indices.append(line[k + 1:end - 1])
                k = end

            need = False
            if len(dims) > 1 and len(indices) == len(dims):
                need = True
            elif len(dims) == 1 and len(indices) == 1:
                if '++' in indices[0] or '--' in indices[0]:
                    need = True

            if need and indices:
                try:
                    idx_exprs = [fold(Parser(tokenize(idx)).parse_expr())
                                 for idx in indices]
                except SyntaxError:
                    idx_exprs = None
                if idx_exprs is not None:
                    flat = fold(code._flatten(word, idx_exprs))
                    flat_tmp = code.alloc()
                    temps_to_free.append(flat_tmp)
                    code.gen_expr(flat, flat_tmp, indent)
                    result.append(f"{word}[{flat_tmp}]")
                    i = k
                    continue

        result.append(word)
        i = j

    return ''.join(result), temps_to_free

# ======================================================================
# Compound/assign helpers
# ======================================================================

def _check_const_lvalue(lhs, consts, var_map):
    if lhs in consts: report_error(f"Cannot assign to constant '{lhs}'")


def _expr_uses_var(node, var_name):
    if isinstance(node, Var): return node.name == var_name
    if isinstance(node, Const): return False
    if isinstance(node, DimsExpr): return False
    if isinstance(node, DimSizeExpr): return _expr_uses_var(node.index, var_name)
    if isinstance(node, MemberAccess): return _expr_uses_var(node.obj, var_name)
    if isinstance(node, RawArrayRead): return _expr_uses_var(node.index, var_name)
    if isinstance(node, ArrayRead): return any(_expr_uses_var(i, var_name) for i in node.indices)
    if isinstance(node, FlattenExpr): return any(_expr_uses_var(i, var_name) for i in node.indices)
    if isinstance(node, Unary): return _expr_uses_var(node.arg, var_name)
    if isinstance(node, BinOp):
        return _expr_uses_var(node.left, var_name) or _expr_uses_var(node.right, var_name)
    if isinstance(node, (PreInc, PostInc, PreDec, PostDec)): return _expr_uses_var(node.arg, var_name)
    if isinstance(node, AbsExpr): return _expr_uses_var(node.arg, var_name)
    return False


def compound_simple(lhs, op, rhs_val, var_map, consts, code, pool, indent=''):
    if '[' in lhs:
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        if isinstance(flat, Const): index_src, need_free = str(flat.val), False
        elif isinstance(flat, Var): index_src, need_free = code.var.get(flat.name, flat.name), False
        else:
            index_src, need_free = code.alloc(), True; code.gen_expr(flat, index_src, indent)
        cur = code.alloc()
        code.emit(f"set {cur} {arr}[{index_src}]", indent)
        code.emit_op(op_map[op], cur, rhs_val, indent)
        code.emit(f"setarray {arr}[{index_src}] {cur}", indent)
        code.free(cur)
        if need_free: code.free(index_src)
    else:
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        code.emit_op(op_map[op], target, rhs_val, indent)


def compound_expr(lhs, op, ast, var_map, consts, code, pool, indent=''):
    if '[' in lhs:
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        if isinstance(flat, Const): index_src, need_free = str(flat.val), False
        elif isinstance(flat, Var): index_src, need_free = code.var.get(flat.name, flat.name), False
        else:
            index_src, need_free = code.alloc(), True; code.gen_expr(flat, index_src, indent)
        cur = code.alloc()
        code.emit(f"set {cur} {arr}[{index_src}]", indent)
        if isinstance(ast, Const): code.emit_op(op_map[op], cur, str(ast.val), indent)
        elif isinstance(ast, Var): code.emit_op(op_map[op], cur, code.var.get(ast.name, ast.name), indent)
        else:
            rhs_t = code.alloc(); code.gen_expr(ast, rhs_t, indent)
            code.emit_op(op_map[op], cur, rhs_t, indent); code.free(rhs_t)
        code.emit(f"setarray {arr}[{index_src}] {cur}", indent)
        code.free(cur)
        if need_free: code.free(index_src)
    else:
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        if isinstance(ast, Const): code.emit_op(op_map[op], target, str(ast.val), indent)
        elif isinstance(ast, Var): code.emit_op(op_map[op], target, var_map.get(ast.name, ast.name), indent)
        else:
            rhs_t = code.alloc(); code.gen_expr(ast, rhs_t, indent)
            code.emit_op(op_map[op], target, rhs_t, indent); code.free(rhs_t)


def assign_simple(lhs, rhs_val, var_map, consts, code, pool, indent=''):
    if '[' in lhs:
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        if isinstance(flat, Const):
            code.emit(f"setarray {arr}[{flat.val}] {rhs_val}", indent)
        else:
            idx_name = code.index_name(flat)
            code.emit(f"setarray {arr}[{idx_name}] {rhs_val}", indent)
            if not isinstance(flat, (Const, Var)): code.free(idx_name)
    else:
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        code.emit_op('set', target, rhs_val, indent)


def assign_expr(lhs, ast, var_map, consts, code, pool, indent=''):
    if '[' in lhs:
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        code.write_array(arr, flat, ast, indent)
    else:
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        if isinstance(ast, Const):
            code.emit_set_const(target, ast.val, indent)
        elif isinstance(ast, Var):
            src = var_map.get(ast.name, ast.name)
            if target != src: code.emit(f"set {target} {src}", indent)
        elif _expr_uses_var(ast, lhs):
            fresh = code.alloc()
            code.gen_expr(ast, fresh, indent)
            code.emit(f"set {target} {fresh}", indent)
            code.free(fresh)
        else:
            code.gen_expr(ast, target, indent)


# ======================================================================
# Inc/dec, abs
# ======================================================================

def handle_incdec(line, var_map, consts, code, pool, indent=''):
    s = line_without_comment(line).strip()
    m_post = re.match(r'^(\w+(?:\[[^\]]+\])*)\s*(\+\+|--)$', s)
    if m_post:
        _incdec_standalone(m_post.group(1), 1 if m_post.group(2) == '++' else -1,
                           var_map, consts, code, pool, indent); return True
    m_pre = re.match(r'^(\+\+|--)\s*(\w+(?:\[[^\]]+\])*)$', s)
    if m_pre:
        _incdec_standalone(m_pre.group(2), 1 if m_pre.group(1) == '++' else -1,
                           var_map, consts, code, pool, indent); return True
    return False


def _incdec_standalone(lhs, inc, var_map, consts, code, pool, indent=''):
    if '[' in lhs:
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        if isinstance(flat, Const): index_src, need_free = str(flat.val), False
        elif isinstance(flat, Var): index_src, need_free = code.var.get(flat.name, flat.name), False
        else:
            index_src, need_free = code.alloc(), True; code.gen_expr(flat, index_src, indent)
        cur = code.alloc()
        code.emit(f"set {cur} {arr}[{index_src}]", indent)
        code.emit(f"{'add' if inc == 1 else 'sub'} {cur} 1", indent)
        code.emit(f"setarray {arr}[{index_src}] {cur}", indent)
        code.free(cur)
        if need_free: code.free(index_src)
    else:
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        code.emit(f"{'add' if inc == 1 else 'sub'} {target} 1", indent)


def handle_abs_statement(line, var_map, consts, code, pool, indent=''):
    """Handle only the C-style 'abs(...)' form. Bare 'abs <var>' is CON
    native and passed through by is_raw_con_line as a raw line."""
    s = line_without_comment(line).strip()
    m = re.match(r'^abs\s*\(\s*(\w+(?:\[[^\]]+\])*)\s*\)$', s)
    if not m:
        return False
    lhs = m.group(1)
    if '[' in lhs:
        # Array element — load, apply native abs, write back
        lt = Parser(tokenize(lhs)); arr = lt.consume('ID').value
        indices = []
        while lt.peek().value == '[':
            lt.consume(); indices.append(lt.parse_expr()); lt.consume('SYM', ']')
        flat = fold(code._flatten(arr, indices))
        if isinstance(flat, Const):
            index_src, need_free = str(flat.val), False
        elif isinstance(flat, Var):
            index_src, need_free = code.var.get(flat.name, flat.name), False
        else:
            index_src, need_free = code.alloc(), True
            code.gen_expr(flat, index_src, indent)
        cur = code.alloc()
        code.emit(f"set {cur} {arr}[{index_src}]", indent)
        code.emit(f"abs {cur}", indent)
        code.emit(f"setarray {arr}[{index_src}] {cur}", indent)
        code.free(cur)
        if need_free:
            code.free(index_src)
    else:
        # Scalar — rewrite to native CON syntax, no expansion
        _check_const_lvalue(lhs, consts, var_map)
        target = var_map.get(lhs, lhs)
        code.emit(f"abs {target}", indent)
    return True


# ======================================================================
# State call helpers
# ======================================================================

def _total_temp_for(callee, ns):
    """Temps that `callee` uses in the given namespace (via _TOTAL_TEMP_USAGE)."""
    if callee in _TOTAL_TEMP_USAGE:
        return _TOTAL_TEMP_USAGE[callee].get(ns, set())
    if callee in EXTERN_TEMP_USAGE:
        actor, idxs = EXTERN_TEMP_USAGE[callee]
        return idxs if STATE_NAMESPACE.get(callee, 'global') == ns else set()
    return set()


def trans_usage_through_inline(callee, ns, visited=None):
    """For inline callee: transitively collect non-inline callee temps in `ns`."""
    if visited is None: visited = set()
    if callee in visited: return set()
    visited.add(callee)
    result = set()
    for c in _CALLS_FOR_EXT.get(callee, set()):
        if c in INLINE_STATES:
            result |= trans_usage_through_inline(c, ns, visited)
        else:
            result |= _total_temp_for(c, ns)
    return result


def _check_ns_call(callee):
    callee_ns = STATE_NAMESPACE.get(callee, 'global')
    if is_event_namespace(_CURRENT_NAMESPACE) or is_event_namespace(callee_ns):
        if callee_ns != _CURRENT_NAMESPACE:
            report_error(
                f"Cannot call state '{callee}' (namespace '{callee_ns}') from "
                f"namespace '{_CURRENT_NAMESPACE}'; cross-namespace calls "
                f"involving event namespaces are forbidden"
            )


def emit_state_call(callee, args_str, var_map, consts, code, pool, indent=''):
    _check_ns_call(callee)
    parts = split_args_raw(args_str)
    arg_names, alloc_temps, writeback_arrays = [], [], []

    for p in parts:
        a = fold(Parser(tokenize(p)).parse_expr())
        if isinstance(a, Const):
            t = code.alloc(); code.emit_set_const(t, a.val, indent)
            arg_names.append(t); alloc_temps.append(t); writeback_arrays.append(None)
        elif isinstance(a, Var):
            arg_names.append(var_map.get(a.name, a.name)); writeback_arrays.append(None)
        elif isinstance(a, ArrayRead):
            t = code.alloc(); code.gen_expr(a, t, indent)
            arg_names.append(t); alloc_temps.append(t); writeback_arrays.append(a)
        else:
            t = code.alloc(); code.gen_expr(a, t, indent)
            arg_names.append(t); alloc_temps.append(t); writeback_arrays.append(None)

    if arg_names:
        code.emit(f"setarrayseq __param_array {' '.join(arg_names)}", indent)
    code.emit(f"state {callee}", indent)
    if callee in RETURN_STATES and arg_names:
        code.emit(f"getarrayseq __param_array {' '.join(arg_names)}", indent)
        for idx, arr_read in enumerate(writeback_arrays):
            if arr_read is None: continue
            flat = fold(code._flatten(arr_read.array, arr_read.indices))
            if isinstance(flat, Const):
                code.emit(f"setarray {arr_read.array}[{flat.val}] {arg_names[idx]}", indent)
            else:
                idx_tmp = code.alloc(); code.gen_expr(flat, idx_tmp, indent)
                code.emit(f"setarray {arr_read.array}[{idx_tmp}] {arg_names[idx]}", indent)
                code.free(idx_tmp)

    for t in alloc_temps:
        try: code.free(t)
        except Exception: pass


def inline_call(callee, args_str, var_map, consts, code, pool, indent='',
                process_comments=False):
    params, body, _ns, ret = INLINE_STATES[callee]
    is_variadic = bool(params and params[-1] == '...')
    formal_params = params[:-1] if is_variadic else list(params)
    raw_args = split_args_raw(args_str)

    if is_variadic:
        if len(raw_args) < len(formal_params):
            report_error(f"Not enough arguments for {callee}: need at least "
                         f"{len(formal_params)}, got {len(raw_args)}")
    else:
        if len(raw_args) != len(formal_params):
            report_error(f"Wrong argument count for {callee}: expected "
                         f"{len(formal_params)}, got {len(raw_args)}")

    local_map = {}; string_params = {}; aliased_params = {}; used_caller_temps = set()

    for idx, p_name in enumerate(formal_params):
        arg = raw_args[idx]
        if p_name.startswith('!'):
            sname = p_name[1:]
            if not ((arg.startswith('"') and arg.endswith('"') and len(arg) >= 2) or
                    (arg.startswith("'") and arg.endswith("'") and len(arg) >= 2)):
                report_error(f"Text parameter '{p_name}' requires a quoted argument, got: {arg!r}")
            content = arg[1:-1]
            resolved = content
            if resolved in string_params: resolved = string_params[resolved]
            string_params[sname] = resolved
            continue
        try:
            ast = fold(Parser(tokenize(arg)).parse_expr())
        except (SyntaxError, NotImplementedError):
            ast = None
        if isinstance(ast, Var) and ast.name in arrays:
            report_error(f"Array '{ast.name}' cannot be passed to scalar parameter "
                         f"'{p_name}'; use a !-prefixed param and quote: "
                         f"{callee}(…, \"{ast.name}\")")
        aliased = False
        if ret and isinstance(ast, Var) and ast.name in var_map:
            src = var_map[ast.name]
            if src not in used_caller_temps:
                local_map[p_name] = src; aliased_params[p_name] = src
                used_caller_temps.add(src); aliased = True
        if not aliased:
            t = pool.alloc(); local_map[p_name] = t
            if isinstance(ast, Const): code.emit_set_const(t, ast.val, indent)
            elif isinstance(ast, Var):
                src = var_map.get(ast.name, ast.name)
                if t != src: code.emit(f"set {t} {src}", indent)
            elif ast is not None: code.gen_expr(ast, t, indent)

    variadic_temps = []
    if is_variadic:
        for i in range(len(formal_params), len(raw_args)):
            variadic_temps.append(raw_args[i])

    body_decls = set()
    for bline in body:
        bm = re.match(r'(let|const)\s+(\w+)\b', line_without_comment(bline).strip())
        if bm: body_decls.add(bm.group(2))
    for sname in string_params:
        if sname in body_decls: continue
        pat = r'(?<![!\w])' + re.escape(sname) + r'\s*\['
        for bline in body:
            if re.search(pat, line_without_comment(bline)):
                report_error(f"Array parameter '!{sname}' must be referenced as "
                             f"'!{sname}' inside the body; found bare '{sname}[' in: {bline.strip()}")

    scan_body = body if process_comments else strip_block_comments(body)
    inline_calls = {}
    for i, bl in enumerate(scan_body):
        bs = line_without_comment(bl).strip()
        cm = re.match(r'^(?:state\s+)?(\w+)\s*\(', bs)
        if cm:
            bc = cm.group(1)
            if bc in KNOWN_STATES and bc not in INLINE_STATES:
                inline_calls[i] = _total_temp_for(bc, _CURRENT_NAMESPACE)

    inline_decl = {}
    for i, bl in enumerate(scan_body):
        bs = line_without_comment(bl).strip()
        dm = re.match(r'(let|const)\s+(\w+)\s*(?:=\s*(.*))?$', bs)
        if not dm: dm = re.match(r'(let|const)\s+(\w+)\s+(\S+.*)$', bs)
        if dm: inline_decl[dm.group(2)] = i

    inline_last = {}
    for nm, dl in inline_decl.items():
        last = -1
        for i in range(dl + 1, len(scan_body)):
            if re.search(r'\b' + re.escape(nm) + r'\b', line_without_comment(scan_body[i])):
                last = i
        inline_last[nm] = last

    inline_let_excl = {}
    for nm, dl in inline_decl.items():
        last = inline_last[nm]; excl = set()
        for cidx, ctemps in inline_calls.items():
            if dl <= cidx <= last: excl |= ctemps
        inline_let_excl[nm] = excl

    global _CURRENT_LET_EXCLUDED
    saved_let_excl = _CURRENT_LET_EXCLUDED
    _CURRENT_LET_EXCLUDED = {**saved_let_excl, **inline_let_excl}

    saved_var = code.var; code.var = {**var_map, **local_map}
    saved_consts = code.consts; code.consts = consts

    count = len(variadic_temps)
    for bline in body:
        for sl in substitute_variadic_and_strings(bline, variadic_temps, string_params, count):
            process_line(sl, code.var, consts, pool, code, process_comments)

    if ret:
        for idx, p_name in enumerate(formal_params):
            if p_name.startswith('!'): continue
            if p_name in aliased_params: continue
            if idx >= len(raw_args): continue
            try:
                orig_ast = fold(Parser(tokenize(raw_args[idx])).parse_expr())
            except (SyntaxError, NotImplementedError):
                continue
            if isinstance(orig_ast, Var):
                target = var_map.get(orig_ast.name, orig_ast.name)
                code.emit(f"set {target} {local_map[p_name]}", indent)
            elif isinstance(orig_ast, ArrayRead):
                flat = fold(code._flatten(orig_ast.array, orig_ast.indices))
                if isinstance(flat, Const):
                    code.emit(f"setarray {orig_ast.array}[{flat.val}] "
                              f"{local_map[p_name]}", indent)
                else:
                    idx_tmp = code.alloc(); code.gen_expr(flat, idx_tmp, indent)
                    code.emit(f"setarray {orig_ast.array}[{idx_tmp}] "
                              f"{local_map[p_name]}", indent)
                    code.free(idx_tmp)

        if is_variadic:
            for i in range(len(formal_params), len(raw_args)):
                try:
                    v_ast = fold(Parser(tokenize(raw_args[i])).parse_expr())
                except (SyntaxError, NotImplementedError):
                    continue
                if isinstance(v_ast, ArrayRead):
                    warn(f"@return on {callee}: variadic argument #{i - len(formal_params)} "
                         f"is an array access ('{raw_args[i]}'); writeback requires a "
                         f"simple variable. Bind to a `let` and write back manually.")

    for v, temp in list(code.var.items()):
        if v not in saved_var and v not in aliased_params:
            try: pool.free(temp)
            except Exception: pass

    code.var = saved_var; code.consts = saved_consts
    _CURRENT_LET_EXCLUDED = saved_let_excl


# ======================================================================
# Braced line handler
# ======================================================================

def handle_braced_line(line, var_map, consts, pool, code, indent=''):
    m = re.match(r'^\s*\{(.+)\}\s*$', line)
    if not m: return line
    inner = m.group(1).strip()
    old_len = len(code.out)

    cmpd = re.match(r'^(\w+(?:\[[^\]]+\])*)\s*([+\-*/%&|^]=|<<=|>>=)\s*(.*)$', inner)
    if cmpd:
        lhs, op, rhs = cmpd.group(1), cmpd.group(2), cmpd.group(3)
        if op.endswith('='): op = op[:-1]
        try:
            if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
               and 'or' not in rhs and 'xor' not in rhs:
                rhs_subst = rhs
                for letv, temp in var_map.items():
                    rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
                compound_simple(lhs, op, rhs_subst, var_map, consts, code, pool, indent)
            else:
                ast = fold(Parser(tokenize(rhs)).parse_expr())
                compound_expr(lhs, op, ast, var_map, consts, code, pool, indent)
        except (SyntaxError, NotImplementedError):
            rhs_subst = rhs
            for letv, temp in var_map.items():
                rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
            compound_simple(lhs, op, rhs_subst, var_map, consts, code, pool, indent)
    elif re.match(_lvalue_re, inner) and '=' in inner:
        parts = inner.split('=', 1); lhs, rhs = parts[0].strip(), parts[1].strip()
        try:
            if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
               and 'or' not in rhs and 'xor' not in rhs:
                rhs_subst = rhs
                for letv, temp in var_map.items():
                    rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
                assign_simple(lhs, rhs_subst, var_map, consts, code, pool, indent)
            else:
                ast = fold(Parser(tokenize(rhs)).parse_expr())
                assign_expr(lhs, ast, var_map, consts, code, pool, indent)
        except (SyntaxError, NotImplementedError):
            rhs_subst = rhs
            for letv, temp in var_map.items():
                rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
            assign_simple(lhs, rhs_subst, var_map, consts, code, pool, indent)
    else:
        cooked = inner
        for letv, temp in var_map.items():
            cooked = re.sub(r'\b' + re.escape(letv) + r'\b', temp, cooked)
        return cooked

    processed = code.out[-1] if len(code.out) > old_len else inner
    del code.out[old_len:]
    return processed


# ======================================================================
# Core line processor
# ======================================================================

def process_line(line, var_map, consts, pool, code, process_comments=False):
    stripped = line.lstrip()
    if not stripped: code.emit('', ''); return
    indent = line[:len(line) - len(stripped)]
    parse_s = line_without_comment(line).strip()
    if not parse_s: code.emit(line); return
    if '/*' in line and not process_comments: code.emit(line); return

    # Case range
    case_m = re.match(r'^(\s*)case\s+(\S+)\s+\.\.\.\s+(\S+)\s*(//.*)?$', line)
    if case_m:
        sv = resolve_label(case_m.group(2)); ev = resolve_label(case_m.group(3))
        comment = case_m.group(4) or ''
        if sv is not None and ev is not None:
            if sv > ev: report_error(f"Invalid case range {sv} > {ev}")
            for v in range(sv, ev + 1): code.emit(f"case {v}{comment}", indent)
            return
        warn(f"Cannot resolve case range {case_m.group(2)} ... {case_m.group(3)}")

    # static_array
    sm = re.match(r'^(static_array|static_gamearray)\s+(.+)$', parse_s)
    if sm:
        kind = sm.group(1); rest = sm.group(2).strip()
        modern = re.match(r'^(\w+)\s+(\w+)\s*((?:\[\w+\])+)$', rest)
        if modern:
            type_raw = modern.group(1); arr_name = modern.group(2)
            canonical = resolve_type(type_raw)
            if canonical not in TYPE_FLAGS:
                report_error(f"Unknown type '{type_raw}' in {kind}")
            flag = TYPE_FLAGS[canonical]
            raw_dims = re.findall(r'\[(\w+)\]', modern.group(3)); dims = []
            for d in raw_dims:
                if d.isdigit(): dims.append(int(d))
                else:
                    r = resolve_label(d)
                    if r is None: report_error(f"Cannot resolve dimension '{d}' for '{arr_name}'")
                    dims.append(r)
            total = 1
            for d in dims: total *= d
            N = len(dims)
            arrays[arr_name] = {'dims': dims, 'size': total, 'flag': flag, 'N': N, 'static': True}
            LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
            code.emit(f"array {arr_name} {total} {flag}", indent); return
        parts = rest.split()
        if len(parts) < 3:
            report_error(f"{kind} (old syntax) needs <name> <dim> [<dim> ...] <flag>")
        arr_name = parts[0]
        try: flag = int(parts[-1])
        except ValueError:
            r = resolve_label(parts[-1]); flag = r if r is not None else 0
        dims = []
        for tok in parts[1:-1]:
            if tok.isdigit(): dims.append(int(tok))
            else:
                r = resolve_label(tok)
                if r is None: report_error(f"Cannot resolve dimension '{tok}' for '{arr_name}'")
                dims.append(r)
        total = 1
        for d in dims: total *= d
        N = len(dims)
        arrays[arr_name] = {'dims': dims, 'size': total, 'flag': flag, 'N': N, 'static': True}
        LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
        code.emit(f"array {arr_name} {total} {flag}", indent); return

    if is_raw_con_line(line):
        comment_split = line.split('//', 1)
        code_part = comment_split[0]
        comment_part = ('//' + comment_split[1]) if len(comment_split) > 1 else ''
        try:
            cooked_code, temps = rewrite_multi_array_reads(code_part, code, indent)
        except (SyntaxError, NotImplementedError) as e:
            warn(f"Cannot flatten multi-D array: {e}")
            cooked_code = code_part; temps = []
        cooked = cooked_code.rstrip()
        for letv, temp in var_map.items():
            cooked = re.sub(r'\b' + re.escape(letv) + r'\b', temp, cooked)
        if comment_part: cooked = cooked + '  ' + comment_part
        code.emit(cooked)
        for t in temps:
            try: code.free(t)
            except Exception: pass
        return

    s = parse_s

    if re.match(r'^\s*\{.+\}\s*$', line):
        cooked = handle_braced_line(line, var_map, consts, pool, code, indent)
        code.emit('{ ' + cooked + ' }', indent); return

    m = re.match(r'const\s+(\w+)\s*(?:=\s*(.+))?$', s)
    if not m: m = re.match(r'const\s+(\w+)\s+(\S+.*)$', s)
    if m:
        nm = m.group(1); init = m.group(2) or '0'
        if nm in var_map: report_error(f"Variable '{nm}' already declared")
        old_ex = pool.excluded.copy()
        let_excl = _CURRENT_LET_EXCLUDED.get(nm, set())
        if let_excl: pool.set_excluded(old_ex | let_excl)
        t = pool.alloc(); pool.set_excluded(old_ex); var_map[nm] = t; consts.add(nm)
        ast = fold(Parser(tokenize(init)).parse_expr())
        if isinstance(ast, Const): code.emit_set_const(t, ast.val, indent)
        else: code.gen_expr(ast, t, indent)
        comment = extract_comment(line)
        if comment: code.out[-1] += ' ' + comment
        return

    m = re.match(r'let\s+(\w+)\s*(?:=\s*(.+))?$', s)
    if not m: m = re.match(r'let\s+(\w+)\s+(\S+.*)$', s)
    if m:
        nm = m.group(1); init = m.group(2) or '0'
        if nm in var_map: report_error(f"Variable '{nm}' already declared")
        old_ex = pool.excluded.copy()
        let_excl = _CURRENT_LET_EXCLUDED.get(nm, set())
        if let_excl: pool.set_excluded(old_ex | let_excl)
        t = pool.alloc(); pool.set_excluded(old_ex); var_map[nm] = t
        ast = fold(Parser(tokenize(init)).parse_expr())
        if isinstance(ast, Const): code.emit_set_const(t, ast.val, indent)
        else: code.gen_expr(ast, t, indent)
        comment = extract_comment(line)
        if comment: code.out[-1] += ' ' + comment
        return

    if handle_incdec(line, var_map, consts, code, pool, indent): return
    if handle_abs_statement(line, var_map, consts, code, pool, indent): return

    cmpd = re.match(r'^(\w+(?:\[[^\]]+\])*)\s*([+\-*/%&|^]=|<<=|>>=)\s*(.*)$', s)
    if cmpd:
        lhs, op, rhs = cmpd.group(1), cmpd.group(2), cmpd.group(3)
        if op.endswith('='): op = op[:-1]
        try:
            if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
               and 'or' not in rhs and 'xor' not in rhs:
                rhs_subst = rhs
                for letv, temp in var_map.items():
                    rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
                compound_simple(lhs, op, rhs_subst, var_map, consts, code, pool, indent)
            else:
                ast = fold(Parser(tokenize(rhs)).parse_expr())
                compound_expr(lhs, op, ast, var_map, consts, code, pool, indent)
        except (SyntaxError, NotImplementedError):
            rhs_subst = rhs
            for letv, temp in var_map.items():
                rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
            compound_simple(lhs, op, rhs_subst, var_map, consts, code, pool, indent)
        return

    if re.match(_lvalue_re, s) and '=' in s:
        parts = s.split('=', 1); lhs, rhs = parts[0].strip(), parts[1].strip()
        try:
            if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
               and 'or' not in rhs and 'xor' not in rhs:
                rhs_subst = rhs
                for letv, temp in var_map.items():
                    rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
                assign_simple(lhs, rhs_subst, var_map, consts, code, pool, indent)
            else:
                ast = fold(Parser(tokenize(rhs)).parse_expr())
                assign_expr(lhs, ast, var_map, consts, code, pool, indent)
        except (SyntaxError, NotImplementedError):
            rhs_subst = rhs
            for letv, temp in var_map.items():
                rhs_subst = re.sub(r'\b' + re.escape(letv) + r'\b', temp, rhs_subst)
            assign_simple(lhs, rhs_subst, var_map, consts, code, pool, indent)
        return

    call = re.match(r'^(?:state\s+)?(\w+)\s*\((.*)\)$', s)
    if call and call.group(1) in KNOWN_STATES:
        callee, args = call.group(1), call.group(2)
        if callee in INLINE_STATES:
            inline_call(callee, args, var_map, consts, code, pool, indent, process_comments)
        else:
            emit_state_call(callee, args, var_map, consts, code, pool, indent)
        return

    if s.startswith('zero(') or s.startswith('zero '):
        mz = re.match(r'^zero\s*\(\s*(\w+)\s*\)$', s)
        if mz and mz.group(1) in arrays:
            emit_array_zero(mz.group(1), indent, code); return
    if s.startswith('resize2d') or s.startswith('resize3d') or s.startswith('resizeNd'):
        if _handle_resize(s, indent, code, pool):
            return

    if s.startswith('resizearray '):
        parts = s.split()
        if len(parts) >= 2 and parts[1] in arrays:
            arr = parts[1]
            if arrays[arr].get('static'): report_error(f"Cannot resizearray static array '{arr}'")
            elif len(arrays[arr]['dims']) > 1:
                warn(f"resizearray on multi-dim array '{arr}' — use resizeNd/zero; header will desync")

    cooked = line
    for letv, temp in var_map.items():
        cooked = re.sub(r'\b' + re.escape(letv) + r'\b', temp, cooked)
    code.emit(cooked)


# ======================================================================
# Body processing (shared by state & event)
# ======================================================================

def _process_body(body, line_numbers, var_map, consts, pool, code,
                  free_line, process_comments):
    """Inner loop shared by process_state and process_event_body."""
    idx = 0; in_block = False
    while idx < len(body):
        set_current_line(line_numbers[idx])
        line = body[idx]
        parse_s = line_without_comment(line).strip()

        if in_block:
            if '*/' in line: in_block = False
            code.emit(line); idx += 1; continue
        if '/*' in line:
            in_block = True; code.emit(line); idx += 1; continue
        if not parse_s: code.emit(line); idx += 1; continue
        if parse_s.startswith('//') or parse_s.startswith('#'):
            code.emit(line); idx += 1; continue

        if_match = re.match(r'^(if[a-zA-Z0-9_]*)\s+(.+)$', parse_s)
        if if_match:
            cond = if_match.group(2).strip()
            if_indent = line[:len(line) - len(line.lstrip())]
            if_comment = extract_comment(line)
            j = idx + 1
            if j < len(body) and body[j].strip() == '{':
                brace_line = body[j]; j += 1
                block = []
                while j < len(body) and body[j].strip() != '}':
                    block.append(body[j]); j += 1
                closing = None
                if j < len(body) and body[j].strip() == '}':
                    closing = body[j]; j += 1
                saved_out, code.out = code.out, []
                for bline in block:
                    process_line(bline, var_map, consts, pool, code, process_comments)
                block_code = code.out; code.out = saved_out
                cond_sub = cond
                for letv, temp in var_map.items():
                    cond_sub = re.sub(r'\b' + re.escape(letv) + r'\b', temp, cond_sub)
                try: cond_sub, cond_temps = rewrite_multi_array_reads(cond_sub, code, if_indent)
                except (SyntaxError, NotImplementedError): cond_temps = []
                code.emit(f"{if_match.group(1)} {cond_sub}" + (f" {if_comment}" if if_comment else ""), if_indent)
                for t in cond_temps: code.free(t)
                code.emit(brace_line)
                for ln in block_code: code.emit(ln)
                if closing is not None: code.emit(closing)
                idx = j; continue
            else:
                true_line = body[j] if j < len(body) else None
                if true_line is None: report_error("Expected statement after if")
                saved_out, code.out = code.out, []
                set_current_line(line_numbers[j])
                process_line(true_line, var_map, consts, pool, code, process_comments)
                true_code = code.out; code.out = saved_out
                cond_sub = cond
                for letv, temp in var_map.items():
                    cond_sub = re.sub(r'\b' + re.escape(letv) + r'\b', temp, cond_sub)
                try: cond_sub, cond_temps = rewrite_multi_array_reads(cond_sub, code, if_indent)
                except (SyntaxError, NotImplementedError): cond_temps = []
                code.emit(f"{if_match.group(1)} {cond_sub}" + (f" {if_comment}" if if_comment else ""), if_indent)
                for t in cond_temps: code.free(t)
                for ln in true_code: code.emit(ln)
                j += 1
                if j < len(body) and body[j].strip().startswith('else'):
                    else_line = body[j]
                    else_stripped = line_without_comment(else_line).strip()

                    if else_stripped == 'else':
                        # Plain else — consume next line as body
                        else_comment = extract_comment(else_line)
                        else_indent = else_line[:len(else_line) - len(else_line.lstrip())]
                        j += 1
                        false_line = body[j] if j < len(body) else None
                        if false_line is None:
                            report_error("Expected statement after else")
                        saved_out, code.out = code.out, []
                        set_current_line(line_numbers[j])
                        process_line(false_line, var_map, consts, pool, code, process_comments)
                        false_code = code.out
                        code.out = saved_out
                        code.emit(f"else" + (f" {else_comment}" if else_comment else ""), else_indent)
                        for ln in false_code:
                            code.emit(ln)
                        j += 1
                    else:
                        # 'else if<cond> …' (or anything else after 'else'):
                        # pass through verbatim; do NOT consume the next line,
                        # it's the body of the chained if.
                        process_line(else_line, var_map, consts, pool, code, process_comments)
                        j += 1
                idx = j; continue

        process_line(line, var_map, consts, pool, code, process_comments)
        for v, fl in list(free_line.items()):
            if fl == idx and v in var_map:
                try: pool.free(var_map[v])
                except Exception: pass
                del var_map[v]
        idx += 1


def _scan_own_used(opt_out):
    used_by_ns = {}
    for line in strip_comments_for_scan(opt_out):
        for m in re.finditer(r'__ns_(\w+?)_(\d+)', line):
            ns = m.group(1); idx = int(m.group(2))
            used_by_ns.setdefault(ns, set()).add(idx)
    return used_by_ns


# ======================================================================
# State processor
# ======================================================================

def process_state(name, params, body, namespace, return_params,
                  process_comments=False, line_numbers=None,
                  total_temp_usage=None):
    if line_numbers is None: line_numbers = list(range(1, len(body) + 1))
    if total_temp_usage is None: total_temp_usage = {}

    pool = get_pool(namespace)
    pool.reset()

    scan_body = body if process_comments else strip_block_comments(body)
    call_positions = {}
    for idx, ln in enumerate(scan_body):
        s = line_without_comment(ln).strip()
        cm = re.match(r'^(?:state\s+)?(\w+)\s*\(', s)
        if cm:
            callee = cm.group(1)
            if callee in INLINE_STATES:
                trans = trans_usage_through_inline(callee, namespace)
                if trans: call_positions[idx] = trans
                continue
            if callee in total_temp_usage:
                t = total_temp_usage[callee].get(namespace, set())
                if t: call_positions[idx] = t
            elif callee in EXTERN_TEMP_USAGE:
                actor, idxs = EXTERN_TEMP_USAGE[callee]
                if STATE_NAMESPACE.get(callee, 'global') == namespace:
                    call_positions[idx] = idxs

    var_map = {}; consts = set(); decl_line = {}
    in_block = False
    for i, ln in enumerate(body):
        set_current_line(line_numbers[i])
        if in_block:
            if '*/' in ln: in_block = False
            continue
        if '/*' in ln: in_block = True; continue
        s = line_without_comment(ln).strip()
        if s.startswith('//') or s.startswith('#'): continue
        m = re.match(r'(let|const)\s+(\w+)\s*(?:=\s*(.*))?$', s)
        if not m: m = re.match(r'(let|const)\s+(\w+)\s+(\S+.*)$', s)
        if m:
            kind, nm = m.group(1), m.group(2)
            decl_line[nm] = i
            if kind == 'const': consts.add(nm)

    all_vars = params + list(decl_line.keys())
    last_use = {}
    for v in all_vars:
        last = -1
        start = -1 if v in params else decl_line[v]
        for i in range(start + 1, len(body)):
            if re.search(r'\b' + re.escape(v) + r'\b', line_without_comment(body[i])):
                last = i
        last_use[v] = last

    pairs = brace_pairs(body)
    free_line = {}
    for v in all_vars:
        sc = scope_end(decl_line[v], pairs, len(body)) if v in decl_line else len(body) - 1
        l = last_use[v]
        free_line[v] = sc if l == -1 else min(l, sc)
    if return_params:
        for p in params: free_line[p] = len(body)

    all_callee_temps = set()
    for ctemps in call_positions.values(): all_callee_temps |= ctemps
    pool.set_excluded(all_callee_temps)
    for p in params:
        t = pool.alloc(); var_map[p] = t
    pool.set_excluded(set())

    let_excluded = {}
    for nm, dl in decl_line.items():
        last = last_use.get(nm, -1)
        excl = set()
        for cidx, ctemps in call_positions.items():
            if dl <= cidx <= last: excl |= ctemps
        let_excluded[nm] = excl

    global _CURRENT_LET_EXCLUDED, _CURRENT_NAMESPACE
    saved_let_excl = _CURRENT_LET_EXCLUDED
    saved_ns = _CURRENT_NAMESPACE
    _CURRENT_LET_EXCLUDED = let_excluded
    _CURRENT_NAMESPACE = namespace

    code = CodeGen(pool, var_map, consts)
    indent0 = ''
    if body:
        first_line = body[0]
        indent0 = first_line[:len(first_line) - len(first_line.lstrip())]
    if params:
        code.emit(f"getarrayseq __param_array {' '.join(var_map[p] for p in params)}", indent0)

    cacheable = []
    for arr_name, info in arrays.items():
        if info.get('static') or len(info['dims']) <= 1: continue
        if _state_resizes_array(body, arr_name): continue
        cacheable.append(arr_name)
    for arr_name in cacheable:
        N = len(arrays[arr_name]['dims'])
        temps = []
        for k in range(1, N):
            t = code.alloc()
            code.emit(f"set {t} {arr_name}[{k + 1}]", indent0)
            temps.append(t)
        code.cached_dims[arr_name] = temps

    _process_body(body, line_numbers, var_map, consts, pool, code,
                  free_line, process_comments)

    if return_params and params:
        code.emit(f"setarrayseq __param_array {' '.join(var_map[p] for p in params)}", indent0)
    code.release_all()
    opt_out = peephole_optimize(code.out)

    _CURRENT_LET_EXCLUDED = saved_let_excl
    _CURRENT_NAMESPACE = saved_ns

    used_by_ns = _scan_own_used(opt_out)
    return [f"defstate {name}"] + opt_out + ["ends"], pool.high, used_by_ns


def process_event_body(event_kind, event_name, body, line_numbers, process_comments, ns_name):
    pool = get_pool(ns_name)
    pool.reset()

    var_map = {}; consts = set(); decl_line = {}
    in_block = False
    for i, ln in enumerate(body):
        set_current_line(line_numbers[i])
        if in_block:
            if '*/' in ln: in_block = False
            continue
        if '/*' in ln: in_block = True; continue
        s = line_without_comment(ln).strip()
        if s.startswith('//') or s.startswith('#'): continue
        m = re.match(r'(let|const)\s+(\w+)\s*(?:=\s*(.*))?$', s)
        if not m: m = re.match(r'(let|const)\s+(\w+)\s+(\S+.*)$', s)
        if m:
            kind, nm = m.group(1), m.group(2)
            decl_line[nm] = i
            if kind == 'const': consts.add(nm)

    last_use = {}
    for v, dl in decl_line.items():
        last = -1
        for i in range(dl + 1, len(body)):
            if re.search(r'\b' + re.escape(v) + r'\b', line_without_comment(body[i])):
                last = i
        last_use[v] = last

    pairs = brace_pairs(body)
    free_line = {}
    for v, dl in decl_line.items():
        sc = scope_end(dl, pairs, len(body))
        l = last_use[v]
        free_line[v] = sc if l == -1 else min(l, sc)

    global _CURRENT_LET_EXCLUDED, _CURRENT_NAMESPACE
    saved_let_excl = _CURRENT_LET_EXCLUDED
    saved_ns = _CURRENT_NAMESPACE
    _CURRENT_LET_EXCLUDED = {}
    _CURRENT_NAMESPACE = ns_name

    code = CodeGen(pool, var_map, consts)
    _process_body(body, line_numbers, var_map, consts, pool, code,
                  free_line, process_comments)
    code.release_all()

    _CURRENT_LET_EXCLUDED = saved_let_excl
    _CURRENT_NAMESPACE = saved_ns

    opt_out = peephole_optimize(code.out)
    return [f"{event_kind} {event_name}"] + opt_out + ["endevent"]


# ======================================================================
# Call graph & total usage (per-namespace)
# ======================================================================

def build_call_graph_and_temp_sets(lines, process_comments=False):
    global _CALLS_FOR_EXT, _TOTAL_TEMP_USAGE
    states = {}; calls = {}

    i = 0; in_block = False
    while i < len(lines):
        set_current_line(i + 1)
        line = lines[i].rstrip('\n')
        s = line_without_comment(line).strip()
        if in_block:
            if '*/' in line: in_block = False
            i += 1; continue
        if '/*' in line:
            in_block = True; i += 1; continue
        if not s: i += 1; continue
        if s.startswith('//') or s.startswith('#'): i += 1; continue
        decos = []
        while i < len(lines) and s.startswith('@'):
            decos.append(s); i += 1
            s = line_without_comment(lines[i]).strip() if i < len(lines) else ''
        if i < len(lines) and s.startswith('defstate'):
            j = i + 1
            while j < len(lines) and lines[j].strip().lower() != 'ends': j += 1
            if j >= len(lines): report_error("Missing 'ends'")
            hdr = s[len('defstate'):].strip()
            m = re.match(r'(\w+)\s*(?:\(([^)]*)\))?', hdr)
            sn = m.group(1)
            params = [p.strip() for p in m.group(2).split(',') if p.strip()] if m.group(2) else []
            body = lines[i + 1:j]
            ns = STATE_NAMESPACE.get(sn, 'global')
            ret = '@return' in decos
            states[sn] = (params, body, ns, ret, list(range(i + 1, j + 1)))
            calls[sn] = set()
            scan = body if process_comments else strip_block_comments(body)
            for bline in scan:
                cs = line_without_comment(bline).strip()
                cm = re.match(r'^(?:state\s+)?(\w+)\s*\(', cs)
                if cm and cm.group(1) in KNOWN_STATES: calls[sn].add(cm.group(1))
            i = j + 1
        else:
            i += 1

    _CALLS_FOR_EXT.clear(); _CALLS_FOR_EXT.update(calls)

    def trans_callees(sn, visited=None):
        if visited is None: visited = set()
        if sn in visited: return set()
        visited.add(sn)
        result = set()
        for c in calls.get(sn, set()):
            if c in INLINE_STATES: result |= trans_callees(c, visited)
            elif c in states: result.add(c)
        return result

    remaining = set(states.keys()); order = []; cycle_states = set()
    while remaining:
        progress = False
        for sn in list(remaining):
            if trans_callees(sn) & remaining: continue
            order.append(sn); remaining.discard(sn); progress = True
        if not progress:
            for sn in remaining:
                cycle_states.add(sn); order.append(sn)
            break
    if cycle_states:
        warn(f"Cyclic state dependencies among {sorted(cycle_states)}; "
             f"using conservative estimates for those")

    def callee_usage_by_ns(sn, visited=None):
        if visited is None: visited = set()
        if sn in visited: return {}
        visited.add(sn)
        result = {}
        for c in calls.get(sn, set()):
            if c in INLINE_STATES:
                sub = callee_usage_by_ns(c, visited)
            elif c in _TOTAL_TEMP_USAGE:
                sub = _TOTAL_TEMP_USAGE[c]
            elif c in EXTERN_TEMP_USAGE:
                actor, idxs = EXTERN_TEMP_USAGE[c]
                cns = STATE_NAMESPACE.get(c, 'global')
                sub = {cns: set(idxs)}
            else:
                sub = {}
            for k, v in sub.items():
                result.setdefault(k, set()).update(v)
        return result

    _TOTAL_TEMP_USAGE.clear()
    for sn in order:
        params, body, ns, ret, line_numbers = states[sn]
        pool = get_pool(ns); pool.reset()

        if sn in cycle_states:
            try:
                _, high, _ = process_state(sn, params, body, ns, ret,
                                           process_comments, line_numbers, {})
            except SugarError:
                high = 0
            _TOTAL_TEMP_USAGE[sn] = {ns: set(range(high))}
            continue

        try:
            _, _, own_by_ns = process_state(sn, params, body, ns, ret,
                                            process_comments, line_numbers,
                                            _TOTAL_TEMP_USAGE)
        except SugarError:
            own_by_ns = {}

        combined = {n: set(s) for n, s in own_by_ns.items()}
        for c_ns, c_idx in callee_usage_by_ns(sn).items():
            combined.setdefault(c_ns, set()).update(c_idx)
        _TOTAL_TEMP_USAGE[sn] = combined

    return calls, _TOTAL_TEMP_USAGE


# ======================================================================
# Transpile
# ======================================================================

def _parse_namespace_decorator(d):
    if not d.startswith('@namespace'):
        return None
    rest = d[len('@namespace'):].strip()
    if not rest:
        report_error("@namespace requires a name")
    parts = rest.split()
    name = parts[0]
    if len(parts) > 1:
        kind = parts[1]
        if kind not in ('global', 'actor'):
            report_error(f"@namespace kind must be 'global' or 'actor', got '{kind}'")
    else:
        kind = name if name in ('global', 'actor') else 'global'
    return (name, kind)


def transpile(lines, process_comments=False, check_unknown_callees=False):
    global arrays, RETURN_STATES, INLINE_STATES, KNOWN_STATES, _TOTAL_TEMP_USAGE
    LOCAL_DEFINES.clear(); LOCAL_INLINE_STATES.clear(); LOCAL_RETURN_STATES.clear()
    LOCAL_ONLY_INLINE.clear(); LOCAL_ARRAYS.clear()
    STATE_NAMESPACE.clear(); POOLS.clear()
    NS_KIND.clear(); NS_KIND.update({'global': 'global', 'actor': 'actor'}); EVENT_NAMESPACES.clear()
    out = []; state_temp_info = {}

    # First pass
    i = 0; in_block = False
    while i < len(lines):
        set_current_line(i + 1)
        line = lines[i].rstrip('\n')
        s = line_without_comment(line).strip()
        if in_block:
            if '*/' in line: in_block = False
            i += 1; continue
        if '/*' in line:
            in_block = True; i += 1; continue
        if not s: i += 1; continue
        if s.startswith('//') or s.startswith('#'): i += 1; continue

        if s.startswith('define '):
            parts = s.split(None, 2)
            if len(parts) >= 3:
                name, value = parts[1], parts[2].strip()
                if name in DEFINES and DEFINES[name] != value:
                    warn(f"Define '{name}' redefined")
                DEFINES[name] = value; LOCAL_DEFINES[name] = value
            i += 1; continue

        decos = []
        while i < len(lines) and s.startswith('@'):
            decos.append(s); i += 1
            s = line_without_comment(lines[i]).strip() if i < len(lines) else ''

        # Deprecation checks
        for d in decos:
            if d == '@global':
                report_error("'@global' is deprecated; use '@namespace global'")
            if d == '@actor':
                report_error("'@actor' is deprecated; use '@namespace actor'")

        if i < len(lines) and s.startswith('defstate'):
            k = i + 1
            while k < len(lines) and lines[k].strip().lower() != 'ends': k += 1
            if k >= len(lines): report_error("Missing 'ends'")
            hdr = s[len('defstate'):].strip()
            m = re.match(r'(\w+)\s*(?:\(([^)]*)\))?', hdr)
            sn = m.group(1)
            params = [p.strip() for p in m.group(2).split(',') if p.strip()] if m.group(2) else []
            KNOWN_STATES.add(sn)
            is_return = '@return' in decos
            is_inline = '@inline' in decos
            is_local = '@local' in decos

            # Namespace
            ns_name = 'global'
            ns_decorator_found = False
            for d in decos:
                if d.startswith('@namespace'):
                    ns_name, kind = _parse_namespace_decorator(d)
                    register_namespace(ns_name, kind)
                    ns_decorator_found = True
                    break
            if is_inline and ns_decorator_found:
                warn(f"@namespace on @inline state '{sn}' is ignored "
                     f"(inline states inherit caller's namespace)")

            if is_return:
                RETURN_STATES.add(sn); LOCAL_RETURN_STATES.add(sn)
            else:
                RETURN_STATES.discard(sn)

            if is_inline:
                body = lines[i + 1:k]
                INLINE_STATES[sn] = (params, body, ns_name, is_return)
                LOCAL_INLINE_STATES[sn] = (params, body, ns_name, is_return)
                if is_local: LOCAL_ONLY_INLINE.add(sn)
                else: LOCAL_ONLY_INLINE.discard(sn)
            else:
                if is_local:
                    warn(f"@local on non-inline state '{sn}' — ignored")
                INLINE_STATES.pop(sn, None)
                LOCAL_ONLY_INLINE.discard(sn)
                STATE_NAMESPACE[sn] = ns_name
            i = k + 1
        else:
            em = re.match(r'^(onevent|appendevent)\s+(\w+)\s*(//.*)?$', s)
            if em:
                event_kind = em.group(1)
                event_name = em.group(2)
                ns_name = None
                ns_kind = 'global'
                for d in decos:
                    if d.startswith('@namespace'):
                        ns_name, ns_kind = _parse_namespace_decorator(d)
                        break
                if ns_name is None:
                    fallback = f"ev_{event_name}"
                    warn(
                        f"{event_kind} {event_name} has no @namespace decorator; "
                        f"using fallback '{fallback}' to protect against "
                        f"temp clobbering. Add any '@namespace <name>' to silence."
                    )
                    ns_name = fallback
                    ns_kind = 'global'
                register_namespace(ns_name, ns_kind)
                if ns_name not in ('global', 'actor'):
                    EVENT_NAMESPACES.add(ns_name)
                # Skip body
                k = i + 1
                while k < len(lines) and lines[k].strip().lower() != 'endevent':
                    k += 1
                if k >= len(lines):
                    report_error(f"Missing 'endevent' for '{event_name}'")
                i = k + 1
                continue
            i += 1

    _prescan_arrays(lines)
    calls, total_temp_usage = build_call_graph_and_temp_sets(lines, process_comments)
    _TOTAL_TEMP_USAGE = total_temp_usage

    if check_unknown_callees:
        for sn, callees in calls.items():
            for c in callees:
                if c not in total_temp_usage and c not in EXTERN_TEMP_USAGE:
                    warn(f"State '{sn}' calls external state '{c}' whose temp "
                         f"usage is unknown during generation")

    # Second pass
    i = 0; decos = []; in_block = False
    while i < len(lines):
        set_current_line(i + 1)
        line = lines[i].rstrip('\n')
        parse_s = line_without_comment(line).strip()

        if in_block:
            if '*/' in line: in_block = False
            out.append(line); i += 1; continue
        if '/*' in line:
            in_block = True; out.append(line); i += 1; continue
        if not parse_s: out.append(line); i += 1; continue
        if parse_s.startswith('//') or parse_s.startswith('#'):
            out.append(line); i += 1; continue
        if parse_s.startswith('@'):
            decos.append(parse_s); i += 1; continue

        if re.match(r'^(let|const)\b', parse_s):
            report_error(f"'{parse_s.split()[0]}' is only allowed inside a state or event block")

        # Event blocks
        em = re.match(r'^(onevent|appendevent)\s+(\w+)\s*(//.*)?$', parse_s)
        if em:
            event_kind = em.group(1)
            event_name = em.group(2)
            ns_name = None
            for d in decos:
                if d.startswith('@namespace'):
                    ns_name, _ = _parse_namespace_decorator(d)
                    break
            if ns_name is None:
                ns_name = f"ev_{event_name}"
            decos = []
            body_start = i + 1
            i += 1
            event_body = []
            while i < len(lines) and lines[i].strip().lower() != 'endevent':
                event_body.append(lines[i]); i += 1
            if i >= len(lines):
                report_error(f"Missing 'endevent' for '{event_name}'")
            i += 1
            body_line_numbers = list(range(body_start, body_start + len(event_body)))
            try:
                out.extend(process_event_body(event_kind, event_name, event_body,
                                              body_line_numbers, process_comments,
                                              ns_name))
            except SugarError:
                pass
            continue

        if parse_s.startswith('defstate'):
            hdr = parse_s[len('defstate'):].strip()
            m = re.match(r'(\w+)\s*(?:\(([^)]*)\))?', hdr)
            sn = m.group(1)
            params = [p.strip() for p in m.group(2).split(',') if p.strip()] if m.group(2) else []
            def_comment = extract_comment(line)
            if sn in INLINE_STATES:
                i += 1
                while i < len(lines) and lines[i].strip().lower() != 'ends':
                    i += 1
                i += 1; decos = []; continue
            body = []; body_start = i + 1; i += 1
            while i < len(lines) and lines[i].strip().lower() != 'ends':
                body.append(lines[i]); i += 1
            if i >= len(lines):
                report_error(f"Missing 'ends' for state {sn}")
            i += 1
            ns = STATE_NAMESPACE.get(sn, 'global')
            ret = '@return' in decos
            body_line_numbers = list(range(body_start, body_start + len(body)))
            try:
                state_lines, _, used_by_ns = process_state(sn, params, body, ns, ret,
                                                           process_comments, body_line_numbers,
                                                           total_temp_usage)
                state_temp_info[sn] = (ns, 0, used_by_ns)
                if def_comment:
                    state_lines[0] += f" {def_comment}"
                out.extend(state_lines)
            except SugarError:
                pass
            decos = []; continue

        # static_array
        sm = re.match(r'^(static_array|static_gamearray)\s+(.+)$', parse_s)
        if sm:
            kind = sm.group(1); rest = sm.group(2).strip()
            modern = re.match(r'^(\w+)\s+(\w+)\s*((?:\[\w+\])+)$', rest)
            if modern:
                type_raw, arr_name = modern.group(1), modern.group(2)
                canonical = resolve_type(type_raw)
                if canonical not in TYPE_FLAGS:
                    report_error(f"Unknown type '{type_raw}' in {kind}")
                flag = TYPE_FLAGS[canonical]
                raw_dims = re.findall(r'\[(\w+)\]', modern.group(3)); dims = []
                for d in raw_dims:
                    if d.isdigit(): dims.append(int(d))
                    else:
                        r = resolve_label(d)
                        if r is None: report_error(f"Cannot resolve dimension '{d}' for '{arr_name}'")
                        dims.append(r)
                total = 1
                for d in dims: total *= d
                N = len(dims)
                arrays[arr_name] = {'dims': dims, 'size': total, 'flag': flag, 'N': N, 'static': True}
                LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
                out.append(f"array {arr_name} {total} {flag}")
                i += 1; continue
            parts = rest.split()
            if len(parts) < 3:
                report_error(f"{kind} (old syntax) needs <name> <dim> [<dim> ...] <flag>")
            arr_name = parts[0]
            try: flag = int(parts[-1])
            except ValueError:
                r = resolve_label(parts[-1]); flag = r if r is not None else 0
            dims = []
            for tok in parts[1:-1]:
                if tok.isdigit(): dims.append(int(tok))
                else:
                    r = resolve_label(tok)
                    if r is None: report_error(f"Cannot resolve dimension '{tok}' for '{arr_name}'")
                    dims.append(r)
            total = 1
            for d in dims: total *= d
            N = len(dims)
            arrays[arr_name] = {'dims': dims, 'size': total, 'flag': flag, 'N': N, 'static': True}
            LOCAL_ARRAYS[arr_name] = dict(arrays[arr_name])
            out.append(f"array {arr_name} {total} {flag}")
            i += 1; continue

        # Dynamic arrays
        tm = re.match(r'^(\w+)\s+', parse_s)
        if tm and resolve_type(tm.group(1)) in TYPE_FLAGS:
            canon = resolve_type(tm.group(1))
            rest = parse_s[tm.end():].strip()
            m2 = re.match(r'(\w+)\s*((?:\[\w+\])+)', rest)
            if m2:
                nm = m2.group(1)
                raw_dims = re.findall(r'\[(\w+)\]', m2.group(2))
                dims, ok = [], True
                for d in raw_dims:
                    if d.isdigit(): dims.append(int(d))
                    else:
                        r = resolve_label(d)
                        if r is None or r <= 0:
                            report_error(f"Cannot resolve dimension '{d}' for '{nm}'")
                            ok = False; break
                        dims.append(r)
                if ok:
                    N = len(dims); data_size = 1
                    for d in dims: data_size *= d
                    if N == 1:
                        arrays[nm] = {'dims': dims, 'size': data_size,
                                      'flag': TYPE_FLAGS[canon], 'N': 1}
                        LOCAL_ARRAYS[nm] = dict(arrays[nm])
                        out.append(f"array {nm} {data_size} {TYPE_FLAGS[canon]}")
                    else:
                        _check_header_fits(nm, dims, TYPE_FLAGS[canon])
                        total = (N + 1) + data_size
                        arrays[nm] = {'dims': dims, 'size': data_size,
                                      'flag': TYPE_FLAGS[canon], 'N': N}
                        LOCAL_ARRAYS[nm] = dict(arrays[nm])
                        out.append(f"array {nm} {total} {TYPE_FLAGS[canon]}")
                        out.append(f"setarray {nm}[0] {N}")
                        for k, d in enumerate(dims):
                            out.append(f"setarray {nm}[{k + 1}] {d}")
                    i += 1; continue

        if parse_s.startswith('array '):
            parts = parse_s.split()
            if len(parts) >= 4:
                try: sz = int(parts[2])
                except ValueError:
                    r = resolve_label(parts[2]); sz = r if r is not None else 0
                try: flag = int(parts[3])
                except ValueError:
                    r = resolve_label(parts[3]); flag = r if r is not None else 0
                arrays[parts[1]] = {'dims': [sz], 'size': sz, 'flag': flag, 'N': 1}
                LOCAL_ARRAYS[parts[1]] = dict(arrays[parts[1]])
            out.append(line); i += 1; continue

        if parse_s.startswith('define '):
            out.append(line); i += 1; continue

        # Top-level call
        call = re.match(r'^(?:state\s+)?(\w+)\s*\((.*)\)$', parse_s)
        if call and call.group(1) in KNOWN_STATES \
           and not parse_s.startswith('zero') and not parse_s.startswith('resize'):
            callee, args = call.group(1), call.group(2)
            ns = 'global'
            pool = get_pool(ns); pool.reset()
            code = CodeGen(pool, {})
            indent = line[:len(line) - len(line.lstrip())]
            global _CURRENT_NAMESPACE
            saved_ns = _CURRENT_NAMESPACE
            _CURRENT_NAMESPACE = ns
            try:
                if callee in INLINE_STATES:
                    inline_call(callee, args, {}, set(), code, pool, indent, process_comments)
                else:
                    emit_state_call(callee, args, {}, set(), code, pool, indent)
                out.extend(code.out)
            except SugarError:
                pass
            _CURRENT_NAMESPACE = saved_ns
            i += 1; continue

        indent = line[:len(line) - len(line.lstrip())]
        ns = 'global'
        pool = get_pool(ns); pool.reset()
        code = CodeGen(pool, {})
        handled = False
        try:
            if handle_incdec(line, {}, set(), code, pool, indent):
                out.extend(code.out); handled = True
        except SugarError:
            handled = True
        if handled: i += 1; continue

        pool = get_pool(ns); pool.reset()
        code = CodeGen(pool, {})
        handled = False
        try:
            if handle_abs_statement(line, {}, set(), code, pool, indent):
                out.extend(code.out); handled = True
        except SugarError:
            handled = True
        if handled: i += 1; continue

        cmpd = re.match(r'^(\w+(?:\[[^\]]+\])*)\s*([+\-*/%&|^]=|<<=|>>=)\s*(.*)$', parse_s)
        if cmpd:
            pool = get_pool(ns); pool.reset()
            code = CodeGen(pool, {})
            lhs, op, rhs = cmpd.group(1), cmpd.group(2), cmpd.group(3)
            if op.endswith('='): op = op[:-1]
            try:
                if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
                   and 'or' not in rhs and 'xor' not in rhs:
                    compound_simple(lhs, op, rhs, {}, set(), code, pool, indent)
                else:
                    ast = fold(Parser(tokenize(rhs)).parse_expr())
                    compound_expr(lhs, op, ast, {}, set(), code, pool, indent)
                out.extend(code.out)
            except SugarError:
                pass
            i += 1; continue

        if re.match(_lvalue_re, parse_s) and '=' in parse_s:
            pool = get_pool(ns); pool.reset()
            code = CodeGen(pool, {})
            parts = parse_s.split('=', 1); lhs, rhs = parts[0].strip(), parts[1].strip()
            try:
                if not re.search(r'[+\-*/%&|^()]|<<|>>', rhs) and 'and' not in rhs \
                   and 'or' not in rhs and 'xor' not in rhs:
                    assign_simple(lhs, rhs, {}, set(), code, pool, indent)
                else:
                    ast = fold(Parser(tokenize(rhs)).parse_expr())
                    assign_expr(lhs, ast, {}, set(), code, pool, indent)
                out.extend(code.out)
            except SugarError:
                pass
            i += 1; continue

        if parse_s.startswith('zero('):
            mz = re.match(r'zero\((\w+)\)', parse_s)
            if mz and mz.group(1) in arrays:
                pool = get_pool(ns); pool.reset()
                code = CodeGen(pool, {})
                emit_array_zero(mz.group(1), '', code)
                out.extend(code.out); code.release_all()
            else: out.append(line)
            i += 1; continue

        if parse_s.startswith('resize2d') or parse_s.startswith('resize3d') \
           or parse_s.startswith('resizeNd'):
            pool = get_pool(ns); pool.reset()
            code = CodeGen(pool, {})
            handled = False
            try:
                if _handle_resize(parse_s, '', code, pool):
                    out.extend(code.out)
                    handled = True
            except SugarError:
                handled = True
            code.release_all()
            if not handled:
                out.append(line)
            i += 1; continue

        if re.match(r'^\s*\{.+\}\s*$', line):
            pool = get_pool(ns); pool.reset()
            code = CodeGen(pool, {})
            cooked = handle_braced_line(line, {}, set(), pool, code, indent)
            out.append('{ ' + cooked + ' }')
            code.release_all(); i += 1; continue

        out.append(line); i += 1

    return out, state_temp_info


# ======================================================================
# Externs
# ======================================================================

def register_externs(lines, source_name=""):
    j = 0
    while j < len(lines):
        s = line_without_comment(lines[j]).strip()
        if not s: j += 1; continue

        m = re.match(r'^@extern_namespace\s+(\w+)\s+(global|actor)', s)
        if m:
            register_namespace(m.group(1), m.group(2)); j += 1; continue

        m = re.match(r'^@extern_temps\s+(\w+)\s+(\w+)\s*(.*)', s)
        if m:
            name, ns = m.group(1), m.group(2)
            rest = m.group(3).strip()
            idx_list = [int(x) for x in re.split(r'[,\s]+', rest) if x] if rest else []
            key = (name, ns)
            if key in EXTERN_TEMP_USAGE and EXTERN_SOURCES.get(key) != source_name:
                report_error(f"Extern conflict: state '{name}' ns '{ns}' defined in multiple externs")
            EXTERN_TEMP_USAGE[key] = set(idx_list)
            EXTERN_SOURCES[key] = source_name
            KNOWN_STATES.add(name)
            STATE_NAMESPACE[name] = ns
            if name not in RETURN_STATES: pass
            j += 1; continue

        m = re.match(r'^@extern_params\s+(\w+)\s+(.*)', s)
        if m:
            EXTERN_PARAMS[m.group(1)] = m.group(2).split()
            KNOWN_STATES.add(m.group(1)); j += 1; continue

        m = re.match(r'^@extern_return\s+(\w+)', s)
        if m:
            RETURN_STATES.add(m.group(1)); j += 1; continue

        m = re.match(r'^@extern_define\s+(\w+)\s+(.+)', s)
        if m:
            name, value = m.group(1), m.group(2).strip()
            if name in DEFINES and DEFINES[name] != value:
                warn(f"Extern define '{name}' conflicts: {DEFINES[name]} vs {value}")
            DEFINES[name] = value; j += 1; continue

        m = re.match(r'^@extern_array\s+(\w+)\s+(-?\d+)\s+(static|dynamic)\s+([\d\s,]+)', s)
        if m:
            name = m.group(1); flag = int(m.group(2)); kind = m.group(3)
            dims = [int(x) for x in re.split(r'[,\s]+', m.group(4).strip()) if x]
            if not dims: report_error(f"@extern_array '{name}' needs dimensions")
            N = len(dims); data_size = 1
            for d in dims: data_size *= d
            entry = {'dims': dims, 'size': data_size, 'flag': flag, 'N': N}
            if kind == 'static': entry['static'] = True
            elif N > 1: _check_header_fits(name, dims, flag)
            arrays[name] = entry; j += 1; continue

        if s.startswith('@'):
            decorators = []
            while j < len(lines):
                s2 = line_without_comment(lines[j]).strip()
                if s2.startswith('@'): decorators.append(s2); j += 1
                else: break
            if j < len(lines):
                dline = line_without_comment(lines[j]).strip()
                if dline.startswith('defstate'):
                    hdr = dline[len('defstate'):].strip()
                    dm = re.match(r'(\w+)\s*(?:\(([^)]*)\))?', hdr)
                    if dm:
                        dname = dm.group(1)
                        dparams = [p.strip() for p in dm.group(2).split(',') if p.strip()] if dm.group(2) else []
                        body = []
                        j += 1
                        while j < len(lines) and lines[j].strip().lower() != 'ends':
                            body.append(lines[j]); j += 1
                        if j < len(lines): j += 1
                        if '@inline' in decorators:
                            INLINE_STATES[dname] = (dparams, body, 'global',
                                                    '@return' in decorators)
                            KNOWN_STATES.add(dname)
                            if '@return' in decorators: RETURN_STATES.add(dname)
                    continue
            continue

        j += 1


def generate_externs(state_temp_info, output_path):
    ext_temps = {}

    def callees_of(state): return _CALLS_FOR_EXT.get(state, set())

    def trans_external_usage(state):
        result = {}
        for c in callees_of(state):
            if c in INLINE_STATES:
                sub = trans_external_usage(c) if c in _CALLS_FOR_EXT else {}
                if c not in _CALLS_FOR_EXT:
                    for key, idxs in EXTERN_TEMP_USAGE.items():
                        if key[0] == c:
                            sub.setdefault(key[1], set()).update(idxs)
            elif c in state_temp_info:
                sub = compute_ext(c)
            else:
                sub = {}
                for key, idxs in EXTERN_TEMP_USAGE.items():
                    if key[0] == c:
                        sub.setdefault(key[1], set()).update(idxs)
            for ns, s in sub.items():
                result.setdefault(ns, set()).update(s)
        return result

    def compute_ext(name):
        if name in ext_temps: return ext_temps[name]
        if name not in state_temp_info: return {}
        _, _, own = state_temp_info[name]
        combined = {ns: set(s) for ns, s in own.items()}
        for ns, s in trans_external_usage(name).items():
            combined.setdefault(ns, set()).update(s)
        ext_temps[name] = combined
        return combined

    for sn in state_temp_info: compute_ext(sn)

    inline_callee_usage = {}
    for name in LOCAL_INLINE_STATES:
        inline_callee_usage[name] = trans_external_usage(name)

    with open(output_path, 'w') as f:
        f.write("# Externs generated by SugarCON\n")

        for name, value in LOCAL_DEFINES.items():
            f.write(f"@extern_define {name} {value}\n")

        custom_ns = set()
        for _ns, _max, used_by_ns in state_temp_info.values():
            for ns in used_by_ns: custom_ns.add(ns)
        for ns in sorted(custom_ns):
            if ns in ('global', 'actor'): continue
            kind = NS_KIND.get(ns, 'global')
            f.write(f"@extern_namespace {ns} {kind}\n")
        for name in LOCAL_INLINE_STATES:
            if name in LOCAL_ONLY_INLINE: continue
            ns = 'global'
            if ns not in ('global', 'actor') and ns not in custom_ns:
                custom_ns.add(ns)
                f.write(f"@extern_namespace {ns} {NS_KIND.get(ns, 'global')}\n")

        for name, info in LOCAL_ARRAYS.items():
            kind = 'static' if info.get('static') else 'dynamic'
            dims_str = ' '.join(str(d) for d in info['dims'])
            f.write(f"@extern_array {name} {info['flag']} {kind} {dims_str}\n")

        for name in sorted(LOCAL_RETURN_STATES):
            if name in LOCAL_ONLY_INLINE: continue
            f.write(f"@extern_return {name}\n")

        for name, (_ns, _max, _used) in state_temp_info.items():
            for ns, idxs in ext_temps.get(name, {}).items():
                indices = ','.join(str(i) for i in sorted(idxs))
                f.write(f"@extern_temps {name} {ns} {indices}\n")

        for name in LOCAL_INLINE_STATES:
            if name in LOCAL_ONLY_INLINE: continue
            usage = inline_callee_usage.get(name, {})
            for ns, idxs in usage.items():
                indices = ','.join(str(i) for i in sorted(idxs))
                f.write(f"@extern_temps {name} {ns} {indices}\n")

        for name, (params, body, _ns, ret) in LOCAL_INLINE_STATES.items():
            if name in LOCAL_ONLY_INLINE: continue
            if ret: f.write("@return\n")
            f.write("@inline\n")
            f.write(f"defstate {name}({', '.join(params)})\n")
            for bline in body: f.write(bline + "\n")
            f.write("ends\n")

    print(f"Externs written to {output_path}")


def compute_declarations(lines):
    max_idx = {}
    for line in strip_comments_for_scan(lines):
        for m in re.finditer(r'__ns_(\w+?)_(\d+)', line):
            ns = m.group(1); idx = int(m.group(2))
            max_idx[ns] = max(max_idx.get(ns, -1), idx)
    decls = []
    for ns, mx in max_idx.items():
        kind = NS_KIND.get(ns, 'global')
        flag = 0 if kind == 'global' else 2
        for i in range(mx + 1):
            decls.append(f"var __ns_{ns}_{i} 0 {flag}")
    return decls


# ======================================================================
# Main
# ======================================================================

def _paths_conflict(a, b):
    try:
        aa = os.path.abspath(a); bb = os.path.abspath(b)
    except Exception:
        return False
    if aa == bb: return True
    if os.path.exists(a) and os.path.exists(b):
        try: return os.path.samefile(a, b)
        except OSError: pass
    return False


def main():
    ap = argparse.ArgumentParser(description='SugarCON transpiler for EDuke32')
    ap.add_argument('input', nargs='?', help='Input .scon file')
    ap.add_argument('-o', '--output', help='Output file')
    ap.add_argument('--externs', action='append', default=[], help='Externs file(s)')
    ap.add_argument('--generate-externs', action='store_true',
                    help='Generate .ext file instead of transpiling')
    ap.add_argument('--process-comments', action='store_true',
                    help='Process code inside /* … */ blocks')
    ap.add_argument('--main-file', action='store_true',
                    help='This file owns __param_array in multi-file builds')
    args = ap.parse_args()

    if not args.input:
        print("Error: no input file provided. Use -h for help.", file=sys.stderr)
        sys.exit(1)

    if args.output:
        if args.output.lower().endswith('.scon'):
            print(f"Error: refusing to write to .scon file '{args.output}' "
                  f"(would destroy source).", file=sys.stderr); sys.exit(1)
        if _paths_conflict(args.output, args.input):
            print(f"Error: refusing to overwrite input file '{args.input}'.",
                  file=sys.stderr); sys.exit(1)

    for ef in args.externs:
        with open(ef) as f:
            source_name = os.path.basename(ef)
            try: register_externs(f.read().split('\n'), source_name)
            except SugarError: pass

    with open(args.input) as f:
        source = f.read()

    lines = source.split('\n')
    result, state_temp_info = transpile(
        lines,
        process_comments=args.process_comments,
        check_unknown_callees=args.generate_externs,
    )

    if ERROR_LIST:
        print("Errors encountered:")
        for err in ERROR_LIST: print(f"  {err}")
        sys.exit(1)

    if args.generate_externs:
        if not args.output:
            base = os.path.splitext(args.input)[0]
            args.output = base + ".ext"
        generate_externs(state_temp_info, args.output)
        return

    uses_param_array = any(
        '__param_array' in line
        for line in strip_comments_for_scan(result)
    )
    is_main = args.main_file or bool(
        re.search(r'^\s*include(optional)?\s+"', source, re.MULTILINE)
    )
    if args.externs:
        should_declare = uses_param_array and is_main
    else:
        should_declare = uses_param_array

    pre = compute_declarations(result)
    if should_declare:
        pre.append("array __param_array 0 0")

    out_str = '\n'.join(pre + result)
    out_str = '\n'.join(pre + result)
    if args.output:
        with open(args.output, 'w') as f: f.write(out_str)
    else: print(out_str)


if __name__ == '__main__':
    main()
