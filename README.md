# SugarCON

My take on turning CON into a more modern, slightly more ~function~ state oriented language.
Sort of unfinished and/or underdeveloped (just really wanted to release this publicly).

## Description

Initially conceived as a set of features meant to speed up prototyping in CON, and
in general make the language less painful to work with for the modern programmer.
Later the aim changed towards making the language easier to use for procedural programming.
The final result is a mixed bag, mostly C-like syntax, but has cherry picked from other
languages like function decorators from Python. The language features a very bare bones macro-like
system too. The majority of additions are just syntactic sugar hence the name.
Due to the EDuke32 project this was conceived for going into development limbo, many planned
features were retroactively added without any real usage, only bare minimum testing, so things
may not completely work as expected (most notably: extern files & macros).
Namespaces were an exceptionally last minute addition as prototyping never got far enough
to bump into event hooks (appendevent/onevent) that disrupt CON execution flow.

## Quick start

File extensions used by the transpiler: *.scon* (SugarCON source), *.ext* (header file like cross-file data)
See samples directory for an example project setup. Requires Python 3.8+, no dependencies.

## Language showcase

From samples/sugar_scripts/rough_sec_surf.scon
```
// SPDX-License-Identifier: Unlicense

define MAX_I32 2147483647
define MAX_ARRAYSEQ 32
define NUM_SIZES 4
define OLDMAXSECTORS 1024
define NEWMAXSECTORS 4096

// Multidimensional arrays are supported. Could have any number of dimensions.
// This is just syntactic sugar for accessing a flattened multidimensional array.
// These arrays are row-major.
// Arrays have Rust/HolyC like type data type specifiers. Eg.: i8, u16, boolean.
// Do note that i32 is a hack and that u32 doesn't work as expected. i32 MIGHT actually be
// 64 bit on 64 bit builds of EDuke32, development of the project never got far
// enough for such a thing to be investigated.
i32 secsize[OLDMAXSECTORS][NUM_SIZES]
// Multidimensional arrays declared like this are so-called dynamic arrays which support
// resizing their dimensions at runtime, but not the number of their dimensions.
// Access into them is slightly slower than static arrays since a lookup has
// to be performed to determine their current dimensions.
// Static arrays are the fastest due to their dimensions being substituted by the
// transpiler in their flattening access logic.
static_array i32 sumarr[4]

var sumcounter 0 0

/*********************
* States with the return decorator will overwrite
* the passed in variables values with their values
* present at the end of the state
**********************/

// function has to be called with: sectnum, MAX_I32, MAX_I32, -MAX_I32, -MAX_I32
@return
defstate getsecsize(dasec, minx, miny, maxx, maxy) // function-like named parameter passing
  // the 'let' keyword creates a locally scoped variable
  let i = 0
  // features alternative vanilla CON-like syntax:
  // let i 0
  
  for i walofsec dasec
    {
      ifg wall[i].x maxx
        maxx = wall[i].x
      ifg wall[i].y maxy
        maxy = wall[i].y
      ifl wall[i].x minx
        minx = wall[i].x
      ifl wall[i].y miny
        miny = wall[i].y
    }
ends

/*******************
* Inlined states are good for optimization.
* They get substituted in-place avoiding setarrayseq
* and getarrayseq calls as used by states with parameters.
*******************/
@inline
@return
defstate swap(a, b)
  let tmp = b
  b = a
  a = tmp
ends

/*******************
* The local decorator denotes that the inlined state is scoped to the current file.
* Inlined states support macro functionality such as string & variadic parameters.
*******************/
@local
@inline
defstate map_over_2darr(!func, !array, numseconddee, ...)
  let i 0
  let j 0
  let cnt 0
  // Const allows declaring variables like let but prevents their mutation in
  // SugarCON statements, passing as return value to vanilla CON functions WILL
  // mutate them!!!
  const nLabeledParams = 1 // since string params are handled by the transpiler
  const maxparams = (MAX_ARRAYSEQ - nLabeledParams) - 1

  // Safety check so we don't run out of arrayseq slots
  // ... syntax auto expands to number of variadic parameters in if and switch statements
  ifg ... maxparams
  {
    // The exclamation mark before a parameter's name denotes that it's a string.
    // Inside the state body it will get substituted. Placing an exclamation mark
    // after the variable name will place it's value inside quotes
    qputs 98 map_over_2darr: call: !func! exceeded maximum number of allowed parameters!!!
    echo 98
    terminate
  }

  // Determine length of first dimension of array
  getarraysize array cnt
  cnt /= numseconddee // C-style shorthands are supported

  for i range cnt
  {
    // We've got a hardcoded __param_array present in every transpiled file
    // Manually invoke the state with overloaded params
    for j range numseconddee
    {
      // ... syntax when not in an if or switch statement auto-expands to the passed in parameters
      // seperated by spaces. The ,,, syntax does the same except seperated with a comma and space ", "
      // Exclamation mark substitution allows for array access too
      setarrayseq __param_array !array[i][j] ...
      state !func
    }
  }
ends

/*
  Sums the sector 2D array in a pretty hacky way
*/
defstate sum_sector_array(value)
  sumcounter = sumcounter % NUM_SIZES

  // C-style increment/decrement
  sumarr[sumcounter++] += value
ends

// Calculates rough surface area of sector in BUILD units
@return
defstate rough_sec_surf(surface)
  sumcounter = 0
  // Built-in quick array zeroing trick
  zero(sumarr)
  // Also handles multidimensional arrays, preserving their header
  zero(secsize)

  // Manually read the header of the dynamic array:
  // Header structure is the following (cnt = 0):
  // [0] = number of dimensions (n)
  // [1 ... n] = dimensions[ cnt++ ] (counter increments until it reaches n - 1)
  // [n + 1] = start of array data
  // So since we're dealing with a 2D array and we want to iterate over it's first dimension
  // we need to grab the value located at index 1.
  let i 0
  const len = secsize[1]
  for i range len
  {
    // We reuse i as the sectnum, and break when
    // we exceed the runtime populated sector count
    ifg i numsectors
      break

    secsize[i][0] = MAX_I32
    secsize[i][1] = MAX_I32
    secsize[i][2] = -MAX_I32
    secsize[i][3] = -MAX_I32
    getsecsize(i, secsize[i][0], secsize[i][1], secsize[i][2], secsize[i][3], secsize[i][4])
  }

  // Calling a macro here (always inlined). String parameters need to be quoted.
  // No extra parameters are passed in this instance.
  map_over_2darr("sum_sector_array", 'secsize', len)

  surface = 0

  // Add X dimensions
  surface += abs(sumarr[2] - sumarr[0])
  // Add Y dimensions
  surface += abs(sumarr[3] - sumarr[1])
ends

// main has to be called from another CON file or use this commented out appendevent

// LAST MINUTE ADDITION:
// Namespaces: they change the pool of temporary variables used by SugarCON
// statements so that event hooks disrupting execution flow don't interfere with
// the global program state. appendevent/onevent/defstate blocks can be namespaced.
// Make sure to call only code in the same namespace unless the code is vanilla CON.
// By default 2 namespaces exist: global and actor. Actor is a leftover from VERY
// early in the project and has never seen any use, I think it's actively harmful
// and a horrible idea to use.
// global is the default namespace
/*
// Silence warning about un-namespaced appendevent
@namespace global
appendevent EVENT_ENTERLEVEL
  state main_
endevent
*/

// main func
// calling from an external project file (when done properly by including the .ext)
// will prevent all the temporary variables which are used under the hood for let/const
// and expressions from being used in the calling functions scope.
// BEWARE of (some) events and while loops! They CAN clobber the entire program's values!
// If invoked at a particularly bad time
defstate main_
  let total_area 0

  // Resizearray SHOULD NEVER be used with multidimensional arrays
  // zero, resizeNd, resize2d, resize3d are safe convenience wrappers.
  // resizeNd(arrayname, ...) - takes as many size arguments as many
  // dimensions the array has.
  // flatten(arrayname, ...) can be used to get the calculated flattened
  // index of the array
  resize2d(secsize, NEWMAXSECTORS, NUM_SIZES)

  // get the number of dimensions of arrays (both static and dynamic)
  // const d = dims(arrayname)
  // get the size of the given dimension. Dimensions start at 0 like indexes
  // const s = dimsize(arrayname, 0)

  rough_sec_surf(total_area)

  qputs 98 Surface area of map (in BU): %d
  qsprintf 98 98 total_area
  
  // I don't remember whether quote actually prints to the console...
  quote 98
  echo 98

  // Source for conversion: https://wiki.eduke32.com/wiki/Build_units
  // Transpiler will automatically optimize this to a bit shift
  let total_area_meters = total_area / 512

  qputs 98 Surface area of map (in m): %d
  qsprintf 98 98 total_area

  quote 98
  echo 98
ends
```

## Licensing

The transpiler is licensed under the GPL-3.0.

The code samples present in the 'samples/' directory are public domain under the
Unlicense license. You are free to copy, modify, distribute, and incorporate the
sample code into your own projects without restriction.

## AI usage disclosure

This project was implemented entirely by DeepSeek-R1 based off of my language specification.
The language is entirely human made, while the transpiler is 100% AI.
