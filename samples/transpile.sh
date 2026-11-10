#/bin/env bash

# I've never actually scripted in bash properly
# so I apologize in advance for this mess

# change path to match your installation
output_dir="$(pwd)/scripts/"
script_dir="$(pwd)/sugar_scripts/"
ext_dir="${script_dir}exts/"

# Change to match your install dir
transpiler="$(pwd)/sugarcon.py"

# Clean up our leftover exts
rm -f ${script_dir}exts/*.ext

# First pass of extern gen
for f in $script_dir*.scon; do
  if [ -f "$f" ]; then 
    python "$transpiler" "$f" -o "${ext_dir}$(basename ${f%.*}).ext" --generate-externs > /dev/null
  fi
done

# Raise number of passes to as many source files you
# call a state through. We were only ever doing 1 file
# deep calls, but we've had it set to 2 just as a safety measure
passes=2

for ((i = 0; i < $passes; i++)); do
  for f in $script_dir*.scon; do
    if [ -f "$f" ]; then 
      python "$transpiler" "$f" \
        -o "${ext_dir}$(basename ${f%.*}).ext" \
        --externs "${ext_dir}"*.ext \
        --generate-externs > /dev/null
    fi
  done
done

# Write the final 
for f in $script_dir*.scon; do
  if [ -f "$f" ]; then 
    python "$transpiler" "$f" -o \
      "${output_dir}$(basename ${f%.*}).con" \
      --externs "${ext_dir}"*.ext
  fi
done
