#!/bin/bash
# run_aigfuzz_test.sh
# This script runs aigfuzz 100 times, then calls the C++ and C test executables
# to process the generated AIG, and finally uses diff to compare the outputs.

# Create directories for inputs and outputs.
INPUT_DIR="input_files"
CPP_OUT_DIR="cpp_output"
C_OUT_DIR="c_output"
rm -rf "$INPUT_DIR" "$CPP_OUT_DIR" "$C_OUT_DIR"
mkdir -p "$INPUT_DIR" "$CPP_OUT_DIR" "$C_OUT_DIR"

# Loop for 100 iterations.
for seed in $(seq 1 200); do
    echo "===================="
    echo "Seed: $seed"
    
    rm -f cpp_output.aag cpp_output.aig c_output.aag c_output.aig
    # Generate an input AIG file using aigfuzz.
    INPUT_FILE="$INPUT_DIR/input_${seed}.aig"
    echo "Generating input file: $INPUT_FILE"
    ../aiger-tools/aiger/aigfuzz -2 -o "$INPUT_FILE" "$seed"
    
    # Run the C++ test executable.
    # Assume test takes the input file as its only argument and writes output files:
    # "cpp_output.aag" (ASCII) and "cpp_output.aig" (binary) in the current directory.
    echo "Running C++ test executable..."
    ./test "$INPUT_FILE"
    # Rename/move the outputs to include the seed.
    mv cpp_output.aag "$CPP_OUT_DIR/cpp_${seed}.aag"
    mv cpp_output.aig "$CPP_OUT_DIR/cpp_${seed}.aig"
    mv c_output.aag "$C_OUT_DIR/c_${seed}.aag"
    mv c_output.aig "$C_OUT_DIR/c_${seed}.aig"
    
    # Compare ASCII outputs.
    if diff -q "$CPP_OUT_DIR/cpp_${seed}.aag" "$C_OUT_DIR/c_${seed}.aag" > /dev/null; then
        echo "Seed $seed: ASCII outputs match."
    else
        echo "Seed $seed: ASCII outputs DIFFER!"
        exit 1
    fi
    
    # Compare binary outputs.
    if diff -q "$CPP_OUT_DIR/cpp_${seed}.aig" "$C_OUT_DIR/c_${seed}.aig" > /dev/null; then
        echo "Seed $seed: Binary outputs match."
    else
        echo "Seed $seed: Binary outputs DIFFER!"
        exit 1
    fi
done

echo "Test complete. Check the '$CPP_OUT_DIR' and '$C_OUT_DIR' directories and use diff for further comparison."
