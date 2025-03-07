# Makefile

# Define the compilers.
CC    = gcc
CXX   = g++

# Compiler flags.
CFLAGS    = -Wall -g -std=c99
CXXFLAGS  = -Wall -g -std=c++17

# List of object files.
OBJS = aiger.o aiger_cpp.o test.o

# Default target.
all: test

# Compile the C file.
aiger.o: aiger.c aiger.h
	$(CC) $(CFLAGS) -c aiger.c -o aiger.o

# Compile the C++ file for the C++ part.
aiger_cpp.o: aiger.cpp aiger.hpp
	$(CXX) $(CXXFLAGS) -c aiger.cpp -o aiger_cpp.o

# Compile the test file.
test.o: test.cpp aiger.hpp
	$(CXX) $(CXXFLAGS) -c test.cpp -o test.o

# Link all object files into the final executable.
test: $(OBJS)
	$(CXX) $(CXXFLAGS) $(OBJS) -o test

# Clean up generated files.
clean:
	rm -f $(OBJS) test

