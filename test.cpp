// test_aiger.cpp
#include "aiger.hpp"         // Our C++ Aiger class
extern "C" {
  #include "aiger.h"         // The original C AIGER library header
}
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <string>
#include <cassert>

using namespace aiger_cxx;

// Helper: compare two symbol arrays (C++ vs. C)
bool compareSymbols(const std::vector<AigerSymbol>& cppSymbols, const aiger_symbol* cSymbols, size_t cCount, const char* typeName) {
    if (cppSymbols.size() != cCount) {
        std::cerr << "Mismatch in number of " << typeName << " symbols: C++ has " 
                  << cppSymbols.size() << ", C has " << cCount << "\n";
        return false;
    }
    for (size_t i = 0; i < cppSymbols.size(); ++i) {
        if (cppSymbols[i].lit != cSymbols[i].lit) {
            std::cerr << "Mismatch in " << typeName << " literal at index " << i << ": C++ = " 
                      << cppSymbols[i].lit << ", C = " << cSymbols[i].lit << "\n";
            return false;
        }
        std::string cppName = cppSymbols[i].name;
        std::string cName = cSymbols[i].name ? cSymbols[i].name : "";
        if (cppName != cName) {
            std::cerr << "Mismatch in " << typeName << " name at index " << i << ": C++ = " 
                      << cppName << ", C = " << cName << "\n";
            return false;
        }
    }
    return true;
}

// Helper: compare AND gates (C++ vs. C)
bool compareAnds(const std::vector<AigerAnd>& cppAnds, const aiger_and* cAnds, size_t cCount) {
    if (cppAnds.size() != cCount) {
        std::cerr << "Mismatch in number of AND gates: C++ has " 
                  << cppAnds.size() << ", C has " << cCount << "\n";
        return false;
    }
    for (size_t i = 0; i < cppAnds.size(); ++i) {
        if (cppAnds[i].lhs != cAnds[i].lhs ||
            cppAnds[i].rhs0 != cAnds[i].rhs0 ||
            cppAnds[i].rhs1 != cAnds[i].rhs1) {
            std::cerr << "Mismatch in AND gate at index " << i << "\n";
            return false;
        }
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " input_file.aag or input_file.aig\n";
        return EXIT_FAILURE;
    }
    std::string filename = argv[1];

    // -------------------------------
    // Read circuit using original C implementation
    // -------------------------------
    aiger* cCircuit = aiger_init();
    const char* cError = aiger_open_and_read_from_file(cCircuit, filename.c_str());
    if (cError) {
        std::cerr << "C read error: " << cError << "\n";
        aiger_reset(cCircuit);
        return EXIT_FAILURE;
    }
    std::cout << "C circuit read successfully.\n";

    // -------------------------------
    // Read circuit using C++ implementation
    // -------------------------------
    Aiger cppCircuit;
    std::string error = cppCircuit.readFromFile(filename);
    if (!error.empty()) {
        std::cerr << "C++ read error: " << error << "\n";
        return EXIT_FAILURE;
    }
    std::cout << "C++ circuit read successfully.\n";

    // -------------------------------
    // Compare components between C++ and C circuits.
    // -------------------------------
    bool ok = true;
    ok = ok && compareSymbols(cppCircuit.getInputs(), cCircuit->inputs, cCircuit->num_inputs, "input");
    ok = ok && compareSymbols(cppCircuit.getLatches(), cCircuit->latches, cCircuit->num_latches, "latch");
    ok = ok && compareSymbols(cppCircuit.getOutputs(), cCircuit->outputs, cCircuit->num_outputs, "output");
    ok = ok && compareSymbols(cppCircuit.getBad(), cCircuit->bad, cCircuit->num_bad, "bad");
    ok = ok && compareSymbols(cppCircuit.getConstraints(), cCircuit->constraints, cCircuit->num_constraints, "constraint");
    ok = ok && compareSymbols(cppCircuit.getJustice(), cCircuit->justice, cCircuit->num_justice, "justice");
    ok = ok && compareSymbols(cppCircuit.getFairness(), cCircuit->fairness, cCircuit->num_fairness, "fairness");
    ok = ok && compareAnds(cppCircuit.getAnds(), cCircuit->ands, cCircuit->num_ands);
    // Compare comments (assuming C++ comments vector and C comments are stored as an array of char* terminated by NULL)
    size_t cCommentsCount = 0;
    if (cCircuit->comments) {
        while (cCircuit->comments[cCommentsCount] != nullptr)
            ++cCommentsCount;
    }
    if (cppCircuit.getComments().size() != cCommentsCount) {
        std::cerr << "Mismatch in number of comments: C++ " << cppCircuit.getComments().size() 
                  << ", C " << cCommentsCount << "\n";
        ok = false;
    }
    if (ok)
        std::cout << "Circuits match between C++ and C implementations.\n";
    else
        std::cerr << "Circuits do NOT match!\n";

    // -------------------------------
    // Write out the circuit using the C++ functions (both ASCII and binary)
    // -------------------------------
    if (!cppCircuit.writeToFile(Mode::Ascii, "cpp_output.aag")) {
        std::cerr << "C++ failed to write ASCII output.\n";
        return EXIT_FAILURE;
    }
    if (!cppCircuit.writeToFile(Mode::Binary, "cpp_output.aig")) {
        std::cerr << "C++ failed to write binary output.\n";
        return EXIT_FAILURE;
    }
    std::cout << "C++ outputs written to 'cpp_output.aag' and 'cpp_output.aig'.\n";

    // -------------------------------
    // Write out the circuit using the C functions.
    // (Assuming the C library provides aiger_open_and_write_to_file.)
    // -------------------------------
    if (!aiger_open_and_write_to_file(cCircuit, "c_output.aag")) {
        std::cerr << "C failed to write ASCII output.\n";
        aiger_reset(cCircuit);
        return EXIT_FAILURE;
    }
    if (!aiger_open_and_write_to_file(cCircuit, "c_output.aig")) {
        std::cerr << "C failed to write binary output.\n";
        aiger_reset(cCircuit);
        return EXIT_FAILURE;
    }
    std::cout << "C outputs written to 'c_output.aag' and 'c_output.aig'.\n";

    // Clean up the C circuit.
    aiger_reset(cCircuit);
    return EXIT_SUCCESS;
}

