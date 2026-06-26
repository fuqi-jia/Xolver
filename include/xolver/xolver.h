#pragma once
// Xolver — public C++ API umbrella header.
//
// A single include for the entire public surface:
//
//     #include <xolver/xolver.h>
//
// Link against the bundled static library plus the system math libraries:
//
//     g++ -std=c++20 -Iinclude your_app.cpp -Llib -lxolver -lgmp -lmpfr -lpthread
//
// (libxolver.a bundles xolver_core + CaDiCaL + libpoly + the SMT-LIB parser;
//  GMP/MPFR are taken from the system. The prebuilt `bin/xolver` CLI in a
//  release archive is fully static and needs none of this — just run it.)
#include "xolver/Result.h"
#include "xolver/Sort.h"
#include "xolver/Term.h"
#include "xolver/Model.h"
#include "xolver/Proof.h"
#include "xolver/Statistics.h"
#include "xolver/Solver.h"
