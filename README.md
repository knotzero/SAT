# SAT Solver Comparison

This project provides a theoretical and experimental comparison of classical SAT solving algorithms: **Resolution**, **Davis–Putnam (DP)**, and **Davis–Putnam–Logemann–Loveland (DPLL)**. The solvers are implemented in Python, and their performance is benchmarked using various CNF instances from SATLIB.

## 📌 Purpose

The goal of this project is to:
- Understand the core principles behind foundational SAT algorithms.
- Evaluate their performance and scalability.
- Highlight the practical benefits of techniques such as backtracking, unit propagation, and clause learning used in modern SAT solvers.

## 🧠 Algorithms Implemented

1. **Resolution Method**
   - Refutation-based; derives contradictions through clause resolution.
2. **Davis–Putnam (DP) Algorithm**
   - Performs variable elimination using resolution.
3. **Davis–Putnam–Logemann–Loveland (DPLL) Algorithm**
   - Recursive backtracking solver using unit propagation and pure literal elimination.

## 🧪 How to Use

### Requirements
- Python 3.x

### Running the Code

Each solver is implemented as a Python script. You can run them on CNF files (in DIMACS format) as follows:

```bash
py PATH_TO/sat.py path/to/TEST_FOLDER
```

## 📝 Input Format

```
p cnf [variables] [clauses]
[clause 1 literals] 0
[clause 2 literals] 0
...
```
