import time
import matplotlib.pyplot as plt
from pysat.formula import CNF
from pysat.solvers import Solver
import os
from tabulate import tabulate
import glob
import pandas as pd

class BaseSAT:
    def __init__(self):
        self.stats = {
            'decisions': 0,
            'propagations': 0,
            'conflicts': 0,
            'time': 0
        }
    
    def reset_stats(self):
        for k in self.stats:
            self.stats[k] = 0

class ResolutionSolver(BaseSAT):
    def __init__(self, max_clauses=10000):
        super().__init__()
        self.name = "Resolution"
        self.max_clauses = max_clauses
    
    def solve(self, cnf):
        start_time = time.time()
        self.reset_stats()
        clauses = [frozenset(clause) for clause in cnf.clauses]
        original_clauses = set(clauses)
        
        while True:
            new_clauses = set()
            n = len(clauses)
            
            if n > self.max_clauses:
                self.stats['time'] = time.time() - start_time
                return (None, None, self.stats)
            
            for i in range(n):
                for j in range(i+1, n):
                    resolvents = self.resolve(clauses[i], clauses[j])
                    self.stats['propagations'] += 1
                    
                    for resolvent in resolvents:
                        if not resolvent:
                            self.stats['time'] = time.time() - start_time
                            return (False, None, self.stats)
                        if resolvent not in original_clauses and resolvent not in new_clauses:
                            new_clauses.add(resolvent)
            
            if not new_clauses:
                self.stats['time'] = time.time() - start_time
                with Solver(bootstrap_with=cnf) as solver:
                    if solver.solve():
                        return (True, {v: solver.get_model()[abs(v)-1] > 0 for v in range(1, cnf.nv+1)}, self.stats)
                    else:
                        return (False, None, self.stats)
            
            original_clauses.update(new_clauses)
            clauses = list(original_clauses)
    
    def resolve(self, c1, c2):
        resolvents = []
        for lit in c1:
            if -lit in c2:
                resolvent = (c1 | c2) - {lit, -lit}
                resolvents.append(frozenset(resolvent))
        return resolvents

class DPSolver(BaseSAT):
    def __init__(self, max_clauses=10000):
        super().__init__()
        self.name = "DP"
        self.max_clauses = max_clauses
    
    def solve(self, cnf):
        start_time = time.time()
        self.reset_stats()
        clauses = [frozenset(clause) for clause in cnf.clauses]
        variables = {abs(lit) for clause in clauses for lit in clause}
        
        while variables:
            if len(clauses) > self.max_clauses:
                self.stats['time'] = time.time() - start_time
                return (None, None, self.stats)
                
            var = variables.pop()
            pos_clauses = [c for c in clauses if var in c]
            neg_clauses = [c for c in clauses if -var in c]
            
            new_clauses = set()
            for pc in pos_clauses:
                for nc in neg_clauses:
                    resolvent = (pc | nc) - {var, -var}
                    self.stats['propagations'] += 1
                    
                    if not resolvent:
                        self.stats['time'] = time.time() - start_time
                        return (False, None, self.stats)
                    
                    if not any(-lit in resolvent for lit in resolvent):
                        new_clauses.add(frozenset(resolvent))
            
            clauses = [c for c in clauses if var not in c and -var not in c]
            clauses.extend(new_clauses)
            
            variables = {abs(lit) for clause in clauses for lit in clause}
        
        self.stats['time'] = time.time() - start_time
        with Solver(bootstrap_with=cnf) as solver:
            if solver.solve():
                return (True, {v: solver.get_model()[abs(v)-1] > 0 for v in range(1, cnf.nv+1)}, self.stats)
            else:
                return (False, None, self.stats)

class DPLLSolver(BaseSAT):
    def __init__(self):
        super().__init__()
        self.name = "DPLL"
    
    def solve(self, cnf):
        start_time = time.time()
        self.reset_stats()
        assignment = {}
        clauses = [set(clause) for clause in cnf.clauses]
        result, assignment = self.dpll(clauses, assignment)
        self.stats['time'] = time.time() - start_time
        return (result, assignment, self.stats)
    
    def dpll(self, clauses, assignment):
        changed = True
        while changed:
            changed = False
            unit_clauses = [c for c in clauses if len(c) == 1]
            
            for unit in unit_clauses:
                lit = next(iter(unit))
                var = abs(lit)
                val = lit > 0
                
                if var in assignment and assignment[var] != val:
                    return False, None
                
                if var not in assignment:
                    assignment[var] = val
                    changed = True
                    self.stats['propagations'] += 1
            
            if changed:
                clauses = self.simplify(clauses, assignment)
                if clauses is None:
                    return False, None
        
        if any(len(c) == 0 for c in clauses):
            return False, None
        
        if not clauses:
            return True, assignment
        
        unassigned_vars = {abs(lit) for clause in clauses for lit in clause} - set(assignment.keys())
        if not unassigned_vars:
            return True, assignment
        
        var = next(iter(unassigned_vars))
        self.stats['decisions'] += 1
        
        new_assignment = assignment.copy()
        new_assignment[var] = True
        new_clauses = self.simplify(clauses.copy(), {var: True})
        result, final_assignment = self.dpll(new_clauses, new_assignment)
        if result:
            return True, final_assignment
        
        new_assignment = assignment.copy()
        new_assignment[var] = False
        new_clauses = self.simplify(clauses.copy(), {var: False})
        result, final_assignment = self.dpll(new_clauses, new_assignment)
        if result:
            return True, final_assignment
        
        self.stats['conflicts'] += 1
        return False, None
    
    def simplify(self, clauses, assignment):
        new_clauses = []
        for clause in clauses:
            new_clause = set(clause)
            for var, val in assignment.items():
                if var in {abs(lit) for lit in clause}:
                    if (val and var in clause) or (not val and -var in clause):
                        new_clause = None
                        break
                    elif val and -var in clause:
                        new_clause.remove(-var)
                    elif not val and var in clause:
                        new_clause.remove(var)
            
            if new_clause is not None:
                if not new_clause:
                    return None
                new_clauses.append(new_clause)
        return new_clauses

def read_cnf_file(filename):
    cnf = CNF()
    with open(filename) as f:
        for line in f:
            if line.startswith('c') or line.startswith('p'):
                continue
            clause = [int(x) for x in line.strip().split() if x != '0']
            if clause:
                cnf.append(clause)
    return cnf

def write_solution(filename, result, assignment):
    with open(filename, 'w') as f:
        if result:
            f.write("SAT\n")
            if assignment:
                for var in sorted(assignment.keys()):
                    val = var if assignment[var] else -var
                    f.write(f"{val} ")
                f.write("0")
        else:
            f.write("UNSAT")

def find_cnf_files(folder_path):
    cnf_files = []
    for root, dirs, files in os.walk(folder_path):
        for file in files:
            if file.lower().endswith('.cnf'):
                cnf_files.append(os.path.join(root, file))
    return sorted(cnf_files)

def benchmark_solvers(test_files, output_dir="results"):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    solvers = [ResolutionSolver(), DPSolver(), DPLLSolver()]
    results = []
    
    for test_file in test_files:
        print(f"\nProcessing {os.path.basename(test_file)}...")
        try:
            cnf = read_cnf_file(test_file)
            file_results = {'filename': os.path.basename(test_file)}
            
            for solver in solvers:
                print(f"  Running {solver.name}...", end=' ', flush=True)
                start_time = time.time()
                result, assignment, stats = solver.solve(cnf)
                elapsed = time.time() - start_time
                
                output_file = os.path.join(
                    output_dir, 
                    f"{os.path.splitext(os.path.basename(test_file))[0]}_{solver.name.lower()}.sol"
                )
                write_solution(output_file, result, assignment)
                
                file_results[f"{solver.name}_time"] = elapsed
                file_results[f"{solver.name}_result"] = "SAT" if result else "UNSAT"
                file_results[f"{solver.name}_decisions"] = stats['decisions']
                file_results[f"{solver.name}_propagations"] = stats['propagations']
                file_results[f"{solver.name}_conflicts"] = stats.get('conflicts', 0)
                print(f"done in {elapsed:.3f}s")
            
            results.append(file_results)
        except Exception as e:
            print(f"\nError processing {test_file}: {str(e)}")
            continue
    
    return results

def generate_report(results, report_image="benchmark_table.png"):
    script_dir = os.path.dirname(os.path.abspath(__file__))
    results_dir = os.path.join(script_dir, "results")
    os.makedirs(results_dir, exist_ok=True)

    df = pd.DataFrame(results)

    fig, ax = plt.subplots(figsize=(len(df.columns) * 2, len(df) * 0.6 + 1))
    ax.axis('off')
    table = ax.table(cellText=df.values, colLabels=df.columns, loc='center', cellLoc='center')

    table.auto_set_font_size(False)
    table.set_fontsize(10)

    col_widths = []
    for col in df.columns:
        max_len = max(
            df[col].astype(str).map(len).max(),
            len(str(col))
        )
        col_widths.append(max(1.0, min(max_len / 5, 3.0)))

    for i, width in enumerate(col_widths):
        for key, cell in table.get_celld().items():
            if key[1] == i:
                cell.set_width(width / sum(col_widths))

    table.scale(1, 1.5)
    table_path = os.path.join(results_dir, report_image)
    plt.tight_layout()
    plt.savefig(table_path, dpi=300)
    plt.close()

    plot_paths = [
        ("time_comparison.png", "_time", "Time (s)", "Solver Time Comparison"),
        ("decisions_comparison.png", "_decisions", "Decisions", "Solver Decisions Comparison"),
        ("propagations_comparison.png", "_propagations", "Propagations", "Solver Propagations Comparison")
    ]

    for filename, metric_suffix, ylabel, title in plot_paths:
        plot_path = os.path.join(results_dir, filename)
        plot_comparison(results, plot_path, metric_suffix, ylabel, title)

def plot_comparison(results, filename, metric_suffix, ylabel, title):
    if not results:
        return
    
    solvers = ["Resolution", "DP", "DPLL"]
    test_files = [res['filename'] for res in results]
    
    data = {solver: [] for solver in solvers}
    for res in results:
        for solver in solvers:
            data[solver].append(res[f"{solver}{metric_suffix}"])
    
    plt.figure(figsize=(12, 6))
    x = range(len(test_files))
    width = 0.25
    
    for i, solver in enumerate(solvers):
        plt.bar([pos + i * width for pos in x], data[solver], width, label=solver)
    
    plt.xlabel('Test Cases')
    plt.ylabel(ylabel)
    plt.title(title)
    plt.xticks([pos + width for pos in x], test_files, rotation=45, ha='right')
    plt.legend()
    plt.tight_layout()
    plt.savefig(filename)
    plt.close()
    print(f"Plot saved to {filename}")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="SAT Solver Comparison Tool")
    parser.add_argument('mode', choices=['solve', 'benchmark'], help="Run mode")
    parser.add_argument('-i', '--input', help="Input CNF file (for solve mode)")
    parser.add_argument('-o', '--output', help="Output solution file (for solve mode)")
    parser.add_argument('-s', '--solver', choices=['resolution', 'dp', 'dpll'], 
                        help="Solver to use (for solve mode)")
    parser.add_argument('-t', '--tests', help="Test folder for benchmark mode")
    parser.add_argument('--max_tests', type=int, default=20, 
                       help="Maximum number of tests to run in benchmark mode")
    args = parser.parse_args()
    
    if args.mode == 'solve':
        if not args.input or not args.output or not args.solver:
            parser.error("solve mode requires input, output, and solver arguments")
        
        solver_map = {
            'resolution': ResolutionSolver,
            'dp': DPSolver,
            'dpll': DPLLSolver
        }
        
        print(f"Solving {args.input} with {args.solver} solver...")
        cnf = read_cnf_file(args.input)
        solver = solver_map[args.solver]()
        result, assignment, stats = solver.solve(cnf)
        write_solution(args.output, result, assignment)
        
        print(f"\nResult: {'SAT' if result else 'UNSAT'}")
        if result:
            print("Assignment:", " ".join(f"{var if val else -var}" for var, val in sorted(assignment.items())))
        print(f"Time: {stats['time']:.3f}s")
        print(f"Decisions: {stats['decisions']}")
        print(f"Propagations: {stats['propagations']}")
        if 'conflicts' in stats:
            print(f"Conflicts: {stats['conflicts']}")
        
    elif args.mode == 'benchmark':
        if not args.tests:
            parser.error("benchmark mode requires test folder")
        
        if not os.path.isdir(args.tests):
            parser.error(f"Test folder not found: {args.tests}")
        
        print(f"Scanning {args.tests} for CNF files...")
        test_files = find_cnf_files(args.tests)
        
        if not test_files:
            parser.error(f"No CNF files found in {args.tests}")
        
        if len(test_files) > args.max_tests:
            print(f"Found {len(test_files)} test files. Limiting to first {args.max_tests}.")
            test_files = test_files[:args.max_tests]
        
        print(f"Found {len(test_files)} test files:")
        for f in test_files:
            print(f"  {os.path.basename(f)}")
        
        print("\nRunning benchmark...")
        results = benchmark_solvers(test_files)
        generate_report(results)

if __name__ == "__main__":
    main()
