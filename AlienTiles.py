from pysat.solvers import Gluecard4
from pysat.formula import IDPool
from pysat.pb import PBEnc

def find_min_k(n, c, target_colors):
    
    v = IDPool()
    solver = Gluecard4()
    
    # x[i][j][k]: (i, j) được bấm k lần
    x = {}
    for i in range(n):
        for j in range(n):
            lits = [v.id(f'x_{i}_{j}_{k}') for k in range(c)]
            x[(i, j)] = lits
            solver.append_formula(PBEnc.equals(lits = lits, bound = 1, vpool = v).clauses)

    # ràng buộc mod
    for i in range(n):
        for j in range(n):
            impact_lits, impact_weights = [], []
            for col in range(n):
                for kv in range(1, c):
                    impact_lits.append(x[(i, col)][kv])
                    impact_weights.append(kv)
            for row in range(n):
                if row != i:
                    for kv in range(1, c):
                        impact_lits.append(x[(row, j)][kv])
                        impact_weights.append(kv)

            max_impact = (2 * n - 1) * (c - 1)
            # các giá trị S thỏa mãn
            sums = [m * c + target_colors[(i, j)] for m in range(max_impact // c + 1) 
                             if m * c + target_colors[(i, j)] <= max_impact]
            
            t_vars = [v.id(f'sum_{i}_{j}_{sv}') for sv in sums]
            for idx, sv in enumerate(sums):
                eq_cl = PBEnc.equals(lits = impact_lits, weights = impact_weights, bound = sv, vpool = v).clauses
                for cl in eq_cl: solver.add_clause([-t_vars[idx]] + cl)
            solver.add_clause(t_vars)

    all_x, all_w = [], []
    for i in range(n):
        for j in range(n):
            for kv in range(1, c):
                all_x.append(x[(i, j)][kv])
                all_w.append(kv)

    k_min = n * n * (c - 1)
    
    while solver.solve():
        model = solver.get_model()
        # tính k từ model hiện tại
        current_k = 0
        for lit, weight in zip(all_x, all_w):
            if model[lit-1] > 0:
                current_k += weight
        
        k_min = current_k
        # thêm ràng buộc tìm k bé hơn
        solver.append_formula(PBEnc.atmost(lits = all_x, weights = all_w, bound = k_min - 1, vpool = v).clauses)
    
    return k_min

def solve_alien_general(n, c, k_target):
    v = IDPool()
    solver = Gluecard4()
    
    x, s = {}, {}
    for i in range(n):
        for j in range(n):
            x[(i, j)] = [v.id(f'x_{i}_{j}_{k}') for k in range(c)]
            solver.append_formula(PBEnc.equals(lits = x[(i, j)], bound = 1, vpool = v).clauses)
            s[(i, j)] = [v.id(f's_{i}_{j}_{m}') for m in range(c)]
            solver.append_formula(PBEnc.equals(lits = s[(i, j)], bound = 1, vpool = v).clauses)

    # ràng buộc mod
    for i in range(n):
        for j in range(n):
            impact_lits, impact_weights = [], []
            for col in range(n):
                for k in range(1, c):impact_lits.append(x[(i, col)][k]); impact_weights.append(k)
            for row in range(n):
                if row != i:
                    for k in range(1, c):
                        impact_lits.append(x[(row, j)][k]); impact_weights.append(k)

            max_i = (2 * n - 1) * (c - 1)
            t_vars = [v.id(f't_{i}_{j}_{kv}') for kv in range(max_i + 1)]
            for kv, t_var in enumerate(t_vars):
                eq_cl = PBEnc.equals(lits = impact_lits, weights = impact_weights, bound = kv, vpool = v).clauses
                for cl in eq_cl: solver.add_clause([-t_var] + cl)
            
            solver.append_formula(PBEnc.equals(lits = t_vars, bound = 1, vpool = v).clauses)
            for kv, t_var in enumerate(t_vars):
                solver.add_clause([-t_var, s[(i, j)][kv % c]])

    # tổng số lần bấm = target
    all_x_lits, all_weights = [], []
    for i in range(n):
        for j in range(n):
            for k in range(1, c):
                all_x_lits.append(x[(i, j)][k]); all_weights.append(k)
    solver.append_formula(PBEnc.equals(lits = all_x_lits, weights = all_weights, bound = k_target, vpool = v).clauses)

    solutions_count = 0
    while solver.solve():
        model = solver.get_model()
        solutions_count += 1
        
        # tìm trạng thái s
        current_colors = {}
        current_s_lits = []
        for i in range(n):
            for j in range(n):
                for m in range(c):
                    if model[s[(i, j)][m]-1] > 0:
                        current_colors[(i, j)] = m
                        current_s_lits.append(s[(i, j)][m])
                        break
        
       # tìm k min với s
        k_min = find_min_k(n, c, current_colors)

        if(k_min == k_target):
            return s
        
        # ràng buộc để tìm trạng thái khác
        solver.add_clause([-lit for lit in current_s_lits])
        
    return None

if __name__ == "__main__":
    n = int(input())
    c = int(input())

    i = 1
    s = solve_alien_general(n, c, i)
    res = s
    while s != None:
        res = s
        i += 1
        s = solve_alien_general(n, c, i)
    print(i - 1)