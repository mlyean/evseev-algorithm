import itertools
import inspect
from functools import wraps
import logging
import sys

root = logging.getLogger()
root.setLevel(logging.DEBUG)

handler = logging.StreamHandler(sys.stdout)
# handler.setLevel(logging.INFO)
# Replace the above with this to disable printing steps:
handler.setLevel(logging.WARNING)

root.addHandler(handler)

_depth = 0

def dump_args(func):
    """
    Decorator to print function call details.

    This includes parameters names and effective values.
    """

    @wraps(func)
    def wrapper(*args, **kwargs):
        global _depth

        func_args = inspect.signature(func).bind(*args, **kwargs).arguments
        func_args_str = ", ".join(map("{0[0]} = {0[1]!s}".format, func_args.items()))
        logging.info("┃ "*_depth + f"{func.__qualname__} ( {func_args_str} )")
        _depth += 1
        result = func(*args, **kwargs)
        if inspect.isgenerator(result):
            result = list(result)
        logging.info("┃ "*(_depth-1) + "┗ " + f"return {result!s}")
        _depth -= 1
        return result

    return wrapper

S.<q, t> = ZZ['q', 't']

# A = (Q, E, B, R) algebraic data
# Q is a set of variables
# E is a pair ([=0], {!=0}) consisting of a list and a set
# B is a list of ints
# R is a dict, keys are triples, values are monomials

@dump_args
def split_into_cases(A):
    Q, E, B, R = A
    for expr in R.values():
        for a in expr.variables():
            if a in E[1]:
                continue

            E1 = (E[0].copy(), E[1].union({a}))
            A1 = (Q, E1, B, R)

            yield from split_into_cases(A1)

            Q2 = Q.copy()
            E2 = (E[0] + [a], E[1].copy())
            R2 = R.copy()
            A2 = reduce_alg_data((Q2, E2, B, R2))

            if A2 is not None:
                yield from split_into_cases(A2)

            return

    Q1 = Q.copy()
    E1 = (E[0].copy(), E[1].copy())
    R1 = R.copy()
    A1 = reduce_alg_data((Q1, E1, B, R1))

    if A1 is not None:
        yield A1


def is_monomial(expr):
    return all(m >= 0 and (f.is_symbol() or f.is_constant()) for f, m in expr.factor_list())


@dump_args
def reduce_alg_data(A):
    # Reduce the number of variables in the algebraic data. Modifies A
    Q, E, B, R = A

    for expr in E[0]:
        if expr.is_constant() and not expr.is_zero():
            return None

    while SR.zero() in E[0]:
        E[0].remove(SR.zero())

    for expr in E[0]:
        if len(expr.factor_list()) > 1: # Temporary hack
            continue
        variables = expr.variables()
        for a in variables:
            # TODO: This does not work as expected, fix this
            sols = solve(expr, a, solution_dict=True)
            if len(sols) != 1:
                continue
            sol = sols[0]
            lhs, rhs = list(sol.items())[0]
            # assert lhs == a
            if not (is_monomial(rhs) and all(w in Q for w in rhs.variables())):
                continue
            # assert a not in rhs.variables()

            if a in E[1]:
                if rhs == 0:
                    return None
                E[1].remove(a)
                for w in rhs.variables():
                    E[1].add(w)

            E0_new = []
            for expr2 in E[0]:
                expr3 = simplify(expr2.subs(a==rhs))
                if expr3 != 0:
                    E0_new.append(expr3)

            E = (E0_new, E[1])
            Q.remove(a)

            to_remove = []
            for k in R:
                R[k] = simplify(R[k].subs(a==rhs))
                if R[k] == 0:
                    to_remove.append(k)
            for k in to_remove:
                del R[k]

            return reduce_alg_data((Q, E, B, R))

    return (Q, E, B, R)


@dump_args
def aggregate(*args):
    return [[sum((l[0][0] for l in args), S.zero())] + sum((l[0][1:] for l in args), [])] + sum((l[1:] for l in args), [])

@dump_args
def general(A):
    Q, E, B, R = A
    if len(R) == 0:
        try:
            used_vars = set().union(*[set(expr.variables()) for expr in E[0]])
            used_vars_tup = tuple(used_vars)
            solutions = solve(E[0], used_vars_tup, solution_dict=True)

            poly_vals = []
            # Interpolate using first 7 primes, improve this
            for p in Primes()[:7]:
                pts = set()
                for system in solutions:
                    variables = list(set(v for expr in system.values() for v in expr.variables()))

                    for pt in itertools.product(range(p), repeat=len(variables)):
                        pair = {k: v for k, v in zip(variables, pt)}
                        pair2 = tuple(int(system[k].subs(pair)) % p if k in system else pair[k] for k in used_vars_tup)
                        if all(val != 0 for val, v in zip(pair2, used_vars_tup) if v in E[1]):
                            pts.add(pair2)

                poly_vals.append((p, len(pts)))

            f = q^len(B) * (q-1)^(len(E[1].difference(used_vars))) * q^len(Q.difference(used_vars.union(E[1]))) * PolynomialRing(QQ, 'x').lagrange_polynomial(poly_vals)(q)
            return [[f]]
        except Exception:
            return [[S.zero(), [Q, E, 0, len(B), 0]]]

    z = B[-1]
    # assert all((u, z, v) not in R and (z, u, v) not in R for u in B for v in B)

    B1 = B.copy()
    B1.remove(z)

    R1 = {k: v for k, v in R.items() if z not in k}
    A1 = (Q, E, B1, R1)

    O1 = general(A1)
    O2 = type_b(A, z)

    return aggregate(O1, O2)

@dump_args
def type_b(A, z):
    Q, E, B, R = A
    # assert z in B

    def P(v1, v2, v3):
        if not (v1, v2, v3) in R:
            return SR.zero()
        return R[(v1, v2, v3)]

    # Step 1
    if not any(k[2] == z for k in R):
        logging.info("┃ "*_depth + "Type B Step 1")
        B1 = B.copy()
        B1.remove(z)

        R1 = {k: v for k, v in R.items() if z not in k}

        A1 = (Q, E, B1, R1)

        O1 = general(A1)
        O1[0][0] *= q-1
        for U in O1[0][1:]:
            U[2] += 1
        for Oi in O1[1:]:
            Oi[1] += 1

        return O1

    # Step 2
    for y in B:
        if any(k[1] == y for k in R):
            continue
        if not any(k[0] == y and k[2] == z for k in R):
            continue
        if not all(k[2] == z for k in R if k[0] == y):
            continue
        logging.info("┃ "*_depth + "Type B Step 2")
        X = [x for x in B if (y, x, z) in R]

        def c(x):
            #assert x in X
            return R[(y, x, z)]

        Q1 = Q.copy()
        E1 = (E[0].copy(), E[1].copy())

        B1 = B.copy()
        B1.remove(X[-1])
        B1.remove(y)

        R1 = dict()
        # Loop could be optimized
        for u, v, w in itertools.product(B1, repeat=3):
            if u in X:
                if v in X:
                    if w in X:
                        # Case 8
                        if (u, v, w) in R and (y, X[-1], z) in R:
                            R1[(u, v, w)] = simplify(R[(u, v, w)] * R[(y, X[-1], z)])
                    else:
                        # Case 4
                        expr = simplify(c(X[-1])^2 * P(u,v,w) - c(u)*c(X[-1])*P(X[-1],v,w) - c(v)*c(X[-1])*P(u,X[-1],w) + c(u)*c(v)*P(X[-1],X[-1],w))
                        if expr != 0:
                            if is_monomial(expr):
                                R1[(u, v, w)] = expr
                            else:
                                duvw = SR.temp_var()
                                R1[(u, v, w)] = duvw
                                Q1.add(duvw)
                                E1[0].append(duvw - expr)
                else:
                    if w in X:
                        # Case 7
                        if (u, v, w) in R:
                            R1[(u, v, w)] = R[(u, v, w)]
                    else:
                        # Case 3
                        expr = simplify(c(X[-1])*P(u,v,w) - c(u)*P(X[-1],v,w))
                        if expr != 0:
                            if is_monomial(expr):
                                R1[(u, v, w)] = expr
                            else:
                                duvw = SR.temp_var()
                                R1[(u, v, w)] = duvw
                                Q1.add(duvw)
                                E1[0].append(duvw - expr)
            else:
                if v in X:
                    if w in X:
                        # Case 6
                        if (u, v, w) in R:
                            R1[(u, v, w)] = R[(u, v, w)]
                    else:
                        # Case 2
                        expr = simplify(c(X[-1])*P(u,v,w) - c(v)*P(u,X[-1],w))
                        if expr != 0:
                            if is_monomial(expr):
                                R1[(u, v, w)] = expr
                            else:
                                duvw = SR.temp_var()
                                R1[(u, v, w)] = duvw
                                Q1.add(duvw)
                                E1[0].append(duvw - expr)
                else:
                    if w in X:
                        # Case 5
                        if (u, v, w) in R:
                            duvw = SR.temp_var()
                            R1[(u, v, w)] = duvw
                            Q1.add(duvw)
                            E1[0].append(duvw*c(X[-1]) - P(u, v, w))
                    else:
                        # Case 1
                        if (u, v, w) in R:
                            R1[(u, v, w)] = R[(u, v, w)]

        A1 = reduce_alg_data((Q1, E1, B1, R1))
        if A1 is None:
            return [[S.zero()]]

        O = aggregate(*[type_b(As, z) for As in split_into_cases(A1)])

        O[0][0] *= t
        for U in O[0][1:]:
            U[4] += 1
        for Oi in O[1:]:
            Oi[3] += 1

        return O

    # Step 3
    M = [v for v in B if all(k[0] != v and k[1] != v for k in R)]

    y_best = None
    L_best = []
    for y in B:
        if any(k[1] == y for k in R):
            continue
        if any(k[0] == y and k[2] not in M for k in R):
            continue
        L = [w for w in M if any((y, x, w) in R for x in B)]
        if y_best is None and L or (z not in L_best and z in L) or (z in L_best and z in L and len(L) < len(L_best)):
            y_best = y
            L_best = L

    if y_best is not None:
        logging.info("┃ "*_depth + "Type B Step 3")
        y = y_best
        L = L_best

        W = L.copy()
        if z in W:
            W.remove(z)

        k = len(W)
        B1 = [x for x in B if x not in L]
        if z not in B1:
            B1.append(z)

        b = SR.temp_var(k)
        Q1 = Q.union(b)
        E1 = (E[0].copy(), E[1].copy())

        R1 = dict()
        for u, v, w in itertools.product(B1, repeat=3):
            if w == z:
                expr = simplify(P(u, v, z) + sum(b[i]*P(u, v, W[i]) for i in range(k)))
                if expr != 0:
                    if is_monomial(expr):
                        R1[(u, v, w)] = expr
                    else:
                        duvw = SR.temp_var()
                        R1[(u, v, w)] = duvw
                        Q1.add(duvw)
                        E1[0].append(duvw - expr)
            else:
                if (u, v, w) in R:
                    R1[(u, v, w)] = R[(u, v, w)]

        A1 = (Q1, E1, B1, R1)
        return aggregate(*[type_b(As, z) for As in split_into_cases(A1)])

    # Step 4
    logging.info("┃ "*_depth + "Type B Step 4")
    return [[S.zero()], [(A, z), 0, 0, 0]]

def alg_data_U(n):
    ctr = 0
    M = [[None] * n for _ in range(n)]
    for k in range(1, n):
        for i in range(n-k):
            j = i + k
            M[i][j] = ctr
            ctr += 1

    R = dict()

    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                R[(M[i][j], M[j][k], M[i][k])] = SR.one()

    return (set(), ([], set()), list(range(ctr)), R)


if __name__ == "__main__":
    for n in range(2, 14):
        print(f"n={n}")
        out = general(alg_data_U(n))
        print(out)
        ans = {}
        for k, v in out[0][0].monomial_coefficients().items():
            if k[1] not in ans:
                ans[k[1]] = 0
            ans[k[1]] += v * q^k[0]
        for k, v in sorted(ans.items()):
            print(f"{k}: {v}")
        print("Sum of squares =", sum(v * q^(2*k) for k, v in ans.items()))
        clear_vars()
