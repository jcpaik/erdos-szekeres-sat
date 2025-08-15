import itertools

from lib.sat import SATInstance

def subsets(n, k):
    return itertools.combinations(list(range(n)), k)

def etv(n, a, b, m, flip_cup=True):
    etv = SATInstance()
    v = {(i, j, k):etv.new_var(f"v({i},{j},{k})") for i, j, k in subsets(m, 3)}

    cap = {}

    for i, j in subsets(m, 2):
        for d in range(2, min(a, j - i + 1) + 1):
            cap[(i, j, d)] = etv.new_var(f"cap({i},{j},{d})")

    for i, j in subsets(m, 2):
        # any two points form a 2-cap
        etv.add(cap[(i, j, 2)])
        # no a-cap
        if j - i + 1 >= a:
            etv.add(~cap[(i, j, a)])
        # any d-cap induces (d-1)-cap
        for d in range(3, min(a, j - i + 1) + 1):
            etv.add_implies(cap[(i, j, d)], cap[(i, j, d - 1)])

    for i, j, k in subsets(m, 3):
        # 3-cap
        cap[(i, j, k, 3)] = ~v[(i, j, k)]
        for d in range(4, min(j - i + 2, a) + 1):
            cap[(i, j, k, d)] = etv.new_var(f"cap({i},{j},{k},{d})")

    for i, j, k in subsets(m, 3):
        for d in range(3, min(j - i + 2, a) + 1):
            etv.add_implies(cap[(i, j, k, d)], cap[(i, k, d)])
            if d < a:
                for l in range(k + 1, m):
                    # extending a d-cup
                    etv.add_implies(cap[(i, j, k, d)] & ~v[(j, k, l)], cap[(i, k, l, d + 1)])

    cup = {}

    for i, j in subsets(m, 2):
        for d in range(2, min(b, j - i + 1) + 1):
            cup[(i, j, d)] = etv.new_var(f"cup({i},{j},{d})")

    for i, j in subsets(m, 2):
        # any two points form a 2-cup
        etv.add(cup[(i, j, 2)])
        # no a-cup
        if j - i + 1 >= b:
            etv.add(~cup[(i, j, b)])
        # any d-cup induces (d-1)-cup
        for d in range(3, min(b, j - i + 1) + 1):
            etv.add_implies(cup[(i, j, d)], cup[(i, j, d - 1)])

    if flip_cup:
        for i, j, k in subsets(m, 3):
            # 3-cup
            cup[(i, j, k, 3)] = v[(i, j, k)]
            for d in range(4, min(k - j + 2, b) + 1):
                cup[(i, j, k, d)] = etv.new_var(f"cup({i},{j},{k},{d})")

        for i, j, k in subsets(m, 3):
            for d in range(3, min(k - j + 2, b) + 1):
                etv.add_implies(cup[(i, j, k, d)], cup[(i, k, d)])
                if d < b:
                    for l in range(i):
                        # extending a d-cup
                        etv.add_implies(cup[(i, j, k, d)] & v[(l, i, j)], cup[(l, i, k, d + 1)])
    else:
        for i, j, k in subsets(m, 3):
            # 3-cup
            cup[(i, j, k, 3)] = v[(i, j, k)]
            for d in range(4, min(j - i + 2, b) + 1):
                cup[(i, j, k, d)] = etv.new_var(f"cup({i},{j},{k},{d})")

        for i, j, k in subsets(m, 3):
            for d in range(3, min(j - i + 2, b) + 1):
                etv.add_implies(cup[(i, j, k, d)], cup[(i, k, d)])
                if d < b:
                    for l in range(k + 1, m):
                        # extending a d-cup
                        etv.add_implies(cup[(i, j, k, d)] & v[(j, k, l)], cup[(i, k, l, d + 1)])

    for i, j in subsets(m, 2):
        for d in range(2, n + 1):
            e = n + 2 - d
            if (i, j, d) in cap and (i, j, e) in cup:
                etv.add(~cap[(i, j, d)] | ~cup[(i, j, e)])

    etv.v = v
    etv.cap = cap
    etv.cup = cup
    return etv

def etv_signotope(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    v = etvp.v
    for i, j, k, l in subsets(m, 4):
        p = v[(i, j, k)]
        q = v[(i, j, l)]
        r = v[(i, k, l)]
        s = v[(j, k, l)]

        etvp.add_implies(p & s, q)
        etvp.add_implies(q & s, r)
        etvp.add_implies(p & r, q)

        etvp.add_implies(~p & ~s, ~q)
        etvp.add_implies(~q & ~s, ~r)
        etvp.add_implies(~p & ~r, ~q)

    return etvp

def etv_ax4(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    v = etvp.v
    for i, j, k, l in subsets(m, 4):
        p = v[(i, j, k)]
        q = v[(i, j, l)]
        r = v[(i, k, l)]
        s = v[(j, k, l)]

        etvp.add_implies(p & ~q & r, s)
        etvp.add_implies(~p & q & ~r, ~s)

    return etvp

def etv_ax4_interior(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    v = etvp.v
    for i, j, k, l in subsets(m, 4):
        p = v[(i, j, k)]
        q = v[(i, j, l)]
        r = v[(i, k, l)]
        s = v[(j, k, l)]

        etvp.add_implies(p & r, q)
        etvp.add_implies(~p & ~r, ~q)
        etvp.add_implies(q & s, r)
        etvp.add_implies(~q & ~s, ~r)

    return etvp

    
def etv_ax5(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    v = etvp.v
    for i, j, k, l in subsets(m, 4):
        p = v[(i, j, k)]
        q = v[(i, j, l)]
        r = v[(i, k, l)]
        s = v[(j, k, l)]

        etvp.add_implies(p & s, q)
        etvp.add_implies(p & s, r)
        etvp.add_implies(~p & ~s, ~q)
        etvp.add_implies(~p & ~s, ~r)

    return etvp


def etv_semisimple(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    v = etvp.v
    for i, j, k, l in subsets(m, 4):
        p = v[(i, j, k)]
        q = v[(i, j, l)]
        r = v[(i, k, l)]
        s = v[(j, k, l)]

        etvp.add_implies(q & s, r)
        etvp.add_implies(p & r, q)
        etvp.add_implies(~q & ~s, ~r)
        etvp.add_implies(~p & ~r, ~q)

        etvp.add_implies(p & ~q & s, ~r)
        etvp.add_implies(p & ~r & s, ~q)
        etvp.add_implies(~p & q & ~s, r)
        etvp.add_implies(~p & r & ~s, q)

    return etvp

def etv_solution(n, a, b, m):
    etvp = etv(n, a, b, m, flip_cup=True)
    if etvp.solve():
        return {key: val.solution() for key, val in etvp.v.items()}
    else:
        return None
