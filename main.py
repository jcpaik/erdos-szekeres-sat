# TODO: copy the jupyter notebook codes to here, make it reproducable

import os
import fire
import lib.erdos as erdos
import itertools
from lib.util import binom

def subsets(n, k):
    return itertools.combinations(list(range(n)), k)

etv = {
    "": erdos.etv,
    "signotope": erdos.etv_signotope,
    "ax4": erdos.etv_ax4,
    "ax4_interior": erdos.etv_ax4_interior,
    "ax5": erdos.etv_ax5,
    "semisimple": erdos.etv_semisimple,
    "restrict": erdos.etv_signotope,
}

def main(n, a, b, N, filename=None, order=""):
    inst = etv[order](n, a, b, N)
    if not filename:
        filename = f"etv_{n}_{a}_{b}_{N}"
    if order == "restrict":
        v = inst.v
        for i, j, k, l in subsets(N, 4):
            p = v[(i, j, k)]
            q = v[(i, j, l)]
            r = v[(i, k, l)]
            s = v[(j, k, l)]
            inst.add_implies(p & q & ~s, r)

    if inst.solve(filename):
        print("Solution found")
        sol_filename = filename + ".color"
        with open(sol_filename, "w") as f:
            for triple, var in inst.v.items():
                color = 'R' if var.solution() else 'B'
                line = f"{triple[0]+1} {triple[1]+1} {triple[2]+1} {color}"
                f.write(line + "\n")
        print("Solution stored in " + sol_filename)
    else:
        print("Solution not found")

if __name__ == '__main__':
    fire.Fire(main)
