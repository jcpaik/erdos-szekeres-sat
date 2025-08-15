# TODO: copy the jupyter notebook codes to here, make it reproducable

import os
import fire
import lib.erdos as erdos
from lib.util import binom

etv = {
    "": erdos.etv,
    "signotope": erdos.etv_signotope,
    "ax4": erdos.etv_ax4,
    "ax4_interior": erdos.etv_ax4_interior,
    "ax5": erdos.etv_ax5,
    "semisimple": erdos.etv_semisimple,
}

def main(n, a, b, N, filename=None, order=""):
    inst = etv[order](n, a, b, N)
    if not filename:
        filename = f"etv_{n}_{a}_{b}_{N}"
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
