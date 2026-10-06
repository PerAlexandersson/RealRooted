#!/usr/bin/env python3
"""Generate the universal kernel certificate of the 321 big-descent theorem (issue #1143).

Reads `scripts/data/big_descents_certificate.json`: the 89 integer terms of the numerator p_0
(an entry [a, b, c, z] means z R^a X^b k^c) and the positive denominator L.  The script then

* forms N = dP and H~ = 2LN - (R-k)(R+k-3)(R+2X+k+1) p_0(k+1) + 2k(2X+2k+7)(R+X+k+2) p_0(k),
* checks the rational telescoping identity P - rho g(k+1) + g(k) = H~ / (2Ld),
* computes the Bernstein coefficients h of 27720 H~(7+s, X, (7+s)v) in degree 12,
* checks that they are nonnegative integers with h_000 > 0, and that
  27720 R^12 H~(R, X, k) = P_+(R-7, X, k, R-k) with
  P_+(S, X, K, T) = sum h_(a,b,i) C(12,i) S^a X^b K^i T^(12-i).

It writes `RealRooted/CombinatorialExamples/BigDescents321/Certificate/Data.lean`, holding the
reflected expressions and the `decide +kernel` checks.  Lean checks every identity and sign;
this script only produces the data.

Requires sympy.  Usage: python3 scripts/gen_big_descents_certificate.py
"""
import json
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path

import sympy as sp

WIDTH = 100
DEG = 12
SHIFT = 7
ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "scripts/data/big_descents_certificate.json"
OUT = ROOT / "RealRooted/CombinatorialExamples/BigDescents321/Certificate/Data.lean"

R, X, k = sp.symbols("R X k")


def F(r, J, kk):
    return kk * (4 * J + 3 * kk + 2 * r + 5) - r * (r - 1)


def certificate():
    d = json.loads(DATA.read_text())
    assert d["shift"] == SHIFT and d["bernstein_degree"] == DEG
    L = int(d["denominator"])
    p0 = [(a, b, c, int(z)) for a, b, c, z in d["terms"]]
    return L, p0


def compute(L, p0terms):
    p0 = sum(sp.Integer(z) * R**a * X**b * k**c for a, b, c, z in p0terms)
    A = (X + 3) * (2 * X + 7)
    B = (X + 2) * (2 * X + 3)
    L1 = ((R - k) * (R + 2 * X + k + 2) * (R + 2 * X + k + 3) * (R + 2 * X + k + 4)
          / (4 * (R + k - 2) * (2 * X + 2 * k + 5) * (2 * X + 2 * k + 7) * (R + X + k + 2)))
    L2 = ((R - k) * (R - k - 1) * (R + 2 * X + k + 2) * (R + 2 * X + k + 3)
          / (4 * (R + k - 3) * (R + k - 2) * (2 * X + 2 * k + 5) * (2 * X + 2 * k + 7)))
    L3 = (R - k) * (R + X + k + 1) / ((R + k - 2) * (R + 2 * X + k + 1))
    P = (4 * A * L1 * F(R - 1, X + 2, k) - 8 * A * L2 * F(R - 2, X + 2, k)
         - B * F(R, X, k) + 2 * B * L3 * F(R - 1, X, k))
    dd = ((R + k - 3) * (R + k - 2) * (2 * X + 2 * k + 5) * (2 * X + 2 * k + 7)
          * (R + X + k + 2) * (R + 2 * X + k + 1))
    dg = (R + k - 3) * (R + k - 2) * (2 * X + 2 * k + 5) * (R + 2 * X + k + 1)
    N = sp.cancel(sp.together(dd * P))
    Ht = (2 * L * N - (R - k) * (R + k - 3) * (R + 2 * X + k + 1) * p0.subs(k, k + 1)
          + 2 * k * (2 * X + 2 * k + 7) * (R + X + k + 2) * p0)
    Ht = sp.expand(Ht)
    rho = ((R + k - 1) * (R - k) * (2 * X + R + k + 2)
           / (4 * (k + 1) * (X + k + sp.Rational(5, 2)) * (X + k + R + 2)))

    def g(kk):
        return kk * p0.subs(k, kk) / (L * dg.subs(k, kk))

    num, _ = sp.fraction(sp.together(P - rho * g(k + 1) + g(k) - Ht / (2 * L * dd)))
    assert sp.expand(num) == 0, "telescoping identity fails"
    return {e: int(z) for e, z in sp.Poly(Ht, R, X, k).as_dict().items()}


def bernstein(Ht):
    """Coefficients of P_+(S, X, K, T), keyed by exponents (a, b, i, 12 - i)."""
    Q = defaultdict(int)
    for (a, b, c), z in Ht.items():
        n = a + c
        for j in range(n + 1):
            Q[(j, b, c)] += z * comb(n, j) * SHIFT ** (n - j)
    h = defaultdict(Fraction)
    for (a, b, c), z in Q.items():
        for i in range(c, DEG + 1):
            h[(a, b, i)] += Fraction(27720 * z * comb(i, c), comb(DEG, c))
    assert all(x.denominator == 1 and x >= 0 for x in h.values()), "h is not in ℕ"
    h = {e: int(x) for e, x in h.items() if x}
    assert h[(0, 0, 0)] > 0
    Pp = {(a, b, i, DEG - i): x * comb(DEG, i) for (a, b, i), x in h.items()}
    rhs = defaultdict(int)
    for (a, b, i, t), x in Pp.items():
        for j in range(a + 1):
            c1 = comb(a, j) * (-SHIFT) ** (a - j)
            for m in range(t + 1):
                rhs[(j + m, b, i + t - m)] += x * c1 * comb(t, m) * (-1) ** (t - m)
    rhs = {e: z for e, z in rhs.items() if z}
    assert rhs == {(a + DEG, b, c): 27720 * z for (a, b, c), z in Ht.items()}
    return Pp


NAMES = ["aS", "aX", "aK", "aT"]
# Horner order of the variables of `P₊`: `X` outermost, then `S`, `K`, `T`.
ORDER = [1, 0, 2, 3]


def horner(terms, order, i=0):
    """Horner form of `terms`, whose exponent tuples list the variables `NAMES[o]` for `o` in
    `order`, as a reflected `Expr`."""
    if i == len(order):
        return f"(c {terms[()]})"
    groups = defaultdict(dict)
    for e, z in terms.items():
        groups[e[0]][e[1:]] = z
    exps = sorted(groups, reverse=True)
    v = NAMES[order[i]]
    acc = horner(groups[exps[0]], order, i + 1)
    cur = exps[0]
    for e in exps[1:]:
        gap = cur - e
        m = v if gap == 1 else f"(.pow {v} {gap})"
        acc = f"(.add (.mul {acc} {m}) {horner(groups[e], order, i + 1)})"
        cur = e
    if cur > 0:
        m = v if cur == 1 else f"(.pow {v} {cur})"
        acc = f"(.mul {acc} {m})"
    return acc


def wrap(head, text, indent="    "):
    """`head` followed by `text`, broken at spaces to fit WIDTH."""
    lines, cur = [], head
    for tok in text.split(" "):
        if len(cur) + 1 + len(tok) > WIDTH:
            lines.append(cur)
            cur = indent + tok
        else:
            cur += " " + tok
    lines.append(cur)
    return "\n".join(lines) + "\n"


def term_list(name, doc, rows):
    out = f"/-- {doc} -/\ndef {name} : List (ℕ × ℕ × ℕ × ℤ) := [\n"
    out += ",\n".join(f"  ({a}, {b}, {c}, {z})" for a, b, c, z in rows) + "]\n\n"
    return out


HEADER = '''/-
Generated by scripts/gen_big_descents_certificate.py; do not edit by hand.
-/
import RealRooted.CombinatorialExamples.BigDescents321.Certificate.Reflect

/-!
# Data of the universal kernel certificate

The reflected polynomials of the certificate in issue #1143, §11, with their kernel checks:

* `htildeE`, the polynomial `H̃(R, X, k)`, built from `N = dP`, the numerator `p₀` and `L`;
* `htData`, the expanded coefficients of `H̃`, split by the degree in `X`;
* `pplusE`, the polynomial `P₊(S, X, K, T)` with natural-number coefficients, split the same way;
* `htilde_check`: `H̃` equals its expansion;
* `chunk_check_*`: `27720 R¹² H̃ = P₊(R - 7, X, k, R - k)`, one `X`-degree at a time;
* `prest_posB`: every coefficient of `P₊` other than `h₀₀₀ T¹²` is nonnegative.
-/

namespace RealRooted.BigDescents321.CertData

open Lean.Grind.CommRing RealRooted.BigDescents321.Reflect

/-- The variable `R`. -/
abbrev vR : Expr := .var 0
/-- The variable `X`. -/
abbrev vX : Expr := .var 1
/-- The variable `k`. -/
abbrev vk : Expr := .var 2
/-- An integer constant. -/
abbrev c (z : ℤ) : Expr := .num z

/-- `F(r, J, k) = k(4J + 3k + 2r + 5) - r(r - 1)`. -/
def fE (r J k : Expr) : Expr :=
  .sub (.mul k (.add (.add (.add (.mul (c 4) J) (.mul (c 3) k)) (.mul (c 2) r)) (c 5)))
    (.mul r (.sub r (c 1)))

/-- The affine form `aR + bX + dk + e`. -/
def lin (a b d e : ℤ) : Expr :=
  .add (.add (.add (.mul (c a) vR) (.mul (c b) vX)) (.mul (c d) vk)) (c e)

/-- `A = (X + 3)(2X + 7)`. -/
def aE : Expr := .mul (lin 0 1 0 3) (lin 0 2 0 7)
/-- `B = (X + 2)(2X + 3)`. -/
def bE : Expr := .mul (lin 0 1 0 2) (lin 0 2 0 3)

/-- `N = dP`, an integer polynomial of total degree `10`. -/
def nE : Expr :=
  .add (.sub (.sub
    (List.foldr .mul (fE (.sub vR (c 1)) (.add vX (c 2)) vk)
      [aE, lin 1 0 (-1) 0, lin 1 2 1 2, lin 1 2 1 3, lin 1 2 1 4, lin 1 0 1 (-3), lin 1 2 1 1])
    (List.foldr .mul (fE (.sub vR (c 2)) (.add vX (c 2)) vk)
      [c 2, aE, lin 1 0 (-1) 0, lin 1 0 (-1) (-1), lin 1 2 1 2, lin 1 2 1 3, lin 1 1 1 2,
        lin 1 2 1 1]))
    (.mul bE (.mul (fE vR vX vk) (List.foldr .mul (c 1)
      [lin 1 0 1 (-3), lin 1 0 1 (-2), lin 0 2 2 5, lin 0 2 2 7, lin 1 1 1 2, lin 1 2 1 1]))))
    (List.foldr .mul (fE (.sub vR (c 1)) vX vk)
      [c 2, bE, lin 1 0 (-1) 0, lin 1 1 1 1, lin 1 0 1 (-3), lin 0 2 2 5, lin 0 2 2 7,
        lin 1 1 1 2])

'''

MIDDLE = '''/-- `H̃ = 2LN - (R - k)(R + k - 3)(R + 2X + k + 1) p₀(k + 1)
+ 2k(2X + 2k + 7)(R + X + k + 2) p₀(k)`. -/
def htildeE : Expr :=
  .add (.sub (.mul (.mul (c 2) (c lden)) nE)
    (List.foldr .mul (termsExpr vR vX (.add vk (c 1)) p0Data)
      [lin 1 0 (-1) 0, lin 1 0 1 (-3), lin 1 2 1 1]))
    (List.foldr .mul (termsExpr vR vX vk p0Data) [c 2, vk, lin 0 2 2 7, lin 1 1 1 2])

'''


def main():
    L, p0 = certificate()
    Ht = compute(L, p0)
    Pp = bernstein(Ht)
    bs = sorted({e[1] for e in Pp})
    assert bs == sorted({e[1] for e in Ht})
    out = HEADER
    out += term_list("p0Data", "The terms of the certificate numerator `p₀`.", p0)
    out += "/-- The certificate denominator `L`. -/\n"
    out += f"def lden : ℤ := {L}\n\n" if len(str(L)) < 80 else wrap("def lden : ℤ :=", str(L))
    out += MIDDLE
    for b in bs:
        rows = [(a, bb, cc, z) for (a, bb, cc), z in sorted(Ht.items()) if bb == b]
        out += term_list(f"ht{b}", f"The terms of `H̃` of degree `{b}` in `X`.", rows)
    out += "/-- All terms of `H̃`. -/\n"
    out += "def htData : List (ℕ × ℕ × ℕ × ℤ) :=\n  " + " ++ ".join(f"ht{b}" for b in bs)
    out += "\n\n"
    for i, (nm, var) in enumerate(zip(NAMES, "SXKT")):
        out += f"/-- The variable `{var}` of `P₊`. -/\nabbrev {nm} : Expr := .var {i}\n"
    out += "\n"
    key0 = (0, 0, 0, DEG)
    out += "/-- The distinguished positive term `h₀₀₀ T¹²` of `P₊`. -/\n"
    out += wrap("def pTop : Expr :=", f".mul (c {Pp[key0]}) (.pow aT 12)", "  ")
    out += "\n"
    for b in bs:
        sub = {e: z for e, z in Pp.items() if e[1] == b and e != key0}
        out += f"/-- The terms of `P₊ - h₀₀₀ T¹²` of degree `{b}` in `X`. -/\n"
        perm = {tuple(e[o] for o in ORDER): z for e, z in sub.items()}
        out += wrap(f"def pp{b} : Expr :=", horner(perm, ORDER), "    ")
        out += "\n"
    out += "/-- `P₊ - h₀₀₀ T¹²`. -/\ndef prestE : Expr :=\n  "
    out += " (".join(f".add pp{b}" for b in bs[:-1]) + f" pp{bs[-1]}" + ")" * (len(bs) - 2)
    out += "\n\n"
    out += '''/-- `P₊(S, X, K, T)`, a polynomial with natural-number coefficients. -/
def pplusE : Expr := .add pTop prestE

/-- The substitution `S = R - 7`, `X = X`, `K = k`, `T = R - k`. -/
def σ : ℕ → Expr
  | 0 => .sub vR (c 7)
  | 1 => vX
  | 2 => vk
  | _ => .sub vR vk

/-! ### Kernel checks -/

theorem htilde_check : check htildeE (termsExpr vR vX vk htData) = true := by
  decide +kernel

'''
    for b in bs:
        rhs = "(.add pTop pp0)" if b == 0 else f"pp{b}"
        out += f"theorem chunk_check_{b} :\n"
        out += f"    check (.mul (c 27720) (.mul (.pow vR 12) (termsExpr vR vX vk ht{b})))\n"
        out += f"      (subst σ {rhs}) = true := by\n  decide +kernel\n\n"
    out += "theorem prest_posB : PosB prestE = true := by\n  decide +kernel\n\n"
    out += "end RealRooted.BigDescents321.CertData\n"
    for n, line in enumerate(out.splitlines(), 1):
        assert len(line) <= WIDTH, f"line {n} too long"
    OUT.write_text(out)
    print(f"wrote {OUT.relative_to(ROOT)}: {len(Ht)} terms of H~, {len(Pp)} of P+, "
          f"X-degrees {bs}")


if __name__ == "__main__":
    main()
