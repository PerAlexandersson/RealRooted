import RealRooted.Kurtz

/-!
# Kurtz challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "kurtz"
authors = ["Kurtz"]
years = [1992]

[[definitions]]
name = "RealRooted.Kurtz.PositiveCoeffsUpToDegree"
module = "RealRooted.Kurtz"
label = "Positive coefficients"

[[definitions]]
name = "RealRooted.Kurtz.KurtzStrictInequalities"
module = "RealRooted.Kurtz"
label = "Kurtz inequalities a_k² > 4 a_{k-1} a_{k+1}"

[[theorems]]
name = "RealRooted.Kurtz.coefficient_criterion"
module = "RealRooted.Kurtz"
label = "Kurtz's criterion"
-->

<!-- realrooted-catalog-content -->
# Kurtz’s coefficient criterion

If a polynomial $\sum_{k=0}^n a_k x^k$ of degree $n \geq 2$ has positive
coefficients and $a_k^2 > 4a_{k-1}a_{k+1}$ for $0 < k < n$, then all its roots
are real. Kurtz also shows that the roots are distinct; the Lean statement
records real-rootedness only.

## References

D. C. Kurtz, “A sufficient condition for all the roots of a polynomial to be
real,” *American Mathematical Monthly* 99 (1992), 259–263.  See also the
[contextual account on symmetricfunctions.com](https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem

Original references: J. I. Hutchinson, "On a remarkable class of entire
functions", Trans. Amer. Math. Soc. 25 (1923), 325--332, and D. C. Kurtz,
"A sufficient condition for all the roots of a polynomial to be real",
Amer. Math. Monthly 99 (1992), 259--263.

This module exposes the reusable theorem implementation in `RealRooted.Kurtz`.
-/

namespace RealRooted
namespace Challenges
namespace Kurtz

export RealRooted.Kurtz
  (PositiveCoeffsUpToDegree
    KurtzStrictInequalities
    coefficient_criterion)

end Kurtz
end Challenges
end RealRooted
