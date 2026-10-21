import RealRooted.CoefficientDominance.NewtonDefectRoots

/-!
# Local Newton defects and positive root parameters

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "local-newton-defect-roots"
formalized = "2026-10-11"
references = [
  "KarpenkoVishnyakova2017",
  "AkianGaubertSharify2017",
]

[[theorems]]
name = "RealRooted.NewtonDefectRoots.esym_sq_sub_sq_esym_le"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Off-diagonal elementary-symmetric bound"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.leadingRatio_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear box for the leading-subset ratio"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.defectConstant_le_leadingRatio"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic lower bound for the leading-subset ratio"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear local-defect box for a root parameter"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_mem_quadratic_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic local-defect box for a root parameter"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_div_succ_le"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Adjacent root-parameter separation"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear box in polynomial coefficients"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_mem_quadratic_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic box in polynomial coefficients"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_isEquivalent_coefficientRatio"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Root parameters asymptotic to coefficient ratios"
headline = true
-->

<!-- realrooted-catalog-content -->
# Local Newton defects and positive root parameters

We consider positive, antitone reciprocal parameters $x_i$ and their elementary
symmetric sums $e_k$.  The off-diagonal estimate bounds $e_k^2$ minus the sum
of squared subset products by $2e_{k-1}e_{k+1}$.  Consequently, the ratio of
the leading subset product to $e_k$ lies between $1-2\delta_k$ and $1$, where
$\delta_k=e_{k-1}e_{k+1}/e_k^2$ with the endpoint convention in the module.

Writing $\eta_i=x_i^{-1}$ and $\rho_i=e_i/e_{i+1}$, we prove two-sided
local bounds for each $\eta_i$.  The linear result gives
$(1-2\delta_i)\rho_i\leq\eta_i\leq\rho_i/(1-2\delta_{i+1})$ when the
displayed upper denominator is positive.  If the two relevant defects are at
most $1/4$, the quadratic constant
$C(u)=(1+\sqrt{1-4u})/2$ gives the sharper corresponding bounds.

We also prove an adjacent-parameter separation estimate under the quadratic
hypothesis.  For $a_0\prod_{i<n}(1+x_iX)$ with $a_0>0$, the same linear and
quadratic bounds are expressed directly through coefficient ratios and local
defects.  Finally, if the two adjacent defects tend to zero along a filter,
then the fixed root parameter is asymptotic to its consecutive-coefficient
ratio; no bound on the ambient degrees is assumed.

## References

See [@KarpenkoVishnyakova2017; @AkianGaubertSharify2017].
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.NewtonDefectRoots

end RealRooted.Challenges.NewtonDefectRoots
