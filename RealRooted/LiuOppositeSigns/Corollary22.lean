import RealRooted.LiuOppositeSigns.Theorem21Assembly

/-!
# Liu bounded theorem packages

This module contains bounded endpoint and low-degree theorem packages derived
from the reverse assembly for Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

end LiuOppositeSigns
end RealRooted
