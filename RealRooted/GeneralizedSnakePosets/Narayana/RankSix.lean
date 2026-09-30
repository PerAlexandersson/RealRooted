import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts

/-!
# Rank-six modified-Narayana certificate

This module contains fixed-length root-list bridges and the explicit root,
sign, interval, and cross-inequality certificate proving the rank-six instance
of Braun--Jal Lemma 3.3.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Differ-by-one interlacing for a quadratic whose roots lie between the
ordered roots of a cubic. -/
theorem interlaces_of_quadratic_cubic_root_lists
    {g f : ℝ[X]} {a b c u v : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2)
    (hf_roots : f.roots = (↑[a, b, c] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c) :
    Interlaces g f :=
  Interlaces.of_quadratic_cubic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc huv hau hub hbv hvc

end GeneralizedSnakePosets
end RealRooted
