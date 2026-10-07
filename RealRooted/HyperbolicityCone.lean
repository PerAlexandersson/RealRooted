import RealRooted.Hyperbolicity

/-!
# Gårding: hyperbolicity cones are convex

For a homogeneous polynomial `P` hyperbolic at `e`, the hyperbolicity cone is the path
component of `e` in the nonvanishing locus of `P`.  Gårding proved that this cone is convex.

The proof uses two facts already available here: `P` is hyperbolic at every point `y` of the
cone (`MvPolynomial.HyperbolicAt.of_joinedIn`), and for `x` in the cone the roots of
`t ↦ P(x + t y)` are negative (`affineLineRestriction_isRoot_neg_of_joinedIn`).  By
homogeneity `P((1 - s) x + s y) = (1 - s)^d P(x + s/(1 - s) y) ≠ 0` for `0 ≤ s < 1`, so the
segment from `x` to `y` stays in the nonvanishing locus.

## References

* L. Gårding, *An inequality for hyperbolic polynomials*, J. Math. Mech. 8 (1959), 957–965.
-/

open MvPolynomial

namespace RealRooted

/-- The hyperbolicity cone of `P` at `e`: the path component of `e` in the nonvanishing
locus of `P`. -/
def hyperbolicityCone {σ : Type*} (P : MvPolynomial σ ℝ) (e : σ → ℝ) : Set (σ → ℝ) :=
  pathComponentIn {x | eval x P ≠ 0} e

/-- **Gårding's theorem**: the hyperbolicity cone of a homogeneous polynomial is convex. -/
theorem convex_hyperbolicityCone {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ} {e : σ → ℝ}
    (he : P.HyperbolicAt e) (hhom : P.IsHomogeneous d) :
    Convex ℝ (hyperbolicityCone P e) := by
  intro x hx y hy a b ha hb hab
  set F := {x : σ → ℝ | eval x P ≠ 0}
  have hyx : JoinedIn F y x := hy.symm.trans hx
  have hseg : segment ℝ x y ⊆ F := by
    rintro z ⟨a', b', ha', hb', hab', rfl⟩
    by_cases hd : d = 0
    · subst hd
      have hconst : ∀ z, eval z P = eval (fun _ => (0 : ℝ)) P := fun z => by
        simpa using (hhom.eval_smul 0 z).symm
      change eval _ P ≠ 0
      rw [hconst, ← hconst e]
      exact he.1
    rcases ha'.eq_or_lt with ha0 | ha0
    · subst ha0
      rw [zero_add] at hab'
      subst hab'
      convert hy.target_mem using 1
      simp
    have hneg := MvPolynomial.HyperbolicAt.affineLineRestriction_isRoot_neg_of_joinedIn
      (MvPolynomial.HyperbolicAt.of_joinedIn he hhom hy) hhom hd hyx
    have hz : a' • x + b' • y = fun i => a' * (x i + y i * (b' / a')) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    change eval _ P ≠ 0
    rw [hz, hhom.eval_smul]
    refine mul_ne_zero (pow_ne_zero _ ha0.ne') fun h0 => ?_
    have := hneg (b' / a') (by
      rw [Polynomial.IsRoot, MvPolynomial.eval_affineLineRestriction]
      exact h0)
    linarith [div_nonneg hb' ha0.le]
  have hxz : JoinedIn F x (a • x + b • y) :=
    JoinedIn.of_segment_subset (((convex_segment x y).segment_subset (left_mem_segment ℝ x y)
      ⟨a, b, ha, hb, hab, rfl⟩).trans hseg)
  exact JoinedIn.trans hx hxz

end RealRooted
