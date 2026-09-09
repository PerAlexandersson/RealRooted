import RealRooted.Basic

/-!
# Simple real roots

The elementary root-multiplicity interface for a real polynomial with no
repeated real roots.
-/

open Polynomial

noncomputable section

namespace RealRooted

variable {p : ℝ[X]}

/-- A polynomial has simple roots if every real root has multiplicity `1`. -/
def HasSimpleRoots (p : ℝ[X]) : Prop :=
  ∀ r : ℝ, p.IsRoot r → p.rootMultiplicity r = 1

/-- A polynomial has simple roots away from one exceptional point. -/
def HasSimpleRootsExcept (p : ℝ[X]) (a : ℝ) : Prop :=
  ∀ r : ℝ, r ≠ a → p.IsRoot r → p.rootMultiplicity r = 1

@[simp] lemma not_hasSimpleRoots_zero : ¬ HasSimpleRoots 0 := by
  simp [HasSimpleRoots]

@[grind <=]
lemma HasSimpleRoots.ne_zero (hp : HasSimpleRoots p) : p ≠ 0 := by
  rintro rfl
  simp at hp

/-- A proper-position pair with no common real root has simple real roots in
both entries. -/
theorem Prec.hasSimpleRoots_of_no_common_root {f g : ℝ[X]} (hprec : Prec f g)
    (hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ g.IsRoot r)) :
    HasSimpleRoots f ∧ HasSimpleRoots g := by
  constructor
  · intro r hroot
    have hother : ¬ g.IsRoot r := fun hr ↦ hno r ⟨hroot, hr⟩
    have hotherMult : g.rootMultiplicity r = 0 := by simp_all
    have hpos : 0 < f.rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hprec.1.1).mpr hroot
    have hbound := (rootMultiplicity_bounds_of_prec hprec r).1
    lia
  · intro r hroot
    have hother : ¬ f.IsRoot r := fun hr ↦ hno r ⟨hr, hroot⟩
    have hotherMult : f.rootMultiplicity r = 0 := by simp_all
    have hpos : 0 < g.rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hprec.2.1.1).mpr hroot
    have hbound := (rootMultiplicity_bounds_of_prec hprec r).2
    lia

lemma HasSimpleRoots.hasSimpleRootsExcept (hp : HasSimpleRoots p) (a : ℝ) :
    HasSimpleRootsExcept p a :=
  fun r _ hr => hp r hr

/-- A polynomial with simple roots away from one exceptional point is nonzero. -/
lemma HasSimpleRootsExcept.ne_zero {a : ℝ} {p : ℝ[X]}
    (hp : HasSimpleRootsExcept p a) :
    p ≠ 0 := by
  intro hp0
  have hmult := hp (a + 1) (by linarith)
    (by simp [hp0, Polynomial.IsRoot.def])
  simp [hp0] at hmult

/-- At a simple real root, the derivative does not vanish. -/
lemma HasSimpleRoots.eval_derivative_ne_zero
    (hsimple : HasSimpleRoots p) {r : ℝ} (hr : p.IsRoot r) :
    p.derivative.eval r ≠ 0 := by
  intro hder0
  have hder_root : p.derivative.IsRoot r := by simp_all
  have hmult : 1 < p.rootMultiplicity r :=
    (one_lt_rootMultiplicity_iff_isRoot hsimple.ne_zero).2 ⟨hr, hder_root⟩
  rw [hsimple r hr] at hmult
  lia

/-- A polynomial with simple real roots has no duplicate entries in its root
multiset. -/
lemma HasSimpleRoots.roots_nodup (hsimple : HasSimpleRoots p) :
    p.roots.Nodup := by
  refine Multiset.nodup_iff_count_le_one.mpr ?_
  intro r
  rw [count_roots (a := r) p]
  by_cases hr : p.IsRoot r
  · simp [hsimple r hr]
  · have hmult0 : p.rootMultiplicity r = 0 := by simp_all
    lia

/-- A nonzero polynomial with a duplicate-free root multiset has simple real
roots. -/
lemma HasSimpleRoots.of_roots_nodup {p : ℝ[X]}
    (hp : p ≠ 0) (hnd : p.roots.Nodup) :
    HasSimpleRoots p := by
  intro r hr
  have hpos : 0 < p.rootMultiplicity r := (rootMultiplicity_pos hp).2 hr
  have hle : p.rootMultiplicity r ≤ 1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp hnd r
  lia

/-- Multiplying by `X` preserves simple real roots when zero was not already a
root. -/
lemma HasSimpleRoots.X_mul (hsimple : HasSimpleRoots p)
    (hzero : ¬ p.IsRoot 0) :
    HasSimpleRoots (X * p) := by
  have hXp : X * p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hsimple.ne_zero
  apply HasSimpleRoots.of_roots_nodup hXp
  rw [Polynomial.roots_mul hXp, Polynomial.roots_X]
  refine Multiset.nodup_add.mpr ⟨by simp, hsimple.roots_nodup, ?_⟩
  rw [Multiset.singleton_disjoint]
  intro hzeroRoot
  exact hzero ((Polynomial.mem_roots hsimple.ne_zero).mp hzeroRoot)

/-- At a simple real root the root multiset carries exactly one copy. -/
lemma HasSimpleRoots.roots_count_eq_one (hsimple : HasSimpleRoots p)
    {c : ℝ} (hc : p.IsRoot c) :
    p.roots.count c = 1 := by
  rw [count_roots (a := c) p]
  exact hsimple c hc

/-- The sorted root list of a polynomial with simple real roots is strictly
sorted. -/
lemma HasSimpleRoots.roots_sort_sortedLT (hsimple : HasSimpleRoots p) :
    (p.roots.sort (· ≤ ·)).SortedLT := by
  have hsorted : (p.roots.sort (· ≤ ·)).SortedLE := by
    simpa using (Multiset.pairwise_sort (s := p.roots) (r := (· ≤ ·))).sortedLE
  have hnodup : (p.roots.sort (· ≤ ·)).Nodup := by
    apply Multiset.coe_nodup.mp
    simpa using hsimple.roots_nodup
  exact hsorted.sortedLT_of_nodup hnodup

end RealRooted
