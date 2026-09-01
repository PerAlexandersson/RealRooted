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
