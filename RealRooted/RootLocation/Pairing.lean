module

public import RealRooted.RootLocation.Basic
public import RealRooted.RootPolynomial

/-!
# Pairing the linear factors of a polynomial

For a product-compatible class `K` of polynomials (for instance the polynomials whose image under
a transform lies in a fixed root region) and a set `S` of roots such that every product
`(X - r) (X - s)` with `r, s ∈ S` belongs to `K`, the monic polynomial with a multiset of roots in
`S` splits as `F * R` with `F ∈ K` and a remainder `R` which is either `1` or a single linear
factor `X - r` with `r` one of the given roots.  This is the combinatorial step ("pair the roots,
at most one remains") behind the sharp source domains of the Touchard and ordered Bell
transforms.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Adjoining a root multiplies `rootPolynomial` by the linear factor. -/
theorem rootPolynomial_cons (a : ℝ) (s : Multiset ℝ) :
    rootPolynomial (a ::ₘ s) = (X - C a) * rootPolynomial s := by
  simp [rootPolynomial]

/-- `rootPolynomial` turns a sum of multisets into a product. -/
theorem rootPolynomial_add (s t : Multiset ℝ) :
    rootPolynomial (s + t) = rootPolynomial s * rootPolynomial t := by
  simp [rootPolynomial]

/-- A polynomial rooted in `S` is a nonzero constant times the root polynomial of its roots. -/
theorem IsRealRootedIn.eq_C_mul_rootPolynomial {S : Set ℝ} {p : ℝ[X]} (hp : IsRealRootedIn S p) :
    p = C p.leadingCoeff * rootPolynomial p.roots :=
  hp.splits.eq_prod_roots

/-- If `K` contains `1`, is closed under multiplication and contains `X - r` for every `r ∈ s`,
then it contains the root polynomial of `s`. -/
theorem rootPolynomial_mem_of_forall_X_sub_C_mem {K : Set ℝ[X]} (h1 : (1 : ℝ[X]) ∈ K)
    (hmul : ∀ f ∈ K, ∀ g ∈ K, f * g ∈ K) {s : Multiset ℝ} (hs : ∀ r ∈ s, X - C r ∈ K) :
    rootPolynomial s ∈ K := by
  induction s using Multiset.induction_on with
  | empty => simpa [rootPolynomial] using h1
  | cons a s ih =>
    rw [rootPolynomial_cons]
    exact hmul _ (hs a (Multiset.mem_cons_self a s)) _
      (ih fun r hr ↦ hs r (Multiset.mem_cons_of_mem hr))

/-- **Pairing of roots.**  Let `K` be a set of polynomials containing `1` and closed under
multiplication, and `S` a set of reals such that `(X - r) (X - s) ∈ K` for all `r, s ∈ S`.  Then
the root polynomial of every multiset `m ⊆ S` is `F * R` with `F ∈ K` and `R` either `1` or a
single linear factor `X - r` with `r ∈ m`. -/
theorem exists_rootPolynomial_eq_mul_of_pairs {K : Set ℝ[X]} {S : Set ℝ}
    (h1 : (1 : ℝ[X]) ∈ K) (hmul : ∀ f ∈ K, ∀ g ∈ K, f * g ∈ K)
    (hpair : ∀ r ∈ S, ∀ s ∈ S, (X - C r) * (X - C s) ∈ K) (m : Multiset ℝ)
    (hm : ∀ r ∈ m, r ∈ S) :
    ∃ F R : ℝ[X], rootPolynomial m = F * R ∧ F ∈ K ∧ (R = 1 ∨ ∃ r ∈ m, R = X - C r) := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨1, 1, by simp [rootPolynomial], h1, Or.inl rfl⟩
  | cons a m ih =>
    obtain ⟨F, R, hFR, hF, hR⟩ := ih fun r hr ↦ hm r (Multiset.mem_cons_of_mem hr)
    have ha : a ∈ S := hm a (Multiset.mem_cons_self a m)
    rcases hR with rfl | ⟨r, hr, rfl⟩
    · exact ⟨F, X - C a, by rw [rootPolynomial_cons, hFR]; ring, hF,
        Or.inr ⟨a, Multiset.mem_cons_self a m, rfl⟩⟩
    · refine ⟨F * ((X - C a) * (X - C r)), 1, by rw [rootPolynomial_cons, hFR]; ring,
        hmul _ hF _ (hpair a ha r (hm r (Multiset.mem_cons_of_mem hr))), Or.inl rfl⟩

end RealRooted
