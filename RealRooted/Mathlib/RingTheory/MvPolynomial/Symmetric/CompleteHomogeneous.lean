import Mathlib.Data.Finset.Sym
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Complete homogeneous symmetric polynomial evaluations

This file adds evaluation and finite variable-adjunction lemmas for Mathlib's
`MvPolynomial.hsymm`.  The statements are shaped for eventual upstreaming and
do not introduce a second complete homogeneous polynomial definition.
-/

open scoped BigOperators

namespace MvPolynomial

noncomputable section

variable {σ R S : Type*} [Fintype σ] [DecidableEq σ]
  [CommSemiring R] [CommSemiring S]

/-- Evaluation of `hsymm` is the sum of the corresponding products over
unordered tuples. -/
theorem aeval_hsymm_eq_sum_sym [Algebra R S] (n : ℕ) (f : σ → S) :
    aeval f (hsymm σ R n) = ∑ s : Sym σ n, (s.1.map f).prod := by
  simp [hsymm, ← Multiset.prod_hom']

/-- Adjoining the last variable partitions positive-degree unordered tuples
according to whether they contain that variable. -/
private def finLastSymSuccEquiv (m r : ℕ) :
    Sym (Fin (m + 1)) (r + 1) ≃
      Sym (Fin (m + 1)) r ⊕ Sym (Fin m) (r + 1) :=
  (Sym.equivCongr finSuccEquivLast).trans <|
    symOptionSuccEquiv.trans <|
      Equiv.sumCongr (Sym.equivCongr finSuccEquivLast.symm) (Equiv.refl _)

private theorem finLastSymSuccEquiv_symm_inl (m r : ℕ)
    (s : Sym (Fin (m + 1)) r) :
    (finLastSymSuccEquiv m r).symm (Sum.inl s) = Fin.last m ::ₛ s := by
  change Sym.map finSuccEquivLast.symm
      (SymOptionSuccEquiv.decode
        (Sum.inl (Sym.map finSuccEquivLast s))) = Fin.last m ::ₛ s
  rw [SymOptionSuccEquiv.decode_inl, Sym.map_cons, Sym.map_map]
  simp

private theorem finLastSymSuccEquiv_symm_inr (m r : ℕ)
    (s : Sym (Fin m) (r + 1)) :
    (finLastSymSuccEquiv m r).symm (Sum.inr s) =
      s.map Fin.castSucc := by
  change Sym.map finSuccEquivLast.symm
      (SymOptionSuccEquiv.decode (Sum.inr s)) = s.map Fin.castSucc
  rw [SymOptionSuccEquiv.decode_inr, Sym.map_map]
  apply Sym.ext
  simp

/-- Evaluated variable adjunction for complete homogeneous symmetric
polynomials. -/
theorem aeval_hsymm_fin_succ [Algebra R S] (m r : ℕ)
    (f : Fin (m + 1) → S) :
    aeval f (hsymm (Fin (m + 1)) R (r + 1)) =
      aeval (fun i : Fin m => f i.castSucc) (hsymm (Fin m) R (r + 1)) +
        f (Fin.last m) * aeval f (hsymm (Fin (m + 1)) R r) := by
  rw [aeval_hsymm_eq_sum_sym, aeval_hsymm_eq_sum_sym,
    aeval_hsymm_eq_sum_sym]
  rw [Finset.mul_sum]
  calc
    (∑ s : Sym (Fin (m + 1)) (r + 1), (s.1.map f).prod) =
        ∑ s : Sym (Fin (m + 1)) r ⊕ Sym (Fin m) (r + 1),
          Sum.elim
            (fun t => f (Fin.last m) * (t.1.map f).prod)
            (fun t => (t.1.map (fun i => f i.castSucc)).prod) s := by
      symm
      apply Fintype.sum_equiv (finLastSymSuccEquiv m r).symm
      intro s
      rcases s with s | s
      · rw [finLastSymSuccEquiv_symm_inl]
        simp only [Sum.elim_inl]
        change f (Fin.last m) * (s.1.map f).prod =
          (Multiset.map f (Fin.last m ::ₘ s.1)).prod
        simp
      · rw [finLastSymSuccEquiv_symm_inr]
        simp [Multiset.map_map]
    _ = (∑ s : Sym (Fin (m + 1)) r,
          f (Fin.last m) * (s.1.map f).prod) +
        ∑ s : Sym (Fin m) (r + 1),
          (s.1.map (fun i => f i.castSucc)).prod :=
      Fintype.sum_sum_type _
    _ = (∑ s : Sym (Fin m) (r + 1),
          (s.1.map (fun i => f i.castSucc)).prod) +
        ∑ s : Sym (Fin (m + 1)) r,
          f (Fin.last m) * (s.1.map f).prod := add_comm _ _

/-- There are no positive-degree complete homogeneous monomials in zero
variables. -/
@[simp]
theorem hsymm_fin_zero_succ (n : ℕ) :
    hsymm (Fin 0) R (n + 1) = 0 := by
  simp [hsymm]

/-- Evaluation in zero variables vanishes in positive degree. -/
@[simp]
theorem aeval_hsymm_fin_zero_succ [Algebra R S] (n : ℕ)
    (f : Fin 0 → S) :
    aeval f (hsymm (Fin 0) R (n + 1)) = 0 := by
  rw [hsymm_fin_zero_succ]
  simp

/-- Degree-zero evaluation is one for every finite variable family. -/
@[simp]
theorem aeval_hsymm_zero [Algebra R S] (f : σ → S) :
    aeval f (hsymm σ R 0) = 1 := by
  simp

end

end MvPolynomial
