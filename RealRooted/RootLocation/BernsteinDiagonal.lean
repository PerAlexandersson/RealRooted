module

public import RealRooted.MultiplierSequence
public import RealRooted.RootLocation.Mobius
import RealRooted.BernsteinCone
import RealRooted.Hadamard.Grace
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.MultiplierSequence.ProperPositionPF

/-!
# Bernstein-diagonal interval preservers

Fix `D` and the binomial-normalized Bernstein basis
`B_k = choose D k * X ^ k * (1 + X) ^ (D - k)` of the polynomials of degree at most `D`.  For a
sequence `γ`, the *Bernstein-diagonal map* `L = bernsteinDiagonal D γ` is the linear map with
`L B_k = γ_k B_k`.  We define it as the conjugate `K_D ∘ diag γ ∘ J_D` of the coefficientwise
multiplier `diag γ` by the Cayley change of variable `J_D f = (1 - X)^D f (X / (1 - X))` and its
inverse `K_D q = (1 + X)^D q (X / (1 + X))`, because `J_D B_k = choose D k * X ^ k`
(`Polynomial.cayleyTransform_binomialBasisRaw`).

Put `g = L ((1 + 2 X) ^ D) = ∑ γ_k B_k`, the `bernsteinDiagonalSymbol`.  Since
`J_D ((1 + 2 X) ^ D) = (1 + X) ^ D`, the Cayley transform of `g` is the Jensen polynomial
`∑ choose D k * γ_k X ^ k`, and `L f = K_D (J_D g ⋆_D J_D f)` where `⋆_D` is the finite
Schur--Szegő composition `schurSzegoComp D`.

## Main results

* `RealRooted.bernsteinDiagonal_basis`: `L B_k = γ_k B_k`.
* `RealRooted.bernsteinDiagonalSymbol_eq_sum`: `g = ∑ γ_k B_k`.
* `RealRooted.bernsteinDiagonal_maps_iff`: `L` sends every positive-leading polynomial of degree
  exactly `D` rooted in `[-1, 0]` to `0` or to another such polynomial iff `g` is `0` or such a
  polynomial (Kostov--Shapiro, *On the Schur--Szegő composition of polynomials*, Proposition 1.2
  and Theorem 1.3, transported to `[-1, 0]` by the Cayley change of variable).
* `RealRooted.bernsteinDiagonal_ne_zero_iff`: under these conditions, `L` is nonzero on every
  such polynomial iff all roots of `g` lie in `(-1, 0)`.

The inputs must have degree exactly `D`: a root at infinity of `f` (a degree drop) becomes the
root `1` of `J_D f`, which lies outside `(-∞, 0]`.  A root of `f` at `-1` is sent to infinity by
`J_D` (it lowers the degree of `J_D f`), and `K_D` turns such a degree deficit back into a root
at `-1`; this is why the closed interval `[-1, 0]` is the natural home of the inputs and
outputs, while the open interval `(-1, 0)` governs injectivity.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ### The map and its symbol -/

/-- The binomial-normalized Bernstein basis element `B_k = choose D k * X ^ k * (1 + X) ^ (D - k)`
of the polynomials of degree at most `D`. -/
def binomialBernsteinBasis (D k : ℕ) : ℝ[X] :=
  C (D.choose k : ℝ) * (X ^ k * (1 + X) ^ (D - k))

/-- The Bernstein-diagonal map `L` with `L B_k = γ_k B_k` (see `bernsteinDiagonal_basis`) on the
polynomials of degree at most `D`: the conjugate `K_D ∘ diag γ ∘ J_D` of the coefficientwise
multiplier by the Cayley change of variable. -/
def bernsteinDiagonal (D : ℕ) (γ : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  cayleyConj D (diagonalLinearMap γ)

/-- The symbol `g = L ((1 + 2 X) ^ D) = ∑ γ_k B_k` of the Bernstein-diagonal map. -/
def bernsteinDiagonalSymbol (D : ℕ) (γ : ℕ → ℝ) : ℝ[X] :=
  bernsteinDiagonal D γ ((1 + C 2 * X) ^ D)

/-- Unfolding `bernsteinDiagonal`: `L f = K_D (diag γ (J_D f))`. -/
theorem bernsteinDiagonal_apply (D : ℕ) (γ : ℕ → ℝ) (f : ℝ[X]) :
    bernsteinDiagonal D γ f =
      Polynomial.mobiusTransform D 1 0 1 1 (diagonalOperator γ (cayleyTransform D f)) :=
  cayleyConj_apply D (diagonalLinearMap γ) f

/-- The Cayley transform of a degree-`D` basis element is a monomial. -/
theorem cayleyTransform_binomialBernsteinBasis {D k : ℕ} (hk : k ≤ D) :
    cayleyTransform D (binomialBernsteinBasis D k) = C (D.choose k : ℝ) * X ^ k := by
  rw [binomialBernsteinBasis, cayleyTransform_C_mul, cayleyTransform_binomialBasisRaw hk]

@[simp] theorem binomialBernsteinBasis_zero (D : ℕ) :
    binomialBernsteinBasis D 0 = (1 + X) ^ D := by
  simp [binomialBernsteinBasis]

@[simp] theorem binomialBernsteinBasis_self (D : ℕ) :
    binomialBernsteinBasis D D = X ^ D := by
  simp [binomialBernsteinBasis]

/-- `L B_k = γ_k B_k`: the Bernstein-diagonal map is diagonal in the binomial Bernstein basis. -/
theorem bernsteinDiagonal_basis (D : ℕ) (γ : ℕ → ℝ) {k : ℕ} (hk : k ≤ D) :
    bernsteinDiagonal D γ (binomialBernsteinBasis D k) = C (γ k) * binomialBernsteinBasis D k := by
  have hdiag : diagonalOperator γ (C (D.choose k : ℝ) * X ^ k) =
      C (γ k * D.choose k) * X ^ k := by
    ext n
    simp only [coeff_diagonalOperator, coeff_C_mul, coeff_X_pow]
    split_ifs
    · subst_vars; ring
    · ring
  rw [bernsteinDiagonal_apply, cayleyTransform_binomialBernsteinBasis hk, hdiag,
    Polynomial.mobiusTransform_C_mul, Polynomial.mobiusTransform_X_pow D 1 0 1 1 hk,
    binomialBernsteinBasis]
  simp only [map_one, map_zero, one_mul, add_zero, map_mul]
  rw [add_comm X 1]
  ring

/-- The Jensen polynomial `∑ choose D k * γ_k X ^ k` is the Cayley transform of the symbol. -/
theorem bernsteinDiagonalSymbol_eq_mobiusTransform (D : ℕ) (γ : ℕ → ℝ) :
    bernsteinDiagonalSymbol D γ =
      Polynomial.mobiusTransform D 1 0 1 1 (jensenPolynomial D γ) := by
  rw [bernsteinDiagonalSymbol, bernsteinDiagonal_apply, cayleyTransform_twoPascal,
    jensenPolynomial_eq_diagonalOperator_X_add_one_pow, add_comm (1 : ℝ[X]) X]

/-- The Cayley transform of the symbol is the Jensen polynomial of `γ`. -/
theorem cayleyTransform_bernsteinDiagonalSymbol (D : ℕ) (γ : ℕ → ℝ) :
    cayleyTransform D (bernsteinDiagonalSymbol D γ) = jensenPolynomial D γ := by
  rw [bernsteinDiagonalSymbol_eq_mobiusTransform,
    cayleyTransform_mobiusTransform_one_zero_one_one D (natDegree_jensenPolynomial_le D γ)]

/-- The symbol is `g = ∑ γ_k B_k`. -/
theorem bernsteinDiagonalSymbol_eq_sum (D : ℕ) (γ : ℕ → ℝ) :
    bernsteinDiagonalSymbol D γ =
      ∑ k ∈ Finset.range (D + 1), C (γ k) * binomialBernsteinBasis D k := by
  rw [bernsteinDiagonalSymbol_eq_mobiusTransform,
    Polynomial.mobiusTransform_eq_sum D 1 0 1 1 (natDegree_jensenPolynomial_le D γ)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [coeff_jensenPolynomial, hk', ite_true, binomialBernsteinBasis, map_one, map_zero,
    one_mul, add_zero, map_mul]
  rw [add_comm X 1]
  ring

/-- The value at `0` of the symbol is `γ 0`. -/
theorem eval_zero_mobiusTransform_one_zero_one_one {D : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ D) :
    (Polynomial.mobiusTransform D 1 0 1 1 q).eval 0 = q.coeff 0 := by
  rw [Polynomial.mobiusTransform_eq_sum D 1 0 1 1 hq, eval_finsetSum,
    Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos D)) h

/-! ### The class of positive-leading degree-`D` polynomials rooted in `[-1, 0]` -/

/-- A positive-leading polynomial of degree exactly `D` rooted in `[-1, 0]`: the inputs and
outputs of the Bernstein-diagonal preservers. -/
def IsBernsteinRooted (D : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree = D ∧ 0 < p.leadingCoeff ∧ IsRealRootedIn (Icc (-1) 0) p

namespace IsBernsteinRooted

variable {D : ℕ} {p q : ℝ[X]}

/-- A member of the class is nonzero. -/
protected theorem ne_zero (h : IsBernsteinRooted D p) : p ≠ 0 := h.2.2.ne_zero

/-- The Cayley transform of a member of the class has degree at most `D`. -/
protected theorem natDegree_cayleyTransform_le (h : IsBernsteinRooted D p) :
    (cayleyTransform D p).natDegree ≤ D := by
  rw [cayleyTransform_eq_mobiusTransform]
  exact natDegree_mobiusTransform_le D 1 0 (-1) 1 h.1.le

/-- The Cayley transform of a member of the class is nonzero. -/
protected theorem cayleyTransform_ne_zero (h : IsBernsteinRooted D p) :
    cayleyTransform D p ≠ 0 := by
  rw [cayleyTransform_eq_mobiusTransform]
  exact mobiusTransform_ne_zero D 1 0 (-1) 1 h.ne_zero h.1.le (Ne.isUnit (by simp))

/-- The Cayley transform of a member of the class is a PF polynomial. -/
protected theorem isPFPolynomial_cayleyTransform (h : IsBernsteinRooted D p) :
    IsPFPolynomial (cayleyTransform D p) := by
  have hI := h.2.2.cayleyTransform_Iic h.1
  refine ⟨hasNonnegCoeffs_cayleyTransform_of_roots_mem_Icc h.2.2.splits h.1 h.2.1.le
    h.2.2.2.2, Or.inr hI.splits, fun r hr => hI.mem_of_mem_roots hr⟩

/-- `K_D` sends a nonzero PF polynomial of degree at most `D` to a member of the class. -/
protected theorem mobiusTransform_of_isPFPolynomial {q : ℝ[X]} (hq : IsPFPolynomial q)
    (hq0 : q ≠ 0) (hdeg : q.natDegree ≤ D) :
    IsBernsteinRooted D (Polynomial.mobiusTransform D 1 0 1 1 q) := by
  obtain ⟨hI, hD⟩ := IsRealRootedIn.mobiusTransform_one_zero_one_one hdeg
    ⟨hq0, hq.splits, fun r hr => hq.roots_nonpos r hr⟩
  refine ⟨hD, ?_, hI⟩
  rw [leadingCoeff, hD, coeff_mobiusTransform_one_zero_one_one D hdeg]
  exact eval_pos_of_hasNonnegCoeffs hq.hasNonnegCoeffs hq0 one_pos

end IsBernsteinRooted

/-- `K_D` sends a PF polynomial of degree at most `D` to `0` or to a member of the class. -/
theorem mobiusTransform_eq_zero_or_isBernsteinRooted {D : ℕ} {q : ℝ[X]} (hq : IsPFPolynomial q)
    (hdeg : q.natDegree ≤ D) :
    Polynomial.mobiusTransform D 1 0 1 1 q = 0 ∨
      IsBernsteinRooted D (Polynomial.mobiusTransform D 1 0 1 1 q) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · exact Or.inr (IsBernsteinRooted.mobiusTransform_of_isPFPolynomial hq hq0 hdeg)

/-- A polynomial which is `0` or in the class has a PF Cayley transform. -/
theorem isPFPolynomial_cayleyTransform_of_eq_zero_or {D : ℕ} {p : ℝ[X]}
    (h : p = 0 ∨ IsBernsteinRooted D p) : IsPFPolynomial (cayleyTransform D p) := by
  rcases h with rfl | h
  · rw [cayleyTransform_eq_mobiusTransform, mobiusTransform_zero]
    exact IsPFPolynomial.zero
  · exact h.isPFPolynomial_cayleyTransform

/-- The symbol is `0` or in the class iff the Jensen polynomial of `γ` is PF. -/
theorem bernsteinDiagonalSymbol_eq_zero_or_iff (D : ℕ) (γ : ℕ → ℝ) :
    (bernsteinDiagonalSymbol D γ = 0 ∨ IsBernsteinRooted D (bernsteinDiagonalSymbol D γ)) ↔
      IsPFPolynomial (jensenPolynomial D γ) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [cayleyTransform_bernsteinDiagonalSymbol] using
      isPFPolynomial_cayleyTransform_of_eq_zero_or h
  · rw [bernsteinDiagonalSymbol_eq_mobiusTransform]
    exact mobiusTransform_eq_zero_or_isBernsteinRooted h (natDegree_jensenPolynomial_le D γ)

/-- `(1 + 2 X) ^ D` is in the class (all roots equal `-1/2`). -/
theorem isBernsteinRooted_one_add_two_mul_X_pow (D : ℕ) :
    IsBernsteinRooted D ((1 + C 2 * X) ^ D) := by
  have hlin : (1 + C 2 * X : ℝ[X]) = C 2 * (X - C (-(1 / 2))) := by
    rw [mul_sub, ← C_mul]
    norm_num
    ring
  have hdeg : (1 + C 2 * X : ℝ[X]).natDegree = 1 := by
    rw [add_comm]; exact natDegree_linear (by norm_num)
  have hlead : (1 + C 2 * X : ℝ[X]).leadingCoeff = 2 := by
    rw [show (1 + C 2 * X : ℝ[X]) = C 2 * X + C 1 by simp [add_comm],
      leadingCoeff_linear (show (2 : ℝ) ≠ 0 by norm_num)]
  refine ⟨by rw [natDegree_pow, hdeg, mul_one], by rw [leadingCoeff_pow, hlead]; positivity, ?_⟩
  refine IsRealRootedIn.pow ?_ D
  rw [hlin]
  exact IsRealRootedIn.C_mul (by norm_num) (IsRealRootedIn.X_sub_C ⟨by norm_num, by norm_num⟩)

/-- `(1 + X) ^ D` is in the class. -/
theorem isBernsteinRooted_one_add_X_pow (D : ℕ) : IsBernsteinRooted D ((1 + X) ^ D) := by
  have h : IsRealRootedIn (Icc (-1) 0) (1 + X : ℝ[X]) := by
    simpa [sub_eq_add_neg, add_comm] using
      IsRealRootedIn.X_sub_C (S := Icc (-1 : ℝ) 0) (r := -1) ⟨le_rfl, by norm_num⟩
  have h1 : (1 + X : ℝ[X]) = X + C 1 := by simp [add_comm]
  refine ⟨?_, ?_, h.pow D⟩
  · rw [h1, natDegree_pow, natDegree_X_add_C, mul_one]
  · rw [h1, leadingCoeff_pow, leadingCoeff_X_add_C]; simp

/-- `X ^ D` is in the class. -/
theorem isBernsteinRooted_X_pow (D : ℕ) : IsBernsteinRooted D (X ^ D) := by
  refine ⟨by simp, by simp, ?_⟩
  exact (IsRealRootedIn.X (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 from ⟨by norm_num, le_rfl⟩)).pow D

/-! ### The exact diagonal characterization -/

/-- **Bernstein-diagonal characterization** (issue #2361).  The Bernstein-diagonal map `L` with
`L B_k = γ_k B_k` sends every positive-leading polynomial of degree exactly `D` rooted in
`[-1, 0]` to `0` or to another such polynomial iff its symbol `g = L ((1 + 2 X) ^ D)` is `0` or
such a polynomial.

Necessity tests the polynomial `(1 + 2 X) ^ D`.  For sufficiency, `J_D B_k = choose D k * X ^ k`
gives `L f = K_D (J_D g ⋆_D J_D f)` with `⋆_D = schurSzegoComp D`; both Cayley transforms are PF,
so is their composition by the finite Schur--Szegő theorem (Kostov--Shapiro, Proposition 1.2 and
Theorem 1.3), and `K_D` transports PF polynomials back to the class. -/
theorem bernsteinDiagonal_maps_iff (D : ℕ) (γ : ℕ → ℝ) :
    (∀ f : ℝ[X], IsBernsteinRooted D f →
        bernsteinDiagonal D γ f = 0 ∨ IsBernsteinRooted D (bernsteinDiagonal D γ f)) ↔
      (bernsteinDiagonalSymbol D γ = 0 ∨ IsBernsteinRooted D (bernsteinDiagonalSymbol D γ)) := by
  refine ⟨fun h => h _ (isBernsteinRooted_one_add_two_mul_X_pow D), fun h f hf => ?_⟩
  have hj := (bernsteinDiagonalSymbol_eq_zero_or_iff D γ).1 h
  have hF := hf.isPFPolynomial_cayleyTransform
  have hS := IsPFPolynomial.schurSzegoComp hj hF (natDegree_jensenPolynomial_le D γ)
    hf.natDegree_cayleyTransform_le
  rw [bernsteinDiagonal_apply, ← schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le
    hf.natDegree_cayleyTransform_le]
  exact mobiusTransform_eq_zero_or_isBernsteinRooted hS (natDegree_schurSzegoComp_le D _ _)

/-! #### Positive coefficients of PF polynomials -/

/-- A PF polynomial with nonzero constant coefficient has positive coefficients up to its
degree: it has no internal zero coefficients. -/
theorem IsPFPolynomial.coeff_pos {j : ℝ[X]} (hj : IsPFPolynomial j) (h0 : j.coeff 0 ≠ 0)
    {k : ℕ} (hk : k ≤ j.natDegree) : 0 < j.coeff k :=
  hj.coeff_pos_of_coeff_zero_pos (lt_of_le_of_ne (hj.hasNonnegCoeffs 0) (Ne.symm h0)) hk

/-- **Injectivity of the Bernstein-diagonal map.**  Assume the symbol `g` is `0` or a member of the
class (the condition of `bernsteinDiagonal_maps_iff`).  Then `L f ≠ 0` for every positive-leading
polynomial `f` of degree `D` rooted in `[-1, 0]` iff all roots of `g` lie in `(-1, 0)`.

The endpoint polynomials `(1 + X) ^ D` and `X ^ D` have `L ((1 + X) ^ D) = γ_0 (1 + X) ^ D` and
`L (X ^ D) = γ_D X ^ D`, which forces `γ_0 ≠ 0 ≠ γ_D`, that is, no root of `g` at `0` or `-1`.
Conversely, then the PF polynomial `J_D g` has all its coefficients positive, so `L f` has a
nonzero coefficient whenever `f ≠ 0`. -/
theorem bernsteinDiagonal_ne_zero_iff (D : ℕ) (γ : ℕ → ℝ)
    (hg : bernsteinDiagonalSymbol D γ = 0 ∨ IsBernsteinRooted D (bernsteinDiagonalSymbol D γ)) :
    (∀ f : ℝ[X], IsBernsteinRooted D f → bernsteinDiagonal D γ f ≠ 0) ↔
      IsRealRootedIn (Ioo (-1) 0) (bernsteinDiagonalSymbol D γ) := by
  set g := bernsteinDiagonalSymbol D γ with hgdef
  have hj : IsPFPolynomial (jensenPolynomial D γ) :=
    (bernsteinDiagonalSymbol_eq_zero_or_iff D γ).1 hg
  have hJg : cayleyTransform D g = jensenPolynomial D γ :=
    cayleyTransform_bernsteinDiagonalSymbol D γ
  have heval : g.eval 0 = (jensenPolynomial D γ).coeff 0 := by
    rw [hgdef, bernsteinDiagonalSymbol_eq_mobiusTransform,
      eval_zero_mobiusTransform_one_zero_one_one (natDegree_jensenPolynomial_le D γ)]
  have hc0 : (jensenPolynomial D γ).coeff 0 = γ 0 := by simp
  have hcD : (jensenPolynomial D γ).coeff D = γ D := by simp
  constructor
  · intro hall
    have hγ0 : γ 0 ≠ 0 := by
      intro h0
      refine hall _ (isBernsteinRooted_one_add_X_pow D) ?_
      have := bernsteinDiagonal_basis D γ (Nat.zero_le D)
      rwa [binomialBernsteinBasis_zero, h0, map_zero, zero_mul] at this
    have hγD : γ D ≠ 0 := by
      intro h0
      refine hall _ (isBernsteinRooted_X_pow D) ?_
      have := bernsteinDiagonal_basis D γ le_rfl
      rwa [binomialBernsteinBasis_self, h0, map_zero, zero_mul] at this
    have hjdeg : (jensenPolynomial D γ).natDegree = D :=
      le_antisymm (natDegree_jensenPolynomial_le D γ)
        (le_natDegree_of_ne_zero (by rw [hcD]; exact hγD))
    have hg0 : g ≠ 0 := by
      intro h0
      have : (jensenPolynomial D γ).coeff 0 = 0 := by rw [← heval, h0, eval_zero]
      exact hγ0 (by rwa [hc0] at this)
    have hgc : IsBernsteinRooted D g := hg.resolve_left hg0
    have hIoc : IsRealRootedIn (Ioc (-1) 0) g := by
      refine (isRealRootedIn_Ioc_iff_cayleyTransform hgc.1).2 ⟨?_, by rw [hJg, hjdeg]⟩
      rw [hJg]
      exact ⟨fun h => hγ0 (by simpa [hc0] using congrArg (fun q => q.coeff 0) h),
        hj.splits, fun r hr => hj.roots_nonpos r hr⟩
    refine ⟨hIoc.ne_zero, hIoc.splits, fun r hr => ?_⟩
    have hr' := hIoc.mem_of_mem_roots hr
    refine ⟨hr'.1, lt_of_le_of_ne hr'.2 ?_⟩
    rintro rfl
    have := (mem_roots hg0).1 hr
    rw [IsRoot.def, heval, hc0] at this
    exact hγ0 this
  · intro hI f hf
    have hg0 : g ≠ 0 := hI.ne_zero
    have hgc : IsBernsteinRooted D g := hg.resolve_left hg0
    have hIoc : IsRealRootedIn (Ioc (-1) 0) g := hI.mono Ioo_subset_Ioc_self
    have hjdeg : (jensenPolynomial D γ).natDegree = D := by
      rw [← hJg]; exact ((isRealRootedIn_Ioc_iff_cayleyTransform hgc.1).1 hIoc).2
    have hj0 : (jensenPolynomial D γ).coeff 0 ≠ 0 := by
      rw [← heval]
      intro h0
      have := hI.mem_of_isRoot (IsRoot.def.2 h0)
      exact absurd this.2 (lt_irrefl 0)
    have hF := hf.isPFPolynomial_cayleyTransform
    set F := cayleyTransform D f with hFdef
    have hk : 0 < F.coeff F.natDegree := by
      rw [← leadingCoeff]
      exact lt_of_le_of_ne (hF.hasNonnegCoeffs _)
        (Ne.symm (leadingCoeff_ne_zero.2 hf.cayleyTransform_ne_zero))
    have hkD : F.natDegree ≤ D := hf.natDegree_cayleyTransform_le
    have hjk := hj.coeff_pos hj0 (le_of_le_of_eq hkD hjdeg.symm)
    have hγk : 0 < γ F.natDegree := by
      simp only [coeff_jensenPolynomial, hkD] at hjk
      exact (mul_pos_iff_of_pos_left (Nat.cast_pos.2 (Nat.choose_pos hkD))).1 hjk
    have hne : diagonalOperator γ F ≠ 0 := by
      intro h0
      have := congrArg (fun q => q.coeff F.natDegree) h0
      simp only [coeff_diagonalOperator, coeff_zero] at this
      exact (mul_pos hγk hk).ne' this
    rw [bernsteinDiagonal_apply]
    exact mobiusTransform_ne_zero D 1 0 1 1 hne
      ((natDegree_diagonalOperator_le _ _).trans hkD) (Ne.isUnit (by simp))

end RealRooted
