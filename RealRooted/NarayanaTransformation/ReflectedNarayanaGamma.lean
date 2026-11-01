module

public import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator
public import RealRooted.DegreeDropReversal
public import RealRooted.NarayanaTransformation.ContinuousNarayanaGamma
import RealRooted.PFPolynomial
import RealRooted.MultiplierSequence.JensenHypergeometric
import RealRooted.PolarDerivative

/-!
# Reflected continuous Narayana gamma polynomials

This file identifies the coefficient-defined continuous Narayana gamma family
with its gamma-operator step and reflects its `n`-th member in degree `n`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The `n`-th continuous Narayana gamma polynomial reflected in degree `n`. -/
@[expose]
noncomputable def reflectedNarayanaGamma (theta : ℝ) (n : ℕ) : ℝ[X] :=
  (continuousNarayanaGamma theta n).reflect n

/-- The zeroth reflected continuous Narayana gamma polynomial is one. -/
@[simp]
theorem reflectedNarayanaGamma_zero (theta : ℝ) :
    reflectedNarayanaGamma theta 0 = 1 := by
  simp [reflectedNarayanaGamma]

/-- The first reflected continuous Narayana gamma polynomial is `X`. -/
@[simp]
theorem reflectedNarayanaGamma_one (theta : ℝ) :
    reflectedNarayanaGamma theta 1 = X := by
  simp [reflectedNarayanaGamma]

/-- The coefficient at `X ^ (n - k)` is the factorial--Pochhammer coefficient
from the continuous Narayana gamma polynomial. -/
theorem coeff_reflectedNarayanaGamma_sub (theta : ℝ) (n k : ℕ)
    (hk : k ≤ n / 2) :
    (reflectedNarayanaGamma theta n).coeff (n - k) =
      continuousNarayanaGammaCoeff theta n k := by
  rw [reflectedNarayanaGamma, Polynomial.coeff_reflect,
    Polynomial.revAt_le (Nat.sub_le n k),
    show n - (n - k) = k by lia,
    coeff_continuousNarayanaGamma, ite_eq_left hk]

/-- The coefficient-defined continuous Narayana gamma family satisfies the
gamma-operator recurrence. -/
theorem continuousNarayanaGamma_add_two_eq_gammaOperator
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    continuousNarayanaGamma theta (n + 2) =
      MultisetEulerianNarayana.gammaOperator (n + 1)
        (((n : ℝ) + 2 * theta + 2) / 2)
          (continuousNarayanaGamma theta (n + 1)) := by
  let a : ℝ := ((n : ℝ) + 2 * theta + 2) / 2
  have ha : a ≠ 0 := by
    dsimp [a]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrec := continuousNarayanaGamma_deriv_rec htheta (n + 1)
  norm_num only [Nat.cast_add, Nat.cast_one] at hrec
  have hscaled :
      C a * continuousNarayanaGamma theta (n + 2) =
        MultisetEulerianNarayana.gammaOperatorNumerator (n + 1) a
          (continuousNarayanaGamma theta (n + 1)) := by
    unfold MultisetEulerianNarayana.gammaOperatorNumerator
    apply Polynomial.funext
    intro x
    have heval := congrArg (eval x) hrec
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_one,
      Nat.cast_add, Nat.cast_one] at heval ⊢
    dsimp only [a]
    linear_combination (1 / 2 : ℝ) * heval
  unfold MultisetEulerianNarayana.gammaOperator
  calc
    continuousNarayanaGamma theta (n + 2) =
        C a⁻¹ * (C a * continuousNarayanaGamma theta (n + 2)) := by
          rw [← mul_assoc, ← C_mul]
          simp [ha]
    _ = _ := by rw [hscaled]

private theorem reflect_linear (a b : ℝ) :
    reflect 1 (C a + C b * X) = C b + C a * X := by
  rw [show (C a + C b * X : ℝ[X]) = C a * X ^ 0 + C b * X ^ 1 by simp,
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  rw [show revAt 1 0 = 1 by decide, show revAt 1 1 = 0 by decide]
  norm_num
  ring

private theorem reflect_gamma_derivative_multiplier :
    reflect 2 (C 2 * X * (1 - C 4 * X) : ℝ[X]) = C 2 * (X - C 4) := by
  rw [show (C 2 * X * (1 - C 4 * X) : ℝ[X]) =
      C 2 * X ^ 1 + C (-8) * X ^ 2 by
        apply Polynomial.funext
        intro x
        simp
        ring,
    reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow]
  apply Polynomial.funext
  intro x
  simp
  ring

private theorem reflect_derivative_eq
    {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    reflect (n - 1) p.derivative =
      C (n : ℝ) * reflect n p - X * (reflect n p).derivative := by
  have hreflect : (reflect n p).natDegree ≤ n := by
    exact natDegree_reflect_le.trans (max_le le_rfl hp)
  simpa using
    (C_mul_sub_X_mul_derivative_eq_reflect (g := reflect n p) hreflect).symm

/-- The reflected continuous Narayana gamma polynomials satisfy the derivative
recurrence with the growing zero root. -/
theorem reflectedNarayanaGamma_derivative_recurrence
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    C ((n : ℝ) + 2 * theta + 1) * reflectedNarayanaGamma theta (n + 1) =
      (C (-4 * (n : ℝ)) + C (3 * (n : ℝ) + 2 * theta + 1) * X) *
          reflectedNarayanaGamma theta n +
        C 2 * X * (C 4 - X) * (reflectedNarayanaGamma theta n).derivative := by
  rcases n with _ | n
  · simp [reflectedNarayanaGamma]
  let G := continuousNarayanaGamma theta (n + 1)
  have hG : G.natDegree ≤ n + 1 := by
    rw [natDegree_continuousNarayanaGamma htheta]
    exact Nat.div_le_self (n + 1) 2
  have hG' : G.derivative.natDegree ≤ n := by
    exact (natDegree_derivative_le G).trans (by lia)
  have hlin :
      (C ((n : ℝ) + 1 + 2 * theta + 1) + C (4 * ((n : ℝ) + 1)) * X).natDegree ≤ 1 := by
    compute_degree!
  have hquad : (C 2 * X * (1 - C 4 * X) : ℝ[X]).natDegree ≤ 2 := by
    compute_degree!
  have hrec := congrArg (reflect (n + 2))
    (continuousNarayanaGamma_deriv_rec htheta (n + 1))
  dsimp only [G] at hG hG'
  norm_num only [Nat.cast_add, Nat.cast_one] at hrec
  rw [reflect_C_mul, reflect_add] at hrec
  have hfirst : reflect (n + 2)
      ((C ((n : ℝ) + 1 + 2 * theta + 1) + C (4 * ((n : ℝ) + 1)) * X) *
        continuousNarayanaGamma theta (n + 1)) =
      reflect 1 (C ((n : ℝ) + 1 + 2 * theta + 1) +
          C (4 * ((n : ℝ) + 1)) * X) *
        reflect (n + 1) (continuousNarayanaGamma theta (n + 1)) := by
    simpa only [show 1 + (n + 1) = n + 2 by lia] using
      (reflect_mul _ _ hlin hG)
  have hsecond : reflect (n + 2)
      (C 2 * X * (1 - C 4 * X) *
        (continuousNarayanaGamma theta (n + 1)).derivative) =
      reflect 2 (C 2 * X * (1 - C 4 * X)) *
        reflect n (continuousNarayanaGamma theta (n + 1)).derivative := by
    simpa only [show 2 + n = n + 2 by lia] using
      (reflect_mul _ _ hquad hG')
  have hderivative :
      reflect n (continuousNarayanaGamma theta (n + 1)).derivative =
        C ((n + 1 : ℕ) : ℝ) *
            reflect (n + 1) (continuousNarayanaGamma theta (n + 1)) -
          X * (reflect (n + 1)
            (continuousNarayanaGamma theta (n + 1))).derivative := by
    simpa only [show n + 1 - 1 = n by lia] using reflect_derivative_eq hG
  rw [hfirst, hsecond, reflect_linear, reflect_gamma_derivative_multiplier,
    hderivative] at hrec
  change C ((n : ℝ) + 1 + 2 * theta + 1) *
      reflectedNarayanaGamma theta (n + 2) =
    (C (4 * ((n : ℝ) + 1)) + C ((n : ℝ) + 1 + 2 * theta + 1) * X) *
        reflectedNarayanaGamma theta (n + 1) +
      C 2 * (X - C 4) *
        (C ((n + 1 : ℕ) : ℝ) * reflectedNarayanaGamma theta (n + 1) -
          X * (reflectedNarayanaGamma theta (n + 1)).derivative) at hrec
  norm_num only [Nat.cast_add, Nat.cast_one]
  change C ((n : ℝ) + 1 + 2 * theta + 1) *
      reflectedNarayanaGamma theta (n + 2) = _
  rw [hrec]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X,
    Nat.cast_add, Nat.cast_one]
  ring

private theorem reflect_pure_recurrence_multiplier (a : ℝ) :
    reflect 2 (C a * (1 - C 4 * X) : ℝ[X]) =
      C a * X * (X - C 4) := by
  rw [reflect_C_mul]
  have hsucc : reflect 2 (1 - C 4 * X : ℝ[X]) =
      reflect 1 (1 - C 4 * X) * X := by
    exact Polynomial.reflect_succ (1 - C 4 * X : ℝ[X]) (D := 1)
      (by compute_degree!)
  have hpoly : (1 - C 4 * X : ℝ[X]) = C 1 + C (-4) * X := by
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_add]
    ring
  rw [hsucc, hpoly, reflect_linear]
  apply Polynomial.funext
  intro x
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X]
  ring

/-- The reflected continuous Narayana gamma polynomials satisfy the pure
three-term recurrence. -/
theorem reflectedNarayanaGamma_pure_recurrence
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    C ((n : ℝ) + 2 * theta + 2) * reflectedNarayanaGamma theta (n + 2) =
      C ((2 * n : ℝ) + 2 * theta + 3) * X *
          reflectedNarayanaGamma theta (n + 1) +
        C ((n : ℝ) + 1) * X * (C 4 - X) *
          reflectedNarayanaGamma theta n := by
  have hrec := congrArg (reflect (n + 2))
    (continuousNarayanaGamma_pure_rec htheta n)
  rw [reflect_C_mul, reflect_sub] at hrec
  have hfirst : reflect (n + 2)
      (C ((2 * n : ℝ) + 2 * theta + 3) *
        continuousNarayanaGamma theta (n + 1)) =
      C ((2 * n : ℝ) + 2 * theta + 3) *
        reflectedNarayanaGamma theta (n + 1) * X := by
    rw [reflect_C_mul, show n + 2 = (n + 1) + 1 by lia,
      Polynomial.reflect_succ _
        ((natDegree_continuousNarayanaGamma_le theta (n + 1)).trans
          (Nat.div_le_self (n + 1) 2))]
    simp only [reflectedNarayanaGamma]
    ring
  have hdegree :
      (C ((n : ℝ) + 1) * (1 - C 4 * X) : ℝ[X]).natDegree ≤ 2 := by
    compute_degree!
  have hsecond : reflect (n + 2)
      (C ((n : ℝ) + 1) * (1 - C 4 * X) *
        continuousNarayanaGamma theta n) =
      reflect 2 (C ((n : ℝ) + 1) * (1 - C 4 * X)) *
        reflectedNarayanaGamma theta n := by
    simpa only [show 2 + n = n + 2 by lia, reflectedNarayanaGamma] using
      (reflect_mul _ _ hdegree
        ((natDegree_continuousNarayanaGamma_le theta n).trans
          (Nat.div_le_self n 2)))
  rw [hfirst, hsecond, reflect_pure_recurrence_multiplier] at hrec
  change C ((n : ℝ) + 2 * theta + 2) *
      reflectedNarayanaGamma theta (n + 2) = _ at hrec
  change C ((n : ℝ) + 2 * theta + 2) * reflectedNarayanaGamma theta (n + 2) = _
  rw [hrec]
  ring

/-- After removing the forced zero power, the constant in the derivative
recurrence is zero at even indices and four at odd indices. -/
theorem reflectedNarayanaGamma_effectiveConstant (n : ℕ) :
    -4 * (n : ℝ) + 8 * (((n + 1) / 2 : ℕ) : ℝ) =
      if n % 2 = 0 then 0 else 4 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show (2 * k + 1) / 2 = k by lia]
    simp
    ring
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by lia]
    simp
    ring

/-- Reflection in the ambient degree gives a polynomial of degree exactly `n`. -/
theorem natDegree_reflectedNarayanaGamma
    {theta : ℝ} (_htheta : -1 < theta) (n : ℕ) :
    (reflectedNarayanaGamma theta n).natDegree = n := by
  apply DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne
  · exact (natDegree_continuousNarayanaGamma_le theta n).trans
      (Nat.div_le_self n 2)
  · rw [continuousNarayanaGamma_coeff_zero]
    norm_num

/-- Every reflected continuous Narayana gamma polynomial is monic. -/
theorem monic_reflectedNarayanaGamma
    {theta : ℝ} (_htheta : -1 < theta) (n : ℕ) :
    (reflectedNarayanaGamma theta n).Monic := by
  rw [Polynomial.Monic, reflectedNarayanaGamma,
    DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le]
  · exact continuousNarayanaGamma_coeff_zero theta n
  · exact (natDegree_continuousNarayanaGamma_le theta n).trans
      (Nat.div_le_self n 2)
  · rw [continuousNarayanaGamma_coeff_zero]
    norm_num

/-- Reflection preserves coefficient nonnegativity for the continuous
Narayana gamma family. -/
theorem reflectedNarayanaGamma_hasNonnegCoeffs
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    HasNonnegCoeffs (reflectedNarayanaGamma theta n) := by
  intro k
  rw [reflectedNarayanaGamma, Polynomial.coeff_reflect]
  exact continuousNarayanaGamma_hasNonnegCoeffs htheta n _

/-- Every reflected continuous Narayana gamma polynomial splits over `ℝ`. -/
theorem reflectedNarayanaGamma_splits
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    (reflectedNarayanaGamma theta n).Splits := by
  apply (continuousNarayanaGamma_splits htheta n).reflect
  exact (natDegree_continuousNarayanaGamma_le theta n).trans
    (Nat.div_le_self n 2)

/-- Reflection exhibits the growing power of `X` explicitly. -/
theorem reflectedNarayanaGamma_eq_X_pow_mul_reverse
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    reflectedNarayanaGamma theta n =
      X ^ (n - n / 2) * (continuousNarayanaGamma theta n).reverse := by
  have hdeg : (continuousNarayanaGamma theta n).natDegree ≤ n :=
    (natDegree_continuousNarayanaGamma_le theta n).trans (Nat.div_le_self n 2)
  rw [reflectedNarayanaGamma, Polynomial.reflect_eq_X_pow_mul_reverse _ hdeg,
    natDegree_continuousNarayanaGamma htheta]

/-- Zero has exact multiplicity `ceil (n / 2)` in the reflected family. -/
theorem rootMultiplicity_zero_reflectedNarayanaGamma
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    (reflectedNarayanaGamma theta n).rootMultiplicity 0 = (n + 1) / 2 := by
  let G := continuousNarayanaGamma theta n
  have hGpos := continuousNarayanaGamma_hasPosLeadingCoeff htheta n
  have hG0 : G.coeff 0 ≠ 0 := by
    rw [continuousNarayanaGamma_coeff_zero]
    norm_num
  have hrev : G.reverse ≠ 0 :=
    DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hG0
  have hprod : X ^ (n - n / 2) * G.reverse ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hrev
  rw [reflectedNarayanaGamma_eq_X_pow_mul_reverse htheta n,
    rootMultiplicity_mul hprod]
  have hpow : (X ^ (n - n / 2) : ℝ[X]).rootMultiplicity 0 = n - n / 2 := by
    simpa using rootMultiplicity_X_sub_C_pow (R := ℝ) 0 (n - n / 2)
  have hreverse : G.reverse.rootMultiplicity 0 = 0 := by
    apply rootMultiplicity_eq_zero
    intro hroot
    have hzero : G.leadingCoeff = 0 := by
      rw [← Polynomial.coeff_zero_reverse, coeff_zero_eq_eval_zero]
      exact hroot
    exact hGpos.ne' hzero
  rw [hpow, hreverse, add_zero]
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd <;> lia

/-- Every nonzero root of a reflected continuous Narayana gamma polynomial
is strictly negative. -/
theorem isRoot_reflectedNarayanaGamma_neg_of_ne_zero
    {theta r : ℝ} (htheta : -1 < theta) {n : ℕ}
    (hr : (reflectedNarayanaGamma theta n).IsRoot r) (hr0 : r ≠ 0) :
    r < 0 := by
  have hdeg : (continuousNarayanaGamma theta n).natDegree ≤ n :=
    (natDegree_continuousNarayanaGamma_le theta n).trans (Nat.div_le_self n 2)
  have hroot : (continuousNarayanaGamma theta n).IsRoot r⁻¹ := by
    apply (DegreeDropReversal.isRoot_reflect_inv_iff (inv_ne_zero hr0) hdeg).1
    simpa [reflectedNarayanaGamma] using hr
  have hGne : continuousNarayanaGamma theta n ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff 0) hzero
    rw [continuousNarayanaGamma_coeff_zero] at hcoeff
    norm_num at hcoeff
  have hmem : r⁻¹ ∈ (continuousNarayanaGamma theta n).roots :=
    (mem_roots hGne).2 hroot
  exact inv_lt_zero'.mp (continuousNarayanaGamma_roots_neg htheta n r⁻¹ hmem)

/-- Every nonzero root of a reflected continuous Narayana gamma polynomial
is simple. -/
theorem reflectedNarayanaGamma_hasSimpleRootsExcept_zero
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    HasSimpleRootsExcept (reflectedNarayanaGamma theta n) 0 := by
  let G := continuousNarayanaGamma theta n
  have hGsplits := continuousNarayanaGamma_splits htheta n
  have hGsimple := continuousNarayanaGamma_hasSimpleRoots htheta n
  have hG0 : G.coeff 0 ≠ 0 := by
    rw [continuousNarayanaGamma_coeff_zero]
    norm_num
  have hrev : G.reverse ≠ 0 :=
    DegreeDropReversal.reverse_ne_zero_of_coeff_zero_ne hG0
  have hrevSimple : HasSimpleRoots G.reverse := by
    apply HasSimpleRoots.of_roots_nodup hrev
    rw [Polynomial.roots_reverse_eq_map_inv hGsplits hG0]
    exact (Multiset.nodup_map_iff_of_injective inv_injective).mpr
      hGsimple.roots_nodup
  intro r hr0 hr
  have hfactor := reflectedNarayanaGamma_eq_X_pow_mul_reverse htheta n
  have hprod : X ^ (n - n / 2) * G.reverse ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hrev
  have hpow : ¬ (X ^ (n - n / 2) : ℝ[X]).IsRoot r := by
    simp [Polynomial.IsRoot.def, hr0]
  have hrevroot : G.reverse.IsRoot r := by
    rw [hfactor, Polynomial.IsRoot.def, eval_mul] at hr
    exact (mul_eq_zero.mp hr).resolve_left (by simpa [Polynomial.IsRoot.def] using hpow)
  rw [hfactor, rootMultiplicity_mul hprod, rootMultiplicity_eq_zero hpow, zero_add]
  exact hrevSimple r hrevroot

/-- Consecutive reflected continuous Narayana gamma polynomials weakly
interlace, with their ambient degrees giving the required one-degree gap. -/
theorem reflectedNarayanaGamma_interlaces
    {theta : ℝ} (htheta : -1 < theta) (n : ℕ) :
    Interlaces (reflectedNarayanaGamma theta n)
      (reflectedNarayanaGamma theta (n + 1)) := by
  have hPF : ∀ m, IsPFPolynomial (continuousNarayanaGamma theta m) := fun m ↦
    IsPFPolynomial.of_realRooted_nonneg
      (continuousNarayanaGamma_hasNonnegCoeffs htheta m)
      (continuousNarayanaGamma_splits htheta m)
  have hstrict := strictInterl_reciprocalShift_succ (n := n)
    (hPF n)
    (hPF (n + 1))
    ((natDegree_continuousNarayanaGamma_le theta n).trans (Nat.div_le_self n 2))
    ((natDegree_continuousNarayanaGamma_le theta (n + 1)).trans
      (Nat.div_le_self (n + 1) 2))
    (strictInterl_continuousNarayanaGamma_succ htheta n)
  change Interlaces
    (reciprocalShift n (continuousNarayanaGamma theta n))
    (reciprocalShift (n + 1) (continuousNarayanaGamma theta (n + 1)))
  apply hstrict.toInterlaces
  change (reflectedNarayanaGamma theta n).natDegree + 1 =
    (reflectedNarayanaGamma theta (n + 1)).natDegree
  rw [natDegree_reflectedNarayanaGamma htheta n,
    natDegree_reflectedNarayanaGamma htheta (n + 1)]

end RealRooted
