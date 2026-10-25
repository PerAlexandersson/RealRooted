module

public import RealRooted.BorceaBranden.RealHKOConverse
public import RealRooted.BorceaBranden.RealFiniteClassification

@[expose] public section

noncomputable section

namespace RealRooted
namespace BorceaBranden

private theorem eq_zero_of_range_stableOrZero_of_eval_eq_zero
    {D σ : Type*} [AddCommMonoid D] [Module ℝ D]
    (T : D →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : ∀ f, MvRealStableOrZero (T f))
    (z : σ → ℂ) (hz : ∀ i, 0 < (z i).im)
    (f : D) (heval : MvPolynomial.eval z (complexifyMv (T f)) = 0) :
    T f = 0 := by
  rcases hT f with hzero | hstable
  · exact hzero
  · exact (hstable z hz heval).elim

private def evalComplexifyLinear
    {D σ : Type*} [AddCommMonoid D] [Module ℝ D]
    (T : D →ₗ[ℝ] MvPolynomial σ ℝ) (z : σ → ℂ) : D →ₗ[ℝ] ℂ where
  toFun f := MvPolynomial.eval z (complexifyMv (T f))
  map_add' f g := by simp [complexifyMv]
  map_smul' c f := by
    simp [complexifyMv, MvPolynomial.smul_eq_C_mul]

private def ratioReLinear
    {D : Type*} [AddCommMonoid D] [Module ℝ D]
    (e : D →ₗ[ℝ] ℂ) (a : ℂ) : D →ₗ[ℝ] ℝ where
  toFun f := ((e f) / a).re
  map_add' f g := by simp [add_div]
  map_smul' c f := by
    simp only [map_smul, Complex.real_smul]
    rw [mul_div_assoc]
    simp

private def ratioImLinear
    {D : Type*} [AddCommMonoid D] [Module ℝ D]
    (e : D →ₗ[ℝ] ℂ) (a : ℂ) : D →ₗ[ℝ] ℝ where
  toFun f := ((e f) / a).im
  map_add' f g := by simp [add_div]
  map_smul' c f := by
    simp only [map_smul, Complex.real_smul]
    rw [mul_div_assoc]
    simp

private theorem eq_of_div_re_im
    {x a : ℂ} (ha : a ≠ 0) {r s : ℝ}
    (hre : (x / a).re = r) (him : (x / a).im = s) :
    x = (r + s * Complex.I) * a := by
  have hratio : x / a = (r : ℂ) + (s : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using hre
    · simpa using him
  exact (div_eq_iff ha).mp hratio

/-- A real linear map has a rank-at-most-two representation whose entire
range pencil is real stable or zero. -/
def HasStableRankTwoRangeRepresentation
    {D σ : Type*} [AddCommMonoid D] [Module ℝ D]
    (T : D →ₗ[ℝ] MvPolynomial σ ℝ) : Prop :=
  ∃ (α β : D →ₗ[ℝ] ℝ) (P Q : MvPolynomial σ ℝ),
    AllComboMvRealStableOrZero P Q ∧
      ∀ f, T f = (α f) • P + (β f) • Q

/-- Borcea--Brändén, arXiv:0809.0401, Lemma 3.2(i), for an arbitrary real
module domain. -/
theorem hasStableRankTwoRangeRepresentation_of_forall_realStableOrZero
    {D σ : Type*} [AddCommGroup D] [Module ℝ D]
    (T : D →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : ∀ f, MvRealStableOrZero (T f)) :
    HasStableRankTwoRangeRepresentation T := by
  by_cases hzero : ∀ f, T f = 0
  · refine ⟨0, 0, 0, 0, ?_, ?_⟩
    · intro c d
      simpa using (MvRealStableOrZero.zero (sigma := σ))
    · intro f
      simp [hzero f]
  · obtain ⟨p, hp⟩ := not_forall.mp hzero
    let P := T p
    have hPstable : MvRealStable P := (hT p).resolve_left hp
    let z : σ → ℂ := fun _ => Complex.I
    have hz : ∀ i, 0 < (z i).im := by simp [z]
    let e := evalComplexifyLinear T z
    let a := e p
    have ha : a ≠ 0 := hPstable z hz
    by_cases hone : ∀ f, (e f / a).im = 0
    · let α := ratioReLinear e a
      refine ⟨α, 0, P, 0, ?_, ?_⟩
      · intro c d
        simp only [mul_zero, add_zero]
        simpa [MvPolynomial.smul_eq_C_mul] using hPstable.orZero.C_mul c
      · intro f
        have heq : e f = ((α f : ℝ) : ℂ) * a := by
          simpa [α, ratioReLinear] using
            (eq_of_div_re_im ha rfl (hone f))
        let q := f - (α f) • p
        have heval : MvPolynomial.eval z (complexifyMv (T q)) = 0 := by
          change e q = 0
          simp only [q, map_sub, map_smul, Complex.real_smul]
          change e f - ((α f : ℝ) : ℂ) * a = 0
          rw [heq]
          exact sub_self _
        have hq := eq_zero_of_range_stableOrZero_of_eval_eq_zero
          T hT z hz q heval
        have hTf : T f = (α f) • P := by
          have heq' := congrArg (fun R => R + (α f) • P) hq
          simpa [q, P] using heq'
        simpa using hTf
    · obtain ⟨q, hq⟩ := not_forall.mp hone
      let Q := T q
      let b := e q
      let d : ℝ := (b / a).im
      have hd : d ≠ 0 := hq
      let β₀ := ratioImLinear e a
      let β : D →ₗ[ℝ] ℝ := (d⁻¹) • β₀
      let α₀ := ratioReLinear e a
      let α : D →ₗ[ℝ] ℝ := α₀ - ((b / a).re) • β
      refine ⟨α, β, P, Q, ?_, ?_⟩
      · intro c d'
        have hvalue : MvPolynomial.C c * P + MvPolynomial.C d' * Q =
            T (c • p + d' • q) := by
          simp [P, Q, map_add, map_smul, MvPolynomial.smul_eq_C_mul]
        rw [hvalue]
        exact hT _
      · intro f
        have hβ : β f = (e f / a).im / d := by
          simp [β, β₀, ratioImLinear, div_eq_mul_inv, mul_comm]
        have hα : α f = (e f / a).re - β f * (b / a).re := by
          simp [α, α₀, ratioReLinear, mul_comm]
        have heq : e f = ((α f : ℝ) : ℂ) * a +
            ((β f : ℝ) : ℂ) * b := by
          have hratio : e f / a = (α f : ℂ) + (β f : ℂ) * (b / a) := by
            apply Complex.ext
            · simp [hα]
            · simp [hβ, d, hd]
          apply (div_eq_iff ha).mp at hratio
          rw [hratio]
          field_simp [ha]
        let r := f - (α f) • p - (β f) • q
        have heval : MvPolynomial.eval z (complexifyMv (T r)) = 0 := by
          change e r = 0
          simp only [r, map_sub, map_smul, Complex.real_smul]
          change e f - ((α f : ℝ) : ℂ) * a -
            ((β f : ℝ) : ℂ) * b = 0
          rw [heq]
          ring
        have hr := eq_zero_of_range_stableOrZero_of_eval_eq_zero
          T hT z hz r heval
        have hTf : T f = (α f) • P + (β f) • Q := by
          have heq' := congrArg
            (fun R => R + (α f) • P + (β f) • Q) hr
          simpa [r, P, Q, add_assoc] using heq'
        exact hTf

/-- The range-rigidity implication in Borcea--Branden, arXiv:0809.0401,
Lemma 3.2(i): if every value of a real linear operator is real stable or zero,
then its range has the stable rank-at-most-two representation. -/
theorem hasStableRankTwoRepresentation_of_forall_realStableOrZero
    {σ : Type*} {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : ∀ f, MvRealStableOrZero (T f)) :
    HasStableRankTwoRepresentation κ T := by
  by_cases hzero : ∀ f, T f = 0
  · refine ⟨0, 0, 0, 0, ?_, ?_⟩
    · intro c d
      simpa using (MvRealStableOrZero.zero (sigma := σ))
    · intro f
      simp [hzero f]
  · push Not at hzero
    obtain ⟨p, hp⟩ := hzero
    let P := T p
    have hPstable : MvRealStable P := (hT p).resolve_left hp
    let z : σ → ℂ := fun _ => Complex.I
    have hz : ∀ i, 0 < (z i).im := by simp [z]
    let e := evalComplexifyLinear T z
    let a := e p
    have ha : a ≠ 0 := hPstable z hz
    by_cases hone : ∀ f, (e f / a).im = 0
    · let α := ratioReLinear e a
      refine ⟨α, 0, P, 0, ?_, ?_⟩
      · intro c d
        simp only [mul_zero, add_zero]
        simpa [MvPolynomial.smul_eq_C_mul] using hPstable.orZero.C_mul c
      · intro f
        have heq : e f = ((α f : ℝ) : ℂ) * a := by
          simpa [α, ratioReLinear] using
            (eq_of_div_re_im ha rfl (hone f))
        let q := f - (α f) • p
        have heval : MvPolynomial.eval z (complexifyMv (T q)) = 0 := by
          change e q = 0
          simp only [q, map_sub, map_smul, Complex.real_smul]
          change e f - ((α f : ℝ) : ℂ) * a = 0
          rw [heq]
          exact sub_self _
        have hq := eq_zero_of_range_stableOrZero_of_eval_eq_zero T hT z hz q heval
        have hTf : T f = (α f) • P := by
          have := congrArg (fun R => R + (α f) • P) hq
          simpa [q, P] using this
        simpa using hTf
    · push Not at hone
      obtain ⟨q, hq⟩ := hone
      let Q := T q
      let b := e q
      let d : ℝ := (b / a).im
      have hd : d ≠ 0 := hq
      let β₀ := ratioImLinear e a
      let β : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] ℝ := (d⁻¹) • β₀
      let α₀ := ratioReLinear e a
      let α : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] ℝ :=
        α₀ - ((b / a).re) • β
      refine ⟨α, β, P, Q, ?_, ?_⟩
      · intro c d'
        have hvalue : MvPolynomial.C c * P + MvPolynomial.C d' * Q =
            T (c • p + d' • q) := by
          simp [P, Q, map_add, map_smul, MvPolynomial.smul_eq_C_mul]
        rw [hvalue]
        exact hT _
      · intro f
        have hβ : β f = (e f / a).im / d := by
          simp [β, β₀, ratioImLinear, div_eq_mul_inv, mul_comm]
        have hα : α f = (e f / a).re - β f * (b / a).re := by
          simp [α, α₀, ratioReLinear, mul_comm]
        have heq : e f = ((α f : ℝ) : ℂ) * a +
            ((β f : ℝ) : ℂ) * b := by
          have hratio : e f / a = (α f : ℂ) + (β f : ℂ) * (b / a) := by
            apply Complex.ext
            · simp [hα]
            · simp [hβ, d, hd]
          apply (div_eq_iff ha).mp at hratio
          rw [hratio]
          field_simp [ha]
        let r := f - (α f) • p - (β f) • q
        have heval : MvPolynomial.eval z (complexifyMv (T r)) = 0 := by
          change e r = 0
          simp only [r, map_sub, map_smul, Complex.real_smul]
          change e f - ((α f : ℝ) : ℂ) * a -
            ((β f : ℝ) : ℂ) * b = 0
          rw [heq]
          ring
        have hr := eq_zero_of_range_stableOrZero_of_eval_eq_zero T hT z hz r heval
        have hTf : T f = (α f) • P + (β f) • Q := by
          have := congrArg
            (fun R => R + (α f) • P + (β f) • Q) hr
          simpa [r, P, Q, add_assoc] using this
        exact hTf

end BorceaBranden
end RealRooted
