module

public import RealRooted.EulerOperator.ArithmeticSections
import RealRooted.Mathlib.Data.Nat.Factorial.ArithmeticProduct

/-!
# Arithmetic polar multipliers without Gamma functions

Finite products over integers not divisible by the stride describe the
arithmetic polar approximants. Reflection and translation evaluate these
products at multiples of the stride, without using Gamma functions at poles.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted

/-- The multiplier obtained from the arithmetic polar parameters. -/
noncomputable def arithmeticPolarMultiplier (r N k : ℕ) : ℝ :=
  ∏ a ∈ (Ioc 0 N).filter (fun a => ¬r ∣ a), ((a : ℝ) - k)

theorem coeff_arithmetic_polarThetaProduct (r N k : ℕ) (p : ℝ[X]) :
    (polarThetaProduct (arithmeticPolarParameters r N) p).coeff k =
      arithmeticPolarMultiplier r N k * p.coeff k := by
  rw [coeff_polarThetaProduct]
  rfl

/-- The constant multiplier is the factorial with the stride multiples removed. -/
theorem arithmeticPolarMultiplier_zero_mul (r N : ℕ) :
    arithmeticPolarMultiplier r N 0 * (r : ℝ) ^ (N / r) * (N / r).factorial =
      N.factorial := by
  simpa only [arithmeticPolarMultiplier, Nat.cast_zero, sub_zero, Nat.cast_mul,
    Nat.cast_prod, Nat.cast_pow] using
    congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_Ioc_not_dvd_mul_pow_mul_factorial r N)

/-- The constant multiplier is positive, including at zero stride or cutoff. -/
theorem arithmeticPolarMultiplier_zero_pos (r N : ℕ) :
    0 < arithmeticPolarMultiplier r N 0 := by
  simp only [arithmeticPolarMultiplier, Nat.cast_zero, sub_zero]
  exact prod_pos fun a ha => Nat.cast_pos.mpr (mem_Ioc.mp (mem_filter.mp ha).1).1

/-- Reflection in a multiple of the stride preserves its nonmultiple indices. -/
private theorem sub_mem_nonmultiples {r L a : ℕ} (hL : r ∣ L)
    (ha : a ∈ (Ioc 0 L).filter (fun a => ¬r ∣ a)) :
    L - a ∈ (Ioc 0 L).filter (fun a => ¬r ∣ a) := by
  obtain ⟨hai, had⟩ := mem_filter.mp ha
  obtain ⟨ha0, haL⟩ := mem_Ioc.mp hai
  have halt : a < L := lt_of_le_of_ne haL (fun h => had (h ▸ hL))
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.sub_pos_of_lt halt, Nat.sub_le _ _⟩,
    fun h => had ((Nat.dvd_sub_iff_right haL hL).mp h)⟩

/-- The multiplier at a multiple endpoint is its reflected constant value,
with one minus sign for each parameter. -/
theorem arithmeticPolarMultiplier_self {r L : ℕ} (hL : r ∣ L) :
    arithmeticPolarMultiplier r L L =
      (-1 : ℝ) ^ (L - L / r) * arithmeticPolarMultiplier r L 0 := by
  let s := (Ioc 0 L).filter (fun a => ¬r ∣ a)
  have hprod : (∏ a ∈ s, ((L - a : ℕ) : ℝ)) = ∏ a ∈ s, (a : ℝ) := by
    apply prod_bij (fun a _ => L - a) (fun _ ha => sub_mem_nonmultiples hL ha)
    · intro a ha b hb he
      have haL := (mem_Ioc.mp (mem_filter.mp ha).1).2
      have hbL := (mem_Ioc.mp (mem_filter.mp hb).1).2
      lia
    · intro b hb
      exact ⟨L - b, sub_mem_nonmultiples hL hb,
        Nat.sub_sub_self (mem_Ioc.mp (mem_filter.mp hb).1).2⟩
    · intro a _
      rfl
  have hcard : s.card = L - L / r := card_arithmeticPolarParameters r L
  change (∏ a ∈ s, ((a : ℝ) - L)) = _
  calc
    _ = ∏ a ∈ s, -((L - a : ℕ) : ℝ) := by
      apply prod_congr rfl
      intro a ha
      rw [Nat.cast_sub (mem_Ioc.mp (mem_filter.mp ha).1).2]
      ring
    _ = (-1 : ℝ) ^ s.card * ∏ a ∈ s, ((L - a : ℕ) : ℝ) := prod_neg _
    _ = _ := by rw [hcard, hprod]; simp [arithmeticPolarMultiplier, s]

/-- Translation by a multiple of the stride preserves the product on the
remaining interval. -/
private theorem prod_nonmultiples_sub {r L N : ℕ} (hL : r ∣ L) :
    (∏ a ∈ (Ioc L N).filter (fun a => ¬r ∣ a), ((a : ℝ) - L)) =
      arithmeticPolarMultiplier r (N - L) 0 := by
  simp only [arithmeticPolarMultiplier, Nat.cast_zero, sub_zero]
  apply prod_bij (fun a _ => a - L)
  · intro a ha
    obtain ⟨hai, had⟩ := mem_filter.mp ha
    obtain ⟨haL, haN⟩ := mem_Ioc.mp hai
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.sub_pos_of_lt haL, Nat.sub_le_sub_right haN L⟩,
      fun h => had ((Nat.dvd_sub_iff_left haL.le hL).mp h)⟩
  · intro a ha b hb he
    have haL := (mem_Ioc.mp (mem_filter.mp ha).1).1
    have hbL := (mem_Ioc.mp (mem_filter.mp hb).1).1
    lia
  · intro b hb
    obtain ⟨hbi, hbd⟩ := mem_filter.mp hb
    obtain ⟨hb0, hbN⟩ := mem_Ioc.mp hbi
    refine ⟨b + L, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by lia, by lia⟩, ?_⟩, by lia⟩
    exact fun h => hbd ((Nat.dvd_add_iff_left hL).mpr h)
  · intro a ha
    rw [Nat.cast_sub (mem_Ioc.mp (mem_filter.mp ha).1).1.le]

/-- Splitting a finite product at a multiple of the stride gives its exact
Gamma-free value there. -/
theorem arithmeticPolarMultiplier_of_dvd {r L N : ℕ} (hL : r ∣ L) (hLN : L ≤ N) :
    arithmeticPolarMultiplier r N L = (-1 : ℝ) ^ (L - L / r) *
      arithmeticPolarMultiplier r L 0 * arithmeticPolarMultiplier r (N - L) 0 := by
  unfold arithmeticPolarMultiplier
  rw [prod_filter, ← prod_Ioc_consecutive _ (Nat.zero_le L) hLN,
    ← prod_filter, ← prod_filter]
  change arithmeticPolarMultiplier r L L * _ = _
  rw [arithmeticPolarMultiplier_self hL, prod_nonmultiples_sub hL]
  rfl

/-- At a stride-multiple cutoff, the constant multiplier has a factorial ratio
with nonzero denominator. -/
theorem arithmeticPolarMultiplier_zero_mul_eq {r : ℕ} (hr : r ≠ 0) (M : ℕ) :
    arithmeticPolarMultiplier r (r * M) 0 =
      ((r * M).factorial : ℝ) / ((r : ℝ) ^ M * M.factorial) := by
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hrR) (by positivity))]
  simpa only [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr), mul_assoc] using
    arithmeticPolarMultiplier_zero_mul r (r * M)

/-- The exact finite arithmetic multiplier ratio. Every factorial and
descending factorial in the denominator is nonzero under the stated bounds. -/
theorem arithmeticPolarMultiplier_ratio {r M k : ℕ} (hr : r ≠ 0) (hk : k ≤ M) :
    arithmeticPolarMultiplier r (r * M) (r * k) / arithmeticPolarMultiplier r (r * M) 0 =
      (-1 : ℝ) ^ (r * k - k) * ((r * k).factorial : ℝ) / k.factorial *
        M.descFactorial k / (r * M).descFactorial (r * k) := by
  have hmul : r * k ≤ r * M := Nat.mul_le_mul_left r hk
  rw [arithmeticPolarMultiplier_of_dvd (dvd_mul_right r k) hmul,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr), ← Nat.mul_sub_left_distrib,
    arithmeticPolarMultiplier_zero_mul_eq hr, arithmeticPolarMultiplier_zero_mul_eq hr,
    arithmeticPolarMultiplier_zero_mul_eq hr]
  have hp : (r : ℝ) ^ M = (r : ℝ) ^ k * (r : ℝ) ^ (M - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hM : (M.factorial : ℝ) = ((M - k).factorial : ℝ) * M.descFactorial k := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk).symm
  have hRM : ((r * M).factorial : ℝ) =
      ((r * (M - k)).factorial : ℝ) * (r * M).descFactorial (r * k) := by
    rw [Nat.mul_sub_left_distrib]
    exact_mod_cast (Nat.factorial_mul_descFactorial hmul).symm
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hdR : ((r * M).descFactorial (r * k) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hmul).ne'
  have hkR : (k.factorial : ℝ) ≠ 0 := by positivity
  have hsubR : ((M - k).factorial : ℝ) ≠ 0 := by positivity
  have hrsubR : ((r * (M - k)).factorial : ℝ) ≠ 0 := by positivity
  rw [hp, hM, hRM]
  field_simp

end RealRooted
