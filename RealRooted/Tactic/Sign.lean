import RealRooted.Tactic.SideGoals

/-!
# Sign certificate tactic

The `rr_sign` tactic is a small arithmetic closer for coefficient-sign side
goals in Ma--Wang and Liu--Wang recurrence certificates.  It is intentionally
local: it does not apply an interlacing theorem, but it should close the
recurring polynomial-evaluation inequalities once the root interval and scalar
positivity hypotheses are in the context.
-/

open Polynomial

namespace RealRooted

namespace Tactic

syntax (name := rr_sign_side) "rr_sign_side" : tactic

syntax (name := rr_sign_side_term) "rr_sign_side_term" : term

macro_rules
  | `(tactic| rr_sign_side) =>
      `(tactic|
        first
          | rr_side_nonneg
          | rr_side)
  | `(rr_sign_side_term) =>
      `(by rr_sign_side)

end Tactic

lemma eval_X_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (X : ℝ[X]).eval r ≤ 0 := by
  simpa using hr

lemma eval_X_mul_nonpos_of_nonpos_of_nonneg {r : ℝ} {q : ℝ[X]}
    (hr : r ≤ 0) (hq : 0 ≤ q.eval r) :
    (X * q : ℝ[X]).eval r ≤ 0 := by
  simpa [Polynomial.eval_mul] using mul_nonpos_of_nonpos_of_nonneg hr hq

lemma eval_C_mul_X_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X : ℝ[X]).eval r ≤ 0 := by
  simpa using mul_nonpos_of_nonneg_of_nonpos hc hr

lemma eval_C_mul_X_sub_C_nonpos_of_nonneg_of_nonneg_of_nonpos {c a r : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hr : r ≤ 0) :
    (C c * X - C a : ℝ[X]).eval r ≤ 0 := by
  have hcx : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have htail : c * r - a ≤ 0 := by linarith
  simpa [Polynomial.eval_sub, Polynomial.eval_mul] using htail

lemma eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg {c r : ℝ} {q : ℝ[X]}
    (hc : 0 ≤ c) (hr : r ≤ 0) (hq : 0 ≤ q.eval r) :
    (C c * X * q : ℝ[X]).eval r ≤ 0 := by
  have hcx : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  simpa [Polynomial.eval_mul, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hcx hq

lemma eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have hone : 0 ≤ 1 - r := by linarith
  simpa [sub_eq_add_neg, mul_assoc] using mul_nonpos_of_nonpos_of_nonneg hcr hone

lemma eval_C_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg_of_nonneg_of_nonpos
    {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ≤ 0) :
    (C a * X + C (-b) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hleft : a * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hr
  have hright : -b * r ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg r)
  have hsum : a * r + -b * r ^ 2 ≤ 0 := by linarith
  simpa [
    Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_C,
    Polynomial.eval_X] using hsum

lemma eval_C_mul_two_X_sub_two_X_sq_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2) : ℝ[X]).eval r ≤ 0 := by
  have htail : 2 * r - 2 * r ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg r, hr]
  simpa [
    Polynomial.eval_mul,
    Polynomial.eval_sub,
    Polynomial.eval_pow,
    mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_X_mul_one_sub_X_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (X * (1 - X) : ℝ[X]).eval r ≤ 0 := by
  have hone : 0 ≤ 1 - r := by linarith
  simpa [Polynomial.eval_mul, sub_eq_add_neg] using
    mul_nonpos_of_nonpos_of_nonneg hr hone

lemma eval_X_mul_C_sub_X_nonpos_of_nonneg_of_nonpos {a r : ℝ}
    (ha : 0 ≤ a) (hr : r ≤ 0) :
    (X * (C a - X) : ℝ[X]).eval r ≤ 0 := by
  have htail : 0 ≤ a - r := by linarith
  simpa [Polynomial.eval_mul, Polynomial.eval_sub] using
    mul_nonpos_of_nonpos_of_nonneg hr htail

lemma eval_C_mul_X_mul_C_sub_X_nonpos_of_nonneg_of_nonneg_of_nonpos {c a r : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hr : r ≤ 0) :
    (C c * X * (C a - X) : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have htail : 0 ≤ a - r := by linarith
  simpa [Polynomial.eval_mul, Polynomial.eval_sub, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hcr htail

lemma eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ≤ 0) :
    (X * (C a - C b * X) : ℝ[X]).eval r ≤ 0 := by
  have hbr : b * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hr
  have htail : 0 ≤ a - b * r := by linarith
  simpa [Polynomial.eval_mul, Polynomial.eval_sub, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hr htail

lemma eval_C_mul_X_mul_C_sub_C_mul_X_nonpos
    {c a b r : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : r ≤ 0) :
    (C c * X * (C a - C b * X) : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have hbr : b * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hr
  have htail : 0 ≤ a - b * r := by linarith
  simpa [Polynomial.eval_mul, Polynomial.eval_sub, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hcr htail

lemma eval_one_add_X_nonpos_of_le_neg_one {r : ℝ} (hr : r ≤ -1) :
    (1 + X : ℝ[X]).eval r ≤ 0 := by
  have hone : 1 + r ≤ 0 := by linarith
  simpa [add_comm] using hone

lemma eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ -1) :
    (C c * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hone : 1 + r ≤ 0 := by linarith
  simpa [Polynomial.eval_mul, add_comm] using mul_nonpos_of_nonneg_of_nonpos hc hone

lemma eval_C_add_X_nonpos_of_le_neg {a r : ℝ} (hr : r ≤ -a) :
    (C a + X : ℝ[X]).eval r ≤ 0 := by
  have htail : a + r ≤ 0 := by linarith
  simpa [add_comm] using htail

lemma eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg {c a r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ -a) :
    (C c * (C a + X) : ℝ[X]).eval r ≤ 0 := by
  have htail : (C a + X : ℝ[X]).eval r ≤ 0 :=
    eval_C_add_X_nonpos_of_le_neg hr
  simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_neg_C_mul_C_add_C_mul_X_nonpos_of_nonneg_of_nonneg_of_le_of_ge_neg_one
    {c a b r : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (hba : b ≤ a) (hlo : -1 ≤ r) :
    (-(C c) * (C a + C b * X) : ℝ[X]).eval r ≤ 0 := by
  have hbr : -b ≤ b * r := by
    have hmul := mul_le_mul_of_nonneg_left hlo hb
    simpa using hmul
  have hfactor : 0 ≤ a + b * r := by
    linarith
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  simpa [Polynomial.eval_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hneg hfactor

lemma eval_neg_C_mul_one_add_X_nonpos_of_nonneg_of_ge_neg_one {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) :
    (-(C c) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  simpa using
    eval_neg_C_mul_C_add_C_mul_X_nonpos_of_nonneg_of_nonneg_of_le_of_ge_neg_one
      (c := c) (a := 1) (b := 1) hc rr_sign_side_term rr_sign_side_term hlo

lemma eval_neg_C_mul_one_add_two_mul_X_nonpos_of_nonneg_of_ge_neg_half {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -(1 / 2 : ℝ) ≤ r) :
    (-(C c) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  have hfactor : 0 ≤ 1 + 2 * r := by linarith
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  simpa [Polynomial.eval_mul, add_comm, add_left_comm, add_assoc, mul_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hneg hfactor

lemma eval_X_sub_one_nonpos_of_le_one {r : ℝ} (hr : r ≤ 1) :
    (X - 1 : ℝ[X]).eval r ≤ 0 := by
  simpa [sub_eq_add_neg] using sub_nonpos.mpr hr

lemma eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 1) :
    (C c * (X - 1) : ℝ[X]).eval r ≤ 0 := by
  have htail : r - 1 ≤ 0 := sub_nonpos.mpr hr
  simpa [Polynomial.eval_mul, sub_eq_add_neg] using
    mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_X_mul_one_add_X_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hone : 0 ≤ 1 + r := by linarith
  simpa [Polynomial.eval_mul, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hhi hone

lemma eval_X_add_X_sq_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C (1 : ℝ) * X + C (1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hone : 0 ≤ 1 + r := by linarith
  have hprod : r * (1 + r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hhi hone
  have heval :
      (C (1 : ℝ) * X + C (1 : ℝ) * X ^ 2 : ℝ[X]).eval r =
        r * (1 + r) := by
    simp [
      Polynomial.eval_add,
      Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  rw [heval]
  exact hprod

lemma eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hhi
  have hone : 0 ≤ 1 + r := by linarith
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hcr hone

lemma eval_C_mul_X_add_C_mul_X_sq_nonpos_of_nonneg_of_mem_Icc {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * X + C c * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hhi
  have hone : 0 ≤ 1 + r := by linarith
  have hprod : c * r * (1 + r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcr hone
  have heval :
      (C c * X + C c * X ^ 2 : ℝ[X]).eval r =
        c * r * (1 + r) := by
    simp [
      Polynomial.eval_add,
      Polynomial.eval_mul,
      Polynomial.eval_pow,
      Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [heval]
  exact hprod

lemma eval_X_mul_one_add_C_mul_X_nonpos_of_nonpos_of_linear_nonneg
    {c r : ℝ} (hhi : r ≤ 0) (hlin : 0 ≤ 1 + c * r) :
    (X * (1 + C c * X) : ℝ[X]).eval r ≤ 0 := by
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hhi hlin

lemma eval_C_mul_X_mul_one_add_C_mul_X_nonpos
    {a c r : ℝ} (ha : 0 ≤ a) (hhi : r ≤ 0) (hlin : 0 ≤ 1 + c * r) :
    (C a * X * (1 + C c * X) : ℝ[X]).eval r ≤ 0 := by
  have hleft : a * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hhi
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hleft hlin

lemma eval_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -(1 / 4 : ℝ) ≤ r) (hhi : r ≤ 0) :
    (X * (1 + C (4 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  have hlin : 0 ≤ 1 + 4 * r := by
    linarith
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hhi hlin

lemma eval_C_mul_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -(1 / 4 : ℝ) ≤ r) (hhi : r ≤ 0) :
    (C c * X * (1 + C (4 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  have hlin : 0 ≤ 1 + 4 * r := by
    linarith
  have hleft : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hhi
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hleft hlin

lemma eval_X_sq_sub_one_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X ^ 2 - 1 : ℝ[X]).eval r ≤ 0 := by
  have hnonneg : 0 ≤ r + 1 := by linarith
  have hprod : r * (r + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hhi hnonneg
  have hsq : r ^ 2 ≤ 1 := by nlinarith
  simpa [Polynomial.eval_sub, Polynomial.eval_pow] using sub_nonpos.mpr hsq

lemma eval_C_mul_X_sq_sub_one_nonpos_of_nonneg_of_mem_Icc {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * (X ^ 2 - 1) : ℝ[X]).eval r ≤ 0 := by
  have htail := eval_X_sq_sub_one_nonpos_of_mem_Icc hlo hhi
  simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ -1) :
    (-(C c) * X * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hx : r ≤ 0 := by linarith
  have hone : 1 + r ≤ 0 := by linarith
  have hprod : 0 ≤ r * (1 + r) :=
    mul_nonneg_of_nonpos_of_nonpos hx hone
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hneg hprod

lemma eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ -(1 / 2 : ℝ)) :
    ((1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  have hone : 0 ≤ 1 + r := by linarith
  have htwo : 1 + 2 * r ≤ 0 := by linarith
  simpa [Polynomial.eval_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonneg_of_nonpos hone htwo

lemma eval_C_mul_one_add_X_mul_one_add_two_mul_X_nonpos_of_nonneg_of_mem_interval
    {c r : ℝ} (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ -(1 / 2 : ℝ)) :
    (C c * (1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r ≤ 0 := by
  have hone : 0 ≤ 1 + r := by linarith
  have htwo : 1 + 2 * r ≤ 0 := by linarith
  have htail : (1 + r) * (1 + 2 * r) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hone htwo
  exact
    calc
      (C c * (1 + X) * (1 + C (2 : ℝ) * X) : ℝ[X]).eval r =
          c * ((1 + r) * (1 + 2 * r)) := by
            simp [Polynomial.eval_mul, mul_assoc, add_comm]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_X_mul_one_sub_X_sq_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (X * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hsq : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
  simpa [Polynomial.eval_mul, Polynomial.eval_pow, sub_eq_add_neg] using
    mul_nonpos_of_nonpos_of_nonneg hr hsq

lemma eval_C_mul_X_mul_one_sub_X_sq_nonpos_of_nonneg_of_nonpos {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    (C c * X * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hr
  have hsq : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
  simpa [Polynomial.eval_mul, Polynomial.eval_pow, mul_assoc, sub_eq_add_neg] using
    mul_nonpos_of_nonpos_of_nonneg hcr hsq

lemma eval_X_mul_one_sub_X_mul_one_add_X_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X * (1 - X) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hleft : r * (1 - r) ≤ 0 := by
    have hone_sub : 0 ≤ 1 - r := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hhi hone_sub
  have hone_add : 0 ≤ 1 + r := by linarith
  simpa [Polynomial.eval_mul, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using mul_nonpos_of_nonpos_of_nonneg hleft hone_add

lemma eval_C_mul_X_mul_one_sub_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
    {c r : ℝ} (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * X * (1 - X) * (1 + X) : ℝ[X]).eval r ≤ 0 := by
  have hleft : c * r * (1 - r) ≤ 0 := by
    have hcr : c * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hhi
    have hone_sub : 0 ≤ 1 - r := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hcr hone_sub
  have hone_add : 0 ≤ 1 + r := by linarith
  simpa [Polynomial.eval_mul, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using mul_nonpos_of_nonpos_of_nonneg hleft hone_add

lemma eval_X_sub_X_pow_three_nonpos_of_mem_Icc {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (X - X ^ 3 : ℝ[X]).eval r ≤ 0 := by
  have hleft : r * (1 - r) ≤ 0 := by
    have hone_sub : 0 ≤ 1 - r := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hhi hone_sub
  have hone_add : 0 ≤ 1 + r := by linarith
  have hprod : r * (1 - r) * (1 + r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hleft hone_add
  have heq : (X - X ^ 3 : ℝ[X]).eval r = r * (1 - r) * (1 + r) := by
    simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  simpa [heq] using hprod

lemma eval_C_mul_X_sub_X_pow_three_nonpos_of_nonneg_of_mem_Icc {c r : ℝ}
    (hc : 0 ≤ c) (hlo : -1 ≤ r) (hhi : r ≤ 0) :
    (C c * (X - X ^ 3) : ℝ[X]).eval r ≤ 0 := by
  have htail := eval_X_sub_X_pow_three_nonpos_of_mem_Icc hlo hhi
  simpa [Polynomial.eval_mul] using mul_nonpos_of_nonneg_of_nonpos hc htail

lemma eval_neg_C_mul_one_sub_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
  simpa [sub_eq_add_neg] using mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_neg_one_add_two_X_sub_X_sq_nonpos {r : ℝ} :
    (C (-1 : ℝ) + C (2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hsq : 0 ≤ (1 - r) ^ 2 := sq_nonneg (1 - r)
  have heval :
      (C (-1 : ℝ) + C (2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r =
        -((1 - r) ^ 2) := by
    simp [
      Polynomial.eval_add,
      Polynomial.eval_mul,
      Polynomial.eval_pow,
      Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [heval]
  exact neg_nonpos.mpr hsq

lemma eval_neg_C_mul_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ r ^ 2 := sq_nonneg r
  simpa using mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_neg_C_mul_one_add_X_sq_nonpos_of_nonneg {c r : ℝ}
    (hc : 0 ≤ c) :
    (-(C c) * (1 + X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  simpa [add_comm, add_left_comm, add_assoc] using
    mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_C_neg_add_C_neg_two_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg
    {c r : ℝ} (hc : 0 ≤ c) :
    (C (-c) + C (-(2 * c)) * X + C (-c) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  have hprod : -c * (1 + r) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg hsq
  have heval :
      (C (-c) + C (-(2 * c)) * X + C (-c) * X ^ 2 : ℝ[X]).eval r =
        -c * (1 + r) ^ 2 := by
    simp [
      Polynomial.eval_add,
      Polynomial.eval_mul,
      Polynomial.eval_pow,
      Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [heval]
  exact hprod

lemma eval_neg_one_sub_two_X_sub_X_sq_nonpos {r : ℝ} :
    (C (-1 : ℝ) + C (-2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hsq : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  have heval :
      (C (-1 : ℝ) + C (-2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r =
        -((1 + r) ^ 2) := by
    simp [
      Polynomial.eval_add,
      Polynomial.eval_mul,
      Polynomial.eval_pow,
      Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [heval]
  exact neg_nonpos.mpr hsq

lemma eval_C_neg_nonpos_of_nonneg {c r : ℝ} (hc : 0 ≤ c) :
    (C (-c) : ℝ[X]).eval r ≤ 0 := by
  simpa using neg_nonpos.mpr hc

lemma eval_neg_C_nonpos_of_nonneg {c r : ℝ} (hc : 0 ≤ c) :
    (-(C c) : ℝ[X]).eval r ≤ 0 := by
  simpa using neg_nonpos.mpr hc

lemma eval_neg_C_mul_sq_nonpos_of_nonneg {c r : ℝ} {q : ℝ[X]}
    (hc : 0 ≤ c) :
    (-(C c) * q ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hneg : -c ≤ 0 := neg_nonpos.mpr hc
  have hsq : 0 ≤ (q.eval r) ^ 2 := sq_nonneg (q.eval r)
  simpa [Polynomial.eval_pow] using mul_nonpos_of_nonpos_of_nonneg hneg hsq

lemma eval_neg_monic_quadratic_nonpos_of_discrim_nonpos {b c r : ℝ}
    (hdisc : b ^ 2 ≤ 4 * c) :
    (-(X ^ 2 + C b * X + C c) : ℝ[X]).eval r ≤ 0 := by
  have hdisc_nonneg : 0 ≤ 4 * c - b ^ 2 := by nlinarith
  have hsq : 0 ≤ (2 * r + b) ^ 2 := sq_nonneg (2 * r + b)
  have hsum : 0 ≤ (2 * r + b) ^ 2 + (4 * c - b ^ 2) :=
    add_nonneg hsq hdisc_nonneg
  have hsum_eq : (2 * r + b) ^ 2 + (4 * c - b ^ 2) =
      4 * (r ^ 2 + b * r + c) := by
    ring
  have hpoly : 0 ≤ r ^ 2 + b * r + c := by
    nlinarith
  simpa [
    Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_neg,
    Polynomial.eval_C,
    Polynomial.eval_X] using neg_nonpos.mpr hpoly

lemma eval_neg_C_mul_monic_quadratic_nonpos_of_nonneg_of_discrim_nonpos
    {a b c r : ℝ} (ha : 0 ≤ a) (hdisc : b ^ 2 ≤ 4 * c) :
    (-(C a) * (X ^ 2 + C b * X + C c) : ℝ[X]).eval r ≤ 0 := by
  have hdisc_nonneg : 0 ≤ 4 * c - b ^ 2 := by nlinarith
  have hsq : 0 ≤ (2 * r + b) ^ 2 := sq_nonneg (2 * r + b)
  have hsum : 0 ≤ (2 * r + b) ^ 2 + (4 * c - b ^ 2) :=
    add_nonneg hsq hdisc_nonneg
  have hsum_eq : (2 * r + b) ^ 2 + (4 * c - b ^ 2) =
      4 * (r ^ 2 + b * r + c) := by
    ring
  have hpoly : 0 ≤ r ^ 2 + b * r + c := by
    nlinarith
  have hneg : -a ≤ 0 := neg_nonpos.mpr ha
  simpa [
    Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_neg,
    Polynomial.eval_C,
    Polynomial.eval_X] using mul_nonpos_of_nonpos_of_nonneg hneg hpoly

lemma eval_neg_quadratic_nonpos_of_discrim_nonpos
    {a b c r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hdisc : b ^ 2 ≤ 4 * a * c) :
    (-(C a * X ^ 2 + C b * X + C c) : ℝ[X]).eval r ≤ 0 := by
  have hpoly : 0 ≤ a * r ^ 2 + b * r + c := by
    by_cases ha0 : a = 0
    · subst a
      have hb0 : b = 0 := by nlinarith [sq_nonneg b]
      subst b
      simpa using hc
    · have hapos : 0 < a := lt_of_le_of_ne' ha ha0
      have hdisc_nonneg : 0 ≤ 4 * a * c - b ^ 2 := by nlinarith
      have hsq : 0 ≤ (2 * a * r + b) ^ 2 := sq_nonneg (2 * a * r + b)
      have hsum : 0 ≤ (2 * a * r + b) ^ 2 + (4 * a * c - b ^ 2) :=
        add_nonneg hsq hdisc_nonneg
      have hsum_eq : (2 * a * r + b) ^ 2 + (4 * a * c - b ^ 2) =
          4 * a * (a * r ^ 2 + b * r + c) := by
        ring
      nlinarith
  simpa [
    Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_neg,
    Polynomial.eval_C,
    Polynomial.eval_X] using neg_nonpos.mpr hpoly

lemma eval_neg_expanded_quadratic_nonpos_of_discrim_nonpos
    {a b c r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hdisc : b ^ 2 ≤ 4 * c * a) :
    (C (-a) + C b * X + C (-c) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hdisc' : (-b) ^ 2 ≤ 4 * c * a := by
    nlinarith
  have htail : (-(C c * X ^ 2 + C (-b) * X + C a) : ℝ[X]).eval r ≤ 0 :=
    eval_neg_quadratic_nonpos_of_discrim_nonpos hc ha hdisc'
  simpa [
    Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_neg,
    Polynomial.eval_C,
    Polynomial.eval_X] using htail

lemma eval_quadratic_nonpos_of_nonpos_of_nonpos_of_discrim_nonpos
    {a b c r : ℝ} (ha : a ≤ 0) (hc : c ≤ 0) (hdisc : b ^ 2 ≤ 4 * a * c) :
    (C a + C b * X + C c * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  have hdisc' : b ^ 2 ≤ 4 * (-c) * (-a) := by
    nlinarith
  have htail :
      (C (-(-a)) + C b * X + C (-(-c)) * X ^ 2 : ℝ[X]).eval r ≤ 0 :=
    eval_neg_expanded_quadratic_nonpos_of_discrim_nonpos
      (a := -a) (b := b) (c := -c) (r := r) (by linarith) (by linarith) hdisc'
  simpa using htail

lemma eval_neg_two_fifths_add_four_fifths_X_sub_two_fifths_X_sq_nonpos {r : ℝ} :
    (C (-2 / 5 : ℝ) + C (4 / 5 : ℝ) * X + C (-2 / 5 : ℝ) * X ^ 2 :
      ℝ[X]).eval r ≤ 0 :=
  eval_quadratic_nonpos_of_nonpos_of_nonpos_of_discrim_nonpos
    (a := -2 / 5) (b := 4 / 5) (c := -2 / 5) (r := r)
    rr_sign_side_term rr_sign_side_term rr_sign_side_term

lemma eval_neg_two_thirds_add_four_thirds_X_sub_two_thirds_X_sq_nonpos {r : ℝ} :
    (C (-2 / 3 : ℝ) + C (4 / 3 : ℝ) * X + C (-2 / 3 : ℝ) * X ^ 2 :
      ℝ[X]).eval r ≤ 0 :=
  eval_quadratic_nonpos_of_nonpos_of_nonpos_of_discrim_nonpos
    (a := -2 / 3) (b := 4 / 3) (c := -2 / 3) (r := r)
    rr_sign_side_term rr_sign_side_term rr_sign_side_term

lemma eval_neg_eight_fifths_add_eight_fifths_X_sub_two_fifths_X_sq_nonpos {r : ℝ} :
    (C (-8 / 5 : ℝ) + C (8 / 5 : ℝ) * X + C (-2 / 5 : ℝ) * X ^ 2 :
      ℝ[X]).eval r ≤ 0 :=
  eval_quadratic_nonpos_of_nonpos_of_nonpos_of_discrim_nonpos
    (a := -8 / 5) (b := 8 / 5) (c := -2 / 5) (r := r)
    rr_sign_side_term rr_sign_side_term rr_sign_side_term

namespace Tactic

syntax (name := rr_sign) "rr_sign" : tactic

macro_rules
  | `(tactic| rr_sign) =>
      `(tactic|
        solve
        | first
          | assumption
          | exact
              RealRooted.eval_X_add_X_sq_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_neg_one_add_two_X_sub_X_sq_nonpos
          | exact RealRooted.eval_neg_one_sub_two_X_sub_X_sq_nonpos
          | exact
              RealRooted.eval_neg_two_fifths_add_four_fifths_X_sub_two_fifths_X_sq_nonpos
          | exact
              RealRooted.eval_neg_two_thirds_add_four_thirds_X_sub_two_thirds_X_sq_nonpos
          | exact
              RealRooted.eval_neg_eight_fifths_add_eight_fifths_X_sub_two_fifths_X_sq_nonpos
          | exact
              RealRooted.eval_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_four_mul_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_nonpos_of_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_two_X_sub_two_X_sq_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_mul_one_sub_X_nonpos_of_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_C_sub_X_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_C_sub_X_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_C_sub_C_mul_X_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_C_sub_C_mul_X_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_one_add_X_nonpos_of_le_neg_one
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_C_add_X_nonpos_of_le_neg
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_C_add_X_nonpos_of_nonneg_of_le_neg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_X_nonpos_of_nonneg_of_ge_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_two_mul_X_nonpos_of_nonneg_of_ge_neg_half
                rr_sign_side_term
                rr_sign_side_term
          | exact RealRooted.eval_X_sub_one_nonpos_of_le_one
              rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sub_one_nonpos_of_nonneg_of_le_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_add_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_add_C_mul_X_sq_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_add_C_mul_X_nonpos_of_nonpos_of_linear_nonneg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_add_C_mul_X_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_sq_sub_one_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sq_sub_one_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_X_mul_one_add_X_nonpos_of_nonneg_of_le_neg_one
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_one_add_X_mul_one_add_two_mul_X_nonpos_of_mem_interval
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_one_add_X_mul_one_add_two_mul_X_nonpos_of_nonneg_of_mem_interval
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_sub_X_sq_nonpos_of_nonpos
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_sq_nonpos_of_nonneg_of_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_one_sub_X_mul_one_add_X_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_one_sub_X_mul_one_add_X_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_sub_X_pow_three_nonpos_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_sub_X_pow_three_nonpos_of_nonneg_of_mem_Icc
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_X_mul_nonpos_of_nonpos_of_nonneg
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_C_mul_X_mul_nonpos_of_nonneg_of_nonpos_of_nonneg
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_sub_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_one_add_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact
              RealRooted.eval_C_neg_add_C_neg_two_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg
                rr_sign_side_term
          | exact RealRooted.eval_C_neg_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_C_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_C_mul_sq_nonpos_of_nonneg
              rr_sign_side_term
          | exact RealRooted.eval_neg_monic_quadratic_nonpos_of_discrim_nonpos
              rr_sign_side_term
          | exact
              RealRooted.eval_neg_C_mul_monic_quadratic_nonpos_of_nonneg_of_discrim_nonpos
                rr_sign_side_term
                rr_sign_side_term
          | exact
              RealRooted.eval_neg_quadratic_nonpos_of_discrim_nonpos
                rr_sign_side_term
                rr_sign_side_term
                rr_sign_side_term
          | simp_all [
              Polynomial.eval_add,
              Polynomial.eval_sub,
              Polynomial.eval_mul,
              Polynomial.eval_pow,
              Polynomial.eval_neg,
              Polynomial.eval_C,
              Polynomial.eval_X,
              sub_eq_add_neg]
            <;>
            first
              | positivity
              | norm_num
              | nlinarith
              | ring_nf <;> nlinarith
              | rr_side
          | positivity
          | norm_num
          | nlinarith
          | ring_nf <;> nlinarith
          | rr_side)

end Tactic
end RealRooted
