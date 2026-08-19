import RealRooted.SameDegreeDerivative
import RealRooted.Tactic.MaWang

/-!
# Endpoint-derivative tactic frontends

This module packages the two interval-preserving differential operators

* `q * f.derivative`, and
* `(q * f).derivative`,

where `q = (X - C a) * (X - C b)` and every root of `f` lies in `[a, b]`.
The first operator adjoins the endpoints to the derivative roots. The second
first adjoins the endpoints and then differentiates. Both steps are handled by
the weak Ma--Wang criterion and preserve the interval invariant.
-/

open Polynomial Set

namespace RealRooted

private lemma endpointQuadratic_ne_zero (a b : ℝ) :
    (X - C a) * (X - C b) ≠ (0 : ℝ[X]) :=
  mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)

private lemma natDegree_endpointQuadratic (a b : ℝ) :
    ((X - C a) * (X - C b) : ℝ[X]).natDegree = 2 := by
  rw [natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)]
  simp

private lemma hasPosLeadingCoeff_endpointQuadratic (a b : ℝ) :
    HasPosLeadingCoeff ((X - C a) * (X - C b) : ℝ[X]) :=
  (hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)

private lemma eval_endpointQuadratic_nonpos_of_mem_Icc {a b r : ℝ}
    (hr : r ∈ Icc a b) :
    (((X - C a) * (X - C b) : ℝ[X]).eval r) ≤ 0 := by
  simpa using mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hr.1) (sub_nonpos.mpr hr.2)

private lemma roots_endpointQuadratic_mem_Icc {a b : ℝ} (hab : a ≤ b) :
    ∀ r ∈ ((X - C a) * (X - C b) : ℝ[X]).roots, r ∈ Icc a b := by
  intro r hr
  rw [roots_mul (endpointQuadratic_ne_zero a b), roots_X_sub_C, roots_X_sub_C] at hr
  rcases Multiset.mem_add.mp hr with hr | hr
  · simp only [Multiset.mem_singleton] at hr
    subst r
    exact ⟨le_rfl, hab⟩
  · simp only [Multiset.mem_singleton] at hr
    subst r
    exact ⟨hab, le_rfl⟩

/-- Multiplying the derivative by the endpoint quadratic raises the degree by
one. -/
theorem natDegree_endpointDerivative {f : ℝ[X]} {a b : ℝ}
    (hdeg : 1 ≤ f.natDegree) :
    (((X - C a) * (X - C b)) * f.derivative).natDegree =
      f.natDegree + 1 := by
  rw [natDegree_mul (endpointQuadratic_ne_zero a b)
    (Polynomial.derivative_ne_zero.mpr (by lia))]
  rw [f.natDegree_derivative, natDegree_endpointQuadratic]
  lia

/-- Multiplying the derivative by the endpoint quadratic preserves positivity
of the leading coefficient. -/
theorem hasPosLeadingCoeff_endpointDerivative {f : ℝ[X]} {a b : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : 1 ≤ f.natDegree) :
    HasPosLeadingCoeff (((X - C a) * (X - C b)) * f.derivative) :=
  (hasPosLeadingCoeff_endpointQuadratic a b).mul
    (hf_pos.derivative (by lia))

/-- Differentiating the product with the endpoint quadratic raises the degree
by one. -/
theorem natDegree_derivative_endpointProduct {f : ℝ[X]} {a b : ℝ}
    (hf_pos : HasPosLeadingCoeff f) :
    (((X - C a) * (X - C b) * f).derivative).natDegree =
      f.natDegree + 1 := by
  have hq_ne := endpointQuadratic_ne_zero a b
  have hqf_deg : (((X - C a) * (X - C b)) * f).natDegree =
      f.natDegree + 2 := by
    rw [natDegree_mul hq_ne hf_pos.ne_zero, natDegree_endpointQuadratic]
    lia
  rw [Polynomial.natDegree_derivative, hqf_deg]
  lia

/-- Differentiating the product with the endpoint quadratic preserves
positivity of the leading coefficient. -/
theorem hasPosLeadingCoeff_derivative_endpointProduct {f : ℝ[X]} {a b : ℝ}
    (hf_pos : HasPosLeadingCoeff f) :
    HasPosLeadingCoeff (((X - C a) * (X - C b) * f).derivative) := by
  apply ((hasPosLeadingCoeff_endpointQuadratic a b).mul hf_pos).derivative
  rw [natDegree_mul (endpointQuadratic_ne_zero a b) hf_pos.ne_zero]
  rw [natDegree_endpointQuadratic]
  lia

/-- If the roots of a positive-degree split polynomial lie in `[a,b]`, then
`(X-a)(X-b)f'` is in proper position to its right. -/
theorem prec_endpointDerivative {f : ℝ[X]} {a b : ℝ}
    (hf : f.Splits) (hdeg : 1 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots : ∀ r, f.IsRoot r → r ∈ Icc a b) :
    Prec f (((X - C a) * (X - C b)) * f.derivative) := by
  let q : ℝ[X] := (X - C a) * (X - C b)
  have htarget_deg : (q * f.derivative).natDegree = f.natDegree + 1 := by
    exact natDegree_endpointDerivative hdeg
  have htarget_pos : HasPosLeadingCoeff (q * f.derivative) :=
    hasPosLeadingCoeff_endpointDerivative hf_pos hdeg
  have hprec : Prec f (0 * f + q * f.derivative) :=
    prec_mw_derivative_of_nonpos_of_pos_natDegree hf hdeg
      (by simp only [zero_mul, zero_add]; rw [htarget_deg]; lia)
      (by simp only [zero_mul, zero_add]; rw [htarget_deg])
      (by simpa using htarget_pos) hf_pos (by
        intro r hr
        exact eval_endpointQuadratic_nonpos_of_mem_Icc (hroots r hr))
  simpa [q] using hprec

/-- The roots of `(X-a)(X-b)f'` stay in `[a,b]`. -/
theorem roots_endpointDerivative_mem_Icc {f : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b) (hf : f.Splits) (hdeg : 1 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots : ∀ r, f.IsRoot r → r ∈ Icc a b) :
    ∀ r ∈ (((X - C a) * (X - C b)) * f.derivative).roots,
      r ∈ Icc a b := by
  have hder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hder_roots : ∀ r ∈ f.derivative.roots, r ∈ Icc a b := by
    by_cases hdeg_one : f.natDegree = 1
    · have hder_deg : f.derivative.natDegree = 0 := by rw [f.natDegree_derivative, hdeg_one]
      rw [eq_C_of_natDegree_eq_zero hder_deg]
      simp
    · exact roots_derivative_mem_Icc_of_roots_mem_Icc hf (by lia)
        (fun r hr => hroots r ((mem_roots hf_pos.ne_zero).mp hr))
  intro r hr
  rw [roots_mul
      (mul_ne_zero (endpointQuadratic_ne_zero a b) hder_ne)] at hr
  rcases Multiset.mem_add.mp hr with hr | hr
  · exact roots_endpointQuadratic_mem_Icc hab r hr
  · exact hder_roots r hr

/-- If the roots of `f` lie in `[a,b]`, then the derivative of
`(X-a)(X-b)f` is in proper position to the right of `f`. -/
theorem prec_derivative_endpointProduct {f : ℝ[X]} {a b : ℝ}
    (hf : f.Splits) (hdeg : 1 ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hroots : ∀ r, f.IsRoot r → r ∈ Icc a b) :
    Prec f (((X - C a) * (X - C b) * f).derivative) := by
  let q : ℝ[X] := (X - C a) * (X - C b)
  have htarget_eq :
      (q * f).derivative = q.derivative * f + q * f.derivative := by
    rw [derivative_mul]
  have htarget_deg :
      (q.derivative * f + q * f.derivative).natDegree = f.natDegree + 1 := by
    rw [← htarget_eq]
    exact natDegree_derivative_endpointProduct hf_pos
  have htarget_pos :
      HasPosLeadingCoeff (q.derivative * f + q * f.derivative) := by
    rw [← htarget_eq]
    exact hasPosLeadingCoeff_derivative_endpointProduct hf_pos
  have hprec : Prec f (q.derivative * f + q * f.derivative) :=
    prec_mw_derivative_of_nonpos_of_pos_natDegree hf hdeg
      (by rw [htarget_deg]; lia) (by rw [htarget_deg]) htarget_pos hf_pos (by
        intro r hr
        exact eval_endpointQuadratic_nonpos_of_mem_Icc (hroots r hr))
  simpa [q, derivative_mul] using hprec

/-- The roots of `((X-a)(X-b)f)'` stay in `[a,b]`. -/
theorem roots_derivative_endpointProduct_mem_Icc {f : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b) (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hroots : ∀ r, f.IsRoot r → r ∈ Icc a b) :
    ∀ r ∈ (((X - C a) * (X - C b) * f).derivative).roots,
      r ∈ Icc a b := by
  let q : ℝ[X] := (X - C a) * (X - C b)
  have hq_ne : q ≠ 0 := endpointQuadratic_ne_zero a b
  have hqf_ne : q * f ≠ 0 := mul_ne_zero hq_ne hf_pos.ne_zero
  have hqf_splits : (q * f).Splits :=
    (isRealRooted_mul hq_ne
      ((isRealRooted_X_sub_C a).2.mul (isRealRooted_X_sub_C b).2)
      hf_pos.ne_zero hf).2
  have hqf_deg : 2 ≤ (q * f).natDegree := by
    rw [natDegree_mul hq_ne hf_pos.ne_zero]
    rw [show q.natDegree = 2 by exact natDegree_endpointQuadratic a b]
    lia
  have hqf_roots : ∀ r ∈ (q * f).roots, r ∈ Icc a b := by
    intro r hr
    rw [roots_mul hqf_ne] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · exact roots_endpointQuadratic_mem_Icc hab r hr
    · exact hroots r ((mem_roots hf_pos.ne_zero).mp hr)
  exact roots_derivative_mem_Icc_of_roots_mem_Icc
    hqf_splits hqf_deg hqf_roots

/-- Iterating `(X-a)(X-b)f'` preserves the root interval and gives a `Prec`
chain. -/
theorem prec_endpointDerivative_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = ((X - C a) * (X - C b)) * (P n).derivative) :
    ∀ n, Prec (P n) (P (n + 1)) := by
  have hinv : ∀ n, (P n).Splits ∧ ∀ r ∈ (P n).roots, r ∈ Icc a b := by
    intro n
    induction n with
    | zero => exact ⟨hbase_splits, hbase_roots⟩
    | succ n ih =>
        have hprec := prec_endpointDerivative ih.1 (hdeg n) (hpos n)
          (fun r hr => ih.2 r ((mem_roots (hpos n).ne_zero).mpr hr))
        constructor
        · rw [hrec n]
          exact hprec.2.1.2
        · rw [hrec n]
          exact roots_endpointDerivative_mem_Icc
            hab ih.1 (hdeg n) (hpos n)
              (fun r hr => ih.2 r ((mem_roots (hpos n).ne_zero).mpr hr))
  intro n
  rw [hrec n]
  exact prec_endpointDerivative (hinv n).1 (hdeg n) (hpos n)
    (fun r hr => (hinv n).2 r ((mem_roots (hpos n).ne_zero).mpr hr))

/-- Iterating `((X-a)(X-b)f)'` preserves the root interval and gives a `Prec`
chain. -/
theorem prec_derivative_endpointProduct_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = (((X - C a) * (X - C b)) * P n).derivative) :
    ∀ n, Prec (P n) (P (n + 1)) := by
  have hinv : ∀ n, (P n).Splits ∧ ∀ r ∈ (P n).roots, r ∈ Icc a b := by
    intro n
    induction n with
    | zero => exact ⟨hbase_splits, hbase_roots⟩
    | succ n ih =>
        have hprec := prec_derivative_endpointProduct ih.1 (hdeg n) (hpos n)
          (fun r hr => ih.2 r ((mem_roots (hpos n).ne_zero).mpr hr))
        constructor
        · rw [hrec n]
          exact hprec.2.1.2
        · rw [hrec n]
          exact roots_derivative_endpointProduct_mem_Icc
            hab ih.1 (hpos n)
              (fun r hr => ih.2 r ((mem_roots (hpos n).ne_zero).mpr hr))
  intro n
  rw [hrec n]
  exact prec_derivative_endpointProduct (hinv n).1 (hdeg n) (hpos n)
    (fun r hr => (hinv n).2 r ((mem_roots (hpos n).ne_zero).mpr hr))

theorem interlaces_endpointDerivative_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = ((X - C a) * (X - C b)) * (P n).derivative)
    (hdeg_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n, Interlaces (P n) (P (n + 1)) := fun n =>
  (prec_endpointDerivative_sequence
    hab hbase_splits hbase_roots hpos hdeg hrec n).toInterlaces (hdeg_succ n)

theorem interlaces_derivative_endpointProduct_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = (((X - C a) * (X - C b)) * P n).derivative)
    (hdeg_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n, Interlaces (P n) (P (n + 1)) := fun n =>
  (prec_derivative_endpointProduct_sequence
    hab hbase_splits hbase_roots hpos hdeg hrec n).toInterlaces (hdeg_succ n)

theorem isRealRooted_endpointDerivative_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = ((X - C a) * (X - C b)) * (P n).derivative) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := fun n =>
  (prec_endpointDerivative_sequence
    hab hbase_splits hbase_roots hpos hdeg hrec n).1

theorem isRealRooted_derivative_endpointProduct_sequence
    {P : ℕ → ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hbase_splits : (P 0).Splits)
    (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hdeg : ∀ n, 1 ≤ (P n).natDegree)
    (hrec : ∀ n,
      P (n + 1) = (((X - C a) * (X - C b)) * P n).derivative) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := fun n =>
  (prec_derivative_endpointProduct_sequence
    hab hbase_splits hbase_roots hpos hdeg hrec n).1

namespace Tactic

syntax (name := rr_endpoint_derivative_sequence_named)
  "rr_endpoint_derivative_sequence" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

syntax (name := rr_endpoint_derivative_sequence_interlaces_named)
  "rr_endpoint_derivative_sequence_interlaces" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term : tactic

syntax (name := rr_endpoint_derivative_sequence_realrooted_named)
  "rr_endpoint_derivative_sequence_realrooted" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

syntax (name := rr_endpoint_product_derivative_sequence_named)
  "rr_endpoint_product_derivative_sequence" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

syntax (name := rr_endpoint_product_derivative_sequence_interlaces_named)
  "rr_endpoint_product_derivative_sequence_interlaces" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term : tactic

syntax (name := rr_endpoint_product_derivative_sequence_realrooted_named)
  "rr_endpoint_product_derivative_sequence_realrooted" " using "
    "lower_le_upper" ":=" term ","
    "base_splits" ":=" term ","
    "base_roots" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_pos" ":=" term ","
    "recurrence" ":=" term : tactic

macro_rules
  | `(tactic|
      rr_endpoint_derivative_sequence using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic| exact prec_endpointDerivative_sequence $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_derivative_sequence_interlaces using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term,
        degree_succ := $hds:term) =>
      `(tactic|
        exact interlaces_endpointDerivative_sequence
          $hab $hs $hr $hp $hd $hrec $hds)
  | `(tactic|
      rr_endpoint_derivative_sequence_realrooted using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact isRealRooted_endpointDerivative_sequence $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_product_derivative_sequence using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact prec_derivative_endpointProduct_sequence $hab $hs $hr $hp $hd $hrec)
  | `(tactic|
      rr_endpoint_product_derivative_sequence_interlaces using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term,
        degree_succ := $hds:term) =>
      `(tactic|
        exact interlaces_derivative_endpointProduct_sequence
          $hab $hs $hr $hp $hd $hrec $hds)
  | `(tactic|
      rr_endpoint_product_derivative_sequence_realrooted using
        lower_le_upper := $hab:term,
        base_splits := $hs:term,
        base_roots := $hr:term,
        pos_lc := $hp:term,
        degree_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact isRealRooted_derivative_endpointProduct_sequence
          $hab $hs $hr $hp $hd $hrec)

end Tactic
end RealRooted
