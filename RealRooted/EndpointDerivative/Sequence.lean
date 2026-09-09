import RealRooted.EndpointDerivative.Basic

open Polynomial Set

namespace RealRooted

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

end RealRooted
