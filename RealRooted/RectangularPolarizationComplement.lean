import RealRooted.MultiaffineReciprocal
import RealRooted.RectangularPolarization

/-!
# Complementary rectangular polarization

This file defines the signed reciprocal rectangular polarization used in the
Gribinski--Marcus differential representation of rectangular convolution.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section


/-- The signed multiaffine reciprocal of a rectangular polarization. -/
def reciprocalRectangularPolarization (m n : ℕ) (p : ℂ[X]) :
    MvPolynomial (Sum (Fin n) (Fin (m + n))) ℂ :=
  MvPolynomial.C ((-1 : ℂ) ^ m) *
    signedMultiaffineReciprocal (rectangularPolarization m n p)

private theorem reciprocalRectangularPolarization_indexed (m n : ℕ) (p : ℂ[X]) :
    reciprocalRectangularPolarization m n p =
      ∑ k ∈ Finset.range (n + 1),
        MvPolynomial.C
            (p.coeff k / (n.choose k : ℂ) /
              ((m + n).choose (m + k) : ℂ)) *
          MvPolynomial.rename Sum.inl
            (MvPolynomial.esymm (Fin n) ℂ (n - k)) *
          MvPolynomial.rename Sum.inr
            (MvPolynomial.esymm (Fin (m + n)) ℂ (n - k)) := by
  unfold reciprocalRectangularPolarization rectangularPolarization
  rw [signedMultiaffineReciprocal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hmkn : m + k ≤ m + n := Nat.add_le_add_left hkn m
  have hleft : MvPolynomial.IsMultiaffine
      (MvPolynomial.esymm (Fin n) ℂ k) :=
    MvPolynomial.IsMultiaffine.esymm k
  have hright : MvPolynomial.IsMultiaffine
      (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k)) :=
    MvPolynomial.IsMultiaffine.esymm (m + k)
  have hblock : MvPolynomial.IsMultiaffine
      (MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin n) ℂ k) *
        MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))) := by
    apply (hleft.rename Sum.inl_injective).mul_of_disjoint_vars
      (hright.rename Sum.inr_injective)
    rw [Finset.disjoint_left]
    intro v hvleft hvright
    obtain ⟨i, hi, hiv⟩ := MvPolynomial.mem_vars_rename Sum.inl
      (MvPolynomial.esymm (Fin n) ℂ k) hvleft
    obtain ⟨j, hj, hjv⟩ := MvPolynomial.mem_vars_rename Sum.inr
      (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k)) hvright
    exact Sum.inl_ne_inr (hiv.trans hjv.symm)
  rw [mul_assoc, signedMultiaffineReciprocal_C_mul hblock,
    signedMultiaffineReciprocal_rename_mul_rename hleft hright,
    signedMultiaffineReciprocal_esymm n k hkn,
    signedMultiaffineReciprocal_esymm (m + n) (m + k) hmkn]
  simp only [map_mul, MvPolynomial.rename_C]
  rw [show m + n - (m + k) = n - k by lia]
  have hsign :
      (-1 : ℂ) ^ m * ((-1 : ℂ) ^ k * (-1 : ℂ) ^ (m + k)) = 1 := by
    rw [pow_add]
    ring_nf
    simp
  have hCsign :
      (MvPolynomial.C ((-1 : ℂ) ^ m) *
          MvPolynomial.C ((-1 : ℂ) ^ k) *
        MvPolynomial.C ((-1 : ℂ) ^ (m + k)) :
          MvPolynomial (Sum (Fin n) (Fin (m + n))) ℂ) = 1 := by
    rw [← map_mul, ← map_mul,
      show (-1 : ℂ) ^ m * (-1 : ℂ) ^ k * (-1 : ℂ) ^ (m + k) = 1 by
        simpa [mul_assoc] using hsign,
      map_one]
  calc
    _ = (MvPolynomial.C ((-1 : ℂ) ^ m) *
            MvPolynomial.C ((-1 : ℂ) ^ k) *
          MvPolynomial.C ((-1 : ℂ) ^ (m + k))) *
        MvPolynomial.C
          (p.coeff k / (n.choose k : ℂ) /
            ((m + n).choose (m + k) : ℂ)) *
        MvPolynomial.rename Sum.inl
          (MvPolynomial.esymm (Fin n) ℂ (n - k)) *
        MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm (Fin (m + n)) ℂ (n - k)) := by ring
    _ = _ := by rw [hCsign, one_mul]

/-- Explicit elementary-symmetric expansion of the reciprocal rectangular
polarization. -/
theorem reciprocalRectangularPolarization_explicit (m n : ℕ) (p : ℂ[X]) :
    reciprocalRectangularPolarization m n p =
      ∑ i ∈ Finset.range (n + 1),
        MvPolynomial.C
            (p.coeff (n - i) / (n.choose i : ℂ) /
              ((m + n).choose i : ℂ)) *
          MvPolynomial.rename Sum.inl
            (MvPolynomial.esymm (Fin n) ℂ i) *
          MvPolynomial.rename Sum.inr
            (MvPolynomial.esymm (Fin (m + n)) ℂ i) := by
  rw [reciprocalRectangularPolarization_indexed]
  rw [← Finset.sum_range_reflect
    (fun k =>
      MvPolynomial.C
          (p.coeff k / (n.choose k : ℂ) /
            ((m + n).choose (m + k) : ℂ)) *
        MvPolynomial.rename Sum.inl
          (MvPolynomial.esymm (Fin n) ℂ (n - k)) *
        MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm (Fin (m + n)) ℂ (n - k))) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hrefl : n + 1 - 1 - i = n - i := by lia
  rw [hrefl, show n - (n - i) = i by lia]
  rw [Nat.choose_symm hin]
  rw [show m + (n - i) = m + n - i by lia]
  rw [← Nat.choose_symm (by lia : i ≤ m + n)]

/-- The reciprocal rectangular polarization is multiaffine. -/
theorem isMultiaffine_reciprocalRectangularPolarization
    (m n : ℕ) (p : ℂ[X]) :
    MvPolynomial.IsMultiaffine
      (reciprocalRectangularPolarization m n p) := by
  unfold reciprocalRectangularPolarization
  exact (isMultiaffine_signedMultiaffineReciprocal
    (rectangularPolarization m n p)).C_mul _

/-- Reciprocal rectangular polarization preserves upper-half-plane stability. -/
theorem mvUpperHalfPlaneStable_reciprocalRectangularPolarization
    {m n : ℕ} {p : ℂ[X]} (hpdeg : p.natDegree = n)
    (hplead : p.leadingCoeff ≠ 0)
    (hstable : MvUpperHalfPlaneStable (xyLift p)) :
    MvUpperHalfPlaneStable (reciprocalRectangularPolarization m n p) := by
  unfold reciprocalRectangularPolarization
  apply MvUpperHalfPlaneStable.C_mul
  · exact (mvUpperHalfPlaneStable_rectangularPolarization hpdeg hplead hstable)
      |>.signedMultiaffineReciprocal
        (isMultiaffine_rectangularPolarization m n p)
  · exact pow_ne_zero m (by norm_num)

end

end RealRooted
