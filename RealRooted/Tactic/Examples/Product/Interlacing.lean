import RealRooted.Tactic.Product.Interlacing

/-!
# `rr_product_natDegree` / `rr_product_interlaces` examples

Regression tests for OEIS product sequences `P (n + 1) = L n * P n`, drawn from
`real-rooted-oeis-proofs`: integer, `n`-dependent, and rational linear factors,
and constant, square, and quadratic base rows.
-/

open Polynomial

namespace RealRooted.Tactic.ProductInterlacingExamples

noncomputable section

def A007318 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * A007318 n

theorem A007318_natDegree (n : ℕ) : (A007318 n).natDegree = n := by rr_product_natDegree
theorem A007318_interlaces (n : ℕ) : Interlaces (A007318 n) (A007318 (n + 1)) := by
  rr_product_interlaces

def A008955 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + C ((n + 1 : ℝ) ^ 2) * X) * A008955 n

theorem A008955_natDegree (n : ℕ) : (A008955 n).natDegree = n := by rr_product_natDegree
theorem A008955_interlaces (n : ℕ) : Interlaces (A008955 n) (A008955 (n + 1)) := by
  rr_product_interlaces

def A088996 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (n : ℝ) + C (n + 1 : ℝ) * X) * A088996 n

theorem A088996_natDegree (n : ℕ) : (A088996 n).natDegree = n := by rr_product_natDegree
theorem A088996_interlaces (n : ℕ) : Interlaces (A088996 n) (A088996 (n + 1)) := by
  rr_product_interlaces

def A178820 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C ((n + 4 : ℝ) / (n + 1)) + C ((n + 4 : ℝ) / (n + 1)) * X) * A178820 n

theorem A178820_natDegree (n : ℕ) : (A178820 n).natDegree = n := by rr_product_natDegree
theorem A178820_interlaces (n : ℕ) : Interlaces (A178820 n) (A178820 (n + 1)) := by
  rr_product_interlaces

def A269947 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C ((n + 2 : ℝ) ^ 3 + 16) + X) * A269947 n

theorem A269947_natDegree (n : ℕ) : (A269947 n).natDegree = n := by rr_product_natDegree
theorem A269947_interlaces (n : ℕ) : Interlaces (A269947 n) (A269947 (n + 1)) := by
  rr_product_interlaces

def A013612 : ℕ → ℝ[X]
  | 0 => 1 + 10 * X + 25 * X ^ 2
  | n + 1 => (1 + 5 * X) * A013612 n

theorem A013612_natDegree (n : ℕ) : (A013612 n).natDegree = n + 2 := by rr_product_natDegree
theorem A013612_interlaces (n : ℕ) : Interlaces (A013612 n) (A013612 (n + 1)) := by
  rr_product_interlaces

def A038226 : ℕ → ℝ[X]
  | 0 => 9 + 48 * X + 64 * X ^ 2
  | n + 1 => (3 + 8 * X) * A038226 n

theorem A038226_natDegree (n : ℕ) : (A038226 n).natDegree = n + 2 := by rr_product_natDegree
theorem A038226_interlaces (n : ℕ) : Interlaces (A038226 n) (A038226 (n + 1)) := by
  rr_product_interlaces

def A159854 : ℕ → ℝ[X]
  | 0 => X ^ 2
  | n + 1 => (1 + X) * A159854 n

theorem A159854_natDegree (n : ℕ) : (A159854 n).natDegree = n + 2 := by rr_product_natDegree
theorem A159854_interlaces (n : ℕ) : Interlaces (A159854 n) (A159854 (n + 1)) := by
  rr_product_interlaces

def A028326 : ℕ → ℝ[X]
  | 0 => 2
  | n + 1 => (1 + X) * A028326 n

theorem A028326_natDegree (n : ℕ) : (A028326 n).natDegree = n := by rr_product_natDegree
theorem A028326_interlaces (n : ℕ) : Interlaces (A028326 n) (A028326 (n + 1)) := by
  rr_product_interlaces

end

end RealRooted.Tactic.ProductInterlacingExamples
