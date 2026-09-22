import RealRooted.JacobiDeformation.AppellOperatorIdentity

/-!
# The scalar Appell-coordinate summand bridge

The actual Appell coefficient at the two scalar coordinates is one actual
Jacobi-deformation summand, with its remaining power of `xi` explicit.
-/

namespace RealRooted.JacobiDeformation

private theorem neg_one_pow_twice (a b : ℕ) :
    (-1 : ℝ) ^ a * (-1 : ℝ) ^ a * (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = 1 := by
  calc
    (-1 : ℝ) ^ a * (-1 : ℝ) ^ a * (-1 : ℝ) ^ b * (-1 : ℝ) ^ b =
        ((-1 : ℝ) ^ a * (-1 : ℝ) ^ a) * ((-1 : ℝ) ^ b * (-1 : ℝ) ^ b) := by
      ring
    _ = (-1 : ℝ) ^ (a + a) * (-1 : ℝ) ^ (b + b) := by
      rw [← pow_add, ← pow_add]
    _ = (-1 : ℝ) ^ ((a + a) + (b + b)) := by
      rw [← pow_add]
    _ = ((-1 : ℝ) ^ 2) ^ (a + b) := by
      rw [show (a + a) + (b + b) = 2 * (a + b) by ring, pow_mul]
    _ = 1 := by norm_num

/-- Evaluating one actual Appell kernel coefficient at the two scalar
coordinates gives the corresponding actual deformation summand. -/
theorem appellKernelCoefficient_coordinate_eq_summand (m i j : ℕ)
    (δ c d U V xi r z : ℝ) (hij : i + j ≤ m)
    (hU : xi * r * z = -U) (hV : xi * (1 - r) * (1 - z) = -V) :
    (-1 : ℝ) ^ m * xi ^ m *
        appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d i j *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      summand m δ c d U V i j * xi ^ (m - i - j) := by
  have hsplit : xi ^ m = xi ^ (i + j) * xi ^ (m - i - j) := by
    rw [← pow_add]
    congr 1
    lia
  have hU_pow : xi ^ i * (r * z) ^ i = (-U) ^ i := by
    calc
      xi ^ i * (r * z) ^ i = (xi * (r * z)) ^ i := (mul_pow _ _ _).symm
      _ = (-U) ^ i := by rw [show xi * (r * z) = xi * r * z by ring, hU]
  have hV_pow : xi ^ j * ((1 - r) * (1 - z)) ^ j = (-V) ^ j := by
    calc
      xi ^ j * ((1 - r) * (1 - z)) ^ j =
          (xi * ((1 - r) * (1 - z))) ^ j := (mul_pow _ _ _).symm
      _ = (-V) ^ j := by
        rw [show xi * ((1 - r) * (1 - z)) = xi * (1 - r) * (1 - z) by ring, hV]
  have hcoordinates : xi ^ (i + j) * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j := by
    rw [pow_add, hU_pow, hV_pow]
    simp only [neg_pow]
    rw [← pow_add]
    ring
  have hxi_coordinates : xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j) := by
    calc
      xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
          (xi ^ (i + j) * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j) *
            xi ^ (m - i - j) := by
        rw [hsplit]
        ring
      _ = (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j) := by
        rw [hcoordinates]
  have hnegative : risingFactorial (-(m : ℝ)) (i + j) =
      (-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ) := by
    rw [risingFactorial, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial]
  have hfactorial : ((m - (i + j)).factorial : ℝ) *
      (m.descFactorial (i + j) : ℝ) = (m.factorial : ℝ) := by
    have hfactorial' := Nat.factorial_mul_descFactorial hij
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hfactorial'
  have hfactorial_ne : ((m - (i + j)).factorial : ℝ) ≠ 0 := by
    positivity
  have hratio : (m.descFactorial (i + j) : ℝ) =
      (m.factorial : ℝ) / ((m - (i + j)).factorial : ℝ) := by
    apply (eq_div_iff hfactorial_ne).2
    simpa [mul_comm] using hfactorial
  have hsub : m - i - j = m - (i + j) := by lia
  have hkernel :
      (-1 : ℝ) ^ m * xi ^ m *
          ((-1 : ℝ) ^ m * ((-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ)) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)) *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
        (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
          (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
            (risingFactorial c i * risingFactorial d j)) *
          U ^ i * V ^ j * xi ^ (m - i - j) := by
    calc
      (-1 : ℝ) ^ m * xi ^ m *
          ((-1 : ℝ) ^ m * ((-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ)) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)) *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
          ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m * (-1 : ℝ) ^ (i + j)) *
            (m.descFactorial (i + j) : ℝ) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial) *
            (xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j) := by
        ring
      _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m * (-1 : ℝ) ^ (i + j)) *
            (m.descFactorial (i + j) : ℝ) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial) *
            ((-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j)) := by
        rw [hxi_coordinates]
      _ = (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
            (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j)) *
            U ^ i * V ^ j * xi ^ (m - i - j) := by
        rw [show (-1 : ℝ) ^ m * (-1 : ℝ) ^ m * (-1 : ℝ) ^ (i + j) *
            (-1 : ℝ) ^ (i + j) = 1 by exact neg_one_pow_twice m (i + j)]
        ring
  calc
    (-1 : ℝ) ^ m * xi ^ m *
        appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d i j *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
        (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
          (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
            (risingFactorial c i * risingFactorial d j)) *
          U ^ i * V ^ j * xi ^ (m - i - j) := by
      rw [appellKernelCoefficient, if_pos hij, hnegative]
      exact hkernel
    _ = summand m δ c d U V i j * xi ^ (m - i - j) := by
      unfold summand
      rw [hsub, ← hratio]
      ring

end RealRooted.JacobiDeformation
