import RealRooted.BrandenLeite.KernelClosure
import RealRooted.BrandenLeite.TwoKernelAlgebra
import RealRooted.BrandenLeite.ZeroConstant

/-!
# The two-kernel PF and proper-position theorem

We approximate the zero-constant PF kernel by the positive-initial PF
sequences extracted in `ZeroConstant`, apply the finite kernel-limit theorem,
and identify its rows with the literal two-kernel coefficient polynomials.
-/

open Filter Matrix Polynomial Topology

namespace RealRooted.BrandenLeite

noncomputable section

/-- Finite Toeplitz truncations of PF sequences are totally nonnegative. -/
theorem finiteToeplitz_isTotallyNonneg
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (N : ℕ) :
    (finiteToeplitz a N).IsTotallyNonneg := by
  change (toeplitz a).IsTotallyNonneg at ha
  exact ha.submatrix
    (fun _ _ hij => by simpa using hij)
    (fun _ _ hij => by simpa using hij)

/-- The finite Toeplitz kernels satisfy the complete PF and consecutive
zero-aware proper-position conclusion of the matrix-limit theorem. -/
theorem finiteToeplitz_kernelRows_pf_and_prec0
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : h 0 = 0) (N : ℕ) :
    (∀ i : Fin (N + 1),
        IsPFPolynomial (kernelRow (finiteToeplitz g N) (finiteToeplitz h N) i)) ∧
      ∀ i : Fin N,
        Interl
          (kernelRow (finiteToeplitz g N) (finiteToeplitz h N) i.castSucc)
          (kernelRow (finiteToeplitz g N) (finiteToeplitz h N) i.succ) := by
  obtain ⟨a, ha_pf, ha0pos, halim⟩ :=
    exists_pf_pos_zero_approximation_of_pf hh
  let G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := finiteToeplitz g N
  let H : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    fun m => finiteToeplitz (a m) N
  let K : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := finiteToeplitz h N
  have hG : G.IsTotallyNonneg := finiteToeplitz_isTotallyNonneg hg N
  have hH : ∀ m, (H m).IsTotallyNonneg := by
    intro m
    exact finiteToeplitz_isTotallyNonneg (ha_pf m) N
  have hGlower : ∀ i j, i < j → G i j = 0 := by
    intro i j hij
    change finiteToeplitz g N i j = 0
    rw [finiteToeplitz_apply, if_neg (not_le_of_gt hij)]
  have hHlower : ∀ m i j, i < j → H m i j = 0 := by
    intro m i j hij
    change finiteToeplitz (a m) N i j = 0
    rw [finiteToeplitz_apply, if_neg (not_le_of_gt hij)]
  have hKstrict : ∀ i j, i.val ≤ j.val → K i j = 0 := by
    intro i j hij
    change finiteToeplitz h N i j = 0
    rw [finiteToeplitz_apply]
    by_cases hji : j ≤ i
    · have hEq : i = j := le_antisymm (Fin.mk_le_mk.mpr hij) hji
      subst j
      simp [hh0]
    · simp [hji]
  have hGdiag : ∀ i, G i i = g 0 := by
    intro i
    simp [G, finiteToeplitz_apply]
  have hHdiag : ∀ m i, H m i i = a m 0 := by
    intro m i
    simp [H, finiteToeplitz_apply]
  have hlim : ∀ i j, Tendsto (fun m => H m i j) atTop (𝓝 (K i j)) := by
    intro i j
    by_cases hji : j ≤ i
    · simpa [H, K, finiteToeplitz_apply, hji] using
        halim (i.val - j.val)
    · simp [H, K, finiteToeplitz_apply, hji]
  change
    (∀ i : Fin (N + 1), IsPFPolynomial (kernelRow G K i)) ∧
      ∀ i : Fin N, Interl (kernelRow G K i.castSucc)
        (kernelRow G K i.succ)
  exact kernelRows_pf_and_prec0_of_tendsto hg0 ha0pos hG hH
    hGlower hHlower hKstrict hGdiag hHdiag hlim

/-- Literal two-kernel specialization of the Brändén--Saud Leite theorem.
For PF coefficient sequences `g,h`, with positive `g(0)` and zero `h(0)`,
every coefficient row of `g(z)/(1-X*g(z)*h(z))` is PF and consecutive rows
are in zero-aware proper position. -/
theorem twoKernelRows_pf_and_prec0
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : h 0 = 0) :
    (∀ n, IsPFPolynomial
        (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n)) ∧
      ∀ n, Interl
        (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n)
        (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) (n + 1)) := by
  have hzero : PowerSeries.constantCoeff (PowerSeries.mk h) = 0 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hh0
  constructor
  · intro n
    have hfinite := finiteToeplitz_kernelRows_pf_and_prec0 hg hh hg0 hh0 n
    have heq :
        twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n =
          kernelRow (finiteToeplitz g n) (finiteToeplitz h n)
            (Fin.last n) := by
      simpa using twoKernelRow_eq_kernelRow_fin
        (g := PowerSeries.mk g) hzero (Fin.last n)
    rw [heq]
    exact hfinite.1 (Fin.last n)
  · intro n
    have hfinite :=
      finiteToeplitz_kernelRows_pf_and_prec0 hg hh hg0 hh0 (n + 1)
    have heqLeft :
        twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n =
          kernelRow (finiteToeplitz g (n + 1)) (finiteToeplitz h (n + 1))
            (Fin.last n).castSucc := by
      simpa using twoKernelRow_eq_kernelRow_fin
        (g := PowerSeries.mk g) hzero (Fin.last n).castSucc
    have heqRight :
        twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) (n + 1) =
          kernelRow (finiteToeplitz g (n + 1)) (finiteToeplitz h (n + 1))
            (Fin.last n).succ := by
      simpa using twoKernelRow_eq_kernelRow_fin
        (g := PowerSeries.mk g) hzero (Fin.last n).succ
    rw [heqLeft, heqRight]
    exact hfinite.2 (Fin.last n)

/-- Each literal two-kernel row is a PF polynomial. -/
theorem twoKernelRow_isPFPolynomial
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : h 0 = 0) (n : ℕ) :
    IsPFPolynomial (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n) :=
  (twoKernelRows_pf_and_prec0 hg hh hg0 hh0).1 n

/-- Consecutive literal two-kernel rows are in zero-aware proper position. -/
theorem prec0_twoKernelRow_succ
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : h 0 = 0) (n : ℕ) :
    Interl
      (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) n)
      (twoKernelRow (PowerSeries.mk g) (PowerSeries.mk h) (n + 1)) :=
  (twoKernelRows_pf_and_prec0 hg hh hg0 hh0).2 n

end

end RealRooted.BrandenLeite
