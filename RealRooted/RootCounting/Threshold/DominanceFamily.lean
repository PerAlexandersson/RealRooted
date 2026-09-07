import RealRooted.RootCounting.Threshold.LogConcavity
import RealRooted.RootCounting.Threshold.Signs

/-!
# Geometrically separated roots from coefficient dominance

Strengthened local log-concavity creates pairs of dominance radii. Alternating
signs at those radii yield families of negative roots whose magnitudes are
geometrically separated. The endpoint estimates and intermediate-value
chaining live in the lower `LogConcavity` and `Signs` modules.
-/

namespace RealRooted.RootCounting

open Polynomial

noncomputable section

/-- The lower magnitude at which coefficient `j` is made dominant. -/
private def lowerDominanceRadius (p : ℝ[X]) (c : ℝ) (j : ℕ) : ℝ :=
  c * p.coeff (j - 1) / p.coeff j

/-- The upper magnitude at which coefficient `j` is made dominant. -/
private def upperDominanceRadius (p : ℝ[X]) (c : ℝ) (j : ℕ) : ℝ :=
  p.coeff j / (c * p.coeff (j + 1))

private theorem lowerDominanceRadius_pos {p : ℝ[X]} {N j : ℕ} {c : ℝ}
    (hc : 0 < c) (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hj : 1 ≤ j) (hjN : j ≤ N) :
    0 < lowerDominanceRadius p c j := by
  rw [lowerDominanceRadius]
  exact div_pos (mul_pos hc (hpos (j - 1) (by lia))) (hpos j hjN)

private theorem upperDominanceRadius_pos {p : ℝ[X]} {N j : ℕ} {c : ℝ}
    (hc : 0 < c) (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hnext : j + 1 ≤ N) :
    0 < upperDominanceRadius p c j := by
  rw [upperDominanceRadius]
  exact div_pos (hpos j (by lia)) (mul_pos hc (hpos (j + 1) hnext))

private theorem dominanceRadii_separated {p : ℝ[X]} {N j : ℕ} {c theta : ℝ}
    (hc : 0 < c) (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    (hstrong : c ^ 2 * theta * (p.coeff (j - 1) * p.coeff (j + 1)) ≤
      (p.coeff j) ^ 2) :
    theta * lowerDominanceRadius p c j ≤ upperDominanceRadius p c j := by
  have h1 := hpos (j - 1) (by lia)
  have h2 := hpos j (by lia)
  have h3 := hpos (j + 1) hnext
  rw [lowerDominanceRadius, upperDominanceRadius, mul_div_assoc',
    div_le_div_iff₀ h2 (mul_pos hc h3)]
  nlinarith

private theorem lowerDominanceRadius_sign {p : ℝ[X]} {N j : ℕ} {c theta : ℝ}
    (hc : 3 < c) (htheta : 1 < theta) (hdegree : p.natDegree = N)
    (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    (hstrong : c ^ 2 * theta * (p.coeff (j - 1) * p.coeff (j + 1)) ≤
      (p.coeff j) ^ 2) :
    0 < (-1 : ℝ) ^ j * p.eval (-(lowerDominanceRadius p c j)) := by
  have hc0 : 0 < c := by linarith
  have h1 := hpos (j - 1) (by lia)
  have h2 := hpos j (by lia)
  have h3 := hpos (j + 1) hnext
  have hradius := lowerDominanceRadius_pos hc0 hpos hj (by lia)
  have hid : p.coeff j * lowerDominanceRadius p c j =
      c * p.coeff (j - 1) := by
    rw [lowerDominanceRadius]
    field_simp
  refine sign_of_dominant_logConcave_of_adjacent_bounds hdegree hpos
    hlog_concave j hj hnext hradius (hupper := ?_) (hlower := ?_)
  · have hexp : 3 * p.coeff (j + 1) * lowerDominanceRadius p c j =
        3 * p.coeff (j + 1) * (c * p.coeff (j - 1)) / p.coeff j := by
      rw [lowerDominanceRadius]
      ring
    rw [hexp, div_lt_iff₀ h2]
    nlinarith [hstrong, mul_pos h1 h3,
      mul_pos (mul_pos (by linarith : (0 : ℝ) < c - 3)
        (by linarith : (0 : ℝ) < c)) (mul_pos h1 h3),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ theta - 1)
        (by positivity : (0 : ℝ) ≤ c ^ 2)) (le_of_lt (mul_pos h1 h3))]
  · nlinarith [hid, mul_pos (by linarith : (0 : ℝ) < c - 3) h1]

private theorem upperDominanceRadius_sign {p : ℝ[X]} {N j : ℕ} {c theta : ℝ}
    (hc : 3 < c) (htheta : 1 < theta) (hdegree : p.natDegree = N)
    (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    (hj : 1 ≤ j) (hnext : j + 1 ≤ N)
    (hstrong : c ^ 2 * theta * (p.coeff (j - 1) * p.coeff (j + 1)) ≤
      (p.coeff j) ^ 2) :
    0 < (-1 : ℝ) ^ j * p.eval (-(upperDominanceRadius p c j)) := by
  have hc0 : 0 < c := by linarith
  have h1 := hpos (j - 1) (by lia)
  have h2 := hpos j (by lia)
  have h3 := hpos (j + 1) hnext
  have hradius := upperDominanceRadius_pos hc0 hpos hnext
  have hid : c * (p.coeff (j + 1) * upperDominanceRadius p c j) =
      p.coeff j := by
    rw [upperDominanceRadius]
    field_simp
  refine sign_of_dominant_logConcave_of_adjacent_bounds hdegree hpos
    hlog_concave j hj hnext hradius (hupper := ?_) (hlower := ?_)
  · nlinarith [hid, mul_pos (by linarith : (0 : ℝ) < c - 3) h2]
  · have hexp : p.coeff j * upperDominanceRadius p c j =
        p.coeff j * p.coeff j / (c * p.coeff (j + 1)) := by
      rw [upperDominanceRadius]
      ring
    rw [hexp, lt_div_iff₀ (mul_pos hc0 h3)]
    nlinarith [hstrong, mul_pos h1 h3,
      mul_pos (mul_pos (by linarith : (0 : ℝ) < c - 3)
        (by linarith : (0 : ℝ) < c)) (mul_pos h1 h3),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ theta - 1)
        (by positivity : (0 : ℝ) ≤ c ^ 2)) (le_of_lt (mul_pos h1 h3))]

private theorem eval_one_pos_of_coeff_pos {p : ℝ[X]} {N : ℕ}
    (hdegree : p.natDegree = N)
    (hpos : ∀ i, i ≤ N → 0 < p.coeff i) :
    0 < p.eval 1 := by
  apply eval_pos_of_hasNonnegCoeffs ?_ ?_ one_pos
  · intro i
    by_cases hi : i ≤ N
    · exact (hpos i hi).le
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [hdegree]
      lia
  · intro hp
    subst p
    simpa using hpos 0 (Nat.zero_le N)

private theorem upperDominanceRadius_lt_lowerDominanceRadius_succ
    {p : ℝ[X]} {N j : ℕ} {c : ℝ}
    (hc : 1 < c) (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hnext : j + 1 ≤ N) :
    upperDominanceRadius p c j < lowerDominanceRadius p c (j + 1) := by
  have hc0 : 0 < c := by linarith
  have h2 := hpos j (by lia)
  have h3 := hpos (j + 1) hnext
  rw [upperDominanceRadius, lowerDominanceRadius]
  have hidx : j + 1 - 1 = j := by lia
  rw [hidx, div_lt_div_iff₀ (mul_pos hc0 h3) h3]
  nlinarith [mul_pos h2 h3,
    mul_pos (mul_pos (by linarith : (0 : ℝ) < c - 1)
      (by linarith : (0 : ℝ) < c + 1)) (mul_pos h2 h3)]

/-- Strong log-concavity on an initial coefficient range yields positive
negative-root magnitudes with geometric separation. The last magnitude lies
below the lower dominance radius at index `J`. -/
theorem exists_outer_geometric_root_family_of_logConcave
    {p : ℝ[X]} {N J : ℕ} {c theta : ℝ}
    (hc : 3 < c) (htheta : 1 < theta)
    (hdegree : p.natDegree = N)
    (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    (hJnext : J + 1 ≤ N) (hJpos : 1 ≤ J)
    (hstrong : ∀ j, 1 ≤ j → j ≤ J →
      c ^ 2 * theta * (p.coeff (j - 1) * p.coeff (j + 1)) ≤
        (p.coeff j) ^ 2) :
    ∃ x : ℕ → ℝ,
      (∀ i, i < J → 0 < x i ∧ p.IsRoot (-(x i))) ∧
      (∀ i, i + 1 < J → theta * x i ≤ x (i + 1)) ∧
      x (J - 1) < c * p.coeff (J - 1) / p.coeff J := by
  classical
  have hc0 : (0 : ℝ) < c := by linarith
  have hsign_lower : ∀ j, 1 ≤ j → j ≤ J →
      0 < (-1 : ℝ) ^ j * p.eval (-(lowerDominanceRadius p c j)) := by
    intro j hj hjJ
    exact lowerDominanceRadius_sign hc htheta hdegree hpos hlog_concave hj
      (by lia) (hstrong j hj hjJ)
  have hsign_upper : ∀ j, 1 ≤ j → j ≤ J →
      0 < (-1 : ℝ) ^ j * p.eval (-(upperDominanceRadius p c j)) := by
    intro j hj hjJ
    exact upperDominanceRadius_sign hc htheta hdegree hpos hlog_concave hj
      (by lia) (hstrong j hj hjJ)
  have hwidth : ∀ j, 1 ≤ j → j ≤ J →
      theta * lowerDominanceRadius p c j ≤ upperDominanceRadius p c j := by
    intro j hj hjJ
    exact dominanceRadii_separated hc0 hpos hj (by lia) (hstrong j hj hjJ)
  have heval1 : 0 < p.eval 1 := eval_one_pos_of_coeff_pos hdegree hpos
  set s0 : ℝ := min (lowerDominanceRadius p c 1 / 2)
    (min 1 (p.coeff 0 / (2 * p.eval 1))) with hs0
  have hradius1 : 0 < lowerDominanceRadius p c 1 :=
    lowerDominanceRadius_pos hc0 hpos (by lia) (by lia)
  have hs0pos : 0 < s0 := by
    rw [hs0]
    refine lt_min (by linarith) (lt_min (by norm_num) ?_)
    exact div_pos (hpos 0 (by lia)) (mul_pos (by norm_num) heval1)
  have hs0le1 : s0 ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hs0lt : s0 < lowerDominanceRadius p c 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs0sign : 0 < p.eval (-s0) := by
    refine sign_near_zero_of_pos_coeffs (by simpa [hdegree] using hpos)
      hs0pos hs0le1 ?_
    have hb : s0 ≤ p.coeff 0 / (2 * p.eval 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hb
    nlinarith
  set lo : ℕ → ℝ := fun i => if i = 0 then s0 else upperDominanceRadius p c i
    with hlo
  have hlosign : ∀ i, i < J →
      0 < (-1 : ℝ) ^ i * p.eval (-(lo i)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa [hlo] using hs0sign
    · have hi_ne : i ≠ 0 := by lia
      have hloi : lo i = upperDominanceRadius p c i := by
        simp only [hlo, if_neg hi_ne]
      rw [hloi]
      exact hsign_upper i hi0 (by lia)
  have hloup : ∀ i, i < J → lo i < lowerDominanceRadius p c (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa [hlo] using hs0lt
    · have hi_ne : i ≠ 0 := by lia
      have hloi : lo i = upperDominanceRadius p c i := by
        simp only [hlo, if_neg hi_ne]
      rw [hloi]
      exact upperDominanceRadius_lt_lowerDominanceRadius_succ
        (by linarith) hpos (by lia)
  obtain ⟨x, hx⟩ := exists_isRoot_neg_family_of_signed_evals (d := 0)
    (by simpa using hlosign)
    (fun i hi => by simpa using hsign_lower (i + 1) (by lia) (by lia)) hloup
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hxi, -, hxroot⟩ := hx i hi
    refine ⟨?_, hxroot⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hlo0 : lo 0 = s0 := by simp [hlo]
      rw [hlo0] at hxi
      linarith
    · have hi_ne : i ≠ 0 := by lia
      have hloi : lo i = upperDominanceRadius p c i := by
        simp only [hlo, if_neg hi_ne]
      rw [hloi] at hxi
      exact lt_trans (upperDominanceRadius_pos hc0 hpos (by lia)) hxi
  · intro i hi
    obtain ⟨-, hxi, -⟩ := hx i (by lia)
    obtain ⟨hxi1, -, -⟩ := hx (i + 1) hi
    have hi1_ne : i + 1 ≠ 0 := by lia
    have hloi1 : lo (i + 1) = upperDominanceRadius p c (i + 1) := by
      simp only [hlo, if_neg hi1_ne]
    rw [hloi1] at hxi1
    have hsep := hwidth (i + 1) (by lia) (by lia)
    nlinarith
  · obtain ⟨-, hxi, -⟩ := hx (J - 1) (by lia)
    have hidx : J - 1 + 1 = J := by lia
    rw [hidx, lowerDominanceRadius] at hxi
    exact hxi

/-- Strong log-concavity on a terminal coefficient range yields positive
negative-root magnitudes with geometric separation. The first magnitude lies
above the upper dominance radius at index `N - J`. -/
theorem exists_top_geometric_root_family_of_logConcave
    {p : ℝ[X]} {N J : ℕ} {c theta : ℝ}
    (hc : 3 < c) (htheta : 1 < theta)
    (hdegree : p.natDegree = N)
    (hpos : ∀ i, i ≤ N → 0 < p.coeff i)
    (hlog_concave : ∀ i, 0 < i → i < N →
      p.coeff (i - 1) * p.coeff (i + 1) ≤ (p.coeff i) ^ 2)
    (hJnext : J + 1 ≤ N) (hJpos : 1 ≤ J)
    (hstrong : ∀ k, N - J ≤ k → k + 1 ≤ N →
      c ^ 2 * theta * (p.coeff (k - 1) * p.coeff (k + 1)) ≤
        (p.coeff k) ^ 2) :
    ∃ x : ℕ → ℝ,
      (∀ i, i < J → 0 < x i ∧ p.IsRoot (-(x i))) ∧
      (∀ i, i + 1 < J → theta * x i ≤ x (i + 1)) ∧
      p.coeff (N - J) / (c * p.coeff (N - J + 1)) < x 0 := by
  classical
  have hc0 : (0 : ℝ) < c := by linarith
  have hsign_lower : ∀ k, N - J ≤ k → 1 ≤ k → k + 1 ≤ N →
      0 < (-1 : ℝ) ^ k * p.eval (-(lowerDominanceRadius p c k)) := by
    intro k hk hj hnext
    exact lowerDominanceRadius_sign hc htheta hdegree hpos hlog_concave hj
      hnext (hstrong k hk hnext)
  have hsign_upper : ∀ k, N - J ≤ k → 1 ≤ k → k + 1 ≤ N →
      0 < (-1 : ℝ) ^ k * p.eval (-(upperDominanceRadius p c k)) := by
    intro k hk hj hnext
    exact upperDominanceRadius_sign hc htheta hdegree hpos hlog_concave hj
      hnext (hstrong k hk hnext)
  have hwidth : ∀ k, N - J ≤ k → 1 ≤ k → k + 1 ≤ N →
      theta * lowerDominanceRadius p c k ≤ upperDominanceRadius p c k := by
    intro k hk hj hnext
    exact dominanceRadii_separated hc0 hpos hj hnext (hstrong k hk hnext)
  have heval1 : 0 < p.eval 1 := eval_one_pos_of_coeff_pos hdegree hpos
  have hcoeffN : 0 < p.coeff N := hpos N le_rfl
  set sinf : ℝ := max (1 + p.eval 1 / p.coeff N)
    (1 + upperDominanceRadius p c (N - 1)) with hsinf
  have hsinf1 : 1 ≤ sinf := by
    refine le_trans ?_ (le_max_left (1 + p.eval 1 / p.coeff N)
      (1 + upperDominanceRadius p c (N - 1)))
    have : 0 < p.eval 1 / p.coeff N := div_pos heval1 hcoeffN
    linarith
  have hsinflt : p.eval 1 < p.coeff N * sinf := by
    have hle : 1 + p.eval 1 / p.coeff N ≤ sinf := le_max_left _ _
    have hid : p.coeff N * (1 + p.eval 1 / p.coeff N) =
        p.coeff N + p.eval 1 := by
      field_simp
    nlinarith
  have hsinf_upper : upperDominanceRadius p c (N - 1) < sinf :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hsign_inf : 0 < (-1 : ℝ) ^ N * p.eval (-sinf) := by
    have hfar := sign_at_far_left_of_eval_one_lt
      (p := p) (by simpa [hdegree] using hpos) (by rw [hdegree]; lia)
      hsinf1 (by simpa [hdegree] using hsinflt)
    simpa [hdegree] using hfar
  set hiend : ℕ → ℝ := fun i =>
    if i + 1 = J then sinf else lowerDominanceRadius p c (N - J + i + 1)
    with hhiend
  have hlosign : ∀ i, i < J →
      0 < (-1 : ℝ) ^ (i + (N - J)) *
        p.eval (-(upperDominanceRadius p c (N - J + i))) := by
    intro i hi
    have hidx : i + (N - J) = N - J + i := by lia
    rw [hidx]
    exact hsign_upper (N - J + i) (by lia) (by lia) (by lia)
  have hhisign : ∀ i, i < J →
      0 < (-1 : ℝ) ^ (i + (N - J) + 1) * p.eval (-(hiend i)) := by
    intro i hi
    by_cases hilast : i + 1 = J
    · have hhi : hiend i = sinf := by simp [hhiend, hilast]
      rw [hhi]
      have hidx : i + (N - J) + 1 = N := by lia
      rw [hidx]
      exact hsign_inf
    · have hhi : hiend i = lowerDominanceRadius p c (N - J + i + 1) := by
        simp [hhiend, hilast]
      rw [hhi]
      have hidx : i + (N - J) + 1 = N - J + i + 1 := by lia
      rw [hidx]
      exact hsign_lower (N - J + i + 1) (by lia) (by lia) (by lia)
  have hloup : ∀ i, i < J →
      upperDominanceRadius p c (N - J + i) < hiend i := by
    intro i hi
    by_cases hilast : i + 1 = J
    · have hhi : hiend i = sinf := by simp [hhiend, hilast]
      rw [hhi]
      have hidx : N - J + i = N - 1 := by lia
      rw [hidx]
      exact hsinf_upper
    · have hhi : hiend i = lowerDominanceRadius p c (N - J + i + 1) := by
        simp [hhiend, hilast]
      rw [hhi]
      exact upperDominanceRadius_lt_lowerDominanceRadius_succ
        (by linarith) hpos (by lia)
  obtain ⟨x, hx⟩ := exists_isRoot_neg_family_of_signed_evals
    (d := N - J) hlosign hhisign hloup
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hxi, -, hxroot⟩ := hx i hi
    exact ⟨lt_trans (upperDominanceRadius_pos hc0 hpos (by lia)) hxi, hxroot⟩
  · intro i hi
    obtain ⟨-, hxi, -⟩ := hx i (by lia)
    obtain ⟨hxi1, -, -⟩ := hx (i + 1) hi
    have hilast : i + 1 ≠ J := by lia
    have hhi : hiend i = lowerDominanceRadius p c (N - J + i + 1) := by
      simp [hhiend, hilast]
    rw [hhi] at hxi
    have hidx : N - J + (i + 1) = N - J + i + 1 := by lia
    rw [hidx] at hxi1
    have hsep := hwidth (N - J + i + 1) (by lia) (by lia) (by lia)
    nlinarith
  · obtain ⟨hxi, -, -⟩ := hx 0 (by lia)
    have hidx : N - J + 0 = N - J := by lia
    rw [hidx, upperDominanceRadius] at hxi
    exact hxi

end

end RealRooted.RootCounting
