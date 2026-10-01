import RealRooted.GeneralizedSnakePosets.ChainPolynomial
import RealRooted.GeneralizedSnakePosets.SnakeBoard

/-!
# Snake boards as monochromatic bands

Index the gaps of a snake word `w` of length `n` from the bottom, so that gap
`g` carries the letter `w[n - 1 - g]`.  Row `i` lies below column `j` exactly
when some gap `g` with `i ≤ g < j` carries `L`.  Column `j` lies below row `i`
exactly when some gap `g` with `j ≤ g < i` carries `R`.

So `(i, j)` is an incomparable cross pair exactly when the gaps between `i` and
`j` are all `R` (if `i < j`) or all `L` (if `j < i`).  These are the band cells
`bandCells n (gapLetter w)`.  After reversing the column order, non-nesting
placements become chains that increase in both coordinates, so the snake
polynomial is the `incRel` chain polynomial of the band.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The letter at gap `g`, counted from the bottom of the two chains. -/
def gapLetter (w : SnakeWord) (g : ℕ) : SnakeLetter :=
  w.getD (w.length - (g + 1)) SnakeLetter.L

theorem snakeCrossCoverEdge_iff {w : SnakeWord} {a b : ℕ} :
    snakeCrossCoverEdge w a b = true ↔
      ∃ g < w.length,
        (gapLetter w g = .L ∧ a = snakeRowCode g ∧ b = snakeColCode (g + 1)) ∨
          (gapLetter w g = .R ∧ a = snakeColCode g ∧ b = snakeRowCode (g + 1)) := by
  rw [snakeCrossCoverEdge]
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨idx, hidx, h⟩
    refine ⟨w.length - (idx + 1), by lia, ?_⟩
    have hg : gapLetter w (w.length - (idx + 1)) = w.getD idx SnakeLetter.L := by
      rw [gapLetter, show w.length - (w.length - (idx + 1) + 1) = idx by lia]
    rw [hg]
    cases hl : w.getD idx SnakeLetter.L <;> simp_all
  · rintro ⟨g, hg, h⟩
    refine ⟨w.length - (g + 1), by lia, ?_⟩
    have hgap : w.length - (w.length - (g + 1) + 1) = g := by lia
    rw [hgap]
    rcases h with ⟨hl, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩ <;>
      rw [gapLetter, List.getD_eq_getElem?_getD] at hl <;> simp [hl]

/-- The semantic order on codes: same chain and weakly increasing, or a cross
pair separated by a gap with the right letter. -/
def SnakeReachSpec (w : SnakeWord) (a b : ℕ) : Prop :=
  (a % 2 = b % 2 ∧ a ≤ b) ∨
    (a % 2 = 0 ∧ b % 2 = 1 ∧ ∃ g, a / 2 ≤ g ∧ g < b / 2 ∧ gapLetter w g = .L) ∨
      (a % 2 = 1 ∧ b % 2 = 0 ∧ ∃ g, a / 2 ≤ g ∧ g < b / 2 ∧ gapLetter w g = .R)

theorem snakeReachSpec_of_coverEdge {w : SnakeWord} {a c b : ℕ}
    (hcover : snakeCoverEdge w a c = true) (h : SnakeReachSpec w c b) :
    SnakeReachSpec w a b := by
  rw [snakeCoverEdge, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    snakeCrossCoverEdge_iff] at hcover
  simp only [SnakeReachSpec, snakeRowCode, snakeColCode] at h hcover ⊢
  rcases hcover with ⟨rfl, -⟩ | ⟨g, -, ⟨hl, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2, g, hg1, hg2, hl⟩ | ⟨h1, h2, g, hg1, hg2, hl⟩
    · exact Or.inl ⟨by lia, by lia⟩
    · exact Or.inr (Or.inl ⟨by lia, h2, g, by lia, hg2, hl⟩)
    · exact Or.inr (Or.inr ⟨by lia, h2, g, by lia, hg2, hl⟩)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩ | ⟨-, h2, g', hg1, hg2, -⟩
    · exact Or.inr (Or.inl ⟨by lia, by lia, g, by lia, by lia, hl⟩)
    · lia
    · exact Or.inl ⟨by lia, by lia⟩
  · rcases h with ⟨h1, h2⟩ | ⟨-, h2, g', hg1, hg2, -⟩ | ⟨h1, -⟩
    · exact Or.inr (Or.inr ⟨by lia, by lia, g, by lia, by lia, hl⟩)
    · exact Or.inl ⟨by lia, by lia⟩
    · lia

theorem snakeReachSpec_of_reachableFuel {w : SnakeWord} {fuel a b : ℕ}
    (h : snakeReachableFuel w fuel a b = true) : SnakeReachSpec w a b := by
  induction fuel generalizing a with
  | zero =>
      simp only [snakeReachableFuel, beq_iff_eq] at h
      exact Or.inl ⟨by rw [h], h.le⟩
  | succ fuel ih =>
      simp only [snakeReachableFuel, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        List.mem_range, Bool.and_eq_true] at h
      rcases h with rfl | ⟨c, -, hcover, hc⟩
      · exact Or.inl ⟨rfl, le_rfl⟩
      · exact snakeReachSpec_of_coverEdge hcover (ih hc)

theorem snakeReachableFuel_trans {w : SnakeWord} {f₁ f₂ a c b : ℕ}
    (h₁ : snakeReachableFuel w f₁ a c = true) (h₂ : snakeReachableFuel w f₂ c b = true) :
    snakeReachableFuel w (f₁ + f₂) a b = true := by
  induction f₁ generalizing a with
  | zero =>
      simp only [snakeReachableFuel, beq_iff_eq] at h₁
      subst h₁
      exact snakeReachableFuel_of_le (by lia) h₂
  | succ f ih =>
      simp only [snakeReachableFuel, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        List.mem_range, Bool.and_eq_true] at h₁
      rcases h₁ with rfl | ⟨d, hd, hcover, hdc⟩
      · exact snakeReachableFuel_of_le (by lia) h₂
      · rw [show f + 1 + f₂ = f + f₂ + 1 by lia]
        exact snakeReachableFuel_succ_of_coverEdge_of_reachable hd hcover (ih hdc)

theorem snakeElementReachable_rowCode_colCode_of_gap {w : SnakeWord} {i j g : ℕ}
    (hig : i ≤ g) (hgj : g < j) (hj : j ≤ w.length) (hl : gapLetter w g = .L) :
    snakeElementReachable w (snakeRowCode i) (snakeColCode j) = true := by
  have h₁ := snakeReachableFuel_rowCode_add w (r := i) (k := g - i) (by lia)
  have hcross : snakeReachableFuel w 1 (snakeRowCode g) (snakeColCode (g + 1)) = true := by
    refine snakeReachableFuel_succ_of_coverEdge (by simp [snakeColCode, snakeCodeBound]; lia) ?_
    rw [snakeCoverEdge, Bool.or_eq_true]
    exact Or.inr (snakeCrossCoverEdge_iff.mpr ⟨g, by lia, Or.inl ⟨hl, rfl, rfl⟩⟩)
  have h₃ := snakeReachableFuel_colCode_add w (c := g + 1) (k := j - (g + 1)) (by lia)
  rw [show i + (g - i) = g by lia] at h₁
  rw [show g + 1 + (j - (g + 1)) = j by lia] at h₃
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia)
    (snakeReachableFuel_trans (snakeReachableFuel_trans h₁ hcross) h₃)

theorem snakeElementReachable_colCode_rowCode_of_gap {w : SnakeWord} {i j g : ℕ}
    (hjg : j ≤ g) (hgi : g < i) (hi : i ≤ w.length) (hl : gapLetter w g = .R) :
    snakeElementReachable w (snakeColCode j) (snakeRowCode i) = true := by
  have h₁ := snakeReachableFuel_colCode_add w (c := j) (k := g - j) (by lia)
  have hcross : snakeReachableFuel w 1 (snakeColCode g) (snakeRowCode (g + 1)) = true := by
    refine snakeReachableFuel_succ_of_coverEdge (by simp [snakeRowCode, snakeCodeBound]; lia) ?_
    rw [snakeCoverEdge, Bool.or_eq_true]
    exact Or.inr (snakeCrossCoverEdge_iff.mpr ⟨g, by lia, Or.inr ⟨hl, rfl, rfl⟩⟩)
  have h₃ := snakeReachableFuel_rowCode_add w (r := g + 1) (k := i - (g + 1)) (by lia)
  rw [show j + (g - j) = g by lia] at h₁
  rw [show g + 1 + (i - (g + 1)) = i by lia] at h₃
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia)
    (snakeReachableFuel_trans (snakeReachableFuel_trans h₁ hcross) h₃)

private theorem eq_R_of_ne_L {a : SnakeLetter} (h : a ≠ .L) : a = .R := by
  cases a <;> simp_all

private theorem eq_L_of_ne_R {a : SnakeLetter} (h : a ≠ .R) : a = .L := by
  cases a <;> simp_all

/-- Row `i` and column `j` are incomparable exactly when the gaps between them
all carry `R` (if `i < j`) or all carry `L` (if `j < i`). -/
theorem mem_snakeIncomparableBoard_cells_iff {w : SnakeWord} {i j : ℕ} :
    (i, j) ∈ (snakeIncomparableBoard w).cells ↔
      i ≤ w.length ∧ j ≤ w.length ∧ (∀ g, i ≤ g → g < j → gapLetter w g = .R) ∧
        (∀ g, j ≤ g → g < i → gapLetter w g = .L) := by
  rw [snakeIncomparableBoard, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_range, Finset.mem_range, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  constructor
  · rintro ⟨⟨hi, hj⟩, hrc, hcr⟩
    refine ⟨by lia, by lia, fun g hig hgj => eq_R_of_ne_L fun hl => ?_,
      fun g hjg hgi => eq_L_of_ne_R fun hl => ?_⟩
    · rw [snakeElementReachable_rowCode_colCode_of_gap hig hgj (by lia) hl] at hrc
      cases hrc
    · rw [snakeElementReachable_colCode_rowCode_of_gap hjg hgi (by lia) hl] at hcr
      cases hcr
  · rintro ⟨hi, hj, hR, hL⟩
    refine ⟨⟨by lia, by lia⟩, Bool.eq_false_iff.mpr fun h => ?_,
      Bool.eq_false_iff.mpr fun h => ?_⟩
    · have hs := snakeReachSpec_of_reachableFuel h
      simp only [SnakeReachSpec, snakeRowCode, snakeColCode] at hs
      rcases hs with ⟨h1, -⟩ | ⟨-, -, g, hg1, hg2, hl⟩ | ⟨h1, -⟩
      · lia
      · rw [hR g (by lia) (by lia)] at hl
        cases hl
      · lia
    · have hs := snakeReachSpec_of_reachableFuel h
      simp only [SnakeReachSpec, snakeRowCode, snakeColCode] at hs
      rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, g, hg1, hg2, hl⟩
      · lia
      · lia
      · rw [hL g (by lia) (by lia)] at hl
        cases hl

/-! ## Band cells -/

/-- The cells `(i, j)` of `[0, n]²` whose gaps all carry `R` (when `i < j`) or
all carry `L` (when `j < i`), for a letter function `ℓ` on the gaps. -/
def bandCells (n : ℕ) (ℓ : ℕ → SnakeLetter) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun p =>
    (∀ g, p.1 ≤ g → g < p.2 → ℓ g = .R) ∧ (∀ g, p.2 ≤ g → g < p.1 → ℓ g = .L)

@[simp] theorem mem_bandCells {n : ℕ} {ℓ : ℕ → SnakeLetter} {i j : ℕ} :
    (i, j) ∈ bandCells n ℓ ↔
      i ≤ n ∧ j ≤ n ∧ (∀ g, i ≤ g → g < j → ℓ g = .R) ∧ (∀ g, j ≤ g → g < i → ℓ g = .L) := by
  classical
  unfold bandCells
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨⟨hi, hj⟩, h⟩
    exact ⟨by lia, by lia, h⟩
  · rintro ⟨hi, hj, h⟩
    exact ⟨⟨by lia, by lia⟩, h⟩

theorem bandCells_congr {n : ℕ} {ℓ ℓ' : ℕ → SnakeLetter} (h : ∀ g < n, ℓ g = ℓ' g) :
    bandCells n ℓ = bandCells n ℓ' := by
  ext ⟨i, j⟩
  simp only [mem_bandCells]
  constructor
  · rintro ⟨hi, hj, hR, hL⟩
    exact ⟨hi, hj, fun g h1 h2 => (h g (by lia)).symm.trans (hR g h1 h2),
      fun g h1 h2 => (h g (by lia)).symm.trans (hL g h1 h2)⟩
  · rintro ⟨hi, hj, hR, hL⟩
    exact ⟨hi, hj, fun g h1 h2 => (h g (by lia)).trans (hR g h1 h2),
      fun g h1 h2 => (h g (by lia)).trans (hL g h1 h2)⟩

theorem snakeIncomparableBoard_cells_eq_bandCells (w : SnakeWord) :
    (snakeIncomparableBoard w).cells = bandCells w.length (gapLetter w) := by
  ext ⟨i, j⟩
  rw [mem_snakeIncomparableBoard_cells_iff, mem_bandCells]

/-- **The snake polynomial is the increasing-chain polynomial of the band.** -/
theorem generalizedSnakeRookModel_snakePolynomial_eq_chainPolynomial (w : SnakeWord) :
    generalizedSnakeRookModel.snakePolynomial w =
      chainPolynomial incRel (bandCells w.length (gapLetter w)) := by
  rw [generalizedSnakeRookModel_snakePolynomial,
    FiniteSkewBoard.rookPolynomial_eq_chainPolynomial_reflect (N := w.length),
    generalizedSnakeBoard, Finset.image_image, ← snakeIncomparableBoard_cells_eq_bandCells]
  · congr 1
    refine (Finset.image_congr fun p hp => ?_).trans Finset.image_id
    have := (mem_snakeIncomparableBoard_cells_le (w := w) (r := p.1) (c := p.2) hp).2
    simp only [Function.comp_apply, id_eq]
    ext
    · rfl
    · change w.length - (w.length - p.2) = p.2
      lia
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.sub_le _ _

/-- Shifting a band: the band of the letters above gap `s` is the part of the
band in `[s, n]²`. -/
theorem image_bandCells_shift {n s : ℕ} (ℓ : ℕ → SnakeLetter) :
    (bandCells n fun g => ℓ (g + s)).image (fun p => (p.1 + s, p.2 + s)) =
      (bandCells (n + s) ℓ).filter fun p => s ≤ p.1 ∧ s ≤ p.2 := by
  ext ⟨i, j⟩
  simp only [Finset.mem_image, Finset.mem_filter, mem_bandCells, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hR, hL⟩, rfl, rfl⟩
    refine ⟨⟨by lia, by lia, fun g h1 h2 => ?_, fun g h1 h2 => ?_⟩, by lia, by lia⟩
    · simpa [show g - s + s = g by lia] using hR (g - s) (by lia) (by lia)
    · simpa [show g - s + s = g by lia] using hL (g - s) (by lia) (by lia)
  · rintro ⟨⟨hi, hj, hR, hL⟩, hsi, hsj⟩
    exact ⟨i - s, j - s, ⟨by lia, by lia, fun g h1 h2 => hR _ (by lia) (by lia),
      fun g h1 h2 => hL _ (by lia) (by lia)⟩, by lia, by lia⟩

/-- Translation does not change increasing-chain polynomials. -/
theorem chainPolynomial_incRel_image_shift (D : Finset (ℕ × ℕ)) (s : ℕ) :
    chainPolynomial incRel (D.image fun p => (p.1 + s, p.2 + s)) = chainPolynomial incRel D := by
  refine chainPolynomial_image ?_ fun a _ b _ => ?_
  · rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simp only [Prod.mk.injEq] at h ⊢
    lia
  · simp only [incRel]
    lia

/-- The letter swap `L ↔ R`. -/
def SnakeLetter.flip : SnakeLetter → SnakeLetter
  | .L => .R
  | .R => .L

@[simp] theorem SnakeLetter.flip_eq_R {a : SnakeLetter} : a.flip = .R ↔ a = .L := by
  cases a <;> simp [SnakeLetter.flip]

@[simp] theorem SnakeLetter.flip_eq_L {a : SnakeLetter} : a.flip = .L ↔ a = .R := by
  cases a <;> simp [SnakeLetter.flip]

/-- Swapping the letters transposes the band, which preserves increasing
chains. -/
theorem chainPolynomial_bandCells_flip (n : ℕ) (ℓ : ℕ → SnakeLetter) :
    chainPolynomial incRel (bandCells n fun g => (ℓ g).flip) =
      chainPolynomial incRel (bandCells n ℓ) := by
  have himage : (bandCells n ℓ).image Prod.swap = bandCells n fun g => (ℓ g).flip := by
    ext ⟨i, j⟩
    simp only [Finset.mem_image, mem_bandCells, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq,
      SnakeLetter.flip_eq_R, SnakeLetter.flip_eq_L]
    constructor
    · rintro ⟨a, b, ⟨ha, hb, hR, hL⟩, rfl, rfl⟩
      exact ⟨hb, ha, hL, hR⟩
    · rintro ⟨hi, hj, hR, hL⟩
      exact ⟨j, i, ⟨hj, hi, hL, hR⟩, rfl, rfl⟩
  rw [← himage]
  refine chainPolynomial_image (Prod.swap_injective.injOn) fun a _ b _ => ?_
  simp only [incRel, Prod.fst_swap, Prod.snd_swap]
  tauto

end GeneralizedSnakePosets
end RealRooted
