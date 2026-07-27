import RealRooted.GeneralizedSnakePosets.SnakeWord

/-!
# Cover graph for generalized snake posets

This module contains the coded two-chain elements and one-step cover graph
used by the Braun--Jal generalized snake poset development.
-/

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Codes and cover edges -/

/-- Code for the `r`-th element of the first chain in the generalized snake
poset.  Rows are indexed from bottom to top. -/
def snakeRowCode (r : ℕ) : ℕ :=
  2 * r

/-- Code for the `c`-th element of the second chain in the generalized snake
poset.  Columns are indexed from left to right. -/
def snakeColCode (c : ℕ) : ℕ :=
  2 * c + 1

/-- Row and column codes have opposite parity. -/
theorem snakeRowCode_ne_colCode (r c : ℕ) :
    snakeRowCode r ≠ snakeColCode c := by
  simp [snakeRowCode, snakeColCode]
  lia

/-- Column and row codes have opposite parity. -/
theorem snakeColCode_ne_rowCode (c r : ℕ) :
    snakeColCode c ≠ snakeRowCode r :=
  (snakeRowCode_ne_colCode r c).symm

/-- Number of coded chain elements in the generalized snake poset for `w`. -/
def snakeCodeBound (w : SnakeWord) : ℕ :=
  2 * (w.length + 1)

/-- Arithmetic core of the constant-suffix reachability calculation in
Braun--Jal Theorem 3.5: a final constant suffix has a cross edge from some
column `d` to a row above it exactly when the starting column is strictly below
the target row. -/
theorem exists_constantSuffixCrossIndex_iff_lt {n c r : ℕ} (hr : r ≤ n) :
    (∃ d, c ≤ d ∧ d < n ∧ d + 1 ≤ r) ↔ c < r := by
  constructor
  · rintro ⟨d, hcd, _hd, hdr⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hcd) hdr
  · intro hcr
    refine ⟨c, le_rfl, ?_, Nat.succ_le_iff.mpr hcr⟩
    exact Nat.lt_of_lt_of_le hcr hr

/-- The cross-chain cover edges of Braun--Jal's generalized snake poset.

If the letter at gap `g` is `L`, the cover is `row (g - 1) < col g`;
if it is `R`, the cover is `col (g - 1) < row g`. -/
def snakeCrossCoverEdge (w : SnakeWord) (a b : ℕ) : Bool :=
  (List.range w.length).any fun idx =>
    let gap := w.length - (idx + 1)
    match w.getD idx SnakeLetter.L with
    | SnakeLetter.L => a == snakeRowCode gap && b == snakeColCode (gap + 1)
    | SnakeLetter.R => a == snakeColCode gap && b == snakeRowCode (gap + 1)

/-- Cross-chain covers in an all-`R` snake word are exactly the edges
`col d < row (d + 1)` for `d < n`. -/
theorem snakeCrossCoverEdge_replicate_R {n a b : ℕ} :
    snakeCrossCoverEdge (List.replicate n SnakeLetter.R) a b = true ↔
      ∃ d, d < n ∧ a = snakeColCode d ∧ b = snakeRowCode (d + 1) := by
  rw [snakeCrossCoverEdge]
  simp only [List.length_replicate, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨idx, hidx, hbool⟩
    have hget : (List.replicate n SnakeLetter.R)[idx]?.getD SnakeLetter.L =
        SnakeLetter.R := by
      simp [hidx]
    simp only [List.getD_eq_getElem?_getD, hget, Bool.and_eq_true,
      beq_iff_eq] at hbool
    rcases hbool with ⟨ha, hb⟩
    exact ⟨n - (idx + 1), by lia, ha, hb⟩
  · rintro ⟨d, hd, ha, hb⟩
    let idx := n - 1 - d
    have hidx : idx < n := by
      dsimp [idx]
      lia
    have hgap : n - (idx + 1) = d := by
      dsimp [idx]
      lia
    have hget : (List.replicate n SnakeLetter.R)[idx]?.getD SnakeLetter.L =
        SnakeLetter.R := by
      simp [hidx]
    exact ⟨idx, hidx, by
      simp only [List.getD_eq_getElem?_getD, hget, ha, hgap, BEq.rfl, hb,
        Bool.and_self]⟩

/-- Cross-chain covers in an all-`L` snake word are exactly the edges
`row d < col (d + 1)` for `d < n`. -/
theorem snakeCrossCoverEdge_replicate_L {n a b : ℕ} :
    snakeCrossCoverEdge (List.replicate n SnakeLetter.L) a b = true ↔
      ∃ d, d < n ∧ a = snakeRowCode d ∧ b = snakeColCode (d + 1) := by
  rw [snakeCrossCoverEdge]
  simp only [List.length_replicate, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨idx, hidx, hbool⟩
    have hget : (List.replicate n SnakeLetter.L)[idx]?.getD SnakeLetter.L =
        SnakeLetter.L := by
      simp [hidx]
    simp only [List.getD_eq_getElem?_getD, hget, Bool.and_eq_true,
      beq_iff_eq] at hbool
    rcases hbool with ⟨ha, hb⟩
    exact ⟨n - (idx + 1), by lia, ha, hb⟩
  · rintro ⟨d, hd, ha, hb⟩
    let idx := n - 1 - d
    have hidx : idx < n := by
      dsimp [idx]
      lia
    have hgap : n - (idx + 1) = d := by
      dsimp [idx]
      lia
    have hget : (List.replicate n SnakeLetter.L)[idx]?.getD SnakeLetter.L =
        SnakeLetter.L := by
      simp [hidx]
    exact ⟨idx, hidx, by
      simp only [List.getD_eq_getElem?_getD, hget, ha, hgap, BEq.rfl, hb,
        Bool.and_self]⟩

/-- Arithmetic for the reverse enumeration of final-suffix cover gaps. -/
theorem snakeSuffixCoverIndex_spec {n k d : ℕ}
    (hd : d < n - (k + 1)) :
    let idx := n - 1 - d
    idx < n ∧ n - (idx + 1) = d ∧ k < idx := by
  dsimp
  lia

/-- If the final constant suffix after a last-change index consists of `R`
letters, then every suffix gap contributes the corresponding cross cover. -/
theorem snakeCrossCoverEdge_suffix_R_of_isLastChangeIndex
    {w : SnakeWord} {k d : ℕ} (hlast : w.IsLastChangeIndex k)
    (hd : d < w.length - (k + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    snakeCrossCoverEdge w (snakeColCode d) (snakeRowCode (d + 1)) = true := by
  rw [snakeCrossCoverEdge]
  simp only [List.any_eq_true, List.mem_range]
  let idx := w.length - 1 - d
  have hspec := snakeSuffixCoverIndex_spec (n := w.length) (k := k) (d := d) hd
  have hidx_lt : idx < w.length := hspec.1
  have hgap : w.length - (idx + 1) = d := hspec.2.1
  have hkidx : k < idx := hspec.2.2
  have hletter : w.getD idx SnakeLetter.L = SnakeLetter.R := by
    rw [hlast.getD_eq_final_of_lt hkidx hidx_lt, hfinal]
  have hletter? : w[idx]?.getD SnakeLetter.L = SnakeLetter.R := by
    simpa [List.getD_eq_getElem?_getD] using hletter
  refine ⟨idx, hidx_lt, ?_⟩
  simp [hletter?, hgap]

/-- If the final constant suffix after a last-change index consists of `L`
letters, then every suffix gap contributes the corresponding cross cover. -/
theorem snakeCrossCoverEdge_suffix_L_of_isLastChangeIndex
    {w : SnakeWord} {k d : ℕ} (hlast : w.IsLastChangeIndex k)
    (hd : d < w.length - (k + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    snakeCrossCoverEdge w (snakeRowCode d) (snakeColCode (d + 1)) = true := by
  rw [snakeCrossCoverEdge]
  simp only [List.any_eq_true, List.mem_range]
  let idx := w.length - 1 - d
  have hspec := snakeSuffixCoverIndex_spec (n := w.length) (k := k) (d := d) hd
  have hidx_lt : idx < w.length := hspec.1
  have hgap : w.length - (idx + 1) = d := hspec.2.1
  have hkidx : k < idx := hspec.2.2
  have hletter : w.getD idx SnakeLetter.L = SnakeLetter.L := by
    rw [hlast.getD_eq_final_of_lt hkidx hidx_lt, hfinal]
  have hletter? : w[idx]?.getD SnakeLetter.L = SnakeLetter.L := by
    simpa [List.getD_eq_getElem?_getD] using hletter
  refine ⟨idx, hidx_lt, ?_⟩
  simp [hletter?, hgap]

/-- One cover edge of the generalized snake poset: either a chain edge or one
of Braun--Jal's cross-chain covers. -/
def snakeCoverEdge (w : SnakeWord) (a b : ℕ) : Bool :=
  (a + 2 == b && b < snakeCodeBound w) || snakeCrossCoverEdge w a b

/-- Every cover edge strictly increases the numeric code. -/
theorem snakeCoverEdge_lt {w : SnakeWord} {a b : ℕ}
    (hcover : snakeCoverEdge w a b = true) :
    a < b := by
  rw [snakeCoverEdge] at hcover
  rw [Bool.or_eq_true] at hcover
  rcases hcover with hchain | hcross
  · rw [Bool.and_eq_true] at hchain
    rcases hchain with ⟨hnext, _hbound⟩
    rw [beq_iff_eq] at hnext
    lia
  · rw [snakeCrossCoverEdge] at hcross
    simp only [List.any_eq_true, List.mem_range] at hcross
    rcases hcross with ⟨idx, _hidx, hbool⟩
    split at hbool
    · simp only [Bool.and_eq_true, beq_iff_eq] at hbool
      rcases hbool with ⟨rfl, rfl⟩
      simp [snakeRowCode, snakeColCode]
    · simp only [Bool.and_eq_true, beq_iff_eq] at hbool
      rcases hbool with ⟨rfl, rfl⟩
      simp [snakeRowCode, snakeColCode]
      lia

/-- Covers in an all-`R` snake word are same-chain successor covers or the
constant-`R` cross-chain covers. -/
theorem snakeCoverEdge_replicate_R {n a b : ℕ} :
    snakeCoverEdge (List.replicate n SnakeLetter.R) a b = true ↔
      (a + 2 = b ∧ b < 2 * (n + 1)) ∨
        ∃ d, d < n ∧ a = snakeColCode d ∧ b = snakeRowCode (d + 1) := by
  simp [snakeCoverEdge, snakeCodeBound, snakeCrossCoverEdge_replicate_R]

/-- Covers in an all-`L` snake word are same-chain successor covers or the
constant-`L` cross-chain covers. -/
theorem snakeCoverEdge_replicate_L {n a b : ℕ} :
    snakeCoverEdge (List.replicate n SnakeLetter.L) a b = true ↔
      (a + 2 = b ∧ b < 2 * (n + 1)) ∨
        ∃ d, d < n ∧ a = snakeRowCode d ∧ b = snakeColCode (d + 1) := by
  simp [snakeCoverEdge, snakeCodeBound, snakeCrossCoverEdge_replicate_L]

/-- Consecutive row elements are connected by a chain cover. -/
theorem snakeCoverEdge_rowCode_succ {w : SnakeWord} {r : ℕ}
    (hr : r < w.length) :
    snakeCoverEdge w (snakeRowCode r) (snakeRowCode (r + 1)) = true := by
  simp [snakeCoverEdge, snakeRowCode, snakeCodeBound]
  lia

/-- Consecutive column elements are connected by a chain cover. -/
theorem snakeCoverEdge_colCode_succ {w : SnakeWord} {c : ℕ}
    (hc : c < w.length) :
    snakeCoverEdge w (snakeColCode c) (snakeColCode (c + 1)) = true := by
  simp [snakeCoverEdge, snakeColCode, snakeCodeBound]
  lia

/-- In an all-`R` snake word, each column `c < n` covers row `c + 1`. -/
theorem snakeCoverEdge_replicate_R_colCode_rowCode_succ {n c : ℕ}
    (hc : c < n) :
    snakeCoverEdge (List.replicate n SnakeLetter.R) (snakeColCode c)
      (snakeRowCode (c + 1)) = true := by
  rw [snakeCoverEdge_replicate_R]
  right
  exact ⟨c, hc, rfl, rfl⟩

/-- In an all-`L` snake word, each row `r < n` covers column `r + 1`. -/
theorem snakeCoverEdge_replicate_L_rowCode_colCode_succ {n r : ℕ}
    (hr : r < n) :
    snakeCoverEdge (List.replicate n SnakeLetter.L) (snakeRowCode r)
      (snakeColCode (r + 1)) = true := by
  rw [snakeCoverEdge_replicate_L]
  right
  exact ⟨r, hr, rfl, rfl⟩

end GeneralizedSnakePosets
end RealRooted
