import RealRooted.GeneralizedSnakePosets.SnakeCover

/-!
# Reachability for generalized snake posets

This module contains bounded reachability in the directed cover graph of a
Braun--Jal generalized snake poset, together with the all-`R` and all-`L`
constant-word reachability criteria used by the concrete board model.
-/

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Bounded reachability -/

/-- Bounded reachability in the directed cover graph of the generalized snake
poset.  The fuel `snakeCodeBound w` is enough for the finite acyclic graph and
keeps the board assignment executable. -/
def snakeReachableFuel (w : SnakeWord) : ℕ → ℕ → ℕ → Bool
  | 0, a, b => a == b
  | fuel + 1, a, b =>
      (a == b) ||
        (List.range (snakeCodeBound w)).any fun c =>
          snakeCoverEdge w a c && snakeReachableFuel w fuel c b

/-- Bounded reachability is reflexive for every amount of fuel. -/
@[simp] theorem snakeReachableFuel_self (w : SnakeWord) (fuel a : ℕ) :
    snakeReachableFuel w fuel a a = true := by
  cases fuel <;> simp [snakeReachableFuel]

/-- Reachability in the cover graph weakly increases the numeric code. -/
theorem snakeReachableFuel_le {w : SnakeWord} {fuel a b : ℕ}
    (hreach : snakeReachableFuel w fuel a b = true) :
    a ≤ b := by
  induction fuel generalizing a with
  | zero =>
      simp only [snakeReachableFuel, beq_iff_eq] at hreach
      subst b
      exact le_rfl
  | succ fuel ih =>
      change ((a == b) ||
        (List.range (snakeCodeBound w)).any fun c =>
          snakeCoverEdge w a c && snakeReachableFuel w fuel c b) = true at hreach
      rw [Bool.or_eq_true] at hreach
      rcases hreach with hab | hstep
      · rw [beq_iff_eq] at hab
        subst b
        exact le_rfl
      · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hstep
        rcases hstep with ⟨c, _hc, hcover, htail⟩
        exact le_trans (Nat.le_of_lt (snakeCoverEdge_lt hcover)) (ih htail)

/-- If the target code is smaller than the source code, no fuel can reach it. -/
theorem snakeReachableFuel_eq_false_of_target_lt {w : SnakeWord}
    {fuel a b : ℕ} (hba : b < a) :
    snakeReachableFuel w fuel a b = false := by
  exact Bool.eq_false_of_not_eq_true fun hreach =>
    (not_lt_of_ge (snakeReachableFuel_le hreach)) hba

/-- Prepend one cover edge to an already reachable path. -/
theorem snakeReachableFuel_succ_of_coverEdge_of_reachable {w : SnakeWord}
    {fuel a b c : ℕ} (hc : c < snakeCodeBound w)
    (hcover : snakeCoverEdge w a c = true)
    (hreach : snakeReachableFuel w fuel c b = true) :
    snakeReachableFuel w (fuel + 1) a b = true := by
  simp only [snakeReachableFuel]
  by_cases hab : a = b
  · simp [hab]
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
      Bool.and_eq_true]
    exact Or.inr ⟨c, hc, hcover, hreach⟩

/-- A single cover edge is reachable with any positive amount of fuel. -/
theorem snakeReachableFuel_succ_of_coverEdge {w : SnakeWord} {fuel a b : ℕ}
    (hb : b < snakeCodeBound w) (hcover : snakeCoverEdge w a b = true) :
    snakeReachableFuel w (fuel + 1) a b = true :=
  snakeReachableFuel_succ_of_coverEdge_of_reachable hb hcover
    (snakeReachableFuel_self w fuel b)

/-- Repeated column-chain successor covers give reachability with the exact
number of steps as fuel. -/
theorem snakeReachableFuel_colCode_add (w : SnakeWord) :
    ∀ {c k : ℕ}, c + k ≤ w.length →
      snakeReachableFuel w k (snakeColCode c) (snakeColCode (c + k)) = true := by
  intro c k
  induction k generalizing c with
  | zero =>
      intro hck
      simp
  | succ k ih =>
      intro hck
      have hc : c < w.length := by
        lia
      have hnext_bound : snakeColCode (c + 1) < snakeCodeBound w := by
        simp [snakeColCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_colCode_succ (w := w) (c := c) hc
      have htail : c + 1 + k ≤ w.length := by
        lia
      have hreach := ih (c := c + 1) htail
      have hend : c + (k + 1) = c + 1 + k := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- Repeated row-chain successor covers give reachability with the exact number
of steps as fuel. -/
theorem snakeReachableFuel_rowCode_add (w : SnakeWord) :
    ∀ {r k : ℕ}, r + k ≤ w.length →
      snakeReachableFuel w k (snakeRowCode r) (snakeRowCode (r + k)) = true := by
  intro r k
  induction k generalizing r with
  | zero =>
      intro hrk
      simp
  | succ k ih =>
      intro hrk
      have hr : r < w.length := by
        lia
      have hnext_bound : snakeRowCode (r + 1) < snakeCodeBound w := by
        simp [snakeRowCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_rowCode_succ (w := w) (r := r) hr
      have htail : r + 1 + k ≤ w.length := by
        lia
      have hreach := ih (r := r + 1) htail
      have hend : r + (k + 1) = r + 1 + k := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- In an all-`R` snake word, walking `k` column steps and then taking the
cross edge reaches row `c + k + 1`. -/
theorem snakeReachableFuel_replicate_R_colCode_rowCode_succ_add {n c k : ℕ}
    (hck : c + k < n) :
    snakeReachableFuel (List.replicate n SnakeLetter.R) (k + 1)
      (snakeColCode c) (snakeRowCode (c + k + 1)) = true := by
  induction k generalizing c with
  | zero =>
      have hrow_bound :
          snakeRowCode (c + 1) < snakeCodeBound (List.replicate n SnakeLetter.R) := by
        simp [snakeRowCode, snakeCodeBound]
        lia
      exact snakeReachableFuel_succ_of_coverEdge hrow_bound
        (snakeCoverEdge_replicate_R_colCode_rowCode_succ hck)
  | succ k ih =>
      have hc : c < n := by
        lia
      have hnext_bound :
          snakeColCode (c + 1) < snakeCodeBound (List.replicate n SnakeLetter.R) := by
        simp [snakeColCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_colCode_succ (w := List.replicate n SnakeLetter.R)
        (c := c) (by simpa using hc)
      have htail : c + 1 + k < n := by
        lia
      have hreach := ih (c := c + 1) htail
      have hend : c + (k + 1) + 1 = c + 1 + k + 1 := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- In an all-`L` snake word, walking `k` row steps and then taking the cross
edge reaches column `r + k + 1`. -/
theorem snakeReachableFuel_replicate_L_rowCode_colCode_succ_add {n r k : ℕ}
    (hrk : r + k < n) :
    snakeReachableFuel (List.replicate n SnakeLetter.L) (k + 1)
      (snakeRowCode r) (snakeColCode (r + k + 1)) = true := by
  induction k generalizing r with
  | zero =>
      have hcol_bound :
          snakeColCode (r + 1) < snakeCodeBound (List.replicate n SnakeLetter.L) := by
        simp [snakeColCode, snakeCodeBound]
        lia
      exact snakeReachableFuel_succ_of_coverEdge hcol_bound
        (snakeCoverEdge_replicate_L_rowCode_colCode_succ hrk)
  | succ k ih =>
      have hr : r < n := by
        lia
      have hnext_bound :
          snakeRowCode (r + 1) < snakeCodeBound (List.replicate n SnakeLetter.L) := by
        simp [snakeRowCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_rowCode_succ (w := List.replicate n SnakeLetter.L)
        (r := r) (by simpa using hr)
      have htail : r + 1 + k < n := by
        lia
      have hreach := ih (r := r + 1) htail
      have hend : r + (k + 1) + 1 = r + 1 + k + 1 := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- In a final `R` suffix after a last-change index, walking `steps` column
steps and then taking the suffix cross edge reaches row `c + steps + 1`. -/
theorem snakeReachableFuel_suffix_R_colCode_rowCode_succ_add
    {w : SnakeWord} {last c steps : ℕ} (hlast : w.IsLastChangeIndex last)
    (hcs : c + steps < w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    snakeReachableFuel w (steps + 1)
      (snakeColCode c) (snakeRowCode (c + steps + 1)) = true := by
  induction steps generalizing c with
  | zero =>
      have hrow_bound : snakeRowCode (c + 1) < snakeCodeBound w := by
        simp [snakeRowCode, snakeCodeBound]
        lia
      have hcross := snakeCrossCoverEdge_suffix_R_of_isLastChangeIndex
        (w := w) (k := last) (d := c) hlast (by simpa using hcs) hfinal
      have hcover :
          snakeCoverEdge w (snakeColCode c) (snakeRowCode (c + 1)) = true := by
        rw [snakeCoverEdge]
        simp [hcross]
      exact snakeReachableFuel_succ_of_coverEdge hrow_bound hcover
  | succ steps ih =>
      have hc : c < w.length := by
        lia
      have hnext_bound : snakeColCode (c + 1) < snakeCodeBound w := by
        simp [snakeColCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_colCode_succ (w := w) (c := c) hc
      have htail : c + 1 + steps < w.length - (last + 1) := by
        lia
      have hreach := ih (c := c + 1) htail
      have hend : c + (steps + 1) + 1 = c + 1 + steps + 1 := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- In a final `L` suffix after a last-change index, walking `steps` row steps
and then taking the suffix cross edge reaches column `r + steps + 1`. -/
theorem snakeReachableFuel_suffix_L_rowCode_colCode_succ_add
    {w : SnakeWord} {last r steps : ℕ} (hlast : w.IsLastChangeIndex last)
    (hrs : r + steps < w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    snakeReachableFuel w (steps + 1)
      (snakeRowCode r) (snakeColCode (r + steps + 1)) = true := by
  induction steps generalizing r with
  | zero =>
      have hcol_bound : snakeColCode (r + 1) < snakeCodeBound w := by
        simp [snakeColCode, snakeCodeBound]
        lia
      have hcross := snakeCrossCoverEdge_suffix_L_of_isLastChangeIndex
        (w := w) (k := last) (d := r) hlast (by simpa using hrs) hfinal
      have hcover :
          snakeCoverEdge w (snakeRowCode r) (snakeColCode (r + 1)) = true := by
        rw [snakeCoverEdge]
        simp [hcross]
      exact snakeReachableFuel_succ_of_coverEdge hcol_bound hcover
  | succ steps ih =>
      have hr : r < w.length := by
        lia
      have hnext_bound : snakeRowCode (r + 1) < snakeCodeBound w := by
        simp [snakeRowCode, snakeCodeBound]
        lia
      have hcover := snakeCoverEdge_rowCode_succ (w := w) (r := r) hr
      have htail : r + 1 + steps < w.length - (last + 1) := by
        lia
      have hreach := ih (r := r + 1) htail
      have hend : r + (steps + 1) + 1 = r + 1 + steps + 1 := by
        lia
      rw [hend]
      exact snakeReachableFuel_succ_of_coverEdge_of_reachable hnext_bound hcover hreach

/-- In an all-`R` snake word, a column reaches exactly the higher rows in exact
path fuel. -/
theorem snakeReachableFuel_replicate_R_colCode_rowCode_of_lt {n c r : ℕ}
    (hcr : c < r) (hr : r ≤ n) :
    snakeReachableFuel (List.replicate n SnakeLetter.R) (r - c)
      (snakeColCode c) (snakeRowCode r) = true := by
  have hgap : c + (r - c - 1) < n := by
    lia
  have hreach := snakeReachableFuel_replicate_R_colCode_rowCode_succ_add
    (n := n) (c := c) (k := r - c - 1) hgap
  have htarget :
      snakeReachableFuel (List.replicate n SnakeLetter.R) (r - c)
          (snakeColCode c) (snakeRowCode r) =
        snakeReachableFuel (List.replicate n SnakeLetter.R) (r - c - 1 + 1)
          (snakeColCode c) (snakeRowCode (c + (r - c - 1) + 1)) := by
    congr 2 <;> lia
  rw [htarget]
  exact hreach

/-- In an all-`L` snake word, a row reaches exactly the higher columns in exact
path fuel. -/
theorem snakeReachableFuel_replicate_L_rowCode_colCode_of_lt {n r c : ℕ}
    (hrc : r < c) (hc : c ≤ n) :
    snakeReachableFuel (List.replicate n SnakeLetter.L) (c - r)
      (snakeRowCode r) (snakeColCode c) = true := by
  have hgap : r + (c - r - 1) < n := by
    lia
  have hreach := snakeReachableFuel_replicate_L_rowCode_colCode_succ_add
    (n := n) (r := r) (k := c - r - 1) hgap
  have htarget :
      snakeReachableFuel (List.replicate n SnakeLetter.L) (c - r)
          (snakeRowCode r) (snakeColCode c) =
        snakeReachableFuel (List.replicate n SnakeLetter.L) (c - r - 1 + 1)
          (snakeRowCode r) (snakeColCode (r + (c - r - 1) + 1)) := by
    congr 2 <;> lia
  rw [htarget]
  exact hreach

/-- In an all-`R` word, rows never reach columns. -/
theorem snakeReachableFuel_replicate_R_rowCode_colCode_eq_false
    {n fuel r c : ℕ} :
    snakeReachableFuel (List.replicate n SnakeLetter.R) fuel
      (snakeRowCode r) (snakeColCode c) = false := by
  induction fuel generalizing r with
  | zero =>
      exact Bool.eq_false_of_not_eq_true fun hreach => by
        simp only [snakeReachableFuel, beq_iff_eq] at hreach
        exact snakeRowCode_ne_colCode r c hreach
  | succ fuel ih =>
      apply Bool.eq_false_of_not_eq_true
      intro hreach
      change ((snakeRowCode r == snakeColCode c) ||
        (List.range (snakeCodeBound (List.replicate n SnakeLetter.R))).any fun x =>
          snakeCoverEdge (List.replicate n SnakeLetter.R) (snakeRowCode r) x &&
            snakeReachableFuel (List.replicate n SnakeLetter.R) fuel x
              (snakeColCode c)) = true at hreach
      rw [Bool.or_eq_true] at hreach
      rcases hreach with heq | hstep
      · rw [beq_iff_eq] at heq
        exact snakeRowCode_ne_colCode r c heq
      · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hstep
        rcases hstep with ⟨x, _hx, hcover, htail⟩
        rw [snakeCoverEdge_replicate_R] at hcover
        rcases hcover with hchain | hcross
        · rcases hchain with ⟨hnext, _hbound⟩
          have hx : x = snakeRowCode (r + 1) := by
            rw [← hnext]
            simp [snakeRowCode]
            lia
          rw [hx] at htail
          have hfalse := ih (r := r + 1)
          rw [hfalse] at htail
          cases htail
        · rcases hcross with ⟨d, _hd, hrow, _hx⟩
          exact snakeRowCode_ne_colCode r d hrow

/-- In an all-`L` word, columns never reach rows. -/
theorem snakeReachableFuel_replicate_L_colCode_rowCode_eq_false
    {n fuel c r : ℕ} :
    snakeReachableFuel (List.replicate n SnakeLetter.L) fuel
      (snakeColCode c) (snakeRowCode r) = false := by
  induction fuel generalizing c with
  | zero =>
      exact Bool.eq_false_of_not_eq_true fun hreach => by
        simp only [snakeReachableFuel, beq_iff_eq] at hreach
        exact snakeColCode_ne_rowCode c r hreach
  | succ fuel ih =>
      apply Bool.eq_false_of_not_eq_true
      intro hreach
      change ((snakeColCode c == snakeRowCode r) ||
        (List.range (snakeCodeBound (List.replicate n SnakeLetter.L))).any fun x =>
          snakeCoverEdge (List.replicate n SnakeLetter.L) (snakeColCode c) x &&
            snakeReachableFuel (List.replicate n SnakeLetter.L) fuel x
              (snakeRowCode r)) = true at hreach
      rw [Bool.or_eq_true] at hreach
      rcases hreach with heq | hstep
      · rw [beq_iff_eq] at heq
        exact snakeColCode_ne_rowCode c r heq
      · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hstep
        rcases hstep with ⟨x, _hx, hcover, htail⟩
        rw [snakeCoverEdge_replicate_L] at hcover
        rcases hcover with hchain | hcross
        · rcases hchain with ⟨hnext, _hbound⟩
          have hx : x = snakeColCode (c + 1) := by
            rw [← hnext]
            simp [snakeColCode]
            lia
          rw [hx] at htail
          have hfalse := ih (c := c + 1)
          rw [hfalse] at htail
          cases htail
        · rcases hcross with ⟨d, _hd, hcol, _hx⟩
          exact snakeColCode_ne_rowCode c d hcol

/-- In an all-`R` word, columns cannot reach rows weakly below them. -/
theorem snakeReachableFuel_replicate_R_colCode_rowCode_eq_false_of_le
    {n fuel c r : ℕ} (hrc : r ≤ c) :
    snakeReachableFuel (List.replicate n SnakeLetter.R) fuel
      (snakeColCode c) (snakeRowCode r) = false := by
  exact snakeReachableFuel_eq_false_of_target_lt (by
    simp [snakeRowCode, snakeColCode]
    lia)

/-- In an all-`L` word, rows cannot reach columns weakly below them. -/
theorem snakeReachableFuel_replicate_L_rowCode_colCode_eq_false_of_le
    {n fuel r c : ℕ} (hcr : c ≤ r) :
    snakeReachableFuel (List.replicate n SnakeLetter.L) fuel
      (snakeRowCode r) (snakeColCode c) = false := by
  induction fuel generalizing r with
  | zero =>
      exact Bool.eq_false_of_not_eq_true fun hreach => by
        simp only [snakeReachableFuel, beq_iff_eq] at hreach
        exact snakeRowCode_ne_colCode r c hreach
  | succ fuel ih =>
      apply Bool.eq_false_of_not_eq_true
      intro hreach
      change ((snakeRowCode r == snakeColCode c) ||
        (List.range (snakeCodeBound (List.replicate n SnakeLetter.L))).any fun x =>
          snakeCoverEdge (List.replicate n SnakeLetter.L) (snakeRowCode r) x &&
            snakeReachableFuel (List.replicate n SnakeLetter.L) fuel x
              (snakeColCode c)) = true at hreach
      rw [Bool.or_eq_true] at hreach
      rcases hreach with heq | hstep
      · rw [beq_iff_eq] at heq
        exact snakeRowCode_ne_colCode r c heq
      · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hstep
        rcases hstep with ⟨x, _hx, hcover, htail⟩
        rw [snakeCoverEdge_replicate_L] at hcover
        rcases hcover with hchain | hcross
        · rcases hchain with ⟨hnext, _hbound⟩
          have hx : x = snakeRowCode (r + 1) := by
            rw [← hnext]
            simp [snakeRowCode]
            lia
          rw [hx] at htail
          have hfalse := ih (r := r + 1) (by lia)
          rw [hfalse] at htail
          cases htail
        · rcases hcross with ⟨d, _hd, hrow, hxcol⟩
          have hrd : r = d := by
            simpa [snakeRowCode] using hrow
          rw [← hrd] at hxcol
          rw [hxcol] at htail
          have hdrop : snakeColCode c < snakeColCode (r + 1) := by
            simp [snakeColCode]
            lia
          have hfalse := snakeReachableFuel_eq_false_of_target_lt
            (w := List.replicate n SnakeLetter.L) (fuel := fuel)
            (a := snakeColCode (r + 1)) (b := snakeColCode c) hdrop
          rw [hfalse] at htail
          cases htail

/-- Adding one unit of fuel preserves reachability. -/
theorem snakeReachableFuel_succ_of_reachable {w : SnakeWord} {fuel a b : ℕ}
    (hreach : snakeReachableFuel w fuel a b = true) :
    snakeReachableFuel w (fuel + 1) a b = true := by
  induction fuel generalizing a with
  | zero =>
      simp only [snakeReachableFuel, beq_iff_eq] at hreach
      subst b
      simp
  | succ fuel ih =>
      change ((a == b) ||
        (List.range (snakeCodeBound w)).any fun c =>
          snakeCoverEdge w a c && snakeReachableFuel w (fuel + 1) c b) = true
      change ((a == b) ||
        (List.range (snakeCodeBound w)).any fun c =>
          snakeCoverEdge w a c && snakeReachableFuel w fuel c b) = true at hreach
      rw [Bool.or_eq_true] at hreach
      rcases hreach with hab | hstep
      · rw [beq_iff_eq] at hab
        simp [hab]
      · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hstep
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
          Bool.and_eq_true]
        rcases hstep with ⟨c, hc, hcover, htail⟩
        exact Or.inr ⟨c, hc, hcover, ih htail⟩

/-- Increasing the available fuel preserves reachability. -/
theorem snakeReachableFuel_of_le {w : SnakeWord} {fuel fuel' a b : ℕ}
    (hff : fuel ≤ fuel') (hreach : snakeReachableFuel w fuel a b = true) :
    snakeReachableFuel w fuel' a b = true := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hff
  clear hff
  induction extra with
  | zero =>
      simpa using hreach
  | succ extra ih =>
      rw [Nat.add_succ]
      exact snakeReachableFuel_succ_of_reachable ih

/-! ## Element reachability -/

/-- Reachability in the generalized snake poset cover graph. -/
def snakeElementReachable (w : SnakeWord) (a b : ℕ) : Bool :=
  snakeReachableFuel w (snakeCodeBound w) a b

/-- In an all-`R` snake word, a column is below any higher reachable row at the
`snakeElementReachable` level. -/
theorem snakeElementReachable_replicate_R_colCode_rowCode_of_lt {n c r : ℕ}
    (hcr : c < r) (hr : r ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.R)
      (snakeColCode c) (snakeRowCode r) = true := by
  unfold snakeElementReachable
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia)
    (snakeReachableFuel_replicate_R_colCode_rowCode_of_lt hcr hr)

/-- In an all-`L` snake word, a row is below any higher reachable column at the
`snakeElementReachable` level. -/
theorem snakeElementReachable_replicate_L_rowCode_colCode_of_lt {n r c : ℕ}
    (hrc : r < c) (hc : c ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.L)
      (snakeRowCode r) (snakeColCode c) = true := by
  unfold snakeElementReachable
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia)
    (snakeReachableFuel_replicate_L_rowCode_colCode_of_lt hrc hc)

/-- In a final `R` suffix after a last-change index, a suffix column is below
any higher suffix row. -/
theorem snakeElementReachable_suffix_R_colCode_rowCode_of_lt
    {w : SnakeWord} {last c r : ℕ} (hlast : w.IsLastChangeIndex last)
    (hcr : c < r) (hr : r ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.R) :
    snakeElementReachable w (snakeColCode c) (snakeRowCode r) = true := by
  unfold snakeElementReachable
  have hgap : c + (r - c - 1) < w.length - (last + 1) := by
    lia
  have hreach := snakeReachableFuel_suffix_R_colCode_rowCode_succ_add
    (w := w) (last := last) (c := c) (steps := r - c - 1) hlast hgap hfinal
  have hreach_exact :
      snakeReachableFuel w (r - c) (snakeColCode c) (snakeRowCode r) = true := by
    have htarget :
        snakeReachableFuel w (r - c) (snakeColCode c) (snakeRowCode r) =
          snakeReachableFuel w (r - c - 1 + 1) (snakeColCode c)
            (snakeRowCode (c + (r - c - 1) + 1)) := by
      congr 2 <;> lia
    rw [htarget]
    exact hreach
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia) hreach_exact

/-- In a final `L` suffix after a last-change index, a suffix row is below any
higher suffix column. -/
theorem snakeElementReachable_suffix_L_rowCode_colCode_of_lt
    {w : SnakeWord} {last r c : ℕ} (hlast : w.IsLastChangeIndex last)
    (hrc : r < c) (hc : c ≤ w.length - (last + 1))
    (hfinal : w.getD (w.length - 1) SnakeLetter.L = SnakeLetter.L) :
    snakeElementReachable w (snakeRowCode r) (snakeColCode c) = true := by
  unfold snakeElementReachable
  have hgap : r + (c - r - 1) < w.length - (last + 1) := by
    lia
  have hreach := snakeReachableFuel_suffix_L_rowCode_colCode_succ_add
    (w := w) (last := last) (r := r) (steps := c - r - 1) hlast hgap hfinal
  have hreach_exact :
      snakeReachableFuel w (c - r) (snakeRowCode r) (snakeColCode c) = true := by
    have htarget :
        snakeReachableFuel w (c - r) (snakeRowCode r) (snakeColCode c) =
          snakeReachableFuel w (c - r - 1 + 1) (snakeRowCode r)
            (snakeColCode (r + (c - r - 1) + 1)) := by
      congr 2 <;> lia
    rw [htarget]
    exact hreach
  exact snakeReachableFuel_of_le (by simp [snakeCodeBound]; lia) hreach_exact

/-- At the `snakeElementReachable` level, all-`R` rows never reach columns. -/
theorem snakeElementReachable_replicate_R_rowCode_colCode_eq_false
    {n r c : ℕ} :
    snakeElementReachable (List.replicate n SnakeLetter.R)
      (snakeRowCode r) (snakeColCode c) = false :=
  snakeReachableFuel_replicate_R_rowCode_colCode_eq_false

/-- At the `snakeElementReachable` level, all-`L` columns never reach rows. -/
theorem snakeElementReachable_replicate_L_colCode_rowCode_eq_false
    {n c r : ℕ} :
    snakeElementReachable (List.replicate n SnakeLetter.L)
      (snakeColCode c) (snakeRowCode r) = false :=
  snakeReachableFuel_replicate_L_colCode_rowCode_eq_false

/-- All-`R` column-to-row reachability is exactly the strict index inequality. -/
theorem snakeElementReachable_replicate_R_colCode_rowCode_eq_true_iff
    {n c r : ℕ} (hr : r ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.R)
      (snakeColCode c) (snakeRowCode r) = true ↔ c < r := by
  constructor
  · intro hreach
    have hle := snakeReachableFuel_le hreach
    simp [snakeRowCode, snakeColCode] at hle
    lia
  · intro hcr
    exact snakeElementReachable_replicate_R_colCode_rowCode_of_lt hcr hr

/-- All-`L` row-to-column reachability is exactly the strict index inequality. -/
theorem snakeElementReachable_replicate_L_rowCode_colCode_eq_true_iff
    {n r c : ℕ} (hc : c ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.L)
      (snakeRowCode r) (snakeColCode c) = true ↔ r < c := by
  constructor
  · intro hreach
    by_contra hnot
    have hcr : c ≤ r := Nat.le_of_not_gt hnot
    have hreachFuel :
        snakeReachableFuel (List.replicate n SnakeLetter.L)
          (snakeCodeBound (List.replicate n SnakeLetter.L))
          (snakeRowCode r) (snakeColCode c) = true := by
      simpa [snakeElementReachable] using hreach
    have hfalse :=
      snakeReachableFuel_replicate_L_rowCode_colCode_eq_false_of_le
        (n := n) (fuel := snakeCodeBound (List.replicate n SnakeLetter.L)) hcr
    rw [hfalse] at hreachFuel
    cases hreachFuel
  · intro hrc
    exact snakeElementReachable_replicate_L_rowCode_colCode_of_lt hrc hc

/-- In an all-`R` word, a column fails to reach a row exactly when the row is
weakly below the column. -/
theorem snakeElementReachable_replicate_R_colCode_rowCode_eq_false_iff
    {n c r : ℕ} (hr : r ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.R)
      (snakeColCode c) (snakeRowCode r) = false ↔ r ≤ c := by
  rw [← Bool.not_eq_true]
  rw [snakeElementReachable_replicate_R_colCode_rowCode_eq_true_iff hr]
  exact not_lt

/-- In an all-`L` word, a row fails to reach a column exactly when the column is
weakly below the row. -/
theorem snakeElementReachable_replicate_L_rowCode_colCode_eq_false_iff
    {n r c : ℕ} (hc : c ≤ n) :
    snakeElementReachable (List.replicate n SnakeLetter.L)
      (snakeRowCode r) (snakeColCode c) = false ↔ c ≤ r := by
  rw [← Bool.not_eq_true]
  rw [snakeElementReachable_replicate_L_rowCode_colCode_eq_true_iff hc]
  exact not_lt

end GeneralizedSnakePosets
end RealRooted
