import RealRooted.BrandenVecchi.SignedWordEnumerator
import RealRooted.BrandenVecchi.SignedWordRuns.Basic

/-!
# Statistics of signed-word run decompositions

This file proves the pointwise length, adjacency-statistic, and multiplicative
weight identities for canonical run-length data.  The results are stated first
for lists and arbitrary decidable adjacency relations, then specialized to the
signed-word summand from Brändén--Vecchi Theorem 8.11.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

/-! ## Generic adjacent-pair counts -/

/-- Number of adjacent pairs satisfying a decidable relation. -/
def adjacentCount {α : Type*} (relation : α → α → Prop)
    [DecidableRel relation] : List α → ℕ
  | [] => 0
  | [_] => 0
  | left :: right :: rest =>
      (if relation left right then 1 else 0) +
        adjacentCount relation (right :: rest)

@[simp]
theorem adjacentCount_nil {α : Type*} (relation : α → α → Prop)
    [DecidableRel relation] :
    adjacentCount relation [] = 0 :=
  rfl

@[simp]
theorem adjacentCount_singleton {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation] (a : α) :
    adjacentCount relation [a] = 0 :=
  rfl

@[simp]
theorem adjacentCount_cons_cons {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation]
    (left right : α) (rest : List α) :
    adjacentCount relation (left :: right :: rest) =
      (if relation left right then 1 else 0) +
        adjacentCount relation (right :: rest) :=
  rfl

/-- Prepending a nonempty constant block adds its internal adjacent pairs and
one possible boundary pair. -/
theorem adjacentCount_replicate_succ_append {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation] (a : α) :
    ∀ (n : ℕ) (tail : List α),
      adjacentCount relation (List.replicate (n + 1) a ++ tail) =
        n * (if relation a a then 1 else 0) +
          match tail with
          | [] => 0
          | b :: rest =>
              (if relation a b then 1 else 0) +
                adjacentCount relation (b :: rest)
  | 0, [] => by simp
  | 0, b :: rest => by simp
  | n + 1, tail => by
      rw [show List.replicate (n + 1 + 1) a =
          a :: List.replicate (n + 1) a by
        simp [List.replicate_succ]]
      rw [show List.replicate (n + 1) a =
          a :: List.replicate n a by
        simp [List.replicate_succ]]
      simp only [List.cons_append, adjacentCount_cons_cons]
      change (if relation a a then 1 else 0) +
          adjacentCount relation (List.replicate (n + 1) a ++ tail) = _
      rw [adjacentCount_replicate_succ_append relation a n tail]
      by_cases hself : relation a a
      · simp only [if_pos hself, mul_one]
        ac_rfl
      · simp [hself]

/-- Appending to a nonempty list adds exactly the new final adjacent pair. -/
theorem adjacentCount_append_singleton {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation] (x : α) :
    ∀ (word : List α) (hword : word ≠ []),
      adjacentCount relation (word ++ [x]) =
        adjacentCount relation word +
          if relation (word.getLast hword) x then 1 else 0
  | [], hword => (hword rfl).elim
  | [a], _ => by simp
  | a :: b :: rest, _ => by
      have htail := adjacentCount_append_singleton relation x
        (b :: rest) (by simp)
      simp only [List.cons_append] at htail
      change adjacentCount relation (a :: b :: (rest ++ [x])) = _
      rw [adjacentCount_cons_cons, htail, adjacentCount_cons_cons]
      simp [Nat.add_assoc]

/-- Adjacent-pair counting on a nonempty tuple is the corresponding sum over
its adjacent indices. -/
theorem adjacentCount_ofFn_succ {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation]
    (n : ℕ) (word : Fin (n + 1) → α) :
    adjacentCount relation (List.ofFn word) =
      ∑ i : Fin n,
        if relation (word i.castSucc) (word i.succ) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let initialWord : Fin (n + 1) → α := fun i => word i.castSucc
      let last := word (Fin.last (n + 1))
      have hword : Fin.snoc initialWord last = word :=
        Fin.snoc_init_self word
      rw [← hword, List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [List.concat_eq_append]
      change adjacentCount relation (List.ofFn initialWord ++ [last]) = _
      rw [adjacentCount_append_singleton relation last
          (List.ofFn initialWord) (by simp),
        ih initialWord, Fin.sum_univ_castSucc]
      simp only [List.getLast_ofFn_succ, Fin.snoc_castSucc,
        Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc,
        initialWord, last]

/-- List-level descent number. -/
def listDescentNumber {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (word : List α) : ℕ :=
  adjacentCount (fun left right => right < left) word

/-- List-level collision number. -/
def listCollisionNumber {α : Type*} [DecidableEq α]
    (word : List α) : ℕ :=
  adjacentCount (· = ·) word

/-- A list with distinct adjacent entries has no equality-adjacent pairs. -/
theorem adjacentCount_eq_of_isChain_ne {α : Type*} [DecidableEq α]
    (word : List α) (hword : word.IsChain (· ≠ ·)) :
    adjacentCount (· = ·) word = 0 := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b rest =>
          rw [List.isChain_cons_cons] at hword
          rw [adjacentCount_cons_cons, if_neg hword.1]
          simpa using ih hword.2

/-! ## Run-length expressions -/

namespace RunLengthData

/-- The Smirnov skeleton: one representative for each maximal run. -/
def representatives {α : Type*} (data : RunLengthData α) : List α :=
  data.runs.map Prod.fst

/-- Total excess length contributed by repetitions inside runs. -/
def excess {α : Type*} (data : RunLengthData α) : ℕ :=
  (data.runs.map fun run => run.2 - 1).sum

/-- Internal adjacent pairs satisfying `relation`, counted run by run. -/
def adjacentExcess {α : Type*} (relation : α → α → Prop)
    [DecidableRel relation] (data : RunLengthData α) : ℕ :=
  (data.runs.map fun run =>
    (run.2 - 1) * if relation run.1 run.1 then 1 else 0).sum

/-- Product of representative weights, each raised to its run length. -/
def runWeight {α M : Type*} [CommMonoid M]
    (weight : α → M) (data : RunLengthData α) : M :=
  (data.runs.map fun run => weight run.1 ^ run.2).prod

/-- Expansion length is the sum of the run lengths. -/
theorem length_expand {α : Type*} (data : RunLengthData α) :
    data.expand.length = (data.runs.map Prod.snd).sum := by
  simp only [expand, List.length_flatten]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro run _
  simp

/-- Multiplicative word weight factors run by run. -/
theorem prod_map_expand {α M : Type*} [CommMonoid M]
    (weight : α → M) (data : RunLengthData α) :
    (data.expand.map weight).prod = data.runWeight weight := by
  simp only [expand, List.map_flatten, List.prod_flatten, runWeight]
  apply congrArg List.prod
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro run _
  simp

private theorem adjacentCount_expand_runs {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation] :
    ∀ (runs : List (α × ℕ))
      (_hpos : ∀ run ∈ runs, 0 < run.2),
      adjacentCount relation
          ((runs.map fun run => List.replicate run.2 run.1).flatten) =
        adjacentCount relation (runs.map Prod.fst) +
          (runs.map fun run =>
            (run.2 - 1) * if relation run.1 run.1 then 1 else 0).sum
  | [], _ => rfl
  | (a, length) :: runs, hpos => by
      have hlength : 0 < length := hpos (a, length) (by simp)
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hlength
      have htail_pos : ∀ run ∈ runs, 0 < run.2 := by
        intro run hrun
        exact hpos run (by simp [hrun])
      have ih := adjacentCount_expand_runs relation runs htail_pos
      cases runs with
      | nil =>
          simp only [List.map_cons, List.map_nil, List.flatten_cons,
            List.flatten_nil, List.append_nil, List.sum_cons, List.sum_nil,
            adjacentCount_singleton, Nat.add_zero]
          rw [hn, Nat.add_sub_cancel]
          simpa using
            (adjacentCount_replicate_succ_append relation a n [])
      | cons next rest =>
          obtain ⟨b, nextLength⟩ := next
          have hnextLength : 0 < nextLength :=
            htail_pos (b, nextLength) (by simp)
          obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' hnextLength
          have htail_form :
              List.replicate (m + 1) b ++
                  ((rest.map fun run =>
                    List.replicate run.2 run.1).flatten) =
                b :: (List.replicate m b ++
                  ((rest.map fun run =>
                    List.replicate run.2 run.1).flatten)) := by
            simp [List.replicate_succ]
          simp only [List.map_cons, List.flatten_cons, List.sum_cons] at ih ⊢
          rw [hm, Nat.add_sub_cancel] at ih
          rw [hn, hm, Nat.add_sub_cancel, Nat.add_sub_cancel]
          rw [htail_form] at ih ⊢
          rw [adjacentCount_replicate_succ_append relation a n]
          simp only [adjacentCount_cons_cons]
          rw [ih]
          ac_rfl

/-- Adjacent-pair counts on an expansion split into the skeleton boundary
count plus the internal counts of its constant runs. -/
theorem adjacentCount_expand {α : Type*}
    (relation : α → α → Prop) [DecidableRel relation]
    (data : RunLengthData α) :
    adjacentCount relation data.expand =
      adjacentCount relation data.representatives +
        data.adjacentExcess relation := by
  exact adjacentCount_expand_runs relation data.runs data.lengths_pos

/-- The descent number of the expanded signed word is the descent number of
its Smirnov skeleton. -/
theorem listDescentNumber_expand {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    listDescentNumber data.expand =
      listDescentNumber data.representatives := by
  change adjacentCount
      (fun left right : SignedLetter q p => right < left) data.expand =
    adjacentCount
      (fun left right : SignedLetter q p => right < left)
        data.representatives
  rw [adjacentCount_expand]
  simp [adjacentExcess]

/-- Collisions in an expanded canonical word are exactly its total excess
run length. -/
theorem listCollisionNumber_expand {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    listCollisionNumber data.expand = data.excess := by
  change adjacentCount
      (fun left right : SignedLetter q p => left = right) data.expand =
    data.excess
  rw [adjacentCount_expand]
  have hzero : adjacentCount
      (fun left right : SignedLetter q p => left = right)
        data.representatives = 0 :=
    adjacentCount_eq_of_isChain_ne data.representatives (by
      simpa [representatives] using data.representatives_ne)
  rw [hzero, Nat.zero_add]
  simp [adjacentExcess, excess]

/-- Under signed admissibility, a positive representative contributes
exponent one. -/
theorem length_eq_one_of_isPositive {q p : ℕ}
    {data : RunLengthData (SignedLetter q p)} (hsigned : data.IsSigned)
    {run : SignedLetter q p × ℕ} (hrun : run ∈ data.runs)
    (hpositive : run.1.IsPositive) :
    run.2 = 1 :=
  hsigned run hrun hpositive

end RunLengthData

/-! ## List/finite-function bridges -/

/-- Product of weights along a list. -/
def listWordWeight {α M : Type*} [CommMonoid M]
    (weight : α → M) (word : List α) : M :=
  (word.map weight).prod

/-- The list product agrees with the existing finite-function word weight. -/
theorem listWordWeight_ofFn {R : Type*} [CommSemiring R]
    {q p n : ℕ} (weight : SignedLetter q p → R)
    (word : Fin n → SignedLetter q p) :
    listWordWeight weight (List.ofFn word) = signedWordWeight weight word := by
  simp [listWordWeight, signedWordWeight, List.prod_ofFn]

/-- The list descent statistic agrees with the existing signed-word
statistic. -/
theorem listDescentNumber_ofFn {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    listDescentNumber (List.ofFn word) = signedDescentNumber word := by
  cases n with
  | zero => simp [listDescentNumber]
  | succ n =>
      rw [listDescentNumber, adjacentCount_ofFn_succ]
      simp [signedDescentNumber,
        RealRooted.ParkingFunctions.descentNumber,
        RealRooted.ParkingFunctions.descentSet]

/-- The list collision statistic agrees with the existing signed-word
statistic. -/
theorem listCollisionNumber_ofFn {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    listCollisionNumber (List.ofFn word) = signedCollisionNumber word := by
  cases n with
  | zero => simp [listCollisionNumber]
  | succ n =>
      rw [listCollisionNumber, adjacentCount_ofFn_succ]
      simp [signedCollisionNumber, collisionSet]

/-! ## Pointwise compressed-word identities -/

/-- The run lengths in the compression of a length-`n` word sum to `n`. -/
theorem sum_runLengths_compress_ofFn {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    (((compressRunLengthData (List.ofFn word)).runs.map Prod.snd).sum) = n := by
  calc
    _ = (compressRunLengthData (List.ofFn word)).expand.length :=
      (compressRunLengthData (List.ofFn word)).length_expand.symm
    _ = (List.ofFn word).length := by rw [expand_compressRunLengthData]
    _ = n := List.length_ofFn

/-- Compression preserves the descent statistic. -/
theorem descentNumber_representatives_compress_ofFn {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    listDescentNumber
        (compressRunLengthData (List.ofFn word)).representatives =
      signedDescentNumber word := by
  calc
    _ = listDescentNumber
        (compressRunLengthData (List.ofFn word)).expand :=
      (compressRunLengthData (List.ofFn word)).listDescentNumber_expand.symm
    _ = listDescentNumber (List.ofFn word) := by
      rw [expand_compressRunLengthData]
    _ = signedDescentNumber word := listDescentNumber_ofFn word

/-- The collision number is the sum of `runLength - 1`. -/
theorem excess_compress_ofFn {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    (compressRunLengthData (List.ofFn word)).excess =
      signedCollisionNumber word := by
  calc
    _ = listCollisionNumber
        (compressRunLengthData (List.ofFn word)).expand :=
      (compressRunLengthData (List.ofFn word)).listCollisionNumber_expand.symm
    _ = listCollisionNumber (List.ofFn word) := by
      rw [expand_compressRunLengthData]
    _ = signedCollisionNumber word := listCollisionNumber_ofFn word

/-- The finite-function word weight is the runwise representative weight. -/
theorem runWeight_compress_ofFn {R : Type*} [CommSemiring R]
    {q p n : ℕ} (weight : SignedLetter q p → R)
    (word : Fin n → SignedLetter q p) :
    (compressRunLengthData (List.ofFn word)).runWeight weight =
      signedWordWeight weight word := by
  calc
    _ = ((compressRunLengthData (List.ofFn word)).expand.map weight).prod :=
      ((compressRunLengthData (List.ofFn word)).prod_map_expand weight).symm
    _ = ((List.ofFn word).map weight).prod := by
      rw [expand_compressRunLengthData]
    _ = listWordWeight weight (List.ofFn word) := rfl
    _ = signedWordWeight weight word := listWordWeight_ofFn weight word

/-- In an admissible word, every positive representative in its compression
has exponent one. -/
theorem compress_ofFn_length_eq_one_of_isPositive {q p n : ℕ}
    (word : Fin n → SignedLetter q p) (hword : IsSignedWord n word)
    {run : SignedLetter q p × ℕ}
    (hrun : run ∈ (compressRunLengthData (List.ofFn word)).runs)
    (hpositive : run.1.IsPositive) :
    run.2 = 1 := by
  apply RunLengthData.length_eq_one_of_isPositive ?_ hrun hpositive
  rw [← (compressRunLengthData
    (List.ofFn word)).isSignedList_expand_iff]
  simpa using (isSignedList_ofFn_iff word).mpr hword

namespace RunLengthData

/-- The complete polynomial summand expressed in compressed-run data. -/
noncomputable def runSummand {R : Type*} [CommSemiring R] {q p : ℕ}
    (weight : SignedLetter q p → R)
    (data : RunLengthData (SignedLetter q p)) : R[X] :=
  C (data.runWeight weight) *
    X ^ listDescentNumber data.representatives *
      (1 + X) ^ data.excess

end RunLengthData

/-- The literal per-word summand is exactly its compressed-run expression. -/
theorem signedWordSummand_eq_runSummand {R : Type*} [CommSemiring R]
    {q p n : ℕ} (weight : SignedLetter q p → R)
    (word : Fin n → SignedLetter q p) :
    C (signedWordWeight weight word) *
        X ^ signedDescentNumber word *
          (1 + X) ^ signedCollisionNumber word =
      (compressRunLengthData (List.ofFn word)).runSummand weight := by
  rw [RunLengthData.runSummand, runWeight_compress_ofFn,
    descentNumber_representatives_compress_ofFn, excess_compress_ofFn]

end RealRooted.BrandenVecchi
