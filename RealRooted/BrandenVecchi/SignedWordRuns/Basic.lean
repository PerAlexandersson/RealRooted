import RealRooted.BrandenVecchi.SignedWords
import RealRooted.Mathlib.Data.List.SplitBy
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn

/-!
# Run decompositions of finite signed words

This file packages the maximal equality runs of a list as representatives and
positive run lengths.  It then restricts the generic run-length equivalence to
the signed words in Brändén--Vecchi Theorem 8.11: a positive representative
must have run length one, while a negative representative may repeat.
-/

namespace RealRooted.BrandenVecchi

/-! ## Generic run-length data -/

/-- Canonical run-length data: adjacent representatives are distinct and
every run length is positive. -/
structure RunLengthData (α : Type*) where
  runs : List (α × ℕ)
  representatives_ne : (runs.map Prod.fst).IsChain (· ≠ ·)
  lengths_pos : ∀ run ∈ runs, 0 < run.2

namespace RunLengthData

@[ext]
theorem ext {α : Type*} {left right : RunLengthData α}
    (hruns : left.runs = right.runs) : left = right := by
  cases left
  cases right
  simp_all

/-- Expand run-length data by repeating each representative. -/
def expand {α : Type*} (data : RunLengthData α) : List α :=
  (data.runs.map fun run => List.replicate run.2 run.1).flatten

/-- The constant blocks represented by run-length data. -/
def blocks {α : Type*} (data : RunLengthData α) : List (List α) :=
  data.runs.map fun run => List.replicate run.2 run.1

@[simp]
theorem blocks_flatten {α : Type*} (data : RunLengthData α) :
    data.blocks.flatten = data.expand :=
  rfl

@[simp]
theorem expand_nil {α : Type*} : expand (⟨[], .nil, by simp⟩ : RunLengthData α) = [] :=
  rfl

end RunLengthData

/-- The maximal equality blocks of a list. -/
def equalityRuns {α : Type*} [DecidableEq α] (word : List α) : List (List α) :=
  word.splitBy fun a b => decide (a = b)

@[simp]
theorem flatten_equalityRuns {α : Type*} [DecidableEq α] (word : List α) :
    (equalityRuns word).flatten = word := by
  simp [equalityRuns]

theorem nil_notMem_equalityRuns {α : Type*} [DecidableEq α] (word : List α) :
    [] ∉ equalityRuns word := by
  exact List.nil_notMem_splitBy _ _

theorem isChain_eq_of_mem_equalityRuns {α : Type*} [DecidableEq α]
    {word block : List α} (hblock : block ∈ equalityRuns word) :
    block.IsChain (· = ·) := by
  have h := List.isChain_of_mem_splitBy hblock
  exact h.imp fun a b hab => of_decide_eq_true hab

theorem equalityRuns_separated {α : Type*} [DecidableEq α] (word : List α) :
    (equalityRuns word).IsChain fun left right =>
      ∃ hleft hright, left.getLast hleft ≠ right.head hright := by
  have h := List.isChain_getLast_head_splitBy
    (fun a b : α => decide (a = b)) word
  exact h.imp fun left right hsep => by
    obtain ⟨hleft, hright, hne⟩ := hsep
    exact ⟨hleft, hright, by simpa using hne⟩

private theorem head_eq_getLast_of_isChain_eq {α : Type*} {block : List α}
    (hblock : block ≠ []) (hchain : block.IsChain (· = ·)) :
    block.head hblock = block.getLast hblock := by
  have hrep : block = List.replicate block.length (block.head hblock) :=
    (List.isChain_eq_iff_eq_replicate.mp hchain) _ (List.head_mem_head? _)
  have hoptions : block.head? = block.getLast? := by
    rw [hrep]
    have hlength : 0 < block.length := List.length_pos_iff_ne_nil.mpr hblock
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hlength.ne'
    rw [hn]
    simp only [List.head?_replicate, List.getLast?_replicate,
      Nat.succ_ne_zero, ↓reduceIte]
  rw [List.head?_eq_some_head hblock,
    List.getLast?_eq_some_getLast hblock] at hoptions
  exact Option.some.inj hoptions

private def blocksToRuns {α : Type*} :
    (blocks : List (List α)) → [] ∉ blocks → List (α × ℕ)
  | [], _ => []
  | block :: blocks, hnil =>
      let hblock : block ≠ [] := fun h => hnil (by simp [h])
      let hblocks : [] ∉ blocks := fun h => hnil (by simp [h])
      (block.head hblock, block.length) :: blocksToRuns blocks hblocks

private theorem blocksToRuns_representatives_ne {α : Type*} :
    ∀ (blocks : List (List α)) (hnil : [] ∉ blocks),
      (∀ block ∈ blocks, block.IsChain (· = ·)) →
      blocks.IsChain (fun left right =>
        ∃ hleft hright, left.getLast hleft ≠ right.head hright) →
      ((blocksToRuns blocks hnil).map Prod.fst).IsChain (· ≠ ·)
  | [], _, _, _ => .nil
  | [block], _, _, _ => by simp [blocksToRuns]
  | block :: next :: blocks, hnil, hconstant, hseparated => by
      have hblock : block ≠ [] := fun h => hnil (by simp [h])
      have hnext : next ≠ [] := fun h => hnil (by simp [h])
      have hhead : block.head hblock ≠ next.head hnext := by
        obtain ⟨hblock', hnext', hne⟩ := hseparated.rel_head
        rw [head_eq_getLast_of_isChain_eq hblock
          (hconstant block (by simp))]
        exact hne
      have htailnil : [] ∉ next :: blocks := fun h => hnil (by simp [h])
      have htailconstant :
          ∀ current ∈ next :: blocks, current.IsChain (· = ·) := by
        intro current hcurrent
        exact hconstant current (by simp [hcurrent])
      have htail := blocksToRuns_representatives_ne (next :: blocks)
        htailnil htailconstant hseparated.tail
      simpa [blocksToRuns] using List.IsChain.cons_cons hhead htail

private theorem blocksToRuns_lengths_pos {α : Type*} :
    ∀ (blocks : List (List α)) (hnil : [] ∉ blocks),
      ∀ run ∈ blocksToRuns blocks hnil, 0 < run.2
  | [], _, _, hrun => by simp [blocksToRuns] at hrun
  | block :: blocks, hnil, run, hrun => by
      have hblock : block ≠ [] := fun h => hnil (by simp [h])
      have hblocks : [] ∉ blocks := fun h => hnil (by simp [h])
      simp only [blocksToRuns, List.mem_cons] at hrun
      rcases hrun with rfl | hrun
      · exact List.length_pos_iff_ne_nil.mpr hblock
      · exact blocksToRuns_lengths_pos blocks hblocks run hrun

/-- Compress a list into its maximal equality-run representatives and
lengths. -/
def compressRunLengthData {α : Type*} [DecidableEq α]
    (word : List α) : RunLengthData α where
  runs := blocksToRuns (equalityRuns word) (nil_notMem_equalityRuns word)
  representatives_ne := blocksToRuns_representatives_ne _ _
    (fun _ hblock => isChain_eq_of_mem_equalityRuns hblock)
    (equalityRuns_separated word)
  lengths_pos := blocksToRuns_lengths_pos _ _

private theorem expand_blocksToRuns {α : Type*} :
    ∀ (blocks : List (List α)) (hnil : [] ∉ blocks),
      (∀ block ∈ blocks, block.IsChain (· = ·)) →
      ((blocksToRuns blocks hnil).map
        fun run => List.replicate run.2 run.1).flatten = blocks.flatten
  | [], _, _ => by simp [blocksToRuns]
  | block :: blocks, hnil, hconstant => by
      have hblock : block ≠ [] := fun h => hnil (by simp [h])
      have hblocks : [] ∉ blocks := fun h => hnil (by simp [h])
      have hrep :
          List.replicate block.length (block.head hblock) = block := by
        symm
        exact (List.isChain_eq_iff_eq_replicate.mp
          (hconstant block (by simp))) _ (List.head_mem_head? _)
      have htailconstant : ∀ current ∈ blocks, current.IsChain (· = ·) := by
        intro current hcurrent
        exact hconstant current (by simp [hcurrent])
      simp [blocksToRuns, hrep,
        expand_blocksToRuns blocks hblocks htailconstant]

/-- Expanding the canonical run-length compression recovers the source list. -/
@[simp]
theorem expand_compressRunLengthData {α : Type*} [DecidableEq α]
    (word : List α) :
    (compressRunLengthData word).expand = word := by
  rw [show (compressRunLengthData word).expand =
      (equalityRuns word).flatten by
    exact expand_blocksToRuns _ _
      (fun _ hblock => isChain_eq_of_mem_equalityRuns hblock)]
  exact flatten_equalityRuns word

namespace RunLengthData

/-- Every block encoded by run-length data is nonempty. -/
theorem nil_notMem_blocks {α : Type*} (data : RunLengthData α) :
    [] ∉ data.blocks := by
  intro hnil
  rw [blocks, List.mem_map] at hnil
  obtain ⟨run, hrun, hrun_nil⟩ := hnil
  have hpos := data.lengths_pos run hrun
  have hzero : run.2 = 0 := by
    simpa using congrArg List.length hrun_nil
  exact hpos.ne' hzero

/-- Every block encoded by run-length data is constant. -/
theorem isChain_eq_of_mem_blocks {α : Type*} (data : RunLengthData α)
    {block : List α} (hblock : block ∈ data.blocks) :
    block.IsChain (· = ·) := by
  rw [blocks, List.mem_map] at hblock
  obtain ⟨run, _, rfl⟩ := hblock
  exact List.isChain_replicate_of_rel _ rfl

/-- Consecutive encoded blocks have distinct boundary elements. -/
theorem blocks_separated {α : Type*} (data : RunLengthData α) :
    data.blocks.IsChain fun left right =>
      ∃ hleft hright, left.getLast hleft ≠ right.head hright := by
  rw [blocks, List.isChain_map]
  have hruns : data.runs.IsChain fun left right => left.1 ≠ right.1 :=
    (List.isChain_map Prod.fst).mp data.representatives_ne
  exact hruns.imp_of_mem_imp fun left right hleft hright hne => by
    have hleft_pos := data.lengths_pos left hleft
    have hright_pos := data.lengths_pos right hright
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hleft_pos.ne'
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hright_pos.ne'
    refine ⟨by simp [hm], by simp [hn], ?_⟩
    simpa [hm, hn] using hne

/-- Splitting an expanded canonical encoding into maximal equality runs
recovers its encoded blocks. -/
theorem equalityRuns_expand {α : Type*} [DecidableEq α]
    (data : RunLengthData α) :
    equalityRuns data.expand = data.blocks := by
  rw [equalityRuns, ← blocks_flatten]
  exact List.splitBy_flatten data.nil_notMem_blocks
    (fun block hblock =>
      (data.isChain_eq_of_mem_blocks hblock).imp fun _ _ h => by
        simpa using h)
    (data.blocks_separated.imp fun _ _ h => by
      obtain ⟨hleft, hright, hne⟩ := h
      exact ⟨hleft, hright, by simpa using hne⟩)

end RunLengthData

private theorem blocksToRuns_map_replicate {α : Type*} :
    ∀ (runs : List (α × ℕ))
      (_hpos : ∀ run ∈ runs, 0 < run.2)
      (hnil : [] ∉ runs.map fun run => List.replicate run.2 run.1),
      blocksToRuns (runs.map fun run => List.replicate run.2 run.1) hnil = runs
  | [], _, _ => by simp [blocksToRuns]
  | run :: runs, hpos, hnil => by
      have hrun_pos : 0 < run.2 := hpos run (by simp)
      have htail_pos : ∀ current ∈ runs, 0 < current.2 := by
        intro current hcurrent
        exact hpos current (by simp [hcurrent])
      have htail_nil :
          [] ∉ runs.map fun current => List.replicate current.2 current.1 := by
        intro h
        exact hnil (by simp [h])
      have htail := blocksToRuns_map_replicate runs htail_pos htail_nil
      simpa [blocksToRuns, hrun_pos.ne'] using htail

private theorem blocksToRuns_congr {α : Type*}
    {left right : List (List α)} (heq : left = right)
    (hleft : [] ∉ left) (hright : [] ∉ right) :
    blocksToRuns left hleft = blocksToRuns right hright := by
  subst right
  rfl

namespace RunLengthData

/-- Compressing an expanded canonical encoding recovers the encoding. -/
@[simp]
theorem compress_expand {α : Type*} [DecidableEq α]
    (data : RunLengthData α) :
    compressRunLengthData data.expand = data := by
  apply RunLengthData.ext
  change blocksToRuns (equalityRuns data.expand) _ = data.runs
  calc
    _ = blocksToRuns data.blocks data.nil_notMem_blocks :=
      blocksToRuns_congr data.equalityRuns_expand _ _
    _ = data.runs :=
      blocksToRuns_map_replicate data.runs data.lengths_pos _

/-- Canonical run-length data are uniquely determined by their expansion. -/
theorem expand_injective {α : Type*} :
    Function.Injective (expand : RunLengthData α → List α) := by
  classical
  intro left right heq
  rw [← left.compress_expand, ← right.compress_expand, heq]

end RunLengthData

/-- Lists are equivalent to their canonical run-length encodings. -/
def runLengthEquiv (α : Type*) [DecidableEq α] :
    List α ≃ RunLengthData α where
  toFun := compressRunLengthData
  invFun := RunLengthData.expand
  left_inv := expand_compressRunLengthData
  right_inv := RunLengthData.compress_expand

/-! ## Signed run-length data -/

/-- List-level form of signed-word admissibility. -/
def IsSignedList {q p : ℕ} (word : List (SignedLetter q p)) : Prop :=
  word.IsChain SignedAdjacent

/-- The list and finite-function formulations of signed-word admissibility
agree. -/
theorem isSignedList_ofFn_iff {q p n : ℕ}
    (word : Fin n → SignedLetter q p) :
    IsSignedList (List.ofFn word) ↔ IsSignedWord n word := by
  cases n with
  | zero => simp [IsSignedList]
  | succ n =>
      rw [IsSignedList, List.isChain_ofFn, isSignedWord_succ_iff]
      constructor
      · intro h i
        have hadjacent := h i.val (by lia)
        convert hadjacent using 1 <;>
          apply congrArg word <;>
          apply Fin.ext <;>
          rfl
      · intro h i hi
        have hadjacent := h ⟨i, by lia⟩
        convert hadjacent using 1 <;>
          apply congrArg word <;>
          apply Fin.ext <;>
          rfl

namespace RunLengthData

/-- Signed run-length data have singleton positive runs. -/
def IsSigned {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) : Prop :=
  ∀ run ∈ data.runs, run.1.IsPositive → run.2 = 1

/-- Equivalently, every genuinely repeated run has negative
representative. -/
theorem isSigned_iff_repeated_isNegative {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    data.IsSigned ↔
      ∀ run ∈ data.runs, 1 < run.2 → run.1.IsNegative := by
  constructor
  · intro hsigned run hrun hrepeated
    rcases SignedLetter.isNegative_or_isPositive run.1 with hnegative | hpositive
    · exact hnegative
    · have hone := hsigned run hrun hpositive
      lia
  · intro hrepeated run hrun hpositive
    by_contra hone
    have hpos := data.lengths_pos run hrun
    have hnegative := hrepeated run hrun (by lia)
    exact SignedLetter.not_isNegative_and_isPositive run.1
      ⟨hnegative, hpositive⟩

private theorem blocks_isChain_signedAdjacent {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    data.blocks.IsChain fun left right =>
      ∀ᵉ (x ∈ left.getLast?) (y ∈ right.head?), SignedAdjacent x y := by
  exact data.blocks_separated.imp fun left right h => by
    obtain ⟨hleft, hright, hne⟩ := h
    simp [List.getLast?_eq_some_getLast hleft,
      List.head?_eq_some_head hright, SignedAdjacent, hne]

/-- An encoded word is admissible exactly when every positive run has
length one. -/
theorem isSignedList_expand_iff {q p : ℕ}
    (data : RunLengthData (SignedLetter q p)) :
    IsSignedList data.expand ↔ data.IsSigned := by
  rw [IsSignedList, ← data.blocks_flatten,
    List.isChain_flatten data.nil_notMem_blocks]
  constructor
  · rintro ⟨hblocks, _⟩ run hrun hpositive
    have hmem : List.replicate run.2 run.1 ∈ data.blocks := by
      rw [blocks]
      exact List.mem_map.mpr ⟨run, hrun, rfl⟩
    have hchain := hblocks (List.replicate run.2 run.1) hmem
    by_contra hone
    have htwo : 2 ≤ run.2 := by
      have hpos := data.lengths_pos run hrun
      lia
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' htwo
    rw [hk] at hchain
    have hadjacent : SignedAdjacent run.1 run.1 := by
      simpa [List.replicate_succ] using hchain.rel_head
    have hnegative := (signedAdjacent_self_iff run.1).mp hadjacent
    exact SignedLetter.not_isNegative_and_isPositive run.1
      ⟨hnegative, hpositive⟩
  · intro hsigned
    constructor
    · intro block hblock
      rw [blocks, List.mem_map] at hblock
      obtain ⟨run, hrun, rfl⟩ := hblock
      rcases SignedLetter.isNegative_or_isPositive run.1 with
        hnegative | hpositive
      · exact List.isChain_replicate_of_rel _
          ((signedAdjacent_self_iff run.1).mpr hnegative)
      · rw [hsigned run hrun hpositive]
        simp
    · exact data.blocks_isChain_signedAdjacent

/-- Every repeated run in the compression of an admissible signed list has a
negative representative. -/
theorem compress_repeated_isNegative {q p : ℕ}
    {word : List (SignedLetter q p)} (hword : IsSignedList word)
    {run : SignedLetter q p × ℕ}
    (hrun : run ∈ (compressRunLengthData word).runs)
    (hrepeated : 1 < run.2) :
    run.1.IsNegative := by
  apply ((compressRunLengthData word).isSigned_iff_repeated_isNegative.mp ?_)
    run hrun hrepeated
  rw [← (compressRunLengthData word).isSignedList_expand_iff]
  simpa using hword

end RunLengthData

/-- Canonical run-length data satisfying signed admissibility. -/
abbrev SignedRunLengthData (q p : ℕ) :=
  {data : RunLengthData (SignedLetter q p) // data.IsSigned}

/-- Admissible signed lists are equivalent to canonical signed run-length
data. -/
def signedRunLengthEquiv (q p : ℕ) :
    {word : List (SignedLetter q p) // IsSignedList word} ≃
      SignedRunLengthData q p :=
  (runLengthEquiv (SignedLetter q p)).subtypeEquiv fun word => by
    change IsSignedList word ↔ (compressRunLengthData word).IsSigned
    simpa using
      (RunLengthData.isSignedList_expand_iff
        (compressRunLengthData word))

/-- Every repeated canonical run of an admissible finite-function word has a
negative representative. -/
theorem compress_ofFn_repeated_isNegative {q p n : ℕ}
    (word : Fin n → SignedLetter q p) (hword : IsSignedWord n word)
    {run : SignedLetter q p × ℕ}
    (hrun : run ∈ (compressRunLengthData (List.ofFn word)).runs)
    (hrepeated : 1 < run.2) :
    run.1.IsNegative := by
  exact RunLengthData.compress_repeated_isNegative
    ((isSignedList_ofFn_iff word).mpr hword) hrun hrepeated

end RealRooted.BrandenVecchi
