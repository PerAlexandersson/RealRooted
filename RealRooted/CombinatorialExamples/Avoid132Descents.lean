import RealRooted.Mathlib.Combinatorics.Enumerative.SimionSchmidt
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.Mathlib.Combinatorics.Enumerative.DyckStatistics
import RealRooted.NarayanaTransformation.Recurrences.Interlacing
import RealRooted.NarayanaTransformation.Endpoints

/-!
# Descents of `132`-avoiding permutations

The number of `132`-avoiding permutations of `n + 1` letters with `k` descents is the Narayana
number `Nat.narayana (n + 1) (k + 1)`.  Hence their descent polynomial is the Narayana
polynomial `narayanaPolynomial 1 n`, which is real-rooted, and consecutive ones strictly
interlace.

The proof encodes permutations as lists, decomposes a `132`-avoider at its largest letter
(`σ = L ++ [max] ++ R`, every letter of `L` exceeding every letter of `R`, and
`des σ = des L + des R + [R ≠ []]`), turns the resulting recurrence into the functional equation
`U = x (1 + U) (1 + t U)`, and extracts coefficients by an explicit Lagrange-type formula.
All of this is private; the public interface is stated for the staging API
`Equiv.Perm.avoiders` and `Equiv.Perm.descentCount`.
-/

open Finset Polynomial
open RealRooted.SimionSchmidt (Avoids132)

namespace RealRooted
namespace Avoid132

/-- Number of descents: positions `i` with `σ i > σ (i + 1)`. -/
private def descents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ ⟨i.val + 1, h⟩ < σ i).card

/-- 132-avoiding permutations of `Fin n` with exactly `k` descents. -/
private def A (n k : ℕ) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) => Avoids132 σ ∧ descents σ = k).card


/-- Descents of a list of naturals. -/
private def ldes : List ℕ → ℕ
  | a :: b :: t => (if b < a then 1 else 0) + ldes (b :: t)
  | _ => 0

/-- 132-avoidance for a list of naturals. -/
private def lavoid : List ℕ → Prop
  | [] => True
  | a :: t => t.Pairwise (fun b c => ¬ (a < c ∧ c < b)) ∧ lavoid t

private instance lavoid.decidable : DecidablePred lavoid := fun l => by
  induction l with
  | nil => unfold lavoid; infer_instance
  | cons a t ih => unfold lavoid; infer_instance

private lemma ldes_cons_cons (a b : ℕ) (t : List ℕ) :
    ldes (a :: b :: t) = (if b < a then 1 else 0) + ldes (b :: t) := rfl

private lemma ldes_le_length (l : List ℕ) : ldes l ≤ l.length := by
  induction l with
  | nil => simp [ldes]
  | cons a t ih =>
    cases t with
    | nil => simp [ldes]
    | cons b t => rw [ldes_cons_cons]; simp only [List.length_cons] at *; split_ifs <;> lia

private lemma ldes_append_cons {s t : List ℕ} {b : ℕ} (hs : ∀ x ∈ s, x < b) :
    ldes (s ++ b :: t) = ldes s + ldes (b :: t) := by
  induction s with
  | nil => simp [ldes]
  | cons x s ih =>
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons_append]
      have hxb := hs x (by simp)
      simp only [ldes_cons_cons, not_lt.2 hxb.le, ↓reduceIte]
      simp [ldes]
    | cons y s =>
      simp only [List.cons_append] at *
      rw [ldes_cons_cons, ih (fun z hz => hs z (List.mem_cons_of_mem _ hz)), ldes_cons_cons]
      ring

private lemma ldes_cons_top {t : List ℕ} {b : ℕ} (ht : ∀ x ∈ t, x < b) :
    ldes (b :: t) = ldes t + (if t = [] then 0 else 1) := by
  cases t with
  | nil => simp [ldes]
  | cons y t =>
    simp only [ldes_cons_cons, ht y (by simp), ↓reduceIte, reduceCtorEq]
    lia

private lemma ldes_map_add (c : ℕ) (s : List ℕ) : ldes (s.map (· + c)) = ldes s := by
  induction s with
  | nil => simp [ldes]
  | cons x s ih =>
    cases s with
    | nil => simp [ldes]
    | cons y s =>
      simp only [List.map_cons] at *
      rw [ldes_cons_cons, ih, ldes_cons_cons]
      simp

private lemma lavoid_map_add (c : ℕ) (s : List ℕ) : lavoid (s.map (· + c)) ↔ lavoid s := by
  induction s with
  | nil => simp [lavoid]
  | cons x s ih =>
    simp only [List.map_cons, lavoid, ih, List.pairwise_map]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩ <;>
      refine h1.imp ?_ <;> intro a b h <;> lia

private lemma lavoid_append_top {s t : List ℕ} {b : ℕ} (hs : ∀ x ∈ s, x < b) (ht : ∀ x ∈ t, x < b) :
    lavoid (s ++ b :: t) ↔ lavoid s ∧ lavoid t ∧ ∀ x ∈ s, ∀ y ∈ t, y ≤ x := by
  induction s with
  | nil =>
    simp only [List.nil_append, lavoid, List.not_mem_nil, false_implies, implies_true, and_true,
      true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      exact List.Pairwise.imp_of_mem (R := fun _ _ => True) (fun {a c} ha hc _ => by
        have := ht c hc; have := ht a ha; lia) (List.pairwise_of_forall (fun _ _ => trivial))
  | cons x s ih =>
    have hs' : ∀ z ∈ s, z < b := fun z hz => hs z (List.mem_cons_of_mem _ hz)
    have hxb : x < b := hs x (by simp)
    simp only [List.cons_append, lavoid, ih hs', List.pairwise_append, List.pairwise_cons,
      List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, ⟨h2, h3⟩, h4⟩, h5, h6, h7⟩
      refine ⟨⟨h1, h5⟩, h6, ?_, h7⟩
      intro y hy
      have := h2 y hy; have := ht y hy; lia
    · rintro ⟨⟨h1, h5⟩, h6, h8, h7⟩
      refine ⟨⟨h1, ⟨?_, ?_⟩, ?_⟩, h5, h6, h7⟩
      · intro y hy; have := h8 y hy; lia
      · exact List.Pairwise.imp_of_mem (R := fun _ _ => True) (fun {a c} ha hc _ => by
          have := h8 c hc; lia) (List.pairwise_of_forall (fun _ _ => trivial))
      · intro a ha
        refine ⟨by have := hs' a ha; lia, ?_⟩
        intro c hc; have := h8 c hc; lia

private lemma append_cons_cancel {s s' t t' : List ℕ} {m : ℕ} (hs : m ∉ s) (hs' : m ∉ s')
    (h : s ++ m :: t = s' ++ m :: t') : s = s' ∧ t = t' := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil => simpa using h
    | cons y s' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hs'
  | cons x s ih =>
    cases s' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hs
    | cons y s' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have := ih (fun hm => hs (List.mem_cons_of_mem _ hm))
        (fun hm => hs' (List.mem_cons_of_mem _ hm)) h.2
      exact ⟨by rw [h.1, this.1], this.2⟩

private lemma perm_range_of_lt {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < L.length) :
    L.Perm (List.range L.length) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hnd (List.nodup_range)
  apply Finset.eq_of_subset_of_card_le
  · intro x hx; simp only [List.mem_toFinset, List.mem_range] at *; exact hlt x hx
  · rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup List.nodup_range]; simp

private lemma ldes_ofFn : ∀ (n : ℕ) (f : Fin n → ℕ),
    ldes (List.ofFn f) =
      (univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, f ⟨i.val + 1, h⟩ < f i).card
  | 0, f => by simp [ldes]
  | 1, f => by
    simp only [List.ofFn_succ, List.ofFn_zero, ldes]
    symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i _ ⟨h, _⟩; lia
  | n + 2, f => by
    have h := ldes_ofFn (n+1) (fun i => f i.succ)
    rw [List.ofFn_succ] at h
    rw [List.ofFn_succ, List.ofFn_succ, ldes_cons_cons, h,
      Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ (n := n + 1)]
    congr 1
    · exact if_congr ⟨fun h => ⟨by lia, h⟩, fun h => h.2⟩ rfl rfl
    · apply Finset.sum_congr rfl
      intro i _
      apply if_congr _ rfl rfl
      simp only [Fin.val_succ]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨by lia, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨by lia, h'⟩

private lemma lavoid_ofFn : ∀ (n : ℕ) (f : Fin n → ℕ),
    lavoid (List.ofFn f) ↔ ∀ i j k : Fin n, i < j → j < k → ¬ (f i < f k ∧ f k < f j)
  | 0, f => by simp [lavoid]
  | n + 1, f => by
    rw [List.ofFn_succ, lavoid, lavoid_ofFn n, List.pairwise_ofFn]
    simp only [Fin.forall_fin_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, Fin.succ_pos,
      false_implies, implies_true, true_implies, true_and]

/-- Permutation lists of `range n`. -/
private def S (n : ℕ) : Finset (List ℕ) := (List.range n).permutations.toFinset

private lemma mem_S {n : ℕ} {L : List ℕ} : L ∈ S n ↔ L.Perm (List.range n) := by
  simp [S, List.mem_permutations]

/-- 132-avoiding permutation lists of `range n` with `k` descents. -/
private def Xs (n k : ℕ) : Finset (List ℕ) := (S n).filter fun L => lavoid L ∧ ldes L = k

private lemma A_eq_card_Xs (n k : ℕ) : A n k = (Xs n k).card := by
  unfold A Xs
  apply Finset.card_bij (fun σ _ => List.ofFn (fun i => ((σ i : Fin n) : ℕ)))
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_filter, mem_S]
    refine ⟨?_, ?_, ?_⟩
    · have hnd : (List.ofFn (fun i => ((σ i : Fin n) : ℕ))).Nodup := by
        rw [List.nodup_ofFn]
        intro i j h; exact σ.injective (Fin.ext h)
      have := perm_range_of_lt hnd (by
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        simp)
      simpa using this
    · rw [lavoid_ofFn]; exact fun i j k hij hjk => by
        exact hσ.1 i j k hij hjk
    · rw [ldes_ofFn, ← hσ.2]; rfl
  · intro σ _ τ _ h
    have := List.ofFn_injective h
    ext i
    exact congrFun this i
  · intro L hL
    simp only [Finset.mem_filter, mem_S] at hL
    obtain ⟨hp, hav, hdes⟩ := hL
    have hlen : L.length = n := by simpa using hp.length_eq
    have hnd : L.Nodup := hp.nodup_iff.2 List.nodup_range
    have hlt : ∀ i : Fin n, L.get (i.cast hlen.symm) < n := by
      intro i
      have := hp.subset (List.get_mem L (i.cast hlen.symm))
      simpa using this
    let f : Fin n → Fin n := fun i => ⟨L.get (i.cast hlen.symm), hlt i⟩
    have hf : Function.Injective f := by
      intro i j h
      simp only [f, Fin.mk.injEq] at h
      have := (hnd.get_inj_iff).1 h
      ext; simpa using congrArg Fin.val this
    let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
    have hσ : List.ofFn (fun i => ((σ i : Fin n) : ℕ)) = L := by
      apply List.ext_get (by simp [hlen])
      intro i h1 h2
      simp [σ, f]
    refine ⟨σ, ?_, hσ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hσ] at hav hdes
    rw [lavoid_ofFn] at hav
    refine ⟨fun i j k hij hjk => hav i j k hij hjk, ?_⟩
    rw [← hdes, ldes_ofFn]; rfl

/-- Right blocks, counted with the extra descent coming from the maximum in front. -/
private def Xs' (l i : ℕ) : Finset (List ℕ) :=
  (S l).filter fun L => lavoid L ∧ ldes L + (if l = 0 then 0 else 1) = i

private lemma lt_of_mem_S {n : ℕ} {L : List ℕ} (h : L ∈ S n) {x : ℕ} (hx : x ∈ L) : x < n := by
  rw [mem_S] at h; simpa using h.subset hx

private lemma length_of_mem_S {n : ℕ} {L : List ℕ} (h : L ∈ S n) : L.length = n := by
  rw [mem_S] at h; simpa using h.length_eq

private lemma nodup_of_mem_S {n : ℕ} {L : List ℕ} (h : L ∈ S n) : L.Nodup := by
  rw [mem_S] at h; exact h.nodup_iff.2 List.nodup_range

private lemma decomp (m k : ℕ) :
    (Xs (m+1) k).card = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal k,
      (Xs p.1 q.1).card * (Xs' p.2 q.2).card := by
  have hsum : ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal k, (Xs p.1 q.1).card * (Xs' p.2 q.2).card
      = (((antidiagonal m) ×ˢ (antidiagonal k)).sigma
          (fun pq => Xs pq.1.1 pq.2.1 ×ˢ Xs' pq.1.2 pq.2.2)).card := by
    rw [Finset.card_sigma, Finset.sum_product]; simp [Finset.card_product]
  rw [hsum]; symm
  apply Finset.card_bij (fun a _ => a.2.1.map (· + a.1.1.2) ++ m :: a.2.2)
  · rintro ⟨⟨⟨j, l⟩, ⟨i, i'⟩⟩, ⟨L1, L2⟩⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
      Xs, Xs', Finset.mem_filter] at ha
    obtain ⟨⟨hjl, hii⟩, ⟨hL1, hav1, hd1⟩, ⟨hL2, hav2, hd2⟩⟩ := ha
    have h1 : ∀ x ∈ L1, x < j := fun x hx => lt_of_mem_S hL1 hx
    have h2 : ∀ x ∈ L2, x < l := fun x hx => lt_of_mem_S hL2 hx
    have hmap : ∀ x ∈ L1.map (· + l), l ≤ x ∧ x < m := by
      intro x hx; simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx; have := h1 y hy; lia
    have hs : ∀ x ∈ L1.map (· + l), x < m := fun x hx => (hmap x hx).2
    have ht : ∀ x ∈ L2, x < m := fun x hx => by have := h2 x hx; lia
    simp only [Xs, Finset.mem_filter, mem_S]
    refine ⟨?_, ?_, ?_⟩
    · have hlen : (L1.map (· + l) ++ m :: L2).length = m + 1 := by
        rw [List.length_append, List.length_map, List.length_cons, length_of_mem_S hL1,
          length_of_mem_S hL2]
        lia
      rw [← hlen]
      apply perm_range_of_lt
      · rw [List.nodup_append, List.nodup_cons]
        refine ⟨(nodup_of_mem_S hL1).map (add_left_injective l),
          ⟨fun h => lt_irrefl _ (ht m h), nodup_of_mem_S hL2⟩, ?_⟩
        intro a ha b hb
        have := hmap a ha
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · lia
        · have := h2 b hb; lia
      · rw [hlen]; intro x hx; simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · have := hs x hx; lia
        · lia
        · have := ht x hx; lia
    · rw [lavoid_append_top hs ht, lavoid_map_add]
      refine ⟨hav1, hav2, fun x hx y hy => ?_⟩
      have := (hmap x hx).1; have := h2 y hy; lia
    · rw [ldes_append_cons hs, ldes_map_add, ldes_cons_top ht]
      have : (L2 = []) ↔ l = 0 := by rw [← List.length_eq_zero_iff, length_of_mem_S hL2]
      simp only [this]; lia
  · rintro ⟨⟨⟨j, l⟩, ⟨i, i'⟩⟩, ⟨L1, L2⟩⟩ ha ⟨⟨⟨j', l'⟩, ⟨i2, i2'⟩⟩, ⟨L1', L2'⟩⟩ ha' h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
      Xs, Xs', Finset.mem_filter] at ha ha'
    obtain ⟨⟨hjl, hii⟩, ⟨hL1, hav1, hd1⟩, ⟨hL2, hav2, hd2⟩⟩ := ha
    obtain ⟨⟨hjl', hii'⟩, ⟨hL1', hav1', hd1'⟩, ⟨hL2', hav2', hd2'⟩⟩ := ha'
    simp only at h
    have hm1 : m ∉ L1.map (· + l) := by
      intro hm; simp only [List.mem_map] at hm
      obtain ⟨y, hy, hy'⟩ := hm; have := lt_of_mem_S hL1 hy; lia
    have hm2 : m ∉ L1'.map (· + l') := by
      intro hm; simp only [List.mem_map] at hm
      obtain ⟨y, hy, hy'⟩ := hm; have := lt_of_mem_S hL1' hy; lia
    obtain ⟨e1, e2⟩ := append_cons_cancel hm1 hm2 h
    subst e2
    have hll : l = l' := by rw [← length_of_mem_S hL2, ← length_of_mem_S hL2']
    subst hll
    have hjj : j = j' := by lia
    subst hjj
    have e3 : L1 = L1' := (List.map_injective_iff.2 (add_left_injective l)) e1
    subst e3
    have : i = i2 := by rw [← hd1, ← hd1']
    subst this
    have : i' = i2' := by lia
    subst this; rfl
  · intro L hL
    simp only [Xs, Finset.mem_filter, mem_S] at hL
    obtain ⟨hp, hav, hdes⟩ := hL
    have hnd : L.Nodup := hp.nodup_iff.2 List.nodup_range
    have hlt : ∀ x ∈ L, x < m + 1 := fun x hx => by simpa using hp.subset hx
    have hmem : ∀ x < m + 1, x ∈ L := fun x hx => hp.symm.subset (by simpa using hx)
    obtain ⟨s, t, rfl⟩ := List.append_of_mem (hmem m (by lia))
    have hnd' := hnd
    rw [List.nodup_append, List.nodup_cons] at hnd'
    obtain ⟨hnds, ⟨hmt, hndt⟩, hdisj⟩ := hnd'
    have hms : m ∉ s := fun h => hdisj m h m (by simp) rfl
    have hs : ∀ x ∈ s, x < m := fun x hx => by
      have := hlt x (by simp [hx]); have : x ≠ m := fun e => hms (e ▸ hx); lia
    have ht : ∀ x ∈ t, x < m := fun x hx => by
      have := hlt x (by simp [hx]); have : x ≠ m := fun e => hmt (e ▸ hx); lia
    rw [lavoid_append_top hs ht] at hav
    obtain ⟨havs, havt, hst⟩ := hav
    have hst' : ∀ x ∈ s, ∀ y ∈ t, y < x := fun x hx y hy =>
      lt_of_le_of_ne (hst x hx y hy) (fun e => hdisj x hx y (by simp [hy]) e.symm)
    have hjl : s.length + t.length = m := by
      have := hp.length_eq
      rw [List.length_append, List.length_cons, List.length_range] at this
      lia
    have htl : ∀ y ∈ t, y < t.length := by
      intro y hy
      have hsub : Finset.range (y+1) ⊆ t.toFinset := by
        intro z hz; rw [Finset.mem_range] at hz; rw [List.mem_toFinset]
        have hzL := hmem z (by have := ht y hy; lia)
        simp only [List.mem_append, List.mem_cons] at hzL
        rcases hzL with hz' | rfl | hz'
        · have := hst' z hz' y hy; lia
        · have := ht y hy; lia
        · exact hz'
      have := Finset.card_le_card hsub
      rw [Finset.card_range, List.toFinset_card_of_nodup hndt] at this; lia
    have htp : t.Perm (List.range t.length) := perm_range_of_lt hndt htl
    have hsl : ∀ x ∈ s, t.length ≤ x := by
      intro x hx; by_contra hlt'; push Not at hlt'
      have : x ∈ t := htp.symm.subset (by simpa using hlt')
      exact hdisj x hx x (by simp [this]) rfl
    have hss : (s.map (· - t.length)).map (· + t.length) = s := by
      rw [List.map_map]; conv_rhs => rw [← List.map_id s]
      apply List.map_congr_left; intro x hx; simp only [Function.comp_apply, id]
      have := hsl x hx; lia
    have hnds' : (s.map (· - t.length)).Nodup := hnds.map_on (fun x hx y hy e => by
      have := hsl x hx; have := hsl y hy; lia)
    have hs'p : (s.map (· - t.length)).Perm (List.range s.length) := by
      have := perm_range_of_lt hnds' (by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
        have := hs y hy; have := hsl y hy; simp only [List.length_map]; lia)
      simpa using this
    refine ⟨⟨((s.length, t.length), (ldes (s.map (· - t.length)),
      ldes t + (if t.length = 0 then 0 else 1))), (s.map (· - t.length), t)⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
        Xs, Xs', Finset.mem_filter, mem_S]
      refine ⟨⟨hjl, ?_⟩, ⟨hs'p, ?_, trivial⟩, ⟨htp, havt, trivial⟩⟩
      · have hds : ldes s = ldes (s.map (· - t.length)) := by
          conv_lhs => rw [← hss]
          exact ldes_map_add _ _
        rw [← hdes, ldes_append_cons hs, hds, ldes_cons_top ht]
        have : (t = []) ↔ t.length = 0 := List.length_eq_zero_iff.symm
        simp only [this]
      · rw [← lavoid_map_add t.length, hss]; exact havs
    · simp only; rw [hss]

/-! ### The algebraic side: Lagrange-inversion closed form -/

/-- Coefficient of `t^k` in the closed form of `[x^n] U^r`. -/
private noncomputable def g (n r k : ℕ) : ℚ := (r : ℚ) / n * (n.choose k) * (n.choose (r + k))

private lemma alg_id (a b c d n s k : ℚ) (R1 : a * (n + 1) = (a + b) * (k + 1))
    (R2 : c * (n + 1) = (c + d) * (s + k + 2)) (hd : s + k + 2 = n + 1 → d = 0) :
    (s + 1) * n * (a + b) * (c + d) =
      (n + 1) * (s * b * c + (s + 1) * b * d + (s + 1) * a * c + (s + 2) * a * d) := by
  by_cases h : s+k+2 = n+1
  · have h0 := hd h
    subst h0
    have hn : n = s + k + 1 := by linarith
    subst hn
    linear_combination (-c) * R1
  · have hne : n + 1 - (s+k+2) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have : (n+1-(s+k+2)) * ((s+1)*n*(a+b)*(c+d) -
        (n+1)*(s*b*c + (s+1)*b*d + (s+1)*a*c + (s+2)*a*d)) = 0 := by
      linear_combination (-1) * (((n+1-(s+1+(k+1)))*d + (s+1+(k+1))*d) * R1 +
        (-(n+1-(s+1+(k+1)))*b + ((s+1)*a - (k+1)*b)) * R2)
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hne
    · linear_combination h'

private lemma choose_rel (n k : ℕ) :
    (n.choose k : ℚ) * (n+1) = (n.choose k + n.choose (k+1)) * (k+1) := by
  have := Nat.add_one_mul_choose_eq n k
  rw [Nat.choose_succ_succ] at this
  have h : (n.choose k) * (n+1) = (n.choose k + n.choose (k+1)) * (k+1) := by linarith [this]
  exact_mod_cast h

private lemma g_rec_succ (n s k : ℕ) (hn : 1 ≤ n) :
    g (n+1) (s+1) (k+1) = g n s (k+1) + g n (s+1) (k+1) + g n (s+1) k + g n (s+2) k := by
  unfold g
  obtain ⟨j, hj⟩ : ∃ j, j = s + 1 + k := ⟨_, rfl⟩
  rw [show s + 1 + (k+1) = j + 1 by lia, show s + (k+1) = j by lia,
    show s + 1 + k = j by lia, show s + 2 + k = j + 1 by lia, Nat.choose_succ_succ n k,
    Nat.choose_succ_succ n j]
  have R1 := choose_rel n k
  have R2 := choose_rel n j
  rw [show ((j:ℕ):ℚ) + 1 = s + k + 2 by rw [hj]; push_cast; ring] at R2
  have hE := alg_id _ _ _ _ _ _ _ R1 R2 (by
    intro h
    have h' : s + k + 2 = n + 1 := by exact_mod_cast h
    rw [Nat.choose_eq_zero_of_lt (by lia)]; simp)
  have hn' : (n:ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination hE

private lemma g_rec_zero (n s : ℕ) (hn : 1 ≤ n) : g (n+1) (s+1) 0 = g n s 0 + g n (s+1) 0 := by
  unfold g
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [Nat.choose_succ_succ n s]
  have R := choose_rel n s
  have hn' : (n:ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination R

/-- Closed form for the coefficient `[x^n] U^r`, as a polynomial in `t`. -/
private noncomputable def Cf (n r : ℕ) : ℚ[X] :=
  if n = 0 then (if r = 0 then 1 else 0) else ∑ k ∈ range (n+1), C (g n r k) * X^k

private lemma coeff_Cf {n : ℕ} (hn : n ≠ 0) (r k : ℕ) : (Cf n r).coeff k = g n r k := by
  simp only [Cf, hn, ↓reduceIte, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [Finset.mem_range, not_lt] at h
    unfold g; rw [Nat.choose_eq_zero_of_lt (by lia)]; simp

private lemma Cf_rec (n r : ℕ) :
    Cf (n+1) (r+1) = Cf n r + (1 + X) * Cf n (r+1) + X * Cf n (r+2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext k
    rw [coeff_Cf (by norm_num)]
    simp only [Cf, ite_true, add_eq_zero, one_ne_zero, and_false, ite_false, mul_zero, add_zero]
    rcases k with _ | _ | k <;> rcases r with _ | r <;>
      simp [g, coeff_one, Nat.choose_eq_zero_of_lt]
  · ext k
    simp only [coeff_add, add_mul, one_mul]
    rw [coeff_Cf (by lia), coeff_Cf (by lia), coeff_Cf (by lia)]
    rcases k with _ | k
    · simp only [coeff_X_mul_zero, add_zero]
      exact g_rec_zero n r hn
    · rw [coeff_X_mul, coeff_X_mul, coeff_Cf (by lia), coeff_Cf (by lia),
        g_rec_succ n r k hn]
      ring

/-! ### From the combinatorial recurrence to power series -/

private lemma S_zero : S 0 = {[]} := by simp [S]

private lemma card_Xs_zero (k : ℕ) : (Xs 0 k).card = if k = 0 then 1 else 0 := by
  unfold Xs; rw [S_zero]
  split_ifs with h
  · subst h; rw [Finset.card_eq_one]
    refine ⟨[], ?_⟩
    ext L; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, trivial, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro L hL; simp only [Finset.mem_singleton] at hL; subst hL
    simp [ldes, Ne.symm h]

private lemma card_Xs_eq_zero {n k : ℕ} (h : n < k) : (Xs n k).card = 0 := by
  rw [Xs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro L hL ⟨_, hd⟩
  have := ldes_le_length L
  rw [length_of_mem_S hL] at this; lia

private lemma card_Xs'_zero (i : ℕ) : (Xs' 0 i).card = (Xs 0 i).card := by
  unfold Xs' Xs; simp

private lemma card_Xs'_succ (l i : ℕ) :
    (Xs' (l+1) i).card = if i = 0 then 0 else (Xs (l+1) (i-1)).card := by
  unfold Xs' Xs
  simp only [add_eq_zero, one_ne_zero, and_false, ite_false]
  split_ifs with h
  · subst h; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro L _; simp
  · congr 1; apply Finset.filter_congr; intro L _; exact and_congr_right (fun _ => by lia)

/-- Descent polynomial of 132-avoiding permutation lists of length `n`. -/
private noncomputable def P (n : ℕ) : ℚ[X] := ∑ k ∈ range (n+1), C ((Xs n k).card : ℚ) * X^k

private lemma coeff_P (n k : ℕ) : (P n).coeff k = (Xs n k).card := by
  rw [P, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp only [Finset.mem_range, not_lt] at h
    rw [card_Xs_eq_zero (by lia)]; simp

private lemma P_zero : P 0 = 1 := by
  ext k; rw [coeff_P, card_Xs_zero, coeff_one]
  split_ifs <;> simp_all

/-- Descent polynomial of the right block (including the descent out of the maximum). -/
private noncomputable def Q (l : ℕ) : ℚ[X] := if l = 0 then 1 else X * P l

private lemma coeff_Q (l i : ℕ) : (Q l).coeff i = (Xs' l i).card := by
  rcases l with _ | l
  · simp only [Q, ↓reduceIte]
    rw [card_Xs'_zero, card_Xs_zero, coeff_one]
    split_ifs <;> simp_all
  · have hl : l + 1 ≠ 0 := by lia
    simp only [Q, hl, ↓reduceIte]
    rw [card_Xs'_succ]
    rcases i with _ | i
    · simp
    · rw [coeff_X_mul, coeff_P]; simp

private lemma P_succ (m : ℕ) : P (m+1) = ∑ p ∈ antidiagonal m, P p.1 * Q p.2 := by
  ext k
  rw [coeff_P, decomp, finsetSum_coeff]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [coeff_P, coeff_Q]

/-- The generating function `U = Σ_{n ≥ 1} P n x^n`. -/
private noncomputable def U : PowerSeries ℚ[X] := PowerSeries.mk P - 1

private lemma U_eq : U = PowerSeries.X * ((1 + U) * (1 + PowerSeries.C (X : ℚ[X]) * U)) := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [U, P_zero]
  · rw [PowerSeries.coeff_succ_X_mul, U, add_sub_cancel, PowerSeries.coeff_mul]
    simp only [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one, add_eq_zero, one_ne_zero,
      and_false, ite_false, sub_zero]
    rw [P_succ]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [map_add, PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one, Q]
    split_ifs with h
    · simp [h, P_zero]
    · simp

private lemma U_pow_succ (s : ℕ) :
    U^(s+1) = PowerSeries.X * (U^s + (1 + PowerSeries.C (X : ℚ[X])) * U^(s+1)
      + PowerSeries.C (X : ℚ[X]) * U^(s+2)) := by
  calc U^(s+1) = U^s * U := pow_succ _ _
    _ = U^s * (PowerSeries.X * ((1 + U) * (1 + PowerSeries.C (X : ℚ[X]) * U))) := by rw [← U_eq]
    _ = _ := by ring

private lemma coeff_U_pow (n : ℕ) : ∀ r, PowerSeries.coeff n (U ^ r) = Cf n r := by
  induction n with
  | zero =>
    intro r
    rcases r with _ | s
    · simp [Cf]
    · rw [U_pow_succ, PowerSeries.coeff_zero_X_mul]; simp [Cf]
  | succ n ih =>
    intro r
    rcases r with _ | s
    · simp [Cf, g]
    · rw [U_pow_succ, PowerSeries.coeff_succ_X_mul, map_add, map_add, add_mul, one_mul, map_add,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, ih, ih, ih, Cf_rec]
      ring


private theorem narayana_A (n k : ℕ) :
    (n + 1) * A (n + 1) k = Nat.choose (n + 1) (k + 1) * Nat.choose (n + 1) k := by
  have h1 : PowerSeries.coeff (n+1) U = P (n+1) := by simp [U]
  have h2 := coeff_U_pow (n+1) 1
  rw [pow_one, h1] at h2
  have h3 := congrArg (fun p => p.coeff k) h2
  rw [coeff_P, coeff_Cf (by lia)] at h3
  rw [A_eq_card_Xs]
  unfold g at h3
  have : ((n+1 : ℕ) : ℚ) * (Xs (n+1) k).card = ((n+1).choose (k+1) * (n+1).choose k : ℕ) := by
    rw [h3, add_comm 1 k]; push_cast; field_simp
  exact_mod_cast this

private lemma descents_eq_descentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    descents σ = σ.descentCount := by
  unfold descents
  rw [Equiv.Perm.descentCount_eq_list, List.descentCount]
  refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, h, hlt⟩ := hi
    rw [List.mem_descentSet]
    exact ⟨by simpa using h, by simpa using hlt⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro i hi
    rw [List.mem_descentSet] at hi
    obtain ⟨h, hlt⟩ := hi
    have hn : i + 1 < n := by simpa using h
    refine ⟨⟨i, by lia⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hn, by simpa using hlt⟩

private lemma mem_avoiders_p132_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ ∈ Equiv.Perm.avoiders n [⟨3, SimionSchmidt.p132⟩] ↔ Avoids132 σ := by
  rw [← SimionSchmidt.avoids_p132_iff]
  simp only [Equiv.Perm.avoiders, Finset.mem_filter, Finset.mem_univ, true_and,
    List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq, and_true]

private lemma card_filter_avoiders_eq (n k : ℕ) :
    ((Equiv.Perm.avoiders n [⟨3, SimionSchmidt.p132⟩]).filter
      (fun σ => σ.descentCount = k)).card = A n k := by
  unfold A
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_avoiders_p132_iff,
    descents_eq_descentCount]

/-- The number of `132`-avoiding permutations of `n + 1` letters with `k` descents is the
Narayana number: `(n + 1) * #{σ avoiding 132 | des σ = k} = C(n + 1, k + 1) * C(n + 1, k)`. -/
theorem succ_mul_card_avoiders_descentCount_eq (n k : ℕ) :
    (n + 1) * ((Equiv.Perm.avoiders (n + 1) [⟨3, SimionSchmidt.p132⟩]).filter
      (fun σ => σ.descentCount = k)).card =
        Nat.choose (n + 1) (k + 1) * Nat.choose (n + 1) k := by
  rw [card_filter_avoiders_eq]
  exact narayana_A n k

/-- The descent distribution of `132`-avoiding permutations is given by the Narayana
numbers `Nat.narayana (n + 1) (k + 1)`. -/
theorem card_avoiders_descentCount_eq_narayana (n k : ℕ) :
    ((Equiv.Perm.avoiders (n + 1) [⟨3, SimionSchmidt.p132⟩]).filter
      (fun σ => σ.descentCount = k)).card = Nat.narayana (n + 1) (k + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  rw [succ_mul_card_avoiders_descentCount_eq, Nat.narayana_mul (n + 1) (k + 1) n.succ_ne_zero
    k.succ_ne_zero, Nat.add_sub_cancel]

/-- The descent generating polynomial of the `132`-avoiding permutations of `n` letters. -/
noncomputable def descentGeneratingPolynomial (n : ℕ) : ℝ[X] :=
  Finset.genPoly (Equiv.Perm.avoiders n [⟨3, SimionSchmidt.p132⟩]) Equiv.Perm.descentCount

private lemma mul_succ_eq_of_succ_mul_eq {n k c : ℕ}
    (h : (n + 1) * c = Nat.choose (n + 1) (k + 1) * Nat.choose (n + 1) k) :
    c * (k + 1) = Nat.choose n k * Nat.choose (n + 1) k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  calc
    (n + 1) * (c * (k + 1)) = ((n + 1) * c) * (k + 1) := by ring
    _ = Nat.choose (n + 1) (k + 1) * Nat.choose (n + 1) k * (k + 1) := by rw [h]
    _ = (Nat.choose (n + 1) (k + 1) * (k + 1)) * Nat.choose (n + 1) k := by ring
    _ = ((n + 1) * Nat.choose n k) * Nat.choose (n + 1) k := by rw [Nat.add_one_mul_choose_eq]
    _ = (n + 1) * (Nat.choose n k * Nat.choose (n + 1) k) := by ring

private lemma card_mul_succ_eq (n k : ℕ) :
    ((Equiv.Perm.avoiders (n + 1) [⟨3, SimionSchmidt.p132⟩]).filter
      (fun σ => σ.descentCount = k)).card * (k + 1) = Nat.choose n k * Nat.choose (n + 1) k :=
  mul_succ_eq_of_succ_mul_eq (succ_mul_card_avoiders_descentCount_eq n k)

/-- The descent polynomial of the `132`-avoiders of `n + 1` letters is the Narayana polynomial
`narayanaPolynomial 1 n`, with coefficients `C(n, k) C(n + 1, k) / (k + 1)`. -/
theorem descentGeneratingPolynomial_succ_eq_narayanaPolynomial (n : ℕ) :
    descentGeneratingPolynomial (n + 1) = narayanaPolynomial 1 n := by
  ext k
  unfold descentGeneratingPolynomial
  rw [Finset.coeff_genPoly]
  by_cases hk : k ≤ n
  · rw [coeff_narayanaPolynomial_of_le hk, narayanaTransformCoeff]
    have hden : (Nat.choose (1 + k) k : ℝ) = k + 1 := by
      rw [add_comm, Nat.choose_succ_self_right]
      push_cast
      ring
    rw [hden, eq_div_iff (by positivity)]
    exact_mod_cast card_mul_succ_eq n k
  · rw [coeff_narayanaPolynomial_of_lt (Nat.lt_of_not_ge hk)]
    have hc : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    have h0 := card_mul_succ_eq n k
    rw [hc, zero_mul] at h0
    have h1 : ((Equiv.Perm.avoiders (n + 1) [⟨3, SimionSchmidt.p132⟩]).filter
      (fun σ => σ.descentCount = k)).card = 0 := by
      lia
    rw [h1, Nat.cast_zero]

/-- The descent generating polynomial of the `132`-avoiding permutations is real-rooted. -/
theorem isRealRooted_descentGeneratingPolynomial_succ (n : ℕ) :
    descentGeneratingPolynomial (n + 1) ≠ 0 ∧ (descentGeneratingPolynomial (n + 1)).Splits := by
  rw [descentGeneratingPolynomial_succ_eq_narayanaPolynomial]
  exact ⟨narayanaPolynomial_ne_zero 1 n, splits_narayanaPolynomial 1 n⟩

/-- The descent polynomials of the `132`-avoiders of `n + 2` and `n + 3` letters strictly
interlace. -/
theorem strictInterl_descentGeneratingPolynomial_succ (n : ℕ) :
    StrictInterl (descentGeneratingPolynomial (n + 2)) (descentGeneratingPolynomial (n + 3)) := by
  rw [descentGeneratingPolynomial_succ_eq_narayanaPolynomial (n + 1),
    descentGeneratingPolynomial_succ_eq_narayanaPolynomial (n + 2)]
  exact strictInterl_narayanaPolynomial_succ 1 n

end Avoid132
end RealRooted
