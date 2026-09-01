import RealRooted.Basic

/-!
# Interlacing and root multiplicities

Duplicate roots in the upper row of an interlacing pair force a common root.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem interlaces_dup_mem {ss rs : List ℝ} (hrs : rs.Pairwise (· ≤ ·))
    (hint : ListInterlaces ss rs) (hnd : ¬ rs.Nodup) :
    ∃ r ∈ rs, r ∈ ss := by
  induction ss generalizing rs with
  | nil =>
    match rs with
    | [] => simp at hnd
    | [r] => simp at hnd
    | r₁ :: r₂ :: rest => simp [ListInterlaces] at hint
  | cons s ss ih =>
    match rs with
    | [] => simp at hnd
    | [r] => simp at hnd
    | r₁ :: r₂ :: rest =>
      obtain ⟨h₁, h₂, htail⟩ := hint
      rw [List.pairwise_cons] at hrs
      obtain ⟨h_r₁_le, h_rs_tail⟩ := hrs
      by_cases h_r₁_r₂ : r₁ = r₂
      · have h₂' : s ≤ r₁ := h_r₁_r₂ ▸ h₂
        have h_s_r₁ : s = r₁ := le_antisymm h₂' h₁
        simp [*]
      · have h_r₁_lt : r₁ < r₂ :=
          lt_of_le_of_ne (h_r₁_le r₂ (by simp)) h_r₁_r₂
        rw [List.pairwise_cons] at h_rs_tail
        obtain ⟨h_r₂_le, hrest⟩ := h_rs_tail
        have h_r₁_notin : r₁ ∉ r₂ :: rest := by
          intro hmem
          rcases List.mem_cons.mp hmem with rfl | hm
          · simp_all
          · exact absurd (h_r₂_le r₁ hm) (not_le.mpr h_r₁_lt)
        have h_dup_tail : ¬ (r₂ :: rest).Nodup := fun hnod ↦
          hnd (List.nodup_cons.mpr ⟨h_r₁_notin, hnod⟩)
        obtain ⟨r, h_r_mem, h_r_ss⟩ :=
          ih (List.pairwise_cons.mpr ⟨h_r₂_le, hrest⟩) htail h_dup_tail
        exact ⟨r, List.mem_cons_of_mem r₁ h_r_mem, List.mem_cons_of_mem s h_r_ss⟩

theorem alternates_dup_mem {ss rs : List ℝ} (hrs : rs.Pairwise (· ≤ ·))
    (halt : ListAlternates ss rs) (hnd : ¬ rs.Nodup) :
    ∃ r ∈ rs, r ∈ ss := by
  match ss, rs with
  | [], [] => simp at hnd
  | [], r :: rs' => simp [ListAlternates] at halt
  | s :: ss', [] => simp at hnd
  | s :: ss', r :: rs' =>
    obtain ⟨h_s_r, htail⟩ := halt
    obtain ⟨x, h_x_mem, h_x_ss'⟩ := interlaces_dup_mem hrs htail hnd
    exact ⟨x, h_x_mem, List.mem_cons_of_mem s h_x_ss'⟩

theorem exists_common_root_of_not_nodup {f g : ℝ[X]} (hpq : Prec g f)
    (hnd : ¬ f.roots.Nodup) :
    ∃ r, r ∈ f.roots ∧ r ∈ g.roots := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  rw [← hrseq, Multiset.coe_nodup] at hnd
  have h_res : ∃ r ∈ rs, r ∈ ss := by
    rcases hshape with ⟨-, hint⟩ | ⟨-, halt⟩
    · exact interlaces_dup_mem hrs hint hnd
    · exact alternates_dup_mem hrs halt hnd
  obtain ⟨r, h_r_rs, h_r_ss⟩ := h_res
  exact ⟨r, by rw [← hrseq]; exact Multiset.mem_coe.mpr h_r_rs,
    by rw [← hsseq]; exact Multiset.mem_coe.mpr h_r_ss⟩

theorem interlaces_dup_mem_left {ss rs : List ℝ} (hss : ss.Pairwise (· ≤ ·))
    (hint : ListInterlaces ss rs) (hnd : ¬ ss.Nodup) :
    ∃ s ∈ ss, s ∈ rs := by
  induction ss generalizing rs with
  | nil => simp at hnd
  | cons s ss' ih =>
    match rs with
    | [] => simp [ListInterlaces] at hint
    | [r] => simp [ListInterlaces] at hint
    | r₁ :: r₂ :: rest =>
      obtain ⟨h₁, h₂, htail⟩ := hint
      rw [List.pairwise_cons] at hss
      obtain ⟨h_s_le, h_ss'⟩ := hss
      by_cases h_s_mem : s ∈ ss'
      · obtain ⟨s₀, ss₀, hss₀eq⟩ : ∃ s₀ ss₀, ss' = s₀ :: ss₀ := by
          cases ss' with
          | nil => simp at h_s_mem
          | cons a t => simp
        subst hss₀eq
        have h_r₂_s₀ : r₂ ≤ s₀ := by
          match rest with
          | [] => simp [ListInterlaces] at htail
          | r₃ :: rest' => exact htail.1
        rw [List.pairwise_cons] at h_ss'
        have h_s_s₀ : s = s₀ := by
          rcases List.mem_cons.mp h_s_mem with rfl | h_mem
          · rfl
          · exact le_antisymm (h_s_le s₀ List.mem_cons_self) (h_ss'.1 s h_mem)
        have h_s_r₂ : s = r₂ := le_antisymm h₂ (h_s_s₀ ▸ h_r₂_s₀)
        simp_all
      · have h_dup' : ¬ ss'.Nodup := fun hn ↦
          hnd (List.nodup_cons.mpr ⟨h_s_mem, hn⟩)
        obtain ⟨x, h_x_ss', h_x_rs⟩ := ih h_ss' htail h_dup'
        exact ⟨x, List.mem_cons_of_mem s h_x_ss', List.mem_cons_of_mem r₁ h_x_rs⟩

theorem alternates_dup_mem_left {ss rs : List ℝ} (hss : ss.Pairwise (· ≤ ·))
    (halt : ListAlternates ss rs) (hnd : ¬ ss.Nodup) :
    ∃ s ∈ ss, s ∈ rs := by
  match ss, rs with
  | [], [] => simp at hnd
  | s :: ss', [] => simp [ListAlternates] at halt
  | [], r :: rs' => simp at hnd
  | s :: ss', r :: rs' =>
    obtain ⟨h_s_r, htail⟩ := halt
    rw [List.pairwise_cons] at hss
    obtain ⟨h_s_le, h_ss'⟩ := hss
    by_cases h_s_mem : s ∈ ss'
    · obtain ⟨s₀, ss₀, rfl⟩ : ∃ s₀ ss₀, ss' = s₀ :: ss₀ := by
        cases ss' with | nil => simp at h_s_mem | cons a t => simp
      have h_r_s₀ : r ≤ s₀ := by
        match rs' with
        | [] => simp [ListInterlaces] at htail
        | r₂ :: rest => exact htail.1
      have h_s_s₀ : s = s₀ := by
        rcases List.mem_cons.mp h_s_mem with rfl | h_mem
        · rfl
        · rw [List.pairwise_cons] at h_ss'
          exact le_antisymm (h_s_le s₀ List.mem_cons_self) (h_ss'.1 s h_mem)
      have h_s_r' : s = r := le_antisymm h_s_r (h_s_s₀ ▸ h_r_s₀)
      simp_all
    · have h_dup' : ¬ ss'.Nodup := fun hn ↦
        hnd (List.nodup_cons.mpr ⟨h_s_mem, hn⟩)
      obtain ⟨x, h_x_ss', h_x_rs⟩ := interlaces_dup_mem_left h_ss' htail h_dup'
      exact ⟨x, List.mem_cons_of_mem s h_x_ss', h_x_rs⟩

theorem exists_common_root_of_not_nodup_g {f g : ℝ[X]} (hpq : Prec g f)
    (hnd : ¬ g.roots.Nodup) :
    ∃ r, r ∈ f.roots ∧ r ∈ g.roots := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  rw [← hsseq, Multiset.coe_nodup] at hnd
  have h_res : ∃ s ∈ ss, s ∈ rs := by
    rcases hshape with ⟨-, hint⟩ | ⟨-, halt⟩
    · exact interlaces_dup_mem_left hss hint hnd
    · exact alternates_dup_mem_left hss halt hnd
  obtain ⟨s, h_s_ss, h_s_rs⟩ := h_res
  exact ⟨s, by rw [← hrseq]; exact Multiset.mem_coe.mpr h_s_rs,
    by rw [← hsseq]; exact Multiset.mem_coe.mpr h_s_ss⟩

end RealRooted
