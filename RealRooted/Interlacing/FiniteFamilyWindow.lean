module

public import RealRooted.Interlacing.WindowInduction
import RealRooted.LiuWang.FiniteFamily

/-!
# Finite-family recurrence induction on an interlacing window

We combine `WindowInvariant.induction` with Liu--Wang's finite-family
criterion (Theorem 2.3 of *A unified approach to polynomial sequences with
only real zeros*, arXiv:math/0509207v5). This supplies the sequence-level
interface requested in RealRooted issue #1234, comment of 2026-11-09.

The window has arbitrary width and a fixed graph of directed edges. Old
edges shift within that graph; every new edge starts at a designated pivot
and ends at the new row. Both `StrictInterl` and differ-by-one `Interlaces`
edges are supported. The external degree law may have plateaus; only an
`Interlaces` edge requires an exact degree increase.

The finite family and its index set may vary with the rank. Thus a client
can include derivatives, lagged rows, or grouped terms, provided that it
proves their interlacing and positive leading signs from the window.
In particular, the derivative of a lagged row is not automatically an
admissible family member. Constant rows can be handled by omitting their
zero derivatives from the index set. Repeated roots are permitted: we use
the coefficientwise Liu--Wang hypotheses, not a simple-root flux test.
-/

public section

open Polynomial

namespace RealRooted.WindowInvariant

/-- A finite-family recurrence supplies the edge from a certified pivot
to the next row, allowing either a degree plateau or a degree increase. -/
theorem strictInterl_next_of_finite_family
    {ι : Type*} {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w pivot : ℕ}
    (h : WindowInvariant P degreeLaw E n w) (hpivot : pivot < w)
    {s : Finset ι} {a : ℝ[X]} {b g : ι → ℝ[X]}
    (hrec : P (n + w) = a * P (n + pivot) + ∑ i ∈ s, b i * g i)
    (hg : ∀ i ∈ s, StrictInterl (g i) (P (n + pivot)))
    (hgpos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, (P (n + pivot)).IsRoot r → (b i).eval r ≤ 0)
    (hpos : HasPosLeadingCoeff (P (n + w)))
    (hlo : degreeLaw (n + pivot) ≤ (P (n + w)).natDegree)
    (hhi : (P (n + w)).natDegree ≤ degreeLaw (n + pivot) + 1) :
    StrictInterl (P (n + pivot)) (P (n + w)) := by
  rw [hrec]
  exact LiuWang.strictInterl_mul_add_sum_mul_of_eval_nonpos
    (h.ne_zero pivot hpivot) (h.splits pivot hpivot) hg hgpos hb
    (hrec ▸ hpos) (by rw [← hrec, h.natDegree_eq pivot hpivot]; exact hlo)
    (by rw [← hrec, h.natDegree_eq pivot hpivot]; exact hhi)

/-- Append a row above a pivot and shift the old rows and edges. An old
edge is inherited at incremented offsets; every edge meeting the appended
row must have the pivot as source. Only differ-by-one edges need the final
degree equality. -/
private theorem succ_of_strictInterl_next
    {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w pivot : ℕ}
    (h : WindowInvariant P degreeLaw E n w) (hpivot : pivot < w)
    (hshift : ∀ e ∈ E, e.target + 1 < w →
      (⟨e.source + 1, e.target + 1, e.kind⟩ : WindowEdge) ∈ E)
    (hnew : ∀ e ∈ E, e.target + 1 = w → e.source + 1 = pivot)
    (hnext : StrictInterl (P (n + pivot)) (P (n + w)))
    (hpos : HasPosLeadingCoeff (P (n + w)))
    (hdegree : (P (n + w)).natDegree = degreeLaw (n + w))
    (hsucc : ∀ e ∈ E, e.target + 1 = w → e.kind = .interlaces →
      degreeLaw (n + w) = degreeLaw (n + pivot) + 1) :
    WindowInvariant P degreeLaw E (n + 1) w := by
  have hrow : ∀ i, i < w →
      P (n + 1 + i) ≠ 0 ∧ (P (n + 1 + i)).Splits ∧
        (P (n + 1 + i)).natDegree = degreeLaw (n + 1 + i) ∧
          HasPosLeadingCoeff (P (n + 1 + i)) := by
    intro i hi
    by_cases hlast : i + 1 = w
    · have heq : n + 1 + i = n + w := by lia
      rw [heq]
      exact ⟨hpos.ne_zero, hnext.2.1.2, hdegree, hpos⟩
    · have hlt : i + 1 < w := by lia
      have heq : n + 1 + i = n + (i + 1) := by lia
      rw [heq]
      exact ⟨h.ne_zero _ hlt, h.splits _ hlt, h.natDegree_eq _ hlt,
        h.posLeadingCoeff _ hlt⟩
  refine ⟨fun i hi ↦ (hrow i hi).1, fun i hi ↦ (hrow i hi).2.1,
    fun i hi ↦ (hrow i hi).2.2.1, fun i hi ↦ (hrow i hi).2.2.2,
    h.source_lt, h.target_lt, ?_⟩
  intro e he
  by_cases hlast : e.target + 1 = w
  · have hs : n + 1 + e.source = n + pivot := by
      have := hnew e he hlast
      lia
    have ht : n + 1 + e.target = n + w := by lia
    cases hk : e.kind with
    | strictInterl => simpa only [WindowEdge.Holds, hk, hs, ht] using hnext
    | interlaces =>
        have hdeg : (P (n + w)).natDegree = (P (n + pivot)).natDegree + 1 := by
          rw [hdegree, h.natDegree_eq pivot hpivot]
          exact hsucc e he hlast hk
        simpa only [WindowEdge.Holds, hk, hs, ht] using hnext.toInterlaces hdeg.symm
  · have hlt : e.target + 1 < w := by have := h.target_lt e he; lia
    have hedge := h.edge _ (hshift e he hlt)
    have hs : n + 1 + e.source = n + (e.source + 1) := by lia
    have ht : n + 1 + e.target = n + (e.target + 1) := by lia
    simpa only [WindowEdge.Holds, hs, ht] using hedge

/-- A finite-family Liu--Wang step preserves a finite interlacing window.
The graph conditions describe only the shifting of offsets. All family
members, including derivative terms, must have certified interlacing. -/
theorem succ_of_finite_family
    {ι : Type*} {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w pivot : ℕ}
    (h : WindowInvariant P degreeLaw E n w) (hpivot : pivot < w)
    (hshift : ∀ e ∈ E, e.target + 1 < w →
      (⟨e.source + 1, e.target + 1, e.kind⟩ : WindowEdge) ∈ E)
    (hnew : ∀ e ∈ E, e.target + 1 = w → e.source + 1 = pivot)
    {s : Finset ι} {a : ℝ[X]} {b g : ι → ℝ[X]}
    (hrec : P (n + w) = a * P (n + pivot) + ∑ i ∈ s, b i * g i)
    (hg : ∀ i ∈ s, StrictInterl (g i) (P (n + pivot)))
    (hgpos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, (P (n + pivot)).IsRoot r → (b i).eval r ≤ 0)
    (hpos : HasPosLeadingCoeff (P (n + w)))
    (hdegree : (P (n + w)).natDegree = degreeLaw (n + w))
    (hlo : degreeLaw (n + pivot) ≤ degreeLaw (n + w))
    (hhi : degreeLaw (n + w) ≤ degreeLaw (n + pivot) + 1)
    (hsucc : ∀ e ∈ E, e.target + 1 = w → e.kind = .interlaces →
      degreeLaw (n + w) = degreeLaw (n + pivot) + 1) :
    WindowInvariant P degreeLaw E (n + 1) w := by
  have hnext := h.strictInterl_next_of_finite_family hpivot hrec hg hgpos hb hpos
    (by rw [hdegree]; exact hlo) (by rw [hdegree]; exact hhi)
  exact succ_of_strictInterl_next h hpivot hshift hnew hnext hpos hdegree hsucc

/-- Sequence-level finite-family induction with a fixed interlacing graph
and an arbitrary degree law, including plateaus. Rank-dependent hypotheses
may use the complete current window certificate. -/
theorem induction_of_finite_family
    {ι : Type*} {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {w pivot : ℕ}
    (hbase : WindowInvariant P degreeLaw E 0 w) (hpivot : pivot < w)
    (hshift : ∀ e ∈ E, e.target + 1 < w →
      (⟨e.source + 1, e.target + 1, e.kind⟩ : WindowEdge) ∈ E)
    (hnew : ∀ e ∈ E, e.target + 1 = w → e.source + 1 = pivot)
    {s : ℕ → Finset ι} {a : ℕ → ℝ[X]} {b g : ℕ → ι → ℝ[X]}
    (hrec : ∀ n, P (n + w) = a n * P (n + pivot) + ∑ i ∈ s n, b n i * g n i)
    (hg : ∀ n, WindowInvariant P degreeLaw E n w →
      ∀ i ∈ s n, StrictInterl (g n i) (P (n + pivot)))
    (hgpos : ∀ n, WindowInvariant P degreeLaw E n w →
      ∀ i ∈ s n, HasPosLeadingCoeff (g n i))
    (hb : ∀ n, WindowInvariant P degreeLaw E n w →
      ∀ i ∈ s n, ∀ r, (P (n + pivot)).IsRoot r → (b n i).eval r ≤ 0)
    (hpos : ∀ n, WindowInvariant P degreeLaw E n w → HasPosLeadingCoeff (P (n + w)))
    (hdegree : ∀ n, WindowInvariant P degreeLaw E n w →
      (P (n + w)).natDegree = degreeLaw (n + w))
    (hlo : ∀ n, degreeLaw (n + pivot) ≤ degreeLaw (n + w))
    (hhi : ∀ n, degreeLaw (n + w) ≤ degreeLaw (n + pivot) + 1)
    (hsucc : ∀ n e, e ∈ E → e.target + 1 = w → e.kind = .interlaces →
      degreeLaw (n + w) = degreeLaw (n + pivot) + 1) :
    ∀ n, WindowInvariant P degreeLaw E n w := by
  apply WindowInvariant.induction hbase
  intro n h
  exact h.succ_of_finite_family hpivot hshift hnew (hrec n)
    (hg n h) (hgpos n h) (hb n h) (hpos n h) (hdegree n h) (hlo n) (hhi n) (hsucc n)

end RealRooted.WindowInvariant
