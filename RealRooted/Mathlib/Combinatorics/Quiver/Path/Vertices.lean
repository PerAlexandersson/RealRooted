module

public import Mathlib.Combinatorics.Quiver.Path.Vertices

/-!
# Indexed vertices of quiver paths

Small path facts stated in the forward order of `Path.vertices`.  Mathlib's
`Path.toList` instead runs backwards and omits the endpoint, so the chain
lemma below explicitly reverses it before extracting a forward arrow.
-/

public section

namespace Quiver.Path

variable {V : Type*} [Quiver V]

private theorem vertices_eq_reverse_cons_toList {a b : V} (p : Path a b) :
    p.vertices = (b :: p.toList).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp [ih, List.concat_eq_append]

private theorem vertices_isChain_nonempty {a b : V} (p : Path a b) :
    p.vertices.IsChain (fun v w => Nonempty (v ⟶ w)) := by
  rw [vertices_eq_reverse_cons_toList]
  exact List.isChain_reverse.mpr p.isChain_cons_toList_nonempty

/-- Consecutive entries of a path's forward vertex list are joined by an arrow. -/
theorem nonempty_hom_vertices_get_succ {a b : V} (p : Path a b) {n : ℕ}
    (hn : n + 1 < p.vertices.length) :
    Nonempty (p.vertices[n] ⟶ p.vertices[n + 1]) :=
  List.isChain_iff_getElem.mp (vertices_isChain_nonempty p) n hn

/-- A grading which increases by one along each arrow increases by the path length. -/
theorem grade_end_eq_add_length (grade : V → ℕ)
    (hgrade : ∀ {v w : V}, (v ⟶ w) → grade w = grade v + 1)
    {a b : V} (p : Path a b) :
    grade b = grade a + p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [length_cons]
    calc
      grade _ = grade _ + 1 := hgrade e
      _ = (grade _ + p.length) + 1 := by rw [ih]
      _ = grade _ + (p.length + 1) := Nat.add_assoc _ _ _

/-- The grade of every indexed path vertex is its initial grade plus its index. -/
theorem grade_vertices_get (grade : V → ℕ)
    (hgrade : ∀ {v w : V}, (v ⟶ w) → grade w = grade v + 1)
    {a b : V} (p : Path a b) (n : ℕ) (hn : n < p.vertices.length) :
    grade p.vertices[n] = grade a + n := by
  obtain ⟨v, p₁, _, _, hlength, hv⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length n hn
  rw [← hv]
  simpa only [hlength] using grade_end_eq_add_length grade hgrade p₁

end Quiver.Path
