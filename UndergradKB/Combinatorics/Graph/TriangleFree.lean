import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import UndergradKB.Common.Attr

/-!
# Triangle-free graphs of large chromatic number (Keller–Trotter, Chapter 5.4)

Proposition 5.25: for every `t ≥ 3` there is a graph with chromatic number `t` and clique number
`2`.  We formalize the second (Mycielski) proof: from `G` build the Mycielskian `M(G)` on the
vertex set `{z} ∪ V × {old, copy}`; it is triangle-free when `G` is, and its chromatic number
is one more.
-/

namespace UndergradKB.Combinatorics.Mycielski

open SimpleGraph

variable {V : Type*}

/-- Adjacency of the Mycielskian.  Vertices are `some (x, false)` (the original `x`),
`some (x, true)` (the copy `y_x`) and `none` (the apex `z`). -/
def mycAdj (G : SimpleGraph V) : Option (V × Bool) → Option (V × Bool) → Prop
  | some (x, false), some (x', false) => G.Adj x x'
  | some (x, false), some (x', true) => G.Adj x x'
  | some (x, true), some (x', false) => G.Adj x x'
  | none, some (_, true) => True
  | some (_, true), none => True
  | _, _ => False

/-- The Mycielskian of `G`: a copy of `G`, an independent copy `y_x` of the vertex set where `y_x`
is joined to the original neighbours of `x`, and a new vertex `z` joined to every `y_x`. (CO-109) -/
@[kb "kellertrotter2017" "Proposition 5.25 (second proof), p. 109"]
def mycielskian (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := mycAdj G
  symm := ⟨by
    rintro (_ | ⟨x, _ | _⟩) (_ | ⟨x', _ | _⟩) h <;> simp_all [mycAdj, G.adj_comm]⟩
  loopless := ⟨by
    rintro (_ | ⟨x, _ | _⟩) h <;> simp_all [mycAdj]⟩

/-- The Mycielskian of a triangle-free graph is triangle-free. -/
theorem cliqueFree_three_mycielskian {G : SimpleGraph V} (h : G.CliqueFree 3) :
    (mycielskian G).CliqueFree 3 := by
  classical
  have htri : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z → False := fun x y z hxy hxz hyz =>
    h {x, y, z} (is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hs
  change mycAdj G a b at hab
  change mycAdj G a c at hac
  change mycAdj G b c at hbc
  rcases a with _ | ⟨x, _ | _⟩ <;> rcases b with _ | ⟨y, _ | _⟩ <;>
    rcases c with _ | ⟨z, _ | _⟩ <;> simp only [mycAdj] at hab hac hbc <;>
    exact htri _ _ _ hab hac hbc

/-- If `G` is `n`-colorable then its Mycielskian is `(n+1)`-colorable. -/
theorem colorable_mycielskian {G : SimpleGraph V} {n : ℕ} (h : G.Colorable n) :
    (mycielskian G).Colorable (n + 1) := by
  obtain ⟨C⟩ := h
  refine ⟨Coloring.mk (fun v => match v with
    | none => Fin.last n
    | some (x, _) => (C x).castSucc) ?_⟩
  rintro (_ | ⟨x, _ | _⟩) (_ | ⟨x', _ | _⟩) hadj <;>
    simp only [mycielskian, mycAdj] at hadj <;>
    first
      | exact fun h => C.valid hadj (Fin.castSucc_injective _ h)
      | (have := (C x').isLt; simp [Fin.ext_iff]; omega)
      | (have := (C x).isLt; simp [Fin.ext_iff]; omega)

/-- If the Mycielskian is `k`-colorable then `G` is `(k-1)`-colorable: recolor each original
vertex that has the apex's colour by the colour of its copy. -/
theorem colorable_of_mycielskian {G : SimpleGraph V} {k : ℕ} (h : (mycielskian G).Colorable k) :
    G.Colorable (k - 1) := by
  classical
  obtain ⟨C⟩ := h
  set k0 := C none with hk0
  have hy : ∀ x, C (some (x, true)) ≠ k0 := fun x hx =>
    (C.valid (show (mycielskian G).Adj (some (x, true)) none from trivial)) hx
  let c : V → {c : Fin k // c ≠ k0} := fun x =>
    if h : C (some (x, false)) = k0 then ⟨C (some (x, true)), hy x⟩ else ⟨C (some (x, false)), h⟩
  have hc : ∀ {x x'}, G.Adj x x' → c x ≠ c x' := by
    intro x x' hxx'
    have h1 : C (some (x, false)) ≠ C (some (x', false)) :=
      C.valid (show (mycielskian G).Adj (some (x, false)) (some (x', false)) from hxx')
    have h2 : C (some (x, false)) ≠ C (some (x', true)) :=
      C.valid (show (mycielskian G).Adj (some (x, false)) (some (x', true)) from hxx')
    have h3 : C (some (x, true)) ≠ C (some (x', false)) :=
      C.valid (show (mycielskian G).Adj (some (x, true)) (some (x', false)) from hxx')
    simp only [c]
    split_ifs with e1 e2 e2
    · exact absurd (e1.trans e2.symm) h1
    · intro hh; exact h3 (congrArg Subtype.val hh)
    · intro hh; exact h2 (congrArg Subtype.val hh)
    · intro hh; exact h1 (congrArg Subtype.val hh)
  have := (Coloring.mk c hc).colorable
  have hcard : Fintype.card {c : Fin k // c ≠ k0} = k - 1 := by
    rw [Fintype.card_subtype_compl]; simp
  rwa [hcard] at this

/-- The Mycielskian raises the chromatic number by exactly one. -/
theorem chromaticNumber_mycielskian {G : SimpleGraph V} {n : ℕ}
    (hG : G.chromaticNumber = n) : (mycielskian G).chromaticNumber = n + 1 := by
  have hcol : G.Colorable n := chromaticNumber_le_iff_colorable.mp hG.le
  apply le_antisymm
  · exact_mod_cast (colorable_mycielskian hcol).chromaticNumber_le
  · by_contra hlt
    rw [not_le] at hlt
    have hle : (mycielskian G).chromaticNumber ≤ n := by
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top n)).mp hlt
    have hM := chromaticNumber_le_iff_colorable.mp hle
    have hG' := colorable_of_mycielskian hM
    have := hG'.chromaticNumber_le
    rw [hG] at this
    have hn : n = 0 := by
      have : (n : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := this
      have := Nat.cast_le.mp this
      omega
    subst hn
    have := (colorable_zero_iff.mp hM)
    exact this.false none

/-- CO-109 (Proposition 5.25, Mycielski's construction). For every `t ≥ 1` there is a finite
triangle-free graph with chromatic number `t`. -/
theorem exists_triangleFree_chromaticNumber (t : ℕ) (ht : 1 ≤ t) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      G.CliqueFree 3 ∧ G.chromaticNumber = t := by
  induction t, ht using Nat.le_induction with
  | base =>
    have h3 : (⊥ : SimpleGraph Unit).CliqueFree 3 := cliqueFree_bot (by decide)
    have h1 : (⊥ : SimpleGraph Unit).chromaticNumber = 1 := chromaticNumber_bot
    exact ⟨Unit, inferInstance, ⊥, h3, by simpa using h1⟩
  | succ n hn ih =>
    obtain ⟨W, _, G, h3, hχ⟩ := ih
    exact ⟨Option (W × Bool), inferInstance, mycielskian G, cliqueFree_three_mycielskian h3, by
      rw [chromaticNumber_mycielskian hχ]; push_cast; rfl⟩

/-- CO-109. Proposition 5.25: for every `t ≥ 3` there is a graph `G` with `χ(G) = t` and clique
number `2`, i.e. `G` has an edge but no triangle. -/
@[kb "kellertrotter2017" "Proposition 5.25, p. 109"]
theorem exists_chromaticNumber_eq_cliqueNum_two (t : ℕ) (ht : 3 ≤ t) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      G.CliqueFree 3 ∧ ¬ G.CliqueFree 2 ∧ G.chromaticNumber = t := by
  obtain ⟨W, hW, G, h3, hχ⟩ := exists_triangleFree_chromaticNumber t (by omega)
  refine ⟨W, hW, G, h3, fun h2 => ?_, hχ⟩
  rw [cliqueFree_two] at h2
  subst h2
  have : (⊥ : SimpleGraph W).chromaticNumber ≤ 1 := by
    by_cases hne : Nonempty W
    · exact chromaticNumber_bot.le
    · rw [not_nonempty_iff] at hne
      exact (Colorable.of_isEmpty 1).chromaticNumber_le |>.trans (by simp)
  rw [hχ] at this
  have : t ≤ 1 := by exact_mod_cast this
  omega

end UndergradKB.Combinatorics.Mycielski
