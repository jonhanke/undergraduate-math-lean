import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import UndergradKB.Foundations.StraightLineK5
import UndergradKB.Foundations.StraightLineK33

/-!
# Foundations: which complete and complete bipartite graphs have straight-line drawings

Levin, Section 2.3.3 (pdf p. 152) asks: for which `n` and `m, n` are `Kₙ` and `K_{m,n}` planar?
Practice Problem 2.3.6 #1 (pdf p. 158) asks the question for eight particular graphs. With straight
edges (`StraightLineDrawing`; Fáry's theorem, not in Mathlib, says this is no restriction for finite
simple graphs) the answers are proved here:

* `Kₙ` has a straight-line drawing if and only if `n ≤ 4` (`isStraightLinePlanar_top_iff`);
* `K_{m,n}` has one if and only if `m ≤ 2` or `n ≤ 2`
  (`isStraightLinePlanar_completeBipartite_iff`).

The negative halves come from `K₅` and `K_{3,3}` (`not_straightLineDrawing_K5`,
`not_straightLineDrawing_K33`) because a drawing restricts to every subgraph
(`StraightLineDrawing.comap`); the positive halves are explicit drawings of `K₄` and `K_{2,n}`.
-/

namespace UndergradKB.Foundations

open Set SimpleGraph

/-- A graph is straight-line planar if it has a drawing in the plane with straight edges and no
crossings. -/
def IsStraightLinePlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (StraightLineDrawing G)

/-- A drawing of `G` restricts to a drawing of every graph embedded in `G`. -/
def StraightLineDrawing.comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H ↪g G) (D : StraightLineDrawing G) : StraightLineDrawing H where
  pos := D.pos ∘ f
  injective := D.injective.comp f.injective
  vertex_not_mem u v w huv hwu hwv :=
    D.vertex_not_mem (f u) (f v) (f w) (f.map_adj_iff.2 huv) (f.injective.ne hwu)
      (f.injective.ne hwv)
  disjoint u v u' v' h h' h1 h2 h3 h4 :=
    D.disjoint (f u) (f v) (f u') (f v') (f.map_adj_iff.2 h) (f.map_adj_iff.2 h')
      (f.injective.ne h1) (f.injective.ne h2) (f.injective.ne h3) (f.injective.ne h4)

theorem IsStraightLinePlanar.comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H ↪g G) (hG : IsStraightLinePlanar G) : IsStraightLinePlanar H :=
  ⟨hG.some.comap f⟩

/-- A point of the segment `[p, q]` lies on the line `p q`. -/
theorem orient_eq_zero_of_mem_segment {p q z : ℝ × ℝ} (h : z ∈ segment ℝ p q) :
    orient p q z = 0 := by
  rw [segment_eq_image] at h
  obtain ⟨θ, -, rfl⟩ := h
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- If `r` and `s` lie strictly on the same side of the line `p q`, the segments `[p, q]` and
`[r, s]` are disjoint. -/
theorem disjoint_of_same_side {p q r s : ℝ × ℝ} (h : 0 < orient p q r * orient p q s) :
    Disjoint (segment ℝ p q) (segment ℝ r s) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have h0 := orient_eq_zero_of_mem_segment hz
  rw [segment_eq_image] at hz'
  obtain ⟨θ, ⟨h1, h2⟩, rfl⟩ := hz'
  have e : orient p q ((1 - θ) • r + θ • s) = (1 - θ) * orient p q r + θ * orient p q s := by
    simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e] at h0
  rcases lt_or_gt_of_ne (show orient p q r ≠ 0 by rintro h3; rw [h3] at h; simp at h) with
    h3 | h3
  · have h4 : orient p q s < 0 := by
      by_contra h4; push Not at h4; nlinarith
    rcases eq_or_lt_of_le h1 with h5 | h5
    · subst h5; nlinarith
    · nlinarith
  · have h4 : 0 < orient p q s := by
      by_contra h4; push Not at h4; nlinarith
    rcases eq_or_lt_of_le h1 with h5 | h5
    · subst h5; nlinarith
    · nlinarith

/-- The vertices of the drawing of `K₄`. -/
def k4Pos : Fin 4 → ℝ × ℝ := ![(0, 0), (4, 0), (0, 4), (1, 1)]

/-- `K₄` has a straight-line drawing: a triangle with a vertex inside. -/
def k4Drawing : StraightLineDrawing (⊤ : SimpleGraph (Fin 4)) where
  pos := k4Pos
  injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [k4Pos, Prod.ext_iff]
  vertex_not_mem u v w huv hwu hwv hw := by
    have h0 := orient_eq_zero_of_mem_segment hw
    rw [top_adj] at huv
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all [k4Pos, orient] <;> norm_num at h0
  disjoint u v u' v' h h' h1 h2 h3 h4 := by
    rw [top_adj] at h h'
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;> simp at h h' h1 h2 h3 h4 <;>
      first
      | (apply disjoint_of_same_side; norm_num [k4Pos, orient]; done)
      | (apply Disjoint.symm; apply disjoint_of_same_side; norm_num [k4Pos, orient]; done)

/-- The vertices of the drawing of `K_{2,n}`: the two vertices of the first side at `(0, 1)` and
`(0, -1)`, the `n` vertices of the other side at `(1, 0), (2, 0), …`. -/
def k2nPos (n : ℕ) : Fin 2 ⊕ Fin n → ℝ × ℝ :=
  Sum.elim ![(0, 1), (0, -1)] fun j => ((j : ℕ) + 1, 0)

theorem k2nPos_segment {n : ℕ} {i : Fin 2} {j : Fin n} {z : ℝ × ℝ}
    (h : z ∈ segment ℝ (k2nPos n (Sum.inl i)) (k2nPos n (Sum.inr j))) :
    ∃ θ ∈ Icc (0 : ℝ) 1, z = (θ * ((j : ℕ) + 1), (1 - θ) * ![1, -1] i) := by
  rw [segment_eq_image] at h
  obtain ⟨θ, hθ, rfl⟩ := h
  refine ⟨θ, hθ, ?_⟩
  fin_cases i <;> simp [k2nPos]

theorem k2nPos_mem {n : ℕ} {i : Fin 2} {j : Fin n} {w : Fin 2 ⊕ Fin n}
    (h : k2nPos n w ∈ segment ℝ (k2nPos n (Sum.inl i)) (k2nPos n (Sum.inr j))) :
    w = Sum.inl i ∨ w = Sum.inr j := by
  obtain ⟨θ, ⟨h0, h1⟩, he⟩ := k2nPos_segment h
  rcases w with i' | j'
  · left
    have hj : (0 : ℝ) < (j : ℕ) + 1 := by positivity
    fin_cases i <;> fin_cases i' <;> simp [k2nPos, Prod.ext_iff] at he ⊢ <;>
      · obtain ⟨e1, e2⟩ := he
        rcases e1 with h | h <;> (try subst h) <;> linarith
  · right
    simp only [k2nPos, Sum.elim_inr, Prod.ext_iff] at he
    obtain ⟨e1, e2⟩ := he
    have hθ : θ = 1 := by
      fin_cases i <;> simp at e2 <;> linarith
    subst hθ
    simp only [one_mul] at e1
    congr 1
    exact Fin.ext (by exact_mod_cast (add_right_cancel e1))

theorem k2nPos_disjoint {n : ℕ} {i i' : Fin 2} {j j' : Fin n} (hi : i ≠ i') (hj : j ≠ j') :
    Disjoint (segment ℝ (k2nPos n (Sum.inl i)) (k2nPos n (Sum.inr j)))
      (segment ℝ (k2nPos n (Sum.inl i')) (k2nPos n (Sum.inr j'))) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := k2nPos_segment hz
  obtain ⟨θ', ⟨h0', h1'⟩, he⟩ := k2nPos_segment hz'
  simp only [Prod.ext_iff] at he
  obtain ⟨e1, e2⟩ := he
  have hθ : θ = 1 ∧ θ' = 1 := by
    fin_cases i <;> fin_cases i' <;> simp at hi e2 <;> constructor <;> linarith
  obtain ⟨rfl, rfl⟩ := hθ
  simp only [one_mul] at e1
  exact hj (Fin.ext (by exact_mod_cast (add_right_cancel e1)))

/-- `K_{2,n}` has a straight-line drawing. -/
def k2nDrawing (n : ℕ) : StraightLineDrawing (completeBipartiteGraph (Fin 2) (Fin n)) where
  pos := k2nPos n
  injective := by
    intro v w h
    rcases v with i | j <;> rcases w with i' | j'
    · fin_cases i <;> fin_cases i' <;> simp_all [k2nPos, Prod.ext_iff] <;> norm_num at h
    · fin_cases i <;> simp [k2nPos, Prod.ext_iff] at h
    · fin_cases i' <;> simp [k2nPos, Prod.ext_iff] at h
    · simp only [k2nPos, Sum.elim_inr, Prod.ext_iff] at h
      exact congrArg Sum.inr (Fin.ext (by exact_mod_cast (add_right_cancel h.1)))
  vertex_not_mem u v w huv hwu hwv hw := by
    rcases u with i | j <;> rcases v with i' | j' <;> simp at huv
    · rcases k2nPos_mem hw with h | h <;> simp_all
    · rw [segment_symm] at hw
      rcases k2nPos_mem hw with h | h <;> simp_all
  disjoint u v u' v' h h' h1 h2 h3 h4 := by
    rcases u with i | j <;> rcases v with i2 | j2 <;> simp at h <;>
      rcases u' with i' | j' <;> rcases v' with i2' | j2' <;> simp at h'
    · exact k2nPos_disjoint (by simpa using h1) (by simpa using h4)
    · rw [segment_symm (𝕜 := ℝ) (k2nPos n (Sum.inr j'))]
      exact k2nPos_disjoint (by simpa using h2) (by simpa using h3)
    · rw [segment_symm (𝕜 := ℝ) (k2nPos n (Sum.inr j))]
      exact k2nPos_disjoint (by simpa using h3) (by simpa using h2)
    · rw [segment_symm (𝕜 := ℝ) (k2nPos n (Sum.inr j)),
        segment_symm (𝕜 := ℝ) (k2nPos n (Sum.inr j'))]
      exact k2nPos_disjoint (by simpa using h4) (by simpa using h1)

/-- Embedding of complete bipartite graphs from injections of the two sides. -/
def completeBipartiteEmb {α β γ δ : Type*} (f : α ↪ γ) (g : β ↪ δ) :
    completeBipartiteGraph α β ↪g completeBipartiteGraph γ δ where
  toEmbedding := f.sumMap g
  map_rel_iff' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;> simp

/-- Swapping the two sides of a complete bipartite graph. -/
def completeBipartiteSwap (α β : Type*) :
    completeBipartiteGraph α β ↪g completeBipartiteGraph β α where
  toEmbedding := ⟨Sum.swap, fun a b h => by simpa using congrArg Sum.swap h⟩
  map_rel_iff' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Function.Embedding.coeFn_mk, Sum.swap]

/-- **`Kₙ` is planar if and only if `n ≤ 4`** (with straight edges): Levin's question in
Section 2.3.3. -/
@[kb "levin2025" "Activity §2.3.3, p. 152"]
theorem isStraightLinePlanar_top_iff (n : ℕ) :
    IsStraightLinePlanar (⊤ : SimpleGraph (Fin n)) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hn
    exact not_straightLineDrawing_K5
      (h.comap (Embedding.completeGraph (Fin.castLEEmb (by omega)))).some
  · intro hn
    exact ⟨k4Drawing.comap (Embedding.completeGraph (Fin.castLEEmb hn))⟩

/-- **`K_{m,n}` is planar if and only if `m ≤ 2` or `n ≤ 2`** (with straight edges): Levin's
question in Section 2.3.3. -/
@[kb "levin2025" "Activity §2.3.3, p. 152"]
theorem isStraightLinePlanar_completeBipartite_iff (m n : ℕ) :
    IsStraightLinePlanar (completeBipartiteGraph (Fin m) (Fin n)) ↔ m ≤ 2 ∨ n ≤ 2 := by
  constructor
  · intro h
    by_contra hmn
    push Not at hmn
    exact not_straightLineDrawing_K33 (h.comap (completeBipartiteEmb
      (Fin.castLEEmb (by omega)) (Fin.castLEEmb (by omega)))).some
  · rintro (hm | hn)
    · exact ⟨(k2nDrawing n).comap
        (completeBipartiteEmb (Fin.castLEEmb hm) (Function.Embedding.refl _))⟩
    · exact ⟨(k2nDrawing m).comap ((completeBipartiteSwap _ _).trans
        (completeBipartiteEmb (Fin.castLEEmb hn) (Function.Embedding.refl _)))⟩

/-- Levin, Practice Problem 2.3.6 #1 (with straight edges): `K₇` is not planar, `K₆` is not
planar, `K₅` is not planar, `K_{3,3}` is not planar, `K_{4,4}` is not planar, `K_{4,5}` is not
planar, `K_{3,10}` is not planar, and `K_{2,5}` is planar. -/
@[kb "levin2025" "Practice Problem 2.3.6 #1, p. 158"]
theorem levin_pp_2_3_6_1 :
    ¬ IsStraightLinePlanar (⊤ : SimpleGraph (Fin 7)) ∧
      ¬ IsStraightLinePlanar (⊤ : SimpleGraph (Fin 6)) ∧
      ¬ IsStraightLinePlanar (⊤ : SimpleGraph (Fin 5)) ∧
      ¬ IsStraightLinePlanar (completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      ¬ IsStraightLinePlanar (completeBipartiteGraph (Fin 4) (Fin 4)) ∧
      ¬ IsStraightLinePlanar (completeBipartiteGraph (Fin 4) (Fin 5)) ∧
      ¬ IsStraightLinePlanar (completeBipartiteGraph (Fin 3) (Fin 10)) ∧
      IsStraightLinePlanar (completeBipartiteGraph (Fin 2) (Fin 5)) := by
  simp only [isStraightLinePlanar_top_iff, isStraightLinePlanar_completeBipartite_iff]
  norm_num

end UndergradKB.Foundations
