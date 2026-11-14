import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Foundations: straight-line plane drawings

Levin (Section 2.3) calls a graph planar when it can be drawn in the plane without edges crossing,
the edges being arbitrary curves. Mathlib has neither plane embeddings by arcs nor the Jordan curve
theorem, so this file works with drawings whose edges are straight segments
(`StraightLineDrawing`). By Fáry's theorem (not in Mathlib) a finite simple graph is planar if and
only if it has such a drawing; using straight edges is a restriction recorded as a loose end.

The basic tool is the orientation determinant `orient p q r` (twice the signed area of the
triangle `p q r`): it vanishes exactly for collinear points (`orient_eq_zero_mem_segment`), and two
segments whose endpoints separate each other in the sense of orientation signs meet
(`segments_meet`). Sign identities between orientations (`orient_four`, `orient_plucker`) are
the combinatorial input of the non-planarity proofs for `K₅` and `K_{3,3}`.
-/

namespace UndergradKB.Foundations

open Set

/-- Twice the signed area of the triangle `p q r` in the plane `ℝ × ℝ`: positive when `p, q, r`
turn counterclockwise, negative when clockwise, zero when they are collinear. -/
def orient (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

theorem orient_swap (p q r : ℝ × ℝ) : orient q p r = -orient p q r := by
  unfold orient; ring

theorem orient_cycle (p q r : ℝ × ℝ) : orient q r p = orient p q r := by
  unfold orient; ring

/-- The four-point identity `[bcd] - [acd] + [abd] - [abc] = 0`. -/
theorem orient_four (a b c d : ℝ × ℝ) :
    orient b c d - orient a c d + orient a b d - orient a b c = 0 := by
  unfold orient; ring

/-- The three-term Grassmann–Plücker relation for five points of the plane. -/
theorem orient_plucker (x a b c d : ℝ × ℝ) :
    orient x a b * orient x c d - orient x a c * orient x b d + orient x a d * orient x b c = 0 := by
  unfold orient; ring

/-- If `r - p = t (q - p)`, then one of the three points lies on the segment joining the other
two. -/
theorem mem_segment_of_eq_smul {p q r : ℝ × ℝ} {t : ℝ} (h : r - p = t • (q - p)) :
    r ∈ segment ℝ p q ∨ p ∈ segment ℝ r q ∨ q ∈ segment ℝ p r := by
  have hr : r = p + t • (q - p) := by rw [← h]; abel
  rcases lt_or_ge t 0 with ht | ht
  · right; left
    have h1 : (1 : ℝ) - t ≠ 0 := by linarith
    refine ⟨1 / (1 - t), -t / (1 - t), by apply div_nonneg <;> linarith,
      by apply div_nonneg <;> linarith, ?_, ?_⟩
    · field_simp; ring
    · subst hr
      ext <;> simp <;> field_simp <;> ring
  rcases le_or_gt t 1 with ht1 | ht1
  · left
    refine ⟨1 - t, t, by linarith, ht, by ring, ?_⟩
    subst hr
    ext <;> simp <;> ring
  · right; right
    refine ⟨1 - 1 / t, 1 / t, ?_, by positivity, by ring, ?_⟩
    · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · have h1 : t ≠ 0 := by linarith
      subst hr
      ext <;> simp <;> field_simp <;> ring

/-- Three collinear distinct points: one of them lies on the segment joining the other two. -/
theorem orient_eq_zero_mem_segment {p q r : ℝ × ℝ} (hpq : p ≠ q) (h : orient p q r = 0) :
    r ∈ segment ℝ p q ∨ p ∈ segment ℝ r q ∨ q ∈ segment ℝ p r := by
  unfold orient at h
  by_cases h1 : q.1 - p.1 = 0
  · have h2 : q.2 - p.2 ≠ 0 := by
      intro h2
      apply hpq
      ext <;> linarith
    apply mem_segment_of_eq_smul (t := (r.2 - p.2) / (q.2 - p.2))
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      have : (r.1 - p.1) * (q.2 - p.2) = 0 := by rw [h1] at h; linarith
      rcases mul_eq_zero.1 this with h3 | h3
      · rw [h3, h1]; ring
      · exact absurd h3 h2
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      field_simp
  · apply mem_segment_of_eq_smul (t := (r.1 - p.1) / (q.1 - p.1))
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith

/-- Two segments `[p, q]` and `[r, s]` meet when `r, s` lie strictly on opposite sides of the
line `p q` and `p, q` lie strictly on opposite sides of the line `r s`. -/
theorem segments_meet {p q r s : ℝ × ℝ} (h1 : orient p q r * orient p q s < 0)
    (h2 : orient r s p * orient r s q < 0) :
    ∃ z, z ∈ segment ℝ p q ∧ z ∈ segment ℝ r s := by
  set A := orient p q r with hA
  set B := orient p q s with hB
  set C := orient r s p with hC
  set D := orient r s q with hD
  have key : B - A = C - D := by
    simp only [hA, hB, hC, hD]; unfold orient; ring
  have hBA : B - A ≠ 0 := by
    intro h0
    have : B = A := by linarith
    rw [this] at h1; nlinarith [sq_nonneg A]
  have hpos : (0 < A ∧ B < 0) ∨ (A < 0 ∧ 0 < B) := by
    rcases lt_trichotomy A 0 with h | h | h
    · right; exact ⟨h, by nlinarith⟩
    · rw [h] at h1; simp at h1
    · left; exact ⟨h, by nlinarith⟩
  have hpos' : (0 < C ∧ D < 0) ∨ (C < 0 ∧ 0 < D) := by
    rcases lt_trichotomy C 0 with h | h | h
    · right; exact ⟨h, by nlinarith⟩
    · rw [h] at h2; simp at h2
    · left; exact ⟨h, by nlinarith⟩
  refine ⟨(B / (B - A)) • r + (-A / (B - A)) • s, ⟨D / (D - C), -C / (D - C), ?_, ?_, ?_, ?_⟩,
    ⟨B / (B - A), -A / (B - A), ?_, ?_, ?_, rfl⟩⟩
  · rcases hpos' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact div_nonneg_of_nonpos h4.le (by linarith)
    · exact div_nonneg h4.le (by linarith)
  · rcases hpos' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · exact div_nonneg (by linarith) (by linarith)
  · have : D - C ≠ 0 := by intro h0; apply hBA; linarith
    field_simp; ring
  · have hDC : D - C = -(B - A) := by linarith
    rw [hDC]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      simp only [hA, hB, hC, hD]; unfold orient; ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      simp only [hA, hB, hC, hD]; unfold orient; ring
  · rcases hpos with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact div_nonneg_of_nonpos h4.le (by linarith)
    · exact div_nonneg h4.le (by linarith)
  · rcases hpos with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · exact div_nonneg (by linarith) (by linarith)
  · field_simp; ring

/-- A drawing of the graph `G` in the plane with straight edges and no crossings: distinct
vertices go to distinct points, no vertex lies on an edge not incident to it, and two edges with no
common endpoint do not meet. (Two edges with a common endpoint then meet only there.) -/
structure StraightLineDrawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → ℝ × ℝ
  /-- Distinct vertices are drawn at distinct points. -/
  injective : Function.Injective pos
  /-- No vertex lies on an edge it is not an endpoint of. -/
  vertex_not_mem : ∀ u v w, G.Adj u v → w ≠ u → w ≠ v → pos w ∉ segment ℝ (pos u) (pos v)
  /-- Two edges without a common endpoint do not meet. -/
  disjoint : ∀ u v u' v', G.Adj u v → G.Adj u' v' → u ≠ u' → u ≠ v' → v ≠ u' → v ≠ v' →
    Disjoint (segment ℝ (pos u) (pos v)) (segment ℝ (pos u') (pos v'))

/-- In a straight-line drawing the three corners of a triangle of the graph are not collinear. -/
theorem StraightLineDrawing.orient_ne_zero {V : Type*} {G : SimpleGraph V}
    (D : StraightLineDrawing G) {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w)
    (huw : G.Adj u w) : orient (D.pos u) (D.pos v) (D.pos w) ≠ 0 := by
  intro h
  rcases orient_eq_zero_mem_segment (D.injective.ne huv.ne) h with h1 | h1 | h1
  · exact D.vertex_not_mem u v w huv huw.ne.symm hvw.ne.symm h1
  · exact D.vertex_not_mem w v u hvw.symm huw.ne huv.ne h1
  · exact D.vertex_not_mem u w v huw huv.ne.symm hvw.ne h1

/-! ## Sign bookkeeping -/

theorem decide_pos_ne_mul_neg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : decide (0 < x) ≠ decide (0 < y)) : x * y < 0 := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · simp [hx.not_gt, hy.not_gt] at h
  · exact mul_neg_of_neg_of_pos hx hy
  · exact mul_neg_of_pos_of_neg hx hy
  · simp [hx, hy] at h

theorem decide_pos_eq_mul_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : decide (0 < x) = decide (0 < y)) : 0 < x * y := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · exact mul_pos_of_neg_of_neg hx hy
  · simp [hx.not_gt, hy] at h
  · simp [hx, hy.not_gt] at h
  · exact mul_pos hx hy

/-- Sign pattern forbidden by a vanishing alternating sum of four nonzero reals. -/
def quadOk (b1 b2 b3 b4 : Bool) : Bool :=
  !(b1 && !b2 && b3 && !b4) && !(!b1 && b2 && !b3 && b4)

theorem quadOk_of {x1 x2 x3 x4 : ℝ} (h : x1 - x2 + x3 - x4 = 0) :
    quadOk (decide (0 < x1)) (decide (0 < x2)) (decide (0 < x3)) (decide (0 < x4)) = true := by
  unfold quadOk
  by_cases h1 : 0 < x1 <;> by_cases h2 : 0 < x2 <;> by_cases h3 : 0 < x3 <;>
    by_cases h4 : 0 < x4 <;> simp [h1, h2, h3, h4] <;> linarith

/-- Sign pattern forbidden by a vanishing sum of three reals, given the signs of the three
terms. -/
def triOk (b1 b2 b3 : Bool) : Bool :=
  !(b1 && b2 && b3)

theorem triOk_of {y1 y2 y3 : ℝ} (h : y1 + y2 + y3 = 0) :
    triOk (decide (0 < y1)) (decide (0 < y2)) (decide (0 < y3)) = true := by
  unfold triOk
  by_cases h1 : 0 < y1 <;> by_cases h2 : 0 < y2 <;> by_cases h3 : 0 < y3 <;>
    simp [h1, h2, h3]; linarith

theorem triOk_of_neg {y1 y2 y3 : ℝ} (h : y1 + y2 + y3 = 0) (h1 : y1 ≠ 0) (h2 : y2 ≠ 0)
    (h3 : y3 ≠ 0) :
    triOk (!decide (0 < y1)) (!decide (0 < y2)) (!decide (0 < y3)) = true := by
  unfold triOk
  by_cases h1' : 0 < y1 <;> by_cases h2' : 0 < y2 <;> by_cases h3' : 0 < y3 <;>
    simp [h1', h2', h3']
  have := lt_of_le_of_ne (not_lt.1 h1') h1
  have := lt_of_le_of_ne (not_lt.1 h2') h2
  have := lt_of_le_of_ne (not_lt.1 h3') h3
  linarith

/-- The sign of a product of two nonzero reals. -/
theorem decide_mul_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (0 < x * y) = (decide (0 < x) == decide (0 < y)) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · simp [mul_pos_of_neg_of_neg hx hy, hx.not_gt, hy.not_gt]
  · simp [(mul_neg_of_neg_of_pos hx hy).not_gt, hx.not_gt, hy]
  · simp [(mul_neg_of_pos_of_neg hx hy).not_gt, hx, hy.not_gt]
  · simp [mul_pos hx hy, hx, hy]

theorem decide_neg_pos {x : ℝ} (hx : x ≠ 0) : decide (0 < -x) = !decide (0 < x) := by
  rcases hx.lt_or_gt with hx | hx
  · simp [hx, hx.not_gt]
  · simp [hx, (neg_neg_of_pos hx).not_gt]

/-! ## Four points in a drawing -/

/-- The four-point identity for four points `p₁, p₂, p₃, p₄` as a sign constraint on the
orientations of the triples `123, 124, 134, 234`. -/
theorem quadOk_four (p1 p2 p3 p4 : ℝ × ℝ) :
    quadOk (decide (0 < orient p2 p3 p4)) (decide (0 < orient p1 p3 p4))
      (decide (0 < orient p1 p2 p4)) (decide (0 < orient p1 p2 p3)) = true :=
  quadOk_of (orient_four p1 p2 p3 p4)

/-- If the segments `[p₁, p₂]` and `[p₃, p₄]` are disjoint and the four triples are not
collinear, the sign pattern of a crossing of these two segments does not occur. -/
theorem cross12_false {p1 p2 p3 p4 : ℝ × ℝ} (h123 : orient p1 p2 p3 ≠ 0)
    (h124 : orient p1 p2 p4 ≠ 0) (h134 : orient p1 p3 p4 ≠ 0) (h234 : orient p2 p3 p4 ≠ 0)
    (hd : Disjoint (segment ℝ p1 p2) (segment ℝ p3 p4)) :
    (decide (0 < orient p1 p2 p3) != decide (0 < orient p1 p2 p4) &&
      decide (0 < orient p1 p3 p4) != decide (0 < orient p2 p3 p4)) = false := by
  by_contra hc
  simp only [Bool.not_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨z, hz1, hz2⟩ := segments_meet (decide_pos_ne_mul_neg h123 h124 hc.1)
    (by
      have q1 : orient p3 p4 p1 = orient p1 p3 p4 := by unfold orient; ring
      have q2 : orient p3 p4 p2 = orient p2 p3 p4 := by unfold orient; ring
      rw [q1, q2]; exact decide_pos_ne_mul_neg h134 h234 hc.2)
  exact Set.disjoint_left.1 hd hz1 hz2

/-- Crossing of `[p₁, p₃]` and `[p₂, p₄]`, in terms of the orientations of `123, 124, 134, 234`. -/
theorem cross13_false {p1 p2 p3 p4 : ℝ × ℝ} (h123 : orient p1 p2 p3 ≠ 0)
    (h124 : orient p1 p2 p4 ≠ 0) (h134 : orient p1 p3 p4 ≠ 0) (h234 : orient p2 p3 p4 ≠ 0)
    (hd : Disjoint (segment ℝ p1 p3) (segment ℝ p2 p4)) :
    (decide (0 < orient p1 p2 p3) == decide (0 < orient p1 p3 p4) &&
      decide (0 < orient p1 p2 p4) == decide (0 < orient p2 p3 p4)) = false := by
  by_contra hc
  simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
  have e1 : orient p1 p3 p2 * orient p1 p3 p4 < 0 := by
    have := decide_pos_eq_mul_pos h123 h134 hc.1
    have q1 : orient p1 p3 p2 = -orient p1 p2 p3 := by unfold orient; ring
    rw [q1]; linarith
  have e2 : orient p2 p4 p1 * orient p2 p4 p3 < 0 := by
    have := decide_pos_eq_mul_pos h124 h234 hc.2
    have q1 : orient p2 p4 p1 = orient p1 p2 p4 := by unfold orient; ring
    have q2 : orient p2 p4 p3 = -orient p2 p3 p4 := by unfold orient; ring
    rw [q1, q2]; linarith
  obtain ⟨z, hz1, hz2⟩ := segments_meet e1 e2
  exact Set.disjoint_left.1 hd hz1 hz2

/-- Crossing of `[p₁, p₄]` and `[p₂, p₃]`, in terms of the orientations of `123, 124, 134, 234`. -/
theorem cross14_false {p1 p2 p3 p4 : ℝ × ℝ} (h123 : orient p1 p2 p3 ≠ 0)
    (h124 : orient p1 p2 p4 ≠ 0) (h134 : orient p1 p3 p4 ≠ 0) (h234 : orient p2 p3 p4 ≠ 0)
    (hd : Disjoint (segment ℝ p1 p4) (segment ℝ p2 p3)) :
    (decide (0 < orient p1 p2 p4) != decide (0 < orient p1 p3 p4) &&
      decide (0 < orient p1 p2 p3) != decide (0 < orient p2 p3 p4)) = false := by
  by_contra hc
  simp only [Bool.not_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  have e1 : orient p1 p4 p2 * orient p1 p4 p3 < 0 := by
    have := decide_pos_ne_mul_neg h124 h134 hc.1
    have q1 : orient p1 p4 p2 = -orient p1 p2 p4 := by unfold orient; ring
    have q2 : orient p1 p4 p3 = -orient p1 p3 p4 := by unfold orient; ring
    rw [q1, q2]; linarith
  have e2 : orient p2 p3 p1 * orient p2 p3 p4 < 0 := by
    have := decide_pos_ne_mul_neg h123 h234 hc.2
    have q1 : orient p2 p3 p1 = orient p1 p2 p3 := by unfold orient; ring
    rw [q1]; exact this
  obtain ⟨z, hz1, hz2⟩ := segments_meet e1 e2
  exact Set.disjoint_left.1 hd hz1 hz2

end UndergradKB.Foundations
