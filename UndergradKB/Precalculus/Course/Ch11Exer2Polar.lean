import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Course.Ch11ExerE

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.5,
intersections of polar graphs

The points of intersection of two polar graphs, as subsets of the plane: the graph of `r = f θ` is
`polarGraphFn f`, and the book's answer (pairs `(r, θ)` including the pole) is the finite set of the corresponding
points. -/

namespace UndergradKB.Precalculus.Course

open Real Set

private lemma pol7_c53 : cos (5 * π / 3) = 1 / 2 := by
  rw [show 5 * π / 3 = -(π / 3) + 2 * π by ring, cos_add_two_pi, cos_neg, cos_pi_div_three]

private lemma pol7_s53 : sin (5 * π / 3) = -(√3 / 2) := by
  rw [show 5 * π / 3 = -(π / 3) + 2 * π by ring, sin_add_two_pi, sin_neg, sin_pi_div_three]

/-- A point `polarPoint r θ` has `x² + y² = r²`. -/
private lemma pol7_sq (r θ : ℝ) :
    (polarPoint r θ).1 ^ 2 + (polarPoint r θ).2 ^ 2 = r ^ 2 := by
  simp only [polarPoint]
  linear_combination r ^ 2 * sin_sq_add_cos_sq θ

/-- Stitz-Zeager Exercise 11.5.21: the circle `r = 3 cos θ` and the cardioid `r = 1 + cos θ` meet exactly at the
pole and the points `(3/2, π/3)` and `(3/2, 5π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.21, p. 970"]
theorem exer_11_5_21 :
    polarGraphFn (fun θ => 3 * cos θ) ∩ polarGraphFn (fun θ => 1 + cos θ) =
      {(0, 0), polarPoint (3 / 2) (π / 3), polarPoint (3 / 2) (5 * π / 3)} := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e1 : polarPoint (3 / 2) (π / 3) = (3 / 4, 3 * √3 / 4) := by
    simp only [polarPoint, cos_pi_div_three, sin_pi_div_three, Prod.mk.injEq]; constructor <;> ring
  have e2 : polarPoint (3 / 2) (5 * π / 3) = (3 / 4, -(3 * √3 / 4)) := by
    simp only [polarPoint, pol7_c53, pol7_s53, Prod.mk.injEq]; constructor <;> ring
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq,Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h2⟩⟩
    have a1 := pol7_sq (3 * cos θ1) θ1
    have a2 := pol7_sq (1 + cos θ2) θ2
    rw [← h1] at a1
    rw [← h2] at a2
    have b1 := congrArg Prod.fst h1
    have b2 := congrArg Prod.fst h2
    simp only [polarPoint] at b1 b2
    simp only at a1 a2
    -- P1: x² + y² = 3x, P2: (x² + y² - x)² = x² + y²
    have P1 : x ^ 2 + y ^ 2 = 3 * x := by rw [a1, b1]; nlinarith [cos_sq_add_sin_sq θ1]
    have P2 : (x ^ 2 + y ^ 2 - x) ^ 2 = x ^ 2 + y ^ 2 := by
      have : x ^ 2 + y ^ 2 - x = 1 + cos θ2 := by rw [a2, b2]; nlinarith [cos_sq_add_sin_sq θ2]
      rw [this, a2]
    have hx : x * (4 * x - 3) = 0 := by
      have : (3 * x - x) ^ 2 = 3 * x := by rw [← P1]; exact P2
      nlinarith
    rcases mul_eq_zero.mp hx with h | h
    · left
      have hy : y = 0 := by nlinarith [sq_nonneg y]
      rw [h, hy]
    · right
      have hx' : x = 3 / 4 := by linarith
      have hy : (y - 3 * √3 / 4) * (y + 3 * √3 / 4) = 0 := by nlinarith
      rcases mul_eq_zero.mp hy with h' | h'
      · left; rw [e1]; exact Prod.ext hx' (by show y = 3 * √3 / 4; linarith)
      · right; rw [e2]; exact Prod.ext hx' (by show y = -(3 * √3 / 4); linarith)
  · rintro (h | h | h)
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨π / 2, ?_⟩, ⟨π, ?_⟩⟩ <;> simp [polarPoint]
    · refine ⟨⟨π / 3, ?_⟩, ⟨π / 3, ?_⟩⟩ <;> rw [h] <;> rw [cos_pi_div_three] <;> norm_num
    · refine ⟨⟨5 * π / 3, ?_⟩, ⟨5 * π / 3, ?_⟩⟩ <;> rw [h] <;> rw [pol7_c53] <;> norm_num

private lemma pol7_s76 : sin (7 * π / 6) = -(1 / 2) := by
  rw [show 7 * π / 6 = π / 6 + π by ring, sin_add_pi, sin_pi_div_six]

private lemma pol7_c76 : cos (7 * π / 6) = -(√3 / 2) := by
  rw [show 7 * π / 6 = π / 6 + π by ring, cos_add_pi, cos_pi_div_six]

private lemma pol7_s116 : sin (11 * π / 6) = -(1 / 2) := by
  rw [show 11 * π / 6 = -(π / 6) + 2 * π by ring, sin_add_two_pi, sin_neg, sin_pi_div_six]

private lemma pol7_c116 : cos (11 * π / 6) = √3 / 2 := by
  rw [show 11 * π / 6 = -(π / 6) + 2 * π by ring, cos_add_two_pi, cos_neg, cos_pi_div_six]

/-- Stitz-Zeager Exercise 11.5.23: the limaçon `r = 1 - 2 sin θ` and the circle `r = 2` meet exactly at the points
`(2, 7π/6)` and `(2, 11π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.23, p. 970"]
theorem exer_11_5_23 :
    polarGraphFn (fun θ => 1 - 2 * sin θ) ∩ polarGraphFn (fun _ => (2 : ℝ)) =
      {polarPoint 2 (7 * π / 6), polarPoint 2 (11 * π / 6)} := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e1 : polarPoint 2 (7 * π / 6) = (-√3, -1) := by
    simp only [polarPoint, pol7_s76, pol7_c76, Prod.mk.injEq]; constructor <;> ring
  have e2 : polarPoint 2 (11 * π / 6) = (√3, -1) := by
    simp only [polarPoint, pol7_s116, pol7_c116, Prod.mk.injEq]; constructor <;> ring
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h2⟩⟩
    have a1 := pol7_sq (1 - 2 * sin θ1) θ1
    have a2 := pol7_sq 2 θ2
    rw [← h1] at a1
    rw [← h2] at a2
    have b1 := congrArg Prod.snd h1
    simp only [polarPoint] at b1
    simp only at a1 a2
    have P2 : x ^ 2 + y ^ 2 = 4 := by rw [a2]; norm_num
    have P1 : x ^ 2 + y ^ 2 + 2 * y = 1 - 2 * sin θ1 := by
      rw [a1, b1]; ring
    have hy : (y + 1) * (y + 3) = 0 := by
      have h4 : (1 - 2 * sin θ1) ^ 2 = x ^ 2 + y ^ 2 := a1.symm
      rw [← P1] at h4
      nlinarith
    rcases mul_eq_zero.mp hy with h | h
    · have hy' : y = -1 := by linarith
      have hx : (x + √3) * (x - √3) = 0 := by nlinarith
      rcases mul_eq_zero.mp hx with h' | h'
      · left; rw [e1]; exact Prod.ext (by show x = -√3; linarith) hy'
      · right; rw [e2]; exact Prod.ext (by show x = √3; linarith) hy'
    · exfalso; nlinarith [sq_nonneg x]
  · rintro (h | h)
    · refine ⟨⟨7 * π / 6, ?_⟩, ⟨7 * π / 6, ?_⟩⟩ <;> rw [h]
      rw [pol7_s76]; norm_num
    · refine ⟨⟨11 * π / 6, ?_⟩, ⟨11 * π / 6, ?_⟩⟩ <;> rw [h]
      rw [pol7_s116]; norm_num

private lemma pol7_c32 : cos (3 * π / 2) = 0 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; norm_num

private lemma pol7_s32 : sin (3 * π / 2) = -1 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]

/-- Stitz-Zeager Exercise 11.5.24: the limaçon `r = 1 - 2 cos θ` and the circle `r = 1` meet exactly at the points
`(1, π/2)`, `(1, 3π/2)` and `(-1, 0)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.24, p. 970"]
theorem exer_11_5_24 :
    polarGraphFn (fun θ => 1 - 2 * cos θ) ∩ polarGraphFn (fun _ => (1 : ℝ)) =
      {polarPoint 1 (π / 2), polarPoint 1 (3 * π / 2), polarPoint (-1) 0} := by
  have e1 : polarPoint 1 (π / 2) = (0, 1) := by
    simp only [polarPoint, cos_pi_div_two, sin_pi_div_two, Prod.mk.injEq]; constructor <;> ring
  have e2 : polarPoint 1 (3 * π / 2) = (0, -1) := by
    simp only [polarPoint, pol7_c32, pol7_s32, Prod.mk.injEq]; constructor <;> ring
  have e3 : polarPoint (-1) 0 = (-1, 0) := by
    simp only [polarPoint, cos_zero, sin_zero, Prod.mk.injEq]; constructor <;> ring
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h2⟩⟩
    have a1 := pol7_sq (1 - 2 * cos θ1) θ1
    have a2 := pol7_sq 1 θ2
    rw [← h1] at a1
    rw [← h2] at a2
    have b1 := congrArg Prod.fst h1
    simp only [polarPoint] at b1
    simp only at a1 a2
    have P2 : x ^ 2 + y ^ 2 = 1 := by rw [a2]; norm_num
    have P1 : x ^ 2 + y ^ 2 + 2 * x = 1 - 2 * cos θ1 := by
      rw [a1, b1]; nlinarith [cos_sq_add_sin_sq θ1]
    have hx : x * (x + 1) = 0 := by
      have h4 : (1 - 2 * cos θ1) ^ 2 = x ^ 2 + y ^ 2 := a1.symm
      rw [← P1] at h4
      nlinarith
    rcases mul_eq_zero.mp hx with h | h
    · have hy : (y - 1) * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hy with h' | h'
      · left; rw [e1]; exact Prod.ext h (by show y = 1; linarith)
      · right; left; rw [e2]; exact Prod.ext h (by show y = -1; linarith)
    · right; right
      have hx' : x = -1 := by linarith
      rw [e3]; exact Prod.ext hx' (by show y = 0; nlinarith [sq_nonneg y])
  · rintro (h | h | h)
    · refine ⟨⟨π / 2, ?_⟩, ⟨π / 2, ?_⟩⟩ <;> rw [h]
      rw [cos_pi_div_two]; norm_num
    · refine ⟨⟨3 * π / 2, ?_⟩, ⟨3 * π / 2, ?_⟩⟩ <;> rw [h]
      rw [pol7_c32]; norm_num
    · refine ⟨⟨0, ?_⟩, ⟨π, ?_⟩⟩ <;> rw [h]
      · rw [cos_zero]; norm_num
      · simp [polarPoint]

private lemma pol7_c56 : cos (5 * π / 6) = -(√3 / 2) := by
  rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, cos_pi_div_six]

private lemma pol7_s56 : sin (5 * π / 6) = 1 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]

/-- Stitz-Zeager Exercise 11.5.27: the lemniscate `r² = 4 cos 2θ` and the circle `r = √2` meet exactly at the
points `(√2, π/6)`, `(√2, 5π/6)`, `(√2, 7π/6)` and `(√2, 11π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.27, p. 970"]
theorem exer_11_5_27 :
    {p : ℝ × ℝ | ∃ θ r : ℝ, r ^ 2 = 4 * cos (2 * θ) ∧ p = polarPoint r θ} ∩ polarGraphFn (fun _ => √2) =
      {polarPoint (√2) (π / 6), polarPoint (√2) (5 * π / 6), polarPoint (√2) (7 * π / 6),
        polarPoint (√2) (11 * π / 6)} := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = √2 * (√3 / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = √2 * (1 / 2) := ⟨_, rfl⟩
  have ha2 : a ^ 2 = 3 / 2 := by rw [ha, mul_pow, div_pow, h2, h3]; norm_num
  have hb2 : b ^ 2 = 1 / 2 := by rw [hb, mul_pow, h2]; norm_num
  have e1 : polarPoint (√2) (π / 6) = (a, b) :=
    Prod.ext (by simp only [polarPoint, cos_pi_div_six, ha]) (by simp only [polarPoint, sin_pi_div_six, hb])
  have e2 : polarPoint (√2) (5 * π / 6) = (-a, b) :=
    Prod.ext (by simp only [polarPoint, pol7_c56, ha]; ring) (by simp only [polarPoint, pol7_s56, hb])
  have e3 : polarPoint (√2) (7 * π / 6) = (-a, -b) :=
    Prod.ext (by simp only [polarPoint, pol7_c76, ha]; ring) (by simp only [polarPoint, pol7_s76, hb]; ring)
  have e4 : polarPoint (√2) (11 * π / 6) = (a, -b) :=
    Prod.ext (by simp only [polarPoint, pol7_c116, ha]) (by simp only [polarPoint, pol7_s116, hb]; ring)
  have k1 : cos (2 * (π / 6)) = 1 / 2 := by rw [show 2 * (π / 6) = π / 3 by ring, cos_pi_div_three]
  have k2 : cos (2 * (5 * π / 6)) = 1 / 2 := by rw [show 2 * (5 * π / 6) = 5 * π / 3 by ring, pol7_c53]
  have k3 : cos (2 * (7 * π / 6)) = 1 / 2 := by
    rw [show 2 * (7 * π / 6) = π / 3 + 2 * π by ring, cos_add_two_pi, cos_pi_div_three]
  have k4 : cos (2 * (11 * π / 6)) = 1 / 2 := by
    rw [show 2 * (11 * π / 6) = 5 * π / 3 + 2 * π by ring, cos_add_two_pi, pol7_c53]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, r1, hr, h1⟩, ⟨θ2, h3'⟩⟩
    simp only [polarPoint, Prod.mk.injEq] at h1 h3'
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hx2, hy2⟩ := h3'
    have a1 : x ^ 2 + y ^ 2 = r1 ^ 2 := by
      rw [hx, hy]; linear_combination r1 ^ 2 * sin_sq_add_cos_sq θ1
    have a2 : x ^ 2 + y ^ 2 = 2 := by
      rw [hx2, hy2]; linear_combination (√2 ^ 2) * sin_sq_add_cos_sq θ2 + h2
    have hxy : x ^ 2 - y ^ 2 = r1 ^ 2 * cos (2 * θ1) := by
      rw [hx, hy, cos_two_mul]; linear_combination (-r1 ^ 2) * sin_sq_add_cos_sq θ1
    have hr2 : r1 ^ 2 = 2 := by linarith
    have hc : cos (2 * θ1) = 1 / 2 := by linarith
    have hd : x ^ 2 - y ^ 2 = 1 := by rw [hxy, hr2, hc]; norm_num
    have hxa : (x - a) * (x + a) = 0 := by
      have : (x - a) * (x + a) = x ^ 2 - a ^ 2 := by ring
      rw [this]; linarith
    have hyb : (y - b) * (y + b) = 0 := by
      have : (y - b) * (y + b) = y ^ 2 - b ^ 2 := by ring
      rw [this]; linarith
    rcases mul_eq_zero.mp hxa with h | h <;> rcases mul_eq_zero.mp hyb with h' | h'
    · left; rw [e1]; exact Prod.ext (by show x = a; linarith) (by show y = b; linarith)
    · right; right; right; rw [e4]; exact Prod.ext (by show x = a; linarith) (by show y = -b; linarith)
    · right; left; rw [e2]; exact Prod.ext (by show x = -a; linarith) (by show y = b; linarith)
    · right; right; left; rw [e3]; exact Prod.ext (by show x = -a; linarith) (by show y = -b; linarith)
  · rintro (h | h | h | h)
    · exact ⟨⟨π / 6, √2, by rw [h2, k1]; norm_num, h⟩, ⟨π / 6, h⟩⟩
    · exact ⟨⟨5 * π / 6, √2, by rw [h2, k2]; norm_num, h⟩, ⟨5 * π / 6, h⟩⟩
    · exact ⟨⟨7 * π / 6, √2, by rw [h2, k3]; norm_num, h⟩, ⟨7 * π / 6, h⟩⟩
    · exact ⟨⟨11 * π / 6, √2, by rw [h2, k4]; norm_num, h⟩, ⟨11 * π / 6, h⟩⟩

private lemma pol7_c12 : cos (π / 12) = √2 * (√3 + 1) / 4 := by
  rw [show π / 12 = π / 4 - π / 6 by ring, cos_sub, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six,
    sin_pi_div_six]
  ring

private lemma pol7_s12 : sin (π / 12) = √2 * (√3 - 1) / 4 := by
  rw [show π / 12 = π / 4 - π / 6 by ring, sin_sub, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six,
    sin_pi_div_six]
  ring

private lemma pol7_c512 : cos (5 * π / 12) = √2 * (√3 - 1) / 4 := by
  rw [show 5 * π / 12 = π / 4 + π / 6 by ring, cos_add, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six,
    sin_pi_div_six]
  ring

private lemma pol7_s512 : sin (5 * π / 12) = √2 * (√3 + 1) / 4 := by
  rw [show 5 * π / 12 = π / 4 + π / 6 by ring, sin_add, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six,
    sin_pi_div_six]
  ring

/-- If `x² + y² = 1`, `xy = 1/4` and `u² + v² = 1`, `uv = 1/4` (`u, v` positive), the point `(x, y)` is one of
`(u, v)`, `(v, u)`, `(-u, -v)`, `(-v, -u)`. -/
private lemma pol7_four {u v x y : ℝ} (huv : u ^ 2 + v ^ 2 = 1) (h : u * v = 1 / 4)
    (hs : x ^ 2 + y ^ 2 = 1) (hp : x * y = 1 / 4) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨ (x = -u ∧ y = -v) ∨ (x = -v ∧ y = -u) := by
  have h1 : (x + y - (u + v)) * (x + y + (u + v)) = 0 := by nlinarith
  have h2 : (x - y - (u - v)) * (x - y + (u - v)) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with a | a <;> rcases mul_eq_zero.mp h2 with b | b
  · left; constructor <;> linarith
  · right; left; constructor <;> linarith
  · right; right; right; constructor <;> linarith
  · right; right; left; constructor <;> linarith

private lemma pol7_pp (r θ : ℝ) : polarPoint (-r) θ = polarPoint r (θ + π) := by
  simp only [polarPoint, cos_add_pi, sin_add_pi]
  ext <;> ring

/-- Stitz-Zeager Exercise 11.5.28: the lemniscate `r² = 2 sin 2θ` and the circle `r = 1` meet exactly at the points
`(1, π/12)`, `(1, 5π/12)`, `(1, 13π/12)` and `(1, 17π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.28, p. 970"]
theorem exer_11_5_28 :
    {p : ℝ × ℝ | ∃ θ r : ℝ, r ^ 2 = 2 * sin (2 * θ) ∧ p = polarPoint r θ} ∩ polarGraphFn (fun _ => (1 : ℝ)) =
      {polarPoint 1 (π / 12), polarPoint 1 (5 * π / 12), polarPoint 1 (13 * π / 12),
        polarPoint 1 (17 * π / 12)} := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3 : 1 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : 0 < √2 := by positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = √2 * (√3 + 1) / 4 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = √2 * (√3 - 1) / 4 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hv0 : 0 < v := by rw [hv]; have : 0 < √3 - 1 := by linarith
                         positivity
  have huv : u ^ 2 + v ^ 2 = 1 := by
    rw [hu, hv]; nlinarith
  have huv' : u * v = 1 / 4 := by
    rw [hu, hv]; nlinarith
  have e1 : polarPoint 1 (π / 12) = (u, v) :=
    Prod.ext (by simp only [polarPoint, pol7_c12, hu, one_mul]) (by simp only [polarPoint, pol7_s12, hv, one_mul])
  have e2 : polarPoint 1 (5 * π / 12) = (v, u) :=
    Prod.ext (by simp only [polarPoint, pol7_c512, hv, one_mul]) (by simp only [polarPoint, pol7_s512, hu, one_mul])
  have e3 : polarPoint 1 (13 * π / 12) = (-u, -v) :=
    Prod.ext (by simp only [polarPoint, show 13 * π / 12 = π / 12 + π by ring, cos_add_pi, pol7_c12, hu]; ring)
      (by simp only [polarPoint, show 13 * π / 12 = π / 12 + π by ring, sin_add_pi, pol7_s12, hv]; ring)
  have e4 : polarPoint 1 (17 * π / 12) = (-v, -u) :=
    Prod.ext (by simp only [polarPoint, show 17 * π / 12 = 5 * π / 12 + π by ring, cos_add_pi, pol7_c512, hv]; ring)
      (by simp only [polarPoint, show 17 * π / 12 = 5 * π / 12 + π by ring, sin_add_pi, pol7_s512, hu]; ring)
  have k1 : sin (2 * (π / 12)) = 1 / 2 := by rw [show 2 * (π / 12) = π / 6 by ring, sin_pi_div_six]
  have k2 : sin (2 * (5 * π / 12)) = 1 / 2 := by
    rw [show 2 * (5 * π / 12) = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]
  have k3 : sin (2 * (13 * π / 12)) = 1 / 2 := by
    rw [show 2 * (13 * π / 12) = π / 6 + 2 * π by ring, sin_add_two_pi, sin_pi_div_six]
  have k4 : sin (2 * (17 * π / 12)) = 1 / 2 := by
    rw [show 2 * (17 * π / 12) = (π - π / 6) + 2 * π by ring, sin_add_two_pi, sin_pi_sub, sin_pi_div_six]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, r1, hr, h1⟩, ⟨θ2, h3'⟩⟩
    simp only [polarPoint, Prod.mk.injEq] at h1 h3'
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hx2, hy2⟩ := h3'
    have a1 : x ^ 2 + y ^ 2 = r1 ^ 2 := by
      rw [hx, hy]; linear_combination r1 ^ 2 * sin_sq_add_cos_sq θ1
    have a2 : x ^ 2 + y ^ 2 = 1 := by
      rw [hx2, hy2]; linear_combination sin_sq_add_cos_sq θ2
    have hr2 : r1 ^ 2 = 1 := by linarith
    have hs : sin (2 * θ1) = 1 / 2 := by linarith
    have hp : x * y = 1 / 4 := by
      rw [hx, hy]
      have : r1 * cos θ1 * (r1 * sin θ1) = r1 ^ 2 * (sin (2 * θ1) / 2) := by rw [sin_two_mul]; ring
      rw [this, hr2, hs]; norm_num
    rcases pol7_four huv huv' a2 hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · left; rw [e1]; exact Prod.ext a b
    · right; left; rw [e2]; exact Prod.ext a b
    · right; right; left; rw [e3]; exact Prod.ext a b
    · right; right; right; rw [e4]; exact Prod.ext a b
  · rintro (h | h | h | h)
    · exact ⟨⟨π / 12, 1, by rw [k1]; norm_num, h⟩, ⟨π / 12, h⟩⟩
    · exact ⟨⟨5 * π / 12, 1, by rw [k2]; norm_num, h⟩, ⟨5 * π / 12, h⟩⟩
    · exact ⟨⟨13 * π / 12, 1, by rw [k3]; norm_num, h⟩, ⟨13 * π / 12, h⟩⟩
    · exact ⟨⟨17 * π / 12, 1, by rw [k4]; norm_num, h⟩, ⟨17 * π / 12, h⟩⟩

/-- Stitz-Zeager Exercise 11.5.30: the rose `r = 2 sin 2θ` and the circle `r = 1` meet exactly at the eight points
`(1, π/12)`, `(1, 5π/12)`, `(1, 13π/12)`, `(1, 17π/12)`, `(-1, 7π/12)`, `(-1, 11π/12)`, `(-1, 19π/12)`,
`(-1, 23π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.30, p. 970"]
theorem exer_11_5_30 :
    polarGraphFn (fun θ => 2 * sin (2 * θ)) ∩ polarGraphFn (fun _ => (1 : ℝ)) =
      {polarPoint 1 (π / 12), polarPoint 1 (5 * π / 12), polarPoint 1 (13 * π / 12), polarPoint 1 (17 * π / 12),
        polarPoint (-1) (7 * π / 12), polarPoint (-1) (11 * π / 12), polarPoint (-1) (19 * π / 12),
        polarPoint (-1) (23 * π / 12)} := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3 : 1 < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : 0 < √2 := by positivity
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = √2 * (√3 + 1) / 4 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = √2 * (√3 - 1) / 4 := ⟨_, rfl⟩
  have huv : u ^ 2 + v ^ 2 = 1 := by
    rw [hu, hv]; nlinarith
  have huv' : u * v = 1 / 4 := by
    rw [hu, hv]; nlinarith
  have e1 : polarPoint 1 (π / 12) = (u, v) :=
    Prod.ext (by simp only [polarPoint, pol7_c12, hu, one_mul]) (by simp only [polarPoint, pol7_s12, hv, one_mul])
  have e2 : polarPoint 1 (5 * π / 12) = (v, u) :=
    Prod.ext (by simp only [polarPoint, pol7_c512, hv, one_mul]) (by simp only [polarPoint, pol7_s512, hu, one_mul])
  have e3 : polarPoint 1 (13 * π / 12) = (-u, -v) :=
    Prod.ext (by simp only [polarPoint, show 13 * π / 12 = π / 12 + π by ring, cos_add_pi, pol7_c12, hu]; ring)
      (by simp only [polarPoint, show 13 * π / 12 = π / 12 + π by ring, sin_add_pi, pol7_s12, hv]; ring)
  have e4 : polarPoint 1 (17 * π / 12) = (-v, -u) :=
    Prod.ext (by simp only [polarPoint, show 17 * π / 12 = 5 * π / 12 + π by ring, cos_add_pi, pol7_c512, hv]; ring)
      (by simp only [polarPoint, show 17 * π / 12 = 5 * π / 12 + π by ring, sin_add_pi, pol7_s512, hu]; ring)
  have c712 : cos (7 * π / 12) = -v := by
    rw [show 7 * π / 12 = π / 12 + π / 2 by ring, cos_add_pi_div_two, pol7_s12, hv]
  have s712 : sin (7 * π / 12) = u := by
    rw [show 7 * π / 12 = π / 12 + π / 2 by ring, sin_add_pi_div_two, pol7_c12, hu]
  have c1112 : cos (11 * π / 12) = -u := by
    rw [show 11 * π / 12 = π - π / 12 by ring, cos_pi_sub, pol7_c12, hu]
  have s1112 : sin (11 * π / 12) = v := by
    rw [show 11 * π / 12 = π - π / 12 by ring, sin_pi_sub, pol7_s12, hv]
  have c1912 : cos (19 * π / 12) = v := by
    rw [show 19 * π / 12 = 7 * π / 12 + π by ring, cos_add_pi, c712]; ring
  have s1912 : sin (19 * π / 12) = -u := by
    rw [show 19 * π / 12 = 7 * π / 12 + π by ring, sin_add_pi, s712]
  have c2312 : cos (23 * π / 12) = u := by
    rw [show 23 * π / 12 = 11 * π / 12 + π by ring, cos_add_pi, c1112]; ring
  have s2312 : sin (23 * π / 12) = -v := by
    rw [show 23 * π / 12 = 11 * π / 12 + π by ring, sin_add_pi, s1112]
  have e5 : polarPoint (-1) (7 * π / 12) = (v, -u) :=
    Prod.ext (by simp only [polarPoint, c712]; ring) (by simp only [polarPoint, s712]; ring)
  have e6 : polarPoint (-1) (11 * π / 12) = (u, -v) :=
    Prod.ext (by simp only [polarPoint, c1112]; ring) (by simp only [polarPoint, s1112]; ring)
  have e7 : polarPoint (-1) (19 * π / 12) = (-v, u) :=
    Prod.ext (by simp only [polarPoint, c1912]; ring) (by simp only [polarPoint, s1912]; ring)
  have e8 : polarPoint (-1) (23 * π / 12) = (-u, v) :=
    Prod.ext (by simp only [polarPoint, c2312]; ring) (by simp only [polarPoint, s2312]; ring)
  have k1 : sin (2 * (π / 12)) = 1 / 2 := by rw [show 2 * (π / 12) = π / 6 by ring, sin_pi_div_six]
  have k2 : sin (2 * (5 * π / 12)) = 1 / 2 := by
    rw [show 2 * (5 * π / 12) = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]
  have k3 : sin (2 * (13 * π / 12)) = 1 / 2 := by
    rw [show 2 * (13 * π / 12) = π / 6 + 2 * π by ring, sin_add_two_pi, sin_pi_div_six]
  have k4 : sin (2 * (17 * π / 12)) = 1 / 2 := by
    rw [show 2 * (17 * π / 12) = (π - π / 6) + 2 * π by ring, sin_add_two_pi, sin_pi_sub, sin_pi_div_six]
  have k5 : sin (2 * (7 * π / 12)) = -(1 / 2) := by rw [show 2 * (7 * π / 12) = 7 * π / 6 by ring, pol7_s76]
  have k6 : sin (2 * (11 * π / 12)) = -(1 / 2) := by rw [show 2 * (11 * π / 12) = 11 * π / 6 by ring, pol7_s116]
  have k7 : sin (2 * (19 * π / 12)) = -(1 / 2) := by
    rw [show 2 * (19 * π / 12) = 7 * π / 6 + 2 * π by ring, sin_add_two_pi, pol7_s76]
  have k8 : sin (2 * (23 * π / 12)) = -(1 / 2) := by
    rw [show 2 * (23 * π / 12) = 11 * π / 6 + 2 * π by ring, sin_add_two_pi, pol7_s116]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h3'⟩⟩
    simp only [polarPoint, Prod.mk.injEq] at h1 h3'
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hx2, hy2⟩ := h3'
    obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = 2 * sin (2 * θ1) := ⟨_, rfl⟩
    rw [← hr1] at hx hy
    have a1 : x ^ 2 + y ^ 2 = r1 ^ 2 := by
      rw [hx, hy]; linear_combination r1 ^ 2 * sin_sq_add_cos_sq θ1
    have a2 : x ^ 2 + y ^ 2 = 1 := by
      rw [hx2, hy2]; linear_combination sin_sq_add_cos_sq θ2
    have hr2 : (r1 - 1) * (r1 + 1) = 0 := by nlinarith
    have hp : x * y = r1 ^ 3 / 4 := by
      rw [hx, hy]
      have : r1 * cos θ1 * (r1 * sin θ1) = r1 ^ 2 * (sin (2 * θ1) / 2) := by rw [sin_two_mul]; ring
      rw [this]
      have : sin (2 * θ1) = r1 / 2 := by rw [hr1]; ring
      rw [this]; ring
    rcases mul_eq_zero.mp hr2 with h | h
    · have hr : r1 = 1 := by linarith
      rw [hr] at hp
      rcases pol7_four huv huv' a2 (by rw [hp]; norm_num) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · left; rw [e1]; exact Prod.ext a b
      · right; left; rw [e2]; exact Prod.ext a b
      · right; right; left; rw [e3]; exact Prod.ext a b
      · right; right; right; left; rw [e4]; exact Prod.ext a b
    · have hr : r1 = -1 := by linarith
      rw [hr] at hp
      have a2' : x ^ 2 + (-y) ^ 2 = 1 := by rw [neg_sq]; exact a2
      rcases pol7_four huv huv' a2' (by rw [mul_neg, hp]; norm_num) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · right; right; right; right; right; left; rw [e6]; exact Prod.ext a (by show y = -v; linarith)
      · right; right; right; right; left; rw [e5]; exact Prod.ext a (by show y = -u; linarith)
      · right; right; right; right; right; right; right; rw [e8]; exact Prod.ext a (by show y = v; linarith)
      · right; right; right; right; right; right; left; rw [e7]; exact Prod.ext a (by show y = u; linarith)
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨⟨π / 12, by rw [h, k1]; norm_num⟩, ⟨π / 12, h⟩⟩
    · exact ⟨⟨5 * π / 12, by rw [h, k2]; norm_num⟩, ⟨5 * π / 12, h⟩⟩
    · exact ⟨⟨13 * π / 12, by rw [h, k3]; norm_num⟩, ⟨13 * π / 12, h⟩⟩
    · exact ⟨⟨17 * π / 12, by rw [h, k4]; norm_num⟩, ⟨17 * π / 12, h⟩⟩
    · exact ⟨⟨7 * π / 12, by rw [h, k5]; norm_num⟩, ⟨7 * π / 12 + π, h.trans (pol7_pp 1 _)⟩⟩
    · exact ⟨⟨11 * π / 12, by rw [h, k6]; norm_num⟩, ⟨11 * π / 12 + π, h.trans (pol7_pp 1 _)⟩⟩
    · exact ⟨⟨19 * π / 12, by rw [h, k7]; norm_num⟩, ⟨19 * π / 12 + π, h.trans (pol7_pp 1 _)⟩⟩
    · exact ⟨⟨23 * π / 12, by rw [h, k8]; norm_num⟩, ⟨23 * π / 12 + π, h.trans (pol7_pp 1 _)⟩⟩

private lemma pol7_c23 : cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]

private lemma pol7_s23 : sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]

private lemma pol7_c43 : cos (4 * π / 3) = -(1 / 2) := by
  rw [show 4 * π / 3 = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]

private lemma pol7_s43 : sin (4 * π / 3) = -(√3 / 2) := by
  rw [show 4 * π / 3 = π / 3 + π by ring, sin_add_pi, sin_pi_div_three]

/-- Stitz-Zeager Exercise 11.5.29: the rose `r = 4 cos 2θ` and the circle `r = 2` meet exactly at the eight points
`(2, π/6)`, `(2, 5π/6)`, `(2, 7π/6)`, `(2, 11π/6)`, `(-2, π/3)`, `(-2, 2π/3)`, `(-2, 4π/3)`, `(-2, 5π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.29, p. 970"]
theorem exer_11_5_29 :
    polarGraphFn (fun θ => 4 * cos (2 * θ)) ∩ polarGraphFn (fun _ => (2 : ℝ)) =
      {polarPoint 2 (π / 6), polarPoint 2 (5 * π / 6), polarPoint 2 (7 * π / 6), polarPoint 2 (11 * π / 6),
        polarPoint (-2) (π / 3), polarPoint (-2) (2 * π / 3), polarPoint (-2) (4 * π / 3),
        polarPoint (-2) (5 * π / 3)} := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : polarPoint 2 (π / 6) = (√3, 1) :=
    Prod.ext (by simp only [polarPoint, cos_pi_div_six]; ring) (by simp only [polarPoint, sin_pi_div_six]; ring)
  have e2 : polarPoint 2 (5 * π / 6) = (-√3, 1) :=
    Prod.ext (by simp only [polarPoint, pol7_c56]; ring) (by simp only [polarPoint, pol7_s56]; ring)
  have e3 : polarPoint 2 (7 * π / 6) = (-√3, -1) :=
    Prod.ext (by simp only [polarPoint, pol7_c76]; ring) (by simp only [polarPoint, pol7_s76]; ring)
  have e4 : polarPoint 2 (11 * π / 6) = (√3, -1) :=
    Prod.ext (by simp only [polarPoint, pol7_c116]; ring) (by simp only [polarPoint, pol7_s116]; ring)
  have e5 : polarPoint (-2) (π / 3) = (-1, -√3) :=
    Prod.ext (by simp only [polarPoint, cos_pi_div_three]; ring) (by simp only [polarPoint, sin_pi_div_three]; ring)
  have e6 : polarPoint (-2) (2 * π / 3) = (1, -√3) :=
    Prod.ext (by simp only [polarPoint, pol7_c23]; ring) (by simp only [polarPoint, pol7_s23]; ring)
  have e7 : polarPoint (-2) (4 * π / 3) = (1, √3) :=
    Prod.ext (by simp only [polarPoint, pol7_c43]; ring) (by simp only [polarPoint, pol7_s43]; ring)
  have e8 : polarPoint (-2) (5 * π / 3) = (-1, √3) :=
    Prod.ext (by simp only [polarPoint, pol7_c53]; ring) (by simp only [polarPoint, pol7_s53]; ring)
  have k1 : cos (2 * (π / 6)) = 1 / 2 := by rw [show 2 * (π / 6) = π / 3 by ring, cos_pi_div_three]
  have k2 : cos (2 * (5 * π / 6)) = 1 / 2 := by rw [show 2 * (5 * π / 6) = 5 * π / 3 by ring, pol7_c53]
  have k3 : cos (2 * (7 * π / 6)) = 1 / 2 := by
    rw [show 2 * (7 * π / 6) = π / 3 + 2 * π by ring, cos_add_two_pi, cos_pi_div_three]
  have k4 : cos (2 * (11 * π / 6)) = 1 / 2 := by
    rw [show 2 * (11 * π / 6) = 5 * π / 3 + 2 * π by ring, cos_add_two_pi, pol7_c53]
  have k5 : cos (2 * (π / 3)) = -(1 / 2) := by rw [show 2 * (π / 3) = 2 * π / 3 by ring, pol7_c23]
  have k6 : cos (2 * (2 * π / 3)) = -(1 / 2) := by rw [show 2 * (2 * π / 3) = 4 * π / 3 by ring, pol7_c43]
  have k7 : cos (2 * (4 * π / 3)) = -(1 / 2) := by
    rw [show 2 * (4 * π / 3) = 2 * π / 3 + 2 * π by ring, cos_add_two_pi, pol7_c23]
  have k8 : cos (2 * (5 * π / 3)) = -(1 / 2) := by
    rw [show 2 * (5 * π / 3) = 4 * π / 3 + 2 * π by ring, cos_add_two_pi, pol7_c43]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h3'⟩⟩
    simp only [polarPoint, Prod.mk.injEq] at h1 h3'
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hx2, hy2⟩ := h3'
    obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = 4 * cos (2 * θ1) := ⟨_, rfl⟩
    rw [← hr1] at hx hy
    have a1 : x ^ 2 + y ^ 2 = r1 ^ 2 := by
      rw [hx, hy]; linear_combination r1 ^ 2 * sin_sq_add_cos_sq θ1
    have a2 : x ^ 2 + y ^ 2 = 4 := by
      rw [hx2, hy2]; linear_combination 4 * sin_sq_add_cos_sq θ2
    have hr2 : (r1 - 2) * (r1 + 2) = 0 := by nlinarith
    have hd : x ^ 2 - y ^ 2 = r1 ^ 2 * (r1 / 4) := by
      have hc : cos (2 * θ1) = r1 / 4 := by rw [hr1]; ring
      rw [hx, hy, ← hc, cos_two_mul]; linear_combination (-r1 ^ 2) * sin_sq_add_cos_sq θ1
    rcases mul_eq_zero.mp hr2 with h | h
    · have hr : r1 = 2 := by linarith
      rw [hr] at hd
      have hx3 : (x - √3) * (x + √3) = 0 := by
        have : (x - √3) * (x + √3) = x ^ 2 - √3 ^ 2 := by ring
        rw [this, h3]; linarith
      have hy3 : (y - 1) * (y + 1) = 0 := by
        have : (y - 1) * (y + 1) = y ^ 2 - 1 ^ 2 := by ring
        rw [this]; linarith
      rcases mul_eq_zero.mp hx3 with a | a <;> rcases mul_eq_zero.mp hy3 with b | b
      · left; rw [e1]; exact Prod.ext (by show x = √3; linarith) (by show y = 1; linarith)
      · right; right; right; left; rw [e4]; exact Prod.ext (by show x = √3; linarith) (by show y = -1; linarith)
      · right; left; rw [e2]; exact Prod.ext (by show x = -√3; linarith) (by show y = 1; linarith)
      · right; right; left; rw [e3]; exact Prod.ext (by show x = -√3; linarith) (by show y = -1; linarith)
    · have hr : r1 = -2 := by linarith
      rw [hr] at hd
      have hx3 : (x - 1) * (x + 1) = 0 := by
        have : (x - 1) * (x + 1) = x ^ 2 - 1 ^ 2 := by ring
        rw [this]; linarith
      have hy3 : (y - √3) * (y + √3) = 0 := by
        have : (y - √3) * (y + √3) = y ^ 2 - √3 ^ 2 := by ring
        rw [this, h3]; linarith
      rcases mul_eq_zero.mp hx3 with a | a <;> rcases mul_eq_zero.mp hy3 with b | b
      · right; right; right; right; right; right; left; rw [e7]
        exact Prod.ext (by show x = 1; linarith) (by show y = √3; linarith)
      · right; right; right; right; right; left; rw [e6]
        exact Prod.ext (by show x = 1; linarith) (by show y = -√3; linarith)
      · right; right; right; right; right; right; right; rw [e8]
        exact Prod.ext (by show x = -1; linarith) (by show y = √3; linarith)
      · right; right; right; right; left; rw [e5]
        exact Prod.ext (by show x = -1; linarith) (by show y = -√3; linarith)
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨⟨π / 6, by rw [h, k1]; norm_num⟩, ⟨π / 6, h⟩⟩
    · exact ⟨⟨5 * π / 6, by rw [h, k2]; norm_num⟩, ⟨5 * π / 6, h⟩⟩
    · exact ⟨⟨7 * π / 6, by rw [h, k3]; norm_num⟩, ⟨7 * π / 6, h⟩⟩
    · exact ⟨⟨11 * π / 6, by rw [h, k4]; norm_num⟩, ⟨11 * π / 6, h⟩⟩
    · exact ⟨⟨π / 3, by rw [h, k5]; norm_num⟩, ⟨π / 3 + π, h.trans (pol7_pp 2 _)⟩⟩
    · exact ⟨⟨2 * π / 3, by rw [h, k6]; norm_num⟩, ⟨2 * π / 3 + π, h.trans (pol7_pp 2 _)⟩⟩
    · exact ⟨⟨4 * π / 3, by rw [h, k7]; norm_num⟩, ⟨4 * π / 3 + π, h.trans (pol7_pp 2 _)⟩⟩
    · exact ⟨⟨5 * π / 3, by rw [h, k8]; norm_num⟩, ⟨5 * π / 3 + π, h.trans (pol7_pp 2 _)⟩⟩

private lemma pol7_c34 : cos (3 * π / 4) = -(√2 / 2) := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]

private lemma pol7_s34 : sin (3 * π / 4) = √2 / 2 := by
  rw [show 3 * π / 4 = π - π / 4 by ring, sin_pi_sub, sin_pi_div_four]

private lemma pol7_c74 : cos (7 * π / 4) = √2 / 2 := by
  rw [show 7 * π / 4 = -(π / 4) + 2 * π by ring, cos_add_two_pi, cos_neg, cos_pi_div_four]

private lemma pol7_s74 : sin (7 * π / 4) = -(√2 / 2) := by
  rw [show 7 * π / 4 = -(π / 4) + 2 * π by ring, sin_add_two_pi, sin_neg, sin_pi_div_four]

/-- Stitz-Zeager Exercise 11.5.22: the cardioids `r = 1 + sin θ` and `r = 1 - cos θ` meet exactly at the pole and
the points `((2 + √2)/2, 3π/4)` and `((2 - √2)/2, 7π/4)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.22, p. 970"]
theorem exer_11_5_22 :
    polarGraphFn (fun θ => 1 + sin θ) ∩ polarGraphFn (fun θ => 1 - cos θ) =
      {(0, 0), polarPoint ((2 + √2) / 2) (3 * π / 4), polarPoint ((2 - √2) / 2) (7 * π / 4)} := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : polarPoint ((2 + √2) / 2) (3 * π / 4) = (-(√2 + 1) / 2, (√2 + 1) / 2) :=
    Prod.ext (by simp only [polarPoint, pol7_c34]; linear_combination (-1 / 4) * h2)
      (by simp only [polarPoint, pol7_s34]; linear_combination (1 / 4) * h2)
  have e2 : polarPoint ((2 - √2) / 2) (7 * π / 4) = ((√2 - 1) / 2, -(√2 - 1) / 2) :=
    Prod.ext (by simp only [polarPoint, pol7_c74]; linear_combination (-1 / 4) * h2)
      (by simp only [polarPoint, pol7_s74]; linear_combination (1 / 4) * h2)
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, polarGraphFn, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨θ1, h1⟩, ⟨θ2, h3'⟩⟩
    simp only [polarPoint, Prod.mk.injEq] at h1 h3'
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hx2, hy2⟩ := h3'
    have P1 : (x ^ 2 + y ^ 2 - y) ^ 2 = x ^ 2 + y ^ 2 := by
      have a1 : x ^ 2 + y ^ 2 = (1 + sin θ1) ^ 2 := by
        rw [hx, hy]; linear_combination (1 + sin θ1) ^ 2 * sin_sq_add_cos_sq θ1
      have a2 : x ^ 2 + y ^ 2 - y = 1 + sin θ1 := by
        rw [a1, hy]; ring
      rw [a2, a1]
    have P2 : (x ^ 2 + y ^ 2 + x) ^ 2 = x ^ 2 + y ^ 2 := by
      have a1 : x ^ 2 + y ^ 2 = (1 - cos θ2) ^ 2 := by
        rw [hx2, hy2]; linear_combination (1 - cos θ2) ^ 2 * sin_sq_add_cos_sq θ2
      have a2 : x ^ 2 + y ^ 2 + x = 1 - cos θ2 := by
        rw [a1, hx2]; ring
      rw [a2, a1]
    have key : (x + y) * (2 * (x ^ 2 + y ^ 2) + x - y) = 0 := by
      have : (x + y) * (2 * (x ^ 2 + y ^ 2) + x - y) = (x ^ 2 + y ^ 2 + x) ^ 2 - (x ^ 2 + y ^ 2 - y) ^ 2 := by ring
      rw [this, P1, P2]; ring
    rcases mul_eq_zero.mp key with hA | hB
    · have hy' : y = -x := by linarith
      rw [hy'] at P2
      have hx0 : x ^ 2 * (4 * x ^ 2 + 4 * x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hx0 with h | h
      · left
        have : x = 0 := by nlinarith [sq_nonneg x]
        rw [hy', this]; simp
      · right
        have h' : (2 * x + 1 - √2) * (2 * x + 1 + √2) = 0 := by nlinarith
        rcases mul_eq_zero.mp h' with c | c
        · right; rw [e2]; exact Prod.ext (by show x = (√2 - 1) / 2; linarith) (by show y = -(√2 - 1) / 2; linarith)
        · left; rw [e1]; exact Prod.ext (by show x = -(√2 + 1) / 2; linarith) (by show y = (√2 + 1) / 2; linarith)
    · left
      have hS : x ^ 2 + y ^ 2 = (y - x) / 2 := by linarith
      have e : (x + y) ^ 2 = 2 * (y - x) := by
        have h := P2
        rw [hS] at h
        linear_combination 4 * h
      have hb : (y - x) * (y - x + 1) = 0 := by nlinarith [e, hS]
      rcases mul_eq_zero.mp hb with c | c
      · have hyx : y = x := by linarith
        rw [hyx] at e
        have : x = 0 := by nlinarith [sq_nonneg x]
        rw [hyx, this]
      · exfalso; nlinarith [sq_nonneg (x + y)]
  · rintro (h | h | h)
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨3 * π / 2, ?_⟩, ⟨0, ?_⟩⟩
      · rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; simp [polarPoint]
      · simp [polarPoint]
    · refine ⟨⟨3 * π / 4, ?_⟩, ⟨3 * π / 4, ?_⟩⟩ <;> rw [h]
      · rw [pol7_s34]; congr 1; ring
      · rw [pol7_c34]; congr 1; ring
    · refine ⟨⟨7 * π / 4, ?_⟩, ⟨7 * π / 4, ?_⟩⟩ <;> rw [h]
      · rw [pol7_s74]; congr 1; ring
      · rw [pol7_c74]; congr 1; ring

end UndergradKB.Precalculus.Course
