import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 3.1 -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter

private lemma w7_rm (q : ℝ[X]) (a : ℝ) (n : ℕ) (h : q.eval a ≠ 0) :
    (q * (X - C a) ^ n).rootMultiplicity a = n := by
  have hq : q ≠ 0 := fun h0 => h (by simp [h0])
  rw [rootMultiplicity_mul_X_sub_C_pow hq, rootMultiplicity_eq_zero (by simpa [IsRoot] using h)]
  simp

private lemma w7_rm' (p q : ℝ[X]) (a : ℝ) (n : ℕ) (hp : p = q * (X - C a) ^ n)
    (h : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  rw [hp]; exact w7_rm q a n h

/-- Positive leading coefficient of positive degree: `p(x) → +∞` as `x → +∞`. -/
private lemma w7_top_pos (p : ℝ[X]) (hd : 0 < p.natDegree) (hl : 0 < p.leadingCoeff) :
    Tendsto (fun x : ℝ => p.eval x) atTop atTop := by
  apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
  · have hp : p ≠ 0 := fun h => by rw [h] at hl; simp at hl
    rw [degree_eq_natDegree hp]; exact_mod_cast hd
  · exact hl.le

/-- Negative leading coefficient of positive degree: `p(x) → -∞` as `x → +∞`. -/
private lemma w7_top_neg (p : ℝ[X]) (hd : 0 < p.natDegree) (hl : p.leadingCoeff < 0) :
    Tendsto (fun x : ℝ => p.eval x) atTop atBot := by
  apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
  · have hp : p ≠ 0 := fun h => by rw [h] at hl; simp at hl
    rw [degree_eq_natDegree hp]; exact_mod_cast hd
  · exact hl.le

/-- Reduce the behaviour at `-∞` to that at `+∞` through `x ↦ -x`. -/
private lemma w7_bot (f g : ℝ[X]) (hg : ∀ x : ℝ, g.eval x = f.eval (-x)) (L : Filter ℝ)
    (h : Tendsto (fun x : ℝ => g.eval x) atTop L) : Tendsto (fun x : ℝ => f.eval x) atBot L := by
  have := h.comp tendsto_neg_atBot_atTop
  refine this.congr (fun x => ?_)
  simp [Function.comp, hg]

/-! ## Section 3.1 -/

/-- Stitz-Zeager Exercise 3.1.3: `q(r) = 1 - 16r⁴` has degree `4`, leading coefficient `-16`,
constant term `1`, and tends to `-∞` at both ends. -/
@[kb "stitzzeager2013" "Exercise 3.1.3, p. 258"]
theorem exer_3_1_3 (q : ℝ[X]) (hq : q = 1 - 16 * X ^ 4) :
    q.natDegree = 4 ∧ q.leadingCoeff = -16 ∧ q.coeff 0 = 1 ∧
      Tendsto (fun x : ℝ => q.eval x) atBot atBot ∧ Tendsto (fun x : ℝ => q.eval x) atTop atBot := by
  subst hq
  have hd : (1 - 16 * X ^ 4 : ℝ[X]).natDegree = 4 := by compute_degree!
  have hl : (1 - 16 * X ^ 4 : ℝ[X]).leadingCoeff = -16 := by
    rw [leadingCoeff, hd]; compute_degree!
  have ht := w7_top_neg (1 - 16 * X ^ 4 : ℝ[X]) (by omega) (by rw [hl]; norm_num)
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero]; simp, ?_, ht⟩
  refine w7_bot _ (1 - 16 * X ^ 4 : ℝ[X]) (fun x => ?_) _ ht
  simp; ring

/-- Stitz-Zeager Exercise 3.1.4: `Z(b) = 42b - b³` has degree `3`, leading coefficient `-1`,
constant term `0`, tends to `+∞` as `b → -∞` and to `-∞` as `b → +∞`. -/
@[kb "stitzzeager2013" "Exercise 3.1.4, p. 258"]
theorem exer_3_1_4 (Z : ℝ[X]) (hZ : Z = 42 * X - X ^ 3) :
    Z.natDegree = 3 ∧ Z.leadingCoeff = -1 ∧ Z.coeff 0 = 0 ∧
      Tendsto (fun x : ℝ => Z.eval x) atBot atTop ∧ Tendsto (fun x : ℝ => Z.eval x) atTop atBot := by
  subst hZ
  have hd : (42 * X - X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  have hl : (42 * X - X ^ 3 : ℝ[X]).leadingCoeff = -1 := by
    rw [leadingCoeff, hd]; compute_degree!
  have hd' : (X ^ 3 - 42 * X : ℝ[X]).natDegree = 3 := by compute_degree!
  have hl' : (X ^ 3 - 42 * X : ℝ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff, hd']; compute_degree!
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero]; simp, ?_,
    w7_top_neg _ (by omega) (by rw [hl]; norm_num)⟩
  refine w7_bot _ (X ^ 3 - 42 * X : ℝ[X]) (fun x => ?_) _
    (w7_top_pos _ (by omega) (by rw [hl']; norm_num))
  simp; ring

/-- Stitz-Zeager Exercise 3.1.5: `f(x) = √3 x¹⁷ + 22.5 x¹⁰ - π x⁷ + 13` has degree `17`, leading
coefficient `√3`, constant term `13`, tends to `-∞` at `-∞` and to `+∞` at `+∞`. -/
@[kb "stitzzeager2013" "Exercise 3.1.5, p. 258"]
theorem exer_3_1_5 (f : ℝ[X])
    (hf : f = C (Real.sqrt 3) * X ^ 17 + C (45 / 2 : ℝ) * X ^ 10 - C Real.pi * X ^ 7 + C 13) :
    f.natDegree = 17 ∧ f.leadingCoeff = Real.sqrt 3 ∧ f.coeff 0 = 13 ∧
      Tendsto (fun x : ℝ => f.eval x) atBot atBot ∧ Tendsto (fun x : ℝ => f.eval x) atTop atTop := by
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hd : f.natDegree = 17 := by rw [hf]; compute_degree!
  have hl : f.leadingCoeff = Real.sqrt 3 := by
    rw [leadingCoeff, hd, hf]; compute_degree!
  set g : ℝ[X] := -(C (Real.sqrt 3) * X ^ 17) + C (45 / 2 : ℝ) * X ^ 10 + C Real.pi * X ^ 7 + C 13
    with hgdef
  have hgd : g.natDegree = 17 := by rw [hgdef]; compute_degree!
  have hgl : g.leadingCoeff = -Real.sqrt 3 := by
    rw [leadingCoeff, hgd, hgdef]; compute_degree!
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero, hf]; simp, ?_, w7_top_pos f (by omega) (by rw [hl]; exact h3p)⟩
  refine w7_bot f g (fun x => ?_) _ (w7_top_neg g (by omega) (by rw [hgl]; linarith))
  rw [hgdef, hf]; simp; ring

/-- Stitz-Zeager Exercise 3.1.6: `s(t) = -4.9t² + v₀t + s₀` has degree `2`, leading coefficient
`-4.9`, constant term `s₀`, and tends to `-∞` at both ends. -/
@[kb "stitzzeager2013" "Exercise 3.1.6, p. 258"]
theorem exer_3_1_6 (v₀ s₀ : ℝ) (s : ℝ[X])
    (hs : s = C (-49 / 10 : ℝ) * X ^ 2 + C v₀ * X + C s₀) :
    s.natDegree = 2 ∧ s.leadingCoeff = -49 / 10 ∧ s.coeff 0 = s₀ ∧
      Tendsto (fun x : ℝ => s.eval x) atBot atBot ∧ Tendsto (fun x : ℝ => s.eval x) atTop atBot := by
  have hd : s.natDegree = 2 := by rw [hs]; compute_degree!
  have hl : s.leadingCoeff = -49 / 10 := by rw [leadingCoeff, hd, hs]; compute_degree!
  have ht := w7_top_neg s (by omega) (by rw [hl]; norm_num)
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero, hs]; simp, ?_, ht⟩
  set g : ℝ[X] := C (-49 / 10 : ℝ) * X ^ 2 - C v₀ * X + C s₀ with hgdef
  have hgd : g.natDegree = 2 := by rw [hgdef]; compute_degree!
  have hgl : g.leadingCoeff = -49 / 10 := by rw [leadingCoeff, hgd, hgdef]; compute_degree!
  refine w7_bot s g (fun x => ?_) _ (w7_top_neg g (by omega) (by rw [hgl]; norm_num))
  rw [hgdef, hs]; simp; ring

/-- Stitz-Zeager Exercise 3.1.10: `G(t) = 4(t - 2)²(t + 1/2)` has degree `3`, leading coefficient `4`,
constant term `8`, and tends to `-∞` at `-∞` and to `+∞` at `+∞`. -/
@[kb "stitzzeager2013" "Exercise 3.1.10, p. 258"]
theorem exer_3_1_10 (G : ℝ[X]) (hG : G = 4 * (X - 2) ^ 2 * (X + C (1 / 2 : ℝ))) :
    G.natDegree = 3 ∧ G.leadingCoeff = 4 ∧ G.coeff 0 = 8 ∧
      Tendsto (fun x : ℝ => G.eval x) atBot atBot ∧ Tendsto (fun x : ℝ => G.eval x) atTop atTop := by
  have e : G = 4 * X ^ 3 - 14 * X ^ 2 + 8 * X + 8 := by
    rw [hG]
    have : (C (1 / 2 : ℝ)) * 2 = (1 : ℝ[X]) := by
      rw [← map_ofNat C 2, ← C_mul]; norm_num
    linear_combination (2 * (X - 2) ^ 2) * this
  have hd : G.natDegree = 3 := by rw [e]; compute_degree!
  have hl : G.leadingCoeff = 4 := by rw [leadingCoeff, hd, e]; compute_degree!
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero, e]; simp, ?_,
    w7_top_pos G (by omega) (by rw [hl]; norm_num)⟩
  have hd2 : (8 - 8 * X - 14 * X ^ 2 - 4 * X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  have hl2 : (8 - 8 * X - 14 * X ^ 2 - 4 * X ^ 3 : ℝ[X]).leadingCoeff = -4 := by
    rw [leadingCoeff, hd2]; compute_degree!
  refine w7_bot G (8 - 8 * X - 14 * X ^ 2 - 4 * X ^ 3) (fun x => ?_) _
    (w7_top_neg _ (by omega) (by rw [hl2]; norm_num))
  rw [e]; simp; ring

/-- Stitz-Zeager Exercise 3.1.14: `g(x) = (2x + 1)²(x - 3)` has the zero `-1/2` of multiplicity `2`,
the zero `3` of multiplicity `1`, and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.14, p. 258"]
theorem exer_3_1_14 (g : ℝ[X]) (hg : g = (2 * X + 1) ^ 2 * (X - 3)) :
    g.rootMultiplicity (-1 / 2) = 2 ∧ g.rootMultiplicity 3 = 1 ∧
      ∀ x : ℝ, g.eval x = 0 ↔ x = -1 / 2 ∨ x = 3 := by
  refine ⟨w7_rm' _ (4 * (X - 3)) (-1 / 2) 2 ?_ (by simp; norm_num),
    w7_rm' _ ((2 * X + 1) ^ 2) 3 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [hg]
    have : (C (-1 / 2 : ℝ)) * 2 = (-1 : ℝ[X]) := by
      rw [← map_ofNat C 2, ← C_mul]; norm_num
    linear_combination ((X - 3) * (4 * X + 1 - 2 * C (-1 / 2 : ℝ))) * this
  · rw [hg]; simp only [map_ofNat]; ring
  · simp only [hg, eval_mul, eval_pow, eval_add, eval_ofNat, eval_X, eval_sub, eval_one, mul_eq_zero,
      pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith

/-- Stitz-Zeager Exercise 3.1.21: `g(x) = (x + 2)³ + 1` has domain and range all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 3.1.21, p. 258"]
theorem exer_3_1_21 : Set.range (fun x : ℝ => (x + 2) ^ 3 + 1) = Set.univ := by
  ext y
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨principalRoot 3 (y - 1) - 2, ?_⟩
  have := principalRoot_pow (n := 3) (x := y - 1) (by norm_num) (Or.inl (by decide))
  rw [sub_add_cancel, this]; ring

/-- Stitz-Zeager Exercise 3.1.24: `g(x) = -x⁵ - 3` has range all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 3.1.24, p. 258"]
theorem exer_3_1_24 : Set.range (fun x : ℝ => -x ^ 5 - 3) = Set.univ := by
  ext y
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨principalRoot 5 (-(y + 3)), ?_⟩
  have := principalRoot_pow (n := 5) (x := -(y + 3)) (by norm_num) (Or.inl (by decide))
  rw [this]; ring

/-- Stitz-Zeager Exercise 3.1.25: `g(x) = (x + 1)⁵ + 10` has range all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 3.1.25, p. 258"]
theorem exer_3_1_25 : Set.range (fun x : ℝ => (x + 1) ^ 5 + 10) = Set.univ := by
  ext y
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨principalRoot 5 (y - 10) - 1, ?_⟩
  have := principalRoot_pow (n := 5) (x := y - 10) (by norm_num) (Or.inl (by decide))
  rw [sub_add_cancel, this]; ring

/-- Stitz-Zeager Exercise 3.1.26: the range of `g(x) = 8 - x⁶` is `(-∞, 8]`. -/
@[kb "stitzzeager2013" "Exercise 3.1.26, p. 258"]
theorem exer_3_1_26 : Set.range (fun x : ℝ => 8 - x ^ 6) = Set.Iic 8 := by
  ext y
  simp only [Set.mem_range, Set.mem_Iic]
  constructor
  · rintro ⟨x, rfl⟩
    have : 0 ≤ x ^ 6 := by positivity
    linarith
  · intro hy
    have h0 : 0 ≤ 8 - y := by linarith
    refine ⟨principalRoot 6 (8 - y), ?_⟩
    have := principalRoot_pow (n := 6) (x := 8 - y) (by norm_num) (Or.inr h0)
    rw [this]; ring

/-- Stitz-Zeager Exercise 3.1.28: a box folded from an `8.5 × 11` sheet by cutting squares of side
`x` has volume `V(x) = x(8.5 - 2x)(11 - 2x) = 4x³ - 39x² + 93.5x` on `0 < x < 4.25`; the maximum
`V ≈ 66.15` occurs at `x = (39 - √399)/12 ≈ 1.58`. -/
@[kb "stitzzeager2013" "Exercise 3.1.28, p. 258"]
theorem exer_3_1_28 (V : ℝ → ℝ) (hV : ∀ x, V x = x * (17 / 2 - 2 * x) * (11 - 2 * x)) :
    (∀ x, V x = 4 * x ^ 3 - 39 * x ^ 2 + 187 / 2 * x) ∧
      (∀ x, 0 < x → x < 17 / 4 → V x ≤ V ((39 - Real.sqrt 399) / 12)) ∧
      1.58 < (39 - Real.sqrt 399) / 12 ∧ (39 - Real.sqrt 399) / 12 < 1.59 ∧
      66.14 < V ((39 - Real.sqrt 399) / 12) ∧ V ((39 - Real.sqrt 399) / 12) < 66.16 := by
  have hs : Real.sqrt 399 ^ 2 = 399 := Real.sq_sqrt (by norm_num)
  have hlo : (19.97 : ℝ) < Real.sqrt 399 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 399 < 19.98 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hV2 : ∀ x, V x = 4 * x ^ 3 - 39 * x ^ 2 + 187 / 2 * x := fun x => by rw [hV]; ring
  have hx0 : 1.58 < (39 - Real.sqrt 399) / 12 ∧ (39 - Real.sqrt 399) / 12 < 1.59 :=
    ⟨by linarith, by linarith⟩
  have hder : 12 * ((39 - Real.sqrt 399) / 12) ^ 2 - 78 * ((39 - Real.sqrt 399) / 12) + 187 / 2 = 0 := by
    linear_combination (1 / 12) * hs
  have key : ∀ x, V ((39 - Real.sqrt 399) / 12) - V x =
      (x - (39 - Real.sqrt 399) / 12) ^ 2 * (39 - 8 * ((39 - Real.sqrt 399) / 12) - 4 * x) := by
    intro x
    rw [hV2, hV2]
    linear_combination (((39 - Real.sqrt 399) / 12) - x) * hder
  refine ⟨hV2, fun x hx0' hx1 => ?_, hx0.1, hx0.2, ?_, ?_⟩
  · have := key x
    have h2 : 0 ≤ (x - (39 - Real.sqrt 399) / 12) ^ 2 * (39 - 8 * ((39 - Real.sqrt 399) / 12) - 4 * x) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.2])
    linarith
  · have h1 := key (1.58)
    have h2 : 0 ≤ (1.58 - (39 - Real.sqrt 399) / 12) ^ 2 *
        (39 - 8 * ((39 - Real.sqrt 399) / 12) - 4 * 1.58) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.2])
    have h3 : V 1.58 = 66.147648 := by rw [hV]; norm_num
    linarith
  · have h1 := key (1.58)
    have h3 : V 1.58 = 66.147648 := by rw [hV]; norm_num
    have h4 : (1.58 - (39 - Real.sqrt 399) / 12) ^ 2 < 0.0001 := by nlinarith [hx0.1, hx0.2]
    have h5 : 0 < (39 - 8 * ((39 - Real.sqrt 399) / 12) - 4 * 1.58) := by linarith [hx0.2]
    have h6 : (39 - 8 * ((39 - Real.sqrt 399) / 12) - 4 * 1.58) < 30 := by linarith [hx0.1]
    have h7 := mul_lt_mul'' h4 h6 (sq_nonneg _) h5.le
    nlinarith

/-- Stitz-Zeager Exercise 3.1.29: the revenue `R(x) = -5x³ + 35x² + 155x` is maximal on `x ≥ 0` at
`x = (7 + √142)/3 ≈ 6.305` with maximum about `1115.417`. -/
@[kb "stitzzeager2013" "Exercise 3.1.29, p. 259"]
theorem exer_3_1_29 (R : ℝ → ℝ) (hR : ∀ x, R x = -5 * x ^ 3 + 35 * x ^ 2 + 155 * x) :
    (∀ x, 0 ≤ x → R x ≤ R ((7 + Real.sqrt 142) / 3)) ∧
      6.30 < (7 + Real.sqrt 142) / 3 ∧ (7 + Real.sqrt 142) / 3 < 6.31 ∧
      1115.41 < R ((7 + Real.sqrt 142) / 3) ∧ R ((7 + Real.sqrt 142) / 3) < 1115.42 := by
  have hs : Real.sqrt 142 ^ 2 = 142 := Real.sq_sqrt (by norm_num)
  have hlo : (11.91 : ℝ) < Real.sqrt 142 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 142 < 11.92 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hder : 15 * ((7 + Real.sqrt 142) / 3) ^ 2 - 70 * ((7 + Real.sqrt 142) / 3) - 155 = 0 := by
    linear_combination (5 / 3) * hs
  have key : ∀ x, R ((7 + Real.sqrt 142) / 3) - R x =
      (x - (7 + Real.sqrt 142) / 3) ^ 2 * (5 * x - 35 + 10 * ((7 + Real.sqrt 142) / 3)) := by
    intro x
    rw [hR, hR]
    linear_combination (-(((7 + Real.sqrt 142) / 3) - x)) * hder
  have hx0 : 6.30 < (7 + Real.sqrt 142) / 3 ∧ (7 + Real.sqrt 142) / 3 < 6.31 :=
    ⟨by linarith, by linarith⟩
  refine ⟨fun x hx => ?_, hx0.1, hx0.2, ?_, ?_⟩
  · have := key x
    have h2 : 0 ≤ (x - (7 + Real.sqrt 142) / 3) ^ 2 * (5 * x - 35 + 10 * ((7 + Real.sqrt 142) / 3)) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.1])
    linarith
  · have h1 := key 6.3
    have h2 : 0 ≤ (6.3 - (7 + Real.sqrt 142) / 3) ^ 2 *
        (5 * 6.3 - 35 + 10 * ((7 + Real.sqrt 142) / 3)) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.1])
    have h3 : R 6.3 = 1115.415 := by rw [hR]; norm_num
    linarith
  · have h1 := key 6.3
    have h3 : R 6.3 = 1115.415 := by rw [hR]; norm_num
    have h4 : (6.3 - (7 + Real.sqrt 142) / 3) ^ 2 < 0.0001 := by nlinarith [hx0.1, hx0.2]
    have h5 : 0 < (5 * 6.3 - 35 + 10 * ((7 + Real.sqrt 142) / 3)) := by linarith [hx0.1]
    have h6 : (5 * 6.3 - 35 + 10 * ((7 + Real.sqrt 142) / 3)) < 100 := by linarith [hx0.2]
    have h7 := mul_lt_mul'' h4 h6 (sq_nonneg _) h5.le
    nlinarith

/-- Stitz-Zeager Exercise 3.1.31: the profit `P(x) = -5x³ + 35x² - 45x - 25` is maximal on `x ≥ 0` at
`x = (7 + √22)/3 ≈ 3.897` with maximum about `35.255`. -/
@[kb "stitzzeager2013" "Exercise 3.1.31, p. 259"]
theorem exer_3_1_31 (P : ℝ → ℝ) (hP : ∀ x, P x = -5 * x ^ 3 + 35 * x ^ 2 - 45 * x - 25) :
    (∀ x, 0 ≤ x → P x ≤ P ((7 + Real.sqrt 22) / 3)) ∧
      3.89 < (7 + Real.sqrt 22) / 3 ∧ (7 + Real.sqrt 22) / 3 < 3.9 ∧
      35.25 < P ((7 + Real.sqrt 22) / 3) ∧ P ((7 + Real.sqrt 22) / 3) < 35.26 := by
  have hs : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)
  have hlo : (4.69 : ℝ) < Real.sqrt 22 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 22 < 4.7 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hder : 15 * ((7 + Real.sqrt 22) / 3) ^ 2 - 70 * ((7 + Real.sqrt 22) / 3) + 45 = 0 := by
    linear_combination (5 / 3) * hs
  have key : ∀ x, P ((7 + Real.sqrt 22) / 3) - P x =
      (x - (7 + Real.sqrt 22) / 3) ^ 2 * (5 * x - 35 + 10 * ((7 + Real.sqrt 22) / 3)) := by
    intro x
    rw [hP, hP]
    linear_combination (-(((7 + Real.sqrt 22) / 3) - x)) * hder
  have hx0 : 3.89 < (7 + Real.sqrt 22) / 3 ∧ (7 + Real.sqrt 22) / 3 < 3.9 :=
    ⟨by linarith, by linarith⟩
  refine ⟨fun x hx => ?_, hx0.1, hx0.2, ?_, ?_⟩
  · have := key x
    have h2 : 0 ≤ (x - (7 + Real.sqrt 22) / 3) ^ 2 * (5 * x - 35 + 10 * ((7 + Real.sqrt 22) / 3)) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.1])
    linarith
  · have h1 := key 3.9
    have h2 : 0 ≤ (3.9 - (7 + Real.sqrt 22) / 3) ^ 2 *
        (5 * 3.9 - 35 + 10 * ((7 + Real.sqrt 22) / 3)) :=
      mul_nonneg (sq_nonneg _) (by linarith [hx0.1])
    have h3 : P 3.9 = 35.255 := by rw [hP]; norm_num
    linarith
  · have h1 := key 3.9
    have h3 : P 3.9 = 35.255 := by rw [hP]; norm_num
    have h4 : (3.9 - (7 + Real.sqrt 22) / 3) ^ 2 < 0.0001 := by nlinarith [hx0.1, hx0.2]
    have h5 : 0 < (5 * 3.9 - 35 + 10 * ((7 + Real.sqrt 22) / 3)) := by linarith [hx0.1]
    have h6 : (5 * 3.9 - 35 + 10 * ((7 + Real.sqrt 22) / 3)) < 100 := by linarith [hx0.2]
    have h7 := mul_lt_mul'' h4 h6 (sq_nonneg _) h5.le
    nlinarith

/-- Stitz-Zeager Exercise 3.1.32: with `C(x) = .03x³ - 4.5x² + 225x + 250` and `p(x) = -1.5x + 250`,
the profit `P(x) = x p(x) - C(x)` over whole numbers of systems is largest at `x = 71`, where it is
`5910.67`. -/
@[kb "stitzzeager2013" "Exercise 3.1.32, p. 259"]
theorem exer_3_1_32 (P : ℝ → ℝ)
    (hP : ∀ x, P x = x * (-(3 / 2) * x + 250) -
      (3 / 100 * x ^ 3 - 9 / 2 * x ^ 2 + 225 * x + 250)) :
    P 71 = 591067 / 100 ∧ ∀ n : ℕ, P n ≤ P 71 := by
  have key : ∀ x : ℝ, P x - P 71 = (x - 71) * (-(3 / 100) * x ^ 2 + 87 / 100 * x + 8677 / 100) := by
    intro x; rw [hP, hP]; ring
  refine ⟨by rw [hP]; norm_num, fun n => ?_⟩
  have hn := key n
  rcases le_or_gt (n : ℝ) 70 with h | h
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hq : 0 < -(3 / 100) * (n : ℝ) ^ 2 + 87 / 100 * n + 8677 / 100 := by nlinarith
    nlinarith
  · have h71 : (71 : ℝ) ≤ n := by
      have : (70 : ℕ) < n := by exact_mod_cast h
      exact_mod_cast this
    rcases eq_or_lt_of_le h71 with h' | h'
    · rw [← h']
    · have h72 : (72 : ℝ) ≤ n := by
        have : (71 : ℕ) < n := by exact_mod_cast h'
        exact_mod_cast this
      have hq : -(3 / 100) * (n : ℝ) ^ 2 + 87 / 100 * n + 8677 / 100 < 0 := by nlinarith
      nlinarith

end UndergradKB.Precalculus.Course
