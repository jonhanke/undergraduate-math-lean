import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras
import UndergradKB.Precalculus.Course.Ch10Extra

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.6 (inverse trigonometric functions, continued)

`arccot` is `arccotR`, `arcsec`/`arccsc` are `arcsecCF`/`arccscCF` from `TrigExtras` unless noted. -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

private lemma arcsin_of {y x : ℝ} (h : sin x = y) (h1 : -(π / 2) ≤ x) (h2 : x ≤ π / 2) :
    arcsin y = x := by
  rw [← h]; exact arcsin_sin h1 h2

private lemma arccos_of {y x : ℝ} (h : cos x = y) (h1 : 0 ≤ x) (h2 : x ≤ π) : arccos y = x := by
  rw [← h]; exact arccos_cos h1 h2

private lemma arctan_of {y x : ℝ} (h : tan x = y) (h1 : -(π / 2) < x) (h2 : x < π / 2) :
    arctan y = x := by
  rw [← h]; exact arctan_tan h1 h2

private lemma arccot_of {y x : ℝ} (h : cos x / sin x = y) (h1 : 0 < x) (h2 : x < π) :
    arccotR y = x := by
  unfold arccotR
  have : y = tan (π / 2 - x) := by
    rw [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]; exact h.symm
  rw [this, arctan_tan (by linarith) (by linarith)]; ring

private lemma sqrt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : √a = b := by
  rw [h, Real.sqrt_sq hb]

private lemma arcsec_pos {x : ℝ} (h : 1 ≤ x) : arcsecCF x = arccos x⁻¹ := by
  unfold arcsecCF; simp [h]

private lemma arcsec_neg {x : ℝ} (h : ¬ 1 ≤ x) : arcsecCF x = 2 * π - arccos x⁻¹ := by
  unfold arcsecCF; simp [h]

private lemma arccsc_pos {x : ℝ} (h : 1 ≤ x) : arccscCF x = arcsin x⁻¹ := by
  unfold arccscCF; simp [h]

private lemma arccsc_neg {x : ℝ} (h : ¬ 1 ≤ x) : arccscCF x = π - arcsin x⁻¹ := by
  unfold arccscCF; simp [h]

private lemma three_half_le : (3 / 2 : ℝ) ≤ √3 := by
  have hp : 0 ≤ √3 := Real.sqrt_nonneg 3
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma c56 : cos (5 * π / 6) = -(√3 / 2) ∧ sin (5 * π / 6) = 1 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six]
  exact ⟨rfl, rfl⟩

private lemma c34 : cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2 := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]
  exact ⟨rfl, rfl⟩

private lemma c23 : cos (2 * π / 3) = -(1 / 2) ∧ sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

private lemma inv_sqrt3 : (1 : ℝ) / √3 = √3 / 3 := by
  have hp : 0 < √3 := by positivity
  field_simp; nlinarith [s3]


private lemma sq_le_iff3 (x c : ℝ) (hc : 0 < c) : x ^ 2 ≤ c ^ 2 ↔ -c ≤ x ∧ x ≤ c :=
  ⟨fun h => abs_le_of_sq_le_sq' h hc.le, fun h => sq_le_sq' h.1 h.2⟩

private lemma ge_sq_iff (x c : ℝ) (hc : 0 < c) : c ^ 2 ≤ x ^ 2 ↔ x ≤ -c ∨ c ≤ x := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    nlinarith [hn.1, hn.2]
  · rintro (h | h) <;> nlinarith

private lemma inv_abs_ge (u : ℝ) (hu : u ≠ 0) : (-1 ≤ 1 / u ∧ 1 / u ≤ 1) ↔ (1 ≤ u ∨ u ≤ -1) := by
  rcases lt_or_gt_of_ne hu with h | h
  · have h1 : 1 / u < 0 := by rw [one_div]; exact inv_lt_zero.2 h
    have e : -1 ≤ 1 / u ↔ u ≤ -1 := by
      rw [le_div_iff_of_neg h]; constructor <;> intro hh <;> linarith
    constructor
    · rintro ⟨a, _⟩; right; exact e.1 a
    · rintro (a | a)
      · linarith
      · exact ⟨e.2 a, by linarith⟩
  · have h1 : 0 < 1 / u := by positivity
    have e : 1 / u ≤ 1 ↔ 1 ≤ u := div_le_one h
    constructor
    · rintro ⟨_, b⟩; left; exact e.1 b
    · rintro (a | a)
      · exact ⟨by linarith, e.2 a⟩
      · linarith

/-- Stitz-Zeager Exercise 10.6.222: the domain of `arcsin(5x)` (argument in `[-1, 1]`) is `[-1/5, 1/5]`. -/
@[kb "stitzzeager2013" "Exercise 10.6.222, p. 858"]
theorem exer_10_6_222 : {x : ℝ | -1 ≤ 5 * x ∧ 5 * x ≤ 1} = Set.Icc (-(1 / 5)) (1 / 5) := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 10.6.223: the domain of `arccos((3x - 1)/2)` is `[-1/3, 1]`. -/
@[kb "stitzzeager2013" "Exercise 10.6.223, p. 858"]
theorem exer_10_6_223 :
    {x : ℝ | -1 ≤ (3 * x - 1) / 2 ∧ (3 * x - 1) / 2 ≤ 1} = Set.Icc (-(1 / 3)) 1 := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 10.6.224: the domain of `arcsin(2x²)` is `[-√2/2, √2/2]`. -/
@[kb "stitzzeager2013" "Exercise 10.6.224, p. 858"]
theorem exer_10_6_224 :
    {x : ℝ | -1 ≤ 2 * x ^ 2 ∧ 2 * x ^ 2 ≤ 1} = Set.Icc (-(√2 / 2)) (√2 / 2) := by
  have hp : 0 < √2 := by positivity
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  have e : 2 * x ^ 2 ≤ 1 ↔ x ^ 2 ≤ (√2 / 2) ^ 2 := by
    rw [div_pow, s2]; constructor <;> intro h <;> linarith
  rw [← sq_le_iff3 x (√2 / 2) (by positivity), ← e]
  constructor
  · rintro ⟨_, b⟩; exact b
  · intro b; exact ⟨by nlinarith [sq_nonneg x], b⟩

/-- Stitz-Zeager Exercise 10.6.225: the domain of `arccos(1/(x² - 4))` is
`(-∞, -√5] ∪ [-√3, √3] ∪ [√5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.225, p. 858"]
theorem exer_10_6_225 :
    {x : ℝ | x ^ 2 - 4 ≠ 0 ∧ -1 ≤ 1 / (x ^ 2 - 4) ∧ 1 / (x ^ 2 - 4) ≤ 1} =
      Set.Iic (-√5) ∪ Set.Icc (-√3) (√3) ∪ Set.Ici (√5) := by
  have p5 : 0 < √5 := by positivity
  have p3 : 0 < √3 := by positivity
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici]
  constructor
  · rintro ⟨hne, h⟩
    rcases (inv_abs_ge _ hne).1 h with h | h
    · have : √5 ^ 2 ≤ x ^ 2 := by rw [s5]; linarith
      rcases (ge_sq_iff x _ p5).1 this with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · have : x ^ 2 ≤ √3 ^ 2 := by rw [s3]; linarith
      exact Or.inl (Or.inr ((sq_le_iff3 x _ p3).1 this))
  · intro h
    have hne : x ^ 2 - 4 ≠ 0 := by
      intro h0
      rcases h with (h | h) | h
      · nlinarith [s5]
      · nlinarith [s3, h.1, h.2]
      · nlinarith [s5]
    refine ⟨hne, (inv_abs_ge _ hne).2 ?_⟩
    rcases h with (h | h) | h
    · left; have := (ge_sq_iff x _ p5).2 (Or.inl h); rw [s5] at this; linarith
    · right; have := (sq_le_iff3 x _ p3).2 h; rw [s3] at this; linarith
    · left; have := (ge_sq_iff x _ p5).2 (Or.inr h); rw [s5] at this; linarith

/-- Stitz-Zeager Exercise 10.6.227: the domain of `arccot(2x/(x² - 9))` is all `x` except `±3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.227, p. 858"]
theorem exer_10_6_227 :
    {x : ℝ | x ^ 2 - 9 ≠ 0} = Set.Iio (-3) ∪ Set.Ioo (-3) 3 ∪ Set.Ioi 3 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · intro h
    rcases lt_trichotomy x (-3) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact absurd (by rw [h1]; norm_num) h
    · rcases lt_trichotomy x 3 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact absurd (by rw [h2]; norm_num) h
      · exact Or.inr h2
  · intro h h0
    rcases h with (h | h) | h <;> nlinarith [h]

/-- Stitz-Zeager Exercise 10.6.228: the domain of `arctan(ln(2x - 1))` is `(1/2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.228, p. 858"]
theorem exer_10_6_228 : {x : ℝ | 0 < 2 * x - 1} = Set.Ioi (1 / 2) := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 10.6.229: the domain of `arccot(√(2x - 1))` is `[1/2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.229, p. 858"]
theorem exer_10_6_229 : {x : ℝ | 0 ≤ 2 * x - 1} = Set.Ici (1 / 2) := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_Ici]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 10.6.230: the domain of `arcsec(12x)` (`|12x| ≥ 1`) is
`(-∞, -1/12] ∪ [1/12, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.230, p. 858"]
theorem exer_10_6_230 :
    {x : ℝ | 1 ≤ |12 * x|} = Set.Iic (-(1 / 12)) ∪ Set.Ici (1 / 12) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  rw [le_abs']
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Stitz-Zeager Exercise 10.6.231: the domain of `arccsc(x + 5)` is `(-∞, -6] ∪ [-4, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.231, p. 858"]
theorem exer_10_6_231 : {x : ℝ | 1 ≤ |x + 5|} = Set.Iic (-6) ∪ Set.Ici (-4) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  rw [le_abs']
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Stitz-Zeager Exercise 10.6.232: the domain of `arcsec(x³/8)` (`|x³/8| ≥ 1`) is
`(-∞, -2] ∪ [2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.232, p. 858"]
theorem exer_10_6_232 : {x : ℝ | 1 ≤ |x ^ 3 / 8|} = Set.Iic (-2) ∪ Set.Ici 2 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  rw [le_abs']
  constructor
  · rintro (h | h)
    · left; by_contra hn; push Not at hn; nlinarith [sq_nonneg (x + 2), sq_nonneg x, sq_nonneg (x - 1)]
    · right; by_contra hn; push Not at hn
      nlinarith [sq_nonneg (x + 2), sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (x + 1)]
  · rintro (h | h)
    · left; nlinarith [sq_nonneg (x + 2), sq_nonneg x, sq_nonneg (x - 1)]
    · right; nlinarith [sq_nonneg (x - 2), sq_nonneg x, sq_nonneg (x - 1)]

/-- Stitz-Zeager Exercise 10.6.233: the domain of `arccsc(e^(2x))` (`|e^(2x)| ≥ 1`) is `[0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.233, p. 858"]
theorem exer_10_6_233 : {x : ℝ | 1 ≤ |Real.exp (2 * x)|} = Set.Ici 0 := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ici]
  rw [abs_of_pos (Real.exp_pos _), Real.one_le_exp_iff]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 10.6.234: for `|x| ≥ 1`, the angle `y` with `y ∈ [0, π]`, `y ≠ π/2` and
`sec y = x` is exactly `arccos(1/x)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.234, p. 858"]
theorem exer_10_6_234 (x : ℝ) (hx : 1 ≤ |x|) (y : ℝ) :
    (0 ≤ y ∧ y ≤ π ∧ y ≠ π / 2 ∧ (cos y)⁻¹ = x) ↔ y = arccos (1 / x) := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have h1 : |1 / x| ≤ 1 := by rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
  obtain ⟨hl, hr⟩ := abs_le.1 h1
  constructor
  · rintro ⟨a, b, _, d⟩
    have : cos y = 1 / x := by rw [← d]; simp
    rw [← this, arccos_cos a b]
  · rintro rfl
    refine ⟨arccos_nonneg _, arccos_le_pi _, ?_, ?_⟩
    · rw [Ne, arccos_eq_pi_div_two]; simpa using hx0
    · rw [cos_arccos hl hr, one_div, inv_inv]

/-- Stitz-Zeager Exercise 10.6.235: for `|x| ≥ 1`, the angle `y` with `y ∈ [-π/2, π/2]`, `y ≠ 0` and
`csc y = x` is exactly `arcsin(1/x)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.235, p. 858"]
theorem exer_10_6_235 (x : ℝ) (hx : 1 ≤ |x|) (y : ℝ) :
    (-(π / 2) ≤ y ∧ y ≤ π / 2 ∧ y ≠ 0 ∧ (sin y)⁻¹ = x) ↔ y = arcsin (1 / x) := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have h1 : |1 / x| ≤ 1 := by rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
  obtain ⟨hl, hr⟩ := abs_le.1 h1
  constructor
  · rintro ⟨a, b, _, d⟩
    have : sin y = 1 / x := by rw [← d]; simp
    rw [← this, arcsin_sin a b]
  · rintro rfl
    refine ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _, ?_, ?_⟩
    · rw [Ne, arcsin_eq_zero_iff]; simpa using hx0
    · rw [sin_arcsin hl hr, one_div, inv_inv]

/-- Stitz-Zeager Exercise 10.6.236: `arcsin x + arccos x = π/2` for `-1 ≤ x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.236, p. 858"]
theorem exer_10_6_236 (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : arcsin x + arccos x = π / 2 := by
  rw [arccos_eq_pi_div_two_sub_arcsin]; ring

/-- Stitz-Zeager Exercise 10.6.238: `arctan 1 + arctan 2 + arctan 3 = π`. -/
@[kb "stitzzeager2013" "Exercise 10.6.238, p. 858"]
theorem exer_10_6_238 : arctan 1 + arctan 2 + arctan 3 = π := by
  rw [arctan_one, add_assoc, arctan_add_eq_add_pi (by norm_num) (by norm_num),
    show ((2 : ℝ) + 3) / (1 - 2 * 3) = -1 by norm_num, arctan_neg, arctan_one]
  ring

end UndergradKB.Precalculus.Course
