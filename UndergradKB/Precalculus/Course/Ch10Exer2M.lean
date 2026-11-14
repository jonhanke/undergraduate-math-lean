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


private lemma r2le : √2 / 2 ≤ 1 := by nlinarith [s2, Real.sqrt_nonneg 2]
private lemma r3le : √3 / 2 ≤ 1 := by nlinarith [s3, Real.sqrt_nonneg 3]

private lemma cot_arccot (x : ℝ) : cos (arccotR x) / sin (arccotR x) = x := by
  unfold arccotR
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub, ← tan_eq_sin_div_cos, tan_arctan]

private lemma sec_arcsec_pos {x : ℝ} (hx : 1 ≤ x) : (cos (arcsecCF x))⁻¹ = x := by
  have h0 : 0 < x := by linarith
  rw [arcsec_pos hx, cos_arccos (by have := inv_pos.2 h0; linarith) (inv_le_one_of_one_le₀ hx),
    inv_inv]

private lemma sec_arcsec_neg {x : ℝ} (hx : x ≤ -1) : (cos (arcsecCF x))⁻¹ = x := by
  have h0 : x < 0 := by linarith
  have h1 : ¬ 1 ≤ x := by intro h; linarith
  have h2 : -1 ≤ x⁻¹ := by
    rw [inv_eq_one_div, le_div_iff_of_neg h0]; linarith
  rw [arcsec_neg h1, cos_two_pi_sub, cos_arccos h2 (by have := inv_lt_zero.2 h0; linarith), inv_inv]

private lemma sec_arcsec_lt {x : ℝ} (h0 : 0 < x) (hx : x < 1) : (cos (arcsecCF x))⁻¹ ≠ x := by
  have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ h0).2 hx.le
  rw [arcsec_neg (not_le.2 hx), arccos_eq_zero.2 h1, sub_zero, cos_two_pi, inv_one]
  exact ne_of_gt hx

private lemma csc_arccsc_pos {x : ℝ} (hx : 1 ≤ x) : (sin (arccscCF x))⁻¹ = x := by
  have h0 : 0 < x := by linarith
  rw [arccsc_pos hx, sin_arcsin (by have := inv_pos.2 h0; linarith) (inv_le_one_of_one_le₀ hx),
    inv_inv]

private lemma csc_arccsc_neg {x : ℝ} (hx : x ≤ -1) : (sin (arccscCF x))⁻¹ = x := by
  have h0 : x < 0 := by linarith
  have h1 : ¬ 1 ≤ x := by intro h; linarith
  have h2 : -1 ≤ x⁻¹ := by
    rw [inv_eq_one_div, le_div_iff_of_neg h0]; linarith
  rw [arccsc_neg h1, sin_pi_sub, sin_arcsin h2 (by have := inv_lt_zero.2 h0; linarith), inv_inv]

private lemma csc_arccsc_lt {x : ℝ} (h0 : 0 < x) (hx : x < 1) : (sin (arccscCF x))⁻¹ ≠ x := by
  have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ h0).2 hx.le
  rw [arccsc_neg (not_le.2 hx), arcsin_eq_pi_div_two.2 h1, sin_pi_sub, sin_pi_div_two, inv_one]
  exact ne_of_gt hx


private lemma tan_iff' {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

private lemma arctan_cs (y : ℝ) (hy : y ≠ 0) : cos (arctan y) ≠ 0 ∧ sin (arctan y) ≠ 0 := by
  have hc : 0 < cos (arctan y) := cos_arctan_pos y
  refine ⟨hc.ne', ?_⟩
  have h := tan_arctan y
  rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h
  rw [h]; exact mul_ne_zero hy hc.ne'

private lemma tan_sol_pos (y x : ℝ) (hy : 0 < y) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = y ↔ x = arctan y ∨ x = arctan y + π := by
  obtain ⟨a, ha⟩ : ∃ a, a = arctan y := ⟨_, rfl⟩
  have hs : tan a = y := by rw [ha]; exact tan_arctan y
  have ha0 : 0 < a := by rw [ha]; exact arctan_pos.mpr hy
  have ha1 : a < π / 2 := by rw [ha]; exact arctan_lt_pi_div_two y
  have hcs := arctan_cs y hy.ne'
  rw [← ha] at hcs
  rw [← ha, ← hs, tan_iff' hcs.1 hcs.2]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h⟩
    have hk0 : (-1 : ℝ) < k := by nlinarith
    have hk1 : (k : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
    have h2 : k < 2 := by exact_mod_cast hk1
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · left; simpa using h
    · right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩

private lemma cot_tan (x c : ℝ) : cos x / sin x = c ↔ tan x = c⁻¹ := by
  have e : cos x / sin x = (tan x)⁻¹ := by rw [tan_eq_sin_div_cos, inv_div]
  rw [e, inv_eq_iff_eq_inv]


private lemma s10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
private lemma s6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

private lemma sin_acot (x : ℝ) : sin (arccotR x) = 1 / √(1 + x ^ 2) := by
  unfold arccotR; rw [sin_pi_div_two_sub, cos_arctan]

private lemma cos_acot (x : ℝ) : cos (arccotR x) = x / √(1 + x ^ 2) := by
  unfold arccotR; rw [cos_pi_div_two_sub, sin_arctan]

private lemma sinsec_a {x : ℝ} (h1 : 0 ≤ x) (h2 : x < π / 2) : arcsecCF (cos x)⁻¹ = x := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  rw [arcsec_pos ((one_le_inv₀ hc).2 (cos_le_one x)), inv_inv,
    arccos_cos h1 (by linarith [Real.pi_pos])]

private lemma eqp' {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma sin_sq_half' (t : ℝ) : sin (t / 2) ^ 2 = 1 / 2 - cos t / 2 := by
  have h := cos_two_mul (t / 2)
  rw [mul_div_cancel₀ _ two_ne_zero] at h
  have := sin_sq_add_cos_sq (t / 2)
  linarith

/-- Stitz-Zeager Exercise 10.6.134: `sin(arccot √5) = √6/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.134, p. 856"]
theorem exer_10_6_134 : sin (arccotR √5) = √6 / 6 := by
  rw [sin_acot, s5, show (1 : ℝ) + 5 = 6 by norm_num]
  have hp : 0 < √6 := by positivity
  field_simp; nlinarith [s6]

/-- Stitz-Zeager Exercise 10.6.135: `sin(arccsc(-3)) = -1/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.135, p. 856"]
theorem exer_10_6_135 : sin (arccscCF (-3)) = -(1 / 3) := by
  rw [← inv_inv (sin (arccscCF (-3))), csc_arccsc_neg (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.6.138: `cos(arccot 3) = 3√10/10`. -/
@[kb "stitzzeager2013" "Exercise 10.6.138, p. 856"]
theorem exer_10_6_138 : cos (arccotR 3) = 3 * √10 / 10 := by
  rw [cos_acot, show (1 : ℝ) + 3 ^ 2 = 10 by norm_num]
  have hp : 0 < √10 := by positivity
  field_simp; nlinarith [s10]

/-- Stitz-Zeager Exercise 10.6.139: `cos(arcsec 5) = 1/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.139, p. 856"]
theorem exer_10_6_139 : cos (arcsecCF 5) = 1 / 5 := by
  rw [arcsec_pos (by norm_num), cos_arccos (by norm_num) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.6.142: `tan(arcsec(5/3)) = 4/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.142, p. 856"]
theorem exer_10_6_142 : tan (arcsecCF (5 / 3)) = 4 / 3 := by
  have e : √(1 - ((5 / 3 : ℝ)⁻¹) ^ 2) = 4 / 5 :=
    sqrt_of_sq (by norm_num) (by norm_num)
  rw [arcsec_pos (by norm_num), tan_eq_sin_div_cos, sin_arccos, cos_arccos (by norm_num) (by norm_num), e]
  norm_num

/-- Stitz-Zeager Exercise 10.6.143: `tan(arccot 12) = 1/12`. -/
@[kb "stitzzeager2013" "Exercise 10.6.143, p. 856"]
theorem exer_10_6_143 : tan (arccotR 12) = 1 / 12 := by
  rw [tan_eq_sin_div_cos, sin_acot, cos_acot]
  have hp : 0 < √(1 + (12 : ℝ) ^ 2) := by positivity
  field_simp

/-- Stitz-Zeager Exercise 10.6.145: `cot(arccos(√3/2)) = √3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.145, p. 856"]
theorem exer_10_6_145 : cos (arccos (√3 / 2)) / sin (arccos (√3 / 2)) = √3 := by
  have e : √(1 - (√3 / 2) ^ 2) = 1 / 2 :=
    sqrt_of_sq (by norm_num) (by rw [div_pow, s3]; norm_num)
  have h0 : 0 ≤ √3 / 2 := by positivity
  rw [cos_arccos (by linarith) r3le, sin_arccos, e]; ring

/-- Stitz-Zeager Exercise 10.6.146: `cot(arccsc √5) = 2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.146, p. 856"]
theorem exer_10_6_146 : cos (arccscCF √5) / sin (arccscCF √5) = 2 := by
  have hp : 0 < √5 := by positivity
  have h1 : (1 : ℝ) ≤ √5 := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have e : √(1 - ((√5)⁻¹) ^ 2) = 2 * (√5)⁻¹ :=
    sqrt_of_sq (by positivity) (by rw [mul_pow, inv_pow, s5]; norm_num)
  rw [arccsc_pos h1, sin_arcsin (by have := inv_pos.2 hp; linarith) (inv_le_one_of_one_le₀ h1),
    cos_arcsin, e]
  field_simp

/-- Stitz-Zeager Exercise 10.6.147: `cot(arctan 0.25) = 4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.147, p. 856"]
theorem exer_10_6_147 : cos (arctan 0.25) / sin (arctan 0.25) = 4 := by
  rw [cos_arctan, sin_arctan]
  have hp : 0 < √(1 + (0.25 : ℝ) ^ 2) := by positivity
  field_simp; norm_num

/-- Stitz-Zeager Exercise 10.6.149: `sec(arcsin(-12/13)) = 13/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.149, p. 856"]
theorem exer_10_6_149 : (cos (arcsin (-(12 / 13))))⁻¹ = 13 / 5 := by
  have e : √(1 - (-(12 / 13 : ℝ)) ^ 2) = 5 / 13 := sqrt_of_sq (by norm_num) (by norm_num)
  rw [cos_arcsin, e]; norm_num

/-- Stitz-Zeager Exercise 10.6.151: `sec(arccot(-√10/10)) = -√11`. -/
@[kb "stitzzeager2013" "Exercise 10.6.151, p. 856"]
theorem exer_10_6_151 : (cos (arccotR (-(√10 / 10))))⁻¹ = -√11 := by
  have s11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have e : 1 + (-(√10 / 10)) ^ 2 = 11 / 10 := by rw [neg_sq, div_pow, s10]; norm_num
  have h : √10 * √11 = 10 * √(11 / 10) := by
    rw [← Real.sqrt_mul (by norm_num), show (10 : ℝ) * 11 = 10 ^ 2 * (11 / 10) by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hp : 0 < √10 := by positivity
  have hq : 0 < √(11 / 10) := Real.sqrt_pos.mpr (by norm_num)
  rw [cos_acot, e, inv_div]
  have hne : -(√10 / 10) ≠ 0 := by
    have : 0 < √10 / 10 := by positivity
    linarith
  rw [div_eq_iff hne]
  linarith

/-- Stitz-Zeager Exercise 10.6.152: `csc(arccot 9) = √82`. -/
@[kb "stitzzeager2013" "Exercise 10.6.152, p. 856"]
theorem exer_10_6_152 : (sin (arccotR 9))⁻¹ = √82 := by
  rw [sin_acot, one_div, inv_inv]; norm_num

/-- Stitz-Zeager Exercise 10.6.153: `csc(arcsin(3/5)) = 5/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.153, p. 856"]
theorem exer_10_6_153 : (sin (arcsin (3 / 5)))⁻¹ = 5 / 3 := by
  rw [sin_arcsin (by norm_num) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.6.154: `csc(arctan(-2/3)) = -√13/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.154, p. 856"]
theorem exer_10_6_154 : (sin (arctan (-(2 / 3))))⁻¹ = -(√13 / 2) := by
  have e : √(1 + (-(2 / 3 : ℝ)) ^ 2) = √13 / 3 :=
    sqrt_of_sq (by positivity) (by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num)
  have hp : 0 < √13 := by positivity
  rw [sin_arctan, e, inv_div]
  field_simp

/-- Stitz-Zeager Exercise 10.6.156: `cos(arcsec 3 + arctan 2) = (√5 - 4√10)/15`. -/
@[kb "stitzzeager2013" "Exercise 10.6.156, p. 856"]
theorem exer_10_6_156 : cos (arcsecCF 3 + arctan 2) = (√5 - 4 * √10) / 15 := by
  have e1 : √(1 - ((3 : ℝ)⁻¹) ^ 2) = 2 * √2 / 3 :=
    sqrt_of_sq (by positivity) (by rw [div_pow, mul_pow, s2]; norm_num)
  have e5 : 1 / √5 = √5 / 5 := by
    have hp : 0 < √5 := by positivity
    rw [div_eq_div_iff hp.ne' (by norm_num)]; nlinarith [s5]
  have e5' : 2 / √5 = 2 * √5 / 5 := by
    have hp : 0 < √5 := by positivity
    rw [div_eq_div_iff hp.ne' (by norm_num)]; nlinarith [s5]
  have r10 : √10 = √2 * √5 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [cos_add, arcsec_pos (by norm_num), cos_arccos (by norm_num) (by norm_num), sin_arccos, e1,
    cos_arctan, sin_arctan, show (1 : ℝ) + 2 ^ 2 = 5 by norm_num, e5, e5', r10]
  ring

/-- Stitz-Zeager Exercise 10.6.157: `tan(arctan 3 + arccos(-3/5)) = 1/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.157, p. 856"]
theorem exer_10_6_157 : tan (arctan 3 + arccos (-(3 / 5))) = 1 / 3 := by
  have e : √(1 - (-(3 / 5 : ℝ)) ^ 2) = 4 / 5 := sqrt_of_sq (by norm_num) (by norm_num)
  have hp : 0 < √(1 + (3 : ℝ) ^ 2) := by positivity
  rw [tan_eq_sin_div_cos, sin_add, cos_add, sin_arctan, cos_arctan,
    cos_arccos (by norm_num) (by norm_num), sin_arccos, e]
  field_simp
  ring

/-- Stitz-Zeager Exercise 10.6.159: `sin(2 arccsc(13/5)) = 120/169`. -/
@[kb "stitzzeager2013" "Exercise 10.6.159, p. 856"]
theorem exer_10_6_159 : sin (2 * arccscCF (13 / 5)) = 120 / 169 := by
  have e : √(1 - ((13 / 5 : ℝ)⁻¹) ^ 2) = 12 / 13 := sqrt_of_sq (by norm_num) (by norm_num)
  rw [arccsc_pos (by norm_num), sin_two_mul, sin_arcsin (by norm_num) (by norm_num), cos_arcsin, e]
  norm_num

/-- Stitz-Zeager Exercise 10.6.163: `cos(2 arccot(-√5)) = 2/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.163, p. 856"]
theorem exer_10_6_163 : cos (2 * arccotR (-√5)) = 2 / 3 := by
  rw [cos_two_mul, cos_acot, div_pow, neg_sq, s5, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Stitz-Zeager Exercise 10.6.164: `sin(arctan(2)/2) = √((5 - √5)/10)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.164, p. 856"]
theorem exer_10_6_164 : sin (arctan 2 / 2) = √((5 - √5) / 10) := by
  have h5 : √5 ≤ 5 := by nlinarith [s5, Real.sqrt_nonneg 5]
  have hp : 0 < √5 := by positivity
  have hpos : 0 < sin (arctan 2 / 2) := by
    apply sin_pos_of_pos_of_lt_pi
    · have : 0 < arctan 2 := arctan_pos.mpr (by norm_num)
      linarith
    · have := arctan_lt_pi_div_two 2
      linarith [Real.pi_pos]
  refine eqp' hpos (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt (by linarith), sin_sq_half', cos_arctan, show (1 : ℝ) + 2 ^ 2 = 5 by norm_num]
  field_simp
  nlinarith [s5]

/-- Stitz-Zeager Exercise 10.6.169: `csc(arccos x) = 1/√(1 - x²)` for `-1 < x < 1`; at `x = ±1` the
cosecant is undefined (`sin(arccos(±1)) = 0`). -/
@[kb "stitzzeager2013" "Exercise 10.6.169, p. 857"]
theorem exer_10_6_169 :
    (∀ x : ℝ, -1 < x → x < 1 → (sin (arccos x))⁻¹ = 1 / √(1 - x ^ 2)) ∧ sin (arccos 1) = 0 ∧
      sin (arccos (-1)) = 0 := by
  refine ⟨fun x _ _ => by rw [sin_arccos, one_div], by simp, by simp⟩

/-- Stitz-Zeager Exercise 10.6.174: `sin(arccos(x/5)) = √(25 - x²)/5` for `-5 ≤ x ≤ 5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.174, p. 857"]
theorem exer_10_6_174 (x : ℝ) (h1 : -5 ≤ x) (h2 : x ≤ 5) :
    sin (arccos (x / 5)) = √(25 - x ^ 2) / 5 := by
  have h : 0 ≤ 25 - x ^ 2 := by nlinarith
  rw [sin_arccos]
  exact sqrt_of_sq (by positivity) (by rw [div_pow, div_pow, Real.sq_sqrt h]; ring)

/-- Stitz-Zeager Exercise 10.6.175: `cos(arcsin(x/2)) = √(4 - x²)/2` for `-2 ≤ x ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.175, p. 857"]
theorem exer_10_6_175 (x : ℝ) (h1 : -2 ≤ x) (h2 : x ≤ 2) :
    cos (arcsin (x / 2)) = √(4 - x ^ 2) / 2 := by
  have h : 0 ≤ 4 - x ^ 2 := by nlinarith
  rw [cos_arcsin]
  exact sqrt_of_sq (by positivity) (by rw [div_pow, div_pow, Real.sq_sqrt h]; ring)

/-- Stitz-Zeager Exercise 10.6.178: `sin(2 arcsin(x√3/3)) = 2x√(3 - x²)/3` for `-√3 ≤ x ≤ √3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.178, p. 857"]
theorem exer_10_6_178 (x : ℝ) (h1 : -√3 ≤ x) (h2 : x ≤ √3) :
    sin (2 * arcsin (x * √3 / 3)) = 2 * x * √(3 - x ^ 2) / 3 := by
  have hp : 0 < √3 := by positivity
  have h : 0 ≤ 3 - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : 0 ≤ x + √3), s3]
  have hc : √(1 - (x * √3 / 3) ^ 2) = √3 * √(3 - x ^ 2) / 3 :=
    sqrt_of_sq (by positivity) (by rw [div_pow, mul_pow, div_pow, mul_pow, s3, Real.sq_sqrt h]; ring)
  have b1 : -1 ≤ x * √3 / 3 := by
    have := mul_le_mul_of_nonneg_right h1 hp.le
    nlinarith [s3]
  have b2 : x * √3 / 3 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h2 hp.le
    nlinarith [s3]
  rw [sin_two_mul, sin_arcsin b1 b2, cos_arcsin, hc]
  linear_combination (2 * x * √(3 - x ^ 2) / 9) * s3

/-- Stitz-Zeager Exercise 10.6.180: `sec(arctan 2x) tan(arctan 2x) = 2x√(1 + 4x²)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.180, p. 857"]
theorem exer_10_6_180 (x : ℝ) :
    (cos (arctan (2 * x)))⁻¹ * tan (arctan (2 * x)) = 2 * x * √(1 + 4 * x ^ 2) := by
  rw [cos_arctan, tan_arctan, one_div, inv_inv, mul_pow]
  ring_nf

/-- Stitz-Zeager Exercise 10.6.182: `cos(arcsin x + arctan x) = (√(1 - x²) - x²)/√(1 + x²)` for
`-1 ≤ x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.182, p. 857"]
theorem exer_10_6_182 (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    cos (arcsin x + arctan x) = (√(1 - x ^ 2) - x ^ 2) / √(1 + x ^ 2) := by
  rw [cos_add, cos_arcsin, sin_arcsin h1 h2, cos_arctan, sin_arctan]
  ring

/-- Stitz-Zeager Exercise 10.6.183: `tan(2 arcsin x) = 2x√(1 - x²)/(1 - 2x²)` for `-1 < x < 1`,
`x² ≠ 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.183, p. 857"]
theorem exer_10_6_183 (x : ℝ) (h1 : -1 < x) (h2 : x < 1) (h3 : x ^ 2 ≠ 1 / 2) :
    tan (2 * arcsin x) = 2 * x * √(1 - x ^ 2) / (1 - 2 * x ^ 2) := by
  rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, sin_arcsin h1.le h2.le, cos_arcsin,
    Real.sq_sqrt (by nlinarith)]
  congr 1; ring

/-- Stitz-Zeager Exercise 10.6.184: `sin((1/2) arctan x) = ± √((√(x²+1) - 1)/(2√(x²+1)))`, positive for
`x ≥ 0` and negative for `x < 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.184, p. 857"]
theorem exer_10_6_184 (x : ℝ) :
    (0 ≤ x → sin (arctan x / 2) = √((√(1 + x ^ 2) - 1) / (2 * √(1 + x ^ 2)))) ∧
      (x < 0 → sin (arctan x / 2) = -√((√(1 + x ^ 2) - 1) / (2 * √(1 + x ^ 2)))) := by
  have hr1 : 1 ≤ √(1 + x ^ 2) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + x ^ 2 by nlinarith)
    simpa using this
  have hr : 0 < √(1 + x ^ 2) := by linarith
  have hsq : sin (arctan x / 2) ^ 2 = (√(1 + x ^ 2) - 1) / (2 * √(1 + x ^ 2)) := by
    rw [sin_sq_half', cos_arctan]
    field_simp
  have hnn : 0 ≤ (√(1 + x ^ 2) - 1) / (2 * √(1 + x ^ 2)) := by
    apply div_nonneg <;> linarith
  have hlt := arctan_lt_pi_div_two x
  have hgt := neg_pi_div_two_lt_arctan x
  constructor
  · intro hx
    have h0 : 0 ≤ arctan x := by
      rw [← arctan_zero]; exact arctan_strictMono.monotone hx
    have hs : 0 ≤ sin (arctan x / 2) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    exact (sq_eq_sq₀ hs (Real.sqrt_nonneg _)).1 (by rw [hsq, Real.sq_sqrt hnn])
  · intro hx
    have h0 : arctan x < 0 := by
      rw [← arctan_zero]; exact arctan_strictMono hx
    have hs : sin (arctan x / 2) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [Real.pi_pos])
    have := (sq_eq_sq₀ (neg_nonneg.2 hs) (Real.sqrt_nonneg _)).1
      (by rw [neg_sq, hsq, Real.sq_sqrt hnn])
    linarith

/-- Stitz-Zeager Exercise 10.6.185: if `sin θ = x/2` with `-π/2 < θ < π/2` then
`θ + sin 2θ = arcsin(x/2) + x√(4 - x²)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.185, p. 857"]
theorem exer_10_6_185 (θ x : ℝ) (h : sin θ = x / 2) (h1 : -(π / 2) < θ) (h2 : θ < π / 2) :
    θ + sin (2 * θ) = arcsin (x / 2) + x * √(4 - x ^ 2) / 2 := by
  have hθ : arcsin (x / 2) = θ := by rw [← h]; exact arcsin_sin h1.le h2.le
  have hcn : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨h1.le, h2.le⟩
  have h4 : 0 ≤ 4 - x ^ 2 := by
    have := sin_sq_add_cos_sq θ
    rw [h] at this; nlinarith [sq_nonneg (cos θ)]
  have hc : cos θ = √(4 - x ^ 2) / 2 := by
    refine (sq_eq_sq₀ hcn (by positivity)).1 ?_
    have := sin_sq_add_cos_sq θ
    rw [h] at this
    rw [div_pow, Real.sq_sqrt h4]; nlinarith
  rw [hθ, sin_two_mul, h, hc]; ring

/-- Stitz-Zeager Exercise 10.6.186: if `tan θ = x/7` with `-π/2 < θ < π/2` then
`θ/2 - sin(2θ)/2 = arctan(x/7)/2 - 7x/(x² + 49)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.186, p. 857"]
theorem exer_10_6_186 (θ x : ℝ) (h : tan θ = x / 7) (h1 : -(π / 2) < θ) (h2 : θ < π / 2) :
    1 / 2 * θ - 1 / 2 * sin (2 * θ) = 1 / 2 * arctan (x / 7) - 7 * x / (x ^ 2 + 49) := by
  have hθ : arctan (x / 7) = θ := by rw [← h]; exact arctan_tan h1 h2
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  have hs : sin θ = x / 7 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h; exact h
  have hq : cos θ ^ 2 = 49 / (x ^ 2 + 49) := by
    have := sin_sq_add_cos_sq θ
    rw [hs] at this
    have hx : 0 < x ^ 2 + 49 := by positivity
    field_simp
    nlinarith
  rw [hθ, sin_two_mul, hs]
  have : 2 * (x / 7 * cos θ) * cos θ = 2 * (x / 7) * cos θ ^ 2 := by ring
  rw [this, hq]
  have hx : 0 < x ^ 2 + 49 := by positivity
  field_simp
  ring

/-- Stitz-Zeager Exercise 10.6.187: if `sec θ = x/4` with `0 < θ < π/2` then
`4 tan θ - 4θ = √(x² - 16) - 4 arcsec(x/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.6.187, p. 857"]
theorem exer_10_6_187 (θ x : ℝ) (h : (cos θ)⁻¹ = x / 4) (h1 : 0 < θ) (h2 : θ < π / 2) :
    4 * tan θ - 4 * θ = √(x ^ 2 - 16) - 4 * arcsecCF (x / 4) := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩
  have ht : 0 < tan θ := tan_pos_of_pos_of_lt_pi_div_two h1 h2
  have hsq : tan θ ^ 2 = x ^ 2 / 16 - 1 := by
    have h5 : cos θ ^ 2 ≠ 0 := by positivity
    have h6 : (cos θ ^ 2)⁻¹ = x ^ 2 / 16 := by rw [← inv_pow, h]; ring
    rw [tan_eq_sin_div_cos, div_pow, sin_sq, ← h6]
    field_simp
  have hnn : 0 ≤ x ^ 2 - 16 := by nlinarith [sq_nonneg (tan θ)]
  have htt : tan θ = √(x ^ 2 - 16) / 4 := by
    refine eqp' ht (by positivity) ?_
    rw [div_pow, Real.sq_sqrt hnn, hsq]; ring
  rw [← h, sinsec_a h1.le h2, htt]
  ring

/-- Stitz-Zeager Exercise 10.6.206: on `[0, 2π)`, `cot x = 1/117` exactly when `x = arctan 117` or
`x = arctan 117 + π` (about `1.5622` and `4.7038`). -/
@[kb "stitzzeager2013" "Exercise 10.6.206, p. 858"]
theorem exer_10_6_206 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x / sin x = 1 / 117 ↔ x = arctan 117 ∨ x = arctan 117 + π := by
  rw [cot_tan, show ((1 : ℝ) / 117)⁻¹ = 117 by norm_num]
  exact tan_sol_pos _ x (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.216: `5 sin 3x + 12 cos 3x = 13 sin(3x + arcsin(12/13))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.216, p. 858"]
theorem exer_10_6_216 (x : ℝ) :
    5 * sin (3 * x) + 12 * cos (3 * x) = 13 * sin (3 * x + arcsin (12 / 13)) := by
  have e : √(1 - (12 / 13 : ℝ) ^ 2) = 5 / 13 := sqrt_of_sq (by norm_num) (by norm_num)
  rw [sin_add, sin_arcsin (by norm_num) (by norm_num), cos_arcsin, e]; ring

/-- Stitz-Zeager Exercise 10.6.217: `3 cos 2x + 4 sin 2x = 5 sin(2x + arcsin(3/5))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.217, p. 858"]
theorem exer_10_6_217 (x : ℝ) :
    3 * cos (2 * x) + 4 * sin (2 * x) = 5 * sin (2 * x + arcsin (3 / 5)) := by
  have e : √(1 - (3 / 5 : ℝ) ^ 2) = 4 / 5 := sqrt_of_sq (by norm_num) (by norm_num)
  rw [sin_add, sin_arcsin (by norm_num) (by norm_num), cos_arcsin, e]; ring

/-- Stitz-Zeager Exercise 10.6.218: `cos x - 3 sin x = √10 sin(x + arccos(-3√10/10))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.218, p. 858"]
theorem exer_10_6_218 (x : ℝ) :
    cos x - 3 * sin x = √10 * sin (x + arccos (-(3 * √10 / 10))) := by
  have hp : 0 < √10 := by positivity
  have h3 : √10 ≤ 10 / 3 := by nlinarith [s10]
  have e : √(1 - (-(3 * √10 / 10)) ^ 2) = √10 / 10 :=
    sqrt_of_sq (by positivity) (by rw [neg_sq, div_pow, div_pow, mul_pow, s10]; nlinarith [s10])
  rw [sin_add, cos_arccos (by nlinarith) (by nlinarith), sin_arccos, e]
  linear_combination (-(cos x - 3 * sin x) / 10) * s10

/-- Stitz-Zeager Exercise 10.6.219: `7 sin 10x - 24 cos 10x = 25 sin(10x + arcsin(-24/25))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.219, p. 858"]
theorem exer_10_6_219 (x : ℝ) :
    7 * sin (10 * x) - 24 * cos (10 * x) = 25 * sin (10 * x + arcsin (-(24 / 25))) := by
  have e : √(1 - (-(24 / 25 : ℝ)) ^ 2) = 7 / 25 := sqrt_of_sq (by norm_num) (by norm_num)
  rw [sin_add, sin_arcsin (by norm_num) (by norm_num), cos_arcsin, e]; ring

/-- Stitz-Zeager Exercise 10.6.220: `-cos x - 2√2 sin x = 3 sin(x + π + arcsin(1/3))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.220, p. 858"]
theorem exer_10_6_220 (x : ℝ) :
    -cos x - 2 * √2 * sin x = 3 * sin (x + π + arcsin (1 / 3)) := by
  have hp : 0 < √2 := by positivity
  have e : √(1 - (1 / 3 : ℝ) ^ 2) = 2 * √2 / 3 :=
    sqrt_of_sq (by positivity) (by rw [div_pow, div_pow, mul_pow, s2]; norm_num)
  rw [show x + π + arcsin (1 / 3) = (x + arcsin (1 / 3)) + π by ring, sin_add_pi, sin_add,
    sin_arcsin (by norm_num) (by norm_num), cos_arcsin, e]
  ring

/-- Stitz-Zeager Exercise 10.6.221: `2 sin x - cos x = √5 sin(x + arcsin(-√5/5))`. -/
@[kb "stitzzeager2013" "Exercise 10.6.221, p. 858"]
theorem exer_10_6_221 (x : ℝ) :
    2 * sin x - cos x = √5 * sin (x + arcsin (-(√5 / 5))) := by
  have hp : 0 < √5 := by positivity
  have h5 : √5 ≤ 5 := by nlinarith [s5]
  have e : √(1 - (-(√5 / 5)) ^ 2) = 2 * √5 / 5 :=
    sqrt_of_sq (by positivity) (by rw [neg_sq, div_pow, div_pow, mul_pow, s5]; nlinarith [s5])
  rw [sin_add, sin_arcsin (by nlinarith) (by nlinarith), cos_arcsin, e]
  linear_combination (-(2 * sin x - cos x) / 5) * s5

end UndergradKB.Precalculus.Course
