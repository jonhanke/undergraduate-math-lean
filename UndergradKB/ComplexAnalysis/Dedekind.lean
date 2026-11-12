import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.GCD.Basic
import UndergradKB.Common.Attr

/-!
# Dedekind sums and their reciprocity law (row CX-148)

For coprime positive integers `a`, `b` the Dedekind sum is
`s(a, b) = (1 / 4b) ∑_{k=1}^{b-1} cot (π k a / b) cot (π k / b)`.
This file proves the reciprocity law
`s(a, b) + s(b, a) = -1/4 + (1/12) (a/b + 1/(ab) + b/a)`.

Instead of the residue calculus, the proof goes through the sawtooth form
`∑_{k=1}^{b-1} ((k/b)) ((k a / b))`, `((x)) = x - ⌊x⌋ - 1/2`:

* finite Fourier identities (`cot_sine_sum`, `sawtooth_sine_sum`) show that the cotangent form
  equals the sawtooth form (`dedekindSumCot_eq_sawSum`);
* an elementary lattice-point count (`sq_floor_lattice`, `sq_floor_mod`, `sum_floor`) proves the
  reciprocity law for the sawtooth form (`sawSum_reciprocity`).
-/

open Finset Real

namespace UndergradKB.ComplexAnalysis

/-! ### Finite trigonometric sums -/

lemma sum_cos_sin_range {b l : ℕ} (hl0 : 0 < l) (hlb : l < b) :
    ∑ k ∈ range b, Real.cos (2 * π * k * l / b) = 0 ∧
      ∑ k ∈ range b, Real.sin (2 * π * k * l / b) = 0 := by
  have hb : (b : ℝ) ≠ 0 := by
    have : 0 < b := by omega
    positivity
  set x : ℝ := 2 * π * l / b with hx
  set z : ℂ := Complex.exp ((x : ℂ) * Complex.I) with hz
  have hzk : ∀ k : ℕ, z ^ k = Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hzb : z ^ b = 1 := by
    rw [hzk]
    have : (((b * x : ℝ) : ℂ)) * Complex.I = (l : ℂ) * (2 * π * Complex.I) := by
      rw [hx]
      have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h1 : (x : ℂ) = (n : ℂ) * (2 * π) := by
      have := hn
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      apply mul_right_cancel₀ hI
      rw [this]; ring
    have h2 : x = n * (2 * π) := by exact_mod_cast h1
    have h3 : (l : ℝ) = b * n := by
      rw [hx] at h2
      field_simp at h2
      nlinarith [Real.pi_pos]
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hl0
    have hlb' : (l : ℝ) < b := by exact_mod_cast hlb
    have hbpos : (0 : ℝ) < b := by linarith
    rcases le_or_gt n 0 with hn0 | hn0
    · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      nlinarith
  have hsum : ∑ k ∈ range b, z ^ k = 0 := by
    rw [geom_sum_eq hz1, hzb]
    simp
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [Complex.im_sum, Complex.zero_im] at him
  constructor
  · rw [← hre]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzk, Complex.exp_ofReal_mul_I_re, hx]
    congr 1
    ring
  · rw [← him]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hzk, Complex.exp_ofReal_mul_I_im, hx]
    congr 1
    ring

lemma sum_cos_Ico {b l : ℕ} (hl0 : 0 < l) (hlb : l < b) :
    ∑ k ∈ Ico 1 b, Real.cos (2 * π * k * l / b) = -1 := by
  have h := (sum_cos_sin_range hl0 hlb).1
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
  simp at h
  linarith

lemma cot_mul_sin_two_mul {x : ℝ} (hx : Real.sin x ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    Real.cot x * Real.sin (2 * m * x)
      = 1 + 2 * ∑ l ∈ Ico 1 m, Real.cos (2 * l * x) + Real.cos (2 * m * x) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one, Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, mul_one]
    rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have e1 : Real.sin (2 * ((n + 1 : ℕ) : ℝ) * x)
        = Real.sin (2 * n * x) * Real.cos (2 * x) + Real.cos (2 * n * x) * Real.sin (2 * x) := by
      rw [← Real.sin_add]; congr 1; push_cast; ring
    have e2 : Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x)
        = Real.cos (2 * n * x) * Real.cos (2 * x) - Real.sin (2 * n * x) * Real.sin (2 * x) := by
      rw [← Real.cos_add]; congr 1; push_cast; ring
    have key : Real.cot x * Real.sin (2 * ((n + 1 : ℕ) : ℝ) * x)
        = Real.cot x * Real.sin (2 * n * x) + Real.cos (2 * n * x)
          + Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x) := by
      rw [e1, e2, Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
      field_simp
      linear_combination (2 * Real.cos x * Real.sin (2 * n * x)) * Real.sin_sq_add_cos_sq x
    rw [key, ih]
    ring

lemma sum_nat_mul_pow (z : ℂ) (N : ℕ) :
    (z - 1) * ∑ n ∈ range N, (n : ℂ) * z ^ n
      = ((N : ℂ) - 1) * z ^ N - ∑ n ∈ range N, z ^ n + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    push_cast
    ring

lemma im_inv_exp_sub_one {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    ((Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) - 1)⁻¹).im = -Real.cot θ / 2 := by
  rw [Complex.inv_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.normSq_apply,
    Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.sub_im, Complex.exp_ofReal_mul_I_im]
  simp only [Complex.one_re, Complex.one_im, sub_zero]
  rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq θ
  have hD : (2 * Real.cos θ ^ 2 - 1 - 1) * (2 * Real.cos θ ^ 2 - 1 - 1)
      + 2 * Real.sin θ * Real.cos θ * (2 * Real.sin θ * Real.cos θ)
      = 4 * Real.sin θ ^ 2 := by
    have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
    rw [show 2 * Real.sin θ * Real.cos θ * (2 * Real.sin θ * Real.cos θ)
      = 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2 by ring]
    nlinarith [hc]
  rw [hD]
  field_simp
  ring

lemma sum_nat_mul_sin {b m : ℕ} (hm0 : 0 < m) (hmb : m < b) :
    ∑ n ∈ range b, (n : ℝ) * Real.sin (2 * π * n * m / b)
      = -(b : ℝ) / 2 * Real.cot (π * m / b) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb : (b : ℝ) ≠ 0 := hbpos.ne'
  set x : ℝ := 2 * π * m / b with hx
  set z : ℂ := Complex.exp ((x : ℂ) * Complex.I) with hz
  have hzk : ∀ k : ℕ, z ^ k = Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hzb : z ^ b = 1 := by
    rw [hzk]
    have : (((b * x : ℝ) : ℂ)) * Complex.I = (m : ℂ) * (2 * π * Complex.I) := by
      rw [hx]
      have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h1 : (x : ℂ) = (n : ℂ) * (2 * π) := by
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      apply mul_right_cancel₀ hI
      rw [hn]; ring
    have h2 : x = n * (2 * π) := by exact_mod_cast h1
    have h3 : (m : ℝ) = b * n := by
      rw [hx] at h2
      field_simp at h2
      nlinarith [Real.pi_pos]
    have hlpos : (0 : ℝ) < m := by exact_mod_cast hm0
    have hlb' : (m : ℝ) < b := by exact_mod_cast hmb
    rcases le_or_gt n 0 with hn0 | hn0
    · have : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      nlinarith
  have hgeom : ∑ n ∈ range b, z ^ n = 0 := by
    rw [geom_sum_eq hz1, hzb]
    simp
  have hG := sum_nat_mul_pow z b
  rw [hgeom, hzb] at hG
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  have hS : ∑ n ∈ range b, (n : ℂ) * z ^ n = (b : ℂ) / (z - 1) := by
    rw [eq_div_iff hz1']
    rw [mul_comm]
    rw [hG]
    ring
  have him := congrArg Complex.im hS
  have hsin : Real.sin (π * m / b) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hbpos]; nlinarith [Real.pi_pos, (by exact_mod_cast hmb : (m : ℝ) < b)]
  have hxθ : x = 2 * (π * m / b) := by rw [hx]; ring
  rw [Complex.im_sum] at him
  have hl : ∑ n ∈ range b, ((n : ℂ) * z ^ n).im
      = ∑ n ∈ range b, (n : ℝ) * Real.sin (2 * π * n * m / b) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have e : (n : ℝ) * x = 2 * π * n * m / b := by rw [hx]; ring
    rw [← Complex.ofReal_natCast, Complex.im_ofReal_mul, hzk, Complex.exp_ofReal_mul_I_im, e]
  have hzθ : z = Complex.exp (((2 * (π * m / b) : ℝ) : ℂ) * Complex.I) := by rw [hz, hxθ]
  have hr : ((b : ℂ) / (z - 1)).im = (b : ℝ) * (-Real.cot (π * m / b) / 2) := by
    rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, hzθ,
      im_inv_exp_sub_one hsin]
  rw [hl, hr] at him
  rw [him]
  ring

/-- The sawtooth function `x ↦ x - 1/2 - ⌊x⌋` has sine coefficients given by the cotangent. -/
lemma sawtooth_sine_sum {b m : ℕ} (hm0 : 0 < m) (hmb : m < b) :
    ∑ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * Real.sin (2 * π * n * m / b)
      = -Real.cot (π * m / b) / 2 := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have h1 := sum_nat_mul_sin hm0 hmb
  have h2 := (sum_cos_sin_range hm0 hmb).2
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h1 h2
  simp at h1 h2
  have hpt : ∀ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * Real.sin (2 * π * n * m / b)
      = (1 / (b : ℝ)) * ((n : ℝ) * Real.sin (2 * π * n * m / b))
        - (1 / 2) * Real.sin (2 * π * n * m / b) := by
    intro n _
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
  field_simp
  ring

lemma sin_mod (b u j : ℕ) (hb : 0 < b) :
    Real.sin (2 * π * u * j / b) = Real.sin (2 * π * u * ((j % b : ℕ) : ℝ) / b) := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have h : (j : ℝ) = b * ((j / b : ℕ) : ℝ) + ((j % b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod j b).symm
  have e : 2 * π * (u : ℝ) * j / b
      = 2 * π * u * ((j % b : ℕ) : ℝ) / b + ((u * (j / b) : ℕ) : ℝ) * (2 * π) := by
    rw [h]
    push_cast
    field_simp
    ring
  rw [e, Real.sin_add_nat_mul_two_pi]

lemma cot_mod (b j : ℕ) (hb : 0 < b) :
    Real.cot (π * j / b) = Real.cot (π * ((j % b : ℕ) : ℝ) / b) := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have h : (j : ℝ) = b * ((j / b : ℕ) : ℝ) + ((j % b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod j b).symm
  have e : π * (j : ℝ) / b = π * ((j % b : ℕ) : ℝ) / b + ((j / b : ℕ) : ℝ) * π := by
    rw [h]
    field_simp
    ring
  rw [e, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_add_nat_mul_pi,
    Real.sin_add_nat_mul_pi]
  have hne : ((-1 : ℝ) ^ (j / b)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_div_mul_left _ _ hne]

/-- The cotangent has the sawtooth function `((m/b))` as its sine coefficients. -/
lemma cot_sine_sum {b m : ℕ} (hm0 : 0 < m) (hmb : m < b) :
    ∑ k ∈ Ico 1 b, Real.cot (π * k / b) * Real.sin (2 * π * k * m / b) = (b : ℝ) - 2 * m := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hpt : ∀ k ∈ Ico 1 b, Real.cot (π * k / b) * Real.sin (2 * π * k * m / b)
      = 1 + 2 * ∑ l ∈ Ico 1 m, Real.cos (2 * π * k * l / b) + Real.cos (2 * π * k * m / b) := by
    intro k hk
    rw [mem_Ico] at hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hkb : (k : ℝ) < b := by exact_mod_cast hk.2
    have hs : Real.sin (π * k / b) ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · rw [div_lt_iff₀ hbpos]; nlinarith [Real.pi_pos]
    have := cot_mul_sin_two_mul hs m hm0
    have e : ∀ l : ℕ, 2 * (l : ℝ) * (π * k / b) = 2 * π * k * l / b := fun l => by ring
    simp only [e] at this
    exact this
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ l ∈ Ico 1 m, ∑ k ∈ Ico 1 b, Real.cos (2 * π * k * l / b) = -1 := by
    intro l hl
    rw [mem_Ico] at hl
    exact sum_cos_Ico (by omega) (by omega)
  rw [Finset.sum_congr rfl h1, sum_cos_Ico hm0 hmb]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  ring

/-! ### Lattice-point arguments -/

lemma sum_Ico_id (b : ℕ) (hb : 1 ≤ b) :
    ∑ k ∈ Ico 1 b, (k : ℝ) = b * (b - 1) / 2 := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    push_cast
    ring

lemma sum_Ico_sq (b : ℕ) (hb : 1 ≤ b) :
    ∑ k ∈ Ico 1 b, (k : ℝ) ^ 2 = (b - 1) * b * (2 * b - 1) / 6 := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    push_cast
    ring

lemma mul_ne_of_coprime {a b y : ℕ} (hab : Nat.Coprime a b) (hy0 : 0 < y) (hya : y < a) (x : ℕ) :
    x * a ≠ y * b := by
  intro h
  have h1 : a ∣ y * b := ⟨x, by rw [← h]; ring⟩
  have hd : a ∣ y := Nat.Coprime.dvd_of_dvd_mul_right hab h1
  exact absurd (Nat.le_of_dvd hy0 hd) (by omega)

lemma filter_lt_eq {a b y : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) (hy0 : 0 < y)
    (hya : y < a) :
    (Ico 1 b).filter (fun x => x * a < y * b) = Icc 1 (y * b / a) := by
  have ha : 0 < a := by omega
  ext x
  simp only [mem_filter, mem_Ico, mem_Icc]
  have hne : x * a ≠ y * b := mul_ne_of_coprime hab hy0 hya x
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (Nat.le_div_iff_mul_le ha).2 h3.le⟩
  · rintro ⟨h1, h2⟩
    have h3 : x * a ≤ y * b := (Nat.le_div_iff_mul_le ha).1 h2
    have h4 : x * a < y * b := lt_of_le_of_ne h3 hne
    refine ⟨⟨h1, ?_⟩, h4⟩
    by_contra hxb
    have hxb' : b ≤ x := not_lt.1 hxb
    have h5 : b * a ≤ x * a := Nat.mul_le_mul_right a hxb'
    have h6 : y * b < a * b := Nat.mul_lt_mul_of_pos_right hya hb
    nlinarith

lemma card_lt_count {a b y : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) (hy0 : 0 < y)
    (hya : y < a) :
    ((Ico 1 b).filter (fun x => x * a < y * b)).card = y * b / a := by
  rw [filter_lt_eq hb hab hy0 hya]
  simp

lemma cnt_split {a b j : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) (hj0 : 0 < j) (hja : j < a) :
    ((Ico 1 b).filter (fun k => j * b < k * a)).card + j * b / a = b - 1 := by
  have h1 := card_lt_count hb hab hj0 hja
  have h2 : (Ico 1 b).filter (fun k => j * b < k * a)
      = (Ico 1 b).filter (fun k => ¬ (k * a < j * b)) := by
    refine Finset.filter_congr (fun k _ => ?_)
    have hne := mul_ne_of_coprime hab hj0 hja k
    constructor
    · intro h; omega
    · intro h; omega
  rw [h2, ← h1, add_comm, card_filter_add_card_filter_not]
  simp

lemma mod_ne_zero_of_coprime {a b k : ℕ} (hab : Nat.Coprime a b) (hk0 : 0 < k) (hkb : k < b) :
    k * a % b ≠ 0 := by
  intro h
  have h1 : b ∣ k * a := Nat.dvd_of_mod_eq_zero h
  have h2 : b ∣ k := Nat.Coprime.dvd_of_dvd_mul_right hab.symm h1
  exact absurd (Nat.le_of_dvd hk0 h2) (by omega)

lemma div_reflect_aux (a b k q r a' : ℕ) (hqr : b * q + r = k * a) (hr0 : 0 < r) (hrb : r < b)
    (ha' : a = q + 1 + a') (hbk : (b - k) * a + k * a = b * a) : (b - k) * a / b = a' := by
  have hba : b * a = b * q + b + b * a' := by rw [ha']; ring
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · nlinarith

lemma div_reflect {a b k : ℕ} (hb : 0 < b) (hab : Nat.Coprime a b) (hk0 : 0 < k) (hkb : k < b) :
    (b - k) * a / b + k * a / b + 1 = a := by
  have hr0 : k * a % b ≠ 0 := mod_ne_zero_of_coprime hab hk0 hkb
  have hrb : k * a % b < b := Nat.mod_lt _ hb
  have hqr : b * (k * a / b) + k * a % b = k * a := Nat.div_add_mod _ _
  have hqa : k * a / b < a := by
    rw [Nat.div_lt_iff_lt_mul hb]
    nlinarith [Nat.mul_lt_mul_of_pos_right hkb (show 0 < a by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at hab; omega
      · exact h)]
  have hbk : (b - k) * a + k * a = b * a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hkb.le]
  obtain ⟨a', ha'⟩ : ∃ a', a = k * a / b + 1 + a' := ⟨a - k * a / b - 1, by omega⟩
  have := div_reflect_aux a b k (k * a / b) (k * a % b) a' hqr (Nat.pos_of_ne_zero hr0) hrb ha' hbk
  omega

section Saw

variable {a b : ℕ}

lemma sum_floor (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) = ((a : ℝ) - 1) * ((b : ℝ) - 1) / 2 := by
  have h1 : ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ)
      = ∑ k ∈ Ico 1 b, (((b - k) * a / b : ℕ) : ℝ) := by
    have := Finset.sum_Ico_reflect (fun k => ((k * a / b : ℕ) : ℝ)) 1 (m := b) (n := b)
      (by omega)
    simp only [Nat.add_sub_cancel_left, add_tsub_cancel_right] at this
    exact this.symm
  have h2 : ∀ k ∈ Ico 1 b, (((b - k) * a / b : ℕ) : ℝ) = (a : ℝ) - 1 - ((k * a / b : ℕ) : ℝ) := by
    intro k hk
    rw [mem_Ico] at hk
    have := div_reflect hb hab (by omega) hk.2
    have h3 : (((b - k) * a / b : ℕ) : ℝ) + ((k * a / b : ℕ) : ℝ) + 1 = a := by
      exact_mod_cast this
    linarith
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico,
    nsmul_eq_mul, Nat.cast_sub hb] at h1
  push_cast at h1
  linarith

lemma sum_sq_mod (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∑ k ∈ Ico 1 b, ((k * a % b : ℕ) : ℝ) ^ 2 = ∑ k ∈ Ico 1 b, (k : ℝ) ^ 2 := by
  have hinj : Set.InjOn (fun k => k * a % b) (Ico 1 b : Set ℕ) := by
    intro k1 hk1 k2 hk2 h
    simp only [coe_Ico, Set.mem_Ico] at hk1 hk2
    have h1 : k1 * a ≡ k2 * a [MOD b] := h
    have h2 : k1 ≡ k2 [MOD b] := Nat.ModEq.cancel_right_of_coprime hab.symm h1
    have h3 : k1 % b = k2 % b := h2
    rwa [Nat.mod_eq_of_lt hk1.2, Nat.mod_eq_of_lt hk2.2] at h3
  have hsub : (Ico 1 b).image (fun k => k * a % b) ⊆ Ico 1 b := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [mem_Ico] at hk ⊢
    exact ⟨Nat.one_le_iff_ne_zero.2 (mod_ne_zero_of_coprime hab hk.1 hk.2), Nat.mod_lt _ hb⟩
  have himg : (Ico 1 b).image (fun k => k * a % b) = Ico 1 b :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hinj])
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

lemma sawSum_expand (hb : 0 < b) :
    ∑ k ∈ Ico 1 b, ((k : ℝ) / b - 1 / 2) * ((k * a : ℝ) / b - ((k * a / b : ℕ) : ℝ) - 1 / 2)
    = ((a : ℝ) / b ^ 2) * ∑ k ∈ Ico 1 b, (k : ℝ) ^ 2
      - (1 / (b : ℝ)) * ∑ k ∈ Ico 1 b, (k : ℝ) * ((k * a / b : ℕ) : ℝ)
      - ((1 + a) / (2 * (b : ℝ))) * ∑ k ∈ Ico 1 b, (k : ℝ)
      + (1 / 2) * ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) + ((b : ℝ) - 1) / 4 := by
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have h : ∀ k ∈ Ico 1 b, ((k : ℝ) / b - 1 / 2) * ((k * a : ℝ) / b - ((k * a / b : ℕ) : ℝ) - 1 / 2)
      = ((a : ℝ) / b ^ 2) * (k : ℝ) ^ 2 - (1 / (b : ℝ)) * ((k : ℝ) * ((k * a / b : ℕ) : ℝ))
        - ((1 + a) / (2 * (b : ℝ))) * (k : ℝ) + (1 / 2) * ((k * a / b : ℕ) : ℝ) + 1 / 4 := by
    intro k _
    field_simp
    ring
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub (by omega : 1 ≤ b)]
  push_cast
  ring

lemma sq_floor_mod (hb : 0 < b) (hab : Nat.Coprime a b) :
    (b : ℝ) ^ 2 * ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) ^ 2
    = -(a : ℝ) ^ 2 * ∑ k ∈ Ico 1 b, (k : ℝ) ^ 2
      + 2 * a * b * ∑ k ∈ Ico 1 b, (k : ℝ) * ((k * a / b : ℕ) : ℝ)
      + ∑ k ∈ Ico 1 b, (k : ℝ) ^ 2 := by
  have hpt : ∀ k ∈ Ico 1 b, (b : ℝ) ^ 2 * ((k * a / b : ℕ) : ℝ) ^ 2
      = (-(a : ℝ) ^ 2) * (k : ℝ) ^ 2 + (2 * a * b) * ((k : ℝ) * ((k * a / b : ℕ) : ℝ))
        + ((k * a % b : ℕ) : ℝ) ^ 2 := by
    intro k _
    have h : ((b * (k * a / b) + k * a % b : ℕ) : ℝ) = ((k * a : ℕ) : ℝ) := by
      rw [Nat.div_add_mod]
    push_cast at h
    have hr : ((k * a % b : ℕ) : ℝ) = k * a - b * ((k * a / b : ℕ) : ℝ) := by linarith
    rw [hr]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_sq_mod hb hab]

lemma sq_floor_lattice (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) ^ 2
    = ((b : ℝ) - 1) * ((a : ℝ) - 1) ^ 2
      - 2 * ∑ j ∈ Ico 1 a, (j : ℝ) * ((j * b / a : ℕ) : ℝ)
      + ∑ j ∈ Ico 1 a, ((j * b / a : ℕ) : ℝ) := by
  have hq : ∀ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) ^ 2
      = ∑ j ∈ Ico 1 a, (if j * b < k * a then (2 * (j : ℝ) - 1) else 0) := by
    intro k hk
    rw [mem_Ico] at hk
    rw [← Finset.sum_filter, filter_lt_eq ha hab.symm (by omega) hk.2]
    have key : ∀ m : ℕ, ∑ j ∈ Icc 1 m, (2 * (j : ℝ) - 1) = (m : ℝ) ^ 2 := by
      intro m
      induction m with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
    rw [key]
  rw [Finset.sum_congr rfl hq, Finset.sum_comm]
  have hin : ∀ j ∈ Ico 1 a, ∑ k ∈ Ico 1 b, (if j * b < k * a then (2 * (j : ℝ) - 1) else 0)
      = (2 * (j : ℝ) - 1) * (((b : ℝ) - 1) - ((j * b / a : ℕ) : ℝ)) := by
    intro j hj
    rw [mem_Ico] at hj
    have hc := cnt_split hb hab (by omega : 0 < j) hj.2
    have hc' : (((Ico 1 b).filter (fun k => j * b < k * a)).card : ℝ) + ((j * b / a : ℕ) : ℝ)
        = (b : ℝ) - 1 := by
      have : (((((Ico 1 b).filter (fun k => j * b < k * a)).card + j * b / a : ℕ)) : ℝ)
          = ((b - 1 : ℕ) : ℝ) := by rw [hc]
      push_cast [Nat.cast_sub (by omega : 1 ≤ b)] at this
      linarith
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (((Ico 1 b).filter (fun k => j * b < k * a)).card : ℝ)
        = ((b : ℝ) - 1) - ((j * b / a : ℕ) : ℝ) := by linarith
    rw [this]
    ring
  rw [Finset.sum_congr rfl hin]
  have hexp : ∀ j ∈ Ico 1 a, (2 * (j : ℝ) - 1) * (((b : ℝ) - 1) - ((j * b / a : ℕ) : ℝ))
      = (2 * ((b : ℝ) - 1)) * (j : ℝ) + (-((b : ℝ) - 1)) - 2 * ((j : ℝ) * ((j * b / a : ℕ) : ℝ))
        + ((j * b / a : ℕ) : ℝ) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul]
  rw [sum_Ico_id a (by omega), Nat.cast_sub (by omega : 1 ≤ a)]
  push_cast
  ring

/-- Sawtooth form of the Dedekind sum, in terms of natural-number floors:
`∑_{k=1}^{b-1} ((k/b)) ((k a / b))` with `((x)) = x - ⌊x⌋ - 1/2` (valid when `b ∤ k a`). -/
noncomputable def sawSum (a b : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 b, ((k : ℝ) / b - 1 / 2) * ((k * a : ℝ) / b - ((k * a / b : ℕ) : ℝ) - 1 / 2)

/-- Beck §10.4 (CX-148), sawtooth form: the reciprocity law for the Dedekind sum
`∑ ((k/b)) ((k a / b))`, proved by lattice-point counting. -/
@[kb "beck2025" "Dedekind sum §10.4, p. 165"]
theorem sawSum_reciprocity (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    sawSum a b + sawSum b a
      = -1 / 4 + ((a : ℝ) / b + 1 / ((a : ℝ) * b) + (b : ℝ) / a) / 12 := by
  have ha' : (a : ℝ) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by positivity
  unfold sawSum
  rw [sawSum_expand hb, sawSum_expand ha]
  have E4 := sq_floor_mod hb hab
  have E5 := sq_floor_lattice ha hb hab
  have F1 := sum_floor hb hab
  have F2 := sum_floor ha hab.symm
  rw [sum_Ico_id a (by omega), sum_Ico_sq a (by omega), sum_Ico_id b (by omega),
    sum_Ico_sq b (by omega)]
  rw [sum_Ico_sq b (by omega)] at E4
  rw [F1, F2]
  set Q := ∑ k ∈ Ico 1 b, ((k * a / b : ℕ) : ℝ) ^ 2 with hQ
  set T := ∑ k ∈ Ico 1 b, (k : ℝ) * ((k * a / b : ℕ) : ℝ) with hT
  set T' := ∑ j ∈ Ico 1 a, (j : ℝ) * ((j * b / a : ℕ) : ℝ) with hT'
  rw [F2] at E5
  have hT1 : T = ((b : ℝ) ^ 2 * Q + (a ^ 2 - 1) * ((b - 1) * b * (2 * b - 1) / 6)) / (2 * a * b) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have hT2 : T' = (((b : ℝ) - 1) * ((a : ℝ) - 1) ^ 2 + ((b : ℝ) - 1) * ((a : ℝ) - 1) / 2 - Q) / 2 := by
    linarith
  rw [hT1, hT2]
  field_simp
  ring

/-! ### The cotangent form -/

/-- The Dedekind sum `s(a, b) = (1 / 4b) ∑_{k=1}^{b-1} cot (π k a / b) cot (π k / b)`. -/
@[kb "beck2025" "Dedekind sum §10.4, p. 165"]
noncomputable def dedekindSumCot (a b : ℕ) : ℝ :=
  1 / (4 * (b : ℝ)) * ∑ k ∈ Ico 1 b, Real.cot (π * k * a / b) * Real.cot (π * k / b)

/-- The cotangent form of the Dedekind sum equals the sawtooth form. -/
@[kb "beck2025" "Dedekind sum §10.4, p. 165"]
theorem dedekindSumCot_eq_sawSum (hb : 0 < b) (hab : Nat.Coprime a b) :
    dedekindSumCot a b = sawSum a b := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hcot : ∀ k ∈ Ico 1 b, Real.cot (π * k * a / b)
      = -2 * ∑ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * Real.sin (2 * π * n * ((k * a : ℕ) : ℝ) / b) := by
    intro k hk
    rw [mem_Ico] at hk
    have hm0 : 0 < k * a % b := Nat.pos_of_ne_zero (mod_ne_zero_of_coprime hab hk.1 hk.2)
    have hmb : k * a % b < b := Nat.mod_lt _ hb
    have hC := sawtooth_sine_sum hm0 hmb
    have e : π * k * a / b = π * ((k * a : ℕ) : ℝ) / b := by push_cast; ring
    rw [e, cot_mod b (k * a) hb]
    have h : ∀ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * Real.sin (2 * π * n * ((k * a : ℕ) : ℝ) / b)
        = ((n : ℝ) / b - 1 / 2) * Real.sin (2 * π * n * ((k * a % b : ℕ) : ℝ) / b) := by
      intro n _
      rw [sin_mod b n (k * a) hb]
    rw [Finset.sum_congr rfl h, hC]
    ring
  have hA : ∀ n ∈ Ico 1 b, ∑ k ∈ Ico 1 b,
      Real.cot (π * k / b) * Real.sin (2 * π * n * ((k * a : ℕ) : ℝ) / b)
      = (b : ℝ) - 2 * ((n * a % b : ℕ) : ℝ) := by
    intro n hn
    rw [mem_Ico] at hn
    have hm0 : 0 < n * a % b := Nat.pos_of_ne_zero (mod_ne_zero_of_coprime hab hn.1 hn.2)
    have hmb : n * a % b < b := Nat.mod_lt _ hb
    rw [← cot_sine_sum hm0 hmb]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e : 2 * π * n * ((k * a : ℕ) : ℝ) / b = 2 * π * k * ((n * a : ℕ) : ℝ) / b := by
      push_cast; ring
    rw [e, sin_mod b k (n * a) hb]
  have hswap : ∑ k ∈ Ico 1 b, Real.cot (π * k * a / b) * Real.cot (π * k / b)
      = -2 * ∑ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * ((b : ℝ) - 2 * ((n * a % b : ℕ) : ℝ)) := by
    calc ∑ k ∈ Ico 1 b, Real.cot (π * k * a / b) * Real.cot (π * k / b)
        = ∑ k ∈ Ico 1 b, ∑ n ∈ Ico 1 b, (-2) * (((n : ℝ) / b - 1 / 2) *
            (Real.cot (π * k / b) * Real.sin (2 * π * n * ((k * a : ℕ) : ℝ) / b))) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [hcot k hk, mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          ring
      _ = ∑ n ∈ Ico 1 b, ∑ k ∈ Ico 1 b, (-2) * (((n : ℝ) / b - 1 / 2) *
            (Real.cot (π * k / b) * Real.sin (2 * π * n * ((k * a : ℕ) : ℝ) / b))) :=
          Finset.sum_comm
      _ = -2 * ∑ n ∈ Ico 1 b, ((n : ℝ) / b - 1 / 2) * ((b : ℝ) - 2 * ((n * a % b : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [← Finset.mul_sum, ← Finset.mul_sum, hA n hn]
  unfold dedekindSumCot sawSum
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have h : ((b * (n * a / b) + n * a % b : ℕ) : ℝ) = ((n * a : ℕ) : ℝ) := by
    rw [Nat.div_add_mod]
  push_cast at h
  have hM : ((n * a % b : ℕ) : ℝ) = n * a - b * ((n * a / b : ℕ) : ℝ) := by linarith
  rw [hM]
  field_simp
  ring

/-- Beck §10.4, Exercise (2) (CX-148): the reciprocity law for the Dedekind sum
`s(a, b) = (1/4b) ∑_{k=1}^{b-1} cot (π k a / b) cot (π k / b)` of coprime positive integers. -/
@[kb "beck2025" "Dedekind sum §10.4, p. 165"]
theorem dedekindSumCot_reciprocity (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    dedekindSumCot a b + dedekindSumCot b a
      = -1 / 4 + ((a : ℝ) / b + 1 / ((a : ℝ) * b) + (b : ℝ) / a) / 12 := by
  rw [dedekindSumCot_eq_sawSum hb hab, dedekindSumCot_eq_sawSum ha hab.symm]
  exact sawSum_reciprocity ha hb hab

end Saw

end UndergradKB.ComplexAnalysis
