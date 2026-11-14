import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.5 (graphs of polar equations). The graph of `r = f θ` is `polarGraphFn f`, the set of points
named by `(f θ, θ)` for some `θ`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

/-- The graph of the polar equation `r = f θ`: the points named by `(f θ, θ)`, `θ` arbitrary. -/
def polarGraphFn (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | ∃ θ : ℝ, p = polarPoint (f θ) θ}

/-! ## Helpers -/

/-- The graph of `r = a cos θ + b sin θ` is the circle `x² + y² = a x + b y`. -/
private theorem x11e_circle (a b : ℝ) :
    polarGraphFn (fun θ => a * cos θ + b * sin θ) = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = a * p.1 + b * p.2} := by
  ext ⟨x, y⟩
  simp only [polarGraphFn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    nlinarith [sin_sq_add_cos_sq θ]
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      by_cases hab : a = 0 ∧ b = 0
      · refine ⟨0, ?_⟩
        simp [polarPoint, hx, hy, hab.1, hab.2]
      · set w : ℂ := ⟨-b, a⟩ with hw
        have hwn : 0 < ‖w‖ := by
          rw [norm_pos_iff]
          intro hw0
          apply hab
          have h1 := congrArg Complex.re hw0
          have h2 := congrArg Complex.im hw0
          simp [hw] at h1 h2
          exact ⟨h2, h1⟩
        have c1 : ‖w‖ * cos (Complex.arg w) = -b := Complex.norm_mul_cos_arg w
        have c2 : ‖w‖ * sin (Complex.arg w) = a := Complex.norm_mul_sin_arg w
        refine ⟨Complex.arg w, ?_⟩
        have : a * cos (Complex.arg w) + b * sin (Complex.arg w) = 0 := by
          apply mul_left_cancel₀ hwn.ne'
          linear_combination a * c1 + b * c2
        simp [polarPoint, this, hx, hy]
    · set z : ℂ := ⟨x, y⟩ with hz
      have hn : 0 < ‖z‖ := by
        rw [norm_pos_iff]
        intro hz0
        apply h0
        have h1 := congrArg Complex.re hz0
        have h2 := congrArg Complex.im hz0
        simp [hz] at h1 h2
        rw [h1, h2]; ring
      have hx : x = ‖z‖ * cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
      have hy : y = ‖z‖ * sin (Complex.arg z) := (Complex.norm_mul_sin_arg z).symm
      have e1 : x ^ 2 + y ^ 2 = ‖z‖ ^ 2 := by
        have hc := sin_sq_add_cos_sq (Complex.arg z)
        have : x ^ 2 + y ^ 2 = ‖z‖ ^ 2 * (sin (Complex.arg z) ^ 2 + cos (Complex.arg z) ^ 2) := by
          rw [hx, hy]; ring
        rw [this, hc, mul_one]
      refine ⟨Complex.arg z, ?_⟩
      have hr : ‖z‖ = a * cos (Complex.arg z) + b * sin (Complex.arg z) := by
        apply mul_left_cancel₀ hn.ne'
        linear_combination (-1) * e1 + h + a * hx + b * hy
      simp only [polarPoint, Prod.mk.injEq]
      rw [← hr]
      exact ⟨hx, hy⟩

/-- Every point `(x, y)` is named by `(√(x² + y²), θ)` for some `θ ∈ [0, 2π]`. -/
private theorem x11e_name (x y : ℝ) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 2 * π ∧ (x, y) = polarPoint (√(x ^ 2 + y ^ 2)) θ := by
  set z : ℂ := ⟨x, y⟩ with hz
  have hn : ‖z‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [hz, sq]
  have hx : x = √(x ^ 2 + y ^ 2) * cos (Complex.arg z) := by rw [← hn]; exact (Complex.norm_mul_cos_arg z).symm
  have hy : y = √(x ^ 2 + y ^ 2) * sin (Complex.arg z) := by rw [← hn]; exact (Complex.norm_mul_sin_arg z).symm
  have hpi := pi_pos
  have h1 := Complex.arg_le_pi z
  have h2 := Complex.neg_pi_lt_arg z
  by_cases h : 0 ≤ Complex.arg z
  · refine ⟨Complex.arg z, h, by linarith, ?_⟩
    simp only [polarPoint, Prod.mk.injEq]
    exact ⟨hx, hy⟩
  · refine ⟨Complex.arg z + 2 * π, by linarith, by linarith, ?_⟩
    simp only [polarPoint, cos_add_two_pi, sin_add_two_pi, Prod.mk.injEq]
    exact ⟨hx, hy⟩

/-! ## Section 11.5 -/

/-- Stitz-Zeager Exercise 11.5.1: the polar graph `r = 6 sin θ` is the circle `x² + (y - 3)² = 9`. -/
@[kb "stitzzeager2013" "Exercise 11.5.1, p. 970"]
theorem exer_11_5_1 :
    polarGraphFn (fun θ => 6 * sin θ) = {p : ℝ × ℝ | p.1 ^ 2 + (p.2 - 3) ^ 2 = 9} := by
  have h := x11e_circle 0 6
  simp only [zero_mul, zero_add] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.5.2: the polar graph `r = 2 cos θ` is the circle `(x - 1)² + y² = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.5.2, p. 970"]
theorem exer_11_5_2 :
    polarGraphFn (fun θ => 2 * cos θ) = {p : ℝ × ℝ | (p.1 - 1) ^ 2 + p.2 ^ 2 = 1} := by
  have h := x11e_circle 2 0
  simp only [zero_mul, add_zero] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 11.5.25: the graphs `r = 2 cos θ` and `r = 2√3 sin θ` meet exactly at the pole
and at the point `(√3, π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.25, p. 970"]
theorem exer_11_5_25 :
    polarGraphFn (fun θ => 2 * cos θ) ∩ polarGraphFn (fun θ => 2 * √3 * sin θ) =
      {(0, 0), polarPoint (√3) (π / 6)} := by
  have h1 := x11e_circle 2 0
  have h2 := x11e_circle 0 (2 * √3)
  simp only [zero_mul, add_zero, zero_add] at h1 h2
  rw [h1, h2]
  have hs : (0 : ℝ) < √3 := by positivity
  have hss : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e : polarPoint (√3) (π / 6) = (3 / 2, √3 / 2) := by
    simp only [polarPoint, cos_pi_div_six, sin_pi_div_six, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb⟩
    have hx : x = √3 * y := by nlinarith
    rw [hx] at ha hb
    have : y * (4 * y - 2 * √3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; rw [hx, h]; simp
    · right
      have hy : y = √3 / 2 := by linarith
      refine ⟨?_, hy⟩
      rw [hx, hy]; nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.5.26: the graphs `r = 3 cos θ` and `r = sin θ` meet exactly at the pole and at
the point `(3√10/10, arctan 3)`. -/
@[kb "stitzzeager2013" "Exercise 11.5.26, p. 970"]
theorem exer_11_5_26 :
    polarGraphFn (fun θ => 3 * cos θ) ∩ polarGraphFn (fun θ => sin θ) =
      {(0, 0), polarPoint (3 * √10 / 10) (arctan 3)} := by
  have h1 := x11e_circle 3 0
  have h2 := x11e_circle 0 1
  simp only [zero_mul, add_zero, zero_add, one_mul] at h1 h2
  have h2' : polarGraphFn (fun θ => sin θ) = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = p.2} := by
    have := h2; simpa using this
  rw [h1, h2']
  have hs : (0 : ℝ) < √10 := by positivity
  have hss : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
  have h10 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have e : polarPoint (3 * √10 / 10) (arctan 3) = (3 / 10, 9 / 10) := by
    simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h10, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  rw [e]
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb⟩
    have hy : y = 3 * x := by nlinarith
    rw [hy] at ha
    have : x * (10 * x - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; rw [hy, h]; simp
    · right
      have hx : x = 3 / 10 := by linarith
      exact ⟨hx, by rw [hy, hx]; norm_num⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.5.31: the polar region `0 ≤ r ≤ 3`, `0 ≤ θ ≤ 2π` is the closed disk
`x² + y² ≤ 9`. -/
@[kb "stitzzeager2013" "Exercise 11.5.31, p. 970"]
theorem exer_11_5_31 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 3 ∧ 0 ≤ θ ∧ θ ≤ 2 * π ∧ p = polarPoint r θ} =
      {p | p.1 ^ 2 + p.2 ^ 2 ≤ 9} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, θ, h0, h3, -, -, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    rw [e]; nlinarith
  · intro h
    obtain ⟨θ, h1, h2, e⟩ := x11e_name x y
    refine ⟨√(x ^ 2 + y ^ 2), θ, Real.sqrt_nonneg _, ?_, h1, h2, e⟩
    rw [Real.sqrt_le_left (by norm_num)]; linarith

/-- Stitz-Zeager Exercise 11.5.48: the region `3 ≤ r ≤ 5`, `0 ≤ θ ≤ 2π` (outside `r = 3`, inside `r = 5`) is
the annulus `9 ≤ x² + y² ≤ 25`. -/
@[kb "stitzzeager2013" "Exercise 11.5.48, p. 971"]
theorem exer_11_5_48 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 3 ≤ r ∧ r ≤ 5 ∧ 0 ≤ θ ∧ θ ≤ 2 * π ∧ p = polarPoint r θ} =
      {p | 9 ≤ p.1 ^ 2 + p.2 ^ 2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 25} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, θ, h3, h5, -, -, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    rw [e]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    obtain ⟨θ, t1, t2, e⟩ := x11e_name x y
    refine ⟨√(x ^ 2 + y ^ 2), θ, ?_, ?_, t1, t2, e⟩
    · exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
    · rw [Real.sqrt_le_left (by norm_num)]; linarith

/-- Stitz-Zeager Exercise 11.5.62(a): `f(θ) = 2 + 4 cos θ` is even and the graph of `r = f θ` is symmetric
about the x-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.62a, p. 973"]
theorem exer_11_5_62_a :
    (∀ θ : ℝ, 2 + 4 * cos (-θ) = 2 + 4 * cos θ) ∧
      ∀ p ∈ polarGraphFn (fun θ => 2 + 4 * cos θ), (p.1, -p.2) ∈ polarGraphFn (fun θ => 2 + 4 * cos θ) := by
  refine ⟨fun θ => by rw [cos_neg], ?_⟩
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨-θ, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [polarPoint, cos_neg, sin_neg, Prod.mk.injEq]
  exact ⟨trivial, by ring⟩

/-- Stitz-Zeager Exercise 11.5.62(b): `f(θ) = 3 sin 2θ` is not even (`f(-π/4) ≠ f(π/4)`), yet the graph of
`r = f θ` is symmetric about the x-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.62b, p. 973"]
theorem exer_11_5_62_b :
    3 * sin (2 * (-(π / 4))) ≠ 3 * sin (2 * (π / 4)) ∧
      ∀ p ∈ polarGraphFn (fun θ => 3 * sin (2 * θ)),
        (p.1, -p.2) ∈ polarGraphFn (fun θ => 3 * sin (2 * θ)) := by
  refine ⟨?_, ?_⟩
  · rw [show 2 * (-(π / 4)) = -(π / 2) by ring, show 2 * (π / 4) = π / 2 by ring, sin_neg,
      sin_pi_div_two]
    norm_num
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨π - θ, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e : 2 * (π - θ) = -(2 * θ) + 2 * π := by ring
  simp only [polarPoint, e, sin_add_two_pi, sin_neg, cos_pi_sub, sin_pi_sub, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.5.63(a): `f(θ) = 5 sin 2θ` is odd and the graph of `r = f θ` is symmetric about
the origin. -/
@[kb "stitzzeager2013" "Exercise 11.5.63a, p. 973"]
theorem exer_11_5_63_a :
    (∀ θ : ℝ, 5 * sin (2 * (-θ)) = -(5 * sin (2 * θ))) ∧
      ∀ p ∈ polarGraphFn (fun θ => 5 * sin (2 * θ)),
        (-p.1, -p.2) ∈ polarGraphFn (fun θ => 5 * sin (2 * θ)) := by
  refine ⟨fun θ => by rw [mul_neg, sin_neg]; ring, ?_⟩
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨θ + π, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e : 2 * (θ + π) = 2 * θ + 2 * π := by ring
  simp only [polarPoint, e, sin_add_two_pi, cos_add_pi, sin_add_pi, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.5.63(b): `f(θ) = 3 cos 2θ` is not odd (`f(0) ≠ -f(0)`), yet the graph of
`r = f θ` is symmetric about the origin. -/
@[kb "stitzzeager2013" "Exercise 11.5.63b, p. 973"]
theorem exer_11_5_63_b :
    3 * cos (2 * (-(0 : ℝ))) ≠ -(3 * cos (2 * (0 : ℝ))) ∧
      ∀ p ∈ polarGraphFn (fun θ => 3 * cos (2 * θ)),
        (-p.1, -p.2) ∈ polarGraphFn (fun θ => 3 * cos (2 * θ)) := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨θ + π, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e : 2 * (θ + π) = 2 * θ + 2 * π := by ring
  simp only [polarPoint, e, cos_add_two_pi, cos_add_pi, sin_add_pi, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.5.64(a): `f(θ) = 4 - 2 sin θ` satisfies `f(π - θ) = f(θ)` and the graph of
`r = f θ` is symmetric about the y-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.64a, p. 973"]
theorem exer_11_5_64_a :
    (∀ θ : ℝ, 4 - 2 * sin (π - θ) = 4 - 2 * sin θ) ∧
      ∀ p ∈ polarGraphFn (fun θ => 4 - 2 * sin θ),
        (-p.1, p.2) ∈ polarGraphFn (fun θ => 4 - 2 * sin θ) := by
  refine ⟨fun θ => by rw [sin_pi_sub], ?_⟩
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨π - θ, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [polarPoint, cos_pi_sub, sin_pi_sub, Prod.mk.injEq]
  exact ⟨by ring, trivial⟩

/-- Stitz-Zeager Exercise 11.5.64(b): `f(θ) = 5 sin 2θ` has `f(π - π/4) ≠ f(π/4)`, yet its graph is
symmetric about the y-axis. -/
@[kb "stitzzeager2013" "Exercise 11.5.64b, p. 974"]
theorem exer_11_5_64_b :
    5 * sin (2 * (π - π / 4)) ≠ 5 * sin (2 * (π / 4)) ∧
      ∀ p ∈ polarGraphFn (fun θ => 5 * sin (2 * θ)),
        (-p.1, p.2) ∈ polarGraphFn (fun θ => 5 * sin (2 * θ)) := by
  refine ⟨?_, ?_⟩
  · rw [show 2 * (π - π / 4) = -(π / 2) + 2 * π by ring, show 2 * (π / 4) = π / 2 by ring,
      sin_add_two_pi, sin_neg, sin_pi_div_two]
    norm_num
  rintro ⟨x, y⟩ ⟨θ, h⟩
  refine ⟨-θ, ?_⟩
  simp only [polarPoint, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [polarPoint, mul_neg, cos_neg, sin_neg, Prod.mk.injEq]
  constructor <;> ring

end UndergradKB.Precalculus.Course
