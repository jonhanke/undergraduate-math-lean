import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import UndergradKB.Common.Attr

/-!
# Polar coordinates and arguments of complex numbers (Stitz–Zeager, Precalculus, Chapter 11)

A polar pair `(r, θ)` names the Cartesian point `(r cos θ, r sin θ)`.
-/

namespace UndergradKB.Precalculus

open UndergradKB

/-! ### Polar coordinates -/

/-- The Cartesian point named by the polar pair `(r, θ)`. -/
noncomputable def polarPoint (r θ : ℝ) : ℝ × ℝ := (r * Real.cos θ, r * Real.sin θ)

/-- The polar graph `r = a`: all points named by `(a, θ)`, `θ` arbitrary. -/
def polarGraphRadius (a : ℝ) : Set (ℝ × ℝ) := {p | ∃ θ : ℝ, p = polarPoint a θ}

/-- The polar graph `θ = α`: all points named by `(r, α)`, `r` arbitrary. -/
def polarGraphAngle (α : ℝ) : Set (ℝ × ℝ) := {p | ∃ r : ℝ, p = polarPoint r α}

/-- The polar graph `r = a` (`a ≠ 0`) is the circle `x² + y² = a²` of radius `|a|`, and the
polar graph `θ = α` is the line `x sin α = y cos α` through the origin at angle `α` (PC-252). -/
@[kb "stitzzeager2013" "Theorem 11.8, p. 952"]
theorem polar_graph_circle_and_line :
    (∀ a : ℝ, a ≠ 0 → polarGraphRadius a = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = |a| ^ 2}) ∧
    (∀ α : ℝ, polarGraphAngle α = {p : ℝ × ℝ | p.1 * Real.sin α = p.2 * Real.cos α}) := by
  constructor
  · intro a ha
    ext ⟨x, y⟩
    simp only [polarGraphRadius, Set.mem_setOf_eq, sq_abs]
    constructor
    · rintro ⟨θ, h⟩
      simp only [polarPoint, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      nlinarith [Real.sin_sq_add_cos_sq θ]
    · intro h
      set z : ℂ := ⟨x / a, y / a⟩ with hz
      have hn : ‖z‖ = 1 := by
        rw [Complex.norm_def, Complex.normSq_apply]
        have : z.re * z.re + z.im * z.im = 1 := by
          simp only [hz]; field_simp; nlinarith
        rw [this]; simp
      refine ⟨Complex.arg z, ?_⟩
      have h1 := Complex.norm_mul_cos_arg z
      have h2 := Complex.norm_mul_sin_arg z
      rw [hn] at h1 h2
      simp only [polarPoint, hz, one_mul] at h1 h2 ⊢
      rw [h1, h2]
      refine Prod.ext ?_ ?_ <;> field_simp
  · intro α
    ext ⟨x, y⟩
    simp only [polarGraphAngle, Set.mem_setOf_eq]
    constructor
    · rintro ⟨r, h⟩
      simp only [polarPoint, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      ring
    · intro h
      refine ⟨x * Real.cos α + y * Real.sin α, ?_⟩
      simp only [polarPoint, Prod.mk.injEq]
      constructor
      · linear_combination (-x) * Real.sin_sq_add_cos_sq α + Real.sin α * h
      · linear_combination (-Real.cos α) * h - y * Real.sin_sq_add_cos_sq α

/-! ### Different names for the same point (PC-253) -/

private lemma angle_eq_of_cos_sin {a b : ℝ} (hc : Real.cos a = Real.cos b)
    (hs : Real.sin a = Real.sin b) : ∃ n : ℤ, a = b + n * (2 * Real.pi) := by
  have h : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have : (a : ℂ) = b + n * (2 * Real.pi) := by
    have h2 : (a : ℂ) * Complex.I = (b + n * (2 * Real.pi) : ℂ) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero h2
  exact_mod_cast this

/-- `(r, θ)`, `(r, θ + 2πk)` and `(-r, θ + (2k+1)π)` name the same point; conversely, for
`r ≠ 0` any second polar name of the point `(r, θ)` is of one of these two forms (PC-253). -/
@[kb "stitzzeager2013" "§11.5, p. 967"]
theorem polar_point_same_names (r θ : ℝ) (k : ℤ) :
    polarPoint r (θ + k * (2 * Real.pi)) = polarPoint r θ ∧
    polarPoint (-r) (θ + (2 * k + 1) * Real.pi) = polarPoint r θ ∧
    (r ≠ 0 → ∀ r' θ' : ℝ, polarPoint r' θ' = polarPoint r θ →
      (r' = r ∧ ∃ n : ℤ, θ' = θ + n * (2 * Real.pi)) ∨
      (r' = -r ∧ ∃ n : ℤ, θ' = θ + (2 * n + 1) * Real.pi)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [polarPoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  · have h : θ + (2 * k + 1) * Real.pi = (θ + Real.pi) + k * (2 * Real.pi) := by ring
    rw [h]
    simp [polarPoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  · intro hr r' θ' h
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hsq : r' ^ 2 = r ^ 2 := by
      linear_combination (r' * Real.cos θ' + r * Real.cos θ) * h1 +
        (r' * Real.sin θ' + r * Real.sin θ) * h2 - r' ^ 2 * Real.sin_sq_add_cos_sq θ' +
        r ^ 2 * Real.sin_sq_add_cos_sq θ
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hc : Real.cos θ' = Real.cos θ := mul_left_cancel₀ hr h1
      have hs : Real.sin θ' = Real.sin θ := mul_left_cancel₀ hr h2
      exact angle_eq_of_cos_sin hc hs
    · right
      refine ⟨rfl, ?_⟩
      have hc : Real.cos θ' = Real.cos (θ + Real.pi) := by
        rw [Real.cos_add_pi]; apply mul_left_cancel₀ hr; linarith
      have hs : Real.sin θ' = Real.sin (θ + Real.pi) := by
        rw [Real.sin_add_pi]; apply mul_left_cancel₀ hr; linarith
      obtain ⟨n, hn⟩ := angle_eq_of_cos_sin hc hs
      exact ⟨n, by rw [hn]; ring⟩

/-! ### Arguments of a complex number (PC-260, PC-262) -/

/-- The set of all arguments of `z`: the angles `θ` with `z = |z| (cos θ + i sin θ)`. -/
def complexArgs (z : ℂ) : Set ℝ :=
  {θ | z = (‖z‖ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)}

private lemma mem_complexArgs {z : ℂ} {θ : ℝ} :
    θ ∈ complexArgs z ↔ z.re = ‖z‖ * Real.cos θ ∧ z.im = ‖z‖ * Real.sin θ := by
  unfold complexArgs
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨by simpa [-Complex.ofReal_cos, -Complex.ofReal_sin] using congrArg Complex.re h,
      by simpa [-Complex.ofReal_cos, -Complex.ofReal_sin] using congrArg Complex.im h⟩
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin] <;> linarith

/-- The modulus is the polar radius of `(Re z, Im z)`, the principal argument `Arg z` is an
argument lying in `(-π, π]`, and every argument is `Arg z` plus a multiple of `2π` when
`z ≠ 0` (PC-260). -/
@[kb "stitzzeager2013" "Definition 11.2, p. 1003"]
theorem complex_modulus_arguments (z : ℂ) :
    ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) ∧
    Complex.arg z ∈ complexArgs z ∧ Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi ∧
    (z ≠ 0 → complexArgs z = {θ | ∃ n : ℤ, θ = Complex.arg z + n * (2 * Real.pi)}) := by
  refine ⟨?_, ?_, Complex.arg_mem_Ioc z, fun hz => ?_⟩
  · rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  · exact mem_complexArgs.mpr ⟨(Complex.norm_mul_cos_arg z).symm, (Complex.norm_mul_sin_arg z).symm⟩
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    ext θ
    rw [mem_complexArgs]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have c1 := Complex.norm_mul_cos_arg z
      have c2 := Complex.norm_mul_sin_arg z
      exact angle_eq_of_cos_sin (mul_left_cancel₀ hn.ne' (by linarith))
        (mul_left_cancel₀ hn.ne' (by linarith))
    · rintro ⟨n, rfl⟩
      rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
      exact ⟨(Complex.norm_mul_cos_arg z).symm, (Complex.norm_mul_sin_arg z).symm⟩

/-- Arguments by cases: `tan θ = Im z / Re z` when `Re z ≠ 0`; the arguments are `π/2 + 2πk`
(if `Im z > 0`) or `-π/2 + 2πk` (if `Im z < 0`) when `Re z = 0`; every real number is an
argument of `0` (PC-262). -/
@[kb "stitzzeager2013" "Theorem 11.15, p. 1007"]
theorem complex_arguments_cases (z : ℂ) :
    (z.re ≠ 0 → ∀ θ ∈ complexArgs z, Real.tan θ = z.im / z.re) ∧
    (z.re = 0 → 0 < z.im →
      complexArgs z = {θ | ∃ n : ℤ, θ = Real.pi / 2 + n * (2 * Real.pi)}) ∧
    (z.re = 0 → z.im < 0 →
      complexArgs z = {θ | ∃ n : ℤ, θ = -(Real.pi / 2) + n * (2 * Real.pi)}) ∧
    (z = 0 → complexArgs z = Set.univ) := by
  refine ⟨fun hre θ hθ => ?_, fun hre him => ?_, fun hre him => ?_, fun hz => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_complexArgs.mp hθ
    have hcos : Real.cos θ ≠ 0 := by
      intro hc; rw [hc, mul_zero] at h1; exact hre h1
    have hn : ‖z‖ ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact hre h1
    rw [Real.tan_eq_sin_div_cos, h1, h2]
    field_simp
  · have hz : z ≠ 0 := fun h => by simp [h] at him
    have := (complex_modulus_arguments z).2.2.2 hz
    rw [this, (Complex.arg_eq_pi_div_two_iff).mpr ⟨hre, him⟩]
  · have hz : z ≠ 0 := fun h => by simp [h] at him
    have := (complex_modulus_arguments z).2.2.2 hz
    rw [this, (Complex.arg_eq_neg_pi_div_two_iff).mpr ⟨hre, him⟩]
  · ext θ
    simp only [Set.mem_univ, iff_true]
    rw [mem_complexArgs]
    simp [hz]

end UndergradKB.Precalculus
