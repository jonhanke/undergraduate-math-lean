import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 1 (Complex Numbers): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`). -/

namespace UndergradKB.ComplexAnalysis.Course.Beck1
open Complex Polynomial
open scoped ComplexConjugate

/-- Beck Proposition 1.1.2 (CX-002). A nonzero complex number has inverse conj z over |z|^2. -/
@[kb "beck2025" "Proposition 1.1.2, p. 12"]
theorem inv_eq_conj_div_normSq (z : ℂ) : z⁻¹ = conj z / (Complex.normSq z : ℂ) :=
  by rw [Complex.inv_def]; simp [div_eq_mul_inv]

/-- Beck Theorem 1.1.4 (CX-004). A nonconstant complex polynomial of degree d has d roots
counted with multiplicity. -/
@[kb "beck2025" "Theorem 1.1.4, p. 14"]
theorem fundamental_theorem_of_algebra (p : ℂ[X]) (_hp : 0 < p.natDegree) :
    p.roots.card = p.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

/-- Beck Definition 1.2.2 (CX-005). Polar form: z = |z| (cos(arg z) + i sin(arg z)); in rectangular
terms x = r cos phi and y = r sin phi. -/
@[kb "beck2025" "Definition 1.2.2, p. 15"]
theorem polar_form (z : ℂ) :
    z.re = ‖z‖ * Real.cos (Complex.arg z) ∧ z.im = ‖z‖ * Real.sin (Complex.arg z) :=
  ⟨(Complex.norm_mul_cos_arg z).symm, (Complex.norm_mul_sin_arg z).symm⟩

/-- Beck Proposition 1.2.3 (CX-006). The modulus of z1 - z2 is the Euclidean distance of the points. -/
@[kb "beck2025" "Proposition 1.2.3, p. 15"]
theorem norm_sub_eq_euclidean_dist (z₁ z₂ : ℂ) :
    ‖z₁ - z₂‖ = Real.sqrt ((z₁.re - z₂.re) ^ 2 + (z₁.im - z₂.im) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [sq]

/-- Beck Proposition 1.2.7 (CX-007), parts (a)-(f), for e^{i phi} = exp(i phi). -/
@[kb "beck2025" "Proposition 1.2.7, p. 18"]
theorem exp_i_mul_properties :
    (∀ φ₁ φ₂ : ℝ, exp (φ₁ * I) * exp (φ₂ * I) = exp (↑(φ₁ + φ₂) * I)) ∧
    exp ((0 : ℝ) * I) = 1 ∧
    (∀ φ : ℝ, 1 / exp (φ * I) = exp (↑(-φ) * I)) ∧
    (∀ φ : ℝ, exp (↑(φ + 2 * Real.pi) * I) = exp (φ * I)) ∧
    (∀ φ : ℝ, ‖exp (φ * I)‖ = 1) ∧
    (∀ φ : ℝ, HasDerivAt (fun t : ℝ => exp (t * I)) (I * exp (φ * I)) φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b; rw [← Complex.exp_add]; push_cast; ring_nf
  · simp
  · intro φ; rw [one_div, ← Complex.exp_neg]; push_cast; ring_nf
  · intro φ
    have := Complex.exp_periodic.nat_mul 1
    simp only [Nat.cast_one, one_mul] at this
    push_cast
    rw [add_mul, Complex.exp_add]
    have h : exp (2 * ↑Real.pi * I) = 1 := Complex.exp_two_pi_mul_I
    rw [h, mul_one]
  · intro φ; exact Complex.norm_exp_ofReal_mul_I φ
  · intro φ
    have h := ((Complex.ofRealCLM.hasDerivAt (x := φ)).mul_const I).cexp
    simpa [mul_comm] using h

/-- Beck Definition 1.2.8 (CX-008). A complex number is a root of unity (of the form
e^{2 pi i m/n}, n > 0) iff some positive power of it is 1. -/
@[kb "beck2025" "Definition 1.2.8, p. 18"]
theorem root_of_unity_iff (ζ : ℂ) :
    (∃ (m : ℤ) (n : ℕ), 0 < n ∧ ζ = exp (2 * Real.pi * I * ((m : ℂ) / n))) ↔
      ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1 := by
  constructor
  · rintro ⟨m, n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    rw [← Complex.exp_nat_mul]
    have : (n : ℂ) * (2 * ↑Real.pi * I * ((m : ℂ) / n)) = m * (2 * Real.pi * I) := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · rintro ⟨n, hn, h⟩
    have hne : ζ ≠ 0 := by
      rintro rfl; simp [zero_pow hn.ne'] at h
    let u : ℂˣ := Units.mk0 ζ hne
    have : NeZero n := ⟨hn.ne'⟩
    have hu : u ∈ rootsOfUnity n ℂ := by
      rw [_root_.mem_rootsOfUnity]; ext; simpa [u] using h
    obtain ⟨i, -, hi⟩ := (Complex.mem_rootsOfUnity n u).1 hu
    exact ⟨i, n, hn, by rw [Int.cast_natCast]; simpa [u] using hi.symm⟩

/-- Beck Example 1.2.9 (CX-008). The 4th roots of unity are 1, -1, i, -i, and i is primitive. -/
@[kb "beck2025" "Example 1.2.9, p. 18"]
theorem fourth_roots_of_unity :
    {z : ℂ | z ^ 4 = 1} = {1, -1, I, -I} ∧ IsPrimitiveRoot I 4 := by
  refine ⟨?_, ?_⟩
  · ext z
    simp only [Set.mem_ofPred_eq,Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h' : (z - 1) * (z + 1) * (z - I) * (z + I) = 0 := by
        have : (z - 1) * (z + 1) * (z - I) * (z + I) = z ^ 4 - 1 := by
          linear_combination (-(z ^ 2 - 1)) * Complex.I_sq
        rw [this, h]; ring
      rcases mul_eq_zero.1 h' with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · left; exact sub_eq_zero.1 h3
          · right; left; exact eq_neg_of_add_eq_zero_left h3
        · right; right; left; exact sub_eq_zero.1 h2
      · right; right; right; exact eq_neg_of_add_eq_zero_left h1
    · have hI : I ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
      rintro (rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · exact hI
      · rw [neg_pow, hI]; norm_num
  · exact Complex.isPrimitiveRoot_I

/-- Beck Proposition 1.3.3 (CX-010), parts (a)-(i): properties of the conjugate. -/
@[kb "beck2025" "Proposition 1.3.3, p. 20"]
theorem conj_properties :
    (∀ z₁ z₂ : ℂ, conj (z₁ + z₂) = conj z₁ + conj z₂ ∧ conj (z₁ - z₂) = conj z₁ - conj z₂) ∧
    (∀ z₁ z₂ : ℂ, conj (z₁ * z₂) = conj z₁ * conj z₂) ∧
    (∀ z₁ z₂ : ℂ, conj (z₁ / z₂) = conj z₁ / conj z₂) ∧
    (∀ z : ℂ, conj (conj z) = z) ∧
    (∀ z : ℂ, ‖conj z‖ = ‖z‖) ∧
    (∀ z : ℂ, (‖z‖ ^ 2 : ℂ) = z * conj z) ∧
    (∀ z : ℂ, (z.re : ℂ) = (z + conj z) / 2) ∧
    (∀ z : ℂ, (z.im : ℂ) = (z - conj z) / (2 * I)) ∧
    (∀ φ : ℝ, conj (exp (φ * I)) = exp (-φ * I)) := by
  refine ⟨fun a b => ⟨map_add _ _ _, map_sub _ _ _⟩, map_mul _, map_div₀ _, Complex.conj_conj,
    Complex.norm_conj, ?_, ?_, ?_, ?_⟩
  · intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  · intro z; exact Complex.re_eq_add_conj z
  · intro z; exact Complex.im_eq_sub_conj z
  · intro φ
    rw [← Complex.exp_conj]; simp

/-- Beck Proposition 1.3.4 (CX-011). Triangle inequality. -/
@[kb "beck2025" "Proposition 1.3.4, p. 21"]
theorem triangle_inequality (z₁ z₂ : ℂ) : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ :=
  norm_add_le z₁ z₂

/-- Beck Corollary 1.3.5 (CX-012). Triangle inequality in its variants: with either signs, the
reverse triangle inequality, and the triangle inequality for finite sums. -/
@[kb "beck2025" "Corollary 1.3.5, p. 21"]
theorem triangle_inequality_variants :
    (∀ z₁ z₂ : ℂ, ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ ∧ ‖z₁ - z₂‖ ≤ ‖z₁‖ + ‖z₂‖) ∧
    (∀ z₁ z₂ : ℂ, |‖z₁‖ - ‖z₂‖| ≤ ‖z₁ + z₂‖ ∧ |‖z₁‖ - ‖z₂‖| ≤ ‖z₁ - z₂‖) ∧
    (∀ (n : ℕ) (z : Fin n → ℂ), ‖∑ k, z k‖ ≤ ∑ k, ‖z k‖) := by
  refine ⟨fun a b => ⟨norm_add_le a b, norm_sub_le a b⟩, fun a b => ⟨?_, abs_norm_sub_norm_le a b⟩,
    fun n z => norm_sum_le _ _⟩
  have := abs_norm_sub_norm_le a (-b)
  simpa [sub_neg_eq_add] using this

/-- Beck Example 1.4.4 (CX-014). Open disks and exteriors of circles are open; closed disks are closed. -/
@[kb "beck2025" "Example 1.4.4, p. 23"]
theorem disks_open_closed (a : ℂ) (r : ℝ) (_hr : 0 < r) :
    IsOpen {z : ℂ | ‖z - a‖ < r} ∧ IsOpen {z : ℂ | r < ‖z - a‖} ∧
      IsClosed {z : ℂ | ‖z - a‖ ≤ r} := by
  refine ⟨?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · exact isOpen_lt continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) continuous_const

/-- Beck Example 1.4.6 (CX-015). The closure of the open disk is the closed disk, and the boundary
of the disk is the circle. -/
@[kb "beck2025" "Example 1.4.6, p. 23"]
theorem closure_frontier_disk (a : ℂ) (r : ℝ) (hr : 0 < r) :
    closure {z : ℂ | ‖z - a‖ < r} = {z : ℂ | ‖z - a‖ ≤ r} ∧
      frontier {z : ℂ | ‖z - a‖ < r} = {z : ℂ | ‖z - a‖ = r} := by
  have h1 : {z : ℂ | ‖z - a‖ < r} = Metric.ball a r := by ext; simp [dist_eq_norm]
  have h2 : {z : ℂ | ‖z - a‖ ≤ r} = Metric.closedBall a r := by ext; simp [dist_eq_norm]
  have h3 : {z : ℂ | ‖z - a‖ = r} = Metric.sphere a r := by ext; simp
  rw [h1, h2, h3]
  exact ⟨closure_ball a hr.ne', frontier_ball a hr.ne'⟩

end UndergradKB.ComplexAnalysis.Course.Beck1
