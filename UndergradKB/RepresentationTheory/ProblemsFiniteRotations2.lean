import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.ProblemsSU2b
import UndergradKB.RepresentationTheory.ProblemsFiniteRotations

/-! # Problem 3.24: the axis of a nontrivial rotation

A nontrivial element of `SO(3)` fixes exactly the vectors on one line (its axis).
-/

namespace UndergradKB.RepresentationTheory

open Quaternion Matrix SU2Quaternion

namespace SO3Rot

/-- The rotation matrix attached to the quaternion `r + a i + b j + c k`, in real coordinates. -/
def rm (r a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![r ^ 2 + a ^ 2 - b ^ 2 - c ^ 2, 2 * (a * b - r * c), 2 * (a * c + r * b);
    2 * (a * b + r * c), r ^ 2 - a ^ 2 + b ^ 2 - c ^ 2, 2 * (b * c - r * a);
    2 * (a * c - r * b), 2 * (b * c + r * a), r ^ 2 - a ^ 2 - b ^ 2 + c ^ 2]

theorem rmat_eq_rm (q : ℍ[ℝ]) : rmat q = rm q.re q.imI q.imJ q.imK := rfl

theorem rm_mulVec_axis {r a b c : ℝ} (hN : r ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    rm r a b c *ᵥ ![a, b, c] = ![a, b, c] := by
  funext i
  fin_cases i <;> simp [rm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · linear_combination a * hN
  · linear_combination b * hN
  · linear_combination c * hN

theorem rm_fixed {r a b c : ℝ} (hN : r ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 1) (hpos : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0)
    (x : Fin 3 → ℝ) (h : rm r a b c *ᵥ x = x) : ∃ t : ℝ, x = t • ![a, b, c] := by
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp [rm, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 e2
  set x0 := x 0
  set x1 := x 1
  set x2 := x 2
  have hE0 : -(b ^ 2 + c ^ 2) * x0 + (a * b - r * c) * x1 + (a * c + r * b) * x2 = 0 := by
    linear_combination (1 / 2) * e0 - (1 / 2) * x0 * hN
  have hE1 : (a * b + r * c) * x0 - (a ^ 2 + c ^ 2) * x1 + (b * c - r * a) * x2 = 0 := by
    linear_combination (1 / 2) * e1 - (1 / 2) * x1 * hN
  have hE2 : (a * c - r * b) * x0 + (b * c + r * a) * x1 - (a ^ 2 + b ^ 2) * x2 = 0 := by
    linear_combination (1 / 2) * e2 - (1 / 2) * x2 * hN
  have hw0 : b * x2 - c * x1 = 0 := by
    linear_combination r * hE0 - b * hE2 + c * hE1 - (b * x2 - c * x1) * hN
  have hw1 : c * x0 - a * x2 = 0 := by
    linear_combination r * hE1 - c * hE0 + a * hE2 - (c * x0 - a * x2) * hN
  have hw2 : a * x1 - b * x0 = 0 := by
    linear_combination r * hE2 - a * hE1 + b * hE0 - (a * x1 - b * x0) * hN
  have d0 : (a ^ 2 + b ^ 2 + c ^ 2) * x0 = (a * x0 + b * x1 + c * x2) * a := by
    linear_combination (-1) * hE0 + r * hw0
  have d1 : (a ^ 2 + b ^ 2 + c ^ 2) * x1 = (a * x0 + b * x1 + c * x2) * b := by
    linear_combination (-1) * hE1 + r * hw1
  have d2 : (a ^ 2 + b ^ 2 + c ^ 2) * x2 = (a * x0 + b * x1 + c * x2) * c := by
    linear_combination (-1) * hE2 + r * hw2
  refine ⟨(a * x0 + b * x1 + c * x2) / (a ^ 2 + b ^ 2 + c ^ 2), ?_⟩
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    show x0 = _ * a
    field_simp
    linarith
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    show x1 = _ * b
    field_simp
    linarith
  · simp only [Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
    show x2 = _ * c
    field_simp
    linarith

/-- A nontrivial rotation `M ∈ SO(3)` has a nonzero fixed vector `v`, and the fixed vectors of `M` are
exactly the multiples of `v`. -/
theorem fixed_axis {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsSO3 M) (hne : M ≠ 1) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ ∀ x, M *ᵥ x = x ↔ ∃ t : ℝ, x = t • v := by
  obtain ⟨u, rfl⟩ := inRange_of_isSO3 hM
  rw [rmat_eq_rm] at hne ⊢
  have hN : u.1.re ^ 2 + u.1.imI ^ 2 + u.1.imJ ^ 2 + u.1.imK ^ 2 = 1 := by
    have := normSq_eq_one_of_mem u.2
    rw [normSq_def'] at this
    exact this
  generalize u.1.re = r at hN hne ⊢
  generalize u.1.imI = a at hN hne ⊢
  generalize u.1.imJ = b at hN hne ⊢
  generalize u.1.imK = c at hN hne ⊢
  have hpos : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by
    intro h0
    apply hne
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hr : r ^ 2 = 1 := by rw [ha, hb, hc] at hN; linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rm, ha, hb, hc, hr]
  refine ⟨![a, b, c], ?_, fun x ↦ ⟨rm_fixed hN hpos x, ?_⟩⟩
  · intro h0
    apply hpos
    have ha : a = 0 := congrFun h0 0
    have hb : b = 0 := congrFun h0 1
    have hc : c = 0 := congrFun h0 2
    rw [ha, hb, hc]; norm_num
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, rm_mulVec_axis hN]

end SO3Rot

end UndergradKB.RepresentationTheory
