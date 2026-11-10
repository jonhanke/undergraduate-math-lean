import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import UndergradKB.Trigonometry.PolarCurves

/-! # Cardioids and limaçons (OpenStax §10.4)

* `cardioid_cos`, `cardioid_sin`: the cardioids `r = a(1 + cos θ)` and `r = a(1 + sin θ)` pass through the pole
  and are symmetric about the polar axis, respectively the line `θ = π/2`;
* `limacon_inner_loop_pole`: for `0 < a < b` the limaçon `r = a + b cos θ` passes through the pole exactly twice
  as `θ` runs over `[0, 2π)` (the inner loop).
-/

namespace UndergradKB.Trigonometry

open Complex ComplexConjugate Set

/-- **Cardioid `r = a(1 + cos θ)`**: it passes through the pole and is symmetric about the polar axis.
(TR-138) -/
@[kb "openstaxalgtrig2e" "§10.4 Cardioids, p. 930"]
theorem cardioid_cos (a : ℝ) :
    (0 : ℂ) ∈ polarGraph (fun r θ => r = a * (1 + Real.cos θ)) ∧
      ∀ z ∈ polarGraph (fun r θ => r = a * (1 + Real.cos θ)),
        conj z ∈ polarGraph (fun r θ => r = a * (1 + Real.cos θ)) := by
  refine ⟨⟨0, Real.pi, by simp, by simp [polarPoint]⟩, polarGraph_symm_polarAxis (Or.inl ?_)⟩
  intro r θ h
  rwa [Real.cos_neg]

/-- **Cardioid `r = a(1 + sin θ)`**: it passes through the pole and is symmetric about the line `θ = π/2`.
(TR-138) -/
theorem cardioid_sin (a : ℝ) :
    (0 : ℂ) ∈ polarGraph (fun r θ => r = a * (1 + Real.sin θ)) ∧
      ∀ z ∈ polarGraph (fun r θ => r = a * (1 + Real.sin θ)),
        -conj z ∈ polarGraph (fun r θ => r = a * (1 + Real.sin θ)) := by
  refine ⟨⟨0, -(Real.pi / 2), by simp, by simp [polarPoint]⟩,
    polarGraph_symm_line_pi_div_two (Or.inr ?_)⟩
  intro r θ h
  rwa [Real.sin_pi_sub]

/-- **Limaçon with an inner loop**: for `0 < a < b`, the angles `θ ∈ [0, 2π)` at which `r = a + b cos θ`
vanishes (the curve passes through the pole) are exactly `arccos (-a/b)` and `2π - arccos (-a/b)`: two of them.
(TR-140) -/
@[kb "openstaxalgtrig2e" "§10.4 Limaçons with an inner loop, p. 934"]
theorem limacon_inner_loop_pole {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    {θ | θ ∈ Ico 0 (2 * Real.pi) ∧ a + b * Real.cos θ = 0} =
        {Real.arccos (-a / b), 2 * Real.pi - Real.arccos (-a / b)} ∧
      {θ | θ ∈ Ico 0 (2 * Real.pi) ∧ a + b * Real.cos θ = 0}.ncard = 2 := by
  have hb : 0 < b := ha.trans hab
  set c := -a / b with hc
  have hc0 : c < 0 := by rw [hc, neg_div]; exact neg_lt_zero.2 (div_pos ha hb)
  have hc1 : -1 < c := by
    rw [hc, neg_div, neg_lt_neg_iff, div_lt_one hb]; exact hab
  set α := Real.arccos c with hα
  have hα1 : Real.pi / 2 < α := Real.pi_div_two_lt_arccos.2 hc0
  have hα2 : α < Real.pi := Real.arccos_lt_pi.2 hc1
  have hcos : Real.cos α = c := Real.cos_arccos hc1.le (by linarith)
  have hiff : ∀ θ, a + b * Real.cos θ = 0 ↔ Real.cos θ = c := by
    intro θ
    rw [hc]
    constructor <;> intro h
    · field_simp; linarith
    · rw [h]; field_simp; ring
  have hset : {θ | θ ∈ Ico 0 (2 * Real.pi) ∧ a + b * Real.cos θ = 0} = {α, 2 * Real.pi - α} := by
    ext θ
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, mem_Ico, hiff]
    constructor
    · rintro ⟨⟨h0, h2⟩, hθ⟩
      rcases le_or_gt θ Real.pi with h | h
      · left
        rw [hα, ← hθ, Real.arccos_cos h0 h]
      · right
        have h' : Real.cos (2 * Real.pi - θ) = c := by rw [Real.cos_two_pi_sub, hθ]
        have := Real.arccos_cos (x := 2 * Real.pi - θ) (by linarith) (by linarith)
        rw [h', ← hα] at this
        linarith
    · rintro (rfl | rfl)
      · exact ⟨⟨by linarith, by linarith⟩, hcos⟩
      · exact ⟨⟨by linarith, by linarith⟩, by rw [Real.cos_two_pi_sub, hcos]⟩
  refine ⟨hset, ?_⟩
  rw [hset, ncard_pair]
  intro h
  linarith

end UndergradKB.Trigonometry
