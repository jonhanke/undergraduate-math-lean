import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Common.Attr

/-!
# Dual WZ pairs (Petkovsek–Wilf–Zeilberger, "A = B", Section 7.3)

Replacing a numerator factorial `(a n + b k + c)!` by `(-1)^(a n + b k) / (-1 - a n - b k - c)!`
multiplies `F` and `G` by one constant, because of the gamma reflection formula; hence the
WZ equation is preserved.
-/

namespace UndergradKB.Combinatorics.AeqB

/-- CO-458. Factor lemma: for integers `a b n k` and a non-integer real `c`, the dual factor
`(-1)^(an+bk) / Γ(-(an+bk+c))` equals the constant `-sin(π c)/π` times `Γ(an+bk+c+1)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (dual identities), p. 141"]
theorem dual_factor_eq (a b n k : ℤ) (c : ℝ) (hc : ∀ m : ℤ, c ≠ m) :
    (-1 : ℝ) ^ (a * n + b * k) / Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c))
      = (-Real.sin (Real.pi * c) / Real.pi) *
        Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) := by
  set m : ℤ := a * n + b * k with hm
  have hsin : Real.sin (Real.pi * c) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp h
    apply hc j
    have hpi := Real.pi_pos
    have : ((j : ℝ) - c) * Real.pi = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hpi.ne'
  have hs : Real.sin (Real.pi * (m + c)) = (-1) ^ m * Real.sin (Real.pi * c) := by
    rw [show Real.pi * ((m : ℝ) + c) = Real.pi * c + m * Real.pi by ring]
    exact Real.sin_add_int_mul_pi _ _
  have hrefl := Real.Gamma_mul_Gamma_one_sub (-((m : ℝ) + c))
  have h1 : 1 - -((m : ℝ) + c) = (m : ℝ) + c + 1 := by ring
  rw [h1, show Real.pi * -((m : ℝ) + c) = -(Real.pi * (m + c)) by ring, Real.sin_neg, hs] at hrefl
  have hpow : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  have hpm : ((-1 : ℝ) ^ m) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hpi := Real.pi_ne_zero
  have hG : Real.Gamma (-((m : ℝ) + c)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrefl
    have : Real.pi / -((-1 : ℝ) ^ m * Real.sin (Real.pi * c)) ≠ 0 :=
      div_ne_zero hpi (neg_ne_zero.mpr (mul_ne_zero hpm hsin))
    exact this hrefl.symm
  have hne : -((-1 : ℝ) ^ m * Real.sin (Real.pi * c)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hpm hsin)
  have hPQ : Real.Gamma (-((m : ℝ) + c)) * Real.Gamma ((m : ℝ) + c + 1) *
      ((-1 : ℝ) ^ m * Real.sin (Real.pi * c)) = -Real.pi := by
    rw [eq_div_iff hne] at hrefl
    linarith
  rw [div_eq_iff hG]
  apply mul_left_cancel₀ hpm
  have h2 : (-1 : ℝ) ^ m * (-Real.sin (Real.pi * c) / Real.pi *
      Real.Gamma ((m : ℝ) + c + 1) * Real.Gamma (-((m : ℝ) + c))) =
      -(Real.Gamma (-((m : ℝ) + c)) * Real.Gamma ((m : ℝ) + c + 1) *
        ((-1 : ℝ) ^ m * Real.sin (Real.pi * c))) / Real.pi := by ring
  rw [h2, hPQ, hpow]
  field_simp

/-- CO-458. Dual identities: if `(F, G)` satisfy the WZ equation and both contain the factor
`Γ(an+bk+c+1)` (a numerator factorial), then replacing that factor by
`(-1)^(an+bk)/Γ(-(an+bk+c))` in both keeps the WZ equation. -/
@[kb "petkovsekwilfzeilberger1996" "text (dual identities), p. 141"]
theorem wzEq_dual (a b : ℤ) (c : ℝ) (hc : ∀ m : ℤ, c ≠ m) (F G H H' : ℤ → ℤ → ℝ)
    (hF : ∀ n k, F n k = Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) * H n k)
    (hG : ∀ n k, G n k = Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) * H' n k)
    (hWZ : WZEq F G) :
    WZEq
      (fun n k => (-1 : ℝ) ^ (a * n + b * k) /
        Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c)) * H n k)
      (fun n k => (-1 : ℝ) ^ (a * n + b * k) /
        Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c)) * H' n k) := by
  intro n k
  have e : ∀ n k, (-1 : ℝ) ^ (a * n + b * k) /
      Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c)) = (-Real.sin (Real.pi * c) / Real.pi) *
        Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) := fun n k => dual_factor_eq a b n k c hc
  have := hWZ n k
  simp only [hF, hG] at this
  simp only [e]
  linear_combination (-Real.sin (Real.pi * c) / Real.pi) * this

end UndergradKB.Combinatorics.AeqB
