import UndergradKB.Calculus.RiemannSums

/-! # Calculus: Simpson's rule

OpenStax Calculus 2:§3.6: Simpson's rule `S_n` (`n` even), its description as a weighted average of the midpoint and
trapezoidal sums, the error bound `M (b-a)^5 / (180 n^4)` for `|f⁗| ≤ M`, and convergence. -/

namespace UndergradKB.Calculus

open Set Finset intervalIntegral MeasureTheory Filter Topology

/-- OpenStax Calculus 2:§3.6 (CA-238). Simpson's rule `S_n` for `n` even: `n/2` parabolic panels of width `2Δx`,
`Δx = (b-a)/n`, each contributing `(Δx/3)(f(x_{2j}) + 4 f(x_{2j+1}) + f(x_{2j+2}))`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.6, p. 291"]
noncomputable def simpson (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((b - a) / n / 3) * ∑ j ∈ range (n / 2),
    (f (a + 2 * j * ((b - a) / n)) + 4 * f (a + (2 * j + 1) * ((b - a) / n))
      + f (a + (2 * j + 2) * ((b - a) / n)))

/-- OpenStax Calculus 2:Theorem 3.6 (CA-238). Simpson's rule in the weighted form `1, 4, 2, 4, ..., 4, 1` times
`Δx/3` (here `n = 2(k+1)`). -/
@[kb "openstaxcalculus2016" "2:Theorem 3.6, p. 291"]
theorem simpson_weights (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    simpson f a b (2 * (k + 1)) = ((b - a) / (2 * (k + 1) : ℕ) / 3) *
      (f a + f b + 4 * ∑ j ∈ range (k + 1), f (a + (2 * j + 1) * ((b - a) / (2 * (k + 1) : ℕ)))
        + 2 * ∑ j ∈ range k, f (a + (2 * j + 2) * ((b - a) / (2 * (k + 1) : ℕ)))) := by
  have hn : (2 * (k + 1) : ℕ) ≠ 0 := by omega
  have hn' : ((2 * (k + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn
  have h2 : 2 * (k + 1) / 2 = k + 1 := by omega
  unfold simpson
  rw [h2]
  congr 1
  simp only [sum_add_distrib, ← mul_sum]
  rw [sum_range_succ' (fun j : ℕ => f (a + 2 * (j : ℝ) * ((b - a) / (2 * (k + 1) : ℕ)))),
    sum_range_succ (fun j : ℕ => f (a + (2 * (j : ℝ) + 2) * ((b - a) / (2 * (k + 1) : ℕ))))]
  have hb : a + (2 * (k : ℝ) + 2) * ((b - a) / (2 * (k + 1) : ℕ)) = b := by
    push_cast; field_simp; ring
  have e : ∀ j : ℕ, a + 2 * ((j + 1 : ℕ) : ℝ) * ((b - a) / (2 * (k + 1) : ℕ))
      = a + (2 * (j : ℝ) + 2) * ((b - a) / (2 * (k + 1) : ℕ)) := by
    intro j; push_cast; ring
  simp only [e, hb, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  ring

/-- OpenStax Calculus 2:§3.6 (CA-239). `S_{2n} = (2 M_n + T_n)/3`: Simpson's rule is a weighted average of the
midpoint and trapezoidal sums. -/
@[kb "openstaxcalculus2016" "2:§3.6 Remark (Simpson as weighted average), p. 292"]
theorem simpson_two_mul (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    simpson f a b (2 * n) = (2 * midSum f a b n + trapezoidal_integral f n a b) / 3 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [trapezoidal_integral_eq_avg f a b hn]
  unfold simpson midSum leftSum rightSum
  rw [show 2 * n / 2 = n by omega]
  push_cast
  have e0 : ∀ j : ℕ, a + 2 * (j : ℝ) * ((b - a) / (2 * n)) = regularPartition a b n j := by
    intro j; unfold regularPartition; field_simp
  have e1 : ∀ j : ℕ, a + (2 * (j : ℝ) + 1) * ((b - a) / (2 * n))
      = a + ((j : ℝ) + 1 / 2) * ((b - a) / n) := by
    intro j; field_simp
  have e2 : ∀ j : ℕ, a + (2 * (j : ℝ) + 2) * ((b - a) / (2 * n)) = regularPartition a b n (j + 1) := by
    intro j; unfold regularPartition; push_cast; field_simp
  simp only [e0, e1, e2, sum_add_distrib, ← mul_sum]
  field_simp
  ring

/-- Variant of `abs_le_of_abs_deriv_le` with an explicit constant `C'` with `C = C' (k+1)`. -/
theorem abs_le_of_abs_deriv_le' {φ φ' : ℝ → ℝ} {T C C' : ℝ} {k : ℕ}
    (h : ∀ x, HasDerivAt φ (φ' x) x) (h0 : φ 0 = 0) (hC : C = C' * (k + 1))
    (hb : ∀ t ∈ Icc 0 T, |φ' t| ≤ C * t ^ k) :
    ∀ t ∈ Icc 0 T, |φ t| ≤ C' * t ^ (k + 1) := by
  intro t ht
  have := abs_le_of_abs_deriv_le h h0 hb t ht
  have e : C / ((k : ℝ) + 1) = C' := by rw [hC]; field_simp
  rwa [e] at this

/-- One-panel Simpson error: on `[c-h, c+h]`, `|∫ f - (h/3)(f(c-h) + 4 f(c) + f(c+h))| ≤ M h^5 / 90`
when `|f⁗| ≤ M` there. -/
theorem simpson_panel_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {c h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ x ∈ Icc (c - h) (c + h), |iteratedDeriv 4 f x| ≤ M) :
    |(∫ x in c - h..c + h, f x) - h / 3 * (f (c - h) + 4 * f c + f (c + h))| ≤ M * h ^ 5 / 90 := by
  have hc : Continuous f := hf.continuous
  have f0 : ∀ x, HasDerivAt f (iteratedDeriv 1 f x) x := by
    intro x
    have := hasDerivAt_iteratedDeriv (n := 4) hf (k := 0) (by norm_num) x
    rwa [iteratedDeriv_zero] at this
  have f1 : ∀ x, HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f x) x :=
    hasDerivAt_iteratedDeriv (n := 4) hf (k := 1) (by norm_num)
  have f2 : ∀ x, HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f x) x :=
    hasDerivAt_iteratedDeriv (n := 4) hf (k := 2) (by norm_num)
  have f3 : ∀ x, HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f x) x :=
    hasDerivAt_iteratedDeriv (n := 4) hf (k := 3) (by norm_num)
  set F : ℝ → ℝ := fun u => ∫ y in (0:ℝ)..u, f y with hFdef
  have hF : ∀ x, HasDerivAt F (f x) x := hasDerivAt_integral_primitive hc
  have ht : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t / 3) (1 / 3) t := fun t => by
    simpa using (hasDerivAt_id t).div_const 3
  -- E3
  have hE3 : ∀ t, HasDerivAt
      (fun t => (1 / 3) * (iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t))
        - t / 3 * (iteratedDeriv 2 f (c + t) + iteratedDeriv 2 f (c - t)))
      (-(t / 3) * (iteratedDeriv 3 f (c + t) - iteratedDeriv 3 f (c - t))) t := by
    intro t
    have h1 := (hasDerivAt_shift_add f1 c t).sub (hasDerivAt_shift_sub f1 c t)
    have h2 := (hasDerivAt_shift_add f2 c t).add (hasDerivAt_shift_sub f2 c t)
    exact ((h1.const_mul (1 / 3)).sub ((ht t).mul h2)).congr_deriv (by simp only [Pi.add_apply]; ring)
  have hE2 : ∀ t, HasDerivAt
      (fun t => (2 / 3) * (f (c + t) + f (c - t)) - 4 / 3 * f c
        - t / 3 * (iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t)))
      ((1 / 3) * (iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t))
        - t / 3 * (iteratedDeriv 2 f (c + t) + iteratedDeriv 2 f (c - t))) t := by
    intro t
    have h0 := (hasDerivAt_shift_add f0 c t).add (hasDerivAt_shift_sub f0 c t)
    have h1 := (hasDerivAt_shift_add f1 c t).sub (hasDerivAt_shift_sub f1 c t)
    exact (((h0.const_mul (2 / 3)).sub_const (4 / 3 * f c)).sub ((ht t).mul h1)).congr_deriv (by simp only [Pi.sub_apply]; ring)
  have hE1 : ∀ t, HasDerivAt
      (fun t => F (c + t) - F (c - t) - t / 3 * (f (c - t) + 4 * f c + f (c + t)))
      ((2 / 3) * (f (c + t) + f (c - t)) - 4 / 3 * f c
        - t / 3 * (iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t))) t := by
    intro t
    have hF' := (hasDerivAt_shift_add hF c t).sub (hasDerivAt_shift_sub hF c t)
    have h0 := ((hasDerivAt_shift_sub f0 c t).add_const (4 * f c)).add (hasDerivAt_shift_add f0 c t)
    exact (hF'.sub ((ht t).mul h0)).congr_deriv (by simp only [Pi.add_apply]; ring)
  have b3 : ∀ t ∈ Icc 0 h,
      |-(t / 3) * (iteratedDeriv 3 f (c + t) - iteratedDeriv 3 f (c - t))| ≤ (2 * M / 3) * t ^ 2 := by
    intro t ht
    have := abs_sub_le_of_abs_deriv_le f3 hM (x := c - t) (y := c + t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : |c + t - (c - t)| = 2 * t := by rw [abs_of_nonneg (by linarith [ht.1])]; ring
    rw [e] at this
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t / 3)]
    calc t / 3 * |iteratedDeriv 3 f (c + t) - iteratedDeriv 3 f (c - t)| ≤ t / 3 * (M * (2 * t)) :=
          mul_le_mul_of_nonneg_left this (by linarith [ht.1])
      _ = 2 * M / 3 * t ^ 2 := by ring
  have b2 := abs_le_of_abs_deriv_le' hE3 (by simp) (C' := 2 * M / 9) (by push_cast; ring) b3
  have b1 := abs_le_of_abs_deriv_le' hE2 (by simp; ring) (C' := M / 18) (by push_cast; ring) b2
  have b0 := abs_le_of_abs_deriv_le' hE1 (by simp) (C' := M / 90) (by push_cast; ring) b1 h ⟨hh, le_rfl⟩
  have hint : ∫ x in c - h..c + h, f x = F (c + h) - F (c - h) :=
    integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hc.intervalIntegrable _ _)
  rw [hint]
  calc _ ≤ M / 90 * h ^ (4 + 1) := b0
    _ = _ := by ring

/-- OpenStax Calculus 2:§3.6 (CA-240). Simpson error bound: if `f` is `C⁴` and the fourth derivative is bounded by
`M` on `[a,b]`, then `|S_n - ∫_a^b f| ≤ M (b-a)^5 / (180 n^4)` for even `n > 0`. (`f` is `C⁴` on all of `ℝ`.) -/
@[kb "openstaxcalculus2016" "2:§3.6 Rule (Error Bound for Simpson's Rule), p. 292"]
theorem simpson_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : Even n) (hpos : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 4 f x| ≤ M) :
    |simpson f a b n - ∫ x in a..b, f x| ≤ M * (b - a) ^ 5 / (180 * n ^ 4) := by
  obtain ⟨m, hm⟩ := hn
  have hn2 : n = 2 * m := by omega
  subst hn2
  have hm0 : 0 < m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm0
  have hd : 0 ≤ (b - a) / ((2 * m : ℕ) : ℝ) := by
    have := sub_nonneg.2 hab; positivity
  have key := sum_panel_error_le hab hf.continuous.continuousOn hm0
    (fun j => (b - a) / ((2 * m : ℕ) : ℝ) / 3 *
      (f (a + 2 * j * ((b - a) / ((2 * m : ℕ) : ℝ))) + 4 * f (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ)))
        + f (a + (2 * j + 2) * ((b - a) / ((2 * m : ℕ) : ℝ)))))
    (B := M * ((b - a) / ((2 * m : ℕ) : ℝ)) ^ 5 / 90) (by
      intro j hj
      have hmi := regularPartition_mem hab hm0 hj.le
      have hmi1 := regularPartition_mem hab hm0 (Nat.succ_le_of_lt hj)
      have e1 : regularPartition a b m j =
          (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ))) - (b - a) / ((2 * m : ℕ) : ℝ) := by
        simp only [regularPartition]; push_cast; field_simp; ring
      have e2 : regularPartition a b m (j + 1) =
          (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ))) + (b - a) / ((2 * m : ℕ) : ℝ) := by
        simp only [regularPartition]; push_cast; field_simp; ring
      have e3 : a + 2 * (j : ℝ) * ((b - a) / ((2 * m : ℕ) : ℝ)) =
          (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ))) - (b - a) / ((2 * m : ℕ) : ℝ) := by ring
      have e4 : a + (2 * (j : ℝ) + 2) * ((b - a) / ((2 * m : ℕ) : ℝ)) =
          (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ))) + (b - a) / ((2 * m : ℕ) : ℝ) := by ring
      rw [e1, e2, e3, e4]
      have := simpson_panel_error_le hf (c := a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ)))
        (h := (b - a) / ((2 * m : ℕ) : ℝ)) (M := M) hd (fun x hx => hM x
          ⟨by rw [e1] at hmi; exact hmi.1.trans hx.1, by rw [e2] at hmi1; exact hx.2.trans hmi1.2⟩)
      rwa [abs_sub_comm])
  have e : simpson f a b (2 * m) = ∑ j ∈ range m, (b - a) / ((2 * m : ℕ) : ℝ) / 3 *
      (f (a + 2 * j * ((b - a) / ((2 * m : ℕ) : ℝ))) + 4 * f (a + (2 * j + 1) * ((b - a) / ((2 * m : ℕ) : ℝ)))
        + f (a + (2 * j + 2) * ((b - a) / ((2 * m : ℕ) : ℝ)))) := by
    rw [simpson, mul_sum, show 2 * m / 2 = m by omega]
  rw [e]
  refine key.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- OpenStax Calculus 2:Theorem 3.6 (CA-238). Simpson's rule converges: `S_{2n} → ∫_a^b f` for continuous `f`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.6, p. 291"]
theorem tendsto_simpson {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => simpson f a b (2 * n)) atTop (𝓝 (∫ x in a..b, f x)) := by
  have := (((tendsto_midSum hab hf).const_mul 2).add (tendsto_trapezoid hab hf)).div_const 3
  rw [show (2 * (∫ x in a..b, f x) + ∫ x in a..b, f x) / 3 = ∫ x in a..b, f x by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (simpson_two_mul f a b hn).symm

end UndergradKB.Calculus
