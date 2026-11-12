import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import UndergradKB.ComplexAnalysis.Laurent
import UndergradKB.ComplexAnalysis.Singularities
import UndergradKB.Common.Attr

/-! # Uniqueness of Laurent coefficients and classification of singularities
(rows CX-132, CX-139)

* Uniqueness of the coefficients of a Laurent series converging on an annulus
  (Beck Corollary 8.3.7), by termwise integration against `(z - c)^(-(n+1))`, and the existence of
  the Laurent expansion on a punctured disc (Corollary 8.3.8).
* Classification of an isolated singularity by the negative-index Laurent coefficients (Beck
  Proposition 9.1.10): removable, pole (with the normal form of the pole), essential. -/

open Complex Metric Set Filter Topology Real MeasureTheory

namespace UndergradKB.ComplexAnalysis

/-! ## Uniqueness of the coefficients -/

/-- Beck Corollary 8.3.7 (CX-132). If `∑ aₙ (w - c)ⁿ` converges to `f w` on the annulus
`r < ‖w - c‖ < R`, then `aₙ` is the Laurent coefficient `laurentCoeff f c ρ n` for every
`ρ ∈ (r, R)`. -/
@[kb "beck2025" "Corollary 8.3.7, p. 141"]
theorem laurentCoeff_unique {f : ℂ → ℂ} {c : ℂ} {r R ρ : ℝ} {a : ℤ → ℂ}
    (hr : 0 ≤ r) (hρ : r < ρ) (hρ' : ρ < R)
    (ha : ∀ w, r < ‖w - c‖ → ‖w - c‖ < R → HasSum (fun n : ℤ => a n * (w - c) ^ n) (f w))
    (n : ℤ) : a n = laurentCoeff f c ρ n := by
  have hρ0 : 0 < ρ := hr.trans_lt hρ
  have hz0 : ∀ θ, circleMap c ρ θ - c ≠ 0 := fun θ =>
    sub_ne_zero.2 (circleMap_ne_center hρ0.ne')
  have hmem : ∀ θ, r < ‖circleMap c ρ θ - c‖ ∧ ‖circleMap c ρ θ - c‖ < R := by
    intro θ
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
    exact ⟨hρ, hρ'⟩
  have hsum : Summable (fun m : ℤ => ‖a m‖ * ρ ^ m) := by
    have h := (ha (c + (ρ : ℂ)) (by simpa [abs_of_pos hρ0] using hρ)
      (by simpa [abs_of_pos hρ0] using hρ')).summable
    have h2 := summable_norm_iff.2 h
    simpa [norm_mul, norm_zpow, abs_of_pos hρ0] using h2
  set F : ℤ → ℝ → ℂ := fun m θ => deriv (circleMap c ρ) θ •
      ((circleMap c ρ θ - c) ^ (-(n + 1)) * (a m * (circleMap c ρ θ - c) ^ m)) with hF
  have hcont : ∀ m, Continuous (F m) := by
    intro m
    have hc : Continuous fun θ => circleMap c ρ θ - c :=
      (continuous_circleMap c ρ).sub continuous_const
    simp only [hF, deriv_circleMap]
    exact ((continuous_circleMap 0 ρ).mul continuous_const).smul
      ((hc.zpow₀ _ fun θ => Or.inl (hz0 θ)).mul
        (continuous_const.mul (hc.zpow₀ _ fun θ => Or.inl (hz0 θ))))
  have key : HasSum (fun m => ∫ θ in (0:ℝ)..2 * π, F m θ)
      (∫ θ in (0:ℝ)..2 * π, deriv (circleMap c ρ) θ •
        ((circleMap c ρ θ - c) ^ (-(n + 1)) * f (circleMap c ρ θ))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ρ * ρ ^ (-(n + 1)) * (‖a m‖ * ρ ^ m)) (fun m => (hcont m).aestronglyMeasurable)
      (fun m => ?_) ?_ ?_ ?_
    · refine Eventually.of_forall fun θ _ => le_of_eq ?_
      simp only [hF, deriv_circleMap, norm_smul, norm_mul, norm_zpow, circleMap_sub_center,
        norm_circleMap_zero, abs_of_pos hρ0, Complex.norm_I]
      ring
    · exact Eventually.of_forall fun _ _ => hsum.mul_left _
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ => ?_
      exact ((ha _ (hmem θ).1 (hmem θ).2).mul_left _).const_smul _
  have hint : ∀ m : ℤ, (∫ θ in (0:ℝ)..2 * π, F m θ) =
      if m = n then a n * (2 * π * I) else 0 := by
    intro m
    have h1 : (∫ θ in (0:ℝ)..2 * π, F m θ) = ∮ z in C(c, ρ), a m * (z - c) ^ (m + -(n + 1)) := by
      unfold circleIntegral
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [hF]
      congr 1
      rw [zpow_add₀ (hz0 θ)]
      ring
    rw [h1, circleIntegral.integral_const_mul]
    split_ifs with h
    · subst h
      have e : m + -(m + 1) = -1 := by ring
      simp only [e, zpow_neg_one]
      rw [circleIntegral.integral_sub_center_inv c hρ0.ne']
    · rw [circleIntegral.integral_sub_zpow_of_ne (by omega) c c ρ, mul_zero]
  have hunique := (hasSum_ite_eq n (a n * (2 * π * I))).unique (by simpa only [hint] using key)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have e2 : (∮ z in C(c, ρ), (z - c) ^ (-(n + 1)) * f z) = a n * (2 * π * I) := by
    rw [hunique]; rfl
  unfold laurentCoeff
  rw [e2]
  field_simp

/-- Beck Corollary 8.3.7 (CX-132), as stated in the book: two Laurent series converging to the same
function on an annulus have the same coefficients. -/
@[kb "beck2025" "Corollary 8.3.7, p. 141"]
theorem laurent_series_unique {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} {a b : ℤ → ℂ}
    (hr : 0 ≤ r) (hrR : r < R)
    (ha : ∀ w, r < ‖w - c‖ → ‖w - c‖ < R → HasSum (fun n : ℤ => a n * (w - c) ^ n) (f w))
    (hb : ∀ w, r < ‖w - c‖ → ‖w - c‖ < R → HasSum (fun n : ℤ => b n * (w - c) ^ n) (f w))
    (n : ℤ) : a n = b n := by
  have h1 : r < (r + R) / 2 := by linarith
  have h2 : (r + R) / 2 < R := by linarith
  rw [laurentCoeff_unique hr h1 h2 ha n, laurentCoeff_unique hr h1 h2 hb n]

/-- Beck Corollary 8.3.8 (CX-132). If `f` is holomorphic on `G \ {c}` and the disc of radius `R`
around `c` lies in `G`, then `f` is the sum of its Laurent series about `c` on `0 < ‖w - c‖ < R`
(coefficients computed on any circle of radius `ρ ∈ (0, R)`). -/
@[kb "beck2025" "Corollary 8.3.8, p. 141"]
theorem hasSum_laurentCoeff_punctured {G : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ}
    (hGR : ball c R ⊆ G) (hf : DifferentiableOn ℂ f (G \ {c})) (hρ : 0 < ρ) (hρ' : ρ < R)
    {w : ℂ} (hw : 0 < ‖w - c‖) (hw' : ‖w - c‖ < R) :
    HasSum (fun n : ℤ => laurentCoeff f c ρ n * (w - c) ^ n) (f w) := by
  refine hasSum_laurentCoeff (r := 0) (hf.mono ?_) le_rfl hρ hρ' hw hw'
  intro z hz
  refine ⟨hGR hz.1, fun h => hz.2 ?_⟩
  rw [mem_singleton_iff] at h
  rw [h]; exact mem_closedBall_self le_rfl

/-! ## Classification of singularities -/

/-- A removable singularity extends over the whole disc of holomorphy. -/
theorem removable_extend {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R \ {c})) (h : HasRemovableSingularity f c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ EqOn f g (ball c R \ {c}) := by
  classical
  obtain ⟨r', hr', g₀, hg₀, hfg⟩ := h
  have hgc : ContinuousAt g₀ c := (hg₀.differentiableAt (ball_mem_nhds c hr')).continuousAt
  refine ⟨Function.update f c (g₀ c), ?_, fun z hz => (Function.update_of_ne hz.2 _ _).symm⟩
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds c hR)]
  refine ⟨hf.congr fun z hz => Function.update_of_ne hz.2 _ _, ?_⟩
  rw [continuousAt_update_same]
  refine (hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hr')] with z hz hzb
  exact (hfg ⟨hzb, hz⟩).symm

/-- If `f` agrees with a function `g` holomorphic on the disc, the negative Laurent coefficients
vanish and the coefficient of index `0` is `g c`. -/
theorem laurentCoeff_of_extension {f g : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hfg : EqOn f g (ball c R \ {c})) :
    (∀ n < 0, laurentCoeff f c ρ n = 0) ∧ laurentCoeff f c ρ 0 = g c := by
  have hsph : ∀ z ∈ sphere c ρ, z ∈ ball c R \ {c} := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    refine ⟨mem_ball_iff_norm.2 (by linarith), fun h => ?_⟩
    rw [mem_singleton_iff] at h
    rw [h, sub_self, norm_zero] at hz
    linarith
  have hcb : closedBall c ρ ⊆ ball c R := closedBall_subset_ball hρ'
  have hbs : ball c ρ ⊆ ball c R := ball_subset_closedBall.trans hcb
  constructor
  · intro n hn
    unfold laurentCoeff
    have e : (∮ z in C(c, ρ), (z - c) ^ (-(n + 1)) * f z) =
        ∮ z in C(c, ρ), (z - c) ^ (-(n + 1)) * g z :=
      circleIntegral.integral_congr hρ.le fun z hz => by simp only [hfg (hsph z hz)]
    have hd : ∀ z ∈ ball c R, DifferentiableAt ℂ (fun z => (z - c) ^ (-(n + 1)) * g z) z :=
      fun z hz => ((differentiableAt_id.sub_const c).zpow (Or.inr (by omega))).mul
        (hg.differentiableAt (isOpen_ball.mem_nhds hz))
    have h0 : (∮ z in C(c, ρ), (z - c) ^ (-(n + 1)) * g z) = 0 :=
      circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le countable_empty
        (fun z hz => (hd z (hcb hz)).continuousAt.continuousWithinAt)
        (fun z hz => hd z (hbs hz.1))
    rw [e, h0, mul_zero]
  · unfold laurentCoeff
    have e : (∮ z in C(c, ρ), (z - c) ^ (-((0:ℤ) + 1)) * f z) =
        ∮ z in C(c, ρ), (z - c)⁻¹ • g z :=
      circleIntegral.integral_congr hρ.le fun z hz => by
        simp only [hfg (hsph z hz), smul_eq_mul, zero_add, zpow_neg, zpow_one]
    have hd : ∀ z ∈ ball c R, DifferentiableAt ℂ g z :=
      fun z hz => hg.differentiableAt (isOpen_ball.mem_nhds hz)
    rw [e, circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      (mem_ball_self hρ) (fun z hz => (hd z (hcb hz)).continuousAt.continuousWithinAt)
      (fun z hz => hd z (hbs hz.1)), smul_eq_mul]
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact inv_mul_cancel_left₀ h2pi _

/-- Shifting the coefficients: multiplying by `(z - c)^m` shifts the index by `m`. -/
theorem laurentCoeff_mul_pow {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (n : ℤ) :
    laurentCoeff (fun z => (z - c) ^ m * f z) c ρ n = laurentCoeff f c ρ (n - m) := by
  unfold laurentCoeff
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  have hz0 : z - c ≠ 0 := by
    intro h
    rw [mem_sphere_iff_norm, h, norm_zero] at hz
    linarith
  simp only
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hz0]
  congr 2
  ring

/-- Beck Proposition 9.1.10(a) (CX-139). A singularity is removable iff all negative-index Laurent
coefficients vanish. -/
@[kb "beck2025" "Proposition 9.1.10, p. 152"]
theorem removable_iff_laurentCoeff_neg_eq_zero {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) :
    HasRemovableSingularity f c ↔ ∀ n < 0, laurentCoeff f c ρ n = 0 := by
  constructor
  · intro h
    obtain ⟨g, hg, hfg⟩ := removable_extend hR hf h
    exact (laurentCoeff_of_extension hρ hρ' hg hfg).1
  · intro h0
    have hf' : DifferentiableOn ℂ f (ball c R \ closedBall c 0) := by
      rw [closedBall_zero]; exact hf
    have hS : ∀ w, 0 < ‖w - c‖ → ‖w - c‖ < R →
        HasSum (fun n : ℤ => laurentCoeff f c ρ n * (w - c) ^ n) (f w) :=
      fun w h1 h2 => hasSum_laurentCoeff hf' le_rfl hρ hρ' h1 h2
    have hsum : Summable (fun n : ℤ => ‖laurentCoeff f c ρ n‖ * ρ ^ n) := by
      have h := (hS (c + (ρ : ℂ)) (by simpa [abs_of_pos hρ] using hρ)
        (by simpa [abs_of_pos hρ] using hρ')).summable
      have h2 := summable_norm_iff.2 h
      simpa [norm_mul, norm_zpow, abs_of_pos hρ] using h2
    set S := ∑' n : ℤ, ‖laurentCoeff f c ρ n‖ * ρ ^ n with hSdef
    have hbound : ∀ w, 0 < ‖w - c‖ → ‖w - c‖ ≤ ρ → ‖f w‖ ≤ S := by
      intro w h1 h2
      have hw := hS w h1 (lt_of_le_of_lt h2 hρ')
      have hn : Summable (fun n : ℤ => ‖laurentCoeff f c ρ n * (w - c) ^ n‖) :=
        summable_norm_iff.2 hw.summable
      rw [← hw.tsum_eq]
      refine (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum (fun n => ?_) hn hsum)
      rw [norm_mul, norm_zpow]
      by_cases hn0 : n < 0
      · rw [h0 n hn0]; simp
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hn0)
        simp only [zpow_natCast]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 k) (norm_nonneg _)
    refine (removable_iff_tendsto_mul_sub hR hf).2 ?_
    refine squeeze_zero_norm' (a := fun z => ‖z - c‖ * S) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hρ)] with z hz hzb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound z (norm_pos_iff.2 (sub_ne_zero.2 hz))
        (le_of_lt (mem_ball_iff_norm.1 hzb))) (norm_nonneg _)
    · have : Tendsto (fun z : ℂ => ‖z - c‖ * S) (𝓝 c) (𝓝 (‖c - c‖ * S)) :=
        ((continuous_norm.comp (continuous_id.sub continuous_const)).mul
          continuous_const).tendsto c
      simpa using this.mono_left nhdsWithin_le_nhds

/-- Multiplying by `(z - c)^m` gives a removable singularity iff the coefficients below `-m` vanish. -/
theorem removable_mul_pow_iff {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) (m : ℕ) :
    HasRemovableSingularity (fun z => (z - c) ^ m * f z) c ↔
      ∀ n < -(m : ℤ), laurentCoeff f c ρ n = 0 := by
  have hd : DifferentiableOn ℂ (fun z => (z - c) ^ m * f z) (ball c R \ {c}) :=
    ((differentiableOn_id.sub_const c).pow m).mul hf
  rw [removable_iff_laurentCoeff_neg_eq_zero hR hρ hρ' hd]
  constructor
  · intro h n hn
    have := h (n + m) (by omega)
    rwa [laurentCoeff_mul_pow hρ, add_sub_cancel_right] at this
  · intro h n hn
    rw [laurentCoeff_mul_pow hρ]
    exact h _ (by omega)

/-- Normal form of a singularity whose coefficients below `-m` vanish: `f = g / (z - c)^m` on the
punctured disc with `g` holomorphic on the disc and `g c = c_{-m}`. -/
theorem exists_pow_form {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) (m : ℕ)
    (hm : ∀ n < -(m : ℤ), laurentCoeff f c ρ n = 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c = laurentCoeff f c ρ (-(m : ℤ)) ∧
      ∀ z ∈ ball c R \ {c}, f z = g z / (z - c) ^ m := by
  have hd : DifferentiableOn ℂ (fun z => (z - c) ^ m * f z) (ball c R \ {c}) :=
    ((differentiableOn_id.sub_const c).pow m).mul hf
  obtain ⟨g, hg, hfg⟩ := removable_extend hR hd
    ((removable_mul_pow_iff hR hρ hρ' hf m).2 hm)
  refine ⟨g, hg, ?_, fun z hz => ?_⟩
  · have := (laurentCoeff_of_extension hρ hρ' hg hfg).2
    rw [laurentCoeff_mul_pow hρ, zero_sub] at this
    exact this.symm
  · have hz0 : (z - c) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz.2)
    rw [eq_div_iff hz0, mul_comm]
    exact hfg hz

/-- Beck Proposition 9.1.10(b) (CX-139). A singularity is a pole iff only finitely many
negative-index coefficients are nonzero, but not none: there is `m > 0` with `c_{-m} ≠ 0` and
`c_n = 0` for all `n < -m`. -/
@[kb "beck2025" "Proposition 9.1.10, p. 152"]
theorem hasPole_iff_laurentCoeff {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) :
    HasPole f c ↔ ∃ m : ℕ, 0 < m ∧ laurentCoeff f c ρ (-(m : ℤ)) ≠ 0 ∧
      ∀ n < -(m : ℤ), laurentCoeff f c ρ n = 0 := by
  classical
  constructor
  · intro hp
    obtain ⟨hnr, n, -, ht⟩ := (hasPole_iff hR hf).1 hp
    have hP : ∃ m : ℕ, ∀ k < -(m : ℤ), laurentCoeff f c ρ k = 0 := by
      refine ⟨n, (removable_mul_pow_iff hR hρ hρ' hf n).1 ?_⟩
      have hd : DifferentiableOn ℂ (fun z => (z - c) ^ n * f z) (ball c R \ {c}) :=
        ((differentiableOn_id.sub_const c).pow n).mul hf
      refine (removable_iff_tendsto_mul_sub hR hd).2 (ht.congr fun z => ?_)
      ring
    set m₀ := Nat.find hP with hm₀
    have hm₀P : ∀ k < -(m₀ : ℤ), laurentCoeff f c ρ k = 0 := Nat.find_spec hP
    obtain ⟨m', hm'⟩ : ∃ m', m₀ = m' + 1 := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | h0
      · exfalso
        apply hnr
        rw [removable_iff_laurentCoeff_neg_eq_zero hR hρ hρ' hf]
        intro k hk
        exact hm₀P k (by rw [h0]; simpa using hk)
      · exact ⟨m₀ - 1, by omega⟩
    refine ⟨m₀, by omega, fun hne => ?_, hm₀P⟩
    have hlt : m' < m₀ := by omega
    refine Nat.find_min hP hlt fun k hk => ?_
    rcases lt_or_eq_of_le (show k ≤ -(m₀ : ℤ) by omega) with h | h
    · exact hm₀P k h
    · rw [h]; exact hne
  · rintro ⟨m, hm, hne, hP⟩
    obtain ⟨g, hg, hgc, hfg⟩ := exists_pow_form hR hρ hρ' hf m hP
    refine (hasPole_iff hR hf).2 ⟨?_, m, hm, ?_⟩
    · intro hrem
      exact hne ((removable_iff_laurentCoeff_neg_eq_zero hR hρ hρ' hf).1 hrem _ (by omega))
    · have hgc' : ContinuousAt g c :=
        (hg.differentiableAt (ball_mem_nhds c hR)).continuousAt
      have hlim : Tendsto (fun z => (z - c) * g z) (𝓝 c) (𝓝 0) := by
        have : Tendsto (fun z => (z - c) * g z) (𝓝 c) (𝓝 ((c - c) * g c)) :=
          (continuousAt_id.sub continuousAt_const).mul hgc' |>.tendsto
        simpa using this
      refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hR)] with z hz hzb
      have hz0 : z - c ≠ 0 := sub_ne_zero.2 hz
      rw [hfg z ⟨hzb, hz⟩]
      field_simp
      ring

/-- Beck Proposition 9.1.10(b) (CX-139), the order of the pole: if `m` is the index with
`c_{-m} ≠ 0` and `c_n = 0` for `n < -m`, then `f = g / (z - c)^m` on the punctured disc with `g`
holomorphic on the disc and `g c = c_{-m} ≠ 0`. -/
@[kb "beck2025" "Proposition 9.1.10, p. 152"]
theorem pole_order_form {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) {m : ℕ}
    (hne : laurentCoeff f c ρ (-(m : ℤ)) ≠ 0) (hP : ∀ n < -(m : ℤ), laurentCoeff f c ρ n = 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c ≠ 0 ∧
      ∀ z ∈ ball c R \ {c}, f z = g z / (z - c) ^ m := by
  obtain ⟨g, hg, hgc, hfg⟩ := exists_pow_form hR hρ hρ' hf m hP
  exact ⟨g, hg, by rw [hgc]; exact hne, hfg⟩

/-- Beck Proposition 9.1.10(c) (CX-139). A singularity is essential iff infinitely many
negative-index coefficients are nonzero. -/
@[kb "beck2025" "Proposition 9.1.10, p. 152"]
theorem hasEssentialSingularity_iff_laurentCoeff {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ) (hρ' : ρ < R) (hf : DifferentiableOn ℂ f (ball c R \ {c})) :
    HasEssentialSingularity f c ↔
      {n : ℤ | n < 0 ∧ laurentCoeff f c ρ n ≠ 0}.Infinite := by
  have hA := removable_iff_laurentCoeff_neg_eq_zero hR hρ hρ' hf
  have hB := hasPole_iff_laurentCoeff hR hρ hρ' hf
  constructor
  · rintro ⟨hnr, hnp⟩
    by_contra hinf
    rw [Set.not_infinite] at hinf
    have hne : {n : ℤ | n < 0 ∧ laurentCoeff f c ρ n ≠ 0}.Nonempty := by
      by_contra h0
      apply hnr
      rw [hA]
      intro n hn
      by_contra hc
      exact h0 ⟨n, hn, hc⟩
    obtain ⟨n₀, ⟨hn₀, hc₀⟩, hmin⟩ := Set.exists_min_image _ id hinf hne
    apply hnp
    rw [hB]
    refine ⟨(-n₀).toNat, by omega, ?_, ?_⟩
    · have : -(((-n₀).toNat : ℕ) : ℤ) = n₀ := by omega
      rw [this]; exact hc₀
    · intro n hn
      by_contra hc
      have := hmin n ⟨by omega, hc⟩
      simp only [id] at this
      omega
  · intro hinf
    refine ⟨fun hrem => ?_, fun hp => ?_⟩
    · apply hinf
      have : {n : ℤ | n < 0 ∧ laurentCoeff f c ρ n ≠ 0} = ∅ := by
        ext n
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
        exact fun hn => (hA.1 hrem) n hn
      rw [this]; exact Set.finite_empty
    · obtain ⟨m, -, -, hP⟩ := hB.1 hp
      apply hinf
      refine (Set.finite_Ico (-(m : ℤ)) 0).subset fun n ⟨hn, hc⟩ => ⟨?_, hn⟩
      by_contra h
      exact hc (hP n (by omega))

end UndergradKB.ComplexAnalysis
