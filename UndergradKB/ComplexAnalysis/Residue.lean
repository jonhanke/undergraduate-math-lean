import UndergradKB.ComplexAnalysis.Laurent

/-!
# Residues

Beck et al., *A First Course in Complex Analysis*, Section 9.2 (checklist rows CX-140, CX-142). Mathlib has no
residues. Here:

* `residue f c`: the limit, as `ρ → 0⁺`, of `(2πi)⁻¹ ∮_{|z-c|=ρ} f(z) dz`. For `f` holomorphic on a punctured disc
  about `c` the circle integral does not depend on `ρ` (`residue_eq_circleIntegral`) and the residue is the
  coefficient `c₋₁` of the Laurent series (`residue_eq_laurentCoeff`), which is the book's Definition 9.2.1.
  The residue depends only on `f` near `c` (`residue_congr`).
* Computing residues: zero at a removable singularity, the derivative formula at a pole of order `n`
  (Proposition 9.2.4), and `f(z₀)/g'(z₀)` for `f/g` at a simple zero of `g` (Proposition 9.2.7).
-/

open Complex Metric Set Filter Topology Real

namespace UndergradKB.ComplexAnalysis

/-- Beck Definition 9.2.1 (CX-140): the residue of `f` at `c`, the limit as `ρ → 0⁺` of
`(2πi)⁻¹ ∮_{|z-c|=ρ} f(z) dz`. At an isolated singularity it is the Laurent coefficient `c₋₁`
(`residue_eq_laurentCoeff`). -/
@[kb "beck2025" "Definition 9.2.1, p. 154"]
noncomputable def residue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ρ => (2 * π * I)⁻¹ * ∮ z in C(c, ρ), f z

theorem ball_sdiff_closedBall_zero (c : ℂ) (R : ℝ) :
    ball c R \ closedBall c 0 = ball c R \ {c} := by
  rw [closedBall_zero]

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, I_ne_zero]

/-- For `f` holomorphic on a punctured disc `0 < |z - c| < R`, the residue is `(2πi)⁻¹ ∮ f` over any circle
`|z - c| = ρ`, `0 < ρ < R`. -/
theorem residue_eq_circleIntegral {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ {c})) (hρ : 0 < ρ) (hρR : ρ < R) :
    residue f c = (2 * π * I)⁻¹ * ∮ z in C(c, ρ), f z := by
  rw [← ball_sdiff_closedBall_zero] at hf
  have hconst : ∀ ρ' ∈ Ioo 0 R,
      (2 * π * I)⁻¹ * (∮ z in C(c, ρ'), f z) = (2 * π * I)⁻¹ * ∮ z in C(c, ρ), f z := by
    rintro ρ' ⟨h0, h1⟩
    congr 1
    rcases le_total ρ' ρ with h | h
    · exact (circleIntegral_eq_of_differentiableOn_annulus hf le_rfl h0 h hρR).symm
    · exact circleIntegral_eq_of_differentiableOn_annulus hf le_rfl hρ h h1
  have hmem : Ioo (0 : ℝ) R ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (hρ.trans hρR)
  have ht : Tendsto (fun ρ' => (2 * π * I)⁻¹ * ∮ z in C(c, ρ'), f z) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * π * I)⁻¹ * ∮ z in C(c, ρ), f z)) :=
    tendsto_const_nhds.congr' (eventually_of_mem hmem fun ρ' h => (hconst ρ' h).symm)
  exact ht.limUnder_eq

/-- Beck Definition 9.2.1 (CX-140): at an isolated singularity the residue is the coefficient `c₋₁` of the
Laurent series (computed on any circle of the punctured disc). -/
@[kb "beck2025" "Definition 9.2.1, p. 154"]
theorem residue_eq_laurentCoeff {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ {c})) (hρ : 0 < ρ) (hρR : ρ < R) :
    residue f c = laurentCoeff f c ρ (-1) := by
  rw [residue_eq_circleIntegral hf hρ hρR, laurentCoeff]
  simp

/-- The residue depends only on the values of `f` on a punctured neighbourhood of `c`. -/
theorem residue_congr {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝[≠] c] g) : residue f c = residue g c := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 h
  have hev : (fun ρ => (2 * π * I)⁻¹ * ∮ z in C(c, ρ), f z) =ᶠ[𝓝[>] (0 : ℝ)]
      fun ρ => (2 * π * I)⁻¹ * ∮ z in C(c, ρ), g z := by
    refine eventually_of_mem (Ioo_mem_nhdsGT hε) fun ρ hρ => ?_
    have e : (∮ z in C(c, ρ), f z) = ∮ z in C(c, ρ), g z := by
      refine circleIntegral.integral_congr hρ.1.le fun z hz => ?_
      have hz' : z ∈ ball c ε ∩ {c}ᶜ := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, mem_sphere.1 hz]; exact hρ.2
        · intro hzc
          rw [mem_singleton_iff] at hzc
          rw [hzc, mem_sphere, dist_self] at hz; linarith [hρ.1]
      exact hεs hz'
    simp only [e]
  unfold residue limUnder
  rw [Filter.map_congr hev]

/-- Beck Proposition 9.2.4 (a) (CX-142): the residue at a removable singularity is zero. -/
@[kb "beck2025" "Proposition 9.2.4, p. 155"]
theorem residue_eq_zero_of_removable {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hfg : EqOn f g (ball c R \ {c})) :
    residue f c = 0 := by
  have hev : f =ᶠ[𝓝[≠] c] g :=
    eventually_of_mem (inter_mem_nhdsWithin _ (ball_mem_nhds c hR)) fun z hz => hfg ⟨hz.2, hz.1⟩
  rw [residue_congr hev, residue_eq_circleIntegral (hg.mono sdiff_subset) (half_pos hR)
    (half_lt_self hR)]
  have hd : DiffContOnCl ℂ g (ball c (R / 2)) :=
    (hg.mono (closedBall_subset_ball (half_lt_self hR))).diffContOnCl_ball le_rfl
  rw [hd.circleIntegral_eq_zero (half_pos hR).le, mul_zero]

/-- Beck Proposition 9.2.4 (b) (CX-142): at a pole of order at most `m + 1`, i.e. when
`f(z) = g(z) / (z - c)^(m+1)` near `c` with `g` holomorphic at `c`, the residue is
`g^(m)(c) / m!`, the limit of the `m`-th derivative of `(z - c)^(m+1) f(z)` divided by `m!`. -/
@[kb "beck2025" "Proposition 9.2.4, p. 155"]
theorem residue_of_eq_div_pow {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (m : ℕ)
    (hfg : ∀ z ∈ ball c R \ {c}, f z = g z / (z - c) ^ (m + 1)) :
    residue f c = iteratedDeriv m g c / m.factorial := by
  have hev : f =ᶠ[𝓝[≠] c] fun z => g z / (z - c) ^ (m + 1) :=
    eventually_of_mem (inter_mem_nhdsWithin _ (ball_mem_nhds c hR)) fun z hz => hfg z ⟨hz.2, hz.1⟩
  have hF : DifferentiableOn ℂ (fun z => g z / (z - c) ^ (m + 1)) (ball c R \ {c}) := by
    refine (hg.mono sdiff_subset).div (by fun_prop) fun z hz => pow_ne_zero _ (sub_ne_zero.2 ?_)
    exact hz.2
  rw [residue_congr hev, residue_eq_circleIntegral hF (half_pos hR) (half_lt_self hR)]
  have hd : DifferentiableOn ℂ g (closedBall c (R / 2)) :=
    hg.mono (closedBall_subset_ball (half_lt_self hR))
  have key := hd.circleIntegral_one_div_sub_center_pow_smul (half_pos hR) m
  simp only [smul_eq_mul, one_div] at key
  have e : (∮ z in C(c, R / 2), g z / (z - c) ^ (m + 1)) =
      ∮ z in C(c, R / 2), ((z - c) ^ (m + 1))⁻¹ * g z := by
    congr 1; ext z; rw [div_eq_inv_mul]
  rw [e, key]
  have : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp [two_pi_I_ne_zero]

/-- Beck Proposition 9.2.7 (CX-142): if `f` and `g` are holomorphic at `c` and `c` is a simple zero of `g`
(`g c = 0`, `g' c ≠ 0`), then the residue of `f / g` at `c` is `f(c) / g'(c)`. -/
@[kb "beck2025" "Proposition 9.2.7, p. 156"]
theorem residue_div_of_simple_zero {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hg : DifferentiableOn ℂ g (ball c R))
    (hgc : g c = 0) (hg' : deriv g c ≠ 0) :
    residue (fun z => f z / g z) c = f c / deriv g c := by
  set h := dslope g c
  have hh : DifferentiableOn ℂ h (ball c R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds c hR)).2 hg
  have hhc : h c = deriv g c := dslope_same g c
  have hcont : ContinuousAt h c := (hh.differentiableAt (ball_mem_nhds c hR)).continuousAt
  obtain ⟨ε, hε, hεh⟩ : ∃ ε > 0, ∀ z ∈ ball c ε, h z ≠ 0 := by
    have := hcont.eventually_ne (hhc ▸ hg')
    obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ε, hε, fun z hz => hs hz⟩
  set δ := min ε R
  have hδ : 0 < δ := lt_min hε hR
  have hδε : ball c δ ⊆ ball c ε := ball_subset_ball (min_le_left _ _)
  have hδR : ball c δ ⊆ ball c R := ball_subset_ball (min_le_right _ _)
  have hk : DifferentiableOn ℂ (fun z => f z / h z) (ball c δ) :=
    (hf.mono hδR).div (hh.mono hδR) fun z hz => hεh z (hδε hz)
  have hgz : ∀ z, g z = (z - c) * h z := by
    intro z
    have := sub_smul_dslope g c z
    rw [hgc, sub_zero, smul_eq_mul] at this
    exact this.symm
  have := residue_of_eq_div_pow (f := fun z => f z / g z) hδ hk 0 fun z _ => by
    rw [hgz z, zero_add, pow_one, div_div, mul_comm]
  rw [this, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, hhc]

end UndergradKB.ComplexAnalysis
