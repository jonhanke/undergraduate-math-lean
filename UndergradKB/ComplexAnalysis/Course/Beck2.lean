import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 2 (Differentiation): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).
Functions on a domain `G` are modelled as functions `ℂ → ℂ` whose values off `G` are irrelevant;
the limit `z → z₀` inside `G` is the filter `𝓝[G \ {z₀}] z₀`. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck2
open Complex Filter Topology
open scoped ComplexConjugate

/-- Beck Definition 2.1.2 (CX-021). The epsilon-delta description of the limit of `f` at `z₀`,
along points of `G`, is equivalent to the filter limit. -/
@[kb "beck2025" "Definition 2.1.2, p. 32"]
theorem limit_iff_epsilon_delta (f : ℂ → ℂ) (G : Set ℂ) (z₀ w₀ : ℂ) :
    Tendsto f (𝓝[G \ {z₀}] z₀) (𝓝 w₀) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ z ∈ G, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ → ‖f z - w₀‖ < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine forall_congr' fun ε => imp_congr_right fun hε => exists_congr fun δ =>
    and_congr_right fun hδ => ?_
  constructor
  · intro h z hz h0 h1
    have := @h z ⟨hz, fun hz' => by rw [Set.mem_singleton_iff] at hz'; simp [hz'] at h0⟩
      (by simpa [dist_eq_norm] using h1)
    simpa [dist_eq_norm] using this
  · intro h z hz h1
    have h0 : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.2)
    simpa [dist_eq_norm] using h z hz.1 h0 (by simpa [dist_eq_norm] using h1)

/-- Beck Example 2.1.3 (CX-021). The limit of `z^2` as `z → i` is `-1`. -/
@[kb "beck2025" "Example 2.1.3, p. 33"]
theorem limit_sq_at_I : Tendsto (fun z : ℂ => z ^ 2) (𝓝[≠] I) (𝓝 (-1)) := by
  have : Tendsto (fun z : ℂ => z ^ 2) (𝓝 I) (𝓝 (I ^ 2)) := (continuous_pow 2).tendsto I
  rw [Complex.I_sq] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Beck Proposition 2.1.4 (CX-022). A limit survives restriction to a subset `G'` of the domain,
provided `z₀` is still an accumulation point of `G'`. -/
@[kb "beck2025" "Proposition 2.1.4, p. 33"]
theorem limit_restrict (f : ℂ → ℂ) (G G' : Set ℂ) (z₀ w₀ : ℂ) (hG : G' ⊆ G)
    (_hacc : (𝓝[G' \ {z₀}] z₀).NeBot) (h : Tendsto f (𝓝[G \ {z₀}] z₀) (𝓝 w₀)) :
    Tendsto f (𝓝[G' \ {z₀}] z₀) (𝓝 w₀) :=
  h.mono_left (nhdsWithin_mono _ (Set.sdiff_subset_sdiff_left hG))

/-- Beck Example 2.1.5 (CX-022). The function `z / conj z` has no limit at `0`. -/
@[kb "beck2025" "Example 2.1.5, p. 33"]
theorem no_limit_z_div_conj : ¬ ∃ w : ℂ, Tendsto (fun z : ℂ => z / conj z) (𝓝[≠] 0) (𝓝 w) := by
  rintro ⟨w, hw⟩
  have key : ∀ u : ℂ, u ≠ 0 → (∀ r : ℝ, r ≠ 0 → (r : ℂ) * u / conj ((r : ℂ) * u) = u / conj u) →
      Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) : ℝ) * u) atTop (𝓝[≠] 0) := by
    intro u hu _
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa using h2.mul_const u
    · simp [hu, Nat.cast_add_one_ne_zero]
  have e1 := hw.comp (key 1 one_ne_zero (by intro r hr; simp [hr]))
  have e2 := hw.comp (key I I_ne_zero (by
    intro r hr; simp [hr]))
  have a1 : (fun z : ℂ => z / conj z) ∘ (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) : ℝ) * (1 : ℂ))
      = fun _ => (1 : ℂ) := by
    funext n
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast this
    simp
    field_simp
  have a2 : (fun z : ℂ => z / conj z) ∘ (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) : ℝ) * I)
      = fun _ => (-1 : ℂ) := by
    funext n
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast this
    simp [Complex.conj_I]
    field_simp
  rw [a1] at e1
  rw [a2] at e2
  have h1 := tendsto_nhds_unique e1 tendsto_const_nhds
  have h2 := tendsto_nhds_unique e2 tendsto_const_nhds
  have h3 := h1.symm.trans h2
  norm_num at h3

/-- Beck Proposition 2.1.6 (CX-023). Limit laws: linear combinations, products and quotients. -/
@[kb "beck2025" "Proposition 2.1.6, p. 34"]
theorem limit_laws (f g : ℂ → ℂ) (G : Set ℂ) (z₀ a b c : ℂ)
    (hf : Tendsto f (𝓝[G \ {z₀}] z₀) (𝓝 a)) (hg : Tendsto g (𝓝[G \ {z₀}] z₀) (𝓝 b)) :
    Tendsto (fun z => f z + c * g z) (𝓝[G \ {z₀}] z₀) (𝓝 (a + c * b)) ∧
    Tendsto (fun z => f z * g z) (𝓝[G \ {z₀}] z₀) (𝓝 (a * b)) ∧
    (b ≠ 0 → Tendsto (fun z => f z / g z) (𝓝[G \ {z₀}] z₀) (𝓝 (a / b))) :=
  ⟨hf.add (hg.const_mul c), hf.mul hg, fun hb => hf.div hg hb⟩

/-- Beck Definition 2.1.8 (CX-024). Continuity of `f` at `z₀ ∈ G` (within `G`) in the
epsilon-delta form. -/
@[kb "beck2025" "Definition 2.1.8, p. 34"]
theorem continuousWithinAt_iff_epsilon_delta (f : ℂ → ℂ) (G : Set ℂ) (z₀ : ℂ) :
    ContinuousWithinAt f G z₀ ↔
      ∀ ε > 0, ∃ δ > 0, ∀ z ∈ G, ‖z - z₀‖ < δ → ‖f z - f z₀‖ < ε := by
  simp only [Metric.continuousWithinAt_iff, dist_eq_norm]

open scoped Classical in
/-- The function `z / conj z`, set to `1` at `0`, from Beck's Example 2.1.9. -/
noncomputable def gAux (z : ℂ) : ℂ := if z = 0 then 1 else z / conj z

lemma gAux_of_ne {z : ℂ} (hz : z ≠ 0) : gAux z = z / conj z := by simp [gAux, hz]

/-- Beck Example 2.1.9 (CX-024). `z^2` is continuous on `ℂ`; the function `z / conj z`
(set to `1` at `0`) is continuous except at `0`. -/
@[kb "beck2025" "Example 2.1.9, p. 34"]
theorem continuity_examples :
    Continuous (fun z : ℂ => z ^ 2) ∧
    (∀ z : ℂ, z ≠ 0 → ContinuousAt gAux z) ∧ ¬ ContinuousAt gAux 0 := by
  refine ⟨continuous_pow 2, ?_, ?_⟩
  · intro z hz
    have h1 : ContinuousAt (fun z : ℂ => z / conj z) z :=
      ContinuousAt.div (f := fun z : ℂ => z) (g := fun z : ℂ => conj z) continuousAt_id
        Complex.continuous_conj.continuousAt (by simpa using hz)
    refine h1.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact (gAux_of_ne hy).symm
  · intro hc
    apply no_limit_z_div_conj
    refine ⟨gAux 0, ?_⟩
    have h2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact gAux_of_ne hy

/-- Beck Proposition 2.1.11 (CX-025). If `g → w₀` and `f` is continuous at `w₀`, then
`f (g z) → f w₀`. -/
@[kb "beck2025" "Proposition 2.1.11, p. 35"]
theorem limit_comp (f g : ℂ → ℂ) (G : Set ℂ) (z₀ w₀ : ℂ)
    (hg : Tendsto g (𝓝[G \ {z₀}] z₀) (𝓝 w₀)) (hf : ContinuousAt f w₀) :
    Tendsto (fun z => f (g z)) (𝓝[G \ {z₀}] z₀) (𝓝 (f w₀)) :=
  hf.tendsto.comp hg

/-- Beck Proposition 2.2.5 (CX-028). Sum, product, quotient, power and chain rules, and
continuity at points of differentiability. -/
@[kb "beck2025" "Proposition 2.2.5, p. 37"]
theorem derivative_rules (f g h : ℂ → ℂ) (z f' g' h' c : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) (hh : HasDerivAt h h' (g z)) :
    HasDerivAt (fun w => f w + c * g w) (f' + c * g') z ∧
    HasDerivAt (fun w => f w * g w) (f' * g z + f z * g') z ∧
    (g z ≠ 0 → HasDerivAt (fun w => f w / g w) ((f' * g z - f z * g') / g z ^ 2) z) ∧
    (∀ n : ℤ, n ≠ 0 → (z ≠ 0 ∨ 0 ≤ n) →
      HasDerivAt (fun w : ℂ => w ^ n) ((n : ℂ) * z ^ (n - 1)) z) ∧
    ContinuousAt f z ∧
    HasDerivAt (fun w => h (g w)) (h' * g') z := by
  refine ⟨hf.add (hg.const_mul c), hf.mul hg, fun h0 => hf.div hg h0,
    fun n _ hn => hasDerivAt_zpow n z hn, hf.continuousAt, hh.comp z hg⟩

/-- Beck Proposition 2.2.8 (CX-031). Derivative of an inverse function on open sets `G`, `H`. -/
@[kb "beck2025" "Proposition 2.2.8, p. 38"]
theorem derivative_of_inverse (f g : ℂ → ℂ) (G H : Set ℂ) (hH : IsOpen H)
    (hfg : ∀ w ∈ H, f (g w) = w) (w₀ : ℂ) (hw₀ : w₀ ∈ H) (f' : ℂ)
    (hf : HasDerivAt f f' (g w₀)) (hf' : f' ≠ 0) (hg : ContinuousAt g w₀) :
    HasDerivAt g f'⁻¹ w₀ := by
  have _ := G
  refine HasDerivAt.of_local_left_inverse hg hf hf' ?_
  filter_upwards [hH.mem_nhds hw₀] with w hw using hfg w hw

/-- Beck Proposition 2.4.1 (CX-033). A real function with derivative zero on an interval is
constant there. -/
@[kb "beck2025" "Proposition 2.4.1, p. 42"]
theorem const_of_deriv_zero_interval (I : Set ℝ) (hI : I.OrdConnected) (f : ℝ → ℝ)
    (hf : ∀ x ∈ I, HasDerivAt f 0 x) : ∃ c : ℝ, ∀ x ∈ I, f x = c := by
  have key : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → f y = f x := by
    intro x hx y hy hxy
    have hcont : ContinuousOn f (Set.Icc x y) := fun t ht =>
      (hf t (hI.out hx hy ht)).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun t ht => (hf t (hI.out hx hy (Set.Ico_subset_Icc_self ht))).hasDerivWithinAt) y
      ⟨hxy, le_rfl⟩
  by_cases hne : I.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨f x₀, fun x hx => ?_⟩
    rcases le_total x₀ x with h | h
    · exact key x₀ hx₀ x hx h
    · exact (key x hx x₀ hx₀ h).symm
  · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- Beck Theorem 2.4.2 (CX-034). A complex function with zero derivative on a region
(open and connected set) is constant. -/
@[kb "beck2025" "Theorem 2.4.2, p. 43"]
theorem const_of_deriv_zero_region (G : Set ℂ) (hG : IsOpen G) (hC : IsConnected G)
    (f : ℂ → ℂ) (hf : ∀ z ∈ G, HasDerivAt f 0 z) : ∃ c : ℂ, ∀ z ∈ G, f z = c :=
  hG.exists_is_const_of_deriv_eq_zero hC.isPreconnected
    (fun z hz => (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hf z hz).deriv)

end UndergradKB.ComplexAnalysis.Course.Beck2
