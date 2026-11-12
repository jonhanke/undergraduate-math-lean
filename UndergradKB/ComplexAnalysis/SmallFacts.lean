import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Connected.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Defs
import UndergradKB.Common.Attr

/-! # Small facts from Chapters 1-5 (rows CX-019, CX-029, CX-039, CX-051, CX-061, CX-078)

Conformality of differentiable maps along smooth paths, limits involving `∞` (poles of `1/z²` and of
Mobius maps, behaviour at infinity), branches of the logarithm and their uniqueness up to `2πik`,
some explicit antiderivatives, the size of a polynomial for large `|z|`, and connectedness of open
connected sets by polygonal paths with horizontal and vertical segments. -/

open Complex Metric Set Filter Topology Real

namespace UndergradKB.ComplexAnalysis

/-! ## Conformality (CX-029) -/

/-- Beck Proposition 2.2.6 (CX-029). Let `f` be complex differentiable at `z₀` with `f'(z₀) = d ≠ 0`
and let `γ₁, γ₂ : ℝ → ℂ` be paths through `z₀` at time `0` with nonzero velocities `v₁, v₂`.  Then
`f ∘ γᵢ` has velocity `d vᵢ` at `0` (nonzero), and the quotient of the tangent vectors, whose
argument is the angle between the paths, is unchanged. -/
@[kb "beck2025" "Proposition 2.2.6, p. 38"]
theorem angle_preserved {f : ℂ → ℂ} {z₀ d : ℂ} (hf : HasDerivAt f d z₀) (hd : d ≠ 0)
    {γ₁ γ₂ : ℝ → ℂ} {v₁ v₂ : ℂ} (h₁ : HasDerivAt γ₁ v₁ 0) (h₂ : HasDerivAt γ₂ v₂ 0)
    (hγ₁ : γ₁ 0 = z₀) (hγ₂ : γ₂ 0 = z₀) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    HasDerivAt (f ∘ γ₁) (d * v₁) 0 ∧ HasDerivAt (f ∘ γ₂) (d * v₂) 0 ∧ d * v₁ ≠ 0 ∧
      d * v₂ ≠ 0 ∧ (d * v₂) / (d * v₁) = v₂ / v₁ ∧ arg ((d * v₂) / (d * v₁)) = arg (v₂ / v₁) := by
  have e₁ : HasDerivAt f d (γ₁ 0) := hγ₁ ▸ hf
  have e₂ : HasDerivAt f d (γ₂ 0) := hγ₂ ▸ hf
  have q : (d * v₂) / (d * v₁) = v₂ / v₁ := mul_div_mul_left _ _ hd
  refine ⟨?_, ?_, mul_ne_zero hd hv₁, mul_ne_zero hd hv₂, q, by rw [q]⟩
  · simpa [mul_comm] using e₁.scomp (0 : ℝ) h₁
  · simpa [mul_comm] using e₂.scomp (0 : ℝ) h₂

/-! ## Limits involving infinity (CX-039) -/

private theorem tendsto_inv_norm_sub_atTop' (z₀ : ℂ) :
    Tendsto (fun z : ℂ => ‖z - z₀‖⁻¹) (𝓝[≠] z₀) atTop := by
  have h0 : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 ‖z₀ - z₀‖) :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).tendsto z₀
    simpa using this
  have h : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝[≠] z₀) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => norm_pos_iff.2 (sub_ne_zero.2 hz)⟩
  exact tendsto_inv_nhdsGT_zero.comp h

/-- Beck Example 3.2.2 (CX-039). `1/z² → ∞` as `z → 0`. -/
@[kb "beck2025" "Example 3.2.2, p. 51"]
theorem tendsto_one_div_sq_atTop :
    Tendsto (fun z : ℂ => ‖1 / z ^ 2‖) (𝓝[≠] 0) atTop := by
  have h0 : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto 0)
    simpa using this
  have h : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (𝓝[≠] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => by
        have : 0 < ‖z‖ := norm_pos_iff.2 hz
        exact pow_pos this 2⟩
  refine (tendsto_inv_nhdsGT_zero.comp h).congr fun z => ?_
  simp [norm_pow]

/-- Beck Example 3.2.3 (CX-039). The limit at `∞` of `(a z + b)/(c z + d)` is `a / c` when `c ≠ 0`. -/
@[kb "beck2025" "Example 3.2.3, p. 51"]
theorem tendsto_mobius_cobounded {a b c d : ℂ} (hc : c ≠ 0) :
    Tendsto (fun z : ℂ => (a * z + b) / (c * z + d)) (Bornology.cobounded ℂ) (𝓝 (a / c)) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have h1 : Tendsto (fun z : ℂ => (a + b * z⁻¹) / (c + d * z⁻¹)) (Bornology.cobounded ℂ)
      (𝓝 ((a + b * 0) / (c + d * 0))) :=
    (tendsto_const_nhds.add (hinv.const_mul b)).div (tendsto_const_nhds.add (hinv.const_mul d))
      (by simpa using hc)
  simp only [mul_zero, add_zero] at h1
  refine h1.congr' ?_
  have hne : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z⁻¹ ≠ 0 :=
    (tendsto_inv₀_cobounded' (α := ℂ)).eventually self_mem_nhdsWithin
  filter_upwards [hne] with z hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have e1 : a + b * z⁻¹ = (a * z + b) * z⁻¹ := by field_simp
  have e2 : c + d * z⁻¹ = (c * z + d) * z⁻¹ := by field_simp
  rw [e1, e2, mul_div_mul_right _ _ hz]

/-- Beck Example 3.2.3 (CX-039). For `a d - b c ≠ 0` and `c ≠ 0`, `(a z + b)/(c z + d) → ∞` as
`z → -d/c`. -/
@[kb "beck2025" "Example 3.2.3, p. 51"]
theorem tendsto_mobius_pole {a b c d : ℂ} (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) :
    Tendsto (fun z : ℂ => ‖(a * z + b) / (c * z + d)‖) (𝓝[≠] (-d / c)) atTop := by
  set z₀ : ℂ := -d / c with hz₀
  have hN : a * z₀ + b ≠ 0 := by
    intro h
    apply hdet
    have : a * (-d / c) + b = 0 := h
    field_simp at this
    linear_combination -this
  have hnum : Tendsto (fun z : ℂ => ‖a * z + b‖ * ‖c‖⁻¹) (𝓝[≠] z₀) (𝓝 (‖a * z₀ + b‖ * ‖c‖⁻¹)) := by
    have : Continuous fun z : ℂ => ‖a * z + b‖ * ‖c‖⁻¹ := by fun_prop
    exact (this.tendsto z₀).mono_left nhdsWithin_le_nhds
  have hpos : 0 < ‖a * z₀ + b‖ * ‖c‖⁻¹ :=
    mul_pos (norm_pos_iff.2 hN) (inv_pos.2 (norm_pos_iff.2 hc))
  refine (hnum.pos_mul_atTop hpos (tendsto_inv_norm_sub_atTop' z₀)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hden : c * z + d = c * (z - z₀) := by rw [hz₀]; field_simp; ring
  rw [hden, norm_div, norm_mul]
  field_simp

/-! ## Branches of the logarithm (CX-051) -/

/-- Beck Definition 3.5.1 (CX-051). `L` is a branch of the logarithm on `G`: it is continuous on `G`
and `exp (L z) = z` for `z ∈ G`. -/
@[kb "beck2025" "Definition 3.5.1, p. 61"]
def IsBranchOfLog (L : ℂ → ℂ) (G : Set ℂ) : Prop :=
  ContinuousOn L G ∧ ∀ z ∈ G, Complex.exp (L z) = z

/-- Beck Definition 3.5.1 (CX-051). The principal logarithm is a branch on the slit plane. -/
@[kb "beck2025" "Definition 3.5.1, p. 61"]
theorem isBranchOfLog_log : IsBranchOfLog Complex.log slitPlane :=
  ⟨fun _ hz => (continuousAt_clog hz).continuousWithinAt,
    fun _ hz => exp_log (slitPlane_ne_zero hz)⟩

/-- A continuous integer-valued real function on a preconnected set is constant. -/
theorem constant_of_int_valued {S : Set ℂ} (hS : IsPreconnected S) {φ : ℂ → ℝ}
    (hc : ContinuousOn φ S) (hint : ∀ z ∈ S, ∃ k : ℤ, φ z = k) :
    ∀ x ∈ S, ∀ y ∈ S, φ x = φ y := by
  have key : ∀ x ∈ S, ∀ y ∈ S, φ x ≤ φ y → φ x = φ y := by
    intro x hx y hy hxy
    by_contra hne
    have hlt : φ x < φ y := lt_of_le_of_ne hxy hne
    obtain ⟨m, hm⟩ := hint x hx
    obtain ⟨n, hn⟩ := hint y hy
    have hmn : m + 1 ≤ n := by
      have : (m : ℝ) < n := by rw [← hm, ← hn]; exact hlt
      exact_mod_cast this
    have hIcc := (hS.image φ hc).Icc_subset (mem_image_of_mem φ hx) (mem_image_of_mem φ hy)
    have ht : ((m : ℝ) + 1 / 2) ∈ Icc (φ x) (φ y) := by
      rw [hm, hn]
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
      constructor <;> linarith
    obtain ⟨z, hz, hzt⟩ := hIcc ht
    obtain ⟨k, hk⟩ := hint z hz
    rw [hk] at hzt
    rcases le_or_gt k m with h | h
    · have : (k : ℝ) ≤ m := by exact_mod_cast h
      linarith
    · have : (m : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
  intro x hx y hy
  rcases le_total (φ x) (φ y) with h | h
  · exact key x hx y hy h
  · exact (key y hy x hx h).symm

/-- Beck Definition 3.5.1 (CX-051). Two branches of the logarithm on a connected set differ by a
constant `2πik`, `k ∈ ℤ`. -/
@[kb "beck2025" "Definition 3.5.1, p. 61"]
theorem branches_differ_by_const {L₁ L₂ : ℂ → ℂ} {G : Set ℂ} (hG : IsPreconnected G)
    (h₁ : IsBranchOfLog L₁ G) (h₂ : IsBranchOfLog L₂ G) :
    ∃ k : ℤ, ∀ z ∈ G, L₁ z = L₂ z + 2 * π * I * k := by
  have hn : ∀ z ∈ G, ∃ n : ℤ, L₁ z = L₂ z + n * (2 * π * I) := fun z hz =>
    exp_eq_exp_iff_exists_int.1 ((h₁.2 z hz).trans (h₂.2 z hz).symm)
  rcases G.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, by simp⟩
  obtain ⟨k, hk⟩ := hn z₀ hz₀
  refine ⟨k, fun z hz => ?_⟩
  obtain ⟨n, hnz⟩ := hn z hz
  have him : ∀ w ∈ G, ∀ m : ℤ, L₁ w = L₂ w + m * (2 * π * I) →
      (L₁ w - L₂ w).im / (2 * π) = m := by
    intro w _ m hm
    have : L₁ w - L₂ w = m * (2 * π * I) := by rw [hm]; ring
    rw [this]
    simp
  have hcont : ContinuousOn (fun w => (L₁ w - L₂ w).im / (2 * π)) G :=
    (Complex.continuous_im.comp_continuousOn (h₁.1.sub h₂.1)).div_const _
  have := constant_of_int_valued hG hcont (fun w hw => by
    obtain ⟨m, hm⟩ := hn w hw
    exact ⟨m, him w hw m hm⟩) z hz z₀ hz₀
  rw [him z hz n hnz, him z₀ hz₀ k hk] at this
  have hnk : n = k := by exact_mod_cast this
  rw [hnz, hnk]
  ring

/-! ## Antiderivatives (CX-061) -/

/-- Beck Example 4.2.2 (CX-061). `z ↦ z³/3` is an antiderivative of `z ↦ z²` on `ℂ`. -/
@[kb "beck2025" "Example 4.2.2, p. 75"]
theorem hasDerivAt_cube_div_three (z : ℂ) : HasDerivAt (fun w : ℂ => w ^ 3 / 3) (z ^ 2) z := by
  have := (hasDerivAt_pow 3 z).div_const 3
  convert this using 1
  push_cast
  ring

/-- Beck Example 4.2.3 (CX-061). `-cos` is an antiderivative of `sin` on `ℂ`. -/
@[kb "beck2025" "Example 4.2.3, p. 75"]
theorem hasDerivAt_neg_cos (z : ℂ) : HasDerivAt (fun w : ℂ => -Complex.cos w) (Complex.sin z) z := by
  exact HasDerivAt.congr_deriv (Complex.hasDerivAt_cos z).neg (neg_neg _)

/-- Beck Example 4.2.4 (CX-061). The principal logarithm is an antiderivative of `1/z` on the slit
plane. -/
@[kb "beck2025" "Example 4.2.4, p. 75"]
theorem hasDerivAt_log_one_div {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt Complex.log (1 / z) z := by
  simpa using (hasStrictDerivAt_log hz).hasDerivAt

/-! ## Size of a polynomial (CX-078) -/

/-- Beck Proposition 5.3.1 (CX-078). A polynomial of degree `d ≥ 1` with leading coefficient `a`
satisfies `|a||z|^d / 2 ≤ |p(z)| ≤ 2|a||z|^d` for `|z|` large. -/
@[kb "beck2025" "Proposition 5.3.1, p. 95"]
theorem polynomial_norm_bounds (p : Polynomial ℂ) (hd : 1 ≤ p.natDegree) :
    ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖p.leadingCoeff‖ * ‖z‖ ^ p.natDegree / 2 ≤ ‖p.eval z‖ ∧
        ‖p.eval z‖ ≤ 2 * ‖p.leadingCoeff‖ * ‖z‖ ^ p.natDegree := by
  set d := p.natDegree with hdd
  set a := p.leadingCoeff with ha
  have hp0 : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) hd
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hp0)
  set B := ∑ i ∈ Finset.range d, ‖p.coeff i‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨max 1 (2 * B / ‖a‖), lt_max_of_lt_left one_pos, fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hz2 : 2 * B / ‖a‖ ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hBz : B ≤ ‖a‖ * ‖z‖ / 2 := by
    rw [div_le_iff₀ ha0] at hz2; linarith
  have hsplit : p.eval z = (∑ i ∈ Finset.range d, p.coeff i * z ^ i) + a * z ^ d := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]; rfl
  have hzd : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlow : ‖∑ i ∈ Finset.range d, p.coeff i * z ^ i‖ ≤ ‖a‖ * ‖z‖ ^ d / 2 := by
    calc _ ≤ ∑ i ∈ Finset.range d, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖z‖ ^ (d - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hz1 (by have := Finset.mem_range.1 hi; omega)) (norm_nonneg _)
      _ = B * ‖z‖ ^ (d - 1) := by rw [← Finset.sum_mul]
      _ ≤ (‖a‖ * ‖z‖ / 2) * ‖z‖ ^ (d - 1) :=
          mul_le_mul_of_nonneg_right hBz (by positivity)
      _ = ‖a‖ * ‖z‖ ^ d / 2 := by rw [hzd]; ring
  have hlead : ‖a * z ^ d‖ = ‖a‖ * ‖z‖ ^ d := by rw [norm_mul, norm_pow]
  have hpos : 0 ≤ ‖a‖ * ‖z‖ ^ d := by positivity
  constructor
  · have e : a * z ^ d = p.eval z - ∑ i ∈ Finset.range d, p.coeff i * z ^ i := by
      rw [hsplit]; ring
    have := norm_sub_le (p.eval z) (∑ i ∈ Finset.range d, p.coeff i * z ^ i)
    rw [← e, hlead] at this
    linarith
  · rw [hsplit]
    have := norm_add_le (∑ i ∈ Finset.range d, p.coeff i * z ^ i) (a * z ^ d)
    rw [hlead] at this
    linarith

/-! ## Polygonal paths with horizontal and vertical segments (CX-019) -/

/-- Beck Theorem 1.4.16 (CX-019). `HVJoined G a b` says that `b` is reached from `a` by a finite
chain of points in which consecutive points share their real part or their imaginary part
(a horizontal or vertical step) and the closed segment between them lies in `G`. -/
@[kb "beck2025" "Theorem 1.4.16, p. 25"]
inductive HVJoined (G : Set ℂ) (a : ℂ) : ℂ → Prop
  | refl (h : a ∈ G) : HVJoined G a a
  | step {b c : ℂ} : HVJoined G a b → (b.re = c.re ∨ b.im = c.im) → segment ℝ b c ⊆ G →
      HVJoined G a c

private theorem norm_re_step_le (x y : ℂ) : ‖(⟨y.re, x.im⟩ : ℂ) - x‖ ≤ ‖y - x‖ := by
  have : (⟨y.re, x.im⟩ : ℂ) - x = (((y - x).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp)
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

private theorem norm_im_step_le (x y : ℂ) : ‖(⟨x.re, y.im⟩ : ℂ) - x‖ ≤ ‖y - x‖ := by
  have : (⟨x.re, y.im⟩ : ℂ) - x = (((y - x).im : ℝ) : ℂ) * I := Complex.ext (by simp) (by simp)
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm _

private theorem hv_forward {G : Set ℂ} {a x y : ℂ} {ε : ℝ} (hB : ball x ε ⊆ G)
    (hy : y ∈ ball x ε) (h : HVJoined G a x) : HVJoined G a y := by
  have hε : 0 < ε := dist_nonneg.trans_lt (mem_ball.1 hy)
  have hm : (⟨y.re, x.im⟩ : ℂ) ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    exact (norm_re_step_le x y).trans_lt hy
  have s1 : HVJoined G a ⟨y.re, x.im⟩ := HVJoined.step (c := ⟨y.re, x.im⟩) h (Or.inr rfl)
    (((convex_ball x ε).segment_subset (mem_ball_self hε) hm).trans hB)
  exact HVJoined.step s1 (Or.inl rfl) (((convex_ball x ε).segment_subset hm hy).trans hB)

private theorem hv_backward {G : Set ℂ} {a x y : ℂ} {ε : ℝ} (hB : ball x ε ⊆ G)
    (hy : y ∈ ball x ε) (h : HVJoined G a y) : HVJoined G a x := by
  have hε : 0 < ε := dist_nonneg.trans_lt (mem_ball.1 hy)
  have hm : (⟨x.re, y.im⟩ : ℂ) ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    exact (norm_im_step_le x y).trans_lt hy
  have s1 : HVJoined G a ⟨x.re, y.im⟩ := HVJoined.step (c := ⟨x.re, y.im⟩) h (Or.inr rfl)
    (((convex_ball x ε).segment_subset hy hm).trans hB)
  exact HVJoined.step s1 (Or.inl rfl)
    (((convex_ball x ε).segment_subset hm (mem_ball_self hε)).trans hB)

/-- Beck Theorem 1.4.16 and Example 1.4.17 (CX-019). In an open connected set `G` any two points
`a, b` are joined by a polygonal path of horizontal and vertical segments inside `G`. -/
@[kb "beck2025" "Theorem 1.4.16, p. 25"]
theorem hvJoined_of_isPreconnected {G : Set ℂ} (hG : IsOpen G) (hc : IsPreconnected G)
    {a b : ℂ} (ha : a ∈ G) (hb : b ∈ G) : HVJoined G a b := by
  have hUo : IsOpen {z | z ∈ G ∧ HVJoined G a z} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzG, hz⟩
    obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hG z hzG
    exact ⟨ε, hε, fun y hy => ⟨hB hy, hv_forward hB hy hz⟩⟩
  have hVo : IsOpen {z | z ∈ G ∧ ¬ HVJoined G a z} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzG, hz⟩
    obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hG z hzG
    exact ⟨ε, hε, fun y hy => ⟨hB hy, fun hy' => hz (hv_backward hB hy hy')⟩⟩
  have hdisj : Disjoint {z | z ∈ G ∧ HVJoined G a z} {z | z ∈ G ∧ ¬ HVJoined G a z} := by
    rw [Set.disjoint_left]
    exact fun z hz hz' => hz'.2 hz.2
  have hsub : G ⊆ {z | z ∈ G ∧ HVJoined G a z} ∪ {z | z ∈ G ∧ ¬ HVJoined G a z} := by
    intro z hz
    by_cases h : HVJoined G a z
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have := hc.subset_left_of_subset_union hUo hVo hdisj hsub ⟨a, ha, ha, HVJoined.refl ha⟩ hb
  exact this.2

end UndergradKB.ComplexAnalysis
