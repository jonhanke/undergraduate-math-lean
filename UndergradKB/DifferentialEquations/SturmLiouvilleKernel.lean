import UndergradKB.DifferentialEquations.SturmLiouvilleL2
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # The Green operator of a regular Sturm-Liouville problem is injective

If `F ∈ L²(r dx)` is orthogonal to every `C²` function vanishing near both endpoints, then `F = 0`
(`eq_zero_of_perp_bc`): such functions contain `χ_k g` for smooth compactly supported `g` and cutoffs `χ_k`
that equal `1` on larger and larger subintervals of `(a, b)`; dominated convergence gives
`∫ F g r dx = 0`, and smooth compactly supported functions are dense in `L²`.

Consequently the Green operator has trivial kernel (`greenOp_eq_zero_iff`): its range contains all such
`C²` functions (`toL2_mem_range`) and it is symmetric. -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace RegularSL

variable (S : RegularSL)

/-- Cutoff function centered at the midpoint of `[a, b]`, equal to `1` on a ball of radius
`(b-a)/2 - (b-a)/(4(k+1))` and vanishing outside the ball of radius `(b-a)/2 - (b-a)/(8(k+1))`. -/
noncomputable def cutoff (k : ℕ) : ContDiffBump ((S.a + S.b) / 2) where
  rIn := (S.b - S.a) / 2 - (S.b - S.a) / ((k : ℝ) + 1) / 4
  rOut := (S.b - S.a) / 2 - (S.b - S.a) / ((k : ℝ) + 1) / 8
  rIn_pos := by
    have h1 : 0 < (S.b - S.a) / ((k : ℝ) + 1) := div_pos (sub_pos.2 S.hab) (by positivity)
    have h2 : (S.b - S.a) / ((k : ℝ) + 1) ≤ S.b - S.a :=
      div_le_self (sub_pos.2 S.hab).le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    linarith
  rIn_lt_rOut := by
    have h1 : 0 < (S.b - S.a) / ((k : ℝ) + 1) := div_pos (sub_pos.2 S.hab) (by positivity)
    linarith

lemma cutoff_eventually_zero_a (k : ℕ) : ∀ᶠ t in 𝓝 S.a, S.cutoff k t = 0 := by
  have h1 : 0 < (S.b - S.a) / ((k : ℝ) + 1) := div_pos (sub_pos.2 S.hab) (by positivity)
  filter_upwards [Iio_mem_nhds (show S.a < S.a + (S.b - S.a) / ((k : ℝ) + 1) / 8 by linarith)] with t ht
  simp only [mem_Iio] at ht
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  show (S.b - S.a) / 2 - (S.b - S.a) / ((k : ℝ) + 1) / 8 ≤ |t - (S.a + S.b) / 2|
  have := le_abs_self (-(t - (S.a + S.b) / 2))
  rw [abs_neg] at this
  linarith

lemma cutoff_eventually_zero_b (k : ℕ) : ∀ᶠ t in 𝓝 S.b, S.cutoff k t = 0 := by
  have h1 : 0 < (S.b - S.a) / ((k : ℝ) + 1) := div_pos (sub_pos.2 S.hab) (by positivity)
  filter_upwards [Ioi_mem_nhds (show S.b - (S.b - S.a) / ((k : ℝ) + 1) / 8 < S.b by linarith)] with t ht
  simp only [mem_Ioi] at ht
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  show (S.b - S.a) / 2 - (S.b - S.a) / ((k : ℝ) + 1) / 8 ≤ |t - (S.a + S.b) / 2|
  have := le_abs_self (t - (S.a + S.b) / 2)
  linarith

lemma cutoff_eventually_one {t : ℝ} (ht : t ∈ Ioo S.a S.b) : ∀ᶠ k : ℕ in atTop, S.cutoff k t = 1 := by
  have hab : |t - (S.a + S.b) / 2| < (S.b - S.a) / 2 := by
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (S.b - S.a)
  have hev := hlim.eventually
    (gt_mem_nhds (show (S.b - S.a) * 0 < 4 * ((S.b - S.a) / 2 - |t - (S.a + S.b) / 2|) by linarith))
  filter_upwards [hev] with k hk
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  show |t - (S.a + S.b) / 2| ≤ (S.b - S.a) / 2 - (S.b - S.a) / ((k : ℝ) + 1) / 4
  have e : (S.b - S.a) / ((k : ℝ) + 1) = (S.b - S.a) * (1 / ((k : ℝ) + 1)) := by rw [mul_one_div]
  rw [e]
  linarith

/-- Almost every point for the weighted measure lies in the open interval `(a, b)`. -/
lemma ae_mem_Ioo : ∀ᵐ t ∂S.wμ, t ∈ Ioo S.a S.b := by
  have h0 : volume ({S.a, S.b} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({S.a, S.b} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 h0
  have hac : S.wμ ≪ (volume : Measure ℝ) :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  filter_upwards [hac.ae_le h1, S.ae_mem] with t h1 h2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at h1
  exact ⟨lt_of_le_of_ne h2.1 (Ne.symm h1.1), lt_of_le_of_ne h2.2 h1.2⟩

/-- If `F` is orthogonal to all `C²` functions vanishing near the endpoints, then `∫ F g dν = 0` for every
`C²` compactly supported `g`. -/
lemma integral_eq_zero_of_perp_bc {F : Lp ℝ 2 S.wμ}
    (hF : ∀ (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y), (∀ᶠ t in 𝓝 S.a, y t = 0) → (∀ᶠ t in 𝓝 S.b, y t = 0) →
      ⟪F, S.toL2 y hy.continuous⟫ = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgs : HasCompactSupport g) :
    ∫ t, F t * g t ∂S.wμ = 0 := by
  have hk : ∀ k : ℕ, ∫ t, F t * (S.cutoff k t * g t) ∂S.wμ = 0 := by
    intro k
    have hy : ContDiff ℝ 2 (fun t => S.cutoff k t * g t) := (S.cutoff k).contDiff.mul hg
    have h := hF _ hy
      ((S.cutoff_eventually_zero_a k).mono fun t ht => by simp [ht])
      ((S.cutoff_eventually_zero_b k).mono fun t ht => by simp [ht])
    rw [MeasureTheory.L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [S.toL2_ae hy.continuous] with t ht
    rw [ht]
    simp [mul_comm]
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgs
  have hFi : Integrable (fun t => F t) S.wμ := (Lp.memLp F).integrable one_le_two
  have hlim : Tendsto (fun k : ℕ => ∫ t, F t * (S.cutoff k t * g t) ∂S.wμ) atTop
      (𝓝 (∫ t, F t * g t ∂S.wμ)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖F t‖ * C) ?_ (hFi.norm.mul_const C) ?_ ?_
    · intro k
      exact ((Lp.memLp F).aestronglyMeasurable).mul
        (((S.cutoff k).continuous.mul hg.continuous).aestronglyMeasurable)
    · intro k
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (S.cutoff k).nonneg]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc S.cutoff k t * ‖g t‖ ≤ 1 * C :=
            mul_le_mul (S.cutoff k).le_one (hC t) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · filter_upwards [S.ae_mem_Ioo] with t ht
      have : ∀ᶠ k : ℕ in atTop, F t * (S.cutoff k t * g t) = F t * g t :=
        (S.cutoff_eventually_one ht).mono fun k hk => by rw [hk, one_mul]
      exact tendsto_const_nhds.congr' (this.mono fun k hk => hk.symm)
  have h0 : Tendsto (fun k : ℕ => ∫ t, F t * (S.cutoff k t * g t) ∂S.wμ) atTop (𝓝 0) := by
    simp only [hk]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

/-- A function orthogonal in `L²(r dx)` to every `C²` function vanishing near `a` and near `b` is zero. -/
theorem eq_zero_of_perp_bc {F : Lp ℝ 2 S.wμ}
    (hF : ∀ (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y), (∀ᶠ t in 𝓝 S.a, y t = 0) → (∀ᶠ t in 𝓝 S.b, y t = 0) →
      ⟪F, S.toL2 y hy.continuous⟫ = 0) : F = 0 := by
  have hD := Lp.dense_hasCompactSupport_contDiff (μ := S.wμ) (F := ℝ) (E := ℝ) (p := 2) (by norm_num)
  have hclosed : IsClosed {f : Lp ℝ 2 S.wμ | ⟪F, f⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : {f : Lp ℝ 2 S.wμ | ∃ (g : ℝ → ℝ), f =ᵐ[S.wμ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆
      {f : Lp ℝ 2 S.wμ | ⟪F, f⟫ = 0} := by
    rintro f ⟨g, hfg, hgs, hgd⟩
    show ⟪F, f⟫ = 0
    rw [MeasureTheory.L2.inner_def]
    rw [← S.integral_eq_zero_of_perp_bc hF (hgd.of_le (WithTop.coe_le_coe.2 le_top)) hgs]
    refine integral_congr_ae ?_
    filter_upwards [hfg] with t ht
    rw [ht]
    simp [mul_comm]
  have hFF : ⟪F, F⟫ = 0 := closure_minimal hsub hclosed (hD F)
  exact inner_self_eq_zero.1 hFF

/-- The Green operator is injective. -/
theorem greenOp_eq_zero_iff {F : Lp ℝ 2 S.wμ} : S.greenOp F = 0 ↔ F = 0 := by
  constructor
  · intro h
    refine S.eq_zero_of_perp_bc fun y hy ha hb => ?_
    have ya : y S.a = 0 := ha.self_of_nhds
    have yb : y S.b = 0 := hb.self_of_nhds
    have dya : deriv y S.a = 0 := by
      rw [(show y =ᶠ[𝓝 S.a] fun _ => (0 : ℝ) from ha).deriv_eq]; simp
    have dyb : deriv y S.b = 0 := by
      rw [(show y =ᶠ[𝓝 S.b] fun _ => (0 : ℝ) from hb).deriv_eq]; simp
    obtain ⟨φ, hφ⟩ := S.toL2_mem_range hy (by rw [ya, dya]; ring) (by rw [yb, dyb]; ring)
    rw [← hφ, ← S.isSymmetric_greenOp F φ]
    simp [h]
  · rintro rfl
    exact map_zero _

end RegularSL

end UndergradKB.DifferentialEquations
