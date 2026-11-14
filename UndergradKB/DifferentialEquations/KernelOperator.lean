import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Function.Floor

/-! # Integral operators with a continuous kernel are compact and self-adjoint on L²

Wave 4 named the missing input for the Sturm-Liouville spectral theorem (Lebl, Theorem 5.1.1): the compactness of
the integral operator `f ↦ ∫ K(x, t) f(t) dν(t)` on `L²(ν)` for a continuous kernel `K`.  Here `ν` is a finite
measure on `ℝ` carried by an interval `[a, b]` (for Sturm-Liouville problems, `r(x) dx` on `[a, b]`).

Construction: for `x : ℝ` the section `K x ·` is a bounded function, hence an element `kSection x` of `L²(ν)`, and
`(T f)(x) = ⟪kSection x, f⟫`.  More generally, `lpOp κ` is the operator `f ↦ (x ↦ ⟪κ x, f⟫)` for any bounded strongly
measurable `κ : ℝ → L²(ν)`, with `‖lpOp κ - lpOp κ'‖ ≤ C sup ‖κ x - κ' x‖`.  Freezing `x` on a grid of `[a, b]`
gives finite-rank operators (sums of rank-one operators `f ↦ ⟪u, f⟫ w`) converging to `T` in operator norm, by the
uniform continuity of `K` on `[a, b]²`; a limit of compact operators is compact.  A symmetric kernel gives a
symmetric operator (Fubini). -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace KernelOp

variable {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- The constant of `Lp.norm_le_of_ae_bound` for `p = 2`. -/
noncomputable def cν (ν : Measure ℝ) [IsFiniteMeasure ν] : ℝ :=
  (measureUnivNNReal ν : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹

lemma cν_nonneg : 0 ≤ cν ν := Real.rpow_nonneg (NNReal.coe_nonneg _) _

lemma norm_le_of_ae_bound' {g : Lp ℝ 2 ν} {C : ℝ} (hC : 0 ≤ C) (h : ∀ᵐ x ∂ν, ‖g x‖ ≤ C) :
    ‖g‖ ≤ cν ν * C := by
  have := Lp.norm_le_of_ae_bound hC h
  simpa [cν] using this

/-- The function `x ↦ ⟪κ x, f⟫` is in `L²`. -/
lemma memLp_inner {κ : ℝ → Lp ℝ 2 ν} (hκ : StronglyMeasurable κ) {B : ℝ} (hB : ∀ x, ‖κ x‖ ≤ B)
    (f : Lp ℝ 2 ν) : MemLp (fun x => ⟪κ x, f⟫) 2 ν := by
  refine MemLp.of_bound ?_ (B * ‖f‖) (ae_of_all _ fun x => ?_)
  · exact ((continuous_id.inner continuous_const).comp_stronglyMeasurable hκ).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

/-- The linear map `f ↦ (x ↦ ⟪κ x, f⟫)`. -/
noncomputable def lpOpₗ (κ : ℝ → Lp ℝ 2 ν) (hκ : StronglyMeasurable κ) (B : ℝ) (hB : ∀ x, ‖κ x‖ ≤ B) :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := (memLp_inner hκ hB f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_inner hκ hB (f + g)), MemLp.coeFn_toLp (memLp_inner hκ hB f),
      MemLp.coeFn_toLp (memLp_inner hκ hB g),
      Lp.coeFn_add ((memLp_inner hκ hB f).toLp _) ((memLp_inner hκ hB g).toLp _)] with x h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3, inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_inner hκ hB (c • f)), MemLp.coeFn_toLp (memLp_inner hκ hB f),
      Lp.coeFn_smul c ((memLp_inner hκ hB f).toLp _)] with x h1 h2 h3
    rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, real_inner_smul_right, smul_eq_mul]

lemma lpOpₗ_apply_ae (κ : ℝ → Lp ℝ 2 ν) (hκ : StronglyMeasurable κ) (B : ℝ) (hB : ∀ x, ‖κ x‖ ≤ B)
    (f : Lp ℝ 2 ν) : lpOpₗ κ hκ B hB f =ᵐ[ν] fun x => ⟪κ x, f⟫ :=
  MemLp.coeFn_toLp (memLp_inner hκ hB f)

omit [IsFiniteMeasure ν] in
lemma B_nonneg {κ : ℝ → Lp ℝ 2 ν} {B : ℝ} (hB : ∀ x, ‖κ x‖ ≤ B) : 0 ≤ B :=
  (norm_nonneg _).trans (hB 0)

/-- The continuous linear operator `f ↦ (x ↦ ⟪κ x, f⟫)`. -/
noncomputable def lpOp (κ : ℝ → Lp ℝ 2 ν) (hκ : StronglyMeasurable κ) (B : ℝ) (hB : ∀ x, ‖κ x‖ ≤ B) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (lpOpₗ κ hκ B hB).mkContinuous (cν ν * B) fun f => by
    rw [mul_assoc]
    refine norm_le_of_ae_bound' (mul_nonneg (B_nonneg hB) (norm_nonneg _)) ?_
    filter_upwards [lpOpₗ_apply_ae κ hκ B hB f] with x hx
    rw [hx, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

lemma lpOp_apply_ae (κ : ℝ → Lp ℝ 2 ν) (hκ : StronglyMeasurable κ) (B : ℝ) (hB : ∀ x, ‖κ x‖ ≤ B)
    (f : Lp ℝ 2 ν) : lpOp κ hκ B hB f =ᵐ[ν] fun x => ⟪κ x, f⟫ :=
  lpOpₗ_apply_ae κ hκ B hB f

/-- Two such operators are close when the `κ` are uniformly close `ν`-almost everywhere. -/
lemma norm_lpOp_sub_le {κ κ' : ℝ → Lp ℝ 2 ν} (hκ : StronglyMeasurable κ) (hκ' : StronglyMeasurable κ')
    {B B' : ℝ} (hB : ∀ x, ‖κ x‖ ≤ B) (hB' : ∀ x, ‖κ' x‖ ≤ B') {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ᵐ x ∂ν, ‖κ x - κ' x‖ ≤ ε) : ‖lpOp κ hκ B hB - lpOp κ' hκ' B' hB'‖ ≤ cν ν * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg cν_nonneg hε) fun f => ?_
  rw [mul_assoc]
  refine norm_le_of_ae_bound' (mul_nonneg hε (norm_nonneg _)) ?_
  filter_upwards [h, lpOp_apply_ae κ hκ B hB f, lpOp_apply_ae κ' hκ' B' hB' f,
    Lp.coeFn_sub (lpOp κ hκ B hB f) (lpOp κ' hκ' B' hB' f)] with x hx h1 h2 h3
  rw [sub_apply, h3, Pi.sub_apply, h1, h2, ← inner_sub_left, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

omit [IsFiniteMeasure ν] in
/-- The coercion of a finite sum in `L²` is almost everywhere the sum of the coercions. -/
lemma coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 ν) :
    ⇑(∑ i ∈ s, F i) =ᵐ[ν] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    simp only [Finset.sum_empty]
    exact hx
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (F j) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hj]

omit [IsFiniteMeasure ν] in
/-- The rank-one operator `f ↦ ⟪u, f⟫ w`. -/
noncomputable def rankOne (u w : Lp ℝ 2 ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν := (innerSL ℝ u).smulRight w

omit [IsFiniteMeasure ν] in
lemma rankOne_apply (u w f : Lp ℝ 2 ν) : rankOne u w f = ⟪u, f⟫ • w := by
  simp [rankOne, innerSL_apply_apply]

omit [IsFiniteMeasure ν] in
lemma isCompactOperator_rankOne (u w : Lp ℝ 2 ν) : IsCompactOperator (rankOne u w) := by
  have h : IsCompactOperator (innerSL ℝ u) := isCompactOperator_of_locallyCompactSpace_dom _
  have := h.continuous_comp (g := fun c : ℝ => c • w) (continuous_id.smul continuous_const)
  convert this using 1
  funext f
  simp [rankOne_apply]

omit [IsFiniteMeasure ν] in
lemma isCompactOperator_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hF : ∀ i ∈ s, IsCompactOperator (F i)) : IsCompactOperator ⇑(∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, FunLike.coe_add]
    have h1 := hF j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    exact h1.add h2

/-- A continuous kernel bounded by `M`. -/
structure Kernel where
  /-- The kernel `K(x, t)`. -/
  K : ℝ → ℝ → ℝ
  /-- A bound for `|K|`. -/
  M : ℝ
  cont : Continuous (fun z : ℝ × ℝ => K z.1 z.2)
  bound : ∀ x t, |K x t| ≤ M

namespace Kernel

variable (k : Kernel)

lemma M_nonneg : 0 ≤ k.M := (abs_nonneg _).trans (k.bound 0 0)

lemma continuous_section (x : ℝ) : Continuous (k.K x) :=
  k.cont.comp (continuous_const.prodMk continuous_id)

variable (ν) in
lemma memLp_section (x : ℝ) : MemLp (k.K x) 2 ν :=
  MemLp.of_bound (k.continuous_section x).aestronglyMeasurable k.M
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact k.bound x t)

variable (ν) in
/-- The section `K x ·` as an element of `L²(ν)`. -/
noncomputable def sec (x : ℝ) : Lp ℝ 2 ν := (k.memLp_section ν x).toLp _

lemma sec_ae (x : ℝ) : k.sec ν x =ᵐ[ν] k.K x := MemLp.coeFn_toLp _

lemma norm_sec_le (x : ℝ) : ‖k.sec ν x‖ ≤ cν ν * k.M := by
  refine norm_le_of_ae_bound' k.M_nonneg ?_
  filter_upwards [k.sec_ae x] with t ht
  rw [ht, Real.norm_eq_abs]; exact k.bound x t

lemma norm_sec_sub_le {x x' ε : ℝ} (hε : 0 ≤ ε) (h : ∀ᵐ t ∂ν, |k.K x t - k.K x' t| ≤ ε) :
    ‖k.sec ν x - k.sec ν x'‖ ≤ cν ν * ε := by
  refine norm_le_of_ae_bound' hε ?_
  filter_upwards [h, k.sec_ae x, k.sec_ae x', Lp.coeFn_sub (k.sec ν x) (k.sec ν x')] with t h0 h1 h2 h3
  rw [h3, Pi.sub_apply, h1, h2, Real.norm_eq_abs]; exact h0

lemma inner_sec (x : ℝ) (f : Lp ℝ 2 ν) : ⟪k.sec ν x, f⟫ = ∫ t, k.K x t * f t ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [k.sec_ae x] with t ht
  rw [ht]
  simp [mul_comm]

variable {a b : ℝ}

/-- Uniform continuity of the sections on a compact set, when `ν` lives on `[a, b]`. -/
lemma sec_unif (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) {s : Set ℝ} (hs : IsCompact s) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ s, ∀ x' ∈ s, |x - x'| < δ → ‖k.sec ν x - k.sec ν x'‖ ≤ η := by
  have hc : IsCompact (s ×ˢ Icc a b) := hs.prod isCompact_Icc
  have hu := hc.uniformContinuousOn_of_continuous k.cont.continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (η / (cν ν + 1)) (div_pos hη (by linarith [cν_nonneg (ν := ν)]))
  refine ⟨δ, hδ, fun x hx x' hx' hxx' => ?_⟩
  have hb : ‖k.sec ν x - k.sec ν x'‖ ≤ cν ν * (η / (cν ν + 1)) := by
    refine k.norm_sec_sub_le (div_pos hη (by linarith [cν_nonneg (ν := ν)])).le ?_
    filter_upwards [hν] with t ht
    have := hδ' (x, t) ⟨hx, ht⟩ (x', t) ⟨hx', ht⟩ (by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_le hxx'.le (le_of_lt hδ))
    rwa [Real.dist_eq] at this
  calc ‖k.sec ν x - k.sec ν x'‖ ≤ cν ν * (η / (cν ν + 1)) := hb
    _ ≤ η := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by linarith [cν_nonneg (ν := ν)])]
      nlinarith [cν_nonneg (ν := ν)]

lemma continuous_sec (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) : Continuous (k.sec ν) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, h⟩ := k.sec_unif hν (isCompact_Icc (a := x - 1) (b := x + 1)) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun x' hx' => ?_⟩
  rw [Real.dist_eq] at hx'
  have h1 : |x' - x| < 1 := hx'.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  refine (h x' ⟨by linarith [abs_lt.1 h1], by linarith [abs_lt.1 h1]⟩ x
    ⟨by linarith, by linarith⟩ (hx'.trans_le (min_le_left _ _))).trans_lt (half_lt_self hε)

variable (ν) in
/-- **The integral operator** `f ↦ (x ↦ ∫ K(x, t) f(t) dν(t))` on `L²(ν)`. -/
noncomputable def op (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  lpOp (k.sec ν) (k.continuous_sec hν).stronglyMeasurable (cν ν * k.M) k.norm_sec_le

lemma op_apply_ae (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) (f : Lp ℝ 2 ν) :
    k.op ν hν f =ᵐ[ν] fun x => ∫ t, k.K x t * f t ∂ν := by
  filter_upwards [lpOp_apply_ae (k.sec ν) (k.continuous_sec hν).stronglyMeasurable (cν ν * k.M)
    k.norm_sec_le f] with x hx
  rw [op, hx, k.inner_sec]

lemma op_apply_ae' (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) (f : Lp ℝ 2 ν) :
    k.op ν hν f =ᵐ[ν] fun x => ⟪k.sec ν x, f⟫ :=
  lpOp_apply_ae (k.sec ν) (k.continuous_sec hν).stronglyMeasurable (cν ν * k.M) k.norm_sec_le f

/-! ### Finite-rank approximations: freeze `x` on a grid of `[a, b]` -/

/-- Index of the grid cell of `x` (grid of `N` cells on `[a, b]`, the last one closed). -/
noncomputable def gidx (a b : ℝ) (N : ℕ) (x : ℝ) : ℕ := min ⌊(x - a) / ((b - a) / N)⌋₊ (N - 1)

/-- The left end of the `i`-th cell. -/
noncomputable def gpt (a b : ℝ) (N : ℕ) (i : ℕ) : ℝ := a + i * ((b - a) / N)

omit k in
lemma measurable_gidx (a b : ℝ) (N : ℕ) : Measurable (gidx a b N) := by
  have h : Measurable fun x : ℝ => ⌊(x - a) / ((b - a) / N)⌋₊ :=
    Nat.measurable_floor.comp ((measurable_id.sub_const a).div_const _)
  exact (measurable_from_top (f := fun m : ℕ => min m (N - 1))).comp h

omit k in
lemma gidx_lt {N : ℕ} (hN : 0 < N) (x : ℝ) : gidx a b N x < N :=
  (min_le_right _ _).trans_lt (Nat.sub_lt hN one_pos)

omit k in
lemma gpt_mem (hab : a < b) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) : gpt a b N i ∈ Icc a b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < (b - a) / N := div_pos (by linarith) hN'
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  refine ⟨by unfold gpt; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩
  unfold gpt
  have : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
  nlinarith

omit k in
lemma abs_sub_gpt_le (hab : a < b) {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Icc a b) :
    |x - gpt a b N (gidx a b N x)| ≤ (b - a) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (b - a) / N with hhdef
  have hh : 0 < h := div_pos (by linarith) hN'
  have hNh : (N : ℝ) * h = b - a := by rw [hhdef]; field_simp
  set y := (x - a) / h with hy
  have y0 : 0 ≤ y := div_nonneg (by linarith [hx.1]) hh.le
  have yN : y ≤ N := by rw [hy, div_le_iff₀ hh]; linarith [hx.2]
  have hxy : x = a + y * h := by rw [hy]; field_simp; ring
  have f1 := Nat.floor_le y0
  have f2 := Nat.lt_floor_add_one y
  unfold gidx gpt
  rw [← hhdef, ← hy]
  rcases le_total ⌊y⌋₊ (N - 1) with hm | hm
  · rw [min_eq_left hm, hxy, abs_le]
    constructor <;> nlinarith
  · rw [min_eq_right hm, hxy, abs_le]
    have hfN : (⌊y⌋₊ : ℝ) ≤ N := by
      exact_mod_cast (Nat.floor_le_floor yN).trans (by simp)
    have hcast : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN]; simp
    have hm' : (N : ℝ) - 1 ≤ ⌊y⌋₊ := by rw [← hcast]; exact_mod_cast hm
    rw [hcast]
    constructor <;> nlinarith

/-- The cell `{x | gidx x = i}` is measurable. -/
lemma measurableSet_cell (a b : ℝ) (N i : ℕ) : MeasurableSet (gidx a b N ⁻¹' {i}) :=
  measurable_gidx a b N (measurableSet_singleton i)

variable (ν) in
/-- The finite-rank approximation `f ↦ (x ↦ ⟪K(gpt (gidx x), ·), f⟫)`. -/
noncomputable def approx (a b : ℝ) (N : ℕ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ∑ i ∈ Finset.range N, rankOne (k.sec ν (gpt a b N i))
    (indicatorConstLp 2 (measurableSet_cell a b N i) (measure_ne_top ν _) (1 : ℝ))

lemma isCompactOperator_approx (a b : ℝ) (N : ℕ) : IsCompactOperator (k.approx ν a b N) :=
  isCompactOperator_sum _ _ fun _ _ => isCompactOperator_rankOne _ _

lemma approx_apply_ae {N : ℕ} (hN : 0 < N) (f : Lp ℝ 2 ν) :
    k.approx ν a b N f =ᵐ[ν] fun x => ⟪k.sec ν (gpt a b N (gidx a b N x)), f⟫ := by
  have hs := coeFn_finset_sum (Finset.range N) fun i => rankOne (k.sec ν (gpt a b N i))
    (indicatorConstLp 2 (measurableSet_cell a b N i) (measure_ne_top ν _) (1 : ℝ)) f
  have hi : ∀ᵐ x ∂ν, ∀ i : ℕ, (rankOne (k.sec ν (gpt a b N i))
      (indicatorConstLp 2 (measurableSet_cell a b N i) (measure_ne_top ν _) (1 : ℝ)) f) x
      = ⟪k.sec ν (gpt a b N i), f⟫ * (gidx a b N ⁻¹' {i}).indicator (fun _ => (1 : ℝ)) x := by
    rw [ae_all_iff]
    intro i
    rw [rankOne_apply]
    filter_upwards [Lp.coeFn_smul ⟪k.sec ν (gpt a b N i), f⟫
      (indicatorConstLp 2 (measurableSet_cell a b N i) (measure_ne_top ν _) (1 : ℝ)),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_cell a b N i) (hμs := measure_ne_top ν _)
        (c := (1 : ℝ))] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [hs, hi] with x h1 h2
  simp only [approx, sum_apply]
  rw [h1]
  simp only [h2]
  rw [Finset.sum_eq_single (gidx a b N x)]
  · simp
  · intro j _ hj
    simp [Set.indicator, Ne.symm hj]
  · intro h; exact absurd (Finset.mem_range.2 (gidx_lt hN x)) h

lemma norm_op_sub_approx_le (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x ∈ Icc a b, ‖k.sec ν x - k.sec ν (gpt a b N (gidx a b N x))‖ ≤ η) :
    ‖k.op ν hν - k.approx ν a b N‖ ≤ cν ν * η := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg cν_nonneg hη) fun f => ?_
  rw [mul_assoc]
  refine norm_le_of_ae_bound' (mul_nonneg hη (norm_nonneg _)) ?_
  filter_upwards [hν, lpOp_apply_ae (k.sec ν) (k.continuous_sec hν).stronglyMeasurable (cν ν * k.M)
    k.norm_sec_le f, k.approx_apply_ae hN f,
    Lp.coeFn_sub (k.op ν hν f) (k.approx ν a b N f)] with x hx h1 h2 h3
  rw [sub_apply, h3, Pi.sub_apply, op, h1, h2, ← inner_sub_left,
    Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (h x hx) (norm_nonneg _))

/-- **An integral operator with a continuous kernel is compact on `L²(ν)`** (`ν` finite, carried by
`[a, b]`). -/
theorem isCompactOperator_op (hab : a < b) (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) :
    IsCompactOperator (k.op ν hν) := by
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun N => k.approx ν a b N) ?_
    (Eventually.of_forall fun N => k.isCompactOperator_approx a b N)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc := cν_nonneg (ν := ν)
  set η := ε / (2 * (cν ν + 1)) with hηdef
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hδ'⟩ := k.sec_unif hν (isCompact_Icc (a := a) (b := b)) hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  have hN₀pos : 0 < N₀ := by
    have : (0 : ℝ) < N₀ := lt_of_le_of_lt (div_nonneg (by linarith) hδ.le) hN₀
    exact_mod_cast this
  refine ⟨N₀, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le hN₀pos hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hgrid : (b - a) / N < δ := by
    rw [div_lt_iff₀ hNr]
    have h1 : (b - a) / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
    rw [div_lt_iff₀ hδ] at h1
    linarith
  rw [dist_eq_norm, norm_sub_rev]
  refine lt_of_le_of_lt (k.norm_op_sub_approx_le hν hNpos hη.le fun x hx => ?_) ?_
  · exact hδ' x hx _ (gpt_mem hab hNpos (gidx_lt hNpos x))
      ((abs_sub_gpt_le hab hNpos hx).trans_lt hgrid)
  · rw [hηdef, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-- **A symmetric continuous kernel gives a symmetric operator.** -/
theorem isSymmetric_op (hν : ∀ᵐ t ∂ν, t ∈ Icc a b) (hsym : ∀ x t, k.K x t = k.K t x) :
    (k.op ν hν : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν).IsSymmetric := by
  intro f g
  have hf : Integrable f ν := (Lp.memLp f).integrable one_le_two
  have hg : Integrable g ν := (Lp.memLp g).integrable one_le_two
  have hK : AEStronglyMeasurable (fun z : ℝ × ℝ => k.K z.1 z.2) (ν.prod ν) :=
    k.cont.aestronglyMeasurable
  have hint : Integrable (fun z : ℝ × ℝ => k.K z.1 z.2 * (g z.1 * f z.2)) (ν.prod ν) :=
    (hg.mul_prod hf).bdd_mul hK (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact k.bound _ _)
  have e1 : ⟪(k.op ν hν : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν) f, g⟫
      = ∫ x, ∫ t, k.K x t * (g x * f t) ∂ν ∂ν := by
    rw [ContinuousLinearMap.coe_coe, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [k.op_apply_ae hν f] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, ← integral_const_mul]
    congr 1; funext t; ring
  have e2 : ⟪f, (k.op ν hν : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν) g⟫
      = ∫ t, ∫ x, k.K x t * (g x * f t) ∂ν ∂ν := by
    rw [ContinuousLinearMap.coe_coe, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [k.op_apply_ae hν g] with t ht
    rw [ht]
    simp only [RCLike.inner_apply, conj_trivial, ← integral_mul_const]
    congr 1; funext x; rw [hsym x t]; ring
  rw [e1, e2]
  exact integral_integral_swap hint

end Kernel

end KernelOp

end UndergradKB.DifferentialEquations
