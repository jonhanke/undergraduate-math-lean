import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import UndergradKB.Common.Attr
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.LimitTheorems
import UndergradKB.Probability.Moments
import UndergradKB.Probability.Transforms

/-! # Probability: worked examples on continuous conditioning and Chebyshev's inequality

Examples 4.18, 4.19, 4.21 (spinner and dart conditioning), 8.1 and 8.4 (Chebyshev in standard
deviations), 8.5 and 8.6 (laws of large numbers for uniform and normal samples), 8.7 (Monte Carlo
integration) and 9.9 (the surveyor). -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval Real

namespace UndergradKB.Probability

/-! ## Examples 4.18, 4.19 and 4.21 (PR-174) -/

section Conditioning

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Example 4.18 (PR-174). For a (measurable) spinner `X` uniform on `[0,1]`, given
that it stops in `[0, 1/2]`, the probability that it lies in `[1/6, 1/3]` is `1/3`. -/
@[kb "grinsteadsnell2006" "Example 4.18, p. 170"]
theorem spinner_conditional {X : Ω → ℝ} (hXm : Measurable X)
    (hX : pdf.IsUniform X (Icc (0 : ℝ) 1) P) :
    (P[X ⁻¹' Icc (1 / 6 : ℝ) (1 / 3) | X ⁻¹' Icc (0 : ℝ) (1 / 2)]).toReal = 1 / 3 := by
  have hm : P.map X = volume.restrict (Icc 0 1) := by rw [hX.map_eq, cond_Icc_zero_one]
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → P.real (X ⁻¹' Icc a b) = b - a := by
    intro a b ha hab hb
    rw [measureReal_def, ← Measure.map_apply hXm measurableSet_Icc,
      hm, Measure.restrict_apply measurableSet_Icc,
      inter_eq_left.2 (Icc_subset_Icc ha hb)]
    simp [hab]
  have hinter : X ⁻¹' Icc (0 : ℝ) (1 / 2) ∩ X ⁻¹' Icc (1 / 6 : ℝ) (1 / 3) =
      X ⁻¹' Icc (1 / 6 : ℝ) (1 / 3) := by
    rw [← preimage_inter, inter_eq_right.2]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  rw [cond_apply (hXm measurableSet_Icc), hinter, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def, ← measureReal_def, key _ _ (by norm_num) (by norm_num) (by norm_num),
    key _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end Conditioning

section Disk

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The reflection of the plane changing the sign of coordinate `i`. -/
noncomputable def reflect (i : Fin 2) : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin 2 => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma reflect_apply_self (i : Fin 2) (y : Plane) : reflect i y i = -(y i) := by
  simp [reflect]

lemma reflect_apply_ne {i j : Fin 2} (h : j ≠ i) (y : Plane) : reflect i y j = y j := by
  simp [reflect, h]

lemma reflect_measurePreserving (i : Fin 2) :
    MeasurePreserving (reflect i) (volume : Measure Plane) volume :=
  (reflect i).measurePreserving

lemma measurableSet_coord_nonneg (i : Fin 2) : MeasurableSet {y : Plane | 0 ≤ y i} :=
  (isClosed_le continuous_const (by fun_prop)).measurableSet

lemma volume_coord_zero (i : Fin 2) : (volume : Measure Plane) {y : Plane | y i = 0} = 0 := by
  have : {y : Plane | y i = 0} = (LinearMap.ker
      ((EuclideanSpace.proj i : StrongDual ℝ Plane) : Plane →ₗ[ℝ] ℝ) : Submodule ℝ Plane) := by
    ext y; simp
  rw [this]
  refine Measure.addHaar_submodule _ _ ?_
  intro h
  have h1 : (EuclideanSpace.single i (1 : ℝ) : Plane) ∈ LinearMap.ker
      ((EuclideanSpace.proj i : StrongDual ℝ Plane) : Plane →ₗ[ℝ] ℝ) := by rw [h]; trivial
  simp at h1

/-- A set symmetric under the reflection in coordinate `i` has half its area in `{y i ≥ 0}`. -/
lemma two_mul_volume_half {S : Set Plane} (hS : MeasurableSet S) (i : Fin 2)
    (hsym : reflect i ⁻¹' S = S) :
    2 * volume (S ∩ {y : Plane | 0 ≤ y i}) = volume S := by
  have hpos : MeasurableSet {y : Plane | 0 < y i} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hneg : MeasurableSet {y : Plane | y i < 0} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hz : MeasurableSet {y : Plane | y i = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hS' : ∀ y, reflect i y ∈ S ↔ y ∈ S := fun y => by rw [← mem_preimage, hsym]
  have h1 : volume (S ∩ {y : Plane | y i < 0}) = volume (S ∩ {y : Plane | 0 < y i}) := by
    have : S ∩ {y : Plane | y i < 0} = reflect i ⁻¹' (S ∩ {y : Plane | 0 < y i}) := by
      ext y
      simp only [mem_inter_iff, mem_preimage, hS', reflect_apply_self, mem_ofPred_eq, neg_pos]
    rw [this, (reflect_measurePreserving i).measure_preimage (hS.inter hpos).nullMeasurableSet]
  have h2 : volume (S ∩ {y : Plane | 0 ≤ y i}) = volume (S ∩ {y : Plane | 0 < y i}) := by
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ fun y hy => le_of_lt (show 0 < y i from hy)))
    calc volume (S ∩ {y : Plane | 0 ≤ y i})
        ≤ volume ((S ∩ {y : Plane | 0 < y i}) ∪ {y : Plane | y i = 0}) := by
          refine measure_mono fun y hy => ?_
          rcases (show 0 ≤ y i from hy.2).lt_or_eq with h | h
          · exact Or.inl ⟨hy.1, h⟩
          · exact Or.inr h.symm
      _ ≤ volume (S ∩ {y : Plane | 0 < y i}) + volume {y : Plane | y i = 0} :=
          measure_union_le _ _
      _ = _ := by rw [volume_coord_zero, add_zero]
  have h3 := measure_inter_add_sdiff (μ := volume) S (measurableSet_coord_nonneg i)
  have h4 : S \ {y : Plane | 0 ≤ y i} = S ∩ {y : Plane | y i < 0} := by
    ext y; simp only [mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_le]
  rw [h4, h1, ← h2] at h3
  rw [two_mul]
  exact h3

lemma reflect_preimage_ball (i : Fin 2) (r : ℝ) :
    reflect i ⁻¹' Metric.ball (0 : Plane) r = Metric.ball 0 r := by
  ext y; simp

lemma reflect_preimage_coord_nonneg {i j : Fin 2} (h : j ≠ i) :
    reflect i ⁻¹' {y : Plane | 0 ≤ y j} = {y : Plane | 0 ≤ y j} := by
  ext y; simp [reflect_apply_ne h]

lemma toReal_volume_half {S : Set Plane} (hS : MeasurableSet S) (i : Fin 2)
    (hsym : reflect i ⁻¹' S = S) :
    (volume (S ∩ {y : Plane | 0 ≤ y i})).toReal = (volume S).toReal / 2 := by
  have h := congrArg ENNReal.toReal (two_mul_volume_half hS i hsym)
  rw [ENNReal.toReal_mul] at h
  simp only [ENNReal.toReal_ofNat] at h
  linarith

lemma volume_ball_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : Plane) r)).toReal = r ^ 2 * π := by
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Plane}

/-- Probability for a uniform point of the unit disk: normalized area. -/
lemma disk_real (hXm : Measurable X) (hX : pdf.IsUniform X (Metric.ball 0 1) P) {A : Set Plane}
    (hA : MeasurableSet A) :
    P.real (X ⁻¹' A) = (volume (Metric.ball (0 : Plane) 1 ∩ A)).toReal / π := by
  rw [measureReal_def, ← Measure.map_apply hXm hA, hX.map_eq,
    cond_apply Metric.isOpen_ball.measurableSet, ENNReal.toReal_mul, ENNReal.toReal_inv,
    volume_ball_toReal 1 zero_le_one]
  simp [div_eq_inv_mul]

/-- Grinstead–Snell Example 4.19 (PR-174). For a dart `X` uniform on the unit disk, given that it
lands in the upper half `y ≥ 0`, the probability that its distance from the centre is less than
`1/2` is `1/4`. -/
@[kb "grinsteadsnell2006" "Example 4.19, p. 171"]
theorem dart_conditional_upper_half (hXm : Measurable X)
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) :
    (P[X ⁻¹' Metric.ball (0 : Plane) (1 / 2) | X ⁻¹' {y : Plane | 0 ≤ y 1}]).toReal = 1 / 4 := by
  have hE := measurableSet_coord_nonneg (1 : Fin 2)
  have hD : MeasurableSet (Metric.ball (0 : Plane) (1 / 2)) := Metric.isOpen_ball.measurableSet
  have hPE : P.real (X ⁻¹' {y : Plane | 0 ≤ y 1}) = 1 / 2 := by
    rw [disk_real hXm hX hE, toReal_volume_half Metric.isOpen_ball.measurableSet 1
      (reflect_preimage_ball 1 1), volume_ball_toReal 1 zero_le_one]
    field_simp
  have hPDE : P.real (X ⁻¹' {y : Plane | 0 ≤ y 1} ∩ X ⁻¹' Metric.ball (0 : Plane) (1 / 2)) =
      1 / 8 := by
    rw [← preimage_inter, disk_real hXm hX (hE.inter hD)]
    have : Metric.ball (0 : Plane) 1 ∩ ({y : Plane | 0 ≤ y 1} ∩ Metric.ball 0 (1 / 2)) =
        Metric.ball 0 (1 / 2) ∩ {y : Plane | 0 ≤ y 1} := by
      rw [inter_comm {y : Plane | 0 ≤ y 1}, ← inter_assoc,
        inter_eq_right.2 (Metric.ball_subset_ball (by norm_num))]
    rw [this, toReal_volume_half hD 1 (reflect_preimage_ball 1 _),
      volume_ball_toReal _ (by norm_num)]
    field_simp
    norm_num
  rw [cond_apply (hXm hE), ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def,
    ← measureReal_def, hPE, hPDE]
  norm_num

/-- Grinstead–Snell Example 4.21 (PR-174). For a dart `X` uniform on the unit disk, the events
"upper half" (`y ≥ 0`) and "right half" (`x ≥ 0`) are independent, each of probability `1/2`, and the
first quadrant has probability `1/4 = (1/2)(1/2)`. -/
@[kb "grinsteadsnell2006" "Example 4.21, p. 172"]
theorem dart_halves_independent (hXm : Measurable X)
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) :
    P.real (X ⁻¹' {y : Plane | 0 ≤ y 1}) = 1 / 2 ∧ P.real (X ⁻¹' {y : Plane | 0 ≤ y 0}) = 1 / 2 ∧
      P.real (X ⁻¹' {y : Plane | 0 ≤ y 1} ∩ X ⁻¹' {y : Plane | 0 ≤ y 0}) = 1 / 4 ∧
      IndepSet (X ⁻¹' {y : Plane | 0 ≤ y 1}) (X ⁻¹' {y : Plane | 0 ≤ y 0}) P := by
  have hball : MeasurableSet (Metric.ball (0 : Plane) 1) := Metric.isOpen_ball.measurableSet
  have hE := measurableSet_coord_nonneg (1 : Fin 2)
  have hF := measurableSet_coord_nonneg (0 : Fin 2)
  have hV := volume_ball_toReal 1 zero_le_one
  have hpi := Real.pi_pos
  have h1 : P.real (X ⁻¹' {y : Plane | 0 ≤ y 1}) = 1 / 2 := by
    rw [disk_real hXm hX hE, toReal_volume_half hball 1 (reflect_preimage_ball 1 1), hV]
    field_simp
  have h2 : P.real (X ⁻¹' {y : Plane | 0 ≤ y 0}) = 1 / 2 := by
    rw [disk_real hXm hX hF, toReal_volume_half hball 0 (reflect_preimage_ball 0 1), hV]
    field_simp
  have h3 : P.real (X ⁻¹' {y : Plane | 0 ≤ y 1} ∩ X ⁻¹' {y : Plane | 0 ≤ y 0}) = 1 / 4 := by
    rw [← preimage_inter, disk_real hXm hX (hE.inter hF)]
    have : Metric.ball (0 : Plane) 1 ∩ ({y : Plane | 0 ≤ y 1} ∩ {y : Plane | 0 ≤ y 0}) =
        (Metric.ball 0 1 ∩ {y : Plane | 0 ≤ y 0}) ∩ {y : Plane | 0 ≤ y 1} := by
      ext y; simp only [mem_inter_iff]; tauto
    rw [this, toReal_volume_half (hball.inter hF) 1
      (by rw [preimage_inter, reflect_preimage_ball, reflect_preimage_coord_nonneg (by decide)]),
      toReal_volume_half hball 0 (reflect_preimage_ball 0 1), hV]
    field_simp
    norm_num
  refine ⟨h1, h2, h3, ?_⟩
  rw [indepSet_iff_measure_inter_eq_mul (hXm hE) (hXm hF) P]
  rw [measureReal_def] at h1 h2 h3
  have fin : ∀ s : Set Ω, P s ≠ ⊤ := fun s => measure_ne_top P s
  have := (ENNReal.toReal_eq_toReal_iff' (fin _) (ENNReal.mul_ne_top (fin _) (fin _))).1
    (show (P (X ⁻¹' {y : Plane | 0 ≤ y 1} ∩ X ⁻¹' {y : Plane | 0 ≤ y 0})).toReal =
      ((P (X ⁻¹' {y : Plane | 0 ≤ y 1})) * P (X ⁻¹' {y : Plane | 0 ≤ y 0})).toReal by
        rw [ENNReal.toReal_mul, h1, h2, h3]; norm_num)
  exact this

end Disk

/-! ## Examples 8.1 and 8.4 (PR-175) -/

section ChebyshevSd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Example 8.1 (PR-175). For a real random variable `X` with finite variance
`σ² > 0` and any `k > 0`, `P(|X - μ| ≥ kσ) ≤ 1/k²`. -/
@[kb "grinsteadsnell2006" "Example 8.1, p. 314"]
theorem chebyshev_standard_deviations {X : Ω → ℝ} (hX : MemLp X 2 P) (hσ : 0 < Var[X; P])
    {k : ℝ} (hk : 0 < k) :
    P.real {ω | k * √(Var[X; P]) ≤ |X ω - P[X]|} ≤ 1 / k ^ 2 := by
  have hs : 0 < √(Var[X; P]) := Real.sqrt_pos.2 hσ
  have h := meas_ge_le_variance_div_sq hX (mul_pos hk hs)
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (le_of_eq ?_))
  congr 1
  rw [mul_pow, Real.sq_sqrt hσ.le]
  field_simp

/-- Grinstead–Snell Example 8.4 (PR-175). The same bound for a continuous random variable (one with a
density with respect to Lebesgue measure): `P(|X - μ| ≥ kσ) ≤ 1/k²`. -/
@[kb "grinsteadsnell2006" "Example 8.4, p. 324"]
theorem chebyshev_standard_deviations_continuous {X : Ω → ℝ} [HasPDF X P volume]
    (hX : MemLp X 2 P) (hσ : 0 < Var[X; P]) {k : ℝ} (hk : 0 < k) :
    P.real {ω | k * √(Var[X; P]) ≤ |X ω - P[X]|} ≤ 1 / k ^ 2 :=
  chebyshev_standard_deviations hX hσ hk

/-- The law putting probability `1/2` on each of `ε` and `-ε`. -/
noncomputable def twoPointLaw (ε : ℝ) : Measure ℝ :=
  bernoulliMeasure ε (-ε) ⟨1 / 2, by constructor <;> norm_num⟩

instance (ε : ℝ) : IsProbabilityMeasure (twoPointLaw ε) := by
  unfold twoPointLaw; infer_instance

lemma twoPointLaw_memLp (ε : ℝ) : MemLp id 2 (twoPointLaw ε) := by
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ?_
  unfold twoPointLaw
  exact integrable_bernoulliMeasure _ _ _ _

lemma twoPointLaw_integral (ε : ℝ) : ∫ x, x ∂(twoPointLaw ε) = 0 := by
  unfold twoPointLaw
  rw [integral_bernoulliMeasure]
  simp
  ring

lemma twoPointLaw_variance (ε : ℝ) : Var[id; twoPointLaw ε] = ε ^ 2 := by
  rw [variance_eq_sub (twoPointLaw_memLp ε)]
  have : ∫ x, (id x) ^ 2 ∂(twoPointLaw ε) = ε ^ 2 := by
    unfold twoPointLaw
    rw [integral_bernoulliMeasure]
    simp only [id]
    simp only [smul_eq_mul, neg_sq]
    ring
  have h2 : ∫ x, id x ∂(twoPointLaw ε) = 0 := twoPointLaw_integral ε
  simp only [Pi.pow_apply] at *
  rw [this, h2]
  norm_num

/-- Grinstead–Snell Example 8.4 (PR-175), sharpness. If `X` takes the values `ε` and `-ε` with
probability `1/2` each (`ε > 0`), then `μ = 0`, `σ² = ε²`, and `P(|X - μ| ≥ ε) = 1 = σ²/ε²`, so
Chebyshev's inequality is an equality. -/
@[kb "grinsteadsnell2006" "Example 8.4, p. 324"]
theorem chebyshev_sharp {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε) (hX : HasLaw X (twoPointLaw ε) P) :
    P[X] = 0 ∧ Var[X; P] = ε ^ 2 ∧ P.real {ω | ε ≤ |X ω - P[X]|} = 1 ∧
      P.real {ω | ε ≤ |X ω - P[X]|} = Var[X; P] / ε ^ 2 := by
  have hm : P[X] = 0 := by rw [hX.integral_eq]; exact twoPointLaw_integral ε
  have hv : Var[X; P] = ε ^ 2 := by rw [hX.variance_eq]; exact twoPointLaw_variance ε
  have h1 : P.real {ω | ε ≤ |X ω - P[X]|} = 1 := by
    rw [hm]
    have hS : MeasurableSet {x : ℝ | ε ≤ |x - 0|} :=
      (isClosed_le continuous_const (by fun_prop)).measurableSet
    rw [hX.measureReal_eq (p := fun x => ε ≤ |x - 0|) hS, measureReal_def]
    unfold twoPointLaw
    rw [bernoulliMeasure_apply_of_mem_of_mem _ hS (by simp [abs_of_pos hε]) (by simp [abs_of_pos hε])]
    simp
  refine ⟨hm, hv, h1, ?_⟩
  rw [h1, hv]
  field_simp

end ChebyshevSd

/-! ## Examples 8.5 and 8.6 (PR-176) -/

section Samples

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma uniform_hasLaw {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P) :
    HasLaw Y (volume.restrict (Icc (0 : ℝ) 1)) P :=
  ⟨h.aemeasurable, by rw [h.map_eq, cond_Icc_zero_one]⟩

lemma memLp_id_uniform_Icc : MemLp id 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  refine MemLp.of_bound aestronglyMeasurable_id 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [id, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩

/-- Grinstead–Snell Example 8.5 (PR-176). For `n ≥ 1` independent numbers `X i` chosen uniformly in
`[0,1]`, the average `S_n/n` has mean `1/2` and variance `1/(12n)`, and for every `ε > 0`,
`P(|S_n/n - 1/2| ≥ ε) ≤ 1/(12 n ε²)`. -/
@[kb "grinsteadsnell2006" "Example 8.5, p. 325"]
theorem uniform_samples_chebyshev {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, pdf.IsUniform (X i) (Icc (0 : ℝ) 1) P) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i] = 1 / 2 ∧
      Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P] = 1 / (12 * n) ∧
      P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1 / 2|} ≤ 1 / (12 * n * ε ^ 2) := by
  have hL : ∀ i, MemLp (X i) 2 P := fun i => (uniform_hasLaw (hX i)).memLp memLp_id_uniform_Icc
  have hμ : ∀ i, P[X i] = 1 / 2 := fun i => integral_of_isUniform_Icc (hX i)
  have hσ : ∀ i, Var[X i; P] = 1 / 12 := fun i => variance_of_isUniform_Icc (hX i)
  have hnR : (n : ℝ) ≠ 0 := by positivity
  obtain ⟨h1, h2⟩ := average_mean_variance hind hL hμ hσ hn
  refine ⟨h1, by rw [h2]; field_simp, ?_⟩
  have h := weak_law_chebyshev_bound hL (fun _ _ hij => hind.indepFun hij) hμ hσ hn hε
  convert h using 1
  field_simp

/-- Grinstead–Snell Example 8.6 (PR-176). For `n ≥ 1` independent standard normal samples `X i`, the
average `S_n/n` has mean `0` and variance `1/n`, and for every `ε > 0`,
`P(|S_n/n - 0| ≥ ε) ≤ 1/(n ε²)`. -/
@[kb "grinsteadsnell2006" "Example 8.6, p. 326"]
theorem normal_samples_chebyshev {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i] = 0 ∧
      Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P] = 1 / n ∧
      P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 0|} ≤ 1 / (n * ε ^ 2) := by
  have hL : ∀ i, MemLp (X i) 2 P := fun i => (hX i).memLp (memLp_id_gaussianReal 2)
  have hμ : ∀ i, P[X i] = 0 := fun i => by rw [(hX i).integral_eq, integral_id_gaussianReal]
  have hσ : ∀ i, Var[X i; P] = 1 := fun i => by
    rw [(hX i).variance_eq, variance_id_gaussianReal]; simp
  obtain ⟨h1, h2⟩ := average_mean_variance hind hL hμ hσ hn
  refine ⟨h1, by rw [h2], ?_⟩
  exact weak_law_chebyshev_bound hL (fun _ _ hij => hind.indepFun hij) hμ hσ hn hε

end Samples

/-! ## Example 8.7 (PR-177) -/

section MonteCarlo

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : ℝ → ℝ}

lemma uniform_ae_mem {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P) :
    ∀ᵐ ω ∂P, Y ω ∈ Icc (0 : ℝ) 1 := by
  have hl := uniform_hasLaw h
  refine (ae_map_iff h.aemeasurable measurableSet_Icc).1 ?_
  rw [hl.map_eq]
  exact ae_restrict_mem measurableSet_Icc

lemma monte_carlo_aesm {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) : AEStronglyMeasurable (fun ω => g (Y ω)) P := by
  have hl := uniform_hasLaw h
  have : AEStronglyMeasurable g (P.map Y) := by
    rw [hl.map_eq]; exact hg.aestronglyMeasurable measurableSet_Icc
  exact this.comp_aemeasurable h.aemeasurable

lemma monte_carlo_memLp {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) (hgI : ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ Icc (0 : ℝ) 1) :
    MemLp (fun ω => g (Y ω)) 2 P := by
  refine MemLp.of_bound (monte_carlo_aesm h hg) 1 ?_
  filter_upwards [uniform_ae_mem h] with ω hω
  have := hgI _ hω
  simp only [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [this.1], this.2⟩

lemma monte_carlo_mean {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) : ∫ ω, g (Y ω) ∂P = ∫ x in (0 : ℝ)..1, g x := by
  have hl := uniform_hasLaw h
  have := hl.integral_comp (f := g) (by exact hg.aestronglyMeasurable measurableSet_Icc)
  simp only [Function.comp_def] at this
  rw [this, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

lemma monte_carlo_var_le {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) (hgI : ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ Icc (0 : ℝ) 1) :
    Var[fun ω => g (Y ω); P] ≤ 1 / 4 := by
  have := variance_le_sq_of_bounded (μ := P) (a := 0) (b := 1) (X := fun ω => g (Y ω))
    (by filter_upwards [uniform_ae_mem h] with ω hω using hgI _ hω)
    (monte_carlo_aesm h hg).aemeasurable
  norm_num at this
  linarith

/-- Grinstead–Snell Example 8.7 (PR-177). Let `g` be continuous on `[0,1]` with values in `[0,1]` and
`X` uniform on `[0,1]`. Then `Y = g(X)` has mean `∫₀¹ g`, and its variance is `< 1` (indeed `≤ 1/4`). -/
@[kb "grinsteadsnell2006" "Example 8.7, p. 327"]
theorem monte_carlo_mean_variance {Y : Ω → ℝ} (h : pdf.IsUniform Y (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) (hgI : ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ Icc (0 : ℝ) 1) :
    P[fun ω => g (Y ω)] = ∫ x in (0 : ℝ)..1, g x ∧ Var[fun ω => g (Y ω); P] < 1 ∧
      Var[fun ω => g (Y ω); P] ≤ 1 / 4 :=
  ⟨monte_carlo_mean h hg, lt_of_le_of_lt (monte_carlo_var_le h hg hgI) (by norm_num),
    monte_carlo_var_le h hg hgI⟩

/-- Grinstead–Snell Example 8.7 (PR-177), the Chebyshev estimate. For `X i` independent and uniform on
`[0,1]`, `g` continuous on `[0,1]` with values in `[0,1]`, and `n ≥ 1`, the average of the `g (X k)`
is within `ε` of `∫₀¹ g` except with probability at most `σ²/(n ε²) ≤ 1/(4 n ε²) < 1/(n ε²)`;
we state the final bound `P(|A_n - ∫₀¹ g| ≥ ε) ≤ 1/(n ε²)` together with the sharper `1/(4 n ε²)`. -/
@[kb "grinsteadsnell2006" "Example 8.7, p. 327"]
theorem monte_carlo_chebyshev {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, pdf.IsUniform (X i) (Icc (0 : ℝ) 1) P)
    (hg : ContinuousOn g (Icc 0 1)) (hgI : ∀ x ∈ Icc (0 : ℝ) 1, g x ∈ Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, g (X k ω)) / n - ∫ x in (0 : ℝ)..1, g x|} ≤
        1 / (4 * n * ε ^ 2) ∧
      P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, g (X k ω)) / n - ∫ x in (0 : ℝ)..1, g x|} ≤
        1 / (n * ε ^ 2) := by
  -- replace `g` by a continuous function `G` agreeing with it on `[0,1]`
  set G : ℝ → ℝ := fun x => g (max 0 (min 1 x)) with hG
  have hcl : Continuous fun x : ℝ => max 0 (min 1 x) := by fun_prop
  have hGc : Continuous G :=
    hg.comp_continuous hcl (fun x => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩)
  have hGI : ∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc (0 : ℝ) 1 := fun x hx => hgI _
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hGg : ∀ x ∈ Icc (0 : ℝ) 1, G x = g x := fun x hx => by
    simp only [hG]; rw [min_eq_right hx.2, max_eq_right hx.1]
  have hint : ∫ x in (0 : ℝ)..1, G x = ∫ x in (0 : ℝ)..1, g x := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le zero_le_one] at hx
    exact hGg x hx
  have hY : ∀ i, MemLp (fun ω => G (X i ω)) 2 P := fun i =>
    monte_carlo_memLp (hX i) hGc.continuousOn hGI
  have hYind : iIndepFun (fun i ω => G (X i ω)) P :=
    hind.comp (fun _ => G) (fun _ => hGc.measurable)
  have hμ : ∀ i, P[fun ω => G (X i ω)] = ∫ x in (0 : ℝ)..1, g x := fun i => by
    rw [monte_carlo_mean (hX i) hGc.continuousOn, hint]
  have hlawG : HasLaw G ((volume.restrict (Icc (0 : ℝ) 1)).map G)
      (volume.restrict (Icc (0 : ℝ) 1)) := ⟨hGc.aemeasurable, rfl⟩
  have hσ : ∀ i, Var[fun ω => G (X i ω); P] =
      Var[id; (volume.restrict (Icc (0 : ℝ) 1)).map G] := fun i =>
    (hlawG.fun_comp (uniform_hasLaw (hX i))).variance_eq
  have key := weak_law_chebyshev_bound (X := fun i ω => G (X i ω)) hY
    (fun _ _ hij => hYind.indepFun hij) hμ hσ hn hε
  have hae : ∀ᵐ ω ∂P, ∀ k, X k ω ∈ Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun k => uniform_ae_mem (hX k)
  have hset : {ω | ε ≤ |(∑ k ∈ Finset.range n, g (X k ω)) / n - ∫ x in (0 : ℝ)..1, g x|} =ᵐ[P]
      {ω | ε ≤ |(∑ k ∈ Finset.range n, G (X k ω)) / n - ∫ x in (0 : ℝ)..1, g x|} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with ω hω
    have : ∑ k ∈ Finset.range n, g (X k ω) = ∑ k ∈ Finset.range n, G (X k ω) :=
      Finset.sum_congr rfl fun k _ => (hGg _ (hω k)).symm
    simp only [mem_ofPred_eq, this]
  rw [measureReal_congr hset]
  have hv : Var[id; (volume.restrict (Icc (0 : ℝ) 1)).map G] ≤ 1 / 4 := by
    rw [← hσ 0]; exact monte_carlo_var_le (hX 0) hGc.continuousOn hGI
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfin : Var[id; (volume.restrict (Icc (0 : ℝ) 1)).map G] / (n * ε ^ 2) ≤
      1 / (4 * n * ε ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hnR (pow_pos hε 2)]
  have hfin2 : 1 / (4 * (n : ℝ) * ε ^ 2) ≤ 1 / (n * ε ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_pos hnR (pow_pos hε 2)]
  exact ⟨key.trans hfin, (key.trans hfin).trans hfin2⟩

end MonteCarlo

/-! ## Example 9.9 (PR-178) -/

section Surveyor

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Example 9.9 (PR-178). The surveyor's independent measurements `X i` have mean `1`
and standard deviation `.0002`. For `n ≥ 1`, the average `S_n/n` differs from `1` by `.0001` or more
with probability at most `4/n`; in particular for `n ≥ 80` this probability is at most `1/20`, so the
error is less than `.0001` with probability at least `.95`. -/
@[kb "grinsteadsnell2006" "Example 9.9, p. 366"]
theorem surveyor_chebyshev {X : ℕ → Ω → ℝ} (hL : ∀ i, MemLp (X i) 2 P) (hind : iIndepFun X P)
    (hμ : ∀ i, P[X i] = 1) (hσ : ∀ i, √(Var[X i; P]) = 2 / 10000) {n : ℕ} (hn : 0 < n) :
    P.real {ω | 1 / 10000 ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1|} ≤ 4 / n ∧
      (80 ≤ n → P.real {ω | 1 / 10000 ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1|} ≤ 1 / 20) ∧
      (80 ≤ n → 19 / 20 ≤
        P.real {ω | |(∑ k ∈ Finset.range n, X k ω) / n - 1| < 1 / 10000}) := by
  have hv : ∀ i, Var[X i; P] = (2 / 10000) ^ 2 := fun i => by
    rw [← hσ i, Real.sq_sqrt (variance_nonneg _ _)]
  have h := weak_law_chebyshev_bound hL (fun _ _ hij => hind.indepFun hij) hμ hv hn
    (ε := 1 / 10000) (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : (2 / 10000 : ℝ) ^ 2 / (n * (1 / 10000) ^ 2) = 4 / n := by
    field_simp; norm_num
  rw [h4] at h
  have h80 : 80 ≤ n → P.real {ω | 1 / 10000 ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1|} ≤ 1 / 20 := by
    intro h80
    refine h.trans ?_
    rw [div_le_div_iff₀ hnR (by norm_num)]
    have : (80 : ℝ) ≤ n := by exact_mod_cast h80
    linarith
  refine ⟨h, h80, fun h80' => ?_⟩
  have hc : {ω | |(∑ k ∈ Finset.range n, X k ω) / n - 1| < 1 / 10000} =
      {ω | 1 / 10000 ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1|}ᶜ := by
    ext ω; simp
  have hS : AEMeasurable (fun ω => (∑ k ∈ Finset.range n, X k ω) / n - 1) P := by
    have := (memLp_finsetSum' (Finset.range n) (fun i _ => hL i)).aestronglyMeasurable.aemeasurable
    have e : (∑ i ∈ Finset.range n, X i) = fun ω => ∑ k ∈ Finset.range n, X k ω := by
      funext ω; simp
    rw [e] at this
    exact (this.div_const _).sub_const _
  have hmeas : NullMeasurableSet {ω | 1 / 10000 ≤ |(∑ k ∈ Finset.range n, X k ω) / n - 1|} P :=
    (hS.nullMeasurableSet_preimage (s := {x : ℝ | 1 / 10000 ≤ |x|})
      (isClosed_le continuous_const continuous_abs).measurableSet)
  rw [hc, probReal_compl_eq_one_sub₀ hmeas]
  linarith [h80 h80']

end Surveyor

end UndergradKB.Probability
