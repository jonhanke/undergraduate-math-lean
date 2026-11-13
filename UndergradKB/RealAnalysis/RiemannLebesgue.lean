import UndergradKB.RealAnalysis.Darboux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import UndergradKB.Common.Attr

/-!
# The Riemann (Darboux) integral agrees with Mathlib's interval integral

For a Riemann integrable `f` on `[a, b]` (in the Darboux sense of Lebl, *Basic Analysis I*, Definition 5.1.9, as
ported from ReasBook in `UndergradKB.RealAnalysis.Darboux`), `f` is interval integrable in Mathlib's (Lebesgue)
sense and `∫_a^b f` (Darboux) equals `∫ x in a..b, f x`. Neither Mathlib nor ReasBook states this; it lets every
theorem of Mathlib about the interval integral (fundamental theorem of calculus, change of variables, ...) be used
for the book's integral.

Proof: for a partition `P`, the step functions equal to the infimum (supremum) of `f` on each piece `(x_{i-1}, x_i]`
lie below (above) `f` on `(a, b]` and integrate to `L(P, f)` (`U(P, f)`). Taking partitions with
`U - L < 1/(k+1)`, the supremum `g` of the lower and the infimum `h` of the upper step functions are measurable,
`g ≤ f ≤ h` on `(a, b]` and `∫ (h - g) = 0`, so `f = g` almost everywhere: `f` is integrable, and its integral lies
between `L(P, f)` and `U(P, f)` for every such `P`, hence equals the Darboux integral.

Also: the converse of Lebl's Proposition 5.1.13 (a Riemann integrable function has partitions with arbitrarily small
`U - L`), which the book uses throughout section 5.2.
-/

open MeasureTheory Set Filter Topology

namespace UndergradKB.RealAnalysis

variable {a b : ℝ}

/-! ## Partitions: the half-open pieces `(x_{i-1}, x_i]` -/

/-- The `i`-th half-open piece `(x_{i-1}, x_i]` of a partition. -/
def IntervalPartition.piece (P : IntervalPartition a b) (i : Fin P.n) : Set ℝ :=
  Ioc (P.points i.castSucc) (P.points i.succ)

lemma IntervalPartition.points_last (P : IntervalPartition a b) : P.points (Fin.last P.n) = b :=
  P.right_eq

lemma IntervalPartition.a_le_points (P : IntervalPartition a b) (j : Fin (P.n + 1)) : a ≤ P.points j :=
  by have h := P.mono.monotone (Fin.zero_le j); rwa [P.left_eq] at h

lemma IntervalPartition.points_le_b (P : IntervalPartition a b) (j : Fin (P.n + 1)) : P.points j ≤ b :=
  by have h := P.mono.monotone (Fin.le_last j); rwa [P.points_last] at h

lemma IntervalPartition.piece_subset (P : IntervalPartition a b) (i : Fin P.n) : P.piece i ⊆ Ioc a b :=
  Ioc_subset_Ioc (P.a_le_points _) (P.points_le_b _)

lemma IntervalPartition.Icc_piece_subset (P : IntervalPartition a b) (i : Fin P.n) :
    Icc (P.points i.castSucc) (P.points i.succ) ⊆ Icc a b :=
  Icc_subset_Icc (P.a_le_points _) (P.points_le_b _)

lemma IntervalPartition.not_mem_piece_of_ne (P : IntervalPartition a b) {i j : Fin P.n} (hij : i ≠ j) {x : ℝ}
    (hi : x ∈ P.piece i) : x ∉ P.piece j := by
  intro hj
  rcases lt_or_gt_of_ne hij with h | h
  · have : P.points i.succ ≤ P.points j.castSucc := P.mono.monotone (Fin.succ_le_castSucc_iff.2 h)
    exact lt_irrefl x (lt_of_le_of_lt (hi.2.trans this) hj.1)
  · have : P.points j.succ ≤ P.points i.castSucc := P.mono.monotone (Fin.succ_le_castSucc_iff.2 h)
    exact lt_irrefl x (lt_of_le_of_lt (hj.2.trans this) hi.1)

lemma IntervalPartition.exists_mem_piece (P : IntervalPartition a b) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ i, x ∈ P.piece i := by
  classical
  let S : Finset (Fin (P.n + 1)) := Finset.univ.filter (fun j => P.points j < x)
  have h0 : (0 : Fin (P.n + 1)) ∈ S := by simp [S, P.left_eq, hx.1]
  let j := S.max' ⟨0, h0⟩
  have hjS : j ∈ S := S.max'_mem _
  have hjx : P.points j < x := (Finset.mem_filter.1 hjS).2
  have hjlast : j ≠ Fin.last P.n := by
    intro h
    rw [h, P.points_last] at hjx
    exact absurd hx.2 (not_le.2 hjx)
  refine ⟨j.castPred hjlast, ?_, ?_⟩
  · simpa using hjx
  · by_contra hlt
    push Not at hlt
    have hmem : (j.castPred hjlast).succ ∈ S := by simp [S, hlt]
    have hle : (j.castPred hjlast).succ ≤ j := S.le_max' _ hmem
    have hlt' : j < (j.castPred hjlast).succ := by
      conv_lhs => rw [← Fin.castSucc_castPred j hjlast]
      exact Fin.castSucc_lt_succ
    exact absurd hle (not_le.2 hlt')

/-! ## Step functions on a partition -/

/-- The step function equal to `c i` on the piece `(x_{i-1}, x_i]` (and `0` off `(a, b]`). -/
noncomputable def stepFn (P : IntervalPartition a b) (c : Fin P.n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (P.piece i).indicator (fun _ => c i) x

lemma stepFn_eq (P : IntervalPartition a b) (c : Fin P.n → ℝ) {i : Fin P.n} {x : ℝ} (hx : x ∈ P.piece i) :
    stepFn P c x = c i := by
  classical
  rw [stepFn, Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem
    (P.not_mem_piece_of_ne (Ne.symm hji) hx) _) (by simp)]
  exact indicator_of_mem hx _

lemma measurable_stepFn (P : IntervalPartition a b) (c : Fin P.n → ℝ) : Measurable (stepFn P c) := by
  unfold stepFn
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator measurableSet_Ioc

lemma integrable_stepFn (P : IntervalPartition a b) (c : Fin P.n → ℝ) :
    IntegrableOn (stepFn P c) (Ioc a b) := by
  unfold stepFn
  exact integrable_finsetSum _ fun i _ => (integrable_const (c i)).indicator measurableSet_Ioc

lemma integral_stepFn (P : IntervalPartition a b) (c : Fin P.n → ℝ) :
    ∫ x in Ioc a b, stepFn P c x = ∑ i, c i * P.delta i := by
  unfold stepFn
  rw [integral_finsetSum _ fun i _ =>
    (integrable_const (c i)).indicator (show MeasurableSet (P.piece i) from measurableSet_Ioc)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator_const _ (show MeasurableSet (P.piece i) from measurableSet_Ioc), smul_eq_mul, measureReal_def,
    Measure.restrict_apply (show MeasurableSet (P.piece i) from measurableSet_Ioc), inter_eq_left.2 (P.piece_subset i), IntervalPartition.piece,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 (P.mono.monotone Fin.castSucc_lt_succ.le)),
    IntervalPartition.delta, mul_comm]

/-! ## Infimum and supremum on a piece -/

section Tags

variable {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
include hM

lemma bddBelow_image_piece (P : IntervalPartition a b) (i : Fin P.n) :
    BddBelow (f '' Icc (P.points i.castSucc) (P.points i.succ)) :=
  ⟨-M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.1 (hM x (P.Icc_piece_subset i hx))).1⟩

lemma bddAbove_image_piece (P : IntervalPartition a b) (i : Fin P.n) :
    BddAbove (f '' Icc (P.points i.castSucc) (P.points i.succ)) :=
  ⟨M, by
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.1 (hM x (P.Icc_piece_subset i hx))).2⟩

lemma lowerTag_le (P : IntervalPartition a b) {i : Fin P.n} {x : ℝ} (hx : x ∈ P.piece i) :
    lowerTag f P i ≤ f x :=
  csInf_le (bddBelow_image_piece hM P i) (mem_image_of_mem f (Ioc_subset_Icc_self hx))

lemma le_upperTag (P : IntervalPartition a b) {i : Fin P.n} {x : ℝ} (hx : x ∈ P.piece i) :
    f x ≤ upperTag f P i :=
  le_csSup (bddAbove_image_piece hM P i) (mem_image_of_mem f (Ioc_subset_Icc_self hx))

lemma stepFn_lowerTag_le (P : IntervalPartition a b) {x : ℝ} (hx : x ∈ Ioc a b) :
    stepFn P (lowerTag f P) x ≤ f x := by
  obtain ⟨i, hi⟩ := P.exists_mem_piece hx
  rw [stepFn_eq P _ hi]
  exact lowerTag_le hM P hi

lemma le_stepFn_upperTag (P : IntervalPartition a b) {x : ℝ} (hx : x ∈ Ioc a b) :
    f x ≤ stepFn P (upperTag f P) x := by
  obtain ⟨i, hi⟩ := P.exists_mem_piece hx
  rw [stepFn_eq P _ hi]
  exact le_upperTag hM P hi

lemma lowerDarbouxSum_le_lowerDarbouxIntegral (P : IntervalPartition a b) :
    lowerDarbouxSum f P ≤ lowerDarbouxIntegral f a b := by
  refine le_csSup ⟨M * (b - a), ?_⟩ ⟨P, rfl⟩
  rintro _ ⟨Q, rfl⟩
  exact ((lower_upper_sum_bounds (m := -M) (M := M) (fun x hx => (abs_le.1 (hM x hx)).1)
    (fun x hx => (abs_le.1 (hM x hx)).2) Q).2.1).trans
    (lower_upper_sum_bounds (m := -M) (M := M) (fun x hx => (abs_le.1 (hM x hx)).1)
      (fun x hx => (abs_le.1 (hM x hx)).2) Q).2.2

lemma upperDarbouxIntegral_le_upperDarbouxSum (P : IntervalPartition a b) :
    upperDarbouxIntegral f a b ≤ upperDarbouxSum f P := by
  refine csInf_le ⟨-M * (b - a), ?_⟩ ⟨P, rfl⟩
  rintro _ ⟨Q, rfl⟩
  have h := lower_upper_sum_bounds (m := -M) (M := M) (fun x hx => (abs_le.1 (hM x hx)).1)
    (fun x hx => (abs_le.1 (hM x hx)).2) Q
  linarith [h.1, h.2.1]

end Tags

/-! ## The converse of Proposition 5.1.13 -/

/-- A Riemann integrable function has partitions with `U(P, f) - L(P, f)` arbitrarily small (the converse of
Lebl's Proposition 5.1.13). -/
@[kb "lebl2026" "Proposition 5.1.13 (converse), p. 187"]
theorem RiemannIntegrableOn.exists_upper_sub_lower_lt {f : ℝ → ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b)
    {ε : ℝ} (hε : 0 < ε) : ∃ P : IntervalPartition a b, upperDarbouxSum f P - lowerDarbouxSum f P < ε := by
  obtain ⟨⟨M, hM⟩, heq⟩ := hf
  have := intervalPartition_nonempty hab
  have hbound : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M := ⟨M, hM⟩
  have hbddA : BddAbove (range fun P : IntervalPartition a b => lowerDarbouxSum f P) := by
    refine ⟨lowerDarbouxIntegral f a b, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact lowerDarbouxSum_le_lowerDarbouxIntegral hM P
  have hbddB : BddBelow (range fun P : IntervalPartition a b => upperDarbouxSum f P) := by
    refine ⟨upperDarbouxIntegral f a b, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact upperDarbouxIntegral_le_upperDarbouxSum hM P
  obtain ⟨_, ⟨P1, rfl⟩, h1⟩ := exists_lt_of_lt_csSup (range_nonempty _)
    (show lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxIntegral f a b by linarith)
  obtain ⟨_, ⟨P2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (range_nonempty _)
    (show upperDarbouxIntegral f a b < upperDarbouxIntegral f a b + ε / 2 by linarith)
  obtain ⟨Q, hQ1, hQ2⟩ := intervalPartition_common_refinement P1 P2
  have hL := (lower_upper_sum_refinement hbound hQ1).1
  have hU := (lower_upper_sum_refinement hbound hQ2).2
  exact ⟨Q, by linarith⟩

/-! ## The bridge -/

/-- A Riemann integrable function on `[a, b]` (Darboux sense) is integrable on `(a, b]` in Mathlib's (Lebesgue)
sense, and its Riemann integral equals `∫ x in Ioc a b, f x`. -/
theorem RiemannIntegrableOn.integrableOn_and_integral_eq {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : RiemannIntegrableOn f a b) :
    IntegrableOn f (Ioc a b) ∧ riemannIntegral f a b hf = ∫ x in Ioc a b, f x := by
  obtain ⟨M, hM⟩ := hf.1
  have hgap : ∀ k : ℕ, ∃ P : IntervalPartition a b,
      upperDarbouxSum f P - lowerDarbouxSum f P < 1 / ((k : ℝ) + 1) :=
    fun k => hf.exists_upper_sub_lower_lt hab (by positivity)
  choose P hP using hgap
  set φ : ℕ → ℝ → ℝ := fun k => stepFn (P k) (lowerTag f (P k)) with hφ
  set ψ : ℕ → ℝ → ℝ := fun k => stepFn (P k) (upperTag f (P k)) with hψ
  have hφf : ∀ k, ∀ x ∈ Ioc a b, φ k x ≤ f x := fun k x hx => stepFn_lowerTag_le hM (P k) hx
  have hfψ : ∀ k, ∀ x ∈ Ioc a b, f x ≤ ψ k x := fun k x hx => le_stepFn_upperTag hM (P k) hx
  have hfM : ∀ x ∈ Ioc a b, |f x| ≤ M := fun x hx => hM x (Ioc_subset_Icc_self hx)
  -- the envelopes
  set g : ℝ → ℝ := fun x => ⨆ k, φ k x with hg
  set h : ℝ → ℝ := fun x => ⨅ k, ψ k x with hh
  have hgm : Measurable g := Measurable.iSup fun k => measurable_stepFn _ _
  have hhm : Measurable h := Measurable.iInf fun k => measurable_stepFn _ _
  have hφg : ∀ k, ∀ x ∈ Ioc a b, φ k x ≤ g x := fun k x hx =>
    le_ciSup ⟨f x, by rintro _ ⟨j, rfl⟩; exact hφf j x hx⟩ k
  have hgf : ∀ x ∈ Ioc a b, g x ≤ f x := fun x hx => ciSup_le fun k => hφf k x hx
  have hfh : ∀ x ∈ Ioc a b, f x ≤ h x := fun x hx => le_ciInf fun k => hfψ k x hx
  have hhψ : ∀ k, ∀ x ∈ Ioc a b, h x ≤ ψ k x := fun k x hx =>
    ciInf_le ⟨f x, by rintro _ ⟨j, rfl⟩; exact hfψ j x hx⟩ k
  -- bounds by `M`
  have hφM : ∀ k, ∀ x ∈ Ioc a b, -M ≤ φ k x := by
    intro k x hx
    obtain ⟨i, hi⟩ := (P k).exists_mem_piece hx
    simp only [hφ]
    rw [stepFn_eq _ _ hi]
    refine le_csInf ((nonempty_Icc.2 ((P k).mono.monotone Fin.castSucc_lt_succ.le)).image f) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (abs_le.1 (hM y ((P k).Icc_piece_subset i hy))).1
  have hψM : ∀ k, ∀ x ∈ Ioc a b, ψ k x ≤ M := by
    intro k x hx
    obtain ⟨i, hi⟩ := (P k).exists_mem_piece hx
    simp only [hψ]
    rw [stepFn_eq _ _ hi]
    refine csSup_le ((nonempty_Icc.2 ((P k).mono.monotone Fin.castSucc_lt_succ.le)).image f) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (abs_le.1 (hM y ((P k).Icc_piece_subset i hy))).2
  have hgI : IntegrableOn g (Ioc a b) := by
    refine Integrable.mono' (integrable_const M) hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(hφM 0 x hx).trans (hφg 0 x hx), (hgf x hx).trans ((abs_le.1 (hfM x hx)).2)⟩
  have hhI : IntegrableOn h (Ioc a b) := by
    refine Integrable.mono' (integrable_const M) hhm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨((abs_le.1 (hfM x hx)).1).trans (hfh x hx), (hhψ 0 x hx).trans (hψM 0 x hx)⟩
  -- `∫ (h - g) = 0`
  have hint_le : ∀ k : ℕ, ∫ x in Ioc a b, (h x - g x) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hmono : ∫ x in Ioc a b, (h x - g x) ≤ ∫ x in Ioc a b, (ψ k x - φ k x) :=
      integral_mono_ae (hhI.sub hgI) ((integrable_stepFn _ _).sub (integrable_stepFn _ _))
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => by
          linarith [hhψ k x hx, hφg k x hx]))
    rw [integral_sub (integrable_stepFn _ _) (integrable_stepFn _ _)] at hmono
    simp only [integral_stepFn] at hmono
    have := hP k
    rw [upperDarbouxSum, lowerDarbouxSum] at this
    linarith
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] fun x => h x - g x :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => by
      simp only [Pi.zero_apply, sub_nonneg]; exact (hgf x hx).trans (hfh x hx))
  have hint0 : ∫ x in Ioc a b, (h x - g x) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (integral_nonneg_of_ae hnonneg)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    linarith [hint_le k]
  have hae : (fun x => h x - g x) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg (hhI.sub hgI)).1 hint0
  have hfg : f =ᵐ[volume.restrict (Ioc a b)] g := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with x hx hxI
    have : h x = g x := by simpa [sub_eq_zero] using hx
    exact le_antisymm (this ▸ hfh x hxI) (hgf x hxI)
  have hfI : IntegrableOn f (Ioc a b) := hgI.congr hfg.symm
  refine ⟨hfI, ?_⟩
  -- the value
  have hR := hf.2
  have key : ∀ k : ℕ, |riemannIntegral f a b hf - ∫ x in Ioc a b, f x| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hL : lowerDarbouxSum f (P k) ≤ ∫ x in Ioc a b, f x := by
      rw [lowerDarbouxSum, ← integral_stepFn]
      exact integral_mono_ae (integrable_stepFn _ _) hfI
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => hφf k x hx))
    have hU : ∫ x in Ioc a b, f x ≤ upperDarbouxSum f (P k) := by
      rw [upperDarbouxSum, ← integral_stepFn]
      exact integral_mono_ae hfI (integrable_stepFn _ _)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => hfψ k x hx))
    have hRL : lowerDarbouxSum f (P k) ≤ riemannIntegral f a b hf :=
      lowerDarbouxSum_le_lowerDarbouxIntegral hM (P k)
    have hRU : riemannIntegral f a b hf ≤ upperDarbouxSum f (P k) := by
      have := upperDarbouxIntegral_le_upperDarbouxSum hM (P k)
      simp only [riemannIntegral]
      linarith
    rw [abs_le]
    constructor <;> linarith [hP k]
  by_contra hne
  have hpos := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  linarith [key k]

/-- **The Riemann integral is the interval integral.** If `f` is Riemann integrable on `[a, b]` (Darboux sense,
Lebl Definition 5.1.9), then `f` is interval integrable in Mathlib's sense and `∫_a^b f = ∫ x in a..b, f x`. -/
@[kb "lebl2026" "Definition 5.1.9 (agreement with the interval integral), p. 185"]
theorem RiemannIntegrableOn.intervalIntegrable {f : ℝ → ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hf.integrableOn_and_integral_eq hab).1

@[inherit_doc RiemannIntegrableOn.intervalIntegrable, kb "lebl2026" "Definition 5.1.9 (agreement with the interval integral), p. 185"]
theorem riemannIntegral_eq_intervalIntegral {f : ℝ → ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    riemannIntegral f a b hf = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact (hf.integrableOn_and_integral_eq hab).2

end UndergradKB.RealAnalysis
