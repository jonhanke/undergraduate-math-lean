import UndergradKB.Calculus.MultipleIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr

/-!
# Fubini's theorem in cylindrical and spherical coordinates

Iterated integrals over a box of coordinates, in every order of integration, for the cylindrical and
spherical coordinate maps of `UndergradKB.Calculus.MultipleIntegrals`.
-/

namespace UndergradKB.Calculus

open MeasureTheory Set

/-! ## Iterated integrals over a box in `(ℝ × ℝ) × ℝ` -/

/-- A function continuous on a box in `(ℝ × ℝ) × ℝ` has its box integral equal to the iterated
interval integral in the order `x, y, z`. -/
theorem box_integral_eq_iterated {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContinuousOn G ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f)) :
    ∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
      ∫ x in a..b, ∫ y in c..d, ∫ z in e..f, G ((x, y), z) := by
  have hcomp : IsCompact ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hint : IntegrableOn G ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f) volume :=
    hG.integrableOn_compact hcomp
  have hI : Integrable G ((volume.restrict (Icc a b ×ˢ Icc c d)).prod (volume.restrict (Icc e f))) := by
    rw [Measure.prod_restrict]
    exact hint
  have hH : IntegrableOn (fun x : ℝ × ℝ => ∫ z, G (x, z) ∂(volume.restrict (Icc e f)))
      (Icc a b ×ˢ Icc c d) volume := hI.integral_prod_left
  rw [Measure.volume_eq_prod, setIntegral_prod G hint]
  refine Eq.trans (setIntegral_prod (μ := volume) (ν := volume)
    (fun x : ℝ × ℝ => ∫ z in Icc e f, G (x, z)) hH) ?_
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    intervalIntegral.integral_of_le hef, integral_Icc_eq_integral_Ioc]

/-- Swap of the first two coordinates of `(x, y), z`. -/
def permA : ((ℝ × ℝ) × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)

/-- Swap of the last two coordinates of `(x, y), z`. -/
def permB : ((ℝ × ℝ) × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

theorem permA_apply (q : (ℝ × ℝ) × ℝ) : permA q = ((q.1.2, q.1.1), q.2) := rfl

theorem permB_apply (q : (ℝ × ℝ) × ℝ) : permB q = ((q.1.1, q.2), q.1.2) := rfl

theorem permA_mp : MeasurePreserving permA (volume : Measure ((ℝ × ℝ) × ℝ)) volume :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).prod
    (MeasurePreserving.id (volume : Measure ℝ))

theorem permB_mp : MeasurePreserving permB (volume : Measure ((ℝ × ℝ) × ℝ)) volume := by
  have h1 := volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)
  have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.swap : ℝ × ℝ → ℝ × ℝ))
      (volume : Measure (ℝ × ℝ × ℝ)) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  exact (MeasurePreserving.symm _ h1).comp (h2.comp h1)

/-- Integral over a permuted box, for a coordinate permutation `σ` given by an explicit formula. -/
theorem perm_box_integral {E : ((ℝ × ℝ) × ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ)}
    (hE : MeasurePreserving E (volume : Measure ((ℝ × ℝ) × ℝ)) volume)
    (σ : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) (hσ : ∀ q, E q = σ q) (hσc : Continuous σ)
    {S : Set ((ℝ × ℝ) × ℝ)} {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    (hS : σ ⁻¹' S = (Icc a b ×ˢ Icc c d) ×ˢ Icc e f)
    {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContinuousOn G S) :
    ∫ q in S, G q = ∫ x in a..b, ∫ y in c..d, ∫ z in e..f, G (σ ((x, y), z)) := by
  obtain rfl : (⇑E) = σ := funext hσ
  have h := hE.setIntegral_preimage_emb E.measurableEmbedding G S
  rw [← h]
  rw [← box_integral_eq_iterated hab hcd hef (G := fun q => G (E q))]
  · rw [hS]
  · rw [← hS]
    exact hG.comp hσc.continuousOn (fun q hq => hq)

/-- A function continuous on a box of `(ℝ × ℝ) × ℝ` has its box integral equal to the iterated interval
integral in each of the six orders of the three variables. -/
theorem box_integral_six_orders {a b c d e f : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f)
    {G : (ℝ × ℝ) × ℝ → ℝ} (hG : ContinuousOn G ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f)) :
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ x in a..b, ∫ y in c..d, ∫ z in e..f, G ((x, y), z)) ∧
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ x in a..b, ∫ z in e..f, ∫ y in c..d, G ((x, y), z)) ∧
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ y in c..d, ∫ x in a..b, ∫ z in e..f, G ((x, y), z)) ∧
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ y in c..d, ∫ z in e..f, ∫ x in a..b, G ((x, y), z)) ∧
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ z in e..f, ∫ x in a..b, ∫ y in c..d, G ((x, y), z)) ∧
    (∫ p in (Icc a b ×ˢ Icc c d) ×ˢ Icc e f, G p =
        ∫ z in e..f, ∫ y in c..d, ∫ x in a..b, G ((x, y), z)) := by
  refine ⟨box_integral_eq_iterated hab hcd hef hG, ?_, ?_, ?_, ?_, ?_⟩
  · exact perm_box_integral (E := permB) permB_mp (fun q => ((q.1.1, q.2), q.1.2))
      (fun q => permB_apply q) (by fun_prop) hab hef hcd (by ext q; simp only [mem_preimage, mem_prod, mem_Icc]; tauto) hG
  · exact perm_box_integral (E := permA) permA_mp (fun q => ((q.1.2, q.1.1), q.2))
      (fun q => permA_apply q) (by fun_prop) hcd hab hef (by ext q; simp only [mem_preimage, mem_prod, mem_Icc]; tauto) hG
  · exact perm_box_integral (E := permB.trans permA)
      (permB_mp.trans permA_mp)
      (fun q => ((q.2, q.1.1), q.1.2))
      (fun q => rfl) (by fun_prop) hcd hef hab (by ext q; simp only [mem_preimage, mem_prod, mem_Icc]; tauto) hG
  · exact perm_box_integral (E := permA.trans permB)
      (permA_mp.trans permB_mp)
      (fun q => ((q.1.2, q.2), q.1.1))
      (fun q => rfl) (by fun_prop) hef hab hcd (by ext q; simp only [mem_preimage, mem_prod, mem_Icc]; tauto) hG
  · exact perm_box_integral (E := permB.trans (permA.trans permB))
      (permB_mp.trans (permA_mp.trans permB_mp))
      (fun q => ((q.2, q.1.2), q.1.1))
      (fun q => rfl) (by fun_prop) hef hcd hab (by ext q; simp only [mem_preimage, mem_prod, mem_Icc]; tauto) hG

/-! ## Cylindrical coordinates -/

theorem continuous_cylindricalCoord : Continuous cylindricalCoord :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_cylindricalCoord p).continuousAt

theorem cylindricalCoord_apply (r θ z : ℝ) :
    cylindricalCoord ((r, θ), z) = ((r * Real.cos θ, r * Real.sin θ), z) := rfl

/-- The part of a cylindrical box outside the domain of the change of variables is null. -/
theorem volume_cylindrical_box_diff {a b α β c d : ℝ} (ha : 0 ≤ a) (hα : -Real.pi ≤ α)
    (hβ : β ≤ Real.pi) :
    volume (((Icc a b ×ˢ Icc α β) ×ˢ Icc c d) \ (polarCoord.target ×ˢ (univ : Set ℝ))) = 0 := by
  have h0 : volume ({q : (ℝ × ℝ) × ℝ | q.1.1 = 0}) = 0 := by
    have : {q : (ℝ × ℝ) × ℝ | q.1.1 = 0} = ({0} ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
      ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h1 : volume ({q : (ℝ × ℝ) × ℝ | q.1.2 = -Real.pi}) = 0 := by
    have : {q : (ℝ × ℝ) × ℝ | q.1.2 = -Real.pi} =
        ((univ : Set ℝ) ×ˢ {-Real.pi}) ×ˢ (univ : Set ℝ) := by
      ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h2 : volume ({q : (ℝ × ℝ) × ℝ | q.1.2 = Real.pi}) = 0 := by
    have : {q : (ℝ × ℝ) × ℝ | q.1.2 = Real.pi} =
        ((univ : Set ℝ) ×ˢ {Real.pi}) ×ˢ (univ : Set ℝ) := by
      ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine measure_mono_null ?_ (measure_union_null (measure_union_null h0 h1) h2)
  rintro ⟨⟨r, θ⟩, z⟩ ⟨⟨⟨hr, hθ⟩, -⟩, hn⟩
  simp only [mem_Icc] at hr hθ
  simp only [mem_prod, polarCoord_target, mem_Ioi, mem_Ioo, mem_univ, and_true, not_and,
    not_lt] at hn
  by_cases h : r = 0
  · exact Or.inl (Or.inl h)
  · have hr0 : 0 < r := lt_of_le_of_ne (ha.trans hr.1) (Ne.symm h)
    have h3 := hn hr0
    by_cases h' : -Real.pi < θ
    · have h4 := h3 h'
      exact Or.inr (by show θ = Real.pi; linarith [hθ.2])
    · exact Or.inl (Or.inr (by show θ = -Real.pi; linarith [hθ.1]))

/-- Change of variables over a closed cylindrical box (boundary included). -/
theorem setIntegral_cylindricalCoord_image_box {a b α β c d : ℝ} (ha : 0 ≤ a) (hα : -Real.pi ≤ α)
    (hβ : β ≤ Real.pi) (f : (ℝ × ℝ) × ℝ → ℝ) :
    ∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
      ∫ q in (Icc a b ×ˢ Icc α β) ×ˢ Icc c d, q.1.1 * f (cylindricalCoord q) := by
  set R : Set ((ℝ × ℝ) × ℝ) := (Icc a b ×ˢ Icc α β) ×ˢ Icc c d with hRdef
  have hRm : MeasurableSet R :=
    (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc
  set R' : Set ((ℝ × ℝ) × ℝ) := R ∩ (polarCoord.target ×ˢ (univ : Set ℝ)) with hR'def
  have hR'm : MeasurableSet R' :=
    hRm.inter (polarCoord.open_target.measurableSet.prod MeasurableSet.univ)
  have hN : volume (R \ (polarCoord.target ×ˢ (univ : Set ℝ))) = 0 :=
    volume_cylindrical_box_diff ha hα hβ
  haveI : (volume : Measure ((ℝ × ℝ) × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have himg : volume (cylindricalCoord '' (R \ (polarCoord.target ×ˢ (univ : Set ℝ)))) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun q _ => (hasFDerivAt_cylindricalCoord q).differentiableAt.differentiableWithinAt) hN
  have hae : cylindricalCoord '' R =ᵐ[volume] cylindricalCoord '' R' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ himg
      rintro _ ⟨⟨q, hq, rfl⟩, hn⟩
      exact ⟨q, ⟨hq, fun h => hn ⟨q, ⟨hq, h⟩, rfl⟩⟩, rfl⟩
    · rw [diff_eq_empty.2 (image_mono inter_subset_left)]
      simp
  have hae' : R' =ᵐ[volume] R := by
    rw [ae_eq_set]
    constructor
    · rw [diff_eq_empty.2 inter_subset_left]; simp
    · refine measure_mono_null ?_ hN
      intro q hq
      exact ⟨hq.1, fun h => hq.2 ⟨hq.1, h⟩⟩
  rw [setIntegral_congr_set hae, setIntegral_cylindricalCoord_image hR'm inter_subset_right,
    setIntegral_congr_set hae']

/-- OpenStax Calculus 3:Theorem 5.12 (CA-584). Fubini's theorem in cylindrical coordinates: let
`E` be the image under `(r, θ, z) ↦ (r cos θ, r sin θ, z)` of the box `a ≤ r ≤ b`, `α ≤ θ ≤ β`,
`c ≤ z ≤ d` (with `0 ≤ a`, `-π ≤ α`, `β ≤ π`), and `f` continuous on `E`. Then the triple integral of
`f` over `E` equals the iterated integral of `r · f(r cos θ, r sin θ, z)`, in each of the six orders of
integrating `r`, `θ`, `z`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.12, p. 513"]
theorem fubini_cylindrical {a b α β c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hα : -Real.pi ≤ α)
    (hαβ : α ≤ β) (hβ : β ≤ Real.pi) (hcd : c ≤ d) {f : (ℝ × ℝ) × ℝ → ℝ}
    (hf : ContinuousOn f (cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d))) :
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ r in a..b, ∫ θ in α..β, ∫ z in c..d, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ r in a..b, ∫ z in c..d, ∫ θ in α..β, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ θ in α..β, ∫ r in a..b, ∫ z in c..d, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ θ in α..β, ∫ z in c..d, ∫ r in a..b, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ z in c..d, ∫ r in a..b, ∫ θ in α..β, r * f ((r * Real.cos θ, r * Real.sin θ), z)) ∧
    (∫ p in cylindricalCoord '' ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d), f p =
        ∫ z in c..d, ∫ θ in α..β, ∫ r in a..b, r * f ((r * Real.cos θ, r * Real.sin θ), z)) := by
  have hG : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => q.1.1 * f (cylindricalCoord q))
      ((Icc a b ×ˢ Icc α β) ×ˢ Icc c d) :=
    (continuous_fst.comp continuous_fst).continuousOn.mul
      (hf.comp continuous_cylindricalCoord.continuousOn (mapsTo_image _ _))
  have h := box_integral_six_orders hab hαβ hcd hG
  rw [← setIntegral_cylindricalCoord_image_box ha hα hβ f] at h
  exact h

/-! ## Spherical coordinates -/

/-- The measurable equivalence `v ↦ ((v 0, v 1), v 2)` from `Fin 3 → ℝ` to `(ℝ × ℝ) × ℝ`. -/
def sphEquiv : (Fin 3 → ℝ) ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)).trans
    MeasurableEquiv.prodAssoc.symm

theorem sphEquiv_apply (v : Fin 3 → ℝ) : sphEquiv v = ((v 0, v 1), v 2) := rfl

theorem sphEquiv_mp : MeasurePreserving sphEquiv (volume : Measure (Fin 3 → ℝ)) volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      (volume : Measure (ℝ × (Fin 2 → ℝ))) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  have h3 := MeasurePreserving.symm _ (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ))
  exact h3.comp (h2.comp h1)

/-- The vector `![v 0, v 1, v 2]` is `v`. -/
theorem vec3_eta (v : Fin 3 → ℝ) : ![v 0, v 1, v 2] = v := by
  ext i; fin_cases i <;> rfl

theorem continuous_sphericalCoord : Continuous sphericalCoord :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_sphericalCoord p).continuousAt

theorem continuous_vec3 : Continuous (fun q : (ℝ × ℝ) × ℝ => (![q.1.1, q.1.2, q.2] : Fin 3 → ℝ)) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- The spherical box `a ≤ ρ ≤ b`, `φ1 ≤ φ ≤ φ2`, `α ≤ θ ≤ β`, as a subset of `Fin 3 → ℝ`. -/
def sphBox (a b φ1 φ2 α β : ℝ) : Set (Fin 3 → ℝ) :=
  {v | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β}

theorem sphBox_eq (a b φ1 φ2 α β : ℝ) :
    sphBox a b φ1 φ2 α β = sphEquiv ⁻¹' ((Icc a b ×ˢ Icc φ1 φ2) ×ˢ Icc α β) := by
  ext v
  simp only [sphBox, mem_setOf_eq, mem_preimage, sphEquiv_apply, mem_prod]
  tauto

theorem measurableSet_sphBox (a b φ1 φ2 α β : ℝ) : MeasurableSet (sphBox a b φ1 φ2 α β) := by
  rw [sphBox_eq]
  exact sphEquiv.measurable
    ((measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc)

theorem measurableSet_sphericalDomain : MeasurableSet sphericalDomain := by
  have h : ∀ i : Fin 3, Measurable fun v : Fin 3 → ℝ => v i := measurable_pi_apply
  simp only [sphericalDomain, setOf_and]
  exact (measurableSet_lt measurable_const (h 0)).inter
    ((measurableSet_lt measurable_const (h 1)).inter
    ((measurableSet_lt (h 1) measurable_const).inter
    ((measurableSet_lt measurable_const (h 2)).inter
    (measurableSet_lt (h 2) measurable_const))))

/-- The part of a spherical box outside the domain of the change of variables is null. -/
theorem volume_sphBox_diff {a b φ1 φ2 α β : ℝ} (ha : 0 ≤ a) (hφ1 : 0 ≤ φ1) (hφ2 : φ2 ≤ Real.pi)
    (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) :
    volume (sphBox a b φ1 φ2 α β \ sphericalDomain) = 0 := by
  have hnull : ∀ S : Set ((ℝ × ℝ) × ℝ), volume S = 0 → volume (sphEquiv ⁻¹' S) = 0 := fun S h => by
    rw [sphEquiv_mp.measure_preimage_equiv]; exact h
  have h0 : volume ({v : Fin 3 → ℝ | v 0 = 0}) = 0 := by
    have : {v : Fin 3 → ℝ | v 0 = 0} = sphEquiv ⁻¹' (({0} ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) := by
      ext v; simp [sphEquiv_apply]
    rw [this]; apply hnull
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h1 : ∀ c : ℝ, volume ({v : Fin 3 → ℝ | v 1 = c}) = 0 := fun c => by
    have : {v : Fin 3 → ℝ | v 1 = c} = sphEquiv ⁻¹' (((univ : Set ℝ) ×ˢ {c}) ×ˢ (univ : Set ℝ)) := by
      ext v; simp [sphEquiv_apply]
    rw [this]; apply hnull
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have h2 : ∀ c : ℝ, volume ({v : Fin 3 → ℝ | v 2 = c}) = 0 := fun c => by
    have : {v : Fin 3 → ℝ | v 2 = c} = sphEquiv ⁻¹' (((univ : Set (ℝ × ℝ)) ×ˢ {c})) := by
      ext v; simp [sphEquiv_apply]
    rw [this]; apply hnull
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine measure_mono_null ?_ (measure_union_null
    (measure_union_null (measure_union_null (measure_union_null h0 (h1 0)) (h1 Real.pi))
      (h2 (-Real.pi))) (h2 Real.pi))
  rintro v ⟨⟨hr, hφ, hθ⟩, hn⟩
  simp only [mem_Icc] at hr hφ hθ
  simp only [sphericalDomain, mem_setOf_eq, not_and, not_lt] at hn
  by_cases h : v 0 = 0
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · have hr0 : 0 < v 0 := lt_of_le_of_ne (ha.trans hr.1) (Ne.symm h)
    have h3 := hn hr0
    by_cases h' : 0 < v 1
    · have h4 := h3 h'
      by_cases h'' : v 1 < Real.pi
      · have h5 := h4 h''
        by_cases h6 : -Real.pi < v 2
        · have h7 := h5 h6
          exact Or.inr (by show v 2 = Real.pi; linarith [hθ.2])
        · exact Or.inl (Or.inr (by show v 2 = -Real.pi; linarith [hθ.1]))
      · exact Or.inl (Or.inl (Or.inr (by show v 1 = Real.pi; linarith [hφ.2])))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (by show v 1 = 0; linarith [hφ.1]))))

/-- Change of variables over a closed spherical box (boundary included). -/
theorem setIntegral_sphericalCoord_image_box {a b φ1 φ2 α β : ℝ} (ha : 0 ≤ a) (hφ1 : 0 ≤ φ1)
    (hφ2 : φ2 ≤ Real.pi) (hα : -Real.pi ≤ α) (hβ : β ≤ Real.pi) (f : (Fin 3 → ℝ) → ℝ) :
    ∫ p in sphericalCoord '' sphBox a b φ1 φ2 α β, f p =
      ∫ v in sphBox a b φ1 φ2 α β, v 0 ^ 2 * Real.sin (v 1) * f (sphericalCoord v) := by
  set R := sphBox a b φ1 φ2 α β with hRdef
  have hRm : MeasurableSet R := measurableSet_sphBox _ _ _ _ _ _
  set R' : Set (Fin 3 → ℝ) := R ∩ sphericalDomain with hR'def
  have hR'm : MeasurableSet R' := hRm.inter measurableSet_sphericalDomain
  have hN : volume (R \ sphericalDomain) = 0 := volume_sphBox_diff ha hφ1 hφ2 hα hβ
  have himg : volume (sphericalCoord '' (R \ sphericalDomain)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun q _ => (hasFDerivAt_sphericalCoord q).differentiableAt.differentiableWithinAt) hN
  have hae : sphericalCoord '' R =ᵐ[volume] sphericalCoord '' R' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ himg
      rintro _ ⟨⟨q, hq, rfl⟩, hn⟩
      exact ⟨q, ⟨hq, fun h => hn ⟨q, ⟨hq, h⟩, rfl⟩⟩, rfl⟩
    · rw [sdiff_eq_empty.2 (image_mono inter_subset_left)]
      simp
  have hae' : R' =ᵐ[volume] R := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.2 inter_subset_left]; simp
    · refine measure_mono_null ?_ hN
      intro q hq
      exact ⟨hq.1, fun h => hq.2 ⟨hq.1, h⟩⟩
  rw [setIntegral_congr_set hae, setIntegral_sphericalCoord_image hR'm inter_subset_right,
    setIntegral_congr_set hae']

/-- OpenStax Calculus 3:Theorem 5.13 (CA-586). Fubini's theorem in spherical coordinates: let `E` be
the image under `(ρ, φ, θ) ↦ (ρ sin φ cos θ, ρ sin φ sin θ, ρ cos φ)` (as `sphericalCoord ![ρ, φ, θ]`)
of the box `a ≤ ρ ≤ b`, `φ1 ≤ φ ≤ φ2`, `α ≤ θ ≤ β` (with `0 ≤ a`, `0 ≤ φ1`, `φ2 ≤ π`, `-π ≤ α`,
`β ≤ π`), and `f` continuous on `E`. Then the triple integral of `f` over `E` equals the iterated
integral of `ρ² sin φ · f(sphericalCoord ![ρ, φ, θ])`, in each of the six orders of integrating `ρ`,
`φ`, `θ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.13, p. 520"]
theorem fubini_spherical {a b φ1 φ2 α β : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hφ1 : 0 ≤ φ1)
    (hφ : φ1 ≤ φ2) (hφ2 : φ2 ≤ Real.pi) (hα : -Real.pi ≤ α) (hαβ : α ≤ β) (hβ : β ≤ Real.pi)
    {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContinuousOn f (sphericalCoord ''
      {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β})) :
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ ρ in a..b, ∫ φ in φ1..φ2, ∫ θ in α..β,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ ρ in a..b, ∫ θ in α..β, ∫ φ in φ1..φ2,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ φ in φ1..φ2, ∫ ρ in a..b, ∫ θ in α..β,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ φ in φ1..φ2, ∫ θ in α..β, ∫ ρ in a..b,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ θ in α..β, ∫ ρ in a..b, ∫ φ in φ1..φ2,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) ∧
    (∫ p in sphericalCoord '' {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β},
        f p = ∫ θ in α..β, ∫ φ in φ1..φ2, ∫ ρ in a..b,
          ρ ^ 2 * Real.sin φ * f (sphericalCoord ![ρ, φ, θ])) := by
  have hset : {v : Fin 3 → ℝ | v 0 ∈ Icc a b ∧ v 1 ∈ Icc φ1 φ2 ∧ v 2 ∈ Icc α β} =
      sphBox a b φ1 φ2 α β := rfl
  rw [hset] at hf ⊢
  set G : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    q.1.1 ^ 2 * Real.sin q.1.2 * f (sphericalCoord ![q.1.1, q.1.2, q.2]) with hGdef
  have hbox : sphBox a b φ1 φ2 α β = sphEquiv ⁻¹' ((Icc a b ×ˢ Icc φ1 φ2) ×ˢ Icc α β) :=
    sphBox_eq _ _ _ _ _ _
  have hG : ContinuousOn G ((Icc a b ×ˢ Icc φ1 φ2) ×ˢ Icc α β) := by
    have h1 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => f (sphericalCoord ![q.1.1, q.1.2, q.2]))
        ((Icc a b ×ˢ Icc φ1 φ2) ×ˢ Icc α β) := by
      refine hf.comp (continuous_sphericalCoord.comp continuous_vec3).continuousOn ?_
      intro q hq
      refine ⟨![q.1.1, q.1.2, q.2], ?_, rfl⟩
      rw [hbox]
      simpa [sphEquiv_apply] using hq
    exact ((((continuous_fst.comp continuous_fst).pow 2).mul
      (Real.continuous_sin.comp (continuous_snd.comp continuous_fst))).continuousOn).mul h1
  have hint : ∫ v in sphBox a b φ1 φ2 α β, v 0 ^ 2 * Real.sin (v 1) * f (sphericalCoord v) =
      ∫ q in (Icc a b ×ˢ Icc φ1 φ2) ×ˢ Icc α β, G q := by
    rw [hbox, ← sphEquiv_mp.setIntegral_preimage_emb sphEquiv.measurableEmbedding G]
    refine setIntegral_congr_fun ?_ fun v _ => ?_
    · rw [← hbox]; exact measurableSet_sphBox _ _ _ _ _ _
    · simp only [hGdef, sphEquiv_apply, vec3_eta]
  have h := box_integral_six_orders hab hφ hαβ hG
  rw [setIntegral_sphericalCoord_image_box ha hφ1 hφ2 hα hβ f, hint]
  exact h

end UndergradKB.Calculus
