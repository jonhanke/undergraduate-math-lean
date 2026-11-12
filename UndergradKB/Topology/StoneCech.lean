import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Order.Filter.Ultrafilter.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum
import UndergradKB.Common.Attr

/-!
# Stone-Cech compactifications (Morris, Topology Without Tears, section 10.4)

The book defines a Stone-Cech compactification of a space `X` as a compact Hausdorff space `K` with a
continuous map `β : X → K` through which every continuous map into a compact Hausdorff space factors
uniquely.  Mathlib has the construction `StoneCech X`; we add the book's notion as a Prop-valued
structure `IsStoneCech` (the universe `w` is that of the test spaces `Y`) and prove the results of the
section about it.
-/

namespace UndergradKB.Topology

open Set Filter unitInterval

universe u v w

/-- Bridging notion for Morris, Topology Without Tears, Definition 10.4.1: `β : X → K` makes the
compact Hausdorff space `K` a Stone-Cech compactification of `X` (every continuous map from `X` to a
compact Hausdorff space `Y` of universe `w` extends uniquely along `β`). -/
structure IsStoneCech {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K]
    (β : X → K) : Prop where
  compactSpace : CompactSpace K
  t2Space : T2Space K
  continuous : Continuous β
  exists_unique_extension : ∀ {Y : Type w} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : X → Y), Continuous φ → ∃! Φ : K → Y, Continuous Φ ∧ Φ ∘ β = φ

section Basic

variable {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K] {β : X → K}

/-- Two continuous maps from a Stone-Cech compactification that agree after composing with `β` are
equal. -/
theorem IsStoneCech.hom_ext (h : IsStoneCech.{u, v, w} β) {Y : Type w} [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] {Ψ₁ Ψ₂ : K → Y} (h₁ : Continuous Ψ₁) (h₂ : Continuous Ψ₂)
    (hΨ : Ψ₁ ∘ β = Ψ₂ ∘ β) : Ψ₁ = Ψ₂ := by
  have hc : Continuous (Ψ₂ ∘ β) := h₂.comp h.continuous
  exact (h.exists_unique_extension (Ψ₂ ∘ β) hc).unique ⟨h₁, hΨ⟩ ⟨h₂, rfl⟩

/-- The Stone-Cech property transports along a homeomorphism of the compactification. -/
theorem IsStoneCech.of_homeomorph {K' : Type*} [TopologicalSpace K']
    (h : IsStoneCech.{u, v, w} β) (e : K ≃ₜ K') : IsStoneCech.{u, _, w} (e ∘ β) := by
  have := h.compactSpace
  have := h.t2Space
  have : T2Space K' := e.symm.isEmbedding.t2Space
  refine ⟨e.compactSpace, this, e.continuous.comp h.continuous, ?_⟩
  intro Y _ _ _ φ hφ
  obtain ⟨Φ, ⟨hΦ, hΦβ⟩, huniq⟩ := h.exists_unique_extension φ hφ
  refine ⟨Φ ∘ e.symm, ⟨hΦ.comp e.symm.continuous, ?_⟩, ?_⟩
  · ext x; simp [← hΦβ]
  · rintro Ψ ⟨hΨ, hΨβ⟩
    have : Ψ ∘ e = Φ := huniq _ ⟨hΨ.comp e.continuous, by rw [Function.comp_assoc, hΨβ]⟩
    ext y
    have := congrFun this (e.symm y)
    simpa using this

end Basic

/-- Mathlib's `StoneCech X` with `stoneCechUnit` is a Stone-Cech compactification in the book's sense. -/
theorem isStoneCech_stoneCech (X : Type u) [TopologicalSpace X] :
    IsStoneCech.{u, u, w} (stoneCechUnit : X → StoneCech X) := by
  refine ⟨inferInstance, inferInstance, continuous_stoneCechUnit, ?_⟩
  intro Y _ _ _ φ hφ
  refine ⟨stoneCechExtend hφ, ⟨continuous_stoneCechExtend hφ, stoneCechExtend_extends hφ⟩, ?_⟩
  rintro Ψ ⟨hΨ, hΨβ⟩
  exact stoneCech_hom_ext hΨ (continuous_stoneCechExtend hφ)
    (by rw [hΨβ, stoneCechExtend_extends])

section Density

variable {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K] {β : X → K}

omit [TopologicalSpace X] in
/-- Density of the image already follows from uniqueness of extensions of maps to `[0,1]`. -/
theorem denseRange_of_unitInterval_ext_unique [CompactSpace K] [T2Space K]
    (huniq : ∀ Ψ₁ Ψ₂ : K → I, Continuous Ψ₁ → Continuous Ψ₂ → Ψ₁ ∘ β = Ψ₂ ∘ β → Ψ₁ = Ψ₂) :
    DenseRange β := by
  intro z
  by_contra hz
  obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed (isClosed_closure (s := range β))
    (isClosed_singleton (x := z)) (disjoint_singleton_right.2 hz)
  let F : K → I := fun x => ⟨f x, hf x⟩
  have hF : Continuous F := f.continuous.subtype_mk _
  have h0 : F = fun _ => 0 := by
    refine huniq F (fun _ => 0) hF continuous_const ?_
    ext x
    simpa [F] using hf0 (subset_closure ⟨x, rfl⟩)
  have := congrFun h0 z
  have h1 : f z = 1 := hf1 rfl
  have : (F z : ℝ) = 0 := by rw [this]; rfl
  simp [F, h1] at this

/-- Morris, Topology Without Tears, Lemma 10.4.7 (TP-319). In any Stone-Cech compactification of `X`
the image of `X` is dense. -/
@[kb "morris2024" "Lemma 10.4.7, p. 331"]
theorem IsStoneCech.denseRange (h : IsStoneCech.{u, v, 0} β) : DenseRange β := by
  have := h.compactSpace
  have := h.t2Space
  exact denseRange_of_unitInterval_ext_unique fun _ _ h₁ h₂ hΨ => h.hom_ext h₁ h₂ hΨ

end Density

section Uniqueness

variable {X : Type u} {K₁ K₂ : Type v} [TopologicalSpace X] [TopologicalSpace K₁]
  [TopologicalSpace K₂] {β₁ : X → K₁} {β₂ : X → K₂}

/-- Morris, Topology Without Tears, Proposition 10.4.8 (TP-320). Any two Stone-Cech compactifications
of `X` are homeomorphic by a homeomorphism commuting with the maps from `X`. -/
@[kb "morris2024" "Proposition 10.4.8, p. 332"]
theorem IsStoneCech.exists_homeomorph (h₁ : IsStoneCech.{u, v, v} β₁)
    (h₂ : IsStoneCech.{u, v, v} β₂) : ∃ Θ : K₁ ≃ₜ K₂, Θ ∘ β₁ = β₂ := by
  have := h₁.compactSpace
  have := h₁.t2Space
  have := h₂.compactSpace
  have := h₂.t2Space
  obtain ⟨Θ, ⟨hΘ, hΘβ⟩, -⟩ := h₁.exists_unique_extension β₂ h₂.continuous
  obtain ⟨Θ', ⟨hΘ', hΘ'β⟩, -⟩ := h₂.exists_unique_extension β₁ h₁.continuous
  have h12 : Θ' ∘ Θ = id :=
    h₁.hom_ext (hΘ'.comp hΘ) continuous_id
      (by rw [Function.comp_assoc, hΘβ, hΘ'β]; rfl)
  have h21 : Θ ∘ Θ' = id :=
    h₂.hom_ext (hΘ.comp hΘ') continuous_id
      (by rw [Function.comp_assoc, hΘ'β, hΘβ]; rfl)
  exact ⟨⟨⟨Θ, Θ', congrFun h12, congrFun h21⟩, hΘ, hΘ'⟩, hΘβ⟩

end Uniqueness

section Compact

/-- Morris, Topology Without Tears, Remark 10.4.10 (TP-321), first half. A compact Hausdorff space
together with the identity map is its own Stone-Cech compactification. -/
@[kb "morris2024" "Remark 10.4.10, p. 333"]
theorem isStoneCech_id (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    IsStoneCech.{u, u, w} (id : X → X) := by
  refine ⟨inferInstance, inferInstance, continuous_id, ?_⟩
  intro Y _ _ _ φ hφ
  refine ⟨φ, ⟨hφ, rfl⟩, ?_⟩
  rintro Ψ ⟨-, hΨ⟩
  exact hΨ

/-- Morris, Topology Without Tears, Remark 10.4.10 (TP-321). For compact Hausdorff `X` the canonical
map into its Stone-Cech compactification is a homeomorphism. -/
@[kb "morris2024" "Remark 10.4.10, p. 333"]
theorem exists_homeomorph_stoneCech_of_compact (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : ∃ e : X ≃ₜ StoneCech X, ⇑e = stoneCechUnit := by
  obtain ⟨e, he⟩ := (isStoneCech_id.{u, u} X).exists_homeomorph (isStoneCech_stoneCech X)
  exact ⟨e, he⟩

end Compact

section Criterion

variable {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K]

/-- Morris, Topology Without Tears, Proposition 10.4.12 (TP-322). A compact Hausdorff `K` with a map
`θ : X → K` such that every continuous map `X → [0,1]` extends uniquely to `K` is a Stone-Cech
compactification of `X`. -/
@[kb "morris2024" "Proposition 10.4.12, p. 333"]
theorem isStoneCech_of_unitInterval [CompactSpace K] [T2Space K] {θ : X → K} (hθ : Continuous θ)
    (h : ∀ φ : X → I, Continuous φ → ∃! Φ : K → I, Continuous Φ ∧ Φ ∘ θ = φ) :
    IsStoneCech.{u, v, w} θ := by
  have huniq : ∀ Ψ₁ Ψ₂ : K → I, Continuous Ψ₁ → Continuous Ψ₂ → Ψ₁ ∘ θ = Ψ₂ ∘ θ → Ψ₁ = Ψ₂ := by
    intro Ψ₁ Ψ₂ h₁ h₂ hΨ
    exact (h (Ψ₂ ∘ θ) (h₂.comp hθ)).unique ⟨h₁, hΨ⟩ ⟨h₂, rfl⟩
  have hdense := denseRange_of_unitInterval_ext_unique huniq
  let j : StoneCech X → K := stoneCechExtend hθ
  have hj : Continuous j := continuous_stoneCechExtend hθ
  have hjθ : j ∘ stoneCechUnit = θ := stoneCechExtend_extends hθ
  have hsurj : Function.Surjective j := by
    have hc : IsClosed (range j) := (isCompact_range hj).isClosed
    have : range θ ⊆ range j := by
      rintro _ ⟨x, rfl⟩
      exact ⟨stoneCechUnit x, congrFun hjθ x⟩
    intro y
    exact hc.closure_subset_iff.2 this (hdense y)
  have hinj : Function.Injective j := by
    intro p q hpq
    by_contra hne
    obtain ⟨f, hf0, hf1, hf⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := p)) (isClosed_singleton (x := q)) (disjoint_singleton.2 hne)
    let g : StoneCech X → I := fun x => ⟨f x, hf x⟩
    have hg : Continuous g := f.continuous.subtype_mk _
    obtain ⟨G, ⟨hG, hGθ⟩, -⟩ := h (g ∘ stoneCechUnit) (hg.comp continuous_stoneCechUnit)
    have hGj : G ∘ j = g :=
      stoneCech_hom_ext (hG.comp hj) hg (by rw [Function.comp_assoc, hjθ, hGθ])
    have e1 : g p = g q := by
      rw [← hGj]
      simp [hpq]
    have hp : f p = 0 := hf0 rfl
    have hq : f q = 1 := hf1 rfl
    have := congrArg Subtype.val e1
    simp [g, hp, hq] at this
  let e : StoneCech X ≃ₜ K :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j ⟨hinj, hsurj⟩) hj
  have h1 := (isStoneCech_stoneCech.{u, w} X).of_homeomorph e
  have h2 : (e ∘ stoneCechUnit) = θ := hjθ
  rw [h2] at h1
  exact h1

end Criterion

section Nat

variable {X : Type} [TopologicalSpace X]

/-- The map from `ℕ` to the closure in `StoneCech X` of the image of `ℕ` under `e`. -/
def natToClosure (e : ℕ → X) :
    ℕ → closure (range fun n : ℕ => (stoneCechUnit (e n) : StoneCech X)) :=
  fun n => ⟨stoneCechUnit (e n), subset_closure ⟨n, rfl⟩⟩

/-- Morris, Topology Without Tears, Proposition 10.4.13 (TP-323), general form. If `ℕ` is embedded as
a closed subset of a normal space `X`, then the closure in `βX` of the image of `ℕ` is the
Stone-Cech compactification of `ℕ`. -/
theorem isStoneCech_natToClosure [NormalSpace X] {e : ℕ → X} (he : Topology.IsClosedEmbedding e) :
    IsStoneCech.{0, 0, w} (natToClosure e) := by
  have : CompactSpace (closure (range fun n : ℕ => (stoneCechUnit (e n) : StoneCech X))) :=
    isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have hdense : DenseRange (natToClosure e) := by
    intro k
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have : Subtype.val '' range (natToClosure e) =
        range fun n : ℕ => (stoneCechUnit (e n) : StoneCech X) := by
      rw [← range_comp]
      rfl
    rw [this]
    exact k.2
  refine isStoneCech_of_unitInterval continuous_of_discreteTopology ?_
  intro φ hφ
  obtain ⟨g, hg⟩ := ContinuousMap.exists_extension he (⟨φ, hφ⟩ : C(ℕ, I))
  have hgφ : ∀ n, g (e n) = φ n := fun n => congrArg (fun f : C(ℕ, I) => f n) hg
  refine ⟨fun k => stoneCechExtend g.continuous k.1,
    ⟨(continuous_stoneCechExtend g.continuous).comp continuous_subtype_val, ?_⟩, ?_⟩
  · ext n
    simp [natToClosure, hgφ]
  · rintro Ψ ⟨hΨ, hΨθ⟩
    refine Continuous.ext_on hdense hΨ
      ((continuous_stoneCechExtend g.continuous).comp continuous_subtype_val) ?_
    rintro _ ⟨n, rfl⟩
    have := congrFun hΨθ n
    simp only [Function.comp] at this
    rw [this]
    simp [natToClosure, hgφ]

/-- Morris, Topology Without Tears, Proposition 10.4.13 (TP-323). The closure of `ℕ` in `β ℝ` is the
Stone-Cech compactification of `ℕ`. -/
@[kb "morris2024" "Proposition 10.4.13, p. 334"]
theorem isStoneCech_natToClosure_real :
    IsStoneCech.{0, 0, w} (natToClosure (fun n : ℕ => (n : ℝ))) :=
  isStoneCech_natToClosure Nat.isClosedEmbedding_coe_real

/-- Morris, Topology Without Tears, Remark 10.4.14 (TP-323). The closure of `ℕ` in `β ℚ` is the
Stone-Cech compactification of `ℕ`. -/
@[kb "morris2024" "Remark 10.4.14, p. 334"]
theorem isStoneCech_natToClosure_rat :
    IsStoneCech.{0, 0, w} (natToClosure (fun n : ℕ => (n : ℚ))) :=
  isStoneCech_natToClosure Nat.isClosedEmbedding_coe_rat

end Nat

section Cardinality

open Cardinal

/-- For discrete `X`, the map `Ultrafilter X → StoneCech X` extending `stoneCechUnit` is bijective. -/
theorem bijective_ultrafilter_extend_stoneCechUnit (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] :
    Function.Bijective (Ultrafilter.extend (stoneCechUnit : X → StoneCech X)) := by
  have hE : Continuous (Ultrafilter.extend (stoneCechUnit : X → StoneCech X)) :=
    continuous_ultrafilter_extend _
  refine ⟨?_, ?_⟩
  · intro u v huv
    by_contra hne
    have : ∃ A, A ∈ u ∧ A ∉ v := by
      by_contra hcon
      push Not at hcon
      exact hne (Ultrafilter.eq_of_le (show (v : Filter X) ≤ u from fun A hA => hcon A hA)).symm
    obtain ⟨A, hAu, hAv⟩ := this
    classical
    let g : X → Bool := fun x => decide (x ∈ A)
    have hg : Continuous g := continuous_of_discreteTopology
    have hΦ := continuous_stoneCechExtend hg
    have hcomp : stoneCechExtend hg ∘ Ultrafilter.extend (stoneCechUnit : X → StoneCech X) =
        Ultrafilter.extend g := by
      refine Continuous.ext_on denseRange_pure (hΦ.comp hE) (continuous_ultrafilter_extend g) ?_
      rintro _ ⟨x, rfl⟩
      simp [ultrafilter_extend_pure]
    have h1 : Ultrafilter.extend g u = true := by
      rw [ultrafilter_extend_eq_iff, nhds_discrete, Filter.le_pure_iff, Ultrafilter.coe_map,
        Filter.mem_map]
      exact Filter.mem_of_superset hAu (fun x hx => by simp [g, hx])
    have h2 : Ultrafilter.extend g v = false := by
      rw [ultrafilter_extend_eq_iff, nhds_discrete, Filter.le_pure_iff, Ultrafilter.coe_map,
        Filter.mem_map]
      exact Filter.mem_of_superset (Ultrafilter.compl_mem_iff_notMem.2 hAv)
        (fun x hx => by simpa [g] using hx)
    have a := congrFun hcomp u
    have b := congrFun hcomp v
    simp only [Function.comp] at a b
    rw [h1, huv] at a
    rw [h2, a] at b
    exact Bool.noConfusion b
  · intro y
    have hc : IsClosed (range (Ultrafilter.extend (stoneCechUnit : X → StoneCech X))) :=
      (isCompact_range hE).isClosed
    have : range (stoneCechUnit : X → StoneCech X) ⊆
        range (Ultrafilter.extend (stoneCechUnit : X → StoneCech X)) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨pure x, ultrafilter_extend_pure _ _⟩
    exact hc.closure_subset_iff.2 this (denseRange_stoneCechUnit y)

/-- For a discrete space, the Stone-Cech compactification is the space of ultrafilters. -/
noncomputable def ultrafilterEquivStoneCech (X : Type u) [TopologicalSpace X] [DiscreteTopology X] :
    Ultrafilter X ≃ StoneCech X :=
  Equiv.ofBijective _ (bijective_ultrafilter_extend_stoneCechUnit X)

/-- Morris, Topology Without Tears, Corollary 10.4.20 (TP-328). For an infinite discrete space `X`,
the Stone-Cech compactification has cardinality `2 ^ 2 ^ #X`. -/
@[kb "morris2024" "Corollary 10.4.20, p. 335"]
theorem mk_stoneCech_of_discrete (X : Type u) [TopologicalSpace X] [DiscreteTopology X]
    [Infinite X] : #(StoneCech X) = 2 ^ (2 ^ #X : Cardinal) := by
  rw [← Cardinal.mk_congr (ultrafilterEquivStoneCech X)]
  exact Cardinal.mk_ultrafilter_of_infinite

/-- Morris, Topology Without Tears, Proposition 10.4.15 (TP-324). For a separable space `X` the
cardinality of `βX` is at most that of `βℕ`. -/
@[kb "morris2024" "Proposition 10.4.15, p. 334"]
theorem mk_stoneCech_le_of_separable (X : Type u) [TopologicalSpace X] [TopologicalSpace.SeparableSpace X] :
    Cardinal.lift.{0} #(StoneCech X) ≤ Cardinal.lift.{u} #(StoneCech ℕ) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hc : Continuous (fun x : X => (IsEmpty.false x).elim : X → Empty) :=
      ⟨fun s _ => by
        rw [Set.eq_empty_of_isEmpty ((fun x : X => (IsEmpty.false x).elim : X → Empty) ⁻¹' s)]
        exact isOpen_empty⟩
    have : IsEmpty (StoneCech X) := ⟨fun y => (stoneCechExtend hc y).elim⟩
    simp
  · obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq X
    have hsc : Continuous s := continuous_of_discreteTopology
    have hg : Continuous (stoneCechUnit ∘ s) := continuous_stoneCechUnit.comp hsc
    have hΦ := continuous_stoneCechExtend hg
    have hsurj : Function.Surjective (stoneCechExtend hg) := by
      have hc : IsClosed (range (stoneCechExtend hg)) := (isCompact_range hΦ).isClosed
      have hd : DenseRange (stoneCechUnit ∘ s) :=
        denseRange_stoneCechUnit.comp hs continuous_stoneCechUnit
      have : range (stoneCechUnit ∘ s) ⊆ range (stoneCechExtend hg) := by
        rintro _ ⟨n, rfl⟩
        exact ⟨stoneCechUnit n, by simp⟩
      intro y
      exact hc.closure_subset_iff.2 this (hd y)
    exact Cardinal.lift_mk_le_lift_mk_of_surjective hsurj

/-- Cardinality of `βℕ`. -/
theorem mk_stoneCech_nat : #(StoneCech ℕ) = 2 ^ continuum := by
  rw [mk_stoneCech_of_discrete, Cardinal.mk_nat, Cardinal.two_power_aleph0]

/-- If `ℕ` embeds as a closed subset of a normal space `X`, then `β ℕ` has at most the cardinality of
`β X`. -/
theorem mk_stoneCech_nat_le {X : Type} [TopologicalSpace X] [NormalSpace X] {e : ℕ → X}
    (he : Topology.IsClosedEmbedding e) : #(StoneCech ℕ) ≤ #(StoneCech X) := by
  obtain ⟨Θ, -⟩ := (isStoneCech_natToClosure.{0} he).exists_homeomorph (isStoneCech_stoneCech ℕ)
  calc #(StoneCech ℕ) = #(closure (range fun n : ℕ => (stoneCechUnit (e n) : StoneCech X))) :=
        (Cardinal.mk_congr Θ.toEquiv).symm
    _ ≤ #(StoneCech X) := Cardinal.mk_set_le _

/-- Morris, Topology Without Tears, Propositions 10.4.16 and 10.4.17 (TP-325). The Stone-Cech
compactifications of `ℕ`, `ℚ` and `ℝ` all have cardinality `2 ^ 𝔠`. -/
@[kb "morris2024" "Proposition 10.4.17, p. 335"]
theorem mk_stoneCech_nat_rat_real :
    #(StoneCech ℕ) = 2 ^ continuum ∧ #(StoneCech ℚ) = 2 ^ continuum ∧
      #(StoneCech ℝ) = 2 ^ continuum := by
  refine ⟨mk_stoneCech_nat, ?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · have := mk_stoneCech_le_of_separable ℚ
      simpa [mk_stoneCech_nat] using this
    · rw [← mk_stoneCech_nat]
      exact mk_stoneCech_nat_le Nat.isClosedEmbedding_coe_rat
  · refine le_antisymm ?_ ?_
    · have := mk_stoneCech_le_of_separable ℝ
      simpa [mk_stoneCech_nat] using this
    · rw [← mk_stoneCech_nat]
      exact mk_stoneCech_nat_le Nat.isClosedEmbedding_coe_real

end Cardinality

end UndergradKB.Topology
