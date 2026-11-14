import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Bornology.BoundedOperation
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis: definition items, course layer
Thin restatements in the book's terms of Definitions 2.1.1, 2.1.10, 2.2.7, 3.2.1 and 3.2.4.
The extended plane is modelled in this library by `OnePoint ℂ` (see `mobiusExt`); the arithmetic rules of
Definition 3.2.4 are stated as limit statements in `ℂ`, which is how the book justifies them. -/

namespace UndergradKB.ComplexAnalysis.Course.BeckDefs
open Filter Topology Set Metric

/-- Beck Definition 2.1.1 (CX-020). A function on `G` assigns to each `z ∈ G` exactly one value; functions
`ℂ → ℂ` are used for functions on `G`, and two of them define the same function on `G` iff they agree on `G`. -/
@[kb "beck2025" "Definition 2.1.1, p. 32"]
theorem function_on_set (G : Set ℂ) :
    (∀ f : G → ℂ, ∀ z : G, ∃! w, f z = w) ∧
    (∀ f g : ℂ → ℂ, G.domRestrict f = G.domRestrict g ↔ Set.EqOn f g G) :=
  ⟨fun f z => ⟨f z, rfl, fun _ h => h.symm⟩, fun _ _ => Set.domRestrict_eq_domRestrict_iff⟩

/-- Beck Definition 2.1.10 (CX-020). Image `g(G) = {g z : z ∈ G}`, and the composition `(f ∘ g)(z) = f (g z)`
is defined on `G` when `g(G) ⊆ H` (and `f` is defined on `H`). -/
@[kb "beck2025" "Definition 2.1.10, p. 35"]
theorem image_and_composition (G H K : Set ℂ) (f g : ℂ → ℂ) :
    (g '' G = {w | ∃ z ∈ G, g z = w}) ∧
    (g '' G ⊆ H ↔ Set.MapsTo g G H) ∧
    (Set.MapsTo g G H → Set.MapsTo f H K → Set.MapsTo (f ∘ g) G K ∧ ∀ z ∈ G, (f ∘ g) z = f (g z)) :=
  ⟨rfl, Set.image_subset_iff, fun hg hf => ⟨hf.comp hg, fun _ _ => rfl⟩⟩

/-- Beck Definition 2.2.7 (CX-030). One-to-one, onto, bijection, inverse function. -/
@[kb "beck2025" "Definition 2.2.7, p. 38"]
theorem injective_surjective_bijective_inverse (G H : Set ℂ) (f : ℂ → ℂ) :
    (Set.InjOn f G ↔ ∀ z₁ ∈ G, ∀ z₂ ∈ G, f z₁ = f z₂ → z₁ = z₂) ∧
    (Set.SurjOn f G H ↔ ∀ w ∈ H, ∃ z ∈ G, f z = w) ∧
    (Set.BijOn f G H ↔ Set.MapsTo f G H ∧ ∀ w ∈ H, ∃! z, z ∈ G ∧ f z = w) ∧
    (Set.BijOn f G H → ∃ g : ℂ → ℂ, Set.InvOn g f G H ∧ Set.BijOn g H G) := by
  refine ⟨Iff.rfl, ?_, ?_, ?_⟩
  · exact ⟨fun h w hw => by simpa using h hw, fun h w hw => by simpa using h w hw⟩
  · constructor
    · intro h
      refine ⟨h.mapsTo, fun w hw => ?_⟩
      obtain ⟨z, hz, rfl⟩ := h.surjOn hw
      exact ⟨z, ⟨hz, rfl⟩, fun y hy => h.injOn hy.1 hz hy.2⟩
    · rintro ⟨hm, h⟩
      refine ⟨hm, fun a ha b hb hab => ?_, fun w hw => ?_⟩
      · obtain ⟨z, _, hz⟩ := h (f a) (hm ha)
        exact (hz a ⟨ha, rfl⟩).trans (hz b ⟨hb, hab.symm⟩).symm
      · obtain ⟨z, hz, _⟩ := h w hw
        exact ⟨z, hz.1, hz.2⟩
  · intro h
    exact ⟨Function.invFunOn f G, h.invOn_invFunOn, Set.BijOn.symm h.invOn_invFunOn.symm h⟩

/-- Beck Definition 3.2.1(a) (CX-039). `lim_{z→z₀} f(z) = ∞`. -/
@[kb "beck2025" "Definition 3.2.1, p. 51"]
theorem tendsto_infty_at_point_iff (G : Set ℂ) (f : ℂ → ℂ) (z₀ : ℂ) :
    Tendsto f (𝓝[G \ {z₀}] z₀) (Bornology.cobounded ℂ) ↔
      ∀ M > 0, ∃ δ > 0, ∀ z ∈ G, 0 < ‖z - z₀‖ → ‖z - z₀‖ < δ → M < ‖f z‖ := by
  rw [(nhdsWithin_basis_ball (s := G \ {z₀}) (x := z₀)).tendsto_iff
    (hasBasis_cobounded_compl_closedBall (0 : ℂ))]
  constructor
  · intro h M hM
    obtain ⟨δ, hδ, hz⟩ := h M trivial
    refine ⟨δ, hδ, fun z hzG h0 hlt => ?_⟩
    have := hz (x := z) ⟨by simpa [dist_eq_norm] using hlt, hzG,
      by simpa [sub_eq_zero] using h0.ne'⟩
    simpa using this
  · intro h M _
    obtain ⟨δ, hδ, hz⟩ := h (max M 1) (by positivity)
    refine ⟨δ, hδ, fun z hz' => ?_⟩
    have h1 := hz z hz'.2.1 (norm_pos_iff.2 (sub_ne_zero.2 hz'.2.2))
      (by simpa [dist_eq_norm] using hz'.1)
    simpa using lt_of_le_of_lt (le_max_left _ _) h1

/-- Beck Definition 3.2.1(b) (CX-039). `lim_{z→∞} f(z) = L`. -/
@[kb "beck2025" "Definition 3.2.1, p. 51"]
theorem tendsto_at_infty_iff (G : Set ℂ) (f : ℂ → ℂ) (L : ℂ) :
    Tendsto f (Bornology.cobounded ℂ ⊓ 𝓟 G) (𝓝 L) ↔
      ∀ ε > 0, ∃ N > 0, ∀ z ∈ G, N < ‖z‖ → ‖f z - L‖ < ε := by
  rw [((hasBasis_cobounded_compl_closedBall (0 : ℂ)).inf_principal G).tendsto_iff
    nhds_basis_ball]
  constructor
  · intro h ε hε
    obtain ⟨N, -, hz⟩ := h ε hε
    refine ⟨max N 1, by positivity, fun z hzG hlt => ?_⟩
    have := hz (x := z) ⟨by simpa using lt_of_le_of_lt (le_max_left _ _) hlt, hzG⟩
    simpa [dist_eq_norm] using this
  · intro h ε hε
    obtain ⟨N, -, hz⟩ := h ε hε
    refine ⟨N, trivial, fun z hz' => ?_⟩
    simpa [dist_eq_norm] using hz z hz'.2 (by simpa using hz'.1)

/-- Beck Definition 3.2.1(c) (CX-039). `lim_{z→∞} f(z) = ∞`. -/
@[kb "beck2025" "Definition 3.2.1, p. 51"]
theorem tendsto_infty_at_infty_iff (G : Set ℂ) (f : ℂ → ℂ) :
    Tendsto f (Bornology.cobounded ℂ ⊓ 𝓟 G) (Bornology.cobounded ℂ) ↔
      ∀ M > 0, ∃ N > 0, ∀ z ∈ G, N < ‖z‖ → M < ‖f z‖ := by
  rw [((hasBasis_cobounded_compl_closedBall (0 : ℂ)).inf_principal G).tendsto_iff
    (hasBasis_cobounded_compl_closedBall (0 : ℂ))]
  constructor
  · intro h M hM
    obtain ⟨N, -, hz⟩ := h M trivial
    refine ⟨max N 1, by positivity, fun z hzG hlt => ?_⟩
    have := hz (x := z) ⟨by simpa using lt_of_le_of_lt (le_max_left _ _) hlt, hzG⟩
    simpa using this
  · intro h M _
    obtain ⟨N, hN, hz⟩ := h (max M 1) (by positivity)
    refine ⟨N, trivial, fun z hz' => ?_⟩
    have h1 := hz z hz'.2 (by simpa using hz'.1)
    simpa using lt_of_le_of_lt (le_max_left _ _) h1

/-- Beck Definition 3.2.4 (CX-040). The arithmetic rules of the extended plane `ℂ ∪ {∞}` as limits in `ℂ`:
`∞ + a = ∞`, `∞ · a = ∞` (`a ≠ 0`), `∞ · ∞ = ∞`, `a / ∞ = 0`, `a / 0 = ∞` (`a ≠ 0`). -/
@[kb "beck2025" "Definition 3.2.4, p. 52"]
theorem extended_plane_rules (a : ℂ) :
    Tendsto (fun z : ℂ => z + a) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) ∧
    (a ≠ 0 → Tendsto (fun z : ℂ => z * a) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ)) ∧
    Tendsto (fun p : ℂ × ℂ => p.1 * p.2) (Bornology.cobounded ℂ ×ˢ Bornology.cobounded ℂ)
      (Bornology.cobounded ℂ) ∧
    Tendsto (fun z : ℂ => a / z) (Bornology.cobounded ℂ) (𝓝 0) ∧
    (a ≠ 0 → Tendsto (fun z : ℂ => a / z) (𝓝[≠] 0) (Bornology.cobounded ℂ)) := by
  have hnorm : ∀ {α : Type} {l : Filter α} (g : α → ℂ),
      Tendsto (fun x => ‖g x‖) l atTop → Tendsto g l (Bornology.cobounded ℂ) := fun g h => by
    rw [← comap_norm_atTop, tendsto_comap_iff]; exact h
  have h_mul : a ≠ 0 → Tendsto (fun z : ℂ => z * a) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) :=
    fun ha => hnorm _ (by
      simp only [norm_mul]
      exact tendsto_norm_cobounded_atTop.atTop_mul_const (norm_pos_iff.2 ha))
  refine ⟨?_, h_mul, ?_, ?_, fun ha => ?_⟩
  · exact (tendsto_add_const_cobounded a)
  · exact hnorm _ (by
      simp only [norm_mul]
      exact (tendsto_norm_cobounded_atTop.comp tendsto_fst).atTop_mul_atTop₀
        (tendsto_norm_cobounded_atTop.comp tendsto_snd) |>.mono_left le_rfl)
  · simpa [div_eq_mul_inv] using (tendsto_inv₀_cobounded (α := ℂ)).const_mul a
  · have h2 : Tendsto (fun z : ℂ => a * z) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
      simpa [mul_comm] using h_mul ha
    simp only [div_eq_mul_inv]
    exact h2.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ))

end UndergradKB.ComplexAnalysis.Course.BeckDefs
