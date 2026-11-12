import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Piecewise
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Compactness.Compact
import UndergradKB.Common.Attr

/-!
# Tietze extension and extension from dense subspaces

Normality of a space is characterised by the extension of continuous maps from closed subspaces
into `[0,1]`, `(0,1)`, `ℝ`, or any infinite retract of a power of `ℝ`.  Mathlib has the extension
direction (class `TietzeExtension`); the converse direction is proved here once and for all in
`normalSpace_of_extension_property`.  A Hausdorff space is normal in the book's sense exactly when
it is `T4Space`; each characterisation is stated for `NormalSpace` and for the book's form.

The last result is the criterion for extending a map from a dense subspace into a compact Hausdorff
space.
-/

open Topology Set Filter unitInterval

namespace UndergradKB.Topology

universe u v

/-- A Hausdorff space is normal in the book's sense iff it is `T4Space`. -/
theorem t4Space_iff_normalSpace (X : Type u) [TopologicalSpace X] [T2Space X] :
    T4Space X ↔ NormalSpace X :=
  ⟨fun _ => inferInstance, fun _ => {}⟩

/-- The converse direction of all Tietze-type characterisations: if the continuous maps from every
closed subspace into a Hausdorff space `Y` with two distinct points extend over `X`, then `X` is
normal (separate `A` and `B` by extending the map equal to `a` on `A` and `b` on `B`). -/
theorem normalSpace_of_extension_property {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] {a b : Y} (hab : a ≠ b)
    (h : ∀ S : Set X, IsClosed S → ∀ φ : C(S, Y), ∃ Φ : C(X, Y), Φ.restrict S = φ) :
    NormalSpace X := by
  classical
  refine ⟨fun A B hA hB hAB => ?_⟩
  let S : Set X := A ∪ B
  have hS : IsClosed S := hA.union hB
  have hcl : IsClosed {x : S | x.1 ∈ A} := hA.preimage continuous_subtype_val
  have hop : IsOpen {x : S | x.1 ∈ A} := by
    have : {x : S | x.1 ∈ A} = {x : S | x.1 ∈ B}ᶜ := by
      ext x
      constructor
      · intro hxA hxB
        exact disjoint_left.mp hAB hxA hxB
      · intro hnB
        rcases x.2 with hx | hx
        · exact hx
        · exact absurd hx hnB
    rw [this]
    exact (hB.preimage continuous_subtype_val).isOpen_compl
  have hφ : Continuous (fun x : S => if x.1 ∈ A then a else b) := by
    apply Continuous.if _ continuous_const continuous_const
    intro x hx
    have hclo : IsClopen {x : S | x.1 ∈ A} := ⟨hcl, hop⟩
    rw [hclo.frontier_eq] at hx
    exact absurd hx (notMem_empty x)
  obtain ⟨Φ, hΦ⟩ := h S hS ⟨_, hφ⟩
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
  have hA' : ∀ x ∈ A, Φ x = a := by
    intro x hx
    have := DFunLike.congr_fun hΦ ⟨x, Or.inl hx⟩
    simpa [hx] using this
  have hB' : ∀ x ∈ B, Φ x = b := by
    intro x hx
    have := DFunLike.congr_fun hΦ ⟨x, Or.inr hx⟩
    simpa [disjoint_right.mp hAB hx] using this
  exact ⟨Φ ⁻¹' U, Φ ⁻¹' V, hU.preimage Φ.continuous, hV.preimage Φ.continuous,
    fun x hx => by simpa [hA' x hx] using haU, fun x hx => by simpa [hB' x hx] using hbV,
    hUV.preimage Φ⟩

/-- Morris, Topology Without Tears, Proposition 10.3.43 (TP-306). A space is normal iff every
continuous map from a closed subspace into `[0,1]` extends continuously to the whole space. -/
@[kb "morris2024" "Proposition 10.3.43, p. 291"]
theorem normalSpace_iff_extension_unitInterval (X : Type u) [TopologicalSpace X] :
    NormalSpace X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, I), ∃ Φ : C(X, I), Φ.restrict S = φ := by
  constructor
  · intro _ S hS φ
    exact ContinuousMap.exists_restrict_eq hS φ
  · intro h
    exact normalSpace_of_extension_property (zero_ne_one : (0 : I) ≠ 1) h

/-- Morris, Topology Without Tears, Proposition 10.3.43 (TP-306), in the book's form for a
Hausdorff space. -/
@[kb "morris2024" "Proposition 10.3.43, p. 291"]
theorem t4Space_iff_extension_unitInterval (X : Type u) [TopologicalSpace X] [T2Space X] :
    T4Space X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, I), ∃ Φ : C(X, I), Φ.restrict S = φ :=
  (t4Space_iff_normalSpace X).trans (normalSpace_iff_extension_unitInterval X)

/-- Morris, Topology Without Tears, Proposition 10.3.44 (TP-307). A space is normal iff every
continuous map from a closed subspace into the open interval `(0,1)` extends continuously. -/
@[kb "morris2024" "Proposition 10.3.44, p. 293"]
theorem normalSpace_iff_extension_Ioo (X : Type u) [TopologicalSpace X] :
    NormalSpace X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, Ioo (0 : ℝ) 1),
        ∃ Φ : C(X, Ioo (0 : ℝ) 1), Φ.restrict S = φ := by
  constructor
  · intro _ S hS φ
    obtain ⟨g, hg, hgS⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
      (Y := X) (t := Ioo (0 : ℝ) 1)
      ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp φ) (fun x => (φ x).2)
      ⟨1 / 2, by norm_num⟩ hS
    refine ⟨⟨fun x => ⟨g x, hg x⟩, g.continuous.subtype_mk _⟩, ?_⟩
    ext x
    simpa using DFunLike.congr_fun hgS x
  · intro h
    have hne : (⟨1 / 3, by norm_num, by norm_num⟩ : Ioo (0 : ℝ) 1) ≠ ⟨2 / 3, by norm_num, by norm_num⟩ := by
      intro h'
      have := congrArg Subtype.val h'
      norm_num at this
    exact normalSpace_of_extension_property hne h

/-- Morris, Topology Without Tears, Proposition 10.3.44 (TP-307), in the book's form for a
Hausdorff space. -/
@[kb "morris2024" "Proposition 10.3.44, p. 293"]
theorem t4Space_iff_extension_Ioo (X : Type u) [TopologicalSpace X] [T2Space X] :
    T4Space X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, Ioo (0 : ℝ) 1),
        ∃ Φ : C(X, Ioo (0 : ℝ) 1), Φ.restrict S = φ :=
  (t4Space_iff_normalSpace X).trans (normalSpace_iff_extension_Ioo X)

/-- Morris, Topology Without Tears, Proposition 10.3.46 (TP-309). A space is normal iff every
continuous real-valued map on a closed subspace extends continuously to the whole space. -/
@[kb "morris2024" "Proposition 10.3.46, p. 294"]
theorem normalSpace_iff_extension_real (X : Type u) [TopologicalSpace X] :
    NormalSpace X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, ℝ), ∃ Φ : C(X, ℝ), Φ.restrict S = φ := by
  constructor
  · intro _ S hS φ
    exact ContinuousMap.exists_restrict_eq hS φ
  · intro h
    exact normalSpace_of_extension_property (zero_ne_one : (0 : ℝ) ≠ 1) h

/-- Morris, Topology Without Tears, Proposition 10.3.46 (TP-309), in the book's form for a
Hausdorff space. -/
@[kb "morris2024" "Proposition 10.3.46, p. 294"]
theorem t4Space_iff_extension_real (X : Type u) [TopologicalSpace X] [T2Space X] :
    T4Space X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, ℝ), ∃ Φ : C(X, ℝ), Φ.restrict S = φ :=
  (t4Space_iff_normalSpace X).trans (normalSpace_iff_extension_real X)

/-! ### Retracts -/

/-- Morris, Topology Without Tears, Definition 10.3.47 (TP-310). A subspace `Y` of `X` is a
retract if some continuous map `X → Y` fixes every point of `Y`. -/
@[kb "morris2024" "Definition 10.3.47, p. 294"]
def IsRetractSubspace {X : Type u} [TopologicalSpace X] (Y : Set X) : Prop :=
  ∃ r : C(X, Y), ∀ y : Y, r y = y

/-- Morris, Topology Without Tears, Example 10.3.48 (TP-310). The closed interval `[a, b]` is a
retract of `ℝ`; in particular `[0, 1]` is. -/
@[kb "morris2024" "Example 10.3.48, p. 294"]
theorem isRetractSubspace_Icc (a b : ℝ) (hab : a ≤ b) : IsRetractSubspace (Icc a b) :=
  ⟨⟨Set.projIcc a b hab, continuous_projIcc⟩, fun y => projIcc_val hab y⟩

/-- The unit interval `[0,1]` is a retract of `ℝ` (the case of `isRetractSubspace_Icc`). -/
theorem isRetractSubspace_unitInterval : IsRetractSubspace (Icc (0 : ℝ) 1) :=
  isRetractSubspace_Icc 0 1 zero_le_one

/-- Morris, Topology Without Tears, Lemma 10.3.49 (basis of TP-313). A retract of a space with the
Tietze extension property has the Tietze extension property. -/
theorem tietzeExtension_of_isRetractSubspace {Z : Type v} [TopologicalSpace Z]
    [TietzeExtension.{u, v} Z] {Y : Set Z} (hY : IsRetractSubspace Y) :
    TietzeExtension.{u, v} Y := by
  obtain ⟨r, hr⟩ := hY
  exact TietzeExtension.of_retract (⟨Subtype.val, continuous_subtype_val⟩ : C(Y, Z)) r
    (by ext y; exact congrArg Subtype.val (hr y))

/-- Morris, Topology Without Tears, Theorem 10.3.51 (Tietze Extension Theorem) (TP-313). If `Y` is
an infinite retract of a power `ℝ^J`, then a space is normal iff continuous maps from closed
subspaces into `Y` extend continuously. -/
@[kb "morris2024" "Theorem 10.3.51, p. 295"]
theorem normalSpace_iff_extension_retract (X : Type u) [TopologicalSpace X] (J : Type u)
    (Y : Set (J → ℝ)) (hY : IsRetractSubspace Y) [Infinite Y] :
    NormalSpace X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, Y), ∃ Φ : C(X, Y), Φ.restrict S = φ := by
  constructor
  · intro _ S hS φ
    have : TietzeExtension.{u, u} Y := tietzeExtension_of_isRetractSubspace hY
    exact ContinuousMap.exists_restrict_eq hS φ
  · intro h
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Y
    exact normalSpace_of_extension_property hab h

/-- Morris, Topology Without Tears, Theorem 10.3.51 (TP-313), in the book's form for a Hausdorff
space. -/
@[kb "morris2024" "Theorem 10.3.51, p. 295"]
theorem t4Space_iff_extension_retract (X : Type u) [TopologicalSpace X] [T2Space X] (J : Type u)
    (Y : Set (J → ℝ)) (hY : IsRetractSubspace Y) [Infinite Y] :
    T4Space X ↔
      ∀ S : Set X, IsClosed S → ∀ φ : C(S, Y), ∃ Φ : C(X, Y), Φ.restrict S = φ :=
  (t4Space_iff_normalSpace X).trans (normalSpace_iff_extension_retract X J Y hY)

/-! ### Extension from a dense subspace -/

/-- Morris, Topology Without Tears, Proposition 10.3.53 (TP-314). Let `S` be a dense subspace of
`X` and `φ : S → K` continuous into a compact Hausdorff space.  Then `φ` extends continuously to
`X` iff, for all disjoint closed `C₁, C₂ ⊆ K`, the closures in `X` of `φ⁻¹ C₁` and `φ⁻¹ C₂` are
disjoint.  (The book leaves tacit that `C₁` and `C₂` are disjoint.) -/
@[kb "morris2024" "Proposition 10.3.53, p. 297"]
theorem exists_continuous_extension_iff {X : Type u} [TopologicalSpace X] {S : Set X}
    (hS : Dense S) {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (φ : S → K) (hφ : Continuous φ) :
    (∃ Φ : X → K, Continuous Φ ∧ ∀ s : S, Φ s = φ s) ↔
      ∀ C₁ C₂ : Set K, IsClosed C₁ → IsClosed C₂ → Disjoint C₁ C₂ →
        Disjoint (closure (((↑) : S → X) '' (φ ⁻¹' C₁)))
          (closure (((↑) : S → X) '' (φ ⁻¹' C₂))) := by
  constructor
  · rintro ⟨Φ, hΦ, hext⟩ C₁ C₂ h₁ h₂ hd
    have key : ∀ C : Set K, IsClosed C →
        closure (((↑) : S → X) '' (φ ⁻¹' C)) ⊆ Φ ⁻¹' C := by
      intro C hC
      apply closure_minimal _ (hC.preimage hΦ)
      rintro _ ⟨s, hs, rfl⟩
      show Φ s ∈ C
      rw [hext]
      exact hs
    exact (hd.preimage Φ).mono (key C₁ h₁) (key C₂ h₂)
  · intro H
    have di : IsDenseInducing ((↑) : S → X) := hS.isDenseInducing_val
    have hlim : ∀ x : X, ∃ c, Tendsto φ (comap ((↑) : S → X) (𝓝 x)) (𝓝 c) := by
      intro x
      have : (comap ((↑) : S → X) (𝓝 x)).NeBot :=di.comap_nhds_neBot x
      obtain ⟨c, hc⟩ := exists_clusterPt_of_compactSpace (map φ (comap ((↑) : S → X) (𝓝 x)))
      refine ⟨c, tendsto_nhds_of_unique_mapClusterPt ?_⟩
      -- membership in the closure of the preimage of a neighbourhood of a cluster point
      have key : ∀ (y : K), MapClusterPt y (comap ((↑) : S → X) (𝓝 x)) φ → ∀ C : Set K,
          C ∈ 𝓝 y → x ∈ closure (((↑) : S → X) '' (φ ⁻¹' C)) := by
        intro y hy C hC
        rw [mem_closure_iff_frequently]
        have h1 := frequently_comap.mp (mapClusterPt_iff_frequently.mp hy C hC)
        exact h1.mono fun b ⟨a, hab, ha⟩ => ⟨a, ha, hab⟩
      intro d hd
      by_contra hne
      obtain ⟨U, V, hU, hV, hcU, hdV, hUV⟩ := t2_separation (Ne.symm hne)
      obtain ⟨W, hW, hcW, hWU⟩ := normal_exists_closure_subset
        (isClosed_singleton (x := c)) hU (singleton_subset_iff.mpr hcU)
      have hdisj : Disjoint (closure W) (closure V) :=
        (hUV.closure_right hU).mono_left hWU
      have hcW' : closure W ∈ 𝓝 c := mem_of_superset (hW.mem_nhds (singleton_subset_iff.mp hcW)) subset_closure
      have hdV' : closure V ∈ 𝓝 d := mem_of_superset (hV.mem_nhds hdV) subset_closure
      have := H (closure W) (closure V) isClosed_closure isClosed_closure hdisj
      exact disjoint_left.mp this (key c hc _ hcW') (key d hd _ hdV')
    exact ⟨di.extend φ, di.continuous_extend hlim, fun s => di.extend_eq hφ s⟩

end UndergradKB.Topology
