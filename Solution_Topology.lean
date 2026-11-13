/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Topology.PeriodThree
import UndergradKB.Topology.Peano
import UndergradKB.Topology.BanachMazur
import UndergradKB.Topology.ClosedSubgroupsRn
import UndergradKB.Topology.ClosedSubgroupsRn2
import UndergradKB.Topology.Wallman
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.DualityTheorem
import UndergradKB.Topology.StructureTheorems
import UndergradKB.Topology.SharkovskiiOdd4
import UndergradKB.Topology.SharkovskiiOdd7

/-!
# Proofs of the topology headline statements

Proves the statements of `Challenge_Topology.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Topology.lean`.
-/

namespace UndergradKB.Headlines.Topology

universe u

open Function Set Topology UndergradKB.Topology

theorem period_three {f : ℝ → ℝ} (hf : Continuous f)
    (h3 : ∃ a, minimalPeriod f a = 3) : ∀ n : ℕ, 0 < n → ∃ x, minimalPeriod f x = n :=
  UndergradKB.Topology.exists_minimalPeriod_eq_of_minimalPeriod_three hf h3

theorem peano_curve (n : ℕ) (_hn : 0 < n) :
    ∃ ψ : unitInterval → (Fin n → unitInterval), Continuous ψ ∧ Function.Surjective ψ :=
  UndergradKB.Topology.peano_exists_continuous_surjective_cube n _hn

theorem banach_mazur (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] : Nonempty (E →ₗᵢ[ℝ] C(unitInterval, ℝ)) :=
  UndergradKB.Topology.banach_mazur E

theorem closed_subgroup_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ p q : ℕ, Nonempty (G ≃ₜ+ ((Fin p → ℝ) × (Fin q → ℤ))) :=
  UndergradKB.Topology.ClosedSubgroupsRn.closed_subgroup_equiv_real_pi_prod_int_pi G hG

theorem quotient_closed_subgroup_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : AddSubgroup E) (hG : IsClosed (G : Set E)) :
    ∃ c d : ℕ, Nonempty ((E ⧸ G) ≃ₜ+ ((Fin c → ℝ) × (Fin d → AddCircle (1 : ℝ)))) :=
  (UndergradKB.Topology.ClosedSubgroupsRn.quotient_closed_subgroup_equiv G hG).imp fun _ ⟨d, _, h⟩ => ⟨d, h⟩

theorem closed_subgroup_torus_equiv {n : ℕ} (H : AddSubgroup (Fin n → AddCircle (1 : ℝ)))
    (hH : IsClosed (H : Set (Fin n → AddCircle (1 : ℝ)))) :
    ∃ (a : ℕ) (F : AddSubgroup H), Finite F ∧
      Nonempty (H ≃ₜ+ ((Fin a → AddCircle (1 : ℝ)) × F)) :=
  UndergradKB.Topology.ClosedSubgroupsRn2.closed_subgroup_torus_equiv H hH

theorem wallman_compactification (X : Type*) [TopologicalSpace X] [T1Space X] :
    CompactSpace (Wallman X) ∧ T1Space (Wallman X) ∧ Topology.IsEmbedding (Wallman.pt : X → Wallman X) ∧
      DenseRange (Wallman.pt : X → Wallman X) ∧
      ∀ (K : Type _) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : X → K),
        Continuous f → ∃ g : Wallman X → K, Continuous g ∧ ∀ x, g (Wallman.pt x) = f x :=
  UndergradKB.Topology.Wallman.wallman_compactification X

theorem normalSpace_iff_wallman_eq_stoneCech {X : Type*} [TopologicalSpace X] [T1Space X] :
    NormalSpace X ↔ ∃ e : Wallman X ≃ₜ StoneCech X, ∀ x, e (Wallman.pt x) = stoneCechUnit x :=
  UndergradKB.Topology.Wallman.normalSpace_iff_exists_homeomorph_stoneCech

theorem pontryagin_duality_real_circle_int (a b c : ℕ) :
    DualityHolds (((Fin a → Multiplicative ℝ) × (Fin b → Circle)) × (Fin c → Multiplicative ℤ)) :=
  UndergradKB.Topology.dualityHolds_real_circle_int_pow a b c

theorem pontryagin_van_kampen {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] : DualityHolds G :=
  UndergradKB.Topology.LCA.dualityHolds_of_LCA

theorem sharkovskii {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n)
    (hper : ∃ x, minimalPeriod f x = n) {k : ℕ} (hk : 0 < k) (hlt : SharkovskiiLT n k) :
    ∃ y, minimalPeriod f y = k :=
  UndergradKB.Topology.sharkovskii_theorem hf hn hper hk hlt

theorem converse_sharkovskii {n : ℕ} (hn : 0 < n) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = n) ∧
      ∀ l, 0 < l → SharkovskiiLT l n → ¬ ∃ x, minimalPeriod f x = l :=
  UndergradKB.Topology.converse_sharkovskii hn

theorem lca_principal_structure {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ∃ S : Subgroup G, IsOpen (S : Set G) ∧
      ∃ (a : ℕ) (K : Type u) (_ : CommGroup K) (_ : TopologicalSpace K),
        IsTopologicalGroup K ∧ CompactSpace K ∧ T2Space K ∧
          Nonempty (S ≃ₜ* (Fin a → Multiplicative ℝ) × K) :=
  UndergradKB.Topology.exists_open_subgroup_equiv_real_compact

theorem lca_connected_structure {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [ConnectedSpace G] :
    ∃ (a : ℕ) (K : Type u) (_ : CommGroup K) (_ : TopologicalSpace K),
      IsTopologicalGroup K ∧ CompactSpace K ∧ T2Space K ∧ ConnectedSpace K ∧
        Nonempty (G ≃ₜ* (Fin a → Multiplicative ℝ) × K) :=
  UndergradKB.Topology.exists_equiv_real_compact_of_connectedSpace

end UndergradKB.Headlines.Topology
