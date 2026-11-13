import UndergradKB.Topology.LCASeparation
import UndergradKB.Topology.ClassicalDuals
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-!
# Wave 2: annihilators and closures of subgroups of `ℝⁿ`, general case (Morris, A5.14.5-7)

Uses that `ℝⁿ` is a locally compact Hausdorff abelian group, so a point outside a closed subgroup is
separated from it by a character (`LCA.exists_char_trivial_on_ne_of_LCA`).
-/

open Set Real
open scoped Topology

namespace UndergradKB.Topology

namespace Kron2c

/-- `t ↦ exp (2 π i t)`. -/
noncomputable def eC (t : ℝ) : Circle := Circle.exp (2 * π * t)

theorem eC_eq_one_iff {t : ℝ} : eC t = 1 ↔ ∃ k : ℤ, t = k := by
  unfold eC
  rw [Circle.exp_eq_one]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_right_cancel₀ (show (2 * π) ≠ 0 by positivity) ?_⟩
    linarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem prod_eC {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    ∏ j ∈ s, eC (c j) = eC (∑ j ∈ s, c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eC]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih]
    unfold eC
    rw [mul_add, Circle.exp_add]

end Kron2c

open Kron2c

/-- Every character of `ℝⁿ` (written multiplicatively) is `x ↦ exp (2 π i (y | x))`. -/
theorem exists_pairing_form {n : ℕ} (χ : PontryaginDual (Multiplicative (Fin n → ℝ))) :
    ∃ y : Fin n → ℝ, ∀ x : Fin n → ℝ,
      χ (Multiplicative.ofAdd x) = Circle.exp (2 * π * ∑ j, y j * x j) := by
  classical
  let ψ : Fin n → PontryaginDual (Multiplicative ℝ) := fun j =>
    { toFun := fun t => χ (Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd t)))
      map_one' := by simp
      map_mul' := fun s t => by
        show χ (Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd s + Multiplicative.toAdd t)))
          = _
        rw [Pi.single_add, ofAdd_add, map_mul]
      continuous_toFun := by
        refine χ.continuous.comp (continuous_ofAdd.comp ?_)
        exact (continuous_const.update j continuous_id).comp continuous_toAdd }
  choose t ht using fun j => dual_real_apply (ψ j)
  refine ⟨t, fun x => ?_⟩
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  have h1 : χ (Multiplicative.ofAdd x) = ∏ j, eC (t j * x j) := by
    conv_lhs => rw [hx]
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := ht j (x j)
    have e : eC (t j * x j) = Circle.exp (2 * π * t j * x j) := by
      unfold eC; congr 1; ring
    rw [e, ← this]
    rfl
  rw [h1, prod_eC]
  rfl

/-- Morris, Topology Without Tears, Proposition A5.14.7 (TP-622). A point `x` lies in the closure of a
subgroup `G` of `ℝⁿ` iff `(y | x)` is an integer for every `y ∈ ℝⁿ` such that `(y | g)` is an integer for
all `g ∈ G`. -/
@[kb "morris2024" "Proposition A5.14.7, p. 604"]
theorem mem_closure_iff_integral_pairing_general {n : ℕ} (G : AddSubgroup (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ closure (G : Set (Fin n → ℝ)) ↔
      ∀ y : Fin n → ℝ, (∀ g ∈ G, ∃ k : ℤ, ∑ j, y j * g j = k) → ∃ k : ℤ, ∑ j, y j * x j = k := by
  classical
  constructor
  · intro hx y hy
    have hcont : Continuous fun z : Fin n → ℝ => ∑ j, y j * z j := by fun_prop
    have hclosed : IsClosed ((fun z : Fin n → ℝ => ∑ j, y j * z j) ⁻¹' range ((↑) : ℤ → ℝ)) :=
      Int.isClosedEmbedding_coe_real.isClosed_range.preimage hcont
    have hsub : (G : Set (Fin n → ℝ)) ⊆
        (fun z : Fin n → ℝ => ∑ j, y j * z j) ⁻¹' range ((↑) : ℤ → ℝ) := by
      intro g hg
      obtain ⟨k, hk⟩ := hy g hg
      exact ⟨k, hk.symm⟩
    obtain ⟨k, hk⟩ := closure_minimal hsub hclosed hx
    exact ⟨k, hk.symm⟩
  · intro h
    by_contra hx
    haveI : LocallyCompactSpace (Multiplicative (Fin n → ℝ)) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → ℝ))
    haveI : T2Space (Multiplicative (Fin n → ℝ)) := inferInstanceAs (T2Space (Fin n → ℝ))
    let H : Subgroup (Multiplicative (Fin n → ℝ)) := AddSubgroup.toSubgroup G.topologicalClosure
    have hHc : IsClosed (H : Set (Multiplicative (Fin n → ℝ))) :=
      (AddSubgroup.isClosed_topologicalClosure G :)
    have hxH : Multiplicative.ofAdd x ∉ H := by
      show x ∉ (G.topologicalClosure : Set (Fin n → ℝ))
      rw [AddSubgroup.topologicalClosure_coe]
      exact hx
    obtain ⟨χ, hχH, hχx⟩ := LCA.exists_char_trivial_on_ne_of_LCA H hHc hxH
    obtain ⟨y, hy⟩ := exists_pairing_form χ
    obtain ⟨k, hk⟩ := h y (fun g hg => by
      have h1 := hχH (Multiplicative.ofAdd g) (G.le_topologicalClosure hg)
      rw [hy, Circle.exp_eq_one] at h1
      obtain ⟨m, hm⟩ := h1
      refine ⟨m, mul_left_cancel₀ (show (2 * π) ≠ 0 by positivity) ?_⟩
      rw [hm]; ring)
    apply hχx
    rw [hy, Circle.exp_eq_one]
    exact ⟨k, by rw [hk]; ring⟩

/-- The annihilator in `ℝⁿ` of a set `G`: the vectors `y` with `(y | x)` an integer for all `x ∈ G`. -/
def realAnnihilator {n : ℕ} (G : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ G, ∃ k : ℤ, ∑ j, y j * x j = k}

/-- Morris, Topology Without Tears, Proposition A5.14.6 (TP-621). The double annihilator of a subgroup
`G` of `ℝⁿ` is the closure of `G` (so `G` itself when `G` is closed). -/
@[kb "morris2024" "Proposition A5.14.6, p. 604"]
theorem realAnnihilator_realAnnihilator {n : ℕ} (G : AddSubgroup (Fin n → ℝ)) :
    realAnnihilator (realAnnihilator (G : Set (Fin n → ℝ))) = closure (G : Set (Fin n → ℝ)) := by
  ext x
  rw [mem_closure_iff_integral_pairing_general]
  have hc : ∀ y : Fin n → ℝ, ∑ j, x j * y j = ∑ j, y j * x j := fun y =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  constructor
  · intro h y hy
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, by rw [← hc, hk]⟩
  · intro h y hy
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, by rw [hc, hk]⟩

end UndergradKB.Topology
