import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.PNat.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris: further examples and remarks (wave 3, part 2)

Thin theorems for examples and remarks of Morris, *Topology Without Tears*, from Chapters 9-12 and
the appendices: a non-metrizable continuous image of the Cantor space, `sin (1/x)` has no continuous
extension, pointwise but not uniform convergence, orders, counting examples, topological groups,
filters and dynamics.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace Metric

section Examples

/-- Morris, Topology Without Tears, Remark 9.5.5. The converse of the theorem on continuous images of
the Cantor space fails: the evaluation at `0` maps the Cantor space `ℕ → Bool` continuously onto the
two-point indiscrete space, which is compact but not metrizable. -/
@[kb "morris2024" "Remark 9.5.5, p. 251"]
theorem morris_ex_9_5_5 :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (f : (ℕ → Bool) → Y),
      Continuous f ∧ Function.Surjective f ∧ ¬ MetrizableSpace Y := by
  refine ⟨Bool, ⊤, fun x => x 0, continuous_top, fun b => ⟨fun _ => b, rfl⟩, ?_⟩
  intro h
  let _ : TopologicalSpace Bool := ⊤
  have h2 : T2Space Bool := inferInstance
  obtain ⟨U, V, hU, hV, ht, hf, hUV⟩ := t2_separation (X := Bool) (x := true) (y := false) (by decide)
  have hc : ∀ s : Set Bool, IsOpen s → s = ∅ ∨ s = univ := fun s hs => (isOpen_top_iff s).1 hs
  rcases hc U hU with rfl | rfl
  · exact ht
  · exact Set.disjoint_left.1 hUV ht (by
      rcases hc V hV with rfl | rfl
      · exact hf
      · trivial)

/-- Morris, Topology Without Tears, Remark 9.5.11. Discrete spaces, `ℝ` and the euclidean plane are
locally connected. -/
@[kb "morris2024" "Remark 9.5.11, p. 253"]
theorem morris_ex_9_5_11 :
    (∀ (X : Type) [TopologicalSpace X] [DiscreteTopology X], LocallyConnectedSpace X) ∧
    LocallyConnectedSpace ℝ ∧ LocallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) :=
  ⟨fun _ _ _ => inferInstance, inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, Remark 10.4.11. The continuous map `x ↦ sin (1/x)` on `(0, 1]`
has no continuous extension to `[0, 1]`; hence `[0, 1]` is not the Stone-Cech compactification of
`(0, 1]`. -/
@[kb "morris2024" "Remark 10.4.11, p. 333"]
theorem morris_ex_10_4_11 :
    ¬ ∃ F : ℝ → ℝ, ContinuousWithinAt F (Icc 0 1) 0 ∧ ∀ x ∈ Ioc (0 : ℝ) 1, F x = Real.sin (1 / x) := by
  rintro ⟨F, hF, hFx⟩
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hpos : 0 < Real.pi := Real.pi_pos
  -- two sequences tending to zero inside `(0, 1]`
  set u : ℕ → ℝ := fun n => 1 / (Real.pi * (n + 1)) with hu
  set v : ℕ → ℝ := fun n => 1 / ((n + 1) * (2 * Real.pi) + Real.pi / 2) with hv
  have hn : ∀ n : ℕ, (1 : ℝ) ≤ n + 1 := fun n => by have := n.cast_nonneg (α := ℝ); linarith
  have hu_mem : ∀ n, u n ∈ Ioc (0 : ℝ) 1 := fun n => by
    have h1 : 0 < Real.pi * (n + 1) := by have := hn n; positivity
    refine ⟨by simp only [hu]; positivity, ?_⟩
    simp only [hu]
    rw [div_le_one h1]
    nlinarith [hn n]
  have hv_mem : ∀ n, v n ∈ Ioc (0 : ℝ) 1 := fun n => by
    have h1 : 0 < (n + 1) * (2 * Real.pi) + Real.pi / 2 := by have := hn n; positivity
    refine ⟨by simp only [hv]; positivity, ?_⟩
    simp only [hv]
    rw [div_le_one h1]
    nlinarith [hn n]
  have hu_t : Tendsto u atTop (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => Real.pi * ((n : ℝ) + 1)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hpos
      exact tendsto_const_nhds.div_atTop this
    · exact Ioc_subset_Icc_self (hu_mem n) |> fun h => ⟨h.1, h.2⟩
  have hv_t : Tendsto v atTop (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (2 * Real.pi) + Real.pi / 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const (by positivity))
      exact tendsto_const_nhds.div_atTop this
    · exact Ioc_subset_Icc_self (hv_mem n) |> fun h => ⟨h.1, h.2⟩
  have h1 : Tendsto (F ∘ u) atTop (𝓝 (F 0)) := hF.tendsto.comp hu_t
  have h2 : Tendsto (F ∘ v) atTop (𝓝 (F 0)) := hF.tendsto.comp hv_t
  have hFu : ∀ n, F (u n) = 0 := fun n => by
    rw [hFx _ (hu_mem n)]
    have : 1 / u n = ((n + 1 : ℕ) : ℝ) * Real.pi := by
      simp only [hu, one_div_one_div]; push_cast; ring
    rw [this, Real.sin_nat_mul_pi]
  have hFv : ∀ n, F (v n) = 1 := fun n => by
    rw [hFx _ (hv_mem n)]
    have : 1 / v n = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) + Real.pi / 2 := by
      simp only [hv, one_div_one_div]; push_cast; ring
    rw [this, Real.sin_add_pi_div_two, Real.cos_nat_mul_two_pi]
  simp only [Function.comp_def, hFu] at h1
  simp only [Function.comp_def, hFv] at h2
  have e1 : F 0 = 0 := tendsto_nhds_unique h1 tendsto_const_nhds
  have e2 : F 0 = 1 := tendsto_nhds_unique h2 tendsto_const_nhds
  rw [e1] at e2
  exact zero_ne_one e2

/-- Morris, Topology Without Tears, Remark 12.1.12. The functions `pₙ(x) = n x / (1 + n² x²)` converge
pointwise to `0` on `(0, ∞)` but not uniformly: pointwise convergence does not imply uniform
convergence. -/
@[kb "morris2024" "Remark 12.1.12, p. 367"]
theorem morris_ex_12_1_12 :
    (∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n * x) / (1 + (n * x) ^ 2)) atTop (𝓝 0)) ∧
    ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => (n * x) / (1 + (n * x) ^ 2)) (fun _ => 0) atTop (Ioi 0) := by
  constructor
  · intro x hx
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hx)
    refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
    · positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnx : 0 < (n : ℝ) * x := by positivity
      rw [div_le_div_iff₀ (by positivity) hnx]
      nlinarith [sq_nonneg ((n : ℝ) * x)]
  · intro h
    rw [Metric.tendstoUniformlyOn_iff] at h
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1 / 4) (by norm_num))
    have hn : (0 : ℝ) < (max N 1 : ℕ) := by
      have : 1 ≤ max N 1 := le_max_right _ _
      exact_mod_cast this
    have := hN (max N 1) (le_max_left _ _) (1 / (max N 1 : ℕ)) (by simp)
    rw [Real.dist_eq] at this
    have e : ((max N 1 : ℕ) : ℝ) * (1 / ((max N 1 : ℕ) : ℝ)) = 1 := by field_simp
    rw [e] at this
    norm_num at this

/-- Morris, Topology Without Tears, Example 10.2.3. Divisibility is a partial order on the positive
integers: reflexive, transitive and antisymmetric. -/
@[kb "morris2024" "Example 10.2.3, p. 267"]
theorem morris_ex_10_2_3 :
    (∀ n : ℕ+, n ∣ n) ∧ (∀ m n k : ℕ+, m ∣ n → n ∣ k → m ∣ k) ∧
    (∀ m n : ℕ+, m ∣ n → n ∣ m → m = n) :=
  ⟨fun n => dvd_refl n, fun _ _ _ => dvd_trans, fun _ _ => PNat.dvd_antisymm⟩

/-- Morris, Topology Without Tears, Example 10.2.4. For a set `U`, inclusion is a partial order on the
subsets of `U`. -/
@[kb "morris2024" "Example 10.2.4, p. 267"]
theorem morris_ex_10_2_4 (U : Type*) :
    (∀ A : Set U, A ⊆ A) ∧ (∀ A B C : Set U, A ⊆ B → B ⊆ C → A ⊆ C) ∧
    (∀ A B : Set U, A ⊆ B → B ⊆ A → A = B) :=
  ⟨fun _ => Subset.rfl, fun _ _ _ => Subset.trans, fun _ _ => Subset.antisymm⟩

/-- Morris, Topology Without Tears, Example 10.2.5. The reversed relation `x ≤* y ↔ y ≤ x` of a
partial order is again a partial order. -/
@[kb "morris2024" "Example 10.2.5, p. 267"]
theorem morris_ex_10_2_5 (X : Type*) [PartialOrder X] :
    (∀ x : X, x ≤ x) ∧ (∀ x y z : X, (y ≤ x) → (z ≤ y) → (z ≤ x)) ∧
    (∀ x y : X, (y ≤ x) → (x ≤ y) → x = y) :=
  ⟨fun _ => le_rfl, fun _ _ _ h1 h2 => h2.trans h1, fun _ _ h1 h2 => le_antisymm h2 h1⟩

/-- Morris, Topology Without Tears, Examples 10.2.10. The usual orders on `ℝ`, `ℚ`, `ℕ` and `ℤ` are
linear orders (any two elements are comparable). -/
@[kb "morris2024" "Example 10.2.10, p. 269"]
theorem morris_ex_10_2_10_a :
    (∀ x y : ℝ, x ≤ y ∨ y ≤ x) ∧ (∀ x y : ℚ, x ≤ y ∨ y ≤ x) ∧
    (∀ x y : ℕ, x ≤ y ∨ y ≤ x) ∧ (∀ x y : ℤ, x ≤ y ∨ y ≤ x) :=
  ⟨fun x y => le_total x y, fun x y => le_total x y, fun x y => le_total x y, fun x y => le_total x y⟩

/-- Morris, Topology Without Tears, Examples 10.2.10. The inclusion order on the subsets of a set with
at least two points is not a linear order. -/
@[kb "morris2024" "Example 10.2.10, p. 269"]
theorem morris_ex_10_2_10_b (U : Type*) [Nontrivial U] :
    ∃ A B : Set U, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  refine ⟨{a}, {b}, ?_, ?_⟩
  · simpa using hab
  · simpa using hab.symm

/-- Morris, Topology Without Tears, Remark 11.1.8 (ii), (v). A constant map `ℝ → ℝ` is closed and
continuous but not open. -/
@[kb "morris2024" "Remark 11.1.8, p. 341"]
theorem morris_ex_11_1_8_a :
    IsClosedMap (fun _ : ℝ => (0 : ℝ)) ∧ Continuous (fun _ : ℝ => (0 : ℝ)) ∧
    ¬ IsOpenMap (fun _ : ℝ => (0 : ℝ)) := by
  refine ⟨?_, continuous_const, ?_⟩
  · intro s _
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [hne.image_const]; exact isClosed_singleton
  · intro h
    have := h _ isOpen_univ
    rw [univ_nonempty.image_const] at this
    exact not_isOpen_singleton (0 : ℝ) this

/-- Morris, Topology Without Tears, Remark 11.1.8 (vi). The exponential map `ℝ → ℝ` is continuous but
not closed (its image of the closed set `ℝ` is `(0, ∞)`). -/
@[kb "morris2024" "Remark 11.1.8, p. 341"]
theorem morris_ex_11_1_8_b : Continuous Real.exp ∧ ¬ IsClosedMap Real.exp := by
  refine ⟨Real.continuous_exp, fun h => ?_⟩
  have h1 := h _ isClosed_univ
  rw [image_univ, Real.range_exp] at h1
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact Set.mem_Ici.2 le_rfl
  rw [h1.closure_eq] at h0
  exact lt_irrefl (0 : ℝ) (show (0 : ℝ) < 0 from h0)

end Examples

end UndergradKB.Topology.Course
