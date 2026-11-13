import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Equiv.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Morris: further examples and remarks (wave 3, part 3)

Thin theorems for examples and remarks of Morris, *Topology Without Tears*, from the appendices and
Chapter 12: counting examples, topological groups, filters and nets, iteration of `x ↦ x³`,
separating families and matrix algebras.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace Metric

section Examples

/-- Morris, Topology Without Tears, Example A1.1.7. The set of even positive integers is countably
infinite (in one-to-one correspondence with `ℕ`). -/
@[kb "morris2024" "Example A1.1.7, p. 396"]
theorem morris_ex_A1_1_7 : Nonempty (ℕ ≃ {n : ℕ | Even n ∧ 0 < n}) := by
  have hinf : ({n : ℕ | Even n ∧ 0 < n}).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * (n + 1))
      (fun a b h => by simpa using h)
      (fun n => ⟨even_two_mul _, by omega⟩)
  have := hinf.to_subtype
  exact nonempty_equiv_of_countable

/-- Morris, Topology Without Tears, Example A1.1.8. The set `ℤ` of all integers is countably
infinite. -/
@[kb "morris2024" "Example A1.1.8, p. 396"]
theorem morris_ex_A1_1_8 : Nonempty (ℕ ≃ ℤ) := nonempty_equiv_of_countable

/-- Morris, Topology Without Tears, Example A1.1.9. The set of positive perfect squares is countably
infinite. -/
@[kb "morris2024" "Example A1.1.9, p. 396"]
theorem morris_ex_A1_1_9 : Nonempty (ℕ ≃ {n : ℕ | ∃ m : ℕ, 0 < m ∧ n = m ^ 2}) := by
  have hinf : ({n : ℕ | ∃ m : ℕ, 0 < m ∧ n = m ^ 2}).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n + 1) ^ 2)
      (fun a b h => by simpa using h)
      (fun n => ⟨n + 1, by omega, rfl⟩)
  have := hinf.to_subtype
  exact nonempty_equiv_of_countable

/-- Morris, Topology Without Tears, Example A1.1.22. Every rational number is an algebraic number
(a root of a nonzero integer polynomial). -/
@[kb "morris2024" "Example A1.1.22, p. 399"]
theorem morris_ex_A1_1_22 (q : ℚ) : IsAlgebraic ℤ (q : ℝ) := by
  refine ⟨Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num, ?_, ?_⟩
  · intro h
    have := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      Polynomial.coeff_C, Polynomial.coeff_zero] at this
    simp at this
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    have h1 : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    linarith [mul_comm (q : ℝ) q.den]

/-- Morris, Topology Without Tears, Example A1.1.23. The number `√2` is algebraic but not rational. -/
@[kb "morris2024" "Example A1.1.23, p. 399"]
theorem morris_ex_A1_1_23 : IsAlgebraic ℤ (Real.sqrt 2) ∧ Irrational (Real.sqrt 2) := by
  refine ⟨⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩, irrational_sqrt_two⟩
  · intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp at this
  · simp
    exact sub_eq_zero.2 (map_ofNat (Polynomial.aeval (Real.sqrt 2)) 2).symm

/-- Morris, Topology Without Tears, Remark A1.2.8. There are infinitely many infinite cardinals:
`ℵ₀ < card 𝒫(ℕ) < card 𝒫(𝒫(ℕ))`. -/
@[kb "morris2024" "Remark A1.2.8, p. 408"]
theorem morris_ex_A1_2_8 :
    Cardinal.mk ℕ < Cardinal.mk (Set ℕ) ∧ Cardinal.mk (Set ℕ) < Cardinal.mk (Set (Set ℕ)) := by
  rw [Cardinal.mk_set, Cardinal.mk_set, Cardinal.mk_set]
  exact ⟨Cardinal.cantor _, Cardinal.cantor _⟩

/-- Morris, Topology Without Tears, Example A5.1.2 (5). Any group carrying the discrete topology is a
topological group. -/
@[kb "morris2024" "Example A5.1.2, p. 514"]
theorem morris_ex_A5_1_2_a (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    IsTopologicalGroup G :=
  { continuous_mul := continuous_of_discreteTopology
    continuous_inv := continuous_of_discreteTopology }

/-- Morris, Topology Without Tears, Example A5.1.2 (6). Any group carrying the indiscrete topology is
a topological group. -/
@[kb "morris2024" "Example A5.1.2, p. 514"]
theorem morris_ex_A5_1_2_b (G : Type*) [Group G] : @IsTopologicalGroup G ⊤ _ :=
  @IsTopologicalGroup.mk G ⊤ _ (@ContinuousMul.mk G ⊤ _ continuous_top)
    (@ContinuousInv.mk G ⊤ _ continuous_top)

/-- Morris, Topology Without Tears, Example A5.1.4. Declare a subset `U` of `ℤ` open when `0 ∉ U` or
`ℤ \ U` is finite. -/
@[instance_reducible] def zeroOrCofiniteTopology : TopologicalSpace ℤ where
  IsOpen U := 0 ∉ U ∨ Uᶜ.Finite
  isOpen_univ := Or.inr (by simp)
  isOpen_inter U V hU hV := by
    rcases hU with hU | hU
    · exact Or.inl (fun h => hU h.1)
    rcases hV with hV | hV
    · exact Or.inl (fun h => hV h.2)
    · exact Or.inr (by rw [compl_inter]; exact hU.union hV)
  isOpen_sUnion S hS := by
    by_cases h : 0 ∈ ⋃₀ S
    · obtain ⟨U, hUS, h0⟩ := h
      refine Or.inr ?_
      rcases hS U hUS with h1 | h1
      · exact absurd h0 h1
      · exact h1.subset (compl_subset_compl.2 (subset_sUnion_of_mem hUS))
    · exact Or.inl h

/-- Morris, Topology Without Tears, Example A5.1.4. The topology on `ℤ` in which `U` is open iff
`0 ∉ U` or `ℤ \ U` is finite is not a group topology: addition is not continuous (translation by `1`
fails to be continuous). -/
@[kb "morris2024" "Example A5.1.4, p. 515"]
theorem morris_ex_A5_1_4 : ¬ @ContinuousAdd ℤ zeroOrCofiniteTopology _ := by
  intro h
  have hc : @Continuous ℤ ℤ zeroOrCofiniteTopology zeroOrCofiniteTopology (fun x => x + 1) := by
    let _ := zeroOrCofiniteTopology
    exact continuous_id.add continuous_const
  have h1 : IsOpen[zeroOrCofiniteTopology] ({1} : Set ℤ) := Or.inl (by simp)
  have h2 := @Continuous.isOpen_preimage ℤ ℤ zeroOrCofiniteTopology zeroOrCofiniteTopology _ hc _ h1
  have e : (fun x : ℤ => x + 1) ⁻¹' {1} = {0} := by ext x; simp
  rw [e] at h2
  rcases h2 with h2 | h2
  · exact h2 rfl
  · exact (Set.Finite.infinite_compl (Set.finite_singleton (0 : ℤ))) h2

/-- Morris, Topology Without Tears, Example A5.2.2. The additive group `ℝ` and the multiplicative group of
positive reals are topologically isomorphic via the exponential map. -/
@[kb "morris2024" "Example A5.2.2, p. 520"]
theorem morris_ex_A5_2_2 :
    ∃ e : ℝ ≃ₜ Ioi (0 : ℝ), ∀ x y, (e (x + y) : ℝ) = e x * e y :=
  ⟨Real.expOrderIso.toHomeomorph, fun x y => Real.exp_add x y⟩

/-- Morris, Topology Without Tears, Examples A5.5.4. The subgroups of `ℝ` generated by `{1, √2}` and
by `{√2, √3}` are dense. -/
@[kb "morris2024" "Example A5.5.4, p. 539"]
theorem morris_ex_A5_5_4 :
    Dense (AddSubgroup.closure {1, Real.sqrt 2} : Set ℝ) ∧
    Dense (AddSubgroup.closure {Real.sqrt 2, Real.sqrt 3} : Set ℝ) := by
  refine ⟨dense_addSubgroupClosure_pair_iff.2 ?_, dense_addSubgroupClosure_pair_iff.2 ?_⟩
  · rw [one_div]; exact irrational_sqrt_two.inv
  · have h6 : Irrational (Real.sqrt 6) := by
      have := (irrational_sqrt_natCast_iff (n := 6)).2 (by
        rintro ⟨r, hr⟩
        have : r ≤ 3 := by nlinarith
        interval_cases r <;> omega)
      simpa using this
    have e : Real.sqrt 2 / Real.sqrt 3 = Real.sqrt 6 / 3 := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      have h3 : (0 : ℝ) < 3 := by norm_num
      have : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        rw [← Real.sqrt_mul h2]; norm_num
      rw [this]
      have : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt h3.le
      have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 h3).ne'
      field_simp
      linarith
    rw [e]
    exact h6.div_natCast (by norm_num)

/-- Morris, Topology Without Tears, Example A5.12.2 (for `ℤ`). The group `ℤ` is monothetic: it has an
element generating a dense subgroup. -/
@[kb "morris2024" "Example A5.12.2, p. 581"]
theorem morris_ex_A5_12_2 : ∃ g : ℤ, Dense (AddSubgroup.zmultiples g : Set ℤ) := by
  refine ⟨1, ?_⟩
  have : (AddSubgroup.zmultiples (1 : ℤ) : Set ℤ) = univ := by
    ext x; simp only [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff, mem_univ, iff_true]
    exact ⟨x, by simp⟩
  rw [this]; exact dense_univ

/-- Morris, Topology Without Tears, Example A6.2.8. The sequence `1, 1/2, 1/3, ...` converges to `0`. -/
@[kb "morris2024" "Example A6.2.8, p. 643"]
theorem morris_ex_A6_2_8 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Morris, Topology Without Tears, Example A6.2.9. In any topological space the neighbourhood filter
(base) of a point `x` converges to `x`. -/
@[kb "morris2024" "Example A6.2.9, p. 643"]
theorem morris_ex_A6_2_9 {X : Type*} [TopologicalSpace X] (x : X) : Tendsto id (𝓝 x) (𝓝 x) :=
  tendsto_id

/-- Morris, Topology Without Tears, Example A6.3.22. The map `n ↦ 3 n` on `ℕ` is non-decreasing and
cofinal, so `x₃, x₆, x₉, ...` is a subnet of any sequence. -/
@[kb "morris2024" "Example A6.3.22, p. 655"]
theorem morris_ex_A6_3_22 : Monotone (fun n : ℕ => 3 * n) ∧ Tendsto (fun n : ℕ => 3 * n) atTop atTop :=
  ⟨fun _ _ h => by dsimp only; omega, tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩⟩

/-- Morris, Topology Without Tears, Example A6.3.23. The map `θ n = 1 + ⌊n / 2⌋` on `ℕ` is non-decreasing
and cofinal but not injective, so the associated subnet `x₁, x₂, x₂, x₃, x₃, ...` of a sequence is not a
subsequence. -/
@[kb "morris2024" "Example A6.3.23, p. 655"]
theorem morris_ex_A6_3_23 :
    Monotone (fun n : ℕ => 1 + n / 2) ∧ Tendsto (fun n : ℕ => 1 + n / 2) atTop atTop ∧
    ¬ StrictMono (fun n : ℕ => 1 + n / 2) := by
  refine ⟨fun _ _ h => by dsimp only; omega, ?_, fun h => ?_⟩
  · exact tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  · have := h (show 2 < 3 by norm_num)
    dsimp only at this
    omega

/-- Morris, Topology Without Tears, Examples 12.2.2 (a). The polynomial functions on `[0, 1]` separate
the points of `[0, 1]` (the function `x ↦ x` already does). -/
@[kb "morris2024" "Example 12.2.2, p. 375"]
theorem morris_ex_12_2_2_a : (polynomialFunctions (Icc (0 : ℝ) 1)).SeparatesPoints :=
  polynomialFunctions_separatesPoints _

/-- Morris, Topology Without Tears, Examples 12.2.2 (c). The functions `sin (2 π n x)`, `n ∈ ℕ`, take
the same value at `0` and at `1`, so this family does not separate the points `0` and `1`. -/
@[kb "morris2024" "Example 12.2.2, p. 375"]
theorem morris_ex_12_2_2_c :
    ∀ f ∈ {f : ℝ → ℝ | ∃ n : ℕ, f = fun x => Real.sin (2 * Real.pi * n * x)}, f 0 = f 1 := by
  rintro f ⟨n, rfl⟩
  simp only [mul_zero, mul_one, Real.sin_zero]
  have : 2 * Real.pi * n = ((2 * n : ℕ) : ℝ) * Real.pi := by push_cast; ring
  rw [this, Real.sin_nat_mul_pi]

/-- Morris, Topology Without Tears, Example 12.2.5. For `n ≥ 2` the algebra of `n × n` real matrices is
not commutative. -/
@[kb "morris2024" "Example 12.2.5, p. 377"]
theorem morris_ex_12_2_5 (n : ℕ) :
    ∃ A B : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 1 1, fun h => ?_⟩
  have := congrFun (congrFun h 0) 1
  simp at this

/-- Morris, Topology Without Tears, Example A3.3.1 (fixed points). The fixed points of `f x = x³`
are `0`, `1` and `-1`. -/
@[kb "morris2024" "Example A3.3.1, p. 443"]
theorem morris_ex_A3_3_1_a : {x : ℝ | x ^ 3 = x} = {0, 1, -1} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    have : x * (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem tendsto_three_pow_nat : Tendsto (fun n : ℕ => 3 ^ n) atTop atTop :=
  tendsto_atTop_mono (fun n : ℕ => (Nat.lt_pow_self (by norm_num : 1 < 3)).le) tendsto_id

/-- Closed form for the iterates of `x ↦ x³`. -/
theorem iterate_cube (x : ℝ) (n : ℕ) : (fun y : ℝ => y ^ 3)^[n] x = x ^ (3 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- Morris, Topology Without Tears, Example A3.3.1 (orbits inside the unit interval). If `|x₀| < 1`, the
orbit of `x₀` under `x ↦ x³` tends to `0`. -/
@[kb "morris2024" "Example A3.3.1, p. 443"]
theorem morris_ex_A3_3_1_b {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun n : ℕ => (fun y : ℝ => y ^ 3)^[n] x) atTop (𝓝 0) := by
  simp only [iterate_cube]
  exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx).comp
    tendsto_three_pow_nat

/-- Morris, Topology Without Tears, Example A3.3.1 (orbits outside the unit interval). If `|x₀| > 1`, the
orbit of `x₀` under `x ↦ x³` diverges to infinity in absolute value. -/
@[kb "morris2024" "Example A3.3.1, p. 443"]
theorem morris_ex_A3_3_1_c {x : ℝ} (hx : 1 < |x|) :
    Tendsto (fun n : ℕ => |(fun y : ℝ => y ^ 3)^[n] x|) atTop atTop := by
  simp only [iterate_cube, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hx).comp
    tendsto_three_pow_nat

end Examples

end UndergradKB.Topology.Course
