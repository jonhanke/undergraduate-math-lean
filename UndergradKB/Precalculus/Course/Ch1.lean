import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Real.Lemmas
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): sets, intervals, floor, graphs, symmetry, extrema -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Interval notation: `[a,b]` and `(a,b)` of reals are described by non-strict and strict inequalities (PC-002). -/
@[kb "stitzzeager2013" "§1.1, p. 15"]
theorem box_1_1_interval_notation (a b x : ℝ) :
    (x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b) ∧ (x ∈ Ioo a b ↔ a < x ∧ x < b) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Half-open and unbounded intervals are described by the corresponding inequalities (PC-002). -/
@[kb "stitzzeager2013" "§1.1, p. 15"]
theorem box_1_1_interval_notation_half_open (a b x : ℝ) :
    (x ∈ Ico a b ↔ a ≤ x ∧ x < b) ∧ (x ∈ Iic b ↔ x ≤ b) ∧ (x ∈ Ioi a ↔ a < x) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Definition 1.2: membership in an intersection and in a union of sets of reals (PC-003). -/
@[kb "stitzzeager2013" "Definition 1.2, p. 16"]
theorem def_1_2_mem_inter_union (A B : Set ℝ) (x : ℝ) :
    (x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) ∧ (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- The greatest integer function: `⌊x⌋` is an integer at most `x`, and every integer at most `x` is at most `⌊x⌋`
(PC-017). -/
@[kb "stitzzeager2013" "§1.4, p. 79"]
theorem box_1_4_greatest_integer (x : ℝ) :
    (⌊x⌋ : ℝ) ≤ x ∧ x < ⌊x⌋ + 1 ∧ ∀ k : ℤ, (k : ℝ) ≤ x → k ≤ ⌊x⌋ :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x, fun _ hk => Int.le_floor.mpr hk⟩

/-- The graph of `y = f x` is the set of points `(x, f x)` in the plane (PC-021). -/
@[kb "stitzzeager2013" "§1.6, p. 105"]
theorem box_1_6_graph_of_function (f : ℝ → ℝ) (p : ℝ × ℝ) :
    p ∈ univ.graphOn f ↔ p.2 = f p.1 := by
  obtain ⟨x, y⟩ := p
  simp [Set.graphOn, eq_comm]

/-- A function is even when `f (-x) = f x`, and odd when `f (-x) = -f x` (PC-023). -/
@[kb "stitzzeager2013" "§1.6, p. 107"]
theorem box_1_6_even_odd (f : ℝ → ℝ) :
    (Function.Even f ↔ ∀ x, f (-x) = f x) ∧ (Function.Odd f ↔ ∀ x, f (-x) = -f x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- The only function that is both even and odd is the zero function (PC-024). -/
@[kb "stitzzeager2013" "§1.6, p. 107"]
theorem box_1_6_even_and_odd_zero (f : ℝ → ℝ) (he : Function.Even f) (ho : Function.Odd f) :
    ∀ x, f x = 0 :=
  fun x => congrFun (Function.zero_of_even_and_odd he ho) x

/-- Definition 1.11: local maxima and minima are the extreme values on a neighbourhood of `a`, absolute ones on all
of the domain; the neighbourhood is any open interval around `a` (PC-026). -/
@[kb "stitzzeager2013" "Definition 1.11, p. 114"]
theorem def_1_11_local_extrema (f : ℝ → ℝ) (a : ℝ) :
    (IsLocalMax f a ↔ ∃ ε > 0, ∀ x ∈ Ioo (a - ε) (a + ε), f x ≤ f a) ∧
    (IsLocalMin f a ↔ ∃ ε > 0, ∀ x ∈ Ioo (a - ε) (a + ε), f a ≤ f x) := by
  constructor
  · rw [IsLocalMax, IsMaxFilter, Metric.eventually_nhds_iff]
    constructor
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hx => h (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])⟩
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun {x} hx => h x (by rw [Real.dist_eq, abs_lt] at hx; constructor <;> linarith [hx.1, hx.2])⟩
  · rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff]
    constructor
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hx => h (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])⟩
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun {x} hx => h x (by rw [Real.dist_eq, abs_lt] at hx; constructor <;> linarith [hx.1, hx.2])⟩

/-- Definition 1.11: absolute maximum and minimum of `f` at `a` over all of the domain (PC-026). -/
@[kb "stitzzeager2013" "Definition 1.11, p. 114"]
theorem def_1_11_absolute_extrema (f : ℝ → ℝ) (a : ℝ) :
    (IsMaxOn f univ a ↔ ∀ x, f x ≤ f a) ∧ (IsMinOn f univ a ↔ ∀ x, f a ≤ f x) := by
  simp [isMaxOn_univ_iff, isMinOn_univ_iff]

end UndergradKB.Precalculus.Course
