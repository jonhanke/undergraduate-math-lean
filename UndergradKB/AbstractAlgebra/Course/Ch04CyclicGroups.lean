import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 4: cyclic groups (course layer)

Thin wrappers around Mathlib for cyclic subgroups, element orders, the circle group and roots of
unity. -/

open Complex

namespace UndergradKB.AbstractAlgebra.Course

section Cyclic

variable {G : Type*} [Group G]

/-- AA-048. For `a` in a group, `⟨a⟩ = {aᵏ | k ∈ ℤ}` is a subgroup and it is the smallest subgroup
containing `a`. -/
@[kb "judson2026" "Theorem 4.1.3, p. 59"]
theorem judson_4_1_3 (a : G) :
    (∀ g : G, g ∈ Subgroup.zpowers a ↔ ∃ k : ℤ, a ^ k = g) ∧
    ∀ H : Subgroup G, a ∈ H → Subgroup.zpowers a ≤ H :=
  ⟨fun _ => Subgroup.mem_zpowers_iff, fun _ ha => (Subgroup.zpowers_le).mpr ha⟩

/-- AA-051. Every cyclic group is abelian. -/
@[kb "judson2026" "Theorem 4.1.9, p. 60"]
theorem judson_4_1_9 [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

/-- AA-052. Every subgroup of a cyclic group is cyclic. -/
@[kb "judson2026" "Theorem 4.1.10, p. 61"]
theorem judson_4_1_10 [IsCyclic G] (H : Subgroup G) : IsCyclic H :=
  inferInstance

/-- AA-054. If `a` has order `n`, then `aᵏ = e` iff `n ∣ k`. -/
@[kb "judson2026" "Proposition 4.1.12, p. 61"]
theorem judson_4_1_12 (a : G) (n : ℕ) (hn : orderOf a = n) (k : ℤ) :
    a ^ k = 1 ↔ (n : ℤ) ∣ k := by
  rw [← hn]
  exact orderOf_dvd_iff_zpow_eq_one.symm

/-- AA-055. If `a` has finite order `n` then `aᵏ` has order `n / gcd(k, n)`. -/
@[kb "judson2026" "Theorem 4.1.13, p. 61"]
theorem judson_4_1_13 (a : G) (n : ℕ) (hn0 : n ≠ 0) (hn : orderOf a = n) (k : ℕ) :
    orderOf (a ^ k) = n / Nat.gcd k n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Nat.div_self (Nat.pos_of_ne_zero hn0)]
  · rw [orderOf_pow' a hk.ne', hn, Nat.gcd_comm]

end Cyclic

/-- AA-053. Every subgroup of `ℤ` is `nℤ` for some `n ≥ 0`. -/
@[kb "judson2026" "Corollary 4.1.11, p. 61"]
theorem judson_4_1_11 (H : AddSubgroup ℤ) : ∃ n : ℕ, H = AddSubgroup.zmultiples (n : ℤ) := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H)
  refine ⟨(g : ℤ).natAbs, ?_⟩
  have h1 : H = AddSubgroup.zmultiples (g : ℤ) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    · exact (AddSubgroup.zmultiples_le).mpr g.2
  exact h1.trans (Int.zmultiples_natAbs _).symm

/-- AA-056. The generators of `ℤ_n` are exactly the residues `r` with `gcd(r, n) = 1`. -/
@[kb "judson2026" "Corollary 4.1.14, p. 61"]
theorem judson_4_1_14 (n : ℕ) [NeZero n] (r : ℕ) :
    (∀ x : ZMod n, x ∈ AddSubgroup.zmultiples (r : ZMod n)) ↔ Nat.gcd r n = 1 := by
  have key : IsUnit (r : ZMod n) ↔ Nat.gcd r n = 1 := ZMod.isUnit_iff_coprime r n
  rw [← key]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (h 1)
    rw [zsmul_eq_mul] at hk
    exact IsUnit.of_mul_eq_one (k : ZMod n) (by rw [mul_comm]; exact hk)
  · intro h x
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp h
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((x * u).val : ℤ), ?_⟩
    rw [zsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm u, hu, mul_one]

/-- AA-057. Polar form: `(r cis θ)(s cis φ) = r s cis(θ + φ)`. -/
@[kb "judson2026" "Proposition 4.2.5, p. 64"]
theorem judson_4_2_5 (r s θ φ : ℝ) :
    ((r : ℂ) * (Real.cos θ + Real.sin θ * I)) * ((s : ℂ) * (Real.cos φ + Real.sin φ * I)) =
      ((r * s : ℝ) : ℂ) * (Real.cos (θ + φ) + Real.sin (θ + φ) * I) := by
  rw [Real.cos_add, Real.sin_add]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- AA-058. De Moivre: `(r cis θ)ⁿ = rⁿ cis(nθ)`. -/
@[kb "judson2026" "Theorem 4.2.7, p. 64"]
theorem judson_4_2_7 (r : ℝ) (θ : ℂ) (n : ℕ) :
    ((r : ℂ) * (Complex.cos θ + Complex.sin θ * I)) ^ n =
      (r : ℂ) ^ n * (Complex.cos (n * θ) + Complex.sin (n * θ) * I) := by
  rw [mul_pow, Complex.cos_add_sin_mul_I_pow]

/-- AA-059. The circle group `T = {z ∈ ℂ* | |z| = 1}` is a subgroup of `ℂ*`. -/
@[kb "judson2026" "Proposition 4.2.9, p. 65"]
theorem judson_4_2_9 :
    ∃ T : Subgroup ℂˣ, ∀ z : ℂˣ, z ∈ T ↔ ‖(z : ℂ)‖ = 1 := by
  refine ⟨{ carrier := {z | ‖(z : ℂ)‖ = 1}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ },
    fun z => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    simp [ha, hb]
  · simp
  · intro a ha
    simp only [Set.mem_ofPred_eq] at *
    simp [ha]

/-- AA-061. For `n > 0`, the complex `n`th roots of unity are the numbers `exp(2πi k / n)` with
`0 ≤ k < n`; they form a cyclic group of order `n`. -/
@[kb "judson2026" "Theorem 4.2.10, p. 65"]
theorem judson_4_2_10 (n : ℕ) [NeZero n] :
    (∀ x : ℂˣ, x ∈ rootsOfUnity n ℂ ↔ ∃ k < n, Complex.exp (2 * Real.pi * I * (k / n)) = x) ∧
    IsCyclic (rootsOfUnity n ℂ) ∧ Nat.card (rootsOfUnity n ℂ) = n :=
  ⟨Complex.mem_rootsOfUnity n, inferInstance, Complex.card_rootsOfUnity n⟩

end UndergradKB.AbstractAlgebra.Course
