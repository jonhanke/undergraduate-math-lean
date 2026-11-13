import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylAlgebra

/-! # Problem 1.26(a): the Weyl algebra is simple in characteristic zero

Commutators with `x` and `y` act on the monomial basis `xⁱ yʲ` like the partial derivatives
`∂/∂y` and `∂/∂x`; iterating them on a nonzero element of an ideal reaches a nonzero scalar.
-/

namespace UndergradKB.RepresentationTheory

open Module

section

variable {k : Type*} [Field k] [CharZero k]

/-- `z ↦ z x - x z`. -/
noncomputable def weylAdX : WeylAlgebra k →ₗ[k] WeylAlgebra k :=
  LinearMap.mulRight k (weylX k) - LinearMap.mulLeft k (weylX k)

/-- `z ↦ y z - z y`. -/
noncomputable def weylAdY : WeylAlgebra k →ₗ[k] WeylAlgebra k :=
  LinearMap.mulLeft k (weylY k) - LinearMap.mulRight k (weylY k)

theorem weylAdX_apply (z : WeylAlgebra k) : weylAdX z = z * weylX k - weylX k * z := rfl
theorem weylAdY_apply (z : WeylAlgebra k) : weylAdY z = weylY k * z - z * weylY k := rfl

/-- `yʲ x = x yʲ + j yʲ⁻¹`. -/
theorem weylY_pow_mul_X (j : ℕ) :
    weylY k ^ j * weylX k = weylX k * weylY k ^ j + j • weylY k ^ (j - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases j with _ | j
    · simp [weylY_mul_weylX]
    · rw [pow_succ, mul_assoc, weylY_mul_weylX, mul_add, ← mul_assoc, ih]
      simp only [Nat.add_sub_cancel, add_mul, smul_mul_assoc, mul_one, mul_assoc,
        ← pow_succ, add_smul, one_smul]
      abel

theorem weylAdX_basis (a c : ℕ) :
    weylAdX (weylBasis (k := k) (a, c)) = (c : k) • weylBasis (k := k) (a, c - 1) := by
  rw [weylAdX_apply, weylBasis_apply, weylBasis_apply]
  simp only
  rw [mul_assoc, weylY_pow_mul_X, mul_add, ← mul_assoc, ← (Commute.self_pow (weylX k) a).eq,
    mul_assoc, add_sub_cancel_left, mul_smul_comm, ← Nat.cast_smul_eq_nsmul k]

theorem weylAdY_basis (a c : ℕ) :
    weylAdY (weylBasis (k := k) (a, c)) = (a : k) • weylBasis (k := k) (a - 1, c) := by
  rw [weylAdY_apply, weylBasis_apply, weylBasis_apply]
  simp only
  rw [← mul_assoc, y_mul_x_pow _ _ weylY_mul_weylX, add_mul, mul_assoc (weylX k ^ a) (weylY k) (weylY k ^ c),
    ← pow_succ', mul_assoc (weylX k ^ a) (weylY k ^ c) (weylY k), ← pow_succ,
    add_sub_cancel_left, smul_mul_assoc, ← Nat.cast_smul_eq_nsmul k]

theorem repr_adX (z : WeylAlgebra k) (i j : ℕ) :
    weylBasis.repr (weylAdX z) (i, j) = ((j : k) + 1) * weylBasis.repr z (i, j + 1) := by
  have : (Finsupp.lapply (i, j) ∘ₗ (weylBasis (k := k)).repr.toLinearMap ∘ₗ weylAdX) =
      ((j : k) + 1) • (Finsupp.lapply (i, j + 1) ∘ₗ (weylBasis (k := k)).repr.toLinearMap) := by
    refine weylBasis.ext fun ⟨a, c⟩ => ?_
    simp only [LinearMap.comp_apply, weylAdX_basis, LinearEquiv.coe_coe, map_smul,
      Basis.repr_self, Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases h : a = i ∧ c = j + 1
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, mul_zero]
      split_ifs with h2
      · obtain ⟨h2a, h2b⟩ := h2
        rcases Nat.eq_zero_or_pos c with hc | hc
        · simp [hc]
        · exact absurd ⟨by omega, by omega⟩ h
      · simp
  exact congrArg (fun f => f z) this

theorem repr_adY (z : WeylAlgebra k) (i j : ℕ) :
    weylBasis.repr (weylAdY z) (i, j) = ((i : k) + 1) * weylBasis.repr z (i + 1, j) := by
  have : (Finsupp.lapply (i, j) ∘ₗ (weylBasis (k := k)).repr.toLinearMap ∘ₗ weylAdY) =
      ((i : k) + 1) • (Finsupp.lapply (i + 1, j) ∘ₗ (weylBasis (k := k)).repr.toLinearMap) := by
    refine weylBasis.ext fun ⟨a, c⟩ => ?_
    simp only [LinearMap.comp_apply, weylAdY_basis, LinearEquiv.coe_coe, map_smul,
      Basis.repr_self, Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases h : a = i + 1 ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, mul_zero]
      split_ifs with h2
      · obtain ⟨h2a, h2b⟩ := h2
        rcases Nat.eq_zero_or_pos a with hc | hc
        · simp [hc]
        · exact absurd ⟨by omega, by omega⟩ h
      · simp
  exact congrArg (fun f => f z) this

theorem repr_adX_pow (m : ℕ) (z : WeylAlgebra k) (i j : ℕ) :
    weylBasis.repr ((weylAdX ^ m) z) (i, j) =
      (Nat.descFactorial (j + m) m : k) * weylBasis.repr z (i, j + m) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, repr_adX]
    have : Nat.descFactorial (j + (m + 1)) (m + 1) = (j + m + 1) * Nat.descFactorial (j + m) m := by
      rw [← add_assoc]; exact Nat.succ_descFactorial_succ _ _
    rw [this, add_assoc]
    push_cast
    ring

theorem repr_adY_pow (m : ℕ) (z : WeylAlgebra k) (i j : ℕ) :
    weylBasis.repr ((weylAdY ^ m) z) (i, j) =
      (Nat.descFactorial (i + m) m : k) * weylBasis.repr z (i + m, j) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, repr_adY]
    have : Nat.descFactorial (i + (m + 1)) (m + 1) = (i + m + 1) * Nat.descFactorial (i + m) m := by
      rw [← add_assoc]; exact Nat.succ_descFactorial_succ _ _
    rw [this, add_assoc]
    push_cast
    ring

theorem weylAdX_mem (I : TwoSidedIdeal (WeylAlgebra k)) {z : WeylAlgebra k} (hz : z ∈ I) :
    weylAdX z ∈ I :=
  I.sub_mem (I.mul_mem_right _ _ hz) (I.mul_mem_left _ _ hz)

theorem weylAdY_mem (I : TwoSidedIdeal (WeylAlgebra k)) {z : WeylAlgebra k} (hz : z ∈ I) :
    weylAdY z ∈ I :=
  I.sub_mem (I.mul_mem_left _ _ hz) (I.mul_mem_right _ _ hz)

theorem weylAdX_pow_mem (I : TwoSidedIdeal (WeylAlgebra k)) (m : ℕ) {z : WeylAlgebra k}
    (hz : z ∈ I) : (weylAdX ^ m) z ∈ I := by
  induction m with
  | zero => simpa using hz
  | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact weylAdX_mem I ih

theorem weylAdY_pow_mem (I : TwoSidedIdeal (WeylAlgebra k)) (m : ℕ) {z : WeylAlgebra k}
    (hz : z ∈ I) : (weylAdY ^ m) z ∈ I := by
  induction m with
  | zero => simpa using hz
  | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact weylAdY_mem I ih

theorem weylBasis_repr_one : weylBasis.repr (1 : WeylAlgebra k) = Finsupp.single (0, 0) 1 := by
  have : (1 : WeylAlgebra k) = weylBasis (k := k) (0, 0) := by simp [weylBasis_apply]
  rw [this, Basis.repr_self]

/-- Problem 1.26(a): in characteristic zero every nonzero two-sided ideal of the Weyl algebra is
the whole algebra. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weyl_ideal_eq_top (I : TwoSidedIdeal (WeylAlgebra k)) (h : I ≠ ⊥) : I = ⊤ := by
  classical
  obtain ⟨z, hzI, hz0⟩ : ∃ z ∈ I, z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h (le_bot_iff.1 fun z hz => (TwoSidedIdeal.mem_bot _).2 (hcon z hz))
  set m := (weylBasis.repr z).support.sup Prod.snd with hm
  have hz' : weylBasis.repr z ≠ 0 := by simpa using hz0
  obtain ⟨p, hp⟩ : (weylBasis.repr z).support.Nonempty :=
    Finsupp.support_nonempty_iff.2 hz'
  have hmax : ∃ i0, weylBasis.repr z (i0, m) ≠ 0 := by
    have : ∃ q ∈ (weylBasis.repr z).support, q.2 = m := by
      obtain ⟨q, hq, hq2⟩ := Finset.exists_mem_eq_sup _ ⟨p, hp⟩ Prod.snd
      exact ⟨q, hq, hq2.symm⟩
    obtain ⟨q, hq, hq2⟩ := this
    exact ⟨q.1, by rw [← hq2]; exact Finsupp.mem_support_iff.1 hq⟩
  obtain ⟨i0, hi0⟩ := hmax
  have hbig : ∀ i j, m < j → weylBasis.repr z (i, j) = 0 := by
    intro i j hj
    by_contra hne
    have := Finset.le_sup (f := Prod.snd) (Finsupp.mem_support_iff.2 hne)
    simp only at this
    omega
  set w := (weylAdX ^ m) z with hw
  have hwI : w ∈ I := weylAdX_pow_mem I m hzI
  have hw0 : weylBasis.repr w (i0, 0) ≠ 0 := by
    rw [hw, repr_adX_pow]
    simp only [zero_add]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_self m ▸ (Nat.factorial_pos m).ne')) hi0
  have hwj : ∀ i j, 0 < j → weylBasis.repr w (i, j) = 0 := by
    intro i j hj
    rw [hw, repr_adX_pow, hbig i (j + m) (by omega), mul_zero]
  have hwne : weylBasis.repr w ≠ 0 := fun h0 => hw0 (by simp [h0])
  set n := (weylBasis.repr w).support.sup Prod.fst with hn
  obtain ⟨p', hp'⟩ : (weylBasis.repr w).support.Nonempty := Finsupp.support_nonempty_iff.2 hwne
  have hmax' : weylBasis.repr w (n, 0) ≠ 0 := by
    obtain ⟨q, hq, hq2⟩ := Finset.exists_mem_eq_sup _ ⟨p', hp'⟩ Prod.fst
    have hq0 : q.2 = 0 := by
      by_contra hne
      exact Finsupp.mem_support_iff.1 hq (hwj q.1 q.2 (Nat.pos_of_ne_zero hne))
    have : q = (n, 0) := Prod.ext hq2.symm hq0
    rw [← this]; exact Finsupp.mem_support_iff.1 hq
  have hbig' : ∀ i j, n < i → weylBasis.repr w (i, j) = 0 := by
    intro i j hi
    by_contra hne
    have := Finset.le_sup (f := Prod.fst) (Finsupp.mem_support_iff.2 hne)
    simp only at this
    omega
  set u := (weylAdY ^ n) w with hu
  have huI : u ∈ I := weylAdY_pow_mem I n hwI
  have hu00 : weylBasis.repr u (0, 0) ≠ 0 := by
    rw [hu, repr_adY_pow]
    simp only [zero_add]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_self n ▸ (Nat.factorial_pos n).ne')) hmax'
  have hu_eq : u = weylBasis.repr u (0, 0) • (1 : WeylAlgebra k) := by
    apply weylBasis.repr.injective
    ext ⟨i, j⟩
    rw [map_smul, weylBasis_repr_one]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij; simp
    · rw [if_neg (by tauto : ¬ (0 = i ∧ 0 = j)), mul_zero]
      rw [hu, repr_adY_pow]
      by_cases hi : i = 0
      · have hj : 0 < j := by omega
        rw [hwj _ _ hj, mul_zero]
      · rw [hbig' _ _ (by omega), mul_zero]
  rw [eq_top_iff]
  intro a _
  have e : ∀ r : k, r ≠ 0 → u = r • (1 : WeylAlgebra k) → (1 : WeylAlgebra k) ∈ I := by
    intro r hr0 hur
    have := I.mul_mem_left (algebraMap k (WeylAlgebra k) r⁻¹) _ huI
    rw [hur, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hr0, one_smul] at this
    exact this
  have h1 : (1 : WeylAlgebra k) ∈ I := e _ hu00 hu_eq
  simpa using I.mul_mem_left a _ h1

/-- Problem 1.26(a): the Weyl algebra over a field of characteristic zero is a simple ring. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weyl_isSimpleRing : IsSimpleRing (WeylAlgebra k) := by
  haveI : Nontrivial (WeylAlgebra k) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg (fun a => weylBasis.repr a (0, 0)) h
    simp [weylBasis_repr_one] at h2
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · exact Or.inr (weyl_ideal_eq_top I hI)

end

end UndergradKB.RepresentationTheory
