import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 4 (Polynomials): course layer

Thin theorems stated in the book's terms, proved by Mathlib.
-/

namespace UndergradKB.LinearAlgebra.Course

open Polynomial Complex

/-! ## 4A Zeros of polynomials -/

/-- Axler 4.4: basic facts about conjugation and absolute value on the complex numbers. -/
@[kb "axler2024" "4.4, p. 139"]
theorem axler_4_4 (z w : ℂ) :
    z + starRingEnd ℂ z = ((2 * z.re : ℝ) : ℂ) ∧
    z - starRingEnd ℂ z = ((2 * z.im : ℝ) : ℂ) * I ∧
    z * starRingEnd ℂ z = (‖z‖ ^ 2 : ℝ) ∧
    starRingEnd ℂ (z + w) = starRingEnd ℂ z + starRingEnd ℂ w ∧
    starRingEnd ℂ (z * w) = starRingEnd ℂ z * starRingEnd ℂ w ∧
    starRingEnd ℂ (starRingEnd ℂ z) = z ∧
    |z.re| ≤ ‖z‖ ∧ |z.im| ≤ ‖z‖ ∧
    ‖starRingEnd ℂ z‖ = ‖z‖ ∧ ‖z * w‖ = ‖z‖ * ‖w‖ ∧ ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by
  refine ⟨Complex.add_conj z, Complex.sub_conj z, ?_, map_add _ _ _, map_mul _ _ _,
    starRingEnd_self_apply z, Complex.abs_re_le_norm z, Complex.abs_im_le_norm z,
    Complex.norm_conj z, norm_mul z w, norm_add_le z w⟩
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Axler 4.5: `λ` is a zero of `p` exactly when `p(λ) = 0`. -/
@[kb "axler2024" "4.5, p. 140"]
theorem axler_4_5 (p : ℂ[X]) (l : ℂ) : p.IsRoot l ↔ p.eval l = 0 := Iff.rfl

/-- Axler 4.6 (and Hefferon Five.I.1.5): `λ` is a zero of `p` iff `p = (z - λ) q` for some
polynomial `q` (of one degree less when `p ≠ 0`). -/
@[kb "axler2024" "4.6, p. 140", kb "hefferon2020" "Five.I.1.5, p. 409"]
theorem axler_4_6 {K : Type*} [CommRing K] [IsDomain K] (p : K[X]) (l : K) :
    p.IsRoot l ↔ ∃ q : K[X], p = (X - C l) * q ∧ (p ≠ 0 → q.natDegree + 1 = p.natDegree) := by
  constructor
  · intro h
    refine ⟨p /ₘ (X - C l), (mul_divByMonic_eq_iff_isRoot.2 h).symm, fun hp => ?_⟩
    have := natDegree_divByMonic p (monic_X_sub_C l)
    rw [natDegree_X_sub_C] at this
    have hpos : 0 < p.natDegree := by
      by_contra h0
      have h0' : p.natDegree = 0 := by omega
      rw [natDegree_eq_zero] at h0'
      obtain ⟨c, rfl⟩ := h0'
      simp at h
      simp_all
    omega
  · rintro ⟨q, hq, -⟩
    simp [hq]

/-- Axler 4.8: a nonzero polynomial of degree `m` has at most `m` zeros. -/
@[kb "axler2024" "4.8, p. 141"]
theorem axler_4_8 {K : Type*} [CommRing K] [IsDomain K] (p : K[X]) :
    Multiset.card p.roots ≤ p.natDegree := card_roots' p

/-- Axler 4.12: fundamental theorem of algebra, existence of a zero. -/
@[kb "axler2024" "4.12, p. 143"]
theorem axler_4_12 (p : ℂ[X]) (hp : 0 < p.degree) : ∃ z : ℂ, p.IsRoot z :=
  Complex.exists_root hp

/-- Axler 4.13 (and Hefferon Five.I.1.11): a nonconstant complex polynomial factors as
`c (z - l₁) ⋯ (z - lₘ)`, and the list of zeros (with multiplicity) is unique. -/
@[kb "axler2024" "4.13, p. 144", kb "hefferon2020" "Five.I.1.11, p. 410"]
theorem axler_4_13 (p : ℂ[X]) (hp : 0 < p.degree) :
    (∃ (c : ℂ) (s : Multiset ℂ), c ≠ 0 ∧ Multiset.card s = p.natDegree ∧
      p = C c * (s.map fun l => X - C l).prod) ∧
    ∀ (c : ℂ) (s : Multiset ℂ), c ≠ 0 → p = C c * (s.map fun l => X - C l).prod →
      c = p.leadingCoeff ∧ s = p.roots := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  refine ⟨⟨p.leadingCoeff, p.roots, leadingCoeff_ne_zero.2 hp0, IsAlgClosed.card_roots_eq_natDegree,
    (C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree).symm⟩, ?_⟩
  intro c s hc h
  have hs : p.roots = s := by
    rw [h, roots_C_mul _ hc, roots_multiset_prod_X_sub_C]
  refine ⟨?_, hs.symm⟩
  rw [h, leadingCoeff_mul, leadingCoeff_C,
    (monic_multiset_prod_of_monic _ _ fun l _ => monic_X_sub_C l).leadingCoeff, mul_one]

/-- Axler 4.14: non-real zeros of a real polynomial come in conjugate pairs. -/
@[kb "axler2024" "4.14, p. 145"]
theorem axler_4_14 (p : ℝ[X]) (z : ℂ) (hz : aeval z p = 0) : aeval (starRingEnd ℂ z) p = 0 := by
  rw [Polynomial.aeval_conj (K := ℂ) p z, hz, map_zero]

end UndergradKB.LinearAlgebra.Course
