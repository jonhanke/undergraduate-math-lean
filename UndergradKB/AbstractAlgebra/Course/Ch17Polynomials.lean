import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Prime.Int
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Polynomials

/-! # Judson–Beezer, chapter 17: polynomials (course layer)

Thin wrappers, in the book's terms, around Mathlib results. -/

namespace UndergradKB.AbstractAlgebra.Course

open Polynomial

/-- AA-277. For a commutative ring `R` with identity, `R[x]` is a commutative ring with
identity. -/
@[kb "judson2026" "Theorem 17.1.3, p. 232"]
theorem judson_17_1_3 {R : Type*} [CommRing R] :
    (∀ p q : R[X], p * q = q * p) ∧ (∀ p : R[X], 1 * p = p ∧ p * 1 = p) :=
  ⟨fun _ _ => mul_comm _ _, fun p => ⟨one_mul p, mul_one p⟩⟩

/-- AA-278. Over an integral domain, `deg (p q) = deg p + deg q` and `R[x]` is an integral
domain. -/
@[kb "judson2026" "Proposition 17.1.4, p. 232"]
theorem judson_17_1_4 {R : Type*} [CommRing R] [IsDomain R] :
    (∀ p q : R[X], (p * q).degree = p.degree + q.degree) ∧ IsDomain R[X] :=
  ⟨fun _ _ => Polynomial.degree_mul, inferInstance⟩

/-- AA-280. Evaluation at `α ∈ R` is a ring homomorphism `R[x] → R`. -/
@[kb "judson2026" "Theorem 17.1.5, p. 233"]
theorem judson_17_1_5 {R : Type*} [CommRing R] (α : R) :
    ∃ φ : R[X] →+* R, ∀ p : R[X], φ p = p.eval α :=
  ⟨Polynomial.evalRingHom α, fun _ => rfl⟩

private lemma deg_lt_of_eq_zero_or {F : Type*} [Field F] {g r : F[X]} (hg : g ≠ 0)
    (h : r = 0 ∨ r.degree < g.degree) : r.degree < g.degree := by
  rcases h with rfl | h
  · rw [degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by simpa [degree_eq_bot] using hg)
  · exact h

/-- AA-281. Division algorithm in `F[x]`: for `g ≠ 0` there are unique `q, r` with
`f = g q + r` and `r = 0` or `deg r < deg g`. -/
@[kb "judson2026" "Theorem 17.2.1, p. 233"]
theorem judson_17_2_1 {F : Type*} [Field F] (f g : F[X]) (hg : g ≠ 0) :
    ∃ q r : F[X], f = g * q + r ∧ (r = 0 ∨ r.degree < g.degree) ∧
      ∀ q' r' : F[X], f = g * q' + r' → (r' = 0 ∨ r'.degree < g.degree) → q' = q ∧ r' = r := by
  refine ⟨f / g, f % g, (EuclideanDomain.div_add_mod f g).symm, Or.inr (degree_mod_lt f hg), ?_⟩
  intro q' r' h1 h2
  have e : g * (f / g) + f % g = g * q' + r' := (EuclideanDomain.div_add_mod f g).trans h1
  have hr' := deg_lt_of_eq_zero_or hg h2
  have hr := degree_mod_lt f hg
  have key : g * (f / g - q') = r' - f % g := by
    rw [mul_sub]; linear_combination e
  have hq : f / g = q' := by
    by_contra hne
    have hne' : f / g - q' ≠ 0 := sub_ne_zero.mpr hne
    have h3 : g.degree ≤ (r' - f % g).degree := by
      rw [← key, degree_mul]
      exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hne')
    have h4 : (r' - f % g).degree < g.degree :=
      (degree_sub_le r' (f % g)).trans_lt (max_lt hr' hr)
    exact absurd h3 (not_le.mpr h4)
  subst hq
  refine ⟨rfl, ?_⟩
  have : r' = f % g := by
    have := e
    simpa using this.symm
  exact this

/-- AA-282. `α` is a zero of `p` iff `x - α` divides `p`. -/
@[kb "judson2026" "Corollary 17.2.3, p. 235"]
theorem judson_17_2_3 {F : Type*} [Field F] (p : F[X]) (α : F) :
    p.IsRoot α ↔ (X - C α) ∣ p :=
  (Polynomial.dvd_iff_isRoot).symm

/-- AA-283. A nonzero polynomial of degree `n` over a field has at most `n` distinct zeros. -/
@[kb "judson2026" "Corollary 17.2.4, p. 235"]
theorem judson_17_2_4 {F : Type*} [Field F] (p : F[X]) (hp : p ≠ 0) (Z : Finset F)
    (hZ : ∀ z ∈ Z, p.IsRoot z) : Z.card ≤ p.natDegree :=
  Polynomial.card_le_degree_of_subset_roots (fun z hz => by
    rw [Polynomial.mem_roots hp]; exact hZ z hz)

/-- AA-285. Bezout in `F[x]`: for `p, q` not both zero there is a unique monic common divisor
`d` divisible by every common divisor (the gcd), and `d = r p + s q` for some `r, s`. -/
@[kb "judson2026" "Proposition 17.2.5, p. 235"]
theorem judson_17_2_5 {F : Type*} [Field F] (p q : F[X]) (hpq : p ≠ 0 ∨ q ≠ 0) :
    (∃ d : F[X], (d.Monic ∧ d ∣ p ∧ d ∣ q ∧ ∀ e, e ∣ p → e ∣ q → e ∣ d) ∧
      ∃ r s : F[X], d = r * p + s * q) ∧
    ∀ d d' : F[X], (d.Monic ∧ d ∣ p ∧ d ∣ q ∧ ∀ e, e ∣ p → e ∣ q → e ∣ d) →
      (d'.Monic ∧ d' ∣ p ∧ d' ∣ q ∧ ∀ e, e ∣ p → e ∣ q → e ∣ d') → d = d' := by
  refine ⟨?_, ?_⟩
  · classical
    set g := EuclideanDomain.gcd p q with hg
    have hg0 : g ≠ 0 := by
      intro h0
      rw [hg, EuclideanDomain.gcd_eq_zero_iff] at h0
      rcases hpq with h | h
      · exact h h0.1
      · exact h h0.2
    have hc : IsUnit (C g.leadingCoeff⁻¹) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)))
    refine ⟨C g.leadingCoeff⁻¹ * g, ⟨?_, ?_, ?_, ?_⟩,
      C g.leadingCoeff⁻¹ * EuclideanDomain.gcdA p q,
      C g.leadingCoeff⁻¹ * EuclideanDomain.gcdB p q, ?_⟩
    · exact monic_C_mul_of_mul_leadingCoeff_eq_one
        (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hg0))
    · exact hc.mul_left_dvd.mpr (EuclideanDomain.gcd_dvd_left p q)
    · exact hc.mul_left_dvd.mpr (EuclideanDomain.gcd_dvd_right p q)
    · exact fun e h1 h2 => dvd_mul_of_dvd_right (EuclideanDomain.dvd_gcd h1 h2) _
    · have := EuclideanDomain.gcd_eq_gcd_ab p q
      rw [← hg] at this
      linear_combination (C g.leadingCoeff⁻¹) * this
  · rintro d d' ⟨hm, h1, h2, hd⟩ ⟨hm', h1', h2', hd'⟩
    have hdd : d ∣ d' := hd' d h1 h2
    have hd'd : d' ∣ d := hd d' h1' h2'
    exact eq_of_monic_of_associated hm hm' (associated_of_dvd_dvd hdd hd'd)

/-- AA-289. A monic integer polynomial with a rational zero has an integer zero, which divides
the constant term. -/
@[kb "judson2026" "Corollary 17.3.5, p. 238"]
theorem judson_17_3_5 (p : ℤ[X]) (hp : p.Monic) (α : ℚ)
    (hα : (p.map (Int.castRingHom ℚ)).IsRoot α) :
    ∃ m : ℤ, (m : ℚ) = α ∧ p.IsRoot m ∧ m ∣ p.coeff 0 := by
  have h0 : aeval α p = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact hα
  obtain ⟨m, hm⟩ := isInteger_of_is_root_of_monic hp h0
  have hm' : (m : ℚ) = α := by simpa using hm
  have hroot : p.IsRoot m := by
    subst hm'
    have : ((p.eval m : ℤ) : ℚ) = 0 := by
      have h := hα
      rw [IsRoot, eval_map, eval₂_at_intCast] at h
      simpa using h
    exact_mod_cast this
  exact ⟨m, hm', hroot, hroot.dvd_coeff_zero⟩

/-- AA-291. If `F` is a field, every ideal of `F[x]` is principal. -/
@[kb "judson2026" "Theorem 17.3.10, p. 239"]
theorem judson_17_3_10 {F : Type*} [Field F] (I : Ideal F[X]) : ∃ p : F[X], I = Ideal.span {p} :=
  ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩

/-- AA-293. For a field `F` and nonzero `p ∈ F[x]`, the ideal `⟨p⟩` is maximal iff `p` is
irreducible. -/
@[kb "judson2026" "Theorem 17.3.12, p. 239"]
theorem judson_17_3_12 {F : Type*} [Field F] (p : F[X]) (hp : p ≠ 0) :
    (Ideal.span {p}).IsMaximal ↔ Irreducible p :=
  (Ideal.irreducible_iff_isMaximal_span_singleton hp).symm

/-- AA-290. Eisenstein's criterion: if a prime `q` divides every coefficient of a nonconstant
`f ∈ ℤ[x]` except the leading one, and `q² ∤ f(0)`, then `f` is irreducible over `ℚ`. -/
@[kb "judson2026" "Theorem 17.3.7, p. 238"]
theorem judson_17_3_7 (f : ℤ[X]) (q : ℕ) (hq : q.Prime) (hn : 0 < f.natDegree)
    (hlead : ¬ (q : ℤ) ∣ f.leadingCoeff) (hdiv : ∀ i < f.natDegree, (q : ℤ) ∣ f.coeff i)
    (h0 : ¬ ((q : ℤ) ^ 2 ∣ f.coeff 0)) : Irreducible (f.map (Int.castRingHom ℚ)) := by
  have hqp : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hf0 : f ≠ 0 := by rintro rfl; simp at hn
  set c := f.content with hc
  set g := f.primPart with hgdef
  have hf : f = C c * g := eq_C_content_mul_primPart f
  have hc0 : c ≠ 0 := by
    intro h
    exact hf0 (by rw [hf, h]; simp)
  have hcoeff : ∀ i, f.coeff i = c * g.coeff i := fun i => by
    conv_lhs => rw [hf]
    rw [coeff_C_mul]
  have hdeg : g.natDegree = f.natDegree := natDegree_primPart f
  have hqc : ¬ (q : ℤ) ∣ c := by
    intro h
    apply hlead
    rw [leadingCoeff, hcoeff]
    exact dvd_mul_of_dvd_left h _
  have hgrp : g.IsPrimitive := isPrimitive_primPart f
  have hirr : Irreducible g := by
    apply irreducible_of_eisenstein_criterion (P := Ideal.span {(q : ℤ)})
      ((Ideal.span_singleton_prime hqp.ne_zero).mpr hqp)
    · rw [Ideal.mem_span_singleton]
      intro h
      apply hlead
      rw [leadingCoeff, hcoeff, ← hdeg]
      exact dvd_mul_of_dvd_right h _
    · intro n hn'
      rw [Ideal.mem_span_singleton]
      have hn2 : n < g.natDegree := by
        rw [degree_eq_natDegree (by rintro h; rw [h] at hdeg; simp at hdeg; omega)] at hn'
        exact_mod_cast hn'
      have := hdiv n (hdeg ▸ hn2)
      rw [hcoeff] at this
      exact (hqp.dvd_or_dvd this).resolve_left hqc
    · exact natDegree_pos_iff_degree_pos.mp (hdeg ▸ hn)
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      apply h0
      rw [hcoeff]
      exact dvd_mul_of_dvd_right h _
    · exact hgrp
  have h1 := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hgrp).mp hirr
  have h2 : f.map (Int.castRingHom ℚ) = C (c : ℚ) * g.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [hf]
    simp
  rw [h2]
  exact (irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc0)))).mpr h1

/-- AA-287. A rational polynomial is `r/s` times an integer polynomial with coprime coefficients
(primitive), where `gcd(r, s) = 1`. -/
@[kb "judson2026" "Lemma 17.3.3, p. 237"]
theorem judson_17_3_3 (f : ℚ[X]) :
    ∃ r s : ℤ, s ≠ 0 ∧ Int.gcd r s = 1 ∧ ∃ g : ℤ[X], g.IsPrimitive ∧
      f = C ((r : ℚ) / s) * g.map (Int.castRingHom ℚ) :=
  exists_primitive_smul_rat f

/-- AA-288. Gauss's Lemma: a monic integer polynomial that factors over `ℚ` into monic factors
factors over `ℤ` into monic factors of the same degrees. -/
@[kb "judson2026" "Theorem 17.3.4, p. 237"]
theorem judson_17_3_4 (p : ℤ[X]) (hp : p.Monic) (α β : ℚ[X]) (hα : α.Monic) (hβ : β.Monic)
    (h : p.map (Int.castRingHom ℚ) = α * β) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      a.natDegree = α.natDegree ∧ b.natDegree = β.natDegree :=
  gauss_lemma_monic p hp α β hα hβ h

end UndergradKB.AbstractAlgebra.Course
