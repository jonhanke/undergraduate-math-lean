import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 17: polynomials

Results of chapter 17 that Mathlib does not state in the book's form. -/

open Polynomial

namespace UndergradKB.AbstractAlgebra

/-- AA-293. Over a field, `⟨p⟩` is a maximal ideal iff `p` is irreducible. -/
@[kb "judson2026" "Theorem 17.3.12, p. 239"]
theorem span_singleton_isMaximal_iff_irreducible {F : Type*} [Field F] (p : F[X]) :
    (Ideal.span {p}).IsMaximal ↔ Irreducible p := by
  constructor
  · intro hmax
    by_cases hp : p = 0
    · subst hp
      exfalso
      have h1 : (Ideal.span {(0 : F[X])}) = Ideal.span {X} := by
        apply hmax.eq_of_le
        · rw [Ne, Ideal.span_singleton_eq_top]; exact not_isUnit_X
        · simp
      have : (X : F[X]) ∈ Ideal.span {(0 : F[X])} := by
        rw [h1]; exact Ideal.subset_span rfl
      simp at this
    · exact ((Ideal.span_singleton_prime hp).mp hmax.isPrime).irreducible
  · intro h
    exact PrincipalIdealRing.isMaximal_of_irreducible h

/-- AA-290. Eisenstein's criterion over `ℚ`, for an integer polynomial of positive degree. -/
@[kb "judson2026" "Theorem 17.3.7, p. 238"]
theorem eisenstein_irreducible_rat (f : ℤ[X]) (p : ℤ) (hp : Prime p)
    (hdeg : 0 < f.natDegree)
    (hlead : ¬ p ∣ f.leadingCoeff)
    (hmid : ∀ n, n < f.natDegree → p ∣ f.coeff n)
    (h0 : ¬ p ^ 2 ∣ f.coeff 0) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hlead (by simp)
  have hc : f.content ≠ 0 := fun h => hf0 (content_eq_zero_iff.mp h)
  set g := f.primPart with hg
  have hfg : f = C f.content * g := (eq_C_content_mul_primPart f)
  have hgdeg : g.natDegree = f.natDegree := natDegree_primPart f
  have hcd : f.content ∣ f.leadingCoeff := by
    have := Polynomial.content_dvd_coeff (p := f) f.natDegree
    exact this
  have hpc : ¬ p ∣ f.content := fun h => hlead (h.trans hcd)
  have hcoeff : ∀ n, f.coeff n = f.content * g.coeff n := by
    intro n
    conv_lhs => rw [hfg]
    simp
  have hglead : g.leadingCoeff ∉ Ideal.span {p} := by
    rw [Ideal.mem_span_singleton]
    intro h
    apply hlead
    rw [leadingCoeff, hcoeff, ← hgdeg]
    exact Dvd.dvd.mul_left h _
  have hgP : ∀ n : ℕ, (n : WithBot ℕ) < degree g → g.coeff n ∈ Ideal.span {p} := by
    intro n hn
    have hn' : n < g.natDegree := by
      have hg0 : g ≠ 0 := by
        intro h; rw [h] at hgdeg; simp at hgdeg; omega
      rw [degree_eq_natDegree hg0] at hn
      exact_mod_cast hn
    rw [Ideal.mem_span_singleton]
    have := hmid n (by omega)
    rw [hcoeff] at this
    exact (hp.dvd_or_dvd this).resolve_left hpc
  have hgpos : 0 < degree g := by
    rw [natDegree_pos_iff_degree_pos.symm]; omega
  have hg0' : g.coeff 0 ∉ (Ideal.span {p}) ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    apply h0
    rw [hcoeff]
    exact Dvd.dvd.mul_left h _
  have hirr : Irreducible g :=
    irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hglead hgP hgpos hg0'
      (isPrimitive_primPart f)
  have hirrQ : Irreducible (g.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_primPart f)).mp hirr
  have hmap : f.map (Int.castRingHom ℚ) =
      C ((f.content : ℤ) : ℚ) * g.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [hfg]
    simp
  rw [hmap]
  refine (irreducible_isUnit_mul ?_).mpr hirrQ
  rw [isUnit_C]
  simpa using hc

/-- AA-323. A monic polynomial over a UFD `D` that is a product of two monic polynomials over the
fraction field `K` is a product of two monic polynomials over `D` of the same degrees. -/
@[kb "judson2026" "Corollary 18.2.21, p. 254"]
theorem monic_factor_of_map_ufd {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (p : D[X]) (hp : p.Monic) (α β : K[X]) (hα : α.Monic) (hβ : β.Monic)
    (h : p.map (algebraMap D K) = α * β) :
    ∃ a b : D[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      a.natDegree = α.natDegree ∧ b.natDegree = β.natDegree := by
  have hdα : α ∣ p.map (algebraMap D K) := ⟨β, h⟩
  have hdβ : β ∣ p.map (algebraMap D K) := ⟨α, by rw [mul_comm]; exact h⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp hdα
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp hdβ
  rw [hα.leadingCoeff, C_1, mul_one] at ha
  rw [hβ.leadingCoeff, C_1, mul_one] at hb
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  have ham : a.Monic := by
    apply monic_of_injective hinj
    rw [ha]; exact hα
  have hbm : b.Monic := by
    apply monic_of_injective hinj
    rw [hb]; exact hβ
  refine ⟨a, b, ham, hbm, ?_, ?_, ?_⟩
  · apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_mul, ha, hb]
    exact h
  · rw [← ha, natDegree_map_eq_of_injective hinj]
  · rw [← hb, natDegree_map_eq_of_injective hinj]

/-- AA-288. Gauss's lemma in the book's form: a monic integer polynomial that is a product of two
monic rational polynomials is a product of two monic integer polynomials of the same degrees. -/
@[kb "judson2026" "Theorem 17.3.4, p. 237"]
theorem gauss_lemma_monic (p : ℤ[X]) (hp : p.Monic) (α β : ℚ[X]) (hα : α.Monic) (hβ : β.Monic)
    (h : p.map (Int.castRingHom ℚ) = α * β) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      a.natDegree = α.natDegree ∧ b.natDegree = β.natDegree :=
  monic_factor_of_map_ufd ℚ p hp α β hα hβ (by simpa using h)

/-- AA-281. Uniqueness in the division algorithm over a field. -/
@[kb "judson2026" "Theorem 17.2.1, p. 233"]
theorem division_algorithm_unique {F : Type*} [Field F] {f g q q' r r' : F[X]} (hg : g ≠ 0)
    (h : f = g * q + r) (hr : r.degree < g.degree)
    (h' : f = g * q' + r') (hr' : r'.degree < g.degree) : q = q' ∧ r = r' := by
  have key : g * (q - q') = r' - r := by
    rw [mul_sub]; linear_combination h' - h
  have hq : q = q' := by
    by_contra hne
    have hne' : r' - r ≠ 0 := by
      rw [← key]; exact mul_ne_zero hg (sub_ne_zero.mpr hne)
    have h1 : g.degree ≤ (r' - r).degree := degree_le_of_dvd ⟨_, key.symm⟩ hne'
    have h2 : (r' - r).degree < g.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hr' hr)
    exact absurd h1 (not_le.mpr h2)
  subst hq
  refine ⟨rfl, ?_⟩
  linear_combination h' - h

/-- AA-281, existence part (Mathlib's Euclidean division): a quotient and remainder with
`deg r < deg g` exist. -/
theorem division_algorithm_exists {F : Type*} [Field F] (f : F[X]) {g : F[X]} (hg : g ≠ 0) :
    ∃ q r : F[X], f = g * q + r ∧ r.degree < g.degree :=
  ⟨f / g, f % g, by rw [EuclideanDomain.div_add_mod], degree_mod_lt f hg⟩

/-- AA-284. For `f, g` not both zero over a field there is exactly one monic common divisor that
is divisible by every common divisor (the monic gcd). -/
@[kb "judson2026" "Definition gcd of polynomials, p. 235"]
theorem exists_unique_monic_gcd {F : Type*} [Field F] (f g : F[X]) (h : f ≠ 0 ∨ g ≠ 0) :
    ∃! d : F[X], d.Monic ∧ d ∣ f ∧ d ∣ g ∧ ∀ e, e ∣ f → e ∣ g → e ∣ d := by
  classical
  set d0 := EuclideanDomain.gcd f g with hd0
  have hne : d0 ≠ 0 := by
    intro h0
    rw [hd0, EuclideanDomain.gcd_eq_zero_iff] at h0
    tauto
  have hu : IsUnit (C d0.leadingCoeff⁻¹ : F[X]) :=
    isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hne)).isUnit
  have hass : Associated d0 (d0 * C d0.leadingCoeff⁻¹) := ⟨hu.unit, rfl⟩
  have hmon : (d0 * C d0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hne
  have hf : d0 ∣ f := EuclideanDomain.gcd_dvd_left f g
  have hg : d0 ∣ g := EuclideanDomain.gcd_dvd_right f g
  refine ⟨d0 * C d0.leadingCoeff⁻¹, ⟨hmon, ?_, ?_, ?_⟩, ?_⟩
  · exact hass.symm.dvd_iff_dvd_left.mpr hf
  · exact hass.symm.dvd_iff_dvd_left.mpr hg
  · intro e he1 he2
    exact hass.dvd_iff_dvd_right.mp (EuclideanDomain.dvd_gcd he1 he2)
  · rintro d ⟨hm, hd1, hd2, hd3⟩
    have h1 : d ∣ d0 * C d0.leadingCoeff⁻¹ :=
      hass.dvd_iff_dvd_right.mp (EuclideanDomain.dvd_gcd hd1 hd2)
    have h2 : d0 * C d0.leadingCoeff⁻¹ ∣ d :=
      hd3 _ (hass.symm.dvd_iff_dvd_left.mpr hf) (hass.symm.dvd_iff_dvd_left.mpr hg)
    exact eq_of_monic_of_associated hm hmon (associated_of_dvd_dvd h1 h2)

/-- AA-287. A rational polynomial is `r/s` times a primitive integer polynomial, with
`gcd r s = 1` and `s ≠ 0`. -/
@[kb "judson2026" "Lemma 17.3.3, p. 237"]
theorem exists_primitive_smul_rat (f : ℚ[X]) :
    ∃ r s : ℤ, s ≠ 0 ∧ Int.gcd r s = 1 ∧ ∃ g : ℤ[X], g.IsPrimitive ∧
      f = C ((r : ℚ) / s) * g.map (Int.castRingHom ℚ) := by
  obtain ⟨b, hb, hf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f
  set h := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f with hh
  have hb0 : (b : ℚ) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hmap : h.map (Int.castRingHom ℚ) = C (b : ℚ) * f := by
    have : h.map (algebraMap ℤ ℚ) = b • f := hf
    rw [zsmul_eq_mul] at this
    simpa using this
  have hc : h = C h.content * h.primPart := eq_C_content_mul_primPart h
  set q : ℚ := (h.content : ℚ) / b with hq
  have hfq : f = C q * h.primPart.map (Int.castRingHom ℚ) := by
    have h1 : C (b : ℚ) * f = C (h.content : ℚ) * h.primPart.map (Int.castRingHom ℚ) := by
      rw [← hmap]
      conv_lhs => rw [hc]
      simp
    have h2 : f = C ((b : ℚ)⁻¹) * (C (b : ℚ) * f) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0]; simp
    rw [h2, h1, ← mul_assoc, ← C_mul, hq]
    congr 2
    field_simp
  refine ⟨q.num, q.den, by exact_mod_cast q.den_nz, ?_, h.primPart, isPrimitive_primPart h, ?_⟩
  · have := q.reduced
    simpa [Int.gcd] using this
  · have : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    rw [show ((q.den : ℤ) : ℚ) = (q.den : ℚ) by simp, this]
    exact hfq

/-- AA-279. The ring of polynomials in two indeterminates is `R[x][y]`: an `R`-algebra isomorphism
sending the first variable to the outer indeterminate and the second to the constant `x`. -/
@[kb "judson2026" "Definition polynomial ring in several indeterminates, p. 233"]
noncomputable def mvPolynomialFinTwoEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R) :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

theorem mvPolynomialFinTwoEquiv_X_zero (R : Type*) [CommRing R] :
    mvPolynomialFinTwoEquiv R (MvPolynomial.X 0) = Polynomial.X := by
  rw [mvPolynomialFinTwoEquiv, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero]
  simp

theorem mvPolynomialFinTwoEquiv_X_one (R : Type*) [CommRing R] :
    mvPolynomialFinTwoEquiv R (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  have : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
  rw [mvPolynomialFinTwoEquiv, AlgEquiv.trans_apply, this, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- AA-321. Lemma 18.2.19: if `p ≠ 0` over a UFD `D` factors as `f g` in `K[x]` (`K` the fraction
field), then `p = f₁ g₁` in `D[x]` with `deg f₁ = deg f` and `deg g₁ = deg g`. -/
@[kb "judson2026" "Lemma 18.2.19, p. 254"]
theorem factor_of_map_ufd {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (p : D[X]) (hp : p ≠ 0) (f g : K[X]) (h : p.map (algebraMap D K) = f * g) :
    ∃ f₁ g₁ : D[X], p = f₁ * g₁ ∧ f₁.natDegree = f.natDegree ∧ g₁.natDegree = g.natDegree := by
  let _ : NormalizedGCDMonoid D := Nonempty.some inferInstance
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  have hp' : p.map (algebraMap D K) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hf0 : f ≠ 0 := left_ne_zero_of_mul (h ▸ hp')
  have hg0 : g ≠ 0 := right_ne_zero_of_mul (h ▸ hp')
  obtain ⟨b, hb, hf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors D) f
  set f' := IsLocalization.integerNormalization (nonZeroDivisors D) f with hf'
  have hb0 : algebraMap D K b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hb (hinj (by simpa using h0))
  have hf'0 : f' ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hf
    have : b • f = 0 := hf.symm
    rw [Algebra.smul_def] at this
    simp [hb0, hf0] at this
  have hc0 : f'.content ≠ 0 := fun h0 => hf'0 (content_eq_zero_iff.mp h0)
  have hc0' : algebraMap D K f'.content ≠ 0 := fun h0 => hc0 (hinj (by simpa using h0))
  set u := f'.primPart with hu
  have hmap : f'.map (algebraMap D K) = C (algebraMap D K f'.content) * u.map (algebraMap D K) := by
    conv_lhs => rw [eq_C_content_mul_primPart f']
    rw [Polynomial.map_mul, Polynomial.map_C]
  have hfu : u.map (algebraMap D K) = C ((algebraMap D K f'.content)⁻¹ * algebraMap D K b) * f := by
    have h1 : C (algebraMap D K b) * f = C (algebraMap D K f'.content) * u.map (algebraMap D K) := by
      rw [← hmap, hf, Algebra.smul_def]
      simp
    rw [C_mul, mul_assoc, h1, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0']
    simp
  set q := (algebraMap D K f'.content)⁻¹ * algebraMap D K b with hq
  have hq0 : q ≠ 0 := mul_ne_zero (inv_ne_zero hc0') hb0
  have hf_eq : f = C q⁻¹ * u.map (algebraMap D K) := by
    rw [hfu, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hq0]; simp
  have hdvd : u.map (algebraMap D K) ∣ p.map (algebraMap D K) :=
    ⟨C q⁻¹ * g, by rw [h, hf_eq]; ring⟩
  obtain ⟨g₁, hg₁⟩ := ((isPrimitive_primPart f').dvd_iff_fraction_map_dvd_fraction_map K).mpr hdvd
  have hg_eq : g = C q * g₁.map (algebraMap D K) := by
    have h2 : f * g = f * (C q * g₁.map (algebraMap D K)) := by
      rw [← h, hg₁, Polynomial.map_mul, hfu]; ring
    exact mul_left_cancel₀ hf0 h2
  refine ⟨u, g₁, hg₁, ?_, ?_⟩
  · rw [← natDegree_map_eq_of_injective hinj, hfu, natDegree_C_mul hq0]
  · conv_rhs => rw [hg_eq]
    rw [natDegree_C_mul hq0, natDegree_map_eq_of_injective hinj]

/-- AA-292. In `F[x, y]` the ideal generated by `x` and `y` is not principal. -/
@[kb "judson2026" "Example 17.3.11, p. 239"]
theorem not_isPrincipal_span_X_X {F : Type*} [Field F] :
    ¬ (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) F), MvPolynomial.X 1}).IsPrincipal := by
  intro ⟨g, hg⟩
  set I : Ideal (MvPolynomial (Fin 2) F) := Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}
    with hI
  have hg0 : g ∈ I := by rw [hg]; exact Ideal.mem_span_singleton_self g
  have hnu : ¬ IsUnit g := by
    intro hu
    have h1 : I = ⊤ := Ideal.eq_top_of_isUnit_mem I hg0 hu
    have hle : I ≤ RingHom.ker (MvPolynomial.eval (fun _ : Fin 2 => (0 : F))) := by
      rw [hI, Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl <;> simp
    rw [h1] at hle
    have : (1 : MvPolynomial (Fin 2) F) ∈ RingHom.ker (MvPolynomial.eval (fun _ : Fin 2 => (0 : F))) :=
      hle Submodule.mem_top
    simp at this
  have key : ∀ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) F) ∈ I →
      (MvPolynomial.X i : MvPolynomial (Fin 2) F) ∣ g := by
    intro i hi
    rw [hg] at hi
    obtain ⟨h0, hh0⟩ := Ideal.mem_span_singleton'.mp hi
    -- hh0 : h0 * g = X i
    have hirr := (MvPolynomial.prime_X (R := F) (i := i)).irreducible
    rcases hirr.isUnit_or_isUnit hh0.symm with ⟨u, hu⟩ | hgu
    · refine ⟨↑u⁻¹, ?_⟩
      rw [← hh0, ← hu, mul_comm (↑u : MvPolynomial (Fin 2) F) g, mul_assoc, Units.mul_inv,
        mul_one]
    · exact absurd hgu hnu
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) F) ∈ I := Ideal.subset_span (by simp)
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) F) ∈ I := Ideal.subset_span (by simp)
  have hgd1 : g ∣ (MvPolynomial.X 1 : MvPolynomial (Fin 2) F) := by
    rw [hg] at hX1
    exact Ideal.mem_span_singleton.mp hX1
  have := (MvPolynomial.X_dvd_X (R := F) (i := 0) (j := 1)).mp ((key 0 hX0).trans hgd1)
  exact absurd this (by decide)

end UndergradKB.AbstractAlgebra
