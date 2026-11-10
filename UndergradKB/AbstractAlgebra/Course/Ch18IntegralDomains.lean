import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Polynomials

/-! # Judson–Beezer, chapter 18: integral domains (course layer)

Thin wrappers, in the book's terms, around Mathlib results. -/

namespace UndergradKB.AbstractAlgebra.Course

open Polynomial

universe u

/-- AA-294. Every integral domain `D` has a field of fractions: a field `K` in which `D`
embeds and every element is a quotient of elements of `D` (Mathlib's `IsFractionRing`). -/
@[kb "judson2026" "Lemma 18.1.3, p. 248"]
theorem judson_18_1_3 (D : Type u) [CommRing D] [IsDomain D] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra D K), IsFractionRing D K :=
  ⟨FractionRing D, inferInstance, inferInstance, inferInstance⟩

/-- AA-295. In a field of fractions `K` of a domain `D`, the map `D → K` is injective, every
element of `K` is a quotient of two elements of `D`, and every injective ring map from `D`
into a field `E` extends uniquely to `K → E`. -/
@[kb "judson2026" "Theorem 18.1.4, p. 248"]
theorem judson_18_1_4 (D K E : Type*) [CommRing D] [IsDomain D] [Field K] [Field E] [Algebra D K]
    [IsFractionRing D K] (f : D →+* E) (hf : Function.Injective f) :
    Function.Injective (algebraMap D K) ∧
      (∀ x : K, ∃ a b : D, b ≠ 0 ∧ algebraMap D K a / algebraMap D K b = x) ∧
      ∃! g : K →+* E, ∀ a : D, g (algebraMap D K a) = f a := by
  refine ⟨IsFractionRing.injective D K, fun x => ?_, ⟨IsFractionRing.lift hf, fun a => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := D) x
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, h⟩
  · simp
  · intro g hg
    exact (IsFractionRing.lift_unique hf hg).symm

/-- AA-296. The field of fractions of `F[x]` is the field of rational expressions `F(x)`. -/
@[kb "judson2026" "Example 18.1.5, p. 249"]
theorem judson_18_1_5 (F : Type*) [Field F] : IsFractionRing F[X] (RatFunc F) :=
  inferInstance

/-- AA-297. A field of characteristic 0 contains a copy of `ℚ`. -/
@[kb "judson2026" "Corollary 18.1.6, p. 249"]
theorem judson_18_1_6 (F : Type*) [Field F] [CharZero F] :
    ∃ f : ℚ →+* F, Function.Injective f :=
  ⟨Rat.castHom F, (Rat.castHom F).injective⟩

/-- AA-297. A field of characteristic `p` (prime) contains a copy of `ℤ_p`. -/
@[kb "judson2026" "Corollary 18.1.7, p. 249"]
theorem judson_18_1_7 (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ f : ZMod p →+* F, Function.Injective f :=
  ⟨ZMod.castHom (dvd_refl p) F, (ZMod.castHom (dvd_refl p) F).injective⟩

/-- AA-303. `ℤ` is a unique factorization domain (fundamental theorem of arithmetic). -/
@[kb "judson2026" "Example 18.2.2, p. 250"]
theorem judson_18_2_2 : UniqueFactorizationMonoid ℤ := inferInstance

/-- AA-306. In a domain: `a ∣ b` iff `⟨b⟩ ⊆ ⟨a⟩`; `a, b` are associates iff `⟨a⟩ = ⟨b⟩`; `a`
is a unit iff `⟨a⟩ = D`. -/
@[kb "judson2026" "Lemma 18.2.4, p. 250"]
theorem judson_18_2_4 {D : Type*} [CommRing D] [IsDomain D] (a b : D) :
    (a ∣ b ↔ Ideal.span {b} ≤ Ideal.span {a}) ∧
      (Associated a b ↔ Ideal.span {a} = Ideal.span {b}) ∧
      (IsUnit a ↔ Ideal.span {a} = ⊤) :=
  ⟨Ideal.span_singleton_le_span_singleton.symm, Ideal.span_singleton_eq_span_singleton.symm,
    (Ideal.span_singleton_eq_top).symm⟩

/-- AA-307. In a PID, a nonzero principal ideal `⟨p⟩` is maximal iff `p` is irreducible. -/
@[kb "judson2026" "Theorem 18.2.5, p. 250"]
theorem judson_18_2_5 {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (p : D)
    (hp : p ≠ 0) : (Ideal.span {p}).IsMaximal ↔ Irreducible p :=
  (Ideal.irreducible_iff_isMaximal_span_singleton hp).symm

/-- AA-308. In a PID, every irreducible element is prime. -/
@[kb "judson2026" "Corollary 18.2.6, p. 251"]
theorem judson_18_2_6 {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] (p : D)
    (hp : Irreducible p) : Prime p :=
  hp.prime

/-- AA-310. In a PID, every ascending chain of ideals stabilizes. -/
@[kb "judson2026" "Lemma 18.2.7, p. 251"]
theorem judson_18_2_7 {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
    (I : ℕ →o Ideal D) : ∃ n, ∀ m, n ≤ m → I n = I m :=
  monotone_stabilizes_iff_noetherian.mpr inferInstance I

/-- AA-311. Every PID is a UFD. -/
@[kb "judson2026" "Theorem 18.2.8, p. 251"]
theorem judson_18_2_8 {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D] :
    UniqueFactorizationMonoid D :=
  inferInstance

/-- AA-312. If `F` is a field then `F[x]` is a UFD. -/
@[kb "judson2026" "Corollary 18.2.9, p. 252"]
theorem judson_18_2_9 (F : Type*) [Field F] : UniqueFactorizationMonoid F[X] :=
  inferInstance

/-- AA-315. `ℤ`, `F[x]` (`F` a field) and the Gaussian integers `ℤ[i]` are Euclidean domains. -/
@[kb "judson2026" "Example 18.2.11, p. 252"]
theorem judson_18_2_11 (F : Type*) [Field F] :
    Nonempty (EuclideanDomain ℤ) ∧ Nonempty (EuclideanDomain F[X]) ∧
      Nonempty (EuclideanDomain GaussianInt) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- AA-316. Every Euclidean domain is a PID. -/
@[kb "judson2026" "Theorem 18.2.14, p. 253"]
theorem judson_18_2_14 {D : Type*} [EuclideanDomain D] : IsPrincipalIdealRing D :=
  inferInstance

/-- AA-317. Every Euclidean domain is a UFD. -/
@[kb "judson2026" "Corollary 18.2.15, p. 253"]
theorem judson_18_2_15 {D : Type*} [EuclideanDomain D] : UniqueFactorizationMonoid D :=
  inferInstance

/-- AA-319. Gauss's lemma: a product of primitive polynomials over a UFD is primitive. -/
@[kb "judson2026" "Theorem 18.2.17, p. 254"]
theorem judson_18_2_17 {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    {p q : D[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive := by
  classical
  let : StrongNormalizationMonoid D := UniqueFactorizationMonoid.strongNormalizationMonoid
  let : StrongNormalizedGCDMonoid D := UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid D
  exact hp.mul hq

/-- AA-320. Over a domain with normalized gcds (every UFD admits such a structure), the content
of a product of polynomials is the product of the contents. -/
@[kb "judson2026" "Lemma 18.2.18, p. 254"]
theorem judson_18_2_18 {D : Type*} [CommRing D] [IsDomain D] [StrongNormalizedGCDMonoid D]
    (p q : D[X]) : (p * q).content = p.content * q.content :=
  Polynomial.content_mul

/-- AA-322. For `F` the field of fractions of a UFD `D`, a primitive `p ∈ D[x]` is irreducible
in `D[x]` iff it is irreducible in `F[x]`. -/
@[kb "judson2026" "Corollary 18.2.20, p. 254"]
theorem judson_18_2_20 {D : Type*} (F : Type*) [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] [Field F] [Algebra D F] [IsFractionRing D F] {p : D[X]}
    (hp : p.IsPrimitive) : Irreducible p ↔ Irreducible (p.map (algebraMap D F)) := by
  classical
  let : StrongNormalizationMonoid D := UniqueFactorizationMonoid.strongNormalizationMonoid
  let : StrongNormalizedGCDMonoid D := UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid D
  exact hp.irreducible_iff_irreducible_map_fraction_map

/-- AA-324. If `D` is a UFD then `D[x]` is a UFD. -/
@[kb "judson2026" "Theorem 18.2.22, p. 254"]
theorem judson_18_2_22 {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D] :
    UniqueFactorizationMonoid D[X] :=
  inferInstance

/-- AA-324. `ℤ[x]` is a UFD. -/
@[kb "judson2026" "Corollary 18.2.24, p. 255"]
theorem judson_18_2_24 : UniqueFactorizationMonoid ℤ[X] := inferInstance

/-- AA-325. If `D` is a UFD then `D[x₁, …, xₙ]` is a UFD (here for any set of variables). -/
@[kb "judson2026" "Corollary 18.2.25, p. 255"]
theorem judson_18_2_25 (σ : Type*) {D : Type*} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] : UniqueFactorizationMonoid (MvPolynomial σ D) :=
  MvPolynomial.uniqueFactorizationMonoid σ

/-- AA-321. Let `D` be a UFD with fraction field `F`. If a nonzero `p ∈ D[x]` factors in `F[x]`,
it factors in `D[x]` with factors of the same degrees. -/
@[kb "judson2026" "Lemma 18.2.19, p. 254"]
theorem judson_18_2_19 {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (p : D[X]) (hp : p ≠ 0) (f g : K[X]) (h : p.map (algebraMap D K) = f * g) :
    ∃ f₁ g₁ : D[X], p = f₁ * g₁ ∧ f₁.natDegree = f.natDegree ∧ g₁.natDegree = g.natDegree :=
  factor_of_map_ufd K p hp f g h

/-- AA-323. A monic `p ∈ D[x]` (`D` a UFD with fraction field `F`) that factors into monic
polynomials in `F[x]` factors in `D[x]` into monic polynomials of the same degrees. -/
@[kb "judson2026" "Corollary 18.2.21, p. 254"]
theorem judson_18_2_21 {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (p : D[X]) (hp : p.Monic) (α β : K[X]) (hα : α.Monic) (hβ : β.Monic)
    (h : p.map (algebraMap D K) = α * β) :
    ∃ a b : D[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      a.natDegree = α.natDegree ∧ b.natDegree = β.natDegree :=
  monic_factor_of_map_ufd K p hp α β hα hβ h

end UndergradKB.AbstractAlgebra.Course
