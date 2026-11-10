import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 16: rings

Results of chapter 16 that Mathlib does not state in the book's form. Note on conventions: the book
does not assume rings have an identity, while Mathlib's `Ring` is unital. Where this matters the
statements below say so. -/

namespace UndergradKB.AbstractAlgebra

section Subring

variable {R : Type*} [Ring R]

/-- AA-245. Subring criterion, in the unital convention of Mathlib: a subset is (the carrier of) a
subring iff it contains `1` and is closed under products and differences. -/
@[kb "judson2026" "Proposition 16.1.10, p. 213"]
theorem exists_subring_iff (S : Set R) :
    (∃ T : Subring R, (T : Set R) = S) ↔
      1 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, ∀ b ∈ S, a - b ∈ S) := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨T.one_mem, fun a ha b hb => T.mul_mem ha hb, fun a ha b hb => T.sub_mem ha hb⟩
  · rintro ⟨h1, hmul, hsub⟩
    have h0 : (0 : R) ∈ S := by simpa using hsub 1 h1 1 h1
    have hneg : ∀ a ∈ S, -a ∈ S := fun a ha => by simpa using hsub 0 h0 a ha
    exact ⟨{ carrier := S
             mul_mem' := fun {a b} ha hb => hmul a ha b hb
             one_mem' := h1
             add_mem' := fun {a b} ha hb => by simpa using hsub a ha (-b) (hneg b hb)
             zero_mem' := h0
             neg_mem' := fun {a} ha => hneg a ha }, rfl⟩

end Subring

section NonUnitalSubring

variable {R : Type*} [NonUnitalRing R]

/-- AA-245, in the book's convention (rings need not have `1`): a subset is a subring iff it is
nonempty and closed under products and differences. -/
theorem exists_nonUnitalSubring_iff (S : Set R) :
    (∃ T : NonUnitalSubring R, (T : Set R) = S) ↔
      S.Nonempty ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, ∀ b ∈ S, a - b ∈ S) := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨⟨0, T.zero_mem⟩, fun a ha b hb => T.mul_mem ha hb, fun a ha b hb => T.sub_mem ha hb⟩
  · rintro ⟨⟨x, hx⟩, hmul, hsub⟩
    have h0 : (0 : R) ∈ S := by simpa using hsub x hx x hx
    have hneg : ∀ a ∈ S, -a ∈ S := fun a ha => by simpa using hsub 0 h0 a ha
    exact ⟨{ carrier := S
             mul_mem' := fun {a b} ha hb => hmul a ha b hb
             add_mem' := fun {a b} ha hb => by simpa using hsub a ha (-b) (hneg b hb)
             zero_mem' := h0
             neg_mem' := fun {a} ha => hneg a ha }, rfl⟩

end NonUnitalSubring

/-- Book's zero divisor: a nonzero element `a` with `a * b = 0` for some nonzero `b`. -/
def IsBookZeroDivisor {R : Type*} [Mul R] [Zero R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b ≠ 0, a * b = 0

/-- AA-238. A nontrivial commutative ring is an integral domain iff it has no zero divisors. -/
@[kb "judson2026" "Definition zero divisor, p. 211"]
theorem isDomain_iff_no_zero_divisors (R : Type*) [CommRing R] [Nontrivial R] :
    IsDomain R ↔ ∀ a : R, ¬ IsBookZeroDivisor a := by
  constructor
  · intro h a ⟨ha, b, hb, hab⟩
    exact hb ((mul_eq_zero.mp hab).resolve_left ha)
  · intro h
    have : NoZeroDivisors R :=
      ⟨fun {a b} hab => by
        by_contra hne
        rw [not_or] at hne
        exact h a ⟨hne.1, b, hne.2, hab⟩⟩
    exact NoZeroDivisors.to_isDomain R

/-- AA-271. The nonzero prime ideals of `ℤ` are exactly `pℤ` for `p` a prime number. -/
@[kb "judson2026" "Example 16.4.5, p. 219"]
theorem int_ideal_isPrime_ne_bot_iff (I : Ideal ℤ) :
    (I.IsPrime ∧ I ≠ ⊥) ↔ ∃ p : ℕ, p.Prime ∧ I = Ideal.span {(p : ℤ)} := by
  constructor
  · rintro ⟨hI, hne⟩
    obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
    have ha : a ≠ 0 := by
      rintro rfl
      exact hne (by simp)
    have hp : Prime a := (Ideal.span_singleton_prime ha).mp hI
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hp, ?_⟩
    rw [Int.span_natAbs]
  · rintro ⟨p, hp, rfl⟩
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    refine ⟨(Ideal.span_singleton_prime hp'.ne_zero).mpr hp', ?_⟩
    simpa using hp'.ne_zero

/-- AA-271. For `p` prime, `pℤ` is a maximal ideal of `ℤ`. -/
@[kb "judson2026" "Example 16.4.2, p. 219"]
theorem int_span_isMaximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  haveI := Fact.mk hp
  Int.ideal_span_isMaximal_of_prime p

/-- AA-252. The units of the Gaussian integers are `±1, ±i`. -/
@[kb "judson2026" "Example 16.2.1, p. 214"]
theorem gaussianInt_isUnit_iff (z : GaussianInt) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = Zsqrtd.mk 0 1 ∨ z = Zsqrtd.mk 0 (-1) := by
  rw [← Zsqrtd.norm_eq_one_iff' (by norm_num)]
  obtain ⟨a, b⟩ := z
  simp only [Zsqrtd.norm_def]
  constructor
  · intro h
    have hs : a * a + b * b = 1 := by linarith
    have ha : a ≤ 1 := by nlinarith [mul_self_nonneg b]
    have ha' : -1 ≤ a := by nlinarith [mul_self_nonneg b]
    have hb : b ≤ 1 := by nlinarith [mul_self_nonneg a]
    have hb' : -1 ≤ b := by nlinarith [mul_self_nonneg a]
    interval_cases a <;> interval_cases b <;> simp_all [Zsqrtd.ext_iff]
  · intro h
    rcases h with h | h | h | h <;> simp [Zsqrtd.ext_iff] at h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num

/-- AA-252. The Gaussian integers are an integral domain but not a field. -/
theorem gaussianInt_isDomain_not_field : IsDomain GaussianInt ∧ ¬ IsField GaussianInt := by
  refine ⟨inferInstance, fun hf => ?_⟩
  have h2 : (2 : GaussianInt) ≠ 0 := by decide
  obtain ⟨w, hw⟩ := hf.mul_inv_cancel h2
  have : IsUnit (2 : GaussianInt) := IsUnit.of_mul_eq_one w hw
  rw [gaussianInt_isUnit_iff] at this
  simp [Zsqrtd.ext_iff] at this


/-- AA-265. Correspondence theorem, ideal part: ideals of `R ⧸ I` correspond to ideals of `R`
containing `I`, order-preservingly in both directions (the map is `comap` of the quotient map). -/
@[kb "judson2026" "Theorem 16.3.15, p. 218"]
noncomputable def idealQuotientOrderIso {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal (R ⧸ I) ≃o {J : Ideal R // I ≤ J} :=
  have hI : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := Ideal.mk_ker
  let e := Ideal.relIsoOfSurjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  { toFun := fun J => ⟨(e J).1, hI.symm.le.trans (e J).2⟩
    invFun := fun J => e.symm ⟨J.1, hI.le.trans J.2⟩
    left_inv := fun J => by simp
    right_inv := fun J => by
      apply Subtype.ext
      simp [e]
    map_rel_iff' := fun {J K} => by
      have := e.map_rel_iff (a := J) (b := K)
      simp }

theorem idealQuotientOrderIso_apply {R : Type*} [CommRing R] (I : Ideal R) (J : Ideal (R ⧸ I)) :
    (idealQuotientOrderIso I J : Ideal R) = J.comap (Ideal.Quotient.mk I) := rfl

section RingHom

variable {R S : Type*}

/-- AA-254. The image of a commutative ring under a ring homomorphism is commutative. -/
@[kb "judson2026" "Proposition 16.3.3, p. 216"]
theorem range_mul_comm [CommRing R] [Ring S] (f : R →+* S) (x y : f.range) : x * y = y * x := by
  obtain ⟨x, a, rfl⟩ := x
  obtain ⟨y, b, rfl⟩ := y
  ext
  simp [← map_mul, mul_comm]

/-- AA-254. A homomorphism from a field to a nontrivial ring is injective. -/
theorem injective_of_field [Field R] [Semiring S] [Nontrivial S] (f : R →+* S) :
    Function.Injective f :=
  f.injective

/-- AA-254. The image of a field under a ring homomorphism to a nontrivial ring is a field. -/
theorem isField_range [Field R] [Ring S] [Nontrivial S] (f : R →+* S) : IsField f.range := by
  refine ⟨⟨0, 1, ?_⟩, range_mul_comm f, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp at this
  · rintro ⟨x, a, rfl⟩ hx
    have ha : a ≠ 0 := fun h => hx (by simp [h])
    refine ⟨⟨f a⁻¹, a⁻¹, rfl⟩, ?_⟩
    ext
    simp [← map_mul, ha]

end RingHom

section SecondIso

variable {R : Type*} [CommRing R] (S : Subring R) (I : Ideal R)

/-- The sum `S + I` of a subring and an ideal, as a subring of `R` (the preimage in `R` of the image
of `S` in `R ⧸ I`). -/
def subringAddIdeal : Subring R :=
  (S.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I)

theorem mem_subringAddIdeal {x : R} : x ∈ subringAddIdeal S I ↔ ∃ s ∈ S, ∃ i ∈ I, s + i = x := by
  simp only [subringAddIdeal, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, x - s, by rw [← Ideal.Quotient.eq]; exact h.symm, by ring⟩
  · rintro ⟨s, hs, i, hi, rfl⟩
    exact ⟨s, hs, by rw [Ideal.Quotient.eq]; simpa using I.neg_mem hi⟩

/-- AA-263. Second isomorphism theorem for rings, in the book's form: for a subring `S` and an ideal
`I` of a commutative ring, `S / (S ∩ I) ≅ (S + I) / I`, where `S ∩ I` is the ideal
`I.comap S.subtype` of `S` and `I` is regarded as an ideal of the subring `S + I`. -/
@[kb "judson2026" "Theorem 16.3.13, p. 218"]
theorem second_isomorphism_theorem :
    Nonempty (S ⧸ I.comap S.subtype ≃+*
      (subringAddIdeal S I) ⧸ I.comap (subringAddIdeal S I).subtype) := by
  set T := subringAddIdeal S I with hT
  have hS : RingHom.ker ((Ideal.Quotient.mk I).comp S.subtype) = I.comap S.subtype := by
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hT' : RingHom.ker ((Ideal.Quotient.mk I).comp T.subtype) = I.comap T.subtype := by
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hr : ((Ideal.Quotient.mk I).comp T.subtype).range =
      ((Ideal.Quotient.mk I).comp S.subtype).range := by
    ext y
    simp only [RingHom.mem_range, RingHom.comp_apply, Subring.subtype_apply]
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨s, hs, hst⟩ := (Subring.mem_map.mp ht)
      exact ⟨⟨s, hs⟩, hst⟩
    · rintro ⟨⟨s, hs⟩, rfl⟩
      exact ⟨⟨s, Subring.mem_comap.mpr (Subring.mem_map.mpr ⟨s, hs, rfl⟩)⟩, rfl⟩
  exact ⟨((Ideal.quotEquivOfEq hS.symm).trans
    (RingHom.quotientKerEquivRange ((Ideal.Quotient.mk I).comp S.subtype))).trans
    ((RingEquiv.subringCongr hr.symm).trans
    ((RingHom.quotientKerEquivRange ((Ideal.Quotient.mk I).comp T.subtype)).symm.trans
    (Ideal.quotEquivOfEq hT')))⟩

end SecondIso

end UndergradKB.AbstractAlgebra
