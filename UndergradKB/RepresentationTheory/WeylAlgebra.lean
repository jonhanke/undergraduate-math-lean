import Mathlib.Algebra.FreeAlgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import UndergradKB.Common.Attr
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.Bilinear
import UndergradKB.RepresentationTheory.Sl2

/-! # Weyl algebra and presentations of enveloping algebras (Etingof et al., §1.7, Examples 1.46-1.47)

Mathlib has no Weyl algebra, so it is introduced as a quotient of the free algebra (`RingQuot`).

* `WeylAlgebra k`: generators `x, y`, relation `y x = x y + 1`; `weylLift` is its universal property.
* `weyl_span`: the monomials `xⁱ yʲ` span; `weyl_linearIndependent` (characteristic zero): they are
  linearly independent, proved through the faithful action on `k[t]` (`x ↦ t`, `y ↦ d/dt`).
* `Sl2Alg k`: generators `h, e, f` with the three `sl₂` relations; `sl2AlgHomEquiv` is the universal
  property and `sl2UEquiv` an algebra isomorphism with `U(L)` for any Lie algebra `L` with an
  `sl₂`-basis (`IsSl2Basis`).
* `HeisAlg k`: generators `x, y, c` with `y x - x y = c`, `c` central; `heisUEquiv` identifies it with
  `U(L)` for a Lie algebra with a Heisenberg basis (`IsHeisBasis`); `weyl_universal_of_heisU` says the
  Weyl algebra is the quotient of `U(L)` by `c = 1` (surjection, universal property).
* Not included: the kernel described as a two-sided ideal, the `q`-Weyl algebra.
-/

namespace UndergradKB.RepresentationTheory

open Polynomial

section Weyl

variable (k : Type*) [CommRing k]

/-- The defining relation `y x = x y + 1` of the Weyl algebra, on the free algebra on `x = ι 0`,
`y = ι 1`. -/
inductive WeylRel : FreeAlgebra k (Fin 2) → FreeAlgebra k (Fin 2) → Prop
  | rel : WeylRel (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0) (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1 + 1)

/-- The Weyl algebra: the free algebra on `x, y` modulo `y x - x y = 1`. -/
@[kb "etingof2011" "§1.7, p. 11"]
abbrev WeylAlgebra : Type _ := RingQuot (WeylRel k)

/-- The generator `x` of the Weyl algebra. -/
def weylX : WeylAlgebra k := RingQuot.mkAlgHom k (WeylRel k) (FreeAlgebra.ι k 0)

/-- The generator `y` of the Weyl algebra. -/
def weylY : WeylAlgebra k := RingQuot.mkAlgHom k (WeylRel k) (FreeAlgebra.ι k 1)

variable {k}

/-- The defining relation holds in the Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem weylY_mul_weylX : weylY k * weylX k = weylX k * weylY k + 1 := by
  have := RingQuot.mkAlgHom_rel k (WeylRel.rel (k := k))
  simpa [weylX, weylY] using this

/-- Universal property: an algebra map out of the Weyl algebra is the same as elements `x, y`
with `y x = x y + 1`. -/
noncomputable def weylLift {A : Type*} [Ring A] [Algebra k A] (x y : A) (h : y * x = x * y + 1) :
    WeylAlgebra k →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k ![x, y], by
    intro a b hab
    cases hab
    simpa using h⟩

theorem weylLift_x {A : Type*} [Ring A] [Algebra k A] (x y : A) (h : y * x = x * y + 1) :
    weylLift x y h (weylX k) = x := by
  simp [weylLift, weylX]

theorem weylLift_y {A : Type*} [Ring A] [Algebra k A] (x y : A) (h : y * x = x * y + 1) :
    weylLift x y h (weylY k) = y := by
  simp [weylLift, weylY]

/-- Commutation rule `y xⁿ = xⁿ y + n xⁿ⁻¹`. -/
theorem y_mul_x_pow {A : Type*} [Ring A] (x y : A) (h : y * x = x * y + 1) (n : ℕ) :
    y * x ^ n = x ^ n * y + n • x ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp [h]
    · have : y * x ^ (n + 1 + 1) = (y * x ^ (n + 1)) * x := by rw [pow_succ _ (n + 1), mul_assoc]
      rw [this, ih]
      simp only [Nat.add_sub_cancel, add_mul, smul_mul_assoc, mul_assoc, h, mul_add, mul_one]
      rw [← mul_assoc]
      simp only [← pow_succ, add_smul, one_smul]
      abel

/-- The span of the monomials `xⁱ yʲ`. -/
def monSpan {A : Type*} [Ring A] [Algebra k A] (x y : A) : Submodule k A :=
  Submodule.span k (Set.range fun p : ℕ × ℕ => x ^ p.1 * y ^ p.2)

theorem x_mul_mem_monSpan {A : Type*} [Ring A] [Algebra k A] (x y : A) {s : A}
    (hs : s ∈ monSpan (k := k) x y) : x * s ∈ monSpan (k := k) x y := by
  have : monSpan (k := k) x y ≤ (monSpan (k := k) x y).comap (LinearMap.mulLeft k x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    show x * (x ^ i * y ^ j) ∈ monSpan (k := k) x y
    rw [← mul_assoc, ← pow_succ']
    exact Submodule.subset_span ⟨(i + 1, j), rfl⟩
  exact this hs

theorem y_mul_mem_monSpan {A : Type*} [Ring A] [Algebra k A] (x y : A) (h : y * x = x * y + 1)
    {s : A} (hs : s ∈ monSpan (k := k) x y) : y * s ∈ monSpan (k := k) x y := by
  have : monSpan (k := k) x y ≤ (monSpan (k := k) x y).comap (LinearMap.mulLeft k y) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    show y * (x ^ i * y ^ j) ∈ monSpan (k := k) x y
    rw [← mul_assoc, y_mul_x_pow x y h, add_mul, mul_assoc, ← pow_succ', smul_mul_assoc]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨(i, j + 1), rfl⟩) ?_
    rw [← Nat.cast_smul_eq_nsmul k]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i - 1, j), rfl⟩)
  exact this hs

theorem one_mem_monSpan {A : Type*} [Ring A] [Algebra k A] (x y : A) :
    (1 : A) ∈ monSpan (k := k) x y := by
  have := Submodule.subset_span (R := k) (s := Set.range fun p : ℕ × ℕ => x ^ p.1 * y ^ p.2)
    ⟨(0, 0), rfl⟩
  simpa [monSpan] using this

/-- The monomials `xⁱ yʲ` span the Weyl algebra. -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem weyl_span :
    Submodule.span k (Set.range fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2) = ⊤ := by
  have h := weylY_mul_weylX (k := k)
  have key : ∀ a : FreeAlgebra k (Fin 2), ∀ s ∈ monSpan (k := k) (weylX k) (weylY k),
      RingQuot.mkAlgHom k (WeylRel k) a * s ∈ monSpan (k := k) (weylX k) (weylY k) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro s hs
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact Submodule.smul_mem _ _ hs
    | grade1 i =>
      intro s hs
      fin_cases i
      · exact x_mul_mem_monSpan _ _ hs
      · exact y_mul_mem_monSpan _ _ h hs
    | mul a b ha hb =>
      intro s hs
      rw [map_mul, mul_assoc]
      exact ha _ (hb s hs)
    | add a b ha hb =>
      intro s hs
      rw [map_add, add_mul]
      exact Submodule.add_mem _ (ha s hs) (hb s hs)
  rw [eq_top_iff]
  rintro z -
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (WeylRel k) z
  simpa [monSpan] using key a 1 (one_mem_monSpan _ _)

end Weyl

section WeylBasis

variable (k : Type*) [Field k]

/-- The faithful representation of the Weyl algebra on `k[t]`: `x` acts by multiplication by `t`,
`y` by `d/dt`. -/
noncomputable def weylRep : WeylAlgebra k →ₐ[k] Module.End k k[X] :=
  weylLift (LinearMap.mulLeft k (X : k[X])) (derivative (R := k)) (by
    refine LinearMap.ext fun p => ?_
    show derivative ((X : k[X]) * p) = (X : k[X]) * derivative p + p
    simp [derivative_mul, add_comm])

variable {k}

theorem weylRep_x : weylRep k (weylX k) = LinearMap.mulLeft k (X : k[X]) := by
  simp [weylRep, weylLift_x]

theorem weylRep_y : weylRep k (weylY k) = derivative (R := k) := by
  simp [weylRep, weylLift_y]

theorem mulLeft_pow_apply (i : ℕ) (p : k[X]) :
    ((LinearMap.mulLeft k (X : k[X])) ^ i) p = X ^ i * p := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    show X * ((LinearMap.mulLeft k (X : k[X]) ^ i) p) = _
    rw [ih, pow_succ', mul_assoc]

theorem weylRep_monomial (i j m : ℕ) :
    weylRep k (weylX k ^ i * weylY k ^ j) (X ^ m) = (Nat.descFactorial m j : k) • X ^ (i + (m - j)) := by
  rw [map_mul, map_pow (weylRep k), map_pow (weylRep k), weylRep_x, weylRep_y]
  show (LinearMap.mulLeft k (X : k[X]) ^ i) (((derivative (R := k)) ^ j) (X ^ m)) = _
  rw [pow_apply_eq_iterate (derivative (R := k)) j, iterate_derivative_X_pow_eq_smul, map_smul, mulLeft_pow_apply,
    ← pow_add]

variable [CharZero k]

/-- The monomials `xⁱ yʲ` are linearly independent in the Weyl algebra over a field of
characteristic zero (via the faithful representation on `k[t]`). -/
@[kb "etingof2011" "§1.7, p. 11"]
theorem weyl_linearIndependent :
    LinearIndependent k (fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2) := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  have hex : ∃ j, ∃ i, l (i, j) ≠ 0 := by
    obtain ⟨p, hp⟩ : ∃ p, l p ≠ 0 := by
      by_contra hcon
      exact hne (Finsupp.ext fun p => by_contra fun hp => hcon ⟨p, hp⟩)
    exact ⟨p.2, p.1, hp⟩
  classical
  let j0 := Nat.find hex
  obtain ⟨i0, hi0⟩ := Nat.find_spec hex
  have hmin : ∀ p, l p ≠ 0 → j0 ≤ p.2 := fun p hp => Nat.find_min' hex ⟨p.1, hp⟩
  have h1 := congrArg (fun a => lcoeff k i0 (weylRep k a (X ^ j0))) hl
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_zero, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, weylRep_monomial, lcoeff_apply, coeff_smul,
    coeff_X_pow, LinearMap.zero_apply, smul_eq_mul] at h1
  rw [Finset.sum_eq_single (i0, j0)] at h1
  · simp at h1
    exact hi0 h1
  · intro p hp hpne
    have hle := hmin p (Finsupp.mem_support_iff.1 hp)
    rcases hle.eq_or_lt with heq | hlt
    · have : p.1 ≠ i0 := fun h => hpne (Prod.ext h heq.symm)
      simp [← heq, Ne.symm this]
    · have : Nat.descFactorial j0 p.2 = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hlt
      simp [this]
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 hi0) h

/-- The basis `xⁱ yʲ` (`i, j ≥ 0`) of the Weyl algebra in characteristic zero. -/
@[kb "etingof2011" "§1.7, p. 11"]
noncomputable def weylBasis : Module.Basis (ℕ × ℕ) k (WeylAlgebra k) :=
  Module.Basis.mk weyl_linearIndependent weyl_span.ge

theorem weylBasis_apply (p : ℕ × ℕ) : weylBasis (k := k) p = weylX k ^ p.1 * weylY k ^ p.2 := by
  simp [weylBasis]

end WeylBasis


open Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section LieBasis

variable {k : Type*} [CommRing k] {L A : Type*} [LieRing L] [LieAlgebra k L] [Ring A] [Algebra k A]
  {ι : Type*}

/-- A linear map from a Lie algebra with a basis to an associative algebra, which respects the
bracket on pairs of basis vectors, is a Lie algebra morphism (the target carries the commutator
bracket). -/
def lieHomOfBasis (b : Basis ι k L) (φ : L →ₗ[k] A)
    (h : ∀ i j, φ ⁅b i, b j⁆ = φ (b i) * φ (b j) - φ (b j) * φ (b i)) : L →ₗ⁅k⁆ A :=
  { φ with
    map_lie' := by
      intro x y
      have key : (LinearMap.mk₂ k (fun x y : L => φ ⁅x, y⁆) (by intros; simp) (by intros; simp)
            (by intros; simp) (by intros; simp)) =
          LinearMap.mk₂ k (fun x y : L => φ x * φ y - φ y * φ x)
            (by intros; simp [add_mul, mul_add]; abel)
            (by intros; simp [smul_sub, smul_mul_assoc, mul_smul_comm])
            (by intros; simp [add_mul, mul_add]; abel)
            (by intros; simp [smul_sub, smul_mul_assoc, mul_smul_comm]) :=
        LinearMap.ext_basis b b h
      have := congr($key x y)
      simpa [Ring.lie_def] using this }

@[simp] lemma lieHomOfBasis_apply (b : Basis ι k L) (φ : L →ₗ[k] A) (h) (x : L) :
    lieHomOfBasis b φ h x = φ x := rfl

end LieBasis

section Sl2U

variable (k : Type*) [Field k]

/-- The relations of `sl₂` on the free algebra on `h = ι 0`, `e = ι 1`, `f = ι 2`. -/
inductive Sl2Rel : FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop
  | ef : Sl2Rel (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 1)
      (FreeAlgebra.ι k 0)
  | he : Sl2Rel (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1 - FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0)
      ((2 : k) • FreeAlgebra.ι k 1)
  | hf : Sl2Rel (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 0)
      (-((2 : k) • FreeAlgebra.ι k 2))

/-- The algebra with generators `h, e, f` and the defining relations of `sl₂`. -/
abbrev Sl2Alg : Type _ := RingQuot (Sl2Rel k)

/-- The generator `h`. -/
def sl2AlgH : Sl2Alg k := RingQuot.mkAlgHom k (Sl2Rel k) (FreeAlgebra.ι k 0)
/-- The generator `e`. -/
def sl2AlgE : Sl2Alg k := RingQuot.mkAlgHom k (Sl2Rel k) (FreeAlgebra.ι k 1)
/-- The generator `f`. -/
def sl2AlgF : Sl2Alg k := RingQuot.mkAlgHom k (Sl2Rel k) (FreeAlgebra.ι k 2)

theorem isSl2Rel_gens : Sl2.IsSl2Rel k (sl2AlgH k) (sl2AlgE k) (sl2AlgF k) where
  ef := by
    simpa [sl2AlgH, sl2AlgE, sl2AlgF] using RingQuot.mkAlgHom_rel k (Sl2Rel.ef (k := k))
  he := by
    simpa [sl2AlgH, sl2AlgE, sl2AlgF] using RingQuot.mkAlgHom_rel k (Sl2Rel.he (k := k))
  hf := by
    simpa [sl2AlgH, sl2AlgE, sl2AlgF] using RingQuot.mkAlgHom_rel k (Sl2Rel.hf (k := k))

variable {k}

/-- Universal property of the presented algebra: a triple satisfying the `sl₂` relations gives an
algebra map. -/
noncomputable def sl2AlgLift {A : Type*} [Ring A] [Algebra k A] (h e f : A)
    (r : Sl2.IsSl2Rel k h e f) : Sl2Alg k →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k ![h, e, f], by
    intro a b hab
    cases hab
    · simpa using r.ef
    · simpa using r.he
    · simpa using r.hf⟩

theorem sl2AlgLift_H {A : Type*} [Ring A] [Algebra k A] (h e f : A) (r : Sl2.IsSl2Rel k h e f) :
    sl2AlgLift h e f r (sl2AlgH k) = h := by simp [sl2AlgLift, sl2AlgH]

theorem sl2AlgLift_E {A : Type*} [Ring A] [Algebra k A] (h e f : A) (r : Sl2.IsSl2Rel k h e f) :
    sl2AlgLift h e f r (sl2AlgE k) = e := by simp [sl2AlgLift, sl2AlgE]

theorem sl2AlgLift_F {A : Type*} [Ring A] [Algebra k A] (h e f : A) (r : Sl2.IsSl2Rel k h e f) :
    sl2AlgLift h e f r (sl2AlgF k) = f := by simp [sl2AlgLift, sl2AlgF]

/-- Two algebra maps out of the presented algebra agree when they agree on `h, e, f`. -/
theorem sl2Alg_hom_ext {A : Type*} [Ring A] [Algebra k A] {g₁ g₂ : Sl2Alg k →ₐ[k] A}
    (hh : g₁ (sl2AlgH k) = g₂ (sl2AlgH k)) (he : g₁ (sl2AlgE k) = g₂ (sl2AlgE k))
    (hf : g₁ (sl2AlgF k) = g₂ (sl2AlgF k)) : g₁ = g₂ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  fin_cases i
  · exact hh
  · exact he
  · exact hf

variable (k) in
/-- Algebra maps out of the presented algebra correspond to triples satisfying the `sl₂`
relations. -/
@[kb "etingof2011" "Example 1.46, p. 16"]
noncomputable def sl2AlgHomEquiv (A : Type*) [Ring A] [Algebra k A] :
    (Sl2Alg k →ₐ[k] A) ≃ {t : A × A × A // Sl2.IsSl2Rel k t.1 t.2.1 t.2.2} where
  toFun g := ⟨(g (sl2AlgH k), g (sl2AlgE k), g (sl2AlgF k)), by
    have := isSl2Rel_gens k
    constructor
    · simpa [map_sub, map_mul] using congrArg g this.ef
    · simpa [map_sub, map_mul] using congrArg g this.he
    · simpa [map_sub, map_mul] using congrArg g this.hf⟩
  invFun t := sl2AlgLift t.1.1 t.1.2.1 t.1.2.2 t.2
  left_inv g := sl2Alg_hom_ext (by simp [sl2AlgLift_H]) (by simp [sl2AlgLift_E])
    (by simp [sl2AlgLift_F])
  right_inv t := by
    apply Subtype.ext
    simp [sl2AlgLift_H, sl2AlgLift_E, sl2AlgLift_F]

end Sl2U

section Sl2Iso

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]

/-- A basis `h, e, f` of a Lie algebra with the bracket relations of `sl₂`. -/
structure IsSl2Basis (b : Basis (Fin 3) k L) : Prop where
  ef : ⁅b 1, b 2⁆ = b 0
  he : ⁅b 0, b 1⁆ = (2 : k) • b 1
  hf : ⁅b 0, b 2⁆ = -((2 : k) • b 2)

variable {b : Basis (Fin 3) k L}

/-- A triple satisfying the `sl₂` relations in an associative algebra defines a Lie algebra
morphism from a Lie algebra with an `sl₂`-basis. -/
noncomputable def sl2LieHom (hb : IsSl2Basis b) {A : Type*} [Ring A] [Algebra k A] (h e f : A)
    (r : Sl2.IsSl2Rel k h e f) : L →ₗ⁅k⁆ A :=
  lieHomOfBasis b (b.constr k ![h, e, f]) (by
    have he2 : e * h - h * e = -((2 : k) • e) := by rw [← r.he]; abel
    have hf2 : f * h - h * f = (2 : k) • f := by rw [← neg_sub, r.hf, neg_neg]
    have ef2 : f * e - e * f = -h := by rw [← r.ef]; abel
    have hb1 : ⁅b 1, b 0⁆ = -((2 : k) • b 1) := by rw [← lie_skew, hb.he]
    have hb2 : ⁅b 2, b 0⁆ = (2 : k) • b 2 := by rw [← lie_skew, hb.hf, neg_neg]
    have hb3 : ⁅b 2, b 1⁆ = -b 0 := by rw [← lie_skew, hb.ef]
    have c0 : b.constr k ![h, e, f] (b 0) = h := b.constr_basis k _ 0
    have c1 : b.constr k ![h, e, f] (b 1) = e := b.constr_basis k _ 1
    have c2 : b.constr k ![h, e, f] (b 2) = f := b.constr_basis k _ 2
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, lie_self, map_zero,
        sub_self, hb.ef, hb.he, hb.hf, hb1, hb2, hb3, map_smul, map_neg, c0, c1, c2, r.ef, r.he,
        r.hf, he2, hf2, ef2])

theorem sl2LieHom_basis (hb : IsSl2Basis b) {A : Type*} [Ring A] [Algebra k A] (h e f : A)
    (r : Sl2.IsSl2Rel k h e f) (i : Fin 3) : sl2LieHom hb h e f r (b i) = ![h, e, f] i := by
  simp [sl2LieHom]

/-- The algebra map from the presented algebra to `U(L)`. -/
noncomputable def sl2ToU (hb : IsSl2Basis b) :
    Sl2Alg k →ₐ[k] UniversalEnvelopingAlgebra k L :=
  sl2AlgLift (UniversalEnvelopingAlgebra.ι k (b 0)) (UniversalEnvelopingAlgebra.ι k (b 1))
    (UniversalEnvelopingAlgebra.ι k (b 2)) (by
      constructor
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.ef]
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.he, map_smul]
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.hf, map_neg, map_smul])

theorem sl2ToU_H (hb : IsSl2Basis b) :
    sl2ToU hb (sl2AlgH k) = UniversalEnvelopingAlgebra.ι k (b 0) := sl2AlgLift_H _ _ _ _

theorem sl2ToU_E (hb : IsSl2Basis b) :
    sl2ToU hb (sl2AlgE k) = UniversalEnvelopingAlgebra.ι k (b 1) := sl2AlgLift_E _ _ _ _

theorem sl2ToU_F (hb : IsSl2Basis b) :
    sl2ToU hb (sl2AlgF k) = UniversalEnvelopingAlgebra.ι k (b 2) := sl2AlgLift_F _ _ _ _

/-- The algebra map from `U(L)` to the presented algebra, from the universal property. -/
noncomputable def sl2OfU (hb : IsSl2Basis b) :
    UniversalEnvelopingAlgebra k L →ₐ[k] Sl2Alg k :=
  UniversalEnvelopingAlgebra.lift k (sl2LieHom hb (sl2AlgH k) (sl2AlgE k) (sl2AlgF k) (isSl2Rel_gens k))

theorem sl2OfU_ι (hb : IsSl2Basis b) (i : Fin 3) :
    sl2OfU hb (UniversalEnvelopingAlgebra.ι k (b i)) = ![sl2AlgH k, sl2AlgE k, sl2AlgF k] i := by
  rw [sl2OfU, UniversalEnvelopingAlgebra.lift_ι_apply, sl2LieHom_basis]

/-- `U(sl₂)` is isomorphic to the algebra with generators `h, e, f` and the three defining
relations (for any Lie algebra with a basis `h, e, f` with the `sl₂` brackets). -/
@[kb "etingof2011" "Example 1.46, p. 16"]
noncomputable def sl2UEquiv (hb : IsSl2Basis b) :
    Sl2Alg k ≃ₐ[k] UniversalEnvelopingAlgebra k L :=
  AlgEquiv.ofAlgHom (sl2ToU hb) (sl2OfU hb)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      refine LieHom.ext fun x => ?_
      have hlin : (((sl2ToU hb).comp (sl2OfU hb)).toLinearMap ∘ₗ
            (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap : L →ₗ[k] _) =
          (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap := by
        refine b.ext fun i => ?_
        fin_cases i
        · show sl2ToU hb (sl2OfU hb (UniversalEnvelopingAlgebra.ι k (b 0))) = _
          rw [sl2OfU_ι]; exact sl2ToU_H hb
        · show sl2ToU hb (sl2OfU hb (UniversalEnvelopingAlgebra.ι k (b 1))) = _
          rw [sl2OfU_ι]; exact sl2ToU_E hb
        · show sl2ToU hb (sl2OfU hb (UniversalEnvelopingAlgebra.ι k (b 2))) = _
          rw [sl2OfU_ι]; exact sl2ToU_F hb
      exact congr($hlin x))
    (sl2Alg_hom_ext
      (by
        show sl2OfU hb (sl2ToU hb (sl2AlgH k)) = sl2AlgH k
        rw [sl2ToU_H]; exact sl2OfU_ι hb 0)
      (by
        show sl2OfU hb (sl2ToU hb (sl2AlgE k)) = sl2AlgE k
        rw [sl2ToU_E]; exact sl2OfU_ι hb 1)
      (by
        show sl2OfU hb (sl2ToU hb (sl2AlgF k)) = sl2AlgF k
        rw [sl2ToU_F]; exact sl2OfU_ι hb 2))

end Sl2Iso

section HeisU

variable (k : Type*) [CommRing k]

/-- The relations of the Heisenberg Lie algebra on the free algebra on `x = ι 0`, `y = ι 1`,
`c = ι 2`: `y x - x y = c` and `c` central. -/
inductive HeisRel : FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop
  | yx : HeisRel (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0 - FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1)
      (FreeAlgebra.ι k 2)
  | xc : HeisRel (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 0) 0
  | yc : HeisRel (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 1) 0

/-- The algebra with generators `x, y, c` and the relations of the Heisenberg Lie algebra. -/
abbrev HeisAlg : Type _ := RingQuot (HeisRel k)

/-- The generator `x`. -/
def heisAlgX : HeisAlg k := RingQuot.mkAlgHom k (HeisRel k) (FreeAlgebra.ι k 0)
/-- The generator `y`. -/
def heisAlgY : HeisAlg k := RingQuot.mkAlgHom k (HeisRel k) (FreeAlgebra.ι k 1)
/-- The generator `c`. -/
def heisAlgC : HeisAlg k := RingQuot.mkAlgHom k (HeisRel k) (FreeAlgebra.ι k 2)

/-- The Heisenberg relations for three elements of an associative algebra. -/
structure IsHeisRel {A : Type*} [Ring A] (x y c : A) : Prop where
  yx : y * x - x * y = c
  xc : x * c - c * x = 0
  yc : y * c - c * y = 0

theorem isHeisRel_gens : IsHeisRel (heisAlgX k) (heisAlgY k) (heisAlgC k) where
  yx := by simpa [heisAlgX, heisAlgY, heisAlgC] using RingQuot.mkAlgHom_rel k (HeisRel.yx (k := k))
  xc := by simpa [heisAlgX, heisAlgY, heisAlgC] using RingQuot.mkAlgHom_rel k (HeisRel.xc (k := k))
  yc := by simpa [heisAlgX, heisAlgY, heisAlgC] using RingQuot.mkAlgHom_rel k (HeisRel.yc (k := k))

variable {k}

/-- Universal property of the presented algebra. -/
noncomputable def heisAlgLift {A : Type*} [Ring A] [Algebra k A] (x y c : A)
    (r : IsHeisRel x y c) : HeisAlg k →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k ![x, y, c], by
    intro a b hab
    cases hab
    · simpa using r.yx
    · simpa using r.xc
    · simpa using r.yc⟩

theorem heisAlgLift_X {A : Type*} [Ring A] [Algebra k A] (x y c : A) (r : IsHeisRel x y c) :
    heisAlgLift x y c r (heisAlgX k) = x := by simp [heisAlgLift, heisAlgX]

theorem heisAlgLift_Y {A : Type*} [Ring A] [Algebra k A] (x y c : A) (r : IsHeisRel x y c) :
    heisAlgLift x y c r (heisAlgY k) = y := by simp [heisAlgLift, heisAlgY]

theorem heisAlgLift_C {A : Type*} [Ring A] [Algebra k A] (x y c : A) (r : IsHeisRel x y c) :
    heisAlgLift x y c r (heisAlgC k) = c := by simp [heisAlgLift, heisAlgC]

theorem heisAlg_hom_ext {A : Type*} [Ring A] [Algebra k A] {g₁ g₂ : HeisAlg k →ₐ[k] A}
    (hx : g₁ (heisAlgX k) = g₂ (heisAlgX k)) (hy : g₁ (heisAlgY k) = g₂ (heisAlgY k))
    (hc : g₁ (heisAlgC k) = g₂ (heisAlgC k)) : g₁ = g₂ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hc

variable {L : Type*} [LieRing L] [LieAlgebra k L]

/-- A basis `x, y, c` of a Lie algebra with the Heisenberg brackets `[y, x] = c`, `c` central. -/
structure IsHeisBasis (b : Basis (Fin 3) k L) : Prop where
  yx : ⁅b 1, b 0⁆ = b 2
  xc : ⁅b 0, b 2⁆ = 0
  yc : ⁅b 1, b 2⁆ = 0

variable {b : Basis (Fin 3) k L}

/-- A triple satisfying the Heisenberg relations in an associative algebra defines a Lie algebra
morphism from a Lie algebra with a Heisenberg basis. -/
noncomputable def heisLieHom (hb : IsHeisBasis b) {A : Type*} [Ring A] [Algebra k A] (x y c : A)
    (r : IsHeisRel x y c) : L →ₗ⁅k⁆ A :=
  lieHomOfBasis b (b.constr k ![x, y, c]) (by
    have xy2 : x * y - y * x = -c := by rw [← r.yx]; abel
    have cx2 : c * x - x * c = 0 := by rw [← neg_sub, r.xc, neg_zero]
    have cy2 : c * y - y * c = 0 := by rw [← neg_sub, r.yc, neg_zero]
    have hb1 : ⁅b 0, b 1⁆ = -b 2 := by rw [← lie_skew, hb.yx]
    have hb2 : ⁅b 2, b 0⁆ = 0 := by rw [← lie_skew, hb.xc, neg_zero]
    have hb3 : ⁅b 2, b 1⁆ = 0 := by rw [← lie_skew, hb.yc, neg_zero]
    have c0 : b.constr k ![x, y, c] (b 0) = x := b.constr_basis k _ 0
    have c1 : b.constr k ![x, y, c] (b 1) = y := b.constr_basis k _ 1
    have c2 : b.constr k ![x, y, c] (b 2) = c := b.constr_basis k _ 2
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, lie_self, map_zero,
        sub_self, hb.yx, hb.xc, hb.yc, hb1, hb2, hb3, map_neg, c0, c1, c2, r.yx, r.xc, r.yc,
        xy2, cx2, cy2])

theorem heisLieHom_basis (hb : IsHeisBasis b) {A : Type*} [Ring A] [Algebra k A] (x y c : A)
    (r : IsHeisRel x y c) (i : Fin 3) : heisLieHom hb x y c r (b i) = ![x, y, c] i := by
  simp [heisLieHom]

/-- The algebra map from the presented algebra to `U(L)`. -/
noncomputable def heisToU (hb : IsHeisBasis b) :
    HeisAlg k →ₐ[k] UniversalEnvelopingAlgebra k L :=
  heisAlgLift (UniversalEnvelopingAlgebra.ι k (b 0)) (UniversalEnvelopingAlgebra.ι k (b 1))
    (UniversalEnvelopingAlgebra.ι k (b 2)) (by
      constructor
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.yx]
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.xc, map_zero]
      · rw [← Ring.lie_def, ← LieHom.map_lie, hb.yc, map_zero])

/-- The algebra map from `U(L)` to the presented algebra. -/
noncomputable def heisOfU (hb : IsHeisBasis b) :
    UniversalEnvelopingAlgebra k L →ₐ[k] HeisAlg k :=
  UniversalEnvelopingAlgebra.lift k
    (heisLieHom hb (heisAlgX k) (heisAlgY k) (heisAlgC k) (isHeisRel_gens k))

theorem heisOfU_ι (hb : IsHeisBasis b) (i : Fin 3) :
    heisOfU hb (UniversalEnvelopingAlgebra.ι k (b i)) = ![heisAlgX k, heisAlgY k, heisAlgC k] i := by
  rw [heisOfU, UniversalEnvelopingAlgebra.lift_ι_apply, heisLieHom_basis]

theorem heisToU_X (hb : IsHeisBasis b) :
    heisToU hb (heisAlgX k) = UniversalEnvelopingAlgebra.ι k (b 0) := heisAlgLift_X _ _ _ _

theorem heisToU_Y (hb : IsHeisBasis b) :
    heisToU hb (heisAlgY k) = UniversalEnvelopingAlgebra.ι k (b 1) := heisAlgLift_Y _ _ _ _

theorem heisToU_C (hb : IsHeisBasis b) :
    heisToU hb (heisAlgC k) = UniversalEnvelopingAlgebra.ι k (b 2) := heisAlgLift_C _ _ _ _

/-- `U` of the Heisenberg Lie algebra is the algebra generated by `x, y, c` with the relations
`y x - x y = c`, `c` central. -/
@[kb "etingof2011" "Example 1.47, p. 16"]
noncomputable def heisUEquiv (hb : IsHeisBasis b) :
    HeisAlg k ≃ₐ[k] UniversalEnvelopingAlgebra k L :=
  AlgEquiv.ofAlgHom (heisToU hb) (heisOfU hb)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      refine LieHom.ext fun x => ?_
      have hlin : (((heisToU hb).comp (heisOfU hb)).toLinearMap ∘ₗ
            (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap : L →ₗ[k] _) =
          (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap := by
        refine b.ext fun i => ?_
        fin_cases i
        · show heisToU hb (heisOfU hb (UniversalEnvelopingAlgebra.ι k (b 0))) = _
          rw [heisOfU_ι]; exact heisToU_X hb
        · show heisToU hb (heisOfU hb (UniversalEnvelopingAlgebra.ι k (b 1))) = _
          rw [heisOfU_ι]; exact heisToU_Y hb
        · show heisToU hb (heisOfU hb (UniversalEnvelopingAlgebra.ι k (b 2))) = _
          rw [heisOfU_ι]; exact heisToU_C hb
      exact congr($hlin x))
    (heisAlg_hom_ext
      (by
        show heisOfU hb (heisToU hb (heisAlgX k)) = heisAlgX k
        rw [heisToU_X]; exact heisOfU_ι hb 0)
      (by
        show heisOfU hb (heisToU hb (heisAlgY k)) = heisAlgY k
        rw [heisToU_Y]; exact heisOfU_ι hb 1)
      (by
        show heisOfU hb (heisToU hb (heisAlgC k)) = heisAlgC k
        rw [heisToU_C]; exact heisOfU_ι hb 2))

end HeisU

section WeylQuotient

variable {k : Type*} [CommRing k] {L : Type*} [LieRing L] [LieAlgebra k L] {b : Basis (Fin 3) k L}

theorem isHeisRel_weyl : IsHeisRel (weylX k) (weylY k) (1 : WeylAlgebra k) where
  yx := by rw [weylY_mul_weylX]; abel
  xc := by simp
  yc := by simp

/-- The quotient map `U(Heis) → Weyl algebra` sending `x ↦ x`, `y ↦ y`, `c ↦ 1`. -/
noncomputable def heisUToWeyl (hb : IsHeisBasis b) :
    UniversalEnvelopingAlgebra k L →ₐ[k] WeylAlgebra k :=
  UniversalEnvelopingAlgebra.lift k (heisLieHom hb (weylX k) (weylY k) 1 isHeisRel_weyl)

theorem heisUToWeyl_ι (hb : IsHeisBasis b) (i : Fin 3) :
    heisUToWeyl hb (UniversalEnvelopingAlgebra.ι k (b i)) = ![weylX k, weylY k, 1] i := by
  rw [heisUToWeyl, UniversalEnvelopingAlgebra.lift_ι_apply, heisLieHom_basis]

theorem heisUToWeyl_c (hb : IsHeisBasis b) :
    heisUToWeyl hb (UniversalEnvelopingAlgebra.ι k (b 2)) = 1 := heisUToWeyl_ι hb 2

/-- The map `U(Heis) → Weyl algebra` is surjective. -/
theorem heisUToWeyl_surjective (hb : IsHeisBasis b) : Function.Surjective (heisUToWeyl hb) := by
  have hx : weylX k ∈ (heisUToWeyl hb).range := ⟨UniversalEnvelopingAlgebra.ι k (b 0), heisUToWeyl_ι hb 0⟩
  have hy : weylY k ∈ (heisUToWeyl hb).range := ⟨UniversalEnvelopingAlgebra.ι k (b 1), heisUToWeyl_ι hb 1⟩
  intro z
  have hz : z ∈ Submodule.span k (Set.range fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2) := by
    rw [weyl_span]; trivial
  have hle : Submodule.span k (Set.range fun p : ℕ × ℕ => weylX k ^ p.1 * weylY k ^ p.2) ≤
      Subalgebra.toSubmodule (heisUToWeyl hb).range := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact (heisUToWeyl hb).range.mul_mem (pow_mem hx i) (pow_mem hy j)
  exact hle hz

/-- The Weyl algebra is the quotient of `U(Heis)` by `c = 1`: the quotient map sends `c` to `1`,
is surjective, and any algebra map out of `U(Heis)` sending `c` to `1` factors uniquely through it. -/
@[kb "etingof2011" "Example 1.47, p. 16"]
theorem weyl_universal_of_heisU (hb : IsHeisBasis b) {A : Type*} [Ring A] [Algebra k A]
    (g : UniversalEnvelopingAlgebra k L →ₐ[k] A)
    (hg : g (UniversalEnvelopingAlgebra.ι k (b 2)) = 1) :
    ∃! g' : WeylAlgebra k →ₐ[k] A, g'.comp (heisUToWeyl hb) = g := by
  have hrel : g (UniversalEnvelopingAlgebra.ι k (b 1)) * g (UniversalEnvelopingAlgebra.ι k (b 0)) =
      g (UniversalEnvelopingAlgebra.ι k (b 0)) * g (UniversalEnvelopingAlgebra.ι k (b 1)) + 1 := by
    have hU : UniversalEnvelopingAlgebra.ι k (b 1) * UniversalEnvelopingAlgebra.ι k (b 0) -
        UniversalEnvelopingAlgebra.ι k (b 0) * UniversalEnvelopingAlgebra.ι k (b 1) =
        UniversalEnvelopingAlgebra.ι k (b 2) := by
      rw [← Ring.lie_def, ← LieHom.map_lie, hb.yx]
    have := congrArg g hU
    rw [map_sub, map_mul, map_mul, hg] at this
    rw [← this]; abel
  have hex : (weylLift _ _ hrel).comp (heisUToWeyl hb) = g := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    have hlin : (((weylLift _ _ hrel).comp (heisUToWeyl hb)).toLinearMap ∘ₗ
          (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap : L →ₗ[k] A) =
        g.toLinearMap ∘ₗ (UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ _).toLinearMap := by
      refine b.ext fun i => ?_
      fin_cases i
      · show weylLift _ _ hrel (heisUToWeyl hb (UniversalEnvelopingAlgebra.ι k (b 0))) = _
        rw [heisUToWeyl_ι]; exact weylLift_x _ _ _
      · show weylLift _ _ hrel (heisUToWeyl hb (UniversalEnvelopingAlgebra.ι k (b 1))) = _
        rw [heisUToWeyl_ι]; exact weylLift_y _ _ _
      · show weylLift _ _ hrel (heisUToWeyl hb (UniversalEnvelopingAlgebra.ι k (b 2))) = _
        rw [heisUToWeyl_c, map_one]; exact hg.symm
    exact congr($hlin x)
  refine ⟨weylLift _ _ hrel, hex, ?_⟩
  intro g'' hg''
  apply AlgHom.ext
  intro z
  obtain ⟨u, rfl⟩ := heisUToWeyl_surjective hb z
  have h1 := congrArg (fun f => f u) (hg''.trans hex.symm)
  exact h1

end WeylQuotient

end UndergradKB.RepresentationTheory
