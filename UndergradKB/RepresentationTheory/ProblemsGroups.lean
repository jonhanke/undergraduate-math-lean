import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.SpechtRational

/-! # Problems on groups and lattices (Etingof et al.: Problems 5.1, 4.31, 4.39, 5.40(a))

* Problem 5.1: `trdeg_fractionRing_mvPolynomial`, `mvPolynomial_embedding_le` (an injective `k`-algebra map
  `k[x_1..x_n] → k(y_1..y_m)` forces `n ≤ m`), `fractionRing_mvPolynomial_equiv_card_eq` (isomorphic rational
  function fields have equally many variables).  The proof goes through transcendence degree rather than the
  dimension-growth argument of the book.
* Problem 4.31: `indStages`, induction in stages as an equivalence of representations
  `Ind_H^G Ind_K^H ρ ≃ Ind_K^G ρ` for monoid maps `K → H → G` (Mathlib's coinduction, which for
  subgroup inclusions is the book's `Ind`).
* Problem 4.39: `isRealType_of_rational_basis` (a representation of a finite group over `ℂ` with a rational
  basis is of real type) and `sum_dim_irreps_perm`, the sum of the dimensions of the irreducible complex
  representations of `S_n` is the number of `g` with `g² = 1`.
* Problem 5.40 (a): `e8Simple_isBasis`.  Parts (b)-(d) are not formalized.
-/

open Cardinal

namespace UndergradKB.RepresentationTheory

universe u

/-- The rational function field in `m` variables has transcendence degree `m`. -/
theorem trdeg_fractionRing_mvPolynomial (k : Type u) [Field k] (m : ℕ) :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin m) k)) = m := by
  have h1 := trdeg_add_eq (A := FractionRing (MvPolynomial (Fin m) k)) k (MvPolynomial (Fin m) k)
  have h2 : Algebra.trdeg (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) = 0 := by
    have : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin m) k)) (FractionRing (MvPolynomial (Fin m) k)) := inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k)) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := MvPolynomial (Fin m) k) (K := FractionRing (MvPolynomial (Fin m) k))).mpr this
    exact trdeg_eq_zero
  rw [h2, add_zero, MvPolynomial.trdeg_of_isDomain] at h1
  simpa using h1.symm

/-- Problem 5.1, first part. -/
@[kb "etingof2011" "Problem 5.1, p. 78"]
theorem mvPolynomial_embedding_le (k : Type u) [Field k] {n m : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] FractionRing (MvPolynomial (Fin m) k))
    (hf : Function.Injective f) : n ≤ m := by
  have h := trdeg_le_of_injective f hf
  rw [trdeg_fractionRing_mvPolynomial, MvPolynomial.trdeg_of_isDomain] at h
  simpa using h

/-- Problem 5.1, second part: isomorphic rational function fields have the same number of variables. -/
@[kb "etingof2011" "Problem 5.1, p. 78"]
theorem fractionRing_mvPolynomial_equiv_card_eq (k : Type u) [Field k] {n m : ℕ}
    (e : FractionRing (MvPolynomial (Fin n) k) ≃ₐ[k] FractionRing (MvPolynomial (Fin m) k)) :
    m = n := by
  have h := e.trdeg_eq
  rw [trdeg_fractionRing_mvPolynomial, trdeg_fractionRing_mvPolynomial] at h
  exact_mod_cast h.symm

section InductionInStages

open Representation

variable {k : Type u} {K H G : Type*} [Semiring k] [Monoid K] [Monoid H] [Monoid G]
  {V : Type*} [AddCommMonoid V] [Module k V]

lemma coind_apply_val (φ : K →* H) (ρ : Representation k K V) (h x : H) (f : coindV φ ρ) :
    (coind φ ρ h f).1 x = f.1 (x * h) := rfl

/-- The linear isomorphism `Ind_H^G Ind_K^H V ≃ Ind_K^G V`, evaluating the inner function at `1`. -/
def indStagesLinearEquiv (φ : K →* H) (ψ : H →* G) (ρ : Representation k K V) :
    coindV ψ (coind φ ρ) ≃ₗ[k] coindV (ψ.comp φ) ρ where
  toFun F := ⟨fun g => (F.1 g).1 1, fun x g => by
    have h1 := F.2 (φ x) g
    have h2 := congrArg (fun f : coindV φ ρ => f.1 1) h1
    simp only [coind_apply_val, one_mul] at h2
    simpa using h2.trans (by simpa using (F.1 g).2 x 1)⟩
  map_add' F F' := rfl
  map_smul' c F := rfl
  invFun f := ⟨fun g => ⟨fun h => f.1 (ψ h * g), fun x h => by
    simpa [mul_assoc] using f.2 x (ψ h * g)⟩, fun h g => by
    apply Subtype.ext
    funext h'
    show f.1 (ψ h' * (ψ h * g)) = f.1 (ψ (h' * h) * g)
    rw [map_mul, mul_assoc]⟩
  left_inv F := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext h
    have h1 := F.2 h g
    have h2 := congrArg (fun f : coindV φ ρ => f.1 1) h1
    simp only [coind_apply_val, one_mul] at h2
    exact h2
  right_inv f := by
    apply Subtype.ext
    funext g
    simp

/-- **Problem 4.31**, induction in stages: for monoid maps `K → H → G` and a representation `ρ` of `K`,
`Ind_H^G (Ind_K^H ρ) ≅ Ind_K^G ρ` as representations of `G`.  When `K ≤ H ≤ G` are subgroups, take `φ`, `ψ` the
inclusions. -/
@[kb "etingof2011" "Problem 4.31, p. 55"]
def indStages (φ : K →* H) (ψ : H →* G) (ρ : Representation k K V) :
    (coind ψ (coind φ ρ)).Equiv (coind (ψ.comp φ) ρ) :=
  Representation.Equiv.mk (indStagesLinearEquiv φ ψ ρ) fun g => by
    ext F
    rfl

end InductionInStages

section RealType

open Representation
open scoped Matrix

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- A representation of a finite group over `ℂ` that has a basis in which all matrices are rational is of
real type: averaging the standard dot product over the group gives an invariant symmetric form, which is
positive definite over `ℚ` and hence nondegenerate over `ℂ`. -/
theorem isRealType_of_rational_basis (ρ : Representation ℂ G V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (M : G → Matrix ι ι ℚ)
    (hM : ∀ g, LinearMap.toMatrix b b (ρ g) = (M g).map (algebraMap ℚ ℂ)) : IsRealType ρ := by
  set Mc : G → Matrix ι ι ℂ := fun g => LinearMap.toMatrix b b (ρ g) with hMc
  have hmul : ∀ g h, Mc (g * h) = Mc g * Mc h := fun g h => by
    simp only [hMc, map_mul, LinearMap.toMatrix_mul]
  have hone : Mc 1 = 1 := by simp [hMc]
  set Q : Matrix ι ι ℚ := ∑ g, (M g)ᵀ * M g with hQ
  set Qc : Matrix ι ι ℂ := ∑ g, (Mc g)ᵀ * Mc g with hQc
  have hQmap : Qc = Q.map (algebraMap ℚ ℂ) := by
    have h1 : ∀ g, (Mc g)ᵀ * Mc g = ((M g)ᵀ * M g).map (algebraMap ℚ ℂ) := fun g => by
      rw [show Mc g = (M g).map (algebraMap ℚ ℂ) from hM g, Matrix.map_mul, Matrix.transpose_map]
    rw [hQc, Finset.sum_congr rfl fun g _ => h1 g]
    exact (map_sum (algebraMap ℚ ℂ).mapMatrix (fun g => (M g)ᵀ * M g) Finset.univ).symm
  have hdet : Q.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hQx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx
    have hsum : ∑ g, (M g *ᵥ x) ⬝ᵥ (M g *ᵥ x) = 0 := by
      have : x ⬝ᵥ Q *ᵥ x = 0 := by rw [hQx]; simp
      rw [← this, hQ, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Matrix.mulVec_mulVec]
      have := Matrix.dotProduct_mulVec x (M g)ᵀ (M g *ᵥ x)
      rw [Matrix.vecMul_transpose] at this
      exact this.symm
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _ => Finset.sum_nonneg fun i _ => mul_self_nonneg ((M g *ᵥ x) i))).mp hsum 1
      (Finset.mem_univ _)
    have h2 := dotProduct_self_eq_zero.mp h1
    have hM1 : M 1 = 1 := by
      apply Matrix.map_injective (algebraMap ℚ ℂ).injective
      show (M 1).map (algebraMap ℚ ℂ) = (1 : Matrix ι ι ℚ).map (algebraMap ℚ ℂ)
      rw [← hM 1]
      simp
    rwa [hM1, Matrix.one_mulVec] at h2
  have hB : ∀ x y, Matrix.toBilin b Qc x y = b.repr x ⬝ᵥ Qc *ᵥ b.repr y := fun x y => by
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b, LinearMap.BilinForm.toMatrix_toBilin]
  have hsym : Qcᵀ = Qc := by
    simp [hQc, Matrix.transpose_sum, Matrix.transpose_mul]
  have hinvQ : ∀ g, (Mc g)ᵀ * Qc * Mc g = Qc := fun g => by
    conv_rhs => rw [hQc, ← Equiv.sum_comp (Equiv.mulRight g) (fun h => (Mc h)ᵀ * Mc h)]
    rw [hQc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [hmul, Matrix.transpose_mul, Matrix.mul_assoc]
  refine ⟨Matrix.toBilin b Qc, ?_, ?_, ?_⟩
  · rw [Matrix.nondegenerate_toBilin_iff b]
    apply Matrix.nondegenerate_of_det_ne_zero
    rw [hQmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr hdet
  · intro x y
    rw [hB, hB, Matrix.dotProduct_mulVec]
    have h2 : b.repr x ᵥ* Qc = Qc *ᵥ b.repr x := by
      have := Matrix.vecMul_transpose Qc (b.repr x)
      rwa [hsym] at this
    rw [h2, dotProduct_comm]
  · intro g x y
    rw [hB, hB]
    have e : ∀ v, b.repr (ρ g v) = Mc g *ᵥ b.repr v := fun v =>
      (LinearMap.toMatrix_mulVec_repr b b (ρ g) v).symm
    rw [e, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    rw [hinvQ g]

open scoped Classical in
/-- **Problem 4.39**: the sum of the dimensions of the irreducible complex representations of `S_n` equals the
number of `g ∈ S_n` with `g² = 1` (here dimensions are the character values at `1`, as complex numbers). -/
@[kb "etingof2011" "Problem 4.39, p. 59"]
theorem sum_dim_irreps_perm (n : ℕ) :
    ∑ χ : irrChars ℂ (Equiv.Perm (Fin n)), (χ : Equiv.Perm (Fin n) → ℂ) 1 =
      ((Finset.univ.filter fun g : Equiv.Perm (Fin n) => g ^ 2 = 1).card : ℂ) := by
  have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  convert sum_irrChars_one_of_fsIndicator_eq_one (k := ℂ) (G := Equiv.Perm (Fin n)) ?_
  rintro ⟨χ, Y, rfl⟩
  obtain ⟨ι, _, _, b, M, hM⟩ := exists_rational_basis_irrep n Y
  exact fsIndicator_character_eq_one_of_isRealType Y.ρ (isRealType_of_rational_basis Y.ρ b M hM)

end RealType

section E8

/-- The lattice `L` of Problem 5.40: vectors of `ℚ⁸` whose coordinates are either all integers or all
half-odd-integers, with even coordinate sum. -/
def E8Lattice : Set (Fin 8 → ℚ) :=
  {v | ((∀ i, ∃ z : ℤ, v i = z) ∨ (∀ i, ∃ z : ℤ, v i = z + 1 / 2)) ∧ ∃ s : ℤ, ∑ i, v i = 2 * s}

/-- The eight vectors `α_1, …, α_8` of Problem 5.40 (indexed from `0`). -/
def e8Simple : Fin 8 → Fin 8 → ℚ := ![
  ![1, -1, 0, 0, 0, 0, 0, 0], ![0, 1, -1, 0, 0, 0, 0, 0], ![0, 0, 1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 1, -1, 0, 0, 0], ![0, 0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 0, 0, 1, -1, 0],
  ![0, 0, 0, 0, 0, 1, 1, 0], ![-1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2]]

lemma e8_comb_apply (c : Fin 8 → ℤ) :
    (∑ i, c i • e8Simple i) 0 = c 0 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 1 = -c 0 + c 1 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 2 = -c 1 + c 2 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 3 = -c 2 + c 3 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 4 = -c 3 + c 4 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 5 = -c 4 + c 5 + c 6 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 6 = -c 5 + c 6 - c 7 / 2 ∧
    (∑ i, c i • e8Simple i) 7 = -c 7 / 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Pi.add_apply, zsmul_eq_mul, e8Simple]
  simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

lemma e8_comb_mem (c : Fin 8 → ℤ) : (∑ i, c i • e8Simple i) ∈ E8Lattice := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := e8_comb_apply c
  refine ⟨?_, c 6 - 2 * c 7, ?_⟩
  · obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (c 7)
    · left
      have hm' : (c 7 : ℚ) = 2 * m := by exact_mod_cast hm
      intro i
      fin_cases i
      · exact ⟨c 0 - m, by simp only [Fin.zero_eta, h0]; push_cast; linarith⟩
      · exact ⟨-c 0 + c 1 - m, by simp only [Fin.mk_one, h1]; push_cast; linarith⟩
      · exact ⟨-c 1 + c 2 - m, by simp only [Fin.reduceFinMk, h2]; push_cast; linarith⟩
      · exact ⟨-c 2 + c 3 - m, by simp only [Fin.reduceFinMk, h3]; push_cast; linarith⟩
      · exact ⟨-c 3 + c 4 - m, by simp only [Fin.reduceFinMk, h4]; push_cast; linarith⟩
      · exact ⟨-c 4 + c 5 + c 6 - m, by simp only [Fin.reduceFinMk, h5]; push_cast; linarith⟩
      · exact ⟨-c 5 + c 6 - m, by simp only [Fin.reduceFinMk, h6]; push_cast; linarith⟩
      · exact ⟨-m, by simp only [Fin.reduceFinMk, h7]; push_cast; linarith⟩
    · right
      have hm' : (c 7 : ℚ) = 2 * m + 1 := by exact_mod_cast hm
      intro i
      fin_cases i
      · exact ⟨c 0 - m - 1, by simp only [Fin.zero_eta, h0]; push_cast; linarith⟩
      · exact ⟨-c 0 + c 1 - m - 1, by simp only [Fin.mk_one, h1]; push_cast; linarith⟩
      · exact ⟨-c 1 + c 2 - m - 1, by simp only [Fin.reduceFinMk, h2]; push_cast; linarith⟩
      · exact ⟨-c 2 + c 3 - m - 1, by simp only [Fin.reduceFinMk, h3]; push_cast; linarith⟩
      · exact ⟨-c 3 + c 4 - m - 1, by simp only [Fin.reduceFinMk, h4]; push_cast; linarith⟩
      · exact ⟨-c 4 + c 5 + c 6 - m - 1, by simp only [Fin.reduceFinMk, h5]; push_cast; linarith⟩
      · exact ⟨-c 5 + c 6 - m - 1, by simp only [Fin.reduceFinMk, h6]; push_cast; linarith⟩
      · exact ⟨-m - 1, by simp only [Fin.reduceFinMk, h7]; push_cast; linarith⟩
  · rw [Fin.sum_univ_eight, h0, h1, h2, h3, h4, h5, h6, h7]
    push_cast
    ring

lemma e8_comb_injective {c c' : Fin 8 → ℤ}
    (h : ∑ i, c i • e8Simple i = ∑ i, c' i • e8Simple i) : c = c' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := e8_comb_apply c
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := e8_comb_apply c'
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  have e6 := congrFun h 6
  have e7 := congrFun h 7
  rw [a0, b0] at e0
  rw [a1, b1] at e1
  rw [a2, b2] at e2
  rw [a3, b3] at e3
  rw [a4, b4] at e4
  rw [a5, b5] at e5
  rw [a6, b6] at e6
  rw [a7, b7] at e7
  have q0 : c 0 = c' 0 := by
    have : (c 0 : ℚ) = c' 0 := by linarith
    exact_mod_cast this
  have q1 : c 1 = c' 1 := by
    have : (c 1 : ℚ) = c' 1 := by linarith
    exact_mod_cast this
  have q2 : c 2 = c' 2 := by
    have : (c 2 : ℚ) = c' 2 := by linarith
    exact_mod_cast this
  have q3 : c 3 = c' 3 := by
    have : (c 3 : ℚ) = c' 3 := by linarith
    exact_mod_cast this
  have q4 : c 4 = c' 4 := by
    have : (c 4 : ℚ) = c' 4 := by linarith
    exact_mod_cast this
  have q5 : c 5 = c' 5 := by
    have : (c 5 : ℚ) = c' 5 := by linarith
    exact_mod_cast this
  have q6 : c 6 = c' 6 := by
    have : (c 6 : ℚ) = c' 6 := by linarith
    exact_mod_cast this
  have q7 : c 7 = c' 7 := by
    have : (c 7 : ℚ) = c' 7 := by linarith
    exact_mod_cast this
  funext i
  fin_cases i <;> assumption

lemma e8_key (v : Fin 8 → ℚ) (t : ℤ) (z : Fin 8 → ℤ) (hv : ∀ i, v i = z i + (t : ℚ) / 2) (s : ℤ)
    (hs : ∑ i, v i = 2 * s) : ∃ c : Fin 8 → ℤ, v = ∑ i, c i • e8Simple i := by
  rw [Fin.sum_univ_eight] at hs
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  set s' : ℤ := s - 2 * t with hs'
  have hs2 : ((s' : ℤ) : ℚ) * 2 = z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 := by
    rw [hs']
    push_cast
    rw [h0, h1, h2, h3, h4, h5, h6, h7] at hs
    linarith
  obtain ⟨c, hc⟩ : ∃ c : Fin 8 → ℤ, c 0 = z 0 - z 7 ∧ c 1 = z 0 + z 1 - 2 * z 7 ∧
      c 2 = z 0 + z 1 + z 2 - 3 * z 7 ∧ c 3 = z 0 + z 1 + z 2 + z 3 - 4 * z 7 ∧
      c 4 = z 0 + z 1 + z 2 + z 3 + z 4 - 5 * z 7 ∧ c 5 = s' - 3 * z 7 - z 6 ∧
      c 6 = s' - 4 * z 7 ∧ c 7 = -2 * z 7 - t :=
    ⟨![z 0 - z 7, z 0 + z 1 - 2 * z 7, z 0 + z 1 + z 2 - 3 * z 7,
    z 0 + z 1 + z 2 + z 3 - 4 * z 7, z 0 + z 1 + z 2 + z 3 + z 4 - 5 * z 7,
    s' - 3 * z 7 - z 6, s' - 4 * z 7, -2 * z 7 - t], by simp⟩
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc
  refine ⟨c, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := e8_comb_apply c
  have d0 : (c 0 : ℚ) = z 0 - z 7 := by rw [c0]; push_cast; ring
  have d1 : (c 1 : ℚ) = z 0 + z 1 - 2 * z 7 := by rw [c1]; push_cast; ring
  have d2 : (c 2 : ℚ) = z 0 + z 1 + z 2 - 3 * z 7 := by rw [c2]; push_cast; ring
  have d3 : (c 3 : ℚ) = z 0 + z 1 + z 2 + z 3 - 4 * z 7 := by rw [c3]; push_cast; ring
  have d4 : (c 4 : ℚ) = z 0 + z 1 + z 2 + z 3 + z 4 - 5 * z 7 := by rw [c4]; push_cast; ring
  have d5 : (c 5 : ℚ) = s' - 3 * z 7 - z 6 := by rw [c5]; push_cast; ring
  have d6 : (c 6 : ℚ) = s' - 4 * z 7 := by rw [c6]; push_cast; ring
  have d7 : (c 7 : ℚ) = -2 * z 7 - t := by rw [c7]; push_cast; ring
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, a0, h0]; linarith
  · simp only [Fin.mk_one, a1, h1]; linarith
  · simp only [Fin.reduceFinMk, a2, h2]; linarith
  · simp only [Fin.reduceFinMk, a3, h3]; linarith
  · simp only [Fin.reduceFinMk, a4, h4]; linarith
  · simp only [Fin.reduceFinMk, a5, h5]; linarith
  · simp only [Fin.reduceFinMk, a6, h6]; linarith
  · simp only [Fin.reduceFinMk, a7, h7]; linarith

/-- **Problem 5.40 (a)**: the vectors `α_1, …, α_8` lie in `L` and form a `ℤ`-basis of it: every element of `L`
is uniquely an integer combination of them, and every integer combination lies in `L`. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e8Simple_isBasis :
    (∀ c : Fin 8 → ℤ, (∑ i, c i • e8Simple i) ∈ E8Lattice) ∧
      ∀ v ∈ E8Lattice, ∃! c : Fin 8 → ℤ, v = ∑ i, c i • e8Simple i := by
  refine ⟨e8_comb_mem, fun v hv => ?_⟩
  obtain ⟨hz, s, hs⟩ := hv
  have hex : ∃ c : Fin 8 → ℤ, v = ∑ i, c i • e8Simple i := by
    rcases hz with h | h
    · choose z hz using h
      exact e8_key v 0 z (fun i => by rw [hz i]; simp) s hs
    · choose z hz using h
      exact e8_key v 1 z (fun i => by rw [hz i]; simp) s hs
  obtain ⟨c, hc⟩ := hex
  exact ⟨c, hc, fun c' hc' => e8_comb_injective (hc'.symm.trans hc)⟩

end E8

end UndergradKB.RepresentationTheory
