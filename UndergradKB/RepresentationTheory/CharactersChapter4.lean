import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.FrobeniusSchur
import UndergradKB.RepresentationTheory.GL2
import UndergradKB.RepresentationTheory.MatrixElements

/-! # Frobenius-Schur indicator, character tables, group determinant (Etingof et al., Chapters 3-4)

* Definition 4.3: the indicator of an irreducible complex representation is `1` for real type and `-1` for
  quaternionic type (the case of complex type is in `CharactersMore.lean`).
* Section 4.24.1: the size `q² - q` of an elliptic conjugacy class of `GL_2(F_q)`.
* Lemma 4.8: the generic determinant is irreducible (`irreducible_genericDet`).
* Example 3.15: the character table of the quaternion group `Q8` (`irrChars_q8`).
-/

namespace UndergradKB.RepresentationTheory

open Representation Module
open scoped Matrix

section FrobeniusSchurValues

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem sum_sum_ite_and {n : ℕ} (i l : Fin n) (f : Fin n → Fin n → ℂ) :
    ∑ x, ∑ y, (if i = x ∧ l = y then f x y else 0) = f i l := by
  simp [ite_and]

/-- If an irreducible complex representation carries an invariant nondegenerate bilinear form with
`B v w = ε B w v` (where `ε * ε = 1`), then `∑_g χ(g²) = ε |G|`. The proof writes the transpose of the
representing matrices through the Gram matrix of `B` and applies the orthogonality of matrix elements. -/
theorem sum_character_sq_of_invariantForm (ρ : Representation ℂ G V) [IsIrreducible ρ] (ε : ℂ)
    (hε : ε * ε = 1) (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ v w, B v w = ε * B w v) (hinv : IsInvariantBilinForm ρ B) :
    ∑ g : G, ρ.character (g ^ 2) = ε * (Nat.card G : ℂ) := by
  classical
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set b := Module.finBasis ℂ V with hb
  set n := finrank ℂ V with hn
  let R : G → Matrix (Fin n) (Fin n) ℂ := fun g => LinearMap.toMatrix b b (ρ g)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.BilinForm.toMatrix b B
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hMT : Mᵀ = ε • M := by
    ext i j
    simp [M, LinearMap.BilinForm.toMatrix_apply, hs (b j) (b i)]
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hU)
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hU)
  -- invariance in matrix form
  have hRinv : ∀ g, (R g)ᵀ * M * R g = M := by
    intro g
    have h1 : B.comp (ρ g) (ρ g) = B := by
      ext v w
      exact hinv g v w
    have := LinearMap.BilinForm.toMatrix_comp b b B (ρ g) (ρ g)
    rw [h1] at this
    exact this.symm
  have hRS : ∀ g, R g * R g⁻¹ = 1 := by
    intro g
    simp only [R]
    rw [← LinearMap.toMatrix_mul, ← map_mul]
    simp
  have hT : ∀ g, (R g)ᵀ = M * R g⁻¹ * N := by
    intro g
    calc (R g)ᵀ = (R g)ᵀ * M * R g * R g⁻¹ * N := by
          rw [mul_assoc ((R g)ᵀ * M), hRS, mul_one, mul_assoc, hMN, mul_one]
      _ = M * R g⁻¹ * N := by rw [hRinv]
  have hent : ∀ g i l, R g l i = ∑ c, ∑ a, M i a * R g⁻¹ a c * N c l := by
    intro g i l
    have := congrFun (congrFun (hT g) i) l
    rw [Matrix.transpose_apply] at this
    rw [this]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  have hnz : (n : ℂ) ≠ 0 := finrank_ne_zero_of_isIrreducible (ρ := ρ) (k := ℂ)
  have hstep : ∀ i l, ∑ g : G, R g i l * R g l i = (Nat.card G : ℂ) / n * (M i l * N i l) := by
    intro i l
    have : ∀ g : G, R g i l * R g l i = ∑ c, ∑ a, (M i a * N c l) * (R g i l * R g⁻¹ a c) := by
      intro g
      rw [hent g i l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_comm]
    have h2 : ∀ c : Fin n, ∑ g : G, ∑ a : Fin n, (M i a * N c l) * (R g i l * R g⁻¹ a c) =
        ∑ a : Fin n, (M i a * N c l) * ∑ g : G, (R g i l * R g⁻¹ a c) := by
      intro c
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun c _ => h2 c]
    have h3 : ∀ a c : Fin n, ∑ g : G, (R g i l * R g⁻¹ a c) =
        if i = c ∧ l = a then (Nat.card G : ℂ) / n else 0 := fun a c =>
      sum_matrix_mul_matrix_inv (ρ := ρ) b i l a c
    simp only [h3]
    simp only [mul_ite, mul_zero]
    rw [sum_sum_ite_and i l]
    ring
  have hMNt : M * Nᵀ = ε • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h1 : Mᵀ * Nᵀ = 1 := by rw [← Matrix.transpose_mul, hNM, Matrix.transpose_one]
    rw [hMT, Matrix.smul_mul] at h1
    have h2 : M * Nᵀ = ε • (ε • (M * Nᵀ)) := by rw [smul_smul, hε, one_smul]
    rw [h2, h1]
  have hdiag : ∀ i, ∑ l, M i l * N i l = ε := by
    intro i
    have := congrFun (congrFun hMNt i) i
    simpa [Matrix.mul_apply] using this
  have htr : ∀ g : G, ρ.character (g ^ 2) = ∑ i, ∑ l, R g i l * R g l i := by
    intro g
    rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, pow_two, map_mul,
      LinearMap.toMatrix_mul, Matrix.trace]
    simp [Matrix.mul_apply, R]
  simp only [htr]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  simp only [hstep]
  simp only [← Finset.mul_sum, hdiag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Etingof et al., Definition 4.3**: the Frobenius-Schur indicator `|G|⁻¹ ∑_g χ(g²)` of an irreducible complex
representation of real type is `1`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
theorem fsIndicator_character_eq_one_of_isRealType (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (h : IsRealType ρ) : fsIndicator ρ.character = 1 := by
  obtain ⟨B, hB, hs, hinv⟩ := h
  have := sum_character_sq_of_invariantForm ρ 1 (by norm_num) B hB (fun v w => by rw [one_mul]; exact hs v w) hinv
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [fsIndicator, this, one_mul, inv_mul_cancel₀ hG]

/-- **Etingof et al., Definition 4.3**: the Frobenius-Schur indicator of an irreducible complex representation of
quaternionic type is `-1`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
theorem fsIndicator_character_eq_neg_one_of_isQuaternionicType (ρ : Representation ℂ G V)
    [IsIrreducible ρ] (h : IsQuaternionicType ρ) : fsIndicator ρ.character = -1 := by
  obtain ⟨B, hB, hs, hinv⟩ := h
  have := sum_character_sq_of_invariantForm ρ (-1) (by norm_num) B hB
    (fun v w => by rw [neg_one_mul]; exact hs v w) hinv
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [fsIndicator, this, neg_one_mul, mul_neg, inv_mul_cancel₀ hG]

/-- **Etingof et al., Definition 4.3** (complex type, restated with `fsIndicator`): the indicator is `0`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
theorem fsIndicator_character_eq_zero_of_isComplexType (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (h : IsComplexType ρ) : fsIndicator ρ.character = 0 :=
  card_inv_mul_sum_character_sq_eq_zero ρ h

end FrobeniusSchurValues

section Q8

open QuaternionGroup

/-- The quaternion group of order 8. -/
abbrev Q8 := QuaternionGroup 2

/-- The sign `(-1)^i` of a residue modulo 4. -/
def q8sgn (i : ZMod 4) : ℤˣ := if i.val % 2 = 0 then 1 else -1

/-- The four linear characters of `Q8`, with values in `ℤˣ`: `u` says whether `a` is sent to `-1`, and `v` whether `xa 0` is. -/
def q8Lin (u v : Bool) : Q8 →* ℤˣ where
  toFun g := match g with
    | a i => if u then q8sgn i else 1
    | xa i => (if v then -1 else 1) * (if u then q8sgn i else 1)
  map_one' := by cases u <;> cases v <;> decide
  map_mul' := by
    cases u <;> cases v <;> decide

/-- The four linear characters of `Q8` as complex-valued functions. -/
def q8Char (u v : Bool) : Q8 → ℂ := fun g => (((q8Lin u v g : ℤˣ) : ℤ) : ℂ)

/-- The character of the 2-dimensional irreducible representation of `Q8`: `2` at `1`, `-2` at `-1`, `0` elsewhere. -/
def q8Psi : Q8 → ℂ := fun g => if g = 1 then 2 else if g = a 2 then -2 else 0

/-- The monoid homomorphism `Q8 →* ℂ` given by a linear character. -/
def q8Hom (u v : Bool) : Q8 →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp (q8Lin u v))

/-- A one-dimensional representation attached to a monoid homomorphism to `ℂ`. -/
def lineRep' {G : Type*} [Group G] (φ : G →* ℂ) : Representation ℂ G ℂ where
  toFun g := φ g • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [mul_comm]

theorem character_lineRep' {G : Type*} [Group G] (φ : G →* ℂ) (g : G) :
    (lineRep' φ).character g = φ g := by
  simp [Representation.character, lineRep']

theorem isIrreducible_of_finrank_eq_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hV : finrank ℂ V = 1) : IsIrreducible ρ := by
  have : IsSimpleOrder (Submodule ℂ V) := is_simple_module_of_finrank_eq_one (K := ℂ) (A := ℂ) hV
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top this
  · rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
    · left
      exact Subrepresentation.toSubmodule_injective h
    · right
      exact Subrepresentation.toSubmodule_injective h

/-- A label for the conjugacy class of an element of `Q8`. -/
def q8cls : Q8 → Fin 5
  | a i => if i.val = 0 then 0 else if i.val = 2 then 1 else 2
  | xa i => if i.val % 2 = 0 then 3 else 4

theorem q8_isConj_iff (x y : Q8) : IsConj x y ↔ q8cls x = q8cls y := by
  rw [isConj_iff]
  revert x y
  decide

theorem card_conjClasses_q8 : Nat.card (ConjClasses Q8) = 5 := by
  let f : ConjClasses Q8 → Fin 5 := Quotient.lift q8cls (fun x y h => (q8_isConj_iff x y).mp h)
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using Quotient.inductionOn with | _ x =>
      induction q using Quotient.inductionOn with | _ y =>
      intro h
      exact Quotient.sound ((q8_isConj_iff x y).mpr h)
    · intro j
      have : ∀ j : Fin 5, ∃ g : Q8, q8cls g = j := by decide
      obtain ⟨g, hg⟩ := this j
      exact ⟨ConjClasses.mk g, hg⟩
  rw [Nat.card_eq_of_bijective f hf]
  simp

/-- The linear character `q8Char u v` is the character of a one-dimensional irreducible representation. -/
theorem q8Char_mem_irrChars (u v : Bool) : q8Char u v ∈ irrChars ℂ Q8 := by
  have hirr := isIrreducible_of_finrank_eq_one (lineRep' (q8Hom u v)) (Module.finrank_self ℂ)
  refine ⟨@IrrRep.mk ℂ Q8 _ _ ℂ _ _ _ (lineRep' (q8Hom u v)) hirr, ?_⟩
  funext g
  exact character_lineRep' (q8Hom u v) g

theorem q8Char_injective : Function.Injective fun p : Bool × Bool => q8Char p.1 p.2 := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have h1 := congrFun h (a 1)
  have h2 := congrFun h (xa 0)
  have key : ∀ u u' v v' : Bool, ((((q8Lin u v (a 1) : ℤˣ) : ℤ) : ℂ) = (((q8Lin u' v' (a 1) : ℤˣ) : ℤ) : ℂ)) →
      ((((q8Lin u v (xa 0) : ℤˣ) : ℤ) : ℂ) = (((q8Lin u' v' (xa 0) : ℤˣ) : ℤ) : ℂ)) → u = u' ∧ v = v' := by
    intro u u' v v' h1 h2
    have h1' := Int.cast_injective (α := ℂ) h1
    have h2' := Int.cast_injective (α := ℂ) h2
    revert h1' h2'
    cases u <;> cases u' <;> cases v <;> cases v' <;> decide
  obtain ⟨rfl, rfl⟩ := key u u' v v' h1 h2
  rfl

/-- The sum of the values of the four linear characters, plus twice `q8Psi`, vanishes away from `1`. -/
theorem q8_column (g : Q8) (hg : g ≠ 1) :
    (∑ p : Bool × Bool, q8Char p.1 p.2 g) + 2 * q8Psi g = 0 := by
  have key : ∀ g : Q8, g ≠ 1 → (∑ p : Bool × Bool, (((q8Lin p.1 p.2 g : ℤˣ) : ℤ))) +
      2 * (if g = 1 then (2 : ℤ) else if g = a 2 then -2 else 0) = 0 := by decide
  have hpsi : q8Psi g = ((if g = 1 then (2 : ℤ) else if g = a 2 then -2 else 0 : ℤ) : ℂ) := by
    simp only [q8Psi]
    split_ifs <;> simp
  show (∑ p : Bool × Bool, (((q8Lin p.1 p.2 g : ℤˣ) : ℤ) : ℂ)) + 2 * q8Psi g = 0
  rw [hpsi]
  exact_mod_cast key g hg

/-- **Etingof et al., Example 3.15** (character table of `Q8`): the irreducible characters of the quaternion group
of order 8 are exactly the four linear characters `q8Char u v` (the characters trivial or equal to `-1` on `a` and
on `xa 0`) and the class function `q8Psi` with values `2` at `1`, `-2` at `-1` and `0` elsewhere. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem irrChars_q8 :
    irrChars ℂ Q8 = insert q8Psi (Set.range fun p : Bool × Bool => q8Char p.1 p.2) := by
  classical
  have : Invertible (Nat.card Q8 : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hfin : (irrChars ℂ Q8).Finite := irrChars_finite
  have hcardT : hfin.toFinset.card = 5 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
    rw [card_irrChars, card_conjClasses_q8]
  set F : Bool × Bool → (Q8 → ℂ) := fun p => q8Char p.1 p.2 with hF
  set S : Finset (Q8 → ℂ) := Finset.univ.image F with hS
  have hcardS : S.card = 4 := by
    rw [hS, Finset.card_image_of_injective _ q8Char_injective]
    simp
  have hST : S ⊆ hfin.toFinset := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfin.mem_toFinset.mpr (q8Char_mem_irrChars p.1 p.2)
  obtain ⟨χ5, hχ5T, hχ5S⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := hfin.toFinset)
    (by omega)
  have hEq : hfin.toFinset = insert χ5 S := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hχ5T
      · exact hST hx
    · rw [Finset.card_insert_of_notMem hχ5S]
      omega
  -- sums over the irreducible characters
  have hsum : ∀ H : (Q8 → ℂ) → ℂ, ∑ χ : irrChars ℂ Q8, H (χ : Q8 → ℂ) = H χ5 + ∑ p : Bool × Bool, H (F p) := by
    intro H
    rw [← Finset.sum_subtype hfin.toFinset (p := fun x => x ∈ irrChars ℂ Q8) (fun x => hfin.mem_toFinset) H, hEq,
      Finset.sum_insert hχ5S, hS, Finset.sum_image (fun p _ q _ h => q8Char_injective h)]
  have hχ5mem : χ5 ∈ irrChars ℂ Q8 := hfin.mem_toFinset.mp hχ5T
  -- the dimension of the fifth character
  have h1 : χ5 1 ^ 2 = 4 := by
    have := sum_irrChars_one_sq (k := ℂ) (G := Q8)
    rw [hsum (fun f : Q8 → ℂ => f 1 ^ 2)] at this
    have hc : (Nat.card Q8 : ℂ) = 8 := by
      rw [Nat.card_eq_fintype_card]
      simp [QuaternionGroup.card]
    rw [hc] at this
    have hone : ∀ p : Bool × Bool, F p 1 = 1 := by
      intro p
      simp [hF, q8Char]
    simp only [hone] at this
    simp at this
    linear_combination this
  have hdim : χ5 1 = 2 := by
    obtain ⟨X, hX⟩ := hχ5mem
    have hX' : X.ρ.character = χ5 := hX
    have hn : χ5 1 = (Module.finrank ℂ X.V : ℂ) := by rw [← hX', char_one]
    rw [hn] at h1 ⊢
    have h2 : (Module.finrank ℂ X.V) ^ 2 = 4 := by exact_mod_cast h1
    have h3 : Module.finrank ℂ X.V = 2 := by
      have : Module.finrank ℂ X.V ≤ 2 := by nlinarith
      have : 0 < Module.finrank ℂ X.V := by
        rcases Nat.eq_zero_or_pos (Module.finrank ℂ X.V) with h | h
        · rw [h] at h2; omega
        · exact h
      interval_cases (Module.finrank ℂ X.V) <;> omega
    rw [h3]; norm_num
  have hcol : ∀ g : Q8, g ≠ 1 → χ5 g * 2 + ∑ p : Bool × Bool, F p g = 0 := by
    intro g hg
    have := sum_irrChars_mul_inv (k := ℂ) (G := Q8) g 1
    have hnc : ¬ IsConj g 1 := fun h => hg (isConj_one_left.mp h)
    simp only [inv_one, hnc, ↓reduceIte] at this
    rw [hsum (fun f : Q8 → ℂ => f g * f 1)] at this
    have hone : ∀ p : Bool × Bool, F p 1 = 1 := by
      intro p
      simp [hF, q8Char]
    simp only [hone, hdim, mul_one] at this
    linear_combination this
  have hψ : χ5 = q8Psi := by
    funext g
    by_cases hg : g = 1
    · subst hg
      simp [hdim, q8Psi]
    · have h := q8_column g hg
      have := hcol g hg
      simp only [hF] at this
      linear_combination (1/2 : ℂ) * this - (1 / 2 : ℂ) * h
  ext x
  rw [← hfin.mem_toFinset, hEq, Finset.mem_insert, hψ, hS, Finset.mem_image]
  simp [hF]

/-- The character table of `Q8` also yields the two-dimensional irreducible representation: there is an irreducible
complex representation of `Q8` of dimension `2` whose character is `q8Psi`. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem exists_irrRep_q8_dim_two :
    ∃ X : IrrRep ℂ Q8, X.ρ.character = q8Psi ∧ Module.finrank ℂ X.V = 2 := by
  have h : q8Psi ∈ irrChars ℂ Q8 := by rw [irrChars_q8]; exact Set.mem_insert _ _
  obtain ⟨X, hX⟩ := h
  refine ⟨X, hX, ?_⟩
  have h1 := char_one X.ρ
  have hX' : X.ρ.character = q8Psi := hX
  rw [hX'] at h1
  have : ((Module.finrank ℂ X.V : ℕ) : ℂ) = 2 := by rw [← h1]; simp [q8Psi]
  exact_mod_cast this

end Q8

universe u

namespace GL2

open Matrix

section Elliptic

variable {F : Type u} [Field F]

/-- The determinant of `a • 1 + b • C`, where `C` is the companion matrix of `x² - t x + n`, is nonzero for
`(a, b) ≠ 0` provided the quadratic has no root. -/
lemma ell_det_ne_zero {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) {a b : F} (hab : (a, b) ≠ 0) :
    a * (a + b * t) - (-(b * n)) * b ≠ 0 := by
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := fun ha => hab (by simp [ha])
    simpa using ha
  · intro h0
    apply h (-a / b)
    field_simp
    linear_combination h0

/-- The element `a • 1 + b • C` of `GL_2(F)`, `C = [[0, -n], [1, t]]` the companion matrix of `x² - t x + n`. -/
noncomputable def ellUnit {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) (p : {p : F × F // p ≠ 0}) :
    GL (Fin 2) F :=
  GeneralLinearGroup.mk'' !![p.1.1, -(p.1.2 * n); p.1.2, p.1.1 + p.1.2 * t]
    (by
      rw [Matrix.det_fin_two_of]
      exact (isUnit_iff_ne_zero.mpr (ell_det_ne_zero h p.2)))

lemma ellUnit_injective {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) : Function.Injective (ellUnit h) := by
  intro p q hpq
  have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hpq
  have e00 := congrFun (congrFun e 0) 0
  have e10 := congrFun (congrFun e 1) 0
  simp [ellUnit] at e00 e10
  exact Subtype.ext (Prod.ext e00 e10)

/-- The companion matrix `[[0, -n], [1, t]]` of an irreducible quadratic `x² - t x + n` (an elliptic element). -/
noncomputable def ellipticElt {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) : GL (Fin 2) F :=
  ellUnit h ⟨(0, 1), by simp⟩

lemma centralizer_elliptic {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    (Subgroup.centralizer {(ellipticElt h : GL (Fin 2) F)} : Set (GL (Fin 2) F)) = Set.range (ellUnit h) := by
  ext g
  constructor
  · intro hg
    have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      (Subgroup.mem_centralizer_iff.1 hg _ (Set.mem_singleton _))
    have e00 := congrFun (congrFun e 0) 0
    have e11 := congrFun (congrFun e 1) 0
    have e01 := congrFun (congrFun e 0) 1
    simp [ellipticElt, ellUnit, Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
    have hdet := (GeneralLinearGroup.det g).isUnit.ne_zero
    have hne : ((g : Matrix (Fin 2) (Fin 2) F) 0 0, (g : Matrix (Fin 2) (Fin 2) F) 1 0) ≠ 0 := by
      intro h0
      have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := congrArg Prod.fst h0
      have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := congrArg Prod.snd h0
      apply hdet
      rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by rw [← e00, h10]; ring
      rw [h00, h01]; ring
    refine ⟨⟨_, hne⟩, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ellUnit] <;> first | done | linear_combination e00 | linear_combination e11
  · rintro ⟨p, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Units.ext
    ext i j
    simp only [Units.val_mul, ellipticElt, ellUnit, coe_mk'']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma card_centralizer_elliptic [Finite F] {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    Nat.card (Subgroup.centralizer {(ellipticElt h : GL (Fin 2) F)}) = Nat.card F ^ 2 - 1 := by
  have h1 : Nat.card (Subgroup.centralizer {(ellipticElt h : GL (Fin 2) F)}) =
      Nat.card (Set.range (ellUnit h)) := by
    rw [← centralizer_elliptic h]; rfl
  rw [h1, Nat.card_range_of_injective (ellUnit_injective h)]
  have := Fintype.ofFinite F
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun p : F × F => p = 0), Fintype.card_subtype_eq,
    Fintype.card_prod, Nat.card_eq_fintype_card, sq]

/-- **Etingof et al., §4.24.1 (table)**: the conjugacy class of an elliptic element (the companion matrix of a
monic quadratic without roots in `F`) has `q² - q` elements. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_conjugatesOf_elliptic [Finite F] {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    (conjugatesOf (ellipticElt h : GL (Fin 2) F)).ncard = Nat.card F ^ 2 - Nat.card F := by
  have h2 := ncard_conjugatesOf_mul_card_centralizer (ellipticElt h : GL (Fin 2) F)
  rw [card_centralizer_elliptic h, card_GL2] at h2
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq
  rw [hr] at h2 ⊢
  have hpos : 0 < (2 + r) ^ 2 - 1 := by
    have : (2 + r) ^ 2 - 1 = (1 + r) * (3 + r) := Nat.sub_eq_of_eq_add (by ring)
    rw [this]; positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h2]
  have e2 : (2 + r) ^ 2 - 1 = (1 + r) * (3 + r) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 + r) ^ 2 - (2 + r) = (1 + r) * (2 + r) := Nat.sub_eq_of_eq_add (by ring)
  have e1 : 2 + r - 1 = 1 + r := by omega
  exact Nat.mul_comm _ _

end Elliptic

end GL2

section GenericDet

open MvPolynomial

section KillVar

variable (K : Type*) {σ : Type*} [Field K] [DecidableEq σ]

/-- The substitution setting the variable `u` to `0` and fixing all other variables. -/
noncomputable def killVar (u : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun w => if w = u then 0 else X w

variable {K}

@[simp] theorem killVar_X (u w : σ) : killVar K u (X w) = if w = u then 0 else X w := by
  simp [killVar]

theorem killVar_of_notMem_vars {u : σ} {p : MvPolynomial σ K} (h : u ∉ p.vars) : killVar K u p = p := by
  have := aeval_ite_mem_eq_self p (s := ({u}ᶜ : Set σ)) (by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact h hw)
  have e : (fun w => if w = u then (0 : MvPolynomial σ K) else X w) =
      fun i => if i ∈ ({u}ᶜ : Set σ) then X i else 0 := by
    funext w
    by_cases hw : w = u <;> simp [hw]
  unfold killVar
  rw [e]
  exact this

theorem notMem_vars_killVar (u : σ) (p : MvPolynomial σ K) : u ∉ (killVar K u p).vars := by
  intro h
  unfold killVar at h
  change u ∈ (bind₁ (fun w => if w = u then (0 : MvPolynomial σ K) else X w) p).vars at h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ p h)
  by_cases hiu : i = u
  · simp [hiu] at hi
  · simp only [hiu, ite_false] at hi
    rw [vars_X] at hi
    simp only [Finset.mem_singleton] at hi
    exact hiu hi.symm

theorem killVar_ne_self {u : σ} {p : MvPolynomial σ K} (h : u ∈ p.vars) : killVar K u p ≠ p := by
  intro e
  apply notMem_vars_killVar u p
  rw [e]
  exact h

theorem vars_killVar_subset (u : σ) (p : MvPolynomial σ K) : (killVar K u p).vars ⊆ p.vars := by
  intro w hw
  unfold killVar at hw
  change w ∈ (bind₁ (fun w => if w = u then (0 : MvPolynomial σ K) else X w) p).vars at hw
  obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ p hw)
  by_cases hiu : i = u
  · simp [hiu] at hwi
  · simp only [hiu, ite_false] at hwi
    rw [vars_X] at hwi
    simp only [Finset.mem_singleton] at hwi
    rw [hwi]
    exact hi

end KillVar

section Det

variable (K : Type*) {ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The monomial `∏_k x_{π(k), k}` of the Leibniz expansion of the generic determinant. -/
noncomputable def detTerm (π : Equiv.Perm ι) : MvPolynomial (ι × ι) K := ∏ k, X (π k, k)

theorem genericDet_eq : (Matrix.mvPolynomialX ι ι K).det =
    ∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : MvPolynomial (ι × ι) K) * detTerm K π := by
  rw [Matrix.det_apply']
  rfl

variable {K}

theorem killVar_detTerm (u : ι × ι) (π : Equiv.Perm ι) :
    killVar K u (detTerm K π) = if ∃ k, (π k, k) = u then 0 else detTerm K π := by
  unfold detTerm
  rw [map_prod]
  by_cases h : ∃ k, (π k, k) = u
  · obtain ⟨k, hk⟩ := h
    have h' : ∃ k, (π k, k) = u := ⟨k, hk⟩
    simp only [h', ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  · simp only [h, ↓reduceIte]
    push Not at h
    exact Finset.prod_congr rfl fun k _ => by simp [h k]

omit [Fintype ι] [DecidableEq ι] in
theorem not_both_mem (π : Equiv.Perm ι) {v w : ι × ι} (hvw : v ≠ w) (h : v.1 = w.1 ∨ v.2 = w.2) :
    ¬ ((∃ k, (π k, k) = v) ∧ ∃ k, (π k, k) = w) := by
  rintro ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  apply hvw
  rw [← hk, ← hk']
  rcases h with h | h
  · rw [← hk, ← hk'] at h
    have : k = k' := π.injective h
    rw [this]
  · rw [← hk, ← hk'] at h
    simp only at h
    rw [h]

theorem detTerm_split (π : Equiv.Perm ι) {v w : ι × ι} (hvw : v ≠ w) (h : v.1 = w.1 ∨ v.2 = w.2) :
    detTerm K π = killVar K v (detTerm K π) + killVar K w (detTerm K π) -
      killVar K v (killVar K w (detTerm K π)) := by
  have hex := not_both_mem π hvw h
  have key : ∀ u : ι × ι, (∃ k, (π k, k) = u) → killVar K u (detTerm K π) = 0 := by
    intro u hu
    rw [killVar_detTerm]
    simp [hu]
  have key' : ∀ u : ι × ι, ¬ (∃ k, (π k, k) = u) → killVar K u (detTerm K π) = detTerm K π := by
    intro u hu
    rw [killVar_detTerm]
    simp [hu]
  by_cases hv : ∃ k, (π k, k) = v
  · have hw : ¬ ∃ k, (π k, k) = w := fun hw => hex ⟨hv, hw⟩
    rw [key' w hw, key v hv]
    ring
  · by_cases hw : ∃ k, (π k, k) = w
    · rw [key w hw, key' v hv, map_zero]
      ring
    · rw [key' w hw, key' v hv]
      ring

theorem genericDet_split {v w : ι × ι} (hvw : v ≠ w) (h : v.1 = w.1 ∨ v.2 = w.2) :
    (Matrix.mvPolynomialX ι ι K).det = killVar K v (Matrix.mvPolynomialX ι ι K).det +
      killVar K w (Matrix.mvPolynomialX ι ι K).det -
      killVar K v (killVar K w (Matrix.mvPolynomialX ι ι K).det) := by
  rw [genericDet_eq]
  simp only [map_sum, map_mul, map_intCast]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← mul_add, ← mul_sub, ← detTerm_split π hvw h]

theorem degreeOf_detTerm_le (u : ι × ι) (π : Equiv.Perm ι) : degreeOf u (detTerm K π) ≤ 1 := by
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp only [degreeOf_X]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun k => u = (π k, k)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have := (ha.symm.trans hb).symm
    exact (Prod.mk.inj this).2.symm
  simpa using this

theorem degreeOf_genericDet_le (u : ι × ι) : degreeOf u (Matrix.mvPolynomialX ι ι K).det ≤ 1 := by
  rw [genericDet_eq]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun π _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have : ((Equiv.Perm.sign π : ℤ) : MvPolynomial (ι × ι) K) = C ((Equiv.Perm.sign π : ℤ) : K) := by simp
  rw [this, degreeOf_C, zero_add]
  exact degreeOf_detTerm_le u π

omit [Fintype ι] in
theorem eval_killVar (u : ι × ι) (s : ι × ι → K) (p : MvPolynomial (ι × ι) K) :
    eval s (killVar K u p) = eval (fun w => if w = u then 0 else s w) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [killVar]
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp =>
    rw [map_mul, map_mul, hp, killVar_X]
    by_cases hw : w = u <;> simp [hw]

/-- Every variable occurs in the generic determinant. -/
theorem mem_vars_genericDet (u : ι × ι) : u ∈ (Matrix.mvPolynomialX ι ι K).det.vars := by
  by_contra hu
  have h1 := killVar_of_notMem_vars hu
  set π : Equiv.Perm ι := Equiv.swap u.1 u.2 with hπ
  set s : ι × ι → K := fun w => (π.permMatrix K) w.1 w.2 with hs
  have e1 : eval s (Matrix.mvPolynomialX ι ι K).det ≠ 0 := by
    rw [Matrix.eval_det_mvPolynomialX]
    have : (Matrix.of fun i j : ι => s (i, j)) = π.permMatrix K := rfl
    rw [this, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have e2 : eval s (killVar K u (Matrix.mvPolynomialX ι ι K).det) = 0 := by
    rw [eval_killVar, Matrix.eval_det_mvPolynomialX]
    apply Matrix.det_eq_zero_of_row_eq_zero u.1
    intro j
    by_cases hj : j = u.2
    · simp [hj]
    · have : (u.1, j) ≠ u := fun h => hj (congrArg Prod.snd h)
      simp [this, hs, hπ, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply, Ne.symm hj]
  rw [h1] at e2
  exact e1 e2

section Irreducible

variable (K ι) in
/-- The determinant of the generic `n × n` matrix with independent variables as entries. -/
noncomputable abbrev genericDet : MvPolynomial (ι × ι) K := (Matrix.mvPolynomialX ι ι K).det

theorem genericDet_ne_zero : genericDet K ι ≠ 0 := Matrix.det_mvPolynomialX_ne_zero ι K

/-- In a factorisation of the generic determinant, each variable occurs in exactly one factor. -/
theorem mem_vars_or {P Q : MvPolynomial (ι × ι) K} (h : P * Q = genericDet K ι) (u : ι × ι) :
    (u ∈ P.vars ∧ u ∉ Q.vars) ∨ (u ∈ Q.vars ∧ u ∉ P.vars) := by
  have hP : P ≠ 0 := left_ne_zero_of_mul (h ▸ genericDet_ne_zero)
  have hQ : Q ≠ 0 := right_ne_zero_of_mul (h ▸ genericDet_ne_zero)
  have hu : u ∈ (P * Q).vars := h ▸ mem_vars_genericDet u
  have hd : degreeOf u P + degreeOf u Q ≤ 1 := by
    rw [← degreeOf_mul_eq hP hQ, h]
    exact degreeOf_genericDet_le u
  rcases Finset.mem_union.mp (vars_mul P Q hu) with h1 | h1
  · left
    refine ⟨h1, fun h2 => ?_⟩
    have := (mem_vars_iff_degreeOf_ne_zero).mp h1
    have := (mem_vars_iff_degreeOf_ne_zero).mp h2
    omega
  · right
    refine ⟨h1, fun h2 => ?_⟩
    have := (mem_vars_iff_degreeOf_ne_zero).mp h1
    have := (mem_vars_iff_degreeOf_ne_zero).mp h2
    omega

/-- Two variables in the same row or column cannot be separated by a factorisation. -/
theorem no_split {P Q : MvPolynomial (ι × ι) K} (h : P * Q = genericDet K ι) {v w : ι × ι} (hvw : v ≠ w)
    (hrc : v.1 = w.1 ∨ v.2 = w.2) (hvP : v ∈ P.vars) (hvQ : v ∉ Q.vars) (hwQ : w ∈ Q.vars)
    (hwP : w ∉ P.vars) : False := by
  have hsplit : genericDet K ι = killVar K v (genericDet K ι) + killVar K w (genericDet K ι) -
      killVar K v (killVar K w (genericDet K ι)) := genericDet_split (K := K) (ι := ι) hvw hrc
  rw [← h] at hsplit
  have hQ0 : v ∉ (killVar K w Q).vars := fun hh => hvQ (vars_killVar_subset w Q hh)
  rw [map_mul, map_mul, map_mul, killVar_of_notMem_vars hwP, killVar_of_notMem_vars hvQ,
    killVar_of_notMem_vars hQ0] at hsplit
  have hz : (P - killVar K v P) * (Q - killVar K w Q) = 0 := by linear_combination hsplit
  rcases mul_eq_zero.mp hz with h1 | h1
  · exact killVar_ne_self hvP (sub_eq_zero.mp h1).symm
  · exact killVar_ne_self hwQ (sub_eq_zero.mp h1).symm

theorem isUnit_of_mem_vars [Nonempty ι] {P Q : MvPolynomial (ι × ι) K} (h : P * Q = genericDet K ι)
    {u : ι × ι} (hu : u ∈ P.vars) : IsUnit Q := by
  have hQ : Q ≠ 0 := right_ne_zero_of_mul (h ▸ genericDet_ne_zero)
  have hsym : ∀ {v w : ι × ι}, (v.1 = w.1 ∨ v.2 = w.2) → v ∈ P.vars → w ∈ P.vars := by
    intro v w hrc hv
    by_cases hvw : v = w
    · rw [← hvw]; exact hv
    · rcases mem_vars_or h w with hw | hw
      · exact hw.1
      · exfalso
        rcases mem_vars_or h v with hv' | hv'
        · exact no_split h hvw hrc hv'.1 hv'.2 hw.1 hw.2
        · exact hv'.2 hv
  have hall : ∀ w : ι × ι, w ∈ P.vars := by
    intro w
    have h1 : (u.1, w.2) ∈ P.vars := hsym (v := u) (w := (u.1, w.2)) (Or.inl rfl) hu
    exact hsym (v := (u.1, w.2)) (w := w) (Or.inr rfl) h1
  have hvars : Q.vars = ∅ := by
    ext w
    simp only [Finset.notMem_empty, iff_false]
    intro hw
    rcases mem_vars_or h w with h1 | h1
    · exact h1.2 hw
    · exact h1.2 (hall w)
  rw [vars_eq_empty_iff_eq_C] at hvars
  have hc : Q.coeff 0 ≠ 0 := fun h0 => hQ (by rw [hvars, h0, map_zero])
  rw [hvars]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- **Etingof et al., Lemma 4.8**: the determinant of the generic matrix, a polynomial in the `n²` entries as
independent variables over a field `K`, is irreducible (for `n ≥ 1`). -/
@[kb "etingof2011" "Lemma 4.8, p. 48"]
theorem irreducible_genericDet [Nonempty ι] : Irreducible (genericDet K ι) := by
  refine ⟨fun hu => ?_, fun P Q h => ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨E, hE⟩ := hu.exists_right_inv
    have hQ : genericDet K ι ≠ 0 := genericDet_ne_zero
    have hE0 : E ≠ 0 := right_ne_zero_of_mul (hE ▸ one_ne_zero)
    have := degreeOf_mul_eq (n := (i, i)) hQ hE0
    rw [hE, degreeOf_one] at this
    have hv : degreeOf (i, i) (genericDet K ι) ≠ 0 :=
      (mem_vars_iff_degreeOf_ne_zero).mp (mem_vars_genericDet (K := K) (i, i))
    omega
  · obtain ⟨i⟩ := ‹Nonempty ι›
    rcases mem_vars_or h.symm (i, i) with h1 | h1
    · exact Or.inr (isUnit_of_mem_vars h.symm h1.1)
    · exact Or.inl (isUnit_of_mem_vars (by rw [mul_comm]; exact h.symm) h1.1)

end Irreducible

end Det

end GenericDet

end UndergradKB.RepresentationTheory
