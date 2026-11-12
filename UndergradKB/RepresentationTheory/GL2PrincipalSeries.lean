import UndergradKB.RepresentationTheory.GL2
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.RepresentationTheory.LittleGroupTheorem
import UndergradKB.RepresentationTheory.CharacterDetermines
import UndergradKB.Common.Attr

/-! # Irreducibility of the principal series of GL_2(F_q) (Etingof et al., Theorem 4.71)

Let `F` be a finite field, `G = GL_2(F)`, `B` the Borel subgroup of upper triangular matrices, and for two
characters `λ₁, λ₂` of `F^×` let `V_{λ₁,λ₂} = Ind_B^G C_λ` be the principal series (`principalSeries`, defined in
`GL2.lean`). We prove:

* `isIrreducible_principalSeries`: if `λ₁ ≠ λ₂`, then `V_{λ₁,λ₂}` is irreducible;
* `nonempty_equiv_principalSeries_iff`: for `λ₁ ≠ λ₂` and `λ₁' ≠ λ₂'`, the representations `V_{λ₁,λ₂}` and
  `V_{λ₁',λ₂'}` are isomorphic exactly when the unordered pairs `{λ₁, λ₂}` and `{λ₁', λ₂'}` agree.
* `principalSeries_diag_decomposition`: `V_{μ,μ}` is the direct sum of the line `C_μ` spanned by `x ↦ μ(det x)`
  and an irreducible subrepresentation `W_μ` of dimension `q` (its character has norm `2`).

The proof computes the Hermitian inner product of two induced characters by a Mackey-type double sum
(`hermitianPairing_principalSeries`): with `e_λ` the character of `C_λ` extended by zero to `G`,
`(χ_{V_λ}, χ_{V_λ'}) = |B|⁻² ∑_{u ∈ G} ∑_{h ∈ G} e_λ(h) conj e_λ'(u h u⁻¹)`.
For `u ∈ B` the inner sum is `|B|` or `0` according as `λ = λ'`. For `u ∉ B`, an element `h` of `B` with
`u h u⁻¹ ∈ B` has the diagonal entries of `u h u⁻¹` equal to those of `h` swapped (`conj_diag_of_not_mem`), and for
every pair `x, y` of nonzero scalars such an `h` with diagonal `(x, y)` exists (`exists_twist`); hence the inner sum
vanishes unless `λ₁ = λ₂'` and `λ₂ = λ₁'`, in which case it is a positive integer.
This replaces the book's computation of the character on the four kinds of conjugacy classes; the outcome is the
same. For `λ₁ = λ₂` every `u ∉ B` contributes `|B ∩ u⁻¹ B u| = (q - 1)²` (`card_stab`), giving norm `2`.
-/

universe u

namespace UndergradKB.RepresentationTheory.GL2

open Matrix Representation Module ComplexConjugate

set_option linter.unusedSectionVars false

/-! ### A double-sum identity for averaged characters -/

section Mackey

variable {G : Type*} [Group G] [Fintype G]

/-- The product of two conjugation-averaged functions, summed over the group. -/
lemma sum_conjAvg_mul_conj (e e' : G → ℂ) :
    ∑ g, (∑ x, e (x * g * x⁻¹)) * conj (∑ y, e' (y * g * y⁻¹)) =
      (Fintype.card G : ℂ) * ∑ u, ∑ h, e h * conj (e' (u * h * u⁻¹)) := by
  have key : ∀ x : G, ∑ g, ∑ y, e (x * g * x⁻¹) * conj (e' (y * g * y⁻¹)) =
      ∑ u, ∑ h, e h * conj (e' (u * h * u⁻¹)) := by
    intro x
    rw [Finset.sum_comm]
    refine Fintype.sum_equiv (Equiv.mulRight x⁻¹) _ _ (fun y => ?_)
    refine Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [show y * x⁻¹ * (x * g * x⁻¹) * (y * x⁻¹)⁻¹ = y * g * y⁻¹ by group]
  calc ∑ g, (∑ x, e (x * g * x⁻¹)) * conj (∑ y, e' (y * g * y⁻¹))
      = ∑ x, ∑ g, ∑ y, e (x * g * x⁻¹) * conj (e' (y * g * y⁻¹)) := by
        simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A function on a group which is multiplied by a constant `c ≠ 1` under left translation by `t` has sum zero. -/
lemma sum_eq_zero_of_mul_left {f : G → ℂ} (t : G) (c : ℂ) (hc : c ≠ 1) (hf : ∀ h, f (t * h) = c * f h) :
    ∑ h, f h = 0 := by
  have h1 : ∑ h, f h = c * ∑ h, f h := by
    rw [Finset.mul_sum]
    calc ∑ h, f h = ∑ h, f (t * h) :=
          (Fintype.sum_equiv (Equiv.mulLeft t) (fun h => f (t * h)) f (fun h => rfl)).symm
      _ = ∑ h, c * f h := Finset.sum_congr rfl fun h _ => hf h
  have : (1 - c) * ∑ h, f h = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hc))

/-- Values of a homomorphism from a finite group to `ℂˣ` have conjugate equal to their inverse. -/
lemma conj_hom_eq_inv {H : Type*} [Group H] [Finite H] (χ : H →* ℂˣ) (b : H) :
    conj (χ b : ℂ) = ((χ b)⁻¹ : ℂˣ) := by
  have hpow : (χ b : ℂ) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have hnorm : ‖(χ b : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  have hne : (χ b : ℂ) ≠ 0 := (χ b).ne_zero
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
  simp

lemma conj_hom_mul_self {H : Type*} [Group H] [Finite H] (χ : H →* ℂˣ) (b : H) :
    (χ b : ℂ) * conj (χ b : ℂ) = 1 := by
  rw [conj_hom_eq_inv]; simp

end Mackey

/-! ### Characters of the Borel subgroup extended by zero -/

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

instance decidableMemBorel : DecidablePred (· ∈ borel F) := fun g =>
  inferInstanceAs (Decidable ((g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0))

noncomputable instance fintypeRCosetsBorel : Fintype (RCosets (borel F)) := Fintype.ofFinite _

/-- A character of `B`, extended by zero to `GL_2(F)`. -/
noncomputable def extC (χ : borel F →* ℂˣ) (y : GL (Fin 2) F) : ℂ :=
  if h : y ∈ borel F then (χ ⟨y, h⟩ : ℂ) else 0

lemma extC_of_mem (χ : borel F →* ℂˣ) {y : GL (Fin 2) F} (h : y ∈ borel F) : extC χ y = χ ⟨y, h⟩ := by
  simp [extC, h]

lemma extC_of_not_mem (χ : borel F →* ℂˣ) {y : GL (Fin 2) F} (h : y ∉ borel F) : extC χ y = 0 := by
  simp [extC, h]

lemma extC_mul_left (χ : borel F →* ℂˣ) {t : GL (Fin 2) F} (ht : t ∈ borel F) (h : GL (Fin 2) F) :
    extC χ (t * h) = χ ⟨t, ht⟩ * extC χ h := by
  by_cases hh : h ∈ borel F
  · rw [extC_of_mem χ (mul_mem ht hh), extC_of_mem χ hh, ← Units.val_mul, ← map_mul]
    rfl
  · have : t * h ∉ borel F := fun h' => hh (by simpa using mul_mem (inv_mem ht) h')
    rw [extC_of_not_mem χ this, extC_of_not_mem χ hh, mul_zero]

lemma extC_mul_right (χ : borel F →* ℂˣ) {t : GL (Fin 2) F} (ht : t ∈ borel F) (h : GL (Fin 2) F) :
    extC χ (h * t) = extC χ h * χ ⟨t, ht⟩ := by
  by_cases hh : h ∈ borel F
  · rw [extC_of_mem χ (mul_mem hh ht), extC_of_mem χ hh, ← Units.val_mul, ← map_mul]
    rfl
  · have : h * t ∉ borel F := fun h' => hh (by simpa using mul_mem h' (inv_mem ht))
    rw [extC_of_not_mem χ this, extC_of_not_mem χ hh, zero_mul]

lemma character_lineRep (χ : borel F →* ℂˣ) (b : borel F) : (lineRep χ).character b = χ b := by
  simp [Representation.character, lineRep]

lemma charExt_lineRep (χ : borel F →* ℂˣ) : charExt (borel F) (lineRep χ) = extC χ := by
  funext y
  by_cases h : y ∈ borel F
  · simp [charExt, extC, h, character_lineRep]
  · simp [charExt, extC, h]

noncomputable instance invertible_card_borel : Invertible (Nat.card (borel F) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

lemma character_principalSeries (l₁ l₂ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) :
    (principalSeries l₁ l₂).character g =
      (Nat.card (borel F) : ℂ)⁻¹ * ∑ x : GL (Fin 2) F, extC (borelChar l₁ l₂) (x * g * x⁻¹) := by
  rw [character_Ind_averaged, charExt_lineRep, invOf_eq_inv]

/-- The Mackey-type formula for the inner product of two principal series characters. -/
theorem hermitianPairing_principalSeries (l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ) :
    hermitianPairing (principalSeries l₁ l₂).character (principalSeries l₁' l₂').character =
      ((Nat.card (borel F) : ℂ)⁻¹) ^ 2 * ∑ u : GL (Fin 2) F, ∑ h : GL (Fin 2) F,
        extC (borelChar l₁ l₂) h * conj (extC (borelChar l₁' l₂') (u * h * u⁻¹)) := by
  simp only [hermitianPairing, character_principalSeries, map_mul, map_inv₀, Complex.conj_natCast]
  have hG : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp_rw [mul_mul_mul_comm _ (∑ x : GL (Fin 2) F, _) _ (conj _), ← Finset.mul_sum]
  rw [sum_conjAvg_mul_conj, ← Nat.card_eq_fintype_card]
  field_simp

/-! ### The double cosets -/

lemma borelChar_apply (l₁ l₂ : Fˣ →* ℂˣ) (b : borel F) :
    (borelChar l₁ l₂ b : ℂ) = l₁ (Units.mk0 _ (borel_diag_ne_zero b.2).1) *
      l₂ (Units.mk0 _ (borel_diag_ne_zero b.2).2) := by
  simp [borelChar, borelEquiv]

lemma borelChar_apply' (l₁ l₂ : Fˣ →* ℂˣ) {y : GL (Fin 2) F} (hy : y ∈ borel F) :
    (borelChar l₁ l₂ ⟨y, hy⟩ : ℂ) = l₁ (Units.mk0 ((y : Matrix (Fin 2) (Fin 2) F) 0 0) (borel_diag_ne_zero hy).1) *
      l₂ (Units.mk0 ((y : Matrix (Fin 2) (Fin 2) F) 1 1) (borel_diag_ne_zero hy).2) :=
  borelChar_apply l₁ l₂ ⟨y, hy⟩

/-- For `u⁻¹ ∉ B` and `h ∈ B` with `u h u⁻¹ ∈ B`, the upper-left entry of `u h u⁻¹` is the lower-right
entry of `h` (and conversely, by the determinant). -/
lemma conj_diag_of_not_mem {u h : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F) (hh : h ∈ borel F)
    (hM : u * h * u⁻¹ ∈ borel F) :
    ((u * h * u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
      ((u * h * u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  set M := u * h * u⁻¹ with hMdef
  have hid : u⁻¹ * M = h * u⁻¹ := by rw [hMdef]; group
  have hid' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hid
  simp only [Units.val_mul] at hid'
  have e10 := congrFun (congrFun hid' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e10
  rw [mem_borel.1 hM, mem_borel.1 hh] at e10
  have hc : ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := hu
  have h1 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have : ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((M : Matrix (Fin 2) (Fin 2) F) 0 0 - (h : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e10
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc)
  refine ⟨h1, ?_⟩
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = (h : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hMdef]
    simp only [Units.val_mul, Matrix.det_mul]
    have : (u : Matrix (Fin 2) (Fin 2) F).det * ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    linear_combination (h : Matrix (Fin 2) (Fin 2) F).det * this
  rw [Matrix.det_fin_two, Matrix.det_fin_two, mem_borel.1 hM, mem_borel.1 hh, h1] at hdet
  have hd := (borel_diag_ne_zero hh).2
  have : (h : Matrix (Fin 2) (Fin 2) F) 1 1 *
      ((M : Matrix (Fin 2) (Fin 2) F) 1 1 - (h : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
    linear_combination hdet
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hd)

/-- For `u⁻¹ ∉ B` and nonzero `x, y`, there is `t ∈ B` with diagonal `(x, y)` and `u t u⁻¹ ∈ B`. -/
lemma exists_twist {u : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F) (x y : Fˣ) :
    ∃ t : GL (Fin 2) F, t ∈ borel F ∧ u * t * u⁻¹ ∈ borel F ∧
      (t : Matrix (Fin 2) (Fin 2) F) 0 0 = x ∧ (t : Matrix (Fin 2) (Fin 2) F) 1 1 = y := by
  set w : Matrix (Fin 2) (Fin 2) F := ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hw
  have hc : w 1 0 ≠ 0 := hu
  set β : F := ((y : F) - x) * w 0 0 / w 1 0 with hβ
  let T : Matrix (Fin 2) (Fin 2) F := !![(x : F), β; 0, (y : F)]
  have hT : IsUnit T.det := by simp [T, Matrix.det_fin_two]
  refine ⟨GeneralLinearGroup.mk'' T hT, by simp [mem_borel, coe_mk'', T], ?_, by simp [coe_mk'', T],
    by simp [coe_mk'', T]⟩
  rw [mem_borel]
  have hu' : (u : Matrix (Fin 2) (Fin 2) F) = w⁻¹ := by
    rw [hw, GeneralLinearGroup.coe_inv, Matrix.inv_inv_of_invertible]
  have hdet : w.det ≠ 0 := by
    rw [hw]; exact (Matrix.isUnit_iff_isUnit_det _).1 (u⁻¹).isUnit |>.ne_zero
  have hM : ((u * GeneralLinearGroup.mk'' T hT * u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      w⁻¹ * T * w := by
    rw [Units.val_mul, Units.val_mul, coe_mk'', ← hw, hu']
  rw [hM, Matrix.inv_def, Matrix.adjugate_fin_two]
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, T, hβ]
  simp [Matrix.det_fin_two] at hdet ⊢
  field_simp
  ring

/-! ### Evaluating the inner sums -/

/-- The inner sum for `u ∈ B`. -/
lemma inner_sum_of_mem (χ χ' : borel F →* ℂˣ) {u : GL (Fin 2) F} (hu : u ∈ borel F) :
    ∑ h : GL (Fin 2) F, extC χ h * conj (extC χ' (u * h * u⁻¹)) =
      ∑ h : GL (Fin 2) F, extC χ h * conj (extC χ' h) := by
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [extC_mul_right χ' (inv_mem hu), extC_mul_left χ' hu]
  have : (χ' ⟨u, hu⟩ : ℂ) * (χ' ⟨u⁻¹, inv_mem hu⟩ : ℂ) = 1 := by
    have h1 : (⟨u, hu⟩ * ⟨u⁻¹, inv_mem hu⟩ : borel F) = 1 := Subtype.ext (mul_inv_cancel u)
    rw [← Units.val_mul, ← map_mul, h1, map_one, Units.val_one]
  rw [show (χ' ⟨u, hu⟩ : ℂ) * extC χ' h * (χ' ⟨u⁻¹, inv_mem hu⟩ : ℂ) = extC χ' h by
    rw [mul_comm (χ' ⟨u, hu⟩ : ℂ), mul_assoc, this, mul_one]]

lemma sum_extC_mul_conj_self (χ : borel F →* ℂˣ) :
    ∑ h : GL (Fin 2) F, extC χ h * conj (extC χ h) = Nat.card (borel F) := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun h => h ∈ borel F)]
  have h2 : ∑ h : {h : GL (Fin 2) F // h ∉ borel F}, extC χ h * conj (extC χ h) = 0 :=
    Finset.sum_eq_zero fun h _ => by rw [extC_of_not_mem χ h.2, zero_mul]
  rw [h2, add_zero]
  have h1 : ∀ h : {h : GL (Fin 2) F // h ∈ borel F}, extC χ h * conj (extC χ h) = 1 := fun h => by
    rw [extC_of_mem χ h.2, conj_hom_mul_self]
  rw [Finset.sum_congr rfl fun h _ => h1 h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

lemma sum_extC_mul_conj_of_ne (χ χ' : borel F →* ℂˣ) (hne : χ ≠ χ') :
    ∑ h : GL (Fin 2) F, extC χ h * conj (extC χ' h) = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, χ t ≠ χ' t := by
    by_contra h; push Not at h; exact hne (MonoidHom.ext h)
  refine sum_eq_zero_of_mul_left (t : GL (Fin 2) F) ((χ t : ℂ) * conj (χ' t : ℂ)) ?_ fun h => ?_
  · intro h1
    apply ht
    have h2 := conj_hom_mul_self χ' t
    apply Units.ext
    calc (χ t : ℂ) = (χ t : ℂ) * conj (χ' t : ℂ) * (χ' t : ℂ) := by
          rw [mul_assoc, mul_comm (conj _), conj_hom_mul_self, mul_one]
      _ = (χ' t : ℂ) := by rw [h1, one_mul]
  · rw [extC_mul_left χ t.2, extC_mul_left χ' t.2, map_mul]
    ring

/-- The inner sum for `u⁻¹ ∉ B`, when the pair `(λ₁, λ₂)` is not the swap of `(λ₁', λ₂')`. -/
lemma inner_sum_of_not_mem (l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ) {u : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F)
    (hne : ¬ (l₁ = l₂' ∧ l₂ = l₁')) :
    ∑ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₁' l₂') (u * h * u⁻¹)) = 0 := by
  have key : ∃ x y : Fˣ, (l₁ x : ℂ) * l₂ y * conj ((l₁' y : ℂ) * l₂' x) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    constructor
    · ext x
      have := hall x 1
      simp only [map_one, Units.val_one, mul_one, one_mul] at this
      have h2 := conj_hom_mul_self l₂' x
      calc (l₁ x : ℂ) = (l₁ x : ℂ) * conj (l₂' x : ℂ) * (l₂' x : ℂ) := by
            rw [mul_assoc, mul_comm (conj _), h2, mul_one]
        _ = _ := by rw [this, one_mul]
    · ext y
      have := hall 1 y
      simp only [map_one, Units.val_one, mul_one, one_mul] at this
      have h2 := conj_hom_mul_self l₁' y
      calc (l₂ y : ℂ) = (l₂ y : ℂ) * conj (l₁' y : ℂ) * (l₁' y : ℂ) := by
            rw [mul_assoc, mul_comm (conj _), h2, mul_one]
        _ = _ := by rw [this, one_mul]
  obtain ⟨x, y, hxy⟩ := key
  obtain ⟨t, htB, htM, ht0, ht1⟩ := exists_twist hu x y
  have hdiag := conj_diag_of_not_mem hu htB htM
  refine sum_eq_zero_of_mul_left t _ hxy fun h => ?_
  rw [extC_mul_left _ htB, show u * (t * h) * u⁻¹ = (u * t * u⁻¹) * (u * h * u⁻¹) by group,
    extC_mul_left _ htM, map_mul, borelChar_apply' _ _ htB, borelChar_apply' _ _ htM]
  have e1 : Units.mk0 _ (borel_diag_ne_zero htB).1 = x := Units.ext ht0
  have e2 : Units.mk0 _ (borel_diag_ne_zero htB).2 = y := Units.ext ht1
  have e3 : Units.mk0 _ (borel_diag_ne_zero htM).1 = y := Units.ext (hdiag.1.trans ht1)
  have e4 : Units.mk0 _ (borel_diag_ne_zero htM).2 = x := Units.ext (hdiag.2.trans ht0)
  rw [e1, e2, e3, e4]
  ring

/-- For the swapped pair, every term of the inner sum for `u⁻¹ ∉ B` is `0` or `1`, and the term at `h = 1` is
`1`; so the inner sum is a positive natural number. -/
lemma inner_sum_swap_eq (l₁ l₂ : Fˣ →* ℂˣ) {u : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F) :
    ∑ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₂ l₁) (u * h * u⁻¹)) =
      (Finset.univ.filter fun h : GL (Fin 2) F => h ∈ borel F ∧ u * h * u⁻¹ ∈ borel F).card := by
  have hterm : ∀ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₂ l₁) (u * h * u⁻¹)) =
      if h ∈ borel F ∧ u * h * u⁻¹ ∈ borel F then 1 else 0 := by
    intro h
    split_ifs with hh
    · rw [extC_of_mem _ hh.1, extC_of_mem _ hh.2, borelChar_apply' _ _ hh.1, borelChar_apply' _ _ hh.2]
      have hdiag := conj_diag_of_not_mem hu hh.1 hh.2
      have e3 : Units.mk0 _ (borel_diag_ne_zero hh.2).1 = Units.mk0 _ (borel_diag_ne_zero hh.1).2 :=
        Units.ext hdiag.1
      have e4 : Units.mk0 _ (borel_diag_ne_zero hh.2).2 = Units.mk0 _ (borel_diag_ne_zero hh.1).1 :=
        Units.ext hdiag.2
      rw [e3, e4, map_mul, conj_hom_eq_inv, conj_hom_eq_inv, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val]
      have ha : (l₁ (Units.mk0 _ (borel_diag_ne_zero hh.1).1) : ℂ) ≠ 0 := Units.ne_zero _
      have hb : (l₂ (Units.mk0 _ (borel_diag_ne_zero hh.1).2) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp
    · push Not at hh
      by_cases h1 : h ∈ borel F
      · rw [extC_of_not_mem _ (hh h1), map_zero, mul_zero]
      · rw [extC_of_not_mem _ h1, zero_mul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_boole]

lemma inner_sum_swap (l₁ l₂ : Fˣ →* ℂˣ) {u : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F) :
    ∃ n : ℕ, 0 < n ∧
      ∑ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₂ l₁) (u * h * u⁻¹)) = n :=
  ⟨_, Finset.card_pos.2 ⟨1, by simp [one_mem]⟩, inner_sum_swap_eq l₁ l₂ hu⟩

/-! ### The theorem -/

lemma borelChar_injective {l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ} (h : borelChar l₁ l₂ = borelChar (F := F) l₁' l₂') :
    l₁ = l₁' ∧ l₂ = l₂' := by
  constructor
  · ext x
    have := congrArg (fun χ : borel F →* ℂˣ => (χ (borelEquiv.symm (x, 1, 0)) : ℂ)) h
    simpa [borelChar, borelEquiv] using this
  · ext y
    have := congrArg (fun χ : borel F →* ℂˣ => (χ (borelEquiv.symm (1, y, 0)) : ℂ)) h
    simpa [borelChar, borelEquiv] using this

/-- The pairing splits into the contribution of `B` and that of the complement. -/
lemma hermitianPairing_principalSeries_split (l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ) :
    hermitianPairing (principalSeries l₁ l₂).character (principalSeries l₁' l₂').character =
      ((Nat.card (borel F) : ℂ)⁻¹) ^ 2 * ((Nat.card (borel F) : ℂ) *
        ∑ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₁' l₂') h) +
        ∑ u : {u : GL (Fin 2) F // u ∉ borel F}, ∑ h : GL (Fin 2) F,
          extC (borelChar l₁ l₂) h * conj (extC (borelChar l₁' l₂') ((u : GL (Fin 2) F) * h * (u : GL (Fin 2) F)⁻¹))) := by
  rw [hermitianPairing_principalSeries, ← Fintype.sum_subtype_add_sum_subtype (fun u => u ∈ borel F)]
  congr 2
  rw [Finset.sum_congr rfl fun u _ => inner_sum_of_mem _ _ u.2, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem hermitianPairing_principalSeries_eq_zero {l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ}
    (h1 : ¬ (l₁ = l₁' ∧ l₂ = l₂')) (h2 : ¬ (l₁ = l₂' ∧ l₂ = l₁')) :
    hermitianPairing (principalSeries l₁ l₂).character (principalSeries (F := F) l₁' l₂').character = 0 := by
  rw [hermitianPairing_principalSeries_split,
    sum_extC_mul_conj_of_ne _ _ fun h => h1 (borelChar_injective h),
    Finset.sum_eq_zero fun u _ => inner_sum_of_not_mem l₁ l₂ l₁' l₂'
      (fun hu => u.2 (by simpa using inv_mem hu)) h2]
  simp

theorem hermitianPairing_principalSeries_self {l₁ l₂ : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) :
    hermitianPairing (principalSeries l₁ l₂).character (principalSeries (F := F) l₁ l₂).character = 1 := by
  rw [hermitianPairing_principalSeries_split, sum_extC_mul_conj_self,
    Finset.sum_eq_zero fun u _ => inner_sum_of_not_mem l₁ l₂ l₁ l₂
      (fun hu => u.2 (by simpa using inv_mem hu)) (fun h => hne h.1)]
  have : (Nat.card (borel F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

theorem hermitianPairing_principalSeries_swap_ne_zero (l₁ l₂ : Fˣ →* ℂˣ) :
    hermitianPairing (principalSeries l₁ l₂).character (principalSeries (F := F) l₂ l₁).character ≠ 0 := by
  classical
  rw [hermitianPairing_principalSeries_split]
  have hB : (Nat.card (borel F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero hB)) ?_
  -- the first summand is a natural number, the second a sum of positive natural numbers over a nonempty set
  choose n hn hsum using fun u : {u : GL (Fin 2) F // u ∉ borel F} =>
    inner_sum_swap l₁ l₂ (u := u.1) (fun hu => u.2 (by simpa using inv_mem hu))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∑ h : GL (Fin 2) F, extC (borelChar l₁ l₂) h * conj (extC (borelChar l₂ l₁) h) = m := by
    by_cases he : borelChar l₁ l₂ = borelChar (F := F) l₂ l₁
    · rw [he, sum_extC_mul_conj_self]; exact ⟨_, rfl⟩
    · rw [sum_extC_mul_conj_of_ne _ _ he]; exact ⟨0, by simp⟩
  rw [hm, Finset.sum_congr rfl fun u _ => hsum u]
  have wB : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by simp [Matrix.det_fin_two]
  let w : GL (Fin 2) F := GeneralLinearGroup.mk'' !![0, 1; 1, 0] (isUnit_iff_ne_zero.2 wB)
  have hw : w ∉ borel F := by simp [mem_borel, w, coe_mk'']
  have hpos : 0 < ∑ u : {u : GL (Fin 2) F // u ∉ borel F}, n u :=
    Finset.sum_pos (fun u _ => hn u) ⟨⟨w, hw⟩, Finset.mem_univ _⟩
  intro h0
  have : ((Nat.card (borel F) * m + ∑ u : {u : GL (Fin 2) F // u ∉ borel F}, n u : ℕ) : ℂ) = 0 := by
    push_cast; exact h0
  have := Nat.cast_eq_zero.1 this
  omega

/-- **Etingof et al., Theorem 4.71 (irreducibility).** For a finite field `F` and characters `λ₁ ≠ λ₂` of
`F^×`, the principal series representation `V_{λ₁,λ₂} = Ind_B^G C_λ` of `GL_2(F)` is irreducible. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem isIrreducible_principalSeries {l₁ l₂ : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) :
    IsIrreducible (principalSeries (F := F) l₁ l₂) :=
  isIrreducible_of_hermitianPairing_self_eq_one _ (hermitianPairing_principalSeries_self hne)

/-- **Etingof et al., Theorem 4.71 (isomorphisms).** For characters `λ₁ ≠ λ₂` and `λ₁' ≠ λ₂'` of `F^×`, the
principal series `V_{λ₁,λ₂}` and `V_{λ₁',λ₂'}` are isomorphic if and only if `{λ₁, λ₂} = {λ₁', λ₂'}` as
unordered pairs. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem nonempty_equiv_principalSeries_iff {l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) (hne' : l₁' ≠ l₂') :
    Nonempty (Representation.Equiv (principalSeries (F := F) l₁ l₂) (principalSeries l₁' l₂')) ↔
      (l₁ = l₁' ∧ l₂ = l₂') ∨ (l₁ = l₂' ∧ l₂ = l₁') := by
  constructor
  · rintro ⟨e⟩
    by_contra h
    push Not at h
    have hc := Representation.char_iso e
    have h0 := hermitianPairing_principalSeries_eq_zero (F := F) (l₁ := l₁) (l₂ := l₂) (l₁' := l₁')
      (l₂' := l₂') (fun h' => h.1 h'.1 h'.2) (fun h' => h.2 h'.1 h'.2)
    rw [← hc, hermitianPairing_principalSeries_self hne] at h0
    exact one_ne_zero h0
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Representation.Equiv.refl _⟩
    · haveI := isIrreducible_principalSeries (F := F) hne
      haveI := isIrreducible_principalSeries (F := F) hne'
      have h1 := hermitianPairing_irreducible (principalSeries (F := F) l₁ l₂) (principalSeries l₂ l₁)
      have h2 := hermitianPairing_principalSeries_swap_ne_zero (F := F) l₁ l₂
      rw [h1] at h2
      split_ifs at h2 with hh
      · obtain ⟨e⟩ := hh
        exact ⟨e.symm⟩
      · exact absurd rfl h2

/-! ### The case `λ₁ = λ₂ = μ` -/

/-- With `w = u⁻¹`, an element `h ∈ B` with `u h u⁻¹ ∈ B` satisfies `w₁₀ h₀₁ = w₀₀ (h₁₁ - h₀₀)`. -/
lemma conj_offdiag_of_not_mem {u h : GL (Fin 2) F} (hM : u * h * u⁻¹ ∈ borel F)
    (hdiag : ((u * h * u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 1) :
    ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 *
        ((h : Matrix (Fin 2) (Fin 2) F) 1 1 - (h : Matrix (Fin 2) (Fin 2) F) 0 0) := by
  set M := u * h * u⁻¹ with hMdef
  have hid : u⁻¹ * M = h * u⁻¹ := by rw [hMdef]; group
  have hid' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hid
  simp only [Units.val_mul] at hid'
  have e00 := congrFun (congrFun hid' 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00
  rw [mem_borel.1 hM, hdiag] at e00
  linear_combination -e00

/-- For `u⁻¹ ∉ B`, the subgroup `B ∩ u⁻¹ B u` has `(q - 1)²` elements (it is parametrised by its diagonal). -/
lemma card_stab {u : GL (Fin 2) F} (hu : u⁻¹ ∉ borel F) :
    (Finset.univ.filter fun h : GL (Fin 2) F => h ∈ borel F ∧ u * h * u⁻¹ ∈ borel F).card =
      (Fintype.card F - 1) ^ 2 := by
  have hc : ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := hu
  rw [show (Fintype.card F - 1) ^ 2 = (Finset.univ : Finset (Fˣ × Fˣ)).card by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_units]; ring]
  refine Finset.card_bij (fun h hh => (Units.mk0 _ (borel_diag_ne_zero (Finset.mem_filter.1 hh).2.1).1,
    Units.mk0 _ (borel_diag_ne_zero (Finset.mem_filter.1 hh).2.1).2)) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro h₁ hh₁ h₂ hh₂ heq
    have hh₁' := (Finset.mem_filter.1 hh₁).2
    have hh₂' := (Finset.mem_filter.1 hh₂).2
    simp only [Prod.mk.injEq] at heq
    have a00 : (h₁ : Matrix (Fin 2) (Fin 2) F) 0 0 = (h₂ : Matrix (Fin 2) (Fin 2) F) 0 0 :=
      congrArg Units.val heq.1
    have a11 : (h₁ : Matrix (Fin 2) (Fin 2) F) 1 1 = (h₂ : Matrix (Fin 2) (Fin 2) F) 1 1 :=
      congrArg Units.val heq.2
    have o1 := conj_offdiag_of_not_mem hh₁'.2 (conj_diag_of_not_mem hu hh₁'.1 hh₁'.2).1
    have o2 := conj_offdiag_of_not_mem hh₂'.2 (conj_diag_of_not_mem hu hh₂'.1 hh₂'.2).1
    have a01 : (h₁ : Matrix (Fin 2) (Fin 2) F) 0 1 = (h₂ : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      rw [a00, a11] at o1
      exact mul_left_cancel₀ hc (o1.trans o2.symm)
    have a10 : (h₁ : Matrix (Fin 2) (Fin 2) F) 1 0 = (h₂ : Matrix (Fin 2) (Fin 2) F) 1 0 :=
      (mem_borel.1 hh₁'.1).trans (mem_borel.1 hh₂'.1).symm
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact a00
    · exact a01
    · exact a10
    · exact a11
  · rintro ⟨x, y⟩ _
    obtain ⟨t, htB, htM, ht0, ht1⟩ := exists_twist hu x y
    refine ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, htB, htM⟩, ?_⟩
    ext
    · exact ht0
    · exact ht1

/-- For `λ₁ = λ₂ = μ` the character of the principal series has norm `2`. -/
theorem hermitianPairing_principalSeries_diag (μ : Fˣ →* ℂˣ) :
    hermitianPairing (principalSeries μ μ).character (principalSeries (F := F) μ μ).character = 2 := by
  have hS : ∀ u : {u : GL (Fin 2) F // u ∉ borel F},
      ∑ h : GL (Fin 2) F, extC (borelChar μ μ) h * conj (extC (borelChar μ μ) ((u : GL (Fin 2) F) * h *
        (u : GL (Fin 2) F)⁻¹)) = (((Fintype.card F - 1) ^ 2 : ℕ) : ℂ) := fun u => by
    have hu : (u : GL (Fin 2) F)⁻¹ ∉ borel F := fun hu => u.2 (by simpa using inv_mem hu)
    rw [inner_sum_swap_eq μ μ hu, card_stab hu]
  rw [hermitianPairing_principalSeries_split, sum_extC_mul_conj_self, Finset.sum_congr rfl fun u _ => hS u,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card (α := {x // x ∈ borel F})]
  have hq : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  have hG : Nat.card (GL (Fin 2) F) = Nat.card (borel F) * (Nat.card F + 1) := by
    rw [← index_borel, Subgroup.card_mul_index]
  have key : (Nat.card (GL (Fin 2) F) - Nat.card (borel F)) * (Fintype.card F - 1) ^ 2 =
      Nat.card (borel F) * Nat.card (borel F) := by
    rw [hG, hq, show Nat.card (borel F) * (Nat.card F + 1) - Nat.card (borel F) =
      Nat.card (borel F) * Nat.card F by rw [mul_add, mul_one, Nat.add_sub_cancel], mul_assoc]
    congr 1
    rw [card_borel]
    ring
  rw [← Nat.cast_mul (Nat.card (GL (Fin 2) F) - Nat.card (borel F)), key, Nat.cast_mul]
  have hB : (Nat.card (borel F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  ring

/-- The character `g ↦ μ(det g)` of `GL_2(F)`. -/
noncomputable def detCharC (μ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) : ℂ := μ (GeneralLinearGroup.det g)

lemma detCharC_mul (μ : Fˣ →* ℂˣ) (g h : GL (Fin 2) F) : detCharC μ (g * h) = detCharC μ g * detCharC μ h := by
  simp [detCharC, map_mul]

lemma extC_borelChar_diag (μ : Fˣ →* ℂˣ) {h : GL (Fin 2) F} (hh : h ∈ borel F) :
    extC (borelChar μ μ) h = detCharC μ h := by
  rw [extC_of_mem _ hh, borelChar_apply' _ _ hh, detCharC, ← Units.val_mul, ← map_mul]
  congr 2
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, mem_borel.1 hh]

lemma hermitianPairing_conj (f₁ f₂ : GL (Fin 2) F → ℂ) :
    hermitianPairing f₁ f₂ = conj (hermitianPairing f₂ f₁) := by
  simp only [hermitianPairing, map_mul, map_inv₀, Complex.conj_natCast, map_sum, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun g _ => mul_comm _ _

lemma hermitianPairing_detCharC (μ : Fˣ →* ℂˣ) : hermitianPairing (detCharC (F := F) μ) (detCharC μ) = 1 := by
  simp only [hermitianPairing, detCharC, conj_hom_mul_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Nat.card_eq_fintype_card]
  have hG : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

lemma hermitianPairing_principalSeries_detCharC (μ : Fˣ →* ℂˣ) :
    hermitianPairing (principalSeries (F := F) μ μ).character (detCharC μ) = 1 := by
  have hclass : ∀ x g : GL (Fin 2) F, detCharC μ (x * g * x⁻¹) = detCharC μ g := by
    intro x g
    rw [detCharC_mul, detCharC_mul, mul_comm (detCharC μ x), mul_assoc, ← detCharC_mul, mul_inv_cancel]
    simp [detCharC]
  have key : ∀ x : GL (Fin 2) F, ∑ g, extC (borelChar μ μ) (x * g * x⁻¹) * conj (detCharC μ g) =
      ∑ h, extC (borelChar μ μ) h * conj (detCharC μ h) := by
    intro x
    refine Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hclass]
  have hsum : ∑ h, extC (borelChar μ μ) h * conj (detCharC μ h) = Nat.card (borel F) := by
    rw [← sum_extC_mul_conj_self (borelChar μ μ)]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h ∈ borel F
    · rw [extC_borelChar_diag μ hh]
    · rw [extC_of_not_mem _ hh, zero_mul, zero_mul]
  simp only [hermitianPairing, character_principalSeries]
  have e1 : ∀ g, ((Nat.card (borel F) : ℂ)⁻¹ * ∑ x, extC (borelChar μ μ) (x * g * x⁻¹)) * conj (detCharC μ g) =
      (Nat.card (borel F) : ℂ)⁻¹ * ∑ x, extC (borelChar μ μ) (x * g * x⁻¹) * conj (detCharC μ g) := by
    intro g; rw [mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun g _ => e1 g, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => key x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum,
    ← Nat.card_eq_fintype_card]
  have hG : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hB : (Nat.card (borel F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-- The function `x ↦ μ(det x)`, a vector of `V_{μ,μ}`. -/
noncomputable def detVec (μ : Fˣ →* ℂˣ) : coindV (borel F).subtype (lineRep (borelChar μ μ)) :=
  ⟨detCharC μ, by
    intro b x
    show detCharC μ ((b : GL (Fin 2) F) * x) = (borelChar μ μ b : ℂ) • detCharC μ x
    rw [detCharC_mul, smul_eq_mul, ← extC_borelChar_diag μ b.2, extC_of_mem _ b.2]⟩

lemma principalSeries_detVec (μ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) :
    principalSeries μ μ g (detVec μ) = detCharC μ g • detVec μ := by
  apply Subtype.ext
  funext x
  show detCharC μ (x * g) = detCharC μ g * detCharC μ x
  rw [detCharC_mul, mul_comm]

lemma detVec_ne_zero (μ : Fˣ →* ℂˣ) : detVec (F := F) μ ≠ 0 := by
  intro h
  have := congrArg (fun f : coindV (borel F).subtype (lineRep (borelChar μ μ)) => (f : GL (Fin 2) F → ℂ) 1) h
  simp [detVec, detCharC] at this

/-- Subrepresentations of a principal series as additive groups: the ambient space is itself a submodule, so the
group structure is recovered from the complex module structure. -/
noncomputable instance subrepAddCommGroup (l₁ l₂ : Fˣ →* ℂˣ) (S : Subrepresentation (principalSeries (F := F) l₁ l₂)) :
    AddCommGroup S.toSubmodule :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The line spanned by `x ↦ μ(det x)`, a subrepresentation of `V_{μ,μ}` isomorphic to `C_μ`. -/
noncomputable def detLine (μ : Fˣ →* ℂˣ) : Subrepresentation (principalSeries (F := F) μ μ) where
  toSubmodule := Submodule.span ℂ {detVec μ}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, principalSeries_detVec, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

lemma detLine_apply (μ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) {v} (hv : v ∈ (detLine μ).toSubmodule) :
    principalSeries μ μ g v = detCharC μ g • v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [map_smul, principalSeries_detVec, smul_comm]

lemma finrank_detLine (μ : Fˣ →* ℂˣ) : finrank ℂ (detLine (F := F) μ).toSubmodule = 1 :=
  finrank_span_singleton (detVec_ne_zero μ)

lemma character_detLine (μ : Fˣ →* ℂˣ) : (detLine (F := F) μ).toRepresentation.character = detCharC μ := by
  funext g
  have : (detLine μ).toRepresentation g = detCharC μ g • LinearMap.id :=
    LinearMap.ext fun v => Subtype.ext (detLine_apply μ g v.2)
  rw [Representation.character, this, map_smul, LinearMap.trace_id, finrank_detLine]
  simp

/-- **Etingof et al., Theorem 4.71 (the case `λ₁ = λ₂ = μ`).** The principal series `V_{μ,μ}` is the direct sum of
the line `C_μ` (spanned by `x ↦ μ(det x)`, on which `g` acts by `μ(det g)`) and an irreducible representation
`W_μ` of dimension `q`. -/
@[kb "etingof2011" "Theorem 4.71, p. 71"]
theorem principalSeries_diag_decomposition (μ : Fˣ →* ℂˣ) :
    ∃ S W : Subrepresentation (principalSeries (F := F) μ μ), IsCompl S W ∧
      finrank ℂ S.toSubmodule = 1 ∧
      (∀ g : GL (Fin 2) F, ∀ v ∈ S.toSubmodule,
        principalSeries μ μ g v = (μ (GeneralLinearGroup.det g) : ℂ) • v) ∧
      IsIrreducible W.toRepresentation ∧ finrank ℂ W.toSubmodule = Nat.card F := by
  obtain ⟨W, hW⟩ := ComplementedLattice.exists_isCompl (detLine (F := F) μ)
  refine ⟨detLine μ, W, hW, finrank_detLine μ, fun g v hv => detLine_apply μ g hv, ?_, ?_⟩
  · apply isIrreducible_of_hermitianPairing_self_eq_one
    have hchar : (principalSeries (F := F) μ μ).character =
        (detLine μ).toRepresentation.character + W.toRepresentation.character := by
      funext g
      rw [← char_iso (prodEquivOfIsCompl (detLine μ) W hW), Pi.add_apply, char_prod]
    rw [character_detLine] at hchar
    have h2 := hermitianPairing_principalSeries_diag (F := F) μ
    have h1 := hermitianPairing_principalSeries_detCharC (F := F) μ
    have h1' : hermitianPairing (detCharC μ) (principalSeries (F := F) μ μ).character = 1 := by
      rw [hermitianPairing_conj, h1, map_one]
    have hψ := hermitianPairing_detCharC (F := F) μ
    rw [hchar] at h2 h1 h1'
    rw [hermitianPairing_add_left, hermitianPairing_add_right, hermitianPairing_add_right] at h2
    rw [hermitianPairing_add_left] at h1
    rw [hermitianPairing_add_right] at h1'
    linear_combination h2 - h1 - h1' + hψ
  · have h := Submodule.finrank_add_eq_of_isCompl (isCompl_toSubmodule hW)
    rw [finrank_detLine, finrank_principalSeries] at h
    omega

end UndergradKB.RepresentationTheory.GL2
