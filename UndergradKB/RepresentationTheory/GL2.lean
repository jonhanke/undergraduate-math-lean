import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import UndergradKB.RepresentationTheory.Induced
import UndergradKB.Common.Attr

/-! # The group GL_2(F_q) (Etingof et al., §4.24)

For a finite field `F` of cardinality `q` we record:

* the commutator subgroup of `GL_2(F)` is the kernel of `det` (Proposition 4.70), assuming `q > 3`;
* consequently the one-dimensional complex representations of `GL_2(F)` are exactly the characters
  `ξ ∘ det` for characters `ξ` of `F^×`, and there are `q - 1` of them (§4.24.2);
* the Borel subgroup `B` of upper triangular matrices has `(q-1)² q` elements and index `q + 1`;
  hence the principal series representation `Ind_B^G C_λ` has dimension `q + 1` (§4.24.3);
* sizes of some conjugacy classes (§4.24.1), computed through centralizer orders.
-/

universe u

namespace UndergradKB.RepresentationTheory.GL2

open Matrix

variable {F : Type u} [Field F]

/-! ## The commutator subgroup -/

/-- **Etingof et al., Proposition 4.70**: the commutator subgroup of `GL_2(F)` is the kernel of the
determinant, i.e. the image of `SL_2(F)`.  Hypothesis: some `a ≠ 0` with `a² ≠ 1` exists (equivalent to
`#F > 3`; for `F = F_2` the statement is false). -/
@[kb "etingof2011" "Proposition 4.70, p. 70"]
theorem commutator_GL2 (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator (GL (Fin 2) F) = (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
  obtain ⟨a, ha, ha2⟩ := h
  apply le_antisymm (Abelianization.commutator_le_ker _)
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.range_eq_map,
    ← SL2.commutator_eq_top ha ha2, commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

/-- The same statement, with the image of `SL_2(F)` in `GL_2(F)` named explicitly. -/
theorem commutator_GL2_eq_range (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator (GL (Fin 2) F) =
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
  rw [commutator_GL2 h, SpecialLinearGroup.range_toGL_eq_ker_det]

/-! ## One-dimensional representations -/

/-- Every character `ξ : F^× → ℂ^×` gives a one-dimensional representation `ξ ∘ det` of `GL_2(F)`. -/
def detChar (ξ : Fˣ →* ℂˣ) : GL (Fin 2) F →* ℂˣ := ξ.comp GeneralLinearGroup.det

/-- Distinct characters of `F^×` give distinct characters `ξ ∘ det`. -/
theorem detChar_injective :
    Function.Injective (fun ξ : Fˣ →* ℂˣ => (detChar ξ : GL (Fin 2) F →* ℂˣ)) := by
  intro ξ η h
  ext u
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.det_surjective (n := Fin 2) u
  have := DFunLike.congr_fun h g
  simp only [detChar, MonoidHom.comp_apply] at this
  rw [this]

/-- **Etingof et al., §4.24.2**: if the commutator subgroup of `GL_2(F)` is the kernel of `det`
(Proposition 4.70), then every one-dimensional representation of `GL_2(F)` is `ξ ∘ det` for a unique
character `ξ` of `F^×`. -/
@[kb "etingof2011" "§4.24.2, p. 70"]
theorem exists_unique_detChar (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) (φ : GL (Fin 2) F →* ℂˣ) :
    ∃! ξ : Fˣ →* ℂˣ, φ = detChar ξ := by
  have hker : (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker ≤ φ.ker := by
    rw [← commutator_GL2 h]
    exact Abelianization.commutator_le_ker φ
  have key : φ = detChar
      ((GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).liftOfSurjective
        GeneralLinearGroup.det_surjective ⟨φ, hker⟩) :=
    (MonoidHom.liftOfRightInverse_comp _ _ _ ⟨φ, hker⟩).symm
  exact ⟨_, key, fun η hη => detChar_injective (hη.symm.trans key)⟩

/-- The number of one-dimensional complex representations of `GL_2(F_q)` is `q - 1`, provided the
commutator subgroup is the kernel of `det`. -/
theorem card_homs_GL2 [Finite F] (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    Nat.card (GL (Fin 2) F →* ℂˣ) = Nat.card F - 1 := by
  have e : (Fˣ →* ℂˣ) ≃ (GL (Fin 2) F →* ℂˣ) :=
    Equiv.ofBijective detChar ⟨detChar_injective, fun φ =>
      (exists_unique_detChar h φ).exists.imp fun _ hξ => hξ.symm⟩
  rw [← Nat.card_congr e, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units]

/-! ## The Borel subgroup and the principal series -/

/-- The Borel subgroup of upper triangular matrices in `GL_2(F)`. -/
def borel (F : Type u) [Field F] : Subgroup (GL (Fin 2) F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [hg]

lemma mem_borel {g : GL (Fin 2) F} :
    g ∈ borel F ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

lemma borel_diag_ne_zero {g : GL (Fin 2) F} (hg : g ∈ borel F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  have h := (GeneralLinearGroup.det g).isUnit.ne_zero
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, mem_borel.1 hg] at h
  simp only [mul_zero, sub_zero] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

lemma coe_mk'' (A : Matrix (Fin 2) (Fin 2) F) (h : IsUnit A.det) :
    ((GeneralLinearGroup.mk'' A h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A := rfl

/-- Parametrisation of the Borel subgroup by (upper-left, lower-right, upper-right) entries. -/
noncomputable def borelEquiv : borel F ≃ Fˣ × Fˣ × F where
  toFun b := (Units.mk0 _ (borel_diag_ne_zero b.2).1, Units.mk0 _ (borel_diag_ne_zero b.2).2,
    (b.1 : Matrix (Fin 2) (Fin 2) F) 0 1)
  invFun x := ⟨GeneralLinearGroup.mk'' !![(x.1 : F), x.2.2; 0, (x.2.1 : F)] (by
      simp [Matrix.det_fin_two]), by
    simp [mem_borel]⟩
  left_inv b := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := mem_borel.1 b.2
    fin_cases i <;> fin_cases j <;> simp [this]
  right_inv x := by
    ext <;> simp

/-- The Borel subgroup of `GL_2(F_q)` has `(q-1)² q` elements. -/
lemma card_borel [Finite F] :
    Nat.card (borel F) = (Nat.card F - 1) ^ 2 * Nat.card F := by
  rw [Nat.card_congr borelEquiv, Nat.card_prod, Nat.card_prod, Nat.card_units]
  ring

/-- `|GL_2(F_q)| = (q²-1)(q²-q)`. -/
lemma card_GL2 [Finite F] :
    Nat.card (GL (Fin 2) F) = (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Fin.prod_univ_two]
  simp [Nat.card_eq_fintype_card]

/-- The Borel subgroup has index `q + 1` in `GL_2(F_q)`. -/
theorem index_borel [Finite F] : (borel F).index = Nat.card F + 1 := by
  have h1 := (borel F).card_mul_index
  rw [card_borel, card_GL2] at h1
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq
  rw [hr] at h1 ⊢
  have hpos : 0 < (1 + r) ^ 2 * (2 + r) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have e1 : 2 + r - 1 = 1 + r := by omega
  have e2 : (2 + r) ^ 2 - 1 = (1 + r) * (3 + r) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 + r) ^ 2 - (2 + r) = (1 + r) * (2 + r) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3] at h1
  rw [h1]
  ring

/-- The character `b ↦ λ₁(b₁₁) λ₂(b₂₂)` of the Borel subgroup. -/
noncomputable def borelChar (l₁ l₂ : Fˣ →* ℂˣ) : borel F →* ℂˣ where
  toFun b := l₁ (borelEquiv b).1 * l₂ (borelEquiv b).2.1
  map_one' := by
    have h : (borelEquiv (1 : borel F)).1 = 1 ∧ (borelEquiv (1 : borel F)).2.1 = 1 := by
      constructor <;> ext <;> simp [borelEquiv]
    rw [h.1, h.2, map_one, map_one, mul_one]
  map_mul' b c := by
    have h : (borelEquiv (b * c)).1 = (borelEquiv b).1 * (borelEquiv c).1 ∧
        (borelEquiv (b * c)).2.1 = (borelEquiv b).2.1 * (borelEquiv c).2.1 := by
      have hb := mem_borel.1 b.2
      have hc := mem_borel.1 c.2
      constructor <;> ext <;> simp [borelEquiv, Matrix.mul_apply, Fin.sum_univ_two, hb, hc]
    rw [h.1, h.2, map_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

/-- The one-dimensional complex representation `C_λ` of the Borel subgroup attached to a character. -/
noncomputable def lineRep (χ : borel F →* ℂˣ) : Representation ℂ (borel F) ℂ where
  toFun b := (χ b : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' b c := by ext; simp [mul_comm]

/-- The principal series representation `Ind_B^G C_λ` of `GL_2(F)` for the pair of characters
`(λ₁, λ₂)` of `F^×`. -/
noncomputable abbrev principalSeries (l₁ l₂ : Fˣ →* ℂˣ) :=
  Ind (borel F) (lineRep (borelChar l₁ l₂))

open Module in
/-- **Etingof et al., §4.24.3**: the principal series representation of `GL_2(F_q)` has
dimension `q + 1`. -/
@[kb "etingof2011" "§4.24.3 definition, p. 71"]
theorem finrank_principalSeries [Finite F] (l₁ l₂ : Fˣ →* ℂˣ) :
    finrank ℂ (Representation.coindV (borel F).subtype (lineRep (borelChar l₁ l₂))) =
      Nat.card F + 1 := by
  have : Finite (GL (Fin 2) F) := inferInstance
  rw [finrank_Ind, index_borel]
  simp

/-! ## Conjugacy class sizes -/

/-- In a finite group the size of the conjugacy class of `g` times the order of its centralizer is
the order of the group (orbit-stabilizer). -/
theorem ncard_conjugatesOf_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    (conjugatesOf g).ncard * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  rw [← Subgroup.index_centralizer_eq_ncard, mul_comm, Subgroup.card_mul_index]

/-- The matrix `[[a, b], [0, a]]` as an element of `GL_2(F)`. -/
noncomputable def upperUnit (a : Fˣ) (b : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mk'' !![(a : F), b; 0, (a : F)] (by simp [Matrix.det_fin_two])

/-- The diagonal matrix `diag(a, d)` as an element of `GL_2(F)`. -/
noncomputable def diagUnit (a d : Fˣ) : GL (Fin 2) F :=
  GeneralLinearGroup.mk'' !![(a : F), 0; 0, (d : F)] (by simp [Matrix.det_fin_two])

lemma upperUnit_injective : Function.Injective (fun p : Fˣ × F => (upperUnit p.1 p.2 : GL (Fin 2) F)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [upperUnit, coe_mk''] at h00 h01
  exact Prod.ext (Units.ext h00) h01

lemma diagUnit_injective : Function.Injective (fun p : Fˣ × Fˣ => (diagUnit p.1 p.2 : GL (Fin 2) F)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [diagUnit, coe_mk''] at h00 h11
  exact Prod.ext (Units.ext h00) (Units.ext h11)

/-- The scalar matrices are central: their class has one element, and the centralizer is everything. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_conjugatesOf_scalar (c : Fˣ) :
    (conjugatesOf (diagUnit c c : GL (Fin 2) F)).ncard = 1 := by
  have h : Subgroup.centralizer {(diagUnit c c : GL (Fin 2) F)} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Units.ext
    ext i j
    simp only [Units.val_mul, diagUnit, coe_mk'']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [← Subgroup.index_centralizer_eq_ncard, h, Subgroup.index_top]

/-- The centralizer of the parabolic element `[[x, 1], [0, x]]` consists of the matrices
`[[a, b], [0, a]]`. -/
lemma centralizer_upper (x : Fˣ) :
    (Subgroup.centralizer {(upperUnit x 1 : GL (Fin 2) F)} : Set (GL (Fin 2) F)) =
      Set.range (fun p : Fˣ × F => (upperUnit p.1 p.2 : GL (Fin 2) F)) := by
  ext h
  constructor
  · intro hh
    have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      (Subgroup.mem_centralizer_iff.1 hh _ (Set.mem_singleton _))
    have e00 := congrFun (congrFun e 0) 0
    have e01 := congrFun (congrFun e 0) 1
    simp [upperUnit, coe_mk'', Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    have hc : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e00
    have hd : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination e01
    have ha := (GeneralLinearGroup.det h).isUnit.ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hc, hd] at ha
    have ha' : (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0; apply ha; rw [h0]; ring
    refine ⟨(Units.mk0 _ ha', (h : Matrix (Fin 2) (Fin 2) F) 0 1), ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperUnit, coe_mk'', hc, hd]
  · rintro ⟨p, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Units.ext
    ext i j
    simp only [Units.val_mul, upperUnit, coe_mk'']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The centralizer of `diag(x, y)` with `x ≠ y` consists of the diagonal matrices. -/
lemma centralizer_diag {x y : Fˣ} (hxy : x ≠ y) :
    (Subgroup.centralizer {(diagUnit x y : GL (Fin 2) F)} : Set (GL (Fin 2) F)) =
      Set.range (fun p : Fˣ × Fˣ => (diagUnit p.1 p.2 : GL (Fin 2) F)) := by
  have hxy' : (x : F) - y ≠ 0 := sub_ne_zero.2 (fun h => hxy (Units.ext h))
  ext h
  constructor
  · intro hh
    have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
      (Subgroup.mem_centralizer_iff.1 hh _ (Set.mem_singleton _))
    have e01 := congrFun (congrFun e 0) 1
    have e10 := congrFun (congrFun e 1) 0
    simp [diagUnit, coe_mk'', Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    have hb : (h : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (h : Matrix (Fin 2) (Fin 2) F) 0 1 * ((x : F) - y) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hxy'
    have hc : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (h : Matrix (Fin 2) (Fin 2) F) 1 0 * ((x : F) - y) = 0 := by linear_combination -e10
      exact (mul_eq_zero.1 this).resolve_right hxy'
    have hdet := (GeneralLinearGroup.det h).isUnit.ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hb, hc] at hdet
    simp only [mul_zero, sub_zero] at hdet
    refine ⟨(Units.mk0 _ (left_ne_zero_of_mul hdet), Units.mk0 _ (right_ne_zero_of_mul hdet)), ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagUnit, coe_mk'', hb, hc]
  · rintro ⟨p, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Units.ext
    ext i j
    simp only [Units.val_mul, diagUnit, coe_mk'']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The centralizer of the parabolic element has `q (q - 1)` elements. -/
lemma card_centralizer_upper [Finite F] (x : Fˣ) :
    Nat.card (Subgroup.centralizer {(upperUnit x 1 : GL (Fin 2) F)}) =
      (Nat.card F - 1) * Nat.card F := by
  have h : Nat.card (Subgroup.centralizer {(upperUnit x 1 : GL (Fin 2) F)}) =
      Nat.card (Set.range (fun p : Fˣ × F => (upperUnit p.1 p.2 : GL (Fin 2) F))) := by
    rw [← centralizer_upper x]; rfl
  rw [h, Nat.card_range_of_injective upperUnit_injective, Nat.card_prod, Nat.card_units]

/-- The centralizer of a hyperbolic element has `(q - 1)²` elements. -/
lemma card_centralizer_diag [Finite F] {x y : Fˣ} (hxy : x ≠ y) :
    Nat.card (Subgroup.centralizer {(diagUnit x y : GL (Fin 2) F)}) = (Nat.card F - 1) ^ 2 := by
  have h : Nat.card (Subgroup.centralizer {(diagUnit x y : GL (Fin 2) F)}) =
      Nat.card (Set.range (fun p : Fˣ × Fˣ => (diagUnit p.1 p.2 : GL (Fin 2) F))) := by
    rw [← centralizer_diag hxy]; rfl
  rw [h, Nat.card_range_of_injective diagUnit_injective, Nat.card_prod, Nat.card_units]
  ring

/-- **Etingof et al., §4.24.1 (table)**: the conjugacy class of the parabolic element
`[[x, 1], [0, x]]` has `q² - 1` elements. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_conjugatesOf_parabolic [Finite F] (x : Fˣ) :
    (conjugatesOf (upperUnit x 1 : GL (Fin 2) F)).ncard = Nat.card F ^ 2 - 1 := by
  have h := ncard_conjugatesOf_mul_card_centralizer (upperUnit x 1 : GL (Fin 2) F)
  rw [card_centralizer_upper, card_GL2] at h
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq
  rw [hr] at h ⊢
  have hpos : 0 < (2 + r - 1) * (2 + r) := by
    have : 2 + r - 1 = 1 + r := by omega
    rw [this]; positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  have e1 : 2 + r - 1 = 1 + r := by omega
  have e2 : (2 + r) ^ 2 - 1 = (1 + r) * (3 + r) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 + r) ^ 2 - (2 + r) = (1 + r) * (2 + r) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3]

/-- **Etingof et al., §4.24.1 (table)**: the conjugacy class of the hyperbolic element `diag(x, y)`,
`x ≠ y`, has `q² + q` elements. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_conjugatesOf_hyperbolic [Finite F] {x y : Fˣ} (hxy : x ≠ y) :
    (conjugatesOf (diagUnit x y : GL (Fin 2) F)).ncard = Nat.card F ^ 2 + Nat.card F := by
  have h := ncard_conjugatesOf_mul_card_centralizer (diagUnit x y : GL (Fin 2) F)
  rw [card_centralizer_diag hxy, card_GL2] at h
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq
  rw [hr] at h ⊢
  have hpos : 0 < (2 + r - 1) ^ 2 := by
    have : 2 + r - 1 = 1 + r := by omega
    rw [this]; positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  have e1 : 2 + r - 1 = 1 + r := by omega
  have e2 : (2 + r) ^ 2 - 1 = (1 + r) * (3 + r) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (2 + r) ^ 2 - (2 + r) = (1 + r) * (2 + r) := Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, e3]
  ring

end UndergradKB.RepresentationTheory.GL2
