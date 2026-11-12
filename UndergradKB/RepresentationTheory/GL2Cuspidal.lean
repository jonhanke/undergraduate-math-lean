import Mathlib.FieldTheory.Finite.Basic
import UndergradKB.RepresentationTheory.GL2Classes
import UndergradKB.RepresentationTheory.GL2PrincipalSeries
import UndergradKB.RepresentationTheory.CharacterTables
import UndergradKB.Common.Attr

/-! # The complementary (cuspidal) series of `GL_2(F_q)` (Etingof et al., §4.24.4)

Let `F` be a finite field and fix a monic quadratic `x² - t x + n` without root in `F`; its companion matrix `C`
(`ellipticElt`) is an elliptic element of `G = GL_2(F)`.  The *nonsplit torus* `K` is the centralizer of `C` in `G`
(`torus`); it consists of the invertible matrices `a + b C`, so it is a model of `F_{q²}^×` acting on `F_{q²}`
by multiplication in the basis `1, C` (`mem_torus_iff`), and has `q² - 1` elements.

For a character `ν` of `K` the representation `Y_ν = Ind_K^G C_ν` (`torusInd`) has dimension `q² - q` and its
character is computed (`character_torusInd_*`): it is zero on parabolic and hyperbolic elements, equal to
`(q² - q) ν(z)` on a scalar `z`, and `ν(z) + ν(z^σ)` on an element `z` of `K` which is not scalar.  Here
`z^σ` is the adjugate `adjG z = det z · z⁻¹`, which on `K` is the non-trivial Galois conjugation of `F_{q²}`
over `F` (we work with this description and do not identify it with `z ↦ z^q`).  Since `Y_ν` has the same
character as `Y_{ν ∘ σ}`, the two representations are isomorphic (`nonempty_equiv_torusInd_comp_sigma`).

Lemma 4.72 and the conclusion of §4.24.4: for `ν` restricting to `α` on the scalars with `ν ∘ σ ≠ ν`, the class
function `cuspChar = χ_{W₁} χ_{V_{α,1}} - χ_{V_{α,1}} - χ_{Y_ν}` (with `χ_{W₁} = χ_{V_{1,1}} - 1`) is a virtual
character (`cuspChar_mem_virtualChars`), has norm one (`hermitianPairing_cuspChar`) and value `q - 1` at `1`
(`cuspChar_one`), hence is the character of an irreducible `(q-1)`-dimensional representation
(`exists_irrep_cuspidal`).  The norm is computed without class-by-class sums over the elliptic classes: the
parabolic and scalar classes are summed directly (`sum_class_function`), and the remaining terms are handled by
Frobenius reciprocity for `Y_ν` (`sum_mul_conj_torusInd`) and orthogonality on `K` (`sum_extT_adjG_mul_conj`).

Not proved here: that `σ` is the `q`-th power map on `K ≅ F_{q²}^×`, that `K` is cyclic, the count
`q(q-1)/2` of the pairs `{ν, ν^σ}` with `ν^σ ≠ ν` (each with its restriction `α`), the distinctness of the resulting
representations for distinct pairs, and the final count `q² - 1` of all irreducible representations.
-/

universe u

namespace UndergradKB.RepresentationTheory.GL2

open Matrix Representation Module ComplexConjugate

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-! ### Scalars and the adjugate on `G` -/

/-- The scalar matrix `c • 1` as an element of `GL_2(F)`. -/
noncomputable abbrev scal (c : Fˣ) : GL (Fin 2) F := diagUnit c c

lemma scal_mul (c : Fˣ) (g : GL (Fin 2) F) : scal c * g = g * scal c := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, scal, diagUnit, coe_mk'']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma scal_mul_scal (c d : Fˣ) : (scal (c * d) : GL (Fin 2) F) = scal c * scal d := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, scal, diagUnit, coe_mk'']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma scal_one : (scal 1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal, diagUnit, coe_mk'']

lemma det_scal (c : Fˣ) : GeneralLinearGroup.det (scal c : GL (Fin 2) F) = c * c := by
  apply Units.ext
  simp [scal, diagUnit, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, coe_mk'']

/-- The adjugate `g ↦ det g · g⁻¹` on `GL_2(F)`, a group-theoretic form of the adjugate matrix. -/
noncomputable def adjG (g : GL (Fin 2) F) : GL (Fin 2) F := scal (GeneralLinearGroup.det g) * g⁻¹

lemma val_adjG (g : GL (Fin 2) F) :
    ((adjG g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  have hd : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (GeneralLinearGroup.det g).ne_zero
    rwa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
  rw [adjG, Units.val_mul, GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scal, diagUnit, coe_mk'', GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

lemma adjG_conj (x g : GL (Fin 2) F) : adjG (x * g * x⁻¹) = x * adjG g * x⁻¹ := by
  have hd : GeneralLinearGroup.det (x * g * x⁻¹) = GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det x), mul_inv_cancel_right]
  have hc := scal_mul (GeneralLinearGroup.det g) x
  unfold adjG
  rw [hd, show (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ by group]
  calc scal (GeneralLinearGroup.det g) * (x * g⁻¹ * x⁻¹)
      = (scal (GeneralLinearGroup.det g) * x) * g⁻¹ * x⁻¹ := by group
    _ = (x * scal (GeneralLinearGroup.det g)) * g⁻¹ * x⁻¹ := by rw [hc]
    _ = x * (scal (GeneralLinearGroup.det g) * g⁻¹) * x⁻¹ := by group

lemma adjG_scal (c : Fˣ) : adjG (scal c : GL (Fin 2) F) = scal c := by
  rw [adjG, det_scal]
  have : (scal c : GL (Fin 2) F)⁻¹ = scal c⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, ← scal_mul_scal, mul_inv_cancel, scal_one]
  rw [this, ← scal_mul_scal, mul_inv_cancel_right]

lemma adjG_one : (adjG 1 : GL (Fin 2) F) = 1 := by
  simp [adjG, scal_one]

lemma adjG_mul_of_comm {z w : GL (Fin 2) F} (hzw : z * w = w * z) :
    adjG (z * w) = adjG z * adjG w := by
  have h1 : (z * w)⁻¹ = z⁻¹ * w⁻¹ := by rw [hzw, _root_.mul_inv_rev]
  have c1 := scal_mul (GeneralLinearGroup.det w) z⁻¹
  unfold adjG
  rw [map_mul, scal_mul_scal, h1]
  calc scal (GeneralLinearGroup.det z) * scal (GeneralLinearGroup.det w) * (z⁻¹ * w⁻¹)
      = scal (GeneralLinearGroup.det z) * (scal (GeneralLinearGroup.det w) * z⁻¹) * w⁻¹ := by group
    _ = scal (GeneralLinearGroup.det z) * (z⁻¹ * scal (GeneralLinearGroup.det w)) * w⁻¹ := by rw [c1]
    _ = _ := by group

lemma trace_adjG (g : GL (Fin 2) F) :
    Matrix.trace ((adjG g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [val_adjG]; simp [Matrix.trace_fin_two, add_comm]

lemma det_adjG (g : GL (Fin 2) F) :
    ((adjG g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (g : Matrix (Fin 2) (Fin 2) F).det := by
  rw [val_adjG]; simp [Matrix.det_fin_two]; ring

/-- The conjugation orbit of any group element has fibres of the size of its centralizer. -/
lemma card_filter_conj_eq {G : Type*} [Group G] [Fintype G] [DecidableEq G] (g z : G)
    (hz : ∃ x0, x0 * g * x0⁻¹ = z) :
    (Finset.univ.filter fun x : G => x * g * x⁻¹ = z).card = Nat.card (Subgroup.centralizer {g}) := by
  obtain ⟨x0, rfl⟩ := hz
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun x => ⟨x0⁻¹ * x.1, ?_⟩
      invFun := fun y => ⟨x0 * y.1, ?_⟩
      left_inv := fun x => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun y => Subtype.ext (inv_mul_cancel_left _ _) }
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have hx : x.1 * k * x.1⁻¹ = x0 * k * x0⁻¹ := x.2
    calc k * (x0⁻¹ * x.1) = x0⁻¹ * (x0 * k * x0⁻¹) * x.1 := by group
      _ = x0⁻¹ * (x.1 * k * x.1⁻¹) * x.1 := by rw [hx]
      _ = x0⁻¹ * x.1 * k := by group
  · have hy := Subgroup.mem_centralizer_iff.1 y.2 g (Set.mem_singleton _)
    show (x0 * y.1) * g * (x0 * y.1)⁻¹ = x0 * g * x0⁻¹
    calc (x0 * y.1) * g * (x0 * y.1)⁻¹ = x0 * (y.1 * g) * y.1⁻¹ * x0⁻¹ := by group
      _ = x0 * (g * y.1) * y.1⁻¹ * x0⁻¹ := by rw [hy]
      _ = x0 * g * x0⁻¹ := by group

/-! ### The nonsplit torus -/

section Torus

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- **The nonsplit torus** `K ≤ GL_2(F)` attached to an irreducible quadratic `x² - t x + n`: the centralizer of
its companion matrix `C`, i.e. the group of invertible matrices `a + b C`.  It is a model of the multiplicative
group of `F_{q²}` (acting on itself by multiplication, in the basis `1, C` over `F`). -/
noncomputable def torus : Subgroup (GL (Fin 2) F) := Subgroup.centralizer {(ellipticElt h : GL (Fin 2) F)}

/-- The elements of the nonsplit torus are exactly the invertible matrices `a + b C`, `(a, b) ≠ 0`. -/
lemma mem_torus_iff {g : GL (Fin 2) F} : g ∈ torus h ↔ ∃ p, ellUnit h p = g := by
  have e : g ∈ torus h ↔ g ∈ Set.range (ellUnit h) := by
    rw [← centralizer_elliptic h]; exact Iff.rfl
  exact e.trans Set.mem_range

lemma torus_entries {z : GL (Fin 2) F} (hz : z ∈ torus h) :
    ∃ a b : F, (a, b) ≠ 0 ∧
      (z : Matrix (Fin 2) (Fin 2) F) = !![a, -(b * n); b, a + b * t] := by
  obtain ⟨p, rfl⟩ := (mem_torus_iff h).1 hz
  exact ⟨p.1.1, p.1.2, p.2, rfl⟩

/-- The order of the nonsplit torus is `q² - 1`. -/
lemma card_torus : Nat.card (torus h) = Nat.card F ^ 2 - 1 := card_centralizer_elliptic h

lemma diag_mem_torus (c : Fˣ) : (scal c : GL (Fin 2) F) ∈ torus h := by
  refine (mem_torus_iff h).2 ⟨⟨((c : F), 0), fun h0 => c.ne_zero (congrArg Prod.fst h0)⟩, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ellUnit, scal, diagUnit, coe_mk'']

lemma torus_comm {z w : GL (Fin 2) F} (hz : z ∈ torus h) (hw : w ∈ torus h) : z * w = w * z := by
  obtain ⟨a, b, -, hza⟩ := torus_entries h hz
  obtain ⟨a', b', -, hwa⟩ := torus_entries h hw
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hza, hwa]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma adjG_mem {z : GL (Fin 2) F} (hz : z ∈ torus h) : adjG z ∈ torus h :=
  mul_mem (diag_mem_torus h _) (inv_mem hz)

/-- The Galois conjugation `z ↦ z^σ = det z · z⁻¹` of the nonsplit torus (the nontrivial automorphism of
`F_{q²}` over `F`, the book's `z ↦ z^q`). -/
noncomputable def sigmaT : torus h →* torus h where
  toFun z := ⟨adjG (z : GL (Fin 2) F), adjG_mem h z.2⟩
  map_one' := Subtype.ext adjG_one
  map_mul' z w := Subtype.ext (adjG_mul_of_comm (torus_comm h z.2 w.2))

lemma coe_sigmaT (z : torus h) : ((sigmaT h z : torus h) : GL (Fin 2) F) = adjG (z : GL (Fin 2) F) := rfl

lemma sigmaT_scal (c : Fˣ) :
    sigmaT h ⟨scal c, diag_mem_torus h c⟩ = ⟨scal c, diag_mem_torus h c⟩ :=
  Subtype.ext (adjG_scal c)

/-- An element of `GL_2(F)` which is not `NonScalar` is a scalar matrix. -/
lemma exists_scal_of_not_nonScalar {g : GL (Fin 2) F} (hg : ¬ NonScalar g) : ∃ u : Fˣ, g = scal u := by
  unfold NonScalar at hg
  obtain ⟨h10, h01, h00⟩ := not_not.1 hg
  have hn := (GeneralLinearGroup.det g).ne_zero
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h01, ← h00] at hn
  have h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0; apply hn; rw [h0]; ring
  refine ⟨Units.mk0 _ h0, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal, diagUnit, h10, h01, h00]

lemma adjG_adjG (y : GL (Fin 2) F) : adjG (adjG y) = y := by
  have hd : GeneralLinearGroup.det (adjG y) = GeneralLinearGroup.det y := by
    simp only [adjG, map_mul, map_inv, det_scal]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hc := scal_mul (GeneralLinearGroup.det y) y
  conv_lhs => rw [adjG, hd]
  unfold adjG
  rw [_root_.mul_inv_rev, inv_inv]
  calc scal (GeneralLinearGroup.det y) * (y * (scal (GeneralLinearGroup.det y))⁻¹)
      = (scal (GeneralLinearGroup.det y) * y) * (scal (GeneralLinearGroup.det y))⁻¹ := by group
    _ = (y * scal (GeneralLinearGroup.det y)) * (scal (GeneralLinearGroup.det y))⁻¹ := by rw [hc]
    _ = y := by group

end Torus

/-! ### The induced representation `Y_ν` -/

section Induced

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- A character `ν : K → ℂ^×` viewed as a homomorphism to the multiplicative monoid `ℂ`. -/
noncomputable def nuHom (ν : torus h →* ℂˣ) : torus h →* ℂ := (Units.coeHom ℂ).comp ν

/-- **Etingof et al., §4.24.4**: the representation `Y_ν = Ind_K^G C_ν` of `GL_2(F)`, induced from the character
`ν` of the nonsplit torus `K`. -/
noncomputable abbrev torusInd (ν : torus h →* ℂˣ) :=
  Ind (torus h) (lineRep' (nuHom h ν))

/-- The character `ν` of `K`, extended by zero to `G`. -/
noncomputable def extT (ν : torus h →* ℂˣ) (y : GL (Fin 2) F) : ℂ :=
  charExt (torus h) (lineRep' (nuHom h ν)) y

lemma extT_of_mem (ν : torus h →* ℂˣ) {y : GL (Fin 2) F} (hy : y ∈ torus h) :
    extT h ν y = ν ⟨y, hy⟩ := by
  simp [extT, charExt_of_mem _ _ hy, character_lineRep', nuHom]

lemma extT_of_not_mem (ν : torus h →* ℂˣ) {y : GL (Fin 2) F} (hy : y ∉ torus h) :
    extT h ν y = 0 := charExt_of_not_mem _ _ hy

lemma natCard_torus_ne_zero : (Nat.card (torus h) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- The averaged induced-character formula for `Y_ν`. -/
theorem character_torusInd (ν : torus h →* ℂˣ) (g : GL (Fin 2) F) :
    (torusInd h ν).character g =
      (Nat.card (torus h) : ℂ)⁻¹ * ∑ x : GL (Fin 2) F, extT h ν (x * g * x⁻¹) := by
  haveI : Invertible (Nat.card (torus h) : ℂ) := invertibleOfNonzero (natCard_torus_ne_zero h)
  haveI : Fintype (RCosets (torus h)) := Fintype.ofFinite _
  rw [character_Ind_averaged, invOf_eq_inv]
  rfl

lemma card_GL2_eq_torus : Nat.card (GL (Fin 2) F) = Nat.card (torus h) * (Nat.card F ^ 2 - Nat.card F) := by
  rw [card_GL2, card_torus]

/-- `Y_ν` has dimension `q² - q`. -/
theorem finrank_torusInd (ν : torus h →* ℂˣ) :
    finrank ℂ (coindV (torus h).subtype (lineRep' (nuHom h ν))) = Nat.card F ^ 2 - Nat.card F := by
  rw [finrank_Ind]
  have h1 := (torus h).card_mul_index
  rw [card_GL2_eq_torus h] at h1
  rw [finrank_self, one_mul]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

/-- On the scalar matrix `c`, the character of `Y_ν` is `(q² - q) ν(c)`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem character_torusInd_scal (ν : torus h →* ℂˣ) (c : Fˣ) :
    (torusInd h ν).character (scal c) =
      ((Nat.card F ^ 2 - Nat.card F : ℕ) : ℂ) * (ν ⟨scal c, diag_mem_torus h c⟩ : ℂ) := by
  rw [character_torusInd]
  have hx : ∀ x : GL (Fin 2) F, x * scal c * x⁻¹ = scal c := fun x => by
    rw [← scal_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [Finset.sum_congr rfl fun x _ => by rw [hx, extT_of_mem h ν (diag_mem_torus h c)],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, card_GL2_eq_torus h,
    Nat.cast_mul]
  have := natCard_torus_ne_zero h
  field_simp

/-- If an element `z` of `K` has an eigenvalue in `F` (a root of its characteristic polynomial), then it is
scalar. -/
lemma torus_val10_of_root {z : GL (Fin 2) F} (hz : z ∈ torus h) (l : F)
    (hl : l ^ 2 - Matrix.trace (z : Matrix (Fin 2) (Fin 2) F) * l +
      (z : Matrix (Fin 2) (Fin 2) F).det = 0) :
    (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨a, b, hab, hza⟩ := torus_entries h hz
  by_contra hb
  have hb' : b ≠ 0 := by simpa [hza] using hb
  apply ell_det_ne_zero h (a := a - l) (b := b) (fun h0 => hb' (congrArg Prod.snd h0))
  rw [hza] at hl
  simp [Matrix.trace_fin_two, Matrix.det_fin_two] at hl
  linear_combination hl

/-- **Etingof et al., §4.24.4**: the character of `Y_ν` vanishes on every non-scalar element with an eigenvalue
in `F` (in particular on parabolic and hyperbolic elements), as no conjugate of such an element lies in `K`. -/
theorem character_torusInd_of_root (ν : torus h →* ℂˣ) {g : GL (Fin 2) F} (hg : NonScalar g) (l : F)
    (hl : l ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) * l +
      (g : Matrix (Fin 2) (Fin 2) F).det = 0) :
    (torusInd h ν).character g = 0 := by
  rw [character_torusInd, Finset.sum_eq_zero, mul_zero]
  intro x _
  apply extT_of_not_mem
  intro hx
  have hc : IsConj g (x * g * x⁻¹) := isConj_iff.2 ⟨x, rfl⟩
  have hl' : l ^ 2 - Matrix.trace ((x * g * x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * l +
      ((x * g * x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [← isConj_trace hc, ← isConj_det hc]; exact hl
  have h10 := torus_val10_of_root h hx l hl'
  obtain ⟨a, b, hab, hy⟩ := torus_entries h hx
  have hb : b = 0 := by simpa [hy] using h10
  have hanz : a ≠ 0 := fun ha => hab (by simp [ha, hb])
  have e1 : x * g * x⁻¹ = scal (Units.mk0 a hanz) := by
    apply Units.ext
    rw [hy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, scal, diagUnit, coe_mk'']
  have e2 : g = scal (Units.mk0 a hanz) := by
    calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
      _ = x⁻¹ * scal (Units.mk0 a hanz) * x := by rw [e1]
      _ = scal (Units.mk0 a hanz) := by rw [← scal_mul, inv_mul_cancel_right]
  exact hg (by rw [e2]; simp [scal, diagUnit, coe_mk''])

/-- **Etingof et al., §4.24.4**: the character of `Y_ν` vanishes on parabolic elements. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem character_torusInd_upper (ν : torus h →* ℂˣ) (x : Fˣ) :
    (torusInd h ν).character (upperUnit x 1) = 0 :=
  character_torusInd_of_root h ν (nonScalar_upper x) x (by
    rw [trace_upper, det_upper]; ring)

/-- **Etingof et al., §4.24.4**: the character of `Y_ν` vanishes on hyperbolic elements. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem character_torusInd_diag (ν : torus h →* ℂˣ) {x y : Fˣ} (hxy : x ≠ y) :
    (torusInd h ν).character (diagUnit x y) = 0 :=
  character_torusInd_of_root h ν (nonScalar_diag hxy) x (by
    rw [trace_diag, det_diag]; ring)

/-! #### Elements of `K` which are not scalar -/

lemma adjG_ne_self {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : adjG z ≠ z := by
  intro heq
  obtain ⟨a, b, -, hza⟩ := torus_entries h hz
  have hb : b ≠ 0 := by simpa [hza] using hz10
  have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) heq
  simp only [val_adjG, hza] at e
  have e10 := congrFun (congrFun e 1) 0
  have e00 := congrFun (congrFun e 0) 0
  simp at e10 e00
  have ht : t = 0 := e00.resolve_left hb
  have h2 : (2 : F) = 0 := by
    have : b * 2 = 0 := by linear_combination -e10
    exact (mul_eq_zero.1 this).resolve_left hb
  have hchar : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hr : ringChar F = 2 := ringChar.eq_iff.2 hchar
  obtain ⟨r, hr'⟩ := FiniteField.isSquare_of_char_two hr n
  apply h r
  rw [ht]
  linear_combination hr' + r ^ 2 * h2

/-- An element of `K` conjugate to a non-scalar element `z` of `K` is `z` or its Galois conjugate `z^σ`. -/
lemma torus_conj_cases {z y x : GL (Fin 2) F} (hz : z ∈ torus h) (hy : y ∈ torus h)
    (hxy : x * z * x⁻¹ = y) : y = z ∨ y = adjG z := by
  have hc : IsConj z y := isConj_iff.2 ⟨x, hxy⟩
  have ht := isConj_trace hc
  have hd := isConj_det hc
  by_cases hyz : y = z
  · exact Or.inl hyz
  right
  obtain ⟨a, b, -, hza⟩ := torus_entries h hz
  obtain ⟨a', b', -, hya⟩ := torus_entries h hy
  rw [hza, hya] at ht hd
  simp [Matrix.trace_fin_two, Matrix.det_fin_two] at ht hd
  have hprod : ((y : Matrix (Fin 2) (Fin 2) F) - z) * ((y : Matrix (Fin 2) (Fin 2) F) - (adjG z : Matrix (Fin 2) (Fin 2) F)) = 0 := by
    rw [val_adjG]
    simp only [hza, hya]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-a') * ht + hd
    · linear_combination (b' * n) * ht
    · linear_combination (-b') * ht
    · linear_combination (-(a' + b' * t)) * ht + hd
  have hne : (a' - a, b' - b) ≠ 0 := by
    intro h0
    apply hyz
    have h1 : a' = a := sub_eq_zero.1 (congrArg Prod.fst h0)
    have h2 : b' = b := sub_eq_zero.1 (congrArg Prod.snd h0)
    apply Units.ext
    rw [hya, hza, h1, h2]
  have hAB : (y : Matrix (Fin 2) (Fin 2) F) - z =
      !![a' - a, -((b' - b) * n); b' - b, (a' - a) + (b' - b) * t] := by
    rw [hya, hza]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hU : IsUnit ((y : Matrix (Fin 2) (Fin 2) F) - z) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hAB, Matrix.det_fin_two_of]
    exact ell_det_ne_zero h hne
  have := (hU.mul_right_eq_zero).1 hprod
  exact Units.ext (sub_eq_zero.1 this)

lemma exists_conj_adjG {z : GL (Fin 2) F} (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ x0, x0 * z * x0⁻¹ = adjG z := by
  have hz : NonScalar z := fun hh => hz10 hh.1
  have hz' : NonScalar (adjG z) := by
    rintro ⟨h10, -, -⟩
    apply hz10
    rw [val_adjG] at h10
    simpa using h10
  exact isConj_iff.1 (isConj_of_trace_det hz hz' (trace_adjG z).symm (det_adjG z).symm)

lemma centralizer_eq_torus {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : Subgroup.centralizer {z} = torus h := by
  obtain ⟨a, b, -, hza⟩ := torus_entries h hz
  have hb : b ≠ 0 := by simpa [hza] using hz10
  have hZ : (z : Matrix (Fin 2) (Fin 2) F) =
      a • (1 : Matrix (Fin 2) (Fin 2) F) + b • ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [hza]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ellipticElt, ellUnit, coe_mk'']
  ext y
  constructor
  · intro hy
    have hzy : z * y = y * z := Subgroup.mem_centralizer_iff.1 hy z (Set.mem_singleton z)
    rw [torus, Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have e := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hzy
    simp only [Units.val_mul] at e
    rw [hZ] at e
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at e
    have e2 := add_left_cancel e
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact smul_right_injective _ hb e2
  · intro hy
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact torus_comm h hz hy

/-- **Etingof et al., §4.24.4**: for an element `z` of the nonsplit torus which is not scalar, the character of
`Y_ν` is `ν(z) + ν(z^σ)`, where `z^σ` is the Galois conjugate of `z` (`z^q` in the book). -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem character_torusInd_torus (ν : torus h →* ℂˣ) {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    (torusInd h ν).character z = (ν ⟨z, hz⟩ : ℂ) + (ν (sigmaT h ⟨z, hz⟩) : ℂ) := by
  have hσ : adjG z ∈ torus h := adjG_mem h hz
  have hne : adjG z ≠ z := adjG_ne_self h hz hz10
  have hpt : ∀ x : GL (Fin 2) F, extT h ν (x * z * x⁻¹) =
      (if x * z * x⁻¹ = z then (ν ⟨z, hz⟩ : ℂ) else 0) +
        (if x * z * x⁻¹ = adjG z then (ν (sigmaT h ⟨z, hz⟩) : ℂ) else 0) := by
    intro x
    by_cases hy : x * z * x⁻¹ ∈ torus h
    · rcases torus_conj_cases h hz hy rfl with h1 | h1
      · have h2 : (⟨x * z * x⁻¹, hy⟩ : torus h) = ⟨z, hz⟩ := Subtype.ext h1
        rw [if_pos h1, if_neg (by rw [h1]; exact hne.symm), extT_of_mem h ν hy, h2, add_zero]
      · have h2 : (⟨x * z * x⁻¹, hy⟩ : torus h) = sigmaT h ⟨z, hz⟩ := Subtype.ext h1
        rw [if_pos h1, if_neg (by rw [h1]; exact hne), extT_of_mem h ν hy, h2, zero_add]
    · rw [extT_of_not_mem h ν hy, if_neg (fun e => hy (by rw [e]; exact hz)),
        if_neg (fun e => hy (by rw [e]; exact hσ)), add_zero]
  have c1 : (Finset.univ.filter fun x : GL (Fin 2) F => x * z * x⁻¹ = z).card = Nat.card (torus h) := by
    rw [card_filter_conj_eq z z ⟨1, by simp⟩, centralizer_eq_torus h hz hz10]
  have c2 : (Finset.univ.filter fun x : GL (Fin 2) F => x * z * x⁻¹ = adjG z).card = Nat.card (torus h) := by
    rw [card_filter_conj_eq z _ (exists_conj_adjG hz10), centralizer_eq_torus h hz hz10]
  rw [character_torusInd, Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, c1, c2,
    nsmul_eq_mul, nsmul_eq_mul, ← mul_add, ← mul_assoc, inv_mul_cancel₀ (natCard_torus_ne_zero h), one_mul]

/-! #### The isomorphism `Y_ν ≅ Y_{ν^σ}` -/

lemma extT_comp_sigma (ν : torus h →* ℂˣ) (y : GL (Fin 2) F) :
    extT h (ν.comp (sigmaT h)) y = extT h ν (adjG y) := by
  by_cases hy : y ∈ torus h
  · rw [extT_of_mem h _ hy, extT_of_mem h ν (adjG_mem h hy)]; rfl
  · have : adjG y ∉ torus h := fun hh => hy (by have := adjG_mem h hh; rwa [adjG_adjG] at this)
    rw [extT_of_not_mem h _ hy, extT_of_not_mem h ν this]

/-- Every character of `GL_2(F)` takes the same value at `g` and at its adjugate `det g · g⁻¹`
(they are conjugate, or both equal to a scalar). -/
lemma char_adjG {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) F) V)
    (g : GL (Fin 2) F) : ρ.character (adjG g) = ρ.character g := by
  by_cases hg : NonScalar g
  · have hg' : NonScalar (adjG g) := by
      rintro ⟨h1, h2, h3⟩
      apply hg
      rw [val_adjG] at h1 h2 h3
      simp at h1 h2 h3
      exact ⟨h1, h2, h3.symm⟩
    obtain ⟨x, hx⟩ := isConj_iff.1
      (isConj_of_trace_det hg hg' (trace_adjG g).symm (det_adjG g).symm)
    rw [← hx, ρ.char_conj]
  · obtain ⟨u, rfl⟩ := exists_scal_of_not_nonScalar hg
    rw [adjG_scal]

theorem character_torusInd_comp_sigma (ν : torus h →* ℂˣ) (g : GL (Fin 2) F) :
    (torusInd h (ν.comp (sigmaT h))).character g = (torusInd h ν).character (adjG g) := by
  rw [character_torusInd, character_torusInd]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by rw [extT_comp_sigma, adjG_conj]

/-- **Etingof et al., §4.24.4**: the representations `Y_ν` and `Y_{ν^σ}` (induced from `ν` and its Galois
conjugate `ν ∘ σ`, the book's `ν^q`) are isomorphic, since they have the same character. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem nonempty_equiv_torusInd_comp_sigma (ν : torus h →* ℂˣ) :
    Nonempty (Representation.Equiv (torusInd h ν) (torusInd h (ν.comp (sigmaT h)))) :=
  nonempty_equiv_of_character_eq _ _
    (funext fun g => by rw [character_torusInd_comp_sigma, char_adjG])

end Induced

/-! ### Characters of the principal series on some elements

We need the values of `χ_{V_{λ₁,λ₂}}` on scalar matrices, on parabolic elements, on hyperbolic elements for the
trivial pair `(1, 1)`, and on elements without eigenvalue in `F`. -/

section PrincipalValues

lemma scal_mem_borel (c : Fˣ) : (scal c : GL (Fin 2) F) ∈ borel F := by
  simp [mem_borel, scal, diagUnit]

lemma extC_scal (l₁ l₂ : Fˣ →* ℂˣ) (c : Fˣ) :
    extC (borelChar l₁ l₂) (scal c : GL (Fin 2) F) = (l₁ c : ℂ) * l₂ c := by
  rw [extC_of_mem _ (scal_mem_borel c), borelChar_apply']
  simp [scal, diagUnit]

lemma card_GL2_borel : Nat.card (GL (Fin 2) F) = Nat.card (borel F) * (Nat.card F + 1) := by
  rw [← index_borel, Subgroup.card_mul_index]

lemma natCard_borel_ne_zero : (Nat.card (borel F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

lemma card_filter_borel :
    (Finset.univ.filter fun u : GL (Fin 2) F => u ∈ borel F).card = Nat.card (borel F) := by
  rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]

/-- **Etingof et al., §4.24.3**: on a scalar matrix `c`, `χ_{V_{λ₁,λ₂}}(c) = (q + 1) λ₁(c) λ₂(c)`. -/
theorem character_principalSeries_scal (l₁ l₂ : Fˣ →* ℂˣ) (c : Fˣ) :
    (principalSeries (F := F) l₁ l₂).character (scal c) =
      ((Nat.card F + 1 : ℕ) : ℂ) * ((l₁ c : ℂ) * l₂ c) := by
  rw [character_principalSeries]
  have hx : ∀ x : GL (Fin 2) F, x * scal c * x⁻¹ = scal c := fun x => by
    rw [← scal_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [Finset.sum_congr rfl fun x _ => by rw [hx, extC_scal], Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card, card_GL2_borel, Nat.cast_mul]
  have := natCard_borel_ne_zero (F := F)
  field_simp

lemma extC_conj_of_mem (χ : borel F →* ℂˣ) {u : GL (Fin 2) F} (hu : u ∈ borel F) (h : GL (Fin 2) F) :
    extC χ (u * h * u⁻¹) = extC χ h := by
  rw [extC_mul_right χ (inv_mem hu), extC_mul_left χ hu]
  have : (χ ⟨u, hu⟩ : ℂ) * (χ ⟨u⁻¹, inv_mem hu⟩ : ℂ) = 1 := by
    have h1 : (⟨u, hu⟩ * ⟨u⁻¹, inv_mem hu⟩ : borel F) = 1 := Subtype.ext (mul_inv_cancel u)
    rw [← Units.val_mul, ← map_mul, h1, map_one, Units.val_one]
  rw [show (χ ⟨u, hu⟩ : ℂ) * extC χ h * (χ ⟨u⁻¹, inv_mem hu⟩ : ℂ) = extC χ h by
    rw [mul_comm (χ ⟨u, hu⟩ : ℂ), mul_assoc, this, mul_one]]

lemma extC_conj_upper_of_not_mem (l₁ l₂ : Fˣ →* ℂˣ) (x0 : Fˣ) {u : GL (Fin 2) F}
    (hu : u⁻¹ ∉ borel F) : extC (borelChar l₁ l₂) (u * upperUnit x0 1 * u⁻¹) = 0 := by
  by_contra hne
  have hM : u * upperUnit x0 1 * u⁻¹ ∈ borel F := by
    by_contra hM; exact hne (extC_of_not_mem _ hM)
  have hB : (upperUnit x0 1 : GL (Fin 2) F) ∈ borel F := by simp [mem_borel, upperUnit]
  have hd := conj_diag_of_not_mem hu hB hM
  have ho := conj_offdiag_of_not_mem hM hd.1
  exact hu (mem_borel.2 (by simpa [upperUnit] using ho))

/-- **Etingof et al., §4.24.3**: on the parabolic element `[[x, 1], [0, x]]`,
`χ_{V_{λ₁,λ₂}} = λ₁(x) λ₂(x)`. -/
theorem character_principalSeries_upper (l₁ l₂ : Fˣ →* ℂˣ) (x : Fˣ) :
    (principalSeries (F := F) l₁ l₂).character (upperUnit x 1) = (l₁ x : ℂ) * l₂ x := by
  rw [character_principalSeries]
  have hB : (upperUnit x 1 : GL (Fin 2) F) ∈ borel F := by simp [mem_borel, upperUnit]
  have hpt : ∀ u : GL (Fin 2) F, extC (borelChar l₁ l₂) (u * upperUnit x 1 * u⁻¹) =
      if u ∈ borel F then (l₁ x : ℂ) * l₂ x else 0 := by
    intro u
    by_cases hu : u ∈ borel F
    · rw [if_pos hu, extC_conj_of_mem _ hu, extC_of_mem _ hB, borelChar_apply']
      simp [upperUnit]
    · rw [if_neg hu]
      exact extC_conj_upper_of_not_mem l₁ l₂ x (fun hh => hu (by simpa using inv_mem hh))
  rw [Finset.sum_congr rfl fun u _ => hpt u, ← Finset.sum_filter, Finset.sum_const, card_filter_borel,
    nsmul_eq_mul]
  have := natCard_borel_ne_zero (F := F)
  field_simp

lemma extC_one (y : GL (Fin 2) F) :
    extC (borelChar (1 : Fˣ →* ℂˣ) 1) y = if y ∈ borel F then 1 else 0 := by
  by_cases hy : y ∈ borel F
  · rw [if_pos hy, extC_of_mem _ hy, borelChar_apply']
    simp
  · rw [if_neg hy, extC_of_not_mem _ hy]

lemma conj_diag_10 (a b : Fˣ) (x : GL (Fin 2) F) :
    ((x * diagUnit a b * x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 * ((a : F) - b) /
        ((x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
          (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hd : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (GeneralLinearGroup.det x).ne_zero
    rwa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
  simp [diagUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  field_simp
  ring

lemma conj_diag_mem_borel_iff {a b : Fˣ} (hab : a ≠ b) (x : GL (Fin 2) F) :
    x * diagUnit a b * x⁻¹ ∈ borel F ↔
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∨ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hd : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (GeneralLinearGroup.det x).ne_zero
    rwa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
  have hab' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hab (Units.ext h))
  rw [mem_borel, conj_diag_10, div_eq_zero_iff, mul_eq_zero, mul_eq_zero]
  simp [hd, hab']

lemma swap_mul_swap : (swapElt * swapElt : GL (Fin 2) F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapElt, coe_mk'', Matrix.mul_apply, Fin.sum_univ_two]

lemma val_mul_swap_10 (x : GL (Fin 2) F) :
    ((x * swapElt : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  simp [swapElt, coe_mk'', Matrix.mul_apply, Fin.sum_univ_two]

lemma val_mul_swap_11 (x : GL (Fin 2) F) :
    ((x * swapElt : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  simp [swapElt, coe_mk'', Matrix.mul_apply, Fin.sum_univ_two]

lemma card_filter_col_zero :
    (Finset.univ.filter fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0).card =
      Nat.card (borel F) := by
  rw [← card_filter_borel]
  refine Finset.card_bij' (fun x _ => x * swapElt) (fun x _ => x * swapElt) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact mem_borel.2 ((val_mul_swap_10 x).trans hx)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [val_mul_swap_11]; exact mem_borel.1 hx
  · intro x _; rw [mul_assoc, swap_mul_swap, mul_one]
  · intro x _; rw [mul_assoc, swap_mul_swap, mul_one]

/-- **Etingof et al., §4.24.3**: the character of `V_{1,1}` takes the value `2` on a hyperbolic element
(a permutation character: `V_{1,1}` is the permutation representation on the projective line). -/
theorem character_principalSeries_one_diag {a b : Fˣ} (hab : a ≠ b) :
    (principalSeries (F := F) 1 1).character (diagUnit a b) = 2 := by
  rw [character_principalSeries]
  have hpt : ∀ x : GL (Fin 2) F, extC (borelChar (1 : Fˣ →* ℂˣ) 1) (x * diagUnit a b * x⁻¹) =
      if (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∨ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 then 1 else 0 := by
    intro x
    rw [extC_one]
    simp only [conj_diag_mem_borel_iff hab]
  rw [Finset.sum_congr rfl fun x _ => hpt x, ← Finset.sum_filter, Finset.sum_const, Finset.filter_or,
    Finset.card_union_of_disjoint, card_filter_col_zero]
  · have h1 : (Finset.univ.filter fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0).card =
        Nat.card (borel F) := card_filter_borel
    rw [h1, nsmul_eq_mul, Nat.cast_add]
    have := natCard_borel_ne_zero (F := F)
    field_simp
    ring
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    have := (GeneralLinearGroup.det x).ne_zero
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h1, h2] at this
    simp at this

/-- If `g` has no eigenvalue in `F`, then `χ_{V_{λ₁,λ₂}}(g) = 0`. -/
theorem character_principalSeries_of_no_root (l₁ l₂ : Fˣ →* ℂˣ) {g : GL (Fin 2) F}
    (hg : ∀ l : F, l ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) * l +
      (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0) :
    (principalSeries (F := F) l₁ l₂).character g = 0 := by
  rw [character_principalSeries, Finset.sum_eq_zero, mul_zero]
  intro x _
  apply extC_of_not_mem
  intro hx
  have hc : IsConj g (x * g * x⁻¹) := isConj_iff.2 ⟨x, rfl⟩
  apply hg (((x * g * x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)
  rw [isConj_trace hc, isConj_det hc, Matrix.trace_fin_two, Matrix.det_fin_two, mem_borel.1 hx]
  ring

end PrincipalValues

/-! ### Sums of class functions over `GL_2(F)` -/

section ClassSums

lemma not_isConj_scal_upper (c x : Fˣ) :
    ¬ IsConj (scal c : GL (Fin 2) F) (upperUnit x 1) := by
  intro hc
  obtain ⟨y, hy⟩ := isConj_iff.1 hc
  have : y * scal c * y⁻¹ = scal c := by rw [← scal_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [this] at hy
  have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hy
  simp [scal, diagUnit, upperUnit] at this

lemma eq_scal_of_isConj_scal {g : GL (Fin 2) F} {c : Fˣ} (hc : IsConj g (scal c)) : g = scal c := by
  obtain ⟨x, hx⟩ := isConj_iff.1 hc
  calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
    _ = x⁻¹ * scal c * x := by rw [hx]
    _ = scal c := by rw [← scal_mul, inv_mul_cancel_right]

lemma scal_injective : Function.Injective (fun c : Fˣ => (scal c : GL (Fin 2) F)) := by
  intro c d h
  exact congrArg Prod.fst (diagUnit_injective (F := F) (a₁ := (c, c)) (a₂ := (d, d)) h)

/-- Every element of `GL_2(F)` is scalar, conjugate to a parabolic or hyperbolic standard element, or has no
eigenvalue in `F`. -/
lemma cover_elt (g : GL (Fin 2) F) :
    (∃ c : Fˣ, g = scal c) ∨ (∃ x : Fˣ, IsConj g (upperUnit x 1)) ∨
      (∃ x y : Fˣ, x ≠ y ∧ IsConj g (diagUnit x y)) ∨
      (∀ l : F, l ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) * l +
        (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0) := by
  rcases conjClass_cover (ConjClasses.mk g) with ⟨c, hc⟩ | ⟨x, hx⟩ | ⟨x, y, hxy, hc⟩ | ⟨t, n, hirr, hc⟩
  · exact Or.inl ⟨c, eq_scal_of_isConj_scal (ConjClasses.mk_eq_mk_iff_isConj.1 hc).symm⟩
  · exact Or.inr (Or.inl ⟨x, (ConjClasses.mk_eq_mk_iff_isConj.1 hx).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, hxy, ConjClasses.mk_eq_mk_iff_isConj.1 hc⟩))
  · refine Or.inr (Or.inr (Or.inr fun l => ?_))
    have hcj := ConjClasses.mk_eq_mk_iff_isConj.1 hc
    rw [isConj_trace hcj, isConj_det hcj, trace_elliptic, det_elliptic]
    exact hirr l

lemma card_filter_isConj_upper (x : Fˣ) :
    (Finset.univ.filter fun g : GL (Fin 2) F => IsConj g (upperUnit x 1)).card =
      Nat.card F ^ 2 - 1 := by
  rw [← ncard_conjugatesOf_parabolic x, ← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  exact isConj_comm

lemma sum_ite_scalar (Φ : GL (Fin 2) F → ℂ) :
    ∑ g, (if ∃ c : Fˣ, g = scal c then Φ g else 0) = ∑ c : Fˣ, Φ (scal c) := by
  have : ∀ g : GL (Fin 2) F, (if ∃ c : Fˣ, g = scal c then Φ g else 0) =
      ∑ c : Fˣ, if g = scal c then Φ g else 0 := by
    intro g
    by_cases hg : ∃ c : Fˣ, g = scal c
    · obtain ⟨c0, rfl⟩ := hg
      rw [if_pos ⟨c0, rfl⟩, Finset.sum_eq_single c0]
      · simp
      · intro c _ hc
        rw [if_neg]
        intro h; exact hc (scal_injective h).symm
      · simp
    · rw [if_neg hg]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      intro h; exact hg ⟨c, h⟩
  rw [Finset.sum_congr rfl fun g _ => this g, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

/-- A class function on `GL_2(F)` vanishing on hyperbolic elements and on elements without eigenvalue is summed
over the scalar and parabolic classes. -/
lemma sum_class_function (Φ : GL (Fin 2) F → ℂ) (hΦ : ∀ x g : GL (Fin 2) F, Φ (x * g * x⁻¹) = Φ g)
    (hH : ∀ x y : Fˣ, x ≠ y → Φ (diagUnit x y) = 0)
    (hE : ∀ g : GL (Fin 2) F, (∀ l : F, l ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) * l +
        (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0) → Φ g = 0) :
    ∑ g, Φ g = ∑ c : Fˣ, Φ (scal c) +
      ((Nat.card F ^ 2 - 1 : ℕ) : ℂ) * ∑ x : Fˣ, Φ (upperUnit x 1) := by
  have hconj : ∀ g g' : GL (Fin 2) F, IsConj g g' → Φ g = Φ g' := fun g g' hgg => by
    obtain ⟨x, hx⟩ := isConj_iff.1 hgg
    rw [← hx, hΦ]
  have hpt : ∀ g : GL (Fin 2) F, Φ g = (if ∃ c : Fˣ, g = scal c then Φ g else 0) +
      ∑ x : Fˣ, (if IsConj g (upperUnit x 1) then Φ g else 0) := by
    intro g
    rcases cover_elt g with ⟨c0, hc0⟩ | ⟨x0, hx0⟩ | ⟨x, y, hxy, hxy'⟩ | hroot
    · rw [if_pos ⟨c0, hc0⟩, Finset.sum_eq_zero, add_zero]
      intro x _
      rw [if_neg]
      rw [hc0]; exact not_isConj_scal_upper c0 x
    · have hns : ¬ ∃ c : Fˣ, g = scal c := by
        rintro ⟨c, rfl⟩; exact not_isConj_scal_upper c x0 hx0
      rw [if_neg hns, zero_add, Finset.sum_eq_single x0]
      · rw [if_pos hx0]
      · intro x _ hx
        rw [if_neg]
        intro hgx
        apply hx
        have := ConjClasses.mk_eq_mk_iff_isConj.2 (hgx.symm.trans hx0)
        exact upper_inj this
      · simp
    · have h0 : Φ g = 0 := (hconj g _ hxy').trans (hH x y hxy)
      rw [h0]; simp
    · have h0 : Φ g = 0 := hE g hroot
      rw [h0]; simp
  rw [Finset.sum_congr rfl fun g _ => hpt g, Finset.sum_add_distrib, sum_ite_scalar, Finset.sum_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∀ g : GL (Fin 2) F, (if IsConj g (upperUnit x 1) then Φ g else 0) =
      if IsConj g (upperUnit x 1) then Φ (upperUnit x 1) else 0 := by
    intro g
    by_cases hg : IsConj g (upperUnit x 1)
    · rw [if_pos hg, if_pos hg, hconj g _ hg]
    · rw [if_neg hg, if_neg hg]
  rw [Finset.sum_congr rfl fun g _ => this g, ← Finset.sum_filter, Finset.sum_const,
    card_filter_isConj_upper, nsmul_eq_mul]

end ClassSums

/-! ### Frobenius reciprocity for `Y_ν` and the sums over `K` -/

section CuspSums

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- A form of Frobenius reciprocity for `Y_ν = Ind_K^G C_ν`: for a class function `f` of `G`,
`∑_g f(g) conj χ_{Y_ν}(g) = (|G|/|K|) ∑_{y ∈ K} f(y) conj ν(y)`. -/
lemma sum_mul_conj_torusInd (ν : torus h →* ℂˣ) (f : GL (Fin 2) F → ℂ)
    (hf : ∀ x g : GL (Fin 2) F, f (x * g * x⁻¹) = f g) :
    ∑ g, f g * conj ((torusInd h ν).character g) =
      (Nat.card (GL (Fin 2) F) : ℂ) * (Nat.card (torus h) : ℂ)⁻¹ * ∑ y, f y * conj (extT h ν y) := by
  have hconjK : conj ((Nat.card (torus h) : ℂ)⁻¹) = (Nat.card (torus h) : ℂ)⁻¹ := by simp
  have h1 : ∀ g, f g * conj ((torusInd h ν).character g) =
      (Nat.card (torus h) : ℂ)⁻¹ * ∑ x, f g * conj (extT h ν (x * g * x⁻¹)) := by
    intro g
    rw [character_torusInd, map_mul, map_sum, hconjK, mul_left_comm, Finset.mul_sum]
  have h2 : ∀ x : GL (Fin 2) F, ∑ g, f g * conj (extT h ν (x * g * x⁻¹)) =
      ∑ y, f y * conj (extT h ν y) := by
    intro x
    refine Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hf x g]
  rw [Finset.sum_congr rfl fun g _ => h1 g, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  ring

lemma extT_mul_left (ν : torus h →* ℂˣ) {t' : GL (Fin 2) F} (ht : t' ∈ torus h) (y : GL (Fin 2) F) :
    extT h ν (t' * y) = ν ⟨t', ht⟩ * extT h ν y := by
  by_cases hy : y ∈ torus h
  · rw [extT_of_mem h ν (mul_mem ht hy), extT_of_mem h ν hy, ← Units.val_mul, ← map_mul]
    rfl
  · have : t' * y ∉ torus h := fun hh => hy (by simpa using mul_mem (inv_mem ht) hh)
    rw [extT_of_not_mem h ν this, extT_of_not_mem h ν hy, mul_zero]

lemma sum_extT_mul_conj_self (ν : torus h →* ℂˣ) :
    ∑ y, extT h ν y * conj (extT h ν y) = Nat.card (torus h) := by
  classical
  have hpt : ∀ y, extT h ν y * conj (extT h ν y) = if y ∈ torus h then 1 else 0 := by
    intro y
    by_cases hy : y ∈ torus h
    · rw [if_pos hy, extT_of_mem h ν hy, conj_hom_mul_self]
    · rw [if_neg hy, extT_of_not_mem h ν hy]; simp
  rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_boole, Nat.cast_inj,
    ← Fintype.card_subtype, Nat.card_eq_fintype_card]

/-- If `ν ∘ σ ≠ ν`, then `∑_y ν̃(y^σ) conj ν̃(y) = 0`. -/
lemma sum_extT_adjG_mul_conj (ν : torus h →* ℂˣ) (hσ : ν.comp (sigmaT h) ≠ ν) :
    ∑ y, extT h ν (adjG y) * conj (extT h ν y) = 0 := by
  obtain ⟨t0, ht0⟩ : ∃ t0 : torus h, ν (sigmaT h t0) ≠ ν t0 := by
    by_contra hall
    push Not at hall
    exact hσ (MonoidHom.ext hall)
  set c : ℂ := (ν (sigmaT h t0) : ℂ) * conj (ν t0 : ℂ) with hc
  have hc1 : c ≠ 1 := by
    intro h1
    apply ht0
    apply Units.ext
    calc (ν (sigmaT h t0) : ℂ) = (ν (sigmaT h t0) : ℂ) * conj (ν t0 : ℂ) * (ν t0 : ℂ) := by
          rw [mul_assoc, mul_comm (conj _), conj_hom_mul_self, mul_one]
      _ = (ν t0 : ℂ) := by rw [← hc, h1, one_mul]
  refine sum_eq_zero_of_mul_left (t0 : GL (Fin 2) F) c hc1 fun y => ?_
  by_cases hy : y ∈ torus h
  · have h1 : adjG ((t0 : GL (Fin 2) F) * y) = adjG t0 * adjG y :=
      adjG_mul_of_comm (torus_comm h t0.2 hy)
    have e : (⟨adjG (t0 : GL (Fin 2) F), adjG_mem h t0.2⟩ : torus h) = sigmaT h t0 := rfl
    rw [h1, extT_mul_left h ν (adjG_mem h t0.2), extT_mul_left h ν t0.2, map_mul, e, hc]
    ring
  · rw [extT_mul_left h ν t0.2, extT_of_not_mem h ν hy]
    simp

lemma torus_scal_of_val10 {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (h10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : ∃ c : Fˣ, z = scal c := by
  obtain ⟨a, b, hab, hza⟩ := torus_entries h hz
  have hb : b = 0 := by simpa [hza] using h10
  have ha : a ≠ 0 := fun ha => hab (by simp [ha, hb])
  refine ⟨Units.mk0 a ha, Units.ext ?_⟩
  rw [hza]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, scal, diagUnit]

lemma cast_sq_sub_one : ((Nat.card F ^ 2 - 1 : ℕ) : ℂ) = (Nat.card F : ℂ) ^ 2 - 1 := by
  have hq : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  rw [Nat.cast_sub hq]
  push_cast; ring

lemma card_cast_torus : (Nat.card (torus h) : ℂ) = (Nat.card F : ℂ) ^ 2 - 1 := by
  rw [card_torus, cast_sq_sub_one]

lemma cast_N : ((Nat.card F ^ 2 - Nat.card F : ℕ) : ℂ) = (Nat.card F : ℂ) ^ 2 - Nat.card F := by
  have hq : Nat.card F ≤ Nat.card F ^ 2 := by
    have := Nat.card_pos (α := F)
    nlinarith
  rw [Nat.cast_sub hq]
  push_cast; ring

lemma cast_card_G : (Nat.card (GL (Fin 2) F) : ℂ) =
    ((Nat.card F : ℂ) ^ 2 - 1) * ((Nat.card F : ℂ) ^ 2 - Nat.card F) := by
  rw [card_GL2, Nat.cast_mul, cast_N, cast_sq_sub_one]

lemma cast_pred : ((Nat.card F - 1 : ℕ) : ℂ) = (Nat.card F : ℂ) - 1 := by
  rw [Nat.cast_sub Nat.card_pos]; simp

lemma card_units_cast : ((Fintype.card Fˣ : ℕ) : ℂ) = (Nat.card F : ℂ) - 1 := by
  rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
  exact cast_pred

/-- The sum `∑_y χ_Y(y) conj ν̃(y)`. -/
lemma sum_Y_mul_conj_ext (ν : torus h →* ℂˣ) (hσ : ν.comp (sigmaT h) ≠ ν) :
    ∑ y, (torusInd h ν).character y * conj (extT h ν y) =
      (Nat.card (torus h) : ℂ) +
        (((Nat.card F ^ 2 - Nat.card F : ℕ) : ℂ) - 2) * ((Fintype.card Fˣ : ℕ) : ℂ) := by
  have hpt : ∀ y : GL (Fin 2) F, (torusInd h ν).character y * conj (extT h ν y) =
      extT h ν y * conj (extT h ν y) + extT h ν (adjG y) * conj (extT h ν y) +
        (if ∃ c : Fˣ, y = scal c then
          (((Nat.card F ^ 2 - Nat.card F : ℕ) : ℂ) - 2) * (extT h ν y * conj (extT h ν y)) else 0) := by
    intro y
    by_cases hy : y ∈ torus h
    · by_cases hs : ∃ c : Fˣ, y = scal c
      · obtain ⟨c, rfl⟩ := hs
        rw [character_torusInd_scal h ν c, if_pos ⟨c, rfl⟩, adjG_scal, extT_of_mem h ν hy]
        ring
      · have h10 : (y : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h0 => hs (torus_scal_of_val10 h hy h0)
        have e : sigmaT h ⟨y, hy⟩ = ⟨adjG y, adjG_mem h hy⟩ := rfl
        rw [character_torusInd_torus h ν hy h10, if_neg hs, extT_of_mem h ν hy,
          extT_of_mem h ν (adjG_mem h hy), e]
        ring
    · rw [extT_of_not_mem h ν hy]
      simp
  rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_extT_mul_conj_self, sum_extT_adjG_mul_conj h ν hσ, sum_ite_scalar, add_zero]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun c _ => by rw [extT_of_mem h ν (diag_mem_torus h c), conj_hom_mul_self],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end CuspSums

/-! ### The virtual character of Lemma 4.72 -/

section Lemma472

noncomputable instance invertibleCardGL : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- The character `(χ_{V_{1,1}} - 2) χ_{V_{α,1}}`, i.e. `χ_{W₁ ⊗ V_{α,1}} - χ_{V_{α,1}}` (the character of
`W₁` is `χ_{V_{1,1}} - 1`). -/
noncomputable def phiV (α : Fˣ →* ℂˣ) (g : GL (Fin 2) F) : ℂ :=
  ((principalSeries (F := F) 1 1).character g - 2) * (principalSeries (F := F) α 1).character g

/-- **Etingof et al., §4.24.4**: the character of the virtual representation
`W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν`, where the character of `W₁` is `χ_{V_{1,1}} - 1`. -/
noncomputable def cuspChar (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) (g : GL (Fin 2) F) : ℂ :=
  (((principalSeries (F := F) 1 1).character g - 1) * (principalSeries (F := F) α 1).character g) -
    (principalSeries (F := F) α 1).character g - (torusInd h ν).character g

lemma cuspChar_eq (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) (g : GL (Fin 2) F) :
    cuspChar h α ν g = phiV α g - (torusInd h ν).character g := by
  simp only [cuspChar, phiV]; ring

lemma phiV_conj (α : Fˣ →* ℂˣ) (x g : GL (Fin 2) F) : phiV α (x * g * x⁻¹) = phiV α g := by
  simp [phiV, Representation.char_conj]

lemma phiV_scal (α : Fˣ →* ℂˣ) (c : Fˣ) :
    phiV α (scal c) = ((Nat.card F : ℂ) ^ 2 - 1) * α c := by
  simp only [phiV, character_principalSeries_scal]
  simp
  ring

lemma phiV_upper (α : Fˣ →* ℂˣ) (x : Fˣ) : phiV α (upperUnit x 1) = -(α x : ℂ) := by
  simp only [phiV, character_principalSeries_upper]
  simp
  ring

lemma phiV_diag (α : Fˣ →* ℂˣ) {x y : Fˣ} (hxy : x ≠ y) : phiV α (diagUnit x y) = 0 := by
  rw [phiV, character_principalSeries_one_diag hxy]; simp

lemma phiV_noroot (α : Fˣ →* ℂˣ) {g : GL (Fin 2) F}
    (hg : ∀ l : F, l ^ 2 - Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) * l +
      (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0) : phiV α g = 0 := by
  rw [phiV, character_principalSeries_of_no_root α 1 hg, mul_zero]

lemma sum_phiV_sq (α : Fˣ →* ℂˣ) :
    ∑ g, phiV α g * conj (phiV α g) = (Nat.card (GL (Fin 2) F) : ℂ) * (Nat.card F : ℂ) := by
  rw [sum_class_function (fun g => phiV α g * conj (phiV α g)) (fun x g => by simp only [phiV_conj])
    (fun x y hxy => by simp [phiV_diag α hxy]) (fun g hg => by simp [phiV_noroot α hg])]
  have e1 : ∀ c : Fˣ, phiV α (scal c) * conj (phiV α (scal c)) = ((Nat.card F : ℂ) ^ 2 - 1) ^ 2 := by
    intro c
    rw [phiV_scal, map_mul]
    simp only [map_sub, map_pow, Complex.conj_natCast, map_one]
    linear_combination ((Nat.card F : ℂ) ^ 2 - 1) ^ 2 * conj_hom_mul_self α c
  have e2 : ∀ x : Fˣ, phiV α (upperUnit x 1) * conj (phiV α (upperUnit x 1)) = 1 := by
    intro x
    rw [phiV_upper, map_neg]
    linear_combination conj_hom_mul_self α x
  rw [Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_congr rfl fun x _ => e2 x, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, card_units_cast, cast_sq_sub_one,
    cast_card_G]
  ring

lemma sum_phiV_mul_conj_ext (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) :
    ∑ y, phiV α y * conj (extT h ν y) =
      ((Nat.card F : ℂ) ^ 2 - 1) * ((Fintype.card Fˣ : ℕ) : ℂ) := by
  have hpt : ∀ y : GL (Fin 2) F, phiV α y * conj (extT h ν y) =
      if ∃ c : Fˣ, y = scal c then phiV α y * conj (extT h ν y) else 0 := by
    intro y
    by_cases hs : ∃ c : Fˣ, y = scal c
    · rw [if_pos hs]
    · rw [if_neg hs]
      by_cases hy : y ∈ torus h
      · have h10 : (y : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h0 => hs (torus_scal_of_val10 h hy h0)
        rw [phiV_noroot α (fun l hl => h10 (torus_val10_of_root h hy l hl)), zero_mul]
      · rw [extT_of_not_mem h ν hy]; simp
  rw [Finset.sum_congr rfl fun y _ => hpt y, sum_ite_scalar]
  have e : ∀ c : Fˣ, phiV α (scal c) * conj (extT h ν (scal c)) = (Nat.card F : ℂ) ^ 2 - 1 := by
    intro c
    rw [extT_of_mem h ν (diag_mem_torus h c), hα, phiV_scal]
    linear_combination ((Nat.card F : ℂ) ^ 2 - 1) * conj_hom_mul_self α c
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma sum_Y_sq (ν : torus h →* ℂˣ) (hσ : ν.comp (sigmaT h) ≠ ν) :
    ∑ g, (torusInd h ν).character g * conj ((torusInd h ν).character g) =
      (Nat.card (GL (Fin 2) F) : ℂ) * ((Nat.card F : ℂ) - 1) := by
  have hK := natCard_torus_ne_zero h
  rw [sum_mul_conj_torusInd h ν (torusInd h ν).character (fun x g => (torusInd h ν).char_conj g x),
    sum_Y_mul_conj_ext h ν hσ]
  rw [card_cast_torus h] at hK ⊢
  rw [cast_N, card_units_cast]
  field_simp
  ring

lemma sum_phiV_Y (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) :
    ∑ g, phiV α g * conj ((torusInd h ν).character g) =
      (Nat.card (GL (Fin 2) F) : ℂ) * ((Nat.card F : ℂ) - 1) := by
  have hK := natCard_torus_ne_zero h
  rw [sum_mul_conj_torusInd h ν (phiV α) (phiV_conj α), sum_phiV_mul_conj_ext h α ν hα]
  rw [card_cast_torus h] at hK ⊢
  rw [card_units_cast]
  field_simp

/-- **Etingof et al., Lemma 4.72 (norm)**: the virtual character `W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν` has norm `1`,
where `ν` restricts to `α` on the scalars and `ν^σ ≠ ν` (`ν^q ≠ ν` in the book). -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem hermitianPairing_cuspChar (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hσ : ν.comp (sigmaT h) ≠ ν) :
    hermitianPairing (cuspChar h α ν) (cuspChar h α ν) = 1 := by
  have hG : (Nat.card (GL (Fin 2) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hpt : ∀ g, cuspChar h α ν g * conj (cuspChar h α ν g) =
      phiV α g * conj (phiV α g) - phiV α g * conj ((torusInd h ν).character g) -
        conj (phiV α g * conj ((torusInd h ν).character g)) +
        (torusInd h ν).character g * conj ((torusInd h ν).character g) := by
    intro g
    rw [cuspChar_eq]
    simp only [map_sub, map_mul, Complex.conj_conj]
    ring
  have hc : ∑ g, conj (phiV α g * conj ((torusInd h ν).character g)) =
      conj (∑ g, phiV α g * conj ((torusInd h ν).character g)) :=
    (map_sum (starRingEnd ℂ) _ _).symm
  unfold hermitianPairing
  rw [Finset.sum_congr rfl fun g _ => hpt g, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hc, sum_phiV_sq, sum_phiV_Y h α ν hα, sum_Y_sq h ν hσ]
  simp only [map_mul, map_sub, Complex.conj_natCast, map_one]
  field_simp
  ring

lemma cuspChar_scal (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (c : Fˣ) :
    cuspChar h α ν (scal c) = ((Nat.card F : ℂ) - 1) * α c := by
  rw [cuspChar_eq, phiV_scal, character_torusInd_scal h ν c, hα, cast_N]
  ring

/-- **Etingof et al., Lemma 4.72 (value at `1`)**: the virtual character has value `q - 1` at the identity. -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem cuspChar_one (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) :
    cuspChar h α ν 1 = (Nat.card F : ℂ) - 1 := by
  have := cuspChar_scal h α ν hα 1
  rw [scal_one, map_one] at this
  simpa using this

/-- The virtual character is a virtual character in the sense of Definition 4.26 (an integer combination of
characters of representations), as `χ_{W₁ ⊗ V} = χ_{V_{1,1}} χ_V - χ_V`. -/
theorem cuspChar_mem_virtualChars (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) :
    cuspChar h α ν ∈ virtualChars ℂ (GL (Fin 2) F) := by
  have hT := S4Table.character_mem_virtualChars
    (V := TensorProduct ℂ (coindV (borel F).subtype (lineRep (borelChar (1 : Fˣ →* ℂˣ) 1)))
      (coindV (borel F).subtype (lineRep (borelChar α 1))))
    ((principalSeries (F := F) 1 1).tprod (principalSeries (F := F) α 1))
  rw [Representation.char_tensor] at hT
  have hV : (principalSeries (F := F) α 1).character ∈ virtualChars ℂ (GL (Fin 2) F) :=
    S4Table.character_mem_virtualChars _
  have hY : (torusInd h ν).character ∈ virtualChars ℂ (GL (Fin 2) F) :=
    S4Table.character_mem_virtualChars _
  have hfun : cuspChar h α ν =
      (principalSeries (F := F) 1 1).character * (principalSeries (F := F) α 1).character -
        (2 : ℤ) • (principalSeries (F := F) α 1).character - (torusInd h ν).character := by
    funext g
    simp only [cuspChar, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, Pi.intCast_apply]
    push_cast
    ring
  rw [hfun]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hT (Submodule.smul_mem _ _ hV)) hY

lemma inv_eq_conj_of_mem_virtualChars {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {ζ : G → ℂ} (hζ : ζ ∈ virtualChars ℂ G) (g : G) : ζ g⁻¹ = conj (ζ g) := by
  obtain ⟨n, rfl⟩ := mem_virtualChars_iff.1 hζ
  simp only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, map_sum, map_mul, map_intCast,
    Pi.mul_apply, Pi.intCast_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  obtain ⟨X, hX⟩ := χ.2
  have : (χ : G → ℂ) = X.ρ.character := hX.symm
  rw [this, character_inv_eq_conj]

lemma pairing_eq_hermitianPairing {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {ζ : G → ℂ} (hζ : ζ ∈ virtualChars ℂ G) : pairing ζ ζ = hermitianPairing ζ ζ := by
  rw [pairing_apply, hermitianPairing]
  congr 1
  exact Finset.sum_congr rfl fun g _ => by rw [inv_eq_conj_of_mem_virtualChars hζ g]

open scoped ComplexOrder in
/-- **Etingof et al., §4.24.4 (conclusion)**: for a character `ν` of the nonsplit torus with `ν^σ ≠ ν` and
`ν` restricting to `α` on the scalars, the virtual character `W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν` is the character of
an irreducible representation of `GL_2(F_q)`; it has dimension `q - 1`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem cuspChar_mem_irrChars (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hσ : ν.comp (sigmaT h) ≠ ν) :
    cuspChar h α ν ∈ irrChars ℂ (GL (Fin 2) F) := by
  have hvirt := cuspChar_mem_virtualChars h α ν
  refine mem_irrChars_of_pairing_eq_one hvirt ?_ ?_
  · rw [pairing_eq_hermitianPairing hvirt]
    exact hermitianPairing_cuspChar h α ν hα hσ
  · rw [cuspChar_one h α ν hα, ← cast_pred]
    exact Nat.cast_pos.2 (Nat.sub_pos_of_lt (by
      have : 1 < Fintype.card F := Fintype.one_lt_card
      rwa [Nat.card_eq_fintype_card]))

/-- **Etingof et al., §4.24.4 (conclusion)**: an irreducible `(q-1)`-dimensional representation of `GL_2(F_q)`
with character `W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν`, for each character `ν` of the nonsplit torus with `ν^σ ≠ ν`
(and `α` its restriction to the scalars). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem exists_irrep_cuspidal (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hσ : ν.comp (sigmaT h) ≠ ν) :
    ∃ X : IrrRep ℂ (GL (Fin 2) F), X.ρ.character = cuspChar h α ν ∧
      finrank ℂ X.V = Nat.card F - 1 := by
  obtain ⟨X, hX0⟩ := cuspChar_mem_irrChars h α ν hα hσ
  have hX : X.ρ.character = cuspChar h α ν := hX0
  refine ⟨X, hX, ?_⟩
  have h1 : X.ρ.character 1 = finrank ℂ X.V := X.ρ.char_one
  rw [hX, cuspChar_one h α ν hα, ← cast_pred] at h1
  exact_mod_cast h1.symm

end Lemma472

/-! ### The Galois conjugation is the `q`-th power map -/

section FrobeniusPow

open Polynomial

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

lemma companion_sq : ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      t • ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) +
        n • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticElt, ellUnit, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma isUnit_companion_sub (c : F) :
    IsUnit (((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - c • (1 : Matrix (Fin 2) (Fin 2) F)) := by
  have : (((ellUnit h ⟨(-c, 1), fun h0 => one_ne_zero (congrArg Prod.snd h0)⟩ : GL (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) =
      ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ellipticElt, ellUnit] <;> ring
  rw [← this]
  exact (Units.isUnit _)

/-- The `q`-th power of the companion matrix is its Galois conjugate `t - C`. -/
lemma companion_pow_card : ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ Fintype.card F =
    t • (1 : Matrix (Fin 2) (Fin 2) F) -
      ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  set Cm : Matrix (Fin 2) (Fin 2) F := ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hCm
  obtain ⟨q, hq⟩ : ∃ q, q = Fintype.card F := ⟨_, rfl⟩
  have hq0 : q ≠ 0 := hq ▸ Fintype.card_ne_zero
  have hexp : ∀ P : F[X], expand F q P = P ^ q := fun P => by
    rw [hq]; exact FiniteField.Polynomial.expand_card P
  rw [← hq]
  set Q : F[X] := X ^ 2 - C t * X + C n with hQ
  have hQ0 : aeval (R := F) Cm Q = 0 := by
    have := companion_sq h
    simpa [hQ, Algebra.algebraMap_eq_smul_one, ← hCm, sq] using this
  have hD0 : aeval (R := F) Cm (X ^ q) * aeval (R := F) Cm (X ^ q) - t • aeval (R := F) Cm (X ^ q) + n • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have h1 : aeval (R := F) Cm (expand F q Q) = 0 := by
      rw [hexp, map_pow, hQ0, zero_pow hq0]
    have h2 : expand F q Q = (X ^ q) ^ 2 - C t * X ^ q + C n := by
      simp [hQ, expand_X]
    rw [h2] at h1
    simpa [Algebra.algebraMap_eq_smul_one, sq] using h1
  have hpoly : (X ^ q - X : F[X]) * (X ^ q - (C t - X)) =
      ((X ^ q) ^ 2 - C t * X ^ q + C n) - Q := by rw [hQ]; ring
  have hprod : (aeval (R := F) Cm (X ^ q - X)) * (aeval (R := F) Cm (X ^ q - (C t - X))) = 0 := by
    rw [← map_mul, hpoly, map_sub, hQ0, sub_zero]
    simpa [Algebra.algebraMap_eq_smul_one, sq] using hD0
  have hDm : aeval (R := F) Cm (X ^ q) = Cm ^ q := by simp
  -- the power lies in the torus
  have hw : (ellipticElt h : GL (Fin 2) F) ^ q ∈ torus h :=
    pow_mem (Subgroup.mem_centralizer_iff.2 fun k hk => by rw [Set.mem_singleton_iff] at hk; rw [hk]) q
  obtain ⟨a', b', hab', hwa⟩ := torus_entries h hw
  have hwv : (((ellipticElt h : GL (Fin 2) F) ^ q : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Cm ^ q := by
    rw [Units.val_pow_eq_pow_val]
  rw [hwv] at hwa
  by_cases hne : Cm ^ q = Cm
  · exfalso
    have h0 : aeval (R := F) Cm (X ^ q - X : F[X]) = 0 := by simp [hne]
    have hP : (X ^ q - X : F[X]) = ∏ c : F, (X - C c) := by
      have hm : (X ^ q - X : F[X]).Monic := monic_X_pow_sub (by
        rw [degree_X]; exact_mod_cast (by
          have := Fintype.one_lt_card (α := F); omega : 1 < q))
      have hr := FiniteField.roots_X_pow_card_sub_X F
      rw [← hq] at hr
      have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [hr, Finset.card_val, Finset.card_univ, ← hq]
        rw [hq]
        exact (FiniteField.X_pow_card_sub_X_natDegree_eq (R := F) Fintype.one_lt_card).symm)
      rw [hr] at this
      exact this.symm
    have hU : ∀ s : Finset F, IsUnit (aeval (R := F) Cm (∏ c ∈ s, (X - C c))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert c s hc ih =>
        rw [Finset.prod_insert hc, map_mul]
        refine IsUnit.mul ?_ ih
        simpa [Algebra.algebraMap_eq_smul_one, ← hCm] using isUnit_companion_sub h c
    rw [hP] at h0
    have := hU Finset.univ
    rw [h0] at this
    exact not_isUnit_zero this
  · have hp : ((a', b' - 1) : F × F) ≠ 0 := by
      intro h0
      apply hne
      have e1 : a' = 0 := congrArg Prod.fst h0
      have e2 : b' = 1 := sub_eq_zero.1 (congrArg Prod.snd h0)
      rw [hwa, e1, e2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hCm, ellipticElt, ellUnit]
    have hU : IsUnit (aeval (R := F) Cm (X ^ q - X : F[X])) := by
      have : aeval (R := F) Cm (X ^ q - X : F[X]) = (ellUnit h ⟨(a', b' - 1), hp⟩ : GL (Fin 2) F) := by
        simp only [map_sub, hDm, aeval_X]
        rw [hwa]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hCm, ellipticElt, ellUnit] <;> ring
      rw [this]; exact Units.isUnit _
    have := (hU.mul_right_eq_zero).1 hprod
    simp only [map_sub, hDm, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] at this
    exact this

/-- **The Galois conjugation of the nonsplit torus is the `q`-th power map**: `z^σ = z^q`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem sigmaT_eq_pow (z : torus h) : sigmaT h z = z ^ Nat.card F := by
  obtain ⟨a, b, -, hza⟩ := torus_entries h z.2
  set Cm : Matrix (Fin 2) (Fin 2) F := ((ellipticElt h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hCm
  have hZ : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Cm := by
    rw [hza]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hCm, ellipticElt, ellUnit]
  have hZa : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =aeval (R := F) Cm (C a + C b * X) := by
    rw [hZ]; simp [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  apply Units.ext
  have hpow : ((z ^ Nat.card F : torus h) : GL (Fin 2) F).val =
      (aeval (R := F) Cm (C a + C b * X)) ^ Fintype.card F := by
    rw [← hZa, Nat.card_eq_fintype_card, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rw [show (((sigmaT h z : torus h) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _ from
    congrArg Units.val (coe_sigmaT h z)]
  rw [hpow, ← map_pow, ← FiniteField.Polynomial.expand_card]
  simp only [map_add, map_mul, expand_C, expand_X, map_pow, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one]
  rw [companion_pow_card h, val_adjG, hza]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hCm, ellipticElt, ellUnit] <;> ring

/-- The character `ν^q : z ↦ ν(z)^q` of the nonsplit torus. -/
noncomputable def nuPow (ν : torus h →* ℂˣ) : torus h →* ℂˣ := (powMonoidHom (Nat.card F)).comp ν

lemma nuPow_apply (ν : torus h →* ℂˣ) (z : torus h) : nuPow h ν z = ν z ^ Nat.card F := rfl

/-- `ν ∘ σ` is the book's `ν^q`. -/
theorem comp_sigmaT_eq_nuPow (ν : torus h →* ℂˣ) : ν.comp (sigmaT h) = nuPow h ν := by
  ext z
  simp [nuPow, sigmaT_eq_pow]

/-- **Etingof et al., §4.24.4**: `Y_ν ≅ Y_{ν^q}` with `ν^q(z) = ν(z)^q`. -/
@[kb "etingof2011" "§4.24.4, p. 73"]
theorem nonempty_equiv_torusInd_nuPow (ν : torus h →* ℂˣ) :
    Nonempty (Representation.Equiv (torusInd h ν) (torusInd h (nuPow h ν))) := by
  rw [← comp_sigmaT_eq_nuPow]; exact nonempty_equiv_torusInd_comp_sigma h ν

/-- **Etingof et al., §4.24.4 (conclusion)**: for `ν` restricting to `α` on the scalars with `ν^q ≠ ν`,
there is an irreducible `(q-1)`-dimensional representation with character
`W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem exists_irrep_cuspidal_nuPow (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hq : nuPow h ν ≠ ν) :
    ∃ X : IrrRep ℂ (GL (Fin 2) F), X.ρ.character = cuspChar h α ν ∧
      finrank ℂ X.V = Nat.card F - 1 :=
  exists_irrep_cuspidal h α ν hα (by rw [comp_sigmaT_eq_nuPow]; exact hq)

/-- **Etingof et al., Lemma 4.72** with `ν^q`: the virtual character has norm `1`. -/
@[kb "etingof2011" "Lemma 4.72, p. 74"]
theorem hermitianPairing_cuspChar_nuPow (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ)
    (hα : ∀ c : Fˣ, ν ⟨scal c, diag_mem_torus h c⟩ = α c) (hq : nuPow h ν ≠ ν) :
    hermitianPairing (cuspChar h α ν) (cuspChar h α ν) = 1 :=
  hermitianPairing_cuspChar h α ν hα (by rw [comp_sigmaT_eq_nuPow]; exact hq)

end FrobeniusPow

end UndergradKB.RepresentationTheory.GL2
