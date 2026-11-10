import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex
import UndergradKB.Common.Attr

/-!
# The dihedral group as the symmetry group of a regular polygon

The regular `n`-gon in the complex plane has the `n`-th roots of unity as vertices.  Its rigid
motions are the isometries of `ℂ` mapping the vertex set onto itself.  We show that this group
is isomorphic to Mathlib's abstract `DihedralGroup n` (for `n ≥ 3`, in fact for `n ≥ 2`) and has
`2 * n` elements.
-/

namespace UndergradKB.AbstractAlgebra

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The vertices of the regular `n`-gon: the `n`-th roots of unity in the complex plane. -/
def polygonVertices (n : ℕ) : Set ℂ := {z | z ^ n = 1}

/-- The rigid motions of the regular `n`-gon: isometries of the plane preserving its vertex set. -/
def polygonSymmetries (n : ℕ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | ∀ z, z ∈ polygonVertices n ↔ f z ∈ polygonVertices n}
  mul_mem' := by
    intro f g hf hg z
    exact (hg z).trans (hf (g z))
  one_mem' := fun z => Iff.rfl
  inv_mem' := by
    intro f hf z
    have := hf (f.symm z)
    rw [f.apply_symm_apply] at this
    exact this.symm

/-- Rotation of the plane by a unit complex number, as an isometry. -/
def rotIso (a : Circle) : ℂ ≃ᵢ ℂ := (rotation a).toIsometryEquiv

/-- Reflection `z ↦ a * conj z`, as an isometry. -/
def refIso (a : Circle) : ℂ ≃ᵢ ℂ := (conjLIE.trans (rotation a)).toIsometryEquiv

@[simp] lemma rotIso_apply (a : Circle) (z : ℂ) : rotIso a z = a * z := rfl

@[simp] lemma refIso_apply (a : Circle) (z : ℂ) : refIso a z = a * conj z := rfl

lemma toCircle_pow_card (n : ℕ) [NeZero n] (i : ZMod n) :
    ((ZMod.toCircle i : Circle) : ℂ) ^ n = 1 := by
  have : (ZMod.toCircle i : Circle) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]; simp
  rw [← Circle.coe_pow, this]; rfl

lemma rotIso_mem (n : ℕ) (a : Circle) (ha : (a : ℂ) ^ n = 1) :
    rotIso a ∈ polygonSymmetries n := by
  intro z
  simp [polygonVertices, mul_pow, ha]

lemma refIso_mem (n : ℕ) (a : Circle) (ha : (a : ℂ) ^ n = 1) :
    refIso a ∈ polygonSymmetries n := by
  intro z
  simp only [polygonVertices, Set.mem_ofPred_eq, refIso_apply, mul_pow, ha, one_mul]
  rw [← map_pow]
  exact (map_eq_one_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).symm

variable {n : ℕ} [NeZero n]

lemma conj_toCircle (a : ZMod n) :
    conj ((ZMod.toCircle a : Circle) : ℂ) = ((ZMod.toCircle (-a) : Circle) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- The set-theoretic map from the abstract dihedral group to the symmetry group. -/
def dihedralToSym : DihedralGroup n → polygonSymmetries n
  | .r i => ⟨rotIso (ZMod.toCircle i), rotIso_mem n _ (toCircle_pow_card n i)⟩
  | .sr i => ⟨refIso (ZMod.toCircle (-i)), refIso_mem n _ (toCircle_pow_card n _)⟩

lemma dihedralToSym_mul (x y : DihedralGroup n) :
    dihedralToSym (x * y) = dihedralToSym x * dihedralToSym y := by
  cases x <;> cases y <;>
  · apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    simp [dihedralToSym, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, AddChar.map_add_eq_mul, sub_eq_add_neg, mul_assoc, conj_toCircle]
    try ring

/-- The homomorphism from the abstract dihedral group to the rigid motions of the polygon. -/
def dihedralHom : DihedralGroup n →* polygonSymmetries n :=
  MonoidHom.mk' dihedralToSym dihedralToSym_mul

lemma dihedralHom_injective : Function.Injective (dihedralHom (n := n)) := by
  have hr : ∀ i j : ZMod n, dihedralToSym (.r i) = dihedralToSym (.r j) → i = j := by
    intro i j h
    have := congrArg (fun f : polygonSymmetries n => (f : ℂ ≃ᵢ ℂ) 1) h
    simp [dihedralToSym] at this
    exact ZMod.injective_toCircle (Subtype.ext this)
  have hs : ∀ i j : ZMod n, dihedralToSym (.sr i) = dihedralToSym (.sr j) → i = j := by
    intro i j h
    have := congrArg (fun f : polygonSymmetries n => (f : ℂ ≃ᵢ ℂ) 1) h
    simp [dihedralToSym] at this
    exact neg_injective (ZMod.injective_toCircle (Subtype.ext this))
  have hrs : ∀ i j : ZMod n, dihedralToSym (.r i) ≠ dihedralToSym (.sr j) := by
    intro i j h
    have h1 := congrArg (fun f : polygonSymmetries n => (f : ℂ ≃ᵢ ℂ) 1) h
    have h2 := congrArg (fun f : polygonSymmetries n => (f : ℂ ≃ᵢ ℂ) I) h
    simp [dihedralToSym] at h1 h2
    rw [h1] at h2
    have hb : ((ZMod.toCircle (-j) : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    apply hb
    have h3 : (2 * I) * ((ZMod.toCircle (-j) : Circle) : ℂ) = 0 := by linear_combination h2
    simpa [Complex.I_ne_zero] using h3
  intro x y h
  have h' : dihedralToSym x = dihedralToSym y := h
  cases x <;> cases y
  · exact congrArg _ (hr _ _ h')
  · exact absurd h' (hrs _ _)
  · exact absurd h'.symm (hrs _ _)
  · exact congrArg _ (hs _ _ h')

lemma vertex_iff_exists (hn : 2 ≤ n) (z : ℂ) :
    z ∈ polygonVertices n ↔ ∃ i : ZMod n, ((ZMod.toCircle i : Circle) : ℂ) = z := by
  constructor
  · intro hz
    have hprim : IsPrimitiveRoot ((ZMod.toCircle (1 : ZMod n) : Circle) : ℂ) n := by
      have := ZMod.toCircle_natCast (N := n) 1
      simp only [Nat.cast_one, mul_one] at this
      rw [this]
      exact Complex.isPrimitiveRoot_exp n NeZero.out
    obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hz
    refine ⟨(k : ZMod n), ?_⟩
    rw [← hk, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow]
    simp
  · rintro ⟨i, rfl⟩
    exact toCircle_pow_card n i

/-- An isometry preserving the vertex set fixes the centre, the centroid of the vertices. -/
lemma fix_zero (hn : 2 ≤ n) (f : ℂ ≃ᵢ ℂ) (hf : f ∈ polygonSymmetries n) : f 0 = 0 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  let S : Finset ℂ := Finset.univ.image (ZMod.stdAddChar (N := n))
  have hS : ∀ z, z ∈ S ↔ z ^ n = 1 := by
    intro z
    have e : z ^ n = 1 ↔ z ∈ polygonVertices n := Iff.rfl
    rw [e, vertex_iff_exists hn]
    simp [S, ZMod.stdAddChar_apply]
  have hsumS : ∑ z ∈ S, z = 0 := by
    rw [Finset.sum_image (fun a _ b _ h => ZMod.injective_stdAddChar h)]
    apply AddChar.sum_eq_zero_of_ne_one
    intro h
    have h1 : ZMod.stdAddChar (N := n) 1 = ZMod.stdAddChar (N := n) 0 := by
      rw [h]; simp
    exact one_ne_zero (ZMod.injective_stdAddChar h1)
  have himage : S.image f = S := by
    ext w
    rw [Finset.mem_image, hS]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hf z).mp ((hS z).mp hz)
    · intro hw
      refine ⟨f.symm w, (hS _).mpr ?_, f.apply_symm_apply w⟩
      have := hf (f.symm w)
      rw [f.apply_symm_apply] at this
      exact this.mpr hw
  have hsum : ∑ z ∈ S, f z = 0 := by
    calc ∑ z ∈ S, f z = ∑ w ∈ S.image f, w :=
          (Finset.sum_image (f := fun w : ℂ => w) (g := f) (fun a _ b _ h => f.injective h)).symm
      _ = 0 := by rw [himage, hsumS]
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ ZMod.injective_stdAddChar]
    simp
  let h : ℂ →ᵃ[ℝ] ℂ := f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
  have hh : ∀ z, f z = h.linear z + f 0 := by
    intro z
    have := congrFun (AffineMap.decomp h) z
    have e : (h : ℂ → ℂ) = f := by
      ext x; simp [h]
    simpa [e] using this
  have key : ∑ z ∈ S, f z = n • f 0 := by
    rw [Finset.sum_congr rfl (fun z _ => hh z), Finset.sum_add_distrib, ← map_sum, hsumS]
    simp [hcard]
  rw [hsum] at key
  rcases smul_eq_zero.mp key.symm with h0 | h0
  · exact absurd h0 (NeZero.ne n)
  · exact h0

lemma dihedralHom_surjective (hn : 2 ≤ n) : Function.Surjective (dihedralHom (n := n)) := by
  rintro ⟨f, hf⟩
  have h0 := fix_zero hn f hf
  obtain ⟨a, ha⟩ := linear_isometry_complex (f.toRealLinearIsometryEquivOfMapZero h0)
  have hfz : ∀ z, f z = (f.toRealLinearIsometryEquivOfMapZero h0) z := fun z => rfl
  have h1 : (a : ℂ) ^ n = 1 := by
    have := (hf 1).mp (by simp [polygonVertices])
    rcases ha with ha | ha
    · rw [hfz, ha] at this
      simpa [polygonVertices] using this
    · rw [hfz, ha] at this
      simpa [polygonVertices] using this
  obtain ⟨k, hk⟩ := (vertex_iff_exists hn (a : ℂ)).mp h1
  have hka : ZMod.toCircle k = a := Subtype.ext hk
  rcases ha with ha | ha
  · refine ⟨DihedralGroup.r k, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change rotIso (ZMod.toCircle k) z = f z
    rw [hfz, ha, hka]
    simp
  · refine ⟨DihedralGroup.sr (-k), ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change refIso (ZMod.toCircle (-(-k))) z = f z
    rw [hfz, ha, neg_neg, hka]
    simp

/-- The isomorphism `D_n ≃* (rigid motions of the regular n-gon)`, for `n ≥ 2`. -/
def dihedralEquivPolygonSymmetries (hn : 2 ≤ n) : DihedralGroup n ≃* polygonSymmetries n :=
  MulEquiv.ofBijective dihedralHom ⟨dihedralHom_injective, dihedralHom_surjective hn⟩

end

/-- AA-074. For `n ≥ 3`, the group of rigid motions of the regular `n`-gon (isometries of the
plane preserving the vertex set, the `n`-th roots of unity) is isomorphic to the dihedral group
`D_n`, and has `2 * n` elements. -/
@[kb "judson2026" "Definition (unnumbered) dihedral group, p. 79"]
theorem polygonSymmetries_equiv_dihedral (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (polygonSymmetries n ≃* DihedralGroup n) ∧ Nat.card (polygonSymmetries n) = 2 * n := by
  haveI : NeZero n := ⟨by omega⟩
  have e := dihedralEquivPolygonSymmetries (n := n) (by omega)
  exact ⟨⟨e.symm⟩, by rw [Nat.card_congr e.symm.toEquiv, DihedralGroup.nat_card]⟩

end UndergradKB.AbstractAlgebra
