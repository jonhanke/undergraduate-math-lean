import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Fixed
import UndergradKB.Common.Attr

/-!
# Radical extensions and normal closures

Intermediate fields of a fixed field `L ⊇ F` that are obtained from `F` by a finite tower of adjunctions of
roots (`α ^ n` lies in the previous field, `n ≥ 1`) are called radical (`IsRadical`). We show that radicality is
preserved by algebra homomorphisms and by compositums, and that the normal closure of a finite radical
extension inside a normal extension `L / F` is radical and normal.
-/

namespace UndergradKB.AbstractAlgebra

open IntermediateField

variable {F L L' : Type*} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']

/-- Radical intermediate fields: `F` itself, and `K(α)` whenever `K` is radical and `α ^ n ∈ K`, `n ≥ 1`. -/
inductive IsRadical (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L] :
    IntermediateField F L → Prop
  | bot : IsRadical F ⊥
  | step {K : IntermediateField F L} (hK : IsRadical F K) (α : L) (n : ℕ) (hn : 0 < n)
      (hα : α ^ n ∈ K) : IsRadical F (K ⊔ F⟮α⟯)

/-- The image of a radical intermediate field under an `F`-algebra homomorphism is radical. -/
theorem IsRadical.map {K : IntermediateField F L} (h : IsRadical F K) (φ : L →ₐ[F] L') :
    IsRadical F (K.map φ) := by
  induction h with
  | bot =>
    have : (⊥ : IntermediateField F L).map φ = ⊥ := by
      ext x
      simp only [mem_map, mem_bot]
      constructor
      · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, by simp⟩
      · rintro ⟨r, rfl⟩
        exact ⟨algebraMap F L r, ⟨r, rfl⟩, by simp⟩
    rw [this]; exact IsRadical.bot
  | @step K hK α n hn hα ih =>
    have h1 : (F⟮α⟯).map φ = F⟮φ α⟯ := by
      rw [adjoin_map, Set.image_singleton]
    rw [IntermediateField.map_sup, h1]
    refine IsRadical.step ih (φ α) n hn ?_
    rw [← map_pow]
    exact ⟨_, hα, rfl⟩

/-- The compositum of two radical intermediate fields is radical. -/
theorem IsRadical.sup {K E : IntermediateField F L} (hK : IsRadical F K) (hE : IsRadical F E) :
    IsRadical F (K ⊔ E) := by
  induction hE with
  | bot => simpa using hK
  | @step E hE α n hn hα ih =>
    rw [← sup_assoc]
    exact IsRadical.step ih α n hn (le_sup_right (a := K) hα)

/-- A finite compositum of radical intermediate fields is radical. -/
theorem IsRadical.iSup {ι : Type*} [Finite ι] {K : ι → IntermediateField F L}
    (h : ∀ i, IsRadical F (K i)) : IsRadical F (⨆ i, K i) := by
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup]
  exact Finset.sup_induction IsRadical.bot (fun _ ha _ hb => ha.sup hb) (fun i _ => h i)

/-- Helper: each embedding of a radical `E` into a normal `L` has radical range. -/
theorem IsRadical.fieldRange_of_normal [Normal F L] {E : IntermediateField F L} (h : IsRadical F E)
    (f : E →ₐ[F] L) : IsRadical F f.fieldRange := by
  let τ : L →ₐ[F] L := f.liftNormal L
  have hτ : ∀ x : E, τ x = f x := fun x => f.liftNormal_commutes L x
  have : f.fieldRange = E.map τ := by
    ext y
    simp only [AlgHom.mem_fieldRange, mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hτ x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hτ ⟨x, hx⟩).symm⟩
  rw [this]
  exact h.map τ

/-- AA-441. Lemma 23.3.3: if `E / F` is a finite radical extension inside a normal extension `L / F`,
then the normal closure of `E` in `L` is a normal extension of `F` containing `E` that is radical. -/
@[kb "judson2026" "Lemma 23.3.3, p. 329"]
theorem isRadical_normalClosure [Normal F L] (E : IntermediateField F L) [FiniteDimensional F E]
    (h : IsRadical F E) :
    IsRadical F (normalClosure F E L) ∧ Normal F (normalClosure F E L) ∧ E ≤ normalClosure F E L := by
  refine ⟨?_, inferInstance, le_normalClosure E⟩
  rw [normalClosure_def]
  exact IsRadical.iSup fun f => h.fieldRange_of_normal f

end UndergradKB.AbstractAlgebra
