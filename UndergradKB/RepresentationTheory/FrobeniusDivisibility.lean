import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import UndergradKB.RepresentationTheory.Characters

/-! # Frobenius divisibility (Etingof et al., §4.4)

`G` a finite group, `k` an algebraically closed field of characteristic zero (the book works over `ℂ`), `V` an
irreducible finite-dimensional representation with character `χ`.

* Proposition 4.17: for `g ∈ G` with conjugacy class `C`, the number `|C| χ(g) / dim V` is an algebraic integer.
* Theorem 4.16 (Frobenius divisibility): `dim V` divides `|G|`.

The proof is the book's. The class sum `z_C = ∑_{x ∈ C} x` is central in `ℤ[G]`, so acts on `V` by a scalar
`ω_C = |C| χ(g) / dim V`; the image of the centre of `ℤ[G]` in `End V` is a finitely generated `ℤ`-module, so the
`ω_C` are algebraic integers. Then `|G| / dim V = ∑_C ω_C χ(g_C⁻¹)` is an algebraic integer and a rational number,
hence an integer.
-/

namespace UndergradKB.RepresentationTheory

open Representation MonoidAlgebra Module

open scoped Classical

section ClassSum

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
theorem isConj_conj_iff (c x h : G) : IsConj (c * x * c⁻¹) h ↔ IsConj x h :=
  ⟨fun H ↦ (isConj_iff.mpr ⟨c, rfl⟩).trans H, fun H ↦ (isConj_iff.mpr ⟨c, rfl⟩).symm.trans H⟩

/-- The size of the conjugacy class of `h`. -/
noncomputable def conjCard (h : G) : ℕ := (Finset.univ.filter (IsConj · h)).card

theorem conjCard_pos (h : G) : 0 < conjCard h :=
  Finset.card_pos.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl h⟩⟩

theorem conjCard_eq_of_isConj {x y : G} (hxy : IsConj x y) : conjCard x = conjCard y := by
  unfold conjCard
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun H ↦ H.trans hxy, fun H ↦ H.trans hxy.symm⟩

/-- The sum of the elements of the conjugacy class of `h`, in the integral group ring. -/
noncomputable def classSum (h : G) : MonoidAlgebra ℤ G :=
  ∑ x : G, if IsConj x h then of ℤ G x else 0

theorem classSum_mem_center (h : G) : classSum h ∈ Subalgebra.center ℤ (MonoidAlgebra ℤ G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [classSum, Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul, ← map_mul]
    refine Fintype.sum_equiv (MulAut.conj g) _ _ (fun x ↦ ?_)
    show _ = if IsConj (g * x * g⁻¹) h then of ℤ G (g * x * g⁻¹ * g) else 0
    simp only [isConj_conj_iff, inv_mul_cancel_right]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- Grouping a sum over `G` by conjugacy classes. -/
theorem sum_div_conjCard {k : Type*} [Field k] [CharZero k] (F : G → k)
    (hF : ∀ x y, IsConj x y → F x = F y) :
    ∑ g : G, F g / conjCard g = ∑ C : ConjClasses G, F C.exists_rep.choose := by
  rw [← Finset.sum_fiberwise Finset.univ ConjClasses.mk (fun g ↦ F g / conjCard g)]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  set r := C.exists_rep.choose
  have hr : ConjClasses.mk r = C := C.exists_rep.choose_spec
  have hmem : ∀ x, ConjClasses.mk x = C ↔ IsConj x r := fun x ↦ by
    rw [← hr, ConjClasses.mk_eq_mk_iff_isConj]
  have hconst : ∀ x ∈ Finset.univ.filter (fun x ↦ ConjClasses.mk x = C),
      F x / conjCard x = F r / conjCard r := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem] at hx
    rw [hF x r hx, conjCard_eq_of_isConj hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun x ↦ ConjClasses.mk x = C)).card = conjCard r := by
    unfold conjCard
    congr 1
    ext x
    simp [hmem]
  rw [hcard]
  have : (conjCard r : k) ≠ 0 := Nat.cast_ne_zero.mpr (conjCard_pos r).ne'
  field_simp

end ClassSum

variable {k G V : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsIrreducible ρ]

/-- The action of the integral group ring on `V`. -/
noncomputable abbrev intAction : MonoidAlgebra ℤ G →ₐ[ℤ] Module.End k V :=
  MonoidAlgebra.lift ℤ (Module.End k V) G ρ

theorem isIntegral_intAction {z : MonoidAlgebra ℤ G} (hz : z ∈ Subalgebra.center ℤ (MonoidAlgebra ℤ G)) :
    IsIntegral ℤ (intAction ρ z) := by
  let S := (Subalgebra.center ℤ (MonoidAlgebra ℤ G)).map (intAction ρ)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    rw [Subalgebra.map_toSubmodule]
    exact (IsNoetherian.noetherian _).map _
  exact IsIntegral.of_mem_of_fg S hfg _ ⟨z, hz, rfl⟩

omit [CharZero k] [FiniteDimensional k V] [IsIrreducible ρ] in
theorem intAction_comm {z : MonoidAlgebra ℤ G} (hz : z ∈ Subalgebra.center ℤ (MonoidAlgebra ℤ G)) (g : G) :
    intAction ρ z ∘ₗ ρ g = ρ g ∘ₗ intAction ρ z := by
  have h1 : intAction ρ (of ℤ G g) = ρ g := by simp [intAction]
  rw [← h1, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
    Subalgebra.mem_center_iff.mp hz]

include ρ in
theorem finrank_ne_zero' : (finrank k V : k) ≠ 0 := by
  have : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact finrank_ne_zero_of_isIrreducible (ρ := ρ)

/-- **Etingof et al., Proposition 4.17**: for an irreducible representation `V` with character `χ` and an element
`h` whose conjugacy class has `|C|` elements, `|C| χ(h) / dim V` is an algebraic integer. -/
@[kb "etingof2011" "Proposition 4.17, p. 51"]
theorem isIntegral_conjCard_mul_character_div (h : G) :
    IsIntegral ℤ ((conjCard h : k) * ρ.character h / finrank k V) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute _ (intAction_comm ρ (classSum_mem_center h))
  have hint := isIntegral_intAction ρ (classSum_mem_center h)
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero fun h0 ↦ finrank_ne_zero' ρ (by rw [h0, Nat.cast_zero]))
  have hc' : intAction ρ (classSum h) = algebraMap k (Module.End k V) c := by
    rw [hc, Module.algebraMap_end_eq_smul_id]
  rw [hc', ← Algebra.ofId_apply,
    ← AlgHom.coe_restrictScalars' ℤ (Algebra.ofId k (Module.End k V)),
    isIntegral_algHom_iff _ (algebraMap k (Module.End k V)).injective] at hint
  have htr := congrArg (LinearMap.trace k V) hc
  rw [map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  have hsum : LinearMap.trace k V (intAction ρ (classSum h)) = conjCard h * ρ.character h := by
    simp only [classSum, map_sum]
    rw [Finset.sum_congr rfl (g := fun x ↦ if IsConj x h then ρ.character h else 0)]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rfl
    · intro x _
      split_ifs with hx
      · obtain ⟨c, hc⟩ := isConj_iff.mp hx
        simp only [intAction, lift_of, ← hc, char_conj]
        rfl
      · simp
  rw [hsum] at htr
  have : (conjCard h : k) * ρ.character h / finrank k V = c := by
    rw [htr, mul_div_cancel_right₀ _ (finrank_ne_zero' ρ)]
  rw [this]
  exact hint

include ρ in
/-- **Etingof et al., Theorem 4.16** (Frobenius divisibility): the dimension of an irreducible representation of a
finite group over an algebraically closed field of characteristic zero divides the order of the group. -/
@[kb "etingof2011" "Theorem 4.16, p. 51"]
theorem finrank_dvd_card : finrank k V ∣ Fintype.card G := by
  have hd := finrank_ne_zero' ρ
  have : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `∑ χ(g) χ(g⁻¹) = |G|`
  have horth : ∑ g : G, ρ.character g * ρ.character g⁻¹ = Fintype.card G := by
    have := char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩, inv_mul_eq_one₀ (NeZero.ne _)] at this
    rw [← this, Nat.card_eq_fintype_card]
  let F : G → k := fun g ↦ (conjCard g : k) * ρ.character g / finrank k V * ρ.character g⁻¹
  have hF : ∀ x y, IsConj x y → F x = F y := by
    intro x y hxy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    simp only [F, conjCard_eq_of_isConj hxy, char_conj, mul_inv_rev, inv_inv, ← mul_assoc]
  have key : (Fintype.card G : k) / finrank k V = ∑ C : ConjClasses G, F C.exists_rep.choose := by
    rw [← sum_div_conjCard F hF, ← horth, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    have : (conjCard g : k) ≠ 0 := Nat.cast_ne_zero.mpr (conjCard_pos g).ne'
    simp only [F]
    field_simp
  have hint : IsIntegral ℤ ((Fintype.card G : k) / finrank k V) := by
    rw [key]
    refine IsIntegral.sum _ fun C _ ↦ ?_
    exact (isIntegral_conjCard_mul_character_div ρ _).mul (isIntegral_character ρ _)
  have hq : algebraMap ℚ k (Fintype.card G / finrank k V : ℚ) = (Fintype.card G : k) / finrank k V := by
    simp
  rw [← hq, ← Algebra.ofId_apply, ← AlgHom.coe_restrictScalars' ℤ (Algebra.ofId ℚ k),
    isIntegral_algHom_iff _ (algebraMap ℚ k).injective, IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨n, hn⟩ := hint
  have hd0 : finrank k V ≠ 0 := fun h0 ↦ hd (by rw [h0, Nat.cast_zero])
  have hd' : (finrank k V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  rw [eq_div_iff hd'] at hn
  rw [algebraMap_int_eq, eq_intCast] at hn
  have hz : (n * finrank k V : ℤ) = Fintype.card G := by exact_mod_cast hn
  exact Int.natCast_dvd_natCast.mp ⟨n, by rw [← hz, mul_comm]⟩

end UndergradKB.RepresentationTheory
