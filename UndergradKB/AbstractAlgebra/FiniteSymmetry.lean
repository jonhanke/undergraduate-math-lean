import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.LinearAlgebra.UnitaryGroup
import UndergradKB.AbstractAlgebra.MatrixGroups
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 12: finite subgroups of `O(2)`

Theorem 12.2.4: a finite group of symmetries fixing the origin of the plane is cyclic or
dihedral. We prove it for finite subgroups of `O(2)`. The rotation part (determinant `1`) of such
a group is cyclic, since the rotations embed in `ℂ` by `A ↦ A₀₀ + A₁₀ i`; if the group contains a
reflection, the rotation part has index two and the group is dihedral. -/

namespace UndergradKB.AbstractAlgebra

open Matrix

section Core

variable {G : Type*} [Group G]

/-- Abstract dihedral criterion: if `H` is a finite cyclic subgroup of the finite group `G`, `s`
is outside `H`, every element outside `H` squares to `1`, and `s⁻¹ x ∈ H` for each `x ∉ H`, then
`G` is dihedral of order `2 * |H|`. -/
theorem dihedral_of_index_two [Finite G] (H : Subgroup G) [IsCyclic H] (s : G) (hs : s ∉ H)
    (hsq : ∀ x, x ∉ H → x * x = 1) (hcov : ∀ x, x ∉ H → s⁻¹ * x ∈ H) :
    ∃ n : ℕ, n = Nat.card H ∧ 0 < n ∧ Nonempty (G ≃* DihedralGroup n) := by
  have hn : 0 < Nat.card H := Nat.card_pos
  set n := Nat.card H with hn_def
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨n, rfl, hn, ?_⟩
  let e : Multiplicative (ZMod n) ≃* H := zmodCyclicMulEquiv inferInstance
  let c : ZMod n → G := fun a => (e (Multiplicative.ofAdd a) : G)
  have hc_add : ∀ a b, c (a + b) = c a * c b := by
    intro a b
    simp [c]
  have hc_neg : ∀ a, c (-a) = (c a)⁻¹ := by
    intro a
    simp [c]
  have hc_inj : Function.Injective c := by
    intro a b hab
    have := e.injective (Subtype.ext hab)
    exact this
  have hc_mem : ∀ a, c a ∈ H := fun a => (e (Multiplicative.ofAdd a)).2
  have hc_surj : ∀ x ∈ H, ∃ a, c a = x := by
    intro x hx
    obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
    exact ⟨Multiplicative.toAdd a, by simpa [c] using congrArg Subtype.val ha⟩
  have hss : s * s = 1 := hsq s hs
  have hsc : ∀ a, s * c a * s = c (-a) := by
    intro a
    have hnot : s * c a ∉ H := by
      intro h
      apply hs
      have := H.mul_mem h (H.inv_mem (hc_mem a))
      simpa using this
    have h := hsq _ hnot
    have h2 : (s * c a * s) * c a = 1 := by
      rw [← h]; simp only [mul_assoc]
    rw [hc_neg]
    exact mul_eq_one_iff_eq_inv.mp h2
  have hcs : ∀ a, c a * s = s * c (-a) := by
    intro a
    calc c a * s = s * (s * c a * s) := by
          rw [← mul_assoc, ← mul_assoc, hss, one_mul]
      _ = s * c (-a) := by rw [hsc]
  let f : DihedralGroup n → G
    | DihedralGroup.r i => c i
    | DihedralGroup.sr i => s * c i
  have hf : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    rcases x with i | i <;> rcases y with j | j
    · simp only [DihedralGroup.r_mul_r, f, hc_add]
    · simp only [DihedralGroup.r_mul_sr, f, sub_eq_add_neg, add_comm j (-i), hc_add, ← mul_assoc,
        hcs]
    · simp only [DihedralGroup.sr_mul_r, f, hc_add, mul_assoc]
    · simp only [DihedralGroup.sr_mul_sr, f, sub_eq_add_neg, add_comm j (-i), hc_add, ← mul_assoc,
        hsc]
  let ψ : DihedralGroup n →* G := MonoidHom.mk' f hf
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have hxy' : f x = f y := hxy
    rcases x with i | i <;> rcases y with j | j
    · simp only [f] at hxy'
      rw [hc_inj hxy']
    · exfalso
      simp only [f] at hxy'
      apply hs
      have := H.mul_mem (hc_mem i) (H.inv_mem (hc_mem j))
      rw [hxy'] at this
      simpa using this
    · exfalso
      simp only [f] at hxy'
      apply hs
      have := H.mul_mem (hc_mem j) (H.inv_mem (hc_mem i))
      rw [← hxy'] at this
      simpa using this
    · simp only [f] at hxy'
      rw [hc_inj (mul_left_cancel hxy')]
  have hsurj : Function.Surjective ψ := by
    intro x
    by_cases hx : x ∈ H
    · obtain ⟨a, ha⟩ := hc_surj x hx
      exact ⟨DihedralGroup.r a, ha⟩
    · obtain ⟨a, ha⟩ := hc_surj _ (hcov x hx)
      refine ⟨DihedralGroup.sr a, ?_⟩
      show s * c a = x
      rw [ha]; simp
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

end Core

section Matrices

/-- Entry relations for an orthogonal `2 × 2` matrix: with the first column `(a, c)`, a matrix of
determinant `1` has second column `(-c, a)` and one of determinant `-1` has `(c, -a)`. -/
lemma orth_two_entries {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) :
    (A.det = 1 → A 0 1 = -A 1 0 ∧ A 1 1 = A 0 0) ∧
      (A.det = -1 → A 0 1 = A 1 0 ∧ A 1 1 = -A 0 0) := by
  have h1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hA
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  rw [Matrix.det_fin_two]
  constructor
  · intro h
    exact ⟨by linear_combination (-A 0 1) * e00 + A 0 0 * e01 - A 1 0 * h,
      by linear_combination (-A 1 1) * e00 + A 1 0 * e01 + A 0 0 * h⟩
  · intro h
    exact ⟨by linear_combination (-A 0 1) * e00 + A 0 0 * e01 - A 1 0 * h,
      by linear_combination (-A 1 1) * e00 + A 1 0 * e01 + A 0 0 * h⟩

variable (G : Subgroup (Matrix.orthogonalGroup (Fin 2) ℝ))

/-- The rotation part of a subgroup of `O(2)`: its elements of determinant `1`. -/
def rotationPart : Subgroup G where
  carrier := {g | ((g : Matrix.orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    simp [Matrix.det_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : ((a * a⁻¹ : G) : Matrix.orthogonalGroup (Fin 2) ℝ).1.det = 1 := by simp
    simp only [Subgroup.coe_mul, Submonoid.coe_mul, Matrix.det_mul, ha, one_mul] at h
    simpa using h

lemma mem_rotationPart {g : G} :
    g ∈ rotationPart G ↔
      ((g : Matrix.orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := Iff.rfl

/-- The rotation part is cyclic: rotations embed in `ℂ`. -/
instance rotationPart_cyclic [Finite G] : IsCyclic (rotationPart G) := by
  let f : rotationPart G →* ℂ :=
    { toFun := fun g =>
        ((((g : G) : Matrix.orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
          ((((g : G) : Matrix.orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) *
            Complex.I
      map_one' := by simp
      map_mul' := by
        intro x y
        have hx := (orth_two_entries (x : G).1.2).1 x.2
        have hy := (orth_two_entries (y : G).1.2).1 y.2
        apply Complex.ext
        · simp [Matrix.mul_apply, Fin.sum_univ_two, hx.1]
          ring
        · simp [Matrix.mul_apply, Fin.sum_univ_two, hx.2]
          ring }
  refine isCyclic_of_injective_ringHom f ?_
  intro x y hxy
  have hx := (orth_two_entries (x : G).1.2).1 x.2
  have hy := (orth_two_entries (y : G).1.2).1 y.2
  have h0 := congrArg Complex.re hxy
  have h1 := congrArg Complex.im hxy
  simp [f] at h0 h1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hx.1, hx.2, hy.1, hy.2]

/-- AA-185. Theorem 12.2.4 (in the form for `O(2)`): every finite subgroup `G` of the orthogonal
group `O(2)` is cyclic or dihedral, of the form `ℤ_n` or `D_n` where `n` is the order of its
rotation part (the elements of determinant `1`). -/
@[kb "judson2026" "Theorem 12.2.4, p. 167"]
theorem finite_subgroup_orthogonal_two [Finite G] :
    ∃ n : ℕ, n = Nat.card (rotationPart G) ∧ 0 < n ∧
      (Nonempty (G ≃* Multiplicative (ZMod n)) ∨ Nonempty (G ≃* DihedralGroup n)) := by
  by_cases hall : ∀ g : G, g ∈ rotationPart G
  · have hsurj : Function.Surjective (rotationPart G).subtype := fun g => ⟨⟨g, hall g⟩, rfl⟩
    haveI : IsCyclic G := isCyclic_of_surjective (rotationPart G).subtype hsurj
    have hcard : Nat.card (rotationPart G) = Nat.card G :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    refine ⟨Nat.card G, hcard.symm, Nat.card_pos, Or.inl ⟨(zmodCyclicMulEquiv inferInstance).symm⟩⟩
  · push_neg at hall
    obtain ⟨s, hs⟩ := hall
    have hdet : ∀ g : G, g ∉ rotationPart G →
        ((g : Matrix.orthogonalGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
      intro g hg
      rcases det_orthogonal_eq_one_or_neg_one (g : G).1.2 with h | h
      · exact absurd h hg
      · exact h
    obtain ⟨n, hn, hpos, ⟨e⟩⟩ := dihedral_of_index_two (rotationPart G) s hs
      (by
        intro x hx
        have h := (orth_two_entries (x : G).1.2).2 (hdet x hx)
        have h1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp (x : G).1.2
        have hT : (((x : G) : Matrix.orthogonalGroup (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ)ᵀ = ((x : G) : Matrix.orthogonalGroup (Fin 2) ℝ) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h.1, h.2]
        apply Subtype.ext
        apply Subtype.ext
        simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
          hT] at h1
        simpa using h1)
      (by
        intro x hx
        have h1 := hdet x hx
        have h2 := hdet s hs
        show ((s⁻¹ * x : G) : Matrix.orthogonalGroup (Fin 2) ℝ).1.det = 1
        have h3 : ((s⁻¹ * s : G) : Matrix.orthogonalGroup (Fin 2) ℝ).1.det = 1 := by simp
        simp only [Subgroup.coe_mul, Submonoid.coe_mul, Matrix.det_mul, h2] at h3 ⊢
        rw [h1]
        linarith)
    exact ⟨n, hn, hpos, Or.inr ⟨e⟩⟩

end Matrices

end UndergradKB.AbstractAlgebra
