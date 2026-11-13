import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.ProblemsElasticity

/-! # Elasticity (Etingof et al., Problem 3.27), continued

* `skewParam_equivariant`, `hatEquiv`, `hat_equivariant`: the hat map `ℝ³ → skew-symmetric matrices` is an
  `SO(3)`-equivariant linear isomorphism: `g · hat(v) · gᵀ = hat(g v)` for `g ∈ SO(3)`.  Hence the skew part of
  `End V` is isomorphic to `V`.
* `V_irreducible_complex`, `skewC_irreducible`, `tlSymC_irreducible`: after complexification, the
  `SO(3)`-invariant complex subspaces of `ℂ³`, of the complex skew-symmetric matrices and of the complex
  traceless symmetric matrices are `0` or everything.  (The rotations used have rational entries; no irrational
  angle is needed, since the argument is field-independent.)
-/

namespace UndergradKB.RepresentationTheory

open Matrix

namespace Elasticity

noncomputable section

/-- The group `SO(3)`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-! ### The hat map is equivariant -/

lemma so_adjugate (g : SO3) : adjugate g.1 = g.1ᵀ := by
  have h1 := so_mul_transpose g
  have hd : g.1.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.1 g.2).2
  calc adjugate g.1 = adjugate g.1 * (g.1 * g.1ᵀ) := by rw [h1, Matrix.mul_one]
    _ = (adjugate g.1 * g.1) * g.1ᵀ := by rw [Matrix.mul_assoc]
    _ = g.1ᵀ := by rw [Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul]

/-- **Problem 3.27, equivariance of the hat map**: `g · hat(x) · gᵀ = hat(g x)` for `g ∈ SO(3)`. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem skewParam_equivariant (g : SO3) (x : Fin 3 → ℝ) :
    g.1 * (skewParam x).1 * g.1ᵀ = (skewParam (g.1 *ᵥ x)).1 := by
  have hadj := so_adjugate g
  rw [Matrix.adjugate_fin_three] at hadj
  have a00 := congrFun (congrFun hadj 0) 0
  have a01 := congrFun (congrFun hadj 0) 1
  have a02 := congrFun (congrFun hadj 0) 2
  have a10 := congrFun (congrFun hadj 1) 0
  have a11 := congrFun (congrFun hadj 1) 1
  have a12 := congrFun (congrFun hadj 1) 2
  have a20 := congrFun (congrFun hadj 2) 0
  have a21 := congrFun (congrFun hadj 2) 1
  have a22 := congrFun (congrFun hadj 2) 2
  simp at a00 a01 a02 a10 a11 a12 a20 a21 a22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewParam, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] <;>
    first
    | ring1
    | linear_combination (x 0) * a00 + (x 1) * a10 + (x 2) * a20
    | linear_combination -((x 0) * a00 + (x 1) * a10 + (x 2) * a20)
    | linear_combination (x 0) * a01 + (x 1) * a11 + (x 2) * a21
    | linear_combination -((x 0) * a01 + (x 1) * a11 + (x 2) * a21)
    | linear_combination (x 0) * a02 + (x 1) * a12 + (x 2) * a22
    | linear_combination -((x 0) * a02 + (x 1) * a12 + (x 2) * a22)

/-- The hat map `ℝ³ ≃ skew-symmetric matrices` as a linear equivalence. -/
def hatEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] skewSub :=
  LinearEquiv.ofBijective skewParam skewParam_bijective

/-- **Problem 3.27**: the linear isomorphism `ℝ³ ≅ skewSub` intertwines the action of `SO(3)` on `V = ℝ³`
with the conjugation action on skew-symmetric matrices. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem hat_equivariant (g : SO3) (x : Fin 3 → ℝ) :
    (hatEquiv (g.1 *ᵥ x)).1 = g.1 * (hatEquiv x).1 * g.1ᵀ :=
  (skewParam_equivariant g x).symm

/-! ### Complexification -/

/-- Complex `3 × 3` matrices. -/
abbrev MatC := Matrix (Fin 3) (Fin 3) ℂ

/-- A real rotation viewed as a complex matrix. -/
def cm (g : SO3) : MatC := g.1.map Complex.ofReal

/-- Complex skew-symmetric matrices. -/
def skewC : Submodule ℂ MatC where
  carrier := {M | Mᵀ = -M}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_add, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_smul, ha, smul_neg]

/-- Complex traceless symmetric matrices. -/
def tlSymC : Submodule ℂ MatC where
  carrier := {S | Sᵀ = S ∧ trace S = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_add, ha.1, hb.1, trace_add, ha.2, hb.2]
    simp
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_smul, ha.1, trace_smul, ha.2]
    simp

/-- A complex subspace of `Mat₃(ℂ)` invariant under conjugation by (real) `SO(3)`. -/
def InvC (U : Submodule ℂ MatC) : Prop := ∀ g : SO3, ∀ M ∈ U, cm g * M * (cm g)ᵀ ∈ U

/-- A complex subspace of `ℂ³` invariant under (real) `SO(3)`. -/
def InvV (U : Submodule ℂ (Fin 3 → ℂ)) : Prop := ∀ g : SO3, ∀ x ∈ U, cm g *ᵥ x ∈ U

lemma InvC.conj {U : Submodule ℂ MatC} (hU : InvC U) (r : SO3) {R : MatC} (hr : cm r = R)
    {M N : MatC} (hM : M ∈ U) (h : R * M * Rᵀ = N) : N ∈ U := by
  subst hr; exact h ▸ hU r M hM

lemma InvV.conj {U : Submodule ℂ (Fin 3 → ℂ)} (hU : InvV U) (r : SO3) {R : MatC} (hr : cm r = R)
    {x y : Fin 3 → ℂ} (hx : x ∈ U) (h : R *ᵥ x = y) : y ∈ U := by
  subst hr; exact h ▸ hU r x hx

lemma conjC_apply (g M : MatC) (i j : Fin 3) :
    (g * M * gᵀ) i j = ∑ a, ∑ b, g i a * M a b * g j b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma cm_rD1 : cm rD1 = !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]
lemma cm_rD2 : cm rD2 = !![(-1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]
lemma cm_rD3 : cm rD3 = !![(-1 : ℂ), 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]
lemma cm_rC : cm rC = !![(0 : ℂ), 0, 1; 1, 0, 0; 0, 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]
lemma cm_rR : cm rR = !![(3 / 5 : ℂ), -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]

local macro "mc" : tactic =>
  `(tactic| (ext i j; simp only [conjC_apply, Fin.sum_univ_three]; fin_cases i <;> fin_cases j <;>
    simp <;> norm_num))

/-- **Problem 3.27, `V ⊗ ℂ` is irreducible**: a complex subspace of `ℂ³` invariant under `SO(3)` is `0` or
everything. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem V_irreducible_complex (U : Submodule ℂ (Fin 3 → ℂ)) (hinv : InvV U) : U = ⊥ ∨ U = ⊤ := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have q0 : ((2 * x 0) • ![(1 : ℂ), 0, 0]) ∈ U := by
    have := U.add_mem hx (hinv.conj rD1 cm_rD1 hx rfl)
    convert this using 1
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have q1 : ((2 * x 1) • ![(0 : ℂ), 1, 0]) ∈ U := by
    have := U.add_mem hx (hinv.conj rD2 cm_rD2 hx rfl)
    convert this using 1
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have q2 : ((2 * x 2) • ![(0 : ℂ), 0, 1]) ∈ U := by
    have := U.add_mem hx (hinv.conj rD3 cm_rD3 hx rfl)
    convert this using 1
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have c0 : (![(1 : ℂ), 0, 0] ∈ U) → ![(0 : ℂ), 1, 0] ∈ U := fun h =>
    hinv.conj rC cm_rC h (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
  have c1 : (![(0 : ℂ), 1, 0] ∈ U) → ![(0 : ℂ), 0, 1] ∈ U := fun h =>
    hinv.conj rC cm_rC h (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
  have c2 : (![(0 : ℂ), 0, 1] ∈ U) → ![(1 : ℂ), 0, 0] ∈ U := fun h =>
    hinv.conj rC cm_rC h (by ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
  have hall : ![(1 : ℂ), 0, 0] ∈ U ∧ ![(0 : ℂ), 1, 0] ∈ U ∧ ![(0 : ℂ), 0, 1] ∈ U := by
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext i; fin_cases i <;> simp [hcon]
    rcases hx' with hx' | hx' | hx'
    · have e0 := (Submodule.smul_mem_iff U (by simpa using hx' : (2 * x 0) ≠ 0)).1 q0
      have e1 := c0 e0
      exact ⟨e0, e1, c1 e1⟩
    · have e1 := (Submodule.smul_mem_iff U (by simpa using hx' : (2 * x 1) ≠ 0)).1 q1
      have e2 := c1 e1
      exact ⟨c2 e2, e1, e2⟩
    · have e2 := (Submodule.smul_mem_iff U (by simpa using hx' : (2 * x 2) ≠ 0)).1 q2
      have e0 := c2 e2
      exact ⟨e0, c0 e0, e2⟩
  rw [Submodule.eq_top_iff']
  intro y
  have : y = y 0 • ![(1 : ℂ), 0, 0] + y 1 • ![(0 : ℂ), 1, 0] + y 2 • ![(0 : ℂ), 0, 1] := by
    ext i; fin_cases i <;> simp
  rw [this]
  exact U.add_mem (U.add_mem (U.smul_mem _ hall.1) (U.smul_mem _ hall.2.1)) (U.smul_mem _ hall.2.2)

/-- **Problem 3.27, the complexified skew part is irreducible.** -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem skewC_irreducible (U : Submodule ℂ MatC) (hU : U ≤ skewC) (hinv : InvC U) :
    U = ⊥ ∨ U = skewC := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨M, hM, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hMs : Mᵀ = -M := hU hM
  have s : ∀ i j, M j i = - M i j := fun i j => by
    have := congrFun (congrFun hMs i) j; simpa using this
  have m00 : M 0 0 = 0 := by have := s 0 0; linear_combination (1 / 2 : ℂ) * this
  have m11 : M 1 1 = 0 := by have := s 1 1; linear_combination (1 / 2 : ℂ) * this
  have m22 : M 2 2 = 0 := by have := s 2 2; linear_combination (1 / 2 : ℂ) * this
  have m10 : M 1 0 = - M 0 1 := s 0 1
  have m20 : M 2 0 = - M 0 2 := s 0 2
  have m21 : M 2 1 = - M 1 2 := s 1 2
  have p0 : (2 * (- M 1 2)) • (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : MatC) ∈ U := by
    have := U.add_mem hM (hinv.conj rD1 cm_rD1 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have p1 : (2 * M 0 2) • (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : MatC) ∈ U := by
    have := U.add_mem hM (hinv.conj rD2 cm_rD2 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have p2 : (2 * (- M 0 1)) • (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U := by
    have := U.add_mem hM (hinv.conj rD3 cm_rD3 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have c0 : (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : MatC) ∈ U →
      (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : MatC) ∈ U := fun h => hinv.conj rC cm_rC h (by mc)
  have c1 : (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : MatC) ∈ U →
      (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U := fun h => hinv.conj rC cm_rC h (by mc)
  have c2 : (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U →
      (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : MatC) ∈ U := fun h => hinv.conj rC cm_rC h (by mc)
  have hall : (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : MatC) ∈ U ∧
      (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : MatC) ∈ U ∧ (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U := by
    have hx : M 1 2 ≠ 0 ∨ M 0 2 ≠ 0 ∨ M 0 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext i j; fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21, hcon]
    rcases hx with hx | hx | hx
    · have h0 := (Submodule.smul_mem_iff U (by simpa using hx : (2 * (- M 1 2)) ≠ 0)).1 p0
      have h1 := c0 h0
      exact ⟨h0, h1, c1 h1⟩
    · have h1 := (Submodule.smul_mem_iff U (by simpa using hx : (2 * M 0 2) ≠ 0)).1 p1
      have h2 := c1 h1
      exact ⟨c2 h2, h1, h2⟩
    · have h2 := (Submodule.smul_mem_iff U (by simpa using hx : (2 * (- M 0 1)) ≠ 0)).1 p2
      have h0 := c2 h2
      exact ⟨h0, c0 h0, h2⟩
  refine le_antisymm ?_ ?_
  · exact hU
  · intro N hN
    have hNs : Nᵀ = -N := hN
    have t : ∀ i j, N j i = - N i j := fun i j => by
      have := congrFun (congrFun hNs i) j; simpa using this
    have n00 : N 0 0 = 0 := by have := t 0 0; linear_combination (1 / 2 : ℂ) * this
    have n11 : N 1 1 = 0 := by have := t 1 1; linear_combination (1 / 2 : ℂ) * this
    have n22 : N 2 2 = 0 := by have := t 2 2; linear_combination (1 / 2 : ℂ) * this
    have hN' : N = (- N 1 2) • (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : MatC)
        + (N 0 2) • (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : MatC)
        + (- N 0 1) • (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : MatC) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [n00, n11, n22, t 0 1, t 0 2, t 1 2]
    rw [hN']
    exact U.add_mem (U.add_mem (U.smul_mem _ hall.1) (U.smul_mem _ hall.2.1))
      (U.smul_mem _ hall.2.2)

/-- Averaging over the rotations by `π` about the coordinate axes (complex version). -/
lemma proj_offdiagC {U : Submodule ℂ MatC} (hinv : InvC U) {X : MatC} (hX : X ∈ U)
    (hs : ∀ i j, X j i = X i j) :
    (4 * X 0 1) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U ∧
    (4 * X 0 2) • (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : MatC) ∈ U ∧
    (4 * X 1 2) • (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : MatC) ∈ U := by
  have s10 := hs 0 1
  have s20 := hs 0 2
  have s21 := hs 1 2
  refine ⟨?_, ?_, ?_⟩
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD3 cm_rD3 hX rfl))
      (hinv.conj rD1 cm_rD1 hX rfl)) (hinv.conj rD2 cm_rD2 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD2 cm_rD2 hX rfl))
      (hinv.conj rD1 cm_rD1 hX rfl)) (hinv.conj rD3 cm_rD3 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD1 cm_rD1 hX rfl))
      (hinv.conj rD2 cm_rD2 hX rfl)) (hinv.conj rD3 cm_rD3 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring

lemma tlSymC_le_of_n01 {U : Submodule ℂ MatC} (hinv : InvC U)
    (h : (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U) : tlSymC ≤ U := by
  have h12 : (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : MatC) ∈ U := hinv.conj rC cm_rC h (by mc)
  have h02 : (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : MatC) ∈ U := hinv.conj rC cm_rC h12 (by mc)
  have hY : (-24 / 25 : ℂ) • (!![1, 0, 0; 0, -1, 0; 0, 0, 0] : MatC)
      + (-7 / 25 : ℂ) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U :=
    hinv.conj rR cm_rR h (by mc)
  have h1 := U.sub_mem hY (U.smul_mem (-7 / 25 : ℂ) h)
  rw [add_sub_cancel_right] at h1
  have d01 : (!![1, 0, 0; 0, -1, 0; 0, 0, 0] : MatC) ∈ U :=
    (Submodule.smul_mem_iff U (by norm_num : (-24 / 25 : ℂ) ≠ 0)).1 h1
  have d12 : (!![0, 0, 0; 0, 1, 0; 0, 0, -1] : MatC) ∈ U := hinv.conj rC cm_rC d01 (by mc)
  intro N hN
  obtain ⟨hsym, htr⟩ := hN
  have t : ∀ i j, N j i = N i j := fun i j => by
    have := congrFun (congrFun hsym i) j; simpa using this
  have htr' : N 0 0 + N 1 1 + N 2 2 = 0 := by simpa [trace_fin_three] using htr
  have hN' : N = (N 0 0) • ((!![1, 0, 0; 0, -1, 0; 0, 0, 0] : MatC) + !![0, 0, 0; 0, 1, 0; 0, 0, -1])
      + (N 1 1) • (!![0, 0, 0; 0, 1, 0; 0, 0, -1] : MatC)
      + (N 0 1) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : MatC)
      + (N 0 2) • (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : MatC)
      + (N 1 2) • (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : MatC) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2] <;>
      first | ring1 | linear_combination htr' | linear_combination -htr'
  rw [hN']
  exact U.add_mem (U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ (U.add_mem d01 d12))
    (U.smul_mem _ d12)) (U.smul_mem _ h)) (U.smul_mem _ h02)) (U.smul_mem _ h12)

lemma n01_of_diagC {U : Submodule ℂ MatC} (hinv : InvC U) {a b c : ℂ}
    (h : (!![a, 0, 0; 0, b, 0; 0, 0, c] : MatC) ∈ U) (hab : a ≠ b) :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : MatC) ∈ U := by
  have hY := hinv.conj rR cm_rR h rfl
  have hent : ((!![(3 / 5 : ℂ), -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1] * (!![a, 0, 0; 0, b, 0; 0, 0, c] : MatC) *
      (!![(3 / 5 : ℂ), -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1])ᵀ) 0 1) = (12 / 25 : ℂ) * (a - b) := by
    simp only [conjC_apply, Fin.sum_univ_three]
    simp
    ring
  have := (proj_offdiagC hinv hY (fun i j => by
    simp only [conjC_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp <;> ring)).1
  have h0 : (4 * ((!![(3 / 5 : ℂ), -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1] *
      (!![a, 0, 0; 0, b, 0; 0, 0, c] : MatC) *
      (!![(3 / 5 : ℂ), -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1])ᵀ) 0 1)) ≠ 0 := by
    rw [hent]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (sub_ne_zero.2 hab))
  exact (Submodule.smul_mem_iff U h0).1 this

/-- **Problem 3.27, the complexified traceless symmetric part `W ⊗ ℂ` is irreducible.** -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem tlSymC_irreducible (U : Submodule ℂ MatC) (hU : U ≤ tlSymC) (hinv : InvC U) :
    U = ⊥ ∨ U = tlSymC := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  refine le_antisymm hU ?_
  obtain ⟨M, hM, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hsym, htr⟩ := hU hM
  have t : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hsym i) j; simpa using this
  have htr' : M 0 0 + M 1 1 + M 2 2 = 0 := by simpa [trace_fin_three] using htr
  obtain ⟨p01, p02, p12⟩ := proj_offdiagC hinv hM t
  apply tlSymC_le_of_n01 hinv
  by_cases h01 : M 0 1 = 0
  · by_cases h02 : M 0 2 = 0
    · by_cases h12 : M 1 2 = 0
      · have hD : M = !![M 0 0, 0, 0; 0, M 1 1, 0; 0, 0, M 2 2] := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2, h01, h02, h12]
        rw [hD] at hM
        have hM2 : (!![M 2 2, 0, 0; 0, M 0 0, 0; 0, 0, M 1 1] : MatC) ∈ U :=
          hinv.conj rC cm_rC hM (by mc)
        have hM3 : (!![M 1 1, 0, 0; 0, M 2 2, 0; 0, 0, M 0 0] : MatC) ∈ U :=
          hinv.conj rC cm_rC hM2 (by mc)
        by_cases e1 : M 0 0 = M 1 1
        · by_cases e2 : M 2 2 = M 0 0
          · by_cases e3 : M 1 1 = M 2 2
            · exfalso
              apply hne
              have h3 : (3 : ℂ) * M 0 0 = 0 := by linear_combination htr' + e1 - e2
              have z0 : M 0 0 = 0 := by
                rcases mul_eq_zero.1 h3 with h | h
                · norm_num at h
                · exact h
              have z1 : M 1 1 = 0 := by rw [← e1]; exact z0
              have z2 : M 2 2 = 0 := by rw [e2]; exact z0
              ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2, h01, h02, h12,
                z0, z1, z2]
            · exact n01_of_diagC hinv hM3 e3
          · exact n01_of_diagC hinv hM2 e2
        · exact n01_of_diagC hinv hM e1
      · have := (Submodule.smul_mem_iff U (by simpa using h12 : (4 * M 1 2) ≠ 0)).1 p12
        have h2 : (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : MatC) ∈ U := hinv.conj rC cm_rC this (by mc)
        exact hinv.conj rC cm_rC h2 (by mc)
    · have := (Submodule.smul_mem_iff U (by simpa using h02 : (4 * M 0 2) ≠ 0)).1 p02
      exact hinv.conj rC cm_rC this (by mc)
  · exact (Submodule.smul_mem_iff U (by simpa using h01 : (4 * M 0 1) ≠ 0)).1 p01

end

end Elasticity

end UndergradKB.RepresentationTheory
