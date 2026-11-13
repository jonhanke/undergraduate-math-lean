import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Basic.Real.Star
import UndergradKB.Common.Attr

/-! # Elasticity (Etingof et al., Problem 3.27)

`SO(3)` acts on `End V = Mat₃(ℝ)` by conjugation `M ↦ g M gᵀ`.

* `decomposition`: `End V = skew ⊕ S²V` and `S²V = ℝ·1 ⊕ W` (`W` the traceless symmetric matrices);
  `inv_skewSub`, `inv_symSub`, `inv_tlSym`, `inv_scalars`: these are invariant;
  `finrank_tlSym` (`dim W = 5`), `finrank_skewSub` (`dim = 3`).
* `skew_irreducible`, `tlSym_irreducible`: the invariant subspaces of the skew part and of `W` are
  trivial (over `ℝ`; not proved after complexification).
* `classification`, `elasticMap_equivariant`: the equivariant linear maps `S²V → End V` are exactly
  `S ↦ K (tr S/3) · 1 + μ (S - (tr S/3) · 1)`, proved by direct computation with explicit rotations.
* Not included: the equivariant identification of the skew part with `V = ℝ³`.
-/

namespace UndergradKB.RepresentationTheory

open Matrix

/-- Real `3 × 3` matrices. -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

namespace Elasticity

noncomputable section

/-- The space of symmetric matrices `S²V`. -/
def symSub : Submodule ℝ Mat3 where
  carrier := {S | Sᵀ = S}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_smul, ha]

/-- Conjugation by a matrix preserves symmetric matrices. -/
def conjSym (g : Mat3) (S : symSub) : symSub :=
  ⟨g * S.1 * gᵀ, by
    have h : S.1ᵀ = S.1 := S.2
    show (g * S.1 * gᵀ)ᵀ = g * S.1 * gᵀ
    rw [transpose_mul, transpose_mul, transpose_transpose, h, Matrix.mul_assoc]⟩

/-- A rotation as an element of `SO(3)`, from an orthogonal matrix of determinant one. -/
def soMk (g : Mat3) (h1 : g * gᵀ = 1) (h2 : g.det = 1) :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨g, by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, h2⟩
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h1⟩

local macro "mt" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num))

/-- Rotation by `π` about the first axis. -/
def rD1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![1, 0, 0; 0, -1, 0; 0, 0, -1] (by mt) (by simp [Matrix.det_fin_three])
/-- Rotation by `π` about the second axis. -/
def rD2 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![-1, 0, 0; 0, 1, 0; 0, 0, -1] (by mt) (by simp [Matrix.det_fin_three])
/-- Rotation by `π` about the third axis. -/
def rD3 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![-1, 0, 0; 0, -1, 0; 0, 0, 1] (by mt) (by simp [Matrix.det_fin_three])
/-- Rotation exchanging axes 2 and 3 (and reversing axis 1). -/
def rP : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![-1, 0, 0; 0, 0, 1; 0, 1, 0] (by mt) (by simp [Matrix.det_fin_three])
/-- Rotation exchanging axes 1 and 2 (and reversing axis 3). -/
def rQ : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![0, 1, 0; 1, 0, 0; 0, 0, -1] (by mt) (by simp [Matrix.det_fin_three])
/-- The cyclic permutation of the axes. -/
def rC : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by mt) (by simp [Matrix.det_fin_three])
/-- The rotation about the third axis with cosine `3/5` and sine `4/5`. -/
def rR : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  soMk !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1] (by mt) (by simp [Matrix.det_fin_three]; norm_num)

@[simp] lemma rD1_val : rD1.1 = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := rfl
@[simp] lemma rD2_val : rD2.1 = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl
@[simp] lemma rD3_val : rD3.1 = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl
@[simp] lemma rP_val : rP.1 = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl
@[simp] lemma rQ_val : rQ.1 = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := rfl
@[simp] lemma rC_val : rC.1 = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl
@[simp] lemma rR_val : rR.1 = !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1] := rfl

/-- The diagonal matrix unit `E₁₁`. -/
def e0 : symSub := ⟨!![1, 0, 0; 0, 0, 0; 0, 0, 0], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩
/-- The diagonal matrix unit `E₂₂`. -/
def e1 : symSub := ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩
/-- The diagonal matrix unit `E₃₃`. -/
def e2 : symSub := ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩
/-- `E₁₂ + E₂₁`. -/
def n01 : symSub := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 0], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩
/-- `E₁₃ + E₃₁`. -/
def n02 : symSub := ⟨!![0, 0, 1; 0, 0, 0; 1, 0, 0], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩
/-- `E₂₃ + E₃₂`. -/
def n12 : symSub := ⟨!![0, 0, 0; 0, 0, 1; 0, 1, 0], by
  show _ᵀ = _
  ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[simp] lemma e0_val : e0.1 = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := rfl
@[simp] lemma e1_val : e1.1 = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := rfl
@[simp] lemma e2_val : e2.1 = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := rfl
@[simp] lemma n01_val : n01.1 = !![0, 1, 0; 1, 0, 0; 0, 0, 0] := rfl
@[simp] lemma n02_val : n02.1 = !![0, 0, 1; 0, 0, 0; 1, 0, 0] := rfl
@[simp] lemma n12_val : n12.1 = !![0, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

/-- A rotation `g` and symmetric matrices with `g S gᵀ = T` give `f T = g f(S) gᵀ`. -/
lemma equiv_apply (f : symSub →ₗ[ℝ] Mat3)
    (hf : ∀ (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (S : symSub),
      f (conjSym g.1 S) = g.1 * f S * g.1ᵀ)
    (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (S T : symSub)
    (h : g.1 * S.1 * g.1ᵀ = T.1) : f T = g.1 * f S * g.1ᵀ := by
  rw [← hf]
  congr 1
  exact Subtype.ext h.symm

local macro "mt" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num))

lemma conj_apply (g M : Mat3) (i j : Fin 3) :
    (g * M * gᵀ) i j = ∑ a, ∑ b, g i a * M a b * g j b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

section
variable (f : symSub →ₗ[ℝ] Mat3)
    (hf : ∀ (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (S : symSub),
      f (conjSym g.1 S) = g.1 * f S * g.1ᵀ)
include hf

lemma step_e0 : ∃ a b : ℝ, f e0 = !![a, 0, 0; 0, b, 0; 0, 0, b] := by
  have eq := equiv_apply f hf
  have h1 := eq rD1 e0 e0 (by mt)
  have h2 := eq rD2 e0 e0 (by mt)
  have h3 := eq rP e0 e0 (by mt)
  have e1 := fun i j => congrFun (congrFun h1 i) j
  have e2 := fun i j => congrFun (congrFun h2 i) j
  have e3 := fun i j => congrFun (congrFun h3 i) j
  simp only [conj_apply, Fin.sum_univ_three] at e1 e2 e3
  have a01 := e1 0 1
  have a02 := e1 0 2
  have a10 := e1 1 0
  have a20 := e1 2 0
  have a12 := e2 1 2
  have a21 := e2 2 1
  have a11 := e3 1 1
  simp at a01 a02 a10 a20 a12 a21 a11
  refine ⟨f e0 0 0, f e0 1 1, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith

lemma step_n01 : ∃ c : ℝ, f n01 = !![0, c, 0; c, 0, 0; 0, 0, 0] := by
  have eq := equiv_apply f hf
  have h1 := eq rD3 n01 n01 (by mt)
  have h2 := eq rD1 n01 (-n01) (by mt)
  have h3 := eq rQ n01 n01 (by mt)
  rw [map_neg] at h2
  have e1 := fun i j => congrFun (congrFun h1 i) j
  have e2 := fun i j => congrFun (congrFun h2 i) j
  have e3 := fun i j => congrFun (congrFun h3 i) j
  simp only [conj_apply, Fin.sum_univ_three] at e1 e2 e3
  have a02 := e1 0 2
  have a12 := e1 1 2
  have a20 := e1 2 0
  have a21 := e1 2 1
  have b00 := e2 0 0
  have b11 := e2 1 1
  have b22 := e2 2 2
  have c01 := e3 0 1
  simp at a02 a12 a20 a21 b00 b11 b22 c01
  refine ⟨f n01 0 1, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith

local macro "mc" : tactic =>
  `(tactic| (ext i j; simp only [conj_apply, Fin.sum_univ_three]; fin_cases i <;> fin_cases j <;> simp <;> norm_num))

/-- **Problem 3.27 (b), classification.**  Every `SO(3)`-equivariant linear map `f` from the
symmetric matrices `S²V` to `End V = Mat₃(ℝ)` (conjugation action) has the form
`f(S) = K · (tr S / 3) · 1 + μ · (S - (tr S / 3) · 1)`: it is a scalar `K` on the trace part
`ℝ · 1` and a scalar `μ` on the traceless symmetric part `W`. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem classification :
    ∃ K μ : ℝ, ∀ S : symSub,
      f S = (K * (trace S.1 / 3)) • (1 : Mat3) + μ • (S.1 - (trace S.1 / 3) • (1 : Mat3)) := by
  have eq := equiv_apply f hf
  obtain ⟨a, b, hA0⟩ := step_e0 f hf
  obtain ⟨c, hB⟩ := step_n01 f hf
  have hA1 : f e1 = !![b, 0, 0; 0, a, 0; 0, 0, b] := by
    rw [eq rC e0 e1 (by mt), hA0]; mc
  have hA2 : f e2 = !![b, 0, 0; 0, b, 0; 0, 0, a] := by
    rw [eq rC e1 e2 (by mt), hA1]; mc
  have hB12 : f n12 = !![0, 0, 0; 0, 0, c; 0, c, 0] := by
    rw [eq rC n01 n12 (by mt), hB]; mc
  have hB02 : f n02 = !![0, 0, c; 0, 0, 0; c, 0, 0] := by
    rw [eq rC n12 n02 (by mt), hB12]; mc
  have hr := eq rR (e0 - e1) ((-7 / 25 : ℝ) • (e0 - e1) + (24 / 25 : ℝ) • n01) (by mt)
  simp only [map_add, map_smul, map_sub, hA0, hA1, hB] at hr
  have hr01 := congrFun (congrFun hr 0) 1
  simp only [conj_apply, Fin.sum_univ_three] at hr01
  simp at hr01
  have hc : c = a - b := by linarith
  refine ⟨a + 2 * b, a - b, fun S => ?_⟩
  have hs01 : S.1 1 0 = S.1 0 1 := by
    have := congrFun (congrFun S.2 0) 1; simpa using this
  have hs02 : S.1 2 0 = S.1 0 2 := by
    have := congrFun (congrFun S.2 0) 2; simpa using this
  have hs12 : S.1 2 1 = S.1 1 2 := by
    have := congrFun (congrFun S.2 1) 2; simpa using this
  have hS : S = S.1 0 0 • e0 + S.1 1 1 • e1 + S.1 2 2 • e2 + S.1 0 1 • n01 + S.1 0 2 • n02
      + S.1 1 2 • n12 := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [hs01, hs02, hs12]
  rw [congrArg f hS]
  simp only [map_add, map_smul, hA0, hA1, hA2, hB, hB12, hB02]
  ext i j; fin_cases i <;> fin_cases j <;> simp [trace_fin_three, hs01, hs02, hs12, hc] <;> ring


end


/-- The skew-symmetric matrices (`≅ V = ℝ³`, the Lie algebra `so(3)`). -/
def skewSub : Submodule ℝ Mat3 where
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

/-- The traceless symmetric matrices `W` (5-dimensional). -/
def tlSym : Submodule ℝ Mat3 where
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

/-- A subspace of `End V` is invariant under conjugation by `SO(3)`. -/
def Inv (U : Submodule ℝ Mat3) : Prop :=
  ∀ (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ), ∀ M ∈ U, g.1 * M * g.1ᵀ ∈ U

lemma Inv.conj {U : Submodule ℝ Mat3} (hU : Inv U) (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {M N : Mat3} (hM : M ∈ U) (h : g.1 * M * g.1ᵀ = N) : N ∈ U := h ▸ hU g M hM

local macro "mc" : tactic =>
  `(tactic| (ext i j; simp only [conj_apply, Fin.sum_univ_three]; fin_cases i <;> fin_cases j <;> simp <;> norm_num))

/-- **Problem 3.27 (b), the skew part is irreducible**: a conjugation-invariant subspace of the
skew-symmetric matrices is `0` or everything. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem skew_irreducible (U : Submodule ℝ Mat3) (hU : U ≤ skewSub) (hinv : Inv U) :
    U = ⊥ ∨ U = skewSub := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨M, hM, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hMs : Mᵀ = -M := hU hM
  have s : ∀ i j, M j i = - M i j := fun i j => by
    have := congrFun (congrFun hMs i) j; simpa using this
  have m00 : M 0 0 = 0 := by have := s 0 0; linarith
  have m11 : M 1 1 = 0 := by have := s 1 1; linarith
  have m22 : M 2 2 = 0 := by have := s 2 2; linarith
  have m10 : M 1 0 = - M 0 1 := s 0 1
  have m20 : M 2 0 = - M 0 2 := s 0 2
  have m21 : M 2 1 = - M 1 2 := s 1 2
  have p0 : (2 * (- M 1 2)) • (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : Mat3) ∈ U := by
    have := U.add_mem hM (hinv.conj rD1 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have p1 : (2 * M 0 2) • (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : Mat3) ∈ U := by
    have := U.add_mem hM (hinv.conj rD2 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have p2 : (2 * (- M 0 1)) • (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U := by
    have := U.add_mem hM (hinv.conj rD3 hM rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [m00, m11, m22, m10, m20, m21] <;> ring
  have c0 : (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : Mat3) ∈ U →
      (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : Mat3) ∈ U := fun h => hinv.conj rC h (by mc)
  have c1 : (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : Mat3) ∈ U →
      (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U := fun h => hinv.conj rC h (by mc)
  have c2 : (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U →
      (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : Mat3) ∈ U := fun h => hinv.conj rC h (by mc)
  have hall : (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : Mat3) ∈ U ∧
      (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : Mat3) ∈ U ∧ (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U := by
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
    have n00 : N 0 0 = 0 := by have := t 0 0; linarith
    have n11 : N 1 1 = 0 := by have := t 1 1; linarith
    have n22 : N 2 2 = 0 := by have := t 2 2; linarith
    have hN' : N = (- N 1 2) • (!![0, 0, 0; 0, 0, -1; 0, 1, 0] : Mat3)
        + (N 0 2) • (!![0, 0, 1; 0, 0, 0; -1, 0, 0] : Mat3)
        + (- N 0 1) • (!![0, -1, 0; 1, 0, 0; 0, 0, 0] : Mat3) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [n00, n11, n22, t 0 1, t 0 2, t 1 2]
    rw [hN']
    exact U.add_mem (U.add_mem (U.smul_mem _ hall.1) (U.smul_mem _ hall.2.1))
      (U.smul_mem _ hall.2.2)


/-- Projection of a symmetric element of an invariant subspace onto the off-diagonal components,
by averaging over the rotations by `π` about the coordinate axes. -/
lemma proj_offdiag {U : Submodule ℝ Mat3} (hinv : Inv U) {X : Mat3} (hX : X ∈ U)
    (hs : ∀ i j, X j i = X i j) :
    (4 * X 0 1) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U ∧
    (4 * X 0 2) • (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : Mat3) ∈ U ∧
    (4 * X 1 2) • (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : Mat3) ∈ U := by
  have s10 := hs 0 1
  have s20 := hs 0 2
  have s21 := hs 1 2
  refine ⟨?_, ?_, ?_⟩
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD3 hX rfl)) (hinv.conj rD1 hX rfl))
      (hinv.conj rD2 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD2 hX rfl)) (hinv.conj rD1 hX rfl))
      (hinv.conj rD3 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring
  · have := U.sub_mem (U.sub_mem (U.add_mem hX (hinv.conj rD1 hX rfl)) (hinv.conj rD2 hX rfl))
      (hinv.conj rD3 hX rfl)
    convert this using 1
    ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [s10, s20, s21] <;> ring

/-- If an invariant subspace contains `E₁₂ + E₂₁` it contains all traceless symmetric matrices. -/
lemma tlSym_le_of_n01 {U : Submodule ℝ Mat3} (hinv : Inv U)
    (h : (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U) : tlSym ≤ U := by
  have h12 : (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : Mat3) ∈ U := hinv.conj rC h (by mc)
  have h02 : (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : Mat3) ∈ U := hinv.conj rC h12 (by mc)
  have hY : (-24 / 25 : ℝ) • (!![1, 0, 0; 0, -1, 0; 0, 0, 0] : Mat3)
      + (-7 / 25 : ℝ) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U :=
    hinv.conj rR h (by mc)
  have h1 := U.sub_mem hY (U.smul_mem (-7 / 25 : ℝ) h)
  rw [add_sub_cancel_right] at h1
  have d01 : (!![1, 0, 0; 0, -1, 0; 0, 0, 0] : Mat3) ∈ U :=
    (Submodule.smul_mem_iff U (by norm_num : (-24 / 25 : ℝ) ≠ 0)).1 h1
  have d12 : (!![0, 0, 0; 0, 1, 0; 0, 0, -1] : Mat3) ∈ U := hinv.conj rC d01 (by mc)
  intro N hN
  obtain ⟨hsym, htr⟩ := hN
  have t : ∀ i j, N j i = N i j := fun i j => by
    have := congrFun (congrFun hsym i) j; simpa using this
  have htr' : N 0 0 + N 1 1 + N 2 2 = 0 := by simpa [trace_fin_three] using htr
  have hN' : N = (N 0 0) • ((!![1, 0, 0; 0, -1, 0; 0, 0, 0] : Mat3) + !![0, 0, 0; 0, 1, 0; 0, 0, -1])
      + (N 1 1) • (!![0, 0, 0; 0, 1, 0; 0, 0, -1] : Mat3)
      + (N 0 1) • (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Mat3)
      + (N 0 2) • (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : Mat3)
      + (N 1 2) • (!![0, 0, 0; 0, 0, 1; 0, 1, 0] : Mat3) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2] <;> linarith
  rw [hN']
  exact U.add_mem (U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ (U.add_mem d01 d12))
    (U.smul_mem _ d12)) (U.smul_mem _ h)) (U.smul_mem _ h02)) (U.smul_mem _ h12)

/-- A diagonal matrix in an invariant subspace with distinct first two entries forces
`E₁₂ + E₂₁` into the subspace. -/
lemma n01_of_diag {U : Submodule ℝ Mat3} (hinv : Inv U) {a b c : ℝ}
    (h : (!![a, 0, 0; 0, b, 0; 0, 0, c] : Mat3) ∈ U) (hab : a ≠ b) :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Mat3) ∈ U := by
  have hY := hinv.conj rR h (rfl : rR.1 * _ * rR.1ᵀ = _)
  have := (proj_offdiag hinv hY (fun i j => by
    simp only [conj_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp <;> ring)).1
  have h0 : (4 * (rR.1 * (!![a, 0, 0; 0, b, 0; 0, 0, c] : Mat3) * rR.1ᵀ) 0 1) ≠ 0 := by
    simp only [conj_apply, Fin.sum_univ_three]
    simp
    intro hh
    apply hab
    linarith
  exact (Submodule.smul_mem_iff U h0).1 this

/-- **Problem 3.27 (b), `W` is irreducible**: a conjugation-invariant subspace of the traceless
symmetric matrices is `0` or all of `W`. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem tlSym_irreducible (U : Submodule ℝ Mat3) (hU : U ≤ tlSym) (hinv : Inv U) :
    U = ⊥ ∨ U = tlSym := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  refine le_antisymm hU ?_
  obtain ⟨M, hM, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hsym, htr⟩ := hU hM
  have t : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hsym i) j; simpa using this
  have htr' : M 0 0 + M 1 1 + M 2 2 = 0 := by simpa [trace_fin_three] using htr
  obtain ⟨p01, p02, p12⟩ := proj_offdiag hinv hM t
  apply tlSym_le_of_n01 hinv
  by_cases h01 : M 0 1 = 0
  · by_cases h02 : M 0 2 = 0
    · by_cases h12 : M 1 2 = 0
      · -- diagonal case
        have hD : M = !![M 0 0, 0, 0; 0, M 1 1, 0; 0, 0, M 2 2] := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2, h01, h02, h12]
        rw [hD] at hM
        have hM2 : (!![M 2 2, 0, 0; 0, M 0 0, 0; 0, 0, M 1 1] : Mat3) ∈ U :=
          hinv.conj rC hM (by mc)
        have hM3 : (!![M 1 1, 0, 0; 0, M 2 2, 0; 0, 0, M 0 0] : Mat3) ∈ U :=
          hinv.conj rC hM2 (by mc)
        by_cases e1 : M 0 0 = M 1 1
        · by_cases e2 : M 2 2 = M 0 0
          · by_cases e3 : M 1 1 = M 2 2
            · exfalso
              apply hne
              have z0 : M 0 0 = 0 := by linarith
              have z1 : M 1 1 = 0 := by linarith
              have z2 : M 2 2 = 0 := by linarith
              ext i j; fin_cases i <;> fin_cases j <;> simp [t 0 1, t 0 2, t 1 2, h01, h02, h12,
                z0, z1, z2]
            · exact n01_of_diag hinv hM3 e3
          · exact n01_of_diag hinv hM2 e2
        · exact n01_of_diag hinv hM e1
      · have := (Submodule.smul_mem_iff U (by simpa using h12 : (4 * M 1 2) ≠ 0)).1 p12
        have h2 : (!![0, 0, 1; 0, 0, 0; 1, 0, 0] : Mat3) ∈ U := hinv.conj rC this (by mc)
        exact hinv.conj rC h2 (by mc)
    · have := (Submodule.smul_mem_iff U (by simpa using h02 : (4 * M 0 2) ≠ 0)).1 p02
      exact hinv.conj rC this (by mc)
  · exact (Submodule.smul_mem_iff U (by simpa using h01 : (4 * M 0 1) ≠ 0)).1 p01


lemma so_mul_transpose (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : g.1 * g.1ᵀ = 1 := by
  have h := ((Matrix.mem_specialOrthogonalGroup_iff.1 g.2).1)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

lemma so_transpose_mul (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) : g.1ᵀ * g.1 = 1 := by
  have h := ((Matrix.mem_specialOrthogonalGroup_iff.1 g.2).1)
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

lemma trace_conj (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (M : Mat3) :
    trace (g.1 * M * g.1ᵀ) = trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, so_transpose_mul, Matrix.one_mul]

/-- The skew-symmetric matrices are conjugation invariant. -/
theorem inv_skewSub : Inv skewSub := by
  intro g M hM
  have hM' : Mᵀ = -M := hM
  show (g.1 * M * g.1ᵀ)ᵀ = -(g.1 * M * g.1ᵀ)
  rw [transpose_mul, transpose_mul, transpose_transpose, hM']
  simp [Matrix.mul_assoc]

/-- The symmetric matrices are conjugation invariant. -/
theorem inv_symSub : Inv symSub := by
  intro g M hM
  have hM' : Mᵀ = M := hM
  show (g.1 * M * g.1ᵀ)ᵀ = g.1 * M * g.1ᵀ
  rw [transpose_mul, transpose_mul, transpose_transpose, hM', Matrix.mul_assoc]

/-- The traceless symmetric matrices are conjugation invariant. -/
theorem inv_tlSym : Inv tlSym := by
  intro g M hM
  obtain ⟨h1, h2⟩ := hM
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, transpose_mul, transpose_transpose, h1, Matrix.mul_assoc]
  · rw [trace_conj, h2]

/-- The scalar matrices are conjugation invariant. -/
theorem inv_scalars : Inv (ℝ ∙ (1 : Mat3)) := by
  intro g M hM
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hM
  refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, so_mul_transpose]

/-- **Problem 3.27 (a), decomposition.**  `End V = (ℝ·1 ⊕ W) ⊕ (skew)`: the skew-symmetric and the
symmetric matrices are complementary, and the symmetric matrices `S²V` are the direct sum of
the scalars `ℝ·1` and the traceless symmetric matrices `W`. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem decomposition :
    IsCompl skewSub symSub ∧ Disjoint (ℝ ∙ (1 : Mat3)) tlSym ∧ symSub = (ℝ ∙ (1 : Mat3)) ⊔ tlSym := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro M h1 h2
    have a : Mᵀ = -M := h1
    have b : Mᵀ = M := h2
    ext i j
    have := congrFun (congrFun (a.symm.trans b) i) j
    simp at this ⊢
    linarith
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro M
    have : M = (1 / 2 : ℝ) • (M + Mᵀ) + (1 / 2 : ℝ) • (M - Mᵀ) := by
      ext i j; simp; ring
    have h1 : (1 / 2 : ℝ) • (M + Mᵀ) ∈ symSub := by
      show ((1 / 2 : ℝ) • (M + Mᵀ))ᵀ = (1 / 2 : ℝ) • (M + Mᵀ)
      rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
    have h2 : (1 / 2 : ℝ) • (M - Mᵀ) ∈ skewSub := by
      show ((1 / 2 : ℝ) • (M - Mᵀ))ᵀ = -((1 / 2 : ℝ) • (M - Mᵀ))
      rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h2)
  · rw [Submodule.disjoint_def]
    intro M h1 h2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h1
    have := h2.2
    simp at this
    simp [this]
  · refine le_antisymm ?_ (sup_le ?_ fun S h => h.1)
    · intro S hS
      have hS' : Sᵀ = S := hS
      have : S = (trace S / 3) • (1 : Mat3) + (S - (trace S / 3) • (1 : Mat3)) := by abel
      rw [this]
      refine Submodule.add_mem_sup (Submodule.mem_span_singleton.2 ⟨_, rfl⟩) ⟨?_, ?_⟩
      · rw [transpose_sub, transpose_smul, transpose_one, hS']
      · simp [trace_sub, trace_smul]
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact transpose_one


/-- Parametrisation of the traceless symmetric matrices by `ℝ⁵`. -/
def tlParam : (Fin 5 → ℝ) →ₗ[ℝ] tlSym where
  toFun x := ⟨!![x 0, x 2, x 3; x 2, x 1, x 4; x 3, x 4, -x 0 - x 1], by
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp [trace_fin_three]⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c x := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

lemma tlParam_bijective : Function.Bijective tlParam := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := congrArg Subtype.val hx
    have e := fun i j => congrFun (congrFun h i) j
    have e00 := e 0 0
    have e11 := e 1 1
    have e01 := e 0 1
    have e02 := e 0 2
    have e12 := e 1 2
    simp [tlParam] at e00 e11 e01 e02 e12
    ext i; fin_cases i <;> simp [e00, e11, e01, e02, e12]
  · rintro ⟨S, hsym, htr⟩
    have t : ∀ i j, S j i = S i j := fun i j => by
      have := congrFun (congrFun hsym i) j; simpa using this
    have htr' : S 0 0 + S 1 1 + S 2 2 = 0 := by simpa [trace_fin_three] using htr
    refine ⟨![S 0 0, S 1 1, S 0 1, S 0 2, S 1 2], ?_⟩
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [tlParam, t 0 1, t 0 2, t 1 2] <;> linarith

/-- **Problem 3.27 (a), `dim W = 5`.** -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem finrank_tlSym : Module.finrank ℝ tlSym = 5 := by
  rw [← (LinearEquiv.ofBijective tlParam tlParam_bijective).finrank_eq]
  simp

/-- Parametrisation of the skew-symmetric matrices by `ℝ³` (the hat map). -/
def skewParam : (Fin 3 → ℝ) →ₗ[ℝ] skewSub where
  toFun x := ⟨!![0, -x 2, x 1; x 2, 0, -x 0; -x 1, x 0, 0], by
    show _ᵀ = -_
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c x := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp

lemma skewParam_bijective : Function.Bijective skewParam := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := congrArg Subtype.val hx
    have e := fun i j => congrFun (congrFun h i) j
    have e12 := e 1 2
    have e02 := e 0 2
    have e01 := e 0 1
    simp [skewParam] at e12 e02 e01
    ext i; fin_cases i <;> simp [e12, e02, e01]
  · rintro ⟨M, hM⟩
    have hM' : Mᵀ = -M := hM
    have t : ∀ i j, M j i = - M i j := fun i j => by
      have := congrFun (congrFun hM' i) j; simpa using this
    have m00 : M 0 0 = 0 := by have := t 0 0; linarith
    have m11 : M 1 1 = 0 := by have := t 1 1; linarith
    have m22 : M 2 2 = 0 := by have := t 2 2; linarith
    refine ⟨![-M 1 2, M 0 2, -M 0 1], ?_⟩
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [skewParam, m00, m11, m22, t 0 1, t 0 2, t 1 2]

/-- The skew-symmetric matrices form a 3-dimensional space (isomorphic to `V = ℝ³`). -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem finrank_skewSub : Module.finrank ℝ skewSub = 3 := by
  rw [← (LinearEquiv.ofBijective skewParam skewParam_bijective).finrank_eq]
  simp


/-- The elasticity maps `S ↦ K (tr S / 3) · 1 + μ (S - (tr S / 3) · 1)`. -/
def elasticMap (K μ : ℝ) : symSub →ₗ[ℝ] Mat3 where
  toFun S := (K * (trace S.1 / 3)) • (1 : Mat3) + μ • (S.1 - (trace S.1 / 3) • (1 : Mat3))
  map_add' S T := by
    simp only [Submodule.coe_add, trace_add]
    module
  map_smul' c S := by
    simp only [Submodule.coe_smul, trace_smul, RingHom.id_apply, smul_eq_mul]
    module

/-- **Problem 3.27 (b), converse**: each map `elasticMap K μ` is `SO(3)`-equivariant. Together with
`classification` this shows the equivariant maps `S²V → End V` are exactly the two-parameter
family `(K, μ)`. -/
@[kb "etingof2011" "Problem 3.27, p. 45"]
theorem elasticMap_equivariant (K μ : ℝ) (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (S : symSub) :
    elasticMap K μ (conjSym g.1 S) = g.1 * elasticMap K μ S * g.1ᵀ := by
  have h1 := so_mul_transpose g
  have ht : trace (g.1 * S.1 * g.1ᵀ) = trace S.1 := trace_conj g S.1
  show (K * (trace (g.1 * S.1 * g.1ᵀ) / 3)) • (1 : Mat3)
      + μ • (g.1 * S.1 * g.1ᵀ - (trace (g.1 * S.1 * g.1ᵀ) / 3) • (1 : Mat3)) =
    g.1 * ((K * (trace S.1 / 3)) • (1 : Mat3)
      + μ • (S.1 - (trace S.1 / 3) • (1 : Mat3))) * g.1ᵀ
  rw [ht]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, h1]

end

end Elasticity

end UndergradKB.RepresentationTheory
