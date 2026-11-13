import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.ProblemsSU2

/-! # Problem 3.23(f): `SU(2) → SO(3)` (Etingof et al.)

The conjugation action `x ↦ q x q⁻¹` of unit quaternions on the pure quaternions `ℝ³` gives a surjective
homomorphism `rotQ : unitary ℍ[ℝ] →* SO(3)` with kernel `{1, -1}`; composing with the isomorphism of
`ProblemsSU2` gives `rotSU2 : SU(2) →* SO(3)` with kernel `{1, -1}`.  Surjectivity is proved by Euler-type
factorization: any rotation is brought to a rotation about the `z`-axis by a rotation about `z` followed by one
about `x`; rotations about the axes are images of `p + r k` and `p + r i` (half angle via a complex square root).
-/

namespace UndergradKB.RepresentationTheory

open Quaternion Matrix SU2Quaternion

namespace SO3Rot

/-- The rotation matrix of the conjugation `x ↦ q x q̄` on the pure quaternions `x₁ i + x₂ j + x₃ k`. -/
def rmat (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

/-- A pure quaternion from a vector. -/
def vec (x : Fin 3 → ℝ) : ℍ[ℝ] := ⟨0, x 0, x 1, x 2⟩

theorem conj_vec (q : ℍ[ℝ]) (x : Fin 3 → ℝ) : q * vec x * star q = vec (rmat q *ᵥ x) := by
  ext <;> simp [vec, rmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem rmat_mul (p q : ℍ[ℝ]) : rmat (p * q) = rmat p * rmat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem rmat_one : rmat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat]

theorem rmat_star (q : ℍ[ℝ]) : rmat (star q) = (rmat q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat] <;> ring

theorem rmat_det (q : ℍ[ℝ]) : (rmat q).det = (normSq q) ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [rmat, normSq_def']
  ring

/-- Special orthogonality of a real `3 × 3` matrix. -/
def IsSO3 (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop := M * Mᵀ = 1 ∧ Mᵀ * M = 1 ∧ M.det = 1

theorem IsSO3.mul {M N : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsSO3 M) (hN : IsSO3 N) : IsSO3 (M * N) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc N, hN.1, one_mul, hM.1]
  · rw [Matrix.transpose_mul, mul_assoc, ← mul_assoc Mᵀ, hM.2.1, one_mul, hN.2.1]
  · rw [Matrix.det_mul, hM.2.2, hN.2.2, one_mul]

theorem isSO3_rmat (u : unitary ℍ[ℝ]) : IsSO3 (rmat u.1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← rmat_star, ← rmat_mul, Unitary.mul_star_self_of_mem u.2, rmat_one]
  · rw [← rmat_star, ← rmat_mul, Unitary.star_mul_self_of_mem u.2, rmat_one]
  · rw [rmat_det, normSq_eq_one_of_mem u.2]; simp

theorem rmat_mem (u : unitary ℍ[ℝ]) : rmat u.1 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr (isSO3_rmat u).1, (isSO3_rmat u).2.2⟩

end SO3Rot

open SO3Rot

/-- **Problem 3.23(f)**: the conjugation action of unit quaternions on pure quaternions `ℝ³`, as a homomorphism
to `SO(3)`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
noncomputable def rotQ : unitary ℍ[ℝ] →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun u := ⟨rmat u.1, rmat_mem u⟩
  map_one' := Subtype.ext rmat_one
  map_mul' a b := Subtype.ext (rmat_mul a.1 b.1)

/-- The rotation `rotQ u` acts on pure quaternions by conjugation `x ↦ u x ū = u x u⁻¹`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem rotQ_conj (u : unitary ℍ[ℝ]) (x : Fin 3 → ℝ) :
    u.1 * vec x * star u.1 = vec ((rotQ u).1 *ᵥ x) := conj_vec u.1 x

/-- **Problem 3.23(f), kernel**: a unit quaternion acts trivially iff it is `±1`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem rotQ_eq_one_iff (u : unitary ℍ[ℝ]) : rotQ u = 1 ↔ u.1 = 1 ∨ u.1 = -1 := by
  constructor
  · intro h
    have hm : rmat u.1 = 1 := congrArg Subtype.val h
    have hn := normSq_eq_one_of_mem u.2
    rw [normSq_def'] at hn
    have e0 := congrFun (congrFun hm 0) 0
    have e1 := congrFun (congrFun hm 1) 1
    have e2 := congrFun (congrFun hm 2) 2
    simp [rmat] at e0 e1 e2
    have hb : u.1.imI = 0 := by nlinarith [sq_nonneg u.1.imI, sq_nonneg u.1.imJ, sq_nonneg u.1.imK]
    have hc : u.1.imJ = 0 := by nlinarith [sq_nonneg u.1.imI, sq_nonneg u.1.imJ, sq_nonneg u.1.imK]
    have hd : u.1.imK = 0 := by nlinarith [sq_nonneg u.1.imI, sq_nonneg u.1.imJ, sq_nonneg u.1.imK]
    have ha : u.1.re ^ 2 = 1 := by rw [hb, hc, hd] at hn; linarith
    have hprod : (u.1.re - 1) * (u.1.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h1 | h1
    · left
      ext <;> simp [hb, hc, hd] <;> linarith
    · right
      ext <;> simp [hb, hc, hd] <;> linarith
  · rintro (h | h)
    · have : u = 1 := Subtype.ext h
      rw [this, map_one]
    · apply Subtype.ext
      show rmat u.1 = 1
      rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rmat]

/-! ### Surjectivity -/

namespace SO3Rot

/-- Rotation about the `z`-axis. -/
def Rz (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-- Rotation about the `x`-axis. -/
def Rx (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c, -s; 0, s, c]

/-- Matrices that are images of unit quaternions. -/
def InRange (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop := ∃ u : unitary ℍ[ℝ], rmat u.1 = M

theorem InRange.mul {M N : Matrix (Fin 3) (Fin 3) ℝ} (hM : InRange M) (hN : InRange N) :
    InRange (M * N) := by
  obtain ⟨u, rfl⟩ := hM
  obtain ⟨v, rfl⟩ := hN
  exact ⟨u * v, by show rmat (u.1 * v.1) = _; rw [rmat_mul]⟩

theorem InRange.transpose {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : InRange M) : InRange Mᵀ := by
  obtain ⟨u, rfl⟩ := hM
  exact ⟨star u, by show rmat (star u.1) = _; rw [rmat_star]⟩

theorem InRange.isSO3 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : InRange M) : IsSO3 M := by
  obtain ⟨u, rfl⟩ := hM
  exact isSO3_rmat u

theorem mem_unitary_of_normSq {q : ℍ[ℝ]} (h : normSq q = 1) : q ∈ unitary ℍ[ℝ] := by
  rw [Unitary.mem_iff, star_mul_self, self_mul_star, h]
  simp

theorem half_angle (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ∃ p r : ℝ, p ^ 2 + r ^ 2 = 1 ∧ p ^ 2 - r ^ 2 = c ∧ 2 * p * r = s := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (⟨c, s⟩ : ℂ) (by norm_num : 0 < 2)
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp [sq] at hre him
  have h1 : w.re ^ 2 - w.im ^ 2 = c := by rw [sq, sq]; exact hre
  have h2 : 2 * w.re * w.im = s := by linarith
  refine ⟨w.re, w.im, ?_, h1, h2⟩
  have hX : (w.re ^ 2 + w.im ^ 2 - 1) * (w.re ^ 2 + w.im ^ 2 + 1) = 0 := by
    linear_combination (w.re ^ 2 - w.im ^ 2 + c) * h1 + (2 * w.re * w.im + s) * h2 + h
  rcases mul_eq_zero.mp hX with h3 | h3
  · linarith
  · nlinarith [sq_nonneg w.re, sq_nonneg w.im]

theorem inRange_Rz (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : InRange (Rz c s) := by
  obtain ⟨p, r, h1, h2, h3⟩ := half_angle c s h
  have hu : (⟨p, 0, 0, r⟩ : ℍ[ℝ]) ∈ unitary ℍ[ℝ] :=
    mem_unitary_of_normSq (by rw [normSq_def']; simp; linarith)
  refine ⟨⟨_, hu⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat, Rz] <;> nlinarith

theorem inRange_Rx (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : InRange (Rx c s) := by
  obtain ⟨p, r, h1, h2, h3⟩ := half_angle c s h
  have hu : (⟨p, r, 0, 0⟩ : ℍ[ℝ]) ∈ unitary ℍ[ℝ] :=
    mem_unitary_of_normSq (by rw [normSq_def']; simp; linarith)
  refine ⟨⟨_, hu⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat, Rx] <;> nlinarith

theorem exists_cs (x y : ℝ) : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c * x = s * y := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨1, 0, by norm_num, by simp [hx, hy]⟩
  · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hρ : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hsq := Real.sq_sqrt hpos.le
    refine ⟨y / Real.sqrt (x ^ 2 + y ^ 2), x / Real.sqrt (x ^ 2 + y ^ 2), ?_, ?_⟩
    · field_simp
      linarith
    · field_simp

/-- A special orthogonal matrix fixing the `z`-axis is a rotation about it. -/
theorem eq_Rz_of_fix {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : IsSO3 B) (h02 : B 0 2 = 0) (h12 : B 1 2 = 0)
    (h22 : B 2 2 = 1) : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ B = Rz c s := by
  have e22 := congrFun (congrFun hB.1 2) 2
  have f00 := congrFun (congrFun hB.2.1 0) 0
  have f11 := congrFun (congrFun hB.2.1 1) 1
  have f01 := congrFun (congrFun hB.2.1 0) 1
  have hd := hB.2.2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e22 f00 f11 f01
  rw [Matrix.det_fin_three] at hd
  have h20 : B 2 0 = 0 := by nlinarith [sq_nonneg (B 2 0), sq_nonneg (B 2 1)]
  have h21 : B 2 1 = 0 := by nlinarith [sq_nonneg (B 2 0), sq_nonneg (B 2 1)]
  simp only [h02, h12, h22, h20, h21] at f00 f11 f01 hd
  have E1 : B 0 0 ^ 2 + B 1 0 ^ 2 = 1 := by linarith
  have E2 : B 0 0 * B 0 1 + B 1 0 * B 1 1 = 0 := by linarith
  have E3 : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by linarith
  have h01 : B 0 1 = -B 1 0 := by
    linear_combination (-B 0 1) * E1 + B 0 0 * E2 - B 1 0 * E3
  have h11 : B 1 1 = B 0 0 := by
    linear_combination (-B 1 1) * E1 + B 0 0 * E3 + B 1 0 * E2
  refine ⟨B 0 0, B 1 0, E1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz, h01, h11, h02, h12, h22, h20, h21]

theorem inRange_of_isSO3 {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : IsSO3 A) : InRange A := by
  have hn : A 0 2 ^ 2 + A 1 2 ^ 2 + A 2 2 ^ 2 = 1 := by
    have := congrFun (congrFun hA.2.1 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at this
    nlinarith
  obtain ⟨c1, s1, h1, h1x⟩ := exists_cs (A 0 2) (A 1 2)
  set x := A 0 2 with hx
  set y := A 1 2 with hy
  set z := A 2 2 with hz
  set t := s1 * x + c1 * y with ht
  have ht2 : t ^ 2 = x ^ 2 + y ^ 2 := by
    rw [ht]
    linear_combination (x ^ 2 + y ^ 2) * h1 - (c1 * x - s1 * y) * h1x
  have hzt : z ^ 2 + t ^ 2 = 1 := by linarith
  have hM1 : InRange (Rx z t * Rz c1 s1) := (inRange_Rx z t hzt).mul (inRange_Rz c1 s1 h1)
  set M1 := Rx z t * Rz c1 s1 with hM1def
  have hB : IsSO3 (M1 * A) := hM1.isSO3.mul hA
  have b02 : (M1 * A) 0 2 = 0 := by
    simp [hM1def, Matrix.mul_apply, Fin.sum_univ_three, Rx, Rz, ← hx, ← hy, ← hz]
    linear_combination h1x
  have b12 : (M1 * A) 1 2 = 0 := by
    simp [hM1def, Matrix.mul_apply, Fin.sum_univ_three, Rx, Rz, ← hx, ← hy, ← hz]
    rw [ht]; ring
  have b22 : (M1 * A) 2 2 = 1 := by
    simp [hM1def, Matrix.mul_apply, Fin.sum_univ_three, Rx, Rz, ← hx, ← hy, ← hz]
    rw [ht] at hzt
    nlinarith
  obtain ⟨c3, s3, h3, hBz⟩ := eq_Rz_of_fix hB b02 b12 b22
  have hA' : A = M1ᵀ * (M1 * A) := by
    rw [← mul_assoc, hM1.isSO3.2.1, one_mul]
  rw [hA', hBz]
  exact hM1.transpose.mul (inRange_Rz c3 s3 h3)

end SO3Rot

/-- **Problem 3.23(f), surjectivity**: every rotation of `ℝ³` is the conjugation by a unit quaternion. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem rotQ_surjective : Function.Surjective rotQ := by
  intro g
  have hg := g.2
  have hso : IsSO3 g.1 :=
    ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hg.1, (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hg.1,
      hg.2⟩
  obtain ⟨u, hu⟩ := inRange_of_isSO3 hso
  exact ⟨u, Subtype.ext hu⟩

/-- **Problem 3.23(f)**: the homomorphism `SU(2) → SO(3)` obtained from `rotQ` and `unitaryQuatEquivSU2`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
noncomputable def rotSU2 :
    Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rotQ.comp unitaryQuatEquivSU2.symm.toMonoidHom

@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem rotSU2_surjective : Function.Surjective rotSU2 := by
  intro g
  obtain ⟨u, hu⟩ := rotQ_surjective g
  exact ⟨unitaryQuatEquivSU2 u, by simpa [rotSU2] using hu⟩

/-- **Problem 3.23(f), kernel**: an element of `SU(2)` maps to the identity of `SO(3)` iff it is `±1`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem rotSU2_eq_one_iff (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    rotSU2 g = 1 ↔ g.1 = 1 ∨ g.1 = -1 := by
  obtain ⟨u, rfl⟩ := unitaryQuatEquivSU2.surjective g
  have h1 : rotSU2 (unitaryQuatEquivSU2 u) = rotQ u := by simp [rotSU2]
  have h2 : (unitaryQuatEquivSU2 u).1 = qmat u.1 := rfl
  have hneg : qmat (-1) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qmat]
  rw [h1, rotQ_eq_one_iff, h2]
  constructor
  · rintro (h | h)
    · left; rw [h, qmat_one]
    · right; rw [h, hneg]
  · rintro (h | h)
    · left; apply qmat_injective; rw [h, qmat_one]
    · right; apply qmat_injective; rw [h, hneg]

end UndergradKB.RepresentationTheory
