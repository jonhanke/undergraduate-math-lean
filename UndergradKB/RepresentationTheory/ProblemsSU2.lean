import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Data.Complex.Basic
import UndergradKB.Common.Attr

/-! # Problem 3.23: `SU(2)`, the quaternions, and `ℂ²` as a real representation (Etingof et al.)

* (e) `unitaryQuatEquivSU2`: the group of unit quaternions (`unitary ℍ[ℝ]`) is isomorphic to `SU(2)` via
  `a + bi + cj + dk ↦ [[a + bi, c + di], [-c + di, a - bi]]`; `mem_unitary_quaternion_iff_norm` identifies it with
  the quaternions of norm `1`.
* (d) `quaternion_star_mul`, `quaternion_norm_mul`: conjugation reverses products and the norm is multiplicative.
* (c), (b) `su2Commutant`, `su2Commutant_algEquiv`: the algebra of real-linear endomorphisms of `ℂ²` commuting with
  `SU(2)` is isomorphic to `ℍ[ℝ]` (as an `ℝ`-algebra); hence it is 4-dimensional, its nonzero elements are
  invertible and it has a basis `1, i, j, k` with the quaternion relations.
* (a) `su2_real_irreducible`: `ℂ²` is an irreducible real representation of `SU(2)`.
-/

namespace UndergradKB.RepresentationTheory

open Quaternion Matrix

namespace SU2Quaternion

/-- The matrix attached to a quaternion `a + bi + cj + dk`. -/
def qmat (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

theorem qmat_mul (p q : ℍ[ℝ]) : qmat (p * q) = qmat p * qmat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem qmat_one : qmat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qmat]

theorem qmat_star (q : ℍ[ℝ]) : qmat (star q) = star (qmat q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [qmat, Matrix.star_apply]

theorem qmat_det (q : ℍ[ℝ]) : (qmat q).det = ((normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  rw [normSq_def']
  push_cast
  apply Complex.ext <;> simp [qmat, sq] <;> ring

theorem qmat_injective : Function.Injective qmat := by
  intro p q h
  have h00 := congrArg (fun M => M 0 0) h
  have h01 := congrArg (fun M => M 0 1) h
  simp only [qmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.mk.injEq] at h00 h01
  ext
  · exact h00.1
  · exact h00.2
  · exact h01.1
  · exact h01.2

theorem normSq_eq_one_of_mem {u : ℍ[ℝ]} (hu : u ∈ unitary ℍ[ℝ]) : normSq u = 1 := by
  have h := Unitary.mul_star_self_of_mem hu
  rw [self_mul_star] at h
  have := congrArg QuaternionAlgebra.re h
  simpa using this

theorem qmat_mem (u : unitary ℍ[ℝ]) : qmat u.1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [← qmat_star, ← qmat_mul, Unitary.mul_star_self_of_mem u.2, qmat_one]
  · rw [qmat_det, normSq_eq_one_of_mem u.2]; simp

/-- The homomorphism from unit quaternions to `SU(2)`. -/
noncomputable def toSU2 : unitary ℍ[ℝ] →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun u := ⟨qmat u.1, qmat_mem u⟩
  map_one' := Subtype.ext qmat_one
  map_mul' a b := Subtype.ext (qmat_mul a.1 b.1)

theorem toSU2_val (u : unitary ℍ[ℝ]) : (toSU2 u).1 = qmat u.1 := rfl

theorem toSU2_injective : Function.Injective toSU2 := by
  intro a b h
  exact Subtype.ext (qmat_injective (congrArg Subtype.val h))

theorem toSU2_surjective : Function.Surjective toSU2 := by
  rintro ⟨A, hA⟩
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, ] at hA
  obtain ⟨hA1, hdet⟩ := hA
  have hA2 : star A * A = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_unitaryGroup_iff.mpr hA1)
    exact this
  have hadj : Matrix.adjugate A = star A := by
    calc Matrix.adjugate A = (star A * A) * Matrix.adjugate A := by rw [hA2, one_mul]
      _ = star A * (A * Matrix.adjugate A) := by rw [mul_assoc]
      _ = star A := by rw [Matrix.mul_adjugate, hdet, one_smul, mul_one]
  rw [Matrix.adjugate_fin_two] at hadj
  have h00 := congrArg (fun M => M 0 0) hadj
  have h01 := congrArg (fun M => M 0 1) hadj
  have h10 := congrArg (fun M => M 1 0) hadj
  have h11 := congrArg (fun M => M 1 1) hadj
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.star_apply, Matrix.head_cons] at h00 h01 h10 h11
  let q : ℍ[ℝ] := ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩
  have e10 : A 1 0 = -star (A 0 1) := by rw [← h10]; simp
  have e11 : A 1 1 = star (A 0 0) := h00
  have hq : qmat q = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> (apply Complex.ext <;> simp [qmat, q, e10, e11])
  have hmem : q ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor
    · apply qmat_injective
      rw [qmat_mul, qmat_star, qmat_one, hq]; exact hA2
    · apply qmat_injective
      rw [qmat_mul, qmat_star, qmat_one, hq]; exact hA1
  exact ⟨⟨q, hmem⟩, Subtype.ext hq⟩

end SU2Quaternion

/-- **Etingof et al., Problem 3.23(e)**: the group of unit quaternions is isomorphic to `SU(2)`, via
`a + bi + cj + dk ↦ [[a + bi, c + di], [-c + di, a - bi]]`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
noncomputable def unitaryQuatEquivSU2 :
    unitary ℍ[ℝ] ≃* Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  MulEquiv.ofBijective SU2Quaternion.toSU2
    ⟨SU2Quaternion.toSU2_injective, SU2Quaternion.toSU2_surjective⟩

@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem unitaryQuatEquivSU2_apply (u : unitary ℍ[ℝ]) :
    (unitaryQuatEquivSU2 u).1 =
      !![(⟨u.1.re, u.1.imI⟩ : ℂ), ⟨u.1.imJ, u.1.imK⟩; ⟨-u.1.imJ, u.1.imK⟩, ⟨u.1.re, -u.1.imI⟩] := rfl

/-- The unitary quaternions are exactly the quaternions of norm `1`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem mem_unitary_quaternion_iff_norm (q : ℍ[ℝ]) : q ∈ unitary ℍ[ℝ] ↔ ‖q‖ = 1 := by
  constructor
  · intro h
    have h1 := SU2Quaternion.normSq_eq_one_of_mem h
    rw [normSq_eq_norm_mul_self] at h1
    nlinarith [norm_nonneg q]
  · intro h
    have h1 : normSq q = 1 := by rw [normSq_eq_norm_mul_self, h]; simp
    rw [Unitary.mem_iff, star_mul_self, self_mul_star, h1]
    simp

/-- **Problem 3.23(d)**: quaternionic conjugation reverses products. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem quaternion_star_mul (p q : ℍ[ℝ]) : star (p * q) = star q * star p := star_mul p q

/-- **Problem 3.23(d)**: the norm of quaternions is multiplicative. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem quaternion_norm_mul (p q : ℍ[ℝ]) : ‖p * q‖ = ‖p‖ * ‖q‖ := norm_mul p q

/-! ### `ℂ²` as the quaternions, and the commutant -/

namespace SU2Quaternion

/-- `ℍ ≅ ℂ²` as real vector spaces, intertwining left multiplication by `q` with the matrix `qmat q`. -/
noncomputable def quatEquiv : ℍ[ℝ] ≃ₗ[ℝ] (Fin 2 → ℂ) where
  toFun x := ![⟨x.re, x.imI⟩, ⟨-x.imJ, x.imK⟩]
  map_add' x y := by
    funext i; fin_cases i <;> apply Complex.ext <;> simp <;> ring
  map_smul' r x := by
    funext i; fin_cases i <;> apply Complex.ext <;> simp
  invFun v := ⟨(v 0).re, (v 0).im, -(v 1).re, (v 1).im⟩
  left_inv x := by ext <;> simp
  right_inv v := by
    funext i; fin_cases i <;> apply Complex.ext <;> simp

theorem quatEquiv_mul (q x : ℍ[ℝ]) : quatEquiv (q * x) = qmat q *ᵥ quatEquiv x := by
  funext i
  fin_cases i <;> apply Complex.ext <;>
    simp [quatEquiv, qmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The action of `g ∈ SU(2)` on `ℂ²`, viewed as a real-linear endomorphism. -/
noncomputable def su2Op (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Module.End ℝ (Fin 2 → ℂ) :=
  (Matrix.mulVecLin g.1).restrictScalars ℝ

theorem su2Op_apply (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    su2Op g v = g.1 *ᵥ v := rfl

theorem su2Op_toSU2 (u : unitary ℍ[ℝ]) (y : ℍ[ℝ]) :
    su2Op (toSU2 u) (quatEquiv y) = quatEquiv (u.1 * y) := by
  rw [su2Op_apply, toSU2_val, quatEquiv_mul]

/-- The quaternion units. -/
def qI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def qJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def qK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem qI_mem : qI ∈ unitary ℍ[ℝ] := by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp [qI]
theorem qJ_mem : qJ ∈ unitary ℍ[ℝ] := by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp [qJ]
theorem qK_mem : qK ∈ unitary ℍ[ℝ] := by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp [qK]

theorem mul_decomp (q y : ℍ[ℝ]) :
    q * y = q.re • y + q.imI • (qI * y) + q.imJ • (qJ * y) + q.imK • (qK * y) := by
  ext <;> simp [qI, qJ, qK] <;> ring

theorem map_mul_of_basis {T : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]} (hI : ∀ y, T (qI * y) = qI * T y)
    (hJ : ∀ y, T (qJ * y) = qJ * T y) (hK : ∀ y, T (qK * y) = qK * T y) (q y : ℍ[ℝ]) :
    T (q * y) = q * T y := by
  rw [mul_decomp q y]
  simp only [map_add, map_smul, hI, hJ, hK]
  rw [mul_decomp q (T y)]

theorem mul_mem_of_basis {W : Submodule ℝ ℍ[ℝ]} (hI : ∀ y ∈ W, qI * y ∈ W)
    (hJ : ∀ y ∈ W, qJ * y ∈ W) (hK : ∀ y ∈ W, qK * y ∈ W) (q : ℍ[ℝ]) {y : ℍ[ℝ]} (hy : y ∈ W) :
    q * y ∈ W := by
  rw [mul_decomp q y]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ hy) (W.smul_mem _ (hI y hy)))
    (W.smul_mem _ (hJ y hy))) (W.smul_mem _ (hK y hy))

/-- An endomorphism of `ℂ²` commuting with `SU(2)` is right multiplication by a quaternion. -/
theorem commutant_form (T : Module.End ℝ (Fin 2 → ℂ))
    (hT : ∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, su2Op g * T = T * su2Op g) :
    ∃ r : ℍ[ℝ], ∀ x, T (quatEquiv x) = quatEquiv (x * r) := by
  let T' : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] := quatEquiv.symm.toLinearMap ∘ₗ T ∘ₗ quatEquiv.toLinearMap
  have hT' : ∀ (u : unitary ℍ[ℝ]) (y : ℍ[ℝ]), T' (u.1 * y) = u.1 * T' y := by
    intro u y
    have h2 : su2Op (toSU2 u) (T (quatEquiv y)) = T (su2Op (toSU2 u) (quatEquiv y)) :=
      LinearMap.congr_fun (hT (toSU2 u)) (quatEquiv y)
    have h3 := su2Op_toSU2 u (quatEquiv.symm (T (quatEquiv y)))
    rw [LinearEquiv.apply_symm_apply] at h3
    show quatEquiv.symm (T (quatEquiv (u.1 * y))) = u.1 * quatEquiv.symm (T (quatEquiv y))
    rw [← su2Op_toSU2 u y, ← h2, h3, LinearEquiv.symm_apply_apply]
  have hall := map_mul_of_basis (T := T') (fun y => hT' ⟨qI, qI_mem⟩ y) (fun y => hT' ⟨qJ, qJ_mem⟩ y)
    (fun y => hT' ⟨qK, qK_mem⟩ y)
  refine ⟨T' 1, fun x => ?_⟩
  have h1 : T' x = x * T' 1 := by
    have := hall x 1
    rwa [mul_one] at this
  have h2 : quatEquiv (T' x) = T (quatEquiv x) := by
    show quatEquiv (quatEquiv.symm (T (quatEquiv x))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [← h2, h1]

/-- Right multiplication by `star q`, transported to `ℂ²`. -/
noncomputable def epsLin : ℍ[ℝ] →ₗ[ℝ] Module.End ℝ (Fin 2 → ℂ) where
  toFun q := quatEquiv.toLinearMap ∘ₗ LinearMap.mulRight ℝ (star q) ∘ₗ quatEquiv.symm.toLinearMap
  map_add' p q := by
    refine LinearMap.ext fun w => ?_
    simp [star_add, mul_add]
  map_smul' r q := by
    refine LinearMap.ext fun w => ?_
    simp

theorem epsLin_apply (q : ℍ[ℝ]) (w : Fin 2 → ℂ) :
    epsLin q w = quatEquiv (quatEquiv.symm w * star q) := rfl

/-- The algebra map `ℍ → End_ℝ(ℂ²)`, `q ↦ (right multiplication by q̄)`. -/
noncomputable def eps : ℍ[ℝ] →ₐ[ℝ] Module.End ℝ (Fin 2 → ℂ) :=
  AlgHom.ofLinearMap epsLin
    (LinearMap.ext fun w => by simp [epsLin_apply])
    (fun p q => LinearMap.ext fun w => by
      simp [epsLin_apply, star_mul, mul_assoc])

theorem eps_apply (q : ℍ[ℝ]) (w : Fin 2 → ℂ) :
    eps q w = quatEquiv (quatEquiv.symm w * star q) := rfl

end SU2Quaternion

open SU2Quaternion

/-- The algebra of real-linear endomorphisms of `ℂ²` commuting with all of `SU(2)`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
noncomputable def su2Commutant : Subalgebra ℝ (Module.End ℝ (Fin 2 → ℂ)) :=
  Subalgebra.centralizer ℝ (Set.range su2Op)

theorem eps_mem_commutant (q : ℍ[ℝ]) : eps q ∈ su2Commutant := by
  rw [su2Commutant, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  obtain ⟨u, rfl⟩ := toSU2_surjective g
  refine LinearMap.ext fun w => ?_
  obtain ⟨y, rfl⟩ := quatEquiv.surjective w
  simp only [mul_apply_eq_comp, Function.comp_apply, eps_apply, LinearEquiv.symm_apply_apply,
    su2Op_toSU2, mul_assoc]

/-- **Problem 3.23(c)**: the commutant of `SU(2)` in `End_ℝ(ℂ²)` is isomorphic, as an `ℝ`-algebra, to the
quaternions `ℍ[ℝ]`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
noncomputable def su2Commutant_algEquiv : ℍ[ℝ] ≃ₐ[ℝ] su2Commutant :=
  AlgEquiv.ofBijective (eps.codRestrict su2Commutant eps_mem_commutant) (by
    have hcod : ∀ q, ((eps.codRestrict su2Commutant eps_mem_commutant q : su2Commutant) :
        Module.End ℝ (Fin 2 → ℂ)) = eps q := fun q => rfl
    constructor
    · intro p q h
      have h1 := congrArg (fun T : su2Commutant => (T : Module.End ℝ (Fin 2 → ℂ)) (quatEquiv 1)) h
      simp only [hcod, eps_apply, LinearEquiv.symm_apply_apply, one_mul] at h1
      exact star_injective (quatEquiv.injective h1)
    · rintro ⟨T, hT⟩
      rw [su2Commutant, Subalgebra.mem_centralizer_iff] at hT
      obtain ⟨r, hr⟩ := commutant_form T (fun g => hT _ ⟨g, rfl⟩)
      refine ⟨star r, Subtype.ext (LinearMap.ext fun w => ?_)⟩
      obtain ⟨y, rfl⟩ := quatEquiv.surjective w
      simp only [hcod, eps_apply, LinearEquiv.symm_apply_apply, star_star]
      exact (hr y).symm)

/-- **Problem 3.23(b)**: the commutant of `SU(2)` in `End_ℝ(ℂ²)` is 4-dimensional over `ℝ`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem finrank_su2Commutant : Module.finrank ℝ su2Commutant = 4 :=
  (su2Commutant_algEquiv.toLinearEquiv.finrank_eq).symm.trans Quaternion.finrank_eq_four

/-- **Problem 3.23(b)**: every nonzero element of the commutant is invertible. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem su2Commutant_isUnit (T : Module.End ℝ (Fin 2 → ℂ)) (hT : T ∈ su2Commutant) (h0 : T ≠ 0) :
    IsUnit T := by
  obtain ⟨q, hq⟩ := su2Commutant_algEquiv.surjective ⟨T, hT⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply h0
    have := congrArg Subtype.val hq
    simpa using this.symm
  have h1 : IsUnit q := isUnit_iff_ne_zero.mpr hq0
  have h2 := h1.map su2Commutant_algEquiv
  rw [hq] at h2
  exact h2.map su2Commutant.val

/-- **Problem 3.23(c)**: the commutant has a basis `1, i, j, k` with the quaternion relations. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem su2Commutant_quaternion_basis :
    ∃ b : Module.Basis (Fin 4) ℝ su2Commutant, b 0 = 1 ∧ b 1 * b 1 = -1 ∧ b 2 * b 2 = -1 ∧
      b 3 * b 3 = -1 ∧ b 1 * b 2 = b 3 ∧ b 2 * b 3 = b 1 ∧ b 3 * b 1 = b 2 := by
  let B : Module.Basis (Fin 4) ℝ ℍ[ℝ] := QuaternionAlgebra.basisOneIJK (-1) 0 (-1)
  have h0 : B 0 = 1 := by ext <;> simp [B, QuaternionAlgebra.basisOneIJK]
  have h1 : B 1 = qI := by ext <;> simp [B, QuaternionAlgebra.basisOneIJK, qI]
  have h2 : B 2 = qJ := by ext <;> simp [B, QuaternionAlgebra.basisOneIJK, qJ]
  have h3 : B 3 = qK := by ext <;> simp [B, QuaternionAlgebra.basisOneIJK, qK]
  have hb : ∀ i, (B.map su2Commutant_algEquiv.toLinearEquiv) i = su2Commutant_algEquiv (B i) :=
    fun i => rfl
  have qII : qI * qI = -1 := by ext <;> simp [qI]
  have qJJ : qJ * qJ = -1 := by ext <;> simp [qJ]
  have qKK : qK * qK = -1 := by ext <;> simp [qK]
  have qIJ : qI * qJ = qK := by ext <;> simp [qI, qJ, qK]
  have qJK : qJ * qK = qI := by ext <;> simp [qI, qJ, qK]
  have qKI : qK * qI = qJ := by ext <;> simp [qI, qJ, qK]
  refine ⟨B.map su2Commutant_algEquiv.toLinearEquiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, h0, map_one]
  · rw [hb, h1, ← map_mul, qII, map_neg, map_one]
  · rw [hb, h2, ← map_mul, qJJ, map_neg, map_one]
  · rw [hb, h3, ← map_mul, qKK, map_neg, map_one]
  · rw [hb, hb, h1, h2, ← map_mul, qIJ, hb, h3]
  · rw [hb, hb, h2, h3, ← map_mul, qJK, hb, h1]
  · rw [hb, hb, h3, h1, ← map_mul, qKI, hb, h2]

/-- **Problem 3.23(a)**: `ℂ²` is an irreducible real representation of `SU(2)`: it is nonzero and the only real
subspaces invariant under all `g ∈ SU(2)` are `0` and `ℂ²`. -/
@[kb "etingof2011" "Problem 3.23, p. 44"]
theorem su2_real_irreducible :
    (⊥ : Submodule ℝ (Fin 2 → ℂ)) ≠ ⊤ ∧
      ∀ W : Submodule ℝ (Fin 2 → ℂ),
        (∀ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ w ∈ W, g.1 *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  refine ⟨bot_ne_top, fun W hW => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  let W' : Submodule ℝ ℍ[ℝ] := W.comap quatEquiv.toLinearMap
  have hu : ∀ u : unitary ℍ[ℝ], ∀ y ∈ W', u.1 * y ∈ W' := by
    intro u y hy
    have hy' : quatEquiv y ∈ W := hy
    show quatEquiv (u.1 * y) ∈ W
    rw [← su2Op_toSU2, su2Op_apply]
    exact hW _ _ hy'
  have hall := mul_mem_of_basis (W := W') (fun y hy => hu ⟨qI, qI_mem⟩ y hy)
    (fun y hy => hu ⟨qJ, qJ_mem⟩ y hy) (fun y hy => hu ⟨qK, qK_mem⟩ y hy)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hx : quatEquiv.symm w ∈ W' := by
    show quatEquiv (quatEquiv.symm w) ∈ W
    rwa [LinearEquiv.apply_symm_apply]
  have hx0 : quatEquiv.symm w ≠ 0 := by
    intro h; apply hw0
    have := congrArg quatEquiv h
    simpa using this
  rw [eq_top_iff]
  intro v _
  have h1 := hall (quatEquiv.symm v * (quatEquiv.symm w)⁻¹) hx
  rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at h1
  have h2 : quatEquiv (quatEquiv.symm v) ∈ W := h1
  rwa [LinearEquiv.apply_symm_apply] at h2

end UndergradKB.RepresentationTheory
