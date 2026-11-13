import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import UndergradKB.RepresentationTheory.ProblemsContent
import UndergradKB.Common.Attr

/-! # Problem 4.52, continued: `E` is diagonalizable (Etingof et al.)

On a representation `V` of `S_n` carrying an invariant positive definite Hermitian form `H`, each `ρ (a b)` is a
unitary involution, hence `H`-self-adjoint, so `E = (0 1) + ⋯ + (0 m)` is self-adjoint.  A self-adjoint operator
has an orthonormal eigenbasis with real eigenvalues, and for every polynomial `P`
`Tr P(E) = ∑ P(λ_i)`.  Combining with the trace formula `trace_aeval_jmOp` for `V_μ`, with
`P = ∏_c (X - e_c)²`, shows that all the eigenvalues of `E` are corner contents; hence `E` is diagonalizable
on `V_μ` with eigenvalues among the contents of the corners of `μ`.
-/

namespace UndergradKB.RepresentationTheory

open Finset Branching
open scoped Classical ComplexConjugate

namespace Content

/-- A self-adjoint operator for a positive definite Hermitian form has an eigenbasis with real eigenvalues, and
`Tr P(T) = ∑ P(λ_i)`. -/
theorem exists_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hH : IsPosDefHermitian H) (T : V →ₗ[ℂ] V)
    (hT : ∀ v w, H (T v) w = H v (T w)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (lam : Fin (Module.finrank ℂ V) → ℝ),
      (∀ i, T (b i) = (lam i : ℂ) • b i) ∧
        ∀ P : Polynomial ℂ, LinearMap.trace ℂ V (Polynomial.aeval T P) = ∑ i, P.eval (lam i : ℂ) := by
  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H x y
      conj_inner_symm := fun x y => hH.conj_symm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · subst hx; simp [Inner.inner]
        · exact (hH.pos x hx).2.le
      add_left := fun x y z => by simp [map_add]
      smul_left := fun x y r => by simp [map_smulₛₗ]
      definite := fun x hx => by
        by_contra hne
        have := (hH.pos x hne).2
        have h0 : H x x = 0 := hx
        rw [h0] at this
        simp at this }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (cd := cd)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hsym : T.IsSymmetric := fun x y => hT x y
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  refine ⟨(hsym.eigenvectorBasis hn).toBasis, hsym.eigenvalues hn, fun i => ?_, fun P => ?_⟩
  · simpa using hsym.apply_eigenvectorBasis hn i
  · rw [LinearMap.trace_eq_sum_inner _ (hsym.eigenvectorBasis hn)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev := hsym.hasEigenvector_eigenvectorBasis hn i
    rw [Module.End.aeval_apply_of_hasEigenvector hev, inner_smul_right]
    simp

/-- Every `ρ (a b)` is `H`-self-adjoint for an invariant form `H` (it is a unitary involution). -/
theorem swap_selfAdjoint {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hH : IsInvariantForm ρ H)
    (a b : Fin n) (v w : V) : H (ρ (Equiv.swap a b) v) w = H v (ρ (Equiv.swap a b) w) := by
  have h1 := hH (Equiv.swap a b) (ρ (Equiv.swap a b) v) w
  have h2 : ρ (Equiv.swap a b) (ρ (Equiv.swap a b) v) = v := by
    rw [← mul_apply_eq_comp, ← map_mul, Equiv.swap_mul_self, map_one]
    rfl
  rw [h2] at h1
  exact h1.symm

/-- `E = ∑_j ρ (0 j)` is self-adjoint for an invariant Hermitian form. -/
theorem jmOp_selfAdjoint {m : ℕ} (μ : DiagramsOfSize (m + 1))
    (H : (spechtIrrRep (m + 1) μ).V →ₗ⋆[ℂ] (spechtIrrRep (m + 1) μ).V →ₗ[ℂ] ℂ)
    (hH : IsInvariantForm (spechtIrrRep (m + 1) μ).ρ H) (v w : (spechtIrrRep (m + 1) μ).V) :
    H (jmOp μ v) w = H v (jmOp μ w) := by
  rw [jmOp_eq_sum]
  simp only [LinearMap.sum_apply, map_sum, LinearMap.add_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact swap_selfAdjoint _ H hH _ _ v w

/-- `E` has a basis of eigenvectors whose eigenvalues are the contents of corners of `μ`
(`m ≥ 2`, i.e. `n ≥ 3`). -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem jmOp_eigenbasis {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V)) ℂ (spechtIrrRep (m + 1) μ).V)
      (c : Fin (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V) → {c : ℕ × ℕ // IsCorner μ.1 c}),
      ∀ i, jmOp μ (b i) = (((c i).1.2 : ℂ) - ((c i).1.1 : ℂ)) • b i := by
  obtain ⟨H, hH, hHi⟩ := exists_invariantPosDefHermitian (spechtIrrRep (m + 1) μ).ρ
  obtain ⟨b, lam, hb, htr⟩ := exists_eigenbasis H hH (jmOp μ) (jmOp_selfAdjoint μ H hHi)
  -- every eigenvalue is a corner content
  set e : {c : ℕ × ℕ // IsCorner μ.1 c} → ℝ := fun c => (c.1.2 : ℝ) - c.1.1 with he
  set Q : Polynomial ℂ := ∏ c : {c : ℕ × ℕ // IsCorner μ.1 c}, (Polynomial.X - Polynomial.C ((e c : ℝ) : ℂ))
    with hQ
  have hQeval : ∀ x : ℝ, Q.eval (x : ℂ) = ((∏ c, (x - e c) : ℝ) : ℂ) := by
    intro x
    rw [hQ, Polynomial.eval_prod]
    push_cast
    simp
  have h1 := trace_aeval_jmOp hm μ (Q ^ 2)
  rw [htr] at h1
  have h2 : ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c},
      (Q ^ 2).eval ((c.1.2 : ℂ) - (c.1.1 : ℂ)) *
        (Module.finrank ℂ (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).V : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have : Q.eval ((c.1.2 : ℂ) - (c.1.1 : ℂ)) = 0 := by
      have hc : ((c.1.2 : ℂ) - (c.1.1 : ℂ)) = ((e c : ℝ) : ℂ) := by simp [he]
      rw [hc, hQeval]
      norm_cast
      exact Finset.prod_eq_zero (Finset.mem_univ c) (sub_self _)
    simp [this]
  rw [h2] at h1
  have h3 : ∀ i, ∏ c, (lam i - e c) = 0 := by
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum] at hre
    simp only [Polynomial.eval_pow, hQeval, Complex.zero_re] at hre
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V))),
        0 ≤ (∏ c, (lam i - e c)) ^ 2 := fun i _ => sq_nonneg _
    have hsum : ∑ i, (∏ c, (lam i - e c)) ^ 2 = 0 := by
      rw [← hre]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.ofReal_pow]
      exact (Complex.ofReal_re _).symm
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ _)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have h4 : ∀ i, ∃ c : {c : ℕ × ℕ // IsCorner μ.1 c}, lam i = e c := by
    intro i
    obtain ⟨c, _, hc⟩ := Finset.prod_eq_zero_iff.mp (h3 i)
    exact ⟨c, sub_eq_zero.mp hc⟩
  choose c hc using h4
  refine ⟨b, c, fun i => ?_⟩
  rw [hb i, hc i]
  simp [he]

theorem corner_coords_of_isRect {μ : YoungDiagram} (hR : IsRect μ) {d : ℕ × ℕ} (hd : IsCorner μ d) :
    d.2 + 1 = μ.rowLen 0 ∧ d.1 + 1 = μ.colLen 0 := by
  have hd1 : d.1 < μ.colLen 0 := by
    have := μ.up_left_mem le_rfl (Nat.zero_le d.2) hd.1
    exact YoungDiagram.mem_iff_lt_colLen.mp this
  have hr := hR d.1 hd1
  have h2 := rowLen_corner hd
  have hlast : d.1 + 1 ≥ μ.colLen 0 := by
    by_contra hlt
    push Not at hlt
    apply hd.2.1
    rw [YoungDiagram.mem_iff_lt_rowLen, hR (d.1 + 1) hlt]
    omega
  omega

/-- **Etingof et al., Problem 4.52(b)**: if `μ` is rectangular (`a` rows of length `b`), then `E` acts on `V_μ`
by the scalar `b - a`, the content of the unique corner. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem jmOp_eq_scalar_of_isRect {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) (hR : IsRect μ.1) :
    jmOp μ = algebraMap ℂ (Module.End ℂ (spechtIrrRep (m + 1) μ).V)
      ((μ.1.rowLen 0 : ℂ) - (μ.1.colLen 0 : ℂ)) := by
  obtain ⟨b, c, hbc⟩ := jmOp_eigenbasis hm μ
  refine b.ext fun i => ?_
  rw [hbc i, Module.algebraMap_end_apply]
  congr 1
  obtain ⟨h1, h2⟩ := corner_coords_of_isRect hR (c i).2
  have e1 : ((c i).1.2 : ℂ) + 1 = (μ.1.rowLen 0 : ℂ) := by exact_mod_cast h1
  have e2 : ((c i).1.1 : ℂ) + 1 = (μ.1.colLen 0 : ℂ) := by exact_mod_cast h2
  linear_combination e1 - e2

/-- **Etingof et al., Problem 4.52(b)**: `E` acts on the Specht module `V_μ` (`n ≥ 3`) by a scalar if and only
if `μ` is a rectangle; the scalar is then `(row length) - (number of rows)`. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem jmOp_scalar_iff_isRect {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) :
    (∃ s : ℂ, jmOp μ = algebraMap ℂ (Module.End ℂ (spechtIrrRep (m + 1) μ).V) s) ↔ IsRect μ.1 := by
  constructor
  · rintro ⟨s, hs⟩
    refine (unique_corner_iff_isRect μ.1).mp fun c c' hc hc' => ?_
    exact congrArg Subtype.val
      (unique_corner_of_jmOp_scalar hm μ s hs ⟨c, hc⟩ ⟨c', hc'⟩)
  · intro hR
    exact ⟨_, jmOp_eq_scalar_of_isRect hm μ hR⟩

/-- The polynomial `∏_{k = -m}^{m} (X - k)`. -/
noncomputable def intRangePoly (m : ℕ) : Polynomial ℂ :=
  ∏ k ∈ Finset.Icc (-(m : ℤ)) m, (Polynomial.X - Polynomial.C (k : ℂ))

theorem eval_intRangePoly_eq_zero {m : ℕ} {z : ℤ} (hz : -(m : ℤ) ≤ z ∧ z ≤ m) :
    (intRangePoly m).eval (z : ℂ) = 0 := by
  unfold intRangePoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr hz) (by simp)

/-- `∏_{k=-m}^m (E - k)` kills every Specht module of `S_{m+1}`. -/
theorem aeval_jmOp_intRange {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) :
    Polynomial.aeval (jmOp μ) (intRangePoly m) = 0 := by
  obtain ⟨b, c, hbc⟩ := jmOp_eigenbasis hm μ
  refine b.ext fun i => ?_
  have hev : Module.End.HasEigenvector (jmOp μ) (((c i).1.2 : ℂ) - ((c i).1.1 : ℂ)) (b i) :=
    ⟨Module.End.mem_eigenspace_iff.mpr (hbc i), b.ne_zero i⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev]
  have hbd := content_box_bounds (YoungDiagram.mem_cells _ |>.mp ((c i).2.1 |> fun h => (YoungDiagram.mem_cells _).mpr h))
  have hcard : (μ.1.card : ℤ) = m + 1 := by rw [μ.2]; push_cast; ring
  have hz : (((c i).1.2 : ℂ) - ((c i).1.1 : ℂ)) = (((((c i).1.2 : ℤ) - (c i).1.1 : ℤ)) : ℂ) := by push_cast; rfl
  rw [hz, eval_intRangePoly_eq_zero (z := ((c i).1.2 : ℤ) - (c i).1.1) ⟨by omega, by omega⟩]
  simp

/-- The element `E = (0 1) + ⋯ + (0 m)` of the group algebra of `S_{m+1}`. -/
noncomputable def jmElt (m : ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin (m + 1))) :=
  ∑ j : Fin m, MonoidAlgebra.of ℂ (Equiv.Perm (Fin (m + 1))) (Equiv.swap 0 j.succ)

theorem asAlgebraHom_jmElt {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    ρ.asAlgebraHom (jmElt m) = ∑ j : Fin m, ρ (Equiv.swap 0 j.succ) := by
  unfold jmElt
  rw [map_sum]
  simp [Representation.asAlgebraHom_of]

theorem asAlgebraHom_intRange {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    ρ.asAlgebraHom (Polynomial.aeval (jmElt m) (intRangePoly m)) =
      Polynomial.aeval (∑ j : Fin m, ρ (Equiv.swap 0 j.succ)) (intRangePoly m) := by
  rw [← asAlgebraHom_jmElt, ← Polynomial.aeval_algHom_apply]

/-- Equivalences of representations intertwine the action of the group algebra. -/
theorem asAlgebraHom_equiv {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : Representation.Equiv ρ σ) (a : MonoidAlgebra ℂ G) (v : V) :
    e (ρ.asAlgebraHom a v) = σ.asAlgebraHom a (e v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | single g r =>
    rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg _ (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)

/-- The polynomial `∏_{k=-m}^m (E - k)` vanishes in the group algebra of `S_{m+1}` (`m ≥ 2`). -/
theorem aeval_jmElt_intRange {m : ℕ} (hm : 2 ≤ m) :
    Polynomial.aeval (jmElt m) (intRangePoly m) = 0 := by
  have : Invertible (Nat.card (Equiv.Perm (Fin (m + 1))) : ℂ) := invertibleNatCard
  apply eq_zero_of_forall_simple
  intro S hS s hs
  let X := IrrRep.ofSimple (k := ℂ) (G := Equiv.Perm (Fin (m + 1))) S
  have hX : X.ρ.asAlgebraHom (Polynomial.aeval (jmElt m) (intRangePoly m)) = 0 := by
    obtain ⟨la, ⟨e⟩⟩ := exists_equiv_spechtModule (m + 1) X
    have hzero : (Representation.ofModule (k := ℂ) (G := Equiv.Perm (Fin (m + 1)))
        (spechtModule la)).asAlgebraHom (Polynomial.aeval (jmElt m) (intRangePoly m)) = 0 := by
      have h1 := asAlgebraHom_intRange (spechtIrrRep (m + 1) la).ρ
      rw [← jmOp_eq_sum] at h1
      rw [aeval_jmOp_intRange hm la] at h1
      exact h1
    refine LinearMap.ext fun v => ?_
    have h := asAlgebraHom_equiv e (Polynomial.aeval (jmElt m) (intRangePoly m)) v
    have h2 := congrArg (fun φ => φ (e v)) hzero
    exact (map_eq_zero_iff _ e.toLinearEquiv.injective).mp (h.trans h2)
  have := congrArg (fun φ : X.V →ₗ[ℂ] X.V ↦
    φ (show X.V from (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin (m + 1)))) S).symm
      ⟨s, hs⟩)) hX
  change (Representation.ofModule S).asAlgebraHom (Polynomial.aeval (jmElt m) (intRangePoly m))
    ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin (m + 1)))) S).symm ⟨s, hs⟩) = 0 at this
  erw [Representation.ofModule_asAlgebraHom_apply_apply] at this
  simp only [AddEquiv.apply_symm_apply, map_eq_zero_iff _
    (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin (m + 1)))) S).symm.injective] at this
  simpa using congrArg Subtype.val this

/-- **Etingof et al., Problem 4.52(a)**: on any finite-dimensional complex representation `ρ` of `S_{m+1}`
(`m ≥ 2`), the operator `E = ρ (0 1) + ⋯ + ρ (0 m)` is diagonalizable, with integer eigenvalues in
`[-m, m] = [1 - n, n - 1]` (`n = m + 1`). -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem jmElt_eigenbasis {m : ℕ} (hm : 2 ≤ m) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (k : Fin (Module.finrank ℂ V) → ℤ),
      (∀ i, -(m : ℤ) ≤ k i ∧ k i ≤ m) ∧
        ∀ i, (∑ j : Fin m, ρ (Equiv.swap 0 j.succ)) (b i) = (k i : ℂ) • b i := by
  obtain ⟨H, hH, hHi⟩ := exists_invariantPosDefHermitian ρ
  set T : V →ₗ[ℂ] V := ∑ j : Fin m, ρ (Equiv.swap 0 j.succ) with hT
  have hsymm : ∀ v w, H (T v) w = H v (T w) := by
    intro v w
    simp only [hT, LinearMap.sum_apply, map_sum, LinearMap.add_apply]
    exact Finset.sum_congr rfl fun j _ => swap_selfAdjoint ρ H hHi _ _ v w
  obtain ⟨b, lam, hb, -⟩ := exists_eigenbasis H hH T hsymm
  have hzero : Polynomial.aeval T (intRangePoly m) = 0 := by
    have := congrArg ρ.asAlgebraHom (aeval_jmElt_intRange hm)
    rw [asAlgebraHom_intRange, map_zero] at this
    exact this
  have hk : ∀ i, ∃ k : ℤ, -(m : ℤ) ≤ k ∧ k ≤ m ∧ (lam i : ℂ) = (k : ℂ) := by
    intro i
    have hev : Module.End.HasEigenvector T (lam i : ℂ) (b i) :=
      ⟨Module.End.mem_eigenspace_iff.mpr (hb i), b.ne_zero i⟩
    have h := Module.End.aeval_apply_of_hasEigenvector (p := intRangePoly m) hev
    rw [hzero] at h
    have h0 : (intRangePoly m).eval (lam i : ℂ) = 0 := by
      have h' : (intRangePoly m).eval (lam i : ℂ) • b i = 0 := by rw [← h]; rfl
      exact (smul_eq_zero.mp h').resolve_right (b.ne_zero i)
    unfold intRangePoly at h0
    rw [Polynomial.eval_prod] at h0
    obtain ⟨k, hkmem, hk0⟩ := Finset.prod_eq_zero_iff.mp h0
    have hk1 := Finset.mem_Icc.mp hkmem
    refine ⟨k, hk1.1, hk1.2, ?_⟩
    simpa [sub_eq_zero] using hk0
  choose k hk1 hk2 hk3 using hk
  exact ⟨b, k, fun i => ⟨hk1 i, hk2 i⟩, fun i => by rw [hb i, hk3 i]⟩

/-- `E` is annihilated by `∏_c (X - e_c)`, the product over the corner contents (so its minimal polynomial is
squarefree and split: `E` is diagonalizable). -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem aeval_jmOp_corners {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) :
    Polynomial.aeval (jmOp μ)
      (∏ c : {c : ℕ × ℕ // IsCorner μ.1 c},
        (Polynomial.X - Polynomial.C ((c.1.2 : ℂ) - (c.1.1 : ℂ)))) = 0 := by
  obtain ⟨b, c, hbc⟩ := jmOp_eigenbasis hm μ
  refine b.ext fun i => ?_
  have hev : Module.End.HasEigenvector (jmOp μ) (((c i).1.2 : ℂ) - ((c i).1.1 : ℂ)) (b i) :=
    ⟨Module.End.mem_eigenspace_iff.mpr (hbc i), b.ne_zero i⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev, Polynomial.eval_prod]
  rw [Finset.prod_eq_zero (Finset.mem_univ (c i)) (by simp)]
  simp

end Content

end UndergradKB.RepresentationTheory
