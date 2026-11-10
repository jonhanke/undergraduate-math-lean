import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-! # Projective geometry (Hefferon, Topic: Projective Geometry)

Points and lines of the real projective plane are nonzero vectors of `ℝ³` up to a scalar
(`Projectivization ℝ (Fin 3 → ℝ)`); a line is given by a row vector `L` and contains the point
`v` exactly when `L ⬝ᵥ v = 0`. -/

namespace UndergradKB.LinearAlgebra

open Matrix Projectivization

/-- The real projective plane: nonzero vectors of `ℝ³` up to nonzero scalar. It serves both for
points (column vectors) and for lines (row vectors of coefficients). -/
abbrev ProjPlane : Type := Projectivization ℝ (Fin 3 → ℝ)

/-- Incidence of a line `ℓ` (row vector) and a point `p` (column vector): `L ⬝ᵥ v = 0` for
representatives, which does not depend on the choice of representatives. -/
noncomputable def Incident (ℓ p : ProjPlane) : Prop := ℓ.rep ⬝ᵥ p.rep = 0

/-- A line is given by a nonzero row vector up to scalar, and a point lies on it iff the dot
product is zero, independent of representatives: rescaling either vector does not change it. -/
@[kb "hefferon2020" "Topic-Projective.2, p. 395"]
theorem hefferon_Topic_Projective_2 (L v : Fin 3 → ℝ) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    (c • L) ⬝ᵥ (d • v) = 0 ↔ L ⬝ᵥ v = 0 := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  simp [hc, hd]

/-- Point `v` is on line `L` in the projective sense iff `L ⬝ᵥ v = 0` for any representatives. -/
@[kb "hefferon2020" "Topic-Projective.3, p. 395"]
theorem hefferon_Topic_Projective_3 (L v : Fin 3 → ℝ) (hL : L ≠ 0) (hv : v ≠ 0) :
    Incident (mk ℝ L hL) (mk ℝ v hv) ↔ L ⬝ᵥ v = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℝ L hL
  obtain ⟨b, hb⟩ := exists_smul_eq_mk_rep ℝ v hv
  unfold Incident
  rw [← ha, ← hb]
  exact hefferon_Topic_Projective_2 L v _ _ a.ne_zero b.ne_zero

/-- Incidence is symmetric: a point on a line and a line through a point are the same relation
(this is why the roles of points and lines can be interchanged). -/
theorem incident_comm (ℓ p : ProjPlane) : Incident ℓ p ↔ Incident p ℓ := by
  unfold Incident
  rw [dotProduct_comm]

/-- Two nonzero vectors are linearly independent iff they give different projective points. -/
theorem pair_li_iff_mk_ne {v w : Fin 3 → ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    LinearIndependent ℝ ![v, w] ↔ mk ℝ v hv ≠ mk ℝ w hw := by
  rw [← independent_mk_iff_LinearIndependent hv hw, independent_pair_iff_ne]

/-! ### Collinearity and determinants -/

theorem det_eq_zero_iff_not_li (a b c : Fin 3 → ℝ) :
    (Matrix.of ![a, b, c]).det = 0 ↔ ¬ LinearIndependent ℝ ![a, b, c] := by
  have h := Matrix.linearIndependent_row_iff_isUnit (A := Matrix.of ![a, b, c])
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at h
  have h' : LinearIndependent ℝ ![a, b, c] ↔ (Matrix.of ![a, b, c]).det ≠ 0 := h
  rw [h', not_not]

theorem isCollinear_iff_not_li (a b c : Fin 3 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    IsCollinear ({mk ℝ a ha, mk ℝ b hb, mk ℝ c hc} : Set ProjPlane) ↔
      ¬ LinearIndependent ℝ ![a, b, c] := by
  constructor
  · rintro ⟨M, hfin, hrank, hsub⟩ hli
    have hmem : ∀ i, (![a, b, c] : Fin 3 → Fin 3 → ℝ) i ∈ M.submodule := by
      intro i
      fin_cases i
      · exact (Subspace.mem_submodule_iff M ha).2 (hsub (by simp))
      · exact (Subspace.mem_submodule_iff M hb).2 (hsub (by simp))
      · exact (Subspace.mem_submodule_iff M hc).2 (hsub (by simp))
    have hle : Submodule.span ℝ (Set.range ![a, b, c]) ≤ M.submodule :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hmem i)
    have h3 := finrank_span_eq_card hli
    have h4 := Submodule.finrank_mono hle
    simp only [Fintype.card_fin] at h3
    omega
  · intro hnli
    refine ⟨(Submodule.span ℝ (Set.range ![a, b, c])).projectivization, ?_, ?_, ?_⟩
    · rw [Subspace.submodule.apply_symm_apply]; infer_instance
    · rw [Subspace.submodule.apply_symm_apply]
      have h1 := finrank_range_le_card (R := ℝ) ![a, b, c]
      have h2 := (linearIndependent_iff_card_eq_finrank_span (R := ℝ) (b := ![a, b, c])).not.1 hnli
      simp only [Fintype.card_fin] at h1 h2
      have : (Set.range ![a, b, c]).finrank ℝ = Module.finrank ℝ (Submodule.span ℝ (Set.range ![a, b, c])) := rfl
      omega
    · intro x hx
      have hsp : ∀ (v : Fin 3 → ℝ) (hv : v ≠ 0), v ∈ Set.range ![a, b, c] →
          mk ℝ v hv ∈ (Submodule.span ℝ (Set.range ![a, b, c])).projectivization := fun v hv h =>
        (Submodule.mk_mem_projectivization_iff _ hv).2 (Submodule.subset_span h)
      rcases hx with rfl | rfl | rfl
      · exact hsp a ha ⟨0, rfl⟩
      · exact hsp b hb ⟨1, rfl⟩
      · exact hsp c hc ⟨2, rfl⟩

/-- Three projective points are collinear iff the determinant of representatives is zero iff the
representatives are linearly dependent; dually, three lines (row vectors) are concurrent iff the
determinant of the rows is zero. -/
@[kb "hefferon2020" "Topic-Projective.7, p. 397"]
theorem hefferon_Topic_Projective_7 :
    (∀ (a b c : Fin 3 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
      (IsCollinear ({mk ℝ a ha, mk ℝ b hb, mk ℝ c hc} : Set ProjPlane) ↔
        (Matrix.of ![a, b, c]).det = 0) ∧
      ((Matrix.of ![a, b, c]).det = 0 ↔ ¬ LinearIndependent ℝ ![a, b, c])) ∧
    (∀ L₀ L₁ L₂ : Fin 3 → ℝ,
      (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ L₀ ⬝ᵥ v = 0 ∧ L₁ ⬝ᵥ v = 0 ∧ L₂ ⬝ᵥ v = 0) ↔
        (Matrix.of ![L₀, L₁, L₂]).det = 0) := by
  refine ⟨fun a b c ha hb hc => ⟨?_, det_eq_zero_iff_not_li a b c⟩, fun L₀ L₁ L₂ => ?_⟩
  · rw [isCollinear_iff_not_li a b c ha hb hc, det_eq_zero_iff_not_li]
  · rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h0, h1, h2⟩
      refine ⟨v, hv, ?_⟩
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2 ⊢ <;>
        linarith
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_, ?_, ?_⟩
      · simpa [Matrix.mulVec, dotProduct] using congrFun h 0
      · simpa [Matrix.mulVec, dotProduct] using congrFun h 1
      · simpa [Matrix.mulVec, dotProduct] using congrFun h 2

/-! ### Duality -/

/-- Any two distinct points lie on exactly one line. -/
theorem exists_unique_line (p q : ProjPlane) (h : p ≠ q) :
    ∃! ℓ : ProjPlane, Incident ℓ p ∧ Incident ℓ q := by
  induction p using Projectivization.ind with | h v hv =>
  induction q using Projectivization.ind with | h w hw =>
  have hli : LinearIndependent ℝ ![v, w] := (pair_li_iff_mk_ne hv hw).2 h
  have hn : v ⨯₃ w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2 hli
  refine ⟨mk ℝ (v ⨯₃ w) hn, ⟨?_, ?_⟩, ?_⟩
  · rw [hefferon_Topic_Projective_3, dotProduct_comm]; exact dot_self_cross v w
  · rw [hefferon_Topic_Projective_3, dotProduct_comm]; exact dot_cross_self v w
  · intro ℓ' ⟨h1, h2⟩
    induction ℓ' using Projectivization.ind with | h L hL =>
    rw [hefferon_Topic_Projective_3] at h1 h2
    by_contra hne
    have hli' : LinearIndependent ℝ ![L, v ⨯₃ w] := (pair_li_iff_mk_ne hL hn).2 hne
    have hc := crossProduct_ne_zero_iff_linearIndependent.2 hli'
    apply hc
    rw [cross_cross_eq_smul_sub_smul', h2, dotProduct_comm, h1]
    simp

/-- Duality principle, concretely. Incidence of a line and a point is a symmetric relation, so
the roles of points and lines are interchangeable; applied to the statement "two distinct points
lie on a unique line" it gives "two distinct lines meet in a unique point". -/
@[kb "hefferon2020" "Topic-Projective.5, p. 396"]
theorem hefferon_Topic_Projective_5 :
    (∀ ℓ p : ProjPlane, Incident ℓ p ↔ Incident p ℓ) ∧
    (∀ p q : ProjPlane, p ≠ q → ∃! ℓ : ProjPlane, Incident ℓ p ∧ Incident ℓ q) ∧
    (∀ ℓ m : ProjPlane, ℓ ≠ m → ∃! p : ProjPlane, Incident ℓ p ∧ Incident m p) := by
  refine ⟨incident_comm, exists_unique_line, fun ℓ m h => ?_⟩
  simp only [incident_comm ℓ, incident_comm m]
  exact exists_unique_line ℓ m h

/-! ### The frame lemma -/

/-- Frame lemma: four points of the projective plane, no three collinear (every three of the
representatives are linearly independent), have representatives that are, for the first three,
the vectors of a basis of `ℝ³` and, for the fourth, the sum of those three basis vectors. The
representatives are the given vectors rescaled by the nonzero `c i`. -/
@[kb "hefferon2020" "Topic-Projective.9, p. 398"]
theorem hefferon_Topic_Projective_9 (p : Fin 4 → (Fin 3 → ℝ))
    (h : ∀ t : Fin 3 → Fin 4, Function.Injective t → LinearIndependent ℝ (p ∘ t)) :
    ∃ (B : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ)) (c : Fin 4 → ℝ), (∀ i, c i ≠ 0) ∧
      (∀ i : Fin 3, c i.castSucc • p i.castSucc = B i) ∧ c 3 • p 3 = B 0 + B 1 + B 2 := by
  have hli : LinearIndependent ℝ (p ∘ Fin.castSucc) := h _ (Fin.castSucc_injective 3)
  let b0 : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb0 : ∀ i, b0 i = p i.castSucc := fun i => by simp [b0]
  set a : Fin 3 → ℝ := fun i => b0.repr (p 3) i with ha
  have hsum : a 0 • p 0 + a 1 • p 1 + a 2 • p 2 = p 3 := by
    have := b0.sum_repr (p 3)
    rw [Fin.sum_univ_three, hb0, hb0, hb0] at this
    exact this
  have h0 : a 0 ≠ 0 := by
    intro h0
    have := (Fintype.linearIndependent_iff.1 (h ![1, 2, 3] (by decide))) ![a 1, a 2, -1]
      (by
        simp [Fin.sum_univ_three]
        rw [h0, zero_smul] at hsum
        rw [← hsum]
        module) 2
    simp at this
  have h1 : a 1 ≠ 0 := by
    intro h1
    have := (Fintype.linearIndependent_iff.1 (h ![0, 2, 3] (by decide))) ![a 0, a 2, -1]
      (by
        simp [Fin.sum_univ_three]
        rw [h1, zero_smul] at hsum
        rw [← hsum]
        module) 2
    simp at this
  have h2 : a 2 ≠ 0 := by
    intro h2
    have := (Fintype.linearIndependent_iff.1 (h ![0, 1, 3] (by decide))) ![a 0, a 1, -1]
      (by
        simp [Fin.sum_univ_three]
        rw [h2, zero_smul] at hsum
        rw [← hsum]
        module) 2
    simp at this
  have hu : ∀ i, a i ≠ 0 := fun i => by fin_cases i <;> assumption
  let B := b0.unitsSMul (fun i => Units.mk0 (a i) (hu i))
  have hB : ∀ i, B i = a i • p i.castSucc := fun i => by rw [Module.Basis.unitsSMul_apply, Units.smul_def, hb0]; rfl
  refine ⟨B, ![a 0, a 1, a 2, 1], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hu]
  · intro i
    rw [hB]
    fin_cases i <;> rfl
  · rw [hB, hB, hB]
    simpa using hsum.symm

/-! ### Desargues' theorem -/

private lemma finrank_span_pair {u v : Fin 3 → ℝ} (h : LinearIndependent ℝ ![u, v]) :
    Module.finrank ℝ (Submodule.span ℝ {u, v}) = 2 := by
  rw [← Matrix.range_cons_cons_empty _ _ ![]]
  simp [finrank_span_eq_card h]

private lemma pair_of_family {A : Fin 3 → Fin 3 → ℝ} (hA : LinearIndependent ℝ A) {i j : Fin 3}
    (hij : i ≠ j) : LinearIndependent ℝ ![A i, A j] := by
  have := hA.comp ![i, j] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)
  convert this using 1
  funext x
  fin_cases x <;> rfl

private lemma inter_one_dim (S T : Submodule ℝ (Fin 3 → ℝ)) (hS : Module.finrank ℝ S = 2)
    (hT : Module.finrank ℝ T = 2) (hne : S ≠ T) {w P : Fin 3 → ℝ} (hw : w ∈ S ⊓ T) (hw0 : w ≠ 0)
    (hP : P ∈ S ⊓ T) : ∃ c : ℝ, P = c • w := by
  have hsup : Module.finrank ℝ (S ⊔ T : Submodule ℝ (Fin 3 → ℝ)) ≤ 3 := by
    have := Submodule.finrank_le (S ⊔ T)
    simpa using this
  have h1 : 2 < Module.finrank ℝ (S ⊔ T : Submodule ℝ (Fin 3 → ℝ)) := by
    by_contra hcon
    apply hne
    have e1 : S = S ⊔ T := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have e2 : T = S ⊔ T := Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    rw [e1, ← e2]
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq S T
  have h3 : Module.finrank ℝ (S ⊓ T : Submodule ℝ (Fin 3 → ℝ)) = 1 := by omega
  have key := (finrank_eq_one_iff_of_ne_zero' (K := ℝ) (V := ↥(S ⊓ T)) ⟨w, hw⟩
    (fun h => hw0 (congrArg Subtype.val h))).1 h3 ⟨P, hP⟩
  obtain ⟨c, hc⟩ := key
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

private lemma fin3_facts : ((0 : Fin 3) + 1 = 1 ∧ (0 : Fin 3) + 2 = 2 ∧ (1 : Fin 3) + 1 = 2 ∧
    (1 : Fin 3) + 2 = 0 ∧ (2 : Fin 3) + 1 = 0 ∧ (2 : Fin 3) + 2 = 1) := by decide

/-- A vertex of the second triangle lies in the plane of `O` and the corresponding vertex of the
first triangle, with both coefficients nonzero. -/
private lemma perspective_coeffs {O A B : Fin 3 → ℝ} (hOA : LinearIndependent ℝ ![O, A])
    (hOB : LinearIndependent ℝ ![O, B]) (hAB : LinearIndependent ℝ ![A, B])
    (hper : ¬ LinearIndependent ℝ ![O, A, B]) :
    ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ B = y • O + x • A := by
  rw [Fintype.not_linearIndependent_iff] at hper
  obtain ⟨g, hg, k, hk⟩ := hper
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at hg
    obtain ⟨e0, e1⟩ := LinearIndependent.pair_iff.1 hOA (g 0) (g 1) hg
    fin_cases k
    · exact hk e0
    · exact hk e1
    · exact hk h2
  have hy : g 2 * (-g 0 / g 2) = -g 0 := by field_simp
  have hx : g 2 * (-g 1 / g 2) = -g 1 := by field_simp
  have hB : B = (-g 0 / g 2) • O + (-g 1 / g 2) • A := by
    apply smul_right_injective _ hg2
    simp only [smul_add, smul_smul, hy, hx]
    linear_combination (norm := module) hg
  refine ⟨-g 1 / g 2, -g 0 / g 2, ?_, ?_, hB⟩
  · intro h0
    rw [h0, zero_smul, add_zero] at hB
    have := LinearIndependent.pair_iff.1 hOB (-g 0 / g 2) (-1) (by rw [hB]; module)
    simp at this
  · intro h0
    rw [h0, zero_smul, zero_add] at hB
    have := LinearIndependent.pair_iff.1 hAB (-g 1 / g 2) (-1) (by rw [hB]; module)
    simp at this

/-- Desargues' theorem in the real projective plane. Two triangles `A₀A₁A₂` and `B₀B₁B₂`
(non-degenerate, with representative vectors in `ℝ³`) are in perspective from the point `O`
(each `O, Aᵢ, Bᵢ` is collinear, and these three points are pairwise distinct). If `Pₖ` is a point
on both the side `Aₖ₊₁Aₖ₊₂` and the side `Bₖ₊₁Bₖ₊₂` (the two sides being distinct lines), then
`P₀, P₁, P₂` are collinear, i.e. their representatives are linearly dependent. -/
@[kb "hefferon2020" "Topic-Projective.8, p. 397"]
theorem hefferon_Topic_Projective_8 (O : Fin 3 → ℝ) (A B P : Fin 3 → Fin 3 → ℝ)
    (hA : LinearIndependent ℝ A) (hB : LinearIndependent ℝ B)
    (hOA : ∀ i, LinearIndependent ℝ ![O, A i]) (hOB : ∀ i, LinearIndependent ℝ ![O, B i])
    (hAB : ∀ i, LinearIndependent ℝ ![A i, B i])
    (hper : ∀ i, ¬ LinearIndependent ℝ ![O, A i, B i])
    (hPA : ∀ k, P k ∈ Submodule.span ℝ {A (k + 1), A (k + 2)})
    (hPB : ∀ k, P k ∈ Submodule.span ℝ {B (k + 1), B (k + 2)})
    (hne : ∀ k, Submodule.span ℝ {A (k + 1), A (k + 2)} ≠ Submodule.span ℝ {B (k + 1), B (k + 2)})
    (hP0 : ∀ k, P k ≠ 0) :
    ¬ LinearIndependent ℝ P := by
  have hco := fun i => perspective_coeffs (hOA i) (hOB i) (hAB i) (hper i)
  choose x y hx hy hBi using hco
  -- the normalized vertices `u i = O + (x i / y i) • A i = (y i)⁻¹ • B i`
  let u : Fin 3 → Fin 3 → ℝ := fun i => O + (x i / y i) • A i
  have hu : ∀ i, u i = (y i)⁻¹ • B i := by
    intro i
    simp only [u, hBi i, smul_add, smul_smul]
    rw [inv_mul_cancel₀ (hy i)]
    congr 1
    · simp
    · congr 1; field_simp
  let w : Fin 3 → Fin 3 → ℝ := fun k => u (k + 1) - u (k + 2)
  have hk12 : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  have hwA : ∀ k, w k ∈ Submodule.span ℝ {A (k + 1), A (k + 2)} := by
    intro k
    have : w k = (x (k + 1) / y (k + 1)) • A (k + 1) - (x (k + 2) / y (k + 2)) • A (k + 2) := by
      simp only [w, u]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hwB : ∀ k, w k ∈ Submodule.span ℝ {B (k + 1), B (k + 2)} := by
    intro k
    have : w k = (y (k + 1))⁻¹ • B (k + 1) - (y (k + 2))⁻¹ • B (k + 2) := by
      simp only [w]; rw [hu, hu]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hw0 : ∀ k, w k ≠ 0 := by
    intro k hk
    have e : w k = (x (k + 1) / y (k + 1)) • A (k + 1) + (-(x (k + 2) / y (k + 2))) • A (k + 2) := by
      simp only [w, u]; module
    rw [e] at hk
    have := (LinearIndependent.pair_iff.1 (pair_of_family hA (hk12 k))) _ _ hk
    exact div_ne_zero (hx _) (hy _) this.1
  have hc : ∀ k, ∃ c : ℝ, P k = c • w k := by
    intro k
    exact inter_one_dim _ _ (finrank_span_pair (pair_of_family hA (hk12 k)))
      (finrank_span_pair (pair_of_family hB (hk12 k))) (hne k)
      (Submodule.mem_inf.2 ⟨hwA k, hwB k⟩) (hw0 k) (Submodule.mem_inf.2 ⟨hPA k, hPB k⟩)
  choose c hc using hc
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k h0
    apply hP0 k
    rw [hc k, h0, zero_smul]
  have hsum : ∑ k, (c k)⁻¹ • P k = 0 := by
    have : ∀ k, (c k)⁻¹ • P k = w k := by
      intro k
      rw [hc k, smul_smul, inv_mul_cancel₀ (hc0 k), one_smul]
    simp only [this, Fin.sum_univ_three, w]
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fin3_facts
    simp only [f1, f2, f3, f4, f5, f6]
    abel
  rw [Fintype.not_linearIndependent_iff]
  exact ⟨fun k => (c k)⁻¹, hsum, 0, inv_ne_zero (hc0 0)⟩

/-! ### The Euclidean plane inside the projective plane -/

private lemma affine_ne_zero (x y : ℝ) : (![x, y, 1] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 2
  simp at this

/-- The point `(x, y)` of the Euclidean plane, as the projective point of `(x, y, 1)`. -/
noncomputable def affinePoint (x y : ℝ) : ProjPlane := mk ℝ ![x, y, 1] (affine_ne_zero x y)

/-- The line `a x + b y = c` of the Euclidean plane, as the projective line with row vector
`(a, b, -c)` (requires `(a, b) ≠ 0`). -/
noncomputable def affineLine (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : ProjPlane :=
  mk ℝ ![a, b, -c] (by
    intro h0
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp at h1 h2
    rcases h with h | h
    · exact h h1
    · exact h h2)

/-- The line at infinity: the row vector `(0, 0, 1)`. -/
noncomputable def lineAtInfinity : ProjPlane :=
  mk ℝ ![0, 0, 1] (by intro h; have := congrFun h 2; simp at this)

/-- The Euclidean plane `z = 1` embeds in the projective plane; its image is exactly the set of
points off the line at infinity `z = 0`; the line `a x + b y = c` is the set of embedded points
on its projective line, and two distinct parallel lines (same `(a, b)`, different `c`) have no
common Euclidean point but meet, in exactly one point, which is an ideal point (on the line at
infinity). -/
@[kb "hefferon2020" "Topic-Projective.6, p. 396"]
theorem hefferon_Topic_Projective_6 :
    (∀ x y x' y', affinePoint x y = affinePoint x' y' → x = x' ∧ y = y') ∧
    (∀ p : ProjPlane, (∃ x y, p = affinePoint x y) ↔ ¬ Incident lineAtInfinity p) ∧
    (∀ a b c (h : a ≠ 0 ∨ b ≠ 0) x y,
      Incident (affineLine a b c h) (affinePoint x y) ↔ a * x + b * y = c) ∧
    (∀ a b c d (h : a ≠ 0 ∨ b ≠ 0), c ≠ d → ∃ q : ProjPlane, Incident lineAtInfinity q ∧
      (∀ x y, ¬ (a * x + b * y = c ∧ a * x + b * y = d)) ∧
      ∀ r, (Incident (affineLine a b c h) r ∧ Incident (affineLine a b d h) r) ↔ r = q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y x' y' h
    unfold affinePoint at h
    rw [mk_eq_mk_iff'] at h
    obtain ⟨t, ht⟩ := h
    have h2 := congrFun ht 2
    have h0 := congrFun ht 0
    have h1 := congrFun ht 1
    simp at h2 h0 h1
    subst h2
    simp at h0 h1
    exact ⟨h0.symm, h1.symm⟩
  · intro p
    constructor
    · rintro ⟨x, y, rfl⟩
      unfold lineAtInfinity affinePoint
      rw [hefferon_Topic_Projective_3]
      simp [dotProduct, Fin.sum_univ_three]
    · intro hp
      induction p using Projectivization.ind with | h v hv =>
      unfold lineAtInfinity at hp
      rw [hefferon_Topic_Projective_3] at hp
      simp [dotProduct, Fin.sum_univ_three] at hp
      refine ⟨v 0 / v 2, v 1 / v 2, ?_⟩
      unfold affinePoint
      rw [mk_eq_mk_iff']
      refine ⟨v 2, ?_⟩
      funext i
      fin_cases i <;> simp [hp] <;> field_simp
  · intro a b c h x y
    unfold affineLine affinePoint
    rw [hefferon_Topic_Projective_3]
    simp [dotProduct, Fin.sum_univ_three]
    constructor <;> intro e <;> linarith
  · intro a b c d h hcd
    have hq : (![-b, a, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro h0
      have h1 := congrFun h0 0
      have h2 := congrFun h0 1
      simp at h1 h2
      rcases h with h | h
      · exact h h2
      · exact h h1
    refine ⟨mk ℝ _ hq, ?_, ?_, ?_⟩
    · unfold lineAtInfinity
      rw [hefferon_Topic_Projective_3]
      simp [dotProduct, Fin.sum_univ_three]
    · rintro x y ⟨h1, h2⟩
      exact hcd (h1.symm.trans h2)
    · intro r
      induction r using Projectivization.ind with | h v hv =>
      unfold affineLine
      rw [hefferon_Topic_Projective_3, hefferon_Topic_Projective_3]
      simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      constructor
      · rintro ⟨e1, e2⟩
        have hv2 : v 2 = 0 := by
          have : (d - c) * v 2 = 0 := by linarith
          rcases mul_eq_zero.1 this with h0 | h0
          · exact absurd (by linarith) hcd
          · exact h0
        have e3 : a * v 0 + b * v 1 = 0 := by rw [hv2] at e1; linarith
        rw [mk_eq_mk_iff']
        rcases h with h | h
        · refine ⟨v 1 / a, ?_⟩
          funext i
          fin_cases i <;> simp [hv2] <;> field_simp <;> linarith
        · refine ⟨-v 0 / b, ?_⟩
          funext i
          fin_cases i <;> simp [hv2] <;> field_simp <;> linarith
      · intro e
        rw [mk_eq_mk_iff'] at e
        obtain ⟨t, ht⟩ := e
        have h0 := congrFun ht 0
        have h1 := congrFun ht 1
        have h2 := congrFun ht 2
        simp at h0 h1 h2
        rw [← h0, ← h1, ← h2]
        constructor <;> ring

end UndergradKB.LinearAlgebra
