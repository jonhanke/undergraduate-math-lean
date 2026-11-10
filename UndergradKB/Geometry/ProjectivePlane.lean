import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.ProjectiveDuality
import UndergradKB.Geometry.AffineSpaceModel

/-! # The projective plane in the space model (Petrunin, chapter 15)

Sections 15A, 15D-15G of Petrunin's *Euclidean plane and its relatives*, worked in the space model of
`ProjectiveDuality.lean` (points of the projective plane are the lines thru the origin of `ℝ³`, lines are the
planes thru the origin).  We set up the linear algebra (representing vectors, collinearity as the vanishing of a
`3 × 3` determinant, joins of points), then prove Desargues' theorem with its dual (the book's duality
argument), Pappus' theorem with its dual, pencils of lines and the projective completion, projective
transformations induced by `GL₃`, the classification of Theorem 15.2, the invariance of the cross-ratio and
polars with respect to a circle.
-/

namespace UndergradKB.Geometry

open Module
open scoped RealInnerProductSpace

/-! ## Linear algebra of the space model -/

section Foundations

/-- The point of the space model spanned by a nonzero vector of `ℝ³`. -/
noncomputable def ProjPoint.mk' (v : Space3) (hv : v ≠ 0) : ProjPoint :=
  ⟨Submodule.span ℝ {v}, finrank_span_singleton hv⟩

theorem ProjPoint.mem_mk' {v w : Space3} (hv : v ≠ 0) :
    w ∈ (ProjPoint.mk' v hv).1 ↔ ∃ t : ℝ, t • v = w :=
  Submodule.mem_span_singleton

theorem ProjPoint.exists_rep (P : ProjPoint) : ∃ (v : Space3) (hv : v ≠ 0), P = ProjPoint.mk' v hv := by
  have hne : P.1 ≠ ⊥ := by
    intro h
    have := P.2
    rw [h] at this
    simp at this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, Subtype.ext ?_⟩
  exact (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v P.1).2 hv)
    (by rw [finrank_span_singleton hv0, P.2])).symm

theorem ProjPoint.mk'_eq_iff {v w : Space3} (hv : v ≠ 0) (hw : w ≠ 0) :
    ProjPoint.mk' v hv = ProjPoint.mk' w hw ↔ ∃ t : ℝ, t • v = w := by
  constructor
  · intro h
    have h' : Submodule.span ℝ {v} = Submodule.span ℝ {w} := congrArg Subtype.val h
    have : w ∈ Submodule.span ℝ {v} := by rw [h']; exact Submodule.mem_span_singleton_self _
    exact Submodule.mem_span_singleton.mp this
  · rintro ⟨t, rfl⟩
    have ht : t ≠ 0 := by rintro rfl; exact hw (by simp)
    apply Subtype.ext
    exact (Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht) v).symm

theorem ProjPoint.mk'_liesOn_iff {v : Space3} (hv : v ≠ 0) (ℓ : ProjLine) :
    (ProjPoint.mk' v hv).LiesOn ℓ ↔ v ∈ ℓ.1 :=
  Submodule.span_singleton_le_iff_mem v ℓ.1

/-- The determinant of three vectors of `ℝ³` (the triple product). -/
def det3 (u v w : Space3) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- The line of the space model with normal vector `n`. -/
noncomputable def lineOfNormal (n : Space3) (hn : n ≠ 0) : ProjLine :=
  projDuality (ProjPoint.mk' n hn)

theorem ProjLine.exists_normal (ℓ : ProjLine) : ∃ (n : Space3) (hn : n ≠ 0), ℓ = lineOfNormal n hn := by
  obtain ⟨n, hn, h⟩ := (projDuality.symm ℓ).exists_rep
  refine ⟨n, hn, ?_⟩
  unfold lineOfNormal
  rw [← h]
  simp

theorem mk'_liesOn_lineOfNormal {v n : Space3} (hv : v ≠ 0) (hn : n ≠ 0) :
    (ProjPoint.mk' v hv).LiesOn (lineOfNormal n hn) ↔ n 0 * v 0 + n 1 * v 1 + n 2 * v 2 = 0 := by
  rw [ProjPoint.mk'_liesOn_iff]
  change v ∈ (Submodule.span ℝ {n})ᗮ ↔ _
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm, inner_space3]

/-- Collinearity of three points of the projective plane: they lie on a common line. -/
def ProjCollinear (P Q R : ProjPoint) : Prop :=
  ∃ ℓ : ProjLine, P.LiesOn ℓ ∧ Q.LiesOn ℓ ∧ R.LiesOn ℓ

/-- Three points of the space model are collinear iff the determinant of representing vectors vanishes. -/
theorem projCollinear_mk'_iff {u v w : Space3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    ProjCollinear (ProjPoint.mk' u hu) (ProjPoint.mk' v hv) (ProjPoint.mk' w hw) ↔ det3 u v w = 0 := by
  constructor
  · rintro ⟨ℓ, h1, h2, h3⟩
    obtain ⟨n, hn, rfl⟩ := ℓ.exists_normal
    rw [mk'_liesOn_lineOfNormal] at h1 h2 h3
    have e0 : det3 u v w * n 0 = 0 := by
      unfold det3
      linear_combination (v 1 * w 2 - v 2 * w 1) * h1 - (u 1 * w 2 - u 2 * w 1) * h2 +
        (u 1 * v 2 - u 2 * v 1) * h3
    have e1 : det3 u v w * n 1 = 0 := by
      unfold det3
      linear_combination -(v 0 * w 2 - v 2 * w 0) * h1 + (u 0 * w 2 - u 2 * w 0) * h2 -
        (u 0 * v 2 - u 2 * v 0) * h3
    have e2 : det3 u v w * n 2 = 0 := by
      unfold det3
      linear_combination (v 0 * w 1 - v 1 * w 0) * h1 - (u 0 * w 1 - u 1 * w 0) * h2 +
        (u 0 * v 1 - u 1 * v 0) * h3
    by_contra hd
    apply hn
    ext i
    fin_cases i
    · simpa [hd] using e0
    · simpa [hd] using e1
    · simpa [hd] using e2
  · intro hd
    set M : Matrix (Fin 3) (Fin 3) ℝ := !![u 0, u 1, u 2; v 0, v 1, v 2; w 0, w 1, w 2] with hM
    have hdet : M.det = 0 := by
      rw [hM, Matrix.det_fin_three]
      simp
      unfold det3 at hd
      linear_combination hd
    obtain ⟨n, hn, hMn⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hn' : (WithLp.toLp 2 n : Space3) ≠ 0 := by
      intro h
      apply hn
      ext i
      have := congrArg (fun x : Space3 => x i) h
      simpa using this
    have r0 := congrFun hMn 0
    have r1 := congrFun hMn 1
    have r2 := congrFun hMn 2
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at r0 r1 r2
    refine ⟨lineOfNormal _ hn', ?_, ?_, ?_⟩
    · rw [mk'_liesOn_lineOfNormal]; simp; linear_combination r0
    · rw [mk'_liesOn_lineOfNormal]; simp; linear_combination r1
    · rw [mk'_liesOn_lineOfNormal]; simp; linear_combination r2

theorem finrank_sup_eq_two {P Q : ProjPoint} (hPQ : P ≠ Q) : finrank ℝ ↥(P.1 ⊔ Q.1) = 2 := by
  have hne : P.1 ≠ Q.1 := fun h => hPQ (Subtype.ext h)
  have hinf : P.1 ⊓ Q.1 = ⊥ := by
    by_contra h
    have hle : finrank ℝ ↥(P.1 ⊓ Q.1) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : P.1 ⊓ Q.1 ≤ P.1)
      rwa [P.2] at this
    have hpos : finrank ℝ ↥(P.1 ⊓ Q.1) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
    have h1 : finrank ℝ ↥(P.1 ⊓ Q.1) = 1 := by omega
    have eP : P.1 ⊓ Q.1 = P.1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, P.2])
    have eQ : P.1 ⊓ Q.1 = Q.1 := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, Q.2])
    exact hne (eP.symm.trans eQ)
  have := Submodule.finrank_sup_add_finrank_inf_eq P.1 Q.1
  rw [hinf, finrank_bot, P.2, Q.2] at this
  omega

/-- The line through two distinct points of the projective plane. -/
noncomputable def ProjPoint.join (P Q : ProjPoint) (hPQ : P ≠ Q) : ProjLine :=
  ⟨P.1 ⊔ Q.1, finrank_sup_eq_two hPQ⟩

theorem ProjPoint.left_liesOn_join {P Q : ProjPoint} (h : P ≠ Q) : P.LiesOn (P.join Q h) :=
  le_sup_left

theorem ProjPoint.right_liesOn_join {P Q : ProjPoint} (h : P ≠ Q) : Q.LiesOn (P.join Q h) :=
  le_sup_right

theorem ProjPoint.eq_join_of {P Q : ProjPoint} (h : P ≠ Q) {ℓ : ProjLine} (hP : P.LiesOn ℓ)
    (hQ : Q.LiesOn ℓ) : ℓ = P.join Q h := by
  apply Subtype.ext
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hP hQ) (by rw [finrank_sup_eq_two h, ℓ.2])).symm

theorem projCollinear_iff_liesOn_join {P Q R : ProjPoint} (h : P ≠ Q) :
    ProjCollinear P Q R ↔ R.LiesOn (P.join Q h) := by
  constructor
  · rintro ⟨ℓ, hP, hQ, hR⟩
    rw [ProjPoint.eq_join_of h hP hQ] at hR
    exact hR
  · intro hR
    exact ⟨P.join Q h, P.left_liesOn_join h, ProjPoint.right_liesOn_join h, hR⟩

theorem ProjCollinear.symm12 {P Q R : ProjPoint} (h : ProjCollinear P Q R) : ProjCollinear Q P R := by
  obtain ⟨ℓ, a, b, c⟩ := h; exact ⟨ℓ, b, a, c⟩

theorem ProjCollinear.symm23 {P Q R : ProjPoint} (h : ProjCollinear P Q R) : ProjCollinear P R Q := by
  obtain ⟨ℓ, a, b, c⟩ := h; exact ⟨ℓ, a, c, b⟩

theorem mem_sup_mk' {p q r : Space3} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (ProjPoint.mk' r hr).1 ≤ (ProjPoint.mk' p hp).1 ⊔ (ProjPoint.mk' q hq).1 ↔
      ∃ s t : ℝ, s • p + t • q = r := by
  change Submodule.span ℝ {r} ≤ Submodule.span ℝ {p} ⊔ Submodule.span ℝ {q} ↔ _
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨s, t, rfl⟩
  · rintro ⟨s, t, rfl⟩
    exact ⟨s • p, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), t • q,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩

/-- Two points on two lines that are not the same line coincide. -/
theorem eq_of_collinear_of_collinear {B C B' C' X X' : ProjPoint} (hBC : B ≠ C) (hB'C' : B' ≠ C')
    (hl : ¬ ∃ ℓ : ProjLine, B.LiesOn ℓ ∧ C.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C'.LiesOn ℓ)
    (h1 : ProjCollinear B C X) (h2 : ProjCollinear B' C' X) (h1' : ProjCollinear B C X')
    (h2' : ProjCollinear B' C' X') : X = X' := by
  by_contra hne
  rw [projCollinear_iff_liesOn_join hBC] at h1 h1'
  rw [projCollinear_iff_liesOn_join hB'C'] at h2 h2'
  have e1 := ProjPoint.eq_join_of hne h1 h1'
  have e2 := ProjPoint.eq_join_of hne h2 h2'
  apply hl
  refine ⟨B.join C hBC, B.left_liesOn_join hBC, ProjPoint.right_liesOn_join hBC, ?_, ?_⟩
  · rw [e1, ← e2]; exact B'.left_liesOn_join hB'C'
  · rw [e1, ← e2]; exact ProjPoint.right_liesOn_join hB'C'

end Foundations

/-! ## Desargues' theorem and its dual (Theorems 15.5 and 15.14) -/

section Desargues

theorem mk'_eq_of_smul_eq {b c : Space3} (hb : b ≠ 0) (hc : c ≠ 0) {s s' : ℝ} (_hs : s ≠ 0)
    (hs' : s' ≠ 0) (h : s • b = s' • c) : ProjPoint.mk' b hb = ProjPoint.mk' c hc := by
  rw [ProjPoint.mk'_eq_iff]
  refine ⟨s' ⁻¹ * s, ?_⟩
  rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hs', one_smul]

theorem proj_desargues_side {X : ProjPoint} {b c b' c' o : Space3} {hb : b ≠ 0} {hc : c ≠ 0}
    {hb' : b' ≠ 0} {hc' : c' ≠ 0} (ho : o ≠ 0) {sB tB sC tC : ℝ}
    (hBC : ProjPoint.mk' b hb ≠ ProjPoint.mk' c hc) (hB'C' : ProjPoint.mk' b' hb' ≠ ProjPoint.mk' c' hc')
    (hl : ¬ ∃ ℓ : ProjLine, (ProjPoint.mk' b hb).LiesOn ℓ ∧ (ProjPoint.mk' c hc).LiesOn ℓ ∧
      (ProjPoint.mk' b' hb').LiesOn ℓ ∧ (ProjPoint.mk' c' hc').LiesOn ℓ)
    (hoB : sB • b + tB • b' = o) (hoC : sC • c + tC • c' = o)
    (hX1 : ProjCollinear (ProjPoint.mk' b hb) (ProjPoint.mk' c hc) X)
    (hX2 : ProjCollinear (ProjPoint.mk' b' hb') (ProjPoint.mk' c' hc') X) :
    ∃ hx : sB • b - sC • c ≠ 0, X = ProjPoint.mk' (sB • b - sC • c) hx := by
  have hx : sB • b - sC • c ≠ 0 := by
    intro h
    have h1 : sB • b = sC • c := sub_eq_zero.mp h
    by_cases hsB : sB = 0
    · have hsC : sC = 0 := by
        rw [hsB, zero_smul] at h1
        exact (smul_eq_zero.mp h1.symm).resolve_right hc
      subst hsB hsC
      simp only [zero_smul, zero_add] at hoB hoC
      have htB : tB ≠ 0 := by rintro rfl; apply ho; rw [← hoB]; simp
      have htC : tC ≠ 0 := by rintro rfl; apply ho; rw [← hoC]; simp
      exact hB'C' (mk'_eq_of_smul_eq hb' hc' htB htC (hoB.trans hoC.symm))
    · have hsC : sC ≠ 0 := by
        rintro rfl
        rw [zero_smul] at h1
        exact hb ((smul_eq_zero.mp h1).resolve_left hsB)
      exact hBC (mk'_eq_of_smul_eq hb hc hsB hsC h1)
  refine ⟨hx, eq_of_collinear_of_collinear hBC hB'C' hl hX1 hX2 ?_ ?_⟩
  · rw [projCollinear_iff_liesOn_join hBC]
    exact (mem_sup_mk' hb hc hx).2 ⟨sB, -sC, by module⟩
  · rw [projCollinear_iff_liesOn_join hB'C']
    exact (mem_sup_mk' hb' hc' hx).2 ⟨-tB, tC, by linear_combination (norm := module) hoC - hoB⟩

/-- **Desargues' theorem, space model** (Petrunin, Theorem 15.5, p. 125): if the lines `AA'`, `BB'`, `CC'`
of the projective plane meet in `O`, then the intersection points `X = BC ∩ B'C'`, `Y = CA ∩ C'A'`,
`Z = AB ∩ A'B'` are collinear.  Hypotheses: the six points are such that the lines named exist
(`A ≠ B` etc.) and the pairs of lines `BC, B'C'`, ... are distinct (so that `X, Y, Z` are well defined).
The book's nondegenerate triangles are a special case.  Proved by linear algebra in `ℝ³`. -/
@[kb "petrunin2025" "Theorem 15.5, p. 125"]
theorem desargues_forward {A B C A' B' C' O X Y Z : ProjPoint}
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hC'A' : C' ≠ A')
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hOA : ProjCollinear A A' O) (hOB : ProjCollinear B B' O) (hOC : ProjCollinear C C' O)
    (hX : ProjCollinear B C X ∧ ProjCollinear B' C' X)
    (hY : ProjCollinear C A Y ∧ ProjCollinear C' A' Y)
    (hZ : ProjCollinear A B Z ∧ ProjCollinear A' B' Z)
    (hlX : ¬ ∃ ℓ : ProjLine, B.LiesOn ℓ ∧ C.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C'.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : ProjLine, C.LiesOn ℓ ∧ A.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A'.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : ProjLine, A.LiesOn ℓ ∧ B.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B'.LiesOn ℓ) :
    ProjCollinear X Y Z := by
  obtain ⟨a, ha, rfl⟩ := A.exists_rep
  obtain ⟨b, hb, rfl⟩ := B.exists_rep
  obtain ⟨c, hc, rfl⟩ := C.exists_rep
  obtain ⟨a', ha', rfl⟩ := A'.exists_rep
  obtain ⟨b', hb', rfl⟩ := B'.exists_rep
  obtain ⟨c', hc', rfl⟩ := C'.exists_rep
  obtain ⟨o, ho, rfl⟩ := O.exists_rep
  rw [projCollinear_iff_liesOn_join hAA'] at hOA
  rw [projCollinear_iff_liesOn_join hBB'] at hOB
  rw [projCollinear_iff_liesOn_join hCC'] at hOC
  obtain ⟨sA, tA, hA⟩ := (mem_sup_mk' ha ha' ho).1 hOA
  obtain ⟨sB, tB, hB⟩ := (mem_sup_mk' hb hb' ho).1 hOB
  obtain ⟨sC, tC, hC⟩ := (mem_sup_mk' hc hc' ho).1 hOC
  obtain ⟨hx, rfl⟩ := proj_desargues_side ho hBC hB'C' hlX hB hC hX.1 hX.2
  obtain ⟨hy, rfl⟩ := proj_desargues_side ho hCA hC'A' hlY hC hA hY.1 hY.2
  obtain ⟨hz, rfl⟩ := proj_desargues_side ho hAB hA'B' hlZ hA hB hZ.1 hZ.2
  rw [projCollinear_mk'_iff]
  have hz' : sA • a - sB • b = -((sB • b - sC • c) + (sC • c - sA • a)) := by module
  rw [hz']
  unfold det3
  simp only [PiLp.neg_apply, PiLp.add_apply]
  ring

theorem dual_liesOn (m ℓ : ProjLine) :
    (projDuality.symm m).LiesOn ℓ ↔ (projDuality.symm ℓ).LiesOn m := by
  rw [projDuality_liesOn_iff, Equiv.apply_symm_apply]

theorem projCollinear_ne {A B C : ProjPoint} (h : ¬ ProjCollinear A B C) :
    A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  obtain ⟨a, ha, rfl⟩ := A.exists_rep
  obtain ⟨b, hb, rfl⟩ := B.exists_rep
  obtain ⟨c, hc, rfl⟩ := C.exists_rep
  rw [projCollinear_mk'_iff] at h
  refine ⟨?_, ?_, ?_⟩
  · intro e
    obtain ⟨t, rfl⟩ := (ProjPoint.mk'_eq_iff ha hb).1 e
    apply h; unfold det3; simp; ring
  · intro e
    obtain ⟨t, rfl⟩ := (ProjPoint.mk'_eq_iff hb hc).1 e
    apply h; unfold det3; simp; ring
  · intro e
    obtain ⟨t, rfl⟩ := (ProjPoint.mk'_eq_iff hc ha).1 e
    apply h; unfold det3; simp; ring

theorem join_tri_ne {A B C : ProjPoint} (h : ¬ ProjCollinear A B C) (hAB : A ≠ B) (hBC : B ≠ C)
    (hCA : C ≠ A) :
    B.join C hBC ≠ C.join A hCA ∧ C.join A hCA ≠ A.join B hAB ∧ A.join B hAB ≠ B.join C hBC := by
  refine ⟨fun e => h ⟨C.join A hCA, ProjPoint.right_liesOn_join hCA, ?_, C.left_liesOn_join hCA⟩,
    fun e => h ⟨A.join B hAB, A.left_liesOn_join hAB, ProjPoint.right_liesOn_join hAB, ?_⟩,
    fun e => h ⟨B.join C hBC, ?_, B.left_liesOn_join hBC, ProjPoint.right_liesOn_join hBC⟩⟩
  · rw [← e]; exact B.left_liesOn_join hBC
  · rw [← e]; exact C.left_liesOn_join hCA
  · rw [← e]; exact A.left_liesOn_join hAB

theorem eq_of_liesOn_two {ℓ m : ProjLine} (h : ℓ ≠ m) {P Q : ProjPoint} (hP1 : P.LiesOn ℓ)
    (hP2 : P.LiesOn m) (hQ1 : Q.LiesOn ℓ) (hQ2 : Q.LiesOn m) : P = Q := by
  obtain ⟨R, _, hu⟩ := existsUnique_point_on h
  exact (hu P ⟨hP1, hP2⟩).trans (hu Q ⟨hQ1, hQ2⟩).symm

/-- **Dual Desargues theorem** (Petrunin, Theorem 15.14, p. 129): if two triangles `ABC`, `A'B'C'` of the
projective plane (nondegenerate, with `A ≠ A'`, ...) have `X = BC ∩ B'C'`, `Y = CA ∩ C'A'`,
`Z = AB ∩ A'B'` collinear, then the lines `AA'`, `BB'`, `CC'` are concurrent.  As in the book it is deduced
from the theorem `desargues_forward` by the duality `projDuality` of Theorem 15.12: it is applied to the
poles of the sides. -/
@[kb "petrunin2025" "Theorem 15.14, p. 129"]
theorem desargues_converse {A B C A' B' C' X Y Z : ProjPoint}
    (hABC : ¬ ProjCollinear A B C) (hA'B'C' : ¬ ProjCollinear A' B' C')
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hX : ProjCollinear B C X ∧ ProjCollinear B' C' X)
    (hY : ProjCollinear C A Y ∧ ProjCollinear C' A' Y)
    (hZ : ProjCollinear A B Z ∧ ProjCollinear A' B' Z)
    (hlX : ¬ ∃ ℓ : ProjLine, B.LiesOn ℓ ∧ C.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C'.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : ProjLine, C.LiesOn ℓ ∧ A.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A'.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : ProjLine, A.LiesOn ℓ ∧ B.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B'.LiesOn ℓ)
    (hXYZ : ProjCollinear X Y Z) :
    ∃ O : ProjPoint, ProjCollinear A A' O ∧ ProjCollinear B B' O ∧ ProjCollinear C C' O := by
  obtain ⟨hAB, hBC, hCA⟩ := projCollinear_ne hABC
  obtain ⟨hA'B', hB'C', hC'A'⟩ := projCollinear_ne hA'B'C'
  obtain ⟨n1, n2, n3⟩ := join_tri_ne hABC hAB hBC hCA
  obtain ⟨n1', n2', n3'⟩ := join_tri_ne hA'B'C' hA'B' hB'C' hC'A'
  obtain ⟨L, hXL, hYL, hZL⟩ := hXYZ
  have hX1 := (projCollinear_iff_liesOn_join hBC).1 hX.1
  have hX2 := (projCollinear_iff_liesOn_join hB'C').1 hX.2
  have hY1 := (projCollinear_iff_liesOn_join hCA).1 hY.1
  have hY2 := (projCollinear_iff_liesOn_join hC'A').1 hY.2
  have hZ1 := (projCollinear_iff_liesOn_join hAB).1 hZ.1
  have hZ2 := (projCollinear_iff_liesOn_join hA'B').1 hZ.2
  have d := projDuality_liesOn_iff
  have H : ProjCollinear (projDuality.symm (A.join A' hAA')) (projDuality.symm (B.join B' hBB'))
      (projDuality.symm (C.join C' hCC')) := by
    refine desargues_forward (A := projDuality.symm (B.join C hBC))
      (B := projDuality.symm (C.join A hCA)) (C := projDuality.symm (A.join B hAB))
      (A' := projDuality.symm (B'.join C' hB'C')) (B' := projDuality.symm (C'.join A' hC'A'))
      (C' := projDuality.symm (A'.join B' hA'B')) (O := projDuality.symm L) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun e => n1 (projDuality.symm.injective e)
    · exact fun e => n2 (projDuality.symm.injective e)
    · exact fun e => n3 (projDuality.symm.injective e)
    · exact fun e => n1' (projDuality.symm.injective e)
    · exact fun e => n2' (projDuality.symm.injective e)
    · exact fun e => n3' (projDuality.symm.injective e)
    · intro e
      have e' := projDuality.symm.injective e
      exact hlX ⟨_, B.left_liesOn_join hBC, ProjPoint.right_liesOn_join hBC,
        by rw [e']; exact B'.left_liesOn_join hB'C', by rw [e']; exact ProjPoint.right_liesOn_join hB'C'⟩
    · intro e
      have e' := projDuality.symm.injective e
      exact hlY ⟨_, C.left_liesOn_join hCA, ProjPoint.right_liesOn_join hCA,
        by rw [e']; exact C'.left_liesOn_join hC'A', by rw [e']; exact ProjPoint.right_liesOn_join hC'A'⟩
    · intro e
      have e' := projDuality.symm.injective e
      exact hlZ ⟨_, A.left_liesOn_join hAB, ProjPoint.right_liesOn_join hAB,
        by rw [e']; exact A'.left_liesOn_join hA'B', by rw [e']; exact ProjPoint.right_liesOn_join hA'B'⟩
    · exact ⟨projDuality X, (d X _).1 hX1, (d X _).1 hX2, (d X L).1 hXL⟩
    · exact ⟨projDuality Y, (d Y _).1 hY1, (d Y _).1 hY2, (d Y L).1 hYL⟩
    · exact ⟨projDuality Z, (d Z _).1 hZ1, (d Z _).1 hZ2, (d Z L).1 hZL⟩
    · exact ⟨⟨projDuality A, (d A _).1 (ProjPoint.right_liesOn_join hCA), (d A _).1 (A.left_liesOn_join hAB),
        (d A _).1 (A.left_liesOn_join hAA')⟩,
        ⟨projDuality A', (d A' _).1 (ProjPoint.right_liesOn_join hC'A'), (d A' _).1 (A'.left_liesOn_join hA'B'),
        (d A' _).1 (ProjPoint.right_liesOn_join hAA')⟩⟩
    · exact ⟨⟨projDuality B, (d B _).1 (ProjPoint.right_liesOn_join hAB), (d B _).1 (B.left_liesOn_join hBC),
        (d B _).1 (B.left_liesOn_join hBB')⟩,
        ⟨projDuality B', (d B' _).1 (ProjPoint.right_liesOn_join hA'B'), (d B' _).1 (B'.left_liesOn_join hB'C'),
        (d B' _).1 (ProjPoint.right_liesOn_join hBB')⟩⟩
    · exact ⟨⟨projDuality C, (d C _).1 (ProjPoint.right_liesOn_join hBC), (d C _).1 (C.left_liesOn_join hCA),
        (d C _).1 (C.left_liesOn_join hCC')⟩,
        ⟨projDuality C', (d C' _).1 (ProjPoint.right_liesOn_join hB'C'), (d C' _).1 (C'.left_liesOn_join hC'A'),
        (d C' _).1 (ProjPoint.right_liesOn_join hCC')⟩⟩
    · rintro ⟨L', h1, h2, h3, h4⟩
      rw [dual_liesOn] at h1 h2 h3 h4
      exact hAA' ((eq_of_liesOn_two n2 h1 h2 (ProjPoint.right_liesOn_join hCA) (A.left_liesOn_join hAB)).symm.trans
        (eq_of_liesOn_two n2' h3 h4 (ProjPoint.right_liesOn_join hC'A') (A'.left_liesOn_join hA'B')))
    · rintro ⟨L', h1, h2, h3, h4⟩
      rw [dual_liesOn] at h1 h2 h3 h4
      exact hBB' ((eq_of_liesOn_two n3 h1 h2 (ProjPoint.right_liesOn_join hAB) (B.left_liesOn_join hBC)).symm.trans
        (eq_of_liesOn_two n3' h3 h4 (ProjPoint.right_liesOn_join hA'B') (B'.left_liesOn_join hB'C')))
    · rintro ⟨L', h1, h2, h3, h4⟩
      rw [dual_liesOn] at h1 h2 h3 h4
      exact hCC' ((eq_of_liesOn_two n1 h1 h2 (ProjPoint.right_liesOn_join hBC) (C.left_liesOn_join hCA)).symm.trans
        (eq_of_liesOn_two n1' h3 h4 (ProjPoint.right_liesOn_join hB'C') (C'.left_liesOn_join hC'A')))
  obtain ⟨L2, h1, h2, h3⟩ := H
  rw [dual_liesOn] at h1 h2 h3
  exact ⟨projDuality.symm L2, ⟨_, A.left_liesOn_join hAA', ProjPoint.right_liesOn_join hAA', h1⟩,
    ⟨_, B.left_liesOn_join hBB', ProjPoint.right_liesOn_join hBB', h2⟩,
    ⟨_, C.left_liesOn_join hCC', ProjPoint.right_liesOn_join hCC', h3⟩⟩

/-- **Desargues' theorem with its converse** (Petrunin, Theorems 15.5 and 15.14, p. 129): for two
nondegenerate triangles `ABC`, `A'B'C'` (with `A ≠ A'`, ...) such that the pairs of corresponding sides are
distinct lines, the lines `AA'`, `BB'`, `CC'` are concurrent iff the intersection points `X, Y, Z` of
corresponding sides are collinear. -/
@[kb "petrunin2025" "Theorem 15.14 (iff), p. 129"]
theorem desargues_iff {A B C A' B' C' X Y Z : ProjPoint}
    (hABC : ¬ ProjCollinear A B C) (hA'B'C' : ¬ ProjCollinear A' B' C')
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hX : ProjCollinear B C X ∧ ProjCollinear B' C' X)
    (hY : ProjCollinear C A Y ∧ ProjCollinear C' A' Y)
    (hZ : ProjCollinear A B Z ∧ ProjCollinear A' B' Z)
    (hlX : ¬ ∃ ℓ : ProjLine, B.LiesOn ℓ ∧ C.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C'.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : ProjLine, C.LiesOn ℓ ∧ A.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A'.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : ProjLine, A.LiesOn ℓ ∧ B.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B'.LiesOn ℓ) :
    (∃ O : ProjPoint, ProjCollinear A A' O ∧ ProjCollinear B B' O ∧ ProjCollinear C C' O) ↔
      ProjCollinear X Y Z := by
  obtain ⟨hAB, hBC, hCA⟩ := projCollinear_ne hABC
  obtain ⟨hA'B', hB'C', hC'A'⟩ := projCollinear_ne hA'B'C'
  constructor
  · rintro ⟨O, h1, h2, h3⟩
    exact desargues_forward hAB hBC hCA hA'B' hB'C' hC'A' hAA' hBB' hCC' h1 h2 h3 hX hY hZ hlX hlY hlZ
  · exact desargues_converse hABC hA'B'C' hAA' hBB' hCC' hX hY hZ hlX hlY hlZ

end Desargues

/-! ## Pappus' theorem and its dual (Theorem 15.6, Exercise 15.15) -/

section Pappus

theorem exists_relation4 (a b c d : Space3) :
    ∃ p q r s : ℝ, ¬(p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0) ∧ p • a + q • b + r • c + s • d = 0 := by
  have h : ¬ LinearIndependent ℝ ![a, b, c, d] := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at h
  obtain ⟨g, hg, i, hi⟩ := h
  refine ⟨g 0, g 1, g 2, g 3, ?_, ?_⟩
  · rintro ⟨h0, h1, h2, h3⟩
    fin_cases i <;> simp_all
  · simpa [Fin.sum_univ_four] using hg

theorem indep_pair {p q : Space3} {hp : p ≠ 0} {hq : q ≠ 0}
    (hpq : ProjPoint.mk' p hp ≠ ProjPoint.mk' q hq) {s t : ℝ} (h : s • p + t • q = 0) :
    s = 0 ∧ t = 0 := by
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, zero_add] at h
    exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hq⟩
  · by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at h
      exact absurd ((smul_eq_zero.mp h).resolve_left hs) hp
    · exact absurd (mk'_eq_of_smul_eq hp hq hs (neg_ne_zero.2 ht)
        (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h)) hpq

theorem det3_zero_of_dep {x y z : Space3} {α β γ : ℝ} (h : α • x + β • y + γ • z = 0)
    (hne : ¬(α = 0 ∧ β = 0 ∧ γ = 0)) : det3 x y z = 0 := by
  by_cases hα : α = 0
  · by_cases hβ : β = 0
    · have hγ : γ ≠ 0 := fun hγ => hne ⟨hα, hβ, hγ⟩
      have h' : γ * det3 x y z = 0 := by
        have : det3 x y (α • x + β • y + γ • z) = 0 := by
          rw [h]; unfold det3; simp
        rw [← this]; unfold det3; simp; ring
      exact (mul_eq_zero.mp h').resolve_left hγ
    · have h' : β * det3 x y z = 0 := by
        have : det3 x (α • x + β • y + γ • z) z = 0 := by
          rw [h]; unfold det3; simp
        rw [← this]; unfold det3; simp; ring
      exact (mul_eq_zero.mp h').resolve_left hβ
  · have h' : α * det3 x y z = 0 := by
      have : det3 (α • x + β • y + γ • z) y z = 0 := by
        rw [h]; unfold det3; simp
      rw [← this]; unfold det3; simp; ring
    exact (mul_eq_zero.mp h').resolve_left hα

theorem eq_mk'_of_two {p q p' q' x : Space3} {hp : p ≠ 0} {hq : q ≠ 0} {hp' : p' ≠ 0} {hq' : q' ≠ 0}
    (hx : x ≠ 0) (hpq : ProjPoint.mk' p hp ≠ ProjPoint.mk' q hq)
    (hp'q' : ProjPoint.mk' p' hp' ≠ ProjPoint.mk' q' hq')
    (hl : ¬ ∃ ℓ : ProjLine, (ProjPoint.mk' p hp).LiesOn ℓ ∧ (ProjPoint.mk' q hq).LiesOn ℓ ∧
      (ProjPoint.mk' p' hp').LiesOn ℓ ∧ (ProjPoint.mk' q' hq').LiesOn ℓ)
    (h1 : ∃ s t : ℝ, s • p + t • q = x) (h2 : ∃ s t : ℝ, s • p' + t • q' = x) {X : ProjPoint}
    (hX1 : ProjCollinear (ProjPoint.mk' p hp) (ProjPoint.mk' q hq) X)
    (hX2 : ProjCollinear (ProjPoint.mk' p' hp') (ProjPoint.mk' q' hq') X) :
    X = ProjPoint.mk' x hx := by
  refine eq_of_collinear_of_collinear hpq hp'q' hl hX1 hX2 ?_ ?_
  · rw [projCollinear_iff_liesOn_join hpq]; exact (mem_sup_mk' hp hq hx).2 h1
  · rw [projCollinear_iff_liesOn_join hp'q']; exact (mem_sup_mk' hp' hq' hx).2 h2

theorem exists_normalized {A B C : ProjPoint} (hc : ProjCollinear A B C) (hAB : A ≠ B) (hBC : B ≠ C)
    (hCA : C ≠ A) : ∃ (a b : Space3) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0),
      A = ProjPoint.mk' a ha ∧ B = ProjPoint.mk' b hb ∧ C = ProjPoint.mk' (a + b) hab := by
  obtain ⟨a0, ha0, rfl⟩ := A.exists_rep
  obtain ⟨b0, hb0, rfl⟩ := B.exists_rep
  obtain ⟨c0, hc0, rfl⟩ := C.exists_rep
  rw [projCollinear_iff_liesOn_join hAB] at hc
  obtain ⟨s, t, hst⟩ := (mem_sup_mk' ha0 hb0 hc0).1 hc
  have hs : s ≠ 0 := by
    rintro rfl
    simp only [zero_smul, zero_add] at hst
    exact hBC (mk'_eq_of_smul_eq hb0 hc0 (s := t) (s' := 1) (by rintro rfl; simp at hst; exact hc0 hst.symm)
      one_ne_zero (by rw [one_smul]; exact hst))
  have ht : t ≠ 0 := by
    rintro rfl
    simp only [zero_smul, add_zero] at hst
    exact hCA (mk'_eq_of_smul_eq hc0 ha0 (s := 1) (s' := s) one_ne_zero hs
      (by rw [one_smul]; exact hst.symm))
  have ha : s • a0 ≠ 0 := smul_ne_zero hs ha0
  have hb : t • b0 ≠ 0 := smul_ne_zero ht hb0
  have hab : s • a0 + t • b0 ≠ 0 := by rw [hst]; exact hc0
  refine ⟨s • a0, t • b0, ha, hb, hab, ?_, ?_, ?_⟩
  · exact (ProjPoint.mk'_eq_iff ha0 ha).2 ⟨s, rfl⟩
  · exact (ProjPoint.mk'_eq_iff hb0 hb).2 ⟨t, rfl⟩
  · exact (ProjPoint.mk'_eq_iff hc0 hab).2 ⟨1, by rw [one_smul]; exact hst.symm⟩

theorem pappus_core {a b a' b' : Space3} {ha : a ≠ 0} {hb : b ≠ 0} {ha' : a' ≠ 0} {hb' : b' ≠ 0}
    {hc : a + b ≠ 0} {hc' : a' + b' ≠ 0} {X Y Z : ProjPoint}
    (hAB : ProjPoint.mk' a ha ≠ ProjPoint.mk' b hb) (hA'B' : ProjPoint.mk' a' ha' ≠ ProjPoint.mk' b' hb')
    (hAB' : ProjPoint.mk' a ha ≠ ProjPoint.mk' b' hb') (hA'B : ProjPoint.mk' a' ha' ≠ ProjPoint.mk' b hb)
    (hBC' : ProjPoint.mk' b hb ≠ ProjPoint.mk' (a' + b') hc')
    (hB'C : ProjPoint.mk' b' hb' ≠ ProjPoint.mk' (a + b) hc)
    (hCA' : ProjPoint.mk' (a + b) hc ≠ ProjPoint.mk' a' ha')
    (hC'A : ProjPoint.mk' (a' + b') hc' ≠ ProjPoint.mk' a ha)
    (hX : ProjCollinear (ProjPoint.mk' b hb) (ProjPoint.mk' (a' + b') hc') X ∧
      ProjCollinear (ProjPoint.mk' b' hb') (ProjPoint.mk' (a + b) hc) X)
    (hY : ProjCollinear (ProjPoint.mk' (a + b) hc) (ProjPoint.mk' a' ha') Y ∧
      ProjCollinear (ProjPoint.mk' (a' + b') hc') (ProjPoint.mk' a ha) Y)
    (hZ : ProjCollinear (ProjPoint.mk' a ha) (ProjPoint.mk' b' hb') Z ∧
      ProjCollinear (ProjPoint.mk' a' ha') (ProjPoint.mk' b hb) Z)
    (hlX : ¬ ∃ ℓ : ProjLine, (ProjPoint.mk' b hb).LiesOn ℓ ∧ (ProjPoint.mk' (a' + b') hc').LiesOn ℓ ∧
      (ProjPoint.mk' b' hb').LiesOn ℓ ∧ (ProjPoint.mk' (a + b) hc).LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : ProjLine, (ProjPoint.mk' (a + b) hc).LiesOn ℓ ∧ (ProjPoint.mk' a' ha').LiesOn ℓ ∧
      (ProjPoint.mk' (a' + b') hc').LiesOn ℓ ∧ (ProjPoint.mk' a ha).LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : ProjLine, (ProjPoint.mk' a ha).LiesOn ℓ ∧ (ProjPoint.mk' b' hb').LiesOn ℓ ∧
      (ProjPoint.mk' a' ha').LiesOn ℓ ∧ (ProjPoint.mk' b hb).LiesOn ℓ) :
    ProjCollinear X Y Z := by
  obtain ⟨p, q, r, s, hnz, hpq⟩ := exists_relation4 a b a' b'
  have hxne : (q - p) • b + r • (a' + b') ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep_pair hBC' h0
    have hq : q = p := by linarith
    rw [hq, h2] at hpq
    have h3 : p • (a + b) + s • b' = 0 := by linear_combination (norm := module) hpq
    obtain ⟨h4, h5⟩ := indep_pair hB'C.symm h3
    exact hnz ⟨h4, by rw [hq, h4], h2, h5⟩
  have hyne : q • (a + b) + (r - s) • a' ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep_pair hCA' h0
    have hrs : r = s := by linarith
    rw [h1, hrs] at hpq
    have h3 : p • a + s • (a' + b') = 0 := by linear_combination (norm := module) hpq
    obtain ⟨h4, h5⟩ := indep_pair hC'A.symm h3
    exact hnz ⟨h4, h1, by rw [hrs, h5], h5⟩
  have hzne : p • a + s • b' ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep_pair hAB' h0
    rw [h1, h2] at hpq
    have h3 : q • b + r • a' = 0 := by linear_combination (norm := module) hpq
    obtain ⟨h4, h5⟩ := indep_pair hA'B.symm h3
    exact hnz ⟨h1, h4, h5, h2⟩
  have hxe := eq_mk'_of_two hxne hBC' hB'C hlX ⟨q - p, r, rfl⟩
    ⟨r - s, -p, by linear_combination (norm := module) (-1 : ℝ) • hpq⟩ hX.1 hX.2
  have hye := eq_mk'_of_two hyne hCA' hC'A hlY ⟨q, r - s, rfl⟩
    ⟨-s, q - p, by linear_combination (norm := module) (-1 : ℝ) • hpq⟩ hY.1 hY.2
  have hze := eq_mk'_of_two hzne hAB' hA'B hlZ ⟨p, s, rfl⟩
    ⟨-r, -q, by linear_combination (norm := module) (-1 : ℝ) • hpq⟩ hZ.1 hZ.2
  rw [hxe, hye, hze, projCollinear_mk'_iff]
  have hdep : (s * q) • ((q - p) • b + r • (a' + b')) + (p * r) • (q • (a + b) + (r - s) • a') +
      (s * q - s * p + p * r - q * r) • (p • a + s • b') = 0 := by
    linear_combination (norm := module) (s * q - s * p + p * r) • hpq
  by_cases hall : s * q = 0 ∧ p * r = 0 ∧ s * q - s * p + p * r - q * r = 0
  · exfalso
    obtain ⟨hα, hβ, -⟩ := hall
    rcases mul_eq_zero.1 hα with hs | hq0 <;> rcases mul_eq_zero.1 hβ with hp0 | hr0
    · rw [hs, hp0] at hpq
      obtain ⟨h4, h5⟩ := indep_pair hA'B.symm (show q • b + r • a' = 0 by
        linear_combination (norm := module) hpq)
      exact hnz ⟨hp0, h4, h5, hs⟩
    · rw [hs, hr0] at hpq
      obtain ⟨h4, h5⟩ := indep_pair hAB (show p • a + q • b = 0 by
        linear_combination (norm := module) hpq)
      exact hnz ⟨h4, h5, hr0, hs⟩
    · rw [hq0, hp0] at hpq
      obtain ⟨h4, h5⟩ := indep_pair hA'B' (show r • a' + s • b' = 0 by
        linear_combination (norm := module) hpq)
      exact hnz ⟨hp0, hq0, h4, h5⟩
    · rw [hq0, hr0] at hpq
      obtain ⟨h4, h5⟩ := indep_pair hAB' (show p • a + s • b' = 0 by
        linear_combination (norm := module) hpq)
      exact hnz ⟨h4, hq0, hr0, h5⟩
  · exact det3_zero_of_dep hdep hall

/-- **Pappus' theorem, space model** (Petrunin, Theorem 15.6, p. 126): if `A, B, C` are collinear and
`A', B', C'` are collinear in the projective plane, then the points `X = BC' ∩ B'C`, `Y = CA' ∩ C'A`,
`Z = AB' ∩ A'B` are collinear.  Generalization: the book's hypotheses are replaced by the explicit
nondegeneracy conditions (the named lines exist and the pairs of lines are distinct). -/
@[kb "petrunin2025" "Theorem 15.6, p. 126"]
theorem pappus_proj {A B C A' B' C' X Y Z : ProjPoint}
    (hABC : ProjCollinear A B C) (hA'B'C' : ProjCollinear A' B' C')
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hC'A' : C' ≠ A')
    (hAB' : A ≠ B') (hA'B : A' ≠ B) (hBC' : B ≠ C') (hB'C : B' ≠ C) (hCA' : C ≠ A') (hC'A : C' ≠ A)
    (hX : ProjCollinear B C' X ∧ ProjCollinear B' C X)
    (hY : ProjCollinear C A' Y ∧ ProjCollinear C' A Y)
    (hZ : ProjCollinear A B' Z ∧ ProjCollinear A' B Z)
    (hlX : ¬ ∃ ℓ : ProjLine, B.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : ProjLine, C.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : ProjLine, A.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B.LiesOn ℓ) :
    ProjCollinear X Y Z := by
  obtain ⟨a, b, ha, hb, hab, rfl, rfl, rfl⟩ := exists_normalized hABC hAB hBC hCA
  obtain ⟨a', b', ha', hb', hab', rfl, rfl, rfl⟩ := exists_normalized hA'B'C' hA'B' hB'C' hC'A'
  exact pappus_core hAB hA'B' hAB' hA'B hBC' hB'C hCA' hC'A hX hY hZ hlX hlY hlZ

/-- Three lines of the projective plane are concurrent: they pass through a common point (the dual of
`ProjCollinear`). -/
def ProjConcurrent (a b c : ProjLine) : Prop :=
  ∃ P : ProjPoint, P.LiesOn a ∧ P.LiesOn b ∧ P.LiesOn c

theorem projCollinear_dual_iff (a b c : ProjLine) :
    ProjCollinear (projDuality.symm a) (projDuality.symm b) (projDuality.symm c) ↔
      ProjConcurrent a b c := by
  constructor
  · rintro ⟨ℓ, h1, h2, h3⟩
    rw [dual_liesOn] at h1 h2 h3
    exact ⟨_, h1, h2, h3⟩
  · rintro ⟨P, h1, h2, h3⟩
    exact ⟨projDuality P, (projDuality_liesOn_iff P a).1 h1, (projDuality_liesOn_iff P b).1 h2,
      (projDuality_liesOn_iff P c).1 h3⟩

theorem exists4_dual_iff (a b c d : ProjLine) :
    (∃ ℓ : ProjLine, (projDuality.symm a).LiesOn ℓ ∧ (projDuality.symm b).LiesOn ℓ ∧
      (projDuality.symm c).LiesOn ℓ ∧ (projDuality.symm d).LiesOn ℓ) ↔
      ∃ P : ProjPoint, P.LiesOn a ∧ P.LiesOn b ∧ P.LiesOn c ∧ P.LiesOn d := by
  constructor
  · rintro ⟨ℓ, h1, h2, h3, h4⟩
    rw [dual_liesOn] at h1 h2 h3 h4
    exact ⟨_, h1, h2, h3, h4⟩
  · rintro ⟨P, h1, h2, h3, h4⟩
    exact ⟨projDuality P, (projDuality_liesOn_iff P a).1 h1, (projDuality_liesOn_iff P b).1 h2,
      (projDuality_liesOn_iff P c).1 h3, (projDuality_liesOn_iff P d).1 h4⟩

/-- **Dual Pappus theorem** (Petrunin, Exercise 15.15, p. 129): if the lines `a, b, c` are concurrent and the
lines `a', b', c'` are concurrent, and `x`, `y`, `z` are lines through the points `b ∩ c'` and `b' ∩ c`,
`c ∩ a'` and `c' ∩ a`, `a ∩ b'` and `a' ∩ b` respectively (the pairs of lines being distinct), then `x, y, z`
are concurrent.  Deduced from `pappus_proj` by the duality `projDuality`. -/
@[kb "petrunin2025" "Exercise 15.15, p. 129"]
theorem pappus_dual {a b c a' b' c' x y z : ProjLine}
    (habc : ProjConcurrent a b c) (ha'b'c' : ProjConcurrent a' b' c')
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (ha'b' : a' ≠ b') (hb'c' : b' ≠ c') (hc'a' : c' ≠ a')
    (hab' : a ≠ b') (ha'b : a' ≠ b) (hbc' : b ≠ c') (hb'c : b' ≠ c) (hca' : c ≠ a') (hc'a : c' ≠ a)
    (hx : ProjConcurrent b c' x ∧ ProjConcurrent b' c x)
    (hy : ProjConcurrent c a' y ∧ ProjConcurrent c' a y)
    (hz : ProjConcurrent a b' z ∧ ProjConcurrent a' b z)
    (hlx : ¬ ∃ P : ProjPoint, P.LiesOn b ∧ P.LiesOn c' ∧ P.LiesOn b' ∧ P.LiesOn c)
    (hly : ¬ ∃ P : ProjPoint, P.LiesOn c ∧ P.LiesOn a' ∧ P.LiesOn c' ∧ P.LiesOn a)
    (hlz : ¬ ∃ P : ProjPoint, P.LiesOn a ∧ P.LiesOn b' ∧ P.LiesOn a' ∧ P.LiesOn b) :
    ProjConcurrent x y z := by
  have inj := fun {u v : ProjLine} (h : u ≠ v) (e : projDuality.symm u = projDuality.symm v) =>
    h (projDuality.symm.injective e)
  rw [← projCollinear_dual_iff]
  rw [← projCollinear_dual_iff] at habc ha'b'c'
  rw [← exists4_dual_iff] at hlx hly hlz
  simp only [← projCollinear_dual_iff] at hx hy hz
  exact pappus_proj habc ha'b'c' (inj hab) (inj hbc) (inj hca) (inj ha'b') (inj hb'c') (inj hc'a')
    (inj hab') (inj ha'b) (inj hbc') (inj hb'c) (inj hca') (inj hc'a) hx hy hz hlx hly hlz

end Pappus

/-! ## Pencils of lines in the Euclidean plane (Section 15A) -/

section Pencils

/-- The line `a x + b y + c = 0` of the plane `ℝ × ℝ`, as a set of points. -/
def lineSet (a b c : ℝ) : Set (ℝ × ℝ) := {p | a * p.1 + b * p.2 + c = 0}

/-- A line of the Euclidean plane `ℝ × ℝ`: the solution set of `a x + b y + c = 0` with `(a, b) ≠ 0`. -/
def AffLine : Type := {L : Set (ℝ × ℝ) // ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ L = lineSet a b c}

/-- The line `a x + b y + c = 0`. -/
def AffLine.mk' (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : AffLine := ⟨lineSet a b c, a, b, c, h, rfl⟩

theorem AffLine.exists_rep (L : AffLine) : ∃ (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0), L = AffLine.mk' a b c h := by
  obtain ⟨a, b, c, h, hL⟩ := L.2
  exact ⟨a, b, c, h, Subtype.ext hL⟩

theorem AffLine.mem_mk' {a b c : ℝ} (h : a ≠ 0 ∨ b ≠ 0) (p : ℝ × ℝ) :
    p ∈ (AffLine.mk' a b c h).1 ↔ a * p.1 + b * p.2 + c = 0 := Iff.rfl

/-- Two lines of the plane are parallel if they coincide or do not meet. -/
def AffLine.Parallel (L M : AffLine) : Prop := L = M ∨ Disjoint L.1 M.1

theorem inter_point {a1 b1 c1 a2 b2 c2 : ℝ} (hd : a1 * b2 - a2 * b1 ≠ 0) :
    a1 * ((b1 * c2 - b2 * c1) / (a1 * b2 - a2 * b1)) + b1 * ((a2 * c1 - a1 * c2) / (a1 * b2 - a2 * b1)) + c1 = 0 ∧
    a2 * ((b1 * c2 - b2 * c1) / (a1 * b2 - a2 * b1)) + b2 * ((a2 * c1 - a1 * c2) / (a1 * b2 - a2 * b1)) + c2 = 0 := by
  obtain ⟨D, hD⟩ : ∃ D, D = a1 * b2 - a2 * b1 := ⟨_, rfl⟩
  rw [← hD] at hd ⊢
  constructor <;> (field_simp; rw [hD]; ring)

theorem exists_mem_lineSet {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) (c : ℝ) : ∃ p, p ∈ lineSet a b c := by
  rcases h with h | h
  · exact ⟨(-c / a, 0), by show a * (-c / a) + b * 0 + c = 0; field_simp; ring⟩
  · exact ⟨(0, -c / b), by show a * 0 + b * (-c / b) + c = 0; field_simp; ring⟩

/-- **Criterion for parallelism** of the lines `a₁ x + b₁ y + c₁ = 0` and `a₂ x + b₂ y + c₂ = 0`:
`a₁ b₂ = a₂ b₁`. -/
theorem AffLine.parallel_iff {a1 b1 c1 a2 b2 c2 : ℝ} (h1 : a1 ≠ 0 ∨ b1 ≠ 0) (h2 : a2 ≠ 0 ∨ b2 ≠ 0) :
    (AffLine.mk' a1 b1 c1 h1).Parallel (AffLine.mk' a2 b2 c2 h2) ↔ a1 * b2 = a2 * b1 := by
  constructor
  · rintro (h | h)
    · have hset : lineSet a1 b1 c1 = lineSet a2 b2 c2 := congrArg Subtype.val h
      obtain ⟨p, hp⟩ := exists_mem_lineSet h1 c1
      have hq : (p.1 - b1, p.2 + a1) ∈ lineSet a1 b1 c1 := by
        have hp' : a1 * p.1 + b1 * p.2 + c1 = 0 := hp
        show a1 * (p.1 - b1) + b1 * (p.2 + a1) + c1 = 0
        linear_combination hp'
      have hp2 : a2 * p.1 + b2 * p.2 + c2 = 0 := (hset ▸ hp : p ∈ lineSet a2 b2 c2)
      have hq2 : a2 * (p.1 - b1) + b2 * (p.2 + a1) + c2 = 0 :=
        (hset ▸ hq : (p.1 - b1, p.2 + a1) ∈ lineSet a2 b2 c2)
      linear_combination hq2 - hp2
    · by_contra hne
      have hd : a1 * b2 - a2 * b1 ≠ 0 := sub_ne_zero.2 hne
      obtain ⟨e1, e2⟩ := inter_point hd (c1 := c1) (c2 := c2)
      have hq1 : ((b1 * c2 - b2 * c1) / (a1 * b2 - a2 * b1), (a2 * c1 - a1 * c2) / (a1 * b2 - a2 * b1))
          ∈ (AffLine.mk' a1 b1 c1 h1).1 := e1
      have hq2 : ((b1 * c2 - b2 * c1) / (a1 * b2 - a2 * b1), (a2 * c1 - a1 * c2) / (a1 * b2 - a2 * b1))
          ∈ (AffLine.mk' a2 b2 c2 h2).1 := e2
      exact Set.disjoint_left.1 h hq1 hq2
  · intro h
    by_cases hex : ∃ p, p ∈ lineSet a1 b1 c1 ∧ p ∈ lineSet a2 b2 c2
    · left
      obtain ⟨p, hp1, hp2⟩ := hex
      change a1 * p.1 + b1 * p.2 + c1 = 0 at hp1
      change a2 * p.1 + b2 * p.2 + c2 = 0 at hp2
      apply Subtype.ext
      ext q
      show a1 * q.1 + b1 * q.2 + c1 = 0 ↔ a2 * q.1 + b2 * q.2 + c2 = 0
      have key : ∀ {a1 b1 c1 a2 b2 c2 : ℝ}, (a1 ≠ 0 ∨ b1 ≠ 0) → a1 * b2 = a2 * b1 →
          a1 * p.1 + b1 * p.2 + c1 = 0 → a2 * p.1 + b2 * p.2 + c2 = 0 →
          a1 * q.1 + b1 * q.2 + c1 = 0 → a2 * q.1 + b2 * q.2 + c2 = 0 := by
        intro a1 b1 c1 a2 b2 c2 h1 h hp1 hp2 hq1
        have hq' : a1 * (q.1 - p.1) + b1 * (q.2 - p.2) = 0 := by linear_combination hq1 - hp1
        have : a2 * (q.1 - p.1) + b2 * (q.2 - p.2) = 0 := by
          rcases h1 with ha | hb
          · have : a1 * (a2 * (q.1 - p.1) + b2 * (q.2 - p.2)) = 0 := by
              linear_combination a2 * hq' + (q.2 - p.2) * h
            exact (mul_eq_zero.1 this).resolve_left ha
          · have : b1 * (a2 * (q.1 - p.1) + b2 * (q.2 - p.2)) = 0 := by
              linear_combination b2 * hq' - (q.1 - p.1) * h
            exact (mul_eq_zero.1 this).resolve_left hb
        linear_combination this + hp2
      exact ⟨key h1 h hp1 hp2, key h2 h.symm hp2 hp1⟩
    · right
      rw [Set.disjoint_left]
      intro q hq1 hq2
      exact hex ⟨q, hq1, hq2⟩

theorem AffLine.parallel_equivalence : Equivalence AffLine.Parallel := by
  refine ⟨fun _ => Or.inl rfl, fun {L M} h => ?_, fun {L M N} hLM hMN => ?_⟩
  · rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · obtain ⟨a1, b1, c1, h1, rfl⟩ := L.exists_rep
    obtain ⟨a2, b2, c2, h2, rfl⟩ := M.exists_rep
    obtain ⟨a3, b3, c3, h3, rfl⟩ := N.exists_rep
    rw [AffLine.parallel_iff] at hLM hMN ⊢
    rcases h2 with ha | hb
    · have : a2 * (a1 * b3) = a2 * (a3 * b1) := by linear_combination a1 * hMN + a3 * hLM
      exact mul_left_cancel₀ ha this
    · have : b2 * (a1 * b3) = b2 * (a3 * b1) := by linear_combination b3 * hLM + b1 * hMN
      exact mul_left_cancel₀ hb this

/-- A set of lines of the plane is *concurrent* if the lines all pass through one point, or are pairwise
parallel (Petrunin, p. 121). -/
def AffLine.Concurrent (S : Set AffLine) : Prop :=
  (∃ p : ℝ × ℝ, ∀ L ∈ S, p ∈ L.1) ∨ (∀ L ∈ S, ∀ M ∈ S, L.Parallel M)

/-- A *pencil* is a maximal set of concurrent lines (Petrunin, p. 121). -/
@[kb "petrunin2025" "Definition of pencil, p. 121"]
def AffLine.IsPencil (S : Set AffLine) : Prop := Maximal AffLine.Concurrent S

/-- The central pencil with center `p`: all lines through `p`. -/
def AffLine.centralPencil (p : ℝ × ℝ) : Set AffLine := {L | p ∈ L.1}

/-- The parallel pencil of `L₀`: all lines parallel to `L₀`. -/
def AffLine.parallelPencil (L₀ : AffLine) : Set AffLine := {M | L₀.Parallel M}

theorem AffLine.concurrent_central (p : ℝ × ℝ) : AffLine.Concurrent (AffLine.centralPencil p) :=
  Or.inl ⟨p, fun _ hL => hL⟩

theorem AffLine.concurrent_parallelPencil (L₀ : AffLine) :
    AffLine.Concurrent (AffLine.parallelPencil L₀) :=
  Or.inr fun _ hM _ hN => AffLine.parallel_equivalence.trans (AffLine.parallel_equivalence.symm hM) hN

/-- The horizontal line through `p`. -/
def AffLine.hLine (p : ℝ × ℝ) : AffLine := AffLine.mk' 0 1 (-p.2) (Or.inr one_ne_zero)

/-- The vertical line through `p`. -/
def AffLine.vLine (p : ℝ × ℝ) : AffLine := AffLine.mk' 1 0 (-p.1) (Or.inl one_ne_zero)

theorem AffLine.mem_hLine {p q : ℝ × ℝ} : q ∈ (AffLine.hLine p).1 ↔ q.2 = p.2 := by
  show 0 * q.1 + 1 * q.2 + -p.2 = 0 ↔ _
  constructor <;> intro h <;> linarith

theorem AffLine.mem_vLine {p q : ℝ × ℝ} : q ∈ (AffLine.vLine p).1 ↔ q.1 = p.1 := by
  show 1 * q.1 + 0 * q.2 + -p.1 = 0 ↔ _
  constructor <;> intro h <;> linarith

theorem AffLine.not_parallel_hLine_vLine (p : ℝ × ℝ) : ¬ (AffLine.hLine p).Parallel (AffLine.vLine p) := by
  unfold AffLine.hLine AffLine.vLine
  rw [AffLine.parallel_iff]
  norm_num

/-- **A central pencil is a pencil** (Petrunin, p. 121). -/
@[kb "petrunin2025" "Central pencil, p. 121"]
theorem AffLine.isPencil_central (p : ℝ × ℝ) : AffLine.IsPencil (AffLine.centralPencil p) := by
  refine ⟨AffLine.concurrent_central p, fun y hy hle L hL => ?_⟩
  have h1 : AffLine.hLine p ∈ y := hle (show p ∈ (AffLine.hLine p).1 from AffLine.mem_hLine.2 rfl)
  have h2 : AffLine.vLine p ∈ y := hle (show p ∈ (AffLine.vLine p).1 from AffLine.mem_vLine.2 rfl)
  rcases hy with ⟨p', hp'⟩ | hpar
  · have e1 := AffLine.mem_hLine.1 (hp' _ h1)
    have e2 := AffLine.mem_vLine.1 (hp' _ h2)
    have : p' = p := Prod.ext e2 e1
    exact this ▸ hp' L hL
  · exact absurd (hpar _ h1 _ h2) (AffLine.not_parallel_hLine_vLine p)

/-- **A parallel class of lines is a pencil** (Petrunin, p. 121). -/
@[kb "petrunin2025" "Parallel pencil, p. 121"]
theorem AffLine.isPencil_parallel (L₀ : AffLine) : AffLine.IsPencil (AffLine.parallelPencil L₀) := by
  refine ⟨AffLine.concurrent_parallelPencil L₀, fun y hy hle L hL => ?_⟩
  rcases hy with ⟨p', hp'⟩ | hpar
  · exfalso
    obtain ⟨a, b, c, h, rfl⟩ := L₀.exists_rep
    have hM : AffLine.mk' a b (-(a * p'.1 + b * p'.2) + 1) h ∈ AffLine.parallelPencil (AffLine.mk' a b c h) := by
      show (AffLine.mk' a b c h).Parallel _
      rw [AffLine.parallel_iff]
    have := hp' _ (hle hM)
    change a * p'.1 + b * p'.2 + (-(a * p'.1 + b * p'.2) + 1) = 0 at this
    linarith
  · exact hpar _ (hle (AffLine.parallel_equivalence.refl L₀)) _ hL

/-- **Classification of pencils** (Petrunin, p. 121): a pencil is a central pencil or a parallel pencil. -/
@[kb "petrunin2025" "Two types of pencils, p. 121"]
theorem AffLine.isPencil_cases {S : Set AffLine} (hS : AffLine.IsPencil S) :
    (∃ p : ℝ × ℝ, S = AffLine.centralPencil p) ∨ ∃ L₀ : AffLine, S = AffLine.parallelPencil L₀ := by
  obtain ⟨hc, hmax⟩ := hS
  rcases hc with ⟨p, hp⟩ | hpar
  · left
    refine ⟨p, le_antisymm (fun L hL => hp L hL) ?_⟩
    exact hmax (AffLine.concurrent_central p) (fun L hL => hp L hL)
  · right
    by_cases hne : S.Nonempty
    · obtain ⟨L₀, hL₀⟩ := hne
      refine ⟨L₀, le_antisymm (fun M hM => hpar L₀ hL₀ M hM) ?_⟩
      exact hmax (AffLine.concurrent_parallelPencil L₀) (fun M hM => hpar L₀ hL₀ M hM)
    · exfalso
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h := hmax (AffLine.concurrent_central (0, 0)) (by rw [hne]; exact Set.empty_subset _)
      have hv : AffLine.vLine (0, 0) ∈ AffLine.centralPencil (0, 0) := AffLine.mem_vLine.2 rfl
      have := h hv
      rw [hne] at this
      exact this

theorem AffLine.eq_of_mem_inter {L M : AffLine} (hnp : ¬ L.Parallel M) {p q : ℝ × ℝ} (hpL : p ∈ L.1)
    (hpM : p ∈ M.1) (hqL : q ∈ L.1) (hqM : q ∈ M.1) : p = q := by
  obtain ⟨a1, b1, c1, h1, rfl⟩ := L.exists_rep
  obtain ⟨a2, b2, c2, h2, rfl⟩ := M.exists_rep
  rw [AffLine.parallel_iff] at hnp
  change a1 * p.1 + b1 * p.2 + c1 = 0 at hpL
  change a2 * p.1 + b2 * p.2 + c2 = 0 at hpM
  change a1 * q.1 + b1 * q.2 + c1 = 0 at hqL
  change a2 * q.1 + b2 * q.2 + c2 = 0 at hqM
  have hd : a1 * b2 - a2 * b1 ≠ 0 := sub_ne_zero.2 hnp
  have e1 : (a1 * b2 - a2 * b1) * (p.1 - q.1) = 0 := by
    linear_combination b2 * (hpL - hqL) - b1 * (hpM - hqM)
  have e2 : (a1 * b2 - a2 * b1) * (p.2 - q.2) = 0 := by
    linear_combination a1 * (hpM - hqM) - a2 * (hpL - hqL)
  exact Prod.ext (sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hd))
    (sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hd))

theorem AffLine.pencil_through_cases {S : Set AffLine} (hS : AffLine.IsPencil S) {L M : AffLine}
    (hL : L ∈ S) (hM : M ∈ S) (hLM : L ≠ M) :
    (L.Parallel M ∧ S = AffLine.parallelPencil L) ∨
      (¬ L.Parallel M ∧ ∃ p, p ∈ L.1 ∧ p ∈ M.1 ∧ S = AffLine.centralPencil p) := by
  rcases AffLine.isPencil_cases hS with ⟨p, rfl⟩ | ⟨L₀, rfl⟩
  · right
    refine ⟨?_, p, hL, hM, rfl⟩
    rintro (h | h)
    · exact hLM h
    · exact Set.disjoint_left.1 h hL hM
  · left
    have hLM' : L.Parallel M := AffLine.parallel_equivalence.trans (AffLine.parallel_equivalence.symm hL) hM
    refine ⟨hLM', Set.ext fun N => ⟨fun hN => ?_, fun hN => ?_⟩⟩
    · exact AffLine.parallel_equivalence.trans (AffLine.parallel_equivalence.symm hL) hN
    · exact AffLine.parallel_equivalence.trans hL hN

/-- **Any two (distinct) lines completely determine the pencil containing both** (Petrunin, p. 121). -/
@[kb "petrunin2025" "Pencil through two lines, p. 121"]
theorem AffLine.existsUnique_pencil {L M : AffLine} (hLM : L ≠ M) :
    ∃! S : Set AffLine, AffLine.IsPencil S ∧ L ∈ S ∧ M ∈ S := by
  by_cases hpar : L.Parallel M
  · refine ⟨AffLine.parallelPencil L, ⟨AffLine.isPencil_parallel L, AffLine.parallel_equivalence.refl L, hpar⟩, ?_⟩
    rintro S ⟨hS, hL, hM⟩
    rcases AffLine.pencil_through_cases hS hL hM hLM with ⟨_, h⟩ | ⟨hnp, -⟩
    · exact h
    · exact absurd hpar hnp
  · have hnd : ¬ Disjoint L.1 M.1 := fun h => hpar (Or.inr h)
    obtain ⟨p, hpL, hpM⟩ := Set.not_disjoint_iff.1 hnd
    refine ⟨AffLine.centralPencil p, ⟨AffLine.isPencil_central p, hpL, hpM⟩, ?_⟩
    rintro S ⟨hS, hL, hM⟩
    rcases AffLine.pencil_through_cases hS hL hM hLM with ⟨h, -⟩ | ⟨-, q, hqL, hqM, h⟩
    · exact absurd h hpar
    · rw [h, AffLine.eq_of_mem_inter hpar hqL hqM hpL hpM]

theorem AffLine.parallelPencil_eq_iff (L M : AffLine) :
    AffLine.parallelPencil L = AffLine.parallelPencil M ↔ L.Parallel M := by
  constructor
  · intro h
    have : M ∈ AffLine.parallelPencil M := AffLine.parallel_equivalence.refl M
    rw [← h] at this
    exact this
  · intro h
    ext N
    exact ⟨fun hN => AffLine.parallel_equivalence.trans (AffLine.parallel_equivalence.symm h) hN,
      fun hN => AffLine.parallel_equivalence.trans h hN⟩

end Pencils

/-! ## The projective completion (Sections 15A and 15C) -/

section Completion

/-- The ideal point of the space model given by the direction `(-b, a)` of the line `a x + b y + c = 0`:
the line thru the origin spanned by `(-b, a, 0)`. -/
noncomputable def idealOf (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : ProjPoint :=
  ProjPoint.mk' !₂[-b, a, 0] (lineVec_ne_zero (by rcases h with h | h; exacts [Or.inr h, Or.inl (neg_ne_zero.2 h)]))

theorem idealOf_eq_iff {a1 b1 a2 b2 : ℝ} (h1 : a1 ≠ 0 ∨ b1 ≠ 0) (h2 : a2 ≠ 0 ∨ b2 ≠ 0) :
    idealOf a1 b1 h1 = idealOf a2 b2 h2 ↔ a1 * b2 = a2 * b1 := by
  unfold idealOf
  rw [ProjPoint.mk'_eq_iff]
  constructor
  · rintro ⟨t, ht⟩
    have e0 := congrArg (fun v : Space3 => v 0) ht
    have e1 := congrArg (fun v : Space3 => v 1) ht
    simp at e0 e1
    linear_combination (-a1) * e0 + b1 * e1
  · intro h
    rcases h1 with ha | hb
    · refine ⟨a2 / a1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp <;> linarith
    · refine ⟨b2 / b1, ?_⟩
      ext i
      fin_cases i <;> simp <;> field_simp <;> linarith

theorem idealOf_isIdeal (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : (idealOf a b h).IsIdeal := by
  intro v hv
  obtain ⟨t, rfl⟩ := (ProjPoint.mem_mk' _).1 hv
  simp

/-- The coefficients `(a, b)` of a chosen equation of a line. -/
noncomputable def AffLine.normal (L : AffLine) : ℝ × ℝ :=
  (L.exists_rep.choose, L.exists_rep.choose_spec.choose)

theorem AffLine.normal_ne (L : AffLine) : L.normal.1 ≠ 0 ∨ L.normal.2 ≠ 0 :=
  L.exists_rep.choose_spec.choose_spec.choose_spec.choose

/-- The ideal point of the parallel pencil of a line (before passing to the quotient). -/
noncomputable def AffLine.idealPoint (L : AffLine) : ProjPoint := idealOf L.normal.1 L.normal.2 L.normal_ne

theorem AffLine.idealPoint_mk' (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (AffLine.mk' a b c h).idealPoint = idealOf a b h := by
  set L := AffLine.mk' a b c h with hL
  obtain ⟨c0, hc0⟩ : ∃ c0, L = AffLine.mk' L.normal.1 L.normal.2 c0 L.normal_ne :=
    ⟨_, L.exists_rep.choose_spec.choose_spec.choose_spec.choose_spec⟩
  have hpar : (AffLine.mk' L.normal.1 L.normal.2 c0 L.normal_ne).Parallel (AffLine.mk' a b c h) := by
    rw [← hc0]; exact Or.inl rfl
  rw [AffLine.parallel_iff] at hpar
  exact (idealOf_eq_iff _ _).2 hpar

theorem AffLine.idealPoint_eq_iff (L M : AffLine) : L.idealPoint = M.idealPoint ↔ L.Parallel M := by
  obtain ⟨a1, b1, c1, h1, rfl⟩ := L.exists_rep
  obtain ⟨a2, b2, c2, h2, rfl⟩ := M.exists_rep
  rw [AffLine.idealPoint_mk', AffLine.idealPoint_mk', idealOf_eq_iff, AffLine.parallel_iff]

/-- The setoid of parallelism on the lines of the plane. -/
def AffLine.parallelSetoid : Setoid AffLine := ⟨AffLine.Parallel, AffLine.parallel_equivalence⟩

/-- The parallel pencils of lines, i.e. the ideal points of the projective completion. -/
def ParallelClass : Type := Quotient AffLine.parallelSetoid

/-- **The projective completion** of the Euclidean plane (Petrunin, Section 15A, p. 121): the plane together
with one ideal point for each parallel class of lines. -/
@[kb "petrunin2025" "Projective completion, p. 121"]
def ProjCompletion : Type := (ℝ × ℝ) ⊕ ParallelClass

/-- The bijection of the projective completion with the points of the space model: `(x, y) ↦ ℝ·(x, y, 1)`
and the ideal point of a pencil with direction `v` to `ℝ·(v, 0)`. -/
noncomputable def ProjCompletion.toProj : ProjCompletion → ProjPoint :=
  Sum.elim (fun p => affineToProj p.1 p.2)
    (Quotient.lift (s := AffLine.parallelSetoid) AffLine.idealPoint
      (fun _ _ h => (AffLine.idealPoint_eq_iff _ _).2 h))

theorem AffLine.idealPoint_isIdeal (L : AffLine) : L.idealPoint.IsIdeal := idealOf_isIdeal _ _ _

/-- **The projective completion is in bijection with the points of the space model** (Petrunin, Section 15C,
p. 122). -/
@[kb "petrunin2025" "Space model, p. 122"]
theorem ProjCompletion.toProj_bijective : Function.Bijective ProjCompletion.toProj := by
  constructor
  · rintro (p | c) (q | d) h
    · exact congrArg Sum.inl (affineToProj_injective h)
    · exfalso
      induction d using Quotient.inductionOn with | _ M =>
      have h' : affineToProj p.1 p.2 = M.idealPoint := h
      have := (range_affineToProj (affineToProj p.1 p.2)).1 ⟨p, rfl⟩
      exact this (h' ▸ M.idealPoint_isIdeal)
    · exfalso
      induction c using Quotient.inductionOn with | _ M =>
      have h' : M.idealPoint = affineToProj q.1 q.2 := h
      have := (range_affineToProj (affineToProj q.1 q.2)).1 ⟨q, rfl⟩
      exact this (h' ▸ M.idealPoint_isIdeal)
    · induction c using Quotient.inductionOn with | _ L =>
      induction d using Quotient.inductionOn with | _ M =>
      exact congrArg Sum.inr (Quotient.sound ((AffLine.idealPoint_eq_iff L M).1 h))
  · intro P
    by_cases hP : P.IsIdeal
    · obtain ⟨v, hv, rfl⟩ := P.exists_rep
      have hv2 : v 2 = 0 := hP v (Submodule.mem_span_singleton_self _)
      have hne : v 1 ≠ 0 ∨ -v 0 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hv
        ext i
        fin_cases i
        · simpa using hcon.2
        · simpa using hcon.1
        · simpa using hv2
      refine ⟨Sum.inr (Quotient.mk _ (AffLine.mk' (v 1) (-v 0) 0 hne)), ?_⟩
      change (AffLine.mk' (v 1) (-v 0) 0 hne).idealPoint = _
      rw [AffLine.idealPoint_mk']
      unfold idealOf
      rw [ProjPoint.mk'_eq_iff]
      refine ⟨1, ?_⟩
      ext i
      fin_cases i <;> simp [hv2]
    · obtain ⟨p, hp⟩ := (range_affineToProj P).2 hP
      exact ⟨Sum.inl p, hp⟩

/-- The incidence structure of the projective completion: the completed line of an affine line `L` consists of
the points of `L` and the ideal point of its parallel pencil. -/
def AffLine.completed (L : AffLine) : Set ProjCompletion :=
  {P | Sum.elim (fun p => p ∈ L.1) (fun c => c = Quotient.mk AffLine.parallelSetoid L) P}

/-- The ideal line: all the ideal points. -/
def ProjCompletion.idealLine : Set ProjCompletion := Set.range Sum.inr

/-- The line of the space model corresponding to the ideal line: the plane `z = 0`. -/
noncomputable def idealProjLine : ProjLine :=
  lineOfNormal !₂[0, 0, 1] (by
    intro h
    have := congrArg (fun v : Space3 => v 2) h
    simp at this)

/-- **Incidence of the projective completion corresponds to incidence in the space model** (Petrunin,
Observation 15.1, p. 123): the affine line `a x + b y + c = 0` with its ideal point corresponds to the plane
orthogonal to `(a, b, c)`. -/
@[kb "petrunin2025" "Observation 15.1 (completion form), p. 123"]
theorem ProjCompletion.mem_completed_iff (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (P : ProjCompletion) :
    P ∈ (AffLine.mk' a b c h).completed ↔ (P.toProj).LiesOn (affineLineToProj a b c h) := by
  rcases P with p | cl
  · exact (affineToProj_liesOn_iff p.1 p.2 a b c h).symm
  · induction cl using Quotient.inductionOn with | _ M =>
    obtain ⟨a2, b2, c2, h2, rfl⟩ := M.exists_rep
    change Quotient.mk AffLine.parallelSetoid (AffLine.mk' a2 b2 c2 h2) =
      Quotient.mk AffLine.parallelSetoid (AffLine.mk' a b c h) ↔ _
    rw [Quotient.eq, show (AffLine.parallelSetoid.r) = AffLine.Parallel from rfl, AffLine.parallel_iff]
    change _ ↔ (ProjCompletion.toProj (Sum.inr (Quotient.mk _ (AffLine.mk' a2 b2 c2 h2)))).LiesOn
      (lineOfNormal !₂[a, b, c] (lineVec_ne_zero h))
    have : ProjCompletion.toProj (Sum.inr (Quotient.mk AffLine.parallelSetoid (AffLine.mk' a2 b2 c2 h2))) =
        idealOf a2 b2 h2 := AffLine.idealPoint_mk' a2 b2 c2 h2
    rw [this]
    unfold idealOf
    rw [mk'_liesOn_lineOfNormal]
    simp
    constructor <;> intro hh <;> linarith

/-- **The ideal line corresponds to the plane `z = 0`** (Petrunin, Section 15C, p. 123): a point of the
projective completion is an ideal point iff its line lies in the plane `z = 0`. -/
@[kb "petrunin2025" "Ideal line, p. 123"]
theorem ProjCompletion.mem_idealLine_iff (P : ProjCompletion) :
    P ∈ ProjCompletion.idealLine ↔ (P.toProj).LiesOn idealProjLine := by
  rcases P with p | cl
  · constructor
    · rintro ⟨x, hx⟩; exact absurd hx (by simp)
    · intro h
      change (affineToProj p.1 p.2).LiesOn (lineOfNormal _ _) at h
      have e : affineToProj p.1 p.2 = ProjPoint.mk' (spacePoint p.1 p.2) (spacePoint_ne_zero _ _) := rfl
      rw [e, mk'_liesOn_lineOfNormal] at h
      simp [spacePoint] at h
  · refine ⟨fun _ => ?_, fun _ => ⟨cl, rfl⟩⟩
    induction cl using Quotient.inductionOn with | _ M =>
    obtain ⟨a2, b2, c2, h2, rfl⟩ := M.exists_rep
    have : ProjCompletion.toProj (Sum.inr (Quotient.mk AffLine.parallelSetoid (AffLine.mk' a2 b2 c2 h2))) =
        idealOf a2 b2 h2 := AffLine.idealPoint_mk' a2 b2 c2 h2
    rw [this]
    unfold idealOf idealProjLine
    rw [mk'_liesOn_lineOfNormal]
    simp

end Completion

end UndergradKB.Geometry
