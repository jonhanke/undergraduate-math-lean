import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.DehnSolids

/-!
# Etingof et al., Problem 1.51 (c): Hilbert's third problem

The cube `[0, a]³` (six faces) has Dehn invariant zero; the regular tetrahedron with vertices `(1,1,1)`,
`(1,-1,-1)`, `(-1,1,-1)`, `(-1,-1,1)` (four faces) has a nonzero Dehn invariant, because its dihedral angle
`arccos (1/3)` is an irrational multiple of `π`. So the two are not scissors-congruent.
-/

namespace UndergradKB.RepresentationTheory

open Real TensorProduct MeasureTheory InnerProductGeometry

lemma polyDehn_eq_zero_of_rational (l : List Face)
    (hl : ∀ p ∈ facePairs l, ratSubspace.mkQ (dihedral p.1 p.2 / π) = 0) : polyDehn l = 0 := by
  rw [polyDehn_eq]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  rw [dehnTerm, hl p hp, tmul_zero]

lemma mkQ_dihedral_of_inner_eq_zero {h k : Face} (hk : inner ℝ h.normal k.normal = 0) :
    ratSubspace.mkQ (dihedral h k / π) = 0 := by
  rw [dihedral, (inner_eq_zero_iff_angle_eq_pi_div_two _ _).1 hk,
    show (π - π / 2) / π = ((1 / 2 : ℚ) : ℝ) by field_simp [pi_ne_zero]; push_cast; ring]
  exact mkQ_rat _

lemma list_sum_map_tmul {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ ⧸ ratSubspace) :
    (L.map fun p => f p ⊗ₜ[ℚ] c).sum = (L.map f).sum ⊗ₜ[ℚ] c := by
  induction L with
  | nil => simp
  | cons p t ih => simp [ih, add_tmul]

lemma tmul_mkQ_ne_zero {x α : ℝ} (hx : x ≠ 0) (hα : Irrational α) :
    x ⊗ₜ[ℚ] ratSubspace.mkQ α ≠ 0 := by
  intro h
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ _).1 hx)
  have := congrArg (fun t => TensorProduct.lid ℚ _ (TensorProduct.map φ LinearMap.id t)) h
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero] at this
  exact mkQ_ne_zero_of_irrational hα ((smul_eq_zero.1 this).resolve_left hφ)

lemma not_linearIndependent_self (v : Space3) : ¬ LinearIndependent ℝ ![v, v] := by
  rw [LinearIndependent.pair_iff]
  intro h
  have := h 1 (-1) (by simp)
  exact one_ne_zero this.1

lemma not_linearIndependent_neg' (v : Space3) : ¬ LinearIndependent ℝ ![-v, v] := by
  rw [LinearIndependent.pair_iff]
  intro h
  have := h 1 1 (by simp)
  exact one_ne_zero this.1

lemma not_linearIndependent_neg (v : Space3) : ¬ LinearIndependent ℝ ![v, -v] := by
  rw [LinearIndependent.pair_iff]
  intro h
  have := h 1 1 (by simp)
  exact one_ne_zero this.1

/-! ### The cube -/

/-- The unit vector `eᵢ` of `ℝ³`. -/
noncomputable def unitVec (i : Fin 3) : Space3 := EuclideanSpace.single i 1

lemma unitVec_inner (i j : Fin 3) (hij : i ≠ j) : inner ℝ (unitVec i) (unitVec j) = 0 := by
  simp [unitVec, EuclideanSpace.inner_single_left, hij.symm]

attribute [irreducible] unitVec

/-- The six faces `xᵢ ≤ a` and `-xᵢ ≤ 0` of the cube `[0, a]³`. -/
noncomputable def cubeFaces (a : ℝ) : List Face :=
  [⟨(1 : ℝ) • unitVec 0, a⟩, ⟨(1 : ℝ) • unitVec 1, a⟩, ⟨(1 : ℝ) • unitVec 2, a⟩,
    ⟨(-1 : ℝ) • unitVec 0, 0⟩, ⟨(-1 : ℝ) • unitVec 1, 0⟩, ⟨(-1 : ℝ) • unitVec 2, 0⟩]

lemma cube_pair (i j : Fin 3) {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (c d : ℝ) :
    ratSubspace.mkQ (dihedral ⟨s • unitVec i, c⟩ ⟨t • unitVec j, d⟩ / π) = 0 := by
  by_cases hij : i = j
  · subst hij
    apply mkQ_dihedral_of_not_independent
    rw [LinearIndependent.pair_iff]
    intro H
    have := H t (-s) (by simp [smul_smul, mul_comm])
    exact ht this.1
  · apply mkQ_dihedral_of_inner_eq_zero
    simp [inner_smul_left, inner_smul_right, unitVec_inner i j hij]

/-- The faces of `cubeFaces a` cut out the cube `[0, a]³`. -/
theorem cell_cubeFaces (a : ℝ) : cell (cubeFaces a) = {x | ∀ i, 0 ≤ x i ∧ x i ≤ a} := by
  ext x
  simp only [cell, cubeFaces, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Face.half, Set.mem_setOf_eq, one_smul, neg_smul, unitVec, inner_neg_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    neg_nonpos, Fin.forall_fin_succ, Fin.forall_fin_zero_pi]
  simp only [Fin.forall_iff_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
  tauto

/-- **Etingof et al., Problem 1.51 (c).** The cube has Dehn invariant zero (all its dihedral angles are `π/2`). -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem polyDehn_cube (a : ℝ) : polyDehn (cubeFaces a) = 0 := by
  apply polyDehn_eq_zero_of_rational
  rintro ⟨h, k⟩ hp
  obtain ⟨h1, h2⟩ := mem_of_mem_facePairs hp
  simp only [cubeFaces, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact cube_pair _ _ (by norm_num) (by norm_num) _ _

/-! ### The regular tetrahedron -/

/-- The outward normals of the regular tetrahedron with vertices `(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`,
`(-1,-1,1)`: minus the opposite vertex. -/
noncomputable def tetraNormal : Fin 4 → Space3
  | 0 => !₂[-1, -1, -1]
  | 1 => !₂[-1, 1, 1]
  | 2 => !₂[1, -1, 1]
  | 3 => !₂[1, 1, -1]

/-- The four faces `⟪nᵢ, x⟫ ≤ 1` of the regular tetrahedron. -/
noncomputable def tetraFaces : List Face :=
  [⟨tetraNormal 0, 1⟩, ⟨tetraNormal 1, 1⟩, ⟨tetraNormal 2, 1⟩, ⟨tetraNormal 3, 1⟩]

lemma tetraNormal_inner (i j : Fin 4) (hij : i ≠ j) : inner ℝ (tetraNormal i) (tetraNormal j) = -1 := by
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [tetraNormal, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num

lemma tetraNormal_norm (i : Fin 4) : ‖tetraNormal i‖ = √3 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  fin_cases i <;> simp [tetraNormal, Fin.sum_univ_three] <;> norm_num

lemma tetra_dihedral (i j : Fin 4) (hij : i ≠ j) :
    dihedral ⟨tetraNormal i, 1⟩ ⟨tetraNormal j, 1⟩ = arccos (1 / 3) := by
  simp only [dihedral, InnerProductGeometry.angle, tetraNormal_inner i j hij, tetraNormal_norm]
  rw [Real.mul_self_sqrt (by norm_num), show (-1 : ℝ) / 3 = -(1 / 3) by ring, arccos_neg]
  ring

/-- Points of the edge between faces 0 and 1 (the segment from `(-1,1,-1)` to `(-1,-1,1)`). -/
lemma tetra_edge01_mem (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    !₂[-1, 1 - 2 * t, -1 + 2 * t] ∈ cell tetraFaces ∩ (⟨tetraNormal 0, 1⟩ : Face).plane ∩
      (⟨tetraNormal 1, 1⟩ : Face).plane := by
  obtain ⟨h0, h1⟩ := ht
  simp only [cell, tetraFaces, Set.mem_inter_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Face.half, Face.plane, Set.mem_setOf_eq, tetraNormal, PiLp.inner_apply, Fin.sum_univ_three]
  norm_num
  and_intros <;> linarith

lemma isBounded_cell_tetraFaces : Bornology.IsBounded (cell tetraFaces) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨√27, fun x hx => ?_⟩
  simp only [cell, tetraFaces, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Face.half, Set.mem_setOf_eq, tetraNormal, PiLp.inner_apply, Fin.sum_univ_three] at hx
  simp at hx
  obtain ⟨h0, h1, h2, h3⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

lemma tetra_edge01_pos : 0 < edgeLength (cell tetraFaces) ⟨tetraNormal 0, 1⟩ ⟨tetraNormal 1, 1⟩ := by
  set u : Space3 := (√2)⁻¹ • !₂[0, -1, 1]
  have h2 : (0 : ℝ) < √2 := by positivity
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h2, EuclideanSpace.norm_eq,
      Fin.sum_univ_three]
    simp
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    exact inv_mul_cancel₀ h2.ne'
  set x₀ : Space3 := !₂[-1, 1, -1]
  have hsub : (fun t : ℝ => x₀ + t • u) '' Set.Icc 0 √2 ⊆
      cell tetraFaces ∩ (⟨tetraNormal 0, 1⟩ : Face).plane ∩ (⟨tetraNormal 1, 1⟩ : Face).plane := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have := tetra_edge01_mem (t / (2 * √2)) ⟨by positivity, by
      rw [div_le_one (by positivity)]; nlinarith⟩
    convert this using 1
    ext i
    fin_cases i <;> simp [x₀, u] <;> field_simp <;> ring_nf <;>
      simp [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring
  have hfin : μH[1] (cell tetraFaces ∩ (⟨tetraNormal 0, 1⟩ : Face).plane ∩ (⟨tetraNormal 1, 1⟩ : Face).plane)
      < ⊤ := by
    refine hausdorff_lt_top_of_subset_planes (isBounded_cell_tetraFaces.subset fun x hx => hx.1.1) ?_
      (fun x hx => ⟨hx.1.2, hx.2⟩)
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e0 := congrArg (fun v : Space3 => v 0) hst
    have e1 := congrArg (fun v : Space3 => v 1) hst
    simp [tetraNormal] at e0 e1
    constructor <;> linarith
  rw [edgeLength, ENNReal.toReal_pos_iff]
  refine ⟨?_, hfin⟩
  calc (0 : ENNReal) < ENNReal.ofReal (√2 - 0) := by simp [h2]
    _ = μH[1] ((fun t : ℝ => x₀ + t • u) '' Set.Icc 0 √2) := (hausdorff_segment x₀ u hu _ _).symm
    _ ≤ _ := measure_mono hsub

/-- **Etingof et al., Problem 1.51 (c).** The regular tetrahedron has nonzero Dehn invariant. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem polyDehn_tetrahedron_ne_zero : polyDehn tetraFaces ≠ 0 := by
  have hpairs : ∀ p ∈ facePairs tetraFaces, dehnTerm (cell tetraFaces) p.1 p.2 =
      edgeLength (cell tetraFaces) p.1 p.2 ⊗ₜ[ℚ] ratSubspace.mkQ (arccos (1 / 3) / π) := by
    intro p hp
    simp only [tetraFaces, facePairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [dehnTerm]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [tetra_dihedral _ _ (by decide)]
  rw [polyDehn_eq, List.map_congr_left hpairs, list_sum_map_tmul]
  refine tmul_mkQ_ne_zero ?_ arccos_one_third_div_pi_irrational
  apply ne_of_gt
  have hnn : ∀ p : Face × Face, 0 ≤ edgeLength (cell tetraFaces) p.1 p.2 := fun _ => ENNReal.toReal_nonneg
  simp only [tetraFaces, facePairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.sum_cons, List.sum_nil, add_zero]
  have := tetra_edge01_pos
  have h1 := hnn (⟨tetraNormal 0, 1⟩, ⟨tetraNormal 2, 1⟩)
  have h2 := hnn (⟨tetraNormal 0, 1⟩, ⟨tetraNormal 3, 1⟩)
  have h3 := hnn (⟨tetraNormal 1, 1⟩, ⟨tetraNormal 2, 1⟩)
  have h4 := hnn (⟨tetraNormal 1, 1⟩, ⟨tetraNormal 3, 1⟩)
  have h5 := hnn (⟨tetraNormal 2, 1⟩, ⟨tetraNormal 3, 1⟩)
  simp only [tetraFaces] at this h1 h2 h3 h4 h5
  linarith

/-- **Etingof et al., Problem 1.51 (c): Hilbert's third problem.** A cube and the regular tetrahedron are not
scissors-congruent (by straight cuts whose plane contains no edge of the piece cut, rigid motions and gluing). -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem not_scissorsCongruent_cube_tetrahedron (a : ℝ) :
    ¬ ScissorsCongruent [cubeFaces a] [tetraFaces] := by
  intro h
  have := totalDehn_eq_of_scissorsCongruent h
  simp only [totalDehn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, polyDehn_cube] at this
  exact polyDehn_tetrahedron_ne_zero this.symm

end UndergradKB.RepresentationTheory
