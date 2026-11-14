import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.DehnInvariant

/-!
# Etingof et al., Problem 1.51 (a): the Dehn invariant of polyhedra in space is additive under straight cuts

A convex polyhedron in `ℝ³` is recorded by a finite list of closed half-spaces `⟪n, x⟫ ≤ c` (its faces); the solid
is their intersection. For two faces with planes `P`, `Q` the solid meets `P ∩ Q` in a segment (an edge when the
normals are independent); its length is the one-dimensional Hausdorff measure, and the dihedral angle is
`π - ∠(n, n')`. The Dehn invariant is `∑ l ⊗ (β/π)` over pairs of faces, in `ℝ ⊗_ℚ (ℝ/ℚ)`, computed with the
edge-list invariant `dehnInvariant` of `DehnInvariant.lean`. Pairs whose normals are dependent contribute zero
(their angle is a rational multiple of `π`).

A straight cut by the plane of a face `m` replaces the solid by the two pieces with faces `l ++ [m]` and
`l ++ [-m]`. We prove that the invariant is additive whenever the cutting plane contains no edge of the solid
(`polyDehn_cut`); the edges lying in the cutting plane (where a dihedral angle is split) are the case left out.
-/

namespace UndergradKB.RepresentationTheory

open Real TensorProduct MeasureTheory InnerProductGeometry

/-- Euclidean space `ℝ³`. -/
abbrev Space3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A face of a polyhedron: the closed half-space `⟪normal, x⟫ ≤ offset`. -/
structure Face where
  normal : Space3
  offset : ℝ

namespace Face

/-- The closed half-space of a face. -/
def half (h : Face) : Set Space3 := {x | inner ℝ h.normal x ≤ h.offset}

/-- The plane of a face. -/
def plane (h : Face) : Set Space3 := {x | inner ℝ h.normal x = h.offset}

/-- The opposite half-space, with the same plane. -/
def neg (h : Face) : Face := ⟨-h.normal, -h.offset⟩

lemma plane_neg (h : Face) : h.neg.plane = h.plane := by
  ext x; simp [plane, neg, inner_neg_left, neg_inj]

lemma plane_subset_half (h : Face) : h.plane ⊆ h.half := fun x hx => le_of_eq hx

lemma isClosed_half (h : Face) : IsClosed h.half :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

end Face

/-- The solid cut out by a list of faces. -/
def cell (l : List Face) : Set Space3 := {x | ∀ h ∈ l, x ∈ h.half}

lemma cell_append_singleton (l : List Face) (m : Face) : cell (l ++ [m]) = cell l ∩ m.half := by
  ext x; simp [cell, or_imp, forall_and]

/-- The length of the part of `S` on the planes of two faces. -/
noncomputable def edgeLength (S : Set Space3) (h k : Face) : ℝ := (μH[1] (S ∩ h.plane ∩ k.plane)).toReal

/-- The dihedral angle between two faces. -/
noncomputable def dihedral (h k : Face) : ℝ := π - angle h.normal k.normal

/-- The pairs of faces at distinct positions of a list. -/
def facePairs : List Face → List (Face × Face)
  | [] => []
  | h :: t => t.map (fun k => (h, k)) ++ facePairs t

lemma facePairs_append_singleton (l : List Face) (m : Face) :
    (facePairs (l ++ [m])).Perm (facePairs l ++ l.map (fun h => (h, m))) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons h t ih =>
    simp only [List.cons_append, facePairs, List.map_append, List.map_cons, List.map_nil]
    refine (List.Perm.append_left _ ih).trans ?_
    simp only [List.append_assoc, List.singleton_append]
    exact List.Perm.append_left _ List.perm_middle.symm

lemma mem_of_mem_facePairs {l : List Face} {p : Face × Face} (hp : p ∈ facePairs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [facePairs] at hp
  | cons h t ih =>
    simp only [facePairs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨k, hk, rfl⟩ | hp
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hk⟩
    · exact ⟨List.mem_cons_of_mem _ (ih hp).1, List.mem_cons_of_mem _ (ih hp).2⟩

/-- The edges of the polyhedron with faces `l`: one entry (length, dihedral angle) per pair of faces. -/
noncomputable def edgeList (l : List Face) : List (ℝ × ℝ) :=
  (facePairs l).map fun p => (edgeLength (cell l) p.1 p.2, dihedral p.1 p.2)

/-- The Dehn invariant `∑ l(a) ⊗ β(a)/π` of the polyhedron with faces `l`. -/
noncomputable def polyDehn (l : List Face) : DehnSpace := dehnInvariant (edgeList l)

/-- The contribution of one pair of faces. -/
noncomputable def dehnTerm (S : Set Space3) (h k : Face) : DehnSpace :=
  edgeLength S h k ⊗ₜ[ℚ] ratSubspace.mkQ (dihedral h k / π)

lemma polyDehn_eq (l : List Face) : polyDehn l = ((facePairs l).map fun p => dehnTerm (cell l) p.1 p.2).sum := by
  simp only [polyDehn, dehnInvariant, edgeList, List.map_map]
  rfl

/-! ### Pairs with dependent normals contribute nothing -/

lemma mkQ_dihedral_of_not_independent {h k : Face} (hd : ¬ LinearIndependent ℝ ![h.normal, k.normal]) :
    ratSubspace.mkQ (dihedral h k / π) = 0 := by
  have key : angle h.normal k.normal = 0 ∨ angle h.normal k.normal = π / 2 ∨ angle h.normal k.normal = π := by
    by_cases h0 : h.normal = 0
    · right; left; rw [h0, angle_zero_left]
    · rw [LinearIndependent.pair_iff] at hd
      push Not at hd
      obtain ⟨s, t, hst, hne⟩ := hd
      have ht : t ≠ 0 := by
        rintro rfl
        simp only [zero_smul, add_zero, smul_eq_zero, h0, or_false] at hst
        exact hne hst rfl
      have hk : k.normal = (-s / t) • h.normal := by
        have e : t • k.normal = -(s • h.normal) := eq_neg_of_add_eq_zero_right hst
        calc k.normal = t⁻¹ • (t • k.normal) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-s / t) • h.normal := by rw [e, smul_neg, smul_smul, ← neg_smul]; congr 1; ring
      rcases lt_trichotomy (-s / t) 0 with hr | hr | hr
      · right; right; rw [hk, angle_smul_right_of_neg _ _ hr, angle_neg_right, angle_self h0, sub_zero]
      · right; left; rw [hk, hr, zero_smul, angle_zero_right]
      · left; rw [hk, angle_smul_right_of_pos _ _ hr, angle_self h0]
  have hpi := pi_ne_zero
  rcases key with e | e | e <;> rw [dihedral, e]
  · rw [show (π - 0) / π = ((1 : ℚ) : ℝ) by field_simp; push_cast; ring]; exact mkQ_rat _
  · rw [show (π - π / 2) / π = ((1 / 2 : ℚ) : ℝ) by field_simp; push_cast; ring]; exact mkQ_rat _
  · rw [show (π - π) / π = ((0 : ℚ) : ℝ) by simp]; exact mkQ_rat _

lemma dehnTerm_of_not_independent (S : Set Space3) {h k : Face}
    (hd : ¬ LinearIndependent ℝ ![h.normal, k.normal]) : dehnTerm S h k = 0 := by
  rw [dehnTerm, mkQ_dihedral_of_not_independent hd, tmul_zero]

/-! ### Edge lengths are finite -/

/-- The map `t ↦ x₀ + t u` along a unit vector is an isometry. -/
lemma isometry_line (x₀ u : Space3) (hu : ‖u‖ = 1) : Isometry (fun t : ℝ => x₀ + t • u) := by
  refine Isometry.of_dist_eq fun s t => ?_
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one, Real.norm_eq_abs,
    Real.dist_eq]

/-- The length of a segment on a line. -/
lemma hausdorff_segment (x₀ u : Space3) (hu : ‖u‖ = 1) (a b : ℝ) :
    μH[1] ((fun t : ℝ => x₀ + t • u) '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  rw [(isometry_line x₀ u hu).hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real,
    Real.volume_Icc]

/-- A bounded set on the intersection of two planes with independent normals has finite length. -/
lemma hausdorff_lt_top_of_subset_planes {S : Set Space3} (hS : Bornology.IsBounded S) {h k : Face}
    (hi : LinearIndependent ℝ ![h.normal, k.normal]) (hsub : S ⊆ h.plane ∩ k.plane) : μH[1] S < ⊤ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set K : Submodule ℝ Space3 := Submodule.span ℝ (Set.range ![h.normal, k.normal])
  set Ko : Submodule ℝ Space3 := Submodule.orthogonal K
  have hK : Module.finrank ℝ K = 2 := by
    rw [finrank_span_eq_card hi]; simp
  have hKo : Module.finrank ℝ Ko = 1 := by
    have := Submodule.finrank_add_finrank_orthogonal K
    rw [finrank_euclideanSpace, Fintype.card_fin, hK] at this
    have h' : Module.finrank ℝ Ko + 2 = 3 := by rw [add_comm]; exact this
    omega
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Ko) (by
    intro hb; rw [hb, finrank_bot] at hKo; exact zero_ne_one hKo)
  set u : Space3 := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  have huK : u ∈ Ko := Ko.smul_mem _ hvK
  have hspan : Ko = Submodule.span ℝ {u} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact huK
    · rw [hKo, finrank_span_singleton]; intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  obtain ⟨R, hR⟩ := hS.subset_closedBall x₀
  have hsubline : S ⊆ (fun t : ℝ => x₀ + t • u) '' Set.Icc (-R) R := by
    intro y hy
    have hmem : y - x₀ ∈ Ko := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨i, rfl⟩
        have h1 := (hsub hy).1; have h2 := (hsub hy).2; have h3 := (hsub hx₀).1; have h4 := (hsub hx₀).2
        simp only [Face.plane, Set.mem_setOf_eq] at h1 h2 h3 h4
        fin_cases i <;> simp [inner_sub_right, h1, h2, h3, h4]
      · simp
      · intro a b _ _ ha hb; rw [inner_add_left, ha, hb, add_zero]
      · intro a b _ hb; rw [inner_smul_left, hb, mul_zero]
    rw [hspan] at hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
    have hdist : |t| ≤ R := by
      have := hR hy
      rw [Metric.mem_closedBall, dist_eq_norm, ← ht, norm_smul, hu, mul_one, Real.norm_eq_abs] at this
      exact this
    exact ⟨t, abs_le.1 hdist, by show x₀ + t • u = y; rw [ht]; abel⟩
  calc μH[1] S ≤ μH[1] ((fun t : ℝ => x₀ + t • u) '' Set.Icc (-R) R) := measure_mono hsubline
    _ = ENNReal.ofReal (R - -R) := hausdorff_segment x₀ u hu _ _
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ### Additivity under a cut -/

/-- Cutting a set by a plane that meets it in a null set splits its length. -/
lemma hausdorff_cut (T : Set Space3) (m : Face) (hT : μH[1] (T ∩ m.plane) = 0) :
    μH[1] (T ∩ m.half) + μH[1] (T ∩ m.neg.half) = μH[1] T := by
  have hmeas : MeasurableSet m.half := m.isClosed_half.measurableSet
  rw [← measure_inter_add_sdiff T hmeas]
  congr 1
  apply le_antisymm
  · calc μH[1] (T ∩ m.neg.half) ≤ μH[1] ((T \ m.half) ∪ (T ∩ m.plane)) := by
          refine measure_mono fun x ⟨hxT, hx⟩ => ?_
          by_cases hxm : x ∈ m.half
          · right; refine ⟨hxT, le_antisymm hxm ?_⟩
            simp only [Face.half, Face.neg, Set.mem_setOf_eq, inner_neg_left, neg_le_neg_iff] at hx
            exact hx
          · left; exact ⟨hxT, hxm⟩
      _ ≤ μH[1] (T \ m.half) + μH[1] (T ∩ m.plane) := measure_union_le _ _
      _ = μH[1] (T \ m.half) := by rw [hT, add_zero]
  · refine measure_mono fun x ⟨hxT, hx⟩ => ⟨hxT, ?_⟩
    simp only [Face.half, Face.neg, Set.mem_setOf_eq, inner_neg_left, neg_le_neg_iff, not_le] at hx ⊢
    exact hx.le

lemma cell_inter_assoc (A H P Q : Set Space3) : A ∩ H ∩ P ∩ Q = (A ∩ P ∩ Q) ∩ H := by
  ext; simp only [Set.mem_inter_iff]; tauto

/-- The terms of a pair of old faces add up. -/
lemma dehnTerm_cut {l : List Face} (hb : Bornology.IsBounded (cell l)) (m : Face) {h k : Face}
    (hnull : LinearIndependent ℝ ![h.normal, k.normal] →
      μH[1] (cell l ∩ h.plane ∩ k.plane ∩ m.plane) = 0) :
    dehnTerm (cell (l ++ [m])) h k + dehnTerm (cell (l ++ [m.neg])) h k = dehnTerm (cell l) h k := by
  by_cases hi : LinearIndependent ℝ ![h.normal, k.normal]
  · rw [dehnTerm, dehnTerm, dehnTerm, ← add_tmul]
    congr 1
    simp only [edgeLength, cell_append_singleton]
    rw [cell_inter_assoc (cell l) m.half, cell_inter_assoc (cell l) m.neg.half]
    set T := cell l ∩ h.plane ∩ k.plane
    have hfin : μH[1] T < ⊤ :=
      hausdorff_lt_top_of_subset_planes (hb.subset fun x hx => hx.1.1) hi
        (fun x hx => ⟨hx.1.2, hx.2⟩)
    have hcut := hausdorff_cut T m (hnull hi)
    rw [← ENNReal.toReal_add (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfin).ne
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfin).ne, hcut]
  · simp only [dehnTerm_of_not_independent _ hi, add_zero]

/-- The new edges in the cutting plane appear in both pieces with supplementary angles. -/
lemma dehnTerm_new {l : List Face} (m h : Face) :
    dehnTerm (cell (l ++ [m])) h m + dehnTerm (cell (l ++ [m.neg])) h m.neg = 0 := by
  have hlen : edgeLength (cell (l ++ [m.neg])) h m.neg = edgeLength (cell (l ++ [m])) h m := by
    simp only [edgeLength, cell_append_singleton, Face.plane_neg]
    congr 2
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨⟨hA, _⟩, hh⟩, hm⟩; exact ⟨⟨⟨hA, m.plane_subset_half hm⟩, hh⟩, hm⟩
    · rintro ⟨⟨⟨hA, _⟩, hh⟩, hm⟩
      refine ⟨⟨⟨hA, ?_⟩, hh⟩, hm⟩
      rw [← Face.plane_neg] at hm; exact m.neg.plane_subset_half hm
  have hang : ratSubspace.mkQ (dihedral h m / π) + ratSubspace.mkQ (dihedral h m.neg / π) = 0 := by
    rw [← map_add, dihedral, dihedral, Face.neg, angle_neg_right,
      show (π - angle h.normal m.normal) / π + (π - (π - angle h.normal m.normal)) / π = ((1 : ℚ) : ℝ) by
        field_simp [pi_ne_zero]; push_cast; ring]
    exact mkQ_rat 1
  rw [dehnTerm, dehnTerm, hlen, ← tmul_add, hang, tmul_zero]

/-- **Etingof et al., Problem 1.51 (a).** If a bounded polyhedron `A` (faces `l`) is cut by the plane of `m`
into `B` (faces `l ++ [m]`) and `C` (faces `l ++ [-m]`), and the cutting plane contains no edge of `A` (it meets
the line of any two faces with independent normals in a null subset of `A`), then `D(A) = D(B) + D(C)`. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem polyDehn_cut {l : List Face} (hb : Bornology.IsBounded (cell l)) (m : Face)
    (hnull : ∀ h ∈ l, ∀ k ∈ l, LinearIndependent ℝ ![h.normal, k.normal] →
      μH[1] (cell l ∩ h.plane ∩ k.plane ∩ m.plane) = 0) :
    polyDehn l = polyDehn (l ++ [m]) + polyDehn (l ++ [m.neg]) := by
  have e1 : polyDehn (l ++ [m]) = ((facePairs l ++ l.map (fun h => (h, m))).map
      fun p => dehnTerm (cell (l ++ [m])) p.1 p.2).sum := by
    rw [polyDehn_eq]; exact ((facePairs_append_singleton l m).map _).sum_eq
  have e2 : polyDehn (l ++ [m.neg]) = ((facePairs l ++ l.map (fun h => (h, m.neg))).map
      fun p => dehnTerm (cell (l ++ [m.neg])) p.1 p.2).sum := by
    rw [polyDehn_eq]; exact ((facePairs_append_singleton l m.neg).map _).sum_eq
  rw [polyDehn_eq l, e1, e2, List.map_append, List.map_append, List.sum_append, List.sum_append, List.map_map, List.map_map]
  have hnew : ((l.map ((fun p : Face × Face => dehnTerm (cell (l ++ [m])) p.1 p.2) ∘ fun h => (h, m))).sum +
      (l.map ((fun p : Face × Face => dehnTerm (cell (l ++ [m.neg])) p.1 p.2) ∘ fun h => (h, m.neg))).sum) = 0 := by
    rw [← List.sum_map_add]
    simp only [Function.comp, dehnTerm_new, List.map_const', List.sum_replicate, smul_zero]
  have hold : ((facePairs l).map fun p => dehnTerm (cell (l ++ [m])) p.1 p.2).sum +
      ((facePairs l).map fun p => dehnTerm (cell (l ++ [m.neg])) p.1 p.2).sum =
      ((facePairs l).map fun p => dehnTerm (cell l) p.1 p.2).sum := by
    rw [← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    have hp' := mem_of_mem_facePairs hp
    exact dehnTerm_cut hb m (hnull p.1 hp'.1 p.2 hp'.2)
  rw [add_add_add_comm, hold, hnew, add_zero]

end UndergradKB.RepresentationTheory
