import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import UndergradKB.Geometry.Area2
import UndergradKB.Common.Attr

/-! # The Wallace-Bolyai-Gerwien theorem (Petrunin, remark after Proposition 20.10)

Two polygonal sets of equal area are equidecomposable (the converse of the easy direction
`Equidecomposable.area_eq`).  Plan: a convenient relation `Dec` (finite families with null
overlaps) is shown to be an equivalence relation; parallelograms can be sheared, trapezoids are
folded into parallelograms, parallelograms are cut into rectangles, polygonal sets are cut into
trapezoids. -/

namespace UndergradKB.Geometry

open MeasureTheory

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ### Images of polygonal sets -/

theorem volume_image_isometryEquiv (f : E2 ≃ᵢ E2) (S : Set E2) : volume (f '' S) = volume S := by
  have h := Isometry.euclideanHausdorffMeasure_image (d := 2) f.isometry S
  simpa only [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using h

theorem IsElementary.image_affine {S : Set E2} (h : IsElementary S) (g : E2 →ᵃ[ℝ] E2) :
    IsElementary (g '' S) := by
  rcases h with ⟨A, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩
  · exact Or.inl ⟨g A, Set.image_singleton⟩
  · exact Or.inr (Or.inl ⟨g A, g B, image_segment ℝ g A B⟩)
  · refine Or.inr (Or.inr ⟨g A, g B, g C, ?_⟩)
    unfold solidTriangle
    rw [AffineMap.image_convexHull]
    simp [Set.image_insert_eq]

theorem IsPolygonal.image_affine {S : Set E2} (hS : IsPolygonal S) (g : E2 →ᵃ[ℝ] E2) :
    IsPolygonal (g '' S) := by
  obtain ⟨F, hF, hFe, rfl⟩ := hS
  refine ⟨(fun T => g '' T) '' F, hF.image _, ?_, by rw [Set.image_sUnion]⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hFe T hT).image_affine g

theorem IsPolygonal.image_isometryEquiv {S : Set E2} (hS : IsPolygonal S) (f : E2 ≃ᵢ E2) :
    IsPolygonal (f '' S) := by
  have := hS.image_affine f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
  exact this

/-! ### Polygonal sets of measure zero are degenerate -/

theorem affineIndependent_of_det {A B C : E2}
    (hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) ≠ 0) :
    AffineIndependent ℝ ![A, B, C] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  rw [collinear_iff_of_mem (p₀ := A) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨r, hr⟩ := hv B (by simp)
  obtain ⟨r', hr'⟩ := hv C (by simp)
  apply hD
  have h1 := congrArg (fun x : E2 => x 0) hr
  have h2 := congrArg (fun x : E2 => x 1) hr
  have h3 := congrArg (fun x : E2 => x 0) hr'
  have h4 := congrArg (fun x : E2 => x 1) hr'
  simp at h1 h2 h3 h4
  rw [h1, h2, h3, h4]; ring

theorem IsElementary.degenerate_of_volume_eq_zero {S : Set E2} (h : IsElementary S)
    (h0 : volume S = 0) : IsDegenerateElementary S := by
  rcases h with ⟨A, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩
  · exact Or.inl ⟨A, rfl⟩
  · exact Or.inr ⟨A, B, rfl⟩
  · by_cases hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) = 0
    · obtain ⟨X, Y, hXY⟩ := solidTriangle_eq_segment_of_det hD
      exact Or.inr ⟨X, Y, hXY⟩
    · exfalso
      let t : Affine.Triangle ℝ E2 := ⟨![A, B, C], affineIndependent_of_det hD⟩
      have h1 := area_solidTriangle_eq_volume t
      have h2 : area (solidTriangle A B C) = 0 := by simp [area, h0]
      have h3 : solidTriangle (t.points 0) (t.points 1) (t.points 2) = solidTriangle A B C := rfl
      rw [h3, h2] at h1
      exact (Affine.Simplex.volume_pos t).ne h1

theorem IsPolygonal.degenerate_of_volume_eq_zero {S : Set E2} (h : IsPolygonal S)
    (h0 : volume S = 0) : IsDegeneratePolygonal S := by
  obtain ⟨F, hF, hFe, rfl⟩ := h
  refine ⟨F, hF, fun T hT => (hFe T hT).degenerate_of_volume_eq_zero ?_, rfl⟩
  exact measure_mono_null (Set.subset_sUnion_of_mem hT) h0

/-! ### The relation `Dec` -/

/-- Finite families of polygonal pieces with null overlaps, pairwise congruent.  For polygonal sets
this is (equivalent to) `Equidecomposable`, but it is easier to compose. -/
def Dec (P P' : Set E2) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (Q Q' : ι → Set E2), (∀ i, IsPolygonal (Q i)) ∧
    (∀ i, IsPolygonal (Q' i)) ∧ P = ⋃ i, Q i ∧ P' = ⋃ i, Q' i ∧
    (∀ i j, i ≠ j → volume (Q i ∩ Q j) = 0) ∧ (∀ i j, i ≠ j → volume (Q' i ∩ Q' j) = 0) ∧
    ∀ i, SetCongruent (Q i) (Q' i)

theorem Dec.equidecomposable {P P' : Set E2} (h : Dec P P') : Equidecomposable P P' := by
  obtain ⟨ι, inst, Q, Q', hQ, hQ', rfl, rfl, h1, h2, hc⟩ := h
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => Q (e.symm k), fun k => Q' (e.symm k),
    ⟨fun k => hQ _, ?_, fun i j hij => ?_⟩, ⟨fun k => hQ' _, ?_, fun i j hij => ?_⟩,
    fun k => hc _⟩
  · exact (e.symm.surjective.iUnion_comp Q).symm
  · exact ((hQ _).inter (hQ _)).degenerate_of_volume_eq_zero
      (h1 _ _ fun h => hij (e.symm.injective h))
  · exact (e.symm.surjective.iUnion_comp Q').symm
  · exact ((hQ' _).inter (hQ' _)).degenerate_of_volume_eq_zero
      (h2 _ _ fun h => hij (e.symm.injective h))

theorem Dec.symm {P P' : Set E2} (h : Dec P P') : Dec P' P := by
  obtain ⟨ι, inst, Q, Q', hQ, hQ', hP, hP', h1, h2, hc⟩ := h
  exact ⟨ι, inst, Q', Q, hQ', hQ, hP', hP, h2, h1, fun i => (hc i).symm⟩

theorem Dec.of_congruent {P P' : Set E2} (hP : IsPolygonal P) (hP' : IsPolygonal P')
    (h : SetCongruent P P') : Dec P P' :=
  ⟨Unit, inferInstance, fun _ => P, fun _ => P', fun _ => hP, fun _ => hP',
    (Set.iUnion_const P).symm, (Set.iUnion_const P').symm,
    fun i j hij => absurd (Subsingleton.elim i j) hij,
    fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ => h⟩

theorem Dec.refl {P : Set E2} (hP : IsPolygonal P) : Dec P P :=
  Dec.of_congruent hP hP (SetCongruent.refl P)

theorem Dec.isPolygonal_left {P P' : Set E2} (h : Dec P P') : IsPolygonal P := by
  obtain ⟨ι, inst, Q, Q', hQ, hQ', rfl, rfl, h1, h2, hc⟩ := h
  have : ⋃ i, Q i = ⋃₀ (Set.range Q) := by rw [Set.sUnion_range]
  rw [this]
  exact IsPolygonal.sUnion (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact hQ i)

theorem Dec.isPolygonal_right {P P' : Set E2} (h : Dec P P') : IsPolygonal P' :=
  h.symm.isPolygonal_left

theorem Dec.trans {P P' P'' : Set E2} (h : Dec P P') (h' : Dec P' P'') : Dec P P'' := by
  obtain ⟨ι, inst, Q, Q', hQ, hQ', rfl, rfl, h1, h2, hc⟩ := h
  obtain ⟨κ, inst', R, R', hR, hR', hP, rfl, k1, k2, hd⟩ := h'
  choose f hf using hc
  choose g hg using hd
  let _ := inst
  let _ := inst'
  -- the refined pieces
  let C : ι × κ → Set E2 := fun p => Q' p.1 ∩ R p.2
  have hC : ∀ p, IsPolygonal (C p) := fun p => (hQ' p.1).inter (hR p.2)
  have hCU : ∀ i, Q' i = ⋃ j, C (i, j) := by
    intro i
    simp only [C, ← Set.inter_iUnion, ← hP]
    exact (Set.inter_eq_left.2 (Set.subset_iUnion Q' i)).symm
  have hA : ∀ p, (f p.1).symm '' C p ⊆ Q p.1 := by
    rintro p _ ⟨y, hy, rfl⟩
    have : y ∈ f p.1 '' Q p.1 := by rw [hf p.1]; exact hy.1
    obtain ⟨z, hz, rfl⟩ := this
    simpa using hz
  have hB : ∀ p, g p.2 '' C p ⊆ R' p.2 := by
    rintro p _ ⟨y, hy, rfl⟩
    rw [← hg p.2]; exact ⟨y, hy.2, rfl⟩
  refine ⟨ι × κ, inferInstance, fun p => (f p.1).symm '' C p, fun p => (g p.2) '' C p,
    fun p => (hC p).image_isometryEquiv _, fun p => (hC p).image_isometryEquiv _, ?_, ?_, ?_, ?_,
    fun p => ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Prod.exists]
    constructor
    · rintro ⟨i, hi⟩
      have : f i x ∈ Q' i := by rw [← hf i]; exact ⟨x, hi, rfl⟩
      rw [hCU i] at this
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 this
      exact ⟨i, j, f i x, hj, by simp⟩
    · rintro ⟨i, j, y, hy, rfl⟩
      exact ⟨i, hA (i, j) ⟨y, hy, rfl⟩⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      rw [← hg j] at hj
      obtain ⟨y, hy, rfl⟩ := hj
      have : y ∈ ⋃ i, Q' i := by rw [hP]; exact Set.mem_iUnion.2 ⟨j, hy⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
      exact ⟨(i, j), y, ⟨hi, hy⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, hx⟩
      exact ⟨j, hB (i, j) hx⟩
  · rintro ⟨i, j⟩ ⟨k, l⟩ hne
    by_cases hik : i = k
    · subst hik
      have hjl : j ≠ l := fun h => hne (by rw [h])
      rw [← Set.image_inter (f i).symm.injective, volume_image_isometryEquiv]
      exact measure_mono_null (show C (i, j) ∩ C (i, l) ⊆ R j ∩ R l from fun x hx => ⟨hx.1.2, hx.2.2⟩)
        (k1 j l hjl)
    · exact measure_mono_null (Set.inter_subset_inter (hA (i, j)) (hA (k, l))) (h1 i k hik)
  · rintro ⟨i, j⟩ ⟨k, l⟩ hne
    by_cases hjl : j = l
    · subst hjl
      have hik : i ≠ k := fun h => hne (by rw [h])
      rw [← Set.image_inter (g j).injective, volume_image_isometryEquiv]
      exact measure_mono_null (show C (i, j) ∩ C (k, j) ⊆ Q' i ∩ Q' k from fun x hx => ⟨hx.1.1, hx.2.1⟩)
        (h2 i k hik)
    · exact measure_mono_null (Set.inter_subset_inter (hB (i, j)) (hB (k, l))) (k2 j l hjl)
  · refine SetCongruent.trans ⟨f p.1, ?_⟩ ⟨g p.2, rfl⟩
    rw [Set.image_image]; simp

theorem Dec.iUnion {κ : Type} [Fintype κ] {P P' : κ → Set E2} (h : ∀ k, Dec (P k) (P' k))
    (h1 : ∀ i j, i ≠ j → volume (P i ∩ P j) = 0) (h2 : ∀ i j, i ≠ j → volume (P' i ∩ P' j) = 0) :
    Dec (⋃ k, P k) (⋃ k, P' k) := by
  choose ι inst Q Q' hQ hQ' hU hU' n1 n1' hc using h
  have sub : ∀ k a, Q k a ⊆ P k := fun k a => by rw [hU k]; exact Set.subset_iUnion (Q k) a
  have sub' : ∀ k a, Q' k a ⊆ P' k := fun k a => by rw [hU' k]; exact Set.subset_iUnion (Q' k) a
  refine ⟨Σ k, ι k, inferInstance, fun p => Q p.1 p.2, fun p => Q' p.1 p.2, fun p => hQ _ _,
    fun p => hQ' _ _, ?_, ?_, ?_, ?_, fun p => hc _ _⟩
  · ext x; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨k, hk⟩
      rw [hU k] at hk
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hk
      exact ⟨⟨k, a⟩, ha⟩
    · rintro ⟨⟨k, a⟩, ha⟩
      exact ⟨k, sub k a ha⟩
  · ext x; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨k, hk⟩
      rw [hU' k] at hk
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hk
      exact ⟨⟨k, a⟩, ha⟩
    · rintro ⟨⟨k, a⟩, ha⟩
      exact ⟨k, sub' k a ha⟩
  · rintro ⟨k, a⟩ ⟨l, b⟩ hne
    by_cases hkl : k = l
    · subst hkl
      exact n1 k a b fun h => hne (by rw [h])
    · exact measure_mono_null (Set.inter_subset_inter (sub k a) (sub l b)) (h1 k l hkl)
  · rintro ⟨k, a⟩ ⟨l, b⟩ hne
    by_cases hkl : k = l
    · subst hkl
      exact n1' k a b fun h => hne (by rw [h])
    · exact measure_mono_null (Set.inter_subset_inter (sub' k a) (sub' l b)) (h2 k l hkl)

theorem Dec.union {P P' R R' : Set E2} (h : Dec P P') (h' : Dec R R')
    (h1 : volume (P ∩ R) = 0) (h2 : volume (P' ∩ R') = 0) : Dec (P ∪ R) (P' ∪ R') := by
  have := Dec.iUnion (κ := Bool) (P := fun b => cond b P R) (P' := fun b => cond b P' R')
    (by intro b; cases b <;> assumption) ?_ ?_
  · have e : ∀ A B : Set E2, (⋃ b : Bool, cond b A B) = A ∪ B := by
      intro A B; ext x; simp [Bool.exists_bool, or_comm]
    rwa [e, e] at this
  · rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · simpa [Set.inter_comm] using h1
    · simpa using h1
    · exact absurd rfl hij
  · rintro (_ | _) (_ | _) hij
    · exact absurd rfl hij
    · simpa [Set.inter_comm] using h2
    · simpa using h2
    · exact absurd rfl hij

theorem SetCongruent.vadd (S : Set E2) (w : E2) : SetCongruent S ((fun x => x + w) '' S) :=
  ⟨IsometryEquiv.addRight w, rfl⟩

/-! ### Trapezoids -/

/-- The trapezoid `t ≤ x₀ ≤ s`, `f₀ + f₁ x₀ ≤ x₁ ≤ g₀ + g₁ x₀` (with vertical parallel sides). -/
def trap (t s f0 f1 g0 g1 : ℝ) : Set E2 :=
  {x | t ≤ x 0 ∧ x 0 ≤ s ∧ f0 + f1 * x 0 ≤ x 1 ∧ x 1 ≤ g0 + g1 * x 0}

theorem convex_trap (t s f0 f1 g0 g1 : ℝ) : Convex ℝ (trap t s f0 f1 g0 g1) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  obtain rfl : b = 1 - a := by linarith
  simp only [trap, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx4 ha, mul_le_mul_of_nonneg_left hy4 hb]

theorem trap_eq_convexHull {t s f0 f1 g0 g1 : ℝ} (ht : t < s) (h0 : f0 + f1 * t ≤ g0 + g1 * t)
    (h1 : f0 + f1 * s ≤ g0 + g1 * s) :
    trap t s f0 f1 g0 g1 = convexHull ℝ {!₂[t, f0 + f1 * t], !₂[t, g0 + g1 * t],
      !₂[s, f0 + f1 * s], !₂[s, g0 + g1 * s]} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
    set A0 : E2 := !₂[t, f0 + f1 * t] with hA0
    set B0 : E2 := !₂[t, g0 + g1 * t] with hB0
    set A1 : E2 := !₂[s, f0 + f1 * s] with hA1
    set B1 : E2 := !₂[s, g0 + g1 * s] with hB1
    have hc := convex_convexHull ℝ ({A0, B0, A1, B1} : Set E2)
    have mA0 : A0 ∈ convexHull ℝ ({A0, B0, A1, B1} : Set E2) := subset_convexHull ℝ _ (by simp)
    have mB0 : B0 ∈ convexHull ℝ ({A0, B0, A1, B1} : Set E2) := subset_convexHull ℝ _ (by simp)
    have mA1 : A1 ∈ convexHull ℝ ({A0, B0, A1, B1} : Set E2) := subset_convexHull ℝ _ (by simp)
    have mB1 : B1 ∈ convexHull ℝ ({A0, B0, A1, B1} : Set E2) := subset_convexHull ℝ _ (by simp)
    have hst : 0 < s - t := by linarith
    set l : ℝ := (x 0 - t) / (s - t) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hst.le
    have hl1 : l ≤ 1 := (div_le_one hst).2 (by linarith)
    have hlx : x 0 = (1 - l) * t + l * s := by rw [hl]; field_simp; ring
    set D : ℝ := (1 - l) * ((g0 + g1 * t) - (f0 + f1 * t)) + l * ((g0 + g1 * s) - (f0 + f1 * s))
      with hD
    have hD0 : 0 ≤ D := by rw [hD]; nlinarith
    have hDx : D = (g0 + g1 * x 0) - (f0 + f1 * x 0) := by rw [hD, hlx]; ring
    obtain ⟨m, hm0, hm1, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧ m * D = x 1 - (f0 + f1 * x 0) := by
      rcases hD0.eq_or_lt with h | h
      · refine ⟨0, le_rfl, zero_le_one, ?_⟩
        rw [← h]; linarith
      · refine ⟨(x 1 - (f0 + f1 * x 0)) / D, div_nonneg (by linarith) hD0, ?_, ?_⟩
        · rw [div_le_one h]; linarith
        · field_simp
    have p1 := hc mA0 mB0 (sub_nonneg.2 hm1) hm0 (by ring)
    have p2 := hc mA1 mB1 (sub_nonneg.2 hm1) hm0 (by ring)
    have p3 := hc p1 p2 (sub_nonneg.2 hl1) hl0 (by ring)
    convert p3 using 1
    have hm' := hm
    rw [hD] at hm'
    apply E2_ext
    · simp [hA0, hB0, hA1, hB1]; rw [hlx]; ring
    · simp [hA0, hB0, hA1, hB1]
      linear_combination (-1 : ℝ) * hm' + f1 * hlx
  · refine convexHull_min ?_ (convex_trap t s f0 f1 g0 g1)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [trap] <;> constructor <;> nlinarith

theorem isPolygonal_trap {t s f0 f1 g0 g1 : ℝ} (ht : t < s) (h0 : f0 + f1 * t ≤ g0 + g1 * t)
    (h1 : f0 + f1 * s ≤ g0 + g1 * s) : IsPolygonal (trap t s f0 f1 g0 g1) := by
  rw [trap_eq_convexHull ht h0 h1]
  exact isPolygonal_convexHull_of_finite (Set.toFinite _)

/-! ### Parallelograms and shears -/

/-- The affine map `p ↦ o + p₀ a + p₁ b`. -/
def psi (o a b : E2) : E2 →ᵃ[ℝ] E2 where
  toFun p := o + p 0 • a + p 1 • b
  linear :=
    { toFun := fun p => p 0 • a + p 1 • b
      map_add' := fun p q => by simp [add_smul]; abel
      map_smul' := fun c p => by simp [smul_add, smul_smul] }
  map_vadd' p v := by
    show o + (v + p) 0 • a + (v + p) 1 • b = (v 0 • a + v 1 • b) + (o + p 0 • a + p 1 • b)
    simp [add_smul]; abel

@[simp] theorem psi_apply (o a b p : E2) : psi o a b p = o + p 0 • a + p 1 • b := rfl

/-- The parallelogram `{o + a u + b v | a, b ∈ [0,1]}`. -/
def par (o u v : E2) : Set E2 := psi o v u '' trap 0 1 0 0 1 0

theorem mem_par {o u v x : E2} : x ∈ par o u v ↔
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ x = o + a • u + b • v := by
  constructor
  · rintro ⟨p, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨p 1, p 0, by simpa using h3, by simpa using h4, h1, h2, ?_⟩
    simp only [psi_apply]; abel
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    refine ⟨!₂[b, a], ⟨by simpa using h3, by simpa using h4, by simpa using h1,
      by simpa using h2⟩, ?_⟩
    simp only [psi_apply]
    simp; abel

theorem par_swap (o u v : E2) : par o u v = par o v u := by
  ext x
  rw [mem_par, mem_par]
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩; exact ⟨b, a, h3, h4, h1, h2, by abel⟩
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩; exact ⟨b, a, h3, h4, h1, h2, by abel⟩

theorem par_neg (o u v : E2) : par (o + u) (-u) v = par o u v := by
  ext x
  rw [mem_par, mem_par]
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨1 - a, b, by linarith, by linarith, h3, h4, by module⟩
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨1 - a, b, by linarith, by linarith, h3, h4, by module⟩

theorem isPolygonal_par (o u v : E2) : IsPolygonal (par o u v) :=
  (isPolygonal_trap zero_lt_one (by norm_num) (by norm_num)).image_affine _

/-- The determinant of two vectors of the plane. -/
def det2 (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

theorem psi_injective {o u v : E2} (hd : det2 u v ≠ 0) : Function.Injective (psi o v u) := by
  intro p q h
  have h0 := congrArg (fun x : E2 => x 0) h
  have h1 := congrArg (fun x : E2 => x 1) h
  simp at h0 h1
  unfold det2 at hd
  have ha : (p 0 - q 0) * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination (-u 1) * h0 + u 0 * h1
  have hb : (p 1 - q 1) * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * h0 - v 0 * h1
  have ha' := (mul_eq_zero.1 ha).resolve_right hd
  have hb' := (mul_eq_zero.1 hb).resolve_right hd
  exact E2_ext (by linarith) (by linarith)

theorem differentiable_affineMap (g : E2 →ᵃ[ℝ] E2) : Differentiable ℝ g := by
  rw [g.decomp]
  exact (LinearMap.toContinuousLinearMap g.linear).differentiable.add (differentiable_const _)

theorem volume_image_affine_null (g : E2 →ᵃ[ℝ] E2) {N : Set E2} (hN : volume N = 0) :
    volume (g '' N) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (differentiable_affineMap g).differentiableOn hN

theorem dec_shear_aux {o u v : E2} (hd : det2 u v ≠ 0) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Dec (par o u v) (par o u (v + l • u)) := by
  set ψ := psi o v u with hψ
  have hinj : Function.Injective ψ := psi_injective hd
  have e1 : par o u v = ψ '' trap 0 1 0 l 1 0 ∪ ψ '' trap 0 1 0 0 0 l := by
    rw [← Set.image_union]
    unfold par
    congr 1
    ext x
    simp only [trap, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      rcases le_total (l * x 0) (x 1) with h | h
      · left; exact ⟨h1, h2, by linarith, by linarith⟩
      · right; exact ⟨h1, h2, by linarith, by linarith⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨h1, h2, by nlinarith, by linarith⟩
      · refine ⟨h1, h2, by linarith, by nlinarith⟩
  have e2 : par o u (v + l • u) = ψ '' trap 0 1 0 l 1 0 ∪ ψ '' trap 0 1 1 0 1 l := by
    rw [← Set.image_union]
    ext x
    rw [mem_par]
    constructor
    · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
      rcases le_total (a + l * b) 1 with h | h
      · refine ⟨!₂[b, a + l * b], Or.inl ⟨h3, h4, by simp; nlinarith, by simp; linarith⟩, ?_⟩
        simp [hψ]; module
      · refine ⟨!₂[b, a + l * b], Or.inr ⟨h3, h4, by simp; linarith, by simp; nlinarith⟩, ?_⟩
        simp [hψ]; module
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · refine ⟨p 1 - l * p 0, p 0, by simp at h3 ⊢; linarith,
          by simp at h4 ⊢; nlinarith [mul_nonneg hl0 h1], h1, h2, ?_⟩
        simp [hψ]; module
      · refine ⟨p 1 - l * p 0, p 0, by simp at h3 ⊢; nlinarith [mul_le_mul_of_nonneg_left h2 hl0],
          by simp at h4 ⊢; linarith, h1, h2, ?_⟩
        simp [hψ]; module
  rw [e1, e2]
  have pM : IsPolygonal (ψ '' trap 0 1 0 l 1 0) :=
    (isPolygonal_trap zero_lt_one (by simpa using hl1) (by simpa using hl1)).image_affine ψ
  have pT2 : IsPolygonal (ψ '' trap 0 1 0 0 0 l) :=
    (isPolygonal_trap zero_lt_one (by simp) (by simpa using hl0)).image_affine ψ
  have pT1 : IsPolygonal (ψ '' trap 0 1 1 0 1 l) :=
    (isPolygonal_trap zero_lt_one (by simp) (by simpa using hl0)).image_affine ψ
  have cT : SetCongruent (ψ '' trap 0 1 0 0 0 l) (ψ '' trap 0 1 1 0 1 l) := by
    have : ψ '' trap 0 1 1 0 1 l = (fun x => x + u) '' (ψ '' trap 0 1 0 0 0 l) := by
      rw [Set.image_image]
      have : trap 0 1 1 0 1 l = (fun p : E2 => p + !₂[0, 1]) '' trap 0 1 0 0 0 l := by
        ext x
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨x - !₂[0, 1], ⟨by simpa using h1, by simpa using h2, by simp at h3 ⊢; linarith,
            by simp at h4 ⊢; linarith⟩, by simp⟩
        · rintro ⟨p, ⟨h1, h2, h3, h4⟩, rfl⟩
          exact ⟨by simpa using h1, by simpa using h2, by simp at h3 ⊢; linarith,
            by simp at h4 ⊢; linarith⟩
      rw [this, Set.image_image]
      congr 1
      funext p
      simp [hψ]; module
    rw [this]; exact SetCongruent.vadd _ u
  refine Dec.union (Dec.refl pM) (Dec.of_congruent pT2 pT1 cT) ?_ ?_
  · rw [← Set.image_inter hinj]
    refine volume_image_affine_null ψ (volume_inter_eq_zero_of_line (α := l) (β := -1) (γ := 0)
      (Or.inr (by norm_num)) ?_)
    rintro x ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩
    simp at h3 h8 ⊢; linarith
  · rw [← Set.image_inter hinj]
    refine volume_image_affine_null ψ (volume_inter_eq_zero_of_line (α := 0) (β := 1) (γ := 1)
      (Or.inr (by norm_num)) ?_)
    rintro x ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩⟩
    simp at h4 h7 ⊢; linarith

theorem det2_add_smul (u v : E2) (c : ℝ) : det2 u (v + c • u) = det2 u v := by
  simp [det2]; ring

theorem det2_neg (u v : E2) : det2 (-u) v = -det2 u v := by
  simp [det2]; ring

theorem det2_swap (u v : E2) : det2 v u = -det2 u v := by
  simp [det2]; ring

theorem dec_shear_nonneg {o u : E2} : ∀ (n : ℕ) (v : E2), det2 u v ≠ 0 → ∀ l : ℝ, 0 ≤ l →
    l ≤ n → Dec (par o u v) (par o u (v + l • u))
  | 0, v, _, l, h0, h1 => by
    have : l = 0 := by simp at h1; linarith
    subst this
    simpa using Dec.refl (isPolygonal_par o u v)
  | n + 1, v, hd, l, h0, h1 => by
    by_cases hl : l ≤ 1
    · exact dec_shear_aux hd h0 hl
    · have h2 := dec_shear_aux (o := o) hd zero_le_one le_rfl
      have hd' : det2 u (v + (1 : ℝ) • u) ≠ 0 := by rwa [det2_add_smul]
      have h3 := dec_shear_nonneg (o := o) (u := u) n (v + (1 : ℝ) • u) hd' (l - 1) (by linarith)
        (by push_cast at h1; linarith)
      have e : v + (1 : ℝ) • u + (l - 1) • u = v + l • u := by module
      rw [e] at h3
      exact h2.trans h3

/-- Shearing a parallelogram: replacing the side `v` by `v + l u` is a dissection (`l` real). -/
theorem dec_shear {o u v : E2} (hd : det2 u v ≠ 0) (l : ℝ) :
    Dec (par o u v) (par o u (v + l • u)) := by
  rcases le_total 0 l with h | h
  · obtain ⟨n, hn⟩ := exists_nat_ge l
    exact dec_shear_nonneg n v hd l h hn
  · have hd' : det2 (-u) v ≠ 0 := by rwa [det2_neg, neg_ne_zero]
    obtain ⟨n, hn⟩ := exists_nat_ge (-l)
    have := dec_shear_nonneg (o := o + u) n v hd' (-l) (by linarith) hn
    have e : v + (-l) • (-u) = v + l • u := by module
    rwa [e, par_neg, par_neg] at this

/-! ### Motions given by orthonormal frames, and rectangles -/

theorem motion_exists (o p q : E2) (hp : p 0 ^ 2 + p 1 ^ 2 = 1) (hq : q 0 ^ 2 + q 1 ^ 2 = 1)
    (hpq : p 0 * q 0 + p 1 * q 1 = 0) :
    ∃ g : E2 ≃ᵢ E2, ∀ x, g x = o + x 0 • p + x 1 • q := by
  let L : E2 →ₗᵢ[ℝ] E2 :=
    { toLinearMap := (psi 0 p q).linear
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        have : ∀ x : E2, (psi 0 p q).linear x = x 0 • p + x 1 • q := fun x => rfl
        simp only [this, Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          Real.norm_eq_abs, sq_abs]
        linear_combination x 0 ^ 2 * hp + x 1 ^ 2 * hq + 2 * x 0 * x 1 * hpq }
  let e := L.toLinearIsometryEquiv rfl
  refine ⟨e.toIsometryEquiv.trans (IsometryEquiv.addLeft o), fun x => ?_⟩
  show o + (x 0 • p + x 1 • q) = _
  rw [add_assoc]

/-- The rectangle `[0,W] × [0,h]`. -/
def rect (W h : ℝ) : Set E2 := trap 0 W 0 0 h 0

theorem isPolygonal_rect {W h : ℝ} (hW : 0 < W) (hh : 0 ≤ h) : IsPolygonal (rect W h) :=
  isPolygonal_trap hW (by simpa using hh) (by simpa using hh)

theorem rect_eq_par {W h : ℝ} (hW : 0 < W) (hh : 0 < h) :
    rect W h = par 0 !₂[W, 0] !₂[0, h] := by
  ext x
  rw [mem_par]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨x 0 / W, x 1 / h, div_nonneg h1 hW.le, (div_le_one hW).2 h2, ?_, ?_, ?_⟩
    · simp at h3; exact div_nonneg h3 hh.le
    · simp at h4; exact (div_le_one hh).2 h4
    · apply E2_ext <;> simp <;> field_simp
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    refine ⟨by simp; positivity, by simp; nlinarith, by simp; positivity, by simp; nlinarith⟩

theorem rect_congr (o : E2) {u v : E2} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : u 0 ^ 2 + u 1 ^ 2 = a ^ 2) (hv : v 0 ^ 2 + v 1 ^ 2 = b ^ 2)
    (huv : u 0 * v 0 + u 1 * v 1 = 0) : SetCongruent (rect a b) (par o u v) := by
  obtain ⟨g, hg⟩ := motion_exists o (a⁻¹ • u) (b⁻¹ • v)
    (by simp; field_simp; linarith) (by simp; field_simp; linarith)
    (by simp; field_simp; linear_combination huv)
  refine ⟨g, ?_⟩
  rw [rect_eq_par ha hb]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, t, h1, h2, h3, h4, rfl⟩ := mem_par.1 hx
    rw [mem_par]
    refine ⟨s, t, h1, h2, h3, h4, ?_⟩
    rw [hg]
    simp [smul_smul]
    field_simp
  · intro hy
    obtain ⟨s, t, h1, h2, h3, h4, rfl⟩ := mem_par.1 hy
    refine ⟨!₂[s * a, t * b], mem_par.2 ⟨s, t, h1, h2, h3, h4, ?_⟩, ?_⟩
    · apply E2_ext <;> simp
    · rw [hg]
      simp [smul_smul]
      have e1 : s * a * a⁻¹ = s := by field_simp
      have e2 : t * b * b⁻¹ = t := by field_simp
      rw [e1, e2]

/-! ### Normal form of a parallelogram -/

theorem nf_algebra (u0 u1 v0 v1 L : ℝ) (hL : 0 < L) (hnu : 0 < u0 ^ 2 + u1 ^ 2)
    (h : (u0 * v1 - u1 * v0) ^ 2 ≤ L ^ 2 * (u0 ^ 2 + u1 ^ 2)) :
    ∃ lam mu : ℝ, (v0 + lam * u0) ^ 2 + (v1 + lam * u1) ^ 2 = L ^ 2 ∧
      (v0 + lam * u0) * (u0 + mu * (v0 + lam * u0)) +
        (v1 + lam * u1) * (u1 + mu * (v1 + lam * u1)) = 0 ∧
      (u0 + mu * (v0 + lam * u0)) ^ 2 + (u1 + mu * (v1 + lam * u1)) ^ 2 =
        (u0 * v1 - u1 * v0) ^ 2 / L ^ 2 := by
  have hD : 0 ≤ L ^ 2 * (u0 ^ 2 + u1 ^ 2) - (u0 * v1 - u1 * v0) ^ 2 := by linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, (u0 ^ 2 + u1 ^ 2) * lam + (u0 * v0 + u1 * v1) =
      Real.sqrt (L ^ 2 * (u0 ^ 2 + u1 ^ 2) - (u0 * v1 - u1 * v0) ^ 2) :=
    ⟨(Real.sqrt (L ^ 2 * (u0 ^ 2 + u1 ^ 2) - (u0 * v1 - u1 * v0) ^ 2) - (u0 * v0 + u1 * v1)) /
      (u0 ^ 2 + u1 ^ 2), by field_simp; ring⟩
  have hsq : ((u0 ^ 2 + u1 ^ 2) * lam + (u0 * v0 + u1 * v1)) ^ 2 =
      L ^ 2 * (u0 ^ 2 + u1 ^ 2) - (u0 * v1 - u1 * v0) ^ 2 := by rw [hlam, Real.sq_sqrt hD]
  have h1 : (v0 + lam * u0) ^ 2 + (v1 + lam * u1) ^ 2 = L ^ 2 := by
    have : (u0 ^ 2 + u1 ^ 2) * ((v0 + lam * u0) ^ 2 + (v1 + lam * u1) ^ 2 - L ^ 2) = 0 := by
      linear_combination hsq
    have := (mul_eq_zero.1 this).resolve_left hnu.ne'
    linarith
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu * L ^ 2 + (u0 * (v0 + lam * u0) + u1 * (v1 + lam * u1)) = 0 :=
    ⟨-(u0 * (v0 + lam * u0) + u1 * (v1 + lam * u1)) / L ^ 2, by field_simp; ring⟩
  refine ⟨lam, mu, h1, by linear_combination hmu + mu * h1, ?_⟩
  rw [eq_div_iff (by positivity)]
  linear_combination (mu * L ^ 2 + (u0 * (v0 + lam * u0) + u1 * (v1 + lam * u1))) * hmu +
    (mu ^ 2 * L ^ 2 - (u0 ^ 2 + u1 ^ 2)) * h1

/-- Every parallelogram is equidecomposable with a rectangle `L × (area / L)`, as soon as
`L` is at least the height of the parallelogram over the side `u`. -/
theorem dec_normal_form (o : E2) {u v : E2} (hd : det2 u v ≠ 0) {L : ℝ} (hL : 0 < L)
    (h : det2 u v ^ 2 ≤ L ^ 2 * (u 0 ^ 2 + u 1 ^ 2)) :
    Dec (par o u v) (rect L (|det2 u v| / L)) := by
  have hnu : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    rcases (add_nonneg (sq_nonneg (u 0)) (sq_nonneg (u 1))).eq_or_lt with h0 | h0
    · exfalso; apply hd
      have a0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have a1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      simp [det2, a0, a1]
    · exact h0
  obtain ⟨lam, mu, h1, h2, h3⟩ := nf_algebra (u 0) (u 1) (v 0) (v 1) L hL hnu h
  have hd1 : det2 u (v + lam • u) = det2 u v := det2_add_smul u v lam
  have s1 := dec_shear (o := o) hd lam
  have hd2 : det2 (v + lam • u) u ≠ 0 := by rw [det2_swap, hd1]; exact neg_ne_zero.2 hd
  have s2 := dec_shear (o := o) hd2 mu
  rw [par_swap o u (v + lam • u)] at s1
  refine (s1.trans s2).trans (Dec.symm ?_)
  refine Dec.of_congruent (isPolygonal_rect hL (by positivity)) (isPolygonal_par _ _ _) ?_
  refine rect_congr o hL (div_pos (abs_pos.2 hd) hL) (by simpa using h1) ?_
    (by simp; linear_combination h2)
  rw [div_pow, sq_abs]
  simp [det2]; linear_combination h3

/-! ### Folding a trapezoid into a parallelogram -/

/-- Cutting a trapezoid along its midline and rotating one half by `π` about the midpoint of a leg
gives a parallelogram with the vertical sides of length `H` (the sum of the two parallel sides). -/
theorem dec_trap_par {t m f0 f1 g0 g1 H : ℝ} (ht : t < m) (h0 : f0 + f1 * t ≤ g0 + g1 * t)
    (h1 : f0 + f1 * (2 * m - t) ≤ g0 + g1 * (2 * m - t))
    (hH : H = (g0 + g1 * t - (f0 + f1 * t)) +
      (g0 + g1 * (2 * m - t) - (f0 + f1 * (2 * m - t)))) :
    Dec (trap t (2 * m - t) f0 f1 g0 g1) (trap t m (g0 - H) g1 g0 g1) := by
  have hst : 0 < (2 * m - t) - t := by linarith
  have key : ∀ y, ((g0 + g1 * y) - (f0 + f1 * y)) * ((2 * m - t) - t) =
      ((2 * m - t) - y) * ((g0 + g1 * t) - (f0 + f1 * t)) +
      (y - t) * ((g0 + g1 * (2 * m - t)) - (f0 + f1 * (2 * m - t))) := fun y => by ring
  have hd : ∀ y, t ≤ y → y ≤ 2 * m - t →
      f0 + f1 * y ≤ g0 + g1 * y ∧ g0 + g1 * y - H ≤ f0 + f1 * y := by
    intro y hy1 hy2
    have e1 := key y
    have p1 : 0 ≤ ((2 * m - t) - y) * ((g0 + g1 * t) - (f0 + f1 * t)) :=
      mul_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (y - t) * ((g0 + g1 * (2 * m - t)) - (f0 + f1 * (2 * m - t))) :=
      mul_nonneg (by linarith) (by linarith)
    constructor
    · have : 0 ≤ ((g0 + g1 * y) - (f0 + f1 * y)) * ((2 * m - t) - t) := by rw [e1]; linarith
      have := (mul_nonneg_iff_of_pos_right hst).1 this
      linarith
    · have p3 : 0 ≤ (y - t) * ((g0 + g1 * t) - (f0 + f1 * t)) :=
        mul_nonneg (by linarith) (by linarith)
      have p4 : 0 ≤ ((2 * m - t) - y) * ((g0 + g1 * (2 * m - t)) - (f0 + f1 * (2 * m - t))) :=
        mul_nonneg (by linarith) (by linarith)
      have : 0 ≤ (H - ((g0 + g1 * y) - (f0 + f1 * y))) * ((2 * m - t) - t) := by
        have : (H - ((g0 + g1 * y) - (f0 + f1 * y))) * ((2 * m - t) - t) =
            (y - t) * ((g0 + g1 * t) - (f0 + f1 * t)) +
            ((2 * m - t) - y) * ((g0 + g1 * (2 * m - t)) - (f0 + f1 * (2 * m - t))) := by
          rw [hH]; ring
        rw [this]; linarith
      have := (mul_nonneg_iff_of_pos_right hst).1 this
      linarith
  have hL1 : f0 + f1 * m ≤ g0 + g1 * m := (hd m ht.le (by linarith)).1
  let ρ : E2 ≃ᵢ E2 := IsometryEquiv.subLeft !₂[2 * m, 2 * (f0 + f1 * m)]
  have eR : ρ '' trap m (2 * m - t) f0 f1 g0 g1 = trap t m (g0 - H) g1 f0 f1 := by
    ext y
    constructor
    · rintro ⟨x, ⟨a1, a2, a3, a4⟩, rfl⟩
      simp only [ρ, IsometryEquiv.subLeft_apply] at *
      simp only [trap, Set.mem_ofPred_eq, PiLp.sub_apply]
      simp
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨a1, a2, a3, a4⟩
      refine ⟨ρ y, ?_, by simp [ρ]⟩
      simp only [trap, Set.mem_ofPred_eq, ρ, IsometryEquiv.subLeft_apply, PiLp.sub_apply]
      simp
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have eU : trap t (2 * m - t) f0 f1 g0 g1 =
      trap t m f0 f1 g0 g1 ∪ trap m (2 * m - t) f0 f1 g0 g1 := by
    ext x
    simp only [trap, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩
      rcases le_total (x 0) m with h | h
      · exact Or.inl ⟨a1, h, a3, a4⟩
      · exact Or.inr ⟨h, a2, a3, a4⟩
    · rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
      · exact ⟨a1, by linarith, a3, a4⟩
      · exact ⟨by linarith, a2, a3, a4⟩
  have eP : trap t m f0 f1 g0 g1 ∪ trap t m (g0 - H) g1 f0 f1 =
      trap t m (g0 - H) g1 g0 g1 := by
    ext x
    simp only [trap, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
      · have := (hd (x 0) a1 (by linarith)).2
        exact ⟨a1, a2, by linarith, a4⟩
      · have := (hd (x 0) a1 (by linarith)).1
        exact ⟨a1, a2, a3, by linarith⟩
    · rintro ⟨a1, a2, a3, a4⟩
      rcases le_total (f0 + f1 * x 0) (x 1) with h | h
      · exact Or.inl ⟨a1, a2, h, a4⟩
      · exact Or.inr ⟨a1, a2, a3, h⟩
  have pL := isPolygonal_trap ht h0 hL1
  have pR := isPolygonal_trap (by linarith : m < 2 * m - t) hL1 h1
  rw [eU, ← eP, ← eR]
  refine Dec.union (Dec.refl pL) (Dec.of_congruent pR (pR.image_isometryEquiv ρ) ⟨ρ, rfl⟩) ?_ ?_
  · refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := m) (Or.inl one_ne_zero) ?_
    rintro x ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
    simp; linarith
  · rw [eR]
    refine volume_inter_eq_zero_of_line (α := f1) (β := -1) (γ := -f0) (Or.inr (by norm_num)) ?_
    rintro x ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
    simp; linarith

theorem trap_eq_par {t m g0 g1 H : ℝ} (ht : t < m) (hH : 0 < H) :
    trap t m (g0 - H) g1 g0 g1 =
      par !₂[t, g0 + g1 * t - H] !₂[m - t, g1 * (m - t)] !₂[0, H] := by
  have hw : 0 < m - t := by linarith
  ext x
  rw [mem_par]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩
    refine ⟨(x 0 - t) / (m - t), (x 1 - (g0 - H + g1 * x 0)) / H, div_nonneg (by linarith) hw.le,
      (div_le_one hw).2 (by linarith), div_nonneg (by linarith) hH.le,
      (div_le_one hH).2 (by linarith), ?_⟩
    apply E2_ext
    · simp; field_simp; ring
    · simp; field_simp; ring
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    simp only [trap, Set.mem_ofPred_eq]
    simp
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- A nondegenerate trapezoid (vertical parallel sides at `x₀ = t` and `x₀ = 2m - t`) is
equidecomposable with a rectangle of equal area and any side length `L ≥ H`, where `H` is the sum
of the two parallel sides. -/
theorem dec_trap_rect {t m f0 f1 g0 g1 H L : ℝ} (ht : t < m) (h0 : f0 + f1 * t ≤ g0 + g1 * t)
    (h1 : f0 + f1 * (2 * m - t) ≤ g0 + g1 * (2 * m - t))
    (hH : H = (g0 + g1 * t - (f0 + f1 * t)) +
      (g0 + g1 * (2 * m - t) - (f0 + f1 * (2 * m - t)))) (hpos : 0 < H) (hL : H ≤ L) :
    Dec (trap t (2 * m - t) f0 f1 g0 g1) (rect L ((m - t) * H / L)) := by
  have hL0 : 0 < L := lt_of_lt_of_le hpos hL
  refine (dec_trap_par ht h0 h1 hH).trans ?_
  rw [trap_eq_par ht hpos]
  have hw : 0 < m - t := by linarith
  have hd : det2 !₂[m - t, g1 * (m - t)] !₂[0, H] = (m - t) * H := by simp [det2]
  have := dec_normal_form (!₂[t, g0 + g1 * t - H] : E2) (u := !₂[m - t, g1 * (m - t)])
    (v := !₂[0, H]) (by rw [hd]; positivity) hL0 (by
      rw [hd]; simp
      have hH2 : H ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hpos.le hL 2
      nlinarith [mul_le_mul_of_nonneg_left hH2 (sq_nonneg (m - t)),
        mul_nonneg (sq_nonneg L) (mul_nonneg (sq_nonneg (m - t)) (sq_nonneg g1))])
  rwa [hd, abs_of_pos (by positivity)] at this

/-! ### Slicing a convex polygon by vertical lines -/

theorem exists_uv {l r x : E2} {a b : ℝ} (hab : a < b) (hl : l 0 ≤ a) (hr : b ≤ r 0)
    (hx : x ∈ segment ℝ l r) (hx1 : a ≤ x 0) (hx2 : x 0 ≤ b) :
    ∃ u v : E2, u ∈ segment ℝ l r ∧ v ∈ segment ℝ l r ∧ u 0 = a ∧ v 0 = b ∧
      x ∈ segment ℝ u v := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
  obtain rfl : p = 1 - q := by linarith
  have hD : 0 < r 0 - l 0 := by linarith
  have hxq : ((1 - q) • l + q • r) 0 = l 0 + q * (r 0 - l 0) := by simp; ring
  rw [hxq] at hx1 hx2
  obtain ⟨ta, hta⟩ : ∃ ta, ta = (a - l 0) / (r 0 - l 0) := ⟨_, rfl⟩
  obtain ⟨tb, htb⟩ : ∃ tb, tb = (b - l 0) / (r 0 - l 0) := ⟨_, rfl⟩
  have hta' : ta * (r 0 - l 0) = a - l 0 := by rw [hta]; field_simp
  have htb' : tb * (r 0 - l 0) = b - l 0 := by rw [htb]; field_simp
  have hta0 : 0 ≤ ta := by rw [hta]; exact div_nonneg (by linarith) hD.le
  have haq : ta ≤ q := by nlinarith
  have hqb : q ≤ tb := by nlinarith
  have htab : ta < tb := by nlinarith
  have hq1 : q ≤ 1 := by linarith
  have htb1 : tb ≤ 1 := by
    by_contra h; push_neg at h; nlinarith
  obtain ⟨k, hk⟩ : ∃ k, k * (tb - ta) = q - ta := ⟨(q - ta) / (tb - ta), by field_simp⟩
  have hk0 : 0 ≤ k := by nlinarith
  have hk1 : k ≤ 1 := by nlinarith
  refine ⟨(1 - ta) • l + ta • r, (1 - tb) • l + tb • r, ⟨1 - ta, ta, by linarith, hta0, by ring, rfl⟩,
    ⟨1 - tb, tb, by linarith, by linarith, by ring, rfl⟩, ?_, ?_, ⟨1 - k, k, by linarith, hk0, by ring, ?_⟩⟩
  · simp; nlinarith
  · simp; nlinarith
  · ext i
    simp
    linear_combination (r i - l i) * hk

theorem exists_slice {K : Set E2} (hK : IsCompact K) (c : ℝ) (hne : ∃ e ∈ K, e 0 = c) :
    ∃ A B : E2, A ∈ K ∧ B ∈ K ∧ A 0 = c ∧ B 0 = c ∧
      ∀ u ∈ K, u 0 = c → A 1 ≤ u 1 ∧ u 1 ≤ B 1 := by
  have hS : IsCompact (K ∩ {x : E2 | x 0 = c}) :=
    hK.inter_right (isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨e, he, hec⟩ := hne
  have hSne : (K ∩ {x : E2 | x 0 = c}).Nonempty := ⟨e, he, hec⟩
  have hcont : Continuous (fun x : E2 => x 1) := by fun_prop
  obtain ⟨A, hA, hAmin⟩ := hS.exists_isMinOn hSne hcont.continuousOn
  obtain ⟨B, hB, hBmax⟩ := hS.exists_isMaxOn hSne hcont.continuousOn
  exact ⟨A, B, hA.1, hB.1, hA.2, hB.2, fun u hu hu0 => ⟨hAmin ⟨hu, hu0⟩, hBmax ⟨hu, hu0⟩⟩⟩

theorem convex_halfspace0 (a : ℝ) : Convex ℝ {y : E2 | y 0 ≤ a} := by
  intro y hy z hz s t hs ht hst
  simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  have : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hy hs, mul_le_mul_of_nonneg_left hz ht]

theorem convex_halfspace0' (a : ℝ) : Convex ℝ {y : E2 | a ≤ y 0} := by
  intro y hy z hz s t hs ht hst
  simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
  have : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hy hs, mul_le_mul_of_nonneg_left hz ht]

theorem slab_trap {E : Set E2} (hE : E.Finite) {a b : ℝ} (hab : a < b)
    (ha : ∃ e ∈ E, e 0 = a) (hb : ∃ e ∈ E, e 0 = b) (hgap : ∀ e ∈ E, ¬(a < e 0 ∧ e 0 < b)) :
    ∃ f0 f1 g0 g1 : ℝ, f0 + f1 * a ≤ g0 + g1 * a ∧ f0 + f1 * b ≤ g0 + g1 * b ∧
      convexHull ℝ E ∩ {x | a ≤ x 0 ∧ x 0 ≤ b} = trap a b f0 f1 g0 g1 := by
  have hK : IsCompact (convexHull ℝ E) := hE.isCompact_convexHull ℝ
  have hsub : ∀ e ∈ E, e ∈ convexHull ℝ E := fun e he => subset_convexHull ℝ E he
  obtain ⟨Aa, Ba, hAa, hBa, hAa0, hBa0, hsa⟩ := exists_slice hK a
    (by obtain ⟨e, he, h⟩ := ha; exact ⟨e, hsub e he, h⟩)
  obtain ⟨Ab, Bb, hAb, hBb, hAb0, hBb0, hsb⟩ := exists_slice hK b
    (by obtain ⟨e, he, h⟩ := hb; exact ⟨e, hsub e he, h⟩)
  have hba : 0 < b - a := by linarith
  obtain ⟨f1, hf1⟩ : ∃ f1, f1 * (b - a) = Ab 1 - Aa 1 := ⟨(Ab 1 - Aa 1) / (b - a), by field_simp⟩
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 * (b - a) = Bb 1 - Ba 1 := ⟨(Bb 1 - Ba 1) / (b - a), by field_simp⟩
  have hfa : (Aa 1 - f1 * a) + f1 * a = Aa 1 := by ring
  have hfb : (Aa 1 - f1 * a) + f1 * b = Ab 1 := by linear_combination hf1
  have hga : (Ba 1 - g1 * a) + g1 * a = Ba 1 := by ring
  have hgb : (Ba 1 - g1 * a) + g1 * b = Bb 1 := by linear_combination hg1
  refine ⟨Aa 1 - f1 * a, f1, Ba 1 - g1 * a, g1, by rw [hfa, hga]; exact (hsa Ba hBa hBa0).1,
    by rw [hfb, hgb]; exact (hsb Bb hBb hBb0).1, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hx1, hx2⟩
    obtain ⟨e1, he1, he1a⟩ := ha
    obtain ⟨e2, he2, he2b⟩ := hb
    have hsplit : E = {e ∈ E | e 0 ≤ a} ∪ {e ∈ E | b ≤ e 0} := by
      ext e; simp only [Set.mem_union, Set.mem_sep_iff]
      constructor
      · intro he
        have := hgap e he
        rcases le_or_gt (e 0) a with h | h
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, by by_contra h'; exact this ⟨h, by linarith⟩⟩
      · rintro (h | h) <;> exact h.1
    have hn1 : ({e ∈ E | e 0 ≤ a} : Set E2).Nonempty := ⟨e1, he1, he1a.le⟩
    have hn2 : ({e ∈ E | b ≤ e 0} : Set E2).Nonempty := ⟨e2, he2, he2b.ge⟩
    rw [hsplit, convexHull_union hn1 hn2] at hx
    obtain ⟨l, hl, r, hr, hlr⟩ := mem_convexJoin.1 hx
    have sa : ({e ∈ E | e 0 ≤ a} : Set E2) ⊆ {y : E2 | y 0 ≤ a} := fun e he => he.2
    have sb : ({e ∈ E | b ≤ e 0} : Set E2) ⊆ {y : E2 | b ≤ y 0} := fun e he => he.2
    have ta : ({e ∈ E | e 0 ≤ a} : Set E2) ⊆ E := fun e he => he.1
    have tb : ({e ∈ E | b ≤ e 0} : Set E2) ⊆ E := fun e he => he.1
    have hl0 : l 0 ≤ a := convexHull_min sa (convex_halfspace0 a) hl
    have hr0 : b ≤ r 0 := convexHull_min sb (convex_halfspace0' b) hr
    have hconv := convex_convexHull ℝ E
    have hlK : l ∈ convexHull ℝ E := convexHull_mono ta hl
    have hrK : r ∈ convexHull ℝ E := convexHull_mono tb hr
    obtain ⟨u, v, hu, hv, hu0, hv0, hxuv⟩ := exists_uv hab hl0 hr0 hlr hx1 hx2
    have huK := hconv.segment_subset hlK hrK hu
    have hvK := hconv.segment_subset hlK hrK hv
    have hu1 := hsa u huK hu0
    have hv1 := hsb v hvK hv0
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hxuv
    obtain rfl : p = 1 - q := by linarith
    have e0 : ((1 - q) • u + q • v) 0 = (1 - q) * a + q * b := by simp [hu0, hv0]
    have e1 : ((1 - q) • u + q • v) 1 = (1 - q) * u 1 + q * v 1 := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e0]; nlinarith
    · rw [e0]; nlinarith
    · rw [e0, e1]
      nlinarith [mul_le_mul_of_nonneg_left hu1.1 hp, mul_le_mul_of_nonneg_left hv1.1 hq]
    · rw [e0, e1]
      nlinarith [mul_le_mul_of_nonneg_left hu1.2 hp, mul_le_mul_of_nonneg_left hv1.2 hq]
  · intro hx
    refine ⟨?_, hx.1, hx.2.1⟩
    have hx' := hx
    rw [trap_eq_convexHull hab (by rw [hfa, hga]; exact (hsa Ba hBa hBa0).1)
      (by rw [hfb, hgb]; exact (hsb Bb hBb hBb0).1)] at hx'
    refine convexHull_min ?_ (convex_convexHull ℝ E) hx'
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · convert hAa using 1; apply E2_ext
      · simp [hAa0]
      · simp
    · convert hBa using 1; apply E2_ext
      · simp [hBa0]
      · simp
    · convert hAb using 1; apply E2_ext
      · simp [hAb0]
      · simpa using hfb
    · convert hBb using 1; apply E2_ext
      · simp [hBb0]
      · simpa using hgb

theorem exists_gap (X : Finset ℝ) (mn mx : ℝ) (hmn : mn ∈ X) (hmx : mx ∈ X) (hlt : mn < mx)
    {y : ℝ} (h1 : mn ≤ y) (h2 : y ≤ mx) (hhi : ∀ c ∈ X, c ≤ mx) :
    ∃ a ∈ X, ∃ b ∈ X, a < b ∧ (∀ c ∈ X, ¬(a < c ∧ c < b)) ∧ a ≤ y ∧ y ≤ b := by
  classical
  have hne : (X.filter (fun c => c ≤ y ∧ c < mx)).Nonempty := ⟨mn, by simp [hmn, h1, hlt]⟩
  have ha := Finset.max'_mem _ hne
  obtain ⟨ha1, ha2, ha3⟩ := Finset.mem_filter.1 ha
  have hne2 : (X.filter (fun c => (X.filter (fun c => c ≤ y ∧ c < mx)).max' hne < c)).Nonempty :=
    ⟨mx, by simp [hmx, ha3]⟩
  have hb := Finset.min'_mem _ hne2
  obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
  refine ⟨_, ha1, _, hb1, hb2, ?_, ha2, ?_⟩
  · intro c hc ⟨h3, h4⟩
    have := Finset.min'_le _ c (Finset.mem_filter.2 ⟨hc, h3⟩)
    linarith
  · by_contra hy
    push_neg at hy
    have hbm : (X.filter (fun c => (X.filter (fun c => c ≤ y ∧ c < mx)).max' hne < c)).min' hne2
        < mx := lt_of_lt_of_le hy h2
    have := Finset.le_max' (X.filter (fun c => c ≤ y ∧ c < mx)) _
      (Finset.mem_filter.2 ⟨hb1, hy.le, hbm⟩)
    linarith

theorem exists_trap_decomp {E : Set E2} (hE : E.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (t s f0 f1 g0 g1 : ι → ℝ) (N : Set E2),
      IsPolygonal N ∧ volume N = 0 ∧ N ⊆ convexHull ℝ E ∧
      convexHull ℝ E = N ∪ ⋃ i, trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) ∧
      (∀ i, t i < s i ∧ f0 i + f1 i * t i ≤ g0 i + g1 i * t i ∧
        f0 i + f1 i * s i ≤ g0 i + g1 i * s i) ∧
      (∀ i, trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) ⊆ convexHull ℝ E) ∧
      (∀ i j, i ≠ j → volume (trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) ∩
        trap (t j) (s j) (f0 j) (f1 j) (g0 j) (g1 j)) = 0) := by
  classical
  obtain ⟨X, hX⟩ : ∃ X : Finset ℝ, ∀ c, c ∈ X ↔ ∃ e ∈ E, e 0 = c :=
    ⟨(hE.image (fun e : E2 => e 0)).toFinset, fun c => by simp⟩
  obtain ⟨G, hG⟩ : ∃ G : Finset (ℝ × ℝ), ∀ p, p ∈ G ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 < p.2 ∧
      ∀ c ∈ X, ¬(p.1 < c ∧ c < p.2) :=
    ⟨(X ×ˢ X).filter (fun p => p.1 < p.2 ∧ ∀ c ∈ X, ¬(p.1 < c ∧ c < p.2)),
      fun p => by simp [and_assoc]⟩
  have hdata : ∀ p : G, ∃ f0 f1 g0 g1 : ℝ, f0 + f1 * p.1.1 ≤ g0 + g1 * p.1.1 ∧
      f0 + f1 * p.1.2 ≤ g0 + g1 * p.1.2 ∧ convexHull ℝ E ∩ {x | p.1.1 ≤ x 0 ∧ x 0 ≤ p.1.2} =
        trap p.1.1 p.1.2 f0 f1 g0 g1 := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hG p).1 hp
    exact slab_trap hE h3 ((hX _).1 h1) ((hX _).1 h2) (fun e he h => h4 _ ((hX _).2 ⟨e, he, rfl⟩) h)
  choose f0 f1 g0 g1 hf0 hf1 hf using hdata
  have hK : IsCompact (convexHull ℝ E) := hE.isCompact_convexHull ℝ
  have hXE : ∀ e ∈ E, e 0 ∈ X := fun e he => (hX _).2 ⟨e, he, rfl⟩
  -- the cover
  have hcover : G.Nonempty → ∀ x ∈ convexHull ℝ E, ∃ p : G, x ∈ convexHull ℝ E ∩
      {x | p.1.1 ≤ x 0 ∧ x 0 ≤ p.1.2} := by
    rintro ⟨p0, hp0⟩ x hx
    obtain ⟨h1, h2, h3, h4⟩ := (hG p0).1 hp0
    have hXne : X.Nonempty := ⟨_, h1⟩
    have hmn : X.min' hXne ∈ X := Finset.min'_mem _ _
    have hmx : X.max' hXne ∈ X := Finset.max'_mem _ _
    have hlt : X.min' hXne < X.max' hXne :=
      lt_of_le_of_lt (Finset.min'_le _ _ h1) (lt_of_lt_of_le h3 (Finset.le_max' _ _ h2))
    have hxlo : X.min' hXne ≤ x 0 := by
      have : convexHull ℝ E ⊆ {y : E2 | X.min' hXne ≤ y 0} :=
        convexHull_min (fun e he => Finset.min'_le _ _ (hXE e he)) (convex_halfspace0' _)
      exact this hx
    have hxhi : x 0 ≤ X.max' hXne := by
      have : convexHull ℝ E ⊆ {y : E2 | y 0 ≤ X.max' hXne} :=
        convexHull_min (fun e he => Finset.le_max' _ _ (hXE e he)) (convex_halfspace0 _)
      exact this hx
    obtain ⟨a, ha, b, hb, hab, hgap, hax, hxb⟩ :=
      exists_gap X _ _ hmn hmx hlt hxlo hxhi (fun c hc => Finset.le_max' _ _ hc)
    exact ⟨⟨(a, b), (hG _).2 ⟨ha, hb, hab, hgap⟩⟩, hx, hax, hxb⟩
  have hnull : ¬ G.Nonempty → volume (convexHull ℝ E) = 0 := by
    intro hGe
    rcases E.eq_empty_or_nonempty with rfl | ⟨e0, he0⟩
    · simp
    have hXne : X.Nonempty := ⟨_, hXE e0 he0⟩
    have hmn : X.min' hXne ∈ X := Finset.min'_mem _ _
    have hmx : X.max' hXne ∈ X := Finset.max'_mem _ _
    have heq : X.min' hXne = X.max' hXne := by
      by_contra hne
      have hlt : X.min' hXne < X.max' hXne := lt_of_le_of_ne (Finset.min'_le _ _ hmx) hne
      obtain ⟨a, ha, b, hb, hab, hgap, -, -⟩ := exists_gap X _ _ hmn hmx hlt le_rfl hlt.le
        (fun c hc => Finset.le_max' _ _ hc)
      exact hGe ⟨(a, b), (hG _).2 ⟨ha, hb, hab, hgap⟩⟩
    refine measure_mono_null (t := {x : E2 | 1 * x 0 + 0 * x 1 = X.min' hXne}) ?_
      (volume_line_eq_zero _ (Or.inl one_ne_zero))
    intro x hx
    have h1 : X.min' hXne ≤ x 0 := (convexHull_min
      (fun e he => Finset.min'_le _ _ (hXE e he)) (convex_halfspace0' _)) hx
    have h2 : x 0 ≤ X.max' hXne := (convexHull_min
      (fun e he => Finset.le_max' _ _ (hXE e he)) (convex_halfspace0 _)) hx
    simp only [Set.mem_ofPred_eq]; linarith
  have hsubK : ∀ i : G, trap i.1.1 i.1.2 (f0 i) (f1 i) (g0 i) (g1 i) ⊆ convexHull ℝ E := by
    intro i; rw [← hf i]; exact Set.inter_subset_left
  have hdisj : ∀ p ∈ G, ∀ q ∈ G, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2, hp3, hp4⟩ := (hG p).1 hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := (hG q).1 hq
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · left; by_contra hlt; push_neg at hlt; exact hp4 q.1 hq1 ⟨h, hlt⟩
    · exfalso
      apply hpq
      refine Prod.ext h ?_
      rcases lt_trichotomy p.2 q.2 with h' | h' | h'
      · exact absurd ⟨by linarith, h'⟩ (hq4 p.2 hp2)
      · exact h'
      · exact absurd ⟨by linarith, h'⟩ (hp4 q.2 hq2)
    · right; by_contra hlt; push_neg at hlt; exact hq4 p.1 hp1 ⟨h, hlt⟩
  refine ⟨G, inferInstance, fun p => p.1.1, fun p => p.1.2, f0, f1, g0, g1,
    if G.Nonempty then ∅ else convexHull ℝ E, ?_, ?_, ?_, ?_, ?_, hsubK, ?_⟩
  · split_ifs
    · exact isPolygonal_empty
    · exact isPolygonal_convexHull_of_finite hE
  · split_ifs with h
    · simp
    · exact hnull h
  · split_ifs
    · exact Set.empty_subset _
    · exact subset_rfl
  · by_cases hGe : G.Nonempty
    · simp only [hGe, if_true, Set.empty_union]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨p, hp⟩ := hcover hGe x hx
        exact ⟨p, by rw [← hf p]; exact hp⟩
      · rintro ⟨i, hi⟩; exact hsubK i hi
    · simp only [hGe, if_false]
      exact (Set.union_eq_self_of_subset_right (Set.iUnion_subset hsubK)).symm
  · intro i
    obtain ⟨_, _, h3, _⟩ := (hG i.1).1 i.2
    exact ⟨h3, hf0 i, hf1 i⟩
  · intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rcases hdisj i.1 i.2 j.1 j.2 hne with h | h
    · refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := i.1.2) (Or.inl one_ne_zero) ?_
      rintro x ⟨⟨a1, a2, -, -⟩, ⟨b1, b2, -, -⟩⟩
      simp only; linarith
    · refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := j.1.2) (Or.inl one_ne_zero) ?_
      rintro x ⟨⟨a1, a2, -, -⟩, ⟨b1, b2, -, -⟩⟩
      simp only; linarith

/-! ### Cutting a polygonal set into convex cells -/

theorem isClosed_HSet (L : Set (ℝ × ℝ × ℝ)) : IsClosed (HSet L) := by
  have : HSet L = ⋂ p ∈ L, {x : E2 | p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2} := by
    ext x; simp [HSet]
  rw [this]
  exact isClosed_biInter fun p _ => isClosed_le (by fun_prop) continuous_const

/-- The reflected half-plane triple. -/
def negt (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (-p.1, -p.2.1, -p.2.2)

theorem mem_cell {Lf S : Finset (ℝ × ℝ × ℝ)} {x : E2} :
    x ∈ HSet (↑S ∪ negt '' (↑Lf \ ↑S)) ↔ (∀ p ∈ S, p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2) ∧
      ∀ q ∈ Lf, q ∉ S → q.2.2 ≤ q.1 * x 0 + q.2.1 * x 1 := by
  constructor
  · intro h
    refine ⟨fun p hp => h p (Or.inl hp), fun q hq hqS => ?_⟩
    have := h (negt q) (Or.inr ⟨q, ⟨hq, hqS⟩, rfl⟩)
    simp only [negt] at this
    linarith
  · rintro ⟨h1, h2⟩ p hp
    rcases hp with hp | ⟨q, ⟨hq, hqS⟩, rfl⟩
    · exact h1 p hp
    · have := h2 q hq hqS
      simp only [negt]
      linarith

theorem exists_cells {P : Set E2} (hP : IsPolygonal P) :
    ∃ (κ : Type) (_ : Fintype κ) (E : κ → Set E2), (∀ c, (E c).Finite) ∧
      P = ⋃ c, convexHull ℝ (E c) ∧
      ∀ c d, c ≠ d → volume (convexHull ℝ (E c) ∩ convexHull ℝ (E d)) = 0 := by
  classical
  obtain ⟨F, hF, hFe, rfl⟩ := hP
  have hPc : IsCompact (⋃₀ F) := hF.isCompact_sUnion fun T hT => (hFe T hT).isCompact
  choose! LT hLTfin hLTeq using fun T (hT : T ∈ F) => (hFe T hT).exists_HSet
  obtain ⟨Lf, hLf⟩ : ∃ Lf : Finset (ℝ × ℝ × ℝ), ∀ p, p ∈ Lf ↔
      (∃ T ∈ F, p ∈ LT T) ∧ (p.1 ≠ 0 ∨ p.2.1 ≠ 0) := by
    have hfin : {p : ℝ × ℝ × ℝ | (∃ T ∈ F, p ∈ LT T) ∧ (p.1 ≠ 0 ∨ p.2.1 ≠ 0)}.Finite := by
      refine (Set.Finite.biUnion hF fun T hT => hLTfin T hT).subset ?_
      rintro p ⟨⟨T, hT, hp⟩, -⟩
      exact Set.mem_biUnion hT hp
    exact ⟨hfin.toFinset, fun p => by simp⟩
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮 : Finset (Finset (ℝ × ℝ × ℝ)), ∀ S, S ∈ 𝒮 ↔ S ⊆ Lf ∧
      HSet (↑S ∪ negt '' (↑Lf \ ↑S)) ⊆ ⋃₀ F :=
    ⟨Lf.powerset.filter fun S => HSet (↑S ∪ negt '' (↑Lf \ ↑S)) ⊆ ⋃₀ F, fun S => by simp⟩
  have hcomp : ∀ S : 𝒮, IsCompact (HSet (↑S.1 ∪ negt '' (↑Lf \ ↑S.1))) := fun S =>
    IsCompact.of_isClosed_subset hPc (isClosed_HSet _) ((h𝒮 S.1).1 S.2).2
  have hfinL : ∀ S : 𝒮, (↑S.1 ∪ negt '' (↑Lf \ ↑S.1) : Set (ℝ × ℝ × ℝ)).Finite := fun S =>
    S.1.finite_toSet.union ((Lf.finite_toSet.subset Set.diff_subset).image _)
  have hEx : ∀ S : 𝒮, ∃ E : Set E2, E.Finite ∧
      HSet (↑S.1 ∪ negt '' (↑Lf \ ↑S.1)) = convexHull ℝ E := fun S =>
    HSet_eq_convexHull (hfinL S) (hcomp S)
  choose E hEfin hEeq using hEx
  refine ⟨𝒮, inferInstance, E, hEfin, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨T, hT, hxT⟩ := hx
      have hxT' := hxT
      rw [hLTeq T hT] at hxT'
      let Sx : Finset (ℝ × ℝ × ℝ) := Lf.filter fun p => p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2
      have hcell : HSet (↑Sx ∪ negt '' (↑Lf \ ↑Sx)) ⊆ T := by
        intro y hy
        obtain ⟨h1, h2⟩ := mem_cell.1 hy
        rw [hLTeq T hT]
        intro p hp
        by_cases hnd : p.1 ≠ 0 ∨ p.2.1 ≠ 0
        · have hpL : p ∈ Lf := (hLf p).2 ⟨⟨T, hT, hp⟩, hnd⟩
          exact h1 p (Finset.mem_filter.2 ⟨hpL, hxT' p hp⟩)
        · push_neg at hnd
          have := hxT' p hp
          rw [hnd.1, hnd.2] at this ⊢
          simpa using this
      have hS : Sx ∈ 𝒮 := (h𝒮 Sx).2 ⟨Finset.filter_subset _ _,
        hcell.trans (Set.subset_sUnion_of_mem hT)⟩
      refine ⟨⟨Sx, hS⟩, ?_⟩
      rw [← hEeq]
      refine mem_cell.2 ⟨fun p hp => (Finset.mem_filter.1 hp).2, fun q hq hqS => ?_⟩
      by_contra hlt
      exact hqS (Finset.mem_filter.2 ⟨hq, (not_le.1 hlt).le⟩)
    · rintro ⟨S, hS⟩
      rw [← hEeq] at hS
      exact ((h𝒮 S.1).1 S.2).2 hS
  · intro S S' hne
    rw [← hEeq, ← hEeq]
    have hne' : S.1 ≠ S'.1 := fun h => hne (Subtype.ext h)
    have hq : ∃ q, (q ∈ S.1 ∧ q ∉ S'.1) ∨ (q ∈ S'.1 ∧ q ∉ S.1) := by
      by_contra h
      apply hne'
      ext q
      constructor
      · intro h1; by_contra h2; exact h ⟨q, Or.inl ⟨h1, h2⟩⟩
      · intro h1; by_contra h2; exact h ⟨q, Or.inr ⟨h1, h2⟩⟩
    obtain ⟨q, hq⟩ := hq
    have hqL : q ∈ Lf := by
      rcases hq with hq | hq
      · exact ((h𝒮 S.1).1 S.2).1 hq.1
      · exact ((h𝒮 S'.1).1 S'.2).1 hq.1
    have hnd := ((hLf q).1 hqL).2
    refine volume_inter_eq_zero_of_line (α := q.1) (β := q.2.1) (γ := q.2.2) hnd ?_
    rintro z ⟨hz, hz'⟩
    obtain ⟨a1, a2⟩ := mem_cell.1 hz
    obtain ⟨b1, b2⟩ := mem_cell.1 hz'
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := a1 q h1
      have := b2 q hqL h2
      simp only; linarith
    · have := b1 q h1
      have := a2 q hqL h2
      simp only; linarith

theorem isPolygonal_iUnion {ι : Type} [Fintype ι] {S : ι → Set E2} (h : ∀ i, IsPolygonal (S i)) :
    IsPolygonal (⋃ i, S i) := by
  rw [← Set.sUnion_range]
  exact IsPolygonal.sUnion (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact h i)

/-- Every polygonal set is a null polygonal set together with finitely many trapezoids with
vertical parallel sides, any two of which overlap in a null set. -/
theorem exists_trap_cover {P : Set E2} (hP : IsPolygonal P) :
    ∃ (ι : Type) (_ : Fintype ι) (t s f0 f1 g0 g1 : ι → ℝ) (N : Set E2),
      IsPolygonal N ∧ volume N = 0 ∧
      P = N ∪ ⋃ i, trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) ∧
      (∀ i, t i < s i ∧ f0 i + f1 i * t i ≤ g0 i + g1 i * t i ∧
        f0 i + f1 i * s i ≤ g0 i + g1 i * s i) ∧
      (∀ i j, i ≠ j → volume (trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) ∩
        trap (t j) (s j) (f0 j) (f1 j) (g0 j) (g1 j)) = 0) := by
  obtain ⟨κ, _, E, hEfin, hPE, hnull⟩ := exists_cells hP
  choose ι inst t s f0 f1 g0 g1 N hNp hN0 hNsub hU hb hsub hdis using
    fun c => exists_trap_decomp (hEfin c)
  refine ⟨Σ c, ι c, inferInstance, fun p => t p.1 p.2, fun p => s p.1 p.2, fun p => f0 p.1 p.2,
    fun p => f1 p.1 p.2, fun p => g0 p.1 p.2, fun p => g1 p.1 p.2, ⋃ c, N c,
    isPolygonal_iUnion hNp, measure_iUnion_null hN0, ?_, fun p => hb _ _, ?_⟩
  · rw [hPE]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨c, hx⟩
      rw [hU c] at hx
      rcases hx with hx | hx
      · exact Or.inl ⟨c, hx⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        exact Or.inr ⟨⟨c, i⟩, hi⟩
    · rintro (⟨c, hx⟩ | ⟨⟨c, i⟩, hx⟩)
      · exact ⟨c, hNsub c hx⟩
      · exact ⟨c, hsub c i hx⟩
  · rintro ⟨c, i⟩ ⟨d, j⟩ hne
    by_cases hcd : c = d
    · subst hcd
      exact hdis c i j fun h => hne (by rw [h])
    · exact measure_mono_null (Set.inter_subset_inter (hsub c i) (hsub d j)) (hnull c d hcd)

theorem volume_trap_eq_zero {t s f0 f1 g0 g1 : ℝ} (ht : t < s)
    (hH : (g0 + g1 * t - (f0 + f1 * t)) + (g0 + g1 * s - (f0 + f1 * s)) = 0)
    (h0 : f0 + f1 * t ≤ g0 + g1 * t) (h1 : f0 + f1 * s ≤ g0 + g1 * s) :
    volume (trap t s f0 f1 g0 g1) = 0 := by
  refine measure_mono_null (t := {x : E2 | f1 * x 0 + (-1) * x 1 = -f0}) ?_
    (volume_line_eq_zero _ (Or.inr (by norm_num)))
  rintro x ⟨a1, a2, a3, a4⟩
  have e1 : g0 + g1 * t - (f0 + f1 * t) = 0 := by linarith
  have e2 : g0 + g1 * s - (f0 + f1 * s) = 0 := by linarith
  have key : ((g0 + g1 * x 0) - (f0 + f1 * x 0)) * (s - t) =
      (s - x 0) * (g0 + g1 * t - (f0 + f1 * t)) + (x 0 - t) * (g0 + g1 * s - (f0 + f1 * s)) := by
    ring
  rw [e1, e2, mul_zero, mul_zero, add_zero] at key
  have : (g0 + g1 * x 0) - (f0 + f1 * x 0) = 0 :=
    (mul_eq_zero.1 key).resolve_right (by linarith)
  simp only [Set.mem_ofPred_eq]; linarith

theorem volume_rect {W h : ℝ} (hW : 0 ≤ W) (hh : 0 ≤ h) :
    volume (rect W h) = ENNReal.ofReal W * ENNReal.ofReal h := by
  have : rect W h = (WithLp.ofLp ⁻¹' Set.pi Set.univ fun i : Fin 2 => Set.Icc (0 : ℝ) (![W, h] i)) := by
    ext x
    simp [rect, trap, Pi.le_def, Fin.forall_fin_two]
    tauto
  rw [this, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet]
  simp [Real.volume_Icc_pi, Fin.prod_univ_two]

theorem area_rect {W h : ℝ} (hW : 0 ≤ W) (hh : 0 ≤ h) : area (rect W h) = W * h := by
  unfold area
  rw [volume_rect hW hh, ENNReal.toReal_mul, ENNReal.toReal_ofReal hW, ENNReal.toReal_ofReal hh]

theorem dec_trap_rect' {t s f0 f1 g0 g1 H L : ℝ} (ht : t < s) (h0 : f0 + f1 * t ≤ g0 + g1 * t)
    (h1 : f0 + f1 * s ≤ g0 + g1 * s)
    (hH : H = (g0 + g1 * t - (f0 + f1 * t)) + (g0 + g1 * s - (f0 + f1 * s)))
    (hpos : 0 < H) (hL : H ≤ L) :
    Dec (trap t s f0 f1 g0 g1) (rect L (((s - t) / 2) * H / L)) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = 2 * m - t := ⟨(t + s) / 2, by ring⟩
  have := dec_trap_rect (by linarith : t < m) h0 h1 hH hpos hL
  have e : (2 * m - t - t) / 2 = m - t := by ring
  rwa [e]

/-! ### Stacking rectangles -/

theorem dec_stack {ι : Type} [Fintype ι] [Nonempty ι] {S : ι → Set E2} {b : ι → ℝ} {W : ℝ}
    (hW : 0 < W) (hb : ∀ i, 0 < b i) (hS : ∀ i, Dec (S i) (rect W (b i)))
    (hd : ∀ i j, i ≠ j → volume (S i ∩ S j) = 0) :
    Dec (⋃ i, S i) (rect W (∑ i, b i)) := by
  classical
  have key : ∀ s : Finset ι, s.Nonempty → Dec (⋃ i ∈ s, S i) (rect W (∑ i ∈ s, b i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h (by simp)
    | insert j s hj ih =>
      intro _
      by_cases hs : s.Nonempty
      · have ih' := ih hs
        obtain ⟨c, hc⟩ : ∃ c, c = ∑ i ∈ s, b i := ⟨_, rfl⟩
        rw [← hc] at ih'
        have hc0 : 0 < c := by rw [hc]; exact Finset.sum_pos (fun i _ => hb i) hs
        have hbj := hb j
        have eT : trap 0 W c 0 (c + b j) 0 = (fun x => x + !₂[0, c]) '' rect W (b j) := by
          ext x
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            exact ⟨x - !₂[0, c], ⟨by simpa using h1, by simpa using h2,
              by simp at h3 ⊢; linarith, by simp at h4 ⊢; linarith⟩, by simp⟩
          · rintro ⟨y, ⟨a1, a2, a3, a4⟩, rfl⟩
            exact ⟨by simpa using a1, by simpa using a2, by simp at a3 ⊢; linarith,
              by simp at a4 ⊢; linarith⟩
        have hsh : Dec (S j) (trap 0 W c 0 (c + b j) 0) := by
          refine (hS j).trans (Dec.of_congruent (isPolygonal_rect hW hbj.le)
            (isPolygonal_trap hW (by simp; linarith) (by simp; linarith)) ?_)
          rw [eT]; exact SetCongruent.vadd _ _
        have n1 : volume ((⋃ i ∈ s, S i) ∩ S j) = 0 := by
          rw [Set.iUnion₂_inter]
          exact (measure_biUnion_null_iff s.countable_toSet).2
            fun i hi => hd i j fun h => hj (h ▸ hi)
        have n2 : volume (rect W c ∩ trap 0 W c 0 (c + b j) 0) = 0 := by
          refine volume_inter_eq_zero_of_line (α := 0) (β := 1) (γ := c) (Or.inr one_ne_zero) ?_
          rintro x ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
          simp at a4 b3 ⊢; linarith
        have e1 : (⋃ i ∈ insert j s, S i) = (⋃ i ∈ s, S i) ∪ S j := by
          rw [Finset.set_biUnion_insert, Set.union_comm]
        have e2 : rect W c ∪ trap 0 W c 0 (c + b j) 0 = rect W (∑ i ∈ insert j s, b i) := by
          rw [Finset.sum_insert hj, ← hc, add_comm (b j) c]
          ext x
          simp only [rect, trap, Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · rintro (⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩)
            · exact ⟨a1, a2, a3, by linarith⟩
            · exact ⟨a1, a2, by linarith, by linarith⟩
          · rintro ⟨a1, a2, a3, a4⟩
            rcases le_total (x 1) c with h | h
            · exact Or.inl ⟨a1, a2, a3, by simpa using h⟩
            · exact Or.inr ⟨a1, a2, by simpa using h, by simpa using a4⟩
        rw [e1, ← e2]
        exact Dec.union ih' hsh n1 n2 |>.symm.symm
      · rw [Finset.not_nonempty_iff_eq_empty] at hs
        subst hs
        simpa using hS j
  simpa using key Finset.univ Finset.univ_nonempty

/-! ### Null pieces -/

theorem segment_congr (X Y : E2) :
    SetCongruent (segment ℝ X Y) (segment ℝ 0 !₂[dist X Y, 0]) := by
  by_cases hXY : X = Y
  · subst hXY
    refine ⟨IsometryEquiv.addRight (-X), ?_⟩
    have : (!₂[dist X X, 0] : E2) = 0 := by ext i; fin_cases i <;> simp
    rw [this, segment_same, segment_same]
    simp
  · have hℓ : 0 < dist X Y := dist_pos.2 hXY
    have hℓ2 : dist X Y ^ 2 = (Y 0 - X 0) ^ 2 + (Y 1 - X 1) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]; ring
    set ℓ := dist X Y with hℓdef
    obtain ⟨g, hg⟩ := motion_exists X (ℓ⁻¹ • (Y - X))
      !₂[-(ℓ⁻¹ • (Y - X)) 1, (ℓ⁻¹ • (Y - X)) 0]
      (by simp; field_simp; linarith) (by simp; field_simp; linarith) (by simp; ring)
    refine SetCongruent.symm ⟨g, ?_⟩
    have hgψ : (g : E2 → E2) = psi X (ℓ⁻¹ • (Y - X))
        !₂[-(ℓ⁻¹ • (Y - X)) 1, (ℓ⁻¹ • (Y - X)) 0] := funext hg
    rw [hgψ, image_segment]
    congr 1
    · simp
    · simp [smul_smul, hℓ.ne']

theorem dec_junk {J : Set E2} (hJ : IsDegeneratePolygonal J) {B W h : ℝ}
    (hB : ∀ x ∈ J, ∀ y ∈ J, dist x y ≤ B) (hBW : B ≤ W) (hh : 0 ≤ h) :
    ∃ J' : Set E2, J' ⊆ rect W h ∧ volume J' = 0 ∧ Dec J J' := by
  obtain ⟨F, hF, hFd, rfl⟩ := hJ
  haveI := hF.fintype
  have hseg : ∀ T : F, ∃ X Y : E2, T.1 = segment ℝ X Y := by
    intro T
    rcases hFd T.1 T.2 with ⟨A, hA⟩ | ⟨A, B, hAB⟩
    · exact ⟨A, A, by rw [hA, segment_same]⟩
    · exact ⟨A, B, hAB⟩
  choose X Y hXY using hseg
  have hmem : ∀ T : F, X T ∈ ⋃₀ F ∧ Y T ∈ ⋃₀ F := fun T =>
    ⟨Set.mem_sUnion.2 ⟨T.1, T.2, by rw [hXY T]; exact left_mem_segment ℝ _ _⟩,
      Set.mem_sUnion.2 ⟨T.1, T.2, by rw [hXY T]; exact right_mem_segment ℝ _ _⟩⟩
  have hpoly : ∀ T : F, IsPolygonal T.1 := fun T => (hFd T.1 T.2).isElementary.isPolygonal
  have hpolyS : ∀ T : F, IsPolygonal (segment ℝ 0 !₂[dist (X T) (Y T), 0]) := fun T =>
    (show IsElementary (segment ℝ (0 : E2) !₂[dist (X T) (Y T), 0]) from
      Or.inr (Or.inl ⟨_, _, rfl⟩)).isPolygonal
  refine ⟨⋃ T : F, segment ℝ 0 !₂[dist (X T) (Y T), 0], ?_, ?_, ?_⟩
  · refine Set.iUnion_subset fun T => ?_
    have hd : dist (X T) (Y T) ≤ W := (hB _ (hmem T).1 _ (hmem T).2).trans hBW
    have hd0 : 0 ≤ dist (X T) (Y T) := dist_nonneg
    rintro x ⟨a, b, ha, hb, hab, rfl⟩
    simp only [rect, trap, Set.mem_ofPred_eq]
    simp
    refine ⟨by positivity, by nlinarith, hh⟩
  · exact measure_iUnion_null fun T => measure_segment_eq_zero _ _
  · rw [Set.sUnion_eq_iUnion]
    refine Dec.iUnion (fun T => Dec.of_congruent (hpoly T) (hpolyS T) ?_) ?_ ?_
    · rw [hXY T]; exact segment_congr _ _
    · intro T T' _
      exact measure_mono_null Set.inter_subset_left (by rw [hXY T]; exact measure_segment_eq_zero _ _)
    · intro T T' _
      exact measure_mono_null Set.inter_subset_left (measure_segment_eq_zero _ _)

/-! ### Equidecomposability is an equivalence relation -/

theorem Equidecomposable.dec {P P' : Set E2} (h : Equidecomposable P P') : Dec P P' := by
  obtain ⟨n, Q, Q', h1, h2, hc⟩ := h
  exact ⟨Fin n, inferInstance, Q, Q', h1.1, h2.1, h1.2.1, h2.2.1,
    fun i j hij => volume_eq_zero_of_area_eq_zero ((h1.1 i).inter (h1.1 j))
      (h1.2.2 i j hij).area_eq_zero,
    fun i j hij => volume_eq_zero_of_area_eq_zero ((h2.1 i).inter (h2.1 j))
      (h2.2.2 i j hij).area_eq_zero, hc⟩

theorem Equidecomposable.symm {P P' : Set E2} (h : Equidecomposable P P') :
    Equidecomposable P' P := h.dec.symm.equidecomposable

/-- Equidecomposability is transitive (via common refinements of subdivisions). -/
theorem Equidecomposable.trans {P P' P'' : Set E2} (h : Equidecomposable P P')
    (h' : Equidecomposable P' P'') : Equidecomposable P P'' :=
  (h.dec.trans h'.dec).equidecomposable

/-! ### The theorem -/

theorem exists_dec_rect {P : Set E2} (hP : IsPolygonal P) (hpos : 0 < area P) :
    ∃ W0 : ℝ, 0 < W0 ∧ ∀ W, W0 ≤ W → Dec P (rect W (area P / W)) := by
  classical
  obtain ⟨ι, _, t, s, f0, f1, g0, g1, N, hNp, hN0, hPN, hb, hdis⟩ := exists_trap_cover hP
  obtain ⟨H, hHd⟩ : ∃ H : ι → ℝ, ∀ i, H i = (g0 i + g1 i * t i - (f0 i + f1 i * t i)) +
      (g0 i + g1 i * s i - (f0 i + f1 i * s i)) := ⟨_, fun _ => rfl⟩
  have hH0 : ∀ i, 0 ≤ H i := fun i => by
    have := hb i; rw [hHd]; linarith [this.2.1, this.2.2]
  obtain ⟨Z, hZd⟩ : ∃ Z : ι → Set E2, ∀ i, Z i = trap (t i) (s i) (f0 i) (f1 i) (g0 i) (g1 i) :=
    ⟨_, fun _ => rfl⟩
  have hZp : ∀ i, IsPolygonal (Z i) := fun i => by
    rw [hZd]; exact isPolygonal_trap (hb i).1 (hb i).2.1 (hb i).2.2
  have hPJ : P = (⋃ i : {i // 0 < H i}, Z i) ∪ (N ∪ ⋃ i : {i // ¬ 0 < H i}, Z i) := by
    rw [hPN]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, hZd]
    constructor
    · rintro (h | ⟨i, hi⟩)
      · exact Or.inr (Or.inl h)
      · by_cases hHi : 0 < H i
        · exact Or.inl ⟨⟨i, hHi⟩, hi⟩
        · exact Or.inr (Or.inr ⟨⟨i, hHi⟩, hi⟩)
    · rintro (⟨i, hi⟩ | h | ⟨i, hi⟩)
      · exact Or.inr ⟨i.1, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i.1, hi⟩
  have hZ0 : ∀ i : {i // ¬ 0 < H i}, volume (Z i.1) = 0 := fun i => by
    rw [hZd]
    exact volume_trap_eq_zero (hb i.1).1 (by rw [← hHd]; exact le_antisymm (not_lt.1 i.2) (hH0 _))
      (hb i.1).2.1 (hb i.1).2.2
  have hJp : IsPolygonal (N ∪ ⋃ i : {i // ¬ 0 < H i}, Z i) :=
    hNp.union (isPolygonal_iUnion fun i => hZp i.1)
  have hJ0 : volume (N ∪ ⋃ i : {i // ¬ 0 < H i}, Z i) = 0 :=
    measure_union_null hN0 (measure_iUnion_null hZ0)
  have hJd := hJp.degenerate_of_volume_eq_zero hJ0
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hJp.isBounded
  have hne : Nonempty {i // 0 < H i} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : volume P = 0 := by rw [hPJ, Set.iUnion_of_empty, Set.empty_union]; exact hJ0
    simp [area, this] at hpos
  have hsum : 0 ≤ ∑ i, H i := Finset.sum_nonneg fun i _ => hH0 i
  refine ⟨1 + ∑ i, H i + |C|, by linarith [abs_nonneg C], fun W hW => ?_⟩
  have hWpos : 0 < W := lt_of_lt_of_le (by linarith [abs_nonneg C]) hW
  have hHW : ∀ i, H i ≤ W := fun i => by
    have := Finset.single_le_sum (fun j _ => hH0 j) (Finset.mem_univ i)
    linarith [abs_nonneg C]
  obtain ⟨a, ha⟩ : ∃ a : ι → ℝ, ∀ i, a i = ((s i - t i) / 2) * H i := ⟨_, fun _ => rfl⟩
  have hapos : ∀ i : {i // 0 < H i}, 0 < a i.1 := fun i => by
    rw [ha]; exact mul_pos (by linarith [(hb i.1).1]) i.2
  have hstack := dec_stack (S := fun i : {i // 0 < H i} => Z i.1) (b := fun i => a i.1 / W) hWpos
    (fun i => div_pos (hapos i) hWpos)
    (fun i => by
      rw [hZd, ha]
      exact dec_trap_rect' (hb i.1).1 (hb i.1).2.1 (hb i.1).2.2 (hHd i.1) i.2 (hHW i.1))
    (fun i j hij => by
      rw [hZd, hZd]; exact hdis i.1 j.1 fun h => hij (Subtype.ext h))
  rw [← Finset.sum_div] at hstack
  obtain ⟨J', hJ'sub, hJ'0, hJ'⟩ := dec_junk hJd (B := |C|) (W := W) (h := (∑ i, a i.1) / W)
    (fun x hx y hy => (hC hx hy).trans (le_abs_self C)) (by linarith)
    (div_nonneg (Finset.sum_nonneg fun i _ => (hapos i).le) hWpos.le)
  have hdec : Dec P (rect W ((∑ i : {i // 0 < H i}, a i.1) / W)) := by
    rw [hPJ]
    have := Dec.union hstack hJ' (measure_mono_null Set.inter_subset_right hJ0)
      (measure_mono_null Set.inter_subset_right hJ'0)
    rwa [Set.union_eq_self_of_subset_right hJ'sub] at this
  have hareaP : area P = ∑ i : {i // 0 < H i}, a i.1 := by
    rw [hdec.equidecomposable.area_eq, area_rect hWpos.le
      (div_nonneg (Finset.sum_nonneg fun i _ => (hapos i).le) hWpos.le)]
    field_simp
  rw [hareaP]
  exact hdec

/-- **Wallace-Bolyai-Gerwien theorem** (the converse of `Equidecomposable.area_eq`): two polygonal
sets of equal positive area are equidecomposable.  The book states the remark without the
positivity assumption; it cannot be dropped for the book's definition, as a point and a segment have
equal area `0` but are not equidecomposable (every piece of a subdivision of a point is a point). -/
@[kb "petrunin2025" "Remark after Proposition 20.10, p. 170"]
theorem equidecomposable_of_area_eq {P P' : Set E2} (hP : IsPolygonal P) (hP' : IsPolygonal P')
    (hA : area P = area P') (hpos : 0 < area P) : Equidecomposable P P' := by
  obtain ⟨W0, hW0, hW⟩ := exists_dec_rect hP hpos
  obtain ⟨W0', hW0', hW'⟩ := exists_dec_rect hP' (hA ▸ hpos)
  have h1 := hW (max W0 W0') (le_max_left _ _)
  have h2 := hW' (max W0 W0') (le_max_right _ _)
  rw [← hA] at h2
  exact (h1.trans h2.symm).equidecomposable

end UndergradKB.Geometry
