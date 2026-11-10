import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Normed.Affine.MazurUlam
import UndergradKB.Geometry.Area
import UndergradKB.Common.Attr

/-! # Area, continued (Petrunin, chapter 20)

Section 20B (Claim 20.6, intersections of polygonal sets, rings of sets), Exercise 20.3 (vertices of
solid triangles), the easy half of the remark after Proposition 20.10 (equidecomposable sets have
equal area), the dissection proof of the Pythagorean theorem (Section 20H) and quadrable sets
(Section 20J). -/

namespace UndergradKB.Geometry

open MeasureTheory Filter Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ### Intersections of closed half-planes -/

/-- The intersection of finitely many closed half-planes `a x₀ + b x₁ ≤ c`, `(a, b, c) ∈ L`. -/
def HSet (L : Set (ℝ × ℝ × ℝ)) : Set E2 := {x | ∀ p ∈ L, p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2}

theorem HSet_inter (L M : Set (ℝ × ℝ × ℝ)) : HSet L ∩ HSet M = HSet (L ∪ M) := by
  ext x; simp only [HSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ p (hp | hp)
    exacts [h1 p hp, h2 p hp]
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩

theorem HSet_convex (L : Set (ℝ × ℝ × ℝ)) : Convex ℝ (HSet L) := by
  intro x hx y hy a b ha hb hab p hp
  have h1 := hx p hp
  have h2 := hy p hp
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have : p.1 * (a * x 0 + b * y 0) + p.2.1 * (a * x 1 + b * y 1) =
      a * (p.1 * x 0 + p.2.1 * x 1) + b * (p.1 * y 0 + p.2.1 * y 1) := by ring
  rw [this]
  have : p.2.2 = a * p.2.2 + b * p.2.2 := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- The corner point cut out by two half-plane boundaries. -/
noncomputable def corner (pq : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)) : E2 :=
  !₂[(pq.1.2.2 * pq.2.2.1 - pq.2.2.2 * pq.1.2.1) / (pq.1.1 * pq.2.2.1 - pq.2.1 * pq.1.2.1),
    (pq.1.1 * pq.2.2.2 - pq.2.1 * pq.1.2.2) / (pq.1.1 * pq.2.2.1 - pq.2.1 * pq.1.2.1)]

theorem extremePoints_HSet_subset {L : Set (ℝ × ℝ × ℝ)} (hL : L.Finite) :
    (HSet L).extremePoints ℝ ⊆ corner '' (L ×ˢ L) := by
  intro x hx
  have hxP : x ∈ HSet L := hx.1
  -- find two tight constraints with nonzero determinant
  by_cases hex : ∃ p ∈ L, ∃ q ∈ L, p.1 * x 0 + p.2.1 * x 1 = p.2.2 ∧
      q.1 * x 0 + q.2.1 * x 1 = q.2.2 ∧ p.1 * q.2.1 - q.1 * p.2.1 ≠ 0
  · obtain ⟨p, hp, q, hq, h1, h2, hd⟩ := hex
    refine ⟨(p, q), ⟨hp, hq⟩, ?_⟩
    unfold corner
    ext i
    fin_cases i
    · simp only [Fin.zero_eta]
      show (_ : ℝ) = x 0
      simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero]
      rw [div_eq_iff (by simpa using hd)]
      rw [← h1, ← h2]; ring
    · simp only [Fin.mk_one]
      show (_ : ℝ) = x 1
      simp
      rw [div_eq_iff (by simpa using hd)]
      rw [← h1, ← h2]; ring
  · exfalso
    push Not at hex
    -- a direction `v` along which all tight constraints are constant
    obtain ⟨v, hv0, hv⟩ : ∃ v : E2, v ≠ 0 ∧ ∀ p ∈ L, p.1 * x 0 + p.2.1 * x 1 = p.2.2 →
        p.1 * v 0 + p.2.1 * v 1 = 0 := by
      by_cases h : ∃ p ∈ L, p.1 * x 0 + p.2.1 * x 1 = p.2.2 ∧ (p.1 ≠ 0 ∨ p.2.1 ≠ 0)
      · obtain ⟨p, hp, hpt, hpn⟩ := h
        refine ⟨!₂[-p.2.1, p.1], ?_, ?_⟩
        · intro h0
          have a0 := congrArg (fun w : E2 => w 0) h0
          have a1 := congrArg (fun w : E2 => w 1) h0
          simp at a0 a1
          rcases hpn with h | h
          · exact h a1
          · exact h a0
        · intro q hq hqt
          have := hex p hp q hq hpt hqt
          simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
          linarith
      · push Not at h
        refine ⟨!₂[1, 0], ?_, ?_⟩
        · intro h0
          have a0 := congrArg (fun w : E2 => w 0) h0
          simp at a0
        · intro q hq hqt
          obtain ⟨h1, h2⟩ := h q hq hqt
          simp [h1, h2]
    have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p ∈ L, p.1 * (x 0 + t * v 0) + p.2.1 * (x 1 + t * v 1) ≤ p.2.2 := by
      refine (hL.eventually_all).2 fun p hp => ?_
      by_cases ht : p.1 * x 0 + p.2.1 * x 1 = p.2.2
      · have := hv p hp ht
        refine Eventually.of_forall fun t => ?_
        have : p.1 * (x 0 + t * v 0) + p.2.1 * (x 1 + t * v 1) =
            (p.1 * x 0 + p.2.1 * x 1) + t * (p.1 * v 0 + p.2.1 * v 1) := by ring
        rw [this, ‹p.1 * v 0 + p.2.1 * v 1 = 0›, ht]; simp
      · have hlt : p.1 * x 0 + p.2.1 * x 1 < p.2.2 := lt_of_le_of_ne (hxP p hp) ht
        have hc : Continuous (fun t : ℝ => p.1 * (x 0 + t * v 0) + p.2.1 * (x 1 + t * v 1)) := by
          fun_prop
        have := hc.continuousAt.eventually_lt (g := fun _ => p.2.2) (x₀ := 0) continuousAt_const
          (by simpa using hlt)
        exact this.mono fun t ht => ht.le
    have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p ∈ L,
        p.1 * (x 0 + (-t) * v 0) + p.2.1 * (x 1 + (-t) * v 1) ≤ p.2.2 := by
      have := (continuous_neg (G := ℝ)).tendsto 0
      rw [neg_zero] at this
      exact this.eventually hgood
    obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (((hgood.and hneg).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and
      self_mem_nhdsWithin).exists
    have ht0 : (0 : ℝ) < t := ht
    have hmem1 : x + t • v ∈ HSet L := by
      intro p hp; simpa using h1 p hp
    have hmem2 : x + (-t) • v ∈ HSet L := by
      intro p hp; simpa using h2 p hp
    have := (mem_extremePoints.1 hx).2 _ hmem1 _ hmem2 ?_
    · have h3 := this.1
      have : t • v = 0 := by simpa using h3
      rcases smul_eq_zero.1 this with h | h
      · exact ht0.ne' h
      · exact hv0 h
    · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring

theorem HSet_eq_convexHull {L : Set (ℝ × ℝ × ℝ)} (hL : L.Finite) (hc : IsCompact (HSet L)) :
    ∃ E : Set E2, E.Finite ∧ HSet L = convexHull ℝ E := by
  have hfin : ((HSet L).extremePoints ℝ).Finite :=
    ((hL.prod hL).image corner).subset (extremePoints_HSet_subset hL)
  refine ⟨_, hfin, ?_⟩
  have := closure_convexHull_extremePoints hc (HSet_convex L)
  exact this.symm.trans (hfin.isCompact_convexHull ℝ).isClosed.closure_eq


theorem E2_ext {x y : E2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i
  · exact h0
  · exact h1

/-- The half-plane `0 ≤ α x₀ + β x₁ + γ` as a triple for `HSet`. -/
def haf (α β γ : ℝ) : ℝ × ℝ × ℝ := (-α, -β, γ)

theorem mem_HSet_haf (α β γ : ℝ) (x : E2) :
    (∀ p ∈ ({haf α β γ} : Set (ℝ × ℝ × ℝ)), p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2) ↔
      0 ≤ α * x 0 + β * x 1 + γ := by
  simp only [Set.mem_singleton_iff, forall_eq, haf]
  constructor <;> intro h <;> linarith

theorem mem_HSet_insert (p : ℝ × ℝ × ℝ) (L : Set (ℝ × ℝ × ℝ)) (x : E2) :
    x ∈ HSet (insert p L) ↔ (p.1 * x 0 + p.2.1 * x 1 ≤ p.2.2) ∧ x ∈ HSet L := by
  simp [HSet]

/-! ### Elementary sets are intersections of half-planes -/

theorem segment_eq_HSet {A B : E2} (hAB : A ≠ B) : ∃ L : Set (ℝ × ℝ × ℝ), L.Finite ∧
    segment ℝ A B = HSet L := by
  have hd : B 0 - A 0 ≠ 0 ∨ B 1 - A 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hAB (E2_ext (by linarith [h.1]) (by linarith [h.2]))
  set d0 := B 0 - A 0 with hd0
  set d1 := B 1 - A 1 with hd1
  have hpos : 0 < d0 ^ 2 + d1 ^ 2 := by
    rcases hd with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  refine ⟨{(-d1, d0, -d1 * A 0 + d0 * A 1), (d1, -d0, d1 * A 0 - d0 * A 1),
    (d0, d1, d0 * B 0 + d1 * B 1), (-d0, -d1, -(d0 * A 0 + d1 * A 1))}, by simp, ?_⟩
  ext x
  simp only [HSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    have ha' : a = 1 - b := by linarith
    subst ha'
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have e0 : B 0 = A 0 + d0 := by rw [hd0]; ring
    have e1 : B 1 = A 1 + d1 := by rw [hd1]; ring
    rw [e0, e1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith [mul_nonneg ha (add_nonneg (sq_nonneg d0) (sq_nonneg d1))]
    · nlinarith [mul_nonneg hb (add_nonneg (sq_nonneg d0) (sq_nonneg d1))]
  · rintro ⟨h1, h2, h3, h4⟩
    set t := (d0 * (x 0 - A 0) + d1 * (x 1 - A 1)) / (d0 ^ 2 + d1 ^ 2) with ht
    have hn : -d1 * (x 0 - A 0) + d0 * (x 1 - A 1) = 0 := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hpos]; linarith
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    have hx0 : (d0 ^ 2 + d1 ^ 2) * (x 0 - A 0) = d0 * (d0 * (x 0 - A 0) + d1 * (x 1 - A 1)) := by
      linear_combination (-d1) * hn
    have hx1 : (d0 ^ 2 + d1 ^ 2) * (x 1 - A 1) = d1 * (d0 * (x 0 - A 0) + d1 * (x 1 - A 1)) := by
      linear_combination d0 * hn
    apply E2_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [ht]; field_simp
      nlinarith [hx0]
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [ht]; field_simp
      nlinarith [hx1]

theorem singleton_eq_HSet (A : E2) : ∃ L : Set (ℝ × ℝ × ℝ), L.Finite ∧ ({A} : Set E2) = HSet L := by
  refine ⟨{(1, 0, A 0), (-1, 0, -A 0), (0, 1, A 1), (0, -1, -A 1)}, by simp, ?_⟩
  ext x
  simp only [HSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2, h3, h4⟩
    exact E2_ext (by linarith) (by linarith)

theorem mem_solidTriangle_iff {A B C x : E2} : x ∈ solidTriangle A B C ↔
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ a • A + b • B + c • C = x := by
  unfold solidTriangle
  constructor
  · intro hx
    rw [convexHull_insert (Set.insert_nonempty _ _), convexHull_pair, mem_convexJoin] at hx
    obtain ⟨_, rfl, y, ⟨b, c, hb, hc, hbc, rfl⟩, a', a'', ha', ha'', ha, rfl⟩ := hx
    refine ⟨a', a'' * b, a'' * c, ha', by positivity, by positivity, ?_, ?_⟩
    · linear_combination ha + a'' * hbc
    · simp only [smul_add, smul_smul, add_assoc]
  · rintro ⟨a, b, c, ha, hb, hc, h, rfl⟩
    have := (convex_convexHull ℝ ({A, B, C} : Set E2)).sum_mem (t := Finset.univ) (w := ![a, b, c])
      (z := ![A, B, C]) (by intro i _; fin_cases i <;> simpa using ‹_›)
      (by simp [Fin.sum_univ_three, h]) (by
        intro i _; fin_cases i
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp)
        · exact subset_convexHull ℝ _ (by simp))
    simpa [Fin.sum_univ_three] using this

theorem solidTriangle_eq_HSet_of_det {A B C : E2}
    (hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) ≠ 0) :
    ∃ L : Set (ℝ × ℝ × ℝ), L.Finite ∧ solidTriangle A B C = HSet L := by
  set D := (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) with hDdef
  -- barycentric coordinates
  set lB : E2 → ℝ := fun x => ((x 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (x 1 - A 1)) / D with hlB
  set lC : E2 → ℝ := fun x => ((B 0 - A 0) * (x 1 - A 1) - (x 0 - A 0) * (B 1 - A 1)) / D with hlC
  refine ⟨{haf ((C 1 - A 1) / D) (-(C 0 - A 0) / D) ((-A 0 * (C 1 - A 1) + (C 0 - A 0) * A 1) / D),
    haf (-(B 1 - A 1) / D) ((B 0 - A 0) / D) ((-(B 0 - A 0) * A 1 + A 0 * (B 1 - A 1)) / D),
    haf (((B 1 - A 1) - (C 1 - A 1)) / D) (((C 0 - A 0) - (B 0 - A 0)) / D)
      (1 - (-A 0 * (C 1 - A 1) + (C 0 - A 0) * A 1) / D - (-(B 0 - A 0) * A 1 + A 0 * (B 1 - A 1)) / D)},
    by simp, ?_⟩
  ext x
  rw [mem_solidTriangle_iff]
  simp only [HSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, haf]
  have eB : ∀ x : E2, lB x = (C 1 - A 1) / D * x 0 + -(C 0 - A 0) / D * x 1 +
      (-A 0 * (C 1 - A 1) + (C 0 - A 0) * A 1) / D := by intro x; simp only [hlB]; ring
  have eC : ∀ x : E2, lC x = -(B 1 - A 1) / D * x 0 + (B 0 - A 0) / D * x 1 +
      (-(B 0 - A 0) * A 1 + A 0 * (B 1 - A 1)) / D := by intro x; simp only [hlC]; ring
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, h, rfl⟩
    have hb' : lB (a • A + b • B + c • C) = b := by
      simp only [hlB, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have : a = 1 - b - c := by linarith
      subst this
      field_simp; ring
    have hc' : lC (a • A + b • B + c • C) = c := by
      simp only [hlC, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have : a = 1 - b - c := by linarith
      subst this
      field_simp; ring
    rw [eB] at hb'
    rw [eC] at hc'
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hb' hc' ⊢
      simp only [div_eq_mul_inv] at hb' hc' ⊢
      have : a = 1 - b - c := by linarith
      subst this
      linarith
  · rintro ⟨h1, h2, h3⟩
    have hb : 0 ≤ lB x := by rw [eB]; linarith
    have hc : 0 ≤ lC x := by rw [eC]; linarith
    refine ⟨1 - lB x - lC x, lB x, lC x, ?_, hb, hc, by ring, ?_⟩
    · simp only [div_eq_mul_inv] at h3 eB eC ⊢
      rw [eB, eC]; linarith
    · apply E2_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hlB, hlC]
        field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hlB, hlC]
        field_simp; ring

theorem solidTriangle_eq_segment_of_subset {A B C X Y : E2} (h : ({A, B, C} : Set E2) ⊆ segment ℝ X Y)
    (hX : X ∈ ({A, B, C} : Set E2)) (hY : Y ∈ ({A, B, C} : Set E2)) :
    solidTriangle A B C = segment ℝ X Y := by
  unfold solidTriangle
  apply le_antisymm
  · exact convexHull_min h (convex_segment X Y)
  · rw [← convexHull_pair]
    exact convexHull_mono (by intro z hz; rcases hz with rfl | rfl <;> assumption)

theorem solidTriangle_eq_segment_of_det {A B C : E2}
    (hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) = 0) :
    ∃ X Y : E2, solidTriangle A B C = segment ℝ X Y := by
  by_cases hAB : A = B
  · subst hAB
    refine ⟨A, C, ?_⟩
    unfold solidTriangle
    rw [Set.insert_eq_of_mem (by simp), convexHull_pair]
  have hd : B 0 - A 0 ≠ 0 ∨ B 1 - A 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hAB (E2_ext (by linarith [h.1]) (by linarith [h.2])).symm
  have hpos : 0 < (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by
    rcases hd with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  set s : ℝ := ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1)) /
    ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2) with hs
  have hc0 : C 0 = A 0 + s * (B 0 - A 0) := by
    rw [hs]; field_simp
    linear_combination (-(B 1 - A 1)) * hD
  have hc1 : C 1 = A 1 + s * (B 1 - A 1) := by
    rw [hs]; field_simp
    linear_combination ((B 0 - A 0)) * hD
  have hA : A ∈ ({A, B, C} : Set E2) := by simp
  have hB : B ∈ ({A, B, C} : Set E2) := by simp
  have hC : C ∈ ({A, B, C} : Set E2) := by simp
  rcases lt_or_ge s 0 with h0 | h0
  · refine ⟨C, B, solidTriangle_eq_segment_of_subset ?_ hC hB⟩
    have hAm : A ∈ segment ℝ C B := by
      refine ⟨1 / (1 - s), -s / (1 - s), div_nonneg zero_le_one (by linarith), ?_, ?_, ?_⟩
      · have : 0 < 1 - s := by linarith
        exact div_nonneg (by linarith) this.le
      · have : 1 - s ≠ 0 := by linarith
        field_simp; ring
      · have : 1 - s ≠ 0 := by linarith
        apply E2_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hc0]; field_simp; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hc1]; field_simp; ring
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hAm
    · exact right_mem_segment _ _ _
    · exact left_mem_segment _ _ _
  rcases le_or_gt s 1 with h1 | h1
  · refine ⟨A, B, solidTriangle_eq_segment_of_subset ?_ hA hB⟩
    have hCm : C ∈ segment ℝ A B := by
      refine ⟨1 - s, s, by linarith, h0, by ring, ?_⟩
      apply E2_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hc0]; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [hc1]; ring
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
    · exact hCm
  · refine ⟨A, C, solidTriangle_eq_segment_of_subset ?_ hA hC⟩
    have hs0 : s ≠ 0 := by linarith
    have hBm : B ∈ segment ℝ A C := by
      refine ⟨1 - 1 / s, 1 / s, ?_, by positivity, by ring, ?_⟩
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · apply E2_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hc0]; field_simp; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hc1]; field_simp; ring
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact left_mem_segment _ _ _
    · exact hBm
    · exact right_mem_segment _ _ _

/-- Every elementary set is an intersection of finitely many closed half-planes. -/
theorem IsElementary.exists_HSet {S : Set E2} (h : IsElementary S) :
    ∃ L : Set (ℝ × ℝ × ℝ), L.Finite ∧ S = HSet L := by
  rcases h with ⟨A, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩
  · exact singleton_eq_HSet A
  · by_cases hAB : A = B
    · subst hAB; rw [segment_same]; exact singleton_eq_HSet A
    · exact segment_eq_HSet hAB
  · by_cases hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) = 0
    · obtain ⟨X, Y, hXY⟩ := solidTriangle_eq_segment_of_det hD
      rw [hXY]
      by_cases hXY' : X = Y
      · subst hXY'; rw [segment_same]; exact singleton_eq_HSet X
      · exact segment_eq_HSet hXY'
    · exact solidTriangle_eq_HSet_of_det hD

/-! ### Claim 20.6: intersections of polygonal sets -/

theorem IsElementary.isPolygonal {S : Set E2} (h : IsElementary S) : IsPolygonal S :=
  ⟨{S}, Set.finite_singleton _, by simpa using h, by simp⟩

theorem card_le_three_of_affineIndependent (t : Finset E2)
    (h : AffineIndependent ℝ ((↑) : t → E2)) : t.card ≤ 3 := by
  have h1 := h.card_le_finrank_succ
  have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E2)))
  rw [finrank_euclideanSpace_fin] at h2
  simp only [Fintype.card_coe] at h1
  omega

theorem isPolygonal_convexHull_finset (t : Finset E2) (ht : t.card ≤ 3) :
    IsPolygonal (convexHull ℝ (t : Set E2)) := by
  classical
  interval_cases hc : t.card
  · rw [Finset.card_eq_zero] at hc; subst hc; simpa using isPolygonal_empty
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
    exact IsElementary.isPolygonal (Or.inl ⟨a, by simp⟩)
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.1 hc
    exact IsElementary.isPolygonal (Or.inr (Or.inl ⟨a, b, by simp [convexHull_pair]⟩))
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.1 hc
    exact IsElementary.isPolygonal (Or.inr (Or.inr ⟨a, b, c, by simp [solidTriangle]⟩))

/-- The convex hull of a finite set of points of the plane is a polygonal set: by Carathéodory's
theorem it is the (finite) union of the solid triangles, segments and points spanned by at most
three of the points. -/
theorem isPolygonal_convexHull_of_finite {E : Set E2} (hE : E.Finite) :
    IsPolygonal (convexHull ℝ E) := by
  classical
  set 𝓕 : Set (Set E2) := (fun t : Finset E2 => convexHull ℝ (t : Set E2)) ''
    {t : Finset E2 | (t : Set E2) ⊆ E ∧ AffineIndependent ℝ ((↑) : t → E2)} with h𝓕
  have hfin : 𝓕.Finite := by
    refine Set.Finite.image _ ?_
    refine (hE.toFinset.powerset.finite_toSet).subset ?_
    intro t ht
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    intro y hy
    simpa using ht.1 hy
  have heq : convexHull ℝ E = ⋃₀ 𝓕 := by
    rw [convexHull_eq_union]
    ext x
    simp only [Set.mem_iUnion, exists_prop, Set.mem_sUnion, h𝓕, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, h1, h2, hx⟩
      exact ⟨_, ⟨t, ⟨h1, h2⟩, rfl⟩, hx⟩
    · rintro ⟨_, ⟨t, ⟨h1, h2⟩, rfl⟩, hx⟩
      exact ⟨t, h1, h2, hx⟩
  rw [heq]
  refine IsPolygonal.sUnion hfin ?_
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  exact isPolygonal_convexHull_finset t (card_le_three_of_affineIndependent t h2)

/-- The intersection of two elementary sets is polygonal (it is a compact intersection of
half-planes, hence the convex hull of finitely many points). -/
theorem IsElementary.inter_isPolygonal {S T : Set E2} (hS : IsElementary S) (hT : IsElementary T) :
    IsPolygonal (S ∩ T) := by
  have hc : IsCompact (S ∩ T) := hS.isCompact.inter_right hT.isCompact.isClosed
  obtain ⟨L, hL, hSL⟩ := hS.exists_HSet
  obtain ⟨M, hM, hTM⟩ := hT.exists_HSet
  have hST : S ∩ T = HSet (L ∪ M) := by rw [hSL, hTM, HSet_inter]
  rw [hST] at hc ⊢
  obtain ⟨E, hE, hEq⟩ := HSet_eq_convexHull (hL.union hM) hc
  rw [hEq]
  exact isPolygonal_convexHull_of_finite hE

/-- Claim 20.6, intersection part: the intersection of two polygonal sets is polygonal. -/
@[kb "petrunin2025" "Claim 20.6, p. 167"]
theorem IsPolygonal.inter {S T : Set E2} (hS : IsPolygonal S) (hT : IsPolygonal T) :
    IsPolygonal (S ∩ T) := by
  obtain ⟨F, hF, hFe, rfl⟩ := hS
  obtain ⟨G, hG, hGe, rfl⟩ := hT
  have : ⋃₀ F ∩ ⋃₀ G = ⋃₀ ((fun p : Set E2 × Set E2 => p.1 ∩ p.2) '' (F ×ˢ G)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨⟨A, hA, hxA⟩, B, hB, hxB⟩
      exact ⟨A ∩ B, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hxB⟩
    · rintro ⟨_, ⟨A, B, ⟨hA, hB⟩, rfl⟩, hxA, hxB⟩
      exact ⟨⟨A, hA, hxA⟩, B, hB, hxB⟩
  rw [this]
  refine IsPolygonal.sUnion ((hF.prod hG).image _) ?_
  rintro _ ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩
  exact (hFe A hA).inter_isPolygonal (hGe B hB)

/-! ### Rings of sets -/

/-- A ring of sets in the book's sense: a class of sets closed under union and intersection. -/
@[kb "petrunin2025" "Claim 20.6, p. 167"]
def IsRingOfSets {α : Type*} (𝓡 : Set (Set α)) : Prop :=
  (∀ S ∈ 𝓡, ∀ T ∈ 𝓡, S ∪ T ∈ 𝓡) ∧ ∀ S ∈ 𝓡, ∀ T ∈ 𝓡, S ∩ T ∈ 𝓡

/-- Mathlib's `IsSetRing` (empty set, unions, differences) gives a ring of sets in the book's sense. -/
theorem IsRingOfSets.of_isSetRing {α : Type*} {𝓡 : Set (Set α)} (h : MeasureTheory.IsSetRing 𝓡) :
    IsRingOfSets 𝓡 :=
  ⟨fun _ hS _ hT => h.union_mem hS hT, fun _ hS _ hT => h.inter_mem hS hT⟩

/-- Definition after Claim 20.6 and Claim 20.6: the polygonal sets of the plane form a ring of
sets. -/
@[kb "petrunin2025" "Claim 20.6, p. 167"]
theorem isRingOfSets_isPolygonal : IsRingOfSets {S : Set E2 | IsPolygonal S} :=
  ⟨fun _ hS _ hT => hS.union hT, fun _ hS _ hT => hS.inter hT⟩

theorem not_isClosed_segment_diff : ¬ IsClosed (segment ℝ (0 : E2) !₂[1, 0] \ {0}) := by
  intro hcl
  let g : ℝ → E2 := fun t => !₂[t, 0]
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hpre : g ⁻¹' (segment ℝ (0 : E2) !₂[1, 0] \ {0}) = Set.Ioc 0 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨a, b, ha, hb, hab, h⟩, hne⟩
      have h0 := congrArg (fun w : E2 => w 0) h
      simp [g] at h0
      refine ⟨?_, ?_⟩
      · rcases hb.lt_or_eq with h1 | h1
        · rw [← h0]; exact h1
        · exfalso; apply hne; ext i; fin_cases i <;> simp [g, ← h0, ← h1]
      · rw [← h0]; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨1 - t, t, by linarith, h1.le, by ring, ?_⟩, ?_⟩
      · ext i; fin_cases i <;> simp [g]
      · intro h
        have := congrArg (fun w : E2 => w 0) h
        simp [g] at this
        linarith
  have := hcl.preimage hg
  rw [hpre] at this
  have h2 : closure (Set.Ioc (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioc (by norm_num)
  rw [this.closure_eq] at h2
  have : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by simp
  rw [← h2] at this
  simp at this

/-- The polygonal sets do not form a set ring in Mathlib's sense: they are not closed under set
difference (a segment minus an endpoint is not closed, so not polygonal).  They are a ring of sets
only in the book's weaker sense, `isRingOfSets_isPolygonal`. -/
@[kb "petrunin2025" "Claim 20.6, p. 167"]
theorem not_isSetRing_isPolygonal : ¬ MeasureTheory.IsSetRing {S : Set E2 | IsPolygonal S} := by
  intro h
  have h1 : IsPolygonal (segment ℝ (0 : E2) !₂[1, 0]) :=
    IsElementary.isPolygonal (Or.inr (Or.inl ⟨_, _, rfl⟩))
  have h2 : IsPolygonal ({0} : Set E2) := IsElementary.isPolygonal (Or.inl ⟨_, rfl⟩)
  exact not_isClosed_segment_diff (h.sdiff_mem h1 h2).isCompact.isClosed

/-! ### Exercise 20.3: vertices of solid triangles -/

theorem det_ne_zero_of_affineIndependent {A B C : E2} (h : AffineIndependent ℝ ![A, B, C]) :
    (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) ≠ 0 := by
  intro hD
  rw [affineIndependent_iff_not_collinear_set] at h
  apply h
  by_cases hAB : A = B
  · subst hAB
    simp [collinear_pair]
  have hd : B 0 - A 0 ≠ 0 ∨ B 1 - A 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hAB (E2_ext (by linarith [h.1]) (by linarith [h.2]))
  have hpos : 0 < (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by
    rcases hd with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  set s : ℝ := ((B 0 - A 0) * (C 0 - A 0) + (B 1 - A 1) * (C 1 - A 1)) /
    ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2) with hs
  have hc0 : C 0 = A 0 + s * (B 0 - A 0) := by
    rw [hs]; field_simp
    linear_combination (-(B 1 - A 1)) * hD
  have hc1 : C 1 = A 1 + s * (B 1 - A 1) := by
    rw [hs]; field_simp
    linear_combination ((B 0 - A 0)) * hD
  have hC : C ∈ line[ℝ, A, B] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨s, E2_ext ?_ ?_⟩
    · simp [AffineMap.lineMap_apply, hc0]; ring
    · simp [AffineMap.lineMap_apply, hc1]; ring
  have := collinear_insert_of_mem_affineSpan_pair hC
  have e : ({C, A, B} : Set E2) = {A, B, C} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rwa [e] at this

theorem exists_pos_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℝ), P t) : ∃ t, 0 < t ∧ P t := by
  obtain ⟨t, h1, h2⟩ := ((h.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).and
    self_mem_nhdsWithin).exists
  exact ⟨t, h2, h1⟩

theorem exists_neg_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℝ), P t) : ∃ t, t < 0 ∧ P t := by
  obtain ⟨t, h1, h2⟩ := ((h.filter_mono (nhdsWithin_le_nhds (s := Set.Iio (0:ℝ)))).and
    self_mem_nhdsWithin).exists
  exact ⟨t, h2, h1⟩

theorem exists_small_step {a b c p q r : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    ∃ s : ℝ, s ≠ 0 ∧ 0 ≤ a + s * p ∧ 0 ≤ b + s * q ∧ 0 ≤ c + s * r := by
  have hbc : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b + t * q ∧ 0 < c + t * r := by
    have h1 : Continuous (fun t : ℝ => b + t * q) := by fun_prop
    have h2 : Continuous (fun t : ℝ => c + t * r) := by fun_prop
    exact ((h1.tendsto 0).eventually (lt_mem_nhds (by simpa using hb))).and
      ((h2.tendsto 0).eventually (lt_mem_nhds (by simpa using hc)))
  rcases ha.lt_or_eq with ha' | ha'
  · have h0 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < a + t * p := by
      have h1 : Continuous (fun t : ℝ => a + t * p) := by fun_prop
      exact (h1.tendsto 0).eventually (lt_mem_nhds (by simpa using ha'))
    obtain ⟨t, ht, h⟩ := exists_pos_of_eventually (hbc.and h0)
    exact ⟨t, ht.ne', h.2.le, h.1.1.le, h.1.2.le⟩
  · subst ha'
    rcases le_or_gt 0 p with hp | hp
    · obtain ⟨t, ht, h⟩ := exists_pos_of_eventually hbc
      exact ⟨t, ht.ne', by simpa using mul_nonneg ht.le hp, h.1.le, h.2.le⟩
    · obtain ⟨t, ht, h⟩ := exists_neg_of_eventually hbc
      exact ⟨t, ht.ne, by simpa using mul_nonneg_of_nonpos_of_nonpos ht.le hp.le, h.1.le, h.2.le⟩

theorem exists_small_step' {a b c p q r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : ¬ (a = 0 ∧ b = 0)) (hac : ¬ (a = 0 ∧ c = 0)) (hbc : ¬ (b = 0 ∧ c = 0)) :
    ∃ s : ℝ, s ≠ 0 ∧ 0 ≤ a + s * p ∧ 0 ≤ b + s * q ∧ 0 ≤ c + s * r := by
  have ha0 : a = 0 → 0 < b ∧ 0 < c := fun h =>
    ⟨lt_of_le_of_ne hb fun e => hab ⟨h, e.symm⟩, lt_of_le_of_ne hc fun e => hac ⟨h, e.symm⟩⟩
  by_cases h1 : 0 < a
  · by_cases h2 : 0 < b
    · obtain ⟨s, hs, h3, h4, h5⟩ := exists_small_step (a := c) (b := a) (c := b) (p := r) (q := p)
        (r := q) hc h1 h2
      exact ⟨s, hs, h4, h5, h3⟩
    · have hb0 : b = 0 := le_antisymm (not_lt.1 h2) hb
      have hc' : 0 < c := lt_of_le_of_ne hc fun e => hbc ⟨hb0, e.symm⟩
      obtain ⟨s, hs, h3, h4, h5⟩ := exists_small_step (a := b) (b := a) (c := c) (p := q) (q := p)
        (r := r) hb h1 hc'
      exact ⟨s, hs, h4, h3, h5⟩
  · have ha0' : a = 0 := le_antisymm (not_lt.1 h1) ha
    obtain ⟨hb', hc'⟩ := ha0 ha0'
    exact exists_small_step ha hb' hc'

/-- Through a vertex `A` of a nondegenerate triangle, the parallel to the opposite side meets the
solid triangle only at `A`. -/
theorem exists_line_inter_eq_vertex {A B C : E2}
    (hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) ≠ 0) :
    ∃ P Q : E2, P ≠ Q ∧ (line[ℝ, P, Q] : Set E2) ∩ solidTriangle A B C = {A} := by
  refine ⟨A, A + (C - B), ?_, ?_⟩
  · intro h
    have h' : C - B = 0 := by simpa using h.symm
    apply hD
    have h0 : C 0 = B 0 := by
      have := congrArg (fun w : E2 => w 0) h'; simp at this; linarith
    have h1 : C 1 = B 1 := by
      have := congrArg (fun w : E2 => w 1) h'; simp at this; linarith
    rw [h0, h1]; ring
  · ext x
    constructor
    · rintro ⟨hl, ht⟩
      rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hl
      obtain ⟨r, rfl⟩ := hl
      rw [mem_solidTriangle_iff] at ht
      obtain ⟨a, b, c, ha, hb, hc, hs, he⟩ := ht
      obtain rfl : a = 1 - b - c := by linarith
      have e0 := congrArg (fun w : E2 => w 0) he
      have e1 := congrArg (fun w : E2 => w 1) he
      simp only [AffineMap.lineMap_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        vsub_eq_sub, vadd_eq_add, PiLp.sub_apply] at e0 e1
      have k0 : (b + r) * (B 0 - A 0) + (c - r) * (C 0 - A 0) = 0 := by linear_combination e0
      have k1 : (b + r) * (B 1 - A 1) + (c - r) * (C 1 - A 1) = 0 := by linear_combination e1
      have hb' : (b + r) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (C 1 - A 1) * k0 - (C 0 - A 0) * k1
      have hc' : (c - r) * ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) = 0 := by
        linear_combination (B 0 - A 0) * k1 - (B 1 - A 1) * k0
      have h1 := (mul_eq_zero.1 hb').resolve_right hD
      have h2 := (mul_eq_zero.1 hc').resolve_right hD
      have hr : r = 0 := by linarith
      subst hr
      simp
    · rintro rfl
      exact ⟨left_mem_affineSpan_pair _ _ _, subset_convexHull ℝ _ (by simp)⟩

/-- Through a point of a nondegenerate solid triangle that is not a vertex, every line meets the
solid triangle in a second point. -/
theorem exists_ne_mem_line_inter {A B C X P Q : E2}
    (hD : (B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1) ≠ 0)
    (hX : X ∈ solidTriangle A B C) (hXA : X ≠ A) (hXB : X ≠ B) (hXC : X ≠ C) (hPQ : P ≠ Q)
    (hXl : X ∈ line[ℝ, P, Q]) :
    ∃ y, y ∈ (line[ℝ, P, Q] : Set E2) ∧ y ∈ solidTriangle A B C ∧ y ≠ X := by
  obtain ⟨a, b, c, ha, hb, hc, hs, rfl⟩ := mem_solidTriangle_iff.1 hX
  have hbc : ¬ (b = 0 ∧ c = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hXA
    obtain rfl : a = 1 := by linarith
    simp
  have hac : ¬ (a = 0 ∧ c = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hXB
    obtain rfl : b = 1 := by linarith
    simp
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hXC
    obtain rfl : c = 1 := by linarith
    simp
  set u : ℝ := B 0 - A 0 with hu
  set w : ℝ := B 1 - A 1 with hw
  set u' : ℝ := C 0 - A 0 with hu'
  set w' : ℝ := C 1 - A 1 with hw'
  set D : ℝ := u * w' - u' * w with hDdef
  set m : ℝ := (Q - P) 0 with hm
  set n : ℝ := (Q - P) 1 with hn
  set p : ℝ := (m * w' - u' * n) / D with hp
  set q : ℝ := (u * n - w * m) / D with hq
  have hpq0 : p * u + q * u' = m := by
    rw [hp, hq]; field_simp; ring
  have hpq1 : p * w + q * w' = n := by
    rw [hp, hq]; field_simp; ring
  obtain ⟨s, hs0, h1, h2, h3⟩ := exists_small_step' (p := -(p + q)) (q := p) (r := q) ha hb hc
    hab hac hbc
  have hu0 : Q - P ≠ 0 := sub_ne_zero.2 hPQ.symm
  refine ⟨s • (Q - P) + (a • A + b • B + c • C), ?_, ?_, ?_⟩
  · have hdir : Q - P ∈ (line[ℝ, P, Q]).direction := by
      rw [direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ (by simp) (by simp)
    have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ s hdir) hXl
    simpa using this
  · rw [mem_solidTriangle_iff]
    refine ⟨a + s * -(p + q), b + s * p, c + s * q, h1, h2, h3, by linarith, ?_⟩
    apply E2_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      change _ = s * m + _
      linear_combination s * hpq0
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      change _ = s * n + _
      linear_combination s * hpq1
  · intro h
    have : s • (Q - P) = 0 := by simpa using h
    rcases smul_eq_zero.1 this with h | h
    exacts [hs0 h, hu0 h]

theorem solidTriangle_cyc (A B C : E2) : solidTriangle B C A = solidTriangle A B C := by
  unfold solidTriangle
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem affineIndependent_points_eq (t : Affine.Triangle ℝ E2) :
    AffineIndependent ℝ ![t.points 0, t.points 1, t.points 2] := by
  have : ![t.points 0, t.points 1, t.points 2] = t.points := by
    ext i : 1
    fin_cases i <;> rfl
  rw [this]
  exact t.independent

/-- Exercise 20.3: a point of the solid triangle of a nondegenerate triangle is a vertex if and
only if some line meets the solid triangle exactly in that point. -/
@[kb "petrunin2025" "Exercise 20.3, p. 166"]
theorem isVertex_iff_exists_line (t : Affine.Triangle ℝ E2) {X : E2}
    (hX : X ∈ solidTriangle (t.points 0) (t.points 1) (t.points 2)) :
    (∃ i, X = t.points i) ↔ ∃ P Q : E2, P ≠ Q ∧
      (line[ℝ, P, Q] : Set E2) ∩ solidTriangle (t.points 0) (t.points 1) (t.points 2) = {X} := by
  have hD := det_ne_zero_of_affineIndependent (affineIndependent_points_eq t)
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact exists_line_inter_eq_vertex hD
    · have hD' : (t.points 2 0 - t.points 1 0) * (t.points 0 1 - t.points 1 1) -
          (t.points 0 0 - t.points 1 0) * (t.points 2 1 - t.points 1 1) ≠ 0 := by
        intro h; apply hD; linear_combination h
      have := exists_line_inter_eq_vertex hD'
      rwa [solidTriangle_cyc] at this
    · have hD' : (t.points 0 0 - t.points 2 0) * (t.points 1 1 - t.points 2 1) -
          (t.points 1 0 - t.points 2 0) * (t.points 0 1 - t.points 2 1) ≠ 0 := by
        intro h; apply hD; linear_combination h
      have := exists_line_inter_eq_vertex hD'
      rw [solidTriangle_cyc, solidTriangle_cyc] at this
      exact this
  · rintro ⟨P, Q, hPQ, hl⟩
    by_contra hne
    push Not at hne
    have hXl : X ∈ line[ℝ, P, Q] := by
      have : X ∈ (line[ℝ, P, Q] : Set E2) ∩
          solidTriangle (t.points 0) (t.points 1) (t.points 2) := by rw [hl]; rfl
      exact this.1
    obtain ⟨y, hy1, hy2, hy3⟩ := exists_ne_mem_line_inter hD hX (hne 0) (hne 1) (hne 2) hPQ hXl
    have : y ∈ (line[ℝ, P, Q] : Set E2) ∩ solidTriangle (t.points 0) (t.points 1) (t.points 2) :=
      ⟨hy1, hy2⟩
    rw [hl] at this
    exact hy3 this

/-- Exercise 20.3, consequence stated in the book: if a motion maps the solid triangle of a
nondegenerate triangle onto the solid triangle of another one, it maps vertices to vertices. -/
@[kb "petrunin2025" "Exercise 20.3, p. 166"]
theorem isometryEquiv_vertices (t t' : Affine.Triangle ℝ E2) (f : E2 ≃ᵢ E2)
    (h : f '' solidTriangle (t.points 0) (t.points 1) (t.points 2) =
      solidTriangle (t'.points 0) (t'.points 1) (t'.points 2)) (i : Fin 3) :
    ∃ j, f (t.points i) = t'.points j := by
  have hmem : t.points i ∈ solidTriangle (t.points 0) (t.points 1) (t.points 2) :=
    subset_convexHull ℝ _ (by fin_cases i <;> simp)
  obtain ⟨P, Q, hPQ, hl⟩ := (isVertex_iff_exists_line t hmem).1 ⟨i, rfl⟩
  have hmem' : f (t.points i) ∈ solidTriangle (t'.points 0) (t'.points 1) (t'.points 2) := by
    rw [← h]; exact ⟨_, hmem, rfl⟩
  refine (isVertex_iff_exists_line t' hmem').2 ?_
  refine ⟨f P, f Q, fun e => hPQ (f.injective e), ?_⟩
  let g : E2 →ᵃ[ℝ] E2 := f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
  have hg : ∀ x, g x = f x := fun x => by
    show f.toRealAffineIsometryEquiv x = f x
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv]
  have hline : (line[ℝ, f P, f Q] : Set E2) = f '' (line[ℝ, P, Q] : Set E2) := by
    have h1 := AffineSubspace.map_span (k := ℝ) g {P, Q}
    rw [Set.image_pair, hg, hg] at h1
    rw [← h1, AffineSubspace.coe_map]
    ext x; simp [hg]
  rw [hline, ← h, ← Set.image_inter f.injective, hl, Set.image_singleton]

/-! ### Subdivisions and equidecomposability -/

/-- A subdivision of `P` into the polygonal sets `Q 0, …, Q (n-1)` (Section 20D): `P` is their
union and any two different pieces meet in a degenerate polygonal set. -/
@[kb "petrunin2025" "Section 20D, p. 169"]
def IsSubdivision {n : ℕ} (P : Set E2) (Q : Fin n → Set E2) : Prop :=
  (∀ i, IsPolygonal (Q i)) ∧ P = ⋃ i, Q i ∧ ∀ i j, i ≠ j → IsDegeneratePolygonal (Q i ∩ Q j)

theorem volume_eq_zero_of_area_eq_zero {S : Set E2} (hS : IsPolygonal S) (h : area S = 0) :
    volume S = 0 := by
  unfold area at h
  rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
  · exact h
  · exact absurd h hS.measure_lt_top.ne

/-- Proposition 20.10: the area of a set subdivided into polygonal sets is the sum of the areas of
the pieces. -/
@[kb "petrunin2025" "Proposition 20.10, p. 169"]
theorem IsSubdivision.area_eq_sum {n : ℕ} {P : Set E2} {Q : Fin n → Set E2}
    (h : IsSubdivision P Q) : area P = ∑ i, area (Q i) := by
  obtain ⟨hQ, rfl, hd⟩ := h
  unfold area
  have h1 : volume (⋃ i, Q i) = ∑ i, volume (Q i) := by
    have := measure_biUnion_finset₀ (μ := volume) (s := (Finset.univ : Finset (Fin n)))
      (f := Q) (fun i _ j _ hij => by
        have := volume_eq_zero_of_area_eq_zero
          ((hQ i).inter (hQ j)) (hd i j hij).area_eq_zero
        exact this) (fun i _ => (hQ i).measurableSet.nullMeasurableSet)
    simpa using this
  rw [h1, ENNReal.toReal_sum (fun i _ => (hQ i).measure_lt_top.ne)]

/-- Two polygonal sets are equidecomposable if they admit subdivisions into polygonal sets with
pieces pairwise congruent (Remark after Proposition 20.10). -/
@[kb "petrunin2025" "Remark after Proposition 20.10, p. 170"]
def Equidecomposable (P P' : Set E2) : Prop :=
  ∃ (n : ℕ) (Q Q' : Fin n → Set E2), IsSubdivision P Q ∧ IsSubdivision P' Q' ∧
    ∀ i, SetCongruent (Q i) (Q' i)

/-- Remark after Proposition 20.10 (the easy direction): equidecomposable polygonal sets have equal
area.  The converse (Wallace-Bolyai-Gerwien) is not formalized. -/
@[kb "petrunin2025" "Remark after Proposition 20.10, p. 170"]
theorem Equidecomposable.area_eq {P P' : Set E2} (h : Equidecomposable P P') : area P = area P' := by
  obtain ⟨n, Q, Q', h1, h2, hc⟩ := h
  rw [h1.area_eq_sum, h2.area_eq_sum]
  exact Finset.sum_congr rfl fun i _ => (hc i).area_eq

theorem Equidecomposable.refl {P : Set E2} (hP : IsPolygonal P) : Equidecomposable P P :=
  ⟨1, fun _ => P, fun _ => P,
    ⟨fun _ => hP, (Set.iUnion_const P).symm, fun i j hij => absurd (Subsingleton.elim i j) hij⟩,
    ⟨fun _ => hP, (Set.iUnion_const P).symm, fun i j hij => absurd (Subsingleton.elim i j) hij⟩,
    fun _ => SetCongruent.refl _⟩

/-! ### Section 20J: quadrable sets -/

/-- Quadrable sets (Section 20J): for every `ε > 0` there are polygonal sets `P ⊆ S ⊆ Q` with
`area Q - area P < ε`. -/
@[kb "petrunin2025" "Section 20J, p. 177"]
def IsQuadrable (S : Set E2) : Prop :=
  ∀ ε > 0, ∃ P Q : Set E2, IsPolygonal P ∧ IsPolygonal Q ∧ P ⊆ S ∧ S ⊆ Q ∧ area Q - area P < ε

/-- The inner area: the supremum of the areas of polygonal subsets. -/
noncomputable def innerArea (S : Set E2) : ℝ := sSup {r | ∃ P, IsPolygonal P ∧ P ⊆ S ∧ r = area P}

/-- The outer area: the infimum of the areas of polygonal supersets. -/
noncomputable def outerArea (S : Set E2) : ℝ := sInf {r | ∃ Q, IsPolygonal Q ∧ S ⊆ Q ∧ r = area Q}

theorem IsPolygonal.isQuadrable {S : Set E2} (h : IsPolygonal S) : IsQuadrable S :=
  fun ε hε => ⟨S, S, h, h, subset_rfl, subset_rfl, by simpa using hε⟩

/-- The Lebesgue area of a quadrable set is squeezed between the areas of polygonal sets. -/
theorem IsQuadrable.area_between {S : Set E2} {P Q : Set E2} (hP : IsPolygonal P)
    (hQ : IsPolygonal Q) (hPS : P ⊆ S) (hSQ : S ⊆ Q) :
    area P ≤ area S ∧ area S ≤ area Q :=
  ⟨ENNReal.toReal_mono ((measure_mono hSQ).trans_lt hQ.measure_lt_top).ne (measure_mono hPS),
    area_mono hQ hSQ⟩

/-- Section 20J: for a quadrable set `S` there is a unique real number lying between the areas of
all polygonal sets inside and all polygonal sets containing `S`; it is the Lebesgue area of `S`.
(The book's displayed inequality `area Q ⩽ s ⩽ area P` has the two polygonal sets swapped.) -/
@[kb "petrunin2025" "Section 20J, p. 177"]
theorem IsQuadrable.existsUnique_between {S : Set E2} (h : IsQuadrable S) :
    ∃! s : ℝ, ∀ P Q : Set E2, IsPolygonal P → IsPolygonal Q → P ⊆ S → S ⊆ Q →
      area P ≤ s ∧ s ≤ area Q := by
  refine ⟨area S, fun P Q hP hQ hPS hSQ => IsQuadrable.area_between hP hQ hPS hSQ, ?_⟩
  intro s hs
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, Q, hP, hQ, hPS, hSQ, hPQ⟩ := h ε hε
    have h1 := hs P Q hP hQ hPS hSQ
    have h2 := IsQuadrable.area_between hP hQ hPS hSQ
    linarith [h1.2, h1.1, h2.1, h2.2]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨P, Q, hP, hQ, hPS, hSQ, hPQ⟩ := h ε hε
    have h1 := hs P Q hP hQ hPS hSQ
    have h2 := IsQuadrable.area_between hP hQ hPS hSQ
    linarith [h1.2, h1.1, h2.1, h2.2]

/-- For a quadrable set the inner area, the outer area and the Lebesgue area coincide. -/
@[kb "petrunin2025" "Section 20J, p. 177"]
theorem IsQuadrable.innerArea_eq {S : Set E2} (h : IsQuadrable S) : innerArea S = area S := by
  obtain ⟨P0, Q0, hP0, hQ0, hP0S, hSQ0, -⟩ := h 1 one_pos
  have hfin : volume S ≠ ⊤ := ((measure_mono hSQ0).trans_lt hQ0.measure_lt_top).ne
  unfold innerArea
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨_, ∅, isPolygonal_empty, by simp, rfl⟩ ?_ ?_
  · rintro _ ⟨P, hP, hPS, rfl⟩
    exact ENNReal.toReal_mono hfin (measure_mono hPS)
  · intro w hw
    obtain ⟨P, Q, hP, hQ, hPS, hSQ, hPQ⟩ := h (area S - w) (by linarith)
    have := area_mono hQ hSQ
    exact ⟨area P, ⟨P, hP, hPS, rfl⟩, by linarith⟩

@[kb "petrunin2025" "Section 20J, p. 177"]
theorem IsQuadrable.outerArea_eq {S : Set E2} (h : IsQuadrable S) : outerArea S = area S := by
  obtain ⟨P0, Q0, hP0, hQ0, hP0S, hSQ0, -⟩ := h 1 one_pos
  have hfin : volume S ≠ ⊤ := ((measure_mono hSQ0).trans_lt hQ0.measure_lt_top).ne
  unfold outerArea
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, Q0, hQ0, hSQ0, rfl⟩ ?_ ?_
  · rintro _ ⟨Q, hQ, hSQ, rfl⟩
    exact area_mono hQ hSQ
  · intro w hw
    obtain ⟨P, Q, hP, hQ, hPS, hSQ, hPQ⟩ := h (w - area S) (by linarith)
    have := ENNReal.toReal_mono hfin (measure_mono hPS)
    exact ⟨area Q, ⟨Q, hQ, hSQ, rfl⟩, by unfold area at *; linarith⟩

/-- Remarks on p. 177: a quadrable set is Lebesgue measurable (null-measurable for Lebesgue
measure), and its book area (the unique number squeezed between polygonal approximations,
`IsQuadrable.existsUnique_between`) is its Lebesgue measure.  (The statement about extensions of
area to all bounded sets and the Banach-Tarski paradox is not formalized.) -/
@[kb "petrunin2025" "Remarks, p. 177"]
theorem IsQuadrable.nullMeasurableSet {S : Set E2} (h : IsQuadrable S) :
    NullMeasurableSet S volume := by
  choose P Q hP hQ hPS hSQ hPQ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  set A : Set E2 := ⋃ n, P n with hA
  have hAm : MeasurableSet A := MeasurableSet.iUnion fun n => (hP n).measurableSet
  have hAS : A ⊆ S := Set.iUnion_subset hPS
  have hfin : volume S ≠ ⊤ := ((measure_mono (hSQ 0)).trans_lt (hQ 0).measure_lt_top).ne
  have hnull : volume (S \ A) = 0 := by
    have hfin' : volume (S \ A) ≠ ⊤ := ((measure_mono Set.sdiff_subset).trans_lt hfin.lt_top).ne
    have key : ∀ n : ℕ, (volume (S \ A)).toReal ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have h1 : S \ A ⊆ Q n \ P n := Set.sdiff_subset_sdiff (hSQ n) (Set.subset_iUnion P n)
      have h2 : volume (Q n \ P n) = volume (Q n) - volume (P n) :=
        measure_sdiff ((hPS n).trans (hSQ n)) (hP n).measurableSet.nullMeasurableSet
          (hP n).measure_lt_top.ne
      have h3 : (volume (Q n \ P n)).toReal = area (Q n) - area (P n) := by
        rw [h2, ENNReal.toReal_sub_of_le (measure_mono ((hPS n).trans (hSQ n)))
          (hQ n).measure_lt_top.ne]; rfl
      have h4 : volume (Q n \ P n) ≠ ⊤ :=
        ((measure_mono Set.sdiff_subset).trans_lt (hQ n).measure_lt_top).ne
      calc (volume (S \ A)).toReal ≤ (volume (Q n \ P n)).toReal :=
            ENNReal.toReal_mono h4 (measure_mono h1)
        _ ≤ _ := by rw [h3]; exact (hPQ n).le
    have hz : (volume (S \ A)).toReal ≤ 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      linarith [key n]
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hz ENNReal.toReal_nonneg) with h0 | h0
    · exact h0
    · exact absurd h0 hfin'
  have hae : S =ᵐ[volume] A := by
    rw [ae_eq_set]
    exact ⟨hnull, by rw [Set.sdiff_eq_empty.2 hAS]; simp⟩
  exact hAm.nullMeasurableSet.congr hae.symm

/-! ### Section 20H: the dissection proof of the Pythagorean theorem -/

/-- A line `α x₀ + β x₁ = γ` has Lebesgue measure zero. -/
theorem volume_line_eq_zero {α β : ℝ} (γ : ℝ) (h : α ≠ 0 ∨ β ≠ 0) :
    volume {x : E2 | α * x 0 + β * x 1 = γ} = 0 := by
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    rcases h with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  let φ : E2 →ₗ[ℝ] ℝ :=
    { toFun := fun x => α * x 0 + β * x 1
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  let x₀ : E2 := !₂[γ * α / (α ^ 2 + β ^ 2), γ * β / (α ^ 2 + β ^ 2)]
  have hx₀ : φ x₀ = γ := by
    show α * (γ * α / (α ^ 2 + β ^ 2)) + β * (γ * β / (α ^ 2 + β ^ 2)) = γ
    field_simp
  let s : AffineSubspace ℝ E2 := AffineSubspace.mk' x₀ (LinearMap.ker φ)
  have hs : (s : Set E2) = {x | α * x 0 + β * x 1 = γ} := by
    ext x
    simp only [SetLike.mem_coe, s, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub,
      map_sub, Set.mem_ofPred_eq, hx₀]
    show φ x - γ = 0 ↔ _
    rw [sub_eq_zero]; rfl
  rw [← hs]
  apply Measure.addHaar_affineSubspace
  intro htop
  have h1 : x₀ + !₂[α, β] ∈ s := by rw [htop]; trivial
  have h2 : x₀ + !₂[α, β] ∈ (s : Set E2) := h1
  rw [hs] at h2
  have h3 : α * (x₀ 0 + α) + β * (x₀ 1 + β) = γ := h2
  have h4 : α * x₀ 0 + β * x₀ 1 = γ := hx₀
  nlinarith

theorem volume_inter_eq_zero_of_line {S T : Set E2} {α β γ : ℝ} (h : α ≠ 0 ∨ β ≠ 0)
    (hST : ∀ x ∈ S ∩ T, α * x 0 + β * x 1 = γ) : volume (S ∩ T) = 0 :=
  measure_mono_null (fun x hx => (hST x hx : x ∈ {x : E2 | α * x 0 + β * x 1 = γ}))
    (volume_line_eq_zero γ h)

theorem mem_corner_iff (V : E2) (w h : ℝ) (x : E2) :
    x ∈ solidTriangle V (V + !₂[w, 0]) (V + !₂[0, h]) ↔
      ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ x 0 = V 0 + u * w ∧ x 1 = V 1 + v * h := by
  rw [mem_solidTriangle_iff]
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    obtain rfl : a = 1 - b - c := by linarith
    refine ⟨b, c, hb, hc, by linarith, ?_, ?_⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp; ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp; ring
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    refine ⟨1 - u - v, u, v, by linarith, hu, hv, by ring, E2_ext ?_ ?_⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp [h0]; ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      simp [h1]; ring

/-- The area of the solid right triangle with vertices `V`, `V + (w, 0)`, `V + (0, h)`. -/
theorem area_corner (V : E2) {w h : ℝ} (hw : w ≠ 0) (hh : h ≠ 0) :
    area (solidTriangle V (V + !₂[w, 0]) (V + !₂[0, h])) = |w| * |h| / 2 := by
  set A' : E2 := V + !₂[w, 0] with hA'
  set C' : E2 := V + !₂[0, h] with hC'
  have hind : AffineIndependent ℝ ![A', V, C'] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    rw [collinear_iff_of_mem (p₀ := V) (by simp)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r1, hr1⟩ := hv A' (by simp)
    obtain ⟨r2, hr2⟩ := hv C' (by simp)
    have a0 := congrArg (fun z : E2 => z 0) hr1
    have a1 := congrArg (fun z : E2 => z 1) hr1
    have c0 := congrArg (fun z : E2 => z 0) hr2
    have c1 := congrArg (fun z : E2 => z 1) hr2
    simp [hA', hC'] at a0 a1 c0 c1
    have hr1' : r1 ≠ 0 := by rintro rfl; simp at a0; exact hw a0
    have hv0 : v 0 ≠ 0 := by intro h0; rw [h0] at a0; simp at a0; exact hw a0
    have : r2 = 0 := c0.resolve_right hv0
    subst this
    simp at c1
    exact hh c1
  let t : Affine.Triangle ℝ E2 := ⟨![A', V, C'], hind⟩
  have hang : EuclideanGeometry.angle (t.points 0) (t.points 1) (t.points 2) = Real.pi / 2 := by
    show EuclideanGeometry.angle A' V C' = Real.pi / 2
    unfold EuclideanGeometry.angle
    rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simp [hA', hC', PiLp.inner_apply, Fin.sum_univ_two]
  have key := area_solidTriangle_of_angle_eq_pi_div_two t hang
  have e : solidTriangle (t.points 0) (t.points 1) (t.points 2) = solidTriangle V A' C' := by
    show solidTriangle A' V C' = _
    unfold solidTriangle
    congr 1
    exact Set.insert_comm _ _ _
  rw [e] at key
  rw [key]
  have d1 : dist (t.points 0) (t.points 1) = |w| := by
    show dist A' V = |w|
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [hA', Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
  have d2 : dist (t.points 1) (t.points 2) = |h| := by
    show dist V C' = |h|
    rw [dist_comm, dist_eq_norm, EuclideanSpace.norm_eq]
    simp [hC', Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
  rw [d1, d2]; ring

/-- The square of side `a + b` with a vertex at the origin. -/
def pyK (a b : ℝ) : Set E2 := {x | 0 ≤ x 0 ∧ x 0 ≤ a + b ∧ 0 ≤ x 1 ∧ x 1 ≤ a + b}

/-- The inner square, with vertices `(a, 0)`, `(a + b, a)`, `(b, a + b)`, `(0, b)`; its side is the
hypotenuse of the right triangle with legs `a` and `b`. -/
def pyI (a b : ℝ) : Set E2 :=
  {x | 0 ≤ b * (x 0 - a) + a * x 1 ∧ b * (x 0 - a) + a * x 1 ≤ a ^ 2 + b ^ 2 ∧
    0 ≤ -a * (x 0 - a) + b * x 1 ∧ -a * (x 0 - a) + b * x 1 ≤ a ^ 2 + b ^ 2}

/-- The four corner right triangles with legs `a` and `b`, at the corners `(0,0)`, `(a+b, 0)`,
`(a+b, a+b)`, `(0, a+b)` of the big square. -/
def pyT1 (a b : ℝ) : Set E2 := solidTriangle !₂[0, 0] (!₂[0, 0] + !₂[a, 0]) (!₂[0, 0] + !₂[0, b])
def pyT2 (a b : ℝ) : Set E2 :=
  solidTriangle !₂[a + b, 0] (!₂[a + b, 0] + !₂[-b, 0]) (!₂[a + b, 0] + !₂[0, a])
def pyT3 (a b : ℝ) : Set E2 :=
  solidTriangle !₂[a + b, a + b] (!₂[a + b, a + b] + !₂[-a, 0]) (!₂[a + b, a + b] + !₂[0, -b])
def pyT4 (a b : ℝ) : Set E2 :=
  solidTriangle !₂[0, a + b] (!₂[0, a + b] + !₂[b, 0]) (!₂[0, a + b] + !₂[0, -a])

theorem mem_pyT1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E2) :
    x ∈ pyT1 a b ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ b * x 0 + a * x 1 ≤ a * b := by
  unfold pyT1
  rw [mem_corner_iff]
  simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
  constructor
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    refine ⟨by rw [h0]; positivity, by rw [h1]; positivity, ?_⟩
    rw [h0, h1]; nlinarith [mul_le_mul_of_nonneg_left huv (mul_pos ha hb).le]
  · rintro ⟨i1, i2, i3⟩
    refine ⟨x 0 / a, x 1 / b, div_nonneg i1 ha.le, div_nonneg i2 hb.le, ?_, ?_, ?_⟩
    · rw [div_add_div _ _ ha.ne' hb.ne', div_le_one (mul_pos ha hb)]; nlinarith
    · field_simp
    · field_simp

theorem mem_pyT2 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E2) :
    x ∈ pyT2 a b ↔ x 0 ≤ a + b ∧ 0 ≤ x 1 ∧ b * x 1 ≤ a * (x 0 - a) := by
  unfold pyT2
  rw [mem_corner_iff]
  simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    refine ⟨by nlinarith [mul_nonneg hu hb.le], by rw [h1]; simp; positivity, ?_⟩
    rw [h0, h1]; simp; nlinarith [mul_le_mul_of_nonneg_left huv (mul_pos ha hb).le]
  · rintro ⟨i1, i2, i3⟩
    refine ⟨(a + b - x 0) / b, x 1 / a, div_nonneg (by linarith) hb.le, div_nonneg i2 ha.le, ?_, ?_, ?_⟩
    · rw [div_add_div _ _ hb.ne' ha.ne', div_le_one (mul_pos hb ha)]; nlinarith
    · field_simp; ring
    · simp; field_simp

theorem mem_pyT3 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E2) :
    x ∈ pyT3 a b ↔ x 0 ≤ a + b ∧ x 1 ≤ a + b ∧ a * b + a ^ 2 + b ^ 2 ≤ b * x 0 + a * x 1 := by
  unfold pyT3
  rw [mem_corner_iff]
  simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    refine ⟨by rw [h0]; simp; positivity, by rw [h1]; simp; positivity, ?_⟩
    rw [h0, h1]; simp; nlinarith [mul_le_mul_of_nonneg_left huv (mul_pos ha hb).le]
  · rintro ⟨i1, i2, i3⟩
    refine ⟨(a + b - x 0) / a, (a + b - x 1) / b, div_nonneg (by linarith) ha.le,
      div_nonneg (by linarith) hb.le, ?_, ?_, ?_⟩
    · rw [div_add_div _ _ ha.ne' hb.ne', div_le_one (mul_pos ha hb)]; nlinarith
    · simp; field_simp; ring
    · simp; field_simp; ring

theorem mem_pyT4 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E2) :
    x ∈ pyT4 a b ↔ 0 ≤ x 0 ∧ x 1 ≤ a + b ∧ a * x 0 - b * x 1 ≤ -b ^ 2 := by
  unfold pyT4
  rw [mem_corner_iff]
  simp only [Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    refine ⟨by rw [h0]; simp; positivity, by rw [h1]; simp; positivity, ?_⟩
    rw [h0, h1]; simp; nlinarith [mul_le_mul_of_nonneg_left huv (mul_pos ha hb).le]
  · rintro ⟨i1, i2, i3⟩
    refine ⟨x 0 / b, (a + b - x 1) / a, div_nonneg i1 hb.le, div_nonneg (by linarith) ha.le,
      ?_, ?_, ?_⟩
    · rw [div_add_div _ _ hb.ne' ha.ne', div_le_one (mul_pos hb ha)]; nlinarith
    · simp; field_simp
    · simp; field_simp; ring

/-- The five pieces of the dissection: the four corner triangles and the inner square. -/
def pyPieces (a b : ℝ) : Fin 5 → Set E2 := ![pyT1 a b, pyT2 a b, pyT3 a b, pyT4 a b, pyI a b]

theorem pyK_eq_iUnion {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : pyK a b = ⋃ i, pyPieces a b i := by
  ext x
  simp only [Set.mem_iUnion, pyPieces]
  constructor
  · rintro ⟨k1, k2, k3, k4⟩
    by_cases h1 : b * x 0 + a * x 1 < a * b
    · exact ⟨0, (mem_pyT1 ha hb x).2 ⟨k1, k3, h1.le⟩⟩
    by_cases h3 : a * b + a ^ 2 + b ^ 2 < b * x 0 + a * x 1
    · exact ⟨2, (mem_pyT3 ha hb x).2 ⟨k2, k4, h3.le⟩⟩
    by_cases h2 : a ^ 2 < a * x 0 - b * x 1
    · exact ⟨1, (mem_pyT2 ha hb x).2 ⟨k2, k3, by nlinarith⟩⟩
    by_cases h4 : a * x 0 - b * x 1 < -b ^ 2
    · exact ⟨3, (mem_pyT4 ha hb x).2 ⟨k1, k4, h4.le⟩⟩
    push Not at h1 h2 h3 h4
    exact ⟨4, by simp [pyI]; refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      obtain ⟨i1, i2, i3⟩ := (mem_pyT1 ha hb x).1 hi
      refine ⟨i1, ?_, i2, ?_⟩ <;> nlinarith
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one] at hi
      obtain ⟨i1, i2, i3⟩ := (mem_pyT2 ha hb x).1 hi
      refine ⟨?_, i1, i2, ?_⟩ <;> nlinarith
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] at hi
      obtain ⟨i1, i2, i3⟩ := (mem_pyT3 ha hb x).1 hi
      refine ⟨?_, i1, ?_, i2⟩ <;> nlinarith
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] at hi
      obtain ⟨i1, i2, i3⟩ := (mem_pyT4 ha hb x).1 hi
      refine ⟨i1, ?_, ?_, i2⟩ <;> nlinarith
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, pyI, Set.mem_ofPred_eq] at hi
      obtain ⟨i1, i2, i3, i4⟩ := hi
      have hc2 : 0 < a ^ 2 + b ^ 2 := by positivity
      have e0 : (a ^ 2 + b ^ 2) * x 0 = a * (a ^ 2 + b ^ 2) + b * (b * (x 0 - a) + a * x 1) -
          a * (-a * (x 0 - a) + b * x 1) := by ring
      have e1 : (a ^ 2 + b ^ 2) * x 1 = a * (b * (x 0 - a) + a * x 1) +
          b * (-a * (x 0 - a) + b * x 1) := by ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine le_of_mul_le_mul_left ?_ hc2
        nlinarith [mul_nonneg ha.le (sub_nonneg.2 i4), mul_nonneg hb.le i1]
      · refine le_of_mul_le_mul_left ?_ hc2
        nlinarith [mul_nonneg hb.le (sub_nonneg.2 i2), mul_nonneg ha.le i3]
      · refine le_of_mul_le_mul_left ?_ hc2
        nlinarith [mul_nonneg ha.le i1, mul_nonneg hb.le i3]
      · refine le_of_mul_le_mul_left ?_ hc2
        nlinarith [mul_nonneg ha.le (sub_nonneg.2 i2), mul_nonneg hb.le (sub_nonneg.2 i4)]

theorem area_iUnion_of_null {n : ℕ} (Q : Fin n → Set E2) (hm : ∀ i, MeasurableSet (Q i))
    (hfin : ∀ i, volume (Q i) ≠ ⊤) (hd : ∀ i j, i ≠ j → volume (Q i ∩ Q j) = 0) :
    area (⋃ i, Q i) = ∑ i, area (Q i) := by
  unfold area
  have h1 : volume (⋃ i, Q i) = ∑ i, volume (Q i) := by
    have := measure_biUnion_finset₀ (μ := volume) (s := (Finset.univ : Finset (Fin n)))
      (f := Q) (fun i _ j _ hij => hd i j hij) (fun i _ => (hm i).nullMeasurableSet)
    simpa using this
  rw [h1, ENNReal.toReal_sum (fun i _ => hfin i)]

theorem volume_pyK {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : volume (pyK a b) = ENNReal.ofReal (a + b) ^ 2 := by
  have : pyK a b = (WithLp.ofLp ⁻¹' Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) (a + b)) := by
    ext x
    simp [pyK, Pi.le_def, Fin.forall_fin_two]
    tauto
  rw [this, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet]
  simp [Real.volume_Icc_pi]

theorem isClosed_pyI (a b : ℝ) : IsClosed (pyI a b) := by
  have h : ∀ i : Fin 2, Continuous (fun x : E2 => x i) := fun i => by fun_prop
  unfold pyI
  simp only [Set.ofPred_and]
  refine (isClosed_le (by fun_prop) (by fun_prop)).inter ((isClosed_le (by fun_prop)
    (by fun_prop)).inter ((isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le (by fun_prop) (by fun_prop))))

theorem pyPieces_null {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : Fin 5) (hij : i ≠ j) :
    volume (pyPieces a b i ∩ pyPieces a b j) = 0 := by
  have hc2 : 0 < a ^ 2 + b ^ 2 := by positivity
  have n12 : volume (pyT1 a b ∩ pyT2 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := a) (Or.inl one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT1 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT2 ha hb x).1 h2
    have u : x 0 ≤ a := by nlinarith
    have v : a ≤ x 0 := by nlinarith
    linarith
  have n13 : volume (pyT1 a b ∩ pyT3 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := 0) (Or.inl one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT1 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT3 ha hb x).1 h2
    exfalso; nlinarith
  have n14 : volume (pyT1 a b ∩ pyT4 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 0) (β := 1) (γ := b) (Or.inr one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT1 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT4 ha hb x).1 h2
    have u : x 1 ≤ b := by nlinarith
    have v : b ≤ x 1 := by nlinarith
    linarith
  have n15 : volume (pyT1 a b ∩ pyI a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := b) (β := a) (γ := a * b) (Or.inr ha.ne') ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT1 ha hb x).1 h1
    obtain ⟨r1, r2, r3, r4⟩ := h2
    nlinarith
  have n23 : volume (pyT2 a b ∩ pyT3 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 0) (β := 1) (γ := a) (Or.inr one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT2 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT3 ha hb x).1 h2
    have u : x 1 ≤ a := by nlinarith
    have v : a ≤ x 1 := by nlinarith
    linarith
  have n24 : volume (pyT2 a b ∩ pyT4 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := 0) (Or.inl one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT2 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT4 ha hb x).1 h2
    exfalso; nlinarith
  have n25 : volume (pyT2 a b ∩ pyI a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := a) (β := -b) (γ := a ^ 2) (Or.inl ha.ne') ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT2 ha hb x).1 h1
    obtain ⟨r1, r2, r3, r4⟩ := h2
    nlinarith
  have n34 : volume (pyT3 a b ∩ pyT4 a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := 1) (β := 0) (γ := b) (Or.inl one_ne_zero) ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT3 ha hb x).1 h1
    obtain ⟨q1, q2, q3⟩ := (mem_pyT4 ha hb x).1 h2
    have u : x 0 ≤ b := by nlinarith
    have v : b ≤ x 0 := by nlinarith
    linarith
  have n35 : volume (pyT3 a b ∩ pyI a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := b) (β := a) (γ := a * b + a ^ 2 + b ^ 2)
      (Or.inr ha.ne') ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT3 ha hb x).1 h1
    obtain ⟨r1, r2, r3, r4⟩ := h2
    nlinarith
  have n45 : volume (pyT4 a b ∩ pyI a b) = 0 := by
    refine volume_inter_eq_zero_of_line (α := a) (β := -b) (γ := -b ^ 2) (Or.inl ha.ne') ?_
    rintro x ⟨h1, h2⟩
    obtain ⟨p1, p2, p3⟩ := (mem_pyT4 ha hb x).1 h1
    obtain ⟨r1, r2, r3, r4⟩ := h2
    nlinarith
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | simpa [pyPieces] using n12
    | simpa [pyPieces, Set.inter_comm] using n12
    | simpa [pyPieces] using n13
    | simpa [pyPieces, Set.inter_comm] using n13
    | simpa [pyPieces] using n14
    | simpa [pyPieces, Set.inter_comm] using n14
    | simpa [pyPieces] using n15
    | simpa [pyPieces, Set.inter_comm] using n15
    | simpa [pyPieces] using n23
    | simpa [pyPieces, Set.inter_comm] using n23
    | simpa [pyPieces] using n24
    | simpa [pyPieces, Set.inter_comm] using n24
    | simpa [pyPieces] using n25
    | simpa [pyPieces, Set.inter_comm] using n25
    | simpa [pyPieces] using n34
    | simpa [pyPieces, Set.inter_comm] using n34
    | simpa [pyPieces] using n35
    | simpa [pyPieces, Set.inter_comm] using n35
    | simpa [pyPieces] using n45
    | simpa [pyPieces, Set.inter_comm] using n45

theorem area_pyPieces_ne_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 5) :
    volume (pyPieces a b i) ≠ ⊤ := by
  have hK : volume (pyK a b) ≠ ⊤ := by
    rw [volume_pyK ha hb]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hK (measure_mono ?_)
  rw [pyK_eq_iUnion ha hb]
  exact Set.subset_iUnion (pyPieces a b) i

theorem pyPieces_measurable (a b : ℝ) (i : Fin 5) : MeasurableSet (pyPieces a b i) := by
  fin_cases i
  · exact (IsElementary.isPolygonal (Or.inr (Or.inr ⟨_, _, _, rfl⟩))).measurableSet
  · exact (IsElementary.isPolygonal (Or.inr (Or.inr ⟨_, _, _, rfl⟩))).measurableSet
  · exact (IsElementary.isPolygonal (Or.inr (Or.inr ⟨_, _, _, rfl⟩))).measurableSet
  · exact (IsElementary.isPolygonal (Or.inr (Or.inr ⟨_, _, _, rfl⟩))).measurableSet
  · exact (isClosed_pyI a b).measurableSet

/-- Section 20H, the dissection proof of the Pythagorean theorem.  For legs `a, b > 0`, the square
of side `a + b` is the union of the four corner right triangles with legs `a` and `b` and the inner
square on the hypotenuse; any two pieces meet in a null set (they only share boundary segments);
each triangle has area `ab/2`, the big square has area `(a+b)²`, and hence the inner square has area
`(a+b)² - 4 · (ab/2) = a² + b²`. -/
@[kb "petrunin2025" "Section 20H, Pythagorean theorem, p. 173"]
theorem pythagoras_dissection {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pyK a b = ⋃ i, pyPieces a b i ∧
      (∀ i j, i ≠ j → volume (pyPieces a b i ∩ pyPieces a b j) = 0) ∧
      area (pyK a b) = (a + b) ^ 2 ∧
      area (pyT1 a b) = a * b / 2 ∧ area (pyT2 a b) = a * b / 2 ∧
      area (pyT3 a b) = a * b / 2 ∧ area (pyT4 a b) = a * b / 2 ∧
      area (pyI a b) = a ^ 2 + b ^ 2 := by
  have h1 : area (pyT1 a b) = a * b / 2 := by
    unfold pyT1; rw [area_corner _ ha.ne' hb.ne', abs_of_pos ha, abs_of_pos hb]
  have h2 : area (pyT2 a b) = a * b / 2 := by
    unfold pyT2; rw [area_corner _ (neg_ne_zero.2 hb.ne') ha.ne', abs_neg, abs_of_pos ha,
      abs_of_pos hb]; ring
  have h3 : area (pyT3 a b) = a * b / 2 := by
    unfold pyT3; rw [area_corner _ (neg_ne_zero.2 ha.ne') (neg_ne_zero.2 hb.ne'), abs_neg,
      abs_neg, abs_of_pos ha, abs_of_pos hb]
  have h4 : area (pyT4 a b) = a * b / 2 := by
    unfold pyT4; rw [area_corner _ hb.ne' (neg_ne_zero.2 ha.ne'), abs_neg, abs_of_pos ha,
      abs_of_pos hb]; ring
  have hK : area (pyK a b) = (a + b) ^ 2 := by
    unfold area
    rw [volume_pyK ha hb, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  have hsum : area (pyK a b) = ∑ i, area (pyPieces a b i) := by
    rw [pyK_eq_iUnion ha hb]
    exact area_iUnion_of_null _ (pyPieces_measurable a b) (area_pyPieces_ne_top ha hb)
      (pyPieces_null ha hb)
  rw [Fin.sum_univ_five] at hsum
  simp only [pyPieces, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.reduceFinMk] at hsum
  refine ⟨pyK_eq_iUnion ha hb, pyPieces_null ha hb, hK, h1, h2, h3, h4, ?_⟩
  rw [h1, h2, h3, h4, hK] at hsum
  nlinarith

/-- The side of the inner square is the hypotenuse `c` of the right triangle with legs `a`, `b`;
the inner square has area `c²`, so the dissection gives `a² + b² = c²`. (Here the side length is
computed from the coordinate model of distance, and the dissection is the area argument.) -/
theorem pythagoras_dissection_hypotenuse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    area (pyI a b) = dist (!₂[a, 0] : E2) !₂[a + b, a] ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := pythagoras_dissection ha hb
  rw [h, EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two]
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- The axis-parallel square `[0, s]²`. -/
def sqBox (s : ℝ) : Set E2 := {x | 0 ≤ x 0 ∧ x 0 ≤ s ∧ 0 ≤ x 1 ∧ x 1 ≤ s}

/-- The axis-parallel square of side `s ≥ 0` has area `s²`. -/
theorem area_sqBox {s : ℝ} (hs : 0 ≤ s) : area (sqBox s) = s ^ 2 := by
  have : sqBox s = (WithLp.ofLp ⁻¹' Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) s) := by
    ext x
    simp [sqBox, Pi.le_def, Fin.forall_fin_two]
    tauto
  unfold area
  rw [this, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet]
  simp [Real.volume_Icc_pi, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs]

/-- Pythagoras by dissection, with the hypotenuse entering only as the side of the inner square:
if the inner square `pyI a b` is the image of the axis-parallel square `[0,c]²` under a motion
(so it is a square of side `c`), then `a² + b² = c²`.  The proof compares two area computations of
`pyI a b`: `c²` (invariance of area under motions and the area of an axis-parallel square) and
`a² + b²` (the dissection of the square of side `a + b`). -/
@[kb "petrunin2025" "Section 20H, Pythagorean theorem, p. 173"]
theorem pythagoras_dissection' {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (f : E2 ≃ᵢ E2) (hf : f '' sqBox c = pyI a b) : a ^ 2 + b ^ 2 = c ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := pythagoras_dissection ha hb
  rw [← h, ← hf, area_image_isometryEquiv, area_sqBox hc]

/-- The motion carrying `[0,c]²` onto the inner square, where `c` is the length of the hypotenuse
(the relation `c² = a² + b²` is used here only to see that the map is an isometry; it is not used
in `pythagoras_dissection'`). -/
noncomputable def motionPy (a b c : ℝ) (hc : c ≠ 0) (hc2 : c ^ 2 = a ^ 2 + b ^ 2) : E2 ≃ᵢ E2 :=
  { toFun := fun x => !₂[a + (b * x 0 - a * x 1) / c, (a * x 0 + b * x 1) / c]
    invFun := fun y => !₂[(b * (y 0 - a) + a * y 1) / c, (-a * (y 0 - a) + b * y 1) / c]
    left_inv := fun x => by
      apply E2_ext
      · simp
        field_simp
        first | linear_combination (x 0) * hc2 | linear_combination (-x 0) * hc2
      · simp
        field_simp
        first | linear_combination (x 1) * hc2 | linear_combination (-x 1) * hc2
    right_inv := fun y => by
      apply E2_ext
      · simp
        field_simp
        first | linear_combination (y 0 - a) * hc2 | linear_combination (-(y 0 - a)) * hc2
      · simp
        field_simp
        first | linear_combination (y 1) * hc2 | linear_combination (-y 1) * hc2
    isometry_toFun := Isometry.of_dist_eq fun x y => by
      rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
      congr 1
      simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.dist_eq, sq_abs]
      field_simp
      first
        | linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * hc2
        | linear_combination (-((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2)) * hc2 }

theorem motionPy_image {a b c : ℝ} (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2) :
    motionPy a b c hc.ne' hc2 '' sqBox c = pyI a b := by
  have hc' : c ≠ 0 := hc.ne'
  ext y
  constructor
  · rintro ⟨x, ⟨x1, x2, x3, x4⟩, rfl⟩
    have e0 : b * ((motionPy a b c hc' hc2 x) 0 - a) + a * (motionPy a b c hc' hc2 x) 1 = c * x 0 := by
      show b * (a + (b * x 0 - a * x 1) / c - a) + a * ((a * x 0 + b * x 1) / c) = c * x 0
      field_simp
      first | linear_combination (x 0) * hc2 | linear_combination (-x 0) * hc2
    have e1 : -a * ((motionPy a b c hc' hc2 x) 0 - a) + b * (motionPy a b c hc' hc2 x) 1 = c * x 1 := by
      show -a * (a + (b * x 0 - a * x 1) / c - a) + b * ((a * x 0 + b * x 1) / c) = c * x 1
      field_simp
      first | linear_combination (x 1) * hc2 | linear_combination (-x 1) * hc2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [e0]; rw [e0]; rw [e1]; rw [e1]] <;> nlinarith
  · intro hy
    obtain ⟨y1, y2, y3, y4⟩ := hy
    refine ⟨(motionPy a b c hc' hc2).symm y, ?_, (motionPy a b c hc' hc2).apply_symm_apply y⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 0 ≤ (b * (y 0 - a) + a * y 1) / c
      exact div_nonneg y1 hc.le
    · show (b * (y 0 - a) + a * y 1) / c ≤ c
      rw [div_le_iff₀ hc]; nlinarith
    · show 0 ≤ (-a * (y 0 - a) + b * y 1) / c
      exact div_nonneg y3 hc.le
    · show (-a * (y 0 - a) + b * y 1) / c ≤ c
      rw [div_le_iff₀ hc]; nlinarith

/-- Pythagoras by dissection, final form: for the right triangle with legs `a`, `b` the inner
square of the dissection has a side `c` (the hypotenuse, `dist` between two adjacent vertices of
the inner square); the inner square is the image of `[0,c]²` under a motion, and the area count
gives `a² + b² = c²`. -/
theorem pythagoras_by_dissection {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 + b ^ 2 = dist (!₂[a, 0] : E2) !₂[a + b, a] ^ 2 := by
  set c := dist (!₂[a, 0] : E2) !₂[a + b, a] with hc
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hc, EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hcpos : 0 < c := dist_pos.2 fun h => by
    have := congrArg (fun z : E2 => z 0) h
    simp at this; linarith
  exact pythagoras_dissection' ha hb hcpos.le (motionPy a b c hcpos.ne' hc2)
    (motionPy_image hcpos hc2)

end UndergradKB.Geometry
