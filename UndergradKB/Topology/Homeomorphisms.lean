import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Homeomorphisms of intervals, removal of points, path-connectedness, fixed points

Morris, *Topology Without Tears* (2024), Chapters 4 and 5: open intervals are homeomorphic to each
other and to `ℝ`, a homeomorphism restricts to the complements of corresponding points, the
intervals `(a,b)`, `[c,d)`, `[c,d]` are pairwise non-homeomorphic, semi-open sets, intervals are
path-connected, `ℝ` is not homeomorphic to `ℝ²`, and the fixed point theorem on `[0,1]`.
-/

namespace UndergradKB.Topology

open Set

/-! ### Open intervals (TP-066, TP-067) -/

/-- Morris, Topology Without Tears, Example 4.2.4 (TP-066). Any two non-empty bounded open intervals
of `ℝ` are homeomorphic, via an increasing affine map. -/
@[kb "morris2024" "Example 4.2.4, p. 98"]
noncomputable def ioo_homeomorph_ioo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Set.Ioo a b ≃ₜ Set.Ioo c d :=
  let s : ℝ := (d - c) / (b - a)
  have hs : 0 < s := div_pos (sub_pos.2 hcd) (sub_pos.2 hab)
  have h1 : s * a + (c - s * a) = c := by ring
  have h2 : s * b + (c - s * a) = d := by
    have : s * (b - a) = d - c := div_mul_cancel₀ _ (sub_pos.2 hab).ne'
    linarith
  (Homeomorph.image (affineHomeomorph s (c - s * a) hs.ne') (Set.Ioo a b)).trans
    (Homeomorph.setCongr (by rw [affineHomeomorph_image_Ioo _ _ _ _ hs, h1, h2]))

/-- Morris, Topology Without Tears, Example 4.2.5 (TP-067). `ℝ` is homeomorphic to the open
interval `(-1, 1)`. -/
@[kb "morris2024" "Example 4.2.5, p. 99"]
noncomputable def real_homeomorph_Ioo_neg_one_one : ℝ ≃ₜ Set.Ioo (-1 : ℝ) 1 :=
  (orderIsoIooNegOneOne ℝ).toHomeomorph

/-- Morris, Topology Without Tears, Example 4.2.6 (TP-067). Every open interval `(a, b)` with
`a < b` is homeomorphic to `ℝ`. -/
@[kb "morris2024" "Example 4.2.6, p. 99"]
noncomputable def ioo_homeomorph_real {a b : ℝ} (hab : a < b) : Set.Ioo a b ≃ₜ ℝ :=
  (ioo_homeomorph_ioo hab (by norm_num : (-1 : ℝ) < 1)).trans real_homeomorph_Ioo_neg_one_one.symm

/-! ### Removing points (TP-072) -/

/-- Morris, Topology Without Tears, Remark 4.3.6 (TP-072). A homeomorphism `f : X ≃ₜ Y` restricts to
a homeomorphism from `X \ {a}` onto `Y \ {f a}`. -/
@[kb "morris2024" "Remark 4.3.6, p. 105"]
def homeomorph_compl_singleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (a : X) : ({a}ᶜ : Set X) ≃ₜ ({f a}ᶜ : Set Y) :=
  (f.image ({a}ᶜ : Set X)).trans
    (Homeomorph.setCongr (by rw [f.image_compl, Set.image_singleton]))

theorem homeomorph_compl_singleton_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (a : X) (x : ({a}ᶜ : Set X)) :
    ((homeomorph_compl_singleton f a x : ({f a}ᶜ : Set Y)) : Y) = f x := rfl

theorem val_image_compl {X : Type*} {s : Set X} (A : Set s) :
    Subtype.val '' Aᶜ = s \ Subtype.val '' A := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    rintro ⟨u, hu, hux⟩
    have : u = w := Subtype.ext hux
    subst this
    exact hw hu
  · rintro ⟨hx, hnot⟩
    exact ⟨⟨x, hx⟩, fun hm => hnot ⟨_, hm, rfl⟩, rfl⟩

/-- Removing a set `A` of points from `s` and the corresponding set from `t` along a homeomorphism
`s ≃ₜ t` preserves (pre)connectedness of the remainder, as subsets of the ambient space. -/
theorem isPreconnected_sdiff_iff {X : Type*} [TopologicalSpace X] {s t : Set X}
    (e : s ≃ₜ t) (A : Set s) :
    IsPreconnected (s \ Subtype.val '' A) ↔ IsPreconnected (t \ Subtype.val '' (e '' A)) := by
  rw [← val_image_compl, ← val_image_compl, _root_.Topology.IsInducing.subtypeVal.isPreconnected_image,
    _root_.Topology.IsInducing.subtypeVal.isPreconnected_image, ← e.image_compl,
    e.isPreconnected_image]

/-- If `{e a}ᶜ` is preconnected in the target of a homeomorphism `e`, then `{a}ᶜ` is preconnected. -/
theorem isPreconnected_compl_singleton_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (a : X) (h : IsPreconnected ({e a}ᶜ : Set Y)) :
    IsPreconnected ({a}ᶜ : Set X) := by
  rw [isPreconnected_iff_preconnectedSpace] at h ⊢
  let g := (homeomorph_compl_singleton e a).symm
  have := isPreconnected_range (f := g) g.continuous
  rw [g.surjective.range_eq] at this
  exact preconnectedSpace_iff_univ.2 this

/-! ### Non-homeomorphic intervals (TP-073) -/

theorem not_isPreconnected_Ioo_diff_singleton {a b y : ℝ} (hy : y ∈ Set.Ioo a b) :
    ¬ IsPreconnected (Set.Ioo a b \ {y}) := by
  intro h
  have hoc := h.ordConnected
  have hx : (a + y) / 2 ∈ Set.Ioo a b \ {y} :=
    ⟨⟨by linarith [hy.1], by linarith [hy.1, hy.2]⟩,
      fun e => by have e' : (a + y) / 2 = y := e; linarith [hy.1]⟩
  have hz : (y + b) / 2 ∈ Set.Ioo a b \ {y} :=
    ⟨⟨by linarith [hy.1, hy.2], by linarith [hy.2]⟩,
      fun e => by have e' : (y + b) / 2 = y := e; linarith [hy.2]⟩
  have := hoc.out hx hz (show y ∈ Set.Icc ((a + y) / 2) ((y + b) / 2) from
    ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  exact this.2 (mem_singleton y)

theorem not_isPreconnected_Ico_diff_pair {a b y z : ℝ} (hy : y ∈ Set.Ico a b) (hz : z ∈ Set.Ico a b)
    (hyz : y < z) : ¬ IsPreconnected (Set.Ico a b \ {y, z}) := by
  intro h
  have hoc := h.ordConnected
  have hx : (y + z) / 2 ∈ Set.Ico a b \ {y, z} :=
    ⟨⟨by linarith [hy.1], by linarith [hz.2]⟩, fun e => by
      rcases (show (y + z) / 2 = y ∨ (y + z) / 2 = z from e) with e | e <;> linarith⟩
  have hw : (z + b) / 2 ∈ Set.Ico a b \ {y, z} :=
    ⟨⟨by linarith [hy.1, hz.1, hz.2], by linarith [hz.2]⟩, fun e => by
      rcases (show (z + b) / 2 = y ∨ (z + b) / 2 = z from e) with e | e <;>
        linarith [hz.2, hy.1, hz.1]⟩
  have := hoc.out hx hw (show z ∈ Set.Icc ((y + z) / 2) ((z + b) / 2) from
    ⟨by linarith, by linarith [hz.2]⟩)
  exact this.2 (mem_insert_of_mem _ (mem_singleton z))

/-- Morris, Topology Without Tears, Corollary 4.3.7 (i) (TP-073). `(a,b)` is not homeomorphic to
`[c,d)`. -/
@[kb "morris2024" "Corollary 4.3.7, p. 105"]
theorem isEmpty_homeomorph_Ioo_Ico {a b c d : ℝ} (_hab : a < b) (hcd : c < d) :
    IsEmpty (Set.Ioo a b ≃ₜ Set.Ico c d) := by
  refine ⟨fun h => ?_⟩
  have hc : c ∈ Set.Ico c d := ⟨le_rfl, hcd⟩
  have key := isPreconnected_sdiff_iff h.symm {⟨c, hc⟩}
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, Set.Ico_sdiff_left] at key
  exact not_isPreconnected_Ioo_diff_singleton (h.symm ⟨c, hc⟩).2 (key.1 isPreconnected_Ioo)

/-- Morris, Topology Without Tears, Corollary 4.3.7 (ii) (TP-073). `(a,b)` is not homeomorphic to
`[c,d]`. -/
@[kb "morris2024" "Corollary 4.3.7, p. 105"]
theorem isEmpty_homeomorph_Ioo_Icc {a b c d : ℝ} (_hab : a < b) (hcd : c < d) :
    IsEmpty (Set.Ioo a b ≃ₜ Set.Icc c d) := by
  refine ⟨fun h => ?_⟩
  have hc : c ∈ Set.Icc c d := ⟨le_rfl, hcd.le⟩
  have key := isPreconnected_sdiff_iff h.symm {⟨c, hc⟩}
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, Set.Icc_sdiff_left] at key
  exact not_isPreconnected_Ioo_diff_singleton (h.symm ⟨c, hc⟩).2 (key.1 isPreconnected_Ioc)

/-- Morris, Topology Without Tears, Corollary 4.3.7 (iii) (TP-073). `[a,b)` is not homeomorphic to
`[c,d]`. -/
@[kb "morris2024" "Corollary 4.3.7, p. 105"]
theorem isEmpty_homeomorph_Ico_Icc {a b c d : ℝ} (_hab : a < b) (hcd : c < d) :
    IsEmpty (Set.Ico a b ≃ₜ Set.Icc c d) := by
  refine ⟨fun h => ?_⟩
  have hc : c ∈ Set.Icc c d := ⟨le_rfl, hcd.le⟩
  have hd : d ∈ Set.Icc c d := ⟨hcd.le, le_rfl⟩
  have key := isPreconnected_sdiff_iff h.symm {⟨c, hc⟩, ⟨d, hd⟩}
  rw [Set.image_pair, Set.image_pair, Set.image_pair, Set.Icc_sdiff_both] at key
  have hne : (h.symm ⟨c, hc⟩ : ℝ) ≠ (h.symm ⟨d, hd⟩ : ℝ) := by
    intro e
    have := congrArg Subtype.val (h.symm.injective (Subtype.ext e))
    have : c = d := this
    linarith
  have hpre := key.1 isPreconnected_Ioo
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_isPreconnected_Ico_diff_pair (h.symm ⟨c, hc⟩).2 (h.symm ⟨d, hd⟩).2 hlt hpre
  · rw [Set.pair_comm] at hpre
    exact not_isPreconnected_Ico_diff_pair (h.symm ⟨d, hd⟩).2 (h.symm ⟨c, hc⟩).2 hgt hpre

/-! ### Semi-open sets (TP-075) -/

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (TP-075). A set `A` is semi-open if there is an
open `O` with `O ⊆ A ⊆ closure O`. -/
def IsSemiOpen {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ O : Set X, IsOpen O ∧ O ⊆ A ∧ A ⊆ closure O

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (i) (TP-075). Open sets are semi-open. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem IsOpen.isSemiOpen {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen A) :
    IsSemiOpen A :=
  ⟨A, h, subset_rfl, subset_closure⟩

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (ii) (TP-075). A closed set need not be
semi-open: `{0}` in `ℝ`. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem isClosed_not_isSemiOpen : IsClosed ({0} : Set ℝ) ∧ ¬ IsSemiOpen ({0} : Set ℝ) := by
  refine ⟨isClosed_singleton, ?_⟩
  rintro ⟨O, hO, hOA, hAO⟩
  have : O = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hx0 : x = 0 := hOA hx
    subst hx0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 hx
    have hy : ε / 2 ∈ O :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
    have := hOA hy
    simp at this
    linarith
  rw [this, closure_empty] at hAO
  exact (hAO rfl : (0:ℝ) ∈ (∅ : Set ℝ))

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (iii) (TP-075). A set of reals that contains
an interval property (order-connected) and has at least two points is semi-open. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem isSemiOpen_of_ordConnected {A : Set ℝ} (hA : A.OrdConnected) (h2 : ∃ x ∈ A, ∃ y ∈ A, x ≠ y) :
    IsSemiOpen A := by
  refine ⟨interior A, isOpen_interior, interior_subset, fun p hp => ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := h2
  obtain ⟨q, hq, hpq⟩ : ∃ q ∈ A, q ≠ p := by
    by_cases hxp : x = p
    · exact ⟨y, hy, fun e => hxy (hxp.trans e.symm)⟩
    · exact ⟨x, hx, hxp⟩
  rcases lt_or_gt_of_ne hpq with h | h
  · have hsub : Set.Ioo q p ⊆ interior A :=
      interior_maximal (Ioo_subset_Icc_self.trans (hA.out hq hp)) isOpen_Ioo
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨h.le, le_rfl⟩)
  · have hsub : Set.Ioo p q ⊆ interior A :=
      interior_maximal (Ioo_subset_Icc_self.trans (hA.out hp hq)) isOpen_Ioo
    exact closure_mono hsub (by rw [closure_Ioo h.ne]; exact ⟨le_rfl, h.le⟩)

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (iv) (TP-075). For the discrete topology the
semi-open sets are the open sets. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem isSemiOpen_iff_isOpen_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) : IsSemiOpen A ↔ IsOpen A :=
  ⟨fun _ => isOpen_discrete A, IsOpen.isSemiOpen⟩

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (iv) (TP-075). For the indiscrete topology the
semi-open sets are the open sets. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem isSemiOpen_iff_isOpen_of_indiscrete {X : Type*} [TopologicalSpace X] [IndiscreteTopology X]
    (A : Set X) : IsSemiOpen A ↔ IsOpen A := by
  refine ⟨?_, IsOpen.isSemiOpen⟩
  rintro ⟨O, hO, hOA, hAO⟩
  rcases (IndiscreteTopology.isOpen_iff O).1 hO with rfl | rfl
  · rw [closure_empty] at hAO
    have : A = ∅ := Set.subset_empty_iff.1 hAO
    rw [this]; exact isOpen_empty
  · have : A = univ := Set.eq_univ_of_univ_subset hOA
    rw [this]; exact isOpen_univ

/-- Morris, Topology Without Tears, Exercises 4.3 #10 (iv) (TP-075). For the finite-closed (cofinite)
topology the semi-open sets are the open sets. -/
@[kb "morris2024" "Exercises 4.3, p. 108"]
theorem isSemiOpen_iff_isOpen_of_cofinite {X : Type*} (A : Set (CofiniteTopology X)) :
    IsSemiOpen A ↔ IsOpen A := by
  refine ⟨?_, IsOpen.isSemiOpen⟩
  rintro ⟨O, hO, hOA, hAO⟩
  rcases (CofiniteTopology.isOpen_iff'.1 hO) with rfl | hfin
  · rw [closure_empty] at hAO
    have : A = ∅ := Set.subset_empty_iff.1 hAO
    rw [this]; exact isOpen_empty
  · exact CofiniteTopology.isOpen_iff'.2 (Or.inr (hfin.subset (Set.compl_subset_compl.2 hOA)))

/-! ### Path-connectedness (TP-086, TP-089) -/

/-- Morris, Topology Without Tears, Example 5.2.4 (TP-086). Every non-empty interval of `ℝ`
(order-connected set) is path-connected. -/
@[kb "morris2024" "Example 5.2.4, p. 118"]
theorem isPathConnected_of_ordConnected {A : Set ℝ} (hA : A.OrdConnected) (hne : A.Nonempty) :
    IsPathConnected A :=
  (hA.convex (𝕜 := ℝ)).isPathConnected hne

/-- Morris, Topology Without Tears, Example 5.2.4 (TP-086). A closed bounded interval `[a, b]`,
`a ≤ b`, is a path-connected space. -/
@[kb "morris2024" "Example 5.2.4, p. 118"]
theorem pathConnectedSpace_Icc {a b : ℝ} (h : a ≤ b) : PathConnectedSpace (Set.Icc a b) :=
  isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_of_ordConnected ordConnected_Icc (nonempty_Icc.2 h))

/-- Morris, Topology Without Tears, Example 5.2.4 (TP-086). An open bounded interval `(a, b)`,
`a < b`, is a path-connected space. -/
@[kb "morris2024" "Example 5.2.4, p. 118"]
theorem pathConnectedSpace_Ioo {a b : ℝ} (h : a < b) : PathConnectedSpace (Set.Ioo a b) :=
  isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_of_ordConnected ordConnected_Ioo (nonempty_Ioo.2 h))

/-- Morris, Topology Without Tears, Example 5.2.5 (TP-086). `ℝⁿ` (as `Fin n → ℝ`) is
path-connected. -/
@[kb "morris2024" "Example 5.2.5, p. 118"]
theorem pathConnectedSpace_fin_pi (n : ℕ) : PathConnectedSpace (Fin n → ℝ) := inferInstance

/-- Morris, Topology Without Tears, Example 5.2.5 (TP-086). Euclidean `n`-space is path-connected. -/
@[kb "morris2024" "Example 5.2.5, p. 118"]
theorem pathConnectedSpace_euclideanSpace (n : ℕ) : PathConnectedSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Morris, Topology Without Tears, Example 5.2.8 (TP-089). The plane minus the origin (indeed minus
any point) is path-connected. -/
@[kb "morris2024" "Example 5.2.8, p. 119"]
theorem isPathConnected_euclideanSpace_two_compl_singleton (p : EuclideanSpace ℝ (Fin 2)) :
    IsPathConnected ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- Morris, Topology Without Tears, Example 5.2.8 (TP-089). The plane minus the origin is
connected. -/
@[kb "morris2024" "Example 5.2.8, p. 119"]
theorem isConnected_euclideanSpace_two_compl_origin :
    IsConnected ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
  (isPathConnected_euclideanSpace_two_compl_singleton 0).isConnected

theorem not_isPreconnected_real_compl_singleton (a : ℝ) : ¬ IsPreconnected ({a}ᶜ : Set ℝ) := by
  intro h
  have hoc := h.ordConnected
  have h1 : a - 1 ∈ ({a}ᶜ : Set ℝ) := by simp
  have h2 : a + 1 ∈ ({a}ᶜ : Set ℝ) := by simp
  have := hoc.out h1 h2 ⟨by linarith, by linarith⟩
  simp at this

/-- Morris, Topology Without Tears, Example 5.2.8 (TP-089). `ℝ` is not homeomorphic to `ℝ²`
(Euclidean plane). -/
@[kb "morris2024" "Example 5.2.8, p. 119"]
theorem isEmpty_homeomorph_real_euclideanSpace_two :
    IsEmpty (ℝ ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  refine ⟨fun e => ?_⟩
  have hc := (isPathConnected_euclideanSpace_two_compl_singleton (e 0)).isConnected.isPreconnected
  exact not_isPreconnected_real_compl_singleton 0
    (isPreconnected_compl_singleton_of_homeomorph e 0 hc)

/-- Morris, Topology Without Tears, Example 5.2.8 (TP-089). `ℝ` is not homeomorphic to `ℝ × ℝ`. -/
@[kb "morris2024" "Example 5.2.8, p. 119"]
theorem isEmpty_homeomorph_real_prod_real : IsEmpty (ℝ ≃ₜ ℝ × ℝ) := by
  refine ⟨fun e => ?_⟩
  have hp : IsPathConnected ({e 0}ᶜ : Set (ℝ × ℝ)) := by
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank]
    simp
  exact not_isPreconnected_real_compl_singleton 0
    (isPreconnected_compl_singleton_of_homeomorph e 0 hp.isConnected.isPreconnected)

/-! ### Fixed point theorem (TP-092) -/

/-- Morris, Topology Without Tears, Corollary 5.2.11 (TP-092) for a general closed interval: every
continuous self-map of `[a, b]` has a fixed point. -/
theorem exists_fixedPoint_Icc {a b : ℝ} (hab : a ≤ b) {f : Set.Icc a b → Set.Icc a b}
    (hf : Continuous f) : ∃ x, f x = x := by
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  let g : Set.Icc a b → ℝ := fun x => (f x : ℝ) - x
  have hg : Continuous g := (continuous_subtype_val.comp hf).sub continuous_subtype_val
  let lo : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let hi : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have h1 : g hi ≤ 0 := by simp only [g, hi]; linarith [(f hi).2.2]
  have h2 : 0 ≤ g lo := by simp only [g, lo]; linarith [(f lo).2.1]
  obtain ⟨x, hx⟩ := intermediate_value_univ hi lo hg ⟨h1, h2⟩
  refine ⟨x, Subtype.ext ?_⟩
  simp only [g] at hx
  linarith

/-- Morris, Topology Without Tears, Corollary 5.2.11 (TP-092). Every continuous map of `[0,1]` into
itself has a fixed point. -/
@[kb "morris2024" "Corollary 5.2.11, p. 120"]
theorem exists_fixedPoint_unitInterval {f : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1}
    (hf : Continuous f) : ∃ x, f x = x :=
  exists_fixedPoint_Icc zero_le_one hf

end UndergradKB.Topology
