import Mathlib.Topology.ClopenBox
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Metrizable.Uniformity
import UndergradKB.Common.Attr

/-! # Brouwer's characterisation of the Cantor set; totally disconnected compact groups

* `nonempty_homeomorph_cantor_of_perfect`: (Brouwer) a nonempty compact Hausdorff, second
  countable, totally disconnected space without isolated points is homeomorphic to the Cantor space
  `ℕ → Bool`, hence to the Cantor set.
* `nonempty_homeomorph_cantor_of_group` (Morris, Theorem A5.0.23, TP-496, in the metrizable case):
  the underlying space of an infinite, totally disconnected, compact, metrizable group is the Cantor
  cube `{0,1}^ℵ₀`.

Proof of Brouwer's theorem: enumerate the (countably many) clopen sets `B 0, B 1, ...`. Build a
binary tree of nonempty clopen sets: at depth `n` a node `U` is cut by `B n` when both parts are
nonempty, and otherwise by any clopen set splitting `U` (there is one, since `U` has two points).
Every branch is a decreasing sequence of nonempty compact sets; two points of the intersection would
be separated by some `B n`, which would have cut the branch, so the intersection is one point. The
resulting map `(ℕ → Bool) → X` is a continuous bijection from a compact space onto a Hausdorff space.
-/

open Set Filter Topology TopologicalSpace

namespace UndergradKB.Topology
namespace CantorBrouwer

variable {X : Type*} [TopologicalSpace X]

/-- In a space without isolated points and with a totally separated topology, a nonempty clopen set
can be cut into two nonempty clopen pieces. -/
theorem exists_split [TotallySeparatedSpace X] (hper : ∀ x : X, ¬ IsOpen ({x} : Set X))
    {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ A : Set X, IsClopen A ∧ A ⊆ U ∧ A.Nonempty ∧ (U \ A).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have : ∃ y ∈ U, y ≠ x := by
    by_contra! h
    have : U = {x} := Set.eq_singleton_iff_unique_mem.2 ⟨hx, h⟩
    exact hper x (this ▸ hU.isOpen)
  obtain ⟨y, hy, hyx⟩ := this
  obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated hyx.symm
  exact ⟨U ∩ C, hU.inter hC, inter_subset_left, ⟨x, hx, hxC⟩, ⟨y, hy, fun h => hyC h.2⟩⟩

section Tree

variable (B : ℕ → Set X)

open Classical in
/-- The cut of a node `U` at depth `n`. -/
noncomputable def cut (hper : ∀ x : X, ¬ IsOpen ({x} : Set X)) [TotallySeparatedSpace X]
    (n : ℕ) (U : Set X) : Set X :=
  if (U ∩ B n).Nonempty ∧ (U \ B n).Nonempty then U ∩ B n
  else if h : IsClopen U ∧ U.Nonempty then (exists_split hper h.1 h.2).choose else U

variable [TotallySeparatedSpace X] (hper : ∀ x : X, ¬ IsOpen ({x} : Set X))

open Classical in
/-- The piece of a node `U` selected by the bit `b`. -/
noncomputable def piece (n : ℕ) (U : Set X) (b : Bool) : Set X :=
  if b then cut B hper n U else U \ cut B hper n U

/-- The node of depth `n` along the branch `s`. -/
noncomputable def node (s : ℕ → Bool) : ℕ → Set X
  | 0 => univ
  | n + 1 => piece B hper n (node s n) (s n)

variable {B} (hB : ∀ n, IsClopen (B n))
include hB

theorem cut_spec {n : ℕ} {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) :
    IsClopen (cut B hper n U) ∧ cut B hper n U ⊆ U ∧ (cut B hper n U).Nonempty ∧
      (U \ cut B hper n U).Nonempty := by
  unfold cut
  split_ifs with h1 h2
  · exact ⟨hU.inter (hB n), inter_subset_left, h1.1, by
      obtain ⟨y, hy, hyB⟩ := h1.2
      exact ⟨y, hy, fun h => hyB h.2⟩⟩
  · exact (exists_split hper h2.1 h2.2).choose_spec
  · exact absurd ⟨hU, hne⟩ h2

theorem piece_spec {n : ℕ} {U : Set X} (hU : IsClopen U) (hne : U.Nonempty) (b : Bool) :
    IsClopen (piece B hper n U b) ∧ piece B hper n U b ⊆ U ∧ (piece B hper n U b).Nonempty := by
  obtain ⟨h1, h2, h3, h4⟩ := cut_spec hper hB (n := n) hU hne
  cases b
  · exact ⟨hU.diff h1, sdiff_subset, h4⟩
  · exact ⟨h1, h2, h3⟩

theorem node_spec [Nonempty X] (s : ℕ → Bool) (n : ℕ) : IsClopen (node B hper s n) ∧ (node B hper s n).Nonempty
    ∧ node B hper s (n + 1) ⊆ node B hper s n := by
  induction n with
  | zero =>
    have h := piece_spec hper hB (n := 0) isClopen_univ univ_nonempty (s 0)
    exact ⟨isClopen_univ, univ_nonempty, h.2.1⟩
  | succ n ih =>
    have h := piece_spec hper hB (n := n) ih.1 ih.2.1 (s n)
    have h' := piece_spec hper hB (n := n + 1) h.1 h.2.2 (s (n + 1))
    exact ⟨h.1, h.2.2, h'.2.1⟩

omit hB in
theorem node_congr {s t : ℕ → Bool} {n : ℕ} (h : ∀ i < n, s i = t i) :
    node B hper s n = node B hper t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [node]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

omit hB in
theorem piece_disjoint (n : ℕ) (U : Set X) :
    Disjoint (piece B hper n U true) (piece B hper n U false) := by
  simp only [piece, Bool.false_eq_true, ↓reduceIte]
  exact disjoint_sdiff_right

theorem antitone_node [Nonempty X] (s : ℕ → Bool) : Antitone (node B hper s) :=
  antitone_nat_of_succ_le fun n => (node_spec hper hB s n).2.2

variable [CompactSpace X] [T2Space X]

omit [T2Space X] in
theorem nonempty_iInter_node [Nonempty X] (s : ℕ → Bool) : (⋂ n, node B hper s n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun n => (node_spec hper hB s n).2.2) (fun n => (node_spec hper hB s n).2.1)
    (node_spec hper hB s 0).1.isClosed.isCompact (fun n => (node_spec hper hB s n).1.isClosed)

omit hB [CompactSpace X] [T2Space X] in
theorem subsingleton_iInter_node [Nonempty X] (hsep : ∀ x y : X, x ≠ y → ∃ n, x ∈ B n ∧ y ∉ B n)
    (s : ℕ → Bool) : (⋂ n, node B hper s n).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨n, hxB, hyB⟩ := hsep x y hxy
  rw [mem_iInter] at hx hy
  have hcut : cut B hper n (node B hper s n) = node B hper s n ∩ B n := by
    unfold cut
    simp only [show (node B hper s n ∩ B n).Nonempty ∧ (node B hper s n \ B n).Nonempty from
      ⟨⟨x, hx n, hxB⟩, ⟨y, hy n, hyB⟩⟩, and_self, ↓reduceIte]
  have hx1 := hx (n + 1)
  have hy1 := hy (n + 1)
  simp only [node, piece, hcut] at hx1 hy1
  by_cases h : s n = true
  · simp only [h, ↓reduceIte] at hy1
    exact hyB hy1.2
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hx1
    exact hx1.2 ⟨hx n, hxB⟩

end Tree

/-- **Brouwer's theorem.**  A nonempty compact Hausdorff, second countable, totally disconnected
space without isolated points is homeomorphic to the Cantor space `ℕ → Bool`. -/
theorem nonempty_homeomorph_cantor_of_perfect [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] [Nonempty X]
    (hper : ∀ x : X, ¬ IsOpen ({x} : Set X)) : Nonempty (X ≃ₜ (ℕ → Bool)) := by
  classical
  have : TotallySeparatedSpace X := inferInstance
  -- an enumeration of the clopen sets
  have : Countable (Clopens X) := Clopens.countable_iff_secondCountable.2 inferInstance
  obtain ⟨E, hE⟩ := exists_surjective_nat (Clopens X)
  let B : ℕ → Set X := fun n => E n
  have hB : ∀ n, IsClopen (B n) := fun n => (E n).isClopen
  have hsep : ∀ x y : X, x ≠ y → ∃ n, x ∈ B n ∧ y ∉ B n := by
    intro x y hxy
    obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated hxy
    obtain ⟨n, hn⟩ := hE ⟨C, hC⟩
    exact ⟨n, by simp [B, hn, hxC], by simpa [B, hn] using hyC⟩
  let φ : (ℕ → Bool) → X := fun s => (nonempty_iInter_node hper hB s).some
  have hφ : ∀ s n, φ s ∈ node B hper s n := fun s n =>
    mem_iInter.1 (nonempty_iInter_node hper hB s).some_mem n
  have hφ' : ∀ s, ∀ x, (∀ n, x ∈ node B hper s n) → φ s = x := fun s x hx =>
    subsingleton_iInter_node hper hsep s (mem_iInter.2 (hφ s)) (mem_iInter.2 hx)
  -- injective
  have hinj : Function.Injective φ := by
    intro s t hst
    by_contra hne
    have hex : ∃ n, s n ≠ t n := by
      by_contra! h
      exact hne (funext h)
    let n := Nat.find hex
    have hn : s n ≠ t n := Nat.find_spec hex
    have hlt : ∀ i < n, s i = t i := fun i hi => by
      have := Nat.find_min hex hi
      push Not at this
      exact this
    have e := node_congr (B := B) hper hlt
    have h1 := hφ s (n + 1)
    have h2 := hφ t (n + 1)
    simp only [node] at h1 h2
    rw [e, hst] at h1
    have hd := piece_disjoint (B := B) hper n (node B hper t n)
    cases hs : s n <;> cases ht : t n <;> rw [hs] at h1 <;> rw [ht] at h2
    · exact hn (hs.trans ht.symm)
    · exact Set.disjoint_left.1 hd h2 h1
    · exact Set.disjoint_left.1 hd h1 h2
    · exact hn (hs.trans ht.symm)
  -- surjective
  have hsurj : Function.Surjective φ := by
    intro x
    let W : ℕ → Set X := fun n => Nat.rec univ
      (fun n W => if x ∈ cut B hper n W then cut B hper n W else W \ cut B hper n W) n
    let b : ℕ → Bool := fun n => decide (x ∈ cut B hper n (W n))
    have hW : ∀ n, node B hper b n = W n ∧ x ∈ W n := by
      intro n
      induction n with
      | zero => exact ⟨rfl, mem_univ x⟩
      | succ n ih =>
        have hWs : W (n + 1) = if x ∈ cut B hper n (W n) then cut B hper n (W n)
            else W n \ cut B hper n (W n) := rfl
        simp only [node, ih.1, hWs, piece, b]
        by_cases hx : x ∈ cut B hper n (W n)
        · simp [hx]
        · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte, true_and]
          exact ⟨ih.2, hx⟩
    exact ⟨b, hφ' b x fun n => (hW n).1 ▸ (hW n).2⟩
  -- continuous
  have hcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
    rintro U ⟨hsU, hUo⟩
    have hInter : (⋂ n, node B hper s n) = {φ s} :=
      ((subsingleton_iInter_node hper hsep s).eq_singleton_of_mem (mem_iInter.2 (hφ s)))
    obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (antitone_node hper hB s).directed_ge
      (fun n => (node_spec hper hB s n).1.isClosed.isCompact)
      (fun n => (node_spec hper hB s n).1.isClosed)
      (by rw [hInter, nhdsSet_singleton]; exact hUo.mem_nhds hsU)
    have hev : ∀ᶠ t in 𝓝 s, ∀ i ∈ Finset.range n, t i = s i := by
      rw [Filter.eventually_all_finset]
      intro i _
      exact (continuous_apply i).continuousAt.preimage_mem_nhds
        ((isOpen_discrete {s i}).mem_nhds rfl)
    filter_upwards [hev] with t ht
    have e := node_congr (B := B) hper (s := t) (t := s) (n := n) fun i hi => ht i (Finset.mem_range.2 hi)
    exact hn (e ▸ hφ t n)
  exact ⟨(hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm⟩

end CantorBrouwer

open CantorBrouwer

/-- Brouwer's theorem, Cantor set form: a nonempty compact metrizable totally disconnected space
without isolated points is homeomorphic to the Cantor set. -/
@[kb "morris2024" "Exercises 9.1 #2, p. 225"]
theorem nonempty_homeomorph_cantorSet_of_perfect {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MetrizableSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (hper : ∀ x : X, ¬ IsOpen ({x} : Set X)) : Nonempty (X ≃ₜ cantorSet) := by
  let _ := metrizableSpaceMetric X
  obtain ⟨h⟩ := nonempty_homeomorph_cantor_of_perfect hper
  exact ⟨h.trans cantorSetHomeomorphNatToBool.symm⟩

/-- In an infinite compact Hausdorff group no point is isolated. -/
theorem not_isOpen_singleton_of_infinite_compact_group {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Infinite G] (x : G) : ¬ IsOpen ({x} : Set G) := by
  intro hx
  have h1 : IsOpen ({1} : Set G) := by
    have : (fun y => x * y) ⁻¹' {x} = {1} := by ext y; simp
    rw [← this]
    exact hx.preimage (continuous_const.mul continuous_id)
  have : DiscreteTopology G := by
    refine discreteTopology_iff_isOpen_singleton.2 fun g => ?_
    have : (fun y => g⁻¹ * y) ⁻¹' {1} = {g} := by
      ext y; simp [eq_comm]
    rw [← this]
    exact h1.preimage (continuous_const.mul continuous_id)
  exact (finite_of_compact_of_discrete (X := G)).false

/-- **Morris, Theorem A5.0.23 (TP-496), metrizable case.**  The underlying space of an infinite,
totally disconnected, compact, metrizable (Hausdorff) group is homeomorphic to the Cantor cube
`{0,1}^ℵ₀ = ℕ → Bool`.  (The book's theorem covers all weights, with the Cantor cube `{0,1}^m`;
the case of uncountable weight is not proved here.) -/
@[kb "morris2024" "Theorem A5.0.23, p. 509"]
theorem nonempty_homeomorph_cantor_of_group {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MetrizableSpace G] [TotallyDisconnectedSpace G]
    [Infinite G] : Nonempty (G ≃ₜ (ℕ → Bool)) := by
  let _ := metrizableSpaceMetric G
  exact nonempty_homeomorph_cantor_of_perfect not_isOpen_singleton_of_infinite_compact_group

end UndergradKB.Topology
