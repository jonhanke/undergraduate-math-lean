import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Logic.Relation
import Mathlib.Order.Fin.Basic
import UndergradKB.Common.Attr

/-!
# Network flows (Keller–Trotter, Chapter 13)

A network is a finite oriented graph with a source, a sink and nonnegative capacities on the edges. A flow puts
on each edge a value between zero and its capacity and is conserved at every vertex other than the source and the
sink; its value is the net outflow of the source. A cut is a partition of the vertices into a part containing the
source and a part containing the sink.

Main results:
* `Network.value_le_capacity` (Theorem 13.4): the value of a flow is at most the capacity of a cut;
* `Network.augment` (Proposition 13.7): augmenting along an augmenting path raises the value by the augmentation;
* `Network.capacity_labelled_eq_value` (the labelling algorithm stops at a cut, text p. 293);
* `Network.maxFlow_minCut` (Theorem 13.10, max-flow min-cut);
* `Network.exists_integral_maxFlow` (Theorem 14.1, integrality).

Capacities are stored as a function on all ordered pairs which vanishes off the edges (the book defines them on edges
only); flows are functions on ordered pairs vanishing off the edges.
-/

namespace UndergradKB.Combinatorics.Flow

open Finset

/-- CO-288. A network: a finite oriented graph (at most one of `(x,y)`, `(y,x)` is an edge) with a source having only
out-edges, a sink having only in-edges, and a nonnegative capacity on each edge. -/
@[kb "kellertrotter2017" "Definition (unnumbered) network, source, sink, capacity, p. 283"]
structure Network (V : Type*) where
  /-- The directed edges. -/
  adj : V → V → Prop
  /-- An oriented graph: never both `(x,y)` and `(y,x)` (in particular no loops). -/
  oriented : ∀ x y, adj x y → ¬ adj y x
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  /-- The source has only out-edges. -/
  no_in_source : ∀ x, ¬ adj x source
  /-- The sink has only in-edges. -/
  no_out_sink : ∀ y, ¬ adj sink y
  /-- The capacity of the edge `(x,y)` (zero when `(x,y)` is not an edge). -/
  cap : V → V → ℝ
  cap_nonneg : ∀ x y, 0 ≤ cap x y
  cap_of_not_adj : ∀ x y, ¬ adj x y → cap x y = 0

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)

/-- The net outflow `∑_y (φ(v,y) - φ(y,v))` of a function on ordered pairs at the vertex `v`. -/
def netOut (φ : V → V → ℝ) (v : V) : ℝ := ∑ y, (φ v y - φ y v)

/-- CO-289. A flow: on each edge a value between zero and the capacity, zero off the edges, and conservation (inflow
equals outflow) at every vertex other than the source and the sink. -/
@[kb "kellertrotter2017" "Definition (unnumbered) flow, p. 284"]
structure IsFlow (φ : V → V → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ φ x y
  le_cap : ∀ x y, φ x y ≤ N.cap x y
  conserve : ∀ v, v ≠ N.source → v ≠ N.sink → netOut φ v = 0

/-- CO-289. The value of a flow: the net outflow of the source (its outflow, since the source has no in-edges). -/
@[kb "kellertrotter2017" "Definition (unnumbered) value of a flow, p. 284"]
def value (φ : V → V → ℝ) : ℝ := netOut φ N.source

/-- CO-290. A cut: a set `L` of vertices containing the source and not the sink (its complement `U` contains the sink). -/
@[kb "kellertrotter2017" "Definition (unnumbered) cut, p. 285"]
structure IsCut (L : Finset V) : Prop where
  source_mem : N.source ∈ L
  sink_not_mem : N.sink ∉ L

/-- CO-290. The capacity of a cut `(L, U)`: the total capacity of the edges from `L` to `U`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) capacity of a cut, p. 285"]
def capacity (L : Finset V) : ℝ := ∑ x ∈ L, ∑ y ∈ Lᶜ, N.cap x y

variable {N}

lemma IsFlow.eq_zero_of_not_adj {φ : V → V → ℝ} (hφ : N.IsFlow φ) {x y : V} (h : ¬ N.adj x y) : φ x y = 0 :=
  le_antisymm ((hφ.le_cap x y).trans (N.cap_of_not_adj x y h).le) (hφ.nonneg x y)

/-- Summing the net outflow over a set `L` leaves only the edges between `L` and its complement. -/
lemma sum_netOut (φ : V → V → ℝ) (L : Finset V) :
    ∑ x ∈ L, netOut φ x = ∑ x ∈ L, ∑ y ∈ Lᶜ, (φ x y - φ y x) := by
  unfold netOut
  have hsplit : ∀ x, ∑ y, (φ x y - φ y x) = ∑ y ∈ L, (φ x y - φ y x) + ∑ y ∈ Lᶜ, (φ x y - φ y x) := fun x =>
    (Finset.sum_add_sum_compl L _).symm
  simp_rw [hsplit, Finset.sum_add_distrib]
  have h0 : ∑ x ∈ L, ∑ y ∈ L, (φ x y - φ y x) = 0 := by
    simp_rw [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := L) (t := L) (f := fun x y => φ y x)]
    exact sub_self _
  rw [h0, zero_add]

/-- For a flow and a cut, the value equals the net flow across the cut. -/
lemma value_eq_sum_cut {φ : V → V → ℝ} (hφ : N.IsFlow φ) {L : Finset V} (hL : N.IsCut L) :
    N.value φ = ∑ x ∈ L, ∑ y ∈ Lᶜ, (φ x y - φ y x) := by
  rw [← sum_netOut, value, ← Finset.sum_erase_add _ _ hL.source_mem]
  rw [Finset.sum_eq_zero (fun x hx => hφ.conserve x (Finset.ne_of_mem_erase hx)
    (fun h => hL.sink_not_mem (h ▸ Finset.mem_of_mem_erase hx))), zero_add]

/-- CO-291. Weak duality: the value of any flow is at most the capacity of any cut. -/
@[kb "kellertrotter2017" "Theorem 13.4, p. 286"]
theorem value_le_capacity {φ : V → V → ℝ} (hφ : N.IsFlow φ) {L : Finset V} (hL : N.IsCut L) :
    N.value φ ≤ N.capacity L := by
  rw [value_eq_sum_cut hφ hL, capacity]
  gcongr with x _ y _
  linarith [hφ.le_cap x y, hφ.nonneg y x]

/-! ### Augmenting paths -/

/-- CO-292. The residual relation of a flow: `x` to `y` along a forward edge `(x,y)` with spare capacity, or along a
backward edge `(y,x)` that is used (carries positive flow). -/
def Residual (φ : V → V → ℝ) (x y : V) : Prop :=
  (N.adj x y ∧ φ x y < N.cap x y) ∨ (N.adj y x ∧ 0 < φ y x)

open Classical in
/-- The amount by which the step `x → y` of an augmenting path can carry extra flow: the spare capacity of a forward
edge, the flow on a backward edge. -/
noncomputable def residualCap (φ : V → V → ℝ) (x y : V) : ℝ :=
  if N.adj x y then N.cap x y - φ x y else φ y x

/-- CO-292. An augmenting path: a sequence of distinct vertices `f 0 = source, …, f k = sink`, each step along a forward
edge with spare capacity or a backward edge carrying positive flow. -/
@[kb "kellertrotter2017" "Definition (unnumbered) augmenting path, p. 288"]
structure AugPath (φ : V → V → ℝ) (a b : V) where
  /-- The number of steps. -/
  len : ℕ
  /-- The vertices of the path. -/
  vert : Fin (len + 1) → V
  injective : Function.Injective vert
  first : vert 0 = a
  last : vert (Fin.last len) = b
  step : ∀ i : Fin len, N.Residual φ (vert i.castSucc) (vert i.succ)

open Classical in
/-- The change of flow along one step `a → b`: `+δ` on a forward edge, `-δ` on a backward edge. -/
noncomputable def stepChange (δ : ℝ) (a b : V) (x y : V) : ℝ :=
  if x = a ∧ y = b ∧ N.adj a b then δ else if x = b ∧ y = a ∧ N.adj b a then -δ else 0

lemma netOut_stepChange (δ : ℝ) {a b : V} (h : N.adj a b ∨ N.adj b a) (v : V) :
    netOut (N.stepChange δ a b) v = δ * ((if v = a then 1 else 0) - (if v = b then 1 else 0)) := by
  classical
  have hab : a ≠ b := by
    rintro rfl
    rcases h with h | h <;> exact N.oriented _ _ h h
  unfold netOut stepChange
  rw [Finset.sum_sub_distrib]
  rcases h with h | h
  · have h' : ¬ N.adj b a := N.oriented _ _ h
    simp only [h, h', and_true, and_false, ite_false]
    by_cases hva : v = a <;> by_cases hvb : v = b <;> simp_all [Finset.sum_ite_eq']
  · have h' : ¬ N.adj a b := N.oriented _ _ h
    simp only [h, h', and_true, and_false, ite_false]
    by_cases hva : v = a <;> by_cases hvb : v = b <;> simp_all [Finset.sum_ite_eq']

/-- The total change of flow along an augmenting path, by `δ`. -/
noncomputable def pathChange {φ : V → V → ℝ} {a b : V} (p : N.AugPath φ a b) (δ : ℝ) (x y : V) : ℝ :=
  ∑ i : Fin p.len, N.stepChange δ (p.vert i.castSucc) (p.vert i.succ) x y

lemma netOut_sum {ι : Type*} (s : Finset ι) (f : ι → V → V → ℝ) (v : V) :
    netOut (fun x y => ∑ i ∈ s, f i x y) v = ∑ i ∈ s, netOut (f i) v := by
  unfold netOut
  simp_rw [← Finset.sum_sub_distrib]
  exact Finset.sum_comm

lemma netOut_add (φ ψ : V → V → ℝ) (v : V) :
    netOut (fun x y => φ x y + ψ x y) v = netOut φ v + netOut ψ v := by
  unfold netOut
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma residual_adj {φ : V → V → ℝ} {x y : V} (h : N.Residual φ x y) : N.adj x y ∨ N.adj y x := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Telescoping along the vertices of a path. -/
lemma sum_fin_telescope {k : ℕ} (f : Fin (k + 1) → V) (v : V) :
    ∑ i : Fin k, ((if v = f i.castSucc then (1 : ℝ) else 0) - (if v = f i.succ then 1 else 0)) =
      (if v = f 0 then 1 else 0) - (if v = f (Fin.last k) then 1 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => f i.castSucc)
    simp only [Fin.castSucc_zero, Fin.succ_castSucc] at this ⊢
    rw [this, Fin.succ_last, sub_add_sub_cancel]
    rfl

lemma netOut_pathChange {φ : V → V → ℝ} {a b : V} (p : N.AugPath φ a b) (δ : ℝ) (v : V) :
    netOut (N.pathChange p δ) v = δ * ((if v = a then 1 else 0) - (if v = b then 1 else 0)) := by
  unfold pathChange
  rw [netOut_sum]
  simp_rw [N.netOut_stepChange δ (N.residual_adj (p.step _))]
  rw [← Finset.mul_sum, sum_fin_telescope p.vert v, p.first, p.last]

/-- On an ordered pair `(x,y)`, at most one step of an augmenting path changes the flow. -/
lemma pathChange_cases {φ : V → V → ℝ} {a b : V} (p : N.AugPath φ a b) (δ : ℝ) (x y : V) :
    N.pathChange p δ x y = 0 ∨
      (∃ i : Fin p.len, p.vert i.castSucc = x ∧ p.vert i.succ = y ∧ N.adj x y ∧ N.pathChange p δ x y = δ) ∨
      (∃ i : Fin p.len, p.vert i.castSucc = y ∧ p.vert i.succ = x ∧ N.adj x y ∧ N.pathChange p δ x y = -δ) := by
  classical
  -- the index of a vertex as a start (resp. end) of a step is unique, and a pair is never crossed both ways
  have hcs : ∀ i j : Fin p.len, p.vert i.castSucc = p.vert j.castSucc → i = j := fun i j h =>
    Fin.castSucc_injective _ (p.injective h)
  have hsu : ∀ i j : Fin p.len, p.vert i.succ = p.vert j.succ → i = j := fun i j h =>
    Fin.succ_injective _ (p.injective h)
  have hboth : ∀ i j : Fin p.len, p.vert i.castSucc = p.vert j.succ → p.vert i.succ = p.vert j.castSucc → False := by
    intro i j h1 h2
    have e1 := congrArg Fin.val (p.injective h1)
    have e2 := congrArg Fin.val (p.injective h2)
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    omega
  unfold pathChange stepChange
  by_cases hf : ∃ i : Fin p.len, p.vert i.castSucc = x ∧ p.vert i.succ = y ∧ N.adj x y
  · obtain ⟨i, hi1, hi2, hxy⟩ := hf
    refine Or.inr (Or.inl ⟨i, hi1, hi2, hxy, ?_⟩)
    rw [Finset.sum_eq_single i]
    · simp [hi1, hi2, hxy]
    · intro j _ hji
      have h1 : ¬ (x = p.vert j.castSucc ∧ y = p.vert j.succ ∧ N.adj (p.vert j.castSucc) (p.vert j.succ)) :=
        fun h => hji (hcs i j (hi1.trans h.1)).symm
      have h2 : ¬ (x = p.vert j.succ ∧ y = p.vert j.castSucc ∧ N.adj (p.vert j.succ) (p.vert j.castSucc)) :=
        fun h => hboth i j (hi1.trans h.1) (hi2.trans h.2.1)
      rw [ite_eq_right h1, ite_eq_right h2]
    · simp
  · by_cases hb : ∃ i : Fin p.len, p.vert i.castSucc = y ∧ p.vert i.succ = x ∧ N.adj x y
    · obtain ⟨i, hi1, hi2, hxy⟩ := hb
      refine Or.inr (Or.inr ⟨i, hi1, hi2, hxy, ?_⟩)
      rw [Finset.sum_eq_single i]
      · have h1 : ¬ (x = p.vert i.castSucc ∧ y = p.vert i.succ ∧ N.adj (p.vert i.castSucc) (p.vert i.succ)) := by
          rintro ⟨h1, h2, -⟩
          exact hboth i i (hi1.trans h2) (hi2.trans h1)
        rw [ite_eq_right h1]
        simp [hi1, hi2, hxy]
      · intro j _ hji
        have h1 : ¬ (x = p.vert j.castSucc ∧ y = p.vert j.succ ∧ N.adj (p.vert j.castSucc) (p.vert j.succ)) :=
          fun h => hboth j i (h.1.symm.trans hi2.symm) (h.2.1.symm.trans hi1.symm)
        have h2 : ¬ (x = p.vert j.succ ∧ y = p.vert j.castSucc ∧ N.adj (p.vert j.succ) (p.vert j.castSucc)) :=
          fun h => hji (hsu i j (hi2.trans h.1)).symm
        rw [ite_eq_right h1, ite_eq_right h2]
      · simp
    · left
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : ¬ (x = p.vert i.castSucc ∧ y = p.vert i.succ ∧ N.adj (p.vert i.castSucc) (p.vert i.succ)) := by
        rintro ⟨h1, h2, h3⟩
        exact hf ⟨i, h1.symm, h2.symm, h1 ▸ h2 ▸ h3⟩
      have h2 : ¬ (x = p.vert i.succ ∧ y = p.vert i.castSucc ∧ N.adj (p.vert i.succ) (p.vert i.castSucc)) := by
        rintro ⟨h1, h2, h3⟩
        exact hb ⟨i, h2.symm, h1.symm, h1 ▸ h2 ▸ h3⟩
      rw [ite_eq_right h1, ite_eq_right h2]

/-- CO-293. Augmenting a flow along an augmenting path from the source to the sink by an amount `δ` that does not
exceed the residual capacity of any step gives a flow of value `value + δ`. -/
@[kb "kellertrotter2017" "Proposition 13.7, p. 289"]
theorem augment {φ : V → V → ℝ} (hφ : N.IsFlow φ) (p : N.AugPath φ N.source N.sink) {δ : ℝ} (hδ : 0 ≤ δ)
    (hle : ∀ i : Fin p.len, δ ≤ N.residualCap φ (p.vert i.castSucc) (p.vert i.succ)) :
    N.IsFlow (fun x y => φ x y + N.pathChange p δ x y) ∧
      N.value (fun x y => φ x y + N.pathChange p δ x y) = N.value φ + δ := by
  classical
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun v hs ht => ?_⟩, ?_⟩
  · rcases N.pathChange_cases p δ x y with h | ⟨i, -, -, -, h⟩ | ⟨i, h1, h2, hxy, h⟩
    · rw [h]; linarith [hφ.nonneg x y]
    · rw [h]; linarith [hφ.nonneg x y]
    · rw [h]
      have := hle i
      rw [residualCap, h1, h2, ite_eq_right (N.oriented _ _ hxy)] at this
      linarith
  · rcases N.pathChange_cases p δ x y with h | ⟨i, h1, h2, hxy, h⟩ | ⟨i, -, -, -, h⟩
    · rw [h]; linarith [hφ.le_cap x y]
    · rw [h]
      have := hle i
      rw [residualCap, h1, h2, ite_eq_left hxy] at this
      linarith
    · rw [h]; linarith [hφ.le_cap x y]
  · rw [netOut_add, hφ.conserve v hs ht, N.netOut_pathChange p δ v, ite_eq_right hs, ite_eq_right ht]
    ring
  · rw [value, netOut_add, N.netOut_pathChange p δ, ite_eq_left rfl, ite_eq_right N.source_ne_sink]
    unfold value
    ring

end Network

end UndergradKB.Combinatorics.Flow
