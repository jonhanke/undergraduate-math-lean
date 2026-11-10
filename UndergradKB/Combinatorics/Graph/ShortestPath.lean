import Mathlib.Basic.ENNReal.Operations
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import UndergradKB.Common.Attr

/-!
# Shortest paths in weighted digraphs and Dijkstra's algorithm (Keller–Trotter, Section 12.3)

Model: a digraph on a type `V` with edge lengths `w : V → V → ℝ≥0∞`; the value `⊤` means that
`(x, y)` is not an edge (this is the book's convention `w(x,y) = ∞`).  A `Walk w a b` is a
sequence of vertices from `a` to `b` in which consecutive vertices are joined by an edge; it is a
(directed) path when its vertices are distinct.  The distance `dist w a b` is the infimum of the
lengths of the paths from `a` to `b` (`⊤` if there is none).
-/

open scoped ENNReal

namespace UndergradKB.Combinatorics.ShortestPath

variable {V : Type*} (w : V → V → ℝ≥0∞)

/-- A directed walk from `a` to `b` along finite-length edges of the weighted digraph `w`. -/
inductive Walk : V → V → Type _
  | nil (a : V) : Walk a a
  | cons {a b c : V} : w a b ≠ ⊤ → Walk b c → Walk a c

namespace Walk

variable {w} {a b c d : V}

/-- The length of a walk: the sum of its edge lengths. -/
def len {a b : V} : Walk w a b → ℝ≥0∞
  | nil _ => 0
  | @cons _ _ a b _ _ p => w a b + p.len

/-- The vertices visited by a walk, in order. -/
def support {a b : V} : Walk w a b → List V
  | nil a => [a]
  | @cons _ _ a _ _ _ p => a :: p.support

/-- Concatenation of walks. -/
def append {a b c : V} : Walk w a b → Walk w b c → Walk w a c
  | nil _, q => q
  | cons h p, q => cons h (p.append q)

/-- A (directed) path is a walk whose vertices are pairwise distinct. -/
def IsPath (p : Walk w a b) : Prop := p.support.Nodup

lemma len_append (p : Walk w a b) (q : Walk w b c) : (p.append q).len = p.len + q.len := by
  induction p with
  | nil => simp [append, len]
  | cons h p ih => simp [append, len, ih, add_assoc]

lemma len_ne_top (p : Walk w a b) : p.len ≠ ⊤ := by
  induction p with
  | nil => simp [len]
  | @cons a b c h p ih => simp [len, ih, h]

lemma support_ne_nil (p : Walk w a b) : p.support ≠ [] := by
  cases p <;> simp [support]

lemma support_head (p : Walk w a b) : p.support.head? = some a := by
  cases p <;> simp [support]

lemma support_eq_cons (p : Walk w a b) : p.support = a :: p.support.tail := by
  cases p <;> simp [support]

lemma end_mem_support (p : Walk w a b) : b ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons h p ih => simp [support, ih]

lemma start_mem_support (p : Walk w a b) : a ∈ p.support := by
  cases p <;> simp [support]

lemma support_append (p : Walk w a b) (q : Walk w b c) :
    (p.append q).support = p.support ++ q.support.tail := by
  induction p with
  | nil => simp [append, support, ← q.support_eq_cons]
  | cons h p ih => simp [append, support, ih]

lemma support_append' (p : Walk w a b) (q : Walk w b c) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p with
  | nil => simp [append, support]
  | @cons a b c h p ih =>
    have hne := p.support_ne_nil
    simp only [append, support, ih]
    rw [List.dropLast_cons_of_ne_nil hne]
    rfl

lemma IsPath.of_append_left {p : Walk w a b} {q : Walk w b c} (h : (p.append q).IsPath) :
    p.IsPath := by
  unfold IsPath at *
  rw [support_append] at h
  exact h.sublist (List.sublist_append_left _ _)

lemma IsPath.of_append_right {p : Walk w a b} {q : Walk w b c} (h : (p.append q).IsPath) :
    q.IsPath := by
  unfold IsPath at *
  rw [support_append'] at h
  exact h.sublist (List.sublist_append_right _ _)

/-- Passing to the part of a walk after a vertex `v` of it does not increase the length. -/
lemma exists_suffix (p : Walk w a b) {v : V} (hv : v ∈ p.support) :
    ∃ q : Walk w v b, q.len ≤ p.len ∧ q.support.Sublist p.support := by
  induction p with
  | nil a =>
    simp only [support, List.mem_singleton] at hv
    subst hv
    exact ⟨nil _, le_rfl, List.Sublist.refl _⟩
  | @cons a b c h p ih =>
    simp only [support, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨cons h p, le_rfl, List.Sublist.refl _⟩
    · obtain ⟨q, hq1, hq2⟩ := ih hv
      refine ⟨q, hq1.trans ?_, hq2.cons _⟩
      simp [len]

/-- Every walk can be shortcut to a path that is not longer. -/
lemma exists_isPath_le (p : Walk w a b) : ∃ q : Walk w a b, q.IsPath ∧ q.len ≤ p.len := by
  classical
  induction p with
  | nil a => exact ⟨nil a, by simp [IsPath, support], le_rfl⟩
  | @cons a b c h p ih =>
    obtain ⟨q, hq, hql⟩ := ih
    by_cases ha : a ∈ q.support
    · obtain ⟨q', h1, h2⟩ := q.exists_suffix ha
      refine ⟨q', hq.sublist h2, h1.trans (hql.trans ?_)⟩
      simp [len]
    · refine ⟨cons h q, ?_, ?_⟩
      · simp only [IsPath, support, List.nodup_cons]
        exact ⟨ha, hq⟩
      · simp only [len]
        gcongr

/-- A walk starting in `S` and ending outside `S` has a first edge leaving `S`. -/
lemma exists_exit (S : Set V) (p : Walk w a b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ (z y : V) (p₁ : Walk w a z) (h : w z y ≠ ⊤) (p₂ : Walk w y b),
      z ∈ S ∧ y ∉ S ∧ p = p₁.append (cons h p₂) := by
  induction p with
  | nil => exact absurd ha hb
  | @cons a c b h p ih =>
    by_cases hc : c ∈ S
    · obtain ⟨z, y, p₁, h', p₂, hz, hy, rfl⟩ := ih hc hb
      exact ⟨z, y, cons h p₁, h', p₂, hz, hy, rfl⟩
    · exact ⟨a, c, nil a, h, p, ha, hc, rfl⟩

end Walk

variable {w}

open Walk

/-- CO-278. The distance from `a` to `b`: the infimum of the lengths of the directed paths from
`a` to `b` (`⊤` when there is none). -/
@[kb "kellertrotter2017" "Problem 12.13, p. 270"]
noncomputable def dist (w : V → V → ℝ≥0∞) (a b : V) : ℝ≥0∞ :=
  ⨅ (p : Walk w a b) (_ : p.IsPath), p.len

lemma dist_le_len {a b : V} (p : Walk w a b) : dist w a b ≤ p.len := by
  obtain ⟨q, hq, hql⟩ := p.exists_isPath_le
  exact (iInf₂_le q hq).trans hql

lemma dist_self (a : V) : dist w a a = 0 :=
  le_antisymm ((dist_le_len (nil a)).trans (by simp [len])) zero_le

/-- A shortest path from `a` to `b`: a path whose length is the distance. -/
def Walk.IsShortest {a b : V} (p : Walk w a b) : Prop := p.IsPath ∧ p.len = dist w a b

/-- Triangle inequality along a final edge. -/
lemma dist_le_dist_add {a v x : V} (h : w v x ≠ ⊤) : dist w a x ≤ dist w a v + w v x := by
  unfold dist
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hp => ?_
  exact (dist_le_len (p.append (cons h (nil x)))).trans (by simp [len_append, len])

/-- CO-280. Proposition 12.16: if a shortest path is cut at any vertex, then both the initial and
the final segment are shortest paths (between their endpoints). -/
@[kb "kellertrotter2017" "Proposition 12.16, p. 275"]
theorem Walk.IsShortest.of_append {r u x : V} {Q : Walk w r u} {R : Walk w u x}
    (h : (Q.append R).IsShortest) : Q.IsShortest ∧ R.IsShortest := by
  obtain ⟨hP, hl⟩ := h
  rw [len_append] at hl
  have hQp := hP.of_append_left
  have hRp := hP.of_append_right
  have hRt := R.len_ne_top
  have hQt := Q.len_ne_top
  refine ⟨⟨hQp, le_antisymm ?_ (dist_le_len Q)⟩, ⟨hRp, le_antisymm ?_ (dist_le_len R)⟩⟩
  · refine le_iInf₂ fun Q' _ => ?_
    have := hl.le.trans (dist_le_len (Q'.append R))
    rw [len_append] at this
    exact (ENNReal.add_le_add_iff_right hRt).mp this
  · refine le_iInf₂ fun R' _ => ?_
    have := hl.le.trans (dist_le_len (Q.append R'))
    rw [len_append] at this
    exact (ENNReal.add_le_add_iff_left hQt).mp this

/-! ### Dijkstra's algorithm -/

section Dijkstra

variable [Fintype V] [DecidableEq V]

/-- The temporary vertices, given the list `σ` of permanent vertices. -/
def tempSet (σ : List V) : Finset V := Finset.univ.filter (· ∉ σ)

lemma mem_tempSet {σ : List V} {x : V} : x ∈ tempSet σ ↔ x ∉ σ := by simp [tempSet]

/-- A temporary vertex of least `δ` (an arbitrary one among ties). -/
noncomputable def argminTemp (δ : V → ℝ≥0∞) (σ : List V) (h : (tempSet σ).Nonempty) : V :=
  Classical.choose (Finset.exists_min_image (tempSet σ) δ h)

lemma argminTemp_mem (δ : V → ℝ≥0∞) (σ : List V) (h : (tempSet σ).Nonempty) :
    argminTemp δ σ h ∈ tempSet σ :=
  (Classical.choose_spec (Finset.exists_min_image (tempSet σ) δ h)).1

lemma argminTemp_le (δ : V → ℝ≥0∞) (σ : List V) (h : (tempSet σ).Nonempty) :
    ∀ y ∈ tempSet σ, δ (argminTemp δ σ h) ≤ δ y :=
  (Classical.choose_spec (Finset.exists_min_image (tempSet σ) δ h)).2

lemma tempSet_card_lt {σ : List V} {x : V} (hx : x ∈ tempSet σ) :
    (tempSet (σ ++ [x])).card < (tempSet σ).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, hx, by simp [mem_tempSet]⟩
  · intro y hy
    simp only [mem_tempSet, List.mem_append, not_or] at hy ⊢
    exact hy.1

/-- The relaxation step: after `x` has become permanent (`σ` is the new list of permanent
vertices), every temporary `y` gets `δ y := min (δ y) (δ x + w x y)`. -/
def relax (w : V → V → ℝ≥0∞) (σ : List V) (δ : V → ℝ≥0∞) (x : V) : V → ℝ≥0∞ :=
  fun y => if y ∈ σ then δ y else min (δ y) (δ x + w x y)

/-- Dijkstra's algorithm from the permanent list `σ` and the tentative distances `δ`: while a
temporary vertex remains, make a temporary vertex of least `δ` permanent (append it to `σ`) and
relax its out-edges.  Terminates by well-founded recursion on the number of temporary vertices.
Returns the list `σ` of permanent vertices in the order chosen, together with the final `δ`. -/
noncomputable def dijkstraAux (w : V → V → ℝ≥0∞) (σ : List V) (δ : V → ℝ≥0∞) :
    List V × (V → ℝ≥0∞) :=
  if h : (tempSet σ).Nonempty then
    dijkstraAux w (σ ++ [argminTemp δ σ h])
      (relax w (σ ++ [argminTemp δ σ h]) δ (argminTemp δ σ h))
  else (σ, δ)
termination_by (tempSet σ).card
decreasing_by exact tempSet_card_lt (argminTemp_mem δ σ h)

/-- CO-279. Dijkstra's algorithm (Algorithm 12.14) with root `r`.  Initialization: `σ = (r)`,
`δ r = 0` and `δ x = w r x` for `x ≠ r`; then repeat the inductive step. -/
@[kb "kellertrotter2017" "Algorithm 12.14, p. 270"]
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (r : V) : List V × (V → ℝ≥0∞) :=
  dijkstraAux w [r] (fun x => if x = r then 0 else w r x)

/-- The invariant of the algorithm: the permanent vertices have their true distance, the
temporary ones the best distance via a last edge from a permanent vertex, and permanent `δ`-values
are at most the temporary ones. -/
structure Inv (w : V → V → ℝ≥0∞) (r : V) (σ : List V) (δ : V → ℝ≥0∞) : Prop where
  nodup : σ.Nodup
  head : σ.head? = some r
  perm : ∀ v ∈ σ, δ v = dist w r v
  temp : ∀ y ∉ σ, δ y = ⨅ v ∈ σ, (dist w r v + w v y)
  le : ∀ v ∈ σ, ∀ y ∉ σ, δ v ≤ δ y
  sorted : (σ.map δ).Pairwise (· ≤ ·)
  path : ∀ v ∈ σ, dist w r v ≠ ⊤ → ∃ p : Walk w r v, p.IsShortest

omit [Fintype V] in
lemma Inv.init (w : V → V → ℝ≥0∞) (r : V) :
    Inv w r [r] (fun x => if x = r then 0 else w r x) where
  nodup := by simp
  head := by simp
  perm := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    simp [dist_self]
  temp := by
    intro y hy
    simp only [List.mem_singleton] at hy
    simp [hy, dist_self]
  le := by
    intro v hv y hy
    simp only [List.mem_singleton] at hv
    subst hv
    simp
  sorted := by simp
  path := by
    intro v hv _
    simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨nil v, by simp [IsPath, support], by simp [len, dist_self]⟩

omit [Fintype V] [DecidableEq V] in
/-- A finite infimum over a nonempty list is attained. -/
lemma exists_mem_iInf_eq (σ : List V) (hσ : σ ≠ []) (f : V → ℝ≥0∞) :
    ∃ v ∈ σ, ⨅ u ∈ σ, f u = f v := by
  classical
  have hne : σ.toFinset.Nonempty := by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hσ
    exact ⟨a, by simp⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image σ.toFinset f hne
  refine ⟨v, List.mem_toFinset.mp hv, le_antisymm (iInf₂_le v (List.mem_toFinset.mp hv)) ?_⟩
  exact le_iInf₂ fun u hu => hmin u (List.mem_toFinset.mpr hu)

omit [Fintype V] [DecidableEq V] in
lemma Inv.key {w : V → V → ℝ≥0∞} {r : V} {σ : List V} {δ : V → ℝ≥0∞} (hI : Inv w r σ δ)
    {x : V} (hx : x ∉ σ) (hmin : ∀ y ∉ σ, δ x ≤ δ y) : δ x = dist w r x := by
  apply le_antisymm
  · have hr : r ∈ σ := List.mem_of_mem_head? hI.head
    unfold dist
    refine le_iInf₂ fun p _ => ?_
    obtain ⟨z, y, p₁, h, p₂, hz, hy, rfl⟩ := p.exists_exit {v | v ∈ σ} hr hx
    calc δ x ≤ δ y := hmin y hy
      _ = ⨅ v ∈ σ, (dist w r v + w v y) := hI.temp y hy
      _ ≤ dist w r z + w z y := iInf₂_le z hz
      _ ≤ p₁.len + w z y := by gcongr; exact dist_le_len p₁
      _ ≤ (p₁.append (cons h p₂)).len := by
        rw [len_append]; simp only [len]; rw [← add_assoc]; exact le_self_add
  · rw [hI.temp x hx]
    refine le_iInf₂ fun v hv => ?_
    by_cases h : w v x = ⊤
    · simp [h]
    · exact dist_le_dist_add h

omit [Fintype V] in
lemma Inv.step {w : V → V → ℝ≥0∞} {r : V} {σ : List V} {δ : V → ℝ≥0∞} (hI : Inv w r σ δ)
    {x : V} (hx : x ∉ σ) (hmin : ∀ y ∉ σ, δ x ≤ δ y) :
    Inv w r (σ ++ [x]) (relax w (σ ++ [x]) δ x) := by
  have hkey := hI.key hx hmin
  have hrel : ∀ v ∈ σ ++ [x], relax w (σ ++ [x]) δ x v = δ v := fun v hv => by simp [relax, hv]
  have hrel' : ∀ y ∉ σ ++ [x], relax w (σ ++ [x]) δ x y = min (δ y) (δ x + w x y) :=
    fun y hy => by simp [relax, hy]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_append, hI.nodup, List.nodup_singleton, true_and]
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    exact hx (hab ▸ ha)
  · simp [List.head?_append, hI.head]
  · intro v hv
    rw [hrel v hv]
    rcases List.mem_append.mp hv with hv | hv
    · exact hI.perm v hv
    · simp only [List.mem_singleton] at hv
      subst hv
      exact hkey
  · intro y hy
    rw [hrel' y hy]
    have hy' : y ∉ σ := fun h => hy (List.mem_append_left _ h)
    rw [hI.temp y hy', hkey]
    simp only [List.mem_append, List.mem_singleton, iInf_or, iInf_inf_eq, iInf_iInf_eq_left]
  · intro v hv y hy
    have hy' : y ∉ σ := fun h => hy (List.mem_append_left _ h)
    rw [hrel v hv, hrel' y hy]
    rcases List.mem_append.mp hv with hv | hv
    · exact le_min (hI.le v hv y hy') ((hI.le v hv x hx).trans le_self_add)
    · simp only [List.mem_singleton] at hv
      subst hv
      exact le_min (hmin y hy') le_self_add
  · rw [List.map_append, List.map_singleton, hrel x (by simp)]
    have : σ.map (relax w (σ ++ [x]) δ x) = σ.map δ :=
      List.map_congr_left fun v hv => hrel v (List.mem_append_left _ hv)
    rw [this, List.pairwise_append]
    refine ⟨hI.sorted, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact hI.le v hv x hx
  · intro v hv hfin
    rcases List.mem_append.mp hv with hv | hv
    · exact hI.path v hv hfin
    · simp only [List.mem_singleton] at hv
      subst hv
      have hne : σ ≠ [] := fun h => by simpa [h] using hI.head
      obtain ⟨u, hu, hu'⟩ := exists_mem_iInf_eq σ hne fun u => dist w r u + w u v
      have hxu : dist w r u + w u v = dist w r v := by rw [← hkey, hI.temp v hx, hu']
      have h1 : w u v ≠ ⊤ := fun h => hfin (by rw [← hxu, h]; simp)
      have h2 : dist w r u ≠ ⊤ := fun h => hfin (by rw [← hxu, h]; simp)
      obtain ⟨p, hp⟩ := hI.path u hu h2
      obtain ⟨q, hq, hql⟩ := (p.append (cons h1 (nil v))).exists_isPath_le
      refine ⟨q, hq, le_antisymm ?_ (dist_le_len q)⟩
      refine hql.trans ?_
      rw [len_append, hp.2]
      simp [len, hxu]

theorem dijkstraAux_spec (w : V → V → ℝ≥0∞) (r : V) :
    ∀ (n : ℕ) (σ : List V) (δ : V → ℝ≥0∞), (tempSet σ).card = n → Inv w r σ δ →
      Inv w r (dijkstraAux w σ δ).1 (dijkstraAux w σ δ).2 ∧ ∀ x, x ∈ (dijkstraAux w σ δ).1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ δ hn hI
    rw [dijkstraAux]
    split_ifs with h
    · have hxm := argminTemp_mem δ σ h
      refine ih _ (hn ▸ tempSet_card_lt hxm) _ _ rfl ?_
      exact hI.step (mem_tempSet.mp hxm) fun y hy => argminTemp_le δ σ h y (mem_tempSet.mpr hy)
    · refine ⟨hI, fun x => ?_⟩
      by_contra hx
      exact h ⟨x, mem_tempSet.mpr hx⟩

/-- All the information about a finished run of Dijkstra's algorithm. -/
theorem dijkstra_spec (w : V → V → ℝ≥0∞) (r : V) :
    Inv w r (dijkstra w r).1 (dijkstra w r).2 ∧ ∀ x, x ∈ (dijkstra w r).1 :=
  dijkstraAux_spec w r _ _ _ rfl (Inv.init w r)

/-- CO-281. Proposition 12.17: the permanent vertices `v₁, v₂, …, vₙ`, in the order in which the
algorithm chooses them, satisfy `δ v₁ ≤ δ v₂ ≤ ⋯ ≤ δ vₙ` (here stated for all pairs `i < j`).
Moreover the list is an enumeration of `V` without repetition, starting with the root. -/
@[kb "kellertrotter2017" "Proposition 12.17, p. 275"]
theorem dijkstra_sorted (w : V → V → ℝ≥0∞) (r : V) :
    ((dijkstra w r).1.map (dijkstra w r).2).Pairwise (· ≤ ·) ∧ (dijkstra w r).1.Nodup ∧
      (dijkstra w r).1.head? = some r ∧ ∀ x, x ∈ (dijkstra w r).1 :=
  have h := dijkstra_spec w r
  ⟨h.1.sorted, h.1.nodup, h.1.head, h.2⟩

/-- CO-282. Theorem 12.18: when Dijkstra's algorithm terminates, `δ x` is the distance from the
root `r` to `x`, for every vertex `x` (it is `⊤` exactly for the unreachable vertices), and
whenever `x` is reachable there is a shortest path from `r` to `x`.  (The algorithm here does
not carry the paths `P x` along; their existence is part of the invariant.) -/
@[kb "kellertrotter2017" "Theorem 12.18, p. 275"]
theorem dijkstra_dist (w : V → V → ℝ≥0∞) (r x : V) :
    (dijkstra w r).2 x = dist w r x ∧ (dist w r x ≠ ⊤ → ∃ p : Walk w r x, p.IsShortest) := by
  obtain ⟨hI, hall⟩ := dijkstra_spec w r
  exact ⟨hI.perm x (hall x), hI.path x (hall x)⟩

/-- CO-278. In a finite digraph the distance is attained by a path whenever there is a path. -/
@[kb "kellertrotter2017" "Problem 12.13, p. 270"]
theorem exists_isShortest (w : V → V → ℝ≥0∞) (a b : V) (h : dist w a b ≠ ⊤) :
    ∃ p : Walk w a b, p.IsShortest :=
  (dijkstra_dist w a b).2 h

end Dijkstra

end UndergradKB.Combinatorics.ShortestPath
