import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UndergradKB.Common.Attr

/-!
# Graphs of large girth and large chromatic number (Keller–Trotter, Theorem 11.7)

* CO-250: for all `g` and `t` there is a finite graph with chromatic number `> t` and girth `> g`.

Proof by the deletion method.  The random graph `G(n, p)` is realised as weighted counting over
all sets `S` of potential edges (`Sym2 (Fin n)`) with weight `p^|S| (1-p)^(N-|S|)`.  With `n = N^(2r)`
and `p = N/n` one shows that, with positive probability, the number of short cycles is below `n/2`
while there is no independent set of size `a`, where `a ≈ (2/p) log (2n)` is below `n/(2t)`.
Deleting a vertex from every short cycle leaves a graph with the required properties.
-/

namespace UndergradKB.Combinatorics

open Finset SimpleGraph

set_option linter.unusedSectionVars false

namespace ErdosGirth

/-! ### Product weights on subsets of a finite set of potential edges -/

section Weights

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The probability of the edge set `S` when each element is included independently with
probability `p`. -/
noncomputable def wt (p : ℝ) (S : Finset E) : ℝ := p ^ S.card * (1 - p) ^ (Fintype.card E - S.card)

lemma wt_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset E) : 0 ≤ wt p S :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sum_wt (p : ℝ) : ∑ S : Finset E, wt p S = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset E)
  rw [Finset.powerset_univ] at h
  simpa [wt] using h

/-- Probability that all of `F` is present and none of `D` is. -/
lemma sum_wt_cond (p : ℝ) (F D : Finset E) (hFD : Disjoint F D) :
    ∑ S ∈ univ.filter (fun S : Finset E => F ⊆ S ∧ Disjoint S D), wt p S =
      p ^ F.card * (1 - p) ^ D.card := by
  set U : Finset E := (F ∪ D)ᶜ with hUdef
  have hcFD : (F ∪ D).card = F.card + D.card := Finset.card_union_of_disjoint hFD
  have hU : U.card = Fintype.card E - (F.card + D.card) := by
    rw [hUdef, Finset.card_compl, hcFD]
  have hle : F.card + D.card ≤ Fintype.card E := by
    rw [← hcFD]; exact Finset.card_le_univ _
  have himg : univ.filter (fun S : Finset E => F ⊆ S ∧ Disjoint S D) =
      U.powerset.image (fun T => F ∪ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · rintro ⟨hF, hD⟩
      refine ⟨S \ F, ?_, Finset.union_sdiff_of_subset hF⟩
      intro x hx
      rw [Finset.mem_sdiff] at hx
      simp only [hUdef, Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨hx.2, fun hxD => Finset.disjoint_left.mp hD hx.1 hxD⟩
    · rintro ⟨T, hT, rfl⟩
      refine ⟨Finset.subset_union_left, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx hxD
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp hFD hx hxD
      · have := hT hx
        simp only [hUdef, Finset.mem_compl, Finset.mem_union, not_or] at this
        exact this.2 hxD
  have hinj : Set.InjOn (fun T => F ∪ T) (U.powerset : Set (Finset E)) := by
    intro T hT T' hT' h
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hT hT'
    have hnot : ∀ x ∈ U, x ∉ F := by
      intro x hx
      simp only [hUdef, Finset.mem_compl, Finset.mem_union, not_or] at hx
      exact hx.1
    have h : F ∪ T = F ∪ T' := h
    ext x
    constructor
    · intro hx
      have : x ∈ F ∪ T' := h ▸ Finset.mem_union_right F hx
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd h' (hnot x (hT hx))
      · exact h'
    · intro hx
      have : x ∈ F ∪ T := h.symm ▸ Finset.mem_union_right F hx
      rcases Finset.mem_union.mp this with h' | h'
      · exact absurd h' (hnot x (hT' hx))
      · exact h'
  rw [himg, Finset.sum_image hinj]
  have key : ∀ T ∈ U.powerset, wt p (F ∪ T) =
      p ^ F.card * (1 - p) ^ D.card * (p ^ T.card * (1 - p) ^ (U.card - T.card)) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hTF : Disjoint F T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      have := hT hxT
      simp only [hUdef, Finset.mem_compl, Finset.mem_union, not_or] at this
      exact this.1 hx
    have hcT : T.card ≤ U.card := Finset.card_le_card hT
    unfold wt
    rw [Finset.card_union_of_disjoint hTF]
    have e1 : Fintype.card E - (F.card + T.card) = D.card + (U.card - T.card) := by omega
    rw [e1]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) U
  rw [add_sub_cancel, one_pow] at h
  rw [h, mul_one]

/-- The probability that a fixed set of potential edges is entirely present. -/
lemma sum_wt_sub (p : ℝ) (F : Finset E) :
    ∑ S ∈ univ.filter (fun S : Finset E => F ⊆ S), wt p S = p ^ F.card := by
  have h := sum_wt_cond p F ∅ (Finset.disjoint_empty_right F)
  simpa using h

/-- The probability that a fixed set of potential edges is entirely absent. -/
lemma sum_wt_disjoint (p : ℝ) (D : Finset E) :
    ∑ S ∈ univ.filter (fun S : Finset E => Disjoint S D), wt p S = (1 - p) ^ D.card := by
  have h := sum_wt_cond p ∅ D (Finset.disjoint_empty_left D)
  simpa using h

/-- Markov's inequality for the weighted count. -/
lemma markov_wt {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset E → ℝ) (hX : ∀ S, 0 ≤ X S)
    {c : ℝ} (hc : 0 < c) :
    ∑ S ∈ univ.filter (fun S => c ≤ X S), wt p S ≤ (∑ S, wt p S * X S) / c := by
  rw [le_div_iff₀ hc, Finset.sum_mul]
  calc ∑ S ∈ univ.filter (fun S => c ≤ X S), wt p S * c
      ≤ ∑ S ∈ univ.filter (fun S => c ≤ X S), wt p S * X S := by
        refine Finset.sum_le_sum fun S hS => ?_
        exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hS).2 (wt_nonneg h0 h1 S)
    _ ≤ ∑ S, wt p S * X S :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ => mul_nonneg (wt_nonneg h0 h1 S) (hX S))

end Weights

/-! ### The random graph on `Fin n` -/

section Graphs

open Classical

variable {n : ℕ}

/-- The graph on `Fin n` whose edges are the (non-loop) elements of `S`. -/
def graphOf (S : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ s(a, b) ∈ S
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Injective closed tuples of length `m + 3` (cycles of that length, with a start and a
direction) in the graph given by `S`. -/
noncomputable def bad (m : ℕ) (S : Finset (Sym2 (Fin n))) : Finset (Fin (m + 3) → Fin n) :=
  univ.filter fun f => Function.Injective f ∧ ∀ i, (graphOf S).Adj (f i) (f (i + 1))

/-- The edges of the closed tuple `f`. -/
def tupleEdges (m : ℕ) (f : Fin (m + 3) → Fin n) : Finset (Sym2 (Fin n)) :=
  univ.image fun i => s(f i, f (i + 1))

lemma succ_ne (m : ℕ) (i : Fin (m + 3)) : i + 1 ≠ i := by
  intro h
  have := add_eq_left.mp h
  rw [Fin.ext_iff] at this
  simp at this

lemma succ_succ_ne (m : ℕ) (i : Fin (m + 3)) : i + 1 + 1 ≠ i := by
  intro h
  have h2 : (1 : Fin (m + 3)) + 1 = 0 := by
    rw [add_assoc] at h
    exact add_eq_left.mp h
  rw [Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero,
    Nat.mod_eq_of_lt (by omega : 1 + 1 < m + 3)] at h2
  omega

lemma card_tupleEdges {m : ℕ} {f : Fin (m + 3) → Fin n} (hf : Function.Injective f) :
    (tupleEdges m f).card = m + 3 := by
  unfold tupleEdges
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hf h1
  · have e1 := hf h1
    have e2 := hf h2
    apply absurd _ (succ_succ_ne m i)
    calc i + 1 + 1 = j + 1 := by rw [e2]
      _ = i := e1.symm

lemma mem_bad_iff {m : ℕ} {S : Finset (Sym2 (Fin n))} {f : Fin (m + 3) → Fin n} :
    f ∈ bad m S ↔ Function.Injective f ∧ tupleEdges m f ⊆ S := by
  unfold bad
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hf, hadj⟩
    refine ⟨hf, ?_⟩
    intro e he
    unfold tupleEdges at he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    exact (hadj i).2
  · rintro ⟨hf, hsub⟩
    refine ⟨hf, fun i => ⟨fun h => succ_ne m i (hf h).symm, hsub ?_⟩⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

lemma mem_bad_of_adj {m : ℕ} {S : Finset (Sym2 (Fin n))} {f : Fin (m + 3) → Fin n}
    (hf : Function.Injective f) (h : ∀ i, (graphOf S).Adj (f i) (f (i + 1))) : f ∈ bad m S := by
  unfold bad
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hf, h⟩

/-- The expected number of closed tuples of length `m + 3` is at most `(n p)^(m+3)`. -/
lemma expect_bad {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (m : ℕ) :
    ∑ S : Finset (Sym2 (Fin n)), wt p S * ((bad m S).card : ℝ) ≤ ((n : ℝ) * p) ^ (m + 3) := by
  have hcard : ∀ S : Finset (Sym2 (Fin n)),
      ((bad m S).card : ℝ) = ∑ f : Fin (m + 3) → Fin n, if f ∈ bad m S then (1 : ℝ) else 0 := by
    intro S
    rw [Finset.sum_boole]
    congr 2
    ext f; simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ f : Fin (m + 3) → Fin n,
      ∑ S : Finset (Sym2 (Fin n)), wt p S * (if f ∈ bad m S then (1 : ℝ) else 0) ≤ p ^ (m + 3) := by
    intro f
    by_cases hf : Function.Injective f
    · have : ∑ S : Finset (Sym2 (Fin n)), wt p S * (if f ∈ bad m S then (1 : ℝ) else 0) =
          ∑ S ∈ univ.filter (fun S : Finset (Sym2 (Fin n)) => tupleEdges m f ⊆ S), wt p S := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases hS : tupleEdges m f ⊆ S
        · have : f ∈ bad m S := mem_bad_iff.mpr ⟨hf, hS⟩
          simp [this, hS]
        · have : f ∉ bad m S := fun h => hS (mem_bad_iff.mp h).2
          simp [this, hS]
      rw [this, sum_wt_sub, card_tupleEdges hf]
    · have : ∀ S : Finset (Sym2 (Fin n)), f ∉ bad m S := fun S h => hf (mem_bad_iff.mp h).1
      simp only [this, if_false, mul_zero, Finset.sum_const_zero]
      exact pow_nonneg h0 _
  calc ∑ f : Fin (m + 3) → Fin n,
        ∑ S : Finset (Sym2 (Fin n)), wt p S * (if f ∈ bad m S then (1 : ℝ) else 0)
      ≤ ∑ _f : Fin (m + 3) → Fin n, p ^ (m + 3) := Finset.sum_le_sum fun f _ => hinner f
    _ = ((n : ℝ) * p) ^ (m + 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, mul_pow]
        push_cast
        ring

/-- The potential edges inside a vertex set `A`. -/
def DA (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) := A.offDiag.image Sym2.mk.uncurry

lemma card_DA (A : Finset (Fin n)) : (DA A).card = A.card.choose 2 :=
  Sym2.card_image_offDiag A

/-- Union bound: some set of size `a` is independent with probability at most
`C(n,a) (1-p)^C(a,2)`. -/
lemma prob_indep {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (a : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset (Sym2 (Fin n)) =>
        ∃ A : Finset (Fin n), A.card = a ∧ Disjoint S (DA A)), wt p S ≤
      (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) := by
  have hnn := wt_nonneg (E := Sym2 (Fin n)) h0 h1
  rw [Finset.sum_filter]
  calc ∑ S : Finset (Sym2 (Fin n)), (if ∃ A : Finset (Fin n), A.card = a ∧ Disjoint S (DA A)
          then wt p S else 0)
      ≤ ∑ S : Finset (Sym2 (Fin n)), ∑ A ∈ (univ : Finset (Fin n)).powersetCard a,
          (if Disjoint S (DA A) then wt p S else 0) := by
        refine Finset.sum_le_sum fun S _ => ?_
        split_ifs with hex
        · obtain ⟨A, hA, hd⟩ := hex
          have hAmem : A ∈ (univ : Finset (Fin n)).powersetCard a :=
            Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩
          have := Finset.single_le_sum (f := fun A => if Disjoint S (DA A) then wt p S else 0)
            (fun A _ => by split_ifs; exact hnn S; exact le_rfl) hAmem
          simpa [hd] using this
        · exact Finset.sum_nonneg fun A _ => by split_ifs; exact hnn S; exact le_rfl
    _ = ∑ A ∈ (univ : Finset (Fin n)).powersetCard a, (1 - p) ^ (a.choose 2) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [← Finset.sum_filter, sum_wt_disjoint, card_DA,
          (Finset.mem_powersetCard.mp hA).2]
    _ = (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

end Graphs

/-! ### The deletion step -/

section Deterministic

/-- A closed injective tuple read off from a cycle. -/
lemma cycle_tuple {V : Type*} {H : SimpleGraph V} {x : V} (c : H.Walk x x) (hc : c.IsCycle)
    {m : ℕ} (hm : c.length = m + 3) :
    ∃ f : Fin (m + 3) → V, Function.Injective f ∧ ∀ i, H.Adj (f i) (f (i + 1)) := by
  refine ⟨fun i => c.getVert i.val, ?_, ?_⟩
  · intro i j hij
    have := hc.getVert_injOn' (show (i : ℕ) ≤ c.length - 1 by omega)
      (show (j : ℕ) ≤ c.length - 1 by omega) hij
    exact Fin.ext this
  · intro i
    have hv : ((i + 1 : Fin (m + 3)) : ℕ) = (i.val + 1) % (m + 3) := by
      rw [Fin.val_add, Fin.val_one]
    show H.Adj (c.getVert i.val) (c.getVert ((i + 1 : Fin (m + 3)) : ℕ))
    rw [hv]
    have hadj := c.adj_getVert_succ (i := i.val) (by omega)
    by_cases h : i.val + 1 < m + 3
    · rw [Nat.mod_eq_of_lt h]
      exact hadj
    · have h' : i.val + 1 = m + 3 := by omega
      rw [h', Nat.mod_self, Walk.getVert_zero]
      have h2 : c.getVert (m + 3) = x := by rw [← hm]; exact c.getVert_length
      rw [h', h2] at hadj
      exact hadj

/-- Delete the vertices of `D` (they become isolated). -/
def deleteV {V : Type*} (G : SimpleGraph V) (D : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∉ D ∧ b ∉ D
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

variable {n : ℕ}

/-- One vertex (the first) from each short closed tuple. -/
noncomputable def Dset (g : ℕ) (S : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  (range g).biUnion fun m => (bad m S).image fun f => f 0

lemma card_Dset_le (g : ℕ) (S : Finset (Sym2 (Fin n))) :
    (Dset g S).card ≤ ∑ m ∈ range g, (bad m S).card :=
  (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)

/-- The girth of the pruned graph exceeds `g + 2`. -/
lemma egirth_deleteV (g : ℕ) (S : Finset (Sym2 (Fin n))) :
    ((g + 3 : ℕ) : ℕ∞) ≤ (deleteV (graphOf S) (Dset g S : Set (Fin n))).egirth := by
  rw [SimpleGraph.le_egirth]
  intro x w hw
  have h3 := hw.three_le_length
  by_contra hlt
  have hlt' : w.length < g + 3 := by exact_mod_cast not_le.mp hlt
  obtain ⟨m, hm⟩ : ∃ m, w.length = m + 3 := ⟨w.length - 3, by omega⟩
  obtain ⟨f, hf, hadj⟩ := cycle_tuple w hw hm
  have hmem : f ∈ bad m S := mem_bad_of_adj hf fun i => (hadj i).1
  have hD : f 0 ∈ Dset g S :=
    Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (by omega),
      Finset.mem_image.mpr ⟨f, hmem, rfl⟩⟩
  exact (hadj 0).2.1 (Finset.mem_coe.mpr hD)

/-- Deterministic core of the deletion method. -/
lemma core {g t a : ℕ} (S : Finset (Sym2 (Fin n)))
    (hX : 2 * ∑ m ∈ range g, (bad m S).card < n)
    (hA : ∀ A : Finset (Fin n), A.card = a → ¬ Disjoint S (DA A))
    (ht : 2 * (t * (a - 1)) ≤ n) :
    (t : ℕ∞) < (deleteV (graphOf S) (Dset g S : Set (Fin n))).chromaticNumber ∧
      ((g + 2 : ℕ) : ℕ∞) < (deleteV (graphOf S) (Dset g S : Set (Fin n))).egirth := by
  refine ⟨?_, lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (egirth_deleteV g S)⟩
  by_contra hle
  have hcol : (deleteV (graphOf S) (Dset g S : Set (Fin n))).Colorable t :=
    chromaticNumber_le_iff_colorable.mp (not_lt.mp hle)
  obtain ⟨c⟩ := hcol
  have hD := card_Dset_le g S
  have hcompl : n < 2 * (Dset g S)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ (Dset g S)
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (Dset g S)ᶜ) (t := (Finset.univ : Finset (Fin t))) (f := c)
    (n := a - 1) (fun _ _ => Finset.mem_univ _)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (show a ≤ _ by omega : a ≤
    ((Dset g S)ᶜ.filter (fun x => c x = y)).card)
  refine hA A hAcard ?_
  rw [Finset.disjoint_left]
  intro e heS heD
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp heD
  rw [Finset.mem_offDiag] at huv
  have hu := Finset.mem_filter.mp (hAsub huv.1)
  have hv := Finset.mem_filter.mp (hAsub huv.2.1)
  have hadj : (deleteV (graphOf S) (Dset g S : Set (Fin n))).Adj u v :=
    ⟨⟨huv.2.2, heS⟩, by simpa using hu.1, by simpa using hv.1⟩
  exact c.valid hadj (hu.2.trans hv.2.symm)

end Deterministic

/-! ### The probabilistic existence statement -/

section Existence

variable {n : ℕ}

/-- The independence bound: with `p (a - 1) ≥ 2 log (2n)` and `a ≥ 2` the probability is `≤ 1/4`. -/
lemma indep_bound {a : ℕ} {p L : ℝ} (hn : 0 < n) (h0 : 0 < p) (h1 : p ≤ 1)
    (hL : L = Real.log (2 * n)) (ha2 : 2 ≤ a) (hpa : 2 * L ≤ p * ((a : ℝ) - 1)) :
    (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) ≤ 1 / 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (1 - p) ^ (a.choose 2) ≤ Real.exp (-(p * (a.choose 2 : ℝ))) := by
    calc (1 - p) ^ (a.choose 2) ≤ (Real.exp (-p)) ^ (a.choose 2) :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
      _ = Real.exp (-(p * (a.choose 2 : ℝ))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : -(p * (a.choose 2 : ℝ)) ≤ (a : ℝ) * (-L) := by
    rw [Nat.cast_choose_two]
    have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have := mul_le_mul_of_nonneg_left hpa haR
    nlinarith
  have hcho : (n.choose a : ℝ) ≤ (n : ℝ) ^ a := by exact_mod_cast Nat.choose_le_pow n a
  have hexpL : Real.exp (-L) = (2 * (n : ℝ))⁻¹ := by
    rw [Real.exp_neg, hL, Real.exp_log (by positivity)]
  calc (n.choose a : ℝ) * (1 - p) ^ (a.choose 2)
      ≤ (n : ℝ) ^ a * Real.exp ((a : ℝ) * (-L)) := by
        refine mul_le_mul hcho (hk.trans (Real.exp_le_exp.mpr hexp)) (by positivity)
          (by positivity)
    _ = ((n : ℝ) * (2 * (n : ℝ))⁻¹) ^ a := by
        rw [Real.exp_nat_mul, hexpL, mul_pow]
    _ = (1 / 2) ^ a := by
        congr 1
        field_simp
    _ ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) ha2
    _ = 1 / 4 := by norm_num

/-- There is an edge set `S` with few short cycles and no independent set of size `a`. -/
lemma exists_good {g a : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n)
    (hX : 6 * ∑ m ∈ range g, ((n : ℝ) * p) ^ (m + 3) ≤ n)
    (hI : (n.choose a : ℝ) * (1 - p) ^ (a.choose 2) ≤ 1 / 4) :
    ∃ S : Finset (Sym2 (Fin n)), 2 * ∑ m ∈ range g, (bad m S).card < n ∧
      ∀ A : Finset (Fin n), A.card = a → ¬ Disjoint S (DA A) := by
  by_contra hcon
  push Not at hcon
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn := wt_nonneg (E := Sym2 (Fin n)) h0 h1
  set X : Finset (Sym2 (Fin n)) → ℝ := fun S => ∑ m ∈ range g, ((bad m S).card : ℝ) with hXdef
  have hXnn : ∀ S, 0 ≤ X S := fun S => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hEX : ∑ S, wt p S * X S ≤ ∑ m ∈ range g, ((n : ℝ) * p) ^ (m + 3) := by
    simp_rw [hXdef, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun m _ => expect_bad h0 h1 m
  have hmark := markov_wt h0 h1 X hXnn (c := (n : ℝ) / 2) (by positivity)
  have hP1 : ∑ S ∈ univ.filter (fun S => (n : ℝ) / 2 ≤ X S), wt p S ≤ 1 / 3 := by
    refine hmark.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have := hEX.trans (show ∑ m ∈ range g, ((n : ℝ) * p) ^ (m + 3) ≤ n / 6 by linarith)
    linarith
  have hP2 := prob_indep (n := n) h0 h1 a
  have hcover : ∀ S : Finset (Sym2 (Fin n)), wt p S ≤
      (if (n : ℝ) / 2 ≤ X S then wt p S else 0) +
      (if ∃ A : Finset (Fin n), A.card = a ∧ Disjoint S (DA A) then wt p S else 0) := by
    intro S
    have hnnS := hnn S
    by_cases h : 2 * ∑ m ∈ range g, (bad m S).card < n
    · rw [if_pos (hcon S h)]
      have : 0 ≤ (if (n : ℝ) / 2 ≤ X S then wt p S else 0) := by split_ifs <;> simp [hnnS]
      linarith
    · have h' : n ≤ 2 * ∑ m ∈ range g, (bad m S).card := not_lt.mp h
      have h'' : (n : ℝ) ≤ 2 * (∑ m ∈ range g, ((bad m S).card : ℝ)) := by exact_mod_cast h'
      have hle : (n : ℝ) / 2 ≤ X S := by simp only [hXdef]; linarith
      rw [if_pos hle]
      have : 0 ≤ (if ∃ A : Finset (Fin n), A.card = a ∧ Disjoint S (DA A) then wt p S else 0) := by
        split_ifs <;> simp [hnnS]
      linarith
  have htot : (1 : ℝ) ≤ ∑ S ∈ univ.filter (fun S => (n : ℝ) / 2 ≤ X S), wt p S +
      ∑ S ∈ univ.filter (fun S : Finset (Sym2 (Fin n)) =>
        ∃ A : Finset (Fin n), A.card = a ∧ Disjoint S (DA A)), wt p S := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← sum_wt p (E := Sym2 (Fin n))]
    exact Finset.sum_le_sum fun S _ => hcover S
  linarith

end Existence

/-! ### Choice of the parameters -/

section Parameters

/-- The main existence statement, with girth exceeding `g + 2`. -/
lemma exists_graph_aux (g t : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (t : ℕ∞) < G.chromaticNumber ∧ ((g + 2 : ℕ) : ℕ∞) < G.egirth := by
  obtain ⟨r, hr⟩ : ∃ r, r = g + 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 40 * (t + 1) * r := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = M ^ 2 := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = N ^ (2 * r - 1) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = N * q := ⟨_, rfl⟩
  have hr2 : 2 ≤ r := by omega
  have hMpos : 0 < M := by rw [hM]; positivity
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hnpos : 0 < n := by rw [hn]; positivity
  have hnq : n = N ^ (2 * r) := by
    rw [hn, hqdef, ← pow_succ']
    congr 1
    omega
  have hMN : M ≤ N := by rw [hNdef]; exact Nat.le_self_pow (by norm_num) M
  have hNr : N ≤ N ^ r := Nat.le_self_pow (by omega) N
  have h40 : 40 * r ≤ M := by rw [hM]; nlinarith [Nat.zero_le t, Nat.zero_le r]
  have h6g : 6 * g ≤ N ^ r := by omega
  have hpoly : 6 * t + 16 * t * r * M ≤ M ^ 2 := by
    have hM2 : 16 * t * r + 6 * t ≤ M := by rw [hM]; nlinarith [Nat.zero_le t, Nat.zero_le r]
    nlinarith [Nat.mul_le_mul_left M hM2]
  -- real parameters
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hqR0 : (0 : ℝ) < q := by linarith
  set p : ℝ := 1 / (q : ℝ) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hqR0]; exact hqR
  have hnp : (n : ℝ) * p = N := by
    rw [hp, hn]; push_cast; field_simp
  set L : ℝ := Real.log (2 * n) with hL
  have hL0 : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    linarith
  set x : ℝ := 2 * q * L with hx
  have hx0 : 0 < x := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = ⌈x⌉₊ + 1 := ⟨_, rfl⟩
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have ha2 : 2 ≤ a := by
    have : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
    omega
  have hpa : 2 * L ≤ p * ((a : ℝ) - 1) := by
    rw [ha]; push_cast
    rw [hp]
    rw [div_mul_eq_mul_div, le_div_iff₀ hqR0]
    simp only [add_sub_cancel_right]
    nlinarith
  have hI := indep_bound (a := a) (n := n) hnpos hp0 hp1 hL ha2 hpa
  have hX : 6 * ∑ m ∈ range g, ((n : ℝ) * p) ^ (m + 3) ≤ n := by
    rw [hnp]
    have h1 : ∑ m ∈ range g, (N : ℝ) ^ (m + 3) ≤ ∑ m ∈ range g, (N : ℝ) ^ r := by
      refine Finset.sum_le_sum fun m hm => ?_
      have := Finset.mem_range.mp hm
      exact pow_le_pow_right₀ (by exact_mod_cast hNpos) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have h2 : (6 * g : ℝ) ≤ (N : ℝ) ^ r := by exact_mod_cast h6g
    have h3 : (n : ℝ) = (N : ℝ) ^ r * (N : ℝ) ^ r := by
      rw [hnq, ← pow_add]; push_cast; congr 1; omega
    have hNrpos : (0 : ℝ) ≤ (N : ℝ) ^ r := by positivity
    rw [h3]
    nlinarith
  obtain ⟨S, hS1, hS2⟩ := exists_good (n := n) (g := g) (a := a) hp0.le hp1 hnpos hX hI
  have ht : 2 * (t * (a - 1)) ≤ n := by
    have haa : a - 1 = ⌈x⌉₊ := by omega
    rw [haa]
    have hlt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have hlogn : L ≤ 1 + 4 * r * M := by
      have e1 : L = Real.log 2 + Real.log n := by
        rw [hL]; exact Real.log_mul (by norm_num) hnR.ne'
      have e2 : Real.log n = (2 * r) * (2 * Real.log M) := by
        have : (n : ℝ) = ((M : ℝ) ^ 2) ^ (2 * r) := by
          rw [hnq, hNdef]; push_cast; rfl
        rw [this, Real.log_pow, Real.log_pow]; push_cast; ring
      have e3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have e4 : Real.log M ≤ M := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M by exact_mod_cast hMpos)
        linarith
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (2 * (r : ℝ)) * (2 * Real.log M) ≤ (2 * r) * (2 * M) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [e1, e2]
      nlinarith
    have hpolyR : (6 * t + 16 * t * r * M : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hpoly
    have hnN : (n : ℝ) = (M : ℝ) ^ 2 * q := by
      rw [hn, hNdef]; push_cast; ring
    have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have key : (2 * (t * (⌈x⌉₊ : ℝ))) ≤ n := by
      have h1 : (⌈x⌉₊ : ℝ) ≤ 2 * q * (1 + 4 * r * M) + 1 := by
        have : x ≤ 2 * q * (1 + 4 * r * M) := by
          rw [hx]; exact mul_le_mul_of_nonneg_left hlogn (by positivity)
        linarith
      have h2 : (⌈x⌉₊ : ℝ) ≤ q * (3 + 8 * r * M) := by nlinarith
      rw [hnN]
      calc 2 * ((t : ℝ) * (⌈x⌉₊ : ℝ)) ≤ 2 * (t * (q * (3 + 8 * r * M))) := by
            have := mul_le_mul_of_nonneg_left h2 htR
            linarith
        _ = (2 * t * (3 + 8 * r * M)) * q := by ring
        _ ≤ (M : ℝ) ^ 2 * q := by
            apply mul_le_mul_of_nonneg_right _ hqR0.le
            nlinarith
    exact_mod_cast key
  obtain ⟨hc, hg⟩ := core (g := g) (t := t) (a := a) S hS1 hS2 ht
  exact ⟨n, _, hc, hg⟩

end Parameters

end ErdosGirth

/-- CO-250. **Erdős' theorem** (probabilistic deletion method): for all `g` and `t` there is a
finite graph with chromatic number greater than `t` and girth greater than `g`
(`egirth` is the extended girth, `⊤` for forests). -/
@[kb "kellertrotter2017" "Theorem 11.7, p. 258"]
theorem exists_graph_large_girth_large_chromatic (g t : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (t : ℕ∞) < G.chromaticNumber ∧ (g : ℕ∞) < G.egirth := by
  obtain ⟨n, G, h1, h2⟩ := ErdosGirth.exists_graph_aux g t
  refine ⟨n, G, h1, lt_of_le_of_lt ?_ h2⟩
  exact_mod_cast Nat.le_add_right g 2

end UndergradKB.Combinatorics
