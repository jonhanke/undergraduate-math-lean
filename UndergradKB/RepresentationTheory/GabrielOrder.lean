import UndergradKB.RepresentationTheory.ReflectionFunctors
import UndergradKB.RepresentationTheory.DynkinForms
import UndergradKB.Common.Attr

/-! # Orderings of sinks for Gabriel's theorem (Etingof et al., §5.8)

The proof of Theorem 5.34 applies reflection functors at the vertices of a quiver one after the other, each
vertex being a sink at the moment it is used. Here we isolate the combinatorics, which only concerns which arrows
exist, so the orientation of a quiver on `Fin n` is recorded by the relation `R x y` ("there is an arrow `x → y`").

* `flipAt i R`: reversing the arrows at `i`; `flipAlong l R`: reversing at the vertices of `l` in turn.
* `SinkAdm R l`: each vertex of `l` is a sink at the moment it is reached.
* `exists_sinkAdm`: for an orientation without oriented cycles (in particular for any orientation of a positive
  definite graph, which contains no cycle), there is an ordering of all vertices that is admissible in this sense,
  and reversing at all vertices gives back the original orientation (`flipAlong_eq_self`).
* `exists_pow_prod_neg`: Lemma 5.33 for the Coxeter element of an arbitrary ordering of the vertices.
* `exists_sinkAdm_reflAlong_neg`: for a positive definite graph and a nonzero nonnegative vector `β`, there is a
  sink-admissible sequence of vertices along which the successive simple reflections make `β` acquire a negative
  coordinate. This is the combinatorial core of Theorem 5.34.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open Roots

variable {n : ℕ}

/-! ### Reversing arrows at vertices -/

/-- The orientation obtained by reversing every arrow at `i`. -/
def flipAt (i : Fin n) (R : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  fun x y => if x = i ∨ y = i then R y x else R x y

/-- Reversing the arrows at the vertices of a list, one after the other (head first). -/
def flipAlong : List (Fin n) → (Fin n → Fin n → Prop) → (Fin n → Fin n → Prop)
  | [], R => R
  | i :: l, R => flipAlong l (flipAt i R)

/-- A list of vertices is sink-admissible for an orientation if its head is a sink and its tail is
sink-admissible for the orientation reversed at the head. -/
def SinkAdm : (Fin n → Fin n → Prop) → List (Fin n) → Prop
  | _, [] => True
  | R, i :: l => (∀ j, ¬ R i j) ∧ SinkAdm (flipAt i R) l

theorem flipAt_self (i x : Fin n) (R : Fin n → Fin n → Prop) : flipAt i R x x = R x x := by
  unfold flipAt; split_ifs <;> rfl

theorem flipAlong_self (l : List (Fin n)) (R : Fin n → Fin n → Prop) (x : Fin n) :
    flipAlong l R x x = R x x := by
  induction l generalizing R with
  | nil => rfl
  | cons i l ih => exact (ih _).trans (flipAt_self i x R)

/-- For two distinct vertices, the arrow between them has been reversed by `flipAlong l` exactly when the
number of occurrences of the two vertices in `l` is odd. -/
theorem flipAlong_apply (l : List (Fin n)) (R : Fin n → Fin n → Prop) {x y : Fin n} (hxy : x ≠ y) :
    flipAlong l R x y = if (l.count x + l.count y) % 2 = 0 then R x y else R y x := by
  induction l generalizing R with
  | nil => simp [flipAlong]
  | cons i l ih =>
    show flipAlong l (flipAt i R) x y = _
    rw [ih]
    simp only [List.count_cons, beq_iff_eq, flipAt]
    by_cases hx : i = x
    · subst hx
      have hy : y ≠ i := fun h => hxy h.symm
      have hy' : ¬ i = y := fun h => hy h.symm
      simp only [hy', ite_false, true_or, or_true, ite_true, add_zero]
      split_ifs <;> first | rfl | omega
    · by_cases hy : i = y
      · subst hy
        have hx' : x ≠ i := fun h => hx h.symm
        simp only [hx', ite_false, true_or, or_true, ite_true, add_zero]
        split_ifs <;> first | rfl | omega
      · have hx' : x ≠ i := fun h => hx h.symm
        have hy' : y ≠ i := fun h => hy h.symm
        simp only [hx, hy, hx', hy', ite_false, or_self, add_zero]

/-- Reversing at every vertex exactly once gives back the original orientation. -/
theorem flipAlong_eq_self {t : List (Fin n)} (ht : t.Nodup) (hall : ∀ x, x ∈ t) (R : Fin n → Fin n → Prop) :
    flipAlong t R = R := by
  funext x y
  by_cases hxy : x = y
  · subst hxy; exact flipAlong_self t R x
  · rw [flipAlong_apply t R hxy, List.count_eq_one_of_mem ht (hall x), List.count_eq_one_of_mem ht (hall y)]
    simp

theorem flipAlong_append (l₁ l₂ : List (Fin n)) (R : Fin n → Fin n → Prop) :
    flipAlong (l₁ ++ l₂) R = flipAlong l₂ (flipAlong l₁ R) := by
  induction l₁ generalizing R with
  | nil => rfl
  | cons i l ih => exact ih _

theorem sinkAdm_append (l₁ l₂ : List (Fin n)) (R : Fin n → Fin n → Prop) :
    SinkAdm R (l₁ ++ l₂) ↔ SinkAdm R l₁ ∧ SinkAdm (flipAlong l₁ R) l₂ := by
  induction l₁ generalizing R with
  | nil => simp [SinkAdm, flipAlong]
  | cons i l ih =>
    show ((∀ j, ¬ R i j) ∧ SinkAdm (flipAt i R) (l ++ l₂)) ↔ ((∀ j, ¬ R i j) ∧ SinkAdm (flipAt i R) l) ∧ _
    rw [ih]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- The list `t` repeated `N` times. -/
def rep (t : List (Fin n)) (N : ℕ) : List (Fin n) := (List.replicate N t).flatten

theorem rep_succ (t : List (Fin n)) (N : ℕ) : rep t (N + 1) = t ++ rep t N := by
  simp [rep, List.replicate_succ]

theorem sinkAdm_rep {t : List (Fin n)} {R : Fin n → Fin n → Prop} (hR : flipAlong t R = R) (ht : SinkAdm R t)
    (N : ℕ) : SinkAdm R (rep t N) := by
  induction N with
  | zero => simp [rep, SinkAdm]
  | succ N ih =>
    rw [rep_succ, sinkAdm_append, hR]
    exact ⟨ht, ih⟩

/-! ### A sink exists in every set of vertices of an orientation without oriented cycles -/

/-- An orientation has no oriented cycles of length at least three through distinct vertices. -/
def NoCycles (R : Fin n → Fin n → Prop) : Prop :=
  ∀ (k : ℕ) (g : Fin (k + 3) → Fin n), Function.Injective g → (∀ t, R (g t) (g (finRotate _ t))) → False

theorem val_finRotate_add_three {k : ℕ} (x : Fin (k + 3)) :
    ((finRotate (k + 3) x : Fin (k + 3)) : ℕ) = if x.val = k + 2 then 0 else x.val + 1 := by
  have h := coe_finRotate (n := k + 2) x
  rw [h]
  by_cases hx : x = Fin.last (k + 2)
  · subst hx; simp
  · have : x.val ≠ k + 2 := fun e => hx (Fin.ext e)
    simp [hx, this]

theorem exists_sink_in {R : Fin n → Fin n → Prop} (hasym : ∀ x y, R x y → ¬ R y x) (hcyc : NoCycles R)
    (S : Finset (Fin n)) (hS : S.Nonempty) : ∃ y ∈ S, ∀ z ∈ S, ¬ R y z := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀⟩ := hS
  let nx : S → S := fun y => ⟨(hcon y.1 y.2).choose, (hcon y.1 y.2).choose_spec.1⟩
  have hnx : ∀ y : S, R y.1 (nx y).1 := fun y => (hcon y.1 y.2).choose_spec.2
  let f : ℕ → Fin n := fun m => (nx^[m] ⟨y₀, hy₀⟩).1
  have hf : ∀ m, R (f m) (f (m + 1)) := by
    intro m
    simp only [f, Function.iterate_succ_apply']
    exact hnx _
  -- a repetition
  have hrep : ∃ d a, f a = f (a + d + 1) := by
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => f m)
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b - a - 1, a, by rw [he]; congr 1; omega⟩
    · exact ⟨a - b - 1, b, by rw [← he]; congr 1; omega⟩
  let d := Nat.find hrep
  obtain ⟨a, ha⟩ : ∃ a, f a = f (a + d + 1) := Nat.find_spec hrep
  have hmin : ∀ d' < d, ∀ a', f a' ≠ f (a' + d' + 1) := fun d' hd' a' h =>
    Nat.find_min hrep hd' ⟨a', h⟩
  have hinj : ∀ s t, s ≤ d → t ≤ d → f (a + s) = f (a + t) → s = t := by
    intro s t hs ht hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hmin (t - s - 1) (by omega) (a + s) (by rw [hst]; congr 1; omega)
    · exact hmin (s - t - 1) (by omega) (a + t) (by rw [← hst]; congr 1; omega)
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases hd2 : d
    · have h1 := hf a
      rw [← (show a + 0 + 1 = a + 1 by omega), ← ha] at h1
      exact hasym _ _ h1 h1
    · have h1 := hf a
      have h2 := hf (a + 1)
      rw [show a + 1 + 1 = a + 1 + 1 from rfl, ← (show a + 1 + 1 = a + 1 + 1 from rfl), ← ha] at h2
      exact hasym _ _ h1 h2
  · obtain ⟨k, hk⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    let g : Fin (k + 3) → Fin n := fun t => f (a + t.val)
    refine hcyc k g ?_ ?_
    · intro s t hst
      exact Fin.ext (hinj s t (by omega) (by omega) hst)
    · intro t
      simp only [g]
      rw [val_finRotate_add_three]
      by_cases ht : t.val = k + 2
      · rw [if_pos ht, ht]
        have h1 := hf (a + (k + 2))
        rw [show a + (k + 2) + 1 = a + d + 1 by omega, ← ha] at h1
        simpa using h1
      · rw [if_neg ht]
        exact hf (a + t.val)

/-- **An admissible ordering.** For an orientation that is asymmetric and has no oriented cycles, there is an
ordering of all the vertices, each used once, in which each vertex is a sink at the moment it is reached. -/
theorem exists_sinkAdm {R : Fin n → Fin n → Prop} (hasym : ∀ x y, R x y → ¬ R y x) (hcyc : NoCycles R) :
    ∃ t : List (Fin n), t.Nodup ∧ (∀ x, x ∈ t) ∧ SinkAdm R t := by
  classical
  suffices h : ∀ (m : ℕ) (S : Finset (Fin n)), S.card = m → ∀ R' : Fin n → Fin n → Prop,
      (∀ x ∈ S, ∀ y ∈ S, R' x y = R x y) → (∀ x ∉ S, ∀ y ∈ S, ¬ R' y x) →
      ∃ t : List (Fin n), t.Nodup ∧ (∀ x, x ∈ t ↔ x ∈ S) ∧ SinkAdm R' t by
    obtain ⟨t, h1, h2, h3⟩ := h _ Finset.univ rfl R (fun _ _ _ _ => rfl) (fun x hx => absurd (Finset.mem_univ x) hx)
    exact ⟨t, h1, fun x => (h2 x).2 (Finset.mem_univ x), h3⟩
  intro m
  induction m with
  | zero =>
    intro S hS R' _ _
    rw [Finset.card_eq_zero] at hS
    subst hS
    exact ⟨[], List.nodup_nil, by simp, trivial⟩
  | succ m ih =>
    intro S hS R' hR' hout
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨y, hyS, hy⟩ := exists_sink_in hasym hcyc S hne
    have hsink : ∀ j, ¬ R' y j := by
      intro j hj
      by_cases hjS : j ∈ S
      · exact hy j hjS ((hR' y hyS j hjS) ▸ hj)
      · exact hout j hjS y hyS hj
    obtain ⟨t, ht1, ht2, ht3⟩ := ih (S.erase y) (by rw [Finset.card_erase_of_mem hyS]; omega) (flipAt y R')
      (by
        intro x hx z hz
        have hxy : x ≠ y := Finset.ne_of_mem_erase hx
        have hzy : z ≠ y := Finset.ne_of_mem_erase hz
        simp only [flipAt, hxy, hzy, or_self, ite_false]
        exact hR' x (Finset.mem_of_mem_erase hx) z (Finset.mem_of_mem_erase hz))
      (by
        intro x hx z hz
        have hzy : z ≠ y := Finset.ne_of_mem_erase hz
        have hzS := Finset.mem_of_mem_erase hz
        by_cases hxy : x = y
        · subst hxy
          simp only [flipAt, or_true, ite_true]
          intro h
          exact hy z hzS ((hR' x hyS z hzS) ▸ h)
        · have hxS : x ∉ S := fun h => hx (Finset.mem_erase.2 ⟨hxy, h⟩)
          simp only [flipAt, hxy, hzy, or_self, ite_false]
          exact hout x hxS z hzS)
    refine ⟨y :: t, List.nodup_cons.2 ⟨fun h => ?_, ht1⟩, fun x => ?_, hsink, ht3⟩
    · exact Finset.notMem_erase y S ((ht2 y).1 h)
    · rw [List.mem_cons, ht2 x, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, h⟩)
        · exact hyS
        · exact h
      · intro h
        by_cases hxy : x = y
        · exact Or.inl hxy
        · exact Or.inr ⟨hxy, h⟩

/-! ### Orientations of a positive definite graph have no oriented cycles -/

theorem affineCycle_adj {k : ℕ} {i j : Fin (k + 3)} (h : (affineCycle k).Adj i j) :
    j = finRotate _ i ∨ i = finRotate _ j := by
  obtain ⟨hij, h1, -⟩ := h
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  simp only [cycMat, Matrix.of_apply, cycN, hv, ite_false] at h1
  have hfr := @val_finRotate_add_three k
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at h1 with hc
  · rcases hc with hc | hc | hc | hc
    · left; apply Fin.ext; rw [hfr]; split_ifs <;> omega
    · right; apply Fin.ext; rw [hfr]; split_ifs <;> omega
    · right; apply Fin.ext; rw [hfr]; split_ifs <;> omega
    · left; apply Fin.ext; rw [hfr]; split_ifs <;> omega

/-- An orientation `R` of a positive definite graph `G` (every arrow joins adjacent vertices) has no oriented
cycles. -/
theorem noCycles_of_posDefinite {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hG : PosDefinite G)
    {R : Fin n → Fin n → Prop} (hR : ∀ x y, R x y → G.Adj x y) : NoCycles R := by
  intro k g hg hc
  refine hG.not_embed_cycle k g hg fun i j hij => ?_
  rcases affineCycle_adj hij with rfl | rfl
  · exact hR _ _ (hc i)
  · exact (hR _ _ (hc j)).symm

/-! ### Lemma 5.33 for an arbitrary ordering of the vertices -/

section Coxeter

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem list_prod_mem_weylGroup (l : List (Fin n)) : (l.map (simpleReflection G)).prod ∈ weylGroup G := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, rfl⟩

/-- **Lemma 5.33 (any ordering).** For a positive definite graph and the Coxeter element `c` of an ordering
`l` of the vertices (each vertex once), every nonzero vector `β` with nonnegative coordinates has a power
`c^N β` with a strictly negative coordinate. -/
@[kb "etingof2011" "Lemma 5.33, p. 93"]
theorem exists_pow_prod_neg (hP : PosDefinite G) {l : List (Fin n)} (hl : l.Nodup) (hall : ∀ x, x ∈ l)
    {β : Fin n → ℤ} (hβ0 : β ≠ 0) (hβ : ∀ i, 0 ≤ β i) :
    ∃ N : ℕ, ∃ i, ((l.map (simpleReflection G)).prod ^ N) β i < 0 := by
  by_contra hcon
  push Not at hcon
  haveI := weylGroup_finite G hP
  set c := (l.map (simpleReflection G)).prod with hc
  let c' : weylGroup G := ⟨c, list_prod_mem_weylGroup G l⟩
  have hm : 0 < orderOf c' := orderOf_pos c'
  set m := orderOf c' with hmdef
  have hcm : c ^ m = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one c')
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  set γ : Fin n → ℤ := ∑ N ∈ Finset.range m, (c ^ N) β with hγ
  have hfix : c γ = γ := by
    rw [hγ, map_sum]
    have h1 : ∑ N ∈ Finset.range m, c ((c ^ N) β) = ∑ N ∈ Finset.range m, (c ^ (N + 1)) β := by
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [pow_succ', mul_apply_eq_comp]
    rw [h1]
    have h2 := Finset.sum_range_succ (fun N => (c ^ N) β) m
    have h3 := Finset.sum_range_succ' (fun N => (c ^ N) β) m
    beta_reduce at h2 h3
    have h0 : (c ^ 0) β = β := by rw [pow_zero]; rfl
    have h1' : (c ^ m) β = β := by rw [hcm]; rfl
    rw [h1'] at h2
    rw [h0] at h3
    exact add_right_cancel (h3.symm.trans h2)
  have hγ0 : γ = 0 := by
    have hl0 := form_eq_zero_of_prod_fixed G l hl γ hfix
    by_contra hne
    have hpos := hP.form_pos hne
    have hsum : form G γ γ = ∑ j, γ j * form G γ (simpleRoot j) := by
      simp only [simpleRoot, form_single_right]
      rw [form_eq_sum]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, Finset.sum_eq_zero] at hpos
    · exact lt_irrefl _ hpos
    · intro j _
      rw [hl0 j (hall j), mul_zero]
  obtain ⟨i, hi⟩ : ∃ i, 0 < β i := by
    by_contra h
    push Not at h
    exact hβ0 (funext fun i => le_antisymm (h i) (hβ i))
  have hle : β i ≤ γ i := by
    have : (c ^ 0) β i ≤ γ i := by
      rw [hγ, Finset.sum_apply]
      exact Finset.single_le_sum (f := fun N => (c ^ N) β i) (fun N _ => hcon N i) (Finset.mem_range.2 hm)
    simpa using this
  rw [hγ0] at hle
  simp at hle
  omega

/-- Applying the simple reflections at the vertices of a list in turn (head first). -/
def reflAlong : List (Fin n) → (Fin n → ℤ) → (Fin n → ℤ)
  | [], d => d
  | i :: l, d => reflAlong l (simpleReflection G i d)

theorem reflAlong_append (l₁ l₂ : List (Fin n)) (d : Fin n → ℤ) :
    reflAlong G (l₁ ++ l₂) d = reflAlong G l₂ (reflAlong G l₁ d) := by
  induction l₁ generalizing d with
  | nil => rfl
  | cons i l ih => exact ih _

theorem reflAlong_eq_prod (l : List (Fin n)) (d : Fin n → ℤ) :
    reflAlong G l d = (l.reverse.map (simpleReflection G)).prod d := by
  induction l generalizing d with
  | nil => rfl
  | cons i l ih =>
    show reflAlong G l _ = _
    rw [ih, List.reverse_cons, List.map_append, List.prod_append]
    simp [mul_apply_eq_comp]

theorem reflAlong_rep (t : List (Fin n)) (N : ℕ) (d : Fin n → ℤ) :
    reflAlong G (rep t N) d = ((t.reverse.map (simpleReflection G)).prod ^ N) d := by
  induction N generalizing d with
  | zero => simp [rep, reflAlong]
  | succ N ih =>
    rw [rep_succ, reflAlong_append, ih, reflAlong_eq_prod, pow_succ, mul_apply_eq_comp]

/-- Reflections along a list preserve the property of being a root, in both directions. -/
theorem isRoot_reflAlong_iff (l : List (Fin n)) (d : Fin n → ℤ) : IsRoot G (reflAlong G l d) ↔ IsRoot G d := by
  induction l generalizing d with
  | nil => rfl
  | cons i l ih =>
    show IsRoot G (reflAlong G l _) ↔ _
    rw [ih]
    constructor
    · intro h
      have := isRoot_reflect G (isRoot_simpleRoot G i) h
      rwa [show reflect G (simpleRoot i) (isRoot_simpleRoot G i) (simpleReflection G i d) = d from
        reflect_involutive G _ _ d] at this
    · exact isRoot_reflect G (isRoot_simpleRoot G i)

/-- **Combinatorial core of Theorem 5.34.** For an asymmetric orientation `R` of a positive definite graph `G`
and a nonzero vector `β` with nonnegative coordinates, there is a sink-admissible sequence of vertices along which
the successive simple reflections send `β` to a vector with a negative coordinate. -/
theorem exists_sinkAdm_reflAlong_neg (hP : PosDefinite G) {R : Fin n → Fin n → Prop}
    (hasym : ∀ x y, R x y → ¬ R y x) (hR : ∀ x y, R x y → G.Adj x y) {β : Fin n → ℤ} (hβ0 : β ≠ 0)
    (hβ : ∀ i, 0 ≤ β i) : ∃ L : List (Fin n), SinkAdm R L ∧ ∃ i, reflAlong G L β i < 0 := by
  obtain ⟨t, ht, hall, hadm⟩ := exists_sinkAdm hasym (noCycles_of_posDefinite hP hR)
  obtain ⟨N, i, hi⟩ := exists_pow_prod_neg G hP (List.nodup_reverse.2 ht) (fun x => List.mem_reverse.2 (hall x))
    hβ0 hβ
  exact ⟨rep t N, sinkAdm_rep (flipAlong_eq_self ht hall R) hadm N, i, by rwa [reflAlong_rep]⟩

end Coxeter

end UndergradKB.RepresentationTheory.Gabriel
