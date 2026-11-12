import Mathlib.Data.List.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Logic.Relation
import Mathlib.Algebra.Group.Nat.Even
import UndergradKB.Common.Attr

/-!
# The splicing procedure for Euler circuits (Keller–Trotter, proof of Theorem 5.13)

A multigraph is given as a list of edges `List (ℕ × ℕ)` on natural-number vertices (loops allowed,
a loop counting twice in the degree).  Edges are normalised to `(min, max)`, sorted, and the
procedure of the book is run: start at the least vertex, walk along the least available edge until
stuck, and then repeatedly splice in a closed sub-circuit starting at the least vertex of the
current circuit that still has an unused edge.  Odd degrees are detected first, and failure of the
loop to use all edges means the graph is disconnected.
-/

namespace UndergradKB.Combinatorics.Euler

/-- Normal form of an undirected edge. -/
def normE (e : ℕ × ℕ) : ℕ × ℕ := (min e.1 e.2, max e.1 e.2)

/-- Edge `e` is incident with `v`. -/
def incE (v : ℕ) (e : ℕ × ℕ) : Bool := decide (e.1 = v ∨ e.2 = v)

/-- The other endpoint of an edge at `v`. -/
def otherE (v : ℕ) (e : ℕ × ℕ) : ℕ := if e.1 = v then e.2 else e.1

/-- The list of all endpoints (with multiplicity). -/
def vertsOf (es : List (ℕ × ℕ)) : List ℕ := es.flatMap fun e => [e.1, e.2]

/-- Degree of `x` in the multigraph given by an edge list (loops count twice). -/
def deg (es : List (ℕ × ℕ)) (x : ℕ) : ℕ := (vertsOf es).count x

/-- The (normalised) edges used by consecutive vertices of a walk. -/
def steps : List ℕ → List (ℕ × ℕ)
  | a :: b :: t => normE (a, b) :: steps (b :: t)
  | _ => []

/-- Lexicographic order on edges, used to pick the least available edge. -/
def leE (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel leE := fun a b => inferInstanceAs (Decidable (_ ∨ _))

/-- Walk from `cur` along the first available edge until stuck; returns the vertices visited after
`cur` and the unused edges. -/
def trailFrom : ℕ → ℕ → List (ℕ × ℕ) → List ℕ × List (ℕ × ℕ)
  | 0, _, r => ([], r)
  | n + 1, cur, r =>
    match r.find? (incE cur) with
    | none => ([], r)
    | some e =>
      let res := trailFrom n (otherE cur e) (r.erase e)
      (otherE cur e :: res.1, res.2)

/-- Splice the closed walk `v :: p` into a circuit at the first occurrence of `v`. -/
def spliceAt (v : ℕ) (p : List ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: t => if x = v then x :: (p ++ t) else x :: spliceAt v p t

/-- The least vertex of the circuit that still has an unused edge. -/
def nextStart (c : List ℕ) (r : List (ℕ × ℕ)) : Option ℕ :=
  (c.filter fun x => r.any (incE x)).min?

/-- The splicing loop. -/
def circuitLoop : ℕ → List ℕ → List (ℕ × ℕ) → Option (List ℕ)
  | 0, c, r => if r.isEmpty then some c else none
  | n + 1, c, r =>
    match nextStart c r with
    | none => if r.isEmpty then some c else none
    | some v =>
      let res := trailFrom r.length v r
      circuitLoop n (spliceAt v res.1 c) res.2

/-- CO-267. The executable procedure of the proof of Theorem 5.13: odd degree gives `none`;
otherwise start at the least vertex and splice closed sub-circuits at the least vertex with an
unused edge; `none` also if some edge is never reached (disconnected). -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
def eulerCircuit (es : List (ℕ × ℕ)) : Option (List ℕ) :=
  if (vertsOf es).all (fun x => deg es x % 2 == 0) then
    match (vertsOf ((es.map normE).insertionSort leE)).min? with
    | none => some []
    | some v0 => circuitLoop es.length [v0] ((es.map normE).insertionSort leE)
  else none

/-- Meaning of the checker: the vertex list is a closed walk whose consecutive pairs are exactly
the edges, each used once (multiset equality). -/
def IsEulerCircuit (es : List (ℕ × ℕ)) (w : List ℕ) : Prop :=
  w.head? = w.getLast? ∧ (steps w).Perm (es.map normE)

instance (es w) : Decidable (IsEulerCircuit es w) := by unfold IsEulerCircuit; infer_instance

/-- CO-267. Computable checker for Euler circuits. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
def isEulerCircuit (es : List (ℕ × ℕ)) (w : List ℕ) : Bool := decide (IsEulerCircuit es w)

/-- CO-267. The checker means what it should. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
theorem isEulerCircuit_sound {es w} (h : isEulerCircuit es w = true) : IsEulerCircuit es w :=
  of_decide_eq_true h

/-! ### Basic lemmas -/

lemma normE_eq_iff {a b x y : ℕ} :
    normE (a, b) = normE (x, y) ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  simp only [normE, Prod.mk.injEq]
  omega

lemma deg_eq_count (es x) : deg es x = (vertsOf es).count x := rfl

lemma vertsOf_perm {l₁ l₂ : List (ℕ × ℕ)} (h : l₁.Perm l₂) : (vertsOf l₁).Perm (vertsOf l₂) :=
  List.Perm.flatMap_right _ h

lemma deg_perm {l₁ l₂ : List (ℕ × ℕ)} (h : l₁.Perm l₂) (x : ℕ) : deg l₁ x = deg l₂ x :=
  (vertsOf_perm h).count_eq x

lemma deg_map_normE (es : List (ℕ × ℕ)) (x : ℕ) : deg (es.map normE) x = deg es x := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    simp only [deg, vertsOf, List.map_cons, List.flatMap_cons, List.count_append] at ih ⊢
    rw [ih]
    simp only [normE, List.count_cons, List.count_nil]
    split_ifs <;> simp_all <;> omega

lemma deg_cons (e : ℕ × ℕ) (r : List (ℕ × ℕ)) (x : ℕ) :
    deg (e :: r) x = deg r x + ((if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0)) := by
  simp only [deg, vertsOf, List.flatMap_cons, List.count_append, List.count_cons, List.count_nil]
  simp only [beq_iff_eq]
  split_ifs <;> omega

lemma deg_erase {r : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ r) (x : ℕ) :
    deg r x = deg (r.erase e) x + ((if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0)) := by
  rw [deg_perm (List.perm_cons_erase he) x, deg_cons]

lemma deg_eq_zero_of_no_inc {r : List (ℕ × ℕ)} {u : ℕ} (h : ∀ e ∈ r, incE u e = false) :
    deg r u = 0 := by
  simp only [deg, vertsOf, List.count_eq_zero, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, not_exists, not_and]
  intro e he hu
  have := h e he
  simp only [incE, decide_eq_false_iff_not] at this
  rcases hu with hu | hu
  · exact this (Or.inl hu.symm)
  · exact this (Or.inr hu.symm)

lemma cnt_inc {e : ℕ × ℕ} {cur : ℕ} (h : incE cur e = true) (x : ℕ) :
    ((if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0))
      = (if x = cur then 1 else 0) + (if x = otherE cur e then 1 else 0) := by
  obtain ⟨a, b⟩ := e
  simp only [incE, otherE, decide_eq_true_eq] at h ⊢
  by_cases h1 : a = cur
  · subst h1; simp only [ite_true]; split_ifs <;> omega
  · have h2 : b = cur := by tauto
    subst h2; simp only [h1, ite_false]; split_ifs <;> omega

lemma normE_cur {e : ℕ × ℕ} {cur : ℕ} (hn : normE e = e) (h : incE cur e = true) :
    normE (cur, otherE cur e) = e := by
  obtain ⟨a, b⟩ := e
  simp only [incE, otherE, decide_eq_true_eq] at h ⊢
  simp only [normE, Prod.mk.injEq] at hn ⊢
  by_cases h1 : a = cur
  · subst h1; simp only [ite_true]; omega
  · have h2 : b = cur := by tauto
    subst h2; simp only [h1, ite_false]; omega

lemma incE_normE (b d : ℕ) : incE b (normE (b, d)) = true := by
  simp [incE, normE]; omega

lemma steps_cons_cons (a b : ℕ) (t : List ℕ) : steps (a :: b :: t) = normE (a, b) :: steps (b :: t) :=
  rfl

lemma steps_single (a : ℕ) : steps [a] = [] := rfl

lemma steps_mem : ∀ (l : List ℕ) (g : ℕ × ℕ), g ∈ steps l → ∃ a ∈ l, ∃ b ∈ l, g = normE (a, b)
  | [], g, h => by simp [steps] at h
  | [x], g, h => by simp [steps] at h
  | x :: y :: t, g, h => by
    rw [steps_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨x, by simp, y, by simp, rfl⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := steps_mem (y :: t) g h
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, rfl⟩

/-- `steps` is the list of normalised consecutive pairs. -/
lemma steps_eq_zip : ∀ l : List ℕ, steps l = (l.zip l.tail).map normE
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
    rw [steps_cons_cons, steps_eq_zip (y :: t)]
    rfl

/-! ### Splicing -/

lemma steps_splice_aux {u : ℕ} :
    ∀ (p : List ℕ) (a : ℕ) (t : List ℕ), (a :: p).getLast? = some u →
      steps (a :: (p ++ t)) = steps (a :: p) ++ steps (u :: t)
  | [], a, t, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; simp [steps_single]
  | b :: p, a, t, h => by
    have h' : (b :: p).getLast? = some u := by simpa using h
    simp only [List.cons_append, steps_cons_cons, List.cons_append]
    rw [steps_splice_aux p b t h']

lemma spliceAt_head? (v : ℕ) (p c : List ℕ) : (spliceAt v p c).head? = c.head? := by
  cases c with
  | nil => rfl
  | cons x t => unfold spliceAt; split_ifs <;> rfl

lemma spliceAt_getLast? {v : ℕ} {p : List ℕ} (hp : (v :: p).getLast? = some v) :
    ∀ c : List ℕ, v ∈ c → (spliceAt v p c).getLast? = c.getLast?
  | [], h => by simp at h
  | x :: t, h => by
    by_cases hx : x = v
    · subst hx
      simp only [spliceAt, ite_true]
      rw [List.getLast?_cons, List.getLast?_cons, List.getLast?_append]
      simp only [List.getLast?_cons, Option.some.injEq] at hp
      rcases ht : t.getLast? with _ | y <;> rcases hq : p.getLast? with _ | z <;>
        simp_all
    · have hvt : v ∈ t := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [spliceAt, hx, ite_false]
      rw [List.getLast?_cons, List.getLast?_cons, spliceAt_getLast? hp t hvt]

lemma spliceAt_steps {v : ℕ} {p : List ℕ} (hp : (v :: p).getLast? = some v) :
    ∀ c : List ℕ, v ∈ c → (steps (spliceAt v p c)).Perm (steps c ++ steps (v :: p))
  | [], h => by simp at h
  | x :: t, h => by
    by_cases hx : x = v
    · subst hx
      simp only [spliceAt, ite_true]
      rw [steps_splice_aux p x t hp]
      exact List.perm_append_comm
    · have hvt : v ∈ t := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [spliceAt, hx, ite_false]
      have ih := spliceAt_steps hp t hvt
      cases t with
      | nil => simp at hvt
      | cons y t' =>
        have hh := spliceAt_head? v p (y :: t')
        cases hs : spliceAt v p (y :: t') with
        | nil => rw [hs] at hh; simp at hh
        | cons z s' =>
          rw [hs] at hh ih
          have hz : z = y := by simpa using hh
          subst hz
          rw [steps_cons_cons, steps_cons_cons, List.cons_append]
          exact ih.cons _

/-! ### The greedy trail -/

theorem trailFrom_spec : ∀ (n cur : ℕ) (r : List (ℕ × ℕ)) (w : ℕ), r.length ≤ n →
    (∀ e ∈ r, normE e = e) →
    (∀ x, deg r x % 2 = ((if x = cur then 1 else 0) + (if x = w then 1 else 0)) % 2) →
    ∀ p r', trailFrom n cur r = (p, r') →
    ∃ u, (cur :: p).getLast? = some u ∧ (steps (cur :: p) ++ r').Perm r ∧
      (∀ e ∈ r', incE u e = false) ∧
      (∀ x, deg r' x % 2 = ((if x = u then 1 else 0) + (if x = w then 1 else 0)) % 2) ∧
      (r.any (incE cur) = true → p ≠ [])
  | 0, cur, r, w, hlen, _, hpar, p, r', h => by
    have hr : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst hr
    simp only [trailFrom, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cur, by simp, by simp [steps_single], by simp, hpar, by simp⟩
  | n + 1, cur, r, w, hlen, hnorm, hpar, p, r', h => by
    cases hf : r.find? (incE cur) with
    | none =>
      simp only [trailFrom, hf, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hno : ∀ e ∈ r, incE cur e = false := by
        intro e he
        have := List.find?_eq_none.mp hf e he
        simpa using this
      refine ⟨cur, by simp, by simp [steps_single], hno, hpar, ?_⟩
      intro hany
      obtain ⟨e, he, hi⟩ := List.any_eq_true.mp hany
      have := hno e he
      rw [hi] at this; exact absurd this (by simp)
    | some e =>
      have he : e ∈ r := List.mem_of_find?_eq_some hf
      have hi : incE cur e = true := List.find?_some hf
      rcases hT : trailFrom n (otherE cur e) (r.erase e) with ⟨p', r2⟩
      simp only [trailFrom, hf, hT, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlen2 : (r.erase e).length ≤ n := by
        rw [List.length_erase_of_mem he]
        have : 0 < r.length := List.length_pos_of_mem he
        omega
      have hnorm2 : ∀ e' ∈ r.erase e, normE e' = e' := fun e' h' =>
        hnorm e' (List.mem_of_mem_erase h')
      have hpar2 : ∀ x, deg (r.erase e) x % 2 =
          ((if x = otherE cur e then 1 else 0) + (if x = w then 1 else 0)) % 2 := by
        intro x
        have h1 := hpar x
        rw [deg_erase he x, cnt_inc hi x] at h1
        split_ifs at h1 ⊢ <;> omega
      obtain ⟨u, hu, hperm, hst, hpar', -⟩ :=
        trailFrom_spec n (otherE cur e) (r.erase e) w hlen2 hnorm2 hpar2 p' r2 hT
      refine ⟨u, by simpa using hu, ?_, hst, hpar', fun _ => by simp⟩
      rw [steps_cons_cons, normE_cur (hnorm e he) hi, List.cons_append]
      exact (hperm.cons e).trans (List.perm_cons_erase he).symm

/-! ### The splicing loop -/

/-- Reachability in the multigraph with normalised edge list `E`. -/
def Reach (E : List (ℕ × ℕ)) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun x y => normE (x, y) ∈ E)

lemma nextStart_none {c : List ℕ} {r : List (ℕ × ℕ)} (h : nextStart c r = none) :
    ∀ x ∈ c, ∀ e ∈ r, incE x e = false := by
  intro x hx e he
  unfold nextStart at h
  rw [List.min?_eq_none_iff] at h
  have : x ∉ c.filter fun x => r.any (incE x) := by rw [h]; simp
  rw [List.mem_filter] at this
  by_contra hne
  apply this
  refine ⟨hx, ?_⟩
  simp only [List.any_eq_true]
  exact ⟨e, he, by simpa using hne⟩

lemma nextStart_some {c : List ℕ} {r : List (ℕ × ℕ)} {v : ℕ} (h : nextStart c r = some v) :
    v ∈ c ∧ r.any (incE v) = true := by
  unfold nextStart at h
  have := List.mem_filter.mp (List.min?_mem h)
  exact ⟨this.1, this.2⟩

theorem circuitLoop_spec (E : List (ℕ × ℕ)) (v0 : ℕ) (hE : ∀ e ∈ E, normE e = e) :
    ∀ (n : ℕ) (c : List ℕ) (r : List (ℕ × ℕ)), c.head? = some v0 → c.head? = c.getLast? →
      (steps c ++ r).Perm E → (∀ x, deg r x % 2 = 0) → r.length ≤ n →
      ((∀ e ∈ E, Reach E v0 e.1) → ∃ w, circuitLoop n c r = some w) ∧
      ∀ w, circuitLoop n c r = some w → w.head? = w.getLast? ∧ (steps w).Perm E := by
  intro n
  induction n with
  | zero =>
    intro c r _ hcl hp _ hlen
    have hr : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst hr
    simp only [circuitLoop, List.isEmpty_nil, ite_true]
    refine ⟨fun _ => ⟨c, rfl⟩, ?_⟩
    intro w hw
    obtain rfl := Option.some.inj hw
    exact ⟨hcl, by simpa using hp⟩
  | succ n ih =>
    intro c r hh hcl hp hpar hlen
    cases hns : nextStart c r with
    | none =>
      have hstuck := nextStart_none hns
      by_cases hr : r = []
      · subst hr
        simp only [circuitLoop, hns, List.isEmpty_nil, ite_true]
        refine ⟨fun _ => ⟨c, rfl⟩, ?_⟩
        intro w hw
        obtain rfl := Option.some.inj hw
        exact ⟨hcl, by simpa using hp⟩
      · have hcn : circuitLoop (n + 1) c r = none := by
          have : r.isEmpty = false := by
            cases r with
            | nil => exact absurd rfl hr
            | cons _ _ => rfl
          simp [circuitLoop, hns, this]
        refine ⟨?_, by simp [hcn]⟩
        intro hconn
        exfalso
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil r hr
        have hv0 : v0 ∈ c := by
          cases c with
          | nil => simp at hh
          | cons x t => simp at hh; simp [hh]
        have key : ∀ y, Reach E v0 y → y ∈ c := by
          intro y hy
          induction hy with
          | refl => exact hv0
          | @tail b d _ hxy ihy =>
            have hmem : normE (b, d) ∈ steps c ++ r := hp.symm.subset hxy
            rcases List.mem_append.mp hmem with h1 | h1
            · obtain ⟨a, ha, a', ha', hg⟩ := steps_mem c _ h1
              rcases normE_eq_iff.mp hg with ⟨h2, h3⟩ | ⟨h2, h3⟩
              · subst h3; exact ha'
              · subst h3; exact ha
            · have := hstuck b ihy _ h1
              rw [incE_normE] at this; exact absurd this (by simp)
        have heE : e ∈ E := hp.subset (List.mem_append_right _ he)
        have h1 := key _ (hconn e heE)
        have h2 := hstuck _ h1 e he
        have h3 : incE e.1 e = true := by simp [incE]
        rw [h3] at h2; exact absurd h2 (by simp)
    | some v =>
      obtain ⟨hvc, hany⟩ := nextStart_some hns
      rcases hT : trailFrom r.length v r with ⟨p, r'⟩
      have hnormr : ∀ e ∈ r, normE e = e := fun e he =>
        hE e (hp.subset (List.mem_append_right _ he))
      have hpar0 : ∀ x, deg r x % 2 =
          ((if x = v then 1 else 0) + (if x = v then 1 else 0)) % 2 := by
        intro x; have := hpar x; split_ifs <;> omega
      obtain ⟨u, hu, hperm, hst, hpar', hne⟩ :=
        trailFrom_spec r.length v r v le_rfl hnormr hpar0 p r' hT
      have hdeg0 := deg_eq_zero_of_no_inc hst
      have huv : u = v := by
        have := hpar' u
        rw [hdeg0] at this
        by_contra hne'
        simp only [ite_true, hne', ite_false] at this
        omega
      subst huv
      have hpne := hne hany
      have hlen' : r'.length ≤ n := by
        have := hperm.length_eq
        cases p with
        | nil => exact absurd rfl hpne
        | cons q q' =>
          simp only [steps_cons_cons, List.length_append, List.length_cons] at this
          omega
      have hpar'' : ∀ x, deg r' x % 2 = 0 := by
        intro x; have := hpar' x; split_ifs at this <;> omega
      have hp' : ((steps (spliceAt u p c)) ++ r').Perm E := by
        have h1 := (spliceAt_steps hu c hvc).append_right r'
        rw [List.append_assoc] at h1
        exact h1.trans ((hperm.append_left (steps c)).trans hp)
      have hheq : circuitLoop (n + 1) c r = circuitLoop n (spliceAt u p c) r' := by
        simp [circuitLoop, hns, hT]
      rw [hheq]
      exact ih _ _ (by rw [spliceAt_head?]; exact hh)
        (by rw [spliceAt_head?, spliceAt_getLast? hu c hvc]; exact hcl) hp' hpar'' hlen'

/-! ### Correctness -/

lemma deg_even_of_all {es : List (ℕ × ℕ)}
    (h : (vertsOf es).all (fun x => deg es x % 2 == 0) = true) (x : ℕ) : deg es x % 2 = 0 := by
  by_cases hx : x ∈ vertsOf es
  · simp only [List.all_eq_true, beq_iff_eq] at h
    exact h x hx
  · have : deg es x = 0 := List.count_eq_zero_of_not_mem hx
    omega

lemma vertsOf_ne_nil {E : List (ℕ × ℕ)} (h : vertsOf E = []) : E = [] := by
  cases E with
  | nil => rfl
  | cons e t => simp [vertsOf] at h

/-- CO-267. Soundness: whatever the procedure returns is an Euler circuit. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
theorem eulerCircuit_sound {es : List (ℕ × ℕ)} {w : List ℕ} (h : eulerCircuit es = some w) :
    isEulerCircuit es w = true := by
  unfold eulerCircuit at h
  split_ifs at h with hodd
  have hperm := List.perm_insertionSort leE (es.map normE)
  set E := (es.map normE).insertionSort leE with hEdef
  have hE : ∀ e ∈ E, normE e = e := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (hperm.subset he)
    simp only [normE, Prod.mk.injEq]
    omega
  rw [isEulerCircuit, decide_eq_true_iff]
  unfold IsEulerCircuit
  cases hm : (vertsOf E).min? with
  | none =>
    rw [hm] at h
    simp only [Option.some.injEq] at h
    subst h
    have := vertsOf_ne_nil (List.min?_eq_none_iff.mp hm)
    rw [this] at hperm
    exact ⟨rfl, by simpa [steps] using hperm.symm⟩
  | some v0 =>
    rw [hm] at h
    simp only at h
    have hev : ∀ x, deg E x % 2 = 0 := fun x => by
      rw [deg_perm hperm x, deg_map_normE]; exact deg_even_of_all hodd x
    have := (circuitLoop_spec E v0 hE es.length [v0] E rfl rfl
      (by simpa [steps_single] using List.Perm.refl E) hev (by simp [hEdef])).2 w h
    exact ⟨this.1, this.2.trans hperm⟩

/-- The multigraph given by `es` is connected (on its non-isolated vertices). -/
def EdgeListConnected (es : List (ℕ × ℕ)) : Prop :=
  ∀ a b, 0 < deg es a → 0 < deg es b →
    Relation.ReflTransGen (fun x y => normE (x, y) ∈ es.map normE) a b

/-- CO-267. Completeness: if all degrees are even and the edges form a connected multigraph,
the procedure finds an Euler circuit. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
theorem eulerCircuit_complete {es : List (ℕ × ℕ)} (hev : ∀ x, Even (deg es x))
    (hconn : EdgeListConnected es) : eulerCircuit es ≠ none := by
  have hodd : (vertsOf es).all (fun x => deg es x % 2 == 0) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    intro x _
    exact Nat.even_iff.mp (hev x)
  unfold eulerCircuit
  simp only [hodd, ite_true]
  have hperm := List.perm_insertionSort leE (es.map normE)
  set E := (es.map normE).insertionSort leE with hEdef
  have hE : ∀ e ∈ E, normE e = e := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (hperm.subset he)
    simp only [normE, Prod.mk.injEq]
    omega
  cases hm : (vertsOf E).min? with
  | none => simp
  | some v0 =>
    simp only
    have hev' : ∀ x, deg E x % 2 = 0 := fun x => by
      rw [deg_perm hperm x, deg_map_normE]; exact Nat.even_iff.mp (hev x)
    have hv0 : v0 ∈ vertsOf E := List.min?_mem hm
    have hdv0 : 0 < deg es v0 := by
      rw [← deg_map_normE, ← deg_perm hperm]
      exact List.count_pos_iff.mpr hv0
    have hR : ∀ e ∈ E, Reach E v0 e.1 := by
      intro e he
      have hd : 0 < deg es e.1 := by
        rw [← deg_map_normE, ← deg_perm hperm]
        apply List.count_pos_iff.mpr
        simp only [vertsOf, List.mem_flatMap, List.mem_cons]
        exact ⟨e, he, Or.inl rfl⟩
      exact Relation.ReflTransGen.mono (fun a b h => hperm.symm.subset h) _ _ (hconn v0 e.1 hdv0 hd)
    have := (circuitLoop_spec E v0 hE es.length [v0] E rfl rfl
      (by simpa [steps_single] using List.Perm.refl E) hev' (by simp [hEdef])).1 hR
    obtain ⟨w, hw⟩ := this
    rw [hw]; simp

/-! ### Examples -/

/-- Two triangles sharing the vertex `2`. -/
def bowtie : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]

example : (eulerCircuit bowtie).isSome = true := by decide +kernel

example : ∀ w, eulerCircuit bowtie = some w → isEulerCircuit bowtie w = true :=
  fun _ h => eulerCircuit_sound h

example : eulerCircuit bowtie = some [0, 1, 2, 3, 4, 2, 0] := by decide +kernel

/-- A path has odd degrees: rejected. -/
example : eulerCircuit [(0, 1), (1, 2)] = none := by decide +kernel

/-- Two disjoint triangles: even degrees but disconnected, rejected. -/
example : eulerCircuit [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)] = none := by
  decide +kernel

end UndergradKB.Combinatorics.Euler
