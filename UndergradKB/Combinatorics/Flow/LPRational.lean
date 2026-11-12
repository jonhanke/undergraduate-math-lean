import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Linear programs with rational data have rational optima (Keller–Trotter, Chapter 13)

Mathlib has no linear programming theory, so we prove the statement from scratch by Fourier–Motzkin
elimination.  A system of linear inequalities in `n` variables is a list of rows
`(a, b) : (Fin n → ℚ) × ℚ`, meaning `∑ j, a j * x j ≤ b`.  Eliminating the last variable
(`LPRational.elim`) keeps the rows with zero last coefficient and adds one combined row for every pair
of a row with positive and a row with negative last coefficient.

* `LPRational.restr` : a solution of a system restricts to a solution of its elimination;
* `LPRational.ext`   : a solution of the elimination extends to the last variable (in any ordered
  field, so rational solutions extend to rational solutions);
* `fourierMotzkin_rational` : a system with rational data that has a real solution has a rational one;
* `LPRational.proj`  : projecting a rational polyhedron to its first coordinate gives a set cut out
  by finitely many rational inequalities `α t ≤ β`;
* `lp_rational_optimum` : an attained optimum of a rational linear program is rational and attained
  at a rational point.
-/

namespace UndergradKB.Combinatorics.Flow

set_option linter.unusedSectionVars false

namespace LPRational

/-- A row `(a, b)` of a system in `n` variables: the inequality `∑ j, a j * x j ≤ b`. -/
abbrev Row (n : ℕ) := (Fin n → ℚ) × ℚ

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The point `x` satisfies the row `r`. -/
def Sat {n : ℕ} (x : Fin n → K) (r : Row n) : Prop := ∑ j, (r.1 j : K) * x j ≤ (r.2 : K)

/-- The point `x` satisfies all rows of `S`. -/
def SatAll {n : ℕ} (x : Fin n → K) (S : List (Row n)) : Prop := ∀ r ∈ S, Sat x r

/-- Combination of a row `p` (positive last coefficient) with a row `q` (negative last coefficient)
cancelling the last variable. -/
def comb {n : ℕ} (p q : Row (n + 1)) : Row n :=
  (fun j => -q.1 (Fin.last n) * p.1 j.castSucc + p.1 (Fin.last n) * q.1 j.castSucc,
    -q.1 (Fin.last n) * p.2 + p.1 (Fin.last n) * q.2)

/-- Fourier–Motzkin elimination of the last variable. -/
def elim {n : ℕ} (S : List (Row (n + 1))) : List (Row n) :=
  (S.filter (fun r => r.1 (Fin.last n) = 0)).map (fun r => (fun j => r.1 j.castSucc, r.2)) ++
    (S.filter (fun r => 0 < r.1 (Fin.last n))).flatMap
      (fun p => (S.filter (fun r => r.1 (Fin.last n) < 0)).map (comb p))

lemma mem_elim {n : ℕ} {S : List (Row (n + 1))} {r : Row n} :
    r ∈ elim S ↔ (∃ s ∈ S, s.1 (Fin.last n) = 0 ∧ r = ((fun j => s.1 j.castSucc), s.2)) ∨
      (∃ p ∈ S, ∃ q ∈ S, 0 < p.1 (Fin.last n) ∧ q.1 (Fin.last n) < 0 ∧ r = comb p q) := by
  simp only [elim, List.mem_append, List.mem_map, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq]
  constructor
  · rintro (⟨s, ⟨hs, h0⟩, rfl⟩ | ⟨p, ⟨hp, h0⟩, q, ⟨hq, h1⟩, rfl⟩)
    · exact Or.inl ⟨s, hs, h0, rfl⟩
    · exact Or.inr ⟨p, hp, q, hq, h0, h1, rfl⟩
  · rintro (⟨s, hs, h0, rfl⟩ | ⟨p, hp, q, hq, h0, h1, rfl⟩)
    · exact Or.inl ⟨s, ⟨hs, h0⟩, rfl⟩
    · exact Or.inr ⟨p, ⟨hp, h0⟩, q, ⟨hq, h1⟩, rfl⟩

lemma sum_split {n : ℕ} (a : Fin (n + 1) → ℚ) (x : Fin (n + 1) → K) :
    ∑ j, (a j : K) * x j =
      ∑ j : Fin n, (a j.castSucc : K) * x j.castSucc + (a (Fin.last n) : K) * x (Fin.last n) :=
  Fin.sum_univ_castSucc (fun j => (a j : K) * x j)

lemma comb_sum {n : ℕ} (p q : Row (n + 1)) (z : Fin n → K) :
    ∑ j, ((comb p q).1 j : K) * z j =
      -(q.1 (Fin.last n) : K) * ∑ j, (p.1 j.castSucc : K) * z j +
        (p.1 (Fin.last n) : K) * ∑ j, (q.1 j.castSucc : K) * z j := by
  simp only [comb, Rat.cast_add, Rat.cast_mul, Rat.cast_neg, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> (apply Finset.sum_congr rfl; intros; ring)

lemma comb_rhs {n : ℕ} (p q : Row (n + 1)) :
    (((comb p q).2 : ℚ) : K) =
      -(q.1 (Fin.last n) : K) * (p.2 : K) + (p.1 (Fin.last n) : K) * (q.2 : K) := by
  simp [comb]

/-- A solution of a system restricts to a solution of its elimination. -/
lemma restr {n : ℕ} {S : List (Row (n + 1))} {x : Fin (n + 1) → K} (h : SatAll x S) :
    SatAll (fun j : Fin n => x j.castSucc) (elim S) := by
  intro r hr
  rcases mem_elim.1 hr with ⟨s, hs, h0, rfl⟩ | ⟨p, hp, q, hq, h0, h1, rfl⟩
  · have := h s hs
    unfold Sat at this ⊢
    rw [sum_split, h0] at this
    simpa using this
  · have hp' := h p hp
    have hq' := h q hq
    unfold Sat at hp' hq' ⊢
    rw [sum_split] at hp' hq'
    rw [comb_sum, comb_rhs]
    have h0' : (0 : K) < (p.1 (Fin.last n) : K) := by exact_mod_cast h0
    have h1' : (q.1 (Fin.last n) : K) < 0 := by exact_mod_cast h1
    nlinarith [mul_le_mul_of_nonneg_left hp' (neg_nonneg.2 h1'.le),
      mul_le_mul_of_nonneg_left hq' h0'.le]

lemma exists_between_aux (L U : List K) (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : K, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u := by
  induction L with
  | nil =>
    induction U with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons u U ih =>
      obtain ⟨t, ht⟩ := ih (by simp)
      exact ⟨min t u, by simp, by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (ht.2 w hw)⟩
  | cons l L ih =>
    obtain ⟨t, ht1, ht2⟩ := ih (fun l' hl' u hu => h l' (List.mem_cons_of_mem _ hl') u hu)
    refine ⟨max t l, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact le_max_right _ _
      · exact (ht1 w hw).trans (le_max_left _ _)
    · intro u hu
      exact max_le (ht2 u hu) (h l (by simp) u hu)

/-- A solution of the elimination of `S` extends to a solution of `S` (in any ordered field). -/
lemma ext {n : ℕ} {S : List (Row (n + 1))} {y : Fin n → K} (h : SatAll y (elim S)) :
    ∃ t : K, SatAll (Fin.snoc y t : Fin (n + 1) → K) S := by
  set base : Row (n + 1) → K := fun s => ∑ j : Fin n, (s.1 j.castSucc : K) * y j with hbase
  set bound : Row (n + 1) → K := fun s => ((s.2 : K) - base s) / (s.1 (Fin.last n) : K)
    with hbound
  have key : ∀ l ∈ (S.filter (fun r => r.1 (Fin.last n) < 0)).map bound,
      ∀ u ∈ (S.filter (fun r => 0 < r.1 (Fin.last n))).map bound, l ≤ u := by
    intro l hl u hu
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hl hu
    obtain ⟨q, ⟨hq, h1⟩, rfl⟩ := hl
    obtain ⟨p, ⟨hp, h0⟩, rfl⟩ := hu
    have hc := h (comb p q) (mem_elim.2 (Or.inr ⟨p, hp, q, hq, h0, h1, rfl⟩))
    unfold Sat at hc
    rw [comb_sum, comb_rhs] at hc
    have h0' : (0 : K) < (p.1 (Fin.last n) : K) := by exact_mod_cast h0
    have h1' : (q.1 (Fin.last n) : K) < 0 := by exact_mod_cast h1
    have hu : (p.1 (Fin.last n) : K) * bound p = (p.2 : K) - base p := by
      simp only [hbound]; field_simp
    have hl : (q.1 (Fin.last n) : K) * bound q = (q.2 : K) - base q := by
      have hn := h1'.ne
      simp only [hbound]; field_simp
    by_contra hlt
    push Not at hlt
    have hneg : (p.1 (Fin.last n) : K) * (q.1 (Fin.last n) : K) < 0 := mul_neg_of_pos_of_neg h0' h1'
    have := mul_neg_of_neg_of_pos hneg (sub_pos.2 hlt)
    simp only [hbase] at hu hl
    nlinarith
  obtain ⟨t, ht1, ht2⟩ := exists_between_aux _ _ key
  refine ⟨t, ?_⟩
  intro s hs
  unfold Sat
  rw [sum_split]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rcases lt_trichotomy (s.1 (Fin.last n)) 0 with h1 | h0 | h0
  · have h1' : (s.1 (Fin.last n) : K) < 0 := by exact_mod_cast h1
    have hl : bound s ≤ t := ht1 _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simpa using h1⟩, rfl⟩)
    have hm : (s.1 (Fin.last n) : K) * t ≤ (s.1 (Fin.last n) : K) * bound s :=
      mul_le_mul_of_nonpos_left hl h1'.le
    have : (s.1 (Fin.last n) : K) * bound s = (s.2 : K) - base s := by
      have hn := h1'.ne
      simp only [hbound]; field_simp
    simp only [hbase] at this
    linarith
  · have := h _ (mem_elim.2 (Or.inl ⟨s, hs, h0, rfl⟩))
    unfold Sat at this
    simp only [h0, Rat.cast_zero, zero_mul, add_zero]
    exact this
  · have h0' : (0 : K) < (s.1 (Fin.last n) : K) := by exact_mod_cast h0
    have hl : t ≤ bound s := ht2 _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simpa using h0⟩, rfl⟩)
    have hm : (s.1 (Fin.last n) : K) * t ≤ (s.1 (Fin.last n) : K) * bound s :=
      mul_le_mul_of_nonneg_left hl h0'.le
    have : (s.1 (Fin.last n) : K) * bound s = (s.2 : K) - base s := by
      simp only [hbound]; field_simp
    simp only [hbase] at this
    linarith

/-- Projection of a rational polyhedron on its first coordinate is cut out by finitely many
rational inequalities `α t ≤ β`. -/
theorem proj : ∀ (n : ℕ) (S : List (Row (n + 1))), ∃ T : List (ℚ × ℚ), ∀ t : ℝ,
    (∃ x : Fin (n + 1) → ℝ, x 0 = t ∧ SatAll x S) ↔ ∀ p ∈ T, (p.1 : ℝ) * t ≤ p.2 := by
  intro n
  induction n with
  | zero =>
    intro S
    refine ⟨S.map (fun r => (r.1 0, r.2)), fun t => ?_⟩
    constructor
    · rintro ⟨x, rfl, hx⟩ p hp
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
      have := hx r hr
      unfold Sat at this
      simpa using this
    · intro h
      refine ⟨fun _ => t, rfl, fun r hr => ?_⟩
      have := h _ (List.mem_map.2 ⟨r, hr, rfl⟩)
      unfold Sat
      simpa using this
  | succ n ih =>
    intro S
    obtain ⟨T, hT⟩ := ih (elim S)
    refine ⟨T, fun t => ?_⟩
    rw [← hT t]
    constructor
    · rintro ⟨x, hx0, hx⟩
      exact ⟨fun j => x j.castSucc, by simpa using hx0, restr hx⟩
    · rintro ⟨x, hx0, hx⟩
      obtain ⟨s, hs⟩ := ext hx
      refine ⟨Fin.snoc x s, ?_, hs⟩
      have : (Fin.snoc x s : Fin (n + 2) → ℝ) (0 : Fin (n + 1)).castSucc = x 0 :=
        Fin.snoc_castSucc _ _ _
      simpa using this.trans hx0

end LPRational

open LPRational

/-- Fourier–Motzkin: a finite system of linear inequalities with rational data that has a real
solution has a rational solution. -/
theorem fourierMotzkin_rational : ∀ (n : ℕ) (S : List (Row n)),
    (∃ x : Fin n → ℝ, SatAll x S) → ∃ y : Fin n → ℚ, SatAll y S := by
  intro n
  induction n with
  | zero =>
    intro S ⟨x, hx⟩
    refine ⟨fun _ => 0, fun r hr => ?_⟩
    have := hx r hr
    unfold Sat at this ⊢
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at this ⊢
    have h : (0 : ℝ) ≤ (r.2 : ℝ) := this
    exact_mod_cast h
  | succ n ih =>
    intro S ⟨x, hx⟩
    obtain ⟨y, hy⟩ := ih (elim S) ⟨_, restr hx⟩
    obtain ⟨t, ht⟩ := ext hy
    exact ⟨_, ht⟩

/-- The point `x` satisfies the linear inequalities `∑ j, a i j * x j ≤ b i` for all `i`. -/
def LPFeasible {m d : ℕ} (a : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (x : Fin d → ℝ) : Prop :=
  ∀ i, ∑ j, (a i j : ℝ) * x j ≤ b i

namespace LPRational

lemma rat_max (T : List (ℚ × ℚ)) (v : ℝ) (hv : ∀ p ∈ T, (p.1 : ℝ) * v ≤ p.2)
    (hmax : ∀ t : ℝ, (∀ p ∈ T, (p.1 : ℝ) * t ≤ p.2) → t ≤ v) : ∃ q : ℚ, (q : ℝ) = v := by
  classical
  by_cases hne : (T.toFinset.filter (fun p => 0 < p.1)).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ (fun p : ℚ × ℚ => p.2 / p.1) hne
    simp only [Finset.mem_filter, List.mem_toFinset] at hp0
    obtain ⟨hp0T, hp0pos⟩ := hp0
    have hp0' : (0 : ℝ) < p0.1 := by exact_mod_cast hp0pos
    refine ⟨p0.2 / p0.1, ?_⟩
    have hq : (p0.1 : ℝ) * ((p0.2 / p0.1 : ℚ) : ℝ) = p0.2 := by
      push_cast; field_simp
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      set q : ℝ := ((p0.2 / p0.1 : ℚ) : ℝ) with hqdef
      have := hmax ((v + q) / 2) (by
        intro p hp
        rcases lt_trichotomy p.1 0 with h1 | h1 | h1
        · have h1' : (p.1 : ℝ) < 0 := by exact_mod_cast h1
          have := hv p hp
          nlinarith
        · have := hv p hp
          have h1' : (p.1 : ℝ) = 0 := by exact_mod_cast h1
          rw [h1'] at this ⊢
          simpa using this
        · have h1' : (0 : ℝ) < p.1 := by exact_mod_cast h1
          have hle : p0.2 / p0.1 ≤ p.2 / p.1 :=
            hmin p (by simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨hp, h1⟩)
          have hle' : (p.1 : ℚ) * (p0.2 / p0.1) ≤ p.2 := by
            rwa [le_div_iff₀ h1, mul_comm] at hle
          have hle'' : (p.1 : ℝ) * q ≤ p.2 := by
            rw [hqdef]; exact_mod_cast hle'
          nlinarith)
      linarith
    · have := hv p0 hp0T
      by_contra hlt
      push Not at hlt
      nlinarith
  · refine absurd (hmax (v + 1) ?_) (by linarith)
    intro p hp
    have hp' : p.1 ≤ 0 := by
      by_contra hc
      exact hne ⟨p, by simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨hp, not_le.1 hc⟩⟩
    have hp'' : (p.1 : ℝ) ≤ 0 := by exact_mod_cast hp'
    have := hv p hp
    nlinarith

end LPRational

/-- CO-299. Linear programs with rational data have rational optima.  Let `a`, `b`, `c` be rational
data and let `xs` be a real feasible point of `a x ≤ b` at which `c · x` is maximal among all real
feasible points.  Then the optimal value is a rational number `v`, and it is attained at a rational
feasible point `y`. -/
@[kb "kellertrotter2017" "text (linear programs with rational data have rational optima), p. 297"]
theorem lp_rational_optimum {m d : ℕ} (a : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (xs : Fin d → ℝ) (hxs : LPFeasible a b xs)
    (hmax : ∀ x : Fin d → ℝ, LPFeasible a b x → ∑ j, (c j : ℝ) * x j ≤ ∑ j, (c j : ℝ) * xs j) :
    ∃ v : ℚ, (v : ℝ) = ∑ j, (c j : ℝ) * xs j ∧
      ∃ y : Fin d → ℚ, (∀ i, ∑ j, a i j * y j ≤ b i) ∧ ∑ j, c j * y j = v := by
  classical
  -- the projection system in the variables `(t, x)`
  set S : List (Row (d + 1)) :=
    List.ofFn (fun i : Fin m => ((Fin.cons 0 (a i) : Fin (d + 1) → ℚ), b i)) ++
      [((Fin.cons 1 (fun j => - c j) : Fin (d + 1) → ℚ), 0)] with hS
  obtain ⟨T, hT⟩ := LPRational.proj d S
  have hSat : ∀ x : Fin (d + 1) → ℝ, LPRational.SatAll x S ↔
      (LPFeasible a b (fun j => x j.succ) ∧ x 0 ≤ ∑ j, (c j : ℝ) * x j.succ) := by
    intro x
    have h1 : ∀ i, LPRational.Sat x ((Fin.cons 0 (a i) : Fin (d + 1) → ℚ), b i) ↔
        ∑ j, (a i j : ℝ) * x j.succ ≤ b i := by
      intro i; simp [LPRational.Sat, Fin.sum_univ_succ]
    have h2 : LPRational.Sat x ((Fin.cons 1 (fun j => - c j) : Fin (d + 1) → ℚ), 0) ↔
        x 0 ≤ ∑ j, (c j : ℝ) * x j.succ := by
      simp only [LPRational.Sat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [Rat.cast_one, Rat.cast_neg, Rat.cast_zero, one_mul, neg_mul,
        Finset.sum_neg_distrib]
      constructor <;> intro h <;> linarith
    unfold LPRational.SatAll
    rw [hS]
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    constructor
    · intro h
      refine ⟨fun i => (h1 i).1 (h _ (Or.inl ⟨i, rfl⟩)), h2.1 (h _ (Or.inr rfl))⟩
    · rintro ⟨hf, ho⟩ r (⟨i, rfl⟩ | rfl)
      · exact (h1 i).2 (hf i)
      · exact h2.2 ho
  have hchar : ∀ t : ℝ, (∃ x : Fin d → ℝ, LPFeasible a b x ∧ t ≤ ∑ j, (c j : ℝ) * x j) ↔
      ∀ p ∈ T, (p.1 : ℝ) * t ≤ p.2 := by
    intro t
    rw [← hT t]
    constructor
    · rintro ⟨x, hx, ht⟩
      exact ⟨Fin.cons t x, by simp, (hSat _).2 (by simpa using ⟨hx, ht⟩)⟩
    · rintro ⟨x, hx0, hx⟩
      obtain ⟨hf, ho⟩ := (hSat x).1 hx
      exact ⟨fun j => x j.succ, hf, hx0 ▸ ho⟩
  have hv : ∀ p ∈ T, (p.1 : ℝ) * (∑ j, (c j : ℝ) * xs j) ≤ p.2 :=
    (hchar _).1 ⟨xs, hxs, le_refl _⟩
  have hm : ∀ t : ℝ, (∀ p ∈ T, (p.1 : ℝ) * t ≤ p.2) → t ≤ ∑ j, (c j : ℝ) * xs j := by
    intro t ht
    obtain ⟨x, hx, htx⟩ := (hchar t).2 ht
    exact htx.trans (hmax x hx)
  obtain ⟨q, hq⟩ := LPRational.rat_max T _ hv hm
  -- a rational point attaining the value `q`
  have hex : ∃ x : Fin d → ℝ, LPRational.SatAll x
      (List.ofFn (fun i : Fin m => (a i, b i)) ++ [((fun j => - c j : Fin d → ℚ), -q)]) := by
    refine ⟨xs, ?_⟩
    intro r hr
    simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hr
    rcases hr with ⟨i, rfl⟩ | rfl
    · exact hxs i
    · unfold LPRational.Sat
      simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
      linarith
  obtain ⟨y, hy⟩ := fourierMotzkin_rational d _ hex
  have hyA : ∀ i, ∑ j, a i j * y j ≤ b i := by
    intro i
    have := hy (a i, b i) (by simp only [List.mem_append, List.mem_ofFn]; exact Or.inl ⟨i, rfl⟩)
    simpa [LPRational.Sat] using this
  have hyc : q ≤ ∑ j, c j * y j := by
    have := hy ((fun j => - c j : Fin d → ℚ), -q) (by simp)
    simp only [LPRational.Sat, Rat.cast_id, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hyr : ((∑ j, c j * y j : ℚ) : ℝ) ≤ q := by
    have := hmax (fun j => (y j : ℝ)) (by
      intro i
      have := hyA i
      show ∑ j, (a i j : ℝ) * (y j : ℝ) ≤ b i
      exact_mod_cast this)
    rw [hq]
    push_cast
    exact this
  refine ⟨q, hq, y, hyA, le_antisymm ?_ hyc⟩
  exact_mod_cast hyr

end UndergradKB.Combinatorics.Flow
