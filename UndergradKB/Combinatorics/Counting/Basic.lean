import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import UndergradKB.Common.Attr

/-!
# Elementary counting (Keller–Trotter, chapter 2)

Bit strings and subsets, compositions, stars and bars with lower bounds, graphs on `[n]`,
and the closed forms for sums of odd numbers and of cubes.
-/

namespace UndergradKB.Combinatorics

open Finset

/-! ### CO-007: subsets and bit strings -/

/-- The bijection between subsets of a finite type and bit strings (a subset goes to its
indicator function). -/
def subsetEquivBits (α : Type*) [Fintype α] [DecidableEq α] : Finset α ≃ (α → Bool) where
  toFun s i := decide (i ∈ s)
  invFun f := univ.filter (fun i => f i = true)
  left_inv s := by ext i; simp
  right_inv f := by funext i; simp

/-- CO-007. The subsets of an `n`-set are in bijection with bit strings of length `n`; in
particular there are `2 ^ n` of them. -/
@[kb "kellertrotter2017" "Exercise 2.12, p. 46"]
theorem card_bitStrings (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- CO-007. Subsets of size `k` correspond to bit strings with exactly `k` ones, so there are
`C(n,k)` such strings. -/
@[kb "kellertrotter2017" "Exercise 2.12, p. 46"]
theorem card_bitStrings_with_ones (n k : ℕ) :
    #{f : Fin n → Bool | #{i | f i = true} = k} = n.choose k := by
  classical
  conv_rhs => rw [← Finset.card_fin n, ← Finset.card_powersetCard]
  refine Finset.card_bij' (fun f _ => univ.filter (fun i => f i = true))
    (fun s _ i => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro f hf
    simpa using hf
  · intro s hs
    simpa using hs
  · intro f _
    funext i
    simp
  · intro s _
    ext i
    simp

/-- CO-007 (set form). The bijection `subsetEquivBits` sends the `k`-subsets exactly to the bit
strings with `k` ones. -/
@[kb "kellertrotter2017" "Exercise 2.12, p. 46"]
theorem subsetEquivBits_card (n : ℕ) (s : Finset (Fin n)) :
    #{i | subsetEquivBits (Fin n) s i = true} = #s := by
  simp [subsetEquivBits]

/-! ### Stars and bars with lower bounds (CO-008, CO-010) -/

section StarsBars

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of `ι`-indexed tuples of naturals with sum `n` is `C(|ι| + n - 1, n)`. -/
theorem card_piAntidiag_univ (n : ℕ) :
    #(piAntidiag (univ : Finset ι) n) = (Fintype.card ι + n - 1).choose n := by
  have := card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset ι)) n
  simpa [finsuppAntidiag] using this

/-- Solutions in naturals of `∑ x i = n` with `a i ≤ x i`. -/
def lowerBoundedSolutions (a : ι → ℕ) (n : ℕ) : Finset (ι → ℕ) :=
  (piAntidiag (univ : Finset ι) n).filter (fun x => ∀ i, a i ≤ x i)

/-- CO-010. Counting solutions of `∑ x i = n` with lower bounds `x i ≥ a i`: shift the
variables by `a`, giving `C(|ι| + (n - ∑ a) - 1, n - ∑ a)` solutions when `∑ a ≤ n`. -/
@[kb "kellertrotter2017" "Example 2.24, p. 50"]
theorem card_lowerBoundedSolutions (a : ι → ℕ) (n : ℕ) (h : ∑ i, a i ≤ n) :
    #(lowerBoundedSolutions a n) =
      (Fintype.card ι + (n - ∑ i, a i) - 1).choose (n - ∑ i, a i) := by
  rw [← card_piAntidiag_univ]
  refine Finset.card_nbij' (fun x => x - a) (fun y => y + a) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [lowerBoundedSolutions, coe_filter, mem_piAntidiag, Set.mem_ofPred_eq, mem_coe] at hx ⊢
    obtain ⟨⟨hs, -⟩, hle⟩ := hx
    refine ⟨?_, by simp⟩
    rw [show (∑ i, (x - a) i) = ∑ i, (x i - a i) from rfl,
      Finset.sum_tsub_distrib _ (fun i _ => hle i), hs]
  · intro y hy
    simp only [lowerBoundedSolutions, coe_filter, mem_piAntidiag, Set.mem_ofPred_eq, mem_coe] at hy ⊢
    refine ⟨⟨?_, by simp⟩, fun i => by simp⟩
    rw [show (∑ i, (y + a) i) = ∑ i, y i + ∑ i, a i from Finset.sum_add_distrib]
    rw [hy.1]; omega
  · intro x hx
    simp only [lowerBoundedSolutions, coe_filter, Set.mem_ofPred_eq] at hx
    funext i
    show x i - a i + a i = x i
    exact Nat.sub_add_cancel (hx.2 i)
  · intro y _
    funext i
    simp

/-- CO-010. If the lower bounds already exceed `n`, there are no solutions. -/
@[kb "kellertrotter2017" "Example 2.24, p. 50"]
theorem card_lowerBoundedSolutions_of_lt (a : ι → ℕ) (n : ℕ) (h : n < ∑ i, a i) :
    #(lowerBoundedSolutions a n) = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [lowerBoundedSolutions, mem_filter, mem_piAntidiag] at hx
  have h1 := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hx.2 i)
  have h2 : ∑ i, x i = n := hx.1.1
  omega

/-- The compositions of `n` into `r` positive parts, as functions `Fin r → ℕ`. -/
def positiveCompositions (r n : ℕ) : Finset (Fin r → ℕ) :=
  (piAntidiag (univ : Finset (Fin r)) n).filter (fun f => ∀ i, 0 < f i)

/-- CO-008. Writing `n` as an ordered sum of `r` positive integers can be done in
`C(n-1, r-1)` ways. -/
@[kb "kellertrotter2017" "Example 2.21, p. 49"]
theorem card_positiveCompositions (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    #(positiveCompositions r n) = (n - 1).choose (r - 1) := by
  have key : positiveCompositions r n = lowerBoundedSolutions (fun _ => 1) n := by
    ext f; simp [positiveCompositions, lowerBoundedSolutions, Nat.one_le_iff_ne_zero,
      Nat.pos_iff_ne_zero]
  rw [key]
  by_cases hrn : r ≤ n
  · rw [card_lowerBoundedSolutions _ _ (by simpa using hrn)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [show r + (n - r) - 1 = n - 1 by omega,
      ← Nat.choose_symm (show r - 1 ≤ n - 1 by omega)]
    congr 1
    omega
  · rw [card_lowerBoundedSolutions_of_lt _ _ (by simpa using not_le.1 hrn)]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

/-- CO-010 (equation, positive variables): `x₁ + ⋯ + x_r = n` with all `x i > 0`. -/
@[kb "kellertrotter2017" "Example 2.25, p. 50"]
theorem card_solutions_pos (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    #(positiveCompositions r n) = (n - 1).choose (r - 1) :=
  card_positiveCompositions r n hr hn

/-- CO-010 (equation, nonnegative variables): the book's case `x i ≥ 0` with equality. -/
@[kb "kellertrotter2017" "Example 2.25, p. 50"]
theorem card_solutions_nonneg (r n : ℕ) (hr : 0 < r) :
    #(piAntidiag (univ : Finset (Fin r)) n) = (n + r - 1).choose (r - 1) := by
  rw [card_piAntidiag_univ, Fintype.card_fin]
  rw [← Nat.choose_symm (show r - 1 ≤ n + r - 1 by omega),
    show n + r - 1 - (r - 1) = n by omega, Nat.add_comm r n]

/-- Solutions of the inequality `∑ x i ≤ n` with `x i ≥ a i` (all `x i` bounded by `n`). -/
def lowerBoundedIneqSolutions (a : ι → ℕ) (n : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ => range (n + 1))).filter (fun x => ∑ i, x i ≤ n ∧ ∀ i, a i ≤ x i)

/-- CO-010 (inequality version). Adding a slack variable `x₀ = n - ∑ x i` turns `∑ x i ≤ n`
into an equation in one more variable: with `∑ a ≤ n` the count is
`C(|ι| + (n - ∑ a), n - ∑ a)`. -/
@[kb "kellertrotter2017" "Example 2.25, p. 50"]
theorem card_lowerBoundedIneqSolutions (a : ι → ℕ) (n : ℕ) (h : ∑ i, a i ≤ n) :
    #(lowerBoundedIneqSolutions a n) =
      (Fintype.card ι + (n - ∑ i, a i)).choose (n - ∑ i, a i) := by
  let a' : Option ι → ℕ := fun o => o.elim 0 a
  have h' : ∑ o, a' o = ∑ i, a i := by simp [a', Fintype.sum_option]
  have e := card_lowerBoundedSolutions a' n (by rw [h']; exact h)
  rw [h', Fintype.card_option] at e
  rw [show Fintype.card ι + (n - ∑ i, a i) = Fintype.card ι + 1 + (n - ∑ i, a i) - 1 by omega,
    ← e]
  refine Finset.card_nbij' (fun x o => o.elim (n - ∑ i, x i) x) (fun y i => y (some i))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [lowerBoundedIneqSolutions, coe_filter, Fintype.mem_piFinset, mem_range,
      Set.mem_ofPred_eq] at hx
    simp only [lowerBoundedSolutions, coe_filter, mem_piAntidiag, Set.mem_ofPred_eq]
    refine ⟨⟨?_, by simp⟩, ?_⟩
    · simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
      omega
    · intro o
      cases o with
      | none => simp [a']
      | some i => simpa [a'] using hx.2.2 i
  · intro y hy
    simp only [lowerBoundedSolutions, coe_filter, mem_piAntidiag, Set.mem_ofPred_eq] at hy
    simp only [lowerBoundedIneqSolutions, coe_filter, Fintype.mem_piFinset, mem_range,
      Set.mem_ofPred_eq]
    have hs := hy.1.1
    rw [Fintype.sum_option] at hs
    refine ⟨fun i => ?_, by omega, fun i => by simpa [a'] using hy.2 (some i)⟩
    have : y (some i) ≤ ∑ j, y (some j) :=
      Finset.single_le_sum (f := fun j => y (some j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  · intro x hx
    simp only [lowerBoundedIneqSolutions, coe_filter, Fintype.mem_piFinset, mem_range,
      Set.mem_ofPred_eq] at hx
    rfl
  · intro y hy
    simp only [lowerBoundedSolutions, coe_filter, mem_piAntidiag, Set.mem_ofPred_eq] at hy
    have hs := hy.1.1
    rw [Fintype.sum_option] at hs
    funext o
    cases o with
    | none => simp only [Option.elim_none]; omega
    | some i => rfl

end StarsBars

/-! ### CO-031, CO-056, CO-068: three identities -/

/-- CO-031. `∑ C(n,i) 2^i = 3^n` (count ternary strings by the positions that are not `2`). -/
@[kb "kellertrotter2017" "Example 2.19, p. 48"]
theorem sum_choose_mul_two_pow (n : ℕ) :
    ∑ i ∈ range (n + 1), n.choose i * 2 ^ i = 3 ^ n := by
  rw [← (show (2 + 1 : ℕ) ^ n = 3 ^ n by norm_num), add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/-- CO-056. The sum of the first `n` odd positive integers is `n ^ 2`. -/
@[kb "kellertrotter2017" "Proposition 3.13, p. 76"]
theorem sum_first_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem sum_cubes_eq_sq_sum (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 3 = (∑ i ∈ range (n + 1), i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (∑ i ∈ range (n + 1), i) * 2 = (n + 1) * n := by
      simpa using Finset.sum_range_id_mul_two (n + 1)
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (n + 1)]
    nlinarith [h2]

/-- CO-068. The sum of the first `n` cubes is `(n(n+1)/2)^2`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 1.4.1, p. 20"]
theorem sum_cubes (n : ℕ) : ∑ i ∈ Icc 1 n, i ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  have h1 : ∑ i ∈ Icc 1 n, i ^ 3 = ∑ i ∈ range (n + 1), i ^ 3 := by
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (Nat.le_add_left 1 n)]
    simp
    rfl
  rw [h1, sum_cubes_eq_sq_sum, Finset.sum_range_id]
  simp [mul_comm]

/-! ### CO-011, CO-012: lattice paths -/

section LatticePaths

/-- One step of a lattice path: one unit to the right or one unit up. -/
def LatticeStep (p q : ℤ × ℤ) : Prop := q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)

/-- CO-011. A lattice path is a list of integer points in which each point is reached from the
previous one by a step right or a step up. -/
@[kb "kellertrotter2017" "Definition (unnumbered) lattice path, p. 50"]
def IsLatticePath (l : List (ℤ × ℤ)) : Prop := l.IsChain LatticeStep

/-- The lattice paths starting at `s` and ending at `e`. -/
def latticePaths (s e : ℤ × ℤ) : Set (List (ℤ × ℤ)) :=
  {l | IsLatticePath l ∧ l.head? = some s ∧ l.getLast? = some e}

/-- Move horizontally (`true`, `H`) or vertically (`false`, `V`). -/
def moveBy (b : Bool) (p : ℤ × ℤ) : ℤ × ℤ := if b then (p.1 + 1, p.2) else (p.1, p.2 + 1)

/-- The lattice path started at `s` and following an `H`/`V` string. -/
def pathOfWord : ℤ × ℤ → List Bool → List (ℤ × ℤ)
  | s, [] => [s]
  | s, b :: w => s :: pathOfWord (moveBy b s) w

theorem pathOfWord_cons_exists (s : ℤ × ℤ) (w : List Bool) :
    ∃ t, pathOfWord s w = s :: t := by
  cases w <;> simp [pathOfWord]

theorem head?_pathOfWord (s : ℤ × ℤ) (w : List Bool) : (pathOfWord s w).head? = some s := by
  obtain ⟨t, ht⟩ := pathOfWord_cons_exists s w
  simp [ht]

theorem isLatticePath_pathOfWord : ∀ (w : List Bool) (s : ℤ × ℤ), IsLatticePath (pathOfWord s w)
  | [], s => by simp [pathOfWord, IsLatticePath]
  | b :: w, s => by
    have ih := isLatticePath_pathOfWord w (moveBy b s)
    obtain ⟨t, ht⟩ := pathOfWord_cons_exists (moveBy b s) w
    rw [pathOfWord, ht]
    rw [ht] at ih
    unfold IsLatticePath at ih ⊢
    rw [List.isChain_cons_cons]
    refine ⟨?_, ih⟩
    cases b <;> simp [LatticeStep, moveBy]

theorem count_true_add_count_false : ∀ w : List Bool,
    w.count true + w.count false = w.length
  | [] => rfl
  | b :: w => by
    have := count_true_add_count_false w
    cases b <;> simp <;> omega

theorem getLast?_pathOfWord : ∀ (w : List Bool) (s : ℤ × ℤ),
    (pathOfWord s w).getLast? =
      some (s.1 + (w.count true : ℤ), s.2 + (w.count false : ℤ))
  | [], s => by simp [pathOfWord]
  | b :: w, s => by
    have ih := getLast?_pathOfWord w (moveBy b s)
    obtain ⟨t, ht⟩ := pathOfWord_cons_exists (moveBy b s) w
    have key : (pathOfWord s (b :: w)).getLast? = (pathOfWord (moveBy b s) w).getLast? := by
      rw [pathOfWord, ht, List.getLast?_cons_cons]
    rw [key, ih]
    cases b <;> simp [moveBy] <;> ring

theorem pathOfWord_injective (s : ℤ × ℤ) : Function.Injective (pathOfWord s) := by
  intro w
  induction w generalizing s with
  | nil =>
    intro w' h
    cases w' with
    | nil => rfl
    | cons b w' =>
      obtain ⟨t, ht⟩ := pathOfWord_cons_exists (moveBy b s) w'
      simp [pathOfWord, ht] at h
  | cons b w ih =>
    intro w' h
    cases w' with
    | nil =>
      obtain ⟨t, ht⟩ := pathOfWord_cons_exists (moveBy b s) w
      simp [pathOfWord, ht] at h
    | cons b' w' =>
      simp only [pathOfWord, List.cons.injEq, true_and] at h
      have hb : b = b' := by
        have := congrArg List.head? h
        rw [head?_pathOfWord, head?_pathOfWord] at this
        cases b <;> cases b' <;> simp [moveBy] at this ⊢
      subst hb
      rw [ih _ h]

theorem exists_word_of_isLatticePath : ∀ (l : List (ℤ × ℤ)) (s : ℤ × ℤ),
    IsLatticePath l → l.head? = some s → ∃ w, pathOfWord s w = l
  | [], s, _, h => by simp at h
  | [x], s, _, h => by
    simp at h; subst h; exact ⟨[], rfl⟩
  | x :: y :: t, s, hc, h => by
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    unfold IsLatticePath at hc
    rw [List.isChain_cons_cons] at hc
    obtain ⟨w, hw⟩ := exists_word_of_isLatticePath (y :: t) y hc.2 rfl
    rcases hc.1 with h1 | h1
    · have hy : y = moveBy true x := by simpa [moveBy] using h1
      subst hy
      exact ⟨true :: w, by simp [pathOfWord, hw]⟩
    · have hy : y = moveBy false x := by simpa [moveBy] using h1
      subst hy
      exact ⟨false :: w, by simp [pathOfWord, hw]⟩

/-- The bit strings (`H`/`V` words) of length `N` with exactly `a` letters `H`. -/
def hvWords (N a : ℕ) : Finset (List Bool) :=
  ((univ : Finset (Fin N → Bool)).filter (fun f => #{i | f i = true} = a)).image List.ofFn

theorem count_ofFn_true : ∀ (N : ℕ) (f : Fin N → Bool),
    (List.ofFn f).count true = #{i | f i = true}
  | 0, f => by simp
  | N + 1, f => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_true N, Finset.card_filter,
      Finset.card_filter, Fin.sum_univ_succ]
    cases f 0 <;> simp [add_comm]

theorem mem_hvWords (N a : ℕ) (w : List Bool) :
    w ∈ hvWords N a ↔ w.length = N ∧ w.count true = a := by
  constructor
  · intro h
    simp only [hvWords, mem_image, mem_filter, mem_univ, true_and] at h
    obtain ⟨f, hf, rfl⟩ := h
    exact ⟨by simp, by rw [count_ofFn_true]; exact hf⟩
  · rintro ⟨hl, hc⟩
    subst hl
    simp only [hvWords, mem_image, mem_filter, mem_univ, true_and]
    exact ⟨w.get, by rw [← count_ofFn_true, List.ofFn_get]; exact hc, List.ofFn_get w⟩

theorem card_hvWords (N a : ℕ) : #(hvWords N a) = N.choose a := by
  rw [hvWords, Finset.card_image_of_injective _ List.ofFn_injective]
  exact card_bitStrings_with_ones N a

theorem latticePaths_eq_image (m n : ℤ) (a b : ℕ) :
    latticePaths (m, n) (m + a, n + b) = pathOfWord (m, n) '' (hvWords (a + b) a : Set _) := by
  ext l
  simp only [latticePaths, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, mem_hvWords]
  constructor
  · rintro ⟨hc, hh, hl⟩
    obtain ⟨w, rfl⟩ := exists_word_of_isLatticePath l _ hc hh
    rw [getLast?_pathOfWord] at hl
    simp only [Option.some.injEq, Prod.mk.injEq, add_right_inj, Nat.cast_inj] at hl
    refine ⟨w, ⟨?_, hl.1⟩, rfl⟩
    have := count_true_add_count_false w
    omega
  · rintro ⟨w, ⟨hl, hc⟩, rfl⟩
    refine ⟨isLatticePath_pathOfWord w _, head?_pathOfWord _ _, ?_⟩
    rw [getLast?_pathOfWord]
    have := count_true_add_count_false w
    have hf : w.count false = b := by omega
    simp [hc, hf]

/-- CO-012. The number of lattice paths from `(m,n)` to `(m + a, n + b)` is `C(a + b, a)`
(here `a = p - m` and `b = q - n` are the numbers of horizontal and vertical steps). -/
@[kb "kellertrotter2017" "Example 2.27, p. 51"]
theorem ncard_latticePaths (m n : ℤ) (a b : ℕ) :
    (latticePaths (m, n) (m + a, n + b)).ncard = (a + b).choose a := by
  rw [latticePaths_eq_image, Set.ncard_image_of_injective _ (pathOfWord_injective _),
    Set.ncard_coe_finset, card_hvWords]

/-- CO-012, in the book's form: the number of lattice paths from `(m,n)` to `(p,q)` (with
`m ≤ p` and `n ≤ q`) is `C((p-m)+(q-n), p-m)`. -/
@[kb "kellertrotter2017" "Example 2.27, p. 51"]
theorem ncard_latticePaths' (m n p q : ℤ) (hmp : m ≤ p) (hnq : n ≤ q) :
    (latticePaths (m, n) (p, q)).ncard = (((p - m) + (q - n)).toNat).choose (p - m).toNat := by
  have h1 : p = m + ((p - m).toNat : ℕ) := by omega
  have h2 : q = n + ((q - n).toNat : ℕ) := by omega
  have := ncard_latticePaths m n (p - m).toNat (q - n).toNat
  rw [← h1, ← h2] at this
  rw [this]
  congr 1
  omega

end LatticePaths

end UndergradKB.Combinatorics
