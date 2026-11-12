import UndergradKB.RepresentationTheory.Roots
import UndergradKB.Common.Attr

/-! # All roots of type `A_n` (Etingof et al., Example 5.19)

`Roots.lean` shows that the interval vectors `intervalRoot n a b` (`a < b ≤ n`, which are the vectors
`e_a - e_b` in simple-root coordinates) are roots of the path graph on `n` vertices.  Here we prove the
converse: every root is `± intervalRoot n a b`.

The proof uses the identity `B(x, x) = Σ_{a=0}^{n} (y_{a+1} - y_a)²` for the extended sequence
`y = (0, x_0, …, x_{n-1}, 0)`.  The form equals `2` exactly when two of the `n + 1` consecutive differences
are `±1` and the others vanish; since the differences sum to zero these two have opposite signs, so the
sequence is `± ` the indicator of an interval.

* `isRoot_pathGraph_iff`: the roots of `A_n` are exactly the vectors `± intervalRoot n a b`.
* `ncard_roots_pathGraph`: there are `(n + 1) n = N (N - 1)` roots (`N = n + 1`).
* `ncard_positiveRoots_pathGraph`: there are `N (N - 1) / 2` positive roots.
* The counts for `D_N`, `E_6`, `E_7`, `E_8` are not formalized.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Finset

/-- The Cartan matrix entries of the path graph as a function of the natural-number indices. -/
def cartanA (a b : ℕ) : ℤ := if a = b then 2 else if a + 1 = b ∨ b + 1 = a then -1 else 0

theorem cartanMatrix_pathGraph_apply {n : ℕ} (i j : Fin n) :
    cartanMatrix (SimpleGraph.pathGraph n) i j = cartanA i.val j.val := by
  rw [cartanMatrix_apply]
  by_cases h : i = j
  · subst h; simp [cartanA]
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [cartanA, h, h', SimpleGraph.pathGraph_adj, ite_false]
    split_ifs <;> simp

/-- The quadratic form truncated to the first `m` indices. -/
def quadA (z : ℕ → ℤ) (m : ℕ) : ℤ := ∑ a ∈ range m, ∑ b ∈ range m, z a * cartanA a b * z b

theorem quadA_one (z : ℕ → ℤ) : quadA z 1 = 2 * z 0 ^ 2 := by
  simp [quadA, cartanA]; ring

theorem quadA_succ (z : ℕ → ℤ) (m : ℕ) :
    quadA z (m + 2) = quadA z (m + 1) + 2 * z (m + 1) ^ 2 - 2 * z m * z (m + 1) := by
  have hcol : ∑ a ∈ range (m + 1), z a * cartanA a (m + 1) * z (m + 1) = - (z m * z (m + 1)) := by
    rw [Finset.sum_eq_single m]
    · simp [cartanA]
    · intro a ha hne
      simp only [mem_range] at ha
      have h1 : ¬ (a = m + 1) := by omega
      have h2 : ¬ (a + 1 = m + 1 ∨ m + 1 + 1 = a) := by omega
      simp only [cartanA, h1, h2, ite_false, mul_zero, zero_mul]
    · intro h; simp at h
  have hrow : ∑ b ∈ range (m + 1), z (m + 1) * cartanA (m + 1) b * z b = - (z (m + 1) * z m) := by
    rw [Finset.sum_eq_single m]
    · simp [cartanA]
    · intro b hb hne
      simp only [mem_range] at hb
      have h1 : ¬ (m + 1 = b) := by omega
      have h2 : ¬ (m + 1 + 1 = b ∨ b + 1 = m + 1) := by omega
      simp only [cartanA, h1, h2, ite_false, mul_zero, zero_mul]
    · intro h; simp at h
  have hdiag : cartanA (m + 1) (m + 1) = 2 := by simp [cartanA]
  unfold quadA
  simp only [Finset.sum_range_succ (n := m + 1), Finset.sum_add_distrib, hcol, hrow, hdiag]
  ring

theorem quadA_closed (z : ℕ → ℤ) (m : ℕ) :
    quadA z (m + 1) = z 0 ^ 2 + ∑ a ∈ range m, (z (a + 1) - z a) ^ 2 + z m ^ 2 := by
  induction m with
  | zero => rw [quadA_one]; simp; ring
  | succ m ih =>
    rw [quadA_succ, ih, Finset.sum_range_succ]
    ring

/-- Telescoping differences: `d 0 = z 0` and `d (a + 1) = z (a + 1) - z a`. -/
def diffSeq (z : ℕ → ℤ) : ℕ → ℤ
  | 0 => z 0
  | a + 1 => z (a + 1) - z a

theorem sum_diffSeq (z : ℕ → ℤ) (k : ℕ) : ∑ a ∈ range (k + 1), diffSeq z a = z k := by
  induction k with
  | zero => simp [diffSeq]
  | succ k ih => rw [Finset.sum_range_succ, ih]; simp [diffSeq]

theorem quadA_eq_sum_sq (z : ℕ → ℤ) (n : ℕ) (hz : z n = 0) :
    quadA z n = ∑ a ∈ range (n + 1), diffSeq z a ^ 2 := by
  rw [Finset.sum_range_succ' (fun a => diffSeq z a ^ 2)]
  simp only [diffSeq]
  cases n with
  | zero => simp [quadA, hz]
  | succ m =>
    rw [quadA_closed, Finset.sum_range_succ, hz]
    ring

/-- The sequence `0, x_0, …, x_{n-1}, 0, 0, …` (with `x_i` at index `i`, extended by zero). -/
def extSeq {n : ℕ} (x : Fin n → ℤ) (i : ℕ) : ℤ := if h : i < n then x ⟨i, h⟩ else 0

theorem form_pathGraph_eq {n : ℕ} (x : Fin n → ℤ) :
    form (SimpleGraph.pathGraph n) x x = quadA (extSeq x) n := by
  rw [form_eq_sum]
  have h1 : ∀ i j : Fin n, x i * cartanMatrix (SimpleGraph.pathGraph n) i j * x j =
      extSeq x i.val * cartanA i.val j.val * extSeq x j.val := by
    intro i j
    rw [cartanMatrix_pathGraph_apply]
    simp [extSeq]
  simp only [h1]
  unfold quadA
  rw [← Fin.sum_univ_eq_sum_range
    (fun a => ∑ b ∈ range n, extSeq x a * cartanA a b * extSeq x b) n]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => extSeq x a.val * cartanA a.val b * extSeq x b) n

theorem extSeq_self {n : ℕ} (x : Fin n → ℤ) : extSeq x n = 0 := by simp [extSeq]

theorem form_pathGraph_eq_sum_sq {n : ℕ} (x : Fin n → ℤ) :
    form (SimpleGraph.pathGraph n) x x = ∑ a ∈ range (n + 1), diffSeq (extSeq x) a ^ 2 := by
  rw [form_pathGraph_eq, quadA_eq_sum_sq _ _ (extSeq_self x)]

theorem sq_sum_one (d : ℕ → ℤ) (N : ℕ) (h : ∑ a ∈ range N, d a ^ 2 = 1) :
    ∃ p < N, (d p = 1 ∨ d p = -1) ∧ ∀ a < N, a ≠ p → d a = 0 := by
  induction N with
  | zero => simp at h
  | succ N ih =>
    rw [Finset.sum_range_succ] at h
    have hS : 0 ≤ ∑ a ∈ range N, d a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    have hd : 0 ≤ d N ^ 2 := sq_nonneg _
    have hb1 : d N ≤ 1 := by nlinarith
    have hb2 : -1 ≤ d N := by nlinarith
    have hc : d N = -1 ∨ d N = 0 ∨ d N = 1 := by omega
    rcases hc with hc | hc | hc
    · refine ⟨N, Nat.lt_succ_self _, Or.inr hc, fun a ha hne => ?_⟩
      have h0 : ∑ a ∈ range N, d a ^ 2 = 0 := by rw [hc] at h; linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (d a))).1 h0 a
        (Finset.mem_range.2 (by omega))
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    · rw [hc] at h
      obtain ⟨p, hp, hdp, hrest⟩ := ih (by linarith)
      refine ⟨p, by omega, hdp, fun a ha hne => ?_⟩
      by_cases haN : a = N
      · rw [haN, hc]
      · exact hrest a (by omega) hne
    · refine ⟨N, Nat.lt_succ_self _, Or.inl hc, fun a ha hne => ?_⟩
      have h0 : ∑ a ∈ range N, d a ^ 2 = 0 := by rw [hc] at h; linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (d a))).1 h0 a
        (Finset.mem_range.2 (by omega))
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this

theorem sq_sum_two (d : ℕ → ℤ) (N : ℕ) (h : ∑ a ∈ range N, d a ^ 2 = 2) :
    ∃ p q, p < q ∧ q < N ∧ (d p = 1 ∨ d p = -1) ∧ (d q = 1 ∨ d q = -1) ∧
      ∀ a < N, a ≠ p → a ≠ q → d a = 0 := by
  induction N with
  | zero => simp at h
  | succ N ih =>
    rw [Finset.sum_range_succ] at h
    have hS : 0 ≤ ∑ a ∈ range N, d a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    have hd : 0 ≤ d N ^ 2 := sq_nonneg _
    have hb1 : d N ≤ 1 := by nlinarith
    have hb2 : -1 ≤ d N := by nlinarith
    have hc : d N = -1 ∨ d N = 0 ∨ d N = 1 := by omega
    rcases hc with hc | hc | hc
    · rw [hc] at h
      obtain ⟨p, hp, hdp, hrest⟩ := sq_sum_one d N (by linarith)
      refine ⟨p, N, hp, Nat.lt_succ_self _, hdp, Or.inr hc, fun a ha h1 h2 => ?_⟩
      exact hrest a (by omega) h1
    · rw [hc] at h
      obtain ⟨p, q, hpq, hq, hdp, hdq, hrest⟩ := ih (by linarith)
      refine ⟨p, q, hpq, by omega, hdp, hdq, fun a ha h1 h2 => ?_⟩
      by_cases haN : a = N
      · rw [haN, hc]
      · exact hrest a (by omega) h1 h2
    · rw [hc] at h
      obtain ⟨p, hp, hdp, hrest⟩ := sq_sum_one d N (by linarith)
      refine ⟨p, N, hp, Nat.lt_succ_self _, hdp, Or.inl hc, fun a ha h1 h2 => ?_⟩
      exact hrest a (by omega) h1

/-- Partial sums of a sequence supported at two indices. -/
theorem partial_sum_two (d : ℕ → ℤ) (p q N : ℕ) (hrest : ∀ a < N, a ≠ p → a ≠ q → d a = 0)
    (hpq : p < q) (k : ℕ) (hk : k ≤ N) :
    ∑ a ∈ range k, d a = (if p < k then d p else 0) + (if q < k then d q else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    by_cases h1 : k = p
    · subst h1
      have : ¬ (q < k) := by omega
      have : ¬ (q < k + 1) := by omega
      simp [*]
    · by_cases h2 : k = q
      · subst h2
        have : p < k + 1 := by omega
        have : p < k := by omega
        simp [*]
      · rw [hrest k (by omega) h1 h2]
        have e1 : (p < k + 1 ↔ p < k) := by omega
        have e2 : (q < k + 1 ↔ q < k) := by omega
        simp [e1, e2]

/-- **Example 5.19 (completeness).** The roots of the path graph on `n` vertices (type `A_n`, `N = n + 1`)
are exactly the vectors `± (α_a + ⋯ + α_{b-1})` with `0 ≤ a < b ≤ n`, i.e. the vectors `± (e_a - e_b)`. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem isRoot_pathGraph_iff (n : ℕ) (x : Fin n → ℤ) :
    IsRoot (SimpleGraph.pathGraph n) x ↔
      ∃ a b : ℕ, a < b ∧ b ≤ n ∧ (x = intervalRoot n a b ∨ x = -intervalRoot n a b) := by
  constructor
  · intro hx
    have h2 : ∑ a ∈ range (n + 1), diffSeq (extSeq x) a ^ 2 = 2 := by
      rw [← form_pathGraph_eq_sum_sq]; exact hx
    obtain ⟨p, q, hpq, hq, hdp, hdq, hrest⟩ := sq_sum_two _ _ h2
    have hsum : ∑ a ∈ range (n + 1), diffSeq (extSeq x) a = 0 := by
      rw [sum_diffSeq, extSeq_self]
    rw [partial_sum_two _ p q (n + 1) hrest hpq (n + 1) le_rfl] at hsum
    simp only [hpq.trans hq, hq, ite_true] at hsum
    have hneg : diffSeq (extSeq x) q = - diffSeq (extSeq x) p := by omega
    have hcoord : ∀ j : Fin n, x j = if p ≤ j.val ∧ j.val < q then diffSeq (extSeq x) p else 0 := by
      intro j
      have h1 := sum_diffSeq (extSeq x) j.val
      rw [partial_sum_two _ p q (n + 1) hrest hpq (j.val + 1) (by omega), hneg] at h1
      have e : extSeq x j.val = x j := by simp [extSeq]
      rw [e] at h1
      rw [← h1]
      by_cases a1 : p ≤ j.val <;> by_cases a2 : q ≤ j.val <;>
        simp [a1, a2]; omega
    refine ⟨p, q, hpq, by omega, ?_⟩
    rcases hdp with hdp | hdp
    · left
      funext j
      rw [hcoord j, hdp]; rfl
    · right
      funext j
      rw [hcoord j, hdp]
      simp only [intervalRoot, Pi.neg_apply]
      split_ifs <;> simp
  · rintro ⟨a, b, hab, hb, rfl | rfl⟩
    · exact isRoot_intervalRoot n a b hab hb
    · unfold IsRoot
      rw [form_neg_left, form_neg_right, neg_neg]
      exact isRoot_intervalRoot n a b hab hb

/-- The index pairs `(b, a)` with `a < b ≤ n`. -/
def intervalIndex (n : ℕ) : Finset (Σ _ : ℕ, ℕ) := (range (n + 1)).sigma (fun b => range b)

theorem card_intervalIndex (n : ℕ) : (intervalIndex n).card = (n + 1) * n / 2 := by
  simp only [intervalIndex, Finset.card_sigma, Finset.card_range]
  exact Finset.sum_range_id (n + 1)

theorem mem_intervalIndex {n : ℕ} (p : Σ _ : ℕ, ℕ) : p ∈ intervalIndex n ↔ p.2 < p.1 ∧ p.1 ≤ n := by
  simp only [intervalIndex, Finset.mem_sigma, Finset.mem_range]
  omega

theorem intervalRoot_injOn (n : ℕ) :
    Set.InjOn (fun p : Σ _ : ℕ, ℕ => intervalRoot n p.2 p.1) (intervalIndex n : Set (Σ _ : ℕ, ℕ)) := by
  rintro ⟨b, a⟩ hp ⟨b', a'⟩ hp' h
  have h1 := (mem_intervalIndex _).1 hp
  have h2 := (mem_intervalIndex _).1 hp'
  obtain ⟨rfl, rfl⟩ := intervalRoot_injective n a b a' b' h1.1 h1.2 h2.1 h2.2 h
  rfl

theorem intervalRoot_apply_left (n a b : ℕ) (hab : a < b) (hb : b ≤ n) :
    intervalRoot n a b ⟨a, by omega⟩ = 1 := by
  simp [intervalRoot, hab]

theorem positiveRoots_pathGraph_eq (n : ℕ) :
    {x | IsPositiveRoot (SimpleGraph.pathGraph n) x} =
      ↑((intervalIndex n).image fun p => intervalRoot n p.2 p.1) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, IsPositiveRoot,
    isRoot_pathGraph_iff]
  constructor
  · rintro ⟨⟨a, b, hab, hb, rfl | rfl⟩, hnn⟩
    · exact ⟨⟨b, a⟩, (mem_intervalIndex _).2 ⟨hab, hb⟩, rfl⟩
    · exfalso
      have := hnn ⟨a, by omega⟩
      simp only [Pi.neg_apply, intervalRoot_apply_left n a b hab hb] at this
      omega
  · rintro ⟨⟨b, a⟩, hp, rfl⟩
    have h := (mem_intervalIndex _).1 hp
    exact ⟨⟨a, b, h.1, h.2, Or.inl rfl⟩, intervalRoot_nonneg n a b⟩

/-- **Example 5.19 (count).** The path graph on `n` vertices (type `A_n`, `N = n + 1`) has exactly
`N (N - 1) / 2` positive roots. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem ncard_positiveRoots_pathGraph (n : ℕ) :
    {x | IsPositiveRoot (SimpleGraph.pathGraph n) x}.ncard = (n + 1) * n / 2 := by
  rw [positiveRoots_pathGraph_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (intervalRoot_injOn n), card_intervalIndex]

/-- **Example 5.19 (count).** The path graph on `n` vertices (type `A_n`, `N = n + 1`) has exactly
`N (N - 1)` roots. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem ncard_roots_pathGraph (n : ℕ) :
    {x | IsRoot (SimpleGraph.pathGraph n) x}.ncard = (n + 1) * n := by
  classical
  let f : (Σ _ : ℕ, ℕ) → (Fin n → ℤ) := fun p => intervalRoot n p.2 p.1
  have hset : {x | IsRoot (SimpleGraph.pathGraph n) x} =
      ↑((intervalIndex n).image f ∪ (intervalIndex n).image fun p => -f p) := by
    ext x
    simp only [Set.mem_ofPred_eq, isRoot_pathGraph_iff, Finset.coe_union, Finset.coe_image,
      Set.mem_union, Set.mem_image, Finset.mem_coe, f]
    constructor
    · rintro ⟨a, b, hab, hb, rfl | rfl⟩
      · exact Or.inl ⟨⟨b, a⟩, (mem_intervalIndex _).2 ⟨hab, hb⟩, rfl⟩
      · exact Or.inr ⟨⟨b, a⟩, (mem_intervalIndex _).2 ⟨hab, hb⟩, rfl⟩
    · rintro (⟨⟨b, a⟩, hp, rfl⟩ | ⟨⟨b, a⟩, hp, rfl⟩)
      · have h := (mem_intervalIndex _).1 hp
        exact ⟨a, b, h.1, h.2, Or.inl rfl⟩
      · have h := (mem_intervalIndex _).1 hp
        exact ⟨a, b, h.1, h.2, Or.inr rfl⟩
  have hdisj : Disjoint ((intervalIndex n).image f) ((intervalIndex n).image fun p => -f p) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨⟨b, a⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨⟨b', a'⟩, hp', h⟩ := Finset.mem_image.1 hx'
    have h1 := (mem_intervalIndex _).1 hp
    have h2 := (mem_intervalIndex _).1 hp'
    have := congrFun h ⟨a, by simp only at h1; omega⟩
    have h3 := intervalRoot_nonneg n a' b' ⟨a, by simp only at h1; omega⟩
    simp only [f, Pi.neg_apply] at this
    have h4 := intervalRoot_apply_left n a b h1.1 h1.2
    omega
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => -f p) (intervalIndex n : Set (Σ _ : ℕ, ℕ)) := by
    intro p hp q hq h
    exact intervalRoot_injOn n hp hq (neg_injective h)
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn (intervalRoot_injOn n), Finset.card_image_of_injOn hinj,
    card_intervalIndex]
  have : (n + 1) * n % 2 = 0 := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
  omega

end UndergradKB.RepresentationTheory.Roots
