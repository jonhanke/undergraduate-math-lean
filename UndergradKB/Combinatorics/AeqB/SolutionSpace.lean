import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import UndergradKB.Combinatorics.AeqB.Gosper
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.SequenceRing

/-!
# Uniqueness of dissimilar representations (Petkovsek–Wilf–Zeilberger, "A = B", §8.9)

Proposition 8.9.1: up to order, the representation of a sum of hypergeometric terms as a sum of
pairwise dissimilar hypergeometric terms is unique.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

theorem isSimilar_neg' (x : ℕ → K) : IsSimilar (fun n => -x n) x :=
  ⟨-1, 1, by simp, one_ne_zero, Eventually.of_forall fun n => by simp⟩

theorem isSimilar_of_eventually_eq {x y : ℕ → K} (h : ∀ᶠ n : ℕ in atTop, x n = y n) :
    IsSimilar x y :=
  ⟨1, 1, one_ne_zero, one_ne_zero, h.mono fun n hn => by simp [hn]⟩

section Update

variable {ι : Type*} [DecidableEq ι]

theorem update_isHypergeometric (s : Finset ι) (u : ι → ℕ → K) (i : ι) (w : ℕ → K)
    (hu : ∀ x ∈ s, IsHypergeometric (u x)) (hw : IsHypergeometric w) :
    ∀ x ∈ s, IsHypergeometric (Function.update u i w x) := by
  intro x hx
  by_cases hxi : x = i
  · subst hxi; rw [Function.update_self]; exact hw
  · rw [Function.update_of_ne hxi]; exact hu x hx

theorem update_dissimilar (s : Finset ι) (u : ι → ℕ → K) (i : ι) (w : ℕ → K) (hi : i ∈ s)
    (hd : ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → ¬ IsSimilar (u x) (u x')) (hw : IsSimilar w (u i)) :
    ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → ¬ IsSimilar (Function.update u i w x) (Function.update u i w x') := by
  intro x hx x' hx' hne
  by_cases hxi : x = i
  · subst hxi
    rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
    exact fun h => hd x hx x' hx' hne (hw.symm.trans h)
  · by_cases hxi' : x' = i
    · subst hxi'
      rw [Function.update_self, Function.update_of_ne hxi]
      exact fun h => hd x hx x' hx' hne (h.trans hw)
    · rw [Function.update_of_ne hxi, Function.update_of_ne hxi']
      exact hd x hx x' hx' hne

theorem sum_update_apply (s : Finset ι) (u : ι → ℕ → K) (i : ι) (w : ℕ → K) (hi : i ∈ s) (n : ℕ) :
    ∑ x ∈ s, Function.update u i w x n = w n + ∑ x ∈ s.erase i, u x n := by
  rw [← Finset.add_sum_erase s _ hi, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]

end Update

theorem dissimilar_repr_unique_aux {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] :
    ∀ (N : ℕ) (s : Finset ι) (t : Finset κ) (u : ι → ℕ → K) (v : κ → ℕ → K),
      s.card + t.card = N →
      (∀ i ∈ s, IsHypergeometric (u i)) → (∀ j ∈ t, IsHypergeometric (v j)) →
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ IsSimilar (u i) (u i')) →
      (∀ j ∈ t, ∀ j' ∈ t, j ≠ j' → ¬ IsSimilar (v j) (v j')) →
      (∀ᶠ n : ℕ in atTop, ∑ i ∈ s, u i n = ∑ j ∈ t, v j n) →
      s.card = t.card ∧ ∀ i ∈ s, ∃ j ∈ t, ∀ᶠ n : ℕ in atTop, u i n = v j n := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s t u v hN hu hv hdu hdv hsum
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · simp
    · exfalso
      have h0 : ∀ᶠ n : ℕ in atTop, ∑ j ∈ t, v j n = 0 :=
        hsum.mono fun n hn => by simpa using hn.symm
      obtain ⟨j, hj, j', hj', hne, hsim⟩ := exists_similar_of_sum_eq_zero t ht v hv h0
      exact hdv j hj j' hj' hne hsim
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exfalso
    have h0 : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, u i n = 0 := hsum.mono fun n hn => by simpa using hn
    obtain ⟨i, hi, i', hi', hne, hsim⟩ := exists_similar_of_sum_eq_zero s hs u hu h0
    exact hdu i hi i' hi' hne hsim
  -- both nonempty: some `u i` is similar to some `v j`
  obtain ⟨i, hi, j, hj, hsim⟩ : ∃ i ∈ s, ∃ j ∈ t, IsSimilar (u i) (v j) := by
    let F : ι ⊕ κ → ℕ → K := Sum.elim u (fun j n => - v j n)
    have hF : ∀ x ∈ s.disjSum t, IsHypergeometric (F x) := by
      intro x hx
      rcases Finset.mem_disjSum.1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact hu i hi
      · exact (isSimilar_neg' (v j)).isHypergeometric (hv j hj)
    have hFsum : ∀ᶠ n : ℕ in atTop, ∑ x ∈ s.disjSum t, F x n = 0 := by
      filter_upwards [hsum] with n hn
      simp only [F, Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
      rw [hn]; ring
    obtain ⟨i0, hi0⟩ := hs
    obtain ⟨x, hx, y, hy, hxy, hsim⟩ := exists_similar_of_sum_eq_zero (s.disjSum t)
      ⟨Sum.inl i0, Finset.inl_mem_disjSum.2 hi0⟩ F hF hFsum
    rcases x with i | j <;> rcases y with i' | j'
    · exact absurd hsim (hdu i (Finset.inl_mem_disjSum.1 hx) i' (Finset.inl_mem_disjSum.1 hy)
        (fun h => hxy (by rw [h])))
    · exact ⟨i, Finset.inl_mem_disjSum.1 hx, j', Finset.inr_mem_disjSum.1 hy,
        hsim.trans (isSimilar_neg' (v j'))⟩
    · exact ⟨i', Finset.inl_mem_disjSum.1 hy, j, Finset.inr_mem_disjSum.1 hx,
        ((isSimilar_neg' (v j)).symm.trans hsim).symm⟩
    · exact absurd ((isSimilar_neg' (v j)).symm.trans (hsim.trans (isSimilar_neg' (v j'))))
        (hdv j (Finset.inr_mem_disjSum.1 hx) j' (Finset.inr_mem_disjSum.1 hy)
          (fun h => hxy (by rw [h])))
  have hscard : 0 < s.card := Finset.card_pos.2 ⟨i, hi⟩
  have htcard : 0 < t.card := Finset.card_pos.2 ⟨j, hj⟩
  have hse : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  have hte : (t.erase j).card = t.card - 1 := Finset.card_erase_of_mem hj
  have ea : ∀ n : ℕ, u i n + ∑ x ∈ s.erase i, u x n = ∑ x ∈ s, u x n :=
    fun n => Finset.add_sum_erase s (fun x => u x n) hi
  have eb : ∀ n : ℕ, v j n + ∑ x ∈ t.erase j, v x n = ∑ x ∈ t, v x n :=
    fun n => Finset.add_sum_erase t (fun x => v x n) hj
  by_cases hzero : ∀ᶠ n : ℕ in atTop, u i n = v j n
  · have hsum' : ∀ᶠ n : ℕ in atTop, ∑ x ∈ s.erase i, u x n = ∑ x ∈ t.erase j, v x n := by
      filter_upwards [hsum, hzero] with n h1 h2
      linear_combination ea n - eb n + h1 - h2
    obtain ⟨hcard, hmap⟩ := ih ((s.erase i).card + (t.erase j).card) (by omega) (s.erase i)
      (t.erase j) u v rfl (fun x hx => hu x (Finset.mem_of_mem_erase hx))
      (fun x hx => hv x (Finset.mem_of_mem_erase hx))
      (fun x hx x' hx' => hdu x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx'))
      (fun x hx x' hx' => hdv x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx'))
      hsum'
    refine ⟨by omega, fun i' hi' => ?_⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨j, hj, hzero⟩
    · obtain ⟨j', hj', e⟩ := hmap i' (Finset.mem_erase.2 ⟨hii, hi'⟩)
      exact ⟨j', Finset.mem_of_mem_erase hj', e⟩
  · exfalso
    obtain ⟨p, q, hp, hq, hpq⟩ := id hsim
    have hpq0 : p - q ≠ 0 := by
      intro h0
      apply hzero
      filter_upwards [hpq, eventually_eval_ne_zero hq] with n e hq'
      have h1 : p.eval (n : K) = q.eval (n : K) := by
        have := congrArg (eval (n : K)) h0
        simpa [sub_eq_zero] using this
      exact mul_left_cancel₀ hq' (by rw [e, h1])
    have hsimh : IsSimilar (fun n => u i n - v j n) (v j) :=
      ⟨p - q, q, hpq0, hq, hpq.mono fun n e => by
        simp only [eval_sub]; linear_combination e⟩
    have hhyp : IsHypergeometric (fun n => u i n - v j n) := hsimh.isHypergeometric (hv j hj)
    have hsimhu : IsSimilar (fun n => u i n - v j n) (u i) := hsimh.trans hsim.symm
    have hwsim : IsSimilar (fun n => -(u i n - v j n)) (v j) := (isSimilar_neg' _).trans hsimh
    have hwhyp : IsHypergeometric (fun n => -(u i n - v j n)) :=
      (isSimilar_neg' _).isHypergeometric hhyp
    -- first induction application: replace `u i` by `u i - v j`
    have hA := ih (s.card + (t.erase j).card) (by omega) s (t.erase j)
      (Function.update u i (fun n => u i n - v j n)) v rfl
      (update_isHypergeometric s u i _ hu hhyp)
      (fun x hx => hv x (Finset.mem_of_mem_erase hx))
      (update_dissimilar s u i _ hi hdu hsimhu)
      (fun x hx x' hx' => hdv x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx'))
      (by
        filter_upwards [hsum] with n h1
        rw [sum_update_apply s u i _ hi]
        linear_combination ea n - eb n + h1)
    have hB := ih ((s.erase i).card + t.card) (by omega) (s.erase i) t u
      (Function.update v j (fun n => -(u i n - v j n))) rfl
      (fun x hx => hu x (Finset.mem_of_mem_erase hx))
      (update_isHypergeometric t v j _ hv hwhyp)
      (fun x hx x' hx' => hdu x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx'))
      (update_dissimilar t v j _ hj hdv hwsim)
      (by
        filter_upwards [hsum] with n h1
        rw [sum_update_apply t v j _ hj]
        linear_combination ea n - eb n + h1)
    omega

/-- CO-503. Proposition 8.9.1: two representations of the same sequence (equality for large `n`)
as sums of pairwise dissimilar hypergeometric terms `∑_{i ∈ s} u_i = ∑_{j ∈ t} v_j` have the same
number of terms, and every `u_i` equals (for large `n`) some `v_j`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.9.1, p. 171"]
theorem dissimilar_repr_unique {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι)
    (t : Finset κ) (u : ι → ℕ → K) (v : κ → ℕ → K)
    (hu : ∀ i ∈ s, IsHypergeometric (u i)) (hv : ∀ j ∈ t, IsHypergeometric (v j))
    (hdu : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ IsSimilar (u i) (u i'))
    (hdv : ∀ j ∈ t, ∀ j' ∈ t, j ≠ j' → ¬ IsSimilar (v j) (v j'))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, u i n = ∑ j ∈ t, v j n) :
    s.card = t.card ∧ ∀ i ∈ s, ∃ j ∈ t, ∀ᶠ n : ℕ in atTop, u i n = v j n :=
  dissimilar_repr_unique_aux _ s t u v rfl hu hv hdu hdv hsum

/-- CO-503, book shape: for `a_1, …, a_k` and `b_1, …, b_m` pairwise dissimilar hypergeometric
terms with `∑ a_i = ∑ b_j` (for large `n`) we have `k = m` and, after reordering, `a_i = b_{σ i}`
(for large `n`). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.9.1, p. 171"]
theorem dissimilar_repr_unique_fin {k m : ℕ} (a : Fin k → ℕ → K) (b : Fin m → ℕ → K)
    (ha : ∀ i, IsHypergeometric (a i)) (hb : ∀ j, IsHypergeometric (b j))
    (hda : ∀ i i', i ≠ i' → ¬ IsSimilar (a i) (a i'))
    (hdb : ∀ j j', j ≠ j' → ¬ IsSimilar (b j) (b j'))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i, a i n = ∑ j, b j n) :
    k = m ∧ ∃ σ : Fin k ≃ Fin m, ∀ i, ∀ᶠ n : ℕ in atTop, a i n = b (σ i) n := by
  obtain ⟨hcard, hmap⟩ := dissimilar_repr_unique Finset.univ Finset.univ a b (fun i _ => ha i)
    (fun j _ => hb j) (fun i _ i' _ => hda i i') (fun j _ j' _ => hdb j j') hsum
  have hkm : k = m := by simpa using hcard
  subst hkm
  choose φ _ hφ using fun i => hmap i (Finset.mem_univ i)
  have hinj : Function.Injective φ := by
    intro i i' h
    by_contra hne
    apply hda i i' hne
    exact (isSimilar_of_eventually_eq (hφ i)).trans
      (isSimilar_of_eventually_eq ((hφ i').mono fun n hn => by rw [h]; exact hn.symm))
  exact ⟨rfl, Equiv.ofBijective φ hinj.bijective_of_finite, hφ⟩

/-! ### Theorem 8.2.1: the dimension of the kernel of a recurrence operator on `S(K)` -/

/-- `y` solves the recurrence `∑_{i ≤ r} q_i(n) y(n+i) = 0` for all `n ≥ 0`. -/
def IsRecSol (q : ℕ → ℕ → K) (r : ℕ) (y : ℕ → K) : Prop :=
  ∀ n, ∑ i ∈ Finset.range (r + 1), q i n * y (n + i) = 0

/-- The space of solutions on `ℕ`, as a `K`-subspace of the sequences. -/
def recSolSpace (q : ℕ → ℕ → K) (r : ℕ) : Submodule K (ℕ → K) where
  carrier := {y | IsRecSol q r y}
  zero_mem' := fun n => by simp
  add_mem' := fun {y z} hy hz n => by
    have h1 := hy n
    have h2 := hz n
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  smul_mem' := fun c y hy n => by
    have h1 : ∑ i ∈ Finset.range (r + 1), q i n * y (n + i) = 0 := hy n
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ i ∈ Finset.range (r + 1), q i n * (c * y (n + i))
        = c * ∑ i ∈ Finset.range (r + 1), q i n * y (n + i) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [h1, mul_zero]

/-- The solution of the recurrence with prescribed first `r` values (in the style of Mathlib's
`LinearRecurrence.mkSol`), going forward using `q_r(n) ≠ 0`. -/
def mkSol (q : ℕ → ℕ → K) (r : ℕ) (init : Fin r → K) : ℕ → K
  | n =>
    if h : n < r then init ⟨n, h⟩
    else
      -(∑ k : Fin r,
        have _ : n - r + k < n := by have := k.2; omega
        q k (n - r) * mkSol q r init (n - r + k)) / q r (n - r)

theorem mkSol_lt (q : ℕ → ℕ → K) (r : ℕ) (init : Fin r → K) {n : ℕ} (h : n < r) :
    mkSol q r init n = init ⟨n, h⟩ := by
  rw [mkSol, dif_pos h]

theorem mkSol_ge (q : ℕ → ℕ → K) (r : ℕ) (init : Fin r → K) {n : ℕ} (h : r ≤ n) :
    mkSol q r init n =
      -(∑ k : Fin r, q k (n - r) * mkSol q r init (n - r + k)) / q r (n - r) := by
  rw [mkSol, dif_neg (by omega)]

theorem isRecSol_mkSol (q : ℕ → ℕ → K) (r : ℕ) (hr : ∀ n, q r n ≠ 0) (init : Fin r → K) :
    IsRecSol q r (mkSol q r init) := by
  intro n
  rw [Finset.sum_range_succ, mkSol_ge q r init (by omega : r ≤ n + r), Nat.add_sub_cancel,
    ← Fin.sum_univ_eq_sum_range (fun i => q i n * mkSol q r init (n + i)) r]
  field_simp [hr n]
  ring

theorem eq_mkSol_of_isRecSol (q : ℕ → ℕ → K) (r : ℕ) (hr : ∀ n, q r n ≠ 0) {y : ℕ → K}
    (hy : IsRecSol q r y) (init : Fin r → K) (h : ∀ k : Fin r, y k = init k) :
    ∀ n, y n = mkSol q r init n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · rw [mkSol_lt q r init hn]; exact h ⟨n, hn⟩
    · push Not at hn
      rw [mkSol_ge q r init hn]
      have := hy (n - r)
      rw [Finset.sum_range_succ, Nat.sub_add_cancel hn,
        ← Fin.sum_univ_eq_sum_range (fun i => q i (n - r) * y (n - r + i)) r] at this
      have e : ∀ k : Fin r, y (n - r + k) = mkSol q r init (n - r + k) :=
        fun k => ih _ (by have := k.2; omega)
      simp only [e] at this
      field_simp [hr (n - r)]
      linear_combination this

/-- The solution space of a recurrence with `q_r(n) ≠ 0` for all `n` is isomorphic to `K^r` via
the first `r` values. -/
def initMap (q : ℕ → ℕ → K) (r : ℕ) : recSolSpace q r →ₗ[K] (Fin r → K) where
  toFun y k := y.1 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def recSolEquiv (q : ℕ → ℕ → K) (r : ℕ) (hr : ∀ n, q r n ≠ 0) :
    recSolSpace q r ≃ₗ[K] (Fin r → K) :=
  LinearEquiv.ofBijective (initMap q r)
    ⟨fun y z h => Subtype.ext (funext fun n =>
        (eq_mkSol_of_isRecSol q r hr y.2 (fun k => y.1 k) (fun _ => rfl) n).trans
          (eq_mkSol_of_isRecSol q r hr z.2 (fun k => y.1 k) (fun k => (congrFun h k).symm) n).symm),
      fun init => ⟨⟨mkSol q r init, isRecSol_mkSol q r hr init⟩, funext fun k =>
        mkSol_lt q r init k.2⟩⟩

/-- A solution vanishing from some point on, of a recurrence with `q_0(n) ≠ 0`, is zero. -/
theorem eq_zero_of_eventually_zero (q : ℕ → ℕ → K) (r : ℕ) (h0 : ∀ n, q 0 n ≠ 0) {y : ℕ → K}
    (hy : IsRecSol q r y) (M : ℕ) (hM : ∀ m, M ≤ m → y m = 0) : ∀ m, y m = 0 := by
  have key : ∀ k m, M ≤ m + k → y m = 0 := by
    intro k
    induction k with
    | zero => intro m hm; exact hM m (by omega)
    | succ k ih =>
      intro m hm
      have h1 := hy m
      rw [Finset.sum_range_succ'] at h1
      have h2 : ∑ i ∈ Finset.range r, q (i + 1) m * y (m + (i + 1)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ih (m + (i + 1)) (by omega), mul_zero]
      rw [h2, zero_add, Nat.add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left (h0 m)
  exact fun m => key M m (by omega)

/-- Backward extension: a sequence satisfying the recurrence for `n ≥ M` agrees from `M` on with a
solution on all of `ℕ`, if `q_0(n) ≠ 0` for all `n`. -/
theorem exists_recSol_extend (q : ℕ → ℕ → K) (r : ℕ) (h0 : ∀ n, q 0 n ≠ 0) (y0 : ℕ → K) (M : ℕ)
    (hM : ∀ n, M ≤ n → ∑ i ∈ Finset.range (r + 1), q i n * y0 (n + i) = 0) :
    ∃ y : ℕ → K, IsRecSol q r y ∧ ∀ m, M ≤ m → y m = y0 m := by
  have key : ∀ k : ℕ, ∃ y : ℕ → K, (∀ m, M ≤ m → y m = y0 m) ∧
      ∀ n, M ≤ n + k → ∑ i ∈ Finset.range (r + 1), q i n * y (n + i) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨y0, fun _ _ => rfl, fun n hn => hM n (by omega)⟩
    | succ k ih =>
      obtain ⟨y, hy1, hy2⟩ := ih
      by_cases hk : M ≤ k
      · exact ⟨y, hy1, fun n hn => hy2 n (by omega)⟩
      · push Not at hk
        obtain ⟨n0, hn0⟩ : ∃ n0, n0 + (k + 1) = M := ⟨M - (k + 1), by omega⟩
        obtain ⟨v, hv⟩ : ∃ v : K, v = -(∑ i ∈ Finset.range r, q (i + 1) n0 * y (n0 + (i + 1))) /
            q 0 n0 := ⟨_, rfl⟩
        refine ⟨Function.update y n0 v, fun m hm => ?_, fun n hn => ?_⟩
        · rw [Function.update_of_ne (by omega), hy1 m hm]
        · rcases (show n = n0 ∨ n0 < n by omega) with rfl | hlt
          · have e1 : (Function.update y n v) (n + 0) = v := by simp
            have e2 : ∀ i : ℕ, (Function.update y n v) (n + (i + 1)) = y (n + (i + 1)) :=
              fun i => Function.update_of_ne (by omega) _ _
            rw [Finset.sum_range_succ', e1]
            simp only [e2]
            have : q 0 n * v = -(∑ i ∈ Finset.range r, q (i + 1) n * y (n + (i + 1))) := by
              rw [hv]; field_simp [h0 n]
            linear_combination this
          · have := hy2 n (by omega)
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Function.update_of_ne (by omega)]
  obtain ⟨y, hy1, hy2⟩ := key M
  exact ⟨y, fun n => hy2 n (by omega), hy1⟩

/-- The shift iterates on germs: `N^i f = (n ↦ f(n+i))`. -/
theorem shift_iterate_coe (f : ℕ → K) (i : ℕ) :
    (⇑SeqRing.shift)^[i] (f : SeqRing K) = ((fun n => f (n + i) : ℕ → K) : SeqRing K) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, SeqRing.shift_coe]
    congr 1
    funext n
    congr 1
    omega

theorem germ_mul_smul (a b : SeqRing K) (c : K) : a * (c • b) = c • (a * b) := by
  induction a using Germ.inductionOn with | _ f => ?_
  induction b using Germ.inductionOn with | _ g => ?_
  rw [← Germ.coe_smul, ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_smul]
  congr 1
  funext n
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coe_sum_germ {ι : Type*} (s : Finset ι) (a : ι → ℕ → K) :
    ((fun n => ∑ i ∈ s, a i n : ℕ → K) : SeqRing K) = ∑ i ∈ s, ((a i : ℕ → K) : SeqRing K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih, ← Germ.coe_add]
    rfl

/-- The kernel of `L = ∑_{i ≤ r} a_i N^i` (`a_i ∈ S(K)`) on `S(K)`, a `K`-subspace. -/
def kerOp (ps : ℕ → SeqRing K) (r : ℕ) : Submodule K (SeqRing K) where
  carrier := {g | ∑ i ∈ Finset.range (r + 1), ps i * (⇑SeqRing.shift)^[i] g = 0}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show (0 : SeqRing K) = ((0 : ℕ → K) : SeqRing K) from rfl, shift_iterate_coe]
    rw [show (fun n => (0 : ℕ → K) (n + i)) = (0 : ℕ → K) from rfl]
    simp
  add_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    have : ∀ i, (⇑SeqRing.shift)^[i] (g + h) = (⇑SeqRing.shift)^[i] g + (⇑SeqRing.shift)^[i] h :=
      fun i => iterate_map_add SeqRing.shift i g h
    simp only [this, mul_add, Finset.sum_add_distrib, hg, hh, add_zero]
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    induction g using Germ.inductionOn with | _ f => ?_
    have e : ∀ i, (⇑SeqRing.shift)^[i] (c • (f : SeqRing K)) =
        c • (⇑SeqRing.shift)^[i] (f : SeqRing K) := by
      intro i
      rw [← Germ.coe_smul, shift_iterate_coe, shift_iterate_coe, ← Germ.coe_smul]
      rfl
    simp only [e, germ_mul_smul, ← Finset.smul_sum, hg, smul_zero]

/-- For `a_i = [p_i]`, a germ `[f]` lies in the kernel iff `∑ p_i(n) f(n+i) = 0` for large `n`. -/
theorem coe_mem_kerOp_iff (ps : ℕ → SeqRing K) (r : ℕ) (p : ℕ → ℕ → K)
    (hp : ∀ i, ((p i : ℕ → K) : SeqRing K) = ps i) (f : ℕ → K) :
    (f : SeqRing K) ∈ kerOp ps r ↔
      ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (r + 1), p i n * f (n + i) = 0 := by
  show ∑ i ∈ Finset.range (r + 1), ps i * (⇑SeqRing.shift)^[i] (f : SeqRing K) = 0 ↔ _
  have : ∑ i ∈ Finset.range (r + 1), ps i * (⇑SeqRing.shift)^[i] (f : SeqRing K) =
      ((fun n => ∑ i ∈ Finset.range (r + 1), p i n * f (n + i) : ℕ → K) : SeqRing K) := by
    rw [coe_sum_germ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hp i, shift_iterate_coe, ← Germ.coe_mul]
    rfl
  rw [this, SeqRing.coe_eq_zero_iff]

/-- CO-482. Theorem 8.2.1: let `L = ∑_{k=0}^r a_k N^k` be a linear recurrence operator of order
`r` on `S(K)`.  If `a_r` and `a_0` are units of `S(K)` then `dim Ker L = r`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.2.1, p. 157"]
theorem finrank_kerOp (ps : ℕ → SeqRing K) (r : ℕ) (hr : IsUnit (ps r)) (h0 : IsUnit (ps 0)) :
    Module.finrank K (kerOp ps r) = r := by
  choose p hp using fun i => SeqRing.exists_coe (ps i)
  have hr' : ∀ᶠ n : ℕ in atTop, p r n ≠ 0 := by
    rw [← hp r] at hr; exact SeqRing.isUnit_coe_iff.1 hr
  have h0' : ∀ᶠ n : ℕ in atTop, p 0 n ≠ 0 := by
    rw [← hp 0] at h0; exact SeqRing.isUnit_coe_iff.1 h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr'.and h0')
  set q : ℕ → ℕ → K := fun i m => p i (N + m) with hqdef
  have hqr : ∀ m, q r m ≠ 0 := fun m => (hN (N + m) (by omega)).1
  have hq0 : ∀ m, q 0 m ≠ 0 := fun m => (hN (N + m) (by omega)).2
  let Φ : recSolSpace q r →ₗ[K] SeqRing K :=
    { toFun := fun y => ((fun m => y.1 (m - N) : ℕ → K) : SeqRing K)
      map_add' := fun y z => by
        rw [← Germ.coe_add]; rfl
      map_smul' := fun c y => by
        rw [← Germ.coe_smul]; rfl }
  have hΦ : ∀ y, Φ y = ((fun m => y.1 (m - N) : ℕ → K) : SeqRing K) := fun y => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hΦ, SeqRing.coe_eq_zero_iff] at hy
    obtain ⟨M, hM⟩ := eventually_atTop.1 hy
    refine Subtype.ext (funext fun m => ?_)
    exact eq_zero_of_eventually_zero q r hq0 y.2 M (fun m hm => by
      simpa using hM (m + N) (by omega)) m
  have hrange : LinearMap.range Φ = kerOp ps r := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      rw [hΦ, coe_mem_kerOp_iff ps r p hp]
      filter_upwards [eventually_ge_atTop N] with n hn
      have := y.2 (n - N)
      simp only [q] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_cancel' hn, show n + i - N = n - N + i by omega]
    · intro hg
      obtain ⟨f, rfl⟩ := SeqRing.exists_coe g
      obtain ⟨M0, hM0⟩ := eventually_atTop.1 ((coe_mem_kerOp_iff ps r p hp f).1 hg)
      obtain ⟨y, hy, hyf⟩ := exists_recSol_extend q r hq0 (fun m => f (N + m)) M0 (fun n hn => by
        have := hM0 (N + n) (by omega)
        simp only [q]
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show N + (n + i) = N + n + i by omega])
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [hΦ]
      refine SeqRing.coe_eq_coe_iff.2 ?_
      filter_upwards [eventually_ge_atTop (N + M0)] with m hm
      rw [hyf (m - N) (by omega), show N + (m - N) = m by omega]
  have e1 : recSolSpace q r ≃ₗ[K] LinearMap.range Φ := LinearEquiv.ofInjective Φ hinj
  rw [← hrange, ← e1.finrank_eq, (recSolEquiv q r hqr).finrank_eq]
  simp

/-! ### Right division of recurrence operators (text, p. 172) -/

section Division

variable {F : Type*} [Field F] [MulSemiringAction (Multiplicative ℕ) F]

/-- The order of a skew polynomial (the largest exponent of `N` in its support; `0` for `0`). -/
def skewOrder (L : SkewPolynomial F) : ℕ := L.support.sup id

theorem skew_phi_iterate_ne_zero {c : F} (hc : c ≠ 0) (n : ℕ) :
    (⇑(SkewPolynomial.φ : F →+* F))^[n] c ≠ 0 := by
  intro h
  apply hc
  apply (SkewPolynomial.φ (R := F)).injective.iterate n
  rw [h]
  simp

theorem skew_support_monomial {k j : ℕ} {a : F} (h : j ∈ (SkewPolynomial.monomial k a).support) :
    j = k := by
  rw [SkewPolynomial.mem_support_iff, SkewPolynomial.coeff_monomial] at h
  by_contra hne
  exact h (if_neg (fun e => hne e.symm))

/-- CO-506. Right division with remainder for recurrence operators with coefficients in a field
`F` carrying the shift action (e.g. rational functions): for `L₂ ≠ 0` there are `Q, R` with
`L₁ = Q L₂ + R` and `ord R < ord L₂` (every exponent of `N` in `R` is smaller than `ord L₂`).
This is the abstract version; for `F = K(n)` with `N p(n) = p(n+1) N` it is the book's right
division. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem skew_right_division (L₁ L₂ : SkewPolynomial F) (hL₂ : L₂ ≠ 0) :
    ∃ Q R : SkewPolynomial F, L₁ = Q * L₂ + R ∧ ∀ k ∈ R.support, k < skewOrder L₂ := by
  classical
  have hne : L₂.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hL₂ (SkewPolynomial.support_eq_empty.1 h)
  obtain ⟨m, hmmem, hm⟩ := Finset.exists_mem_eq_sup L₂.support hne id
  have hmo : skewOrder L₂ = m := by simpa [skewOrder] using hm
  rw [hmo]
  have hc : L₂.coeff m ≠ 0 := SkewPolynomial.mem_support_iff.1 hmmem
  let P : SkewPolynomial F → Prop := fun L =>
    ∃ Q R : SkewPolynomial F, L = Q * L₂ + R ∧ ∀ k ∈ R.support, k < m
  have P0 : P 0 := ⟨0, 0, by simp, by simp⟩
  have Padd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨QA, RA, hA, hA'⟩ ⟨QB, RB, hB, hB'⟩
    refine ⟨QA + QB, RA + RB, by rw [hA, hB, add_mul]; abel, fun k hk => ?_⟩
    rcases Finset.mem_union.1 (SkewPolynomial.support_add hk) with h | h
    · exact hA' k h
    · exact hB' k h
  have hdec : L₂ = SkewPolynomial.monomial m (L₂.coeff m) +
      ∑ j ∈ L₂.support.erase m, SkewPolynomial.monomial j (L₂.coeff j) := by
    rw [Finset.add_sum_erase _ (fun j => SkewPolynomial.monomial j (L₂.coeff j)) hmmem]
    exact (SkewPolynomial.sum_monomial L₂).symm.trans (SkewPolynomial.sum_def L₂ _)
  have Pmono : ∀ k a, P (SkewPolynomial.monomial k a) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro a
    by_cases hk : k < m
    · exact ⟨0, SkewPolynomial.monomial k a, by simp, fun j hj => by
        rw [skew_support_monomial hj]; exact hk⟩
    · push Not at hk
      set a' : F := a / (⇑(SkewPolynomial.φ : F →+* F))^[k - m] (L₂.coeff m) with ha'
      have hφ := skew_phi_iterate_ne_zero hc (k - m)
      have h1 : SkewPolynomial.monomial (k - m) a' * SkewPolynomial.monomial m (L₂.coeff m) =
          SkewPolynomial.monomial k a := by
        rw [SkewPolynomial.monomial_mul_monomial, Nat.sub_add_cancel hk, ha',
          div_mul_cancel₀ _ hφ]
      have hmul : SkewPolynomial.monomial (k - m) a' * L₂ = SkewPolynomial.monomial k a +
          ∑ j ∈ L₂.support.erase m, SkewPolynomial.monomial (k - m + j)
            (a' * (⇑(SkewPolynomial.φ : F →+* F))^[k - m] (L₂.coeff j)) := by
        conv_lhs => rw [hdec]
        rw [mul_add, Finset.mul_sum, h1]
        congr 1
        exact Finset.sum_congr rfl fun j _ => SkewPolynomial.monomial_mul_monomial _ _ _ _
      have e : SkewPolynomial.monomial k a = SkewPolynomial.monomial (k - m) a' * L₂ +
          ∑ j ∈ L₂.support.erase m, SkewPolynomial.monomial (k - m + j)
            (-(a' * (⇑(SkewPolynomial.φ : F →+* F))^[k - m] (L₂.coeff j))) := by
        have : ∑ j ∈ L₂.support.erase m, SkewPolynomial.monomial (k - m + j)
            (-(a' * (⇑(SkewPolynomial.φ : F →+* F))^[k - m] (L₂.coeff j))) =
            -∑ j ∈ L₂.support.erase m, SkewPolynomial.monomial (k - m + j)
            (a' * (⇑(SkewPolynomial.φ : F →+* F))^[k - m] (L₂.coeff j)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => map_neg _ _
        rw [this, hmul]
        abel
      rw [e]
      refine Padd _ _ ⟨SkewPolynomial.monomial (k - m) a', 0, by simp, by simp⟩ ?_
      refine Finset.sum_induction _ P Padd P0 fun j hj => ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      have hjle : j ≤ m := by
        have := Finset.le_sup (f := id) (Finset.mem_of_mem_erase hj)
        simpa [hm] using this
      exact ih (k - m + j) (by omega) _
  induction L₁ using SkewPolynomial.induction with
  | h0 => exact P0
  | ha n r q _ _ ih => exact Padd _ _ (Pmono n r) ih

end Division

/-! ### The shift action on rational functions -/

/-- The shift `r(n) ↦ r(n+1)` on rational functions, as a ring endomorphism of `K(n)`. -/
noncomputable def ratShift (K : Type*) [Field K] [CharZero K] : RatFunc K →+* RatFunc K :=
  RatFunc.mapRingHom (compRingHom (X + 1 : K[X])) (by
    intro p hp
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    show p.comp (X + 1) ∈ nonZeroDivisors K[X]
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact comp_X_add_one_ne_zero hp)

/-- `ℕ` acts on `K(n)` by iterating the shift, so that `K(n)[N; σ]` is the ring of recurrence
operators with rational coefficients (`N r(n) = r(n+1) N`). -/
noncomputable scoped instance ratShiftAction (K : Type*) [Field K] [CharZero K] :
    MulSemiringAction (Multiplicative ℕ) (RatFunc K) :=
  MulSemiringAction.compHom (RatFunc K) (powersHom (RatFunc K →+* RatFunc K) (ratShift K))

/-- CO-506, book shape: right division with remainder for recurrence operators with rational
coefficients, `L₁ = Q L₂ + R`, `ord R < ord L₂`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem ratfunc_right_division (K : Type*) [Field K] [CharZero K]
    (L₁ L₂ : SkewPolynomial (RatFunc K)) (hL₂ : L₂ ≠ 0) :
    ∃ Q R : SkewPolynomial (RatFunc K), L₁ = Q * L₂ + R ∧
      ∀ k ∈ R.support, k < skewOrder L₂ :=
  skew_right_division L₁ L₂ hL₂

end UndergradKB.Combinatorics.AeqB
