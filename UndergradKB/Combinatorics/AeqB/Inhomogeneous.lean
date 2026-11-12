import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.SequenceRing
import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.SolutionSpace
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.OperatorsMore

/-!
# The inhomogeneous equation `L y = f` over the hypergeometric hull
(Petkovsek–Wilf–Zeilberger, "A = B", §8.9, pp. 171-172)
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### Closure properties of closed forms -/

theorem inh_closedForm_add {a b : ℕ → K} (ha : IsClosedForm a) (hb : IsClosedForm b) :
    IsClosedForm (fun n => a n + b n) := by
  obtain ⟨r₁, c₁, h₁, hh₁, e₁⟩ := ha
  obtain ⟨r₂, c₂, h₂, hh₂, e₂⟩ := hb
  refine ⟨r₁ + r₂, Fin.append c₁ c₂, Fin.append h₁ h₂, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using hh₁ i
    | right i => simpa using hh₂ i
  · filter_upwards [e₁, e₂] with n x y
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, x, y]

theorem inh_closedForm_neg {a : ℕ → K} (ha : IsClosedForm a) : IsClosedForm (fun n => - a n) := by
  obtain ⟨r, c, h, hh, e⟩ := ha
  refine ⟨r, fun i => - c i, h, hh, ?_⟩
  filter_upwards [e] with n x
  simp [x, Finset.sum_neg_distrib]

theorem inh_closedForm_sub {a b : ℕ → K} (ha : IsClosedForm a) (hb : IsClosedForm b) :
    IsClosedForm (fun n => a n - b n) := by
  simpa [sub_eq_add_neg] using inh_closedForm_add ha (inh_closedForm_neg hb)

theorem inh_isHypergeometric_one : IsHypergeometric (fun _ : ℕ => (1 : K)) := by
  rw [isHypergeometric_iff]
  exact ⟨Eventually.of_forall fun _ => one_ne_zero, 1, 1, one_ne_zero, one_ne_zero,
    Eventually.of_forall fun n => by simp⟩

/-- A finite sum of sequences, each eventually zero or hypergeometric, is of closed form. -/
theorem inh_closedForm_sum {ι : Type*} [Fintype ι] (g : ι → ℕ → K)
    (hg : ∀ i, (∀ᶠ n : ℕ in atTop, g i n = 0) ∨ IsHypergeometric (g i)) :
    IsClosedForm (fun n => ∑ i, g i n) := by
  classical
  let c : ι → K := fun i => if IsHypergeometric (g i) then 1 else 0
  let h : ι → ℕ → K := fun i => if IsHypergeometric (g i) then g i else fun _ => 1
  have hh : ∀ i, IsHypergeometric (h i) := by
    intro i
    by_cases hi : IsHypergeometric (g i)
    · simp [h, hi]
    · simpa [h, hi] using (inh_isHypergeometric_one (K := K))
  have hz : ∀ᶠ n : ℕ in atTop, ∀ i, ¬ IsHypergeometric (g i) → g i n = 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : IsHypergeometric (g i)
    · exact Eventually.of_forall fun n h' => absurd hi h'
    · exact ((hg i).resolve_right hi).mono fun n hn _ => hn
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => c (e.symm k), fun k => h (e.symm k), fun k => hh _, ?_⟩
  filter_upwards [hz] with n hn
  rw [Equiv.sum_comp e.symm (fun i => c i * h i n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : IsHypergeometric (g i)
  · simp [c, h, hi]
  · simp [c, hi, hn i hi]

/-- A rational multiple of a hypergeometric term is eventually zero or hypergeometric. -/
theorem inh_ratMul_zero_or_hyper {f r : ℕ → K} (hf : IsHypergeometric f) (hr : SeqRing.IsRationalSeq r) :
    (∀ᶠ n : ℕ in atTop, r n * f n = 0) ∨ IsHypergeometric (fun n => r n * f n) := by
  obtain ⟨p, q, hq, hr⟩ := hr
  by_cases hp : p = 0
  · left
    filter_upwards [hr] with n h
    simp [h, hp]
  · right
    refine IsSimilar.isHypergeometric ⟨p, q, hp, hq, ?_⟩ hf
    filter_upwards [hr, eventually_eval_ne_zero hq] with n h h2
    rw [h]
    field_simp

theorem inh_closedForm_sum_rat {ι : Type*} (J : Finset ι) (f r : ι → ℕ → K)
    (hf : ∀ j ∈ J, IsHypergeometric (f j)) (hr : ∀ j ∈ J, SeqRing.IsRationalSeq (r j)) :
    IsClosedForm (fun n => ∑ j ∈ J, r j n * f j n) := by
  have := inh_closedForm_sum (ι := J) (fun j n => r j n * f j n)
    (fun j => inh_ratMul_zero_or_hyper (hf j j.2) (hr j j.2))
  have e : (fun n => ∑ j : J, r j n * f j n) = fun n => ∑ j ∈ J, r j n * f j n :=
    funext fun n => Finset.sum_coe_sort J (fun j => r j n * f j n)
  rwa [e] at this

/-! ### CO-504 -/

/-- CO-504. Solving `L y = f_1 + ⋯ + f_m` (equality for large `n`) in closed form, where the `f_j`
are pairwise dissimilar hypergeometric terms: a closed-form solution `y` exists if and only if for
every `j` the equation `L (r_j f_j) = f_j` has a rational solution `r_j` (equivalently
`L_j r_j = 1` for the conjugated operator, see `act_mul_eq_self_iff`).  Abramov's algorithm, which
the book only cites, finds such `r_j`; here it is represented by the existence of `r_j`. -/
@[kb "petkovsekwilfzeilberger1996" "text (algorithm for Ly=f), p. 171-172"]
theorem exists_closedForm_solution_iff {ι : Type*} (L : RecOp K) (J : Finset ι) (f : ι → ℕ → K)
    (hf : ∀ j ∈ J, IsHypergeometric (f j))
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (f i) (f j)) :
    (∃ y : ℕ → K, IsClosedForm y ∧
        ∀ᶠ n : ℕ in atTop, RecOp.act L y n = ∑ j ∈ J, f j n) ↔
      ∀ j ∈ J, ∃ r : ℕ → K, SeqRing.IsRationalSeq r ∧
        ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => r m * f j m) n = f j n := by
  classical
  constructor
  · rintro ⟨y, ⟨ρ, c, h, hh, hyc⟩, hLy⟩
    set s : Finset (Fin ρ) := Finset.univ.filter (fun i => c i ≠ 0) with hs
    let t : Fin ρ → ℕ → K := fun i n => c i * h i n
    have ht : ∀ i ∈ s, IsHypergeometric (t i) := fun i hi =>
      (hh i).const_mul (Finset.mem_filter.1 hi).2
    obtain ⟨J', u, -, hJh, hJd, hJsum⟩ := exists_dissimilar_sum s t ht
    have hfs : ∀ n, ∑ i, c i * h i n = ∑ i ∈ s, t i n := by
      intro n
      rw [hs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hc : c i = 0 <;> simp [t, hc]
    have hys : ∀ᶠ n : ℕ in atTop, y n = ∑ j ∈ J', u j n := by
      filter_upwards [hyc, hJsum] with n a b
      rw [a, hfs n, b]
    have hLu : ∀ᶠ n : ℕ in atTop, ∑ j ∈ J', RecOp.act L (u j) n = ∑ j ∈ J, f j n := by
      have := RecOp.act_congr_eventually L (f := y) (g := fun m => ∑ j ∈ J', u j m) hys
      filter_upwards [this, hLy] with n h1 h2
      rw [← RecOp.act_sum_seq L J' u n, ← h1]
      exact h2
    set J'' : Finset (Fin ρ) :=
      J'.filter (fun i => ¬ ∀ᶠ n : ℕ in atTop, RecOp.act L (u i) n = 0) with hJ''
    have hv : ∀ i ∈ J'', IsHypergeometric (RecOp.act L (u i)) ∧
        IsSimilar (RecOp.act L (u i)) (u i) := fun i hi =>
      RecOp.isHypergeometric_act L (hJh i (Finset.mem_filter.1 hi).1) (Finset.mem_filter.1 hi).2
    have hrest : ∀ᶠ n : ℕ in atTop, ∀ i ∈ J', i ∉ J'' → RecOp.act L (u i) n = 0 := by
      rw [Filter.eventually_all_finset]
      intro i hi
      by_cases hz : ∀ᶠ n : ℕ in atTop, RecOp.act L (u i) n = 0
      · exact hz.mono fun n hn _ => hn
      · exact Eventually.of_forall fun n h' => absurd (Finset.mem_filter.2 ⟨hi, hz⟩) h'
    have hsum : ∀ᶠ n : ℕ in atTop, ∑ j ∈ J', RecOp.act L (u j) n = ∑ j ∈ J'', RecOp.act L (u j) n := by
      filter_upwards [hrest] with n hn
      exact (Finset.sum_subset (Finset.filter_subset _ _) fun i hi hi' => hn i hi hi').symm
    have hdv : ∀ i ∈ J'', ∀ i' ∈ J'', i ≠ i' →
        ¬ IsSimilar (RecOp.act L (u i)) (RecOp.act L (u i')) := by
      intro i hi i' hi' hne hsim
      exact hJd i (Finset.mem_filter.1 hi).1 i' (Finset.mem_filter.1 hi').1 hne
        ((hv i hi).2.symm.trans (hsim.trans (hv i' hi').2))
    obtain ⟨-, hmap⟩ := dissimilar_repr_unique J J'' f (fun i => RecOp.act L (u i)) hf
      (fun i hi => (hv i hi).1) hd hdv
      (by filter_upwards [hLu, hsum] with n a b; exact a.symm.trans b)
    intro j hj
    obtain ⟨i, hi, e⟩ := hmap j hj
    have hsimu : IsSimilar (u i) (f j) :=
      (hv i hi).2.symm.trans (isSimilar_of_eventually_eq (e.mono fun n hn => hn.symm))
    obtain ⟨p, q, hp, hq, hpq⟩ := hsimu
    refine ⟨fun n => p.eval (n : K) / q.eval (n : K), ⟨p, q, hq, Eventually.of_forall fun _ => rfl⟩,
      ?_⟩
    have hu : ∀ᶠ n : ℕ in atTop, u i n = p.eval (n : K) / q.eval (n : K) * f j n := by
      filter_upwards [hpq, eventually_eval_ne_zero hq] with n h1 h2
      rw [div_mul_eq_mul_div, eq_div_iff h2]
      linear_combination h1
    have := RecOp.act_congr_eventually L hu
    filter_upwards [this, e] with n h1 h2
    rw [← h1]
    exact h2.symm
  · intro h
    choose! r hrat hL using h
    obtain ⟨z, hz⟩ : ∃ z : ℕ → K, z = fun m => ∑ j ∈ J, r j m * f j m := ⟨_, rfl⟩
    refine ⟨z, ?_, ?_⟩
    · rw [hz]
      exact inh_closedForm_sum_rat J f r hf hrat
    · have := RecOp.act_sum_particular L J (fun j m => r j m * f j m) f hL 0
        (Eventually.of_forall fun n => congrFun (RecOp.act_zero_seq L) n)
      rw [hz]
      simpa using this

/-- CO-504. Structure of the closed-form solutions of `L y = f_1 + ⋯ + f_m`: once rational
solutions `r_j` of `L (r_j f_j) = f_j` are known, every closed-form solution `y` is, for large `n`,
`∑ r_j f_j + h` with `h` of closed form and `L h = 0`.  (Conversely, any closed-form `h` with
`L h = 0` gives a solution `∑ r_j f_j + h`, by `act_sum_particular`; the book chooses `h` from a
hypergeometric basis of `Ker L ∩ L(H_K)`, Corollary 8.7.1.)  Rational solutions are those
produced by Abramov's algorithm, which the book only cites. -/
@[kb "petkovsekwilfzeilberger1996" "text (algorithm for Ly=f), p. 171-172"]
theorem closedForm_solutions_structure {ι : Type*} (L : RecOp K) (J : Finset ι) (f r : ι → ℕ → K)
    (hf : ∀ j ∈ J, IsHypergeometric (f j)) (hrat : ∀ j ∈ J, SeqRing.IsRationalSeq (r j))
    (hL : ∀ j ∈ J, ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => r j m * f j m) n = f j n)
    (y : ℕ → K) (hy : IsClosedForm y)
    (hLy : ∀ᶠ n : ℕ in atTop, RecOp.act L y n = ∑ j ∈ J, f j n) :
    ∃ h : ℕ → K, IsClosedForm h ∧ (∀ᶠ n : ℕ in atTop, RecOp.act L h n = 0) ∧
      ∀ n, y n = ∑ j ∈ J, r j n * f j n + h n := by
  obtain ⟨z, hz⟩ : ∃ z : ℕ → K, z = fun m => ∑ j ∈ J, r j m * f j m := ⟨_, rfl⟩
  have hzc : IsClosedForm z := by
    rw [hz]; exact inh_closedForm_sum_rat J f r hf hrat
  have hzL : ∀ᶠ n : ℕ in atTop, RecOp.act L z n = ∑ j ∈ J, f j n := by
    have := RecOp.act_sum_particular L J (fun j m => r j m * f j m) f hL 0
      (Eventually.of_forall fun n => congrFun (RecOp.act_zero_seq L) n)
    rw [hz]
    simpa using this
  refine ⟨fun n => y n - z n, inh_closedForm_sub hy hzc, ?_, fun n => by simp [hz]⟩
  have hyz : y = z + fun n => y n - z n := by
    funext n
    simp
  have h1 := RecOp.act_add_seq L z (fun n => y n - z n)
  rw [← hyz] at h1
  filter_upwards [hLy, hzL] with n a b
  have := congrFun h1 n
  simp only [Pi.add_apply] at this
  linear_combination a - b - this

end UndergradKB.Combinatorics.AeqB
