import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovLLN
import UndergradKB.Probability.ExamplesMarkov

/-! # The stepping stone model and the Land of Oz law of large numbers

Grinstead–Snell Examples 11.12 and 11.21.  The stepping stone model lives on the `n × n` torus `ZMod n × ZMod n`
with `k` colors; a state is a coloring.  One step chooses a site `s` and one of its eight neighbors `s + d`
uniformly and gives `s` the color of `s + d`.  The chain is absorbing, its absorbing states are the one-color
colorings, and the probability of absorption in the color `c` is the initial proportion of sites of color `c`. -/

set_option linter.unusedSectionVars false

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

/-- A coloring of the `n × n` torus with `k` colors: a state of the stepping stone chain. -/
abbrev SSColoring (n k : ℕ) := ZMod n × ZMod n → Fin k

/-- The eight neighbor offsets `(a, b) ≠ (0, 0)`, `a, b ∈ {-1, 0, 1}`, on the torus. -/
def ssOffsets (n : ℕ) : Finset (ZMod n × ZMod n) :=
  (({-1, 0, 1} : Finset (ZMod n)) ×ˢ ({-1, 0, 1} : Finset (ZMod n))).erase (0, 0)

/-- The result of the event "site `s` copies the color of the neighbor `s + d`" on the coloring `σ`. -/
def ssMove {n k : ℕ} (σ : SSColoring n k) (p : (ZMod n × ZMod n) × (ZMod n × ZMod n)) : SSColoring n k :=
  Function.update σ p.1 (σ (p.1 + p.2))

variable {n k : ℕ} [NeZero n] [NeZero k]

/-- Grinstead–Snell Example 11.12 (PR-213): the transition matrix of the stepping stone chain,
`P σ τ = (1 / (8 n²)) · #{(s, d) : τ = σ with the color of s replaced by that of s + d}`. -/
noncomputable def steppingStone (n k : ℕ) [NeZero n] : Matrix (SSColoring n k) (SSColoring n k) ℝ :=
  fun σ τ => (1 / (8 * (n : ℝ) ^ 2)) *
    ((((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).filter fun p => τ = ssMove σ p).card : ℝ)

theorem mem_ssOffsets {d : ZMod n × ZMod n} :
    d ∈ ssOffsets n ↔ d ≠ (0, 0) ∧ (d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1) ∧ (d.2 = -1 ∨ d.2 = 0 ∨ d.2 = 1) := by
  simp [ssOffsets, Finset.mem_erase, Finset.mem_product]

theorem ss_two_ne_zero (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem ss_one_ne_zero (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  intro h
  apply ss_two_ne_zero hn
  rw [show (2 : ZMod n) = 1 + 1 by norm_num, h, add_zero]

theorem ss_card_offsets (hn : 3 ≤ n) : (ssOffsets n).card = 8 := by
  have h1 := ss_one_ne_zero hn
  have h2 := ss_two_ne_zero hn
  have hm1 : (-1 : ZMod n) ≠ 0 := neg_ne_zero.2 h1
  have hm2 : (-1 : ZMod n) ≠ 1 := by
    intro h
    apply h2
    rw [show (2 : ZMod n) = 1 + 1 by norm_num]
    nth_rewrite 1 [← h]
    simp
  have h3 : ({-1, 0, 1} : Finset (ZMod n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [Ne.symm h1]
    · simp [hm1, hm2]
  rw [ssOffsets, Finset.card_erase_of_mem (by simp), Finset.card_product, h3]

theorem ss_card_pairs (hn : 3 ≤ n) :
    (((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).card : ℝ) = 8 * (n : ℝ) ^ 2 := by
  rw [Finset.card_product, ss_card_offsets hn, Finset.card_univ, Fintype.card_prod, ZMod.card]
  push_cast; ring

/-- The expectation of `g` after one step is the average of `g` over the equally likely events `(s, d)`. -/
theorem ss_mulVec_eq (σ : SSColoring n k) (g : SSColoring n k → ℝ) :
    ∑ τ, steppingStone n k σ τ * g τ =
      (1 / (8 * (n : ℝ) ^ 2)) * ∑ p ∈ (Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n,
        g (ssMove σ p) := by
  simp only [steppingStone, Finset.natCast_card_filter, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

theorem steppingStone_nonneg (σ τ : SSColoring n k) : 0 ≤ steppingStone n k σ τ := by
  unfold steppingStone; positivity

/-- Grinstead–Snell Example 11.12 (PR-213): the stepping stone matrix is a transition matrix (row stochastic). -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem steppingStone_mem (hn : 3 ≤ n) : steppingStone n k ∈ rowStochastic ℝ (SSColoring n k) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨steppingStone_nonneg, fun σ => ?_⟩
  have := ss_mulVec_eq σ (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at this
  rw [this, ss_card_pairs hn]
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  field_simp

/-- If a set of sites contains `u` and is closed under `s ↦ s + (1, 0)` and `s ↦ s + (0, 1)`, it is everything. -/
theorem ss_closed {U : Set (ZMod n × ZMod n)} {u : ZMod n × ZMod n} (hu : u ∈ U)
    (h1 : ∀ s ∈ U, s + (1, 0) ∈ U) (h2 : ∀ s ∈ U, s + (0, 1) ∈ U) (x : ZMod n × ZMod n) : x ∈ U := by
  have ha : ∀ m : ℕ, u + ((m : ZMod n), 0) ∈ U := by
    intro m
    induction m with
    | zero => simpa [Prod.mk_zero_zero] using hu
    | succ m ih =>
      have := h1 _ ih
      convert this using 1
      ext <;> simp [add_assoc]
  have hb : ∀ m m' : ℕ, u + ((m : ZMod n), 0) + (0, (m' : ZMod n)) ∈ U := by
    intro m m'
    induction m' with
    | zero => simpa [Prod.mk_zero_zero] using ha m
    | succ m' ih =>
      have := h2 _ ih
      convert this using 1
      ext <;> simp [add_assoc]
  have := hb (x.1 - u.1).val (x.2 - u.2).val
  convert this using 1
  ext <;> simp

/-- A function on sites unchanged by the two unit steps is constant. -/
theorem ss_const_of_invariant {α : Type*} (g : ZMod n × ZMod n → α)
    (h1 : ∀ s, g (s + (1, 0)) = g s) (h2 : ∀ s, g (s + (0, 1)) = g s) (x y : ZMod n × ZMod n) :
    g x = g y := by
  have := ss_closed (U := {s | g s = g y}) (u := y) rfl (fun s hs => by simp only [Set.mem_ofPred_eq] at *; rw [h1, hs])
    (fun s hs => by simp only [Set.mem_ofPred_eq] at *; rw [h2, hs]) x
  exact this

theorem ss_move_eq_self_iff (σ : SSColoring n k) (p : (ZMod n × ZMod n) × (ZMod n × ZMod n)) :
    σ = ssMove σ p ↔ σ (p.1 + p.2) = σ p.1 := by
  unfold ssMove
  rw [eq_comm, Function.update_eq_self_iff]

/-- Grinstead–Snell Example 11.12 (PR-213): the absorbing states of the stepping stone chain are exactly the
one-color colorings. -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem steppingStone_absorbing_iff (hn : 3 ≤ n) (σ : SSColoring n k) :
    IsAbsorbingState (steppingStone n k) σ ↔ ∃ c, ∀ s, σ s = c := by
  have hA := ss_card_pairs hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiag : steppingStone n k σ σ = (1 / (8 * (n : ℝ) ^ 2)) *
      ((((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).filter
        fun p => σ (p.1 + p.2) = σ p.1).card : ℝ) := by
    simp only [steppingStone, ss_move_eq_self_iff]
  unfold IsAbsorbingState
  rw [hdiag]
  constructor
  · intro h
    have hcard : ((((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).filter
        fun p => σ (p.1 + p.2) = σ p.1).card : ℝ) = (((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).card : ℝ) := by
      rw [hA]; field_simp at h; linarith
    have hcard' := Nat.cast_injective hcard
    have hall := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hcard'.ge
    have hmem : ∀ d ∈ ssOffsets n, ∀ s, σ (s + d) = σ s := fun d hd s => by
      have := (Finset.ext_iff.1 hall (s, d)).2 (by simp [hd])
      exact (Finset.mem_filter.1 this).2
    exact ⟨σ 0, fun s => ss_const_of_invariant σ
      (fun s => hmem (1, 0) (mem_ssOffsets.2 ⟨fun h => ss_one_ne_zero hn (congrArg Prod.fst h), by simp, by simp⟩) s)
      (fun s => hmem (0, 1) (mem_ssOffsets.2 ⟨fun h => ss_one_ne_zero hn (congrArg Prod.snd h), by simp, by simp⟩) s) s 0⟩
  · rintro ⟨c, hc⟩
    have : ((Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n).filter
        (fun p => σ (p.1 + p.2) = σ p.1) = (Finset.univ : Finset (ZMod n × ZMod n)) ×ˢ ssOffsets n :=
      Finset.filter_true_of_mem fun p _ => by rw [hc, hc]
    rw [this, hA]
    field_simp

theorem ss_pow_succ_pos {σ τ ρ : SSColoring n k} (h : 0 < steppingStone n k σ τ) {j : ℕ}
    (hj : 0 < (steppingStone n k ^ j) τ ρ) (hn : 3 ≤ n) : 0 < (steppingStone n k ^ (j + 1)) σ ρ := by
  have hP := steppingStone_mem (k := k) hn
  rw [pow_succ', Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos h hj) (Finset.single_le_sum (f := fun x => steppingStone n k σ x *
    (steppingStone n k ^ j) x ρ) (fun x _ => mul_nonneg (steppingStone_nonneg _ _)
    (nonneg_of_mem_rowStochastic (pow_mem hP j))) (Finset.mem_univ τ))

theorem ss_step_pos {σ : SSColoring n k} {s d : ZMod n × ZMod n} (hd : d ∈ ssOffsets n) (hn : 3 ≤ n) :
    0 < steppingStone n k σ (ssMove σ (s, d)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold steppingStone
  refine mul_pos (by positivity) ?_
  exact_mod_cast Finset.card_pos.2 ⟨(s, d), by simp [hd]⟩

/-- From a coloring in which the color `c` occurs, the one-color coloring `c` can be reached: the color spreads
one site at a time, to a site next to a site of color `c`. -/
theorem ss_reach (hn : 3 ≤ n) (c : Fin k) : ∀ m : ℕ, ∀ σ : SSColoring n k, (∃ u, σ u = c) →
    (Finset.univ.filter fun s => σ s ≠ c).card = m → ∃ j, 0 < (steppingStone n k ^ j) σ (fun _ => c) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro σ ⟨u0, hu0⟩ hm
    by_cases hall : ∀ s, σ s = c
    · exact ⟨0, by have : σ = fun _ => c := funext hall
                   subst this; simp⟩
    · have hex : ∃ u s d, σ u = c ∧ σ s ≠ c ∧ d ∈ ssOffsets n ∧ s + d = u := by
        by_contra H
        push Not at H
        apply hall
        have h1 : (1 : ZMod n) ≠ 0 := ss_one_ne_zero hn
        have := ss_closed (U := {s | σ s = c}) (u := u0) hu0
          (fun s hs => by
            by_contra hne
            exact H s (s + (1, 0)) (-(1, 0)) hs hne
              (mem_ssOffsets.2 ⟨by simpa [Prod.ext_iff] using h1, by simp, by simp⟩) (by ext <;> simp))
          (fun s hs => by
            by_contra hne
            exact H s (s + (0, 1)) (-(0, 1)) hs hne
              (mem_ssOffsets.2 ⟨by simpa [Prod.ext_iff] using h1, by simp, by simp⟩) (by ext <;> simp))
        intro s
        exact this s
      obtain ⟨u, s, d, hu, hs, hd, hsd⟩ := hex
      have hτs : ssMove σ (s, d) s = c := by simp [ssMove, hsd, hu]
      have hlt : (Finset.univ.filter fun t => ssMove σ (s, d) t ≠ c).card < m := by
        rw [← hm]
        refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          by_cases hts : t = s
          · exact absurd (hts ▸ hτs) ht
          · simpa [ssMove, Function.update_of_ne hts] using ht
        · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ s, hs⟩)
          simp only [Finset.mem_filter] at this
          exact this.2 hτs
      obtain ⟨j, hj⟩ := ih _ hlt (ssMove σ (s, d)) ⟨s, hτs⟩ rfl
      exact ⟨j + 1, ss_pow_succ_pos (ss_step_pos hd hn) hj hn⟩

/-- Grinstead–Snell Example 11.12 (PR-213): the stepping stone chain is an absorbing chain (the absorbing states
are the one-color colorings, and from every coloring a one-color coloring is reachable). -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem steppingStone_isAbsorbingChain (hn : 3 ≤ n) : IsAbsorbingChain (steppingStone n k) := by
  have habs : ∀ c : Fin k, IsAbsorbingState (steppingStone n k) (fun _ => c) :=
    fun c => (steppingStone_absorbing_iff hn _).2 ⟨c, fun _ => rfl⟩
  refine ⟨⟨fun _ => (0 : Fin k), habs 0⟩, fun σ => ?_⟩
  obtain ⟨j, hj⟩ := ss_reach hn (σ 0) _ σ ⟨0, rfl⟩ rfl
  exact ⟨j, _, habs _, hj⟩

/-! ### Harmonic function: the proportion of a color -/

/-- The proportion of sites of color `c` in the coloring `σ`. -/
noncomputable def ssProp (c : Fin k) (σ : SSColoring n k) : ℝ :=
  ((Finset.univ.filter fun s => σ s = c).card : ℝ) / (n : ℝ) ^ 2

theorem ss_count_move (c : Fin k) (σ : SSColoring n k) (s d : ZMod n × ZMod n) :
    ((Finset.univ.filter fun t => ssMove σ (s, d) t = c).card : ℝ) =
      ((Finset.univ.filter fun t => σ t = c).card : ℝ) - (if σ s = c then 1 else 0) +
        (if σ (s + d) = c then 1 else 0) := by
  simp only [Finset.natCast_card_filter]
  have : ∀ t, (if ssMove σ (s, d) t = c then (1 : ℝ) else 0) =
      (if σ t = c then 1 else 0) + (if t = s then ((if σ (s + d) = c then 1 else 0) -
        (if σ s = c then 1 else 0)) else 0) := by
    intro t
    by_cases h : t = s
    · subst h; simp [ssMove]
    · simp [ssMove, Function.update_of_ne h, h]
  rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_add_distrib, Finset.sum_ite_eq' ]
  simp; ring

theorem ss_harmonic (hn : 3 ≤ n) (c : Fin k) : steppingStone n k *ᵥ ssProp c = ssProp c := by
  funext σ
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ∑ τ, steppingStone n k σ τ * ssProp c τ = _ := ss_mulVec_eq σ (ssProp c)
  show ∑ τ, steppingStone n k σ τ * ssProp c τ = ssProp c σ
  rw [h1, Finset.sum_product]
  simp only [ssProp, ← Finset.sum_div, ss_count_move]
  rw [Finset.sum_comm]
  have hshift : ∀ d : ZMod n × ZMod n,
      ∑ s, (if σ (s + d) = c then (1 : ℝ) else 0) = ((Finset.univ.filter fun t => σ t = c).card : ℝ) := by
    intro d
    rw [Finset.natCast_card_filter]
    exact Equiv.sum_comp (Equiv.addRight d) (fun t => if σ t = c then (1 : ℝ) else 0)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun d _ => hshift d, ← Finset.natCast_card_filter, Finset.sum_const, nsmul_eq_mul,
    ss_card_offsets hn, Fintype.card_prod, ZMod.card]
  push_cast
  field_simp
  ring

/-- Grinstead–Snell Example 11.12 (PR-213), the book's statement (Exercise 11.2.32): starting from the non-absorbing
coloring `σ`, the probability that the chain is absorbed in the one-color coloring of color `c` (the entry of
`B = N R` of the absorbing chain) equals the initial proportion `#{s : σ s = c} / n²` of sites of color `c`. -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem steppingStone_absorption_prob (hn : 3 ≤ n) (σ : SSColoring n k)
    (hσ : ¬ IsAbsorbingState (steppingStone n k) σ) (c : Fin k) :
    (fundamentalMatrix (steppingStone n k) * absorbR (steppingStone n k)) ⟨σ, hσ⟩
        ⟨fun _ => c, (steppingStone_absorbing_iff hn _).2 ⟨c, fun _ => rfl⟩⟩ =
      ((Finset.univ.filter fun s => σ s = c).card : ℝ) / (n : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h := harmonic_eq_absorption (steppingStone_mem hn) (steppingStone_isAbsorbingChain hn)
    (ss_harmonic hn c) ⟨σ, hσ⟩
  have hf : ∀ a : Absorbing (steppingStone n k), ssProp c a.1 =
      if a = ⟨fun _ => c, (steppingStone_absorbing_iff hn _).2 ⟨c, fun _ => rfl⟩⟩ then 1 else 0 := by
    intro a
    obtain ⟨c', hc'⟩ := (steppingStone_absorbing_iff hn _).1 a.2
    have ha : (a : SSColoring n k) = fun _ => c' := funext hc'
    by_cases hcc : c' = c
    · subst hcc
      have : a = ⟨fun _ => c', (steppingStone_absorbing_iff hn _).2 ⟨c', fun _ => rfl⟩⟩ := Subtype.ext ha
      rw [if_pos this]
      simp only [ssProp, ha, Finset.filter_true_of_mem (fun _ _ => rfl)]
      simp [Finset.card_univ, Fintype.card_prod, ZMod.card]
      field_simp
    · rw [if_neg (fun h => hcc (by have := congrFun (congrArg Subtype.val h) 0; simpa [ha] using this))]
      simp [ssProp, ha, hcc]
  simp only [hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h.symm

/-! ## Example 11.21: the Land of Oz year -/

/-- Grinstead–Snell Example 11.21 (PR-214): in the Land of Oz, whatever the weather on the first day (any initial
distribution `u`), the proportion of rainy, nice and snowy days among the first `n + 1` days converges in
probability to the long-run proportions `2/5, 1/5, 2/5`; so the expected counts in a year of 525 days are
`525 · (2/5, 1/5, 2/5) = (210, 105, 210)`. -/
@[kb "grinsteadsnell2006" "Example 11.21, p. 447"]
theorem oz_year_lln (u : Fin 3 → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1) :
    (∀ (j : Fin 3) (ε : ℝ), 0 < ε →
      Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → Fin 3 with
        ε ≤ |((univ.filter fun m : Fin (n + 1) => x m = j).card : ℝ) / ((n : ℝ) + 1) - ozFixed j|,
        pathProb u ozMatrix n x) atTop (𝓝 0)) ∧
    (∀ j, (525 : ℝ) * ozFixed j = (![210, 105, 210] : Fin 3 → ℝ) j) := by
  obtain ⟨w, -, hs, hfix, hlln⟩ := markov_lln ozMatrix_regular.isErgodicChain u hu0 hu
  have hw : w = ozFixed := ozMatrix_fixed.2.2 w hs hfix
  subst hw
  refine ⟨hlln, fun j => ?_⟩
  fin_cases j <;> simp [ozFixed] <;> norm_num

end UndergradKB.Probability
