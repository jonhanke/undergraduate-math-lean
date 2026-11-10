import UndergradKB.Combinatorics.Probability.RamseyLLL3
import UndergradKB.Common.Attr

/-!
# R(3,n) ≥ c n² / ln² n via the Local Lemma, part 4

The asymmetric Local Lemma inequalities and the existence of a triangle-free graph with no
independent `n`-set under explicit numerical hypotheses on `(N, n, p)`.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace RamseyLLL

open ErdosGirth UndergradKB.Combinatorics.Probability

lemma exp_neg_two_le {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1 / 2) : Real.exp (-2 * f) ≤ 1 - f := by
  have h2 : 1 + 2 * f ≤ Real.exp (2 * f) := by linarith [Real.add_one_le_exp (2 * f)]
  have h3 : Real.exp (-2 * f) * Real.exp (2 * f) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-2 * f) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]

lemma exp_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 / 2) :
    Real.exp (-2 * ∑ j ∈ s, f j) ≤ ∏ j ∈ s, (1 - f j) := by
  have : Real.exp (-2 * ∑ j ∈ s, f j) = ∏ j ∈ s, Real.exp (-2 * f j) := by
    rw [Finset.mul_sum, Real.exp_sum]
  rw [this]
  exact Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
    (fun j hj => exp_neg_two_le (h j hj).1 (h j hj).2)

section Existence

variable {N n : ℕ}

lemma prob_ev_three (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) {X : Finset (Fin N)} (hX : X.card = 3) :
    (space N p h0 h1).prob (ev N n X) = p ^ 3 := by
  classical
  unfold ev
  rw [if_pos hX, space_prob, sum_wt_sub, card_DA, hX]
  norm_num [Nat.choose]

lemma prob_ev_n (hn : 4 ≤ n) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) {X : Finset (Fin N)}
    (hX : X.card = n) :
    (space N p h0 h1).prob (ev N n X) = (1 - p) ^ (n.choose 2) := by
  classical
  unfold ev
  rw [if_neg (by omega), if_pos hX, space_prob, sum_wt_disjoint, card_DA, hX]

/-- **The Local Lemma step.**  Under explicit numerical conditions there is an edge set on `N`
vertices with no triangle and no independent `n`-set. -/
theorem exists_edgeSet (hn : 4 ≤ n) (hnN : n ≤ N) {p : ℝ} (hp0 : 0 < p) (hp3 : p ≤ 1 / 3)
    (hNp : (N : ℝ) * p ^ 2 ≤ 1 / 16)
    (hK : 8 * (N.choose (n - 2) : ℝ) * Real.exp (-(p * (n.choose 2 : ℝ)) / 2) ≤ p) :
    ∃ ω : Finset (Sym2 (Fin N)),
      (∀ X : Finset (Fin N), X.card = 3 → ¬ DA X ⊆ ω) ∧
      ∀ X : Finset (Fin N), X.card = n → ¬ Disjoint ω (DA X) := by
  classical
  have hp1 : p ≤ 1 := by linarith
  set C : ℝ := (n.choose 2 : ℝ) with hC
  have hC6 : (6 : ℝ) ≤ C := by
    have : (4 : ℕ).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hn
    have h6 : (4 : ℕ).choose 2 = 6 := by decide
    rw [h6] at this
    rw [hC]; exact_mod_cast this
  set K : ℝ := (N.choose (n - 2) : ℝ) with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have : 0 < N.choose (n - 2) := Nat.choose_pos (by omega)
    rw [hKdef]; exact_mod_cast this
  set x : ℝ := 2 * p ^ 3 with hxdef
  set y : ℝ := Real.exp (-(p * C) / 2) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y < 1 := by
    rw [hydef, Real.exp_lt_one_iff]; have : 0 < p * C := by positivity
    linarith
  have hyK : 8 * K * y ≤ p := hK
  have hy24 : y ≤ 1 / 24 := by
    have : 8 * y ≤ 8 * K * y := by nlinarith
    linarith
  have hx0 : 0 < x := by positivity
  have hx12 : x ≤ 1 / 2 := by
    have : p ^ 3 ≤ (1 / 3) ^ 3 := pow_le_pow_left₀ hp0.le hp3 3
    rw [hxdef]; norm_num at this ⊢; linarith
  have hQ : (N : ℝ) * x + K * y ≤ p / 4 := by
    have h1 : (N : ℝ) * x = 2 * p * ((N : ℝ) * p ^ 2) := by rw [hxdef]; ring
    have h2 : (N : ℝ) * x ≤ p / 8 := by
      rw [h1]; nlinarith
    have h3 : K * y ≤ p / 8 := by linarith
    linarith
  have hwpos : ∀ j : Finset (Fin N), 0 < wgt n x y j := fun j => by
    unfold wgt; split_ifs <;> assumption
  have hwhalf : ∀ j : Finset (Fin N), wgt n x y j ≤ 1 / 2 := fun j => by
    unfold wgt; split_ifs
    · exact hx12
    · linarith
  have hw1 : ∀ j : Finset (Fin N), wgt n x y j < 1 := fun j => by linarith [hwhalf j]
  have hP : ∀ i : Finset (Fin N), (space N p hp0.le hp1).prob (ev N n i) ≤
      wgt n x y i * ∏ j ∈ nbr N n i, (1 - wgt n x y j) := by
    intro i
    have hprodnn : 0 ≤ ∏ j ∈ nbr N n i, (1 - wgt n x y j) :=
      Finset.prod_nonneg fun j _ => by linarith [hw1 j]
    by_cases hg : good N n i
    · have hprod := exp_le_prod_one_sub (nbr N n i) (wgt n x y)
        (fun j _ => ⟨(hwpos j).le, hwhalf j⟩)
      have hsum := sum_nbr hn hx0.le hy0.le hg
      rcases hg with h3 | hn'
      · rw [prob_ev_three p hp0.le hp1 h3]
        have hcard : ((DA i).card : ℝ) = 3 := by rw [card_DA, h3]; norm_num [Nat.choose]
        rw [hcard] at hsum
        have hwi : wgt n x y i = x := by unfold wgt; rw [if_pos h3]
        rw [hwi]
        have h1 : 1 / 2 ≤ Real.exp (-2 * ∑ j ∈ nbr N n i, wgt n x y j) := by
          have h2 : -2 * (3 * ((N : ℝ) * x + K * y)) ≤ -2 * ∑ j ∈ nbr N n i, wgt n x y j := by
            linarith
          have h3' := Real.exp_le_exp.mpr h2
          have h4 := Real.add_one_le_exp (-2 * (3 * ((N : ℝ) * x + K * y)))
          linarith
        have h5 : p ^ 3 ≤ x * (1 / 2) := by rw [hxdef]; linarith
        calc p ^ 3 ≤ x * (1 / 2) := h5
          _ ≤ x * ∏ j ∈ nbr N n i, (1 - wgt n x y j) :=
              mul_le_mul_of_nonneg_left (h1.trans hprod) hx0.le
      · have h3 : ¬ i.card = 3 := by omega
        rw [prob_ev_n hn p hp0.le hp1 hn']
        have hcard : ((DA i).card : ℝ) = C := by rw [card_DA, hn']
        rw [hcard] at hsum
        have hwi : wgt n x y i = y := by unfold wgt; rw [if_neg h3]
        rw [hwi]
        have h1 : y ≤ Real.exp (-2 * ∑ j ∈ nbr N n i, wgt n x y j) := by
          rw [hydef]
          apply Real.exp_le_exp.mpr
          have : C * ((N : ℝ) * x + K * y) ≤ C * (p / 4) :=
            mul_le_mul_of_nonneg_left hQ (by linarith)
          nlinarith
        have h2 : (1 - p) ^ (n.choose 2) ≤ y * y := by
          calc (1 - p) ^ (n.choose 2) ≤ (Real.exp (-p)) ^ (n.choose 2) :=
                pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
            _ = Real.exp (-(p * C)) := by
                rw [← Real.exp_nat_mul]; congr 1; rw [hC]; ring
            _ = y * y := by
                rw [hydef, ← Real.exp_add]; congr 1; ring
        calc (1 - p) ^ (n.choose 2) ≤ y * y := h2
          _ ≤ y * ∏ j ∈ nbr N n i, (1 - wgt n x y j) :=
              mul_le_mul_of_nonneg_left (h1.trans hprod) hy0.le
    · rw [ev_eq_empty hg]
      simp only [FinProbSpace.prob, Finset.sum_empty]
      exact mul_nonneg (hwpos i).le hprodnn
  have hpos := lovasz_local_lemma_pos (μ := space N p hp0.le hp1) (E := ev N n) (N := nbr N n)
    (x := wgt n x y) hwpos hw1 hP (lllIndep p hp0.le hp1) Finset.univ
  have hne : (noneOf (ev N n) Finset.univ).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hpos
    simp [FinProbSpace.prob] at hpos
  obtain ⟨ω, hω⟩ := hne
  rw [mem_noneOf] at hω
  refine ⟨ω, fun X hX hsub => ?_, fun X hX hdis => ?_⟩
  · apply hω X (Finset.mem_univ _)
    unfold ev
    rw [if_pos hX]
    simpa using hsub
  · apply hω X (Finset.mem_univ _)
    unfold ev
    rw [if_neg (by omega), if_pos hX]
    simpa using hdis

end Existence

end RamseyLLL

end UndergradKB.Combinatorics
