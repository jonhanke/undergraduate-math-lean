import Mathlib.Analysis.Complex.ExponentialBounds
import UndergradKB.Combinatorics.Probability.RamseyLLL4
import UndergradKB.Common.Attr

/-!
# R(3,n) ≥ c n² / ln² n via the Local Lemma, part 5

The choice of parameters (`s = ⌊n / (40 ln n)⌋`, `N = s²`, `p = 1 / (4 s)`, so `p ≈ N^(-1/2)` and
`n p ≈ ln N`) and the verification of the hypotheses of `exists_edgeSet`; the final theorem.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace RamseyLLL

open ErdosGirth UndergradKB.Combinatorics.Probability

/-- Elementary size facts for `n ≥ 10^9`. -/
lemma size_facts (n : ℕ) (hn : 10 ^ 9 ≤ n) {L : ℝ} (hL : L = Real.log n) {s : ℕ}
    (hs : s = ⌊(n : ℝ) / (40 * L)⌋₊) :
    0 < L ∧ (n : ℝ) / (80 * L) ≤ s ∧ (s : ℝ) ≤ n / (40 * L) ∧ n ≤ s ^ 2 ∧ 1 ≤ s := by
  have hn' : (10 : ℝ) ^ 9 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set u : ℝ := Real.sqrt (Real.sqrt n) with hu
  have hu2 : u ^ 2 = Real.sqrt n := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu4 : u ^ 4 = n := by
    have : u ^ 4 = (u ^ 2) ^ 2 := by ring
    rw [this, hu2, Real.sq_sqrt hn0.le]
  have hsq : (25921 : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have hu161 : (161 : ℝ) ≤ u := by
    apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by
    rw [hL]; apply Real.log_pos; linarith
  have hLle : L ≤ 4 * u := by
    have h1 : L = 4 * Real.log u := by
      rw [hL, ← hu4, Real.log_pow]; norm_num
    have h2 := Real.log_le_sub_one_of_pos hu0
    rw [h1]; linarith
  set q : ℝ := (n : ℝ) / (40 * L) with hq
  have hq0 : 0 ≤ q := by positivity
  have hqge : u ^ 3 / 160 ≤ q := by
    rw [hq, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : u ^ 4 = n := hu4
    nlinarith [pow_pos hu0 3]
  have hs1 : (s : ℝ) ≤ q := by rw [hs]; exact Nat.floor_le hq0
  have hs2 : q < s + 1 := by rw [hs]; exact Nat.lt_floor_add_one q
  have hsu : u ^ 2 < s := by
    have : u ^ 3 ≥ 160 * u ^ 2 + 160 := by nlinarith [pow_pos hu0 2]
    linarith
  have hnl : 80 * L ≤ n := by
    have : (n : ℝ) = u ^ 4 := hu4.symm
    nlinarith [pow_pos hu0 3, pow_pos hu0 2]
  refine ⟨hL0, ?_, hs1, ?_, ?_⟩
  · have : (n : ℝ) / (80 * L) = q / 2 := by rw [hq]; field_simp; ring
    rw [this]
    have h1 : (1 : ℝ) ≤ q / 2 := by
      have hu3 : (320 : ℝ) ≤ u ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num) hu161 3
        nlinarith
      linarith
    linarith
  · have h1 : (n : ℝ) ≤ (s : ℝ) ^ 2 := by
      calc (n : ℝ) = (u ^ 2) ^ 2 := by rw [← hu4]; ring
        _ ≤ (s : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsu.le 2
    exact_mod_cast h1
  · have : (1 : ℝ) ≤ s := by nlinarith
    exact_mod_cast this

/-- The numerical hypotheses of `exists_edgeSet` hold for the chosen parameters. -/
lemma hyps (n : ℕ) (hn : 10 ^ 9 ≤ n) {L : ℝ} (hL : L = Real.log n) {s : ℕ}
    (hs : s = ⌊(n : ℝ) / (40 * L)⌋₊) :
    4 ≤ n ∧ n ≤ s ^ 2 ∧ 0 < 1 / (4 * (s : ℝ)) ∧ 1 / (4 * (s : ℝ)) ≤ 1 / 3 ∧
    ((s ^ 2 : ℕ) : ℝ) * (1 / (4 * (s : ℝ))) ^ 2 ≤ 1 / 16 ∧
    8 * ((s ^ 2).choose (n - 2) : ℝ) * Real.exp (-(1 / (4 * (s : ℝ)) * (n.choose 2 : ℝ)) / 2) ≤
      1 / (4 * (s : ℝ)) := by
  obtain ⟨hL0, hs80, hs40, hns, hs1⟩ := size_facts n hn hL hs
  have hn' : (10 : ℝ) ^ 9 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hspos : (0 : ℝ) < s := by linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    linarith
  refine ⟨by omega, hns, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · push_cast
    field_simp
    norm_num
  · -- the main estimate
    have hn3 : 3 ≤ n := by omega
    clear hn' hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    simp only [Nat.add_sub_cancel]
    set nR : ℝ := ((k + 2 : ℕ) : ℝ) with hnR
    have hs40' : (s : ℝ) * (40 * L) ≤ nR := by
      rwa [le_div_iff₀ (by positivity)] at hs40
    have hsn : (s : ℝ) ≤ nR := by nlinarith
    set p : ℝ := 1 / (4 * (s : ℝ)) with hp
    have hp_ge : 1 / nR ≤ p := by
      rw [hp]; apply one_div_le_one_div_of_le (by positivity); nlinarith
    -- the exponent
    have hC : ((k + 2).choose 2 : ℝ) = nR * (nR - 1) / 2 := by
      rw [Nat.cast_choose_two]
    have ht : ((2 * k + 3 : ℕ) : ℝ) * L ≤ p * ((k + 2).choose 2 : ℝ) / 2 := by
      rw [hC, hp]
      have : 1 / (4 * (s : ℝ)) * (nR * (nR - 1) / 2) / 2 = nR * (nR - 1) / (16 * s) := by
        field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      have hnk : nR = (k : ℝ) + 2 := by rw [hnR]; push_cast; ring
      push_cast
      rw [hnk] at hs40' ⊢
      nlinarith
    have hexp : nR ^ (2 * k + 3) ≤ Real.exp (p * ((k + 2).choose 2 : ℝ) / 2) := by
      calc nR ^ (2 * k + 3) = Real.exp (((2 * k + 3 : ℕ) : ℝ) * L) := by
            rw [Real.exp_nat_mul, hL, Real.exp_log hn0]
        _ ≤ _ := Real.exp_le_exp.mpr ht
    have hK : ((s ^ 2).choose k : ℝ) ≤ nR ^ (2 * k) := by
      calc ((s ^ 2).choose k : ℝ) ≤ (((s ^ 2 : ℕ)) : ℝ) ^ k := by
            exact_mod_cast Nat.choose_le_pow (s ^ 2) k
        _ = ((s : ℝ) ^ 2) ^ k := by push_cast; rfl
        _ ≤ (nR ^ 2) ^ k := by
            apply pow_le_pow_left₀ (by positivity)
            exact pow_le_pow_left₀ (by positivity) hsn 2
        _ = nR ^ (2 * k) := by rw [← pow_mul]
    have hnR8 : (8 : ℝ) ≤ nR ^ 2 := by nlinarith
    have hnRk : (0 : ℝ) < nR ^ (2 * k) := by positivity
    have hneg : Real.exp (-(p * ((k + 2).choose 2 : ℝ)) / 2) =
        (Real.exp (p * ((k + 2).choose 2 : ℝ) / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hneg]
    have hE := Real.exp_pos (p * ((k + 2).choose 2 : ℝ) / 2)
    rw [mul_inv_le_iff₀ hE]
    calc 8 * ((s ^ 2).choose k : ℝ) ≤ 8 * nR ^ (2 * k) := by linarith
      _ ≤ nR ^ 2 * nR ^ (2 * k) := by nlinarith
      _ = nR ^ (2 * k + 3) * (1 / nR) := by
          field_simp
          ring
      _ ≤ Real.exp (p * ((k + 2).choose 2 : ℝ) / 2) * p := by
          apply mul_le_mul hexp hp_ge (by positivity) hE.le
      _ = p * Real.exp (p * ((k + 2).choose 2 : ℝ) / 2) := by ring

/-- From an edge set without triangles and without independent `n`-sets to a graph with these
properties on any smaller number of vertices. -/
lemma graph_of_edgeSet {N n M : ℕ} (hM : M ≤ N) (ω : Finset (Sym2 (Fin N)))
    (h3 : ∀ X : Finset (Fin N), X.card = 3 → ¬ DA X ⊆ ω)
    (hn : ∀ X : Finset (Fin N), X.card = n → ¬ Disjoint ω (DA X)) :
    ∃ G : SimpleGraph (Fin M), G.CliqueFree 3 ∧
      ∀ A : Finset (Fin M), A.card = n → ¬ G.IsIndepSet (A : Set (Fin M)) := by
  classical
  let f : Fin M ↪ Fin N := ⟨Fin.castLE hM, Fin.castLE_injective hM⟩
  refine ⟨(graphOf ω).comap f, ?_, ?_⟩
  · intro t ht
    obtain ⟨hcl, hcard⟩ := ht
    apply h3 (t.map f) (by rw [Finset.card_map, hcard])
    intro e he
    obtain ⟨u, v, huv, rfl, hu, hv⟩ := exists_of_mem_DA he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
    have hne : a ≠ b := fun h => huv (by rw [h])
    exact (hcl ha hb hne).2
  · intro A hA hind
    obtain ⟨e, he1, he2⟩ := Finset.not_disjoint_iff.mp (hn (A.map f) (by rw [Finset.card_map, hA]))
    obtain ⟨u, v, huv, rfl, hu, hv⟩ := exists_of_mem_DA he2
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
    have hne : a ≠ b := fun h => huv (by rw [h])
    exact hind ha hb hne ⟨huv, he1⟩

end RamseyLLL

open RamseyLLL in
/-- CO-266. **Lower bound for `R(3, n)` by the Local Lemma** (Keller–Trotter, text pp. 352–353):
for all sufficiently large `n` there is a graph on `⌊n² / (6400 (ln n)²)⌋` vertices with no triangle
and no independent set of `n` vertices; that is, `R(3, n) > n² / (6400 ln² n)`, so
`R(3, n) ≥ c n² / ln² n` with `c = 1/6400`.  The graph is found as a random graph `G(N, p)` with
`N = s²`, `s = ⌊n / (40 ln n)⌋` and `p = 1/(4 s)`, using the asymmetric Local Lemma for the
triangle events and the independent-set events. -/
@[kb "kellertrotter2017" "text, p. 352"]
theorem ramsey_three_lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ G : SimpleGraph (Fin ⌊(n : ℝ) ^ 2 / (6400 * (Real.log n) ^ 2)⌋₊), G.CliqueFree 3 ∧
        ∀ A : Finset (Fin ⌊(n : ℝ) ^ 2 / (6400 * (Real.log n) ^ 2)⌋₊), A.card = n →
          ¬ G.IsIndepSet (A : Set (Fin ⌊(n : ℝ) ^ 2 / (6400 * (Real.log n) ^ 2)⌋₊)) := by
  refine ⟨10 ^ 9, fun n hn => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = ⌊(n : ℝ) / (40 * L)⌋₊ := ⟨_, rfl⟩
  obtain ⟨h4, hns, hp0, hp3, hNp, hK⟩ := hyps n hn hL hs
  obtain ⟨hL0, hs80, -, -, -⟩ := size_facts n hn hL hs
  obtain ⟨ω, hω3, hωn⟩ := exists_edgeSet (N := s ^ 2) (n := n) h4 hns hp0 hp3 hNp hK
  have hM : ⌊(n : ℝ) ^ 2 / (6400 * (Real.log n) ^ 2)⌋₊ ≤ s ^ 2 := by
    apply Nat.floor_le_of_le
    rw [← hL]
    have h1 : ((n : ℝ) / (80 * L)) ^ 2 ≤ (s : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs80 2
    have h2 : ((n : ℝ) / (80 * L)) ^ 2 = (n : ℝ) ^ 2 / (6400 * L ^ 2) := by
      field_simp; ring
    push_cast
    linarith
  exact graph_of_edgeSet hM ω hω3 hωn

end UndergradKB.Combinatorics
