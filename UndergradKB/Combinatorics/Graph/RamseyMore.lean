import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Mathlib.Topology.DiscreteSubset
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Ramsey

/-!
# Ramsey's theorem for `s`-subsets, van der Waerden, and the numerical Erdős bound
(Keller–Trotter, Theorems 11.4, 11.6 and 16.13)
-/

namespace UndergradKB.Combinatorics

open Finset

section GeneralRamsey

variable {α : Type*}

/-- Two-colour Ramsey theorem for `s`-subsets (colours: `φ S` true / false). -/
theorem ramsey_two_colours (s : ℕ) :
    ∀ a b : ℕ, ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ φ : Finset α → Prop,
      (∃ H ⊆ X, H.card = a ∧ ∀ S ⊆ H, S.card = s → φ S) ∨
      (∃ H ⊆ X, H.card = b ∧ ∀ S ⊆ H, S.card = s → ¬ φ S) := by
  classical
  induction s with
  | zero =>
    intro a b
    refine ⟨max a b, fun X hX φ => ?_⟩
    by_cases h : φ ∅
    · obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq (le_trans (le_max_left a b) hX)
      refine Or.inl ⟨H, hH, hc, fun S hS hc0 => ?_⟩
      rw [Finset.card_eq_zero.1 hc0] at *; exact h
    · obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq (le_trans (le_max_right a b) hX)
      refine Or.inr ⟨H, hH, hc, fun S hS hc0 => ?_⟩
      rw [Finset.card_eq_zero.1 hc0]; exact h
  | succ s ih =>
    intro a b
    induction' hab : a + b using Nat.strong_induction_on with m IH generalizing a b
    by_cases ha : a < s + 1
    · refine ⟨a, fun X hX φ => ?_⟩
      obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq hX
      refine Or.inl ⟨H, hH, hc, fun S hS hc0 => ?_⟩
      have := Finset.card_le_card hS
      omega
    by_cases hb : b < s + 1
    · refine ⟨b, fun X hX φ => ?_⟩
      obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq hX
      refine Or.inr ⟨H, hH, hc, fun S hS hc0 => ?_⟩
      have := Finset.card_le_card hS
      omega
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨Na, hNa⟩ := IH (a' + (b' + 1)) (by omega) a' (b' + 1) rfl
    obtain ⟨Nb, hNb⟩ := IH (a' + 1 + b') (by omega) (a' + 1) b' rfl
    obtain ⟨M, hM⟩ := ih Na Nb
    refine ⟨M + 1, fun X hX φ => ?_⟩
    have hXne : X.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨x, hx⟩ := hXne
    have hcard : M ≤ (X.erase x).card := by
      rw [Finset.card_erase_of_mem hx]; omega
    rcases hM (X.erase x) hcard (fun S => φ (insert x S)) with ⟨H, hH, hHc, hHφ⟩ | ⟨H, hH, hHc, hHφ⟩
    · -- all s-subsets S of H have φ (insert x S)
      have hxH : x ∉ H := fun h => by simpa using hH h
      rcases hNa H (by omega) φ with ⟨H', hH', hc', hφ'⟩ | ⟨H', hH', hc', hφ'⟩
      · refine Or.inl ⟨insert x H', ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hx
          · exact Finset.mem_of_mem_erase (hH (hH' hy))
        · rw [Finset.card_insert_of_notMem (fun h => hxH (hH' h)), hc']
        · intro S hS hSc
          by_cases hxS : x ∈ S
          · have hS' : S.erase x ⊆ H' := by
              intro y hy
              have := hS (Finset.mem_of_mem_erase hy)
              rcases Finset.mem_insert.1 this with h | h
              · exact absurd h (Finset.ne_of_mem_erase hy)
              · exact h
            have := hHφ (S.erase x) (hS'.trans hH') (by rw [Finset.card_erase_of_mem hxS]; omega)
            rwa [Finset.insert_erase hxS] at this
          · exact hφ' S (fun y hy => by
              rcases Finset.mem_insert.1 (hS hy) with rfl | h
              · exact absurd hy hxS
              · exact h) hSc
      · exact Or.inr ⟨H', hH'.trans (fun y hy => Finset.mem_of_mem_erase (hH hy)), hc', hφ'⟩
    · have hxH : x ∉ H := fun h => by simpa using hH h
      rcases hNb H (by omega) φ with ⟨H', hH', hc', hφ'⟩ | ⟨H', hH', hc', hφ'⟩
      · exact Or.inl ⟨H', hH'.trans (fun y hy => Finset.mem_of_mem_erase (hH hy)), hc', hφ'⟩
      · refine Or.inr ⟨insert x H', ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hx
          · exact Finset.mem_of_mem_erase (hH (hH' hy))
        · rw [Finset.card_insert_of_notMem (fun h => hxH (hH' h)), hc']
        · intro S hS hSc
          by_cases hxS : x ∈ S
          · have hS' : S.erase x ⊆ H' := by
              intro y hy
              have := hS (Finset.mem_of_mem_erase hy)
              rcases Finset.mem_insert.1 this with h | h
              · exact absurd h (Finset.ne_of_mem_erase hy)
              · exact h
            have := hHφ (S.erase x) (hS'.trans hH') (by rw [Finset.card_erase_of_mem hxS]; omega)
            rwa [Finset.insert_erase hxS] at this
          · exact hφ' S (fun y hy => by
              rcases Finset.mem_insert.1 (hS hy) with rfl | h
              · exact absurd hy hxS
              · exact h) hSc

/-- General Ramsey theorem, core form over arbitrary finite sets with colours `0, …, r-1`
(as natural numbers). -/
theorem ramsey_general_core (s r : ℕ) (h : ℕ → ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ φ : Finset α → ℕ,
      (∀ S ⊆ X, S.card = s → φ S < r) →
      ∃ i < r, ∃ H ⊆ X, H.card = h i ∧ ∀ S ⊆ H, S.card = s → φ S = i := by
  classical
  induction r generalizing h with
  | zero =>
    refine ⟨s, fun X hX φ hφ => ?_⟩
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hX
    exact absurd (hφ S hS hSc) (Nat.not_lt_zero _)
  | succ r ih =>
    obtain ⟨N', hN'⟩ := ih (fun i => h (i + 1))
    obtain ⟨N, hN⟩ := ramsey_two_colours (α := α) s (h 0) N'
    refine ⟨N, fun X hX φ hφ => ?_⟩
    rcases hN X hX (fun S => φ S = 0) with ⟨H, hH, hc, hφ0⟩ | ⟨H, hH, hc, hφ0⟩
    · exact ⟨0, Nat.succ_pos _, H, hH, hc, hφ0⟩
    · obtain ⟨i, hi, H', hH', hc', hφ'⟩ := hN' H (le_of_eq hc.symm) (fun S => φ S - 1)
        (fun S hS hSc => by
          have := hφ S (hS.trans hH) hSc
          have := hφ0 S hS hSc
          omega)
      refine ⟨i + 1, by omega, H', hH'.trans hH, hc', fun S hS hSc => ?_⟩
      have := hφ' S hS hSc
      have := hφ0 S (hS.trans hH') hSc
      omega

/-- CO-263. General Ramsey theorem (Keller–Trotter Theorem 11.6): given `s`, `r` and sizes
`h 0, …, h (r-1)`, there is `n₀` such that for every `n ≥ n₀` and every colouring `φ` of the
`s`-subsets of `[n] = {1,…,n}` with `r` colours, some colour `α` admits a set `H ⊆ [n]` of size
`h α` all of whose `s`-subsets get colour `α`. (The colouring is a function on all finsets of
`ℕ`; only its values on `s`-subsets of `[n]` matter. The book's hypothesis `h i ≥ s` is not
needed.) -/
@[kb "kellertrotter2017" "Theorem 11.6, p. 258"]
theorem ramsey_general (s r : ℕ) (h : Fin r → ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ φ : Finset ℕ → Fin r,
      ∃ α : Fin r, ∃ H ⊆ Finset.Icc 1 n, H.card = h α ∧
        ∀ S ⊆ H, S.card = s → φ S = α := by
  obtain ⟨N, hN⟩ := ramsey_general_core (α := ℕ) s r (fun i => if hi : i < r then h ⟨i, hi⟩ else 0)
  refine ⟨N, fun n hn φ => ?_⟩
  obtain ⟨i, hi, H, hH, hc, hφ⟩ := hN (Finset.Icc 1 n) (by simpa using hn)
    (fun S => (φ S : ℕ)) (fun S _ _ => (φ S).2)
  refine ⟨⟨i, hi⟩, H, hH, by simpa [hi] using hc, fun S hS hSc => ?_⟩
  exact Fin.ext (hφ S hS hSc)

end GeneralRamsey

section VanDerWaerden

/-- CO-264. A sequence `x₀, …, x_{t-1}` of natural numbers is an arithmetic progression of
length `t` if it has the form `a, a+d, …, a+(t-1)d` with common difference `d > 0`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) arithmetic progression, p. 349"]
def IsArithProg {t : ℕ} (x : Fin t → ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin t, x i = a + (i : ℕ) * d

/-- The set of colourings `ℕ → Fin r` with no monochromatic `t`-term progression inside
`{1,…,n}`. -/
def noMonoAP (r t n : ℕ) : Set (ℕ → Fin r) :=
  {c | ∀ a d : ℕ, 0 < d → 1 ≤ a → (∀ i : Fin t, a + (i : ℕ) * d ≤ n) →
    ∃ i : Fin t, c (a + (i : ℕ) * d) ≠ c a}

lemma isClosed_noMonoAP (r t n : ℕ) : IsClosed (noMonoAP r t n) := by
  have : noMonoAP r t n = ⋂ a : ℕ, ⋂ d : ℕ,
      ⋂ (_ : 0 < d ∧ 1 ≤ a ∧ ∀ i : Fin t, a + (i : ℕ) * d ≤ n),
        ⋃ i : Fin t, {c : ℕ → Fin r | c (a + (i : ℕ) * d) ≠ c a} := by
    ext c
    simp only [noMonoAP, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h a d ⟨h1, h2, h3⟩; exact h a d h1 h2 h3
    · intro h a d h1 h2 h3; exact h a d ⟨h1, h2, h3⟩
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun d => isClosed_iInter fun _ =>
    isClosed_iUnion_of_finite fun i => ?_
  have hc : Continuous (fun c : ℕ → Fin r => (c (a + (i : ℕ) * d), c a)) :=
    (continuous_apply _).prodMk (continuous_apply _)
  exact (isClosed_discrete {p : Fin r × Fin r | p.1 ≠ p.2}).preimage hc

/-- CO-265. Van der Waerden's theorem: for every number of colours `r` and length `t` there is
`n₀` such that for `n ≥ n₀` every `r`-colouring of `[n] = {1,…,n}` (given as a function on `ℕ`,
only its values on `[n]` matter) has a monochromatic arithmetic progression of length `t`
contained in `[n]`. Derived from Mathlib's Hales–Jewett-based `exists_mono_homothetic_copy`
by a compactness argument. -/
@[kb "kellertrotter2017" "Theorem 16.13, p. 349"]
theorem van_der_waerden (r t : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : ℕ → Fin r,
      ∃ x : Fin t → ℕ, IsArithProg x ∧ (∀ i, x i ∈ Finset.Icc 1 n) ∧ ∃ α : Fin r, ∀ i, c (x i) = α := by
  by_contra hcon
  push Not at hcon
  have hnon : ∀ n, (noMonoAP r t n).Nonempty := by
    intro n
    obtain ⟨m, hm, c, hc⟩ := hcon n
    refine ⟨c, fun a d hd ha hle => ?_⟩
    exact hc (fun i => a + (i : ℕ) * d) ⟨a, d, hd, fun i => rfl⟩
      (fun i => Finset.mem_Icc.2 ⟨by omega, (hle i).trans hm⟩) (c a)
  have hanti : ∀ n, noMonoAP r t (n + 1) ⊆ noMonoAP r t n := by
    intro n c hc a d hd ha hle
    exact hc a d hd ha (fun i => (hle i).trans (Nat.le_succ n))
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => noMonoAP r t n) hanti hnon (isClosed_noMonoAP r t 0).isCompact
    (isClosed_noMonoAP r t)
  obtain ⟨c, hc⟩ := hne
  rw [Set.mem_iInter] at hc
  obtain ⟨a, ha, b, col, hcol⟩ := Combinatorics.exists_mono_homothetic_copy
    (Finset.range t) (fun m => c (m + 1))
  obtain ⟨i, hi⟩ := hc (b + 1 + a * t) (b + 1) a ha (by omega) (by
    intro i
    have : (i : ℕ) * a ≤ t * a := Nat.mul_le_mul_right _ i.2.le
    nlinarith)
  have h0 : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.2 (by have := i.2; omega)
  have hi' : (i : ℕ) ∈ Finset.range t := Finset.mem_range.2 i.2
  have e0 := hcol 0 h0
  have e1 := hcol i hi'
  simp only [smul_eq_mul, mul_zero, zero_add] at e0 e1
  apply hi
  rw [show b + 1 + (i : ℕ) * a = a * i + b + 1 by ring, e1, ← e0]

end VanDerWaerden

section ErdosBound

open Real in
/-- Counting step for CO-262: if `N < (n/(e√2)) 2^(n/2)` then `2 C(N,n) < 2^C(n,2)`. -/
lemma two_mul_choose_lt (n N : ℕ) (hn : 1 ≤ n)
    (hN : (N : ℝ) < n / (exp 1 * √2) * (2 : ℝ) ^ ((n : ℝ) / 2)) :
    2 * N.choose n < 2 ^ n.choose 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < exp 1 := exp_pos 1
  have hs2 : 0 < √2 := by positivity
  set S : ℝ := √(2 * π * n) with hS
  have hS2 : 2 < S := by
    rw [hS]
    apply Real.lt_sqrt_of_sq_lt
    have := Real.pi_gt_three
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hSpos : 0 < S := by linarith
  have hfac : S * (n / exp 1) ^ n ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  set u : ℝ := (2 : ℝ) ^ ((n : ℝ) / 2) with hu_def
  have hu0 : 0 < u := by positivity
  set w : ℝ := exp 1 * N / n with hw
  have hw0 : 0 ≤ w := by positivity
  have hu : u ^ 2 = 2 ^ n := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = n := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have key : (N : ℝ) * (exp 1 * √2) < n * u := by
    have h := mul_lt_mul_of_pos_right hN (mul_pos he hs2)
    have e : (n : ℝ) / (exp 1 * √2) * u * (exp 1 * √2) = n * u := by field_simp
    linarith
  have hlt : w * √2 < u := by
    rw [hw, div_mul_eq_mul_div, div_lt_iff₀ hnpos]
    linarith
  have hw2 : w ^ 2 ≤ 2 ^ (n - 1) := by
    have h1 : (w * √2) ^ 2 < u ^ 2 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    rw [mul_pow, Real.sq_sqrt (by norm_num), hu] at h1
    have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  have hC : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hwn : w ^ n ≤ 2 ^ n.choose 2 := by
    refine le_of_pow_le_pow_left₀ (two_ne_zero) (by positivity) ?_
    calc (w ^ n) ^ 2 = (w ^ 2) ^ n := by ring
      _ ≤ ((2 : ℝ) ^ (n - 1)) ^ n := pow_le_pow_left₀ (by positivity) hw2 n
      _ = (2 : ℝ) ^ (n * (n - 1)) := by rw [← pow_mul]; ring_nf
      _ = ((2 : ℝ) ^ n.choose 2) ^ 2 := by rw [← pow_mul, mul_comm (n.choose 2) 2, hC, mul_comm]
  have hch : (N.choose n : ℝ) ≤ w ^ n / S := by
    refine (Nat.choose_le_pow_div n N).trans ?_
    have hfpos : 0 < S * (n / exp 1) ^ n := by positivity
    calc (N : ℝ) ^ n / n.factorial ≤ (N : ℝ) ^ n / (S * (n / exp 1) ^ n) :=
          div_le_div_of_nonneg_left (by positivity) hfpos hfac
      _ = w ^ n / S := by
          rw [hw]
          field_simp
          rw [← mul_pow]
          congr 1
          field_simp
  have h2pos : (0 : ℝ) < 2 ^ n.choose 2 := by positivity
  have : (2 * N.choose n : ℝ) < 2 ^ n.choose 2 := by
    have h3 : (w ^ n) / S ≤ 2 ^ n.choose 2 / S := div_le_div_of_nonneg_right hwn hSpos.le
    have h4 : 2 * (2 ^ n.choose 2 / S) < 2 ^ n.choose 2 := by
      rw [← mul_div_assoc, div_lt_iff₀ hSpos]
      nlinarith
    linarith
  exact_mod_cast this

open Real in
/-- CO-262. Erdős' lower bound `R(n,n) ≥ (n/(e√2)) 2^(n/2)` (for `n ≥ 1`), derived from the
counting form of the argument via Stirling's inequality `n! ≥ √(2πn) (n/e)^n`. -/
@[kb "kellertrotter2017" "Theorem 11.4, p. 256"]
theorem ramseyNumber_diag_ge (n : ℕ) (hn : 1 ≤ n) :
    n / (exp 1 * √2) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (ramseyNumber n n : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact not_ramseyProp_of_counting _ _ (two_mul_choose_lt n _ hn hlt)
    (ramseyNumber_le n n hn hn).1

end ErdosBound


end UndergradKB.Combinatorics
