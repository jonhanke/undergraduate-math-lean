import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Combinatorics.AeqB.GosperForm

/-!
# Step 2 of Gosper's algorithm (Petkovsek–Wilf–Zeilberger, "A = B", Section 5.3)

The iterative construction of `a, b, c` from `r = Z f / g` by successive gcd-cancellation along the
nonnegative integer zeros `h_1 < ... < h_N` of the resultant `Res_n(f(n), g(n+h))`, its
correctness (Proposition 5.3.1, properties (5.2.3) and (i)-(iii)), the minimality of the degree
of `c` (Corollary 5.3.2) and the elementary fact behind the factorization-based alternative.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-! ### The construction -/

open Classical in
/-- One pass of Step 2.2 with shift `k`: `s = gcd(p(n), q(n+k))`, then `p ↦ p / s(n)` and
`q ↦ q / s(n-k)`. -/
noncomputable def gosperStep (k : ℕ) (pq : K[X] × K[X]) : K[X] × K[X] :=
  (pq.1 / GCDMonoid.gcd pq.1 (pq.2.comp (X + C (k : K))),
   pq.2 / (GCDMonoid.gcd pq.1 (pq.2.comp (X + C (k : K)))).comp (X + C (-(k : K))))

/-- CO-402. The pairs `(p_j, q_j)` of Step 2.2 for the shifts `h_1, h_2, …` (here `hs 0, hs 1, …`):
`(p_0, q_0) = (f, g)`, `s_j = gcd(p_{j-1}(n), q_{j-1}(n + h_j))`, `p_j = p_{j-1}/s_j(n)`,
`q_j = q_{j-1} / s_j(n - h_j)`. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 2.2), p. 90"]
noncomputable def gosperStage (f g : K[X]) (hs : ℕ → ℕ) : ℕ → K[X] × K[X]
  | 0 => (f, g)
  | j + 1 => gosperStep (hs j) (gosperStage f g hs j)

open Classical in
/-- CO-402. The gcd `s_{j+1} = gcd(p_j(n), q_j(n + h_{j+1}))` used in pass `j + 1`. -/
noncomputable def gosperShiftGcd (f g : K[X]) (hs : ℕ → ℕ) (j : ℕ) : K[X] :=
  GCDMonoid.gcd (gosperStage f g hs j).1 ((gosperStage f g hs j).2.comp (X + C (hs j : K)))

/-- CO-402. The polynomial `c(n) = ∏_{i=1}^N ∏_{j=1}^{h_i} s_i(n - j)` of Step 2.2. -/
noncomputable def gosperStep2C (f g : K[X]) (hs : ℕ → ℕ) (N : ℕ) : K[X] :=
  ∏ i ∈ Finset.range N, gosperQ (gosperShiftGcd f g hs i) (hs i)

open Classical in
theorem gosperStep_spec {pq : K[X] × K[X]} (_hp : pq.1 ≠ 0) (hq : pq.2 ≠ 0) (k : ℕ) :
    ∃ s : K[X], s = GCDMonoid.gcd pq.1 (pq.2.comp (X + C (k : K))) ∧ s ≠ 0 ∧
      s ∣ pq.2.comp (X + C (k : K)) ∧
      (gosperStep k pq).1 * s = pq.1 ∧
      (gosperStep k pq).2 * s.comp (X + C (-(k : K))) = pq.2 ∧
      IsCoprime (gosperStep k pq).1 ((gosperStep k pq).2.comp (X + C (k : K))) := by
  have hq1 : pq.2.comp (X + C (k : K)) ≠ 0 := comp_X_add_C_ne_zero' hq _
  have hs0 : GCDMonoid.gcd pq.1 (pq.2.comp (X + C (k : K))) ≠ 0 := gcd_ne_zero_of_right hq1
  set s := GCDMonoid.gcd pq.1 (pq.2.comp (X + C (k : K))) with hs
  have hsp : s ∣ pq.1 := gcd_dvd_left _ _
  have hsq : s ∣ pq.2.comp (X + C (k : K)) := gcd_dvd_right _ _
  have hT0 : s.comp (X + C (-(k : K))) ≠ 0 := comp_X_add_C_ne_zero' hs0 _
  have hTq : s.comp (X + C (-(k : K))) ∣ pq.2 := by
    have := dvd_comp_shift hsq (-(k : K))
    rwa [comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at this
  have e1 : (gosperStep k pq).1 * s = pq.1 := by
    show pq.1 / s * s = pq.1
    rw [mul_comm]; exact EuclideanDomain.mul_div_cancel' hs0 hsp
  have e2 : (gosperStep k pq).2 * s.comp (X + C (-(k : K))) = pq.2 := by
    show pq.2 / s.comp (X + C (-(k : K))) * s.comp (X + C (-(k : K))) = pq.2
    rw [mul_comm]; exact EuclideanDomain.mul_div_cancel' hT0 hTq
  refine ⟨s, rfl, hs0, hsq, e1, e2, ?_⟩
  have e3 : (gosperStep k pq).2.comp (X + C (k : K)) = pq.2.comp (X + C (k : K)) / s := by
    have := congrArg (fun r => r.comp (X + C (k : K))) e2
    simp only [mul_comp, comp_shift_comp_shift, neg_add_cancel, C_0, add_zero, comp_X] at this
    exact EuclideanDomain.eq_div_of_mul_eq_left hs0 this
  rw [e3]
  exact isCoprime_div_gcd_div_gcd hq1

section Stage

variable {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hs : ℕ → ℕ)
include hf hg

theorem gosperStage_ne_zero : ∀ j, (gosperStage f g hs j).1 ≠ 0 ∧ (gosperStage f g hs j).2 ≠ 0 := by
  intro j
  induction j with
  | zero => exact ⟨hf, hg⟩
  | succ j ih =>
    obtain ⟨s, -, hs0, -, e1, e2, -⟩ := gosperStep_spec ih.1 ih.2 (hs j)
    have hT0 : s.comp (X + C (-(hs j : K))) ≠ 0 := comp_X_add_C_ne_zero' hs0 _
    have hP : (gosperStage f g hs (j + 1)).1 * s ≠ 0 := by
      show (gosperStep (hs j) (gosperStage f g hs j)).1 * s ≠ 0
      rw [e1]; exact ih.1
    have hQ : (gosperStage f g hs (j + 1)).2 * s.comp (X + C (-(hs j : K))) ≠ 0 := by
      show (gosperStep (hs j) (gosperStage f g hs j)).2 * s.comp (X + C (-(hs j : K))) ≠ 0
      rw [e2]; exact ih.2
    exact ⟨left_ne_zero_of_mul hP, left_ne_zero_of_mul hQ⟩

/-- The facts about pass `j + 1` used throughout. -/
theorem gosperStage_succ_spec (j : ℕ) :
    ∃ s : K[X], s = gosperShiftGcd f g hs j ∧ s ≠ 0 ∧
      s ∣ (gosperStage f g hs j).2.comp (X + C (hs j : K)) ∧
      (gosperStage f g hs (j + 1)).1 * s = (gosperStage f g hs j).1 ∧
      (gosperStage f g hs (j + 1)).2 * s.comp (X + C (-(hs j : K))) = (gosperStage f g hs j).2 ∧
      IsCoprime (gosperStage f g hs (j + 1)).1
        ((gosperStage f g hs (j + 1)).2.comp (X + C (hs j : K))) :=
  gosperStep_spec (gosperStage_ne_zero hf hg hs j).1 (gosperStage_ne_zero hf hg hs j).2 (hs j)

theorem gosperStage_fst_dvd_of_le {i i' : ℕ} (h : i ≤ i') :
    (gosperStage f g hs i').1 ∣ (gosperStage f g hs i).1 := by
  induction i', h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ i' _ ih =>
    obtain ⟨s, -, -, -, e1, -⟩ := gosperStage_succ_spec hf hg hs i'
    exact (Dvd.intro _ e1).trans ih

theorem gosperStage_snd_dvd_of_le {i i' : ℕ} (h : i ≤ i') :
    (gosperStage f g hs i').2 ∣ (gosperStage f g hs i).2 := by
  induction i', h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ i' _ ih =>
    obtain ⟨s, -, -, -, -, e2, -⟩ := gosperStage_succ_spec hf hg hs i'
    exact (Dvd.intro _ e2).trans ih

/-- Equation (5.2.3) at every stage: `f (q_N c_N) = g (p_N c_N(n+1))`. -/
theorem gosperStage_identity (N : ℕ) :
    f * ((gosperStage f g hs N).2 * gosperStep2C f g hs N)
      = g * ((gosperStage f g hs N).1 * (gosperStep2C f g hs N).comp (X + 1)) := by
  induction N with
  | zero =>
    simp only [gosperStage, gosperStep2C, Finset.range_zero, Finset.prod_empty, mul_one, one_comp]
    exact mul_comm _ _
  | succ N ih =>
    obtain ⟨s, hsdef, hs0, -, e1, e2, -⟩ := gosperStage_succ_spec hf hg hs N
    have hT0 : s.comp (X + C (-(hs N : K))) ≠ 0 := comp_X_add_C_ne_zero' hs0 _
    have F1 := gosperR_mul s (hs N)
    have hC : gosperStep2C f g hs (N + 1)
        = gosperStep2C f g hs N * gosperQ s (hs N) := by
      unfold gosperStep2C
      rw [Finset.prod_range_succ, ← hsdef]
    have IH' : f * ((gosperStage f g hs (N + 1)).2 * s.comp (X + C (-(hs N : K)))
        * gosperStep2C f g hs N)
        = g * ((gosperStage f g hs (N + 1)).1 * s * (gosperStep2C f g hs N).comp (X + 1)) := by
      rw [e1, e2]; exact ih
    rw [hC, mul_comp, gosperQ_comp]
    apply mul_left_cancel₀ hT0
    linear_combination gosperQ s (hs N) * IH'
      - (g * (gosperStage f g hs (N + 1)).1 * (gosperStep2C f g hs N).comp (X + 1)) * F1

theorem gosperStage_coprime_aux (N : ℕ)
    (hcov : ∀ k : ℕ, ¬ IsCoprime f (g.comp (X + C (k : K))) → ∃ m < N, hs m = k) :
    ∀ k, k ≤ N → ∀ i j, k ≤ i → i ≤ N → k ≤ j → j ≤ N → ∀ h : ℕ,
      (∀ m, k ≤ m → m < N → h ≠ hs m) →
      IsCoprime (gosperStage f g hs i).1 ((gosperStage f g hs j).2.comp (X + C (h : K))) := by
  intro k
  induction k with
  | zero =>
    intro _ i j _ _ _ _ h hh
    have hc : IsCoprime f (g.comp (X + C (h : K))) := by
      by_contra hnc
      obtain ⟨m, hm, e⟩ := hcov h hnc
      exact hh m (Nat.zero_le _) hm e.symm
    exact (hc.of_isCoprime_of_dvd_left
      (gosperStage_fst_dvd_of_le hf hg hs (Nat.zero_le i))).of_isCoprime_of_dvd_right
      (dvd_comp_shift (gosperStage_snd_dvd_of_le hf hg hs (Nat.zero_le j)) _)
  | succ k ih =>
    intro hk i j hki hiN hkj hjN h hh
    by_cases hhk : h = hs k
    · subst hhk
      obtain ⟨s, -, -, -, -, -, hcop⟩ := gosperStage_succ_spec hf hg hs k
      exact (hcop.of_isCoprime_of_dvd_left
        (gosperStage_fst_dvd_of_le hf hg hs hki)).of_isCoprime_of_dvd_right
        (dvd_comp_shift (gosperStage_snd_dvd_of_le hf hg hs hkj) _)
    · refine ih (by omega) i j (by omega) hiN (by omega) hjN h fun m hkm hmN => ?_
      rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
      · exact hhk
      · exact hh m hlt hmN

theorem gosperStage_cover (N : ℕ)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k) :
    ∀ k : ℕ, ¬ IsCoprime f (g.comp (X + C (k : K))) → ∃ m < N, hs m = k :=
  fun k hk => hS k ((resultant_shift_eq_zero_iff (Or.inl hf) _).2 hk)

/-- CO-403. Proposition 5.3.1 (shifts `h` which are not among the later shifts).  For
`k ≤ i, j ≤ N` and `h ∈ ℕ` different from all of `h_{k+1}, …, h_N`: `gcd(p_i(n), q_j(n+h)) = 1`. -/
theorem gosperStage_coprime (N : ℕ)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k)
    {k i j h : ℕ} (hkN : k ≤ N) (hki : k ≤ i) (hiN : i ≤ N) (hkj : k ≤ j) (hjN : j ≤ N)
    (hh : ∀ m, k ≤ m → m < N → h ≠ hs m) :
    IsCoprime (gosperStage f g hs i).1 ((gosperStage f g hs j).2.comp (X + C (h : K))) :=
  gosperStage_coprime_aux hf hg hs N (gosperStage_cover hf hg hs N hS) k hkN i j hki hiN hkj hjN h hh

/-- CO-403. Proposition 5.3.1 in the book's form: if `h_1 < h_2 < … < h_N` (here `hs 0 < hs 1 < …`),
`0 ≤ k ≤ i, j ≤ N`, `h ∈ ℕ` and `h < h_{k+1}` (no condition when `k = N`, where `h_{N+1} = ∞`),
then `gcd(p_i(n), q_j(n+h)) = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.3.1, p. 91"]
theorem gosper_prop_5_3_1 (N : ℕ) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k)
    {k i j h : ℕ} (hkN : k ≤ N) (hki : k ≤ i) (hiN : i ≤ N) (hkj : k ≤ j) (hjN : j ≤ N)
    (hh : k < N → h < hs k) :
    IsCoprime (gosperStage f g hs i).1 ((gosperStage f g hs j).2.comp (X + C (h : K))) :=
  gosperStage_coprime hf hg hs N hS hkN hki hiN hkj hjN fun m hkm hmN =>
    ne_of_lt (lt_of_lt_of_le (hh (by omega)) (hmono.monotone hkm))

theorem gosperShiftGcd_monic (j : ℕ) : (gosperShiftGcd f g hs j).Monic := by
  classical
  obtain ⟨s, hsdef, hs0, -⟩ := gosperStage_succ_spec hf hg hs j
  have h0 : gosperShiftGcd f g hs j ≠ 0 := hsdef ▸ hs0
  have := monic_normalize h0
  unfold gosperShiftGcd at this ⊢
  rwa [normalize_gcd] at this

theorem gosperStep2C_monic (N : ℕ) : (gosperStep2C f g hs N).Monic :=
  monic_prod_of_monic _ _ fun i _ =>
    monic_prod_of_monic _ _ fun _ _ => monic_comp_shift (gosperShiftGcd_monic hf hg hs i) _

theorem gosperStage_snd_monic (hgm : g.Monic) (N : ℕ) : (gosperStage f g hs N).2.Monic := by
  induction N with
  | zero => exact hgm
  | succ N ih =>
    obtain ⟨s, hsdef, -, -, -, e2, -⟩ := gosperStage_succ_spec hf hg hs N
    have hsm : s.Monic := hsdef ▸ gosperShiftGcd_monic hf hg hs N
    refine Monic.of_mul_monic_right (q := s.comp (X + C (-(hs N : K)))) (monic_comp_shift hsm _) ?_
    rw [e2]; exact ih

/-- CO-402 (correctness of Step 2, equation (5.2.3) and property (i)). Let `f, g ≠ 0`, let
`hs 0, …, hs (N-1)` list (a superset of) the nonnegative integer zeros of `h ↦ Res_n(f(n), g(n+h))`
and put `a = Z p_N`, `b = q_N`, `c = ∏_i ∏_{j=1}^{h_i} s_i(n-j)`. Then
`Z f(n) b(n) c(n) = g(n) a(n) c(n+1)`  (i.e. `Z f/g = a c(n+1)/(b c)`) and
`gcd(a(n), b(n+h)) = 1` for every `h ∈ ℕ`.  Moreover `c` is monic, and `b` is monic when `g` is. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 2), p. 90"]
theorem gosper_step2_spec (N : ℕ) (Z : K) (hZ : Z ≠ 0)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k) :
    C Z * f * ((gosperStage f g hs N).2 * gosperStep2C f g hs N)
      = g * ((C Z * (gosperStage f g hs N).1) * (gosperStep2C f g hs N).comp (X + 1)) ∧
    (∀ h : ℕ, IsCoprime (C Z * (gosperStage f g hs N).1)
      ((gosperStage f g hs N).2.comp (X + C (h : K)))) ∧
    (gosperStep2C f g hs N).Monic ∧ (g.Monic → (gosperStage f g hs N).2.Monic) := by
  have hu : IsUnit (C Z : K[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 hZ)
  refine ⟨?_, fun h => ?_, gosperStep2C_monic hf hg hs N, fun hgm => gosperStage_snd_monic hf hg hs hgm N⟩
  · linear_combination C Z * gosperStage_identity hf hg hs N
  · rw [isCoprime_mul_unit_left_left hu]
    exact gosperStage_coprime hf hg hs N hS le_rfl le_rfl le_rfl le_rfl le_rfl
      fun m hm hmN => absurd hmN (by omega)

/-- CO-402 / CO-404 (properties (ii) and (iii) of Theorem 5.3.1 for the output of Step 2, when the
shifts are taken in increasing order). -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.3.1, p. 92"]
theorem gosper_step2_coprime (N : ℕ) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k) :
    IsCoprime (gosperStage f g hs N).1 (gosperStep2C f g hs N) ∧
      IsCoprime (gosperStage f g hs N).2 ((gosperStep2C f g hs N).comp (X + 1)) := by
  constructor
  · unfold gosperStep2C
    refine IsCoprime.prod_right fun i hi => ?_
    have hiN : i < N := Finset.mem_range.1 hi
    unfold gosperQ
    refine IsCoprime.prod_right fun j hj => ?_
    have hj' : j < hs i := Finset.mem_range.1 hj
    obtain ⟨s, hsdef, hs0, hsq, -, e2, -⟩ := gosperStage_succ_spec hf hg hs i
    have hcast : ((hs i : ℕ) : K) + -((j : K) + 1) = ((hs i - 1 - j : ℕ) : K) := by
      rw [show hs i - 1 - j = hs i - (j + 1) by omega, Nat.cast_sub (by omega)]
      push_cast; ring
    have hcast2 : -((hs i : ℕ) : K) + ((hs i - 1 - j : ℕ) : K) = -((j : K) + 1) := by
      rw [← hcast]; ring
    have hT : (s.comp (X + C (-(hs i : K)))).comp (X + C ((hs i - 1 - j : ℕ) : K))
        = s.comp (X + C (-((j : K) + 1))) := by
      rw [comp_shift_comp_shift, hcast2]
    have hQ : (gosperStage f g hs i).2.comp (X + C ((hs i - 1 - j : ℕ) : K))
        = (gosperStage f g hs (i + 1)).2.comp (X + C ((hs i - 1 - j : ℕ) : K))
          * s.comp (X + C (-((j : K) + 1))) := by
      rw [← e2, mul_comp, hT]
    have hdvd : s.comp (X + C (-((j : K) + 1))) ∣
        (gosperStage f g hs i).2.comp (X + C ((hs i - 1 - j : ℕ) : K)) :=
      Dvd.intro_left _ hQ.symm
    rw [← hsdef]
    exact (gosperStage_coprime hf hg hs N hS (k := i) (i := N) (j := i)
      (h := hs i - 1 - j) hiN.le hiN.le le_rfl le_rfl hiN.le fun m hm hmN =>
        ne_of_lt (lt_of_lt_of_le (by omega) (hmono.monotone hm))).of_isCoprime_of_dvd_right hdvd
  · unfold gosperStep2C
    rw [prod_comp]
    refine IsCoprime.prod_right fun i hi => ?_
    have hiN : i < N := Finset.mem_range.1 hi
    rw [gosperQ_comp]
    unfold gosperR
    refine IsCoprime.prod_right fun j hj => ?_
    have hj' : j < hs i := Finset.mem_range.1 hj
    obtain ⟨s, hsdef, hs0, hsq, e1, -⟩ := gosperStage_succ_spec hf hg hs i
    rw [← hsdef]
    have hdvd : s.comp (X + C (-(j : K))) ∣ (gosperStage f g hs i).1.comp (X + C (-(j : K))) :=
      dvd_comp_shift (Dvd.intro_left _ e1) _
    have hcop := isCoprime_comp_shift (gosperStage_coprime hf hg hs N hS (k := i) (i := i)
      (j := N) (h := j) hiN.le le_rfl hiN.le hiN.le le_rfl fun m hm hmN =>
        ne_of_lt (lt_of_lt_of_le hj' (hmono.monotone hm))) (-(j : K))
    rw [comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at hcop
    exact hcop.symm.of_isCoprime_of_dvd_right hdvd

/-- CO-407 (the Step 2 output, packaged).  For `f, g ≠ 0`, shifts `hs` in increasing order covering
the nonnegative integer zeros of the resultant, and `Z ≠ 0`, the output `a = Z p_N`, `b = q_N`,
`c = ∏ ∏ s_i(n-j)` satisfies (5.2.3) and (i)-(iii) of Theorem 5.3.1. -/
theorem gosper_step2_form (N : ℕ) (Z : K) (hZ : Z ≠ 0) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k) :
    C Z * f * ((gosperStage f g hs N).2 * gosperStep2C f g hs N)
      = g * ((C Z * (gosperStage f g hs N).1) * (gosperStep2C f g hs N).comp (X + 1)) ∧
    (∀ h : ℕ, IsCoprime (C Z * (gosperStage f g hs N).1)
      ((gosperStage f g hs N).2.comp (X + C (h : K)))) ∧
    IsCoprime (C Z * (gosperStage f g hs N).1) (gosperStep2C f g hs N) ∧
    IsCoprime (gosperStage f g hs N).2 ((gosperStep2C f g hs N).comp (X + 1)) := by
  have hu : IsUnit (C Z : K[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 hZ)
  obtain ⟨h1, h2, -, -⟩ := gosper_step2_spec hf hg hs N Z hZ hS
  obtain ⟨h3, h4⟩ := gosper_step2_coprime hf hg hs N hmono hS
  exact ⟨h1, h2, (isCoprime_mul_unit_left_left hu _ _).2 h3, h4⟩

end Stage

/-! ### CO-407: Corollary 5.3.2 -/

/-- CO-407. Corollary 5.3.2 (the divisibility behind it).  Let `F/G` be a rational function
(`G ≠ 0`), `a c(n+1) / (b c)` a form of it with `gcd(a, c) = gcd(b, c(n+1)) = 1` (properties (ii),
(iii)), and `A C₀(n+1) / (B C₀)` any other form with `gcd(A, B(n+h)) = 1` for all `h ∈ ℕ`
(properties (5.2.3), (5.2.4), `C₀ ≠ 0`). Then `c` divides `C₀`; in particular `deg c ≤ deg C₀`. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 5.3.2, p. 93"]
theorem gosper_c_dvd_of_triple {F G a b c A B C0 : K[X]} (hG : G ≠ 0) (hc : c ≠ 0) (hC0 : C0 ≠ 0)
    (hac : IsCoprime a c) (hbc : IsCoprime b (c.comp (X + 1)))
    (h1 : F * (b * c) = G * (a * c.comp (X + 1)))
    (hAB : ∀ h : ℕ, IsCoprime A (B.comp (X + C (h : K))))
    (h2 : F * (B * C0) = G * (A * C0.comp (X + 1))) :
    c ∣ C0 ∧ c.natDegree ≤ C0.natDegree := by
  have hdvd : c ∣ C0 := by
    refine dvd_of_gosper_forms_eq (a := a) (b := b) (c := c) (a' := A) (b' := B) (c' := C0)
      hc hC0 hac hbc hAB ?_
    apply mul_left_cancel₀ hG
    linear_combination (-(b * c)) * h2 + (B * C0) * h1
  exact ⟨hdvd, natDegree_le_of_dvd hdvd hC0⟩

/-- CO-407. Corollary 5.3.2 for the output of Step 2: among all `A, B, C₀` with
`Z f B C₀ = g A C₀(n+1)` (equation (5.2.3) for `r = Z f / g`) and `gcd(A, B(n+h)) = 1`
(equation (5.2.4)), the polynomial `c` built by Step 2 divides `C₀`, hence has the least degree. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 5.3.2, p. 93"]
theorem gosper_step2_c_minimal {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hs : ℕ → ℕ) (N : ℕ)
    (Z : K) (hZ : Z ≠ 0) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k)
    {A B C0 : K[X]} (hC0 : C0 ≠ 0) (hAB : ∀ h : ℕ, IsCoprime A (B.comp (X + C (h : K))))
    (h2 : C Z * f * (B * C0) = g * (A * C0.comp (X + 1))) :
    gosperStep2C f g hs N ∣ C0 ∧ (gosperStep2C f g hs N).natDegree ≤ C0.natDegree := by
  obtain ⟨h1, -, h3, h4⟩ := gosper_step2_form hf hg hs N Z hZ hmono hS
  exact gosper_c_dvd_of_triple hg (gosperStep2C_monic hf hg hs N).ne_zero hC0 h3 h4 h1 hAB h2

/-! ### CO-408: the shift from the subleading coefficients -/

omit [CharZero K] in
theorem coeff_pred_comp_shift (u : K[X]) {d : ℕ} (hd : u.natDegree = d + 1) (a : K) :
    (u.comp (X + C a)).coeff d = u.coeff d + ((d : K) + 1) * a * u.coeff (d + 1) := by
  show (u.eval₂ C (X + C a)).coeff d = _
  rw [eval₂_eq_sum_range, hd, finsetSum_coeff, Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : ∑ i ∈ Finset.range d, (C (u.coeff i) * (X + C a) ^ i).coeff d = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]
    simp
  rw [h0, coeff_C_mul, coeff_C_mul, coeff_X_add_C_pow, coeff_X_add_C_pow, Nat.choose_self,
    Nat.choose_succ_self_right]
  simp
  ring

/-- CO-408 (core).  If `v(n) = u(n - h)` and `deg u = d ≥ 1`, then `deg v = d`, `lc v = lc u`, and
the coefficients of `n^{d-1}` satisfy `A - B = d h lc(u)`, where `A = coeff_{d-1} u` and
`B = coeff_{d-1} v`. -/
theorem shift_subleading {u v : K[X]} {d : ℕ} (hd : 1 ≤ d) (hu : u.natDegree = d) (h : K)
    (huv : v = u.comp (X + C (-h))) :
    v.natDegree = d ∧ v.leadingCoeff = u.leadingCoeff ∧
      u.coeff (d - 1) - v.coeff (d - 1) = (d : K) * h * u.leadingCoeff := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  subst huv
  refine ⟨by rw [natDegree_comp_shift, hu], leadingCoeff_comp_shift _ _, ?_⟩
  have e := coeff_pred_comp_shift u hu (-h)
  have hl : u.leadingCoeff = u.coeff (m + 1) := by rw [leadingCoeff, hu]
  simp only [Nat.add_sub_cancel]
  rw [e, hl]
  push_cast
  ring

/-- CO-408.  The book's formula (5.3.8): if `u, v` are monic of degree `d ≥ 1` with
`v(n) = u(n - h)`, then `h = (A - B) / d` where `u = n^d + A n^{d-1} + …`,
`v = n^d + B n^{d-1} + …`; so the shift is determined by the subleading coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text, (5.3.8), p. 94"]
theorem shift_eq_of_subleading {u v : K[X]} {d : ℕ} (hd : 1 ≤ d) (hu : u.Monic)
    (hdeg : u.natDegree = d) (h : K) (huv : v = u.comp (X + C (-h))) :
    v.Monic ∧ v.natDegree = d ∧ h = (u.coeff (d - 1) - v.coeff (d - 1)) / d := by
  obtain ⟨h1, h2, h3⟩ := shift_subleading hd hdeg h huv
  refine ⟨by unfold Monic; rw [h2]; exact hu, h1, ?_⟩
  have hd0 : (d : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eq_div_iff hd0, h3, hu.leadingCoeff]
  ring

/-- CO-408 (uniqueness of the shift).  For `u` of degree `d ≥ 1`, at most one `h` satisfies
`v(n) = u(n - h)`. -/
theorem shift_unique {u v : K[X]} {d : ℕ} (hd : 1 ≤ d) (hdeg : u.natDegree = d) {h h' : K}
    (hv : v = u.comp (X + C (-h))) (hv' : v = u.comp (X + C (-h'))) : h = h' := by
  obtain ⟨-, -, e1⟩ := shift_subleading hd hdeg h hv
  obtain ⟨-, -, e2⟩ := shift_subleading hd hdeg h' hv'
  have hd0 : (d : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hl : u.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (by
    rintro rfl; simp at hdeg; omega)
  have : (d : K) * u.leadingCoeff * (h - h') = 0 := by linear_combination e2 - e1
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (mul_ne_zero hd0 hl)
  · exact sub_eq_zero.1 h0

end UndergradKB.Combinatorics.AeqB
