import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.RingDivision
import UndergradKB.Common.Attr

/-! # General real partial fractions (Lebl, *Notes on Diffy Qs*, §6.1)

* DE-170: a proper rational function whose denominator is a product of powers of pairwise coprime
  monic polynomials `g_i ^ k_i` is a sum of terms `c_{i,l} / g_i ^ l` (`1 ≤ l ≤ k_i`,
  `deg c_{i,l} < deg g_i`), as an identity of real functions off the zeros of the `g_i`.
  The real corollary treats powers of distinct linear factors `x - a` and of distinct irreducible
  quadratics `x² + b x + c` (`b² < 4c`), with constant resp. linear numerators.
* Example 6.1.6: `(s² + s + 1)/(s³ + s) = 1/s + 1/(s² + 1)`.

Sums over `l ∈ {1, …, k}` are written as sums over `l ∈ range k` with the exponent `l + 1`. -/

open Polynomial Finset

namespace UndergradKB.DifferentialEquations

/-! ### The expansion in powers of one factor -/

/-- Expansion of `r / g ^ k` in powers of a single monic `g`, when `deg r < k · deg g`. -/
theorem base_expansion {g : ℝ[X]} (hg : g.Monic) :
    ∀ (k : ℕ) (r : ℝ[X]), r.degree < ((k * g.natDegree : ℕ) : WithBot ℕ) →
      ∃ s : ℕ → ℝ[X], (∀ l, (s l).degree < g.degree) ∧
        ∀ x : ℝ, g.eval x ≠ 0 →
          r.eval x / (g.eval x) ^ k = ∑ l ∈ range k, (s l).eval x / (g.eval x) ^ (l + 1) := by
  intro k
  induction k with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by
      have : r.degree < 0 := by simpa using hr
      rw [← degree_eq_bot]
      exact Nat.WithBot.lt_zero_iff.1 this
    refine ⟨fun _ => 0, fun l => ?_, fun x _ => by simp [hr0]⟩
    rw [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot]
    exact hg.ne_zero
  | succ k ih =>
    intro r hr
    have hd : (r /ₘ g).degree < ((k * g.natDegree : ℕ) : WithBot ℕ) := by
      by_cases h0 : r /ₘ g = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      · have hr0 : r ≠ 0 := fun h => h0 (by simp [h])
        have h1 : r.natDegree < (k + 1) * g.natDegree := (natDegree_lt_iff_degree_lt hr0).2 hr
        have h2 := natDegree_divByMonic r hg
        rw [← natDegree_lt_iff_degree_lt h0, h2]
        rw [add_mul, one_mul] at h1
        have h3 : ¬ r.degree < g.degree := fun h => h0 ((divByMonic_eq_zero_iff hg).2 h)
        have h4 : g.natDegree ≤ r.natDegree :=
          natDegree_le_natDegree (not_lt.1 h3)
        omega
    obtain ⟨s, hs, hsum⟩ := ih (r /ₘ g) hd
    refine ⟨fun l => if l = k then r %ₘ g else s l, fun l => ?_, fun x hx => ?_⟩
    · by_cases hl : l = k
      · simp only [hl, ite_true]; exact degree_modByMonic_lt r hg
      · simp only [hl, ite_false]; exact hs l
    · have hdiv := modByMonic_add_div r g
      have hev : r.eval x = (r %ₘ g).eval x + g.eval x * (r /ₘ g).eval x := by
        conv_lhs => rw [← hdiv]
        simp
      rw [sum_range_succ]
      have : ∑ l ∈ range k, ((if l = k then r %ₘ g else s l)).eval x / (g.eval x) ^ (l + 1) =
          ∑ l ∈ range k, (s l).eval x / (g.eval x) ^ (l + 1) := by
        refine sum_congr rfl fun l hl => ?_
        have : l ≠ k := (mem_range.1 hl).ne
        simp [this]
      rw [this, ← hsum x hx, hev]
      simp only [ite_true]
      field_simp
      ring

/-! ### The general theorem -/

/-- If `q * P + S = p` with `P` monic, `deg S < deg P` and `deg p < deg P`, then `q = 0`. -/
theorem quo_eq_zero_of_degree_lt {P S p q : ℝ[X]} (hP : P.Monic) (hS : S.degree < P.degree)
    (hp : p.degree < P.degree) (h : q * P + S = p) : q = 0 := by
  by_contra hq
  have h1 : q * P = p - S := by rw [← h]; ring
  have h2 : (p - S).degree < P.degree := (degree_sub_le p S).trans_lt (max_lt hp hS)
  have h3 : q * P ≠ 0 := mul_ne_zero hq hP.ne_zero
  have h4 := degree_le_of_dvd (dvd_mul_left P q) h3
  rw [h1] at h4
  exact absurd h2 (not_lt.2 h4)

/-- **General partial fractions.** (DE-170) Let `g_i` (`i ∈ s`) be pairwise coprime monic real
polynomials, `k_i` natural numbers, and `p` a polynomial with `deg p < ∑ k_i deg g_i`. Then there
are polynomials `c i l` of degree `< deg g_i` such that, at every real `x` where no `g_i` vanishes,
`p(x) / ∏ g_i(x)^{k_i} = ∑_i ∑_{l=1}^{k_i} c_{i,l}(x) / g_i(x)^l` (the index `l` is shifted by one). -/
@[kb "lebldiffyqs2026" "§6.1 Partial fractions, p. 297"]
theorem partial_fractions_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ[X])
    (k : ι → ℕ) (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise (↑s) fun i j => IsCoprime (g i) (g j)) (p : ℝ[X])
    (hp : p.degree < ((∑ i ∈ s, k i * (g i).natDegree : ℕ) : WithBot ℕ)) :
    ∃ c : ι → ℕ → ℝ[X], (∀ i ∈ s, ∀ l, (c i l).degree < (g i).degree) ∧
      ∀ x : ℝ, (∀ i ∈ s, (g i).eval x ≠ 0) →
        p.eval x / ∏ i ∈ s, ((g i).eval x) ^ k i =
          ∑ i ∈ s, ∑ l ∈ range (k i), (c i l).eval x / ((g i).eval x) ^ (l + 1) := by
  have hG : ∀ i ∈ s, (g i ^ k i).Monic := fun i hi => (hg i hi).pow _
  have hGG : Set.Pairwise (↑s) fun i j => IsCoprime (g i ^ k i) (g j ^ k j) :=
    fun i hi j hj hij => (hgg hi hj hij).pow
  obtain ⟨q, r, hr, hp'⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod p hG hGG
  set P : ℝ[X] := ∏ i ∈ s, g i ^ k i with hPdef
  have hPm : P.Monic := monic_prod_of_monic s _ hG
  have hPdeg : P.natDegree = ∑ i ∈ s, k i * (g i).natDegree := by
    rw [hPdef, natDegree_prod_of_monic s _ hG]
    exact sum_congr rfl fun i _ => natDegree_pow _ _
  have hPd : P.degree = ((∑ i ∈ s, k i * (g i).natDegree : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hPm.ne_zero, hPdeg]
  have hbot : (⊥ : WithBot ℕ) < P.degree := by
    rw [bot_lt_iff_ne_bot, Ne, degree_eq_bot]; exact hPm.ne_zero
  have hterm : ∀ i ∈ s, (r i * ∏ j ∈ s.erase i, g j ^ k j).degree < P.degree := by
    intro i hi
    by_cases h0 : r i = 0
    · rw [h0, zero_mul, degree_zero]; exact hbot
    · have hE : (∏ j ∈ s.erase i, g j ^ k j).Monic :=
        monic_prod_of_monic _ _ fun j hj => hG j (mem_of_mem_erase hj)
      have hmul := mul_prod_erase s (fun j => g j ^ k j) hi
      refine degree_lt_degree ?_
      have h1 : (r i).natDegree < (g i ^ k i).natDegree :=
        natDegree_lt_natDegree h0 (hr i hi)
      have h2 : P.natDegree = (g i ^ k i).natDegree + (∏ j ∈ s.erase i, g j ^ k j).natDegree := by
        rw [hPdef, ← hmul]
        exact natDegree_mul (hG i hi).ne_zero hE.ne_zero
      rw [natDegree_mul h0 hE.ne_zero, h2]
      omega
  have hS : (∑ i ∈ s, r i * ∏ j ∈ s.erase i, g j ^ k j).degree < P.degree :=
    (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff hbot).2 hterm)
  have hq : q = 0 := quo_eq_zero_of_degree_lt hPm hS (hPd ▸ hp) hp'.symm
  have hexp : ∀ i, ∃ t : ℕ → ℝ[X], i ∈ s → ((∀ l, (t l).degree < (g i).degree) ∧
      ∀ x : ℝ, (g i).eval x ≠ 0 → (r i).eval x / ((g i).eval x) ^ k i =
        ∑ l ∈ range (k i), (t l).eval x / ((g i).eval x) ^ (l + 1)) := by
    intro i
    by_cases hi : i ∈ s
    · have hd : (r i).degree < ((k i * (g i).natDegree : ℕ) : WithBot ℕ) := by
        have := hr i hi
        rwa [degree_eq_natDegree (hG i hi).ne_zero, natDegree_pow] at this
      obtain ⟨t, ht⟩ := base_expansion (hg i hi) (k i) (r i) hd
      exact ⟨t, fun _ => ht⟩
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
  choose c hc using hexp
  refine ⟨c, fun i hi => (hc i hi).1, fun x hx => ?_⟩
  have hne : ∀ i ∈ s, ((g i).eval x) ^ k i ≠ 0 := fun i hi => pow_ne_zero _ (hx i hi)
  have hPx : P.eval x = ∏ i ∈ s, ((g i).eval x) ^ k i := by
    rw [hPdef, eval_prod]; simp
  have hp_eval : p.eval x = ∑ i ∈ s, (r i).eval x * ∏ j ∈ s.erase i, ((g j).eval x) ^ k j := by
    rw [hp', hq]; simp [eval_finsetSum, eval_prod]
  have hPne : ∏ i ∈ s, ((g i).eval x) ^ k i ≠ 0 := prod_ne_zero_iff.2 hne
  rw [hp_eval, Finset.sum_div]
  refine sum_congr rfl fun i hi => ?_
  rw [← (hc i hi).2 x (hx i hi)]
  have := mul_prod_erase s (fun j => ((g j).eval x) ^ k j) hi
  have hEne : ∏ j ∈ s.erase i, ((g j).eval x) ^ k j ≠ 0 :=
    prod_ne_zero_iff.2 fun j hj => hne j (mem_of_mem_erase hj)
  rw [← this]
  field_simp [hne i hi]

/-! ### The real case: linear and irreducible quadratic factors -/

/-- The monic quadratic `X² + b X + c`. -/
noncomputable def quadFactor (b c : ℝ) : ℝ[X] := X ^ 2 + C b * X + C c

theorem quadFactor_monic (b c : ℝ) : (quadFactor b c).Monic := by
  unfold quadFactor; monicity!

theorem quadFactor_natDegree (b c : ℝ) : (quadFactor b c).natDegree = 2 := by
  unfold quadFactor; compute_degree!

theorem quadFactor_degree (b c : ℝ) : (quadFactor b c).degree = 2 := by
  rw [degree_eq_natDegree (quadFactor_monic b c).ne_zero, quadFactor_natDegree]; rfl

theorem quadFactor_eval (b c x : ℝ) : (quadFactor b c).eval x = x ^ 2 + b * x + c := by
  simp [quadFactor]

theorem quad_pos {b c : ℝ} (h : b ^ 2 < 4 * c) (x : ℝ) : 0 < x ^ 2 + b * x + c := by
  nlinarith [sq_nonneg (2 * x + b)]

theorem quadFactor_irreducible {b c : ℝ} (h : b ^ 2 < 4 * c) : Irreducible (quadFactor b c) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => ?_
  · rw [quadFactor_natDegree]; simp
  · rw [IsRoot, quadFactor_eval] at hx
    exact (quad_pos h x).ne' hx

theorem quadFactor_inj {b c b' c' : ℝ} (h : quadFactor b c = quadFactor b' c') :
    b = b' ∧ c = c' := by
  have h1 := congrArg (fun p => p.coeff 1) h
  have h0 := congrArg (fun p => p.coeff 0) h
  simp [quadFactor, coeff_X, coeff_C] at h1 h0
  exact ⟨h1, h0⟩

theorem eval_of_degree_lt_one {p : ℝ[X]} (h : p.degree < 1) (x : ℝ) : p.eval x = p.coeff 0 := by
  have := eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.1 h)
  calc p.eval x = (C (p.coeff 0)).eval x := by rw [← this]
    _ = _ := by simp

theorem eval_of_degree_lt_two {p : ℝ[X]} (h : p.degree < 2) (x : ℝ) :
    p.eval x = p.coeff 1 * x + p.coeff 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · have : p.natDegree < 2 := (natDegree_lt_iff_degree_lt hp).2 (by exact_mod_cast h)
    rw [eval_eq_sum_range' this]
    simp [sum_range_succ]
    ring

/-- The family of factors: `X - a` on the left, `X² + b X + c` on the right. -/
noncomputable def linQuad : ℝ ⊕ (ℝ × ℝ) → ℝ[X]
  | Sum.inl a => X - C a
  | Sum.inr bc => quadFactor bc.1 bc.2

theorem linQuad_inl (a : ℝ) : linQuad (Sum.inl a) = X - C a := rfl

theorem linQuad_inr (bc : ℝ × ℝ) : linQuad (Sum.inr bc) = quadFactor bc.1 bc.2 := rfl

/-- **Real partial fractions.** (DE-170) Let `A` be a finite set of reals (the roots) with
multiplicities `kA a`, and `Q` a finite set of pairs `(b, c)` with `b² < 4c` (distinct irreducible
quadratics `x² + b x + c`) with multiplicities `mQ`. If `p` is a real polynomial with
`deg p < ∑ kA + 2 ∑ mQ` (a proper fraction), there are real coefficients `α, β, γ` such that for
every real `x` that is not in `A`,
`p(x) / (∏ (x-a)^{kA a} · ∏ (x²+bx+c)^{mQ}) = ∑_a ∑_{l=1}^{kA a} α_{a,l}/(x-a)^l
  + ∑_{(b,c)} ∑_{l=1}^{mQ} (β_{bc,l} x + γ_{bc,l})/(x²+bx+c)^l`
(the index `l` is shifted by one). -/
@[kb "lebldiffyqs2026" "§6.1 Partial fractions, p. 297"]
theorem partial_fractions_real (A : Finset ℝ) (kA : ℝ → ℕ) (Q : Finset (ℝ × ℝ))
    (hQ : ∀ bc ∈ Q, bc.1 ^ 2 < 4 * bc.2) (mQ : ℝ × ℝ → ℕ) (p : ℝ[X])
    (hp : p.degree < ((∑ a ∈ A, kA a + 2 * ∑ bc ∈ Q, mQ bc : ℕ) : WithBot ℕ)) :
    ∃ (α : ℝ → ℕ → ℝ) (β γ : ℝ × ℝ → ℕ → ℝ), ∀ x : ℝ, (∀ a ∈ A, x ≠ a) →
      p.eval x / ((∏ a ∈ A, (x - a) ^ kA a) * ∏ bc ∈ Q, (x ^ 2 + bc.1 * x + bc.2) ^ mQ bc) =
        ∑ a ∈ A, ∑ l ∈ range (kA a), α a l / (x - a) ^ (l + 1) +
        ∑ bc ∈ Q, ∑ l ∈ range (mQ bc),
          (β bc l * x + γ bc l) / (x ^ 2 + bc.1 * x + bc.2) ^ (l + 1) := by
  classical
  have hmon : ∀ i ∈ A.disjSum Q, (linQuad i).Monic := by
    rintro (a | bc) _
    · exact monic_X_sub_C a
    · exact quadFactor_monic _ _
  have hlin : ∀ a ∈ A, ∀ bc ∈ Q, IsCoprime (X - C a) (quadFactor bc.1 bc.2) := by
    intro a _ bc hbc
    refine (irreducible_X_sub_C a).coprime_iff_not_dvd.2 ?_
    rw [dvd_iff_isRoot, IsRoot, quadFactor_eval]
    exact (quad_pos (hQ bc hbc) a).ne'
  have hpair : Set.Pairwise (↑(A.disjSum Q) : Set (ℝ ⊕ (ℝ × ℝ)))
      fun i j => IsCoprime (linQuad i) (linQuad j) := by
    rintro (a | bc) hi (a' | bc') hj hij
    · simp only [linQuad]
      refine isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.2 (sub_ne_zero.2 ?_))
      intro h; exact hij (by rw [h])
    · simp only [mem_coe, mem_disjSum] at hi hj
      obtain ⟨a₀, ha, e⟩ := hi.resolve_right (by simp)
      obtain ⟨bc₀, hbc, e'⟩ := hj.resolve_left (by simp)
      simp only [Sum.inl.injEq] at e
      simp only [Sum.inr.injEq] at e'
      subst e e'
      exact hlin _ ha _ hbc
    · simp only [mem_coe, mem_disjSum] at hi hj
      obtain ⟨a₀, ha, e⟩ := hj.resolve_right (by simp)
      obtain ⟨bc₀, hbc, e'⟩ := hi.resolve_left (by simp)
      simp only [Sum.inl.injEq] at e
      simp only [Sum.inr.injEq] at e'
      subst e e'
      exact (hlin _ ha _ hbc).symm
    · simp only [mem_coe, mem_disjSum] at hi
      obtain ⟨bc₀, hbc, e'⟩ := hi.resolve_left (by simp)
      simp only [Sum.inr.injEq] at e'
      subst e'
      simp only [linQuad]
      refine (quadFactor_irreducible (hQ _ hbc)).coprime_iff_not_dvd.2 fun hd => hij ?_
      have := eq_of_monic_of_dvd_of_natDegree_le (quadFactor_monic _ _) (quadFactor_monic _ _) hd
        (by rw [quadFactor_natDegree, quadFactor_natDegree])
      obtain ⟨h1, h2⟩ := quadFactor_inj this
      rw [Prod.ext h1.symm h2.symm]
  have hsum : (∑ i ∈ A.disjSum Q, (Sum.elim kA mQ i) * (linQuad i).natDegree) =
      ∑ a ∈ A, kA a + 2 * ∑ bc ∈ Q, mQ bc := by
    rw [sum_disjSum, mul_sum]
    simp only [Sum.elim_inl, Sum.elim_inr, linQuad, natDegree_X_sub_C, quadFactor_natDegree,
      mul_one]
    congr 1
    exact sum_congr rfl fun _ _ => mul_comm _ _
  obtain ⟨c, hc, hx⟩ := partial_fractions_pow (A.disjSum Q) linQuad (Sum.elim kA mQ) hmon hpair p
    (by rw [hsum]; exact hp)
  refine ⟨fun a l => (c (Sum.inl a) l).coeff 0, fun bc l => (c (Sum.inr bc) l).coeff 1,
    fun bc l => (c (Sum.inr bc) l).coeff 0, fun x hxA => ?_⟩
  have hne : ∀ i ∈ A.disjSum Q, (linQuad i).eval x ≠ 0 := by
    rintro (a | bc) hi
    · simp only [linQuad, eval_sub, eval_X, eval_C]
      exact sub_ne_zero.2 (hxA a (by simpa using hi))
    · have : bc ∈ Q := by simpa using hi
      simp only [linQuad, quadFactor_eval]
      exact (quad_pos (hQ bc this) x).ne'
  have := hx x hne
  simp only [prod_disjSum, sum_disjSum, Sum.elim_inl, Sum.elim_inr, linQuad_inl, linQuad_inr,
    eval_sub, eval_X, eval_C, quadFactor_eval] at this
  rw [this]
  congr 1
  · refine sum_congr rfl fun a ha => sum_congr rfl fun l _ => ?_
    rw [eval_of_degree_lt_one (by simpa [linQuad] using hc (Sum.inl a) (by simpa using ha) l)]
  · refine sum_congr rfl fun bc hbc => sum_congr rfl fun l _ => ?_
    rw [eval_of_degree_lt_two (by
      have := hc (Sum.inr bc) (by simpa using hbc) l
      simpa [linQuad, quadFactor_degree] using this)]

/-! ### Example 6.1.6 -/

/-- **Example 6.1.6** (DE-170), Lebl p. 297: `(s² + s + 1)/(s³ + s) = 1/s + 1/(s² + 1)` for `s ≠ 0`
(partial fractions with a linear and an irreducible quadratic factor; the quadratic numerator is
`B s + C` with `B = 0`, `C = 1`). -/
@[kb "lebldiffyqs2026" "Example 6.1.6, p. 297"]
theorem example_6_1_6 {s : ℝ} (hs : s ≠ 0) :
    (s ^ 2 + s + 1) / (s ^ 3 + s) = 1 / s + 1 / (s ^ 2 + 1) := by
  have h1 : s ^ 2 + 1 ≠ 0 := by positivity
  have h2 : s ^ 3 + s = s * (s ^ 2 + 1) := by ring
  rw [h2]
  field_simp
  ring

end UndergradKB.DifferentialEquations
