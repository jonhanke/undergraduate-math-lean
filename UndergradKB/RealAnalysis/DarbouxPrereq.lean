import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import UndergradKB.Common.Attr

/-!
# Sequence and compactness prerequisites for Darboux integrability (Lebl, Sections 2.1-2.3, 3.3)

Ported from ReasBook (https://github.com/optpku/ReasBook), commit 35bcb693144a4cb67108bac1793b5ffbfea0acd9,
files `ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap02/section01.lean` (lines 14-24,92-116,721-767),
`.../Chap02/section02.lean` (lines 97-130,198-231), `.../Chap02/section03.lean` (lines 1287-1400) and
`.../Chap03/section03.lean` (lines 13-53, without the Theorem 3.3.2 statement and the examples),
by Zichen Wang and Zaiwen Wen, released under the Apache License 2.0 (see `NOTICE` and
`LICENSES/Apache-2.0-ReasBook.txt`). Formalizes J. Lebl, *Basic Analysis I* (cited as `lebl2026`, v6.3; ReasBook
follows v6.2, same numbering in this chapter). Only the declarations (and their dependencies) used by the
ported Riemann-integrability files are taken. Changes from the original: specific Mathlib imports instead of
`import Mathlib`; declarations moved into the namespace `UndergradKB.RealAnalysis`; `@[kb]` citation tags added;
proof repairs for Lean v4.36 / Mathlib 1b1ccf4 where needed. Re-checked by this repository's build.
-/

namespace UndergradKB.RealAnalysis

/-- Definition 2.1.1: A sequence of real numbers is a function `x : ℕ → ℝ`,
whose `n`-th term is denoted `x n` (often written `xₙ`), and also denoted
`{x_n}_{n=1}^{\infty}`. The sequence is bounded if there exists `B : ℝ` with
`|x n| ≤ B` for all `n`. It is bounded below if there is `B` with `B ≤ x n`
for all `n`, and bounded above if there is `B` with `x n ≤ B` for all `n`. -/
abbrev RealSequence : Type :=
  ℕ → ℝ

/-- A real sequence admitting a uniform bound on absolute values. -/
def BoundedSequence (x : RealSequence) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, |x n| ≤ B

/-- Definition 2.1.2: A real sequence `x` converges to `l` if for every
`ε > 0` there is an `M : ℕ` such that `|x n - l| < ε` whenever `n ≥ M`.
Such an `l` is called a limit of the sequence, and a sequence with some
limit is called convergent (otherwise divergent). -/
def ConvergesTo (x : RealSequence) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, |x n - l| < ε

/-- A real sequence is convergent if it admits a (necessarily unique) limit. -/
def ConvergentSequence (x : RealSequence) : Prop :=
  ∃ l : ℝ, ConvergesTo x l

/-- The book's ε–`M` definition of convergence agrees with the standard
`Filter.Tendsto` formulation in mathlib. -/
lemma convergesTo_iff_tendsto (x : RealSequence) (l : ℝ) :
    ConvergesTo x l ↔ Filter.Tendsto x Filter.atTop (nhds l) := by
  unfold ConvergesTo
  simpa [Real.dist_eq] using (Metric.tendsto_atTop (u := x) (a := l)).symm

/-- A constant real sequence converges to its constant value. -/
lemma constant_seq_converges (a : ℝ) :
    ConvergesTo (fun _ : ℕ => a) a := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n hn
  simpa using hε

/-- Definition 2.1.16: Given a real sequence `{x_n}` and a strictly increasing
sequence of indices `n₁ < n₂ < n₃ < …`, the extracted sequence `i ↦ x (n i)` is
called a subsequence of `{x_n}`. -/
structure RealSubsequence (x : RealSequence) where
  /-- the strictly increasing indexing function `n_i` selecting terms of the
  original sequence -/
  indices : ℕ → ℕ
  strictlyIncreasing : StrictMono indices

/-- The indices of a subsequence eventually dominate their position:
`i ≤ n_i` for all `i`. -/
lemma subsequence_indices_ge_self {x : RealSequence} (s : RealSubsequence x) :
    ∀ i, i ≤ s.indices i := by
  intro i
  induction' i with i ih
  · exact Nat.zero_le _
  · have hlt : s.indices i < s.indices i.succ :=
      s.strictlyIncreasing (Nat.lt_succ_self i)
    have hle_succ : (s.indices i).succ ≤ s.indices i.succ :=
      Nat.succ_le_of_lt hlt
    have hle_step : i.succ ≤ (s.indices i).succ := Nat.succ_le_succ ih
    exact le_trans hle_step hle_succ

/-- The subsequence of `x` determined by the index data `s`. -/
def RealSubsequence.asSequence {x : RealSequence} (s : RealSubsequence x) :
    RealSequence :=
  fun i : ℕ => x (s.indices i)

/-- A real sequence `y` is a subsequence of `x` if it arises by composing `x`
with a strictly increasing index map. -/
def IsRealSubsequence (x y : RealSequence) : Prop :=
  ∃ s : RealSubsequence x, y = s.asSequence

/-- Proposition 2.1.17: If a real sequence `{x_n}` converges, then every
strictly increasing subsequence `{x_{n_i}}` also converges, with the same
limit as the original sequence: `lim_{n → ∞} x_n = lim_{i → ∞} x_{n_i}`. -/
lemma convergesTo_subsequence {x : RealSequence} {l : ℝ}
    (hx : ConvergesTo x l) (s : RealSubsequence x) :
    ConvergesTo (s.asSequence) l := by
  intro ε hε
  rcases hx ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro i hi
  have hindex : i ≤ s.indices i := subsequence_indices_ge_self (x := x) s i
  have hMi : M ≤ s.indices i := le_trans hi hindex
  have h := hM (s.indices i) hMi
  simpa [RealSubsequence.asSequence] using h

/-- Proposition 2.2.5: For convergent real sequences `x` and `y`, the usual
algebraic operations preserve convergence. (i) The sum sequence converges to
the sum of the limits. (ii) The difference sequence converges to the
difference of the limits. (iii) The termwise product converges to the product
of the limits. (iv) If `lim_{n → ∞} y_n ≠ 0` and every `y n ≠ 0`, then the
quotient sequence converges to the quotient of the limits. -/
lemma limit_add_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n + y n) (l + m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.add hy'
  exact (convergesTo_iff_tendsto (fun n : ℕ => x n + y n) (l + m)).2 h

/-- The limit of the difference of two convergent real sequences is the
difference of their limits. -/
lemma limit_sub_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n - y n) (l - m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.sub hy'
  simpa [sub_eq_add_neg] using
    (convergesTo_iff_tendsto (fun n : ℕ => x n - y n) (l - m)).2 h

/-- The limit of the termwise product of two convergent real sequences is the
product of their limits. -/
lemma limit_mul_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n * y n) (l * m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.mul hy'
  exact (convergesTo_iff_tendsto (fun n : ℕ => x n * y n) (l * m)).2 h

/-- Theorem 2.3.8 (Bolzano--Weierstrass): Every bounded real sequence
`{x_n}` admits a convergent subsequence `{x_{n_i}}`. -/
theorem bolzanoWeierstrass_real_sequence {x : RealSequence}
    (hx : BoundedSequence x) :
    ∃ s : RealSubsequence x, ConvergentSequence (s.asSequence) := by
  classical
  -- bound the sequence inside a compact interval
  obtain ⟨B, hB⟩ := hx
  have hmem : ∀ n, x n ∈ Set.Icc (-B) B := by
    intro n
    have h := hB n
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
  -- compactness of the closed interval yields a convergent subsequence
  rcases (isCompact_Icc.tendsto_subseq (x := fun n => x n) hmem) with
    ⟨l, _hl, φ, hmono, hφ⟩
  let s : RealSubsequence x := ⟨φ, hmono⟩
  refine ⟨s, ?_⟩
  refine ⟨l, ?_⟩
  -- translate the filter convergence statement to the ε–`M` notion
  have hφ' :
      Filter.Tendsto (s.asSequence) Filter.atTop (nhds l) := by
    exact hφ
  exact (convergesTo_iff_tendsto (x := s.asSequence) (l := l)).2 hφ'

/-- Proposition 2.3.7: A bounded sequence `{x_n}` converges to `x` if and only if
every convergent subsequence `{x_{n_k}}` converges to the same limit `x`. -/
lemma converges_iff_convergent_subsequences_converge
    {x : RealSequence} {l : ℝ} (hx : BoundedSequence x) :
    ConvergesTo x l ↔
      ∀ s : RealSubsequence x,
        ConvergentSequence (s.asSequence) → ConvergesTo (s.asSequence) l := by
  constructor
  · intro hconv s _hsconv
    exact convergesTo_subsequence (x := x) (l := l) hconv s
  · intro hsub
    classical
    -- assume the sequence does not converge to `l` and derive a contradiction
    by_contra hnot
    -- extract a uniform gap from the definition of `ConvergesTo`
    have hε :
        ∃ ε > 0, ∀ M, ∃ n ≥ M, ε ≤ |x n - l| := by
      have hneg : ¬ ConvergesTo x l := hnot
      unfold ConvergesTo at hneg
      push Not at hneg
      rcases hneg with ⟨ε, hεpos, hfail⟩
      refine ⟨ε, hεpos, ?_⟩
      intro M
      rcases hfail M with ⟨n, hn, hlt⟩
      refine ⟨n, hn, ?_⟩
      exact hlt
    rcases hε with ⟨ε, hεpos, hfar⟩
    -- build a subsequence whose terms stay `ε` away from `l`
    let idx : ℕ → ℕ :=
      fun n =>
        Nat.recOn n (Classical.choose (hfar 0))
          (fun k ih =>
            Classical.choose (hfar (ih + 1)))
    have hidx_step :
        ∀ k, idx (k + 1) ≥ idx k + 1 ∧ ε ≤ |x (idx (k + 1)) - l| := by
      intro k
      have hspec := Classical.choose_spec (hfar (idx k + 1))
      rcases hspec with ⟨hge, hdist⟩
      exact ⟨hge, hdist⟩
    have hidx_base : ε ≤ |x (idx 0) - l| :=
      (Classical.choose_spec (hfar 0)).2
    have hfar_idx : ∀ n, ε ≤ |x (idx n) - l| := by
      intro n
      induction' n with n ih
      · simpa using hidx_base
      · simpa using (hidx_step n).2
    have hstrict : StrictMono idx := by
      refine strictMono_nat_of_lt_succ ?_
      intro k
      have hge := (hidx_step k).1
      have hlt : idx k < idx k + 1 := Nat.lt_succ_self _
      exact lt_of_lt_of_le hlt hge
    let s₀ : RealSubsequence x := ⟨idx, hstrict⟩
    -- the constructed subsequence remains bounded
    rcases hx with ⟨B, hB⟩
    have hBound_s₀ : BoundedSequence (s₀.asSequence) := by
      refine ⟨B, ?_⟩
      intro n
      simpa [RealSubsequence.asSequence, s₀] using hB (idx n)
    -- apply Bolzano--Weierstrass to obtain a convergent sub-subsequence
    rcases bolzanoWeierstrass_real_sequence (x := s₀.asSequence) hBound_s₀ with
      ⟨t, hconv_t⟩
    rcases hconv_t with ⟨L, hL⟩
    -- promote the sub-subsequence to a subsequence of the original sequence
    let u : RealSubsequence x :=
      ⟨fun n => s₀.indices (t.indices n),
        s₀.strictlyIncreasing.comp t.strictlyIncreasing⟩
    have hu_seq :
        u.asSequence = t.asSequence := by
      funext n
      rfl
    have hconv_u : ConvergesTo (u.asSequence) L := by
      -- `u.asSequence` definally agrees with `t.asSequence`
      simpa [hu_seq] using hL
    -- use the hypothesis to force convergence of this subsequence to `l`
    have hconv_to_l : ConvergesTo (u.asSequence) l :=
      hsub u ⟨L, hconv_u⟩
    -- contradiction: every term of `u` stays at least `ε` away from `l`
    have hfar_u : ∀ n, ε ≤ |u.asSequence n - l| := by
      intro n
      dsimp [u, RealSubsequence.asSequence, s₀, idx]
      exact hfar_idx (t.indices n)
    have hεpos' : 0 < ε / 2 := by linarith
    rcases hconv_to_l (ε / 2) hεpos' with ⟨M, hM⟩
    have hcontr := hfar_u M
    have hclose := hM M le_rfl
    have hlt : |u.asSequence M - l| < ε := by
      have hhalf : |u.asSequence M - l| < ε / 2 := hclose
      linarith
    exact (not_lt_of_ge hcontr) hlt

/-- Lemma 2.2.3: If convergent real sequences `x` and `y` satisfy
`x n ≤ y n` for every `n`, then their limits obey
`lim_{n → ∞} x_n ≤ lim_{n → ∞} y_n`. -/
lemma limit_le_of_pointwise_le {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m)
    (hxy : ∀ n : ℕ, x n ≤ y n) :
    l ≤ m := by
  classical
  by_contra hle
  have hlt : m < l := lt_of_not_ge hle
  have hpos : 0 < l - m := sub_pos.mpr hlt
  -- work with `ε = (l - m) / 2` and use `ε / 2` in the convergence bounds
  set ε : ℝ := (l - m) / 2 with hεdef
  have hεpos : 0 < ε := by linarith
  have hε2pos : 0 < ε / 2 := by linarith
  rcases hx (ε / 2) hε2pos with ⟨M₁, hM₁⟩
  rcases hy (ε / 2) hε2pos with ⟨M₂, hM₂⟩
  let M := max M₁ M₂
  have hxM : |x M - l| < ε / 2 := hM₁ M (Nat.le_max_left _ _)
  have hyM : |y M - m| < ε / 2 := hM₂ M (Nat.le_max_right _ _)
  have hx_lower : l - ε / 2 < x M := by
    have hx_bounds := abs_lt.mp hxM
    linarith
  have hy_upper : y M < m + ε / 2 := by
    have hy_bounds := abs_lt.mp hyM
    linarith
  have hxyM : x M ≤ y M := hxy M
  have hlt' : l - m < ε := by
    have hmid : l - ε / 2 < y M := lt_of_lt_of_le hx_lower hxyM
    have hfin : l - ε / 2 < m + ε / 2 := lt_trans hmid hy_upper
    linarith
  have hge : ε ≤ l - m := by linarith [hpos, hεdef]
  have hcontra : ¬ l - m < ε := not_lt_of_ge hge
  exact hcontra hlt'

/-- Lemma 3.3.1. A continuous function `f : [a, b] → ℝ` is bounded. -/
lemma lemma_3_3_1 {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, by exact ⟨le_rfl, hle⟩⟩
  have hcompact_image : IsCompact (f '' Set.Icc a b) :=
    hcompact.image_of_continuousOn hf
  have hnonempty_image : (f '' Set.Icc a b).Nonempty := hnonempty.image _
  have hcont_abs : ContinuousOn (fun y : ℝ => |y|) (f '' Set.Icc a b) :=
    continuous_abs.continuousOn
  obtain ⟨y, _, hy_max⟩ :=
    hcompact_image.exists_isMaxOn hnonempty_image hcont_abs
  have hy_max' :
      ∀ z ∈ f '' Set.Icc a b, |z| ≤ |y| := by
    -- eventually filter on a principal set corresponds to pointwise membership
    simpa [IsMaxOn, IsMaxFilter, Filter.eventually_principal] using hy_max
  refine ⟨|y|, ?_⟩
  intro x hx
  have hx_image : f x ∈ f '' Set.Icc a b := ⟨x, hx, rfl⟩
  exact hy_max' (f x) hx_image

/-- Helper lemma for Theorem 3.3.2: a continuous function reaches its minimum on `[a, b]`. -/
lemma theorem_3_3_2_min_helper {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x := by
  classical
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hle⟩⟩
  obtain ⟨c, hc, hc_min⟩ := hcompact.exists_isMinOn hnonempty hf
  exact ⟨c, hc, by simpa [isMinOn_iff] using hc_min⟩

/-- Helper lemma for Theorem 3.3.2: a continuous function reaches its maximum on `[a, b]`. -/
lemma theorem_3_3_2_max_helper {a b : ℝ} (hle : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ d ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f d := by
  classical
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hnonempty : (Set.Icc a b).Nonempty := ⟨a, ⟨le_rfl, hle⟩⟩
  obtain ⟨d, hd, hd_max⟩ := hcompact.exists_isMaxOn hnonempty hf
  exact ⟨d, hd, by simpa [isMaxOn_iff] using hd_max⟩

end UndergradKB.RealAnalysis
