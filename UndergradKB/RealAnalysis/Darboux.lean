import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Cases
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr

/-!
# Darboux sums, Darboux integrals and the Riemann integral (Lebl, Section 5.1)

Ported from ReasBook (https://github.com/optpku/ReasBook), commit 35bcb693144a4cb67108bac1793b5ffbfea0acd9,
file `ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap05/section01.lean` (lines 1-181,406-1285,1676-1761),
by Zichen Wang and Zaiwen Wen, released under the Apache License 2.0 (see `NOTICE` and
`LICENSES/Apache-2.0-ReasBook.txt`). Formalizes J. Lebl, *Basic Analysis I* (cited as `lebl2026`, v6.3; ReasBook
follows v6.2, same numbering in this chapter). Changes from the original: specific Mathlib imports instead of
`import Mathlib`; declarations moved into the namespace `UndergradKB.RealAnalysis`; `@[kb]` citation tags added;
proof repairs for Lean v4.36 / Mathlib 1b1ccf4 where needed. Re-checked by this repository's build.
-/

namespace UndergradKB.RealAnalysis

open scoped BigOperators

/-- Definition 5.1.1: A partition `P` of `[a, b]` is a finite increasing list
`x₀, x₁, …, xₙ` with `x₀ = a` and `xₙ = b`. Write `Δxᵢ = xᵢ - xᵢ₋₁`. For a
bounded function `f : [a, b] → ℝ`, set `mᵢ = inf {f x | x_{i-1} ≤ x ≤ xᵢ}` and
`Mᵢ = sup {f x | x_{i-1} ≤ x ≤ xᵢ}`, and define the lower Darboux sum
`L(P, f) = ∑ mᵢ Δxᵢ` and the upper Darboux sum `U(P, f) = ∑ Mᵢ Δxᵢ`. -/
structure IntervalPartition (a b : ℝ) where
  n : ℕ
  points : Fin (n + 1) → ℝ
  mono : StrictMono points
  left_eq : points 0 = a
  right_eq : points ⟨n, Nat.lt_succ_self _⟩ = b

variable {a b : ℝ}

/-- The mesh length `Δxᵢ = xᵢ - xᵢ₋₁` for the `i`-th subinterval. -/
def IntervalPartition.delta (P : IntervalPartition a b) (i : Fin P.n) : ℝ :=
  P.points i.succ - P.points (Fin.castSucc i)

/-- The infimum of `f` on the `i`-th closed subinterval. -/
noncomputable def lowerTag (f : ℝ → ℝ) (P : IntervalPartition a b) (i : Fin P.n) :
    ℝ :=
  sInf (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))

/-- The supremum of `f` on the `i`-th closed subinterval. -/
noncomputable def upperTag (f : ℝ → ℝ) (P : IntervalPartition a b) (i : Fin P.n) :
    ℝ :=
  sSup (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ))

/-- Lower Darboux sum `L(P, f) = ∑ mᵢ Δxᵢ`. -/
@[kb "lebl2026" "Definition 5.1.1, p. 181"]
noncomputable def lowerDarbouxSum (f : ℝ → ℝ) (P : IntervalPartition a b) : ℝ :=
  ∑ i : Fin P.n, lowerTag f P i * P.delta i

/-- Upper Darboux sum `U(P, f) = ∑ Mᵢ Δxᵢ`. -/
@[kb "lebl2026" "Definition 5.1.1, p. 181"]
noncomputable def upperDarbouxSum (f : ℝ → ℝ) (P : IntervalPartition a b) : ℝ :=
  ∑ i : Fin P.n, upperTag f P i * P.delta i

/-- Proposition 5.1.2: If `f : [a, b] → ℝ` is bounded with `m ≤ f x ≤ M` on
`[a, b]`, then for every partition `P` of `[a, b]` we have
`m * (b - a) ≤ L(P, f) ≤ U(P, f) ≤ M * (b - a)`. -/
@[kb "lebl2026" "Proposition 5.1.2, p. 182"]
lemma lower_upper_sum_bounds {f : ℝ → ℝ} {a b m M : ℝ}
    (hmin : ∀ x ∈ Set.Icc a b, m ≤ f x) (hmax : ∀ x ∈ Set.Icc a b, f x ≤ M)
    (P : IntervalPartition a b) :
    m * (b - a) ≤ lowerDarbouxSum f P ∧
      lowerDarbouxSum f P ≤ upperDarbouxSum f P ∧
      upperDarbouxSum f P ≤ M * (b - a) := by
  classical
  have sum_succ_sub_castSucc : ∀ {n : ℕ} (g : Fin (n + 1) → ℝ),
      (∑ i : Fin n, (g i.succ - g (Fin.castSucc i))) = g (Fin.last n) - g 0 := by
    intro n g
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hsum :=
          (Fin.sum_univ_succ (f := fun i : Fin (n + 1) => (g i.succ - g (Fin.castSucc i))))
        have hih : (∑ i : Fin n, (g (i.succ).succ - g (Fin.castSucc (i.succ)))) =
            g (Fin.last (n + 1)) - g 1 := by
          simpa using (ih (g := fun j : Fin (n + 1) => g j.succ))
        calc
          (∑ i : Fin (n + 1), (g i.succ - g (Fin.castSucc i)))
              = (g (Fin.succ 0) - g (Fin.castSucc 0)) +
                  ∑ i : Fin n, (g (i.succ).succ - g (Fin.castSucc (i.succ))) := hsum
          _ = (g (Fin.succ 0) - g (Fin.castSucc 0)) + (g (Fin.last (n + 1)) - g 1) := by
                rw [hih]
          _ = (g 1 - g 0) + (g (Fin.last (n + 1)) - g 1) := by
                simp
          _ = g (Fin.last (n + 1)) - g 0 := by ring
  have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
    refine sub_nonneg.mpr ?_
    exact le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
  have hsum_delta : (∑ i : Fin P.n, P.delta i) = b - a := by
    have h := sum_succ_sub_castSucc (g := P.points)
    simpa [IntervalPartition.delta, P.left_eq, P.right_eq, Fin.last] using h
  have hsub (i : Fin P.n) :
      Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) ⊆ Set.Icc a b := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hmono : Monotone P.points := P.mono.monotone
    have hleft : a ≤ P.points (Fin.castSucc i) := by
      have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
      simpa [P.left_eq] using h0
    have hright : P.points i.succ ≤ b := by
      have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
      simpa [P.right_eq, Fin.last] using hlast
    exact ⟨le_trans hleft hx1, le_trans hx2 hright⟩
  have htag_bounds (i : Fin P.n) :
      m ≤ lowerTag f P i ∧ lowerTag f P i ≤ upperTag f P i ∧ upperTag f P i ≤ M := by
    have hleft_le : P.points (Fin.castSucc i) ≤ P.points i.succ :=
      le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
    have hxIcc : P.points (Fin.castSucc i) ∈
        Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
      exact ⟨le_rfl, hleft_le⟩
    have hnonempty : (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
      refine ⟨f (P.points (Fin.castSucc i)), ?_⟩
      exact ⟨P.points (Fin.castSucc i), hxIcc, rfl⟩
    have hbelow : BddBelow (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
      refine ⟨m, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmin x (hsub i hx)
    have habove : BddAbove (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
      refine ⟨M, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmax x (hsub i hx)
    have hmin_i : m ≤ lowerTag f P i := by
      refine le_csInf hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmin x (hsub i hx)
    have hmax_i : upperTag f P i ≤ M := by
      refine csSup_le hnonempty ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmax x (hsub i hx)
    have hminmax : lowerTag f P i ≤ upperTag f P i := by
      have hlow : lowerTag f P i ≤ f (P.points (Fin.castSucc i)) := by
        refine csInf_le hbelow ?_
        exact ⟨P.points (Fin.castSucc i), hxIcc, rfl⟩
      have hupp : f (P.points (Fin.castSucc i)) ≤ upperTag f P i := by
        refine le_csSup habove ?_
        exact ⟨P.points (Fin.castSucc i), hxIcc, rfl⟩
      exact le_trans hlow hupp
    exact ⟨hmin_i, ⟨hminmax, hmax_i⟩⟩
  have hminsum : ∑ i : Fin P.n, m * P.delta i ≤ lowerDarbouxSum f P := by
    simpa [lowerDarbouxSum] using
      (Finset.sum_le_sum (by
        intro i hi
        exact mul_le_mul_of_nonneg_right (htag_bounds i).1 (hdelta_nonneg i)))
  have hmid : lowerDarbouxSum f P ≤ upperDarbouxSum f P := by
    simpa [lowerDarbouxSum, upperDarbouxSum] using
      (Finset.sum_le_sum (by
        intro i hi
        exact mul_le_mul_of_nonneg_right (htag_bounds i).2.1 (hdelta_nonneg i)))
  have hmaxsum : upperDarbouxSum f P ≤ ∑ i : Fin P.n, M * P.delta i := by
    simpa [upperDarbouxSum] using
      (Finset.sum_le_sum (by
        intro i hi
        exact mul_le_mul_of_nonneg_right (htag_bounds i).2.2 (hdelta_nonneg i)))
  have hmin : m * (b - a) ≤ lowerDarbouxSum f P := by
    calc
      m * (b - a) = m * (∑ i : Fin P.n, P.delta i) := by
        simp [hsum_delta]
      _ = ∑ i : Fin P.n, m * P.delta i := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n))) (f := fun i => P.delta i) m)
      _ ≤ lowerDarbouxSum f P := hminsum
  have hmax : upperDarbouxSum f P ≤ M * (b - a) := by
    calc
      upperDarbouxSum f P ≤ ∑ i : Fin P.n, M * P.delta i := hmaxsum
      _ = M * (∑ i : Fin P.n, P.delta i) := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n))) (f := fun i => P.delta i) M).symm
      _ = M * (b - a) := by
        simp [hsum_delta]
  exact ⟨hmin, hmid, hmax⟩

/-- Definition 5.1.3: The lower Darboux integral `∫̲_a^b f` is the supremum of
all lower Darboux sums over partitions of `[a, b]`; the upper Darboux integral
`∫̅_a^b f` is the infimum of all upper Darboux sums over partitions of
`[a, b]`. We also write these without an explicit integration variable. -/
@[kb "lebl2026" "Definition 5.1.3, p. 182"]
noncomputable def lowerDarbouxIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P))

/-- See `lowerDarbouxIntegral` for the description of the lower and upper
Darboux integrals. -/
@[kb "lebl2026" "Definition 5.1.3, p. 182"]
noncomputable def upperDarbouxIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P))


/-- Definition 5.1.6: A partition `P̃` of `[a, b]` is a refinement of a
partition `P` if, viewed as sets of partition points, `P ⊆ P̃`. -/
@[kb "lebl2026" "Definition 5.1.6, p. 183"]
def IntervalPartition.IsRefinement (P Q : IntervalPartition a b) : Prop :=
  Set.range P.points ⊆ Set.range Q.points

/-- Proposition 5.1.7: For a bounded function `f : [a, b] → ℝ`, if `P̃` is a
refinement of a partition `P` of `[a, b]`, then `L(P, f) ≤ L(P̃, f)` and
`U(P̃, f) ≤ U(P, f)`. -/
@[kb "lebl2026" "Proposition 5.1.7, p. 183"]
lemma lower_upper_sum_refinement {f : ℝ → ℝ} {a b : ℝ}
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    {P Q : IntervalPartition a b} (hPQ : IntervalPartition.IsRefinement P Q) :
    lowerDarbouxSum f P ≤ lowerDarbouxSum f Q ∧
      upperDarbouxSum f Q ≤ upperDarbouxSum f P := by
  classical
  rcases hbound with ⟨M, hM⟩
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ f x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, f x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2

  have subinterval_subset (R : IntervalPartition a b) (i : Fin R.n) :
      Set.Icc (R.points (Fin.castSucc i)) (R.points i.succ) ⊆ Set.Icc a b := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hmono : Monotone R.points := R.mono.monotone
    have hleft : a ≤ R.points (Fin.castSucc i) := by
      have h0 : R.points 0 ≤ R.points (Fin.castSucc i) := hmono (Fin.zero_le _)
      simpa [R.left_eq] using h0
    have hright : R.points i.succ ≤ b := by
      have hlast : R.points i.succ ≤ R.points (Fin.last R.n) := hmono (Fin.le_last _)
      simpa [R.right_eq, Fin.last] using hlast
    exact ⟨le_trans hleft hx1, le_trans hx2 hright⟩

  have hnonempty (R : IntervalPartition a b) (i : Fin R.n) :
      (f '' Set.Icc (R.points (Fin.castSucc i)) (R.points i.succ)).Nonempty := by
    have hle : R.points (Fin.castSucc i) ≤ R.points i.succ :=
      le_of_lt (R.mono (Fin.castSucc_lt_succ (i := i)))
    refine ⟨f (R.points (Fin.castSucc i)), ?_⟩
    exact ⟨R.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩

  have hbddBelow (R : IntervalPartition a b) (i : Fin R.n) :
      BddBelow (f '' Set.Icc (R.points (Fin.castSucc i)) (R.points i.succ)) := by
    refine ⟨-M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmin x (subinterval_subset R i hx)

  have hbddAbove (R : IntervalPartition a b) (i : Fin R.n) :
      BddAbove (f '' Set.Icc (R.points (Fin.castSucc i)) (R.points i.succ)) := by
    refine ⟨M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hmax x (subinterval_subset R i hx)

  have lowerTag_mono {i : Fin P.n} {q : Fin Q.n}
      (hsub : Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ) ⊆
        Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) :
      lowerTag f P i ≤ lowerTag f Q q := by
    have hsubset :
        f '' Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ) ⊆
          f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hsub hx, rfl⟩
    have hle :
        sInf (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) ≤
          sInf (f '' Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ)) :=
      csInf_le_csInf (hbddBelow P i) (hnonempty Q q) hsubset
    simpa [lowerTag] using hle

  have upperTag_mono {i : Fin P.n} {q : Fin Q.n}
      (hsub : Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ) ⊆
        Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) :
      upperTag f Q q ≤ upperTag f P i := by
    have hsubset :
        f '' Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ) ⊆
          f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, hsub hx, rfl⟩
    have hle :
        sSup (f '' Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ)) ≤
          sSup (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) :=
      csSup_le_csSup (hbddAbove P i) (hnonempty Q q) hsubset
    simpa [upperTag] using hle

  have hk : ∀ i : Fin (P.n + 1), ∃ j : Fin (Q.n + 1), Q.points j = P.points i := by
    intro i
    have : P.points i ∈ Set.range Q.points := hPQ ⟨i, rfl⟩
    rcases this with ⟨j, hj⟩
    exact ⟨j, hj⟩
  classical
  choose k hk_eq using hk
  have hk_mono : StrictMono k := by
    intro i j hij
    have hP : P.points i < P.points j := P.mono hij
    have hQ : Q.points (k i) < Q.points (k j) := by simpa [hk_eq] using hP
    have hmonoQ : Monotone Q.points := Q.mono.monotone
    by_contra hnot
    have hle : k j ≤ k i := le_of_not_gt hnot
    have hle' : Q.points (k j) ≤ Q.points (k i) := hmonoQ hle
    exact (not_lt_of_ge hle') hQ
  have hk0 : k 0 = 0 := by
    have h0 : Q.points (k 0) = Q.points 0 := by
      simpa [P.left_eq, Q.left_eq] using (hk_eq 0)
    exact (Q.mono.injective h0)
  have hklast : k (Fin.last P.n) = Fin.last Q.n := by
    have hlast : Q.points (k (Fin.last P.n)) = Q.points (Fin.last Q.n) := by
      simpa [P.right_eq, Q.right_eq, Fin.last] using (hk_eq (Fin.last P.n))
    exact (Q.mono.injective hlast)

  have sum_Ico_succ_sub (g : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
      (Finset.sum (Finset.Ico m n) fun q => g (q + 1) - g q) = g n - g m := by
    have h :
        ∀ t : ℕ,
          (Finset.sum (Finset.Ico m (m + t)) fun q => g (q + 1) - g q) = g (m + t) - g m := by
      intro t
      induction t with
      | zero =>
          simp
      | succ t ih =>
          have hm : m ≤ m + t := Nat.le_add_right _ _
          have hmt : m + t ≤ m + t + 1 := Nat.le_succ _
          have hstep :=
            (Finset.sum_Ico_consecutive (f := fun q => g (q + 1) - g q) hm hmt).symm
          calc
            Finset.sum (Finset.Ico m (m + t + 1)) (fun q => g (q + 1) - g q)
                =
                Finset.sum (Finset.Ico m (m + t)) (fun q => g (q + 1) - g q) +
                  Finset.sum (Finset.Ico (m + t) (m + t + 1)) (fun q => g (q + 1) - g q) := by
                  simpa [Nat.add_assoc] using hstep
            _ =
                Finset.sum (Finset.Ico m (m + t)) (fun q => g (q + 1) - g q) +
                  (g (m + t + 1) - g (m + t)) := by
                  simp
            _ = (g (m + t) - g m) + (g (m + t + 1) - g (m + t)) := by
                  rw [ih]
            _ = g (m + t + 1) - g m := by ring
    have h' := h (n - m)
    simpa [Nat.add_sub_of_le hmn] using h'

  have delta_eq_sum_refine (i : Fin P.n) :
      P.delta i =
        Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val) fun q =>
          if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0 := by
    classical
    let m : ℕ := (k (Fin.castSucc i)).val
    let n : ℕ := (k i.succ).val
    have hmn : m ≤ n := by
      have hlt : k (Fin.castSucc i) < k i.succ := hk_mono (Fin.castSucc_lt_succ (i := i))
      exact Nat.le_of_lt (Fin.lt_def.mp hlt)
    have hn_le : n ≤ Q.n := Nat.lt_succ_iff.mp (k i.succ).isLt
    have hm_le : m ≤ Q.n := Nat.lt_succ_iff.mp (k (Fin.castSucc i)).isLt
    let g : ℕ → ℝ := fun t =>
      if ht : t ≤ Q.n then Q.points ⟨t, Nat.lt_succ_iff.mpr ht⟩ else Q.points (Fin.last Q.n)
    have g_eq {t : ℕ} (ht : t ≤ Q.n) :
        g t = Q.points ⟨t, Nat.lt_succ_iff.mpr ht⟩ := by
      simp [g, ht]
    have g_n : g n = Q.points (k i.succ) := by
      have hfin : (⟨n, Nat.lt_succ_iff.mpr hn_le⟩ : Fin (Q.n + 1)) = k i.succ := by
        apply Fin.ext
        simp [n]
      simp [g_eq, hn_le, hfin]
    have g_m : g m = Q.points (k (Fin.castSucc i)) := by
      have hfin : (⟨m, Nat.lt_succ_iff.mpr hm_le⟩ : Fin (Q.n + 1)) = k (Fin.castSucc i) := by
        apply Fin.ext
        simp [m]
      simp [g_eq, hm_le, hfin]
    have hsum :
        Finset.sum (Finset.Ico m n) (fun q => g (q + 1) - g q) =
          Finset.sum (Finset.Ico m n) (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      have hq_lt_n : q < n := (Finset.mem_Ico.mp hq).2
      have hq_lt : q < Q.n := lt_of_lt_of_le hq_lt_n hn_le
      have hq_le : q ≤ Q.n := le_of_lt hq_lt
      have hq1_le : q + 1 ≤ Q.n := by
        have hq1_le' : q + 1 ≤ n := Nat.succ_le_of_lt hq_lt_n
        exact le_trans hq1_le' hn_le
      simp [g, hq_le, hq1_le, IntervalPartition.delta, hq_lt]
    have hsum' := sum_Ico_succ_sub g m n hmn
    have hsum'' :
        Finset.sum (Finset.Ico m n) (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0) =
          Q.points (k i.succ) - Q.points (k (Fin.castSucc i)) := by
      calc
        Finset.sum (Finset.Ico m n) (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)
            = Finset.sum (Finset.Ico m n) (fun q => g (q + 1) - g q) := by
                symm
                exact hsum
        _ = g n - g m := hsum'
        _ = Q.points (k i.succ) - Q.points (k (Fin.castSucc i)) := by
              simp [g_n, g_m]
    have hP : P.delta i = Q.points (k i.succ) - Q.points (k (Fin.castSucc i)) := by
      simp [IntervalPartition.delta, hk_eq]
    have hP' : P.delta i =
        Finset.sum (Finset.Ico m n) (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0) := by
      exact hP.trans hsum''.symm
    simpa [m, n] using hP'

  have block_subinterval_subset {i : Fin P.n} {q : Fin Q.n}
      (hq : q.val ∈ Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val) :
      Set.Icc (Q.points (Fin.castSucc q)) (Q.points q.succ) ⊆
        Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hq_lt_n : q.val < (k i.succ).val := (Finset.mem_Ico.mp hq).2
    have hq_ge : (k (Fin.castSucc i)).val ≤ q.val := (Finset.mem_Ico.mp hq).1
    have hmonoQ : Monotone Q.points := Q.mono.monotone
    have hleft :
        Q.points (k (Fin.castSucc i)) ≤ Q.points (Fin.castSucc q) := by
      have hq_ge' :
          k (Fin.castSucc i) ≤ (Fin.castSucc q : Fin (Q.n + 1)) := by
        exact (Fin.le_iff_val_le_val).mpr hq_ge
      exact hmonoQ hq_ge'
    have hright :
        Q.points q.succ ≤ Q.points (k i.succ) := by
      have hq_succ_le : (q.val + 1) ≤ (k i.succ).val := Nat.succ_le_of_lt hq_lt_n
      have hq_succ_le' : (q.succ : Fin (Q.n + 1)) ≤ k i.succ := by
        exact (Fin.le_iff_val_le_val).mpr hq_succ_le
      exact hmonoQ hq_succ_le'
    have hk_left : Q.points (k (Fin.castSucc i)) = P.points (Fin.castSucc i) := hk_eq _
    have hk_right : Q.points (k i.succ) = P.points i.succ := hk_eq _
    exact ⟨by
      have := le_trans (by simpa [hk_left] using hleft) hx1
      exact this, by
      have := le_trans hx2 (by simpa [hk_right] using hright)
      exact this⟩

  -- TODO: use `k` to decompose each `P.delta` as a sum of `Q.delta` over
  -- consecutive blocks, then compare tags via `lowerTag_mono` and `upperTag_mono`.
  -- This yields the required inequalities for lower and upper sums.
  have hdelta_nonneg (q : Fin Q.n) : 0 ≤ Q.delta q := by
    refine sub_nonneg.mpr ?_
    exact le_of_lt (Q.mono (Fin.castSucc_lt_succ (i := q)))

  let F_lower : ℕ → ℝ := fun q =>
    if hq : q < Q.n then lowerTag f Q ⟨q, hq⟩ * Q.delta ⟨q, hq⟩ else 0
  let F_upper : ℕ → ℝ := fun q =>
    if hq : q < Q.n then upperTag f Q ⟨q, hq⟩ * Q.delta ⟨q, hq⟩ else 0

  have lower_block_sum_le (i : Fin P.n) :
      lowerTag f P i * P.delta i ≤
        Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
          (fun q => F_lower q) := by
    classical
    calc
      lowerTag f P i * P.delta i
          =
          lowerTag f P i *
            Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
              (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0) := by
            simp [delta_eq_sum_refine]
      _ =
          Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => lowerTag f P i * (if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)) := by
            simpa using
              (Finset.mul_sum
                (s := Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
                (f := fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)
                (a := lowerTag f P i))
      _ ≤
          Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => F_lower q) := by
            refine Finset.sum_le_sum ?_
            intro q hq
            by_cases hq' : q < Q.n
            · have hqmem :
                  (⟨q, hq'⟩ : Fin Q.n).val ∈
                    Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val := by
                simpa using hq
              have hsub :
                  Set.Icc (Q.points (Fin.castSucc (⟨q, hq'⟩ : Fin Q.n)))
                      (Q.points ((⟨q, hq'⟩ : Fin Q.n).succ)) ⊆
                    Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
                block_subinterval_subset (i := i) (q := ⟨q, hq'⟩) hqmem
              have htag : lowerTag f P i ≤ lowerTag f Q ⟨q, hq'⟩ :=
                lowerTag_mono hsub
              have hmul := mul_le_mul_of_nonneg_right htag (hdelta_nonneg ⟨q, hq'⟩)
              simpa [F_lower, hq'] using hmul
            · simp [F_lower, hq']

  have upper_block_sum_le (i : Fin P.n) :
      Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
        (fun q => F_upper q) ≤
        upperTag f P i * P.delta i := by
    classical
    have hsum_le :
        Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => F_upper q) ≤
          Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => upperTag f P i * (if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)) := by
      refine Finset.sum_le_sum ?_
      intro q hq
      by_cases hq' : q < Q.n
      · have hqmem :
            (⟨q, hq'⟩ : Fin Q.n).val ∈
              Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val := by
          simpa using hq
        have hsub :
            Set.Icc (Q.points (Fin.castSucc (⟨q, hq'⟩ : Fin Q.n)))
                (Q.points ((⟨q, hq'⟩ : Fin Q.n).succ)) ⊆
              Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) :=
          block_subinterval_subset (i := i) (q := ⟨q, hq'⟩) hqmem
        have htag : upperTag f Q ⟨q, hq'⟩ ≤ upperTag f P i :=
          upperTag_mono hsub
        have hmul := mul_le_mul_of_nonneg_right htag (hdelta_nonneg ⟨q, hq'⟩)
        simpa [F_upper, hq'] using hmul
      · simp [F_upper, hq']
    calc
      Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
        (fun q => F_upper q)
          ≤
          Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => upperTag f P i * (if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)) := hsum_le
      _ =
          upperTag f P i *
            Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
              (fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0) := by
            symm
            simpa using
              (Finset.mul_sum
                (s := Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
                (f := fun q => if hq : q < Q.n then Q.delta ⟨q, hq⟩ else 0)
                (a := upperTag f P i))
      _ = upperTag f P i * P.delta i := by
            simp [delta_eq_sum_refine]

  have sum_blocks_eq_range (F : ℕ → ℝ) :
      (∑ i : Fin P.n,
        Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
          (fun q => F q))
        =
        Finset.sum (Finset.Ico 0 (k (Fin.last P.n)).val) (fun q => F q) := by
    classical
    let block : ℕ → ℝ := fun i =>
      if h : i < P.n then
        Finset.sum
          (Finset.Ico (k (Fin.castSucc (⟨i, h⟩ : Fin P.n))).val
            (k (⟨i, h⟩ : Fin P.n).succ).val)
          (fun q => F q)
      else 0
    have hsum_fin :
        (∑ i : Fin P.n,
          Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
            (fun q => F q)) =
          Finset.sum (Finset.range P.n) (fun i => block i) := by
      have hsum_eq :
          (∑ i : Fin P.n,
            Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
              (fun q => F q)) =
            ∑ i : Fin P.n, block i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        cases' i with i hi'
        simp [block, hi']
      have hsum_range' :
          (∑ i : Fin P.n, block i) =
            Finset.sum (Finset.range P.n) (fun i => block i) := by
        simpa using (Fin.sum_univ_eq_sum_range (f := block) (n := P.n))
      exact hsum_eq.trans hsum_range'
    have hsum_range :
        ∀ t (ht : t ≤ P.n),
          Finset.sum (Finset.range t) (fun i => block i) =
            Finset.sum (Finset.Ico 0 (k ⟨t, Nat.lt_succ_of_le ht⟩).val)
              (fun q => F q) := by
      intro t ht
      induction t with
      | zero =>
          have hzero : (⟨0, Nat.lt_succ_of_le ht⟩ : Fin (P.n + 1)) = 0 := by
            apply Fin.ext
            simp
          simp [hzero, hk0]
      | succ t ih =>
          have ht' : t ≤ P.n := Nat.le_of_succ_le ht
          have ht_lt : t < P.n := Nat.lt_of_succ_le ht
          have hcast :
              (Fin.castSucc (⟨t, ht_lt⟩ : Fin P.n) : Fin (P.n + 1)) =
                ⟨t, Nat.lt_succ_of_le ht'⟩ := by
            apply Fin.ext
            simp
          have hsucc :
              ((⟨t, ht_lt⟩ : Fin P.n).succ : Fin (P.n + 1)) =
                ⟨t + 1, Nat.lt_succ_of_le ht⟩ := by
            apply Fin.ext
            simp
          have hblock :
              block t =
                Finset.sum (Finset.Ico (k ⟨t, Nat.lt_succ_of_le ht'⟩).val
                                    (k ⟨t + 1, Nat.lt_succ_of_le ht⟩).val)
                  (fun q => F q) := by
            simp [block, ht_lt]
          have hle :
              (k ⟨t, Nat.lt_succ_of_le ht'⟩).val ≤
                (k ⟨t + 1, Nat.lt_succ_of_le ht⟩).val := by
            have hlt :
                k ⟨t, Nat.lt_succ_of_le ht'⟩ < k ⟨t + 1, Nat.lt_succ_of_le ht⟩ := by
              apply hk_mono
              exact (Fin.lt_def).mpr (Nat.lt_succ_self t)
            exact le_of_lt (Fin.lt_def.mp hlt)
          calc
            Finset.sum (Finset.range (t + 1)) (fun i => block i)
                = Finset.sum (Finset.range t) (fun i => block i) + block t := by
                    simpa using (Finset.sum_range_succ (f := block) t)
            _ =
                Finset.sum (Finset.Ico 0 (k ⟨t, Nat.lt_succ_of_le ht'⟩).val)
                  (fun q => F q) + block t := by
                    rw [ih ht']
            _ =
                Finset.sum (Finset.Ico 0 (k ⟨t + 1, Nat.lt_succ_of_le ht⟩).val)
                  (fun q => F q) := by
                    have hconsec :=
                      (Finset.sum_Ico_consecutive (f := F) (m := 0)
                        (n := (k ⟨t, Nat.lt_succ_of_le ht'⟩).val)
                        (k := (k ⟨t + 1, Nat.lt_succ_of_le ht⟩).val)
                        (Nat.zero_le _) hle)
                    simpa [hblock] using hconsec
    have hsum_final :
        Finset.sum (Finset.range P.n) (fun i => block i) =
          Finset.sum (Finset.Ico 0 (k (Fin.last P.n)).val) (fun q => F q) := by
      have h := hsum_range P.n le_rfl
      have hlast' :
          (⟨P.n, Nat.lt_succ_of_le le_rfl⟩ : Fin (P.n + 1)) = Fin.last P.n := by
        apply Fin.ext
        simp [Fin.last]
      simpa [hlast'] using h
    exact hsum_fin.trans hsum_final

  have hlower :
      lowerDarbouxSum f P ≤ lowerDarbouxSum f Q := by
    have hsum_lower :
        lowerDarbouxSum f P ≤
          Finset.sum (Finset.Ico 0 Q.n) (fun q => F_lower q) := by
      calc
        lowerDarbouxSum f P
            ≤ ∑ i : Fin P.n,
                Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
                  (fun q => F_lower q) := by
                  simpa [lowerDarbouxSum] using
                    (Finset.sum_le_sum (by
                      intro i hi
                      exact lower_block_sum_le i))
        _ =
            Finset.sum (Finset.Ico 0 (k (Fin.last P.n)).val) (fun q => F_lower q) := by
              exact sum_blocks_eq_range F_lower
        _ =
            Finset.sum (Finset.Ico 0 (Fin.last Q.n).val) (fun q => F_lower q) := by
              simp [hklast]
        _ = Finset.sum (Finset.Ico 0 Q.n) (fun q => F_lower q) := by
              simp [Fin.last]
    have hsum_lower_fin :
        lowerDarbouxSum f Q =
          Finset.sum (Finset.Ico 0 Q.n) (fun q => F_lower q) := by
      have hsum_eq :
          lowerDarbouxSum f Q = ∑ q : Fin Q.n, F_lower q := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro q hq
        have hq' : (⟨(q : ℕ), q.isLt⟩ : Fin Q.n) = q := by
          apply Fin.ext
          simp
        simp [F_lower, q.isLt, hq']
      have hsum_range :
          (∑ q : Fin Q.n, F_lower q) =
            Finset.sum (Finset.range Q.n) (fun q => F_lower q) := by
        simpa using (Fin.sum_univ_eq_sum_range (f := F_lower) (n := Q.n))
      have hsum_range' :
          (∑ q : Fin Q.n, F_lower q) =
            Finset.sum (Finset.Ico 0 Q.n) (fun q => F_lower q) := by
        have hsum_range' := hsum_range
        rw [Finset.range_eq_Ico] at hsum_range'
        exact hsum_range'
      exact hsum_eq.trans hsum_range'
    calc
      lowerDarbouxSum f P ≤
          Finset.sum (Finset.Ico 0 Q.n) (fun q => F_lower q) := hsum_lower
      _ = lowerDarbouxSum f Q := by
            symm
            exact hsum_lower_fin

  have hupper :
      upperDarbouxSum f Q ≤ upperDarbouxSum f P := by
    have hsum_upper :
        Finset.sum (Finset.Ico 0 Q.n) (fun q => F_upper q) ≤ upperDarbouxSum f P := by
      calc
        Finset.sum (Finset.Ico 0 Q.n) (fun q => F_upper q)
            = Finset.sum (Finset.Ico 0 (Fin.last Q.n).val) (fun q => F_upper q) := by
                  simp [Fin.last]
        _ = Finset.sum (Finset.Ico 0 (k (Fin.last P.n)).val) (fun q => F_upper q) := by
              simp [hklast]
        _ = ∑ i : Fin P.n,
                Finset.sum (Finset.Ico (k (Fin.castSucc i)).val (k i.succ).val)
                  (fun q => F_upper q) := by
              symm
              exact sum_blocks_eq_range F_upper
        _ ≤ ∑ i : Fin P.n, upperTag f P i * P.delta i := by
              simpa [upperDarbouxSum] using
                (Finset.sum_le_sum (by
                  intro i hi
                  exact upper_block_sum_le i))
        _ = upperDarbouxSum f P := by
              simp [upperDarbouxSum]
    have hsum_upper_fin :
        upperDarbouxSum f Q =
          Finset.sum (Finset.Ico 0 Q.n) (fun q => F_upper q) := by
      have hsum_eq :
          upperDarbouxSum f Q = ∑ q : Fin Q.n, F_upper q := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro q hq
        have hq' : (⟨(q : ℕ), q.isLt⟩ : Fin Q.n) = q := by
          apply Fin.ext
          simp
        simp [F_upper, q.isLt, hq']
      have hsum_range :
          (∑ q : Fin Q.n, F_upper q) =
            Finset.sum (Finset.range Q.n) (fun q => F_upper q) := by
        simpa using (Fin.sum_univ_eq_sum_range (f := F_upper) (n := Q.n))
      have hsum_range' :
          (∑ q : Fin Q.n, F_upper q) =
            Finset.sum (Finset.Ico 0 Q.n) (fun q => F_upper q) := by
        have hsum_range' := hsum_range
        rw [Finset.range_eq_Ico] at hsum_range'
        exact hsum_range'
      exact hsum_eq.trans hsum_range'
    calc
      upperDarbouxSum f Q =
          Finset.sum (Finset.Ico 0 Q.n) (fun q => F_upper q) := hsum_upper_fin
      _ ≤ upperDarbouxSum f P := hsum_upper

  exact ⟨hlower, hupper⟩

/-- A partition exists whenever the interval is nonempty. -/
lemma intervalPartition_nonempty {a b : ℝ} (hab : a ≤ b) :
    Nonempty (IntervalPartition a b) := by
  classical
  by_cases h : a = b
  · refine ⟨{ n := 0, points := fun _ => a, mono := ?_, left_eq := rfl, right_eq := by simp [h] }⟩
    simpa using (Subsingleton.strictMono (f := fun _ : Fin 1 => a))
  · have hlt : a < b := lt_of_le_of_ne hab h
    refine  ⟨
      {
        n := 1,
        points := fun i => if (i : ℕ) = 0 then a else b,
        mono := ?_, left_eq := by simp, right_eq := by simp }
      ⟩
    refine
      (Fin.strictMono_iff_lt_succ
        (f := fun i : Fin 2 => if (i : ℕ) = 0 then a else b)).2 ?_
    intro i
    have hi : i = 0 := Fin.eq_zero i
    simp [hi, hlt]

/-- Two partitions admit a common refinement given by the union of their points. -/
lemma intervalPartition_common_refinement {a b : ℝ} (P1 P2 : IntervalPartition a b) :
    ∃ Q : IntervalPartition a b,
      IntervalPartition.IsRefinement P1 Q ∧ IntervalPartition.IsRefinement P2 Q := by
  classical
  let s : Finset ℝ :=
    Finset.image P1.points Finset.univ ∪ Finset.image P2.points Finset.univ
  have ha_mem : a ∈ s := by
    have : a ∈ Finset.image P1.points Finset.univ := by
      refine Finset.mem_image.mpr ?_
      refine ⟨0, by simp, ?_⟩
      simp [P1.left_eq]
    exact Finset.mem_union.mpr (Or.inl this)
  have hs_nonempty : s.Nonempty := ⟨a, ha_mem⟩
  have hs_card_pos : 0 < s.card := Finset.card_pos.mpr hs_nonempty
  let k : ℕ := s.card
  have hk : s.card = k := rfl
  let n : ℕ := k - 1
  have hnk : n + 1 = k := by
    dsimp [n, k]
    exact Nat.succ_pred_eq_of_pos hs_card_pos
  let points : Fin (n + 1) → ℝ := fun i => s.orderEmbOfFin hk (Fin.cast hnk i)
  have hmono : StrictMono points :=
    (s.orderEmbOfFin hk).strictMono.comp (Fin.cast_strictMono hnk)
  have hleft_le : ∀ x ∈ s, a ≤ x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · rcases Finset.mem_image.mp hx1 with ⟨i, _, rfl⟩
      have hmonoP1 : Monotone P1.points := P1.mono.monotone
      have h0 : P1.points 0 ≤ P1.points i := hmonoP1 (Fin.zero_le _)
      simpa [P1.left_eq] using h0
    · rcases Finset.mem_image.mp hx2 with ⟨i, _, rfl⟩
      have hmonoP2 : Monotone P2.points := P2.mono.monotone
      have h0 : P2.points 0 ≤ P2.points i := hmonoP2 (Fin.zero_le _)
      simpa [P2.left_eq] using h0
  have hright_le : ∀ x ∈ s, x ≤ b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · rcases Finset.mem_image.mp hx1 with ⟨i, _, rfl⟩
      have hmonoP1 : Monotone P1.points := P1.mono.monotone
      have hlast : P1.points i ≤ P1.points (Fin.last P1.n) := hmonoP1 (Fin.le_last _)
      have hlast' := hlast
      simp [P1.right_eq, Fin.last] at hlast'
      exact hlast'
    · rcases Finset.mem_image.mp hx2 with ⟨i, _, rfl⟩
      have hmonoP2 : Monotone P2.points := P2.mono.monotone
      have hlast : P2.points i ≤ P2.points (Fin.last P2.n) := hmonoP2 (Fin.le_last _)
      have hlast' := hlast
      simp [P2.right_eq, Fin.last] at hlast'
      exact hlast'
  have hmin : s.min' hs_nonempty = a := by
    refine (Finset.min'_eq_iff (s:=s) (H:=hs_nonempty) a).2 ?_
    refine ⟨ha_mem, ?_⟩
    intro x hx
    exact hleft_le x hx
  have hb_mem : b ∈ s := by
    have : b ∈ Finset.image P1.points Finset.univ := by
      refine Finset.mem_image.mpr ?_
      refine ⟨Fin.last P1.n, by simp, ?_⟩
      simp [P1.right_eq, Fin.last]
    exact Finset.mem_union.mpr (Or.inl this)
  have hmax : s.max' hs_nonempty = b := by
    refine (Finset.max'_eq_iff (s:=s) (H:=hs_nonempty) b).2 ?_
    refine ⟨hb_mem, ?_⟩
    intro x hx
    exact hright_le x hx
  have hleft_eq : points 0 = a := by
    have hz : 0 < k := hs_card_pos
    have h0 : (Fin.cast hnk 0 : Fin k) = ⟨0, hz⟩ := by
      apply Fin.ext
      simp
    calc
      points 0 = s.orderEmbOfFin hk (Fin.cast hnk 0) := rfl
      _ = s.orderEmbOfFin hk ⟨0, hz⟩ := by simp [h0]
      _ = s.min' hs_nonempty := by
            simpa [hk] using (Finset.orderEmbOfFin_zero (s:=s) (h:=hk) hz)
      _ = a := hmin
  have hright_eq : points (Fin.last n) = b := by
    have hz : 0 < k := hs_card_pos
    have hlast : (Fin.cast hnk (Fin.last n) : Fin k) =
        ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ := by
      apply Fin.ext
      simp [n, k]
    calc
      points (Fin.last n) = s.orderEmbOfFin hk (Fin.cast hnk (Fin.last n)) := rfl
      _ = s.orderEmbOfFin hk ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ := by
            simp [hlast]
      _ = s.max' hs_nonempty := by
            simpa [hk] using (Finset.orderEmbOfFin_last (s:=s) (h:=hk) hz)
      _ = b := hmax
  let Q : IntervalPartition a b :=
    { n := n
      points := points
      mono := hmono
      left_eq := hleft_eq
      right_eq := by
        simpa [Fin.last] using hright_eq }
  have hsurj : Function.Surjective (Fin.cast hnk) := by
    intro i
    refine ⟨Fin.cast hnk.symm i, ?_⟩
    simp
  have hrange : Set.range points = (s : Set ℝ) := by
    have hrange' : Set.range points = Set.range (s.orderEmbOfFin hk) := by
      exact Function.Surjective.range_comp hsurj (s.orderEmbOfFin hk)
    simpa [Finset.range_orderEmbOfFin (s:=s) (h:=hk)] using hrange'
  have hP1 : IntervalPartition.IsRefinement P1 Q := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    have : P1.points i ∈ (s : Set ℝ) := by
      have : P1.points i ∈ s := by
        apply Finset.mem_union.mpr
        left
        refine Finset.mem_image.mpr ?_
        exact ⟨i, by simp, rfl⟩
      simpa using this
    simpa [Q, hrange] using this
  have hP2 : IntervalPartition.IsRefinement P2 Q := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    have : P2.points i ∈ (s : Set ℝ) := by
      have : P2.points i ∈ s := by
        apply Finset.mem_union.mpr
        right
        refine Finset.mem_image.mpr ?_
        exact ⟨i, by simp, rfl⟩
      simpa using this
    simpa [Q, hrange] using this
  exact ⟨Q, hP1, hP2⟩

/-- A boundedness witness from a two-sided bound on `[a, b]`. -/
lemma bounded_of_between {f : ℝ → ℝ} {a b m M : ℝ}
    (hmin : ∀ x ∈ Set.Icc a b, m ≤ f x) (hmax : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ B := by
  refine ⟨max (-m) M, ?_⟩
  intro x hx
  by_cases hfx : 0 ≤ f x
  · have hM := hmax x hx
    calc
      |f x| = f x := abs_of_nonneg hfx
      _ ≤ M := hM
      _ ≤ max (-m) M := le_max_right _ _
  · have hfxneg : f x < 0 := lt_of_not_ge hfx
    have hminx := hmin x hx
    have hneg : -f x ≤ -m := by
      exact neg_le_neg hminx
    calc
      |f x| = -f x := abs_of_neg hfxneg
      _ ≤ -m := hneg
      _ ≤ max (-m) M := le_max_left _ _

/-- Any lower sum is bounded above by any upper sum. -/
lemma lower_sum_le_upper_sum_any {f : ℝ → ℝ} {a b m M : ℝ}
    (hmin : ∀ x ∈ Set.Icc a b, m ≤ f x) (hmax : ∀ x ∈ Set.Icc a b, f x ≤ M)
    (P1 P2 : IntervalPartition a b) :
    lowerDarbouxSum f P1 ≤ upperDarbouxSum f P2 := by
  classical
  have hbound : ∃ B : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ B :=
    bounded_of_between hmin hmax
  rcases intervalPartition_common_refinement P1 P2 with ⟨Q, hP1Q, hP2Q⟩
  have href1 := lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound hP1Q
  have href2 := lower_upper_sum_refinement (f := f) (a := a) (b := b) hbound hP2Q
  have hmid :=
    (lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hmin hmax Q).2.1
  exact le_trans href1.1 (le_trans hmid href2.2)

/-- Proposition 5.1.8: If a bounded function `f : [a, b] → ℝ` satisfies
`m ≤ f x ≤ M` on `[a, b]`, then the lower and upper Darboux integrals obey
`m * (b - a) ≤ ∫̲_a^b f ≤ ∫̅_a^b f ≤ M * (b - a)`. -/
@[kb "lebl2026" "Proposition 5.1.8, p. 184"]
lemma lower_upper_integral_bounds {f : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hmin : ∀ x ∈ Set.Icc a b, m ≤ f x)
    (hmax : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * (b - a) ≤ lowerDarbouxIntegral f a b ∧
      lowerDarbouxIntegral f a b ≤ upperDarbouxIntegral f a b ∧
      upperDarbouxIntegral f a b ≤ M * (b - a) := by
  classical
  obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
  have hBddAbove :
      BddAbove (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
    refine ⟨M * (b - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hmin hmax P
    exact le_trans hsum.2.1 hsum.2.2
  have hBddBelow :
      BddBelow (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) := by
    refine ⟨m * (b - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have h := lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hmin hmax P
    exact le_trans h.1 h.2.1
  have hnonempty_lower :
      (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)).Nonempty := by
    refine ⟨lowerDarbouxSum f P0, ?_⟩
    exact ⟨P0, rfl⟩
  have hnonempty_upper :
      (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)).Nonempty := by
    refine ⟨upperDarbouxSum f P0, ?_⟩
    exact ⟨P0, rfl⟩
  have hlower : m * (b - a) ≤ lowerDarbouxIntegral f a b := by
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hmin hmax P0
    have hmem :
        lowerDarbouxSum f P0 ∈
          Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P) := ⟨P0, rfl⟩
    have hsup : lowerDarbouxSum f P0 ≤ lowerDarbouxIntegral f a b := by
      have hsup' :
          lowerDarbouxSum f P0 ≤
            sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
        exact le_csSup hBddAbove hmem
      simpa [lowerDarbouxIntegral] using hsup'
    exact le_trans hsum.1 hsup
  have hupper : upperDarbouxIntegral f a b ≤ M * (b - a) := by
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hmin hmax P0
    have hmem :
        upperDarbouxSum f P0 ∈
          Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P) := ⟨P0, rfl⟩
    have hinf : upperDarbouxIntegral f a b ≤ upperDarbouxSum f P0 := by
      have hinf' :
          sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P))
            ≤ upperDarbouxSum f P0 := by
        exact csInf_le hBddBelow hmem
      simpa [upperDarbouxIntegral] using hinf'
    exact le_trans hinf hsum.2.2
  have hmid : lowerDarbouxIntegral f a b ≤ upperDarbouxIntegral f a b := by
    have hle :
        ∀ y ∈ Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P),
          y ≤ upperDarbouxIntegral f a b := by
      intro y hy
      rcases hy with ⟨P1, rfl⟩
      have hle' :
          lowerDarbouxSum f P1 ≤
            sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) := by
        refine le_csInf hnonempty_upper ?_
        intro z hz
        rcases hz with ⟨P2, rfl⟩
        exact lower_sum_le_upper_sum_any (f := f) (a := a) (b := b) (m := m) (M := M)
          hmin hmax P1 P2
      simpa [upperDarbouxIntegral] using hle'
    have hsup :
        sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P))
          ≤ upperDarbouxIntegral f a b :=
      csSup_le hnonempty_lower hle
    simpa [lowerDarbouxIntegral] using hsup
  exact ⟨hlower, hmid, hupper⟩

/-- Definition 5.1.9: A bounded function `f : [a, b] → ℝ` is Riemann
integrable if the lower and upper Darboux integrals coincide. The collection of
such functions on `[a, b]` is denoted `ℛ([a, b])`, and when `f` is Riemann
integrable its integral `∫_a^b f` is the common value of the lower and upper
integrals. -/
@[kb "lebl2026" "Definition 5.1.9, p. 185"]
def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M) ∧
    lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b

/-- The set `ℛ([a, b])` of Riemann integrable functions on `[a, b]`. -/
def riemannIntegrableFunctions (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RiemannIntegrableOn f a b}

/-- The Riemann integral of an integrable function is the common value of the
lower and upper Darboux integrals. -/
@[kb "lebl2026" "Definition 5.1.9, p. 185"]
noncomputable def riemannIntegral (f : ℝ → ℝ) (a b : ℝ)
    (hf : RiemannIntegrableOn f a b) : ℝ :=
  by
    classical
    -- The witness `hf` certifies integrability but the value is given by the
    -- lower Darboux integral.
    let _ := hf
    exact lowerDarbouxIntegral f a b

/-- Proposition 5.1.10: If `f : [a, b] → ℝ` is Riemann integrable and
bounded between `m` and `M` on `[a, b]`, then the integral is bounded by
`m * (b - a)` and `M * (b - a)`. -/
@[kb "lebl2026" "Proposition 5.1.10, p. 185"]
lemma riemannIntegral_bounds {f : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hf : RiemannIntegrableOn f a b)
    (hmin : ∀ x ∈ Set.Icc a b, m ≤ f x) (hmax : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    m * (b - a) ≤ riemannIntegral f a b hf ∧
      riemannIntegral f a b hf ≤ M * (b - a) := by
  classical
  rcases hf with ⟨_, hEq⟩
  have hbounds :=
    lower_upper_integral_bounds (f := f) (a := a) (b := b) (m := m) (M := M) hab hmin hmax
  constructor
  · simpa [riemannIntegral] using hbounds.1
  · have hupper : upperDarbouxIntegral f a b ≤ M * (b - a) := hbounds.2.2
    have hlower : lowerDarbouxIntegral f a b ≤ M * (b - a) := by
      simpa [hEq] using hupper
    simpa [riemannIntegral] using hlower

/-- Example 5.1.11: A constant function `f x = c` is Riemann integrable on
`[a, b]`, and its integral is `c * (b - a)`. -/
@[kb "lebl2026" "Example 5.1.11, p. 186"]
lemma constant_function_riemannIntegral (c a b : ℝ) (hab : a ≤ b) :
    ∃ hf : RiemannIntegrableOn (fun _ : ℝ => c) a b,
      riemannIntegral (fun _ : ℝ => c) a b hf = c * (b - a) := by
  classical
  have hbounds :
      c * (b - a) ≤ lowerDarbouxIntegral (fun _ : ℝ => c) a b ∧
        lowerDarbouxIntegral (fun _ : ℝ => c) a b ≤
            upperDarbouxIntegral (fun _ : ℝ => c) a b ∧
        upperDarbouxIntegral (fun _ : ℝ => c) a b ≤ c * (b - a) := by
    simpa using
      (lower_upper_integral_bounds (f := fun _ : ℝ => c) (a := a) (b := b)
        (m := c) (M := c) hab
        (by intro x hx; simp)
        (by intro x hx; simp))
  have hupper_le_lower :
      upperDarbouxIntegral (fun _ : ℝ => c) a b ≤
        lowerDarbouxIntegral (fun _ : ℝ => c) a b := by
    exact le_trans hbounds.2.2 hbounds.1
  have heq :
      lowerDarbouxIntegral (fun _ : ℝ => c) a b =
        upperDarbouxIntegral (fun _ : ℝ => c) a b := by
    exact le_antisymm hbounds.2.1 hupper_le_lower
  have hlower_eq :
      lowerDarbouxIntegral (fun _ : ℝ => c) a b = c * (b - a) := by
    apply le_antisymm
    · exact le_trans hbounds.2.1 hbounds.2.2
    · exact hbounds.1
  refine ⟨?hf, ?hIntegral⟩
  · refine ⟨?hbound, heq⟩
    refine ⟨|c|, ?_⟩
    intro x hx
    simp
  · simpa [riemannIntegral] using hlower_eq


/-- Proposition 5.1.13: A bounded function `f : [a, b] → ℝ` is Riemann
integrable if for every `ε > 0` there exists a partition `P` of `[a, b]` with
`U(P, f) - L(P, f) < ε`. -/
@[kb "lebl2026" "Proposition 5.1.13, p. 187"]
lemma riemannIntegrable_of_upper_lower_gap {f : ℝ → ℝ} {a b : ℝ}
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hgap : ∀ ε > 0, ∃ P : IntervalPartition a b,
      upperDarbouxSum f P - lowerDarbouxSum f P < ε) :
    RiemannIntegrableOn f a b := by
  classical
  rcases hbound with ⟨B, hB⟩
  have hmin : ∀ x ∈ Set.Icc a b, -B ≤ f x := by
    intro x hx
    exact (abs_le.mp (hB x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, f x ≤ B := by
    intro x hx
    exact (abs_le.mp (hB x hx)).2
  obtain ⟨P0, _⟩ := hgap 1 (by linarith)
  have hab : a ≤ b := by
    have hmono : Monotone P0.points := P0.mono.monotone
    have h0 : P0.points 0 ≤ P0.points (Fin.last P0.n) := hmono (Fin.zero_le _)
    simpa [P0.left_eq, P0.right_eq, Fin.last] using h0
  have hsum_bounds (P : IntervalPartition a b) :
      -B * (b - a) ≤ lowerDarbouxSum f P ∧
        lowerDarbouxSum f P ≤ upperDarbouxSum f P ∧
        upperDarbouxSum f P ≤ B * (b - a) := by
    simpa using
      (lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := -B) (M := B) hmin hmax P)
  have hBddAbove :
      BddAbove (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
    refine ⟨B * (b - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum := hsum_bounds P
    exact le_trans hsum.2.1 hsum.2.2
  have hBddBelow :
      BddBelow (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) := by
    refine ⟨-B * (b - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum := hsum_bounds P
    exact le_trans hsum.1 hsum.2.1
  have hmid : lowerDarbouxIntegral f a b ≤ upperDarbouxIntegral f a b := by
    have h :=
      lower_upper_integral_bounds (f := f) (a := a) (b := b) (m := -B) (M := B) hab hmin hmax
    exact h.2.1
  have hupper_le_lower : upperDarbouxIntegral f a b ≤ lowerDarbouxIntegral f a b := by
    by_contra hlt
    have hgt : lowerDarbouxIntegral f a b < upperDarbouxIntegral f a b := lt_of_not_ge hlt
    set ε : ℝ := upperDarbouxIntegral f a b - lowerDarbouxIntegral f a b
    have hεpos : 0 < ε := by
      have : 0 < upperDarbouxIntegral f a b - lowerDarbouxIntegral f a b := sub_pos.mpr hgt
      simpa [ε] using this
    obtain ⟨P, hPgap⟩ := hgap ε hεpos
    have hupper_le_sum :
        upperDarbouxIntegral f a b ≤ upperDarbouxSum f P := by
      have hmem :
          upperDarbouxSum f P ∈
            Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P) := ⟨P, rfl⟩
      have hinf :
          sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P))
            ≤ upperDarbouxSum f P := by
        exact csInf_le hBddBelow hmem
      simpa [upperDarbouxIntegral] using hinf
    have hlower_le :
        lowerDarbouxSum f P ≤ lowerDarbouxIntegral f a b := by
      have hmem :
          lowerDarbouxSum f P ∈
            Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P) := ⟨P, rfl⟩
      have hsup :
          lowerDarbouxSum f P ≤
            sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
        exact le_csSup hBddAbove hmem
      simpa [lowerDarbouxIntegral] using hsup
    have hcontr : ε ≤ upperDarbouxSum f P - lowerDarbouxSum f P := by
      have :
          upperDarbouxIntegral f a b - lowerDarbouxIntegral f a b ≤
            upperDarbouxSum f P - lowerDarbouxSum f P := by
        linarith [hupper_le_sum, hlower_le]
      simpa [ε] using this
    have hlt' : ε < ε := lt_of_le_of_lt hcontr hPgap
    exact (lt_irrefl _ hlt')
  have heq :
      lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
    exact le_antisymm hmid hupper_le_lower
  exact ⟨⟨B, hB⟩, heq⟩

end UndergradKB.RealAnalysis
