import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular

/-! # Law of large numbers for ergodic chains (Grinstead–Snell, Theorem 11.12)

For an ergodic chain with fixed probability vector `w`, the proportion of the times `0, …, n` that the chain spends in
the state `j` converges in probability to `w j`.  The proof is Chebyshev's inequality on the finite space of paths:
the first and second moments of the number of visits are computed from the path weights `pathProb`
(`marg2`, the two-time marginal formula), and the variance of the proportion tends to `0` by the Cesàro convergence
of `P^k` (`ergodic_cesaro_tendsto`).  The analytic part is a statement about real sequences (`var_tendsto`). -/

open Finset Filter Topology Matrix

namespace UndergradKB.Probability

/-! ## Sequences -/

/-- Partial sums `a 0 + ⋯ + a (N-1)`. -/
def csum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ s ∈ range N, a s

/-- The symmetrised kernel `g s t = a_{min} r_{|t-s|}`. -/
def gsym (a r : ℕ → ℝ) (s t : ℕ) : ℝ := if s ≤ t then a s * r (t - s) else a t * r (s - t)

/-- The convolution `∑_{s<N} a_s (r_0 + ⋯ + r_{N-s-1})`. -/
def convT (a r : ℕ → ℝ) (N : ℕ) : ℝ := ∑ s ∈ range N, a s * csum r (N - s)

theorem convT_succ (a r : ℕ → ℝ) (hr0 : r 0 = 1) (N : ℕ) :
    convT a r (N + 1) = convT a r N + ∑ s ∈ range N, a s * r (N - s) + a N := by
  unfold convT
  rw [sum_range_succ]
  have h1 : ∀ s ∈ range N, a s * csum r (N + 1 - s) = a s * csum r (N - s) + a s * r (N - s) := by
    intro s hs
    have hs' := mem_range.1 hs
    have : N + 1 - s = (N - s) + 1 := by omega
    rw [this]; unfold csum; rw [sum_range_succ]; ring
  rw [sum_congr rfl h1, sum_add_distrib]
  simp [csum, hr0]

theorem sum_gsym (a r : ℕ → ℝ) (hr0 : r 0 = 1) (N : ℕ) :
    ∑ s ∈ range N, ∑ t ∈ range N, gsym a r s t = 2 * convT a r N - csum a N := by
  induction N with
  | zero => simp [convT, csum]
  | succ N ih =>
    have e1 : ∑ s ∈ range (N + 1), ∑ t ∈ range (N + 1), gsym a r s t =
        ∑ s ∈ range N, ∑ t ∈ range N, gsym a r s t + ∑ s ∈ range N, gsym a r s N +
          (∑ t ∈ range N, gsym a r N t + gsym a r N N) := by
      simp only [sum_range_succ, sum_add_distrib]
      ring
    have f1 : ∑ s ∈ range N, gsym a r s N = ∑ s ∈ range N, a s * r (N - s) :=
      sum_congr rfl fun s hs => by simp [gsym, (mem_range.1 hs).le]
    have f2 : ∑ t ∈ range N, gsym a r N t = ∑ t ∈ range N, a t * r (N - t) :=
      sum_congr rfl fun t ht => by simp [gsym, not_le.2 (mem_range.1 ht)]
    have f3 : gsym a r N N = a N := by simp [gsym, hr0]
    have hA : csum a (N + 1) = csum a N + a N := sum_range_succ _ _
    rw [e1, f1, f2, f3, ih, convT_succ a r hr0 N, hA]
    ring

theorem sum_mul_sub (a : ℕ → ℝ) (N : ℕ) :
    ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) = ∑ t ∈ range N, csum a (t + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun s => a s * ((N + 1 - s : ℕ) : ℝ)) N,
      sum_range_succ (fun t => csum a (t + 1)) N, ← ih]
    have h1 : ∀ s ∈ range N, a s * ((N + 1 - s : ℕ) : ℝ) = a s * ((N - s : ℕ) : ℝ) + a s := by
      intro s hs
      have := mem_range.1 hs
      have e : N + 1 - s = (N - s) + 1 := by omega
      rw [e]; push_cast; ring
    rw [sum_congr rfl h1, sum_add_distrib]
    simp [csum, sum_range_succ]
    ring

theorem sum_range_cast_succ (N : ℕ) : ∑ t ∈ range N, ((t : ℝ) + 1) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

theorem csum_eq (f : ℕ → ℝ) (w : ℝ) (m : ℕ) : csum f m = m * (w + (csum f m / m - w)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [csum]
  · have : (m : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem remainder_bound (a : ℕ → ℝ) (ha0 : ∀ s, 0 ≤ a s) (ha1 : ∀ s, a s ≤ 1) (η : ℕ → ℝ) (N : ℕ) :
    |∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s)| ≤ N * ∑ m ∈ range N, |η (m + 1)| := by
  have hr : ∑ s ∈ range N, |η (N - s)| = ∑ m ∈ range N, |η (m + 1)| := by
    refine Eq.trans (sum_congr rfl fun s hs => ?_) (sum_range_reflect (fun m => |η (m + 1)|) N)
    have := mem_range.1 hs
    have e : N - 1 - s + 1 = N - s := by omega
    show |η (N - s)| = |η (N - 1 - s + 1)|
    rw [e]
  calc |∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s)|
      ≤ ∑ s ∈ range N, |a s * ((N - s : ℕ) : ℝ) * η (N - s)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ range N, (N : ℝ) * |η (N - s)| := by
        refine sum_le_sum fun s hs => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (ha0 s), abs_of_nonneg (Nat.cast_nonneg _)]
        have h1 : ((N - s : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N s
        have h2 := abs_nonneg (η (N - s))
        have h3 := ha1 s
        have h4 := ha0 s
        have h5 : (0 : ℝ) ≤ ((N - s : ℕ) : ℝ) := Nat.cast_nonneg _
        calc a s * ((N - s : ℕ) : ℝ) * |η (N - s)| ≤ 1 * (N : ℝ) * |η (N - s)| := by gcongr
          _ = (N : ℝ) * |η (N - s)| := by ring
    _ = N * ∑ m ∈ range N, |η (m + 1)| := by rw [← mul_sum, hr]

theorem theta_bound (θ : ℕ → ℝ) (N : ℕ) :
    |∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1)| ≤ N * ∑ t ∈ range N, |θ (t + 1)| := by
  calc |∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1)|
      ≤ ∑ t ∈ range N, |((t : ℝ) + 1) * θ (t + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ range N, (N : ℝ) * |θ (t + 1)| := by
        refine sum_le_sum fun t ht => ?_
        have := mem_range.1 ht
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have h1 : (t : ℝ) + 1 ≤ N := by exact_mod_cast this
        gcongr
    _ = N * ∑ t ∈ range N, |θ (t + 1)| := by rw [mul_sum]

theorem cesaro_shift_tendsto (ν : ℕ → ℝ) (h : Tendsto ν atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ t ∈ range N, |ν (t + 1)|) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => |ν (t + 1)|) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat (f := ν) 1).2 h
    simpa using this.abs
  simpa using h1.cesaro

/-- The analytic core of the law of large numbers: if the Cesàro means of `a` and of `r` both tend to `w`
(with `0 ≤ a ≤ 1`, `r 0 = 1`), then the variance expression below tends to `0`. -/
theorem var_tendsto (a r : ℕ → ℝ) (w : ℝ) (ha0 : ∀ s, 0 ≤ a s) (ha1 : ∀ s, a s ≤ 1) (hr0 : r 0 = 1)
    (hA : Tendsto (fun N : ℕ => csum a N / N) atTop (𝓝 w))
    (hR : Tendsto (fun m : ℕ => csum r m / m) atTop (𝓝 w)) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ) ^ 2) * (∑ s ∈ range N, ∑ t ∈ range N, gsym a r s t) -
      2 * w * (csum a N / N) + w ^ 2) atTop (𝓝 0) := by
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, θ = fun m => csum a m / m - w := ⟨_, rfl⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun m => csum r m / m - w := ⟨_, rfl⟩
  have hθ : Tendsto θ atTop (𝓝 0) := by
    rw [hθdef]; simpa using hA.sub_const w
  have hη : Tendsto η atTop (𝓝 0) := by
    rw [hηdef]; simpa using hR.sub_const w
  have hAθ : ∀ m, csum a m = m * (w + θ m) := fun m => by rw [hθdef]; exact csum_eq a w m
  have hRη : ∀ m, csum r m = m * (w + η m) := fun m => by rw [hηdef]; exact csum_eq r w m
  -- decomposition of the convolution
  have hE : ∀ N : ℕ, convT a r N - w ^ 2 * (N * (N + 1) / 2) =
      w * ∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1) +
        ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s) := by
    intro N
    have h1 : convT a r N = w * ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) +
        ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s) := by
      unfold convT
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [hRη (N - s)]; ring
    have h2 : ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) =
        w * (N * (N + 1) / 2) + ∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1) := by
      rw [sum_mul_sub, ← sum_range_cast_succ, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun t _ => ?_
      rw [hAθ (t + 1)]; push_cast; ring
    rw [h1, h2]; ring
  -- the error term tends to zero
  have hbound : ∀ N : ℕ, 1 ≤ N →
      |(convT a r N - w ^ 2 * (N * (N + 1) / 2)) / (N : ℝ) ^ 2| ≤
        |w| * ((N : ℝ)⁻¹ * ∑ t ∈ range N, |θ (t + 1)|) + (N : ℝ)⁻¹ * ∑ t ∈ range N, |η (t + 1)| := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [hE N, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2), div_le_iff₀ (by positivity)]
    have b1 := theta_bound θ N
    have b2 := remainder_bound a ha0 ha1 η N
    calc |w * ∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1) +
          ∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s)|
        ≤ |w * ∑ t ∈ range N, ((t : ℝ) + 1) * θ (t + 1)| +
          |∑ s ∈ range N, a s * ((N - s : ℕ) : ℝ) * η (N - s)| := abs_add_le _ _
      _ ≤ |w| * (N * ∑ t ∈ range N, |θ (t + 1)|) + N * ∑ m ∈ range N, |η (m + 1)| := by
          rw [abs_mul]
          gcongr
      _ = (|w| * ((N : ℝ)⁻¹ * ∑ t ∈ range N, |θ (t + 1)|) + (N : ℝ)⁻¹ * ∑ t ∈ range N, |η (t + 1)|) *
            (N : ℝ) ^ 2 := by
          field_simp
  have he : Tendsto (fun N : ℕ => (convT a r N - w ^ 2 * (N * (N + 1) / 2)) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => |w| * ((N : ℝ)⁻¹ * ∑ t ∈ range N, |θ (t + 1)|) +
        (N : ℝ)⁻¹ * ∑ t ∈ range N, |η (t + 1)|) atTop (𝓝 0) := by
      have := ((cesaro_shift_tendsto θ hθ).const_mul |w|).add (cesaro_shift_tendsto η hη)
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact hbound N hN
  have h1N : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun N : ℕ => w ^ 2 * (1 + 1 / (N : ℝ)) +
      2 * ((convT a r N - w ^ 2 * (N * (N + 1) / 2)) / (N : ℝ) ^ 2) -
      (csum a N / N) * (1 / (N : ℝ)) - 2 * w * (csum a N / N) + w ^ 2) atTop
      (𝓝 (w ^ 2 * (1 + 0) + 2 * 0 - w * 0 - 2 * w * w + w ^ 2)) := by
    refine ((((tendsto_const_nhds.mul (tendsto_const_nhds.add h1N)).add (he.const_mul 2)).sub
      (hA.mul h1N)).sub (hA.const_mul (2 * w))).add tendsto_const_nhds
  have hz : w ^ 2 * (1 + 0) + 2 * 0 - w * 0 - 2 * w * w + w ^ 2 = 0 := by ring
  rw [hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNne : (N : ℝ) ≠ 0 := by positivity
  rw [sum_gsym a r hr0 N]
  field_simp
  ring


/-! ## Marginals of the path weights -/

section Paths

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The state at time `k` of a path of length `n` (times beyond `n` are clamped to `n`). -/
def pt {n : ℕ} (x : Fin (n + 1) → S) (k : ℕ) : S :=
  x ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩

theorem pt_last {n : ℕ} (x : Fin (n + 1) → S) : pt x n = x (Fin.last n) := by
  unfold pt
  congr 1
  exact Fin.ext (by simp)

theorem pt_coe {n : ℕ} (x : Fin (n + 1) → S) (k : Fin (n + 1)) : pt x k = x k := by
  unfold pt
  congr 1
  exact Fin.ext (by simp; omega)

theorem pt_snoc {n : ℕ} (y : Fin (n + 1) → S) (s : S) {k : ℕ} (hk : k ≤ n) :
    pt (Fin.snoc y s : Fin (n + 2) → S) k = pt y k := by
  have h : (⟨min k (n + 1), Nat.lt_succ_of_le (min_le_right k (n + 1))⟩ : Fin (n + 2)) =
      Fin.castSucc ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ :=
    Fin.ext (by simp; omega)
  unfold pt
  rw [h, Fin.snoc_castSucc]

theorem pt_init {n : ℕ} (x : Fin (n + 2) → S) {k : ℕ} (hk : k ≤ n) :
    pt x k = pt (Fin.init x) k := by
  have h : (⟨min k (n + 1), Nat.lt_succ_of_le (min_le_right k (n + 1))⟩ : Fin (n + 2)) =
      Fin.castSucc ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩ :=
    Fin.ext (by simp; omega)
  unfold pt
  rw [h]
  rfl

theorem sum_paths_succ (n : ℕ) (F : (Fin (n + 2) → S) → ℝ) :
    ∑ x : Fin (n + 2) → S, F x = ∑ y : Fin (n + 1) → S, ∑ s : S, F (Fin.snoc y s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => S)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv_apply]

variable (u : S → ℝ) (P : Matrix S S ℝ)

theorem sum_pathProb_init (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (G : (Fin (n + 1) → S) → ℝ) :
    ∑ x : Fin (n + 2) → S, pathProb u P (n + 1) x * G (Fin.init x) =
      ∑ y : Fin (n + 1) → S, pathProb u P n y * G y := by
  rw [sum_paths_succ]
  simp only [pathProb_snoc, Fin.init_snoc]
  refine sum_congr rfl fun y _ => ?_
  have h := sum_row_of_mem_rowStochastic hP (y (Fin.last n))
  calc ∑ s : S, pathProb u P n y * P (y (Fin.last n)) s * G y
      = pathProb u P n y * G y * ∑ s : S, P (y (Fin.last n)) s := by
        rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
    _ = pathProb u P n y * G y := by rw [h, mul_one]

/-- The two-time marginal reduces a path of length `t + d` to one of length `t`. -/
theorem marg2 (hP : P ∈ rowStochastic ℝ S) (s t : ℕ) (hst : s ≤ t) (φ : S → S → ℝ) (d : ℕ) :
    ∑ x : Fin (t + d + 1) → S, pathProb u P (t + d) x * φ (pt x s) (pt x t) =
      ∑ y : Fin (t + 1) → S, pathProb u P t y * φ (pt y s) (pt y t) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have := sum_pathProb_init u P hP (t + d) (fun y => φ (pt y s) (pt y t))
    refine Eq.trans ?_ (this.trans ih)
    exact sum_congr rfl fun x _ => by
      rw [pt_init x (by omega : s ≤ t + d), pt_init x (by omega : t ≤ t + d)]
      rfl

theorem phi_succ (t : ℕ) (H : (Fin (t + 1) → S) → ℝ) (k : S) :
    ∑ x : Fin (t + 2) → S with x (Fin.last (t + 1)) = k, pathProb u P (t + 1) x * H (Fin.init x) =
      ∑ l : S, (∑ y : Fin (t + 1) → S with y (Fin.last t) = l, pathProb u P t y * H y) * P l k := by
  rw [sum_filter, sum_paths_succ]
  simp only [Fin.snoc_last, pathProb_snoc, Fin.init_snoc]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun y : Fin (t + 1) → S => y (Fin.last t))]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun y hy => ?_
  rw [(mem_filter.1 hy).2]
  ring



theorem phi_base (s : ℕ) (j l : S) :
    ∑ y : Fin (s + 1) → S with y (Fin.last s) = l,
        pathProb u P s y * (if y (Fin.last s) = j then (1 : ℝ) else 0) =
      if l = j then (u ᵥ* P ^ s) l else 0 := by
  have h : ∀ y ∈ (univ.filter fun y : Fin (s + 1) → S => y (Fin.last s) = l),
      pathProb u P s y * (if y (Fin.last s) = j then (1 : ℝ) else 0) =
        pathProb u P s y * (if l = j then 1 else 0) := by
    intro y hy; rw [(mem_filter.1 hy).2]
  rw [sum_congr rfl h, ← sum_mul, sum_pathProb_last]
  split_ifs <;> simp

theorem phi_two (s : ℕ) (j : S) : ∀ t, s ≤ t → ∀ l : S,
    ∑ y : Fin (t + 1) → S with y (Fin.last t) = l,
        pathProb u P t y * (if pt y s = j then (1 : ℝ) else 0) =
      (u ᵥ* P ^ s) j * (P ^ (t - s)) j l := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base =>
    intro l
    have : ∀ y : Fin (s + 1) → S, pt y s = y (Fin.last s) := pt_last
    simp only [this]
    rw [phi_base]
    by_cases h : l = j
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ t hst ih =>
    intro l
    have h1 := phi_succ u P t (fun y => if pt y s = j then (1 : ℝ) else 0) l
    refine Eq.trans (sum_congr rfl fun x _ => ?_) (h1.trans ?_)
    · show _ = pathProb u P (t + 1) x * (if pt (Fin.init x) s = j then (1 : ℝ) else 0)
      rw [pt_init x hst]
    · have e2 : ∀ m ∈ (univ : Finset S),
          (∑ y : Fin (t + 1) → S with y (Fin.last t) = m,
            pathProb u P t y * (if pt y s = j then (1 : ℝ) else 0)) * P m l =
          (u ᵥ* P ^ s) j * ((P ^ (t - s)) j m * P m l) := by
        intro m _
        rw [ih m]; ring
      rw [sum_congr rfl e2, ← mul_sum]
      have : t + 1 - s = t - s + 1 := by omega
      rw [this, pow_succ, Matrix.mul_apply]

theorem two_time (s t : ℕ) (hst : s ≤ t) (j : S) :
    ∑ y : Fin (t + 1) → S, pathProb u P t y *
        ((if pt y s = j then (1 : ℝ) else 0) * (if pt y t = j then 1 else 0)) =
      (u ᵥ* P ^ s) j * (P ^ (t - s)) j j := by
  rw [← phi_two u P s j t hst j, sum_filter]
  refine sum_congr rfl fun y _ => ?_
  rw [pt_last]
  split_ifs <;> simp

variable {u P}

theorem single_marg (hP : P ∈ rowStochastic ℝ S) (j : S) (k n : ℕ) (hk : k ≤ n) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x * (if pt x k = j then (1 : ℝ) else 0) =
      (u ᵥ* P ^ k) j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := marg2 u P hP k k le_rfl (fun a _ => if a = j then (1 : ℝ) else 0) d
  refine Eq.trans this ?_
  simp only [pt_last]
  rw [← sum_pathProb_last u P k j, sum_filter]
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem double_marg (hP : P ∈ rowStochastic ℝ S) (j : S) (s t n : ℕ) (hst : s ≤ t) (htn : t ≤ n) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x *
        ((if pt x s = j then (1 : ℝ) else 0) * (if pt x t = j then 1 else 0)) =
      (u ᵥ* P ^ s) j * (P ^ (t - s)) j j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htn
  have := marg2 u P hP s t hst (fun a b => (if a = j then (1 : ℝ) else 0) * (if b = j then 1 else 0)) d
  exact this.trans (two_time u P s t hst j)

/-- The number of visits to `j` at the times `0, …, n` (as a real number). -/
noncomputable def visits {n : ℕ} (x : Fin (n + 1) → S) (j : S) : ℝ :=
  ∑ k ∈ range (n + 1), if pt x k = j then (1 : ℝ) else 0

theorem visits_eq_card {n : ℕ} (x : Fin (n + 1) → S) (j : S) :
    visits x j = ((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) := by
  unfold visits
  rw [← Fin.sum_univ_eq_sum_range (fun k => if pt x k = j then (1 : ℝ) else 0) (n + 1)]
  simp only [pt_coe]
  rw [sum_boole]

theorem moment1 (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (j : S) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x * visits x j =
      csum (fun k => (u ᵥ* P ^ k) j) (n + 1) := by
  unfold visits csum
  simp only [mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun k hk => single_marg hP j k n (Nat.lt_succ_iff.1 (mem_range.1 hk))

theorem moment2 (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (j : S) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x * visits x j ^ 2 =
      ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
        gsym (fun k => (u ᵥ* P ^ k) j) (fun d => (P ^ d) j j) s t := by
  have h : ∀ x : Fin (n + 1) → S, pathProb u P n x * visits x j ^ 2 =
      ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1), pathProb u P n x *
        ((if pt x s = j then (1 : ℝ) else 0) * (if pt x t = j then 1 else 0)) := by
    intro x
    rw [sq]
    unfold visits
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [mul_sum]
  simp only [h]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s hs => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun t ht => ?_
  have hs' := Nat.lt_succ_iff.1 (mem_range.1 hs)
  have ht' := Nat.lt_succ_iff.1 (mem_range.1 ht)
  by_cases hst : s ≤ t
  · simp only [gsym, hst, ↓reduceIte]
    exact double_marg hP j s t n hst ht'
  · have hts : t ≤ s := (not_le.1 hst).le
    simp only [gsym, hst, ↓reduceIte]
    rw [← double_marg hP j t s n hts hs']
    exact sum_congr rfl fun x _ => by ring

theorem variance_eq (hu : ∑ i, u i = 1) (hP : P ∈ rowStochastic ℝ S) (w : ℝ) (j : S) (n : ℕ) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x * (visits x j / ((n + 1 : ℕ) : ℝ) - w) ^ 2 =
      (1 / ((n + 1 : ℕ) : ℝ) ^ 2) * (∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
          gsym (fun k => (u ᵥ* P ^ k) j) (fun d => (P ^ d) j j) s t) -
        2 * w * (csum (fun k => (u ᵥ* P ^ k) j) (n + 1) / ((n + 1 : ℕ) : ℝ)) + w ^ 2 := by
  have e : ∀ x : Fin (n + 1) → S, pathProb u P n x * (visits x j / ((n + 1 : ℕ) : ℝ) - w) ^ 2 =
      (1 / ((n + 1 : ℕ) : ℝ) ^ 2) * (pathProb u P n x * visits x j ^ 2) -
        (2 * w / ((n + 1 : ℕ) : ℝ)) * (pathProb u P n x * visits x j) + w ^ 2 * pathProb u P n x := by
    intro x; ring
  simp only [e]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, moment2 hP, moment1 hP,
    sum_pathProb hu hP n]
  ring

end Paths

/-! ## The law of large numbers -/

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Grinstead–Snell Theorem 11.12 (PR-119). Law of large numbers for ergodic chains: for an ergodic chain with fixed
probability vector `w` and any initial probability vector `u`, the proportion of the times `0, …, n` at which the
chain is in state `j` differs from `w j` by at least `ε` with probability tending to `0` (the probability is the total
weight `pathProb` of the paths concerned). -/
@[kb "grinsteadsnell2006" "Theorem 11.12, p. 447"]
theorem markov_lln {P : Matrix S S ℝ} (hP : IsErgodicChain P) (u : S → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∑ i, u i = 1) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ (j : S) (ε : ℝ), 0 < ε →
        Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S with
            ε ≤ |((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) / ((n : ℝ) + 1) - w j|,
          pathProb u P n x) atTop (𝓝 0) := by
  obtain ⟨w, hpos, hsum, hfix, hces⟩ := ergodic_cesaro_tendsto hP
  refine ⟨w, hpos, hsum, hfix, fun j ε hε => ?_⟩
  have hPs := hP.1
  have ha0 : ∀ k, 0 ≤ (u ᵥ* P ^ k) j := fun k => (markov_dist_after_n_steps_prob hu0 hu hPs k).1 j
  have ha1 : ∀ k, (u ᵥ* P ^ k) j ≤ 1 := by
    intro k
    have h := (markov_dist_after_n_steps_prob hu0 hu hPs k)
    rw [← h.2]
    exact single_le_sum (fun i _ => h.1 i) (mem_univ j)
  have hr0 : (fun d => (P ^ d) j j) 0 = 1 := by simp
  have hA : Tendsto (fun N : ℕ => csum (fun k => (u ᵥ* P ^ k) j) N / N) atTop (𝓝 (w j)) := by
    have hform : ∀ N : ℕ, csum (fun k => (u ᵥ* P ^ k) j) N / N = ∑ i, u i * cesaroAvg P N i j := by
      intro N
      unfold csum cesaroAvg
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.sum_comm, Finset.sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [← mul_sum, mul_div_assoc]
    simp only [hform]
    have := tendsto_finsetSum (univ : Finset S) fun i _ => (hces i j).const_mul (u i)
    simpa [← sum_mul, hu] using this
  have hR : Tendsto (fun m : ℕ => csum (fun d => (P ^ d) j j) m / m) atTop (𝓝 (w j)) := hces j j
  have hvar := (var_tendsto _ _ (w j) ha0 ha1 hr0 hA hR).comp (tendsto_add_atTop_nat 1)
  have hV : Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S,
      pathProb u P n x * (visits x j / ((n + 1 : ℕ) : ℝ) - w j) ^ 2) atTop (𝓝 0) := by
    refine hvar.congr fun n => ?_
    rw [variance_eq hu hPs]
    rfl
  have hV' : Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S, pathProb u P n x *
      (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) / ((n : ℝ) + 1) - w j) ^ 2)
      atTop (𝓝 0) := by
    simpa only [visits_eq_card, Nat.cast_add, Nat.cast_one] using hV
  have hup := hV'.div_const (ε ^ 2)
  rw [zero_div] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · exact sum_nonneg fun x _ => pathProb_nonneg hu0 hPs n x
  · simp only
    rw [sum_div]
    calc ∑ x : Fin (n + 1) → S with
            ε ≤ |((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) / ((n : ℝ) + 1) - w j|,
          pathProb u P n x
        ≤ ∑ x : Fin (n + 1) → S with
            ε ≤ |((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) / ((n : ℝ) + 1) - w j|,
          pathProb u P n x * ((((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
            ((n : ℝ) + 1) - w j) ^ 2 / ε ^ 2) := by
          refine sum_le_sum fun x hx => ?_
          have h := (mem_filter.1 hx).2
          have h2 : ε ^ 2 ≤ (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
              ((n : ℝ) + 1) - w j) ^ 2 := by
            rw [← sq_abs (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
              ((n : ℝ) + 1) - w j)]
            exact pow_le_pow_left₀ hε.le h 2
          have h3 : 1 ≤ (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
              ((n : ℝ) + 1) - w j) ^ 2 / ε ^ 2 := by
            rw [le_div_iff₀ (by positivity)]; linarith
          have := pathProb_nonneg hu0 hPs n x
          nlinarith
      _ ≤ ∑ x : Fin (n + 1) → S, pathProb u P n x * ((((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
            ((n : ℝ) + 1) - w j) ^ 2 / ε ^ 2) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => ?_
          exact mul_nonneg (pathProb_nonneg hu0 hPs n x) (by positivity)
      _ = ∑ x : Fin (n + 1) → S, pathProb u P n x * (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) /
            ((n : ℝ) + 1) - w j) ^ 2 / ε ^ 2 := by
          exact sum_congr rfl fun x _ => by ring

end UndergradKB.Probability
