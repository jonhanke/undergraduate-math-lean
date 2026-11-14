import UndergradKB.Common.Attr
import UndergradKB.Probability.Equalizations
import UndergradKB.Probability.RandomWalk
import UndergradKB.Probability.ArcSine
import UndergradKB.Probability.FirstMaximum

/-!
# Course layer, Chapter 12 (Grinstead–Snell, Random Walks)

Thin wrappers citing the book's numbered results of Chapter 12 by number. Each wrapper has exactly the
statement of the proved theorem of `UndergradKB.Probability` (`type_of%` shows it in the docs).
-/

namespace UndergradKB.Probability.Course

/-- Grinstead–Snell Definition 12.1 (PR-124). A random walk is the sequence of partial sums
`S_{n+1} = S_n + X_n` of the steps. -/
@[kb "grinsteadsnell2006" "Definition 12.1, p. 479"]
theorem gs_definition_12_1 : type_of% @UndergradKB.Probability.randomWalk_succ :=
  @UndergradKB.Probability.randomWalk_succ

/-- Grinstead–Snell Theorem 12.1 (PR-125). The simple symmetric walk is at the origin at time `2m` with
probability `C(2m,m) 2^(-2m)`, and never at odd times. -/
@[kb "grinsteadsnell2006" "Theorem 12.1, p. 481"]
theorem gs_theorem_12_1 :
    (∀ m : ℕ, u (2 * m) = ((2 * m).choose m : ℚ) / 2 ^ (2 * m)) ∧ ∀ m : ℕ, u (2 * m + 1) = 0 :=
  ⟨UndergradKB.Probability.u_even, UndergradKB.Probability.u_odd⟩

/-- Grinstead–Snell Theorem 12.2 (PR-126). `u_{2n} = ∑_{k=1}^n f_{2k} u_{2n-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.2, p. 481"]
theorem gs_theorem_12_2 : type_of% @UndergradKB.Probability.u_renewal :=
  @UndergradKB.Probability.u_renewal

/-- Grinstead–Snell Theorem 12.3 (PR-126). The first return to the origin is at time `2m` with
probability `u_{2m}/(2m-1)`. -/
@[kb "grinsteadsnell2006" "Theorem 12.3, p. 482"]
theorem gs_theorem_12_3 : type_of% @UndergradKB.Probability.f_even :=
  @UndergradKB.Probability.f_even

/-- Grinstead–Snell Theorem 12.4 (PR-129). A walk of length `2m` is in the lead exactly `2k` times with
probability `u_{2k} u_{2m-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.4, p. 502"]
theorem gs_theorem_12_4 : type_of% @UndergradKB.Probability.leadCount_prob :=
  @UndergradKB.Probability.leadCount_prob

/-- Grinstead–Snell Theorem 12.4 (PR-129), arc sine limit for the time in the lead. -/
@[kb "grinsteadsnell2006" "Theorem 12.4, p. 502"]
theorem gs_theorem_12_4_limit : type_of% @UndergradKB.Probability.leadCount_cdf_tendsto :=
  @UndergradKB.Probability.leadCount_cdf_tendsto

/-- Grinstead–Snell Theorem 12.5 (PR-129). The smallest `j` with `S_j = S_{2n}` equals `2k` with
probability `u_{2k} u_{2n-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.5, p. 503"]
theorem gs_theorem_12_5 : type_of% @UndergradKB.Probability.firstAtEnd_prob :=
  @UndergradKB.Probability.firstAtEnd_prob

/-- Grinstead–Snell Theorem 12.5 (PR-129), arc sine limit for the first time at the final position. -/
@[kb "grinsteadsnell2006" "Theorem 12.5, p. 503"]
theorem gs_theorem_12_5_limit : type_of% @UndergradKB.Probability.firstAtEnd_cdf_tendsto :=
  @UndergradKB.Probability.firstAtEnd_cdf_tendsto

/-- Grinstead–Snell Theorem 12.6 (PR-129). For independent steps with a common continuous symmetric law,
the index `K_n` of the first maximum satisfies `P(K_n < nα) → (2/π) arcsin √α`. -/
@[kb "grinsteadsnell2006" "Theorem 12.6, p. 504"]
theorem gs_theorem_12_6 : type_of% @UndergradKB.Probability.firstMaxIndex_tendsto :=
  @UndergradKB.Probability.firstMaxIndex_tendsto

/-- Grinstead–Snell Theorem 12.6 (PR-129), the exact law behind it: `P(K_n = k) = u_{2k} u_{2n-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.6, p. 504"]
theorem gs_theorem_12_6_law : type_of% @UndergradKB.Probability.firstMaxIndex_prob :=
  @UndergradKB.Probability.firstMaxIndex_prob

/-- Grinstead–Snell Example 12.3 (PR-127). The expected number of equalizations of the simple symmetric walk in `2m` steps. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem gs_example_12_3 : type_of% @UndergradKB.Probability.expectedEqualizations_two_mul :=
  @UndergradKB.Probability.expectedEqualizations_two_mul

/-- Grinstead–Snell Example 12.3 (PR-127). The closed form for the total number of equalizations over all walks. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem gs_example_12_3_b : type_of% @UndergradKB.Probability.equalTotal_two_mul :=
  @UndergradKB.Probability.equalTotal_two_mul

/-- Grinstead–Snell Example 12.3 (PR-127). The asymptotics of the expected number of equalizations. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem gs_example_12_3_c : type_of% @UndergradKB.Probability.expectedEqualizations_asymptotic :=
  @UndergradKB.Probability.expectedEqualizations_asymptotic

/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), fair game, existence: `h(k) = k/M` is the harmonic function on `0..M` with `h(0) = 0`, `h(M) = 1`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gs_section_12_2_gamblers_ruin : type_of% @UndergradKB.Probability.gamblersRuin_fair_exists :=
  @UndergradKB.Probability.gamblersRuin_fair_exists

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), fair game, uniqueness: a function on `0..M` with `h(0) = 0`, `h(M) = 1` and `h(k) = (h(k-1) + h(k+1))/2` for `0 < k < M` equals `k/M`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gs_section_12_2_gamblers_ruin_b : type_of% @UndergradKB.Probability.gamblersRuin_fair_unique :=
  @UndergradKB.Probability.gamblersRuin_fair_unique

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), unfair game with win probability `p`, loss probability `q = 1 - p` and `r = q/p ≠ 1`, existence: `h(k) = (r^k - 1)/(r^M - 1)` is the probability of reaching `M` before `0` from `k`; it satisfies `h(k) = p h(k+1) + q h(k-1)` with `h(0) = 0`, `h(M) = 1`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gs_section_12_2_gamblers_ruin_c : type_of% @UndergradKB.Probability.gamblersRuin_unfair_exists :=
  @UndergradKB.Probability.gamblersRuin_unfair_exists

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), unfair game, uniqueness: any `h` on `0..M` with `h(0) = 0`, `h(M) = 1` and `h(k) = p h(k+1) + q h(k-1)` for `0 < k < M` equals `(r^k - 1)/(r^M - 1)`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gs_section_12_2_gamblers_ruin_d : type_of% @UndergradKB.Probability.gamblersRuin_unfair_unique :=
  @UndergradKB.Probability.gamblersRuin_unfair_unique

end UndergradKB.Probability.Course
