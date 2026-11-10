import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Common.Attr

/-! # The fixed point of the cosine (Corral §6.2)

Corral §6.2 solves `cos x = x` numerically and observes that iterating the cosine from any starting value
converges to the solution, about `0.739085`. We prove:
* `exists_unique_cos_eq_self`: `cos x = x` has exactly one real solution, and it lies in `(0.72, 0.76)`;
* `tendsto_iterate_cos`: for every starting value `x₀`, the iterates `cos (cos (… cos x₀))` converge to it.
The key estimate is that `cos` is a contraction with constant `sin 1 < 1` on `[-1, 1]`, which contains every
value of the cosine.
-/

namespace UndergradKB.Trigonometry

open Real Set Filter Topology

private lemma sin_one_pos : 0 < sin 1 := sin_pos_of_pos_of_lt_pi one_pos (by linarith [two_le_pi])

private lemma sin_one_lt_one : sin 1 < 1 := sin_lt one_pos

/-- On `[-1, 1]` the cosine is a contraction: `|cos x - cos y| ≤ sin 1 · |x - y|`. -/
private lemma abs_cos_sub_cos_le {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |cos x - cos y| ≤ sin 1 * |x - y| := by
  have hpi : (1 : ℝ) ≤ π / 2 := by linarith [two_le_pi]
  have ht : |sin ((x + y) / 2)| ≤ sin 1 := by
    rw [abs_le]
    constructor
    · rw [← sin_neg]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [hx.2, hy.2])
        (by linarith [hx.1, hy.1])
    · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1, hy.1]) hpi
        (by linarith [hx.2, hy.2])
  have hs : |sin ((x - y) / 2)| ≤ |x - y| / 2 := by
    have := abs_sin_le_abs (x := (x - y) / 2)
    rwa [abs_div, abs_two] at this
  rw [cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  calc 2 * |sin ((x + y) / 2)| * |sin ((x - y) / 2)| ≤ 2 * sin 1 * (|x - y| / 2) := by
        gcongr
        linarith [sin_one_pos]
    _ = sin 1 * |x - y| := by ring

private lemma cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos x, cos_le_one x⟩

/-- `cos x = x` has a solution between `0.72` and `0.76`. -/
private lemma exists_cos_eq_self : ∃ c ∈ Icc (0.72 : ℝ) 0.76, cos c = c := by
  have hcont : ContinuousOn (fun x => cos x - x) (Icc (0.72 : ℝ) 0.76) :=
    (continuous_cos.sub continuous_id).continuousOn
  have h1 : cos (0.76 : ℝ) - 0.76 < 0 := by
    have := cos_bound (x := 0.76) (by rw [abs_le]; norm_num)
    rw [abs_le] at this
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.76)] at this
    nlinarith [this.2]
  have h0 : 0 < cos (0.72 : ℝ) - 0.72 := by
    have := cos_bound (x := 0.72) (by rw [abs_le]; norm_num)
    rw [abs_le] at this
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.72)] at this
    nlinarith [this.1]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨h1.le, h0.le⟩
  exact ⟨c, hc, by simp only at hc0; linarith⟩

/-- **The equation `cos x = x`** has exactly one real solution; it lies between `0.72` and `0.76`
(Corral: about `0.739085`). (TR-171) -/
@[kb "corraltrig" "Box §6.2 (cos x = x), p. 141"]
theorem exists_unique_cos_eq_self :
    ∃! c : ℝ, cos c = c ∧ c ∈ Icc (0.72 : ℝ) 0.76 := by
  obtain ⟨c, hc, hcc⟩ := exists_cos_eq_self
  refine ⟨c, ⟨hcc, hc⟩, fun y ⟨hy, _⟩ => ?_⟩
  have hb := abs_cos_sub_cos_le (hy ▸ cos_mem_Icc y) (hcc ▸ cos_mem_Icc c)
  rw [hy, hcc] at hb
  by_contra hne
  have hpos : 0 < |y - c| := abs_pos.2 (sub_ne_zero.2 hne)
  nlinarith [sin_one_lt_one]

/-- Any real solution of `cos x = x` is the one of `exists_unique_cos_eq_self`. -/
theorem cos_eq_self_unique {x y : ℝ} (hx : cos x = x) (hy : cos y = y) : x = y := by
  have hb := abs_cos_sub_cos_le (hx ▸ cos_mem_Icc x) (hy ▸ cos_mem_Icc y)
  rw [hx, hy] at hb
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  nlinarith [sin_one_lt_one]

/-- **Iterating the cosine converges to its fixed point**: for every start `x₀`, the sequence
`x₀, cos x₀, cos (cos x₀), …` converges to the solution `c` of `cos c = c`. (TR-171) -/
@[kb "corraltrig" "D033 (cosine iteration), p. 144"]
theorem tendsto_iterate_cos {c : ℝ} (hc : cos c = c) (x₀ : ℝ) :
    Tendsto (fun n : ℕ => cos^[n] x₀) atTop (𝓝 c) := by
  have hcI : c ∈ Icc (-1 : ℝ) 1 := hc ▸ cos_mem_Icc c
  have hb : ∀ n : ℕ, |cos^[n + 1] x₀ - c| ≤ sin 1 ^ n * |cos x₀ - c| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hmem : cos^[n + 1] x₀ ∈ Icc (-1 : ℝ) 1 := by
        rw [Function.iterate_succ_apply']; exact cos_mem_Icc _
      calc |cos (cos^[n + 1] x₀) - c| = |cos (cos^[n + 1] x₀) - cos c| := by rw [hc]
        _ ≤ sin 1 * |cos^[n + 1] x₀ - c| := abs_cos_sub_cos_le hmem hcI
        _ ≤ sin 1 * (sin 1 ^ n * |cos x₀ - c|) := by gcongr; exact sin_one_pos.le
        _ = sin 1 ^ (n + 1) * |cos x₀ - c| := by ring
  rw [← tendsto_add_atTop_iff_nat 1]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => hb n) ?_
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one sin_one_pos.le sin_one_lt_one).mul_const
    |cos x₀ - c|
  simpa using this

end UndergradKB.Trigonometry
