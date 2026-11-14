import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (Stitz-Zeager): worked examples, wave 5 (continued)

The remaining parts of the trigonometric inequality example 10.7.3 and the domain examples 10.7.4.
Cotangent is written as `cos / sin`, and the domain of a function is the set where its formula is
defined (nonvanishing denominators, nonnegative radicand).
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 10.7: inequalities -/

private theorem sin_gt_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    1 / 2 < sin x ↔ π / 6 < x ∧ x < 5 * π / 6 := by
  have hp := pi_pos
  have m : ∀ y z : ℝ, y ∈ Icc (-(π / 2)) (π / 2) → z ∈ Icc (-(π / 2)) (π / 2) →
      (sin y < sin z ↔ y < z) := fun y z hy hz => strictMonoOn_sin.lt_iff_lt hy hz
  have h6 : sin (π / 6) = 1 / 2 := sin_pi_div_six
  by_cases c1 : x ≤ π / 2
  · have := m (π / 6) x ⟨by linarith, by linarith⟩ ⟨by linarith, c1⟩
    rw [h6] at this
    rw [this]
    constructor
    · intro h; exact ⟨h, by linarith⟩
    · intro h; exact h.1
  · push Not at c1
    by_cases c2 : x < π
    · have := m (π / 6) (π - x) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      rw [h6, sin_pi_sub] at this
      rw [this]
      constructor
      · intro h; exact ⟨by linarith, by linarith⟩
      · intro h; linarith [h.2]
    · push Not at c2
      have : sin x ≤ 0 := by
        have := sin_nonneg_of_nonneg_of_le_pi (x := x - π) (by linarith) (by linarith)
        rw [sin_sub_pi] at this; linarith
      constructor
      · intro h; linarith
      · intro h; linarith [h.2]

private theorem cos_pos_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    0 < cos x ↔ x < π / 2 ∨ 3 * π / 2 < x := by
  have hp := pi_pos
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have := cos_nonneg_of_mem_Icc (x := x - π) ⟨by linarith [hh.1], by linarith [hh.2]⟩
    rw [cos_sub_pi] at this; linarith
  · rintro (h | h)
    · exact cos_pos_of_mem_Ioo ⟨by linarith, h⟩
    · have := cos_pos_of_mem_Ioo (x := x - 2 * π) ⟨by linarith, by linarith⟩
      rwa [cos_sub_two_pi] at this

private theorem cos_neg_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos x < 0 ↔ π / 2 < x ∧ x < 3 * π / 2 := by
  have hp := pi_pos
  constructor
  · intro h
    by_contra hh
    rw [not_and_or] at hh
    rcases hh with hh | hh
    · push Not at hh
      have := cos_nonneg_of_mem_Icc (x := x) ⟨by linarith, hh⟩
      linarith
    · push Not at hh
      have := cos_nonneg_of_mem_Icc (x := x - 2 * π) ⟨by linarith, by linarith⟩
      rw [cos_sub_two_pi] at this; linarith
  · rintro ⟨h2, h3⟩
    have := cos_pos_of_mem_Ioo (x := x - π) ⟨by linarith, by linarith⟩
    rw [cos_sub_pi] at this; linarith

/-- Stitz-Zeager Example 10.7.3(2): within `[0, 2π)`, `sin 2x > cos x` holds exactly on
`(π/6, π/2) ∪ (5π/6, 3π/2)`. -/
@[kb "stitzzeager2013" "Example 10.7.3, p. 878"]
theorem ex_10_7_3_b :
    {x : ℝ | x ∈ Ico 0 (2 * π) ∧ cos x < sin (2 * x)} =
      Ioo (π / 6) (π / 2) ∪ Ioo (5 * π / 6) (3 * π / 2) := by
  have hp := pi_pos
  ext x
  simp only [mem_ofPred_eq, mem_Ico, mem_union, mem_Ioo]
  have e : sin (2 * x) - cos x = cos x * (2 * sin x - 1) := by rw [sin_two_mul]; ring
  have s56 : sin (5 * π / 6) = 1 / 2 := by
    rw [show 5 * π / 6 = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    have hm : 0 < cos x * (2 * sin x - 1) := by linarith
    rcases mul_pos_iff.1 hm with ⟨a, b⟩ | ⟨a, b⟩
    · have hs := (sin_gt_half h0 h1).1 (by linarith)
      rcases (cos_pos_iff h0 h1).1 a with c | c
      · left; exact ⟨hs.1, c⟩
      · linarith [hs.2]
    · have hc := (cos_neg_iff h0 h1).1 a
      right
      refine ⟨?_, hc.2⟩
      by_contra hh
      push Not at hh
      rcases hh.lt_or_eq with hh | hh
      · have := (sin_gt_half h0 h1).2 ⟨by linarith [hc.1], hh⟩
        linarith
      · rw [hh, s56] at b; linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h0 : 0 ≤ x := by linarith
      have h1' : x < 2 * π := by linarith
      refine ⟨⟨h0, h1'⟩, ?_⟩
      have hs := (sin_gt_half h0 h1').2 ⟨h1, by linarith⟩
      have hc := (cos_pos_iff h0 h1').2 (Or.inl h2)
      nlinarith
    · have h0 : 0 ≤ x := by linarith
      have h1' : x < 2 * π := by linarith
      refine ⟨⟨h0, h1'⟩, ?_⟩
      have hc := (cos_neg_iff h0 h1').2 ⟨by linarith, h2⟩
      have hs : sin x < 1 / 2 := by
        by_contra hh
        push Not at hh
        rcases hh.lt_or_eq with hh | hh
        · have := (sin_gt_half h0 h1').1 hh
          linarith [this.2]
        · have hm : sin x = sin (5 * π / 6) := by rw [← hh, s56]
          have := sin_eq_sin_iff.1 hm
          obtain ⟨k, hk | hk⟩ := this
          · have a : (-1 : ℝ) < k := by
              by_contra hh; push Not at hh; nlinarith
            have b : (k : ℝ) < 1 := by
              by_contra hh; push Not at hh; nlinarith
            have a' : (-1 : ℤ) < k := by exact_mod_cast a
            have b' : k < 1 := by exact_mod_cast b
            obtain rfl : k = 0 := by omega
            simp at hk; linarith
          · have a : (-1 : ℝ) < k := by
              by_contra hh; push Not at hh; nlinarith
            have b : (k : ℝ) < 1 := by
              by_contra hh; push Not at hh; nlinarith
            have a' : (-1 : ℤ) < k := by exact_mod_cast a
            have b' : k < 1 := by exact_mod_cast b
            obtain rfl : k = 0 := by omega
            simp at hk; linarith
      nlinarith

private theorem three_le_tan_iff {y : ℝ} (hy1 : -(π / 2) < y) (hy2 : y < π / 2) :
    3 ≤ tan y ↔ arctan 3 ≤ y := by
  have := arctan_strictMono.le_iff_le (a := 3) (b := tan y)
  rw [arctan_tan hy1 hy2] at this
  exact this.symm

/-- Stitz-Zeager Example 10.7.3(3): within `[0, 2π)`, `tan x ≥ 3` holds exactly on
`[arctan 3, π/2) ∪ [arctan 3 + π, 3π/2)`. -/
@[kb "stitzzeager2013" "Example 10.7.3, p. 878"]
theorem ex_10_7_3_c :
    {x : ℝ | x ∈ Ico 0 (2 * π) ∧ 3 ≤ tan x} =
      Ico (arctan 3) (π / 2) ∪ Ico (arctan 3 + π) (3 * π / 2) := by
  have hp := pi_pos
  have a0 : 0 < arctan 3 := arctan_pos.2 (by norm_num)
  have a1 := arctan_lt_pi_div_two 3
  ext x
  simp only [mem_ofPred_eq, mem_Ico, mem_union]
  rcases lt_trichotomy x (π / 2) with h | h | h
  · have hx : 0 ≤ x → (3 ≤ tan x ↔ arctan 3 ≤ x) := fun h0 =>
      three_le_tan_iff (by linarith) h
    constructor
    · rintro ⟨⟨h0, h1⟩, h3⟩
      exact Or.inl ⟨(hx h0).1 h3, h⟩
    · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
      · exact ⟨⟨by linarith, by linarith⟩, (hx (by linarith)).2 h3⟩
      · linarith
  · subst h
    rw [tan_pi_div_two]
    constructor
    · rintro ⟨_, h3⟩; norm_num at h3
    · rintro (⟨_, h4⟩ | ⟨h3, _⟩) <;> linarith
  · rcases lt_trichotomy x (3 * π / 2) with h' | h' | h'
    · have e : tan x = tan (x - π) := by rw [tan_sub_pi]
      have hx : 3 ≤ tan x ↔ arctan 3 ≤ x - π := by
        rw [e]; exact three_le_tan_iff (by linarith) (by linarith)
      constructor
      · rintro ⟨_, h3⟩
        exact Or.inr ⟨by linarith [hx.1 h3], h'⟩
      · rintro (⟨_, h4⟩ | ⟨h3, h4⟩)
        · linarith
        · exact ⟨⟨by linarith, by linarith⟩, hx.2 (by linarith)⟩
    · subst h'
      have : tan (3 * π / 2) = 0 := by
        rw [tan_eq_sin_div_cos, show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]
        simp
      rw [this]
      constructor
      · rintro ⟨_, h3⟩; norm_num at h3
      · rintro (⟨_, h4⟩ | ⟨_, h4⟩) <;> linarith
    · constructor
      · rintro ⟨⟨_, h1⟩, h3⟩
        have e : tan x = tan (x - 2 * π) := by
          have := (tan_periodic.nat_mul 2).sub_eq x
          push_cast at this
          exact this.symm
        have hx : 3 ≤ tan x ↔ arctan 3 ≤ x - 2 * π := by
          rw [e]; exact three_le_tan_iff (by linarith) (by linarith)
        linarith [hx.1 h3]
      · rintro (⟨_, h4⟩ | ⟨_, h4⟩) <;> linarith

/-! ### Section 10.7: domains -/

private theorem not_int_iff {t : ℝ} : (∀ n : ℤ, t ≠ n) ↔ ∃ k : ℤ, (k : ℝ) < t ∧ t < k + 1 := by
  constructor
  · intro h
    refine ⟨⌊t⌋, lt_of_le_of_ne (Int.floor_le t) (h _).symm, Int.lt_floor_add_one t⟩
  · rintro ⟨k, h1, h2⟩ n hn
    have a : k < n := by exact_mod_cast (hn ▸ h1 : (k : ℝ) < n)
    have b : n < k + 1 := by exact_mod_cast (hn ▸ h2 : (n : ℝ) < k + 1)
    omega

/-- Stitz-Zeager Example 10.7.4(1): the domain of `f x = csc (2x + π/3)`, i.e. the set where
`sin (2x + π/3) ≠ 0`, is the union over integers `k` of the intervals
`((3k - 1)π/6, (3k + 2)π/6)`. -/
@[kb "stitzzeager2013" "Example 10.7.4, p. 880"]
theorem ex_10_7_4_a :
    {x : ℝ | sin (2 * x + π / 3) ≠ 0} =
      ⋃ k : ℤ, Ioo ((3 * k - 1) * π / 6) ((3 * k + 2) * π / 6) := by
  have hp := pi_pos
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_Ioo]
  have e : sin (2 * x + π / 3) ≠ 0 ↔ ∀ n : ℤ, (2 * x + π / 3) / π ≠ n := by
    rw [Ne, sin_eq_zero_iff]
    constructor
    · intro h n hn
      exact h ⟨n, ((div_eq_iff hp.ne').1 hn).symm⟩
    · rintro h ⟨n, hn⟩
      exact h n ((div_eq_iff hp.ne').2 hn.symm)
  rw [e, not_int_iff]
  refine exists_congr fun k => ?_
  rw [lt_div_iff₀ hp, div_lt_iff₀ hp]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

private theorem six_int_iff {s : ℝ} :
    (∀ m : ℤ, s ≠ 6 * m + 1 ∧ s ≠ 6 * m + 5) ↔
      ∃ k : ℤ, (6 * k + 1 < s ∧ s < 6 * k + 5) ∨ (6 * k + 5 < s ∧ s < 6 * k + 7) := by
  constructor
  · intro h
    set k : ℤ := ⌊(s - 1) / 6⌋ with hk
    have h1 : (k : ℝ) ≤ (s - 1) / 6 := Int.floor_le _
    have h2 : (s - 1) / 6 < k + 1 := Int.lt_floor_add_one _
    have h3 := h k
    refine ⟨k, ?_⟩
    have l1 : 6 * (k : ℝ) + 1 ≤ s := by linarith
    have l2 : s < 6 * (k : ℝ) + 7 := by linarith
    by_cases c : s < 6 * k + 5
    · left; exact ⟨lt_of_le_of_ne l1 (Ne.symm h3.1), c⟩
    · right; push Not at c
      exact ⟨lt_of_le_of_ne c (Ne.symm h3.2), l2⟩
  · rintro ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ m
    · constructor
      · intro hm
        have a : (k : ℝ) < m := by linarith
        have b : (m : ℝ) < k + 1 := by linarith
        have a' : k < m := by exact_mod_cast a
        have b' : m < k + 1 := by exact_mod_cast b
        omega
      · intro hm
        have a : (m : ℝ) < k := by linarith
        have b : (k : ℝ) - 1 < m := by linarith
        have a' : m < k := by exact_mod_cast a
        have b' : k - 1 < m := by
          have : ((k - 1 : ℤ) : ℝ) < m := by push_cast; exact b
          exact_mod_cast this
        omega
    · constructor
      · intro hm
        have a : (k : ℝ) < m := by linarith
        have b : (m : ℝ) < k + 1 := by linarith
        have a' : k < m := by exact_mod_cast a
        have b' : m < k + 1 := by exact_mod_cast b
        omega
      · intro hm
        have a : (m : ℝ) < k + 1 := by linarith
        have b : (k : ℝ) < m := by linarith
        have a' : k < m := by exact_mod_cast b
        have b' : m < k + 1 := by exact_mod_cast a
        omega

/-- Stitz-Zeager Example 10.7.4(2): the domain of `f x = sin x / (2 cos x - 1)` is the union
over integers `k` of `((6k+1)π/3, (6k+5)π/3) ∪ ((6k+5)π/3, (6k+7)π/3)`. -/
@[kb "stitzzeager2013" "Example 10.7.4, p. 880"]
theorem ex_10_7_4_b :
    {x : ℝ | 2 * cos x - 1 ≠ 0} =
      ⋃ k : ℤ, (Ioo ((6 * k + 1) * π / 3) ((6 * k + 5) * π / 3) ∪
        Ioo ((6 * k + 5) * π / 3) ((6 * k + 7) * π / 3)) := by
  have hp := pi_pos
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_union, mem_Ioo]
  have e : 2 * cos x - 1 ≠ 0 ↔ ∀ m : ℤ, 3 * x / π ≠ 6 * m + 1 ∧ 3 * x / π ≠ 6 * m + 5 := by
    have hc : 2 * cos x - 1 = 0 ↔ cos (π / 3) = cos x := by
      rw [cos_pi_div_three]; constructor <;> intro h <;> linarith
    rw [Ne, hc, cos_eq_cos_iff]
    constructor
    · intro h m
      constructor
      · intro hm
        rw [div_eq_iff hp.ne'] at hm
        exact h ⟨m, Or.inl (by linarith)⟩
      · intro hm
        rw [div_eq_iff hp.ne'] at hm
        exact h ⟨m + 1, Or.inr (by push_cast; linarith)⟩
    · rintro h ⟨k, hk | hk⟩
      · exact (h k).1 ((div_eq_iff hp.ne').2 (by linarith))
      · exact (h (k - 1)).2 ((div_eq_iff hp.ne').2 (by push_cast; linarith))
  rw [e, six_int_iff]
  refine exists_congr fun k => ?_
  simp only [lt_div_iff₀ hp, div_lt_iff₀ hp]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith

private theorem cos_le_sin_iff {y : ℝ} (h0 : 0 < y) (h1 : y < π) :
    cos y ≤ sin y ↔ π / 4 ≤ y := by
  have hp := pi_pos
  have sp : 0 < sin y := sin_pos_of_pos_of_lt_pi h0 h1
  by_cases c : y ≤ π / 2
  · constructor
    · intro h
      by_contra hh
      push Not at hh
      have h1' : sin y < sin (π / 4) :=
        strictMonoOn_sin ⟨by linarith, c⟩ ⟨by linarith, by linarith⟩ hh
      have h2' : cos (π / 4) < cos y :=
        strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hh
      rw [sin_pi_div_four] at h1'
      rw [cos_pi_div_four] at h2'
      linarith
    · intro h
      have hs : sin (π / 4) ≤ sin y :=
        strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, c⟩ h
      have hc : cos y ≤ cos (π / 4) :=
        strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
      rw [sin_pi_div_four] at hs
      rw [cos_pi_div_four] at hc
      linarith
  · push Not at c
    have : cos y ≤ 0 := by
      have := cos_nonneg_of_mem_Icc (x := y - π) ⟨by linarith, by linarith⟩
      rw [cos_sub_pi] at this; linarith
    constructor
    · intro _; linarith
    · intro _; linarith

private theorem cot_shift (y : ℝ) (k : ℤ) :
    cos (y + k * π) / sin (y + k * π) = cos y / sin y := by
  rw [cos_add_int_mul_pi, sin_add_int_mul_pi]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ (by norm_num))

/-- Stitz-Zeager Example 10.7.4(3): the domain of `f x = √(1 - cot x)` (cotangent written as
cosine over sine) is the union over integers `k` of `[(4k+1)π/4, (k+1)π)`. -/
@[kb "stitzzeager2013" "Example 10.7.4, p. 880"]
theorem ex_10_7_4_c :
    {x : ℝ | sin x ≠ 0 ∧ 0 ≤ 1 - cos x / sin x} =
      ⋃ k : ℤ, Ico ((4 * k + 1) * π / 4) ((k + 1) * π) := by
  have hp := pi_pos
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_Ico]
  constructor
  · rintro ⟨hs, hr⟩
    have hn : ∀ n : ℤ, x / π ≠ n := by
      intro n hn
      rw [div_eq_iff hp.ne'] at hn
      exact hs (sin_eq_zero_iff.2 ⟨n, hn.symm⟩)
    obtain ⟨k, h1, h2⟩ := not_int_iff.1 hn
    rw [lt_div_iff₀ hp] at h1
    rw [div_lt_iff₀ hp] at h2
    have hx : x = (x - k * π) + k * π := by ring
    have hy := cot_shift (x - k * π) k
    rw [← hx] at hy
    have sy : 0 < sin (x - k * π) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [hy] at hr
    have : cos (x - k * π) ≤ sin (x - k * π) := by
      rw [sub_nonneg, div_le_one sy] at hr; exact hr
    have := (cos_le_sin_iff (by linarith) (by linarith)).1 this
    exact ⟨k, by nlinarith, by nlinarith⟩
  · rintro ⟨k, h1, h2⟩
    have sy : 0 < sin (x - k * π) := sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
    have hx : x = (x - k * π) + k * π := by ring
    have hy := cot_shift (x - k * π) k
    rw [← hx] at hy
    have hs : sin x ≠ 0 := by
      intro h0
      have := sin_add_int_mul_pi (x - k * π) k
      rw [← hx, h0] at this
      have h' : (-1 : ℝ) ^ k * sin (x - k * π) ≠ 0 :=
        mul_ne_zero (zpow_ne_zero _ (by norm_num)) sy.ne'
      exact h' this.symm
    refine ⟨hs, ?_⟩
    rw [hy, sub_nonneg, div_le_one sy]
    exact (cos_le_sin_iff (by nlinarith) (by nlinarith)).2 (by nlinarith)

end UndergradKB.Precalculus.Course
