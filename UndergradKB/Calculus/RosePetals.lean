import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Card
import UndergradKB.Calculus.Polar
import UndergradKB.Common.Attr

/-! # Calculus: petals of roses

The rose `r = a cos(nθ)` has `n` petals for odd `n` and `2n` petals for even `n` (OpenStax Calculus 2:§7.3,
remark on petals of roses).  Each petal has exactly one tip, a point of the curve at the maximal distance `|a|`
from the pole, so we count tips. -/

namespace UndergradKB.Calculus

open Real Set

/-- The point of the circle of radius `|a|` at angle `t`. -/
noncomputable def circPt (a t : ℝ) : ℝ × ℝ := (a * cos t, a * sin t)

/-- The rose `r = a cos(nθ)` as a point set of the plane (OpenStax Calculus 2:§7.3, roses). -/
def roseCurve (a : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ θ : ℝ, p = polarPoint (a * cos (n * θ)) θ}

/-- The tips of the petals of the rose `r = a cos(nθ)`: the points of the curve at the maximal distance `|a|`
from the origin (each petal has exactly one such point). -/
def roseTips (a : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p ∈ roseCurve a n | p.1 ^ 2 + p.2 ^ 2 = a ^ 2}

/-- `N` equally spaced points on a circle of radius `|a|` are `N` distinct points. -/
theorem circle_points_ncard (a : ℝ) (ha : a ≠ 0) (N : ℕ) (hN : 0 < N) :
    {q : ℝ × ℝ | ∃ j : ℤ, q = circPt a (2 * π * j / N)}.ncard = N := by
  set f : ℕ → ℝ × ℝ := fun j => circPt a (2 * π * j / N) with hf
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hset : {q : ℝ × ℝ | ∃ j : ℤ, q = circPt a (2 * π * j / N)} = f '' ((Finset.range N : Finset ℕ) : Set ℕ) := by
    ext q
    simp only [mem_ofPred_eq, mem_image, Finset.coe_range, mem_Iio]
    constructor
    · rintro ⟨j, rfl⟩
      have h0 : 0 ≤ j % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
      have h1 : j % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
      refine ⟨(j % (N : ℤ)).toNat, by omega, ?_⟩
      have hj := Int.mul_ediv_add_emod j N
      have hang : 2 * π * (j : ℝ) / N = 2 * π * (((j % (N : ℤ)).toNat : ℕ) : ℝ) / N + ((j / (N : ℤ) : ℤ) : ℝ) * (2 * π) := by
        have : (((j % (N : ℤ)).toNat : ℕ) : ℝ) = ((j % (N : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg h0
        rw [this]
        have hj' : (j : ℝ) = N * ((j / (N : ℤ) : ℤ) : ℝ) + ((j % (N : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast hj.symm
        rw [hj']
        field_simp
        ring
      simp only [hf, circPt]
      rw [hang, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    · rintro ⟨j, _, rfl⟩
      exact ⟨j, by simp [hf]⟩
  have hinj : InjOn f ((Finset.range N : Finset ℕ) : Set ℕ) := by
    intro j1 h1 j2 h2 h
    simp only [Finset.coe_range, mem_Iio] at h1 h2
    simp only [hf, circPt, Prod.mk.injEq] at h
    obtain ⟨hc, hs⟩ := h
    have hc' := mul_left_cancel₀ ha hc
    have hs' := mul_left_cancel₀ ha hs
    have hang : ((2 * π * j1 / N : ℝ) : Real.Angle) = ((2 * π * j2 / N : ℝ) : Real.Angle) :=
      Real.Angle.cos_sin_inj hc' hs'
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
    have hk' : (j1 : ℝ) - j2 = k * N := by
      have hpi := Real.pi_pos
      field_simp at hk
      nlinarith [hk]
    have hk'' : (j1 : ℤ) - j2 = k * N := by exact_mod_cast hk'
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · nlinarith
      · nlinarith
    subst hk0
    omega
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]

/-- Description of the tips: `cos(nθ) = ±1`, so `nθ` is an integer multiple of `π`. -/
theorem mem_roseTips_iff (a : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) (q : ℝ × ℝ) :
    q ∈ roseTips a n ↔ ∃ m : ℤ, q = circPt a (2 * π * m / n) ∨
      q = circPt a (π * (2 * m + 1) / n + π) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rintro ⟨⟨θ, rfl⟩, hnorm⟩
    simp only [polarPoint] at hnorm
    have h1 : (a * cos (n * θ)) ^ 2 = a ^ 2 := by
      nlinarith [sin_sq_add_cos_sq θ]
    have h2 : cos (n * θ) ^ 2 = 1 := by
      have : a ^ 2 * (cos (n * θ) ^ 2 - 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.mp h) ha
      · linarith
    have h3 : sin (n * θ) = 0 := by
      have : sin (n * θ) ^ 2 = 0 := by nlinarith [sin_sq_add_cos_sq (n * θ)]
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h3
    have hθ : θ = k * π / n := by field_simp; linarith
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · refine ⟨m, Or.inl ?_⟩
      have : cos (n * θ) = 1 := by
        rw [← hk]
        have : ((2 * m : ℤ) : ℝ) * π = m * (2 * π) := by push_cast; ring
        rw [this, Real.cos_int_mul_two_pi]
      have e : 2 * π * m / n = θ := by rw [hθ]; push_cast; ring
      simp [polarPoint, circPt, this, e]
    · refine ⟨m, Or.inr ?_⟩
      have : cos (n * θ) = -1 := by
        rw [← hk]
        have : ((2 * m + 1 : ℤ) : ℝ) * π = π + m * (2 * π) := by push_cast; ring
        rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]
      have e : π * (2 * m + 1) / n = θ := by rw [hθ]; push_cast; ring
      simp [polarPoint, circPt, this, e, Real.cos_add_pi, Real.sin_add_pi]
  · rintro ⟨m, rfl | rfl⟩
    · have hc : cos (n * (2 * π * m / n)) = 1 := by
        have : (n : ℝ) * (2 * π * m / n) = m * (2 * π) := by field_simp
        rw [this, Real.cos_int_mul_two_pi]
      refine ⟨⟨2 * π * m / n, ?_⟩, ?_⟩
      · simp [polarPoint, circPt, hc]
      · simp only [circPt]
        nlinarith [sin_sq_add_cos_sq (2 * π * m / n)]
    · have hc : cos (n * (π * (2 * m + 1) / n)) = -1 := by
        have : (n : ℝ) * (π * (2 * m + 1) / n) = π + m * (2 * π) := by field_simp; ring
        rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]
      refine ⟨⟨π * (2 * m + 1) / n, ?_⟩, ?_⟩
      · simp [polarPoint, circPt, hc, Real.cos_add_pi, Real.sin_add_pi]
      · simp only [circPt]
        nlinarith [sin_sq_add_cos_sq (π * (2 * m + 1) / n + π)]

/-- OpenStax Calculus 2:§7.3 Remark on petals of roses (CA-403). The rose `r = a cos(nθ)` (`a ≠ 0`, `n ≥ 1`)
has `n` petals if `n` is odd and `2n` petals if `n` is even.  Each petal has exactly one tip, namely a point of
the curve at the maximal distance `|a|` from the pole, so the number of petals is the number of such tips. -/
@[kb "openstaxcalculus2016" "2:§7.3 Remark on petals of roses, p. 584"]
theorem rose_petal_count (a : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (roseTips a n).ncard = if Odd n then n else 2 * n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  split_ifs with hodd
  · obtain ⟨h, hh⟩ := hodd
    have hset : roseTips a n = {q : ℝ × ℝ | ∃ j : ℤ, q = circPt a (2 * π * j / n)} := by
      ext q
      rw [mem_roseTips_iff a ha n hn]
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨m, h1 | h2⟩
        · exact ⟨m, h1⟩
        · refine ⟨m + h + 1, ?_⟩
          rw [h2]
          congr 1
          have : (n : ℝ) = 2 * h + 1 := by rw [hh]; push_cast; ring
          field_simp
          rw [this]
          push_cast
          ring
      · rintro ⟨j, hj⟩
        exact ⟨j, Or.inl hj⟩
    rw [hset]
    exact circle_points_ncard a ha n hn
  · have hev : Even n := Nat.not_odd_iff_even.mp hodd
    obtain ⟨h, hh⟩ := hev
    have hN : (2 * n : ℕ) = 2 * n := rfl
    have hset : roseTips a n = {q : ℝ × ℝ | ∃ j : ℤ, q = circPt a (2 * π * j / ((2 * n : ℕ) : ℝ))} := by
      ext q
      rw [mem_roseTips_iff a ha n hn]
      simp only [mem_ofPred_eq]
      have hnh : (n : ℝ) = h + h := by rw [hh]; push_cast; ring
      have hcast : ((2 * n : ℕ) : ℝ) = 2 * n := by push_cast; ring
      rw [hcast]
      constructor
      · rintro ⟨m, h1 | h2⟩
        · refine ⟨2 * m, ?_⟩
          rw [h1]
          congr 1
          push_cast
          field_simp
        · refine ⟨2 * m + 1 + n, ?_⟩
          rw [h2]
          congr 1
          push_cast
          field_simp
      · rintro ⟨j, hj⟩
        obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
        · refine ⟨m, Or.inl ?_⟩
          rw [hj]
          congr 1
          push_cast
          field_simp
        · refine ⟨m - h, Or.inr ?_⟩
          rw [hj]
          congr 1
          push_cast
          field_simp
          rw [hnh]
          ring
    rw [hset]
    exact circle_points_ncard a ha (2 * n) (by omega)

/-- OpenStax Calculus 2:§7.3 Remark on petals of roses (CA-403), non-integer `n`. The rose `r = a cos(nθ)`
(`a ≠ 0`, `n > 0` real) is a closed curve (the point `θ ↦ (r cos θ, r sin θ)` is periodic in `θ`) if and only if
`n` is rational. -/
@[kb "openstaxcalculus2016" "2:§7.3 Remark on petals of roses, p. 584"]
theorem rose_periodic_iff_rational (a n : ℝ) (ha : a ≠ 0) (hn : 0 < n) :
    (∃ T > 0, ∀ θ, polarPoint (a * cos (n * (θ + T))) (θ + T) = polarPoint (a * cos (n * θ)) θ) ↔
      ∃ q : ℚ, n = q := by
  constructor
  · rintro ⟨T, hT, hper⟩
    have hsq : ∀ θ, cos (n * (θ + T)) ^ 2 = cos (n * θ) ^ 2 := fun θ => by
      have h := hper θ
      simp only [polarPoint, Prod.mk.injEq] at h
      have e : (a * cos (n * (θ + T))) ^ 2 = (a * cos (n * θ)) ^ 2 := by
        have h1 := h.1
        have h2 := h.2
        nlinarith [sin_sq_add_cos_sq (θ + T), sin_sq_add_cos_sq θ, h1, h2,
          congrArg (· ^ 2) h1, congrArg (· ^ 2) h2]
      have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      rw [mul_pow, mul_pow] at e
      exact mul_left_cancel₀ ha2 e
    have h0 := hsq 0
    simp only [zero_add, mul_zero, cos_zero, one_pow] at h0
    have hc2 : cos (2 * (n * T)) = 1 := by rw [cos_two_mul, h0]; ring
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 hc2
    have hp := hper 0
    simp only [polarPoint, zero_add, mul_zero, cos_zero, sin_zero, mul_one, Prod.mk.injEq] at hp
    have hcne : cos (n * T) ≠ 0 := by
      intro h; rw [h] at h0; norm_num at h0
    have hsT : sin T = 0 := by
      have := hp.2
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' ha
        · exact absurd h' hcne
      · exact h
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hsT
    have hm0 : (m : ℝ) ≠ 0 := by
      intro h; rw [h, zero_mul] at hm; linarith
    refine ⟨(k : ℚ) / m, ?_⟩
    push_cast
    rw [eq_div_iff hm0]
    have hpi := pi_pos
    have : n * T = k * π := by linarith
    rw [← hm] at this
    have := mul_right_cancel₀ hpi.ne' (by linarith : n * m * π = k * π)
    linarith
  · rintro ⟨q, rfl⟩
    refine ⟨2 * π * q.den, by positivity, fun θ => ?_⟩
    have e1 : (q : ℝ) * (θ + 2 * π * q.den) = q * θ + (q.num : ℤ) * (2 * π) := by
      have : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
      linear_combination (2 * π) * this
    have e2 : θ + 2 * π * q.den = θ + (q.den : ℕ) * (2 * π) := by ring
    rw [e1, Real.cos_add_int_mul_two_pi, e2]
    simp only [polarPoint, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

end UndergradKB.Calculus
