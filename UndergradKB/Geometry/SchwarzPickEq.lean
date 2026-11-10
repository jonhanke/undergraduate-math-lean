import Mathlib.Analysis.Complex.Schwarz
import UndergradKB.Geometry.HypAngles
import UndergradKB.Common.Attr

/-! # Schwarz-Pick theorem: the equality case (Petrunin, Theorem 18.19, pp. 155-156)

Wave 1 proved the inequality `hdist (f z) (f w) ≤ hdist z w` (`schwarz_pick`). Here: if equality
holds for one pair of distinct points, then `f` is a fractional linear transformation of the form
`y ↦ mobius (-f w) (s · mobius w y)` with `‖s‖ = 1`, and it preserves the h-distance of every pair
(a motion of the h-plane). The proof uses the equality case of the Schwarz lemma in Mathlib
(`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`). -/

namespace UndergradKB.Geometry

open Complex ComplexConjugate Metric

variable {z w : ℂ}

/-- Multiplication by a unit complex number preserves the h-distance (a rotation about the centre). -/
theorem hdist_mul_left {s : ℂ} (hs : ‖s‖ = 1) (P Q : ℂ) : hdist (s * P) (s * Q) = hdist P Q := by
  unfold hdist hcosh
  rw [← mul_sub, norm_mul, norm_mul, norm_mul, hs, one_mul, one_mul, one_mul]

/-- **Schwarz-Pick theorem, equality case (Theorem 18.19, p. 156).** Let `f` be holomorphic on the
open unit disc `D` with `f(D) ⊆ D`. If `d_h(f z, f w) = d_h(z, w)` for one pair of distinct points
`z, w ∈ D`, then there is a unit complex number `s` with `f y = mobius (-f w) (s · mobius w y)` for
all `y ∈ D` (so `f` is a fractional linear transformation), and `f` preserves the h-distance of every
pair of points of `D` (it is a motion of the h-plane). -/
@[kb "petrunin2025" "Theorem 18.19, pp. 155-156"]
theorem schwarz_pick_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : ∀ z, ‖z‖ < 1 → ‖f z‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hzw : z ≠ w)
    (heq : hdist (f z) (f w) = hdist z w) :
    ∃ s : ℂ, ‖s‖ = 1 ∧ (∀ y, ‖y‖ < 1 → f y = mobius (-f w) (s * mobius w y)) ∧
      ∀ y y', ‖y‖ < 1 → ‖y'‖ < 1 → hdist (f y) (f y') = hdist y y' := by
  have hfw := hmaps w hw
  have hnw : ‖-w‖ < 1 := by simpa using hw
  set g : ℂ → ℂ := fun u => mobius (f w) (f (mobius (-w) u)) with hg
  have hm1 : Set.MapsTo (mobius (-w)) (ball 0 1) (ball 0 1) := fun u hu => by
    simpa using norm_mobius_lt_one hnw (by simpa using hu)
  have hm2 : Set.MapsTo f (ball 0 1) (ball 0 1) := fun u hu => by
    simpa using hmaps u (by simpa using hu)
  have hd : DifferentiableOn ℂ g (ball 0 1) :=
    (differentiableOn_mobius hfw).comp (hf.comp (differentiableOn_mobius hnw) hm1) (hm2.comp hm1)
  have h0 : g 0 = 0 := by
    have : mobius (-w) 0 = w := by simp [mobius]
    simp only [hg, this]
    exact mobius_self hfw
  have hmap : Set.MapsTo g (ball 0 1) (closedBall (g 0) 1) := fun u hu => by
    have := norm_mobius_lt_one hfw (hmaps _ (norm_mobius_lt_one hnw (by simpa using hu)))
    rw [h0]
    simpa using this.le
  set m := mobius w z with hm
  have hmn : ‖m‖ < 1 := norm_mobius_lt_one hw hz
  have hm0 : m ≠ 0 := fun h => hzw ((mobius_eq_zero_iff hw hz).1 h)
  have e : g m = mobius (f w) (f z) := by
    simp only [hg, hm, mobius_neg_mobius hw hz]
  have hgm : ‖g m‖ < 1 := by rw [e]; exact norm_mobius_lt_one hfw (hmaps z hz)
  have e1 : hdist (f z) (f w) = hdist 0 (g m) := by
    rw [e, ← hdist_mobius hfw (hmaps z hz) hfw, mobius_self hfw, hdist_comm]
  have e2 : hdist z w = hdist 0 m := by
    rw [hm, ← hdist_mobius hw hz hw, mobius_self hw, hdist_comm]
  have hnorm : ‖g m‖ = ‖m‖ := by
    rw [(hdist_zero_eq_iff hgm).1 rfl, (hdist_zero_eq_iff hmn).1 rfl, ← e1, ← e2, heq]
  have hslope : ‖dslope g 0 m‖ = 1 / 1 := by
    rw [dslope_of_ne _ hm0, slope_def_field, h0, sub_zero, sub_zero, norm_div, hnorm,
      div_self (norm_ne_zero_iff.2 hm0), div_one]
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hmap
    (by simpa using hmn) hslope
  set s := dslope g 0 m
  have hs : ‖s‖ = 1 := by rw [hslope]; norm_num
  have hgy : ∀ u, ‖u‖ < 1 → g u = s * u := fun u hu => by
    have := haff (show u ∈ ball (0 : ℂ) 1 by simpa using hu)
    rw [this, h0]; simp [mul_comm]
  have hfy : ∀ y, ‖y‖ < 1 → f y = mobius (-f w) (s * mobius w y) := fun y hy => by
    have hmy := norm_mobius_lt_one hw hy
    rw [← hgy _ hmy]
    simp only [hg, mobius_neg_mobius hw hy]
    rw [mobius_neg_mobius hfw (hmaps y hy)]
  refine ⟨s, hs, hfy, fun y y' hy hy' => ?_⟩
  have hnfw : ‖-f w‖ < 1 := by simpa using hfw
  have hsy : ‖s * mobius w y‖ < 1 := by rw [norm_mul, hs, one_mul]; exact norm_mobius_lt_one hw hy
  have hsy' : ‖s * mobius w y'‖ < 1 := by
    rw [norm_mul, hs, one_mul]; exact norm_mobius_lt_one hw hy'
  rw [hfy y hy, hfy y' hy', hdist_mobius hnfw hsy hsy', hdist_mul_left hs, hdist_mobius hw hy hy']

end UndergradKB.Geometry
