import UndergradKB.Geometry.NeutralCongruence
import UndergradKB.Common.Attr

/-! # Neutral plane: parallel lines from angles (Petrunin, Exercise 11.6)

In a neutral plane, if `2·∡ABC + 2·∡BCD ≡ 0` then `(AB) ∥ (CD)`. The transversal property (7.9) needs Axiom V;
the neutral proof argues by contradiction with Proposition 11.5 applied to the triangle cut off by the two lines. -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- Moving the first side of an angle along its line changes the angle by `0` or `π`, so `2·∡` does not change. -/
theorem two_zsmul_angle_of_mem_line {O A Z X : P} (hA : A ≠ O) (hZ : Z ∈ N.line O A) (hZO : Z ≠ O)
    (hX : X ≠ O) : (2 : ℤ) • N.angle Z O X = (2 : ℤ) • N.angle A O X := by
  rcases N.mem_metricHalfLine_or_isBetween (Ne.symm hA) hZ with hr | hb
  · rw [N.angle_ray_left hA hr hZO hX]
  · have hπ : N.angle Z O A = π := (N.angle_eq_pi_iff hZO hA).2 hb
    rw [← N.axiomIIIb O Z A X hZO hA hX, hπ, smul_add, Real.Angle.two_zsmul_coe_pi, zero_add]

/-- **Exercise 11.6** (neutral plane). If `2·∡ABC + 2·∡BCD ≡ 0`, the lines `(AB)` and `(CD)` are parallel: equal or
disjoint. -/
@[kb "petrunin2025" "Exercise 11.6, p. 85"]
theorem parallel_of_two_zsmul_angle_add {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (h : (2 : ℤ) • N.angle A B C + (2 : ℤ) • N.angle B C D = 0) :
    N.line A B = N.line C D ∨ Disjoint (N.line A B) (N.line C D) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hmeet⟩ := hcon
  obtain ⟨Z, hZ1, hZ2⟩ := Set.not_disjoint_iff.1 hmeet
  -- if `C ∈ (AB)` then both lines are `(BC)`
  have key : C ∈ N.line A B → B ∈ N.line C D → False := by
    intro hC hB
    apply hne
    rw [← N.line_eq_of_mem hAB (N.right_mem_line A B) hC hBC,
      ← N.line_eq_of_mem hCD (N.left_mem_line C D) hB (Ne.symm hBC), N.line_comm]
  have degABC : C ∈ N.line A B ↔ (2 : ℤ) • N.angle A B C = 0 := by
    rw [← N.degenerate_iff_mem_line hAB, ← N.degenerate_iff_two_zsmul hAB (Ne.symm hBC)]
  have degBCD : B ∈ N.line C D ↔ (2 : ℤ) • N.angle B C D = 0 := by
    rw [← N.degenerate_iff_two_zsmul hBC hCD.symm, ← N.degenerate_iff_mem_line hCD]
    constructor
    · rintro ⟨L, hL, h1, h2, h3⟩
      exact ⟨L, hL, h3, h1, h2⟩
    · rintro ⟨L, hL, h1, h2, h3⟩
      exact ⟨L, hL, h2, h3, h1⟩
  by_cases hZB : Z = B
  · subst hZB
    have h2 := degBCD.1 hZ2
    rw [h2, add_zero] at h
    exact key (degABC.2 h) hZ2
  by_cases hZC : Z = C
  · subst hZC
    have h1 := degABC.1 hZ1
    rw [h1, zero_add] at h
    exact key hZ1 (degBCD.2 h)
  -- move the angles to the vertex `Z`
  have e1 : (2 : ℤ) • N.angle Z B C = (2 : ℤ) • N.angle A B C :=
    N.two_zsmul_angle_of_mem_line hAB (by rw [N.line_comm]; exact hZ1) hZB (Ne.symm hBC)
  have e2 : (2 : ℤ) • N.angle Z C B = (2 : ℤ) • N.angle D C B :=
    N.two_zsmul_angle_of_mem_line (Ne.symm hCD) hZ2 hZC hBC
  have hsum : (2 : ℤ) • (N.angle Z B C + N.angle B C Z) = 0 := by
    rw [smul_add, e1, N.angle_rev hBC hZC, smul_neg, e2, ← smul_neg,
      ← N.angle_rev hBC hCD.symm]
    exact h
  by_cases hdeg : IsTriangle.Degenerate Z B C
  · have hC : C ∈ N.line Z B := (N.degenerate_iff_mem_line hZB).1 hdeg
    have hl : N.line Z B = N.line A B :=
      N.line_eq_of_mem hAB (by rw [N.line_comm] at hZ1 ⊢; exact (N.line_comm A B ▸ hZ1))
        (N.right_mem_line A B) hZB
    have hB : B ∈ N.line C Z := by
      have hdeg' : IsTriangle.Degenerate C Z B := by
        obtain ⟨L, hL, h1, h2, h3⟩ := hdeg
        exact ⟨L, hL, h3, h1, h2⟩
      exact (N.degenerate_iff_mem_line (Ne.symm hZC)).1 hdeg'
    have hl2 : N.line C Z = N.line C D := N.line_eq_of_mem hCD (N.left_mem_line C D) hZ2 (Ne.symm hZC)
    exact key (by rw [← hl]; exact hC) (by rw [← hl2]; exact hB)
  -- the triangle `ZBC` is nondegenerate: Proposition 11.5 and the signs of its angles
  have hT : IsTriangle Z B C := ⟨hZB, hBC, Ne.symm hZC⟩
  have hs := (N.sign_angle_triangle hT hdeg).1
  have hs0 := N.sign_angle_ne_zero hT hdeg
  have h115 := N.uangle_add_uangle_lt_pi (A := B) (B := C) (C := Z) ⟨hBC, Ne.symm hZC, hZB⟩
    (fun hd => hdeg (by obtain ⟨L, hL, h1, h2, h3⟩ := hd; exact ⟨L, hL, h3, h1, h2⟩))
  set x := (N.angle Z B C).toReal with hx
  set y := (N.angle B C Z).toReal with hy
  have ux : N.uangle Z B C = |x| := rfl
  have uy : N.uangle B C Z = |y| := rfl
  have nπ : ∀ θ : Real.Angle, θ.sign ≠ 0 → θ ≠ π := fun θ h e => h (by rw [e, Real.Angle.sign_coe_pi])
  have sx : SignType.sign x = (N.angle Z B C).sign := Real.Angle.sign_toReal (nπ _ hs0)
  have sy : SignType.sign y = (N.angle B C Z).sign := Real.Angle.sign_toReal (nπ _ (hs ▸ hs0))
  have hc : ((2 * (x + y) : ℝ) : Real.Angle) = 0 := by
    rw [show (2 : ℝ) * (x + y) = x + y + (x + y) by ring, Real.Angle.coe_add, Real.Angle.coe_add, hx, hy,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal, ← two_zsmul]
    exact hsum
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.1 hc
  rw [zsmul_eq_mul] at hn
  have hpi := Real.pi_pos
  rcases lt_trichotomy x 0 with hxn | hx0 | hxp
  · have hyn : y < 0 := sign_eq_neg_one_iff.1 (by rw [sy, ← hs, ← sx]; exact sign_neg hxn)
    rw [ux, uy, abs_of_neg hxn, abs_of_neg hyn] at h115
    have a : (n : ℝ) < 0 := by nlinarith
    have b : (-1 : ℝ) < n := by nlinarith
    have a' : n < 0 := by exact_mod_cast a
    have b' : -1 < n := by exact_mod_cast b
    omega
  · exact hs0 (by rw [← sx, hx0, sign_zero])
  · have hyp : 0 < y := sign_eq_one_iff.1 (by rw [sy, ← hs, ← sx]; exact sign_pos hxp)
    rw [ux, uy, abs_of_pos hxp, abs_of_pos hyp] at h115
    have a : (0 : ℝ) < n := by nlinarith
    have b : (n : ℝ) < 1 := by nlinarith
    have a' : 0 < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega

end NeutralPlane

end Neutral

end UndergradKB.Geometry
