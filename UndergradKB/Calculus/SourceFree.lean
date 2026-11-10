import Mathlib.Tactic.TFAE
import UndergradKB.Common.Attr
import UndergradKB.Calculus.DivCurl
import UndergradKB.Calculus.CurlDivLimits

/-! # Calculus: source-free planar fields

The book (OpenStax Calculus 3, §6.4 and Theorem 6.15) states, for a field `F = (P, Q)` on a simply connected domain,
that these are equivalent: the flux across every closed curve is zero; the flux is independent of the path; `F` has a
stream function; `P_x + Q_y = 0`. We prove the equivalence on open *convex* domains. Mathlib's Poincaré lemma for
1-forms (`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`) is stated for convex sets; the simply connected case
needs the Poincaré lemma for simply connected open sets, which Mathlib announces as future work (its file
`MeasureTheory/Integral/CurveIntegral/Poincare.lean` proves the invariance under `C²` homotopies, but not the passage
from continuous to `C²` homotopies).

The direction "source free ⇒ `div F = 0`" holds on every open set: the flux across small circles divided by the
enclosed area tends to `div F` (`circulation_per_area_tendsto` applied to `(-Q, P)`). -/

namespace UndergradKB.Calculus

open Real Filter Topology Set

/-- The flux of `F = (P, Q)` is independent of the path in `U`: two regular `C¹` curves in `U` with the same
initial point and the same terminal point have the same flux (OpenStax Calculus 3:§6.4, the second of the equivalent
conditions for source-free fields). -/
def IsFluxPathIndependent2 (P Q : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ (x₁ y₁ : ℝ → ℝ) (a₁ b₁ : ℝ) (x₂ y₂ : ℝ → ℝ) (a₂ b₂ : ℝ),
    ContDiff ℝ 1 x₁ → ContDiff ℝ 1 y₁ → ContDiff ℝ 1 x₂ → ContDiff ℝ 1 y₂ →
    (∀ t ∈ uIcc a₁ b₁, (x₁ t, y₁ t) ∈ U) → (∀ t ∈ uIcc a₂ b₂, (x₂ t, y₂ t) ∈ U) →
    (∀ t ∈ uIcc a₁ b₁, speed2 x₁ y₁ t ≠ 0) → (∀ t ∈ uIcc a₂ b₂, speed2 x₂ y₂ t ≠ 0) →
    (x₁ a₁, y₁ a₁) = (x₂ a₂, y₂ a₂) → (x₁ b₁, y₁ b₁) = (x₂ b₂, y₂ b₂) →
    flux2 P Q x₁ y₁ a₁ b₁ = flux2 P Q x₂ y₂ a₂ b₂

lemma pdy2_neg (Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : pdy2 (fun q => -Q q) p = -pdy2 Q p := by
  unfold pdy2
  rw [fderiv_fun_neg]
  rfl

/-- On an open convex set, a `C¹` planar field with `div F = 0` has a stream function (Poincaré lemma for the
closed form `-Q dx + P dy`). -/
theorem exists_isStreamFunction_of_div2_eq_zero {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (h : ∀ p ∈ U, div2 P Q p = 0) : ∃ g, IsStreamFunction g P Q U := by
  have hPd : ∀ p ∈ U, DifferentiableAt ℝ P p := fun p hp =>
    (hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hQd : ∀ p ∈ U, DifferentiableAt ℝ (fun q => -Q q) p := fun p hp =>
    ((hQ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)).neg
  exact hc.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
    (fun p hp => (hasFDerivAt_form2 (hQd p hp) (hPd p hp)).differentiableAt.differentiableWithinAt)
    (fun p hp => (form2_symm_iff (hQd p hp) (hPd p hp)).2 (by
      have := h p hp
      unfold div2 at this
      rw [pdy2_neg]
      linarith))

/-- The circle of radius `ε` about `c`, as a pair of coordinate functions. -/
lemma circle_flux_eq {P Q : ℝ × ℝ → ℝ} (c : ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) :
    flux2 P Q (fun t => c.1 + ε * cos t) (fun t => c.2 + ε * sin t) 0 (2 * π) =
      ∫ t in (0 : ℝ)..2 * π, ((fun q => -Q q) (c + ε • (cos t, sin t)) * (-ε * sin t) +
        P (c + ε • (cos t, sin t)) * (ε * cos t)) := by
  have hdx : ∀ t, deriv (fun t => c.1 + ε * cos t) t = -ε * sin t := fun t => by
    have := ((hasDerivAt_cos t).const_mul ε).const_add c.1
    rw [this.deriv]; ring
  have hdy : ∀ t, deriv (fun t => c.2 + ε * sin t) t = ε * cos t := fun t => by
    have := ((hasDerivAt_sin t).const_mul ε).const_add c.2
    rw [this.deriv]
  have hreg : ∀ t ∈ uIcc 0 (2 * π), speed2 (fun t => c.1 + ε * cos t) (fun t => c.2 + ε * sin t) t ≠ 0 := by
    intro t _
    unfold speed2
    rw [hdx, hdy]
    have : (-ε * sin t) ^ 2 + (ε * cos t) ^ 2 = ε ^ 2 := by
      linear_combination ε ^ 2 * sin_sq_add_cos_sq t
    rw [this, Real.sqrt_sq hε.le]
    exact hε.ne'
  rw [flux2_eq_lineIntegral2 hreg]
  unfold lineIntegral2
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hpt : ((c.1 + ε * cos t, c.2 + ε * sin t) : ℝ × ℝ) = c + ε • (cos t, sin t) := by
    ext <;> simp
  simp only [hdx, hdy, hpt]

/-- OpenStax Calculus 3:Theorem 6.14 (CA-642; also one direction of CA-643, on every open set). A source-free planar
field (zero flux across every closed regular `C¹` curve in the open set `U`), continuous on the plane and
differentiable on `U`, has `div F = 0` on `U`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.14, p. 671"]
theorem div2_eq_zero_of_isSourceFree2 {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hPc : Continuous P) (hQc : Continuous Q) (hPd : ∀ p ∈ U, DifferentiableAt ℝ P p)
    (hQd : ∀ p ∈ U, DifferentiableAt ℝ Q p) (hs : IsSourceFree2 P Q U) :
    ∀ p ∈ U, div2 P Q p = 0 := by
  intro c hc
  have hlim := circulation_per_area_tendsto (fun q => -Q q) P hQc.neg hPc c (hQd c hc).neg (hPd c hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU c hc
  have hev : (fun ε : ℝ => (∫ t in (0 : ℝ)..2 * π,
        ((fun q => -Q q) (c + ε • (cos t, sin t)) * (-ε * sin t) +
          P (c + ε • (cos t, sin t)) * (ε * cos t))) / (π * ε ^ 2)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hmem : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ
    filter_upwards [hmem] with ε hε
    rw [← circle_flux_eq c hε.1]
    have hx : ContDiff ℝ 1 (fun t => c.1 + ε * cos t) := by fun_prop
    have hy : ContDiff ℝ 1 (fun t => c.2 + ε * sin t) := by fun_prop
    have hin : ∀ t ∈ uIcc 0 (2 * π), ((c.1 + ε * cos t, c.2 + ε * sin t) : ℝ × ℝ) ∈ U := by
      intro t _
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_mul, abs_of_pos hε.1]
      refine max_lt ?_ ?_
      · calc ε * |cos t| ≤ ε * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one t) hε.1.le
          _ < δ := by linarith [hε.2]
      · calc ε * |sin t| ≤ ε * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one t) hε.1.le
          _ < δ := by linarith [hε.2]
    have hclosed : ((c.1 + ε * cos 0, c.2 + ε * sin 0) : ℝ × ℝ) =
        (c.1 + ε * cos (2 * π), c.2 + ε * sin (2 * π)) := by simp
    have hdx : ∀ t, deriv (fun t => c.1 + ε * cos t) t = -ε * sin t := fun t => by
      have := ((hasDerivAt_cos t).const_mul ε).const_add c.1
      rw [this.deriv]; ring
    have hdy : ∀ t, deriv (fun t => c.2 + ε * sin t) t = ε * cos t := fun t => by
      have := ((hasDerivAt_sin t).const_mul ε).const_add c.2
      rw [this.deriv]
    have hreg : ∀ t ∈ uIcc 0 (2 * π),
        speed2 (fun t => c.1 + ε * cos t) (fun t => c.2 + ε * sin t) t ≠ 0 := by
      intro t _
      unfold speed2
      rw [hdx, hdy]
      have : (-ε * sin t) ^ 2 + (ε * cos t) ^ 2 = ε ^ 2 := by
        linear_combination ε ^ 2 * sin_sq_add_cos_sq t
      rw [this, Real.sqrt_sq hε.1.le]
      exact hε.1.ne'
    rw [hs _ _ 0 (2 * π) hx hy hin hclosed hreg, zero_div]
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  unfold div2
  have e1 : fderiv ℝ (fun q => -Q q) c (0, 1) = -pdy2 Q c := by
    rw [← pdy2_neg]; rfl
  rw [e1] at h0
  unfold pdx2
  linarith

lemma mem_uIcc_reverse {a b t : ℝ} (ht : t ∈ uIcc a b) : a + b - t ∈ uIcc a b := by
  rw [mem_uIcc] at ht ⊢
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

lemma hasDerivAt_reverse {x : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (a b t : ℝ) :
    HasDerivAt (fun s => x (a + b - s)) (-deriv x (a + b - t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => a + b - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (a + b)
  have h2 := ((hx.differentiable one_ne_zero) (a + b - t)).hasDerivAt
  have := h2.comp t h1
  rw [mul_neg_one] at this
  exact this

/-- Reversing the orientation of a curve changes the sign of the flux. -/
lemma flux2_reverse {P Q : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) {a b : ℝ}
    (hreg : ∀ t ∈ uIcc a b, speed2 x y t ≠ 0) :
    (∀ t ∈ uIcc a b, speed2 (fun s => x (a + b - s)) (fun s => y (a + b - s)) t ≠ 0) ∧
    flux2 P Q (fun s => x (a + b - s)) (fun s => y (a + b - s)) a b = -flux2 P Q x y a b := by
  have hdx := fun t => (hasDerivAt_reverse hx a b t).deriv
  have hdy := fun t => (hasDerivAt_reverse hy a b t).deriv
  have hsp : ∀ t, speed2 (fun s => x (a + b - s)) (fun s => y (a + b - s)) t = speed2 x y (a + b - t) := by
    intro t
    unfold speed2
    rw [hdx, hdy, neg_sq, neg_sq]
  have hreg' : ∀ t ∈ uIcc a b, speed2 (fun s => x (a + b - s)) (fun s => y (a + b - s)) t ≠ 0 :=
    fun t ht => by rw [hsp]; exact hreg _ (mem_uIcc_reverse ht)
  refine ⟨hreg', ?_⟩
  rw [flux2_eq hreg', flux2_eq hreg]
  simp only [hdx, hdy]
  have := intervalIntegral.integral_comp_sub_left
    (fun s => P (x s, y s) * deriv y s - Q (x s, y s) * deriv x s) (a + b) (a := a) (b := b)
  simp only [add_sub_cancel_right, add_sub_cancel_left] at this
  rw [← this, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- OpenStax Calculus 3:§6.4 List (equivalent conditions for source free) (CA-636), on an open convex domain
(the book: simply connected). For a planar field `F = (P, Q)`, continuous on the plane and `C¹` on `U`, these are
equivalent: (1) the flux across every closed regular `C¹` curve in `U` is zero; (2) the flux is independent of
the path; (3) `F` has a stream function on `U`; (4) `div F = P_x + Q_y = 0` on `U`. -/
@[kb "openstaxcalculus2016" "3:§6.4 List (equivalent conditions for source free), p. 653"]
theorem sourceFree_tfae {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    (hPc : Continuous P) (hQc : Continuous Q) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    [IsSourceFree2 P Q U, IsFluxPathIndependent2 P Q U, ∃ g, IsStreamFunction g P Q U,
      ∀ p ∈ U, div2 P Q p = 0].TFAE := by
  have hPd : ∀ p ∈ U, DifferentiableAt ℝ P p := fun p hp =>
    (hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hQd : ∀ p ∈ U, DifferentiableAt ℝ Q p := fun p hp =>
    (hQ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  tfae_have 1 → 4 := div2_eq_zero_of_isSourceFree2 hU hPc hQc hPd hQd
  tfae_have 4 → 3 := exists_isStreamFunction_of_div2_eq_zero hU hc hP hQ
  tfae_have 3 → 2 := by
    rintro ⟨g, hg⟩ x₁ y₁ a₁ b₁ x₂ y₂ a₂ b₂ hx₁ hy₁ hx₂ hy₂ hU₁ hU₂ hr₁ hr₂ hs ht
    rw [flux2_eq_lineIntegral2 hr₁, flux2_eq_lineIntegral2 hr₂,
      lineIntegral2_ftli hg hQc.neg.continuousOn hPc.continuousOn hx₁ hy₁ hU₁,
      lineIntegral2_ftli hg hQc.neg.continuousOn hPc.continuousOn hx₂ hy₂ hU₂, hs, ht]
  tfae_have 2 → 1 := by
    intro h x y a b hx hy hUxy hclosed hreg
    obtain ⟨hreg', hrev⟩ := flux2_reverse (P := P) (Q := Q) hx hy hreg
    have hx' : ContDiff ℝ 1 (fun s => x (a + b - s)) := hx.comp (by fun_prop)
    have hy' : ContDiff ℝ 1 (fun s => y (a + b - s)) := hy.comp (by fun_prop)
    have hU' : ∀ t ∈ uIcc a b, (x (a + b - t), y (a + b - t)) ∈ U :=
      fun t ht => hUxy _ (mem_uIcc_reverse ht)
    have := h x y a b (fun s => x (a + b - s)) (fun s => y (a + b - s)) a b hx hy hx' hy' hUxy hU' hreg hreg'
      (by simpa using hclosed) (by simpa using hclosed.symm)
    rw [hrev] at this
    linarith
  tfae_finish

/-- OpenStax Calculus 3:Theorem 6.15 (CA-643), on an open convex domain (the book: simply connected). A planar
field `F = (P, Q)`, continuous on the plane and `C¹` on `U`, is source free on `U` if and only if `div F = 0`
on `U`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.15, p. 672"]
theorem isSourceFree2_iff_div2_eq_zero {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hPc : Continuous P) (hQc : Continuous Q) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) :
    IsSourceFree2 P Q U ↔ ∀ p ∈ U, div2 P Q p = 0 :=
  (sourceFree_tfae hU hc hPc hQc hP hQ).out 1 4

end UndergradKB.Calculus
