import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.Segment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import UndergradKB.Common.Attr

/-! # The Bendixson-Dulac theorem for closed trajectories star-shaped about a point
(Lebl, *Notes on Diffy Qs*, Theorem 8.4.2)

For the planar autonomous system `x' = f(x, y)`, `y' = g(x, y)` on a region `R`, if the divergence
`∂(φ f)/∂x + ∂(φ g)/∂y` (for a continuously differentiable Dulac function `φ`; the book's statement is `φ = 1`)
does not change sign on `R` and vanishes only on a set with empty interior ("a small set such as isolated points or
curves"), then there is no closed trajectory in `R`.

The book proves this by Green's theorem on the region enclosed by the closed trajectory, which needs the Jordan curve
theorem (not in Mathlib).  We prove it for closed trajectories that are star-shaped about a point `c`: the trajectory
is never tangent to a ray from `c` (the angle about `c` moves strictly monotonically), and the segments from `c` to
the trajectory lie in `R` (true for every `c` when `R` is convex, and for a centre `c` when `R` is star-shaped).

Proof (Green's theorem for the cone over the curve, without the Jordan curve theorem).  Let
`Φ(s, t) = c + s ((x, y)(t) - c)` on `[0, 1] × [0, T]`, and pull back the 1-form `P dy - Q dx` (`P = φ f`,
`Q = φ g`): `A ds + B dt` with `A = P(Φ)(y - c₂) - Q(Φ)(x - c₁)` and `B = s (P(Φ) y' - Q(Φ) x')`.  The chain rule
gives `∂B/∂s - ∂A/∂t = s · div(Φ) · ((x - c₁) y' - (y - c₂) x')`.  Integrating, `∫∂A/∂t dt = 0` by periodicity,
`∫∂B/∂s ds = B(1, t) = φ (f g - g f) = 0` along the trajectory, so the double integral of the right side vanishes.
But the right side has one sign and, by the inverse function theorem (`Φ` is a local diffeomorphism where the
trajectory is transverse to the rays), is nonzero somewhere: a contradiction. -/

namespace UndergradKB.DifferentialEquations

open Set Filter Topology MeasureTheory intervalIntegral

/-- The divergence `∂P/∂x + ∂Q/∂y` of the planar vector field `(P, Q)` at `p`. -/
noncomputable def planarDiv (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)

/-- The cone over the curve `(x, y)` with vertex `c`: `c + s ((x t, y t) - c)`. -/
def starHom (c : ℝ × ℝ) (x y : ℝ → ℝ) (s t : ℝ) : ℝ × ℝ :=
  (c.1 + s * (x t - c.1), c.2 + s * (y t - c.2))

lemma clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) : L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma starHom_mem_segment (c : ℝ × ℝ) (x y : ℝ → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    starHom c x y s t ∈ segment ℝ c (x t, y t) :=
  ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, by ext <;> simp [starHom] <;> ring⟩

lemma hasDerivAt_starHom_t (c : ℝ × ℝ) {x y vx vy : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (vx t) t)
    (hy : ∀ t, HasDerivAt y (vy t) t) (s t : ℝ) :
    HasDerivAt (fun t => starHom c x y s t) (s * vx t, s * vy t) t := by
  have h1 := (((hx t).sub_const c.1).const_mul s).const_add c.1
  have h2 := (((hy t).sub_const c.2).const_mul s).const_add c.2
  exact h1.prodMk h2

lemma hasDerivAt_starHom_s (c : ℝ × ℝ) (x y : ℝ → ℝ) (s t : ℝ) :
    HasDerivAt (fun s => starHom c x y s t) (x t - c.1, y t - c.2) s := by
  have h1 := ((hasDerivAt_id s).mul_const (x t - c.1)).const_add c.1
  have h2 := ((hasDerivAt_id s).mul_const (y t - c.2)).const_add c.2
  simp only [id, one_mul] at h1 h2
  exact h1.prodMk h2

lemma continuous_starHom (c : ℝ × ℝ) {x y : ℝ → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun q : ℝ × ℝ => starHom c x y q.1 q.2) := by
  unfold starHom; fun_prop

section Core

variable {D : Set (ℝ × ℝ)} {P Q : ℝ × ℝ → ℝ} {x y vx vy : ℝ → ℝ} {c : ℝ × ℝ} {T : ℝ}

/-- `∂A/∂t` for the pulled-back form. -/
noncomputable def pbA' (P Q : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (x y vx vy : ℝ → ℝ) (s t : ℝ) : ℝ :=
  fderiv ℝ P (starHom c x y s t) (s * vx t, s * vy t) * (y t - c.2) + P (starHom c x y s t) * vy t
    - (fderiv ℝ Q (starHom c x y s t) (s * vx t, s * vy t) * (x t - c.1) + Q (starHom c x y s t) * vx t)

/-- `∂B/∂s` for the pulled-back form. -/
noncomputable def pbB' (P Q : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (x y vx vy : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (P (starHom c x y s t) * vy t - Q (starHom c x y s t) * vx t)
    + s * (fderiv ℝ P (starHom c x y s t) (x t - c.1, y t - c.2) * vy t
      - fderiv ℝ Q (starHom c x y s t) (x t - c.1, y t - c.2) * vx t)

/-- The integrand `s · div(Φ) · ((x - c₁) y' - (y - c₂) x')`. -/
noncomputable def pbG (P Q : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (x y vx vy : ℝ → ℝ) (s t : ℝ) : ℝ :=
  s * planarDiv P Q (starHom c x y s t) * ((x t - c.1) * vy t - (y t - c.2) * vx t)

lemma pbB'_sub_pbA' (s t : ℝ) :
    pbB' P Q c x y vx vy s t - pbA' P Q c x y vx vy s t = pbG P Q c x y vx vy s t := by
  unfold pbB' pbA' pbG planarDiv
  rw [clm_apply_pair (fderiv ℝ P _) (s * vx t), clm_apply_pair (fderiv ℝ Q _) (s * vx t),
    clm_apply_pair (fderiv ℝ P _) (x t - c.1), clm_apply_pair (fderiv ℝ Q _) (x t - c.1)]
  ring

variable (hD : IsOpen D) (hP : ContDiffOn ℝ 1 P D) (hQ : ContDiffOn ℝ 1 Q D)
  (hx : ∀ t, HasDerivAt x (vx t) t) (hy : ∀ t, HasDerivAt y (vy t) t)
  (hvx : Continuous vx) (hvy : Continuous vy)
  (hseg : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, starHom c x y s t ∈ D)
include hD hP hQ hx hy hvx hvy hseg

omit hP hQ hx hy hvx hvy hseg in
lemma hasFDerivAt_of_mem' {R : ℝ × ℝ → ℝ} (hR : ContDiffOn ℝ 1 R D) {p : ℝ × ℝ} (hp : p ∈ D) :
    HasFDerivAt R (fderiv ℝ R p) p :=
  ((hR.differentiableOn one_ne_zero p hp).differentiableAt (hD.mem_nhds hp)).hasFDerivAt

omit hP hQ hvx hvy hseg in
lemma continuousOn_pb_aux {R : ℝ × ℝ → ℝ} (hR : ContDiffOn ℝ 1 R D) {w : ℝ × ℝ → ℝ × ℝ}
    (hw : Continuous w) {K : Set (ℝ × ℝ)} (hK : MapsTo (fun q : ℝ × ℝ => starHom c x y q.1 q.2) K D) :
    ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ R (starHom c x y q.1 q.2) (w q)) K ∧
      ContinuousOn (fun q : ℝ × ℝ => R (starHom c x y q.1 q.2)) K := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hΦ := continuous_starHom c hxc hyc
  refine ⟨?_, (hR.continuousOn.comp hΦ.continuousOn hK)⟩
  exact ((hR.continuousOn_fderiv_of_isOpen hD le_rfl).comp hΦ.continuousOn hK).clm_apply hw.continuousOn

omit hD hP hQ hx hy hvx hvy in
/-- The set `[0, 1] × ℝ` is mapped into `D` by the cone map. -/
lemma mapsTo_strip :
    MapsTo (fun q : ℝ × ℝ => starHom c x y q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) D :=
  fun q hq => hseg q.2 q.1 hq.1

lemma continuousOn_pbA' :
    ContinuousOn (fun q : ℝ × ℝ => pbA' P Q c x y vx vy q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  have hm := mapsTo_strip (c := c) hseg
  have hw : Continuous (fun q : ℝ × ℝ => (q.1 * vx q.2, q.1 * vy q.2)) := by fun_prop
  obtain ⟨hP1, hP2⟩ := continuousOn_pb_aux hD hx hy hP hw hm
  obtain ⟨hQ1, hQ2⟩ := continuousOn_pb_aux hD hx hy hQ hw hm
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  unfold pbA'
  refine ((hP1.mul ?_).add (hP2.mul ?_)).sub ((hQ1.mul ?_).add (hQ2.mul ?_)) <;>
    exact Continuous.continuousOn (by fun_prop)

lemma continuousOn_pbB' :
    ContinuousOn (fun q : ℝ × ℝ => pbB' P Q c x y vx vy q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  have hm := mapsTo_strip (c := c) hseg
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hw : Continuous (fun q : ℝ × ℝ => (x q.2 - c.1, y q.2 - c.2)) := by fun_prop
  obtain ⟨hP1, hP2⟩ := continuousOn_pb_aux hD hx hy hP hw hm
  obtain ⟨hQ1, hQ2⟩ := continuousOn_pb_aux hD hx hy hQ hw hm
  unfold pbB'
  refine ((hP2.mul ?_).sub (hQ2.mul ?_)).add (Continuous.continuousOn (continuous_fst) |>.mul
    ((hP1.mul ?_).sub (hQ1.mul ?_))) <;> exact Continuous.continuousOn (by fun_prop)

lemma continuousOn_pbG :
    ContinuousOn (fun q : ℝ × ℝ => pbG P Q c x y vx vy q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  have := (continuousOn_pbB' hD hP hQ hx hy hvx hvy hseg).sub
    (continuousOn_pbA' hD hP hQ hx hy hvx hvy hseg)
  refine this.congr fun q _ => ?_
  exact (pbB'_sub_pbA' q.1 q.2).symm

omit hvx hvy in
lemma hasDerivAt_pbA {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (fun t => P (starHom c x y s t) * (y t - c.2) - Q (starHom c x y s t) * (x t - c.1))
      (pbA' P Q c x y vx vy s t) t := by
  have hΦ := hasDerivAt_starHom_t c hx hy s t
  have hPt := (hasFDerivAt_of_mem' hD hP (hseg t s hs)).comp_hasDerivAt t hΦ
  have hQt := (hasFDerivAt_of_mem' hD hQ (hseg t s hs)).comp_hasDerivAt t hΦ
  have := (hPt.mul ((hy t).sub_const c.2)).sub (hQt.mul ((hx t).sub_const c.1))
  refine this.congr_deriv ?_
  unfold pbA'; simp only [Function.comp]

omit hx hy hvx hvy in
lemma hasDerivAt_pbB (t : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => s * (P (starHom c x y s t) * vy t - Q (starHom c x y s t) * vx t))
      (pbB' P Q c x y vx vy s t) s := by
  have hΦ := hasDerivAt_starHom_s c x y s t
  have hPt := (hasFDerivAt_of_mem' hD hP (hseg t s hs)).comp_hasDerivAt s hΦ
  have hQt := (hasFDerivAt_of_mem' hD hQ (hseg t s hs)).comp_hasDerivAt s hΦ
  have := (hasDerivAt_id s).mul ((hPt.mul_const (vy t)).sub (hQt.mul_const (vx t)))
  refine this.congr_deriv ?_
  unfold pbB'; simp only [Function.comp, id, Pi.sub_apply, one_mul]

set_option maxHeartbeats 400000 in
/-- **Green's theorem for the cone over a closed curve.**  For a closed curve `(x, y)` (period `T`) along which
`P y' - Q x' = 0`, the integral of `s · div(P, Q)(Φ) · ((x - c₁) y' - (y - c₂) x')` over `[0, 1] × [0, T]`
vanishes. -/
theorem integral_pbG_eq_zero (hT : 0 ≤ T) (hxT : x T = x 0) (hyT : y T = y 0)
    (htan : ∀ t, P (x t, y t) * vy t - Q (x t, y t) * vx t = 0) :
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..T, pbG P Q c x y vx vy s t = 0 := by
  have hA := continuousOn_pbA' hD hP hQ hx hy hvx hvy hseg
  have hB := continuousOn_pbB' hD hP hQ hx hy hvx hvy hseg
  -- continuity in `t` for fixed `s ∈ [0, 1]`, and in `s` for fixed `t`
  have hAt : ∀ s ∈ Icc (0 : ℝ) 1, Continuous (fun t => pbA' P Q c x y vx vy s t) := fun s hs =>
    hA.comp_continuous (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (by fun_prop) (fun t => ⟨hs, mem_univ t⟩)
  have hBt : ∀ s ∈ Icc (0 : ℝ) 1, Continuous (fun t => pbB' P Q c x y vx vy s t) := fun s hs =>
    hB.comp_continuous (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (by fun_prop) (fun t => ⟨hs, mem_univ t⟩)
  have hBs : ∀ t, ContinuousOn (fun s => pbB' P Q c x y vx vy s t) (Icc 0 1) := fun t =>
    hB.comp (g := fun q : ℝ × ℝ => pbB' P Q c x y vx vy q.1 q.2) (f := fun s : ℝ => ((s, t) : ℝ × ℝ))
      (Continuous.continuousOn (by fun_prop)) (fun s hs => ⟨hs, mem_univ t⟩)
  -- inner integral of `∂A/∂t` vanishes
  have hAint : ∀ s ∈ Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..T, pbA' P Q c x y vx vy s t = 0 := by
    intro s hs
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_pbA hD hP hQ hx hy hseg hs t)
      ((hAt s hs).intervalIntegrable _ _)]
    simp [hxT, hyT, starHom]
  -- integral of `∂B/∂s` in `s` vanishes
  have hBint : ∀ t, ∫ s in (0 : ℝ)..1, pbB' P Q c x y vx vy s t = 0 := by
    intro t
    rw [integral_eq_sub_of_hasDerivAt (fun s hs => hasDerivAt_pbB hD hP hQ hseg t
      (by rwa [uIcc_of_le zero_le_one] at hs))
      ((hBs t).intervalIntegrable_of_Icc zero_le_one)]
    have : starHom c x y 1 t = (x t, y t) := by ext <;> simp [starHom]
    simp [this, htan t]
  -- Fubini for `∂B/∂s`
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc 0 T) := isCompact_Icc.prod isCompact_Icc
  have hBint2 : IntegrableOn (Function.uncurry fun s t => pbB' P Q c x y vx vy s t)
      (uIoc 0 1 ×ˢ uIoc 0 T) := by
    refine (ContinuousOn.integrableOn_compact hK
      (hB.mono (prod_mono subset_rfl (subset_univ _)))).mono_set ?_
    rw [uIoc_of_le zero_le_one, uIoc_of_le hT]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hswap := intervalIntegral_intervalIntegral_swap hBint2
  have h0 : ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..T, pbB' P Q c x y vx vy s t = 0 := by
    rw [hswap]; simp [hBint]
  refine (intervalIntegral.integral_congr fun s hs => ?_).trans h0
  rw [uIcc_of_le zero_le_one] at hs
  have hsub := intervalIntegral.integral_sub ((hBt s hs).intervalIntegrable (μ := volume) 0 T)
    ((hAt s hs).intervalIntegrable (μ := volume) 0 T)
  rw [hAint s hs, sub_zero] at hsub
  rw [← hsub]
  exact intervalIntegral.integral_congr fun t _ => (pbB'_sub_pbA' s t).symm

end Core

/-- A continuous real function on `ℝ` that never vanishes has one strict sign. -/
lemma pos_or_neg_of_ne_zero {k : ℝ → ℝ} (hk : Continuous k) (h : ∀ t, k t ≠ 0) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ t, 0 < ε * k t := by
  by_cases hpos : ∀ t, 0 < k t
  · exact ⟨1, one_ne_zero, fun t => by simpa using hpos t⟩
  · push Not at hpos
    obtain ⟨a, ha⟩ := hpos
    have ha' : k a < 0 := lt_of_le_of_ne ha (h a)
    refine ⟨-1, by norm_num, fun t => ?_⟩
    rcases lt_or_gt_of_ne (h t) with ht | ht
    · linarith
    · exfalso
      obtain ⟨u, hu⟩ := intermediate_value_univ a t hk ⟨ha'.le, ht.le⟩
      exact h u hu

/-- The cone map is a local diffeomorphism where the curve is transverse to the rays from `c`, so its image of a
neighbourhood of `(s₀, t₀)` (with `s₀ ≠ 0`) is a neighbourhood. -/
lemma starHom_image_mem_nhds {x y vx vy : ℝ → ℝ} (c : ℝ × ℝ) (hx : ∀ t, HasDerivAt x (vx t) t)
    (hy : ∀ t, HasDerivAt y (vy t) t) (hvx : Continuous vx) (hvy : Continuous vy) {s₀ t₀ : ℝ} (hs₀ : s₀ ≠ 0)
    (hcross : (x t₀ - c.1) * vy t₀ - (y t₀ - c.2) * vx t₀ ≠ 0) {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 (s₀, t₀)) :
    (fun q : ℝ × ℝ => starHom c x y q.1 q.2) '' S ∈ 𝓝 (starHom c x y s₀ t₀) := by
  have hxd : deriv x = vx := funext fun t => (hx t).deriv
  have hyd : deriv y = vy := funext fun t => (hy t).deriv
  have hxc : ContDiff ℝ 1 x :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hx t).differentiableAt, hxd ▸ hvx⟩
  have hyc : ContDiff ℝ 1 y :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hy t).differentiableAt, hyd ▸ hvy⟩
  set Ψ : ℝ × ℝ → ℝ × ℝ := fun q => starHom c x y q.1 q.2 with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ := by
    simp only [hΨdef, starHom]
    fun_prop
  set L := fderiv ℝ Ψ (s₀, t₀)
  have hL : HasFDerivAt Ψ L (s₀, t₀) := (hΨ.differentiable one_ne_zero _).hasFDerivAt
  have hstrict : HasStrictFDerivAt Ψ L (s₀, t₀) := hΨ.contDiffAt.hasStrictFDerivAt hL one_ne_zero
  -- the two columns of `L`
  have h10 : L (1, 0) = (x t₀ - c.1, y t₀ - c.2) := by
    have h1 := hL.comp_hasDerivAt s₀ ((hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ t₀))
    exact h1.unique (hasDerivAt_starHom_s c x y s₀ t₀)
  have h01 : L (0, 1) = (s₀ * vx t₀, s₀ * vy t₀) := by
    have h1 := hL.comp_hasDerivAt t₀ ((hasDerivAt_const t₀ s₀).prodMk (hasDerivAt_id t₀))
    exact h1.unique (hasDerivAt_starHom_t c hx hy s₀ t₀)
  have hinj : Function.Injective (L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have hq' : L q = 0 := hq
    have hdec : q = q.1 • ((1 : ℝ), (0 : ℝ)) + q.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hdec, map_add, map_smul, map_smul, h10, h01] at hq'
    have e1 : q.1 * (x t₀ - c.1) + q.2 * (s₀ * vx t₀) = 0 := by
      simpa using congrArg Prod.fst hq'
    have e2 : q.1 * (y t₀ - c.2) + q.2 * (s₀ * vy t₀) = 0 := by
      simpa using congrArg Prod.snd hq'
    have hk : s₀ * ((x t₀ - c.1) * vy t₀ - (y t₀ - c.2) * vx t₀) ≠ 0 := mul_ne_zero hs₀ hcross
    have ha : q.1 * (s₀ * ((x t₀ - c.1) * vy t₀ - (y t₀ - c.2) * vx t₀)) = 0 := by
      linear_combination (s₀ * vy t₀) * e1 - (s₀ * vx t₀) * e2
    have hb : q.2 * (s₀ * ((x t₀ - c.1) * vy t₀ - (y t₀ - c.2) * vx t₀)) = 0 := by
      linear_combination (x t₀ - c.1) * e2 - (y t₀ - c.2) * e1
    have h1 := (mul_eq_zero.1 ha).resolve_right hk
    have h2 := (mul_eq_zero.1 hb).resolve_right hk
    ext <;> simp [h1, h2]
  have hsurj : (L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ).range = ⊤ :=
    LinearMap.range_eq_top.2 (LinearMap.injective_iff_surjective.1 hinj)
  have hmap := hstrict.map_nhds_eq_of_surj hsurj
  have := image_mem_map (m := Ψ) hS
  rwa [hmap] at this

/-- **Bendixson-Dulac theorem (Lebl, Theorem 8.4.2, with a Dulac function), for star-shaped closed
trajectories.**  Let `f, g, φ` be continuously differentiable on an open region `D`, and suppose the divergence
`∂(φ f)/∂x + ∂(φ g)/∂y` is `≥ 0` on all of `D` or `≤ 0` on all of `D`, and vanishes only on a set with empty interior.
Then the system `x' = f(x, y)`, `y' = g(x, y)` has no closed trajectory `(x, y)` (period `T > 0`) that is star-shaped
about a point `c`: the segments from `c` to the trajectory lie in `D` and the trajectory is never tangent to a ray
from `c`. -/
@[kb "lebldiffyqs2026" "Theorem 8.4.2, p. 376"]
theorem bendixson_dulac_star_dulac {D : Set (ℝ × ℝ)} (hD : IsOpen D) {f g φ : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f D) (hg : ContDiffOn ℝ 1 g D) (hφ : ContDiffOn ℝ 1 φ D)
    (hsign : (∀ p ∈ D, 0 ≤ planarDiv (fun p => φ p * f p) (fun p => φ p * g p) p) ∨
      (∀ p ∈ D, planarDiv (fun p => φ p * f p) (fun p => φ p * g p) p ≤ 0))
    (hsmall : interior {p ∈ D | planarDiv (fun p => φ p * f p) (fun p => φ p * g p) p = 0} = ∅)
    {x y : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (f (x t, y t)) t) (hy : ∀ t, HasDerivAt y (g (x t, y t)) t)
    {T : ℝ} (hT : 0 < T) (hxT : x T = x 0) (hyT : y T = y 0) (c : ℝ × ℝ)
    (hseg : ∀ t, segment ℝ c (x t, y t) ⊆ D)
    (hstar : ∀ t, (x t - c.1) * g (x t, y t) - (y t - c.2) * f (x t, y t) ≠ 0) : False := by
  set P : ℝ × ℝ → ℝ := fun p => φ p * f p with hPdef
  set Q : ℝ × ℝ → ℝ := fun p => φ p * g p with hQdef
  set vx : ℝ → ℝ := fun t => f (x t, y t)
  set vy : ℝ → ℝ := fun t => g (x t, y t)
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hmem : ∀ t, (x t, y t) ∈ D := fun t => hseg t (right_mem_segment ℝ c (x t, y t))
  have hvx : Continuous vx :=
    hf.continuousOn.comp_continuous (hxc.prodMk hyc) hmem
  have hvy : Continuous vy :=
    hg.continuousOn.comp_continuous (hxc.prodMk hyc) hmem
  have hP : ContDiffOn ℝ 1 P D := hφ.mul hf
  have hQ : ContDiffOn ℝ 1 Q D := hφ.mul hg
  have hseg' : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, starHom c x y s t ∈ D := fun t s hs =>
    hseg t (starHom_mem_segment c x y hs t)
  have htan : ∀ t, P (x t, y t) * vy t - Q (x t, y t) * vx t = 0 := fun t => by
    simp only [hPdef, hQdef, vx, vy]; ring
  have hzero := integral_pbG_eq_zero hD hP hQ hx hy hvx hvy hseg' hT.le hxT hyT htan
  -- signs
  have hkc : Continuous fun t => (x t - c.1) * vy t - (y t - c.2) * vx t := by fun_prop
  obtain ⟨ε, hε0, hε⟩ := pos_or_neg_of_ne_zero hkc hstar
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, δ ≠ 0 ∧ ∀ p ∈ D, 0 ≤ δ * planarDiv P Q p := by
    rcases hsign with h | h
    · exact ⟨1, one_ne_zero, fun p hp => by simpa using h p hp⟩
    · exact ⟨-1, by norm_num, fun p hp => by simpa using h p hp⟩
  -- a point of the cone where the divergence does not vanish
  obtain ⟨s₀, t₀, hs₀, ht₀, hdiv₀⟩ : ∃ s₀ t₀, s₀ ∈ Ioo (0 : ℝ) 1 ∧ t₀ ∈ Ioo 0 T ∧
      planarDiv P Q (starHom c x y s₀ t₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hS : Ioo (0 : ℝ) 1 ×ˢ Ioo 0 T ∈ 𝓝 ((1 / 2 : ℝ), T / 2) :=
      prod_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)) (Ioo_mem_nhds (by linarith) (by linarith))
    have hk2 := hstar (T / 2)
    have himg := starHom_image_mem_nhds c hx hy hvx hvy (by norm_num : (1 / 2 : ℝ) ≠ 0) hk2 hS
    have hsub : (fun q : ℝ × ℝ => starHom c x y q.1 q.2) '' (Ioo (0 : ℝ) 1 ×ˢ Ioo 0 T) ⊆
        {p ∈ D | planarDiv P Q p = 0} := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨hseg' q.2 q.1 (Ioo_subset_Icc_self hq.1), hcon q.1 q.2 hq.1 hq.2⟩
    have hint : starHom c x y (1 / 2) (T / 2) ∈ interior {p ∈ D | planarDiv P Q p = 0} :=
      mem_interior_iff_mem_nhds.2 (mem_of_superset himg hsub)
    rw [hsmall] at hint
    exact hint
  -- the integrand times `δ ε` is nonnegative, and positive at `(s₀, t₀)`
  have hG := continuousOn_pbG hD hP hQ hx hy hvx hvy hseg'
  have hnonneg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ δ * ε * pbG P Q c x y vx vy s t := by
    intro s hs t
    have h1 := hδ _ (hseg' t s hs)
    have h2 := (hε t).le
    have : δ * ε * pbG P Q c x y vx vy s t =
        s * (δ * planarDiv P Q (starHom c x y s t)) * (ε * ((x t - c.1) * vy t - (y t - c.2) * vx t)) := by
      unfold pbG; ring
    rw [this]
    exact mul_nonneg (mul_nonneg hs.1 h1) h2
  have hpos₀ : 0 < δ * ε * pbG P Q c x y vx vy s₀ t₀ := by
    have hs₀' : s₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs₀
    have h1 : 0 < δ * planarDiv P Q (starHom c x y s₀ t₀) :=
      lt_of_le_of_ne (hδ _ (hseg' t₀ s₀ hs₀')) (Ne.symm (mul_ne_zero hδ0 hdiv₀))
    have : δ * ε * pbG P Q c x y vx vy s₀ t₀ = s₀ * (δ * planarDiv P Q (starHom c x y s₀ t₀)) *
        (ε * ((x t₀ - c.1) * vy t₀ - (y t₀ - c.2) * vx t₀)) := by
      unfold pbG; ring
    rw [this]
    exact mul_pos (mul_pos hs₀.1 h1) (hε t₀)
  -- the inner integral is continuous in `s` on `[0, 1]`
  set J : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..T, δ * ε * pbG P Q c x y vx vy s t with hJ
  have hclamp : Continuous fun q : ℝ × ℝ => ((max 0 (min 1 q.1) : ℝ), q.2) := by fun_prop
  have hclampG : Continuous fun q : ℝ × ℝ => δ * ε * pbG P Q c x y vx vy (max 0 (min 1 q.1)) q.2 :=
    continuous_const.mul (hG.comp_continuous (g := fun q : ℝ × ℝ => pbG P Q c x y vx vy q.1 q.2)
      (f := fun q : ℝ × ℝ => ((max 0 (min 1 q.1) : ℝ), q.2)) hclamp fun q =>
      ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, mem_univ _⟩)
  have hJc : ContinuousOn J (Icc 0 1) := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => δ * ε * pbG P Q c x y vx vy (max 0 (min 1 s)) t) hclampG 0 T
    refine this.continuousOn.congr fun s hs => ?_
    simp only [hJ, min_eq_right hs.2, max_eq_right hs.1]
  have hJnn : ∀ s ∈ Ioc (0 : ℝ) 1, 0 ≤ J s := fun s hs =>
    intervalIntegral.integral_nonneg hT.le fun t _ => hnonneg s (Ioc_subset_Icc_self hs) t
  have hGt : Continuous fun t => δ * ε * pbG P Q c x y vx vy s₀ t :=
    continuous_const.mul (hG.comp_continuous (g := fun q : ℝ × ℝ => pbG P Q c x y vx vy q.1 q.2)
      (f := fun t : ℝ => ((s₀, t) : ℝ × ℝ)) (by fun_prop)
      fun t => ⟨Ioo_subset_Icc_self hs₀, mem_univ t⟩)
  have hJ₀ : 0 < J s₀ :=
    intervalIntegral.integral_pos hT hGt.continuousOn
      (fun t _ => hnonneg s₀ (Ioo_subset_Icc_self hs₀) t) ⟨t₀, Ioo_subset_Icc_self ht₀, hpos₀⟩
  have hpos : 0 < ∫ s in (0 : ℝ)..1, J s :=
    intervalIntegral.integral_pos zero_lt_one hJc hJnn ⟨s₀, Ioo_subset_Icc_self hs₀, hJ₀⟩
  have hJ0 : ∫ s in (0 : ℝ)..1, J s = 0 := by
    rw [hJ]
    simp only [intervalIntegral.integral_const_mul]
    rw [hzero, mul_zero]
  linarith

/-- **Bendixson-Dulac theorem (Lebl, Theorem 8.4.2, the book's case `φ = 1`), for star-shaped closed
trajectories.**  If `f, g` are continuously differentiable on an open region `D` and `∂f/∂x + ∂g/∂y` is always
`≥ 0` or always `≤ 0` on `D`, vanishing only on a set with empty interior (isolated points or curves), then the system
`x' = f(x, y)`, `y' = g(x, y)` has no closed trajectory in `D` that is star-shaped about a point `c` (segments from
`c` to the trajectory in `D`, trajectory never tangent to a ray from `c`). -/
@[kb "lebldiffyqs2026" "Theorem 8.4.2, p. 376"]
theorem bendixson_dulac_star {D : Set (ℝ × ℝ)} (hD : IsOpen D) {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f D) (hg : ContDiffOn ℝ 1 g D)
    (hsign : (∀ p ∈ D, 0 ≤ planarDiv f g p) ∨ (∀ p ∈ D, planarDiv f g p ≤ 0))
    (hsmall : interior {p ∈ D | planarDiv f g p = 0} = ∅)
    {x y : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (f (x t, y t)) t) (hy : ∀ t, HasDerivAt y (g (x t, y t)) t)
    {T : ℝ} (hT : 0 < T) (hxT : x T = x 0) (hyT : y T = y 0) (c : ℝ × ℝ)
    (hseg : ∀ t, segment ℝ c (x t, y t) ⊆ D)
    (hstar : ∀ t, (x t - c.1) * g (x t, y t) - (y t - c.2) * f (x t, y t) ≠ 0) : False := by
  have hf1 : (fun p => (fun _ => (1 : ℝ)) p * f p) = f := funext fun p => one_mul _
  have hg1 : (fun p => (fun _ => (1 : ℝ)) p * g p) = g := funext fun p => one_mul _
  refine bendixson_dulac_star_dulac hD hf hg (φ := fun _ => 1) contDiffOn_const ?_ ?_ hx hy hT hxT hyT c
    hseg hstar
  · rwa [hf1, hg1]
  · rwa [hf1, hg1]

/-- On a convex open region (for instance the whole plane) the segment hypothesis holds for every point `c` of the
region: no closed trajectory of a field whose divergence has one sign (off a set with empty interior) winds around a
point `c ∈ D` with monotone angle. -/
@[kb "lebldiffyqs2026" "Theorem 8.4.2, p. 376"]
theorem bendixson_dulac_convex {D : Set (ℝ × ℝ)} (hD : IsOpen D) (hDc : Convex ℝ D) {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f D) (hg : ContDiffOn ℝ 1 g D)
    (hsign : (∀ p ∈ D, 0 ≤ planarDiv f g p) ∨ (∀ p ∈ D, planarDiv f g p ≤ 0))
    (hsmall : interior {p ∈ D | planarDiv f g p = 0} = ∅)
    {x y : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (f (x t, y t)) t) (hy : ∀ t, HasDerivAt y (g (x t, y t)) t)
    (hD' : ∀ t, (x t, y t) ∈ D)
    {T : ℝ} (hT : 0 < T) (hxT : x T = x 0) (hyT : y T = y 0) {c : ℝ × ℝ} (hc : c ∈ D)
    (hstar : ∀ t, (x t - c.1) * g (x t, y t) - (y t - c.2) * f (x t, y t) ≠ 0) : False :=
  bendixson_dulac_star hD hf hg hsign hsmall hx hy hT hxT hyT c
    (fun t => hDc.segment_subset hc (hD' t)) hstar

/-- The divergence from the two partial derivatives `∂P/∂x` and `∂Q/∂y` computed along coordinate lines. -/
lemma planarDiv_eq_of_hasDerivAt {P Q : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hP : DifferentiableAt ℝ P p)
    (hQ : DifferentiableAt ℝ Q p) {a b : ℝ} (ha : HasDerivAt (fun u => P (u, p.2)) a p.1)
    (hb : HasDerivAt (fun v => Q (p.1, v)) b p.2) : planarDiv P Q p = a + b := by
  have h1 := hP.hasFDerivAt.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have h2 := hQ.hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  unfold planarDiv
  rw [h1.unique ha, h2.unique hb]

/-- The field of Lebl's Example 8.4.5. -/
def ex845f (p : ℝ × ℝ) : ℝ := p.2 + (p.1 ^ 2 + p.2 ^ 2 - 1) * p.1
/-- The field of Lebl's Example 8.4.5. -/
def ex845g (p : ℝ × ℝ) : ℝ := -p.1 + (p.1 ^ 2 + p.2 ^ 2 - 1) * p.2

/-- **Lebl, Example 8.4.5: the region hypothesis cannot be dropped.**  For `x' = y + (x² + y² - 1) x`,
`y' = -x + (x² + y² - 1) y` on the region `R = {x² + y² > 1/2}` the divergence is `4x² + 4y² - 2 > 0`, yet the unit
circle `x = cos t`, `y = -sin t` is a closed trajectory (period `2π`) in `R`, star-shaped about the origin; the
segments from the origin to it leave `R` (the region has a hole).  (The book writes `y = sin t`, which traverses the
circle backwards: `cos t, sin t` solves the system with time reversed.) -/
@[kb "lebldiffyqs2026" "Example 8.4.5, p. 377"]
theorem example_845 :
    (∀ p : ℝ × ℝ, planarDiv ex845f ex845g p = 4 * p.1 ^ 2 + 4 * p.2 ^ 2 - 2) ∧
    (∀ p : ℝ × ℝ, 1 / 2 < p.1 ^ 2 + p.2 ^ 2 → 0 < planarDiv ex845f ex845g p) ∧
    (∀ t, HasDerivAt Real.cos (ex845f (Real.cos t, -Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -Real.sin t) (ex845g (Real.cos t, -Real.sin t)) t) ∧
    (∀ t, 1 / 2 < Real.cos t ^ 2 + (-Real.sin t) ^ 2) ∧
    Real.cos (2 * Real.pi) = Real.cos 0 ∧ -Real.sin (2 * Real.pi) = -Real.sin 0 ∧
    (∀ t, (Real.cos t - 0) * ex845g (Real.cos t, -Real.sin t)
      - (-Real.sin t - 0) * ex845f (Real.cos t, -Real.sin t) ≠ 0) ∧
    ¬ (1 / 2 < (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) := by
  have hdiv : ∀ p : ℝ × ℝ, planarDiv ex845f ex845g p = 4 * p.1 ^ 2 + 4 * p.2 ^ 2 - 2 := by
    intro p
    have hf : DifferentiableAt ℝ ex845f p := by unfold ex845f; fun_prop
    have hg : DifferentiableAt ℝ ex845g p := by unfold ex845g; fun_prop
    have ha : HasDerivAt (fun u => ex845f (u, p.2)) (3 * p.1 ^ 2 + p.2 ^ 2 - 1) p.1 := by
      have := (((hasDerivAt_pow 2 p.1).add_const (p.2 ^ 2 - 1)).mul (hasDerivAt_id' p.1)).const_add p.2
      simp only [ex845f]
      convert this using 1
      · funext u; simp only [Pi.mul_apply]; ring
      · push_cast; ring
    have hb : HasDerivAt (fun v => ex845g (p.1, v)) (p.1 ^ 2 + 3 * p.2 ^ 2 - 1) p.2 := by
      have := (((hasDerivAt_pow 2 p.2).const_add (p.1 ^ 2 - 1)).mul (hasDerivAt_id' p.2)).const_add (-p.1)
      simp only [ex845g]
      convert this using 1
      · funext v; simp only [Pi.mul_apply]; ring
      · push_cast; ring
    rw [planarDiv_eq_of_hasDerivAt hf hg ha hb]; ring
  refine ⟨hdiv, fun p hp => by rw [hdiv]; linarith, fun t => ?_, fun t => ?_, fun t => ?_, by simp, by simp,
    fun t => ?_, by norm_num⟩
  · have := Real.hasDerivAt_cos t
    simp only [ex845f, neg_sq, Real.cos_sq_add_sin_sq, sub_self, zero_mul, add_zero]
    exact this
  · have := (Real.hasDerivAt_sin t).neg
    simp only [ex845g, neg_sq, Real.cos_sq_add_sin_sq, sub_self, zero_mul, add_zero]
    exact this
  · rw [neg_sq, Real.cos_sq_add_sin_sq]; norm_num
  · simp only [ex845f, ex845g, neg_sq, Real.cos_sq_add_sin_sq, sub_self, zero_mul, add_zero, sub_zero]
    have := Real.cos_sq_add_sin_sq t
    nlinarith

/-- **Lebl, Exercise 8.4.2 (via Theorem 8.4.2).**  If `a + d ≠ 0`, the linear system `x' = a x + b y`,
`y' = c x + d y` has no closed trajectory star-shaped about any point (for instance no ellipse around the origin):
the divergence is the constant `a + d`. -/
@[kb "lebldiffyqs2026" "Theorem 8.4.2, p. 376"]
theorem linear_no_star_closed_trajectory {a b c d : ℝ} (htr : a + d ≠ 0) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (a * x t + b * y t) t) (hy : ∀ t, HasDerivAt y (c * x t + d * y t) t)
    {T : ℝ} (hT : 0 < T) (hxT : x T = x 0) (hyT : y T = y 0) (q : ℝ × ℝ)
    (hstar : ∀ t, (x t - q.1) * (c * x t + d * y t) - (y t - q.2) * (a * x t + b * y t) ≠ 0) : False := by
  set f : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
  set g : ℝ × ℝ → ℝ := fun p => c * p.1 + d * p.2
  have hdiv : ∀ p, planarDiv f g p = a + d := by
    intro p
    have ha : HasDerivAt (fun u => f (u, p.2)) a p.1 := by
      exact (((hasDerivAt_id p.1).const_mul a).add_const (b * p.2)).congr_deriv (by simp)
    have hb : HasDerivAt (fun v => g (p.1, v)) d p.2 := by
      exact (((hasDerivAt_id p.2).const_mul d).const_add (c * p.1)).congr_deriv (by simp)
    exact planarDiv_eq_of_hasDerivAt (by fun_prop) (by fun_prop) ha hb
  have hsign : (∀ p ∈ (univ : Set (ℝ × ℝ)), 0 ≤ planarDiv f g p) ∨
      (∀ p ∈ (univ : Set (ℝ × ℝ)), planarDiv f g p ≤ 0) := by
    rcases le_total 0 (a + d) with h | h
    · exact Or.inl fun p _ => (hdiv p).symm ▸ h
    · exact Or.inr fun p _ => (hdiv p).symm ▸ h
  have hsmall : interior {p ∈ (univ : Set (ℝ × ℝ)) | planarDiv f g p = 0} = ∅ := by
    have : {p ∈ (univ : Set (ℝ × ℝ)) | planarDiv f g p = 0} = ∅ := by
      ext p; simp [hdiv p, htr]
    rw [this, interior_empty]
  exact bendixson_dulac_convex isOpen_univ convex_univ (by fun_prop) (by fun_prop) hsign hsmall
    (f := f) (g := g) hx hy (fun _ => mem_univ _) hT hxT hyT (mem_univ q) hstar

end UndergradKB.DifferentialEquations
