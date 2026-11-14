import UndergradKB.DifferentialEquations.SturmLiouvilleFredholm

/-! # Green's function of a regular Sturm-Liouville problem (Lebl §5.1)

Fix `λ` (called `l`).  Let `u` solve the (clamped, on all of `ℝ`) homogeneous equation with initial data at `a`
satisfying the left boundary condition, `(u(a), u'(a)) = (α₂, α₁)`, and let `v` solve it with data at `b`
satisfying the right one, `(v(b), v'(b)) = (β₂, -β₁)`.  On `[a, b]` the Wronskian-like quantity
`p (u v' - u' v)` is constant; call its value `W`.  If `λ` is not an eigenvalue, then `W ≠ 0` (otherwise `v`
would be an eigenfunction).  The Green's function is
`G(x, t) = u(min x t) v(max x t) / W`, with the arguments clamped to `[a, b]` so that `G` is continuous on
`ℝ²`.  For `f` continuous on `[a, b]` the function
`Y(x) = (v(x) ∫_a^x u f̃ + u(x) ∫_x^b v f̃) / W` (`f̃ = f ∘ clampI`) is `C²`, solves
`(p Y')' - q Y + λ r Y = f` on `[a, b]` with both boundary conditions, and equals `∫_a^b G(x, t) f(t) dt`
on `[a, b]`.  This is the Green's-function form of the existence half of the Fredholm alternative. -/

namespace UndergradKB.DifferentialEquations

open Set intervalIntegral

namespace RegularSL

variable (S : RegularSL)

/-! ### Auxiliary calculus -/

lemma cd2 {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y) : Differentiable ℝ y ∧ ContDiff ℝ 1 (deriv y) := by
  have e : ((2 : WithTop ℕ∞)) = 1 + 1 := by norm_num
  rw [e] at hy
  have h := contDiff_succ_iff_deriv.1 hy
  exact ⟨h.1, h.2.2⟩

lemma hasDerivAt_pd {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y) (x : ℝ) :
    HasDerivAt (fun t => S.p t * deriv y t)
      (deriv S.p x * deriv y x + S.p x * deriv (deriv y) x) x :=
  ((S.p_C1.differentiable one_ne_zero) x).hasDerivAt.mul
    (((cd2 hy).2.differentiable one_ne_zero) x).hasDerivAt

/-- The "Wronskian" `p (u v' - u' v)` of two solutions is constant on `[a, b]`. -/
lemma wron_const_aux {l : ℝ} {u v : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huE : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv u t) t - S.q t * u t + l * S.r t * u t = 0)
    (hvE : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv v t) t - S.q t * v t + l * S.r t * v t = 0) :
    ∀ x ∈ Icc S.a S.b, S.p x * (u x * deriv v x - deriv u x * v x)
      = S.p S.a * (u S.a * deriv v S.a - deriv u S.a * v S.a) := by
  have hder : ∀ x, HasDerivAt (fun x => S.p x * (u x * deriv v x - deriv u x * v x))
      (deriv S.p x * (u x * deriv v x - deriv u x * v x) + S.p x *
        ((deriv u x * deriv v x + u x * deriv (deriv v) x)
          - (deriv (deriv u) x * v x + deriv u x * deriv v x))) x := by
    intro x
    have hp := ((S.p_C1.differentiable one_ne_zero) x).hasDerivAt
    have hu0 := ((cd2 hu).1 x).hasDerivAt
    have hv0 := ((cd2 hv).1 x).hasDerivAt
    have hu1 := (((cd2 hu).2.differentiable one_ne_zero) x).hasDerivAt
    have hv1 := (((cd2 hv).2.differentiable one_ne_zero) x).hasDerivAt
    exact hp.mul ((hu0.mul hv1).sub (hu1.mul hv0))
  have h0 : ∀ x ∈ Icc S.a S.b,
      HasDerivAt (fun x => S.p x * (u x * deriv v x - deriv u x * v x)) 0 x := by
    intro x hx
    have eu := huE x hx
    have ev := hvE x hx
    rw [(S.hasDerivAt_pd hu x).deriv] at eu
    rw [(S.hasDerivAt_pd hv x).deriv] at ev
    exact (hder x).congr_deriv (by linear_combination u x * ev - v x * eu)
  have hc : ContinuousOn (fun x => S.p x * (u x * deriv v x - deriv u x * v x)) (Icc S.a S.b) :=
    fun x _ => (hder x).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hc
    (fun x hx => (h0 x (Ico_subset_Icc_self hx)).hasDerivWithinAt)

/-! ### The functions `u` and `v` -/

lemma exists_uv (l : ℝ) : ∃ w : (ℝ → ℝ) × (ℝ → ℝ), ContDiff ℝ 2 w.1 ∧ ContDiff ℝ 2 w.2 ∧
    (∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv w.1 t) t - S.q t * w.1 t + l * S.r t * w.1 t = 0) ∧
    (∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv w.2 t) t - S.q t * w.2 t + l * S.r t * w.2 t = 0) ∧
    w.1 S.a = S.α₂ ∧ deriv w.1 S.a = S.α₁ ∧ w.2 S.b = S.β₂ ∧ deriv w.2 S.b = -S.β₁ := by
  have hcA := (continuousOn_univ.2 S.continuous_cA)
  have hcB := (continuousOn_univ.2 (S.continuous_cB l))
  have hc0 : ContinuousOn (0 : ℝ → ℝ) univ := continuousOn_const
  obtain ⟨u, hu, hu0, hu1⟩ := lin2_exists isOpen_univ ordConnected_univ hcA hcB hc0
    (t₀ := S.a) trivial S.α₂ S.α₁
  obtain ⟨v, hv, hv0, hv1⟩ := lin2_exists isOpen_univ ordConnected_univ hcA hcB hc0
    (t₀ := S.b) trivial S.β₂ (-S.β₁)
  have hF0 : ∀ t ∈ Icc S.a S.b, (0 : ℝ → ℝ) t = (0 : ℝ → ℝ) t / S.p t := fun t _ => by simp
  obtain ⟨uC, uE⟩ := S.solves_of_lin2 (f := 0) continuous_const hF0 hu
  obtain ⟨vC, vE⟩ := S.solves_of_lin2 (f := 0) continuous_const hF0 hv
  exact ⟨(u, v), uC, vC, uE, vE, hu0, hu1, hv0, hv1⟩

/-- The pair `(u, v)`. -/
noncomputable def uv (l : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) := Classical.choose (S.exists_uv l)

/-- Solution with data `(α₂, α₁)` at `a` (satisfies the left boundary condition). -/
noncomputable def uu (l : ℝ) : ℝ → ℝ := (S.uv l).1

/-- Solution with data `(β₂, -β₁)` at `b` (satisfies the right boundary condition). -/
noncomputable def vv (l : ℝ) : ℝ → ℝ := (S.uv l).2

lemma uv_spec (l : ℝ) : ContDiff ℝ 2 (S.uu l) ∧ ContDiff ℝ 2 (S.vv l) ∧
    (∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv (S.uu l) t) t - S.q t * S.uu l t + l * S.r t * S.uu l t = 0) ∧
    (∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv (S.vv l) t) t - S.q t * S.vv l t + l * S.r t * S.vv l t = 0) ∧
    S.uu l S.a = S.α₂ ∧ deriv (S.uu l) S.a = S.α₁ ∧ S.vv l S.b = S.β₂ ∧
      deriv (S.vv l) S.b = -S.β₁ :=
  Classical.choose_spec (S.exists_uv l)

/-- The constant value of `p (u v' - u' v)` on `[a, b]`. -/
noncomputable def wr (l : ℝ) : ℝ :=
  S.p S.a * (S.uu l S.a * deriv (S.vv l) S.a - deriv (S.uu l) S.a * S.vv l S.a)

lemma wr_const (l : ℝ) : ∀ x ∈ Icc S.a S.b,
    S.p x * (S.uu l x * deriv (S.vv l) x - deriv (S.uu l) x * S.vv l x) = S.wr l := by
  obtain ⟨uC, vC, uE, vE, -⟩ := S.uv_spec l
  exact S.wron_const_aux uC vC uE vE

/-- If `λ` is not an eigenvalue, the constant `W` is nonzero. -/
lemma wr_ne {l : ℝ} (hl : ¬ S.IsEigenvalue l) : S.wr l ≠ 0 := by
  intro hW
  obtain ⟨uC, vC, uE, vE, u0, u1, v0, v1⟩ := S.uv_spec l
  have hpa := S.p_pos S.a (left_mem_Icc.2 S.hab.le)
  unfold wr at hW
  have h1 : S.uu l S.a * deriv (S.vv l) S.a - deriv (S.uu l) S.a * S.vv l S.a = 0 := by
    rcases mul_eq_zero.1 hW with h | h
    · exact absurd h hpa.ne'
    · exact h
  rw [u0, u1] at h1
  apply hl
  refine ⟨S.vv l, ⟨vC, vE, ?_, ?_⟩, ?_⟩
  · linarith
  · rw [v0, v1]; ring
  · by_contra hall
    push Not at hall
    have hz : ∀ t ∈ Icc S.a S.b, S.vv l t = (fun _ => (0 : ℝ)) t := hall
    have dv : DifferentiableAt ℝ (S.vv l) S.b := ((cd2 vC).1) S.b
    have hder : HasDerivWithinAt (S.vv l) (deriv (S.vv l) S.b) (Icc S.a S.b) S.b :=
      dv.hasDerivAt.hasDerivWithinAt
    have hder0 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) (Icc S.a S.b) S.b :=
      hasDerivWithinAt_const _ _ _
    have hb := right_mem_Icc.2 S.hab.le
    have := (uniqueDiffOn_Icc S.hab S.b hb).eq_deriv _ hder (hder0.congr hz (hz S.b hb))
    rw [v1] at this
    have h0 : S.β₂ = 0 := by have := hz S.b hb; simpa [v0] using this
    exact S.β_ne ⟨by linarith, h0⟩

/-! ### The Green's function -/

/-- **Green's function** of the regular Sturm-Liouville problem at `λ = l`:
`G(x, t) = u(min x t) v(max x t) / W`, with the arguments clamped to `[a, b]` (so `G` is continuous on `ℝ²`).
It is meaningful when `l` is not an eigenvalue (then `W ≠ 0`). -/
noncomputable def green (l : ℝ) (x t : ℝ) : ℝ :=
  S.uu l (min (S.clampI x) (S.clampI t)) * S.vv l (max (S.clampI x) (S.clampI t)) / S.wr l

/-- The Green's function is continuous on `ℝ²`. -/
theorem continuous_green (l : ℝ) : Continuous (fun z : ℝ × ℝ => S.green l z.1 z.2) := by
  have hu : Continuous (S.uu l) := (S.uv_spec l).1.continuous
  have hv : Continuous (S.vv l) := (S.uv_spec l).2.1.continuous
  have hc := S.continuous_clampI
  unfold green
  fun_prop

/-- The Green's function is symmetric. -/
theorem green_symm (l x t : ℝ) : S.green l x t = S.green l t x := by
  unfold green
  rw [min_comm, max_comm]

/-! ### The variation-of-constants formula -/

end RegularSL

/-- `∫_a^x u g`. -/
noncomputable def intA (a : ℝ) (u g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in a..x, u t * g t

/-- `∫_x^b v g`. -/
noncomputable def intB (b : ℝ) (v g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in x..b, v t * g t

/-- `(v ∫_a^x u g + u ∫_x^b v g) / W`. -/
noncomputable def yfun (a b : ℝ) (u v g : ℝ → ℝ) (W x : ℝ) : ℝ :=
  (v x * intA a u g x + u x * intB b v g x) / W

/-- The derivative of `yfun`. -/
noncomputable def yfun1 (a b : ℝ) (u v g : ℝ → ℝ) (W x : ℝ) : ℝ :=
  (deriv v x * intA a u g x + deriv u x * intB b v g x) / W

/-- The derivative of `yfun1`. -/
noncomputable def yfun2 (a b : ℝ) (u v g : ℝ → ℝ) (W x : ℝ) : ℝ :=
  (deriv (deriv v) x * intA a u g x + deriv v x * (u x * g x)
    + (deriv (deriv u) x * intB b v g x + deriv u x * -(v x * g x))) / W

lemma hasDerivAt_intA {a : ℝ} {u g : ℝ → ℝ} (hu : Continuous u) (hg : Continuous g) (x : ℝ) :
    HasDerivAt (intA a u g) (u x * g x) x :=
  ((hu.mul hg).integral_hasStrictDerivAt a x).hasDerivAt

lemma hasDerivAt_intB {b : ℝ} {v g : ℝ → ℝ} (hv : Continuous v) (hg : Continuous g) (x : ℝ) :
    HasDerivAt (intB b v g) (-(v x * g x)) x := by
  have h := ((hv.mul hg).integral_hasStrictDerivAt b x).hasDerivAt.neg
  have e : intB b v g = fun y => -∫ t in b..y, v t * g t := by
    funext y
    simp only [intB]
    rw [intervalIntegral.integral_symm b y]
  rw [e]
  exact h

lemma hasDerivAt_yfun {a b : ℝ} {u v g : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hg : Continuous g) (W x : ℝ) :
    HasDerivAt (yfun a b u v g W) (yfun1 a b u v g W x) x := by
  have hu' := ((RegularSL.cd2 hu).1 x).hasDerivAt
  have hv' := ((RegularSL.cd2 hv).1 x).hasDerivAt
  have h := ((hv'.mul (hasDerivAt_intA (a := a) hu.continuous hg x)).add
    (hu'.mul (hasDerivAt_intB (b := b) hv.continuous hg x))).div_const W
  exact h.congr_deriv (by unfold yfun1; ring)

lemma hasDerivAt_yfun1 {a b : ℝ} {u v g : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hg : Continuous g) (W x : ℝ) :
    HasDerivAt (yfun1 a b u v g W) (yfun2 a b u v g W x) x := by
  have hu' := (((RegularSL.cd2 hu).2.differentiable one_ne_zero) x).hasDerivAt
  have hv' := (((RegularSL.cd2 hv).2.differentiable one_ne_zero) x).hasDerivAt
  have h := ((hv'.mul (hasDerivAt_intA (a := a) hu.continuous hg x)).add
    (hu'.mul (hasDerivAt_intB (b := b) hv.continuous hg x))).div_const W
  exact h

lemma yfun_spec {a b : ℝ} {u v g : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hg : Continuous g) (W : ℝ) :
    ContDiff ℝ 2 (yfun a b u v g W) ∧ deriv (yfun a b u v g W) = yfun1 a b u v g W ∧
      deriv (yfun1 a b u v g W) = yfun2 a b u v g W := by
  have hd : Differentiable ℝ (yfun a b u v g W) :=
    fun x => (hasDerivAt_yfun hu hv hg W x).differentiableAt
  have hD1 : deriv (yfun a b u v g W) = yfun1 a b u v g W :=
    funext fun x => (hasDerivAt_yfun hu hv hg W x).deriv
  have hD2 : deriv (yfun1 a b u v g W) = yfun2 a b u v g W :=
    funext fun x => (hasDerivAt_yfun1 hu hv hg W x).deriv
  have hA : Continuous (intA a u g) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_intA (a := a) hu.continuous hg x).continuousAt
  have hB : Continuous (intB b v g) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_intB (b := b) hv.continuous hg x).continuousAt
  have hu0 := hu.continuous
  have hv0 := hv.continuous
  have hu1 : Continuous (deriv u) := (RegularSL.cd2 hu).2.continuous
  have hv1 : Continuous (deriv v) := (RegularSL.cd2 hv).2.continuous
  have hu2 : Continuous (deriv (deriv u)) := ((RegularSL.cd2 hu).2.continuous_deriv le_rfl)
  have hv2 : Continuous (deriv (deriv v)) := ((RegularSL.cd2 hv).2.continuous_deriv le_rfl)
  have hc : Continuous (yfun2 a b u v g W) := by
    unfold yfun2
    fun_prop
  have h1 : ContDiff ℝ 1 (yfun1 a b u v g W) :=
    contDiff_one_iff_deriv.2 ⟨fun x => (hasDerivAt_yfun1 hu hv hg W x).differentiableAt,
      by rw [hD2]; exact hc⟩
  have h1' : ContDiff ℝ 1 (deriv (yfun a b u v g W)) := by rw [hD1]; exact h1
  refine ⟨?_, hD1, hD2⟩
  have e : ((2 : WithTop ℕ∞)) = 1 + 1 := by norm_num
  rw [e]
  exact contDiff_succ_iff_deriv.2 ⟨hd, by simp, h1'⟩

namespace RegularSL

variable (S : RegularSL)

lemma yfun_eq {l : ℝ} {u v g : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hg : Continuous g)
    (huE : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv u t) t - S.q t * u t + l * S.r t * u t = 0)
    (hvE : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv v t) t - S.q t * v t + l * S.r t * v t = 0)
    {W : ℝ} (hW : W ≠ 0)
    (hwr : ∀ x ∈ Icc S.a S.b, S.p x * (u x * deriv v x - deriv u x * v x) = W) :
    ∀ x ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv (yfun S.a S.b u v g W) t) x
        - S.q x * yfun S.a S.b u v g W x + l * S.r x * yfun S.a S.b u v g W x = g x := by
  intro x hx
  obtain ⟨-, hD1, hD2⟩ := yfun_spec (a := S.a) (b := S.b) hu hv hg W
  have eu := huE x hx
  have ev := hvE x hx
  rw [(S.hasDerivAt_pd hu x).deriv] at eu
  rw [(S.hasDerivAt_pd hv x).deriv] at ev
  have hw := hwr x hx
  rw [hD1]
  have hp := ((S.p_C1.differentiable one_ne_zero) x).hasDerivAt
  have h2 : HasDerivAt (fun t => S.p t * yfun1 S.a S.b u v g W t)
      (deriv S.p x * yfun1 S.a S.b u v g W x + S.p x * yfun2 S.a S.b u v g W x) x :=
    hp.mul (hasDerivAt_yfun1 (a := S.a) (b := S.b) hu hv hg W x)
  rw [h2.deriv]
  simp only [yfun, yfun1, yfun2]
  have hW' : W * W⁻¹ = 1 := mul_inv_cancel₀ hW
  generalize intA S.a u g x = A at *
  generalize intB S.b v g x = B at *
  linear_combination (A / W) * ev + (B / W) * eu + (g x / W) * hw + g x * hW'

/-- **Green's function representation (existence in the Fredholm alternative, with a formula).**
If `λ` is not an eigenvalue and `f` is continuous on `[a, b]`, there is a solution `y` of
`(p y')' - q y + λ r y = f` with both boundary conditions (a `C²` function on `ℝ`), and on `[a, b]` it is
given by `y(x) = ∫_a^b G(x, t) f(t) dt`, where `G` is the Green's function `S.green l`. -/
@[kb "lebldiffyqs2026" "§5.1 Sturm-Liouville problems (Green's function for Theorem 5.1.1), p. 275"]
theorem green_solution {l : ℝ} (hl : ¬ S.IsEigenvalue l) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc S.a S.b)) :
    ∃ y, S.IsSolution l f y ∧ ∀ x ∈ Icc S.a S.b, y x = ∫ t in S.a..S.b, S.green l x t * f t := by
  obtain ⟨uC, vC, uE, vE, u0, u1, v0, v1⟩ := S.uv_spec l
  have hW := S.wr_ne hl
  set g : ℝ → ℝ := fun t => f (S.clampI t) with hgdef
  have hgc : Continuous g := hf.comp_continuous S.continuous_clampI S.clampI_mem
  have hgf : ∀ t ∈ Icc S.a S.b, g t = f t := fun t ht => by
    simp only [hgdef, S.clampI_of_mem ht]
  obtain ⟨hYC, hD1, -⟩ := yfun_spec (a := S.a) (b := S.b) uC vC hgc (S.wr l)
  refine ⟨yfun S.a S.b (S.uu l) (S.vv l) g (S.wr l), ⟨hYC, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    rw [← hgf t ht]
    exact S.yfun_eq uC vC hgc uE vE hW (S.wr_const l) t ht
  · rw [hD1]
    simp only [yfun, yfun1, intA, intB, intervalIntegral.integral_same, mul_zero, zero_add, u0, u1]
    ring
  · rw [hD1]
    simp only [yfun, yfun1, intA, intB, intervalIntegral.integral_same, mul_zero, add_zero, v0, v1]
    ring
  · intro x hx
    have hax : S.a ≤ x := hx.1
    have hxb : x ≤ S.b := hx.2
    have hcongr : ∫ t in S.a..S.b, S.green l x t * f t = ∫ t in S.a..S.b, S.green l x t * g t := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Icc S.a S.b := by rwa [uIcc_of_le S.hab.le] at ht
      show S.green l x t * f t = S.green l x t * f (S.clampI t)
      rw [S.clampI_of_mem ht']
    have hc : Continuous fun t => S.green l x t * g t :=
      ((S.continuous_green l).comp (continuous_const.prodMk continuous_id)).mul hgc
    have I1 : ∫ t in S.a..x, S.green l x t * g t = S.vv l x / S.wr l * intA S.a (S.uu l) g x := by
      rw [intA, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Icc S.a x := by rwa [uIcc_of_le hax] at ht
      have ht'' : t ∈ Icc S.a S.b := ⟨ht'.1, ht'.2.trans hxb⟩
      show S.green l x t * g t = _
      unfold green
      rw [S.clampI_of_mem hx, S.clampI_of_mem ht'', min_eq_right ht'.2, max_eq_left ht'.2]
      ring
    have I2 : ∫ t in x..S.b, S.green l x t * g t = S.uu l x / S.wr l * intB S.b (S.vv l) g x := by
      rw [intB, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Icc x S.b := by rwa [uIcc_of_le hxb] at ht
      have ht'' : t ∈ Icc S.a S.b := ⟨hax.trans ht'.1, ht'.2⟩
      show S.green l x t * g t = _
      unfold green
      rw [S.clampI_of_mem hx, S.clampI_of_mem ht'', min_eq_left ht'.1, max_eq_right ht'.1]
      ring
    rw [hcongr, ← integral_add_adjacent_intervals (b := x) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), I1, I2]
    simp only [yfun]
    ring

end RegularSL

end UndergradKB.DifferentialEquations
