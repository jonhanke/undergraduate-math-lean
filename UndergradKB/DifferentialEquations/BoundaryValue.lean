import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.PDE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Boundary value problems: the Fredholm alternative, Neumann and periodic eigenvalues, beams,
series solutions of forced problems (Lebl §4.1, §4.4, §4.5, §5.2)

A "solution" of a boundary value problem on `[a, b]` is a `C²` function `x : ℝ → ℝ` whose differential
equation holds on `[a, b]` (only its restriction to the interval matters).

The main tool is the pair `S, C` of fundamental solutions of `x'' + λ x = 0` at `0`
(`S(0) = 0, S'(0) = 1`, `C(0) = 1, C' = -λ S`), packaged as `BVPFund`; it is realised by sine/cosine,
`τ`/`1`, or hyperbolic sine/cosine according to the sign of `λ`.  Every solution of the homogeneous
equation on `[a, b]` is `z(a) C(t-a) + z'(a) S(t-a)` and a particular solution of `x'' + λ x = f` is
`∫ₐᵗ S(t-s) f(s) ds`, obtained by variation of parameters. -/

namespace UndergradKB.DifferentialEquations

open Real Set intervalIntegral Filter Topology

/-! ## Fundamental solutions -/

/-- `S, C` are the fundamental solutions of `x'' + λ x = 0` at the origin: `S' = C`, `C' = -λ S`,
`S(0) = 0`, `C(0) = 1`. -/
structure BVPFund (lam : ℝ) (S C : ℝ → ℝ) : Prop where
  hS : ∀ τ, HasDerivAt S (C τ) τ
  hC : ∀ τ, HasDerivAt C (-lam * S τ) τ
  S0 : S 0 = 0
  C0 : C 0 = 1

lemma BVPFund.id_sq {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) (τ : ℝ) :
    C τ ^ 2 + lam * S τ ^ 2 = 1 := by
  have hg : ∀ τ, HasDerivAt (fun τ => C τ * C τ + lam * (S τ * S τ)) 0 τ := fun τ => by
    have := ((h.hC τ).mul (h.hC τ)).add (((h.hS τ).mul (h.hS τ)).const_mul lam)
    exact this.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (f := fun τ => C τ * C τ + lam * (S τ * S τ))
    (fun τ => (hg τ).differentiableAt) (fun τ => (hg τ).deriv) τ 0
  simp only [h.S0, h.C0] at hc
  nlinarith [hc]

lemma bvp_fund_pos {ω : ℝ} (hω : ω ≠ 0) :
    BVPFund (ω ^ 2) (fun τ => sin (ω * τ) / ω) (fun τ => cos (ω * τ)) where
  hS τ := ((hasDerivAt_sin_mul ω τ).div_const ω).congr_deriv (by field_simp)
  hC τ := (hasDerivAt_cos_mul ω τ).congr_deriv (by field_simp)
  S0 := by simp
  C0 := by simp

lemma bvp_fund_neg {ν : ℝ} (hν : ν ≠ 0) :
    BVPFund (-(ν ^ 2)) (fun τ => Real.sinh (ν * τ) / ν) (fun τ => Real.cosh (ν * τ)) where
  hS τ := ((hasDerivAt_sinh_mul ν τ).div_const ν).congr_deriv (by field_simp)
  hC τ := (hasDerivAt_cosh_mul ν τ).congr_deriv (by field_simp)
  S0 := by simp
  C0 := by simp

lemma bvp_fund_zero : BVPFund 0 (fun τ => τ) (fun _ => 1) where
  hS τ := hasDerivAt_id τ
  hC τ := by simpa using hasDerivAt_const τ (1 : ℝ)
  S0 := rfl
  C0 := rfl

lemma bvp_fund_exists (lam : ℝ) : ∃ S C, BVPFund lam S C := by
  rcases lt_trichotomy lam 0 with h | h | h
  · have hν : Real.sqrt (-lam) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have := bvp_fund_neg hν
    rw [Real.sq_sqrt (by linarith), neg_neg] at this
    exact ⟨_, _, this⟩
  · subst h; exact ⟨_, _, bvp_fund_zero⟩
  · have hω : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 h).ne'
    have := bvp_fund_pos hω
    rw [Real.sq_sqrt h.le] at this
    exact ⟨_, _, this⟩

/-- A `C²` function from a first derivative that is itself differentiable with continuous derivative. -/
lemma bvp_contDiff_two {x d1 d2 : ℝ → ℝ} (h1 : ∀ t, HasDerivAt x (d1 t) t)
    (h2 : ∀ t, HasDerivAt d1 (d2 t) t) (hc : Continuous d2) : ContDiff ℝ 2 x := by
  have hd1 : deriv x = d1 := funext fun t => (h1 t).deriv
  have hd2 : deriv d1 = d2 := funext fun t => (h2 t).deriv
  have e : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [e, contDiff_succ_iff_deriv]
  refine ⟨fun t => (h1 t).differentiableAt, by simp, ?_⟩
  rw [hd1, show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun t => (h2 t).differentiableAt, by simp, ?_⟩
  rw [hd2]; exact contDiff_zero.2 hc

/-! ## The homogeneous equation -/

/-- The two constants of motion of a `C²` solution `z` of `z'' + λ z = 0` on `[a, b]`. -/
lemma bvp_hom_consts {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) {a b : ℝ} {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hode : ∀ t ∈ Icc a b, deriv (deriv z) t + lam * z t = 0) :
    ∀ t ∈ Icc a b, deriv z t * C (t - a) + lam * z t * S (t - a) = deriv z a ∧
      z t * C (t - a) - deriv z t * S (t - a) = z a := by
  obtain ⟨hd, hd'⟩ := contDiff_two_aux hz
  have hS : ∀ t, HasDerivAt (fun t => S (t - a)) (C (t - a)) t := fun t =>
    (h.hS (t - a)).comp_sub_const t a
  have hC : ∀ t, HasDerivAt (fun t => C (t - a)) (-lam * S (t - a)) t := fun t =>
    (h.hC (t - a)).comp_sub_const t a
  -- the two constants of motion
  have hA : ∀ t ∈ Icc a b, HasDerivAt (fun t => deriv z t * C (t - a) + lam * z t * S (t - a)) 0 t := by
    intro t ht
    have := (((hd' t).hasDerivAt.mul (hC t)).add (((hd t).hasDerivAt.const_mul lam).mul (hS t)))
    refine this.congr_deriv ?_
    have := hode t ht
    have e : deriv (deriv z) t = -(lam * z t) := by linarith
    rw [e]; ring
  have hB : ∀ t ∈ Icc a b, HasDerivAt (fun t => z t * C (t - a) - deriv z t * S (t - a)) 0 t := by
    intro t ht
    have := (((hd t).hasDerivAt.mul (hC t)).sub (((hd' t).hasDerivAt).mul (hS t)))
    refine this.congr_deriv ?_
    have := hode t ht
    have e : deriv (deriv z) t = -(lam * z t) := by linarith
    rw [e]; ring
  have kA := constant_of_has_deriv_right_zero (a := a) (b := b)
    (fun t ht => (hA t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hA t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  have kB := constant_of_has_deriv_right_zero (a := a) (b := b)
    (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  intro t ht
  have a1 := kA t ht
  have b1 := kB t ht
  simp only [sub_self, h.S0, h.C0] at a1 b1
  exact ⟨by simpa using a1, by simpa using b1⟩

/-- A `C²` solution `z` of `z'' + λ z = 0` on `[a, b]` is `z(a) C(t-a) + z'(a) S(t-a)` there. -/
lemma bvp_hom_formula {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) {a b : ℝ} {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hode : ∀ t ∈ Icc a b, deriv (deriv z) t + lam * z t = 0) :
    ∀ t ∈ Icc a b, z t = z a * C (t - a) + deriv z a * S (t - a) := by
  intro t ht
  obtain ⟨a1, b1⟩ := bvp_hom_consts h hz hode t ht
  have idt := h.id_sq (t - a)
  calc z t = (deriv z t * C (t - a) + lam * z t * S (t - a)) * S (t - a)
        + (z t * C (t - a) - deriv z t * S (t - a)) * C (t - a) := by
        linear_combination (-z t) * idt
    _ = _ := by rw [a1, b1]; ring

/-- Both `z(t-a)`-type constants give the vanishing of a solution with zero Cauchy data. -/
lemma bvp_hom_dirichlet {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) {a b : ℝ} {z : ℝ → ℝ}
    (hz : ContDiff ℝ 2 z) (hode : ∀ t ∈ Icc a b, deriv (deriv z) t + lam * z t = 0)
    (ha : z a = 0) (hab : a ≤ b) (hb : z b = 0) (hS : S (b - a) ≠ 0) : ∀ t ∈ Icc a b, z t = 0 := by
  have hf := bvp_hom_formula h hz hode
  have h1 : deriv z a = 0 := by
    have := hf b ⟨hab, le_rfl⟩
    rw [hb, ha] at this
    have : deriv z a * S (b - a) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hS
  intro t ht
  rw [hf t ht, ha, h1]; ring


lemma bvp_continuous_S {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) : Continuous S :=
  continuous_iff_continuousAt.2 fun τ => (h.hS τ).continuousAt

lemma bvp_continuous_C {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) : Continuous C :=
  continuous_iff_continuousAt.2 fun τ => (h.hC τ).continuousAt

lemma bvp_contDiff_S {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) (a : ℝ) :
    ContDiff ℝ 2 (fun t => S (t - a)) :=
  bvp_contDiff_two (d1 := fun t => C (t - a)) (d2 := fun t => -lam * S (t - a))
    (fun t => (h.hS (t - a)).comp_sub_const t a) (fun t => (h.hC (t - a)).comp_sub_const t a)
    (continuous_const.mul ((bvp_continuous_S h).comp (continuous_id.sub continuous_const)))

/-- Linear combinations commute with the second derivative of `C²` functions. -/
lemma bvp_dd_lin {u v : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (K t : ℝ) :
    deriv (deriv (fun t => u t + K * v t)) t = deriv (deriv u) t + K * deriv (deriv v) t := by
  obtain ⟨hu1, hu2⟩ := contDiff_two_aux hu
  obtain ⟨hv1, hv2⟩ := contDiff_two_aux hv
  have e : deriv (fun t => u t + K * v t) = fun t => deriv u t + K * deriv v t :=
    funext fun t => ((hu1 t).hasDerivAt.add ((hv1 t).hasDerivAt.const_mul K)).deriv
  rw [e]
  exact ((hu2 t).hasDerivAt.add ((hv2 t).hasDerivAt.const_mul K)).deriv

/-! ## Variation of parameters -/

/-- **Particular solution (variation of parameters).** For continuous `f`, the function
`S(t-a) ∫ₐᵗ C(s-a) f(s) ds - C(t-a) ∫ₐᵗ S(s-a) f(s) ds` (that is, `∫ₐᵗ S(t-s) f(s) ds`) is a `C²`
solution of `x'' + λ x = f` on `ℝ` with `x(a) = x'(a) = 0`. -/
theorem bvp_particular {lam : ℝ} {S C : ℝ → ℝ} (h : BVPFund lam S C) (a : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ∃ xp : ℝ → ℝ, ContDiff ℝ 2 xp ∧ (∀ t, deriv (deriv xp) t + lam * xp t = f t) ∧ xp a = 0 ∧
      deriv xp a = 0 := by
  have hSc := bvp_continuous_S h
  have hCc := bvp_continuous_C h
  set A : ℝ → ℝ := fun t => ∫ s in a..t, C (s - a) * f s with hAdef
  set B : ℝ → ℝ := fun t => -∫ s in a..t, S (s - a) * f s with hBdef
  have hA : ∀ t, HasDerivAt A (C (t - a) * f t) t := fun t =>
    (Continuous.integral_hasStrictDerivAt
      (hCc.comp (continuous_id.sub continuous_const) |>.mul hf) a t).hasDerivAt
  have hB : ∀ t, HasDerivAt B (-(S (t - a) * f t)) t := fun t =>
    (Continuous.integral_hasStrictDerivAt
      (hSc.comp (continuous_id.sub continuous_const) |>.mul hf) a t).hasDerivAt.neg
  have hS : ∀ t, HasDerivAt (fun t => S (t - a)) (C (t - a)) t := fun t =>
    (h.hS (t - a)).comp_sub_const t a
  have hC : ∀ t, HasDerivAt (fun t => C (t - a)) (-lam * S (t - a)) t := fun t =>
    (h.hC (t - a)).comp_sub_const t a
  set xp : ℝ → ℝ := fun t => S (t - a) * A t + C (t - a) * B t with hxp
  set d1 : ℝ → ℝ := fun t => C (t - a) * A t - lam * S (t - a) * B t with hd1
  set d2 : ℝ → ℝ := fun t => f t - lam * xp t with hd2
  have h1 : ∀ t, HasDerivAt xp (d1 t) t := fun t => by
    refine (((hS t).mul (hA t)).add ((hC t).mul (hB t))).congr_deriv ?_
    simp only [hd1]; ring
  have h2 : ∀ t, HasDerivAt d1 (d2 t) t := fun t => by
    refine (((hC t).mul (hA t)).sub (((hS t).const_mul lam).mul (hB t))).congr_deriv ?_
    have := h.id_sq (t - a)
    simp only [hd2, hxp]
    linear_combination (f t) * this
  have hxd1 : deriv xp = d1 := funext fun t => (h1 t).deriv
  have hxd2 : deriv d1 = d2 := funext fun t => (h2 t).deriv
  have hcont : Continuous d2 :=
    hf.sub (continuous_const.mul (continuous_iff_continuousAt.2 fun t => (h1 t).continuousAt))
  refine ⟨xp, bvp_contDiff_two h1 h2 hcont, fun t => ?_, ?_, ?_⟩
  · rw [hxd1, hxd2]; simp only [hd2]; ring
  · simp [hxp, hAdef, hBdef, h.S0, h.C0]
  · rw [hxd1]; simp [hd1, hAdef, hBdef, h.S0, h.C0]

/-! ## The Fredholm alternative (DE-118) -/

/-- `x` solves the homogeneous Dirichlet problem `x'' + λ x = 0`, `x(a) = x(b) = 0`. -/
def BVPHom (lam a b : ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 x ∧ (∀ t ∈ Icc a b, deriv (deriv x) t + lam * x t = 0) ∧ x a = 0 ∧ x b = 0

/-- `x` solves the forced Dirichlet problem `x'' + λ x = f(t)`, `x(a) = x(b) = 0`. -/
def BVPForced (lam : ℝ) (f : ℝ → ℝ) (a b : ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 x ∧ (∀ t ∈ Icc a b, deriv (deriv x) t + lam * x t = f t) ∧ x a = 0 ∧ x b = 0

/-- A continuous function on `[a, b]` extends to a continuous function on `ℝ`. -/
lemma bvp_extend {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ t ∈ Icc a b, g t = f t := by
  refine ⟨fun t => f (max a (min b t)), ?_, fun t ht => ?_⟩
  · refine hf.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) fun t => ?_
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  · simp only [min_eq_right ht.2, max_eq_right ht.1]

/-- **Fredholm alternative (DE-118).** Either the homogeneous problem `x'' + λ x = 0`,
`x(a) = x(b) = 0` has a nonzero solution, or for every `f` continuous on `[a, b]` the problem
`x'' + λ x = f`, `x(a) = x(b) = 0` has a solution, unique on `[a, b]`; and the two cases exclude each
other. -/
@[kb "lebldiffyqs2026" "Theorem 4.1.2, p. 194"]
theorem fredholm_alternative {a b : ℝ} (hab : a < b) (lam : ℝ) :
    Xor (∃ x, BVPHom lam a b x ∧ ∃ t ∈ Icc a b, x t ≠ 0)
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc a b) →
        ∃ x, BVPForced lam f a b x ∧ ∀ y, BVPForced lam f a b y → ∀ t ∈ Icc a b, y t = x t) := by
  obtain ⟨S, C, h⟩ := bvp_fund_exists lam
  by_cases hS : S (b - a) = 0
  · -- eigenvalue
    have hne : ∃ t ∈ Icc a b, S (t - a) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : HasDerivWithinAt S (0 : ℝ) (Icc 0 (b - a)) 0 :=
        (hasDerivWithinAt_const (0 : ℝ) (Icc 0 (b - a)) (0 : ℝ)).congr
          (fun y hy => by simpa using hcon (y + a) ⟨by linarith [hy.1], by linarith [hy.2]⟩)
          (by simpa using h.S0)
      have h1 : HasDerivWithinAt S (C 0) (Icc 0 (b - a)) 0 := (h.hS 0).hasDerivWithinAt
      have := (uniqueDiffOn_Icc (by linarith) 0
        (left_mem_Icc.2 (by linarith))).eq_deriv _ h1 h0
      rw [h.C0] at this
      exact one_ne_zero this
    have hhom : BVPHom lam a b (fun t => S (t - a)) := by
      refine ⟨bvp_contDiff_S h a, fun t _ => ?_, by simp [h.S0], hS⟩
      have e : deriv (fun t => S (t - a)) = fun t => C (t - a) :=
        funext fun t => ((h.hS (t - a)).comp_sub_const t a).deriv
      rw [e, ((h.hC (t - a)).comp_sub_const t a).deriv]; ring
    have hP : ∃ x, BVPHom lam a b x ∧ ∃ t ∈ Icc a b, x t ≠ 0 := ⟨_, hhom, hne⟩
    refine Or.inl ⟨hP, fun hQ => ?_⟩
    obtain ⟨x, hx, hxu⟩ := hQ (fun _ => 0) continuousOn_const
    obtain ⟨t, ht, hne⟩ := hne
    have h1 := hxu (fun t => S (t - a)) ⟨hhom.1, fun t ht => by simpa using hhom.2.1 t ht,
      hhom.2.2.1, hhom.2.2.2⟩ t ht
    have h2 := hxu (fun _ => 0) ⟨contDiff_const, fun t _ => by simp, rfl, rfl⟩ t ht
    exact hne (h1.trans h2.symm)
  · -- not an eigenvalue
    have hQ : ∀ f : ℝ → ℝ, ContinuousOn f (Icc a b) →
        ∃ x, BVPForced lam f a b x ∧ ∀ y, BVPForced lam f a b y → ∀ t ∈ Icc a b, y t = x t := by
      intro f hf
      obtain ⟨g, hg, hgf⟩ := bvp_extend hab.le hf
      obtain ⟨xp, hxp, hode, hxa, hxa'⟩ := bvp_particular h a hg
      set K : ℝ := -(xp b / S (b - a)) with hK
      have hSd := bvp_contDiff_S h a
      have hx : BVPForced lam f a b (fun t => xp t + K * S (t - a)) := by
        refine ⟨hxp.add (contDiff_const.mul hSd), fun t ht => ?_, ?_, ?_⟩
        · rw [bvp_dd_lin hxp hSd K t]
          have e : deriv (fun t => S (t - a)) = fun t => C (t - a) :=
            funext fun t => ((h.hS (t - a)).comp_sub_const t a).deriv
          have e2 : deriv (deriv (fun t => S (t - a))) t = -lam * S (t - a) := by
            rw [e]; exact ((h.hC (t - a)).comp_sub_const t a).deriv
          rw [e2, ← hgf t ht, ← hode t]; ring
        · simp [hxa, h.S0]
        · simp only [hK]; field_simp; ring
      refine ⟨_, hx, fun y hy t ht => ?_⟩
      have hz := bvp_hom_dirichlet h (z := fun t => y t + (-1) * (xp t + K * S (t - a)))
        (hy.1.add (contDiff_const.mul hx.1)) (fun t ht => ?_) (by linarith [hy.2.2.1, hx.2.2.1])
        hab.le (by linarith [hy.2.2.2, hx.2.2.2]) hS t ht
      · linarith
      · rw [bvp_dd_lin hy.1 hx.1 (-1) t]
        have := hy.2.1 t ht
        have := hx.2.1 t ht
        linarith
    exact Or.inr ⟨hQ, fun ⟨x, hx, hne⟩ => by
      obtain ⟨x', hx', hxu⟩ := hQ (fun _ => 0) continuousOn_const
      obtain ⟨t, ht, hne⟩ := hne
      have h1 := hxu x ⟨hx.1, fun t ht => by simpa using hx.2.1 t ht, hx.2.2.1, hx.2.2.2⟩ t ht
      have h2 := hxu (fun _ => 0) ⟨contDiff_const, fun t _ => by simp, rfl, rfl⟩ t ht
      exact hne (h1.trans h2.symm)⟩

/-! ## Neumann and periodic eigenvalue problems (DE-115) -/

lemma bvp_cos_ode (ω : ℝ) :
    ContDiff ℝ 2 (fun t => cos (ω * t)) ∧
      ∀ t, deriv (deriv (fun t => cos (ω * t))) t + ω ^ 2 * cos (ω * t) = 0 := by
  refine ⟨by fun_prop, fun t => ?_⟩
  have e : deriv (fun ξ => -(ω * sin (ω * ξ))) t = -(ω * (ω * cos (ω * t))) :=
    (((hasDerivAt_sin_mul ω t).const_mul ω).neg).deriv
  rw [deriv_cos_mul, e]; ring

lemma bvp_sin_ode (ω : ℝ) :
    ContDiff ℝ 2 (fun t => sin (ω * t)) ∧
      ∀ t, deriv (deriv (fun t => sin (ω * t))) t + ω ^ 2 * sin (ω * t) = 0 := by
  refine ⟨by fun_prop, fun t => ?_⟩
  rw [deriv_sin_mul, ((hasDerivAt_cos_mul ω t).const_mul ω).deriv]; ring

lemma bvp_sin_zero {L ω : ℝ} (hL : 0 < L) (hω : 0 < ω) (h : sin (ω * L) = 0) :
    ∃ n : ℕ, 0 < n ∧ ω = n * π / L := by
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 h
  have hmpos : 0 < m := by
    have : (0 : ℝ) < m * π := by rw [hm]; positivity
    have h' : (0 : ℝ) < m := by
      by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
    exact_mod_cast h'
  refine ⟨m.toNat, by omega, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℝ) = m := by exact_mod_cast Int.toNat_of_nonneg hmpos.le
  rw [hcast]; field_simp; linarith

/-- **Neumann eigenfunctions (DE-115).** For `n ≥ 0`, `cos(nπt/L)` is a nonzero solution of
`x'' + λ x = 0`, `x'(0) = x'(L) = 0` with `λ = (nπ/L)²`; for `n = 0` it is the constant `1`. -/
@[kb "lebldiffyqs2026" "Example 4.1.4, p. 191"]
theorem neumann_eigenfunction {L : ℝ} (hL : L ≠ 0) (n : ℕ) :
    ContDiff ℝ 2 (fun t => cos (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => cos (n * π / L * t))) t
        + (n * π / L) ^ 2 * cos (n * π / L * t) = 0) ∧
      deriv (fun t => cos (n * π / L * t)) 0 = 0 ∧ deriv (fun t => cos (n * π / L * t)) L = 0 ∧
      cos (n * π / L * 0) ≠ 0 := by
  obtain ⟨h1, h2⟩ := bvp_cos_ode (n * π / L)
  refine ⟨h1, h2, by simp [deriv_cos_mul], ?_, by simp⟩
  have : (n : ℝ) * π / L * L = n * π := by field_simp
  simp [deriv_cos_mul, this, sin_nat_mul_pi]

/-- **Neumann eigenvalues (DE-115).** If `x'' + λ x = 0` on `[0, L]`, `x'(0) = x'(L) = 0` has a nonzero
solution then `λ = (nπ/L)²` for some `n ≥ 0` (`λ = 0` with constant eigenfunction is `n = 0`). -/
@[kb "lebldiffyqs2026" "Example 4.1.4, p. 191"]
theorem neumann_eigenvalue {L lam : ℝ} (hL : 0 < L) {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hode : ∀ t ∈ Icc 0 L, deriv (deriv x) t + lam * x t = 0)
    (h0 : deriv x 0 = 0) (hL' : deriv x L = 0) (hne : ∃ t ∈ Icc 0 L, x t ≠ 0) :
    ∃ n : ℕ, lam = (n * π / L) ^ 2 := by
  -- the core computation, for any fundamental pair
  have core : ∀ {S C : ℝ → ℝ}, BVPFund lam S C → lam * S L = 0 := by
    intro S C h
    have hf := bvp_hom_formula h hx hode
    have hc := bvp_hom_consts h hx hode L ⟨hL.le, le_rfl⟩
    have hx0 : x 0 ≠ 0 := by
      intro hz
      obtain ⟨t, ht, hxt⟩ := hne
      apply hxt
      have := hf t ht
      simp [hz, h0] at this
      exact this
    simp only [sub_zero, hL', h0] at hc
    obtain ⟨c1, c2⟩ := hc
    have hxL : x L ≠ 0 := by
      intro hz; rw [hz] at c2; apply hx0; linarith
    have : x L * (lam * S L) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hxL
  rcases lt_trichotomy lam 0 with hl | hl | hl
  · exfalso
    have hν : Real.sqrt (-lam) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hf := bvp_fund_neg hν
    rw [Real.sq_sqrt (by linarith), neg_neg] at hf
    have := core hf
    have h1 : Real.sinh (Real.sqrt (-lam) * L) = 0 := by
      have : lam * (Real.sinh (Real.sqrt (-lam) * L) / Real.sqrt (-lam)) = 0 := this
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact (div_eq_zero_iff.1 h).resolve_right hν
    have := Real.sinh_eq_zero.1 h1
    rcases mul_eq_zero.1 this with h | h
    · exact hν h
    · linarith
  · exact ⟨0, by simp [hl]⟩
  · have hω : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hl).ne'
    have hf := bvp_fund_pos hω
    rw [Real.sq_sqrt hl.le] at hf
    have := core hf
    have h1 : sin (Real.sqrt lam * L) = 0 := by
      have : lam * (sin (Real.sqrt lam * L) / Real.sqrt lam) = 0 := this
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact (div_eq_zero_iff.1 h).resolve_right hω
    obtain ⟨n, -, hn⟩ := bvp_sin_zero hL (Real.sqrt_pos.2 hl) h1
    exact ⟨n, by rw [← hn, Real.sq_sqrt hl.le]⟩

/-- **Periodic eigenfunctions, cosine (DE-115).** On `[-L, L]`, `cos(nπt/L)` (`n ≥ 0`) solves
`x'' + λ x = 0`, `λ = (nπ/L)²`, with `x(-L) = x(L)` and `x'(-L) = x'(L)`, and is not zero. -/
@[kb "lebldiffyqs2026" "Example 4.1.5, p. 192"]
theorem periodic_cos_eigenfunction {L : ℝ} (hL : L ≠ 0) (n : ℕ) :
    ContDiff ℝ 2 (fun t => cos (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => cos (n * π / L * t))) t
        + (n * π / L) ^ 2 * cos (n * π / L * t) = 0) ∧
      cos (n * π / L * (-L)) = cos (n * π / L * L) ∧
      deriv (fun t => cos (n * π / L * t)) (-L) = deriv (fun t => cos (n * π / L * t)) L ∧
      cos (n * π / L * 0) ≠ 0 := by
  obtain ⟨h1, h2⟩ := bvp_cos_ode (n * π / L)
  have : (n : ℝ) * π / L * L = n * π := by field_simp
  refine ⟨h1, h2, ?_, ?_, by simp⟩
  · rw [mul_neg, this, cos_neg]
  · simp [deriv_cos_mul, mul_neg, this, sin_nat_mul_pi]

/-- **Periodic eigenfunctions, sine (DE-115).** On `[-L, L]`, `sin(nπt/L)` (`n ≥ 1`) solves
`x'' + λ x = 0`, `λ = (nπ/L)²`, with `x(-L) = x(L)` and `x'(-L) = x'(L)`, and is not zero. -/
@[kb "lebldiffyqs2026" "Example 4.1.5, p. 192"]
theorem periodic_sin_eigenfunction {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 2 (fun t => sin (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => sin (n * π / L * t))) t
        + (n * π / L) ^ 2 * sin (n * π / L * t) = 0) ∧
      sin (n * π / L * (-L)) = sin (n * π / L * L) ∧
      deriv (fun t => sin (n * π / L * t)) (-L) = deriv (fun t => sin (n * π / L * t)) L ∧
      ∃ t, sin (n * π / L * t) ≠ 0 := by
  obtain ⟨h1, h2, -, -, h5⟩ := sin_dirichlet_eigenfunction hL hn
  obtain ⟨-, -, -, -, h6⟩ := sin_dirichlet_eigenfunction hL hn
  have : (n : ℝ) * π / L * L = n * π := by field_simp
  refine ⟨h1, h2, ?_, ?_, h6⟩
  · rw [mul_neg, this, sin_neg, sin_nat_mul_pi]; simp
  · simp [deriv_sin_mul, mul_neg, this]

/-- **Periodic eigenvalues (DE-115).** If `x'' + λ x = 0` on `[-L, L]`, `x(-L) = x(L)`,
`x'(-L) = x'(L)` has a nonzero solution then `λ = (nπ/L)²` for some `n ≥ 0`. -/
@[kb "lebldiffyqs2026" "Example 4.1.5, p. 192"]
theorem periodic_eigenvalue {L lam : ℝ} (hL : 0 < L) {x : ℝ → ℝ} (hx : ContDiff ℝ 2 x)
    (hode : ∀ t ∈ Icc (-L) L, deriv (deriv x) t + lam * x t = 0)
    (hv : x (-L) = x L) (hd : deriv x (-L) = deriv x L) (hne : ∃ t ∈ Icc (-L) L, x t ≠ 0) :
    ∃ n : ℕ, lam = (n * π / L) ^ 2 := by
  have core : ∀ {S C : ℝ → ℝ}, BVPFund lam S C → C (2 * L) = 1 := by
    intro S C h
    have hf := bvp_hom_formula h hx hode
    have hc := bvp_hom_consts h hx hode L ⟨by linarith, le_rfl⟩
    have e : L - -L = 2 * L := by ring
    rw [e, ← hv, ← hd] at hc
    obtain ⟨c1, c2⟩ := hc
    by_contra hC
    have hC' : C (2 * L) - 1 ≠ 0 := sub_ne_zero.2 hC
    have key := h.id_sq (2 * L)
    have hp : x (-L) * (2 - 2 * C (2 * L)) = 0 := by
      linear_combination (C (2 * L) - 1) * c2 + S (2 * L) * c1 - x (-L) * key
    have hq : deriv x (-L) * (2 - 2 * C (2 * L)) = 0 := by
      linear_combination (C (2 * L) - 1) * c1 - lam * S (2 * L) * c2 - deriv x (-L) * key
    have h2 : (2 - 2 * C (2 * L)) ≠ 0 := by
      intro hz; apply hC; linarith
    have hp0 := (mul_eq_zero.1 hp).resolve_right h2
    have hq0 := (mul_eq_zero.1 hq).resolve_right h2
    obtain ⟨t, ht, hxt⟩ := hne
    apply hxt
    rw [hf t ht, hp0, hq0]; ring
  rcases lt_trichotomy lam 0 with hl | hl | hl
  · exfalso
    have hν : Real.sqrt (-lam) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have hf := bvp_fund_neg hν
    rw [Real.sq_sqrt (by linarith), neg_neg] at hf
    have h1 : Real.cosh (Real.sqrt (-lam) * (2 * L)) = 1 := core hf
    have h2 := Real.cosh_sq (Real.sqrt (-lam) * (2 * L))
    rw [h1] at h2
    have h3 : Real.sinh (Real.sqrt (-lam) * (2 * L)) = 0 := by nlinarith [sq_nonneg (Real.sinh (Real.sqrt (-lam) * (2 * L)))]
    have := Real.sinh_eq_zero.1 h3
    rcases mul_eq_zero.1 this with h | h
    · exact hν h
    · linarith
  · exact ⟨0, by simp [hl]⟩
  · have hω : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hl).ne'
    have hf := bvp_fund_pos hω
    rw [Real.sq_sqrt hl.le] at hf
    have h1 : cos (Real.sqrt lam * (2 * L)) = 1 := core hf
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 h1
    have h2 : sin (Real.sqrt lam * L) = 0 := by
      have : Real.sqrt lam * L = m * π := by linarith
      rw [this, Real.sin_int_mul_pi]
    obtain ⟨n, -, hn⟩ := bvp_sin_zero hL (Real.sqrt_pos.2 hl) h2
    exact ⟨n, by rw [← hn, Real.sq_sqrt hl.le]⟩

/-! ## The simply supported beam (DE-159) -/

lemma bvp_deriv_sin (c ω : ℝ) :
    deriv (fun x => c * sin (ω * x)) = fun x => (c * ω) * cos (ω * x) :=
  funext fun x => (((hasDerivAt_sin_mul ω x).const_mul c).congr_deriv (by ring)).deriv

lemma bvp_deriv_cos (c ω : ℝ) :
    deriv (fun x => c * cos (ω * x)) = fun x => -(c * ω) * sin (ω * x) :=
  funext fun x => (((hasDerivAt_cos_mul ω x).const_mul c).congr_deriv (by ring)).deriv

/-- **Simply supported beam (DE-159).** For `L > 0` and `n ≥ 1`, `y = sin(nπx/L)` is a nonzero solution of
`y⁽⁴⁾ = λ y` on `[0, L]` with `y(0) = y(L) = 0` and `y''(0) = y''(L) = 0`, where `λ = (nπ/L)⁴`. -/
@[kb "lebldiffyqs2026" "Example 5.2.1, p. 284"]
theorem beam_eigenfunction {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 4 (fun x => sin (n * π / L * x)) ∧
      (∀ x, deriv (deriv (deriv (deriv (fun x => sin (n * π / L * x))))) x
        = (n * π / L) ^ 4 * sin (n * π / L * x)) ∧
      sin (n * π / L * 0) = 0 ∧ sin (n * π / L * L) = 0 ∧
      deriv (deriv (fun x => sin (n * π / L * x))) 0 = 0 ∧
      deriv (deriv (fun x => sin (n * π / L * x))) L = 0 ∧
      ∃ x, sin (n * π / L * x) ≠ 0 := by
  obtain ⟨-, -, h0, hL', hne⟩ := sin_dirichlet_eigenfunction hL hn
  set ω : ℝ := n * π / L with hω
  have e1 : deriv (fun x => sin (ω * x)) = fun x => ω * cos (ω * x) := deriv_sin_mul ω
  have e2 : deriv (deriv (fun x => sin (ω * x))) = fun x => -(ω * ω) * sin (ω * x) := by
    rw [e1, bvp_deriv_cos]
  have e3 : deriv (deriv (deriv (fun x => sin (ω * x)))) = fun x => (-(ω * ω) * ω) * cos (ω * x) := by
    rw [e2, bvp_deriv_sin]
  have e4 : deriv (deriv (deriv (deriv (fun x => sin (ω * x))))) =
      fun x => -((-(ω * ω) * ω) * ω) * sin (ω * x) := by
    rw [e3, bvp_deriv_cos]
  refine ⟨by fun_prop, fun x => ?_, h0, hL', ?_, ?_, hne⟩
  · rw [e4]; ring
  · rw [e2]; simp
  · rw [e2]
    have : ω * L = n * π := by rw [hω]; field_simp
    simp [this, sin_nat_mul_pi]

/-! ## Finite trigonometric polynomials and term-by-term solution (DE-135, DE-136) -/

lemma bvp_trig_hasDeriv (N : Finset ℕ) (ω α β : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ n ∈ N, (α n * cos (ω n * t) + β n * sin (ω n * t)))
      (∑ n ∈ N, (α n * (-(ω n * sin (ω n * t))) + β n * (ω n * cos (ω n * t)))) t :=
  HasDerivAt.fun_sum fun n _ =>
    ((hasDerivAt_cos_mul (ω n) t).const_mul (α n)).add ((hasDerivAt_sin_mul (ω n) t).const_mul (β n))

lemma bvp_trig_hasDeriv2 (N : Finset ℕ) (ω α β : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ n ∈ N, (α n * (-(ω n * sin (ω n * t))) + β n * (ω n * cos (ω n * t))))
      (∑ n ∈ N, (α n * (-(ω n * (ω n * cos (ω n * t)))) +
        β n * (ω n * (-(ω n * sin (ω n * t)))))) t :=
  HasDerivAt.fun_sum fun n _ =>
    (((hasDerivAt_sin_mul (ω n) t).const_mul (ω n)).neg.const_mul (α n)).add
      (((hasDerivAt_cos_mul (ω n) t).const_mul (ω n)).const_mul (β n))

lemma bvp_trig_dd (N : Finset ℕ) (ω α β : ℕ → ℝ) (t : ℝ) :
    deriv (deriv (fun t => ∑ n ∈ N, (α n * cos (ω n * t) + β n * sin (ω n * t)))) t
      = ∑ n ∈ N, (-(ω n ^ 2)) * (α n * cos (ω n * t) + β n * sin (ω n * t)) := by
  have e : deriv (fun t => ∑ n ∈ N, (α n * cos (ω n * t) + β n * sin (ω n * t)))
      = fun t => ∑ n ∈ N, (α n * (-(ω n * sin (ω n * t))) + β n * (ω n * cos (ω n * t))) :=
    funext fun t => (bvp_trig_hasDeriv N ω α β t).deriv
  rw [e, (bvp_trig_hasDeriv2 N ω α β t).deriv]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma bvp_trig_contDiff (N : Finset ℕ) (ω α β : ℕ → ℝ) :
    ContDiff ℝ 2 (fun t => ∑ n ∈ N, (α n * cos (ω n * t) + β n * sin (ω n * t))) :=
  ContDiff.sum fun n _ => by fun_prop

/-- **Term-by-term solution (DE-135, DE-136).** If `k - m ωₙ² ≠ 0` for `n ∈ N`, the trigonometric
polynomial `∑ (aₙ cos ωₙt + bₙ sin ωₙt)/(k - m ωₙ²)` solves `m x'' + k x = ∑ (aₙ cos ωₙt + bₙ sin ωₙt)`. -/
theorem bvp_forced_trig (m k : ℝ) (N : Finset ℕ) (ω α β : ℕ → ℝ)
    (hres : ∀ n ∈ N, k - m * ω n ^ 2 ≠ 0) (t : ℝ) :
    m * deriv (deriv (fun t => ∑ n ∈ N, (α n / (k - m * ω n ^ 2) * cos (ω n * t)
        + β n / (k - m * ω n ^ 2) * sin (ω n * t)))) t
      + k * ∑ n ∈ N, (α n / (k - m * ω n ^ 2) * cos (ω n * t)
        + β n / (k - m * ω n ^ 2) * sin (ω n * t))
      = ∑ n ∈ N, (α n * cos (ω n * t) + β n * sin (ω n * t)) := by
  rw [bvp_trig_dd N ω (fun n => α n / (k - m * ω n ^ 2)) (fun n => β n / (k - m * ω n ^ 2)) t,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have := hres n hn
  field_simp
  ring

/-- **Forced Dirichlet problem by a sine series (DE-135).** If `λ ≠ (nπ/L)²` for `n ∈ N`, then
`x = ∑ bₙ/(λ - (nπ/L)²) sin(nπt/L)` solves `x'' + λ x = ∑ bₙ sin(nπt/L)` with `x(0) = x(L) = 0`. -/
@[kb "lebldiffyqs2026" "Example 4.4.3, p. 222"]
theorem forced_dirichlet_sine {L lam : ℝ} (hL : L ≠ 0) (N : Finset ℕ) (b : ℕ → ℝ)
    (hlam : ∀ n ∈ N, lam ≠ (n * π / L) ^ 2) :
    ContDiff ℝ 2 (fun t => ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * t))) t
        + lam * ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * t)
        = ∑ n ∈ N, b n * sin (n * π / L * t)) ∧
      ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * 0) = 0 ∧
      ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * L) = 0 := by
  have hres : ∀ n ∈ N, lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2 ≠ 0 := fun n hn => by
    have := hlam n hn
    simp only [one_mul]; exact sub_ne_zero.2 this
  have hfun : (fun t => ∑ n ∈ N, b n / (lam - (n * π / L) ^ 2) * sin (n * π / L * t)) =
      fun t => ∑ n ∈ N, ((0 : ℕ → ℝ) n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2)
        * cos ((fun n : ℕ => (n * π / L)) n * t) +
        b n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2) * sin ((fun n : ℕ => (n * π / L)) n * t)) := by
    funext t; simp
  refine ⟨?_, fun t => ?_, ?_, ?_⟩
  · rw [hfun]; exact bvp_trig_contDiff N _ _ _
  · have := bvp_forced_trig 1 lam N (fun n : ℕ => (n * π / L)) 0 b hres t
    rw [← hfun] at this
    simpa using this
  · simp
  · refine Finset.sum_eq_zero fun n _ => ?_
    have : (n : ℝ) * π / L * L = n * π := by field_simp
    rw [this, sin_nat_mul_pi]; simp

/-- **Forced Neumann problem by a cosine series (DE-135).** If `λ ≠ (nπ/L)²` for `n ∈ N`, then
`x = ∑ aₙ/(λ - (nπ/L)²) cos(nπt/L)` solves `x'' + λ x = ∑ aₙ cos(nπt/L)` with `x'(0) = x'(L) = 0`
(the constant term of the cosine series is the `n = 0` entry). -/
@[kb "lebldiffyqs2026" "Example 4.4.4, p. 223"]
theorem forced_neumann_cosine {L lam : ℝ} (hL : L ≠ 0) (N : Finset ℕ) (a : ℕ → ℝ)
    (hlam : ∀ n ∈ N, lam ≠ (n * π / L) ^ 2) :
    ContDiff ℝ 2 (fun t => ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t)) ∧
      (∀ t, deriv (deriv (fun t => ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t))) t
        + lam * ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t)
        = ∑ n ∈ N, a n * cos (n * π / L * t)) ∧
      deriv (fun t => ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t)) 0 = 0 ∧
      deriv (fun t => ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t)) L = 0 := by
  have hres : ∀ n ∈ N, lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2 ≠ 0 := fun n hn => by
    have := hlam n hn
    simp only [one_mul]; exact sub_ne_zero.2 this
  have hfun : (fun t => ∑ n ∈ N, a n / (lam - (n * π / L) ^ 2) * cos (n * π / L * t)) =
      fun t => ∑ n ∈ N, (a n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2)
        * cos ((fun n : ℕ => (n * π / L)) n * t) +
        (0 : ℕ → ℝ) n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2) *
          sin ((fun n : ℕ => (n * π / L)) n * t)) := by
    funext t; simp
  refine ⟨?_, fun t => ?_, ?_, ?_⟩
  · rw [hfun]; exact bvp_trig_contDiff N _ _ _
  · have := bvp_forced_trig 1 lam N (fun n : ℕ => (n * π / L)) a 0 hres t
    rw [← hfun] at this
    simpa using this
  · rw [hfun]
    beta_reduce
    rw [(bvp_trig_hasDeriv N (fun n : ℕ => (n * π / L))
      (fun n => a n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2))
      (fun n => (0 : ℕ → ℝ) n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2)) 0).deriv]
    simp
  · rw [hfun]
    beta_reduce
    rw [(bvp_trig_hasDeriv N (fun n : ℕ => (n * π / L))
      (fun n => a n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2))
      (fun n => (0 : ℕ → ℝ) n / (lam - 1 * (fun n : ℕ => (n * π / L)) n ^ 2)) L).deriv]
    refine Finset.sum_eq_zero fun n _ => ?_
    have : (n : ℝ) * π / L * L = n * π := by field_simp
    simp [this, sin_nat_mul_pi]

/-! ## Periodically forced oscillators (DE-136, DE-137) -/

/-- **Steady periodic solution (DE-136).** Let `m ≠ 0` and `k/m ≠ (nπ/L)²` for `n ∈ N`.  Then
`x = ∑ (aₙ cos(nπt/L) + bₙ sin(nπt/L))/(k - m (nπ/L)²)` solves `m x'' + k x = ∑ (aₙ cos + bₙ sin)`, and
`x` is `2L`-periodic. -/
@[kb "lebldiffyqs2026" "§4.5 steady periodic solution, p. 226"]
theorem steady_periodic_forced {m k L : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (N : Finset ℕ) (a b : ℕ → ℝ)
    (hk : ∀ n ∈ N, k / m ≠ (n * π / L) ^ 2) :
    ContDiff ℝ 2 (fun t => ∑ n ∈ N, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * t)
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * t))) ∧
      (∀ t, m * deriv (deriv (fun t => ∑ n ∈ N, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * t)
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * t)))) t
        + k * ∑ n ∈ N, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * t)
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * t))
        = ∑ n ∈ N, (a n * cos (n * π / L * t) + b n * sin (n * π / L * t))) ∧
      ∀ t, ∑ n ∈ N, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * (t + 2 * L))
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * (t + 2 * L)))
        = ∑ n ∈ N, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * t)
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * t)) := by
  have hres : ∀ n ∈ N, k - m * (fun n : ℕ => (n * π / L)) n ^ 2 ≠ 0 := fun n hn h => by
    apply hk n hn
    simp only at h
    rw [div_eq_iff hm]
    linarith
  refine ⟨bvp_trig_contDiff N (fun n : ℕ => (n * π / L))
      (fun n => a n / (k - m * (n * π / L) ^ 2)) (fun n => b n / (k - m * (n * π / L) ^ 2)),
    fun t => bvp_forced_trig m k N (fun n : ℕ => (n * π / L)) a b hres t, fun t => ?_⟩
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (n : ℝ) * π / L * (t + 2 * L) = n * π / L * t + n * (2 * π) := by field_simp
  rw [this, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

/-- The resonant response `t/(2mω) (α sin ωt - β cos ωt)`. -/
noncomputable def bvpRes (m ω α β : ℝ) (t : ℝ) : ℝ :=
  1 / (2 * m * ω) * (t * (α * sin (ω * t) - β * cos (ω * t)))

lemma bvp_dd_add {u v : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (t : ℝ) :
    deriv (deriv (fun t => u t + v t)) t = deriv (deriv u) t + deriv (deriv v) t := by
  simpa using bvp_dd_lin hu hv 1 t

lemma bvp_res_contDiff (m ω α β : ℝ) : ContDiff ℝ 2 (bvpRes m ω α β) := by
  unfold bvpRes; fun_prop

lemma bvp_res_ode {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (α β t : ℝ) :
    m * deriv (deriv (bvpRes m ω α β)) t + (m * ω ^ 2) * bvpRes m ω α β t
      = α * cos (ω * t) + β * sin (ω * t) := by
  set g : ℝ → ℝ := fun t => α * sin (ω * t) - β * cos (ω * t) with hg
  set gd : ℝ → ℝ := fun t => α * (ω * cos (ω * t)) - β * (-(ω * sin (ω * t))) with hgd
  have hg1 : ∀ t, HasDerivAt g (gd t) t := fun t =>
    ((hasDerivAt_sin_mul ω t).const_mul α).sub ((hasDerivAt_cos_mul ω t).const_mul β)
  have hg2 : ∀ t, HasDerivAt gd (-(ω ^ 2) * g t) t := fun t =>
    ((((hasDerivAt_cos_mul ω t).const_mul ω).const_mul α).sub
      (((hasDerivAt_sin_mul ω t).const_mul ω).neg.const_mul β)).congr_deriv (by simp only [hg]; ring)
  have hx1 : ∀ t, HasDerivAt (bvpRes m ω α β) (1 / (2 * m * ω) * (g t + t * gd t)) t := fun t =>
    ((((hasDerivAt_id' t).mul (hg1 t)).const_mul (1 / (2 * m * ω))).congr_deriv (by ring))
  have hx2 : ∀ t, HasDerivAt (fun t => 1 / (2 * m * ω) * (g t + t * gd t))
      (1 / (2 * m * ω) * (gd t + (gd t + t * (-(ω ^ 2) * g t)))) t := fun t =>
    ((((hg1 t).add ((hasDerivAt_id' t).mul (hg2 t))).const_mul (1 / (2 * m * ω))).congr_deriv
      (by ring))
  have e1 : deriv (bvpRes m ω α β) = fun t => 1 / (2 * m * ω) * (g t + t * gd t) :=
    funext fun t => (hx1 t).deriv
  rw [e1, (hx2 t).deriv]
  simp only [bvpRes, hg, hgd]
  field_simp
  ring

/-- **Resonance, one term (DE-137).** If `m ≠ 0` and `ω > 0`, then `t/(2mω) (α sin ωt - β cos ωt)` solves
`m x'' + m ω² x = α cos ωt + β sin ωt` (forcing at the natural frequency `√(k/m) = ω`), and when
`(α, β) ≠ (0, 0)` it is unbounded. -/
@[kb "lebldiffyqs2026" "§4.5 resonance, p. 229"]
theorem resonance_term {m ω : ℝ} (hm : m ≠ 0) (hω : 0 < ω) (α β : ℝ) :
    ContDiff ℝ 2 (bvpRes m ω α β) ∧
      (∀ t, m * deriv (deriv (bvpRes m ω α β)) t + (m * ω ^ 2) * bvpRes m ω α β t
        = α * cos (ω * t) + β * sin (ω * t)) ∧
      ((α ≠ 0 ∨ β ≠ 0) → ∀ M : ℝ, ∃ t, M < |bvpRes m ω α β t|) := by
  refine ⟨bvp_res_contDiff m ω α β, bvp_res_ode hm hω.ne' α β, fun hαβ M => ?_⟩
  set g : ℝ → ℝ := fun t => α * sin (ω * t) - β * cos (ω * t) with hg
  have hper : ∀ (s : ℝ) (j : ℕ), g (s + j * (2 * π / ω)) = g s := by
    intro s j
    have : ω * (s + j * (2 * π / ω)) = ω * s + j * (2 * π) := by field_simp
    simp only [hg, this, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  obtain ⟨s0, hs0, hgs0⟩ : ∃ s0 : ℝ, 0 ≤ s0 ∧ g s0 ≠ 0 := by
    by_cases hb : β = 0
    · have ha : α ≠ 0 := hαβ.resolve_right (not_not.2 hb)
      refine ⟨π / (2 * ω), by positivity, ?_⟩
      have : ω * (π / (2 * ω)) = π / 2 := by field_simp
      simp [hg, this, ha]
    · exact ⟨0, le_rfl, by simpa [hg] using hb⟩
  set c : ℝ := |g s0| with hc
  have hcpos : 0 < c := abs_pos.2 hgs0
  set T : ℝ := 2 * π / ω with hT
  have hTpos : 0 < T := by positivity
  set c' : ℝ := |1 / (2 * m * ω)| with hc'
  have hc'pos : 0 < c' := abs_pos.2 (by positivity)
  have hκ : 0 < c' * T * c := by positivity
  obtain ⟨j, hj⟩ := exists_nat_gt (M / (c' * T * c))
  refine ⟨s0 + j * T, ?_⟩
  have hjT : (0 : ℝ) ≤ j * T := by positivity
  have h1 : |bvpRes m ω α β (s0 + j * T)| = c' * (s0 + j * T) * c := by
    have : bvpRes m ω α β (s0 + j * T) = 1 / (2 * m * ω) * ((s0 + j * T) * g s0) := by
      unfold bvpRes
      have := hper s0 j
      simp only [hg] at this ⊢
      rw [this]
    rw [this, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s0 + j * T)]
    ring
  rw [h1]
  have h2 : M < j * (c' * T * c) := (div_lt_iff₀ hκ).1 hj
  have h3 : (j : ℝ) * T ≤ s0 + j * T := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos hc'pos hcpos).le]

/-- **Resonance for a periodically forced oscillator (DE-137).** Let `m ≠ 0`, `L > 0`, and suppose the
natural frequency matches exactly one term of the forcing `∑_{n ∈ N} (aₙ cos(nπt/L) + bₙ sin(nπt/L))`:
`k = m (n₀π/L)²` with `n₀ ∈ N`, `n₀ ≥ 1`, `k/m ≠ (nπ/L)²` for the other `n ∈ N`, and
`(a_{n₀}, b_{n₀}) ≠ (0, 0)`.  Then `m x'' + k x = ∑ (aₙ cos + bₙ sin)` has a `C²` solution (the steady
terms plus the resonant `t`-growing term) and it is unbounded. -/
@[kb "lebldiffyqs2026" "Example 4.5.2, p. 229"]
theorem resonance_forced {m k L : ℝ} (hm : m ≠ 0) (hL : 0 < L) (N : Finset ℕ) (a b : ℕ → ℝ)
    {n₀ : ℕ} (hn₀ : n₀ ∈ N) (hn₀pos : 0 < n₀) (hk : k = m * (n₀ * π / L) ^ 2)
    (hnon : ∀ n ∈ N, n ≠ n₀ → k / m ≠ (n * π / L) ^ 2) (hab : a n₀ ≠ 0 ∨ b n₀ ≠ 0) :
    ∃ x : ℝ → ℝ, ContDiff ℝ 2 x ∧
      (∀ t, m * deriv (deriv x) t + k * x t
        = ∑ n ∈ N, (a n * cos (n * π / L * t) + b n * sin (n * π / L * t))) ∧
      ∀ M : ℝ, ∃ t, M < |x t| := by
  have hω : 0 < (n₀ : ℝ) * π / L := by
    have : (0 : ℝ) < n₀ := by exact_mod_cast hn₀pos
    positivity
  have hnon' : ∀ n ∈ N.erase n₀, k / m ≠ (n * π / L) ^ 2 := fun n hn =>
    hnon n (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn)
  obtain ⟨hPc, hPode, -⟩ := steady_periodic_forced hm hL.ne' (N.erase n₀) a b hnon'
  set P : ℝ → ℝ := fun t => ∑ n ∈ N.erase n₀, (a n / (k - m * (n * π / L) ^ 2) * cos (n * π / L * t)
        + b n / (k - m * (n * π / L) ^ 2) * sin (n * π / L * t)) with hP
  obtain ⟨hRc, hRode, hRunb⟩ := resonance_term hm hω (a n₀) (b n₀)
  refine ⟨fun t => P t + bvpRes m (n₀ * π / L) (a n₀) (b n₀) t, hPc.add hRc, fun t => ?_, ?_⟩
  · rw [bvp_dd_add hPc hRc]
    have h1 : m * deriv (deriv P) t + k * P t
        = ∑ n ∈ N.erase n₀, (a n * cos (n * π / L * t) + b n * sin (n * π / L * t)) := hPode t
    have h2 := hRode t
    rw [← hk] at h2
    rw [← Finset.add_sum_erase N _ hn₀]
    linarith
  · intro M
    set B : ℝ := ∑ n ∈ N.erase n₀, (|a n / (k - m * (n * π / L) ^ 2)| +
      |b n / (k - m * (n * π / L) ^ 2)|) with hB
    have hbound : ∀ t, |P t| ≤ B := fun t =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ =>
        (abs_add_le _ _).trans (add_le_add
          (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
          (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))))
    obtain ⟨t, ht⟩ := hRunb hab (M + B)
    refine ⟨t, ?_⟩
    have h3 := abs_sub (P t + bvpRes m (n₀ * π / L) (a n₀) (b n₀) t) (P t)
    have h4 : P t + bvpRes m (n₀ * π / L) (a n₀) (b n₀) t - P t = bvpRes m (n₀ * π / L) (a n₀) (b n₀) t :=
      by ring
    rw [h4] at h3
    linarith [hbound t]

/-! ## Insulated ends: the cosine series tends to its average (DE-142) -/

/-- **Heat equation with insulated ends, long-time limit (DE-142).** For `k > 0`, the cosine series solution
`a₀/2 + ∑_{n ∈ N} aₙ e^{-k(nπ/L)² t} cos(nπx/L)` (with `N` a finite set of positive integers) tends to the
constant `a₀/2` as `t → ∞`, at each point `x`.  (The series is the `heatCosSum` of `heat_neumann_series`
with the constant term `n = 0` carrying the coefficient `a₀/2`.) -/
@[kb "lebldiffyqs2026" "Example 4.6.3, p. 239"]
theorem heat_neumann_tendsto_average {k L : ℝ} (hk : 0 < k) (hL : L ≠ 0) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (a : ℕ → ℝ) (x : ℝ) :
    Tendsto (fun t => heatCosSum k L (fun n => if n = 0 then a 0 / 2 else a n) (insert 0 N) x t)
      atTop (𝓝 (a 0 / 2)) := by
  have h0 : 0 ∉ N := fun h => (lt_irrefl 0 (hN 0 h))
  have e : (fun t => heatCosSum k L (fun n => if n = 0 then a 0 / 2 else a n) (insert 0 N) x t)
      = fun t => a 0 / 2 + ∑ n ∈ N, (if n = 0 then a 0 / 2 else a n) *
        (exp (-(k * (n * π / L) ^ 2) * t) * cos (n * π / L * x)) := by
    funext t
    unfold heatCosSum
    rw [Finset.sum_insert h0]
    simp
  rw [e]
  have hsum : Tendsto (fun t => ∑ n ∈ N, (if n = 0 then a 0 / 2 else a n) *
      (exp (-(k * (n * π / L) ^ 2) * t) * cos (n * π / L * x))) atTop (𝓝 0) := by
    have := tendsto_finsetSum N (f := fun n t => (if n = 0 then a 0 / 2 else a n) *
      (exp (-(k * (n * π / L) ^ 2) * t) * cos (n * π / L * x))) (a := fun _ => (0 : ℝ))
      (fun n hn => by
        have hn' : (0 : ℝ) < n := by exact_mod_cast hN n hn
        have hc : 0 < k * (n * π / L) ^ 2 := by
          have : (n * π / L) ≠ 0 := by positivity
          positivity
        have h1 : Tendsto (fun t => exp (-(k * (n * π / L) ^ 2) * t)) atTop (𝓝 0) := by
          refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (tendsto_id.const_mul_atTop hc)).congr fun t => ?_
          simp [neg_mul]
        simpa using (h1.mul_const (cos (n * π / L * x))).const_mul
          (if n = 0 then a 0 / 2 else a n))
    simpa using this
  simpa using hsum.const_add (a 0 / 2)

/-! ## The converse of d'Alembert's solution (DE-146) -/

lemma bvp_partial_t {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x t : ℝ) :
    deriv (fun s => G (x, s)) t = fderiv ℝ G (x, t) (0, 1) :=
  ((hG (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id' t))).deriv

lemma bvp_partial_x {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x t : ℝ) :
    deriv (fun s => G (s, t)) x = fderiv ℝ G (x, t) (1, 0) :=
  ((hG (x, t)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id' x).prodMk (hasDerivAt_const x t))).deriv

/-- A `C¹` function annihilated by the transport operator `∂ₜ + c ∂ₓ` is constant along the lines
`x - c t = const`. -/
lemma bvp_transport {v : ℝ × ℝ → ℝ} (hv : Differentiable ℝ v) (c : ℝ)
    (h : ∀ p, fderiv ℝ v p (c, 1) = 0) (x t : ℝ) : v (x, t) = v (x - c * t, 0) := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (x - c * t + c * s, s)) (c, 1) s := fun s =>
    ((((hasDerivAt_id' s).const_mul c).const_add (x - c * t)).prodMk (hasDerivAt_id' s)).congr_deriv
      (by simp)
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => v (x - c * t + c * s, s)) 0 s := fun s => by
    have := (hv (x - c * t + c * s, s)).hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (x - c * t + c * s, s)) s (hline s)
    rw [h] at this
    exact this
  have := is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) t 0
  simp only [mul_zero, add_zero, sub_add_cancel] at this
  exact this

lemma bvp_fderiv_apply {Y : ℝ × ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (v w p : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ Y q v) p w = fderiv ℝ (fderiv ℝ Y) p w v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ Y) p :=
    ((hY.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) p
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

lemma bvp_symm {Y : ℝ × ℝ → ℝ} (hY : ContDiff ℝ 2 Y) (p v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ Y) p v w = fderiv ℝ (fderiv ℝ Y) p w v :=
  (ContDiffAt.isSymmSndFDerivAt (hY.contDiffAt (x := p))
    (by simp [minSmoothness_of_isRCLikeNormedField])) v w

lemma bvp_decomp (L : ℝ × ℝ →L[ℝ] ℝ) (c d : ℝ) : L (c, d) = c * L (1, 0) + d * L (0, 1) := by
  have : ((c, d) : ℝ × ℝ) = c • ((1, 0) : ℝ × ℝ) + d • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [this, map_add, map_smul, map_smul]
  simp

/-- **General solution of the wave equation, converse (DE-146).** If `y(x,t)` is a `C²` function on the
plane with `y_tt = a² y_xx` (`a ≠ 0`), then `y(x,t) = F(x + a t) + G(x - a t)` for some `C²` functions
`F, G` (the characteristic coordinates `ξ = x + a t`, `η = x - a t` make `y_ξη = 0`). -/
@[kb "lebldiffyqs2026" "§4.8 characteristic coordinates, p. 252"]
theorem wave_general_solution_converse {a : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ → ℝ}
    (hy : ContDiff ℝ 2 (fun p : ℝ × ℝ => y p.1 p.2)) (hwave : WaveEq a y) :
    ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧
      ∀ x t, y x t = F (x + a * t) + G (x - a * t) := by
  set Y : ℝ × ℝ → ℝ := fun p => y p.1 p.2 with hYdef
  have hY : ContDiff ℝ 2 Y := hy
  have hYd : Differentiable ℝ Y := hY.differentiable (by norm_num)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ Y) := hY.fderiv_right (by norm_num)
  set Dx : ℝ × ℝ → ℝ := fun q => fderiv ℝ Y q (1, 0) with hDx
  set Dt : ℝ × ℝ → ℝ := fun q => fderiv ℝ Y q (0, 1) with hDt
  have hDx1 : ContDiff ℝ 1 Dx := hF1.clm_apply contDiff_const
  have hDt1 : ContDiff ℝ 1 Dt := hF1.clm_apply contDiff_const
  have hDxd : Differentiable ℝ Dx := hDx1.differentiable (by norm_num)
  have hDtd : Differentiable ℝ Dt := hDt1.differentiable (by norm_num)
  -- the wave equation in terms of directional derivatives
  have hW : ∀ q : ℝ × ℝ, fderiv ℝ Dt q (0, 1) = a ^ 2 * fderiv ℝ Dx q (1, 0) := by
    rintro ⟨x, t⟩
    have h := hwave x t
    have e1 : (fun s => deriv (fun s => y x s) s) = fun s => Dt (x, s) :=
      funext fun s => bvp_partial_t hYd x s
    have e2 : (fun ξ => deriv (fun ξ => y ξ t) ξ) = fun ξ => Dx (ξ, t) :=
      funext fun ξ => bvp_partial_x hYd ξ t
    rw [e1, e2, bvp_partial_t hDtd, bvp_partial_x hDxd] at h
    exact h
  have hS : ∀ q : ℝ × ℝ, fderiv ℝ Dt q (1, 0) = fderiv ℝ Dx q (0, 1) := fun q => by
    have e1 : fderiv ℝ Dt q (1, 0) = fderiv ℝ (fderiv ℝ Y) q (1, 0) (0, 1) :=
      bvp_fderiv_apply hY (0, 1) (1, 0) q
    have e2 : fderiv ℝ Dx q (0, 1) = fderiv ℝ (fderiv ℝ Y) q (0, 1) (1, 0) :=
      bvp_fderiv_apply hY (1, 0) (0, 1) q
    rw [e1, e2]
    exact bvp_symm hY q _ _
  -- `w = y_t + a y_x` is constant along `x + a t = const`
  set w : ℝ × ℝ → ℝ := fun q => Dt q + a * Dx q with hw
  have hw1 : ContDiff ℝ 1 w := hDt1.add (contDiff_const.mul hDx1)
  have hwd : Differentiable ℝ w := hw1.differentiable (by norm_num)
  have hwf : ∀ q, fderiv ℝ w q (-a, 1) = 0 := fun q => by
    have e : fderiv ℝ w q = fderiv ℝ Dt q + a • fderiv ℝ Dx q := by
      exact ((hDtd q).hasFDerivAt.add ((hDxd q).hasFDerivAt.const_mul a)).fderiv
    rw [e]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [bvp_decomp (fderiv ℝ Dt q), bvp_decomp (fderiv ℝ Dx q), hW q, hS q]
    ring
  have hwt : ∀ x t, w (x, t) = w (x + a * t, 0) := fun x t => by
    have h := bvp_transport hwd (-a) hwf x t
    have e : x - -a * t = x + a * t := by ring
    rw [e] at h
    exact h
  set h : ℝ → ℝ := fun ξ => w (ξ, 0) with hh
  have hh1 : ContDiff ℝ 1 h := hw1.comp (contDiff_id.prodMk contDiff_const)
  have hhd : Differentiable ℝ h := hh1.differentiable (by norm_num)
  have hhc : Continuous h := hh1.continuous
  set F : ℝ → ℝ := fun ξ => ∫ s in (0 : ℝ)..ξ, h s / (2 * a) with hF
  have hF1' : ∀ ξ, HasDerivAt F (h ξ / (2 * a)) ξ := fun ξ =>
    (Continuous.integral_hasStrictDerivAt (hhc.div_const (2 * a)) 0 ξ).hasDerivAt
  have hF2 : ContDiff ℝ 2 F :=
    bvp_contDiff_two hF1' (d2 := fun ξ => deriv h ξ / (2 * a))
      (fun ξ => (hhd ξ).hasDerivAt.div_const _) ((hh1.continuous_deriv le_rfl).div_const _)
  have hℓ : ∀ q : ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => q.1 + a * q.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ) + a • (ContinuousLinearMap.snd ℝ ℝ ℝ)) q := fun q =>
    hasFDerivAt_fst.add (hasFDerivAt_snd.const_mul a)
  have hv : ∀ q : ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => Y q - F (q.1 + a * q.2))
      (fderiv ℝ Y q - (h (q.1 + a * q.2) / (2 * a)) •
        ((ContinuousLinearMap.fst ℝ ℝ ℝ) + a • (ContinuousLinearMap.snd ℝ ℝ ℝ))) q := fun q =>
    (hYd q).hasFDerivAt.sub ((hF1' (q.1 + a * q.2)).comp_hasFDerivAt (f := fun q : ℝ × ℝ => q.1 + a * q.2) q (hℓ q))
  have hvf : ∀ q : ℝ × ℝ, fderiv ℝ (fun q : ℝ × ℝ => Y q - F (q.1 + a * q.2)) q (a, 1) = 0 :=
    fun q => by
      rw [(hv q).fderiv]
      have h1 := bvp_decomp (fderiv ℝ Y q) a 1
      have h2 : w q = h (q.1 + a * q.2) := by
        obtain ⟨x, t⟩ := q
        exact hwt x t
      have h3 : w q = fderiv ℝ Y q (0, 1) + a * fderiv ℝ Y q (1, 0) := rfl
      have e : h (q.1 + a * q.2) / (2 * a) * (a + a * 1) = h (q.1 + a * q.2) := by
        field_simp; ring
      simp only [sub_apply, smul_apply,
        add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul]
      rw [h1, e]
      linarith
  have hvd : Differentiable ℝ (fun q : ℝ × ℝ => Y q - F (q.1 + a * q.2)) := fun q =>
    (hv q).differentiableAt
  refine ⟨F, fun η => y η 0 - F η, hF2, ?_, fun x t => ?_⟩
  · exact (hY.comp (contDiff_id.prodMk contDiff_const)).sub hF2
  · have := bvp_transport hvd a hvf x t
    simp only [mul_zero, add_zero] at this
    have e : Y (x, t) = y x t := rfl
    have e' : Y (x - a * t, 0) = y (x - a * t) 0 := rfl
    linarith

end UndergradKB.DifferentialEquations
