import UndergradKB.DifferentialEquations.PDE
import UndergradKB.DifferentialEquations.SecondOrderLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-! # Regular Sturm-Liouville problems (Lebl §5.1)

Lebl's problem (5.2) is `(p y')' - q y + λ r y = 0` on `a < x < b` with `α₁ y(a) - α₂ y'(a) = 0` and
`β₁ y(b) + β₂ y'(b) = 0`.  We bundle the data of a *regular* problem (continuity, `p, r > 0`, `q ≥ 0`,
`α, β ≥ 0`, neither coefficient pair zero, the book's sign conventions) in the structure `RegularSL`, and
we call `y` a solution if it is `C²` on the line and satisfies the equation on `[a, b]` and both boundary
conditions (a harmless strengthening of "twice differentiable on `[a, b]`").  `p` is assumed `C¹` on all of
`ℝ` (equivalent to the book's "`p, p'` continuous on `[a, b]`" after extension).

Proved: the Dirichlet problem and the Robin problem are instances (DE-153); weighted inner product and
orthogonality of eigenfunctions for distinct eigenvalues (DE-155); the eigenspace of each eigenvalue is
one-dimensional and eigenvalues are `≥ 0` (the two "unique up to a multiple" and "Moreover" parts of
Theorem 5.1.1, DE-154); uniqueness half of the Fredholm alternative (DE-157).  Not proved: existence of
infinitely many eigenvalues tending to infinity (needs the spectral theorem for the compact Green
operator) and existence in the Fredholm alternative (needs the Green's function). -/

namespace UndergradKB.DifferentialEquations

open Set intervalIntegral

/-- Data of a regular Sturm-Liouville problem on `[a, b]` (Lebl §5.1, (5.2) with the regularity conditions
stated after Theorem 5.1.1).  (DE-153) -/
structure RegularSL where
  a : ℝ
  b : ℝ
  hab : a < b
  p : ℝ → ℝ
  q : ℝ → ℝ
  r : ℝ → ℝ
  α₁ : ℝ
  α₂ : ℝ
  β₁ : ℝ
  β₂ : ℝ
  p_C1 : ContDiff ℝ 1 p
  q_cont : ContinuousOn q (Icc a b)
  r_cont : ContinuousOn r (Icc a b)
  p_pos : ∀ t ∈ Icc a b, 0 < p t
  r_pos : ∀ t ∈ Icc a b, 0 < r t
  q_nonneg : ∀ t ∈ Icc a b, 0 ≤ q t
  α₁_nonneg : 0 ≤ α₁
  α₂_nonneg : 0 ≤ α₂
  β₁_nonneg : 0 ≤ β₁
  β₂_nonneg : 0 ≤ β₂
  α_ne : ¬ (α₁ = 0 ∧ α₂ = 0)
  β_ne : ¬ (β₁ = 0 ∧ β₂ = 0)

namespace RegularSL

variable (S : RegularSL)

/-- `y` solves `(p y')' - q y + λ r y = f` on `[a, b]` together with the boundary conditions
`α₁ y(a) - α₂ y'(a) = 0`, `β₁ y(b) + β₂ y'(b) = 0`.  With `f = 0` this is the homogeneous problem (5.2),
with `f` continuous it is the nonhomogeneous problem of Theorem 5.1.3. -/
def IsSolution (l : ℝ) (f : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 y ∧
  (∀ t ∈ Icc S.a S.b,
    deriv (fun t => S.p t * deriv y t) t - S.q t * y t + l * S.r t * y t = f t) ∧
  S.α₁ * y S.a - S.α₂ * deriv y S.a = 0 ∧ S.β₁ * y S.b + S.β₂ * deriv y S.b = 0

/-- An eigenfunction for `λ`: a nontrivial solution of the homogeneous problem. -/
def IsEigenfunction (l : ℝ) (y : ℝ → ℝ) : Prop :=
  S.IsSolution l 0 y ∧ ∃ t ∈ Icc S.a S.b, y t ≠ 0

/-- `λ` is an eigenvalue when it has an eigenfunction. -/
def IsEigenvalue (l : ℝ) : Prop := ∃ y, S.IsEigenfunction l y

/-- The weighted inner product `⟨f, g⟩_r = ∫_a^b f g r` (Lebl §5.1).  (DE-155) -/
noncomputable def wInner (f g : ℝ → ℝ) : ℝ := ∫ t in S.a..S.b, f t * g t * S.r t

/-- `f` and `g` are orthogonal with respect to the weight `r`. (DE-155) -/
def WOrthogonal (f g : ℝ → ℝ) : Prop := S.wInner f g = 0

end RegularSL

/-! ## Instances: the Dirichlet and Robin problems (Examples 5.1.2, 5.1.3) -/

/-- **The Dirichlet problem `y'' + λ y = 0`, `y(0) = y(L) = 0` is a regular Sturm-Liouville problem
(DE-153).**  Here `p = 1`, `q = 0`, `r = 1`, `α = (1, 0)`, `β = (1, 0)`. -/
@[kb "lebldiffyqs2026" "Example 5.1.2, p. 275"]
def dirichletSL {L : ℝ} (hL : 0 < L) : RegularSL where
  a := 0
  b := L
  hab := hL
  p := fun _ => 1
  q := fun _ => 0
  r := fun _ => 1
  α₁ := 1
  α₂ := 0
  β₁ := 1
  β₂ := 0
  p_C1 := contDiff_const
  q_cont := continuousOn_const
  r_cont := continuousOn_const
  p_pos := fun _ _ => one_pos
  r_pos := fun _ _ => one_pos
  q_nonneg := fun _ _ => le_rfl
  α₁_nonneg := zero_le_one
  α₂_nonneg := le_rfl
  β₁_nonneg := zero_le_one
  β₂_nonneg := le_rfl
  α_ne := by simp
  β_ne := by simp

/-- **The Robin example `y'' + λ y = 0`, `h y(0) - y'(0) = 0`, `y'(1) = 0` (`h > 0`) is a regular
Sturm-Liouville problem (DE-153).**  Here `p = r = 1`, `q = 0`, `α = (h, 1)`, `β = (0, 1)`. -/
@[kb "lebldiffyqs2026" "Example 5.1.3, p. 275"]
def robinSL {h : ℝ} (hh : 0 < h) : RegularSL where
  a := 0
  b := 1
  hab := one_pos
  p := fun _ => 1
  q := fun _ => 0
  r := fun _ => 1
  α₁ := h
  α₂ := 1
  β₁ := 0
  β₂ := 1
  p_C1 := contDiff_const
  q_cont := continuousOn_const
  r_cont := continuousOn_const
  p_pos := fun _ _ => one_pos
  r_pos := fun _ _ => one_pos
  q_nonneg := fun _ _ => le_rfl
  α₁_nonneg := hh.le
  α₂_nonneg := zero_le_one
  β₁_nonneg := le_rfl
  β₂_nonneg := zero_le_one
  α_ne := by simp [hh.ne']
  β_ne := by simp

/-- The Dirichlet instance has the expected equation: `y` solves it iff `y'' + λ y = 0` on `[0, L]` with
`y(0) = y(L) = 0`. -/
theorem dirichletSL_isSolution_iff {L : ℝ} (hL : 0 < L) (l : ℝ) (y : ℝ → ℝ) :
    (dirichletSL hL).IsSolution l 0 y ↔ ContDiff ℝ 2 y ∧
      (∀ t ∈ Icc 0 L, deriv (deriv y) t + l * y t = 0) ∧ y 0 = 0 ∧ y L = 0 := by
  unfold RegularSL.IsSolution
  simp [dirichletSL]

/-! ## Boundary-condition algebra -/

lemma wronskian_zero_of_bc {c₁ c₂ u₁ v₁ u₂ v₂ : ℝ} (hc : ¬ (c₁ = 0 ∧ c₂ = 0))
    (h₁ : c₁ * u₁ + c₂ * v₁ = 0) (h₂ : c₁ * u₂ + c₂ * v₂ = 0) : v₁ * u₂ - u₁ * v₂ = 0 := by
  have e1 : c₁ * (v₁ * u₂ - u₁ * v₂) = 0 := by linear_combination v₁ * h₂ - v₂ * h₁
  have e2 : c₂ * (v₁ * u₂ - u₁ * v₂) = 0 := by linear_combination u₂ * h₁ - u₁ * h₂
  by_contra hW
  exact hc ⟨(mul_eq_zero.1 e1).resolve_right hW, (mul_eq_zero.1 e2).resolve_right hW⟩

lemma nonpos_of_bc {c₁ c₂ u v : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (hc : ¬ (c₁ = 0 ∧ c₂ = 0))
    (h : c₁ * u + c₂ * v = 0) : u * v ≤ 0 := by
  rcases h2.eq_or_lt with h2' | h2'
  · have h1' : 0 < c₁ := by
      rcases h1.eq_or_lt with h | h
      · exact absurd ⟨h.symm, h2'.symm⟩ hc
      · exact h
    have : u = 0 := by
      have : c₁ * u = 0 := by rw [← h2'] at h; linarith
      exact (mul_eq_zero.1 this).resolve_left h1'.ne'
    simp [this]
  · by_contra hh
    push Not at hh
    have := mul_pos h2' hh
    have e : c₂ * (u * v) = -(c₁ * u ^ 2) := by linear_combination u * h
    nlinarith [mul_nonneg h1 (sq_nonneg u)]

lemma exists_subinterval {a b t₀ : ℝ} (hab : a < b) {y : ℝ → ℝ} (hy : Continuous y)
    (ht : t₀ ∈ Icc a b) (h : y t₀ ≠ 0) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ b ∧ ∀ t ∈ Ioo c d, y t ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_ne_fun hy continuous_const) t₀ h
  have key : ∀ t, |t - t₀| < ε → y t ≠ 0 := fun t ht' => by
    have := hball (by simpa [Real.dist_eq] using ht')
    simpa using this
  by_cases hb : t₀ < b
  · refine ⟨t₀, min (t₀ + ε / 2) b, ht.1, lt_min (by linarith) hb, min_le_right _ _, ?_⟩
    intro t htt
    apply key
    have h1 := htt.1
    have h2 := lt_of_lt_of_le htt.2 (min_le_left _ _)
    rw [abs_lt]; constructor <;> linarith
  · have hbt : t₀ = b := le_antisymm ht.2 (not_lt.1 hb)
    subst hbt
    refine ⟨max (t₀ - ε / 2) a, t₀, le_max_right _ _, max_lt (by linarith) hab, le_rfl, ?_⟩
    intro t htt
    apply key
    have h1 := lt_of_le_of_lt (le_max_left _ _) htt.1
    have h2 := htt.2
    rw [abs_lt]; constructor <;> linarith

/-! ## Orthogonality (Theorem 5.1.2) -/

namespace RegularSL

variable (S : RegularSL)

lemma bc_wronskian_a {y₁ y₂ : ℝ → ℝ} (h₁ : S.α₁ * y₁ S.a - S.α₂ * deriv y₁ S.a = 0)
    (h₂ : S.α₁ * y₂ S.a - S.α₂ * deriv y₂ S.a = 0) :
    deriv y₁ S.a * y₂ S.a - y₁ S.a * deriv y₂ S.a = 0 :=
  wronskian_zero_of_bc (c₁ := S.α₁) (c₂ := -S.α₂)
    (fun h => S.α_ne ⟨h.1, by linarith [h.2]⟩) (by linear_combination h₁) (by linear_combination h₂)

lemma bc_wronskian_b {y₁ y₂ : ℝ → ℝ} (h₁ : S.β₁ * y₁ S.b + S.β₂ * deriv y₁ S.b = 0)
    (h₂ : S.β₁ * y₂ S.b + S.β₂ * deriv y₂ S.b = 0) :
    deriv y₁ S.b * y₂ S.b - y₁ S.b * deriv y₂ S.b = 0 :=
  wronskian_zero_of_bc S.β_ne h₁ h₂

/-- **Orthogonality of eigenfunctions of a regular Sturm-Liouville problem (DE-155).**  Eigenfunctions
for distinct eigenvalues are orthogonal with respect to the weight `r`: `∫_a^b y₁ y₂ r = 0`.  (Both
boundary conditions force the boundary term of the Lagrange identity to vanish.) -/
@[kb "lebldiffyqs2026" "Theorem 5.1.2, p. 277"]
theorem orthogonality {l₁ l₂ : ℝ} {y₁ y₂ : ℝ → ℝ} (h₁ : S.IsEigenfunction l₁ y₁)
    (h₂ : S.IsEigenfunction l₂ y₂) (hne : l₁ ≠ l₂) : S.WOrthogonal y₁ y₂ := by
  obtain ⟨⟨c1, e1, a1, b1⟩, -⟩ := h₁
  obtain ⟨⟨c2, e2, a2, b2⟩, -⟩ := h₂
  have wa := S.bc_wronskian_a a1 a2
  have wb := S.bc_wronskian_b b1 b2
  exact sl_orthogonality_of_boundary S.hab.le S.p_C1 (q := fun t => - S.q t) (r := S.r) c1 c2
    (fun t ht => by
      have := e1 t ht
      simp only [Pi.zero_apply] at this
      linear_combination this)
    (fun t ht => by
      have := e2 t ht
      simp only [Pi.zero_apply] at this
      linear_combination this)
    (by rw [wa, wb]; simp) hne

/-- The weighted inner product is symmetric. -/
theorem wInner_comm (f g : ℝ → ℝ) : S.wInner f g = S.wInner g f := by
  unfold wInner
  exact intervalIntegral.integral_congr fun t _ => by ring

/-! ## Eigenspaces are one-dimensional; eigenvalues are nonnegative (Theorem 5.1.1, partial) -/

lemma solvesLin2_of_eq {l : ℝ} {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (he : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv y t) t - S.q t * y t + l * S.r t * y t = 0) :
    SolvesLin2 (fun t => deriv S.p t / S.p t) (fun t => (l * S.r t - S.q t) / S.p t) 0
      (Icc S.a S.b) y := by
  intro t ht
  have d1 : DifferentiableAt ℝ y t := (hy.differentiable (by norm_num)) t
  have d2 : DifferentiableAt ℝ (deriv y) t :=
    ((contDiff_deriv_aux hy).differentiable one_ne_zero) t
  have dp : DifferentiableAt ℝ S.p t := (S.p_C1.differentiable one_ne_zero) t
  refine ⟨d1, d2, ?_⟩
  have hd : deriv (fun t => S.p t * deriv y t) t
      = deriv S.p t * deriv y t + S.p t * deriv (deriv y) t :=
    (dp.hasDerivAt.mul d2.hasDerivAt).deriv
  have this := he t ht
  rw [hd] at this
  have hp := S.p_pos t ht
  have hA : S.p t * (deriv S.p t / S.p t) = deriv S.p t := by field_simp
  have hB : S.p t * ((l * S.r t - S.q t) / S.p t) = l * S.r t - S.q t := by field_simp
  have key : S.p t * (deriv (deriv y) t + deriv S.p t / S.p t * deriv y t
      + (l * S.r t - S.q t) / S.p t * y t) = 0 := by
    linear_combination this + deriv y t * hA + y t * hB
  simpa [hp.ne'] using key

lemma continuousOn_coeffs {l : ℝ} :
    ContinuousOn (fun t => deriv S.p t / S.p t) (Icc S.a S.b) ∧
    ContinuousOn (fun t => (l * S.r t - S.q t) / S.p t) (Icc S.a S.b) :=
  ⟨((S.p_C1.continuous_deriv le_rfl).continuousOn).div S.p_C1.continuous.continuousOn
      (fun t ht => (S.p_pos t ht).ne'),
   ((continuousOn_const.mul S.r_cont).sub S.q_cont).div S.p_C1.continuous.continuousOn
      (fun t ht => (S.p_pos t ht).ne')⟩

lemma eq_const_mul {l : ℝ} {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y) (c : ℝ)
    (he : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv y t) t - S.q t * y t + l * S.r t * y t = 0) :
    ∀ t ∈ Icc S.a S.b, deriv (fun t => S.p t * deriv (fun s => c * y s) t) t
      - S.q t * (c * y t) + l * S.r t * (c * y t) = 0 := by
  intro t ht
  have d1 : ∀ s, DifferentiableAt ℝ y s := fun s => (hy.differentiable (by norm_num)) s
  have hder : deriv (fun s => c * y s) = fun s => c * deriv y s := by
    funext s; exact deriv_const_mul c (d1 s)
  have hfun : (fun t => S.p t * deriv (fun s => c * y s) t) = fun t => c * (S.p t * deriv y t) := by
    funext s; rw [hder]; ring
  have d2 : DifferentiableAt ℝ (deriv y) t :=
    ((contDiff_deriv_aux hy).differentiable one_ne_zero) t
  have dp : DifferentiableAt ℝ S.p t := (S.p_C1.differentiable one_ne_zero) t
  have hdd : DifferentiableAt ℝ (fun t => S.p t * deriv y t) t := dp.mul d2
  rw [hfun, deriv_const_mul c hdd]
  linear_combination c * he t ht

lemma eq_zero_of_initial {l : ℝ} {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (he : ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv y t) t - S.q t * y t + l * S.r t * y t = 0)
    (h0 : y S.a = 0) (h1 : deriv y S.a = 0) : ∀ t ∈ Icc S.a S.b, y t = 0 := by
  have hs := S.solvesLin2_of_eq hy he
  have hz : SolvesLin2 (fun t => deriv S.p t / S.p t) (fun t => (l * S.r t - S.q t) / S.p t) 0
      (Icc S.a S.b) (fun _ => 0) := fun t _ => ⟨differentiableAt_const _, by simp, by simp⟩
  have hc := S.continuousOn_coeffs (l := l)
  exact lin2_unique ordConnected_Icc hc.1 hc.2 hs hz (left_mem_Icc.2 S.hab.le) (by simpa using h0)
    (by simpa using h1)

/-- **Eigenfunctions are unique up to a scalar multiple (DE-154, uniqueness part of Theorem 5.1.1).**
If `y₁` is an eigenfunction for `λ` and `y₂` is any solution of the homogeneous problem for the same `λ`
then `y₂ = c y₁` on `[a, b]` for some constant `c`: the eigenspace of each eigenvalue is
one-dimensional.  (The existence of infinitely many eigenvalues tending to `+∞` is not formalized.) -/
@[kb "lebldiffyqs2026" "Theorem 5.1.1, p. 275"]
theorem eigenfunction_unique {l : ℝ} {y₁ y₂ : ℝ → ℝ} (h₁ : S.IsEigenfunction l y₁)
    (h₂ : S.IsSolution l 0 y₂) : ∃ c : ℝ, ∀ t ∈ Icc S.a S.b, y₂ t = c * y₁ t := by
  obtain ⟨⟨c1, e1, a1, b1⟩, t₀, ht₀, hne⟩ := h₁
  obtain ⟨c2, e2, a2, b2⟩ := h₂
  simp only [Pi.zero_apply] at e1 e2
  have wa := S.bc_wronskian_a a1 a2
  -- the initial data of `y₁` at `a` are not both zero
  have hnz : ¬ (y₁ S.a = 0 ∧ deriv y₁ S.a = 0) := fun h =>
    hne (S.eq_zero_of_initial c1 e1 h.1 h.2 t₀ ht₀)
  -- the initial data of `y₂` at `a` are a multiple of those of `y₁`
  obtain ⟨c, hc0, hc1⟩ : ∃ c : ℝ, y₂ S.a = c * y₁ S.a ∧ deriv y₂ S.a = c * deriv y₁ S.a := by
    by_cases hu : y₁ S.a = 0
    · have hv : deriv y₁ S.a ≠ 0 := fun hv => hnz ⟨hu, hv⟩
      refine ⟨deriv y₂ S.a / deriv y₁ S.a, ?_, ?_⟩
      · have : y₂ S.a = 0 := by
          rw [hu] at wa
          simpa [hv] using wa
        simp [this, hu]
      · field_simp
    · refine ⟨y₂ S.a / y₁ S.a, by field_simp, ?_⟩
      field_simp
      linear_combination -wa
  refine ⟨c, ?_⟩
  have hs2 := S.solvesLin2_of_eq c2 e2
  have hs1 := S.solvesLin2_of_eq (contDiff_const.mul c1) (S.eq_const_mul c1 c e1)
  have hco := S.continuousOn_coeffs (l := l)
  have d1 : DifferentiableAt ℝ y₁ S.a := (c1.differentiable (by norm_num)) S.a
  exact lin2_unique ordConnected_Icc hco.1 hco.2 hs2 hs1 (left_mem_Icc.2 S.hab.le) (by simpa using hc0)
    (by rw [deriv_const_mul c d1]; exact hc1)

lemma integral_r_sq_pos {y : ℝ → ℝ} (hy : Continuous y) {t₀ : ℝ} (ht : t₀ ∈ Icc S.a S.b)
    (h : y t₀ ≠ 0) : 0 < ∫ t in S.a..S.b, S.r t * y t ^ 2 := by
  obtain ⟨c, d, hac, hcd, hdb, hpos⟩ := exists_subinterval S.hab hy ht h
  have hcont : ContinuousOn (fun t => S.r t * y t ^ 2) (Icc S.a S.b) :=
    S.r_cont.mul (hy.pow 2).continuousOn
  have hsub : Icc c d ⊆ Icc S.a S.b := Icc_subset_Icc hac hdb
  have hin : 0 < ∫ t in c..d, S.r t * y t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) hcd
    · exact (hcont.mono hsub).intervalIntegrable_of_Icc hcd.le
    · have h1 := S.r_pos t (hsub ⟨ht.1.le, ht.2.le⟩)
      have h2 := hpos t ht
      positivity
  refine lt_of_lt_of_le hin ?_
  refine intervalIntegral.integral_mono_interval hac hcd.le hdb ?_
    (hcont.intervalIntegrable_of_Icc S.hab.le)
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  have := S.r_pos t ⟨ht.1.le, ht.2⟩
  show 0 ≤ S.r t * y t ^ 2
  positivity

/-- **Eigenvalues of a regular Sturm-Liouville problem are nonnegative (DE-154, the "moreover" part of
Theorem 5.1.1).**  Proof by the Rayleigh quotient: multiply the equation by `y` and integrate by parts,
`λ ∫ r y² = ∫ p y'² + ∫ q y² + (boundary terms ≥ 0)`. -/
@[kb "lebldiffyqs2026" "Theorem 5.1.1, p. 275"]
theorem eigenvalue_nonneg {l : ℝ} {y : ℝ → ℝ} (h : S.IsEigenfunction l y) : 0 ≤ l := by
  obtain ⟨⟨hy, he, ha, hb⟩, t₀, ht₀, hne⟩ := h
  simp only [Pi.zero_apply] at he
  have d1 := contDiff_deriv_aux hy
  have P1 : ContDiff ℝ 1 (fun t => S.p t * deriv y t) := S.p_C1.mul d1
  have hyd : ∀ t, HasDerivAt y (deriv y t) t := fun t =>
    ((hy.differentiable (by norm_num)) t).hasDerivAt
  have hPd : ∀ t, HasDerivAt (fun t => S.p t * deriv y t)
      (deriv (fun t => S.p t * deriv y t) t) t := fun t =>
    ((P1.differentiable one_ne_zero) t).hasDerivAt
  have hF : ∀ t, HasDerivAt (fun t => y t * (S.p t * deriv y t))
      (deriv y t * (S.p t * deriv y t) + y t * deriv (fun t => S.p t * deriv y t) t) t :=
    fun t => (hyd t).mul (hPd t)
  have cy := hy.continuous
  have cd := d1.continuous
  have cp := S.p_C1.continuous
  have cD := P1.continuous_deriv le_rfl
  have hcF : Continuous (fun t => deriv y t * (S.p t * deriv y t)
      + y t * deriv (fun t => S.p t * deriv y t) t) := by fun_prop
  have hint := integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hcF.intervalIntegrable S.a S.b)
  have iA : IntervalIntegrable (fun t => S.p t * deriv y t ^ 2) MeasureTheory.volume S.a S.b :=
    (by fun_prop : Continuous (fun t => S.p t * deriv y t ^ 2)).intervalIntegrable _ _
  have iB : IntervalIntegrable (fun t => S.q t * y t ^ 2) MeasureTheory.volume S.a S.b :=
    (S.q_cont.mul (cy.pow 2).continuousOn).intervalIntegrable_of_Icc S.hab.le
  have iC : IntervalIntegrable (fun t => S.r t * y t ^ 2) MeasureTheory.volume S.a S.b :=
    (S.r_cont.mul (cy.pow 2).continuousOn).intervalIntegrable_of_Icc S.hab.le
  have hcongr : ∫ t in S.a..S.b, (deriv y t * (S.p t * deriv y t)
      + y t * deriv (fun t => S.p t * deriv y t) t)
      = ∫ t in S.a..S.b, ((S.p t * deriv y t ^ 2 + S.q t * y t ^ 2) - l * (S.r t * y t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le S.hab.le] at ht
    linear_combination (y t) * he t ht
  rw [hcongr, intervalIntegral.integral_sub (iA.add iB) (iC.const_mul l),
    intervalIntegral.integral_add iA iB, intervalIntegral.integral_const_mul] at hint
  have hA : 0 ≤ ∫ t in S.a..S.b, S.p t * deriv y t ^ 2 :=
    intervalIntegral.integral_nonneg S.hab.le fun t ht => by
      have := S.p_pos t ht
      positivity
  have hB : 0 ≤ ∫ t in S.a..S.b, S.q t * y t ^ 2 :=
    intervalIntegral.integral_nonneg S.hab.le fun t ht => by
      have := S.q_nonneg t ht
      positivity
  have hC := S.integral_r_sq_pos cy ht₀ hne
  have sb : y S.b * deriv y S.b ≤ 0 :=
    nonpos_of_bc S.β₁_nonneg S.β₂_nonneg S.β_ne hb
  have sa : y S.a * deriv y S.a ≥ 0 := by
    have := nonpos_of_bc (c₁ := S.α₁) (c₂ := S.α₂) (u := y S.a) (v := - deriv y S.a)
      S.α₁_nonneg S.α₂_nonneg S.α_ne (by linear_combination ha)
    linarith
  have pb := S.p_pos S.b (right_mem_Icc.2 S.hab.le)
  have pa := S.p_pos S.a (left_mem_Icc.2 S.hab.le)
  have fb : y S.b * (S.p S.b * deriv y S.b) ≤ 0 := by nlinarith
  have fa : y S.a * (S.p S.a * deriv y S.a) ≥ 0 := by nlinarith
  by_contra hl
  push Not at hl
  nlinarith [mul_neg_of_neg_of_pos hl hC]

/-! ## Fredholm alternative: uniqueness half (Theorem 5.1.3) -/

lemma IsSolution.sub {l : ℝ} {f g y z : ℝ → ℝ} (hy : S.IsSolution l f y) (hz : S.IsSolution l g z) :
    S.IsSolution l (fun t => f t - g t) (fun t => y t - z t) := by
  obtain ⟨hy2, he, ha, hb⟩ := hy
  obtain ⟨hz2, he', ha', hb'⟩ := hz
  have dy : ∀ s, DifferentiableAt ℝ y s := fun s => (hy2.differentiable (by norm_num)) s
  have dz : ∀ s, DifferentiableAt ℝ z s := fun s => (hz2.differentiable (by norm_num)) s
  have hder : deriv (fun s => y s - z s) = fun s => deriv y s - deriv z s := by
    funext s; exact deriv_sub (dy s) (dz s)
  have hfun : (fun t => S.p t * deriv (fun s => y s - z s) t)
      = fun t => S.p t * deriv y t - S.p t * deriv z t := by
    funext s; rw [hder]; ring
  have dpy : ∀ s, DifferentiableAt ℝ (fun t => S.p t * deriv y t) s := fun s =>
    ((S.p_C1.differentiable one_ne_zero) s).mul
      (((contDiff_deriv_aux hy2).differentiable one_ne_zero) s)
  have dpz : ∀ s, DifferentiableAt ℝ (fun t => S.p t * deriv z t) s := fun s =>
    ((S.p_C1.differentiable one_ne_zero) s).mul
      (((contDiff_deriv_aux hz2).differentiable one_ne_zero) s)
  refine ⟨hy2.sub hz2, fun t ht => ?_, ?_, ?_⟩
  · have hsub : deriv (fun t => S.p t * deriv y t - S.p t * deriv z t) t
        = deriv (fun t => S.p t * deriv y t) t - deriv (fun t => S.p t * deriv z t) t :=
      ((dpy t).hasDerivAt.sub (dpz t).hasDerivAt).deriv
    rw [hfun, hsub]
    have := he t ht
    have := he' t ht
    simp only
    linarith
  · have e1 : deriv (fun s => y s - z s) S.a = deriv y S.a - deriv z S.a := by
      rw [hder]
    simp only
    rw [e1]
    linear_combination ha - ha'
  · have e1 : deriv (fun s => y s - z s) S.b = deriv y S.b - deriv z S.b := by
      rw [hder]
    simp only
    rw [e1]
    linear_combination hb - hb'

/-- **Fredholm alternative, uniqueness half (DE-157).**  If `λ` is not an eigenvalue of the regular
Sturm-Liouville problem, the nonhomogeneous problem `(p y')' - q y + λ r y = f` with the same boundary
conditions has at most one solution.  (Existence of a solution for every continuous `f` needs the Green's
function and is not formalized.) -/
@[kb "lebldiffyqs2026" "Theorem 5.1.3, p. 278"]
theorem solution_unique_of_not_eigenvalue {l : ℝ} (hl : ¬ S.IsEigenvalue l) {f y z : ℝ → ℝ}
    (hy : S.IsSolution l f y) (hz : S.IsSolution l f z) : ∀ t ∈ Icc S.a S.b, y t = z t := by
  have hd := IsSolution.sub S hy hz
  have hd0 : S.IsSolution l 0 (fun t => y t - z t) := by
    have : (fun t => f t - f t) = (0 : ℝ → ℝ) := by funext t; simp
    rwa [this] at hd
  intro t ht
  by_contra hne
  exact hl ⟨fun t => y t - z t, hd0, t, ht, sub_ne_zero.2 hne⟩

end RegularSL

end UndergradKB.DifferentialEquations
