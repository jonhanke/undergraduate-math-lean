import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Nonlinear

/-! # Almost linear critical points with both eigenvalues in the left half plane are asymptotically stable

Lebl, *Notes on Diffy Qs*, §8.2, Table 8.1: at an almost linear critical point the behaviour of the linearization
decides stability.  We prove the stable rows of the table (asymptotically stable node and spiral): if the Jacobian
`J = [[a, b], [c, d]]` has trace `a + d < 0` and determinant `ad - bc > 0` (equivalently, both eigenvalues have
negative real part), the critical point is asymptotically stable for the nonlinear system.

Proof (Lyapunov's indirect method).  By Cayley-Hamilton, with `τ = a + d`, `Δ = ad - bc` and `B = J - τI`,
the quadratic form `V(v) = Δ|v|² + |Bv|²` satisfies `∇V · Jv = 2τΔ|v|²`.  Near the critical point the
nonlinear remainder is small compared with `|v|`, so `V' ≤ -κ V` along solutions, and a comparison argument
(`image_le_of_deriv_right_lt_deriv_boundary'`) gives `V(v(t)) ≤ W e^{-κt/2}`. -/

namespace UndergradKB.DifferentialEquations

open Filter Topology

/-- The Lyapunov function `V(u,v) = Δ (u² + v²) + ((bv - du)² + (cu - av)²)` of the matrix `[[a,b],[c,d]]`. -/
def lyapV (a b c d u v : ℝ) : ℝ :=
  (a * d - b * c) * (u ^ 2 + v ^ 2) + ((b * v - d * u) ^ 2 + (c * u - a * v) ^ 2)

/-- Half the `u`-partial derivative of `lyapV`. -/
def lyapP (a b c d u v : ℝ) : ℝ := (a * d - b * c + c ^ 2 + d ^ 2) * u - (a * c + b * d) * v

/-- Half the `v`-partial derivative of `lyapV`. -/
def lyapQ (a b c d u v : ℝ) : ℝ := -(a * c + b * d) * u + (a * d - b * c + a ^ 2 + b ^ 2) * v

lemma lyapV_hasDerivAt (a b c d : ℝ) {u v : ℝ → ℝ} {u' v' t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => lyapV a b c d (u s) (v s))
      (2 * (lyapP a b c d (u t) (v t) * u' + lyapQ a b c d (u t) (v t) * v')) t := by
  have h := (((hu.pow 2).add (hv.pow 2)).const_mul (a * d - b * c)).add
    ((((hv.const_mul b).sub (hu.const_mul d)).pow 2).add (((hu.const_mul c).sub (hv.const_mul a)).pow 2))
  refine HasDerivAt.congr_deriv (f := fun s => lyapV a b c d (u s) (v s)) h ?_
  simp only [Pi.sub_apply, lyapP, lyapQ]
  push_cast
  ring

/-- Cayley-Hamilton in coordinates: along the linear field, `∇V · Jv = 2 τ Δ |v|²`. -/
lemma lyap_linear (a b c d u v : ℝ) :
    lyapP a b c d u v * (a * u + b * v) + lyapQ a b c d u v * (c * u + d * v)
      = (a + d) * (a * d - b * c) * (u ^ 2 + v ^ 2) := by
  simp only [lyapP, lyapQ]; ring

lemma lyapV_ge (a b c d u v : ℝ) : (a * d - b * c) * (u ^ 2 + v ^ 2) ≤ lyapV a b c d u v := by
  unfold lyapV; nlinarith [sq_nonneg (b * v - d * u), sq_nonneg (c * u - a * v)]

/-- The constant `K = Δ + 2 (a² + b² + c² + d²)` with `V ≤ K |v|²`. -/
def lyapK (a b c d : ℝ) : ℝ := a * d - b * c + 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)

lemma lyapV_le (a b c d u v : ℝ) : lyapV a b c d u v ≤ lyapK a b c d * (u ^ 2 + v ^ 2) := by
  unfold lyapV lyapK
  nlinarith [sq_nonneg (b * v + d * u), sq_nonneg (c * u + a * v), sq_nonneg (b * u), sq_nonneg (d * v),
    sq_nonneg (c * v), sq_nonneg (a * u)]

/-- The constant `N` with `P² + Q² ≤ N |v|²`. -/
def lyapN (a b c d : ℝ) : ℝ :=
  (a * d - b * c + c ^ 2 + d ^ 2) ^ 2 + 2 * (a * c + b * d) ^ 2 + (a * d - b * c + a ^ 2 + b ^ 2) ^ 2

lemma lyapPQ_le (a b c d u v : ℝ) :
    lyapP a b c d u v ^ 2 + lyapQ a b c d u v ^ 2 ≤ lyapN a b c d * (u ^ 2 + v ^ 2) := by
  unfold lyapP lyapQ lyapN
  set m := a * d - b * c + c ^ 2 + d ^ 2
  set k := a * c + b * d
  set n := a * d - b * c + a ^ 2 + b ^ 2
  nlinarith [sq_nonneg (m * v + k * u), sq_nonneg (k * v + n * u)]

lemma lyapN_pos {a b c d : ℝ} (hdet : 0 < a * d - b * c) : 0 < lyapN a b c d := by
  unfold lyapN; positivity

lemma lyapK_pos {a b c d : ℝ} (hdet : 0 < a * d - b * c) : 0 < lyapK a b c d := by
  unfold lyapK; positivity

/-- The derivative estimate.  If the remainders `r₁, r₂` satisfy `r₁² + r₂² ≤ ε |v|²` with
`ε = σ² / (4N)`, `σ = -τΔ`, then `2 (P (Jv)₁ + Q (Jv)₂ + P r₁ + Q r₂) ≤ -σ |v|²`. -/
lemma lyap_deriv_bound {a b c d : ℝ} (htr : a + d < 0) (hdet : 0 < a * d - b * c) {u v r₁ r₂ : ℝ}
    (hr : r₁ ^ 2 + r₂ ^ 2 ≤ (-(a + d) * (a * d - b * c)) ^ 2 / (4 * lyapN a b c d) * (u ^ 2 + v ^ 2)) :
    2 * (lyapP a b c d u v * (a * u + b * v + r₁) + lyapQ a b c d u v * (c * u + d * v + r₂))
      ≤ -(-(a + d) * (a * d - b * c)) * (u ^ 2 + v ^ 2) := by
  set σ := -(a + d) * (a * d - b * c) with hσ
  have hσpos : 0 < σ := by rw [hσ]; nlinarith
  set N := lyapN a b c d
  have hN : 0 < N := lyapN_pos hdet
  set P := lyapP a b c d u v
  set Q := lyapQ a b c d u v
  have hlin := lyap_linear a b c d u v
  have hPQ := lyapPQ_le a b c d u v
  set w := u ^ 2 + v ^ 2
  have hw : 0 ≤ w := by positivity
  -- 2 (P r₁ + Q r₂) ≤ (P² + Q²)/s + s (r₁² + r₂²) with s = 2N/σ
  set s := 2 * N / σ with hs
  have hspos : 0 < s := by positivity
  have hcs : 2 * (P * r₁ + Q * r₂) ≤ (P ^ 2 + Q ^ 2) / s + s * (r₁ ^ 2 + r₂ ^ 2) := by
    have h1 : 0 ≤ (P - s * r₁) ^ 2 + (Q - s * r₂) ^ 2 := by positivity
    have : 2 * (P * r₁ + Q * r₂) * s ≤ (P ^ 2 + Q ^ 2) + s ^ 2 * (r₁ ^ 2 + r₂ ^ 2) := by nlinarith
    rw [div_add' _ _ _ hspos.ne', le_div_iff₀ hspos]
    nlinarith
  have h1 : (P ^ 2 + Q ^ 2) / s ≤ σ / 2 * w := by
    rw [div_le_iff₀ hspos, hs]
    have : σ / 2 * w * (2 * N / σ) = N * w := by field_simp
    rw [this]; exact hPQ
  have h2 : s * (r₁ ^ 2 + r₂ ^ 2) ≤ σ / 2 * w := by
    calc s * (r₁ ^ 2 + r₂ ^ 2) ≤ s * (σ ^ 2 / (4 * N) * w) := by gcongr
      _ = σ / 2 * w := by rw [hs]; field_simp; ring
  have hexp : 2 * (P * (a * u + b * v + r₁) + Q * (c * u + d * v + r₂))
      = 2 * ((a + d) * (a * d - b * c) * w) + 2 * (P * r₁ + Q * r₂) := by
    rw [← hlin]; ring
  rw [hexp]
  have : 2 * ((a + d) * (a * d - b * c) * w) = -2 * σ * w := by rw [hσ]; ring
  rw [this]
  linarith

/-- The decay rate `κ = σ / K`, `σ = -(a + d)(ad - bc)`. -/
noncomputable def lyapRate (a b c d : ℝ) : ℝ := (-(a + d) * (a * d - b * c)) / lyapK a b c d

/-- **Decay along solutions.** Under the hypotheses of `almost_linear_asymp_stable`, with `ρ` the radius on which
the remainder estimate holds with `ε = σ²/(4N)`, every solution with `V(v(0)) < W < Δρ²` satisfies
`V(v(t)) ≤ W e^{-κt/2}` for all `t ≥ 0`, where `κ = σ / K`. -/
lemma almost_linear_decay {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ} (htr : a + d < 0)
    (hdet : 0 < a * d - b * c) {ρ : ℝ}
    (hρ : ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ (-(a + d) * (a * d - b * c)) ^ 2 / (4 * lyapN a b c d) * (u ^ 2 + v ^ 2))
    {x y : ℝ → ℝ} (hsol : IsPlanarSol f g x y) {W : ℝ}
    (hW0 : lyapV a b c d (x 0 - x₀) (y 0 - y₀) < W) (hWρ : W < (a * d - b * c) * ρ ^ 2) :
    ∀ t, 0 ≤ t → lyapV a b c d (x t - x₀) (y t - y₀)
      ≤ W * Real.exp (-lyapRate a b c d / 2 * t) := by
  have hσpos : 0 < -(a + d) * (a * d - b * c) := by nlinarith
  have hK : 0 < lyapK a b c d := lyapK_pos hdet
  have hκpos : 0 < lyapRate a b c d := div_pos hσpos hK
  set σ := -(a + d) * (a * d - b * c) with hσ
  set K := lyapK a b c d
  set κ := lyapRate a b c d with hκ
  have hκK : κ * K = σ := div_mul_cancel₀ _ hK.ne'
  set F : ℝ → ℝ := fun t => lyapV a b c d (x t - x₀) (y t - y₀)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt F
      (2 * (lyapP a b c d (x t - x₀) (y t - y₀) * f (x t) (y t)
        + lyapQ a b c d (x t - x₀) (y t - y₀) * g (x t) (y t))) t := by
    intro t ht
    obtain ⟨hx, hy⟩ := hsol t ht
    exact lyapV_hasDerivAt a b c d (hx.sub_const x₀) (hy.sub_const y₀)
  intro t ht
  set B : ℝ → ℝ := fun s => W * Real.exp (-κ / 2 * s)
  have hBd : ∀ s, HasDerivAt B (W * (Real.exp (-κ / 2 * s) * (-κ / 2))) s := fun s =>
    (((hasDerivAt_id s).const_mul (-κ / 2)).exp.congr_deriv (by simp)).const_mul W
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := F) (a := 0) (b := t)
    (f' := fun s => 2 * (lyapP a b c d (x s - x₀) (y s - y₀) * f (x s) (y s)
        + lyapQ a b c d (x s - x₀) (y s - y₀) * g (x s) (y s)))
    (B := B) (B' := fun s => W * (Real.exp (-κ / 2 * s) * (-κ / 2)))
    (fun s hs => (hderiv s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s hs.1).hasDerivWithinAt)
    (by simp only [B, F, mul_zero, Real.exp_zero, mul_one]; exact hW0.le)
    (fun s _ => (hBd s).continuousAt.continuousWithinAt)
    (fun s _ => (hBd s).hasDerivWithinAt)
    (by
      intro s hs hFB
      have hW : 0 < W := lt_of_le_of_lt (le_trans (mul_nonneg hdet.le (by positivity)) (lyapV_ge _ _ _ _ _ _))
        hW0
      set u := x s - x₀
      set v := y s - y₀
      have hexp1 : Real.exp (-κ / 2 * s) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.1)
      have hBs : B s ≤ W := mul_le_of_le_one_right hW.le hexp1
      have hBpos : 0 < B s := mul_pos hW (Real.exp_pos _)
      have hFs : F s = lyapV a b c d u v := rfl
      have hFlt : (a * d - b * c) * (u ^ 2 + v ^ 2) < (a * d - b * c) * ρ ^ 2 :=
        lt_of_le_of_lt (lyapV_ge a b c d u v) (by rw [← hFs, hFB]; linarith)
      have huv : u ^ 2 + v ^ 2 < ρ ^ 2 := lt_of_mul_lt_mul_left hFlt hdet.le
      have hr := hρ u v huv
      have hxu : x₀ + u = x s := by simp [u]
      have hyv : y₀ + v = y s := by simp [v]
      rw [hxu, hyv] at hr
      have hbound := lyap_deriv_bound htr hdet (u := u) (v := v)
        (r₁ := f (x s) (y s) - (a * u + b * v)) (r₂ := g (x s) (y s) - (c * u + d * v)) hr
      have e1 : a * u + b * v + (f (x s) (y s) - (a * u + b * v)) = f (x s) (y s) := by ring
      have e2 : c * u + d * v + (g (x s) (y s) - (c * u + d * v)) = g (x s) (y s) := by ring
      rw [e1, e2] at hbound
      have hVle : F s ≤ K * (u ^ 2 + v ^ 2) := lyapV_le a b c d u v
      -- f'(s) ≤ -σ|v|² ≤ -κ F(s) < -(κ/2) F(s) = B'(s)
      have h1 : κ * F s ≤ σ * (u ^ 2 + v ^ 2) := by
        calc κ * F s ≤ κ * (K * (u ^ 2 + v ^ 2)) := mul_le_mul_of_nonneg_left hVle hκpos.le
          _ = σ * (u ^ 2 + v ^ 2) := by rw [← hκK]; ring
      have hB' : W * (Real.exp (-κ / 2 * s) * (-κ / 2)) = -(κ / 2) * B s := by simp only [B]; ring
      show 2 * (lyapP a b c d u v * f (x s) (y s) + lyapQ a b c d u v * g (x s) (y s))
        < W * (Real.exp (-κ / 2 * s) * (-κ / 2))
      rw [hB']
      rw [hFB] at h1
      have hkB : 0 < κ * B s := mul_pos hκpos hBpos
      linarith)
  exact key (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)

/-- **Differentiability gives the almost linear remainder estimate.** If `F(x,y) = (f(x,y), g(x,y))` is
differentiable at `(x₀, y₀)` with Jacobian `J`, `J(1,0) = (a, c)`, `J(0,1) = (b, d)`, then the remainder satisfies
the squared first-order estimate used in `almost_linear_asymp_stable`. -/
theorem almost_linear_of_hasFDerivAt {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    {J : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => (f p.1 p.2, g p.1 p.2)) J (x₀, y₀))
    (hcrit : f x₀ y₀ = 0 ∧ g x₀ y₀ = 0) (hJ1 : J (1, 0) = (a, c)) (hJ2 : J (0, 1) = (b, d)) :
    ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2) := by
  intro ε hε
  set κ := min 1 (ε / 2) with hκ
  have hκpos : 0 < κ := lt_min one_pos (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκε : κ ≤ ε / 2 := min_le_right _ _
  have hlo := hF.isLittleO.def hκpos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  refine ⟨ρ, hρ, fun u v huv => ?_⟩
  have hu : |u| < ρ := abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg v]) hρ.le
  have hv : |v| < ρ := abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg u]) hρ.le
  have hdist : dist ((x₀ + u, y₀ + v) : ℝ × ℝ) (x₀, y₀) < ρ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [add_sub_cancel_left]
    exact max_lt hu hv
  have h := hball hdist
  have hJuv : J ((x₀ + u, y₀ + v) - (x₀, y₀)) = (a * u + b * v, c * u + d * v) := by
    have : ((x₀ + u, y₀ + v) : ℝ × ℝ) - (x₀, y₀) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, hJ1, hJ2]
    ext <;> simp <;> ring
  rw [hJuv, hcrit.1, hcrit.2] at h
  simp only [Prod.mk_sub_mk, sub_zero, add_sub_cancel_left] at h
  rw [Prod.norm_def, Prod.norm_def] at h
  simp only [Real.norm_eq_abs] at h
  set r₁ := f (x₀ + u) (y₀ + v) - (a * u + b * v)
  set r₂ := g (x₀ + u) (y₀ + v) - (c * u + d * v)
  have hm : max |u| |v| ^ 2 ≤ u ^ 2 + v ^ 2 := by
    rcases le_total |u| |v| with h' | h'
    · rw [max_eq_right h', sq_abs]; nlinarith [sq_nonneg u]
    · rw [max_eq_left h', sq_abs]; nlinarith [sq_nonneg v]
  have h1 : r₁ ^ 2 ≤ (κ * max |u| |v|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (le_max_left _ _) h) 2
  have h2 : r₂ ^ 2 ≤ (κ * max |u| |v|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans (le_max_right _ _) h) 2
  have hκ2 : κ ^ 2 ≤ ε / 2 := by nlinarith
  calc r₁ ^ 2 + r₂ ^ 2 ≤ 2 * (κ ^ 2 * max |u| |v| ^ 2) := by nlinarith
    _ ≤ 2 * (ε / 2 * (u ^ 2 + v ^ 2)) := by gcongr
    _ = ε * (u ^ 2 + v ^ 2) := by ring

/-- **Almost linear stability (DE-222, stable rows of Table 8.1).** Let `(x₀, y₀)` be a critical point of the planar
system `x' = f(x,y)`, `y' = g(x,y)` whose linearization `J = [[a, b], [c, d]]` approximates the field to first order:
for every `ε > 0` there is `ρ > 0` with
`(f(x₀+u, y₀+v) - (au + bv))² + (g(x₀+u, y₀+v) - (cu + dv))² ≤ ε (u² + v²)` when `u² + v² < ρ²`
(this is the almost linear condition; it holds when `f, g` are differentiable at the point with Jacobian `J`, see
`almost_linear_of_hasFDerivAt`).  If both eigenvalues of `J` have negative real part, i.e. `a + d < 0` and
`ad - bc > 0` (asymptotically stable node or spiral of the linearization), then the critical point is
asymptotically stable. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_asymp_stable {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (htr : a + d < 0) (hdet : 0 < a * d - b * c) :
    IsAsympStablePt f g x₀ y₀ := by
  set σ := -(a + d) * (a * d - b * c) with hσ
  have hσpos : 0 < σ := by rw [hσ]; nlinarith
  set Δ := a * d - b * c
  set K := lyapK a b c d
  have hK : 0 < K := lyapK_pos hdet
  have hN := lyapN_pos hdet
  obtain ⟨ρ, hρ, hρbound⟩ := hlin (σ ^ 2 / (4 * lyapN a b c d)) (by positivity)
  set κ := lyapRate a b c d
  have hκpos : 0 < κ := div_pos hσpos hK
  -- For a target radius `e ≤ ρ`, start within `δ` with `K δ² = Δ e² / 2`.
  have main : ∀ e, 0 < e → e ≤ ρ → ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
      (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 →
        ∀ t, 0 ≤ t → (x t - x₀) ^ 2 + (y t - y₀) ^ 2 ≤ e ^ 2 / 2 * Real.exp (-κ / 2 * t) := by
    intro e he heρ
    refine ⟨Real.sqrt (Δ * e ^ 2 / (2 * K)), Real.sqrt_pos.mpr (by positivity), ?_⟩
    intro x y hsol h0 t ht
    rw [Real.sq_sqrt (by positivity)] at h0
    set W := Δ * e ^ 2 / 2
    have hV0 : lyapV a b c d (x 0 - x₀) (y 0 - y₀) < W := by
      calc lyapV a b c d (x 0 - x₀) (y 0 - y₀) ≤ K * ((x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2) := lyapV_le _ _ _ _ _ _
        _ < K * (Δ * e ^ 2 / (2 * K)) := by gcongr
        _ = W := by simp only [W]; field_simp
    have hWρ : W < Δ * ρ ^ 2 := by
      have : e ^ 2 ≤ ρ ^ 2 := by gcongr
      have he2 : 0 < e ^ 2 := by positivity
      show Δ * e ^ 2 / 2 < Δ * ρ ^ 2
      nlinarith
    have hdec := almost_linear_decay htr hdet hρbound hsol hV0 hWρ t ht
    have hge := lyapV_ge a b c d (x t - x₀) (y t - y₀)
    have : Δ * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2) ≤ Δ * (e ^ 2 / 2 * Real.exp (-κ / 2 * t)) := by
      calc Δ * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2) ≤ _ := hge
        _ ≤ _ := hdec
        _ = Δ * (e ^ 2 / 2 * Real.exp (-κ / 2 * t)) := by simp only [W]; ring
    exact le_of_mul_le_mul_left this hdet
  refine ⟨?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hmain⟩ := main (min ε ρ) (lt_min hε hρ) (min_le_right _ _)
    refine ⟨δ, hδ, fun x y hsol h0 t ht => ?_⟩
    have h := hmain x y hsol h0 t ht
    have hexp : Real.exp (-κ / 2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hm : min ε ρ ^ 2 ≤ ε ^ 2 := by gcongr; exact min_le_left _ _
    have hm0 : 0 < min ε ρ ^ 2 := by have := lt_min hε hρ; positivity
    calc (x t - x₀) ^ 2 + (y t - y₀) ^ 2 ≤ min ε ρ ^ 2 / 2 * Real.exp (-κ / 2 * t) := h
      _ ≤ min ε ρ ^ 2 / 2 * 1 := by gcongr
      _ < ε ^ 2 := by linarith
  · obtain ⟨δ, hδ, hmain⟩ := main ρ hρ le_rfl
    refine ⟨δ, hδ, fun x y hsol h0 => ?_⟩
    have hlim : Tendsto (fun t => ρ ^ 2 / 2 * Real.exp (-κ / 2 * t)) atTop (𝓝 0) := by
      have : Tendsto (fun t => Real.exp (-κ / 2 * t)) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        exact tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using this.const_mul (ρ ^ 2 / 2)
    have hev : ∀ᶠ t in atTop, (x t - x₀) ^ 2 + (y t - y₀) ^ 2 ≤ ρ ^ 2 / 2 * Real.exp (-κ / 2 * t) :=
      eventually_atTop.mpr ⟨0, fun t ht => hmain x y hsol h0 t ht⟩
    have hsq : Tendsto (fun t => (x t - x₀) ^ 2 + (y t - y₀) ^ 2) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun t => by positivity) hev hlim
    have hx2 : Tendsto (fun t => (x t - x₀) ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun t => by positivity) (fun t => by nlinarith [sq_nonneg (y t - y₀)]) hsq
    have hy2 : Tendsto (fun t => (y t - y₀) ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun t => by positivity) (fun t => by nlinarith [sq_nonneg (x t - x₀)]) hsq
    have hsqrt : ∀ {z : ℝ → ℝ} {z₀ : ℝ}, Tendsto (fun t => (z t - z₀) ^ 2) atTop (𝓝 0) →
        Tendsto z atTop (𝓝 z₀) := by
      intro z z₀ hz
      have h1 : Tendsto (fun t => Real.sqrt ((z t - z₀) ^ 2)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hz
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun t => |z t - z₀|) atTop (𝓝 0) := by
        simpa [Real.sqrt_sq_eq_abs] using h1
      have h3 : Tendsto (fun t => z t - z₀) atTop (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).mpr h2
      simpa using h3.add_const z₀
    exact ⟨hsqrt hx2, hsqrt hy2⟩

/-- **Almost linear stability, book form (DE-222).** If `(x₀, y₀)` is a critical point of `x' = f(x,y)`,
`y' = g(x,y)`, the field is differentiable there with Jacobian `[[a, b], [c, d]]`, and both eigenvalues of the
Jacobian have negative real part (`a + d < 0`, `ad - bc > 0`: the asymptotically stable node and spiral rows of
Table 8.1), then the critical point is asymptotically stable for the nonlinear system. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_asymp_stable_of_hasFDerivAt {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    {J : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => (f p.1 p.2, g p.1 p.2)) J (x₀, y₀))
    (hcrit : f x₀ y₀ = 0 ∧ g x₀ y₀ = 0) (hJ1 : J (1, 0) = (a, c)) (hJ2 : J (0, 1) = (b, d))
    (htr : a + d < 0) (hdet : 0 < a * d - b * c) :
    IsAsympStablePt f g x₀ y₀ :=
  almost_linear_asymp_stable (almost_linear_of_hasFDerivAt hF hcrit hJ1 hJ2) htr hdet

end UndergradKB.DifferentialEquations
