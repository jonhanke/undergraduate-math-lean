import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.AlmostLinear

/-! # Instability of almost linear critical points (sources and saddles)

Lebl, *Notes on Diffy Qs*, §8.2, Table 8.1.  For an almost linear critical point whose Jacobian `[[a, b], [c, d]]`
has `a + d > 0`, `ad - bc > 0` (unstable node or spiral source) or `ad - bc < 0` (saddle), the point is unstable.

Since `IsStablePt` only quantifies over solutions defined on `[0, ∞)`, instability is stated in Chetaev form
(`ChetaevUnstable`): there is `ε > 0` such that arbitrarily close to the point there are initial values from which
no solution stays within `ε` for all `t ≥ 0`.  The corollary `¬ IsStablePt` needs the extra hypothesis that
solutions exist from every initial point (true by Picard-Lindelöf and continuation, not proved here).

Proof: a quadratic form `V` with `V' ≥ σ |z|²` along the linearization; the nonlinear remainder is `o(|z|)`, so
`V' ≥ c |z|²` on a small ball; where `V > 0` this makes `V` grow linearly, contradicting boundedness in the ball.
For sources `V` is the Lyapunov form `lyapV` of `AlmostLinear`; for saddles it is the traceless form with matrix
`A + Aᵀ - tr(A) I`, for which `AᵀP + PA = 2 AᵀA - 2 det(A) I`. -/

namespace UndergradKB.DifferentialEquations

open Filter Topology

/-- The quadratic form `p u² + 2 q u v + r v²`. -/
def qf (p q r u v : ℝ) : ℝ := p * u ^ 2 + 2 * q * u * v + r * v ^ 2

lemma qf_le (p q r u v : ℝ) : qf p q r u v ≤ (|p| + |q| + |r| + 1) * (u ^ 2 + v ^ 2) := by
  unfold qf
  have h1 : p * u ^ 2 ≤ |p| * u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self p) (sq_nonneg u)
  have h3 : r * v ^ 2 ≤ |r| * v ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self r) (sq_nonneg v)
  have h2 : 2 * q * u * v ≤ |q| * (u ^ 2 + v ^ 2) := by
    rcases abs_cases q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · nlinarith [sq_nonneg (u - v), sq_nonneg (u + v)]
    · nlinarith [sq_nonneg (u - v), sq_nonneg (u + v)]
  nlinarith [abs_nonneg p, abs_nonneg q, abs_nonneg r, sq_nonneg u, sq_nonneg v]

/-- The cross term of the remainder is absorbed by a quarter of the linear gain. -/
lemma cross_bound {P Q r₁ r₂ N σ w : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hw : 0 ≤ w)
    (hPQ : P ^ 2 + Q ^ 2 ≤ N * w) (hr : r₁ ^ 2 + r₂ ^ 2 ≤ σ ^ 2 / (4 * N) * w) :
    -(σ * w) ≤ 2 * (P * r₁ + Q * r₂) := by
  have hcs : (P * r₁ + Q * r₂) ^ 2 ≤ (P ^ 2 + Q ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := by
    nlinarith [sq_nonneg (P * r₂ - Q * r₁)]
  have h2 : (P ^ 2 + Q ^ 2) * (r₁ ^ 2 + r₂ ^ 2) ≤ (N * w) * (σ ^ 2 / (4 * N) * w) :=
    mul_le_mul hPQ hr (by positivity) (by positivity)
  have h3 : (N * w) * (σ ^ 2 / (4 * N) * w) = (σ * w) ^ 2 / 4 := by field_simp
  have h4 : (2 * (P * r₁ + Q * r₂)) ^ 2 ≤ (σ * w) ^ 2 := by nlinarith
  exact (abs_le_of_sq_le_sq' h4 (by positivity)).1

/-- A quadratic form positive somewhere is positive at points arbitrarily close to `0`. -/
lemma exists_small_pos {p q r : ℝ} (h : ∃ u v, 0 < qf p q r u v) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u v, 0 < qf p q r u v ∧ u ^ 2 + v ^ 2 < δ ^ 2 := by
  obtain ⟨u, v, huv⟩ := h
  set w0 := u ^ 2 + v ^ 2 with hw0
  have hw0nn : 0 ≤ w0 := by positivity
  set s := δ / (w0 + 1) with hs
  have hspos : 0 < s := by positivity
  refine ⟨s * u, s * v, ?_, ?_⟩
  · have : qf p q r (s * u) (s * v) = s ^ 2 * qf p q r u v := by unfold qf; ring
    rw [this]; positivity
  · have : (s * u) ^ 2 + (s * v) ^ 2 = s ^ 2 * w0 := by rw [hw0]; ring
    rw [this, hs, div_pow, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have h0 : 0 < δ ^ 2 := by positivity
    have h1 : w0 < (w0 + 1) ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 h0]

/-- **Chetaev growth argument.**  If `V = qf p q r` satisfies `V ≤ M |z|²` and `V' ≥ c |z|²` on the ball of radius
`ρ`, then a solution with `V(z(0)) > 0` cannot stay in that ball for all `t ≥ 0`. -/
lemma chetaev_no_stay {f g : ℝ → ℝ → ℝ} {x₀ y₀ p q r M c ρ : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hc : 0 < c)
    (hV : ∀ u v, qf p q r u v ≤ M * (u ^ 2 + v ^ 2))
    (hder : ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      c * (u ^ 2 + v ^ 2) ≤ 2 * ((p * u + q * v) * f (x₀ + u) (y₀ + v) + (q * u + r * v) * g (x₀ + u) (y₀ + v)))
    {x y : ℝ → ℝ} (hsol : IsPlanarSol f g x y) (h0 : 0 < qf p q r (x 0 - x₀) (y 0 - y₀)) :
    ¬ ∀ t, 0 ≤ t → (x t - x₀) ^ 2 + (y t - y₀) ^ 2 < ρ ^ 2 := by
  intro hstay
  set G : ℝ → ℝ := fun t => qf p q r (x t - x₀) (y t - y₀) with hGdef
  set G' : ℝ → ℝ := fun t => 2 * ((p * (x t - x₀) + q * (y t - y₀)) * f (x t) (y t)
    + (q * (x t - x₀) + r * (y t - y₀)) * g (x t) (y t)) with hG'def
  have hG : ∀ t, 0 ≤ t → HasDerivAt G (G' t) t := by
    intro t ht
    obtain ⟨hx, hy⟩ := hsol t ht
    have hu := hx.sub_const x₀
    have hv := hy.sub_const y₀
    have h := ((hu.pow 2).const_mul p).add (((hu.mul hv).const_mul (2 * q)).add ((hv.pow 2).const_mul r))
    have hfun : G = (fun s => p * (x s - x₀) ^ 2 + (2 * q * ((x s - x₀) * (y s - y₀)) + r * (y s - y₀) ^ 2)) := by
      funext s; simp only [hGdef, qf]; ring
    rw [hfun]
    refine h.congr_deriv ?_
    simp only [hG'def]; push_cast; ring
  have hGn : ∀ t, 0 ≤ t → c * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2) ≤ G' t := by
    intro t ht
    have := hder (x t - x₀) (y t - y₀) (hstay t ht)
    rw [add_sub_cancel, add_sub_cancel] at this
    exact this
  have hmono : MonotoneOn G (Set.Ici 0) :=
    monotoneOn_Ici_of_hasDerivAt (E := G) (E' := G') hG
      (fun t ht => le_trans (by positivity) (hGn t ht))
  have hGge : ∀ t, 0 ≤ t → G 0 ≤ G t := fun t ht => hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  set w0 := G 0 with hw0
  have hw0pos : 0 < w0 := h0
  set k := c * w0 / M with hk
  have hkpos : 0 < k := by positivity
  have hGk : ∀ t, 0 ≤ t → k ≤ G' t := by
    intro t ht
    have h1 : w0 ≤ M * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2) := le_trans (hGge t ht) (hV _ _)
    have h2 : w0 / M ≤ (x t - x₀) ^ 2 + (y t - y₀) ^ 2 := by
      rw [div_le_iff₀ hM]; linarith
    have : k = c * (w0 / M) := by rw [hk]; ring
    rw [this]
    exact le_trans (mul_le_mul_of_nonneg_left h2 hc.le) (hGn t ht)
  have hH : MonotoneOn (fun t => G t - k * t) (Set.Ici 0) := by
    refine monotoneOn_Ici_of_hasDerivAt (E := fun t => G t - k * t) (E' := fun t => G' t - k) ?_ ?_
    · intro t ht
      exact (hG t ht).sub (((hasDerivAt_id t).const_mul k).congr_deriv (by simp))
    · intro t ht; linarith [hGk t ht]
  set T := M * ρ ^ 2 / k with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 := hH (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT0) hT0
  simp only [mul_zero, sub_zero] at h1
  have h2 : k * T = M * ρ ^ 2 := by rw [hT]; field_simp
  have h3 : G T ≤ M * ((x T - x₀) ^ 2 + (y T - y₀) ^ 2) := hV _ _
  have h4 := hstay T hT0
  have : M * ((x T - x₀) ^ 2 + (y T - y₀) ^ 2) < M * ρ ^ 2 := mul_lt_mul_of_pos_left h4 hM
  linarith

/-- **Chetaev-form instability** of the critical point `(x₀, y₀)`: there is `ε > 0` such that arbitrarily close to
the point there is an initial value from which no solution stays within `ε` of the point for all `t ≥ 0`. -/
def ChetaevUnstable (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∃ ε > 0, ∀ δ > 0, ∃ x₁ y₁ : ℝ, (x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2 < δ ^ 2 ∧
    ∀ x y : ℝ → ℝ, IsPlanarSol f g x y → (x 0, y 0) = (x₁, y₁) →
      ¬ ∀ t, 0 ≤ t → (x t - x₀) ^ 2 + (y t - y₀) ^ 2 < ε ^ 2

/-- Chetaev instability from a quadratic form with a definite derivative along the linearization. -/
lemma chetaev_of_almost_linear {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d p q r N σ : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hN : 0 < N) (hσ : 0 < σ)
    (hPQ : ∀ u v, (p * u + q * v) ^ 2 + (q * u + r * v) ^ 2 ≤ N * (u ^ 2 + v ^ 2))
    (hlinear : ∀ u v, 2 * σ * (u ^ 2 + v ^ 2)
      ≤ 2 * ((p * u + q * v) * (a * u + b * v) + (q * u + r * v) * (c * u + d * v)))
    (hpos : ∃ u v, 0 < qf p q r u v) :
    ChetaevUnstable f g x₀ y₀ := by
  obtain ⟨ρ, hρ, hρb⟩ := hlin (σ ^ 2 / (4 * N)) (by positivity)
  refine ⟨ρ, hρ, fun δ hδ => ?_⟩
  obtain ⟨u, v, huv, hsmall⟩ := exists_small_pos hpos hδ
  refine ⟨x₀ + u, y₀ + v, by simpa using hsmall, fun x y hsol h0 => ?_⟩
  have hx0 : x 0 = x₀ + u := congrArg Prod.fst h0
  have hy0 : y 0 = y₀ + v := congrArg Prod.snd h0
  refine chetaev_no_stay (f := f) (g := g) (p := p) (q := q) (r := r) (M := |p| + |q| + |r| + 1) (c := σ)
    hρ (by positivity) hσ (fun u v => qf_le p q r u v) ?_ hsol ?_
  · intro u v huv'
    have hr := hρb u v huv'
    have hc := cross_bound (P := p * u + q * v) (Q := q * u + r * v)
      (r₁ := f (x₀ + u) (y₀ + v) - (a * u + b * v)) (r₂ := g (x₀ + u) (y₀ + v) - (c * u + d * v))
      hN hσ (by positivity) (hPQ u v) hr
    have hl := hlinear u v
    nlinarith
  · rw [hx0, hy0]; simpa using huv

/-- **Non-stay for sources.**  If `a + d > 0` and `ad - bc > 0` the Lyapunov form `lyapV` is a Chetaev function. -/
theorem chetaevUnstable_source {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (htr : 0 < a + d) (hdet : 0 < a * d - b * c) : ChetaevUnstable f g x₀ y₀ := by
  have hqf : ∀ u v, qf (a * d - b * c + c ^ 2 + d ^ 2) (-(a * c + b * d)) (a * d - b * c + a ^ 2 + b ^ 2) u v
      = lyapV a b c d u v := fun u v => by unfold qf lyapV; ring
  refine chetaev_of_almost_linear (N := lyapN a b c d) (σ := (a + d) * (a * d - b * c))
    (p := a * d - b * c + c ^ 2 + d ^ 2) (q := -(a * c + b * d)) (r := a * d - b * c + a ^ 2 + b ^ 2) hlin
    (lyapN_pos hdet) (by positivity) ?_ ?_ ?_
  · intro u v
    have := lyapPQ_le a b c d u v
    simp only [lyapP, lyapQ] at this
    nlinarith
  · intro u v
    have := lyap_linear a b c d u v
    simp only [lyapP, lyapQ] at this
    nlinarith
  · refine ⟨1, 0, ?_⟩
    rw [hqf]
    have := lyapV_ge a b c d 1 0
    nlinarith

/-- **Non-stay for saddles.**  If `ad - bc < 0` the traceless form with matrix `A + Aᵀ - tr(A) I` is a Chetaev
function. -/
theorem chetaevUnstable_saddle {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hdet : a * d - b * c < 0) : ChetaevUnstable f g x₀ y₀ := by
  have hN : 0 < (a - d) ^ 2 + (b + c) ^ 2 := by
    by_contra h
    push_neg at h
    have h1 : (a - d) ^ 2 = 0 := by nlinarith [sq_nonneg (a - d), sq_nonneg (b + c)]
    have h2 : (b + c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - d), sq_nonneg (b + c)]
    have h1' : a = d := by have := pow_eq_zero_iff (two_ne_zero) |>.1 h1; linarith
    have h2' : c = -b := by have := pow_eq_zero_iff (two_ne_zero) |>.1 h2; linarith
    subst h1' h2'
    nlinarith [sq_nonneg a, sq_nonneg b]
  refine chetaev_of_almost_linear (N := (a - d) ^ 2 + (b + c) ^ 2) (σ := -(a * d - b * c))
    (p := a - d) (q := b + c) (r := d - a) hlin hN (by linarith) ?_ ?_ ?_
  · intro u v; nlinarith [sq_nonneg u]
  · intro u v
    nlinarith [sq_nonneg (a * u + b * v), sq_nonneg (c * u + d * v)]
  · set m := a - d with hm
    set k := b + c with hk
    have hN' : 0 < m ^ 2 + k ^ 2 := hN
    have e : ∀ u v, qf m k (d - a) u v = m * (u ^ 2 - v ^ 2) + 2 * k * u * v := by
      intro u v; unfold qf; rw [show d - a = -m by rw [hm]; ring]; ring
    rcases lt_trichotomy m 0 with h | h | h
    · refine ⟨k, -m, ?_⟩
      rw [e]; nlinarith
    · have hk0 : k ≠ 0 := by
        intro hk0; rw [h, hk0] at hN'; norm_num at hN'
      rcases lt_or_gt_of_ne hk0 with h' | h'
      · refine ⟨m - k, m + k, ?_⟩
        have hk2 : 0 < k ^ 2 := by positivity
        rw [e, h]; nlinarith [mul_pos (neg_pos.2 h') hk2]
      · refine ⟨m + k, k - m, ?_⟩
        have hk2 : 0 < k ^ 2 := by positivity
        rw [e, h]; nlinarith [mul_pos h' hk2]
    · refine ⟨m, k, ?_⟩
      rw [e]; nlinarith

/-- Instability implies `¬ IsStablePt` when solutions exist from every initial point. -/
theorem not_isStablePt_of_chetaev {f g : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ}
    (hex : ∀ p : ℝ × ℝ, ∃ x y : ℝ → ℝ, IsPlanarSol f g x y ∧ (x 0, y 0) = p)
    (h : ChetaevUnstable f g x₀ y₀) : ¬ IsStablePt f g x₀ y₀ := by
  intro hst
  obtain ⟨ε, hε, hu⟩ := h
  obtain ⟨δ, hδ, hstab⟩ := hst ε hε
  obtain ⟨x₁, y₁, hclose, hno⟩ := hu δ hδ
  obtain ⟨x, y, hsol, hp⟩ := hex (x₁, y₁)
  refine hno x y hsol hp (hstab x y hsol ?_)
  have hx0 : x 0 = x₁ := congrArg Prod.fst hp
  have hy0 : y 0 = y₁ := congrArg Prod.snd hp
  rw [hx0, hy0]; exact hclose

/-- **Instability of sources and saddles (DE-222, Table 8.1), Chetaev form.**  Let `(x₀, y₀)` be an almost linear
critical point with linearization `J = [[a, b], [c, d]]` (the same first-order hypothesis as in
`almost_linear_asymp_stable`).  If `J` has both eigenvalues with positive real part (`a + d > 0`, `ad - bc > 0`: unstable
node or spiral source) or eigenvalues of opposite signs (`ad - bc < 0`: saddle), then the critical point is
unstable in the sense `ChetaevUnstable`: there is `ε > 0` such that, arbitrarily close to the point, there are
initial values from which no solution stays within `ε` for all `t ≥ 0`.  (This avoids assuming existence of
solutions, which `IsStablePt` would need.) -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_unstable {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (h : (0 < a + d ∧ 0 < a * d - b * c) ∨ a * d - b * c < 0) : ChetaevUnstable f g x₀ y₀ := by
  rcases h with ⟨htr, hdet⟩ | hdet
  · exact chetaevUnstable_source hlin htr hdet
  · exact chetaevUnstable_saddle hlin hdet

/-- **Instability of sources and saddles, differentiable form (DE-222).**  The same as `almost_linear_unstable`
when the field is differentiable at the critical point with Jacobian `[[a, b], [c, d]]`. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_unstable_of_hasFDerivAt {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    {J : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => (f p.1 p.2, g p.1 p.2)) J (x₀, y₀))
    (hcrit : f x₀ y₀ = 0 ∧ g x₀ y₀ = 0) (hJ1 : J (1, 0) = (a, c)) (hJ2 : J (0, 1) = (b, d))
    (h : (0 < a + d ∧ 0 < a * d - b * c) ∨ a * d - b * c < 0) : ChetaevUnstable f g x₀ y₀ :=
  almost_linear_unstable (almost_linear_of_hasFDerivAt hF hcrit hJ1 hJ2) h

/-- **Sources and saddles are not stable (DE-222, Table 8.1).**  Under the hypotheses of `almost_linear_unstable`
the critical point is not stable, i.e. `¬ IsStablePt f g x₀ y₀`.  Hypothesis added beyond the book: solutions exist on
`[0, ∞)` from every initial point (`hex`); this follows from Picard-Lindelöf plus continuation but is not
proved here, and is needed because `IsStablePt` only speaks about existing solutions. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_not_isStablePt {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (h : (0 < a + d ∧ 0 < a * d - b * c) ∨ a * d - b * c < 0)
    (hex : ∀ p : ℝ × ℝ, ∃ x y : ℝ → ℝ, IsPlanarSol f g x y ∧ (x 0, y 0) = p) :
    ¬ IsStablePt f g x₀ y₀ :=
  not_isStablePt_of_chetaev hex (almost_linear_unstable hlin h)

/-- Differentiable form of `almost_linear_not_isStablePt` (DE-222), with the same added existence hypothesis. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_not_isStablePt_of_hasFDerivAt {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    {J : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => (f p.1 p.2, g p.1 p.2)) J (x₀, y₀))
    (hcrit : f x₀ y₀ = 0 ∧ g x₀ y₀ = 0) (hJ1 : J (1, 0) = (a, c)) (hJ2 : J (0, 1) = (b, d))
    (h : (0 < a + d ∧ 0 < a * d - b * c) ∨ a * d - b * c < 0)
    (hex : ∀ p : ℝ × ℝ, ∃ x y : ℝ → ℝ, IsPlanarSol f g x y ∧ (x 0, y 0) = p) :
    ¬ IsStablePt f g x₀ y₀ :=
  almost_linear_not_isStablePt (almost_linear_of_hasFDerivAt hF hcrit hJ1 hJ2) h hex

end UndergradKB.DifferentialEquations
