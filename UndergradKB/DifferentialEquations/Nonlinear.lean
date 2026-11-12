import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import UndergradKB.Common.Attr

/-! # Nonlinear planar systems (Lebl, *Notes on Diffy Qs*, Chapter 8)

A planar autonomous system `x' = f(x,y)`, `y' = g(x,y)` is written with two real functions `x y : ℝ → ℝ`
and hypotheses `HasDerivAt x (f (x t) (y t)) t`, `HasDerivAt y (g (x t) (y t)) t`.
We treat critical points, conservative equations, the pendulum, the Lotka-Volterra system,
stability definitions, and the centre / non-centre examples. The Jacobian matrices are given
explicitly as `2 × 2` matrices, and their eigenvalues are expressed through the characteristic polynomial. -/

namespace UndergradKB.DifferentialEquations

open Polynomial Set Filter Topology

/-! ## Critical points -/

/-- `(x₀, y₀)` is a critical point (equilibrium) of the planar system `x' = f(x,y)`, `y' = g(x,y)`:
both components of the vector field vanish there. -/
def IsCritPt (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : Prop := f x₀ y₀ = 0 ∧ g x₀ y₀ = 0

/-- **Critical points and constant solutions** (DE-218). At a critical point the constant functions solve
the system. -/
@[kb "lebldiffyqs2026" "§8.1 Critical points and equilibria, p. 352"]
theorem const_solution_of_isCritPt {f g : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} (h : IsCritPt f g x₀ y₀) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => x₀) (f x₀ y₀) t ∧ HasDerivAt (fun _ : ℝ => y₀) (g x₀ y₀) t := by
  rw [h.1, h.2]; exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩

/-- **Constant solutions sit at critical points** (DE-218, converse): if the constant functions
`x ≡ x₀`, `y ≡ y₀` solve the system at some time, then `(x₀, y₀)` is a critical point. -/
@[kb "lebldiffyqs2026" "§8.1 Critical points and equilibria, p. 352"]
theorem isCritPt_of_const_solution {f g : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} (t : ℝ)
    (hx : HasDerivAt (fun _ : ℝ => x₀) (f x₀ y₀) t) (hy : HasDerivAt (fun _ : ℝ => y₀) (g x₀ y₀) t) :
    IsCritPt f g x₀ y₀ :=
  ⟨(hx.unique (hasDerivAt_const _ _)), (hy.unique (hasDerivAt_const _ _))⟩

/-! ## Linearization -/

/-- **Linearization** (DE-219, thin restatement). If `f : ℝ × ℝ → ℝ` has Fréchet derivative `L` at the
point `(x₀, y₀)` then `f (x₀+u, y₀+v) - f (x₀,y₀) = f_x u + f_y v + o(‖(u,v)‖)`, where the partial
derivatives are `f_x = L (1,0)` and `f_y = L (0,1)` (the entries of the Jacobian row). -/
@[kb "lebldiffyqs2026" "§8.1.2 Linearization, p. 354"]
theorem linearization_isLittleO {f : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {x₀ y₀ : ℝ}
    (h : HasFDerivAt f L (x₀, y₀)) :
    (fun w : ℝ × ℝ => f (x₀ + w.1, y₀ + w.2) - f (x₀, y₀) - (L (1, 0) * w.1 + L (0, 1) * w.2))
      =o[𝓝 0] fun w => w := by
  have := hasFDerivAt_iff_isLittleO_nhds_zero.1 h
  refine this.congr (fun w => ?_) (fun _ => rfl)
  have : L w = L (1, 0) * w.1 + L (0, 1) * w.2 := by
    have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    calc L w = L (w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ))) := by rw [← hw]
      _ = _ := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
  have e : ((x₀, y₀) + w) = (x₀ + w.1, y₀ + w.2) := rfl
  simp [this, e]

/-! ## Helpers on monotonicity along solutions -/

/-- A function differentiable on `[0,∞)` with nonnegative derivative is monotone there. -/
theorem monotoneOn_Ici_of_hasDerivAt {E E' : ℝ → ℝ} (h : ∀ t, 0 ≤ t → HasDerivAt E (E' t) t)
    (h' : ∀ t, 0 ≤ t → 0 ≤ E' t) : MonotoneOn E (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun t ht => (h t ht).continuousAt.continuousWithinAt)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Ici] at ht; exact (h t (le_of_lt ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at ht; rw [(h t (le_of_lt ht)).deriv]; exact h' t (le_of_lt ht)

/-- A function with zero derivative on `[0,∞)` is constant there. -/
theorem const_Ici_of_hasDerivAt_zero {E : ℝ → ℝ} (h : ∀ t, 0 ≤ t → HasDerivAt E 0 t) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : E s = E t := by
  have h1 := monotoneOn_Ici_of_hasDerivAt (E := E) (E' := fun _ => 0) h (fun _ _ => le_rfl)
  have h2 := monotoneOn_Ici_of_hasDerivAt (E := fun t => -E t) (E' := fun _ => -0)
    (fun t ht => (h t ht).neg) (fun _ _ => by simp)
  rcases le_total s t with hst | hst
  · exact le_antisymm (h1 hs ht hst) (by simpa using h2 hs ht hst)
  · exact le_antisymm (by simpa using h2 ht hs hst) (h1 ht hs hst)

/-! ## Conservative equations -/

/-- **Conservative equation** `x'' + f(x) = 0` as the system `x' = y`, `y' = -f(x)` (DE-225): if `F' = f`,
the energy `y²/2 + F(x)` has derivative zero along solutions. -/
@[kb "lebldiffyqs2026" "§8.2.4 Conservative equations, p. 361"]
theorem conservative_energy_hasDerivAt {f F : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (f s) s) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t) (hy : ∀ t, HasDerivAt y (-f (x t)) t) (t : ℝ) :
    HasDerivAt (fun s => y s ^ 2 / 2 + F (x s)) 0 t := by
  have h1 := ((hy t).pow 2).div_const 2
  have h2 := (hF (x t)).comp t (hx t)
  refine (h1.add h2).congr_deriv ?_
  simp; ring

/-- **Conservation of energy** (DE-225): `y²/2 + F(x)` is constant along every solution of
`x' = y`, `y' = -f(x)`, so trajectories lie on level curves of the energy. -/
@[kb "lebldiffyqs2026" "§8.2.4 Conservative equations, p. 361"]
theorem conservative_energy_const {f F : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (f s) s) {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (y t) t) (hy : ∀ t, HasDerivAt y (-f (x t)) t) (s t : ℝ) :
    y s ^ 2 / 2 + F (x s) = y t ^ 2 / 2 + F (x t) := by
  have hd : Differentiable ℝ (fun s => y s ^ 2 / 2 + F (x s)) := fun t =>
    (conservative_energy_hasDerivAt hF hx hy t).differentiableAt
  exact is_const_of_deriv_eq_zero hd (fun t => (conservative_energy_hasDerivAt hF hx hy t).deriv) s t

/-- The Jacobian matrix `[[0,1],[-k,0]]` of the conservative system at `(x₀, 0)`, where `k = f'(x₀)`. -/
def consJac (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k, 0]

/-- The entries of `consJac f'(x₀)` are the partial derivatives at `(x₀, y₀)` of the vector field
`(y, -f(x))`: `∂x(y) = 0`, `∂y(y) = 1`, `∂x(-f) = -f'(x₀)`, `∂y(-f) = 0`. -/
theorem consJac_partials {f : ℝ → ℝ} {x₀ y₀ k : ℝ} (hf : HasDerivAt f k x₀) :
    HasDerivAt (fun _ : ℝ => y₀) (consJac k 0 0) x₀ ∧ HasDerivAt (fun y : ℝ => y) (consJac k 0 1) y₀ ∧
    HasDerivAt (fun x => -f x) (consJac k 1 0) x₀ ∧ HasDerivAt (fun _ : ℝ => -f x₀) (consJac k 1 1) y₀ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [consJac]
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_id' y₀
  · exact hf.neg
  · exact hasDerivAt_const _ _

/-- The characteristic polynomial of `consJac k` is `λ² + k`. -/
theorem consJac_charpoly (k : ℝ) : (consJac k).charpoly = X ^ 2 + C k := by
  rw [Matrix.charpoly_fin_two]
  simp [consJac, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- Eigenvalues of the conservative linearization (DE-226): `f'(x₀) < 0` gives two real eigenvalues
of opposite signs (a saddle); `f'(x₀) > 0` gives the purely imaginary pair `±i√f'(x₀)`
(no real eigenvalue). -/
@[kb "lebldiffyqs2026" "§8.2.4 Critical points of conservative equations, p. 362"]
theorem conservative_critpt_eigenvalues (k : ℝ) :
    (k < 0 → ∃ r s : ℝ, r < 0 ∧ 0 < s ∧ (consJac k).charpoly.IsRoot r ∧ (consJac k).charpoly.IsRoot s) ∧
    (0 < k → (∀ r : ℝ, ¬ (consJac k).charpoly.IsRoot r) ∧
      ∀ z : ℂ, ((consJac k).map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
        z = Complex.I * Real.sqrt k ∨ z = -(Complex.I * Real.sqrt k)) := by
  refine ⟨fun hk => ?_, fun hk => ⟨fun r => ?_, fun z => ?_⟩⟩
  · have hs := Real.sq_sqrt (neg_nonneg.2 hk.le)
    have hp := Real.sqrt_pos.2 (neg_pos.2 hk)
    refine ⟨-Real.sqrt (-k), Real.sqrt (-k), by linarith, hp, ?_, ?_⟩ <;>
      simp [consJac_charpoly, Polynomial.IsRoot] <;> nlinarith
  · simp only [consJac_charpoly, Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_C]
    nlinarith [sq_nonneg r]
  · rw [Matrix.charpoly_map, consJac_charpoly]
    have hs : (Real.sqrt k : ℂ) ^ 2 = k := by exact_mod_cast Real.sq_sqrt hk.le
    have hz : z ^ 2 + (k : ℂ) = (z - Complex.I * Real.sqrt k) * (z + Complex.I * Real.sqrt k) := by
      have : (Complex.I * Real.sqrt k) ^ 2 = -(k : ℂ) := by rw [mul_pow, Complex.I_sq, hs]; ring
      linear_combination this
    have e : ((X ^ 2 + C k : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot z ↔ z ^ 2 + (k : ℂ) = 0 := by
      simp [Polynomial.IsRoot]
    rw [e, hz, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-! ## The pendulum -/

/-- **Pendulum critical points** (DE-227). For `c = g/L ≠ 0`, the system `x' = y`, `y' = -c sin x`
(the equation `θ'' + (g/L) sin θ = 0`) has critical points exactly `(kπ, 0)`, `k ∈ ℤ`. -/
@[kb "lebldiffyqs2026" "§8.3.1 Pendulum, p. 364"]
theorem pendulum_isCritPt_iff {c : ℝ} (hc : c ≠ 0) (x y : ℝ) :
    IsCritPt (fun _ v => v) (fun u _ => -(c * Real.sin u)) x y ↔ ∃ k : ℤ, x = k * Real.pi ∧ y = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : Real.sin x = 0 := by
      simp only [neg_eq_zero, mul_eq_zero] at h2
      exact h2.resolve_left hc
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h2'
    exact ⟨k, hk.symm, h1⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨rfl, by simp⟩

/-- **Pendulum energy** (DE-227): along solutions of `x' = y`, `y' = -c sin x`, the energy
`y²/2 - c cos x` is constant, so trajectories are level curves of it. -/
@[kb "lebldiffyqs2026" "§8.3.1 Pendulum, p. 364"]
theorem pendulum_energy_const {c : ℝ} {x y : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (y t) t)
    (hy : ∀ t, HasDerivAt y (-(c * Real.sin (x t))) t) (s t : ℝ) :
    y s ^ 2 / 2 - c * Real.cos (x s) = y t ^ 2 / 2 - c * Real.cos (x t) := by
  have hF : ∀ u, HasDerivAt (fun u => -(c * Real.cos u)) (c * Real.sin u) u := fun u => by
    exact (((Real.hasDerivAt_cos u).const_mul c).neg).congr_deriv (by ring)
  have := conservative_energy_const hF hx hy s t
  linarith

/-- **Pendulum linearization** (DE-227): the Jacobian at `(kπ, 0)` is `consJac (c cos kπ)`, with
`c cos kπ = c` for even `k` and `-c` for odd `k`. For `c > 0` and even `k` the characteristic polynomial
is `λ² + c` (eigenvalues `±i√c`, no real ones); for odd `k` it is `λ² - c` (real eigenvalues `±√c`). -/
@[kb "lebldiffyqs2026" "§8.3.1 Pendulum, p. 364"]
theorem pendulum_linearization {c : ℝ} (hc : 0 < c) (k : ℤ) :
    (Even k → (consJac (c * Real.cos (k * Real.pi))).charpoly = X ^ 2 + C c ∧
      (∀ r : ℝ, ¬ (consJac (c * Real.cos (k * Real.pi))).charpoly.IsRoot r) ∧
      ∀ z : ℂ, ((consJac (c * Real.cos (k * Real.pi))).map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
        z = Complex.I * Real.sqrt c ∨ z = -(Complex.I * Real.sqrt c)) ∧
    (Odd k → (consJac (c * Real.cos (k * Real.pi))).charpoly = X ^ 2 - C c ∧
      ∃ r s : ℝ, r < 0 ∧ 0 < s ∧ (consJac (c * Real.cos (k * Real.pi))).charpoly.IsRoot r ∧
        (consJac (c * Real.cos (k * Real.pi))).charpoly.IsRoot s) := by
  rw [Real.cos_int_mul_pi]
  constructor
  · intro he
    rw [he.neg_one_zpow]
    have h := (conservative_critpt_eigenvalues (c * 1)).2 (by linarith)
    simp only [mul_one] at h ⊢
    exact ⟨consJac_charpoly c, h⟩
  · intro ho
    rw [ho.neg_one_zpow]
    have h := (conservative_critpt_eigenvalues (c * -1)).1 (by linarith)
    refine ⟨by rw [consJac_charpoly]; simp [sub_eq_add_neg], h⟩

/-! ## The Lotka-Volterra system -/

/-- The Jacobian of the Lotka-Volterra field `((a - b y) x, (c x - d) y)` at `(x, y)`. -/
def lvJac (a b c d x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a - b * y, -(b * x); c * y, c * x - d]

/-- **Lotka-Volterra critical points** (DE-229): for `a,b,c,d > 0` they are exactly `(0,0)` and
`(d/c, a/b)`. -/
@[kb "lebldiffyqs2026" "§8.3.2 Predator-prey systems, p. 368"]
theorem lv_isCritPt_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (x y : ℝ) :
    IsCritPt (fun u v => (a - b * v) * u) (fun u v => (c * u - d) * v) x y ↔
      (x = 0 ∧ y = 0) ∨ (x = d / c ∧ y = a / b) := by
  constructor
  · rintro ⟨h1, h2⟩
    simp only [mul_eq_zero] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · right; constructor
      · field_simp; linarith
      · field_simp; linarith
    · exfalso; subst h2; linarith
    · exfalso; subst h1; linarith
    · left; exact ⟨h1, h2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [IsCritPt]
    · constructor <;> field_simp <;> ring

/-- The characteristic polynomial of the Lotka-Volterra Jacobian at the origin, `diag(a, -d)`
(a saddle: `a > 0 > -d`). -/
@[kb "lebldiffyqs2026" "§8.3.2 Predator-prey systems, p. 368"]
theorem lv_origin_linearization (a b c d : ℝ) :
    lvJac a b c d 0 0 = !![a, 0; 0, -d] ∧ (lvJac a b c d 0 0).charpoly = (X - C a) * (X + C d) := by
  have h : lvJac a b c d 0 0 = !![a, 0; 0, -d] := by simp [lvJac]
  refine ⟨h, ?_⟩
  rw [h, Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- **Lotka-Volterra at the interior equilibrium** (DE-229): the Jacobian at `(d/c, a/b)` has
characteristic polynomial `λ² + a d`, hence eigenvalues `±i√(ad)`, none real. -/
@[kb "lebldiffyqs2026" "§8.3.2 Predator-prey systems, p. 368"]
theorem lv_interior_linearization {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (lvJac a b c d (d / c) (a / b)).charpoly = X ^ 2 + C (a * d) ∧
    (∀ r : ℝ, ¬ (lvJac a b c d (d / c) (a / b)).charpoly.IsRoot r) ∧
    ∀ z : ℂ, ((lvJac a b c d (d / c) (a / b)).map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
      z = Complex.I * Real.sqrt (a * d) ∨ z = -(Complex.I * Real.sqrt (a * d)) := by
  have ht : (lvJac a b c d (d / c) (a / b)).trace = 0 := by
    simp [Matrix.trace_fin_two, lvJac]; field_simp; ring
  have hdet : (lvJac a b c d (d / c) (a / b)).det = a * d := by
    simp [lvJac, Matrix.det_fin_two]; field_simp; norm_num
  have h : (lvJac a b c d (d / c) (a / b)).charpoly = (consJac (a * d)).charpoly := by
    rw [Matrix.charpoly_fin_two, consJac_charpoly, ht, hdet]
    simp only [map_zero, zero_mul, sub_zero]
  have h2 := (conservative_critpt_eigenvalues (a * d)).2 (mul_pos ha hd)
  refine ⟨by rw [h, consJac_charpoly], by rw [h]; exact h2.1, fun z => ?_⟩
  rw [Matrix.charpoly_map, h, ← Matrix.charpoly_map]
  exact h2.2 z

/-! ## The Lotka-Volterra constant of motion -/

/-- Logarithm of the constant of motion: `a log y + d log x - c x - b y`. -/
noncomputable def lvLog (a b c d x y : ℝ) : ℝ := a * Real.log y + d * Real.log x - c * x - b * y

/-- The constant of motion `C = y^a x^d e^{-cx-by}` of the Lotka-Volterra system. -/
noncomputable def lvConst (a b c d x y : ℝ) : ℝ := y ^ a * x ^ d * Real.exp (-c * x - b * y)

/-- `lvLog` has zero derivative along positive solutions. -/
theorem lvLog_hasDerivAt {a b c d : ℝ} {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x ((a - b * y t) * x t) t) (hy : ∀ t, HasDerivAt y ((c * x t - d) * y t) t)
    (hxp : ∀ t, 0 < x t) (hyp : ∀ t, 0 < y t) (t : ℝ) :
    HasDerivAt (fun s => lvLog a b c d (x s) (y s)) 0 t := by
  have h1 := (((hy t).log (hyp t).ne').const_mul a).add (((hx t).log (hxp t).ne').const_mul d)
  have h2 := h1.sub ((hx t).const_mul c) |>.sub ((hy t).const_mul b)
  refine h2.congr_deriv ?_
  have := (hxp t).ne'
  have := (hyp t).ne'
  field_simp
  ring

/-- **Constant of motion** (DE-230): along a solution of `x' = (a - b y) x`, `y' = (c x - d) y` with
`x, y > 0`, the quantity `C = y^a x^d e^{-cx-by}` does not change in time. -/
@[kb "lebldiffyqs2026" "§8.3.2 Constant of motion, p. 370"]
theorem lvConst_const {a b c d : ℝ} {x y : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x ((a - b * y t) * x t) t) (hy : ∀ t, HasDerivAt y ((c * x t - d) * y t) t)
    (hxp : ∀ t, 0 < x t) (hyp : ∀ t, 0 < y t) (s t : ℝ) :
    lvConst a b c d (x s) (y s) = lvConst a b c d (x t) (y t) := by
  have hd : Differentiable ℝ (fun s => lvLog a b c d (x s) (y s)) := fun t =>
    (lvLog_hasDerivAt hx hy hxp hyp t).differentiableAt
  have hL := is_const_of_deriv_eq_zero hd (fun t => (lvLog_hasDerivAt hx hy hxp hyp t).deriv) s t
  have key : ∀ u v : ℝ, 0 < u → 0 < v → lvConst a b c d u v = Real.exp (lvLog a b c d u v) := by
    intro u v hu hv
    rw [lvConst, lvLog, Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [key _ _ (hxp s) (hyp s), key _ _ (hxp t) (hyp t)]
  exact congrArg Real.exp hL

/-- One-variable estimate: `m log u - s u ≤ m log (m/s) - m` for `m, s, u > 0`, strictly if `u ≠ m/s`. -/
theorem log_estimate {m s u : ℝ} (hm : 0 < m) (hs : 0 < s) (hu : 0 < u) :
    m * Real.log u - s * u ≤ m * Real.log (m / s) - m ∧
      (u ≠ m / s → m * Real.log u - s * u < m * Real.log (m / s) - m) := by
  have hq : 0 < u / (m / s) := by positivity
  have hlog : Real.log (u / (m / s)) = Real.log u - Real.log (m / s) :=
    Real.log_div hu.ne' (by positivity)
  have e : u / (m / s) - 1 = (s * u - m) / m := by field_simp
  have h1 := Real.log_le_sub_one_of_pos hq
  rw [hlog, e] at h1
  have h1' : m * (Real.log u - Real.log (m / s)) ≤ s * u - m := by
    have := mul_le_mul_of_nonneg_left h1 hm.le
    rwa [mul_div_cancel₀ _ hm.ne'] at this
  refine ⟨by nlinarith, fun hne => ?_⟩
  have hne' : u / (m / s) ≠ 1 := by
    intro h; apply hne; field_simp at h ⊢; linarith
  have h2 := Real.log_lt_sub_one_of_pos hq hne'
  rw [hlog, e] at h2
  have := mul_lt_mul_of_pos_left h2 hm
  rw [mul_div_cancel₀ _ hm.ne'] at this
  nlinarith

/-- **Strict global maximum** (DE-230): on the open positive quadrant, the logarithm of the constant of
motion is strictly smaller than at the equilibrium `(d/c, a/b)`. -/
@[kb "lebldiffyqs2026" "§8.3.2 Constant of motion, p. 370"]
theorem lvLog_lt_at_equilibrium {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : (x, y) ≠ (d / c, a / b)) :
    lvLog a b c d x y < lvLog a b c d (d / c) (a / b) := by
  have e1 := log_estimate ha hb hy
  have e2 := log_estimate hd hc hx
  have eq : lvLog a b c d (d / c) (a / b) =
      (a * Real.log (a / b) - a) + (d * Real.log (d / c) - d) := by
    unfold lvLog; field_simp; ring
  have eq2 : lvLog a b c d x y = (a * Real.log y - b * y) + (d * Real.log x - c * x) := by
    unfold lvLog; ring
  rw [eq, eq2]
  by_cases h : y = a / b
  · have hx' : x ≠ d / c := fun h' => hne (by rw [h, h'])
    linarith [e1.1, e2.2 hx']
  · linarith [e1.2 h, e2.1]

/-- The constant of motion `C` itself is strictly smaller than its value at `(d/c, a/b)` elsewhere
on the open positive quadrant. -/
@[kb "lebldiffyqs2026" "§8.3.2 Constant of motion, p. 370"]
theorem lvConst_lt_at_equilibrium {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : (x, y) ≠ (d / c, a / b)) :
    lvConst a b c d x y < lvConst a b c d (d / c) (a / b) := by
  have key : ∀ u v : ℝ, 0 < u → 0 < v → lvConst a b c d u v = Real.exp (lvLog a b c d u v) := by
    intro u v hu hv
    rw [lvConst, lvLog, Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [key _ _ hx hy, key _ _ (by positivity) (by positivity)]
  exact Real.exp_lt_exp.2 (lvLog_lt_at_equilibrium ha hb hc hd hx hy hne)

/-! ## Stability -/

/-- `(x, y)` is a solution on `[0, ∞)` of the planar system `x' = f(x,y)`, `y' = g(x,y)`. -/
def IsPlanarSol (f g : ℝ → ℝ → ℝ) (x y : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt x (f (x t) (y t)) t ∧ HasDerivAt y (g (x t) (y t)) t

/-- **Stability** of the critical point `(x₀, y₀)`: for every `ε > 0` there is `δ > 0` such that every
solution starting within distance `δ` of the point stays within distance `ε` for all `t ≥ 0`
(distances are written through their squares). -/
def IsStablePt (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
    (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 →
      ∀ t, 0 ≤ t → (x t - x₀) ^ 2 + (y t - y₀) ^ 2 < ε ^ 2

/-- **Asymptotic stability**: stable, and every solution starting close enough tends to the point. -/
def IsAsympStablePt (f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  IsStablePt f g x₀ y₀ ∧ ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
    (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 →
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀)

/-- Derivative of `x² + y²`. -/
theorem sq_add_sq_hasDerivAt {x y : ℝ → ℝ} {p q t : ℝ} (hx : HasDerivAt x p t) (hy : HasDerivAt y q t) :
    HasDerivAt (fun s => x s ^ 2 + y s ^ 2) (2 * x t * p + 2 * y t * q) t :=
  ((hx.pow 2).add (hy.pow 2)).congr_deriv (by simp)

/-- The linear centre `x' = β y`, `y' = -β x`: `x² + y²` is constant along solutions. -/
theorem center_energy_const {β : ℝ} {x y : ℝ → ℝ} (h : IsPlanarSol (fun _ v => β * v) (fun u _ => -(β * u)) x y)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : x s ^ 2 + y s ^ 2 = x t ^ 2 + y t ^ 2 := by
  refine const_Ici_of_hasDerivAt_zero (E := fun s => x s ^ 2 + y s ^ 2) (fun t ht => ?_) hs ht
  have := sq_add_sq_hasDerivAt (h t ht).1 (h t ht).2
  exact this.congr_deriv (by ring)

/-- **A centre is stable** (DE-221, DE-223): the origin of `x' = β y`, `y' = -β x` is stable. -/
@[kb "lebldiffyqs2026" "§8.2.3 Centers, p. 359"]
theorem center_isStable (β : ℝ) : IsStablePt (fun _ v => β * v) (fun u _ => -(β * u)) 0 0 := by
  intro ε hε
  refine ⟨ε, hε, fun x y h h0 t ht => ?_⟩
  have := center_energy_const h (le_refl 0) ht
  simp only [sub_zero] at h0 ⊢
  linarith

/-- **A centre is not asymptotically stable** (DE-221, DE-223): the origin of `x' = β y`, `y' = -β x` is
stable (`center_isStable`) but not asymptotically stable, since the circular solutions
`(r cos βt, -r sin βt)` starting arbitrarily close never tend to the origin. -/
@[kb "lebldiffyqs2026" "§8.2.3 Centers, p. 359"]
theorem center_not_isAsympStable (β : ℝ) :
    ¬ IsAsympStablePt (fun _ v => β * v) (fun u _ => -(β * u)) 0 0 := by
  rintro ⟨-, δ, hδ, hconv⟩
  set r := δ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hsol : IsPlanarSol (fun _ v => β * v) (fun u _ => -(β * u))
      (fun t => r * Real.cos (β * t)) (fun t => -(r * Real.sin (β * t))) := by
    intro t _
    have h1 : HasDerivAt (fun t => r * Real.cos (β * t)) (r * (-Real.sin (β * t) * β)) t := by
      simpa using (((Real.hasDerivAt_cos (β * t)).comp t ((hasDerivAt_id t).const_mul β)).const_mul r)
    have h2 : HasDerivAt (fun t => -(r * Real.sin (β * t))) (-(r * (Real.cos (β * t) * β))) t := by
      exact ((((Real.hasDerivAt_sin (β * t)).comp t ((hasDerivAt_id t).const_mul β)).const_mul r).neg).congr_deriv
        (by simp)
    exact ⟨h1.congr_deriv (by ring), h2.congr_deriv (by ring)⟩
  have h0 : (r * Real.cos (β * 0) - 0) ^ 2 + (-(r * Real.sin (β * 0)) - 0) ^ 2 < δ ^ 2 := by
    simp; nlinarith
  obtain ⟨hx, hy⟩ := hconv _ _ hsol h0
  have hE := (hx.pow 2).add (hy.pow 2)
  have hc : ∀ t, (r * Real.cos (β * t)) ^ 2 + (-(r * Real.sin (β * t))) ^ 2 = r ^ 2 := fun t => by
    have := Real.sin_sq_add_cos_sq (β * t)
    nlinarith
  simp only [hc, zero_pow two_ne_zero, add_zero] at hE
  have := tendsto_nhds_unique hE (tendsto_const_nhds (x := r ^ 2) (f := (atTop : Filter ℝ)))
  have : r ^ 2 = 0 := by simpa using this.symm
  nlinarith

/-- **A centre linearization is inconclusive** (DE-224): for `x' = y`, `y' = -x + y³`, the quantity
`x² + y²` has derivative `2 y⁴ ≥ 0`, so it is nondecreasing along solutions on `[0, ∞)`. -/
@[kb "lebldiffyqs2026" "§8.2.3 Example 8.2.3, p. 360"]
theorem cubic_energy_monotone {x y : ℝ → ℝ} (h : IsPlanarSol (fun _ v => v) (fun u v => -u + v ^ 3) x y) :
    (∀ t, 0 ≤ t → HasDerivAt (fun s => x s ^ 2 + y s ^ 2) (2 * y t ^ 4) t) ∧
      MonotoneOn (fun s => x s ^ 2 + y s ^ 2) (Ici 0) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (fun s => x s ^ 2 + y s ^ 2) (2 * y t ^ 4) t := fun t ht =>
    (sq_add_sq_hasDerivAt (h t ht).1 (h t ht).2).congr_deriv (by ring)
  exact ⟨hd, monotoneOn_Ici_of_hasDerivAt hd (fun t _ => by positivity)⟩

/-- **A nonzero solution of `x' = y`, `y' = -x + y³` never tends to the origin** (DE-224). -/
@[kb "lebldiffyqs2026" "§8.2.3 Example 8.2.3, p. 360"]
theorem cubic_not_tendsto {x y : ℝ → ℝ} (h : IsPlanarSol (fun _ v => v) (fun u v => -u + v ^ 3) x y)
    (h0 : x 0 ≠ 0 ∨ y 0 ≠ 0) : ¬ (Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0)) := by
  rintro ⟨hx, hy⟩
  have hmono := (cubic_energy_monotone h).2
  have hpos : 0 < x 0 ^ 2 + y 0 ^ 2 := by
    rcases h0 with h0 | h0
    · have := sq_pos_of_ne_zero h0; positivity
    · have := sq_pos_of_ne_zero h0; positivity
  have hE := (hx.pow 2).add (hy.pow 2)
  simp only [zero_pow two_ne_zero, add_zero] at hE
  have hev : ∀ᶠ t in atTop, (x t ^ 2 + y t ^ 2 : ℝ) < x 0 ^ 2 + y 0 ^ 2 :=
    hE.eventually (gt_mem_nhds hpos)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  have := hmono (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 (le_max_right T 0)) (le_max_right T 0 |> fun _ => by simp)
  have := hT (max T 0) (le_max_left _ _)
  linarith

/-- **The origin of `x' = y`, `y' = -x + y³` is not asymptotically stable** (DE-224), granting
(this is the only input we cannot extract from Mathlib's local existence theorem, as the solutions may
blow up in finite time) that there are solutions on `[0, ∞)` starting at nonzero points arbitrarily
near the origin. -/
@[kb "lebldiffyqs2026" "§8.2.3 Example 8.2.3, p. 360"]
theorem cubic_not_isAsympStable
    (hex : ∀ δ > 0, ∃ x y : ℝ → ℝ, IsPlanarSol (fun _ v => v) (fun u v => -u + v ^ 3) x y ∧
      x 0 ^ 2 + y 0 ^ 2 < δ ^ 2 ∧ (x 0 ≠ 0 ∨ y 0 ≠ 0)) :
    ¬ IsAsympStablePt (fun _ v => v) (fun u v => -u + v ^ 3) 0 0 := by
  rintro ⟨-, δ, hδ, hconv⟩
  obtain ⟨x, y, hs, h1, h2⟩ := hex δ hδ
  have := hconv x y hs (by simpa using h1)
  exact cubic_not_tendsto hs h2 this

end UndergradKB.DifferentialEquations
