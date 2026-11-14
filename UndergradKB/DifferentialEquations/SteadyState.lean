import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-! # Steady-state temperature and the Laplace equation

Lebl, *Notes on Diffy Qs*, §4.9.  A time-independent solution of the heat equation `u_t = k u_xx`
(one space variable) has `v'' = 0`, so the steady-state wire temperature is linear.  In two space
variables the steady state satisfies the Laplace equation `v_xx + v_yy = 0`; for `C²` functions on the
Euclidean plane this is exactly the vanishing of Mathlib's `InnerProductSpace` Laplacian, i.e. harmonicity.
Partial derivatives are iterated `deriv`s of the slices, as in `PDE.lean`. -/

namespace UndergradKB.DifferentialEquations

open Set

/-! ## One space variable -/

/-- A time-independent function `u x t = v x` solves `u_t = k u_xx` (for all `x, t`, `k ≠ 0`) iff `v'' = 0`. -/
theorem heat_timeIndependent_iff {k : ℝ} (hk : k ≠ 0) (v : ℝ → ℝ) :
    (∀ x t : ℝ, deriv (fun s => (fun ξ (_ : ℝ) => v ξ) x s) t
      = k * deriv (fun ξ => deriv (fun ξ => (fun ξ (_ : ℝ) => v ξ) ξ t) ξ) x) ↔
    ∀ x, deriv (deriv v) x = 0 := by
  constructor
  · intro h x
    have := h x 0
    simp only [deriv_const] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hk
  · intro h x t
    simp only [deriv_const]
    have : deriv (fun ξ => deriv v ξ) x = 0 := h x
    rw [this, mul_zero]

/-- A function whose second derivative vanishes on an open interval is affine on the closed interval. -/
theorem exists_affine_of_deriv_deriv_eq_zero {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc a b)) (h1 : ∀ x ∈ Ioo a b, DifferentiableAt ℝ v x)
    (h2 : ∀ x ∈ Ioo a b, DifferentiableAt ℝ (deriv v) x)
    (h0 : ∀ x ∈ Ioo a b, deriv (deriv v) x = 0) :
    ∃ A B : ℝ, ∀ x ∈ Icc a b, v x = A * x + B := by
  have hconst : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, deriv v x = deriv v y :=
    fun x hx y hy => IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun x hx => (h2 x hx).differentiableWithinAt) (fun x hx => h0 x hx) hx hy
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set A := deriv v ((a + b) / 2)
  refine ⟨A, v a - A * a, fun x hx => ?_⟩
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; ring
  · have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    obtain ⟨c, hc1, hc2⟩ := exists_deriv_eq_slope (fun y => v y - A * y) h
      ((hc.mono hsub).sub (continuousOn_const.mul continuousOn_id))
      (fun y hy => ((h1 y ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩).sub
        ((differentiableAt_id.const_mul A))).differentiableWithinAt)
    have hcb : c ∈ Ioo a b := ⟨hc1.1, lt_of_lt_of_le hc1.2 hx.2⟩
    have hd : deriv (fun y => v y - A * y) c = 0 := by
      have : HasDerivAt (fun y => v y - A * y) (deriv v c - A * 1) c :=
        ((h1 c hcb).hasDerivAt).sub ((hasDerivAt_id c).const_mul A)
      rw [this.deriv, hconst c hcb _ hm]; ring
    rw [hd] at hc2
    have hxa : x - a ≠ 0 := by linarith
    have := (eq_div_iff hxa).mp hc2
    linarith

/-- **Steady-state wire temperature (DE-148).**  For a wire on `[0, L]` (`L > 0`), a profile `v` with
the regularity `v` continuous on `[0,L]` and `v`, `v'` differentiable on `(0,L)`: `v'' = 0` on `(0,L)`
(the condition for `u(x,t) = v(x)` to be a steady-state solution of `u_t = k u_xx`, `k ≠ 0`, see
`heat_timeIndependent_iff`) together with `v(0) = T₁`, `v(L) = T₂` holds iff
`v x = (T₂ - T₁) / L * x + T₁` on `[0,L]`; so that line is the unique steady state. -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem steady_state_wire {L T₁ T₂ : ℝ} (hL : 0 < L) {v : ℝ → ℝ}
    (hc : ContinuousOn v (Icc 0 L)) (h1 : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ v x)
    (h2 : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ (deriv v) x) :
    ((∀ x ∈ Ioo 0 L, deriv (deriv v) x = 0) ∧ v 0 = T₁ ∧ v L = T₂) ↔
      ∀ x ∈ Icc 0 L, v x = (T₂ - T₁) / L * x + T₁ := by
  constructor
  · rintro ⟨h0, e0, eL⟩
    obtain ⟨A, B, hAB⟩ := exists_affine_of_deriv_deriv_eq_zero hL hc h1 h2 h0
    have a0 := hAB 0 ⟨le_rfl, hL.le⟩
    have aL := hAB L ⟨hL.le, le_rfl⟩
    have hB : B = T₁ := by rw [e0] at a0; linarith
    have hA : A = (T₂ - T₁) / L := by
      rw [eq_div_iff hL.ne']; rw [eL] at aL; rw [hB] at aL; linarith
    intro x hx
    rw [hAB x hx, hA, hB]
  · intro h
    have hloc : ∀ x ∈ Ioo (0 : ℝ) L, v =ᶠ[nhds x] fun y => (T₂ - T₁) / L * y + T₁ := fun x hx =>
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun y hy => h y ⟨hy.1.le, hy.2.le⟩
    refine ⟨fun x hx => ?_, by simpa using h 0 ⟨le_rfl, hL.le⟩, ?_⟩
    · have hd : ∀ y ∈ Ioo (0 : ℝ) L, deriv v y = (T₂ - T₁) / L := fun y hy => by
        rw [(hloc y hy).deriv_eq]
        have := ((hasDerivAt_id y).const_mul ((T₂ - T₁) / L)).add_const T₁
        simpa using this.deriv
      have : deriv v =ᶠ[nhds x] fun _ => (T₂ - T₁) / L :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) hd
      rw [this.deriv_eq]; simp
    · rw [h L ⟨hL.le, le_rfl⟩]; field_simp; ring

/-! ## Two space variables -/

/-- The Laplace equation `v_xx + v_yy = 0` for `v : ℝ → ℝ → ℝ` (first slot `x`, second `y`),
with partial derivatives as iterated `deriv`s of the slices. -/
def LaplaceEq2 (v : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, deriv (fun ξ => deriv (fun ξ => v ξ y) ξ) x + deriv (fun η => deriv (fun η => v x η) η) y = 0

/-- The two-dimensional heat equation `u_t = k (u_xx + u_yy)` for `u x y t`, stated for all `x, y, t`. -/
def HeatEq2 (k : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y t, deriv (fun s => u x y s) t
    = k * (deriv (fun ξ => deriv (fun ξ => u ξ y t) ξ) x
      + deriv (fun η => deriv (fun η => u x η t) η) y)

/-- **Steady state satisfies the Laplace equation (DE-148).** For `k ≠ 0`, the time-independent function
`u(x,y,t) = v(x,y)` solves `u_t = k (u_xx + u_yy)` iff `v_xx + v_yy = 0`. -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem steady_state_laplace {k : ℝ} (hk : k ≠ 0) (v : ℝ → ℝ → ℝ) :
    HeatEq2 k (fun x y _ => v x y) ↔ LaplaceEq2 v := by
  constructor
  · intro h x y
    have := h x y 0
    simp only [deriv_const] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hk
  · intro h x y t
    simp only [deriv_const]
    rw [h x y, mul_zero]

/-! ## Bridge to Mathlib's Laplacian -/

open InnerProductSpace Laplacian

/-- A function of two real variables, viewed on the Euclidean plane. -/
def onPlane (v : ℝ → ℝ → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => v (p 0) (p 1)

lemma iteratedFDeriv_two_diag {F : EuclideanSpace ℝ (Fin 2) → ℝ} (hF : ContDiff ℝ 2 F)
    (p w : EuclideanSpace ℝ (Fin 2)) :
    iteratedFDeriv ℝ 2 F p ![w, w] = deriv (fun s : ℝ => deriv (fun r : ℝ => F (p + r • w)) s) 0 := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ s : ℝ, deriv (fun r : ℝ => F (p + r • w)) s = fderiv ℝ F (p + s • w) w := by
    intro s
    have hl : HasDerivAt (fun r : ℝ => p + r • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add p
    have := (hd (p + s • w)).hasFDerivAt.comp_hasDerivAt s hl
    exact this.deriv
  have hl0 : HasDerivAt (fun r : ℝ => p + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
  have hh : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) (p + (0 : ℝ) • w) := by
    rw [zero_smul, add_zero]; exact (hd2 p).hasFDerivAt
  have hc := hh.comp_hasDerivAt (0 : ℝ) hl0
  have hg := hc.clm_apply (hasDerivAt_const (0 : ℝ) w)
  have e : deriv (fun s : ℝ => fderiv ℝ F (p + s • w) w) 0 = fderiv ℝ (fderiv ℝ F) p w w := by
    have hg' := hg.congr_deriv (g' := fderiv ℝ (fderiv ℝ F) p w w) (by simp)
    exact hg'.deriv
  have e2 : (fun s : ℝ => deriv (fun r : ℝ => F (p + r • w)) s)
      = fun s : ℝ => fderiv ℝ F (p + s • w) w := funext h1
  rw [e2, e, iteratedFDeriv_two_apply]
  all_goals simp

/-- **The Laplacian is `v_xx + v_yy` (DE-148).** For `v` such that `(x,y) ↦ v x y` is `C²` on the Euclidean
plane, Mathlib's Laplacian of the function on `EuclideanSpace ℝ (Fin 2)` is the sum of the two second
partial derivatives. -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem laplacian_onPlane {v : ℝ → ℝ → ℝ} (hv : ContDiff ℝ 2 (onPlane v))
    (p : EuclideanSpace ℝ (Fin 2)) :
    Δ (onPlane v) p = deriv (fun ξ => deriv (fun ξ => v ξ (p 1)) ξ) (p 0)
      + deriv (fun η => deriv (fun η => v (p 0) η) η) (p 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (onPlane v) (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply]
  rw [iteratedFDeriv_two_diag hv, iteratedFDeriv_two_diag hv]
  congr 1
  · have e1 : ∀ s : ℝ, deriv (fun r : ℝ => onPlane v (p + r • EuclideanSpace.single 0 (1 : ℝ))) s
        = deriv (fun ξ => v ξ (p 1)) (p 0 + s) := by
      intro s
      have : (fun r : ℝ => onPlane v (p + r • EuclideanSpace.single 0 (1 : ℝ)))
          = fun r => (fun ξ => v ξ (p 1)) (p 0 + r) := by
        funext r; simp [onPlane]
      rw [this]; exact deriv_comp_const_add (fun ξ => v ξ (p 1)) (p 0) s
    simp_rw [e1]
    rw [deriv_comp_const_add (fun ξ => deriv (fun ξ => v ξ (p 1)) ξ)]
    simp
  · have e1 : ∀ s : ℝ, deriv (fun r : ℝ => onPlane v (p + r • EuclideanSpace.single 1 (1 : ℝ))) s
        = deriv (fun η => v (p 0) η) (p 1 + s) := by
      intro s
      have : (fun r : ℝ => onPlane v (p + r • EuclideanSpace.single 1 (1 : ℝ)))
          = fun r => (fun η => v (p 0) η) (p 1 + r) := by
        funext r; simp [onPlane]
      rw [this]; exact deriv_comp_const_add (fun η => v (p 0) η) (p 1) s
    simp_rw [e1]
    rw [deriv_comp_const_add (fun η => deriv (fun η => v (p 0) η) η)]
    simp

/-- **Steady-state temperatures are harmonic (DE-148).**  If `v` is `C²` on the plane and
`v_xx + v_yy = 0`, then `v` is harmonic in Mathlib's sense on `EuclideanSpace ℝ (Fin 2)`; conversely a
harmonic function satisfies the Laplace equation.  By `steady_state_laplace` this applies to every
steady-state solution of the two-dimensional heat equation. -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem harmonicOnNhd_iff_laplaceEq2 {v : ℝ → ℝ → ℝ} (hv : ContDiff ℝ 2 (onPlane v)) :
    HarmonicOnNhd (onPlane v) univ ↔ LaplaceEq2 v := by
  constructor
  · intro h x y
    have hp := (h (EuclideanSpace.single 0 x + EuclideanSpace.single 1 y) trivial).2.self_of_nhds
    have := laplacian_onPlane hv (EuclideanSpace.single 0 x + EuclideanSpace.single 1 y)
    simp at this hp
    rw [hp] at this
    simpa using this.symm
  · intro h p _
    refine ⟨hv.contDiffAt, Filter.Eventually.of_forall fun q => ?_⟩
    rw [laplacian_onPlane hv]
    exact h _ _

/-! ## Examples (p. 259) -/

/-- `x² - y²` is harmonic: `v_xx + v_yy = 2 - 2 = 0` (DE-148). -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem laplaceEq2_sq_sub_sq : LaplaceEq2 (fun x y => x ^ 2 - y ^ 2) := by
  intro x y
  have h1 : (fun ξ : ℝ => deriv (fun ξ => ξ ^ 2 - y ^ 2) ξ) = fun ξ => 2 * ξ := by
    funext ξ
    have := ((hasDerivAt_pow 2 ξ).sub_const (y ^ 2))
    simpa using this.deriv
  have h2 : (fun η : ℝ => deriv (fun η => x ^ 2 - η ^ 2) η) = fun η => -(2 * η) := by
    funext η
    have := ((hasDerivAt_pow 2 η).const_sub (x ^ 2))
    simpa using this.deriv
  rw [h1, h2]
  have a := ((hasDerivAt_id x).const_mul (2 : ℝ)).deriv
  have b := (((hasDerivAt_id y).const_mul (2 : ℝ)).neg).deriv
  simp only [id, mul_one] at a b
  simp only [a, b]; norm_num

/-- `x y` is harmonic: `v_xx + v_yy = 0 + 0` (DE-148). -/
@[kb "lebldiffyqs2026" "§4.9 Laplacian, Laplace equation, harmonic function, p. 258"]
theorem laplaceEq2_mul : LaplaceEq2 (fun x y => x * y) := by
  intro x y
  have h1 : (fun ξ : ℝ => deriv (fun ξ => ξ * y) ξ) = fun _ => y := by
    funext ξ; simpa using ((hasDerivAt_id ξ).mul_const y).deriv
  have h2 : (fun η : ℝ => deriv (fun η => x * η) η) = fun _ => x := by
    funext η; simpa using ((hasDerivAt_id η).const_mul x).deriv
  simp [h1, h2]

end UndergradKB.DifferentialEquations
