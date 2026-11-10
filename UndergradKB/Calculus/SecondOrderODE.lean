import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus
open Real

/-- Solution of `a y'' + b y' + c y = f`, constant coefficients. -/
def ConstSol (a b c : ℝ) (f : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
    ∀ x, a * deriv (deriv y) x + b * deriv y x + c * y x = f x

lemma ConstSol.of_hasDeriv {a b c : ℝ} {f y y1 y2 : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt y (y1 x) x) (h2 : ∀ x, HasDerivAt y1 (y2 x) x)
    (h : ∀ x, a * y2 x + b * y1 x + c * y x = f x) : ConstSol a b c f y := by
  have e1 : deriv y = y1 := funext fun x => (h1 x).deriv
  have e2 : deriv y1 = y2 := funext fun x => (h2 x).deriv
  refine ⟨fun x => (h1 x).differentiableAt, ?_, ?_⟩
  · rw [e1]; exact fun x => (h2 x).differentiableAt
  · intro x; rw [e1, e2]; exact h x

/-- `z' = k z` implies `z = z 0 * exp (k x)`. -/
lemma ode_exp {z : ℝ → ℝ} {k : ℝ} (hz : Differentiable ℝ z) (h : ∀ x, deriv z x = k * z x) :
    ∀ x, z x = z 0 * exp (k * x) := by
  have hd : ∀ x, HasDerivAt (fun x => z x * exp (-(k * x))) 0 x := by
    intro x
    have h1 := (hz x).hasDerivAt
    have h2 : HasDerivAt (fun x => exp (-(k * x))) (exp (-(k*x)) * (-(k*1))) x :=
      (((hasDerivAt_id x).const_mul k).neg).exp
    convert h1.mul h2 using 1
    rw [h x]; ring
  have hc : ∀ x, z x * exp (-(k * x)) = z 0 := by
    intro x
    have := is_const_of_deriv_eq_zero (f := fun x => z x * exp (-(k * x)))
      (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) x 0
    simpa using this
  intro x
  have := hc x
  have he : exp (-(k * x)) * exp (k * x) = 1 := by rw [← exp_add]; simp
  calc z x = z x * exp (-(k*x)) * exp (k*x) := by rw [mul_assoc, he, mul_one]
    _ = _ := by rw [this]

/-- energy uniqueness for `w'' = -β² w`. -/
lemma harmonic_zero {w : ℝ → ℝ} {β : ℝ} (hw : Differentiable ℝ w) (hw' : Differentiable ℝ (deriv w))
    (h : ∀ x, deriv (deriv w) x = -(β^2) * w x) (h0 : w 0 = 0) (h0' : deriv w 0 = 0) :
    ∀ x, w x = 0 ∧ deriv w x = 0 := by
  have hd : ∀ x, HasDerivAt (fun x => deriv w x ^ 2 + β^2 * w x ^ 2) 0 x := by
    intro x
    have a1 := (hw' x).hasDerivAt
    have a2 := (hw x).hasDerivAt
    convert (a1.pow 2).add ((a2.pow 2).const_mul (β^2)) using 1
    rw [h x]; simp; ring
  have hc : ∀ x, deriv w x ^ 2 + β^2 * w x ^ 2 = 0 := by
    intro x
    have := is_const_of_deriv_eq_zero (f := fun x => deriv w x ^ 2 + β^2 * w x ^ 2)
      (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) x 0
    simp [h0, h0'] at this; simpa using this
  intro x
  have := hc x
  by_cases hb : β = 0
  · subst hb
    have hz : ∀ x, deriv w x = 0 := by simpa using hc
    refine ⟨?_, hz x⟩
    have := is_const_of_deriv_eq_zero hw hz x 0
    rw [this, h0]
  · have hb2 : 0 < β^2 := by positivity
    have h1 : deriv w x ^ 2 = 0 := by nlinarith [sq_nonneg (deriv w x), sq_nonneg (w x)]
    have h2 : w x ^ 2 = 0 := by nlinarith [sq_nonneg (deriv w x), sq_nonneg (w x)]
    exact ⟨pow_eq_zero_iff (by norm_num) |>.1 h2, pow_eq_zero_iff (by norm_num) |>.1 h1⟩

lemma harmonic_solve {u : ℝ → ℝ} {β : ℝ} (hβ : β ≠ 0) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (h : ∀ x, deriv (deriv u) x = -(β^2) * u x) :
    ∀ x, u x = u 0 * cos (β * x) + deriv u 0 / β * sin (β * x) := by
  set v : ℝ → ℝ := fun x => u 0 * cos (β * x) + deriv u 0 / β * sin (β * x) with hv
  have hv1 : ∀ x, HasDerivAt v (-(u 0 * β * sin (β*x)) + deriv u 0 * cos (β*x)) x := by
    intro x
    have hl : HasDerivAt (fun x => β * x) β x := by simpa using (hasDerivAt_id x).const_mul β
    have := ((hl.cos).const_mul (u 0)).add ((hl.sin).const_mul (deriv u 0 / β))
    convert this using 1
    field_simp
  have hv2 : ∀ x, HasDerivAt (fun x => -(u 0 * β * sin (β*x)) + deriv u 0 * cos (β*x))
      (-(β^2) * v x) x := by
    intro x
    have hl : HasDerivAt (fun x => β * x) β x := by simpa using (hasDerivAt_id x).const_mul β
    have := (((hl.sin).const_mul (u 0 * β)).neg).add ((hl.cos).const_mul (deriv u 0))
    convert this using 1
    simp only [hv]; field_simp; ring
  have ev : deriv v = fun x => -(u 0 * β * sin (β*x)) + deriv u 0 * cos (β*x) :=
    funext fun x => (hv1 x).deriv
  have hvd : Differentiable ℝ v := fun x => (hv1 x).differentiableAt
  have hvd' : Differentiable ℝ (deriv v) := by rw [ev]; exact fun x => (hv2 x).differentiableAt
  have hvv : ∀ x, deriv (deriv v) x = -(β^2) * v x := by
    intro x; rw [ev]; exact (hv2 x).deriv
  have e : deriv (fun x => u x - v x) = fun x => deriv u x - deriv v x :=
    funext fun x => deriv_sub (hu x) (hvd x)
  have := harmonic_zero (w := fun x => u x - v x) (β := β) (hu.sub hvd)
    (by rw [e]; exact hu'.sub hvd')
    (by
      intro x
      have e2 : deriv (deriv (fun x => u x - v x)) x = deriv (deriv u) x - deriv (deriv v) x := by
        rw [e]; exact deriv_sub (hu' x) (hvd' x)
      rw [e2, h, hvv]; ring)
    (by simp [hv])
    (by
      rw [e]; show deriv u 0 - deriv v 0 = 0
      rw [ev]; simp [hβ])
  intro x
  have h1 : u x - v x = 0 := (this x).1
  have h2 : u x = v x := by linarith
  exact h2

lemma hd_exp (r x : ℝ) : HasDerivAt (fun x => exp (r * x)) (r * exp (r * x)) x := by
  have := ((hasDerivAt_id x).const_mul r).exp
  simpa [mul_comm] using this

lemma hd_cos (β x : ℝ) : HasDerivAt (fun x => cos (β * x)) (-(β * sin (β * x))) x := by
  have := ((hasDerivAt_id x).const_mul β).cos
  simp only [id] at this
  convert this using 1; ring

lemma hd_sin (β x : ℝ) : HasDerivAt (fun x => sin (β * x)) (β * cos (β * x)) x := by
  have := ((hasDerivAt_id x).const_mul β).sin
  simp only [id] at this
  convert this using 1; ring

lemma const_of_hd {f : ℝ → ℝ} (h : ∀ x, HasDerivAt f 0 x) (x : ℝ) : f x = f 0 :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) x 0

/-- first-order: `y' = r y + z0 e^(s x)`, `s ≠ r`. -/
lemma lin1_ne {y : ℝ → ℝ} {r s z0 : ℝ} (hrs : s ≠ r) (hy : Differentiable ℝ y)
    (h : ∀ x, deriv y x = r * y x + z0 * exp (s * x)) :
    ∀ x, y x = (y 0 - z0 / (s - r)) * exp (r * x) + z0 / (s - r) * exp (s * x) := by
  have hsr : s - r ≠ 0 := sub_ne_zero.2 hrs
  have hd : ∀ x, HasDerivAt (fun x => y x * exp (-r * x) - z0 / (s - r) * exp ((s - r) * x)) 0 x := by
    intro x
    have h1 := (hy x).hasDerivAt.mul (hd_exp (-r) x)
    have h2 := (hd_exp (s - r) x).const_mul (z0 / (s - r))
    convert h1.sub h2 using 1
    have e : exp (s * x) * exp (-r * x) = exp ((s - r) * x) := by
      rw [← exp_add]; ring_nf
    have e3 : z0 / (s - r) * ((s - r) * exp ((s - r) * x)) = z0 * exp ((s - r) * x) := by
      field_simp
    rw [h x, e3, ← e]
    ring
  intro x
  have := const_of_hd hd x
  simp only [mul_zero, exp_zero, mul_one, zero_mul] at this
  have e1 : exp (-r * x) * exp (r * x) = 1 := by rw [← exp_add]; simp
  have e2 : exp ((s - r) * x) * exp (r * x) = exp (s * x) := by rw [← exp_add]; ring_nf
  have : y x * exp (-r * x) = y 0 - z0 / (s - r) + z0 / (s - r) * exp ((s - r) * x) := by linarith
  calc y x = y x * exp (-r * x) * exp (r * x) := by rw [mul_assoc, e1, mul_one]
    _ = _ := by rw [this]; linear_combination (z0 / (s - r)) * e2

/-- first-order: `y' = r y + z0 e^(r x)`. -/
lemma lin1_eq {y : ℝ → ℝ} {r z0 : ℝ} (hy : Differentiable ℝ y)
    (h : ∀ x, deriv y x = r * y x + z0 * exp (r * x)) :
    ∀ x, y x = (y 0 + z0 * x) * exp (r * x) := by
  have hd : ∀ x, HasDerivAt (fun x => y x * exp (-r * x) - z0 * x) 0 x := by
    intro x
    have h1 := (hy x).hasDerivAt.mul (hd_exp (-r) x)
    have h2 := (hasDerivAt_id' x).const_mul z0
    convert h1.sub h2 using 1
    have e : exp (r * x) * exp (-r * x) = 1 := by
      rw [← exp_add]; simp
    rw [h x]
    linear_combination (-z0) * e
  intro x
  have := const_of_hd hd x
  simp only [mul_zero, exp_zero, mul_one, zero_mul, sub_zero] at this
  have e1 : exp (-r * x) * exp (r * x) = 1 := by rw [← exp_add]; simp
  have : y x * exp (-r * x) = y 0 + z0 * x := by linarith
  calc y x = y x * exp (-r * x) * exp (r * x) := by rw [mul_assoc, e1, mul_one]
    _ = _ := by rw [this]

lemma distinct_core {a r1 r2 : ℝ} (ha : a ≠ 0) (hne : r1 ≠ r2) {y : ℝ → ℝ} :
    ConstSol a (-(a * (r1 + r2))) (a * (r1 * r2)) (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = c1 * exp (r1 * x) + c2 * exp (r2 * x) := by
  constructor
  · rintro ⟨hy, hy', h⟩
    set z : ℝ → ℝ := fun x => deriv y x - r2 * y x with hzdef
    have hz1 : ∀ x, HasDerivAt z (deriv (deriv y) x - r2 * deriv y x) x := fun x =>
      (hy' x).hasDerivAt.sub ((hy x).hasDerivAt.const_mul r2)
    have hzd : Differentiable ℝ z := fun x => (hz1 x).differentiableAt
    have hz : ∀ x, deriv z x = r1 * z x := by
      intro x
      rw [(hz1 x).deriv]
      apply mul_left_cancel₀ ha
      have := h x
      simp only [hzdef]
      linear_combination this
    have hzx := ode_exp hzd hz
    have key := lin1_ne (y := y) (r := r2) (s := r1) (z0 := z 0) hne (hy)
      (fun x => by
        have := hzx x
        simp only [hzdef] at this
        linarith)
    refine ⟨z 0 / (r1 - r2), y 0 - z 0 / (r1 - r2), fun x => ?_⟩
    rw [key x]; ring
  · rintro ⟨c1, c2, h⟩
    have : y = fun x => c1 * exp (r1 * x) + c2 * exp (r2 * x) := funext h
    subst this
    refine ConstSol.of_hasDeriv
      (y1 := fun x => c1 * (r1 * exp (r1 * x)) + c2 * (r2 * exp (r2 * x)))
      (y2 := fun x => c1 * (r1 * (r1 * exp (r1 * x))) + c2 * (r2 * (r2 * exp (r2 * x))))
      (fun x => ((hd_exp r1 x).const_mul c1).add ((hd_exp r2 x).const_mul c2))
      (fun x => (((hd_exp r1 x).const_mul r1).const_mul c1).add
        (((hd_exp r2 x).const_mul r2).const_mul c2)) ?_
    intro x; ring

lemma repeated_core {a r : ℝ} (ha : a ≠ 0) {y : ℝ → ℝ} :
    ConstSol a (-(2 * a * r)) (a * r ^ 2) (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = c1 * exp (r * x) + c2 * x * exp (r * x) := by
  constructor
  · rintro ⟨hy, hy', h⟩
    set z : ℝ → ℝ := fun x => deriv y x - r * y x with hzdef
    have hz1 : ∀ x, HasDerivAt z (deriv (deriv y) x - r * deriv y x) x := fun x =>
      (hy' x).hasDerivAt.sub ((hy x).hasDerivAt.const_mul r)
    have hzd : Differentiable ℝ z := fun x => (hz1 x).differentiableAt
    have hz : ∀ x, deriv z x = r * z x := by
      intro x
      rw [(hz1 x).deriv]
      apply mul_left_cancel₀ ha
      have := h x
      simp only [hzdef]
      linear_combination this
    have hzx := ode_exp hzd hz
    have key := lin1_eq (y := y) (r := r) (z0 := z 0) hy
      (fun x => by
        have := hzx x
        simp only [hzdef] at this
        linarith)
    exact ⟨y 0, z 0, fun x => by rw [key x]; ring⟩
  · rintro ⟨c1, c2, h⟩
    have : y = fun x => c1 * exp (r * x) + c2 * x * exp (r * x) := funext h
    subst this
    have hA : ∀ x, HasDerivAt (fun x => c2 * x * exp (r * x))
        (c2 * exp (r * x) + c2 * x * (r * exp (r * x))) x := fun x => by
      have := ((hasDerivAt_id' x).const_mul c2).mul (hd_exp r x)
      convert this using 1; ring
    have hB : ∀ x, HasDerivAt (fun x => c2 * exp (r * x) + c2 * x * (r * exp (r * x)))
        (c2 * (r * exp (r * x)) + (c2 * (r * exp (r * x)) + c2 * x * (r * (r * exp (r * x))))) x :=
      fun x => by
        have := ((hd_exp r x).const_mul c2).add
          (((hasDerivAt_id' x).const_mul c2).mul ((hd_exp r x).const_mul r))
        convert this using 1; ring
    refine ConstSol.of_hasDeriv
      (y1 := fun x => c1 * (r * exp (r * x)) + (c2 * exp (r * x) + c2 * x * (r * exp (r * x))))
      (y2 := fun x => c1 * (r * (r * exp (r * x))) +
        (c2 * (r * exp (r * x)) + (c2 * (r * exp (r * x)) + c2 * x * (r * (r * exp (r * x))))))
      (fun x => ((hd_exp r x).const_mul c1).add (hA x))
      (fun x => (((hd_exp r x).const_mul r).const_mul c1).add (hB x)) ?_
    intro x; ring

lemma complex_core {a α β : ℝ} (ha : a ≠ 0) (hβ : β ≠ 0) {y : ℝ → ℝ} :
    ConstSol a (-(2 * a * α)) (a * (α ^ 2 + β ^ 2)) (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = exp (α * x) * (c1 * cos (β * x) + c2 * sin (β * x)) := by
  constructor
  · rintro ⟨hy, hy', h⟩
    set u : ℝ → ℝ := fun x => y x * exp (-α * x) with hu
    set u1 : ℝ → ℝ := fun x => (deriv y x - α * y x) * exp (-α * x) with hu1
    have hu1d : ∀ x, HasDerivAt u (u1 x) x := fun x => by
      have := (hy x).hasDerivAt.mul (hd_exp (-α) x)
      convert this using 1; simp only [hu1]; ring
    have hu2d : ∀ x, HasDerivAt u1 (-(β ^ 2) * u x) x := fun x => by
      have := (((hy' x).hasDerivAt.sub ((hy x).hasDerivAt.const_mul α))).mul (hd_exp (-α) x)
      simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply] at this
      convert this using 1
      have hh := h x
      have : deriv (deriv y) x = 2 * α * deriv y x - (α ^ 2 + β ^ 2) * y x := by
        apply mul_left_cancel₀ ha; linear_combination hh
      rw [this]; simp only [hu]; ring
    have e1 : deriv u = u1 := funext fun x => (hu1d x).deriv
    have e2 : ∀ x, deriv (deriv u) x = -(β ^ 2) * u x := fun x => by
      rw [e1]; exact (hu2d x).deriv
    have key := harmonic_solve hβ (fun x => (hu1d x).differentiableAt)
      (by rw [e1]; exact fun x => (hu2d x).differentiableAt) e2
    refine ⟨y 0, (deriv y 0 - α * y 0) / β, fun x => ?_⟩
    have k := key x
    have hx : y x = u x * exp (α * x) := by
      simp only [hu]
      rw [mul_assoc, ← exp_add]; simp
    rw [hx, k, e1]
    simp [hu, hu1]
    ring
  · rintro ⟨c1, c2, h⟩
    have : y = fun x => exp (α * x) * (c1 * cos (β * x) + c2 * sin (β * x)) := funext h
    subst this
    set p1 := α * c1 + β * c2
    set q1 := α * c2 - β * c1
    set p2 := α * p1 + β * q1
    set q2 := α * q1 - β * p1
    refine ConstSol.of_hasDeriv
      (y1 := fun x => exp (α * x) * (p1 * cos (β * x) + q1 * sin (β * x)))
      (y2 := fun x => exp (α * x) * (p2 * cos (β * x) + q2 * sin (β * x)))
      (fun x => by
        have := (hd_exp α x).mul ((((hd_cos β x).const_mul c1)).add ((hd_sin β x).const_mul c2))
        simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply] at this
        convert this using 1; simp only [p1, q1]; ring)
      (fun x => by
        have := (hd_exp α x).mul ((((hd_cos β x).const_mul p1)).add ((hd_sin β x).const_mul q1))
        simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply] at this
        convert this using 1; simp only [p2, q2]; ring) ?_
    intro x
    simp only [p1, q1, p2, q2]
    ring

/-! ### Terminology and structure of solution sets -/

/-- OpenStax Calculus 3:§7.1 (CA-666): `y` solves the second-order linear equation `y'' + p y' + q y = f`
on `ℝ` (homogeneous when `f = 0`). -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (linear, homogeneous, nonhomogeneous second-order equation), p. 752"]
def LinSol (p q f : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
    ∀ x, deriv (deriv y) x + p x * deriv y x + q x * y x = f x

/-- OpenStax Calculus 3:§7.1 (CA-668), for two functions: `f, g` are linearly dependent on the set `s` when
some combination with not both coefficients zero vanishes on `s`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (linear dependence of functions), p. 755"]
def LinDepOn (s : Set ℝ) (f g : ℝ → ℝ) : Prop :=
  ∃ c1 c2 : ℝ, (c1 ≠ 0 ∨ c2 ≠ 0) ∧ ∀ x ∈ s, c1 * f x + c2 * g x = 0

lemma LinSol.lin_comb {p q f1 f2 y1 y2 : ℝ → ℝ} (h1 : LinSol p q f1 y1) (h2 : LinSol p q f2 y2)
    (c1 c2 : ℝ) :
    LinSol p q (fun x => c1 * f1 x + c2 * f2 x) (fun x => c1 * y1 x + c2 * y2 x) := by
  obtain ⟨d1, e1, g1⟩ := h1
  obtain ⟨d2, e2, g2⟩ := h2
  have D : deriv (fun x => c1 * y1 x + c2 * y2 x) = fun x => c1 * deriv y1 x + c2 * deriv y2 x :=
    funext fun x => (((d1 x).hasDerivAt.const_mul c1).add ((d2 x).hasDerivAt.const_mul c2)).deriv
  refine ⟨(d1.const_mul c1).add (d2.const_mul c2), ?_, ?_⟩
  · rw [D]; exact (e1.const_mul c1).add (e2.const_mul c2)
  · intro x
    rw [D]
    have DD : deriv (fun x => c1 * deriv y1 x + c2 * deriv y2 x) x =
        c1 * deriv (deriv y1) x + c2 * deriv (deriv y2) x :=
      (((e1 x).hasDerivAt.const_mul c1).add ((e2 x).hasDerivAt.const_mul c2)).deriv
    rw [DD]
    linear_combination c1 * g1 x + c2 * g2 x

/-- OpenStax Calculus 3:Theorem 7.1 (CA-667): superposition for the homogeneous equation. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.1, p. 754"]
theorem superposition {p q y1 y2 : ℝ → ℝ} (h1 : LinSol p q (fun _ => 0) y1)
    (h2 : LinSol p q (fun _ => 0) y2) (c1 c2 : ℝ) :
    LinSol p q (fun _ => 0) (fun x => c1 * y1 x + c2 * y2 x) := by
  have := h1.lin_comb h2 c1 c2
  simpa using this

/-- OpenStax Calculus 3:Theorem 7.4 (CA-678): given a particular solution `yp` of `y'' + p y' + q y = f`,
the solutions are exactly `yp + yc` with `yc` a solution of the complementary equation. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.4, p. 765"]
theorem general_eq_particular_add_complementary {p q f yp : ℝ → ℝ} (hp : LinSol p q f yp)
    (y : ℝ → ℝ) :
    LinSol p q f y ↔ ∃ yc, LinSol p q (fun _ => 0) yc ∧ ∀ x, y x = yp x + yc x := by
  constructor
  · intro hy
    refine ⟨fun x => y x - yp x, ?_, fun x => by ring⟩
    have := hy.lin_comb hp 1 (-1)
    convert this using 1
    · funext x; ring
    · funext x; ring
  · rintro ⟨yc, hc, h⟩
    have e : y = fun x => 1 * yp x + 1 * yc x := funext fun x => by rw [h x]; ring
    have := hp.lin_comb hc 1 1
    rw [e]
    convert this using 1
    funext x; simp

/-- OpenStax Calculus 3:Theorem 7.2 (CA-669), on a set (interval) `s`: two functions are linearly dependent
exactly when one is a constant multiple of the other (a zero function is the multiple `0`). -/
@[kb "openstaxcalculus2016" "3:Theorem 7.2, p. 755"]
theorem linDepOn_iff (s : Set ℝ) (f g : ℝ → ℝ) :
    LinDepOn s f g ↔ (∃ k : ℝ, ∀ x ∈ s, f x = k * g x) ∨ (∃ k : ℝ, ∀ x ∈ s, g x = k * f x) := by
  constructor
  · rintro ⟨c1, c2, hc, h⟩
    by_cases h1 : c1 = 0
    · right
      have h2 : c2 ≠ 0 := hc.resolve_left (not_not.2 h1)
      refine ⟨0, fun x hx => ?_⟩
      have := h x hx
      rw [h1] at this
      simpa [h2] using this
    · left
      refine ⟨-(c2 / c1), fun x hx => ?_⟩
      have := h x hx
      field_simp
      linarith
  · rintro (⟨k, h⟩ | ⟨k, h⟩)
    · exact ⟨1, -k, Or.inl one_ne_zero, fun x hx => by rw [h x hx]; ring⟩
    · exact ⟨-k, 1, Or.inr one_ne_zero, fun x hx => by rw [h x hx]; ring⟩

/-- OpenStax Calculus 3:§7.2 Variation of Parameters (CA-681): if `y1, y2` solve the complementary equation
and `u1, u2` are differentiable with `u1' y1 + u2' y2 = 0` and `u1' y1' + u2' y2' = f`, then
`u1 y1 + u2 y2` is a particular solution. -/
@[kb "openstaxcalculus2016" "3:§7.2 Strategy: Variation of Parameters, p. 772"]
theorem variation_of_parameters {p q f y1 y2 u1 u2 : ℝ → ℝ}
    (h1 : LinSol p q (fun _ => 0) y1) (h2 : LinSol p q (fun _ => 0) y2)
    (hu1 : Differentiable ℝ u1) (hu2 : Differentiable ℝ u2)
    (c1 : ∀ x, deriv u1 x * y1 x + deriv u2 x * y2 x = 0)
    (c2 : ∀ x, deriv u1 x * deriv y1 x + deriv u2 x * deriv y2 x = f x) :
    LinSol p q f (fun x => u1 x * y1 x + u2 x * y2 x) := by
  obtain ⟨d1, e1, g1⟩ := h1
  obtain ⟨d2, e2, g2⟩ := h2
  have D : deriv (fun x => u1 x * y1 x + u2 x * y2 x) =
      fun x => u1 x * deriv y1 x + u2 x * deriv y2 x := by
    funext x
    have := (((hu1 x).hasDerivAt.mul (d1 x).hasDerivAt).add ((hu2 x).hasDerivAt.mul (d2 x).hasDerivAt))
    have h' : HasDerivAt (fun x => u1 x * y1 x + u2 x * y2 x)
        (deriv u1 x * y1 x + u1 x * deriv y1 x + (deriv u2 x * y2 x + u2 x * deriv y2 x)) x := this
    rw [h'.deriv]
    linear_combination c1 x
  have DD : ∀ x, deriv (fun x => u1 x * deriv y1 x + u2 x * deriv y2 x) x =
      deriv u1 x * deriv y1 x + u1 x * deriv (deriv y1) x +
        (deriv u2 x * deriv y2 x + u2 x * deriv (deriv y2) x) := fun x =>
    (((hu1 x).hasDerivAt.mul (e1 x).hasDerivAt).add ((hu2 x).hasDerivAt.mul (e2 x).hasDerivAt)).deriv
  refine ⟨fun x => ((hu1 x).mul (d1 x)).add ((hu2 x).mul (d2 x)), ?_, ?_⟩
  · rw [D]; exact fun x => ((hu1 x).mul (e1 x)).add ((hu2 x).mul (e2 x))
  · intro x
    rw [D, DD]
    linear_combination c2 x + u1 x * g1 x + u2 x * g2 x

/-- Cramer's-rule step of variation of parameters (CA-681): with Wronskian `W = y1 y2' - y1' y2 ≠ 0`,
the two equations force `u1' = -y2 f / W` and `u2' = y1 f / W`. -/
@[kb "openstaxcalculus2016" "3:§7.2 Strategy: Variation of Parameters, p. 772"]
theorem variation_of_parameters_cramer {y1 y2 y1' y2' u1' u2' f : ℝ} (hW : y1 * y2' - y1' * y2 ≠ 0)
    (c1 : u1' * y1 + u2' * y2 = 0) (c2 : u1' * y1' + u2' * y2' = f) :
    u1' = -y2 * f / (y1 * y2' - y1' * y2) ∧ u2' = y1 * f / (y1 * y2' - y1' * y2) := by
  constructor
  · rw [eq_div_iff hW]
    linear_combination y2' * c1 - y2 * c2
  · rw [eq_div_iff hW]
    linear_combination (-y1') * c1 + y1 * c2

/-! ### Constant coefficients -/

/-- Solution of `a y'' + b y' + c y = f` on `ℝ` with constant coefficients (the form of OpenStax Calculus
3:§7.1 and §7.3). -/
lemma constSol_iff_linSol {a b c : ℝ} (ha : a ≠ 0) {f y : ℝ → ℝ} :
    ConstSol a b c f y ↔ LinSol (fun _ => b / a) (fun _ => c / a) (fun x => f x / a) y := by
  unfold ConstSol LinSol
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun x => ?_))
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

lemma ConstSol.sub {a b c : ℝ} (ha : a ≠ 0) {f y1 y2 : ℝ → ℝ} (h1 : ConstSol a b c f y1)
    (h2 : ConstSol a b c f y2) : ConstSol a b c (fun _ => 0) (fun x => y1 x - y2 x) := by
  rw [constSol_iff_linSol ha] at *
  have := h1.lin_comb h2 1 (-1)
  convert this using 1
  · funext x; ring
  · funext x; ring

/-- OpenStax Calculus 3:§7.1 (CA-671): `e^(r x)` solves `a y'' + b y' + c y = 0` exactly when `r` is a root of
the characteristic equation `a r² + b r + c = 0`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Definition (characteristic equation), p. 757"]
theorem exp_solves_iff_characteristic (a b c r : ℝ) :
    ConstSol a b c (fun _ => 0) (fun x => exp (r * x)) ↔ a * r ^ 2 + b * r + c = 0 := by
  have e1 : ∀ x, HasDerivAt (fun x => exp (r * x)) (r * exp (r * x)) x := hd_exp r
  have e2 : ∀ x, HasDerivAt (fun x => r * exp (r * x)) (r * (r * exp (r * x))) x :=
    fun x => (hd_exp r x).const_mul r
  have D1 : deriv (fun x => exp (r * x)) = fun x => r * exp (r * x) := funext fun x => (e1 x).deriv
  have D2 : ∀ x, deriv (deriv (fun x => exp (r * x))) x = r * (r * exp (r * x)) := fun x => by
    rw [D1]; exact (e2 x).deriv
  constructor
  · rintro ⟨-, -, h⟩
    have := h 0
    rw [D2 0] at this
    simp only [D1, mul_zero, exp_zero, mul_one] at this
    linear_combination this
  · intro h
    refine ⟨fun x => (e1 x).differentiableAt, ?_, fun x => ?_⟩
    · rw [D1]; exact fun x => (e2 x).differentiableAt
    · rw [D2, D1]
      have : exp (r * x) * (a * r ^ 2 + b * r + c) = 0 := by rw [h]; ring
      linear_combination this

/-- OpenStax Calculus 3:§7.1 Distinct Real Roots (CA-672). -/
@[kb "openstaxcalculus2016" "3:§7.1 Distinct Real Roots (unnumbered), p. 757"]
theorem general_solution_distinct_real_roots {a b c r1 r2 : ℝ} (ha : a ≠ 0)
    (hr1 : a * r1 ^ 2 + b * r1 + c = 0) (hr2 : a * r2 ^ 2 + b * r2 + c = 0) (hne : r1 ≠ r2)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = c1 * exp (r1 * x) + c2 * exp (r2 * x) := by
  have hb : b = -(a * (r1 + r2)) := by
    apply mul_left_cancel₀ (sub_ne_zero.2 hne)
    linear_combination hr1 - hr2
  have hc : c = a * (r1 * r2) := by linear_combination hr1 - r1 * hb
  subst hc
  subst hb
  exact distinct_core ha hne

/-- OpenStax Calculus 3:§7.1 Single Repeated Real Root (CA-673): `b² = 4 a c`, `r = -b / (2a)`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Single Repeated Real Root (unnumbered), p. 757"]
theorem general_solution_repeated_root {a b c : ℝ} (ha : a ≠ 0) (hd : b ^ 2 = 4 * a * c)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = c1 * exp (-b / (2 * a) * x) + c2 * x * exp (-b / (2 * a) * x) := by
  have hb : b = -(2 * a * (-b / (2 * a))) := by field_simp
  have hc : c = a * (-b / (2 * a)) ^ 2 := by
    apply mul_left_cancel₀ (show (4 * a : ℝ) ≠ 0 by positivity)
    field_simp
    linear_combination (-1 : ℝ) * hd
  generalize -b / (2 * a) = r at hb hc ⊢
  subst hc
  subst hb
  exact repeated_core ha

/-- OpenStax Calculus 3:§7.1 Complex Conjugate Roots (CA-674): `b² < 4 a c`, roots `α ± β i` with
`α = -b/(2a)`, `β = √(4ac - b²)/(2a)`. -/
@[kb "openstaxcalculus2016" "3:§7.1 Complex Conjugate Roots (unnumbered), p. 758"]
theorem general_solution_complex_roots {a b c : ℝ} (ha : a ≠ 0) (hd : b ^ 2 < 4 * a * c)
    (y : ℝ → ℝ) :
    ConstSol a b c (fun _ => 0) y ↔
      ∃ c1 c2 : ℝ, ∀ x, y x = exp (-b / (2 * a) * x) *
        (c1 * cos (√(4 * a * c - b ^ 2) / (2 * a) * x) +
          c2 * sin (√(4 * a * c - b ^ 2) / (2 * a) * x)) := by
  have hpos : 0 < 4 * a * c - b ^ 2 := by linarith
  have hs : √(4 * a * c - b ^ 2) ^ 2 = 4 * a * c - b ^ 2 := Real.sq_sqrt hpos.le
  have hβ : √(4 * a * c - b ^ 2) / (2 * a) ≠ 0 := by
    have := Real.sqrt_pos.2 hpos
    positivity
  have hb : b = -(2 * a * (-b / (2 * a))) := by field_simp
  have hc : c = a * ((-b / (2 * a)) ^ 2 + (√(4 * a * c - b ^ 2) / (2 * a)) ^ 2) := by
    rw [div_pow (√(4 * a * c - b ^ 2)) (2 * a) 2, hs]
    field_simp
    ring
  generalize hα : -b / (2 * a) = α at hb hc ⊢
  generalize hβ' : √(4 * a * c - b ^ 2) / (2 * a) = β at hb hc hβ ⊢
  clear hα hβ' hs hpos hd
  subst hc
  subst hb
  exact complex_core ha hβ

/-! ### Spring-mass systems (§7.3) -/

/-- OpenStax Calculus 3:§7.3 Equations 7.5-7.6 (CA-682): simple harmonic motion `m x'' + k x = 0`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Equations 7.5-7.6 (simple harmonic motion), p. 776"]
theorem simple_harmonic_motion {m k : ℝ} (hm : 0 < m) (hk : 0 < k) (x : ℝ → ℝ) :
    ConstSol m 0 k (fun _ => 0) x ↔
      ∃ c1 c2 : ℝ, ∀ t, x t = c1 * cos (√(k / m) * t) + c2 * sin (√(k / m) * t) := by
  have hkm : 0 < k / m := div_pos hk hm
  have hs : √(k / m) ^ 2 = k / m := Real.sq_sqrt hkm.le
  have hβ : √(k / m) ≠ 0 := (Real.sqrt_pos.2 hkm).ne'
  have e := complex_core (a := m) (α := 0) (β := √(k / m)) hm.ne' hβ (y := x)
  have e1 : (-(2 * m * (0 : ℝ))) = 0 := by ring
  have e2 : m * ((0 : ℝ) ^ 2 + √(k / m) ^ 2) = k := by
    rw [hs]; field_simp; ring
  rw [e1, e2] at e
  simpa using e

/-- OpenStax Calculus 3:Theorem 7.5 (CA-683): amplitude-phase form. For `(c1, c2) ≠ 0`, there are `A = √(c1²+c2²)`
and a phase `φ` (`A sin φ = c1`, `A cos φ = c2`, so `tan φ = c1 / c2` when `c2 ≠ 0`) with
`c1 cos(ω t) + c2 sin(ω t) = A sin(ω t + φ)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.5, p. 778"]
theorem amplitude_phase (c1 c2 ω : ℝ) (h : c1 ≠ 0 ∨ c2 ≠ 0) :
    ∃ A φ : ℝ, 0 < A ∧ A = √(c1 ^ 2 + c2 ^ 2) ∧ A * sin φ = c1 ∧ A * cos φ = c2 ∧
      (c2 ≠ 0 → tan φ = c1 / c2) ∧
      ∀ t, c1 * cos (ω * t) + c2 * sin (ω * t) = A * sin (ω * t + φ) := by
  set z : ℂ := ⟨c2, c1⟩ with hz
  have hA : ‖z‖ = √(c1 ^ 2 + c2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [hz]; ring_nf
  have hpos : 0 < ‖z‖ := by
    rw [hA]; apply Real.sqrt_pos.2
    rcases h with h | h <;> positivity
  have hs : ‖z‖ * sin (Complex.arg z) = c1 := Complex.norm_mul_sin_arg z
  have hc : ‖z‖ * cos (Complex.arg z) = c2 := Complex.norm_mul_cos_arg z
  refine ⟨‖z‖, Complex.arg z, hpos, hA, hs, hc, fun h2 => ?_, fun t => ?_⟩
  · rw [Real.tan_eq_sin_div_cos, ← hs, ← hc]
    rw [← hc] at h2
    have : ‖z‖ ≠ 0 := hpos.ne'
    have h3 : cos (Complex.arg z) ≠ 0 := right_ne_zero_of_mul h2
    field_simp
  · rw [sin_add, ← hs, ← hc]; ring

lemma tendsto_exp_mul_neg {r : ℝ} (hr : r < 0) :
    Filter.Tendsto (fun t : ℝ => exp (r * t)) Filter.atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atTop_of_neg hr)

lemma tendsto_mul_exp_neg {r : ℝ} (hr : r < 0) :
    Filter.Tendsto (fun t : ℝ => t * exp (r * t)) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (Filter.tendsto_id.const_mul_atTop (neg_pos.2 hr))
  have h2 := h.const_mul (-r)⁻¹
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  have hr' : r ≠ 0 := hr.ne
  simp only [Function.comp, id]
  have : -(-r * t) = r * t := by ring
  rw [this, pow_one]
  field_simp

lemma tendsto_osc_decay {α : ℝ} (hα : α < 0) (c1 c2 β : ℝ) :
    Filter.Tendsto (fun t : ℝ => exp (α * t) * (c1 * cos (β * t) + c2 * sin (β * t)))
      Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm (a := fun t => exp (α * t) * (|c1| + |c2|)) (fun t => ?_) ?_
  · rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    calc |c1 * cos (β * t) + c2 * sin (β * t)|
        ≤ |c1 * cos (β * t)| + |c2 * sin (β * t)| := abs_add_le _ _
      _ ≤ |c1| + |c2| := by
        rw [abs_mul, abs_mul]
        have := abs_cos_le_one (β * t)
        have := abs_sin_le_one (β * t)
        gcongr <;> nlinarith [abs_nonneg c1, abs_nonneg c2, abs_nonneg (cos (β * t)),
          abs_nonneg (sin (β * t))]
  · simpa using (tendsto_exp_mul_neg hα).mul_const (|c1| + |c2|)

/-- OpenStax Calculus 3:§7.3 Case 1, overdamped (CA-684): `b² > 4 m k` (with `m, b, k > 0`) gives two distinct
negative real roots and solutions `c1 e^(r1 t) + c2 e^(r2 t)`, with no oscillation. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 1 overdamped, p. 780"]
theorem overdamped {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k) (hd : 4 * m * k < b ^ 2) :
    ∃ r1 r2 : ℝ, r1 < 0 ∧ r2 < 0 ∧ r1 ≠ r2 ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = c1 * exp (r1 * t) + c2 * exp (r2 * t) := by
  have hpos : 0 < b ^ 2 - 4 * m * k := by linarith
  have hs : √(b ^ 2 - 4 * m * k) ^ 2 = b ^ 2 - 4 * m * k := Real.sq_sqrt hpos.le
  have hs0 : 0 < √(b ^ 2 - 4 * m * k) := Real.sqrt_pos.2 hpos
  have hsb : √(b ^ 2 - 4 * m * k) < b := by
    rw [Real.sqrt_lt' hb]; nlinarith
  set s := √(b ^ 2 - 4 * m * k)
  have hm' : m ≠ 0 := hm.ne'
  have root : ∀ r, (r = (-b + s) / (2 * m) ∨ r = (-b - s) / (2 * m)) → m * r ^ 2 + b * r + k = 0 := by
    intro r hr
    have : m * r ^ 2 + b * r + k = (s ^ 2 - (b ^ 2 - 4 * m * k)) / (4 * m) := by
      rcases hr with rfl | rfl <;> (field_simp; ring)
    rw [this, hs]; simp
  refine ⟨(-b + s) / (2 * m), (-b - s) / (2 * m), ?_, ?_, ?_, fun x => ?_⟩
  · apply div_neg_of_neg_of_pos <;> linarith
  · apply div_neg_of_neg_of_pos <;> linarith
  · intro h
    field_simp at h
    linarith
  · refine general_solution_distinct_real_roots hm' (root _ (Or.inl rfl)) (root _ (Or.inr rfl)) ?_ x
    intro h
    field_simp at h
    linarith

/-- OpenStax Calculus 3:§7.3 Case 2, critically damped (CA-685): `b² = 4 m k` gives one negative root `r` and
solutions `e^(r t) (c1 + c2 t)`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 2 critically damped, p. 782"]
theorem critically_damped {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hd : b ^ 2 = 4 * m * k) :
    ∃ r : ℝ, r < 0 ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = exp (r * t) * (c1 + c2 * t) := by
  refine ⟨-b / (2 * m), div_neg_of_neg_of_pos (by linarith) (by linarith), fun x => ?_⟩
  rw [general_solution_repeated_root hm.ne' hd]
  constructor <;> rintro ⟨c1, c2, h⟩ <;> exact ⟨c1, c2, fun t => by rw [h t]; ring⟩

/-- OpenStax Calculus 3:§7.3 Case 3, underdamped (CA-686): `b² < 4 m k` gives solutions
`e^(α t)(c1 cos β t + c2 sin β t)` with `α < 0`, `β > 0`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 3 underdamped, p. 782"]
theorem underdamped {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hd : b ^ 2 < 4 * m * k) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧ ∀ x : ℝ → ℝ,
      ConstSol m b k (fun _ => 0) x ↔
        ∃ c1 c2 : ℝ, ∀ t, x t = exp (α * t) * (c1 * cos (β * t) + c2 * sin (β * t)) := by
  refine ⟨-b / (2 * m), √(4 * m * k - b ^ 2) / (2 * m),
    div_neg_of_neg_of_pos (by linarith) (by linarith),
    div_pos (Real.sqrt_pos.2 (by linarith)) (by linarith), fun x => ?_⟩
  exact general_solution_complex_roots hm.ne' hd x

/-- OpenStax Calculus 3:§7.3 (CA-686, the remark that every damped solution decays): for `m, b, k > 0`, every
solution of `m x'' + b x' + k x = 0` tends to `0` as `t → ∞`. -/
@[kb "openstaxcalculus2016" "3:§7.3 Case 3 underdamped, p. 782"]
theorem spring_solution_tendsto_zero {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    {x : ℝ → ℝ} (h : ConstSol m b k (fun _ => 0) x) :
    Filter.Tendsto x Filter.atTop (nhds 0) := by
  rcases lt_trichotomy (b ^ 2) (4 * m * k) with hlt | heq | hgt
  · obtain ⟨α, β, hα, -, hiff⟩ := underdamped hm hb hlt
    obtain ⟨c1, c2, hx⟩ := (hiff x).1 h
    rw [show x = _ from funext hx]
    exact tendsto_osc_decay hα c1 c2 β
  · obtain ⟨r, hr, hiff⟩ := critically_damped hm hb heq
    obtain ⟨c1, c2, hx⟩ := (hiff x).1 h
    have h3 : Filter.Tendsto (fun t : ℝ => c1 * exp (r * t) + c2 * (t * exp (r * t)))
        Filter.atTop (nhds (c1 * 0 + c2 * 0)) :=
      ((tendsto_exp_mul_neg hr).const_mul c1).add ((tendsto_mul_exp_neg hr).const_mul c2)
    rw [mul_zero, mul_zero, add_zero] at h3
    refine h3.congr (fun t => ?_)
    rw [hx t]; ring
  · obtain ⟨r1, r2, h1, h2, -, hiff⟩ := overdamped hm hb hk hgt
    obtain ⟨c1, c2, hx⟩ := (hiff x).1 h
    have h3 : Filter.Tendsto (fun t : ℝ => c1 * exp (r1 * t) + c2 * exp (r2 * t))
        Filter.atTop (nhds (c1 * 0 + c2 * 0)) :=
      ((tendsto_exp_mul_neg h1).const_mul c1).add ((tendsto_exp_mul_neg h2).const_mul c2)
    rw [mul_zero, mul_zero, add_zero] at h3
    exact h3.congr (fun t => (hx t).symm)

/-- OpenStax Calculus 3:§7.3 forced vibrations (CA-687): for a forced damped system `m x'' + b x' + k x = f`
(`m, b, k > 0`), any two solutions differ by a transient that tends to `0`, so every solution approaches
any particular (steady-state) solution. -/
@[kb "openstaxcalculus2016" "3:§7.3 Forced vibrations (Eq. 7.8, transient and steady-state solutions), p. 787"]
theorem forced_vibration_transient {m b k : ℝ} (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    {f x xp : ℝ → ℝ} (hx : ConstSol m b k f x) (hxp : ConstSol m b k f xp) :
    Filter.Tendsto (fun t => x t - xp t) Filter.atTop (nhds 0) :=
  spring_solution_tendsto_zero hm hb hk (hx.sub hm.ne' hxp)

/-! ### General solution from two independent solutions (variable continuous coefficients) -/

/-- Gronwall-type step: a nonnegative function with `|E'| ≤ K E` and `E 0 = 0` vanishes on `[-T, T]`. -/
lemma gronwall_zero {E E' : ℝ → ℝ} (hE : ∀ t, HasDerivAt E (E' t) t) {K T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Set.Icc (-T) T, |E' t| ≤ K * E t) (h0 : E 0 = 0) (hnn : ∀ t, 0 ≤ E t) :
    ∀ t ∈ Set.Icc (-T) T, E t = 0 := by
  intro t ht
  rcases le_total 0 t with h | h
  · have hg : ∀ s, HasDerivAt (fun s => E s * exp (-K * s)) ((E' s - K * E s) * exp (-K * s)) s := by
      intro s
      have := (hE s).mul (hd_exp (-K) s)
      convert this using 1; ring
    have anti : AntitoneOn (fun s => E s * exp (-K * s)) (Set.Icc 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      · exact (fun s _ => (hg s).continuousAt.continuousWithinAt)
      · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hg s).deriv]
        have := hb s ⟨by linarith [hs.1], hs.2.le⟩
        have := (abs_le.1 this).2
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_pos _).le
    have := anti ⟨le_refl _, hT⟩ ⟨h, ht.2⟩ h
    have h2 : E t * exp (-K * t) ≤ 0 := by simpa [h0] using this
    have h3 := nonpos_of_mul_nonpos_left h2 (exp_pos _)
    exact le_antisymm h3 (hnn t)
  · have hg : ∀ s, HasDerivAt (fun s => E s * exp (K * s)) ((E' s + K * E s) * exp (K * s)) s := by
      intro s
      have := (hE s).mul (hd_exp K s)
      convert this using 1; ring
    have mono : MonotoneOn (fun s => E s * exp (K * s)) (Set.Icc (-T) 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc (-T) 0)
      · exact (fun s _ => (hg s).continuousAt.continuousWithinAt)
      · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hg s).deriv]
        have := hb s ⟨hs.1.le, by linarith [hs.2]⟩
        have := (abs_le.1 this).1
        exact mul_nonneg (by linarith) (exp_pos _).le
    have := mono ⟨ht.1, h⟩ ⟨by linarith, le_refl _⟩ h
    have h2 : E t * exp (K * t) ≤ 0 := by simpa [h0] using this
    have h3 := nonpos_of_mul_nonpos_left h2 (exp_pos _)
    exact le_antisymm h3 (hnn t)

/-- Uniqueness for the initial value problem of `y'' + p y' + q y = 0` with continuous coefficients. -/
lemma linSol_unique {p q w : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hw : LinSol p q (fun _ => 0) w) (h0 : w 0 = 0) (h0' : deriv w 0 = 0) :
    ∀ x, w x = 0 ∧ deriv w x = 0 := by
  obtain ⟨d, e, g⟩ := hw
  intro x
  set T := |x| with hTdef
  have hT : 0 ≤ T := abs_nonneg x
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨Cq, hCq⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn hq.continuousOn
  have hCp0 : 0 ≤ Cp := (norm_nonneg _).trans (hCp 0 ⟨by linarith, hT⟩)
  have hCq0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq 0 ⟨by linarith, hT⟩)
  let E : ℝ → ℝ := fun t => w t ^ 2 + deriv w t ^ 2
  let E' : ℝ → ℝ := fun t => 2 * w t * deriv w t +
    2 * deriv w t * (-(p t * deriv w t) - q t * w t)
  have hE : ∀ t, HasDerivAt E (E' t) t := by
    intro t
    have := ((d t).hasDerivAt.pow 2).add (((e t).hasDerivAt).pow 2)
    convert this using 1
    have := g t
    have h' : deriv (deriv w) t = -(p t * deriv w t) - q t * w t := by simp at this; linarith
    simp only [E', h']; simp
  have hbd : ∀ t ∈ Set.Icc (-T) T, |E' t| ≤ (1 + Cq + 2 * Cp) * E t := by
    intro t ht
    have hp1 := (abs_le.1 (by simpa [Real.norm_eq_abs] using hCp t ht))
    have hq1 := (abs_le.1 (by simpa [Real.norm_eq_abs] using hCq t ht))
    set a := w t
    set b := deriv w t
    have s1 := sq_nonneg (a + b)
    have s2 := sq_nonneg (a - b)
    have m1 := mul_nonneg (sub_nonneg.2 hq1.2) s1
    have m2 := mul_nonneg (by linarith [hq1.1] : 0 ≤ Cq + q t) s2
    have m3 := mul_nonneg (by linarith [hp1.1] : 0 ≤ Cp + p t) (sq_nonneg b)
    have m4 := mul_nonneg (sub_nonneg.2 hp1.2) (sq_nonneg b)
    have m5 := mul_nonneg hCp0 (sq_nonneg a)
    have m6 := mul_nonneg hCp0 (sq_nonneg b)
    rw [abs_le]
    simp only [E', E]
    constructor <;> nlinarith [mul_nonneg (by linarith [hq1.1] : 0 ≤ Cq + q t) s2,
      mul_nonneg (sub_nonneg.2 hq1.2) s1, mul_nonneg (sub_nonneg.2 hq1.2) s2,
      mul_nonneg (by linarith [hq1.1] : 0 ≤ Cq + q t) s1]
  have hz := gronwall_zero hE (K := 1 + Cq + 2 * Cp) hT hbd (by simp [E, h0, h0'])
    (fun t => by positivity)
  have := hz x ⟨by linarith [neg_abs_le x], le_abs_self x⟩
  simp only [E] at this
  constructor <;> nlinarith [sq_nonneg (w x), sq_nonneg (deriv w x)]

lemma deriv_comb {y1 y2 : ℝ → ℝ} (h1 : Differentiable ℝ y1) (h2 : Differentiable ℝ y2) (c1 c2 x : ℝ) :
    deriv (fun x => c1 * y1 x + c2 * y2 x) x = c1 * deriv y1 x + c2 * deriv y2 x :=
  (((h1 x).hasDerivAt.const_mul c1).add ((h2 x).hasDerivAt.const_mul c2)).deriv

/-- OpenStax Calculus 3:Theorem 7.3 (CA-670), for continuous coefficients on `ℝ`: if `y1, y2` are linearly
independent solutions of `y'' + p y' + q y = 0`, every solution is `c1 y1 + c2 y2`. -/
@[kb "openstaxcalculus2016" "3:Theorem 7.3, p. 756"]
theorem general_solution_of_independent {p q y1 y2 : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
    (h1 : LinSol p q (fun _ => 0) y1) (h2 : LinSol p q (fun _ => 0) y2)
    (hind : ¬ LinDepOn Set.univ y1 y2) {y : ℝ → ℝ} (hy : LinSol p q (fun _ => 0) y) :
    ∃ c1 c2 : ℝ, ∀ x, y x = c1 * y1 x + c2 * y2 x := by
  have h1' := h1
  have h2' := h2
  obtain ⟨d1, e1, -⟩ := h1
  obtain ⟨d2, e2, -⟩ := h2
  -- the Wronskian at 0 is nonzero
  have hW : y1 0 * deriv y2 0 - deriv y1 0 * y2 0 ≠ 0 := by
    intro hW
    have key : ∀ c1 c2 : ℝ, (c1 ≠ 0 ∨ c2 ≠ 0) → c1 * y1 0 + c2 * y2 0 = 0 →
        c1 * deriv y1 0 + c2 * deriv y2 0 = 0 → LinDepOn Set.univ y1 y2 := by
      intro c1 c2 hc a b
      refine ⟨c1, c2, hc, fun x _ => ?_⟩
      have hs := superposition h1' h2' c1 c2
      have := linSol_unique hp hq hs (by simpa using a) (by rw [deriv_comb d1 d2]; exact b) x
      simpa using this.1
    by_cases hA : y2 0 ≠ 0 ∨ y1 0 ≠ 0
    · refine hind (key (y2 0) (-y1 0) (by rcases hA with h | h <;> simp [h]) (by ring) ?_)
      linear_combination -hW
    · push_neg at hA
      by_cases hB : deriv y2 0 ≠ 0 ∨ deriv y1 0 ≠ 0
      · refine hind (key (deriv y2 0) (-deriv y1 0) (by rcases hB with h | h <;> simp [h]) ?_ (by ring))
        rw [hA.1, hA.2]; ring
      · push_neg at hB
        exact hind (key 1 0 (Or.inl one_ne_zero) (by simp [hA.2]) (by simp [hB.2]))
  set W := y1 0 * deriv y2 0 - deriv y1 0 * y2 0 with hWdef
  have dy := hy.1
  set c1 := (y 0 * deriv y2 0 - deriv y 0 * y2 0) / W with hc1
  set c2 := (y1 0 * deriv y 0 - deriv y1 0 * y 0) / W with hc2
  refine ⟨c1, c2, fun x => ?_⟩
  have hs := superposition h1' h2' c1 c2
  have hw : LinSol p q (fun _ => 0) (fun x => 1 * y x + (-1) * (c1 * y1 x + c2 * y2 x)) := by
    have := hy.lin_comb hs 1 (-1)
    convert this using 1
    funext x; simp
  have hv0 : y 0 = c1 * y1 0 + c2 * y2 0 := by
    rw [hc1, hc2]; field_simp; rw [hWdef]; ring
  have hv1 : deriv y 0 = c1 * deriv y1 0 + c2 * deriv y2 0 := by
    rw [hc1, hc2]; field_simp; rw [hWdef]; ring
  have := linSol_unique hp hq hw (by simp [hv0])
    (by rw [deriv_comb dy hs.1, deriv_comb d1 d2]; linarith) x
  have h5 : 1 * y x + (-1) * (c1 * y1 x + c2 * y2 x) = 0 := this.1
  linarith
