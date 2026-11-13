import UndergradKB.DifferentialEquations.SturmLiouville
import UndergradKB.DifferentialEquations.Picard
import UndergradKB.Common.Attr

/-! # Fredholm alternative for regular Sturm-Liouville problems: existence (Lebl Theorem 5.1.3)

Wave 2 (`SturmLiouville.lean`) proved uniqueness: if `λ` is not an eigenvalue, the nonhomogeneous problem has at
most one solution.  Here we prove existence, without a Green's function: extend the coefficients of
`y'' + (p'/p) y' + ((λ r - q)/p) y = f/p` continuously to the whole line by clamping the argument to `[a, b]`,
take a solution `w` of the homogeneous equation whose initial data `(w(a), w'(a)) = (α₂, α₁)` satisfy the left
boundary condition, and a particular solution `y_p` with zero initial data; then `y_p + k w` solves the
problem for a suitable `k` unless `w` satisfies the right boundary condition too, in which case `w` is an
eigenfunction.

Hypotheses beyond the book: those of `RegularSL` (wave 2), and `f` continuous on `[a, b]` only. -/

namespace UndergradKB.DifferentialEquations

open Set

namespace RegularSL

variable (S : RegularSL)

/-- Clamp to `[a, b]`. -/
noncomputable def clampI (t : ℝ) : ℝ := max S.a (min S.b t)

lemma clampI_mem (t : ℝ) : S.clampI t ∈ Icc S.a S.b :=
  ⟨le_max_left _ _, max_le S.hab.le (min_le_left _ _)⟩

lemma clampI_of_mem {t : ℝ} (ht : t ∈ Icc S.a S.b) : S.clampI t = t := by
  unfold clampI
  rw [min_eq_right ht.2, max_eq_right ht.1]

lemma continuous_clampI : Continuous S.clampI := by
  unfold clampI; fun_prop

lemma pc_ne (t : ℝ) : S.p (S.clampI t) ≠ 0 := (S.p_pos _ (S.clampI_mem t)).ne'

/-- Extended coefficient of `y'`. -/
noncomputable def cA (t : ℝ) : ℝ := deriv S.p (S.clampI t) / S.p (S.clampI t)

/-- Extended coefficient of `y`. -/
noncomputable def cB (l t : ℝ) : ℝ := (l * S.r (S.clampI t) - S.q (S.clampI t)) / S.p (S.clampI t)

/-- Extended right-hand side. -/
noncomputable def cF (f : ℝ → ℝ) (t : ℝ) : ℝ := f (S.clampI t) / S.p (S.clampI t)

lemma continuous_cA : Continuous S.cA :=
  ((S.p_C1.continuous_deriv le_rfl).comp S.continuous_clampI).div
    (S.p_C1.continuous.comp S.continuous_clampI) S.pc_ne

lemma continuous_cB (l : ℝ) : Continuous (S.cB l) := by
  have hr : Continuous fun t => S.r (S.clampI t) :=
    S.r_cont.comp_continuous S.continuous_clampI S.clampI_mem
  have hq : Continuous fun t => S.q (S.clampI t) :=
    S.q_cont.comp_continuous S.continuous_clampI S.clampI_mem
  exact ((continuous_const.mul hr).sub hq).div (S.p_C1.continuous.comp S.continuous_clampI) S.pc_ne

lemma continuous_cF {f : ℝ → ℝ} (hf : ContinuousOn f (Icc S.a S.b)) : Continuous (S.cF f) :=
  (hf.comp_continuous S.continuous_clampI S.clampI_mem).div
    (S.p_C1.continuous.comp S.continuous_clampI) S.pc_ne

/-- A solution of the extended equation on `ℝ` is `C²` and solves the Sturm-Liouville equation on `[a, b]`. -/
lemma solves_of_lin2 {l : ℝ} {f g y : ℝ → ℝ} (hgc : Continuous g)
    (hg : ∀ t ∈ Icc S.a S.b, g t = f t / S.p t) (hs : SolvesLin2 S.cA (S.cB l) g univ y) :
    ContDiff ℝ 2 y ∧ ∀ t ∈ Icc S.a S.b,
      deriv (fun t => S.p t * deriv y t) t - S.q t * y t + l * S.r t * y t = f t := by
  have hd : Differentiable ℝ y := fun t => (hs t trivial).1
  have hd2 : Differentiable ℝ (deriv y) := fun t => (hs t trivial).2.1
  have hdd : deriv (deriv y) = fun t => g t - S.cA t * deriv y t - S.cB l t * y t := by
    funext t
    have := (hs t trivial).2.2
    linarith
  have hc : Continuous (deriv (deriv y)) := by
    rw [hdd]
    have := hd.continuous
    have := hd2.continuous
    have := S.continuous_cA
    have := S.continuous_cB l
    fun_prop
  have h1 : ContDiff ℝ 1 (deriv y) := contDiff_one_iff_deriv.2 ⟨hd2, hc⟩
  refine ⟨?_, fun t ht => ?_⟩
  · have : ContDiff ℝ (1 + 1) y := contDiff_succ_iff_deriv.2 ⟨hd, by simp, h1⟩
    have e : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    rwa [e] at this
  · have dp : DifferentiableAt ℝ S.p t := (S.p_C1.differentiable one_ne_zero) t
    have hD : deriv (fun t => S.p t * deriv y t) t
        = deriv S.p t * deriv y t + S.p t * deriv (deriv y) t :=
      (dp.hasDerivAt.mul (hd2 t).hasDerivAt).deriv
    have e := (hs t trivial).2.2
    have hct := S.clampI_of_mem ht
    have hp := S.p_pos t ht
    rw [hg t ht] at e
    simp only [cA, cB, hct] at e
    rw [hD]
    field_simp at e
    linear_combination e

/-- Linear combination `y + k w`. -/
lemma lin2_add_smul {A B g : ℝ → ℝ} {y w : ℝ → ℝ} (hy : SolvesLin2 A B g univ y)
    (hw : SolvesLin2 A B 0 univ w) (k : ℝ) : SolvesLin2 A B g univ (fun t => y t + k * w t) := by
  have dy : Differentiable ℝ y := fun t => (hy t trivial).1
  have dw : Differentiable ℝ w := fun t => (hw t trivial).1
  have dy2 : Differentiable ℝ (deriv y) := fun t => (hy t trivial).2.1
  have dw2 : Differentiable ℝ (deriv w) := fun t => (hw t trivial).2.1
  have h1 : deriv (fun t => y t + k * w t) = fun t => deriv y t + k * deriv w t := by
    funext t; exact ((dy t).hasDerivAt.add ((dw t).hasDerivAt.const_mul k)).deriv
  have h2 : ∀ t, deriv (deriv (fun t => y t + k * w t)) t = deriv (deriv y) t + k * deriv (deriv w) t := by
    intro t; rw [h1]; exact (((dy2 t).hasDerivAt).add ((dw2 t).hasDerivAt.const_mul k)).deriv
  intro t _
  refine ⟨(dy t).add ((dw t).const_mul k), ?_, ?_⟩
  · rw [h1]; exact (dy2 t).add ((dw2 t).const_mul k)
  · rw [h2, h1]
    have e1 := (hy t trivial).2.2
    have e2 := (hw t trivial).2.2
    simp only [Pi.zero_apply] at e2
    simp only
    linear_combination e1 + k * e2

/-- **Existence for the nonhomogeneous problem when `λ` is not an eigenvalue (DE-157, existence half).** -/
theorem exists_solution_of_not_eigenvalue {l : ℝ} (hl : ¬ S.IsEigenvalue l) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc S.a S.b)) : ∃ y, S.IsSolution l f y := by
  have hcA := (continuousOn_univ.2 S.continuous_cA)
  have hcB := (continuousOn_univ.2 (S.continuous_cB l))
  have hcF := (continuousOn_univ.2 (S.continuous_cF hf))
  have hc0 : ContinuousOn (0 : ℝ → ℝ) univ := continuousOn_const
  obtain ⟨yp, hyp, hyp0, hyp1⟩ := lin2_exists isOpen_univ ordConnected_univ hcA hcB hcF
    (t₀ := S.a) trivial 0 0
  obtain ⟨w, hw, hw0, hw1⟩ := lin2_exists isOpen_univ ordConnected_univ hcA hcB hc0
    (t₀ := S.a) trivial S.α₂ S.α₁
  have hFg : ∀ t ∈ Icc S.a S.b, S.cF f t = f t / S.p t := fun t ht => by
    simp [cF, S.clampI_of_mem ht]
  have hF0 : ∀ t ∈ Icc S.a S.b, (0 : ℝ → ℝ) t = (0 : ℝ → ℝ) t / S.p t := fun t _ => by simp
  obtain ⟨wC, wE⟩ := S.solves_of_lin2 (f := 0) continuous_const hF0 hw
  have dw : DifferentiableAt ℝ w S.a := (hw S.a trivial).1
  have dyp : DifferentiableAt ℝ yp S.a := (hyp S.a trivial).1
  by_cases hW : S.β₁ * w S.b + S.β₂ * deriv w S.b = 0
  · exfalso
    apply hl
    refine ⟨w, ⟨wC, wE, ?_, hW⟩, ?_⟩
    · rw [hw0, hw1]; ring
    · by_contra hall
      push Not at hall
      have hz : ∀ t ∈ Icc S.a S.b, w t = (fun _ => (0:ℝ)) t := hall
      have hder : HasDerivWithinAt w (deriv w S.a) (Icc S.a S.b) S.a :=
        (dw.hasDerivAt).hasDerivWithinAt
      have hder0 : HasDerivWithinAt (fun _ : ℝ => (0:ℝ)) (0:ℝ) (Icc S.a S.b) S.a :=
        hasDerivWithinAt_const _ _ _
      have := (uniqueDiffOn_Icc S.hab S.a (left_mem_Icc.2 S.hab.le)).eq_deriv _ hder
        (hder0.congr hz (hz S.a (left_mem_Icc.2 S.hab.le)))
      rw [hw1] at this
      have h0 : S.α₂ = 0 := by have := hz S.a (left_mem_Icc.2 S.hab.le); simpa [hw0] using this
      exact S.α_ne ⟨this, h0⟩
  · set k := -(S.β₁ * yp S.b + S.β₂ * deriv yp S.b) / (S.β₁ * w S.b + S.β₂ * deriv w S.b) with hk
    have hz := lin2_add_smul hyp hw k
    obtain ⟨zC, zE⟩ := S.solves_of_lin2 (f := f) (S.continuous_cF hf) hFg hz
    have dz : ∀ x, deriv (fun t => yp t + k * w t) x = deriv yp x + k * deriv w x := by
      intro x
      exact (((hyp x trivial).1).hasDerivAt.add (((hw x trivial).1).hasDerivAt.const_mul k)).deriv
    refine ⟨fun t => yp t + k * w t, zC, zE, ?_, ?_⟩
    · simp only [dz, hyp0, hyp1, hw0, hw1]; ring
    · simp only [dz]
      have : k * (S.β₁ * w S.b + S.β₂ * deriv w S.b) = -(S.β₁ * yp S.b + S.β₂ * deriv yp S.b) := by
        rw [hk]; field_simp
      linear_combination this

/-- **Fredholm alternative for regular Sturm-Liouville problems (DE-157).**  Either `λ` is an eigenvalue,
or for every `f` continuous on `[a, b]` the nonhomogeneous problem `(p y')' - q y + λ r y = f` with the
boundary conditions has a solution, and it is unique on `[a, b]`.  Beyond the book: `f` is only required
continuous on `[a, b]`, and solutions are `C²` on `ℝ` (as in `RegularSL.IsSolution`); uniqueness is on
`[a, b]`. -/
@[kb "lebldiffyqs2026" "Theorem 5.1.3, p. 278"]
theorem fredholm_alternative (l : ℝ) :
    S.IsEigenvalue l ∨ ∀ f : ℝ → ℝ, ContinuousOn f (Icc S.a S.b) →
      ∃ y, S.IsSolution l f y ∧ ∀ z, S.IsSolution l f z → ∀ t ∈ Icc S.a S.b, z t = y t := by
  by_cases hl : S.IsEigenvalue l
  · exact Or.inl hl
  · refine Or.inr fun f hf => ?_
    obtain ⟨y, hy⟩ := S.exists_solution_of_not_eigenvalue hl hf
    exact ⟨y, hy, fun z hz => S.solution_unique_of_not_eigenvalue hl hz hy⟩

end RegularSL

end UndergradKB.DifferentialEquations
