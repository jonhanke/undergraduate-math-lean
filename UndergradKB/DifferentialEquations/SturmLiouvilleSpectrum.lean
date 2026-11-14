import UndergradKB.DifferentialEquations.SturmLiouvilleL2
import UndergradKB.DifferentialEquations.CompactSelfAdjoint
import UndergradKB.DifferentialEquations.DiscreteEnumeration
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Theorem 5.1.1 (Lebl): the eigenvalues of a regular Sturm-Liouville problem

**Theorem 5.1.1.** A regular Sturm-Liouville problem has infinitely many eigenvalues
`λ₁ < λ₂ < λ₃ < ⋯` with `λₙ → +∞`, each with a one-dimensional space of eigenfunctions, and (for regular
problems) `λₙ ≥ 0`.

Wave 2 proved the last two parts (`RegularSL.eigenfunction_unique`, `RegularSL.eigenvalue_nonneg`).  The book
states the first part without proof.  Proof here (the standard one through the Green operator):
* the Green operator `T` at `λ = -1` is compact and symmetric on `L²(r dx)` (`SturmLiouvilleL2.lean`), and
  `λ ↦ -1/(1 + λ)` maps the eigenvalues of the problem into the eigenvalues of `T`, with inverse
  `μ ↦ -1 - μ⁻¹` on the nonzero eigenvalues of `T`;
* eigenvalues `≤ R` of the problem give eigenvalues of `T` of absolute value `≥ 1/(1 + R)`: finitely many
  (`CompactSA.finite_eigenvalues_abs_ge`);
* if there were only finitely many eigenvalues, the range of `T` would be finite-dimensional
  (`CompactSA.finiteDimensional_range_of_finite`, from the spectral theorem); but it contains the classes of
  infinitely many smooth bumps with disjoint supports inside `(a, b)`, which are orthogonal and nonzero;
* an infinite set of reals with finitely many elements below each bound is the range of a strictly increasing
  sequence tending to `+∞` (`exists_strictMono_enum`). -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace RegularSL

variable (S : RegularSL)

/-- Only finitely many eigenvalues lie below any bound. -/
theorem finite_eigenvalues_le (R : ℝ) : {l | S.IsEigenvalue l ∧ l ≤ R}.Finite := by
  rcases lt_or_ge R 0 with hR | hR
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro l ⟨⟨y, hy⟩, hlR⟩
    exact absurd (S.eigenvalue_nonneg hy) (by linarith)
  have hε : 0 < 1 / (1 + R) := by positivity
  have hfin := CompactSA.finite_eigenvalues_abs_ge S.isCompactOperator_greenOp S.isSymmetric_greenOp hε
  refine Set.Finite.of_finite_image (f := fun l : ℝ => -1 / (1 + l)) (hfin.subset ?_) ?_
  · rintro _ ⟨l, ⟨hl, hlR⟩, rfl⟩
    obtain ⟨y, hy⟩ := hl
    have hl0 := S.eigenvalue_nonneg hy
    refine ⟨S.hasEigenvalue_greenOp ⟨y, hy⟩, ?_⟩
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith : (0 : ℝ) < 1 + l)]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro l₁ h₁ l₂ h₂ he
    obtain ⟨y₁, hy₁⟩ := h₁.1
    obtain ⟨y₂, hy₂⟩ := h₂.1
    have p1 := S.eigenvalue_nonneg hy₁
    have p2 := S.eigenvalue_nonneg hy₂
    simp only at he
    field_simp at he
    linarith

/-! ### Bumps with disjoint supports in `(a, b)` -/

/-- Center of the `n`-th bump. -/
noncomputable def bc (n : ℕ) : ℝ := S.a + 3 * (S.b - S.a) / 2 ^ (n + 2)

/-- Outer radius of the `n`-th bump. -/
noncomputable def br (n : ℕ) : ℝ := (S.b - S.a) / 2 ^ (n + 3)

lemma br_pos (n : ℕ) : 0 < S.br n := div_pos (by linarith [S.hab]) (by positivity)

/-- The `n`-th bump: `1` near `bc n`, supported in the ball of radius `br n`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (S.bc n) where
  rIn := S.br n / 2
  rOut := S.br n
  rIn_pos := half_pos (S.br_pos n)
  rIn_lt_rOut := half_lt_self (S.br_pos n)

lemma bump_contDiff (n : ℕ) : ContDiff ℝ 2 (S.bump n) := (S.bump n).contDiff

lemma bump_center (n : ℕ) : S.bump n (S.bc n) = 1 :=
  (S.bump n).one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos (S.br_pos n)).le)

/-- Outside `(bc n - br n, bc n + br n)` the bump vanishes. -/
lemma bump_eq_zero {n : ℕ} {x : ℝ} (hx : x ≤ S.bc n - S.br n ∨ S.bc n + S.br n ≤ x) :
    S.bump n x = 0 := by
  apply (S.bump n).zero_of_le_dist
  show S.br n ≤ dist x (S.bc n)
  rw [Real.dist_eq]
  rcases hx with h | h
  · have := S.br_pos n
    rw [abs_of_nonpos (by linarith)]; linarith
  · have := S.br_pos n
    rw [abs_of_nonneg (by linarith)]; linarith

lemma two_pow_ge_one (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)

/-- `bc n - br n = a + 5 (b - a)/2^(n+3)` and `bc n + br n = a + 7 (b - a)/2^(n+3)`. -/
lemma bc_sub_br (n : ℕ) : S.bc n - S.br n = S.a + 5 * (S.b - S.a) / 2 ^ (n + 3) := by
  unfold bc br; rw [pow_succ 2 (n + 2)]; field_simp; ring

lemma bc_add_br (n : ℕ) : S.bc n + S.br n = S.a + 7 * (S.b - S.a) / 2 ^ (n + 3) := by
  unfold bc br; rw [pow_succ 2 (n + 2)]; field_simp; ring

lemma bump_eq_zero_near_a (n : ℕ) : S.bump n =ᶠ[𝓝 S.a] fun _ => 0 := by
  have h : S.a < S.bc n - S.br n := by
    rw [bc_sub_br]; have := S.hab; have : (0 : ℝ) < 2 ^ (n + 3) := by positivity
    have : 0 < 5 * (S.b - S.a) / 2 ^ (n + 3) := by positivity
    linarith
  filter_upwards [Iio_mem_nhds h] with x hx
  exact S.bump_eq_zero (Or.inl (le_of_lt hx))

lemma bump_eq_zero_near_b (n : ℕ) : S.bump n =ᶠ[𝓝 S.b] fun _ => 0 := by
  have h : S.bc n + S.br n < S.b := by
    rw [bc_add_br]
    have h8 : (8 : ℝ) ≤ 2 ^ (n + 3) := by
      rw [pow_add]; nlinarith [two_pow_ge_one n]
    have hba : 0 < S.b - S.a := by linarith [S.hab]
    have : 7 * (S.b - S.a) / 2 ^ (n + 3) < S.b - S.a := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  filter_upwards [Ioi_mem_nhds h] with x hx
  exact S.bump_eq_zero (Or.inr (le_of_lt hx))

lemma bump_bc (n : ℕ) : S.bump n S.a = 0 ∧ deriv (S.bump n) S.a = 0 ∧
    S.bump n S.b = 0 ∧ deriv (S.bump n) S.b = 0 := by
  refine ⟨(S.bump_eq_zero_near_a n).eq_of_nhds, ?_, (S.bump_eq_zero_near_b n).eq_of_nhds, ?_⟩
  · rw [(S.bump_eq_zero_near_a n).deriv_eq]; simp
  · rw [(S.bump_eq_zero_near_b n).deriv_eq]; simp

lemma bc_mem (n : ℕ) : S.bc n ∈ Icc S.a S.b := by
  have hba : 0 < S.b - S.a := by linarith [S.hab]
  have h4 : (4 : ℝ) ≤ 2 ^ (n + 2) := by rw [pow_add]; nlinarith [two_pow_ge_one n]
  constructor
  · unfold bc; have : 0 ≤ 3 * (S.b - S.a) / 2 ^ (n + 2) := by positivity
    linarith
  · unfold bc
    have : 3 * (S.b - S.a) / 2 ^ (n + 2) ≤ S.b - S.a := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-- Bumps with different indices have disjoint supports. -/
lemma bump_mul_eq_zero {m n : ℕ} (hmn : m < n) (x : ℝ) : S.bump m x * S.bump n x = 0 := by
  rcases le_or_gt x (S.bc n + S.br n) with h | h
  · -- then `x ≤ bc m - br m`
    have hba : 0 < S.b - S.a := by linarith [S.hab]
    have hle : S.bc n + S.br n ≤ S.bc m - S.br m := by
      rw [bc_add_br, bc_sub_br]
      have hp : (2 : ℝ) ^ (m + 3) * 2 ≤ 2 ^ (n + 3) := by
        rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hpos : (0 : ℝ) < 2 ^ (m + 3) := by positivity
      have : 7 * (S.b - S.a) / 2 ^ (n + 3) ≤ 7 * (S.b - S.a) / (2 ^ (m + 3) * 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      have : 7 * (S.b - S.a) / (2 ^ (m + 3) * 2) ≤ 5 * (S.b - S.a) / 2 ^ (m + 3) := by
        rw [div_le_div_iff₀ (by positivity) hpos]; nlinarith
      linarith
    rw [S.bump_eq_zero (Or.inl (h.trans hle)), zero_mul]
  · rw [S.bump_eq_zero (n := n) (Or.inr h.le), mul_zero]

/-! ### Infinitely many eigenvalues -/

/-- The set of eigenvalues is infinite. -/
theorem infinite_eigenvalues : {l | S.IsEigenvalue l}.Infinite := by
  intro hfin
  set T := S.greenOp
  have hsub : {μ : ℝ | μ ≠ 0 ∧ Module.End.HasEigenvalue (T : Module.End ℝ (Lp ℝ 2 S.wμ)) μ}
      ⊆ (fun l : ℝ => -1 / (1 + l)) '' {l | S.IsEigenvalue l} := by
    rintro μ ⟨hμ, hev⟩
    refine ⟨-1 - μ⁻¹, S.isEigenvalue_of_hasEigenvalue hμ hev, ?_⟩
    simp only
    field_simp
    ring
  have hFD := CompactSA.finiteDimensional_range_of_finite S.isCompactOperator_greenOp
    S.isSymmetric_greenOp ((hfin.image _).subset hsub)
  -- the bumps give an infinite linearly independent family in the range
  have hmem : ∀ n, S.toL2 (S.bump n) (S.bump_contDiff n).continuous ∈
      LinearMap.range (T : Lp ℝ 2 S.wμ →ₗ[ℝ] Lp ℝ 2 S.wμ) := fun n => by
    obtain ⟨a0, a1, b0, b1⟩ := S.bump_bc n
    exact S.toL2_mem_range (S.bump_contDiff n) (by rw [a0, a1]; ring) (by rw [b0, b1]; ring)
  set v : ℕ → LinearMap.range (T : Lp ℝ 2 S.wμ →ₗ[ℝ] Lp ℝ 2 S.wμ) := fun n => ⟨_, hmem n⟩
  have hli : LinearIndependent ℝ (fun n => S.toL2 (S.bump n) (S.bump_contDiff n).continuous) := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun n => ?_) ?_
    · exact S.toL2_ne_zero _ (S.bc_mem n) (by rw [S.bump_center n]; norm_num)
    · intro m n hmn
      rw [S.inner_toL2]
      have : ∀ t, S.r t * (S.bump m t * S.bump n t) = 0 := fun t => by
        rcases lt_or_gt_of_ne hmn with h | h
        · rw [S.bump_mul_eq_zero h t, mul_zero]
        · rw [mul_comm (S.bump m t), S.bump_mul_eq_zero h t, mul_zero]
      simp [this]
  have hli' : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (LinearMap.range (T : Lp ℝ 2 S.wμ →ₗ[ℝ] Lp ℝ 2 S.wμ)).subtype hli
  have := hli'.finite_of_isNoetherian
  exact (not_finite ℕ)

/-- **Lebl, Theorem 5.1.1.**  The eigenvalues of a regular Sturm-Liouville problem
`(p y')' - q y + λ r y = 0`, `α₁ y(a) - α₂ y'(a) = 0`, `β₁ y(b) + β₂ y'(b) = 0` form a sequence
`λ₁ < λ₂ < λ₃ < ⋯` with `λₙ → +∞`; to each `λₙ` there is, up to a constant multiple, a single eigenfunction;
and `λₙ ≥ 0` for all `n` (the problem is regular in the book's sense, `RegularSL`: `q ≥ 0` and
`α₁, α₂, β₁, β₂ ≥ 0`). -/
@[kb "lebldiffyqs2026" "Theorem 5.1.1, p. 275"]
theorem sturm_liouville_eigenvalues :
    ∃ ev : ℕ → ℝ, StrictMono ev ∧ Tendsto ev atTop atTop ∧
      (∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) ∧ (∀ n, 0 ≤ ev n) ∧
      ∀ n {y₁ y₂ : ℝ → ℝ}, S.IsEigenfunction (ev n) y₁ → S.IsSolution (ev n) 0 y₂ →
        ∃ c : ℝ, ∀ t ∈ Icc S.a S.b, y₂ t = c * y₁ t := by
  obtain ⟨ev, hmono, hrange, htend⟩ := exists_strictMono_enum S.infinite_eigenvalues fun R => by
    simpa [Set.inter_def] using S.finite_eigenvalues_le R
  have hiff : ∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l := fun l => by
    have := congrArg (l ∈ ·) hrange
    simp only [mem_range, mem_ofPred_eq, eq_iff_iff] at this
    exact this.symm
  refine ⟨ev, hmono, htend, hiff, fun n => ?_, fun n y₁ y₂ h₁ h₂ => S.eigenfunction_unique h₁ h₂⟩
  obtain ⟨y, hy⟩ := (hiff (ev n)).2 ⟨n, rfl⟩
  exact S.eigenvalue_nonneg hy

end RegularSL

end UndergradKB.DifferentialEquations
