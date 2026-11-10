import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import UndergradKB.Common.Attr

/-! # Assorted applications: Gershgorin disks, Fibonacci by diagonalization, voting paradox,
dimensional analysis. -/

namespace UndergradKB.LinearAlgebra

open Matrix

/-! ## Gershgorin disks (Axler 5.66, 5.67) -/

section Gershgorin

variable {K V ι : Type*} [NormedField K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- The Gershgorin disk of an operator `T` with respect to a basis `b`, for the index `j`: the
closed disk around the diagonal entry `A j j` of the matrix `A` of `T` whose radius is the sum of
the absolute values of the other entries of row `j` (Axler 5.66). -/
noncomputable def gershgorinDisk (b : Module.Basis ι K V) (T : Module.End K V) (j : ι) : Set K :=
  Metric.closedBall (LinearMap.toMatrix b b T j j)
    (∑ k ∈ Finset.univ.erase j, ‖LinearMap.toMatrix b b T j k‖)

/-- Gershgorin disk theorem: each eigenvalue of an operator lies in some Gershgorin disk with
respect to any basis. (Stated over any normed field, so for `ℝ` and `ℂ`.) -/
@[kb "axler2024" "5.67, p. 189"]
theorem axler_5_67 (b : Module.Basis ι K V) (T : Module.End K V) {μ : K}
    (hμ : T.HasEigenvalue μ) : ∃ j, μ ∈ gershgorinDisk b T j := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hc : b.repr v ≠ 0 := by
    intro h
    exact hv.2 (b.repr.injective (by rw [h]; simp))
  have hA : Module.End.HasEigenvalue (Matrix.toLin' (LinearMap.toMatrix b b T)) μ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(b.repr v)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have h1 := LinearMap.toMatrix_mulVec_repr b b T v
      have h2 : T v = μ • v := hv.apply_eq_smul
      rw [h2, map_smul] at h1
      exact h1
    · simpa using hc
  exact eigenvalue_mem_ball hA

end Gershgorin

/-! ## Fibonacci numbers by diagonalization (Axler Exercise 5D.21) -/

section Fibonacci

open Real

/-- The operator `T(x, y) = (y, x + y)` on `ℝ²`. -/
noncomputable def fibOperator : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![0, 1; 1, 1]

lemma fibOperator_apply (x : Fin 2 → ℝ) : fibOperator x = ![x 1, x 0 + x 1] := by
  ext i
  fin_cases i <;> simp [fibOperator, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

lemma fibOperator_pow_eigen {μ : ℝ} {x : Fin 2 → ℝ} (h : fibOperator x = μ • x) (n : ℕ) :
    (fibOperator ^ n) x = μ ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, pow_succ]

lemma fibOperator_eigen_goldenRatio : fibOperator ![1, goldenRatio] = goldenRatio • ![1, goldenRatio] := by
  rw [fibOperator_apply]
  ext i
  fin_cases i
  · simp
  · simp
    have := goldenRatio_sq
    first | done | nlinarith

lemma fibOperator_eigen_goldenConj : fibOperator ![1, goldenConj] = goldenConj • ![1, goldenConj] := by
  rw [fibOperator_apply]
  ext i
  fin_cases i
  · simp
  · simp
    have := goldenConj_sq
    first | done | nlinarith

lemma fib_pair_li : LinearIndependent ℝ ![(![1, goldenRatio] : Fin 2 → ℝ), ![1, goldenConj]] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  have hne : goldenRatio - goldenConj ≠ 0 := by
    rw [goldenRatio_sub_goldenConj]; positivity
  have : s * (goldenRatio - goldenConj) = 0 := by
    have : t = -s := by linarith
    subst this
    linarith
  have hs : s = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hne
  constructor
  · exact hs
  · linarith

/-- Fibonacci numbers by diagonalization. For `T(x, y) = (y, x + y)` on `ℝ²`:
(a) `Tⁿ(0, 1) = (Fₙ, Fₙ₊₁)`; (b) the eigenvalues of `T` are exactly the golden ratio and its
conjugate; (c) `(1, φ)` and `(1, ψ)` are eigenvectors forming a basis of `ℝ²`;
(d) Binet's formula `Fₙ = (φⁿ - ψⁿ)/√5` follows from writing `(0,1)` in that basis;
(e) `Fₙ` is the integer nearest to `φⁿ/√5`. -/
@[kb "axler2024" "Ex5D.21, p. 192"]
theorem axler_5D_21 :
    (∀ n : ℕ, (fibOperator ^ n) ![0, 1] = ![(Nat.fib n : ℝ), (Nat.fib (n + 1) : ℝ)]) ∧
    (∀ μ : ℝ, Module.End.HasEigenvalue fibOperator μ ↔ μ = goldenRatio ∨ μ = goldenConj) ∧
    (Module.End.HasEigenvector fibOperator goldenRatio ![1, goldenRatio] ∧
      Module.End.HasEigenvector fibOperator goldenConj ![1, goldenConj] ∧
      ∃ B : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ),
        B 0 = ![1, goldenRatio] ∧ B 1 = ![1, goldenConj]) ∧
    (∀ n : ℕ, (fibOperator ^ n) ![0, 1] = (√5)⁻¹ • (goldenRatio ^ n • ![1, goldenRatio] -
        goldenConj ^ n • ![1, goldenConj]) ∧
      (Nat.fib n : ℝ) = (goldenRatio ^ n - goldenConj ^ n) / √5) ∧
    (∀ n : ℕ, |goldenRatio ^ n / √5 - (Nat.fib n : ℝ)| < 1 / 2 ∧
      round (goldenRatio ^ n / √5) = Nat.fib n) := by
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hvec : (![0, 1] : Fin 2 → ℝ) = (√5)⁻¹ • (![1, goldenRatio] - ![1, goldenConj]) := by
    ext i
    fin_cases i
    · simp
    · simp
  have ha : ∀ n : ℕ, (fibOperator ^ n) ![0, 1] = ![(Nat.fib n : ℝ), (Nat.fib (n + 1) : ℝ)] := by
    intro n
    induction n with
    | zero => ext i; fin_cases i <;> simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, fibOperator_apply]
      ext i
      fin_cases i
      · simp
      · simp [Nat.fib_add_two]
  have hd : ∀ n : ℕ, (fibOperator ^ n) ![0, 1] = (√5)⁻¹ • (goldenRatio ^ n • ![1, goldenRatio] -
        goldenConj ^ n • ![1, goldenConj]) := by
    intro n
    rw [hvec, map_smul, map_sub, fibOperator_pow_eigen fibOperator_eigen_goldenRatio,
      fibOperator_pow_eigen fibOperator_eigen_goldenConj]
  have hbinet : ∀ n : ℕ, (Nat.fib n : ℝ) = (goldenRatio ^ n - goldenConj ^ n) / √5 := by
    intro n
    have := congrFun (ha n) 0
    rw [hd n] at this
    simp at this
    rw [← this]; ring
  refine ⟨ha, ?_, ⟨?_, ?_, ?_⟩, fun n => ⟨hd n, hbinet n⟩, fun n => ?_⟩
  · intro μ
    constructor
    · intro hμ
      obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
      have h := hv.apply_eq_smul
      rw [fibOperator_apply] at h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      have hv0 : v 0 ≠ 0 := by
        intro e
        apply hv.2
        ext i; fin_cases i
        · simpa using e
        · simp; rw [e] at h0; simpa [e] using h0
      have hq : μ ^ 2 - μ - 1 = 0 := by
        have : v 0 * (μ ^ 2 - μ - 1) = 0 := by
          rw [h0] at h1
          linear_combination -h1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hv0
        · exact h
      have : (μ - goldenRatio) * (μ - goldenConj) = 0 := by
        have e1 := goldenRatio_add_goldenConj
        have e2 := goldenRatio_mul_goldenConj
        nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl)
      · exact Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.2 fibOperator_eigen_goldenRatio, by
            intro h; have := congrFun h 0; simp at this⟩
      · exact Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.2 fibOperator_eigen_goldenConj, by
            intro h; have := congrFun h 0; simp at this⟩
  · exact ⟨Module.End.mem_eigenspace_iff.2 fibOperator_eigen_goldenRatio, by
      intro h; have := congrFun h 0; simp at this⟩
  · exact ⟨Module.End.mem_eigenspace_iff.2 fibOperator_eigen_goldenConj, by
      intro h; have := congrFun h 0; simp at this⟩
  · refine ⟨basisOfLinearIndependentOfCardEqFinrank fib_pair_li (by simp), ?_, ?_⟩ <;> simp
  · have hpsi : |goldenConj ^ n| < 1 ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · right; exact h
      · left
        rw [abs_pow]
        apply pow_lt_one₀ (abs_nonneg _) _ (by omega)
        rw [abs_lt]; exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
    have hbound : |goldenConj ^ n| ≤ 1 := by
      rw [abs_pow]
      apply pow_le_one₀ (abs_nonneg _)
      rw [abs_le]; exact ⟨neg_one_lt_goldenConj.le, by linarith [goldenConj_neg]⟩
    have hsq : (2 : ℝ) < √5 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hdiff : goldenRatio ^ n / √5 - (Nat.fib n : ℝ) = goldenConj ^ n / √5 := by
      rw [hbinet n]; ring
    have hlt : |goldenRatio ^ n / √5 - (Nat.fib n : ℝ)| < 1 / 2 := by
      rw [hdiff, abs_div, abs_of_pos hs5, div_lt_iff₀ hs5]
      nlinarith
    refine ⟨hlt, ?_⟩
    rw [abs_lt] at hlt
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith [hlt.1, hlt.2]

end Fibonacci

/-! ## Voting paradoxes (Hefferon, Topic: Voting Paradoxes) -/

/-- Voting paradox, necessary condition. After cancelling opposite preference orders, each of the
three rows leaves an integer `a`, `b`, `c` (positive: the lists lean one way, negative: the other,
zero: perfect cancellation) and the group totals are `-a+b+c`, `a-b+c`, `a+b-c`. If the three
totals are all nonnegative then `a, b, c` are all nonnegative, and likewise for nonpositive: a
majority cycle needs all three remaining sets of lists to have the same spin. -/
@[kb "hefferon2020" "Topic-Voting.1, p. 173"]
theorem hefferon_Topic_Voting_1 (a b c : ℤ) :
    ((0 ≤ -a + b + c ∧ 0 ≤ a - b + c ∧ 0 ≤ a + b - c) → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∧
    ((-a + b + c ≤ 0 ∧ a - b + c ≤ 0 ∧ a + b - c ≤ 0) → a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0) := by
  constructor <;> intro h <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Dimensional analysis (Hefferon, Topic: Dimensional Analysis) -/

section DimAnalysis

variable {r q : Type*} [Fintype q]

/-- The product `∏ mⱼ ^ pⱼ` of positive quantities `m` raised to the powers `p`. -/
noncomputable def dimMonomial (m p : q → ℝ) : ℝ := ∏ j, m j ^ p j

/-- The exponent vectors of the dimensionless products form a vector space: for a matrix `D`
whose column `j` is the dimensional formula of the `j`-th quantity (rows are base dimensions),
the product with exponents `p` has dimensional formula `D p`, so the dimensionless ones are the
kernel of `D`, a subspace; and on positive quantities the vector space operations correspond to
multiplying two products (addition of exponents) and raising a product to a power (scalar
multiplication of the exponents). -/
@[kb "hefferon2020" "Topic-DimAnalysis.2, p. 178"]
theorem hefferon_Topic_DimAnalysis_2 (D : Matrix r q ℝ) :
    ∃ S : Submodule ℝ (q → ℝ), (∀ p, p ∈ S ↔ D *ᵥ p = 0) ∧
      (∀ m : q → ℝ, (∀ j, 0 < m j) →
        (∀ p p', dimMonomial m (p + p') = dimMonomial m p * dimMonomial m p') ∧
        (∀ (c : ℝ) p, dimMonomial m (c • p) = dimMonomial m p ^ c)) := by
  refine ⟨LinearMap.ker (Matrix.mulVecLin D), fun p => by simp, fun m hm => ⟨fun p p' => ?_, fun c p => ?_⟩⟩
  · simp only [dimMonomial, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Real.rpow_add (hm j) _ _
  · simp only [dimMonomial, Pi.smul_apply, smul_eq_mul]
    rw [← Real.finsetProd_rpow _ _ (fun j _ => Real.rpow_nonneg (hm j).le _)]
    exact Finset.prod_congr rfl fun j _ => by rw [← Real.rpow_mul (hm j).le, mul_comm]

end DimAnalysis

/-! ## Distance-preserving maps of the plane (Hefferon, Topic: Orthonormal Matrices) -/

section Plane

/-- The Euclidean plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Distance-preserving maps of the plane preserve collinearity (of any set, and of triples
in both directions), betweenness, nondegenerate triangles (and their side lengths), and circles. -/
@[kb "hefferon2020" "Topic-Orthonormal.6, p. 329"]
theorem hefferon_Topic_Orthonormal_6 (f : Plane → Plane) (hf : Isometry f) :
    (∀ s : Set Plane, Collinear ℝ s → Collinear ℝ (f '' s)) ∧
    (∀ x y z : Plane, Collinear ℝ {x, y, z} ↔ Collinear ℝ {f x, f y, f z}) ∧
    (∀ x y z : Plane, Wbtw ℝ x y z ↔ Wbtw ℝ (f x) (f y) (f z)) ∧
    (∀ x y z : Plane, AffineIndependent ℝ ![x, y, z] ↔ AffineIndependent ℝ ![f x, f y, f z]) ∧
    (∀ x y : Plane, dist (f x) (f y) = dist x y) ∧
    (∀ (c : Plane) (r : ℝ), f '' Metric.sphere c r = Metric.sphere (f c) r) := by
  set A := hf.affineIsometryOfStrictConvexSpace with hA
  have hAf : ⇑A = f := rfl
  have hinj : Function.Injective f := hf.injective
  have hAI : ∀ x y z : Plane, AffineIndependent ℝ ![x, y, z] ↔
      AffineIndependent ℝ ![f x, f y, f z] := by
    intro x y z
    have e : (![f x, f y, f z] : Fin 3 → Plane) = f ∘ ![x, y, z] := by
      funext i; fin_cases i <;> rfl
    rw [e]
    constructor
    · intro h
      exact h.map' A.toAffineMap hinj
    · intro h
      exact AffineIndependent.of_comp A.toAffineMap h
  refine ⟨?_, ?_, ?_, hAI, hf.dist_eq, ?_⟩
  · intro s hs
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hs ⊢
    obtain ⟨p₀, v, h⟩ := hs
    refine ⟨f p₀, A.toAffineMap.linear v, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨r, hr⟩ := h p hp
    refine ⟨r, ?_⟩
    rw [hr]
    calc f (r • v +ᵥ p₀) = A.toAffineMap (r • v +ᵥ p₀) := rfl
      _ = A.toAffineMap.linear (r • v) +ᵥ A.toAffineMap p₀ := A.toAffineMap.map_vadd _ _
      _ = r • A.toAffineMap.linear v +ᵥ f p₀ := by rw [map_smul]; rfl
  · intro x y z
    rw [collinear_iff_not_affineIndependent_set, collinear_iff_not_affineIndependent_set,
      hAI x y z]
  · intro x y z
    exact (Function.Injective.wbtw_map_iff (f := A.toAffineMap) hinj).symm
  · intro c r
    have hlin : ∀ x, f x = A.linearIsometry x + f 0 := by
      intro x
      have h := A.toAffineMap.linear_apply_vsub x 0
      simp only [vsub_eq_sub, sub_zero] at h
      have h2 : A.linearIsometry x = f x - f 0 := by
        have e : A.linearIsometry x = A.toAffineMap.linear x := rfl
        rw [e, h]; rfl
      rw [h2]; abel
    have hsurj : Function.Surjective f := by
      intro y
      let e := A.linearIsometry.toLinearIsometryEquiv rfl
      refine ⟨e.symm (y - f 0), ?_⟩
      rw [hlin]
      have h3 : A.linearIsometry (e.symm (y - f 0)) = y - f 0 := by
        have := e.apply_symm_apply (y - f 0)
        simpa [e] using this
      rw [h3]; abel
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.mem_sphere] at hx ⊢
      rw [hf.dist_eq]; exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      refine ⟨x, ?_, rfl⟩
      rw [Metric.mem_sphere] at hy ⊢
      rw [← hf.dist_eq]; exact hy

/-- A `2 × 2` matrix with orthonormal columns is determined by its first column `(a, b)` up to a
sign: it is the rotation `[[a, -b], [b, a]]` or the reflection `[[a, b], [b, -a]]`. -/
theorem orthonormal_two_by_two (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : Mᵀ * M = 1) :
    M = !![M 0 0, -M 1 0; M 1 0, M 0 0] ∨ M = !![M 0 0, M 1 0; M 1 0, -M 0 0] := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  set a := M 0 0
  set b := M 1 0
  set c := M 0 1
  set d := M 1 1
  have hc : c = -b * (a * d - b * c) := by linear_combination (-c) * h00 + a * h01
  have hd : d = a * (a * d - b * c) := by linear_combination (-d) * h00 + b * h01
  have ht : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h00 + h11 - (a * c + b * d) * h01
  rcases mul_eq_zero.1 ht with h | h
  · left
    have h1 : a * d - b * c = 1 := by linarith
    rw [h1] at hc hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · right
    have h1 : a * d - b * c = -1 := by linarith
    rw [h1] at hc hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- A `2 × 2` orthonormal matrix with first column `(a, b)` is a rotation or a reflection, and
every rigid motion of the plane is a rotation or reflection followed by a translation. -/
@[kb "hefferon2020" "Topic-Orthonormal.5, p. 332"]
theorem hefferon_Topic_Orthonormal_5 :
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ, Mᵀ * M = 1 →
      M = !![M 0 0, -M 1 0; M 1 0, M 0 0] ∨ M = !![M 0 0, M 1 0; M 1 0, -M 0 0]) ∧
    (∀ f : Plane → Plane, Isometry f → ∃ (a b t₀ t₁ : ℝ), a ^ 2 + b ^ 2 = 1 ∧
      ((∀ x, f x 0 = a * x 0 - b * x 1 + t₀ ∧ f x 1 = b * x 0 + a * x 1 + t₁) ∨
       (∀ x, f x 0 = a * x 0 + b * x 1 + t₀ ∧ f x 1 = b * x 0 - a * x 1 + t₁))) := by
  refine ⟨orthonormal_two_by_two, fun f hf => ?_⟩
  let A := hf.affineIsometryOfStrictConvexSpace
  have hlin : ∀ x, f x = A.linearIsometry x + f 0 := by
    intro x
    have h := A.toAffineMap.linear_apply_vsub x 0
    simp only [vsub_eq_sub, sub_zero] at h
    have h2 : A.linearIsometry x = f x - f 0 := by
      have e : A.linearIsometry x = A.toAffineMap.linear x := rfl
      rw [e, h]; rfl
    rw [h2]; abel
  set L := A.linearIsometry with hL
  let e0 : Plane := EuclideanSpace.single 0 1
  let e1 : Plane := EuclideanSpace.single 1 1
  have hx : ∀ x : Plane, x = x 0 • e0 + x 1 • e1 := by
    intro x
    ext i
    fin_cases i <;> simp [e0, e1]
  have hLx : ∀ x : Plane, L x = x 0 • L e0 + x 1 • L e1 := by
    intro x
    conv_lhs => rw [hx x]
    rw [map_add, map_smul, map_smul]
  have hco : ∀ x : Plane, f x 0 = x 0 * L e0 0 + x 1 * L e1 0 + f 0 0 ∧
      f x 1 = x 0 * L e0 1 + x 1 * L e1 1 + f 0 1 := by
    intro x
    rw [hlin, hLx]
    simp
  have i00 : inner ℝ (L e0) (L e0) = 1 := by rw [L.inner_map_map]; simp [e0]
  have i11 : inner ℝ (L e1) (L e1) = 1 := by rw [L.inner_map_map]; simp [e1]
  have i01 : inner ℝ (L e0) (L e1) = 0 := by
    rw [L.inner_map_map]; simp [e0, e1, EuclideanSpace.inner_single_left]
  simp only [PiLp.inner_apply, Fin.sum_univ_two] at i00 i11 i01
  simp at i00 i11 i01
  obtain ⟨a, ha⟩ : ∃ a, L e0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, L e0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, L e1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, L e1 1 = d := ⟨_, rfl⟩
  simp only [ha, hb, hc, hd] at i00 i11 i01 hco
  have hc' : c = -b * (a * d - b * c) := by
    linear_combination (-c) * i00 + a * i01
  have hd' : d = a * (a * d - b * c) := by
    linear_combination (-d) * i00 + b * i01
  have ht : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * i00 + i11 - (a * c + b * d) * i01
  refine ⟨a, b, f 0 0, f 0 1, by linear_combination i00, ?_⟩
  rcases mul_eq_zero.1 ht with h | h
  · left
    have h1 : a * d - b * c = 1 := by linarith
    rw [h1] at hc' hd'
    intro x
    obtain ⟨h0, h1'⟩ := hco x
    rw [h0, h1', hc', hd']
    constructor <;> ring
  · right
    have h1 : a * d - b * c = -1 := by linarith
    rw [h1] at hc' hd'
    intro x
    obtain ⟨h0, h1'⟩ := hco x
    rw [h0, h1', hc', hd']
    constructor <;> ring

end Plane

/-! ## The method of powers (Hefferon, Topic: Method of Powers) -/

section Powers

open Filter Topology

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

private lemma powers_pow_apply {n : ℕ} (T : Module.End 𝕜 V) (ζ : Fin n → V) (l : Fin n → 𝕜)
    (hζ : ∀ i, T (ζ i) = l i • ζ i) (c : Fin n → 𝕜) (k : ℕ) :
    (T ^ k) (∑ i, c i • ζ i) = ∑ i, (c i * l i ^ k) • ζ i := by
  have h1 : ∀ i k, (T ^ k) (ζ i) = l i ^ k • ζ i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hζ, smul_smul, pow_succ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, h1, smul_smul]

/-- Method of powers. Let `T` have eigenvectors `ζ₀, …, ζₙ` with eigenvalues `λ₀, …, λₙ`, where
`λ₀` is nonzero and strictly dominant (`|λᵢ| < |λ₀|` for `i ≠ 0`), and let `v = Σ cᵢ ζᵢ` with
`c₀ ≠ 0` (and `ζ₀ ≠ 0`). Then `Tᵏ v / λ₀ᵏ` converges to `c₀ ζ₀`; the error is bounded by a
constant times `rᵏ` whenever `|λᵢ / λ₀| ≤ r < 1` for all `i ≠ 0` (geometric rate); and the ratio
of norms `‖Tᵏ⁺¹ v‖ / ‖Tᵏ v‖` converges to `|λ₀|`. -/
@[kb "hefferon2020" "Topic-Powers.1, p. 474"]
theorem hefferon_Topic_Powers_1 {n : ℕ} (T : Module.End 𝕜 V) (ζ : Fin (n + 1) → V)
    (l : Fin (n + 1) → 𝕜) (hζ : ∀ i, T (ζ i) = l i • ζ i) (hζ0 : ζ 0 ≠ 0) (hl0 : l 0 ≠ 0)
    (hdom : ∀ i, i ≠ 0 → ‖l i‖ < ‖l 0‖) (c : Fin (n + 1) → 𝕜) (hc : c 0 ≠ 0) :
    Tendsto (fun k : ℕ => (l 0 ^ k)⁻¹ • (T ^ k) (∑ i, c i • ζ i)) atTop (𝓝 (c 0 • ζ 0)) ∧
    (∀ r : ℝ, (∀ i, i ≠ 0 → ‖l i / l 0‖ ≤ r) → ∀ k : ℕ,
      ‖(l 0 ^ k)⁻¹ • (T ^ k) (∑ i, c i • ζ i) - c 0 • ζ 0‖ ≤
        (∑ i ∈ Finset.univ.erase 0, ‖c i‖ * ‖ζ i‖) * r ^ k) ∧
    Tendsto (fun k : ℕ => ‖(T ^ (k + 1)) (∑ i, c i • ζ i)‖ / ‖(T ^ k) (∑ i, c i • ζ i)‖)
      atTop (𝓝 ‖l 0‖) := by
  set v := ∑ i, c i • ζ i with hv
  have hw : ∀ k : ℕ, (l 0 ^ k)⁻¹ • (T ^ k) v = ∑ i, (c i * (l i / l 0) ^ k) • ζ i := by
    intro k
    rw [hv, powers_pow_apply T ζ l hζ c k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, div_pow]
    congr 1
    field_simp
  have hlim : Tendsto (fun k : ℕ => (l 0 ^ k)⁻¹ • (T ^ k) v) atTop (𝓝 (c 0 • ζ 0)) := by
    simp_rw [hw]
    have : (c 0 • ζ 0) = ∑ i : Fin (n + 1), (if i = 0 then c 0 • ζ 0 else 0) := by simp
    rw [this]
    refine tendsto_finsetSum _ fun i _ => ?_
    by_cases hi : i = 0
    · subst hi
      simp [div_self hl0]
    · simp only [hi, ite_false]
      have h1 : ‖l i / l 0‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.2 hl0)]; exact hdom i hi
      have h2 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1
      have h3 := (h2.const_mul (c i)).smul_const (ζ i)
      simpa using h3
  refine ⟨hlim, ?_, ?_⟩
  · intro r hr k
    have : (l 0 ^ k)⁻¹ • (T ^ k) v - c 0 • ζ 0 =
        ∑ i ∈ Finset.univ.erase 0, (c i * (l i / l 0) ^ k) • ζ i := by
      rw [hw k, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      simp [div_self hl0]
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    rw [norm_smul, norm_mul, norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) (hr i hi0) k
    calc ‖c i‖ * ‖l i / l 0‖ ^ k * ‖ζ i‖ = (‖c i‖ * ‖ζ i‖) * ‖l i / l 0‖ ^ k := by ring
      _ ≤ (‖c i‖ * ‖ζ i‖) * r ^ k := by gcongr
  · have hne : ‖c 0 • ζ 0‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact smul_ne_zero hc hζ0
    have hn : Tendsto (fun k : ℕ => ‖(l 0 ^ k)⁻¹ • (T ^ k) v‖) atTop (𝓝 ‖c 0 • ζ 0‖) :=
      hlim.norm
    have hn1 : Tendsto (fun k : ℕ => ‖(l 0 ^ (k + 1))⁻¹ • (T ^ (k + 1)) v‖) atTop
        (𝓝 ‖c 0 • ζ 0‖) := hn.comp (tendsto_add_atTop_nat 1)
    have hq := (hn1.div hn hne).const_mul ‖l 0‖
    have hq' : Tendsto (fun k : ℕ => ‖l 0‖ * (‖(l 0 ^ (k + 1))⁻¹ • (T ^ (k + 1)) v‖ /
        ‖(l 0 ^ k)⁻¹ • (T ^ k) v‖)) atTop (𝓝 ‖l 0‖) := by
      simpa [div_self hne] using hq
    refine hq'.congr fun k => ?_
    have hl : 0 < ‖l 0‖ := norm_pos_iff.2 hl0
    simp only [norm_smul, norm_inv, norm_pow]
    have hp : 0 < ‖l 0‖ ^ k := pow_pos hl k
    rw [pow_succ, ← mul_div_assoc]
    have e1 : (‖l 0‖ ^ k * ‖l 0‖)⁻¹ * ‖(T ^ (k + 1)) v‖ = (‖l 0‖ ^ k)⁻¹ * ‖l 0‖⁻¹ * ‖(T ^ (k + 1)) v‖ := by
      rw [mul_inv]
    rw [e1]
    field_simp

end Powers

end UndergradKB.LinearAlgebra
