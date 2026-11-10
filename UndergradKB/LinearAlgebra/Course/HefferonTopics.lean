import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.Algebra.LinearRecurrence
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Algebra.Field.ZMod
import UndergradKB.Common.Attr

/-! # Hefferon Topics (Hefferon-only rows)

Topic rows: Fields (LA-029), Markov chains, Orthonormal matrices, Projective geometry,
Linear recurrences. -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix

/-- The two-element set `ZMod 2` is a field (so are `ℝ`, `ℚ`, `ℂ`). -/
@[kb "hefferon2020" "Topic-Fields.1, p. 163"]
theorem hefferon_Topic_Fields_1 :
    Nonempty (Field (ZMod 2)) ∧ Nonempty (Field ℝ) ∧ Nonempty (Field ℚ) ∧ Nonempty (Field ℂ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- A transition matrix (nonnegative entries, each column summing to one) carries a probability
vector to a probability vector: `p(n+1) = M p(n)`. -/
@[kb "hefferon2020" "Topic-Markov.1, p. 324"]
theorem hefferon_Topic_Markov_1 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hM : M ∈ colStochastic ℝ n) (p : n → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    (∀ i, 0 ≤ (M *ᵥ p) i) ∧ ∑ i, (M *ᵥ p) i = 1 :=
  ⟨fun i => Finset.sum_nonneg fun j _ => mul_nonneg (nonneg_of_mem_colStochastic hM) (hp.1 j),
    by rw [sum_mulVec_of_mem_colStochastic hM, hp.2]⟩

/-- A distance-preserving map of the plane is a distance-preserving linear map plus a
translation (in particular, one fixing the origin is linear). -/
@[kb "hefferon2020" "Topic-Orthonormal.2, p. 330"]
theorem hefferon_Topic_Orthonormal_2 (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Isometry f) :
    ∃ L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2), ∀ x, f x = L x + f 0 := by
  let A := hf.affineIsometryOfStrictConvexSpace
  refine ⟨A.linearIsometry, fun x => ?_⟩
  have h := A.toAffineMap.linear_apply_vsub x 0
  simp only [vsub_eq_sub, sub_zero] at h
  have h2 : A.linearIsometry x = f x - f 0 := by
    have e : A.linearIsometry x = A.linear x := rfl
    rw [e, h]; rfl
  rw [h2]; abel

/-- A point of the projective plane is a nonzero vector of `ℝ^3` up to a nonzero scalar. -/
@[kb "hefferon2020" "Topic-Projective.1, p. 393"]
theorem hefferon_Topic_Projective_1 (v w : Fin 3 → ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℝ v hv = Projectivization.mk ℝ w hw ↔ ∃ c : ℝ, c ≠ 0 ∧ c • w = v := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun h0 => hv ?_, hc⟩
    rw [← hc, h0, zero_smul]
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩

/-- Two distinct points of a projective space lie on at most one line (a 2-dimensional
subspace). -/
@[kb "hefferon2020" "Topic-Projective.4, p. 396"]
theorem hefferon_Topic_Projective_4 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {x y : Projectivization K V} (hxy : x ≠ y) (p q : Submodule K V)
    (hp1 : Module.finrank K p = 2) (hq1 : Module.finrank K q = 2)
    (hp2 : x ∈ p.projectivization) (hp3 : y ∈ p.projectivization)
    (hq2 : x ∈ q.projectivization) (hq3 : y ∈ q.projectivization) : p = q :=
  Projectivization.line_unique hxy p q hp1 hq1 hp2 hp3 hq2 hq3

/-- The solutions of a homogeneous linear recurrence of order `k` form a `k`-dimensional space,
isomorphic to `K^k` by taking the first `k` values. -/
@[kb "hefferon2020" "Topic-Recurrence.2, p. 486"]
theorem hefferon_Topic_Recurrence_2 {K : Type*} [Field K] (E : LinearRecurrence K) :
    Module.finrank K E.solSpace = E.order ∧
      ∃ e : E.solSpace ≃ₗ[K] (Fin E.order → K), ∀ u i, e u i = (u : ℕ → K) i :=
  ⟨by simpa using E.toInit.finrank_eq, ⟨E.toInit, fun _ _ => rfl⟩⟩

/-- Binet's formula: `F(n) = (φ^n - ψ^n) / √5` where `φ, ψ` are the roots of `x² - x - 1`. -/
@[kb "hefferon2020" "Topic-Recurrence.1, p. 485"]
theorem hefferon_Topic_Recurrence_1 (n : ℕ) :
    ((Nat.fib n : ℕ) : ℝ) =
      (((1 + √5) / 2) ^ n - ((1 - √5) / 2) ^ n) / √5 ∧
    ((1 + √5) / 2) ^ 2 - (1 + √5) / 2 - 1 = 0 ∧ ((1 - √5) / 2) ^ 2 - (1 - √5) / 2 - 1 = 0 := by
  have h5 : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  refine ⟨Real.coe_fib_eq n, ?_, ?_⟩ <;> nlinarith [h5]

end UndergradKB.LinearAlgebra.Course
