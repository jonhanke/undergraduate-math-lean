import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import UndergradKB.Common.Attr

/-! # Euclidean space and its planes (Petrunin, Section 15C, p. 122)

The book's Euclidean space is `ℝ³` with the Euclidean metric; its planes are the solution sets of
`ax + by + cz + d = 0` with `(a, b, c) ≠ 0`, and each plane is isometric to the Euclidean plane.
We state this for a three-dimensional real inner product space `V` (e.g. `EuclideanSpace ℝ (Fin 3)`,
where `⟪n, x⟫ = ax + by + cz`), planes being two-dimensional affine subspaces. -/

namespace UndergradKB.Geometry

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Each plane is isometric to the Euclidean plane (p. 122).** A two-dimensional affine subspace of
a real inner product space (more generally of a Euclidean affine space) is isometric to
`EuclideanSpace ℝ (Fin 2)`. -/
@[kb "petrunin2025" "Definition of the Euclidean space, p. 122"]
theorem nonempty_isometryEquiv_plane {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    (s : AffineSubspace ℝ P) [Nonempty s] (h : finrank ℝ s.direction = 2) :
    Nonempty (s ≃ᵢ EuclideanSpace ℝ (Fin 2)) := by
  obtain ⟨p⟩ := ‹Nonempty s›
  have : FiniteDimensional ℝ s.direction := Module.finite_of_finrank_eq_succ h
  let e : s.direction ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((stdOrthonormalBasis ℝ s.direction).reindex (finCongr h)).repr
  exact ⟨(AffineIsometryEquiv.vaddConst ℝ p).symm.toIsometryEquiv.trans e.toIsometryEquiv⟩

/-- The solution set `{x | ⟪n, x⟫ = d}` of a linear equation with `n ≠ 0`, as an affine subspace. -/
def planeOfEq (n : V) (d : ℝ) : AffineSubspace ℝ V where
  carrier := {x | inner ℝ n x = d}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ := by
    simp only [Set.mem_ofPred_eq, vsub_eq_sub, vadd_eq_add] at *
    rw [inner_add_right, inner_smul_right, inner_sub_right, h₁, h₂, h₃]
    ring

theorem mem_planeOfEq {n x : V} {d : ℝ} : x ∈ planeOfEq n d ↔ inner ℝ n x = d := Iff.rfl

theorem direction_planeOfEq {n : V} {d : ℝ} (hn : n ≠ 0) :
    (planeOfEq n d).direction = (ℝ ∙ n)ᗮ := by
  have hne : ((d / inner ℝ n n) • n) ∈ planeOfEq n d := by
    rw [mem_planeOfEq, inner_smul_right]
    field_simp [inner_self_ne_zero.2 hn]
  rw [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show inner ℝ n (x -ᵥ y) = 0
    rw [vsub_eq_sub, inner_sub_right, (mem_planeOfEq).1 hx, (mem_planeOfEq).1 hy, sub_self]
  · intro v hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv
    apply Submodule.subset_span
    refine ⟨v + (d / inner ℝ n n) • n, ?_, (d / inner ℝ n n) • n, hne, by simp⟩
    rw [SetLike.mem_coe, mem_planeOfEq, inner_add_right, hv, zero_add, inner_smul_right]
    field_simp [inner_self_ne_zero.2 hn]

/-- **Planes are the solution sets of linear equations (p. 122).** In a three-dimensional real inner
product space, the set `{x | ⟪n, x⟫ = d}` with `n ≠ 0` is a plane (a two-dimensional affine subspace),
and every plane is of this form. -/
@[kb "petrunin2025" "Definition of the Euclidean space, p. 122"]
theorem plane_iff_eq_planeOfEq (h3 : finrank ℝ V = 3) (s : AffineSubspace ℝ V) :
    ((s : Set V).Nonempty ∧ finrank ℝ s.direction = 2) ↔
      ∃ n : V, n ≠ 0 ∧ ∃ d : ℝ, s = planeOfEq n d := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ h3
  constructor
  · rintro ⟨⟨p, hp⟩, h2⟩
    have hperp : finrank ℝ s.directionᗮ = 1 := by
      have := Submodule.finrank_add_finrank_orthogonal s.direction
      omega
    obtain ⟨n, hn, hspan⟩ := finrank_eq_one_iff'.1 hperp
    have hn' : (n : V) ≠ 0 := fun h => hn (Subtype.ext h)
    have hspan' : s.directionᗮ = ℝ ∙ (n : V) := by
      apply le_antisymm
      · intro w hw
        obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
        rw [Submodule.mem_span_singleton]
        exact ⟨c, by simpa using congrArg Subtype.val hc⟩
      · rw [Submodule.span_singleton_le_iff_mem]; exact n.2
    refine ⟨n, hn', inner ℝ (n : V) p, ?_⟩
    apply AffineSubspace.ext_of_direction_eq
    · rw [direction_planeOfEq hn', ← hspan', Submodule.orthogonal_orthogonal]
    · exact ⟨p, hp, (mem_planeOfEq).2 rfl⟩
  · rintro ⟨n, hn, d, rfl⟩
    refine ⟨⟨(d / inner ℝ n n) • n, ?_⟩, ?_⟩
    · show inner ℝ n ((d / inner ℝ n n) • n) = d
      rw [inner_smul_right]
      field_simp [inner_self_ne_zero.2 hn]
    · rw [direction_planeOfEq hn]
      have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ n)
      rw [finrank_span_singleton hn] at this
      omega

end UndergradKB.Geometry
