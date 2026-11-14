import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Ring.GeomSum
import UndergradKB.Topology.NSSGroups
import UndergradKB.Topology.PeterWeylOrthogonal
import UndergradKB.Common.Attr

/-! # Compact NSS groups are exactly the compact linear groups (Morris, Theorem A5.0.28, part)

* `eq_one_of_norm_pow_sub_one_le`: in a real normed algebra, if every power of `h` lies within
  distance `c < 1` of `1`, then `h = 1`.  (Cesàro: `N • (h - 1) = (h ^ N - 1) + Σ_{k<N} (h - 1)(1 - h ^ k)`,
  so `N ‖h - 1‖ ≤ c + N c ‖h - 1‖`.)
* `isNSS_of_injective_normedRing`: a topological group with a continuous injective homomorphism into
  the multiplicative monoid of a real normed algebra is NSS; in particular every subgroup of a finite
  product of unitary groups `U(n)` is NSS (`isNSS_unitary_pi`).
* `isNSS_iff_exists_isClosedEmbedding_unitary` (Morris, Theorem A5.0.28, (ii) ⟺ "linear"): a
  compact Hausdorff group is NSS iff it is topologically isomorphic to a closed subgroup of a finite
  product of unitary groups.  The direction "NSS ⟹ linear" is the Peter-Weyl argument of
  `PeterWeylOrthogonal.lean` (wave 3).  What remains for the full theorem (Lie ⟺ NSS ⟺ locally
  euclidean) is Cartan's closed subgroup theorem (closed subgroups of `U(n)` are Lie groups) and the
  invariance of domain for the locally euclidean condition.
-/

open Set Filter Topology

namespace UndergradKB.Topology

/-- In a real normed algebra, if every power of `h` lies within distance `c < 1` of `1`, then
`h = 1`. -/
theorem eq_one_of_norm_pow_sub_one_le {A : Type*} [NormedRing A] [NormedSpace ℝ A] {h : A} {c : ℝ}
    (hc : c < 1) (hpow : ∀ k : ℕ, ‖h ^ k - 1‖ ≤ c) : h = 1 := by
  set x := h - 1 with hx
  have key : ∀ N : ℕ, (N : ℝ) * ‖x‖ ≤ c + N * c * ‖x‖ := by
    intro N
    have hsum : (∑ k ∈ Finset.range N, x) =
        (h ^ N - 1) + ∑ k ∈ Finset.range N, x * (1 - h ^ k) := by
      have : x * (∑ k ∈ Finset.range N, h ^ k) = h ^ N - 1 := by
        rw [hx, mul_geom_sum]
      rw [← this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_sub, mul_one]; abel
    have hnorm : ‖∑ k ∈ Finset.range N, x‖ = N * ‖x‖ := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
        Real.norm_natCast]
    rw [← hnorm, hsum]
    refine (norm_add_le _ _).trans (add_le_add (hpow N) ?_)
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range N, ‖x * (1 - h ^ k)‖ ≤ c * ‖x‖ := by
      intro k _
      refine (norm_mul_le _ _).trans ?_
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans (hpow k)) (norm_nonneg _)
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring_nf; rfl
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hpow 0)
  by_contra hne
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  -- choose `N` with `N (1 - c) ‖x‖ > c`
  obtain ⟨N, hN⟩ := exists_nat_gt (c / ((1 - c) * ‖x‖))
  have h1 : 0 < (1 - c) * ‖x‖ := mul_pos (by linarith) hxpos
  have := key N
  have h2 : c < N * ((1 - c) * ‖x‖) := (div_lt_iff₀ h1).1 hN
  nlinarith

/-- A topological group with a continuous injective homomorphism into the multiplicative monoid of
a real normed algebra has no small subgroups. -/
theorem isNSS_of_injective_normedRing {G A : Type*} [Group G] [TopologicalSpace G] [NormedRing A]
    [NormedSpace ℝ A] (f : G →* A) (hf : Continuous f) (hinj : Function.Injective f) : IsNSS G := by
  refine ⟨f ⁻¹' {a | ‖a - 1‖ < 1 / 2}, ?_, ?_, ?_⟩
  · exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).preimage hf
  · simp
  · intro H hH
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hpow : ∀ k : ℕ, ‖f g ^ k - 1‖ ≤ 1 / 2 := by
      intro k
      rw [← map_pow]
      exact (hH (H.pow_mem hg k)).le
    exact hinj ((eq_one_of_norm_pow_sub_one_le (by norm_num) hpow).trans f.map_one.symm)

section Unitary

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedSpace

/-- The inclusion of a product of unitary groups into the product of the matrix algebras. -/
noncomputable def unitaryPiIncl {ι : Type*} (d : ι → ℕ) :
    ((i : ι) → Matrix.unitaryGroup (Fin (d i)) ℂ) →* ((i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  MonoidHom.pi fun i => (Matrix.unitaryGroup (Fin (d i)) ℂ).subtype.comp (Pi.evalMonoidHom _ i)

theorem continuous_unitaryPiIncl {ι : Type*} (d : ι → ℕ) : Continuous (unitaryPiIncl d) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

theorem injective_unitaryPiIncl {ι : Type*} (d : ι → ℕ) : Function.Injective (unitaryPiIncl d) :=
  fun _ _ h => funext fun i => Subtype.ext (congrFun h i)

/-- A group with a continuous injective homomorphism into a finite product of unitary groups `U(n)`
(for instance any subgroup of such a product) has no small subgroups. -/
theorem isNSS_of_injective_unitary_pi {G ι : Type*} [Fintype ι] [Group G] [TopologicalSpace G]
    (d : ι → ℕ) (f : G →* ((i : ι) → Matrix.unitaryGroup (Fin (d i)) ℂ)) (hf : Continuous f)
    (hinj : Function.Injective f) : IsNSS G :=
  isNSS_of_injective_normedRing ((unitaryPiIncl d).comp f) ((continuous_unitaryPiIncl d).comp hf)
    ((injective_unitaryPiIncl d).comp hinj)

/-- A finite product of unitary groups has no small subgroups. -/
theorem isNSS_unitary_pi {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    IsNSS ((i : ι) → Matrix.unitaryGroup (Fin (d i)) ℂ) :=
  isNSS_of_injective_unitary_pi d (MonoidHom.id _) continuous_id Function.injective_id

end Unitary

universe u

/-- **Morris, Theorem A5.0.28 (TP-500), the NSS condition.**  A compact (Hausdorff) group is an
NSS-group if and only if it is topologically isomorphic to a closed subgroup of a finite product of
unitary groups `U(n)` (a compact linear group).  The book's further equivalence with "Lie group" and
"locally euclidean" needs Cartan's closed subgroup theorem, which is not in Mathlib. -/
@[kb "morris2024" "Theorem A5.0.28, p. 510"]
theorem isNSS_iff_exists_isClosedEmbedding_unitary (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] :
    IsNSS K ↔ ∃ (ι : Type u) (_ : Fintype ι) (d : ι → ℕ)
      (f : K →* ((i : ι) → Matrix.unitaryGroup (Fin (d i)) ℂ)), Topology.IsClosedEmbedding f := by
  refine ⟨exists_isClosedEmbedding_unitary_of_isNSS K, ?_⟩
  rintro ⟨ι, _, d, f, hf⟩
  exact isNSS_of_injective_unitary_pi d f hf.continuous hf.injective

end UndergradKB.Topology
