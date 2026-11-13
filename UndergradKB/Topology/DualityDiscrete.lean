import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-!
# Subgroups of the dual of a compact group that separate points (Morris, Appendix 5, A5.11)

Without Peter-Weyl: orthogonality of characters for the Haar probability measure, together with the
complex Stone-Weierstrass theorem, shows that a subgroup of the dual of a compact Hausdorff abelian
group which separates points is the whole dual.
-/

open MeasureTheory Set TopologicalSpace

namespace UndergradKB.Topology

noncomputable section

section Orthogonality

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- A character of `K`, as a continuous complex-valued function. -/
def charFun (χ : PontryaginDual K) : C(K, ℂ) :=
  ⟨fun x => ((χ x : Circle) : ℂ), continuous_subtype_val.comp (map_continuous χ)⟩

@[simp] theorem charFun_apply (χ : PontryaginDual K) (x : K) :
    charFun χ x = ((χ x : Circle) : ℂ) := rfl

theorem charFun_mul (χ ψ : PontryaginDual K) : charFun (χ * ψ) = charFun χ * charFun ψ := by
  ext x
  rfl

theorem star_charFun (χ : PontryaginDual K) : star (charFun χ) = charFun χ⁻¹ := by
  ext x
  show star ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]
  rfl

theorem charFun_one : charFun (1 : PontryaginDual K) = 1 := by
  ext x
  rfl

variable [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [T2Space K]

/-- Orthogonality: the Haar probability integral of a nontrivial character vanishes. -/
theorem integral_char_eq_zero (μ : Measure K) [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
    {χ : PontryaginDual K} (hχ : χ ≠ 1) : ∫ x, ((χ x : Circle) : ℂ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (PontryaginDual.ext fun a => by simpa using h a)
  have h := integral_mul_left_eq_self (μ := μ) (fun x => ((χ x : Circle) : ℂ)) a
  simp only [map_mul, Circle.coe_mul] at h
  rw [integral_const_mul] at h
  have ha' : ((χ a : Circle) : ℂ) ≠ 1 := fun e => ha (Subtype.ext e)
  have : (((χ a : Circle) : ℂ) - 1) * ∫ x, ((χ x : Circle) : ℂ) ∂μ = 0 := by
    rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd (sub_eq_zero.1 h0) ha'
  · exact h0

end Orthogonality

section Separating

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- Morris, Topology Without Tears, Corollary A5.11.3 (TP-586). If `K` is a compact Hausdorff
abelian group and `S` is a subgroup of its dual group that separates the points of `K`, then `S`
is the whole dual group. -/
@[kb "morris2024" "Corollary A5.11.3, p. 576"]
theorem subgroup_dual_eq_top_of_separatesPoints (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) : S = ⊤ := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  by_contra hne
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual K, ψ ∉ S := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_top_iff' S |>.2 h)
  let μ : Measure K := Measure.haarMeasure (⊤ : PositiveCompacts K)
  haveI : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have := Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts K))
    rwa [PositiveCompacts.coe_top] at this
  -- the span of the characters in `S`
  let T : Set C(K, ℂ) := {f | ∃ χ ∈ S, f = charFun χ}
  let P : Submodule ℂ C(K, ℂ) := Submodule.span ℂ T
  have hT : ∀ χ ∈ S, charFun χ ∈ P := fun χ hχ => Submodule.subset_span ⟨χ, hχ, rfl⟩
  have hone : (1 : C(K, ℂ)) ∈ P := by
    rw [← charFun_one]
    exact hT 1 S.one_mem
  have hmul : ∀ f g : C(K, ℂ), f ∈ P → g ∈ P → f * g ∈ P := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, hχ, rfl⟩ := hx
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨χ', hχ', rfl⟩ := hy
        rw [← charFun_mul]
        exact hT _ (S.mul_mem hχ hχ')
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact P.add_mem hy hz
      | smul a y _ hy => rw [mul_smul_comm]; exact P.smul_mem a hy
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact P.add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact P.smul_mem a hx
  have hstar : ∀ f : C(K, ℂ), f ∈ P → star f ∈ P := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, hχ, rfl⟩ := hx
      rw [star_charFun]
      exact hT _ (S.inv_mem hχ)
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact P.add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact P.smul_mem _ hx
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { toSubalgebra := P.toSubalgebra hone hmul
      star_mem' := fun {f} hf => hstar f hf }
  have hAmem : ∀ f : C(K, ℂ), f ∈ A ↔ f ∈ P := fun f => Iff.rfl
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ, hne⟩ := hS x y hxy
    refine ⟨_, ⟨charFun χ, (hAmem _).2 (hT χ hχ), rfl⟩, ?_⟩
    intro e
    exact hne (Subtype.ext e)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hmem : charFun ψ ∈ A.topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hmem
  obtain ⟨g, hgA, hg⟩ := Metric.mem_closure_iff.1 hmem (1 / 2) (by norm_num)
  have hgP : g ∈ P := (hAmem g).1 hgA
  -- the integral of `g * conj ψ` vanishes
  have hint : ∀ f : C(K, ℂ), Integrable (fun x => f x * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ)) μ := by
    intro f
    have hc : Continuous (fun x => f x * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ)) :=
      f.continuous.mul (charFun (ψ⁻¹)).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero : ∀ g ∈ P, ∫ x, g x * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) ∂μ = 0 := by
    intro g hgP
    induction hgP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨χ, hχ, rfl⟩ := hx
      have hne1 : χ * ψ⁻¹ ≠ 1 := by
        intro e
        apply hψ
        have : χ = ψ := by
          have := congrArg (· * ψ) e
          simpa using this
        rw [← this]
        exact hχ
      have h0 := integral_char_eq_zero μ hne1
      have e : ∀ x, charFun χ x * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) =
          (((χ * ψ⁻¹) x : Circle) : ℂ) := fun x => (Circle.coe_mul _ _).symm
      simp only [e]
      exact h0
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add (hint x) (hint y)]
      rw [ihx, ihy, add_zero]
    | smul a x hx ihx =>
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, ihx, mul_zero]
  have hone' : ∫ x, (charFun ψ x) * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) ∂μ = 1 := by
    have : ∀ x, (charFun ψ x) * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) = 1 := by
      intro x
      show ((ψ x : Circle) : ℂ) * (((ψ x)⁻¹ : Circle) : ℂ) = 1
      rw [← Circle.coe_mul, mul_inv_cancel]
      rfl
    simp only [this]
    simp
  have hdiff : ∫ x, (charFun ψ x - g x) * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) ∂μ = 1 := by
    simp only [sub_mul]
    rw [integral_sub (hint (charFun ψ)) (hint g), hone', hzero g hgP, sub_zero]
  have hbound : ‖∫ x, (charFun ψ x - g x) * (((ψ⁻¹ : PontryaginDual K) x : Circle) : ℂ) ∂μ‖
      ≤ 1 / 2 * μ.real univ := by
    apply norm_integral_le_of_norm_le_const
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    have h1 := ContinuousMap.dist_apply_le_dist (f := charFun ψ) (g := g) x
    rw [dist_eq_norm] at h1
    exact h1.trans hg.le
  rw [hdiff] at hbound
  simp at hbound
  linarith

end Separating

end

end UndergradKB.Topology
