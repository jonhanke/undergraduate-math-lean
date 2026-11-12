import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-!
# Transitivity, chaos, sensitive dependence and conjugacy of dynamical systems

Morris, *Topology Without Tears* (2024), Appendix 3, Sections A3.7 and A3.8 (`morris2024`).
A dynamical system is a self-map `f : X → X` of a metric space. The notions of transitivity (in the book's
metric form), chaos, sensitive dependence and conjugacy are bridging definitions; periodic points and prime
periods are Mathlib's `Function.periodicPts` and `Function.minimalPeriod`.
-/

open Function Set

namespace UndergradKB.Topology

section Transitive

variable {X : Type*} [MetricSpace X]

/-- The book's (metric) transitivity: for all `x y` and `ε > 0` some `z` within `ε` of `y` has an iterate
`f^n z`, `n ≥ 1`, within `ε` of `x`. -/
def IsTransitiveMap (f : X → X) : Prop :=
  ∀ x y : X, ∀ ε > 0, ∃ z : X, ∃ n : ℕ, 0 < n ∧ dist z y < ε ∧ dist (f^[n] z) x < ε

/-- Morris, Topology Without Tears, Definition A3.7.4 and Exercises A3.7 #4 (TP-451). The metric form of
transitivity is equivalent to topological transitivity: for nonempty open `U`, `V` some `f^n (U)`, `n ≥ 1`,
meets `V`. -/
@[kb "morris2024" "Definition A3.7.4, p. 464"]
theorem isTransitiveMap_iff_topological (f : X → X) :
    IsTransitiveMap f ↔ ∀ U V : Set X, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ n : ℕ, 0 < n ∧ (f^[n] '' U ∩ V).Nonempty := by
  constructor
  · rintro h U V hU hV ⟨y, hy⟩ ⟨x, hx⟩
    obtain ⟨ε1, h1, hb1⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨ε2, h2, hb2⟩ := Metric.isOpen_iff.mp hV x hx
    obtain ⟨z, n, hn, hz, hfz⟩ := h x y (min ε1 ε2) (lt_min h1 h2)
    exact ⟨n, hn, f^[n] z,
      ⟨z, hb1 (Metric.mem_ball.mpr (lt_of_lt_of_le hz (min_le_left _ _))), rfl⟩,
      hb2 (Metric.mem_ball.mpr (lt_of_lt_of_le hfz (min_le_right _ _)))⟩
  · intro h x y ε hε
    obtain ⟨n, hn, w, ⟨z, hz, rfl⟩, hw⟩ := h (Metric.ball y ε) (Metric.ball x ε)
      Metric.isOpen_ball Metric.isOpen_ball ⟨y, Metric.mem_ball_self hε⟩
      ⟨x, Metric.mem_ball_self hε⟩
    exact ⟨z, n, hn, Metric.mem_ball.mp hz, Metric.mem_ball.mp hw⟩

/-- The dynamical system `(X, f)` is *chaotic* if its periodic points are dense and it is transitive. -/
def IsChaoticMap (f : X → X) : Prop :=
  Dense (periodicPts f) ∧ IsTransitiveMap f

/-- Morris, Topology Without Tears, Definition A3.7.7 (TP-452). Chaotic means: dense periodic points and
transitivity. -/
@[kb "morris2024" "Definition A3.7.7, p. 464"]
theorem isChaoticMap_iff (f : X → X) :
    IsChaoticMap f ↔ Dense (periodicPts f) ∧ IsTransitiveMap f := Iff.rfl

/-- The system depends *sensitively on initial conditions* if one `β > 0` works at every point `x` and for
every `ε > 0`: some `y` within `ε` of `x` has an iterate `n ≥ 1` separating from that of `x` by more than `β`. -/
def DependsSensitively (f : X → X) : Prop :=
  ∃ β > 0, ∀ x : X, ∀ ε > 0, ∃ n : ℕ, ∃ y : X, 0 < n ∧ dist x y < ε ∧ β < dist (f^[n] x) (f^[n] y)

/-- Morris, Topology Without Tears, Definition A3.7.9 (TP-453). Unfolding sensitive dependence. -/
@[kb "morris2024" "Definition A3.7.9, p. 465"]
theorem dependsSensitively_iff (f : X → X) :
    DependsSensitively f ↔
      ∃ β > 0, ∀ x : X, ∀ ε > 0, ∃ n : ℕ, ∃ y : X, 0 < n ∧ dist x y < ε ∧ β < dist (f^[n] x) (f^[n] y) :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition A3.7.9 (TP-453). The identity map of a nonempty space does
not depend sensitively on initial conditions. -/
@[kb "morris2024" "Definition A3.7.9, p. 465"]
theorem not_dependsSensitively_id [Nonempty X] : ¬ DependsSensitively (id : X → X) := by
  rintro ⟨β, hβ, h⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, y, -, hxy, hd⟩ := h x β hβ
  simp only [iterate_id, id] at hd
  linarith

/-- Morris, Topology Without Tears, Definition A3.7.9 (TP-453). Doubling on the real line depends
sensitively on initial conditions. -/
@[kb "morris2024" "Definition A3.7.9, p. 465"]
theorem dependsSensitively_mul_two : DependsSensitively (fun x : ℝ => 2 * x) := by
  have hit : ∀ (n : ℕ) (x : ℝ), (fun x : ℝ => 2 * x)^[n] x = 2 ^ n * x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [iterate_succ_apply', ih]; ring
  refine ⟨1, one_pos, fun x ε hε => ?_⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, x + ε / 2, Nat.succ_pos n, ?_, ?_⟩
  · rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  · have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    have h3 : 2 < 2 ^ n * ε := by rwa [div_lt_iff₀ hε] at hn
    rw [hit, hit, Real.dist_eq,
      show 2 ^ (n + 1) * x - 2 ^ (n + 1) * (x + ε / 2) = -(2 ^ (n + 1) * (ε / 2)) by ring, abs_neg,
      abs_of_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hε.le]

end Transitive

/-! ### Conjugacy -/

section Conjugacy

variable {X₁ X₂ : Type*} [MetricSpace X₁] [MetricSpace X₂] {f₁ : X₁ → X₁} {f₂ : X₂ → X₂}

/-- Two dynamical systems are *conjugate* if some homeomorphism `h` satisfies `f₂ ∘ h = h ∘ f₁`. -/
def AreConjugate (f₁ : X₁ → X₁) (f₂ : X₂ → X₂) : Prop :=
  ∃ h : X₁ ≃ₜ X₂, Semiconj h f₁ f₂

/-- Morris, Topology Without Tears, Definition A3.8.1 (TP-454). Conjugacy in the book's terms: a
homeomorphism `h` with `f₂ (h x) = h (f₁ x)` for all `x`. -/
@[kb "morris2024" "Definition A3.8.1, p. 467"]
theorem areConjugate_iff :
    AreConjugate f₁ f₂ ↔ ∃ h : X₁ ≃ₜ X₂, ∀ x, f₂ (h x) = h (f₁ x) :=
  ⟨fun ⟨h, hh⟩ => ⟨h, fun x => (hh x).symm⟩, fun ⟨h, hh⟩ => ⟨h, fun x => (hh x).symm⟩⟩

/-- Morris, Topology Without Tears, Definition A3.8.1 (TP-454). A conjugacy is a conjugacy backwards too. -/
@[kb "morris2024" "Definition A3.8.1, p. 467"]
theorem semiconj_symm_homeomorph {h : X₁ ≃ₜ X₂} (hh : Semiconj h f₁ f₂) : Semiconj h.symm f₂ f₁ := by
  intro y
  apply h.injective
  rw [h.apply_symm_apply, hh (h.symm y), h.apply_symm_apply]

/-- Morris, Topology Without Tears, Remark A3.8.2 (TP-454). Conjugacy is symmetric. -/
@[kb "morris2024" "Remark A3.8.2, p. 467"]
theorem AreConjugate.symm (h : AreConjugate f₁ f₂) : AreConjugate f₂ f₁ := by
  obtain ⟨h, hh⟩ := h
  exact ⟨h.symm, (semiconj_symm_homeomorph hh)⟩

/-- Conjugacy is reflexive. -/
theorem AreConjugate.refl (f : X₁ → X₁) : AreConjugate f f :=
  ⟨Homeomorph.refl X₁, fun _ => rfl⟩

/-- Conjugacy is transitive. -/
theorem AreConjugate.trans {X₃ : Type*} [MetricSpace X₃] {f₃ : X₃ → X₃}
    (h : AreConjugate f₁ f₂) (h' : AreConjugate f₂ f₃) : AreConjugate f₁ f₃ := by
  obtain ⟨h, hh⟩ := h
  obtain ⟨h', hh'⟩ := h'
  exact ⟨h.trans h', fun x => by simp [hh x, hh' (h x)]⟩

variable {h : X₁ ≃ₜ X₂} (hh : Semiconj h f₁ f₂)

include hh

/-- Morris, Topology Without Tears, Theorem A3.8.4 (i) (TP-455). A point is fixed by `f₁` iff its image is
fixed by `f₂`. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem semiconj_isFixedPt_homeomorph_iff (x : X₁) : IsFixedPt f₂ (h x) ↔ IsFixedPt f₁ x := by
  unfold IsFixedPt
  rw [← hh x]
  exact h.injective.eq_iff

/-- Morris, Topology Without Tears, Theorem A3.8.4 (ii) (TP-455). A point is `n`-periodic for `f₁` iff
its image is `n`-periodic for `f₂`. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem semiconj_isPeriodicPt_homeomorph_iff (n : ℕ) (x : X₁) :
    IsPeriodicPt f₂ n (h x) ↔ IsPeriodicPt f₁ n x := by
  unfold IsPeriodicPt IsFixedPt
  rw [← (hh.iterate_right n) x]
  exact h.injective.eq_iff

/-- Morris, Topology Without Tears, Theorem A3.8.4 (ii) (TP-455). A conjugacy preserves prime periods. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem semiconj_minimalPeriod_homeomorph (x : X₁) :
    minimalPeriod f₂ (h x) = minimalPeriod f₁ x :=
  minimalPeriod_eq_minimalPeriod_iff.mpr fun n => semiconj_isPeriodicPt_homeomorph_iff hh n x

/-- Morris, Topology Without Tears, Theorem A3.8.4 (ii) (TP-455). A conjugacy carries the periodic points of
`f₁` onto those of `f₂`. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem semiconj_periodicPts_homeomorph : periodicPts f₂ = h '' periodicPts f₁ := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp hy
    refine ⟨h.symm y, mem_periodicPts.mpr ⟨n, hn, ?_⟩, by simp⟩
    refine (semiconj_isPeriodicPt_homeomorph_iff hh n _).mp ?_
    simpa using hp
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp hx
    exact mem_periodicPts.mpr ⟨n, hn, (semiconj_isPeriodicPt_homeomorph_iff hh n x).mpr hp⟩

/-- Transitivity transfers along a conjugacy. -/
theorem semiconj_isTransitiveMap_of_homeomorph (hf : IsTransitiveMap f₁) : IsTransitiveMap f₂ := by
  rw [isTransitiveMap_iff_topological] at hf ⊢
  intro U V hU hV hUn hVn
  obtain ⟨n, hn, w, ⟨z, hz, rfl⟩, hw⟩ := hf (h ⁻¹' U) (h ⁻¹' V) (hU.preimage h.continuous)
    (hV.preimage h.continuous) (h.surjective.nonempty_preimage.mpr hUn)
    (h.surjective.nonempty_preimage.mpr hVn)
  exact ⟨n, hn, h (f₁^[n] z), ⟨h z, hz, ((hh.iterate_right n) z).symm⟩, hw⟩

/-- Morris, Topology Without Tears, Theorem A3.8.4 (iii) (TP-455). A conjugacy carries chaotic systems to
chaotic systems. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem semiconj_isChaoticMap_of_homeomorph (hf : IsChaoticMap f₁) : IsChaoticMap f₂ := by
  refine ⟨?_, semiconj_isTransitiveMap_of_homeomorph hh hf.2⟩
  rw [semiconj_periodicPts_homeomorph hh]
  exact h.surjective.denseRange.dense_image h.continuous hf.1

omit hh

/-- Morris, Topology Without Tears, Theorem A3.8.4 (iii) (TP-455). Conjugate systems are chaotic together. -/
@[kb "morris2024" "Theorem A3.8.4, p. 468"]
theorem AreConjugate.isChaoticMap_iff (h : AreConjugate f₁ f₂) : IsChaoticMap f₁ ↔ IsChaoticMap f₂ := by
  obtain ⟨g, hg⟩ := h
  exact ⟨semiconj_isChaoticMap_of_homeomorph hg, semiconj_isChaoticMap_of_homeomorph (semiconj_symm_homeomorph hg)⟩

end Conjugacy

end UndergradKB.Topology
