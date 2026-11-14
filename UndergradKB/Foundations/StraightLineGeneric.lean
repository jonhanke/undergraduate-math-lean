import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Compact
import UndergradKB.Foundations.StraightLine

/-!
# Foundations: moving a straight-line drawing into general position

The conditions defining a straight-line drawing (`StraightLineDrawing`) are open: if the vertices
are moved a little, distinct points stay distinct, a point off a segment stays off it, and
disjoint segments stay disjoint (each by compactness of the parameter interval). Moving every
vertex `v` along a direction `w v` such that no three of the directions are collinear makes every
orientation a quadratic polynomial in the parameter with nonzero leading coefficient, hence
nonzero for all small positive parameters. So every straight-line drawing can be replaced by one in
which no three vertices are collinear (`StraightLineDrawing.exists_generic`).
-/

namespace UndergradKB.Foundations

open Set Filter Topology

/-- Orientation of three moved points: a quadratic polynomial in the parameter `ε`. -/
theorem orient_perturb (p q r a b c : ℝ × ℝ) (ε : ℝ) :
    orient (p + ε • a) (q + ε • b) (r + ε • c) =
      orient p q r + ε * ((q.1 - p.1) * (c.2 - a.2) + (b.1 - a.1) * (r.2 - p.2) -
        (q.2 - p.2) * (c.1 - a.1) - (b.2 - a.2) * (r.1 - p.1)) + ε ^ 2 * orient a b c := by
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- A quadratic polynomial with nonzero leading coefficient is nonzero at all small positive
arguments. -/
theorem eventually_quadratic_ne_zero (A B C : ℝ) (hC : C ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), A + ε * B + ε ^ 2 * C ≠ 0 := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  by_cases hA : A = 0
  · subst hA
    by_cases hB : B = 0
    · subst hB
      filter_upwards [hpos] with ε hε
      simp only [zero_add, mul_zero]
      exact mul_ne_zero (pow_ne_zero 2 hε.ne') hC
    · have hc : ContinuousAt (fun ε : ℝ => B + ε * C) 0 := by fun_prop
      have h1 := eventually_nhdsWithin_of_eventually_nhds (s := Ioi 0)
        (hc.eventually_ne (by simpa using hB))
      filter_upwards [hpos, h1] with ε hε h
      have : (0 : ℝ) + ε * B + ε ^ 2 * C = ε * (B + ε * C) := by ring
      rw [this]
      exact mul_ne_zero hε.ne' h
  · have hc : ContinuousAt (fun ε : ℝ => A + ε * B + ε ^ 2 * C) 0 := by fun_prop
    exact eventually_nhdsWithin_of_eventually_nhds (hc.eventually_ne (by simpa using hA))

/-- If a point is off a segment, then after moving the three points continuously by a small
amount it is still off the moved segment. -/
theorem eventually_not_mem_segment {p q r a b c : ℝ × ℝ} (h : r ∉ segment ℝ p q) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), r + ε • c ∉ segment ℝ (p + ε • a) (q + ε • b) := by
  set F : ℝ × ℝ → ℝ × ℝ := fun z =>
    (1 - z.2) • (p + z.1 • a) + z.2 • (q + z.1 • b) - (r + z.1 • c) with hF
  have hK : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ θ ∈ Icc (0 : ℝ) 1, F (ε, θ) ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro θ hθ
    have hc : ContinuousAt F (0, θ) := by
      simp only [hF]; fun_prop
    apply hc.eventually_ne
    intro h0
    apply h
    rw [segment_eq_image]
    refine ⟨θ, hθ, ?_⟩
    simp only [hF, zero_smul, add_zero] at h0
    exact sub_eq_zero.1 h0
  filter_upwards [hK] with ε hε hmem
  rw [segment_eq_image] at hmem
  obtain ⟨θ, hθ, hθe⟩ := hmem
  beta_reduce at hθe
  exact hε θ hθ (by simp only [hF]; rw [hθe, sub_self])

/-- If two segments are disjoint, they stay disjoint after moving their endpoints continuously by
a small amount. -/
theorem eventually_disjoint_segment {p q r s a b c d : ℝ × ℝ}
    (h : Disjoint (segment ℝ p q) (segment ℝ r s)) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), Disjoint (segment ℝ (p + ε • a) (q + ε • b))
      (segment ℝ (r + ε • c) (s + ε • d)) := by
  set F : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun z =>
    ((1 - z.2.1) • (p + z.1 • a) + z.2.1 • (q + z.1 • b)) -
      ((1 - z.2.2) • (r + z.1 • c) + z.2.2 • (s + z.1 • d)) with hF
  have hK : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ θ ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F (ε, θ) ≠ 0 := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro θ hθ
    have hc : ContinuousAt F (0, θ) := by
      simp only [hF]; fun_prop
    apply hc.eventually_ne
    intro h0
    simp only [hF, zero_smul, add_zero] at h0
    have m1 : (1 - θ.1) • p + θ.1 • q ∈ segment ℝ p q := by
      rw [segment_eq_image]; exact ⟨θ.1, hθ.1, rfl⟩
    have m2 : (1 - θ.1) • p + θ.1 • q ∈ segment ℝ r s := by
      rw [segment_eq_image]; exact ⟨θ.2, hθ.2, (sub_eq_zero.1 h0).symm⟩
    exact Set.disjoint_left.1 h m1 m2
  filter_upwards [hK] with ε hε
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rw [segment_eq_image] at hz1 hz2
  obtain ⟨θ1, h1, e1⟩ := hz1
  obtain ⟨θ2, h2, e2⟩ := hz2
  beta_reduce at e1 e2
  exact hε (θ1, θ2) ⟨h1, h2⟩ (by simp only [hF]; rw [e1, e2, sub_self])

/-- **General position.** If `w` assigns to the vertices directions no three of which are
collinear, every straight-line drawing of a finite graph can be moved to a straight-line drawing
in which no three vertices are collinear. -/
theorem StraightLineDrawing.exists_generic {V : Type*} [Finite V] {G : SimpleGraph V}
    (D : StraightLineDrawing G) (w : V → ℝ × ℝ)
    (hw : ∀ u v x, u ≠ v → v ≠ x → u ≠ x → orient (w u) (w v) (w x) ≠ 0) :
    ∃ D' : StraightLineDrawing G,
      ∀ u v x, u ≠ v → v ≠ x → u ≠ x → orient (D'.pos u) (D'.pos v) (D'.pos x) ≠ 0 := by
  set P : ℝ → V → ℝ × ℝ := fun ε v => D.pos v + ε • w v with hP
  have hinj : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ u v, u ≠ v → P ε u ≠ P ε v := by
    refine eventually_all.2 fun u => eventually_all.2 fun v => ?_
    by_cases huv : u = v
    · exact Eventually.of_forall fun _ h => absurd huv h
    · have hc : ContinuousAt (fun ε : ℝ => P ε u - P ε v) 0 := by simp only [hP]; fun_prop
      have := hc.eventually_ne (y := 0) (by
        simp only [hP, zero_smul, add_zero, ne_eq, sub_eq_zero]; exact D.injective.ne huv)
      filter_upwards [this] with ε hε _ h
      exact hε (sub_eq_zero.2 h)
  have hvert : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ u v x, G.Adj u v → x ≠ u → x ≠ v →
      P ε x ∉ segment ℝ (P ε u) (P ε v) := by
    refine eventually_all.2 fun u => eventually_all.2 fun v => eventually_all.2 fun x => ?_
    by_cases h : G.Adj u v ∧ x ≠ u ∧ x ≠ v
    · filter_upwards [eventually_not_mem_segment (a := w u) (b := w v) (c := w x)
        (D.vertex_not_mem u v x h.1 h.2.1 h.2.2)] with ε hε _ _ _
      exact hε
    · exact Eventually.of_forall fun _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  have hdisj : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ u v u' v', G.Adj u v → G.Adj u' v' → u ≠ u' → u ≠ v' →
      v ≠ u' → v ≠ v' → Disjoint (segment ℝ (P ε u) (P ε v)) (segment ℝ (P ε u') (P ε v')) := by
    refine eventually_all.2 fun u => eventually_all.2 fun v => eventually_all.2 fun u' =>
      eventually_all.2 fun v' => ?_
    by_cases h : G.Adj u v ∧ G.Adj u' v' ∧ u ≠ u' ∧ u ≠ v' ∧ v ≠ u' ∧ v ≠ v'
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      filter_upwards [eventually_disjoint_segment (a := w u) (b := w v) (c := w u') (d := w v')
        (D.disjoint u v u' v' h1 h2 h3 h4 h5 h6)] with ε hε _ _ _ _ _ _
      exact hε
    · exact Eventually.of_forall fun _ h1 h2 h3 h4 h5 h6 => absurd ⟨h1, h2, h3, h4, h5, h6⟩ h
  have hgen : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ u v x, u ≠ v → v ≠ x → u ≠ x →
      orient (P ε u) (P ε v) (P ε x) ≠ 0 := by
    refine eventually_all.2 fun u => eventually_all.2 fun v => eventually_all.2 fun x => ?_
    by_cases h : u ≠ v ∧ v ≠ x ∧ u ≠ x
    · filter_upwards [eventually_quadratic_ne_zero _ _ _ (hw u v x h.1 h.2.1 h.2.2)]
        with ε hε _ _ _
      simp only [hP]
      rw [orient_perturb]
      exact hε
    · exact Eventually.of_forall fun _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := ((((eventually_nhdsWithin_of_eventually_nhds hinj).and
    (eventually_nhdsWithin_of_eventually_nhds hvert)).and
    (eventually_nhdsWithin_of_eventually_nhds hdisj)).and hgen).exists
  exact ⟨⟨P ε, fun u v h => by_contra fun hne => h1 u v hne h, h2, h3⟩, h4⟩

end UndergradKB.Foundations
