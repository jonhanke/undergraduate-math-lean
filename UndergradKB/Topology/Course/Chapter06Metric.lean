import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Group.Basic
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Topology Without Tears, Chapter 6 (first half)

Thin wrappers of Mathlib results on metric spaces, sequences and separation.
-/

open Set Topology TopologicalSpace Filter

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Definition 6.1.1 (TP-097). A metric is nonnegative, symmetric, vanishes
exactly on the diagonal and satisfies the triangle inequality. -/
@[kb "morris2024" "Definition 6.1.1, p. 125"]
theorem morris_6_1_1 {X : Type*} [MetricSpace X] :
    (∀ a b : X, dist a b = dist b a) ∧ (∀ a b : X, dist a b = 0 ↔ a = b) ∧
      (∀ a b c : X, dist a c ≤ dist a b + dist b c) ∧ ∀ a b : X, 0 ≤ dist a b :=
  ⟨dist_comm, fun _ _ => dist_eq_zero, dist_triangle, fun _ _ => dist_nonneg⟩

/-- Morris, Topology Without Tears, Exercise 6.1.6 (TP-099). The distance between continuous functions on
`[0,1]` is the supremum of `|f x - g x|`. -/
@[kb "morris2024" "Exercise 6.1.6, p. 128"]
theorem morris_6_1_6 (f g : C(unitInterval, ℝ)) :
    dist f g = ⨆ x : unitInterval, |f x - g x| := by
  rw [ContinuousMap.dist_eq_iSup]
  simp only [Real.dist_eq]

/-- Morris, Topology Without Tears, Exercise 6.1.9 (TP-100). A normed vector space is a metric space with
`d(x,y) = ‖x - y‖`. -/
@[kb "morris2024" "Exercise 6.1.9, p. 129"]
theorem morris_6_1_9 {E : Type*} [NormedAddCommGroup E] (x y : E) : dist x y = ‖x - y‖ :=
  dist_eq_norm x y

/-- Morris, Topology Without Tears, Definition 6.1.10 (TP-101). The open ball of radius `r` about `a` is the set of
points at distance less than `r` from `a`. -/
@[kb "morris2024" "Definition 6.1.10, p. 130"]
theorem morris_6_1_10 {X : Type*} [MetricSpace X] (a : X) (r : ℝ) :
    Metric.ball a r = {x | dist a x < r} := by
  ext x
  exact Metric.mem_ball'

/-- Morris, Topology Without Tears, Proposition 6.1.23 (TP-105). A set in a metric space is open iff every point
of it has an open ball around it inside the set. -/
@[kb "morris2024" "Proposition 6.1.23, p. 133"]
theorem morris_6_1_23 {X : Type*} [MetricSpace X] (U : Set X) :
    IsOpen U ↔ ∀ a ∈ U, ∃ r > 0, Metric.ball a r ⊆ U :=
  Metric.isOpen_iff

/-- Morris, Topology Without Tears, Definition 6.1.24 (TP-108). Hausdorff: distinct points have disjoint open
neighbourhoods. -/
@[kb "morris2024" "Definition 6.1.24, p. 134"]
theorem morris_6_1_24 {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  ⟨fun h x y hxy => h.t2 hxy, fun h => ⟨fun x y hxy => h x y hxy⟩⟩

/-- Morris, Topology Without Tears, Proposition 6.1.25 (TP-109). The topology induced by a metric is Hausdorff. -/
@[kb "morris2024" "Proposition 6.1.25, p. 134"]
theorem morris_6_1_25 {X : Type*} [MetricSpace X] :
    ∀ x y : X, x ≠ y → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  fun _ _ hxy => t2_separation hxy

/-- Morris, Topology Without Tears, Definition 6.1.27 (TP-111). A topological space is metrizable iff some metric
on the underlying set induces its topology. -/
@[kb "morris2024" "Definition 6.1.27, p. 135"]
theorem morris_6_1_27 {X : Type*} [t : TopologicalSpace X] :
    MetrizableSpace X ↔ ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t := by
  constructor
  · intro h
    exact ⟨TopologicalSpace.metrizableSpaceMetric X, rfl⟩
  · rintro ⟨m, hm⟩
    subst hm
    infer_instance

/-- Morris, Topology Without Tears, Definition 6.2.1 (TP-112). A sequence in a metric space converges to `x` iff
for every `ε > 0` its terms are eventually within `ε` of `x`. -/
@[kb "morris2024" "Definition 6.2.1, p. 142"]
theorem morris_6_2_1 {X : Type*} [MetricSpace X] (u : ℕ → X) (x : X) :
    Tendsto u atTop (𝓝 x) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) x < ε :=
  Metric.tendsto_atTop

/-- Morris, Topology Without Tears, Proposition 6.2.2 (TP-113). A sequence in a metric space has at most one
limit. -/
@[kb "morris2024" "Proposition 6.2.2, p. 142"]
theorem morris_6_2_2 {X : Type*} [MetricSpace X] {u : ℕ → X} {a b : X}
    (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

/-- Morris, Topology Without Tears, Proposition 6.2.3 (TP-114). A subset of a metric space is closed iff the limit
of every convergent sequence of its points lies in it. -/
@[kb "morris2024" "Proposition 6.2.3, p. 143"]
theorem morris_6_2_3 {X : Type*} [MetricSpace X] (A : Set X) :
    IsClosed A ↔ ∀ (u : ℕ → X) (x : X), (∀ n, u n ∈ A) → Tendsto u atTop (𝓝 x) → x ∈ A :=
  ⟨fun h _ _ hu ht => h.isSeqClosed hu ht, fun h => IsSeqClosed.isClosed fun _ _ hu ht => h _ _ hu ht⟩

/-- Morris, Topology Without Tears, Proposition 6.2.4 (TP-115). A map between metric spaces is continuous iff it
carries convergent sequences to convergent sequences (with the image limit). -/
@[kb "morris2024" "Proposition 6.2.4, p. 144"]
theorem morris_6_2_4 {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ (u : ℕ → X) (x : X), Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 (f x)) :=
  ⟨fun h _ _ ht => h.seqContinuous ht, fun h => SeqContinuous.continuous fun _ _ ht => h _ _ ht⟩

/-- Morris, Topology Without Tears, Corollary 6.2.5 (TP-116). A map between metric spaces is continuous iff it
satisfies the epsilon-delta condition at every point. -/
@[kb "morris2024" "Corollary 6.2.5, p. 145"]
theorem morris_6_2_5 {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ b : X, ∀ ε > 0, ∃ δ > 0, ∀ a : X, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.continuous_iff

/-- Morris, Topology Without Tears, Section 6.2 (TP-117). A space is sequential iff every sequentially closed set is
closed. -/
@[kb "morris2024" "Exercises 6.2, p. 147"]
theorem morris_ex_6_2_a {X : Type*} [TopologicalSpace X] :
    SequentialSpace X ↔ ∀ A : Set X, IsSeqClosed A → IsClosed A :=
  ⟨fun h A hA => hA.isClosed, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Section 6.2 (TP-117). A space is Frechet-Urysohn iff every point of the
closure of a set is the limit of a sequence from the set. -/
@[kb "morris2024" "Exercises 6.2, p. 147"]
theorem morris_ex_6_2_b {X : Type*} [TopologicalSpace X] :
    FrechetUrysohnSpace X ↔
      ∀ (A : Set X) (x : X), x ∈ closure A → ∃ u : ℕ → X, (∀ n, u n ∈ A) ∧ Tendsto u atTop (𝓝 x) :=
  ⟨fun h A x hx => FrechetUrysohnSpace.closure_subset_seqClosure A hx, fun h => ⟨fun A _ hx => h A _ hx⟩⟩

/-- Morris, Topology Without Tears, Section 6.2 (TP-117). Every Frechet-Urysohn space is sequential. -/
@[kb "morris2024" "Exercises 6.2, p. 147"]
theorem morris_ex_6_2_c {X : Type*} [TopologicalSpace X] [FrechetUrysohnSpace X] : SequentialSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Section 6.1 (TP-118). An isometry preserves distances. -/
@[kb "morris2024" "Exercises 6.1, p. 138"]
theorem morris_ex_6_1_a {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Isometry f ↔ ∀ x y : X, dist (f x) (f y) = dist x y :=
  isometry_iff_dist_eq

/-- Morris, Topology Without Tears, Section 6.1 (TP-118). Two metric spaces are isometric iff there is a
surjective isometry between them. -/
@[kb "morris2024" "Exercises 6.1, p. 138"]
theorem morris_ex_6_1_b {X Y : Type*} [MetricSpace X] [MetricSpace Y] :
    Nonempty (X ≃ᵢ Y) ↔ ∃ f : X → Y, Isometry f ∧ Function.Surjective f := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e, e.isometry, e.surjective⟩
  · rintro ⟨f, hf, hs⟩
    exact ⟨⟨Equiv.ofBijective f ⟨hf.injective, hs⟩, hf⟩⟩

/-- Morris, Topology Without Tears, Section 6.1 (TP-119). A metric space is bounded iff all distances are bounded
by a constant. -/
@[kb "morris2024" "Exercises 6.1, p. 135"]
theorem morris_ex_6_1_c {X : Type*} [MetricSpace X] :
    BoundedSpace X ↔ ∃ M : ℝ, ∀ x y : X, dist x y ≤ M :=
  Metric.boundedSpace_iff

/-- Morris, Topology Without Tears, Section 6.1 (TP-120). A subset is totally bounded iff for each `ε > 0` it is
covered by finitely many `ε`-balls. -/
@[kb "morris2024" "Exercises 6.1, p. 140"]
theorem morris_ex_6_1_d {X : Type*} [MetricSpace X] (A : Set X) :
    TotallyBounded A ↔ ∀ ε > 0, ∃ t : Set X, t.Finite ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε :=
  Metric.totallyBounded_iff

/-- Morris, Topology Without Tears, Section 6.1 (TP-121). A space is normal iff any two disjoint closed sets have
disjoint open neighbourhoods. -/
@[kb "morris2024" "Exercises 6.1, p. 138"]
theorem morris_ex_6_1_e {X : Type*} [TopologicalSpace X] :
    NormalSpace X ↔ ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V :=
  ⟨fun h A B hA hB hd => h.normal A B hA hB hd, fun h => ⟨fun A B hA hB hd => h A B hA hB hd⟩⟩

/-- Morris, Topology Without Tears, Section 6.1 (TP-121). A `T4` space is a normal Hausdorff space. -/
@[kb "morris2024" "Exercises 6.1, p. 138"]
theorem morris_ex_6_1_f {X : Type*} [TopologicalSpace X] :
    T4Space X ↔ NormalSpace X ∧ T2Space X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => { }⟩

end UndergradKB.Topology.Course
