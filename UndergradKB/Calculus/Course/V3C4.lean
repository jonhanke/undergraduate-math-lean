import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Connected.PathConnected
import UndergradKB.Calculus.PDEExamples
import UndergradKB.Calculus.SeveralVariables
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 4 (differentiation of functions of several
variables). The plane is `EuclideanSpace ℝ (Fin 2)` where round disks are needed, and `ℝ × ℝ`
(or curried functions `ℝ → ℝ → ℝ`) where only partial derivatives matter. -/

namespace UndergradKB.Calculus.Course.V3C4

open Filter Topology Set Metric Asymptotics

/-- The plane with its Euclidean metric (round disks). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- OpenStax Calculus 3:§4.2 Definition (disk) (CA-509). The open disk of radius `δ` about `p` is
the set of points at distance less than `δ` from `p`. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (disk), p. 325"]
theorem disk_eq_dist_lt (p : Plane) (δ : ℝ) : ball p δ = {q | dist q p < δ} :=
  Set.ext fun _ => Metric.mem_ball

/-- OpenStax Calculus 3:§4.2 Definition (ball in three or more dimensions) (CA-509). Same for the
open ball in Euclidean `n`-space. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (ball in three or more dimensions), p. 335"]
theorem ball_eq_dist_lt (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    ball p δ = {q | dist q p < δ} :=
  Set.ext fun _ => Metric.mem_ball

/-- OpenStax Calculus 3:§4.2 Definition (limit of a function of two variables) (CA-510). The limit
of `f` at `p` is `L` (taken over the punctured neighbourhood) iff the epsilon-delta condition on
punctured disks holds. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (limit of a function of two variables), p. 325"]
theorem limit_two_variables_iff (f : Plane → ℝ) (p : Plane) (L : ℝ) :
    Tendsto f (𝓝[≠] p) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ q, q ≠ p → dist q p < δ → |f q - L| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp [Real.dist_eq]

/-- OpenStax Calculus 3:§4.2 Definition (limit of a function of two variables) (CA-510). The same
definition in three variables (balls in `ℝ³`). -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (limit of a function of two variables), p. 325"]
theorem limit_three_variables_iff (f : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (L : ℝ) :
    Tendsto f (𝓝[≠] p) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ q, q ≠ p → dist q p < δ → |f q - L| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp [Real.dist_eq]

/-- OpenStax Calculus 3:§4.2 Definition (limit at a boundary point) (CA-511). The limit of `f`
at `p`, using only points of the domain `D` (other than `p`), is `L` iff the epsilon-delta
condition holds on the domain points of small disks. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (limit at a boundary point), p. 331"]
theorem limit_at_boundary_point_iff (D : Set Plane) (f : Plane → ℝ) (p : Plane) (L : ℝ) :
    Tendsto f (𝓝[D \ {p}] p) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ q ∈ D, q ≠ p → dist q p < δ → |f q - L| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp [Real.dist_eq, and_imp]

/-- OpenStax Calculus 3:Theorem 4.1 (CA-512). Limit laws for functions of several variables (sum,
difference, constant multiple, product, quotient with nonzero denominator limit, power), here along
the punctured neighbourhood of `p` in the plane. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.1, p. 326"]
theorem limit_laws {f g : Plane → ℝ} {p : Plane} {L M : ℝ}
    (hf : Tendsto f (𝓝[≠] p) (𝓝 L)) (hg : Tendsto g (𝓝[≠] p) (𝓝 M)) (c : ℝ) (n : ℕ) :
    Tendsto (fun q => f q + g q) (𝓝[≠] p) (𝓝 (L + M)) ∧
    Tendsto (fun q => f q - g q) (𝓝[≠] p) (𝓝 (L - M)) ∧
    Tendsto (fun q => c * f q) (𝓝[≠] p) (𝓝 (c * L)) ∧
    Tendsto (fun q => f q * g q) (𝓝[≠] p) (𝓝 (L * M)) ∧
    (M ≠ 0 → Tendsto (fun q => f q / g q) (𝓝[≠] p) (𝓝 (L / M))) ∧
    Tendsto (fun q => f q ^ n) (𝓝[≠] p) (𝓝 (L ^ n)) :=
  ⟨hf.add hg, hf.sub hg, hf.const_mul c, hf.mul hg, fun h => hf.div hg h, hf.pow n⟩

/-- OpenStax Calculus 3:Theorem 4.1 (CA-512). Constant and identity (coordinate) laws. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.1, p. 326"]
theorem limit_const_and_coordinate (p : Plane) (c : ℝ) :
    Tendsto (fun _ : Plane => c) (𝓝[≠] p) (𝓝 c) ∧
    Tendsto (fun q : Plane => q 0) (𝓝[≠] p) (𝓝 (p 0)) ∧
    Tendsto (fun q : Plane => q 1) (𝓝[≠] p) (𝓝 (p 1)) := by
  refine ⟨tendsto_const_nhds, ?_, ?_⟩
  · exact ((continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · exact ((continuous_apply 1).comp (PiLp.continuous_ofLp 2 _)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds

/-- OpenStax Calculus 3:§4.2 Definition (interior point, boundary point) (CA-514). A point is an
interior point of `S` iff some disk about it lies in `S`. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (interior point, boundary point), p. 330"]
theorem interior_point_iff (S : Set Plane) (p : Plane) :
    p ∈ interior S ↔ ∃ δ > 0, ball p δ ⊆ S := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]

/-- OpenStax Calculus 3:§4.2 Definition (interior point, boundary point) (CA-514). A point is a
boundary point of `S` iff every disk about it meets both `S` and its complement. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (interior point, boundary point), p. 330"]
theorem boundary_point_iff (S : Set Plane) (p : Plane) :
    p ∈ frontier S ↔ ∀ δ > 0, (ball p δ ∩ S).Nonempty ∧ (ball p δ ∩ Sᶜ).Nonempty := by
  rw [frontier_eq_closure_inter_closure, mem_inter_iff, Metric.mem_closure_iff,
    Metric.mem_closure_iff]
  constructor
  · rintro ⟨h1, h2⟩ δ hδ
    obtain ⟨a, ha, hda⟩ := h1 δ hδ
    obtain ⟨b, hb, hdb⟩ := h2 δ hδ
    exact ⟨⟨a, by simpa [dist_comm] using hda, ha⟩, ⟨b, by simpa [dist_comm] using hdb, hb⟩⟩
  · intro h
    refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
    · obtain ⟨a, ha, hs⟩ := (h δ hδ).1
      exact ⟨a, hs, by simpa [dist_comm] using ha⟩
    · obtain ⟨a, ha, hs⟩ := (h δ hδ).2
      exact ⟨a, hs, by simpa [dist_comm] using ha⟩

/-- OpenStax Calculus 3:§4.2 Definition (open set, closed set) (CA-515). A set is open iff every
point has a disk about it inside the set. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (open set, closed set), p. 331"]
theorem open_set_iff (S : Set Plane) : IsOpen S ↔ ∀ p ∈ S, ∃ δ > 0, ball p δ ⊆ S :=
  Metric.isOpen_iff

/-- OpenStax Calculus 3:§4.2 Definition (open set, closed set) (CA-515). A set is closed iff it
contains all of its boundary points. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (open set, closed set), p. 331"]
theorem closed_set_iff (S : Set Plane) : IsClosed S ↔ frontier S ⊆ S :=
  frontier_subset_iff_isClosed.symm

/-- OpenStax Calculus 3:§4.2 Definition (connected set, region) (CA-516). A region (nonempty,
open, connected set) is a nonempty open set that is not the union of two disjoint nonempty open
sets. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (connected set, region), p. 331"]
theorem region_iff (S : Set Plane) :
    (IsOpen S ∧ IsConnected S) ↔
      IsOpen S ∧ S.Nonempty ∧
        ¬ ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧
          S = U ∪ V := by
  constructor
  · rintro ⟨ho, hne, hpre⟩
    refine ⟨ho, hne, ?_⟩
    rintro ⟨U, V, hU, hV, hUne, hVne, hdisj, rfl⟩
    rw [isPreconnected_iff_subset_of_disjoint] at hpre
    have := hpre U V hU hV subset_rfl (by rw [(disjoint_iff_inter_eq_empty.mp hdisj)]; simp)
    rcases this with h | h
    · obtain ⟨v, hv⟩ := hVne
      exact disjoint_left.mp hdisj (h (Or.inr hv)) hv
    · obtain ⟨u, hu⟩ := hUne
      exact disjoint_left.mp hdisj hu (h (Or.inl hu))
  · rintro ⟨ho, hne, hno⟩
    refine ⟨ho, hne, ?_⟩
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hsub hdis
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨a, haS, hau⟩ := not_subset.mp hcon.1
    obtain ⟨b, hbS, hbv⟩ := not_subset.mp hcon.2
    apply hno
    refine ⟨S ∩ u, S ∩ v, ho.inter hu, ho.inter hv, ⟨b, hbS, ?_⟩, ⟨a, haS, ?_⟩, ?_, ?_⟩
    · exact (hsub hbS).resolve_right hbv
    · exact (hsub haS).resolve_left hau
    · rw [disjoint_iff_inter_eq_empty, ← hdis]
      ext x
      simp only [mem_inter_iff]
      tauto
    · ext x
      constructor
      · intro hx
        rcases hsub hx with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h) <;> exact h.1

/-- OpenStax Calculus 3:§4.2 Definition (continuity of a function of two variables) (CA-517).
Epsilon-delta form of continuity at a point of the plane. -/
@[kb "openstaxcalculus2016" "3:§4.2 Definition (continuity of a function of two variables), p. 333"]
theorem continuousAt_iff_epsilon_delta (f : Plane → ℝ) (p : Plane) :
    ContinuousAt f p ↔ ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ → |f q - f p| < ε := by
  rw [Metric.continuousAt_iff]
  simp [Real.dist_eq]

/-- OpenStax Calculus 3:Theorem 4.2 (CA-518). A sum of functions continuous at a point is
continuous there. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.2, p. 333"]
theorem continuousAt_add {f g : Plane → ℝ} {p : Plane} (hf : ContinuousAt f p)
    (hg : ContinuousAt g p) : ContinuousAt (fun q => f q + g q) p :=
  hf.add hg

/-- OpenStax Calculus 3:Theorem 4.3 (CA-519). A product of functions continuous at a point is
continuous there. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.3, p. 334"]
theorem continuousAt_mul {f g : Plane → ℝ} {p : Plane} (hf : ContinuousAt f p)
    (hg : ContinuousAt g p) : ContinuousAt (fun q => f q * g q) p :=
  hf.mul hg

/-- OpenStax Calculus 3:Theorem 4.4 (CA-520). A one-variable function continuous at `g p`
composed with `g` continuous at `p` is continuous at `p`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.4, p. 334"]
theorem continuousAt_comp {g : Plane → ℝ} {h : ℝ → ℝ} {p : Plane} (hg : ContinuousAt g p)
    (hh : ContinuousAt h (g p)) : ContinuousAt (fun q => h (g q)) p :=
  hh.comp hg

/-- OpenStax Calculus 3:§4.3 Definition (partial derivatives of a function of two variables)
(CA-521). `f_x(a,b) = L` iff the difference quotient in `x` (with `y = b` fixed) tends to `L`;
likewise for `f_y`. -/
@[kb "openstaxcalculus2016" "3:§4.3 Definition (partial derivatives of a function of two variables), p. 338"]
theorem partial_derivatives_two_variables_iff (f : ℝ → ℝ → ℝ) (a b L M : ℝ) :
    (HasDerivAt (fun x => f x b) L a ↔
      Tendsto (fun h => (f (a + h) b - f a b) / h) (𝓝[≠] 0) (𝓝 L)) ∧
    (HasDerivAt (fun y => f a y) M b ↔
      Tendsto (fun h => (f a (b + h) - f a b) / h) (𝓝[≠] 0) (𝓝 M)) := by
  have key : ∀ (g : ℝ → ℝ) (c L : ℝ), HasDerivAt g L c ↔
      Tendsto (fun h => (g (c + h) - g c) / h) (𝓝[≠] 0) (𝓝 L) := by
    intro g c L
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simp [div_eq_inv_mul]
  exact ⟨key _ _ _, key _ _ _⟩

/-- OpenStax Calculus 3:§4.3 Definition (partial derivatives of a function of three variables)
(CA-522). Partial derivatives in `x`, `y`, `z` are the one-variable difference-quotient limits
with the other two variables held fixed. -/
@[kb "openstaxcalculus2016" "3:§4.3 Definition (partial derivatives of a function of three variables), p. 343"]
theorem partial_derivatives_three_variables_iff (f : ℝ → ℝ → ℝ → ℝ) (a b c L M N : ℝ) :
    (HasDerivAt (fun x => f x b c) L a ↔
      Tendsto (fun h => (f (a + h) b c - f a b c) / h) (𝓝[≠] 0) (𝓝 L)) ∧
    (HasDerivAt (fun y => f a y c) M b ↔
      Tendsto (fun h => (f a (b + h) c - f a b c) / h) (𝓝[≠] 0) (𝓝 M)) ∧
    (HasDerivAt (fun z => f a b z) N c ↔
      Tendsto (fun h => (f a b (c + h) - f a b c) / h) (𝓝[≠] 0) (𝓝 N)) := by
  have key : ∀ (g : ℝ → ℝ) (c L : ℝ), HasDerivAt g L c ↔
      Tendsto (fun h => (g (c + h) - g c) / h) (𝓝[≠] 0) (𝓝 L) := by
    intro g c L
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simp [div_eq_inv_mul]
  exact ⟨key _ _ _, key _ _ _, key _ _ _⟩

/-- Partial derivative in the first coordinate of a differentiable function (helper). -/
theorem hasDerivAt_partial_fst {f : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {a b : ℝ}
    (h : HasFDerivAt f L (a, b)) : HasDerivAt (fun u => f (u, b)) (L (1, 0)) a :=
  h.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))

/-- Partial derivative in the second coordinate of a differentiable function (helper). -/
theorem hasDerivAt_partial_snd {f : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {a b : ℝ}
    (h : HasFDerivAt f L (a, b)) : HasDerivAt (fun v => f (a, v)) (L (0, 1)) b :=
  h.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))

/-- A linear form on the plane is determined by its values on the basis vectors (helper). -/
theorem apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ) : L (u, v) = L (1, 0) * u + L (0, 1) * v := by
  have : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [this, map_add, map_smul, map_smul]
  simp [mul_comm]

/-- OpenStax Calculus 3:Theorem 4.5 (CA-524). Clairaut's theorem: if `f` is `C²` near `(a,b)`
then the mixed second partial derivatives `f_xy` and `f_yx` agree at `(a,b)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.5, p. 346"]
theorem clairaut {f : ℝ × ℝ → ℝ} {a b : ℝ} (hf : ContDiffAt ℝ 2 f (a, b)) :
    deriv (fun y => deriv (fun x => f (x, y)) a) b =
      deriv (fun x => deriv (fun y => f (x, y)) b) a := by
  have hev : ∀ᶠ p in 𝓝 (a, b), DifferentiableAt ℝ f p := by
    have := hf.eventually (by simp)
    exact this.mono fun p hp => hp.differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (fderiv ℝ f) (a, b) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := (hf.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])) (1, 0) (0, 1)
  have h2 := hd1.hasFDerivAt
  have hL : HasDerivAt (fun y => deriv (fun x => f (x, y)) a)
      (fderiv ℝ (fderiv ℝ f) (a, b) (0, 1) (1, 0)) b := by
    have e1 : HasDerivAt (fun y : ℝ => (a, y)) ((0 : ℝ), (1 : ℝ)) b :=
      (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
    have e2 := h2.comp_hasDerivAt b e1
    have e3 := (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp_hasDerivAt b e2
    refine e3.congr_of_eventuallyEq ?_
    have : ∀ᶠ y in 𝓝 b, DifferentiableAt ℝ f (a, y) :=
      (Continuous.tendsto (continuous_const.prodMk continuous_id) b).eventually hev
    filter_upwards [this] with y hy
    exact (hasDerivAt_partial_fst hy.hasFDerivAt).deriv
  have hR : HasDerivAt (fun x => deriv (fun y => f (x, y)) b)
      (fderiv ℝ (fderiv ℝ f) (a, b) (1, 0) (0, 1)) a := by
    have e1 : HasDerivAt (fun x : ℝ => (x, b)) ((1 : ℝ), (0 : ℝ)) a :=
      (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
    have e2 := h2.comp_hasDerivAt a e1
    have e3 := (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp_hasDerivAt a e2
    refine e3.congr_of_eventuallyEq ?_
    have : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f (x, b) :=
      (Continuous.tendsto (continuous_id.prodMk continuous_const) a).eventually hev
    filter_upwards [this] with x hx
    exact (hasDerivAt_partial_snd hx.hasFDerivAt).deriv
  rw [hL.deriv, hR.deriv, hsymm]

/-- OpenStax Calculus 3:§4.4 Definition (differentiable, two variables) (CA-530). `f` has
derivative `L` at `p` iff `f q - f p` equals `f_x (q₁ - p₁) + f_y (q₂ - p₂)` up to an error that is
`o(‖q - p‖)`, where `f_x = L (1,0)` and `f_y = L (0,1)` are the partials. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (differentiable, two variables), p. 361"]
theorem differentiable_two_variables_iff (f : ℝ × ℝ → ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) (p : ℝ × ℝ) :
    HasFDerivAt f L p ↔
      (fun q : ℝ × ℝ => f q - f p - (L (1, 0) * (q.1 - p.1) + L (0, 1) * (q.2 - p.2)))
        =o[𝓝 p] fun q => q - p := by
  rw [hasFDerivAt_iff_isLittleO]
  have : ∀ q : ℝ × ℝ, L (q - p) = L (1, 0) * (q.1 - p.1) + L (0, 1) * (q.2 - p.2) := fun q =>
    apply_pair L _ _
  simp only [this]

/-- OpenStax Calculus 3:§4.4 Definition (differentiable, three variables) (CA-530). The same for
three variables. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (differentiable, three variables), p. 366"]
theorem differentiable_three_variables_iff (f : ℝ × ℝ × ℝ → ℝ) (L : ℝ × ℝ × ℝ →L[ℝ] ℝ)
    (p : ℝ × ℝ × ℝ) :
    HasFDerivAt f L p ↔
      (fun q : ℝ × ℝ × ℝ => f q - f p -
          (L (1, 0, 0) * (q.1 - p.1) + L (0, 1, 0) * (q.2.1 - p.2.1) +
            L (0, 0, 1) * (q.2.2 - p.2.2))) =o[𝓝 p] fun q => q - p := by
  rw [hasFDerivAt_iff_isLittleO]
  have : ∀ q : ℝ × ℝ × ℝ, L (q - p) = L (1, 0, 0) * (q.1 - p.1) + L (0, 1, 0) * (q.2.1 - p.2.1) +
      L (0, 0, 1) * (q.2.2 - p.2.2) := by
    intro q
    have h : q - p = (q.1 - p.1) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
        (q.2.1 - p.2.1) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        (q.2.2 - p.2.2) • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [h, map_add, map_add, map_smul, map_smul, map_smul]
    simp [mul_comm]
  simp only [this]

/-- OpenStax Calculus 3:Theorem 4.6 (CA-531). A function of two variables differentiable at a
point is continuous there. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.6, p. 363"]
theorem continuousAt_of_differentiableAt_two {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : DifferentiableAt ℝ f p) : ContinuousAt f p :=
  h.continuousAt

/-- OpenStax Calculus 3:§4.4 Fact (differentiable implies continuous, three variables) (CA-531). -/
@[kb "openstaxcalculus2016" "3:§4.4 Fact (differentiable implies continuous, three variables), p. 366"]
theorem continuousAt_of_differentiableAt_three {f : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ}
    (h : DifferentiableAt ℝ f p) : ContinuousAt f p :=
  h.continuousAt

/-- OpenStax Calculus 3:Theorem 4.7 (CA-532). If the first partial derivatives `f₁`, `f₂` of
`f(x,y)` exist near `(a,b)` and are continuous at `(a,b)`, then `f` is differentiable at `(a,b)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.7, p. 363"]
theorem differentiableAt_of_continuous_partials (f f₁ f₂ : ℝ → ℝ → ℝ) (a b : ℝ)
    (h₁ : ∀ᶠ q in 𝓝 (a, b), HasDerivAt (fun x => f x q.2) (f₁ q.1 q.2) q.1)
    (h₂ : ∀ᶠ q in 𝓝 (a, b), HasDerivAt (fun y => f q.1 y) (f₂ q.1 q.2) q.2)
    (c₁ : ContinuousAt (fun q : ℝ × ℝ => f₁ q.1 q.2) (a, b))
    (c₂ : ContinuousAt (fun q : ℝ × ℝ => f₂ q.1 q.2) (a, b)) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2) (a, b) := by
  have hc : Continuous (fun r : ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight r) := by
    exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous
  have := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (a, b)) (f := f)
    (f₁ := fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (f₁ x y))
    (f₂ := fun x y => (1 : ℝ →L[ℝ] ℝ).smulRight (f₂ x y))
    (h₁.mono fun q hq => hq.hasFDerivAt) (h₂.mono fun q hq => hq.hasFDerivAt)
    (hc.continuousAt.comp c₁) (hc.continuousAt.comp c₂)
  exact this.hasFDerivAt.differentiableAt

/-- OpenStax Calculus 3:Theorem 4.8 (CA-534). Chain rule for `z = f(x(t), y(t))`:
`dz/dt = f_x dx/dt + f_y dy/dt`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.8, p. 369"]
theorem chain_rule_one_parameter {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {x' y' t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) (hf : DifferentiableAt ℝ f (x t, y t)) :
    HasDerivAt (fun s => f (x s, y s))
      (deriv (fun u => f (u, y t)) (x t) * x' + deriv (fun v => f (x t, v)) (y t) * y') t := by
  have hg : HasDerivAt (fun s => (x s, y s)) (x', y') t := hx.prodMk hy
  have h := hf.hasFDerivAt.comp_hasDerivAt t hg
  rw [(hasDerivAt_partial_fst hf.hasFDerivAt).deriv, (hasDerivAt_partial_snd hf.hasFDerivAt).deriv]
  exact h.congr_deriv (apply_pair _ _ _)

/-- OpenStax Calculus 3:Theorem 4.9 (CA-535). Chain rule for `z = f(x(u,v), y(u,v))`:
`z_u = f_x x_u + f_y y_u` and `z_v = f_x x_v + f_y y_v`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.9, p. 373"]
theorem chain_rule_two_parameters {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ → ℝ} {xu yu xv yv u v : ℝ}
    (hxu : HasDerivAt (fun s => x s v) xu u) (hyu : HasDerivAt (fun s => y s v) yu u)
    (hxv : HasDerivAt (fun s => x u s) xv v) (hyv : HasDerivAt (fun s => y u s) yv v)
    (hf : DifferentiableAt ℝ f (x u v, y u v)) :
    HasDerivAt (fun s => f (x s v, y s v))
      (deriv (fun a => f (a, y u v)) (x u v) * xu + deriv (fun b => f (x u v, b)) (y u v) * yu) u ∧
    HasDerivAt (fun s => f (x u s, y u s))
      (deriv (fun a => f (a, y u v)) (x u v) * xv + deriv (fun b => f (x u v, b)) (y u v) * yv) v :=
  ⟨chain_rule_one_parameter (x := fun s => x s v) (y := fun s => y s v) hxu hyu hf,
    chain_rule_one_parameter (x := fun s => x u s) (y := fun s => y u s) hxv hyv hf⟩

/-- OpenStax Calculus 3:Theorem 4.10 (CA-536). Generalized chain rule: for `f` of `n` variables
`x_i = X_i(t)` depending on `m` variables, `∂(f∘X)/∂t_j = ∑ᵢ f_{x_i} ∂x_i/∂t_j`
(partials as derivatives along coordinate directions). -/
@[kb "openstaxcalculus2016" "3:Theorem 4.10, p. 375"]
theorem generalized_chain_rule {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {X : (Fin m → ℝ) → (Fin n → ℝ)}
    {t : Fin m → ℝ} (hX : DifferentiableAt ℝ X t) (hf : DifferentiableAt ℝ f (X t)) (j : Fin m) :
    lineDeriv ℝ (fun s => f (X s)) t (Pi.single j 1) =
      ∑ i, lineDeriv ℝ f (X t) (Pi.single i 1) *
        lineDeriv ℝ (fun s => X s i) t (Pi.single j 1) := by
  have hXi : ∀ i, DifferentiableAt ℝ (fun s => X s i) t := fun i =>
    (differentiableAt_pi.mp hX) i
  have hc : DifferentiableAt ℝ (fun s => f (X s)) t := hf.comp t hX
  rw [hc.lineDeriv_eq_fderiv]
  simp_rw [hf.lineDeriv_eq_fderiv]
  have hfd : fderiv ℝ (fun s => f (X s)) t = (fderiv ℝ f (X t)).comp (fderiv ℝ X t) :=
    fderiv_comp t hf hX
  rw [hfd, ContinuousLinearMap.comp_apply]
  have hv : fderiv ℝ X t (Pi.single j 1) = ∑ i, (fderiv ℝ X t (Pi.single j 1)) i • Pi.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, (hXi i).lineDeriv_eq_fderiv]
  have : fderiv ℝ (fun s => X s i) t = (ContinuousLinearMap.proj i).comp (fderiv ℝ X t) := by
    have := fderiv_comp t (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt hX
    rw [ContinuousLinearMap.fderiv] at this
    exact this
  rw [this]
  rfl

/-- OpenStax Calculus 3:Theorem 4.11 (CA-537). Implicit differentiation: if `y(x)` is
differentiable, `F(x, y(x)) = 0` near `a`, `F` is differentiable and `F_y ≠ 0`, then
`dy/dx = -F_x / F_y`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.11, p. 377"]
theorem implicit_derivative_two_variables {F : ℝ × ℝ → ℝ} {y : ℝ → ℝ} {a : ℝ}
    (hy : DifferentiableAt ℝ y a) (hF : DifferentiableAt ℝ F (a, y a))
    (h0 : ∀ᶠ x in 𝓝 a, F (x, y x) = 0) (hFy : deriv (fun v => F (a, v)) (y a) ≠ 0) :
    deriv y a = -deriv (fun u => F (u, y a)) a / deriv (fun v => F (a, v)) (y a) := by
  have h : HasDerivAt (fun s => F (s, y s))
      (deriv (fun u => F (u, y a)) a * 1 + deriv (fun v => F (a, v)) (y a) * deriv y a) a :=
    chain_rule_one_parameter (x := fun s => s) (hasDerivAt_id a) hy.hasDerivAt hF
  have h' : HasDerivAt (fun s => F (s, y s)) 0 a :=
    (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq h0
  have := h.unique h'
  field_simp
  linarith

/-- OpenStax Calculus 3:Theorem 4.11 (CA-537). For `F(x,y,z) = 0` defining `z(x,y)`:
`z_x = -F_x / F_z` (with `F_x`, `F_z` the partials, i.e. the derivative `L` applied to the basis
vectors). -/
@[kb "openstaxcalculus2016" "3:Theorem 4.11, p. 377"]
theorem implicit_derivative_three_variables_x {F : ℝ × ℝ × ℝ → ℝ} {L : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    {z : ℝ → ℝ → ℝ} {a b zx : ℝ} (hz : HasDerivAt (fun s => z s b) zx a)
    (hF : HasFDerivAt F L (a, b, z a b)) (h0 : ∀ᶠ x in 𝓝 a, F (x, b, z x b) = 0)
    (hFz : L (0, 0, 1) ≠ 0) : zx = -L (1, 0, 0) / L (0, 0, 1) := by
  have hg : HasDerivAt (fun s => (s, b, z s b)) ((1 : ℝ), (0 : ℝ), zx) a :=
    (hasDerivAt_id a).prodMk ((hasDerivAt_const a b).prodMk hz)
  have h := hF.comp_hasDerivAt a hg
  have h' : HasDerivAt (fun s => F (s, b, z s b)) 0 a :=
    (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq h0
  have h1 := h.unique h'
  have e : L (1, 0, zx) = L (1, 0, 0) + L (0, 0, 1) * zx := by
    have : ((1 : ℝ), (0 : ℝ), zx) = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + zx • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    simp [mul_comm]
  rw [e] at h1
  field_simp
  linarith

/-- OpenStax Calculus 3:Theorem 4.11 (CA-537). For `F(x,y,z) = 0` defining `z(x,y)`:
`z_y = -F_y / F_z`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.11, p. 377"]
theorem implicit_derivative_three_variables_y {F : ℝ × ℝ × ℝ → ℝ} {L : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    {z : ℝ → ℝ → ℝ} {a b zy : ℝ} (hz : HasDerivAt (fun s => z a s) zy b)
    (hF : HasFDerivAt F L (a, b, z a b)) (h0 : ∀ᶠ y in 𝓝 b, F (a, y, z a y) = 0)
    (hFz : L (0, 0, 1) ≠ 0) : zy = -L (0, 1, 0) / L (0, 0, 1) := by
  have hg : HasDerivAt (fun s => (a, s, z a s)) ((0 : ℝ), (1 : ℝ), zy) b :=
    (hasDerivAt_const b a).prodMk ((hasDerivAt_id b).prodMk hz)
  have h := hF.comp_hasDerivAt b hg
  have h' : HasDerivAt (fun s => F (a, s, z a s)) 0 b :=
    (hasDerivAt_const b (0 : ℝ)).congr_of_eventuallyEq h0
  have h1 := h.unique h'
  have e : L (0, 1, zy) = L (0, 1, 0) + L (0, 0, 1) * zy := by
    have : ((0 : ℝ), (1 : ℝ), zy) = ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + zy • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    simp [mul_comm]
  rw [e] at h1
  field_simp
  linarith

/-- OpenStax Calculus 3:§4.6 Definition (directional derivative, two variables) (CA-538). The
directional derivative of `f` at `p` in direction `u` (a unit vector in `ℝⁿ`; `n = 2, 3` in the
book) is the limit of `(f (p + t u) - f p) / t` as `t → 0`. -/
@[kb "openstaxcalculus2016" "3:§4.6 Definition (directional derivative, two variables), p. 383"]
theorem directional_derivative_iff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p u : EuclideanSpace ℝ (Fin n)) (_hu : ‖u‖ = 1) (L : ℝ) :
    HasLineDerivAt ℝ f L p u ↔
      Tendsto (fun t : ℝ => (f (p + t • u) - f p) / t) (𝓝[≠] 0) (𝓝 L) := by
  rw [hasLineDerivAt_iff_tendsto_slope_zero]
  simp [div_eq_inv_mul]

/-- OpenStax Calculus 3:§4.6 Definition (gradient, two variables) (CA-539). The `i`-th component of
the gradient of a differentiable `f` on Euclidean `n`-space is the partial derivative in the `i`-th
coordinate direction. -/
@[kb "openstaxcalculus2016" "3:§4.6 Definition (gradient, two variables), p. 385"]
theorem gradient_component_eq_partial {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f p) (i : Fin n) :
    gradient f p i = lineDeriv ℝ f p (EuclideanSpace.single i 1) := by
  rw [hf.lineDeriv_eq_fderiv, ← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- OpenStax Calculus 3:Theorem 4.12 (CA-540). The directional derivative of a differentiable `f`
in direction `u` equals the gradient dotted with `u`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.12, p. 384"]
theorem directional_derivative_eq_inner_gradient {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f p) (u : EuclideanSpace ℝ (Fin n)) :
    lineDeriv ℝ f p u = inner ℝ (gradient f p) u := by
  rw [hf.lineDeriv_eq_fderiv, inner_gradient_left]

/-- OpenStax Calculus 3:Theorem 4.12 (CA-540). In the plane, the directional derivative in the unit
direction `(cos θ, sin θ)` is `f_x cos θ + f_y sin θ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.12, p. 384"]
theorem directional_derivative_plane {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p)
    (θ : ℝ) :
    lineDeriv ℝ f p !₂[Real.cos θ, Real.sin θ] =
      lineDeriv ℝ f p (EuclideanSpace.single 0 1) * Real.cos θ +
        lineDeriv ℝ f p (EuclideanSpace.single 1 1) * Real.sin θ := by
  rw [directional_derivative_eq_inner_gradient hf, ← gradient_component_eq_partial hf,
    ← gradient_component_eq_partial hf, PiLp.inner_apply, Fin.sum_univ_two]
  simp [mul_comm]

/-- OpenStax Calculus 3:§4.7 Definition (local and global extrema) (CA-544). `f` has a local
maximum at `p` iff `f q ≤ f p` on some disk about `p`. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (local and global extrema), p. 397"]
theorem local_max_iff_disk (f : Plane → ℝ) (p : Plane) :
    IsLocalMax f p ↔ ∃ δ > 0, ∀ q ∈ ball p δ, f q ≤ f p := by
  unfold IsLocalMax IsMaxFilter
  exact Metric.eventually_nhds_iff_ball

/-- OpenStax Calculus 3:§4.7 Definition (local and global extrema) (CA-544). Local minimum. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (local and global extrema), p. 397"]
theorem local_min_iff_disk (f : Plane → ℝ) (p : Plane) :
    IsLocalMin f p ↔ ∃ δ > 0, ∀ q ∈ ball p δ, f p ≤ f q := by
  unfold IsLocalMin IsMinFilter
  exact Metric.eventually_nhds_iff_ball

/-- OpenStax Calculus 3:Theorem 4.16 (CA-545). If `f` has a local extremum at `(a,b)`, then
both partial derivatives (as derivatives of the one-variable slices) vanish there. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.16, p. 397"]
theorem local_extremum_partials_zero {f : ℝ × ℝ → ℝ} {a b : ℝ} (h : IsLocalExtr f (a, b)) :
    deriv (fun x => f (x, b)) a = 0 ∧ deriv (fun y => f (a, y)) b = 0 :=
  ⟨IsLocalExtr.deriv_eq_zero
      (h.comp_continuous (g := fun x : ℝ => (x, b)) (b := a)
        (continuous_id.prodMk continuous_const).continuousAt),
    IsLocalExtr.deriv_eq_zero
      (h.comp_continuous (g := fun y : ℝ => (a, y)) (b := b)
        (continuous_const.prodMk continuous_id).continuousAt)⟩

/-- OpenStax Calculus 3:§4.7 Definition (bounded set) (CA-548). A set in the plane is bounded iff
it lies in some disk (about a given point). -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (bounded set), p. 401"]
theorem bounded_iff_subset_disk (S : Set Plane) (c : Plane) :
    Bornology.IsBounded S ↔ ∃ r, S ⊆ ball c r :=
  Metric.isBounded_iff_subset_ball c

/-- OpenStax Calculus 3:Theorem 4.18 (CA-549). A continuous function on a nonempty closed bounded
set in the plane attains an absolute maximum and an absolute minimum. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.18, p. 402"]
theorem extreme_value_closed_bounded {S : Set Plane} (hc : IsClosed S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty) {f : Plane → ℝ} (hf : ContinuousOn f S) :
    (∃ p ∈ S, IsMaxOn f S p) ∧ ∃ q ∈ S, IsMinOn f S q := by
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hc hb
  exact ⟨hK.exists_isMaxOn hne hf, hK.exists_isMinOn hne hf⟩

/-! ## Results proved in undergrad-kb -/

section ProvedInKB

open UndergradKB.Calculus (partialX partialY partialXX gradNorm directionalDeriv hessianDet
  IsSaddlePoint IsCriticalPoint)
open UndergradKB.Calculus.PDEExamples (HeatEq2D WaveEq2D LaplaceEq2D sep expL sinL cosL)

/-- OpenStax Calculus 3:§4.2 Principle (limit fails if path-dependent) (CA-513).
If `f` tends to different values along two paths approaching `p`, then `f` has no limit at `p`. -/
@[kb "openstaxcalculus2016" "3:§4.2 Principle (limit fails if path-dependent), p. 328"]
theorem limit_fails_if_path_dependent {ι κ : Type*} {l₁ : Filter ι} {l₂ : Filter κ} [NeBot l₁]
    [NeBot l₂] {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {γ₁ : ι → ℝ × ℝ} {γ₂ : κ → ℝ × ℝ} {L₁ L₂ : ℝ}
    (hγ₁ : Tendsto γ₁ l₁ (𝓝[≠] p)) (hγ₂ : Tendsto γ₂ l₂ (𝓝[≠] p))
    (h₁ : Tendsto (f ∘ γ₁) l₁ (𝓝 L₁)) (h₂ : Tendsto (f ∘ γ₂) l₂ (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    ¬ ∃ L, Tendsto f (𝓝[≠] p) (𝓝 L) :=
  UndergradKB.Calculus.not_limit_of_two_paths hγ₁ hγ₂ h₁ h₂ hne

/-- OpenStax Calculus 3:Equation 4.17 (CA-526).
The two-dimensional heat equation, wave equation and Laplace's equation, each with an explicit
solution built from exponentials, sines and cosines. -/
@[kb "openstaxcalculus2016" "3:Equation 4.17, p. 347"]
theorem classical_pde_examples :
    (∀ α a b : ℝ, HeatEq2D α (sep (expL (α ^ 2 * (a ^ 2 + b ^ 2))) (sinL a) (sinL b))) ∧
    (∀ c a b ω : ℝ, ω ^ 2 = c ^ 2 * (a ^ 2 + b ^ 2) → WaveEq2D c (sep (cosL ω) (sinL a) (sinL b))) ∧
    LaplaceEq2D (fun x y => Real.exp x * Real.sin y) :=
  ⟨UndergradKB.Calculus.PDEExamples.heat_eq_example,
    fun c a b ω h => UndergradKB.Calculus.PDEExamples.wave_eq_example c a b ω h,
    UndergradKB.Calculus.PDEExamples.laplace_eq_exp_sin⟩

/-- OpenStax Calculus 3:Theorem 4.13 (CA-541).
Directional derivatives are bounded by the gradient length, vanish when the gradient is zero, attain
`‖∇f‖` exactly in the gradient direction, and `-‖∇f‖` in the opposite direction. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.13, p. 386"]
theorem directional_derivative_extremes (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (∀ u : ℝ × ℝ, u.1 ^ 2 + u.2 ^ 2 = 1 → |directionalDeriv f p u| ≤ gradNorm f p) ∧
    (partialX f p = 0 → partialY f p = 0 → ∀ u : ℝ × ℝ, directionalDeriv f p u = 0) ∧
    (gradNorm f p ≠ 0 → ∀ u : ℝ × ℝ, u.1 ^ 2 + u.2 ^ 2 = 1 →
      (directionalDeriv f p u = gradNorm f p ↔
        u = (partialX f p / gradNorm f p, partialY f p / gradNorm f p))) ∧
    (gradNorm f p ≠ 0 →
      directionalDeriv f p (-(partialX f p / gradNorm f p), -(partialY f p / gradNorm f p)) =
          -gradNorm f p ∧
      directionalDeriv f p (-(partialY f p / gradNorm f p), partialX f p / gradNorm f p) = 0) :=
  ⟨fun u hu => UndergradKB.Calculus.directionalDeriv_abs_le f p u hu,
    fun hx hy u => UndergradKB.Calculus.directionalDeriv_eq_zero_of_grad_zero f p u hx hy,
    fun hN u hu => UndergradKB.Calculus.directionalDeriv_max_iff f p u hu hN,
    fun hN => UndergradKB.Calculus.directionalDeriv_min_and_perp f p hN⟩

/-- OpenStax Calculus 3:Theorem 4.14 (CA-542).
Along a curve on which `f` is constant, the gradient is orthogonal to the velocity, i.e.
`f_x x' + f_y y' = 0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.14, p. 389"]
theorem gradient_perpendicular_to_level_curve {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {x' y' t₀ c : ℝ}
    (hx : HasDerivAt x x' t₀) (hy : HasDerivAt y y' t₀)
    (hf : DifferentiableAt ℝ f (x t₀, y t₀)) (hlevel : ∀ᶠ t in 𝓝 t₀, f (x t, y t) = c) :
    partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y' = 0 :=
  UndergradKB.Calculus.gradient_orthogonal_level_curve hx hy hf hlevel

/-- OpenStax Calculus 3:Theorem 4.17 (CA-547).
Second derivative test at a critical point with discriminant `D = f_xx f_yy - f_xy²`: `D > 0` and
`f_xx > 0` gives a local minimum, `D > 0` and `f_xx < 0` a local maximum, `D < 0` a saddle point;
`D = 0` is inconclusive (witnessed by `x⁴ + y⁴` and `x⁴ - y⁴`). -/
@[kb "openstaxcalculus2016" "3:Theorem 4.17, p. 398"]
theorem second_derivative_test {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p)
    (hx : partialX f p = 0) (hy : partialY f p = 0) :
    (0 < hessianDet f p → 0 < partialXX f p → IsLocalMin f p) ∧
    (0 < hessianDet f p → partialXX f p < 0 → IsLocalMax f p) ∧
    (hessianDet f p < 0 → ¬ IsLocalMin f p ∧ ¬ IsLocalMax f p ∧ IsSaddlePoint f p) ∧
    ((hessianDet (fun q : ℝ × ℝ => q.1 ^ 4 + q.2 ^ 4) (0, 0) = 0 ∧
      IsLocalMin (fun q : ℝ × ℝ => q.1 ^ 4 + q.2 ^ 4) (0, 0)) ∧
    (hessianDet (fun q : ℝ × ℝ => q.1 ^ 4 + (-1) * q.2 ^ 4) (0, 0) = 0 ∧
      ¬ IsLocalExtr (fun q : ℝ × ℝ => q.1 ^ 4 + (-1) * q.2 ^ 4) (0, 0))) :=
  ⟨fun hD hxx => UndergradKB.Calculus.second_derivative_test_min hf hx hy hD hxx,
    fun hD hxx => UndergradKB.Calculus.second_derivative_test_max hf hx hy hD hxx,
    fun hD => UndergradKB.Calculus.second_derivative_test_saddle hf hx hy hD,
    UndergradKB.Calculus.second_derivative_test_inconclusive⟩

/-- OpenStax Calculus 3:Theorem 4.19 (CA-550).
A function continuous on a compact set and differentiable inside attains its absolute maximum and
minimum, each on the boundary or at an interior critical point. -/
@[kb "openstaxcalculus2016" "3:Theorem 4.19, p. 402"]
theorem absolute_extrema_closed_bounded {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (hcont : ContinuousOn f K)
    (hdiff : ∀ p ∈ interior K, DifferentiableAt ℝ f p) :
    (∃ p ∈ K, IsMaxOn f K p ∧ (p ∈ frontier K ∨ (p ∈ interior K ∧ IsCriticalPoint f p))) ∧
    (∃ p ∈ K, IsMinOn f K p ∧ (p ∈ frontier K ∨ (p ∈ interior K ∧ IsCriticalPoint f p))) :=
  UndergradKB.Calculus.absolute_extrema_on_compact hK hne hcont hdiff

/-- OpenStax Calculus 3:Theorem 4.20 (CA-551).
Lagrange multipliers: at a local extremum of `f` on `g = c` with `∇g ≠ 0`, `∇f = λ ∇g`
(written here for two variables). -/
@[kb "openstaxcalculus2016" "3:Theorem 4.20, p. 412"]
theorem lagrange_multipliers_one_constraint {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {c : ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p) (hc : g p = c)
    (hext : IsLocalExtrOn f {q | g q = c} p) (hgrad : partialX g p ≠ 0 ∨ partialY g p ≠ 0) :
    ∃ l : ℝ, partialX f p = l * partialX g p ∧ partialY f p = l * partialY g p :=
  UndergradKB.Calculus.lagrange_multiplier_two_vars hf hg hc hext hgrad

/-- OpenStax Calculus 3:§4.8 Method (Lagrange multipliers, two constraints) (CA-552).
At a local extremum of `f` subject to `g = c` and `h = d` with independent gradients,
`∇f = λ ∇g + μ ∇h` (written here for two variables). -/
@[kb "openstaxcalculus2016" "3:§4.8 Method (Lagrange multipliers, two constraints), p. 416"]
theorem lagrange_multipliers_two_constraints {f g h : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) (hg : ContDiffAt ℝ 1 g p) (hh : ContDiffAt ℝ 1 h p)
    (hext : IsLocalExtrOn f {q | g q = g p ∧ h q = h p} p)
    (hdet : partialX g p * partialY h p - partialY g p * partialX h p ≠ 0) :
    ∃ l m : ℝ, partialX f p = l * partialX g p + m * partialX h p ∧
      partialY f p = l * partialY g p + m * partialY h p :=
  UndergradKB.Calculus.lagrange_multiplier_two_constraints_two_vars hf hg hh hext hdet

end ProvedInKB

/-! ## Wave 3: further results -/

section Wave3

open UndergradKB.Calculus (partialX partialY tangentPlane totalDifferential IsSaddlePoint
  IsCriticalPoint)

/-- OpenStax Calculus 3:§4.4 Definition (tangent plane) (CA-527).
If a curve `(x(t), y(t))` in the domain passes through the point `(x t₀, y t₀)` where `f` is
differentiable, the curve `t ↦ f(x(t), y(t))` on the surface has the derivative `f_x x' + f_y y'`, and the
points of its tangent line all lie on the plane `z = tangentPlane`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (tangent plane), p. 355"]
theorem tangent_lines_lie_in_tangent_plane {f : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {x' y' t₀ : ℝ}
    (hx : HasDerivAt x x' t₀) (hy : HasDerivAt y y' t₀)
    (hf : DifferentiableAt ℝ f (x t₀, y t₀)) :
    HasDerivAt (fun t => f (x t, y t))
        (partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y') t₀ ∧
    ∀ s : ℝ, f (x t₀, y t₀) + s * (partialX f (x t₀, y t₀) * x' + partialY f (x t₀, y t₀) * y') =
      tangentPlane f (x t₀) (y t₀) (x t₀ + s * x') (y t₀ + s * y') :=
  UndergradKB.Calculus.curve_tangent_in_tangent_plane hx hy hf

/-- OpenStax Calculus 3:§4.4 Definition (equation of the tangent plane) (CA-528).
The tangent plane to `z = f(x,y)` at `(a,b)` is `z = f(a,b) + f_x(a,b)(x-a) + f_y(a,b)(y-b)`, and it is the
only plane that approximates `f` to first order at that point. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (equation of the tangent plane), p. 356"]
theorem tangent_plane_equation {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    (∀ x y : ℝ, tangentPlane f p.1 p.2 x y
        = f (p.1, p.2) + partialX f (p.1, p.2) * (x - p.1) + partialY f (p.1, p.2) * (y - p.2)) ∧
    ∀ {z₀ α β : ℝ},
      (fun q : ℝ × ℝ => f q - (z₀ + α * (q.1 - p.1) + β * (q.2 - p.2))) =o[𝓝 p] (fun q => q - p) →
      z₀ = f p ∧ α = partialX f p ∧ β = partialY f p :=
  ⟨fun _ _ => rfl, fun h => UndergradKB.Calculus.tangent_plane_unique hf h⟩

/-- OpenStax Calculus 3:§4.4 Definition (linear approximation) (CA-529).
Near `p = (a,b)` a function differentiable at `p` agrees with its tangent-plane function up to an error
that is small compared with the distance to `p`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (linear approximation), p. 359"]
theorem linear_approximation_two_variables {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    (fun q : ℝ × ℝ => f q - tangentPlane f p.1 p.2 q.1 q.2) =o[𝓝 p] fun q => q - p :=
  UndergradKB.Calculus.linear_approximation hf

/-- OpenStax Calculus 3:§4.4 Definition (differentials, total differential) (CA-533).
The total differential `dz = f_x dx + f_y dy` approximates the increment `f(p + d) - f(p)` up to an error
that is small compared with `‖d‖`. -/
@[kb "openstaxcalculus2016" "3:§4.4 Definition (differentials, total differential), p. 364"]
theorem total_differential_approximates_increment {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    (∀ dx dy : ℝ, totalDifferential f p dx dy = partialX f p * dx + partialY f p * dy) ∧
    (fun d : ℝ × ℝ => f (p + d) - f p - totalDifferential f p d.1 d.2) =o[𝓝 0] fun d => d :=
  ⟨fun _ _ => rfl, UndergradKB.Calculus.total_differential_approx hf⟩

/-- OpenStax Calculus 3:§4.7 Definition (critical point) (CA-543).
For a function differentiable at `p`, being a critical point means that both first partial derivatives
vanish there (equivalently the derivative is zero), and every local extremum is a critical point. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (critical point), p. 395"]
theorem critical_point_characterization {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    (IsCriticalPoint f p ↔ partialX f p = 0 ∧ partialY f p = 0) ∧
    (IsLocalExtr f p → IsCriticalPoint f p) :=
  ⟨UndergradKB.Calculus.isCriticalPoint_iff hf,
    fun h => UndergradKB.Calculus.isCriticalPoint_of_isLocalExtr h hf⟩

/-- OpenStax Calculus 3:§4.7 Definition (saddle point) (CA-546).
For a function differentiable at `p`, a saddle point is a point where both first partial derivatives
vanish but which is not a local extremum. -/
@[kb "openstaxcalculus2016" "3:§4.7 Definition (saddle point), p. 398"]
theorem saddle_point_characterization {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f p) :
    IsSaddlePoint f p ↔ partialX f p = 0 ∧ partialY f p = 0 ∧ ¬ IsLocalExtr f p :=
  UndergradKB.Calculus.isSaddlePoint_iff hf

end Wave3

end UndergradKB.Calculus.Course.V3C4
