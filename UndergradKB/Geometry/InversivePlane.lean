import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection
import UndergradKB.Geometry.TransversalEulerInversion
import UndergradKB.Geometry.Arcs
import UndergradKB.Common.Attr

/-! # The inversive plane and space (Petrunin, chapters 10, 14 C, 16 E)

Section 10 B (p. 76): the inversive plane is `OnePoint P` (Mathlib's one-point compactification),
the inversion across a circle is extended by exchanging the centre and `∞`, and circlines are
circles together with lines (each completed by `∞`). Section 14 C (p. 117): inversive
transformations. Section 10 E (pp. 81-82): angles after inversion, Proposition 10.24, Theorem 10.25,
Corollary 10.26. Section 16 E (p. 135): inversion across a sphere and Theorem 16.5.

Most of the general statements are made in any real inner product space `V` with a torsor `P`
(dimension arbitrary); the plane versions assume `Fact (finrank ℝ V = 2)`. -/

namespace UndergradKB.Geometry

open EuclideanGeometry Metric OnePoint
open scoped RealInnerProductSpace

section Basic

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {c : P} {R : ℝ}

open scoped Classical in
/-- The extension of the inversion `EuclideanGeometry.inversion c R` to the inversive plane
`OnePoint P`: the centre `c` and `∞` are exchanged (Petrunin, p. 76). -/
@[kb "petrunin2025" "Definition, inversive plane, p. 76"]
noncomputable def inversionOP (c : P) (R : ℝ) (z : OnePoint P) : OnePoint P :=
  z.elim (c : OnePoint P) (fun x => if x = c then ∞ else ((inversion c R x : P) : OnePoint P))

@[simp] theorem inversionOP_infty : inversionOP c R (∞ : OnePoint P) = (c : OnePoint P) := rfl

@[simp] theorem inversionOP_center : inversionOP c R (c : OnePoint P) = ∞ := by
  simp [inversionOP]

theorem inversionOP_coe_of_ne {x : P} (hx : x ≠ c) :
    inversionOP c R (x : OnePoint P) = ((inversion c R x : P) : OnePoint P) := by
  simp [inversionOP, hx]

/-- The extended inversion is an involution. -/
@[kb "petrunin2025" "Definition, inversive plane, p. 76"]
theorem inversionOP_involutive (hR : R ≠ 0) : Function.Involutive (inversionOP c R) := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
    by_cases hx : x = c
    · subst hx; simp
    · have hx' : inversion c R x ≠ c := by simpa [inversion_eq_center hR] using hx
      rw [inversionOP_coe_of_ne hx, inversionOP_coe_of_ne hx', inversion_inversion c hR]

/-- The extended inversion is a bijection of the inversive plane. -/
@[kb "petrunin2025" "Definition, inversive plane, p. 76"]
theorem inversionOP_bijective (hR : R ≠ 0) : Function.Bijective (inversionOP c R) :=
  (inversionOP_involutive hR).bijective

/-- The extended inversion as a permutation. -/
noncomputable def inversionEquiv (c : P) (R : ℝ) (hR : R ≠ 0) : OnePoint P ≃ OnePoint P :=
  (inversionOP_involutive (c := c) hR).toPerm

theorem inversionOP_image_eq_of_maps (hR : R ≠ 0) {S S' : Set (OnePoint P)}
    (h1 : ∀ z ∈ S, inversionOP c R z ∈ S') (h2 : ∀ z ∈ S', inversionOP c R z ∈ S) :
    inversionOP c R '' S = S' := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact h1 w hw
  · intro hz
    exact ⟨inversionOP c R z, h2 z hz, inversionOP_involutive hR z⟩

theorem inversion_mem_of_image_eq (hR : R ≠ 0) {A B : Set P} (h : inversion c R '' A = B) :
    (∀ x ∈ A, inversion c R x ∈ B) ∧ (∀ y ∈ B, inversion c R y ∈ A) := by
  refine ⟨fun x hx => h ▸ Set.mem_image_of_mem _ hx, fun y hy => ?_⟩
  rw [← h] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [inversion_inversion c hR]

/-! ### Circlines -/

/-- The circle with centre `Q` and radius `s` inside the inversive plane. -/
def circOP (Q : P) (s : ℝ) : Set (OnePoint P) := (fun x : P => (x : OnePoint P)) '' Metric.sphere Q s

/-- A hyperplane (a line, in the plane) `H` together with the point `∞`. -/
def hypOP (H : Set P) : Set (OnePoint P) := insert ∞ ((fun x : P => (x : OnePoint P)) '' H)

variable (V) in
/-- `H` is a hyperplane of the affine space: `{x | ⟪x - o, n⟫ = t}` with `n ≠ 0`. -/
def IsHyperplaneSet (H : Set P) : Prop :=
  ∃ (o : P) (n : V) (t : ℝ), n ≠ 0 ∧ H = {x | ⟪x -ᵥ o, n⟫ = t}

variable (V) in
/-- A *generalized sphere* of the inversive space: a sphere of positive radius, or a hyperplane
together with `∞` (in the plane: a circline). -/
def IsInvSphere (S : Set (OnePoint P)) : Prop :=
  (∃ (Q : P) (s : ℝ), 0 < s ∧ S = circOP Q s) ∨ (∃ H : Set P, IsHyperplaneSet V H ∧ S = hypOP H)

theorem IsHyperplaneSet.rebase {H : Set P} (h : IsHyperplaneSet V H) (c : P) :
    ∃ (n : V) (t : ℝ), n ≠ 0 ∧ H = {x | ⟪x -ᵥ c, n⟫ = t} := by
  obtain ⟨o, n, t, hn, rfl⟩ := h
  refine ⟨n, t + ⟪o -ᵥ c, n⟫, hn, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← vsub_add_vsub_cancel x o c, inner_add_left]
  constructor <;> intro h <;> linarith

theorem isHyperplaneSet_perpBisector (p q : P) (h : p ≠ q) :
    IsHyperplaneSet V (AffineSubspace.perpBisector p q : Set P) := by
  refine ⟨midpoint ℝ p q, q -ᵥ p, 0, fun h0 => h (vsub_eq_zero_iff_eq.mp h0).symm, ?_⟩
  ext x
  simp [AffineSubspace.mem_perpBisector_iff_inner_eq_zero]

theorem mem_circOP_coe {Q x : P} {s : ℝ} : (x : OnePoint P) ∈ circOP Q s ↔ x ∈ sphere Q s := by
  unfold circOP
  exact (OnePoint.coe_injective.mem_set_image)

theorem mem_hypOP_coe {H : Set P} {x : P} : (x : OnePoint P) ∈ hypOP H ↔ x ∈ H := by
  unfold hypOP
  simp

theorem infty_mem_hypOP (H : Set P) : (∞ : OnePoint P) ∈ hypOP H := Set.mem_insert _ _

theorem infty_notMem_circOP (Q : P) (s : ℝ) : (∞ : OnePoint P) ∉ circOP Q s := by
  rintro ⟨x, _, h⟩
  exact OnePoint.coe_ne_infty x h

/-- Image of a circle not through the centre. -/
theorem inversionOP_image_circOP_of_ne (hR : R ≠ 0) {Q : P} {s : ℝ} (hs : 0 < s)
    (hd : dist Q c ≠ s) :
    inversionOP c R '' circOP Q s =
      circOP (invSphereCenter c R Q s) (invSphereRadius c R Q s) := by
  obtain ⟨himg, hnc⟩ := image_inversion_sphere hR hs.le hd
  obtain ⟨hA, hB⟩ := inversion_mem_of_image_eq hR himg
  have hcQ : c ∉ sphere Q s := fun h => hd (by rw [dist_comm]; exact h)
  refine inversionOP_image_eq_of_maps hR ?_ ?_
  · rintro z ⟨x, hx, rfl⟩
    have hxc : x ≠ c := fun h => hcQ (h ▸ hx)
    rw [inversionOP_coe_of_ne hxc]
    exact ⟨_, hA x hx, rfl⟩
  · rintro z ⟨y, hy, rfl⟩
    have hyc : y ≠ c := fun h => hnc (h ▸ hy)
    rw [inversionOP_coe_of_ne hyc]
    exact ⟨_, hB y hy, rfl⟩

/-- Image of a circle through the centre: a line (completed by `∞`). -/
theorem inversionOP_image_circOP_through {Q : P} {s : ℝ} (hR : R ≠ 0) (hs : 0 < s)
    (hd : dist Q c = s) :
    inversionOP c R '' circOP Q s =
      hypOP (AffineSubspace.perpBisector c (inversion c R Q) : Set P) := by
  have hQ : Q ≠ c := fun h => by rw [h, dist_self] at hd; linarith
  obtain ⟨himg, hnc⟩ := image_inversion_sphere_through_centre hR hQ
  rw [hd] at himg
  obtain ⟨hA, hB⟩ := inversion_mem_of_image_eq hR himg
  have hcm : c ∈ sphere Q s := by rw [Metric.mem_sphere, dist_comm]; exact hd
  refine inversionOP_image_eq_of_maps hR ?_ ?_
  · rintro z ⟨x, hx, rfl⟩
    by_cases hxc : x = c
    · subst hxc; simp [infty_mem_hypOP]
    · rw [inversionOP_coe_of_ne hxc, mem_hypOP_coe]
      exact hA x ⟨hx, hxc⟩
  · rintro z (rfl | ⟨w, hw, rfl⟩)
    · simpa [inversionOP] using ⟨c, hcm, rfl⟩
    · have hwc : w ≠ c := fun h => hnc (h ▸ hw)
      rw [inversionOP_coe_of_ne hwc]
      exact ⟨_, (hB w hw).1, rfl⟩

/-- A hyperplane through the centre is mapped to itself. -/
theorem inversionOP_image_hypOP_through (hR : R ≠ 0) {n : V} {t : ℝ} (ht : t = 0) :
    inversionOP c R '' hypOP {x : P | ⟪x -ᵥ c, n⟫ = t} = hypOP {x : P | ⟪x -ᵥ c, n⟫ = t} := by
  subst ht
  have key : ∀ x : P, ⟪x -ᵥ c, n⟫ = 0 → ⟪inversion c R x -ᵥ c, n⟫ = 0 := by
    intro x hx
    rw [inversion_vsub_center, inner_smul_left, hx]; simp
  have hc' : c ∈ {x : P | ⟪x -ᵥ c, n⟫ = 0} := by simp
  refine inversionOP_image_eq_of_maps hR ?_ ?_ <;>
  · intro z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · simp only [inversionOP_infty, mem_hypOP_coe]; exact hc'
    · by_cases hxc : x = c
      · subst hxc; simp [infty_mem_hypOP]
      · rw [inversionOP_coe_of_ne hxc, mem_hypOP_coe]
        exact key x hx

/-- A hyperplane not through the centre is mapped to a circle through the centre. -/
theorem inversionOP_image_hypOP_of_ne (hR : 0 < R) {n : V} (hn : n ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    ∃ (Q : P) (s : ℝ), 0 < s ∧ dist Q c = s ∧
      inversionOP c R '' hypOP {x : P | ⟪x -ᵥ c, n⟫ = t} = circOP Q s := by
  obtain ⟨himg, hnc⟩ := image_inversion_hyperplane (c := c) hR.ne' hn ht
  set y : P := ((2 * t / ‖n‖ ^ 2) • n) +ᵥ c with hy
  have hyc : y ≠ c := by
    intro h
    have : (2 * t / ‖n‖ ^ 2) • n = 0 := by
      simpa only [hy, vadd_vsub, vsub_self] using congrArg (· -ᵥ c) h
    rcases smul_eq_zero.mp this with h0 | h0
    · exact (by positivity : 2 * t / ‖n‖ ^ 2 ≠ 0) h0
    · exact hn h0
  have hdy : 0 < dist y c := dist_pos.mpr hyc
  have hs : 0 < R ^ 2 / dist y c := by positivity
  have hdc : dist (inversion c R y) c = R ^ 2 / dist y c := dist_inversion_center c y R
  refine ⟨inversion c R y, R ^ 2 / dist y c, hs, hdc, ?_⟩
  have hcm : c ∈ sphere (inversion c R y) (R ^ 2 / dist y c) := by
    rw [Metric.mem_sphere, dist_comm]; exact hdc
  rw [Set.ext_iff] at himg
  refine inversionOP_image_eq_of_maps hR.ne' ?_ ?_
  · rintro z (rfl | ⟨x, hx, rfl⟩)
    · simpa [inversionOP] using ⟨c, hcm, rfl⟩
    · have hxc : x ≠ c := fun h => hnc (h ▸ hx)
      rw [inversionOP_coe_of_ne hxc]
      exact ⟨_, ((himg _).mp ⟨x, hx, rfl⟩).1, rfl⟩
  · rintro z ⟨w, hw, rfl⟩
    by_cases hwc : w = c
    · subst hwc; simp [infty_mem_hypOP]
    · rw [inversionOP_coe_of_ne hwc, mem_hypOP_coe]
      obtain ⟨x, hx, hxw⟩ := (himg w).mpr ⟨hw, hwc⟩
      rw [← hxw, inversion_inversion c hR.ne']
      exact hx

/-- Inversion maps generalized spheres (spheres, and hyperplanes completed by `∞`) to generalized
spheres; valid in every dimension (Petrunin Theorem 10.7 on p. 76 in the plane, Theorem 16.5(a),
(b) on p. 135 in space). -/
theorem IsInvSphere.image_inversionOP (hR : 0 < R) {S : Set (OnePoint P)} (h : IsInvSphere V S) :
    IsInvSphere V (inversionOP c R '' S) := by
  rcases h with ⟨Q, s, hs, rfl⟩ | ⟨H, hH, rfl⟩
  · by_cases hd : dist Q c = s
    · rw [inversionOP_image_circOP_through hR.ne' hs hd]
      right
      refine ⟨_, isHyperplaneSet_perpBisector c (inversion c R Q) ?_, rfl⟩
      have hQ : Q ≠ c := fun h => by rw [h, dist_self] at hd; linarith
      intro h
      exact hQ (by simpa [inversion_eq_center hR.ne'] using h.symm)
    · left
      refine ⟨_, _, ?_, inversionOP_image_circOP_of_ne hR.ne' hs hd⟩
      have := abs_pos.mpr (power_ne_zero hs.le hd)
      unfold invSphereRadius
      positivity
  · obtain ⟨n, t, hn, rfl⟩ := hH.rebase c
    by_cases ht : t = 0
    · right
      exact ⟨_, ⟨c, n, t, hn, rfl⟩, inversionOP_image_hypOP_through hR.ne' ht⟩
    · obtain ⟨Q, s, hs, -, he⟩ := inversionOP_image_hypOP_of_ne (c := c) hR hn ht
      exact Or.inl ⟨Q, s, hs, he⟩

end Basic

section Plane

variable (V : Type*) {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- A circle of the inversive plane (never contains `∞`). -/
def IsCircle (S : Set (OnePoint P)) : Prop := ∃ (Q : P) (s : ℝ), 0 < s ∧ S = circOP Q s

/-- A line of the inversive plane: an affine line together with `∞`. -/
def IsLineOP (S : Set (OnePoint P)) : Prop :=
  ∃ p q : P, p ≠ q ∧ S = hypOP ((line[ℝ, p, q] : AffineSubspace ℝ P) : Set P)

/-- A *circline* of the inversive plane (Petrunin, p. 76): a circle, or a line completed by `∞`. -/
@[kb "petrunin2025" "Definition, circlines, p. 76"]
def IsCircline (S : Set (OnePoint P)) : Prop := IsCircle S ∨ IsLineOP V S

variable {V}

/-- A circline passes through `∞` iff it is a line (Petrunin, p. 76). -/
@[kb "petrunin2025" "Definition, circlines, p. 76"]
theorem IsCircline.infty_mem_iff {S : Set (OnePoint P)} (h : IsCircline V S) :
    (∞ : OnePoint P) ∈ S ↔ IsLineOP V S := by
  rcases h with ⟨Q, s, hs, rfl⟩ | hl
  · refine ⟨fun h => absurd h (infty_notMem_circOP Q s), ?_⟩
    rintro ⟨p, q, -, h⟩
    rw [h]
    exact absurd (h ▸ infty_mem_hypOP _) (infty_notMem_circOP Q s)
  · exact ⟨fun _ => hl, fun _ => by obtain ⟨p, q, -, rfl⟩ := hl; exact infty_mem_hypOP _⟩

section TwoDim

variable [Fact (Module.finrank ℝ V = 2)]

theorem finrank_orthogonal_span_singleton' {n : V} (hn : n ≠ 0) :
    Module.finrank ℝ (ℝ ∙ n)ᗮ = 1 := by
  have : Fact (Module.finrank ℝ V = 1 + 1) := ⟨by simpa using Fact.out (p := Module.finrank ℝ V = 2)⟩
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by
    have := Fact.out (p := Module.finrank ℝ V = 2); omega)
  exact Submodule.finrank_orthogonal_span_singleton hn

theorem exists_ne_zero_inner_eq_zero {n : V} (hn : n ≠ 0) : ∃ w : V, w ≠ 0 ∧ ⟪w, n⟫ = 0 := by
  have h1 := finrank_orthogonal_span_singleton' hn
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by
    have := Fact.out (p := Module.finrank ℝ V = 2); omega)
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank ℝ (ℝ ∙ n)ᗮ)
  exact ⟨w, fun h => hw (Subtype.ext h),
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.2⟩

theorem hyperplane_eq_line {o : P} {n w : V} (hn : n ≠ 0) (hw : w ≠ 0) (hnw : ⟪w, n⟫ = 0) :
    {x : P | ⟪x -ᵥ o, n⟫ = 0} = ((line[ℝ, o, w +ᵥ o] : AffineSubspace ℝ P) : Set P) := by
  have h1 := finrank_orthogonal_span_singleton' hn
  ext x
  constructor
  · intro hx
    have hx' : x -ᵥ o ∈ (ℝ ∙ n)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hx
    have hw' : w ∈ (ℝ ∙ n)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hnw
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨w, hw'⟩ : (ℝ ∙ n)ᗮ)
      (fun h => hw (congrArg Subtype.val h))).mp h1 ⟨x -ᵥ o, hx'⟩
    have ha' : a • w = x -ᵥ o := congrArg Subtype.val ha
    have : x = AffineMap.lineMap o (w +ᵥ o) a := by
      rw [AffineMap.lineMap_apply, vadd_vsub, ha', vsub_vadd]
    rw [SetLike.mem_coe, this]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · intro hx
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hx
    obtain ⟨r, rfl⟩ := hx
    simp [AffineMap.lineMap_apply, inner_smul_left, hnw]

theorem isHyperplaneSet_line {p q : P} (hpq : p ≠ q) :
    IsHyperplaneSet V ((line[ℝ, p, q] : AffineSubspace ℝ P) : Set P) := by
  have hv : q -ᵥ p ≠ 0 := fun h => hpq (vsub_eq_zero_iff_eq.mp h).symm
  obtain ⟨n, hn, hnv⟩ := exists_ne_zero_inner_eq_zero hv
  refine ⟨p, n, 0, hn, ?_⟩
  have := hyperplane_eq_line (o := p) hn hv (by rw [real_inner_comm]; exact hnv)
  rw [vsub_vadd] at this
  exact this.symm

theorem exists_line_of_isHyperplaneSet {H : Set P} (h : IsHyperplaneSet V H) :
    ∃ p q : P, p ≠ q ∧ H = ((line[ℝ, p, q] : AffineSubspace ℝ P) : Set P) := by
  obtain ⟨o, n, t, hn, rfl⟩ := h
  set o' : P := ((t / ‖n‖ ^ 2) • n) +ᵥ o with ho'
  have hn2 : ‖n‖ ^ 2 ≠ 0 := by positivity
  have ho'n : ⟪o' -ᵥ o, n⟫ = t := by
    rw [ho', vadd_vsub, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
    field_simp
  obtain ⟨w, hw, hwn⟩ := exists_ne_zero_inner_eq_zero hn
  refine ⟨o', w +ᵥ o', fun h => hw ?_, ?_⟩
  · simpa using (congrArg (· -ᵥ o') h).symm
  · rw [← hyperplane_eq_line hn hw hwn]
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← vsub_sub_vsub_cancel_right x o' o, inner_sub_left, ho'n]
    constructor <;> intro h <;> linarith

/-- In a Euclidean plane, circlines are exactly the generalized spheres. -/
theorem isCircline_iff_isInvSphere {S : Set (OnePoint P)} : IsCircline V S ↔ IsInvSphere V S := by
  constructor
  · rintro (⟨Q, s, hs, h⟩ | ⟨p, q, hpq, h⟩)
    · exact Or.inl ⟨Q, s, hs, h⟩
    · exact Or.inr ⟨_, isHyperplaneSet_line hpq, h⟩
  · rintro (⟨Q, s, hs, h⟩ | ⟨H, hH, h⟩)
    · exact Or.inl ⟨Q, s, hs, h⟩
    · obtain ⟨p, q, hpq, rfl⟩ := exists_line_of_isHyperplaneSet hH
      exact Or.inr ⟨p, q, hpq, h⟩

/-- **Inversion maps circlines to circlines** (Petrunin, Theorem 10.7, p. 76), in the inversive
plane: the image of a circle or a line (with `∞`) under the extended inversion is again a circle or
a line (with `∞`). -/
@[kb "petrunin2025" "Theorem 10.7, p. 76"]
theorem IsCircline.image_inversionOP {c : P} {R : ℝ} (hR : 0 < R) {S : Set (OnePoint P)}
    (h : IsCircline V S) : IsCircline V (inversionOP c R '' S) :=
  isCircline_iff_isInvSphere.mpr (IsInvSphere.image_inversionOP hR (isCircline_iff_isInvSphere.mp h))

end TwoDim

end Plane

/-! ### Inversive transformations (Petrunin, p. 117) -/

section Transformations

variable (V) {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- An *inversive transformation* (Petrunin, Definition on p. 117): a bijection of the inversive
plane that maps circlines onto circlines, i.e. it and its inverse map circlines to circlines. -/
@[kb "petrunin2025" "Definition, inversive transformation, p. 117"]
def IsInversiveTransformation (f : OnePoint P ≃ OnePoint P) : Prop :=
  (∀ S : Set (OnePoint P), IsCircline V S → IsCircline V (f '' S)) ∧
    (∀ S : Set (OnePoint P), IsCircline V S → IsCircline V (f.symm '' S))

variable {V}

theorem IsInversiveTransformation.refl : IsInversiveTransformation V (Equiv.refl (OnePoint P)) :=
  ⟨fun S h => by simpa using h, fun S h => by simpa using h⟩

theorem IsInversiveTransformation.symm {f : OnePoint P ≃ OnePoint P}
    (h : IsInversiveTransformation V f) : IsInversiveTransformation V f.symm :=
  ⟨h.2, fun S hS => by simpa using h.1 S hS⟩

/-- Inversive transformations are closed under composition (Petrunin, p. 117). -/
@[kb "petrunin2025" "Definition, inversive transformation, p. 117"]
theorem IsInversiveTransformation.trans {f g : OnePoint P ≃ OnePoint P}
    (hf : IsInversiveTransformation V f) (hg : IsInversiveTransformation V g) :
    IsInversiveTransformation V (f.trans g) := by
  constructor
  · intro S hS
    have := hg.1 _ (hf.1 S hS)
    rwa [Set.image_image] at this
  · intro S hS
    have := hf.2 _ (hg.2 S hS)
    rwa [Set.image_image] at this

/-- The extended inversion is an inversive transformation (Petrunin, p. 117; this is Theorem 10.7
on p. 76 together with the fact that the inversion is an involution). -/
@[kb "petrunin2025" "Definition, inversive transformation, p. 117"]
theorem isInversiveTransformation_inversionEquiv [Fact (Module.finrank ℝ V = 2)] {c : P} {R : ℝ}
    (hR : 0 < R) : IsInversiveTransformation V (inversionEquiv c R hR.ne') := by
  have h1 : ∀ S : Set (OnePoint P), IsCircline V S →
      IsCircline V (inversionEquiv c R hR.ne' '' S) := fun S h => h.image_inversionOP hR
  refine ⟨h1, fun S h => ?_⟩
  have : (inversionEquiv c R hR.ne').symm = inversionEquiv c R hR.ne' := rfl
  rw [this]
  exact h1 S h

/-- The extension to the inversive plane (fixing `∞`) of a map of the plane. -/
def extendOP (e : P → P) (z : OnePoint P) : OnePoint P :=
  z.elim ∞ (fun x => (e x : OnePoint P))

theorem extendOP_image_coe (e : P → P) (A : Set P) :
    extendOP e '' ((fun x : P => (x : OnePoint P)) '' A) = (fun x : P => (x : OnePoint P)) '' (e '' A) := by
  rw [Set.image_image, Set.image_image]; rfl

theorem extendOP_image_hypOP (e : P → P) (A : Set P) :
    extendOP e '' hypOP A = hypOP (e '' A) := by
  unfold hypOP
  rw [Set.image_insert_eq, extendOP_image_coe]; rfl

theorem extendOP_image_circOP (e : P ≃ᵃⁱ[ℝ] P) (Q : P) (s : ℝ) :
    extendOP e '' circOP Q s = circOP (e Q) s := by
  unfold circOP
  rw [extendOP_image_coe]
  congr 1
  exact e.toIsometryEquiv.image_sphere Q s

/-- The extension of an affine isometry of the plane (e.g. a reflection) to the inversive plane
maps circlines to circlines. -/
theorem IsCircline.image_extendOP (e : P ≃ᵃⁱ[ℝ] P) {S : Set (OnePoint P)} (h : IsCircline V S) :
    IsCircline V (extendOP e '' S) := by
  rcases h with ⟨Q, s, hs, rfl⟩ | ⟨p, q, hpq, rfl⟩
  · exact Or.inl ⟨e Q, s, hs, extendOP_image_circOP e Q s⟩
  · refine Or.inr ⟨e p, e q, fun h => hpq (e.injective h), ?_⟩
    rw [extendOP_image_hypOP]
    congr 1
    rw [show (⇑e : P → P) = ⇑(e.toAffineEquiv.toAffineMap) from rfl,
      ← AffineSubspace.coe_map, AffineSubspace.map_span, Set.image_pair]

/-- The extension of an affine isometry of the plane, as a bijection of the inversive plane. -/
noncomputable def extendEquiv (e : P ≃ᵃⁱ[ℝ] P) : OnePoint P ≃ OnePoint P where
  toFun := extendOP e
  invFun := extendOP e.symm
  left_inv z := by induction z using OnePoint.rec <;> simp [extendOP]
  right_inv z := by induction z using OnePoint.rec <;> simp [extendOP]

/-- Isometries of the plane (in particular reflections `EuclideanGeometry.reflection`), extended by
`∞ ↦ ∞`, are inversive transformations (Petrunin, p. 117). -/
@[kb "petrunin2025" "Definition, inversive transformation, p. 117"]
theorem isInversiveTransformation_extendEquiv (e : P ≃ᵃⁱ[ℝ] P) :
    IsInversiveTransformation V (extendEquiv e) :=
  ⟨fun _ h => h.image_extendOP e, fun _ h => h.image_extendOP e.symm⟩

end Transformations

/-! ### Corollary 10.26, the case of a circle through the centre -/

section Cor1026

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The reflection in the perpendicular bisector of `[a b]`, in vector form relative to `a`. -/
theorem reflection_perpBisector_vsub (a b x : P) (hab : a ≠ b) :
    EuclideanGeometry.reflection (AffineSubspace.perpBisector a b) x -ᵥ a =
      (x -ᵥ a) - (2 * ⟪b -ᵥ a, x -ᵥ a⟫ / ‖b -ᵥ a‖ ^ 2 - 1) • (b -ᵥ a) := by
  have hu : b -ᵥ a ≠ 0 := fun h => hab (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖b -ᵥ a‖ ^ 2 ≠ 0 := by positivity
  rw [EuclideanGeometry.reflection_apply_of_mem _ _ (AffineSubspace.midpoint_mem_perpBisector a b)]
  simp_rw [AffineSubspace.direction_perpBisector]
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, vadd_vsub_assoc]
  have h2 : midpoint ℝ a b -ᵥ a = (1 / 2 : ℝ) • (b -ᵥ a) := by
    rw [midpoint_vsub_left]; simp
  have h1 : x -ᵥ midpoint ℝ a b = (x -ᵥ a) - (1 / 2 : ℝ) • (b -ᵥ a) := by
    rw [← vsub_sub_vsub_cancel_right x (midpoint ℝ a b) a, h2]
  rw [h1, h2, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [RCLike.ofReal_real_eq_id, id, nsmul_eq_mul, Nat.cast_ofNat]
  match_scalars <;> field_simp <;> ring

/-- **Petrunin, Corollary 10.26, case of a circle `Γ` through the centre `O` of the inversion across
`Ω`** (the other case is `inversion_inversion_conj`): let `Γ` have centre `S` and radius `s > 0`
with `O ∈ Γ`; the image of `Γ` under the inversion across `Ω` (centre `O`, radius `R`) is the line
`ℓ = perpBisector O (inversion O R S)` (see `inversionOP_image_circOP_through`). If `Q` is the inverse
of `Pt` across `Γ`, then the inverse `Q'` of `Q` across `Ω` is the mirror image of the inverse `P'` of
`Pt` in the line `ℓ`. (The hypotheses `Pt ≠ O`, `Pt ≠ S` exclude the `∞`-cases (here `Q ≠ O` is automatic).) -/
@[kb "petrunin2025" "Corollary 10.26, p. 82"]
theorem reflection_inversion_through {O S Pt : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s)
    (hd : dist S O = s) (hP : Pt ≠ O) (hPS : Pt ≠ S) :
    EuclideanGeometry.reflection (AffineSubspace.perpBisector O (inversion O R S))
        (inversion O R Pt) = inversion O R (inversion S s Pt) := by
  have hSO : S ≠ O := fun h => by rw [h, dist_self] at hd; linarith
  have hyO : O ≠ inversion O R S := fun h => hSO (by simpa [inversion_eq_center hR] using h.symm)
  set p : V := Pt -ᵥ O with hp
  set σ : V := S -ᵥ O with hσ
  have hpS : Pt -ᵥ S = p - σ := (vsub_sub_vsub_cancel_right Pt S O).symm
  have hdP : dist Pt O = ‖p‖ := dist_eq_norm_vsub V _ _
  have hdS0 : dist S O = ‖σ‖ := dist_eq_norm_vsub V _ _
  have hdPS : dist Pt S = ‖p - σ‖ := by rw [dist_eq_norm_vsub V, hpS]
  have hpn : ‖p‖ ≠ 0 := by rw [← hdP]; exact dist_ne_zero.mpr hP
  have hpSn : ‖p - σ‖ ≠ 0 := by rw [← hdPS]; exact dist_ne_zero.mpr hPS
  have hsn : ‖σ‖ ≠ 0 := by rw [← hdS0]; exact dist_ne_zero.mpr hSO
  set a := ‖p‖ ^ 2 with ha
  set b := ‖σ‖ ^ 2 with hb
  set ip := ⟪p, σ⟫ with hip
  set m := ‖p - σ‖ ^ 2 with hm
  have hmab : m = a - 2 * ip + b := norm_sub_sq_real p σ
  have hip' : ip = (a + b - m) / 2 := by rw [hmab]; ring
  have ha0 : a ≠ 0 := pow_ne_zero 2 hpn
  have hm0 : m ≠ 0 := pow_ne_zero 2 hpSn
  have hb0 : b ≠ 0 := pow_ne_zero 2 hsn
  have hbs : b = s ^ 2 := by rw [hb, ← hdS0, hd]
  set k : ℝ := b / m with hk
  have hQvec : inversion S s Pt -ᵥ O = k • p + (1 - k) • σ := by
    rw [← vsub_add_vsub_cancel (inversion S s Pt) S O, inversion_vsub_center, hpS, hdPS, div_pow,
      ← hm, ← hbs]
    simp only [hk]
    module
  have hdQ : dist (inversion S s Pt) O ^ 2 =
      k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b := by
    rw [dist_eq_norm_vsub V, hQvec, norm_sq_smul_add_smul, ← hip']
  have hN : k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b = b * a / m := by
    rw [hk]; field_simp; ring
  have hL : inversion O R (inversion S s Pt) -ᵥ O =
      (R ^ 2 / (b * a / m)) • (k • p + (1 - k) • σ) := by
    rw [inversion_vsub_center, div_pow, hdQ, hN, hQvec]
  have hP'vec : inversion O R Pt -ᵥ O = (R ^ 2 / a) • p := by
    rw [inversion_vsub_center, hdP, div_pow]
  have hy : inversion O R S -ᵥ O = (R ^ 2 / b) • σ := by
    rw [inversion_vsub_center, hdS0, div_pow]
  have hY2 : ‖(R ^ 2 / b) • σ‖ ^ 2 = (R ^ 2 / b) ^ 2 * b := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hYP : ⟪(R ^ 2 / b) • σ, (R ^ 2 / a) • p⟫ = (R ^ 2 / b) * (R ^ 2 / a) * ip := by
    rw [real_inner_smul_left, real_inner_smul_right, hip, real_inner_comm]; ring
  apply vsub_left_cancel (p := O)
  rw [reflection_perpBisector_vsub O _ _ hyO, hP'vec, hy, hL, hY2, hYP, hip', hk]
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  match_scalars <;> field_simp <;> ring

end Cor1026

/-! ### Theorem 10.25: angles after inversion (analytic form) -/

section Angles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {c x : V} {R : ℝ}

theorem fderiv_inversion_apply (v : V) :
    fderiv ℝ (inversion c R) x v =
      (R / dist x c) ^ 2 • (ℝ ∙ (x - c))ᗮ.reflection v := by
  rw [fderiv_inversion]; rfl

theorem fderiv_inversion_pos (hx : x ≠ c) (hR : R ≠ 0) : 0 < (R / dist x c) ^ 2 := by
  have : 0 < dist x c := dist_pos.mpr hx
  positivity

theorem hasDerivAt_inversion_comp {γ : ℝ → V} {t : ℝ} {v : V} (hXc : γ t ≠ c)
    (h : HasDerivAt γ v t) :
    HasDerivAt (fun t => inversion c R (γ t)) (fderiv ℝ (inversion c R) (γ t) v) t := by
  have := (hasFDerivAt_inversion (R := R) hXc).comp_hasDerivAt t h
  rw [(hasFDerivAt_inversion (R := R) hXc).fderiv]
  exact this

/-- The differential of the inversion at `x ≠ c` preserves the unoriented angle between vectors. -/
theorem angle_fderiv_inversion (hx : x ≠ c) (hR : R ≠ 0) (v w : V) :
    InnerProductGeometry.angle (fderiv ℝ (inversion c R) x v) (fderiv ℝ (inversion c R) x w) = InnerProductGeometry.angle v w := by
  rw [fderiv_inversion_apply, fderiv_inversion_apply, InnerProductGeometry.angle_smul_left_of_pos _ _ (fderiv_inversion_pos hx hR),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (fderiv_inversion_pos hx hR)]
  exact (ℝ ∙ (x - c))ᗮ.reflection.toLinearIsometry.angle_map v w

theorem fderiv_inversion_ne_zero (hx : x ≠ c) (hR : R ≠ 0) {v : V} (hv : v ≠ 0) :
    fderiv ℝ (inversion c R) x v ≠ 0 := by
  rw [fderiv_inversion_apply]
  exact smul_ne_zero (fderiv_inversion_pos hx hR).ne' (by simpa using hv)

/-- **Petrunin, Theorem 10.25, unsigned analytic form** (any dimension; also Theorem 16.5(e)
on p. 135): let `γ₁`, `γ₂` be differentiable curves through the same point `X ≠ c` with nonzero
velocities `v₁`, `v₂`. The inverted curves `inversion c R ∘ γᵢ` are differentiable with the nonzero
velocities `D vᵢ`, where `D` is the differential of the inversion at `X`, and the angle between the
velocities of the inverted curves equals the angle between the velocities `v₁`, `v₂`. -/
@[kb "petrunin2025" "Theorem 10.25, p. 81"]
theorem angle_inversion_curves {γ₁ γ₂ : ℝ → V} {t₁ t₂ : ℝ} {v₁ v₂ : V} (hR : R ≠ 0)
    (h₁ : HasDerivAt γ₁ v₁ t₁) (h₂ : HasDerivAt γ₂ v₂ t₂) (hX : γ₁ t₁ = γ₂ t₂)
    (hXc : γ₁ t₁ ≠ c) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    HasDerivAt (fun t => inversion c R (γ₁ t)) (fderiv ℝ (inversion c R) (γ₁ t₁) v₁) t₁ ∧
    HasDerivAt (fun t => inversion c R (γ₂ t)) (fderiv ℝ (inversion c R) (γ₁ t₁) v₂) t₂ ∧
    fderiv ℝ (inversion c R) (γ₁ t₁) v₁ ≠ 0 ∧ fderiv ℝ (inversion c R) (γ₁ t₁) v₂ ≠ 0 ∧
    InnerProductGeometry.angle (fderiv ℝ (inversion c R) (γ₁ t₁) v₁) (fderiv ℝ (inversion c R) (γ₁ t₁) v₂) =
      InnerProductGeometry.angle v₁ v₂ := by
  have hXc₂ : γ₂ t₂ ≠ c := hX ▸ hXc
  refine ⟨?_, ?_, fderiv_inversion_ne_zero hXc hR hv₁, fderiv_inversion_ne_zero hXc hR hv₂,
    angle_fderiv_inversion hXc hR v₁ v₂⟩
  · exact hasDerivAt_inversion_comp hXc h₁
  · rw [hX]
    exact hasDerivAt_inversion_comp hXc₂ h₂

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- The differential of the inversion at `x ≠ c` reverses the oriented angle between vectors. -/
theorem oangle_fderiv_inversion (hx : x ≠ c) (hR : R ≠ 0) (v w : V) :
    o.oangle (fderiv ℝ (inversion c R) x v) (fderiv ℝ (inversion c R) x w) = -o.oangle v w := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by
    have := Fact.out (p := Module.finrank ℝ V = 2); omega)
  set K : Submodule ℝ V := (ℝ ∙ (x - c))ᗮ with hK
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr hx
  have hrank : Module.finrank ℝ Kᗮ = 1 := by
    rw [hK, Submodule.orthogonal_orthogonal]
    exact finrank_span_singleton hxc
  have hdet : LinearMap.det K.reflection.toLinearMap < 0 := by
    rw [Submodule.det_reflection, hrank]; norm_num
  have hmap : Orientation.map (Fin 2) K.reflection.toLinearEquiv o = -o :=
    (Orientation.map_eq_neg_iff_det_neg o _ (by simp [Fact.out (p := Module.finrank ℝ V = 2)])).mpr hdet
  rw [fderiv_inversion_apply, fderiv_inversion_apply, Orientation.oangle_smul_left_of_pos _ _ _ (fderiv_inversion_pos hx hR),
    Orientation.oangle_smul_right_of_pos _ _ _ (fderiv_inversion_pos hx hR)]
  have h := Orientation.oangle_map (o := o) (K.reflection v) (K.reflection w) K.reflection
  rw [hmap, Orientation.oangle_neg_orientation_eq_neg] at h
  simp only [LinearIsometryEquiv.symm_apply_apply] at h
  exact neg_eq_iff_eq_neg.mp h

/-- **Petrunin, Theorem 10.25, oriented form**: in an oriented Euclidean plane the oriented angle
between the velocities of the inverted curves is the negative of the oriented angle between the
velocities of the original curves (`∡X₁AX₂ ≡ -∡Y₁A'Y₂`). -/
@[kb "petrunin2025" "Theorem 10.25, p. 81"]
theorem oangle_inversion_curves {γ₁ γ₂ : ℝ → V} {t₁ t₂ : ℝ} {v₁ v₂ : V} (hR : R ≠ 0)
    (h₁ : HasDerivAt γ₁ v₁ t₁) (h₂ : HasDerivAt γ₂ v₂ t₂) (hX : γ₁ t₁ = γ₂ t₂)
    (hXc : γ₁ t₁ ≠ c) :
    HasDerivAt (fun t => inversion c R (γ₁ t)) (fderiv ℝ (inversion c R) (γ₁ t₁) v₁) t₁ ∧
    HasDerivAt (fun t => inversion c R (γ₂ t)) (fderiv ℝ (inversion c R) (γ₁ t₁) v₂) t₂ ∧
    o.oangle (fderiv ℝ (inversion c R) (γ₁ t₁) v₁) (fderiv ℝ (inversion c R) (γ₁ t₁) v₂) =
      -o.oangle v₁ v₂ := by
  have hXc₂ : γ₂ t₂ ≠ c := hX ▸ hXc
  refine ⟨?_, ?_, oangle_fderiv_inversion o hXc hR v₁ v₂⟩
  · exact hasDerivAt_inversion_comp hXc h₁
  · rw [hX]
    exact hasDerivAt_inversion_comp hXc₂ h₂

end Oriented

end Angles

/-! ### Proposition 10.24: arcs -/

section ArcsSection

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- The arc `ABC` of the circline through the distinct points `A, B, C` of an oriented Euclidean
plane, described by the oriented-angle criterion of Petrunin's Proposition 9.23 (p. 71): the
endpoints `A`, `C`, and the points `X` with `∡AXC = ∡ABC`. For a circle this is the set of points
of the circle on the same side of `(AC)` as `B` plus the endpoints (`mem_arcOrient_iff_of_sphere`);
for `B` strictly between `A` and `C` it is the segment `[AC]` (`arcOrient_eq_of_sbtw`); in
the remaining collinear case it is the part of the line outside the open segment (which in the
inversive plane contains `∞`). -/
@[kb "petrunin2025" "Proposition 9.23 / arcs, p. 71, 81"]
def arcOrient (A B C : P) : Set P := {X | X = A ∨ X = C ∨ ∡ A X C = ∡ A B C}

/-- On a circle, the arc `ABC` is the set of points on the same side of `(AC)` as `B` (and the
endpoints). -/
theorem mem_arcOrient_iff_of_sphere {s : Sphere P} {A B C X : P} (hA : A ∈ s) (hB : B ∈ s)
    (hC : C ∈ s) (hAC : A ≠ C) (hBA : B ≠ A) (hBC : B ≠ C) :
    X ∈ arcOrient A B C ↔ X = A ∨ X = C ∨ (X ∈ s ∧ line[ℝ, A, C].SSameSide X B) := by
  by_cases hXA : X = A
  · simp [arcOrient, hXA]
  by_cases hXC : X = C
  · simp [arcOrient, hXC]
  simp only [arcOrient, Set.mem_ofPred_eq, hXA, hXC, false_or]
  exact oangle_eq_iff_mem_arc hA hB hC hAC hBA hBC hXA hXC

/-- If `B` lies strictly between `A` and `C`, the arc `ABC` is the segment `[AC]`. -/
theorem arcOrient_eq_of_sbtw {A B C : P} (h : Sbtw ℝ A B C) :
    arcOrient A B C = {X | Wbtw ℝ A X C} := by
  have hB : ∡ A B C = (Real.pi : Real.Angle) := oangle_eq_pi_iff_sbtw.mpr h
  ext X
  simp only [arcOrient, Set.mem_ofPred_eq, hB]
  by_cases hXA : X = A
  · subst hXA; simp [wbtw_self_left]
  by_cases hXC : X = C
  · subst hXC; simp [wbtw_self_right]
  simp only [hXA, hXC, false_or]
  rw [oangle_eq_pi_iff_sbtw]
  exact ⟨fun h => h.wbtw, fun h => ⟨h, hXA, hXC⟩⟩

/-- **Petrunin, Proposition 10.24** (the inverse of an arc is an arc; case of arcs whose three
defining points differ from the centre `O` of the inversion, and a test point `D ≠ O`):
`D` lies on the arc `ABC` iff its inverse lies on the arc `A'B'C'` of the inverted points. -/
@[kb "petrunin2025" "Proposition 10.24, p. 81"]
theorem mem_arcOrient_inversion_iff {O A B C D : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hD : D ≠ O) (hAB : A ≠ B) (hBC : B ≠ C) :
    D ∈ arcOrient A B C ↔
      inversion O R D ∈ arcOrient (inversion O R A) (inversion O R B) (inversion O R C) := by
  have inj : ∀ X Y : P, X ≠ Y → inversion O R X ≠ inversion O R Y := fun X Y h h' =>
    h (by simpa [inversion_inversion O hR] using congrArg (inversion O R) h')
  have injiff : ∀ X Y : P, inversion O R X = inversion O R Y ↔ X = Y := fun X Y =>
    ⟨fun h => by simpa [inversion_inversion O hR] using congrArg (inversion O R) h, fun h => h ▸ rfl⟩
  by_cases hDA : D = A
  · subst hDA; simp [arcOrient]
  by_cases hDC : D = C
  · subst hDC; simp [arcOrient]
  simp only [arcOrient, Set.mem_ofPred_eq, hDA, hDC, false_or, injiff]
  have h := oangle_add_oangle_inversion hR hA hB hC hD hAB hBC (Ne.symm hDC) hDA
  rw [oangle_rev A D C, oangle_rev (inversion O R A) (inversion O R D) (inversion O R C)] at h
  have h2 : (∡ A B C - ∡ A D C) =
      -(∡ (inversion O R A) (inversion O R B) (inversion O R C) -
        ∡ (inversion O R A) (inversion O R D) (inversion O R C)) := by
    linear_combination (norm := abel) h
  constructor
  · intro e
    have h0 : ∡ A B C - ∡ A D C = 0 := by rw [e, sub_self]
    rw [h0] at h2
    exact (sub_eq_zero.mp (neg_eq_zero.mp h2.symm)).symm
  · intro e
    have h0 : ∡ (inversion O R A) (inversion O R B) (inversion O R C) -
        ∡ (inversion O R A) (inversion O R D) (inversion O R C) = 0 := by rw [e, sub_self]
    rw [h0, neg_zero, sub_eq_zero] at h2
    exact h2.symm

/-- Proposition 10.24, set form: the inversion maps the arc `ABC` (minus the centre `O`) onto the arc
`A'B'C'` (minus the centre). -/
@[kb "petrunin2025" "Proposition 10.24, p. 81"]
theorem image_inversion_arcOrient {O A B C : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hAB : A ≠ B) (hBC : B ≠ C) :
    inversion O R '' (arcOrient A B C \ {O}) =
      arcOrient (inversion O R A) (inversion O R B) (inversion O R C) \ {O} := by
  ext y
  constructor
  · rintro ⟨D, ⟨hD, hDO⟩, rfl⟩
    refine ⟨(mem_arcOrient_inversion_iff hR hA hB hC hDO hAB hBC).mp hD, ?_⟩
    simpa [inversion_eq_center hR] using hDO
  · rintro ⟨hy, hyO⟩
    have hDO : inversion O R y ≠ O := by simpa [inversion_eq_center hR] using hyO
    refine ⟨inversion O R y, ⟨?_, hDO⟩, inversion_inversion O hR y⟩
    rw [mem_arcOrient_inversion_iff hR hA hB hC hDO hAB hBC, inversion_inversion O hR y]
    exact hy

end ArcsSection

/-! ### Inversion in space (Petrunin, chapter 16 E) -/

section Space

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (V) in
/-- A *circline* of the inversive space: the intersection of two distinct generalized spheres
(spheres, or planes completed by `∞`) containing at least three points. In 3-space these are exactly
the circles and the lines (completed by `∞`), as a circle is the intersection of two spheres
(Petrunin, Observation 16.10, p. 136); the intersection of a sphere and a plane is of this form
(`isInvCircline_circOP_inter_hypOP`). -/
def IsInvCircline (S : Set (OnePoint V)) : Prop :=
  (∃ G₁ G₂ : Set (OnePoint V), IsInvSphere V G₁ ∧ IsInvSphere V G₂ ∧ G₁ ≠ G₂ ∧ S = G₁ ∩ G₂) ∧
    3 ≤ S.encard

theorem isInvCircline_circOP_inter_hypOP {Q : V} {s : ℝ} (hs : 0 < s) {H : Set V}
    (hH : IsHyperplaneSet V H) (h3 : 3 ≤ (circOP Q s ∩ hypOP H).encard) :
    IsInvCircline V (circOP Q s ∩ hypOP H) :=
  ⟨⟨circOP Q s, hypOP H, Or.inl ⟨Q, s, hs, rfl⟩, Or.inr ⟨H, hH, rfl⟩, fun h =>
    infty_notMem_circOP Q s (h ▸ infty_mem_hypOP H), rfl⟩, h3⟩

theorem IsInvCircline.image_inversionOP {c : V} {R : ℝ} (hR : 0 < R) {S : Set (OnePoint V)}
    (h : IsInvCircline V S) : IsInvCircline V (inversionOP c R '' S) := by
  obtain ⟨⟨G₁, G₂, h₁, h₂, hne, rfl⟩, h3⟩ := h
  have hinj : Function.Injective (inversionOP c R) := (inversionOP_bijective hR.ne').1
  refine ⟨⟨inversionOP c R '' G₁, inversionOP c R '' G₂, h₁.image_inversionOP hR, h₂.image_inversionOP hR, fun h => hne ?_, ?_⟩, ?_⟩
  · exact (Set.image_injective.mpr hinj) h
  · exact Set.image_inter hinj
  · rwa [hinj.encard_image]

/-- The inversion across a sphere in `V` (for `V` three-dimensional: Petrunin, p. 135) extended to the
inversive space `V ∪ {∞}`: this is `inversionOP`, which is defined in every dimension. -/
@[kb "petrunin2025" "Definition, inversion across a sphere, p. 135"]
noncomputable abbrev inversionSpace (c : V) (R : ℝ) : OnePoint V → OnePoint V := inversionOP c R

/-- **Petrunin, Theorem 16.5** (inversion across a sphere, in any real inner product space `V`,
radius `R > 0`, centre `c`), parts (a), (b), (c), (e):
(a) the inversion maps spheres and planes (completed by `∞`) to spheres and planes;
(b) it maps circlines to circlines;
(c) it preserves the cross-ratio of four points different from the centre;
(e) it preserves the (unsigned) angle between the velocity vectors of two curves through a common
point `X ≠ c`, i.e. between tangent half-lines. Part (d) (arcs in space) is not formalized; for the
plane see `mem_arcOrient_inversion_iff`. -/
@[kb "petrunin2025" "Theorem 16.5, p. 135"]
theorem inversionSpace_theorem {c : V} {R : ℝ} (hR : 0 < R) :
    (∀ S : Set (OnePoint V), IsInvSphere V S → IsInvSphere V (inversionSpace c R '' S)) ∧
    (∀ S : Set (OnePoint V), IsInvCircline V S → IsInvCircline V (inversionSpace c R '' S)) ∧
    (∀ A B C D : V, A ≠ c → B ≠ c → C ≠ c → D ≠ c →
      crossRatio (inversion c R A) (inversion c R B) (inversion c R C) (inversion c R D) =
        crossRatio A B C D) ∧
    (∀ (γ₁ γ₂ : ℝ → V) (t₁ t₂ : ℝ) (v₁ v₂ : V), HasDerivAt γ₁ v₁ t₁ → HasDerivAt γ₂ v₂ t₂ →
      γ₁ t₁ = γ₂ t₂ → γ₁ t₁ ≠ c → v₁ ≠ 0 → v₂ ≠ 0 →
      ∃ w₁ w₂ : V, HasDerivAt (fun t => inversion c R (γ₁ t)) w₁ t₁ ∧
        HasDerivAt (fun t => inversion c R (γ₂ t)) w₂ t₂ ∧ w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
        InnerProductGeometry.angle w₁ w₂ = InnerProductGeometry.angle v₁ v₂) :=
  ⟨fun _ h => h.image_inversionOP hR, fun _ h => h.image_inversionOP hR,
    fun _ _ _ _ hA hB hC hD => crossRatio_inversion hR.ne' hA hB hC hD,
    fun γ₁ γ₂ t₁ t₂ v₁ v₂ h₁ h₂ hX hXc hv₁ hv₂ => by
      obtain ⟨a, b, c', d, e⟩ := angle_inversion_curves hR.ne' h₁ h₂ hX hXc hv₁ hv₂
      exact ⟨_, _, a, b, c', d, e⟩⟩

end Space

end UndergradKB.Geometry
