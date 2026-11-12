import Mathlib.Geometry.Euclidean.Sphere.PolePolar
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import UndergradKB.Common.Attr
import UndergradKB.Geometry.ProjectivePlane2

/-! # The polar and the pole: footpoint and duality (Petrunin, Section 15H, Claim 15.17)

`ProjectivePlane2.lean` proves that the line `ZZ'` of the secant construction is the polar line (independent
of the secants).  Here we prove the remaining parts of Claim 15.17 and the exercises around it:

* (b) the polar of `P` is the line perpendicular to `OP` through the inverse `P'` of `P` across the circle,
  and `P'` is the footpoint of the center `O` on it (Euclidean form, for Mathlib's `Sphere.polar`);
* (a) the correspondence `P ↦ p` is a duality of the projective plane (a bijection points `→` lines
  preserving incidence, La Hire's theorem), the center corresponds to the ideal line, ideal points to lines
  through the center, and points of the circle to the tangent lines.
-/

namespace UndergradKB.Geometry

open Module
open scoped RealInnerProductSpace

/-! ## (b) The footpoint of the center on the polar is the inverse -/

section Footpoint

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- **The polar is the perpendicular to `OP` through the inverse of `P`, and the inverse is the footpoint of
the center on it** (Petrunin, Claim 15.17(b), p. 130).  For a circle `s` of positive radius and a point `A`
different from the center: the inverse `A'` of `A` across `s` lies on the polar of `A`; a point `x` lies on
the polar iff `x - A'` is perpendicular to `A - O`; and the orthogonal projection of the center `O` onto the
polar is `A'`.  (The hypothesis `A ∉ s` of the book is not needed.) -/
@[kb "petrunin2025" "Claim 15.17(b), p. 130"]
theorem polar_perp_through_inversion {s : EuclideanGeometry.Sphere P} (hs : 0 < s.radius) {A : P}
    (hA : A ≠ s.center) :
    EuclideanGeometry.inversion s.center s.radius A ∈ s.polar A ∧
    (∀ x : P, x ∈ s.polar A ↔
      ⟪x -ᵥ EuclideanGeometry.inversion s.center s.radius A, A -ᵥ s.center⟫ = 0) ∧
    ((EuclideanGeometry.orthogonalProjection (s.polar A) s.center : P) =
      EuclideanGeometry.inversion s.center s.radius A) := by
  refine ⟨EuclideanGeometry.Sphere.self_mem_orthRadius _ _, fun x => ?_, ?_⟩
  · unfold EuclideanGeometry.Sphere.polar
    rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, EuclideanGeometry.inversion_vsub_center,
      real_inner_smul_right, mul_eq_zero]
    have : (s.radius / dist A s.center) ^ 2 ≠ 0 := by
      have := dist_pos.2 hA
      positivity
    exact ⟨fun h => h.resolve_left this, Or.inr⟩
  · unfold EuclideanGeometry.Sphere.polar
    have := EuclideanGeometry.Sphere.orthogonalProjection_orthRadius_center s
      (EuclideanGeometry.inversion s.center s.radius A)
    rw [this]

/-- The line `OA` is perpendicular to the polar of `A`: the direction of the polar is the orthogonal
complement of the span of `A - O`. -/
theorem direction_polar_eq {s : EuclideanGeometry.Sphere P} (hs : 0 < s.radius) (A : P) :
    (s.polar A).direction = (ℝ ∙ (A -ᵥ s.center))ᗮ :=
  EuclideanGeometry.Sphere.direction_polar hs.ne' A

end Footpoint

/-! ## (a) The polar correspondence is a duality of the projective plane -/

section Duality

/-- The inverse of `polarNormal`: the point whose polar has the given normal. -/
noncomputable def poleVec (c0 c1 r : ℝ) (n : Space3) : Space3 :=
  !₂[n 0 - c0 * (n 2 + c0 * n 0 + c1 * n 1) / r ^ 2, n 1 - c1 * (n 2 + c0 * n 0 + c1 * n 1) / r ^ 2,
    -(n 2 + c0 * n 0 + c1 * n 1) / r ^ 2]

theorem polarNormal_poleVec {c0 c1 r : ℝ} (hr : r ≠ 0) (n : Space3) :
    polarNormal c0 c1 r (poleVec c0 c1 r n) = n := by
  ext i
  fin_cases i <;> simp [polarNormal, poleVec] <;> field_simp <;> ring

theorem poleVec_polarNormal {c0 c1 r : ℝ} (hr : r ≠ 0) (p : Space3) :
    poleVec c0 c1 r (polarNormal c0 c1 r p) = p := by
  ext i
  fin_cases i <;> simp [polarNormal, poleVec] <;> field_simp <;> ring

theorem polarNormal_smul (c0 c1 r t : ℝ) (p : Space3) :
    polarNormal c0 c1 r (t • p) = t • polarNormal c0 c1 r p := by
  ext i
  fin_cases i <;> simp [polarNormal] <;> ring

theorem lineOfNormal_eq_iff {n n' : Space3} (hn : n ≠ 0) (hn' : n' ≠ 0) :
    lineOfNormal n hn = lineOfNormal n' hn' ↔ ∃ t : ℝ, t • n = n' := by
  unfold lineOfNormal
  rw [← ProjPoint.mk'_eq_iff hn hn']
  exact projDuality.injective.eq_iff

theorem circlePolar_mk' (c0 c1 r : ℝ) (hr : r ≠ 0) {q : Space3} (hq : q ≠ 0) :
    (ProjPoint.mk' q hq).circlePolar c0 c1 r hr = lineOfNormal (polarNormal c0 c1 r q) (polarNormal_ne_zero hr hq) := by
  unfold ProjPoint.circlePolar
  obtain ⟨t, ht⟩ := (ProjPoint.mk'_eq_iff _ _).1
    (ProjPoint.exists_rep (ProjPoint.mk' q hq)).choose_spec.choose_spec.symm
  rw [lineOfNormal_eq_iff]
  exact ⟨t, (polarNormal_smul c0 c1 r t _).symm.trans (congrArg (polarNormal c0 c1 r) ht)⟩

/-- **The polar correspondence `P ↦ p` is a duality of the projective plane** (Petrunin, Claim 15.17(a),
p. 130): the circle with center `(c₀, c₁)` and radius `r ≠ 0` induces a bijection from the points to the
lines of the projective plane. -/
theorem circlePolar_bijective (c0 c1 r : ℝ) (hr : r ≠ 0) :
    Function.Bijective (fun P : ProjPoint => P.circlePolar c0 c1 r hr) := by
  constructor
  · intro P Q h
    obtain ⟨p, hp, rfl⟩ := P.exists_rep
    obtain ⟨q, hq, rfl⟩ := Q.exists_rep
    simp only [circlePolar_mk'] at h
    obtain ⟨t, ht⟩ := (lineOfNormal_eq_iff _ _).1 h
    rw [← polarNormal_smul] at ht
    have := congrArg (poleVec c0 c1 r) ht
    rw [poleVec_polarNormal hr, poleVec_polarNormal hr] at this
    exact (ProjPoint.mk'_eq_iff _ _).2 ⟨t, this⟩
  · intro ℓ
    obtain ⟨n, hn, rfl⟩ := ℓ.exists_normal
    have hq : poleVec c0 c1 r n ≠ 0 := by
      intro h
      apply hn
      rw [← polarNormal_poleVec hr n, h]
      ext i
      fin_cases i <;> simp [polarNormal]
    refine ⟨ProjPoint.mk' _ hq, ?_⟩
    simp only [circlePolar_mk']
    rw [lineOfNormal_eq_iff]
    exact ⟨1, by rw [one_smul, polarNormal_poleVec hr]⟩

/-- **La Hire's theorem for the projective polar**: `Q` lies on the polar of `P` iff `P` lies on the polar
of `Q`. -/
theorem liesOn_circlePolar_iff_symm (c0 c1 r : ℝ) (hr : r ≠ 0) (P Q : ProjPoint) :
    Q.LiesOn (P.circlePolar c0 c1 r hr) ↔ P.LiesOn (Q.circlePolar c0 c1 r hr) := by
  rw [ProjPoint.liesOn_circlePolar_iff, ProjPoint.liesOn_circlePolar_iff]
  constructor <;> intro h a ha b hb <;> rw [circleBil_symm] <;> exact h b hb a ha

/-- The duality of the projective plane given by the polar with respect to the circle (a bijection
points `≃` lines). -/
noncomputable def circlePolarEquiv (c0 c1 r : ℝ) (hr : r ≠ 0) : ProjPoint ≃ ProjLine :=
  Equiv.ofBijective _ (circlePolar_bijective c0 c1 r hr)

/-- **The polar with respect to a circle is a duality of the projective plane** (Petrunin, Claim 15.17(a)
and the exercise on p. 129, "extend `P ↦ p` to a duality"): `circlePolarEquiv` is a bijection of the points
onto the lines such that a point `P` lies on a line `ℓ` iff the point `circlePolarEquiv.symm ℓ` (the pole of
`ℓ`) lies on the line `circlePolarEquiv P` (the polar of `P`); it agrees with `ProjPoint.circlePolar`. -/
@[kb "petrunin2025" "Claim 15.17, p. 129"]
theorem circlePolarEquiv_duality (c0 c1 r : ℝ) (hr : r ≠ 0) :
    (∀ P : ProjPoint, circlePolarEquiv c0 c1 r hr P = P.circlePolar c0 c1 r hr) ∧
    ∀ (P : ProjPoint) (ℓ : ProjLine),
      P.LiesOn ℓ ↔ ((circlePolarEquiv c0 c1 r hr).symm ℓ).LiesOn (circlePolarEquiv c0 c1 r hr P) := by
  refine ⟨fun P => rfl, fun P ℓ => ?_⟩
  obtain ⟨Q, rfl⟩ := (circlePolarEquiv c0 c1 r hr).surjective ℓ
  rw [Equiv.symm_apply_apply]
  exact liesOn_circlePolar_iff_symm c0 c1 r hr Q P

/-- **Points of the circle correspond to tangent lines, projectively**: a point of the conic lies on its own
polar (Petrunin, Claim 15.17(a), p. 129). -/
theorem onConic_liesOn_circlePolar (c0 c1 r : ℝ) (hr : r ≠ 0) {P : ProjPoint}
    (hP : OnConic (circleBil c0 c1 r) P) : P.LiesOn (P.circlePolar c0 c1 r hr) := by
  rw [ProjPoint.liesOn_circlePolar_iff]
  intro p hp q hq
  obtain ⟨q0, hq0, rfl⟩ := P.exists_rep
  obtain ⟨a, rfl⟩ := (ProjPoint.mem_mk' hq0).1 hp
  obtain ⟨b, rfl⟩ := (ProjPoint.mem_mk' hq0).1 hq
  have := hP q0 (Submodule.mem_span_singleton_self _)
  simp [this]

/-- **A point of the circle corresponds to the tangent line at it** (Petrunin, Claim 15.17(a), p. 129):
for a point `p` of the circle `s` (of positive radius) of the Euclidean plane, the points of the plane lying
on the projective polar of `p` are exactly the points of the tangent line `s.polar p`, which is tangent to `s`
at `p`. -/
@[kb "petrunin2025" "Claim 15.17(a), p. 129"]
theorem polar_of_circle_point (s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (hs : 0 < s.radius) {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ s) :
    (affineToProj (p 0) (p 1)).LiesOn ((affineToProj (p 0) (p 1)).circlePolar (s.center 0) (s.center 1)
      s.radius hs.ne') ∧
    (∀ q : EuclideanSpace ℝ (Fin 2),
      (affineToProj (q 0) (q 1)).LiesOn ((affineToProj (p 0) (p 1)).circlePolar (s.center 0) (s.center 1)
        s.radius hs.ne') ↔ q ∈ s.polar p) ∧
    s.IsTangentAt p (s.polar p) := by
  have hpc : p ≠ s.center := by
    rintro rfl
    rw [EuclideanGeometry.mem_sphere, dist_self] at hp
    exact hs.ne hp
  have heq : s.polar p = s.orthRadius p :=
    (EuclideanGeometry.Sphere.polar_eq_orthRadius_self_iff hs.le).2 (Or.inl hp)
  refine ⟨?_, fun q => ?_, ?_⟩
  · refine onConic_liesOn_circlePolar _ _ _ hs.ne' ?_
    intro v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have := (mem_sphere_iff_circleBil s hs.le p).1 hp
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : (circleBil (s.center 0) (s.center 1) s.radius) (spacePoint (p 0) (p 1))
        (spacePoint (p 0) (p 1)) = 0 := this
    rw [h2]; ring
  · rw [ProjPoint.liesOn_circlePolar_iff, mem_polar_iff_circleBil s hs hpc]
    constructor
    · intro h
      exact h _ (Submodule.mem_span_singleton_self _) _ (Submodule.mem_span_singleton_self _)
    · intro h a ha b hb
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hb
      have h' : circleBil (s.center 0) (s.center 1) s.radius (spacePoint (p 0) (p 1))
          (spacePoint (q 0) (q 1)) = 0 := h
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h']
      ring
  · rw [heq]
    exact EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem.2 hp

/-- **The polar of the center is the ideal line** (Petrunin, exercise on p. 129, "which line corresponds
to `O`?"). -/
@[kb "petrunin2025" "Exercise on duality, p. 129 (center to ideal line)"]
theorem circlePolar_center (c0 c1 r : ℝ) (hr : r ≠ 0) :
    (affineToProj c0 c1).circlePolar c0 c1 r hr = idealProjLine := by
  have : affineToProj c0 c1 = ProjPoint.mk' (spacePoint c0 c1) (spacePoint_ne_zero _ _) := rfl
  rw [this, circlePolar_mk']
  unfold idealProjLine
  rw [lineOfNormal_eq_iff]
  refine ⟨-1 / r ^ 2, ?_⟩
  ext i
  fin_cases i <;> simp [polarNormal, spacePoint] <;> field_simp

/-- **Ideal points correspond to the lines through the center** (Petrunin, exercise on p. 129, "which point
corresponds to the line `a x + b y = 0`?" for the circle centered at the origin): for a point `P` of the
projective plane, the center lies on the polar of `P` iff `P` is an ideal point (equivalently, a line
through the center is the polar of an ideal point; the pole of `a x + b y = 0` is the ideal point spanned by
`(a, b, 0)`). -/
@[kb "petrunin2025" "Exercise on duality, p. 129 (ideal points to lines through the center)"]
theorem center_liesOn_circlePolar_iff (c0 c1 r : ℝ) (hr : r ≠ 0) (P : ProjPoint) :
    (affineToProj c0 c1).LiesOn (P.circlePolar c0 c1 r hr) ↔ P.IsIdeal := by
  rw [liesOn_circlePolar_iff_symm, circlePolar_center]
  constructor
  · intro h v hv
    have := h hv
    exact (mem_idealProjLine v).1 this
  · intro h v hv
    exact (mem_idealProjLine v).2 (h v hv)

/-- The pole of the line through the center with normal `(a, b)`: the polar of the ideal point spanned by
`(a, b, 0)` is the line `a (x - c₀) + b (y - c₁) = 0`; for the circle centered at the origin it is
`a x + b y = 0`. -/
theorem circlePolar_ideal (c0 c1 r : ℝ) (hr : r ≠ 0) {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    (ProjPoint.mk' !₂[a, b, 0] (lineVec_ne_zero h)).circlePolar c0 c1 r hr =
      lineOfNormal !₂[a, b, -(c0 * a + c1 * b)] (lineVec_ne_zero h) := by
  rw [circlePolar_mk', lineOfNormal_eq_iff]
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [polarNormal] <;> ring

end Duality

end UndergradKB.Geometry
