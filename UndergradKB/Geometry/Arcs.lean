import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.Convex.Side
import UndergradKB.Common.Attr

/-! # Inscribed angles, arcs and tangent half-lines (Petrunin, chapter 9)

Tangent-chord angle (Theorem 9.1), the converse of the inscribed angle theorem (Theorem 9.2),
arcs and the two cases of an inscribed angle (Proposition 9.23), inscribed quadrangles
(Proposition 9.26) and tangent half-lines (Proposition 9.27). We work in an oriented Euclidean plane
(`finrank ℝ V = 2` with an orientation) with signed angles `∡` valued in `Real.Angle`.

"The arc `ABC`" of a circle is the part of the circle on the same side of the line `AC` as `B`; the
"opposite arc" is the part on the other side. A circle is a bundled `EuclideanGeometry.Sphere`; the
circle through three distinct points `A, B, C` is any sphere containing them (it is unique). -/

set_option linter.unusedSectionVars false

namespace UndergradKB.Geometry

open EuclideanGeometry Real AffineSubspace
open scoped Affine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [iT : NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

namespace Arcs

/-- In a plane, two points off a line lie strictly on the same side or strictly on opposite sides. -/
theorem sSameSide_or_sOppSide {ℓ : AffineSubspace ℝ P}
    (hℓ : Module.finrank ℝ ℓ.direction = 1) {x y : P} (hx : x ∉ ℓ) (hy : y ∉ ℓ) :
    ℓ.SSameSide x y ∨ ℓ.SOppSide x y := by
  have hne : ℓ ≠ ⊥ := by
    rintro rfl
    rw [direction_bot, finrank_bot] at hℓ
    exact absurd hℓ (by norm_num)
  have : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (n := 1) (Fact.out (p := Module.finrank ℝ V = 2))
  obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot ℓ).2 hne
  have hv : y -ᵥ p ∉ ℓ.direction := fun h =>
    hy (by simpa using AffineSubspace.vadd_mem_of_mem_direction h hp)
  have htop : ℓ.direction ⊔ (ℝ ∙ (y -ᵥ p)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hv, hℓ, Fact.out (p := Module.finrank ℝ V = 2)]
  have hx' : x -ᵥ p ∈ ℓ.direction ⊔ (ℝ ∙ (y -ᵥ p)) := by rw [htop]; trivial
  obtain ⟨d, hd, w, hw, hdw⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hp' : d +ᵥ p ∈ ℓ := AffineSubspace.vadd_mem_of_mem_direction hd hp
  have hxe : x -ᵥ (d +ᵥ p) = a • (y -ᵥ p) := by
    rw [vsub_vadd_eq_vsub_sub, ← hdw]; abel
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    have : x = d +ᵥ p := by simpa using hxe
    rw [this]; exact hp'
  rcases lt_or_gt_of_ne ha with h | h
  · right
    refine ⟨⟨_, hp', p, hp, Or.inr (Or.inr ⟨1, -a, one_pos, by linarith, ?_⟩)⟩, hx, hy⟩
    rw [hxe, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]; simp
  · left
    refine ⟨⟨_, hp', p, hp, Or.inr (Or.inr ⟨1, a, one_pos, h, ?_⟩)⟩, hx, hy⟩
    rw [hxe]; simp

/-- The line through two distinct points has a one-dimensional direction. -/
theorem finrank_direction_line {P₁ P₂ : P} (h : P₁ ≠ P₂) :
    Module.finrank ℝ (line[ℝ, P₁, P₂]).direction = 1 := by
  rw [direction_affineSpan]
  have := (affineIndependent_of_ne ℝ h).finrank_vectorSpan (n := 1) (by simp)
  have hr : Set.range ![P₁, P₂] = {P₁, P₂} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]; simp [Set.pair_comm]
  rwa [hr] at this

/-- For a point off the line `PQ`, the sign of the angle `∡PXQ` is nonzero. -/
theorem oangle_sign_ne_zero_of_notMem {P₁ P₂ X : P} (h : X ∉ line[ℝ, P₁, P₂]) (h₁₂ : P₁ ≠ P₂) :
    (∡ P₁ X P₂).sign ≠ 0 := by
  intro h0
  rw [Real.Angle.sign_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear] at h0
  exact h (h0.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h₁₂)

/-- A point of the plane off the line `PQ` has `∡PXQ` of nonzero sign iff it is off the line. -/
theorem notMem_of_oangle_sign_ne_zero {P₁ P₂ X : P} (h : (∡ P₁ X P₂).sign ≠ 0) :
    X ∉ line[ℝ, P₁, P₂] := by
  intro hX
  apply h
  rw [oangle_sign_eq_zero_iff_collinear]
  have := collinear_insert_of_mem_affineSpan_pair hX
  rwa [Set.insert_comm] at this

/-- Two points off the line `PQ` lie strictly on the same side iff `∡PXQ`, `∡PYQ` have the same
sign. -/
theorem sSameSide_iff_oangle_sign_eq {P₁ P₂ X Y : P} (h₁₂ : P₁ ≠ P₂) (hX : X ∉ line[ℝ, P₁, P₂])
    (hY : Y ∉ line[ℝ, P₁, P₂]) :
    line[ℝ, P₁, P₂].SSameSide X Y ↔ (∡ P₁ X P₂).sign = (∡ P₁ Y P₂).sign := by
  constructor
  · intro h
    exact (h.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)).symm
  · intro h
    rcases sSameSide_or_sOppSide (finrank_direction_line h₁₂) hX hY with h' | h'
    · exact h'
    · exfalso
      have h2 := h'.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ P₁ P₂)
        (right_mem_affineSpan_pair ℝ P₁ P₂)
      have h3 := oangle_sign_ne_zero_of_notMem hX h₁₂
      rw [← h] at h2
      revert h2 h3
      generalize (∡ P₁ X P₂).sign = z
      decide +revert

/-- **Two cases of an inscribed angle**: for `B, D` off the line `AC` with
`2·∡ABC = 2·∡ADC`, the angles are equal iff `B, D` are on the same side of `AC`, and differ by `π`
iff they are on opposite sides. -/
theorem side_dichotomy {A B C D : P} (hAC : A ≠ C) (hB : B ∉ line[ℝ, A, C])
    (hD : D ∉ line[ℝ, A, C]) (h : (2 : ℤ) • ∡ A B C = (2 : ℤ) • ∡ A D C) :
    (∡ A B C = ∡ A D C ↔ line[ℝ, A, C].SSameSide B D) ∧
      (∡ A B C = ∡ A D C + π ↔ line[ℝ, A, C].SOppSide B D) := by
  have hsB := oangle_sign_ne_zero_of_notMem hB hAC
  have hsame := sSameSide_iff_oangle_sign_eq hAC hB hD
  rcases sSameSide_or_sOppSide (finrank_direction_line hAC) hB hD with hs | hs
  · have hsign := hsame.1 hs
    have heq : ∡ A B C = ∡ A D C := (Real.Angle.two_zsmul_eq_iff_eq hsB hsign).1 h
    refine ⟨⟨fun _ => hs, fun _ => heq⟩, ⟨fun h' => ?_, fun h' => absurd h' hs.not_sOppSide⟩⟩
    exfalso
    rw [heq] at h'
    have : (π : Real.Angle) = 0 := by simpa using h'
    exact Real.Angle.pi_ne_zero this
  · have hsign : (∡ A D C).sign = -(∡ A B C).sign :=
      hs.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ A C) (right_mem_affineSpan_pair ℝ A C)
    have hne : ∡ A B C ≠ ∡ A D C := by
      intro he
      rw [← he] at hsign
      revert hsign hsB
      generalize (∡ A B C).sign = z
      decide +revert
    rcases Real.Angle.two_zsmul_eq_iff.1 h with h1 | h2
    · exact absurd h1 hne
    · exact ⟨⟨fun h' => absurd h' hne, fun h' => absurd h' hs.not_sSameSide⟩,
        ⟨fun _ => hs, fun _ => h2⟩⟩

/-- A point `B` on a circle through the distinct points `A`, `C`, different from both, is off the
line `AC`. -/
theorem notMem_line_of_mem_sphere {s : Sphere P} {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hAC : A ≠ C) (hBA : B ≠ A) (hBC : B ≠ C) : B ∉ line[ℝ, A, C] := by
  intro hmem
  have hc : Cospherical ({A, B, C} : Set P) :=
    ⟨s.center, s.radius, by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;> assumption⟩
  have hind := hc.affineIndependent_of_ne hBA.symm hAC hBC
  rw [affineIndependent_iff_not_collinear_set] at hind
  apply hind
  have := collinear_insert_of_mem_affineSpan_pair hmem
  rwa [Set.insert_comm] at this

/-- Three distinct points of a circle determine it: a point `W` with `2·∡XWY = 2·∡XZY`, where
`X, Y, Z` are distinct points of a circle `s`, lies on `s`. -/
theorem mem_sphere_of_two_zsmul_oangle_eq {s : Sphere P} {X Y Z W : P} (hX : X ∈ s) (hY : Y ∈ s)
    (hZ : Z ∈ s) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hZY : Z ≠ Y)
    (h : (2 : ℤ) • ∡ X W Y = (2 : ℤ) • ∡ X Z Y) : W ∈ s := by
  have hc : Cospherical ({X, Z, Y} : Set P) :=
    ⟨s.center, s.radius, by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;> assumption⟩
  have hind := hc.affineIndependent_of_ne hXZ hXY hZY
  have : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (n := 1) (Fact.out (p := Module.finrank ℝ V = 2))
  let t : Affine.Triangle ℝ P := ⟨![X, Z, Y], hind⟩
  have hW : W ∈ t.circumsphere :=
    Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide) h
  have hts : t.circumsphere = s := by
    by_contra hne
    have hX' : X ∈ t.circumsphere := t.mem_circumsphere 0
    have hZ' : Z ∈ t.circumsphere := t.mem_circumsphere 1
    have hY' : Y ∈ t.circumsphere := t.mem_circumsphere 2
    rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two (Fact.out) hne hXY hX' hY' hZ' hX hY hZ
      with h1 | h1
    · exact hXZ h1.symm
    · exact hZY h1
  rwa [hts] at hW

include iT in
/-- On a circle through two distinct points `X`, `Y` there is a third point. -/
theorem exists_mem_sphere_ne {s : Sphere P} {X Y : P} (hX : X ∈ s) (hY : Y ∈ s) (hXY : X ≠ Y) :
    ∃ Z ∈ s, Z ≠ X ∧ Z ≠ Y := by
  set c := s.center
  have hv : X -ᵥ c ≠ 0 := by
    intro h0
    rw [vsub_eq_zero_iff_eq] at h0
    apply hXY
    have h1 : dist X c = s.radius := hX
    have h2 : dist Y c = s.radius := hY
    rw [h0, dist_self] at h1
    rw [← h1] at h2
    rw [h0]
    exact (dist_eq_zero.mp h2).symm
  set v := X -ᵥ c with hvdef
  let o : Orientation ℝ V (Fin 2) := Module.Oriented.positiveOrientation
  have hnorm : ‖o.rightAngleRotation v‖ = ‖v‖ := LinearIsometryEquiv.norm_map _ _
  have hinner : inner ℝ (o.rightAngleRotation v) v = 0 := o.inner_rightAngleRotation_self v
  have hJne : o.rightAngleRotation v ≠ v := by
    intro he
    rw [he] at hinner
    exact hv (inner_self_eq_zero.mp hinner)
  have hJ0 : o.rightAngleRotation v ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    exact hv (norm_eq_zero.mp (by simpa using hnorm.symm))
  have hr : ‖v‖ = s.radius := by
    rw [hvdef, ← dist_eq_norm_vsub V]; exact hX
  have hdist : ∀ w : V, ‖w‖ = ‖v‖ → w +ᵥ c ∈ s := by
    intro w hw
    show dist (w +ᵥ c) c = s.radius
    rw [dist_eq_norm_vsub V, vadd_vsub, hw, hr]
  have hXe : X = v +ᵥ c := (vsub_vadd X c).symm
  by_cases h1 : o.rightAngleRotation v +ᵥ c = Y
  · refine ⟨(-o.rightAngleRotation v) +ᵥ c, hdist _ (by rw [norm_neg, hnorm]), ?_, ?_⟩
    · intro he
      rw [hXe] at he
      have h3 : -o.rightAngleRotation v = v := vadd_right_cancel c he
      have h4 : o.rightAngleRotation v = -v := neg_eq_iff_eq_neg.mp h3
      rw [h4] at hinner
      simp only [inner_neg_left, neg_eq_zero] at hinner
      exact hv (inner_self_eq_zero.mp hinner)
    · intro he
      rw [← h1] at he
      have := vadd_right_cancel c he
      apply hJ0
      have h5 : o.rightAngleRotation v = 0 := by
        have := congrArg (fun w => o.rightAngleRotation v + w) this
        simp only [add_neg_cancel] at this
        have h6 : (2 : ℝ) • o.rightAngleRotation v = 0 := by
          rw [two_smul]; exact this.symm
        simpa using h6
      exact h5
  · refine ⟨o.rightAngleRotation v +ᵥ c, hdist _ hnorm, ?_, fun h => h1 h⟩
    intro he
    rw [hXe] at he
    exact hJne (vadd_right_cancel c he)

end Arcs

open Arcs

/-- Right angle at `X` between `XQ` and the radius `XO` gives `2·∡QXO = π`. -/
theorem two_zsmul_oangle_eq_pi_of_angle {Q X O : P} (h : ∠ Q X O = π / 2) (hQ : Q ≠ X)
    (hO : O ≠ X) : (2 : ℤ) • ∡ Q X O = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff, ← Real.Angle.abs_toReal_eq_pi_div_two_iff,
    ← angle_eq_abs_oangle_toReal hQ hO]
  exact h

/-- Conversely, `2·∡QXO = π` gives a right angle. -/
theorem angle_eq_pi_div_two_of_two_zsmul_oangle {Q X O : P} (h : (2 : ℤ) • ∡ Q X O = π)
    (hQ : Q ≠ X) (hO : O ≠ X) : ∠ Q X O = π / 2 := by
  rw [angle_eq_abs_oangle_toReal hQ hO, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  exact Real.Angle.two_zsmul_eq_pi_iff.mp h

/-- **Angle between a tangent line and a chord** (Petrunin, Theorem 9.1): let `s` be a circle with
centre `O`, `X, Y ∈ s`, and let `(XQ)` be tangent to `s` at `X` (i.e. `XQ ⊥ XO`, with `Q ≠ X`).
Then `2·∡QXY = ∡XOY`. -/
@[kb "petrunin2025" "Theorem 9.1, p. 65"]
theorem two_zsmul_oangle_tangent_chord {s : Sphere P} {X Y Q : P} (hX : X ∈ s) (hY : Y ∈ s)
    (hQX : Q ≠ X) (htan : inner ℝ (Q -ᵥ X) (X -ᵥ s.center) = 0) :
    (2 : ℤ) • ∡ Q X Y = ∡ X s.center Y := by
  rcases eq_or_ne Y X with rfl | hYX
  · simp
  have hc : s.center ≠ X := by
    intro h
    apply hYX
    have h1 : dist X s.center = s.radius := hX
    have h2 : dist Y s.center = s.radius := hY
    rw [h, dist_self] at h1
    rw [h, ← h1] at h2
    exact dist_eq_zero.mp h2
  have hang : ∠ Q X s.center = π / 2 := by
    have h1 := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp htan
    rw [angle, ← neg_vsub_eq_vsub_rev _ s.center, InnerProductGeometry.angle_neg_right, h1]
    linarith
  have h2 := two_zsmul_oangle_eq_pi_of_angle hang hQX hc
  rw [← oangle_add hQX hc hYX, smul_add, h2,
    Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right hX hY hYX.symm, oangle_rev s.center X Y]
  simp only [smul_neg, sub_neg_eq_add]

/-- **Inscribed angle theorem, converse** (Petrunin, Theorem 9.2, "if" part): let `s` be a circle with
centre `O` through `X ≠ Y`, and `P` a point different from `X, Y` with `2·∡XPY = ∡XOY`. Then `P`
lies on `s`. -/
@[kb "petrunin2025" "Theorem 9.2, p. 66"]
theorem mem_sphere_of_two_zsmul_oangle_eq_center {s : Sphere P} {X Y W : P} (hX : X ∈ s)
    (hY : Y ∈ s) (hXY : X ≠ Y) (h : (2 : ℤ) • ∡ X W Y = ∡ X s.center Y) : W ∈ s := by
  obtain ⟨Z, hZ, hZX, hZY⟩ := exists_mem_sphere_ne hX hY hXY
  refine mem_sphere_of_two_zsmul_oangle_eq hX hY hZ hXY hZX.symm hZY ?_
  rw [h, Sphere.oangle_center_eq_two_zsmul_oangle hX hZ hY hZX hZY]

/-- **Arc criterion, same side** (Petrunin, Proposition 9.23(a)): let `A, B, C` be distinct points of
a circle `s` (so `s` is the circle through `A, B, C`) and `X ≠ A, C`. Then `∡AXC = ∡ABC` iff `X`
lies on the arc `ABC`, i.e. on `s` strictly on the same side of `(AC)` as `B`. -/
@[kb "petrunin2025" "Proposition 9.23, p. 71"]
theorem oangle_eq_iff_mem_arc {s : Sphere P} {A B C X : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hAC : A ≠ C) (hBA : B ≠ A) (hBC : B ≠ C) (hXA : X ≠ A) (hXC : X ≠ C) :
    ∡ A X C = ∡ A B C ↔ X ∈ s ∧ line[ℝ, A, C].SSameSide X B := by
  have hBl := notMem_line_of_mem_sphere hA hB hC hAC hBA hBC
  have hsB := oangle_sign_ne_zero_of_notMem hBl hAC
  constructor
  · intro h
    have hXs : X ∈ s :=
      mem_sphere_of_two_zsmul_oangle_eq hA hC hB hAC hBA.symm hBC (by rw [h])
    have hXl : X ∉ line[ℝ, A, C] := by
      apply notMem_of_oangle_sign_ne_zero
      rw [h]; exact hsB
    refine ⟨hXs, ?_⟩
    rw [sSameSide_iff_oangle_sign_eq hAC hXl hBl, h]
  · rintro ⟨hXs, hside⟩
    have h2 : (2 : ℤ) • ∡ A X C = (2 : ℤ) • ∡ A B C :=
      Sphere.two_zsmul_oangle_eq hA hXs hB hC hXA hXC hBA hBC
    have hsign := (sSameSide_iff_oangle_sign_eq hAC hside.left_notMem hBl).1 hside
    exact (Real.Angle.two_zsmul_eq_iff_eq (by rwa [hsign]) hsign).1 h2

/-- **Arc criterion, opposite side** (Petrunin, Proposition 9.23(b)): with `A, B, C` distinct points of
a circle `s` and `X ≠ A, C`, `∡AXC = ∡ABC + π` iff `X` lies on the opposite arc, i.e. on `s` strictly
on the other side of `(AC)` than `B`. -/
@[kb "petrunin2025" "Proposition 9.23, p. 71"]
theorem oangle_eq_add_pi_iff_mem_opposite_arc {s : Sphere P} {A B C X : P} (hA : A ∈ s) (hB : B ∈ s)
    (hC : C ∈ s) (hAC : A ≠ C) (hBA : B ≠ A) (hBC : B ≠ C) (hXA : X ≠ A) (hXC : X ≠ C) :
    ∡ A X C = ∡ A B C + π ↔ X ∈ s ∧ line[ℝ, A, C].SOppSide X B := by
  have hBl := notMem_line_of_mem_sphere hA hB hC hAC hBA hBC
  have hsB := oangle_sign_ne_zero_of_notMem hBl hAC
  constructor
  · intro h
    have hXs : X ∈ s :=
      mem_sphere_of_two_zsmul_oangle_eq hA hC hB hAC hBA.symm hBC (by
        rw [h, smul_add, Real.Angle.two_zsmul_coe_pi, add_zero])
    have hXl : X ∉ line[ℝ, A, C] := by
      apply notMem_of_oangle_sign_ne_zero
      rw [h, Real.Angle.sign_add_pi]
      intro h0
      exact hsB (by simpa using h0)
    refine ⟨hXs, ?_⟩
    have h2 : (2 : ℤ) • ∡ A X C = (2 : ℤ) • ∡ A B C :=
      Sphere.two_zsmul_oangle_eq hA hXs hB hC hXA hXC hBA hBC
    exact ((side_dichotomy hAC hXl hBl h2).2).1 h
  · rintro ⟨hXs, hside⟩
    have h2 : (2 : ℤ) • ∡ A X C = (2 : ℤ) • ∡ A B C :=
      Sphere.two_zsmul_oangle_eq hA hXs hB hC hXA hXC hBA hBC
    exact ((side_dichotomy hAC hside.left_notMem hBl h2).2).2 hside

/-- **Inscribed quadrangles** (Petrunin, Proposition 9.26, first part; the book's degenerate case
of a line is not treated): for a quadrangle `ABCD` with `B, D ∉ {A, C}` and `A, B, C` not collinear,
the four points lie on a circle iff `∡ABC + ∡CDA ≡ 0` or `π` (mod `2π`), i.e.
`2·(∡ABC + ∡CDA) = 0`. -/
@[kb "petrunin2025" "Proposition 9.26, p. 71"]
theorem cospherical_iff_two_zsmul_oangle_add {A B C D : P} (hBA : B ≠ A) (hBC : B ≠ C)
    (hDA : D ≠ A) (hDC : D ≠ C) (hABC : ¬Collinear ℝ ({A, B, C} : Set P)) :
    Cospherical ({A, B, C, D} : Set P) ↔ (2 : ℤ) • (∡ A B C + ∡ C D A) = 0 := by
  rw [smul_add, oangle_rev A D C, smul_neg, add_neg_eq_zero]
  constructor
  · intro h
    rw [Set.pair_comm C D] at h
    exact h.two_zsmul_oangle_eq hBA hBC hDA hDC
  · intro h
    have := cospherical_of_two_zsmul_oangle_eq_of_not_collinear (p₁ := A) (p₂ := B) (p₃ := D)
      (p₄ := C) h hABC
    rwa [Set.pair_comm D C] at this

/-- **Inscribed quadrangles, cyclic order** (Petrunin, Proposition 9.26, second part): for a quadrangle
`ABCD` with `B, D ∉ (AC)` and `2·(∡ABC + ∡CDA) = 0` (which holds when `ABCD` is inscribed, by
`cospherical_iff_two_zsmul_oangle_add`), the sum is `0` iff `B, D` lie on the same side of `(AC)`, and
`π` iff they lie on opposite sides, which is the book's "`A, B, C, D` appear on the circle in the same
cyclic order" (the arcs `ABC` and `ADC` are opposite). -/
@[kb "petrunin2025" "Proposition 9.26, p. 71"]
theorem oangle_add_eq_pi_iff_sOppSide {A B C D : P} (hAC : A ≠ C) (hB : B ∉ line[ℝ, A, C])
    (hD : D ∉ line[ℝ, A, C]) (h : (2 : ℤ) • (∡ A B C + ∡ C D A) = 0) :
    (∡ A B C + ∡ C D A = 0 ↔ line[ℝ, A, C].SSameSide B D) ∧
      (∡ A B C + ∡ C D A = π ↔ line[ℝ, A, C].SOppSide B D) := by
  rw [smul_add, oangle_rev A D C, smul_neg, add_neg_eq_zero] at h
  have hd := side_dichotomy hAC hB hD h
  rw [oangle_rev A D C, ← sub_eq_add_neg, sub_eq_zero, sub_eq_iff_eq_add']
  exact hd

/-- **Tangent half-lines** (Petrunin, Proposition 9.27): let `A, B, C` be distinct points of a circle
`s` and `X ≠ A`. The half-line `[AX)` is tangent to the arc `ABC` at `A`, meaning that the line `(AX)`
is tangent to `s` at `A` and `X`, `B` lie on the same side of `(AC)`, iff `∡ABC + ∡CAX = π`. -/
@[kb "petrunin2025" "Proposition 9.27, p. 72"]
theorem tangent_halfline_iff {s : Sphere P} {A B C X : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hAC : A ≠ C) (hBA : B ≠ A) (hBC : B ≠ C) (hXA : X ≠ A) :
    (s.IsTangentAt A line[ℝ, A, X] ∧ line[ℝ, A, C].SSameSide X B) ↔ ∡ A B C + ∡ C A X = π := by
  have hBl := notMem_line_of_mem_sphere hA hB hC hAC hBA hBC
  have hsB := oangle_sign_ne_zero_of_notMem hBl hAC
  have hOA : s.center ≠ A := by
    intro h
    have h1 : dist A s.center = s.radius := hA
    have h2 : dist B s.center = s.radius := hB
    rw [h, dist_self] at h1
    rw [h, ← h1] at h2
    exact hBA (dist_eq_zero.mp h2)
  have hT : (2 : ℤ) • ∡ C A s.center + (2 : ℤ) • ∡ A B C = π :=
    Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hA hB hC hBA hBC hAC
  have hsum : ∡ X A C + ∡ C A s.center = ∡ X A s.center := oangle_add hXA hAC.symm hOA
  have hrev : ∡ C A X = -∡ X A C := oangle_rev X A C
  have hsgn : (∡ C A X).sign = (∡ A X C).sign := (oangle_rotate_sign C A X).symm
  constructor
  · rintro ⟨htan, hside⟩
    have hang : ∠ X A s.center = π / 2 :=
      (Sphere.IsTangentAt_iff_angle_eq_pi_div_two hA).1 htan
    have h2 := two_zsmul_oangle_eq_pi_of_angle hang hXA hOA
    rw [← hsum, smul_add] at h2
    have hs2 : (2 : ℤ) • (∡ A B C + ∡ C A X) = 0 := by
      rw [smul_add, hrev, smul_neg]
      have : (2 : ℤ) • ∡ X A C = (2 : ℤ) • ∡ A B C := by
        have e1 : (2 : ℤ) • ∡ X A C = π - (2 : ℤ) • ∡ C A s.center := by
          rw [← h2]; abel
        rw [e1, ← hT]; abel
      rw [this]; abel
    have hsign : (∡ A B C).sign = (∡ C A X).sign := by
      rw [hsgn]
      exact hside.oangle_sign_eq (left_mem_affineSpan_pair ℝ A C)
        (right_mem_affineSpan_pair ℝ A C)
    rcases Real.Angle.two_zsmul_eq_zero_iff.1 hs2 with h0 | hpi
    · exfalso
      have h0' : ∡ C A X = -∡ A B C := eq_neg_of_add_eq_zero_right h0
      rw [h0', Real.Angle.sign_neg] at hsign
      revert hsign hsB
      generalize (∡ A B C).sign = z
      decide +revert
    · exact hpi
  · intro h
    have hCAX : ∡ C A X = π - ∡ A B C := by rw [← h]; abel
    have hsign : (∡ A X C).sign = (∡ A B C).sign := by
      rw [← hsgn, hCAX, Real.Angle.sign_pi_sub]
    have hXl : X ∉ line[ℝ, A, C] := by
      apply notMem_of_oangle_sign_ne_zero
      rw [hsign]; exact hsB
    refine ⟨?_, (sSameSide_iff_oangle_sign_eq hAC hXl hBl).2 hsign⟩
    rw [Sphere.IsTangentAt_iff_angle_eq_pi_div_two hA]
    apply angle_eq_pi_div_two_of_two_zsmul_oangle _ hXA hOA
    rw [← hsum, smul_add]
    have e1 : (2 : ℤ) • ∡ X A C = -((2 : ℤ) • ∡ C A X) := by rw [hrev, smul_neg, neg_neg]
    have e2 : (2 : ℤ) • ∡ C A X = (2 : ℤ) • (π : Real.Angle) - (2 : ℤ) • ∡ A B C := by
      rw [hCAX, smul_sub]
    have e3 : (2 : ℤ) • (π : Real.Angle) = 0 := Real.Angle.two_zsmul_coe_pi
    rw [e1, e2, e3, ← hT]
    abel

end UndergradKB.Geometry
