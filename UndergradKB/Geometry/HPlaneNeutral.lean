import Mathlib.Analysis.Complex.Angle
import UndergradKB.Geometry.Neutral
import UndergradKB.Geometry.HPlane
import UndergradKB.Geometry.HypLines
import UndergradKB.Geometry.HypAngles
import UndergradKB.Geometry.HypTriangles
import UndergradKB.Common.Attr

/-! # The h-plane is a neutral plane satisfying Axiom h-V (Petrunin, Chapter 11 and 12)

Beltrami's model (Theorem 11.17, 'if' part, p. 89): the h-plane `HPoint` (the conformal disc model
built inside the complex plane) satisfies Axioms I-IV and the hyperbolic axiom h-V.  We assemble the
pieces proved for the disc model (`HypLines`, `HypAngles`) into `hyperbolicNeutralPlane : NeutralPlane HPoint`
with the angle measure `hoangle`, prove that the lines of the metric space `HPoint` are exactly the
h-lines (`HPoint.isLine_iff`), the half-lines of the metric space are the h-half-lines
(`HPoint.mem_metricHalfLine_iff`), and that Axiom h-V holds.  This is also the example (Chapter 11,
p. 83-89) of a neutral plane that is not Euclidean: Axiom V fails (`hyperbolicNeutralPlane_not_axiomV`). -/

namespace UndergradKB.Geometry

open Complex ComplexConjugate

namespace HPoint

/-- The h-line `hline α c` as a set of points of the h-plane. -/
def hlineSet (α : ℝ) (c : ℂ) : Set HPoint := {p | p.z ∈ hline α c}

theorem image_z_hlineSet (α : ℝ) (c : ℂ) : HPoint.z '' hlineSet α c = hline α c := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hw
    exact ⟨⟨w, hw.1⟩, hw, rfl⟩

theorem z_injective : Function.Injective HPoint.z := fun _ _ h => HPoint.ext h

/-- The lines of the metric space `HPoint` (subsets isometric to `ℝ`) are exactly the h-lines. -/
@[kb "petrunin2025" "Claim 12.15, p. 99"]
theorem isLine_iff (L : Set HPoint) :
    IsLine L ↔ ∃ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 ∧ HPoint.z '' L = hline α c := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hd : ∀ s t, hdist (f s).z (f t).z = |s - t| := fun s t => by
      have := hf.dist_eq s t
      rwa [Real.dist_eq] at this
    obtain ⟨α, c, hlt, hr⟩ := exists_hline_of_isometric (fun t => (f t).norm_lt) hd
    refine ⟨α, c, hlt, ?_⟩
    rw [← hr]
    exact (Set.range_comp HPoint.z f).symm
  · rintro ⟨α, c, hlt, himg⟩
    obtain ⟨g, hg, hr⟩ := exists_isometric_param hlt
    have hmem : ∀ t, ‖g t‖ < 1 := fun t => by
      have : g t ∈ hline α c := hr ▸ ⟨t, rfl⟩
      exact this.1
    refine ⟨fun t => ⟨g t, hmem t⟩, Isometry.of_dist_eq fun s t => ?_, ?_⟩
    · rw [Real.dist_eq]
      exact hg s t
    · apply Set.image_injective.mpr z_injective
      rw [himg, ← Set.range_comp]
      exact hr

end HPoint

/-! ### Half-lines -/

theorem hsegment_subset_hray {P Q z : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (h : z ∈ hsegment P Q) :
    z ∈ hray P Q := by
  obtain ⟨hz, hs⟩ := (mem_hsegment_iff hP hQ).1 h
  rw [segment_eq_image'] at hs
  obtain ⟨θ, ⟨h0, -⟩, hθ⟩ := hs
  exact ⟨hz, θ, h0, by simpa [Complex.real_smul] using hθ.symm⟩

theorem mem_hray_of_mem_hsegment_right {P Q z : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hz : ‖z‖ < 1)
    (hne : Q ≠ P) (h : Q ∈ hsegment P z) : z ∈ hray P Q := by
  obtain ⟨-, hs⟩ := (mem_hsegment_iff hP hz).1 h
  rw [segment_eq_image'] at hs
  obtain ⟨θ, ⟨h0, -⟩, hθ⟩ := hs
  have hm := mobius_ne_zero hP hQ hne
  have e : mobius P Q = (θ : ℂ) * mobius P z := by simpa [Complex.real_smul] using hθ.symm
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hm
    rw [e]; simp
  have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
  refine ⟨hz, 1 / θ, (one_div_pos.2 hpos).le, ?_⟩
  rw [e]
  have : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0
  push_cast
  field_simp

theorem HPoint.mem_hray_of_mem_metricHalfLine {O B X : HPoint} (hBO : B ≠ O)
    (h : X ∈ metricHalfLine O B) : X.z ∈ hray O.z B.z := by
  obtain ⟨f, hf, h0, ⟨q, hq, hfq⟩, t, ht, hft⟩ := h
  subst h0
  subst hfq
  subst hft
  have hd : ∀ a b, hdist (f a).z (f b).z = |a - b| := fun a b => by
    have := hf.dist_eq a b
    rwa [Real.dist_eq] at this
  rcases le_total t q with htq | hqt
  · apply hsegment_subset_hray (f 0).norm_lt (f q).norm_lt
    refine (hdist_add_iff_mem_hsegment (f 0).norm_lt (f t).norm_lt (f q).norm_lt).1 ?_
    rw [hd, hd, hd, zero_sub, zero_sub, abs_neg, abs_neg, abs_of_nonneg hq.le, abs_of_nonneg ht,
      abs_of_nonpos (by linarith)]
    ring
  · apply mem_hray_of_mem_hsegment_right (f 0).norm_lt (f q).norm_lt (f t).norm_lt
      (fun h => hBO (HPoint.ext h))
    refine (hdist_add_iff_mem_hsegment (f 0).norm_lt (f q).norm_lt (f t).norm_lt).1 ?_
    rw [hd, hd, hd, zero_sub, zero_sub, abs_neg, abs_neg, abs_of_nonneg hq.le, abs_of_nonneg ht,
      abs_of_nonpos (by linarith)]
    ring

theorem HPoint.mem_metricHalfLine_of_mem_hray {O B X : HPoint} (hBO : B ≠ O)
    (h : X.z ∈ hray O.z B.z) : X ∈ metricHalfLine O B := by
  obtain ⟨-, s, hs, hsX⟩ := h
  have hmne : mobius O.z B.z ≠ 0 :=
    mobius_ne_zero O.norm_lt B.norm_lt (fun h => hBO (HPoint.ext h))
  obtain ⟨m, hm⟩ : ∃ m, m = mobius O.z B.z := ⟨_, rfl⟩
  rw [← hm] at hmne hsX
  have hm1 : ‖m‖ < 1 := by rw [hm]; exact norm_mobius_lt_one O.norm_lt B.norm_lt
  have hmn : 0 < ‖m‖ := norm_pos_iff.2 hmne
  obtain ⟨u, hu_def⟩ : ∃ u : ℂ, u = m / (‖m‖ : ℂ) := ⟨_, rfl⟩
  have hnc : (‖m‖ : ℂ) ≠ 0 := by exact_mod_cast hmn.ne'
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, norm_norm, div_self hmn.ne']
  have hum : u * (‖m‖ : ℂ) = m := by rw [hu_def]; field_simp
  have hOn : ‖-O.z‖ < 1 := by simpa using O.norm_lt
  have hg : ∀ t : ℝ, ‖u * ((Real.tanh (t / 2) : ℝ) : ℂ)‖ < 1 := fun t => by
    rw [norm_mul, hu, one_mul]; exact norm_tanh_lt t
  let f : ℝ → HPoint := fun t =>
    ⟨mobius (-O.z) (u * ((Real.tanh (t / 2) : ℝ) : ℂ)), norm_mobius_lt_one hOn (hg t)⟩
  have hiso : Isometry f := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [Real.dist_eq]
    show hdist (mobius (-O.z) _) (mobius (-O.z) _) = _
    rw [hdist_mobius hOn (hg s) (hg t), hdist_rot hu, hdist_tanh]
  have hdz : ∀ y : ℂ, ‖y‖ < 1 → ‖y‖ = Real.tanh (hdist 0 y / 2) := fun y hy =>
    (hdist_zero_eq_iff (r := hdist 0 y) hy).1 rfl
  have hq0 : 0 ≠ hdist 0 m := by
    intro h
    have := (hdist_eq_zero_iff (P := 0) (Q := m) (by simp) hm1).1 h.symm
    exact hmne this.symm
  have hqpos : 0 < hdist 0 m := lt_of_le_of_ne (hdist_nonneg (by simp) hm1) hq0
  refine ⟨f, hiso, HPoint.ext ?_, ⟨hdist 0 m, hqpos, HPoint.ext ?_⟩, hdist 0 (mobius O.z X.z),
    hdist_nonneg (by simp) (norm_mobius_lt_one O.norm_lt X.norm_lt), HPoint.ext ?_⟩
  · show mobius (-O.z) (u * ((Real.tanh (0 / 2) : ℝ) : ℂ)) = O.z
    simp [mobius_neg_zero]
  · show mobius (-O.z) (u * ((Real.tanh (hdist 0 m / 2) : ℝ) : ℂ)) = B.z
    rw [← hdz m hm1, hum, hm]
    exact mobius_neg_mobius O.norm_lt B.norm_lt
  · show mobius (-O.z) (u * ((Real.tanh (hdist 0 (mobius O.z X.z) / 2) : ℝ) : ℂ)) = X.z
    rw [← hdz _ (norm_mobius_lt_one O.norm_lt X.norm_lt)]
    have hn : ‖mobius O.z X.z‖ = s * ‖m‖ := by
      rw [hsX, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    have : u * ((‖mobius O.z X.z‖ : ℝ) : ℂ) = mobius O.z X.z := by
      rw [hn]
      calc u * ((s * ‖m‖ : ℝ) : ℂ) = (s : ℂ) * (u * (‖m‖ : ℂ)) := by push_cast; ring
        _ = mobius O.z X.z := by rw [hum, hsX]
    rw [this]
    exact mobius_neg_mobius O.norm_lt X.norm_lt

/-- The half-lines of the metric space `HPoint` are the h-half-lines. -/
@[kb "petrunin2025" "Theorem 11.17, p. 89"]
theorem HPoint.mem_metricHalfLine_iff {O B X : HPoint} (hBO : B ≠ O) :
    X ∈ metricHalfLine O B ↔ X.z ∈ hray O.z B.z :=
  ⟨HPoint.mem_hray_of_mem_metricHalfLine hBO, HPoint.mem_metricHalfLine_of_mem_hray hBO⟩

/-! ### Axioms I-III -/

theorem hneutral_axiomII (A B : HPoint) (hAB : A ≠ B) :
    ∃! L : Set HPoint, IsLine L ∧ A ∈ L ∧ B ∈ L := by
  have hne : A.z ≠ B.z := fun h => hAB (HPoint.ext h)
  obtain ⟨α, c, hlt, hA, hB, huniq⟩ := exists_unique_hline A.norm_lt B.norm_lt hne
  refine ⟨HPoint.hlineSet α c,
    ⟨(HPoint.isLine_iff _).2 ⟨α, c, hlt, HPoint.image_z_hlineSet α c⟩, hA, hB⟩, ?_⟩
  rintro L ⟨hL, hAL, hBL⟩
  obtain ⟨α', c', hlt', himg⟩ := (HPoint.isLine_iff L).1 hL
  have hA' : A.z ∈ hline α' c' := by rw [← himg]; exact Set.mem_image_of_mem _ hAL
  have hB' : B.z ∈ hline α' c' := by rw [← himg]; exact Set.mem_image_of_mem _ hBL
  apply Set.image_injective.mpr HPoint.z_injective
  rw [himg, HPoint.image_z_hlineSet, huniq α' c' hlt' hA' hB']

theorem hneutral_axiomIIIa (O A : HPoint) (hA : A ≠ O) (α : Real.Angle) :
    ∃ B : HPoint, B ≠ O ∧ hoangle A.z O.z B.z = α ∧
      ∀ B' : HPoint, B' ≠ O → hoangle A.z O.z B'.z = α → B' ∈ metricHalfLine O B := by
  have hAO : A.z ≠ O.z := fun h => hA (HPoint.ext h)
  obtain ⟨R, hR, hRO, hang⟩ := hoangle_exists O.norm_lt A.norm_lt hAO α
  have hBO : (⟨R, hR⟩ : HPoint) ≠ O := fun h => hRO (congrArg HPoint.z h)
  refine ⟨⟨R, hR⟩, hBO, hang, fun B' hB' hB'ang => ?_⟩
  have hB'O : B'.z ≠ O.z := fun h => hB' (HPoint.ext h)
  have := hoangle_unique O.norm_lt A.norm_lt hR B'.norm_lt hAO hRO hB'O
    (hang.trans hB'ang.symm)
  rw [HPoint.mem_metricHalfLine_iff hBO]
  show B'.z ∈ hray O.z R
  rw [← this]
  exact ⟨B'.norm_lt, 1, zero_le_one, by simp⟩

theorem hneutral_axiomIIIb (O A B C : HPoint) (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O) :
    hoangle A.z O.z B.z + hoangle B.z O.z C.z = hoangle A.z O.z C.z :=
  hoangle_add O.norm_lt A.norm_lt B.norm_lt C.norm_lt (fun h => hA (HPoint.ext h))
    (fun h => hB (HPoint.ext h)) (fun h => hC (HPoint.ext h))

theorem isOpen_hNondeg : IsOpen HNondeg := by
  have h1 : IsOpen {p : ℂ × ℂ × ℂ | ‖p.1‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {p : ℂ × ℂ × ℂ | ‖p.2.1‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {p : ℂ × ℂ × ℂ | ‖p.2.2‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  have h4 : IsOpen {p : ℂ × ℂ × ℂ | p.1 ≠ p.2.1} := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have h5 : IsOpen {p : ℂ × ℂ × ℂ | p.2.2 ≠ p.2.1} := isOpen_ne_fun (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

theorem hneutral_axiomIIIc (A O B : HPoint) (hA : A ≠ O) (hB : B ≠ O) :
    ContinuousAt (fun x : HPoint × HPoint × HPoint => hoangle x.1.z x.2.1.z x.2.2.z) (A, O, B) := by
  have hmem : (A.z, O.z, B.z) ∈ HNondeg :=
    ⟨A.norm_lt, O.norm_lt, B.norm_lt, fun h => hA (HPoint.ext h), fun h => hB (HPoint.ext h)⟩
  have hc := continuousOn_hoangle.continuousAt (isOpen_hNondeg.mem_nhds hmem)
  have hZ : Continuous fun x : HPoint × HPoint × HPoint => (x.1.z, x.2.1.z, x.2.2.z) := by
    have := HPoint.continuous_z
    fun_prop
  exact ContinuousAt.comp (x := (A, O, B))
    (f := fun x : HPoint × HPoint × HPoint => (x.1.z, x.2.1.z, x.2.2.z)) hc hZ.continuousAt

/-! ### Axiom IV -/

theorem hdist_congr_norm {a b c d : ℂ} (h1 : ‖a - b‖ = ‖c - d‖) (h2 : ‖a‖ = ‖c‖)
    (h3 : ‖b‖ = ‖d‖) : hdist a b = hdist c d := by
  unfold hdist hcosh
  rw [h1, h2, h3]

theorem hnorm_T' {T T' : ℂ → ℂ} (hT : ∀ z, ‖T z‖ = ‖z‖) (hr : ∀ z, T (T' z) = z) (z : ℂ) :
    ‖T' z‖ = ‖z‖ := by
  rw [← hT (T' z), hr]

/-- A motion of the h-plane: move `Q` to the centre, apply a norm-preserving map `T` of `ℂ` (a rotation
possibly composed with a reflection), and move the centre to `Q'`. -/
noncomputable def hMotionEquiv (Q Q' : HPoint) (T T' : ℂ → ℂ) (hT : ∀ z, ‖T z‖ = ‖z‖)
    (hTd : ∀ x y, ‖T x - T y‖ = ‖x - y‖) (hl : ∀ z, T' (T z) = z) (hr : ∀ z, T (T' z) = z) :
    HPoint ≃ᵢ HPoint where
  toFun p := ⟨mobius (-Q'.z) (T (mobius Q.z p.z)), norm_mobius_lt_one (by simpa using Q'.norm_lt)
    (by rw [hT]; exact norm_mobius_lt_one Q.norm_lt p.norm_lt)⟩
  invFun p := ⟨mobius (-Q.z) (T' (mobius Q'.z p.z)), norm_mobius_lt_one (by simpa using Q.norm_lt)
    (by rw [hnorm_T' hT hr]; exact norm_mobius_lt_one Q'.norm_lt p.norm_lt)⟩
  left_inv := fun p => HPoint.ext (by
    show mobius (-Q.z) (T' (mobius Q'.z (mobius (-Q'.z) (T (mobius Q.z p.z))))) = p.z
    rw [mobius_mobius_neg Q'.norm_lt (by rw [hT]; exact norm_mobius_lt_one Q.norm_lt p.norm_lt), hl]
    exact mobius_neg_mobius Q.norm_lt p.norm_lt)
  right_inv := fun p => HPoint.ext (by
    show mobius (-Q'.z) (T (mobius Q.z (mobius (-Q.z) (T' (mobius Q'.z p.z))))) = p.z
    rw [mobius_mobius_neg Q.norm_lt (by
      rw [hnorm_T' hT hr]; exact norm_mobius_lt_one Q'.norm_lt p.norm_lt), hr]
    exact mobius_neg_mobius Q'.norm_lt p.norm_lt)
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    show hdist (mobius (-Q'.z) (T (mobius Q.z x.z))) (mobius (-Q'.z) (T (mobius Q.z y.z))) =
      hdist x.z y.z
    have hn : ‖-Q'.z‖ < 1 := by simpa using Q'.norm_lt
    have hx := norm_mobius_lt_one Q.norm_lt x.norm_lt
    have hy := norm_mobius_lt_one Q.norm_lt y.norm_lt
    rw [hdist_mobius hn (by rw [hT]; exact hx) (by rw [hT]; exact hy),
      hdist_congr_norm (c := mobius Q.z x.z) (d := mobius Q.z y.z) (hTd _ _) (hT _) (hT _),
      hdist_mobius Q.norm_lt x.norm_lt y.norm_lt]

theorem hangle_nonneg' (P Q R : ℂ) : 0 ≤ hangle P Q R := InnerProductGeometry.angle_nonneg _ _

theorem hangle_le_pi' (P Q R : ℂ) : hangle P Q R ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _

theorem hangle_eq_abs_toReal {P Q R : ℂ} (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (hR : ‖R‖ < 1)
    (hPQ : P ≠ Q) (hRQ : R ≠ Q) : hangle P Q R = |(hoangle R Q P).toReal| := by
  rw [hangle_eq_abs hQ hP hR hPQ hRQ]
  unfold hoangle
  rw [Real.Angle.toReal_coe_eq_self_iff.2 ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩]

theorem angle_eq_or_neg_of_abs (θ θ' : Real.Angle) (h : |θ'.toReal| = |θ.toReal|) :
    θ' = θ ∨ θ' = -θ := by
  rcases abs_eq_abs.1 h with h | h
  · left
    calc θ' = ((θ'.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal _).symm
      _ = θ := by rw [h, Real.Angle.coe_toReal]
  · right
    calc θ' = ((θ'.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal _).symm
      _ = -θ := by rw [h, Real.Angle.coe_neg, Real.Angle.coe_toReal]

theorem hangle_eq_of_sides {A B C A' B' C' : HPoint} (hAB : A ≠ B) (hAC : A ≠ C) (hAB' : A' ≠ B')
    (hAC' : A' ≠ C') (h1 : dist A' B' = dist A B) (h2 : dist A' C' = dist A C)
    (h3 : dist B' C' = dist B C) : hangle B'.z A'.z C'.z = hangle B.z A.z C.z := by
  have l := hlaw_cosines A.norm_lt B.norm_lt C.norm_lt (fun h => hAB (HPoint.ext h).symm)
    (fun h => hAC (HPoint.ext h).symm)
  have l' := hlaw_cosines A'.norm_lt B'.norm_lt C'.norm_lt (fun h => hAB' (HPoint.ext h).symm)
    (fun h => hAC' (HPoint.ext h).symm)
  simp only [← HPoint.dist_eq] at l l'
  rw [h1, h2, h3] at l'
  have hs1 : 0 < Real.sinh (dist A B) := Real.sinh_pos_iff.2 (dist_pos.2 hAB)
  have hs2 : 0 < Real.sinh (dist A C) := Real.sinh_pos_iff.2 (dist_pos.2 hAC)
  have key : Real.sinh (dist A B) * Real.sinh (dist A C) *
      (Real.cos (hangle B'.z A'.z C'.z) - Real.cos (hangle B.z A.z C.z)) = 0 := by
    linear_combination l' - l
  have hcos : Real.cos (hangle B'.z A'.z C'.z) = Real.cos (hangle B.z A.z C.z) := by
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h (mul_pos hs1 hs2).ne'
    · linarith
  exact Real.injOn_cos ⟨hangle_nonneg' _ _ _, hangle_le_pi' _ _ _⟩
    ⟨hangle_nonneg' _ _ _, hangle_le_pi' _ _ _⟩ hcos

/-- The h-motions `p ↦ mobius (-Q') (v · mobius Q p)`. -/
noncomputable def hRotMotion (Q Q' : HPoint) (v : ℂ) (hv : ‖v‖ = 1) : HPoint ≃ᵢ HPoint :=
  hMotionEquiv Q Q' (fun z => v * z) (fun z => conj v * z)
    (fun z => by rw [norm_mul, hv, one_mul])
    (fun x y => by rw [← mul_sub, norm_mul, hv, one_mul])
    (fun z => by rw [← mul_assoc, conj_mul_self_unit hv, one_mul])
    (fun z => by rw [← mul_assoc, mul_comm v, conj_mul_self_unit hv, one_mul])

/-- The h-motions `p ↦ mobius (-Q') (v · conj (mobius Q p))`. -/
noncomputable def hRotConjMotion (Q Q' : HPoint) (v : ℂ) (hv : ‖v‖ = 1) : HPoint ≃ᵢ HPoint :=
  hMotionEquiv Q Q' (fun z => v * conj z) (fun z => v * conj z)
    (fun z => by rw [norm_mul, hv, one_mul, Complex.norm_conj])
    (fun x y => by
      rw [← mul_sub, ← map_sub, norm_mul, hv, one_mul, Complex.norm_conj])
    (fun z => by
      simp only [map_mul, Complex.conj_conj]
      rw [← mul_assoc, mul_comm v, conj_mul_self_unit hv, one_mul])
    (fun z => by
      simp only [map_mul, Complex.conj_conj]
      rw [← mul_assoc, mul_comm v, conj_mul_self_unit hv, one_mul])

theorem hneutral_axiomIV (A B C A' B' C' : HPoint) (hAB : A ≠ B) (_hBC : B ≠ C) (hCA : C ≠ A)
    (hAB' : A' ≠ B') (_hBC' : B' ≠ C') (hCA' : C' ≠ A') :
    TriangleCongruent A B C A' B' C' ↔
      dist A' B' = dist A B ∧ dist A' C' = dist A C ∧
        (hoangle C'.z A'.z B'.z = hoangle C.z A.z B.z ∨
          hoangle C'.z A'.z B'.z = -hoangle C.z A.z B.z) := by
  have nB : B.z ≠ A.z := fun h => hAB (HPoint.ext h).symm
  have nC : C.z ≠ A.z := fun h => hCA (HPoint.ext h)
  have nB' : B'.z ≠ A'.z := fun h => hAB' (HPoint.ext h).symm
  have nC' : C'.z ≠ A'.z := fun h => hCA' (HPoint.ext h)
  have hAC : A ≠ C := hCA.symm
  have hAC' : A' ≠ C' := hCA'.symm
  constructor
  · rintro ⟨f, hfA, hfB, hfC⟩
    subst hfA hfB hfC
    have d1 : dist (f A) (f B) = dist A B := f.dist_eq A B
    have d2 : dist (f A) (f C) = dist A C := f.dist_eq A C
    have d3 : dist (f B) (f C) = dist B C := f.dist_eq B C
    have hang := hangle_eq_of_sides hAB hAC hAB' hAC' d1 d2 d3
    rw [hangle_eq_abs_toReal (f A).norm_lt (f B).norm_lt (f C).norm_lt nB' nC',
      hangle_eq_abs_toReal A.norm_lt B.norm_lt C.norm_lt nB nC] at hang
    exact ⟨d1, d2, angle_eq_or_neg_of_abs _ _ hang⟩
  · rintro ⟨h1, h2, h3⟩
    have hang : hangle B.z A.z C.z = hangle B'.z A'.z C'.z := by
      rw [hangle_eq_abs_toReal A.norm_lt B.norm_lt C.norm_lt nB nC,
        hangle_eq_abs_toReal A'.norm_lt B'.norm_lt C'.norm_lt nB' nC']
      rcases h3 with h | h
      · rw [h]
      · rw [h, Real.Angle.abs_toReal_neg]
    obtain ⟨-, v, hv, hcase⟩ := hsas B.norm_lt A.norm_lt C.norm_lt B'.norm_lt A'.norm_lt C'.norm_lt
      nB nC nB' nC' h1.symm h2.symm hang
    rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · exact ⟨hRotMotion A A' v hv, HPoint.ext e1, HPoint.ext e2, HPoint.ext e3⟩
    · exact ⟨hRotConjMotion A A' v hv, HPoint.ext e1, HPoint.ext e2, HPoint.ext e3⟩

/-! ### Axiom h-V -/

theorem hneutral_axiomHV : ∀ ℓ : Set HPoint, IsLine ℓ → ∀ Q : HPoint, Q ∉ ℓ →
    ∃ m m' : Set HPoint, m ≠ m' ∧ IsLine.ParallelThrough ℓ m Q ∧ IsLine.ParallelThrough ℓ m' Q := by
  intro ℓ hℓ Q hQ
  obtain ⟨α, c, hlt, himg⟩ := (HPoint.isLine_iff ℓ).1 hℓ
  have hQn : Q.z ∉ hline α c := by
    intro h
    rw [← himg] at h
    obtain ⟨p, hp, hpq⟩ := h
    have := HPoint.ext hpq
    rw [this] at hp
    exact hQ hp
  obtain ⟨α₁, α₂, c₁, c₂, h1, h2, hP1, hP2, hd1, hd2, hne⟩ :=
    hV_exists_two_parallels_general hlt Q.norm_lt hQn
  have par : ∀ (α' : ℝ) (c' : ℂ), α' ^ 2 < ‖c'‖ ^ 2 → Q.z ∈ hline α' c' →
      Disjoint (hline α' c') (hline α c) →
      IsLine.ParallelThrough ℓ (HPoint.hlineSet α' c') Q := by
    intro α' c' h hq hd
    refine ⟨(HPoint.isLine_iff _).2 ⟨α', c', h, HPoint.image_z_hlineSet _ _⟩, hq, ?_⟩
    rw [Set.disjoint_left]
    intro p hpℓ hpm
    refine Set.disjoint_left.1 hd hpm ?_
    rw [← himg]
    exact ⟨p, hpℓ, rfl⟩
  refine ⟨HPoint.hlineSet α₁ c₁, HPoint.hlineSet α₂ c₂, ?_, par _ _ h1 hP1 hd1,
    par _ _ h2 hP2 hd2⟩
  intro h
  apply hne
  rw [← HPoint.image_z_hlineSet α₁ c₁, ← HPoint.image_z_hlineSet α₂ c₂, h]

/-! ### The neutral plane -/

/-- **Beltrami's model (Theorem 11.17, 'if' part, p. 89).**  The h-plane (the conformal disc model, built
inside the Euclidean plane `ℂ`) is a neutral plane: it satisfies Axioms I-IV, with the angle measure
`hoangle`.  By `hyperbolicNeutralPlane_axiomHV` it also satisfies Axiom h-V, so it is a hyperbolic plane, and by
`hyperbolicNeutralPlane_not_axiomV` it is not Euclidean (this is GE-167, an example of a neutral plane that is
not Euclidean). -/
@[kb "petrunin2025" "Theorem 11.17, p. 89"]
noncomputable def hyperbolicNeutralPlane : NeutralPlane HPoint where
  angle A O B := hoangle A.z O.z B.z
  axiomI := ⟨HPoint.center, ⟨(1 / 2 : ℂ), by norm_num⟩, fun h => by
    have := congrArg HPoint.z h
    simp [HPoint.center] at this⟩
  axiomII := hneutral_axiomII
  axiomIIIa := hneutral_axiomIIIa
  axiomIIIb := hneutral_axiomIIIb
  axiomIIIc := fun A O B hA hB _ => hneutral_axiomIIIc A O B hA hB
  axiomIV := hneutral_axiomIV

/-- **Axiom h-V holds in the h-plane** (Theorem 11.17, 'if' part, p. 89; Claim 12.20): through a point off a
line there are two distinct lines that do not meet it. -/
@[kb "petrunin2025" "Theorem 11.17, p. 89"]
theorem hyperbolicNeutralPlane_axiomHV : hyperbolicNeutralPlane.AxiomHV := hneutral_axiomHV

/-! ### Axiom V fails -/

theorem tanh_half_pos {r : ℝ} (hr : 0 < r) : 0 < Real.tanh (r / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 (by linarith)) (Real.cosh_pos _)

/-- The point at h-distance `r` from the centre on the positive real axis. -/
noncomputable def hxr (r : ℝ) : HPoint := ⟨((Real.tanh (r / 2) : ℝ) : ℂ), norm_tanh_lt r⟩

/-- The point at h-distance `r` from the centre on the positive imaginary axis. -/
noncomputable def hyr (r : ℝ) : HPoint :=
  ⟨Complex.I * ((Real.tanh (r / 2) : ℝ) : ℂ), by
    rw [norm_mul, Complex.norm_I, one_mul]; exact norm_tanh_lt r⟩

theorem dist_center_hxr {r : ℝ} (hr : 0 ≤ r) : dist HPoint.center (hxr r) = r := by
  have := hdist_tanh 0 r
  have h0 : HPoint.center.z = ((Real.tanh (0 / 2) : ℝ) : ℂ) := by simp [HPoint.center]
  rw [HPoint.dist_eq, h0]
  exact this.trans (by rw [zero_sub, abs_neg, abs_of_nonneg hr])

theorem dist_center_hyr {r : ℝ} (hr : 0 ≤ r) : dist HPoint.center (hyr r) = r := by
  have h := hdist_rot Complex.norm_I 0 ((Real.tanh (r / 2) : ℝ) : ℂ)
  rw [mul_zero] at h
  calc dist HPoint.center (hyr r) = dist HPoint.center (hxr r) := h
    _ = r := dist_center_hxr hr

theorem mobius_zero_left (z : ℂ) : mobius 0 z = z := by simp [mobius]

theorem inner_real_I (T : ℝ) : inner ℝ (T : ℂ) (Complex.I * (T : ℂ)) = 0 := by
  rw [Complex.inner]; simp

theorem hray_scale (v : ℂ) {T U : ℝ} (hT : 0 < T) :
    mobius 0 (v * (U : ℂ)) = ((U / T : ℝ) : ℂ) * mobius 0 (v * (T : ℂ)) := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [mobius_zero_left, mobius_zero_left]
  push_cast
  field_simp

theorem real_ne_I_mul (T : ℝ) (h : T ≠ 0) : (T : ℂ) ≠ Complex.I * (T : ℂ) := by
  intro e
  have := congrArg Complex.re e
  simp at this
  exact h this

theorem cosh_dist_hxr_hyr {r : ℝ} (hr : 0 < r) :
    Real.cosh (dist (hxr r) (hyr r)) = Real.cosh r ^ 2 := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hB : (hxr r).z ≠ 0 := by
    have := tanh_half_pos hr
    show ((Real.tanh (r / 2) : ℝ) : ℂ) ≠ 0
    exact_mod_cast this.ne'
  have hC : (hyr r).z ≠ 0 := by
    have := tanh_half_pos hr
    show Complex.I * ((Real.tanh (r / 2) : ℝ) : ℂ) ≠ 0
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast this.ne')
  have l := hlaw_cosines h0 (hxr r).norm_lt (hyr r).norm_lt hB hC
  have e1 : hdist 0 (hxr r).z = r := dist_center_hxr hr.le
  have e2 : hdist 0 (hyr r).z = r := dist_center_hyr hr.le
  have hang : hangle (hxr r).z 0 (hyr r).z = Real.pi / 2 := by
    unfold hangle
    rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, mobius_zero_left,
      mobius_zero_left]
    exact inner_real_I _
  rw [e1, e2, hang, Real.cos_pi_div_two] at l
  rw [HPoint.dist_eq, l]
  ring

/-- **Axiom V fails in the h-plane** (Chapter 11): the neutral plane `hyperbolicNeutralPlane` is not
Euclidean.  Scaling the two sides of a right-angled triangle at the centre by `2` does not scale the third
side by `2`. -/
@[kb "petrunin2025" "Chapter 11, p. 83"]
theorem hyperbolicNeutralPlane_not_axiomV : ¬ hyperbolicNeutralPlane.AxiomV := by
  intro hV
  have p1 := tanh_half_pos (r := 1) one_pos
  have p2 := tanh_half_pos (r := 2) two_pos
  have hne : ∀ r : ℝ, 0 < r → hxr r ≠ HPoint.center := by
    intro r hr h
    have := congrArg HPoint.z h
    have h2 : ((Real.tanh (r / 2) : ℝ) : ℂ) = 0 := this
    exact (tanh_half_pos hr).ne' (by exact_mod_cast h2)
  have hney : ∀ r : ℝ, 0 < r → hyr r ≠ HPoint.center := by
    intro r hr h
    have := congrArg HPoint.z h
    have h2 : Complex.I * ((Real.tanh (r / 2) : ℝ) : ℂ) = 0 := this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact Complex.I_ne_zero h3
    · exact (tanh_half_pos hr).ne' (by exact_mod_cast h3)
  have hxy : hxr 1 ≠ hyr 1 := fun h =>
    real_ne_I_mul (Real.tanh (1 / 2)) p1.ne' (congrArg HPoint.z h)
  have hB' : hxr 2 ∈ metricHalfLine HPoint.center (hxr 1) := by
    rw [HPoint.mem_metricHalfLine_iff (hne 1 one_pos)]
    refine ⟨(hxr 2).norm_lt, Real.tanh (2 / 2) / Real.tanh (1 / 2), ?_, ?_⟩
    · exact div_nonneg p2.le p1.le
    · have := hray_scale 1 (U := Real.tanh (2 / 2)) p1
      simp only [one_mul] at this
      exact this
  have hC' : hyr 2 ∈ metricHalfLine HPoint.center (hyr 1) := by
    rw [HPoint.mem_metricHalfLine_iff (hney 1 one_pos)]
    refine ⟨(hyr 2).norm_lt, Real.tanh (2 / 2) / Real.tanh (1 / 2), ?_, ?_⟩
    · exact div_nonneg p2.le p1.le
    · exact hray_scale Complex.I (U := Real.tanh (2 / 2)) p1
  obtain ⟨h, -⟩ := hV HPoint.center (hxr 1) (hyr 1) (hxr 2) (hyr 2) 2 two_pos
    (hne 1 one_pos).symm (hney 1 one_pos).symm hxy hB' hC'
    (by rw [dist_center_hxr (by norm_num), dist_center_hxr (by norm_num)]; norm_num)
    (by rw [dist_center_hyr (by norm_num), dist_center_hyr (by norm_num)]; norm_num)
  have c1 := cosh_dist_hxr_hyr (r := 1) one_pos
  have c2 := cosh_dist_hxr_hyr (r := 2) two_pos
  rw [h] at c2
  have d1 := Real.cosh_two_mul (dist (hxr 1) (hyr 1))
  have d2 := Real.cosh_two_mul (1 : ℝ)
  rw [mul_one] at d2
  have s1 := Real.cosh_sq (dist (hxr 1) (hyr 1))
  have s2 := Real.cosh_sq (1 : ℝ)
  have hx : 1 < Real.cosh 1 := Real.one_lt_cosh.2 one_ne_zero
  have e1 : Real.cosh (2 * dist (hxr 1) (hyr 1)) = 2 * Real.cosh (dist (hxr 1) (hyr 1)) ^ 2 - 1 := by
    linarith
  have e2 : Real.cosh 2 = 2 * Real.cosh 1 ^ 2 - 1 := by linarith
  rw [e1, e2, c1] at c2
  have : (Real.cosh 1 ^ 2 - 1) ^ 2 = 0 := by
    linear_combination (-1 / 2) * c2
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  nlinarith

end UndergradKB.Geometry
