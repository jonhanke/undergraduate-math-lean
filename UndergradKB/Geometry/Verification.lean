import UndergradKB.Common.Attr
import UndergradKB.Geometry.CentreVerification

/-! # Verification procedures: the centre of a circle cannot be verified (Petrunin, Theorem 19.18, p. 163
and Problem 19.16, pp. 162-163)

`CentreVerification` proves that constructions are carried to constructions by a symmetry of the given
circle `Γ` that moves the centre.  Here we add a formal notion of a *verification procedure* and derive
the statements as the book phrases them: no procedure verifies that a given point is the centre of `Γ`.

A *ruler procedure* (`RProc`) is a finite list of steps over a numbered list of projective points (the
tested point `P` first, then finitely many free points chosen arbitrarily): a step meets two lines
spanned by earlier points, or meets such a line with `Γ`.  Steps are relations (`RStep.Out`), so the
choice of intersection point is uniformly nondeterministic, and a run may be undefined.  The answer is an
atomic test on the final list: two points coincide, or a point lies on a line spanned by two others.

A procedure *verifies* the centre (`RProc.Verifies`) in the book's sense: for every tested point `P` there
is a dense open set `G` of general positions of the `n` free points (product topology) such that, for free
points in `G`, a run exists and every run answers "yes" iff `P` is the centre.  The proof meets the dense
open sets for the centre and for its image under the boost (`exists_generic`).

The same is done for a circumtool and an inversor (`CIProc`) in the inversive plane, with free points
ordinary points of the plane (so that the inversion in the orthogonal circle, a homeomorphism off its
centre, transports general positions).  The inversor is the genuine tool (`IsInvOf`): the inversion
`inversionOP Q s` in a circle (centre and `∞` exchanged), and the reflection in a line (a perpendicular
bisector, fixing `∞`).  The key new fact is `IsInvOf.conj`, Corollary 10.26 in all cases and with all
`∞`/centre conventions: the inversion in `Ω` conjugates the inversion in any circline `C` to the inversion
in the circline `Ω(C)` (circle not through the centre, `conjA`; circle through it, `conjB`; line through
it, `conjC`; line not through it, `conjD`, derived from `conjB`).  Lines are represented as perpendicular
bisectors `perpBisector A B` (every line of the plane is one).
-/

namespace UndergradKB.Geometry

namespace CentreVerification

namespace Verif

/-! ### Ruler procedures -/

/-- A step of a ruler procedure, referring to earlier points by their numbers. -/
inductive RStep
  | lineLine (i j k l : ℕ)
  | lineCircle (i j : ℕ)

/-- `x` is a possible outcome of the step `s` applied to the list `pts` of constructed points. -/
def RStep.Out (pts : List V3) : RStep → V3 → Prop
  | .lineLine i j k l, x => ∃ p q p' q', pts[i]? = some p ∧ pts[j]? = some q ∧ pts[k]? = some p' ∧
      pts[l]? = some q' ∧ LinearIndependent ℝ ![p, q] ∧ LinearIndependent ℝ ![p', q'] ∧
      Submodule.span ℝ {p, q} ≠ Submodule.span ℝ {p', q'} ∧ x ∈ Submodule.span ℝ {p, q} ∧
      x ∈ Submodule.span ℝ {p', q'} ∧ x ≠ 0
  | .lineCircle i j, x => ∃ p q, pts[i]? = some p ∧ pts[j]? = some q ∧ LinearIndependent ℝ ![p, q] ∧
      x ∈ Submodule.span ℝ {p, q} ∧ x ≠ 0 ∧ OnGamma x

/-- A run of a list of steps: each step appends one of its possible outcomes. -/
inductive RRun : List V3 → List RStep → List V3 → Prop
  | nil (pts : List V3) : RRun pts [] pts
  | cons {pts : List V3} {s : RStep} {x : V3} {rest : List RStep} {fin : List V3} :
      s.Out pts x → RRun (pts ++ [x]) rest fin → RRun pts (s :: rest) fin

/-- Atomic tests: two points coincide (projectively), or a point lies on a line spanned by two others. -/
inductive RTest
  | same (i j : ℕ)
  | incident (i j k : ℕ)

/-- The test holds on the list of points. -/
def RTest.Holds (pts : List V3) : RTest → Prop
  | .same i j => ∃ p q, pts[i]? = some p ∧ pts[j]? = some q ∧ ∃ c : ℝ, c ≠ 0 ∧ p = c • q
  | .incident i j k => ∃ p q r, pts[i]? = some p ∧ pts[j]? = some q ∧ pts[k]? = some r ∧
      LinearIndependent ℝ ![q, r] ∧ p ∈ Submodule.span ℝ {q, r}

/-- A ruler procedure: `n` free points (arbitrary choices), finitely many steps and a final atomic test. -/
structure RProc where
  n : ℕ
  steps : List RStep
  test : RTest

/-- `T` verifies the centre of `Γ` (the circle `x₀² + x₁² = x₂²`, centre `(0,0,1)`), in the book's sense:
for every tested point `P ≠ 0` the free points are only required to be in general position, i.e. to lie
in some dense open set `G` of `(ℝ³)ⁿ` (product topology); for free points in `G` the run is defined, and
every run answers "yes" exactly when `P` is (projectively) the centre. -/
def RProc.Verifies (T : RProc) : Prop :=
  ∀ P : V3, P ≠ 0 → ∃ G : Set (Fin T.n → V3), IsOpen G ∧ Dense G ∧ ∀ free ∈ G,
    (∃ fin, RRun (P :: List.ofFn free) T.steps fin) ∧
    ∀ fin, RRun (P :: List.ofFn free) T.steps fin →
      (T.test.Holds fin ↔ ∃ c : ℝ, c ≠ 0 ∧ P = c • centre)

/-- Transport of dense open sets of general positions along a bijection `φ` with inverse `ψ` on an open
dense set `U`. -/
theorem dense_inter_preimage {X : Type*} [TopologicalSpace X] {U : Set X} (hUo : IsOpen U)
    (hUd : Dense U) {φ ψ : X → X} (hψ : ContinuousOn ψ U) (hφU : ∀ x ∈ U, φ x ∈ U)
    (hψφ : ∀ x ∈ U, ψ (φ x) = x) (hφψ : ∀ x ∈ U, φ (ψ x) = x) {G : Set X} (hG : Dense G) :
    Dense (U ∩ φ ⁻¹' G) := by
  rw [dense_iff_inter_open]
  intro W hW hne
  obtain ⟨w, hwW, hwU⟩ := (dense_iff_inter_open.1 hUd) W hW hne
  have hop : IsOpen (U ∩ ψ ⁻¹' (W ∩ U)) := hψ.isOpen_inter_preimage hUo (hW.inter hUo)
  have hne2 : (U ∩ ψ ⁻¹' (W ∩ U)).Nonempty :=
    ⟨φ w, hφU w hwU, by rw [Set.mem_preimage, hψφ w hwU]; exact ⟨hwW, hwU⟩⟩
  obtain ⟨v, hv, hvG⟩ := (dense_iff_inter_open.1 hG) _ hop hne2
  refine ⟨ψ v, hv.2.1, ?_, ?_⟩
  · exact hv.2.2
  · show φ (ψ v) ∈ G
    rw [hφψ v hv.1]; exact hvG

/-- Two dense open sets of general positions can be met simultaneously after applying `φ`. -/
theorem exists_generic {X : Type*} [TopologicalSpace X] [Nonempty X] {U : Set X} (hUo : IsOpen U)
    (hUd : Dense U) {φ ψ : X → X} (hφ : ContinuousOn φ U) (hψ : ContinuousOn ψ U)
    (hφU : ∀ x ∈ U, φ x ∈ U) (hψφ : ∀ x ∈ U, ψ (φ x) = x) (hφψ : ∀ x ∈ U, φ (ψ x) = x)
    {G₁ G₂ : Set X} (h₁o : IsOpen G₁) (h₁d : Dense G₁) (h₂o : IsOpen G₂) (h₂d : Dense G₂) :
    ∃ x, x ∈ G₁ ∧ x ∈ U ∧ φ x ∈ G₂ := by
  have hd := dense_inter_preimage hUo hUd hψ hφU hψφ hφψ h₂d
  obtain ⟨x, hx1, hx2, hx3⟩ := (h₁d.inter_of_isOpen_left hd h₁o).nonempty
  exact ⟨x, hx1, hx2, hx3⟩

section Map

variable (M : V3 ≃ₗ[ℝ] V3)

theorem span_map (p q : V3) :
    Submodule.map (M : V3 →ₗ[ℝ] V3) (Submodule.span ℝ {p, q}) = Submodule.span ℝ {M p, M q} := by
  rw [Submodule.map_span, Set.image_pair]; rfl

theorem mem_span_map {p q y : V3} (h : y ∈ Submodule.span ℝ {p, q}) :
    M y ∈ Submodule.span ℝ {M p, M q} := by
  rw [← span_map]; exact Submodule.mem_map_of_mem h

theorem li_map {p q : V3} (h : LinearIndependent ℝ ![p, q]) : LinearIndependent ℝ ![M p, M q] := by
  have := h.map' (M : V3 →ₗ[ℝ] V3) (LinearEquiv.ker M)
  convert this using 1
  ext i : 1
  fin_cases i <;> rfl

theorem RStep.Out.map (hM : ∀ v, OnGamma (M v) ↔ OnGamma v) {pts : List V3} {s : RStep} {x : V3}
    (h : s.Out pts x) : s.Out (pts.map M) (M x) := by
  cases s with
  | lineLine i j k l =>
    obtain ⟨p, q, p', q', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    refine ⟨M p, M q, M p', M q', by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      li_map M h5, li_map M h6, ?_, mem_span_map M h8, mem_span_map M h9, by simpa using h10⟩
    intro hh
    apply h7
    rw [← span_map, ← span_map] at hh
    exact Submodule.map_injective_of_injective M.injective hh
  | lineCircle i j =>
    obtain ⟨p, q, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨M p, M q, by simp [h1], by simp [h2], li_map M h3, mem_span_map M h4, by simpa using h5,
      (hM x).2 h6⟩

theorem RRun.map (hM : ∀ v, OnGamma (M v) ↔ OnGamma v) {pts : List V3} {steps : List RStep}
    {fin : List V3} (h : RRun pts steps fin) : RRun (pts.map M) steps (fin.map M) := by
  induction h with
  | nil pts => exact .nil _
  | cons hs _ ih =>
    refine .cons (hs.map M hM) ?_
    simpa using ih

theorem RTest.Holds.map {pts : List V3} {t : RTest} (h : t.Holds pts) : t.Holds (pts.map M) := by
  cases t with
  | same i j =>
    obtain ⟨p, q, h1, h2, c, hc, h3⟩ := h
    exact ⟨M p, M q, by simp [h1], by simp [h2], c, hc, by rw [h3, map_smul]⟩
  | incident i j k =>
    obtain ⟨p, q, r, h1, h2, h3, h4, h5⟩ := h
    exact ⟨M p, M q, M r, by simp [h1], by simp [h2], by simp [h3], li_map M h4, mem_span_map M h5⟩

end Map

/-- **Theorem 19.18, p. 163.**  No ruler procedure verifies that a given point is the centre of a given
circle: if it were sound and applicable on the centre, the boost `M` of `CentreVerification`, which
preserves the circle and commutes with runs and tests, would turn an accepting run on the centre into an
accepting run on the point `M Z`, which is not the centre. -/
@[kb "petrunin2025" "Theorem 19.18, p. 163"]
theorem no_ruler_verifies_centre (T : RProc) : ¬ T.Verifies := by
  intro hv
  have hcen : centre ≠ 0 := by
    intro h; have := congrFun h 2; simp [centre] at this
  obtain ⟨G₁, h₁o, h₁d, h₁⟩ := hv centre hcen
  obtain ⟨G₂, h₂o, h₂d, h₂⟩ := hv (boost centre) (by simpa using hcen)
  have hc : ∀ f : LinearEquiv (RingHom.id ℝ) V3 V3, Continuous f := fun f =>
    LinearMap.continuous_of_finiteDimensional (f : V3 →ₗ[ℝ] V3)
  have hcont : ∀ f : LinearEquiv (RingHom.id ℝ) V3 V3,
      Continuous (fun (free : Fin T.n → V3) i => f (free i)) := fun f =>
    continuous_pi fun i => (hc f).comp (continuous_apply i)
  obtain ⟨free, hf1, -, hf2⟩ := exists_generic (U := Set.univ) (X := Fin T.n → V3) isOpen_univ
    dense_univ (φ := fun free i => boost (free i)) (ψ := fun free i => boost.symm (free i))
    (hcont boost).continuousOn (hcont boost.symm).continuousOn (fun _ _ => trivial)
    (fun x _ => by ext i; simp) (fun x _ => by ext i; simp) h₁o h₁d h₂o h₂d
  obtain ⟨⟨fin, hrun⟩, hs⟩ := h₁ free hf1
  have h1 : T.test.Holds fin := (hs fin hrun).2 ⟨1, one_ne_zero, by simp⟩
  have h2 := hrun.map boost onGamma_boost
  have h2' : RRun (boost centre :: List.ofFn fun i => boost (free i)) T.steps (fin.map boost) := by
    simpa [List.map_ofFn, Function.comp_def] using h2
  obtain ⟨c, hc, hcc⟩ := ((h₂ _ hf2).2 _ h2').1 (RTest.Holds.map boost h1)
  exact centre_ne_boost ⟨c, hcc⟩

section GenuineInv

open EuclideanGeometry
open scoped RealInnerProductSpace OnePoint

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem inversion_vsub' (c : P) (R : ℝ) (x : P) :
    inversion c R x -ᵥ c = (R ^ 2 / ‖x -ᵥ c‖ ^ 2) • (x -ᵥ c) := by
  rw [inversion_vsub_center, dist_eq_norm_vsub V, div_pow]

theorem norm_sq_smul' (t : ℝ) (u : V) : ‖t • u‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem invSphereCenter_vsub (O S : P) (R s : ℝ) :
    invSphereCenter O R S s -ᵥ O = (R ^ 2 / (‖S -ᵥ O‖ ^ 2 - s ^ 2)) • (S -ᵥ O) := by
  simp only [invSphereCenter, AffineMap.lineMap_vsub_left, dist_eq_norm_vsub V S O]

theorem invSphereRadius_sq (O S : P) (R s : ℝ) :
    invSphereRadius O R S s ^ 2 = (R ^ 2 * s) ^ 2 / (‖S -ᵥ O‖ ^ 2 - s ^ 2) ^ 2 := by
  simp only [invSphereRadius, dist_eq_norm_vsub V S O, div_pow, sq_abs]

/-- The image of the point at infinity of the plane under the inversion in the image circle. -/
theorem conjA_infty {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O ≠ s)
    (hSO : S ≠ O) :
    inversion (invSphereCenter O R S s) (invSphereRadius O R S s) O = inversion O R S := by
  have hD := power_ne_zero hs.le hd
  have hdu : dist S O = ‖S -ᵥ O‖ := dist_eq_norm_vsub V _ _
  rw [hdu] at hD
  have hu0 : ‖S -ᵥ O‖ ≠ 0 := by rw [← hdu]; exact dist_ne_zero.mpr hSO
  have hk : R ^ 2 / (‖S -ᵥ O‖ ^ 2 - s ^ 2) ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) hD
  apply vsub_left_cancel (p := O)
  rw [← vsub_add_vsub_cancel (inversion (invSphereCenter O R S s) (invSphereRadius O R S s) O)
    (invSphereCenter O R S s) O, inversion_vsub', ← neg_vsub_eq_vsub_rev (invSphereCenter O R S s) O,
    invSphereCenter_vsub, norm_neg, norm_smul, inversion_vsub' O R S, invSphereRadius_sq]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  generalize ‖S -ᵥ O‖ = d at *
  generalize S -ᵥ O = u
  match_scalars <;> field_simp <;> ring

theorem inversion_vsub_self_centre (O S : P) (s : ℝ) (hSO : S ≠ O) :
    inversion S s O -ᵥ O = (1 - s ^ 2 / ‖S -ᵥ O‖ ^ 2) • (S -ᵥ O) := by
  rw [← vsub_add_vsub_cancel (inversion S s O) S O, inversion_vsub', ← neg_vsub_eq_vsub_rev S O,
    norm_neg]
  module

theorem conjA_centre {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O ≠ s)
    (hSO : S ≠ O) :
    inversion O R (inversion S s O) = invSphereCenter O R S s := by
  have hD := power_ne_zero hs.le hd
  have hdu : dist S O = ‖S -ᵥ O‖ := dist_eq_norm_vsub V _ _
  rw [hdu] at hD
  have hu0 : ‖S -ᵥ O‖ ≠ 0 := by rw [← hdu]; exact dist_ne_zero.mpr hSO
  apply vsub_left_cancel (p := O)
  rw [inversion_vsub', inversion_vsub_self_centre O S s hSO, invSphereCenter_vsub, norm_smul]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  generalize ‖S -ᵥ O‖ = d at *
  generalize S -ᵥ O = u
  match_scalars
  field_simp

theorem invSphereCenter_ne {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O ≠ s)
    (hSO : S ≠ O) : invSphereCenter O R S s ≠ O := by
  intro h
  have hD := power_ne_zero hs.le hd
  have h1 := invSphereCenter_vsub O S R s
  rw [h, vsub_self] at h1
  rw [dist_eq_norm_vsub V S O] at hD
  have : R ^ 2 / (‖S -ᵥ O‖ ^ 2 - s ^ 2) = 0 ∨ S -ᵥ O = 0 := smul_eq_zero.mp h1.symm
  rcases this with h2 | h2
  · exact div_ne_zero (pow_ne_zero 2 hR) hD h2
  · exact hSO (vsub_eq_zero_iff_eq.mp h2)

theorem invSphereCenter_self (O : P) (R s : ℝ) : invSphereCenter O R O s = O := by
  simp [invSphereCenter]

theorem invSphereRadius_pos {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O ≠ s) :
    0 < invSphereRadius O R S s := by
  have hD := power_ne_zero hs.le hd
  unfold invSphereRadius
  have : 0 < |dist S O ^ 2 - s ^ 2| := abs_pos.mpr hD
  positivity

theorem inversion_ne_self_of_dist_ne {O S : P} {s : ℝ} (hs : 0 < s) (hd : dist S O ≠ s)
    (hSO : S ≠ O) : inversion S s O ≠ O := by
  intro h
  have h1 := dist_inversion_center S O s
  rw [h, dist_comm] at h1
  have hp : 0 < dist S O := dist_pos.mpr hSO
  field_simp at h1
  exact hd ((sq_eq_sq₀ dist_nonneg hs.le).1 (by linarith))

/-- **Conjugation, circle not through the centre of the inversion.** -/
theorem conjA {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O ≠ s) (z : OnePoint P) :
    inversionOP (invSphereCenter O R S s) (invSphereRadius O R S s) (inversionOP O R z) =
      inversionOP O R (inversionOP S s z) := by
  have hs' := invSphereRadius_pos hR hs hd
  induction z using OnePoint.rec with
  | infty =>
    simp only [inversionOP_infty]
    by_cases hSO : S = O
    · subst hSO; simp [invSphereCenter_self]
    · have hQ := invSphereCenter_ne hR hs hd hSO
      rw [inversionOP_coe_of_ne hQ.symm, inversionOP_coe_of_ne hSO, conjA_infty hR hs hd hSO]
  | coe x =>
    by_cases hxO : x = O
    · rw [hxO]
      simp only [inversionOP_center, inversionOP_infty]
      by_cases hSO : S = O
      · subst hSO; simp [invSphereCenter_self]
      · rw [inversionOP_coe_of_ne (Ne.symm hSO),
          inversionOP_coe_of_ne (inversion_ne_self_of_dist_ne hs hd hSO),
          conjA_centre hR hs hd hSO]
    · by_cases hxS : x = S
      · rw [hxS]
        have hSO : S ≠ O := hxS ▸ hxO
        have hQ := invSphereCenter_ne hR hs hd hSO
        have h1 := conjA_infty hR hs hd hSO
        have h2 : inversion O R S ≠ invSphereCenter O R S s := by
          intro h; rw [h, inversion_eq_center hs'.ne'] at h1
          exact hQ h1.symm
        have h3 : inversion (invSphereCenter O R S s) (invSphereRadius O R S s) (inversion O R S) = O := by
          rw [← h1, inversion_inversion _ hs'.ne']
        rw [inversionOP_coe_of_ne hSO, inversionOP_coe_of_ne h2, h3]
        simp
      · rw [inversionOP_coe_of_ne hxO, inversionOP_coe_of_ne hxS]
        by_cases hw : inversion S s x = O
        · have hSO : S ≠ O := by
            rintro rfl
            exact hxO ((inversion_eq_center hs.ne').1 hw)
          have hxx : x = inversion S s O := by rw [← hw, inversion_inversion _ hs.ne']
          have hx' : inversion O R x = invSphereCenter O R S s := by rw [hxx, conjA_centre hR hs hd hSO]
          rw [hw, hx']
          simp
        · have hx0 : inversion O R x ≠ O := (inversion_eq_center hR).not.2 hxO
          have hxQ : inversion O R x ≠ invSphereCenter O R S s := by
            intro h
            have hSO : S ≠ O := by
              rintro rfl
              rw [invSphereCenter_self] at h
              exact hx0 h
            apply hw
            have : x = inversion S s O := by
              rw [← inversion_inversion O hR x, h, ← conjA_centre hR hs hd hSO, inversion_inversion _ hR]
            rw [this, inversion_inversion _ hs.ne']
          rw [inversionOP_coe_of_ne hxQ, inversionOP_coe_of_ne hw,
            inversion_inversion_conj hR hs.le hd hxO hxS hw]

/-- The reflection in the perpendicular bisector of `[A B]` (a line, in the plane), by the explicit
formula of `reflection_perpBisector_vsub`. -/
noncomputable def lineRefl (A B x : P) : P :=
  ((x -ᵥ A) - (2 * ⟪B -ᵥ A, x -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1) • (B -ᵥ A)) +ᵥ A

/-- The reflection in the line, extended to the inversive plane by fixing `∞`. -/
noncomputable def lineReflOP (A B : P) (z : OnePoint P) : OnePoint P :=
  z.elim OnePoint.infty (fun x => ((lineRefl A B x : P) : OnePoint P))

@[simp] theorem lineReflOP_infty (A B : P) : lineReflOP A B (OnePoint.infty : OnePoint P) = OnePoint.infty := rfl

@[simp] theorem lineReflOP_coe (A B x : P) : lineReflOP A B (x : OnePoint P) = ((lineRefl A B x : P) : OnePoint P) := rfl

theorem lineRefl_eq_reflection {A B : P} (hAB : A ≠ B) (x : P) :
    lineRefl A B x = EuclideanGeometry.reflection (AffineSubspace.perpBisector A B) x := by
  apply vsub_left_cancel (p := A)
  rw [reflection_perpBisector_vsub A B x hAB]
  exact vadd_vsub _ _

theorem lineRefl_vsub (A B x O : P) :
    lineRefl A B x -ᵥ O = (x -ᵥ O) - (2 * ⟪B -ᵥ A, x -ᵥ O⟫ / ‖B -ᵥ A‖ ^ 2 +
      (2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1)) • (B -ᵥ A) := by
  rw [← vsub_sub_vsub_cancel_right (lineRefl A B x) O A, lineRefl, vadd_vsub,
    ← vsub_add_vsub_cancel x O A, inner_add_right]
  module

theorem lineRefl_left (A B : P) : lineRefl A B A = B := by
  simp [lineRefl]

theorem lineRefl_right {A B : P} (hAB : A ≠ B) : lineRefl A B B = A := by
  have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖B -ᵥ A‖ ^ 2 ≠ 0 := by positivity
  apply vsub_left_cancel (p := A)
  rw [lineRefl, vadd_vsub, vsub_self, real_inner_self_eq_norm_sq]
  field_simp
  norm_num

theorem inversion_eq_self_of_dist {c x : P} {R : ℝ} (hR : 0 < R) (h : dist x c = R) :
    inversion c R x = x := by
  rw [inversion, h, div_self hR.ne']
  simp

/-- **Conjugation, circle through the centre of the inversion.** -/
theorem conjB {O S : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s) (hd : dist S O = s) (z : OnePoint P) :
    lineReflOP O (inversion O R S) (inversionOP O R z) = inversionOP O R (inversionOP S s z) := by
  have hSO : S ≠ O := fun h => by rw [h, dist_self] at hd; linarith
  have hOS : O ≠ inversion O R S := fun h => hSO (by simpa [inversion_eq_center hR] using h.symm)
  have hOfix : inversion S s O = O := inversion_eq_self_of_dist hs (by rw [dist_comm]; exact hd)
  induction z using OnePoint.rec with
  | infty =>
    simp only [inversionOP_infty, lineReflOP_coe, lineRefl_left]
    rw [inversionOP_coe_of_ne hSO]
  | coe x =>
    by_cases hxO : x = O
    · rw [hxO, inversionOP_coe_of_ne hSO.symm, hOfix]
      simp
    · by_cases hxS : x = S
      · rw [hxS]
        rw [inversionOP_coe_of_ne hSO]
        simp only [inversionOP_center, inversionOP_infty, lineReflOP_coe]
        rw [lineRefl_right hOS]
      · rw [inversionOP_coe_of_ne hxO, inversionOP_coe_of_ne hxS]
        have hw : inversion S s x ≠ O := by
          intro h
          apply hxO
          have := congrArg (inversion S s) h
          rwa [inversion_inversion _ hs.ne', hOfix] at this
        rw [inversionOP_coe_of_ne hw, lineReflOP_coe, lineRefl_eq_reflection hOS,
          reflection_inversion_through hR hs hd hxO hxS]

theorem inner_offset_zero_of_mem {A B O : P} (hAB : A ≠ B)
    (hO : O ∈ AffineSubspace.perpBisector A B) :
    2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1 = 0 := by
  have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖B -ᵥ A‖ ^ 2 ≠ 0 := by positivity
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero] at hO
  have h1 : O -ᵥ A = (O -ᵥ midpoint ℝ A B) + (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [← vsub_add_vsub_cancel O (midpoint ℝ A B) A, midpoint_vsub_left]
    simp
  rw [real_inner_comm] at hO
  rw [h1, inner_add_right, hO, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem lineRefl_vsub_of_mem {A B O : P} (hAB : A ≠ B) (hO : O ∈ AffineSubspace.perpBisector A B) (x : P) :
    lineRefl A B x -ᵥ O = (x -ᵥ O) - (2 * ⟪B -ᵥ A, x -ᵥ O⟫ / ‖B -ᵥ A‖ ^ 2) • (B -ᵥ A) := by
  rw [lineRefl_vsub, inner_offset_zero_of_mem hAB hO, add_zero]

theorem norm_reflect_sq (u w : V) :
    ‖w - (2 * ⟪u, w⟫ / ‖u‖ ^ 2) • u‖ ^ 2 = ‖w‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  have hu2 : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm]
  field_simp
  ring

/-- **Conjugation, line through the centre of the inversion.** -/
theorem conjC {A B O : P} {R : ℝ} (hR : R ≠ 0) (hAB : A ≠ B) (hO : O ∈ AffineSubspace.perpBisector A B)
    (z : OnePoint P) :
    lineReflOP A B (inversionOP O R z) = inversionOP O R (lineReflOP A B z) := by
  have hOfix : lineRefl A B O = O := by
    apply vsub_left_cancel (p := O)
    rw [lineRefl_vsub_of_mem hAB hO]; simp
  induction z using OnePoint.rec with
  | infty => simp [hOfix]
  | coe x =>
    by_cases hxO : x = O
    · subst hxO; simp [hOfix]
    · have hw : x -ᵥ O ≠ 0 := fun h => hxO (vsub_eq_zero_iff_eq.mp h)
      have hn : ‖x -ᵥ O‖ ^ 2 ≠ 0 := by positivity
      have hy : lineRefl A B x ≠ O := by
        intro h
        have := norm_reflect_sq (B -ᵥ A) (x -ᵥ O)
        rw [← lineRefl_vsub_of_mem hAB hO, h, vsub_self, norm_zero] at this
        apply hn; simpa using this.symm
      have hi : inversion O R x ≠ O := (inversion_eq_center hR).not.2 hxO
      rw [inversionOP_coe_of_ne hxO, lineReflOP_coe, lineReflOP_coe, inversionOP_coe_of_ne hy]
      norm_cast
      apply vsub_left_cancel (p := O)
      rw [lineRefl_vsub_of_mem hAB hO, inversion_vsub', inversion_vsub', lineRefl_vsub_of_mem hAB hO,
        ← lineRefl_vsub_of_mem hAB hO]
      have hnorm : ‖lineRefl A B x -ᵥ O‖ ^ 2 = ‖x -ᵥ O‖ ^ 2 := by
        rw [lineRefl_vsub_of_mem hAB hO]; exact norm_reflect_sq _ _
      rw [hnorm, lineRefl_vsub_of_mem hAB hO x, real_inner_smul_right]
      module

/-- `O` lies on the bisector iff the offset vanishes. -/
theorem mem_perpBisector_iff_offset {A B : P} (hAB : A ≠ B) (O : P) :
    O ∈ AffineSubspace.perpBisector A B ↔ 2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1 = 0 := by
  have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖B -ᵥ A‖ ^ 2 ≠ 0 := by positivity
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero]
  have h1 : O -ᵥ A = (O -ᵥ midpoint ℝ A B) + (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [← vsub_add_vsub_cancel O (midpoint ℝ A B) A, midpoint_vsub_left]
    simp
  have h2 : ⟪B -ᵥ A, O -ᵥ A⟫ = ⟪B -ᵥ A, O -ᵥ midpoint ℝ A B⟫ + 1 / 2 * ‖B -ᵥ A‖ ^ 2 := by
    rw [h1, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [h2, real_inner_comm]
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h
    field_simp at h
    nlinarith

theorem lineRefl_offset_vsub {A B : P} (O : P) :
    lineRefl A B O -ᵥ O = (-(2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1)) • (B -ᵥ A) := by
  rw [lineRefl_vsub]; simp; module

theorem lineRefl_congr {A B O : P} (hAB : A ≠ B) (hO : O ∉ AffineSubspace.perpBisector A B) (x : P) :
    lineRefl O (lineRefl A B O) x = lineRefl A B x := by
  have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖B -ᵥ A‖ ^ 2 ≠ 0 := by positivity
  have he : 2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1 ≠ 0 := fun h =>
    hO ((mem_perpBisector_iff_offset hAB O).2 h)
  apply vsub_left_cancel (p := O)
  rw [lineRefl_vsub O (lineRefl A B O) x O, lineRefl_vsub A B x O, lineRefl_offset_vsub]
  simp only [vsub_self, inner_zero_right, mul_zero, zero_div, zero_sub, real_inner_smul_left,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_neg_left, norm_neg]
  generalize 2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1 = e at *
  generalize ⟪B -ᵥ A, x -ᵥ O⟫ = i
  generalize ‖B -ᵥ A‖ ^ 2 = n at *
  generalize B -ᵥ A = u
  generalize x -ᵥ O = w
  match_scalars <;> field_simp <;> ring

theorem offset_key (a i N : ℝ) (hN : N ≠ 0) (he : 2 * a / N - 1 ≠ 0) :
    (-(2 * a / N - 1) * i - -(2 * a / N - 1) * (1 / 2 * (-(2 * a / N - 1) * N)) = 0 ↔
      i + a - 1 / 2 * N = 0) := by
  have : -(2 * a / N - 1) * i - -(2 * a / N - 1) * (1 / 2 * (-(2 * a / N - 1) * N)) =
      -(2 * a / N - 1) * (i + a - 1 / 2 * N) := by
    field_simp; ring
  rw [this, mul_eq_zero, neg_eq_zero]
  exact ⟨fun h => h.resolve_left he, Or.inr⟩

theorem perpBisector_congr {A B O : P} (hAB : A ≠ B) (hO : O ∉ AffineSubspace.perpBisector A B) :
    AffineSubspace.perpBisector O (lineRefl A B O) = AffineSubspace.perpBisector A B := by
  have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hu2 : ‖B -ᵥ A‖ ^ 2 ≠ 0 := by positivity
  have he : 2 * ⟪B -ᵥ A, O -ᵥ A⟫ / ‖B -ᵥ A‖ ^ 2 - 1 ≠ 0 := fun h =>
    hO ((mem_perpBisector_iff_offset hAB O).2 h)
  ext x
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero, AffineSubspace.mem_perpBisector_iff_inner_eq_zero]
  have hY := lineRefl_offset_vsub (A := A) (B := B) O
  have hm : midpoint ℝ O (lineRefl A B O) -ᵥ O = (1 / 2 : ℝ) • (lineRefl A B O -ᵥ O) := by
    rw [midpoint_vsub_left]; simp
  have hm' : midpoint ℝ A B -ᵥ A = (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [midpoint_vsub_left]; simp
  have e1 : x -ᵥ midpoint ℝ O (lineRefl A B O) = (x -ᵥ O) - (1 / 2 : ℝ) • (lineRefl A B O -ᵥ O) := by
    rw [← vsub_sub_vsub_cancel_right x (midpoint ℝ O (lineRefl A B O)) O, hm]
  have e2 : x -ᵥ midpoint ℝ A B = (x -ᵥ O) + (O -ᵥ A) - (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [← vsub_sub_vsub_cancel_right x (midpoint ℝ A B) A, hm', ← vsub_add_vsub_cancel x O A]
  have e3 : lineRefl A B O -ᵥ O = lineRefl A B O -ᵥ O := rfl
  rw [e1, e2, hY]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_right, inner_neg_right,
    inner_neg_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (B -ᵥ A) (O -ᵥ A)]
  exact offset_key _ _ _ hu2 he

/-- **Conjugation, line not through the centre of the inversion.** -/
theorem conjD {A B O : P} {R : ℝ} (hR : R ≠ 0) (hAB : A ≠ B)
    (hO : O ∉ AffineSubspace.perpBisector A B) :
    ∃ (S : P) (s : ℝ), 0 < s ∧
      inversionOP O R '' circOP S s = hypOP (AffineSubspace.perpBisector A B : Set P) ∧
      ∀ z, inversionOP S s (inversionOP O R z) = inversionOP O R (lineReflOP A B z) := by
  set Y := lineRefl A B O with hY
  have hOY : O ≠ Y := by
    intro h
    have := lineRefl_offset_vsub (A := A) (B := B) O
    rw [← hY, ← h, vsub_self] at this
    have hu : B -ᵥ A ≠ 0 := fun h => hAB (vsub_eq_zero_iff_eq.mp h).symm
    rcases smul_eq_zero.mp this.symm with h2 | h2
    · exact hO ((mem_perpBisector_iff_offset hAB O).2 (neg_eq_zero.mp h2))
    · exact hu h2
  set S := inversion O R Y with hS
  have hSO : S ≠ O := fun h => hOY ((inversion_eq_center hR).1 h).symm
  have hSY : inversion O R S = Y := inversion_inversion O hR Y
  have hs : 0 < dist S O := dist_pos.mpr hSO
  refine ⟨S, dist S O, hs, ?_, ?_⟩
  · rw [inversionOP_image_circOP_through hR hs rfl, hSY, perpBisector_congr hAB hO]
  · intro z
    have h1 := conjB hR hs rfl (inversionOP O R z)
    rw [hSY, inversionOP_involutive hR z] at h1
    have h2 : lineReflOP O Y = lineReflOP A B := by
      funext w
      induction w using OnePoint.rec with
      | infty => simp
      | coe x =>
        simp only [lineReflOP_coe]
        exact congrArg _ (lineRefl_congr hAB hO x)
    rw [h2] at h1
    rw [h1, inversionOP_involutive hR]

variable (V) in
/-- `g` is the genuine inversion in the circline `C`: the inversion `inversionOP Q s` (with the
conventions `centre ↔ ∞`) if `C` is the circle with centre `Q` and radius `s`, and the reflection in the
line (fixing `∞`) if `C` is a line (a perpendicular bisector, completed by `∞`). -/
def IsInvOf (C : Set (OnePoint P)) (g : OnePoint P → OnePoint P) : Prop :=
  (∃ (Q : P) (s : ℝ), 0 < s ∧ C = circOP Q s ∧ g = inversionOP Q s) ∨
  (∃ A B : P, A ≠ B ∧ C = hypOP (AffineSubspace.perpBisector A B : Set P) ∧ g = lineReflOP A B)

theorem perpBisector_set_eq {A B O : P} (hAB : A ≠ B) (hO : O ∈ AffineSubspace.perpBisector A B) :
    ((AffineSubspace.perpBisector A B : AffineSubspace ℝ P) : Set P) = {x | ⟪x -ᵥ O, B -ᵥ A⟫ = 0} := by
  ext x
  have hO' := hO
  rw [AffineSubspace.mem_perpBisector_iff_inner_eq_zero] at hO'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, AffineSubspace.mem_perpBisector_iff_inner_eq_zero]
  rw [← vsub_add_vsub_cancel x O (midpoint ℝ A B), inner_add_left, hO', add_zero]

/-- Circlines of the inversive plane as produced by the circumtool: a circle, or a line (a perpendicular
bisector, completed by `∞`; in the plane every line is one). -/
def IsGenCircline (C : Set (OnePoint P)) : Prop :=
  (∃ (Q : P) (s : ℝ), 0 < s ∧ C = circOP Q s) ∨
  (∃ A B : P, A ≠ B ∧ C = hypOP (AffineSubspace.perpBisector A B : Set P))

variable (V) in
theorem IsGenCircline.exists_inv {C : Set (OnePoint P)} (h : IsGenCircline C) :
    ∃ g, IsInvOf V C g := by
  rcases h with ⟨Q, s, hs, rfl⟩ | ⟨A, B, hAB, rfl⟩
  · exact ⟨_, Or.inl ⟨Q, s, hs, rfl, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨A, B, hAB, rfl, rfl⟩⟩

theorem IsInvOf.isGenCircline {C : Set (OnePoint P)} {g : OnePoint P → OnePoint P}
    (h : IsInvOf V C g) : IsGenCircline C := by
  rcases h with ⟨Q, s, hs, rfl, rfl⟩ | ⟨A, B, hAB, rfl, rfl⟩
  · exact Or.inl ⟨Q, s, hs, rfl⟩
  · exact Or.inr ⟨A, B, hAB, rfl⟩

/-- **Corollary 10.26, in the inversive plane.**  The inversion `f` in a circle `Ω` (centre `O`)
conjugates the genuine inversion in any circline `C` to the genuine inversion in the circline `f C`. -/
theorem IsInvOf.conj {O : P} {R : ℝ} (hR : 0 < R) {C : Set (OnePoint P)}
    {g : OnePoint P → OnePoint P} (h : IsInvOf V C g) :
    ∃ g', IsInvOf V (inversionOP O R '' C) g' ∧ ∀ z, g' (inversionOP O R z) = inversionOP O R (g z) := by
  rcases h with ⟨Q, s, hs, rfl, rfl⟩ | ⟨A, B, hAB, rfl, rfl⟩
  · by_cases hd : dist Q O = s
    · have hQO : Q ≠ O := fun h => by rw [h, dist_self] at hd; linarith
      have hOY : O ≠ inversion O R Q := fun h => hQO (by simpa [inversion_eq_center hR.ne'] using h.symm)
      refine ⟨lineReflOP O (inversion O R Q), Or.inr ⟨O, _, hOY, ?_, rfl⟩, ?_⟩
      · rw [inversionOP_image_circOP_through hR.ne' hs hd]
      · exact conjB hR.ne' hs hd
    · refine ⟨inversionOP (invSphereCenter O R Q s) (invSphereRadius O R Q s),
        Or.inl ⟨_, _, invSphereRadius_pos hR.ne' hs hd, ?_, rfl⟩, conjA hR.ne' hs hd⟩
      exact inversionOP_image_circOP_of_ne hR.ne' hs hd
  · by_cases hO : O ∈ AffineSubspace.perpBisector A B
    · refine ⟨lineReflOP A B, Or.inr ⟨A, B, hAB, ?_, rfl⟩, conjC hR.ne' hAB hO⟩
      rw [perpBisector_set_eq hAB hO]
      exact inversionOP_image_hypOP_through hR.ne' rfl
    · obtain ⟨S, s, hs, himg, hconj⟩ := conjD (R := R) hR.ne' hAB hO
      refine ⟨inversionOP S s, Or.inl ⟨S, s, hs, ?_, rfl⟩, hconj⟩
      rw [← himg, Set.image_image]
      have hinv := inversionOP_involutive (c := O) hR.ne'
      simp only [hinv _, Set.image_id']

end GenuineInv

/-! ### Circumtool and inversor procedures -/

section CI

open EuclideanGeometry

variable (V : Type*) {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The state of a circumtool-and-inversor procedure: constructed points and constructed circlines. -/
structure CIState (P : Type*) where
  pts : List (OnePoint P)
  circs : List (Set (OnePoint P))

/-- A step: the circumtool through three earlier points, or the inversor (inversion of an earlier point in
an earlier circline). -/
inductive CIStep
  | circum (i j k : ℕ)
  | invert (c i : ℕ)

/-- `st'` is a possible result of applying the step `s` to `st`.  The circumtool gives a circle, or a line
if the points are collinear; the inversor applies the *genuine* inversion in the circline (`IsInvOf`:
inversion in a circle with the conventions of `inversionOP`, reflection in a line). -/
def CIStep.Out (st : CIState P) : CIStep → CIState P → Prop
  | .circum i j k, st' => ∃ a b c C, st.pts[i]? = Option.some a ∧ st.pts[j]? = Option.some b ∧
      st.pts[k]? = Option.some c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ C ∧ b ∈ C ∧ c ∈ C ∧
      IsGenCircline C ∧ st' = { st with circs := st.circs ++ [C] }
  | .invert c i, st' => ∃ (C : Set (OnePoint P)) (y : OnePoint P) (g : OnePoint P → OnePoint P),
      st.circs[c]? = Option.some C ∧ st.pts[i]? = Option.some y ∧ IsInvOf V C g ∧
      st' = { st with pts := st.pts ++ [g y] }

/-- A run of a list of steps. -/
inductive CIRun : CIState P → List CIStep → CIState P → Prop
  | nil (st : CIState P) : CIRun st [] st
  | cons {st st' st'' : CIState P} {s : CIStep} {rest : List CIStep} :
      CIStep.Out V st s st' → CIRun st' rest st'' → CIRun st (s :: rest) st''

/-- Atomic tests: two points coincide, or a point lies on a circline. -/
inductive CITest
  | same (i j : ℕ)
  | onCirc (i c : ℕ)

/-- The test holds in the state. -/
def CITest.Holds (st : CIState P) : CITest → Prop
  | .same i j => ∃ p q, st.pts[i]? = Option.some p ∧ st.pts[j]? = Option.some q ∧ p = q
  | .onCirc i c => ∃ p C, st.pts[i]? = Option.some p ∧ st.circs[c]? = Option.some C ∧ p ∈ C

/-- A circumtool-and-inversor procedure. -/
structure CIProc where
  n : ℕ
  steps : List CIStep
  test : CITest

/-- `T` verifies that a point is the centre `Q` of the given circle `Γ`, in the book's sense: for every
tested point `X` the `n` free points (ordinary points of the plane) are only required to lie in a dense
open set `G` of general positions (product topology); for free points in `G` the run is defined and
every run answers "yes" exactly when `X = Q`. -/
def CIProc.Verifies [TopologicalSpace P] (Γ : Set (OnePoint P)) (Q : OnePoint P) (T : CIProc) : Prop :=
  ∀ X : OnePoint P, ∃ G : Set (Fin T.n → P), IsOpen G ∧ Dense G ∧ ∀ free ∈ G,
    (∃ st', CIRun V ⟨X :: List.ofFn (fun i => (free i : OnePoint P)), [Γ]⟩ T.steps st') ∧
    ∀ st', CIRun V ⟨X :: List.ofFn (fun i => (free i : OnePoint P)), [Γ]⟩ T.steps st' →
      (T.test.Holds st' ↔ X = Q)

/-- Image of a state under a map of the inversive plane. -/
def CIState.map (f : OnePoint P → OnePoint P) (st : CIState P) : CIState P :=
  ⟨st.pts.map f, st.circs.map (fun C => f '' C)⟩

variable {V}

theorem CIStep.Out.map {O : P} {R : ℝ} (hR : 0 < R)
    {st st' : CIState P} {s : CIStep} (h : CIStep.Out V st s st') :
    CIStep.Out V (st.map (inversionOP O R)) s (st'.map (inversionOP O R)) := by
  have hinj : Function.Injective (inversionOP O R) := (inversionOP_bijective hR.ne').1
  cases s with
  | circum i j k =>
    obtain ⟨a, b, c, C, h1, h2, h3, hab, hac, hbc, ha, hb, hc, hcl, rfl⟩ := h
    obtain ⟨g, hg⟩ := hcl.exists_inv V
    obtain ⟨g', hg', -⟩ := hg.conj (O := O) hR
    refine ⟨inversionOP O R a, inversionOP O R b, inversionOP O R c, inversionOP O R '' C,
      by simp [CIState.map, h1], by simp [CIState.map, h2], by simp [CIState.map, h3],
      hinj.ne hab, hinj.ne hac, hinj.ne hbc, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩,
      hg'.isGenCircline, ?_⟩
    simp [CIState.map]
  | invert c i =>
    obtain ⟨C, y, g, h1, h2, hg, rfl⟩ := h
    obtain ⟨g', hg', hcomm⟩ := hg.conj (O := O) hR
    refine ⟨inversionOP O R '' C, inversionOP O R y, g', by simp [CIState.map, h1],
      by simp [CIState.map, h2], hg', ?_⟩
    simp [CIState.map, hcomm]

theorem CIRun.map {O : P} {R : ℝ} (hR : 0 < R)
    {st st' : CIState P} {steps : List CIStep} (h : CIRun V st steps st') :
    CIRun V (st.map (inversionOP O R)) steps (st'.map (inversionOP O R)) := by
  induction h with
  | nil st => exact .nil _
  | cons hs _ ih => exact .cons (hs.map hR) ih

theorem CITest.Holds.map (f : OnePoint P → OnePoint P) {st : CIState P} {t : CITest}
    (h : t.Holds st) : t.Holds (st.map f) := by
  cases t with
  | same i j =>
    obtain ⟨p, q, h1, h2, rfl⟩ := h
    exact ⟨f p, f p, by simp [CIState.map, h1], by simp [CIState.map, h2], rfl⟩
  | onCirc i c =>
    obtain ⟨p, C, h1, h2, h3⟩ := h
    exact ⟨f p, f '' C, by simp [CIState.map, h1], by simp [CIState.map, h2], ⟨p, h3, rfl⟩⟩

section Concrete

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] {O Q : P} {R s : ℝ}

/-- **Problem 19.16, pp. 162-163.**  Let `Γ` be the circle with centre `Q` and radius `s`, and let `Ω`
(centre `O`, radius `R`) be a circle orthogonal to `Γ`.  No procedure with a circumtool and an inversor
verifies that a point is the centre of `Γ`: the inversion in `Ω` preserves `Γ`, commutes with runs
(it conjugates the genuine inversion in a circline to the genuine inversion in the image circline, by
Corollary 10.26 in all cases, `IsInvOf.conj`) and tests, and moves the centre. -/
@[kb "petrunin2025" "Problem 19.16, p. 162"]
theorem no_circumtool_inversor_verifies_centre (hR : 0 < R) (hs : 0 < s)
    (hperp : dist Q O ^ 2 = R ^ 2 + s ^ 2) (T : CIProc) :
    ¬ T.Verifies V (circOP Q s) (Q : OnePoint P) := by
  intro hv
  have hR' : R ≠ 0 := hR.ne'
  have hΓ := inversionOP_image_orthogonal hR hs hperp
  obtain ⟨G₁, h₁o, h₁d, h₁⟩ := hv (Q : OnePoint P)
  obtain ⟨G₂, h₂o, h₂d, h₂⟩ := hv (inversionOP O R (Q : OnePoint P))
  set U : Set (Fin T.n → P) := Set.pi Set.univ (fun _ => {O}ᶜ) with hU
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [Fact.out (p := Module.finrank ℝ V = 2)]; norm_num)
  have hd : Dense ({O}ᶜ : Set P) := by
    rw [dense_compl_singleton_iff_not_open]
    intro ho
    let e : V ≃ᵢ P := IsometryEquiv.vaddConst O
    have h1 : IsOpen (e ⁻¹' {O}) := ho.preimage e.continuous
    have h2 : e ⁻¹' {O} = {e.symm O} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (e.toEquiv.eq_symm_apply).symm
    rw [h2] at h1
    exact dense_compl_singleton_iff_not_open.1 (dense_compl_singleton (e.symm O)) h1
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_compl_singleton)
  have hUd : Dense U := dense_pi _ (fun _ _ => hd)
  have hcts : ContinuousOn (fun (free : Fin T.n → P) i => inversion O R (free i)) U := by
    refine continuousOn_pi.2 fun i => fun x hx => ?_
    exact (ContinuousAt.inversion (c := fun _ : Fin T.n → P => O) (R := fun _ : Fin T.n → P => R)
      (x := fun free : Fin T.n → P => free i) continuousAt_const continuousAt_const
      (continuous_apply i).continuousAt (hx i trivial)).continuousWithinAt
  have hmaps : ∀ x ∈ U, (fun i => inversion O R (x i)) ∈ U := fun x hx i _ =>
    (inversion_eq_center hR').not.2 (hx i trivial)
  have hinv : ∀ x ∈ U, (fun i => inversion O R (inversion O R (x i))) = x :=
    fun x _ => by ext i; exact inversion_involutive O hR' (x i)
  obtain ⟨free, hf1, hfU, hf2⟩ := exists_generic (φ := fun (x : Fin T.n → P) i => inversion O R (x i))
    (ψ := fun (x : Fin T.n → P) i => inversion O R (x i)) hUo hUd hcts hcts hmaps hinv hinv h₁o h₁d h₂o h₂d
  obtain ⟨⟨st', hrun⟩, hs'⟩ := h₁ free hf1
  have h1 : T.test.Holds st' := (hs' st' hrun).2 rfl
  have h2 := hrun.map (O := O) hR
  have hl : List.map (inversionOP O R) (List.ofFn fun i => (free i : OnePoint P)) =
      List.ofFn fun i => ((inversion O R (free i) : P) : OnePoint P) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact inversionOP_coe_of_ne (hfU i trivial)
  have hst : (CIState.map (inversionOP O R)
      ⟨(Q : OnePoint P) :: List.ofFn (fun i => (free i : OnePoint P)), [circOP Q s]⟩) =
      ⟨inversionOP O R (Q : OnePoint P) :: List.ofFn (fun i => ((inversion O R (free i) : P) : OnePoint P)),
        [circOP Q s]⟩ := by
    simp only [CIState.map, List.map_cons, List.map_nil, hl]
    rw [hΓ]
  rw [hst] at h2
  have h3 := ((h₂ _ hf2).2 _ h2).1 (CITest.Holds.map _ h1)
  exact inversionOP_centre_ne hR hs hperp h3

/-- **Problem 19.16, pp. 162-163**, without auxiliary data: for every circle `Γ` (centre `Q`, radius
`s > 0`) in a Euclidean plane, no procedure with a circumtool and an inversor verifies that a point is
the centre of `Γ`.  (A circle orthogonal to `Γ` always exists: centre at distance `2s` from `Q`,
radius `√3 · s`.) -/
@[kb "petrunin2025" "Problem 19.16, p. 162"]
theorem no_circumtool_inversor_verifies_centre' (hs : 0 < s) (T : CIProc) :
    ¬ T.Verifies V (circOP Q s) (Q : OnePoint P) := by
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [Fact.out (p := Module.finrank ℝ V = 2)]; norm_num)
  obtain ⟨v, hv⟩ := exists_norm_eq V (show (0 : ℝ) ≤ 2 * s by linarith)
  refine no_circumtool_inversor_verifies_centre (O := v +ᵥ Q) (R := Real.sqrt 3 * s)
    (by positivity) hs ?_ T
  rw [dist_comm, dist_vadd_left, hv]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

end Concrete

end CI

end Verif

end CentreVerification

end UndergradKB.Geometry
