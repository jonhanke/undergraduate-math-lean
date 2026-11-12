import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Shift
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Green
import UndergradKB.Calculus.Surfaces

/-! # Calculus: oriented curves, parametrized patches and the cancellation of interior pieces

Wave 5 of the calculus coverage (OpenStax Calculus 3 §6.4, §6.7, §6.8). The book's general Green, Stokes and
divergence theorems are proved by cutting a region, surface or solid into pieces, applying the theorem to each
piece and observing that the integrals along the interior cuts cancel, since each cut is traversed (or crossed)
once in each direction. This file supplies the bookkeeping:
* an oriented curve is a path `γ : ℝ → E` with a start and a stop parameter (start > stop allowed: the integral
  `∫ t in start..stop` is then taken backwards); its reverse swaps start and stop, which changes the sign of every
  line integral (`planeCurveIntegral_reverse`, `spaceCurveIntegral_reverse`), and an orientation reversing
  reparametrization does the same (`planeCurveIntegral_reparam`, `spaceCurveIntegral_reparam`);
* a parametrized rectangle `r : [a,b]×[c,d] → E` has as boundary the four image edges traversed counterclockwise
  (`ParamRect.boundary`); its reverse `(u,v) ↦ r(a+b-u, v)` is the same surface with the opposite orientation and
  opposite flux (`patchFlux_reverse`);
* the cancellation lemma `sum_map_cancel_pairs`: if a list of pieces is, up to order, a list `outer` together with
  pairs of pieces with opposite integrals, the total integral is that of `outer`. -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-! ### The cancellation lemma -/

/-- Cancellation of interior pieces: if the list `l` is a permutation of `outer` followed by pairs `(e, e')` with
`I e' = -I e`, the sum of `I` over `l` is the sum over `outer`. -/
theorem sum_map_cancel_pairs {α : Type*} (I : α → ℝ) {l outer : List α} (pairs : List (α × α))
    (hpair : ∀ p ∈ pairs, I p.2 = -I p.1)
    (hperm : l.Perm (outer ++ pairs.flatMap fun p => [p.1, p.2])) :
    (l.map I).sum = (outer.map I).sum := by
  rw [(hperm.map I).sum_eq, List.map_append, List.sum_append]
  have h0 : ((pairs.flatMap fun p => [p.1, p.2]).map I).sum = 0 := by
    clear hperm
    induction pairs with
    | nil => simp
    | cons p ps ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        ih (fun q hq => hpair q (List.mem_cons_of_mem _ hq))]
      simp [hpair p List.mem_cons_self]
  rw [h0, add_zero]

/-! ### Oriented curves -/

/-- An oriented curve: the path `γ` traversed from parameter `start` to parameter `stop` (backwards if
`stop < start`). -/
structure OrientedCurve (E : Type*) where
  /-- the path -/
  path : ℝ → E
  /-- the initial parameter -/
  start : ℝ
  /-- the final parameter -/
  stop : ℝ

/-- The same curve traversed in the opposite direction. -/
def OrientedCurve.reverse {E : Type*} (c : OrientedCurve E) : OrientedCurve E := ⟨c.path, c.stop, c.start⟩

/-- The line integral `∫_C P dx + Q dy` along an oriented plane curve. -/
noncomputable def planeCurveIntegral (P Q : ℝ × ℝ → ℝ) (c : OrientedCurve (ℝ × ℝ)) : ℝ :=
  greenLineIntegral P Q (fun t => (c.path t).1) (fun t => (c.path t).2) c.start c.stop

/-- The line integral `∫_C F · dr` along an oriented curve of `ℝ³`. -/
noncomputable def spaceCurveIntegral (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (c : OrientedCurve (Fin 3 → ℝ)) : ℝ :=
  ∫ t in c.start..c.stop, F (c.path t) ⬝ᵥ deriv c.path t

/-- Reversing the orientation of a plane curve changes the sign of the line integral. -/
theorem planeCurveIntegral_reverse (P Q : ℝ × ℝ → ℝ) (c : OrientedCurve (ℝ × ℝ)) :
    planeCurveIntegral P Q c.reverse = -planeCurveIntegral P Q c :=
  intervalIntegral.integral_symm _ _

/-- Reversing the orientation of a space curve changes the sign of the line integral. -/
theorem spaceCurveIntegral_reverse (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (c : OrientedCurve (Fin 3 → ℝ)) :
    spaceCurveIntegral F c.reverse = -spaceCurveIntegral F c :=
  intervalIntegral.integral_symm _ _

/-- Two functions that agree on the open interval have the same interval integral. -/
theorem intervalIntegral_congr_Ioo {f g : ℝ → ℝ} {s t : ℝ}
    (h : ∀ x ∈ Ioo (min s t) (max s t), f x = g x) : ∫ x in s..t, f x = ∫ x in s..t, g x := by
  have key : ∀ {s t : ℝ}, s ≤ t → (∀ x ∈ Ioo s t, f x = g x) → ∫ x in s..t, f x = ∫ x in s..t, g x := by
    intro s t hst h
    rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo h
  rcases le_total s t with hst | hts
  · exact key hst (by simpa [min_eq_left hst, max_eq_right hst] using h)
  · rw [intervalIntegral.integral_symm, key hts (by simpa [min_eq_right hts, max_eq_left hts] using h),
      ← intervalIntegral.integral_symm]

/-- Two paths that agree on the closed parameter interval agree near every interior point. -/
theorem eventuallyEq_of_eqOn_uIcc {E : Type*} {γ₁ γ₂ : ℝ → E} {s t : ℝ} (h : ∀ x ∈ uIcc s t, γ₁ x = γ₂ x)
    {x : ℝ} (hx : x ∈ Ioo (min s t) (max s t)) : γ₁ =ᶠ[nhds x] γ₂ :=
  Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => h y (Ioo_subset_Icc_self hy))

/-- Two plane curves whose paths agree on the parameter interval have the same line integrals. -/
theorem planeCurveIntegral_congr (P Q : ℝ × ℝ → ℝ) {γ₁ γ₂ : ℝ → ℝ × ℝ} {s t : ℝ}
    (h : ∀ x ∈ uIcc s t, γ₁ x = γ₂ x) :
    planeCurveIntegral P Q ⟨γ₁, s, t⟩ = planeCurveIntegral P Q ⟨γ₂, s, t⟩ := by
  refine intervalIntegral_congr_Ioo (fun x hx => ?_)
  have hev := eventuallyEq_of_eqOn_uIcc h hx
  have h1 : (fun t => (γ₁ t).1) =ᶠ[nhds x] (fun t => (γ₂ t).1) := hev.fun_comp Prod.fst
  have h2 : (fun t => (γ₁ t).2) =ᶠ[nhds x] (fun t => (γ₂ t).2) := hev.fun_comp Prod.snd
  simp only [h x (Ioo_subset_Icc_self hx), h1.deriv_eq, h2.deriv_eq]

/-- Two space curves whose paths agree on the parameter interval have the same line integrals. -/
theorem spaceCurveIntegral_congr (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {γ₁ γ₂ : ℝ → Fin 3 → ℝ} {s t : ℝ}
    (h : ∀ x ∈ uIcc s t, γ₁ x = γ₂ x) :
    spaceCurveIntegral F ⟨γ₁, s, t⟩ = spaceCurveIntegral F ⟨γ₂, s, t⟩ := by
  refine intervalIntegral_congr_Ioo (fun x hx => ?_)
  simp only [h x (Ioo_subset_Icc_self hx), (eventuallyEq_of_eqOn_uIcc h hx).deriv_eq]

/-- Reparametrization: running the plane curve `γ ∘ φ` from `s` to `t` gives the same line integral as running
`γ` from `φ s` to `φ t` (`γ` and `φ` of class `C¹`, the field continuous along the curve). In particular a
reparametrization that reverses the direction changes the sign. -/
theorem planeCurveIntegral_reparam {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ 1 γ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {s t : ℝ}
    (hU : ∀ x ∈ φ '' uIcc s t, γ x ∈ U) :
    planeCurveIntegral P Q ⟨γ ∘ φ, s, t⟩ = planeCurveIntegral P Q ⟨γ, φ s, φ t⟩ := by
  have h1 : ContDiff ℝ 1 (fun t => (γ t).1) := contDiff_fst.comp hγ
  have h2 : ContDiff ℝ 1 (fun t => (γ t).2) := contDiff_snd.comp hγ
  set G : ℝ → ℝ := fun u => P (γ u) * deriv (fun t => (γ t).1) u + Q (γ u) * deriv (fun t => (γ t).2) u
    with hG
  have hc : ∀ x, P ((γ ∘ φ) x) * deriv (fun t => ((γ ∘ φ) t).1) x +
      Q ((γ ∘ φ) x) * deriv (fun t => ((γ ∘ φ) t).2) x = (G ∘ φ) x * deriv φ x := by
    intro x
    have e1 : deriv (fun t => ((γ ∘ φ) t).1) x = deriv (fun t => (γ t).1) (φ x) * deriv φ x :=
      deriv_comp (h := φ) (h₂ := fun t => (γ t).1) x ((h1.differentiable one_ne_zero) _)
        ((hφ.differentiable one_ne_zero) x)
    have e2 : deriv (fun t => ((γ ∘ φ) t).2) x = deriv (fun t => (γ t).2) (φ x) * deriv φ x :=
      deriv_comp (h := φ) (h₂ := fun t => (γ t).2) x ((h2.differentiable one_ne_zero) _)
        ((hφ.differentiable one_ne_zero) x)
    rw [e1, e2, Function.comp_apply, Function.comp_apply, hG]
    ring
  have hγU : ContinuousOn γ (φ '' uIcc s t) := hγ.continuous.continuousOn
  have hGc : ContinuousOn G (φ '' uIcc s t) :=
    ((hP.comp hγU hU).mul (h1.continuous_deriv le_rfl).continuousOn).add
      ((hQ.comp hγU hU).mul (h2.continuous_deriv le_rfl).continuousOn)
  have key := intervalIntegral.integral_comp_mul_deriv' (a := s) (b := t) (f := φ) (g := G)
    (fun x _ => ((hφ.differentiable one_ne_zero) x).hasDerivAt) (hφ.continuous_deriv le_rfl).continuousOn hGc
  unfold planeCurveIntegral greenLineIntegral
  rw [← key]
  exact intervalIntegral.integral_congr (fun x _ => hc x)

/-- Reparametrization of a space curve (as `planeCurveIntegral_reparam`). -/
theorem spaceCurveIntegral_reparam {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)} (hF : ContinuousOn F U)
    {γ : ℝ → Fin 3 → ℝ} (hγ : ContDiff ℝ 1 γ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {s t : ℝ}
    (hU : ∀ x ∈ φ '' uIcc s t, γ x ∈ U) :
    spaceCurveIntegral F ⟨γ ∘ φ, s, t⟩ = spaceCurveIntegral F ⟨γ, φ s, φ t⟩ := by
  set G : ℝ → ℝ := fun u => F (γ u) ⬝ᵥ deriv γ u with hG
  have hc : ∀ x, F ((γ ∘ φ) x) ⬝ᵥ deriv (γ ∘ φ) x = (G ∘ φ) x * deriv φ x := by
    intro x
    rw [deriv.scomp x ((hγ.differentiable one_ne_zero) _) ((hφ.differentiable one_ne_zero) x), dotProduct_smul,
      smul_eq_mul, mul_comm, Function.comp_apply, Function.comp_apply, hG]
  have hFγ : ContinuousOn (fun u => F (γ u)) (φ '' uIcc s t) := hF.comp hγ.continuous.continuousOn hU
  have hdγ : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hGc : ContinuousOn G (φ '' uIcc s t) := by
    rw [hG]
    have hi : ∀ i : Fin 3, ContinuousOn (fun u => F (γ u) i * deriv γ u i) (φ '' uIcc s t) := fun i =>
      ((continuous_apply i).comp_continuousOn hFγ).mul ((continuous_apply i).comp hdγ).continuousOn
    simp only [dotProduct, Fin.sum_univ_three]
    exact ((hi 0).add (hi 1)).add (hi 2)
  have key := intervalIntegral.integral_comp_mul_deriv' (a := s) (b := t) (f := φ) (g := G)
    (fun x _ => ((hφ.differentiable one_ne_zero) x).hasDerivAt) (hφ.continuous_deriv le_rfl).continuousOn hGc
  unfold spaceCurveIntegral
  rw [← key]
  exact intervalIntegral.integral_congr (fun x _ => hc x)

/-- `c'` runs along `c` in the opposite direction: `c'.path = c.path ∘ φ` on the parameter interval of `c'`, for a
`C¹` change of parameter `φ` from the interval of `c'` into that of `c` that carries the start of `c'` to the stop
of `c` and the stop of `c'` to the start of `c` (and `c` is of class `C¹`). Two cells glued along an edge traverse
it in opposite directions in this sense. -/
def OrientedCurve.IsOpposite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c c' : OrientedCurve E) :
    Prop :=
  ContDiff ℝ 1 c.path ∧ ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ φ c'.start = c.stop ∧ φ c'.stop = c.start ∧
    ∀ x ∈ uIcc c'.start c'.stop, φ x ∈ uIcc c.start c.stop ∧ c'.path x = c.path (φ x)

/-- A `C¹` curve and its reverse are opposite. -/
theorem OrientedCurve.isOpposite_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : OrientedCurve E) (hc : ContDiff ℝ 1 c.path) : c.IsOpposite c.reverse :=
  ⟨hc, id, contDiff_id, rfl, rfl, fun x hx => ⟨by simpa [OrientedCurve.reverse, uIcc_comm] using hx, rfl⟩⟩

/-- Opposite plane curves have opposite line integrals (field continuous along the curve). -/
theorem planeCurveIntegral_of_isOpposite {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hP : ContinuousOn P U)
    (hQ : ContinuousOn Q U) {c c' : OrientedCurve (ℝ × ℝ)} (h : c.IsOpposite c')
    (hU : ∀ x ∈ uIcc c.start c.stop, c.path x ∈ U) :
    planeCurveIntegral P Q c' = -planeCurveIntegral P Q c := by
  obtain ⟨hc, φ, hφ, h1, h2, h3⟩ := h
  have e1 : planeCurveIntegral P Q c' = planeCurveIntegral P Q ⟨c.path ∘ φ, c'.start, c'.stop⟩ :=
    planeCurveIntegral_congr P Q (fun x hx => (h3 x hx).2)
  rw [e1, planeCurveIntegral_reparam hP hQ hc hφ (fun x ⟨y, hy, hxy⟩ => hxy ▸ hU _ (h3 y hy).1), h1, h2]
  exact planeCurveIntegral_reverse P Q c

/-- Opposite space curves have opposite line integrals (field continuous along the curve). -/
theorem spaceCurveIntegral_of_isOpposite {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)}
    (hF : ContinuousOn F U) {c c' : OrientedCurve (Fin 3 → ℝ)} (h : c.IsOpposite c')
    (hU : ∀ x ∈ uIcc c.start c.stop, c.path x ∈ U) :
    spaceCurveIntegral F c' = -spaceCurveIntegral F c := by
  obtain ⟨hc, φ, hφ, h1, h2, h3⟩ := h
  have e1 : spaceCurveIntegral F c' = spaceCurveIntegral F ⟨c.path ∘ φ, c'.start, c'.stop⟩ :=
    spaceCurveIntegral_congr F (fun x hx => (h3 x hx).2)
  rw [e1, spaceCurveIntegral_reparam hF hc hφ (fun x ⟨y, hy, hxy⟩ => hxy ▸ hU _ (h3 y hy).1), h1, h2]
  exact spaceCurveIntegral_reverse F c

/-! ### Parametrized rectangles (cells and patches) -/

/-- A map `r` of the rectangle `[a,b]×[c,d]` into `E`: a parametrized region of the plane (`E = ℝ²`) or a
parametrized surface patch (`E = ℝ³`). -/
structure ParamRect (E : Type*) where
  /-- the parametrization -/
  map : ℝ × ℝ → E
  /-- lower bound of the first parameter -/
  a : ℝ
  /-- upper bound of the first parameter -/
  b : ℝ
  /-- lower bound of the second parameter -/
  c : ℝ
  /-- upper bound of the second parameter -/
  d : ℝ

/-- The parameter rectangle `[a,b]×[c,d]`. -/
def ParamRect.dom {E : Type*} (p : ParamRect E) : Set (ℝ × ℝ) := Icc p.a p.b ×ˢ Icc p.c p.d

/-- The boundary of a parametrized rectangle: the images of the bottom edge (left to right), the right edge
(upwards), the top edge (right to left) and the left edge (downwards). -/
def ParamRect.boundary {E : Type*} (p : ParamRect E) : List (OrientedCurve E) :=
  [⟨fun x => p.map (x, p.c), p.a, p.b⟩, ⟨fun y => p.map (p.b, y), p.c, p.d⟩,
    ⟨fun x => p.map (x, p.d), p.b, p.a⟩, ⟨fun y => p.map (p.a, y), p.d, p.c⟩]

/-- The boundary edges of a parametrized rectangle lie in the image of the rectangle. -/
theorem ParamRect.boundary_mem_image {E : Type*} (p : ParamRect E) (hab : p.a ≤ p.b) (hcd : p.c ≤ p.d) :
    ∀ e ∈ p.boundary, ∀ x ∈ uIcc e.start e.stop, e.path x ∈ p.map '' p.dom := by
  intro e he x hx
  simp only [ParamRect.boundary, List.mem_cons, List.not_mem_nil, or_false] at he
  have ha : p.a ∈ Icc p.a p.b := ⟨le_rfl, hab⟩
  have hb : p.b ∈ Icc p.a p.b := ⟨hab, le_rfl⟩
  have hc : p.c ∈ Icc p.c p.d := ⟨le_rfl, hcd⟩
  have hd : p.d ∈ Icc p.c p.d := ⟨hcd, le_rfl⟩
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨_, ⟨by simpa [uIcc_of_le hab] using hx, hc⟩, rfl⟩
  · exact ⟨_, ⟨hb, by simpa [uIcc_of_le hcd] using hx⟩, rfl⟩
  · exact ⟨_, ⟨by simpa [uIcc_of_ge hab] using hx, hd⟩, rfl⟩
  · exact ⟨_, ⟨ha, by simpa [uIcc_of_ge hcd] using hx⟩, rfl⟩

/-- The boundary edges of a `C¹` parametrized rectangle are `C¹` curves. -/
theorem ParamRect.boundary_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ParamRect E)
    (hp : ContDiff ℝ 1 p.map) : ∀ e ∈ p.boundary, ContDiff ℝ 1 e.path := by
  intro e he
  simp only [ParamRect.boundary, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hp.comp (contDiff_id.prodMk contDiff_const)
  · exact hp.comp (contDiff_const.prodMk contDiff_id)
  · exact hp.comp (contDiff_id.prodMk contDiff_const)
  · exact hp.comp (contDiff_const.prodMk contDiff_id)

/-- The same patch with the opposite orientation: `(u, v) ↦ r(a + b - u, v)`. -/
def ParamRect.reverse {E : Type*} (p : ParamRect E) : ParamRect E :=
  ⟨fun z => p.map (p.a + p.b - z.1, z.2), p.a, p.b, p.c, p.d⟩

/-- The flux `∬_S F · dS` of a field through a parametrized patch of `ℝ³`, oriented by `r_u × r_v`. -/
noncomputable def patchFlux (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : ParamRect (Fin 3 → ℝ)) : ℝ :=
  surfaceFlux F p.map p.dom

/-- Reversing a patch changes the sign of the flux of every field. -/
theorem patchFlux_reverse (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : ParamRect (Fin 3 → ℝ)) :
    patchFlux F p.reverse = -patchFlux F p := by
  set T : ℝ × ℝ → ℝ × ℝ := fun z => (p.a + p.b - z.1, z.2) with hT
  have hU : ∀ z, partialU p.reverse.map z = -partialU p.map (T z) := by
    intro z
    simp only [partialU, ParamRect.reverse]
    exact deriv_comp_const_sub (f := fun u => p.map (u, z.2)) _ _
  have hV : ∀ z, partialV p.reverse.map z = partialV p.map (T z) := fun z => rfl
  have hint : ∀ z, F (p.reverse.map z) ⬝ᵥ surfNormal p.reverse.map z =
      -(F (p.map (T z)) ⬝ᵥ surfNormal p.map (T z)) := by
    intro z
    simp only [surfNormal, hU, hV]
    rw [LinearMap.map_neg, LinearMap.neg_apply, dotProduct_neg]
    rfl
  have hmp : MeasurePreserving T volume volume := by
    have := (Measure.measurePreserving_sub_left volume (p.a + p.b)).prod (MeasurePreserving.id (volume : Measure ℝ))
    rw [Measure.volume_eq_prod]
    exact this
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.subLeft (p.a + p.b)).prodCongr (MeasurableEquiv.refl ℝ)
  have hemb : MeasurableEmbedding T := e.measurableEmbedding
  have hpre : T ⁻¹' p.dom = p.dom := by
    ext z
    simp only [ParamRect.dom, hT, mem_preimage, mem_prod, mem_Icc]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [patchFlux, patchFlux, surfaceFlux, surfaceFlux]
  simp only [hint, integral_neg]
  rw [← hmp.setIntegral_preimage_emb hemb (fun w => F (p.map w) ⬝ᵥ surfNormal p.map w) p.dom, hpre]
  rfl

end UndergradKB.Calculus
