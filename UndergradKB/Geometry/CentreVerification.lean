import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr
import UndergradKB.Geometry.InversivePlane

/-! # The centre of a circle cannot be verified by a ruler (Petrunin, Theorem 19.18, p. 163)

Ruler-only constructions with a given circle `Γ` whose centre is NOT given are carried out in the real
projective plane `ℙ²(ℝ)`, with points represented by nonzero vectors of `ℝ³` up to a nonzero scalar and
`Γ = {x₀² + x₁² = x₂²}` (the unit circle in the chart `x₂ = 1`).  A step is: join two constructed points
by a line, intersect two distinct constructed lines, or intersect a constructed line with `Γ`.
(Working in the projective plane lets the ruler also meet parallel lines; this only enlarges the set of
constructions, so an impossibility result here implies the one in the affine plane.)

The key fact (`RConstr.map`): a linear automorphism `M` of `ℝ³` preserving the cone of `Γ` carries
constructions to constructions.  The Klein-model boost `M` with `t = 3/5` fixes the two points `(±1, 0)`
of `Γ`, maps `Γ` to itself, and moves the centre `(0, 0)` to `(3/5, 0)`.  Hence the construction made
with the centre `Z` among the data and the construction made with `M Z` among the data are mirror images
of each other (`ruler_centre_indistinguishable`), while `M Z` is not the centre: no ruler-only
construction can verify that a point is the centre of `Γ`.  We also show that the centre is not
constructible from the two fixed points (`centre_not_rconstr`).

Problem 19.16 (p. 162): constructions with a circumtool and an inversor (`CIConstr`, in the inversive plane
`OnePoint P`) are carried to constructions by any inversive transformation preserving the given circle
(`CIConstr.map_iff`); the inversion in a circle orthogonal to `Γ` preserves `Γ` and moves its centre
(`circumtool_inversor_centre_indistinguishable`).
-/

namespace UndergradKB.Geometry

namespace CentreVerification

/-- Points of the projective plane, as vectors of `ℝ³`. -/
abbrev V3 : Type := Fin 3 → ℝ

/-- The cone of the given circle `x₀² + x₁² = x₂²`. -/
def OnGamma (x : V3) : Prop := x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2

/-- Ruler-only constructibility of projective points with a given circle but not its centre
(Petrunin, Theorem 19.18, p. 163).  Points are vectors up to a nonzero scalar; new points are intersections
of two distinct lines spanned by constructed points, or of such a line with the given circle. -/
inductive RConstr (S : Set V3) : V3 → Prop
  | init {x : V3} : x ∈ S → x ≠ 0 → RConstr S x
  | smul {c : ℝ} {x : V3} : c ≠ 0 → RConstr S x → RConstr S (c • x)
  | lineLine {p q p' q' x : V3} : RConstr S p → RConstr S q → RConstr S p' → RConstr S q' →
      LinearIndependent ℝ ![p, q] → LinearIndependent ℝ ![p', q'] →
      Submodule.span ℝ {p, q} ≠ Submodule.span ℝ {p', q'} →
      x ∈ Submodule.span ℝ {p, q} → x ∈ Submodule.span ℝ {p', q'} → x ≠ 0 → RConstr S x
  | lineCircle {p q x : V3} : RConstr S p → RConstr S q → LinearIndependent ℝ ![p, q] →
      x ∈ Submodule.span ℝ {p, q} → x ≠ 0 → OnGamma x → RConstr S x

theorem RConstr.mono {S T : Set V3} (h : ∀ y ∈ S, RConstr T y) {x : V3} (hx : RConstr S x) :
    RConstr T x := by
  induction hx with
  | init hx _ => exact h _ hx
  | smul hc _ ih => exact .smul hc ih
  | lineLine _ _ _ _ h1 h2 h3 h4 h5 h6 ih1 ih2 ih3 ih4 => exact .lineLine ih1 ih2 ih3 ih4 h1 h2 h3 h4 h5 h6
  | lineCircle _ _ h1 h2 h3 h4 ih1 ih2 => exact .lineCircle ih1 ih2 h1 h2 h3 h4

/-- Invariance under a linear automorphism preserving the circle. -/
theorem RConstr.map (M : V3 ≃ₗ[ℝ] V3) (hM : ∀ v, OnGamma (M v) ↔ OnGamma v) {S : Set V3} {x : V3}
    (hx : RConstr S x) : RConstr (M '' S) (M x) := by
  have hspan : ∀ p q : V3, Submodule.map (M : V3 →ₗ[ℝ] V3) (Submodule.span ℝ {p, q}) =
      Submodule.span ℝ {M p, M q} := fun p q => by
    rw [Submodule.map_span, Set.image_pair]; rfl
  have hmem : ∀ (p q y : V3), y ∈ Submodule.span ℝ {p, q} → M y ∈ Submodule.span ℝ {M p, M q} :=
    fun p q y h => by
      rw [← hspan]; exact Submodule.mem_map_of_mem h
  have hli : ∀ p q : V3, LinearIndependent ℝ ![p, q] → LinearIndependent ℝ ![M p, M q] := fun p q h => by
    have := h.map' (M : V3 →ₗ[ℝ] V3) (LinearEquiv.ker M)
    convert this using 1
    ext i : 1
    fin_cases i <;> rfl
  induction hx with
  | init hx h0 => exact .init ⟨_, hx, rfl⟩ (by simpa using h0)
  | @smul c x hc _ ih => rw [map_smul]; exact .smul hc ih
  | @lineLine p q p' q' x _ _ _ _ h1 h2 h3 h4 h5 h6 ih1 ih2 ih3 ih4 =>
    refine .lineLine ih1 ih2 ih3 ih4 (hli _ _ h1) (hli _ _ h2) ?_ (hmem _ _ _ h4) (hmem _ _ _ h5)
      (by simpa using h6)
    intro h
    apply h3
    rw [← hspan, ← hspan] at h
    exact Submodule.map_injective_of_injective M.injective h
  | @lineCircle p q x _ _ h1 h2 h3 h4 ih1 ih2 =>
    exact .lineCircle ih1 ih2 (hli _ _ h1) (hmem _ _ _ h2) (by simpa using h3) ((hM x).2 h4)

/-- The Klein-model boost with `t = 3/5` as a linear automorphism of `ℝ³`:
`(x₀, x₁, x₂) ↦ (x₀ + t x₂, √(1-t²) x₁, t x₀ + x₂)`. -/
noncomputable def boost : V3 ≃ₗ[ℝ] V3 where
  toFun v := ![v 0 + 3 / 5 * v 2, 4 / 5 * v 1, 3 / 5 * v 0 + v 2]
  invFun w := ![25 / 16 * (w 0 - 3 / 5 * w 2), 5 / 4 * w 1, 25 / 16 * (-(3 / 5) * w 0 + w 2)]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring
  left_inv v := by ext i; fin_cases i <;> simp <;> ring
  right_inv v := by ext i; fin_cases i <;> simp <;> ring

theorem boost_apply (v : V3) : boost v = ![v 0 + 3 / 5 * v 2, 4 / 5 * v 1, 3 / 5 * v 0 + v 2] := rfl

theorem boost_symm_apply (w : V3) :
    boost.symm w = ![25 / 16 * (w 0 - 3 / 5 * w 2), 5 / 4 * w 1, 25 / 16 * (-(3 / 5) * w 0 + w 2)] := rfl

theorem onGamma_boost (v : V3) : OnGamma (boost v) ↔ OnGamma v := by
  simp only [OnGamma, boost_apply]
  simp
  constructor <;> intro h <;> nlinarith [h]

theorem onGamma_boost_symm (v : V3) : OnGamma (boost.symm v) ↔ OnGamma v := by
  have := onGamma_boost (boost.symm v)
  simpa using this.symm

/-- The centre `(0,0)` of the unit circle, as a projective point. -/
def centre : V3 := ![0, 0, 1]

/-- The two points `(±1, 0)` of the circle (all their nonzero multiples). -/
def fixedPts : Set V3 := {v | v 1 = 0 ∧ v 2 ≠ 0 ∧ v 0 ^ 2 = v 2 ^ 2}

theorem boost_mem_fixedPts {v : V3} (hv : v ∈ fixedPts) : boost v ∈ fixedPts := by
  obtain ⟨h1, h2, h3⟩ := hv
  simp only [fixedPts, boost_apply, Set.mem_ofPred_eq]
  simp [h1]
  have : v 0 = v 2 ∨ v 0 = -v 2 := sq_eq_sq_iff_eq_or_eq_neg.mp h3
  rcases this with h | h <;> rw [h] <;> refine ⟨?_, by ring⟩ <;> intro h' <;> apply h2 <;> linarith

theorem boost_symm_mem_fixedPts {v : V3} (hv : v ∈ fixedPts) : boost.symm v ∈ fixedPts := by
  obtain ⟨h1, h2, h3⟩ := hv
  simp only [fixedPts, boost_symm_apply, Set.mem_ofPred_eq]
  simp [h1]
  have : v 0 = v 2 ∨ v 0 = -v 2 := sq_eq_sq_iff_eq_or_eq_neg.mp h3
  rcases this with h | h <;> rw [h]
  · refine ⟨?_, ?_⟩
    · intro h'; apply h2; linarith
    · ring
  · refine ⟨?_, ?_⟩
    · intro h'; apply h2; linarith
    · ring

theorem centre_ne_boost : ¬ ∃ c : ℝ, boost centre = c • centre := by
  rintro ⟨c, hc⟩
  have h0 := congrFun hc 0
  have h2 := congrFun hc 2
  simp [boost_apply, centre] at h0 h2

/-- **Theorem 19.18, p. 163 (the verification form).**  Let `S` be a set of data points fixed by the boost
`M` (which preserves the given circle `Γ`) and let `Z` be a candidate for the centre.  Everything that can
be constructed from `S` and `Z` with the ruler corresponds under `M` to what can be constructed from `S`
and `M Z`, and `M` preserves `Γ`.  Taking `Z` to be the centre `(0,0)`, the other candidate `M Z = (3/5, 0)`
is not the centre (`centre_ne_boost`), so no ruler-only construction can tell the two configurations
apart: the centre cannot be verified. -/
@[kb "petrunin2025" "Theorem 19.18, p. 163"]
theorem ruler_centre_indistinguishable {S : Set V3} (hS0 : (0 : V3) ∉ S) (hS : ∀ y ∈ S, boost y ∈ S)
    (hS' : ∀ y ∈ S, boost.symm y ∈ S) {Z : V3} (hZ : Z ≠ 0) (x : V3) :
    RConstr (insert Z S) x ↔ RConstr (insert (boost Z) S) (boost x) := by
  have hne : ∀ y ∈ S, y ≠ 0 := fun y hy h => hS0 (h ▸ hy)
  constructor
  · intro hx
    refine (hx.map boost onGamma_boost).mono ?_
    rintro _ ⟨y, hy | hy, rfl⟩
    · subst hy; exact .init (Set.mem_insert _ _) (by simpa using hZ)
    · exact .init (Set.mem_insert_of_mem _ (hS y hy)) (hne _ (hS y hy))
  · intro hx
    have := (hx.map boost.symm onGamma_boost_symm).mono (T := insert Z S) ?_
    · simpa using this
    rintro _ ⟨y, hy | hy, rfl⟩
    · subst hy; simpa using RConstr.init (S := insert Z S) (Set.mem_insert _ _) hZ
    · exact .init (Set.mem_insert_of_mem _ (hS' y hy)) (hne _ (hS' y hy))

/-- The line `x₁ = 0` (the horizontal diameter) as a submodule. -/
noncomputable def axisLine : Submodule ℝ V3 := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1)

theorem finrank_axisLine : Module.finrank ℝ axisLine = 2 := by
  have hr : LinearMap.range (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨Function.update 0 1 r, by simp⟩
  have := (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).finrank_range_add_finrank_ker
  rw [hr, finrank_top] at this
  simp at this
  exact Nat.add_left_cancel (n := 1) (this.trans (by norm_num))

theorem span_pair_eq_axisLine {p q : V3} (hp : p 1 = 0) (hq : q 1 = 0)
    (h : LinearIndependent ℝ ![p, q]) : Submodule.span ℝ {p, q} = axisLine := by
  have hle : Submodule.span ℝ {p, q} ≤ axisLine := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with rfl | hv
    · exact hp
    · exact (Set.mem_singleton_iff.mp hv ▸ hq)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_axisLine]
  have := finrank_span_eq_card h
  rw [Matrix.range_cons_cons_empty] at this
  simpa using this

/-- Points constructible from the two points `(±1, 0)` of the circle all lie on the circle and on the
horizontal diameter, so the centre is not among them. -/
theorem rconstr_fixedPts_inv {x : V3} (hx : RConstr fixedPts x) :
    x 1 = 0 ∧ x 0 ^ 2 = x 2 ^ 2 ∧ x ≠ 0 := by
  induction hx with
  | init hx _ =>
    obtain ⟨h1, h2, h3⟩ := hx
    exact ⟨h1, h3, fun h => h2 (by simp [h])⟩
  | @smul c x hc _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨by simp [h1], ?_, smul_ne_zero hc h3⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, mul_pow, h2]
  | @lineLine p q p' q' x _ _ _ _ h1 h2 h3 h4 h5 h6 ih1 ih2 ih3 ih4 =>
    exfalso
    exact h3 ((span_pair_eq_axisLine ih1.1 ih2.1 h1).trans (span_pair_eq_axisLine ih3.1 ih4.1 h2).symm)
  | @lineCircle p q x _ _ h1 h2 h3 h4 ih1 ih2 =>
    have hp : Submodule.span ℝ {p, q} ≤ axisLine := by
      rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | hv
      · exact ih1.1
      · exact (Set.mem_singleton_iff.mp hv ▸ ih2.1)
    have hx1 : x 1 = 0 := hp h2
    refine ⟨hx1, ?_, h3⟩
    have := h4
    simp only [OnGamma, hx1] at this
    linarith

/-- **Theorem 19.18, p. 163 (the constructibility form).**  The centre of the given circle is not
constructible with the ruler from the two points `(±1, 0)` of the circle. -/
@[kb "petrunin2025" "Theorem 19.18, p. 163"]
theorem centre_not_rconstr {c : ℝ} (hc : c ≠ 0) : ¬ RConstr fixedPts (c • centre) := by
  intro h
  have := (rconstr_fixedPts_inv h).2.1
  simp [centre] at this
  exact hc (pow_eq_zero_iff (two_ne_zero)|>.mp this.symm)

end CentreVerification

/-! ### Problem 19.16: circumtool and inversor -/

namespace CentreVerification

open OnePoint EuclideanGeometry

section CircInv

variable (V : Type*) {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Points constructible with a circumtool and an inversor from the data `S` and the given circline `Γ`
(Petrunin, Problem 19.16, p. 162), in the inversive plane `OnePoint P`.  The circumtool produces the
circline `C` through three distinct constructed points; the inversor sends a constructed point `y` to its
inverse in a constructed circline (the given `Γ`, or a circumcircline).  The inversion in a circline `C` is
described abstractly by its characteristic properties: it is an inversive transformation, an involution,
and its fixed point set is exactly `C` (for a circle `circOP Q s` it is `inversionEquiv Q s`).  Allowing every
such map only enlarges the tool, so an impossibility result here implies it for the genuine inversor. -/
inductive CIConstr (Γ S : Set (OnePoint P)) : OnePoint P → Prop
  | init {x : OnePoint P} : x ∈ S → CIConstr Γ S x
  | invGiven {g : OnePoint P ≃ OnePoint P} {y : OnePoint P} : IsCircline V Γ →
      IsInversiveTransformation V g → Function.Involutive g → {z | g z = z} = Γ →
      CIConstr Γ S y → CIConstr Γ S (g y)
  | invCirc {C : Set (OnePoint P)} {g : OnePoint P ≃ OnePoint P} {a b c y : OnePoint P} :
      CIConstr Γ S a → CIConstr Γ S b → CIConstr Γ S c → a ≠ b → a ≠ c → b ≠ c →
      a ∈ C → b ∈ C → c ∈ C → IsCircline V C →
      IsInversiveTransformation V g → Function.Involutive g → {z | g z = z} = C →
      CIConstr Γ S y → CIConstr Γ S (g y)

variable {V}

/-- Conjugating an inversive involution by an inversive transformation. -/
theorem conj_props {f g : OnePoint P ≃ OnePoint P} {C : Set (OnePoint P)}
    (hf : IsInversiveTransformation V f) (hg : IsInversiveTransformation V g)
    (hi : Function.Involutive g) (hfix : {z | g z = z} = C) :
    IsInversiveTransformation V (f.symm.trans (g.trans f)) ∧
      Function.Involutive (f.symm.trans (g.trans f)) ∧
      {z | (f.symm.trans (g.trans f)) z = z} = f '' C := by
  refine ⟨hf.symm.trans (hg.trans hf), ?_, ?_⟩
  · intro z
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hi]
    simp
  · ext z
    simp only [Set.mem_ofPred_eq, Equiv.trans_apply]
    constructor
    · intro h
      refine ⟨f.symm z, ?_, by simp⟩
      rw [← hfix]
      show g (f.symm z) = f.symm z
      have := congrArg f.symm h
      simpa using this
    · rintro ⟨w, hw, rfl⟩
      rw [← hfix] at hw
      have : g w = w := hw
      simp [this]

/-- Invariance of circumtool-and-inversor constructions under an inversive transformation preserving `Γ`. -/
theorem CIConstr.map {Γ S : Set (OnePoint P)} (f : OnePoint P ≃ OnePoint P)
    (hf : IsInversiveTransformation V f) (hΓ : f '' Γ = Γ) {x : OnePoint P}
    (hx : CIConstr V Γ S x) : CIConstr V Γ (f '' S) (f x) := by
  induction hx with
  | init h => exact .init ⟨_, h, rfl⟩
  | @invGiven g y hcl hg hi hfix _ ih =>
    obtain ⟨h1, h2, h3⟩ := conj_props hf hg hi hfix
    rw [hΓ] at h3
    have := CIConstr.invGiven (V := V) hcl h1 h2 h3 ih
    simpa using this
  | @invCirc C g a b c y _ _ _ hab hac hbc ha hb hc hcl hg hi hfix _ iha ihb ihc ihy =>
    obtain ⟨h1, h2, h3⟩ := conj_props hf hg hi hfix
    have := CIConstr.invCirc (V := V) (C := f '' C) iha ihb ihc (f.injective.ne hab) (f.injective.ne hac)
      (f.injective.ne hbc) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
      (by simpa using hf.1 _ hcl) h1 h2 h3 ihy
    simpa using this

theorem CIConstr.map_iff {Γ S : Set (OnePoint P)} (f : OnePoint P ≃ OnePoint P)
    (hf : IsInversiveTransformation V f) (hΓ : f '' Γ = Γ) (x : OnePoint P) :
    CIConstr V Γ S x ↔ CIConstr V Γ (f '' S) (f x) := by
  refine ⟨CIConstr.map f hf hΓ, fun h => ?_⟩
  have hΓ' : f.symm '' Γ = Γ := by
    conv_lhs => rw [← hΓ]
    rw [Set.image_image]; simp
  have := CIConstr.map f.symm hf.symm hΓ' h
  simpa [Set.image_image] using this

section Concrete

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] {O Q : P} {R s : ℝ}

omit [Fact (Module.finrank ℝ V = 2)] in
/-- An inversion in a circle `Ω` (centre `O`, radius `R`) orthogonal to `Γ = circOP Q s` (centre `Q`,
radius `s`, i.e. `|OQ|² = R² + s²`) maps `Γ` to itself (Petrunin, Corollary 10.16). -/
theorem inversionOP_image_orthogonal (hR : 0 < R) (hs : 0 < s) (hperp : dist Q O ^ 2 = R ^ 2 + s ^ 2) :
    inversionOP O R '' circOP Q s = circOP Q s := by
  have hd : dist Q O ≠ s := by
    intro h; rw [h] at hperp; nlinarith
  rw [inversionOP_image_circOP_of_ne hR.ne' hs hd]
  have hD : dist Q O ^ 2 - s ^ 2 = R ^ 2 := by linarith
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  simp only [invSphereCenter, invSphereRadius, hD, div_self hR2, AffineMap.lineMap_apply_one,
    abs_of_pos (pow_pos hR 2)]
  congr 2
  field_simp

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The inversion in the orthogonal circle moves the centre `Q` of `Γ` (Petrunin, Exercise 10.8). -/
theorem inversionOP_centre_ne (hR : 0 < R) (hs : 0 < s) (hperp : dist Q O ^ 2 = R ^ 2 + s ^ 2) :
    inversionOP O R (Q : OnePoint P) ≠ Q := by
  have hQO : Q ≠ O := by
    intro h; rw [h, dist_self] at hperp; nlinarith
  have hd : dist Q O ≠ s := by
    intro h; rw [h] at hperp; nlinarith
  rw [inversionOP_coe_of_ne hQO]
  intro h
  have h' := OnePoint.coe_injective h
  have hD : dist Q O ^ 2 - s ^ 2 = R ^ 2 := by linarith
  have := inversion_centre_ne_centre_image (O := O) (Q := Q) hR.ne' hs hd hQO
  apply this
  rw [h']
  simp only [invSphereCenter, hD, div_self (pow_ne_zero 2 hR.ne'), AffineMap.lineMap_apply_one]

omit [Fact (Module.finrank ℝ V = 2)] in
/-- The genuine inversion in a circle has exactly that circle as its fixed point set, so it is one of the
inversors allowed in `CIConstr`. -/
theorem inversionOP_fixed_eq (hs : 0 < s) : {z | inversionOP O s z = z} = circOP O s := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [infty_notMem_circOP]
  | coe x =>
    by_cases hx : x = O
    · subst hx; simp [mem_circOP_coe, hs.ne]
    · simp only [Set.mem_ofPred_eq, inversionOP_coe_of_ne hx, mem_circOP_coe, OnePoint.coe_eq_coe]
      have hpos : 0 < dist x O := dist_pos.mpr hx
      constructor
      · intro h
        have := congrArg (fun y => dist y O) h
        simp only [dist_inversion_center] at this
        have h2 : s ^ 2 = dist x O ^ 2 := by
          field_simp at this; nlinarith
        exact (sq_eq_sq₀ hpos.le hs.le).mp h2.symm
      · intro h
        rw [inversion, h, div_self hs.ne']
        simp

/-- **Problem 19.16, p. 162.**  Let `Γ` be a circle with centre `Q`, let `Ω` be a circle (centre `O`,
radius `R`) orthogonal to `Γ`, and let the data points `S` be invariant under the inversion `f` in `Ω`
(for instance points of `Ω`).  Whatever a circumtool and an inversor construct from the data `S` together
with a candidate centre `Z`, they construct, mirrored by `f`, from `S` together with `f Z`.  For `Z = Q`
the mirrored candidate `f Q` is not the centre (`inversionOP_centre_ne`, and the image circle is `Γ`
again), so no construction can verify that a point is the centre of `Γ`. -/
@[kb "petrunin2025" "Problem 19.16, p. 162"]
theorem circumtool_inversor_centre_indistinguishable (hR : 0 < R) (hs : 0 < s)
    (hperp : dist Q O ^ 2 = R ^ 2 + s ^ 2) {S : Set (OnePoint P)} (hS : inversionOP O R '' S = S)
    (Z x : OnePoint P) :
    CIConstr V (circOP Q s) (insert Z S) x ↔
      CIConstr V (circOP Q s) (insert (inversionOP O R Z) S) (inversionOP O R x) := by
  have key := CIConstr.map_iff (V := V) (S := insert Z S) (inversionEquiv O R hR.ne')
    (isInversiveTransformation_inversionEquiv hR) (inversionOP_image_orthogonal hR hs hperp) x
  have himg : (inversionEquiv O R hR.ne') '' insert Z S = insert (inversionOP O R Z) S := by
    rw [Set.image_insert_eq]
    exact congrArg _ hS
  rw [himg] at key
  exact key

end Concrete

end CircInv

end CentreVerification

end UndergradKB.Geometry
