import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import UndergradKB.Common.Attr
import UndergradKB.ComplexAnalysis.Mobius

/-! # The extended plane and the Riemann sphere (rows CX-040, CX-044, CX-045)

* The extended plane is Mathlib's `OnePoint ℂ`.  A Mobius map with nonzero determinant extends
  to a bijection of it; we write the extension explicitly and identify it with the `GL₂(ℂ)` action.
* The unit sphere in `ℝ × ℝ × ℝ` is identified with `OnePoint ℂ` by stereographic projection from
  the north pole `(0,0,1)`.
* Plane sections of the sphere correspond to generalized circles of `ℂ` (the `genCircle` of
  `UndergradKB.ComplexAnalysis.Mobius`), and every generalized circle arises this way. -/

namespace UndergradKB.ComplexAnalysis

/-! ## Extension of a Mobius map to the extended plane -/

open scoped Classical in
/-- The extension of `z ↦ (a z + b)/(c z + d)` to `OnePoint ℂ`: a finite point with vanishing
denominator goes to `∞`, and `∞` goes to `a/c` (or to `∞` when `c = 0`). -/
noncomputable def mobiusExt (a b c d : ℂ) : OnePoint ℂ → OnePoint ℂ :=
  fun x => x.elim (if c = 0 then OnePoint.infty else ((a / c : ℂ) : OnePoint ℂ))
    (fun z => if c * z + d = 0 then OnePoint.infty else ((mobius a b c d z : ℂ) : OnePoint ℂ))

/-- The invertible matrix `[[a, b], [c, d]]` of a Mobius map. -/
noncomputable def mobiusMatrix {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [Matrix.det_fin_two_of] using h)

@[simp] theorem mobiusMatrix_apply {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    (mobiusMatrix h) 0 0 = a ∧ (mobiusMatrix h) 0 1 = b ∧ (mobiusMatrix h) 1 0 = c ∧
      (mobiusMatrix h) 1 1 = d := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The explicit extension is the `GL₂(ℂ)` action of Mathlib on `OnePoint ℂ`. -/
theorem mobiusExt_eq_smul {a b c d : ℂ} (h : a * d - b * c ≠ 0) (x : OnePoint ℂ) :
    mobiusExt a b c d x = mobiusMatrix h • x := by
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    simp only [mobiusExt, OnePoint.elim_infty, (mobiusMatrix_apply h).1,
      (mobiusMatrix_apply h).2.1, (mobiusMatrix_apply h).2.2.1, (mobiusMatrix_apply h).2.2.2]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    simp only [mobiusExt, OnePoint.elim_some, (mobiusMatrix_apply h).1,
      (mobiusMatrix_apply h).2.1, (mobiusMatrix_apply h).2.2.1, (mobiusMatrix_apply h).2.2.2]
    by_cases hz : c * z + d = 0
    · simp [hz]
    · simp [hz, mobius]

/-- Beck Definition 3.2.4 / Corollary 3.2.5 (CX-040). A Mobius map (`a d - b c ≠ 0`) extends to a
bijection of the extended plane `OnePoint ℂ`. -/
@[kb "beck2025" "Corollary 3.2.5, p. 52"]
theorem mobiusExt_bijective {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    Function.Bijective (mobiusExt a b c d) := by
  have : mobiusExt a b c d = fun x => mobiusMatrix h • x := funext (mobiusExt_eq_smul h)
  rw [this]
  exact MulAction.bijective _

/-- The extension of a Mobius map as an equivalence of `OnePoint ℂ`. -/
noncomputable def mobiusExtEquiv {a b c d : ℂ} (h : a * d - b * c ≠ 0) : OnePoint ℂ ≃ OnePoint ℂ :=
  Equiv.ofBijective _ (mobiusExt_bijective h)

/-- Beck Corollary 3.2.5 (CX-040): for `c ≠ 0` the pole `-d/c` goes to `∞` and `∞` goes to `a/c`. -/
@[kb "beck2025" "Corollary 3.2.5, p. 52"]
theorem mobiusExt_pole {a b c d : ℂ} (hc : c ≠ 0) :
    mobiusExt a b c d ((-d / c : ℂ) : OnePoint ℂ) = OnePoint.infty ∧
    mobiusExt a b c d OnePoint.infty = ((a / c : ℂ) : OnePoint ℂ) := by
  constructor
  · have : c * (-d / c) + d = 0 := by field_simp; ring
    simp [mobiusExt, this]
  · simp [mobiusExt, hc]

/-- Beck Corollary 3.2.5 (CX-040): for `c = 0` the point `∞` is fixed. -/
@[kb "beck2025" "Corollary 3.2.5, p. 52"]
theorem mobiusExt_infty_of_c_eq_zero {a b d : ℂ} :
    mobiusExt a b 0 d OnePoint.infty = OnePoint.infty := by
  simp [mobiusExt]

/-- On finite points with nonvanishing denominator the extension is `mobius`. -/
theorem mobiusExt_coe {a b c d z : ℂ} (hz : c * z + d ≠ 0) :
    mobiusExt a b c d (z : OnePoint ℂ) = ((mobius a b c d z : ℂ) : OnePoint ℂ) := by
  simp [mobiusExt, hz]

/-! ## Stereographic projection -/

/-- The unit sphere in `ℝ³`. -/
def unitSphere : Set (ℝ × ℝ × ℝ) := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The north pole. -/
def northPole : ℝ × ℝ × ℝ := (0, 0, 1)

/-- Beck Definition 3.3.1 (CX-044): stereographic projection from the north pole,
`(x₁,x₂,x₃) ↦ (x₁ + i x₂)/(1 - x₃)`. -/
@[kb "beck2025" "Definition 3.3.1, p. 54"]
noncomputable def stereo (p : ℝ × ℝ × ℝ) : ℂ := ⟨p.1 / (1 - p.2.2), p.2.1 / (1 - p.2.2)⟩

/-- Beck Proposition 3.3.3 (CX-044): the inverse map
`z ↦ (2 Re z, 2 Im z, |z|² - 1)/(|z|² + 1)`. -/
@[kb "beck2025" "Proposition 3.3.3, p. 55"]
noncomputable def stereoInv (z : ℂ) : ℝ × ℝ × ℝ :=
  (2 * z.re / (Complex.normSq z + 1), 2 * z.im / (Complex.normSq z + 1),
    (Complex.normSq z - 1) / (Complex.normSq z + 1))

theorem northPole_mem : northPole ∈ unitSphere := by simp [northPole, unitSphere]

theorem stereoInv_mem (z : ℂ) : stereoInv z ∈ unitSphere := by
  have h : 0 < Complex.normSq z + 1 := by linarith [Complex.normSq_nonneg z]
  simp only [stereoInv, unitSphere, Set.mem_ofPred_eq]
  rw [Complex.normSq_apply] at *
  field_simp
  ring

theorem stereoInv_ne_north (z : ℂ) : stereoInv z ≠ northPole := by
  have h : 0 < Complex.normSq z + 1 := by linarith [Complex.normSq_nonneg z]
  intro e
  have := congrArg (fun p => p.2.2) e
  simp only [stereoInv, northPole] at this
  rw [div_eq_one_iff_eq h.ne'] at this
  linarith

/-- Beck Proposition 3.3.3 (CX-044): `stereo ∘ stereoInv = id` on `ℂ`. -/
@[kb "beck2025" "Proposition 3.3.3, p. 55"]
theorem stereo_stereoInv (z : ℂ) : stereo (stereoInv z) = z := by
  have h : 0 < Complex.normSq z + 1 := by linarith [Complex.normSq_nonneg z]
  have h2 : 1 - (Complex.normSq z - 1) / (Complex.normSq z + 1) = 2 / (Complex.normSq z + 1) := by
    field_simp; ring
  apply Complex.ext <;> simp only [stereo, stereoInv] <;> rw [h2] <;> field_simp

theorem sphere_third_ne_one {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (hN : p ≠ northPole) :
    1 - p.2.2 ≠ 0 := by
  intro h
  have h3 : p.2.2 = 1 := by linarith
  simp only [unitSphere, Set.mem_ofPred_eq] at hp
  rw [h3] at hp
  have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  have h2 : p.2.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  exact hN (Prod.ext h1 (Prod.ext h2 h3))

/-- Beck Proposition 3.3.3 (CX-044): `stereoInv ∘ stereo = id` on the sphere minus the north pole. -/
@[kb "beck2025" "Proposition 3.3.3, p. 55"]
theorem stereoInv_stereo {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (hN : p ≠ northPole) :
    stereoInv (stereo p) = p := by
  have ht := sphere_third_ne_one hp hN
  have hp' : p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1 := hp
  have hs : Complex.normSq (stereo p) = (1 + p.2.2) / (1 - p.2.2) := by
    simp only [stereo, Complex.normSq_apply]
    field_simp
    linear_combination hp'
  have hs1 : Complex.normSq (stereo p) + 1 = 2 / (1 - p.2.2) := by
    rw [hs]; field_simp; ring
  have hs2 : Complex.normSq (stereo p) - 1 = 2 * p.2.2 / (1 - p.2.2) := by
    rw [hs]; field_simp; ring
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show 2 * (p.1 / (1 - p.2.2)) / (Complex.normSq (stereo p) + 1) = p.1
    rw [hs1]; field_simp
  · show 2 * (p.2.1 / (1 - p.2.2)) / (Complex.normSq (stereo p) + 1) = p.2.1
    rw [hs1]; field_simp
  · simp only [stereoInv]; rw [hs1, hs2]; field_simp

/-- Beck Proposition 3.3.3 (CX-044), extended to the Riemann sphere: the unit sphere is in
bijection with `OnePoint ℂ`, the north pole going to `∞`. -/
@[kb "beck2025" "Proposition 3.3.3, p. 55"]
noncomputable def sphereEquivOnePoint : unitSphere ≃ OnePoint ℂ where
  toFun p := open scoped Classical in
    if p.1 = northPole then OnePoint.infty else ((stereo p.1 : ℂ) : OnePoint ℂ)
  invFun x := x.elim ⟨northPole, northPole_mem⟩ (fun z => ⟨stereoInv z, stereoInv_mem z⟩)
  left_inv := by
    intro p
    by_cases h : p.1 = northPole
    · simp [h]
      exact Subtype.ext h.symm
    · simp only [h, if_false, OnePoint.elim_some]
      exact Subtype.ext (stereoInv_stereo p.2 h)
  right_inv := by
    intro x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z =>
      simp [stereoInv_ne_north z, stereo_stereoInv]

/-! ## Circles on the sphere -/

/-- The plane `a₁ x₁ + a₂ x₂ + a₃ x₃ = b`. -/
def plane (a1 a2 a3 b : ℝ) : Set (ℝ × ℝ × ℝ) := {p | a1 * p.1 + a2 * p.2.1 + a3 * p.2.2 = b}

theorem stereoInv_mem_plane_iff (a1 a2 a3 b : ℝ) (z : ℂ) :
    stereoInv z ∈ plane a1 a2 a3 b ↔
      z ∈ genCircle (a3 - b) ⟨a1, a2⟩ (-(a3 + b)) := by
  have h : 0 < Complex.normSq z + 1 := by linarith [Complex.normSq_nonneg z]
  have key : a1 * (stereoInv z).1 + a2 * (stereoInv z).2.1 + a3 * (stereoInv z).2.2 - b =
      circE (a3 - b) ⟨a1, a2⟩ (-(a3 + b)) z / (Complex.normSq z + 1) := by
    simp only [stereoInv, circE, Complex.normSq_apply]
    rw [Complex.normSq_apply] at h
    field_simp
    ring
  simp only [plane, genCircle, Set.mem_ofPred_eq]
  rw [← sub_eq_zero, key, div_eq_zero_iff]
  simp [h.ne']

/-- Beck Theorem 3.3.4 (CX-045), circles to circles: if the plane `a·x = b` cuts the sphere in
a circle (condition `b² < |a|²`, equivalent to meeting the sphere in more than one point), the
stereographic image of the circle minus the north pole is a generalized circle of `ℂ`, namely
`(a₃ - b)|z|² + 2 Re(conj(a₁ + i a₂) z) - (a₃ + b) = 0`; it is a line exactly when the plane passes
through the north pole (`a₃ = b`). -/
@[kb "beck2025" "Theorem 3.3.4, p. 55"]
theorem stereo_image_plane_section (a1 a2 a3 b : ℝ) (hb : b ^ 2 < a1 ^ 2 + a2 ^ 2 + a3 ^ 2) :
    GenCircleParam (a3 - b) ⟨a1, a2⟩ (-(a3 + b)) ∧
    stereo '' {p | p ∈ unitSphere ∧ p ≠ northPole ∧ p ∈ plane a1 a2 a3 b} =
      genCircle (a3 - b) ⟨a1, a2⟩ (-(a3 + b)) := by
  refine ⟨?_, ?_⟩
  · unfold GenCircleParam; simp only; nlinarith
  · ext z
    constructor
    · rintro ⟨p, ⟨hp, hN, hpl⟩, rfl⟩
      rw [← stereoInv_mem_plane_iff, stereoInv_stereo hp hN]
      exact hpl
    · intro hz
      refine ⟨stereoInv z, ⟨stereoInv_mem z, stereoInv_ne_north z, ?_⟩, stereo_stereoInv z⟩
      exact (stereoInv_mem_plane_iff a1 a2 a3 b z).mpr hz

/-- Beck Theorem 3.3.4 (CX-045), the line case: the plane passes through the north pole
iff `a₃ = b`, i.e. the leading coefficient `a₃ - b` of the generalized circle vanishes. -/
@[kb "beck2025" "Theorem 3.3.4, p. 55"]
theorem northPole_mem_plane_iff (a1 a2 a3 b : ℝ) :
    northPole ∈ plane a1 a2 a3 b ↔ a3 - b = 0 := by
  simp only [northPole, plane, Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Beck Theorem 3.3.4 (CX-045), converse: every generalized circle of `ℂ` is the stereographic
image of a plane section of the sphere (minus the north pole). -/
@[kb "beck2025" "Theorem 3.3.4, p. 55"]
theorem exists_plane_of_genCircle {α : ℝ} {β : ℂ} {γ : ℝ} (h : GenCircleParam α β γ) :
    ∃ a1 a2 a3 b : ℝ, b ^ 2 < a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ∧
      stereo '' {p | p ∈ unitSphere ∧ p ≠ northPole ∧ p ∈ plane a1 a2 a3 b} =
        genCircle α β γ := by
  refine ⟨β.re, β.im, (α - γ) / 2, -(α + γ) / 2, ?_, ?_⟩
  · unfold GenCircleParam at h; nlinarith
  · have hb : (-(α + γ) / 2) ^ 2 < β.re ^ 2 + β.im ^ 2 + ((α - γ) / 2) ^ 2 := by
      unfold GenCircleParam at h; nlinarith
    have := (stereo_image_plane_section β.re β.im ((α - γ) / 2) (-(α + γ) / 2) hb).2
    convert this using 2 <;> ring

end UndergradKB.ComplexAnalysis
