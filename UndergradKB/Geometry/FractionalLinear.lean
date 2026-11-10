import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import UndergradKB.Common.Attr

/-! # Fractional linear maps of the extended complex plane (Petrunin, Section 18F, p. 153)

The extended complex plane `Ĉ = ℂ ∪ {∞}` is Mathlib's `OnePoint ℂ`. A fractional linear map
`z ↦ (az + b)/(cz + d)` with `ad - bc ≠ 0` is the action of the invertible matrix
`[[a, b], [c, d]] ∈ GL(2, ℂ)` on `OnePoint ℂ` (Mathlib's `OnePoint.instGLAction`, with
`-d/c ↦ ∞` and `∞ ↦ a/c`). The elementary transformations are `z ↦ z + w`, `z ↦ a z` (`a ≠ 0`) and
`z ↦ 1/z` (with `0 ↔ ∞`). Proposition 18.12: a map of `Ĉ` is fractional linear iff it is a
composition of elementary transformations. -/

namespace UndergradKB.Geometry.FractionalLinear

open Matrix OnePoint

/-- A map of `Ĉ = OnePoint ℂ` is *fractional linear* (p. 153) if it is `z ↦ (az+b)/(cz+d)` for an
invertible matrix `[[a, b], [c, d]]`, i.e. the action of some `g ∈ GL(2, ℂ)`. -/
def IsFractionalLinear (f : OnePoint ℂ → OnePoint ℂ) : Prop :=
  ∃ g : GL (Fin 2) ℂ, ∀ x, f x = g • x

/-- The translation `z ↦ z + w` of `Ĉ` (fixing `∞`). -/
def translate (w : ℂ) : Function.End (OnePoint ℂ) := OnePoint.map (fun z => z + w)

/-- The rotational homothety `z ↦ a z` of `Ĉ` (fixing `∞`). -/
def scale (a : ℂ) : Function.End (OnePoint ℂ) := OnePoint.map (fun z => a * z)

/-- The map `z ↦ 1/z` of `Ĉ`, exchanging `0` and `∞`. -/
noncomputable def inv : Function.End (OnePoint ℂ)
  | Option.none => ((0 : ℂ) : OnePoint ℂ)
  | Option.some z => if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ)

theorem inv_infty : inv ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

theorem inv_coe (z : ℂ) : inv z = if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ) := rfl

/-- The elementary transformations of `Ĉ` (p. 153): translations, rotational homotheties
`z ↦ a z` with `a ≠ 0`, and `z ↦ 1/z`. -/
def elementary : Set (Function.End (OnePoint ℂ)) :=
  {f | (∃ w, f = translate w) ∨ (∃ a ≠ 0, f = scale a) ∨ f = inv}

/-- The matrix `[[a, b], [c, d]]` as an element of `GL(2, ℂ)` when `ad - bc ≠ 0`. -/
noncomputable def glOf (a b c d : ℂ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [det_fin_two] using h)

@[simp] theorem glOf_apply (a b c d : ℂ) (h : a * d - b * c ≠ 0) (i j : Fin 2) :
    (glOf a b c d h) i j = !![a, b; c, d] i j := rfl

theorem glOf_smul_coe (a b c d : ℂ) (h : a * d - b * c ≠ 0) (z : ℂ) :
    glOf a b c d h • (z : OnePoint ℂ) =
      if c * z + d = 0 then ∞ else (((a * z + b) / (c * z + d) : ℂ) : OnePoint ℂ) := by
  rw [smul_some_eq_ite]; simp

theorem glOf_smul_infty (a b c d : ℂ) (h : a * d - b * c ≠ 0) :
    glOf a b c d h • (∞ : OnePoint ℂ) = if c = 0 then ∞ else ((a / c : ℂ) : OnePoint ℂ) := by
  rw [smul_infty_eq_ite]; simp

theorem translate_eq (w : ℂ) : translate w = fun x => glOf 1 w 0 1 (by simp) • x := by
  funext x
  induction x using OnePoint.rec with
  | infty => simp [translate, glOf_smul_infty]
  | coe z => simp [translate, glOf_smul_coe]

theorem scale_eq {a : ℂ} (ha : a ≠ 0) : scale a = fun x => glOf a 0 0 1 (by simpa using ha) • x := by
  funext x
  induction x using OnePoint.rec with
  | infty => simp [scale, glOf_smul_infty]
  | coe z => simp [scale, glOf_smul_coe]

theorem inv_eq : inv = fun x => glOf 0 1 1 0 (by simp) • x := by
  funext x
  induction x using OnePoint.rec with
  | infty => simp [inv_infty, glOf_smul_infty]
  | coe z =>
    simp only [inv_coe, glOf_smul_coe]
    by_cases hz : z = 0 <;> simp [hz]

/-- Two matrices that are proportional act in the same way on `Ĉ`. -/
theorem smul_eq_of_proportional {g h : GL (Fin 2) ℂ} {t : ℂ} (ht : t ≠ 0)
    (hgh : ∀ i j, h i j = t * g i j) (x : OnePoint ℂ) : h • x = g • x := by
  induction x using OnePoint.rec with
  | infty =>
    rw [smul_infty_eq_ite, smul_infty_eq_ite, hgh, hgh]
    simp only [mul_eq_zero, ht, false_or]
    split_ifs
    · rfl
    · rw [mul_div_mul_left _ _ ht]
  | coe z =>
    rw [smul_some_eq_ite, smul_some_eq_ite, hgh, hgh, hgh, hgh]
    have e1 : t * g 1 0 * z + t * g 1 1 = t * (g 1 0 * z + g 1 1) := by ring
    have e2 : t * g 0 0 * z + t * g 0 1 = t * (g 0 0 * z + g 0 1) := by ring
    rw [e1, e2]
    simp only [mul_eq_zero, ht, false_or]
    split_ifs
    · rfl
    · rw [mul_div_mul_left _ _ ht]

theorem isFractionalLinear_of_mem_closure {f : Function.End (OnePoint ℂ)}
    (hf : f ∈ Submonoid.closure elementary) : IsFractionalLinear f := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    rcases hf with ⟨w, rfl⟩ | ⟨a, ha, rfl⟩ | rfl
    · exact ⟨_, fun x => congrFun (translate_eq w) x⟩
    · exact ⟨_, fun x => congrFun (scale_eq ha) x⟩
    · exact ⟨_, fun x => congrFun inv_eq x⟩
  | one => exact ⟨1, fun x => (one_smul _ x).symm⟩
  | mul f g _ _ hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a * b, fun x => by
      show f (g x) = _
      rw [hb, ha, mul_smul]⟩

private theorem mem_closure_of_eq {f : Function.End (OnePoint ℂ)} (g : GL (Fin 2) ℂ)
    (hf : ∀ x, f x = g • x) (l : List (Function.End (OnePoint ℂ)))
    (hl : ∀ e ∈ l, e ∈ elementary) (hprod : ∀ x, l.prod x = g • x) :
    f ∈ Submonoid.closure elementary := by
  have : f = l.prod := by funext x; rw [hf, hprod]
  rw [this]
  exact Submonoid.list_prod_mem _ fun e he => Submonoid.subset_closure (hl e he)

/-- **Proposition 18.12 (p. 153).** A map of the extended complex plane `Ĉ` is fractional linear iff
it is a composition of elementary transformations (translations, `z ↦ a z` with `a ≠ 0`, and
`z ↦ 1/z`). -/
@[kb "petrunin2025" "Proposition 18.12, p. 153"]
theorem isFractionalLinear_iff_mem_closure (f : Function.End (OnePoint ℂ)) :
    IsFractionalLinear f ↔ f ∈ Submonoid.closure elementary := by
  refine ⟨fun ⟨g, hg⟩ => ?_, isFractionalLinear_of_mem_closure⟩
  set a := g 0 0
  set b := g 0 1
  set c := g 1 0
  set d := g 1 1
  have hdet : a * d - b * c ≠ 0 := by
    have := g.det_ne_zero
    rwa [det_fin_two] at this
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by rintro hd; apply hdet; rw [hd, hc]; ring
    have ha : a ≠ 0 := by rintro ha; apply hdet; rw [ha, hc]; ring
    have had : a / d ≠ 0 := div_ne_zero ha hd
    refine mem_closure_of_eq g hg [translate (b / d), scale (a / d)] ?_ ?_
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inl ⟨_, had, rfl⟩)
    · intro x
      simp only [List.prod_cons, List.prod_nil, mul_one]
      show translate (b / d) (scale (a / d) x) = g • x
      rw [translate_eq, scale_eq had]
      simp only [← mul_smul]
      refine smul_eq_of_proportional (t := d⁻¹) (inv_ne_zero hd) (fun i j => ?_) x
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d, hc] <;>
        field_simp [show (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 from hd]
  · have hD : -((a * d - b * c) / c ^ 2) ≠ 0 := by
      have := pow_ne_zero 2 hc
      exact neg_ne_zero.2 (div_ne_zero hdet this)
    refine mem_closure_of_eq g hg
      [translate (a / c), scale (-((a * d - b * c) / c ^ 2)), inv,
        translate (d / c)] ?_ ?_
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inl ⟨_, hD, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨_, rfl⟩
    · intro x
      simp only [List.prod_cons, List.prod_nil, mul_one]
      show translate (a / c) (scale _ (inv (translate (d / c) x))) = g • x
      rw [translate_eq, translate_eq, scale_eq hD, inv_eq]
      simp only [← mul_smul]
      refine smul_eq_of_proportional (t := c⁻¹) (inv_ne_zero hc) (fun i j => ?_) x
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d] <;>
        field_simp [show (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 from hc] <;> ring

end UndergradKB.Geometry.FractionalLinear
