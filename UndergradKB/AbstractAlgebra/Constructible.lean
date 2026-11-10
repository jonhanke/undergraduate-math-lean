import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.KummerPolynomial
import UndergradKB.Common.Attr
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-! # Judson–Beezer, section 21.3: geometric constructions

Straightedge-and-compass constructions are modelled in the complex plane.  `ConstructiblePt` is the
inductive set of points obtainable from `0` and `1` by intersecting lines through two constructed
points and circles with a constructed centre through a constructed point.  A real number `x` is
`Constructible` when the point `x` on the real axis is constructible (equivalently when `|x|` is the
distance of two constructible points; equivalently when it is a coordinate of a constructible point,
see `constructiblePt_iff`).
-/

namespace UndergradKB.AbstractAlgebra

open Complex

/-- `p` lies on the line through `a` and `b`. -/
def OnLine (a b p : ℂ) : Prop := ∃ t : ℝ, p = a + t * (b - a)

/-- The cross product of two plane vectors; nonzero iff the vectors are not parallel. -/
def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- AA-390. The points of the plane constructible with straightedge and compass from `0` and `1`:
new points are intersections of two lines (through constructed points, not parallel), of a line and
a circle (centre constructed, through a constructed point) or of two circles with distinct centres. -/
@[kb "judson2026" "Definition (unnumbered, 21.3.1), p. 295"]
inductive ConstructiblePt : ℂ → Prop
  | zero : ConstructiblePt 0
  | one : ConstructiblePt 1
  | lineLine {a b c d p : ℂ} : ConstructiblePt a → ConstructiblePt b → ConstructiblePt c →
      ConstructiblePt d → cross (b - a) (d - c) ≠ 0 → OnLine a b p → OnLine c d p →
      ConstructiblePt p
  | lineCircle {a b c d p : ℂ} : ConstructiblePt a → ConstructiblePt b → ConstructiblePt c →
      ConstructiblePt d → a ≠ b → OnLine a b p → ‖p - c‖ = ‖d - c‖ → ConstructiblePt p
  | circleCircle {c₁ d₁ c₂ d₂ p : ℂ} : ConstructiblePt c₁ → ConstructiblePt d₁ →
      ConstructiblePt c₂ → ConstructiblePt d₂ → c₁ ≠ c₂ → ‖p - c₁‖ = ‖d₁ - c₁‖ →
      ‖p - c₂‖ = ‖d₂ - c₂‖ → ConstructiblePt p

/-- AA-390. A real number is constructible when the corresponding point of the real axis is. -/
@[kb "judson2026" "Definition (unnumbered, 21.3.1), p. 295"]
def Constructible (x : ℝ) : Prop := ConstructiblePt (x : ℂ)

section geometry

local notation "CP" => ConstructiblePt

lemma norm_eq_iff (z w : ℂ) : ‖z‖ = ‖w‖ ↔ z.re ^ 2 + z.im ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  constructor <;> intro h <;> nlinarith

lemma onLine_iff (a b p : ℂ) : OnLine a b p ↔
    ∃ t : ℝ, p.re = a.re + t * (b.re - a.re) ∧ p.im = a.im + t * (b.im - a.im) := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨t, by simp [h], by simp [h]⟩
  · rintro ⟨t, h1, h2⟩
    exact ⟨t, Complex.ext (by simp [h1]) (by simp [h2])⟩

lemma cp_reflect {a b : ℂ} (ha : CP a) (hb : CP b) : CP (2 * b - a) := by
  by_cases h : a = b
  · subst h; convert ha using 1; ring
  refine ConstructiblePt.lineCircle ha hb hb ha h ⟨2, by push_cast; ring⟩ ?_
  rw [norm_eq_iff]; simp; ring

/-- the apex of the equilateral triangle on `a b` (for `k = ±√3`). -/
noncomputable def apex (a b : ℂ) (k : ℝ) : ℂ :=
  ⟨a.re + (b.re - a.re) / 2 - (b.im - a.im) * k / 2,
   a.im + (b.im - a.im) / 2 + (b.re - a.re) * k / 2⟩

lemma sq_pos_of_ne {a b : ℂ} (h : a ≠ b) : 0 < (b.re - a.re) ^ 2 + (b.im - a.im) ^ 2 := by
  by_contra hc
  apply h
  have h1 : b.re - a.re = 0 := by nlinarith [sq_nonneg (b.re - a.re), sq_nonneg (b.im - a.im)]
  have h2 : b.im - a.im = 0 := by nlinarith [sq_nonneg (b.re - a.re), sq_nonneg (b.im - a.im)]
  exact Complex.ext (by linarith) (by linarith)

lemma cp_apex {a b : ℂ} {k : ℝ} (hk : k ^ 2 = 3) (ha : CP a) (hb : CP b) (hab : a ≠ b) :
    CP (apex a b k) := by
  refine ConstructiblePt.circleCircle ha hb hb ha hab ?_ ?_ <;> rw [norm_eq_iff] <;>
    simp [apex] <;>
    linear_combination (((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2) / 4) * hk

lemma cp_mid {a b : ℂ} (ha : CP a) (hb : CP b) : CP ((a + b) / 2) := by
  by_cases hab : a = b
  · subst hab; convert ha using 1; ring
  have hk : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hk' : (-Real.sqrt 3) ^ 2 = 3 := by rw [neg_sq]; exact hk
  have hk0 : Real.sqrt 3 ≠ 0 := by
    intro h; rw [h] at hk; norm_num at hk
  have hp := cp_apex hk ha hb hab
  have hq := cp_apex hk' ha hb hab
  have hpos := sq_pos_of_ne hab
  refine ConstructiblePt.lineLine hp hq ha hb ?_ ?_ ?_
  · simp [cross, apex]
    intro h
    have : Real.sqrt 3 * ((b.re - a.re) ^ 2 + (b.im - a.im) ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hk0 h
    · linarith
  · rw [onLine_iff]; refine ⟨1 / 2, ?_, ?_⟩ <;> simp [apex] <;> ring
  · rw [onLine_iff]; refine ⟨1 / 2, ?_, ?_⟩ <;> simp <;> ring

lemma cp_neg {a : ℂ} (ha : CP a) : CP (-a) := by
  convert cp_reflect ha ConstructiblePt.zero using 1; ring

lemma cp_add {a b : ℂ} (ha : CP a) (hb : CP b) : CP (a + b) := by
  by_cases hab : a = b
  · subst hab; convert cp_reflect ConstructiblePt.zero ha using 1; ring
  convert cp_reflect ConstructiblePt.zero (cp_mid ha hb) using 1; ring

lemma cp_half {z : ℂ} (hz : CP z) : CP (z / 2) := by
  convert cp_mid ConstructiblePt.zero hz using 1; ring

lemma cp_I : CP Complex.I := by
  have hk : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hk0 : Real.sqrt 3 ≠ 0 := by
    intro h; rw [h] at hk; norm_num at hk
  have h1 : CP (-1) := cp_neg ConstructiblePt.one
  have hp := cp_apex hk h1 ConstructiblePt.one (by
    intro h; have := congrArg Complex.re h; norm_num at this)
  refine ConstructiblePt.lineCircle ConstructiblePt.zero hp ConstructiblePt.zero
    ConstructiblePt.one ?_ ⟨1 / Real.sqrt 3, ?_⟩ ?_
  · intro h
    have := congrArg Complex.im h
    simp [apex] at this
    apply hk0; linarith
  · apply Complex.ext <;> simp [apex] <;> field_simp <;> linarith [hk]
  · rw [norm_eq_iff]; simp

lemma cp_mulI {x : ℝ} (hx : CP (x : ℂ)) : CP (Complex.I * x) := by
  refine ConstructiblePt.lineCircle ConstructiblePt.zero cp_I ConstructiblePt.zero hx
    (by intro h; have := congrArg Complex.im h; simp at this) ⟨x, by ring⟩ ?_
  rw [norm_eq_iff]; simp

lemma cp_of_mulI {y : ℝ} (hy : CP (Complex.I * y)) : CP (y : ℂ) := by
  refine ConstructiblePt.lineCircle ConstructiblePt.zero ConstructiblePt.one
    ConstructiblePt.zero hy (by intro h; have := congrArg Complex.re h; simp at this)
    ⟨y, by simp⟩ ?_
  rw [norm_eq_iff]; simp

lemma cp_re {p : ℂ} (hp : CP p) : CP (p.re : ℂ) := by
  have h : CP ((2 * p.re : ℝ) : ℂ) := by
    refine ConstructiblePt.lineCircle ConstructiblePt.zero ConstructiblePt.one hp
      ConstructiblePt.zero (by intro h; have := congrArg Complex.re h; simp at this)
      ⟨2 * p.re, by simp⟩ ?_
    rw [norm_eq_iff]; simp; ring
  convert cp_half h using 1; push_cast; ring

lemma cp_im {p : ℂ} (hp : CP p) : CP (p.im : ℂ) := by
  have h : CP (Complex.I * ((2 * p.im : ℝ) : ℂ)) := by
    refine ConstructiblePt.lineCircle ConstructiblePt.zero cp_I hp
      ConstructiblePt.zero (by intro h; have := congrArg Complex.im h; simp at this)
      ⟨2 * p.im, by simp; ring⟩ ?_
    rw [norm_eq_iff]; simp; ring
  apply cp_of_mulI
  convert cp_half h using 1; push_cast; ring

lemma cp_of_coords {x y : ℝ} (hx : CP (x : ℂ)) (hy : CP (y : ℂ)) : CP (⟨x, y⟩ : ℂ) := by
  convert cp_add hx (cp_mulI hy) using 1
  apply Complex.ext <;> simp

lemma cp_mul {x y : ℝ} (hx : CP (x : ℂ)) (hy : CP (y : ℂ)) : CP ((x * y : ℝ) : ℂ) := by
  have hA := cp_mulI hx
  have hq : CP (Complex.I * x + (y - Complex.I)) :=
    cp_add hA (by simpa [sub_eq_add_neg] using cp_add hy (cp_neg cp_I))
  refine ConstructiblePt.lineLine hA hq ConstructiblePt.zero ConstructiblePt.one ?_
    ⟨x, ?_⟩ ⟨x * y, ?_⟩
  · simp [cross]
  · push_cast; ring
  · simp

lemma cp_inv {x : ℝ} (hx : CP (x : ℂ)) (h0 : x ≠ 0) : CP ((x⁻¹ : ℝ) : ℂ) := by
  have hA := cp_mulI hx
  have hq : CP (Complex.I + (1 - Complex.I * x)) :=
    cp_add cp_I (by simpa [sub_eq_add_neg] using cp_add ConstructiblePt.one (cp_neg hA))
  refine ConstructiblePt.lineLine cp_I hq ConstructiblePt.zero ConstructiblePt.one ?_
    ⟨x⁻¹, ?_⟩ ⟨x⁻¹, ?_⟩
  · simp [cross]; exact h0
  · have : (x : ℂ) ≠ 0 := by exact_mod_cast h0
    push_cast; field_simp; ring
  · simp

end geometry

/-- AA-391. The constructible real numbers form a subfield of `ℝ`. -/
@[kb "judson2026" "Theorem 21.3.1, p. 295"]
def constructibleField : Subfield ℝ where
  carrier := {x | Constructible x}
  mul_mem' := fun {a b} ha hb => cp_mul ha hb
  one_mem' := by simpa [Constructible] using ConstructiblePt.one
  add_mem' := fun {a b} ha hb => by
    have := cp_add ha hb
    simpa [Constructible] using this
  zero_mem' := by simpa [Constructible] using ConstructiblePt.zero
  neg_mem' := fun {a} ha => by
    have := cp_neg ha
    simpa [Constructible] using this
  inv_mem' := fun {a} ha => by
    by_cases h : a = 0
    · subst h; simpa [Constructible] using ConstructiblePt.zero
    · exact cp_inv ha h

lemma mem_constructibleField {x : ℝ} : x ∈ constructibleField ↔ Constructible x := Iff.rfl

/-- AA-392. The square root of a nonnegative constructible number is constructible. -/
@[kb "judson2026" "Lemma 21.3.3, p. 296"]
theorem Constructible.sqrt {x : ℝ} (hx : Constructible x) (h0 : 0 ≤ x) :
    Constructible (Real.sqrt x) := by
  have h2 : (2 : ℝ) ∈ constructibleField := by
    simp
  have hm : ((x - 1) * 2⁻¹ : ℝ) ∈ constructibleField :=
    mul_mem (sub_mem hx (one_mem _)) (inv_mem h2)
  have hm' : ConstructiblePt (((x - 1) * 2⁻¹ : ℝ) : ℂ) := hm
  apply cp_of_mulI
  refine ConstructiblePt.lineCircle ConstructiblePt.zero cp_I hm' hx
    (by intro h; have := congrArg Complex.im h; simp at this) ⟨Real.sqrt x, by ring⟩ ?_
  rw [norm_eq_iff]
  simp
  nlinarith [Real.sq_sqrt h0]

/-- A point is constructible iff both its coordinates are constructible numbers. -/
theorem constructiblePt_iff (p : ℂ) :
    ConstructiblePt p ↔ Constructible p.re ∧ Constructible p.im :=
  ⟨fun h => ⟨cp_re h, cp_im h⟩, fun h => cp_of_coords h.1 h.2⟩


section tower

open IntermediateField Module

/-- Towers of square-root extensions `ℚ = F₀ ⊂ F₁ ⊂ ⋯ ⊂ F_k` inside `ℝ`, with `F_{i+1} = F_i(√α)`,
`α ∈ F_i`. -/
inductive SqrtTower : IntermediateField ℚ ℝ → Prop
  | bot : SqrtTower ⊥
  | step {F : IntermediateField ℚ ℝ} (α : ℝ) : SqrtTower F → α ∈ F →
      SqrtTower (F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α})

lemma sqrtTower_merge {F G : IntermediateField ℚ ℝ} (hF : SqrtTower F) (hG : SqrtTower G) :
    ∃ H, SqrtTower H ∧ F ≤ H ∧ G ≤ H := by
  induction hG with
  | bot => exact ⟨F, hF, le_rfl, bot_le⟩
  | step α hG hα ih =>
    obtain ⟨H, hH, h1, h2⟩ := ih
    exact ⟨H ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}, .step α hH (h2 hα),
      h1.trans le_sup_left, sup_le_sup_right h2 _⟩

lemma sq_sqrt_mem {F : IntermediateField ℚ ℝ} {α : ℝ} (h : α ∈ F) : (Real.sqrt α) ^ 2 ∈ F := by
  by_cases h0 : 0 ≤ α
  · rw [Real.sq_sqrt h0]; exact h
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]; simp

lemma finrank_step (F : IntermediateField ℚ ℝ) [FiniteDimensional ℚ F] (s : ℝ) (hs : s ^ 2 ∈ F) :
    FiniteDimensional ℚ ↥(F ⊔ IntermediateField.adjoin ℚ {s}) ∧
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧
      finrank ℚ ↥(F ⊔ IntermediateField.adjoin ℚ {s}) = finrank ℚ F * m := by
  have hroot : Polynomial.aeval s (Polynomial.X ^ 2 - Polynomial.C (⟨s ^ 2, hs⟩ : F)) = 0 := by
    simp
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (⟨s ^ 2, hs⟩ : F)).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hint : IsIntegral F s := ⟨_, hmon, by simpa using hroot⟩
  have hdeg : (minpoly F s).natDegree ≤ 2 := by
    have := minpoly.degree_le_of_ne_zero F s hmon.ne_zero hroot
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint),
      Polynomial.degree_eq_natDegree hmon.ne_zero] at this
    simpa [Polynomial.natDegree_X_pow_sub_C] using this
  rw [← restrictScalars_adjoin_eq_sup]
  have hfin : FiniteDimensional F (adjoin F {s}) := adjoin.finiteDimensional hint
  have hpos : 0 < finrank F (adjoin F {s}) := Module.finrank_pos
  have h1 : finrank F (adjoin F {s}) = (minpoly F s).natDegree := adjoin.finrank hint
  have : IsScalarTower ℚ F (adjoin F {s}) := by
    infer_instance
  have hmul := Module.finrank_mul_finrank ℚ F (adjoin F {s})
  have hpos' : 0 < finrank ℚ F := Module.finrank_pos
  refine ⟨Module.finite_of_finrank_pos ?_, finrank F (adjoin F {s}), by omega, hmul.symm⟩
  show 0 < finrank ℚ (adjoin F {s})
  rw [← hmul]; positivity

lemma sqrtTower_finrank {F : IntermediateField ℚ ℝ} (hF : SqrtTower F) :
    FiniteDimensional ℚ F ∧ ∃ n : ℕ, finrank ℚ F = 2 ^ n := by
  induction hF with
  | bot => exact ⟨inferInstance, 0, by simp⟩
  | step α hF hα ih =>
    obtain ⟨hfin, n, hn⟩ := ih
    obtain ⟨h1, m, hm, h2⟩ := finrank_step _ (Real.sqrt α) (sq_sqrt_mem hα)
    refine ⟨h1, ?_⟩
    rcases hm with rfl | rfl
    · exact ⟨n, by rw [h2, hn]; simp⟩
    · exact ⟨n + 1, by rw [h2, hn]; ring⟩

/-- For `s^2 ∈ F`, the number `s` lies in `F(√(s^2))`. -/
lemma mem_sqrt_sq (F : IntermediateField ℚ ℝ) (s : ℝ) :
    s ∈ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt (s ^ 2)} := by
  have h : Real.sqrt (s ^ 2) ∈ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt (s ^ 2)} :=
    (le_sup_right : IntermediateField.adjoin ℚ {Real.sqrt (s ^ 2)} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  generalize hr : Real.sqrt (s ^ 2) = r at h ⊢
  rcases abs_cases s with ⟨h1, _⟩ | ⟨h1, _⟩
  · have : s = r := by rw [← hr, Real.sqrt_sq_eq_abs, h1]
    rwa [this]
  · have : s = -r := by rw [← hr, Real.sqrt_sq_eq_abs, h1]; ring
    rw [this]; exact neg_mem h

local macro "fmem" : tactic => `(tactic| repeat' first
  | assumption
  | apply add_mem
  | apply sub_mem
  | apply mul_mem
  | apply div_mem
  | apply neg_mem
  | apply inv_mem
  | apply pow_mem
  | apply one_mem
  | apply zero_mem
  | apply ofNat_mem)

/-- A real root `t` of a quadratic with coefficients in `F` lies in `F(√α)` for some `α ∈ F`. -/
lemma quad_step (F : IntermediateField ℚ ℝ) {A B C t : ℝ} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (hA0 : A ≠ 0) (h : A * t ^ 2 + B * t + C = 0) :
    ∃ α ∈ F, t ∈ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α} := by
  have hs : (2 * A * t + B) ^ 2 = B ^ 2 - 4 * A * C := by linear_combination 4 * A * h
  have hmem : B ^ 2 - 4 * A * C ∈ F := by fmem
  refine ⟨_, hmem, ?_⟩
  have hsq := mem_sqrt_sq F (2 * A * t + B)
  rw [hs] at hsq
  have hF : F ≤ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt (B ^ 2 - 4 * A * C)} := le_sup_left
  have hA' := hF hA
  have hB' := hF hB
  have : t = ((2 * A * t + B) - B) / (2 * A) := by field_simp; ring
  rw [this]
  fmem

/-- Intersecting a line `αx+βy+γ=0` with a circle `x²+y²+dx+ey+f=0` over `F` needs at most one
square root. -/
lemma lc_step (F : IntermediateField ℚ ℝ) {α β γ d e f x y : ℝ} (hα : α ∈ F) (hβ : β ∈ F)
    (hγ : γ ∈ F) (hd : d ∈ F) (he : e ∈ F) (hf : f ∈ F) (hne : α ≠ 0 ∨ β ≠ 0)
    (h1 : α * x + β * y + γ = 0) (h2 : x ^ 2 + y ^ 2 + d * x + e * y + f = 0) :
    ∃ a ∈ F, x ∈ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt a} ∧
      y ∈ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt a} := by
  by_cases hb : β = 0
  · have ha : α ≠ 0 := hne.resolve_right (not_not.2 hb)
    have hx : x = -γ / α := by
      field_simp; subst hb; linarith
    have hxF : x ∈ F := by rw [hx]; fmem
    obtain ⟨a, haF, hy⟩ := quad_step F (A := 1) (B := e) (C := x ^ 2 + d * x + f) (t := y)
      (one_mem _) he (by fmem) one_ne_zero (by linear_combination h2)
    exact ⟨a, haF, (le_sup_left : F ≤ _) hxF, hy⟩
  · have hpos : 0 < β ^ 2 := by positivity
    obtain ⟨a, haF, hx⟩ := quad_step F (A := β ^ 2 + α ^ 2) (B := 2 * α * γ + d * β ^ 2 - e * α * β)
      (C := γ ^ 2 - e * β * γ + f * β ^ 2) (t := x) (by fmem) (by fmem) (by fmem)
      (by nlinarith [sq_nonneg α])
      (by linear_combination β ^ 2 * h2 - (β * y - α * x - γ + e * β) * h1)
    refine ⟨a, haF, hx, ?_⟩
    have hF : F ≤ F ⊔ IntermediateField.adjoin ℚ {Real.sqrt a} := le_sup_left
    have hα' := hF hα
    have hβ' := hF hβ
    have hγ' := hF hγ
    have : y = -(α * x + γ) / β := by field_simp; linarith
    rw [this]
    fmem

/-- Intersecting two non-parallel lines over `F` stays in `F`. -/
lemma ll_step (F : IntermediateField ℚ ℝ) {α₁ β₁ γ₁ α₂ β₂ γ₂ x y : ℝ} (hα₁ : α₁ ∈ F)
    (hβ₁ : β₁ ∈ F) (hγ₁ : γ₁ ∈ F) (hα₂ : α₂ ∈ F) (hβ₂ : β₂ ∈ F) (hγ₂ : γ₂ ∈ F)
    (hD : α₁ * β₂ - α₂ * β₁ ≠ 0) (h1 : α₁ * x + β₁ * y + γ₁ = 0)
    (h2 : α₂ * x + β₂ * y + γ₂ = 0) : x ∈ F ∧ y ∈ F := by
  have hx : x = (β₁ * γ₂ - β₂ * γ₁) / (α₁ * β₂ - α₂ * β₁) := by
    rw [eq_div_iff hD]; linear_combination β₂ * h1 - β₁ * h2
  have hy : y = (α₂ * γ₁ - α₁ * γ₂) / (α₁ * β₂ - α₂ * β₁) := by
    rw [eq_div_iff hD]; linear_combination α₁ * h2 - α₂ * h1
  constructor
  · rw [hx]; fmem
  · rw [hy]; fmem

/-- The point `z` has both coordinates in `F`. -/
def InF (F : IntermediateField ℚ ℝ) (z : ℂ) : Prop := z.re ∈ F ∧ z.im ∈ F

lemma InF.mono {F G : IntermediateField ℚ ℝ} (h : F ≤ G) {z : ℂ} (hz : InF F z) : InF G z :=
  ⟨h hz.1, h hz.2⟩

lemma line_eq {a b p : ℂ} (h : OnLine a b p) :
    (b.im - a.im) * p.re + (-(b.re - a.re)) * p.im
      + (-(b.im - a.im) * a.re + (b.re - a.re) * a.im) = 0 := by
  obtain ⟨t, h1, h2⟩ := (onLine_iff a b p).1 h
  rw [h1, h2]; ring

lemma circ_eq {p c d : ℂ} (h : ‖p - c‖ = ‖d - c‖) :
    p.re ^ 2 + p.im ^ 2 + (-2 * c.re) * p.re + (-2 * c.im) * p.im
      + (c.re ^ 2 + c.im ^ 2 - ((d.re - c.re) ^ 2 + (d.im - c.im) ^ 2)) = 0 := by
  rw [norm_eq_iff] at h
  simp at h
  linear_combination h

/-- AA-393 (lines). The line through two distinct points with coordinates in a subfield `F ⊆ ℝ` has
an equation `αx + βy + γ = 0` with `α, β, γ ∈ F`, `(α, β) ≠ (0, 0)`. -/
@[kb "judson2026" "Lemma 21.3.5, p. 296"]
theorem line_equation_over (F : Subfield ℝ) {a b : ℂ} (hab : a ≠ b) (a1 : a.re ∈ F) (a2 : a.im ∈ F)
    (b1 : b.re ∈ F) (b2 : b.im ∈ F) :
    ∃ α ∈ F, ∃ β ∈ F, ∃ γ ∈ F, (α ≠ 0 ∨ β ≠ 0) ∧
      ∀ p : ℂ, OnLine a b p ↔ α * p.re + β * p.im + γ = 0 := by
  have hne : b.im - a.im ≠ 0 ∨ -(b.re - a.re) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hab (Complex.ext (by linarith [hcon.2]) (by linarith [hcon.1]))
  refine ⟨b.im - a.im, by fmem, -(b.re - a.re), by fmem,
    -(b.im - a.im) * a.re + (b.re - a.re) * a.im, by fmem, hne, fun p => ⟨line_eq, fun h => ?_⟩⟩
  rw [onLine_iff]
  by_cases hr : b.re - a.re = 0
  · have hi : b.im - a.im ≠ 0 := by
      intro hi; exact hab (Complex.ext (by linarith) (by linarith))
    have hp : p.re = a.re := by
      have h0 : (b.im - a.im) * (p.re - a.re) = 0 := by rw [hr] at h; linarith
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hi
      · linarith
    refine ⟨(p.im - a.im) / (b.im - a.im), ?_, ?_⟩
    · rw [hr, hp]; ring
    · field_simp; ring
  · refine ⟨(p.re - a.re) / (b.re - a.re), ?_, ?_⟩
    · field_simp; ring
    · field_simp; linear_combination -h

/-- AA-393 (circles). The circle with centre having coordinates in `F` and radius `r ∈ F` has an
equation `x² + y² + dx + ey + f = 0` with `d, e, f ∈ F`. -/
@[kb "judson2026" "Lemma 21.3.5, p. 296"]
theorem circle_equation_over (F : Subfield ℝ) {c : ℂ} {r : ℝ} (c1 : c.re ∈ F) (c2 : c.im ∈ F)
    (hr : r ∈ F) (hr0 : 0 ≤ r) :
    ∃ d ∈ F, ∃ e ∈ F, ∃ f ∈ F, ∀ p : ℂ,
      ‖p - c‖ = r ↔ p.re ^ 2 + p.im ^ 2 + d * p.re + e * p.im + f = 0 := by
  refine ⟨-2 * c.re, by fmem, -2 * c.im, by fmem, c.re ^ 2 + c.im ^ 2 - r ^ 2, by fmem,
    fun p => ?_⟩
  rw [← sq_eq_sq₀ (norm_nonneg _) hr0, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linarith

/-- AA-394 (two lines). The intersection of two lines through points with coordinates in `F` has
coordinates in `F` (that is, `F(√0)`). -/
@[kb "judson2026" "Lemma 21.3.6, p. 297"]
theorem lineLine_coords (F : IntermediateField ℚ ℝ) {a b c d p : ℂ} (ha : InF F a) (hb : InF F b)
    (hc : InF F c) (hd : InF F d) (hcr : cross (b - a) (d - c) ≠ 0) (h1 : OnLine a b p)
    (h2 : OnLine c d p) : InF F p := by
  have e1 := line_eq h1
  have e2 := line_eq h2
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨c1, c2⟩ := hc
  obtain ⟨d1, d2⟩ := hd
  refine ll_step F (α₁ := b.im - a.im) (β₁ := -(b.re - a.re))
    (γ₁ := -(b.im - a.im) * a.re + (b.re - a.re) * a.im) (α₂ := d.im - c.im)
    (β₂ := -(d.re - c.re)) (γ₂ := -(d.im - c.im) * c.re + (d.re - c.re) * c.im)
    (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) ?_ e1 e2
  intro h
  apply hcr
  simp only [cross, Complex.sub_re, Complex.sub_im]
  linarith

/-- AA-394 (line and circle). The intersection of a line through two points with coordinates in
`F` and a circle with centre and a point of it in `F` has coordinates in `F(√α)` for some
`α ∈ F`. -/
@[kb "judson2026" "Lemma 21.3.6, p. 297"]
theorem lineCircle_coords (F : IntermediateField ℚ ℝ) {a b c d p : ℂ} (ha : InF F a)
    (hb : InF F b) (hc : InF F c) (hd : InF F d) (hab : a ≠ b) (h1 : OnLine a b p)
    (h2 : ‖p - c‖ = ‖d - c‖) :
    ∃ α ∈ F, InF (F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}) p := by
  have e1 := line_eq h1
  have e2 := circ_eq h2
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  obtain ⟨c1, c2⟩ := hc
  obtain ⟨d1, d2⟩ := hd
  have hne : b.im - a.im ≠ 0 ∨ -(b.re - a.re) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hab
    exact Complex.ext (by linarith [hcon.2]) (by linarith [hcon.1])
  obtain ⟨α, hα, hx, hy⟩ := lc_step F (α := b.im - a.im) (β := -(b.re - a.re))
    (γ := -(b.im - a.im) * a.re + (b.re - a.re) * a.im) (d := -2 * c.re) (e := -2 * c.im)
    (f := c.re ^ 2 + c.im ^ 2 - ((d.re - c.re) ^ 2 + (d.im - c.im) ^ 2))
    (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) hne e1
    (by linear_combination e2)
  exact ⟨α, hα, hx, hy⟩

/-- AA-394 (two circles). The intersection of two circles with distinct centres in `F`, each
through a point with coordinates in `F`, has coordinates in `F(√α)` for some `α ∈ F`. -/
@[kb "judson2026" "Lemma 21.3.6, p. 297"]
theorem circleCircle_coords (F : IntermediateField ℚ ℝ) {c₁ d₁ c₂ d₂ p : ℂ} (hc₁ : InF F c₁)
    (hd₁ : InF F d₁) (hc₂ : InF F c₂) (hd₂ : InF F d₂) (hne : c₁ ≠ c₂)
    (h1 : ‖p - c₁‖ = ‖d₁ - c₁‖) (h2 : ‖p - c₂‖ = ‖d₂ - c₂‖) :
    ∃ α ∈ F, InF (F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}) p := by
  have e1 := circ_eq h1
  have e2 := circ_eq h2
  obtain ⟨a1, a2⟩ := hc₁
  obtain ⟨b1, b2⟩ := hd₁
  obtain ⟨c1, c2⟩ := hc₂
  obtain ⟨d1, d2⟩ := hd₂
  have hne' : 2 * (c₂.re - c₁.re) ≠ 0 ∨ 2 * (c₂.im - c₁.im) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply hne
    exact Complex.ext (by linarith [hcon.1]) (by linarith [hcon.2])
  obtain ⟨α, hα, hx, hy⟩ := lc_step F (α := 2 * (c₂.re - c₁.re)) (β := 2 * (c₂.im - c₁.im))
    (γ := (c₁.re ^ 2 + c₁.im ^ 2 - ((d₁.re - c₁.re) ^ 2 + (d₁.im - c₁.im) ^ 2)) -
      (c₂.re ^ 2 + c₂.im ^ 2 - ((d₂.re - c₂.re) ^ 2 + (d₂.im - c₂.im) ^ 2)))
    (d := -2 * c₁.re) (e := -2 * c₁.im) (x := p.re) (y := p.im)
    (f := c₁.re ^ 2 + c₁.im ^ 2 - ((d₁.re - c₁.re) ^ 2 + (d₁.im - c₁.im) ^ 2))
    (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) (by fmem) hne'
    (by linear_combination e1 - e2) (by linear_combination e1)
  exact ⟨α, hα, hx, hy⟩

lemma sqrtTower_merge4 {a b c d : ℂ} (h1 : ∃ F, SqrtTower F ∧ InF F a)
    (h2 : ∃ F, SqrtTower F ∧ InF F b) (h3 : ∃ F, SqrtTower F ∧ InF F c)
    (h4 : ∃ F, SqrtTower F ∧ InF F d) :
    ∃ H, SqrtTower H ∧ InF H a ∧ InF H b ∧ InF H c ∧ InF H d := by
  obtain ⟨F1, t1, i1⟩ := h1
  obtain ⟨F2, t2, i2⟩ := h2
  obtain ⟨F3, t3, i3⟩ := h3
  obtain ⟨F4, t4, i4⟩ := h4
  obtain ⟨G1, s1, l1, l2⟩ := sqrtTower_merge t1 t2
  obtain ⟨G2, s2, l3, l4⟩ := sqrtTower_merge s1 t3
  obtain ⟨G3, s3, l5, l6⟩ := sqrtTower_merge s2 t4
  exact ⟨G3, s3, i1.mono (l1.trans (l3.trans l5)), i2.mono (l2.trans (l3.trans l5)),
    i3.mono (l4.trans l5), i4.mono l6⟩

/-- AA-395 (one direction, geometric part). Every constructible point has both coordinates in the
top field of a tower of square-root extensions of `ℚ`. -/
theorem constructiblePt_tower {p : ℂ} (hp : ConstructiblePt p) :
    ∃ F, SqrtTower F ∧ InF F p := by
  induction hp with
  | zero => exact ⟨⊥, .bot, zero_mem _, zero_mem _⟩
  | one => exact ⟨⊥, .bot, by simp, zero_mem _⟩
  | lineLine _ _ _ _ hcr h1 h2 iha ihb ihc ihd =>
    obtain ⟨H, tH, ha, hb, hc, hd⟩ := sqrtTower_merge4 iha ihb ihc ihd
    exact ⟨H, tH, lineLine_coords H ha hb hc hd hcr h1 h2⟩
  | lineCircle _ _ _ _ hab h1 h2 iha ihb ihc ihd =>
    obtain ⟨H, tH, ha, hb, hc, hd⟩ := sqrtTower_merge4 iha ihb ihc ihd
    obtain ⟨α, hα, hp⟩ := lineCircle_coords H ha hb hc hd hab h1 h2
    exact ⟨_, .step α tH hα, hp⟩
  | circleCircle _ _ _ _ hne h1 h2 iha ihb ihc ihd =>
    obtain ⟨H, tH, ha, hb, hc, hd⟩ := sqrtTower_merge4 iha ihb ihc ihd
    obtain ⟨α, hα, hp⟩ := circleCircle_coords H ha hb hc hd hne h1 h2
    exact ⟨_, .step α tH hα, hp⟩

/-- The constructible numbers as an intermediate field of `ℝ / ℚ`. -/
noncomputable def constructibleIntermediateField : IntermediateField ℚ ℝ :=
  constructibleField.toIntermediateField (fun q => by
    have : (q : ℝ) ∈ constructibleField := SubfieldClass.ratCast_mem _ q
    simpa using this)

lemma mem_constructibleIntermediateField {x : ℝ} :
    x ∈ constructibleIntermediateField ↔ Constructible x := Iff.rfl

lemma sqrtTower_le {F : IntermediateField ℚ ℝ} (hF : SqrtTower F) :
    F ≤ constructibleIntermediateField := by
  induction hF with
  | bot =>
    intro x hx
    obtain ⟨q, rfl⟩ := (IntermediateField.mem_bot).1 hx
    exact SubfieldClass.ratCast_mem constructibleField q
  | step α hF hα ih =>
    refine sup_le ih ((IntermediateField.adjoin_simple_le_iff).2 ?_)
    have hα' : Constructible α := ih hα
    by_cases h0 : 0 ≤ α
    · exact hα'.sqrt h0
    · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]
      exact constructibleIntermediateField.zero_mem

/-- AA-395. A real number is constructible iff it lies in the top field of a tower of
square-root extensions `ℚ = F₀ ⊂ ⋯ ⊂ F_k`, `F_{i+1} = F_i(√α_i)`, `α_i ∈ F_i`. -/
@[kb "judson2026" "Theorem 21.3.7, p. 297"]
theorem constructible_iff_tower (x : ℝ) :
    Constructible x ↔ ∃ F, SqrtTower F ∧ x ∈ F := by
  constructor
  · intro h
    obtain ⟨F, hF, h1, _⟩ := constructiblePt_tower h
    exact ⟨F, hF, by simpa using h1⟩
  · rintro ⟨F, hF, hx⟩
    exact sqrtTower_le hF hx

/-- AA-395. If `x` is constructible then `[ℚ(x) : ℚ]` is a power of 2. -/
@[kb "judson2026" "Theorem 21.3.7, p. 297"]
theorem Constructible.finrank_eq_two_pow {x : ℝ} (hx : Constructible x) :
    ∃ k : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 ^ k := by
  obtain ⟨F, hF, hxF⟩ := (constructible_iff_tower x).1 hx
  obtain ⟨hfin, n, hn⟩ := sqrtTower_finrank hF
  have hle : IntermediateField.adjoin ℚ {x} ≤ F :=
    (IntermediateField.adjoin_simple_le_iff).2 hxF
  have hdvd := IntermediateField.finrank_dvd_of_le_right hle
  rw [hn] at hdvd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

/-- AA-396. Constructible numbers are algebraic over `ℚ`. -/
@[kb "judson2026" "Corollary 21.3.8, p. 298"]
theorem Constructible.isAlgebraic {x : ℝ} (hx : Constructible x) : IsAlgebraic ℚ x := by
  obtain ⟨F, hF, hxF⟩ := (constructible_iff_tower x).1 hx
  obtain ⟨hfin, _⟩ := sqrtTower_finrank hF
  have := Algebra.IsAlgebraic.of_finite ℚ F
  have h := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hxF⟩ : F)
  exact (isAlgebraic_algebraMap_iff (A := ℝ) (Subtype.val_injective) ).2 h

/-- A real number that is a root of a monic irreducible cubic over `ℚ` is not constructible. -/
lemma not_constructible_of_cubic {x : ℝ} {p : Polynomial ℚ} (hirr : Irreducible p)
    (hm : p.Monic) (hd : p.natDegree = 3) (hr : Polynomial.aeval x p = 0) :
    ¬ Constructible x := by
  intro h
  obtain ⟨k, hk⟩ := h.finrank_eq_two_pow
  have hmin : p = minpoly ℚ x := minpoly.eq_of_irreducible_of_monic hirr hr hm
  have hint : IsIntegral ℚ x := ⟨p, hm, by simpa [Polynomial.aeval_def] using hr⟩
  rw [IntermediateField.adjoin.finrank hint, ← hmin, hd] at hk
  rcases k with _ | k
  · simp at hk
  · rw [pow_succ] at hk; omega

lemma not_rat_pow_eq_two {n : ℕ} (hn : 2 ≤ n) (b : ℚ) : b ^ n ≠ 2 := by
  intro h
  have hx : ((b : ℝ)) ^ n = ((2 : ℤ) : ℝ) := by exact_mod_cast h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmult : multiplicity ((2 : ℕ) : ℤ) (2 : ℤ) % n ≠ 0 := by
    have : multiplicity ((2 : ℕ) : ℤ) (2 : ℤ) = 1 := by
      have : FiniteMultiplicity ((2 : ℕ) : ℤ) (2 : ℤ) := by
        rw [Int.finiteMultiplicity_iff]; norm_num
      simpa using multiplicity_self this
    rw [this, Nat.mod_eq_of_lt (by omega)]; norm_num
  exact (irrational_nrt_of_n_not_dvd_multiplicity n (by norm_num) 2 hx hmult) ⟨b, rfl⟩

/-- AA-397. Doubling the cube is impossible: `∛2` is not constructible. -/
@[kb "judson2026" "Unnumbered result, Section 21.3.2, p. 298"]
theorem not_constructible_cbrt_two : ¬ Constructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
  apply not_constructible_of_cubic (p := Polynomial.X ^ 3 - Polynomial.C (2 : ℚ))
  · exact irreducible_X_pow_sub_C_of_prime Nat.prime_three
      (fun b => not_rat_pow_eq_two (by norm_num) b)
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  · simp
  · simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num

/-- The cubic `y³ - 3y - 1` has no rational root (rational root test). -/
lemma no_rat_root (q : ℚ) : q ^ 3 - 3 * q - 1 ≠ 0 := by
  intro h
  have hmon : (Polynomial.X ^ 3 - Polynomial.C (3 : ℤ) * Polynomial.X - Polynomial.C (1 : ℤ)
      : Polynomial ℤ).Monic := by
    monicity!
  have hr : Polynomial.aeval q (Polynomial.X ^ 3 - Polynomial.C (3 : ℤ) * Polynomial.X
      - Polynomial.C (1 : ℤ) : Polynomial ℤ) = 0 := by
    simp only [map_sub, map_mul, map_pow, Polynomial.aeval_X, map_ofNat, map_one]
    push_cast
    linear_combination h
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmon hr
  simp only [algebraMap_int_eq, eq_intCast] at hz
  subst hz
  have h' : z ^ 3 - 3 * z - 1 = 0 := by exact_mod_cast h
  have h1 : z < 2 := by nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1), sq_nonneg z]
  have h2 : -2 < z := by nlinarith [sq_nonneg (z - 1), sq_nonneg (z + 1), sq_nonneg z]
  interval_cases z <;> omega

lemma irreducible_cubic_aux : Irreducible (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ) * Polynomial.X
    - Polynomial.C (1 : ℚ) : Polynomial ℚ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ) * Polynomial.X
        - Polynomial.C (1 : ℚ) : Polynomial ℚ).natDegree = 3 := by compute_degree!
    rw [this]; simp
  · intro x hx
    apply no_rat_root x
    simpa using hx

/-- AA-399 (algebraic part). The cubic `8x³ - 6x - 1` is irreducible over `ℚ`, by the rational
root test. -/
@[kb "judson2026" "Unnumbered result, Section 21.3.3, p. 298"]
theorem irreducible_eight_cubic :
    Irreducible (Polynomial.C (8 : ℚ) * Polynomial.X ^ 3 - Polynomial.C (6 : ℚ) * Polynomial.X
      - Polynomial.C (1 : ℚ) : Polynomial ℚ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (Polynomial.C (8 : ℚ) * Polynomial.X ^ 3 - Polynomial.C (6 : ℚ) * Polynomial.X
        - Polynomial.C (1 : ℚ) : Polynomial ℚ).natDegree = 3 := by compute_degree!
    rw [this]; simp
  · intro x hx
    apply no_rat_root (2 * x)
    simp at hx
    linear_combination 1 * hx

/-- AA-399. Trisecting a `60°` angle is impossible: `cos 20°` is not constructible. -/
@[kb "judson2026" "Unnumbered result, Section 21.3.3, p. 298"]
theorem not_constructible_cos_twenty_degrees : ¬ Constructible (Real.cos (Real.pi / 9)) := by
  intro h
  have h2 : (2 : ℝ) ∈ constructibleField := by
    simp
  have hx : Constructible (2 * Real.cos (Real.pi / 9)) := mul_mem h2 h
  refine not_constructible_of_cubic (p := Polynomial.X ^ 3 - Polynomial.C (3 : ℚ) * Polynomial.X
    - Polynomial.C (1 : ℚ)) irreducible_cubic_aux (by monicity!) (by compute_degree!) ?_ hx
  have h3 : Real.cos (3 * (Real.pi / 9)) = 1 / 2 := by
    rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring]; exact Real.cos_pi_div_three
  rw [Real.cos_three_mul] at h3
  simp
  linear_combination 2 * h3

/-- AA-399 (geometric form). The point on the unit circle at angle `20°` is not constructible,
so the `60°` angle (which is constructible) cannot be trisected. -/
@[kb "judson2026" "Unnumbered result, Section 21.3.3, p. 298"]
theorem not_constructiblePt_exp_twenty_degrees :
    ¬ ConstructiblePt (Complex.exp (((Real.pi / 9 : ℝ) : ℂ) * Complex.I)) := by
  intro h
  apply not_constructible_cos_twenty_degrees
  have := ((constructiblePt_iff _).1 h).1
  rwa [Complex.exp_ofReal_mul_I_re] at this

/-- The reduction behind AA-398: if `π` is transcendental over `ℚ`, then `√π` is not constructible.  The
transcendence of `π` is proved in `UndergradKB.AbstractAlgebra.transcendental_pi`, and the unconditional statement
is `UndergradKB.AbstractAlgebra.not_constructible_sqrt_pi` (file PiTranscendental.lean). -/
theorem not_constructible_sqrt_pi_of_transcendental (h : Transcendental ℚ Real.pi) :
    ¬ Constructible (Real.sqrt Real.pi) := by
  intro hc
  apply h
  have := hc.isAlgebraic.pow 2
  rwa [Real.sq_sqrt Real.pi_pos.le] at this

section kummer2

open Polynomial

/-- `X ^ n - 2` is irreducible over `ℚ` (Eisenstein at the prime `2`, then Gauss' lemma). -/
private lemma irreducible_X_pow_sub_two {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C (2 : ℚ) : ℚ[X]) := by
  have hmon : (X ^ n - C (2 : ℤ) : ℤ[X]).Monic := monic_X_pow_sub_C _ hn.ne'
  have hdeg : (X ^ n - C (2 : ℤ) : ℤ[X]).natDegree = n :=
    natDegree_X_pow_sub_C (2 : ℤ)
  have hP : (Ideal.span {(2 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  have heis : (X ^ n - C (2 : ℤ) : ℤ[X]).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]
      norm_num
    · intro m hm
      rw [hdeg] at hm
      simp only [coeff_sub, coeff_X_pow, coeff_C, Ideal.mem_span_singleton]
      by_cases h0 : m = 0
      · subst h0
        simp [hm.ne]
      · simp [h0, hm.ne]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp [coeff_X_pow, hn.ne]
  have hZ := heis.irreducible hP hmon.isPrimitive (by omega)
  have := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).1 hZ
  have e : (X ^ n - C (2 : ℤ) : ℤ[X]).map (algebraMap ℤ ℚ) = X ^ n - C (2 : ℚ) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    simp
  rwa [e] at this

private lemma rpow_inv_pow {n : ℕ} (hn : 0 < n) : ((2 : ℝ) ^ ((1 : ℝ) / n)) ^ n = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [one_div, inv_mul_cancel₀ this, Real.rpow_one]

private lemma aeval_rpow_two {n : ℕ} (hn : 0 < n) :
    aeval ((2 : ℝ) ^ ((1 : ℝ) / n)) (X ^ n - C (2 : ℚ) : ℚ[X]) = 0 := by
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [rpow_inv_pow hn]
  simp

/-- The real number `2 ^ (1/n)` has degree `n` over `ℚ`. -/
private lemma finrank_rpow_two {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {(2 : ℝ) ^ ((1 : ℝ) / n)}) = n := by
  have hm : (X ^ n - C (2 : ℚ) : ℚ[X]).Monic := monic_X_pow_sub_C _ hn.ne'
  have hint : IsIntegral ℚ ((2 : ℝ) ^ ((1 : ℝ) / n)) :=
    ⟨_, hm, by simpa [aeval_def] using aeval_rpow_two hn⟩
  rw [adjoin.finrank hint,
    ← minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_two hn) (aeval_rpow_two hn) hm]
  exact natDegree_X_pow_sub_C (2 : ℚ)

end kummer2

lemma constructible_rpow_two (k : ℕ) : Constructible ((2 : ℝ) ^ ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ))) := by
  induction k with
  | zero =>
    have h2 : (2 : ℝ) ∈ constructibleField := by
      simp
    have h2' : Constructible 2 := h2
    simpa using h2'
  | succ k ih =>
    have h := ih.sqrt (by positivity)
    convert h using 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp

/-- AA-396 (second half). The field of constructible numbers is not a finite extension of `ℚ`:
it contains `2 ^ (1/2^k)`, of degree `2^k`, for every `k`. -/
@[kb "judson2026" "Corollary 21.3.8, p. 298"]
theorem constructibleIntermediateField_not_finite :
    ¬ FiniteDimensional ℚ constructibleIntermediateField := by
  intro hfin
  set N := Module.finrank ℚ constructibleIntermediateField
  obtain ⟨k, hk⟩ : ∃ k, N < 2 ^ k := ⟨N, Nat.lt_two_pow_self⟩
  have hn : 0 < 2 ^ k := by positivity
  have hle : IntermediateField.adjoin ℚ {(2 : ℝ) ^ ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ))} ≤
      constructibleIntermediateField :=
    (IntermediateField.adjoin_simple_le_iff).2 (constructible_rpow_two k)
  have hdvd := IntermediateField.finrank_dvd_of_le_right hle
  rw [finrank_rpow_two hn] at hdvd
  have hpos : 0 < N := Module.finrank_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

end tower

end UndergradKB.AbstractAlgebra
