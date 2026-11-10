import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import UndergradKB.Common.Attr

/-! # Affine theorems (Petrunin, chapters 14-15)

Affine maps (14A-C: parallels, midpoints, ratios, coordinate form), Menelaus' theorem (14.19), signed Ceva and
Van Aubel (14.20), and the affine forms of Desargues' (15.5) and Pappus' (15.6) theorems. The book's signed
ratio `(AX/BX)` of distinct collinear points is the real number `r` with `A -ᵥ X = r • (B -ᵥ X)`; we state the
signed theorems with such ratios as scalars. With this convention Menelaus gives the product `1` and Ceva
`-1`, as in the book. Proofs are by coordinates with respect to the triangle (or the two lines).
The projective completion is not formalized: cases with intersection points at infinity are omitted and
intersection points are hypotheses. The dual Desargues theorem (15.14) is not included. -/

namespace UndergradKB.Geometry

open AffineSubspace Affine

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Coordinates with respect to a nondegenerate triangle are unique. -/
theorem coord_eq {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) {x y x' y' : ℝ}
    (e : x • (B -ᵥ A) + y • (C -ᵥ A) = x' • (B -ᵥ A) + y' • (C -ᵥ A)) : x = x' ∧ y = y' := by
  have key : ∀ a b : ℝ, a • (B -ᵥ A) + b • (C -ᵥ A) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_contra hne
    apply h
    rw [collinear_iff_of_mem (p₀ := A) (by simp)]
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => hne ⟨ha, hb⟩
      subst ha
      have hw : C -ᵥ A = 0 := by
        simpa [hb] using hab
      have : C = A := by simpa [vsub_eq_zero_iff_eq] using hw
      subst this
      refine ⟨B -ᵥ C, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    · refine ⟨C -ᵥ A, ?_⟩
      have hu : B -ᵥ A = (-(b / a)) • (C -ᵥ A) := by
        have : a • (B -ᵥ A) = -(b • (C -ᵥ A)) := eq_neg_of_add_eq_zero_left hab
        calc B -ᵥ A = a⁻¹ • (a • (B -ᵥ A)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
          _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨-(b / a), by rw [← hu]; simp⟩
      · exact ⟨1, by simp⟩
  have := key (x - x') (y - y') (by
    rw [sub_smul, sub_smul]
    rw [sub_add_sub_comm, sub_eq_zero]; exact e)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The vector from `A` to a point `lineMap Y Z t`, in terms of the vectors from `A` to `Y` and `Z`. -/
theorem lineMap_vsub_eq (A Y Z : P) (t : ℝ) :
    AffineMap.lineMap Y Z t -ᵥ A = (1 - t) • (Y -ᵥ A) + t • (Z -ᵥ A) := by
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right Z Y A]; module

omit [Module ℝ V] in
theorem vsub_via (A X Y : P) : X -ᵥ Y = (X -ᵥ A) - (Y -ᵥ A) :=
  (vsub_sub_vsub_cancel_right X Y A).symm

/-- **Menelaus' theorem, signed version** (Petrunin, Theorem 14.19 and the remark on signed versions,
p. 119-120). Let `ABC` be a nondegenerate triangle and let a line cross the lines `BC`, `CA`, `AB` at
`A'`, `B'`, `C'`, none of them a vertex. The signed ratios `ra = (BA'/CA')`, `rb = (CB'/AB')`,
`rc = (AC'/BC')` (defined by `B -ᵥ A' = ra • (C -ᵥ A')` etc.) have product `1`. -/
@[kb "petrunin2025" "Theorem 14.19, p. 119"]
theorem menelaus_signed {A B C A' B' C' : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hcol : Collinear ℝ ({A', B', C'} : Set P))
    (hA'B : A' ≠ B) (hA'C : A' ≠ C) (hB'C : B' ≠ C) (hB'A : B' ≠ A) (hC'A : C' ≠ A) (hC'B : C' ≠ B)
    {ra rb rc : ℝ} (hra : B -ᵥ A' = ra • (C -ᵥ A')) (hrb : C -ᵥ B' = rb • (A -ᵥ B'))
    (hrc : A -ᵥ C' = rc • (B -ᵥ C')) : rc * ra * rb = 1 := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have ha0 : a ≠ 0 := by rintro rfl; simp at hA'B
  have ha1 : a ≠ 1 := by rintro rfl; simp at hA'C
  have hb0 : b ≠ 0 := by rintro rfl; simp at hB'C
  have hb1 : b ≠ 1 := by rintro rfl; simp at hB'A
  have hc0 : c ≠ 0 := by rintro rfl; simp at hC'A
  have hc1 : c ≠ 1 := by rintro rfl; simp at hC'B
  have e1 := lineMap_vsub_eq A B C a
  have e2 := lineMap_vsub_eq A C A b
  have e3 := lineMap_vsub_eq A A B c
  simp only [vsub_self, smul_zero, zero_add, add_zero] at e1 e2 e3
  have hAA : A -ᵥ A = 0 := vsub_self A
  rw [vsub_via A B, vsub_via A C, e1] at hra
  rw [vsub_via A C, vsub_via A A, e2] at hrb
  rw [vsub_via A A, vsub_via A B, e3] at hrc
  rw [hAA] at hrb hrc
  have r1 := (coord_eq h (x := a) (y := -a) (x' := -(ra * (1 - a))) (y' := ra * (1 - a))
    (by linear_combination (norm := module) hra)).1
  have r2 := (coord_eq h (x := 0) (y := b) (x' := 0) (y' := -(rb * (1 - b)))
    (by linear_combination (norm := module) hrb)).2
  have r3 := (coord_eq h (x := -c) (y := 0) (x' := rc * (1 - c)) (y' := 0)
    (by linear_combination (norm := module) hrc)).1
  -- collinearity
  rw [collinear_iff_of_mem (p₀ := AffineMap.lineMap A B c) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨s, hs⟩ := hv (AffineMap.lineMap B C a) (by simp)
  obtain ⟨t, ht⟩ := hv (AffineMap.lineMap C A b) (by simp)
  have hs' : AffineMap.lineMap B C a -ᵥ AffineMap.lineMap A B c = s • v := by
    rw [hs, vadd_vsub]
  have ht' : AffineMap.lineMap C A b -ᵥ AffineMap.lineMap A B c = t • v := by
    rw [ht, vadd_vsub]
  rw [vsub_via A, e1, e3] at hs'
  rw [vsub_via A, e2, e3] at ht'
  have hrel : t • ((1 - a - c) • (B -ᵥ A) + a • (C -ᵥ A)) =
      s • (-c • (B -ᵥ A) + (1 - b) • (C -ᵥ A)) := by
    have : t • (s • v) = s • (t • v) := smul_comm _ _ _
    rw [← hs', ← ht'] at this
    rw [show (1 - a - c) • (B -ᵥ A) + a • (C -ᵥ A) = (1 - a) • (B -ᵥ A) + a • (C -ᵥ A) - c • (B -ᵥ A) by
      module, show -c • (B -ᵥ A) + (1 - b) • (C -ᵥ A) = (1 - b) • (C -ᵥ A) - c • (B -ᵥ A) by module]
    exact this
  have hc := coord_eq h (x := t * (1 - a - c)) (y := t * a) (x' := -(s * c)) (y' := s * (1 - b))
    (by linear_combination (norm := module) hrel)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hs'
    have := coord_eq h (x := 1 - a - c) (y := a) (x' := 0) (y' := 0)
      (by linear_combination (norm := module) hs')
    exact ha0 this.2
  have hdet : (1 - a - c) * (1 - b) + a * c = 0 := by
    have : s * ((1 - a - c) * (1 - b) + a * c) = 0 := by
      linear_combination (-(1 - a - c)) * hc.2 + a * hc.1
    exact (mul_eq_zero.1 this).resolve_left hs0
  have hne : (1 - a) * (1 - c) * (1 - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.2 ha1.symm) (sub_ne_zero.2 hc1.symm))
      (sub_ne_zero.2 hb1.symm)
  apply mul_left_cancel₀ hne
  have P : (rc * (1 - c)) * (ra * (1 - a)) * (rb * (1 - b)) = (-c) * (-a) * (-b) := by
    rw [← r3, show ra * (1 - a) = -a by linarith, show rb * (1 - b) = -b by linarith]
  linear_combination P - hdet

/-- Three points are collinear if the vectors `Z - Y` and `X - Y` have proportional coordinates
(zero determinant) with respect to two vectors `a`, `b`. -/
theorem collinear_of_det {X Y Z : P} {a b : V} {s1 s2 v1 v2 : ℝ}
    (hs : Z -ᵥ Y = s1 • a + s2 • b) (hv : X -ᵥ Y = v1 • a + v2 • b)
    (hdet : s1 * v2 - s2 * v1 = 0) : Collinear ℝ ({X, Y, Z} : Set P) := by
  by_cases h0 : v1 ^ 2 + v2 ^ 2 = 0
  · have h1 : v1 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
    have h2 : v2 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2]
    rw [h1, h2] at hv
    have : X = Y := by simpa using hv
    subst this
    simp [collinear_pair]
  · set k := (s1 * v1 + s2 * v2) / (v1 ^ 2 + v2 ^ 2) with hk
    have e1 : s1 = k * v1 := by
      rw [hk]; field_simp; linear_combination v2 * hdet
    have e2 : s2 = k * v2 := by
      rw [hk]; field_simp; linear_combination (-v1) * hdet
    rw [collinear_iff_of_mem (p₀ := Y) (by simp)]
    refine ⟨X -ᵥ Y, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · refine ⟨k, ?_⟩
      rw [eq_vadd_iff_vsub_eq, hs, hv, e1, e2]; module

/-- Key computation for Desargues: if `A' = O + α (A - O)`, `B' = O + β (B - O)` and `Z` lies on `AB`
and on `A'B'`, then `(1/α - 1/β) (Z - O) = (1 - 1/β)(A - O) - (1 - 1/α)(B - O)`. -/
theorem desargues_side {O A B Z : P} (h : ¬Collinear ℝ ({O, A, B} : Set P)) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hβ1 : β ≠ 1)
    (hZ : Z ∈ line[ℝ, A, B])
    (hZ' : Z ∈ line[ℝ, AffineMap.lineMap O A α, AffineMap.lineMap O B β]) :
    α⁻¹ - β⁻¹ ≠ 0 ∧
      (α⁻¹ - β⁻¹) • (Z -ᵥ O) = (1 - β⁻¹) • (A -ᵥ O) - (1 - α⁻¹) • (B -ᵥ O) := by
  obtain ⟨u, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hZ
  obtain ⟨t, ht⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hZ'
  have e1 := lineMap_vsub_eq O A B u
  have e2 := lineMap_vsub_eq O (AffineMap.lineMap O A α) (AffineMap.lineMap O B β) t
  have e3 := lineMap_vsub_eq O O A α
  have e4 := lineMap_vsub_eq O O B β
  simp only [vsub_self, smul_zero, zero_add] at e3 e4
  rw [e3, e4, ht, e1] at e2
  have c := coord_eq h (x := 1 - u) (y := u) (x' := (1 - t) * α) (y' := t * β)
    (by rw [e2]; module)
  have E1 : 1 - u = (1 - t) * α := c.1
  have E2 : u = t * β := c.2
  have hp : α⁻¹ * α = 1 := inv_mul_cancel₀ hα
  have hq : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  refine ⟨?_, ?_⟩
  · intro h0
    have : α = β := by
      have := sub_eq_zero.1 h0
      exact inv_injective this
    subst this
    apply hβ1
    linarith
  · have h1 : (α⁻¹ - β⁻¹) * (1 - u) = 1 - β⁻¹ := by
      linear_combination α⁻¹ * E1 + (1 - t) * hp + β⁻¹ * E2 + t * hq
    have h2 : (α⁻¹ - β⁻¹) * u = α⁻¹ - 1 := by
      linear_combination -α⁻¹ * E1 - (1 - t) * hp - β⁻¹ * E2 - t * hq
    rw [e1, smul_add, smul_smul, smul_smul, h1, h2]; module

/-- In a real vector space of dimension `2`, vectors from `O` to any point are combinations of those to `A`
and `B` when `O A B` is nondegenerate. -/
theorem exists_coords (hV : Module.finrank ℝ V = 2) {O A B : P}
    (h : ¬Collinear ℝ ({O, A, B} : Set P)) (C : P) :
    ∃ m n : ℝ, C -ᵥ O = m • (A -ᵥ O) + n • (B -ᵥ O) := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  have hO : ¬Collinear ℝ ({O, A, B} : Set P) := h
  have hli : LinearIndependent ℝ ![A -ᵥ O, B -ᵥ O] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have := coord_eq (A := O) (B := A) (C := B) h (x := s) (y := t) (x' := 0) (y' := 0)
      (by simpa using hst)
    exact this
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [hV])
  have hmem : C -ᵥ O ∈ Submodule.span ℝ (Set.range ![A -ᵥ O, B -ᵥ O]) := by
    rw [htop]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at hmem
  obtain ⟨m, n, hmn⟩ := Submodule.mem_span_pair.1 hmem
  exact ⟨m, n, hmn.symm⟩

/-- **Desargues' theorem**, affine plane version (Petrunin, Theorem 15.5, p. 125). Let `V` be a real vector
space of dimension `2`; let `A'`, `B'`, `C'` lie on the lines `OA`, `OB`, `OC` (that is, the lines
`AA'`, `BB'`, `CC'` pass through `O`), all different from `O` and from `A`, `B`, `C` respectively, and let `O`
lie on no side of the triangle `ABC` (so that the sides `AB`, `BC`, `CA` are different from the lines `OA`,
`OB`, `OC`). If `X ∈ (BC) ∩ (B'C')`, `Y ∈ (CA) ∩ (C'A')`, `Z ∈ (AB) ∩ (A'B')` then `X`, `Y`, `Z`
are collinear. The case in which some pair of corresponding sides is parallel (the intersection point is
at infinity) is omitted, as is the case of parallel cevians `AA' ∥ BB' ∥ CC'`; here the intersection
points are given as hypotheses, so the statement is the book's one whenever they exist. -/
@[kb "petrunin2025" "Theorem 15.5, p. 125"]
theorem desargues (hV : Module.finrank ℝ V = 2) {O A B C A' B' C' X Y Z : P}
    (hOAB : ¬Collinear ℝ ({O, A, B} : Set P)) (hOBC : ¬Collinear ℝ ({O, B, C} : Set P))
    (hOCA : ¬Collinear ℝ ({O, C, A} : Set P))
    (hA' : A' ∈ line[ℝ, O, A]) (hB' : B' ∈ line[ℝ, O, B]) (hC' : C' ∈ line[ℝ, O, C])
    (hA'O : A' ≠ O) (hB'O : B' ≠ O) (hC'O : C' ≠ O)
    (hA'A : A' ≠ A) (hB'B : B' ≠ B) (hC'C : C' ≠ C)
    (hX : X ∈ line[ℝ, B, C]) (hX' : X ∈ line[ℝ, B', C'])
    (hY : Y ∈ line[ℝ, C, A]) (hY' : Y ∈ line[ℝ, C', A'])
    (hZ : Z ∈ line[ℝ, A, B]) (hZ' : Z ∈ line[ℝ, A', B']) :
    Collinear ℝ ({X, Y, Z} : Set P) := by
  obtain ⟨α, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨β, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨γ, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have hα : α ≠ 0 := by rintro rfl; simp at hA'O
  have hβ : β ≠ 0 := by rintro rfl; simp at hB'O
  have hγ : γ ≠ 0 := by rintro rfl; simp at hC'O
  have hα1 : α ≠ 1 := by rintro rfl; simp at hA'A
  have hβ1 : β ≠ 1 := by rintro rfl; simp at hB'B
  have hγ1 : γ ≠ 1 := by rintro rfl; simp at hC'C
  obtain ⟨hpq, sZ⟩ := desargues_side hOAB hα hβ hβ1 hZ hZ'
  obtain ⟨hqr, sX⟩ := desargues_side hOBC hβ hγ hγ1 hX hX'
  obtain ⟨hrp, sY⟩ := desargues_side hOCA hγ hα hα1 hY hY'
  obtain ⟨m, n, hc⟩ := exists_coords hV hOAB C
  rw [hc] at sX sY
  generalize α⁻¹ = p at *
  generalize β⁻¹ = q at *
  generalize γ⁻¹ = r at *
  have hrp' : r - p ≠ 0 := hrp
  have hz : Z -ᵥ O = ((1 - q) / (p - q)) • (A -ᵥ O) + (-(1 - p) / (p - q)) • (B -ᵥ O) := by
    rw [show Z -ᵥ O = (p - q)⁻¹ • ((p - q) • (Z -ᵥ O)) by rw [smul_smul, inv_mul_cancel₀ hpq, one_smul],
      sZ, div_eq_inv_mul, div_eq_inv_mul]; module
  have hx : X -ᵥ O = (-((1 - q) * m) / (q - r)) • (A -ᵥ O)
      + (((1 - r) - (1 - q) * n) / (q - r)) • (B -ᵥ O) := by
    rw [show X -ᵥ O = (q - r)⁻¹ • ((q - r) • (X -ᵥ O)) by rw [smul_smul, inv_mul_cancel₀ hqr, one_smul],
      sX, div_eq_inv_mul, div_eq_inv_mul]; module
  have hy : Y -ᵥ O = ((((1 - p) * m) - (1 - r)) / (r - p)) • (A -ᵥ O)
      + (((1 - p) * n) / (r - p)) • (B -ᵥ O) := by
    rw [show Y -ᵥ O = (r - p)⁻¹ • ((r - p) • (Y -ᵥ O)) by rw [smul_smul, inv_mul_cancel₀ hrp', one_smul],
      sY, div_eq_inv_mul, div_eq_inv_mul]; module
  refine collinear_of_det (a := A -ᵥ O) (b := B -ᵥ O)
    (s1 := (1 - q) / (p - q) - (((1 - p) * m) - (1 - r)) / (r - p))
    (s2 := (-(1 - p) / (p - q)) - ((1 - p) * n) / (r - p))
    (v1 := (-((1 - q) * m) / (q - r)) - (((1 - p) * m) - (1 - r)) / (r - p))
    (v2 := (((1 - r) - (1 - q) * n) / (q - r)) - ((1 - p) * n) / (r - p)) ?_ ?_ ?_
  · rw [vsub_via O Z Y, hz, hy]; module
  · rw [vsub_via O X Y, hx, hy]; module
  · have hqr' : q - r ≠ 0 := hqr
    field_simp
    ring

/-- If `lineMap O E u ∦ ...`: the two crossing lines of Pappus' configuration are not parallel exactly when a
determinant is nonzero (we only need one direction). -/
theorem pappus_D_ne {O E E' : P} (_h : ¬Collinear ℝ ({O, E, E'} : Set P)) {u w u' w' : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hu' : u' ≠ 0) (hw' : w' ≠ 0)
    (hnp : ¬ line[ℝ, AffineMap.lineMap O E u, AffineMap.lineMap O E' w'] ∥
      line[ℝ, AffineMap.lineMap O E' u', AffineMap.lineMap O E w]) :
    u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹ ≠ 0 := by
  intro hD
  apply hnp
  rw [AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul']
  refine ⟨Units.mk0 (-w / u) (by simp [hw, hu]), ?_⟩
  have key : w * w' = u * u' := by
    field_simp at hD; linarith
  rw [vsub_via O (AffineMap.lineMap O E' w'), vsub_via O (AffineMap.lineMap O E w),
    AffineMap.lineMap_vsub_left, AffineMap.lineMap_vsub_left, AffineMap.lineMap_vsub_left,
    AffineMap.lineMap_vsub_left]
  have k1 : -w / u * w' = -u' := by field_simp; linarith
  have k2 : -w / u * u = -w := by field_simp
  simp only [Units.smul_def, Units.val_mk0]
  rw [smul_sub, smul_smul, smul_smul, k1, k2]; module

/-- Coordinates of the crossing point in Pappus' configuration (basis `E - O`, `E' - O`). -/
theorem pappus_side {O E E' Q : P} (h : ¬Collinear ℝ ({O, E, E'} : Set P)) {u w u' w' : ℝ}
    (hu : u ≠ 0) (hw : w ≠ 0) (hu' : u' ≠ 0) (hw' : w' ≠ 0) (hD : u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹ ≠ 0)
    (hQ : Q ∈ line[ℝ, AffineMap.lineMap O E u, AffineMap.lineMap O E' w'])
    (hQ' : Q ∈ line[ℝ, AffineMap.lineMap O E' u', AffineMap.lineMap O E w]) :
    Q -ᵥ O = ((u'⁻¹ - w'⁻¹) / (u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹)) • (E -ᵥ O)
      + ((u⁻¹ - w⁻¹) / (u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹)) • (E' -ᵥ O) := by
  obtain ⟨s, hs⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hQ
  obtain ⟨t, ht⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hQ'
  have e1 := lineMap_vsub_eq O (AffineMap.lineMap O E u) (AffineMap.lineMap O E' w') s
  have e2 := lineMap_vsub_eq O (AffineMap.lineMap O E' u') (AffineMap.lineMap O E w) t
  simp only [AffineMap.lineMap_vsub_left] at e1 e2
  rw [hs] at e1
  rw [ht] at e2
  have c := coord_eq h (x := (1 - s) * u) (y := s * w') (x' := t * w) (y' := (1 - t) * u')
    (by
      have := e1.symm.trans e2
      linear_combination (norm := module) this)
  have L1 : u⁻¹ * ((1 - s) * u) + w'⁻¹ * (s * w') = 1 := by
    field_simp; ring
  have L2 : w⁻¹ * ((1 - s) * u) + u'⁻¹ * (s * w') = 1 := by
    rw [c.1, c.2]; field_simp; ring
  have hx : (1 - s) * u = (u'⁻¹ - w'⁻¹) / (u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹) := by
    rw [eq_div_iff hD]; linear_combination u'⁻¹ * L1 - w'⁻¹ * L2
  have hy : s * w' = (u⁻¹ - w⁻¹) / (u⁻¹ * u'⁻¹ - w⁻¹ * w'⁻¹) := by
    rw [eq_div_iff hD]; linear_combination u⁻¹ * L2 - w⁻¹ * L1
  rw [← hx, ← hy, e1]; module

/-- **Pappus' theorem**, affine version (Petrunin, Theorem 15.6, p. 126). Let two distinct lines meet at
`O` (given by `O E E'` nondegenerate: the lines are `OE` and `OE'`); let `A, B, C` lie on the first and `A', B', C'`
on the second, all different from `O`. Let `X` be on `(BC')` and `(B'C)`, `Y` on `(CA')` and `(C'A)`, `Z` on
`(AB')` and `(A'B)`, where each of these three pairs of lines is not parallel (so that the intersection point is
unique). Then `X`, `Y`, `Z` are collinear. The case of two parallel lines `(AB) ∥ (A'B')` (intersection
point at infinity) is omitted. -/
@[kb "petrunin2025" "Theorem 15.6, p. 126"]
theorem pappus {O E E' A B C A' B' C' X Y Z : P} (h : ¬Collinear ℝ ({O, E, E'} : Set P))
    (hA : A ∈ line[ℝ, O, E]) (hB : B ∈ line[ℝ, O, E]) (hC : C ∈ line[ℝ, O, E])
    (hA' : A' ∈ line[ℝ, O, E']) (hB' : B' ∈ line[ℝ, O, E']) (hC' : C' ∈ line[ℝ, O, E'])
    (hAO : A ≠ O) (hBO : B ≠ O) (hCO : C ≠ O) (hA'O : A' ≠ O) (hB'O : B' ≠ O) (hC'O : C' ≠ O)
    (hX : X ∈ line[ℝ, B, C']) (hX' : X ∈ line[ℝ, B', C])
    (hY : Y ∈ line[ℝ, C, A']) (hY' : Y ∈ line[ℝ, C', A])
    (hZ : Z ∈ line[ℝ, A, B']) (hZ' : Z ∈ line[ℝ, A', B])
    (hXp : ¬ line[ℝ, B, C'] ∥ line[ℝ, B', C]) (hYp : ¬ line[ℝ, C, A'] ∥ line[ℝ, C', A])
    (hZp : ¬ line[ℝ, A, B'] ∥ line[ℝ, A', B]) :
    Collinear ℝ ({X, Y, Z} : Set P) := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC
  obtain ⟨a', rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b', rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c', rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have ha : a ≠ 0 := by rintro rfl; simp at hAO
  have hb : b ≠ 0 := by rintro rfl; simp at hBO
  have hc : c ≠ 0 := by rintro rfl; simp at hCO
  have ha' : a' ≠ 0 := by rintro rfl; simp at hA'O
  have hb' : b' ≠ 0 := by rintro rfl; simp at hB'O
  have hc' : c' ≠ 0 := by rintro rfl; simp at hC'O
  have dZ := pappus_D_ne h ha hb ha' hb' hZp
  have dX := pappus_D_ne h hb hc hb' hc' hXp
  have dY := pappus_D_ne h hc ha hc' ha' hYp
  have sZ := pappus_side h ha hb ha' hb' dZ hZ hZ'
  have sX := pappus_side h hb hc hb' hc' dX hX hX'
  have sY := pappus_side h hc ha hc' ha' dY hY hY'
  generalize a⁻¹ = ia at *
  generalize b⁻¹ = ib at *
  generalize c⁻¹ = ic at *
  generalize a'⁻¹ = ia' at *
  generalize b'⁻¹ = ib' at *
  generalize c'⁻¹ = ic' at *
  refine collinear_of_det (a := E -ᵥ O) (b := E' -ᵥ O)
    (s1 := (ia' - ib') / (ia * ia' - ib * ib') - (ic' - ia') / (ic * ic' - ia * ia'))
    (s2 := (ia - ib) / (ia * ia' - ib * ib') - (ic - ia) / (ic * ic' - ia * ia'))
    (v1 := (ib' - ic') / (ib * ib' - ic * ic') - (ic' - ia') / (ic * ic' - ia * ia'))
    (v2 := (ib - ic) / (ib * ib' - ic * ic') - (ic - ia) / (ic * ic' - ia * ia')) ?_ ?_ ?_
  · rw [vsub_via O Z Y, sZ, sY]; module
  · rw [vsub_via O X Y, sX, sY]; module
  · generalize hDz : ia * ia' - ib * ib' = Dz at *
    generalize hDx : ib * ib' - ic * ic' = Dx at *
    generalize hDy : ic * ic' - ia * ia' = Dy at *
    field_simp
    rw [← hDz, ← hDx, ← hDy]
    ring

/-! ### Cevians: coordinates with respect to the triangle `A, B, C` -/

section Cevian

variable {A B C X : P}

/-- A point on the cevian `A A'` with `A' = B + a (C - B)`, in coordinates from `A`. -/
theorem cevA {a : ℝ} (hX : X ∈ line[ℝ, A, AffineMap.lineMap B C a]) :
    ∃ x y : ℝ, X -ᵥ A = x • (B -ᵥ A) + y • (C -ᵥ A) ∧ a * x = (1 - a) * y := by
  obtain ⟨k, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hX
  have e := lineMap_vsub_eq A A (AffineMap.lineMap B C a) k
  have e1 := lineMap_vsub_eq A B C a
  rw [e1] at e
  simp only [vsub_self, smul_zero, zero_add] at e
  refine ⟨k * (1 - a), k * a, ?_, by ring⟩
  rw [e]; module

/-- A point `X` with coordinates `(x, y)` from `A` lies on the cevian `B B'`, `B' = C + b (A - C)`, iff
`y = (1 - x)(1 - b)`. -/
theorem cevB (h : ¬Collinear ℝ ({A, B, C} : Set P)) {b x y : ℝ}
    (hX : X -ᵥ A = x • (B -ᵥ A) + y • (C -ᵥ A)) :
    X ∈ line[ℝ, B, AffineMap.lineMap C A b] ↔ y = (1 - x) * (1 - b) := by
  have e1 := lineMap_vsub_eq A C A b
  simp only [vsub_self, smul_zero, add_zero] at e1
  constructor
  · intro hm
    obtain ⟨l, hl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hm
    have e := lineMap_vsub_eq A B (AffineMap.lineMap C A b) l
    rw [hl, e1] at e
    have c := coord_eq h (x := x) (y := y) (x' := (1 - l) + l * 0) (y' := l * (1 - b))
      (by rw [← hX, e]; module)
    have hx : x = 1 - l := by linarith [c.1]
    rw [c.2, hx]; ring
  · intro hy
    refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨1 - x, ?_⟩
    apply vsub_left_cancel (p := A)
    rw [lineMap_vsub_eq A B (AffineMap.lineMap C A b), e1, hX, hy]
    module

/-- A point `X` with coordinates `(x, y)` from `A` lies on the cevian `C C'`, `C' = A + c (B - A)`, iff
`x = (1 - y) c`. -/
theorem cevC (h : ¬Collinear ℝ ({A, B, C} : Set P)) {c x y : ℝ}
    (hX : X -ᵥ A = x • (B -ᵥ A) + y • (C -ᵥ A)) :
    X ∈ line[ℝ, C, AffineMap.lineMap A B c] ↔ x = (1 - y) * c := by
  have e1 := lineMap_vsub_eq A A B c
  simp only [vsub_self, smul_zero, zero_add] at e1
  constructor
  · intro hm
    obtain ⟨l, hl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hm
    have e := lineMap_vsub_eq A C (AffineMap.lineMap A B c) l
    rw [hl, e1] at e
    have c' := coord_eq h (x := x) (y := y) (x' := l * c) (y' := 1 - l)
      (by rw [← hX, e]; module)
    have hy : y = 1 - l := c'.2
    rw [c'.1, hy]; ring
  · intro hy
    refine (mem_affineSpan_pair_iff_exists_lineMap_eq).2 ⟨1 - y, ?_⟩
    apply vsub_left_cancel (p := A)
    rw [lineMap_vsub_eq A C (AffineMap.lineMap A B c), e1, hX, hy]
    module

/-- Scalar ratio `B A' = ra • C A'` in coordinates. -/
theorem ratio_A (h : ¬Collinear ℝ ({A, B, C} : Set P)) {a ra : ℝ}
    (hra : B -ᵥ AffineMap.lineMap B C a = ra • (C -ᵥ AffineMap.lineMap B C a)) :
    ra * (1 - a) = -a := by
  have e1 := lineMap_vsub_eq A B C a
  rw [vsub_via A B, vsub_via A C, e1] at hra
  have := (coord_eq h (x := a) (y := -a) (x' := -(ra * (1 - a))) (y' := ra * (1 - a))
    (by linear_combination (norm := module) hra)).1
  linarith

/-- Scalar ratio `C B' = rb • A B'` in coordinates. -/
theorem ratio_B (h : ¬Collinear ℝ ({A, B, C} : Set P)) {b rb : ℝ}
    (hrb : C -ᵥ AffineMap.lineMap C A b = rb • (A -ᵥ AffineMap.lineMap C A b)) :
    rb * (1 - b) = -b := by
  have e2 := lineMap_vsub_eq A C A b
  simp only [vsub_self, smul_zero, add_zero] at e2
  rw [vsub_via A C, vsub_via A A, e2, vsub_self] at hrb
  have := (coord_eq h (x := 0) (y := b) (x' := 0) (y' := -(rb * (1 - b)))
    (by linear_combination (norm := module) hrb)).2
  linarith

/-- Scalar ratio `A C' = rc • B C'` in coordinates. -/
theorem ratio_C (h : ¬Collinear ℝ ({A, B, C} : Set P)) {c rc : ℝ}
    (hrc : A -ᵥ AffineMap.lineMap A B c = rc • (B -ᵥ AffineMap.lineMap A B c)) :
    rc * (1 - c) = -c := by
  have e3 := lineMap_vsub_eq A A B c
  simp only [vsub_self, smul_zero, zero_add] at e3
  rw [vsub_via A A, vsub_via A B, e3, vsub_self] at hrc
  have := (coord_eq h (x := -c) (y := 0) (x' := rc * (1 - c)) (y' := 0)
    (by linear_combination (norm := module) hrc)).1
  linarith

/-- Algebra shared by Ceva and Van Aubel: the three nonvanishing conditions. -/
theorem cevian_alg {a b c x y : ℝ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) (E1 : a * x = (1 - a) * y) (E2 : y = (1 - x) * (1 - b))
    (E3 : x = (1 - y) * c) :
    x + y ≠ 0 ∧ 1 - x ≠ 0 ∧ 1 - y ≠ 0 := by
  have hx1 : 1 - x ≠ 0 := by
    intro h0
    have hx : x = 1 := by linarith
    have hy : y = 0 := by rw [E2, hx]; ring
    apply ha0
    rw [hx, hy] at E1; linarith
  refine ⟨?_, hx1, ?_⟩
  · intro h0
    have hy : y = 0 := by
      have : a * (x + y) = y := by linear_combination E1
      rw [h0] at this; linarith
    have hx : x = 0 := by linarith
    apply hc0
    rw [hx, hy] at E3; linarith
  · intro h0
    have hy : y = 1 := by linarith
    have hx : x = 0 := by rw [E3, hy]; ring
    apply hb0
    rw [hx, hy] at E2; linarith

/-- **Ceva's theorem, signed version** (Petrunin, Exercise 14.20a and the remark on signed versions,
p. 120). If the cevians `AA'`, `BB'`, `CC'` of a nondegenerate triangle (with `A', B', C'` on the sides, not at
vertices) pass through a point `X`, then the signed ratios `ra = (BA'/CA')`, `rb = (CB'/AB')`,
`rc = (AC'/BC')` have product `-1`. -/
@[kb "petrunin2025" "Exercise 14.20a, p. 120"]
theorem ceva_signed (h : ¬Collinear ℝ ({A, B, C} : Set P)) {A' B' C' : P}
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hA'B : A' ≠ B) (hA'C : A' ≠ C) (hB'C : B' ≠ C) (hB'A : B' ≠ A) (hC'A : C' ≠ A) (hC'B : C' ≠ B)
    (hX1 : X ∈ line[ℝ, A, A']) (hX2 : X ∈ line[ℝ, B, B']) (hX3 : X ∈ line[ℝ, C, C'])
    {ra rb rc : ℝ} (hra : B -ᵥ A' = ra • (C -ᵥ A')) (hrb : C -ᵥ B' = rb • (A -ᵥ B'))
    (hrc : A -ᵥ C' = rc • (B -ᵥ C')) : rc * ra * rb = -1 := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have ha0 : a ≠ 0 := by rintro rfl; simp at hA'B
  have ha1 : a ≠ 1 := by rintro rfl; simp at hA'C
  have hb0 : b ≠ 0 := by rintro rfl; simp at hB'C
  have hb1 : b ≠ 1 := by rintro rfl; simp at hB'A
  have hc0 : c ≠ 0 := by rintro rfl; simp at hC'A
  have hc1 : c ≠ 1 := by rintro rfl; simp at hC'B
  have r1 := ratio_A h hra
  have r2 := ratio_B h hrb
  have r3 := ratio_C h hrc
  obtain ⟨x, y, hX, E1⟩ := cevA hX1
  have E2 := (cevB h hX).1 hX2
  have E3 := (cevC h hX).1 hX3
  obtain ⟨n1, n2, n3⟩ := cevian_alg ha0 hb0 hc0 E1 E2 E3
  have hPi : (x + y) * (1 - x) * (1 - y) ≠ 0 := mul_ne_zero (mul_ne_zero n1 n2) n3
  have key : a * b * c = (1 - a) * (1 - b) * (1 - c) := by
    apply mul_right_cancel₀ hPi
    have f1 : a * (x + y) = y := by linear_combination E1
    have f2 : (1 - a) * (x + y) = x := by linear_combination -E1
    have f3 : b * (1 - x) = 1 - x - y := by linear_combination E2
    have f4 : (1 - b) * (1 - x) = y := by linear_combination -E2
    have f5 : c * (1 - y) = x := by linear_combination -E3
    have f6 : (1 - c) * (1 - y) = 1 - x - y := by linear_combination E3
    calc a * b * c * ((x + y) * (1 - x) * (1 - y))
        = (a * (x + y)) * (b * (1 - x)) * (c * (1 - y)) := by ring
      _ = y * (1 - x - y) * x := by rw [f1, f3, f5]
      _ = ((1 - a) * (x + y)) * ((1 - b) * (1 - x)) * ((1 - c) * (1 - y)) := by rw [f2, f4, f6]; ring
      _ = _ := by ring
  have hne : (1 - a) * (1 - c) * (1 - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.2 ha1.symm) (sub_ne_zero.2 hc1.symm))
      (sub_ne_zero.2 hb1.symm)
  apply mul_left_cancel₀ hne
  have P : (rc * (1 - c)) * (ra * (1 - a)) * (rb * (1 - b)) = (-c) * (-a) * (-b) := by
    rw [r3, r1, r2]
  linear_combination P - key

/-- Scalar ratio `A B' = r • C B'` in coordinates. -/
theorem ratio_B' (h : ¬Collinear ℝ ({A, B, C} : Set P)) {b r : ℝ}
    (hr : A -ᵥ AffineMap.lineMap C A b = r • (C -ᵥ AffineMap.lineMap C A b)) :
    r * b = -(1 - b) := by
  have e2 := lineMap_vsub_eq A C A b
  simp only [vsub_self, smul_zero, add_zero] at e2
  rw [vsub_via A A, vsub_via A C, e2, vsub_self] at hr
  have := (coord_eq h (x := 0) (y := -(1 - b)) (x' := 0) (y' := r * b)
    (by linear_combination (norm := module) hr)).2
  linarith

/-- **Van Aubel's theorem**, signed version (Petrunin, Exercise 14.20b, p. 120): for concurrent cevians
`AA'`, `BB'`, `CC'` through `X` we have `(AC'/BC') + (AB'/CB') = (AX/A'X)`, where the signed ratios `r1, r2, r3`
are defined by `A -ᵥ C' = r1 • (B -ᵥ C')`, `A -ᵥ B' = r2 • (C -ᵥ B')`, `A -ᵥ X = r3 • (A' -ᵥ X)`. (This
holds without the assumption that `A'` lies between `B` and `C`.) -/
@[kb "petrunin2025" "Exercise 14.20b, p. 120"]
theorem van_aubel (h : ¬Collinear ℝ ({A, B, C} : Set P)) {A' B' C' : P}
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hA'B : A' ≠ B) (hB'C : B' ≠ C) (hC'A : C' ≠ A)
    (hX1 : X ∈ line[ℝ, A, A']) (hX2 : X ∈ line[ℝ, B, B']) (hX3 : X ∈ line[ℝ, C, C'])
    {r1 r2 r3 : ℝ} (hr1 : A -ᵥ C' = r1 • (B -ᵥ C')) (hr2 : A -ᵥ B' = r2 • (C -ᵥ B'))
    (hr3 : A -ᵥ X = r3 • (A' -ᵥ X)) : r1 + r2 = r3 := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have ha0 : a ≠ 0 := by rintro rfl; simp at hA'B
  have hb0 : b ≠ 0 := by rintro rfl; simp at hB'C
  have hc0 : c ≠ 0 := by rintro rfl; simp at hC'A
  have R1 := ratio_C h hr1
  have R2 := ratio_B' h hr2
  obtain ⟨x, y, hX, E1⟩ := cevA hX1
  have E2 := (cevB h hX).1 hX2
  have E3 := (cevC h hX).1 hX3
  obtain ⟨n1, n2, n3⟩ := cevian_alg ha0 hb0 hc0 E1 E2 E3
  have e1 := lineMap_vsub_eq A B C a
  rw [vsub_via A A, vsub_via A (AffineMap.lineMap B C a), hX, e1, vsub_self] at hr3
  have R3 := coord_eq h (x := -x) (y := -y) (x' := r3 * (1 - a - x)) (y' := r3 * (a - y))
    (by linear_combination (norm := module) hr3)
  have hs : 1 - x - y ≠ 0 := by
    have : b * (1 - x) = 1 - x - y := by linear_combination E2
    rw [← this]; exact mul_ne_zero hb0 n2
  apply mul_right_cancel₀ hs
  have f3 : b * (1 - x) = 1 - x - y := by linear_combination E2
  have f5 : c * (1 - y) = x := by linear_combination -E3
  have f6 : (1 - c) * (1 - y) = 1 - x - y := by linear_combination E3
  have f4 : (1 - b) * (1 - x) = y := by linear_combination -E2
  have s1 : r1 * (1 - x - y) = -x := by
    rw [← f6]; linear_combination (1 - y) * R1 - f5
  have s2 : r2 * (1 - x - y) = -y := by
    rw [← f3]; linear_combination (1 - x) * R2 - f4
  linear_combination s1 + s2 + R3.1 + R3.2

/-- **Ceva's theorem, converse of the signed version** (Petrunin, remark on signed versions, p. 120): if the
signed ratios have product `-1` and the cevians `AA'` and `BB'` meet at `X`, then `CC'` passes through `X`. (In
the affine plane the third cevian can also be parallel to the other two when those are parallel; this case, with
no point `X`, is omitted.) -/
@[kb "petrunin2025" "Remark on signed versions (Ceva converse), p. 120"]
theorem ceva_converse (h : ¬Collinear ℝ ({A, B, C} : Set P)) {A' B' C' : P}
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hA'B : A' ≠ B) (hA'C : A' ≠ C) (hB'C : B' ≠ C) (hB'A : B' ≠ A) (hC'A : C' ≠ A) (hC'B : C' ≠ B)
    (hX1 : X ∈ line[ℝ, A, A']) (hX2 : X ∈ line[ℝ, B, B'])
    {ra rb rc : ℝ} (hra : B -ᵥ A' = ra • (C -ᵥ A')) (hrb : C -ᵥ B' = rb • (A -ᵥ B'))
    (hrc : A -ᵥ C' = rc • (B -ᵥ C')) (hprod : rc * ra * rb = -1) : X ∈ line[ℝ, C, C'] := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have ha1 : a ≠ 1 := by rintro rfl; simp at hA'C
  have hb1 : b ≠ 1 := by rintro rfl; simp at hB'A
  have r1 := ratio_A h hra
  have r2 := ratio_B h hrb
  have r3 := ratio_C h hrc
  obtain ⟨x, y, hX, E1⟩ := cevA hX1
  have E2 := (cevB h hX).1 hX2
  have key : a * b * c = (1 - a) * (1 - b) * (1 - c) := by
    have P : (rc * (1 - c)) * (ra * (1 - a)) * (rb * (1 - b)) = (-c) * (-a) * (-b) := by
      rw [r3, r1, r2]
    linear_combination P - ((1 - a) * (1 - b) * (1 - c)) * hprod
  have xD : x * (1 - b + a * b) = (1 - a) * (1 - b) := by
    rw [E2] at E1; linear_combination E1
  have hD : 1 - b + a * b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at xD
    exact mul_ne_zero (sub_ne_zero.2 ha1.symm) (sub_ne_zero.2 hb1.symm) xD.symm
  refine (cevC h hX).2 ?_
  apply mul_right_cancel₀ hD
  rw [E2]
  linear_combination (1 - c * (1 - b)) * xD - key

/-- **Menelaus' theorem, converse of the signed version** (Petrunin, remark on signed versions, p. 120): if
`A'`, `B'`, `C'` lie on the lines `BC`, `CA`, `AB` (not at vertices) and the signed ratios have product `1`,
then `A'`, `B'`, `C'` are collinear. -/
@[kb "petrunin2025" "Remark on signed versions (Menelaus converse), p. 120"]
theorem menelaus_converse (h : ¬Collinear ℝ ({A, B, C} : Set P)) {A' B' C' : P}
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hA'C : A' ≠ C) (hB'A : B' ≠ A) (hC'B : C' ≠ B)
    {ra rb rc : ℝ} (hra : B -ᵥ A' = ra • (C -ᵥ A')) (hrb : C -ᵥ B' = rb • (A -ᵥ B'))
    (hrc : A -ᵥ C' = rc • (B -ᵥ C')) (hprod : rc * ra * rb = 1) :
    Collinear ℝ ({A', B', C'} : Set P) := by
  obtain ⟨a, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hA'
  obtain ⟨b, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hB'
  obtain ⟨c, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hC'
  have r1 := ratio_A h hra
  have r2 := ratio_B h hrb
  have r3 := ratio_C h hrc
  have e1 := lineMap_vsub_eq A B C a
  have e2 := lineMap_vsub_eq A C A b
  have e3 := lineMap_vsub_eq A A B c
  simp only [vsub_self, smul_zero, zero_add, add_zero] at e2 e3
  have key : (1 - a) * (1 - b) * (1 - c) = -(a * b * c) := by
    have P : (rc * (1 - c)) * (ra * (1 - a)) * (rb * (1 - b)) = (-c) * (-a) * (-b) := by
      rw [r3, r1, r2]
    linear_combination P - ((1 - a) * (1 - b) * (1 - c)) * hprod
  refine collinear_of_det (a := B -ᵥ A) (b := C -ᵥ A) (s1 := c) (s2 := -(1 - b))
    (v1 := 1 - a) (v2 := a - (1 - b)) ?_ ?_ ?_
  · rw [vsub_via A (AffineMap.lineMap A B c), e3, e2]; module
  · rw [vsub_via A (AffineMap.lineMap B C a), e1, e2]; module
  · linear_combination key

end Cevian

/-! ### Affine maps (Petrunin 14A-14C and the remark before 14.19) -/

section AffineMaps

variable {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]

/-- An affine map sends parallel affine subspaces to parallel affine subspaces (Petrunin, Exercise 14.1,
p. 114; this holds for every affine map, not only bijective ones). -/
@[kb "petrunin2025" "Exercise 14.1, p. 114"]
theorem parallel_map (f : P₁ →ᵃ[ℝ] P₂) {s t : AffineSubspace ℝ P₁} (h : s ∥ t) :
    s.map f ∥ t.map f := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨f.linear v, ?_⟩
  rw [AffineSubspace.map_map, AffineSubspace.map_map]
  congr 1
  ext p
  simp [AffineMap.comp_apply]

/-- Affine maps send the midpoint of a segment to the midpoint of the image segment (Petrunin,
Exercise 14.6, p. 115). -/
@[kb "petrunin2025" "Exercise 14.6, p. 115"]
theorem map_midpoint_affine (f : P₁ →ᵃ[ℝ] P₂) (a b : P₁) :
    f (midpoint ℝ a b) = midpoint ℝ (f a) (f b) :=
  f.map_midpoint a b

/-- Affine maps preserve the relation `X = O + t (P - O)` between collinear points (Petrunin,
Proposition 14.11, p. 116, for genuine affine maps). -/
@[kb "petrunin2025" "Proposition 14.11, p. 116"]
theorem map_lineMap_affine (f : P₁ →ᵃ[ℝ] P₂) (O P : P₁) (t : ℝ) :
    f (AffineMap.lineMap O P t) = AffineMap.lineMap (f O) (f P) t :=
  f.apply_lineMap O P t

/-- Affine maps preserve the (signed) simple ratio of three collinear points, `A -ᵥ X = r • (B -ᵥ X)`
(Petrunin, remark before 14.19, p. 119). -/
@[kb "petrunin2025" "Remark before Theorem 14.19, p. 119"]
theorem ratio_map (f : P₁ →ᵃ[ℝ] P₂) {A B X : P₁} {r : ℝ} (h : A -ᵥ X = r • (B -ᵥ X)) :
    f A -ᵥ f X = r • (f B -ᵥ f X) := by
  rw [← f.linear_apply_vsub, ← f.linear_apply_vsub, h, map_smul]

/-- **Coordinate form of affine equivalences of the plane** (Petrunin, Exercise 14.14, p. 117): every affine
equivalence of `ℝ²` has the form `(x, y) ↦ (a x + b y + r, c x + d y + s)` with `a d - b c ≠ 0`. -/
@[kb "petrunin2025" "Exercise 14.14, p. 117"]
theorem affineEquiv_fin_two_coord (f : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ)) :
    ∃ a b c d r s : ℝ, a * d - b * c ≠ 0 ∧
      ∀ x y : ℝ, f ![x, y] = ![a * x + b * y + r, c * x + d * y + s] := by
  set M := LinearMap.toMatrix' (f.linear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) with hM
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, f 0 0, f 0 1, ?_, ?_⟩
  · have hdet : M.det ≠ 0 := by
      have hmul : M * LinearMap.toMatrix' (f.symm.linear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = 1 := by
        rw [hM, ← LinearMap.toMatrix'_comp]
        have : (f.linear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)).comp
            (f.symm.linear : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = LinearMap.id := by
          ext v : 1
          simp
        rw [this, LinearMap.toMatrix'_id]
      intro h0
      have := congrArg Matrix.det hmul
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    rwa [Matrix.det_fin_two] at hdet
  · intro x y
    have h1 : ∀ v : Fin 2 → ℝ, f v = f.linear v + f 0 := by
      intro v
      have := f.map_vadd 0 v
      simpa using this
    rw [h1]
    funext i
    have h2 : f.linear ![x, y] = M.mulVec ![x, y] := by
      rw [hM, LinearMap.toMatrix'_mulVec]; rfl
    rw [h2]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end AffineMaps

section Unsigned

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- A point `X ≠ Q` of the line `PQ` gives a signed ratio `P -ᵥ X = r • (Q -ᵥ X)`. -/
theorem exists_ratio {X Pt Q : P} (hX : X ∈ line[ℝ, Pt, Q]) (hXQ : X ≠ Q) :
    ∃ r : ℝ, Pt -ᵥ X = r • (Q -ᵥ X) := by
  obtain ⟨t, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hX
  have ht : (1 - t) ≠ 0 := by
    intro h0
    apply hXQ
    have : t = 1 := by linarith
    simp [this]
  refine ⟨-t / (1 - t), ?_⟩
  rw [AffineMap.left_vsub_lineMap, AffineMap.right_vsub_lineMap, smul_smul,
    show -t / (1 - t) * (1 - t) = -t by field_simp, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]

/-- Distance ratio from a signed ratio. -/
theorem dist_ratio_of_ratio {A B X : P} {r : ℝ} (hBX : B ≠ X) (h : A -ᵥ X = r • (B -ᵥ X)) :
    dist A X / dist B X = |r| := by
  rw [dist_eq_norm_vsub V A X, dist_eq_norm_vsub V B X, h, norm_smul, Real.norm_eq_abs]
  have : ‖B -ᵥ X‖ ≠ 0 := by simpa [vsub_eq_zero_iff_eq] using hBX
  field_simp

/-- **Menelaus' theorem** (Petrunin, Theorem 14.19, p. 119). Let `ABC` be a nondegenerate triangle and let a
line cross the lines `BC`, `CA`, `AB` at three points `A'`, `B'`, `C'` (none a vertex). Then
`(AC'/BC') · (BA'/CA') · (CB'/AB') = 1`. -/
@[kb "petrunin2025" "Theorem 14.19, p. 119"]
theorem menelaus {A B C A' B' C' : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hcol : Collinear ℝ ({A', B', C'} : Set P))
    (hA'B : A' ≠ B) (hA'C : A' ≠ C) (hB'C : B' ≠ C) (hB'A : B' ≠ A) (hC'A : C' ≠ A) (hC'B : C' ≠ B) :
    dist A C' / dist B C' * (dist B A' / dist C A') * (dist C B' / dist A B') = 1 := by
  obtain ⟨rc, hrc⟩ := exists_ratio hC' hC'B
  obtain ⟨ra, hra⟩ := exists_ratio hA' hA'C
  obtain ⟨rb, hrb⟩ := exists_ratio hB' hB'A
  have hs := menelaus_signed h hA' hB' hC' hcol hA'B hA'C hB'C hB'A hC'A hC'B hra hrb hrc
  rw [dist_ratio_of_ratio hC'B.symm hrc, dist_ratio_of_ratio hA'C.symm hra,
    dist_ratio_of_ratio hB'A.symm hrb, ← abs_mul, ← abs_mul, hs, abs_one]

end Unsigned

end UndergradKB.Geometry
