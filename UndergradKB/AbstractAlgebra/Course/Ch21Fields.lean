import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Tower
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
import UndergradKB.AbstractAlgebra.Extensions
import UndergradKB.AbstractAlgebra.Constructible
import UndergradKB.AbstractAlgebra.PiTranscendental
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 21: fields (course layer)

Thin wrappers around Mathlib for extension fields, minimal polynomials, the tower law,
algebraic closures and splitting fields. -/

namespace UndergradKB.AbstractAlgebra.Course

open Polynomial Module

universe u

/-- AA-370. An algebraic `α` has a minimal polynomial: a monic irreducible polynomial vanishing at
`α`, dividing every polynomial vanishing at `α`, of least degree among monic ones, and unique
as a monic irreducible polynomial vanishing at `α`. -/
@[kb "judson2026" "Theorem 21.1.10, p. 287"]
theorem judson_21_1_10 {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : IsAlgebraic F α) :
    (minpoly F α).Monic ∧ Irreducible (minpoly F α) ∧ aeval α (minpoly F α) = 0 ∧
    (∀ q : F[X], aeval α q = 0 → minpoly F α ∣ q) ∧
    (∀ q : F[X], q.Monic → aeval α q = 0 → (minpoly F α).degree ≤ q.degree) ∧
    (∀ q : F[X], q.Monic → Irreducible q → aeval α q = 0 → q = minpoly F α) := by
  have h : IsIntegral F α := hα.isIntegral
  exact ⟨minpoly.monic h, minpoly.irreducible h, minpoly.aeval F α,
    fun q hq => minpoly.dvd F α hq, fun q hq hq0 => minpoly.min F α hq hq0,
    fun q hq hirr hq0 => minpoly.eq_of_irreducible_of_monic hirr hq0 hq⟩

/-- AA-371. For `α` algebraic with minimal polynomial `p`, `F(α) ≅ F[x]/⟨p⟩`. -/
@[kb "judson2026" "Proposition 21.1.12, p. 288"]
theorem judson_21_1_12 {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : IsAlgebraic F α) :
    Nonempty (AdjoinRoot (minpoly F α) ≃ₐ[F] IntermediateField.adjoin F {α}) :=
  ⟨IntermediateField.adjoinRootEquivAdjoin F hα.isIntegral⟩

/-- AA-372. If `α` has degree `n` over `F`, then `1, α, …, α^{n-1}` is a basis of `F(α)` over `F`
(so every element of `F(α)` is uniquely `b₀ + b₁ α + ⋯ + b_{n-1} α^{n-1}`) and
`[F(α) : F] = n`. -/
@[kb "judson2026" "Theorem 21.1.13, p. 288"]
theorem judson_21_1_13 {F E : Type*} [Field F] [Field E] [Algebra F E] {α : E}
    (hα : IsAlgebraic F α) :
    (∃ b : Basis (Fin (minpoly F α).natDegree) F (IntermediateField.adjoin F {α}),
      ∀ i, (b i : E) = α ^ (i : ℕ)) ∧
    finrank F (IntermediateField.adjoin F {α}) = (minpoly F α).natDegree := by
  have h := hα.isIntegral
  refine ⟨⟨(IntermediateField.adjoin.powerBasis h).basis, fun i => ?_⟩,
    IntermediateField.adjoin.finrank h⟩
  have h2 := congrFun (PowerBasis.coe_basis (IntermediateField.adjoin.powerBasis h)) i
  refine (congrArg (fun x : IntermediateField.adjoin F {α} => (x : E)) h2).trans ?_
  simp [IntermediateField.adjoin.powerBasis_gen]

/-- AA-374. Every finite extension is algebraic. -/
@[kb "judson2026" "Theorem 21.1.15, p. 289"]
theorem judson_21_1_15 {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    Algebra.IsAlgebraic F E :=
  Algebra.IsAlgebraic.of_finite F E

/-- AA-376. Tower law: for finite extensions `F ⊆ E ⊆ K`, `[K : F] = [K : E] [E : F]`. -/
@[kb "judson2026" "Theorem 21.1.17, p. 289"]
theorem judson_21_1_17 {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K]
    [Algebra F K] [IsScalarTower F E K] [FiniteDimensional F E] [FiniteDimensional E K] :
    finrank F K = finrank E K * finrank F E := by
  rw [mul_comm]
  exact (Module.finrank_mul_finrank F E K).symm

/-- AA-378. If `α` is algebraic over `F` and `β ∈ F(α)`, the degree of `β` over `F` divides the
degree of `α`. -/
@[kb "judson2026" "Corollary 21.1.19, p. 290"]
theorem judson_21_1_19 {F E : Type*} [Field F] [Field E] [Algebra F E] {α β : E}
    (hα : IsAlgebraic F α) (hβ : β ∈ IntermediateField.adjoin F {α}) :
    (minpoly F β).natDegree ∣ (minpoly F α).natDegree := by
  have hα' := hα.isIntegral
  have hβ' : IsIntegral F β := by
    have : FiniteDimensional F (IntermediateField.adjoin F {α}) :=
      IntermediateField.adjoin.finiteDimensional hα'
    exact (Algebra.IsIntegral.isIntegral (⟨β, hβ⟩ : IntermediateField.adjoin F {α})).map
      (IntermediateField.val _)
  have hle : IntermediateField.adjoin F {β} ≤ IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_le_iff]
    simpa using hβ
  have := IntermediateField.finrank_dvd_of_le_right hle
  rwa [IntermediateField.adjoin.finrank hβ', IntermediateField.adjoin.finrank hα'] at this

/-- AA-380. The elements of `E` algebraic over `F` form a subfield of `E`. -/
@[kb "judson2026" "Theorem 21.1.23, p. 291"]
theorem judson_21_1_23 {F E : Type*} [Field F] [Field E] [Algebra F E] :
    ∃ K : IntermediateField F E, ∀ x : E, x ∈ K ↔ IsAlgebraic F x :=
  ⟨algebraicClosure F E, fun _ => mem_algebraicClosure_iff⟩

/-- AA-380. The algebraic numbers form a field: there is a subfield of `ℂ` consisting exactly of
the complex numbers algebraic over `ℚ`. -/
@[kb "judson2026" "Corollary 21.1.24, p. 292"]
theorem judson_21_1_24 : ∃ K : Subfield ℂ, ∀ z : ℂ, z ∈ K ↔ IsAlgebraic ℚ z :=
  ⟨(algebraicClosure ℚ ℂ).toSubfield, fun _ => mem_algebraicClosure_iff⟩

/-- AA-382. A field is algebraically closed iff every nonconstant polynomial has a root iff
every nonconstant polynomial is a constant times a product of linear factors. -/
@[kb "judson2026" "Theorem 21.1.25, p. 292"]
theorem judson_21_1_25 {k : Type*} [Field k] :
    (IsAlgClosed k ↔ ∀ p : k[X], 0 < p.degree → ∃ x, p.IsRoot x) ∧
    (IsAlgClosed k ↔ ∀ p : k[X],
      p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod) := by
  have h1 : IsAlgClosed k ↔ ∀ p : k[X], 0 < p.degree → ∃ x, p.IsRoot x := by
    refine ⟨fun h p hp => IsAlgClosed.exists_root p hp.ne', fun h => ?_⟩
    exact IsAlgClosed.of_exists_root k fun p _ hirr => h p (degree_pos_of_irreducible hirr)
  refine ⟨h1, ⟨fun h p => ?_, fun h => ?_⟩⟩
  · exact (C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree).symm
  · rw [h1]
    intro p hp
    by_contra hne
    have h0 : p ≠ 0 := by
      rintro rfl
      simp at hp
    have hr : p.roots = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun a ha => hne ⟨a, ?_⟩
      exact (mem_roots h0).mp ha
    have := h p
    rw [hr] at this
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at this
    have hle : p.degree ≤ 0 := by
      rw [this]
      exact degree_C_le
    exact absurd hp (not_lt.mpr hle)

/-- AA-383. An algebraically closed field has no proper algebraic extension. -/
@[kb "judson2026" "Corollary 21.1.26, p. 292"]
theorem judson_21_1_26 {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed F]
    [Algebra.IsAlgebraic F E] : Function.Bijective (algebraMap F E) :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- AA-384. Every field has an algebraic closure, unique up to isomorphism. -/
@[kb "judson2026" "Theorem 21.1.27, p. 292"]
theorem judson_21_1_27 (k : Type u) [Field k] :
    (∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsAlgClosure k K) ∧
    ∀ (K L : Type _) [Field K] [Field L] [Algebra k K] [Algebra k L]
      [IsAlgClosure k K] [IsAlgClosure k L], Nonempty (K ≃ₐ[k] L) :=
  ⟨⟨AlgebraicClosure k, inferInstance, inferInstance, inferInstance⟩,
    fun K L _ _ _ _ _ _ => ⟨IsAlgClosure.equiv k K L⟩⟩

/-- AA-385. Fundamental Theorem of Algebra: `ℂ` is algebraically closed. -/
@[kb "judson2026" "Theorem 21.1.28, p. 292"]
theorem judson_21_1_28 : IsAlgClosed ℂ :=
  Complex.isAlgClosed

/-- AA-387. Every polynomial over `F` has a splitting field. -/
@[kb "judson2026" "Theorem 21.2.3, p. 293"]
theorem judson_21_2_3 {F : Type u} [Field F] (f : F[X]) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E), f.IsSplittingField F E :=
  ⟨f.SplittingField, inferInstance, inferInstance, inferInstance⟩

/-- AA-400. Triple-angle formula `cos 3θ = 4 cos³ θ - 3 cos θ`. -/
@[kb "judson2026" "Triple-angle formula, p. 298"]
theorem judson_21_3_triple_angle (θ : ℝ) :
    Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ :=
  Real.cos_three_mul θ

/-- AA-366. Kronecker: every nonconstant polynomial over `F` has a root in some extension
field `E` of `F`. -/
@[kb "judson2026" "Theorem 21.1.5, p. 285"]
theorem judson_21_1_5 {F : Type u} [Field F] (p : F[X]) (hp : 0 < p.natDegree) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (α : E), aeval α p = 0 :=
  UndergradKB.AbstractAlgebra.exists_extension_root p hp

/-- AA-369. `α` is transcendental over `F` iff `F(α)` is isomorphic over `F` to the field of
rational functions `F(x)`. -/
@[kb "judson2026" "Theorem 21.1.9, p. 287"]
theorem judson_21_1_9 {F E : Type*} [Field F] [Field E] [Algebra F E] (α : E) :
    Transcendental F α ↔ Nonempty (RatFunc F ≃ₐ[F] IntermediateField.adjoin F {α}) :=
  UndergradKB.AbstractAlgebra.transcendental_iff_nonempty_algEquiv_ratFunc α

/-- AA-377. For a chain of fields `A₀ ⊆ A₁ ⊆ ⋯ ⊆ A_n`, the degree `[A_n : A₀]` is the product of
the successive degrees `[A_{i+1} : A_i]`. -/
@[kb "judson2026" "Corollary 21.1.18, p. 290"]
theorem judson_21_1_18 {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ℕ → IntermediateField F E) (hA : Monotone A) (n : ℕ) :
    (A 0).relfinrank (A n) = ∏ i ∈ Finset.range n, (A i).relfinrank (A (i + 1)) :=
  UndergradKB.AbstractAlgebra.relfinrank_chain A hA n

/-- AA-379. For an extension `E / F` the following are equivalent: `E / F` is finite; `E` is
generated over `F` by finitely many algebraic elements; `E` is the top of a finite tower of
algebraic simple extensions. -/
@[kb "judson2026" "Theorem 21.1.22, p. 291"]
theorem judson_21_1_22 (F E : Type*) [Field F] [Field E] [Algebra F E] :
    List.TFAE
      [FiniteDimensional F E,
       ∃ s : Finset E, (∀ a ∈ s, IsAlgebraic F a) ∧ IntermediateField.adjoin F (s : Set E) = ⊤,
       ∃ (n : ℕ) (α : ℕ → E),
         (∀ i < n, IsIntegral (IntermediateField.adjoin F (α '' Set.Iio i)) (α i)) ∧
           IntermediateField.adjoin F (α '' Set.Iio n) = ⊤] :=
  UndergradKB.AbstractAlgebra.finite_tfae_tower F E

/-- AA-388. An isomorphism `σ : E ≅ F` extends to an isomorphism `E(α) ≅ F(β)` sending `α` to
`β`, when `α` is algebraic over `E` and `β` is a root of the image of its minimal polynomial. -/
@[kb "judson2026" "Lemma 21.2.4, p. 293"]
theorem judson_21_2_4 {F F' K K' : Type*} [Field F] [Field F'] [Field K] [Field K']
    [Algebra F K] [Algebra F' K'] (σ : F ≃+* F') (α : K) (β : K') (hα : IsIntegral F α)
    (hβ : aeval β ((minpoly F α).map (σ : F →+* F')) = 0) :
    ∃ τ : IntermediateField.adjoin F {α} ≃+* IntermediateField.adjoin F' {β},
      (∀ x : F, τ (algebraMap F (IntermediateField.adjoin F {α}) x) =
        algebraMap F' (IntermediateField.adjoin F' {β}) (σ x)) ∧
        τ (IntermediateField.AdjoinSimple.gen F α) = IntermediateField.AdjoinSimple.gen F' β :=
  UndergradKB.AbstractAlgebra.exists_ringEquiv_adjoin σ α β hα hβ

/-- AA-389. An isomorphism of base fields extends to an isomorphism of splitting fields. -/
@[kb "judson2026" "Theorem 21.2.6, p. 294"]
theorem judson_21_2_6 {F F' K K' : Type*} [Field F] [Field F'] [Field K] [Field K']
    [Algebra F K] [Algebra F' K'] (σ : F ≃+* F') (p : F[X])
    [p.IsSplittingField F K] [(p.map (σ : F →+* F')).IsSplittingField F' K'] :
    ∃ τ : K ≃+* K', ∀ x : F, τ (algebraMap F K x) = algebraMap F' K' (σ x) :=
  UndergradKB.AbstractAlgebra.exists_ringEquiv_of_isSplittingField σ p

/-- AA-389. Any two splitting fields of a polynomial over `F` are isomorphic over `F`. -/
@[kb "judson2026" "Corollary 21.2.8, p. 294"]
theorem judson_21_2_8 {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K]
    [Algebra F K'] (p : F[X]) [p.IsSplittingField F K] [p.IsSplittingField F K'] :
    Nonempty (K ≃ₐ[F] K') :=
  UndergradKB.AbstractAlgebra.splittingField_unique p

/-- AA-391. The constructible real numbers form a subfield of `ℝ`: they contain `0` and `1` and
are closed under sums, negatives, products and inverses. -/
@[kb "judson2026" "Theorem 21.3.1, p. 295"]
theorem judson_21_3_1 :
    (∃ K : Subfield ℝ, ∀ x : ℝ, x ∈ K ↔ UndergradKB.AbstractAlgebra.Constructible x) ∧
    UndergradKB.AbstractAlgebra.Constructible 0 ∧ UndergradKB.AbstractAlgebra.Constructible 1 ∧
    (∀ x y : ℝ, UndergradKB.AbstractAlgebra.Constructible x →
      UndergradKB.AbstractAlgebra.Constructible y →
      UndergradKB.AbstractAlgebra.Constructible (x + y) ∧
      UndergradKB.AbstractAlgebra.Constructible (-x) ∧
      UndergradKB.AbstractAlgebra.Constructible (x * y)) ∧
    (∀ x : ℝ, UndergradKB.AbstractAlgebra.Constructible x → x ≠ 0 →
      UndergradKB.AbstractAlgebra.Constructible x⁻¹) := by
  have h : ∀ x : ℝ, x ∈ UndergradKB.AbstractAlgebra.constructibleField ↔
      UndergradKB.AbstractAlgebra.Constructible x := fun _ => Iff.rfl
  refine ⟨⟨_, h⟩, (h 0).1 (zero_mem _), (h 1).1 (one_mem _), fun x y hx hy => ?_,
    fun x hx _ => (h _).1 (inv_mem ((h x).2 hx))⟩
  exact ⟨(h _).1 (add_mem ((h x).2 hx) ((h y).2 hy)), (h _).1 (neg_mem ((h x).2 hx)),
    (h _).1 (mul_mem ((h x).2 hx) ((h y).2 hy))⟩

/-- AA-392. The square root of a positive constructible number is constructible. -/
@[kb "judson2026" "Lemma 21.3.3, p. 296"]
theorem judson_21_3_3 {x : ℝ} (hx : UndergradKB.AbstractAlgebra.Constructible x) (h0 : 0 < x) :
    UndergradKB.AbstractAlgebra.Constructible (Real.sqrt x) :=
  UndergradKB.AbstractAlgebra.Constructible.sqrt hx h0.le

/-- AA-393. Over a subfield `F ⊆ ℝ`, the line through two distinct points with coordinates in `F`
has an equation `a x + b y + c = 0` with `a, b, c ∈ F` (not both `a, b` zero), and a circle with
center and radius in `F` has an equation `x² + y² + d x + e y + f = 0` with `d, e, f ∈ F`. -/
@[kb "judson2026" "Lemma 21.3.5, p. 296"]
theorem judson_21_3_5 (F : Subfield ℝ) :
    (∀ {a b : ℂ}, a ≠ b → a.re ∈ F → a.im ∈ F → b.re ∈ F → b.im ∈ F →
      ∃ α ∈ F, ∃ β ∈ F, ∃ γ ∈ F, (α ≠ 0 ∨ β ≠ 0) ∧
        ∀ p : ℂ, UndergradKB.AbstractAlgebra.OnLine a b p ↔ α * p.re + β * p.im + γ = 0) ∧
    (∀ {c : ℂ} {r : ℝ}, c.re ∈ F → c.im ∈ F → r ∈ F → 0 ≤ r →
      ∃ d ∈ F, ∃ e ∈ F, ∃ f ∈ F, ∀ p : ℂ,
        ‖p - c‖ = r ↔ p.re ^ 2 + p.im ^ 2 + d * p.re + e * p.im + f = 0) :=
  ⟨fun hab a1 a2 b1 b2 =>
      UndergradKB.AbstractAlgebra.line_equation_over F hab a1 a2 b1 b2,
    fun c1 c2 hr hr0 => UndergradKB.AbstractAlgebra.circle_equation_over F c1 c2 hr hr0⟩

/-- AA-394. For a field `F` of constructible numbers (`ℚ ⊆ F ⊆ ℝ`), a point common to two
non-parallel lines through `F`-points has coordinates in `F`, and a point common to a line and
a circle, or to two circles, defined over `F` has coordinates in `F(√α)` for some `α ∈ F`. -/
@[kb "judson2026" "Lemma 21.3.6, p. 297"]
theorem judson_21_3_6 (F : IntermediateField ℚ ℝ) :
    (∀ {a b c d p : ℂ}, UndergradKB.AbstractAlgebra.InF F a → UndergradKB.AbstractAlgebra.InF F b →
      UndergradKB.AbstractAlgebra.InF F c → UndergradKB.AbstractAlgebra.InF F d →
      UndergradKB.AbstractAlgebra.cross (b - a) (d - c) ≠ 0 →
      UndergradKB.AbstractAlgebra.OnLine a b p → UndergradKB.AbstractAlgebra.OnLine c d p →
      UndergradKB.AbstractAlgebra.InF F p) ∧
    (∀ {a b c d p : ℂ}, UndergradKB.AbstractAlgebra.InF F a → UndergradKB.AbstractAlgebra.InF F b →
      UndergradKB.AbstractAlgebra.InF F c → UndergradKB.AbstractAlgebra.InF F d → a ≠ b →
      UndergradKB.AbstractAlgebra.OnLine a b p → ‖p - c‖ = ‖d - c‖ →
      ∃ α ∈ F, UndergradKB.AbstractAlgebra.InF
        (F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}) p) ∧
    (∀ {c₁ d₁ c₂ d₂ p : ℂ}, UndergradKB.AbstractAlgebra.InF F c₁ →
      UndergradKB.AbstractAlgebra.InF F d₁ → UndergradKB.AbstractAlgebra.InF F c₂ →
      UndergradKB.AbstractAlgebra.InF F d₂ → c₁ ≠ c₂ → ‖p - c₁‖ = ‖d₁ - c₁‖ →
      ‖p - c₂‖ = ‖d₂ - c₂‖ →
      ∃ α ∈ F, UndergradKB.AbstractAlgebra.InF
        (F ⊔ IntermediateField.adjoin ℚ {Real.sqrt α}) p) :=
  ⟨fun ha hb hc hd hcr h1 h2 =>
      UndergradKB.AbstractAlgebra.lineLine_coords F ha hb hc hd hcr h1 h2,
    fun ha hb hc hd hab h1 h2 =>
      UndergradKB.AbstractAlgebra.lineCircle_coords F ha hb hc hd hab h1 h2,
    fun hc₁ hd₁ hc₂ hd₂ hne h1 h2 =>
      UndergradKB.AbstractAlgebra.circleCircle_coords F hc₁ hd₁ hc₂ hd₂ hne h1 h2⟩

/-- AA-395. A real `x` is constructible iff it lies in the top field of a tower of
square-root extensions `ℚ = F₀ ⊂ ⋯ ⊂ F_k`; then `[ℚ(x) : ℚ]` is a power of 2. -/
@[kb "judson2026" "Theorem 21.3.7, p. 297"]
theorem judson_21_3_7 (x : ℝ) :
    (UndergradKB.AbstractAlgebra.Constructible x ↔
      ∃ F, UndergradKB.AbstractAlgebra.SqrtTower F ∧ x ∈ F) ∧
    (UndergradKB.AbstractAlgebra.Constructible x →
      ∃ k : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 ^ k) :=
  ⟨UndergradKB.AbstractAlgebra.constructible_iff_tower x,
    fun hx => UndergradKB.AbstractAlgebra.Constructible.finrank_eq_two_pow hx⟩

/-- AA-396. The field of constructible numbers is an algebraic extension of `ℚ`, but not a
finite one. -/
@[kb "judson2026" "Corollary 21.3.8, p. 298"]
theorem judson_21_3_8 :
    (∀ x : ℝ, UndergradKB.AbstractAlgebra.Constructible x → IsAlgebraic ℚ x) ∧
    ¬ FiniteDimensional ℚ UndergradKB.AbstractAlgebra.constructibleIntermediateField :=
  ⟨fun _ hx => UndergradKB.AbstractAlgebra.Constructible.isAlgebraic hx,
    UndergradKB.AbstractAlgebra.constructibleIntermediateField_not_finite⟩

/-- AA-397. Doubling the cube is impossible: `∛2` is not a constructible number. -/
@[kb "judson2026" "Doubling the cube, p. 298"]
theorem judson_21_3_doubling_cube :
    ¬ UndergradKB.AbstractAlgebra.Constructible ((2 : ℝ) ^ ((1 : ℝ) / 3)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cbrt_two

/-- AA-399. Trisecting a `60°` angle is impossible: `cos 20°` is not a constructible number. -/
@[kb "judson2026" "Trisecting an angle, p. 298"]
theorem judson_21_3_trisect_angle :
    ¬ UndergradKB.AbstractAlgebra.Constructible (Real.cos (Real.pi / 9)) :=
  UndergradKB.AbstractAlgebra.not_constructible_cos_twenty_degrees

/-- AA-398. Squaring the circle is impossible: `√π` is not a constructible number, because `π` is
transcendental over `ℚ` (Lindemann). -/
@[kb "judson2026" "Squaring the circle, p. 298"]
theorem judson_21_3_squaring_circle :
    Transcendental ℚ Real.pi ∧ ¬ UndergradKB.AbstractAlgebra.Constructible (Real.sqrt Real.pi) :=
  ⟨UndergradKB.AbstractAlgebra.transcendental_pi, UndergradKB.AbstractAlgebra.not_constructible_sqrt_pi⟩

end UndergradKB.AbstractAlgebra.Course
