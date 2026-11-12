import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr

/-! # Rational functions and their asymptotes (Stitz-Zeager, Chapter 4)

Small bridging definitions for the book's notions of rational function, vertical, horizontal and slant asymptote
(Mathlib has the limits but not these names), the theorem distinguishing holes from vertical asymptotes
(Theorem 4.1), horizontal asymptotes (Theorem 4.2), slant asymptotes by polynomial division (Theorem 4.3), and the
variation vocabulary of Definition 4.5.

Lean's real division is total (`x / 0 = 0`); the domain of a rational function `p(x)/q(x)` is `{x | q(x) ≠ 0}`, and
the statements below only use its values there or limits that do not see the excluded points.
-/

namespace UndergradKB.Precalculus

open Filter Topology Polynomial Set

/-- Definition 4.1: `r` is a rational function if it is the ratio `p(x)/q(x)` of two polynomial functions with
`q` not the zero polynomial (the domain is where `q(x) ≠ 0`). -/
def IsRationalFunction (r : ℝ → ℝ) : Prop :=
  ∃ p q : ℝ[X], q ≠ 0 ∧ ∀ x, q.eval x ≠ 0 → r x = p.eval x / q.eval x

/-- Definition 4.1: every polynomial function is a rational function (take `q(x) = 1`); sums, products and
quotients of rational functions are rational on their common domain (here: products) (PC-072). -/
@[kb "stitzzeager2013" "Definition 4.1, p. 313"]
theorem isRationalFunction_polynomial (p : ℝ[X]) : IsRationalFunction (fun x => p.eval x) :=
  ⟨p, 1, one_ne_zero, fun x _ => by simp⟩

@[kb "stitzzeager2013" "Definition 4.1, p. 313", inherit_doc isRationalFunction_polynomial]
theorem IsRationalFunction.mul {r s : ℝ → ℝ} (hr : IsRationalFunction r) (hs : IsRationalFunction s) :
    ∃ p q : ℝ[X], q ≠ 0 ∧ ∀ x, (∃ a b : ℝ[X], a ≠ 0 ∧ b ≠ 0 ∧ q = a * b ∧
      (a.eval x ≠ 0 → b.eval x ≠ 0 → r x * s x = p.eval x / q.eval x)) := by
  obtain ⟨p₁, q₁, hq₁, h₁⟩ := hr
  obtain ⟨p₂, q₂, hq₂, h₂⟩ := hs
  refine ⟨p₁ * p₂, q₁ * q₂, mul_ne_zero hq₁ hq₂, fun x => ⟨q₁, q₂, hq₁, hq₂, rfl, fun ha hb => ?_⟩⟩
  rw [h₁ x ha, h₂ x hb, eval_mul, eval_mul, div_mul_div_comm]

/-- Definition 4.2: the line `x = c` is a vertical asymptote of the graph of `y = f(x)` if, as `x → c⁻` or as
`x → c⁺`, `f(x) → ∞` or `f(x) → -∞`. -/
def IsVerticalAsymptote (f : ℝ → ℝ) (c : ℝ) : Prop :=
  Tendsto f (𝓝[<] c) atTop ∨ Tendsto f (𝓝[<] c) atBot ∨ Tendsto f (𝓝[>] c) atTop ∨ Tendsto f (𝓝[>] c) atBot

/-- Definition 4.3: the line `y = c` is a horizontal asymptote of the graph of `y = f(x)` if `f(x) → c` as
`x → -∞` or as `x → ∞`. -/
def IsHorizontalAsymptote (f : ℝ → ℝ) (c : ℝ) : Prop :=
  Tendsto f atBot (𝓝 c) ∨ Tendsto f atTop (𝓝 c)

/-- Definition 4.4: the line `y = mx + b` with `m ≠ 0` is a slant asymptote of the graph of `y = f(x)` if, as
`x → -∞` or as `x → ∞`, `f(x) → mx + b`, which the book makes precise as `f(x) - (mx + b) → 0`. -/
def IsSlantAsymptote (f : ℝ → ℝ) (m b : ℝ) : Prop :=
  m ≠ 0 ∧ (Tendsto (fun x => f x - (m * x + b)) atBot (𝓝 0) ∨
    Tendsto (fun x => f x - (m * x + b)) atTop (𝓝 0))

/-- Definition 4.2: the line `x = 0` is a vertical asymptote of `y = 1/x` (from the right `1/x → ∞`) (PC-073). -/
@[kb "stitzzeager2013" "Definition 4.2, p. 316"]
theorem isVerticalAsymptote_inv : IsVerticalAsymptote (fun x : ℝ => 1 / x) 0 := by
  right; right; left
  simpa using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)

/-- Definition 4.3: `y = c` is a horizontal asymptote of `y = f(x)` exactly when `y = 0` is one for
`y = f(x) - c`; for example `y = 0` is a horizontal asymptote of `y = 1/x` (PC-074). -/
@[kb "stitzzeager2013" "Definition 4.3, p. 316"]
theorem isHorizontalAsymptote_iff_sub (f : ℝ → ℝ) (c : ℝ) :
    IsHorizontalAsymptote f c ↔ IsHorizontalAsymptote (fun x => f x - c) 0 := by
  unfold IsHorizontalAsymptote
  simp only [tendsto_sub_nhds_zero_iff]

@[kb "stitzzeager2013" "Definition 4.3, p. 316", inherit_doc isHorizontalAsymptote_iff_sub]
theorem isHorizontalAsymptote_inv : IsHorizontalAsymptote (fun x : ℝ => 1 / x) 0 := by
  right
  simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)

/-- Definition 4.4 (the book's remark): `y = mx + b` (`m ≠ 0`) is a slant asymptote of `y = f(x)` exactly when
`y = 0` is a horizontal asymptote of `y = f(x) - (mx + b)` (PC-077). -/
@[kb "stitzzeager2013" "Definition 4.4, p. 323"]
theorem isSlantAsymptote_iff (f : ℝ → ℝ) {m : ℝ} (hm : m ≠ 0) (b : ℝ) :
    IsSlantAsymptote f m b ↔ IsHorizontalAsymptote (fun x => f x - (m * x + b)) 0 := by
  simp [IsSlantAsymptote, IsHorizontalAsymptote, hm]

/-! ## Holes and vertical asymptotes -/

/-- A nonzero real polynomial has no zero in a punctured neighbourhood of any point. -/
theorem eventually_eval_ne_zero {g : ℝ[X]} (hg : g ≠ 0) (c : ℝ) : ∀ᶠ x in 𝓝[≠] c, g.eval x ≠ 0 := by
  have hfin : {x | g.eval x = 0}.Finite := by
    simpa [Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hg
  have hn : ({x | g.eval x = 0} \ {c})ᶜ ∈ 𝓝 c :=
    (hfin.sdiff).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with x hx hxc
  intro h0
  exact hx ⟨h0, hxc⟩

/-- Near a zero `c` of a nonzero real polynomial `q`, to the right of `c`, `q` has the sign of `q₁(c)` where
`q = (x - c)^m q₁`, `m ≥ 1`; here: `1/q(x)` tends to `+∞` or to `-∞` as `x → c⁺`, after multiplying by a
function with a nonzero limit. -/
theorem tendsto_div_of_eval_eq_zero_right {p q : ℝ[X]} (hq : q ≠ 0) {c : ℝ} (hqc : q.eval c = 0)
    (hpc : p.eval c ≠ 0) :
    Tendsto (fun x => p.eval x / q.eval x) (𝓝[>] c) atTop ∨
      Tendsto (fun x => p.eval x / q.eval x) (𝓝[>] c) atBot := by
  set m := q.rootMultiplicity c
  set q₁ := q /ₘ (X - C c) ^ m
  have hfac : (X - C c) ^ m * q₁ = q := pow_mul_divByMonic_rootMultiplicity_eq q c
  have hq₁ : q₁.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hq
  have hm : m ≠ 0 := by
    intro h0
    apply hq₁
    have : q₁ = q := by simpa [h0] using hfac
    rw [this, hqc]
  -- p/q₁ is continuous at c with a nonzero limit
  have hlim : Tendsto (fun x => p.eval x / q₁.eval x) (𝓝[>] c) (𝓝 (p.eval c / q₁.eval c)) :=
    ((p.continuous.continuousAt.div q₁.continuous.continuousAt hq₁).tendsto).mono_left
      nhdsWithin_le_nhds
  -- 1/(x - c)^m → ∞ from the right
  have hsub : Tendsto (fun x => x - c) (𝓝[>] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Ioi.mp hx)
  have hinv : Tendsto (fun x => ((x - c) ^ m)⁻¹) (𝓝[>] c) atTop := by
    have h1 : Tendsto (fun x => (x - c)⁻¹) (𝓝[>] c) atTop := tendsto_inv_nhdsGT_zero.comp hsub
    have h2 := (tendsto_pow_atTop hm).comp h1
    refine h2.congr' (Eventually.of_forall fun x => ?_)
    simp [inv_pow]
  have heq : (fun x => p.eval x / q₁.eval x * ((x - c) ^ m)⁻¹) = fun x => p.eval x / q.eval x := by
    funext x
    rw [← hfac, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    field_simp
  rcases lt_or_gt_of_ne (div_ne_zero hpc hq₁) with hneg | hpos
  · right
    rw [← heq]
    exact hlim.neg_mul_atTop hneg hinv
  · left
    rw [← heq]
    exact hlim.pos_mul_atTop hpos hinv

/-- Theorem 4.1 (location of vertical asymptotes and holes): let `r(x) = (p h)(x)/(q h)(x)` be a rational function
which simplifies to `p(x)/q(x)` (cancelling the common factor `h ≠ 0`), where `p` and `q` have no common zeros, and
let `c` be a real number not in the domain of `r`, i.e. `(q h)(c) = 0`. If `q(c) ≠ 0`, the graph has a hole at
`(c, p(c)/q(c))`: `r(x) → p(c)/q(c)` as `x → c` with `x ≠ c`. If `q(c) = 0`, the line `x = c` is a vertical
asymptote (PC-075). -/
@[kb "stitzzeager2013" "Theorem 4.1, p. 318"]
theorem hole_or_vertical_asymptote {p q h : ℝ[X]} (hq : q ≠ 0) (hh : h ≠ 0)
    (hpq : ∀ x, ¬ (p.eval x = 0 ∧ q.eval x = 0)) {c : ℝ} (hc : (q * h).eval c = 0) :
    (q.eval c ≠ 0 →
      Tendsto (fun x => (p * h).eval x / (q * h).eval x) (𝓝[≠] c) (𝓝 (p.eval c / q.eval c))) ∧
    (q.eval c = 0 → IsVerticalAsymptote (fun x => (p * h).eval x / (q * h).eval x) c) := by
  have _ := hc
  have hev : ∀ᶠ x in 𝓝[≠] c,
      (p * h).eval x / (q * h).eval x = p.eval x / q.eval x := by
    filter_upwards [eventually_eval_ne_zero hh c] with x hx
    rw [eval_mul, eval_mul, mul_div_mul_right _ _ hx]
  refine ⟨fun hqc => ?_, fun hqc => ?_⟩
  · have hcont : Tendsto (fun x => p.eval x / q.eval x) (𝓝[≠] c) (𝓝 (p.eval c / q.eval c)) :=
      ((p.continuous.continuousAt.div q.continuous.continuousAt hqc).tendsto).mono_left
        nhdsWithin_le_nhds
    exact hcont.congr' (hev.mono fun x hx => hx.symm)
  · have hpc : p.eval c ≠ 0 := fun hp => hpq c ⟨hp, hqc⟩
    have hev' : ∀ᶠ x in 𝓝[>] c, p.eval x / q.eval x = (p * h).eval x / (q * h).eval x :=
      (hev.filter_mono (nhdsWithin_mono c (fun x (hx : x ∈ Ioi c) => (ne_of_gt (mem_Ioi.mp hx) : x ≠ c)))).mono fun x hx => hx.symm
    right; right
    rcases tendsto_div_of_eval_eq_zero_right hq hqc hpc with h1 | h1
    · left; exact h1.congr' hev'
    · right; exact h1.congr' hev'

/-! ## Horizontal and slant asymptotes -/

/-- Theorem 4.2 (location of horizontal asymptotes): for `r(x) = p(x)/q(x)` with leading coefficients `a` of `p`
and `b` of `q`: if `deg p = deg q` the line `y = a/b` is a horizontal asymptote; if `deg p < deg q` the line
`y = 0` is; if `deg p > deg q` there is no horizontal asymptote (PC-076). -/
@[kb "stitzzeager2013" "Theorem 4.2, p. 320"]
theorem horizontal_asymptote_rational {p q : ℝ[X]} (hq : q ≠ 0) :
    (p.degree = q.degree →
      IsHorizontalAsymptote (fun x => p.eval x / q.eval x) (p.leadingCoeff / q.leadingCoeff)) ∧
    (p.degree < q.degree → IsHorizontalAsymptote (fun x => p.eval x / q.eval x) 0) ∧
    (q.degree < p.degree → ∀ c, ¬ IsHorizontalAsymptote (fun x => p.eval x / q.eval x) c) := by
  refine ⟨fun hd => Or.inr (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq p q hd),
    fun hd => Or.inr (Polynomial.div_tendsto_atTop_zero_of_degree_lt p q hd), fun hd c hc => ?_⟩
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hd
  rcases hc with h | h
  · exact not_tendsto_atTop_of_tendsto_nhds h.abs
      (Polynomial.abs_div_tendsto_atBot_atTop_of_degree_gt p q hd hq)
  · exact not_tendsto_atTop_of_tendsto_nhds h.abs
      (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt p q hd hq)

/-- Theorem 4.3 (determination of slant asymptotes): if `deg p = deg q + 1` and `L` is the quotient of `p` by `q`
in polynomial division, then `L(x) = mx + b` with `m ≠ 0`, and `y = L(x)` is a slant asymptote of `y = p(x)/q(x)`
at both `-∞` and `∞` (PC-078). -/
@[kb "stitzzeager2013" "Theorem 4.3, p. 324"]
theorem slant_asymptote_rational {p q : ℝ[X]} (hq : q ≠ 0) (hdeg : p.natDegree = q.natDegree + 1) :
    (p / q) = C ((p / q).coeff 1) * X + C ((p / q).coeff 0) ∧ (p / q).coeff 1 ≠ 0 ∧
      Tendsto (fun x => p.eval x / q.eval x - ((p / q).coeff 1 * x + (p / q).coeff 0)) atBot (𝓝 0) ∧
      Tendsto (fun x => p.eval x / q.eval x - ((p / q).coeff 1 * x + (p / q).coeff 0)) atTop (𝓝 0) := by
  set L := p / q
  set R := p % q
  have hdiv : q * L + R = p := EuclideanDomain.div_add_mod p q
  have hR : R.degree < q.degree := Polynomial.degree_mod_lt p hq
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hL0 : L ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_add] at hdiv
    have h1 : p.degree < q.degree := hdiv ▸ hR
    have := Polynomial.natDegree_lt_natDegree hp h1
    omega
  have hdegp : p.natDegree = (q * L).natDegree := by
    conv_lhs => rw [← hdiv]
    exact natDegree_add_eq_left_of_degree_lt
      (lt_of_lt_of_le hR (Polynomial.degree_le_mul_left q hL0))
  rw [Polynomial.natDegree_mul hq hL0] at hdegp
  have hL1 : L.natDegree = 1 := by omega
  have hlin : L = C (L.coeff 1) * X + C (L.coeff 0) := eq_X_add_C_of_natDegree_le_one hL1.le
  have hm : L.coeff 1 ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hL0
    rwa [Polynomial.leadingCoeff, hL1] at this
  have hLx : ∀ x, L.eval x = L.coeff 1 * x + L.coeff 0 := fun x => by
    conv_lhs => rw [hlin]
    simp
  have key : ∀ x, ¬ q.IsRoot x →
      p.eval x / q.eval x - (L.coeff 1 * x + L.coeff 0) = R.eval x / q.eval x := by
    intro x hx
    have hx' : q.eval x ≠ 0 := hx
    rw [← hLx]
    conv_lhs => rw [← hdiv]
    rw [eval_add, eval_mul]
    field_simp
    ring
  refine ⟨hlin, hm, ?_, ?_⟩
  · refine (Polynomial.div_tendsto_atBot_zero_of_degree_lt R q hR).congr' ?_
    filter_upwards [Polynomial.eventually_atBot_not_isRoot q hq] with x hx
    exact (key x hx).symm
  · refine (Polynomial.div_tendsto_atTop_zero_of_degree_lt R q hR).congr' ?_
    filter_upwards [Polynomial.eventually_atTop_not_isRoot q hq] with x hx
    exact (key x hx).symm

/-- Theorem 4.3 in the book's terms: with `L(x) = mx + b` the quotient of `p` by `q`, the line `y = L(x)` is a
slant asymptote of `y = p(x)/q(x)` (PC-078). -/
@[kb "stitzzeager2013" "Theorem 4.3, p. 324"]
theorem isSlantAsymptote_rational {p q : ℝ[X]} (hq : q ≠ 0) (hdeg : p.natDegree = q.natDegree + 1) :
    IsSlantAsymptote (fun x => p.eval x / q.eval x) ((p / q).coeff 1) ((p / q).coeff 0) := by
  obtain ⟨-, hm, -, h⟩ := slant_asymptote_rational hq hdeg
  exact ⟨hm, Or.inr h⟩

/-! ## Variation -/

/-- Definition 4.5: `y` varies directly with `x` if `y = kx` for a constant `k`. -/
def VariesDirectly (y x : ℝ → ℝ) : Prop := ∃ k : ℝ, ∀ t, y t = k * x t

/-- Definition 4.5: `y` varies inversely with `x` if `y = k/x` for a constant `k`. -/
def VariesInversely (y x : ℝ → ℝ) : Prop := ∃ k : ℝ, ∀ t, y t = k / x t

/-- Definition 4.5: `z` varies jointly with `x` and `y` if `z = kxy` for a constant `k`. -/
def VariesJointly (z x y : ℝ → ℝ) : Prop := ∃ k : ℝ, ∀ t, z t = k * x t * y t

/-- Definition 4.5 (constant of proportionality): if `y` varies directly with `x`, the constant is the ratio
`y/x` at any instant with `x ≠ 0`; if `y` varies inversely with `x`, it is the product `xy` at any instant with
`x ≠ 0`; if `z` varies jointly with `x` and `y`, it is `z/(xy)` whenever `xy ≠ 0` (PC-079). -/
@[kb "stitzzeager2013" "Definition 4.5, p. 362"]
theorem constant_of_proportionality {x y z : ℝ → ℝ} :
    (∀ k, (∀ t, y t = k * x t) → ∀ t, x t ≠ 0 → k = y t / x t) ∧
    (∀ k, (∀ t, y t = k / x t) → ∀ t, x t ≠ 0 → k = x t * y t) ∧
    (∀ k, (∀ t, z t = k * x t * y t) → ∀ t, x t * y t ≠ 0 → k = z t / (x t * y t)) := by
  refine ⟨fun k hk t ht => ?_, fun k hk t ht => ?_, fun k hk t ht => ?_⟩
  · rw [hk t]; field_simp
  · rw [hk t]; field_simp
  · rw [hk t, mul_assoc, mul_div_assoc, div_self ht, mul_one]

end UndergradKB.Precalculus
