import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar

/-!
# The ring of sequences `S(K)` (Petkovsek–Wilf–Zeilberger, "A = B", Section 8.2)

`S(K)` is the ring of sequences over `K` modulo the ideal of eventually zero sequences.  Mathlib's
`Filter.Germ` at `atTop` (equivalently at `cofinite`) on `ℕ` is exactly this ring.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

/-- CO-480. The ring `S(K)` of sequences over `K` with equality "almost everywhere", i.e. the
quotient of `ℕ → K` by the ideal of eventually zero sequences: the germs of sequences at
`atTop`. -/
@[kb "petkovsekwilfzeilberger1996" "text (definition of S(K)), p. 156"]
abbrev SeqRing (K : Type*) [Field K] := (atTop : Filter ℕ).Germ K

namespace SeqRing

variable {K : Type*} [Field K]

/-- A sequence represents the zero element of `S(K)` iff it is eventually zero. -/
theorem coe_eq_zero_iff {f : ℕ → K} : (f : SeqRing K) = 0 ↔ ∀ᶠ n : ℕ in atTop, f n = 0 :=
  Germ.coe_eq

/-- Two sequences are equal in `S(K)` iff they agree almost everywhere. -/
theorem coe_eq_coe_iff {f g : ℕ → K} : (f : SeqRing K) = g ↔ ∀ᶠ n : ℕ in atTop, f n = g n :=
  Germ.coe_eq

/-- Every element of `S(K)` is represented by a sequence. -/
theorem exists_coe (a : SeqRing K) : ∃ f : ℕ → K, (f : SeqRing K) = a :=
  Germ.inductionOn a fun f => ⟨f, rfl⟩

/-! ### The shift automorphism -/

/-- The shift `N` on `ℕ → K`, descended to `S(K)`: `(N a)(n) = a(n+1)`. -/
def shiftHom : SeqRing K →+* SeqRing K where
  toFun a := a.compTendsto (· + 1) (tendsto_add_atTop_nat 1)
  map_one' := Germ.const_compTendsto (1 : K) _
  map_zero' := Germ.const_compTendsto (0 : K) _
  map_mul' a b := by
    induction a using Germ.inductionOn with | _ f => ?_
    induction b using Germ.inductionOn with | _ g => ?_
    rw [← Germ.coe_mul]
    simp only [Germ.coe_compTendsto, ← Germ.coe_mul]
    rfl
  map_add' a b := by
    induction a using Germ.inductionOn with | _ f => ?_
    induction b using Germ.inductionOn with | _ g => ?_
    rw [← Germ.coe_add]
    simp only [Germ.coe_compTendsto, ← Germ.coe_add]
    rfl

theorem shiftHom_coe (f : ℕ → K) : shiftHom (f : SeqRing K) = ((fun n => f (n + 1) : ℕ → K) :
    SeqRing K) :=
  Germ.coe_compTendsto f (tendsto_add_atTop_nat 1)

/-- CO-480. The shift `N` of `S(K)` is a ring automorphism (`(N a)(n) = a(n+1)`; its inverse is
`a ↦ (n ↦ a(n-1))`). -/
@[kb "petkovsekwilfzeilberger1996" "text (definition of S(K)), p. 156"]
def shift : SeqRing K ≃+* SeqRing K :=
  { shiftHom with
    invFun := fun a => a.compTendsto (· - 1) (tendsto_sub_atTop_nat 1)
    left_inv := fun a => by
      induction a using Germ.inductionOn with | _ f => ?_
      change (shiftHom (f : SeqRing K)).compTendsto (· - 1) (tendsto_sub_atTop_nat 1) = f
      rw [shiftHom_coe, Germ.coe_compTendsto]
      exact Germ.coe_eq.2 ((eventually_ge_atTop 1).mono fun n hn => by
        simp [Nat.sub_add_cancel hn])
    right_inv := fun a => by
      induction a using Germ.inductionOn with | _ f => ?_
      change shiftHom ((f : SeqRing K).compTendsto (· - 1) (tendsto_sub_atTop_nat 1)) = f
      rw [Germ.coe_compTendsto, shiftHom_coe]
      exact Germ.coe_eq.2 ((eventually_ge_atTop 1).mono fun n hn => by
        simp) }

theorem shift_coe (f : ℕ → K) :
    shift (f : SeqRing K) = ((fun n => f (n + 1) : ℕ → K) : SeqRing K) := shiftHom_coe f

/-! ### Units and zero divisors (CO-481) -/

/-- CO-481. A sequence is a unit of `S(K)` iff it is eventually nonzero. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 156"]
theorem isUnit_coe_iff {f : ℕ → K} : IsUnit (f : SeqRing K) ↔ ∀ᶠ n : ℕ in atTop, f n ≠ 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    obtain ⟨g, rfl⟩ := exists_coe b
    have : ((f * g : ℕ → K) : SeqRing K) = ((1 : ℕ → K) : SeqRing K) := hb
    filter_upwards [coe_eq_coe_iff.1 this] with n hn h0
    simp [h0] at hn
  · intro h
    refine isUnit_iff_exists_inv.2 ⟨((fun n => (f n)⁻¹ : ℕ → K) : SeqRing K), ?_⟩
    show ((f * fun n => (f n)⁻¹ : ℕ → K) : SeqRing K) = ((1 : ℕ → K) : SeqRing K)
    exact coe_eq_coe_iff.2 (h.mono fun n hn => by simp [hn])

/-- CO-481. A nonzero non-unit of `S(K)` is a sequence with infinitely many zero terms and
infinitely many nonzero terms; conversely such a sequence is a nonzero non-unit. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 156"]
theorem nonzero_not_isUnit_iff {f : ℕ → K} :
    ((f : SeqRing K) ≠ 0 ∧ ¬ IsUnit (f : SeqRing K)) ↔
      (∃ᶠ n : ℕ in atTop, f n = 0) ∧ ∃ᶠ n : ℕ in atTop, f n ≠ 0 := by
  rw [Ne, coe_eq_zero_iff, isUnit_coe_iff, Filter.not_eventually, Filter.not_eventually]
  simp only [not_not]
  exact and_comm

/-- CO-481. For a nonzero element `f` of `S(K)`: `f` is a non-unit iff it is a zero divisor
(so every nonzero element is a unit or a zero divisor, not both; `b ≠ 0, a b = 0`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 156"]
theorem isZeroDivisor_iff_not_isUnit {a : SeqRing K} (ha : a ≠ 0) :
    (∃ b : SeqRing K, b ≠ 0 ∧ a * b = 0) ↔ ¬ IsUnit a := by
  classical
  obtain ⟨f, rfl⟩ := exists_coe a
  constructor
  · rintro ⟨b, hb, hab⟩ hu
    exact hb ((hu.mul_right_eq_zero).1 hab)
  · intro hu
    have h := nonzero_not_isUnit_iff.1 ⟨ha, hu⟩
    refine ⟨((fun n => if f n = 0 then 1 else 0 : ℕ → K) : SeqRing K), ?_, ?_⟩
    · rw [Ne, coe_eq_zero_iff, Filter.not_eventually]
      refine h.1.mono fun n hn => ?_
      simp [hn]
    · show ((f * fun n => if f n = 0 then 1 else 0 : ℕ → K) : SeqRing K) = ((0 : ℕ → K) :
        SeqRing K)
      refine coe_eq_coe_iff.2 (Eventually.of_forall fun n => ?_)
      by_cases hn : f n = 0 <;> simp [hn]

/-! ### Polynomial, rational and hypergeometric sequences (CO-483) -/

/-- CO-483. A sequence is polynomial if it equals `p(n)` almost everywhere, `p ∈ K[x]`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
def IsPolynomialSeq (a : ℕ → K) : Prop := ∃ p : K[X], ∀ᶠ n : ℕ in atTop, a n = p.eval (n : K)

/-- CO-483. A sequence is rational if it equals `p(n)/q(n)` almost everywhere, for polynomials
`p` and a nonzero polynomial `q` (a rational function `p/q ∈ K(x)`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
def IsRationalSeq (a : ℕ → K) : Prop :=
  ∃ p q : K[X], q ≠ 0 ∧ ∀ᶠ n : ℕ in atTop, a n = p.eval (n : K) / q.eval (n : K)

/-- CO-483. Every polynomial sequence is rational. -/
@[kb "petkovsekwilfzeilberger1996" "text after Definition 8.2.1, p. 158"]
theorem IsPolynomialSeq.isRationalSeq {a : ℕ → K} (h : IsPolynomialSeq a) : IsRationalSeq a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, 1, one_ne_zero, hp.mono fun n hn => by simp [hn]⟩

variable [CharZero K]

/-- CO-483. Every nonzero rational sequence is a unit of `S(K)`. -/
@[kb "petkovsekwilfzeilberger1996" "text after Definition 8.2.1, p. 158"]
theorem IsRationalSeq.isUnit {a : ℕ → K} (h : IsRationalSeq a) (h0 : (a : SeqRing K) ≠ 0) :
    IsUnit (a : SeqRing K) := by
  obtain ⟨p, q, hq, hp⟩ := h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply h0
    exact coe_eq_zero_iff.2 (hp.mono fun n hn => by simp [hn])
  rw [isUnit_coe_iff]
  filter_upwards [hp, eventually_eval_ne_zero hp0, eventually_eval_ne_zero hq] with n h1 h2 h3
  rw [h1]
  exact div_ne_zero h2 h3

/-- CO-483. Every nonzero rational sequence is hypergeometric: if `a = p/q` with `p, q ≠ 0` then
`q(n) p(n+1) a(n+1) - ... `; concretely `a(n+1) / a(n) = ...` is rational, i.e. `a` satisfies
`P(n) a(n+1) + Q(n) a(n) = 0` with nonzero polynomials `P = q(n+1) p(n)`, `Q = -p(n+1) q(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text after Definition 8.2.1, p. 158"]
theorem IsRationalSeq.isHypergeometric {a : ℕ → K} (h : IsRationalSeq a)
    (h0 : (a : SeqRing K) ≠ 0) : IsHypergeometric a := by
  obtain ⟨p, q, hq, hp⟩ := h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply h0
    exact coe_eq_zero_iff.2 (hp.mono fun n hn => by simp [hn])
  have hX : (X + 1 : K[X]) = X + C 1 := by simp
  have hq1 : q.comp (X + 1) ≠ 0 := by rw [hX]; exact comp_X_add_C_ne_zero_iff.2 hq
  have hp1 : p.comp (X + 1) ≠ 0 := by rw [hX]; exact comp_X_add_C_ne_zero_iff.2 hp0
  have hp' : ∀ᶠ n : ℕ in atTop, a (n + 1) = p.eval ((n + 1 : ℕ) : K) / q.eval ((n + 1 : ℕ) : K) :=
    (tendsto_add_atTop_nat 1).eventually hp
  refine ⟨fun hz => h0 (coe_eq_zero_iff.2 hz), q.comp (X + 1) * p, -(p.comp (X + 1) * q),
    mul_ne_zero hq1 hp0, neg_ne_zero.2 (mul_ne_zero hp1 hq), ?_⟩
  filter_upwards [hp, hp', eventually_eval_ne_zero hp0, eventually_eval_ne_zero hq,
    (tendsto_add_atTop_nat 1).eventually (eventually_eval_ne_zero hq)] with n h1 h2 h3 h4 h5
  have e : ∀ r : K[X], (r.comp (X + 1)).eval (n : K) = r.eval ((n + 1 : ℕ) : K) := by
    intro r; simp [eval_comp]
  simp only [eval_mul, eval_neg, e]
  rw [h1, h2]
  field_simp
  ring

/-! ### Proposition 8.2.1 and Corollary 8.2.1 -/

/-- If `y(n+1) = a(n) y(n)` for large `n` and `y` is not eventually zero, then `y` is eventually
nonzero (and so is `a`). -/
theorem eventually_ne_zero_of_shift_eq {y a : ℕ → K}
    (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (h : ∀ᶠ n : ℕ in atTop, y (n + 1) = a n * y n) :
    (∀ᶠ n : ℕ in atTop, y n ≠ 0) ∧ ∀ᶠ n : ℕ in atTop, a n ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have key : ∀ m, N ≤ m → y m = 0 → ∀ n, m ≤ n → y n = 0 := by
    intro m hm h0 n hn
    induction n, hn using Nat.le_induction with
    | base => exact h0
    | succ n hn ih => rw [hN n (hm.trans hn), ih, mul_zero]
  have hy' : ∀ᶠ n : ℕ in atTop, y n ≠ 0 := by
    by_contra hcon
    apply hy
    obtain ⟨m, hm, hm0⟩ : ∃ m ≥ N, y m = 0 := by
      by_contra hno
      push Not at hno
      exact hcon (eventually_atTop.2 ⟨N, fun n hn => hno n hn⟩)
    exact eventually_atTop.2 ⟨m, key m hm hm0⟩
  refine ⟨hy', ?_⟩
  filter_upwards [h, hy', (tendsto_add_atTop_nat 1).eventually hy'] with n h1 h2 h3
  intro ha
  apply h3
  rw [h1, ha, zero_mul]

/-- CO-484. Proposition 8.2.1: if `N y = a y` in `S(K)` with `y ≠ 0`, then both `y` and `a` are
units. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.2.1, p. 158"]
theorem isUnit_of_shift_eq {y a : SeqRing K} (hy : y ≠ 0) (h : shift y = a * y) :
    IsUnit y ∧ IsUnit a := by
  obtain ⟨f, rfl⟩ := exists_coe y
  obtain ⟨g, rfl⟩ := exists_coe a
  rw [shift_coe, ← Germ.coe_mul] at h
  have h' := coe_eq_coe_iff.1 h
  have hy' : ¬ ∀ᶠ n : ℕ in atTop, f n = 0 := fun hz => hy (coe_eq_zero_iff.2 hz)
  have := eventually_ne_zero_of_shift_eq hy' h'
  exact ⟨isUnit_coe_iff.2 this.1, isUnit_coe_iff.2 this.2⟩

/-- CO-485. Corollary 8.2.1: every hypergeometric sequence is a unit of `S(K)`. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 8.2.1, p. 158"]
theorem IsHypergeometric.isUnit {t : ℕ → K} (ht : IsHypergeometric t) :
    IsUnit (t : SeqRing K) :=
  isUnit_coe_iff.2 ht.eventually_ne_zero

end SeqRing

end UndergradKB.Combinatorics.AeqB
