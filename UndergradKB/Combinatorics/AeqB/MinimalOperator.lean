import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Identities3c

/-!
# Minimal operators and first-order right factors (Petkovsek–Wilf–Zeilberger, "A = B", §8.10, p. 173)

CO-509.  Recurrence operators with rational coefficients `K(n)[N; σ]` act on the ring `S(K)` of
sequences modulo eventual equality (`SeqRing K`): a rational function acts by multiplication by its
values `r(n)` (defined for all large `n`), and `N` acts by the shift.  This makes `S(K)` a module
over the operator ring (`seqModule`), so the division theory of operators (CO-506, CO-508) applies:

* every sequence annihilated by a nonzero operator has a minimal operator `M`, and every operator
  annihilating it is a left multiple `L = L₁ M` (`exists_minimal_operator`);
* a hypergeometric sequence `y` with ratio `y(n+1)/y(n) = r(n)` has minimal operator `N - r`, so it
  is a solution of `L y = 0` iff `N - r` is a right factor of `L`
  (`hyper_solution_iff_right_factor`);
* conversely every monic first-order right factor `N - r` (`r ≠ 0`) of `L` comes from a
  hypergeometric solution (`exists_hyper_solution_of_right_factor`), and the correspondence is
  one-to-one: the factor determines the solution up to a constant factor and the solution
  determines the factor (`right_factor_unique`, `hyper_solution_unique`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

namespace MinOp

/-! ### Values of rational functions -/

/-- The value `r(n)` of a rational function at a natural number (`0` at a pole). -/
def ratVal (r : RatFunc K) (n : ℕ) : K := RatFunc.eval (RingHom.id K) (n : K) r

theorem ratVal_def (r : RatFunc K) (n : ℕ) :
    ratVal r n = r.num.eval (n : K) / r.denom.eval (n : K) := rfl

theorem eventually_denom_ne_zero (r : RatFunc K) :
    ∀ᶠ n : ℕ in atTop, r.denom.eval (n : K) ≠ 0 :=
  eventually_eval_ne_zero (RatFunc.denom_ne_zero r)

/-- `p/q` takes the values `p(n)/q(n)` for large `n`. -/
theorem ratVal_div (p q : K[X]) (hq : q ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ratVal (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) n =
      p.eval (n : K) / q.eval (n : K) := by
  set x := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hx : x * algebraMap K[X] (RatFunc K) q = algebraMap K[X] (RatFunc K) p :=
    div_mul_cancel₀ _ hq'
  filter_upwards [eventually_denom_ne_zero x, eventually_eval_ne_zero hq] with n h1 h2
  have e := congrArg (RatFunc.eval (RingHom.id K) (n : K)) hx
  rw [RatFunc.eval_mul (RingHom.id K) (n : K) h1 (by rw [RatFunc.denom_algebraMap]; simp),
    RatFunc.eval_algebraMap,
    RatFunc.eval_algebraMap] at e
  rw [eq_div_iff h2]
  exact e

theorem ratVal_add (r s : RatFunc K) :
    ∀ᶠ n : ℕ in atTop, ratVal (r + s) n = ratVal r n + ratVal s n := by
  filter_upwards [eventually_denom_ne_zero r, eventually_denom_ne_zero s] with n h1 h2
  exact RatFunc.eval_add (RingHom.id K) (n : K) h1 h2

theorem ratVal_mul (r s : RatFunc K) :
    ∀ᶠ n : ℕ in atTop, ratVal (r * s) n = ratVal r n * ratVal s n := by
  filter_upwards [eventually_denom_ne_zero r, eventually_denom_ne_zero s] with n h1 h2
  exact RatFunc.eval_mul (RingHom.id K) (n : K) h1 h2

/-- A rational function vanishing at all large natural numbers is zero. -/
theorem eq_zero_of_ratVal (r : RatFunc K) (h : ∀ᶠ n : ℕ in atTop, ratVal r n = 0) : r = 0 := by
  have hnum : r.num = 0 := by
    apply eq_zero_of_eventually_eval_eq_zero
    filter_upwards [h, eventually_denom_ne_zero r] with n h1 h2
    rw [ratVal_def, div_eq_zero_iff] at h1
    exact h1.resolve_right h2
  rw [← RatFunc.num_div_denom r, hnum]
  simp

/-- The shift of a rational function takes the shifted values. -/
theorem ratVal_ratShift (r : RatFunc K) :
    ∀ᶠ n : ℕ in atTop, ratVal (ratShift K r) n = ratVal r (n + 1) := by
  have e : ratShift K r = algebraMap K[X] (RatFunc K) (r.num.comp (X + 1)) /
      algebraMap K[X] (RatFunc K) (r.denom.comp (X + 1)) := by
    unfold ratShift
    show RatFunc.map (compRingHom (X + 1 : K[X])) (by
      intro p hp
      rw [mem_nonZeroDivisors_iff_ne_zero] at hp
      show p.comp (X + 1) ∈ nonZeroDivisors K[X]
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact comp_X_add_one_ne_zero hp) r = _
    rw [RatFunc.map_apply]
    rfl
  have hd : r.denom.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero (RatFunc.denom_ne_zero r)
  filter_upwards [ratVal_div _ _ hd] with n hn
  rw [e, hn, ratVal_def]
  simp only [eval_comp, eval_add, eval_X, eval_one]
  push_cast
  rfl

/-! ### The module of sequences -/

/-- A rational function as an element of `S(K)` (its values for large `n`). -/
def ratGerm : RatFunc K →+* SeqRing K where
  toFun r := ((ratVal r : ℕ → K) : SeqRing K)
  map_one' := by
    show (((fun n => RatFunc.eval (RingHom.id K) (n : K) 1) : ℕ → K) : SeqRing K) = 1
    simp only [RatFunc.eval_one]; rfl
  map_mul' r s := by
    rw [← Germ.coe_mul]; exact Germ.coe_eq.2 (ratVal_mul r s)
  map_zero' := by
    show (((fun n => RatFunc.eval (RingHom.id K) (n : K) 0) : ℕ → K) : SeqRing K) = 0
    simp only [RatFunc.eval_zero]; rfl
  map_add' r s := by
    rw [← Germ.coe_add]; exact Germ.coe_eq.2 (ratVal_add r s)

theorem ratGerm_apply (r : RatFunc K) : ratGerm r = ((ratVal r : ℕ → K) : SeqRing K) := rfl

theorem ratGerm_ratShift (r : RatFunc K) : ratGerm (ratShift K r) = SeqRing.shift (ratGerm r) := by
  rw [ratGerm_apply, ratGerm_apply, SeqRing.shift_coe]
  exact Germ.coe_eq.2 (ratVal_ratShift r)

theorem ratGerm_ratShift_pow (k : ℕ) (r : RatFunc K) :
    ratGerm ((ratShift K ^ k) r) = (⇑SeqRing.shift)^[k] (ratGerm r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    show ratGerm (ratShift K ((ratShift K ^ k) r)) = _
    rw [ratGerm_ratShift, ih, Function.iterate_succ_apply']

/-- Multiplication by rational functions, as a ring homomorphism into the additive
endomorphisms of `S(K)`. -/
def mulHom : RatFunc K →+* AddMonoid.End (SeqRing K) where
  toFun r := AddMonoidHom.mulLeft (ratGerm r)
  map_one' := by ext y; show ratGerm 1 * y = y; rw [map_one, one_mul]
  map_mul' r s := by
    ext y; show ratGerm (r * s) * y = ratGerm r * (ratGerm s * y); rw [map_mul, mul_assoc]
  map_zero' := by ext y; show ratGerm 0 * y = 0; rw [map_zero, zero_mul]
  map_add' r s := by
    ext y; show ratGerm (r + s) * y = ratGerm r * y + ratGerm s * y; rw [map_add, add_mul]

/-- The shift `N` of `S(K)`, as an additive endomorphism. -/
def shiftEnd : AddMonoid.End (SeqRing K) := (SeqRing.shift : SeqRing K ≃+* SeqRing K).toAddMonoidHom

theorem shiftEnd_pow_apply (k : ℕ) (y : SeqRing K) :
    (shiftEnd ^ k : AddMonoid.End (SeqRing K)) y = (⇑SeqRing.shift)^[k] y := by
  rw [AddMonoid.End.coe_pow]; rfl

theorem iterate_shift_mul (k : ℕ) (a b : SeqRing K) :
    (⇑SeqRing.shift)^[k] (a * b) = (⇑SeqRing.shift)^[k] a * (⇑SeqRing.shift)^[k] b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_mul, ih, ← Function.iterate_succ_apply,
      ← Function.iterate_succ_apply]

/-- The action of `K(n)[N; σ]` on `S(K)`: `(∑ r_k(n) N^k) y = ∑ r_k(n) y(n+k)`. -/
def opHom : SkewPolynomial (RatFunc K) →+* AddMonoid.End (SeqRing K) :=
  SkewMonoidAlgebra.liftNCRingHom mulHom (powersHom _ shiftEnd) (by
    intro x y
    ext z
    induction y using Multiplicative.rec with | ofAdd k => ?_
    show ratGerm ((ratShift K ^ k) x) * (shiftEnd ^ k) z = (shiftEnd ^ k) (ratGerm x * z)
    rw [shiftEnd_pow_apply, shiftEnd_pow_apply, ratGerm_ratShift_pow, iterate_shift_mul])

/-- `S(K)` is a module over the recurrence operators with rational coefficients. -/
scoped instance seqModule : Module (SkewPolynomial (RatFunc K)) (SeqRing K) :=
  Module.compHom (SeqRing K) (opHom (K := K))

theorem smul_def (L : SkewPolynomial (RatFunc K)) (y : SeqRing K) : L • y = opHom L y := rfl

theorem monomial_smul (k : ℕ) (r : RatFunc K) (y : SeqRing K) :
    SkewPolynomial.monomial k r • y = ratGerm r * (⇑SeqRing.shift)^[k] y := by
  rw [smul_def]
  have h : opHom (K := K) (SkewPolynomial.monomial k r) = mulHom r * shiftEnd ^ k := by
    rw [SkewPolynomial.monomial_def]
    exact SkewMonoidAlgebra.liftNC_single _ _ _ _
  rw [h]
  show ratGerm r * (shiftEnd ^ k) y = _
  rw [shiftEnd_pow_apply]

/-- The first-order operator `N - r`. -/
def firstOrderOp (r : RatFunc K) : SkewPolynomial (RatFunc K) :=
  SkewPolynomial.monomial 1 1 - SkewPolynomial.monomial 0 r

theorem firstOrderOp_smul (r : RatFunc K) (y : SeqRing K) :
    firstOrderOp r • y = SeqRing.shift y - ratGerm r * y := by
  rw [firstOrderOp, sub_smul, monomial_smul, monomial_smul, map_one, one_mul]
  rfl

theorem firstOrderOp_ne_zero (r : RatFunc K) : firstOrderOp r ≠ 0 := by
  intro h
  have := congrArg (fun L : SkewPolynomial (RatFunc K) => L.coeff 1) h
  simp [firstOrderOp, SkewPolynomial.coeff_monomial, SkewPolynomial.coeff_sub] at this

theorem coeff_firstOrderOp (r : RatFunc K) (k : ℕ) :
    (firstOrderOp r).coeff k = (if 1 = k then 1 else 0) - (if 0 = k then r else 0) := by
  rw [firstOrderOp, SkewPolynomial.coeff_sub, SkewPolynomial.coeff_monomial,
    SkewPolynomial.coeff_monomial]

theorem skewOrder_firstOrderOp (r : RatFunc K) : skewOrder (firstOrderOp r) = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    rw [SkewPolynomial.mem_support_iff, coeff_firstOrderOp] at hk
    by_contra h
    simp only [id] at h
    apply hk
    have h0 : ¬ (0 = k) := by omega
    have h1 : ¬ (1 = k) := by omega
    simp only [h0, h1, ite_false, sub_zero]
  · apply Finset.le_sup (f := id)
    rw [SkewPolynomial.mem_support_iff, coeff_firstOrderOp]
    simp

/-! ### Minimal operators -/

/-- CO-509. Every sequence annihilated by a nonzero operator with rational coefficients has a
minimal operator `M` (nonzero, annihilating, of least order), and every annihilating operator is a
left multiple of it: `L y = 0` implies `L = L₁ M`. -/
@[kb "petkovsekwilfzeilberger1996" "text (minimal operator), p. 173"]
theorem exists_minimal_operator (y : SeqRing K)
    (hy : ∃ L : SkewPolynomial (RatFunc K), L ≠ 0 ∧ L • y = 0) :
    ∃ M : SkewPolynomial (RatFunc K), M ≠ 0 ∧ M • y = 0 ∧
      (∀ L : SkewPolynomial (RatFunc K), L ≠ 0 → L • y = 0 → skewOrder M ≤ skewOrder L) ∧
      ∀ L : SkewPolynomial (RatFunc K), L • y = 0 → ∃ L₁, L = L₁ * M := by
  classical
  have hex : ∃ d, ∃ L : SkewPolynomial (RatFunc K), L ≠ 0 ∧ L • y = 0 ∧ skewOrder L = d := by
    obtain ⟨L, h1, h2⟩ := hy; exact ⟨_, L, h1, h2, rfl⟩
  obtain ⟨M, hM0, hMy, hMd⟩ := Nat.find_spec hex
  have hmin : ∀ L : SkewPolynomial (RatFunc K), L ≠ 0 → L • y = 0 →
      skewOrder M ≤ skewOrder L := by
    intro L hL0 hLy
    rw [hMd]
    exact Nat.find_min' hex ⟨L, hL0, hLy, rfl⟩
  exact ⟨M, hM0, hMy, hmin, fun L hL =>
    Identities3c.minimal_annihilator_dvd y M hM0 hMy hmin L hL⟩

/-- An operator of order `0` (a rational function) kills an eventually nonzero sequence only if it
is zero. -/
theorem eq_zero_of_order_zero_smul {y : ℕ → K} (hy : ∀ᶠ n : ℕ in atTop, y n ≠ 0)
    (R : SkewPolynomial (RatFunc K)) (hR : ∀ k ∈ R.support, k < 1) (h : R • (y : SeqRing K) = 0) :
    R = 0 := by
  have hRC : R = SkewPolynomial.monomial 0 (R.coeff 0) := by
    rw [SkewPolynomial.ext_iff]
    intro k
    rw [SkewPolynomial.coeff_monomial]
    by_cases hk : k = 0
    · subst hk; simp
    · simp only [show ¬ (0 = k) from Ne.symm hk, ite_false]
      by_contra hne
      have := hR k (SkewPolynomial.mem_support_iff.2 hne)
      omega
  rw [hRC, monomial_smul, Function.iterate_zero, id, ratGerm_apply, ← Germ.coe_mul,
    SeqRing.coe_eq_zero_iff] at h
  have hc : R.coeff 0 = 0 := by
    apply eq_zero_of_ratVal
    filter_upwards [h, hy] with n h1 h2
    exact (mul_eq_zero.1 h1).resolve_right h2
  rw [hRC, hc, map_zero]

/-- The ratio of a hypergeometric sequence: `y(n+1) = r(n) y(n)` for large `n`, with `r ≠ 0`. -/
theorem IsHypergeometric.exists_ratio {y : ℕ → K} (hy : IsHypergeometric y) :
    ∃ r : RatFunc K, r ≠ 0 ∧ ∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n := by
  obtain ⟨-, p, q, hp, hq, h⟩ := isHypergeometric_iff.1 hy
  refine ⟨algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q,
    div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq), ?_⟩
  filter_upwards [h, ratVal_div p q hq, eventually_eval_ne_zero hq] with n h1 h2 h3
  rw [h2, div_mul_eq_mul_div, eq_div_iff h3, mul_comm]
  exact h1

/-- `N - r` annihilates `y` iff `y(n+1) = r(n) y(n)` for large `n`. -/
theorem firstOrderOp_smul_eq_zero_iff (r : RatFunc K) (y : ℕ → K) :
    firstOrderOp r • (y : SeqRing K) = 0 ↔ ∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n := by
  rw [firstOrderOp_smul, SeqRing.shift_coe, ratGerm_apply, ← Germ.coe_mul, sub_eq_zero,
    SeqRing.coe_eq_coe_iff]
  rfl

/-- CO-509. A hypergeometric sequence `y` with ratio `r` (`y(n+1) = r(n) y(n)`) is a solution of
`L y = 0` iff the monic first-order operator `N - r` is a right factor of `L`. -/
@[kb "petkovsekwilfzeilberger1996" "text (minimal operator), p. 173"]
theorem hyper_solution_iff_right_factor {y : ℕ → K} (hy : IsHypergeometric y) {r : RatFunc K}
    (hr : ∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n) (L : SkewPolynomial (RatFunc K)) :
    L • (y : SeqRing K) = 0 ↔ ∃ L₁, L = L₁ * firstOrderOp r := by
  have hNy : firstOrderOp r • (y : SeqRing K) = 0 := (firstOrderOp_smul_eq_zero_iff r y).2 hr
  constructor
  · intro hL
    obtain ⟨Q, R, hQR, hR⟩ := skew_right_division L (firstOrderOp r) (firstOrderOp_ne_zero r)
    rw [skewOrder_firstOrderOp] at hR
    have hRy : R • (y : SeqRing K) = 0 := by
      have h1 : L • (y : SeqRing K) = (Q * firstOrderOp r) • (y : SeqRing K) + R • y := by
        rw [hQR, add_smul]
      rw [mul_smul, hNy, smul_zero, zero_add, hL] at h1
      exact h1.symm
    have := eq_zero_of_order_zero_smul hy.eventually_ne_zero R hR hRy
    exact ⟨Q, by rw [hQR, this, add_zero]⟩
  · rintro ⟨L₁, rfl⟩
    rw [mul_smul, hNy, smul_zero]

/-- CO-509. Conversely, a monic first-order right factor `N - r` (`r ≠ 0`) of `L` gives a
hypergeometric solution of `L y = 0` with ratio `r`. -/
@[kb "petkovsekwilfzeilberger1996" "text (minimal operator), p. 173"]
theorem exists_hyper_solution_of_right_factor (L L₁ : SkewPolynomial (RatFunc K)) (r : RatFunc K)
    (hr : r ≠ 0) (hL : L = L₁ * firstOrderOp r) :
    ∃ y : ℕ → K, IsHypergeometric y ∧ (∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n) ∧
      L • (y : SeqRing K) = 0 := by
  classical
  have hnum : r.num ≠ 0 := by
    intro h; apply hr; rw [← RatFunc.num_div_denom r, h]; simp
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_eval_ne_zero hnum).and (eventually_denom_ne_zero r))
  let y : ℕ → K := fun n => ∏ i ∈ Finset.Ico N n, ratVal r i
  have hrec : ∀ n ≥ N, y (n + 1) = ratVal r n * y n := by
    intro n hn
    simp only [y]
    rw [Finset.prod_Ico_succ_top hn, mul_comm]
  have hval : ∀ i ≥ N, ratVal r i ≠ 0 := by
    intro i hi
    rw [ratVal_def]
    exact div_ne_zero (hN i hi).1 (hN i hi).2
  have hne : ∀ n, y n ≠ 0 := by
    intro n
    exact Finset.prod_ne_zero_iff.2 fun i hi => hval i (Finset.mem_Ico.1 hi).1
  have hrat : ∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n := eventually_atTop.2 ⟨N, hrec⟩
  refine ⟨y, ?_, hrat, ?_⟩
  · rw [isHypergeometric_iff]
    refine ⟨Eventually.of_forall hne, r.num, r.denom, hnum, RatFunc.denom_ne_zero r, ?_⟩
    filter_upwards [hrat, eventually_denom_ne_zero r] with n h1 h2
    rw [h1, ratVal_def]
    field_simp
  · rw [hL, mul_smul, (firstOrderOp_smul_eq_zero_iff r y).2 hrat, smul_zero]

/-- CO-509. The correspondence is one-to-one, first half: a hypergeometric sequence determines its
first-order right factor, i.e. if `N - r` and `N - s` both annihilate `y` then `r = s`. -/
@[kb "petkovsekwilfzeilberger1996" "text (minimal operator), p. 173"]
theorem right_factor_unique {y : ℕ → K} (hy : IsHypergeometric y) {r s : RatFunc K}
    (hr : firstOrderOp r • (y : SeqRing K) = 0) (hs : firstOrderOp s • (y : SeqRing K) = 0) :
    r = s := by
  rw [firstOrderOp_smul_eq_zero_iff] at hr hs
  rw [← sub_eq_zero]
  apply eq_zero_of_ratVal
  filter_upwards [hr, hs, hy.eventually_ne_zero, ratVal_add r (-s), ratVal_mul (-1) s]
    with n h1 h2 h3 h4 h5
  rw [sub_eq_add_neg, h4, show -s = (-1) * s by ring, h5]
  have : (ratVal r n - ratVal s n) * y n = 0 := by linear_combination h2 - h1
  have h6 := (mul_eq_zero.1 this).resolve_right h3
  have h7 : ratVal (-1 : RatFunc K) n = -1 := by
    rw [ratVal_def]
    have : (-1 : RatFunc K) = RatFunc.C (-1) := by simp
    rw [this, RatFunc.num_C, RatFunc.denom_C]
    simp
  rw [h7]
  linear_combination h6

/-- CO-509. The correspondence is one-to-one, second half: two hypergeometric solutions with the
same first-order right factor `N - r` agree up to a nonzero constant factor (for large `n`). -/
@[kb "petkovsekwilfzeilberger1996" "text (minimal operator), p. 173"]
theorem hyper_solution_unique {y z : ℕ → K} (hy : IsHypergeometric y) (hz : IsHypergeometric z)
    {r : RatFunc K} (hry : ∀ᶠ n : ℕ in atTop, y (n + 1) = ratVal r n * y n)
    (hrz : ∀ᶠ n : ℕ in atTop, z (n + 1) = ratVal r n * z n) :
    ∃ c : K, c ≠ 0 ∧ ∀ᶠ n : ℕ in atTop, z n = c * y n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((hry.and hrz).and hy.eventually_ne_zero).and hz.eventually_ne_zero)
  refine ⟨z N / y N, div_ne_zero (hN N le_rfl).2 (hN N le_rfl).1.2, eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    field_simp [(hN N le_rfl).1.2]
  | succ n hn ih =>
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hN n hn
    rw [h1, h2, ih]
    ring

end MinOp

end UndergradKB.Combinatorics.AeqB

end
