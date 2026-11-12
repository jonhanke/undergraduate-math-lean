import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# The q-analogue of algorithm Hyper (Petkovsek–Wilf–Zeilberger, "A = B", pp. 166 and 200)

Let `K` be a field and `q ≠ 0` an element of `K` that is not a root of unity.  We consider a
linear `q`-difference equation `∑_{i ≤ d} p_i(q^n) y(n+i) = 0` with polynomial coefficients
`p_i`.  A `q`-hypergeometric term `y` has `y(n+1)/y(n)` a rational function of `q^n`; its ratio
is put in the `q`-Gosper–Petkovsek shape
`z · a(q^n) / b(q^(n+1)) · c(q^(n+1)) / c(q^n)`  (definition `qHyperRatio`).

We prove:

* soundness: if the polynomial `c` satisfies the auxiliary `q`-recurrence
  `∑_i p_i(x) z^i ∏_{j<i} a(q^j x) ∏_{j=i}^{d-1} b(q^(j+1) x) c(q^i x) = 0`, then every term
  with that ratio solves the equation for large `n`;
* necessity: every eventually nonzero solution with that ratio (with `b`, `c` monic and the
  coprimality conditions) makes `c` satisfy the auxiliary recurrence, forces `a ∣ p_0` and
  `b ∣ p_d(q^(-d) x)`, and gives the leading coefficient equation for `z`.

Throughout, "for large `n`" is passed to polynomial identities in `x` using that the values
`q^n` are pairwise distinct, so a polynomial vanishing at `q^n` for all large `n` is zero.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

namespace QHyper

variable {K : Type*} [Field K]

/-! ### Scaling of the variable -/

/-- The scaling `f(x) ↦ f(r x)` on `K[x]`. -/
def qsh (r : K) (f : K[X]) : K[X] := f.comp (C r * X)

theorem qsh_qsh (r s : K) (f : K[X]) : qsh r (qsh s f) = qsh (s * r) f := by
  simp [qsh, comp_assoc, C_mul, mul_assoc]

theorem qsh_one (f : K[X]) : qsh (1 : K) f = f := by simp [qsh]

theorem qsh_ne_zero {r : K} (hr : r ≠ 0) {f : K[X]} (hf : f ≠ 0) : qsh r f ≠ 0 := by
  intro h
  exact hf ((comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hr)).1 h)

theorem qsh_dvd {r : K} {f g : K[X]} (h : f ∣ g) : qsh r f ∣ qsh r g :=
  by
  obtain ⟨k, hk⟩ := h
  exact ⟨qsh r k, by rw [hk]; simp only [qsh, mul_comp]⟩

theorem qsh_coprime {r : K} {f g : K[X]} (h : IsCoprime f g) : IsCoprime (qsh r f) (qsh r g) :=
  h.map (compRingHom (C r * X))

theorem eval_qsh (r x : K) (f : K[X]) : (qsh r f).eval x = f.eval (r * x) := by
  simp [qsh, eval_comp]

/-! ### Large `n` versus polynomial identities -/

section Eventually

variable {q : K}

theorem pow_injective (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) :
    Function.Injective (fun n : ℕ => q ^ n) := by
  have key : ∀ m n : ℕ, m < n → q ^ m ≠ q ^ n := by
    intro m n hmn h
    apply hq (n - m) (by omega)
    have : q ^ m * q ^ (n - m) = q ^ m * 1 := by
      rw [← pow_add, mul_one, Nat.add_sub_cancel' hmn.le]; exact h.symm
    exact mul_left_cancel₀ (pow_ne_zero m hq0) this
  intro m n h
  rcases lt_trichotomy m n with h1 | h1 | h1
  · exact absurd h (key m n h1)
  · exact h1
  · exact absurd h.symm (key n m h1)

theorem eventually_eval_pow_ne_zero (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    {f : K[X]} (hf : f ≠ 0) : ∀ᶠ n : ℕ in atTop, f.eval (q ^ n) ≠ 0 := by
  classical
  rw [← Nat.cofinite_eq_atTop]
  have hfin : (f.roots.toFinset : Set K).Finite := f.roots.toFinset.finite_toSet
  have : {n : ℕ | f.eval (q ^ n) = 0}.Finite := by
    refine (hfin.preimage (pow_injective hq0 hq).injOn).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp [hf, hn]
  filter_upwards [this.compl_mem_cofinite] with n hn
  exact hn

theorem eventually_eval_pow_shift_ne_zero (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    {f : K[X]} (hf : f ≠ 0) (j : ℕ) : ∀ᶠ n : ℕ in atTop, f.eval (q ^ (n + j)) ≠ 0 :=
  (tendsto_add_atTop_nat j).eventually (eventually_eval_pow_ne_zero hq0 hq hf)

theorem eq_zero_of_eventually_eval_pow (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    {f : K[X]} (h : ∀ᶠ n : ℕ in atTop, f.eval (q ^ n) = 0) : f = 0 := by
  by_contra hf
  obtain ⟨n, h1, h2⟩ := (h.and (eventually_eval_pow_ne_zero hq0 hq hf)).exists
  exact h2 h1

end Eventually

/-! ### The abstract sequence computation -/

theorem step_identity (z : K) (A B C : ℕ → K) (y : ℕ → K) (n i : ℕ)
    (hb : ∀ j < i, B (n + j) ≠ 0) (hc : ∀ j ≤ i, C (n + j) ≠ 0)
    (hS : ∀ j < i, y (n + j + 1) = z * (A (n + j) / B (n + j)) * (C (n + j + 1) / C (n + j)) *
      y (n + j)) :
    y (n + i) * (C n * ∏ j ∈ Finset.range i, B (n + j)) =
      z ^ i * (∏ j ∈ Finset.range i, A (n + j)) * C (n + i) * y n := by
  induction i with
  | zero => simp; ring
  | succ i ih =>
    have ih' := ih (fun j hj => hb j (by omega)) (fun j hj => hc j (by omega))
      (fun j hj => hS j (by omega))
    have hbi := hb i (by omega)
    have hci := hc i (by omega)
    have hci1 := hc (i + 1) le_rfl
    have hS' := hS i (by omega)
    rw [show n + (i + 1) = n + i + 1 from rfl, hS', Finset.prod_range_succ, Finset.prod_range_succ]
    calc _ = (z * A (n + i) * C (n + i + 1) / C (n + i)) *
          (y (n + i) * (C n * ∏ j ∈ Finset.range i, B (n + j))) := by
            field_simp
      _ = _ := by
            rw [ih']
            field_simp
            ring

theorem sum_identity (P : ℕ → K) (z : K) (A B C : ℕ → K) (y : ℕ → K) (n d : ℕ) (p : ℕ → K)
    (hP : ∀ i, P i = p i * (∏ j ∈ Finset.range i, A (n + j)) *
        ∏ j ∈ Finset.Ico i d, B (n + j))
    (hb : ∀ j < d, B (n + j) ≠ 0) (hc : ∀ j ≤ d, C (n + j) ≠ 0)
    (hS : ∀ j < d, y (n + j + 1) = z * (A (n + j) / B (n + j)) * (C (n + j + 1) / C (n + j)) *
      y (n + j)) :
    (∑ i ∈ Finset.range (d + 1), p i * y (n + i)) * (C n * ∏ j ∈ Finset.range d, B (n + j)) =
      y n * ∑ i ∈ Finset.range (d + 1), z ^ i * P i * C (n + i) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := by simpa [Nat.lt_succ_iff] using hi
  have step := step_identity z A B C y n i (fun j hj => hb j (by omega))
    (fun j hj => hc j (by omega)) (fun j hj => hS j (by omega))
  have hsplit : ∏ j ∈ Finset.range d, B (n + j) =
      (∏ j ∈ Finset.range i, B (n + j)) * ∏ j ∈ Finset.Ico i d, B (n + j) :=
    (Finset.prod_range_mul_prod_Ico (fun j => B (n + j)) hid).symm
  rw [hP, hsplit]
  calc p i * y (n + i) * (C n * ((∏ j ∈ Finset.range i, B (n + j)) *
          ∏ j ∈ Finset.Ico i d, B (n + j)))
      = p i * (y (n + i) * (C n * ∏ j ∈ Finset.range i, B (n + j))) *
          ∏ j ∈ Finset.Ico i d, B (n + j) := by ring
    _ = _ := by rw [step]; ring

/-! ### The q-Hyper data -/

/-- `P_i(x) = p_i(x) ∏_{j<i} a(q^j x) ∏_{j=i}^{d-1} b(q^(j+1) x)`. -/
def qHyperP (q : K) (p : ℕ → K[X]) (a b : K[X]) (d i : ℕ) : K[X] :=
  p i * (∏ j ∈ Finset.range i, qsh (q ^ j) a) * ∏ j ∈ Finset.Ico i d, qsh (q ^ (j + 1)) b

/-- The auxiliary `q`-recurrence `∑_i z^i P_i(x) c(q^i x) = 0`, as an identity of polynomials. -/
def QAuxRecurrence (q : K) (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d : ℕ) : Prop :=
  ∑ i ∈ Finset.range (d + 1), C (z ^ i) * qHyperP q p a b d i * qsh (q ^ i) c = 0

/-- The `q`-hypergeometric ratio `z · a(q^n)/b(q^(n+1)) · c(q^(n+1))/c(q^n)`. -/
def qHyperRatio (q z : K) (a b c : K[X]) (n : ℕ) : K :=
  z * (a.eval (q ^ n) / b.eval (q ^ (n + 1))) * (c.eval (q ^ (n + 1)) / c.eval (q ^ n))

/-- `α_i`: the coefficient of `x^m` in `P_i`, where `m` is the largest degree of the `P_i`. -/
def qHyperDeg (q : K) (p : ℕ → K[X]) (a b : K[X]) (d : ℕ) : ℕ :=
  (Finset.range (d + 1)).sup fun i => (qHyperP q p a b d i).natDegree

/-- The top coefficients `α_i`. -/
def qHyperAlpha (q : K) (p : ℕ → K[X]) (a b : K[X]) (d i : ℕ) : K :=
  (qHyperP q p a b d i).coeff (qHyperDeg q p a b d)

theorem qHyperP_eval (q : K) (p : ℕ → K[X]) (a b : K[X]) (d i n : ℕ) :
    (qHyperP q p a b d i).eval (q ^ n) = (p i).eval (q ^ n) *
      (∏ j ∈ Finset.range i, a.eval (q ^ (n + j))) *
        ∏ j ∈ Finset.Ico i d, b.eval (q ^ (n + j + 1)) := by
  simp only [qHyperP, eval_mul, eval_prod, eval_qsh]
  have h1 : ∏ j ∈ Finset.range i, a.eval (q ^ j * q ^ n) =
      ∏ j ∈ Finset.range i, a.eval (q ^ (n + j)) :=
    Finset.prod_congr rfl fun j _ => by rw [← pow_add, add_comm j n]
  have h2 : ∏ j ∈ Finset.Ico i d, b.eval (q ^ (j + 1) * q ^ n) =
      ∏ j ∈ Finset.Ico i d, b.eval (q ^ (n + j + 1)) :=
    Finset.prod_congr rfl fun j _ => by rw [← pow_add, add_comm (j + 1) n]; rfl
  rw [h1, h2]

theorem aux_eval (q : K) (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d n : ℕ) :
    (∑ i ∈ Finset.range (d + 1), C (z ^ i) * qHyperP q p a b d i * qsh (q ^ i) c).eval (q ^ n) =
      ∑ i ∈ Finset.range (d + 1),
        z ^ i * (qHyperP q p a b d i).eval (q ^ n) * c.eval (q ^ (n + i)) := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_qsh]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_add, add_comm i n]

section Main

variable {q : K}

theorem good_eventually (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) {z : K} {a b c : K[X]}
    {y : ℕ → K} (hb : b ≠ 0) (hc : c ≠ 0)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = qHyperRatio q z a b c n * y n) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, (∀ j < d, b.eval (q ^ (n + j + 1)) ≠ 0) ∧
      (∀ j ≤ d, c.eval (q ^ (n + j)) ≠ 0) ∧
      ∀ j < d, y (n + j + 1) = qHyperRatio q z a b c (n + j) * y (n + j) := by
  have h1 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range d, b.eval (q ^ (n + j + 1)) ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun j _ => by
      have := eventually_eval_pow_shift_ne_zero hq0 hq hb (j + 1)
      exact this
  have h2 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (d + 1), c.eval (q ^ (n + j)) ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun j _ => eventually_eval_pow_shift_ne_zero hq0 hq hc j
  have h3 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range d,
      y (n + j + 1) = qHyperRatio q z a b c (n + j) * y (n + j) :=
    (Filter.eventually_all_finset _).2 fun j _ => (tendsto_add_atTop_nat j).eventually hS
  filter_upwards [h1, h2, h3] with n a1 a2 a3
  exact ⟨fun j hj => a1 j (Finset.mem_range.2 hj),
    fun j hj => a2 j (Finset.mem_range.2 (by omega)), fun j hj => a3 j (Finset.mem_range.2 hj)⟩

theorem sum_identity_q (p : ℕ → K[X]) (z : K) (a b c : K[X]) (y : ℕ → K) (n d : ℕ)
    (hb : ∀ j < d, b.eval (q ^ (n + j + 1)) ≠ 0) (hc : ∀ j ≤ d, c.eval (q ^ (n + j)) ≠ 0)
    (hS : ∀ j < d, y (n + j + 1) = qHyperRatio q z a b c (n + j) * y (n + j)) :
    (∑ i ∈ Finset.range (d + 1), (p i).eval (q ^ n) * y (n + i)) *
        (c.eval (q ^ n) * ∏ j ∈ Finset.range d, b.eval (q ^ (n + j + 1))) =
      y n * ∑ i ∈ Finset.range (d + 1),
        z ^ i * (qHyperP q p a b d i).eval (q ^ n) * c.eval (q ^ (n + i)) := by
  have := sum_identity (fun i => (qHyperP q p a b d i).eval (q ^ n)) z
    (fun m => a.eval (q ^ m)) (fun m => b.eval (q ^ (m + 1))) (fun m => c.eval (q ^ m)) y n d
    (fun i => (p i).eval (q ^ n)) (fun i => qHyperP_eval q p a b d i n) hb hc hS
  exact this

/-- CO-495. Soundness of the `q`-analogue of algorithm Hyper (text, p. 166): if `c` satisfies the
auxiliary `q`-recurrence for `z, a, b` (with `b, c ≠ 0`, and `q` nonzero and not a root of unity)
and `y(n+1) = z · a(q^n)/b(q^(n+1)) · c(q^(n+1))/c(q^n) · y(n)` for large `n`, then
`∑_i p_i(q^n) y(n+i) = 0` for large `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text p.166"]
theorem qhyper_sound (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    (p : ℕ → K[X]) (d : ℕ) (z : K) (a b c : K[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrec : QAuxRecurrence q p a b c z d) (y : ℕ → K)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = qHyperRatio q z a b c n * y n) :
    ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (q ^ n) * y (n + i) = 0 := by
  have hE : ∀ n : ℕ, ∑ i ∈ Finset.range (d + 1),
      z ^ i * (qHyperP q p a b d i).eval (q ^ n) * c.eval (q ^ (n + i)) = 0 := by
    intro n
    have := aux_eval q p a b c z d n
    rw [hrec, eval_zero] at this
    exact this.symm
  filter_upwards [good_eventually hq0 hq (z := z) (a := a) (y := y) hb hc hS d,
    eventually_eval_pow_ne_zero hq0 hq hc] with n ⟨h1, h2, h3⟩ h4
  have key := sum_identity_q p z a b c y n d h1 h2 h3
  rw [hE n, mul_zero] at key
  have hne : c.eval (q ^ n) * ∏ j ∈ Finset.range d, b.eval (q ^ (n + j + 1)) ≠ 0 :=
    mul_ne_zero h4 (Finset.prod_ne_zero_iff.2 fun j hj => h1 j (Finset.mem_range.1 hj))
  exact (mul_eq_zero.1 key).resolve_right hne

/-- A sequence with `y(n+1) = r(n) y(n)` for large `n`, not eventually zero, is eventually
nonzero. -/
theorem eventually_ne_zero_of_shift_eq {y r : ℕ → K}
    (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (h : ∀ᶠ n : ℕ in atTop, y (n + 1) = r n * y n) : ∀ᶠ n : ℕ in atTop, y n ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have key : ∀ m, N ≤ m → y m = 0 → ∀ n, m ≤ n → y n = 0 := by
    intro m hm h0 n hn
    induction n, hn using Nat.le_induction with
    | base => exact h0
    | succ n hn ih => rw [hN n (hm.trans hn), ih, mul_zero]
  by_contra hcon
  apply hy
  obtain ⟨m, hm, hm0⟩ : ∃ m ≥ N, y m = 0 := by
    by_contra hno
    push Not at hno
    exact hcon (eventually_atTop.2 ⟨N, fun n hn => hno n hn⟩)
  exact eventually_atTop.2 ⟨m, key m hm hm0⟩

/-- The auxiliary `q`-recurrence follows from a `q`-hypergeometric solution. -/
theorem qaux_of_hyper (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    (p : ℕ → K[X]) (d : ℕ) (y : ℕ → K)
    (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (q ^ n) * y (n + i) = 0)
    (z : K) (a b c : K[X]) (hb : b ≠ 0) (hc : c ≠ 0)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = qHyperRatio q z a b c n * y n) :
    QAuxRecurrence q p a b c z d := by
  have hyne : ∀ᶠ n : ℕ in atTop, y n ≠ 0 := eventually_ne_zero_of_shift_eq hy hS
  apply eq_zero_of_eventually_eval_pow hq0 hq
  filter_upwards [good_eventually hq0 hq (z := z) (a := a) (y := y) hb hc hS d, hL, hyne,
    eventually_eval_pow_ne_zero hq0 hq hc] with n ⟨h1, h2, h3⟩ hLn hyn h4
  have key := sum_identity_q p z a b c y n d h1 h2 h3
  rw [hLn, zero_mul] at key
  rw [aux_eval]
  exact (mul_eq_zero.1 key.symm).resolve_left hyn

theorem qaux_dvd_a (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d : ℕ)
    (hrec : QAuxRecurrence q p a b c z d)
    (hab : ∀ h : ℕ, IsCoprime a (qsh (q ^ h) b)) (hac : IsCoprime a c) : a ∣ p 0 := by
  unfold QAuxRecurrence at hrec
  rw [Finset.sum_range_succ'] at hrec
  have h1 : a ∣ ∑ i ∈ Finset.range d,
      C (z ^ (i + 1)) * qHyperP q p a b d (i + 1) * qsh (q ^ (i + 1)) c := by
    refine Finset.dvd_sum fun i _ => ?_
    have : a ∣ ∏ j ∈ Finset.range (i + 1), qsh (q ^ j) a := by
      have h := Finset.dvd_prod_of_mem (fun j : ℕ => qsh (q ^ j) a)
        (Finset.mem_range.2 (Nat.succ_pos i))
      simp only [pow_zero, qsh_one] at h
      exact h
    unfold qHyperP
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right this _) _) _) _
  have h0 := (dvd_add_right h1).1 (by rw [hrec]; exact dvd_zero a)
  have hIco : Finset.Ico 0 d = Finset.range d := Nat.Ico_zero_eq_range d
  have e0 : C (z ^ 0) * qHyperP q p a b d 0 * qsh (q ^ 0) c =
      p 0 * ((∏ j ∈ Finset.range d, qsh (q ^ (j + 1)) b) * c) := by
    simp [qHyperP, hIco, qsh_one]
    ring
  rw [e0] at h0
  have hcop : IsCoprime a ((∏ j ∈ Finset.range d, qsh (q ^ (j + 1)) b) * c) :=
    IsCoprime.mul_right (IsCoprime.prod_right fun j _ => hab (j + 1)) hac
  exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using h0)

theorem qaux_dvd_b (hq0 : q ≠ 0) (p : ℕ → K[X]) (a b c : K[X]) (z : K) (hz : z ≠ 0) (e : ℕ)
    (hrec : QAuxRecurrence q p a b c z (e + 1))
    (hab : ∀ h : ℕ, IsCoprime a (qsh (q ^ h) b)) (hbc : IsCoprime b c) :
    qsh (q ^ (e + 1)) b ∣ p (e + 1) := by
  unfold QAuxRecurrence at hrec
  rw [Finset.sum_range_succ] at hrec
  set β := qsh (q ^ (e + 1)) b with hβ
  have h1 : β ∣ ∑ i ∈ Finset.range (e + 1),
      C (z ^ i) * qHyperP q p a b (e + 1) i * qsh (q ^ i) c := by
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i < e + 1 := Finset.mem_range.1 hi
    have : β ∣ ∏ j ∈ Finset.Ico i (e + 1), qsh (q ^ (j + 1)) b :=
      Finset.dvd_prod_of_mem (fun j : ℕ => qsh (q ^ (j + 1)) b)
        (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    unfold qHyperP
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right this _) _) _
  have h0 := (dvd_add_right h1).1 (by rw [hrec]; exact dvd_zero β)
  have hu : IsUnit (C (z ^ (e + 1)) : K[X]) :=
    isUnit_C.2 (IsUnit.mk0 _ (pow_ne_zero _ hz))
  have e0 : C (z ^ (e + 1)) * qHyperP q p a b (e + 1) (e + 1) * qsh (q ^ (e + 1)) c =
      C (z ^ (e + 1)) * ((p (e + 1) * ∏ j ∈ Finset.range (e + 1), qsh (q ^ j) a) *
        qsh (q ^ (e + 1)) c) := by
    simp [qHyperP]
    ring
  rw [e0] at h0
  have h2 := (hu.dvd_mul_left).1 h0
  have hca : IsCoprime β (∏ j ∈ Finset.range (e + 1), qsh (q ^ j) a) := by
    refine IsCoprime.prod_right fun j hj => ?_
    have hj' : j < e + 1 := Finset.mem_range.1 hj
    have := qsh_coprime (r := q ^ j) (hab (e + 1 - j))
    rw [qsh_qsh, ← pow_add, show e + 1 - j + j = e + 1 by omega] at this
    exact this.symm
  have hcc : IsCoprime β (qsh (q ^ (e + 1)) c) := qsh_coprime hbc
  have h3 := hcc.dvd_of_dvd_mul_right h2
  exact hca.dvd_of_dvd_mul_right h3

theorem natDegree_qsh_le (r : K) (c : K[X]) : (qsh r c).natDegree ≤ c.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [qsh, comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hN, zero_mul]

/-- CO-495. Necessary conditions for a `q`-hypergeometric solution (text, p. 166; the
`q`-analogue of Theorem 8.4.1).  Let `y` be a solution, not eventually zero, of
`∑_{i ≤ d} p_i(q^n) y(n+i) = 0` (`d ≥ 1`) with `y(n+1) = z a(q^n)/b(q^(n+1)) · c(q^(n+1))/c(q^n) · y(n)`
for large `n`, where `z ≠ 0`, `b, c` are monic, `a` is coprime to every `b(q^h x)` and to `c`, and
`b` is coprime to `c`.  Then (1) `∑ α_i (z q^(deg c))^i = 0`, (2) `a ∣ p_0`,
(3) `b ∣ p_d(q^(-d) x)`, (4) `c` satisfies the auxiliary `q`-recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "text p.166"]
theorem qhyper_necessary (hq0 : q ≠ 0) (hq : ∀ m : ℕ, 0 < m → q ^ m ≠ 1)
    (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d)
    (y : ℕ → K) (hy : ¬ ∀ᶠ n : ℕ in atTop, y n = 0)
    (hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (q ^ n) * y (n + i) = 0)
    (z : K) (hz : z ≠ 0) (a b c : K[X]) (hbm : b.Monic) (hcm : c.Monic)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (C (q ^ h) * X))) (hac : IsCoprime a c)
    (hbc : IsCoprime b c)
    (hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = qHyperRatio q z a b c n * y n) :
    (∑ i ∈ Finset.range (d + 1),
        qHyperAlpha q p a b d i * (z * q ^ c.natDegree) ^ i = 0) ∧ a ∣ p 0 ∧
      b ∣ (p d).comp (C ((q⁻¹) ^ d) * X) ∧ QAuxRecurrence q p a b c z d := by
  have hE := qaux_of_hyper hq0 hq p d y hy hL z a b c hbm.ne_zero hcm.ne_zero hS
  refine ⟨?_, qaux_dvd_a p a b c z d hE hab hac, ?_, hE⟩
  · have hco := congrArg (fun r : K[X] => r.coeff (qHyperDeg q p a b d + c.natDegree)) hE
    simp only [finsetSum_coeff, coeff_zero] at hco
    rw [← hco]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hP : (qHyperP q p a b d i).natDegree ≤ qHyperDeg q p a b d :=
      Finset.le_sup (f := fun i => (qHyperP q p a b d i).natDegree) hi
    rw [mul_assoc, coeff_C_mul,
      coeff_mul_add_eq_of_natDegree_le hP (natDegree_qsh_le (q ^ i) c)]
    have : (qsh (q ^ i) c).coeff c.natDegree = (q ^ i) ^ c.natDegree := by
      rw [qsh, comp_C_mul_X_coeff]
      have := hcm.leadingCoeff
      rw [leadingCoeff] at this
      rw [this, one_mul]
    rw [this]
    simp only [qHyperAlpha]
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm c.natDegree i]
    ring
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have h1 := qaux_dvd_b hq0 p a b c z hz e hE hab hbc
    have h2 := qsh_dvd (r := (q⁻¹) ^ (e + 1)) h1
    rw [qsh_qsh, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, qsh_one] at h2
    exact h2

end Main

end QHyper

end UndergradKB.Combinatorics.AeqB

end
