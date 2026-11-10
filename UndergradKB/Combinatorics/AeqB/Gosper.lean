import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharZero.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar

/-!
# Gosper's algorithm (Petkovsek–Wilf–Zeilberger, "A = B", Chapter 5)

Sequences are `ℕ → K` over a field `K` of characteristic zero, compared for large `n`; a rational
function is a pair of polynomials, the shift `n ↦ n + 1` is `p.comp (X + 1)`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### Theorem 5.2.1 -/

omit [CharZero K] in
/-- Evaluating a shifted polynomial. -/
theorem aeval_comp_X_add_C {L : Type*} [Field L] [Algebra K L] (p : K[X]) (x : L) (c : K) :
    aeval x (p.comp (X + C c)) = aeval (x + algebraMap K L c) p := by
  simp [aeval_comp]

/-- Key lemma for Theorem 5.2.1: if `g ≠ 0` is non-constant, there are roots `α, α + N` of `g`
in an algebraically closed extension with `N` maximal among such natural-number differences. -/
theorem exists_max_root_diff (L : Type*) [Field L] [CharZero L] [Algebra K L] [IsAlgClosed L]
    (g : K[X]) (hg : 0 < g.natDegree) :
    ∃ (N : ℕ) (α : L),
      aeval α g = 0 ∧ aeval (α + N) g = 0 ∧
        ∀ (M : ℕ) (β : L), aeval β g = 0 → aeval (β + M) g = 0 → M ≤ N := by
  classical
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hfin : {N : ℕ | ∃ α β : L, aeval α g = 0 ∧ aeval β g = 0 ∧ β = α + N}.Finite := by
    have hR : (↑(g.aroots L).toFinset : Set L).Finite := (g.aroots L).toFinset.finite_toSet
    have h2 : (Set.image2 (fun β α : L => β - α) (↑(g.aroots L).toFinset : Set L)
        ↑(g.aroots L).toFinset).Finite := Set.Finite.image2 _ hR hR
    refine (h2.preimage Nat.cast_injective.injOn).subset ?_
    rintro N ⟨α, β, ha, hb, rfl⟩
    refine ⟨α + N, ?_, α, ?_, by simp⟩
    all_goals simp [*]
  obtain ⟨α, ha⟩ : ∃ α : L, aeval α g = 0 :=
    IsAlgClosed.exists_aeval_eq_zero L g (natDegree_pos_iff_degree_pos.1 hg).ne'
  obtain ⟨N, ⟨α', β', ha', hb', hN⟩, hmax⟩ := Set.exists_max_image _ id hfin
    ⟨0, α, α, ha, ha, by simp⟩
  refine ⟨N, α', ha', hN ▸ hb', ?_⟩
  intro M β hβ hβM
  exact hmax M ⟨β, β + M, hβ, hβM, rfl⟩

/-- CO-398 (core form, equation (5.2.7)). Let `a, b, c` be polynomials with
`gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ`, and let `f, g` be coprime polynomials with
`a(n) f(n+1) g(n) - b(n-1) f(n) g(n+1) = c(n) g(n) g(n+1)`, i.e. `x = f/g` solves
`a(n) x(n+1) - b(n-1) x(n) = c(n)`.  Then `g` is a constant. -/
theorem natDegree_eq_zero_of_gosper_eq (a b c f g : K[X])
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hfg : IsCoprime f g)
    (h : a * f.comp (X + 1) * g - b.comp (X - 1) * f * g.comp (X + 1)
      = c * g * g.comp (X + 1)) :
    g.natDegree = 0 := by
  by_contra hne
  have hpos : 0 < g.natDegree := Nat.pos_of_ne_zero hne
  obtain ⟨N, α, hα, hβ, hmax⟩ := exists_max_root_diff (AlgebraicClosure K) g hpos
  -- evaluation of the identity at a point
  have E : ∀ x : AlgebraicClosure K, aeval x a * aeval (x + 1) f * aeval x g
      - aeval (x - 1) b * aeval x f * aeval (x + 1) g = aeval x c * aeval x g * aeval (x + 1) g := by
    intro x
    have := congrArg (aeval x) h
    simpa [aeval_comp, sub_eq_add_neg] using this
  have hfne : ∀ x : AlgebraicClosure K, aeval x g = 0 → aeval x f ≠ 0 := fun x hx hf => by
    rcases aeval_ne_zero_of_isCoprime hfg x with h | h <;> contradiction
  -- b vanishes at α + N - 1
  have hb : aeval (α + N - 1) b = 0 := by
    have e := E (α + N)
    rw [hβ] at e
    have h1 : aeval (α + N + 1) g ≠ 0 := by
      intro h0
      have := hmax (N + 1) α hα (by push_cast; rwa [← add_assoc])
      omega
    have : aeval (α + N - 1) b * aeval (α + N) f * aeval (α + N + 1) g = 0 := by
      linear_combination -e
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h1)).resolve_right (hfne _ hβ)
  -- a vanishes at α - 1
  have ha : aeval (α - 1) a = 0 := by
    have e := E (α - 1)
    rw [sub_add_cancel, hα] at e
    have h1 : aeval (α - 1) g ≠ 0 := by
      intro h0
      have := hmax (N + 1) (α - 1) h0 (by
        have : α - 1 + ((N + 1 : ℕ) : AlgebraicClosure K) = α + N := by push_cast; ring
        rw [this]; exact hβ)
      omega
    have : aeval (α - 1) a * aeval α f * aeval (α - 1) g = 0 := by
      linear_combination e
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h1)).resolve_right (hfne _ hα)
  rcases aeval_ne_zero_of_isCoprime (hab N) (α - 1) with h0 | h0
  · exact h0 ha
  · apply h0
    rw [aeval_comp_X_add_C]
    have : α - 1 + algebraMap K (AlgebraicClosure K) (N : K) = α + N - 1 := by simp; ring
    rw [this]; exact hb

/-! ### Shifts and a general form of Theorem 5.2.1 -/

theorem comp_X_add_C_ne_zero' {p : K[X]} (hp : p ≠ 0) (c : K) : p.comp (X + C c) ≠ 0 :=
  comp_X_add_C_ne_zero_iff.2 hp

theorem comp_X_add_one_ne_zero {p : K[X]} (hp : p ≠ 0) : p.comp (X + 1) ≠ 0 := by
  simpa using comp_X_add_C_ne_zero' hp 1

theorem comp_X_sub_one_ne_zero {p : K[X]} (hp : p ≠ 0) : p.comp (X - 1) ≠ 0 := by
  simpa [sub_eq_add_neg] using comp_X_add_C_ne_zero' hp (-1)

theorem comp_X_sub_one_comp_X_add_one (p : K[X]) : (p.comp (X - 1)).comp (X + 1) = p := by
  simp [comp_assoc]

theorem comp_X_add_one_comp_X_sub_one (p : K[X]) : (p.comp (X + 1)).comp (X - 1) = p := by
  simp [comp_assoc]

theorem eval_comp_X_add_one (p : K[X]) (n : ℕ) :
    (p.comp (X + 1)).eval (n : K) = p.eval ((n + 1 : ℕ) : K) := by
  simp [eval_comp]

omit [CharZero K] in
theorem exists_coprime_factor (F G : K[X]) (hG : G ≠ 0) :
    ∃ d f g : K[X], d ≠ 0 ∧ F = d * f ∧ G = d * g ∧ IsCoprime f g := by
  classical
  have hd0 : GCDMonoid.gcd F G ≠ 0 := gcd_ne_zero_of_right hG
  have hc := isCoprime_div_gcd_div_gcd (p := F) hG
  refine ⟨GCDMonoid.gcd F G, F / GCDMonoid.gcd F G, G / GCDMonoid.gcd F G, hd0, ?_, ?_, hc⟩
  · exact (EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_left F G)).symm
  · exact (EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_right F G)).symm

/-- CO-398 (Theorem 5.2.1, unreduced form). If `gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ` and
`a(n) F(n+1) G(n) - b(n-1) F(n) G(n+1) = c(n) G(n) G(n+1)` with `G ≠ 0` (so that `F/G` solves
`a x(n+1) - b(n-1) x(n) = c(n)`), then `G` divides `F`: the rational solution is a polynomial. -/
theorem dvd_of_gosper_eq (a b c F G : K[X])
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hG : G ≠ 0)
    (h : a * F.comp (X + 1) * G - b.comp (X - 1) * F * G.comp (X + 1)
      = c * G * G.comp (X + 1)) : G ∣ F := by
  obtain ⟨d, f, g, hd0, rfl, rfl, hcop⟩ := exists_coprime_factor F G hG
  have hg0 : g ≠ 0 := by rintro rfl; simp at hG
  have hd1 : d.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hd0
  have h2 : a * f.comp (X + 1) * g - b.comp (X - 1) * f * g.comp (X + 1)
      = c * g * g.comp (X + 1) := by
    apply mul_left_cancel₀ (mul_ne_zero hd0 hd1)
    simp only [mul_comp] at h
    linear_combination h
  have hdeg := natDegree_eq_zero_of_gosper_eq a b c f g hab hcop h2
  obtain ⟨r, hr⟩ := natDegree_eq_zero.1 hdeg
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hg0 hr.symm
  refine ⟨C r⁻¹ * f, ?_⟩
  rw [← hr]
  have : C r⁻¹ * C r = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hr0, C_1]
  linear_combination (-(d * f)) * this

/-- CO-398 (Theorem 5.2.1, book form). Let `a, b, c` be polynomials with
`gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ`, and let `x = f/g` be a rational function (`f, g`
coprime) satisfying `a(n) x(n+1) - b(n-1) x(n) = c(n)`, written without denominators as (5.2.7).
Then `x` is a polynomial: `g` is a nonzero constant and `f = p g` for a polynomial `p`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.2.1, p. 86"]
theorem gosper_rational_solution_is_polynomial (a b c f g : K[X])
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hfg : IsCoprime f g) (hg : g ≠ 0)
    (h : a * f.comp (X + 1) * g - b.comp (X - 1) * f * g.comp (X + 1)
      = c * g * g.comp (X + 1)) :
    g.natDegree = 0 ∧ ∃ p : K[X], f = p * g :=
  ⟨natDegree_eq_zero_of_gosper_eq a b c f g hab hfg h, by
    obtain ⟨p, hp⟩ := dvd_of_gosper_eq a b c f g hab hg h
    exact ⟨p, by rw [hp, mul_comm]⟩⟩

/-! ### CO-395, CO-396, CO-397: Gosper-summability and the reductions -/

/-- CO-395. A hypergeometric term `t` is Gosper-summable if some hypergeometric term `z` satisfies
`z(n+1) - z(n) = t(n)` (for large `n`); then the partial sums of `t` are `z` plus a constant. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) Gosper-summable, p. 84"]
def IsGosperSummable (t : ℕ → K) : Prop :=
  IsHypergeometric t ∧ ∃ z : ℕ → K, IsHypergeometric z ∧ ∀ᶠ n : ℕ in atTop, z (n + 1) - z n = t n

/-- CO-396. Reduction to rational functions: let `t` be eventually nonzero with
`q(n) t(n+1) = p(n) t(n)` (so the ratio is `r = p/q`), and write `z(n) = y(n) t(n)` with
`y = u/v` a rational function (`v(n) z(n) = u(n) t(n)`).  Then `z(n+1) - z(n) = t(n)` holds
for large `n` iff `r(n) y(n+1) - y(n) = 1`, i.e. (cross-multiplied)
`p(n) u(n+1) v(n) - q(n) u(n) v(n+1) = q(n) v(n) v(n+1)` as polynomials. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 85"]
theorem gosper_reduction_iff {t z : ℕ → K} {p q u v : K[X]}
    (ht : ∀ᶠ n : ℕ in atTop, t n ≠ 0) (hq : q ≠ 0) (hv : v ≠ 0)
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * t (n + 1) = p.eval (n : K) * t n)
    (hz : ∀ᶠ n : ℕ in atTop, v.eval (n : K) * z n = u.eval (n : K) * t n) :
    (∀ᶠ n : ℕ in atTop, z (n + 1) - z n = t n) ↔
      p * u.comp (X + 1) * v - q * u * v.comp (X + 1) = q * v * v.comp (X + 1) := by
  have hv0 := eventually_eval_ne_zero hv
  have hv1 : ∀ᶠ n : ℕ in atTop, v.eval ((n + 1 : ℕ) : K) ≠ 0 :=
    (tendsto_add_atTop_nat 1).eventually hv0
  have hz1 : ∀ᶠ n : ℕ in atTop, v.eval ((n + 1 : ℕ) : K) * z (n + 1)
      = u.eval ((n + 1 : ℕ) : K) * t (n + 1) := (tendsto_add_atTop_nat 1).eventually hz
  have key : ∀ᶠ n : ℕ in atTop, (z (n + 1) - z n = t n ↔
      (p * u.comp (X + 1) * v - q * u * v.comp (X + 1) - q * v * v.comp (X + 1)).eval (n : K)
        = 0) := by
    filter_upwards [ht, eventually_eval_ne_zero hq, hv0, hv1, hrel, hz, hz1] with
      n htn hqn hvn hv1n hr hzn hz1n
    simp only [eval_sub, eval_mul, eval_comp_X_add_one]
    constructor
    · intro hh
      apply mul_left_cancel₀ htn
      linear_combination (-(v.eval (n : K) * u.eval ((n + 1 : ℕ) : K))) * hr
        + (q.eval (n : K) * v.eval ((n + 1 : ℕ) : K)) * hzn
        - (q.eval (n : K) * v.eval (n : K)) * hz1n
        + (q.eval (n : K) * v.eval (n : K) * v.eval ((n + 1 : ℕ) : K)) * hh
    · intro hh
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hqn hvn) hv1n)
      linear_combination t n * hh + (v.eval (n : K) * u.eval ((n + 1 : ℕ) : K)) * hr
        - (q.eval (n : K) * v.eval ((n + 1 : ℕ) : K)) * hzn
        + (q.eval (n : K) * v.eval (n : K)) * hz1n
  constructor
  · intro h
    have : p * u.comp (X + 1) * v - q * u * v.comp (X + 1) - q * v * v.comp (X + 1) = 0 := by
      apply eq_zero_of_eventually_eval_eq_zero
      filter_upwards [h, key] with n h1 h2
      exact h2.1 h1
    exact sub_eq_zero.1 this
  · intro h
    filter_upwards [key] with n kn
    exact kn.2 (by rw [h, sub_self, eval_zero])

/-- CO-396 (consequence). For a hypergeometric `t` with `q(n) t(n+1) = p(n) t(n)`, `t` is
Gosper-summable iff the equation `r(n) y(n+1) - y(n) = 1` has a rational solution `y = u/v`,
i.e. iff `p(n) u(n+1) v(n) - q(n) u(n) v(n+1) = q(n) v(n) v(n+1)` for polynomials `u`, `v ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 85"]
theorem isGosperSummable_iff {t : ℕ → K} {p q : K[X]} (ht : IsHypergeometric t) (hq : q ≠ 0)
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * t (n + 1) = p.eval (n : K) * t n) :
    IsGosperSummable t ↔ ∃ u v : K[X], v ≠ 0 ∧
      p * u.comp (X + 1) * v - q * u * v.comp (X + 1) = q * v * v.comp (X + 1) := by
  have ht0 := ht.eventually_ne_zero
  constructor
  · rintro ⟨-, z, hzh, hdiff⟩
    have hz0 := hzh.eventually_ne_zero
    obtain ⟨-, P, Q, hP, hQ, hPQ⟩ := isHypergeometric_iff.1 hzh
    have hne : P - Q ≠ 0 := by
      intro h0
      obtain ⟨n, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := (((hdiff.and hPQ).and ht0).and
        (eventually_eval_ne_zero hQ)).exists
      have hpq : P.eval (n : K) - Q.eval (n : K) = 0 := by simpa using congrArg (eval (n : K)) h0
      apply h3
      have hQt : Q.eval (n : K) * t n = 0 := by
        linear_combination (-Q.eval (n : K)) * h1 + h2 + z n * hpq
      exact (mul_eq_zero.1 hQt).resolve_left h4
    have hz' : ∀ᶠ n : ℕ in atTop, (P - Q).eval (n : K) * z n = Q.eval (n : K) * t n := by
      filter_upwards [hdiff, hPQ] with n h1 h2
      simp only [eval_sub]
      linear_combination Q.eval (n : K) * h1 - h2
    exact ⟨Q, P - Q, hne, (gosper_reduction_iff ht0 hq hne hrel hz').1 hdiff⟩
  · rintro ⟨u, v, hv, h⟩
    have hu : u ≠ 0 := by
      rintro rfl
      simp only [zero_comp, mul_zero, zero_mul, sub_zero] at h
      exact mul_ne_zero (mul_ne_zero hq hv) (comp_X_add_one_ne_zero hv) h.symm
    have hv0 := eventually_eval_ne_zero hv
    let z : ℕ → K := fun n => u.eval (n : K) * t n / v.eval (n : K)
    have hz : ∀ᶠ n : ℕ in atTop, v.eval (n : K) * z n = u.eval (n : K) * t n := by
      filter_upwards [hv0] with n hn
      simp only [z]; field_simp
    have hdiff := (gosper_reduction_iff ht0 hq hv hrel hz).2 h
    exact ⟨ht, z, IsSimilar.isHypergeometric ⟨u, v, hu, hv, hz⟩ ht, hdiff⟩

/-- CO-397. Gosper's form and the reduction to `a(n) x(n+1) - b(n-1) x(n) = c(n)`.
Let `r = p/q` and suppose `p b c = q a c(n+1)`, i.e. `r(n) = a(n) c(n+1) / (b(n) c(n))`
(equation (5.2.3)).  Writing `y(n) = b(n-1) x(n) / c(n)` (equation (5.2.5)), the equation
`r(n) y(n+1) - y(n) = 1` (cross-multiplied, with `u = b(n-1) x(n)`, `v = c(n)`) is equivalent
to equation (5.2.6). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 85-86"]
theorem gosper_form_equiv {a b c p q x : K[X]} (hq : q ≠ 0) (hc : c ≠ 0)
    (hform : p * b * c = q * a * c.comp (X + 1)) :
    p * (b.comp (X - 1) * x).comp (X + 1) * c - q * (b.comp (X - 1) * x) * c.comp (X + 1)
        = q * c * c.comp (X + 1) ↔
      a * x.comp (X + 1) - b.comp (X - 1) * x = c := by
  have e : p * (b.comp (X - 1) * x).comp (X + 1) * c - q * (b.comp (X - 1) * x) * c.comp (X + 1)
      - q * c * c.comp (X + 1)
      = q * c.comp (X + 1) * (a * x.comp (X + 1) - b.comp (X - 1) * x - c) := by
    rw [mul_comp, comp_X_sub_one_comp_X_add_one]
    linear_combination x.comp (X + 1) * hform
  have hne : q * c.comp (X + 1) ≠ 0 := mul_ne_zero hq (comp_X_add_one_ne_zero hc)
  constructor
  · intro h
    have h0 : q * c.comp (X + 1) * (a * x.comp (X + 1) - b.comp (X - 1) * x - c) = 0 := by
      rw [← e, h, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hne)
  · intro h
    have h0 := e
    rw [h, sub_self, mul_zero] at h0
    exact sub_eq_zero.1 h0

/-- CO-399 (with CO-396, CO-397). For a hypergeometric term `t` whose ratio has the form
`t(n+1)/t(n) = a(n) c(n+1) / (b(n) c(n))` with `gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ`,
`t` is Gosper-summable iff `a(n) x(n+1) - b(n-1) x(n) = c(n)` has a polynomial solution `x`
(then `z(n) = b(n-1) x(n) t(n) / c(n)` is a hypergeometric antidifference). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 87"]
theorem isGosperSummable_iff_polynomial_solution {t : ℕ → K} {a b c : K[X]}
    (ht : IsHypergeometric t) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hrel : ∀ᶠ n : ℕ in atTop, (b * c).eval (n : K) * t (n + 1)
      = (a * c.comp (X + 1)).eval (n : K) * t n) :
    IsGosperSummable t ↔ ∃ x : K[X], a * x.comp (X + 1) - b.comp (X - 1) * x = c := by
  rw [isGosperSummable_iff ht (mul_ne_zero hb hc) hrel]
  constructor
  · rintro ⟨u, v, hv, hstar⟩
    have hb1 : b.comp (X - 1) ≠ 0 := comp_X_sub_one_ne_zero hb
    have hG : v * b.comp (X - 1) ≠ 0 := mul_ne_zero hv hb1
    have hG1 : (v * b.comp (X - 1)).comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hG
    have heq : a * (u * c).comp (X + 1) * (v * b.comp (X - 1))
        - b.comp (X - 1) * (u * c) * (v * b.comp (X - 1)).comp (X + 1)
        = c * (v * b.comp (X - 1)) * (v * b.comp (X - 1)).comp (X + 1) := by
      simp only [mul_comp, comp_X_sub_one_comp_X_add_one] at hstar ⊢
      linear_combination b.comp (X - 1) * hstar
    obtain ⟨x, hx⟩ := dvd_of_gosper_eq a b c _ _ hab hG heq
    refine ⟨x, ?_⟩
    rw [hx] at heq
    simp only [mul_comp, comp_X_sub_one_comp_X_add_one] at heq hG1
    apply mul_left_cancel₀ (mul_ne_zero hG hG1)
    linear_combination heq
  · rintro ⟨x, hx⟩
    exact ⟨b.comp (X - 1) * x, c, hc,
      (gosper_form_equiv (mul_ne_zero hb hc) hc (by ring)).2 hx⟩

/-! ### CO-401: resultants and shifts -/

/-- CO-401. The resultant `Res_n(f(n), g(n + α))` vanishes iff `f` and the shift `g(n + α)` have a
nonconstant common factor (are not coprime); here with Mathlib's `Polynomial.resultant`
for each fixed `α`.  Consequently the shifts `h ∈ ℕ` violating the gcd condition (5.2.4) are
exactly the natural-number zeros of `h ↦ Res_n(f(n), g(n+h))`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 89"]
theorem resultant_shift_eq_zero_iff {f g : K[X]} (hfg : f ≠ 0 ∨ g ≠ 0) (α : K) :
    resultant f (g.comp (X + C α)) = 0 ↔ ¬ IsCoprime f (g.comp (X + C α)) := by
  rw [resultant_eq_zero_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rcases hfg with hf | hg
  · exact Or.inl hf
  · exact Or.inr (comp_X_add_C_ne_zero' hg α)

/-- CO-401 (consequence). The gcd condition (5.2.4) holds iff no natural number is a zero of
`h ↦ Res_n(f(n), g(n+h))`. -/
theorem forall_isCoprime_shift_iff {f g : K[X]} (hfg : f ≠ 0 ∨ g ≠ 0) :
    (∀ h : ℕ, IsCoprime f (g.comp (X + C (h : K)))) ↔
      ∀ h : ℕ, resultant f (g.comp (X + C (h : K))) ≠ 0 := by
  refine forall_congr' fun h => ?_
  rw [Ne, resultant_shift_eq_zero_iff hfg, not_not]

/-! ### CO-411: k! is not Gosper-summable -/

/-- CO-411. Example 5.5.1: the partial sums of the factorials are not a hypergeometric term plus
a constant, i.e. `t(n) = n!` is not Gosper-summable. -/
@[kb "petkovsekwilfzeilberger1996" "Example 5.5.1, p. 96"]
theorem not_isGosperSummable_factorial : ¬ IsGosperSummable (fun n : ℕ => (n.factorial : K)) := by
  have hne : ∀ n : ℕ, (n.factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hrel : ∀ᶠ n : ℕ in atTop, (1 : K[X]).eval (n : K) * ((n + 1).factorial : K)
      = (X + 1 : K[X]).eval (n : K) * (n.factorial : K) :=
    Eventually.of_forall fun n => by simp [Nat.factorial_succ]
  have hX1 : (X + 1 : K[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : K)
  have ht : IsHypergeometric (fun n : ℕ => (n.factorial : K)) :=
    isHypergeometric_iff.2 ⟨Eventually.of_forall hne, X + 1, 1, hX1, one_ne_zero, hrel⟩
  intro hs
  obtain ⟨u, v, hv, hstar⟩ := (isGosperSummable_iff ht one_ne_zero hrel).1 hs
  have hab : ∀ h : ℕ, IsCoprime (X + 1 : K[X]) ((1 : K[X]).comp (X + C (h : K))) :=
    fun h => by rw [one_comp]; exact isCoprime_one_right
  have heq : (X + 1 : K[X]) * u.comp (X + 1) * v - (1 : K[X]).comp (X - 1) * u * v.comp (X + 1)
      = 1 * v * v.comp (X + 1) := by
    simpa using hstar
  obtain ⟨x, hx⟩ := dvd_of_gosper_eq (X + 1) 1 1 u v hab hv heq
  have hv1 := comp_X_add_one_ne_zero hv
  have hxe : (X + 1 : K[X]) * x.comp (X + 1) - x = 1 := by
    rw [hx] at heq
    simp only [mul_comp, one_comp] at heq
    apply mul_left_cancel₀ (mul_ne_zero hv hv1)
    linear_combination heq
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxe
  have h1 : (X + 1 : K[X]) * x.comp (X + 1) ≠ 0 :=
    mul_ne_zero hX1 (comp_X_add_one_ne_zero hx0)
  have hd1 : ((X + 1 : K[X]) * x.comp (X + 1)).natDegree = x.natDegree + 1 := by
    rw [natDegree_mul hX1 (comp_X_add_one_ne_zero hx0),
      natDegree_comp]
    simp [add_comm]
  have := congrArg natDegree hxe
  rw [natDegree_sub_eq_left_of_natDegree_lt (by omega)] at this
  simp at this
  omega

/-! ### Lemma 5.3.1 and Corollary 5.3.1 (uniqueness of the Gosper form) -/

theorem comp_shift_comp_shift (p : K[X]) (a b : K) :
    (p.comp (X + C a)).comp (X + C b) = p.comp (X + C (a + b)) := by
  rw [comp_assoc]
  congr 1
  simp only [add_comp, X_comp, C_comp, C_add]
  ring

theorem isCoprime_comp_shift {p q : K[X]} (h : IsCoprime p q) (c : K) :
    IsCoprime (p.comp (X + C c)) (q.comp (X + C c)) :=
  h.map (compRingHom (X + C c))

theorem dvd_comp_shift {p q : K[X]} (h : p ∣ q) (c : K) : p.comp (X + C c) ∣ q.comp (X + C c) :=
  (compRingHom (X + C c)).map_dvd h

/-- For `g ≠ 0` the shifts `g(n + k)` and `g(n - k)` are coprime to `g` for all large `k`
(this is where characteristic zero enters). -/
theorem exists_isCoprime_comp_shift (g : K[X]) (hg : g ≠ 0) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
      IsCoprime g (g.comp (X + C (k : K))) ∧ IsCoprime g (g.comp (X + C (-(k : K)))) := by
  by_cases hdeg : g.natDegree = 0
  · have hu : IsUnit g := by
      rw [eq_C_of_natDegree_eq_zero hdeg]
      refine isUnit_C.2 (isUnit_iff_ne_zero.2 ?_)
      intro h0
      apply hg
      rw [eq_C_of_natDegree_eq_zero hdeg, h0, C_0]
    obtain ⟨u, hu⟩ := hu
    refine ⟨0, fun k _ => ⟨⟨↑u⁻¹, 0, by rw [← hu]; simp⟩, ⟨↑u⁻¹, 0, by rw [← hu]; simp⟩⟩⟩
  · obtain ⟨N, α, hα, hβ, hmax⟩ := exists_max_root_diff (AlgebraicClosure K) g
      (Nat.pos_of_ne_zero hdeg)
    have key : ∀ k : ℕ, N + 1 ≤ k → IsCoprime g (g.comp (X + C (k : K))) := by
      intro k hk
      refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2 ?_
      intro x
      by_contra hcon
      push Not at hcon
      rw [aeval_comp_X_add_C] at hcon
      have := hmax k x hcon.1 (by simpa using hcon.2)
      omega
    refine ⟨N + 1, fun k hk => ⟨key k hk, ?_⟩⟩
    have := isCoprime_comp_shift (key k hk).symm (-(k : K))
    rwa [comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at this

/-- CO-405. Lemma 5.3.1: Let `a c1/(b c)` be in the form with `gcd(a, c) = gcd(b, c(n+1)) = 1`
and let `A C(n+1)/(B C)` be a form with `gcd(A, B(n+h)) = 1` for all `h ∈ ℕ`.  If the two
rational functions agree (cross-multiplied: `A b c C(n+1) = a B C c(n+1)`), then `c(n) ∣ C(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "Lemma 5.3.1, p. 92"]
theorem dvd_of_gosper_forms_eq {a b c a' b' c' : K[X]} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (ha : IsCoprime a c) (hb : IsCoprime b (c.comp (X + 1)))
    (hab' : ∀ h : ℕ, IsCoprime a' (b'.comp (X + C (h : K))))
    (h : a' * b * c * c'.comp (X + 1) = a * b' * c' * c.comp (X + 1)) : c ∣ c' := by
  obtain ⟨g, d, D, hg0, rfl, rfl, hdD⟩ := exists_coprime_factor c c' hc'
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hc
  have hg1 : g.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hg0
  simp only [mul_comp] at h
  have h2 : a' * b * d * D.comp (X + 1) = a * b' * D * d.comp (X + 1) := by
    apply mul_left_cancel₀ (mul_ne_zero hg0 hg1)
    linear_combination h
  have hdc : d ∣ g * d := dvd_mul_left d g
  have had : IsCoprime a d := ha.of_isCoprime_of_dvd_right hdc
  -- d ∣ B d(n+1)
  have hd_div : d ∣ b' * d.comp (X + 1) := by
    have h3 : d ∣ (b' * d.comp (X + 1)) * (a * D) := ⟨a' * b * D.comp (X + 1), by
      linear_combination -h2⟩
    exact (IsCoprime.mul_right had.symm hdD).dvd_of_dvd_mul_right h3
  -- d(n+1) ∣ A d
  have hd1_div : d.comp (X + 1) ∣ a' * d := by
    have hb' : IsCoprime b (d.comp (X + 1)) :=
      hb.of_isCoprime_of_dvd_right (by simp)
    have hDD : IsCoprime (d.comp (X + 1)) (D.comp (X + 1)) := by
      simpa using isCoprime_comp_shift hdD 1
    have h3 : d.comp (X + 1) ∣ (a' * d) * (b * D.comp (X + 1)) := ⟨a * b' * D, by
      linear_combination h2⟩
    exact (IsCoprime.mul_right hb'.symm hDD).dvd_of_dvd_mul_right h3
  have hshift1 : ∀ (p : K[X]) (k : K), (p.comp (X + 1)).comp (X + C k) = p.comp (X + C (1 + k)) := by
    intro p k
    have : (X + 1 : K[X]) = X + C 1 := by simp
    rw [this, comp_shift_comp_shift]
  have hfwd : ∀ k : ℕ, d ∣ (∏ i ∈ Finset.range k, b'.comp (X + C (i : K))) *
      d.comp (X + C (k : K)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := dvd_comp_shift hd_div (k : K)
      rw [mul_comp, hshift1, show (1 + (k : K)) = ((k + 1 : ℕ) : K) by push_cast; ring] at hs
      rw [Finset.prod_range_succ, mul_assoc]
      exact ih.trans (mul_dvd_mul_left _ hs)
  have hbwd : ∀ k : ℕ, d ∣ (∏ i ∈ Finset.range k, a'.comp (X + C (-((i + 1 : ℕ) : K)))) *
      d.comp (X + C (-(k : K))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := dvd_comp_shift hd1_div (-((k + 1 : ℕ) : K))
      rw [mul_comp, hshift1, show (1 + -((k + 1 : ℕ) : K)) = -(k : K) by push_cast; ring] at hs
      rw [Finset.prod_range_succ, mul_assoc]
      exact ih.trans (mul_dvd_mul_left _ hs)
  obtain ⟨M, hM⟩ := exists_isCoprime_comp_shift d hd0
  obtain ⟨hc1, hc2⟩ := hM M le_rfl
  have hP := hc1.dvd_of_dvd_mul_right (hfwd M)
  have hP' := hc2.dvd_of_dvd_mul_right (hbwd M)
  have hcop : IsCoprime (∏ i ∈ Finset.range M, a'.comp (X + C (-((i + 1 : ℕ) : K))))
      (∏ i ∈ Finset.range M, b'.comp (X + C (i : K))) := by
    refine IsCoprime.prod_left fun j _ => IsCoprime.prod_right fun i _ => ?_
    have := isCoprime_comp_shift (hab' (i + j + 1)) (-((j + 1 : ℕ) : K))
    rwa [comp_shift_comp_shift, show (((i + j + 1 : ℕ) : K) + -((j + 1 : ℕ) : K)) = (i : K) by
      push_cast; ring] at this
  have hunit : IsUnit d := hcop.isUnit_of_dvd' hP' hP
  exact (IsUnit.mul_right_dvd hunit).2 (dvd_mul_right g D)

/-- CO-406. Corollary 5.3.1: the factorization of Theorem 5.3.1 is unique.  If
`r = a c(n+1) / (b c) = a' c'(n+1) / (b' c')` where both `(a, b, c)` and `(a', b', c')` satisfy
properties (i)-(iii) of Theorem 5.3.1 with `b, c, b', c'` monic, then they coincide. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 5.3.1, p. 93"]
theorem gosper_form_unique {a b c a' b' c' : K[X]} (hbm : b.Monic) (hcm : c.Monic)
    (hbm' : b'.Monic) (hcm' : c'.Monic)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hac : IsCoprime a c)
    (hbc : IsCoprime b (c.comp (X + 1)))
    (hab' : ∀ h : ℕ, IsCoprime a' (b'.comp (X + C (h : K)))) (hac' : IsCoprime a' c')
    (hbc' : IsCoprime b' (c'.comp (X + 1)))
    (h : a * c.comp (X + 1) * b' * c' = a' * c'.comp (X + 1) * b * c) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hc0 := hcm.ne_zero
  have hc0' := hcm'.ne_zero
  have h1 : c ∣ c' := dvd_of_gosper_forms_eq hc0 hc0' hac hbc hab' (by linear_combination -h)
  have h2 : c' ∣ c := dvd_of_gosper_forms_eq hc0' hc0 hac' hbc' hab (by linear_combination h)
  have hcc : c = c' := eq_of_monic_of_associated hcm hcm' (associated_of_dvd_dvd h1 h2)
  subst hcc
  have hc1 : c.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hc0
  have h3 : a * b' = a' * b := by
    apply mul_left_cancel₀ (mul_ne_zero hc0 hc1)
    linear_combination h
  have hb1 : b ∣ b' := by
    have : b ∣ a * b' := ⟨a', by linear_combination h3⟩
    have hco : IsCoprime b a := by simpa using (hab 0).symm
    exact hco.dvd_of_dvd_mul_left this
  have hb2 : b' ∣ b := by
    have : b' ∣ a' * b := ⟨a, by linear_combination -h3⟩
    have hco : IsCoprime b' a' := by simpa using (hab' 0).symm
    exact hco.dvd_of_dvd_mul_left this
  have hbb : b = b' := eq_of_monic_of_associated hbm hbm' (associated_of_dvd_dvd hb1 hb2)
  subst hbb
  exact ⟨mul_left_cancel₀ hbm.ne_zero (by linear_combination h3), rfl, rfl⟩

/-! ### CO-409: degree bounds for polynomial solutions (Section 5.4) -/

theorem natDegree_comp_shift (p : K[X]) (h : K) : (p.comp (X + C h)).natDegree = p.natDegree := by
  simp [natDegree_comp]

theorem leadingCoeff_comp_shift (p : K[X]) (h : K) :
    (p.comp (X + C h)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by simp)]; simp

theorem coeff_comp_shift_natDegree (p : K[X]) (h : K) :
    (p.comp (X + C h)).coeff p.natDegree = p.leadingCoeff := by
  rw [← natDegree_comp_shift p h, coeff_natDegree, leadingCoeff_comp_shift]

theorem comp_X_add_one_eq (p : K[X]) : p.comp (X + 1) = p.comp (X + C 1) := by simp

theorem comp_X_sub_one_eq (p : K[X]) : p.comp (X - 1) = p.comp (X + C (-1)) := by
  simp [sub_eq_add_neg]

/-- CO-409, Case 1. If `deg a ≠ deg b` or `lc a ≠ lc b`, the leading terms of
`a(n) x(n+1) - b(n-1) x(n)` do not cancel, so a nonzero polynomial solution `x` of
`a(n) x(n+1) - b(n-1) x(n) = c(n)` has `deg x = deg c - max (deg a, deg b)` (and `c ≠ 0`). -/
@[kb "petkovsekwilfzeilberger1996" "text, Case 1, p. 95"]
theorem natDegree_solution_case1 {a b c x : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (hne : a.natDegree ≠ b.natDegree ∨ a.leadingCoeff ≠ b.leadingCoeff)
    (h : a * x.comp (X + 1) - b.comp (X - 1) * x = c) :
    c ≠ 0 ∧ c.natDegree = x.natDegree + max a.natDegree b.natDegree := by
  have hx1 : x.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hx
  have hb1 : b.comp (X - 1) ≠ 0 := comp_X_sub_one_ne_zero hb
  have hdu : (a * x.comp (X + 1)).natDegree = a.natDegree + x.natDegree := by
    rw [natDegree_mul ha hx1, comp_X_add_one_eq, natDegree_comp_shift]
  have hdv : (b.comp (X - 1) * x).natDegree = b.natDegree + x.natDegree := by
    rw [natDegree_mul hb1 hx, comp_X_sub_one_eq, natDegree_comp_shift]
  have e1 : (a * x.comp (X + 1)).coeff (a.natDegree + x.natDegree)
      = a.leadingCoeff * x.leadingCoeff := by
    rw [← hdu, coeff_natDegree, leadingCoeff_mul, comp_X_add_one_eq, leadingCoeff_comp_shift]
  have e2 : a.natDegree = b.natDegree → (b.comp (X - 1) * x).coeff (a.natDegree + x.natDegree)
      = b.leadingCoeff * x.leadingCoeff := fun hdeg => by
    rw [hdeg, ← hdv, coeff_natDegree, leadingCoeff_mul, comp_X_sub_one_eq, leadingCoeff_comp_shift]
  have hL0 : c ≠ 0 := by
    rw [← h]
    intro h0
    have h0' : a * x.comp (X + 1) = b.comp (X - 1) * x := sub_eq_zero.1 h0
    have hdeg : a.natDegree = b.natDegree := by
      have := congrArg natDegree h0'
      rw [hdu, hdv] at this
      omega
    have hl : a.leadingCoeff = b.leadingCoeff := by
      have := congrArg (fun p => p.coeff (a.natDegree + x.natDegree)) h0'
      rw [e1, e2 hdeg] at this
      exact mul_right_cancel₀ (leadingCoeff_ne_zero.2 hx) this
    rcases hne with hne | hne
    · exact hne hdeg
    · exact hne hl
  refine ⟨hL0, ?_⟩
  rw [← h]
  by_cases hdeg : a.natDegree = b.natDegree
  · have hne' : a.leadingCoeff ≠ b.leadingCoeff := hne.resolve_left (not_not.2 hdeg)
    have hle : (a * x.comp (X + 1) - b.comp (X - 1) * x).natDegree ≤ a.natDegree + x.natDegree := by
      refine (natDegree_sub_le _ _).trans ?_
      rw [hdu, hdv, hdeg]; simp
    rw [max_eq_left hdeg.ge, add_comm x.natDegree a.natDegree]
    refine le_antisymm hle ?_
    apply le_natDegree_of_ne_zero
    rw [coeff_sub, e1, e2 hdeg, ← sub_mul]
    exact mul_ne_zero (sub_ne_zero.2 hne') (leadingCoeff_ne_zero.2 hx)
  · rcases lt_or_gt_of_ne hdeg with hlt | hlt
    · rw [natDegree_sub_eq_right_of_natDegree_lt (by omega), hdv]; omega
    · rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hdu]; omega

omit [CharZero K] in
theorem natDegree_sub_le_pred {p q : K[X]} {m : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ m)
    (hc : p.coeff m = q.coeff m) : (p - q).natDegree ≤ m - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_sub]
  rcases Nat.lt_or_ge m N with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
      sub_zero]
  · have : N = m := by omega
    subst this
    rw [hc, sub_self]

omit [CharZero K] in
theorem coeff_comp_X_add_one_pred (x : K[X]) (m : ℕ) (hm : x.natDegree = m + 1) :
    (x.comp (X + 1)).coeff m = x.coeff m + ((m : K) + 1) * x.coeff (m + 1) := by
  show (x.eval₂ C (X + 1)).coeff m = _
  rw [eval₂_eq_sum_range, hm, finsetSum_coeff, Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : ∑ i ∈ Finset.range m, (C (x.coeff i) * (X + 1) ^ i).coeff m = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_C_mul, coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]
    simp
  rw [h0, coeff_C_mul, coeff_C_mul, coeff_X_add_one_pow, coeff_X_add_one_pow, Nat.choose_self,
    Nat.choose_succ_self_right]
  push_cast
  ring

/-- CO-409, Cases 2a/2b (coefficient computation (5.4.3)).  Suppose `deg a = deg b = k ≥ 1`,
`lc a = lc b = λ`, and `x ≠ 0` has degree `d`.  Then `a(n) x(n+1) - b(n-1) x(n)` has degree at most
`k + d - 1`, and its coefficient of `n^{k+d-1}` is `lc x * (λ d + A - B)`, where
`A` and `B` are the coefficients of `n^{k-1}` in `a(n)` and `b(n-1)` respectively. -/
@[kb "petkovsekwilfzeilberger1996" "text, Case 2, p. 95"]
theorem coeff_gosper_lhs_case2 {a b x : K[X]} (hdeg : a.natDegree = b.natDegree)
    (hlc : a.leadingCoeff = b.leadingCoeff) (hk : 1 ≤ a.natDegree) :
    (a * x.comp (X + 1) - b.comp (X - 1) * x).natDegree ≤ a.natDegree - 1 + x.natDegree ∧
    (a * x.comp (X + 1) - b.comp (X - 1) * x).coeff (a.natDegree - 1 + x.natDegree)
      = x.leadingCoeff * (a.leadingCoeff * (x.natDegree : K) +
          (a.coeff (a.natDegree - 1) - (b.comp (X - 1)).coeff (a.natDegree - 1))) := by
  set k := a.natDegree with hkdef
  set d := x.natDegree with hddef
  set b' := b.comp (X - 1) with hb'
  set x1 := x.comp (X + 1) with hx1
  have hb'd : b'.natDegree = k := by rw [hb', comp_X_sub_one_eq, natDegree_comp_shift, hdeg]
  have hb'c : b'.coeff k = a.leadingCoeff := by
    rw [← hb'd, coeff_natDegree, hb', comp_X_sub_one_eq, leadingCoeff_comp_shift, hlc]
  have hx1d : x1.natDegree = d := by rw [hx1, comp_X_add_one_eq, natDegree_comp_shift]
  have hx1c : x1.coeff d = x.leadingCoeff := by
    rw [← hx1d, coeff_natDegree, hx1, comp_X_add_one_eq, leadingCoeff_comp_shift]
  have hac : a.coeff k = a.leadingCoeff := rfl
  have he : (a - b').natDegree ≤ k - 1 :=
    natDegree_sub_le_pred le_rfl hb'd.le (by rw [hb'c, hac])
  have hΔ : (x1 - x).natDegree ≤ d - 1 :=
    natDegree_sub_le_pred hx1d.le le_rfl (by rw [hx1c]; rfl)
  have hsplit : a * x1 - b' * x = (a - b') * x1 + b' * (x1 - x) := by ring
  rw [hsplit]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hΔ0 : x1 - x = 0 := by
      rw [eq_C_of_natDegree_le_zero (hΔ.trans (by omega)), coeff_sub]
      have h1 : x1.coeff 0 = x.leadingCoeff := by have := hx1c; rwa [hd0] at this
      have h2 : x.coeff 0 = x.leadingCoeff := by rw [leadingCoeff, ← hddef, hd0]
      rw [h1, h2, sub_self, C_0]
    rw [hΔ0, mul_zero, add_zero]
    have h1 : (a - b').natDegree + x1.natDegree ≤ k - 1 + d := by
      have := he; omega
    refine ⟨(natDegree_mul_le).trans (by rw [hx1d]; omega), ?_⟩
    have := coeff_mul_add_eq_of_natDegree_le (f := a - b') (g := x1) (df := k - 1) (dg := d) he hx1d.le
    rw [this, coeff_sub, hx1c, hd0]
    push_cast
    ring
  · obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hΔc : (x1 - x).coeff m = ((d : K)) * x.leadingCoeff := by
      have hl : x.leadingCoeff = x.coeff (m + 1) := by rw [leadingCoeff, ← hddef, hm]
      rw [coeff_sub, hx1, coeff_comp_X_add_one_pred x m hm, add_sub_cancel_left, hl, hm]
      push_cast
      ring
    have hm' : m = d - 1 := by omega
    have hkd : k - 1 + d = k + m := by omega
    rw [hkd]
    have hle1 : ((a - b') * x1).natDegree ≤ k + m := by
      refine natDegree_mul_le.trans ?_
      rw [hx1d]; have := he; omega
    have hle2 : (b' * (x1 - x)).natDegree ≤ k + m := by
      refine natDegree_mul_le.trans ?_
      rw [hb'd]; have := hΔ; omega
    refine ⟨(natDegree_add_le _ _).trans (max_le hle1 hle2), ?_⟩
    rw [coeff_add]
    have c1 : ((a - b') * x1).coeff (k + m) = (a - b').coeff (k - 1) * x.leadingCoeff := by
      have := coeff_mul_add_eq_of_natDegree_le (f := a - b') (g := x1) (df := k - 1) (dg := d) he hx1d.le
      rw [show k + m = k - 1 + d by omega, this, hx1c]
    have c2 : (b' * (x1 - x)).coeff (k + m) = a.leadingCoeff * ((d : K) * x.leadingCoeff) := by
      have := coeff_mul_add_eq_of_natDegree_le (f := b') (g := x1 - x) (df := k) (dg := m) hb'd.le
        (hΔ.trans (by omega))
      rw [this, hb'c, hΔc]
    rw [c1, c2, coeff_sub]
    ring

/-- CO-409, Cases 2a and 2b.  If `deg a = deg b = k ≥ 1` and `lc a = lc b = λ`, then for a nonzero
polynomial solution `x` of `a(n) x(n+1) - b(n-1) x(n) = c(n)`, either (2a)
`deg x = deg c - deg a + 1` (written `deg c + 1 = k + deg x`), or (2b) `deg x = (B - A)/λ` where
`A, B` are the coefficients of `n^{k-1}` in `a(n)` and `b(n-1)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, Cases 2a-2b, p. 95"]
theorem natDegree_solution_case2 {a b c x : K[X]} (ha : a ≠ 0) (hx : x ≠ 0)
    (hdeg : a.natDegree = b.natDegree) (hlc : a.leadingCoeff = b.leadingCoeff)
    (hk : 1 ≤ a.natDegree) (h : a * x.comp (X + 1) - b.comp (X - 1) * x = c) :
    c.natDegree + 1 = a.natDegree + x.natDegree ∨
      (x.natDegree : K) = ((b.comp (X - 1)).coeff (a.natDegree - 1) - a.coeff (a.natDegree - 1))
        / a.leadingCoeff := by
  obtain ⟨hle, hcoef⟩ := coeff_gosper_lhs_case2 (x := x) hdeg hlc hk
  rw [h] at hle hcoef
  have hl : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 ha
  by_cases hE : a.leadingCoeff * (x.natDegree : K) +
      (a.coeff (a.natDegree - 1) - (b.comp (X - 1)).coeff (a.natDegree - 1)) = 0
  · right
    rw [eq_div_iff hl]
    linear_combination hE
  · left
    have hne : c.coeff (a.natDegree - 1 + x.natDegree) ≠ 0 := by
      rw [hcoef]; exact mul_ne_zero (leadingCoeff_ne_zero.2 hx) hE
    have := le_natDegree_of_ne_zero hne
    omega

end UndergradKB.Combinatorics.AeqB
