import Mathlib.Combinatorics.Derangements.Exponential
import UndergradKB.Combinatorics.Counting.Misc
import UndergradKB.Combinatorics.AeqB.Telescoping2
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.SequenceRing
import UndergradKB.Combinatorics.AeqB.SolutionSpace
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.Hyper
import UndergradKB.Combinatorics.AeqB.HyperAlgorithm
import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.OperatorsMore
import UndergradKB.Combinatorics.AeqB.Involutions
import UndergradKB.Combinatorics.AeqB.Companions
import UndergradKB.Combinatorics.AeqB.Identities3c
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 8: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch08b

open UndergradKB.Combinatorics.AeqB

universe u

/-- CO-431. Proposition 8.1.1: for `F` hypergeometric in `n` and `k` and a hypergeometric `f`
with ratio `f(n+1) = r(n) f(n)`, creative telescoping returns a first-order recurrence with
ratio `r` exactly when the WZ method proves `∑_k F = f`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.1.1, p. 153"]
theorem prop_8_1_1_ct_first_order_iff_wz {K : Type*} [Field K] (F : ℤ → ℤ → K) (f r : ℤ → K)
    (hf : ∀ n : ℤ, f n ≠ 0) (hr : ∀ n : ℤ, f (n + 1) = r n * f n) :
    Prop811.CTFirstOrder F r ↔ Prop811.WZProves F f :=
  Prop811.ctFirstOrder_iff_wzProves F f r hf hr

/-- CO-475. Every hypergeometric term has a closed form (a linear combination of one
hypergeometric term). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.1.1, p. 151"]
theorem def_8_1_1_hypergeometric_is_closed_form {K : Type*} [Field K] [CharZero K] {h : ℕ → K}
    (hh : IsHypergeometric h) : IsClosedForm h :=
  hh.isClosedForm

/-- CO-476. Closed-form decision procedure: if `f` has closed form and satisfies `L f = 0`
eventually, then `f` is an eventual sum of pairwise dissimilar hypergeometric terms, each
of which is itself a solution of `L`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 151"]
theorem text_p151_closed_form_dissimilar_solutions {K : Type*} [Field K] [CharZero K]
    (L : RecOp K) (f : ℕ → K) (hf : IsClosedForm f)
    (hL : ∀ᶠ n : ℕ in Filter.atTop, L.act f n = 0) :
    ∃ (r : ℕ) (J : Finset (Fin r)) (u : Fin r → ℕ → K),
      (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in Filter.atTop, f n = ∑ j ∈ J, u j n) ∧
      ∀ j ∈ J, ∀ᶠ n : ℕ in Filter.atTop, L.act (u j) n = 0 :=
  closedForm_dissimilar_solutions L f hf hL

/-- CO-478. Linear recurrence operators `∑ a_k N^k` on sequences: `y` lies in the kernel
exactly when `∑_k a_k(n) y(n+k) = 0` for all `n`; the solution set of `L y = f` is `0 ∉` for
`f ≠ 0`, is a translate of the kernel once one solution `y₀` is known, and is closed under
adding solutions for added right-hand sides. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (linear recurrence operator), p. 155"]
theorem def_p155_linear_recurrence_operator {K : Type*} [Field K] :
    (∀ (r : ℕ) (a : ℕ → ℕ → K) (y : ℕ → K),
      y ∈ LinearMap.ker (SeqOp.recOp r a) ↔ ∀ n : ℕ, ∑ k ∈ Finset.range (r + 1), a k n * y (n + k) = 0) ∧
    (∀ L : Module.End K (ℕ → K), SeqOp.solSet L 0 = ↑(LinearMap.ker L)) ∧
    (∀ (L : Module.End K (ℕ → K)) (f : ℕ → K), f ≠ 0 → 0 ∉ SeqOp.solSet L f) ∧
    (∀ (L : Module.End K (ℕ → K)) (f y₀ : ℕ → K), y₀ ∈ SeqOp.solSet L f →
      ∀ y : ℕ → K, y ∈ SeqOp.solSet L f ↔ y - y₀ ∈ LinearMap.ker L) ∧
    (∀ (L : Module.End K (ℕ → K)) (f₁ f₂ y₁ y₂ : ℕ → K), y₁ ∈ SeqOp.solSet L f₁ →
      y₂ ∈ SeqOp.solSet L f₂ → y₁ + y₂ ∈ SeqOp.solSet L (f₁ + f₂)) :=
  ⟨fun r a y => SeqOp.mem_ker_recOp r a y, fun L => SeqOp.solSet_zero L,
    fun L _ hf => SeqOp.zero_notMem_solSet L hf,
    fun _ _ _ h => SeqOp.mem_solSet_iff h, fun _ _ _ _ _ h1 h2 => SeqOp.add_mem_solSet h1 h2⟩

/-- CO-479. In the full sequence ring, first-order equations can have solution spaces of
dimension `0` (here the solution space is `⊥`), a finite positive dimension (`4` for the example
`exSol`), or infinite dimension (not finite-dimensional for the even/odd example). -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 8.2.1, p. 155"]
theorem ex_8_2_1_solution_space_dimensions {K : Type*} [Field K] [CharZero K] :
    ¬Module.Finite K (firstOrderSol (evenSeq K) (oddSeq K)) ∧
    firstOrderSol (evenSeq K) (fun _ : ℕ => (-1 : K)) = ⊥ ∧
    Module.finrank K (exSol K) = 4 :=
  ⟨not_finite_firstOrderSol_even_odd, firstOrderSol_even_neg_one, finrank_exSol⟩

/-- CO-480. The ring `S(K)` of sequences modulo eventual equality (Mathlib's germs at
infinity); the shift `N` descends to a ring automorphism given by `f(n) ↦ f(n+1)`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (S(K)), p. 156"]
theorem def_p156_seqring_shift {K : Type*} [Field K] (f : ℕ → K) :
    SeqRing.shift (f : SeqRing K) = ((fun n : ℕ => f (n + 1) : ℕ → K) : SeqRing K) :=
  SeqRing.shift_coe f

/-- CO-481. In `S(K)` a sequence is a unit iff it is eventually nonzero, and a nonzero
non-unit is exactly a zero divisor (infinitely many zero and infinitely many nonzero terms). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 156"]
theorem text_p156_units_and_zero_divisors {K : Type*} [Field K] :
    (∀ f : ℕ → K, IsUnit (f : SeqRing K) ↔ ∀ᶠ n : ℕ in Filter.atTop, f n ≠ 0) ∧
    (∀ f : ℕ → K, ((f : SeqRing K) ≠ 0 ∧ ¬IsUnit (f : SeqRing K)) ↔
      ((∃ᶠ n : ℕ in Filter.atTop, f n = 0) ∧ ∃ᶠ n : ℕ in Filter.atTop, f n ≠ 0)) ∧
    (∀ a : SeqRing K, a ≠ 0 → ((∃ b : SeqRing K, b ≠ 0 ∧ a * b = 0) ↔ ¬IsUnit a)) :=
  ⟨fun _ => SeqRing.isUnit_coe_iff, fun _ => SeqRing.nonzero_not_isUnit_iff,
    fun _ ha => SeqRing.isZeroDivisor_iff_not_isUnit ha⟩

/-- CO-482. Theorem 8.2.1: if the leading and trailing coefficients of a recurrence operator
of order `r` on `S(K)` are units, then its kernel has dimension `r`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.2.1, p. 157"]
theorem thm_8_2_1_kernel_dimension {K : Type*} [Field K] [CharZero K] (ps : ℕ → SeqRing K)
    (r : ℕ) (hr : IsUnit (ps r)) (h0 : IsUnit (ps 0)) :
    Module.finrank K (kerOp ps r) = r :=
  finrank_kerOp ps r hr h0

/-- CO-383. A sequence is hypergeometric when it is eventually nonzero and satisfies
`q(n) t(n+1) = p(n) t(n)` with nonzero polynomials `p, q`; equivalently its ratio
`t(n+1)/t(n)` is eventually a quotient of nonzero polynomials. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
theorem def_8_2_1_hypergeometric {K : Type*} [Field K] [CharZero K] (t : ℕ → K) :
    (IsHypergeometric t ↔ (∀ᶠ n : ℕ in Filter.atTop, t n ≠ 0) ∧
      ∃ p q : Polynomial K, p ≠ 0 ∧ q ≠ 0 ∧
        ∀ᶠ n : ℕ in Filter.atTop, Polynomial.eval (n : K) q * t (n + 1) = Polynomial.eval (n : K) p * t n) ∧
    (IsHypergeometric t ↔ (∀ᶠ n : ℕ in Filter.atTop, t n ≠ 0) ∧
      ∃ p q : Polynomial K, p ≠ 0 ∧ q ≠ 0 ∧
        ∀ᶠ n : ℕ in Filter.atTop, t (n + 1) / t n = Polynomial.eval (n : K) p / Polynomial.eval (n : K) q) :=
  ⟨isHypergeometric_iff, isHypergeometric_iff_ratio⟩

/-- CO-483. Polynomial and rational sequences: every polynomial sequence is rational, and
every nonzero rational sequence is a unit of `S(K)` (and a hypergeometric term). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
theorem def_8_2_1_rational_sequences {K : Type*} [Field K] [CharZero K] :
    (∀ a : ℕ → K, SeqRing.IsPolynomialSeq a → SeqRing.IsRationalSeq a) ∧
    (∀ a : ℕ → K, SeqRing.IsRationalSeq a → (a : SeqRing K) ≠ 0 → IsUnit (a : SeqRing K)) ∧
    (∀ a : ℕ → K, SeqRing.IsRationalSeq a → (a : SeqRing K) ≠ 0 → IsHypergeometric a) :=
  ⟨fun _ h => h.isRationalSeq, fun _ h h0 => h.isUnit h0, fun _ h h0 => h.isHypergeometric h0⟩

/-- CO-484. Proposition 8.2.1: if `N y = a y` in `S(K)` with `y ≠ 0`, then `y` and `a` are
both units. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.2.1, p. 158"]
theorem prop_8_2_1_shift_eq_unit {K : Type*} [Field K] [CharZero K] {y a : SeqRing K}
    (hy : y ≠ 0) (h : SeqRing.shift y = a * y) : IsUnit y ∧ IsUnit a :=
  SeqRing.isUnit_of_shift_eq hy h

/-- CO-485. Corollary 8.2.1: every hypergeometric sequence is a unit in `S(K)`. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 8.2.1, p. 158"]
theorem cor_8_2_1_hypergeometric_unit {K : Type*} [Field K] [CharZero K] {t : ℕ → K}
    (ht : IsHypergeometric t) : IsUnit (t : SeqRing K) :=
  SeqRing.IsHypergeometric.isUnit ht

/-- CO-486. Proposition 8.3.1: for `L = ∑ p_i N^i` with `q_j = ∑_i C(i,j) p_i` and
`b = max (deg q_j - j)`, a polynomial solution `y ≠ 0` of `L y = f` has degree at most
`max (deg f - b, -b - 1, d₁)`, where `d₁` bounds the nonnegative integer roots of the degree
polynomial. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.3.1, p. 160"]
theorem prop_8_3_1_polynomial_degree_bound {K : Type*} [Field K] [CharZero K]
    (p : ℕ → Polynomial K) (r : ℕ) (y f : Polynomial K) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (hbe : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b)
    (d₁ : ℕ) (hd₁ : ∀ x : ℕ, Polynomial.eval (x : K) (degreePoly p r b) = 0 → x ≤ d₁)
    (hf : f ≠ 0) (hy : applyOp p r y = f) :
    y = 0 ∨ (y.natDegree : ℤ) ≤ max (max ((f.natDegree : ℤ) - b) (-b - 1)) (d₁ : ℤ) :=
  natDegree_le_book_bound p r y f b hb hbe d₁ hd₁ hf hy

/-- CO-487. Algorithm Poly (completeness): there is a bound `d` such that all polynomial
solutions of `L y = f` lie in the space of polynomials of degree `≤ d`, so they are found by
undetermined coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Poly), p. 160"]
theorem text_p160_algorithm_poly {K : Type*} [Field K] [CharZero K]
    (p : ℕ → Polynomial K) (r : ℕ) (f : Polynomial K) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (hbe : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b) :
    ∃ d : ℕ, ∀ y : Polynomial K, applyOp p r y = f →
      ∃ hy : y ∈ Polynomial.degreeLT K (d + 1), (polyMap p r (d + 1)) ⟨y, hy⟩ = f :=
  poly_complete p r f b hb hbe

/-- CO-488. Algorithm Hyper: a hypergeometric solution of an order-`d` recurrence exists iff
a candidate `(a, b, z, c)` exists, and there are only finitely many candidate triples
`(a, b, z)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Hyper), p. 162"]
theorem text_p162_algorithm_hyper {K : Type*} [Field K] [CharZero K] (p : ℕ → Polynomial K)
    (d : ℕ) (hd : 0 < d) (h0 : p 0 ≠ 0) (hdn : p d ≠ 0) :
    ((∃ y : ℕ → K, IsHypergeometric y ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ∑ i ∈ Finset.range (d + 1), Polynomial.eval (n : K) (p i) * y (n + i) = 0) ↔
      ∃ (a b : Polynomial K) (z : K) (c : Polynomial K), IsHyperCandidate p d a b z c) ∧
    {t : Polynomial K × Polynomial K × K |
      ∃ c : Polynomial K, IsHyperCandidate p d t.1 t.2.1 t.2.2 c}.Finite :=
  ⟨hyper_exists_iff p d hd h0 hdn, hyper_candidates_finite p d h0 hdn⟩

/-- CO-489. Theorem 8.4.1: if `y ≠ 0` solves the recurrence and has ratio
`z a c(n+1)/(b c(n))` in canonical form, then `∑ α_i z^i = 0`, `a ∣ p₀`,
`b ∣ p_d(n-d+1)`, and `c` solves the auxiliary recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.4.1, p. 162"]
theorem thm_8_4_1_hyper_necessary {K : Type*} [Field K] [CharZero K] (p : ℕ → Polynomial K)
    (d : ℕ) (hd : 0 < d) (h0 : p 0 ≠ 0) (hdn : p d ≠ 0) (y : ℕ → K)
    (hy : ¬∀ᶠ n : ℕ in Filter.atTop, y n = 0)
    (hrec : ∀ᶠ n : ℕ in Filter.atTop,
      ∑ i ∈ Finset.range (d + 1), Polynomial.eval (n : K) (p i) * y (n + i) = 0)
    (z : K) (hz : z ≠ 0) (a b c : Polynomial K) (hbm : b.Monic) (hcm : c.Monic)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (Polynomial.X + Polynomial.C (h : K))))
    (hac : IsCoprime a c) (hbc : IsCoprime b (c.comp (Polynomial.X + 1)))
    (hratio : ∀ᶠ n : ℕ in Filter.atTop, y (n + 1) = hyperRatio z a b c n * y n) :
    ∑ i ∈ Finset.range (d + 1), hyperAlpha p a b d i * z ^ i = 0 ∧ a ∣ p 0 ∧
      b ∣ (p d).comp (Polynomial.X + Polynomial.C (1 - (d : K))) ∧ AuxRecurrence p a b c z d :=
  hyper_necessary p d hd h0 hdn y hy hrec z hz a b c hbm hcm hab hac hbc hratio

/-- CO-490. Hyper is sound and complete: every candidate yields a hypergeometric solution
with the stated ratio, and every hypergeometric solution arises from a candidate. -/
@[kb "petkovsekwilfzeilberger1996" "text (second-order derivation), p. 162"]
theorem text_p162_hyper_sound_complete {K : Type*} [Field K] [CharZero K] (p : ℕ → Polynomial K)
    (d : ℕ) :
    (∀ (a b : Polynomial K) (z : K) (c : Polynomial K), IsHyperCandidate p d a b z c →
      ∃ y : ℕ → K, IsHypergeometric y ∧
        (∀ᶠ n : ℕ in Filter.atTop, y (n + 1) = hyperRatio z a b c n * y n) ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∑ i ∈ Finset.range (d + 1), Polynomial.eval (n : K) (p i) * y (n + i) = 0) ∧
    (0 < d → p 0 ≠ 0 → p d ≠ 0 → ∀ y : ℕ → K, IsHypergeometric y →
      (∀ᶠ n : ℕ in Filter.atTop,
        ∑ i ∈ Finset.range (d + 1), Polynomial.eval (n : K) (p i) * y (n + i) = 0) →
      ∃ (a b : Polynomial K) (z : K) (c : Polynomial K), IsHyperCandidate p d a b z c ∧
        ∀ᶠ n : ℕ in Filter.atTop, y (n + 1) = hyperRatio z a b c n * y n) :=
  ⟨fun a b z c h => hyper_candidate_sound p d a b z c h,
    fun hd h0 hdn y hy hrec => hyper_candidate_complete p d hd h0 hdn y hy hrec⟩

/-- CO-491. Conversely, any `z, a, b, c` with `c` solving the auxiliary recurrence give a
ratio whose solutions satisfy the original recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 163"]
theorem text_p163_hyper_sound {K : Type*} [Field K] [CharZero K] (p : ℕ → Polynomial K)
    (d : ℕ) (z : K) (a b c : Polynomial K) (hb : b ≠ 0) (hc : c ≠ 0)
    (haux : AuxRecurrence p a b c z d) (y : ℕ → K)
    (hy : ∀ᶠ n : ℕ in Filter.atTop, y (n + 1) = hyperRatio z a b c n * y n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∑ i ∈ Finset.range (d + 1), Polynomial.eval (n : K) (p i) * y (n + i) = 0 :=
  hyper_sound p d z a b c hb hc haux y hy

/-- CO-493 (partial). The sums `∑_k C(n,k) C(n+k,k)` (Delannoy numbers) and the Apéry sums
satisfy second-order recurrences with polynomial coefficients (the non-existence of hypergeometric
solutions is not formalised here). -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 8.4.2, p. 164"]
theorem ex_8_4_2_delannoy_apery_recurrences :
    (∀ n : ℕ, (n + 2) * Companions.delannoySum (n + 2) + (n + 1) * Companions.delannoySum n =
      3 * (2 * n + 3) * Companions.delannoySum (n + 1)) ∧
    (∀ n : ℕ, (n + 2) ^ 3 * Companions.aperySum (n + 2) + (n + 1) ^ 3 * Companions.aperySum n =
      (2 * n + 3) * (17 * n ^ 2 + 51 * n + 39) * Companions.aperySum (n + 1)) :=
  ⟨Companions.delannoySum_rec, Companions.aperySum_rec⟩

/-- CO-494. The involution numbers satisfy `y(n+2) = y(n+1) + (n+1) y(n)`, and no hypergeometric
sequence satisfies this recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 8.4.3, p. 165"]
theorem ex_8_4_3_involutions_not_hypergeometric {K : Type*} [Field K] [CharZero K] :
    (∀ n : ℕ, Involutions.involutionNumber (n + 2) =
      Involutions.involutionNumber (n + 1) + (n + 1) * Involutions.involutionNumber n) ∧
    (∀ y : ℕ → K, IsHypergeometric y →
      ¬∀ᶠ n : ℕ in Filter.atTop, y (n + 2) = y (n + 1) + ((n : K) + 1) * y n) :=
  ⟨Involutions.involutionNumber_rec, fun y hy => not_hypergeometric_involution_rec y hy⟩

/-- CO-496 (partial). A d'Alembertian sequence is annihilated by a chain of first-order
operators: a product of first-order recurrence operators with rational coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem text_p167_dalembertian_first_order_product {K : Type*} [Field K] [CharZero K]
    {a : ℕ → K} (h : IsDAlembertian a) :
    ∃ ps : List (Polynomial K × Polynomial K), (∀ pq ∈ ps, pq.1 ≠ 0) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (ps.map (fun pq : Polynomial K × Polynomial K => RecOp.firstOrder pq.1 pq.2)).prod.act a n = 0 :=
  h.exists_firstOrder_product

/-- CO-497 (partial). Reduction of order: if `L = L₁ M` and `L y = 0` eventually, then
`L₁ (M y) = 0`; and for a hypergeometric `h` and `L = L₁ (q N - p)`, `L (h s)` is `L₁` applied to the
first difference of `s` scaled by `q h(m+1)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem text_p167_reduction_of_order {K : Type*} [Field K] [CharZero K] :
    (∀ (L L₁ M : RecOp K), L = L₁ * M → ∀ y : ℕ → K, (∀ᶠ n : ℕ in Filter.atTop, L.act y n = 0) →
      ∀ᶠ n : ℕ in Filter.atTop, L₁.act (M.act y) n = 0) ∧
    (∀ (L L₁ : RecOp K) (p q : Polynomial K), L = L₁ * RecOp.firstOrder q (-p) →
      ∀ h : ℕ → K, (∀ᶠ n : ℕ in Filter.atTop,
        Polynomial.eval (n : K) q * h (n + 1) = Polynomial.eval (n : K) p * h n) →
      ∀ s : ℕ → K, ∀ᶠ n : ℕ in Filter.atTop,
        L.act (fun m : ℕ => h m * s m) n =
          L₁.act (fun m : ℕ => Polynomial.eval (m : K) q * h (m + 1) * (s (m + 1) - s m)) n) :=
  ⟨fun L L₁ M hL y hy => RecOp.reduction_of_order L L₁ M hL y hy,
    fun L L₁ p q hL h hh s => RecOp.act_hyper_mul L L₁ p q hL h hh s⟩

/-- CO-498. Proposition 8.7.1: if `h` is hypergeometric and `L h` is not eventually zero, then
`L h` is hypergeometric and similar to `h`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.7.1, p. 168"]
theorem prop_8_7_1_operator_image_similar {K : Type*} [Field K] [CharZero K] (L : RecOp K)
    {h : ℕ → K} (hh : IsHypergeometric h) (hne : ¬∀ᶠ n : ℕ in Filter.atTop, L.act h n = 0) :
    IsHypergeometric (L.act h) ∧ IsSimilar (L.act h) h :=
  RecOp.isHypergeometric_act L hh hne

/-- CO-499. Theorem 8.7.1: if `L` kills a sum of pairwise dissimilar hypergeometric terms,
then `L` kills each term. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.7.1, p. 169"]
theorem thm_8_7_1_dissimilar_terms_killed_separately {K : Type*} [Field K] [CharZero K]
    {ι : Type*} [DecidableEq ι] (L : RecOp K) (s : Finset ι) (h : ι → ℕ → K)
    (hh : ∀ i ∈ s, IsHypergeometric (h i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬IsSimilar (h i) (h j))
    (hL : ∀ᶠ n : ℕ in Filter.atTop, L.act (fun m : ℕ => ∑ i ∈ s, h i m) n = 0) :
    ∀ i ∈ s, ∀ᶠ n : ℕ in Filter.atTop, L.act (h i) n = 0 :=
  RecOp.act_eq_zero_of_sum_dissimilar L s h hh hd hL

/-- CO-500. Corollary 8.7.1: the solutions of `L y = 0` lying in the linear hull of
hypergeometric terms are spanned by a linearly independent family of hypergeometric terms that
solve `L y = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 8.7.1, p. 169"]
theorem cor_8_7_1_hypergeometric_basis {K : Type u} [Field K] [CharZero K] (L : RecOp K) :
    ∃ (ι : Type u) (b : ι → ℕ → K), (∀ i, IsHypergeometric (b i)) ∧
      (∀ i, ∀ᶠ n : ℕ in Filter.atTop, L.act (b i) n = 0) ∧
      (LinearIndependent K fun i => (b i : SeqRing K)) ∧
      ∀ g ∈ hyperHull K, (∃ f : ℕ → K, (f : SeqRing K) = g ∧ ∀ᶠ n : ℕ in Filter.atTop, L.act f n = 0) →
        g ∈ Submodule.span K (Set.range fun i => (b i : SeqRing K)) := by
  obtain ⟨ι, b, h1, h2, h3, h4⟩ := kernel_inter_hull_basis L
  exact ⟨ι, b, h1, h2, h3, h4⟩

/-- CO-026. The number of derangements of `n ≥ 1` objects is the integer nearest to `n!/e`:
the distance is less than `1/2`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 169"]
theorem text_p169_derangements_nearest_integer (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / Real.exp 1| < 1 / 2 :=
  abs_numDerangements_sub_factorial_div_e_lt n hn

/-- CO-503. Proposition 8.9.1: a representation of a sequence as a sum of pairwise dissimilar
hypergeometric terms is unique up to order (and eventual equality of terms). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.9.1, p. 171"]
theorem prop_8_9_1_dissimilar_representation_unique {K : Type*} [Field K] [CharZero K]
    {k m : ℕ} (a : Fin k → ℕ → K) (b : Fin m → ℕ → K)
    (ha : ∀ i, IsHypergeometric (a i)) (hb : ∀ j, IsHypergeometric (b j))
    (hda : ∀ i i', i ≠ i' → ¬IsSimilar (a i) (a i'))
    (hdb : ∀ j j', j ≠ j' → ¬IsSimilar (b j) (b j'))
    (hab : ∀ᶠ n : ℕ in Filter.atTop, ∑ i, a i n = ∑ j, b j n) :
    k = m ∧ ∃ σ : Fin k ≃ Fin m, ∀ i, ∀ᶠ n : ℕ in Filter.atTop, a i n = b (σ i) n :=
  dissimilar_repr_unique_fin a b ha hb hda hdb hab

/-- CO-504 (partial). Solving `L y = f` over the hypergeometric hull: writing `y = r f₀` for a
hypergeometric `f₀` with ratio `s`, `L (r f₀) = 1 · f₀` iff the conjugated operator is `1`; and
particular solutions of the pieces add up, together with any kernel element. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 171"]
theorem text_p171_solve_over_hull {K : Type*} [Field K] [CharZero K] (L : RecOp K) :
    (∀ {f s : ℕ → K}, (∀ᶠ n : ℕ in Filter.atTop, f (n + 1) = s n * f n) →
      (∀ᶠ n : ℕ in Filter.atTop, f n ≠ 0) → ∀ r : ℕ → K,
      ((∀ᶠ n : ℕ in Filter.atTop, L.act (fun m : ℕ => r m * f m) n = f n) ↔
        ∀ᶠ n : ℕ in Filter.atTop, L.conjOp s r n = 1)) ∧
    (∀ {ι : Type _} (s : Finset ι) (a f : ι → ℕ → K),
      (∀ j ∈ s, ∀ᶠ n : ℕ in Filter.atTop, L.act (a j) n = f j n) →
      ∀ k : ℕ → K, (∀ᶠ n : ℕ in Filter.atTop, L.act k n = 0) →
      ∀ᶠ n : ℕ in Filter.atTop, L.act (fun m : ℕ => ∑ j ∈ s, a j m + k m) n = ∑ j ∈ s, f j n) :=
  ⟨fun hf hne r => RecOp.act_mul_eq_self_iff L hf hne r,
    fun s a f h k hk => RecOp.act_sum_particular L s a f h k hk⟩

/-- CO-505. Recurrence operators multiply by the commutation rule `N p(n) = p(n+1) N`, i.e.
`(a N^r)(b N^s) = a(n) b(n+r) N^{r+s}`; composition of operators acts as composition of the
maps. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem text_p172_operator_multiplication {K : Type*} [Field K] :
    (∀ (r s : ℕ) (a b : Polynomial K),
      RecOp.term r a * RecOp.term s b = RecOp.term (r + s) (a * b.comp (Polynomial.X + Polynomial.C (r : K)))) ∧
    (∀ p : Polynomial K, RecOp.N * SkewPolynomial.C p = SkewPolynomial.C (p.comp (Polynomial.X + 1)) * RecOp.N) ∧
    (∀ (L M : RecOp K) (y : ℕ → K), (L * M).act y = L.act (M.act y)) :=
  ⟨fun r s a b => RecOp.term_mul_term r s a b, fun p => RecOp.N_mul_C p,
    fun L M y => RecOp.act_mul L M y⟩

/-- CO-506. Right division with remainder: for recurrence operators with rational coefficients
and `L₂ ≠ 0`, there are `Q, R` with `L₁ = Q L₂ + R` and `ord R < ord L₂`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem text_p172_right_division {K : Type*} [Field K] [CharZero K]
    (L₁ L₂ : SkewPolynomial (RatFunc K)) (h : L₂ ≠ 0) :
    ∃ Q R : SkewPolynomial (RatFunc K), L₁ = Q * L₂ + R ∧ ∀ k ∈ R.support, k < skewOrder L₂ :=
  ratfunc_right_division K L₁ L₂ h

/-- CO-507 (partial). Right-Euclidean algorithm: any two recurrence operators with rational
coefficients have a greatest common right divisor `G`, which is a combination `A L₁ + B L₂`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem text_p172_gcrd {K : Type*} [Field K] [CharZero K] (L₁ L₂ : SkewPolynomial (RatFunc K)) :
    ∃ G A B : SkewPolynomial (RatFunc K), (∃ Q, L₁ = Q * G) ∧ (∃ Q, L₂ = Q * G) ∧
      G = A * L₁ + B * L₂ :=
  ratfunc_gcrd L₁ L₂

/-- CO-508. The minimal-order annihilating operator `M` of an element `v` right-divides every
annihilating operator of `v`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem text_p173_minimal_annihilator_divides {F : Type*} [Field F]
    [MulSemiringAction (Multiplicative ℕ) F] {V : Type*} [AddCommGroup V]
    [Module (SkewPolynomial F) V] (v : V) (M : SkewPolynomial F) (hM : M ≠ 0) (hv : M • v = 0)
    (hmin : ∀ L : SkewPolynomial F, L ≠ 0 → L • v = 0 → skewOrder M ≤ skewOrder L)
    (L : SkewPolynomial F) (hL : L • v = 0) : ∃ Q : SkewPolynomial F, L = Q * M :=
  Identities3c.minimal_annihilator_dvd v M hM hv hmin L hL

/-- CO-509 (partial). If `L = L₁ (q N - p)` then every sequence with `q(n) y(n+1) = p(n) y(n)`
is a solution of `L y = 0`; so a first-order right factor gives a hypergeometric solution. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem text_p173_solution_of_right_factor {K : Type*} [Field K] [CharZero K]
    (L L₁ : RecOp K) (p q : Polynomial K) (hL : L = L₁ * RecOp.firstOrder q (-p))
    (y : ℕ → K) (hy : ∀ᶠ n : ℕ in Filter.atTop,
      Polynomial.eval (n : K) q * y (n + 1) = Polynomial.eval (n : K) p * y n) :
    ∀ᶠ n : ℕ in Filter.atTop, L.act y n = 0 :=
  RecOp.solution_of_right_factor L L₁ p q hL y hy

/-- CO-510. The adjoint of `L = ∑ p_k(n) N^k` of order `d` is `L* = ∑ p_{d-k}(n+k) N^k`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (adjoint operator), p. 173"]
theorem def_p173_adjoint_operator {K : Type*} [Field K] (d : ℕ) (L : RecOp K) :
    RecOp.adjoint d L =
      ∑ k ∈ Finset.range (d + 1), RecOp.term k ((L.coeff (d - k)).comp (Polynomial.X + Polynomial.C (k : K))) :=
  rfl

/-- CO-511 (partial). For an operator of order at most `d`, `L** N^d = N^d L`
(that is, `L** = N^d L N^{-d}`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem text_p173_adjoint_adjoint {K : Type*} [Field K] [CharZero K] (d : ℕ) (L : RecOp K)
    (hL : ∀ k ∈ SkewPolynomial.support L, k ≤ d) :
    RecOp.adjoint d (RecOp.adjoint d L) * RecOp.N ^ d = RecOp.N ^ d * L :=
  RecOp.adjoint_adjoint_mul d L hL

end UndergradKB.Combinatorics.Course.AeqB.Ch08b
