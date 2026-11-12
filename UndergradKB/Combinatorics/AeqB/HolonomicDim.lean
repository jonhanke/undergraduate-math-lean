import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finsupp.Fintype
import UndergradKB.Common.Attr

/-!
# Discrete holonomic functions by dimension growth (Petkovsek–Wilf–Zeilberger, "A = B", p. 193)

A function `F` of `r` integer variables with values in a field is called holonomic here when the
space of functions spanned by the translates `x^α F(x + β)` with total degree `|α| + |β| ≤ m` grows
at most like a constant times `(m + 1)^r`.  This is the standard precise form of the statement that
`F` satisfies as many independent recurrences with polynomial coefficients as possible.

We prove:

* the constant function `1` is holonomic (so the notion is not vacuous);
* a holonomic function satisfies, in each single variable, a non-trivial recurrence with polynomial
  coefficients (a counting argument: more operators than the dimension allows);
* if `F(x, k)` is holonomic and, for each `x`, vanishes for all but finitely many `k`, then the sum
  `G(x) = ∑_k F(x, k)` satisfies a non-trivial recurrence with polynomial coefficients in each
  variable `x_i`.  This is the consequence of holonomy that is used for sums.  It is not the full
  statement that `G` is holonomic, which would need the theory of Bernstein's inequality.
-/

noncomputable section

namespace UndergradKB.Combinatorics.AeqB.HolonomicDim

open Finset

variable {K : Type*} [Field K] {r : ℕ}

/-- Multiplication by the monomial `x^α` after the shift `x ↦ x + β`. -/
def monoShift (α β : Fin r → ℕ) (F : (Fin r → ℤ) → K) : (Fin r → ℤ) → K :=
  fun x => (∏ i, (x i : K) ^ α i) * F (fun i => x i + β i)

/-- The span of all `x^α F(x + β)` with `|α| + |β| ≤ m`. -/
def bernsteinSpan (F : (Fin r → ℤ) → K) (m : ℕ) : Submodule K ((Fin r → ℤ) → K) :=
  Submodule.span K {G | ∃ α β : Fin r → ℕ, ∑ i, α i + ∑ i, β i ≤ m ∧ G = monoShift α β F}

lemma monoShift_mem_bernsteinSpan (F : (Fin r → ℤ) → K) (m : ℕ) (α β : Fin r → ℕ)
    (h : ∑ i, α i + ∑ i, β i ≤ m) : monoShift α β F ∈ bernsteinSpan F m :=
  Submodule.subset_span ⟨α, β, h, rfl⟩

lemma bernsteinSpan_finite (F : (Fin r → ℤ) → K) (m : ℕ) :
    Module.Finite K (bernsteinSpan F m) := by
  have hfin : {G : (Fin r → ℤ) → K | ∃ α β : Fin r → ℕ, ∑ i, α i + ∑ i, β i ≤ m ∧
      G = monoShift α β F}.Finite := by
    refine (Set.finite_range
      (fun p : (Fin r → Fin (m + 1)) × (Fin r → Fin (m + 1)) =>
        monoShift (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) F)).subset ?_
    rintro G ⟨α, β, h, rfl⟩
    have hα : ∀ i, α i < m + 1 := fun i =>
      Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (α j))
        (Finset.mem_univ i)).trans (le_trans (Nat.le_add_right _ _) h))
    have hβ : ∀ i, β i < m + 1 := fun i =>
      Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (β j))
        (Finset.mem_univ i)).trans (le_trans (Nat.le_add_left _ _) h))
    exact ⟨(fun i => ⟨α i, hα i⟩, fun i => ⟨β i, hβ i⟩), rfl⟩
  exact FiniteDimensional.span_of_finite K hfin

/-- CO-516. A function of `r` integer variables is holonomic when the space of functions
`x^α F(x + β)` with `|α| + |β| ≤ m` has dimension at most `C (m+1)^r` for some constant `C`
(Bernstein dimension at most `r`).  This is the precise form of "satisfies as many independent
recurrences with polynomial coefficients as possible", and it forces a recurrence in each variable
(see `exists_recurrence`). -/
@[kb "petkovsekwilfzeilberger1996" "def p.193 (discrete holonomic function)"]
def IsHolonomic (F : (Fin r → ℤ) → K) : Prop :=
  ∃ C : ℕ, ∀ m : ℕ, Module.finrank K (bernsteinSpan F m) ≤ C * (m + 1) ^ r

lemma coord_lt {α β : Fin r → ℕ} {m : ℕ} (h : ∑ i, α i + ∑ i, β i ≤ m) (i : Fin r) :
    α i < m + 1 :=
  Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ => Nat.zero_le (α j))
    (Finset.mem_univ i)).trans (le_trans (Nat.le_add_right _ _) h))

/-- Sanity check: the constant function `1` is holonomic. -/
theorem isHolonomic_one : IsHolonomic (fun _ : Fin r → ℤ => (1 : K)) := by
  refine ⟨1, fun m => ?_⟩
  let mon : (Fin r → Fin (m + 1)) → ((Fin r → ℤ) → K) :=
    fun a x => ∏ i, (x i : K) ^ (a i : ℕ)
  have hle : bernsteinSpan (fun _ : Fin r → ℤ => (1 : K)) m ≤ Submodule.span K (Set.range mon) := by
    apply Submodule.span_le.2
    rintro G ⟨α, β, h, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun i => ⟨α i, coord_lt h i⟩, ?_⟩
    funext x
    simp [mon, monoShift]
  have : Module.Finite K (Submodule.span K (Set.range mon)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range mon)
  calc Module.finrank K (bernsteinSpan (fun _ : Fin r → ℤ => (1 : K)) m)
      ≤ Module.finrank K (Submodule.span K (Set.range mon)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin r → Fin (m + 1)) := finrank_range_le_card mon
    _ = 1 * (m + 1) ^ r := by simp

/-- Counting: if more vectors than the dimension bound lie in the Bernstein span, they are
linearly dependent. -/
lemma exists_dep {s : ℕ} (F : (Fin s → ℤ) → K) (C : ℕ)
    (hC : ∀ m, Module.finrank K (bernsteinSpan F m) ≤ C * (m + 1) ^ s)
    {ι : Type*} [Fintype ι] (v : ι → ((Fin s → ℤ) → K)) (m : ℕ)
    (hv : ∀ a, v a ∈ bernsteinSpan F m) (hcard : C * (m + 1) ^ s < Fintype.card ι) :
    ∃ c : ι → K, c ≠ 0 ∧ ∑ a, c a • v a = 0 := by
  by_cases hli : LinearIndependent K v
  · exfalso
    let w : ι → bernsteinSpan F m := fun a => ⟨v a, hv a⟩
    have hw : LinearIndependent K w :=
      LinearIndependent.of_comp (bernsteinSpan F m).subtype hli
    have := bernsteinSpan_finite F m
    have h1 := LinearIndependent.fintype_card_le_finrank hw
    have h2 := hC m
    omega
  · obtain ⟨g, hg, a, ha⟩ := Fintype.not_linearIndependent_iff.1 hli
    exact ⟨g, fun h => ha (by simp [h]), hg⟩

lemma arith (C s q m t : ℕ) (ht : t = C * q ^ s) (hm : m + 1 ≤ q * (t + 1)) :
    C * (m + 1) ^ s < (t + 1) ^ (s + 1) := by
  have hpos : 0 < (t + 1) ^ s := by positivity
  calc C * (m + 1) ^ s ≤ C * (q * (t + 1)) ^ s := by gcongr
    _ = C * q ^ s * (t + 1) ^ s := by rw [mul_pow]; ring
    _ = t * (t + 1) ^ s := by rw [ht]
    _ < (t + 1) * (t + 1) ^ s := by nlinarith
    _ = (t + 1) ^ (s + 1) := by ring

/-- The exponent vector of a monomial given by a function. -/
def expo {t : ℕ} (α : Fin r → Fin (t + 1)) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => (α l : ℕ)

lemma expo_inj {t : ℕ} {α β : Fin r → Fin (t + 1)} (h : expo α = expo β) : α = β := by
  funext l
  have := DFunLike.congr_fun h l
  simp [expo] at this
  exact Fin.ext this

/-- The polynomial `∑_α v(α,j) x^α`. -/
def polyOf {t : ℕ} (v : (Fin r → Fin (t + 1)) × Fin (t + 1) → K) (j : Fin (t + 1)) :
    MvPolynomial (Fin r) K :=
  ∑ α : Fin r → Fin (t + 1), MvPolynomial.monomial (expo α) (v (α, j))

lemma eval_polyOf {t : ℕ} (v : (Fin r → Fin (t + 1)) × Fin (t + 1) → K) (j : Fin (t + 1))
    (x : Fin r → ℤ) :
    MvPolynomial.eval (fun l => (x l : K)) (polyOf v j) =
      ∑ α : Fin r → Fin (t + 1), v (α, j) * ∏ l, (x l : K) ^ (α l : ℕ) := by
  rw [polyOf, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [expo]

lemma polyOf_ne {t : ℕ} (v : (Fin r → Fin (t + 1)) × Fin (t + 1) → K) (hv : v ≠ 0) :
    ∃ j, polyOf v j ≠ 0 := by
  classical
  obtain ⟨⟨α, j⟩, h⟩ : ∃ a, v a ≠ 0 := by
    by_contra hh
    exact hv (funext fun a => by_contra fun h => hh ⟨a, h⟩)
  refine ⟨j, fun h0 => h ?_⟩
  have h1 : (polyOf v j).coeff (expo α) = v (α, j) := by
    rw [polyOf, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      have : expo β ≠ expo α := fun e => hβ (expo_inj e)
      simp [this]
    · simp
  rw [h0] at h1
  simpa using h1.symm

lemma assemble {t : ℕ} (v : (Fin r → Fin (t + 1)) × Fin (t + 1) → K) (hv : v ≠ 0)
    (g : (Fin r → ℤ) → Fin (t + 1) → K)
    (h : ∀ x, ∑ a, v a * ((∏ l, (x l : K) ^ (a.1 l : ℕ)) * g x a.2) = 0) :
    ∃ p : Fin (t + 1) → MvPolynomial (Fin r) K, (∃ j, p j ≠ 0) ∧
      ∀ x : Fin r → ℤ, ∑ j, MvPolynomial.eval (fun l => (x l : K)) (p j) * g x j = 0 := by
  refine ⟨polyOf v, polyOf_ne v hv, fun x => ?_⟩
  rw [← h x, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_polyOf, Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

lemma shift_single (x : Fin r → ℤ) (i : Fin r) (j : ℕ) :
    (fun l => x l + ((Pi.single i j : Fin r → ℕ) l : ℤ)) = Function.update x i (x i + j) := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [h]

/-- CO-516. A holonomic function satisfies a nontrivial recurrence in each variable `i`: there
are polynomials `p_0, ..., p_J` in `r` variables, not all zero, such that
`∑_j p_j(x) F(x + j e_i) = 0` for all integer points `x`. -/
@[kb "petkovsekwilfzeilberger1996" "def p.193 (discrete holonomic function)"]
theorem exists_recurrence {F : (Fin r → ℤ) → K} (hF : IsHolonomic F) (i : Fin r) :
    ∃ (J : ℕ) (p : Fin (J + 1) → MvPolynomial (Fin r) K), (∃ j, p j ≠ 0) ∧
      ∀ x : Fin r → ℤ, ∑ j : Fin (J + 1),
        MvPolynomial.eval (fun l => (x l : K)) (p j) * F (Function.update x i (x i + (j : ℕ))) = 0 := by
  obtain ⟨C, hC⟩ := hF
  set t := C * (r + 1) ^ r with ht
  refine ⟨t, ?_⟩
  let v : (Fin r → Fin (t + 1)) × Fin (t + 1) → ((Fin r → ℤ) → K) :=
    fun a => monoShift (fun l => (a.1 l : ℕ)) (Pi.single i (a.2 : ℕ)) F
  have hv : ∀ a, v a ∈ bernsteinSpan F ((r + 1) * t) := by
    intro a
    apply monoShift_mem_bernsteinSpan
    have h1 : ∑ l, ((a.1 l : Fin (t + 1)) : ℕ) ≤ r * t := by
      calc ∑ l, ((a.1 l : Fin (t + 1)) : ℕ) ≤ ∑ _l : Fin r, t :=
            Finset.sum_le_sum fun l _ => Nat.lt_succ_iff.1 (a.1 l).2
        _ = r * t := by simp
    have h2 : ∑ l, (Pi.single i (a.2 : ℕ) : Fin r → ℕ) l ≤ t := by
      simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
      exact Nat.lt_succ_iff.1 a.2.2
    nlinarith
  have hcard : C * ((r + 1) * t + 1) ^ r < Fintype.card ((Fin r → Fin (t + 1)) × Fin (t + 1)) := by
    have := arith C r (r + 1) ((r + 1) * t) t ht (by nlinarith)
    simpa [Fintype.card_prod, Fintype.card_fun, pow_succ] using this
  obtain ⟨c, hc0, hc⟩ := exists_dep F C hC v _ hv hcard
  refine assemble c hc0 (fun x j => F (Function.update x i (x i + (j : ℕ)))) fun x => ?_
  have := congrFun hc x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [v, monoShift, shift_single]

/-! ### Sums over one variable -/

lemma finsum_sum_swap {ι : Type*} (s : Finset ι) (g : ι → ℤ → K)
    (hg : ∀ i, (Function.support (g i)).Finite) :
    ∑ᶠ k, ∑ i ∈ s, g i k = ∑ i ∈ s, ∑ᶠ k, g i k := by
  classical
  let S : Finset ℤ := s.biUnion fun i => (hg i).toFinset
  have hsub : ∀ i ∈ s, Function.support (g i) ⊆ ↑S := fun i hi k hk =>
    Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, hi, (hg i).mem_toFinset.2 hk⟩)
  have hS : Function.support (fun k => ∑ i ∈ s, g i k) ⊆ ↑S := by
    intro k hk
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hk)
    exact hsub i hi (Function.mem_support.2 hne)
  rw [finsum_eq_sum_of_support_subset _ hS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [finsum_eq_sum_of_support_subset _ (hsub i hi)]

lemma finite_support_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ → K)
    (hg : ∀ i, (Function.support (g i)).Finite) :
    (Function.support fun k => ∑ i ∈ s, g i k).Finite := by
  refine (Set.Finite.biUnion s.finite_toSet (fun i _ => hg i)).subset ?_
  intro k hk
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hk)
  exact Set.mem_biUnion hi (Function.mem_support.2 hne)

lemma finite_support_shift (f : ℤ → K) (hf : (Function.support f).Finite) (l : ℤ) (c : K) :
    (Function.support fun k => c * f (k + l)).Finite := by
  have : (Function.support fun k => f (k + l)).Finite :=
    hf.preimage (fun a _ b _ h => by simpa using h)
  exact this.subset fun k hk =>
    Function.mem_support.2 (right_ne_zero_of_mul (Function.mem_support.1 hk))

/-- Summation by parts for a finite sum with partial sums of the coefficients. -/
lemma sbp (c ψ : ℕ → K) (n : ℕ) :
    ∑ l ∈ range (n + 1), c l * ψ l =
      ∑ l ∈ range n, (-(∑ l' ∈ range (l + 1), c l')) * (ψ (l + 1) - ψ l) +
        (∑ l' ∈ range (n + 1), c l') * ψ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun l => c l * ψ l) (n + 1), ih,
      Finset.sum_range_succ (fun l => -(∑ l' ∈ range (l + 1), c l') * (ψ (l + 1) - ψ l)) n,
      Finset.sum_range_succ c (n + 1)]
    ring

/-- Descent on the order of a difference operator in the summation variable: a nonzero relation
`∑_l (∑_a c_l(a) φ_a) (k + l) = 0` valid for all `k`, between finitely supported functions,
yields a nonzero relation among the total sums `∑_k φ_a`. -/
lemma descent {A X : Type*} [Fintype A] (φ : A → X → ℤ → K)
    (hφ : ∀ a x, (Function.support (φ a x)).Finite) :
    ∀ (N : ℕ) (c : ℕ → A → K), (∀ l, N ≤ l → c l = 0) → (∃ l, c l ≠ 0) →
      (∀ x k, ∑ l ∈ range N, ∑ a, c l a * φ a x (k + l) = 0) →
      ∃ v : A → K, v ≠ 0 ∧ ∀ x, ∑ a, v a * ∑ᶠ k, φ a x k = 0 := by
  intro N
  induction N with
  | zero =>
    intro c hc hne _
    obtain ⟨l, hl⟩ := hne
    exact absurd (hc l (Nat.zero_le _)) hl
  | succ N ih =>
    intro c hc hne hrel
    have hg1 : ∀ x (l : ℕ), (Function.support fun k => ∑ a, c l a * φ a x (k + l)).Finite :=
      fun x l => finite_support_sum _ _ fun a => finite_support_shift _ (hφ a x) _ _
    by_cases hv : (fun a => ∑ l ∈ range (N + 1), c l a) = 0
    · obtain ⟨c', hc'⟩ : ∃ c' : ℕ → A → K, ∀ l a, c' l a = -∑ l' ∈ range (l + 1), c l' a :=
        ⟨_, fun _ _ => rfl⟩
      have hv0 : ∀ a, ∑ l ∈ range (N + 1), c l a = 0 := fun a => by
        simpa using congrFun hv a
      have h1 : ∀ l, N ≤ l → c' l = 0 := by
        intro l hl
        funext a
        have : ∑ l' ∈ range (N + 1), c l' a = ∑ l' ∈ range (l + 1), c l' a :=
          Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l' hl' hn => by
            have : c l' = 0 := hc l' (by simp at hl' hn; omega)
            simp [this]
        rw [hc', ← this, hv0 a]
        simp
      have h2 : ∃ l, c' l ≠ 0 := by
        by_contra hno
        have hno' : ∀ l, c' l = 0 := fun l => by_contra fun h => hno ⟨l, h⟩
        have hs : ∀ l a, ∑ l' ∈ range (l + 1), c l' a = 0 := fun l a => by
          have := congrFun (hno' l) a
          simpa [hc'] using this
        obtain ⟨l, hl⟩ := hne
        apply hl
        funext a
        have e := Finset.sum_range_succ (fun l' => c l' a) l
        rw [hs l a] at e
        have e0 : ∑ l' ∈ range l, c l' a = 0 := by
          cases l with
          | zero => simp
          | succ l => exact hs l a
        simpa [e0] using e.symm
      -- the key identity
      have hd : ∀ x k, ∑ l ∈ range N, ∑ a, c' l a * φ a x (k + ((l + 1 : ℕ) : ℤ)) =
          ∑ l ∈ range N, ∑ a, c' l a * φ a x (k + l) := by
        intro x k
        have key : ∀ a, ∑ l ∈ range (N + 1), c l a * φ a x (k + l) =
            ∑ l ∈ range N, c' l a * (φ a x (k + ((l + 1 : ℕ) : ℤ)) - φ a x (k + l)) := by
          intro a
          have := sbp (fun l => c l a) (fun l => φ a x (k + (l : ℤ))) N
          simp only [hv0 a, zero_mul, add_zero] at this
          rw [this]
          exact Finset.sum_congr rfl fun l _ => by rw [hc']
        have h0 := hrel x k
        rw [Finset.sum_comm] at h0
        have h3 : ∑ a, ∑ l ∈ range N, c' l a *
            (φ a x (k + ((l + 1 : ℕ) : ℤ)) - φ a x (k + l)) = 0 := by
          rw [← h0]
          exact Finset.sum_congr rfl fun a _ => (key a).symm
        simp only [mul_sub, Finset.sum_sub_distrib] at h3
        exact (Finset.sum_comm.trans (sub_eq_zero.1 h3)).trans Finset.sum_comm
      let w : X → ℤ → K := fun x k => ∑ l ∈ range N, ∑ a, c' l a * φ a x (k + l)
      have hd' : ∀ x k, w x (k + 1) = w x k := by
        intro x k
        show ∑ l ∈ range N, ∑ a, c' l a * φ a x (k + 1 + l) =
          ∑ l ∈ range N, ∑ a, c' l a * φ a x (k + l)
        rw [← hd x k]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
        rw [show k + 1 + (l : ℤ) = k + ((l + 1 : ℕ) : ℤ) by push_cast; ring]
      have hconst : ∀ x k, w x k = w x 0 := by
        intro x k
        induction k using Int.induction_on with
        | zero => rfl
        | succ i ih => exact (hd' x i).trans ih
        | pred i ih =>
          have := hd' x (-(i : ℤ) - 1)
          rw [show -(i : ℤ) - 1 + 1 = -i by ring] at this
          rw [← this]
          exact ih
      have hfinw : ∀ x, (Function.support (w x)).Finite := fun x =>
        finite_support_sum _ (fun l k => ∑ a, c' l a * φ a x (k + l)) fun l =>
          finite_support_sum _ _ fun a => finite_support_shift _ (hφ a x) _ _
      have hw0 : ∀ x k, w x k = 0 := by
        intro x k
        by_contra h0
        exact Set.infinite_univ (α := ℤ) ((hfinw x).subset fun k' _ => by
          rw [Function.mem_support, hconst x k']
          rwa [hconst x k] at h0)
      exact ih c' h1 h2 fun x k => hw0 x k
    · refine ⟨_, hv, fun x => ?_⟩
      have hz : ∑ᶠ k, ∑ l ∈ range (N + 1), ∑ a, c l a * φ a x (k + l) = 0 :=
        (finsum_congr (hrel x)).trans finsum_zero
      rw [finsum_sum_swap _ _ (hg1 x)] at hz
      have hl : ∀ l ∈ range (N + 1), ∑ᶠ k, ∑ a, c l a * φ a x (k + l) =
          ∑ a, c l a * ∑ᶠ k, φ a x k := by
        intro l _
        rw [finsum_sum_swap _ _ fun a => finite_support_shift _ (hφ a x) _ _]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← mul_finsum]
        congr 1
        exact finsum_comp_equiv (Equiv.addRight (l : ℤ)) (f := φ a x)
      rw [Finset.sum_congr rfl hl] at hz
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact hz

/-- The point `(x, k)` of `ℤ^(r+1)`, with `k` the last coordinate. -/
def pt (x : Fin r → ℤ) (k : ℤ) : Fin (r + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) x k

/-- The sum `G(x) = ∑_k F(x, k)` over the last variable (a finite sum when `F(x, ·)` has finite
support; the finite-sum convention `∑ᶠ` gives `0` otherwise). -/
def sumG (F : (Fin (r + 1) → ℤ) → K) (x : Fin r → ℤ) : K := ∑ᶠ k, F (pt x k)

lemma monoShift_pt (α : Fin r → ℕ) (j l : ℕ) (i : Fin r) (F : (Fin (r + 1) → ℤ) → K)
    (x : Fin r → ℤ) (k : ℤ) :
    monoShift (Fin.snoc (α := fun _ => ℕ) α 0) (Fin.snoc (α := fun _ => ℕ) (Pi.single i j) l) F
        (pt x k) =
      (∏ m, (x m : K) ^ α m) * F (pt (Function.update x i (x i + j)) (k + l)) := by
  have h : (fun m => pt x k m +
      ((Fin.snoc (α := fun _ => ℕ) (Pi.single i j : Fin r → ℕ) l m : ℕ) : ℤ)) =
      pt (Function.update x i (x i + j)) (k + l) := by
    funext m
    refine Fin.lastCases ?_ (fun m => ?_) m
    · simp [pt]
    · have := congrFun (shift_single x i j) m
      simp only [pt, Fin.snoc_castSucc] at this ⊢
      rw [← this]
  simp only [monoShift, Fin.prod_univ_castSucc, h]
  simp [pt]

/-- CO-518. If `F(x, k)` is holonomic and, for each `x`, vanishes for all but finitely many `k`,
then the sum `G(x) = ∑_k F(x, k)` satisfies, for each variable `x_i`, a nontrivial recurrence
`∑_j p_j(x) G(x + j e_i) = 0` with polynomial coefficients.  Modelling: the last coordinate of
`ℤ^(r+1)` is the summation variable `k`, and `sumG F x` is the (finite) sum over `k`.  This is the
consequence of holonomy that is used for sums (a recurrence in each remaining variable); it is not
the full statement that `G` is holonomic, which needs Bernstein's inequality. -/
@[kb "petkovsekwilfzeilberger1996" "text p.193-194"]
theorem sum_recurrence {F : (Fin (r + 1) → ℤ) → K} (hF : IsHolonomic F)
    (hfin : ∀ x : Fin r → ℤ, (Function.support fun k => F (pt x k)).Finite) (i : Fin r) :
    ∃ (J : ℕ) (p : Fin (J + 1) → MvPolynomial (Fin r) K), (∃ j, p j ≠ 0) ∧
      ∀ x : Fin r → ℤ, ∑ j : Fin (J + 1), MvPolynomial.eval (fun l => (x l : K)) (p j) *
        sumG F (Function.update x i (x i + (j : ℕ))) = 0 := by
  obtain ⟨C, hC⟩ := hF
  set t := C * (r + 2) ^ (r + 1) with ht
  refine ⟨t, ?_⟩
  let v : (Fin r → Fin (t + 1)) × Fin (t + 1) × Fin (t + 1) → ((Fin (r + 1) → ℤ) → K) :=
    fun a => monoShift (Fin.snoc (α := fun _ => ℕ) (fun l => (a.1 l : ℕ)) 0)
      (Fin.snoc (α := fun _ => ℕ) (Pi.single i (a.2.1 : ℕ)) (a.2.2 : ℕ)) F
  have hv : ∀ a, v a ∈ bernsteinSpan F ((r + 2) * t) := by
    intro a
    apply monoShift_mem_bernsteinSpan
    have h1 : ∑ l, ((a.1 l : Fin (t + 1)) : ℕ) ≤ r * t := by
      calc ∑ l, ((a.1 l : Fin (t + 1)) : ℕ) ≤ ∑ _l : Fin r, t :=
            Finset.sum_le_sum fun l _ => Nat.lt_succ_iff.1 (a.1 l).2
        _ = r * t := by simp
    have h2 : ∑ l, (Pi.single i (a.2.1 : ℕ) : Fin r → ℕ) l ≤ t := by
      simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true]
      exact Nat.lt_succ_iff.1 a.2.1.2
    have h3 : (a.2.2 : ℕ) ≤ t := Nat.lt_succ_iff.1 a.2.2.2
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_zero]
    nlinarith
  have hcard : C * ((r + 2) * t + 1) ^ (r + 1) <
      Fintype.card ((Fin r → Fin (t + 1)) × Fin (t + 1) × Fin (t + 1)) := by
    have := arith C (r + 1) (r + 2) ((r + 2) * t) t ht (by nlinarith)
    simpa [Fintype.card_prod, Fintype.card_fun, pow_succ, mul_assoc] using this
  obtain ⟨c, hc0, hc⟩ := exists_dep F C hC v _ hv hcard
  let φ : (Fin r → Fin (t + 1)) × Fin (t + 1) → (Fin r → ℤ) → ℤ → K :=
    fun a x k => (∏ m, (x m : K) ^ (a.1 m : ℕ)) *
      F (pt (Function.update x i (x i + (a.2 : ℕ))) k)
  have hφ : ∀ a x, (Function.support (φ a x)).Finite := fun a x =>
    (hfin _).subset fun k hk => Function.mem_support.2
      (right_ne_zero_of_mul (Function.mem_support.1 hk))
  let c' : ℕ → (Fin r → Fin (t + 1)) × Fin (t + 1) → K := fun l a =>
    if h : l < t + 1 then c (a.1, a.2, ⟨l, h⟩) else 0
  have hc'0 : ∀ l, t + 1 ≤ l → c' l = 0 := by
    intro l hl
    funext a
    have h : ¬ l ≤ t := by omega
    simp [c', h]
  have hne : ∃ l, c' l ≠ 0 := by
    obtain ⟨⟨α, j, l⟩, hl⟩ : ∃ a, c a ≠ 0 := by
      by_contra hh
      exact hc0 (funext fun a => by_contra fun h => hh ⟨a, h⟩)
    refine ⟨l, fun h => hl ?_⟩
    have := congrFun h (α, j)
    have h' : (l : ℕ) ≤ t := Nat.lt_succ_iff.1 l.2
    simpa [c', h'] using this
  have hrel : ∀ x k, ∑ l ∈ range (t + 1), ∑ a, c' l a * φ a x (k + l) = 0 := by
    intro x k
    have h0 := congrFun hc (pt x k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← h0]
    simp only [v, monoShift_pt]
    rw [Finset.sum_range (fun l => ∑ a, c' l a * φ a x (k + l))]
    simp only [c', φ, Fintype.sum_prod_type, Fin.is_lt, ↓reduceDIte, Fin.eta]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_comm
  obtain ⟨w, hw0, hw⟩ := descent φ hφ (t + 1) c' hc'0 hne hrel
  refine assemble w hw0 (fun x j => sumG F (Function.update x i (x i + (j : ℕ)))) fun x => ?_
  rw [← hw x]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [φ, sumG, mul_finsum]

end UndergradKB.Combinatorics.AeqB.HolonomicDim

