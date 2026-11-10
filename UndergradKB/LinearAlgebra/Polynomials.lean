import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Roots
import UndergradKB.Common.Attr

/-! # Polynomials (Axler, chapter 4; Hefferon, Five.I.1)

Division with remainder, real quadratics, and the factorization of a real polynomial into linear and
irreducible quadratic factors.
-/

open Polynomial

namespace UndergradKB.LinearAlgebra

section Division

variable {K : Type*} [Field K]

/-- Division algorithm over a field: for a nonzero divisor `s`, the pair `(q, r)` with
`p = s * q + r` and `deg r < deg s` exists and is unique. -/
@[kb "axler2024" "4.9, p. 142"]
theorem axler_4_9 (p s : K[X]) (hs : s ≠ 0) :
    ∃! qr : K[X] × K[X], p = s * qr.1 + qr.2 ∧ qr.2.degree < s.degree := by
  refine ⟨(p / s, p % s), ⟨(EuclideanDomain.div_add_mod p s).symm, degree_mod_lt p hs⟩, ?_⟩
  rintro ⟨q, r⟩ ⟨h1, h2⟩
  simp only at h1 h2
  have h3 : s * (q - p / s) = (p % s) - r := by
    have := EuclideanDomain.div_add_mod p s
    linear_combination (-1 : K[X]) * h1 - this
  have hq : q = p / s := by
    by_contra hne
    have hne' : q - p / s ≠ 0 := sub_ne_zero.mpr hne
    have h4 : s.degree ≤ (s * (q - p / s)).degree := by
      rw [degree_mul]
      have : (0 : WithBot ℕ) ≤ (q - p / s).degree := by
        rw [zero_le_degree_iff]; exact hne'
      calc s.degree = s.degree + 0 := by simp
        _ ≤ _ := by gcongr
    rw [h3] at h4
    have h5 : (p % s - r).degree < s.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_mod_lt p hs) h2)
    exact absurd h4 (not_le.mpr h5)
  subst hq
  have : r = p % s := by
    have := EuclideanDomain.div_add_mod p s
    have h6 : s * (p / s) + r = s * (p / s) + p % s := by rw [← h1, this]
    exact add_left_cancel h6
  rw [this]

end Division

section Real

/-- `x^2 + b x + c` over `ℝ` splits into two real linear factors exactly when `b^2 ≥ 4c`. -/
@[kb "axler2024" "4.15, p. 145"]
theorem axler_4_15 (b c : ℝ) :
    (∃ l₁ l₂ : ℝ, (X ^ 2 + C b * X + C c : ℝ[X]) = (X - C l₁) * (X - C l₂)) ↔ 4 * c ≤ b ^ 2 := by
  have key : ∀ l₁ l₂ : ℝ, ((X - C l₁) * (X - C l₂) : ℝ[X]) =
      X ^ 2 + C (-(l₁ + l₂)) * X + C (l₁ * l₂) := by
    intro l₁ l₂
    simp only [map_neg, map_add, map_mul]
    ring
  constructor
  · rintro ⟨l₁, l₂, h⟩
    rw [key] at h
    have h1 := congrArg (fun q => q.coeff 1) h
    have h0 := congrArg (fun q => q.coeff 0) h
    simp [coeff_X, coeff_C] at h1 h0
    rw [h0, h1]
    nlinarith [sq_nonneg (l₁ - l₂)]
  · intro h
    have hd : 0 ≤ b ^ 2 - 4 * c := by linarith
    set s := Real.sqrt (b ^ 2 - 4 * c) with hs
    have hs2 : s ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt hd
    refine ⟨(-b + s) / 2, (-b - s) / 2, ?_⟩
    rw [key]
    have e1 : -((-b + s) / 2 + (-b - s) / 2) = b := by ring
    have e2 : (-b + s) / 2 * ((-b - s) / 2) = c := by nlinarith
    rw [e1, e2]

/-- No real root of `x^2 + b x + c` iff `b^2 < 4c`. -/
lemma quad_no_root_iff (b c : ℝ) : (∀ x : ℝ, x ^ 2 + b * x + c ≠ 0) ↔ b ^ 2 < 4 * c := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hs2 : Real.sqrt (b ^ 2 - 4 * c) ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
    apply h ((-b + Real.sqrt (b ^ 2 - 4 * c)) / 2)
    nlinarith
  · intro h x hx
    nlinarith [sq_nonneg (2 * x + b)]

lemma quad_monic (b c : ℝ) : (X ^ 2 + C b * X + C c : ℝ[X]).Monic := by
  have : (X ^ 2 + C b * X + C c : ℝ[X]) = X ^ 2 + (C b * X + C c) := by ring
  rw [this]
  exact monic_X_pow_add (lt_of_le_of_lt degree_linear_le (by norm_num))

lemma quad_natDegree (b c : ℝ) : (X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := by
  compute_degree!

/-- The monic quadratic `x^2 + b x + c`, indexed by the pair `(b, c)`. -/
noncomputable def quadFactor (q : ℝ × ℝ) : ℝ[X] := X ^ 2 + C q.1 * X + C q.2

lemma quadFactor_injective : Function.Injective quadFactor := by
  rintro ⟨b, c⟩ ⟨b', c'⟩ h
  have h1 := congrArg (fun q => q.coeff 1) h
  have h0 := congrArg (fun q => q.coeff 0) h
  simp [quadFactor, coeff_X, coeff_C] at h1 h0
  simp [h1, h0]

/-- Real polynomials: constants and linear polynomials are irreducible over `ℝ` (in the sense that they
have no factorization into two polynomials of strictly smaller degree), a monic quadratic is
irreducible iff its discriminant `b^2 - 4c` is negative, and no polynomial of degree at least three is
irreducible. -/
@[kb "hefferon2020" "Five.I.1.6, p. 409"]
theorem hefferon_Five_I_1_6 :
    (∀ p : ℝ[X], p ≠ 0 → p.natDegree ≤ 1 →
      ¬ ∃ a b : ℝ[X], p = a * b ∧ a.natDegree < p.natDegree ∧ b.natDegree < p.natDegree) ∧
    (∀ p : ℝ[X], p.natDegree = 1 → Irreducible p) ∧
    (∀ b c : ℝ, Irreducible (X ^ 2 + C b * X + C c : ℝ[X]) ↔ b ^ 2 < 4 * c) ∧
    (∀ p : ℝ[X], 3 ≤ p.natDegree → ¬ Irreducible p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro p hp hd ⟨a, b, rfl, ha, hb⟩
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hp
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hp
    rw [natDegree_mul ha0 hb0] at ha hb hd
    omega
  · intro p hp
    exact irreducible_of_degree_eq_one (natDegree_eq_one.mp hp |> fun _ => by
      rw [degree_eq_natDegree (by rintro rfl; simp at hp), hp]; rfl)
  · intro b c
    rw [← quad_no_root_iff, (quad_monic b c).irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [quad_natDegree]) (by rw [quad_natDegree]; norm_num)]
    constructor
    · intro h x hx
      have : x ∈ (X ^ 2 + C b * X + C c : ℝ[X]).roots := by
        rw [mem_roots (quad_monic b c).ne_zero]
        simpa [IsRoot] using hx
      simp [h] at this
    · intro h
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx
      rw [mem_roots (quad_monic b c).ne_zero] at hx
      exact h x (by simpa [IsRoot] using hx)
  · intro p hp hirr
    have := hirr.natDegree_le_two
    omega

/-- A monic irreducible real polynomial is either `x - l` or `x^2 + b x + c` with `b^2 < 4c`. -/
lemma monic_irreducible_real {f : ℝ[X]} (hm : f.Monic) (hi : Irreducible f) :
    (∃ l : ℝ, f = X - C l) ∨ ∃ q : ℝ × ℝ, q.1 ^ 2 < 4 * q.2 ∧ f = quadFactor q := by
  have h1 := hi.natDegree_pos
  have h2 := hi.natDegree_le_two
  have : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
  rcases this with hd | hd
  · left
    refine ⟨-f.coeff 0, ?_⟩
    rw [hm.eq_X_add_C hd]
    simp [sub_eq_add_neg]
  · right
    have hf : f = quadFactor (f.coeff 1, f.coeff 0) := by
      ext n
      have hlead : f.coeff 2 = 1 := by simpa [hd] using hm.coeff_natDegree
      rcases n with _ | _ | _ | n
      · simp [quadFactor, coeff_C]
      · simp [quadFactor, coeff_C]
      · simp [quadFactor, hlead]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [quadFactor]
    refine ⟨(f.coeff 1, f.coeff 0), ?_, hf⟩
    rw [hf] at hi
    exact (hefferon_Five_I_1_6.2.2.1 _ _).mp hi

/-- A predicate recording that `p = c * ∏ (x - l) * ∏ (x^2 + b x + c')` with all quadratics having
negative discriminant. -/
def IsRealFactorization (p : ℝ[X]) (d : ℝ × Multiset ℝ × Multiset (ℝ × ℝ)) : Prop :=
  (∀ q ∈ d.2.2, q.1 ^ 2 < 4 * q.2) ∧
    p = C d.1 * (d.2.1.map fun l => X - C l).prod * (d.2.2.map quadFactor).prod

lemma exists_monic_factorization :
    ∀ (n : ℕ) (f : ℝ[X]), f.Monic → f.natDegree = n →
      ∃ (ls : Multiset ℝ) (qs : Multiset (ℝ × ℝ)), (∀ q ∈ qs, q.1 ^ 2 < 4 * q.2) ∧
        f = (ls.map fun l => X - C l).prod * (qs.map quadFactor).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hm hn
    by_cases h0 : f.natDegree = 0
    · refine ⟨0, 0, by simp, ?_⟩
      simpa using (Monic.natDegree_eq_zero hm).mp h0
    · obtain ⟨g, hgm, hgi, k, hk⟩ := exists_monic_irreducible_factor f
        (not_isUnit_of_natDegree_pos f (Nat.pos_of_ne_zero h0))
      have hkm : k.Monic := hgm.of_mul_monic_left (hk ▸ hm)
      have hdeg : f.natDegree = g.natDegree + k.natDegree := by
        rw [hk, natDegree_mul hgm.ne_zero hkm.ne_zero]
      have hlt : k.natDegree < n := by
        have := hgi.natDegree_pos; omega
      obtain ⟨ls, qs, hq, hkk⟩ := ih _ hlt k hkm rfl
      rcases monic_irreducible_real hgm hgi with ⟨l, hl⟩ | ⟨q, hq', hqg⟩
      · refine ⟨l ::ₘ ls, qs, hq, ?_⟩
        rw [hk, hkk, hl]; simp [mul_assoc]
      · refine ⟨ls, q ::ₘ qs, ?_, ?_⟩
        · intro q' hq''
          rcases Multiset.mem_cons.mp hq'' with rfl | h
          · exact hq'
          · exact hq q' h
        · rw [hk, hkk, hqg]; simp only [Multiset.map_cons, Multiset.prod_cons]; ring

lemma isRealFactorization_exists {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ d, IsRealFactorization p d := by
  have hm : (p * C p.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hp
  obtain ⟨ls, qs, hq, h⟩ := exists_monic_factorization _ _ hm rfl
  refine ⟨(p.leadingCoeff, ls, qs), hq, ?_⟩
  have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  show p = C p.leadingCoeff * _ * _
  rw [mul_assoc, ← h, mul_left_comm, ← C_mul, mul_inv_cancel₀ hl]
  simp

lemma monic_linProd (ls : Multiset ℝ) : (ls.map fun l => X - C l).prod.Monic :=
  monic_multiset_prod_of_monic _ _ (fun l _ => monic_X_sub_C l)

lemma monic_quadProd (qs : Multiset (ℝ × ℝ)) : (qs.map quadFactor).prod.Monic :=
  monic_multiset_prod_of_monic _ _ (fun q _ => quad_monic q.1 q.2)

lemma quadProd_roots {qs : Multiset (ℝ × ℝ)} (hq : ∀ q ∈ qs, q.1 ^ 2 < 4 * q.2) :
    (qs.map quadFactor).prod.roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [mem_roots (monic_quadProd qs).ne_zero, IsRoot, eval_multiset_prod, Multiset.map_map] at hx
  have : (0 : ℝ) ∈ qs.map ((eval x) ∘ quadFactor) := by
    exact Multiset.prod_eq_zero_iff.mp hx
  obtain ⟨q, hqm, hq0⟩ := Multiset.mem_map.mp this
  have := (quad_no_root_iff q.1 q.2).mpr (hq q hqm) x
  simp [quadFactor] at hq0
  exact this (by linarith)

lemma IsRealFactorization.lead {p : ℝ[X]} {d} (h : IsRealFactorization p d) :
    p.leadingCoeff = d.1 := by
  rw [h.2, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, (monic_linProd _).leadingCoeff,
    (monic_quadProd _).leadingCoeff]
  simp

lemma IsRealFactorization.roots_eq {p : ℝ[X]} {d} (hp : p ≠ 0) (h : IsRealFactorization p d) :
    p.roots = d.2.1 := by
  have hc : d.1 ≠ 0 := by
    rw [← h.lead]; exact leadingCoeff_ne_zero.mpr hp
  have hp' := h.2
  conv_lhs => rw [hp']
  rw [roots_mul (hp' ▸ hp), roots_C_mul _ hc, quadProd_roots h.1, add_zero,
    roots_multiset_prod_X_sub_C]

lemma isRealFactorization_unique {p : ℝ[X]} (hp : p ≠ 0) {d d' : ℝ × Multiset ℝ × Multiset (ℝ × ℝ)}
    (h : IsRealFactorization p d) (h' : IsRealFactorization p d') : d = d' := by
  have hc : d.1 = d'.1 := h.lead.symm.trans h'.lead
  have hl : d.2.1 = d'.2.1 := (h.roots_eq hp).symm.trans (h'.roots_eq hp)
  have hc0 : d.1 ≠ 0 := by rw [← h.lead]; exact leadingCoeff_ne_zero.mpr hp
  have hB : (d.2.2.map quadFactor).prod = (d'.2.2.map quadFactor).prod := by
    have e := h.2.symm.trans h'.2
    rw [← hc, ← hl] at e
    have hA : C d.1 * (d.2.1.map fun l => X - C l).prod ≠ 0 :=
      mul_ne_zero (by simpa using hc0) (monic_linProd _).ne_zero
    exact mul_left_cancel₀ hA e
  have hq : d.2.2.map quadFactor = d'.2.2.map quadFactor := by
    have irr : ∀ qs : Multiset (ℝ × ℝ), (∀ q ∈ qs, q.1 ^ 2 < 4 * q.2) →
        UniqueFactorizationMonoid.normalizedFactors (qs.map quadFactor).prod = qs.map quadFactor := by
      intro qs hqs
      rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq]
      · refine (Multiset.map_congr (g := id) rfl ?_).trans (Multiset.map_id _)
        intro x hx
        obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hx
        exact (quad_monic q.1 q.2).normalize_eq_self
      · intro x hx
        obtain ⟨q, hqm, rfl⟩ := Multiset.mem_map.mp hx
        exact (hefferon_Five_I_1_6.2.2.1 q.1 q.2).mpr (hqs q hqm)
    rw [← irr _ h.1, ← irr _ h'.1, hB]
  have hq2 : d.2.2 = d'.2.2 := Multiset.map_injective quadFactor_injective hq
  obtain ⟨a, b, c⟩ := d
  obtain ⟨a', b', c'⟩ := d'
  simp only at hc hl hq2
  rw [hc, hl, hq2]

/-- Factorization of real polynomials: every nonzero real polynomial is, uniquely up to the order of
the factors, a constant times a product of monic linear factors `x - l` and monic quadratic factors
`x^2 + b x + c` with `b^2 < 4c`; the data are the constant, the multiset of the `l`, and the multiset
of the pairs `(b, c)`. -/
@[kb "axler2024" "4.16, p. 146"]
theorem axler_4_16 {p : ℝ[X]} (hp : p ≠ 0) :
    ∃! d : ℝ × Multiset ℝ × Multiset (ℝ × ℝ), IsRealFactorization p d := by
  obtain ⟨d, hd⟩ := isRealFactorization_exists hp
  exact ⟨d, hd, fun d' hd' => isRealFactorization_unique hp hd' hd⟩

end Real

end UndergradKB.LinearAlgebra
