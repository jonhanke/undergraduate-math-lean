import UndergradKB.Geometry.RulerCompass
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime

/-! # The Gauss-Wantzel theorem, necessity (Petrunin, Theorem 19.6)

Theorem 19.6 (p. 158): a regular `n`-gon can be constructed with ruler and compass iff `n` is a power of 2 times
a product of distinct Fermat primes. We prove the "only if" half, which contains every impossibility statement
of the book's list (the 7-gon, the 9-gon, ...):

* `IsConstructible.totient_eq_two_pow`: if `cos (2π/n)` is constructible (`n ≥ 1`), then Euler's `φ(n)` is a
  power of 2, because the primitive root of unity `exp (2πi/n) = cos + i sin` lies in a tower of quadratic
  extensions of `ℚ` inside `ℂ` and its degree over `ℚ` is `φ(n)` (irreducibility of cyclotomic polynomials);
* `fermat_form_of_totient_eq_two_pow`: if `φ(n)` is a power of 2, every odd prime divisor `p` of `n` is a Fermat
  prime `2^k + 1` and `p²` does not divide `n`;
* `gauss_wantzel_necessity`: for a ruler-and-compass construction from `O = (0,0)` and `A₁ = (1,0)`, if some
  constructed point is the vertex `A₂ = (cos (2π/n), sin (2π/n))` of the regular `n`-gon with centre `O` and
  vertex `A₁` (it suffices that its first coordinate is `cos (2π/n)`), then `n` has that form.

The sufficiency half (the construction of the 17-gon and its relatives) needs Gauss periods and is not done. -/

namespace UndergradKB.Geometry

open Polynomial IntermediateField Module Real

section Tower

variable {L : Type*} [Field L] [CharZero L]

/-- Towers of quadratic extensions of `ℚ` inside a field `L` of characteristic zero. -/
inductive QuadTowerIn : IntermediateField ℚ L → Prop
  | bot : QuadTowerIn ⊥
  | step {K : IntermediateField ℚ L} (x : L) : QuadTowerIn K → x ^ 2 ∈ K →
      QuadTowerIn (adjoin ℚ ((K : Set L) ∪ {x}))

theorem finrank_adjoin_sq_mem' {K : IntermediateField ℚ L} {x : L} (hx : x ^ 2 ∈ K) :
    IsIntegral K x ∧ (finrank K K⟮x⟯ = 1 ∨ finrank K K⟮x⟯ = 2) := by
  set p : K[X] := X ^ 2 - C ⟨x ^ 2, hx⟩
  have hp : p.Monic := monic_X_pow_sub_C _ two_ne_zero
  have hpdeg : p.natDegree = 2 := by simp [p]
  have hroot : aeval x p = 0 := by simp [p]
  have hint : IsIntegral K x := ⟨p, hp, by simpa [aeval_def] using hroot⟩
  refine ⟨hint, ?_⟩
  rw [adjoin.finrank hint]
  have h1 := minpoly.natDegree_pos hint
  have h2 : (minpoly K x).natDegree ≤ 2 := by
    have := minpoly.degree_le_of_ne_zero K x hp.ne_zero hroot
    rw [degree_eq_natDegree (minpoly.ne_zero hint), degree_eq_natDegree hp.ne_zero, hpdeg] at this
    exact_mod_cast this
  omega

theorem QuadTowerIn.finrank_eq_two_pow {K : IntermediateField ℚ L} (hK : QuadTowerIn K) :
    FiniteDimensional ℚ K ∧ ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  induction hK with
  | bot => exact ⟨inferInstance, 0, by simp⟩
  | @step K x _ hx ih =>
    obtain ⟨hfin, n, hn⟩ := ih
    rw [← restrictScalars_adjoin]
    obtain ⟨hint, hdeg⟩ := finrank_adjoin_sq_mem' hx
    have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hint
    have : FiniteDimensional ℚ K⟮x⟯ := FiniteDimensional.trans ℚ K K⟮x⟯
    refine ⟨(inferInstance : FiniteDimensional ℚ K⟮x⟯), ?_⟩
    have htower : Module.finrank ℚ K * Module.finrank K K⟮x⟯ = Module.finrank ℚ K⟮x⟯ :=
      Module.finrank_mul_finrank ℚ K K⟮x⟯
    change ∃ m, Module.finrank ℚ K⟮x⟯ = 2 ^ m
    rcases hdeg with h | h
    · exact ⟨n, by rw [← htower, h, hn, mul_one]⟩
    · exact ⟨n + 1, by rw [← htower, h, hn, pow_succ]⟩

theorem QuadTowerIn.exists_common {K M : IntermediateField ℚ L} (hK : QuadTowerIn K)
    (hM : QuadTowerIn M) : ∃ N, QuadTowerIn N ∧ K ≤ N ∧ M ≤ N := by
  induction hM with
  | bot => exact ⟨K, hK, le_rfl, bot_le⟩
  | @step M x _ hx ih =>
    obtain ⟨N, hN, hKN, hMN⟩ := ih
    refine ⟨adjoin ℚ ((N : Set L) ∪ {x}), hN.step x (hMN hx), hKN.trans ?_, ?_⟩
    · exact fun y hy => subset_adjoin ℚ _ (Set.mem_union_left _ hy)
    · exact adjoin.mono ℚ _ _ (Set.union_subset_union_left _ hMN)

/-- Numbers of `L` obtained from the integers by `+`, `-`, `·`, `⁻¹` and square roots (any `y` with `y²`
already obtained). -/
inductive IsConstructibleIn : L → Prop
  | intCast (n : ℤ) : IsConstructibleIn n
  | add {x y : L} : IsConstructibleIn x → IsConstructibleIn y → IsConstructibleIn (x + y)
  | neg {x : L} : IsConstructibleIn x → IsConstructibleIn (-x)
  | mul {x y : L} : IsConstructibleIn x → IsConstructibleIn y → IsConstructibleIn (x * y)
  | inv {x : L} : IsConstructibleIn x → IsConstructibleIn x⁻¹
  | sqrt {x y : L} : IsConstructibleIn x → y ^ 2 = x → IsConstructibleIn y

theorem IsConstructibleIn.exists_quadTower {x : L} (hx : IsConstructibleIn x) :
    ∃ K, QuadTowerIn K ∧ x ∈ K := by
  induction hx with
  | intCast n => exact ⟨⊥, .bot, (⊥ : IntermediateField ℚ L).intCast_mem n⟩
  | add _ _ ihx ihy =>
    obtain ⟨K, hK, hxK⟩ := ihx
    obtain ⟨M, hM, hyM⟩ := ihy
    obtain ⟨N, hN, hKN, hMN⟩ := hK.exists_common hM
    exact ⟨N, hN, add_mem (hKN hxK) (hMN hyM)⟩
  | neg _ ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    exact ⟨K, hK, neg_mem hxK⟩
  | mul _ _ ihx ihy =>
    obtain ⟨K, hK, hxK⟩ := ihx
    obtain ⟨M, hM, hyM⟩ := ihy
    obtain ⟨N, hN, hKN, hMN⟩ := hK.exists_common hM
    exact ⟨N, hN, mul_mem (hKN hxK) (hMN hyM)⟩
  | inv _ ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    exact ⟨K, hK, inv_mem hxK⟩
  | @sqrt x y _ hy ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    exact ⟨_, hK.step y (hy ▸ hxK), subset_adjoin ℚ _ (Set.mem_union_right _ rfl)⟩

/-- The degree over `ℚ` of a number obtained by arithmetic and square roots is a power of 2. -/
theorem IsConstructibleIn.natDegree_minpoly {x : L} (hx : IsConstructibleIn x) :
    IsIntegral ℚ x ∧ ∃ n : ℕ, (minpoly ℚ x).natDegree = 2 ^ n := by
  obtain ⟨K, hK, hxK⟩ := hx.exists_quadTower
  obtain ⟨hfin, n, hn⟩ := hK.finrank_eq_two_pow
  have hint : IsIntegral ℚ x := by
    have : IsIntegral ℚ (⟨x, hxK⟩ : K) := IsIntegral.of_finite ℚ _
    exact (isIntegral_iff (S := K)).mp this
  refine ⟨hint, ?_⟩
  have hle : ℚ⟮x⟯ ≤ K := adjoin_simple_le_iff.mpr hxK
  have hdvd : Module.finrank ℚ ℚ⟮x⟯ ∣ Module.finrank ℚ K := finrank_dvd_of_le_right hle
  rw [hn, Nat.dvd_prime_pow Nat.prime_two] at hdvd
  obtain ⟨m, -, hm⟩ := hdvd
  exact ⟨m, by rw [← adjoin.finrank hint, hm]⟩

end Tower

/-- A constructible real number is, as a complex number, obtained by arithmetic and square roots. -/
theorem IsConstructible.ofReal {x : ℝ} (hx : IsConstructible x) : IsConstructibleIn (x : ℂ) := by
  induction hx with
  | intCast n => exact_mod_cast IsConstructibleIn.intCast n
  | add _ _ ihx ihy => push_cast; exact ihx.add ihy
  | neg _ ih => push_cast; exact ih.neg
  | mul _ _ ihx ihy => push_cast; exact ihx.mul ihy
  | inv _ ih => push_cast; exact ih.inv
  | @sqrt x _ ih =>
    rcases le_or_gt 0 x with h | h
    · exact ih.sqrt (by rw [← Complex.ofReal_pow, Real.sq_sqrt h])
    · rw [Real.sqrt_eq_zero_of_nonpos h.le, Complex.ofReal_zero]
      exact_mod_cast IsConstructibleIn.intCast (L := ℂ) 0

/-- If `cos (2π/n)` is constructible then `φ(n)` is a power of 2. -/
theorem IsConstructible.totient_eq_two_pow {n : ℕ} (hn : 0 < n)
    (h : IsConstructible (Real.cos (2 * π / n))) : ∃ k : ℕ, Nat.totient n = 2 ^ k := by
  set θ : ℝ := 2 * π / n
  have hc : IsConstructibleIn ((Real.cos θ : ℝ) : ℂ) := h.ofReal
  -- `i sin θ` is a square root of `cos² θ - 1`
  have hs : IsConstructibleIn (Complex.I * (Real.sin θ : ℂ)) := by
    refine (hc.mul hc |>.add (IsConstructibleIn.intCast (-1))).sqrt ?_
    have hcast : ((Real.sin θ : ℝ) : ℂ) ^ 2 + ((Real.cos θ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    rw [mul_pow, Complex.I_sq]
    simp only [Int.cast_neg, Int.cast_one]
    linear_combination -hcast
  have hz : IsConstructibleIn (Complex.exp (2 * π * Complex.I / n)) := by
    have e : Complex.exp (2 * π * Complex.I / n) =
        ((Real.cos θ : ℝ) : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
      rw [show (2 * π * Complex.I / n : ℂ) = ((θ : ℝ) : ℂ) * Complex.I by
        simp only [θ]; push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    rw [e]; exact hc.add hs
  obtain ⟨-, k, hk⟩ := hz.natDegree_minpoly
  refine ⟨k, ?_⟩
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn, Polynomial.natDegree_cyclotomic] at hk
  exact hk

/-- If `φ(n)` is a power of 2, every odd prime divisor of `n` is a Fermat prime dividing `n` only once. -/
theorem fermat_form_of_totient_eq_two_pow {n k : ℕ} (hk : Nat.totient n = 2 ^ k) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ n ∧ ∃ j : ℕ, p = 2 ^ j + 1 := by
  constructor
  · intro hsq
    have := Nat.totient_dvd_of_dvd hsq
    rw [Nat.totient_prime_pow hp two_pos, hk] at this
    have hdvd : p ∣ 2 ^ k := (dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num)) _).trans this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
    exact hp2 this
  · have := Nat.totient_dvd_of_dvd hpn
    rw [Nat.totient_prime hp, hk, Nat.dvd_prime_pow Nat.prime_two] at this
    obtain ⟨j, -, hj⟩ := this
    exact ⟨j, by have := hp.one_lt; omega⟩

/-- **Gauss-Wantzel theorem, necessity** (Petrunin, Theorem 19.6, p. 158), algebraic form: if `cos (2π/n)`
is constructible, then `n` is a power of 2 times distinct Fermat primes: each odd prime divisor `p` of `n` has
the form `2^j + 1` and `p²` does not divide `n`. -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem gauss_wantzel_necessity_algebraic {n : ℕ} (hn : 0 < n)
    (h : IsConstructible (Real.cos (2 * π / n))) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ n ∧ ∃ j : ℕ, p = 2 ^ j + 1 := by
  obtain ⟨k, hk⟩ := h.totient_eq_two_pow hn
  exact fermat_form_of_totient_eq_two_pow hk hp hpn hp2

/-- **Gauss-Wantzel theorem, necessity** (Petrunin, Theorem 19.6, p. 158): if a ruler-and-compass construction
from the centre `O = (0,0)` and the vertex `A₁ = (1,0)` produces the next vertex `A₂` of the regular `n`-gon
(a point with first coordinate `cos (2π/n)`), then every odd prime divisor `p` of `n` is a Fermat prime
`2^j + 1` and divides `n` only once. -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem gauss_wantzel_necessity {n : ℕ} (hn : 0 < n) {X : ℝ × ℝ}
    (hX : RCConstructible {(0, 0), (1, 0)} (.point X)) (hX1 : X.1 = Real.cos (2 * π / n)) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ n ∧ ∃ j : ℕ, p = 2 ^ j + 1 := by
  have hS : ∀ x ∈ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), IsConstructiblePoint x := by
    rintro x (rfl | rfl)
    exacts [isConstructiblePoint_zero, isConstructiblePoint_one_zero]
  exact gauss_wantzel_necessity_algebraic hn (hX1 ▸ (hX.coords hS).1) hp hpn hp2

/-- The regular 7-gon cannot be constructed with ruler and compass (Petrunin, example after Theorem 19.6). -/
@[kb "petrunin2025" "Theorem 19.6 (case n = 7), p. 158"]
theorem not_isConstructible_cos_two_pi_div_seven : ¬ IsConstructible (Real.cos (2 * π / 7)) := by
  intro h
  obtain ⟨-, j, hj⟩ := gauss_wantzel_necessity_algebraic (n := 7) (by norm_num) (by exact_mod_cast h)
    (by norm_num) dvd_rfl (by norm_num)
  have : 2 ^ j = 6 := by omega
  have hj3 : j < 3 := by
    by_contra hc
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j <;> simp_all

end UndergradKB.Geometry
