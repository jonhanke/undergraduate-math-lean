import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # Constructible numbers (Petrunin, chapter 19C)

The book (p. 160) calls a real number *constructible* when it can be expressed from the integers by `+`, `-`,
`·`, `/` and the square root; by Theorem 19.8 these are the coordinates of the points obtainable by ruler and
compass from `(0,0)` and `(1,0)`. The book lists the classical impossibilities (pp. 157-160) and says their
proofs need field theory; we give them:

* every constructible number lies in a tower of field extensions of `ℚ` of degree at most 2 each, hence its
  degree over `ℚ` is a power of 2;
* doubling the cube is impossible: the real cube root of 2 is not constructible;
* the angle `π/3` cannot be trisected: `cos (π/9)` is not constructible (from `cos (π/3) = 1/2`), and the
  regular 9-gon is not constructible: `cos (2π/9)` is not constructible.

Squaring the circle (`√π` not constructible) needs the transcendence of `π` (Lindemann), which Mathlib does not
have at this commit (it has `irrational_pi` only). -/

namespace UndergradKB.Geometry

open Polynomial IntermediateField Module Real

/-- Constructible real numbers (Petrunin, p. 160): the smallest set of reals containing the integers and closed
under `+`, `-`, `·`, `/` and the square root. (`Real.sqrt` of a negative number is `0`, so allowing every
argument of the square root changes nothing.) -/
inductive IsConstructible : ℝ → Prop
  | intCast (n : ℤ) : IsConstructible n
  | add {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x + y)
  | neg {x : ℝ} : IsConstructible x → IsConstructible (-x)
  | mul {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x * y)
  | inv {x : ℝ} : IsConstructible x → IsConstructible x⁻¹
  | sqrt {x : ℝ} : IsConstructible x → IsConstructible (Real.sqrt x)

namespace IsConstructible

theorem sub {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) : IsConstructible (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem div {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) : IsConstructible (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv

theorem ratCast (q : ℚ) : IsConstructible q := by
  rw [Rat.cast_def]
  exact (intCast q.num).div (by exact_mod_cast intCast (q.den : ℤ))

end IsConstructible

/-- Towers of quadratic extensions inside `ℝ`: `ℚ`, and `K(x)` whenever `K` is a tower and `x² ∈ K`. -/
inductive QuadTower : IntermediateField ℚ ℝ → Prop
  | bot : QuadTower ⊥
  | step {K : IntermediateField ℚ ℝ} (x : ℝ) : QuadTower K → x ^ 2 ∈ K →
      QuadTower (adjoin ℚ ((K : Set ℝ) ∪ {x}))

theorem finrank_adjoin_sq_mem {K : IntermediateField ℚ ℝ} {x : ℝ} (hx : x ^ 2 ∈ K) :
    finrank K K⟮x⟯ = 1 ∨ finrank K K⟮x⟯ = 2 := by
  set p : K[X] := X ^ 2 - C ⟨x ^ 2, hx⟩
  have hp : p.Monic := by
    simpa [p] using monic_X_pow_sub_C (⟨x ^ 2, hx⟩ : K) two_ne_zero
  have hpdeg : p.natDegree = 2 := by
    simp [p]
  have hroot : aeval x p = 0 := by simp [p]
  have hint : IsIntegral K x := ⟨p, hp, by simpa [aeval_def] using hroot⟩
  rw [adjoin.finrank hint]
  have h1 := minpoly.natDegree_pos hint
  have h2 : (minpoly K x).natDegree ≤ 2 := by
    have := minpoly.degree_le_of_ne_zero K x hp.ne_zero hroot
    rw [degree_eq_natDegree (minpoly.ne_zero hint), degree_eq_natDegree hp.ne_zero, hpdeg] at this
    exact_mod_cast this
  omega

/-- Every quadratic tower is finite-dimensional over `ℚ` of degree a power of 2. -/
theorem QuadTower.finrank_eq_two_pow {K : IntermediateField ℚ ℝ} (hK : QuadTower K) :
    FiniteDimensional ℚ K ∧ ∃ n : ℕ, finrank ℚ K = 2 ^ n := by
  induction hK with
  | bot => exact ⟨inferInstance, 0, by simp⟩
  | @step K x _ hx ih =>
    obtain ⟨hfin, n, hn⟩ := ih
    rw [← restrictScalars_adjoin]
    have hint : IsIntegral K x := by
      refine ⟨X ^ 2 - C ⟨x ^ 2, hx⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      simp [eval₂_sub]
    have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hint
    have : FiniteDimensional ℚ K⟮x⟯ := FiniteDimensional.trans ℚ K K⟮x⟯
    refine ⟨(inferInstance : FiniteDimensional ℚ K⟮x⟯), ?_⟩
    have htower : finrank ℚ K * finrank K K⟮x⟯ = finrank ℚ K⟮x⟯ :=
      Module.finrank_mul_finrank ℚ K K⟮x⟯
    change ∃ m, finrank ℚ K⟮x⟯ = 2 ^ m
    rcases finrank_adjoin_sq_mem hx with h | h
    · exact ⟨n, by rw [← htower, h, hn, mul_one]⟩
    · exact ⟨n + 1, by rw [← htower, h, hn, pow_succ]⟩

/-- Two quadratic towers lie in a common one. -/
theorem QuadTower.exists_common {K L : IntermediateField ℚ ℝ} (hK : QuadTower K) (hL : QuadTower L) :
    ∃ M, QuadTower M ∧ K ≤ M ∧ L ≤ M := by
  induction hL with
  | bot => exact ⟨K, hK, le_rfl, bot_le⟩
  | @step L x _ hx ih =>
    obtain ⟨M, hM, hKM, hLM⟩ := ih
    refine ⟨adjoin ℚ ((M : Set ℝ) ∪ {x}), hM.step x (hLM hx), hKM.trans ?_, ?_⟩
    · exact fun y hy => subset_adjoin ℚ _ (Set.mem_union_left _ hy)
    · exact adjoin.mono ℚ _ _ (Set.union_subset_union_left _ hLM)

/-- Every constructible number lies in a quadratic tower. -/
theorem IsConstructible.exists_quadTower {x : ℝ} (hx : IsConstructible x) :
    ∃ K, QuadTower K ∧ x ∈ K := by
  induction hx with
  | intCast n => exact ⟨⊥, .bot, (⊥ : IntermediateField ℚ ℝ).intCast_mem n⟩
  | add _ _ ihx ihy =>
    obtain ⟨K, hK, hxK⟩ := ihx
    obtain ⟨L, hL, hyL⟩ := ihy
    obtain ⟨M, hM, hKM, hLM⟩ := hK.exists_common hL
    exact ⟨M, hM, add_mem (hKM hxK) (hLM hyL)⟩
  | neg _ ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    exact ⟨K, hK, neg_mem hxK⟩
  | mul _ _ ihx ihy =>
    obtain ⟨K, hK, hxK⟩ := ihx
    obtain ⟨L, hL, hyL⟩ := ihy
    obtain ⟨M, hM, hKM, hLM⟩ := hK.exists_common hL
    exact ⟨M, hM, mul_mem (hKM hxK) (hLM hyL)⟩
  | inv _ ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    exact ⟨K, hK, inv_mem hxK⟩
  | @sqrt x _ ih =>
    obtain ⟨K, hK, hxK⟩ := ih
    have hsq : Real.sqrt x ^ 2 ∈ K := by
      rcases le_or_gt 0 x with h | h
      · rwa [Real.sq_sqrt h]
      · rw [Real.sqrt_eq_zero_of_nonpos h.le]; simp
    exact ⟨_, hK.step _ hsq, subset_adjoin ℚ _ (Set.mem_union_right _ rfl)⟩

/-- The degree over `ℚ` of a constructible number is a power of 2: the field theory that the book's remarks
after Theorem 19.8 (p. 160) say the impossibility proofs need. -/
@[kb "petrunin2025" "Section 19C, constructible numbers, p. 160"]
theorem IsConstructible.natDegree_minpoly {x : ℝ} (hx : IsConstructible x) :
    IsIntegral ℚ x ∧ ∃ n : ℕ, (minpoly ℚ x).natDegree = 2 ^ n := by
  obtain ⟨K, hK, hxK⟩ := hx.exists_quadTower
  obtain ⟨hfin, n, hn⟩ := hK.finrank_eq_two_pow
  have hint : IsIntegral ℚ x := by
    have : IsIntegral ℚ (⟨x, hxK⟩ : K) := IsIntegral.of_finite ℚ _
    exact (isIntegral_iff (S := K)).mp this
  refine ⟨hint, ?_⟩
  have hle : ℚ⟮x⟯ ≤ K := adjoin_simple_le_iff.mpr hxK
  have hdvd : finrank ℚ ℚ⟮x⟯ ∣ finrank ℚ K := finrank_dvd_of_le_right hle
  rw [hn, Nat.dvd_prime_pow Nat.prime_two] at hdvd
  obtain ⟨m, -, hm⟩ := hdvd
  exact ⟨m, by rw [← adjoin.finrank hint, hm]⟩

/-- If `x` is a root of a monic cubic over `ℚ` with no rational root, `x` is not constructible. -/
theorem not_isConstructible_of_cubic {x : ℝ} {p : ℚ[X]} (hp : p.Monic) (hdeg : p.natDegree = 3)
    (hroot : aeval x p = 0) (hnot : ∀ q : ℚ, ¬ p.IsRoot q) : ¬ IsConstructible x := by
  intro hx
  obtain ⟨hint, n, hn⟩ := hx.natDegree_minpoly
  have hirr : Irreducible p :=
    irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hnot
  have hmin : p = minpoly ℚ x := minpoly.eq_of_irreducible_of_monic hirr hroot hp
  rw [← hmin, hdeg] at hn
  have h2 : (2 : ℕ) ∣ 3 := by
    rcases n with _ | n
    · simp at hn
    · exact ⟨2 ^ n, by rw [hn, pow_succ, mul_comm]⟩
  omega

/-- **Doubling the cube is impossible** (Petrunin, Section 19B, p. 157-158, and p. 160): a real number `x`
with `x ^ 3 = 2` (the edge of a cube of volume 2) is not constructible. -/
@[kb "petrunin2025" "Section 19B, doubling the cube, pp. 157-160"]
theorem not_isConstructible_cbrt_two {x : ℝ} (hx : x ^ 3 = 2) : ¬ IsConstructible x := by
  refine not_isConstructible_of_cubic (p := X ^ 3 - C 2) (monic_X_pow_sub_C _ (by norm_num))
    (natDegree_X_pow_sub_C _) (by simp [hx]) ?_
  intro q hq
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hq
  have hint : IsIntegral ℤ q :=
    ⟨X ^ 3 - C 2, monic_X_pow_sub_C _ (by norm_num), by simp [eval₂_sub, hq]⟩
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hn3 : n ^ 3 = 2 := by
    have : ((n ^ 3 : ℤ) : ℚ) = (2 : ℤ) := by
      push_cast; rw [show ((n : ℚ)) = q from hn]; exact hq
    exact_mod_cast this
  have h1 : n * (n ^ 2) = 2 := by rw [← hn3]; ring
  rcases le_or_gt n 1 with h | h
  · nlinarith [sq_nonneg n, sq_nonneg (n + 1)]
  · nlinarith

/-- `cos (π/9)` is a root of `X³ - (3/4) X - 1/8` (from `cos 3θ = 4 cos³ θ - 3 cos θ`). -/
theorem cos_pi_div_nine_cubic : Real.cos (π / 9) ^ 3 - 3 / 4 * Real.cos (π / 9) - 1 / 8 = 0 := by
  have h := Real.cos_three_mul (π / 9)
  rw [show 3 * (π / 9) = π / 3 by ring, Real.cos_pi_div_three] at h
  linarith

/-- **The angle `π/3` cannot be trisected** (Petrunin, Section 19B, p. 158, and p. 160): `cos (π/9)` is not
constructible, although `cos (π/3) = 1/2` is. -/
@[kb "petrunin2025" "Section 19B, angle trisection, pp. 158-160"]
theorem not_isConstructible_cos_pi_div_nine : ¬ IsConstructible (Real.cos (π / 9)) := by
  have hmon : (X ^ 3 - C (3 / 4 : ℚ) * X - C (1 / 8)).Monic := by monicity!
  have hdeg : (X ^ 3 - C (3 / 4 : ℚ) * X - C (1 / 8)).natDegree = 3 := by compute_degree!
  refine not_isConstructible_of_cubic hmon hdeg ?_ ?_
  · simpa using cos_pi_div_nine_cubic
  intro q hq
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hq
  -- `r = 2 q` is a root of the monic integer polynomial `X³ - 3 X - 1`
  have hr : (2 * q) ^ 3 - 3 * (2 * q) - 1 = 0 := by linear_combination 8 * hq
  have hmonZ : (X ^ 3 - C (3 : ℤ) * X - C 1).Monic := by monicity!
  have hint : IsIntegral ℤ (2 * q) :=
    ⟨_, hmonZ, by simpa [eval₂_sub] using hr⟩
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm3 : m * (m ^ 2 - 3) = 1 := by
    have : ((m * (m ^ 2 - 3) : ℤ) : ℚ) = (1 : ℤ) := by
      push_cast; rw [show ((m : ℚ)) = 2 * q from hm]; linear_combination hr
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hm3 with h | h <;> subst h <;> norm_num at hm3

/-- **The regular 9-gon is not constructible** (Petrunin, Section 19B, p. 158, the example after the
Gauss-Wantzel theorem 19.6): `cos (2π/9)` is not constructible. -/
@[kb "petrunin2025" "Theorem 19.6 (case n = 9), p. 158"]
theorem not_isConstructible_cos_two_pi_div_nine : ¬ IsConstructible (Real.cos (2 * π / 9)) := by
  intro h
  apply not_isConstructible_cos_pi_div_nine
  have hpos : 0 < Real.cos (π / 9) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_pos]
  have hsq : Real.cos (π / 9) ^ 2 = (1 + Real.cos (2 * π / 9)) / 2 := by
    rw [show 2 * π / 9 = 2 * (π / 9) by ring, Real.cos_two_mul]; ring
  have : Real.cos (π / 9) = Real.sqrt ((1 + Real.cos (2 * π / 9)) / 2) := by
    rw [← hsq, Real.sqrt_sq hpos.le]
  rw [this]
  exact (((IsConstructible.intCast 1).add h).div (by exact_mod_cast IsConstructible.intCast 2)).sqrt

end UndergradKB.Geometry
