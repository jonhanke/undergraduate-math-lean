import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-!
# Radicals (Stitz-Zeager, Precalculus, §5.3)

Mathlib has no real odd root of negative numbers (`Real.rpow` uses the complex power for negative
bases), so we introduce the bridging definition `principalRoot`, and prove the book's
characterisation of the principal root and the radical rules for it.
-/

namespace UndergradKB.Precalculus

/-- The principal `n`-th root of a real number: for `x ≥ 0` it is `x ^ (1/n)`, and for `x < 0`
it is `-((-x)^(1/n))` (this is the correct real root when `n` is odd; for even `n` and `x < 0`
the value is a junk value that no theorem uses). -/
noncomputable def principalRoot (n : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ ((n : ℝ)⁻¹) else -((-x) ^ ((n : ℝ)⁻¹))

lemma principalRoot_of_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    principalRoot n x = x ^ ((n : ℝ)⁻¹) := by
  simp [principalRoot, hx]

lemma principalRoot_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x) : 0 ≤ principalRoot n x := by
  rw [principalRoot_of_nonneg hx]; exact Real.rpow_nonneg hx _

lemma principalRoot_pow {n : ℕ} {x : ℝ} (hn : n ≠ 0) (h : Odd n ∨ 0 ≤ x) :
    (principalRoot n x) ^ n = x := by
  by_cases hx : 0 ≤ x
  · rw [principalRoot_of_nonneg hx]; exact Real.rpow_inv_natCast_pow hx hn
  · have hodd : Odd n := h.resolve_right hx
    have hx' : 0 ≤ -x := by linarith [not_le.mp hx]
    simp only [principalRoot, hx, ite_false]
    rw [hodd.neg_pow, Real.rpow_inv_natCast_pow hx' hn]; ring

lemma principalRoot_unique {n : ℕ} {x r : ℝ} (hn : n ≠ 0) (h : Odd n ∨ 0 ≤ x)
    (hr : Odd n ∨ 0 ≤ r) (hrn : r ^ n = x) : r = principalRoot n x := by
  have hp := principalRoot_pow hn h
  rcases hr with ho | hr0
  · exact ho.strictMono_pow.injective (hrn.trans hp.symm)
  · have hx : 0 ≤ x := by rw [← hrn]; exact pow_nonneg hr0 _
    exact (pow_left_inj₀ hr0 (principalRoot_nonneg hx) hn).1 (hrn.trans hp.symm)

/-- Definition 5.4, odd index: for odd `n` and any real `x`, the principal `n`-th root is the
unique real `r` with `r ^ n = x` (PC-088). -/
@[kb "stitzzeager2013" "Definition 5.4, p. 409"]
theorem principalRoot_eq_iff_odd {n : ℕ} (hn : Odd n) (x r : ℝ) :
    r = principalRoot n x ↔ r ^ n = x := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  constructor
  · rintro rfl; exact principalRoot_pow hn0 (Or.inl hn)
  · intro h; exact principalRoot_unique hn0 (Or.inl hn) (Or.inl hn) h

/-- Definition 5.4, even index: for `n ≥ 1` and `x ≥ 0`, the principal `n`-th root is the unique
nonnegative real `r` with `r ^ n = x` (PC-088). For odd `n` the nonnegativity condition is not
needed; see `principalRoot_eq_iff_odd`. -/
@[kb "stitzzeager2013" "Definition 5.4, p. 409"]
theorem principalRoot_eq_iff_nonneg {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    r = principalRoot n x ↔ 0 ≤ r ∧ r ^ n = x := by
  constructor
  · rintro rfl; exact ⟨principalRoot_nonneg hx, principalRoot_pow hn (Or.inr hx)⟩
  · rintro ⟨h0, h⟩; exact principalRoot_unique hn (Or.inr hx) (Or.inr h0) h

/-- Theorem 5.6, product rule: `ⁿ√(xy) = ⁿ√x ⁿ√y`, for odd `n` (all reals) or for even `n` with
`x, y ≥ 0` (the cases where both roots are real) (PC-089). -/
@[kb "stitzzeager2013" "Theorem 5.6, p. 410"]
theorem principalRoot_mul {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (h : Odd n ∨ (0 ≤ x ∧ 0 ≤ y)) :
    principalRoot n (x * y) = principalRoot n x * principalRoot n y := by
  symm
  apply principalRoot_unique hn
  · rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (mul_nonneg hx hy)
  · rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (mul_nonneg (principalRoot_nonneg hx) (principalRoot_nonneg hy))
  · rw [mul_pow, principalRoot_pow hn (h.imp_right And.left),
      principalRoot_pow hn (h.imp_right And.right)]

/-- Theorem 5.6, quotient rule: `ⁿ√(x/y) = ⁿ√x / ⁿ√y` for `y ≠ 0`, for odd `n` (all reals) or
for even `n` with `x, y ≥ 0` (PC-089). -/
@[kb "stitzzeager2013" "Theorem 5.6, p. 410"]
theorem principalRoot_div {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (_hy : y ≠ 0)
    (h : Odd n ∨ (0 ≤ x ∧ 0 ≤ y)) :
    principalRoot n (x / y) = principalRoot n x / principalRoot n y := by
  symm
  apply principalRoot_unique hn
  · rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (div_nonneg hx hy)
  · rcases h with h | ⟨hx, hy⟩
    · exact Or.inl h
    · exact Or.inr (div_nonneg (principalRoot_nonneg hx) (principalRoot_nonneg hy))
  · rw [div_pow, principalRoot_pow hn (h.imp_right And.left),
      principalRoot_pow hn (h.imp_right And.right)]

/-- Theorem 5.6, powers of radicals: `ⁿ√(xᵐ) = (ⁿ√x)ᵐ` for a natural number `m`, for odd `n`
or `x ≥ 0` (PC-089). -/
@[kb "stitzzeager2013" "Theorem 5.6, p. 410"]
theorem principalRoot_pow_nat {n : ℕ} (hn : n ≠ 0) (m : ℕ) {x : ℝ} (h : Odd n ∨ 0 ≤ x) :
    principalRoot n (x ^ m) = (principalRoot n x) ^ m := by
  symm
  apply principalRoot_unique hn
  · exact h.imp_right (fun hx => pow_nonneg hx m)
  · exact h.imp_right (fun hx => pow_nonneg (principalRoot_nonneg hx) m)
  · rw [← pow_mul, mul_comm, pow_mul, principalRoot_pow hn h]

/-- Theorem 5.6, last rule, odd case: `ⁿ√(xⁿ) = x` for odd `n` and every real `x` (PC-090). -/
@[kb "stitzzeager2013" "Theorem 5.6, p. 410"]
theorem principalRoot_pow_self_odd {n : ℕ} (hn : Odd n) (x : ℝ) :
    principalRoot n (x ^ n) = x :=
  (principalRoot_unique hn.pos.ne' (Or.inl hn) (Or.inl hn) rfl).symm

/-- Theorem 5.6, last rule, even case: `ⁿ√(xⁿ) = |x|` for even `n ≥ 2` and every real `x`
(PC-090). -/
@[kb "stitzzeager2013" "Theorem 5.6, p. 410"]
theorem principalRoot_pow_self_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) (x : ℝ) :
    principalRoot n (x ^ n) = |x| :=
  (principalRoot_unique hn0 (Or.inr (hn.pow_nonneg x)) (Or.inr (abs_nonneg x))
    (hn.pow_abs x)).symm

/-- Definition 5.5: for `x ≥ 0`, `n ≥ 1`, `x ^ (1/n)` is the principal `n`-th root (PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem rpow_one_div_eq_principalRoot {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / (n : ℝ)) = principalRoot n x := by
  rw [principalRoot_of_nonneg hx, one_div]

/-- Definition 5.5: for `x ≥ 0`, `n ≥ 1` and an integer `m`, `x ^ (m/n) = (ⁿ√x)ᵐ` (PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem rpow_intCast_div_eq_principalRoot_zpow {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (m : ℤ) :
    x ^ ((m : ℝ) / n) = (principalRoot n x) ^ m := by
  rw [principalRoot_of_nonneg hx, ← Real.rpow_intCast, ← Real.rpow_mul hx, div_eq_inv_mul]

/-- Definition 5.5: for `x ≥ 0`, `n ≥ 1` and a natural number `m`, `x ^ (m/n) = ⁿ√(xᵐ)`
(PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem rpow_natCast_div_eq_principalRoot_pow {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x)
    (m : ℕ) : x ^ ((m : ℝ) / n) = principalRoot n (x ^ m) := by
  have := rpow_intCast_div_eq_principalRoot_zpow (n := n) hx (m : ℤ)
  simp only [Int.cast_natCast, zpow_natCast] at this
  rw [this, principalRoot_pow_nat hn m (Or.inr hx)]

end UndergradKB.Precalculus
