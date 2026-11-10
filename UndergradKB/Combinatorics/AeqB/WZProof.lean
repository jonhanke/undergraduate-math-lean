import UndergradKB.Combinatorics.AeqB.WZ

/-!
# The WZ proof procedure (Petkovsek–Wilf–Zeilberger, Chapters 2 and 7)

General theorems behind the certificate checks of `Certificates` and `Certificates2`:

* `wz_proof`: the standardized proof algorithm (a rational certificate `R`, `G = R F`, the WZ
  equation, support conditions, check at one `n`);
* `wz_eq_of_ratio_identity`: checking the WZ equation reduces to a rational-function identity
  after dividing by `F(n,k)`;
* `recurrence_of_ratio_identity`: a `k`-free recurrence is self-certifying in the same way;
* `restricted_sum_formula`: the restricted sum identity (7.3.8);
* `IsWZFunction`: WZ functions with free parameters (Gessel's approach).
-/

namespace UndergradKB.Combinatorics.AeqB

section Proof

variable {K : Type*} [CommRing K]

/-- CO-439. The standardized WZ proof algorithm: let `F` be a summand, `R` a certificate and
`G = R F` its mate.  If the WZ equation `F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` holds for all
`n, k`, the summands `F n ·` and the mates `G n ·` have finite support, and the sum at one
value `n₀` equals `1`, then `∑_k F(n,k) = 1` for every `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 36"]
theorem wz_proof (F R : ℤ → ℤ → K)
    (hWZ : ∀ n k, F (n + 1) k - F n k = R n (k + 1) * F n (k + 1) - R n k * F n k)
    (hF : ∀ n, (Function.support (F n)).Finite)
    (hG : ∀ n, (Function.support fun k => R n k * F n k).Finite)
    (n₀ : ℤ) (h₀ : ∑ᶠ k, F n₀ k = 1) (n : ℤ) : ∑ᶠ k, F n k = 1 := by
  have h : WZEq F (fun n k => R n k * F n k) := fun n k => hWZ n k
  rw [h.finsum_const hF hG n n₀, h₀]

/-- CO-448. Checking the WZ equation at a point `(n,k)` reduces to a rational identity: if
`F(n+1,k) = r₁ F(n,k)` and `F(n,k+1) = r₂ F(n,k)` (`r₁, r₂` the ratios as rational functions),
and `r₁ - 1 = R(n,k+1) r₂ - R(n,k)`, then `(F, R F)` satisfies the WZ equation at `(n,k)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 134"]
theorem wz_eq_of_ratio_identity (F R : ℤ → ℤ → K) (n k : ℤ) (r₁ r₂ : K)
    (h₁ : F (n + 1) k = r₁ * F n k) (h₂ : F n (k + 1) = r₂ * F n k)
    (h : r₁ - 1 = R n (k + 1) * r₂ - R n k) :
    F (n + 1) k - F n k = R n (k + 1) * F n (k + 1) - R n k * F n k := by
  rw [h₁, h₂]
  linear_combination (F n k) * h

/-- CO-448, converse: over a field, when `F(n,k) ≠ 0`, the WZ equation at `(n,k)` is equivalent
to the rational identity for the ratios. -/
theorem wz_eq_iff_ratio_identity {L : Type*} [Field L] (F R : ℤ → ℤ → L) (n k : ℤ) (r₁ r₂ : L)
    (h₁ : F (n + 1) k = r₁ * F n k) (h₂ : F n (k + 1) = r₂ * F n k) (h0 : F n k ≠ 0) :
    F (n + 1) k - F n k = R n (k + 1) * F n (k + 1) - R n k * F n k ↔
      r₁ - 1 = R n (k + 1) * r₂ - R n k := by
  rw [h₁, h₂]
  constructor
  · intro h
    apply mul_right_cancel₀ h0
    linear_combination h
  · intro h
    linear_combination (F n k) * h

/-- CO-448. Global form: if the ratios are given by functions `r₁ r₂` of `(n,k)` and the rational
identity `r₁ - 1 = R(n,k+1) r₂ - R(n,k)` holds everywhere, then `(F, R F)` is a solution of the
WZ equation. -/
theorem wzEq_of_ratio_identity (F R r₁ r₂ : ℤ → ℤ → K)
    (h₁ : ∀ n k, F (n + 1) k = r₁ n k * F n k) (h₂ : ∀ n k, F n (k + 1) = r₂ n k * F n k)
    (h : ∀ n k, r₁ n k - 1 = R n (k + 1) * r₂ n k - R n k) :
    WZEq F (fun n k => R n k * F n k) := fun n k =>
  wz_eq_of_ratio_identity F R n k (r₁ n k) (r₂ n k) (h₁ n k) (h₂ n k) (h n k)

/-- CO-441 / CO-545. Self-certifying recurrences: let `ρ i j` (a rational function of `(n,k)`,
here a value) satisfy `F(n-j,k-i) = ρ i j · F(n,k)`.  Then the `k`-free recurrence
`∑ a_ij(n) F(n-j,k-i) = 0` holds at `(n,k)` as soon as the rational identity
`∑ a_ij(n) ρ_ij = 0` does. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 123"]
theorem recurrence_of_ratio_identity (s : Finset (ℕ × ℕ)) (a : ℕ → ℕ → K) (F : ℤ → ℤ → K)
    (n k : ℤ) (ρ : ℕ → ℕ → K) (hρ : ∀ p ∈ s, F (n - p.2) (k - p.1) = ρ p.1 p.2 * F n k)
    (h : ∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2 = 0) :
    ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = 0 := by
  have : ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = (∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2) * F n k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hρ p hp]; ring
  rw [this, h, zero_mul]

/-- CO-441 / CO-545, converse: over a field, when `F(n,k) ≠ 0`, the recurrence holds at `(n,k)`
if and only if the rational identity holds. -/
theorem recurrence_iff_ratio_identity {L : Type*} [Field L] (s : Finset (ℕ × ℕ))
    (a : ℕ → ℕ → L) (F : ℤ → ℤ → L) (n k : ℤ) (ρ : ℕ → ℕ → L)
    (hρ : ∀ p ∈ s, F (n - p.2) (k - p.1) = ρ p.1 p.2 * F n k) (h0 : F n k ≠ 0) :
    ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = 0 ↔ ∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2 = 0 := by
  have : ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = (∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2) * F n k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hρ p hp]; ring
  rw [this]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_right h0, fun h => by rw [h, zero_mul]⟩

end Proof

section Restricted

variable {K : Type*} [AddCommGroup K]

/-- CO-462. The restricted sum (7.3.8): if `(F, G)` satisfy the WZ equation and `G(n,0) = 0`
for `n ≥ 0` (true when the support of `F(n,·)` contains `[0,n]` and `G` vanishes left of it),
then `∑_{k=0}^n F(n,k) = F(0,0) + ∑_{j=1}^n (F(j,j) + G(j-1,j))`. -/
@[kb "petkovsekwilfzeilberger1996" "(7.3.8), p. 143"]
theorem restricted_sum_formula (F G : ℤ → ℤ → K) (hWZ : WZEq F G)
    (hG0 : ∀ n : ℕ, G n 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), F n k
      = F 0 0 + ∑ j ∈ Finset.range n, (F (j + 1 : ℕ) (j + 1 : ℕ) + G j (j + 1 : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ k ∈ Finset.range (n + 1), (F ((n : ℤ) + 1) k - F n k)
        = G n ((n : ℤ) + 1) - G n 0 := by
      have := Finset.sum_range_sub (fun k : ℕ => G n (k : ℤ)) (n + 1)
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => hWZ n k
    rw [Finset.sum_sub_distrib, hG0] at e
    have e' : ∑ k ∈ Finset.range (n + 1), F ((n : ℤ) + 1) k
        = G n ((n : ℤ) + 1) + ∑ k ∈ Finset.range (n + 1), F n k := by
      rw [sub_zero] at e; rw [← e]; abel
    rw [Finset.sum_range_succ (fun k : ℕ => F ((n + 1 : ℕ) : ℤ) k) (n + 1),
      Finset.sum_range_succ (fun j : ℕ => F ((j + 1 : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ)
        + G (j : ℤ) ((j + 1 : ℕ) : ℤ)) n]
    push_cast at e' ih ⊢
    rw [e', ih]
    abel

end Restricted

section Parameters

variable {K : Type*} [CommRing K] {P : Type*} [AddCommGroup P]

/-- CO-464. A WZ function with free parameters (Gessel's approach): a summand
`F(p, k)`, depending on a parameter point `p` in a group `P` of parameters, such that for every
`p`, the sum over `k` is `1` (with finite support), and for every shift direction `u` of the
parameters there is a WZ mate `G_u` with `F(p+u,k) - F(p,k) = G_u(p,k+1) - G_u(p,k)`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) WZ function, p. 145"]
structure IsWZFunction (F : P → ℤ → K) : Prop where
  finite_support : ∀ p, (Function.support (F p)).Finite
  sum_one : ∀ p, ∑ᶠ k, F p k = 1
  mate : ∀ u : P, ∃ G : P → ℤ → K, ∀ p k, F (p + u) k - F p k = G p (k + 1) - G p k

/-- CO-464. If `F` is a WZ function, replacing the free parameters `p` by `p + n • u`
(shifts by multiples of the running variable `n`) gives a WZ pair `(F(p+n u, k), G_u(p+n u, k))`
whose sum over `k` is `1` for each `n`: all parameters are on an equal footing. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 145"]
theorem IsWZFunction.shift_param {F : P → ℤ → K} (hF : IsWZFunction F) (p u : P) :
    ∃ G : ℤ → ℤ → K, WZEq (fun n k => F (p + n • u) k) G ∧
      (∀ n : ℤ, (Function.support fun k => F (p + n • u) k).Finite) ∧
      ∀ n : ℤ, ∑ᶠ k, F (p + n • u) k = 1 := by
  obtain ⟨G, hG⟩ := hF.mate u
  refine ⟨fun n k => G (p + n • u) k, ?_, fun n => hF.finite_support _, fun n => hF.sum_one _⟩
  intro n k
  have := hG (p + n • u) k
  simp only [add_smul, one_smul, ← add_assoc] at this ⊢
  exact this

end Parameters

end UndergradKB.Combinatorics.AeqB
