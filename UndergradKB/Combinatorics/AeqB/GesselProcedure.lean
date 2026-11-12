import UndergradKB.Combinatorics.AeqB.WZProof

/-!
# Gessel's procedure for discovering terminating identities ("A = B", §7.4, p. 145-146)

CO-466.  Gessel's procedure: start from a WZ function with free parameters, replace the parameters
by functions of the running variable `n` affine in `n` (this keeps a WZ pair, `IsWZFunction.shift_param`,
CO-464), find the WZ mate by Gosper's algorithm, transpose the pair (CO-465), shift it — by
constants (CO-465) or, as in the book's worked example `F₄(n,k) = F₃(n, k+n-a)`, by a shear
`k ↦ k + n + γ` — so that the new sum terminates, and evaluate the constant at one value of `n`.

The correctness of the procedure is the statement that every step keeps a WZ pair and that a WZ
pair whose two members have finite support in `k` has a sum independent of `n`.  Gosper's
algorithm only *finds* the mate; correctness needs only that the mate satisfies the WZ equation.

* `WZEq.shear`: the shear `(F(n, k+n+γ), G(n, k+n+γ+1) + F(n, k+n+γ))` of a WZ pair is a WZ pair.
* `WZEq.transpose_shift`, `WZEq.transpose_shear`: the transposed pair shifted, or sheared.
* `gessel_procedure`: from a WZ function with free parameters, a parameter point `p` and a
  direction `u`, every transposed and shifted (constant shift or shear) pair whose members have
  finite support gives a sum independent of `n`, so equal to its value at any one `n₀`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB

section Shear

variable {E : Type*} [AddCommGroup E] {F G : ℤ → ℤ → E}

/-- The shear `k ↦ k + n + γ` of a WZ pair is a WZ pair: with `F'(n,k) = F(n, k+n+γ)` the mate is
`G'(n,k) = G(n, k+n+γ+1) + F(n, k+n+γ)`. (This is the step `F₄(n,k) = F₃(n, k+n-a)` of the
book's example.) -/
theorem WZEq.shear (h : WZEq F G) (γ : ℤ) :
    WZEq (fun n k => F n (k + n + γ)) (fun n k => G n (k + n + γ + 1) + F n (k + n + γ)) := by
  intro n k
  have h1 := h n (k + n + γ + 1)
  have e1 : k + (n + 1) + γ = k + n + γ + 1 := by ring
  have e3 : k + 1 + n + γ = k + n + γ + 1 := by ring
  simp only [e1, e3]
  rw [← sub_eq_zero]
  have : F (n + 1) (k + n + γ + 1) - F n (k + n + γ) -
      (G n (k + n + γ + 1 + 1) + F n (k + n + γ + 1) - (G n (k + n + γ + 1) + F n (k + n + γ))) =
      (F (n + 1) (k + n + γ + 1) - F n (k + n + γ + 1)) -
      (G n (k + n + γ + 1 + 1) - G n (k + n + γ + 1)) := by abel
  rw [this, h1, sub_self]

/-- Transposition followed by a constant shift: `(G(k+β, n+α), F(k+β, n+α))` is a WZ pair. -/
theorem WZEq.transpose_shift (h : WZEq F G) (α β : ℤ) :
    WZEq (fun n k => G (k + β) (n + α)) (fun n k => F (k + β) (n + α)) :=
  (h.transpose).shift α β

/-- Transposition followed by a shear: with `F₃(n,k) = G(k,n)`, `G₃(n,k) = F(k,n)` and
`F₄(n,k) = F₃(n, k+n+γ)`, the pair `(F₄, G₃(n, k+n+γ+1) + F₃(n, k+n+γ))` is a WZ pair. -/
theorem WZEq.transpose_shear (h : WZEq F G) (γ : ℤ) :
    WZEq (fun n k => G (k + n + γ) n) (fun n k => F (k + n + γ + 1) n + G (k + n + γ) n) :=
  (h.transpose).shear γ

end Shear

section Procedure

variable {K : Type*} [CommRing K] {P : Type*} [AddCommGroup P]

/-- CO-466. Gessel's procedure is correct.  Let `F₀` be a WZ function with free parameters
(CO-464), `p` a parameter point and `u` a direction; put `F(n,k) = F₀(p + n u, k)` (the parameters
replaced by functions affine in `n`).  Then there is a WZ mate `G` of `F` (the one Gosper's
algorithm finds, if it succeeds), with `∑_k F(n,k) = 1`, such that
* for every constant shift `(α, β)` for which the transposed shifted pair
  `(G(k+β, n+α), F(k+β, n+α))` has finite support in `k`, the new sum `∑_k G(k+β, n+α)` does not
  depend on `n` (so it equals its value at any single `n₀`);
* for every shear `γ` for which the transposed sheared pair
  `(G(k+n+γ, n), F(k+n+γ+1, n) + G(k+n+γ, n))` has finite support in `k`, the new sum
  `∑_k G(k+n+γ, n)` does not depend on `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text p.145-146"]
theorem gessel_procedure {F₀ : P → ℤ → K} (hF₀ : IsWZFunction F₀) (p u : P) :
    ∃ G : ℤ → ℤ → K, WZEq (fun n k => F₀ (p + n • u) k) G ∧
      (∀ n : ℤ, ∑ᶠ k, F₀ (p + n • u) k = 1) ∧
      (∀ α β : ℤ,
        (∀ n, (Function.support fun k => G (k + β) (n + α)).Finite) →
        (∀ n, (Function.support fun k => F₀ (p + (k + β) • u) (n + α)).Finite) →
        ∀ n n₀ : ℤ, ∑ᶠ k, G (k + β) (n + α) = ∑ᶠ k, G (k + β) (n₀ + α)) ∧
      (∀ γ : ℤ,
        (∀ n, (Function.support fun k => G (k + n + γ) n).Finite) →
        (∀ n, (Function.support fun k =>
          F₀ (p + (k + n + γ + 1) • u) n + G (k + n + γ) n).Finite) →
        ∀ n n₀ : ℤ, ∑ᶠ k, G (k + n + γ) n = ∑ᶠ k, G (k + n₀ + γ) n₀) := by
  obtain ⟨G, hG, -, hsum⟩ := hF₀.shift_param p u
  refine ⟨G, hG, hsum, ?_, ?_⟩
  · intro α β h1 h2 n n₀
    exact (hG.transpose_shift α β).finsum_const h1 h2 n n₀
  · intro γ h1 h2 n n₀
    exact (hG.transpose_shear γ).finsum_const h1 h2 n n₀

end Procedure

end UndergradKB.Combinatorics.AeqB
