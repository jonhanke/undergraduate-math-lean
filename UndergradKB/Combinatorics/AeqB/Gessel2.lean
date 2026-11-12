import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Certificates4
import UndergradKB.Combinatorics.AeqB.Gessel

/-!
# A new `5F4` identity from Dixon's WZ function (A = B, §7.4, p. 136)

CO-467.  The book obtains the terminating identity `5F4(...; 1) = 0` of equation (7.4.1) by
transforming the WZ function of Dixon's identity.  Here we prove it directly.  Writing `m = a + b`
(only this combination enters) and `L = m - 2n - 1`, numerical experiment shows that the summand
is *antisymmetric* under `k ↦ L - k`: the pairs of Pochhammer symbols
`(n+1)_k/(n-m+1)_k`, `(n+c+1)_k/(n-m-c+1)_k`, `(-m)_k/(2n+2)_k`, `(2n-m+1)_k/k!` are, up to the
common sign `(-1)^k`, symmetric under `k ↦ L - k`, while the linear factor
`(2n+1-m+2k)/(2n+1-m)` (the quotient of the parameter pair `n+(3-m)/2`, `n+(1-m)/2`) changes sign.
Hence the sum over `0 ≤ k ≤ L` vanishes.  (The remaining terms `k > L` of the book's sum vanish
because of the numerator parameter `2n-m+1`.)
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

theorem g2_dpoch_add (x : ℝ) (a b : ℕ) : dpoch x (a + b) = dpoch x a * dpoch (x + a) b := by
  induction b with
  | zero => simp [dpoch]
  | succ b ih =>
    show dpoch x ((a + b) + 1) = _
    simp only [dpoch]
    rw [ih]
    push_cast
    ring

theorem g2_dpoch_one (k : ℕ) : dpoch 1 k = (k.factorial : ℝ) := by
  induction k with
  | zero => simp [dpoch]
  | succ k ih =>
    simp only [dpoch, Nat.factorial_succ]
    rw [ih]
    push_cast
    ring

/-- Reflection of a Pochhammer symbol: `(-(u+L-1))_i (u)_{L-i} = (-1)^i (u)_L`. -/
theorem g2_refl (u z : ℝ) (L : ℕ) (hz : z = -(u + L - 1)) :
    ∀ i, i ≤ L → dpoch z i * dpoch u (L - i) = (-1) ^ i * dpoch u L := by
  intro i
  induction i with
  | zero => intro _; simp [dpoch]
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    have e : L - i = (L - (i + 1)) + 1 := by omega
    rw [e] at h
    simp only [dpoch] at h ⊢
    have hc : ((L - (i + 1) : ℕ) : ℝ) = L - i - 1 := by
      rw [Nat.cast_sub hi]; push_cast; ring
    rw [hc] at h
    rw [hz] at h ⊢
    linear_combination (-1) * h

theorem g2_dpoch_ne_of_le (u : ℝ) (L : ℕ) (h : dpoch u L ≠ 0) (j : ℕ) (hj : j ≤ L) :
    dpoch u j ≠ 0 := by
  have e : dpoch u L = dpoch u j * dpoch (u + j) (L - j) := by
    conv_lhs => rw [show L = j + (L - j) by omega]
    exact g2_dpoch_add u j (L - j)
  rw [e] at h
  exact left_ne_zero_of_mul h

/-- The summand of (7.4.1), with the quotient of the parameters `n+(3-m)/2`, `n+(1-m)/2`
written as the linear factor `(2n+1-m+2k)/(2n+1-m)`. -/
noncomputable def g2T (m n : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  dpoch (-(m : ℝ)) k * dpoch ((n : ℝ) + 1) k * dpoch ((n : ℝ) + c + 1) k *
      dpoch (2 * (n : ℝ) - m + 1) k * ((2 * (n : ℝ) + 1 - m + 2 * k) / (2 * (n : ℝ) + 1 - m)) /
    ((k.factorial : ℝ) * dpoch ((n : ℝ) - m - c + 1) k * dpoch ((n : ℝ) - m + 1) k *
      dpoch (2 * (n : ℝ) + 2) k)

noncomputable def g2Q (n : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  dpoch ((n : ℝ) + 1) j * dpoch ((n : ℝ) + c + 1) j /
    (dpoch (2 * (n : ℝ) + 2) j * (j.factorial : ℝ))

noncomputable def g2K (n L : ℕ) (c : ℝ) : ℝ :=
  dpoch (2 * (n : ℝ) + 2) L * (L.factorial : ℝ) / (dpoch ((n : ℝ) + 1) L * dpoch ((n : ℝ) + c + 1) L)

theorem g2_T_eq (n L : ℕ) (c : ℝ) (hc : dpoch ((n : ℝ) + c + 1) L ≠ 0) (hL : 1 ≤ L)
    (i : ℕ) (hi : i ≤ L) :
    g2T (2 * n + 1 + L) n c i =
      ((L - 2 * (i : ℝ)) / L) * (g2Q n c i * g2K n L c * g2Q n c (L - i)) := by
  have hLpos : (L : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    intro h; linarith
  have p1 : NoNegInt ((n : ℝ) + 1) := gs_noNegInt_pos (by positivity)
  have p2 : NoNegInt (2 * (n : ℝ) + 2) := gs_noNegInt_pos (by positivity)
  have p3 : NoNegInt (1 : ℝ) := gs_noNegInt_pos (by norm_num)
  have dn1 := dpoch_ne_zero p1
  have dn2 := dpoch_ne_zero p2
  have dn3 := dpoch_ne_zero p3
  have c_i := g2_dpoch_ne_of_le _ L hc i hi
  have c_li := g2_dpoch_ne_of_le _ L hc (L - i) (by omega)
  have e1 := g2_refl (2 * (n : ℝ) + 2) (-((2 * n + 1 + L : ℕ) : ℝ)) L (by push_cast; ring) i hi
  have e2 := g2_refl 1 (2 * (n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) + 1) L (by push_cast; ring) i hi
  have e3 := g2_refl ((n : ℝ) + c + 1) ((n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) - c + 1) L
    (by push_cast; ring) i hi
  have e4 := g2_refl ((n : ℝ) + 1) ((n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) + 1) L
    (by push_cast; ring) i hi
  rw [g2_dpoch_one (L - i), g2_dpoch_one L] at e2
  have hs : ((-1 : ℝ) ^ i) ≠ 0 := by simp
  have hfi : (i.factorial : ℝ) ≠ 0 := by positivity
  have hfl : (L.factorial : ℝ) ≠ 0 := by positivity
  have hfli : ((L - i).factorial : ℝ) ≠ 0 := by positivity
  have hlin : (2 * (n : ℝ) + 1 - ((2 * n + 1 + L : ℕ) : ℝ)) = -L := by push_cast; ring
  have hlin2 : (2 * (n : ℝ) + 1 - ((2 * n + 1 + L : ℕ) : ℝ) + 2 * i) = 2 * i - L := by
    push_cast; ring
  have hcast : ((L - i : ℕ) : ℝ) = L - i := by rw [Nat.cast_sub hi]
  have d1 := dn1 i
  have d2 := dn2 i
  have d1' := dn1 (L - i)
  have d2' := dn2 (L - i)
  have d1L := dn1 L
  have d2L := dn2 L
  unfold g2T g2Q g2K
  rw [hlin2, hlin]
  generalize (-1 : ℝ) ^ i = s at e1 e2 e3 e4 hs
  generalize dpoch (-((2 * n + 1 + L : ℕ) : ℝ)) i = A1 at e1 ⊢
  generalize dpoch (2 * (n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) + 1) i = A2 at e2 ⊢
  generalize dpoch ((n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) - c + 1) i = A3 at e3 ⊢
  generalize dpoch ((n : ℝ) - ((2 * n + 1 + L : ℕ) : ℝ) + 1) i = A4 at e4 ⊢
  have hA1 : A1 = s * dpoch (2 * (n : ℝ) + 2) L / dpoch (2 * (n : ℝ) + 2) (L - i) := by
    rw [eq_div_iff d2']; exact e1
  have hA2 : A2 = s * (L.factorial : ℝ) / ((L - i).factorial : ℝ) := by
    rw [eq_div_iff hfli]; exact e2
  have hA3 : A3 = s * dpoch ((n : ℝ) + c + 1) L / dpoch ((n : ℝ) + c + 1) (L - i) := by
    rw [eq_div_iff c_li]; exact e3
  have hA4 : A4 = s * dpoch ((n : ℝ) + 1) L / dpoch ((n : ℝ) + 1) (L - i) := by
    rw [eq_div_iff d1']; exact e4
  rw [hA1, hA2, hA3, hA4]
  field_simp
  ring

theorem g2_anti (n L : ℕ) (c : ℝ) (hc : dpoch ((n : ℝ) + c + 1) L ≠ 0) (hL : 1 ≤ L)
    (i : ℕ) (hi : i ≤ L) :
    g2T (2 * n + 1 + L) n c (L - i) = - g2T (2 * n + 1 + L) n c i := by
  rw [g2_T_eq n L c hc hL i hi, g2_T_eq n L c hc hL (L - i) (by omega)]
  have e : L - (L - i) = i := by omega
  rw [e]
  have hcast : ((L - i : ℕ) : ℝ) = L - i := by rw [Nat.cast_sub hi]
  rw [hcast]
  have hLpos : (L : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    intro h; linarith
  field_simp
  ring

/-- CO-467. Equation (7.4.1) of the book (`5F4(...; 1) = 0`, obtained from the WZ function of
Dixon's identity), in the form: for natural numbers `n`, `m` (`m = a + b`, the only combination of
`a`, `b` that occurs) with `2n + 2 ≤ m`, and `c` real,
`∑_{k=0}^{m-2n-1} (-m)_k (n+1)_k (n+c+1)_k (2n-m+1)_k (n+(3-m)/2)_k /
   (k! (n-m-c+1)_k (n-m+1)_k (2n+2)_k (n+(1-m)/2)_k) = 0`,
where the quotient `(n+(3-m)/2)_k/(n+(1-m)/2)_k` is written as the linear factor
`(2n+1-m+2k)/(2n+1-m)` (for odd `m` the symbol `(n+(1-m)/2)_k` itself vanishes, so only this form
is meaningful).  The terms with `k ≥ m - 2n` vanish through the numerator parameter `2n-m+1`, so
the sum is stated over `range (m - 2n)`.  Lean adds the genericity hypotheses `2n + 2 ≤ m`
(for `m = 2n+1` the book's sum is a `0/0` normalisation) and `c + n + 1 + j ≠ 0` for
`j < m - 2n - 1` (so that the denominator `(n-m-c+1)_k` does not vanish).  The proof is by the
antisymmetry `k ↦ m-2n-1-k` of the summand rather than by iterating the WZ certificate. -/
@[kb "petkovsekwilfzeilberger1996" "Eq (7.4.1), p. 136"]
theorem gessel_five_four_zero (m n : ℕ) (c : ℝ) (hm : 2 * n + 2 ≤ m)
    (hc : ∀ j : ℕ, j < m - 2 * n - 1 → (n : ℝ) + c + 1 + j ≠ 0) :
    ∑ k ∈ range (m - 2 * n),
        dpoch (-(m : ℝ)) k * dpoch ((n : ℝ) + 1) k * dpoch ((n : ℝ) + c + 1) k *
            dpoch (2 * (n : ℝ) - m + 1) k *
            ((2 * (n : ℝ) + 1 - m + 2 * k) / (2 * (n : ℝ) + 1 - m)) /
          ((k.factorial : ℝ) * dpoch ((n : ℝ) - m - c + 1) k * dpoch ((n : ℝ) - m + 1) k *
            dpoch (2 * (n : ℝ) + 2) k) = 0 := by
  obtain ⟨L, rfl⟩ : ∃ L, m = 2 * n + 1 + L := ⟨m - (2 * n + 1), by omega⟩
  have hL : 1 ≤ L := by omega
  have hc' : dpoch ((n : ℝ) + c + 1) L ≠ 0 :=
    gs_dpoch_ne _ L (fun i hi => hc i (by omega))
  have e : 2 * n + 1 + L - 2 * n = L + 1 := by omega
  rw [e]
  have key : ∑ k ∈ range (L + 1), g2T (2 * n + 1 + L) n c k = 0 := by
    have h1 := Finset.sum_range_reflect (fun k => g2T (2 * n + 1 + L) n c k) (L + 1)
    have h2 : ∑ j ∈ range (L + 1), g2T (2 * n + 1 + L) n c (L + 1 - 1 - j) =
        ∑ j ∈ range (L + 1), - g2T (2 * n + 1 + L) n c j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have : L + 1 - 1 - j = L - j := by omega
      rw [this]
      exact g2_anti n L c hc' hL j hj'
    rw [h2, Finset.sum_neg_distrib] at h1
    linarith
  exact key

end UndergradKB.Combinatorics.AeqB
