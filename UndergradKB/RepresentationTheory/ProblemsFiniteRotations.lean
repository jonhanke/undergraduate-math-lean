import UndergradKB.Common.Attr
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! # Problem 3.24: the arithmetic of finite subgroups of `SO(3)`

The pole counting identity for a finite subgroup `G ⊂ SO(3)` of order `n` reads
`2 (1 - 1/n) = ∑_i (1 - 1/m_i)`, the sum over the orbits of poles, where `m_i` is the order of the
stabilizer of a pole of the `i`-th orbit.  Here we solve this equation in integers.
-/

namespace UndergradKB.RepresentationTheory

namespace FiniteRotations

/-- The sorted triples `(a, b, c)` with `1/a + 1/b + 1/c = 1 + 2/n`, `a ≥ 2`. -/
theorem three_orbits (n a b c : ℕ) (hn : 2 ≤ n) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h : (1 : ℚ) / a + 1 / b + 1 / c = 1 + 2 / n) :
    (a = 2 ∧ b = 2 ∧ n = 2 * c) ∨ (a = 2 ∧ b = 3 ∧ c = 3 ∧ n = 12) ∨ (a = 2 ∧ b = 3 ∧ c = 4 ∧ n = 24) ∨
      (a = 2 ∧ b = 3 ∧ c = 5 ∧ n = 60) := by
  have hb : 2 ≤ b := ha.trans hab
  have hc : 2 ≤ c := hb.trans hbc
  have hq : ((n : ℚ)) ≠ 0 := by positivity
  have hE : (n : ℚ) * (b * c + a * c + a * b) = a * b * c * (n + 2) := by
    have ha' : (a : ℚ) ≠ 0 := by positivity
    have hb' : (b : ℚ) ≠ 0 := by positivity
    have hc' : (c : ℚ) ≠ 0 := by positivity
    field_simp at h
    linear_combination h
  have hE' : n * (b * c + a * c + a * b) = a * b * c * (n + 2) := by exact_mod_cast hE
  have hlt : a * b * c < b * c + a * c + a * b := by
    by_contra hcon
    push Not at hcon
    nlinarith [Nat.mul_le_mul_left n hcon]
  have ha2 : a = 2 := by
    by_contra hne
    have : 3 ≤ a := by omega
    nlinarith [Nat.mul_le_mul_right (b * c) this, Nat.mul_le_mul_right c hab,
      Nat.mul_le_mul_right b (hab.trans hbc)]
  subst ha2
  have hb4 : b ≤ 3 := by
    by_contra hne
    have : 4 ≤ b := by omega
    nlinarith [Nat.mul_le_mul_right c this, Nat.mul_le_mul_left b hbc]
  interval_cases b
  · left
    refine ⟨rfl, rfl, ?_⟩
    nlinarith
  · have hc5 : c ≤ 5 := by nlinarith
    interval_cases c
    · right; left; refine ⟨rfl, rfl, rfl, ?_⟩; nlinarith
    · right; right; left; refine ⟨rfl, rfl, rfl, ?_⟩; nlinarith
    · right; right; right; refine ⟨rfl, rfl, rfl, ?_⟩; nlinarith

theorem term_ge_half {m : ℕ} (hm : 2 ≤ m) : (1 : ℚ) / 2 ≤ 1 - 1 / (m : ℚ) := by
  have : (1 : ℚ) / m ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)
  linarith

theorem term_nonneg {m : ℕ} (hm : 2 ≤ m) : (0 : ℚ) ≤ 1 - 1 / (m : ℚ) :=
  (by norm_num : (0 : ℚ) ≤ 1 / 2).trans (term_ge_half hm)

/-- **The arithmetic of Problem 3.24.**  Let `n ≥ 2` and let `l = [m₁ ≤ m₂ ≤ …]` be a sorted list of integers
`mᵢ ≥ 2`, each dividing `n`, with `∑ (1 - 1/mᵢ) = 2 - 2/n`.  Then `l = [n, n]` (cyclic case), or
`l = [2, 2, r]` with `n = 2r` (dihedral case), or `(n, l) = (12, [2,3,3])`, `(24, [2,3,4])` or `(60, [2,3,5])`
(tetrahedral, octahedral, icosahedral cases). -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem rotation_orbit_data (n : ℕ) (hn : 2 ≤ n) (l : List ℕ) (hs : l.Pairwise (· ≤ ·))
    (h2 : ∀ m ∈ l, 2 ≤ m) (hd : ∀ m ∈ l, m ∣ n)
    (h : (l.map fun m : ℕ => (1 : ℚ) - 1 / (m : ℚ)).sum = 2 - 2 / (n : ℚ)) :
    l = [n, n] ∨ (∃ r, n = 2 * r ∧ l = [2, 2, r]) ∨ (n = 12 ∧ l = [2, 3, 3]) ∨ (n = 24 ∧ l = [2, 3, 4]) ∨
      (n = 60 ∧ l = [2, 3, 5]) := by
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < n := by linarith
  have hfrac : (0 : ℚ) < 2 / n := by positivity
  have hfrac2 : 2 / (n : ℚ) ≤ 1 := by rw [div_le_one hnpos]; exact hnq
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp at h; linarith
  · simp at h
    have ha : 2 ≤ a := h2 a (by simp)
    have : (0 : ℚ) < (a : ℚ)⁻¹ := by positivity
    linarith
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    have ha : 2 ≤ a := h2 a (by simp)
    have hb : 2 ≤ b := h2 b (by simp)
    have han : a ≤ n := Nat.le_of_dvd (by omega) (hd a (by simp))
    have hbn : b ≤ n := Nat.le_of_dvd (by omega) (hd b (by simp))
    have h1 : (1 : ℚ) / n ≤ 1 / a := one_div_le_one_div_of_le (by positivity) (by exact_mod_cast han)
    have h3 : (1 : ℚ) / n ≤ 1 / b := one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hbn)
    have e : 2 / (n : ℚ) = 2 * (1 / n) := by ring
    have ea : (1 : ℚ) / a = 1 / n := by linarith
    have eb : (1 : ℚ) / b = 1 / n := by linarith
    have : (a : ℚ) = n := by
      have := congrArg (fun x : ℚ => x⁻¹) ea
      simpa using this
    have : (b : ℚ) = n := by
      have := congrArg (fun x : ℚ => x⁻¹) eb
      simpa using this
    left
    have h4 : a = n := by exact_mod_cast ‹(a : ℚ) = n›
    have h5 : b = n := by exact_mod_cast ‹(b : ℚ) = n›
    rw [h4, h5]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    have ha : 2 ≤ a := h2 a (by simp)
    have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
    have hbc : b ≤ c := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 c (by simp)
    have h' : (1 : ℚ) / a + 1 / b + 1 / c = 1 + 2 / n := by linarith
    rcases three_orbits n a b c hn ha hab hbc h' with ⟨rfl, rfl, hn'⟩ | ⟨rfl, rfl, rfl, hn'⟩ |
      ⟨rfl, rfl, rfl, hn'⟩ | ⟨rfl, rfl, rfl, hn'⟩
    · right; left; exact ⟨c, hn', rfl⟩
    · right; right; left; exact ⟨hn', rfl⟩
    · right; right; right; left; exact ⟨hn', rfl⟩
    · right; right; right; right; exact ⟨hn', rfl⟩
  · exfalso
    simp only [List.map_cons, List.sum_cons] at h
    have ha := term_ge_half (h2 a (by simp))
    have hb := term_ge_half (h2 b (by simp))
    have hc := term_ge_half (h2 c (by simp))
    have hd' := term_ge_half (h2 d (by simp))
    have ht : (0 : ℚ) ≤ (t.map fun m : ℕ => (1 : ℚ) - 1 / (m : ℚ)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      exact term_nonneg (h2 m (by simp [hm]))
    linarith

end FiniteRotations

end UndergradKB.RepresentationTheory
