import UndergradKB.Precalculus.PartialFractions
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 8.6 (forms) -/

namespace UndergradKB.Precalculus.Course

open Polynomial

/-- Stitz-Zeager Exercise 8.6.4: for every numerator `N` of smaller degree than the denominator
`x³ (5x + 9)(3x² + 7x + 9)`, the fraction `N/D` has the form
`A₀/x + A₁/x² + A₂/x³ + B/(5x + 9) + (Ex + F)/(3x² + 7x + 9)` for some real numbers, wherever `D(x) ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 8.6.4, p. 647"]
theorem exer_8_6_4 (N : ℝ[X])
    (hN : N.degree < ((X ^ 3 * (C 5 * X + C 9) * (C 3 * X ^ 2 + C 7 * X + C 9) : ℝ[X])).degree) :
    ∃ A0 A1 A2 B E F : ℝ, ∀ x : ℝ, x ^ 3 * (5 * x + 9) * (3 * x ^ 2 + 7 * x + 9) ≠ 0 →
      N.eval x / (x ^ 3 * (5 * x + 9) * (3 * x ^ 2 + 7 * x + 9)) =
        A0 / x + A1 / x ^ 2 + A2 / x ^ 3 + B / (5 * x + 9) + (E * x + F) / (3 * x ^ 2 + 7 * x + 9) := by
  have hD : (X ^ 3 * (C 5 * X + C 9) * (C 3 * X ^ 2 + C 7 * X + C 9) : ℝ[X]) =
      C 1 * (∏ i ∈ (Finset.univ : Finset (Fin 2)), (C (![1, 5] i) * X + C (![0, 9] i)) ^ (![3, 1] i)) *
        ∏ k ∈ (Finset.univ : Finset Unit),
          (C ((fun _ : Unit => (3 : ℝ)) k) * X ^ 2 + C ((fun _ : Unit => (7 : ℝ)) k) * X +
            C ((fun _ : Unit => (9 : ℝ)) k)) ^ ((fun _ : Unit => 1) k) := by
    simp [Fin.prod_univ_two]
  obtain ⟨A, B', C', h⟩ := partial_fractions_book (ι := Fin 2) (κ := Unit) Finset.univ Finset.univ
    ![1, 5] ![0, 9] ![3, 1] (by intro i _; fin_cases i <;> norm_num) (by intro i _; fin_cases i <;> norm_num)
    (by
      intro i _ i' _ hne
      fin_cases i <;> fin_cases i' <;> simp at hne ⊢ <;> norm_num)
    (fun _ => 3) (fun _ => 7) (fun _ => 9) (fun _ => 1) (by intro k _; norm_num)
    (by intro k _ k' _ hne; exact absurd (Subsingleton.elim k k') hne)
    1 one_ne_zero N _ hD hN
  refine ⟨A 0 ⟨0, by decide⟩, A 0 ⟨1, by decide⟩, A 0 ⟨2, by decide⟩, A 1 ⟨0, by decide⟩,
    B' PUnit.unit 0, C' PUnit.unit 0, fun x hx => ?_⟩
  have hx' := h x (by simpa using hx)
  simp [Fin.sum_univ_succ] at hx'
  change _ = (∑ j : Fin 3, A 0 j / x ^ (j.1 + 1)) + (∑ j : Fin 1, A 1 j / (5 * x + 9)) + _ at hx'
  rw [Fin.sum_univ_three, Fin.sum_univ_one] at hx'
  simpa using hx'

/-- Stitz-Zeager Exercise 8.6.5: for every numerator `N` of smaller degree than the denominator
`(x + 4)⁵ (x² + 1)²` (the book says degree below 9), `N/D` has the form
`A₁/(x+4) + ... + A₅/(x+4)⁵ + (B₁x + C₁)/(x²+1) + (B₂x + C₂)/(x²+1)²`, wherever `D(x) ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 8.6.5, p. 647"]
theorem exer_8_6_5 (N : ℝ[X])
    (hN : N.degree < (((X + C 4) ^ 5 * (X ^ 2 + C 1) ^ 2 : ℝ[X])).degree) :
    ∃ A1 A2 A3 A4 A5 B1 C1 B2 C2 : ℝ, ∀ x : ℝ, (x + 4) ^ 5 * (x ^ 2 + 1) ^ 2 ≠ 0 →
      N.eval x / ((x + 4) ^ 5 * (x ^ 2 + 1) ^ 2) =
        A1 / (x + 4) + A2 / (x + 4) ^ 2 + A3 / (x + 4) ^ 3 + A4 / (x + 4) ^ 4 + A5 / (x + 4) ^ 5 +
          ((B1 * x + C1) / (x ^ 2 + 1) + (B2 * x + C2) / (x ^ 2 + 1) ^ 2) := by
  have hD : (((X + C 4) ^ 5 * (X ^ 2 + C 1) ^ 2 : ℝ[X])) =
      C 1 * (∏ i ∈ (Finset.univ : Finset Unit), (C ((fun _ : Unit => (1 : ℝ)) i) * X + C ((fun _ : Unit => (4 : ℝ)) i)) ^
        ((fun _ : Unit => 5) i)) *
        ∏ k ∈ (Finset.univ : Finset Unit),
          (C ((fun _ : Unit => (1 : ℝ)) k) * X ^ 2 + C ((fun _ : Unit => (0 : ℝ)) k) * X +
            C ((fun _ : Unit => (1 : ℝ)) k)) ^ ((fun _ : Unit => 2) k) := by
    simp
  obtain ⟨A, B', C', h⟩ := partial_fractions_book (ι := Unit) (κ := Unit) Finset.univ Finset.univ
    (fun _ => 1) (fun _ => 4) (fun _ => 5) (by intro i _; norm_num) (by intro i _; norm_num)
    (by intro i _ i' _ hne; exact absurd (Subsingleton.elim i i') hne)
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2) (by intro k _; norm_num)
    (by intro k _ k' _ hne; exact absurd (Subsingleton.elim k k') hne)
    1 one_ne_zero N _ hD hN
  refine ⟨A PUnit.unit 0, A PUnit.unit 1, A PUnit.unit 2, A PUnit.unit 3, A PUnit.unit 4,
    B' PUnit.unit 0, C' PUnit.unit 0, B' PUnit.unit 1, C' PUnit.unit 1, fun x hx => ?_⟩
  have hx' := h x (by simpa using hx)
  simp [Fin.sum_univ_succ] at hx'
  linarith [hx']

/-- Stitz-Zeager Exercise 8.6.6: for every numerator `N` of smaller degree than the denominator
`x (4x - 1)² (x² + 5)(9x² + 16)` (the book says degree below 7), `N/D` has the form
`A/x + B₁/(4x-1) + B₂/(4x-1)² + (Cx + E)/(x²+5) + (Fx + G)/(9x²+16)`, wherever `D(x) ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 8.6.6, p. 647"]
theorem exer_8_6_6 (N : ℝ[X])
    (hN : N.degree < ((X * (C 4 * X - C 1) ^ 2 * ((X ^ 2 + C 5) * (C 9 * X ^ 2 + C 16)) : ℝ[X])).degree) :
    ∃ A B1 B2 C E F G : ℝ, ∀ x : ℝ, x * (4 * x - 1) ^ 2 * ((x ^ 2 + 5) * (9 * x ^ 2 + 16)) ≠ 0 →
      N.eval x / (x * (4 * x - 1) ^ 2 * ((x ^ 2 + 5) * (9 * x ^ 2 + 16))) =
        A / x + (B1 / (4 * x - 1) + B2 / (4 * x - 1) ^ 2) +
          ((C * x + E) / (x ^ 2 + 5) + (F * x + G) / (9 * x ^ 2 + 16)) := by
  have hD : ((X * (C 4 * X - C 1) ^ 2 * ((X ^ 2 + C 5) * (C 9 * X ^ 2 + C 16)) : ℝ[X])) =
      C 1 * (∏ i ∈ (Finset.univ : Finset (Fin 2)), (C (![1, 4] i) * X + C (![0, -1] i)) ^ (![1, 2] i)) *
        ∏ k ∈ (Finset.univ : Finset (Fin 2)),
          (C (![1, 9] k) * X ^ 2 + C (![0, 0] k) * X + C (![5, 16] k)) ^ (![1, 1] k) := by
    simp [Fin.prod_univ_two, sub_eq_add_neg]
  obtain ⟨A, B', C', h⟩ := partial_fractions_book (ι := Fin 2) (κ := Fin 2) Finset.univ Finset.univ
    ![1, 4] ![0, -1] ![1, 2] (by intro i _; fin_cases i <;> norm_num) (by intro i _; fin_cases i <;> norm_num)
    (by
      intro i _ i' _ hne
      fin_cases i <;> fin_cases i' <;> simp at hne ⊢ <;> norm_num)
    ![1, 9] ![0, 0] ![5, 16] ![1, 1] (by intro k _; fin_cases k <;> norm_num)
    (by
      intro k _ k' _ hne
      rintro ⟨c, h1, h2, h3⟩
      fin_cases k <;> fin_cases k' <;>
        first
        | exact absurd rfl hne
        | (norm_num at h1 h3; linarith)
        | (norm_num at h1 h3))
    1 one_ne_zero N _ hD hN
  refine ⟨A 0 ⟨0, by decide⟩, A 1 ⟨0, by decide⟩, A 1 ⟨1, by decide⟩, B' 0 ⟨0, by decide⟩,
    C' 0 ⟨0, by decide⟩, B' 1 ⟨0, by decide⟩, C' 1 ⟨0, by decide⟩, fun x hx => ?_⟩
  have hx' := h x (by simpa [sub_eq_add_neg] using hx)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hx'
  change _ = ((∑ j : Fin 1, A 0 j / (1 * x + 0) ^ (j.1 + 1)) +
      (∑ j : Fin 2, A 1 j / (4 * x + -1) ^ (j.1 + 1))) +
      ((∑ j : Fin 1, (B' 0 j * x + C' 0 j) / (1 * x ^ 2 + 0 * x + 5) ^ (j.1 + 1)) +
      (∑ j : Fin 1, (B' 1 j * x + C' 1 j) / (9 * x ^ 2 + 0 * x + 16) ^ (j.1 + 1))) at hx'
  simp [Fin.sum_univ_succ, sub_eq_add_neg] at hx'
  simpa [sub_eq_add_neg] using hx'

end UndergradKB.Precalculus.Course
