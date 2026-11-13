import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import UndergradKB.Common.Attr

/-!
# Sharkovskii's theorem for odd periods: the spiral structure of a minimal odd cycle

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.4 (`morris2024`).  A purely combinatorial
statement on positions `0, ..., m - 1` of the points of an odd cycle: if the Hamiltonian chain `v` of gaps
(with no forward shortcuts, and only the first and last gap covering the first) is given, the orbit of a point
spirals outwards: the orbit points `X 0, X 1, ..., X (j+1)` always fill an interval of positions whose two
ends are `X j` and `X (j+1)`.
-/

namespace UndergradKB.Topology

/-- The data attached to the permutation `π` of the positions `0, ..., m - 1` of an odd cycle and a
Hamiltonian chain `v` of its gaps (`v 0` the loop gap). -/
structure GapData (m : ℕ) where
  π : ℕ → ℕ
  v : ℕ → ℕ
  hm : 3 ≤ m
  π_lt : ∀ i, i < m → π i < m
  pi_pi_ne : ∀ i, i < m → π (π i) ≠ i
  v_inj : ∀ i j, i < m - 1 → j < m - 1 → v i = v j → i = j
  v_lt : ∀ i, i < m - 1 → v i < m - 1
  hout : ∀ j g, j < m - 1 → g < m - 1 → min (π (v j)) (π (v j + 1)) ≤ g →
    g < max (π (v j)) (π (v j + 1)) → (∃ i, i ≤ j + 1 ∧ v i = g) ∧ (g = v 0 → j = 0 ∨ j = m - 2)
  t2 : v 0 + 1 ≤ π (v 0)
  t3 : π (v 0 + 1) ≤ v 0

namespace GapData

variable {m : ℕ} (D : GapData m)

/-- The gap `v 0` is mapped over exactly itself and one neighbour, so one of its endpoints is mapped to the
other. -/
theorem start : D.π (D.v 0) = D.v 0 + 1 ∨ D.π (D.v 0 + 1) = D.v 0 := by
  have hm := D.hm
  have h0 := D.v_lt 0 (by omega)
  have h1 := D.v_lt 1 (by omega)
  have hv01 : D.v 0 ≠ D.v 1 := fun h => by
    have := D.v_inj 0 1 (by omega) (by omega) h
    omega
  have hpt := D.π_lt (D.v 0) (by omega)
  have hpt1 := D.π_lt (D.v 0 + 1) (by omega)
  have hno := D.pi_pi_ne (D.v 0) (by omega)
  have t2 := D.t2
  have t3 := D.t3
  have hg : ∀ g, D.π (D.v 0 + 1) ≤ g → g < D.π (D.v 0) → g = D.v 0 ∨ g = D.v 1 := by
    intro g h1' h2'
    obtain ⟨⟨i, hi, hvi⟩, -⟩ := D.hout 0 g (by omega) (by omega) (by omega) (by omega)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · left; exact hvi.symm
    · right; exact hvi.symm
  have g1 := hg (D.π (D.v 0 + 1)) le_rfl (by omega)
  by_cases hw : D.π (D.v 0) = D.π (D.v 0 + 1) + 1
  · -- a single gap: a 2-cycle of positions
    exfalso
    have e1 : D.π (D.v 0 + 1) = D.v 0 := by omega
    have e2 : D.π (D.v 0) = D.v 0 + 1 := by omega
    rw [e2] at hno
    exact hno e1
  · have g2 := hg (D.π (D.v 0 + 1) + 1) (by omega) (by omega)
    by_cases hw2 : D.π (D.v 0) = D.π (D.v 0 + 1) + 2
    · omega
    · have g3 := hg (D.π (D.v 0 + 1) + 2) (by omega) (by omega)
      omega

end GapData

/-- The orbit `X` of a position under `π`, starting at an endpoint of the loop gap. -/
structure SpiralData (m : ℕ) extends GapData m where
  X : ℕ → ℕ
  X_succ : ∀ i, X (i + 1) = π (X i)
  X_lt : ∀ i, X i < m
  X_inj : ∀ i j, i < m → j < m → X i = X j → i = j
  X_m : X m = X 0
  X_start : (X 0 = v 0 ∧ π (v 0) = v 0 + 1) ∨ (X 0 = v 0 + 1 ∧ π (v 0 + 1) = v 0)

namespace SpiralData

variable {m : ℕ} (D : SpiralData m)

/-- The spiral invariant after `j + 1` steps. -/
def Inv (j : ℕ) : Prop :=
  ∃ α β, α < β ∧ β = α + j + 1 ∧ β < m ∧
    ((D.X j = α ∧ D.X (j + 1) = β) ∨ (D.X j = β ∧ D.X (j + 1) = α)) ∧
    (∀ i, i ≤ j + 1 → α ≤ D.X i ∧ D.X i ≤ β) ∧
    (∀ p, α ≤ p → p ≤ β → ∃ i, i ≤ j + 1 ∧ D.X i = p) ∧
    (∀ g, (∃ i, i ≤ j ∧ D.v i = g) ↔ (α ≤ g ∧ g < β)) ∧
    (∀ i, 1 ≤ i → i ≤ j → ((D.X (i - 1) = D.v i ∧ D.X (i + 1) = D.v i + 1) ∨
        (D.X (i - 1) = D.v i + 1 ∧ D.X (i + 1) = D.v i))) ∧
    ((D.X 0 < D.X 1 ∧ ∀ i, i ≤ j + 1 → (i % 2 = 0 → D.X i ≤ D.X 0) ∧ (i % 2 = 1 → D.X 1 ≤ D.X i)) ∨
     (D.X 1 < D.X 0 ∧ ∀ i, i ≤ j + 1 → (i % 2 = 0 → D.X 0 ≤ D.X i) ∧ (i % 2 = 1 → D.X i ≤ D.X 1)))

theorem inv_one : D.Inv 1 := by
  have hm := D.hm
  have h0 := D.v_lt 0 (by omega)
  have h1 := D.v_lt 1 (by omega)
  have hv01 : D.v 0 ≠ D.v 1 := fun h => by
    have := D.v_inj 0 1 (by omega) (by omega) h
    omega
  have hpt := D.π_lt (D.v 0) (by omega)
  have hpt1 := D.π_lt (D.v 0 + 1) (by omega)
  have hno := D.pi_pi_ne (D.v 0) (by omega)
  have t2 := D.t2
  have t3 := D.t3
  have x1 : D.X 1 = D.π (D.X 0) := D.X_succ 0
  have x2 : D.X (1 + 1) = D.π (D.X 1) := D.X_succ 1
  have hg : ∀ g, D.π (D.v 0 + 1) ≤ g → g < D.π (D.v 0) → g = D.v 0 ∨ g = D.v 1 := by
    intro g h1' h2'
    obtain ⟨⟨i, hi, hvi⟩, -⟩ := D.hout 0 g (by omega) (by omega) (by omega) (by omega)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · left; exact hvi.symm
    · right; exact hvi.symm
  rcases D.X_start with ⟨hX0, hp⟩ | ⟨hX0, hp⟩
  · -- the orbit goes up first: `X 0 = v 0`, `X 1 = v 0 + 1`, `X 2 = v 0 - 1`
    have hX1 : D.X 1 = D.v 0 + 1 := by rw [x1, hX0, hp]
    have hpa : D.π (D.v 0 + 1) ≠ D.v 0 := by
      intro h
      rw [hp] at hno
      exact hno h
    have g1 := hg (D.π (D.v 0 + 1)) le_rfl (by omega)
    have g2 := hg (D.π (D.v 0 + 1) + 1) (by omega) (by omega)
    have hpa2 : D.π (D.v 0 + 1) + 1 = D.v 0 := by omega
    have hv1 : D.v 1 = D.v 0 - 1 := by omega
    have hX2 : D.X (1 + 1) = D.v 0 - 1 := by rw [x2, hX1]; omega
    refine ⟨D.v 0 - 1, D.v 0 + 1, by omega, by omega, by omega, Or.inr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hX1]
    · rw [hX2]
    · intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · omega
      · omega
      · rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]; omega
    · intro p hp1 hp2
      rcases (show p = D.v 0 - 1 ∨ p = D.v 0 ∨ p = D.v 0 + 1 by omega) with rfl | rfl | rfl
      · exact ⟨2, by omega, by rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]⟩
      · exact ⟨0, by omega, hX0⟩
      · exact ⟨1, by omega, hX1⟩
    · intro g
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> omega
      · intro hg'
        rcases (show g = D.v 0 - 1 ∨ g = D.v 0 by omega) with rfl | rfl
        · exact ⟨1, le_rfl, hv1⟩
        · exact ⟨0, by omega, rfl⟩
    · intro i hi1 hi2
      obtain rfl : i = 1 := by omega
      right
      refine ⟨?_, ?_⟩
      · simp only [Nat.sub_self, hX0]; omega
      · rw [show (1 + 1 : ℕ) = 1 + 1 from rfl, hX2]; omega
    · left
      refine ⟨by omega, fun i hi => ?_⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · omega
      · omega
      · rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]; omega
  · -- the orbit goes down first: `X 0 = v 0 + 1`, `X 1 = v 0`, `X 2 = v 0 + 2`
    have hX1 : D.X 1 = D.v 0 := by rw [x1, hX0, hp]
    have hpa : D.π (D.v 0) ≠ D.v 0 + 1 := by
      intro h
      rw [h] at hno
      exact hno hp
    have g1 := hg (D.π (D.v 0 + 1)) le_rfl (by omega)
    have g2 := hg (D.v 0 + 1) (by omega) (by omega)
    have hle2 : D.π (D.v 0) ≤ D.v 0 + 2 := by
      by_contra hc
      have g3 := hg (D.v 0 + 2) (by omega) (by omega)
      omega
    have hpa2 : D.π (D.v 0) = D.v 0 + 2 := by omega
    have hv1 : D.v 1 = D.v 0 + 1 := by omega
    have hX2 : D.X (1 + 1) = D.v 0 + 2 := by rw [x2, hX1]; omega
    refine ⟨D.v 0, D.v 0 + 2, by omega, by omega, by omega, Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hX1]
    · rw [hX2]
    · intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · omega
      · omega
      · rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]; omega
    · intro p hp1 hp2
      rcases (show p = D.v 0 ∨ p = D.v 0 + 1 ∨ p = D.v 0 + 2 by omega) with rfl | rfl | rfl
      · exact ⟨1, by omega, hX1⟩
      · exact ⟨0, by omega, hX0⟩
      · exact ⟨2, by omega, by rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]⟩
    · intro g
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> omega
      · intro hg'
        rcases (show g = D.v 0 ∨ g = D.v 0 + 1 by omega) with rfl | rfl
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, le_rfl, hv1⟩
    · intro i hi1 hi2
      obtain rfl : i = 1 := by omega
      left
      refine ⟨?_, ?_⟩
      · simp only [Nat.sub_self, hX0]; omega
      · rw [show (1 + 1 : ℕ) = 1 + 1 from rfl, hX2]; omega
    · right
      refine ⟨by omega, fun i hi => ?_⟩
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · omega
      · omega
      · rw [show (2 : ℕ) = 1 + 1 by rfl, hX2]; omega

theorem inv_succ {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j + 3 ≤ m) (h : D.Inv j) : D.Inv (j + 1) := by
  obtain ⟨α, β, hαβ, hβ, hβm, hends, hrange, hcover, hW, hendpts, hdir⟩ := h
  have hm := D.hm
  have hu : D.X (j + 1 + 1) = D.π (D.X (j + 1)) := D.X_succ (j + 1)
  have hum : D.X (j + 1 + 1) < m := D.X_lt _
  have hXj : D.X j = D.π (D.X (j - 1)) := by
    have := D.X_succ (j - 1)
    rwa [show j - 1 + 1 = j by omega] at this
  have hvj := D.v_lt j (by omega)
  have hv0 : α ≤ D.v 0 ∧ D.v 0 < β := (hW (D.v 0)).mp ⟨0, by omega, rfl⟩
  have hv0N := D.v_lt 0 (by omega)
  have hunot : D.X (j + 1 + 1) < α ∨ β < D.X (j + 1 + 1) := by
    by_contra hc
    push Not at hc
    obtain ⟨i, hi, hXi⟩ := hcover _ hc.1 hc.2
    have := D.X_inj i (j + 1 + 1) (by omega) (by omega) hXi
    omega
  have hhull : (D.π (D.v j) = D.X j ∧ D.π (D.v j + 1) = D.X (j + 1 + 1)) ∨
      (D.π (D.v j) = D.X (j + 1 + 1) ∧ D.π (D.v j + 1) = D.X j) := by
    rcases hendpts j hj1 le_rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact hXj.symm
      · rw [← h2]; exact hu.symm
    · right
      refine ⟨?_, ?_⟩
      · rw [← h2]; exact hu.symm
      · rw [← h1]; exact hXj.symm
  have hcovg : ∀ g, g < m - 1 → min (D.X j) (D.X (j + 1 + 1)) ≤ g →
      g < max (D.X j) (D.X (j + 1 + 1)) →
      (∃ i, i ≤ j + 1 ∧ D.v i = g) ∧ (g = D.v 0 → j = 0 ∨ j = m - 2) := by
    intro g hg h1 h2
    apply D.hout j g (by omega) hg
    · rcases hhull with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
    · rcases hhull with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
  have hj3 : ¬ (j = 0 ∨ j = m - 2) := by omega
  rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hunot with hu1 | hu2
    · -- the new point lies just below the block
      obtain ⟨⟨i1, hi1, hv1⟩, -⟩ := hcovg (D.X (j + 1 + 1)) (by omega) (by omega) (by omega)
      obtain ⟨⟨i2, hi2, hv2⟩, -⟩ := hcovg (α - 1) (by omega) (by omega) (by omega)
      have hn1 : ¬ ∃ i, i ≤ j ∧ D.v i = D.X (j + 1 + 1) := fun hh => by
        have := (hW _).mp hh; omega
      have hn2 : ¬ ∃ i, i ≤ j ∧ D.v i = α - 1 := fun hh => by
        have := (hW _).mp hh; omega
      have hi1' : i1 = j + 1 := by
        by_contra hne; exact hn1 ⟨i1, by omega, hv1⟩
      have hi2' : i2 = j + 1 := by
        by_contra hne; exact hn2 ⟨i2, by omega, hv2⟩
      rw [hi1'] at hv1
      rw [hi2'] at hv2
      have huα : D.X (j + 1 + 1) = α - 1 := hv1.symm.trans hv2
      refine ⟨α - 1, β, by omega, by omega, hβm, Or.inr ⟨e2, huα⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hi' : i ≤ j + 1
        · have := hrange i hi'; omega
        · have : i = j + 1 + 1 := by omega
          subst this; omega
      · intro p hp1 hp2
        by_cases hp : p = α - 1
        · exact ⟨j + 1 + 1, le_rfl, by omega⟩
        · obtain ⟨i, hi, hXi⟩ := hcover p (by omega) hp2
          exact ⟨i, by omega, hXi⟩
      · intro g
        constructor
        · rintro ⟨i, hi, hvi⟩
          by_cases hij : i ≤ j
          · have := (hW g).mp ⟨i, hij, hvi⟩; omega
          · have : i = j + 1 := by omega
            subst this; omega
        · rintro ⟨hg1, hg2⟩
          by_cases hg : g = α - 1
          · exact ⟨j + 1, le_rfl, by omega⟩
          · obtain ⟨i, hi, hvi⟩ := (hW g).mpr ⟨by omega, hg2⟩
            exact ⟨i, by omega, hvi⟩
      · intro i hi1 hi2
        by_cases hij : i ≤ j
        · exact hendpts i hi1 hij
        · have : i = j + 1 := by omega
          subst this
          right
          rw [Nat.add_sub_cancel]
          exact ⟨by omega, by omega⟩
      · rcases hdir with ⟨hd0, hd⟩ | ⟨hd0, hd⟩
        · left
          refine ⟨hd0, fun i hi => ?_⟩
          by_cases hi' : i ≤ j + 1
          · exact hd i hi'
          · have : i = j + 1 + 1 := by omega
            subst this
            have d1 := hd j (by omega)
            have d2 := hd (j + 1) le_rfl
            constructor <;> intro hp <;> omega
        · right
          refine ⟨hd0, fun i hi => ?_⟩
          by_cases hi' : i ≤ j + 1
          · exact hd i hi'
          · have : i = j + 1 + 1 := by omega
            subst this
            have d1 := hd j (by omega)
            have d2 := hd (j + 1) le_rfl
            constructor <;> intro hp <;> omega
    · exfalso
      exact hj3 ((hcovg (D.v 0) hv0N (by omega) (by omega)).2 rfl)
  · rcases hunot with hu1 | hu2
    · exfalso
      exact hj3 ((hcovg (D.v 0) hv0N (by omega) (by omega)).2 rfl)
    · -- the new point lies just above the block
      obtain ⟨⟨i1, hi1, hv1⟩, -⟩ := hcovg β (by omega) (by omega) (by omega)
      obtain ⟨⟨i2, hi2, hv2⟩, -⟩ := hcovg (D.X (j + 1 + 1) - 1) (by omega) (by omega) (by omega)
      have hn1 : ¬ ∃ i, i ≤ j ∧ D.v i = β := fun hh => by
        have := (hW _).mp hh; omega
      have hn2 : ¬ ∃ i, i ≤ j ∧ D.v i = D.X (j + 1 + 1) - 1 := fun hh => by
        have := (hW _).mp hh; omega
      have hi1' : i1 = j + 1 := by
        by_contra hne; exact hn1 ⟨i1, by omega, hv1⟩
      have hi2' : i2 = j + 1 := by
        by_contra hne; exact hn2 ⟨i2, by omega, hv2⟩
      rw [hi1'] at hv1
      rw [hi2'] at hv2
      have huβ : D.X (j + 1 + 1) = β + 1 := by omega
      refine ⟨α, β + 1, by omega, by omega, by omega, Or.inl ⟨e2, huβ⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hi' : i ≤ j + 1
        · have := hrange i hi'; omega
        · have : i = j + 1 + 1 := by omega
          subst this; omega
      · intro p hp1 hp2
        by_cases hp : p = β + 1
        · exact ⟨j + 1 + 1, le_rfl, by omega⟩
        · obtain ⟨i, hi, hXi⟩ := hcover p hp1 (by omega)
          exact ⟨i, by omega, hXi⟩
      · intro g
        constructor
        · rintro ⟨i, hi, hvi⟩
          by_cases hij : i ≤ j
          · have := (hW g).mp ⟨i, hij, hvi⟩; omega
          · have : i = j + 1 := by omega
            subst this; omega
        · rintro ⟨hg1, hg2⟩
          by_cases hg : g = β
          · exact ⟨j + 1, le_rfl, by omega⟩
          · obtain ⟨i, hi, hvi⟩ := (hW g).mpr ⟨hg1, by omega⟩
            exact ⟨i, by omega, hvi⟩
      · intro i hi1 hi2
        by_cases hij : i ≤ j
        · exact hendpts i hi1 hij
        · have : i = j + 1 := by omega
          subst this
          left
          rw [Nat.add_sub_cancel]
          exact ⟨by omega, by omega⟩
      · rcases hdir with ⟨hd0, hd⟩ | ⟨hd0, hd⟩
        · left
          refine ⟨hd0, fun i hi => ?_⟩
          by_cases hi' : i ≤ j + 1
          · exact hd i hi'
          · have : i = j + 1 + 1 := by omega
            subst this
            have d1 := hd j (by omega)
            have d2 := hd (j + 1) le_rfl
            constructor <;> intro hp <;> omega
        · right
          refine ⟨hd0, fun i hi => ?_⟩
          by_cases hi' : i ≤ j + 1
          · exact hd i hi'
          · have : i = j + 1 + 1 := by omega
            subst this
            have d1 := hd j (by omega)
            have d2 := hd (j + 1) le_rfl
            constructor <;> intro hp <;> omega

theorem inv_all : ∀ j, 1 ≤ j → j + 1 ≤ m - 1 → D.Inv j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ h2
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact D.inv_one
    · exact D.inv_succ hj (by have := D.hm; omega) (ih hj (by omega))

/-- At the end of the spiral, the last gap `v (m - 2)` is mapped over every gap `v e` with `e` even. -/
theorem final (hodd : m % 2 = 1) {e : ℕ} (he1 : 2 ≤ e) (he2 : e % 2 = 0) (he3 : e + 3 ≤ m) :
    min (D.π (D.v (m - 2))) (D.π (D.v (m - 2) + 1)) ≤ D.v e ∧
      D.v e < max (D.π (D.v (m - 2))) (D.π (D.v (m - 2) + 1)) := by
  have hm := D.hm
  obtain ⟨α, β, hαβ, hβ, hβm, hends, hrange, hcover, hW, hendpts, hdir⟩ :=
    D.inv_all (m - 2) (by omega) (by omega)
  have p1 : D.π (D.X (m - 2 - 1)) = D.X (m - 2) := by
    have := D.X_succ (m - 2 - 1)
    rw [show m - 2 - 1 + 1 = m - 2 by omega] at this
    exact this.symm
  have p2 : D.π (D.X (m - 2 + 1)) = D.X 0 := by
    have := D.X_succ (m - 2 + 1)
    rw [show m - 2 + 1 + 1 = m by omega, D.X_m] at this
    exact this.symm
  have hZ : (D.π (D.v (m - 2)) = D.X (m - 2) ∧ D.π (D.v (m - 2) + 1) = D.X 0) ∨
      (D.π (D.v (m - 2)) = D.X 0 ∧ D.π (D.v (m - 2) + 1) = D.X (m - 2)) := by
    rcases hendpts (m - 2) (by omega) le_rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact p1
      · rw [← h2]; exact p2
    · right
      refine ⟨?_, ?_⟩
      · rw [← h2]; exact p2
      · rw [← h1]; exact p1
  have hve := hendpts e (by omega) (by omega)
  have hr1 := hrange (e - 1) (by omega)
  have hr2 := hrange (e + 1) (by omega)
  have hr3 := hrange (m - 2) (by omega)
  have hr4 := hrange 0 (by omega)
  have hr5 := hrange 1 (by omega)
  rcases hdir with ⟨hd0, hd⟩ | ⟨hd0, hd⟩
  · have d1 := hd (e - 1) (by omega)
    have d2 := hd (e + 1) (by omega)
    have d3 := hd (m - 2) (by omega)
    rcases hZ with ⟨z1, z2⟩ | ⟨z1, z2⟩ <;> rcases hve with ⟨v1, v2⟩ | ⟨v1, v2⟩ <;>
      rcases hends with ⟨n1, n2⟩ | ⟨n1, n2⟩ <;> omega
  · have d1 := hd (e - 1) (by omega)
    have d2 := hd (e + 1) (by omega)
    have d3 := hd (m - 2) (by omega)
    rcases hZ with ⟨z1, z2⟩ | ⟨z1, z2⟩ <;> rcases hve with ⟨v1, v2⟩ | ⟨v1, v2⟩ <;>
      rcases hends with ⟨n1, n2⟩ | ⟨n1, n2⟩ <;> omega

end SpiralData

end UndergradKB.Topology
