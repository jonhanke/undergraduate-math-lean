import UndergradKB.Foundations.DPRM.DavisTheorem
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.PFun

/-!
# Foundations, DPRM: coding finite sequences and the pairing function

* `betaFn c d i = c % (1 + (i + 1) d)`, Gödel's β-function; `beta_exists`: every finite sequence is
  `betaFn c d` on an initial segment (Chinese remainder theorem with the moduli of Davis's theorem);
* `pair_dioph`: Cantor-style pairing `Nat.pair` is a Diophantine function;
* `vec_forall_lt_dioph`: Davis's theorem for sets of vectors (`Vector3`).
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Nat Finset Vector3

local infixr:67 " ::ₒ " => Option.elim'
local infixr:65 " ⊗ " => Sum.elim

/-- Gödel's β-function. -/
def betaFn (c d i : ℕ) : ℕ := c % (1 + (i + 1) * d)

/-- Every finite sequence `s 0, ..., s n` is given by the β-function. -/
theorem beta_exists (n : ℕ) (s : ℕ → ℕ) : ∃ c d, ∀ i ≤ n, betaFn c d i = s i := by
  set Q := n + ∑ i ∈ range (n + 1), s i + 1 with hQ
  set d := Q ! with hd
  set m : ℕ → ℕ := fun i => 1 + (i + 1) * d with hm
  have hco : ((range (n + 1) : Finset ℕ) : Set ℕ).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact coprime_one_add_mul (dvd_refl _) h (by omega)
    · exact (coprime_one_add_mul (dvd_refl _) h (by omega)).symm
  have hm0 : ∀ i ∈ range (n + 1), m i ≠ 0 := fun i _ => by simp [hm]
  let c := Nat.chineseRemainderOfFinset s m (range (n + 1)) hm0 hco
  refine ⟨c, d, fun i hi => ?_⟩
  have h1 : (c : ℕ) ≡ s i [MOD m i] := c.2 i (Finset.mem_range.2 (by omega))
  have hsi : s i < m i := by
    have a1 : s i ≤ ∑ i ∈ range (n + 1), s i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have a2 : Q ≤ d := Nat.self_le_factorial Q
    have a3 : d ≤ (i + 1) * d := Nat.le_mul_of_pos_left _ (Nat.succ_pos i)
    simp only [hm]
    omega
  unfold betaFn
  rw [show 1 + (i + 1) * d = m i from rfl, h1, Nat.mod_eq_of_lt hsi]

variable {α : Type} {f g : (α → ℕ) → ℕ}

theorem betaFn_dioph {h : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) (dh : DiophFn h) :
    DiophFn fun v => betaFn (f v) (g v) (h v) :=
  mod_dioph df (add_dioph (const_dioph 1) (mul_dioph (add_dioph dh (const_dioph 1)) dg))

/-- The pairing function is Diophantine. -/
theorem pair_dioph (df : DiophFn f) (dg : DiophFn g) : DiophFn fun v => Nat.pair (f v) (g v) := by
  have df' : DiophFn fun v : Option α → ℕ => f (v ∘ some) := reindex_diophFn some df
  have dg' : DiophFn fun v : Option α → ℕ => g (v ∘ some) := reindex_diophFn some dg
  have dn : DiophFn fun v : Option α → ℕ => v none := proj_dioph none
  have h1 := (lt_dioph df' dg').inter (eq_dioph dn (add_dioph (mul_dioph dg' dg') df'))
  have h2 := (le_dioph dg' df').inter
    (eq_dioph dn (add_dioph (add_dioph (mul_dioph df' df') df') dg'))
  refine (h1.union h2).ext fun v => ?_
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, Nat.pair]
  split_ifs with h
  · constructor
    · rintro (⟨-, e⟩ | ⟨h', -⟩)
      · exact e.symm
      · omega
    · intro e
      exact Or.inl ⟨h, e.symm⟩
  · constructor
    · rintro (⟨h', -⟩ | ⟨-, e⟩)
      · exact absurd h' h
      · exact e.symm
    · intro e
      exact Or.inr ⟨by omega, e.symm⟩

/-- Davis's theorem for sets of vectors. -/
theorem vec_forall_lt_dioph {n : ℕ} {S : Set (Vector3 ℕ (succ n))} (d : Dioph S)
    {y : Vector3 ℕ n → ℕ} (dy : DiophFn y) :
    Dioph {v : Vector3 ℕ n | ∀ k < y v, (k :: v) ∈ S} :=
  Dioph.ext (dioph_forall_lt (reindex_dioph _ (none :: some) d) dy) fun v =>
    forall_congr' fun k => imp_congr_right fun _ => by
      dsimp
      rw [show Option.elim' k v ∘ cons none some = k :: v from
          funext fun s => by rcases s with a | b <;> rfl]
      exact Iff.rfl

end UndergradKB.Foundations.DPRM
