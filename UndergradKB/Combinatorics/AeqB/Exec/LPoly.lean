import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# Executable polynomials for the algorithms of "A = B" (wave 3)

Mathlib's `Polynomial` is noncomputable, so the algorithms of "A = B" (Gosper, Zeilberger, Sister
Celine, operator arithmetic) cannot be run with it. This file gives a small computable
representation used only as a *data structure for computation*: a polynomial is the list of its
coefficients, `[a₀, a₁, …]` standing for `a₀ + a₁ X + …`. Nothing here replaces a Mathlib notion:
every statement about these lists is a statement about their *values* in a field `K`
(`LPoly.ev`), and the algorithms built on them return certificates whose values are fed to the
noncomputable theorems of the repository (`zeilberger_sound`, …).

The coefficients may themselves be list polynomials: `LPoly (LPoly ℚ)` represents polynomials in
two variables (outer variable `k`, inner variable `n`, as in `K[X][X]` of `Celine.lean`).

* `LPoly.ev f x p = ∑ f(pᵢ) xⁱ`: the value of `p` at `x`, the coefficients being interpreted by `f`.
* `IsSemHom f`: `f` respects `+, *, -, 0, 1` (a ring homomorphism on values).
  `IsSemHom.ev`: then `ev f x` does too, so nesting works.
* `isZeroL`: the computable zero test, sound for every interpretation (`ev_eq_zero_of_isZero`).
* `shift c p` is `p(X + c)` (`ev_shift`).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec

/-- A dense polynomial with coefficients in `R`, as the list of its coefficients (lowest degree
first). Only a data structure for computation; its meaning is given by `LPoly.ev`. -/
structure LPoly (R : Type*) where
  /-- the coefficients, lowest degree first -/
  coeffs : List R
  deriving Repr, Inhabited

/-- A computable zero test on a coefficient type. -/
class ZeroTest (R : Type*) where
  /-- `true` only for elements that are zero (it may be incomplete on non-normalized data). -/
  isZ : R → Bool

instance : ZeroTest ℚ := ⟨fun q => q == 0⟩

namespace LPoly

variable {R : Type*} [Add R] [Mul R] [Neg R] [Zero R] [One R]

/-- Coefficientwise sum of two coefficient lists. -/
def addL : List R → List R → List R
  | [], m => m
  | l, [] => l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Product of two coefficient lists. -/
def mulL : List R → List R → List R
  | [], _ => []
  | a :: l, m => addL (m.map (a * ·)) ((0 : R) :: mulL l m)

instance : Add (LPoly R) := ⟨fun p q => ⟨addL p.coeffs q.coeffs⟩⟩
instance : Mul (LPoly R) := ⟨fun p q => ⟨mulL p.coeffs q.coeffs⟩⟩
instance : Neg (LPoly R) := ⟨fun p => ⟨p.coeffs.map (- ·)⟩⟩
instance : Zero (LPoly R) := ⟨⟨[]⟩⟩
instance : One (LPoly R) := ⟨⟨[1]⟩⟩
instance : Sub (LPoly R) := ⟨fun p q => p + -q⟩

/-- The constant polynomial `a`. -/
def const (a : R) : LPoly R := ⟨[a]⟩

/-- The variable `X`. -/
def X : LPoly R := ⟨[0, 1]⟩

/-- `a · p`. -/
def smul (a : R) (p : LPoly R) : LPoly R := ⟨p.coeffs.map (a * ·)⟩

/-- `p(X + c)`, by Horner's rule. -/
def shiftL (c : R) : List R → LPoly R
  | [] => 0
  | a :: l => const a + ⟨[c, 1]⟩ * shiftL c l

/-- `p(X + c)`. -/
def shift (c : R) (p : LPoly R) : LPoly R := shiftL c p.coeffs

/-- `pᵐ`. -/
def pow (p : LPoly R) : ℕ → LPoly R
  | 0 => 1
  | m + 1 => pow p m * p

/-- Product of a list of polynomials. -/
def prodL (l : List (LPoly R)) : LPoly R := l.foldr (· * ·) 1

/-- Sum of a list of polynomials. -/
def sumL (l : List (LPoly R)) : LPoly R := l.foldr (· + ·) 0

/-- Map the coefficients. -/
def mapC {S : Type*} (g : R → S) (p : LPoly R) : LPoly S := ⟨p.coeffs.map g⟩

/-- The computable zero test: all coefficients pass the zero test of `R`. -/
def isZeroL [ZeroTest R] (p : LPoly R) : Bool := p.coeffs.all ZeroTest.isZ

instance [ZeroTest R] : ZeroTest (LPoly R) := ⟨isZeroL⟩

/-- Remove trailing coefficients that pass the zero test. -/
def trim [ZeroTest R] (p : LPoly R) : LPoly R :=
  ⟨(p.coeffs.reverse.dropWhile ZeroTest.isZ).reverse⟩

/-- Length of the trimmed coefficient list (`degree + 1`, and `0` for the zero polynomial). -/
def len [ZeroTest R] (p : LPoly R) : ℕ := (trim p).coeffs.length

/-- Coefficient of `Xⁱ`. -/
def coeff (p : LPoly R) (i : ℕ) : R := p.coeffs.getD i 0

/-! ### Semantics -/

variable {K : Type*} [CommRing K]

/-- The value of a coefficient list at `x`, coefficients interpreted by `f` (Horner). -/
def evL (f : R → K) (x : K) : List R → K
  | [] => 0
  | a :: l => f a + x * evL f x l

/-- The value of `p` at `x`, coefficients interpreted by `f`. -/
def ev (f : R → K) (x : K) (p : LPoly R) : K := evL f x p.coeffs

/-- `f` respects the operations of `R` (on values). -/
structure IsSemHom (f : R → K) : Prop where
  map_add : ∀ a b, f (a + b) = f a + f b
  map_mul : ∀ a b, f (a * b) = f a * f b
  map_neg : ∀ a, f (-a) = - f a
  map_zero : f 0 = 0
  map_one : f 1 = 1

/-- The zero test of `R` is sound for `f`. -/
def ZeroSound [ZeroTest R] (f : R → K) : Prop := ∀ a, ZeroTest.isZ a = true → f a = 0

variable {f : R → K}

theorem evL_addL (hf : IsSemHom f) (x : K) :
    ∀ l m : List R, evL f x (addL l m) = evL f x l + evL f x m
  | [], m => by simp [addL, evL]
  | a :: l, [] => by simp [addL, evL]
  | a :: l, b :: m => by
    simp only [addL, evL, hf.map_add, evL_addL hf x l m]
    ring

theorem evL_map_mul (hf : IsSemHom f) (x : K) (a : R) :
    ∀ m : List R, evL f x (m.map (a * ·)) = f a * evL f x m
  | [] => by simp [evL]
  | b :: m => by
    simp only [List.map_cons, evL, hf.map_mul, evL_map_mul hf x a m]
    ring

theorem evL_mulL (hf : IsSemHom f) (x : K) :
    ∀ l m : List R, evL f x (mulL l m) = evL f x l * evL f x m
  | [], m => by simp [mulL, evL]
  | a :: l, m => by
    simp only [mulL, evL_addL hf, evL_map_mul hf, evL, hf.map_zero, evL_mulL hf x l m]
    ring

theorem ev_add (hf : IsSemHom f) (x : K) (p q : LPoly R) :
    ev f x (p + q) = ev f x p + ev f x q := evL_addL hf x _ _

theorem ev_mul (hf : IsSemHom f) (x : K) (p q : LPoly R) :
    ev f x (p * q) = ev f x p * ev f x q := evL_mulL hf x _ _

theorem ev_neg (hf : IsSemHom f) (x : K) (p : LPoly R) : ev f x (-p) = - ev f x p := by
  show evL f x (p.coeffs.map (- ·)) = _
  unfold ev
  induction p.coeffs with
  | nil => simp [evL]
  | cons a l ih => simp only [List.map_cons, evL, hf.map_neg, ih]; ring

theorem ev_sub (hf : IsSemHom f) (x : K) (p q : LPoly R) :
    ev f x (p - q) = ev f x p - ev f x q := by
  show ev f x (p + -q) = _
  rw [ev_add hf, ev_neg hf, sub_eq_add_neg]

theorem ev_zero (x : K) : ev f x (0 : LPoly R) = 0 := rfl

theorem ev_one (hf : IsSemHom f) (x : K) : ev f x (1 : LPoly R) = 1 := by
  show f 1 + x * 0 = 1
  rw [hf.map_one]; ring

theorem ev_const (x : K) (a : R) : ev f x (const a) = f a := by
  show f a + x * 0 = f a
  ring

theorem ev_X (hf : IsSemHom f) (x : K) : ev f x (X : LPoly R) = x := by
  show f 0 + x * (f 1 + x * 0) = x
  rw [hf.map_zero, hf.map_one]; ring

theorem ev_smul (hf : IsSemHom f) (x : K) (a : R) (p : LPoly R) :
    ev f x (smul a p) = f a * ev f x p := evL_map_mul hf x a _

theorem ev_shift (hf : IsSemHom f) (x : K) (c : R) (p : LPoly R) :
    ev f x (shift c p) = ev f (x + f c) p := by
  unfold shift ev
  induction p.coeffs with
  | nil => rfl
  | cons a l ih =>
    show ev f x (const a + ⟨[c, 1]⟩ * shiftL c l) = _
    have h1 : ev f x (⟨[c, 1]⟩ : LPoly R) = x + f c := by
      show f c + x * (f 1 + x * 0) = _
      rw [hf.map_one]; ring
    rw [ev_add hf, ev_mul hf, ev_const, h1, show ev f x (shiftL c l) = evL f (x + f c) l from ih]
    rfl

theorem ev_pow (hf : IsSemHom f) (x : K) (p : LPoly R) (m : ℕ) :
    ev f x (pow p m) = ev f x p ^ m := by
  induction m with
  | zero => rw [pow, pow_zero]; exact ev_one hf x
  | succ m ih => rw [pow, ev_mul hf, ih, pow_succ]

theorem ev_prodL (hf : IsSemHom f) (x : K) (l : List (LPoly R)) :
    ev f x (prodL l) = (l.map (ev f x)).prod := by
  unfold prodL
  induction l with
  | nil => exact ev_one hf x
  | cons p l ih => rw [List.foldr_cons, ev_mul hf, ih, List.map_cons, List.prod_cons]

theorem ev_sumL (hf : IsSemHom f) (x : K) (l : List (LPoly R)) :
    ev f x (sumL l) = (l.map (ev f x)).sum := by
  unfold sumL
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.foldr_cons, ev_add hf, ih, List.map_cons, List.sum_cons]

theorem evL_eq_zero_of_all [ZeroTest R] (hz : ZeroSound f) (x : K) :
    ∀ l : List R, l.all ZeroTest.isZ = true → evL f x l = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [evL, hz a h.1, evL_eq_zero_of_all hz x l h.2]
    ring

/-- Soundness of the zero test: a list polynomial passing `isZeroL` has value `0` everywhere. -/
theorem ev_eq_zero_of_isZero [ZeroTest R] (hz : ZeroSound f) (x : K) (p : LPoly R)
    (h : isZeroL p = true) : ev f x p = 0 :=
  evL_eq_zero_of_all hz x _ h

/-- An equality test: `p - q` passes the zero test. Sound by `ev_eq_of_eqTest`. -/
def eqTest [ZeroTest R] (p q : LPoly R) : Bool := isZeroL (p - q)

theorem ev_eq_of_eqTest [ZeroTest R] (hf : IsSemHom f) (hz : ZeroSound f) (x : K) (p q : LPoly R)
    (h : eqTest p q = true) : ev f x p = ev f x q := by
  have := ev_eq_zero_of_isZero hz x _ h
  rw [ev_sub hf] at this
  exact sub_eq_zero.1 this

theorem evL_append_zero_tail [ZeroTest R] (hz : ZeroSound f) (x : K) (l t : List R)
    (ht : t.all ZeroTest.isZ = true) : evL f x (l ++ t) = evL f x l := by
  induction l with
  | nil => exact evL_eq_zero_of_all hz x t ht
  | cons a l ih => simp only [List.cons_append, evL, ih]

theorem ev_trim [ZeroTest R] (hz : ZeroSound f) (x : K) (p : LPoly R) :
    ev f x (trim p) = ev f x p := by
  unfold trim ev
  conv_rhs => rw [← List.reverse_reverse p.coeffs,
    ← List.takeWhile_append_dropWhile (p := ZeroTest.isZ) (l := p.coeffs.reverse)]
  rw [List.reverse_append]
  refine (evL_append_zero_tail hz x _ _ ?_).symm
  rw [List.all_reverse]
  exact List.all_takeWhile

/-- Lifting: if `f` interprets `R`, then `ev f x` interprets `LPoly R`. -/
theorem IsSemHom.ev (hf : IsSemHom f) (x : K) : IsSemHom (ev f x : LPoly R → K) where
  map_add := ev_add hf x
  map_mul := ev_mul hf x
  map_neg := ev_neg hf x
  map_zero := ev_zero x
  map_one := ev_one hf x

theorem ZeroSound.ev [ZeroTest R] (hz : ZeroSound f) (x : K) :
    ZeroSound (ev f x : LPoly R → K) := fun p h => ev_eq_zero_of_isZero hz x p h

end LPoly

/-! ### Rational coefficients -/

section Rat

variable {K : Type*} [Field K] [CharZero K]

theorem isSemHom_ratCast : LPoly.IsSemHom (fun q : ℚ => (q : K)) where
  map_add := fun a b => Rat.cast_add a b
  map_mul := fun a b => Rat.cast_mul a b
  map_neg := fun a => Rat.cast_neg a
  map_zero := Rat.cast_zero
  map_one := Rat.cast_one

theorem zeroSound_ratCast : LPoly.ZeroSound (fun q : ℚ => (q : K)) := by
  intro a h
  have : a = 0 := by simpa [ZeroTest.isZ] using h
  simp [this]

end Rat

/-- Polynomials in one variable `n` over `ℚ`. -/
abbrev QPoly := LPoly ℚ

/-- Polynomials in `n` and `k` over `ℚ`: polynomials in `k` whose coefficients are polynomials
in `n`. -/
abbrev QBi := LPoly QPoly

namespace QBi

variable {K : Type*} [Field K] [CharZero K]

/-- The value of a polynomial in `n` at `n`. -/
def ev1 (p : QPoly) (n : K) : K := LPoly.ev (fun q : ℚ => (q : K)) n p

/-- The value of a polynomial in `n, k` at `(n, k)`. -/
def ev2 (p : QBi) (n k : K) : K := LPoly.ev (fun q : QPoly => ev1 q n) k p

theorem hom1 (n : K) : LPoly.IsSemHom (fun q : QPoly => ev1 q n) :=
  isSemHom_ratCast.ev n

theorem zero1 (n : K) : LPoly.ZeroSound (fun q : QPoly => ev1 q n) :=
  zeroSound_ratCast.ev n

theorem hom2 (n k : K) : LPoly.IsSemHom (fun p : QBi => ev2 p n k) := (hom1 n).ev k

theorem zero2 (n k : K) : LPoly.ZeroSound (fun p : QBi => ev2 p n k) := (zero1 n).ev k

end QBi

end UndergradKB.Combinatorics.AeqB.Exec
