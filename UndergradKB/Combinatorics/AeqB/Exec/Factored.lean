import UndergradKB.Combinatorics.AeqB.Exec.Linear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products of linear forms, shifts, and Gosper's canonical form (executable, wave 3)

The ratios of a proper hypergeometric term (A = B, §4.4) are products of linear forms
`α n + β k + γ` with integer coefficients. This file represents such products (`Fac`), expands
them into executable polynomials (`Fac.toBi`), shifts polynomials in `n` and `k`, and computes
Gosper's canonical form `r/s = p₁(k+1)/p₁(k) · p₂(k)/p₃(k)` (A = B, (5.2.3), (6.3.9)) on the
factor lists. The canonical-form search is not proved correct: the identity it is supposed to
satisfy is re-checked on the output by the certificate checkers.

Evaluation lemmas (`ev2_toBi`, `ev2_shiftN`, `ev2_shiftK`, `ev2_prodRange`, `ev2_sumRange`) are
proved: they are what the soundness proofs use.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec

open LPoly QBi

/-- The linear form `α n + β k + γ` with integer coefficients. -/
structure Lin where
  α : ℤ
  β : ℤ
  γ : ℤ
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A product `c · ∏ ℓᵢ` of linear forms. -/
structure Fac where
  c : ℚ
  fs : List Lin
  deriving Repr, Inhabited

namespace Lin

/-- The linear form as a polynomial in `n, k` (outer variable `k`). -/
def toBi (l : Lin) : QBi := ⟨[⟨[(l.γ : ℚ), (l.α : ℚ)]⟩, ⟨[(l.β : ℚ)]⟩]⟩

/-- `ℓ(n + m, k)`. -/
def shiftN (m : ℤ) (l : Lin) : Lin := ⟨l.α, l.β, l.γ + l.α * m⟩

/-- `ℓ(n, k + m)`. -/
def shiftK (m : ℤ) (l : Lin) : Lin := ⟨l.α, l.β, l.γ + l.β * m⟩

end Lin

namespace Fac

def one : Fac := ⟨1, []⟩

def mul (a b : Fac) : Fac := ⟨a.c * b.c, a.fs ++ b.fs⟩

def shiftN (m : ℤ) (a : Fac) : Fac := ⟨a.c, a.fs.map (Lin.shiftN m)⟩

def shiftK (m : ℤ) (a : Fac) : Fac := ⟨a.c, a.fs.map (Lin.shiftK m)⟩

/-- The product as a polynomial in `n, k`. -/
def toBi (a : Fac) : QBi := const (const a.c) * prodL (a.fs.map Lin.toBi)

/-- `∏_{i < m} a(n + g i, k)` as a factor list. -/
def prodShiftN (a : Fac) (g : ℕ → ℤ) (m : ℕ) : Fac :=
  (List.range m).foldr (fun i acc => mul (shiftN (g i) a) acc) one

end Fac

/-! ### Shifts of polynomials in `n, k` -/

namespace QBi

/-- `p(n + c, k)`. -/
def shiftN (c : ℚ) (p : QBi) : QBi := mapC (LPoly.shift c) p

/-- `p(n, k + c)`. -/
def shiftK (c : ℚ) (p : QBi) : QBi := LPoly.shift (const c) p

/-- A polynomial in `n` as a polynomial in `n, k`. -/
def ofN (p : QPoly) : QBi := const p

/-- Sum of `g i` over `i < m`. -/
def sumRange (m : ℕ) (g : ℕ → QBi) : QBi := sumL ((List.range m).map g)

/-- Product of `g i` over `i < m`. -/
def prodRange (m : ℕ) (g : ℕ → QBi) : QBi := prodL ((List.range m).map g)

variable {K : Type*} [Field K] [CharZero K]

theorem ev1_const (c : ℚ) (n : K) : ev1 (const c) n = c := ev_const n c

theorem ev2_add (p q : QBi) (n k : K) : ev2 (p + q) n k = ev2 p n k + ev2 q n k :=
  (hom2 n k).map_add p q

theorem ev2_sub (p q : QBi) (n k : K) : ev2 (p - q) n k = ev2 p n k - ev2 q n k :=
  ev_sub (hom1 n) k p q

theorem ev2_mul (p q : QBi) (n k : K) : ev2 (p * q) n k = ev2 p n k * ev2 q n k :=
  (hom2 n k).map_mul p q

theorem ev2_ofN (p : QPoly) (n k : K) : ev2 (ofN p) n k = ev1 p n := ev_const k p

theorem ev2_shiftK (c : ℚ) (p : QBi) (n k : K) : ev2 (shiftK c p) n k = ev2 p n (k + c) := by
  unfold ev2 shiftK
  rw [ev_shift (hom1 n), ev1_const]

theorem ev1_shift (c : ℚ) (p : QPoly) (n : K) : ev1 (LPoly.shift c p) n = ev1 p (n + c) :=
  ev_shift isSemHom_ratCast n c p

theorem evL_map_shift (c : ℚ) (n k : K) :
    ∀ l : List QPoly, evL (fun q : QPoly => ev1 q n) k (l.map (LPoly.shift c)) =
      evL (fun q : QPoly => ev1 q (n + c)) k l
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, evL, ev1_shift, evL_map_shift c n k l]

theorem ev2_shiftN (c : ℚ) (p : QBi) (n k : K) : ev2 (shiftN c p) n k = ev2 p (n + c) k :=
  evL_map_shift c n k p.coeffs

theorem ev2_sumRange (m : ℕ) (g : ℕ → QBi) (n k : K) :
    ev2 (sumRange m g) n k = ∑ i ∈ Finset.range m, ev2 (g i) n k := by
  unfold sumRange
  rw [show ev2 (sumL ((List.range m).map g)) n k = _ from ev_sumL (hom1 n) k _]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp [ev2]

theorem ev2_prodRange (m : ℕ) (g : ℕ → QBi) (n k : K) :
    ev2 (prodRange m g) n k = ∏ i ∈ Finset.range m, ev2 (g i) n k := by
  unfold prodRange
  rw [show ev2 (prodL ((List.range m).map g)) n k = _ from ev_prodL (hom1 n) k _]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]
    simp [ev2]

theorem eqTest_sound {p q : QBi} (h : eqTest p q = true) (n k : K) : ev2 p n k = ev2 q n k :=
  ev_eq_of_eqTest (hom1 n) (zero1 n) k p q h

end QBi

section Eval

variable {K : Type*} [Field K] [CharZero K]

theorem Lin.ev2_toBi (l : Lin) (n k : K) : ev2 l.toBi n k = l.α * n + l.β * k + l.γ := by
  simp only [ev2, ev1, toBi, LPoly.ev, evL, Rat.cast_intCast]
  ring

theorem Fac.ev2_toBi (a : Fac) (n k : K) :
    ev2 a.toBi n k = a.c * (a.fs.map fun l : Lin => (l.α * n + l.β * k + l.γ : K)).prod := by
  unfold toBi
  rw [QBi.ev2_mul, show ev2 (const (const a.c)) n k = ev1 (const a.c) n from ev_const k _,
    QBi.ev1_const]
  congr 1
  rw [show ev2 (prodL (a.fs.map Lin.toBi)) n k = _ from ev_prodL (hom1 n) k _, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => Lin.ev2_toBi l n k

end Eval

/-! ### Gosper's canonical form on factor lists (search, not verified) -/

namespace Gosper

/-- If `ℓ'(k) = λ · ℓ(k - j)` for an integer `j ≥ 0`, return `(j, λ)`. -/
def matchShift (l l' : Lin) : Option (ℕ × ℚ) :=
  -- ℓ(k - j) = α n + β k + (γ - β j)
  if l.α * l'.β ≠ l'.α * l.β then none else
  if l.β ≠ 0 then
    let lam : ℚ := (l'.β : ℚ) / l.β
    if lam = 0 then none else
    -- γ' = λ (γ - β j)  ⇒  j = (γ - γ'/λ) / β
    let jq : ℚ := ((l.γ : ℚ) - l'.γ / lam) / l.β
    if jq.den = 1 ∧ 0 ≤ jq.num then some (jq.num.toNat, lam) else none
  else if l'.β ≠ 0 then none
  else
    -- both free of k: proportional?
    if l.α ≠ 0 then
      let lam : ℚ := (l'.α : ℚ) / l.α
      if lam ≠ 0 ∧ (l'.γ : ℚ) = lam * l.γ then some (0, lam) else none
    else if l.γ ≠ 0 then
      let lam : ℚ := (l'.γ : ℚ) / l.γ
      if lam ≠ 0 ∧ l'.α = 0 then some (0, lam) else none
    else none

/-- Remove the element at index `i`. -/
def eraseIdx' {α : Type*} (l : List α) (i : ℕ) : List α := l.eraseIdx i

/-- One reduction step: find `ℓ` in `p₂`, `ℓ'` in `p₃` with `ℓ' = λ ℓ(k - j)`, `j ≥ 0`. -/
def step (p1 p2 p3 : Fac) : Option (Fac × Fac × Fac) := Id.run do
  for i in List.range p2.fs.length do
    for i' in List.range p3.fs.length do
      let l := p2.fs[i]!
      let l' := p3.fs[i']!
      match matchShift l l' with
      | none => pure ()
      | some (j, lam) =>
        let c : List Lin := (List.range j).map fun t => Lin.shiftK (-((t : ℤ) + 1)) l
        return some (⟨p1.c, p1.fs ++ c⟩, ⟨p2.c / lam, eraseIdx' p2.fs i⟩, ⟨p3.c, eraseIdx' p3.fs i'⟩)
  return none

/-- Gosper's canonical form of `r/s` given as factor lists: `(p₁, p₂, p₃)` with
`r · p₁ · p₃ = s · p₁(k+1) · p₂` (re-checked by the certificate checkers). -/
def canonical (r s : Fac) : Fac × Fac × Fac :=
  let rec go (fuel : ℕ) (p1 p2 p3 : Fac) : Fac × Fac × Fac :=
    match fuel with
    | 0 => (p1, p2, p3)
    | fuel + 1 =>
      match step p1 p2 p3 with
      | none => (p1, p2, p3)
      | some (q1, q2, q3) => go fuel q1 q2 q3
  go (r.fs.length + s.fs.length + 1) Fac.one r s

end Gosper

end UndergradKB.Combinatorics.AeqB.Exec
