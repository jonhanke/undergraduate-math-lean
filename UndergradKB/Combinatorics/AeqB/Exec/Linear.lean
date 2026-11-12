import UndergradKB.Combinatorics.AeqB.Exec.LPoly

/-!
# Executable linear algebra over `ℚ(n)` (wave 3)

Search routines for the executable algorithms: division with remainder and greatest common divisors
in `ℚ[n]`, rational functions `ℚ(n)` as reduced fractions, and a kernel vector of a matrix over
`ℚ(n)` by Gaussian elimination. These functions are **not** proved correct and need not be: every
algorithm built on them returns a certificate that is re-checked by a computable test whose
soundness is proved (`Exec/Zeilberger.lean`, `Exec/Celine.lean`, `Exec/Operators.lean`). A wrong
answer of the search can only make an algorithm report failure.
-/

namespace UndergradKB.Combinatorics.AeqB.Exec

namespace QPoly

open LPoly

/-- Normal form: trailing zero coefficients removed. -/
def norm (p : QPoly) : QPoly := ⟨(p.coeffs.reverse.dropWhile (· == 0)).reverse⟩

/-- Degree of the normal form (`-1` encoded as `none` for zero). -/
def deg (p : QPoly) : Option ℕ :=
  match (norm p).coeffs.length with
  | 0 => none
  | m + 1 => some m

def isZero (p : QPoly) : Bool := (norm p).coeffs.isEmpty

/-- Leading coefficient (`0` for the zero polynomial). -/
def lead (p : QPoly) : ℚ := (norm p).coeffs.getLastD 0

/-- `c Xᵐ`. -/
def monom (c : ℚ) (m : ℕ) : QPoly := ⟨List.replicate m 0 ++ [c]⟩

/-- Division with remainder by a nonzero polynomial (fuel = degree bound). -/
def divMod (p q : QPoly) : QPoly × QPoly :=
  let q := norm q
  match deg q with
  | none => (0, p)
  | some dq =>
    let lc := lead q
    let rec go (fuel : ℕ) (quo rem : QPoly) : QPoly × QPoly :=
      match fuel with
      | 0 => (quo, rem)
      | fuel + 1 =>
        let rem := norm rem
        match deg rem with
        | none => (quo, rem)
        | some dr =>
          if dr < dq then (quo, rem) else
          let t := monom (lead rem / lc) (dr - dq)
          go fuel (norm (quo + t)) (norm (rem - t * q))
    go (p.coeffs.length + 1) 0 p

/-- Exact quotient (the remainder is dropped). -/
def divExact (p q : QPoly) : QPoly := (divMod p q).1

/-- Monic greatest common divisor (`0` if both are zero). -/
def gcd (p q : QPoly) : QPoly :=
  let rec go (fuel : ℕ) (a b : QPoly) : QPoly :=
    match fuel with
    | 0 => a
    | fuel + 1 => if isZero b then a else go fuel b (divMod a b).2
  let g := norm (go (p.coeffs.length + q.coeffs.length + 2) (norm p) (norm q))
  if isZero g then g else smul (1 / lead g) g

/-- Product of two normal forms, normalized. -/
def mulN (p q : QPoly) : QPoly := norm (p * q)

end QPoly

/-- A rational function in `n` over `ℚ`, as a fraction `num / den` (`den ≠ 0`). -/
structure QFrac where
  num : QPoly
  den : QPoly
  deriving Repr, Inhabited

namespace QFrac

open QPoly

def ofPoly (p : QPoly) : QFrac := ⟨norm p, 1⟩

def zero : QFrac := ⟨0, 1⟩

def isZero (a : QFrac) : Bool := QPoly.isZero a.num

/-- Reduce by the gcd and make the denominator monic. -/
def reduce (a : QFrac) : QFrac :=
  if QPoly.isZero a.num then zero else
  let g := gcd a.num a.den
  let n := divExact a.num g
  let d := divExact a.den g
  let c := lead d
  ⟨norm (LPoly.smul (1 / c) n), norm (LPoly.smul (1 / c) d)⟩

def add (a b : QFrac) : QFrac := reduce ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩
def mul (a b : QFrac) : QFrac := reduce ⟨a.num * b.num, a.den * b.den⟩
def neg (a : QFrac) : QFrac := ⟨-a.num, a.den⟩
def sub (a b : QFrac) : QFrac := add a (neg b)
def inv (a : QFrac) : QFrac := reduce ⟨a.den, a.num⟩
def div (a b : QFrac) : QFrac := mul a (inv b)

end QFrac

namespace Linear

/-- Swap entries `i` and `j` of a list. -/
def swap {α : Type*} [Inhabited α] (l : List α) (i j : ℕ) : List α :=
  (l.set i l[j]!).set j l[i]!

/-- Reduced row echelon form over `ℚ(n)`: returns the reduced rows and the pivot columns. -/
def rref (rows : List (List QFrac)) (ncols : ℕ) : List (List QFrac) × List ℕ := Id.run do
  let mut m := rows
  let mut pivots : List ℕ := []
  let mut r := 0
  for c in List.range ncols do
    if r < m.length then
      -- find a pivot in column c at or below row r
      let mut piv : Option ℕ := none
      for i in List.range m.length do
        if piv.isNone && r ≤ i && !(m[i]!)[c]!.isZero then piv := some i
      match piv with
      | none => pure ()
      | some i =>
        m := swap m r i
        let prow := m[r]!
        let pinv := QFrac.inv prow[c]!
        let prow := prow.map (QFrac.mul pinv)
        m := m.set r prow
        m := (List.range m.length).map fun i' =>
          if i' = r then prow else
            let row := m[i']!
            let f := row[c]!
            if f.isZero then row else
              (List.range ncols).map fun j => QFrac.sub row[j]! (QFrac.mul f prow[j]!)
        pivots := pivots ++ [c]
        r := r + 1
  return (m, pivots)

/-- A basis of the kernel `{v | M v = 0}` over `ℚ(n)` (`M` given by rows with `ncols` columns). -/
def kernel (rows : List (List QFrac)) (ncols : ℕ) : List (List QFrac) :=
  let (m, pivots) := rref rows ncols
  let free := (List.range ncols).filter (fun c => !pivots.contains c)
  free.map fun fc =>
    (List.range ncols).map fun j =>
      if j = fc then ⟨1, 1⟩ else
      match pivots.idxOf? j with
      | some r => QFrac.neg (m[r]!)[fc]!
      | none => QFrac.zero

/-- Clear denominators: multiply a vector over `ℚ(n)` by the product of its distinct
denominators (divided by gcds), giving polynomial entries. -/
def clearDen (v : List QFrac) : List QPoly :=
  let l := v.foldl (fun acc a => QPoly.divExact (QPoly.mulN acc a.den) (QPoly.gcd acc a.den)) 1
  v.map fun a => QPoly.norm (QPoly.divExact (a.num * l) a.den)

end Linear

end UndergradKB.Combinatorics.AeqB.Exec
