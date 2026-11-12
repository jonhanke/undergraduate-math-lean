import UndergradKB.Combinatorics.AeqB.Exec.Zeilberger

/-!
# Sister Celine's method, executable (A = B, Chapter 4; wave 3)

Sister Celine's method (A = B §4.3, steps 1–5) looks for a `k`-free recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n-j, k-i) = 0` for a hypergeometric term `F`: divide by `F(n,k)`, so
that every `F(n-j,k-i)/F(n,k)` becomes a rational function of `n, k`; put everything over a common
denominator; equate the coefficients of the powers of `k` in the numerator to zero; solve the
resulting linear system for the `a_{ij}(n)` over `ℚ(n)`.

`celine I Imax Jmax` runs this over `ℚ(n)` for `F` given by its ratios (`ZInput`: the same data as
for Zeilberger's algorithm). It returns a certificate `CCert`: the `a_{ij}(n)`, the common
denominator `D(n,k)` and the cofactors `c_{ij}` with `N_{ij} c_{ij} = D`, where
`F(n-j,k-i) N_{ij} = F(n,k) M_{ij}` is the chain of one-step ratios.

`ccheck I C` re-checks `N_{ij} c_{ij} = D` for all `i, j` and `∑ a_{ij} M_{ij} c_{ij} = 0` as
polynomial identities, computably. **Correctness** (`ccheck_sound`, CO-388): if `ccheck I C = true`,
every `F` with the given ratios satisfies the recurrence at every integer point `(n,k)` with
`D(n,k) ≠ 0`. (The noncomputable version over `ProperHypergeometricData` is `celine_sound`.)
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec

open LPoly QBi Finset

/-- A certificate of Sister Celine's method: orders `I, J`, coefficients `a_{ij}(n)` (index
`i (J+1) + j`), common denominator `D(n,k)`, cofactors `c_{ij}(n,k)` (same indexing). -/
structure CCert where
  I : ℕ
  J : ℕ
  a : List QPoly
  D : QBi
  cof : List QBi
  deriving Repr, Inhabited

namespace ZInput

variable (T : ZInput)

/-- `N_{ij} = ∏_{t<j} s₁(n-t, k-i) ∏_{t<i} r₁(n, k-1-t)`. -/
def cN (i j : ℕ) : QBi :=
  prodRange j (fun t => shiftK (-(i : ℚ)) (shiftN (-(t : ℚ)) T.s1.toBi)) *
    prodRange i (fun t => shiftK (-1 - (t : ℚ)) T.r1.toBi)

/-- `M_{ij} = ∏_{t<j} s₂(n-t, k-i) ∏_{t<i} r₂(n, k-1-t)`, so that
`F(n-j,k-i) N_{ij} = F(n,k) M_{ij}`. -/
def cM (i j : ℕ) : QBi :=
  prodRange j (fun t => shiftK (-(i : ℚ)) (shiftN (-(t : ℚ)) T.s2.toBi)) *
    prodRange i (fun t => shiftK (-1 - (t : ℚ)) T.r2.toBi)

end ZInput

/-- The polynomial `∑_{i,j} a_{ij}(n) M_{ij}(n,k) c_{ij}(n,k)`, which must vanish. -/
def celineSum (T : ZInput) (C : CCert) : QBi :=
  sumRange (C.I + 1) fun i => sumRange (C.J + 1) fun j =>
    ofN (C.a.getD (i * (C.J + 1) + j) 0) * T.cM i j * C.cof.getD (i * (C.J + 1) + j) 0

/-- The computable certificate check of Sister Celine's method. -/
def ccheck (T : ZInput) (C : CCert) : Bool :=
  ((List.range (C.I + 1)).all fun i => (List.range (C.J + 1)).all fun j =>
      eqTest (T.cN i j * C.cof.getD (i * (C.J + 1) + j) 0) C.D) &&
    isZeroL (celineSum T C)

/-! ### The search -/

namespace Celine

/-- Multiset difference of factor lists (`a` minus `b`, by structural equality of forms). -/
def diffL (a b : List Lin) : List Lin := b.foldl (fun acc l => acc.erase l) a

/-- Least common multiple of factor lists (multiset maximum). -/
def lcmL (a b : List Lin) : List Lin := a ++ diffL b a

/-- `N_{ij}` and `M_{ij}` as factor lists. -/
def facN (T : ZInput) (i j : ℕ) : Fac :=
  ((List.range j).map fun t => (T.s1.shiftN (-(t : ℤ))).shiftK (-(i : ℤ))).foldr Fac.mul
    (((List.range i).map fun t => T.r1.shiftK (-1 - (t : ℤ))).foldr Fac.mul Fac.one)

def facM (T : ZInput) (i j : ℕ) : Fac :=
  ((List.range j).map fun t => (T.s2.shiftN (-(t : ℤ))).shiftK (-(i : ℤ))).foldr Fac.mul
    (((List.range i).map fun t => T.r2.shiftK (-1 - (t : ℤ))).foldr Fac.mul Fac.one)

/-- One attempt of Sister Celine's method with orders `I, J`. -/
def celineAt (T : ZInput) (I J : ℕ) : Option CCert :=
  let idx := (List.range (I + 1)).flatMap fun i => (List.range (J + 1)).map fun j => (i, j)
  let Ns := idx.map fun (i, j) => facN T i j
  let Dfs := Ns.foldl (fun acc N => lcmL acc N.fs) []
  let D : QBi := (⟨1, Dfs⟩ : Fac).toBi
  let cofs : List QBi := Ns.map fun N => (⟨1 / N.c, diffL Dfs N.fs⟩ : Fac).toBi
  let cols : List QBi := (idx.zip cofs).map fun ((i, j), c) => T.cM i j * c
  let nrows := (cols.map fun c => c.coeffs.length).foldl max 0
  let rows : List (List QFrac) := (List.range nrows).map fun m =>
    cols.map fun c => QFrac.ofPoly (coeffK c m)
  match Linear.kernel rows cols.length with
  | [] => none
  | v :: _ =>
    let C : CCert := ⟨I, J, Linear.clearDen v, D, cofs⟩
    if ccheck T C then some C else none

end Celine

/-- **Sister Celine's method** (A = B §4.3), executable: tries the orders `(I, J)` with
`I ≤ Imax`, `J ≤ Jmax` (by increasing `I + J`) and returns the first certificate that passes
`ccheck`. -/
@[kb "petkovsekwilfzeilberger1996" "Sister Celine's algorithm, steps 1-5, p. 69"]
def celine (T : ZInput) (Imax Jmax : ℕ) : Option CCert :=
  let pairs := ((List.range (Imax + 1)).flatMap fun I => (List.range (Jmax + 1)).map fun J => (I, J))
  let sorted := (List.range (Imax + Jmax + 1)).flatMap fun s => pairs.filter fun (I, J) => I + J = s
  sorted.findSome? fun (I, J) => if I + J = 0 then none else Celine.celineAt T I J

/-! ### Soundness -/

section Sound

variable {K : Type*} [Field K] [CharZero K]

theorem chain_k (r1 r2 F : ℤ → ℤ → K) (hr : ∀ n k, r2 n k * F n (k + 1) = r1 n k * F n k)
    (n k : ℤ) (i : ℕ) :
    F n (k - i) * ∏ t ∈ range i, r1 n (k - 1 - t) = F n k * ∏ t ∈ range i, r2 n (k - 1 - t) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prod_range_succ, prod_range_succ]
    have h := hr n (k - 1 - i)
    rw [show k - 1 - (i : ℤ) + 1 = k - i by ring] at h
    rw [show k - ((i + 1 : ℕ) : ℤ) = k - 1 - i by push_cast; ring]
    calc F n (k - 1 - i) * ((∏ t ∈ range i, r1 n (k - 1 - t)) * r1 n (k - 1 - i))
        = (r1 n (k - 1 - i) * F n (k - 1 - i)) * ∏ t ∈ range i, r1 n (k - 1 - t) := by ring
      _ = r2 n (k - 1 - i) * (F n (k - i) * ∏ t ∈ range i, r1 n (k - 1 - t)) := by
          rw [← h]; ring
      _ = F n k * ((∏ t ∈ range i, r2 n (k - 1 - t)) * r2 n (k - 1 - i)) := by rw [ih]; ring

theorem chain_n (s1 s2 F : ℤ → ℤ → K) (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k)
    (n k : ℤ) (j : ℕ) :
    F (n - j) k * ∏ t ∈ range j, s1 (n - t) k = F n k * ∏ t ∈ range j, s2 (n - t) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, prod_range_succ]
    have h := hs (n - j) k
    rw [show n - ((j + 1 : ℕ) : ℤ) = n - j - 1 by push_cast; ring]
    calc F (n - j - 1) k * ((∏ t ∈ range j, s1 (n - t) k) * s1 (n - j) k)
        = (s1 (n - j) k * F (n - j - 1) k) * ∏ t ∈ range j, s1 (n - t) k := by ring
      _ = s2 (n - j) k * (F (n - j) k * ∏ t ∈ range j, s1 (n - t) k) := by rw [← h]; ring
      _ = F n k * ((∏ t ∈ range j, s2 (n - t) k) * s2 (n - j) k) := by rw [ih]; ring

theorem val_cN (T : ZInput) (i j : ℕ) (n k : ℤ) :
    val K (T.cN i j) n k = (∏ t ∈ range j, val K T.s1.toBi (n - t) (k - i)) *
      ∏ t ∈ range i, val K T.r1.toBi n (k - 1 - t) := by
  simp only [val, ZInput.cN, ev2_mul, ev2_prodRange, ev2_shiftK, ev2_shiftN]
  push_cast
  congr 1 <;> refine prod_congr rfl fun t _ => by ring_nf

theorem val_cM (T : ZInput) (i j : ℕ) (n k : ℤ) :
    val K (T.cM i j) n k = (∏ t ∈ range j, val K T.s2.toBi (n - t) (k - i)) *
      ∏ t ∈ range i, val K T.r2.toBi n (k - 1 - t) := by
  simp only [val, ZInput.cM, ev2_mul, ev2_prodRange, ev2_shiftK, ev2_shiftN]
  push_cast
  congr 1 <;> refine prod_congr rfl fun t _ => by ring_nf

/-- The chain of ratios: `F(n-j, k-i) N_{ij}(n,k) = F(n,k) M_{ij}(n,k)`. -/
theorem chain (T : ZInput) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val K T.s2.toBi n k * F n k = val K T.s1.toBi n k * F (n - 1) k)
    (hr : ∀ n k, val K T.r2.toBi n k * F n (k + 1) = val K T.r1.toBi n k * F n k)
    (i j : ℕ) (n k : ℤ) :
    F (n - j) (k - i) * val K (T.cN i j) n k = F n k * val K (T.cM i j) n k := by
  rw [val_cN, val_cM]
  have h1 := chain_n (val K T.s1.toBi) (val K T.s2.toBi) F hs n (k - i) j
  have h2 := chain_k (val K T.r1.toBi) (val K T.r2.toBi) F hr n k i
  calc F (n - j) (k - i) * ((∏ t ∈ range j, val K T.s1.toBi (n - t) (k - i)) *
        ∏ t ∈ range i, val K T.r1.toBi n (k - 1 - t))
      = (F (n - j) (k - i) * ∏ t ∈ range j, val K T.s1.toBi (n - t) (k - i)) *
          ∏ t ∈ range i, val K T.r1.toBi n (k - 1 - t) := by ring
    _ = (∏ t ∈ range j, val K T.s2.toBi (n - t) (k - i)) *
          (F n (k - i) * ∏ t ∈ range i, val K T.r1.toBi n (k - 1 - t)) := by rw [h1]; ring
    _ = _ := by rw [h2]; ring

/-- The recurrence coefficient `a_{ij}(n)` of a Celine certificate. -/
def CCert.coef (K : Type*) [Field K] [CharZero K] (C : CCert) (i j : ℕ) (n : ℤ) : K :=
  ev1 (C.a.getD (i * (C.J + 1) + j) 0) (n : K)

/-- CO-388. **Correctness of the executable Sister Celine method.** If the certificate passes the
computable check `ccheck T C`, then every `F` with the ratios of `T` (`s₂ F(n,k) = s₁ F(n-1,k)`
and `r₂ F(n,k+1) = r₁ F(n,k)` at all integer points) satisfies the `k`-free recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n-j, k-i) = 0` at every point `(n,k)` where the common
denominator `D(n,k)` does not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "Sister Celine's algorithm, steps 1-5, p. 69"]
theorem ccheck_sound (T : ZInput) (C : CCert) (h : ccheck T C = true) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val K T.s2.toBi n k * F n k = val K T.s1.toBi n k * F (n - 1) k)
    (hr : ∀ n k, val K T.r2.toBi n k * F n (k + 1) = val K T.r1.toBi n k * F n k)
    (n k : ℤ) (hD : val K C.D n k ≠ 0) :
    ∑ i ∈ range (C.I + 1), ∑ j ∈ range (C.J + 1), C.coef K i j n * F (n - j) (k - i) = 0 := by
  simp only [ccheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hcof, hsum⟩ := h
  have hz : val K (celineSum T C) n k = 0 := ev_eq_zero_of_isZero (zero1 (n : K)) (k : K) _ hsum
  have hc : ∀ i < C.I + 1, ∀ j < C.J + 1,
      val K (T.cN i j) n k * val K (C.cof.getD (i * (C.J + 1) + j) 0) n k = val K C.D n k := by
    intro i hi j hj
    have := eqTest_sound (K := K) (hcof i hi j hj) (n : K) (k : K)
    rw [ev2_mul] at this
    exact this
  refine (mul_right_inj' hD).1 ?_
  rw [mul_zero, ← mul_zero (F n k), ← hz]
  simp only [celineSum, val, ev2_sumRange, mul_sum]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [mem_range] at hi hj
  have hcij := hc i hi j hj
  have hch := chain T F hs hr i j n k
  simp only [val] at hcij hch
  rw [ev2_mul, ev2_mul, ev2_ofN, CCert.coef, ← hcij]
  linear_combination (ev1 (C.a.getD (i * (C.J + 1) + j) 0) (n : K)) *
    ev2 (C.cof.getD (i * (C.J + 1) + j) 0) (n : K) (k : K) * hch

end Sound

end UndergradKB.Combinatorics.AeqB.Exec
