import Mathlib.Algebra.BigOperators.Ring.Finset
import UndergradKB.Combinatorics.AeqB.Exec.LPoly

/-!
# Sister Celine's method for q-hypergeometric terms, executable (A = B §4.5; wave 3)

The q-analogue of `Celine.lean`. A q-hypergeometric term `F(n,k)` has ratios that are rational
functions of `q`, `q^n`, `q^k`. We write `q` for the base, `N = q^n`, `K = q^k` and represent
polynomials in `(q, N, K)` by `QTri := LPoly (LPoly (LPoly ℚ))` (outermost variable `K`, then `N`,
innermost `q`); `ev3 p q N K` is the value.

The shifts `k ↦ k+1` and `n ↦ n+1` are `K ↦ qK` and `N ↦ qN` (`shiftKm`, `shiftNm`, both by
`scale`, which multiplies the coefficient of `xⁱ` by `cⁱ`; `ev_scale`). To avoid `q⁻¹` only upward
shifts are used: the recurrence is `∑_{i ≤ I, j ≤ J} a_{ij}(q, q^n) F(n+j, k+i) = 0`.

The data: `s₂ F(n+1,k) = s₁ F(n,k)` and `r₂ F(n,k+1) = r₁ F(n,k)` with `s₁ s₂ r₁ r₂ : QTri`
(`QInput`; Laurent monomials in `q^k` have been multiplied through). The chain of ratios is
`F(n+j,k+i) N_{ij} = F(n,k) M_{ij}` with `N_{ij} = ∏_{t<j} s₂(n+t,k+i) ∏_{t<i} r₂(n,k+t)` and `M_{ij}`
the same with `s₁, r₁`.

`qceline` searches for a certificate `QCCert` (coefficients `a_{ij}` in `q, N`, a common
denominator `D` and cofactors `c_{ij}` with `N_{ij} c_{ij} = D`) by fraction-free Gauss–Jordan
elimination over `ℚ[q][N]`; the search is not proved. `qccheck` re-checks the certificate
computably, and `qccheck_sound` (CO-394) proves that a passing certificate gives the recurrence at
every `(n,k)` with `D(q, q^n, q^k) ≠ 0`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec.Q

open LPoly Finset

/-! ### Generic lemmas on `LPoly` -/

section Generic

variable {R : Type*} [Add R] [Mul R] [Neg R] [Zero R] [One R]
  {K : Type*} [CommRing K] {f : R → K}

/-- Coefficientwise `pwⁱ`-scaling of a coefficient list: the `i`-th coefficient `aᵢ` becomes
`pw cⁱ aᵢ`... precisely `(pw cⁱ) aᵢ`. -/
def scaleL (c : R) : R → List R → List R
  | _, [] => []
  | pw, a :: l => (pw * a) :: scaleL c (pw * c) l

/-- `p(c X)`: multiply the coefficient of `xⁱ` by `cⁱ`. -/
def LPoly.scale (c : R) (p : LPoly R) : LPoly R := ⟨scaleL c 1 p.coeffs⟩

theorem evL_scaleL (hf : IsSemHom f) (x : K) (c : R) :
    ∀ (l : List R) (pw : R), evL f x (scaleL c pw l) = f pw * evL f (x * f c) l
  | [], pw => by simp [scaleL, evL]
  | a :: l, pw => by
    simp only [scaleL, evL, hf.map_mul, evL_scaleL hf x c l (pw * c)]
    ring

/-- `p(cX)` evaluated at `x` is `p` evaluated at `x f(c)`. -/
theorem ev_scale (hf : IsSemHom f) (x : K) (c : R) (p : LPoly R) :
    ev f (x) (LPoly.scale c p) = ev f (x * f c) p := by
  unfold LPoly.scale ev
  rw [evL_scaleL hf, hf.map_one, one_mul]

theorem evL_map_of {S : Type*} {f' : S → K} (g : R → S) (hg : ∀ a, f' (g a) = f a) (x : K) :
    ∀ l : List R, evL f' x (l.map g) = evL f x l
  | [] => rfl
  | a :: l => by simp only [List.map_cons, evL, hg, evL_map_of g hg x l]

end Generic

/-! ### Polynomials in `(q, N, K)` and their values -/

/-- Polynomials in `q`. -/
abbrev P1 := LPoly ℚ
/-- Polynomials in `q, N = qⁿ` (outer variable `N`). -/
abbrev P2 := LPoly P1
/-- Polynomials in `q, N = qⁿ, K = qᵏ` (outermost variable `K`). -/
abbrev QTri := LPoly P2

section Eval

variable {K : Type*} [Field K] [CharZero K]

/-- Value of a polynomial in `q` at `q`. -/
def ev1q (p : P1) (q : K) : K := LPoly.ev (fun c : ℚ => (c : K)) q p
/-- Value of a polynomial in `q, N`. -/
def ev2q (p : P2) (q N : K) : K := LPoly.ev (fun a : P1 => ev1q a q) N p
/-- Value of a polynomial in `q, N, K` at `(q, N, K)`. -/
def ev3 (p : QTri) (q N k : K) : K := LPoly.ev (fun a : P2 => ev2q a q N) k p

theorem hom1q (q : K) : IsSemHom (fun a : P1 => ev1q a q) := isSemHom_ratCast.ev q
theorem hom2q (q N : K) : IsSemHom (fun a : P2 => ev2q a q N) := (hom1q q).ev N
theorem hom3q (q N k : K) : IsSemHom (fun a : QTri => ev3 a q N k) := (hom2q q N).ev k
theorem zero1q (q : K) : ZeroSound (fun a : P1 => ev1q a q) := zeroSound_ratCast.ev q
theorem zero2q (q N : K) : ZeroSound (fun a : P2 => ev2q a q N) := (zero1q q).ev N
theorem zero3q (q N k : K) : ZeroSound (fun a : QTri => ev3 a q N k) := (zero2q q N).ev k

theorem ev3_add (p r : QTri) (q N k : K) : ev3 (p + r) q N k = ev3 p q N k + ev3 r q N k :=
  (hom3q q N k).map_add p r
theorem ev3_mul (p r : QTri) (q N k : K) : ev3 (p * r) q N k = ev3 p q N k * ev3 r q N k :=
  (hom3q q N k).map_mul p r
theorem ev3_sub (p r : QTri) (q N k : K) : ev3 (p - r) q N k = ev3 p q N k - ev3 r q N k :=
  ev_sub (hom2q q N) k p r
theorem ev3_const (a : P2) (q N k : K) : ev3 (const a) q N k = ev2q a q N := ev_const k a

theorem ev3_eqTest {p r : QTri} (h : eqTest p r = true) (q N k : K) :
    ev3 p q N k = ev3 r q N k :=
  ev_eq_of_eqTest (hom2q q N) (zero2q q N) k p r h

/-- Sum of `g i` over `i < m`. -/
def sumR (m : ℕ) (g : ℕ → QTri) : QTri := sumL ((List.range m).map g)
/-- Product of `g i` over `i < m`. -/
def prodR (m : ℕ) (g : ℕ → QTri) : QTri := prodL ((List.range m).map g)

theorem ev3_sumR (m : ℕ) (g : ℕ → QTri) (q N k : K) :
    ev3 (sumR m g) q N k = ∑ i ∈ range m, ev3 (g i) q N k := by
  unfold sumR
  rw [show ev3 (sumL ((List.range m).map g)) q N k = _ from ev_sumL (hom2q q N) k _]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp [ev3]

theorem ev3_prodR (m : ℕ) (g : ℕ → QTri) (q N k : K) :
    ev3 (prodR m g) q N k = ∏ i ∈ range m, ev3 (g i) q N k := by
  unfold prodR
  rw [show ev3 (prodL ((List.range m).map g)) q N k = _ from ev_prodL (hom2q q N) k _]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]
    simp [ev3]

/-! ### The q-shifts -/

/-- `p(q, N, qᵐ K)`: the shift `k ↦ k + m`. -/
def shiftKm (m : ℕ) (p : QTri) : QTri := LPoly.scale (const (pow (X : P1) m)) p

/-- `p(q, qᵐ N, K)`: the shift `n ↦ n + m`. -/
def shiftNm (m : ℕ) (p : QTri) : QTri := mapC (LPoly.scale (pow (X : P1) m)) p

theorem ev1q_pow_X (m : ℕ) (q : K) : ev1q (pow (X : P1) m) q = q ^ m := by
  rw [show ev1q (pow (X : P1) m) q = ev (fun c : ℚ => (c : K)) q (pow X m) from rfl,
    ev_pow isSemHom_ratCast, ev_X isSemHom_ratCast]

theorem ev3_shiftKm (m : ℕ) (p : QTri) (q N k : K) :
    ev3 (shiftKm m p) q N k = ev3 p q N (k * q ^ m) := by
  unfold shiftKm ev3
  rw [ev_scale (hom2q q N), show ev2q (const (pow (X : P1) m)) q N = ev1q _ q from ev_const N _,
    ev1q_pow_X]

theorem ev3_shiftNm (m : ℕ) (p : QTri) (q N k : K) :
    ev3 (shiftNm m p) q N k = ev3 p q (N * q ^ m) k := by
  unfold shiftNm ev3 LPoly.ev
  refine evL_map_of _ (fun a => ?_) k p.coeffs
  show ev2q (LPoly.scale _ a) q N = ev2q a q (N * q ^ m)
  unfold ev2q
  rw [ev_scale (hom1q q), ev1q_pow_X]

/-- The value of `p` at `(q, qⁿ, qᵏ)`. -/
def val (q : K) (p : QTri) (n k : ℤ) : K := ev3 p q (q ^ n) (q ^ k)

theorem val_shiftKm (q : K) (hq : q ≠ 0) (m : ℕ) (p : QTri) (n k : ℤ) :
    val q (shiftKm m p) n k = val q p n (k + m) := by
  simp only [val, ev3_shiftKm]
  rw [zpow_add₀ hq, zpow_natCast]

theorem val_shiftNm (q : K) (hq : q ≠ 0) (m : ℕ) (p : QTri) (n k : ℤ) :
    val q (shiftNm m p) n k = val q p (n + m) k := by
  simp only [val, ev3_shiftNm]
  rw [zpow_add₀ hq, zpow_natCast]

end Eval

/-! ### Input, certificate, check -/

/-- The ratio data of a q-hypergeometric term: `s₂ F(n+1,k) = s₁ F(n,k)` and
`r₂ F(n,k+1) = r₁ F(n,k)`, all polynomials in `(q, q^n, q^k)`. -/
structure QInput where
  s1 : QTri
  s2 : QTri
  r1 : QTri
  r2 : QTri
  deriving Repr, Inhabited

/-- A certificate of the q-Sister-Celine method: orders `I, J`, coefficients `a_{ij}(q, q^n)`
(index `i (J+1) + j`), common denominator `D`, cofactors `c_{ij}` (same indexing). -/
structure QCCert where
  I : ℕ
  J : ℕ
  a : List P2
  D : QTri
  cof : List QTri
  deriving Repr, Inhabited

namespace QInput

variable (T : QInput)

/-- `N_{ij} = ∏_{t<j} s₂(n+t, k+i) ∏_{t<i} r₂(n, k+t)`. -/
def cN (i j : ℕ) : QTri :=
  prodR j (fun t => shiftKm i (shiftNm t T.s2)) * prodR i (fun t => shiftKm t T.r2)

/-- `M_{ij} = ∏_{t<j} s₁(n+t, k+i) ∏_{t<i} r₁(n, k+t)`, so that
`F(n+j,k+i) N_{ij} = F(n,k) M_{ij}`. -/
def cM (i j : ℕ) : QTri :=
  prodR j (fun t => shiftKm i (shiftNm t T.s1)) * prodR i (fun t => shiftKm t T.r1)

end QInput

/-- The polynomial `∑_{i,j} a_{ij} M_{ij} c_{ij}`, which must vanish. -/
def qcSum (T : QInput) (C : QCCert) : QTri :=
  sumR (C.I + 1) fun i => sumR (C.J + 1) fun j =>
    const (C.a.getD (i * (C.J + 1) + j) 0) * T.cM i j * C.cof.getD (i * (C.J + 1) + j) 0

/-- The computable certificate check. -/
def qccheck (T : QInput) (C : QCCert) : Bool :=
  ((List.range (C.I + 1)).all fun i => (List.range (C.J + 1)).all fun j =>
      eqTest (T.cN i j * C.cof.getD (i * (C.J + 1) + j) 0) C.D) &&
    isZeroL (qcSum T C)

/-! ### The search (not verified) -/

namespace QCeline

/-- Normalize coefficient polynomials in `q, N` by dropping trailing zeros. -/
def nz2 (p : P2) : P2 := trim (mapC trim p)

/-- Normalize a polynomial in `q, N, K`. -/
def nz3 (p : QTri) : QTri := trim (mapC nz2 p)

/-- Remove the first element equal (as a polynomial) to `l`. -/
def eraseEq (l : QTri) : List QTri → List QTri
  | [] => []
  | x :: xs => if eqTest x l then xs else x :: eraseEq l xs

/-- Multiset difference. -/
def diffL (a b : List QTri) : List QTri := b.foldl (fun acc l => eraseEq l acc) a

/-- Least common multiple of factor lists (multiset maximum). -/
def lcmL (a b : List QTri) : List QTri := a ++ diffL b a

/-- The factors of `N_{ij}`. -/
def facN (T : QInput) (i j : ℕ) : List QTri :=
  (List.range j).map (fun t => nz3 (shiftKm i (shiftNm t T.s2))) ++
    (List.range i).map fun t => nz3 (shiftKm t T.r2)

/-- A row of the (fraction-free) elimination. -/
abbrev Row := List P2

/-- Entry `c` of a row. -/
def entry (r : Row) (c : ℕ) : P2 := r.getD c 0

/-- Not (certainly) zero. -/
def nzr (p : P2) : Bool := !isZeroL p

/-- Exact polynomial division (assumes `d ∣ p`), by long division on highest-first lists;
`dv` divides coefficients exactly. -/
def divStepL {R : Type*} [Sub R] [Mul R] (dv : R → R → R) :
    ℕ → List R → List R → List R
  | 0, _, _ => []
  | fuel + 1, pl, dl =>
    match pl, dl with
    | a :: pt, b :: dt =>
      let c := dv a b
      let pt' := (pt.take dt.length).zipWith (fun x y => x - c * y) dt ++ pt.drop dt.length
      if pt'.length < dt.length + 1 then [c] else c :: divStepL dv fuel pt' (b :: dt)
    | _, _ => []

/-- Exact division in `LPoly R` (`d ≠ 0`, `d ∣ p`). -/
def divExactL {R : Type*} [Add R] [Mul R] [Neg R] [Zero R] [One R] [Sub R] [ZeroTest R]
    (dv : R → R → R) (p d : LPoly R) : LPoly R :=
  let pl := (trim p).coeffs.reverse
  let dl := (trim d).coeffs.reverse
  if pl.length < dl.length ∨ dl.isEmpty then 0 else
    ⟨(divStepL dv (pl.length + 1) pl dl).reverse⟩

/-- Exact division in `ℚ[q]`. -/
def div1 (p d : P1) : P1 := divExactL (fun x y : ℚ => x / y) p d

/-- Exact division in `ℚ[q][N]`. -/
def div2 (p d : P2) : P2 := nz2 (divExactL div1 (nz2 p) (nz2 d))

/-- Bareiss step: `(π · rᵢ - a · r_p) / prev`, entrywise. -/
def rowOp (prev pi a : P2) (ri rp : Row) : Row :=
  (ri.zip rp).map fun x => div2 (pi * x.1 - a * x.2) prev

/-- State of the fraction-free Gauss–Jordan elimination (`prev` is the previous pivot). -/
structure GJ where
  piv : List (ℕ × Row)
  rest : List Row
  free : List ℕ
  prev : P2

/-- Eliminate column `c` from all other rows (Bareiss). -/
def gjStep (st : GJ) (c : ℕ) : GJ :=
  let idx := st.rest.findIdx fun r => nzr (entry r c)
  if idx < st.rest.length then
    let p := st.rest.getD idx []
    let pi := entry p c
    let upd : Row → Row := fun r => rowOp st.prev pi (entry r c) r p
    { piv := st.piv.map (fun x => (x.1, upd x.2)) ++ [(c, p)]
      rest := (st.rest.eraseIdx idx).map upd
      free := st.free
      prev := pi }
  else { st with free := st.free ++ [c] }

/-- Number of leading zero coefficients. -/
def lowDeg {R : Type*} [ZeroTest R] (l : List R) : ℕ := l.findIdx fun x => !ZeroTest.isZ x

/-- Divide a vector by the largest monomial `q^a N^b` dividing all its entries. -/
def stripMon (v : List P2) : List P2 :=
  let vs := v.filter nzr
  let nbs : List ℕ := vs.map fun p => lowDeg p.coeffs
  let nb := nbs.foldl min (nbs.headD 0)
  let qas : List ℕ := vs.flatMap fun p =>
    (p.coeffs.filter fun c => nzr ⟨[c]⟩).map fun c => lowDeg c.coeffs
  let qa := qas.foldl min (qas.headD 0)
  v.map fun p => nz2 ⟨(p.coeffs.drop nb).map fun c => (⟨c.coeffs.drop qa⟩ : P1)⟩

/-- A nonzero kernel vector of the matrix with the given rows (over `ℚ[q][N]`, unreduced). -/
def kernelVec (rows : List Row) (m : ℕ) : Option (List P2) :=
  let st := (List.range m).foldl gjStep ⟨[], rows, [], 1⟩
  match st.free with
  | [] => none
  | f0 :: _ =>
    -- after Bareiss–Jordan every pivot entry equals the last pivot `st.prev`
    some <| stripMon <| (List.range m).map fun c =>
      if c == f0 then nz2 st.prev else
        match st.piv.find? fun x => x.1 == c with
        | some x => nz2 (-(entry x.2 f0))
        | none => 0

/-- The index pairs `(i, j)` in the order `i (J+1) + j`. -/
def idxList (I J : ℕ) : List (ℕ × ℕ) :=
  (List.range (I + 1)).flatMap fun i => (List.range (J + 1)).map fun j => (i, j)

/-- Common denominator (product of the lcm of the factor lists of the `N_{ij}`) and cofactors. -/
def denCof (T : QInput) (I J : ℕ) : QTri × List QTri :=
  let Ns := (idxList I J).map fun (i, j) => facN T i j
  let Dfs := Ns.foldl lcmL []
  (nz3 (prodL Dfs), Ns.map fun N => nz3 (prodL (diffL Dfs N)))

/-- The certificate with coefficient vector `v` (used by the search and by the demos). -/
def certOf (T : QInput) (I J : ℕ) (v : List P2) : QCCert :=
  ⟨I, J, v, (denCof T I J).1, (denCof T I J).2⟩

/-- One attempt with orders `I, J`. -/
def qcelineAt (T : QInput) (I J : ℕ) : Option QCCert :=
  let idx := idxList I J
  let D := (denCof T I J).1
  let cofs := (denCof T I J).2
  let cols : List QTri := (idx.zip cofs).map fun ((i, j), c) => nz3 (T.cM i j * c)
  let nrows := (cols.map fun c => c.coeffs.length).foldl max 0
  let rows : List Row := (List.range nrows).map fun m => cols.map fun c => c.coeffs.getD m 0
  match kernelVec rows cols.length with
  | none => none
  | some v =>
    let C : QCCert := ⟨I, J, v, D, cofs⟩
    if qccheck T C then some C else none

end QCeline

/-- CO-394. **q-Sister-Celine method** (A = B §4.5), executable: tries the orders `(I, J)` with
`I ≤ Imax`, `J ≤ Jmax` (by increasing `I + J`) and returns the first certificate that passes
`qccheck`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.2 (q-Sister Celine), p. 81"]
def qceline (T : QInput) (Imax Jmax : ℕ) : Option QCCert :=
  let pairs := ((List.range (Imax + 1)).flatMap fun I => (List.range (Jmax + 1)).map fun J => (I, J))
  let sorted := (List.range (Imax + Jmax + 1)).flatMap fun s => pairs.filter fun (I, J) => I + J = s
  sorted.findSome? fun (I, J) => if I + J = 0 then none else QCeline.qcelineAt T I J

/-! ### Soundness -/

section Sound

variable {K : Type*} [Field K] [CharZero K]

theorem chain_k (r1 r2 F : ℤ → ℤ → K) (hr : ∀ n k, r2 n k * F n (k + 1) = r1 n k * F n k)
    (n k : ℤ) (i : ℕ) :
    F n (k + i) * ∏ t ∈ range i, r2 n (k + t) = F n k * ∏ t ∈ range i, r1 n (k + t) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prod_range_succ, prod_range_succ]
    have h := hr n (k + i)
    rw [show k + ((i + 1 : ℕ) : ℤ) = k + i + 1 by push_cast; ring]
    linear_combination (∏ t ∈ range i, r2 n (k + t)) * h + r1 n (k + i) * ih

theorem chain_n (s1 s2 F : ℤ → ℤ → K) (hs : ∀ n k, s2 n k * F (n + 1) k = s1 n k * F n k)
    (n k : ℤ) (j : ℕ) :
    F (n + j) k * ∏ t ∈ range j, s2 (n + t) k = F n k * ∏ t ∈ range j, s1 (n + t) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, prod_range_succ]
    have h := hs (n + j) k
    rw [show n + ((j + 1 : ℕ) : ℤ) = n + j + 1 by push_cast; ring]
    linear_combination (∏ t ∈ range j, s2 (n + t) k) * h + s1 (n + j) k * ih

variable (q : K) (hq : q ≠ 0)
include hq

theorem val_cN (T : QInput) (i j : ℕ) (n k : ℤ) :
    val q (T.cN i j) n k = (∏ t ∈ range j, val q T.s2 (n + t) (k + i)) *
      ∏ t ∈ range i, val q T.r2 n (k + t) := by
  simp only [QInput.cN, val, ev3_mul, ev3_prodR]
  congr 1
  · refine prod_congr rfl fun t _ => ?_
    have := val_shiftKm q hq i (shiftNm t T.s2) n k
    rw [val_shiftNm q hq] at this
    exact this
  · refine prod_congr rfl fun t _ => ?_
    exact val_shiftKm q hq t T.r2 n k

theorem val_cM (T : QInput) (i j : ℕ) (n k : ℤ) :
    val q (T.cM i j) n k = (∏ t ∈ range j, val q T.s1 (n + t) (k + i)) *
      ∏ t ∈ range i, val q T.r1 n (k + t) := by
  simp only [QInput.cM, val, ev3_mul, ev3_prodR]
  congr 1
  · refine prod_congr rfl fun t _ => ?_
    have := val_shiftKm q hq i (shiftNm t T.s1) n k
    rw [val_shiftNm q hq] at this
    exact this
  · refine prod_congr rfl fun t _ => ?_
    exact val_shiftKm q hq t T.r1 n k

/-- The chain of ratios: `F(n+j, k+i) N_{ij}(q^n, q^k) = F(n,k) M_{ij}(q^n, q^k)`. -/
theorem qchain (T : QInput) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val q T.s2 n k * F (n + 1) k = val q T.s1 n k * F n k)
    (hr : ∀ n k, val q T.r2 n k * F n (k + 1) = val q T.r1 n k * F n k)
    (i j : ℕ) (n k : ℤ) :
    F (n + j) (k + i) * val q (T.cN i j) n k = F n k * val q (T.cM i j) n k := by
  rw [val_cN q hq, val_cM q hq]
  have h1 := chain_n (val q T.s1) (val q T.s2) F hs n (k + i) j
  have h2 := chain_k (val q T.r1) (val q T.r2) F hr n k i
  linear_combination (∏ t ∈ range i, val q T.r2 n (k + t)) * h1 +
    (∏ t ∈ range j, val q T.s1 (n + t) (k + i)) * h2

/-- The recurrence coefficient `a_{ij}(q, q^n)` of a certificate. -/
def QCCert.coef (C : QCCert) (i j : ℕ) (n : ℤ) : K :=
  ev2q (C.a.getD (i * (C.J + 1) + j) 0) q (q ^ n)

/-- CO-394. **Correctness of the executable q-Sister-Celine method.** Let `K` be a field of
characteristic `0`, `q ∈ K` nonzero. If the certificate passes the computable check
`qccheck T C`, then every `F : ℤ → ℤ → K` with the ratios of `T`
(`s₂ F(n+1,k) = s₁ F(n,k)` and `r₂ F(n,k+1) = r₁ F(n,k)`, the polynomials evaluated at
`(q, q^n, q^k)`, at all integer points) satisfies the `k`-free recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(q, q^n) F(n+j, k+i) = 0` at every `(n,k)` where the common denominator
`D(q, q^n, q^k)` does not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.2 (q-Sister Celine), p. 81"]
theorem qccheck_sound (T : QInput) (C : QCCert) (h : qccheck T C = true) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val q T.s2 n k * F (n + 1) k = val q T.s1 n k * F n k)
    (hr : ∀ n k, val q T.r2 n k * F n (k + 1) = val q T.r1 n k * F n k)
    (n k : ℤ) (hD : val q C.D n k ≠ 0) :
    ∑ i ∈ range (C.I + 1), ∑ j ∈ range (C.J + 1), C.coef q i j n * F (n + j) (k + i) = 0 := by
  simp only [qccheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hcof, hsum⟩ := h
  have hz : val q (qcSum T C) n k = 0 :=
    ev_eq_zero_of_isZero (zero2q q (q ^ n)) (q ^ k) _ hsum
  have hc : ∀ i < C.I + 1, ∀ j < C.J + 1,
      val q (T.cN i j) n k * val q (C.cof.getD (i * (C.J + 1) + j) 0) n k = val q C.D n k := by
    intro i hi j hj
    have := ev3_eqTest (K := K) (hcof i hi j hj) q (q ^ n) (q ^ k)
    rw [ev3_mul] at this
    exact this
  refine (mul_right_inj' hD).1 ?_
  rw [mul_zero, ← mul_zero (F n k), ← hz]
  simp only [qcSum, val, ev3_sumR, mul_sum]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [mem_range] at hi hj
  have hcij := hc i hi j hj
  have hch := qchain q hq T F hs hr i j n k
  simp only [val] at hcij hch
  rw [ev3_mul, ev3_mul, ev3_const, QCCert.coef, ← hcij]
  linear_combination (ev2q (C.a.getD (i * (C.J + 1) + j) 0) q (q ^ n)) *
    ev3 (C.cof.getD (i * (C.J + 1) + j) 0) q (q ^ n) (q ^ k) * hch

end Sound

/-! ### Demo: the Gaussian binomial coefficient `[n choose k]_q`

With `N = qⁿ`, `K = qᵏ`: `F(n+1,k)/F(n,k) = (1-qN)/(1-qN/K) = K(1-qN)/(K-qN)` and
`F(n,k+1)/F(n,k) = (1-N/K)/(1-qK) = (K-N)/(K(1-qK))`. The search (`#eval`, a few seconds
in the interpreter) finds no certificate of orders `(1,1)` but one of orders `(1,2)`, i.e. a
`k`-free recurrence among `F(n,k), F(n+1,k), F(n+1,k+1), F(n+2,k+1)`. The kernel
did not finish reducing the full successful search (minutes, then stuck), so the kernel-checked
statement is that the certificate found by the search passes `qccheck`. -/

namespace QCelineDemo

open QCeline

/-- `q` as a polynomial in `(q, N, K)`. -/
def qT : QTri := const (const (X : P1))
/-- `N = qⁿ`. -/
def NT : QTri := const (X : P2)
/-- `K = qᵏ`. -/
def KT : QTri := X
/-- A rational constant. -/
def cT (c : ℚ) : QTri := const (const (const c))
/-- A polynomial in `q, N` from the coefficient lists (in `q`) of the powers of `N`. -/
def mk2 (l : List (List ℚ)) : P2 := ⟨l.map fun c => ⟨c⟩⟩

/-- Ratio data of the Gaussian binomial `[n choose k]_q`. -/
def qbin : QInput :=
  { s1 := KT * (cT 1 - qT * NT), s2 := KT - qT * NT,
    r1 := KT - NT, r2 := KT * (cT 1 - qT * KT) }

/-- A coefficient of the recurrence found by `qceline qbin 1 2`. -/
def p1 : P2 := mk2 [[-1], [0, 3, 2, 1], [0, 0, -3, -6, -4, -2], [0, 0, 0, 1, 6, 6, 6, 1],
  [0, 0, 0, 0, 0, -2, -4, -6, -3], [0, 0, 0, 0, 0, 0, 0, 1, 2, 3], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]

/-- The other coefficient. -/
def p0 : P2 := mk2 [[1], [0, -4, -2, -1], [0, 0, 6, 8, 5, 2], [0, 0, 0, -4, -12, -10, -8, -1],
  [0, 0, 0, 0, 1, 8, 10, 12, 4], [0, 0, 0, 0, 0, 0, -2, -5, -8, -6],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]

/-- The certificate: `p₀ F(n,k) + p₁ F(n+1,k) + p₁ F(n+1,k+1) - p₁ F(n+2,k+1) = 0`. -/
def cert : QCCert := certOf qbin 1 2 [p0, p1, 0, 0, p1, -p1]

set_option maxRecDepth 100000 in
/-- No certificate of orders `(1,1)` (the q-Pascal recurrences are not `k`-free). -/
example : (qceline qbin 1 1).isNone = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The certificate of orders `(1,2)` passes the computable check. -/
example : qccheck qbin cert = true := by decide +kernel

end QCelineDemo

end UndergradKB.Combinatorics.AeqB.Exec.Q
