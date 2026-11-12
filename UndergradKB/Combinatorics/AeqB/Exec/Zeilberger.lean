import UndergradKB.Combinatorics.AeqB.Exec.Factored
import UndergradKB.Combinatorics.AeqB.Zeilberger

/-!
# Zeilberger's algorithm, executable (A = B, §6.3; wave 3)

Input (`ZInput`): the two ratios of a hypergeometric term `F(n,k)` as products of linear forms,
`F(n,k)/F(n-1,k) = s₁/s₂` and `F(n,k+1)/F(n,k) = r₁/r₂` (for a proper hypergeometric term these are
always products of linear forms).

`zeilberger I Jmax Δmax` runs the algorithm of A = B §6.3 over `ℚ(n)`: for `J = 1, 2, …` it forms
`p₀ = ∑ⱼ aⱼ wⱼ` (6.3.6), Gosper's canonical form `(p₁, p₂, p₃)` of the `aⱼ`-free part (6.3.9), and
solves `p₂(k) b(k+1) - p₃(k-1) b(k) = p₀(k) p₁(k)` (6.3.11) for the `aⱼ(n)` and the coefficients of
`b` (polynomial in `k` of degree `≤ Δ`) by linear algebra over `ℚ(n)` (`Linear.kernel`). It returns
a certificate `ZCert`: the recurrence coefficients `a₀(n), …, a_J(n)` and `p₁, p₂, p₃, b`.

`zcheck I C` re-checks the two polynomial identities (6.3.9) and (6.3.11) of a certificate
computably. **Correctness** (`zcheck_sound`, CO-425/CO-426): if `zcheck I C = true` then for every
`F` with the given ratios, `∑ⱼ aⱼ(n) F(n+j,k) = G(n,k+1) - G(n,k)` with
`G(n,k) = p₃(k-1) b(k) tₖ / p(k)`, at every point where the denominators do not vanish; this is
`Zeilberger.zeilberger_sound` applied to the values of the certificate.

The search itself (canonical form, linear algebra) is not verified: a wrong search result can only
make the algorithm fail, never return a false recurrence.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec

open LPoly QBi Finset

/-- The data of Zeilberger's algorithm: `F(n,k)/F(n-1,k) = s₁/s₂`, `F(n,k+1)/F(n,k) = r₁/r₂`. -/
structure ZInput where
  s1 : Fac
  s2 : Fac
  r1 : Fac
  r2 : Fac
  deriving Repr, Inhabited

/-- A certificate of Zeilberger's algorithm: order `J`, coefficients `a₀(n), …, a_J(n)` of the
recurrence, the canonical form `p₁, p₂, p₃`, and the polynomial `b(n,k)`. -/
structure ZCert where
  J : ℕ
  a : List QPoly
  p1 : QBi
  p2 : QBi
  p3 : QBi
  b : QBi
  deriving Repr, Inhabited

namespace ZInput

variable (I : ZInput)

/-- `∏_{r=1}^{J} s₂(n+r, k)`. -/
def s2P (J : ℕ) : QBi := prodRange J fun r => shiftN ((r : ℚ) + 1) I.s2.toBi

/-- `wⱼ = ∏_{i<j} s₁(n+j-i, k) ∏_{r<J-j} s₂(n+j+r+1, k)`, so that `p₀ = ∑ⱼ aⱼ wⱼ` (6.3.6). -/
def w (J j : ℕ) : QBi :=
  prodRange j (fun i => shiftN ((j : ℚ) - i) I.s1.toBi) *
    prodRange (J - j) (fun r => shiftN ((j : ℚ) + r + 1) I.s2.toBi)

/-- `p₀(n,k) = ∑ⱼ aⱼ(n) wⱼ(n,k)`. -/
def p0 (J : ℕ) (a : List QPoly) : QBi := sumRange (J + 1) fun j => ofN (a.getD j 0) * I.w J j

end ZInput

/-- The polynomial of identity (6.3.9), `r₁ s₂P(k) p₁(k) p₃(k) - r₂ s₂P(k+1) p₁(k+1) p₂(k)`. -/
def zEq9 (I : ZInput) (C : ZCert) : QBi :=
  I.r1.toBi * I.s2P C.J * C.p1 * C.p3 -
    I.r2.toBi * shiftK 1 (I.s2P C.J) * shiftK 1 C.p1 * C.p2

/-- The polynomial of identity (6.3.11), `p₂(k) b(k+1) - p₃(k-1) b(k) - p₀(k) p₁(k)`. -/
def zEq11 (I : ZInput) (C : ZCert) : QBi :=
  C.p2 * shiftK 1 C.b - shiftK (-1) C.p3 * C.b - I.p0 C.J C.a * C.p1

/-- The computable certificate check of Zeilberger's algorithm. -/
def zcheck (I : ZInput) (C : ZCert) : Bool := isZeroL (zEq9 I C) && isZeroL (zEq11 I C)

/-! ### The search -/

/-- `kˡ` as a polynomial in `n, k`. -/
def kPow (l : ℕ) : QBi := ⟨List.replicate l 0 ++ [1]⟩

/-- Coefficient of `kᵐ` of a polynomial in `n, k`. -/
def coeffK (p : QBi) (m : ℕ) : QPoly := p.coeffs.getD m 0

/-- One attempt of Zeilberger's algorithm with order `J` and `deg_k b ≤ Δ`. -/
def zeilbergerAt (I : ZInput) (J Δ : ℕ) : Option ZCert :=
  let r := I.r1.mul (I.s2.prodShiftN (fun r => (r : ℤ) + 1) J)
  let s := I.r2.mul ((I.s2.prodShiftN (fun r => (r : ℤ) + 1) J).shiftK 1)
  let (q1, q2, q3) := Gosper.canonical r s
  let p1 := q1.toBi
  let p2 := q2.toBi
  let p3 := q3.toBi
  let colsA : List QBi := (List.range (J + 1)).map fun j => -(p1 * I.w J j)
  let colsB : List QBi := (List.range (Δ + 1)).map fun l =>
    p2 * shiftK 1 (kPow l) - shiftK (-1) p3 * kPow l
  let cols := colsA ++ colsB
  let nrows := (cols.map fun c => c.coeffs.length).foldl max 0
  let rows : List (List QFrac) := (List.range nrows).map fun m =>
    cols.map fun c => QFrac.ofPoly (coeffK c m)
  let ker := Linear.kernel rows cols.length
  let good := ker.filter fun v => (v.take (J + 1)).any fun x => !x.isZero
  match good with
  | [] => none
  | v :: _ =>
    let v' := Linear.clearDen v
    let C : ZCert := ⟨J, v'.take (J + 1), p1, p2, p3, ⟨v'.drop (J + 1)⟩⟩
    if zcheck I C then some C else none

/-- **Zeilberger's algorithm** (A = B, §6.3), executable: tries the orders `J = 1, …, Jmax` and
degree bounds `Δ = 0, …, Δmax` and returns the first certificate that passes `zcheck`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Zeilberger's algorithm, (6.3.1)-(6.3.12)), p. 116-119"]
def zeilberger (I : ZInput) (Jmax Δmax : ℕ) : Option ZCert :=
  ((List.range Jmax).flatMap fun J => (List.range (Δmax + 1)).map fun Δ => (J + 1, Δ)).findSome?
    fun (J, Δ) => zeilbergerAt I J Δ

/-! ### Finding a WZ mate (A = B §7.2) -/

/-- **Finding a WZ certificate** (A = B §7.2, CO-445), executable: run Gosper's algorithm on
`F(n+1,k) - F(n,k)`, i.e. Zeilberger's step with the fixed operator `N - 1`: the coefficients are
forced to be `(a₀, a₁) = (-c(n), c(n))` and only `c(n)` and `b` are unknown. If it succeeds, the
certificate gives `c(n) (F(n+1,k) - F(n,k)) = G(n,k+1) - G(n,k)` (`wzMate_sound`); if Gosper fails
(no polynomial `b` of degree `≤ Δmax`), the method fails. -/
@[kb "petkovsekwilfzeilberger1996" "text (finding the WZ certificate), p. 133-134"]
def wzMate (I : ZInput) (Δmax : ℕ) : Option ZCert :=
  (List.range (Δmax + 1)).findSome? fun Δ =>
    let J := 1
    let r := I.r1.mul (I.s2.prodShiftN (fun r => (r : ℤ) + 1) J)
    let s := I.r2.mul ((I.s2.prodShiftN (fun r => (r : ℤ) + 1) J).shiftK 1)
    let (q1, q2, q3) := Gosper.canonical r s
    let p1 := q1.toBi
    let p2 := q2.toBi
    let p3 := q3.toBi
    let colA : QBi := -(p1 * (I.w J 1 - I.w J 0))
    let colsB : List QBi := (List.range (Δ + 1)).map fun l =>
      p2 * shiftK 1 (kPow l) - shiftK (-1) p3 * kPow l
    let cols := colA :: colsB
    let nrows := (cols.map fun c => c.coeffs.length).foldl max 0
    let rows : List (List QFrac) := (List.range nrows).map fun m =>
      cols.map fun c => QFrac.ofPoly (coeffK c m)
    match (Linear.kernel rows cols.length).filter fun v => !(v.headD QFrac.zero).isZero with
    | [] => none
    | v :: _ =>
      let v' := Linear.clearDen v
      let c := v'.headD 0
      let C : ZCert := ⟨1, [-c, c], p1, p2, p3, ⟨v'.drop 1⟩⟩
      if zcheck I C then some C else none

/-! ### Input from factorial data, and the rational certificate -/

/-- The ratios of `F(n,k) = yⁿ xᵏ ∏ (aᵢn+bᵢk+cᵢ)! / ∏ (uⱼn+vⱼk+wⱼ)!` (a proper hypergeometric term
without polynomial factor, A = B (4.4.1)), as linear-form products: numerator factorials `num`,
denominator factorials `den`, given as triples `(a, b, c)`. -/
def ZInput.ofProper (num den : List (ℤ × ℤ × ℤ)) (x y : ℚ) : ZInput :=
  -- `(m + b)!/m!` (step `b` in `k`) and `m!/(m - a)!` (step `-a` in `n`) as products of forms
  let up (t : ℤ × ℤ × ℤ) (step : ℤ) : List Lin × List Lin :=
    -- `(m + step)! / m!` with `m = a n + b k + c`
    if 0 ≤ step then ((List.range step.toNat).map fun i => ⟨t.1, t.2.1, t.2.2 + i + 1⟩, [])
    else ([], (List.range (-step).toNat).map fun i => ⟨t.1, t.2.1, t.2.2 - i⟩)
  let rN := num.map fun t => up t t.2.1
  let rD := den.map fun t => up t t.2.1
  -- `F(n,k)/F(n-1,k)`: `m!/(m-a)!` = `(m' + a)!/m'!` with `m' = m - a`
  let sN := num.map fun t => up ⟨t.1, t.2.1, t.2.2 - t.1⟩ t.1
  let sD := den.map fun t => up ⟨t.1, t.2.1, t.2.2 - t.1⟩ t.1
  { r1 := ⟨x, (rN.map Prod.fst).flatten ++ (rD.map Prod.snd).flatten⟩
    r2 := ⟨1, (rN.map Prod.snd).flatten ++ (rD.map Prod.fst).flatten⟩
    s1 := ⟨y, (sN.map Prod.fst).flatten ++ (sD.map Prod.snd).flatten⟩
    s2 := ⟨1, (sN.map Prod.snd).flatten ++ (sD.map Prod.fst).flatten⟩ }

/-- Numerator of the rational certificate `R = G/F = p₃(k-1) b(k) / (p₁(k) ∏_{r=1}^{J} s₂(n+r,k))`. -/
def ZCert.Rnum (C : ZCert) : QBi := shiftK (-1) C.p3 * C.b

/-- Denominator of the rational certificate `R = G/F`. -/
def ZCert.Rden (I : ZInput) (C : ZCert) : QBi := C.p1 * I.s2P C.J

/-! ### Soundness -/

section Sound

variable {K : Type*} [Field K] [CharZero K]

/-- The value of a polynomial in `n, k` at integer points. -/
def val (K : Type*) [Field K] [CharZero K] (p : QBi) (n k : ℤ) : K := ev2 p (n : K) (k : K)

/-- The recurrence coefficient `aⱼ(n)` of a certificate, as a function. -/
def ZCert.coef (K : Type*) [Field K] [CharZero K] (C : ZCert) (j : ℕ) (n : ℤ) : K := ev1 (C.a.getD j 0) (n : K)

theorem val_shiftN (c : ℤ) (p : QBi) (n k : ℤ) :
    (val K (shiftN (c : ℚ) p) n k : K) = val K p (n + c) k := by
  simp only [val, ev2_shiftN]; push_cast; rfl

theorem val_shiftK (c : ℤ) (p : QBi) (n k : ℤ) :
    (val K (shiftK (c : ℚ) p) n k : K) = val K p n (k + c) := by
  simp only [val, ev2_shiftK]; push_cast; rfl

theorem val_s2P (I : ZInput) (J : ℕ) (n k : ℤ) :
    val K (I.s2P J) n k = Zeilberger.s2Prod J (val K I.s2.toBi) n k := by
  simp only [val, ZInput.s2P, ev2_prodRange, Zeilberger.s2Prod]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [show ((r : ℚ) + 1) = (((r + 1 : ℕ) : ℤ) : ℚ) by push_cast; ring]
  exact val_shiftN _ _ n k

theorem val_p0 (I : ZInput) (C : ZCert) (n k : ℤ) :
    val K (I.p0 C.J C.a) n k =
      Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n k := by
  simp only [val, ZInput.p0, ev2_sumRange, Zeilberger.p0]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ZInput.w, ev2_mul, ev2_ofN, ev2_prodRange, ZCert.coef, mul_assoc]
  congr 2
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show ((j : ℚ) - i) = (((j : ℤ) - i : ℤ) : ℚ) by push_cast; ring]
    rw [show (n : ℤ) + j - i = n + ((j : ℤ) - i) by ring]
    exact val_shiftN _ _ n k
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [show ((j : ℚ) + r + 1) = (((j + r + 1 : ℕ) : ℤ) : ℚ) by push_cast; ring]
    exact val_shiftN _ _ n k

/-- CO-425, CO-426. **Correctness of the executable Zeilberger algorithm.** If the certificate
`C` passes the computable check `zcheck I C`, then every `F` with the ratios of `I`
(`s₂ F(n,k) = s₁ F(n-1,k)` and `r₂ F(n,k+1) = r₁ F(n,k)` at all integer points) satisfies the
telescoped recurrence `∑_{j ≤ J} aⱼ(n) F(n+j,k) = G(n,k+1) - G(n,k)` with
`G(n,k) = p₃(n,k-1) b(n,k) tₖ / (p₀(n,k) p₁(n,k))`, `tₖ = ∑ⱼ aⱼ(n) F(n+j,k)`, at every point where
`r₂(n,k) s₂P(n,k+1)`, `p₀ p₁ (n,k)` and `p₀ p₁ (n,k+1)` do not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.3.1)-(6.3.12), p. 116-119"]
theorem zcheck_sound (I : ZInput) (C : ZCert) (h : zcheck I C = true) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val K I.s2.toBi n k * F n k = val K I.s1.toBi n k * F (n - 1) k)
    (hr : ∀ n k, val K I.r2.toBi n k * F n (k + 1) = val K I.r1.toBi n k * F n k) (n k : ℤ)
    (hs0 : val K I.r2.toBi n k * Zeilberger.s2Prod C.J (val K I.s2.toBi) n (k + 1) ≠ 0)
    (hp : Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n k * val K C.p1 n k ≠ 0)
    (hp1 : Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n (k + 1) *
      val K C.p1 n (k + 1) ≠ 0) :
    ∑ j ∈ range (C.J + 1), (C.coef K) j n * F (n + j) k =
      val K C.p3 n (k + 1 - 1) * val K C.b n (k + 1) * Zeilberger.tSeq C.J (C.coef K) F n (k + 1) /
          (Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n (k + 1) *
            val K C.p1 n (k + 1)) -
        val K C.p3 n (k - 1) * val K C.b n k * Zeilberger.tSeq C.J (C.coef K) F n k /
          (Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n k * val K C.p1 n k) := by
  simp only [zcheck, Bool.and_eq_true] at h
  have e9 := ev_eq_zero_of_isZero (zero1 (n : K)) (k : K) _ h.1
  have e11 := ev_eq_zero_of_isZero (zero1 (n : K)) (k : K) _ h.2
  have e9' : (val K (zEq9 I C) n k : K) = 0 := e9
  have e11' : (val K (zEq11 I C) n k : K) = 0 := e11
  have hv : ∀ p q : QBi, (val K (p * q) n k : K) = val K p n k * val K q n k :=
    fun p q => ev2_mul p q _ _
  have hsub : ∀ p q : QBi, (val K (p - q) n k : K) = val K p n k - val K q n k :=
    fun p q => ev2_sub p q _ _
  have hk1 : ∀ p : QBi, (val K (shiftK 1 p) n k : K) = val K p n (k + 1) := fun p => by
    simpa using val_shiftK (K := K) 1 p n k
  have hkm1 : ∀ p : QBi, (val K (shiftK (-1) p) n k : K) = val K p n (k - 1) := fun p => by
    simpa [sub_eq_add_neg] using val_shiftK (K := K) (-1) p n k
  simp only [zEq9, hsub, hv, hk1, val_s2P] at e9'
  simp only [zEq11, hsub, hv, hk1, hkm1, val_p0] at e11'
  refine Zeilberger.zeilberger_sound C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) (val K I.r1.toBi)
    (val K I.r2.toBi) F hs hr (val K C.p1) (val K C.p2) (val K C.p3) (val K C.b) n k ?_ ?_ hs0 hp hp1
  · exact sub_eq_zero.1 e9'
  · rw [← sub_eq_zero, ← e11']

/-- CO-445. **Correctness of the WZ-mate finder.** A certificate of order `1` with coefficients
`(-c(n), c(n))` that passes `zcheck` (as returned by `wzMate`) gives
`c(n) (F(n+1,k) - F(n,k)) = G(n,k+1) - G(n,k)`, i.e. `(F, G/c)` is a WZ pair, at every point where
the denominators of `zcheck_sound` do not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "text (finding the WZ certificate), p. 133-134"]
theorem wzMate_sound (I : ZInput) (C : ZCert) (h : zcheck I C = true) (hJ : C.J = 1) (c : QPoly)
    (ha : C.a = [-c, c]) (F : ℤ → ℤ → K)
    (hs : ∀ n k, val K I.s2.toBi n k * F n k = val K I.s1.toBi n k * F (n - 1) k)
    (hr : ∀ n k, val K I.r2.toBi n k * F n (k + 1) = val K I.r1.toBi n k * F n k) (n k : ℤ)
    (hs0 : val K I.r2.toBi n k * Zeilberger.s2Prod C.J (val K I.s2.toBi) n (k + 1) ≠ 0)
    (hp : Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n k * val K C.p1 n k ≠ 0)
    (hp1 : Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n (k + 1) *
      val K C.p1 n (k + 1) ≠ 0) :
    ev1 c (n : K) * (F (n + 1) k - F n k) =
      val K C.p3 n (k + 1 - 1) * val K C.b n (k + 1) * Zeilberger.tSeq C.J (C.coef K) F n (k + 1) /
          (Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n (k + 1) *
            val K C.p1 n (k + 1)) -
        val K C.p3 n (k - 1) * val K C.b n k * Zeilberger.tSeq C.J (C.coef K) F n k /
          (Zeilberger.p0 C.J (C.coef K) (val K I.s1.toBi) (val K I.s2.toBi) n k * val K C.p1 n k) := by
  rw [← zcheck_sound I C h F hs hr n k hs0 hp hp1, hJ]
  simp only [ZCert.coef, ha, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    List.getD_cons_zero, List.getD_cons_succ, Nat.cast_zero, add_zero, Nat.cast_one]
  rw [show ev1 (-c) (n : K) = - ev1 c (n : K) from (hom1 (n : K)).map_neg c]
  ring

end Sound

end UndergradKB.Combinatorics.AeqB.Exec
