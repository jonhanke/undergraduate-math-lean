import UndergradKB.Combinatorics.AeqB.Exec.Factored
import UndergradKB.Combinatorics.AeqB.Operators

/-!
# Executable recurrence operators and closure of holonomic sequences (A = B, §8.2, §9.2; wave 3)

A recurrence operator `L = ∑ cᵢ(n) Nⁱ` with polynomial coefficients over `ℚ` is stored as the list
of its coefficients (`EOp`); multiplication follows the rule `N c(n) = c(n+1) N` (A = B p. 172,
`RecOp.term_mul_term`). `EOp.act L y n = ∑ cᵢ(n) y(n+i)` is its action on sequences, and
`act_mul : act (A * B) y = act A (act B y)` is proved.

**Closure of P-recursive (holonomic) sequences under addition, executable.** If `L₁ y₁ = 0` and
`L₂ y₂ = 0`, a common left multiple `M₁ L₁ = M₂ L₂` annihilates `y₁ + y₂`. `commonLeftMultiple`
finds `M₁, M₂` by linear algebra over `ℚ(n)` (orders `ord L₂`, `ord L₁`: one more unknown than
equations); `clmCheck` re-checks `M₁ L₁ = M₂ L₂` computably, and `clm_sound` gives the closure.
`toRecOp` interprets an executable operator in the ring `RecOp K` of the repository
(`act_toRecOp`), so the result is stated with `IsPRecursive` (A = B Definition 9.2.1).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB.Exec

open LPoly QBi Finset

/-- An executable recurrence operator `∑ cᵢ(n) Nⁱ`: the list `[c₀, c₁, …]`. -/
structure EOp where
  c : List QPoly
  deriving Repr, Inhabited

namespace EOp

/-- Sum of operators. -/
def add (A B : EOp) : EOp := ⟨addL A.c B.c⟩

/-- `a(n) · B`. -/
def lmul (a : QPoly) (B : EOp) : EOp := ⟨B.c.map (a * ·)⟩

/-- `N · B = ∑ bⱼ(n+1) N^{j+1}`. -/
def nmul (B : EOp) : EOp := ⟨0 :: B.c.map (LPoly.shift 1)⟩

/-- Product of operators: `(a + A' N) B = a B + A' (N B)`. -/
def mulL : List QPoly → EOp → EOp
  | [], _ => ⟨[]⟩
  | a :: A, B => add (lmul a B) (mulL A (nmul B))

def mul (A B : EOp) : EOp := mulL A.c B

/-- `-A`. -/
def neg (A : EOp) : EOp := ⟨A.c.map (- ·)⟩

/-- `Nⁱ`. -/
def npow (i : ℕ) : EOp := ⟨List.replicate i 0 ++ [1]⟩

/-- Computable equality test of operators (all coefficients of `A - B` pass the zero test). -/
def eqTest (A B : EOp) : Bool := (add A (neg B)).c.all fun p => isZeroL p

variable {K : Type*} [Field K] [CharZero K]

/-- The action on sequences, `(∑ cᵢ Nⁱ) y = (n ↦ ∑ cᵢ(n) y(n+i))`. -/
def actL (n : ℕ) : List QPoly → (ℕ → K) → K
  | [], _ => 0
  | c :: l, y => ev1 c (n : K) * y n + actL n l (fun m => y (m + 1))

def act (L : EOp) (y : ℕ → K) (n : ℕ) : K := actL n L.c y

theorem actL_addL (n : ℕ) : ∀ (l m : List QPoly) (y : ℕ → K),
    actL n (addL l m) y = actL n l y + actL n m y
  | [], m, y => by simp [addL, actL]
  | a :: l, [], y => by simp [addL, actL]
  | a :: l, b :: m, y => by
    simp only [addL, actL, actL_addL n l m]
    rw [show ev1 (a + b) (n : K) = ev1 a (n : K) + ev1 b (n : K) from (hom1 (n : K)).map_add a b]
    ring

theorem act_add (A B : EOp) (y : ℕ → K) (n : ℕ) : act (add A B) y n = act A y n + act B y n :=
  actL_addL n _ _ y

theorem actL_map_mul (n : ℕ) (a : QPoly) : ∀ (l : List QPoly) (y : ℕ → K),
    actL n (l.map (a * ·)) y = ev1 a (n : K) * actL n l y
  | [], y => by simp [actL]
  | c :: l, y => by
    simp only [List.map_cons, actL, actL_map_mul n a l]
    rw [show ev1 (a * c) (n : K) = ev1 a (n : K) * ev1 c (n : K) from (hom1 (n : K)).map_mul a c]
    ring

theorem actL_map_shift (n : ℕ) : ∀ (l : List QPoly) (y : ℕ → K),
    actL n (l.map (LPoly.shift 1)) (fun m => y (m + 1)) = actL (n + 1) l y
  | [], y => rfl
  | c :: l, y => by
    simp only [List.map_cons, actL, ev1_shift]
    rw [actL_map_shift n l (fun m => y (m + 1))]
    push_cast
    rfl

theorem act_nmul (B : EOp) (y : ℕ → K) (n : ℕ) : act (nmul B) y n = act B y (n + 1) := by
  show ev1 0 (n : K) * y n + actL n (B.c.map (LPoly.shift 1)) (fun m => y (m + 1)) = _
  rw [actL_map_shift, show ev1 (0 : QPoly) (n : K) = 0 from rfl, zero_mul, zero_add]
  rfl

theorem actL_mulL : ∀ (A : List QPoly) (B : EOp) (y : ℕ → K) (n : ℕ),
    act (mulL A B) y n = actL n A (fun m => act B y m)
  | [], B, y, n => rfl
  | a :: A, B, y, n => by
    simp only [mulL, act_add, actL]
    rw [actL_mulL A (nmul B) y n]
    congr 1
    · exact actL_map_mul n a B.c y
    · congr 1
      funext m
      exact act_nmul B y m

/-- The product of operators acts as the composition. -/
theorem act_mul (A B : EOp) (y : ℕ → K) (n : ℕ) : act (mul A B) y n = act A (act B y) n :=
  actL_mulL A.c B y n

theorem act_neg (A : EOp) (y : ℕ → K) (n : ℕ) : act (neg A) y n = - act A y n := by
  unfold act neg
  induction A.c generalizing y with
  | nil => simp [actL]
  | cons c l ih =>
    simp only [List.map_cons, actL, ih]
    rw [show ev1 (-c) (n : K) = - ev1 c (n : K) from (hom1 (n : K)).map_neg c]
    ring

theorem actL_eq_zero_of_all (n : ℕ) : ∀ (l : List QPoly) (y : ℕ → K),
    (l.all fun p => isZeroL p) = true → actL n l y = 0
  | [], _, _ => rfl
  | c :: l, y, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [actL, actL_eq_zero_of_all n l _ h.2]
    rw [show ev1 c (n : K) = 0 from ev_eq_zero_of_isZero zeroSound_ratCast (n : K) c h.1]
    ring

theorem act_eq_of_eqTest {A B : EOp} (h : eqTest A B = true) (y : ℕ → K) (n : ℕ) :
    act A y n = act B y n := by
  have := actL_eq_zero_of_all (K := K) n _ y h
  have e : act (add A (neg B)) y n = 0 := this
  rw [act_add, act_neg] at e
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e)

theorem act_add_seq (A : EOp) (y z : ℕ → K) (n : ℕ) :
    act A (y + z) n = act A y n + act A z n := by
  unfold act
  induction A.c generalizing y z with
  | nil => simp [actL]
  | cons c l ih =>
    simp only [actL]
    rw [show (fun m => (y + z) (m + 1)) = (fun m => y (m + 1)) + (fun m => z (m + 1)) from rfl, ih]
    simp only [Pi.add_apply]
    ring

end EOp

/-! ### Common left multiples (search) -/

/-- A certificate of a common left multiple: `M₁ L₁ = M₂ L₂`. -/
structure CLMCert where
  M1 : EOp
  M2 : EOp
  deriving Repr, Inhabited

/-- The computable check `M₁ L₁ = M₂ L₂`. -/
def clmCheck (L1 L2 : EOp) (C : CLMCert) : Bool := EOp.eqTest (C.M1.mul L1) (C.M2.mul L2)

/-- A nonzero common left multiple `M₁ L₁ = M₂ L₂` of `L₁` and `L₂`, by linear algebra over
`ℚ(n)`: the unknowns are the coefficients of `M₁` (order `≤ ord L₂`) and `M₂` (order `≤ ord L₁`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
def commonLeftMultiple (L1 L2 : EOp) : Option CLMCert :=
  let r1 := L1.c.length - 1
  let r2 := L2.c.length - 1
  let cols : List EOp := ((List.range (r2 + 1)).map fun i => (EOp.npow i).mul L1) ++
    ((List.range (r1 + 1)).map fun i => EOp.neg ((EOp.npow i).mul L2))
  let nrows := (cols.map fun c => c.c.length).foldl max 0
  let rows : List (List QFrac) := (List.range nrows).map fun k =>
    cols.map fun c => QFrac.ofPoly (c.c.getD k 0)
  match Linear.kernel rows cols.length with
  | [] => none
  | v :: _ =>
    let w := Linear.clearDen v
    let C : CLMCert := ⟨⟨w.take (r2 + 1)⟩, ⟨w.drop (r2 + 1)⟩⟩
    if clmCheck L1 L2 C then some C else none

/-! ### Interpretation in `RecOp K` -/

section RecOp

variable {K : Type*} [Field K] [CharZero K]

open Polynomial in
/-- A polynomial in `n` over `ℚ` as a Mathlib polynomial over `K`. -/
noncomputable def toPolyK (p : QPoly) : K[X] :=
  LPoly.ev (fun q : ℚ => Polynomial.C (q : K)) Polynomial.X p

open Polynomial in
theorem eval_toPolyK (p : QPoly) (x : K) : (toPolyK p).eval x = ev1 p x := by
  unfold toPolyK ev1 LPoly.ev
  induction p.coeffs with
  | nil => simp [evL]
  | cons a l ih => simp [evL, ih]

/-- An executable operator as an element of `RecOp K`. -/
noncomputable def toRecOp (L : EOp) : RecOp K :=
  ∑ i ∈ range L.c.length, RecOp.term i (toPolyK (L.c.getD i 0))

theorem actL_eq_sum (n : ℕ) : ∀ (l : List QPoly) (y : ℕ → K),
    EOp.actL n l y = ∑ i ∈ range l.length, ev1 (l.getD i 0) (n : K) * y (n + i)
  | [], y => by simp [EOp.actL]
  | c :: l, y => by
    rw [EOp.actL, actL_eq_sum n l, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1

theorem act_toRecOp (L : EOp) (y : ℕ → K) (n : ℕ) :
    RecOp.act (toRecOp L) y n = EOp.act L y n := by
  rw [EOp.act, actL_eq_sum, toRecOp]
  induction (range L.c.length) using Finset.induction_on with
  | empty => simp [RecOp.act_zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, RecOp.act_add, Pi.add_apply, ih, RecOp.act_term,
      eval_toPolyK]

end RecOp

/-! ### Soundness: closure under addition -/

section Closure

variable {K : Type*} [Field K] [CharZero K]

/-- CO-513 (closure under addition, executable). If `clmCheck L₁ L₂ C` holds, `L₁ y₁ = 0` and
`L₂ y₂ = 0`, then the common left multiple `M₁ L₁` annihilates `y₁ + y₂`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
theorem clm_sound (L1 L2 : EOp) (C : CLMCert) (h : clmCheck L1 L2 C = true) (y1 y2 : ℕ → K)
    (h1 : ∀ n, EOp.act L1 y1 n = 0) (h2 : ∀ n, EOp.act L2 y2 n = 0) (n : ℕ) :
    EOp.act (C.M1.mul L1) (y1 + y2) n = 0 := by
  rw [EOp.act_add_seq, EOp.act_mul, EOp.act_eq_of_eqTest h, EOp.act_mul]
  have e1 : EOp.act L1 y1 = 0 := funext h1
  have e2 : EOp.act L2 y2 = 0 := funext h2
  rw [e1, e2]
  simp only [EOp.act]
  rw [show (0 : ℕ → K) = fun _ => 0 from rfl]
  have z : ∀ (l : List QPoly) (m : ℕ), EOp.actL m l (fun _ => (0 : K)) = 0 := by
    intro l
    induction l with
    | nil => intro m; rfl
    | cons c l ih => intro m; simp [EOp.actL, ih]
  rw [z, z, add_zero]

/-- The value of a polynomial in `n` at a rational point, computably. -/
def evalQ (p : QPoly) (x : ℚ) : ℚ := LPoly.ev (fun q : ℚ => q) x p

theorem ev1_natCast_eq (p : QPoly) (m : ℕ) : ev1 p (m : K) = ((evalQ p m : ℚ) : K) := by
  unfold ev1 evalQ LPoly.ev
  induction p.coeffs with
  | nil => simp [evL]
  | cons a l ih => simp [evL, ih]

/-- An operator whose last coefficient is nonzero at some natural number `m` is a nonzero
element of `RecOp K`. -/
theorem toRecOp_ne_zero (L : EOp) (m : ℕ) (hL : L.c ≠ [])
    (hm : evalQ (L.c.getLast hL) m ≠ 0) : toRecOp (K := K) L ≠ 0 := by
  intro h0
  -- act on the indicator of `m + (len - 1)` at `m`
  set d := L.c.length - 1 with hd
  have hlen : 0 < L.c.length := List.length_pos_of_ne_nil hL
  let y : ℕ → K := fun t => if t = m + d then 1 else 0
  have h := act_toRecOp (K := K) L y m
  rw [h0, RecOp.act_zero, EOp.act, actL_eq_sum] at h
  rw [Finset.sum_eq_single d] at h
  · simp only [y, ite_true, mul_one, Pi.zero_apply] at h
    have hl : L.c.getD d 0 = L.c.getLast hL := by
      rw [List.getLast_eq_getElem]
      simp only [List.getD, d]
      rw [List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hl, ev1_natCast_eq, eq_comm, Rat.cast_eq_zero] at h
    exact hm h
  · intro i _ hi
    simp only [y]
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), mul_zero]
  · intro hdm
    exact absurd (Finset.mem_range.2 (by omega)) hdm

/-- CO-513, executable closure: **the sum of two P-recursive sequences is P-recursive**, with
the annihilating operator computed by `commonLeftMultiple`. If `clmCheck L₁ L₂ C` holds, the
leading coefficient of `M₁ L₁` is nonzero at some natural number, `L₁ y₁ = 0` and `L₂ y₂ = 0`,
then `y₁ + y₂` is P-recursive. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
theorem isPRecursive_add_of_clm (L1 L2 : EOp) (C : CLMCert) (h : clmCheck L1 L2 C = true)
    (m : ℕ) (hne : (C.M1.mul L1).c ≠ [])
    (hm : evalQ ((C.M1.mul L1).c.getLast hne) m ≠ 0) (y1 y2 : ℕ → K)
    (h1 : ∀ n, EOp.act L1 y1 n = 0) (h2 : ∀ n, EOp.act L2 y2 n = 0) :
    IsPRecursive (y1 + y2) :=
  ⟨toRecOp (C.M1.mul L1), toRecOp_ne_zero _ m hne hm, fun n => by
    rw [act_toRecOp]; exact clm_sound L1 L2 C h y1 y2 h1 h2 n⟩

end Closure

end UndergradKB.Combinatorics.AeqB.Exec
