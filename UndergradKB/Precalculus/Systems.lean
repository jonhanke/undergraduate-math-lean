import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Tactic.NoncommRing
import UndergradKB.Common.Attr

/-!
# Systems of linear equations (Precalculus, Chapter 8.1-8.2)

Linear equations, systems `A x = b`, their terminology, the three equivalence moves, augmented
matrices, row echelon forms and Gauss-Jordan elimination.
-/

open Matrix

namespace UndergradKB.Precalculus

/-! ### Linear equations -/

/-- Solution set in the plane of `a₁ x + a₂ y = c`. -/
def lin2Solutions (a₁ a₂ c : ℝ) : Set (ℝ × ℝ) := {p | a₁ * p.1 + a₂ * p.2 = c}

/-- A linear equation in two variables whose coefficients are not both zero describes a line:
the graph of `y = (c - a₁ x)/a₂` when `a₂ ≠ 0`, and the vertical line `x = c/a₁` when `a₂ = 0`;
in particular it has a solution (PC-128). -/
@[kb "stitzzeager2013" "Definition 8.1, p. 561"]
theorem lin2_solutions_line (a₁ a₂ c : ℝ) (h : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    (a₂ ≠ 0 → lin2Solutions a₁ a₂ c = {p | p.2 = (c - a₁ * p.1) / a₂}) ∧
    (a₂ = 0 → lin2Solutions a₁ a₂ c = {p | p.1 = c / a₁}) ∧
    (lin2Solutions a₁ a₂ c).Nonempty := by
  refine ⟨fun h2 => ?_, fun h2 => ?_, ?_⟩
  · ext p
    simp only [lin2Solutions, Set.mem_ofPred_eq]
    rw [eq_div_iff h2]
    constructor <;> intro h <;> linarith
  · have h1 : a₁ ≠ 0 := by
      rcases h with h | h
      · exact h
      · exact absurd h2 h
    ext p
    simp only [lin2Solutions, Set.mem_ofPred_eq, h2, zero_mul, add_zero]
    rw [eq_div_iff h1]
    constructor <;> intro h <;> linarith
  · by_cases h2 : a₂ = 0
    · have h1 : a₁ ≠ 0 := by
        rcases h with h | h
        · exact h
        · exact absurd h2 h
      exact ⟨(c / a₁, 0), by simp [lin2Solutions, h2]; field_simp⟩
    · exact ⟨(0, c / a₂), by simp [lin2Solutions]; field_simp⟩

/-- Solution set of the linear equation `a₁ x₁ + ... + aₙ xₙ = c` in `n` variables. -/
def linEqSolutions {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | ∑ i, a i * x i = c}

/-- A linear equation in `n` variables with some nonzero coefficient is solvable, and any
variable with nonzero coefficient can be solved for in terms of the others (PC-130). -/
@[kb "stitzzeager2013" "Definition 8.2, p. 566"]
theorem lin_eq_solutions_solve {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (ha : a ≠ 0) :
    (linEqSolutions a c).Nonempty ∧
    ∀ (i : Fin n), a i ≠ 0 → ∀ x : Fin n → ℝ,
      x ∈ linEqSolutions a c ↔
        x i = (c - ∑ j ∈ Finset.univ.erase i, a j * x j) / a i := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    refine ⟨Pi.single i (c / a i), ?_⟩
    simp [linEqSolutions, Pi.single_apply]
    field_simp
  · intro i hi x
    show ∑ j, a j * x j = c ↔ _
    rw [eq_div_iff hi, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    constructor <;> intro h <;> linarith

/-- The two-variable equation is the case `n = 2` of the general one. -/
theorem lin2_mem_iff_linEq (a₁ a₂ c : ℝ) (p : ℝ × ℝ) :
    p ∈ lin2Solutions a₁ a₂ c ↔ (![p.1, p.2] : Fin 2 → ℝ) ∈ linEqSolutions ![a₁, a₂] c := by
  simp [lin2Solutions, linEqSolutions, Fin.sum_univ_two]

/-! ### Systems and their terminology -/

/-- Solution set of the system `A x = b` of `m` linear equations in `n` unknowns. -/
def solutionSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x = b}

/-- The system `A x = b` has at least one solution. -/
def IsConsistent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  (solutionSet A b).Nonempty

/-- The system `A x = b` has no solution. -/
def IsInconsistent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ¬ IsConsistent A b

/-- Consistent with exactly one solution. -/
def IsIndependent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃! x, x ∈ solutionSet A b

/-- Consistent with more than one solution (free parameters). -/
def IsDependent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  IsConsistent A b ∧ ¬ IsIndependent A b

/-- Every system is exactly one of inconsistent, consistent independent, consistent dependent;
independent means exactly one solution, and a dependent system has infinitely many solutions
(PC-129). -/
@[kb "stitzzeager2013" "§8.1, p. 565"]
theorem system_trichotomy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (IsInconsistent A b ∨ IsIndependent A b ∨ IsDependent A b) ∧
    ¬ (IsInconsistent A b ∧ IsIndependent A b) ∧
    ¬ (IsInconsistent A b ∧ IsDependent A b) ∧
    ¬ (IsIndependent A b ∧ IsDependent A b) ∧
    (IsIndependent A b ↔ ∃ x, solutionSet A b = {x}) ∧
    (IsDependent A b ↔ (solutionSet A b).Infinite) := by
  have hcons : IsIndependent A b → IsConsistent A b := fun ⟨x, hx, _⟩ => ⟨x, hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : IsConsistent A b
    · by_cases h2 : IsIndependent A b
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl h1
  · exact fun h => h.1 (hcons h.2)
  · exact fun h => h.1 h.2.1
  · exact fun h => h.2.2 h.1
  · constructor
    · rintro ⟨x, hx, hu⟩
      exact ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, hu⟩⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hx ▸ rfl, fun y hy => by rw [hx] at hy; exact hy⟩
  · constructor
    · rintro ⟨⟨x, hx⟩, hni⟩
      have : ∃ y, y ∈ solutionSet A b ∧ y ≠ x := by
        by_contra hno
        push Not at hno
        exact hni ⟨x, hx, fun y hy => hno y hy⟩
      obtain ⟨y, hy, hyx⟩ := this
      have hinj : Function.Injective (fun t : ℝ => x + t • (y - x)) := by
        intro s t hst
        have h1 : (s - t) • (y - x) = 0 := by
          simp only at hst
          rw [sub_smul]
          exact sub_eq_zero.2 (add_left_cancel hst)
        rcases smul_eq_zero.1 h1 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd (sub_eq_zero.1 h) hyx
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      show A *ᵥ (x + t • (y - x)) = b
      have hx' : A *ᵥ x = b := hx
      have hy' : A *ᵥ y = b := hy
      rw [mulVec_add, mulVec_smul, mulVec_sub, hx', hy']
      simp
    · intro hinf
      have hne : (solutionSet A b).Nonempty := hinf.nonempty
      refine ⟨hne, fun ⟨x, hx, hu⟩ => ?_⟩
      apply hinf
      refine (Set.finite_singleton x).subset fun y hy => ?_
      exact hu y hy

/-! ### Equivalence moves (Theorem 8.1) -/

private lemma update_swap_iff {m : ℕ} (f g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    (f ∘ σ = g ∘ σ) ↔ f = g := by
  constructor
  · intro h
    funext i
    have := congrFun h (σ.symm i)
    simpa using this
  · intro h
    rw [h]

private lemma update_scale_iff {m : ℕ} (f g : Fin m → ℝ) (i : Fin m) (k : ℝ) (hk : k ≠ 0) :
    Function.update f i (k * f i) = Function.update g i (k * g i) ↔ f = g := by
  constructor
  · intro h
    funext i'
    by_cases hi : i' = i
    · subst hi
      have := congrFun h i'
      simpa [hk] using this
    · have := congrFun h i'
      simpa [Function.update_of_ne hi] using this
  · intro h
    rw [h]

private lemma update_add_iff {m : ℕ} (f g : Fin m → ℝ) (i j : Fin m) (hij : i ≠ j) (k : ℝ) :
    Function.update f i (f i + k * f j) = Function.update g i (g i + k * g j) ↔ f = g := by
  constructor
  · intro h
    have hj : f j = g j := by
      have := congrFun h j
      simpa [Function.update_of_ne hij.symm] using this
    funext i'
    by_cases hi : i' = i
    · subst hi
      have := congrFun h i'
      simp only [Function.update_self] at this
      rw [hj] at this
      linarith
    · have := congrFun h i'
      simpa [Function.update_of_ne hi] using this
  · intro h
    rw [h]

private lemma mulVec_updateRow' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (r : Fin n → ℝ) (x : Fin n → ℝ) :
    A.updateRow i r *ᵥ x = Function.update (A *ᵥ x) i (r ⬝ᵥ x) := by
  funext i'
  by_cases h : i' = i
  · subst h
    simp [mulVec]
  · simp [mulVec, updateRow_ne h, Function.update_of_ne h]

/-- Swapping two equations does not change the solution set. -/
theorem solutionSet_swap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    solutionSet (A.submatrix σ id) (b ∘ σ) = solutionSet A b := by
  ext x
  have key : (A.submatrix σ id *ᵥ x) = (A *ᵥ x) ∘ σ := rfl
  simp only [solutionSet, Set.mem_ofPred_eq, key]
  exact update_swap_iff _ _ σ

/-- Multiplying one equation by a nonzero number does not change the solution set. -/
theorem solutionSet_scale {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (i : Fin m) (k : ℝ) (hk : k ≠ 0) :
    solutionSet (A.updateRow i (k • A i)) (Function.update b i (k * b i)) =
      solutionSet A b := by
  ext x
  simp only [solutionSet, Set.mem_ofPred_eq, mulVec_updateRow', smul_dotProduct, smul_eq_mul]
  exact update_scale_iff _ _ i k hk

/-- Adding a multiple of one equation to a different equation does not change the solution set. -/
theorem solutionSet_add_multiple {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (i j : Fin m) (hij : i ≠ j) (k : ℝ) :
    solutionSet (A.updateRow i (A i + k • A j)) (Function.update b i (b i + k * b j)) =
      solutionSet A b := by
  ext x
  simp only [solutionSet, Set.mem_ofPred_eq, mulVec_updateRow', add_dotProduct,
    smul_dotProduct, smul_eq_mul]
  exact update_add_iff _ _ i j hij k

/-- The three moves that turn a system into an equivalent one: swapping two equations, scaling
an equation by a nonzero number, and adding a multiple of one equation to another (PC-131). -/
@[kb "stitzzeager2013" "Theorem 8.1, p. 567"]
theorem system_moves_equivalent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∀ σ : Equiv.Perm (Fin m), solutionSet (A.submatrix σ id) (b ∘ σ) = solutionSet A b) ∧
    (∀ (i : Fin m) (k : ℝ), k ≠ 0 →
      solutionSet (A.updateRow i (k • A i)) (Function.update b i (k * b i)) = solutionSet A b) ∧
    (∀ (i j : Fin m), i ≠ j → ∀ k : ℝ,
      solutionSet (A.updateRow i (A i + k • A j)) (Function.update b i (b i + k * b j)) =
        solutionSet A b) :=
  ⟨solutionSet_swap A b, solutionSet_scale A b, solutionSet_add_multiple A b⟩

/-! ### Augmented matrices (Theorem 8.2) -/

/-- The augmented matrix `[A | b]`: the coefficient matrix with the constants as last column. -/
def augmented {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (b i) (fun k => A i k) j

/-- Coefficient part of an augmented matrix (all columns but the last). -/
def coeffPart {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  M.submatrix id Fin.castSucc

/-- Constants column of an augmented matrix (the last column). -/
def constPart {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) : Fin m → ℝ :=
  fun i => M i (Fin.last n)

/-- Solution set of the system encoded by an augmented matrix. -/
def augSolutions {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) : Set (Fin n → ℝ) :=
  solutionSet (coeffPart M) (constPart M)

/-- The augmented matrix has the coefficients on the left and the constants on the right, and
`x` solves the system iff `[A | b]` kills the vector `(x, -1)` (PC-136). -/
@[kb "stitzzeager2013" "§8.2, p. 580"]
theorem augmented_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    coeffPart (augmented A b) = A ∧ constPart (augmented A b) = b ∧
    ∀ x : Fin n → ℝ, x ∈ solutionSet A b ↔
      augmented A b *ᵥ (Fin.snoc (α := fun _ => ℝ) x (-1)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [coeffPart, augmented]
  · funext i
    simp [constPart, augmented]
  · intro x
    have key : ∀ i, (augmented A b *ᵥ (Fin.snoc (α := fun _ => ℝ) x (-1))) i =
        (A *ᵥ x) i - b i := by
      intro i
      simp [mulVec, dotProduct, Fin.sum_univ_castSucc, augmented, Fin.snoc]
      ring
    show A *ᵥ x = b ↔ _
    constructor
    · intro h
      funext i
      rw [key, h]
      simp
    · intro h
      funext i
      have := congrFun h i
      rw [key] at this
      simpa [sub_eq_zero] using this

private lemma coeffPart_mul {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin (n + 1)) ℝ) : coeffPart (P * M) = P * coeffPart M := by
  ext i j
  simp [coeffPart, Matrix.mul_apply]

private lemma constPart_mul {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin m) (Fin (n + 1)) ℝ) : constPart (P * M) = P *ᵥ constPart M := by
  funext i
  simp [constPart, Matrix.mul_apply, mulVec, dotProduct]

/-- Left multiplication by an invertible matrix does not change the solution set. -/
theorem solutionSet_unit_mul {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (hP : IsUnit P)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    solutionSet (P * A) (P *ᵥ b) = solutionSet A b := by
  obtain ⟨Q, hQ⟩ := hP.exists_left_inv
  ext x
  simp only [solutionSet, Set.mem_ofPred_eq]
  rw [← mulVec_mulVec]
  constructor
  · intro h
    have e : ∀ v : Fin m → ℝ, Q *ᵥ (P *ᵥ v) = v := fun v => by
      rw [mulVec_mulVec, hQ, one_mulVec]
    have := congrArg (fun v => Q *ᵥ v) h
    simp only [e] at this
    exact this
  · intro h
    rw [h]

private lemma coeffPart_updateRow {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) (i : Fin m)
    (r : Fin (n + 1) → ℝ) :
    coeffPart (M.updateRow i r) = (coeffPart M).updateRow i (fun j => r (Fin.castSucc j)) := by
  ext i' j
  by_cases h : i' = i
  · subst h; simp [coeffPart]
  · simp [coeffPart, updateRow_ne h]

private lemma constPart_updateRow {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) (i : Fin m)
    (r : Fin (n + 1) → ℝ) :
    constPart (M.updateRow i r) = Function.update (constPart M) i (r (Fin.last n)) := by
  funext i'
  by_cases h : i' = i
  · subst h; simp [constPart]
  · simp [constPart, updateRow_ne h, Function.update_of_ne h]

/-- Row operations on an augmented matrix give an equivalent system: left multiplication by an
invertible matrix, and the three concrete operations (swap two rows, scale a row by a nonzero
number, add a multiple of one row to another row) (PC-133). -/
@[kb "stitzzeager2013" "Theorem 8.2, p. 580"]
theorem augmented_row_ops_equivalent {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    (∀ P : Matrix (Fin m) (Fin m) ℝ, IsUnit P → augSolutions (P * M) = augSolutions M) ∧
    (∀ σ : Equiv.Perm (Fin m), augSolutions (M.submatrix σ id) = augSolutions M) ∧
    (∀ (i : Fin m) (k : ℝ), k ≠ 0 → augSolutions (M.updateRow i (k • M i)) = augSolutions M) ∧
    (∀ (i j : Fin m), i ≠ j → ∀ k : ℝ,
      augSolutions (M.updateRow i (M i + k • M j)) = augSolutions M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    unfold augSolutions
    rw [coeffPart_mul, constPart_mul]
    exact solutionSet_unit_mul P hP _ _
  · intro σ
    exact solutionSet_swap (coeffPart M) (constPart M) σ
  · intro i k hk
    unfold augSolutions
    rw [coeffPart_updateRow, constPart_updateRow]
    exact solutionSet_scale (coeffPart M) (constPart M) i k hk
  · intro i j hij k
    unfold augSolutions
    rw [coeffPart_updateRow, constPart_updateRow]
    exact solutionSet_add_multiple (coeffPart M) (constPart M) i j hij k

/-! ### Echelon forms (Definitions 8.3-8.5) -/

/-- Row echelon form in the sense of the book: Mathlib's `IsRowEchelon` (each leading entry lies
strictly to the right of the leading entries above it, zero rows at the bottom) together with
every leading entry equal to `1`. -/
def IsRowEchelonForm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  A.IsRowEchelon ∧ ∀ i c, A.IsLeadingEntry i c → A i c = 1

/-- Triangular form of a system, stated through its coefficient matrix `A`: every leading
coefficient is `1`, equations with zero coefficients (the constant equations) come last, and the
leading variables strictly increase going down. -/
def IsTriangularSystem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i c, A.IsLeadingEntry i c → A i c = 1) ∧
  (∀ i₁ i₂, i₁ < i₂ → A i₁ = 0 → A i₂ = 0) ∧
  (∀ i₁ i₂ c₁ c₂, i₁ < i₂ → A.IsLeadingEntry i₁ c₁ → A.IsLeadingEntry i₂ c₂ → c₁ < c₂)

/-- In an echelon matrix, leading entries move strictly to the right going down. -/
theorem leading_lt_of_isRowEchelon {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsRowEchelon) {i₁ i₂ : Fin m} {c₁ c₂ : Fin n} (h : i₁ < i₂)
    (h₁ : A.IsLeadingEntry i₁ c₁) (h₂ : A.IsLeadingEntry i₂ c₂) : c₁ < c₂ := by
  by_contra hc
  push Not at hc
  exact h₂.2 (hA h fun j hj => h₁.1 j (lt_of_lt_of_le hj hc))

/-- A system is in triangular form exactly when its coefficient matrix is in row echelon form
(PC-132). -/
@[kb "stitzzeager2013" "Definition 8.3, p. 568"]
theorem isTriangularSystem_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsTriangularSystem A ↔ IsRowEchelonForm A := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1⟩
    intro i₁ i₂ hlt j₂ hj
    by_contra hne
    have hr2 : A i₂ ≠ 0 := fun h => hne (by simpa using congrFun h j₂)
    have hr1 : A i₁ ≠ 0 := fun h => hr2 (h2 _ _ hlt h)
    obtain ⟨c₁, hc₁⟩ := row_ne_zero_iff_exists_isLeadingEntry.1 hr1
    obtain ⟨c₂, hc₂⟩ := row_ne_zero_iff_exists_isLeadingEntry.1 hr2
    have hlt' := h3 i₁ i₂ c₁ c₂ hlt hc₁ hc₂
    have hle : c₂ ≤ j₂ := by
      by_contra hn
      push Not at hn
      exact hne (hc₂.1 j₂ hn)
    exact hc₁.2 (hj c₁ (lt_of_lt_of_le hlt' hle))
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun i₁ i₂ hlt h => h1.row_eq_zero_of_lt hlt h,
      fun i₁ i₂ c₁ c₂ hlt hc₁ hc₂ => leading_lt_of_isRowEchelon h1 hlt hc₁ hc₂⟩

/-- Row echelon form: leading entries are `1`, they move strictly right going down, and the zero
rows are at the bottom (PC-134). -/
@[kb "stitzzeager2013" "Definition 8.4, p. 581"]
theorem isRowEchelonForm_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsRowEchelonForm A ↔
      (∀ i c, A.IsLeadingEntry i c → A i c = 1) ∧
      (∀ i₁ i₂, i₁ < i₂ → A i₁ = 0 → A i₂ = 0) ∧
      (∀ i₁ i₂ c₁ c₂, i₁ < i₂ → A.IsLeadingEntry i₁ c₁ → A.IsLeadingEntry i₂ c₂ → c₁ < c₂) :=
  (isTriangularSystem_iff A).symm

/-- A reduced row echelon matrix (Mathlib's `Matrix.IsReducedRowEchelon`, whose leading entries
are `1` with only zeros above and below) is in row echelon form, and every column containing a
leading entry has zeros except for that entry. -/
theorem rref_isRowEchelonForm {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsReducedRowEchelon) :
    IsRowEchelonForm A ∧ ∀ i₁ i₂ c, A.IsLeadingEntry i₂ c → i₁ ≠ i₂ → A i₁ c = 0 :=
  ⟨⟨hA.isRowEchelon, fun _ _ h => hA.eq_one h⟩,
    fun _ _ _ h hne => hA.eq_zero_of_ne_of_isLeadingEntry hne h⟩

/-- A square reduced row echelon matrix with no zero row is the identity matrix (PC-135). -/
@[kb "stitzzeager2013" "Definition 8.5, p. 582"]
theorem rref_square_no_zero_row {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsReducedRowEchelon) (hrows : ∀ i, A i ≠ 0) : A = 1 := by
  have hex : ∀ i, ∃ c, A.IsLeadingEntry i c := fun i =>
    row_ne_zero_iff_exists_isLeadingEntry.1 (hrows i)
  choose c hc using hex
  have hmono : StrictMono c := fun i₁ i₂ h =>
    leading_lt_of_isRowEchelon hA.isRowEchelon h (hc i₁) (hc i₂)
  have hsurj : Function.Surjective c :=
    (Finite.injective_iff_surjective).1 hmono.injective
  have hid : ∀ i, c i = i := by
    intro i
    have e1 : (StrictMono.orderIsoOfSurjective c hmono hsurj) = OrderIso.refl (Fin n) :=
      Subsingleton.elim _ _
    have := congrArg (fun e => e i) e1
    simpa using this
  ext i j
  by_cases hij : i = j
  · subst hij
    have := hA.eq_one (hc i)
    rw [hid] at this
    simpa using this
  · have := hA.eq_zero_of_ne_of_isLeadingEntry hij (hc j)
    rw [hid] at this
    simpa [Matrix.one_apply_ne hij] using this

/-! ### Gauss-Jordan elimination -/

private lemma exists_unit_addRow {m q : ℕ} (u : Fin m → ℝ) (k : Fin m) (hk : u k = 0) :
    ∃ E : Matrix (Fin m) (Fin m) ℝ, IsUnit E ∧
      ∀ (N : Matrix (Fin m) (Fin q) ℝ) (i : Fin m) (j : Fin q), (E * N) i j = N i j + u i * N k j := by
  set w : Fin m → ℝ := Pi.single k 1 with hw
  have hwu : w ⬝ᵥ u = 0 := by simp [hw, hk]
  have hXX : vecMulVec u w * vecMulVec u w = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwu]
    ext i j
    simp [vecMulVec]
  refine ⟨1 + vecMulVec u w, ⟨⟨1 + vecMulVec u w, 1 - vecMulVec u w, ?_, ?_⟩, rfl⟩, ?_⟩
  · have : (1 + vecMulVec u w) * (1 - vecMulVec u w) = 1 - vecMulVec u w * vecMulVec u w := by
      noncomm_ring
    rw [this, hXX, sub_zero]
  · have : (1 - vecMulVec u w) * (1 + vecMulVec u w) = 1 - vecMulVec u w * vecMulVec u w := by
      noncomm_ring
    rw [this, hXX, sub_zero]
  · intro N i j
    have hN : (1 + vecMulVec u w) * N = N + vecMulVec u (w ᵥ* N) := by
      rw [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul]
    rw [hN]
    simp [vecMulVec, vecMul, dotProduct, hw, Pi.single_apply]

private lemma pivot_clear {m n : ℕ} (B : Matrix (Fin m) (Fin (n + 1)) ℝ) (i₁ i₀ : Fin m)
    (h1 : ∀ j, B i₁ (Fin.castSucc j) = 0) (h0 : ∀ j, B i₀ (Fin.castSucc j) = 0)
    (hc : B i₀ (Fin.last n) ≠ 0) :
    ∃ E : Matrix (Fin m) (Fin m) ℝ, IsUnit E ∧ ∀ i,
      (∀ j, (E * B) i (Fin.castSucc j) = B i (Fin.castSucc j)) ∧
      (E * B) i (Fin.last n) = if i = i₁ then 1 else 0 := by
  obtain ⟨E1, hE1, hB1c, hB1o, hB1l⟩ : ∃ E1 : Matrix (Fin m) (Fin m) ℝ, IsUnit E1 ∧
      (∀ i j, (E1 * B) i (Fin.castSucc j) = B i (Fin.castSucc j)) ∧
      (∀ i, i ≠ i₁ → ∀ j, (E1 * B) i j = B i j) ∧ (E1 * B) i₁ (Fin.last n) ≠ 0 := by
    by_cases hz : B i₁ (Fin.last n) = 0
    · have hne : i₀ ≠ i₁ := by
        rintro rfl
        exact hc hz
      obtain ⟨E1, hE1, hE1e⟩ := exists_unit_addRow (m := m) (q := n + 1)
        (Pi.single i₁ (1 : ℝ)) i₀ (by simp [Pi.single_eq_of_ne hne])
      refine ⟨E1, hE1, ?_, ?_, ?_⟩
      · intro i j
        rw [hE1e]
        by_cases hi : i = i₁
        · subst hi
          simp [h1, h0]
        · simp [Pi.single_eq_of_ne hi]
      · intro i hi j
        rw [hE1e]
        simp [Pi.single_eq_of_ne hi]
      · rw [hE1e]
        simp [hz, hc]
    · exact ⟨1, isUnit_one, by simp, by simp, by simpa using hz⟩
  have hs : (E1 * B) i₁ (Fin.last n) ≠ 0 := hB1l
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ((E1 * B) i₁ (Fin.last n))⁻¹ := ⟨_, rfl⟩
  have hsne : s ≠ 0 := by rw [hsdef]; exact inv_ne_zero hs
  have hss : s * (E1 * B) i₁ (Fin.last n) = 1 := by rw [hsdef]; exact inv_mul_cancel₀ hs
  set E2 : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (Function.update (1 : Fin m → ℝ) i₁ s)
    with hE2def
  have hE2 : IsUnit E2 := by
    rw [hE2def, Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    by_cases hi : i = i₁
    · subst hi
      simp [isUnit_iff_ne_zero, hsne]
    · simp [Function.update_of_ne hi]
  have hE2e : ∀ (N : Matrix (Fin m) (Fin (n + 1)) ℝ) i j,
      (E2 * N) i j = (if i = i₁ then s else 1) * N i j := by
    intro N i j
    simp [hE2def, Matrix.diagonal_mul, Function.update_apply]
  have hB2c : ∀ i j, (E2 * (E1 * B)) i (Fin.castSucc j) = B i (Fin.castSucc j) := by
    intro i j
    rw [hE2e]
    by_cases hi : i = i₁
    · subst hi
      simp [hB1c, h1]
    · simp [hi, hB1c]
  have hB2l : (E2 * (E1 * B)) i₁ (Fin.last n) = 1 := by
    rw [hE2e]
    simpa using hss
  obtain ⟨E3, hE3, hE3e⟩ := exists_unit_addRow (m := m) (q := n + 1)
    (fun i => if i = i₁ then 0 else -(E2 * (E1 * B)) i (Fin.last n)) i₁ (by simp)
  refine ⟨E3 * (E2 * E1), hE3.mul (hE2.mul hE1), fun i => ?_⟩
  have hassoc : (E3 * (E2 * E1)) * B = E3 * (E2 * (E1 * B)) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  refine ⟨fun j => ?_, ?_⟩
  · rw [hE3e, hB2c i₁ j, h1, hB2c i j]
    simp
  · by_cases hi : i = i₁
    · subst hi
      rw [hE3e, hB2l]
      simp
    · rw [hE3e, hB2l]
      simp [hi]

private lemma rref_ext {m n : ℕ} (F : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hR : (F.submatrix id Fin.castSucc).IsReducedRowEchelon)
    (H1 : ∀ i i', i < i' → (∀ j, F i (Fin.castSucc j) = 0) → F i' (Fin.last n) = 0)
    (H2 : ∀ i, (∀ j, F i (Fin.castSucc j) = 0) → F i (Fin.last n) ≠ 0 → F i (Fin.last n) = 1)
    (H3 : ∀ i i', i < i' → (∀ j, F i' (Fin.castSucc j) = 0) → F i' (Fin.last n) ≠ 0 →
      F i (Fin.last n) = 0) :
    F.IsReducedRowEchelon := by
  have lead_cs : ∀ i (c : Fin n), F.IsLeadingEntry i (Fin.castSucc c) ↔
      (F.submatrix id Fin.castSucc).IsLeadingEntry i c := by
    intro i c
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j hj => h1 (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 hj), h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun j hj => ?_, h2⟩
      induction j using Fin.lastCases with
      | last => exact absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le)
      | cast j => exact h1 j (Fin.castSucc_lt_castSucc_iff.1 hj)
  have lead_last : ∀ i, F.IsLeadingEntry i (Fin.last n) ↔
      (∀ j, F i (Fin.castSucc j) = 0) ∧ F i (Fin.last n) ≠ 0 := by
    intro i
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j => h1 _ (Fin.castSucc_lt_last j), h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun j hj => ?_, h2⟩
      induction j using Fin.lastCases with
      | last => exact absurd hj (lt_irrefl _)
      | cast j => exact h1 j
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hlt j₂ hj
    induction j₂ using Fin.lastCases with
    | last => exact H1 i₁ i₂ hlt (fun j => hj (Fin.castSucc j) (Fin.castSucc_lt_last j))
    | cast j₂ =>
      exact hR.isRowEchelon hlt fun j₁ hj₁ =>
        hj (Fin.castSucc j₁) (Fin.castSucc_lt_castSucc_iff.2 hj₁)
  · intro i c hc
    induction c using Fin.lastCases with
    | last =>
      obtain ⟨hz, hne⟩ := (lead_last i).1 hc
      exact H2 i hz hne
    | cast c => exact hR.eq_one ((lead_cs i c).1 hc)
  · intro i₁ i₂ c hlt hc
    induction c using Fin.lastCases with
    | last =>
      obtain ⟨hz, hne⟩ := (lead_last i₂).1 hc
      exact H3 i₁ i₂ hlt hz hne
    | cast c => exact hR.eq_zero hlt ((lead_cs i₂ c).1 hc)

private lemma rref_extend {m n : ℕ} (B : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hR : (B.submatrix id Fin.castSucc).IsReducedRowEchelon) :
    ∃ E : Matrix (Fin m) (Fin m) ℝ, IsUnit E ∧ (E * B).IsReducedRowEchelon := by
  classical
  have hup : ∀ i₁ i₂, i₁ < i₂ → (∀ j, B i₁ (Fin.castSucc j) = 0) →
      ∀ j, B i₂ (Fin.castSucc j) = 0 := by
    intro i₁ i₂ hlt hz j
    exact hR.isRowEchelon hlt (j₂ := j) (fun j₁ _ => hz j₁)
  by_cases hcase : ∃ i₀, (∀ j, B i₀ (Fin.castSucc j) = 0) ∧ B i₀ (Fin.last n) ≠ 0
  · obtain ⟨i₀, h0, hc⟩ := hcase
    have hne : (Finset.univ.filter fun i => ∀ j, B i (Fin.castSucc j) = 0).Nonempty :=
      ⟨i₀, by simpa using h0⟩
    obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image _ id hne
    have h1 : ∀ j, B i₁ (Fin.castSucc j) = 0 := by simpa using hi₁
    have hmin' : ∀ i, (∀ j, B i (Fin.castSucc j) = 0) → i₁ ≤ i := fun i hi =>
      hmin i (by simpa using hi)
    obtain ⟨E, hE, hEe⟩ := pivot_clear B i₁ i₀ h1 h0 hc
    refine ⟨E, hE, ?_⟩
    have hsub : (E * B).submatrix id Fin.castSucc = B.submatrix id Fin.castSucc := by
      ext i j
      exact (hEe i).1 j
    apply rref_ext (E * B) (by rw [hsub]; exact hR)
    · intro i i' hlt hz
      rw [(hEe i').2]
      have : i₁ ≤ i := hmin' i (fun j => by rw [← (hEe i).1 j]; exact hz j)
      have : i' ≠ i₁ := ne_of_gt (lt_of_le_of_lt this hlt)
      simp [this]
    · intro i _ hne'
      rw [(hEe i).2] at hne' ⊢
      by_cases hi : i = i₁
      · simp [hi]
      · simp [hi] at hne'
    · intro i i' hlt _ hne'
      rw [(hEe i').2] at hne'
      have hi' : i' = i₁ := by
        by_contra h
        simp [h] at hne'
      rw [(hEe i).2]
      have : i ≠ i₁ := by
        rw [← hi'] at *
        exact ne_of_lt hlt
      simp [this]
  · push Not at hcase
    refine ⟨1, isUnit_one, ?_⟩
    rw [Matrix.one_mul]
    refine rref_ext B hR ?_ ?_ ?_
    · intro i i' hlt hz
      exact hcase i' (hup i i' hlt hz)
    · intro i hz hne'
      exact absurd (hcase i hz) hne'
    · intro i i' _ hz hne'
      exact absurd (hcase i' hz) hne'

/-- Existence of reduced row echelon form: every real matrix is turned into a reduced row
echelon matrix by left multiplication with an invertible matrix (a product of elementary row
operations). -/
theorem exists_unit_mul_isReducedRowEchelon {m : ℕ} :
    ∀ (n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
      ∃ P : Matrix (Fin m) (Fin m) ℝ, IsUnit P ∧ (P * A).IsReducedRowEchelon := by
  intro n
  induction n with
  | zero =>
    intro A
    refine ⟨1, isUnit_one, ?_⟩
    rw [Matrix.one_mul]
    exact ⟨fun _ _ _ j₂ => j₂.elim0, fun _ c => c.elim0, fun _ _ c => c.elim0⟩
  | succ n ih =>
    intro A
    obtain ⟨P, hP, hRP⟩ := ih (A.submatrix id Fin.castSucc)
    have hB : (P * A).submatrix id Fin.castSucc = P * A.submatrix id Fin.castSucc := by
      ext i j
      simp [Matrix.mul_apply]
    obtain ⟨E, hE, hEB⟩ := rref_extend (P * A) (by rw [hB]; exact hRP)
    exact ⟨E * P, hE.mul hP, by rw [Matrix.mul_assoc]; exact hEB⟩

/-- Gauss-Jordan elimination: every system (augmented matrix) can be brought by invertible row
operations to a matrix in reduced row echelon form, without changing its solution set; the
same holds for a bare matrix (PC-137). -/
@[kb "stitzzeager2013" "§8.2, p. 583"]
theorem gauss_jordan {m n : ℕ} (M : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, IsUnit P ∧ (P * M).IsReducedRowEchelon ∧
      IsRowEchelonForm (P * M) ∧ augSolutions (P * M) = augSolutions M := by
  obtain ⟨P, hP, hR⟩ := exists_unit_mul_isReducedRowEchelon (m := m) (n + 1) M
  exact ⟨P, hP, hR, (rref_isRowEchelonForm hR).1,
    (augmented_row_ops_equivalent M).1 P hP⟩

end UndergradKB.Precalculus
