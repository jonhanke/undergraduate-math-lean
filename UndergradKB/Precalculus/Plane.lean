import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Data.Set.Prod
import UndergradKB.Common.Attr

/-!
# The Cartesian plane (Stitz–Zeager, Precalculus, Chapter 1)

The plane is modelled as `ℝ × ℝ`; a relation is a `Set (ℝ × ℝ)`; the graph of a function
`f` over a domain `D` is Mathlib's `Set.graphOn f D`. Distances use `EuclideanSpace ℝ (Fin 2)`
since the product metric on `ℝ × ℝ` is the sup metric.
-/

namespace UndergradKB.Precalculus

open UndergradKB

/-! ### Symmetry of points (PC-004) -/

/-- `q` is the mirror image of `p` in the x-axis. -/
def PtSymmX (p q : ℝ × ℝ) : Prop := q = (p.1, -p.2)

/-- `q` is the mirror image of `p` in the y-axis. -/
def PtSymmY (p q : ℝ × ℝ) : Prop := q = (-p.1, p.2)

/-- `q` is the mirror image of `p` through the origin. -/
def PtSymmO (p q : ℝ × ℝ) : Prop := q = (-p.1, -p.2)

/-- Symmetry of two points about the x-axis, y-axis, origin in coordinates (PC-004). -/
@[kb "stitzzeager2013" "Definition 1.3, p. 21"]
theorem pt_symm_coordinates (a b c d : ℝ) :
    (PtSymmX (a, b) (c, d) ↔ c = a ∧ d = -b) ∧
    (PtSymmY (a, b) (c, d) ↔ c = -a ∧ d = b) ∧
    (PtSymmO (a, b) (c, d) ↔ c = -a ∧ d = -b) := by
  simp [PtSymmX, PtSymmY, PtSymmO, Prod.ext_iff]

/-- Point symmetry is a symmetric relation (swap the two points) (PC-004). -/
@[kb "stitzzeager2013" "Definition 1.3, p. 21"]
theorem pt_symm_comm (p q : ℝ × ℝ) :
    (PtSymmX p q ↔ PtSymmX q p) ∧ (PtSymmY p q ↔ PtSymmY q p) ∧ (PtSymmO p q ↔ PtSymmO q p) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [PtSymmX, PtSymmY, PtSymmO, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Distance and midpoint (PC-005, PC-006, PC-007) -/

/-- The distance formula in the Euclidean plane (PC-005). -/
@[kb "stitzzeager2013" "Equation 1.1, p. 23"]
theorem plane_dist_formula (x₀ y₀ x₁ y₁ : ℝ) :
    dist (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) !₂[x₁, y₁] =
      √((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ring

/-- The midpoint of two points of the plane has coordinates the averages (PC-006). -/
@[kb "stitzzeager2013" "Equation 1.2, p. 25"]
theorem plane_midpoint_formula (x₀ y₀ x₁ y₁ : ℝ) :
    midpoint ℝ (x₀, y₀) (x₁, y₁) = ((x₀ + x₁) / 2, (y₀ + y₁) / 2) := by
  ext <;> simp [midpoint_eq_smul_add] <;> ring

/-- The coordinate midpoint is equidistant from the two endpoints, each at half the distance
between them, in the Euclidean plane (PC-006). -/
@[kb "stitzzeager2013" "Equation 1.2, p. 25"]
theorem plane_midpoint_equidistant (x₀ y₀ x₁ y₁ : ℝ) :
    let M : EuclideanSpace ℝ (Fin 2) := !₂[(x₀ + x₁) / 2, (y₀ + y₁) / 2]
    dist (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) M = dist M !₂[x₁, y₁] ∧
      dist (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) M =
        dist (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) !₂[x₁, y₁] / 2 := by
  intro M
  have hM : M = midpoint ℝ (!₂[x₀, y₀] : EuclideanSpace ℝ (Fin 2)) !₂[x₁, y₁] := by
    ext i
    fin_cases i <;> simp [M, midpoint_eq_smul_add] <;> ring
  rw [hM]
  refine ⟨(dist_left_midpoint_eq_dist_right_midpoint _ _).trans (dist_comm _ _), ?_⟩
  rw [dist_left_midpoint]
  simp [div_eq_inv_mul]

/-- The line `y = x` bisects the segment from `(a, b)` to `(b, a)`: the midpoint lies on the
line, and the line's points are equidistant from the endpoints (PC-007). -/
@[kb "stitzzeager2013" "Example 1.1.7, p. 25"]
theorem plane_diagonal_bisects (a b : ℝ) :
    midpoint ℝ (a, b) (b, a) = ((a + b) / 2, (a + b) / 2) ∧
      (∀ t : ℝ, dist (!₂[t, t] : EuclideanSpace ℝ (Fin 2)) !₂[a, b] =
        dist (!₂[t, t] : EuclideanSpace ℝ (Fin 2)) !₂[b, a]) := by
  refine ⟨?_, fun t => ?_⟩
  · rw [plane_midpoint_formula, add_comm b a]
  · rw [plane_dist_formula, plane_dist_formula]
    congr 1
    ring

/-! ### Lines and symmetry of graphs (PC-009, PC-012) -/

/-- The graph of `x = a` is the vertical line through `(a, t)` for all `t`; the graph of
`y = b` is the horizontal line through `(t, b)` for all `t` (PC-009). -/
@[kb "stitzzeager2013" "§1.2, p. 35"]
theorem graph_vertical_horizontal_line (a b : ℝ) :
    {p : ℝ × ℝ | p.1 = a} = Set.range (fun t : ℝ => (a, t)) ∧
      {p : ℝ × ℝ | p.2 = b} = Set.range (fun t : ℝ => (t, b)) := by
  constructor
  · ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq]
    constructor
    · rintro rfl; exact ⟨y, rfl, rfl⟩
    · rintro ⟨t, h1, -⟩; exact h1.symm
  · ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq]
    constructor
    · rintro rfl; exact ⟨x, rfl, rfl⟩
    · rintro ⟨t, -, h2⟩; exact h2.symm

/-- A set of points is symmetric about the x-axis. -/
def SymmetricX (S : Set (ℝ × ℝ)) : Prop := ∀ p ∈ S, (p.1, -p.2) ∈ S

/-- A set of points is symmetric about the y-axis. -/
def SymmetricY (S : Set (ℝ × ℝ)) : Prop := ∀ p ∈ S, (-p.1, p.2) ∈ S

/-- A set of points is symmetric about the origin. -/
def SymmetricO (S : Set (ℝ × ℝ)) : Prop := ∀ p ∈ S, (-p.1, -p.2) ∈ S

/-- Symmetry test: if replacing `x` by `-x` (resp. `y` by `-y`, both) gives an equivalent
equation, the graph is symmetric about the y-axis (resp. x-axis, origin) (PC-012). -/
@[kb "stitzzeager2013" "§1.2, p. 38"]
theorem symmetry_test (E : ℝ → ℝ → Prop) :
    ((∀ x y, E x y ↔ E (-x) y) → SymmetricY {p | E p.1 p.2}) ∧
    ((∀ x y, E x y ↔ E x (-y)) → SymmetricX {p | E p.1 p.2}) ∧
    ((∀ x y, E x y ↔ E (-x) (-y)) → SymmetricO {p | E p.1 p.2}) := by
  refine ⟨fun h p hp => ?_, fun h p hp => ?_, fun h p hp => ?_⟩
  · exact (h p.1 p.2).1 hp
  · exact (h p.1 p.2).1 hp
  · exact (h p.1 p.2).1 hp

/-! ### Functions as relations (PC-014, PC-015) -/

/-- Vertical Line Test: a set of points is the graph of a function over some domain exactly when
every vertical line meets it in at most one point (PC-014). -/
@[kb "stitzzeager2013" "Theorem 1.1, p. 55"]
theorem vertical_line_test (S : Set (ℝ × ℝ)) :
    (∃ (f : ℝ → ℝ) (D : Set ℝ), S = Set.graphOn f D) ↔
      ∀ a : ℝ, (S ∩ {p | p.1 = a}).Subsingleton := by
  classical
  constructor
  · rintro ⟨f, D, rfl⟩ a p ⟨hp, hpa⟩ q ⟨hq, hqa⟩
    rw [Set.mem_graphOn] at hp hq
    ext
    · rw [hpa, hqa]
    · rw [← hp.2, ← hq.2, hpa, hqa]
  · intro h
    refine ⟨fun x => if hx : ∃ y, (x, y) ∈ S then hx.choose else 0, Prod.fst '' S, ?_⟩
    ext ⟨x, y⟩
    rw [Set.mem_graphOn]
    simp only [Set.mem_image]
    constructor
    · intro hxy
      have hex : ∃ y, (x, y) ∈ S := ⟨y, hxy⟩
      refine ⟨⟨(x, y), hxy, rfl⟩, ?_⟩
      simp only [hex, dite_true]
      exact (h x ⟨hex.choose_spec, rfl⟩ ⟨hxy, rfl⟩ |> congrArg Prod.snd)
    · rintro ⟨⟨⟨x', y'⟩, hS, hx⟩, hf⟩
      simp only at hx
      subst hx
      have hex : ∃ y, (x', y) ∈ S := ⟨y', hS⟩
      simp only [hex, dite_true] at hf
      rw [← hf]
      exact hex.choose_spec

/-- The domain of a relation: the set of first coordinates of its points. -/
def relDomain (S : Set (ℝ × ℝ)) : Set ℝ := Prod.fst '' S

/-- The range of a relation: the set of second coordinates of its points. -/
def relRange (S : Set (ℝ × ℝ)) : Set ℝ := Prod.snd '' S

/-- For the graph of a function over a domain `D`, the first coordinates form `D` and the second
coordinates form the range `f '' D` (PC-015). -/
@[kb "stitzzeager2013" "Definition 1.7, p. 57"]
theorem relDomain_relRange_graphOn (f : ℝ → ℝ) (D : Set ℝ) :
    relDomain (Set.graphOn f D) = D ∧ relRange (Set.graphOn f D) = f '' D :=
  ⟨Set.image_fst_graphOn f D, Set.image_snd_graphOn f⟩

end UndergradKB.Precalculus
