import UndergradKB.RepresentationTheory.Roots
import UndergradKB.RepresentationTheory.RootsA
import Mathlib.Algebra.Order.Star.Real
import UndergradKB.Common.Attr

/-! # Dynkin and affine Dynkin diagrams: positive (semi)definiteness (Etingof et al., Problem 5.3)

For a graph `G` on `Fin n` the form `B(x, x) = xᵀ (2 I - adjacency) x` is the quadratic form of
`Roots.lean`.  Here we verify, for explicit graphs, whether it is positive definite or only positive
semidefinite.

* `graphOfCartan M`: the graph of an integer matrix `M`, with an edge where the off-diagonal entry is `-1`;
  `cartanMatrix_graphOfCartan` shows it recovers `M` for symmetric `M` with diagonal `2` and off-diagonal
  entries in `{0, -1}`.  Hence Mathlib's matrices `CartanMatrix.A`, `D`, `E` are Cartan matrices of graphs
  (`cartanMatrix_D_eq`, `cartanMatrix_E_eq`, and `cartanMatrix_pathGraph` in `Roots.lean`).
* Finite diagrams (Problem 5.3, existence half of the classification): the forms of `A_n`
  (`posDefinite_pathGraph`), `D_n` (`posDefinite_D`), `E_6`, `E_7`, `E_8` are positive definite, and these
  graphs are connected, so they are Dynkin diagrams (`isDynkin_pathGraph`, `isDynkin_D`, `isDynkin_E6`, ...).
* Affine diagrams (Problem 5.3(g)): the cycle `Ã_n`, the star `D̃_4` and the diagrams `Ẽ_6`, `Ẽ_7`, `Ẽ_8` have
  positive semidefinite, not definite, forms whose kernel is a line spanned by an explicit vector with
  positive entries (`IsAffineKernel`, `affine_cycle`, `affine_D4`, `affine_E6`, `affine_E7`, `affine_E8`).
* Forbidden subgraphs: `PosDefinite.of_embedding` (the form of a subgraph of a positive definite graph is
  positive definite) gives `PosDefinite.not_embed_affine`, `not_embed_cycle`, `not_embed_D4`: a positive definite
  graph contains no cycle and no vertex with four pairwise distinct neighbours.
* Not formalized: the converse direction of the classification (a connected graph with positive definite form
  is one of `A_n`, `D_n`, `E_6`, `E_7`, `E_8`).  Missing ingredients: the affine diagrams `D̃_n` for `n > 4`
  (two branch points), the forbidden-subgraph argument for trees with a branch point (arm lengths `p, q, r`
  forcing `D_n`, `E_6`, `E_7`, `E_8`, otherwise containing `Ẽ_6`, `Ẽ_7`, `Ẽ_8`), and the fact that a connected
  tree with no vertex of degree 4 etc. is determined by its arm lengths.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix Finset

/-- The simple graph whose edges join the distinct indices where an integer matrix has entry `-1`
in both orders. -/
def graphOfCartan {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ M i j = -1 ∧ M j i = -1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : DecidableRel (graphOfCartan M).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ M i j = -1 ∧ M j i = -1))

theorem cartanMatrix_graphOfCartan {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hd : ∀ i, M i i = 2)
    (hs : ∀ i j, M i j = M j i) (ho : ∀ i j, i ≠ j → M i j = 0 ∨ M i j = -1) :
    cartanMatrix (graphOfCartan M) = M := by
  ext i j
  rw [cartanMatrix_apply]
  by_cases h : i = j
  · subst h; simp [hd]
  · rcases ho i j h with h0 | h0
    · have : ¬ (graphOfCartan M).Adj i j := fun hh => by have := hh.2.1; omega
      simp [h, this, h0]
    · have : (graphOfCartan M).Adj i j := ⟨h, h0, by rw [← hs]; exact h0⟩
      simp [h, this, h0]

/-- The real Cartan matrix of a graph. -/
abbrev cartanReal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  (cartanMatrix G).map (Int.cast : ℤ → ℝ)

theorem cartanReal_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (cartanReal G).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by simp [cartanMatrix_symm G i j]

theorem posDef_of_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ x, x ⬝ᵥ (M *ᵥ x) = q x) (hpos : ∀ x, x ≠ 0 → 0 < q x) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hM, fun x hx => ?_⟩
  simp only [star_trivial]
  rw [hq]
  exact hpos x hx

theorem posDef_of_sos {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (w : Fin k → ℝ)
    (hw : ∀ j, 0 < w j) (l : (Fin n → ℝ) → Fin k → ℝ)
    (hq : ∀ x, x ⬝ᵥ (M *ᵥ x) = ∑ j, w j * (l x j) ^ 2)
    (hinj : ∀ x, (∀ j, l x j = 0) → x = 0) : M.PosDef := by
  refine posDef_of_pos M hM _ hq fun x hx => ?_
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ w j * (l x j) ^ 2 := fun j _ => mul_nonneg (hw j).le (sq_nonneg _)
  rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    apply hinj
    intro j
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm j (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (hw j).ne'
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h1

theorem posDefinite_of_pos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : (Fin n → ℝ) → ℝ) (hq : ∀ x, x ⬝ᵥ (cartanReal G *ᵥ x) = q x)
    (hpos : ∀ x, x ≠ 0 → 0 < q x) : PosDefinite G :=
  posDef_of_pos _ (cartanReal_isHermitian G) q hq hpos

theorem posDefinite_of_sos {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin k → ℝ)
    (hw : ∀ j, 0 < w j) (l : (Fin n → ℝ) → Fin k → ℝ)
    (hq : ∀ x, x ⬝ᵥ (cartanReal G *ᵥ x) = ∑ j, w j * (l x j) ^ 2)
    (hinj : ∀ x, (∀ j, l x j = 0) → x = 0) : PosDefinite G :=
  posDef_of_sos _ (cartanReal_isHermitian G) w hw l hq hinj

/-! ### Connectedness -/

theorem connected_of_parent {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) (p : Fin n → ℕ)
    (h : ∀ i, i ≠ r → ∃ j, G.Adj i j ∧ p j < p i) : G.Connected := by
  have key : ∀ m, ∀ i, p i = m → G.Reachable i r := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      by_cases hir : i = r
      · subst hir; exact SimpleGraph.Reachable.refl _
      · obtain ⟨j, hj, hlt⟩ := h i hir
        exact (SimpleGraph.Adj.reachable hj).trans (ih (p j) (hi ▸ hlt) j rfl)
  exact (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨r, fun i => (key _ i rfl).symm⟩

/-! ### Real quadratic forms through natural-number indexing -/

/-- A real vector on `Fin n` extended by zero to a sequence indexed by `ℕ`. -/
def extR {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then x ⟨i, h⟩ else 0

theorem extR_fin {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : extR x i.val = x i := by simp [extR]

theorem extR_of_le {n : ℕ} (x : Fin n → ℝ) {i : ℕ} (h : n ≤ i) : extR x i = 0 := by
  simp [extR, not_lt.2 h]

theorem eq_zero_of_extR {n : ℕ} (x : Fin n → ℝ) (h : ∀ i, extR x i = 0) : x = 0 := by
  funext i
  have := h i.val
  rwa [extR_fin] at this

theorem dot_cartanReal_eq_range {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (N : ℕ → ℕ → ℤ)
    (hN : ∀ i j : Fin n, M i j = N i j) (x : Fin n → ℝ) :
    x ⬝ᵥ ((M.map (Int.cast : ℤ → ℝ)) *ᵥ x) =
      ∑ a ∈ range n, ∑ b ∈ range n, extR x a * (N a b : ℝ) * extR x b := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range n, extR x a * (N a b : ℝ) * extR x b) n]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => extR x a.val * (N a.val b : ℝ) * extR x b) n]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [extR_fin, extR_fin, ← hN]
  simp only [Matrix.map_apply]
  ring

/-! ### Type `A_n` -/

/-- The truncated quadratic form of `A` on real sequences. -/
def quadR (z : ℕ → ℝ) (m : ℕ) : ℝ := ∑ a ∈ range m, ∑ b ∈ range m, z a * (cartanA a b : ℝ) * z b

theorem quadR_one (z : ℕ → ℝ) : quadR z 1 = 2 * z 0 ^ 2 := by
  simp [quadR, cartanA]; ring

theorem quadR_succ (z : ℕ → ℝ) (m : ℕ) :
    quadR z (m + 2) = quadR z (m + 1) + 2 * z (m + 1) ^ 2 - 2 * z m * z (m + 1) := by
  have hcol : ∑ a ∈ range (m + 1), z a * (cartanA a (m + 1) : ℝ) * z (m + 1) = - (z m * z (m + 1)) := by
    rw [Finset.sum_eq_single m]
    · simp [cartanA]
    · intro a ha hne
      simp only [mem_range] at ha
      have h1 : ¬ (a = m + 1) := by omega
      have h2 : ¬ (a + 1 = m + 1 ∨ m + 1 + 1 = a) := by omega
      simp only [cartanA, h1, h2, ite_false, Int.cast_zero, mul_zero, zero_mul]
    · intro h; simp at h
  have hrow : ∑ b ∈ range (m + 1), z (m + 1) * (cartanA (m + 1) b : ℝ) * z b = - (z (m + 1) * z m) := by
    rw [Finset.sum_eq_single m]
    · simp [cartanA]
    · intro b hb hne
      simp only [mem_range] at hb
      have h1 : ¬ (m + 1 = b) := by omega
      have h2 : ¬ (m + 1 + 1 = b ∨ b + 1 = m + 1) := by omega
      simp only [cartanA, h1, h2, ite_false, Int.cast_zero, mul_zero, zero_mul]
    · intro h; simp at h
  have hdiag : (cartanA (m + 1) (m + 1) : ℝ) = 2 := by simp [cartanA]
  unfold quadR
  simp only [Finset.sum_range_succ (n := m + 1), Finset.sum_add_distrib, hcol, hrow, hdiag]
  ring

theorem quadR_closed (z : ℕ → ℝ) (m : ℕ) :
    quadR z (m + 1) = z 0 ^ 2 + ∑ a ∈ range m, (z (a + 1) - z a) ^ 2 + z m ^ 2 := by
  induction m with
  | zero => rw [quadR_one]; simp; ring
  | succ m ih =>
    rw [quadR_succ, ih, Finset.sum_range_succ]
    ring

theorem dot_pathGraph (n : ℕ) (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (cartanReal (SimpleGraph.pathGraph (n + 1)) *ᵥ x) =
      extR x 0 ^ 2 + ∑ a ∈ range n, (extR x (a + 1) - extR x a) ^ 2 + extR x n ^ 2 := by
  unfold cartanReal
  rw [dot_cartanReal_eq_range _ cartanA (fun i j => cartanMatrix_pathGraph_apply i j)]
  exact quadR_closed _ n

/-- The form of `A_n` (the path graph) is positive definite. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem posDefinite_pathGraph (n : ℕ) : PosDefinite (SimpleGraph.pathGraph n) := by
  cases n with
  | zero =>
    exact posDefinite_of_pos _ (fun _ => 0) (fun x => by simp)
      (fun x hx => absurd (Subsingleton.elim x 0) hx)
  | succ n =>
    refine posDefinite_of_pos _ _ (dot_pathGraph n) fun x hx => ?_
    set z := extR x with hz
    have hnn : 0 ≤ ∑ a ∈ range n, (z (a + 1) - z a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    have h1 := sq_nonneg (z 0)
    have h2 := sq_nonneg (z n)
    rcases (add_nonneg (add_nonneg h1 hnn) h2).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hx
      have e0 : z 0 = 0 := by nlinarith
      have e1 : ∑ a ∈ range n, (z (a + 1) - z a) ^ 2 = 0 := by nlinarith
      have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (z (a + 1) - z a))).1 e1
      have step : ∀ a, a ≤ n → z a = 0 := by
        intro a
        induction a with
        | zero => intro _; exact e0
        | succ a ih =>
          intro ha
          have := e2 a (Finset.mem_range.2 (by omega))
          have := pow_eq_zero_iff (two_ne_zero) |>.1 this
          have := ih (by omega)
          linarith
      apply eq_zero_of_extR
      intro i
      by_cases hi : i ≤ n
      · exact step i hi
      · exact extR_of_le x (by omega)

/-! ### Type `D_n` -/

/-- The entries of Mathlib's matrix `CartanMatrix.D n` as a function of natural-number indices. -/
def dN (n a b : ℕ) : ℤ :=
  if a = b then 2
  else if n ≤ 2 then 0
  else if a + 1 = b ∧ b + 2 < n then -1
  else if b + 1 = a ∧ a + 2 < n then -1
  else if a + 3 = n ∧ (b + 2 = n ∨ b + 1 = n) then -1
  else if b + 3 = n ∧ (a + 2 = n ∨ a + 1 = n) then -1
  else 0

theorem D_apply (n : ℕ) (i j : Fin n) : CartanMatrix.D n i j = dN n i j := by
  simp [CartanMatrix.D, dN, Fin.ext_iff]

theorem cartanMatrix_D_eq (m : ℕ) :
    cartanMatrix (graphOfCartan (CartanMatrix.D m)) = CartanMatrix.D m := by
  refine cartanMatrix_graphOfCartan _ (fun i => by simp) (fun i j => ?_) (fun i j hij => ?_)
  · have := congrFun (congrFun (CartanMatrix.D_transpose m) i) j
    simpa [Matrix.transpose_apply] using this.symm
  · rw [D_apply]
    unfold dN
    have : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp only [this, ite_false]
    split_ifs <;> simp

theorem dN_eq_cartanA (k a b : ℕ) (ha : a < k + 1) (hb : b < k + 1) :
    dN (k + 1 + 1 + 1) a b = cartanA a b := by
  unfold dN cartanA
  split_ifs <;> omega

theorem dN_col1 (k a : ℕ) (ha : a < k + 1) :
    dN (k + 1 + 1 + 1) a (k + 1) = if a = k then -1 else 0 := by
  unfold dN
  split_ifs <;> omega

theorem dN_col2 (k a : ℕ) (ha : a < k + 1) :
    dN (k + 1 + 1 + 1) a (k + 2) = if a = k then -1 else 0 := by
  unfold dN
  split_ifs <;> omega

theorem dN_row1 (k b : ℕ) (hb : b < k + 1) :
    dN (k + 1 + 1 + 1) (k + 1) b = if b = k then -1 else 0 := by
  unfold dN
  split_ifs <;> omega

theorem dN_row2 (k b : ℕ) (hb : b < k + 1) :
    dN (k + 1 + 1 + 1) (k + 2) b = if b = k then -1 else 0 := by
  unfold dN
  split_ifs <;> omega

theorem dN_corner (k : ℕ) :
    dN (k + 1 + 1 + 1) (k + 1) (k + 1) = 2 ∧ dN (k + 1 + 1 + 1) (k + 1) (k + 2) = 0 ∧
      dN (k + 1 + 1 + 1) (k + 2) (k + 1) = 0 ∧ dN (k + 1 + 1 + 1) (k + 2) (k + 2) = 2 := by
  unfold dN
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- The truncated quadratic form of `D` on real sequences. -/
def quadD (z : ℕ → ℝ) (n : ℕ) : ℝ := ∑ a ∈ range n, ∑ b ∈ range n, z a * (dN n a b : ℝ) * z b

theorem quadD_eq (z : ℕ → ℝ) (k : ℕ) :
    quadD z (k + 1 + 1 + 1) = quadR z (k + 1) + 2 * z (k + 1) ^ 2 + 2 * z (k + 2) ^ 2
      - 2 * z k * (z (k + 1) + z (k + 2)) := by
  have hcol1 : ∑ a ∈ range (k + 1), z a * (dN (k + 1 + 1 + 1) a (k + 1) : ℝ) * z (k + 1) =
      - (z k * z (k + 1)) := by
    rw [Finset.sum_eq_single k]
    · rw [dN_col1 k k (by omega)]; simp
    · intro a ha hne
      rw [dN_col1 k a (by simpa using ha)]; simp [hne]
    · intro h; simp at h
  have hcol2 : ∑ a ∈ range (k + 1), z a * (dN (k + 1 + 1 + 1) a (k + 2) : ℝ) * z (k + 2) =
      - (z k * z (k + 2)) := by
    rw [Finset.sum_eq_single k]
    · rw [dN_col2 k k (by omega)]; simp
    · intro a ha hne
      rw [dN_col2 k a (by simpa using ha)]; simp [hne]
    · intro h; simp at h
  have hrow1 : ∑ b ∈ range (k + 1), z (k + 1) * (dN (k + 1 + 1 + 1) (k + 1) b : ℝ) * z b =
      - (z (k + 1) * z k) := by
    rw [Finset.sum_eq_single k]
    · rw [dN_row1 k k (by omega)]; simp
    · intro b hb hne
      rw [dN_row1 k b (by simpa using hb)]; simp [hne]
    · intro h; simp at h
  have hrow2 : ∑ b ∈ range (k + 1), z (k + 2) * (dN (k + 1 + 1 + 1) (k + 2) b : ℝ) * z b =
      - (z (k + 2) * z k) := by
    rw [Finset.sum_eq_single k]
    · rw [dN_row2 k k (by omega)]; simp
    · intro b hb hne
      rw [dN_row2 k b (by simpa using hb)]; simp [hne]
    · intro h; simp at h
  have hmain : ∑ a ∈ range (k + 1), ∑ b ∈ range (k + 1),
      z a * (dN (k + 1 + 1 + 1) a b : ℝ) * z b = quadR z (k + 1) := by
    unfold quadR
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [dN_eq_cartanA k a b (by simpa using ha) (by simpa using hb)]
  obtain ⟨c1, c2, c3, c4⟩ := dN_corner k
  unfold quadD
  simp only [Finset.sum_range_succ _ (k + 1 + 1), Finset.sum_range_succ _ (k + 1), Finset.sum_add_distrib,
    hcol1, hcol2, hrow1, hrow2, hmain, c1, c2, c3, c4]
  push_cast
  ring

/-- The quadratic form of the graph of `CartanMatrix.D (k + 3)`, in closed form. -/
theorem dot_D (k : ℕ) (x : Fin (k + 3) → ℝ) :
    x ⬝ᵥ (cartanReal (graphOfCartan (CartanMatrix.D (k + 3))) *ᵥ x) =
      extR x 0 ^ 2 + ∑ a ∈ range k, (extR x (a + 1) - extR x a) ^ 2 +
        (extR x (k + 1) + extR x (k + 2) - extR x k) ^ 2 + (extR x (k + 1) - extR x (k + 2)) ^ 2 := by
  unfold cartanReal
  rw [cartanMatrix_D_eq, dot_cartanReal_eq_range _ (dN (k + 3)) (fun i j => D_apply _ i j)]
  have := quadD_eq (extR x) k
  unfold quadD at this
  rw [quadR_closed] at this
  refine this.trans ?_
  ring

/-- The form of `D_n` (`n ≥ 3`) is positive definite. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem posDefinite_D (k : ℕ) : PosDefinite (graphOfCartan (CartanMatrix.D (k + 3))) := by
  refine posDefinite_of_pos _ _ (dot_D k) fun x hx => ?_
  set z := extR x with hz
  have hnn : 0 ≤ ∑ a ∈ range k, (z (a + 1) - z a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have h1 := sq_nonneg (z 0)
  have h2 := sq_nonneg (z (k + 1) + z (k + 2) - z k)
  have h3 := sq_nonneg (z (k + 1) - z (k + 2))
  rcases (add_nonneg (add_nonneg (add_nonneg h1 hnn) h2) h3).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have e0 : z 0 = 0 := by nlinarith
    have e1 : ∑ a ∈ range k, (z (a + 1) - z a) ^ 2 = 0 := by nlinarith
    have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (z (a + 1) - z a))).1 e1
    have e3 : z (k + 1) + z (k + 2) - z k = 0 := by nlinarith
    have e4 : z (k + 1) - z (k + 2) = 0 := by nlinarith
    have step : ∀ a, a ≤ k → z a = 0 := by
      intro a
      induction a with
      | zero => intro _; exact e0
      | succ a ih =>
        intro ha
        have := e2 a (Finset.mem_range.2 (by omega))
        have := pow_eq_zero_iff (two_ne_zero) |>.1 this
        have := ih (by omega)
        linarith
    have hk := step k le_rfl
    apply eq_zero_of_extR
    intro i
    by_cases hi : i ≤ k
    · exact step i hi
    · by_cases hi1 : i = k + 1
      · subst hi1; linarith
      · by_cases hi2 : i = k + 2
        · subst hi2; linarith
        · exact extR_of_le x (by omega)

/-! ### Types `E_6`, `E_7`, `E_8` -/

theorem cartanMatrix_E_eq (m : ℕ) :
    cartanMatrix (graphOfCartan (CartanMatrix.E m)) = CartanMatrix.E m := by
  refine cartanMatrix_graphOfCartan _ (fun i => by simp) (fun i j => ?_) (fun i j hij => ?_)
  · have := congrFun (congrFun (CartanMatrix.E_transpose m) i) j
    simpa [Matrix.transpose_apply] using this.symm
  · simp only [CartanMatrix.E, Matrix.of_apply, hij, ite_false]
    split_ifs <;> simp

theorem posDefinite_E6 : PosDefinite (graphOfCartan (CartanMatrix.E 6)) := by
  refine posDefinite_of_sos _ ![2, 2, 3/2, 5/6, 4/5, 3/4] (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 2, x 1 + (-1/2) * x 3, x 2 + (-2/3) * x 3, x 3 + (-6/5) * x 4,
      x 4 + (-5/4) * x 5, x 5]) ?_ ?_
  · intro x
    simp only [cartanReal, cartanMatrix_E_eq, CartanMatrix.E_six_eq]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

theorem posDefinite_E7 : PosDefinite (graphOfCartan (CartanMatrix.E 7)) := by
  refine posDefinite_of_sos _ ![2, 2, 3/2, 5/6, 4/5, 3/4, 2/3] (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 2, x 1 + (-1/2) * x 3, x 2 + (-2/3) * x 3, x 3 + (-6/5) * x 4,
      x 4 + (-5/4) * x 5, x 5 + (-4/3) * x 6, x 6]) ?_ ?_
  · intro x
    simp only [cartanReal, cartanMatrix_E_eq, CartanMatrix.E_seven_eq]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

theorem posDefinite_E8 : PosDefinite (graphOfCartan (CartanMatrix.E 8)) := by
  refine posDefinite_of_sos _ ![2, 2, 3/2, 5/6, 4/5, 3/4, 2/3, 1/2] (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 2, x 1 + (-1/2) * x 3, x 2 + (-2/3) * x 3, x 3 + (-6/5) * x 4,
      x 4 + (-5/4) * x 5, x 5 + (-4/3) * x 6, x 6 + (-3/2) * x 7, x 7]) ?_ ?_
  · intro x
    simp only [cartanReal, cartanMatrix_E_eq, CartanMatrix.E_eight_eq]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

/-! ### Connectedness and Dynkin diagrams -/

theorem adj_D (k : ℕ) (i j : Fin (k + 3)) : (graphOfCartan (CartanMatrix.D (k + 3))).Adj i j ↔
    i.val ≠ j.val ∧ dN (k + 3) i.val j.val = -1 ∧ dN (k + 3) j.val i.val = -1 := by
  simp [graphOfCartan, D_apply, Fin.ext_iff]

theorem connected_D (k : ℕ) : (graphOfCartan (CartanMatrix.D (k + 3))).Connected := by
  refine connected_of_parent _ ⟨0, by omega⟩ (fun i => i.val) fun i hi => ?_
  have hi0 : i.val ≠ 0 := fun e => hi (Fin.ext e)
  by_cases hik : i.val ≤ k
  · refine ⟨⟨i.val - 1, by omega⟩, (adj_D _ _ _).2 ⟨?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;>
      first | omega | (unfold dN; split_ifs <;> omega)
  · refine ⟨⟨k, by omega⟩, (adj_D _ _ _).2 ⟨?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;>
      first | omega | (unfold dN; split_ifs <;> omega)

theorem connected_E6 : (graphOfCartan (CartanMatrix.E 6)).Connected :=
  connected_of_parent _ 3 ![2, 1, 1, 0, 1, 2] (by decide)

theorem connected_E7 : (graphOfCartan (CartanMatrix.E 7)).Connected :=
  connected_of_parent _ 3 ![2, 1, 1, 0, 1, 2, 3] (by decide)

theorem connected_E8 : (graphOfCartan (CartanMatrix.E 8)).Connected :=
  connected_of_parent _ 3 ![2, 1, 1, 0, 1, 2, 3, 4] (by decide)

theorem connected_E9 : (graphOfCartan (CartanMatrix.E 9)).Connected :=
  connected_of_parent _ 3 ![2, 1, 1, 0, 1, 2, 3, 4, 5] (by decide)

/-- **Problem 5.3 (existence half).** The graph `A_n` (a path on `n + 1` vertices) is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem isDynkin_pathGraph (n : ℕ) : IsDynkin (SimpleGraph.pathGraph (n + 1)) :=
  ⟨SimpleGraph.connected_pathGraph_add_one n, posDefinite_pathGraph _⟩

/-- **Problem 5.3 (existence half).** The graph `D_n` (`n = k + 3 ≥ 3`) is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem isDynkin_D (k : ℕ) : IsDynkin (graphOfCartan (CartanMatrix.D (k + 3))) :=
  ⟨connected_D k, posDefinite_D k⟩

/-- **Problem 5.3 (existence half).** The graph `E_6` is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem isDynkin_E6 : IsDynkin (graphOfCartan (CartanMatrix.E 6)) := ⟨connected_E6, posDefinite_E6⟩

/-- **Problem 5.3 (existence half).** The graph `E_7` is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem isDynkin_E7 : IsDynkin (graphOfCartan (CartanMatrix.E 7)) := ⟨connected_E7, posDefinite_E7⟩

/-- **Problem 5.3 (existence half).** The graph `E_8` is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem isDynkin_E8 : IsDynkin (graphOfCartan (CartanMatrix.E 8)) := ⟨connected_E8, posDefinite_E8⟩

/-! ### Affine diagrams -/

/-- An affine (simply laced) Dynkin diagram: a connected loopless graph whose form `2 I - adjacency` is
positive semidefinite but not positive definite. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
def IsAffineDynkin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ (cartanReal G).PosSemidef ∧ ¬ PosDefinite G

/-- The form of `G` is positive semidefinite, and its kernel is the line spanned by the integer vector `v`
with all entries positive. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
def IsAffineKernel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ) : Prop :=
  (∀ i, 0 < v i) ∧ cartanMatrix G *ᵥ v = 0 ∧ (cartanReal G).PosSemidef ∧
    ∀ x : Fin n → ℝ, cartanReal G *ᵥ x = 0 → ∃ c : ℝ, x = c • fun i => (v i : ℝ)

theorem IsAffineKernel.not_posDefinite {n : ℕ} [NeZero n] {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {v : Fin n → ℤ} (h : IsAffineKernel G v) : ¬ PosDefinite G := by
  obtain ⟨hv, hMv, -, -⟩ := h
  intro hpd
  have hne : (fun i => (v i : ℝ)) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    have := hv 0
    simp_all
  have h0 : cartanReal G *ᵥ (fun i => (v i : ℝ)) = 0 := by
    funext i
    have := congrArg (fun y : Fin n → ℤ => (y i : ℝ)) hMv
    simpa [mulVec, dotProduct, cartanReal] using this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 hpd).2 hne
  rw [h0] at this
  simp at this

theorem isAffineKernel_of_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ)
    (hv : ∀ i, 0 < v i) (hMv : cartanMatrix G *ᵥ v = 0) (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ x, x ⬝ᵥ (cartanReal G *ᵥ x) = q x) (hnn : ∀ x, 0 ≤ q x)
    (hz : ∀ x, q x = 0 → ∃ c : ℝ, x = c • fun i => (v i : ℝ)) : IsAffineKernel G v := by
  refine ⟨hv, hMv, ?_, fun x hx => hz x ?_⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨cartanReal_isHermitian G, fun x => ?_⟩
    simp only [star_trivial]
    rw [hq]
    exact hnn x
  · rw [← hq, hx]
    simp

theorem isAffineKernel_of_sos {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ)
    (hv : ∀ i, 0 < v i) (hMv : cartanMatrix G *ᵥ v = 0) (w : Fin k → ℝ) (hw : ∀ j, 0 < w j)
    (l : (Fin n → ℝ) → Fin k → ℝ)
    (hq : ∀ x, x ⬝ᵥ (cartanReal G *ᵥ x) = ∑ j, w j * (l x j) ^ 2)
    (hker : ∀ x, (∀ j, l x j = 0) → ∃ c : ℝ, x = c • fun i => (v i : ℝ)) : IsAffineKernel G v := by
  refine isAffineKernel_of_nonneg G v hv hMv _ hq
    (fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hw j).le (sq_nonneg _)) fun x hx => hker x ?_
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ w j * (l x j) ^ 2 := fun j _ => mul_nonneg (hw j).le (sq_nonneg _)
  intro j
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hx j (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (hw j).ne'
  · exact pow_eq_zero_iff (two_ne_zero) |>.1 h1

theorem IsAffineKernel.isAffineDynkin {n : ℕ} [NeZero n] {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {v : Fin n → ℤ} (h : IsAffineKernel G v) (hc : G.Connected) : IsAffineDynkin G :=
  ⟨hc, h.2.2.1, h.not_posDefinite⟩

theorem E_nine_eq : CartanMatrix.E 9 = !![ 2,  0, -1,  0,  0,  0,  0,  0,  0;
                                          0,  2,  0, -1,  0,  0,  0,  0,  0;
                                         -1,  0,  2, -1,  0,  0,  0,  0,  0;
                                          0, -1, -1,  2, -1,  0,  0,  0,  0;
                                          0,  0,  0, -1,  2, -1,  0,  0,  0;
                                          0,  0,  0,  0, -1,  2, -1,  0,  0;
                                          0,  0,  0,  0,  0, -1,  2, -1,  0;
                                          0,  0,  0,  0,  0,  0, -1,  2, -1;
                                          0,  0,  0,  0,  0,  0,  0, -1,  2] := by decide

/-- **Problem 5.3(g).** The diagram `Ẽ_8` (Mathlib's `CartanMatrix.E 9`): positive semidefinite, with kernel
the line spanned by the positive vector of marks `(2, 3, 4, 6, 5, 4, 3, 2, 1)`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_E8 : IsAffineKernel (graphOfCartan (CartanMatrix.E 9)) ![2, 3, 4, 6, 5, 4, 3, 2, 1] := by
  refine isAffineKernel_of_sos _ _ (by decide) ?_ ![2, 2, 3/2, 5/6, 4/5, 3/4, 2/3, 1/2]
    (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 2, x 1 + (-1/2) * x 3, x 2 + (-2/3) * x 3, x 3 + (-6/5) * x 4,
      x 4 + (-5/4) * x 5, x 5 + (-4/3) * x 6, x 6 + (-3/2) * x 7, x 7 + (-2) * x 8]) ?_ ?_
  · rw [cartanMatrix_E_eq, E_nine_eq]; decide
  · intro x
    simp only [cartanReal, cartanMatrix_E_eq, E_nine_eq]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    refine ⟨x 8, ?_⟩
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

/-- The Cartan matrix of the affine diagram `D̃_4` (a star with four leaves; the centre is index `4`). -/
def affineD4Mat : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 0, 0, 0, -1;
    0, 2, 0, 0, -1;
    0, 0, 2, 0, -1;
    0, 0, 0, 2, -1;
    -1, -1, -1, -1, 2]

/-- The affine Dynkin diagram `D̃_4`. -/
def affineD4 : SimpleGraph (Fin 5) := graphOfCartan affineD4Mat

instance : DecidableRel affineD4.Adj := inferInstanceAs (DecidableRel (graphOfCartan affineD4Mat).Adj)

theorem cartanMatrix_affineD4 : cartanMatrix affineD4 = affineD4Mat :=
  cartanMatrix_graphOfCartan _ (by decide) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (fun i j h => by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | (left; rfl) | (right; rfl))

theorem connected_affineD4 : affineD4.Connected :=
  connected_of_parent _ 4 ![1, 1, 1, 1, 0] (by decide)

/-- **Problem 5.3(g).** The star `D̃_4`: positive semidefinite, kernel spanned by `(1, 1, 1, 1, 2)`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_D4 : IsAffineKernel affineD4 ![1, 1, 1, 1, 2] := by
  refine isAffineKernel_of_sos _ _ (by decide) ?_ ![2, 2, 2, 2] (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 4, x 1 + (-1/2) * x 4, x 2 + (-1/2) * x 4, x 3 + (-1/2) * x 4]) ?_ ?_
  · rw [cartanMatrix_affineD4]; decide
  · intro x
    simp only [cartanReal, cartanMatrix_affineD4, affineD4Mat]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    refine ⟨x 4 / 2, ?_⟩
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

/-- The Cartan matrix of `Ẽ_6` (three arms of length two; the centre is index `6`). -/
def affineE6Mat : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, 0, 0, -1;
    0, 0, 2, -1, 0, 0, 0;
    0, 0, -1, 2, 0, 0, -1;
    0, 0, 0, 0, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, -1, 0, -1, 0, -1, 2]

/-- The affine Dynkin diagram `Ẽ_6`. -/
def affineE6 : SimpleGraph (Fin 7) := graphOfCartan affineE6Mat

instance : DecidableRel affineE6.Adj := inferInstanceAs (DecidableRel (graphOfCartan affineE6Mat).Adj)

theorem cartanMatrix_affineE6 : cartanMatrix affineE6 = affineE6Mat :=
  cartanMatrix_graphOfCartan _ (by decide) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (fun i j h => by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | (left; rfl) | (right; rfl))

theorem connected_affineE6 : affineE6.Connected :=
  connected_of_parent _ 6 ![2, 1, 2, 1, 2, 1, 0] (by decide)

/-- **Problem 5.3(g).** The diagram `Ẽ_6`: positive semidefinite, kernel spanned by `(1, 2, 1, 2, 1, 2, 3)`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_E6 : IsAffineKernel affineE6 ![1, 2, 1, 2, 1, 2, 3] := by
  refine isAffineKernel_of_sos _ _ (by decide) ?_ ![2, 3/2, 2, 3/2, 2, 3/2]
    (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 1, x 1 + (-2/3) * x 6, x 2 + (-1/2) * x 3, x 3 + (-2/3) * x 6,
      x 4 + (-1/2) * x 5, x 5 + (-2/3) * x 6]) ?_ ?_
  · rw [cartanMatrix_affineE6]; decide
  · intro x
    simp only [cartanReal, cartanMatrix_affineE6, affineE6Mat]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    refine ⟨x 6 / 3, ?_⟩
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

/-- The Cartan matrix of `Ẽ_7` (arms of lengths three, three and one; the centre is index `7`). -/
def affineE7Mat : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, 0, 0, 0, 0, -1;
    0, 0, 0, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, 0, -1;
    0, 0, 0, 0, 0, 0, 2, -1;
    0, 0, -1, 0, 0, -1, -1, 2]

/-- The affine Dynkin diagram `Ẽ_7`. -/
def affineE7 : SimpleGraph (Fin 8) := graphOfCartan affineE7Mat

instance : DecidableRel affineE7.Adj := inferInstanceAs (DecidableRel (graphOfCartan affineE7Mat).Adj)

theorem cartanMatrix_affineE7 : cartanMatrix affineE7 = affineE7Mat :=
  cartanMatrix_graphOfCartan _ (by decide) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
    (fun i j h => by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | (left; rfl) | (right; rfl))

theorem connected_affineE7 : affineE7.Connected :=
  connected_of_parent _ 7 ![3, 2, 1, 3, 2, 1, 1, 0] (by decide)

/-- **Problem 5.3(g).** The diagram `Ẽ_7`: positive semidefinite, kernel spanned by
`(1, 2, 3, 1, 2, 3, 2, 4)`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_E7 : IsAffineKernel affineE7 ![1, 2, 3, 1, 2, 3, 2, 4] := by
  refine isAffineKernel_of_sos _ _ (by decide) ?_ ![2, 3/2, 4/3, 2, 3/2, 4/3, 2]
    (by intro j; fin_cases j <;> norm_num)
    (fun x => ![x 0 + (-1/2) * x 1, x 1 + (-2/3) * x 2, x 2 + (-3/4) * x 7, x 3 + (-1/2) * x 4,
      x 4 + (-2/3) * x 5, x 5 + (-3/4) * x 7, x 6 + (-1/2) * x 7]) ?_ ?_
  · rw [cartanMatrix_affineE7]; decide
  · intro x
    simp only [cartanReal, cartanMatrix_affineE7, affineE7Mat]
    simp [dotProduct, mulVec, Fin.sum_univ_succ]
    ring
  · intro x h
    refine ⟨x 7 / 4, ?_⟩
    simp [Fin.forall_fin_succ] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
    funext i
    fin_cases i <;> simp <;> linarith

/-! ### The affine cycle `Ã_n` -/

/-- Entries of the Cartan matrix of the cycle on `k + 3` vertices, as a function of natural-number indices. -/
def cycN (k a b : ℕ) : ℤ :=
  if a = b then 2
  else if a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ b = k + 2) ∨ (b = 0 ∧ a = k + 2) then -1 else 0

/-- The Cartan matrix of the cycle on `k + 3` vertices. -/
def cycMat (k : ℕ) : Matrix (Fin (k + 3)) (Fin (k + 3)) ℤ := Matrix.of fun i j => cycN k i j

/-- The cycle on `k + 3` vertices, the affine Dynkin diagram `Ã_{k+2}`. -/
def affineCycle (k : ℕ) : SimpleGraph (Fin (k + 3)) := graphOfCartan (cycMat k)

instance (k : ℕ) : DecidableRel (affineCycle k).Adj :=
  inferInstanceAs (DecidableRel (graphOfCartan (cycMat k)).Adj)

theorem cartanMatrix_cycMat (k : ℕ) : cartanMatrix (affineCycle k) = cycMat k := by
  refine cartanMatrix_graphOfCartan _ (fun i => by simp [cycMat, cycN]) (fun i j => ?_)
    (fun i j h => ?_)
  · simp only [cycMat, Matrix.of_apply, cycN]
    split_ifs <;> omega
  · have : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp only [cycMat, Matrix.of_apply, cycN, this, ite_false]
    split_ifs <;> simp

theorem connected_affineCycle (k : ℕ) : (affineCycle k).Connected := by
  refine connected_of_parent _ ⟨0, by omega⟩ (fun i => i.val) fun i hi => ?_
  have hi0 : i.val ≠ 0 := fun e => hi (Fin.ext e)
  refine ⟨⟨i.val - 1, by omega⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;> (try dsimp only) <;>
    first | omega | (intro e; have := congrArg Fin.val e; simp at this; omega) |
      (simp only [cycMat, Matrix.of_apply, cycN]; split_ifs <;> omega)

theorem cycN_split (k a b : ℕ) : (cycN k a b : ℝ) = (cartanA a b : ℝ) +
    ((if a = 0 ∧ b = k + 2 then -1 else 0) + (if a = k + 2 ∧ b = 0 then -1 else 0)) := by
  have : cycN k a b = cartanA a b + ((if a = 0 ∧ b = k + 2 then -1 else 0) +
      (if a = k + 2 ∧ b = 0 then -1 else 0)) := by
    unfold cycN cartanA
    split_ifs <;> omega
  rw [this]
  push_cast
  split_ifs <;> simp

theorem dot_cycle (k : ℕ) (x : Fin (k + 3) → ℝ) :
    x ⬝ᵥ (cartanReal (affineCycle k) *ᵥ x) =
      ∑ a ∈ range (k + 2), (extR x (a + 1) - extR x a) ^ 2 + (extR x (k + 2) - extR x 0) ^ 2 := by
  unfold cartanReal
  rw [cartanMatrix_cycMat, dot_cartanReal_eq_range (cycMat k) (cycN k) (fun i j => rfl)]
  set z := extR x with hz
  have hcorner : ∑ a ∈ range (k + 3), ∑ b ∈ range (k + 3), z a *
      ((if a = 0 ∧ b = k + 2 then (-1 : ℝ) else 0) + (if a = k + 2 ∧ b = 0 then -1 else 0)) * z b =
      - 2 * z 0 * z (k + 2) := by
    simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and]
    ring
  have hterm : ∀ a b, z a * (cycN k a b : ℝ) * z b = z a * (cartanA a b : ℝ) * z b +
      z a * ((if a = 0 ∧ b = k + 2 then (-1 : ℝ) else 0) + (if a = k + 2 ∧ b = 0 then -1 else 0)) * z b := by
    intro a b
    rw [cycN_split]
    ring
  simp only [hterm, Finset.sum_add_distrib, hcorner]
  have := quadR_closed z (k + 2)
  unfold quadR at this
  rw [show k + 3 = k + 2 + 1 from rfl, this]
  ring

theorem isAffineKernel_of_nonneg_of_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n → ℤ) (hv : ∀ i, 0 < v i) (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ x, x ⬝ᵥ (cartanReal G *ᵥ x) = q x) (hnn : ∀ x, 0 ≤ q x)
    (h0 : q (fun i => (v i : ℝ)) = 0)
    (hz : ∀ x, q x = 0 → ∃ c : ℝ, x = c • fun i => (v i : ℝ)) : IsAffineKernel G v := by
  have hpsd : (cartanReal G).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨cartanReal_isHermitian G, fun x => ?_⟩
    simp only [star_trivial]
    rw [hq]
    exact hnn x
  have hker : cartanReal G *ᵥ (fun i => (v i : ℝ)) = 0 := by
    rw [← hpsd.dotProduct_mulVec_zero_iff]
    simp only [star_trivial]
    rw [hq]
    exact h0
  have hMv : cartanMatrix G *ᵥ v = 0 := by
    funext i
    have := congrFun hker i
    have h2 : (((cartanMatrix G *ᵥ v) i : ℤ) : ℝ) = 0 := by
      simpa [mulVec, dotProduct, cartanReal] using this
    exact_mod_cast h2
  refine ⟨hv, hMv, hpsd, fun x hx => hz x ?_⟩
  rw [← hq, hx]
  simp

/-- **Problem 5.3(g).** The cycle `Ã_n` (here on `k + 3` vertices): positive semidefinite, kernel spanned by
the all-ones vector. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_cycle (k : ℕ) : IsAffineKernel (affineCycle k) (fun _ => 1) := by
  refine isAffineKernel_of_nonneg_of_zero _ _ (fun _ => one_pos) _ (dot_cycle k)
    (fun x => add_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg _) (sq_nonneg _)) ?_ ?_
  · rw [Finset.sum_eq_zero]
    · simp [extR]
    · intro a ha
      have := Finset.mem_range.1 ha
      simp [extR, show a < k + 3 by omega, show a + 1 < k + 3 by omega]
  · intro x hx
    have hnn : ∀ a ∈ range (k + 2), 0 ≤ (extR x (a + 1) - extR x a) ^ 2 := fun a _ => sq_nonneg _
    have hs : 0 ≤ ∑ a ∈ range (k + 2), (extR x (a + 1) - extR x a) ^ 2 := Finset.sum_nonneg hnn
    have h2 := sq_nonneg (extR x (k + 2) - extR x 0)
    have e1 : ∑ a ∈ range (k + 2), (extR x (a + 1) - extR x a) ^ 2 = 0 := by linarith
    have e2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 e1
    have step : ∀ a, a ≤ k + 2 → extR x a = extR x 0 := by
      intro a
      induction a with
      | zero => intro _; rfl
      | succ a ih =>
        intro ha
        have := e2 a (Finset.mem_range.2 (by omega))
        have := pow_eq_zero_iff (two_ne_zero) |>.1 this
        have := ih (by omega)
        linarith
    refine ⟨extR x 0, ?_⟩
    funext i
    have := step i.val (by omega)
    rw [extR_fin] at this
    simpa using this

/-! ### Subgraphs of positive definite graphs and the forbidden affine diagrams -/

theorem dot_cartanReal_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) :
    x ⬝ᵥ (cartanReal G *ᵥ x) = ∑ i, ∑ j, x i * (cartanMatrix G i j : ℝ) * x j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cartanMatrix_embed_le {m n : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (f : Fin m → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) (i j : Fin m) :
    cartanMatrix G (f i) (f j) ≤ cartanMatrix H i j := by
  rw [cartanMatrix_apply, cartanMatrix_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hfij : f i ≠ f j := fun e => hij (hf e)
    simp only [hij, hfij, ite_false]
    by_cases hH : H.Adj i j
    · simp [hH, hHG i j hH]
    · by_cases hG : G.Adj (f i) (f j) <;> simp [hH, hG]

/-- **Subgraphs of positive definite graphs.** If `G` has a positive definite form and `H` embeds into `G`
(an injective vertex map sending edges to edges), then the form of `H` is positive definite as well.  The proof
passes from a vector `x` to the nonnegative vector `|x|`, which can only lower the form, and extends by zero. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem PosDefinite.of_embedding {m n : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hG : PosDefinite G) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) : PosDefinite H := by
  refine posDefinite_of_pos H _ (dot_cartanReal_eq_sum H) fun x hx => ?_
  set y : Fin m → ℝ := fun i => |x i| with hy
  set Y : Fin n → ℝ := Function.extend f y (0 : Fin n → ℝ) with hYdef
  have hY : ∀ i, Y (f i) = y i := fun i => hf.extend_apply _ _ _
  have hY0 : ∀ a, a ∉ Set.range f → Y a = 0 := fun a ha =>
    by simpa [hYdef] using Function.extend_apply' y (0 : Fin n → ℝ) a (by simpa using ha)
  have hYne : Y ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    intro h0
    have := congrFun h0 (f i)
    rw [hY] at this
    simp [hy, hi] at this
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.1 hG).2 hYne
  simp only [star_trivial] at hpos
  rw [dot_cartanReal_eq_sum] at hpos
  have hsum : ∑ a, ∑ b, Y a * (cartanMatrix G a b : ℝ) * Y b =
      ∑ i, ∑ j, y i * (cartanMatrix G (f i) (f j) : ℝ) * y j := by
    symm
    refine Fintype.sum_of_injective f hf _ _ (fun a ha => ?_) (fun i => ?_)
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [hY0 a ha]; ring
    · refine Fintype.sum_of_injective f hf _ _ (fun b hb => ?_) (fun j => ?_)
      · rw [hY0 b hb]; ring
      · rw [hY, hY]
  rw [hsum] at hpos
  refine lt_of_lt_of_le hpos ?_
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hyy : 0 ≤ y i * y j := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hle : ((cartanMatrix G (f i) (f j) : ℤ) : ℝ) ≤ (cartanMatrix H i j : ℝ) := by
    exact_mod_cast cartanMatrix_embed_le f hf hHG i j
  have h1 : y i * (cartanMatrix G (f i) (f j) : ℝ) * y j ≤ y i * (cartanMatrix H i j : ℝ) * y j := by
    have := mul_le_mul_of_nonneg_left hle hyy
    nlinarith
  refine h1.trans ?_
  by_cases hij : i = j
  · subst hij
    have h0 : |x i| * |x i| = x i * x i := abs_mul_abs_self _
    have h2 : |x i| * (cartanMatrix H i i : ℝ) * |x i| = x i * (cartanMatrix H i i : ℝ) * x i := by
      calc |x i| * (cartanMatrix H i i : ℝ) * |x i| = (|x i| * |x i|) * (cartanMatrix H i i : ℝ) := by ring
        _ = (x i * x i) * (cartanMatrix H i i : ℝ) := by rw [h0]
        _ = _ := by ring
    exact h2.le
  · have hC : (cartanMatrix H i j : ℝ) ≤ 0 := by exact_mod_cast cartanMatrix_offDiag_nonpos H hij
    have hxy : x i * x j ≤ y i * y j := by
      simp only [hy]
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith

/-- A graph with positive definite form contains none of the affine diagrams (as a subgraph via an injective
map on vertices preserving edges): this is the forbidden-subgraph step of the classification in Problem 5.3. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem PosDefinite.not_embed_affine {m n : ℕ} [NeZero m] {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {v : Fin m → ℤ} (hH : IsAffineKernel H v) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : PosDefinite G) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) : False :=
  hH.not_posDefinite (hG.of_embedding f hf hHG)

/-- A positive definite graph contains no cycle (of any length `k + 3`) as a subgraph. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem PosDefinite.not_embed_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : PosDefinite G) (k : ℕ) (f : Fin (k + 3) → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, (affineCycle k).Adj i j → G.Adj (f i) (f j)) : False :=
  hG.not_embed_affine (affine_cycle k) f hf hHG

/-- A positive definite graph contains no star `D̃_4` (so in particular no vertex has four neighbours). -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem PosDefinite.not_embed_D4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : PosDefinite G) (f : Fin 5 → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, affineD4.Adj i j → G.Adj (f i) (f j)) : False :=
  hG.not_embed_affine affine_D4 f hf hHG

/-- The affine diagrams are connected, hence are affine Dynkin diagrams in the sense of `IsAffineDynkin`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_cycle (k : ℕ) : IsAffineDynkin (affineCycle k) :=
  (affine_cycle k).isAffineDynkin (connected_affineCycle k)

@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_D4 : IsAffineDynkin affineD4 := affine_D4.isAffineDynkin connected_affineD4

@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_E6 : IsAffineDynkin affineE6 := affine_E6.isAffineDynkin connected_affineE6

@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_E7 : IsAffineDynkin affineE7 := affine_E7.isAffineDynkin connected_affineE7

@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_E8 : IsAffineDynkin (graphOfCartan (CartanMatrix.E 9)) :=
  affine_E8.isAffineDynkin connected_E9

end UndergradKB.RepresentationTheory.Roots
