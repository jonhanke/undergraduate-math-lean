import UndergradKB.RepresentationTheory.DynkinForms
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import UndergradKB.Common.Attr

/-! # Classification of simply laced Dynkin diagrams, converse half (Etingof et al., Problem 5.3)

`DynkinForms.lean` shows that `A_n`, `D_n`, `E_6`, `E_7`, `E_8` are Dynkin diagrams (connected, positive
definite form) and that a positive definite graph contains no cycle and no affine diagram.  Here we prove the
converse, `classification_dynkin`: a connected graph `G` on `Fin n` with positive definite form is isomorphic
(`SimpleGraph.Iso`) to the path graph `A_n`, to `D_n` (`n ≥ 3`) or to `E_6`, `E_7`, `E_8`.

Route (the book's, with test vectors instead of determinants):

* `PosDefinite.isAcyclic`: a cycle of `G` would give a copy of the affine cycle, so `G` is a tree.
* `PosDefinite.no_dtilde`: two vertices of degree at least three (joined by a path, possibly of length zero,
  i.e. a copy of the affine diagram `D̃_n`, `n ≥ 4`) are impossible.  The proof evaluates the form on the vector
  `2` on the path and `1` on the four leaves, using only that the off-diagonal entries are nonpositive.
* `exists_armData`: a longest path `P` is either all of `G`, or has an interior vertex `b` with a further
  neighbour; a longest third arm hanging off `b` then covers everything else (the boundary argument uses
  maximality of `P` and of the third arm, `no_dtilde`).  Result: `ArmData`, three arms from a centre covering `G`.
* `ArmData.no_E6`, `no_E7`, `no_E8` (using `affine_E6`, `affine_E7`, `affine_E8` and `not_embed_affine`) force
  the sorted arm lengths to be `(0, p, q)` (a path), `(1, 1, r)`, `(1, 2, 2)`, `(1, 2, 3)` or `(1, 2, 4)`.
* `iso_of_bijective_hom`: a bijective homomorphism from a connected graph onto a tree is an isomorphism (edge
  count `N - 1` on both sides), which gives the isomorphisms `ArmData.iso_path`, `iso_D`, `iso_E` without
  excluding the extra edges by hand.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix Finset

/-- Isomorphism criterion: a bijective graph homomorphism from a connected graph to a tree is an isomorphism
(a connected graph on `N` vertices has at least `N - 1` edges, a tree exactly `N - 1`). -/
theorem iso_of_bijective_hom {A B : Type*} [Finite A] [Finite B] {M : SimpleGraph A} {G : SimpleGraph B}
    (hM : M.Connected) (hG : G.IsTree) (φ : A → B) (hφ : Function.Bijective φ)
    (hhom : ∀ i j, M.Adj i j → G.Adj (φ i) (φ j)) : Nonempty (M ≃g G) := by
  classical
  let f : M →g G := ⟨φ, fun {i j} h => hhom i j h⟩
  have hinj : Function.Injective f.mapEdgeSet := SimpleGraph.Hom.mapEdgeSet.injective f hφ.1
  have hcardV : Nat.card A = Nat.card B := Nat.card_congr (Equiv.ofBijective φ hφ)
  have h1 := hM.card_vert_le_card_edgeSet_add_one
  have h2 := (SimpleGraph.isTree_iff_connected_and_card.1 hG).2
  have hbij : Function.Bijective f.mapEdgeSet := hinj.bijective_of_nat_card_le (by omega)
  refine ⟨{ toEquiv := Equiv.ofBijective φ hφ, map_rel_iff' := ?_ }⟩
  intro i j
  simp only [Equiv.ofBijective_apply]
  refine ⟨fun h => ?_, hhom i j⟩
  obtain ⟨⟨e, he⟩, hee⟩ := hbij.2 ⟨s(φ i, φ j), h⟩
  induction e using Sym2.ind with
  | h a b =>
    have hee' : s(φ a, φ b) = s(φ i, φ j) := congrArg Subtype.val hee
    rcases Sym2.eq_iff.1 hee' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hφ.1 h1, ← hφ.1 h2]; exact he
    · rw [← hφ.1 h1, ← hφ.1 h2]; exact he.symm

/-- Sequences: an injective path `p 0, ..., p L` in `G`. -/
def IsPS {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℕ → Fin n) (L : ℕ) : Prop :=
  (∀ i j, i ≤ L → j ≤ L → p i = p j → i = j) ∧ ∀ i, i < L → G.Adj (p i) (p (i + 1))

theorem affineCycle_adj {k : ℕ} {s t : Fin (k + 3)} (h : (affineCycle k).Adj s t) :
    s.val + 1 = t.val ∨ t.val + 1 = s.val ∨ (s.val = 0 ∧ t.val = k + 2) ∨ (t.val = 0 ∧ s.val = k + 2) := by
  have h1 := h.2.1
  simp only [cycMat, Matrix.of_apply, cycN] at h1
  split_ifs at h1
  omega

/-- No cycle through an injective sequence closed up by an edge. -/
theorem PosDefinite.no_cycle_seq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hG : PosDefinite G)
    (q : ℕ → Fin n) (K : ℕ) (hK : 2 ≤ K) (hinj : ∀ i j, i ≤ K → j ≤ K → q i = q j → i = j)
    (hadj : ∀ i, i < K → G.Adj (q i) (q (i + 1))) (hclose : G.Adj (q K) (q 0)) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  refine hG.not_embed_cycle k (fun t => q t.val) (fun s t hst => Fin.ext (hinj _ _ (by omega) (by omega) hst))
    (fun s t h => ?_)
  rcases affineCycle_adj h with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hadj s.val (by omega)
    rwa [h1] at this
  · have := (hadj t.val (by omega)).symm
    rwa [h1] at this
  · show G.Adj (q s.val) (q t.val)
    rw [h1, h2]
    exact hclose.symm
  · show G.Adj (q s.val) (q t.val)
    rw [h1, h2]
    exact hclose

/-- A graph with positive definite form is acyclic. -/
theorem PosDefinite.isAcyclic {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hG : PosDefinite G) :
    G.IsAcyclic := by
  intro v c hc
  have h3 := hc.three_le_length
  refine hG.no_cycle_seq (fun i => c.getVert (i + 1)) (c.length - 1) (by omega) ?_ ?_ ?_
  · intro i j hi hj hij
    have := hc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; omega) hij
    omega
  · intro i hi
    exact c.adj_getVert_succ (by omega)
  · have e : c.length - 1 + 1 = c.length := by omega
    rw [e, SimpleGraph.Walk.getVert_length]
    simpa using (c.adj_getVert_succ (i := 0) (by omega))


/-! ### Path sequences -/

theorem IsPS.card_le {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) :
    L + 1 ≤ n := by
  have := Fintype.card_le_of_injective (fun i : Fin (L + 1) => p i.val)
    (fun i j hij => Fin.ext (h.1 _ _ (by omega) (by omega) hij))
  simpa using this

theorem IsPS.reverse {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) :
    IsPS G (fun i => p (L - i)) L := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · have := h.1 _ _ (by omega) (by omega) hij
    omega
  · have := (h.2 (L - (i + 1)) (by omega)).symm
    have e : L - (i + 1) + 1 = L - i := by omega
    rwa [e] at this

theorem IsPS.mono {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L L' : ℕ} (h : IsPS G p L)
    (hL : L' ≤ L) : IsPS G p L' :=
  ⟨fun i j hi hj => h.1 i j (by omega) (by omega), fun i hi => h.2 i (by omega)⟩

theorem IsPS.shift {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) (m d : ℕ)
    (hd : m + d ≤ L) : IsPS G (fun i => p (m + i)) d := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · have := h.1 _ _ (by omega) (by omega) hij
    omega
  · exact h.2 (m + i) (by omega)

theorem IsPS.shiftDown {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) (m d : ℕ)
    (hd : d ≤ m) (hm : m ≤ L) : IsPS G (fun i => p (m - i)) d := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · have := h.1 _ _ (by omega) (by omega) hij
    omega
  · have := (h.2 (m - (i + 1)) (by omega)).symm
    have e : m - (i + 1) + 1 = m - i := by omega
    rwa [e] at this

theorem IsPS.snoc {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) (y : Fin n)
    (hy : ∀ i, i ≤ L → p i ≠ y) (hadj : G.Adj (p L) y) :
    IsPS G (fun i => if i ≤ L then p i else y) (L + 1) := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · by_cases h1 : i ≤ L <;> by_cases h2 : j ≤ L
    · simp only [h1, h2, ite_true] at hij
      exact h.1 i j h1 h2 hij
    · simp only [h1, h2, ite_true, ite_false] at hij
      exact absurd hij (hy i h1)
    · simp only [h1, h2, ite_true, ite_false] at hij
      exact absurd hij.symm (hy j h2)
    · omega
  · by_cases h1 : i < L
    · have h2 : i + 1 ≤ L := h1
      simp only [h1.le, h2, ite_true]
      exact h.2 i h1
    · have : i = L := by omega
      subst this
      simpa using hadj

theorem IsPS.cons {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (h : IsPS G p L) (y : Fin n)
    (hy : ∀ i, i ≤ L → p i ≠ y) (hadj : G.Adj y (p 0)) :
    IsPS G (fun i => if i = 0 then y else p (i - 1)) (L + 1) := by
  refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
  · by_cases h1 : i = 0 <;> by_cases h2 : j = 0
    · omega
    · simp only [h1, h2, ite_true, ite_false] at hij
      exact absurd hij.symm (hy _ (by omega))
    · simp only [h1, h2, ite_true, ite_false] at hij
      exact absurd hij (hy _ (by omega))
    · simp only [h1, h2, ite_false] at hij
      have := h.1 _ _ (by omega) (by omega) hij
      omega
  · by_cases h1 : i = 0
    · subst h1
      simpa using hadj
    · simp only [h1, ite_false, Nat.add_one_ne_zero]
      have := h.2 (i - 1) (by omega)
      have e : i - 1 + 1 = i + 1 - 1 := by omega
      rwa [← e]

theorem exists_max_PS {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) :
    ∃ p L, IsPS G p L ∧ ∀ p' L', IsPS G p' L' → L' ≤ L := by
  set S : Set ℕ := {L | ∃ p, IsPS G p L} with hS
  have hne : S.Nonempty := ⟨0, fun _ => 0, fun i j hi hj _ => by omega, fun i hi => by omega⟩
  have hbdd : BddAbove S := ⟨n, fun L ⟨p, hp⟩ => by have := hp.card_le; omega⟩
  obtain ⟨p, hp⟩ := Nat.sSup_mem hne hbdd
  exact ⟨p, sSup S, hp, fun p' L' h' => le_csSup hbdd ⟨p', h'⟩⟩

/-- A chord of a path in a positive definite graph is impossible. -/
theorem PosDefinite.noChord {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hG : PosDefinite G)
    {p : ℕ → Fin n} {L : ℕ} (hp : IsPS G p L) {i j : ℕ} (hij : i < j) (hj : j ≤ L)
    (hadj : G.Adj (p i) (p j)) : j = i + 1 := by
  by_contra hne
  refine hG.no_cycle_seq (fun t => p (i + t)) (j - i) (by omega) ?_ ?_ ?_
  · intro a b ha hb hab
    have := hp.1 _ _ (by omega) (by omega) hab
    omega
  · intro t ht
    exact hp.2 (i + t) (by omega)
  · have e : i + (j - i) = j := by omega
    simp only [e, Nat.add_zero]
    exact hadj.symm

/-- Boundary edge from a proper nonempty subset in a connected graph. -/
theorem exists_boundary {n : ℕ} {G : SimpleGraph (Fin n)} (hconn : G.Connected) (S : Set (Fin n))
    (hS : S.Nonempty) (hne : ∃ v, v ∉ S) : ∃ x ∈ S, ∃ y, y ∉ S ∧ G.Adj x y := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨v, hv⟩ := hne
  obtain ⟨w⟩ := hconn.preconnected s v
  obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart S hs hv
  exact ⟨d.fst, hd1, d.snd, hd2, d.adj⟩


/-! ### Two branch points: the affine diagrams `D̃_n` -/

/-- The test vector `2 (e_{c 0} + ... + e_{c d})` along a sequence. -/
def Wv {n : ℕ} (c : ℕ → Fin n) : ℕ → Fin n → ℤ
  | 0 => (2 : ℤ) • (Pi.single (c 0) 1 : Fin n → ℤ)
  | d + 1 => Wv c d + (2 : ℤ) • (Pi.single (c (d + 1)) 1 : Fin n → ℤ)

section dtilde

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem form_single_le {u v : Fin n} (h : u ≠ v) :
    form G (Pi.single u 1 : Fin n → ℤ) (Pi.single v 1) ≤ 0 := by
  rw [form_single_single]; exact cartanMatrix_offDiag_nonpos G h

theorem form_single_adj {u v : Fin n} (h : G.Adj u v) :
    form G (Pi.single u 1 : Fin n → ℤ) (Pi.single v 1) = -1 := by
  rw [form_single_single, cartanMatrix_apply]; simp [G.ne_of_adj h, h]

theorem form_Wv_single_le (c : ℕ → Fin n) (v : Fin n) : ∀ d, (∀ i, i ≤ d → c i ≠ v) →
    form G (Wv c d) (Pi.single v 1) ≤ 0 ∧
      ∀ j, j ≤ d → form G (Wv c d) (Pi.single v 1) ≤ 2 * cartanMatrix G (c j) v
  | 0, hv => by
    have h0 : form G (Wv c 0) (Pi.single v 1) = 2 * cartanMatrix G (c 0) v := by
      simp only [Wv, form_smul_left, form_single_single]
    have h1 := cartanMatrix_offDiag_nonpos G (hv 0 le_rfl)
    refine ⟨by omega, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    exact h0.le
  | d + 1, hv => by
    obtain ⟨ih1, ih2⟩ := form_Wv_single_le c v d (fun i hi => hv i (by omega))
    have h0 : form G (Wv c (d + 1)) (Pi.single v 1) =
        form G (Wv c d) (Pi.single v 1) + 2 * cartanMatrix G (c (d + 1)) v := by
      simp only [Wv, form_add_left, form_smul_left, form_single_single]
    have h1 := cartanMatrix_offDiag_nonpos G (hv (d + 1) le_rfl)
    refine ⟨by omega, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (d + 1) with h | h
    · have := ih2 j (by omega)
      omega
    · obtain rfl : j = d + 1 := by omega
      omega

theorem Wv_apply_zero (c : ℕ → Fin n) (u : Fin n) : ∀ d, (∀ i, i ≤ d → c i ≠ u) → Wv c d u = 0
  | 0, hu => by
    simp [Wv, (hu 0 le_rfl).symm]
  | d + 1, hu => by
    have := Wv_apply_zero c u d (fun i hi => hu i (by omega))
    simp [Wv, this, (hu (d + 1) le_rfl).symm]

theorem form_Wv_le {c : ℕ → Fin n} : ∀ {d : ℕ}, IsPS G c d → form G (Wv c d) (Wv c d) ≤ 8
  | 0, _ => by
    simp only [Wv, form_smul_left, form_smul_right, form_single_single, cartanMatrix_diag]
    omega
  | d + 1, hc => by
    have ih := form_Wv_le (hc.mono (Nat.le_succ d))
    have hv : ∀ i, i ≤ d → c i ≠ c (d + 1) := fun i hi h =>
      absurd (hc.1 _ _ (by omega) le_rfl h) (by omega)
    have h1 := (form_Wv_single_le (G := G) c (c (d + 1)) d hv).2 d le_rfl
    have h2 : cartanMatrix G (c d) (c (d + 1)) = -1 := by
      rw [← form_single_single]; exact form_single_adj (hc.2 d (by omega))
    have h3 : form G (Wv c d) (Pi.single (c (d + 1)) 1) =
        form G (Pi.single (c (d + 1)) 1) (Wv c d) := form_comm G _ _
    have h4 : form G (Wv c (d + 1)) (Wv c (d + 1)) = form G (Wv c d) (Wv c d) +
        4 * form G (Wv c d) (Pi.single (c (d + 1)) 1) + 8 := by
      simp only [Wv, form_add_left, form_add_right, form_smul_left, form_smul_right, form_single_single,
        cartanMatrix_diag, ← h3]
      ring
    omega

/-- **Two branch points.**  In a graph with positive definite form there is no injective path `c 0, ..., c d`
(possibly of length zero) with two further neighbours of `c 0` and two further neighbours of `c d`, all four
distinct and off the path (a copy of the affine diagram `D̃_{d+4}`). -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem PosDefinite.no_dtilde (hG : PosDefinite G) {c : ℕ → Fin n} {d : ℕ} (hc : IsPS G c d)
    {u1 u2 v1 v2 : Fin n} (hu1 : G.Adj (c 0) u1) (hu2 : G.Adj (c 0) u2) (hv1 : G.Adj (c d) v1)
    (hv2 : G.Adj (c d) v2) (n1 : ∀ i, i ≤ d → c i ≠ u1) (n2 : ∀ i, i ≤ d → c i ≠ u2)
    (n3 : ∀ i, i ≤ d → c i ≠ v1) (n4 : ∀ i, i ≤ d → c i ≠ v2) (h12 : u1 ≠ u2) (h13 : u1 ≠ v1)
    (h14 : u1 ≠ v2) (h23 : u2 ≠ v1) (h24 : u2 ≠ v2) (h34 : v1 ≠ v2) : False := by
  set x : Fin n → ℤ := Wv c d + Pi.single u1 1 + Pi.single u2 1 + Pi.single v1 1 + Pi.single v2 1 with hx
  have hx0 : x ≠ 0 := by
    intro h0
    have := congrFun h0 u1
    simp [hx, Wv_apply_zero c u1 d (fun i hi => n1 i hi), h12, h13, h14] at this
  have hpos := hG.form_pos hx0
  have fW := form_Wv_le hc
  have a1 := (form_Wv_single_le (G := G) c u1 d n1).2 0 (Nat.zero_le _)
  have a2 := (form_Wv_single_le (G := G) c u2 d n2).2 0 (Nat.zero_le _)
  have a3 := (form_Wv_single_le (G := G) c v1 d n3).2 d le_rfl
  have a4 := (form_Wv_single_le (G := G) c v2 d n4).2 d le_rfl
  have e1 : cartanMatrix G (c 0) u1 = -1 := by rw [← form_single_single]; exact form_single_adj hu1
  have e2 : cartanMatrix G (c 0) u2 = -1 := by rw [← form_single_single]; exact form_single_adj hu2
  have e3 : cartanMatrix G (c d) v1 = -1 := by rw [← form_single_single]; exact form_single_adj hv1
  have e4 : cartanMatrix G (c d) v2 = -1 := by rw [← form_single_single]; exact form_single_adj hv2
  have c1 := form_comm G (Wv c d) (Pi.single u1 1)
  have c2 := form_comm G (Wv c d) (Pi.single u2 1)
  have c3 := form_comm G (Wv c d) (Pi.single v1 1)
  have c4 := form_comm G (Wv c d) (Pi.single v2 1)
  have s12 := form_single_le (G := G) h12
  have s13 := form_single_le (G := G) h13
  have s14 := form_single_le (G := G) h14
  have s23 := form_single_le (G := G) h23
  have s24 := form_single_le (G := G) h24
  have s34 := form_single_le (G := G) h34
  have t12 := form_comm G (Pi.single u1 1) (Pi.single u2 1)
  have t13 := form_comm G (Pi.single u1 1) (Pi.single v1 1)
  have t14 := form_comm G (Pi.single u1 1) (Pi.single v2 1)
  have t23 := form_comm G (Pi.single u2 1) (Pi.single v1 1)
  have t24 := form_comm G (Pi.single u2 1) (Pi.single v2 1)
  have t34 := form_comm G (Pi.single v1 1) (Pi.single v2 1)
  have d1 := form_single_single G u1 u1
  have d2 := form_single_single G u2 u2
  have d3 := form_single_single G v1 v1
  have d4 := form_single_single G v2 v2
  simp only [cartanMatrix_diag] at d1 d2 d3 d4
  simp only [hx, form_add_left, form_add_right] at hpos
  linarith

end dtilde


/-! ### Arm data -/

/-- Three injective arms emanating from a common centre `ctr`: arm `i` is `ctr = av i 0, av i 1, ..., av i (l i)`,
a path in `G`; different arms meet only in `ctr`. -/
structure ArmData {n : ℕ} (G : SimpleGraph (Fin n)) (l : Fin 3 → ℕ) where
  ctr : Fin n
  av : Fin 3 → ℕ → Fin n
  zero : ∀ i, av i 0 = ctr
  adj : ∀ i s, s < l i → G.Adj (av i s) (av i (s + 1))
  inj : ∀ i s j t, s ≤ l i → t ≤ l j → av i s = av j t → (s = 0 ∧ t = 0) ∨ (i = j ∧ s = t)

namespace ArmData

variable {n : ℕ} {G : SimpleGraph (Fin n)} {l : Fin 3 → ℕ} (A : ArmData G l)

theorem adjc (i : Fin 3) (h : 1 ≤ l i) : G.Adj A.ctr (A.av i 1) := by
  have := A.adj i 0 h
  rwa [A.zero] at this

theorem adjs (i : Fin 3) (s : ℕ) (h : s + 2 ≤ l i) : G.Adj (A.av i (s + 1)) (A.av i (s + 2)) :=
  A.adj i (s + 1) h

theorem av_ne {i j : Fin 3} {s t : ℕ} (hs : s ≤ l i) (ht : t ≤ l j) (h1 : 1 ≤ s ∨ 1 ≤ t)
    (h2 : i ≠ j ∨ s ≠ t) : A.av i s ≠ A.av j t := by
  intro h
  rcases A.inj i s j t hs ht h with ⟨a, b⟩ | ⟨a, b⟩
  · omega
  · rcases h2 with h2 | h2
    · exact h2 a
    · exact h2 b

theorem av_ne_ctr {i : Fin 3} {s : ℕ} (hs : 1 ≤ s) (hs' : s ≤ l i) : A.av i s ≠ A.ctr := by
  intro h
  rw [← A.zero i] at h
  have := A.av_ne (i := i) (j := i) (s := s) (t := 0) hs' (Nat.zero_le _) (Or.inl hs) (Or.inr (by omega))
  exact this h


include A in
theorem no_E6 [DecidableRel G.Adj] (hG : PosDefinite G) (h0 : 2 ≤ l 0) (h1 : 2 ≤ l 1) (h2 : 2 ≤ l 2) : False := by
  refine hG.not_embed_affine affine_E6
    ![A.av 0 2, A.av 0 1, A.av 1 2, A.av 1 1, A.av 2 2, A.av 2 1, A.ctr] ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;>
      first
        | exact absurd hxy (A.av_ne (by omega) (by omega) (by omega) (by simp))
        | exact absurd hxy (A.av_ne_ctr (by omega) (by omega))
        | exact absurd hxy.symm (A.av_ne_ctr (by omega) (by omega))
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp [affineE6, graphOfCartan, affineE6Mat] at h ⊢ <;>
      first
        | exact A.adjc _ (by omega)
        | exact (A.adjc _ (by omega)).symm
        | exact A.adjs _ _ (by omega)
        | exact (A.adjs _ _ (by omega)).symm


include A in
theorem no_E7 [DecidableRel G.Adj] (hG : PosDefinite G) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hi : 1 ≤ l i) (hj : 3 ≤ l j) (hk : 3 ≤ l k) : False := by
  have hji := hij.symm
  have hkj := hjk.symm
  have hki := hik.symm
  refine hG.not_embed_affine affine_E7
    ![A.av j 3, A.av j 2, A.av j 1, A.av k 3, A.av k 2, A.av k 1, A.av i 1, A.ctr] ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;>
      first
        | exact absurd hxy (A.av_ne (by omega) (by omega) (by omega) (by simp [*]))
        | exact absurd hxy (A.av_ne_ctr (by omega) (by omega))
        | exact absurd hxy.symm (A.av_ne_ctr (by omega) (by omega))
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp [affineE7, graphOfCartan, affineE7Mat] at h ⊢ <;>
      first
        | exact A.adjc _ (by omega)
        | exact (A.adjc _ (by omega)).symm
        | exact A.adjs _ _ (by omega)
        | exact (A.adjs _ _ (by omega)).symm

include A in
theorem no_E8 [DecidableRel G.Adj] (hG : PosDefinite G) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hi : 1 ≤ l i) (hj : 2 ≤ l j) (hk : 5 ≤ l k) : False := by
  have hji := hij.symm
  have hkj := hjk.symm
  have hki := hik.symm
  refine hG.not_embed_affine affine_E8
    ![A.av j 2, A.av i 1, A.av j 1, A.ctr, A.av k 1, A.av k 2, A.av k 3, A.av k 4, A.av k 5] ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;>
      first
        | exact absurd hxy (A.av_ne (by omega) (by omega) (by omega) (by simp [*]))
        | exact absurd hxy (A.av_ne_ctr (by omega) (by omega))
        | exact absurd hxy.symm (A.av_ne_ctr (by omega) (by omega))
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp [graphOfCartan, E_nine_eq] at h ⊢ <;>
      first
        | exact A.adjc _ (by omega)
        | exact (A.adjc _ (by omega)).symm
        | exact A.adjs _ _ (by omega)
        | exact (A.adjs _ _ (by omega)).symm


end ArmData

/-- A single path, as arm data with arm lengths `(L, 0, 0)`. -/
def ArmData.ofPath {n : ℕ} {G : SimpleGraph (Fin n)} {p : ℕ → Fin n} {L : ℕ} (hp : IsPS G p L) :
    ArmData G ![L, 0, 0] where
  ctr := p 0
  av := fun i s => if i = 0 then p s else p 0
  zero := fun i => by by_cases h : i = 0 <;> simp [h]
  adj := fun i s hs => by
    fin_cases i
    · simpa using hp.2 s (by simpa using hs)
    · simp at hs
    · simp at hs
  inj := fun i s j t hs ht h => by
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · have hs' : s ≤ L := hs
      have ht' : t ≤ L := ht
      have h' : p s = p t := h
      exact Or.inr ⟨rfl, hp.1 s t hs' ht' h'⟩
    · have hs' : s ≤ L := hs
      have ht' : t ≤ 0 := ht
      have h' : p s = p 0 := h
      have := hp.1 s 0 hs' (Nat.zero_le _) h'
      omega
    · have hs' : s ≤ L := hs
      have ht' : t ≤ 0 := ht
      have h' : p s = p 0 := h
      have := hp.1 s 0 hs' (Nat.zero_le _) h'
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ L := ht
      have h' : p 0 = p t := h
      have := hp.1 0 t (Nat.zero_le _) ht' h'
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ 0 := ht
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ 0 := ht
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ L := ht
      have h' : p 0 = p t := h
      have := hp.1 0 t (Nat.zero_le _) ht' h'
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ 0 := ht
      omega
    · have hs' : s ≤ 0 := hs
      have ht' : t ≤ 0 := ht
      omega

/-- Arm data from a path `p 0, ..., p L` and a third arm `q` hanging off `p m`. -/
def ArmData.ofBranch {n : ℕ} {G : SimpleGraph (Fin n)} {p q : ℕ → Fin n} {L m a : ℕ} (hp : IsPS G p L)
    (hm : m ≤ L) (hq : IsPS G q a) (hq0 : q 0 = p m)
    (hqP : ∀ s, 1 ≤ s → s ≤ a → ∀ i, i ≤ L → q s ≠ p i) : ArmData G ![m, L - m, a] where
  ctr := p m
  av := fun i s => if i = 0 then p (m - s) else if i = 1 then p (m + s) else q s
  zero := fun i => by fin_cases i <;> simp [hq0]
  adj := fun i s hs => by
    fin_cases i
    · simp at hs ⊢
      have := (hp.2 (m - (s + 1)) (by omega)).symm
      have e : m - (s + 1) + 1 = m - s := by omega
      rwa [e] at this
    · simp at hs ⊢
      exact hp.2 (m + s) (by omega)
    · simp at hs ⊢
      exact hq.2 s hs
  inj := fun i s j t hs ht h => by
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · have hs' : s ≤ m := hs
      have ht' : t ≤ m := ht
      have h' : p (m - s) = p (m - t) := h
      have := hp.1 _ _ (by omega) (by omega) h'
      exact Or.inr ⟨rfl, by omega⟩
    · have hs' : s ≤ m := hs
      have ht' : t ≤ L - m := ht
      have h' : p (m - s) = p (m + t) := h
      have := hp.1 _ _ (by omega) (by omega) h'
      omega
    · have hs' : s ≤ m := hs
      have ht' : t ≤ a := ht
      have h' : p (m - s) = q t := h
      by_cases ht0 : t = 0
      · subst ht0
        rw [hq0] at h'
        have := hp.1 _ _ (by omega) (by omega) h'
        omega
      · exact absurd h'.symm (hqP t (by omega) ht' _ (by omega))
    · have hs' : s ≤ L - m := hs
      have ht' : t ≤ m := ht
      have h' : p (m + s) = p (m - t) := h
      have := hp.1 _ _ (by omega) (by omega) h'
      omega
    · have hs' : s ≤ L - m := hs
      have ht' : t ≤ L - m := ht
      have h' : p (m + s) = p (m + t) := h
      have := hp.1 _ _ (by omega) (by omega) h'
      exact Or.inr ⟨rfl, by omega⟩
    · have hs' : s ≤ L - m := hs
      have ht' : t ≤ a := ht
      have h' : p (m + s) = q t := h
      by_cases ht0 : t = 0
      · subst ht0
        rw [hq0] at h'
        have := hp.1 _ _ (by omega) (by omega) h'
        omega
      · exact absurd h'.symm (hqP t (by omega) ht' _ (by omega))
    · have hs' : s ≤ a := hs
      have ht' : t ≤ m := ht
      have h' : q s = p (m - t) := h
      by_cases hs0 : s = 0
      · subst hs0
        rw [hq0] at h'
        have := hp.1 _ _ (by omega) (by omega) h'
        omega
      · exact absurd h' (hqP s (by omega) hs' _ (by omega))
    · have hs' : s ≤ a := hs
      have ht' : t ≤ L - m := ht
      have h' : q s = p (m + t) := h
      by_cases hs0 : s = 0
      · subst hs0
        rw [hq0] at h'
        have := hp.1 _ _ (by omega) (by omega) h'
        omega
      · exact absurd h' (hqP s (by omega) hs' _ (by omega))
    · have hs' : s ≤ a := hs
      have ht' : t ≤ a := ht
      have h' : q s = q t := h
      exact Or.inr ⟨rfl, hq.1 s t hs' ht' h'⟩

/-! ### Existence of arm data covering a connected positive definite graph -/

/-- A connected graph with positive definite form is covered by three arms from a common centre (the third arm
possibly of length zero, in which case the graph is a path). -/
theorem exists_armData {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hconn : G.Connected)
    (hG : PosDefinite G) :
    ∃ (l : Fin 3 → ℕ) (A : ArmData G l), ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v := by
  have : NeZero n := ⟨by
    obtain ⟨v⟩ := hconn.nonempty
    exact (Fin.pos v).ne'⟩
  obtain ⟨p, L, hp, hmax⟩ := exists_max_PS G
  by_cases hcov : ∀ v, ∃ i, i ≤ L ∧ p i = v
  · refine ⟨_, ArmData.ofPath hp, fun v => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcov v
    exact ⟨0, i, hi, rfl⟩
  · push Not at hcov
    obtain ⟨v0, hv0⟩ := hcov
    obtain ⟨x, hx, w, hw, hxw⟩ := exists_boundary hconn {v | ∃ i, i ≤ L ∧ p i = v}
      ⟨p 0, 0, Nat.zero_le _, rfl⟩ ⟨v0, fun ⟨i, hi, h⟩ => hv0 i hi h⟩
    obtain ⟨m, hmL, rfl⟩ := hx
    have hw' : ∀ i, i ≤ L → p i ≠ w := fun i hi h => hw ⟨i, hi, h⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := hmax _ _ (hp.cons w hw' hxw.symm)
      omega
    have hmL' : m ≠ L := by
      rintro rfl
      have := hmax _ _ (hp.snoc w hw' hxw)
      omega
    have hmlt : m < L := lt_of_le_of_ne hmL hmL'
    set Sa : Set ℕ := {a | ∃ q, IsPS G q a ∧ q 0 = p m ∧ ∀ s, 1 ≤ s → s ≤ a → ∀ i, i ≤ L → q s ≠ p i}
      with hSa
    have h1 : 1 ∈ Sa := by
      refine ⟨fun s => if s = 0 then p m else w, ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩, by simp,
        fun s hs1 hs2 i hi => ?_⟩
      · by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · simp only [hi0, hj0, ite_true, ite_false] at hij
          exact absurd hij (hw' m hmL)
        · simp only [hi0, hj0, ite_true, ite_false] at hij
          exact absurd hij.symm (hw' m hmL)
        · omega
      · have : i = 0 := by omega
        subst this
        simpa using hxw
      · have : s = 1 := by omega
        subst this
        simpa using (hw' i hi).symm
    have hbdd : BddAbove Sa := ⟨n, fun a ⟨q, hq, _⟩ => by have := hq.card_le; omega⟩
    obtain ⟨q, hq, hq0, hqP⟩ := Nat.sSup_mem ⟨1, h1⟩ hbdd
    set a := sSup Sa with ha
    have hamax : ∀ a', a' ∈ Sa → a' ≤ a := fun a' h => le_csSup hbdd h
    have ha1 : 1 ≤ a := hamax 1 h1
    have hpne : ∀ i j, i ≤ L → j ≤ L → i ≠ j → p i ≠ p j :=
      fun i j hi hj hne h => hne (hp.1 i j hi hj h)
    have hpq : ∀ i s, i ≤ L → 1 ≤ s → s ≤ a → p i ≠ q s :=
      fun i s hi h1 h2 h => hqP s h1 h2 i hi h.symm
    have hqne : ∀ s t, s ≤ a → t ≤ a → s ≠ t → q s ≠ q t :=
      fun s t hs ht hne h => hne (hq.1 s t hs ht h)
    have hcover : ∀ v, (∃ i, i ≤ L ∧ p i = v) ∨ (∃ s, 1 ≤ s ∧ s ≤ a ∧ q s = v) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨v0, hv0p, hv0q⟩ := hcon
      obtain ⟨x, hx, z, hz, hxz⟩ := exists_boundary hconn
        {v | (∃ i, i ≤ L ∧ p i = v) ∨ (∃ s, 1 ≤ s ∧ s ≤ a ∧ q s = v)}
        ⟨p 0, Or.inl ⟨0, Nat.zero_le _, rfl⟩⟩
        ⟨v0, fun h => h.elim (fun ⟨i, hi, h⟩ => hv0p i hi h) (fun ⟨s, h1, h2, h⟩ => hv0q s h1 h2 h)⟩
      have hzp : ∀ i, i ≤ L → p i ≠ z := fun i hi h => hz (Or.inl ⟨i, hi, h⟩)
      have hzq : ∀ s, 1 ≤ s → s ≤ a → q s ≠ z := fun s h1 h2 h => hz (Or.inr ⟨s, h1, h2, h⟩)
      have hq1 : G.Adj (p m) (q 1) := by
        have := hq.2 0 (by omega)
        rw [hq0] at this
        simpa using this
      rcases hx with ⟨j, hj, rfl⟩ | ⟨s, hs1, hsa, rfl⟩
      · by_cases hj0 : j = 0
        · subst hj0
          have := hmax _ _ (hp.cons z hzp hxz.symm)
          omega
        by_cases hjL : j = L
        · subst hjL
          have := hmax _ _ (hp.snoc z hzp hxz)
          omega
        rcases Nat.lt_trichotomy j m with hjm | hjm | hjm
        · have hc : IsPS G (fun i => p (m - i)) (m - j) := hp.shiftDown m (m - j) (by omega) hmL
          have e : m - (m - j) = j := by omega
          refine hG.no_dtilde hc (u1 := p (m + 1)) (u2 := q 1) (v1 := p (j - 1)) (v2 := z) ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show G.Adj (p (m - 0)) (p (m + 1))
            simpa using hp.2 m (by omega)
          · show G.Adj (p (m - 0)) (q 1)
            simpa using hq1
          · show G.Adj (p (m - (m - j))) (p (j - 1))
            rw [e]
            have := (hp.2 (j - 1) (by omega)).symm
            rwa [show j - 1 + 1 = j by omega] at this
          · show G.Adj (p (m - (m - j))) z
            rw [e]; exact hxz
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hpq _ 1 (by omega) le_rfl ha1
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hzp _ (by omega)
          · exact hpq _ 1 (by omega) le_rfl ha1
          · exact hpne _ _ (by omega) (by omega) (by omega)
          · exact hzp _ (by omega)
          · exact (hpq _ 1 (by omega) le_rfl ha1).symm
          · exact hzq 1 le_rfl ha1
          · exact hzp _ (by omega)
        · obtain rfl := hjm
          have hc : IsPS G (fun _ => p j) 0 := ⟨fun i j' hi hj' _ => by omega, fun i hi => by omega⟩
          refine hG.no_dtilde hc (u1 := p (j - 1)) (u2 := p (j + 1)) (v1 := q 1) (v2 := z) ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show G.Adj (p j) (p (j - 1))
            have := (hp.2 (j - 1) (by omega)).symm
            rwa [show j - 1 + 1 = j by omega] at this
          · exact hp.2 j (by omega)
          · exact hq1
          · exact hxz
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hpq _ 1 (by omega) le_rfl ha1
          · exact fun i hi => hzp _ (by omega)
          · exact hpne _ _ (by omega) (by omega) (by omega)
          · exact hpq _ 1 (by omega) le_rfl ha1
          · exact hzp _ (by omega)
          · exact hpq _ 1 (by omega) le_rfl ha1
          · exact hzp _ (by omega)
          · exact hzq 1 le_rfl ha1
        · have hc : IsPS G (fun i => p (m + i)) (j - m) := hp.shift m (j - m) (by omega)
          have e : m + (j - m) = j := by omega
          refine hG.no_dtilde hc (u1 := p (m - 1)) (u2 := q 1) (v1 := p (j + 1)) (v2 := z) ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · show G.Adj (p (m + 0)) (p (m - 1))
            have := (hp.2 (m - 1) (by omega)).symm
            rw [show m - 1 + 1 = m by omega] at this
            simpa using this
          · show G.Adj (p (m + 0)) (q 1)
            simpa using hq1
          · show G.Adj (p (m + (j - m))) (p (j + 1))
            rw [e]; exact hp.2 j (by omega)
          · show G.Adj (p (m + (j - m))) z
            rw [e]; exact hxz
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hpq _ 1 (by omega) le_rfl ha1
          · exact fun i hi => hpne _ _ (by omega) (by omega) (by omega)
          · exact fun i hi => hzp _ (by omega)
          · exact hpq _ 1 (by omega) le_rfl ha1
          · exact hpne _ _ (by omega) (by omega) (by omega)
          · exact hzp _ (by omega)
          · exact (hpq (j + 1) 1 (by omega) le_rfl ha1).symm
          · exact hzq 1 le_rfl ha1
          · exact hzp _ (by omega)
      · by_cases hsa' : s = a
        · rw [hsa'] at hxz
          have hqz : ∀ i, i ≤ a → q i ≠ z := by
            intro i hi
            by_cases hi0 : i = 0
            · subst hi0; rw [hq0]; exact hzp m hmL
            · exact hzq i (by omega) hi
          have hq' := hq.snoc z hqz hxz
          have := hamax (a + 1) ⟨_, hq', by simp [hq0], fun s' hs1' hs2' i hi => ?_⟩
          · omega
          · by_cases hs3 : s' ≤ a
            · simp only [hs3, ite_true]
              exact hqP s' hs1' hs3 i hi
            · simp only [hs3, ite_false]
              exact (hzp i hi).symm
        · have hsa2 : s < a := by omega
          have hc : IsPS G q s := hq.mono (by omega)
          refine hG.no_dtilde hc (u1 := p (m - 1)) (u2 := p (m + 1)) (v1 := q (s + 1)) (v2 := z) ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · rw [hq0]
            have := (hp.2 (m - 1) (by omega)).symm
            rwa [show m - 1 + 1 = m by omega] at this
          · rw [hq0]; exact hp.2 m (by omega)
          · exact hq.2 s hsa2
          · exact hxz
          · intro i hi
            by_cases hi0 : i = 0
            · subst hi0; rw [hq0]; exact hpne m (m - 1) hmL (by omega) (by omega)
            · exact (hpq (m - 1) i (by omega) (by omega) (by omega)).symm
          · intro i hi
            by_cases hi0 : i = 0
            · subst hi0; rw [hq0]; exact hpne m (m + 1) hmL (by omega) (by omega)
            · exact (hpq (m + 1) i (by omega) (by omega) (by omega)).symm
          · intro i hi
            by_cases hi0 : i = 0
            · subst hi0; rw [hq0]; exact hpq _ (s + 1) hmL (by omega) (by omega)
            · exact hqne _ _ (by omega) (by omega) (by omega)
          · intro i hi
            by_cases hi0 : i = 0
            · subst hi0; rw [hq0]; exact hzp m hmL
            · exact hzq i (by omega) (by omega)
          · exact hpne _ _ (by omega) (by omega) (by omega)
          · exact hpq _ (s + 1) (by omega) (by omega) (by omega)
          · exact hzp _ (by omega)
          · exact hpq _ (s + 1) (by omega) (by omega) (by omega)
          · exact hzp _ (by omega)
          · exact hzq (s + 1) (by omega) (by omega)
    refine ⟨_, ArmData.ofBranch hp hmL hq hq0 hqP, fun v => ?_⟩
    rcases hcover v with ⟨i, hi, rfl⟩ | ⟨s, hs1, hsa, rfl⟩
    · by_cases him : i ≤ m
      · exact ⟨0, m - i, (by show m - i ≤ m; omega), (by show p (m - (m - i)) = p i; congr 1; omega)⟩
      · exact ⟨1, i - m, (by show i - m ≤ L - m; omega), (by show p (m + (i - m)) = p i; congr 1; omega)⟩
    · exact ⟨2, s, hsa, rfl⟩

/-! ### From arm data to the Dynkin diagrams -/

theorem fin3_cases : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x, x = i ∨ x = j ∨ x = k := by decide

namespace ArmData

variable {n : ℕ} {G : SimpleGraph (Fin n)} {l : Fin 3 → ℕ} (A : ArmData G l)

/-- A labelling of `N` positions by (arm, depth) pairs that is injective modulo the centre and hits every
non-central position of the arms gives a bijection with the vertices. -/
theorem bijective_of_pos (hcov : ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v) {N : ℕ} (pi : Fin N → Fin 3)
    (ps : Fin N → ℕ) (hz : ∀ x y, ps x = 0 → ps y = 0 → x = y)
    (hp : ∀ x y, pi x = pi y → ps x = ps y → x = y) (hb : ∀ x, ps x ≤ l (pi x))
    (hs : ∀ i s, s ≤ l i → 0 < s → ∃ x, pi x = i ∧ ps x = s) (h0 : ∃ x, ps x = 0) :
    Function.Bijective (fun x => A.av (pi x) (ps x)) := by
  constructor
  · intro x y hxy
    rcases A.inj _ _ _ _ (hb x) (hb y) hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hz x y h1 h2
    · exact hp x y h1 h2
  · intro v
    obtain ⟨i', s, hs', rfl⟩ := hcov v
    by_cases h : s = 0
    · subst h
      obtain ⟨x, hx⟩ := h0
      exact ⟨x, by simp only [hx, A.zero]⟩
    · obtain ⟨x, hx1, hx2⟩ := hs i' s hs' (Nat.pos_of_ne_zero h)
      exact ⟨x, by simp only [hx1, hx2]⟩

theorem iso_path (hcov : ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v) (hT : G.IsTree) {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (hi : l i = 0) :
    Nonempty (SimpleGraph.pathGraph (l j + l k + 1) ≃g G) := by
  have hkj := hjk.symm
  have hki := hik.symm
  let pi : Fin (l j + l k + 1) → Fin 3 := fun x => if x.val ≤ l j then j else k
  let ps : Fin (l j + l k + 1) → ℕ := fun x => if x.val ≤ l j then l j - x.val else x.val - l j
  have hstep : ∀ x y : Fin (l j + l k + 1), x.val + 1 = y.val →
      G.Adj (A.av (pi x) (ps x)) (A.av (pi y) (ps y)) := by
    intro x y hxy
    have hyl := y.isLt
    by_cases hy : y.val ≤ l j
    · have hx : x.val ≤ l j := by omega
      simp only [pi, ps, hx, hy, ↓reduceIte]
      have := (A.adj j (l j - y.val) (by omega)).symm
      rwa [show l j - y.val + 1 = l j - x.val by omega] at this
    · by_cases hx : x.val ≤ l j
      · simp only [pi, ps, hx, hy, ↓reduceIte]
        have hxj : x.val = l j := by omega
        rw [hxj, Nat.sub_self, A.zero]
        have := A.adjc k (by omega)
        rwa [show y.val - l j = 1 by omega]
      · simp only [pi, ps, hx, hy, ↓reduceIte]
        have := A.adj k (x.val - l j) (by omega)
        rwa [show x.val - l j + 1 = y.val - l j by omega] at this
  refine ⟨(iso_of_bijective_hom (SimpleGraph.connected_pathGraph_add_one _) hT
    (fun x => A.av (pi x) (ps x)) (A.bijective_of_pos hcov pi ps ?_ ?_ ?_ ?_ ?_) ?_).some⟩
  · intro x y hx hy
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [ps] at hx hy
    split_ifs at hx hy <;> omega
  · intro x y h1 h2
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [pi, ps] at h1 h2
    split_ifs at h1 h2 <;> first | omega | exact absurd h1 hjk | exact absurd h1 hkj
  · intro x
    have := x.isLt
    simp only [pi, ps]
    split_ifs <;> omega
  · intro i' s hs hs0
    rcases fin3_cases i j k hij hjk hik i' with h | h | h
    · rw [h] at hs; omega
    · rw [h] at hs
      refine ⟨⟨l j - s, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
    · rw [h] at hs
      refine ⟨⟨l j + s, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
  · exact ⟨⟨l j, by omega⟩, by simp [ps]⟩
  · intro x y hxy
    rw [SimpleGraph.pathGraph_adj] at hxy
    rcases hxy with h | h
    · exact hstep x y h
    · exact (hstep y x h).symm

end ArmData

theorem adjD' (k : ℕ) {a b : Fin (k + 3)} (h : (graphOfCartan (CartanMatrix.D (k + 3))).Adj a b) :
    ((a.val + 1 = b.val ∧ b.val ≤ k) ∨ (a.val = k ∧ (b.val = k + 1 ∨ b.val = k + 2))) ∨
    ((b.val + 1 = a.val ∧ a.val ≤ k) ∨ (b.val = k ∧ (a.val = k + 1 ∨ a.val = k + 2))) := by
  obtain ⟨-, h1, -⟩ := (adj_D k a b).1 h
  unfold dN at h1
  split_ifs at h1 <;> omega

theorem adjE' {m : ℕ} {a b : Fin m} (h : (graphOfCartan (CartanMatrix.E m)).Adj a b) :
    ((a.val = 0 ∧ b.val = 2) ∨ (a.val = 1 ∧ b.val = 3) ∨ (a.val = 2 ∧ b.val = 3) ∨
      (3 ≤ a.val ∧ a.val + 1 = b.val)) ∨
    ((b.val = 0 ∧ a.val = 2) ∨ (b.val = 1 ∧ a.val = 3) ∨ (b.val = 2 ∧ a.val = 3) ∨
      (3 ≤ b.val ∧ b.val + 1 = a.val)) := by
  obtain ⟨-, h1, -⟩ := h
  simp only [CartanMatrix.E, Matrix.of_apply] at h1
  split_ifs at h1 <;> omega

namespace ArmData

variable {n : ℕ} {G : SimpleGraph (Fin n)} {l : Fin 3 → ℕ} (A : ArmData G l)

theorem iso_D (hcov : ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v) (hT : G.IsTree) {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (hi : l i = 1) (hj : l j = 1) :
    Nonempty (graphOfCartan (CartanMatrix.D (l k + 3)) ≃g G) := by
  have hji := hij.symm
  have hkj := hjk.symm
  have hki := hik.symm
  let pi : Fin (l k + 3) → Fin 3 := fun x => if x.val ≤ l k then k else if x.val = l k + 1 then i else j
  let ps : Fin (l k + 3) → ℕ := fun x => if x.val ≤ l k then l k - x.val else 1
  have hor : ∀ x y : Fin (l k + 3), ((x.val + 1 = y.val ∧ y.val ≤ l k) ∨
      (x.val = l k ∧ (y.val = l k + 1 ∨ y.val = l k + 2))) →
      G.Adj (A.av (pi x) (ps x)) (A.av (pi y) (ps y)) := by
    intro x y h
    have hyl := y.isLt
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
    · have hx : x.val ≤ l k := by omega
      simp only [pi, ps, hx, h2, ↓reduceIte]
      have := (A.adj k (l k - y.val) (by omega)).symm
      rwa [show l k - y.val + 1 = l k - x.val by omega] at this
    · have hx : x.val ≤ l k := by omega
      have hy : ¬ y.val ≤ l k := by omega
      simp only [pi, ps, hx, hy, h2, Nat.not_succ_le_self, ↓reduceIte]
      rw [show l k - x.val = 0 by omega, A.zero]
      exact A.adjc i (by omega)
    · have hx : x.val ≤ l k := by omega
      have hy : ¬ y.val ≤ l k := by omega
      have hy1 : ¬ y.val = l k + 1 := by omega
      simp only [pi, ps, hx, hy, hy1, ↓reduceIte]
      rw [show l k - x.val = 0 by omega, A.zero]
      exact A.adjc j (by omega)
  refine iso_of_bijective_hom (connected_D (l k)) hT (fun x => A.av (pi x) (ps x))
    (A.bijective_of_pos hcov pi ps ?_ ?_ ?_ ?_ ?_) ?_
  · intro x y hx hy
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [ps] at hx hy
    split_ifs at hx hy <;> omega
  · intro x y h1 h2
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [pi, ps] at h1 h2
    split_ifs at h1 h2 <;>
      first | omega | exact absurd h1 hij | exact absurd h1 hji | exact absurd h1 hjk |
        exact absurd h1 hkj | exact absurd h1 hik | exact absurd h1 hki
  · intro x
    have := x.isLt
    simp only [pi, ps]
    split_ifs <;> omega
  · intro i' s hs hs0
    rcases fin3_cases i j k hij hjk hik i' with h | h | h
    · rw [h] at hs
      refine ⟨⟨l k + 1, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
    · rw [h] at hs
      refine ⟨⟨l k + 2, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
    · rw [h] at hs
      refine ⟨⟨l k - s, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
  · exact ⟨⟨l k, by omega⟩, by simp [ps]⟩
  · intro x y hxy
    rcases adjD' (l k) hxy with h | h
    · exact hor x y h
    · exact (hor y x h).symm

theorem iso_E (hcov : ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v) (hT : G.IsTree) {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (hi : l i = 1) (hj : l j = 2)
    (hM : (graphOfCartan (CartanMatrix.E (l k + 4))).Connected) :
    Nonempty (graphOfCartan (CartanMatrix.E (l k + 4)) ≃g G) := by
  have hji := hij.symm
  have hkj := hjk.symm
  have hki := hik.symm
  let pi : Fin (l k + 4) → Fin 3 := fun x =>
    if x.val = 0 then j else if x.val = 1 then i else if x.val = 2 then j else k
  let ps : Fin (l k + 4) → ℕ := fun x =>
    if x.val = 0 then 2 else if x.val = 1 then 1 else if x.val = 2 then 1 else x.val - 3
  have hor : ∀ x y : Fin (l k + 4), ((x.val = 0 ∧ y.val = 2) ∨ (x.val = 1 ∧ y.val = 3) ∨
      (x.val = 2 ∧ y.val = 3) ∨ (3 ≤ x.val ∧ x.val + 1 = y.val)) →
      G.Adj (A.av (pi x) (ps x)) (A.av (pi y) (ps y)) := by
    intro x y h
    have hyl := y.isLt
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp +decide only [pi, ps, h1, h2, ↓reduceIte]
      exact (A.adj j 1 (by omega)).symm
    · simp +decide only [pi, ps, h1, h2, ↓reduceIte, Nat.reduceSub]
      rw [A.zero]
      exact (A.adjc i (by omega)).symm
    · simp +decide only [pi, ps, h1, h2, ↓reduceIte, Nat.reduceSub]
      rw [A.zero]
      exact (A.adjc j (by omega)).symm
    · have hx0 : ¬ x.val = 0 := by omega
      have hx1 : ¬ x.val = 1 := by omega
      have hx2 : ¬ x.val = 2 := by omega
      have hy0 : ¬ y.val = 0 := by omega
      have hy1 : ¬ y.val = 1 := by omega
      have hy2 : ¬ y.val = 2 := by omega
      simp only [pi, ps, hx0, hx1, hx2, hy0, hy1, hy2, ↓reduceIte]
      have := A.adj k (x.val - 3) (by omega)
      rwa [show x.val - 3 + 1 = y.val - 3 by omega] at this
  refine iso_of_bijective_hom hM hT (fun x => A.av (pi x) (ps x))
    (A.bijective_of_pos hcov pi ps ?_ ?_ ?_ ?_ ?_) ?_
  · intro x y hx hy
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [ps] at hx hy
    split_ifs at hx hy <;> omega
  · intro x y h1 h2
    have := x.isLt
    have := y.isLt
    apply Fin.ext
    simp only [pi, ps] at h1 h2
    split_ifs at h1 h2 <;>
      first | omega | exact absurd h1 hij | exact absurd h1 hji | exact absurd h1 hjk |
        exact absurd h1 hkj | exact absurd h1 hik | exact absurd h1 hki
  · intro x
    have := x.isLt
    simp only [pi, ps]
    split_ifs <;> omega
  · intro i' s hs hs0
    rcases fin3_cases i j k hij hjk hik i' with h | h | h
    · rw [h] at hs
      refine ⟨⟨1, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
    · rw [h] at hs
      by_cases hs1 : s = 1
      · refine ⟨⟨2, by omega⟩, ?_⟩
        simp [pi, ps, h] <;> omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simp [pi, ps, h] <;> omega
    · rw [h] at hs
      refine ⟨⟨s + 3, by omega⟩, ?_⟩
      simp [pi, ps, h] <;> omega
  · exact ⟨⟨3, by omega⟩, by simp [ps]⟩
  · intro x y hxy
    rcases adjE' hxy with h | h
    · exact hor x y h
    · exact (hor y x h).symm

theorem iso_E' (hcov : ∀ v, ∃ i s, s ≤ l i ∧ A.av i s = v) (hT : G.IsTree) {i j k : Fin 3} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (hi : l i = 1) (hj : l j = 2) (r : ℕ) (hk : l k = r)
    (hM : (graphOfCartan (CartanMatrix.E (r + 4))).Connected) :
    Nonempty (graphOfCartan (CartanMatrix.E (r + 4)) ≃g G) := by
  subst hk
  exact A.iso_E hcov hT hij hjk hik hi hj hM

end ArmData

theorem card_eq_of_iso {a b : ℕ} {M : SimpleGraph (Fin a)} {G : SimpleGraph (Fin b)} (e : M ≃g G) :
    a = b := by
  simpa using Fintype.card_congr e.toEquiv

theorem exists_sorted (l : Fin 3 → ℕ) :
    ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ l i ≤ l j ∧ l j ≤ l k := by
  rcases le_total (l 0) (l 1) with h01 | h01 <;> rcases le_total (l 1) (l 2) with h12 | h12 <;>
    rcases le_total (l 0) (l 2) with h02 | h02 <;>
    first
      | exact ⟨0, 1, 2, by decide, by decide, by decide, by omega, by omega⟩
      | exact ⟨0, 2, 1, by decide, by decide, by decide, by omega, by omega⟩
      | exact ⟨1, 0, 2, by decide, by decide, by decide, by omega, by omega⟩
      | exact ⟨1, 2, 0, by decide, by decide, by decide, by omega, by omega⟩
      | exact ⟨2, 0, 1, by decide, by decide, by decide, by omega, by omega⟩
      | exact ⟨2, 1, 0, by decide, by decide, by decide, by omega, by omega⟩

/-- **Problem 5.3 (classification, converse half).**  A connected graph on `Fin n` whose form
`2 I - adjacency` is positive definite is isomorphic to the path graph `A_n`, to the graph of
`CartanMatrix.D n` (`n ≥ 3`), or to the graph of `CartanMatrix.E 6`, `E 7` or `E 8`.  Together with
`isDynkin_pathGraph`, `isDynkin_D`, `isDynkin_E6`, `isDynkin_E7`, `isDynkin_E8` this is the classification
of simply laced Dynkin diagrams.  The proof follows the book: forbidden subgraphs (cycles, `D̃_n`, `Ẽ_6`,
`Ẽ_7`, `Ẽ_8`) leave a path or a tree with one branch vertex whose arms of lengths `p ≤ q ≤ r` are
`(1, 1, r)`, `(1, 2, 2)`, `(1, 2, 3)` or `(1, 2, 4)`; the isomorphisms with the standard diagrams come from
a bijective homomorphism onto a tree. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem classification_dynkin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : IsDynkin G) :
    Nonempty (SimpleGraph.pathGraph n ≃g G) ∨
    (3 ≤ n ∧ Nonempty (graphOfCartan (CartanMatrix.D n) ≃g G)) ∨
    (n = 6 ∧ Nonempty (graphOfCartan (CartanMatrix.E 6) ≃g G)) ∨
    (n = 7 ∧ Nonempty (graphOfCartan (CartanMatrix.E 7) ≃g G)) ∨
    (n = 8 ∧ Nonempty (graphOfCartan (CartanMatrix.E 8) ≃g G)) := by
  obtain ⟨hconn, hG⟩ := h
  have hT : G.IsTree := ⟨hconn, hG.isAcyclic⟩
  obtain ⟨l, A, hcov⟩ := exists_armData hconn hG
  obtain ⟨i, j, k, hij, hjk, hik, hij', hjk'⟩ := exists_sorted l
  have hmin : ∀ x, l i ≤ l x := by
    intro x
    rcases fin3_cases i j k hij hjk hik x with h | h | h <;> rw [h] <;> omega
  by_cases h0 : l i = 0
  · left
    obtain ⟨e⟩ := A.iso_path hcov hT hij hjk hik h0
    obtain rfl := card_eq_of_iso e
    exact ⟨e⟩
  · right
    have hi : l i = 1 := by
      by_contra hne
      exact A.no_E6 hG (by have := hmin 0; omega) (by have := hmin 1; omega) (by have := hmin 2; omega)
    by_cases hj1 : l j = 1
    · left
      obtain ⟨e⟩ := A.iso_D hcov hT hij hjk hik hi hj1
      obtain rfl := card_eq_of_iso e
      exact ⟨by omega, ⟨e⟩⟩
    · right
      have hj2 : l j = 2 := by
        by_contra hne
        exact A.no_E7 hG hij hjk hik (by omega) (by omega) (by omega)
      have hk4 : l k ≤ 4 := by
        by_contra hne
        exact A.no_E8 hG hij hjk hik (by omega) (by omega) (by omega)
      have hkk : l k = 2 ∨ l k = 3 ∨ l k = 4 := by omega
      rcases hkk with hk | hk | hk
      · left
        obtain ⟨e⟩ := A.iso_E' hcov hT hij hjk hik hi hj2 2 hk connected_E6
        obtain rfl := card_eq_of_iso e
        exact ⟨rfl, ⟨e⟩⟩
      · right; left
        obtain ⟨e⟩ := A.iso_E' hcov hT hij hjk hik hi hj2 3 hk connected_E7
        obtain rfl := card_eq_of_iso e
        exact ⟨rfl, ⟨e⟩⟩
      · right; right
        obtain ⟨e⟩ := A.iso_E' hcov hT hij hjk hik hi hj2 4 hk connected_E8
        obtain rfl := card_eq_of_iso e
        exact ⟨rfl, ⟨e⟩⟩

end UndergradKB.RepresentationTheory.Roots
