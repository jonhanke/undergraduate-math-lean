import UndergradKB.RepresentationTheory.DynkinClassification
import UndergradKB.Common.Attr

/-! # An affine diagram inside a semidefinite graph is the whole graph (Etingof et al., Problem 5.3(g))

If a connected graph `G` has positive semidefinite form `2 I - (adjacency)` and an affine diagram `H` (a graph
whose form is semidefinite with kernel spanned by a positive vector `v`, `IsAffineKernel`) embeds into `G` (an
injective vertex map sending edges to edges), then the embedding is an isomorphism `H ≃g G`
(`iso_of_embed_affine`).

Proof: extend `v` by zero to `V` on `G`. Since `G` has at least the edges of `H`, the form of `G` at `V` is the form
of `H` at `v`, which is `0`, minus the products `v_i v_j` over the additional edges; semidefiniteness forces no
additional edges among the image and `A_G V = 0`. A vertex `b` outside the image adjacent to the image would give
`(A_G V)_b < 0`, so by connectedness the image is everything.

This is the step that turns "contains an affine diagram" into "is that affine diagram" in the classification of
affine Dynkin diagrams.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix Finset

/-- **Etingof et al., Problem 5.3(g)** (step): an affine diagram embedded into a connected graph with positive
semidefinite form fills the whole graph, and the embedding reflects edges. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem bijective_of_embed_affine {m n : ℕ} [NeZero m] {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {v : Fin m → ℤ} (hH : IsAffineKernel H v) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hc : G.Connected) (hG : (cartanReal G).PosSemidef) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) :
    Function.Bijective f ∧ ∀ i j, G.Adj (f i) (f j) → H.Adj i j := by
  obtain ⟨hv, hMv, -, -⟩ := hH
  set y : Fin m → ℝ := fun i => (v i : ℝ) with hy
  have hypos : ∀ i, 0 < y i := fun i => by simp [hy, hv i]
  set Y : Fin n → ℝ := Function.extend f y (0 : Fin n → ℝ) with hYdef
  have hY : ∀ i, Y (f i) = y i := fun i => hf.extend_apply _ _ _
  have hY0 : ∀ a, a ∉ Set.range f → Y a = 0 := fun a ha =>
    by simpa [hYdef] using Function.extend_apply' y (0 : Fin n → ℝ) a (by simpa using ha)
  -- the form of `H` at `v` vanishes
  have hHv : ∑ i, ∑ j, y i * (cartanMatrix H i j : ℝ) * y j = 0 := by
    have : ∀ i, ∑ j, (cartanMatrix H i j : ℝ) * y j = 0 := fun i => by
      have := congrFun hMv i
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      simp only [hy]
      exact_mod_cast this
    calc ∑ i, ∑ j, y i * (cartanMatrix H i j : ℝ) * y j
        = ∑ i, y i * ∑ j, (cartanMatrix H i j : ℝ) * y j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by simp [this]
  -- the form of `G` at `Y`
  have hsum : ∑ a, ∑ b, Y a * (cartanMatrix G a b : ℝ) * Y b =
      ∑ i, ∑ j, y i * (cartanMatrix G (f i) (f j) : ℝ) * y j := by
    symm
    refine Fintype.sum_of_injective f hf _ _ (fun a ha => ?_) (fun i => ?_)
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [hY0 a ha]; ring
    · refine Fintype.sum_of_injective f hf _ _ (fun b hb => ?_) (fun j => ?_)
      · rw [hY0 b hb]; ring
      · rw [hY, hY]
  have hnn : 0 ≤ Y ⬝ᵥ (cartanReal G *ᵥ Y) := by
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hG).2 Y
    simpa using this
  rw [dot_cartanReal_eq_sum, hsum] at hnn
  -- termwise comparison
  have hterm : ∀ i j, y i * (cartanMatrix G (f i) (f j) : ℝ) * y j ≤ y i * (cartanMatrix H i j : ℝ) * y j := by
    intro i j
    have hle : ((cartanMatrix G (f i) (f j) : ℤ) : ℝ) ≤ (cartanMatrix H i j : ℝ) := by
      exact_mod_cast cartanMatrix_embed_le f hf hHG i j
    have hyy : 0 ≤ y i * y j := (mul_pos (hypos i) (hypos j)).le
    nlinarith
  have hdiff : ∑ i, ∑ j, (y i * (cartanMatrix H i j : ℝ) * y j - y i * (cartanMatrix G (f i) (f j) : ℝ) * y j)
      = 0 := by
    have hle : ∑ i, ∑ j, y i * (cartanMatrix G (f i) (f j) : ℝ) * y j ≤
        ∑ i, ∑ j, y i * (cartanMatrix H i j : ℝ) * y j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    simp only [Finset.sum_sub_distrib]
    linarith
  have hdiff0 : ∀ i j, y i * (cartanMatrix H i j : ℝ) * y j = y i * (cartanMatrix G (f i) (f j) : ℝ) * y j := by
    have hnn' : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ ∑ j, (y i * (cartanMatrix H i j : ℝ) * y j -
        y i * (cartanMatrix G (f i) (f j) : ℝ) * y j) :=
      fun i _ => Finset.sum_nonneg fun j _ => sub_nonneg.2 (hterm i j)
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 hdiff i (mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hterm i j))).1 h1 j (mem_univ _)
    linarith
  -- edges are reflected
  have hrefl : ∀ i j, G.Adj (f i) (f j) → H.Adj i j := by
    intro i j hadj
    by_contra hno
    have hij : i ≠ j := fun e => by subst e; exact G.irrefl hadj
    have e1 : cartanMatrix G (f i) (f j) = -1 := by
      rw [cartanMatrix_apply]; simp [hf.ne hij, hadj]
    have e2 : cartanMatrix H i j = 0 := by
      rw [cartanMatrix_apply]; simp [hij, hno]
    have := hdiff0 i j
    rw [e1, e2] at this
    have := mul_pos (hypos i) (hypos j)
    push_cast at *
    nlinarith
  refine ⟨⟨hf, ?_⟩, hrefl⟩
  -- the form vanishes, so `A_G Y = 0`
  have hzero : Y ⬝ᵥ (cartanReal G *ᵥ Y) = 0 := by
    rw [dot_cartanReal_eq_sum, hsum]
    have : ∑ i, ∑ j, y i * (cartanMatrix G (f i) (f j) : ℝ) * y j =
        ∑ i, ∑ j, y i * (cartanMatrix H i j : ℝ) * y j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hdiff0 i j).symm
    rw [this, hHv]
  have hAY : cartanReal G *ᵥ Y = 0 := by
    have := hG.dotProduct_mulVec_zero_iff (x := Y)
    simp only [star_trivial] at this
    exact this.1 hzero
  -- no edge leaves the image
  have hnoedge : ∀ i b, b ∉ Set.range f → ¬ G.Adj b (f i) := by
    intro i b hb hadj
    have hb' := congrFun hAY b
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at hb'
    have hsplit : ∑ a, (cartanMatrix G b a : ℝ) * Y a = ∑ j, (cartanMatrix G b (f j) : ℝ) * y j := by
      symm
      refine Fintype.sum_of_injective f hf _ _ (fun a ha => ?_) (fun j => ?_)
      · rw [hY0 a ha]; ring
      · rw [hY]
    rw [hsplit] at hb'
    have hle : ∀ j ∈ (univ : Finset (Fin m)), (cartanMatrix G b (f j) : ℝ) * y j ≤ 0 := by
      intro j _
      have hne : b ≠ f j := fun e => hb ⟨j, e.symm⟩
      have := cartanMatrix_offDiag_nonpos G hne
      have h0 : (cartanMatrix G b (f j) : ℝ) ≤ 0 := by exact_mod_cast this
      nlinarith [hypos j]
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hle).1 hb' i (mem_univ _)
    have hne : b ≠ f i := fun e => hb ⟨i, e.symm⟩
    have e1 : cartanMatrix G b (f i) = -1 := by
      rw [cartanMatrix_apply]; simp [hne, hadj]
    rw [e1] at hall
    have := hypos i
    push_cast at hall
    linarith
  intro b
  by_contra hb
  have hb' : b ∉ Set.range f := fun ⟨i, hi⟩ => hb ⟨i, hi⟩
  obtain ⟨x, hx, z, hz, hadj⟩ := exists_boundary hc (Set.range f) ⟨f 0, 0, rfl⟩ ⟨b, hb'⟩
  obtain ⟨i, rfl⟩ := hx
  exact hnoedge i z hz hadj.symm

/-- **Etingof et al., Problem 5.3(g)** (step): an affine diagram embedded into a connected graph with positive
semidefinite form is isomorphic to it. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem iso_of_embed_affine {m n : ℕ} [NeZero m] {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {v : Fin m → ℤ} (hH : IsAffineKernel H v) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hc : G.Connected) (hG : (cartanReal G).PosSemidef) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) : Nonempty (H ≃g G) := by
  obtain ⟨hb, hr⟩ := bijective_of_embed_affine hH hc hG f hf hHG
  exact ⟨{ toEquiv := Equiv.ofBijective f hb, map_rel_iff' := fun {i j} => ⟨hr i j, hHG i j⟩ }⟩

end UndergradKB.RepresentationTheory.Roots
