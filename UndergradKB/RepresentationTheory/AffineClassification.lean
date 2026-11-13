import UndergradKB.RepresentationTheory.AffineEmbedding
import UndergradKB.RepresentationTheory.AffineDiagrams
import UndergradKB.Common.Attr

/-! # Classification of affine Dynkin diagrams (Etingof et al., Problem 5.3(g))

A (simply laced) affine Dynkin diagram is a connected loopless graph whose form `2 I - adjacency` is positive
semidefinite but not positive definite (`IsAffineDynkin`). We prove that these are exactly the forbidden diagrams
of Problem 5.3: the cycles `Ã_k` (`affineCycle`), `D̃_k` (`affineD`), `Ẽ_6`, `Ẽ_7`, `Ẽ_8`.

* `not_noForb_of_not_posDefinite`: a connected graph without forbidden subgraphs is one of `A_n`, `D_n`, `E_6`,
  `E_7`, `E_8` (`classification_noForb`), hence positive definite; so a connected graph that is not positive
  definite contains a forbidden diagram.
* `exists_embed_affineD`: a path with two extra neighbours at each end is an embedded `D̃`.
* `iso_of_embed_affine`: in a semidefinite connected graph an embedded affine diagram is the whole graph.
* `classification_affine`, and the converse `isAffineDynkin_of_classification`.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix Finset

/-- A connected graph containing no forbidden diagram is positive definite. -/
theorem posDefinite_of_noForb {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hc : G.Connected)
    (hF : NoForb G) : PosDefinite G := by
  rcases classification_noForb G hc hF with h1 | ⟨h3, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · obtain ⟨e⟩ := h1
    exact (posDefinite_pathGraph n).of_embedding e.symm e.symm.injective fun i j h => e.symm.map_rel_iff.2 h
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact (posDefinite_D k).of_embedding e.symm e.symm.injective fun i j h => e.symm.map_rel_iff.2 h
  · exact posDefinite_E6.of_embedding e.symm e.symm.injective fun i j h => e.symm.map_rel_iff.2 h
  · exact posDefinite_E7.of_embedding e.symm e.symm.injective fun i j h => e.symm.map_rel_iff.2 h
  · exact posDefinite_E8.of_embedding e.symm e.symm.injective fun i j h => e.symm.map_rel_iff.2 h

/-- **Etingof et al., Problem 5.3**: a connected graph is positive definite if and only if it contains none of
the forbidden diagrams (cycles, `D̃_k`, `Ẽ_6`, `Ẽ_7`, `Ẽ_8`). -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem posDefinite_iff_noForb {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hc : G.Connected) :
    PosDefinite G ↔ NoForb G :=
  ⟨PosDefinite.noForb, posDefinite_of_noForb hc⟩

/-- A path `c 0, ..., c d` with two further neighbours `u1, u2` of `c 0` and `v1, v2` of `c d` (all distinct and
off the path) is an embedded copy of `D̃_d`. -/
theorem exists_embed_affineD {n : ℕ} {G : SimpleGraph (Fin n)} {c : ℕ → Fin n} {d : ℕ} (hc : IsPS G c d)
    {u1 u2 v1 v2 : Fin n} (hu1 : G.Adj (c 0) u1) (hu2 : G.Adj (c 0) u2) (hv1 : G.Adj (c d) v1)
    (hv2 : G.Adj (c d) v2) (n1 : ∀ i, i ≤ d → c i ≠ u1) (n2 : ∀ i, i ≤ d → c i ≠ u2)
    (n3 : ∀ i, i ≤ d → c i ≠ v1) (n4 : ∀ i, i ≤ d → c i ≠ v2) (h12 : u1 ≠ u2) (h13 : u1 ≠ v1)
    (h14 : u1 ≠ v2) (h23 : u2 ≠ v1) (h24 : u2 ≠ v2) (h34 : v1 ≠ v2) :
    ∃ f : Fin (d + 5) → Fin n, Function.Injective f ∧ ∀ i j, (affineD d).Adj i j → G.Adj (f i) (f j) := by
  let g : ℕ → Fin n := fun t =>
    if t ≤ d then c t else if t = d + 1 then u1 else if t = d + 2 then u2 else if t = d + 3 then v1 else v2
  have hg : ∀ t, t ≤ d + 4 → ∀ s, s ≤ d + 4 → g t = g s → t = s := by
    intro t ht s hs hts
    simp only [g] at hts
    by_cases a1 : t ≤ d <;> by_cases b1 : s ≤ d
    · simp only [a1, b1, ite_true] at hts; exact hc.1 t s a1 b1 hts
    all_goals
      simp only [a1, b1, ite_true, ite_false] at hts
      split_ifs at hts <;> first
        | omega
        | exact absurd hts ‹_›
        | exact absurd hts.symm ‹_›
        | exact absurd hts (n1 _ (by omega))
        | exact absurd hts (n2 _ (by omega))
        | exact absurd hts (n3 _ (by omega))
        | exact absurd hts (n4 _ (by omega))
        | exact absurd hts.symm (n1 _ (by omega))
        | exact absurd hts.symm (n2 _ (by omega))
        | exact absurd hts.symm (n3 _ (by omega))
        | exact absurd hts.symm (n4 _ (by omega))
  have hadj : ∀ a b, affineDAdj d a b → a ≤ d + 4 → b ≤ d + 4 → G.Adj (g a) (g b) := by
    intro a b h ha hb
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · subst h1
      have := hc.2 a (by omega)
      simp only [g, show a ≤ d by omega, h2, ite_true]
      exact this
    · subst h1 h2; simpa [g] using hu1
    · subst h1 h2; simpa [g] using hu2
    · subst h1 h2; simpa [g] using hv1
    · subst h1 h2; simpa [g] using hv2
  refine ⟨fun t => g t.val, fun s t h => Fin.ext (hg _ (by omega) _ (by omega) h), fun i j h => ?_⟩
  rcases (affineD_adj_iff d i j).1 h with h | h
  · exact hadj _ _ h (by omega) (by omega)
  · exact (hadj _ _ h (by omega) (by omega)).symm

/-- **Etingof et al., Problem 5.3(g)**: classification of affine Dynkin diagrams. A connected graph whose form
`2 I - adjacency` is positive semidefinite but not positive definite is isomorphic to a cycle `Ã_k`
(`k + 3` vertices), to `D̃_k` (`k + 5` vertices), or to `Ẽ_6`, `Ẽ_7`, `Ẽ_8`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem classification_affine {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : IsAffineDynkin G) :
    (∃ k, Nonempty (affineCycle k ≃g G)) ∨ (∃ k, Nonempty (affineD k ≃g G)) ∨
    Nonempty (affineE6 ≃g G) ∨ Nonempty (affineE7 ≃g G) ∨
    Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g G) := by
  obtain ⟨hc, hpsd, hnpd⟩ := h
  have hNF : ¬ NoForb G := fun hF => hnpd (posDefinite_of_noForb hc hF)
  by_cases hcyc : ∀ (k : ℕ) (f : Fin (k + 3) → Fin n), Function.Injective f →
      (∀ i j, (affineCycle k).Adj i j → G.Adj (f i) (f j)) → False
  swap
  · push Not at hcyc
    obtain ⟨k, f, hf, hhom, -⟩ := hcyc
    exact Or.inl ⟨k, iso_of_embed_affine (affine_cycle k) hc hpsd f hf hhom⟩
  by_cases hdt : ∀ {c : ℕ → Fin n} {d : ℕ}, IsPS G c d → ∀ {u1 u2 v1 v2 : Fin n}, G.Adj (c 0) u1 →
      G.Adj (c 0) u2 → G.Adj (c d) v1 → G.Adj (c d) v2 → (∀ i, i ≤ d → c i ≠ u1) → (∀ i, i ≤ d → c i ≠ u2) →
      (∀ i, i ≤ d → c i ≠ v1) → (∀ i, i ≤ d → c i ≠ v2) → u1 ≠ u2 → u1 ≠ v1 → u1 ≠ v2 → u2 ≠ v1 → u2 ≠ v2 →
      v1 ≠ v2 → False
  swap
  · push Not at hdt
    obtain ⟨c, d, hcd, u1, u2, v1, v2, hu1, hu2, hv1, hv2, n1, n2, n3, n4, h12, h13, h14, h23, h24, h34, -⟩ := hdt
    obtain ⟨f, hf, hhom⟩ := exists_embed_affineD hcd hu1 hu2 hv1 hv2 n1 n2 n3 n4 h12 h13 h14 h23 h24 h34
    exact Or.inr (Or.inl ⟨d, iso_of_embed_affine (affine_D d) hc hpsd f hf hhom⟩)
  by_cases h6 : ∀ f : Fin 7 → Fin n, Function.Injective f → (∀ i j, affineE6.Adj i j → G.Adj (f i) (f j)) → False
  swap
  · push Not at h6
    obtain ⟨f, hf, hhom, -⟩ := h6
    exact Or.inr (Or.inr (Or.inl (iso_of_embed_affine affine_E6 hc hpsd f hf hhom)))
  by_cases h7 : ∀ f : Fin 8 → Fin n, Function.Injective f → (∀ i j, affineE7.Adj i j → G.Adj (f i) (f j)) → False
  swap
  · push Not at h7
    obtain ⟨f, hf, hhom, -⟩ := h7
    exact Or.inr (Or.inr (Or.inr (Or.inl (iso_of_embed_affine affine_E7 hc hpsd f hf hhom))))
  by_cases h8 : ∀ f : Fin 9 → Fin n, Function.Injective f →
      (∀ i j, (graphOfCartan (CartanMatrix.E 9)).Adj i j → G.Adj (f i) (f j)) → False
  swap
  · push Not at h8
    obtain ⟨f, hf, hhom, -⟩ := h8
    exact Or.inr (Or.inr (Or.inr (Or.inr (iso_of_embed_affine affine_E8 hc hpsd f hf hhom))))
  exact absurd ⟨hcyc, hdt, h6, h7, h8⟩ hNF

/-- `IsAffineDynkin` is invariant under graph isomorphism. -/
theorem IsAffineKernel.isAffineDynkin_of_iso {m n : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {v : Fin m → ℤ} (hH : IsAffineKernel H v)
    (hHc : H.Connected) (e : H ≃g G) : IsAffineDynkin G := by
  have hv' : ∀ i, 0 < v (e.symm i) := fun i => hH.1 _
  have hMv : cartanMatrix G *ᵥ (fun i => v (e.symm i)) = 0 := by
    funext i
    have := congrFun hH.2.1 (e.symm i)
    have hcm : ∀ a b, cartanMatrix G a b = cartanMatrix H (e.symm a) (e.symm b) := fun a b => by
      rw [cartanMatrix_apply, cartanMatrix_apply]
      simp only [e.symm.injective.eq_iff, e.symm.map_rel_iff]
    simp only [mulVec, dotProduct, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Fintype.sum_equiv e.symm.toEquiv _ _ fun j => by rw [hcm]; rfl
  have hGc : G.Connected := hHc.map e.toHom e.surjective
  have := NeZero.mk (fun h0 : n = 0 => by subst h0; obtain ⟨x⟩ := hGc.nonempty; exact x.elim0)
  exact (isAffineKernel_of_pos G hGc _ hv' hMv).isAffineDynkin hGc

/-- **Etingof et al., Problem 5.3(g)**, converse: the cycles, `D̃_k`, `Ẽ_6`, `Ẽ_7`, `Ẽ_8` (and every graph
isomorphic to one of them) are affine Dynkin diagrams. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_of_classification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : (∃ k, Nonempty (affineCycle k ≃g G)) ∨ (∃ k, Nonempty (affineD k ≃g G)) ∨
      Nonempty (affineE6 ≃g G) ∨ Nonempty (affineE7 ≃g G) ∨
      Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g G)) : IsAffineDynkin G := by
  rcases h with ⟨k, ⟨e⟩⟩ | ⟨k, ⟨e⟩⟩ | h | h | h
  · exact (affine_cycle k).isAffineDynkin_of_iso (connected_affineCycle k) e
  · exact (affine_D k).isAffineDynkin_of_iso (connected_affineD k) e
  · obtain ⟨e⟩ := h; exact affine_E6.isAffineDynkin_of_iso connected_affineE6 e
  · obtain ⟨e⟩ := h; exact affine_E7.isAffineDynkin_of_iso connected_affineE7 e
  · obtain ⟨e⟩ := h; exact affine_E8.isAffineDynkin_of_iso connected_E9 e

end UndergradKB.RepresentationTheory.Roots
