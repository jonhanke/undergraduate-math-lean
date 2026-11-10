import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.BigOperators
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.PruferTree
import UndergradKB.Combinatorics.Graph.Prufer

/-!
# Cayley's formula (Keller–Trotter, Theorem 5.39)

The Prüfer code is a bijection from labelled trees on `[n] = Fin n` (`n ≥ 2`) to strings of length
`n - 2` over `Fin n` (`List.Vector (Fin n) (n - 2)`), whence there are `n ^ (n - 2)` labelled trees.
-/

namespace UndergradKB.Combinatorics.Prufer

open SimpleGraph

/-- The Prüfer code of a labelled tree on `Fin n`, as a string of length `n - 2`. -/
noncomputable def pruferVec (n : ℕ) (hn : 2 ≤ n) (T : {G : SimpleGraph (Fin n) // G.IsTree}) :
    List.Vector (Fin n) (n - 2) :=
  ⟨prufer Finset.univ T.1, by
    have := (prufer_length_mem (isTreeOn_univ_iff.2 T.2) (by simpa using hn)).1
    simpa using this⟩

/-- CO-122. The Prüfer code is a bijection between the labelled trees on `[n]` and the strings of
length `n - 2` over `[n]` (`n ≥ 2`). -/
@[kb "kellertrotter2017" "Theorem 5.39 (proof), p. 122"]
theorem pruferVec_bijective (n : ℕ) (hn : 2 ≤ n) : Function.Bijective (pruferVec n hn) := by
  have hc : (Finset.univ : Finset (Fin n)).card = (n - 2) + 2 := by simp; omega
  have hcode : ∀ G : SimpleGraph (Fin n), prufer Finset.univ G = pruferAux (n - 2) Finset.univ G := by
    intro G; simp [prufer]
  constructor
  · intro T₁ T₂ h
    have h' : prufer Finset.univ T₁.1 = prufer Finset.univ T₂.1 := congrArg Subtype.val h
    rw [hcode, hcode] at h'
    exact Subtype.ext (pruferAux_inj (n - 2) _ _ _ (isTreeOn_univ_iff.2 T₁.2)
      (isTreeOn_univ_iff.2 T₂.2) hc h')
  · intro v
    obtain ⟨G, hG, hcG⟩ := pruferAux_surj (n - 2) Finset.univ hc v.1 v.2 (fun x _ => Finset.mem_univ x)
    exact ⟨⟨G, isTreeOn_univ_iff.1 hG⟩, Subtype.ext ((hcode G).trans hcG)⟩

/-- CO-016. Cayley's formula for `n ≥ 2`: the number of labelled trees on `n` vertices is
`n ^ (n - 2)`. -/
@[kb "kellertrotter2017" "Theorem 5.39, p. 121"]
theorem cayley_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (pruferVec_bijective n hn)), Nat.card_eq_fintype_card,
    card_vector, Fintype.card_fin]

/-- Cayley's formula for all `n ≥ 1` (for `n = 1` the only graph is a tree). -/
@[kb "kellertrotter2017" "Theorem 5.39, p. 121"]
theorem cayley (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have : Unique {T : SimpleGraph (Fin 1) // T.IsTree} :=
      ⟨⟨⟨⊥, IsTree.of_subsingleton⟩⟩, fun T => Subtype.ext (by
        ext a b
        obtain rfl : a = b := Subsingleton.elim a b
        simp)⟩
    simp
  · exact cayley_of_two_le n h

/-- Cayley's formula stated with `Fintype.card` (for any `Fintype` instance on the subtype). -/
theorem cayley_fintype (n : ℕ) (hn : 1 ≤ n) [Fintype {T : SimpleGraph (Fin n) // T.IsTree}] :
    Fintype.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  rw [Fintype.card_eq_nat_card]; exact cayley n hn

end UndergradKB.Combinatorics.Prufer
