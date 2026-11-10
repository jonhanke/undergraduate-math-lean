import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Graph.Ramsey
import UndergradKB.Combinatorics.Graph.Multigraph

/-!
# The diagonal Ramsey bound and Euler's theorem (necessity) for multigraphs

Source: Keller--Trotter, *Applied Combinatorics* (2017), pp. 102 and 255.
-/

namespace UndergradKB.Combinatorics

open Finset SimpleGraph

/-- CO-261. The diagonal Ramsey bound: for `n ≥ 1`, every graph on at least `C(2n-2, n-1)`
vertices contains an `n`-clique or an independent `n`-set; hence `R(n,n) ≤ C(2n-2, n-1)`.
(The Stirling asymptotic `C(2n-2,n-1) ~ 4^n / (4 sqrt(pi n))` is not formalized.) -/
@[kb "kellertrotter2017" "text, p. 255"]
theorem ramseyProp_diagonal (n : ℕ) (hn : 1 ≤ n) :
    RamseyProp n n (Nat.choose (2 * n - 2) (n - 1)) := by
  have h := ramseyProp_choose n n hn hn
  have e : n + n - 2 = 2 * n - 2 := by omega
  rwa [e] at h

/-- CO-261. `R(n,n) ≤ C(2n-2, n-1)`, together with existence of the Ramsey number. -/
@[kb "kellertrotter2017" "text, p. 255"]
theorem ramseyNumber_diagonal_le (n : ℕ) (hn : 1 ≤ n) :
    RamseyProp n n (ramseyNumber n n) ∧ ramseyNumber n n ≤ Nat.choose (2 * n - 2) (n - 1) := by
  have h := ramseyNumber_le n n hn hn
  have e : n + n - 2 = 2 * n - 2 := by omega
  rwa [e] at h

namespace Multigraph

variable {V E : Type*} (M : Multigraph V E)

open scoped Classical in
/-- CO-099 (converse). In a loopless multigraph with an Euler circuit, every vertex has even
degree: each passage through a vertex uses two edge ends. -/
@[kb "kellertrotter2017" "text, p. 102"]
theorem even_degree_of_isEulerian [Fintype E] (hM : M.Loopless) (h : M.IsEulerian) (v : V) :
    Even (M.degree v) := by
  obtain ⟨n, x, e, hlast, hends, huniq⟩ := h
  have hbij : Function.Bijective e := by
    refine ⟨fun i j hij => ?_, fun ε => (huniq ε).exists⟩
    exact (huniq (e i)).unique rfl hij.symm
  rw [M.degree_eq_card hM]
  have hcard : (Finset.univ.filter fun i : Fin n => v ∈ M.ends (e i)).card =
      (Finset.univ.filter fun ε => v ∈ M.ends ε).card :=
    Finset.card_equiv (Equiv.ofBijective e hbij) (by simp)
  rw [← hcard]
  have hne : ∀ i : Fin n, x i.castSucc ≠ x i.succ := by
    intro i heq
    have := hM (e i)
    rw [hends i, Sym2.mk_isDiag_iff] at this
    exact this heq
  let g : Fin (n + 1) → ℕ := fun j => if x j = v then 1 else 0
  have hsum : (Finset.univ.filter fun i : Fin n => v ∈ M.ends (e i)).card =
      ∑ i : Fin n, (g i.castSucc + g i.succ) := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g, hends i, Sym2.mem_iff]
    by_cases h1 : x i.castSucc = v
    · have : ¬ x i.succ = v := fun h2 => hne i (h1.trans h2.symm)
      simp [h1, this]
    · by_cases h2 : x i.succ = v
      · simp [h1, h2, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [hsum, Finset.sum_add_distrib]
  have h1 := Fin.sum_univ_castSucc g
  have h2 := Fin.sum_univ_succ g
  have h3 : g (Fin.last n) = g 0 := by simp [g, hlast]
  refine ⟨∑ i : Fin n, g i.castSucc, ?_⟩
  omega

/-- CO-099. Euler's theorem for finite loopless multigraphs: a connected loopless multigraph is
eulerian iff all its vertices have even degree. -/
@[kb "kellertrotter2017" "text, p. 102"]
theorem isEulerian_iff_even_degree [Fintype V] [Fintype E] (hM : M.Loopless)
    (hc : M.Connected) : M.IsEulerian ↔ ∀ v, Even (M.degree v) :=
  ⟨fun h v => M.even_degree_of_isEulerian hM h v, fun h =>
    M.isEulerian_of_even_degree hM hc h⟩

end Multigraph

end UndergradKB.Combinatorics
