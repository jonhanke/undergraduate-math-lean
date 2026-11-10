import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.MvPolynomial.Eval
import UndergradKB.Common.Attr

/-!
# Burnside's lemma, the cycle index, and Pólya's enumeration theorem (Keller–Trotter, Chapter 15)

A finite group `G` acts on a finite set `S`; it acts on colorings `S → C` by `(g • f) s = f (g⁻¹ • s)`
(Mathlib's `arrowAction`).  The cycles of `g` are the orbits of `⟨g⟩` on `S` (fixed points are
1-cycles).
-/

namespace UndergradKB.Combinatorics.Polya

open scoped Classical
open Finset MulAction

set_option linter.unusedSectionVars false

section Burnside

variable {G X R : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]

omit [Fintype X] in
lemma card_stabilizer_eq_of_mem_orbit {x y : X} (h : y ∈ orbit G x) :
    Fintype.card (stabilizer G y) = Fintype.card (stabilizer G x) :=
  Fintype.card_congr (stabilizerEquivStabilizerOfOrbitRel (orbitRel_apply.2 h)).toEquiv

/-- CO-316. For a finite group acting on a set, the stabilizers of the points of one orbit have
sizes adding up to the order of the group. -/
@[kb "kellertrotter2017" "Proposition 15.8, p. 322"]
theorem sum_card_stabilizer_orbit (x : X) :
    ∑ y ∈ (orbit G x).toFinset, Fintype.card (stabilizer G y) = Fintype.card G := by
  rw [Finset.sum_congr rfl (fun y hy => card_stabilizer_eq_of_mem_orbit (x := x) (by simpa using hy))]
  rw [sum_const, smul_eq_mul, Set.toFinset_card]
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- The pairs `(g, x)` with `g • x = x`, counted by `g` or by `x`. -/
lemma sum_fixed_eq_sum_stabilizer [AddCommMonoid R] (w : X → R) :
    ∑ g : G, ∑ x ∈ univ.filter (fun x => g • x = x), w x
      = ∑ x : X, Fintype.card (stabilizer G x) • w x := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, sum_const, Fintype.card_subtype]
  simp [mem_stabilizer_iff]

/-- Weighted Burnside lemma: for a weight `w` constant on orbits, the sum over `g` of the weights
of the points fixed by `g` is `|G|` times the sum of the weights of the orbits. -/
theorem sum_fixed_weight_eq [AddCommMonoid R] (w : X → R) (hw : ∀ (g : G) x, w (g • x) = w x) :
    ∑ g : G, ∑ x ∈ univ.filter (fun x => g • x = x), w x
      = Fintype.card G • ∑ ω : orbitRel.Quotient G X, w ω.out := by
  rw [sum_fixed_eq_sum_stabilizer, ← Finset.sum_fiberwise univ
    (fun x => (Quotient.mk'' x : orbitRel.Quotient G X)), smul_sum]
  refine sum_congr rfl fun ω _ => ?_
  have hmem : ∀ x, (Quotient.mk'' x : orbitRel.Quotient G X) = ω ↔ x ∈ orbit G ω.out := by
    intro x
    rw [← orbitRel.Quotient.mem_orbit,
      orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
  have hfib : ∀ x ∈ univ.filter (fun x => (Quotient.mk'' x : orbitRel.Quotient G X) = ω),
      Fintype.card (stabilizer G x) • w x = Fintype.card (stabilizer G ω.out) • w ω.out := by
    intro x hx
    have hx' : x ∈ orbit G ω.out := (hmem x).1 (by simpa using hx)
    rw [card_stabilizer_eq_of_mem_orbit hx']
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hx'
    rw [hw]
  rw [Finset.sum_congr rfl hfib, sum_const]
  have hcard : (univ.filter (fun x => (Quotient.mk'' x : orbitRel.Quotient G X) = ω)).card
      = Fintype.card (orbit G ω.out) := by
    rw [← Set.toFinset_card]
    congr 1
    ext x
    simp [hmem]
  rw [hcard, smul_smul, ← MulAction.card_orbit_mul_card_stabilizer_eq_card_group G ω.out]

end Burnside

attribute [local instance] arrowAction

section Invariant

variable {S C R : Type*} [Fintype S] [Fintype C] [CommSemiring R]

lemma card_fiber {H : Type*} [Group H] [MulAction H S] (q : orbitRel.Quotient H S) :
    (univ.filter fun s => (Quotient.mk'' s : orbitRel.Quotient H S) = q).card
      = Nat.card q.orbit := by
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext s
  simp [orbitRel.Quotient.mem_orbit]

/-- Colorings constant on the orbits of a group `H`, weighted by the product of the color weights
of the points: the sum factors over the orbits, each orbit of size `n` contributing
`∑_c w(c)^n`. -/
theorem sum_invariant_prod {H : Type*} [Group H] [MulAction H S] (w : C → R) :
    ∑ f ∈ univ.filter (fun f : S → C => ∀ (h : H) x, f (h • x) = f x), ∏ s, w (f s)
      = ∏ q : orbitRel.Quotient H S, ∑ c, w c ^ Nat.card q.orbit := by
  have hout : ∀ f : S → C, (∀ (h : H) x, f (h • x) = f x) →
      ∀ s, f (Quotient.mk'' s : orbitRel.Quotient H S).out = f s := by
    intro f hf s
    have : (Quotient.mk'' s : orbitRel.Quotient H S).out ∈ orbit H s := by
      rw [← orbitRel_apply]
      exact Quotient.exact (Quotient.out_eq' (Quotient.mk'' s : orbitRel.Quotient H S))
    obtain ⟨h, hh⟩ := mem_orbit_iff.1 this
    rw [← hh, hf]
  have step1 : ∑ f ∈ univ.filter (fun f : S → C => ∀ (h : H) x, f (h • x) = f x), ∏ s, w (f s)
      = ∑ h : orbitRel.Quotient H S → C, ∏ s, w (h (Quotient.mk'' s)) := by
    refine Finset.sum_nbij' (fun f q => f q.out) (fun h s => h (Quotient.mk'' s)) ?_ ?_ ?_ ?_ ?_
    · intro f _; simp
    · intro h _
      simp only [mem_filter, mem_univ, true_and]
      intro g x
      exact congrArg h orbitRel.Quotient.quotient_smul_eq
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      funext s
      exact hout f hf s
    · intro h _
      funext q
      simp
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      refine prod_congr rfl fun s _ => ?_
      show w (f s) = w (f (Quotient.mk'' s : orbitRel.Quotient H S).out)
      rw [hout f hf s]
  rw [step1]
  have step2 : ∀ h : orbitRel.Quotient H S → C,
      ∏ s, w (h (Quotient.mk'' s)) = ∏ q, w (h q) ^ Nat.card q.orbit := by
    intro h
    rw [← Finset.prod_fiberwise univ (fun s => (Quotient.mk'' s : orbitRel.Quotient H S))]
    refine prod_congr rfl fun q _ => ?_
    rw [prod_congr rfl (g := fun _ => w (h q)) (fun s hs => by rw [(mem_filter.1 hs).2]),
      prod_const, card_fiber]
  simp_rw [step2]
  exact (Fintype.prod_sum (fun (q : orbitRel.Quotient H S) (c : C) => w c ^ Nat.card q.orbit)).symm

end Invariant

section Cycles

variable {S : Type*} [Fintype S]

/-- CO-314. The cycle lengths of a permutation of a finite set, as a multiset, *including* the
fixed points (1-cycles).  The cycles of `σ` are the orbits of `⟨σ⟩` on `S`. -/
@[kb "kellertrotter2017" "text (cycle notation), p. 319"]
noncomputable def cycleLengths (σ : Equiv.Perm S) : Multiset ℕ :=
  (univ : Finset (orbitRel.Quotient (Subgroup.zpowers σ) S)).val.map fun q => Nat.card q.orbit

/-- The number of cycles of `σ`, counting fixed points as 1-cycles. -/
noncomputable def numCycles (σ : Equiv.Perm S) : ℕ :=
  Fintype.card (orbitRel.Quotient (Subgroup.zpowers σ) S)

lemma card_cycleLengths (σ : Equiv.Perm S) : (cycleLengths σ).card = numCycles σ := by
  simp [cycleLengths, numCycles]

/-- The number of cycles of length `k` of `σ`. -/
noncomputable def numCyclesOfLength (σ : Equiv.Perm S) (k : ℕ) : ℕ := (cycleLengths σ).count k

end Cycles

section Fixed

variable {S C R : Type*} [Fintype S] [Fintype C] [CommSemiring R]

/-- A coloring is fixed by a permutation exactly when it is constant on every cycle. -/
theorem smul_eq_iff_invariant (σ : Equiv.Perm S) (f : S → C) :
    σ • f = f ↔ ∀ (h : Subgroup.zpowers σ) x, f (h • x) = f x := by
  constructor
  · intro hf
    have hmem : σ ∈ stabilizer (Equiv.Perm S) f := hf
    have hle := Subgroup.zpowers_le.2 hmem
    intro h x
    have h1 : ((h⁻¹ : Subgroup.zpowers σ) : Equiv.Perm S) ∈ stabilizer (Equiv.Perm S) f :=
      hle (h⁻¹).2
    rw [mem_stabilizer_iff] at h1
    have := congrFun h1 x
    change f (((h⁻¹ : Subgroup.zpowers σ) : Equiv.Perm S)⁻¹ • x) = f x at this
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using this
  · intro H
    funext x
    exact H ⟨σ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers σ)⟩ x

/-- Weighted count of the colorings fixed by a permutation: a product over its cycles. -/
theorem sum_fixed_prod_perm (σ : Equiv.Perm S) (w : C → R) :
    ∑ f ∈ univ.filter (fun f : S → C => σ • f = f), ∏ s, w (f s)
      = ∏ q : orbitRel.Quotient (Subgroup.zpowers σ) S, ∑ c, w c ^ Nat.card q.orbit := by
  rw [← sum_invariant_prod (H := Subgroup.zpowers σ)]
  refine sum_congr ?_ fun _ _ => rfl
  ext f
  simp [smul_eq_iff_invariant]

/-- CO-318. A permutation fixes exactly `m ^ (number of cycles)` colorings with `m` colors: each
cycle has to be monochromatic. -/
@[kb "kellertrotter2017" "text (fixed colorings and cycles), p. 323"]
theorem card_fixed_colorings (σ : Equiv.Perm S) :
    (univ.filter fun f : S → C => σ • f = f).card = Fintype.card C ^ numCycles σ := by
  have := sum_fixed_prod_perm (R := ℕ) (C := C) σ (fun _ => 1)
  simpa [numCycles] using this

variable {G : Type*} [Group G] [Fintype G] [MulAction G S]

lemma toPerm_smul_eq (g : G) (f : S → C) : (toPerm g : Equiv.Perm S) • f = g • f := by
  funext x
  rfl

/-- CO-318 for a group action: the number of colorings fixed by `g` is `m ^ (cycles of g)`. -/
@[kb "kellertrotter2017" "text (fixed colorings and cycles), p. 323"]
theorem card_fixedBy_colorings (g : G) :
    Nat.card (fixedBy (S → C) g) = Fintype.card C ^ numCycles (toPerm g : Equiv.Perm S) := by
  rw [← card_fixed_colorings, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

end Fixed

section CycleIndex

variable {G : Type*} {S : Type*} [Fintype S]

/-- The monomial `∏ x_k ^ (number of k-cycles of σ)` attached to a permutation. -/
noncomputable def cycleMonomial (σ : Equiv.Perm S) : MvPolynomial ℕ ℚ :=
  ((cycleLengths σ).map fun k => MvPolynomial.X k).prod

lemma cycleMonomial_eq (σ : Equiv.Perm S) :
    cycleMonomial σ = ∏ k ∈ (cycleLengths σ).toFinset, MvPolynomial.X k ^ numCyclesOfLength σ k :=
  Finset.prod_multiset_map_count _ _

variable (G S) [Group G] [Fintype G] [MulAction G S]

/-- CO-319. The cycle index of a finite group `G` acting on `S`: the average over `g ∈ G` of the
monomial `∏ x_k ^ (number of k-cycles of g)`, as a polynomial in the variables `x_1, x_2, ...`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) cycle index, p. 324"]
noncomputable def cycleIndex : MvPolynomial ℕ ℚ :=
  MvPolynomial.C (1 / (Fintype.card G : ℚ)) * ∑ g : G, cycleMonomial (toPerm g : Equiv.Perm S)

variable {G S}

lemma aeval_cycleMonomial {A : Type*} [CommSemiring A] [Algebra ℚ A] (p : ℕ → A)
    (σ : Equiv.Perm S) :
    MvPolynomial.aeval p (cycleMonomial σ)
      = ∏ q : orbitRel.Quotient (Subgroup.zpowers σ) S, p (Nat.card q.orbit) := by
  simp only [cycleMonomial, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.aeval_X, cycleLengths]
  rfl

lemma aeval_cycleIndex {A : Type*} [CommSemiring A] [Algebra ℚ A] (p : ℕ → A) :
    MvPolynomial.aeval p (cycleIndex G S)
      = algebraMap ℚ A (1 / (Fintype.card G : ℚ)) *
        ∑ g : G, ∏ q : orbitRel.Quotient (Subgroup.zpowers (toPerm g : Equiv.Perm S)) S,
          p (Nat.card q.orbit) := by
  simp only [cycleIndex, map_mul, MvPolynomial.aeval_C, map_sum, aeval_cycleMonomial]

end CycleIndex

section Polya

variable {S C R : Type*} [Fintype S] [Fintype C] [CommSemiring R]
  {G : Type*} [Group G] [Fintype G] [MulAction G S]

/-- The weight of a coloring (product of the weights of the colors used) is constant on orbits. -/
lemma prod_weight_smul (w : C → R) (g : G) (f : S → C) :
    ∏ s, w ((g • f) s) = ∏ s, w (f s) :=
  Equiv.prod_comp (MulAction.toPerm g⁻¹) (fun s => w (f s))

/-- CO-321, in the form with an arbitrary weight `w` on the colors, over a `ℚ`-algebra `R`: the sum,
over the orbits of colorings, of the product of the weights of the colors of a representative equals
the cycle index with `x_k := ∑_c w(c)^k` substituted. -/
theorem polya_weighted [Algebra ℚ R] (w : C → R) :
    ∑ ω : orbitRel.Quotient G (S → C), ∏ s, w (ω.out s)
      = MvPolynomial.aeval (fun k => ∑ c, w c ^ k) (cycleIndex G S) := by
  have hB := sum_fixed_weight_eq (G := G) (X := S → C) (fun f => ∏ s, w (f s))
    (fun g f => prod_weight_smul w g f)
  have hfix : ∀ g : G, ∑ f ∈ univ.filter (fun f : S → C => g • f = f), ∏ s, w (f s)
      = ∏ q : orbitRel.Quotient (Subgroup.zpowers (toPerm g : Equiv.Perm S)) S,
          ∑ c, w c ^ Nat.card q.orbit := by
    intro g
    rw [← sum_fixed_prod_perm]
    refine sum_congr (filter_congr fun f _ => ?_) fun _ _ => rfl
    rw [toPerm_smul_eq]
  have hB' : ∑ g : G, ∏ q : orbitRel.Quotient (Subgroup.zpowers (toPerm g : Equiv.Perm S)) S,
      ∑ c, w c ^ Nat.card q.orbit
      = Fintype.card G • ∑ ω : orbitRel.Quotient G (S → C), ∏ s, w (ω.out s) := by
    rw [← hB]
    exact sum_congr rfl fun g _ => by convert (hfix g).symm
  have hG : (Fintype.card G : ℚ) ≠ 0 := by simp
  rw [aeval_cycleIndex, hB', ← Nat.cast_smul_eq_nsmul ℚ, Algebra.smul_def, ← mul_assoc,
    ← map_mul, one_div, inv_mul_cancel₀ hG, map_one, one_mul]

/-- CO-321. Pólya's enumeration theorem: the generating function of the nonequivalent colorings by
color content (each orbit contributes the monomial `∏_s c_{f s}` of its color content) is the cycle
index with `x_k := ∑_c c^k` substituted. Here the colors `c` are the variables `X c` of a
polynomial ring. -/
@[kb "kellertrotter2017" "Theorem 15.11, p. 326"]
theorem polya_enumeration :
    ∑ ω : orbitRel.Quotient G (S → C), ∏ s, (MvPolynomial.X (ω.out s) : MvPolynomial C ℚ)
      = MvPolynomial.aeval (fun k => ∑ c, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k)
          (cycleIndex G S) :=
  polya_weighted (fun c => (MvPolynomial.X c : MvPolynomial C ℚ))

/-- CO-320. The number of nonequivalent colorings (orbits of `G` on the colorings `S → C`) is the
cycle index with every `x_k := |C|`. -/
@[kb "kellertrotter2017" "text (number of nonequivalent colorings), p. 324"]
theorem card_orbits_colorings :
    (Fintype.card (orbitRel.Quotient G (S → C)) : ℚ)
      = MvPolynomial.aeval (fun _ => (Fintype.card C : ℚ)) (cycleIndex G S) := by
  have := polya_weighted (G := G) (S := S) (C := C) (R := ℚ) (fun _ => 1)
  simpa using this

/-- CO-320, for `m` colors: the number of nonequivalent `m`-colorings is `P_G(m, ..., m)`. -/
@[kb "kellertrotter2017" "text (number of nonequivalent colorings), p. 324"]
theorem card_orbits_colorings_fin (m : ℕ) :
    (Fintype.card (orbitRel.Quotient G (S → Fin m)) : ℚ)
      = MvPolynomial.aeval (fun _ => (m : ℚ)) (cycleIndex G S) := by
  simpa using card_orbits_colorings (G := G) (S := S) (C := Fin m)

end Polya

end UndergradKB.Combinatorics.Polya
