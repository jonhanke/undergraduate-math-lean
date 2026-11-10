import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Nat.Totient
import UndergradKB.Common.Attr
import UndergradKB.Geometry.GaussWantzel
import UndergradKB.Geometry.SetSquare
import UndergradKB.Geometry.RulerCompassConverse

/-! # The Gauss-Wantzel theorem, sufficiency (Petrunin, Theorem 19.6, p. 158)

If `φ(n)` is a power of 2 (equivalently, `n = 2^k p₁ ⋯ p_m` with distinct odd Fermat primes `pᵢ`), then
`cos (2π/n)` is a constructible number, and the regular `n`-gon can be built with ruler and compass.

The route is the Galois-theoretic one (the book, p. 158, only sketches it):

1. `exists_isConstructibleIn_of_two_group`: if `E/ℚ` is finite Galois with Galois group of order `2^m`, then
   every element of `E` is obtained from the integers by `+, -, ·, ⁻¹` and square roots. Proof by induction on
   `m`: a `2`-group has a subgroup `K` of index `2`; an element `x` fixed by `K` is a root of
   `X² - (x + σx) X + x·σx`, whose coefficients are fixed by the whole group.
2. For `φ(n) = 2^m`, `ℚ(ζₙ)/ℚ` is Galois of degree `φ(n)`, so `ζₙ` and `cos (2π/n) = Re ζₙ` are obtained this way.
3. Numbers obtained this way inside `ℂ` have constructible real and imaginary parts (`IsConstructibleIn.re_im`),
   since a complex square root has real and imaginary parts built from real square roots.
4. Arithmetic: `n = 2^k ∏ pᵢ` gives `φ(n) = 2^m`.
-/

namespace UndergradKB.Geometry

open Polynomial IntermediateField Module Real

section Algebra

variable {L L' : Type*} [Field L] [CharZero L] [Field L'] [CharZero L']

theorem IsConstructibleIn.map (φ : L →+* L') {x : L} (hx : IsConstructibleIn x) :
    IsConstructibleIn (φ x) := by
  induction hx with
  | intCast n => simpa using IsConstructibleIn.intCast (L := L') n
  | add _ _ ihx ihy => rw [map_add]; exact ihx.add ihy
  | neg _ ih => rw [map_neg]; exact ih.neg
  | mul _ _ ihx ihy => rw [map_mul]; exact ihx.mul ihy
  | inv _ ih => rw [map_inv₀]; exact ih.inv
  | sqrt _ hy ih => exact ih.sqrt (by rw [← map_pow, hy])

theorem IsConstructibleIn.two {L : Type*} [Field L] [CharZero L] : IsConstructibleIn (2 : L) := by
  simpa using IsConstructibleIn.intCast (L := L) 2

theorem IsConstructibleIn.sub {x y : L} (hx : IsConstructibleIn x) (hy : IsConstructibleIn y) :
    IsConstructibleIn (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

end Algebra

section GroupStep

variable {E : Type*} [Field E] [CharZero E]

/-- The key step: if a group `Γ` acts on `E` and `K` has index `2` in `Γ`, then an element fixed by `K` is
obtained by arithmetic and a square root from elements fixed by all of `Γ`. -/
theorem constructibleIn_of_index_two {Γ : Type*} [Group Γ] (ρ : Γ →* (E ≃+* E)) (K : Subgroup Γ)
    (hK : K.index = 2) (hΓ : ∀ z : E, (∀ g : Γ, ρ g z = z) → IsConstructibleIn z) (x : E)
    (hx : ∀ k ∈ K, ρ k x = x) : IsConstructibleIn x := by
  have hN : K.Normal := Subgroup.normal_of_index_eq_two hK
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hK
  have haK : a ∉ K := by
    intro h
    have := ha 1
    rw [one_mul] at this
    have h1 := K.one_mem
    unfold Xor at this
    tauto
  have haaK : a * a ∈ K := by
    have := ha a
    unfold Xor at this
    tauto
  have hdich : ∀ g, g ∈ K ∨ g * a ∈ K := by
    intro g
    have := ha g
    unfold Xor at this
    tauto
  set y : E := ρ a x with hy
  have hmul : ∀ g h : Γ, ∀ z : E, ρ (g * h) z = ρ g (ρ h z) := fun g h z => by
    rw [map_mul]; rfl
  have hay : ∀ k ∈ K, ρ k y = y := by
    intro k hk
    have hc : a⁻¹ * k * a ∈ K := by
      have := hN.conj_mem k hk a⁻¹
      simpa using this
    have : k * a = a * (a⁻¹ * k * a) := by group
    rw [hy, ← hmul, this, hmul, hx _ hc]
  have hb : ρ a y = x := by
    rw [hy, ← hmul, hx _ haaK]
  have hcase : ∀ g : Γ, (ρ g x = x ∧ ρ g y = y) ∨ (ρ g x = y ∧ ρ g y = x) := by
    intro g
    rcases hdich g with hg | hg
    · exact Or.inl ⟨hx g hg, hay g hg⟩
    · right
      refine ⟨?_, ?_⟩
      · calc ρ g x = ρ g (ρ a y) := by rw [hb]
          _ = ρ (g * a) y := (hmul g a y).symm
          _ = y := hay _ hg
      · rw [hy, ← hmul, hx _ hg]
  have hs : IsConstructibleIn (x + y) := by
    apply hΓ
    intro g
    rcases hcase g with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [map_add, h1, h2]
    · rw [map_add, h1, h2, add_comm]
  have hp : IsConstructibleIn (x * y) := by
    apply hΓ
    intro g
    rcases hcase g with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [map_mul, h1, h2]
    · rw [map_mul, h1, h2, mul_comm]
  have hd : IsConstructibleIn ((x + y) ^ 2 - 4 * (x * y)) :=
    ((hs.mul hs).sub ((IsConstructibleIn.two.mul IsConstructibleIn.two).mul hp))
      |> fun h => by convert h using 1; ring
  have hw : IsConstructibleIn (x - y) := hd.sqrt (by ring)
  have : x = ((x - y) + (x + y)) * (2 : E)⁻¹ := by
    have : (2 : E) ≠ 0 := two_ne_zero
    field_simp
    ring
  rw [this]
  exact (hw.add hs).mul IsConstructibleIn.two.inv

universe u

/-- If a finite `2`-group `Γ` of order `2^m` acts on `E` and the elements fixed by all of `Γ` are obtained by
arithmetic and square roots, then so is every element of `E`. -/
theorem constructibleIn_of_two_group (m : ℕ) :
    ∀ {Γ : Type u} [Group Γ] (ρ : Γ →* (E ≃+* E)), Nat.card Γ = 2 ^ m →
      (∀ z : E, (∀ g : Γ, ρ g z = z) → IsConstructibleIn z) → ∀ z : E, IsConstructibleIn z := by
  induction m with
  | zero =>
    intro Γ _ ρ hc hΓ z
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp (by simpa using hc)
    apply hΓ
    intro g
    rw [Subsingleton.elim g 1, map_one]; rfl
  | succ m ih =>
    intro Γ _ ρ hc hΓ z
    have : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := m)
      (by rw [hc]; exact pow_dvd_pow 2 (Nat.le_succ m))
    have hidx : K.index = 2 := by
      have := K.card_mul_index
      rw [hK, hc, pow_succ] at this
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    refine ih (ρ.comp K.subtype) hK (fun w hw => ?_) z
    exact constructibleIn_of_index_two ρ K hidx hΓ w (fun k hk => hw ⟨k, hk⟩)

theorem isConstructibleIn_ratCast (q : ℚ) : IsConstructibleIn (q : E) := by
  rw [Rat.cast_def, div_eq_mul_inv]
  have h1 : IsConstructibleIn ((q.num : ℤ) : E) := IsConstructibleIn.intCast q.num
  have h2 : IsConstructibleIn (((q.den : ℤ) : E)⁻¹) := (IsConstructibleIn.intCast (q.den : ℤ)).inv
  have e : ((q.den : ℤ) : E) = (q.den : E) := by simp
  rw [e] at h2
  exact h1.mul h2

/-- **Every element of a finite Galois extension `E/ℚ` of `2`-power degree is obtained from the integers by
arithmetic and square roots.** -/
theorem isConstructibleIn_of_galois_two_pow [FiniteDimensional ℚ E] [IsGalois ℚ E] {m : ℕ}
    (h : Module.finrank ℚ E = 2 ^ m) (z : E) : IsConstructibleIn z := by
  have hcard : Nat.card (E ≃ₐ[ℚ] E) = 2 ^ m := by rw [IsGalois.card_aut_eq_finrank, h]
  refine constructibleIn_of_two_group m
    ({ toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl } :
      (E ≃ₐ[ℚ] E) →* (E ≃+* E)) hcard ?_ z
  intro w hw
  have : w ∈ (⊥ : IntermediateField ℚ E) := (IsGalois.mem_bot_iff_fixed w).mpr hw
  obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp this
  simpa using isConstructibleIn_ratCast (E := E) q

end GroupStep

section Cyclotomic

theorem IsConstructible.of_sq {u : ℝ} (h : IsConstructible (u ^ 2)) : IsConstructible u := by
  have h1 := h.sqrt
  rw [Real.sqrt_sq_eq_abs] at h1
  rcases abs_choice u with h2 | h2
  · rwa [h2] at h1
  · rw [h2] at h1; simpa using h1.neg

theorem IsConstructible.two : IsConstructible (2 : ℝ) := by
  simpa using IsConstructible.intCast 2

/-- A complex number obtained from the integers by arithmetic and (complex) square roots has constructible
real and imaginary parts. -/
theorem IsConstructibleIn.re_im {z : ℂ} (hz : IsConstructibleIn z) :
    IsConstructible z.re ∧ IsConstructible z.im := by
  induction hz with
  | intCast n =>
    refine ⟨by simpa using IsConstructible.intCast n, by simpa using IsConstructible.intCast 0⟩
  | add _ _ ihx ihy => exact ⟨by simpa using ihx.1.add ihy.1, by simpa using ihx.2.add ihy.2⟩
  | neg _ ih => exact ⟨by simpa using ih.1.neg, by simpa using ih.2.neg⟩
  | mul _ _ ihx ihy =>
    refine ⟨?_, ?_⟩
    · rw [Complex.mul_re]; exact (ihx.1.mul ihy.1).sub (ihx.2.mul ihy.2)
    · rw [Complex.mul_im]; exact (ihx.1.mul ihy.2).add (ihx.2.mul ihy.1)
  | @inv z _ ih =>
    have hn : IsConstructible (Complex.normSq z) := by
      rw [Complex.normSq_apply]; exact (ih.1.mul ih.1).add (ih.2.mul ih.2)
    refine ⟨?_, ?_⟩
    · rw [Complex.inv_re]; exact ih.1.div hn
    · rw [Complex.inv_im]; exact ih.2.neg.div hn
  | @sqrt x y _ hy ih =>
    have e1 : y.re * y.re - y.im * y.im = x.re := by
      have := congrArg Complex.re hy
      rw [pow_two, Complex.mul_re] at this; exact this
    have e2 : y.re * y.im + y.im * y.re = x.im := by
      have := congrArg Complex.im hy
      rw [pow_two, Complex.mul_im] at this; exact this
    have hr : IsConstructible (Real.sqrt (x.re * x.re + x.im * x.im)) :=
      ((ih.1.mul ih.1).add (ih.2.mul ih.2)).sqrt
    have hsq : (y.re ^ 2 + y.im ^ 2) ^ 2 = x.re * x.re + x.im * x.im := by
      rw [← e1, ← e2]; ring
    have hrr : Real.sqrt (x.re * x.re + x.im * x.im) = y.re ^ 2 + y.im ^ 2 := by
      rw [← hsq]; exact Real.sqrt_sq (by positivity)
    rw [hrr] at hr
    have hu : y.re ^ 2 = (x.re + (y.re ^ 2 + y.im ^ 2)) / 2 := by nlinarith
    have hv : y.im ^ 2 = ((y.re ^ 2 + y.im ^ 2) - x.re) / 2 := by nlinarith
    refine ⟨IsConstructible.of_sq ?_, IsConstructible.of_sq ?_⟩
    · rw [hu]; exact (ih.1.add hr).div IsConstructible.two
    · rw [hv]; exact (hr.sub ih.1).div IsConstructible.two

/-- `exp (2πi/n)` is obtained from the integers by arithmetic and square roots whenever `φ(n)` is a power
of 2: `ℚ(ζₙ)/ℚ` is Galois of degree `φ(n)`. -/
theorem isConstructibleIn_exp {n : ℕ} (hn : 0 < n) (h : ∃ m : ℕ, Nat.totient n = 2 ^ m) :
    IsConstructibleIn (Complex.exp (2 * π * Complex.I / n)) := by
  obtain ⟨m, hm⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  set ζ : ℂ := Complex.exp (2 * π * Complex.I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hcyc : IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}) := by
    change IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsIntegral.tower_top (A := ℚ) (hζ.isIntegral hn)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hGal : IsGalois ℚ (IntermediateField.adjoin ℚ {ζ}) := IsCyclotomicExtension.isGalois {n} ℚ _
  have hrank : Module.finrank ℚ (IntermediateField.adjoin ℚ {ζ}) = 2 ^ m := by
    rw [IsCyclotomicExtension.finrank _ (Polynomial.cyclotomic.irreducible_rat hn), hm]
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {n} ℚ _
  have := isConstructibleIn_of_galois_two_pow hrank (IntermediateField.AdjoinSimple.gen ℚ ζ)
  have h2 := this.map (IntermediateField.adjoin ℚ {ζ}).val.toRingHom
  simpa using h2

/-- If `φ(n)` is a power of 2, then `cos (2π/n)` is a constructible number. -/
theorem isConstructible_cos_of_totient {n : ℕ} (hn : 0 < n) (h : ∃ m : ℕ, Nat.totient n = 2 ^ m) :
    IsConstructible (Real.cos (2 * π / n)) := by
  have hz := (isConstructibleIn_exp hn h).re_im.1
  have e : Complex.exp (2 * π * Complex.I / n) = Complex.exp (((2 * π / n : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [e, Complex.exp_ofReal_mul_I_re] at hz
  exact hz

/-- The sine of `2π/n` is constructible as well. -/
theorem isConstructible_sin_of_totient {n : ℕ} (hn : 0 < n) (h : ∃ m : ℕ, Nat.totient n = 2 ^ m) :
    IsConstructible (Real.sin (2 * π / n)) := by
  have hc := isConstructible_cos_of_totient hn h
  refine IsConstructible.of_sq ?_
  have : Real.sin (2 * π / n) ^ 2 = 1 - Real.cos (2 * π / n) * Real.cos (2 * π / n) := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * π / n)]
  rw [this]
  exact (by simpa using IsConstructible.intCast 1 : IsConstructible (1 : ℝ)).sub (hc.mul hc)

end Cyclotomic

section Arithmetic

theorem totient_prod_fermat (S : Finset ℕ) (hS : ∀ p ∈ S, IsFermatPrime p ∧ p ≠ 2) :
    (∃ m : ℕ, Nat.totient (∏ p ∈ S, p) = 2 ^ m) ∧ ¬ 2 ∣ ∏ p ∈ S, p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⟨0, by simp⟩, by simp⟩
  | @insert q S hq ih =>
    obtain ⟨⟨m, hm⟩, h2⟩ := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    obtain ⟨⟨hqp, j, hj⟩, hq2⟩ := hS q (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hq]
    have hcop : Nat.Coprime q (∏ p ∈ S, p) := by
      rw [Nat.Prime.coprime_iff_not_dvd hqp]
      intro hd
      obtain ⟨p, hp, hqd⟩ := hqp.prime.exists_mem_finset_dvd (f := fun p => p) hd
      have := (Nat.prime_dvd_prime_iff_eq hqp (hS p (Finset.mem_insert_of_mem hp)).1.1).mp hqd
      exact hq (this ▸ hp)
    refine ⟨⟨j + m, ?_⟩, ?_⟩
    · rw [Nat.totient_mul hcop, Nat.totient_prime hqp, hm, hj, pow_add]; simp
    · intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp h).symm
      · exact h2 h

/-- If `n = 2^k p₁ ⋯ p_m` with distinct odd Fermat primes, then `φ(n)` is a power of 2. -/
theorem totient_eq_two_pow_of_fermat_form (k : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, IsFermatPrime p ∧ p ≠ 2) :
    ∃ m : ℕ, Nat.totient (2 ^ k * ∏ p ∈ S, p) = 2 ^ m := by
  obtain ⟨⟨m, hm⟩, h2⟩ := totient_prod_fermat S hS
  have hcop : Nat.Coprime (2 ^ k) (∏ p ∈ S, p) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
  rw [Nat.totient_mul hcop, hm]
  rcases k with _ | k
  · exact ⟨m, by simp⟩
  · exact ⟨k + m, by rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k), pow_add]; simp⟩

end Arithmetic

section Main

/-- **Gauss-Wantzel theorem, sufficiency** (Petrunin, Theorem 19.6, p. 158), algebraic form: if
`n = 2^k p₁ ⋯ p_m` with distinct odd Fermat primes `pᵢ`, then `cos (2π/n)` is a constructible number
(so, by Theorem 19.8, the vertex `(cos (2π/n), sin (2π/n))` of the regular `n`-gon is obtained from `(0,0)` and
`(1,0)` by ruler and compass; see `rcConstructible_ngon_vertex`). -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem gauss_wantzel_sufficiency {n k : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, IsFermatPrime p ∧ p ≠ 2)
    (hn : n = 2 ^ k * ∏ p ∈ S, p) : IsConstructible (Real.cos (2 * π / n)) := by
  have hpos : 0 < n := by
    rw [hn]
    refine Nat.mul_pos (by positivity) (Finset.prod_pos fun p hp => (hS p hp).1.1.pos)
  exact isConstructible_cos_of_totient hpos (hn ▸ totient_eq_two_pow_of_fermat_form k S hS)

/-- **Gauss-Wantzel theorem, algebraic characterization**: for `n ≥ 1`, `cos (2π/n)` is constructible iff
`φ(n)` is a power of 2 (iff `n` is a power of 2 times distinct odd Fermat primes). -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem isConstructible_cos_iff_totient {n : ℕ} (hn : 0 < n) :
    IsConstructible (Real.cos (2 * π / n)) ↔ ∃ m : ℕ, Nat.totient n = 2 ^ m :=
  ⟨fun h => h.totient_eq_two_pow hn, isConstructible_cos_of_totient hn⟩

/-- **Gauss-Wantzel theorem, sufficiency, geometric form**: if `φ(n)` is a power of 2 (in particular if
`n = 2^k p₁ ⋯ p_m` with distinct odd Fermat primes), the vertex `(cos (2π/n), sin (2π/n))` of the regular
`n`-gon with centre `(0,0)` and first vertex `(1,0)` is obtained from `(0,0)` and `(1,0)` by a ruler-and-compass
construction. -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem rcConstructible_ngon_vertex {n : ℕ} (hn : 0 < n) (h : ∃ m : ℕ, Nat.totient n = 2 ^ m) :
    RCConstructible {(0, 0), (1, 0)} (.point (Real.cos (2 * π / n), Real.sin (2 * π / n))) :=
  rcConstructible_of_isConstructible (isConstructible_cos_of_totient hn h)
    (isConstructible_sin_of_totient hn h)

/-- **Gauss-Wantzel theorem** (Petrunin, Theorem 19.6, p. 158): for `n ≥ 1`, the vertex of the regular `n`-gon
is constructible with ruler and compass iff `φ(n)` is a power of 2, i.e. iff `n` is a power of 2 times distinct
odd Fermat primes. -/
@[kb "petrunin2025" "Theorem 19.6, p. 158"]
theorem rcConstructible_ngon_vertex_iff {n : ℕ} (hn : 0 < n) :
    RCConstructible {(0, 0), (1, 0)} (.point (Real.cos (2 * π / n), Real.sin (2 * π / n))) ↔
      ∃ m : ℕ, Nat.totient n = 2 ^ m :=
  ⟨fun h => (isConstructible_cos_iff_totient hn).mp (rcConstructible_iff.mp h).1,
    rcConstructible_ngon_vertex hn⟩

end Main

end UndergradKB.Geometry
