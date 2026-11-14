import UndergradKB.Foundations.DPRM.Davis

/-!
# Foundations, DPRM: Davis's bounded universal quantifier theorem

`dioph_forall_lt`: if `S ⊆ ℕ^(1 + α)` is Diophantine and `y` is a Diophantine function, then
`{v | ∀ k < y v, (k, v) ∈ S}` is Diophantine (Davis 1953; M. Davis, *Hilbert's tenth problem is
unsolvable*, Amer. Math. Monthly 80 (1973), Theorem 5.1). The two directions of the coding are
`davis_sound` and `davis_complete`, stated for an abstract polynomial `P k x` that respects
congruences.
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Nat Finset

local infixr:67 " ::ₒ " => Option.elim'
local infixr:65 " ⊗ " => Sum.elim

/-- The congruence property of a polynomial in the variables `k, x`. -/
def RespectsModEq {β : Type} (P : ℕ → (β → ℕ) → ℤ) : Prop :=
  ∀ (n : ℤ) (k k' : ℕ) (x x' : β → ℕ), (k : ℤ) ≡ k' [ZMOD n] →
    (∀ b, (x b : ℤ) ≡ x' b [ZMOD n]) → P k x ≡ P k' x' [ZMOD n]

/-- Soundness of Davis's coding: the coded data yield, for each `k < y`, a solution of `P k x = 0`. -/
theorem davis_sound {β : Type} (P : ℕ → (β → ℕ) → ℤ) (hP : RespectsModEq P)
    {y u Q e : ℕ} {a : β → ℕ}
    (hQ : ∀ k x, k ≤ u → (∀ b, x b ≤ u) → |P k x| < Q)
    (h2 : ∀ b, u < a b)
    (h3 : 1 + (e + 1) * Q ! = ∏ k ∈ range y, (1 + (k + 1) * Q !))
    (h4 : ∀ b, 1 + (e + 1) * Q ! ∣ (a b).descFactorial (u + 1))
    (h5 : ((1 + (e + 1) * Q ! : ℕ) : ℤ) ∣ P e a) :
    ∀ k < y, k ≤ u → ∃ x, P k x = 0 := by
  intro k hk hku
  have ht : 0 < Q ! := Nat.factorial_pos Q
  have hm1 : 1 + (k + 1) * Q ! ≠ 1 := by
    have : 0 < (k + 1) * Q ! := Nat.mul_pos (Nat.succ_pos k) ht
    omega
  have hp : (1 + (k + 1) * Q !).minFac.Prime := Nat.minFac_prime hm1
  have hpm : (1 + (k + 1) * Q !).minFac ∣ 1 + (k + 1) * Q ! := Nat.minFac_dvd _
  set p := (1 + (k + 1) * Q !).minFac with hpdef
  have hpM : p ∣ 1 + (e + 1) * Q ! := by
    rw [h3]
    exact hpm.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk))
  have hQp : Q < p := lt_of_prime_dvd_one_add (dvd_refl _) hp hpm
  have hcop : Nat.Coprime p (Q !) :=
    Nat.Coprime.coprime_dvd_left hpm (coprime_one_add_mul_self (k + 1) (Q !))
  have he : (e : ℤ) ≡ k [ZMOD p] := intModEq_of_dvd_one_add hcop hpM hpm
  have hx : ∀ b, ∃ j < u + 1, j ≤ a b ∧ p ∣ a b - j := fun b =>
    exists_of_prime_dvd_descFactorial hp (u + 1) (h2 b) (hpM.trans (h4 b))
  choose x hxu hxa hxd using hx
  have hxmod : ∀ b, (a b : ℤ) ≡ x b [ZMOD p] := by
    intro b
    refine (Int.modEq_iff_dvd.2 ?_).symm
    have := Int.natCast_dvd_natCast.2 (hxd b)
    rwa [Nat.cast_sub (hxa b)] at this
  have hcong : P e a ≡ P k x [ZMOD p] := hP p e k a x he hxmod
  have hdiv : (p : ℤ) ∣ P e a := (Int.natCast_dvd_natCast.2 hpM).trans h5
  have hdiv' : (p : ℤ) ∣ P k x :=
    Int.modEq_zero_iff_dvd.1 (hcong.symm.trans (Int.modEq_zero_iff_dvd.2 hdiv))
  have hbound : |P k x| < p := by
    have := hQ k x hku fun b => Nat.lt_succ_iff.1 (hxu b)
    have hQp' : (Q : ℤ) < p := by exact_mod_cast hQp
    linarith
  exact ⟨x, Int.eq_zero_of_abs_lt_dvd hdiv' hbound⟩

/-- Completeness of Davis's coding: solutions for every `k < y`, bounded by `u`, can be coded. -/
theorem davis_complete {β : Type} (P : ℕ → (β → ℕ) → ℤ) (hP : RespectsModEq P)
    {y u Q : ℕ} (wt : ℕ → β → ℕ) (hwt : ∀ k < y, P k (wt k) = 0)
    (hwu : ∀ k < y, ∀ b, wt k b ≤ u) (hyu : y ≤ u) (huQ : u < Q) (hy : 0 < y) :
    ∃ (e : ℕ) (a : β → ℕ), (∀ b, u < a b) ∧
      1 + (e + 1) * Q ! = ∏ k ∈ range y, (1 + (k + 1) * Q !) ∧
      (∀ b, 1 + (e + 1) * Q ! ∣ (a b).descFactorial (u + 1)) ∧
      ((1 + (e + 1) * Q ! : ℕ) : ℤ) ∣ P e a := by
  set t := Q ! with htdef
  set m : ℕ → ℕ := fun k => 1 + (k + 1) * t with hmdef
  have hco : ((range y : Finset ℕ) : Set ℕ).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact coprime_one_add_mul (dvd_refl _) h (by omega)
    · exact (coprime_one_add_mul (dvd_refl _) h (by omega)).symm
  have hm0 : ∀ k ∈ range y, m k ≠ 0 := fun k _ => by simp [hmdef]
  obtain ⟨c, hc, hprod⟩ := prod_one_add_eq t y
  set Pi := ∏ k ∈ range y, m k with hPi
  have hPipos : 0 < Pi := Finset.prod_pos fun k _ => by simp [hmdef]
  let r : β → ℕ := fun b =>
    (Nat.chineseRemainderOfFinset (fun k => wt k b) m (range y) hm0 hco : ℕ)
  have hr : ∀ b, ∀ k < y, r b ≡ wt k b [MOD m k] := fun b k hk =>
    (Nat.chineseRemainderOfFinset (fun k => wt k b) m (range y) hm0 hco).2 k
      (Finset.mem_range.2 hk)
  let a : β → ℕ := fun b => r b + Pi * (u + 1)
  have hmPi : ∀ k < y, m k ∣ Pi := fun k hk => Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  have ha : ∀ b, ∀ k < y, a b ≡ wt k b [MOD m k] := by
    intro b k hk
    obtain ⟨d, hd⟩ := hmPi k hk
    have : a b = r b + m k * (d * (u + 1)) := by simp only [a, hd]; ring
    rw [this]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 (by simp)).symm.trans (hr b k hk)
  have hau : ∀ b, u < a b := fun b => by
    have : u + 1 ≤ Pi * (u + 1) := Nat.le_mul_of_pos_left _ hPipos
    simp only [a]
    omega
  have hc1 : c - 1 + 1 = c := by omega
  refine ⟨c - 1, a, hau, ?_, ?_, ?_⟩
  · rw [hc1, hprod]
  · intro b
    rw [hc1, ← hprod]
    refine Int.natCast_dvd_natCast.1 (prod_dvd_of_coprime_nat hco fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    have hle : wt k b ≤ a b := (hwu k hk' b).trans (hau b).le
    refine Int.natCast_dvd_natCast.2 (((Nat.modEq_iff_dvd' hle).1 (ha b k hk').symm).trans ?_)
    exact sub_dvd_descFactorial (a b) (Nat.lt_succ_of_le (hwu k hk' b))
  · rw [hc1, ← hprod]
    refine prod_dvd_of_coprime_nat hco fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hMk : m k ∣ 1 + (c - 1 + 1) * t := by
      rw [hc1, ← hprod]
      exact hmPi k hk'
    have he : ((c - 1 : ℕ) : ℤ) ≡ k [ZMOD m k] :=
      intModEq_of_dvd_one_add (coprime_one_add_mul_self (k + 1) t) hMk (dvd_refl _)
    have hab : ∀ b, (a b : ℤ) ≡ wt k b [ZMOD m k] := fun b =>
      Int.natCast_modEq_iff.2 (ha b k hk')
    have := hP (m k) (c - 1) k a (wt k) he hab
    rw [hwt k hk'] at this
    exact Int.modEq_zero_iff_dvd.1 this

theorem respectsModEq_poly {α β : Type} (p : Poly (Option α ⊕ β)) (v : α → ℕ) :
    RespectsModEq fun k x => p ((k ::ₒ v) ⊗ x) := by
  intro n k k' x x' hk hx
  refine poly_modEq p n _ _ fun i => ?_
  rcases i with (_ | i) | b
  · exact hk
  · exact Int.ModEq.refl _
  · exact hx b

/-- **Davis's bounded universal quantifier theorem**: if `S ⊆ ℕ^(1 + α)` is Diophantine and `y` is a
Diophantine function, then `{v | ∀ k < y v, (k, v) ∈ S}` is Diophantine. -/
theorem dioph_forall_lt {α : Type} {S : Set (Option α → ℕ)} (d : Dioph S)
    {y : (α → ℕ) → ℕ} (dy : DiophFn y) :
    Dioph {v | ∀ k < y v, k ::ₒ v ∈ S} := by
  classical
  obtain ⟨β, _, p, hp⟩ := dioph_fintype_witness d
  obtain ⟨M, hM⟩ := poly_majorant p
    (Sum.elim (fun o => o.elim (Poly.proj none) fun i => Poly.proj (some i)) fun _ => Poly.proj none)
  let ρ : Option α → α ⊕ Option (Option β) := fun o => o.elim (Sum.inr none) Sum.inl
  let σ : Option α ⊕ β → α ⊕ Option (Option β) :=
    Sum.elim (fun o => o.elim (Sum.inr (some none)) Sum.inl) fun b => Sum.inr (some (some b))
  let U : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => z (Sum.inr none)
  let E : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => z (Sum.inr (some none))
  let A : β → (α ⊕ Option (Option β) → ℕ) → ℕ := fun b z => z (Sum.inr (some (some b)))
  let Y : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => y (z ∘ Sum.inl)
  let Qf : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => (M.map ρ z).natAbs + U z + 1
  let T : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => Nat.factorial (Qf z)
  let Pr : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => ∏ k ∈ range (Y z), (1 + (k + 1) * T z)
  let Md : (α ⊕ Option (Option β) → ℕ) → ℕ := fun z => 1 + (E z + 1) * T z
  let D : Set (α ⊕ Option (Option β) → ℕ) := {z | Y z ≤ U z ∧ (∀ b, U z < A b z) ∧ Md z = Pr z ∧
    (∀ b, Md z ∣ (A b z).descFactorial (U z + 1)) ∧ Md z ∣ (p.map σ z).natAbs}
  have dY : DiophFn Y := reindex_diophFn Sum.inl dy
  have dU : DiophFn U := proj_dioph _
  have dE : DiophFn E := proj_dioph _
  have dA : ∀ b, DiophFn (A b) := fun b => proj_dioph _
  have dQ : DiophFn Qf := add_dioph (add_dioph (abs_poly_dioph (M.map ρ)) dU) (const_dioph 1)
  have dT : DiophFn T := factorial_dioph dQ
  have dPr : DiophFn Pr := prod_succ_mul_dioph dY dT fun z => Nat.factorial_pos _
  have dMd : DiophFn Md := add_dioph (const_dioph 1) (mul_dioph (add_dioph dE (const_dioph 1)) dT)
  have dD : Dioph D := by
    have h1 := le_dioph dY dU
    have h2 := dioph_forall_fintype fun b => lt_dioph dU (dA b)
    have h3 := eq_dioph dMd dPr
    have h4 := dioph_forall_fintype fun b =>
      dvd_dioph dMd (descFactorial_dioph (dA b) (add_dioph dU (const_dioph 1)))
    have h5 := dvd_dioph dMd (abs_poly_dioph (p.map σ))
    exact (h1.inter (h2.inter (h3.inter (h4.inter h5)))).ext fun z => Iff.rfl
  have dZ : Dioph {v : α → ℕ | y v = 0} := eq_dioph dy (const_dioph 0)
  refine (dZ.union (ex_dioph dD)).ext fun v => ?_
  -- evaluation of the coding functions at `v ⊗ w`
  have hρ : ∀ w : Option (Option β) → ℕ, (v ⊗ w) ∘ ρ = w none ::ₒ v := by
    intro w
    funext o
    rcases o with _ | i <;> rfl
  have eQ : ∀ w, Qf (v ⊗ w) = (M (w none ::ₒ v)).natAbs + w none + 1 := by
    intro w
    simp only [Qf, U, Poly.map_apply, hρ, Sum.elim_inr]
  have eP : ∀ w, p.map σ (v ⊗ w) = p ((w (some none) ::ₒ v) ⊗ fun b => w (some (some b))) := by
    intro w
    rw [Poly.map_apply]
    congr 1
    funext i
    rcases i with (_ | i) | b <;> rfl
  have hPm := respectsModEq_poly p v
  -- the bound on the polynomial
  have hQ : ∀ u k (x : β → ℕ), k ≤ u → (∀ b, x b ≤ u) →
      |p ((k ::ₒ v) ⊗ x)| < ((M (u ::ₒ v)).natAbs + u + 1 : ℕ) := by
    intro u k x hku hxu
    have h := hM ((k ::ₒ v) ⊗ x) (u ::ₒ v) fun i => by
      rcases i with (_ | i) | b
      · simpa using hku
      · simp
      · simpa using hxu b
    have : M (u ::ₒ v) ≤ |M (u ::ₒ v)| := le_abs_self _
    push_cast
    linarith
  constructor
  · rintro (h0 | ⟨w, hY, hA, hMP, hdesc, hdvd⟩)
    · intro k hk
      have h0' : y v = 0 := h0
      omega
    · intro k hk
      rw [hp]
      have hY' : y v ≤ w none := hY
      have hMP' : 1 + (w (some none) + 1) * ((M (w none ::ₒ v)).natAbs + w none + 1) ! =
          ∏ k ∈ range (y v), (1 + (k + 1) * ((M (w none ::ₒ v)).natAbs + w none + 1) !) := by
        simpa only [Md, Pr, T, E, Y, eQ, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using hMP
      have hdesc' : ∀ b, 1 + (w (some none) + 1) * ((M (w none ::ₒ v)).natAbs + w none + 1) ! ∣
          (w (some (some b))).descFactorial (w none + 1) := by
        simpa only [Md, T, E, U, A, eQ, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using hdesc
      have hdvd' : 1 + (w (some none) + 1) * ((M (w none ::ₒ v)).natAbs + w none + 1) ! ∣
          (p ((w (some none) ::ₒ v) ⊗ fun b => w (some (some b)))).natAbs := by
        simpa only [Md, T, E, eQ, eP, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using hdvd
      exact davis_sound _ hPm (hQ (w none)) hA hMP' hdesc' (Int.natCast_dvd.2 hdvd') k hk
        (by omega)
  · intro h
    by_cases h0 : y v = 0
    · exact Or.inl h0
    right
    have hw : ∀ k < y v, ∃ x : β → ℕ, p ((k ::ₒ v) ⊗ x) = 0 := fun k hk => (hp _).1 (h k hk)
    choose! wt hwt using hw
    set u := y v + ∑ k ∈ range (y v), ∑ b, wt k b with hu
    have hwu : ∀ k < y v, ∀ b, wt k b ≤ u := by
      intro k hk b
      have h1 : wt k b ≤ ∑ b, wt k b :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
      have h2 : ∑ b, wt k b ≤ ∑ k ∈ range (y v), ∑ b, wt k b :=
        Finset.single_le_sum (f := fun k => ∑ b, wt k b) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hk)
      omega
    obtain ⟨e, a, hau, hprod, hdesc, hdvd⟩ := davis_complete (fun k x => p ((k ::ₒ v) ⊗ x)) hPm
      (Q := (M (u ::ₒ v)).natAbs + u + 1) wt hwt hwu (by omega) (by omega) (by omega)
    refine ⟨fun o => o.elim u fun o' => o'.elim e a, ?_, ?_, ?_, ?_, ?_⟩
    · show y v ≤ u
      omega
    · exact hau
    · simpa only [Md, Pr, T, E, Y, eQ, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using hprod
    · simpa only [Md, T, E, U, A, eQ, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using hdesc
    · simpa only [Md, T, E, eQ, eP, Sum.elim_inr, Sum.elim_comp_inl, Option.elim_none, Option.elim_some] using Int.natCast_dvd.1 hdvd

end UndergradKB.Foundations.DPRM
