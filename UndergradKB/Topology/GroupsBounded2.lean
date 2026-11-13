import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import UndergradKB.Topology.GroupsBounded
import UndergradKB.Common.Attr

/-!
# Abelian groups of bounded exponent are direct sums of cyclic groups

Morris, *Topology Without Tears* (2024), Theorem A5.11.11 (`morris2024`), after Prüfer and Baer.  From the
`p`-group step of `GroupsBounded`: induction on the exponent `p^k`, the splitting of a group of exponent `n`
into its `p`-primary part and the rest, and the conversion of an independent generating family of cyclic
subgroups into an isomorphism with `⨁ ZMod (n i)`.
-/

universe u

open Function

namespace UndergradKB.Topology

/-- The `m`-torsion of the subgroup `S`. -/
def _root_.AddSubgroup.nTors {G : Type*} [AddCommGroup G] (S : AddSubgroup G) (m : ℕ) : AddSubgroup G where
  carrier := {g | g ∈ S ∧ m • g = 0}
  zero_mem' := ⟨S.zero_mem, smul_zero _⟩
  add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, by rw [smul_add, ha.2, hb.2, add_zero]⟩
  neg_mem' := fun ha => ⟨S.neg_mem ha.1, by rw [smul_neg, ha.2, neg_zero]⟩

section Induction

variable (p : ℕ) [hp : Fact p.Prime]

theorem pgroup_cycBasis {G : Type u} [AddCommGroup G] :
    ∀ (k : ℕ) (S : AddSubgroup G), (∀ s ∈ S, p ^ k • s = 0) →
      ∃ (ι : Type u) (y : ι → G), IsCycBasisOn S y := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨PEmpty, PEmpty.elim, fun i => i.elim, ?_, fun t c _ i _ => i.elim⟩
    intro s hs
    have : s = 0 := by simpa using hS s hs
    rw [this]
    exact AddSubgroup.zero_mem _
  | succ k ih =>
    intro S hS
    let T : AddSubgroup G :=
      { carrier := {t | ∃ s ∈ S, t = p • s}
        zero_mem' := ⟨0, S.zero_mem, (smul_zero _).symm⟩
        add_mem' := fun {a b} ha hb => by
          obtain ⟨a', ha', rfl⟩ := ha
          obtain ⟨b', hb', rfl⟩ := hb
          exact ⟨a' + b', S.add_mem ha' hb', (smul_add _ _ _).symm⟩
        neg_mem' := fun {a} ha => by
          obtain ⟨a', ha', rfl⟩ := ha
          exact ⟨-a', S.neg_mem ha', (smul_neg _ _).symm⟩ }
    obtain ⟨ι, y, hy⟩ := ih T (by
      rintro _ ⟨s, hs, rfl⟩
      rw [← mul_nsmul', ← pow_succ]
      exact hS s hs)
    exact cycBasis_step p k S T (fun s hs => ⟨s, hs, rfl⟩) (fun t ht => ht) hS hy

end Induction

/-- Two independent bases of disjoint subgroups combine. -/
theorem IsCycBasisOn.sup {G : Type u} [AddCommGroup G] {S₁ S₂ : AddSubgroup G} {ι₁ ι₂ : Type u}
    {y₁ : ι₁ → G} {y₂ : ι₂ → G} (h₁ : IsCycBasisOn S₁ y₁) (h₂ : IsCycBasisOn S₂ y₂)
    (hd : S₁ ⊓ S₂ = ⊥) : IsCycBasisOn (S₁ ⊔ S₂) (Sum.elim y₁ y₂) := by
  classical
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · rintro (i | j)
    · exact ⟨AddSubgroup.mem_sup_left (a1 i).1, (a1 i).2⟩
    · exact ⟨AddSubgroup.mem_sup_right (b1 j).1, (b1 j).2⟩
  · refine sup_le (a2.trans (AddSubgroup.closure_mono ?_)) (b2.trans (AddSubgroup.closure_mono ?_))
    · rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩
  · intro F c hF
    rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at hF
    simp only [Sum.elim_inl, Sum.elim_inr] at hF
    have hW : ∑ i ∈ F.toLeft, c (Sum.inl i) • y₁ i ∈ S₁ :=
      S₁.sum_mem fun i _ => S₁.zsmul_mem (a1 i).1 _
    have hV : ∑ j ∈ F.toRight, c (Sum.inr j) • y₂ j ∈ S₂ :=
      S₂.sum_mem fun j _ => S₂.zsmul_mem (b1 j).1 _
    have hmem : ∑ i ∈ F.toLeft, c (Sum.inl i) • y₁ i ∈ S₁ ⊓ S₂ :=
      ⟨hW, by rw [eq_neg_of_add_eq_zero_left hF]; exact S₂.neg_mem hV⟩
    rw [hd, AddSubgroup.mem_bot] at hmem
    have hmem' : ∑ j ∈ F.toRight, c (Sum.inr j) • y₂ j = 0 := by
      rw [hmem, zero_add] at hF; exact hF
    have e1 := a3 _ _ hmem
    have e2 := b3 _ _ hmem'
    rintro (i | j) hu
    · exact e1 i (Finset.mem_toLeft.mpr hu)
    · exact e2 j (Finset.mem_toRight.mpr hu)

/-- A group of exponent dividing `n > 0` has an independent generating family of cyclic subgroups. -/
theorem bounded_cycBasis {G : Type u} [AddCommGroup G] :
    ∀ (n : ℕ), 0 < n → ∀ (S : AddSubgroup G), (∀ s ∈ S, n • s = 0) →
      ∃ (ι : Type u) (y : ι → G), IsCycBasisOn S y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn S hS
    by_cases h1 : n = 1
    · subst h1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact pgroup_cycBasis 2 (G := G) 0 S (by simpa using hS)
    · set p := n.minFac with hpdef
      have hpp : p.Prime := Nat.minFac_prime h1
      have : Fact p.Prime := ⟨hpp⟩
      have hpn : p ∣ n := Nat.minFac_dvd n
      set a := n.factorization p with ha
      obtain ⟨r, hrdef⟩ : ∃ r, r = n / p ^ a := ⟨_, rfl⟩
      have hr : n = p ^ a * r := by rw [hrdef]; exact (Nat.mul_div_cancel' (Nat.ordProj_dvd n p)).symm
      have ha1 : 1 ≤ a := by
        rw [ha]; exact (Nat.Prime.dvd_iff_one_le_factorization hpp hn.ne').mp hpn
      have hcop : Nat.Coprime (p ^ a) r := by
        rw [hrdef]; exact (Nat.coprime_ordCompl hpp hn.ne').pow_left _
      have hrpos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · rw [h] at hr; omega
        · exact h
      have hpa : 2 ≤ p ^ a := le_trans hpp.two_le (Nat.le_self_pow (by omega) p)
      have hrlt : r < n := by rw [hr]; nlinarith
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      push_cast at huv
      have huv' : v * (r : ℤ) + u * (p : ℤ) ^ a = 1 := by linarith
      have hsplit : ∀ g : G, g = ((v * r : ℤ) • g) + ((u * (p : ℤ) ^ a : ℤ) • g) := fun g => by
        rw [← add_smul, huv', one_smul]
      have key1 : ∀ g ∈ S, p ^ a • ((v * r : ℤ) • g) = 0 := by
        intro g hg
        rw [← natCast_zsmul, ← mul_smul]
        have : ((p ^ a : ℕ) : ℤ) * (v * r) = v * (n : ℤ) := by rw [hr]; push_cast; ring
        rw [this, mul_smul, natCast_zsmul, hS g hg, smul_zero]
      have key2 : ∀ g ∈ S, r • ((u * (p : ℤ) ^ a : ℤ) • g) = 0 := by
        intro g hg
        rw [← natCast_zsmul, ← mul_smul]
        have : (r : ℤ) * (u * (p : ℤ) ^ a) = u * (n : ℤ) := by rw [hr]; push_cast; ring
        rw [this, mul_smul, natCast_zsmul, hS g hg, smul_zero]
      have hsup : S.nTors (p ^ a) ⊔ S.nTors r = S := by
        apply le_antisymm
        · exact sup_le (fun g hg => hg.1) (fun g hg => hg.1)
        · intro g hg
          rw [hsplit g]
          exact AddSubgroup.add_mem_sup ⟨S.zsmul_mem hg _, key1 g hg⟩ ⟨S.zsmul_mem hg _, key2 g hg⟩
      have hdisj : S.nTors (p ^ a) ⊓ S.nTors r = ⊥ := by
        rw [AddSubgroup.eq_bot_iff_forall]
        rintro g ⟨⟨hgS, hg1⟩, ⟨-, hg2⟩⟩
        rw [hsplit g]
        have e1 : (v * r : ℤ) • g = 0 := by
          rw [mul_comm, mul_smul, natCast_zsmul, smul_comm, hg2, smul_zero]
        have e2 : (u * (p : ℤ) ^ a : ℤ) • g = 0 := by
          rw [mul_comm, mul_smul, ← Nat.cast_pow, natCast_zsmul, smul_comm, hg1, smul_zero]
        rw [e1, e2, add_zero]
      have : Fact p.Prime := ⟨hpp⟩
      obtain ⟨ι₁, y₁, h₁⟩ := pgroup_cycBasis p a (S.nTors (p ^ a)) (fun s hs => hs.2)
      obtain ⟨ι₂, y₂, h₂⟩ := ih r hrlt hrpos (S.nTors r) (fun s hs => hs.2)
      have := h₁.sup h₂ hdisj
      rw [hsup] at this
      exact ⟨_, _, this⟩

/-- An independent generating family of cyclic subgroups of finite order gives an isomorphism with the
restricted direct sum of the cyclic groups. -/
theorem cycBasis_addEquiv {G : Type u} [AddCommGroup G] {ι : Type u} (y : ι → G)
    (hfin : ∀ i, 0 < addOrderOf (y i)) (h : IsCycBasisOn ⊤ y) :
    Nonempty (G ≃+ DirectSum ι (fun i => ZMod (addOrderOf (y i)))) := by
  classical
  have : ∀ i, NeZero (addOrderOf (y i)) := fun i => ⟨(hfin i).ne'⟩
  let f : ∀ i, ZMod (addOrderOf (y i)) →+ G := fun i =>
    ZMod.lift (addOrderOf (y i)) ⟨zmultiplesHom G (y i), by simp [natCast_zsmul]⟩
  have hf : ∀ i (a : ZMod (addOrderOf (y i))), f i a = a.val • y i := by
    intro i a
    calc f i a = f i (((a.val : ℤ)) : ZMod _) := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = a.val • y i := by
        simp only [f]
        rw [ZMod.lift_coe]
        show (zmultiplesHom G (y i)) ((a.val : ℤ)) = _
        rw [zmultiplesHom_apply, natCast_zsmul]
  have hf1 : ∀ i, f i 1 = y i := by
    intro i
    have := ZMod.lift_coe (addOrderOf (y i)) ⟨zmultiplesHom G (y i), by simp [natCast_zsmul]⟩ 1
    simpa using this
  let ψ : DirectSum ι (fun i => ZMod (addOrderOf (y i))) →+ G := DirectSum.toAddMonoid f
  have hsurj : Surjective ψ := by
    intro g
    have hg : g ∈ AddSubgroup.closure (Set.range y) := h.2.1 (AddSubgroup.mem_top g)
    have : AddSubgroup.closure (Set.range y) ≤ ψ.range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨DirectSum.of _ i 1, by rw [show ψ = DirectSum.toAddMonoid f from rfl, DirectSum.toAddMonoid_of, hf1]⟩
    exact this hg
  have hinj : Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have hd' : ∑ i ∈ d.support, (d i).val • y i = 0 := by
      have : ψ d = d.sum (fun i a => f i a) := by
        simp only [ψ, DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
        exact DFinsupp.sumAddHom_apply f d
      rw [this] at hd
      rw [← hd, DFinsupp.sum]
      exact Finset.sum_congr rfl fun i _ => (hf i (d i)).symm
    have h0 := h.2.2 d.support (fun i => ((d i).val : ℤ)) (by
      rw [← hd']
      exact Finset.sum_congr rfl fun i _ => natCast_zsmul _ _)
    ext i
    by_cases hi : i ∈ d.support
    · have := h0 i hi
      rw [natCast_zsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero] at this
      have hlt : (d i).val < addOrderOf (y i) := ZMod.val_lt _
      have : (d i).val = 0 := Nat.eq_zero_of_dvd_of_lt this hlt
      simpa using (ZMod.val_eq_zero _).mp this
    · simpa using hi
  exact ⟨(AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

/-- Morris, Topology Without Tears, Theorem A5.11.11 (TP-593), Prüfer–Baer: an abelian group of bounded
exponent (`n • g = 0` for all `g`, `n > 0`) is a restricted direct sum of finite cyclic groups. -/
@[kb "morris2024" "Theorem A5.11.11, p. 580"]
theorem exists_addEquiv_directSum_cyclic_of_exponent {G : Type u} [AddCommGroup G] (n : ℕ) (hn : 0 < n)
    (h : ∀ g : G, n • g = 0) :
    ∃ (ι : Type u) (m : ι → ℕ), (∀ i, 0 < m i) ∧ Nonempty (G ≃+ DirectSum ι (fun i => ZMod (m i))) := by
  obtain ⟨ι, y, hy⟩ := bounded_cycBasis n hn ⊤ (fun s _ => h s)
  have hfin : ∀ i, 0 < addOrderOf (y i) := fun i =>
    Nat.pos_of_dvd_of_pos (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (h (y i))) hn
  exact ⟨ι, fun i => addOrderOf (y i), hfin, cycBasis_addEquiv y hfin hy⟩

end UndergradKB.Topology
