import UndergradKB.Foundations.DPRM.Sequences
import Mathlib.Computability.Partrec

/-!
# Foundations, DPRM: the graph of a partial recursive function is Diophantine

`partrec_graph_dioph`: for every partial recursive `f : ℕ →. ℕ` (Mathlib's `Nat.Partrec`), the set
`{(x, y) | y ∈ f x}` is Diophantine. Induction on `Nat.Partrec`: the basic functions and composition
are immediate; primitive recursion codes the run by Gödel's β-function and uses Davis's bounded
universal quantifier theorem; minimisation uses the bounded quantifier directly.
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Nat Vector3

/-- The graph of a partial function, as a set of vectors `(x, y)`. -/
def graphSet (f : ℕ →. ℕ) : Set (Vector3 ℕ 2) := {v | v &1 ∈ f (v &0)}

theorem graph_comp {α : Type} {f : ℕ →. ℕ} (hf : Dioph (graphSet f)) {X F : (α → ℕ) → ℕ}
    (dX : DiophFn X) (dF : DiophFn F) : Dioph {v | F v ∈ f (X v)} :=
  dioph_comp2 (S := fun x y => y ∈ f x) dX dF hf

/-- Membership in a primitive recursion, as the existence of the sequence of intermediate values. -/
theorem mem_rec_iff (f g : ℕ →. ℕ) (a : ℕ) : ∀ (n y : ℕ),
    y ∈ (n.rec (f a) fun i IH => IH.bind fun s => g (Nat.pair a (Nat.pair i s)) : Part ℕ) ↔
      ∃ s : ℕ → ℕ, s 0 ∈ f a ∧ (∀ i < n, s (i + 1) ∈ g (Nat.pair a (Nat.pair i (s i)))) ∧ s n = y
  | 0, y => by
    constructor
    · intro h
      exact ⟨fun _ => y, h, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
    · rintro ⟨s, h0, -, rfl⟩
      exact h0
  | n + 1, y => by
    simp only [Part.mem_bind_iff]
    constructor
    · rintro ⟨z, hz, hy⟩
      obtain ⟨s, h0, hs, rfl⟩ := (mem_rec_iff f g a n z).1 hz
      refine ⟨fun i => if i = n + 1 then y else s i, by simpa using h0, fun i hi => ?_, by simp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · simpa [show i ≠ n + 1 by omega, show i ≠ n by omega] using hs i hi
      · simpa using hy
    · rintro ⟨s, h0, hs, rfl⟩
      refine ⟨s n, (mem_rec_iff f g a n (s n)).2 ⟨s, h0, fun i hi => hs i (by omega), rfl⟩, ?_⟩
      exact hs n (Nat.lt_succ_self n)

/-- The β-function form of `mem_rec_iff`. -/
theorem mem_rec_iff_beta (f g : ℕ →. ℕ) (a n y : ℕ) :
    y ∈ (n.rec (f a) fun i IH => IH.bind fun s => g (Nat.pair a (Nat.pair i s)) : Part ℕ) ↔
      ∃ c d, betaFn c d 0 ∈ f a ∧
        (∀ i < n, betaFn c d (i + 1) ∈ g (Nat.pair a (Nat.pair i (betaFn c d i)))) ∧
          betaFn c d n = y := by
  rw [mem_rec_iff]
  constructor
  · rintro ⟨s, h0, hs, rfl⟩
    obtain ⟨c, d, hcd⟩ := beta_exists n s
    refine ⟨c, d, by rw [hcd 0 (Nat.zero_le _)]; exact h0, fun i hi => ?_, hcd n le_rfl⟩
    rw [hcd (i + 1) hi, hcd i hi.le]
    exact hs i hi
  · rintro ⟨c, d, h0, hs, rfl⟩
    exact ⟨betaFn c d, h0, hs, rfl⟩

/-- Membership in a primitive recursion on a pair `N = ⟨a, n⟩`, in β-function form. -/
theorem prec_char (f g : ℕ → Part ℕ) (N y : ℕ) :
    y ∈ Nat.unpaired (fun a n => (n.rec (f a) fun i IH =>
        IH.bind fun s => g (Nat.pair a (Nat.pair i s)) : Part ℕ)) N ↔
      ∃ a n c d, Nat.pair a n = N ∧ betaFn c d 0 ∈ f a ∧
        (∀ k < n, betaFn c d (k + 1) ∈ g (Nat.pair a (Nat.pair k (betaFn c d k)))) ∧
          betaFn c d n = y := by
  rw [Nat.unpaired]
  constructor
  · intro h
    obtain ⟨c, d, h0, hs, hy⟩ := (mem_rec_iff_beta f g _ _ _).1 h
    exact ⟨_, _, c, d, Nat.pair_unpair _, h0, hs, hy⟩
  · rintro ⟨a, n, c, d, rfl, h0, hs, hy⟩
    rw [Nat.unpair_pair]
    exact (mem_rec_iff_beta f g a n _).2 ⟨c, d, h0, hs, hy⟩

/-- Membership in a minimisation. -/
theorem rfind_char (F : ℕ → Part ℕ) (x y : ℕ) :
    y ∈ Nat.rfind (fun n => (fun m => decide (m = 0)) <$> F (Nat.pair x n)) ↔
      0 ∈ F (Nat.pair x y) ∧ ∀ k < y, ∃ z, z + 1 ∈ F (Nat.pair x k) := by
  refine Nat.mem_rfind.trans ?_
  simp only [Part.map_eq_map, Part.mem_map_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hk⟩
    refine ⟨hm, fun k hk' => ?_⟩
    obtain ⟨m, hm, hne⟩ := hk hk'
    obtain ⟨z, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    exact ⟨z, hm⟩
  · rintro ⟨h0, hk⟩
    refine ⟨⟨0, h0, rfl⟩, fun {k} hk' => ?_⟩
    obtain ⟨z, hz⟩ := hk k hk'
    exact ⟨z + 1, hz, Nat.succ_ne_zero z⟩

/-- **The graph of every partial recursive function is Diophantine.** -/
theorem partrec_graph_dioph {f : ℕ →. ℕ} (hf : Nat.Partrec f) : Dioph (graphSet f) := by
  induction hf with
  | zero =>
    refine (eq_dioph (D&1) (const_dioph 0)).ext fun v => ?_
    change v &1 = 0 ↔ v &1 ∈ Part.some 0
    simp
  | succ =>
    refine (eq_dioph (D&1) (add_dioph (D&0) (const_dioph 1))).ext fun v => ?_
    change v &1 = v &0 + 1 ↔ v &1 ∈ Part.some (v &0 + 1)
    simp
  | left =>
    have : Dioph {w : Vector3 ℕ 3 | Nat.pair (w &2) (w &0) = w &1} :=
      eq_dioph (pair_dioph (D&2) (D&0)) (D&1)
    refine ((D∃) 2 this).ext fun v => ?_
    show (∃ b, Nat.pair (v &1) b = v &0) ↔ v &1 ∈ (↑(fun n : ℕ => n.unpair.1) : ℕ →. ℕ) (v &0)
    rw [PFun.coe_val, Part.mem_some_iff]
    constructor
    · rintro ⟨b, hb⟩
      rw [← hb, Nat.unpair_pair]
    · intro h
      exact ⟨(v &0).unpair.2, by rw [h, Nat.pair_unpair]⟩
  | right =>
    have : Dioph {w : Vector3 ℕ 3 | Nat.pair (w &0) (w &2) = w &1} :=
      eq_dioph (pair_dioph (D&0) (D&2)) (D&1)
    refine ((D∃) 2 this).ext fun v => ?_
    show (∃ b, Nat.pair b (v &1) = v &0) ↔ v &1 ∈ (↑(fun n : ℕ => n.unpair.2) : ℕ →. ℕ) (v &0)
    rw [PFun.coe_val, Part.mem_some_iff]
    constructor
    · rintro ⟨b, hb⟩
      rw [← hb, Nat.unpair_pair]
    · intro h
      exact ⟨(v &0).unpair.1, by rw [h, Nat.pair_unpair]⟩
  | @pair f g _ _ hf hg =>
    -- w = b :: a :: v, with x = w&2, y = w&3
    have : Dioph {w : Vector3 ℕ 4 | w &1 ∈ f (w &2) ∧ w &0 ∈ g (w &2) ∧
        w &3 = Nat.pair (w &1) (w &0)} :=
      graph_comp hf (D&2) (D&1) |>.inter <| graph_comp hg (D&2) (D&0) |>.inter <|
        eq_dioph (D&3) (pair_dioph (D&1) (D&0))
    refine ((D∃) 2 ((D∃) 3 this)).ext fun v => ?_
    show (∃ a b, a ∈ f (v &0) ∧ b ∈ g (v &0) ∧ v &1 = Nat.pair a b) ↔
      v &1 ∈ (Nat.pair <$> f (v &0) <*> g (v &0))
    simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, Part.map_eq_map,
      Part.mem_map_iff]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨_, ⟨a, ha, rfl⟩, b, hb, h.symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, h⟩
      exact ⟨a, b, ha, hb, h.symm⟩
  | @comp f g _ _ hf hg =>
    -- w = z :: v, with x = w&1, y = w&2
    have : Dioph {w : Vector3 ℕ 3 | w &0 ∈ g (w &1) ∧ w &2 ∈ f (w &0)} :=
      (graph_comp hg (D&1) (D&0)).inter (graph_comp hf (D&0) (D&2))
    refine ((D∃) 2 this).ext fun v => ?_
    exact (Part.mem_bind_iff (f := g (v &0)) (g := f) (b := v &1)).symm
  | @prec f g _ _ hf hg =>
    -- w = d :: c :: n :: a :: v, with N = w&4, y = w&5
    have hstep : Dioph {u : Vector3 ℕ 7 |
        betaFn (u &2) (u &1) (u &0 + 1) ∈ g (Nat.pair (u &4) (Nat.pair (u &0)
          (betaFn (u &2) (u &1) (u &0))))} :=
      graph_comp hg (pair_dioph (D&4) (pair_dioph (D&0) (betaFn_dioph (D&2) (D&1) (D&0))))
        (betaFn_dioph (D&2) (D&1) (add_dioph (D&0) (const_dioph 1)))
    have : Dioph {w : Vector3 ℕ 6 | Nat.pair (w &3) (w &2) = w &4 ∧
        betaFn (w &1) (w &0) 0 ∈ f (w &3) ∧
        (∀ k < w &2, (k :: w) ∈ {u : Vector3 ℕ 7 |
          betaFn (u &2) (u &1) (u &0 + 1) ∈ g (Nat.pair (u &4) (Nat.pair (u &0)
            (betaFn (u &2) (u &1) (u &0))))}) ∧
        betaFn (w &1) (w &0) (w &2) = w &5} :=
      eq_dioph (pair_dioph (D&3) (D&2)) (D&4) |>.inter <|
        graph_comp hf (D&3) (betaFn_dioph (D&1) (D&0) (const_dioph 0)) |>.inter <|
          vec_forall_lt_dioph hstep (D&2) |>.inter <|
            eq_dioph (betaFn_dioph (D&1) (D&0) (D&2)) (D&5)
    refine ((D∃) 2 ((D∃) 3 ((D∃) 4 ((D∃) 5 this)))).ext fun v => ?_
    exact (prec_char f g (v &0) (v &1)).symm
  | @rfind f _ hf =>
    -- the minimisation: w = z :: k :: v, with x = w&2
    have hstep : Dioph {w : Vector3 ℕ 4 | w &0 + 1 ∈ f (Nat.pair (w &2) (w &1))} :=
      graph_comp hf (pair_dioph (D&2) (D&1)) (add_dioph (D&0) (const_dioph 1))
    have : Dioph {v : Vector3 ℕ 2 | 0 ∈ f (Nat.pair (v &0) (v &1)) ∧
        ∀ k < v &1, (k :: v) ∈ {u : Vector3 ℕ 3 | ∃ z, (z :: u) ∈
          {w : Vector3 ℕ 4 | w &0 + 1 ∈ f (Nat.pair (w &2) (w &1))}}} :=
      (graph_comp hf (pair_dioph (D&0) (D&1)) (const_dioph 0)).inter
        (vec_forall_lt_dioph ((D∃) 3 hstep) (D&1))
    exact this.ext fun v => (rfind_char f (v &0) (v &1)).symm

end UndergradKB.Foundations.DPRM
