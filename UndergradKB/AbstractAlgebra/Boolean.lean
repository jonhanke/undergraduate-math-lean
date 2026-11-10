import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Atoms
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.Monoid.Associated
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Pi
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 19 and switching functions of section 14.3

Boolean algebras: facts about finite Boolean algebras (atoms, representation by the power set of the
atoms), the equational axiomatization of Boolean algebras, divisibility as a partial order,
series-parallel circuits and switching functions. -/

namespace UndergradKB.AbstractAlgebra

section FiniteBoolean

variable {B : Type*} [BooleanAlgebra B]

/-- AA-341. In a Boolean algebra `a ≤ b` iff `a ⊓ bᶜ = ⊥` iff `aᶜ ⊔ b = ⊤`. -/
@[kb "judson2026" "Lemma 19.2.6, p. 267"]
theorem le_iff_inf_compl_eq_bot_iff_compl_sup_eq_top (a b : B) :
    (a ≤ b ↔ a ⊓ bᶜ = ⊥) ∧ (a ⊓ bᶜ = ⊥ ↔ aᶜ ⊔ b = ⊤) := by
  refine ⟨?_, ?_⟩
  · rw [← disjoint_iff, disjoint_compl_right_iff]
  · constructor
    · intro h
      have := congrArg compl h
      simpa using this
    · intro h
      have := congrArg compl h
      simpa using this

/-- AA-346. In a finite Boolean algebra, if `b ≰ c` some atom lies below `b` but not below `c`. -/
@[kb "judson2026" "Lemma 19.2.7, p. 267"]
theorem exists_atom_le_not_le [Finite B] {b c : B} (h : ¬ b ≤ c) :
    ∃ a : B, IsAtom a ∧ a ≤ b ∧ ¬ a ≤ c := by
  have h1 : b ⊓ cᶜ ≠ ⊥ := fun h' => h ((le_iff_inf_compl_eq_bot_iff_compl_sup_eq_top b c).1.2 h')
  obtain ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b ⊓ cᶜ)).resolve_left h1
  refine ⟨a, ha, hab.trans inf_le_left, fun hac => ha.1 ?_⟩
  have h2 : a ≤ c ⊓ cᶜ := le_inf hac (hab.trans inf_le_right)
  simpa using h2

/-- AA-347. In a finite Boolean algebra every element is the join of the atoms below it, and a
finite set of atoms with join `b` is exactly the set of atoms below `b`. -/
@[kb "judson2026" "Lemma 19.2.8, p. 267"]
theorem sup_atoms_le_eq [Finite B] (b : B) :
    (∃ S : Finset B, (∀ a ∈ S, IsAtom a) ∧ S.sup id = b) ∧
    ∀ S : Finset B, (∀ a ∈ S, IsAtom a) → S.sup id = b →
      (S : Set B) = {a : B | IsAtom a ∧ a ≤ b} := by
  refine ⟨?_, ?_⟩
  · refine ⟨(Set.toFinite {a : B | IsAtom a ∧ a ≤ b}).toFinset, by simp +contextual, ?_⟩
    apply le_antisymm
    · refine Finset.sup_le fun a ha => ?_
      simp at ha
      exact ha.2
    · by_contra h
      obtain ⟨a, ha, hab, hac⟩ := exists_atom_le_not_le h
      exact hac (Finset.le_sup (f := id) (by simp [ha, hab]))
  · intro S hS hSb
    ext a
    simp only [Finset.mem_coe, Set.mem_ofPred_eq]
    constructor
    · intro ha
      exact ⟨hS a ha, hSb ▸ Finset.le_sup (f := id) ha⟩
    · rintro ⟨ha, hab⟩
      by_contra hn
      have hd : Disjoint a (S.sup id) := by
        rw [Finset.disjoint_sup_right]
        intro i hi
        exact ha.disjoint_of_ne (hS i hi) (fun h => hn (h ▸ hi))
      rw [hSb] at hd
      exact ha.1 (disjoint_self.1 (hd.mono_right hab |>.mono_left le_rfl))

/-- AA-348. A finite Boolean algebra is order-isomorphic to the power set of its atoms. -/
@[kb "judson2026" "Theorem 19.2.9, p. 267"]
noncomputable def atomsOrderIso [Finite B] : B ≃o Set {a : B // IsAtom a} :=
  letI := Fintype.ofFinite B
  letI := Fintype.toCompleteAtomicBooleanAlgebra B
  CompleteAtomicBooleanAlgebra.toSetOfIsAtom

/-- AA-349. A finite Boolean algebra with `n` atoms has `2 ^ n` elements. -/
@[kb "judson2026" "Corollary 19.2.10, p. 268"]
theorem card_eq_two_pow_card_atoms [Finite B] :
    Nat.card B = 2 ^ Nat.card {a : B // IsAtom a} := by
  rw [Nat.card_congr atomsOrderIso.toEquiv]
  have := Fintype.ofFinite {a : B // IsAtom a}
  rw [Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]

end FiniteBoolean

section Axioms

/-- The equational axioms of Theorem 19.2.2: two commutative, associative, mutually distributive
operations with identities `⊤` (for `⊓`) and `⊥` (for `⊔`), and complements. -/
structure BooleanAxioms (α : Type*) [Min α] [Max α] [Top α] [Bot α] [Compl α] : Prop where
  inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a
  sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a
  inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
  sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  inf_sup_left : ∀ a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
  sup_inf_left : ∀ a b c : α, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
  inf_top : ∀ a : α, a ⊓ ⊤ = a
  sup_bot : ∀ a : α, a ⊔ ⊥ = a
  inf_compl : ∀ a : α, a ⊓ aᶜ = ⊥
  sup_compl : ∀ a : α, a ⊔ aᶜ = ⊤

namespace BooleanAxioms

variable {α : Type*} [Min α] [Max α] [Top α] [Bot α] [Compl α]

theorem sup_idem (h : BooleanAxioms α) (a : α) : a ⊔ a = a :=
  calc a ⊔ a = (a ⊔ a) ⊓ ⊤ := (h.inf_top _).symm
    _ = (a ⊔ a) ⊓ (a ⊔ aᶜ) := by rw [h.sup_compl]
    _ = a ⊔ a ⊓ aᶜ := (h.sup_inf_left a a aᶜ).symm
    _ = a := by rw [h.inf_compl, h.sup_bot]

theorem inf_idem (h : BooleanAxioms α) (a : α) : a ⊓ a = a :=
  calc a ⊓ a = a ⊓ a ⊔ ⊥ := (h.sup_bot _).symm
    _ = a ⊓ a ⊔ a ⊓ aᶜ := by rw [h.inf_compl]
    _ = a ⊓ (a ⊔ aᶜ) := (h.inf_sup_left a a aᶜ).symm
    _ = a := by rw [h.sup_compl, h.inf_top]

theorem sup_top (h : BooleanAxioms α) (a : α) : a ⊔ ⊤ = ⊤ :=
  calc a ⊔ ⊤ = a ⊔ (a ⊔ aᶜ) := by rw [h.sup_compl]
    _ = a ⊔ a ⊔ aᶜ := (h.sup_assoc _ _ _).symm
    _ = ⊤ := by rw [h.sup_idem, h.sup_compl]

theorem inf_bot (h : BooleanAxioms α) (a : α) : a ⊓ ⊥ = ⊥ :=
  calc a ⊓ ⊥ = a ⊓ (a ⊓ aᶜ) := by rw [h.inf_compl]
    _ = a ⊓ a ⊓ aᶜ := (h.inf_assoc _ _ _).symm
    _ = ⊥ := by rw [h.inf_idem, h.inf_compl]

theorem sup_inf_self (h : BooleanAxioms α) (a b : α) : a ⊔ a ⊓ b = a :=
  calc a ⊔ a ⊓ b = a ⊓ ⊤ ⊔ a ⊓ b := by rw [h.inf_top]
    _ = a ⊓ (⊤ ⊔ b) := (h.inf_sup_left a ⊤ b).symm
    _ = a ⊓ ⊤ := by rw [h.sup_comm ⊤ b, h.sup_top]
    _ = a := h.inf_top a

theorem inf_sup_self (h : BooleanAxioms α) (a b : α) : a ⊓ (a ⊔ b) = a :=
  calc a ⊓ (a ⊔ b) = (a ⊔ ⊥) ⊓ (a ⊔ b) := by rw [h.sup_bot]
    _ = a ⊔ ⊥ ⊓ b := (h.sup_inf_left a ⊥ b).symm
    _ = a ⊔ ⊥ := by rw [h.inf_comm ⊥ b, h.inf_bot]
    _ = a := h.sup_bot a

/-- AA-339. Theorem 19.2.2: a set with operations satisfying the equational axioms
(commutativity, associativity, mutual distributivity, identities, complements) is a Boolean
algebra, with the same `⊓`, `⊔`, `⊤`, `⊥`, `ᶜ`. -/
@[kb "judson2026" "Theorem 19.2.2, p. 264-265"]
def toBooleanAlgebra (h : BooleanAxioms α) : BooleanAlgebra α :=
  letI _L : Lattice α := Lattice.mk' h.sup_comm h.sup_assoc h.inf_comm h.inf_assoc
    h.sup_inf_self h.inf_sup_self
  letI D : DistribLattice α := DistribLattice.ofInfSupLe fun a b c => (h.inf_sup_left a b c).le
  { D with
    toCompl := inferInstance
    toTop := inferInstance
    toBot := inferInstance
    inf_compl_le_bot := fun a => (h.inf_compl a).le
    top_le_sup_compl := fun a => (h.sup_compl a).ge
    le_top := fun a => sup_eq_right.1 (h.sup_top a)
    bot_le := fun a => sup_eq_right.1 ((h.sup_comm _ _).trans (h.sup_bot a))
    sdiff := fun a b => a ⊓ bᶜ
    himp := fun a b => b ⊔ aᶜ
    sdiff_eq := fun _ _ => rfl
    himp_eq := fun _ _ => rfl }

end BooleanAxioms

end Axioms

section Divisibility

/-- AA-330. Divisibility on `ℕ` is reflexive, antisymmetric and transitive. -/
@[kb "judson2026" "Example 19.1.5, p. 261"]
theorem nat_dvd_partial_order_axioms :
    (∀ n : ℕ, n ∣ n) ∧ (∀ m n : ℕ, m ∣ n → n ∣ m → m = n) ∧
      ∀ a b c : ℕ, a ∣ b → b ∣ c → a ∣ c :=
  ⟨dvd_refl, fun _ _ => Nat.dvd_antisymm, fun _ _ _ => dvd_trans⟩

/-- A synonym for `ℕ` carrying the divisibility order. -/
def NatDvd : Type := ℕ

/-- The underlying natural number. -/
def NatDvd.val (a : NatDvd) : ℕ := a

instance : PartialOrder NatDvd where
  le a b := a.val ∣ b.val
  le_refl _ := Nat.dvd_refl _
  le_trans _ _ _ := Nat.dvd_trans
  le_antisymm _ _ := Nat.dvd_antisymm

/-- AA-330. On `NatDvd` the order relation is divisibility. -/
theorem NatDvd.le_iff (a b : NatDvd) : a ≤ b ↔ a.val ∣ b.val := Iff.rfl

/-- AA-330. In `Associates ℕ` (where the `PartialOrder` is divisibility up to units) the order is
divisibility. -/
theorem associates_nat_le_iff (a b : ℕ) :
    Associates.mk a ≤ Associates.mk b ↔ a ∣ b := Associates.mk_le_mk_iff_dvd

end Divisibility

section Switching

/-- AA-224. A switching (Boolean) function of `n` variables, a map `𝔹ⁿ → 𝔹`. -/
@[kb "judson2026" "Definition (unnumbered) switching function, p. 194"]
def SwitchingFunction (n : ℕ) : Type := (Fin n → Bool) → Bool

instance (n : ℕ) : Fintype (SwitchingFunction n) :=
  inferInstanceAs (Fintype ((Fin n → Bool) → Bool))

/-- AA-224. There are `2 ^ 2 ^ n` switching functions of `n` variables. -/
@[kb "judson2026" "Definition (unnumbered) switching function, p. 194"]
theorem card_switchingFunction (n : ℕ) : Fintype.card (SwitchingFunction n) = 2 ^ 2 ^ n := by
  show Fintype.card ((Fin n → Bool) → Bool) = _
  simp

instance (n : ℕ) : SMul (Equiv.Perm (Fin n)) (SwitchingFunction n) where
  smul σ f := fun x => f (fun i => x (σ i))

/-- AA-224. Permuting the variables is an action of the permutation group on switching
functions. -/
@[kb "judson2026" "Definition (unnumbered) equivalent switching functions, p. 194"]
instance (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (SwitchingFunction n) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- AA-224. Two switching functions are equivalent if one is obtained from the other by permuting
the variables. -/
@[kb "judson2026" "Definition (unnumbered) equivalent switching functions, p. 194"]
def SwitchingFunction.Equivalent {n : ℕ} (f g : SwitchingFunction n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), σ • f = g

/-- AA-224. Equivalence of switching functions is the orbit relation of the action. -/
theorem SwitchingFunction.equivalent_iff {n : ℕ} (f g : SwitchingFunction n) :
    f.Equivalent g ↔ g ∈ MulAction.orbit (Equiv.Perm (Fin n)) f :=
  MulAction.mem_orbit_iff.symm

end Switching

section Circuits

/-- AA-350. Series-parallel circuits on `n` switch variables: the constants "always closed" and
"always open", a switch, the complementary switch, circuits in series and circuits in parallel. -/
@[kb "judson2026" "Definition series-parallel circuits, p. 268-269"]
inductive Circuit (n : ℕ) : Type
  | closed : Circuit n
  | open_ : Circuit n
  | switch : Fin n → Circuit n
  | notSwitch : Fin n → Circuit n
  | series : Circuit n → Circuit n → Circuit n
  | parallel : Circuit n → Circuit n → Circuit n

namespace Circuit

variable {n : ℕ}

/-- AA-350. The behaviour of a circuit under an assignment of the switches: current flows in a
series connection when both parts conduct, in a parallel connection when one does. -/
@[kb "judson2026" "Definition series-parallel circuits, p. 268-269"]
def eval (v : Fin n → Bool) : Circuit n → Bool
  | closed => true
  | open_ => false
  | switch i => v i
  | notSwitch i => !v i
  | series a b => eval v a && eval v b
  | parallel a b => eval v a || eval v b

/-- The behaviour of a circuit as a switching function. -/
def evalFun (c : Circuit n) : (Fin n → Bool) → Bool := fun v => eval v c

/-- The complementary circuit (De Morgan dual). -/
def compl : Circuit n → Circuit n
  | closed => open_
  | open_ => closed
  | switch i => notSwitch i
  | notSwitch i => switch i
  | series a b => parallel (compl a) (compl b)
  | parallel a b => series (compl a) (compl b)

theorem eval_compl (v : Fin n → Bool) (c : Circuit n) : eval v c.compl = !eval v c := by
  induction c <;> simp [compl, eval, *]

end Circuit

/-- Circuits up to equal behaviour. -/
def CircuitClass (n : ℕ) : Type := Quotient (Setoid.ker (Circuit.evalFun (n := n)))

namespace CircuitClass

variable {n : ℕ}

/-- The behaviour of a class of circuits. -/
def eval : CircuitClass n → ((Fin n → Bool) → Bool) :=
  Quotient.lift Circuit.evalFun fun _ _ h => h

theorem eval_injective : Function.Injective (eval (n := n)) := by
  intro a b
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  intro h
  exact Quotient.sound h

/-- The class of a circuit. -/
def mk (c : Circuit n) : CircuitClass n := Quotient.mk _ c

@[simp] theorem eval_mk (c : Circuit n) : eval (mk c) = Circuit.evalFun c := rfl

theorem mk_surj (a : CircuitClass n) : ∃ c, mk c = a := Quotient.exists_rep a

instance : Max (CircuitClass n) :=
  ⟨Quotient.map₂ Circuit.parallel fun a a' ha b b' hb => by
    have ha' : Circuit.evalFun a = Circuit.evalFun a' := ha
    have hb' : Circuit.evalFun b = Circuit.evalFun b' := hb
    show Circuit.evalFun _ = Circuit.evalFun _
    funext v
    have h1 := congrFun ha' v
    have h2 := congrFun hb' v
    simp_all [Circuit.evalFun, Circuit.eval]⟩

instance : Min (CircuitClass n) :=
  ⟨Quotient.map₂ Circuit.series fun a a' ha b b' hb => by
    have ha' : Circuit.evalFun a = Circuit.evalFun a' := ha
    have hb' : Circuit.evalFun b = Circuit.evalFun b' := hb
    show Circuit.evalFun _ = Circuit.evalFun _
    funext v
    have h1 := congrFun ha' v
    have h2 := congrFun hb' v
    simp_all [Circuit.evalFun, Circuit.eval]⟩

instance : Compl (CircuitClass n) :=
  ⟨Quotient.map Circuit.compl fun a a' ha => by
    have ha' : Circuit.evalFun a = Circuit.evalFun a' := ha
    show Circuit.evalFun _ = Circuit.evalFun _
    funext v
    have h1 := congrFun ha' v
    simp_all [Circuit.evalFun, Circuit.eval_compl]⟩

instance : Top (CircuitClass n) := ⟨mk Circuit.closed⟩
instance : Bot (CircuitClass n) := ⟨mk Circuit.open_⟩
instance : LE (CircuitClass n) := ⟨fun a b => eval a ≤ eval b⟩
instance : LT (CircuitClass n) := ⟨fun a b => eval a < eval b⟩
instance : SDiff (CircuitClass n) := ⟨fun a b => a ⊓ bᶜ⟩
instance : HImp (CircuitClass n) := ⟨fun a b => b ⊔ aᶜ⟩

/-- AA-351. Circuits up to equal behaviour form a Boolean algebra, with parallel as join, series as
meet, the complement circuit as complement. -/
@[kb "judson2026" "Theorem 19.3.7, p. 269"]
instance instBooleanAlgebra : BooleanAlgebra (CircuitClass n) :=
  Function.Injective.booleanAlgebra eval eval_injective Iff.rfl Iff.rfl
    (by
      intro a b
      obtain ⟨c, rfl⟩ := mk_surj a
      obtain ⟨d, rfl⟩ := mk_surj b
      funext v
      rfl)
    (by
      intro a b
      obtain ⟨c, rfl⟩ := mk_surj a
      obtain ⟨d, rfl⟩ := mk_surj b
      funext v
      rfl)
    (by funext v; rfl)
    (by funext v; rfl)
    (by
      intro a
      obtain ⟨c, rfl⟩ := mk_surj a
      funext v
      exact Circuit.eval_compl v c)
    (by
      intro a b
      obtain ⟨c, rfl⟩ := mk_surj a
      obtain ⟨d, rfl⟩ := mk_surj b
      funext v
      show (Circuit.eval v c && Circuit.eval v d.compl) = (Circuit.evalFun c v \ Circuit.evalFun d v)
      rw [Circuit.eval_compl]
      rfl)
    (by
      intro a b
      obtain ⟨c, rfl⟩ := mk_surj a
      obtain ⟨d, rfl⟩ := mk_surj b
      funext v
      show (Circuit.eval v d || Circuit.eval v c.compl) = (Circuit.evalFun c v ⇨ Circuit.evalFun d v)
      rw [Circuit.eval_compl]
      rfl)

/-- AA-351. The behaviour map is a Boolean algebra embedding into the switching functions: series
is meet, parallel is join, and the complement circuit is the complement. -/
theorem eval_series_parallel_compl (c d : Circuit n) :
    Circuit.evalFun (Circuit.series c d) = Circuit.evalFun c ⊓ Circuit.evalFun d ∧
    Circuit.evalFun (Circuit.parallel c d) = Circuit.evalFun c ⊔ Circuit.evalFun d ∧
    Circuit.evalFun c.compl = (Circuit.evalFun c)ᶜ := by
  refine ⟨?_, ?_, ?_⟩ <;> funext v <;> simp [Circuit.evalFun, Circuit.eval, Circuit.eval_compl]

end CircuitClass

end Circuits

end UndergradKB.AbstractAlgebra
