import Mathlib.Topology.Bases
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Constructions
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import UndergradKB.Common.Attr

/-!
# Density character and the Hewitt-Marczewski-Pondiczery theorem

The density character of a space is the least cardinality of a dense subset.  The main result: if
`I` has at most `2^m` elements and every `X i` has a dense subset of cardinality at most `m`
(`m` infinite), then `∏ i, X i` has a dense subset of cardinality at most `m`.

To keep universes apart, the proofs work with maps with dense range from an infinite *index type*
`M` (so "a dense subset of cardinality at most `#M`" becomes `DenseRange f` for some `f : M → X`);
cardinal-valued statements are derived in the last sections.
-/

open Topology Set Filter Cardinal

namespace UndergradKB.Topology

universe u v w

/-! ### Density criterion in a product of discrete spaces -/

/-- A subset of a product of discrete spaces is dense iff it agrees with every point on every finite
set of coordinates. -/
theorem dense_pi_iff_finset_agree {ι : Type v} {Y : ι → Type w} [∀ i, TopologicalSpace (Y i)]
    [∀ i, DiscreteTopology (Y i)] {D : Set (∀ i, Y i)} :
    Dense D ↔ ∀ (x : ∀ i, Y i) (T : Finset ι), ∃ d ∈ D, ∀ i ∈ T, d i = x i := by
  constructor
  · intro hD x T
    have hU : IsOpen (Set.pi (T : Set ι) fun i => ({x i} : Set (Y i))) :=
      isOpen_set_pi T.finite_toSet fun i _ => isOpen_discrete _
    obtain ⟨d, hd1, hd2⟩ := dense_iff_inter_open.mp hD _ hU ⟨x, fun i _ => rfl⟩
    exact ⟨d, hd2, fun i hi => hd1 i hi⟩
  · intro h
    rw [dense_iff_inter_open]
    rintro U hU ⟨f, hf⟩
    obtain ⟨T, u, hu, hsub⟩ := isOpen_pi_iff.mp hU f hf
    obtain ⟨d, hdD, hd⟩ := h f T
    exact ⟨d, hsub (fun i hi => by rw [hd i hi]; exact (hu i hi).2), hdD⟩

theorem dense_of_isEmpty' {α : Type v} [TopologicalSpace α] [IsEmpty α] (s : Set α) : Dense s :=
  fun x => isEmptyElim x

/-! ### Lemma 10.3.35 -/

/-- Morris, Topology Without Tears, Lemma 10.3.35 (TP-299). Let `D` be discrete. If `A F` is dense
in `F^ι` for every finite `F ⊆ D`, then the union of the sets `A F` (viewed in `D^ι`) is dense in
`D^ι`. -/
@[kb "morris2024" "Lemma 10.3.35, p. 287"]
theorem dense_iUnion_image_pi_finset {D : Type u} [TopologicalSpace D] [DiscreteTopology D]
    {ι : Type v} (A : (F : Finset D) → Set (ι → F)) (hA : ∀ F, Dense (A F)) :
    Dense (⋃ F : Finset D, (fun (a : ι → F) (i : ι) => (a i : D)) '' A F) := by
  classical
  rw [dense_pi_iff_finset_agree]
  intro x T
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have : Nonempty (ι → (∅ : Finset D)) := ⟨fun i => isEmptyElim i⟩
    obtain ⟨a, ha⟩ := (hA ∅).nonempty
    exact ⟨_, mem_iUnion.mpr ⟨∅, mem_image_of_mem _ ha⟩, fun i => isEmptyElim i⟩
  · let F : Finset D := insert (x i₀) (T.image x)
    let a₀ : ι → F := fun i =>
      if h : x i ∈ F then ⟨x i, h⟩ else ⟨x i₀, Finset.mem_insert_self _ _⟩
    obtain ⟨a, haA, haT⟩ := dense_pi_iff_finset_agree.mp (hA F) a₀ T
    refine ⟨fun i => (a i : D), mem_iUnion.mpr ⟨F, mem_image_of_mem _ haA⟩, ?_⟩
    intro i hi
    have hmem : x i ∈ F := Finset.mem_insert_of_mem (Finset.mem_image_of_mem x hi)
    show ((a i : F) : D) = x i
    rw [haT i hi]
    simp [a₀, hmem]

/-! ### Dense range from an infinite index type -/

/-- The core of Proposition 10.3.36: for an infinite type `M` and an injective family `e` of subsets
of `M` indexed by `ι`, there is a map `M → {0,1}^ι` with dense range. -/
theorem exists_denseRange_bool_pow {M : Type u} [Infinite M] {ι : Type v} (e : ι → Set M)
    (he : Function.Injective e) : ∃ f : M → (ι → Bool), DenseRange f := by
  classical
  let φ : Finset M × Finset (Finset M) → (ι → Bool) :=
    fun s i => decide (s.1.filter (· ∈ e i) ∈ s.2)
  have hφ : DenseRange φ := by
    rw [DenseRange, dense_pi_iff_finset_agree]
    intro x T
    have hsep : ∀ i j : ι, ∃ a : M, i ≠ j → ¬ (a ∈ e i ↔ a ∈ e j) := by
      intro i j
      by_cases hij : i = j
      · exact ⟨Classical.arbitrary M, fun h => absurd hij h⟩
      · have hne : e i ≠ e j := fun h => hij (he h)
        obtain ⟨a, ha⟩ : ∃ a, ¬ (a ∈ e i ↔ a ∈ e j) := by
          by_contra hcon
          push Not at hcon
          exact hne (Set.ext hcon)
        exact ⟨a, fun _ => ha⟩
    choose w hw using hsep
    let F : Finset M := (T ×ˢ T).image (fun p => w p.1 p.2)
    let 𝓕 : Finset (Finset M) :=
      (T.filter (fun i => x i = true)).image (fun i => F.filter (· ∈ e i))
    refine ⟨φ (F, 𝓕), ⟨(F, 𝓕), rfl⟩, ?_⟩
    intro i hi
    have hdist : ∀ j ∈ T, j ≠ i → F.filter (· ∈ e j) ≠ F.filter (· ∈ e i) := by
      intro j hj hji heq
      have hmem : w j i ∈ F :=
        Finset.mem_image.mpr ⟨(j, i), Finset.mem_product.mpr ⟨hj, hi⟩, rfl⟩
      apply hw j i hji
      have := Finset.ext_iff.mp heq (w j i)
      simpa [Finset.mem_filter, hmem] using this
    show decide (F.filter (· ∈ e i) ∈ 𝓕) = x i
    cases hx : x i
    · simp only [decide_eq_false_iff_not]
      intro hmemF
      obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hmemF
      rw [Finset.mem_filter] at hj
      by_cases hji : j = i
      · have h2 := hj.2
        rw [hji, hx] at h2
        exact absurd h2 (by decide)
      · exact hdist j hj.1 hji hjeq
    · simp only [decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
  have hcard : #(Finset M × Finset (Finset M)) = #M := by
    have : Infinite (Finset M) :=
      Infinite.of_injective (fun a => ({a} : Finset M)) (fun a b h => Finset.singleton_injective h)
    have h1 : #(Finset M) = #M := Cardinal.mk_finset_of_infinite M
    have h2 : #(Finset (Finset M)) = #(Finset M) := Cardinal.mk_finset_of_infinite (Finset M)
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    rw [h2, h1, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk M)]
  obtain ⟨σ⟩ := Cardinal.eq.mp hcard
  refine ⟨φ ∘ σ.symm, ?_⟩
  rw [DenseRange, σ.symm.surjective.range_comp]
  exact hφ

/-- For an infinite type `M` and a finite set `F`, `Set M × F` embeds in `Set M`. -/
theorem nonempty_embedding_set_prod_finite (M : Type u) [Infinite M] (F : Type u) [Finite F] :
    Nonempty (Set M × F ↪ Set M) := by
  have hinf : ℵ₀ ≤ #(Set M) := by
    rw [Cardinal.mk_set]
    exact (Cardinal.aleph0_le_mk M).trans (Cardinal.cantor _).le
  have hF : #F ≤ #(Set M) := (Cardinal.mk_lt_aleph0 (α := F)).le.trans hinf
  have h : #(Set M × F) ≤ #(Set M) := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    calc #(Set M) * #F ≤ #(Set M) * #(Set M) := mul_le_mul' le_rfl hF
      _ = #(Set M) := Cardinal.mul_eq_self hinf
  exact (Cardinal.le_def _ _).mp h

/-- The core of Corollary 10.3.39: for a nonempty finite discrete space `F` and a family of at most
`2^#M` coordinates there is a map `M → F^ι` with dense range. -/
theorem exists_denseRange_finite_pow {M : Type u} [Infinite M] {ι : Type v} (e : ι ↪ Set M)
    (F : Type u) [Finite F] [Nonempty F] [TopologicalSpace F] [DiscreteTopology F] :
    ∃ f : M → (ι → F), DenseRange f := by
  classical
  obtain ⟨E⟩ := nonempty_embedding_set_prod_finite M F
  let e' : ι × F ↪ Set M := (Function.Embedding.prodMap e (Function.Embedding.refl F)).trans E
  obtain ⟨f₀, hf₀⟩ := exists_denseRange_bool_pow e' e'.injective
  let enc : F → (F → Bool) := fun a b => decide (a = b)
  have hinj : Function.Injective enc := by
    intro a b h
    have := congrFun h a
    simpa [enc, eq_comm] using this
  let g : (F → Bool) → F := Function.invFun enc
  let Ψ : (ι × F → Bool) → (ι → F) := fun h i => g (fun b => h (i, b))
  have hΨc : Continuous Ψ := continuous_pi fun i =>
    (continuous_of_discreteTopology (f := g)).comp (continuous_pi fun b => continuous_apply (i, b))
  have hΨs : Function.Surjective Ψ := by
    intro y
    refine ⟨fun p => enc (y p.1) p.2, ?_⟩
    funext i
    exact Function.leftInverse_invFun hinj (y i)
  exact ⟨Ψ ∘ f₀, hΨs.denseRange.comp hf₀ hΨc⟩

/-- The core of Proposition 10.3.40: for an infinite discrete space `M` and a family of at most
`2^#M` coordinates there is a map `M → M^ι` with dense range. -/
theorem exists_denseRange_discrete_pow {M : Type u} [Infinite M] [TopologicalSpace M]
    [DiscreteTopology M] {ι : Type v} (e : ι ↪ Set M) :
    ∃ f : M → (ι → M), DenseRange f := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ i => isEmptyElim i, Function.Surjective.denseRange ?_⟩
    intro y
    exact ⟨Classical.arbitrary M, funext fun i => isEmptyElim i⟩
  · have hF : ∀ F : Finset M, Nonempty F → ∃ g : M → (ι → F), DenseRange g :=
      fun F hF => by
        haveI := hF
        exact exists_denseRange_finite_pow e F
    let d0 : M := Classical.arbitrary M
    let G : Finset M → M → (ι → M) := fun F m =>
      if h : Nonempty F then fun i => ((Classical.choose (hF F h) m i : F) : M) else fun _ => d0
    let A : (F : Finset M) → Set (ι → F) := fun F => {a | ∃ m, (fun i => (a i : M)) = G F m}
    have hA : ∀ F, Dense (A F) := by
      intro F
      by_cases h : Nonempty F
      · refine Dense.mono ?_ (Classical.choose_spec (hF F h))
        rintro _ ⟨m, rfl⟩
        refine ⟨m, ?_⟩
        simp [G]
      · haveI : IsEmpty F := not_nonempty_iff.mp h
        haveI : IsEmpty (ι → F) := ⟨fun a => isEmptyElim (a (Classical.choice hι))⟩
        exact dense_of_isEmpty' _
    have hdense := dense_iUnion_image_pi_finset A hA
    have hsub : (⋃ F : Finset M, (fun (a : ι → F) (i : ι) => (a i : M)) '' A F) ⊆
        range (fun p : Finset M × M => G p.1 p.2) := by
      intro d hd
      rw [mem_iUnion] at hd
      obtain ⟨F, a, ⟨m, hm⟩, rfl⟩ := hd
      exact ⟨(F, m), hm.symm⟩
    have hcard : #(Finset M × M) = #M := by
      have h1 : #(Finset M) = #M := Cardinal.mk_finset_of_infinite M
      simp only [Cardinal.mk_prod, Cardinal.lift_id]
      rw [h1, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk M)]
    obtain ⟨σ⟩ := Cardinal.eq.mp hcard
    refine ⟨(fun p : Finset M × M => G p.1 p.2) ∘ σ.symm, ?_⟩
    rw [DenseRange, σ.symm.surjective.range_comp]
    exact hdense.mono hsub

/-- The core of the Hewitt-Marczewski-Pondiczery theorem: if every `X i` receives a map from `M`
with dense range and `ι` embeds in `Set M`, then `∏ i, X i` receives a map from `M` with dense
range. -/
theorem exists_denseRange_pi {M : Type u} [Infinite M] {ι : Type v} (e : ι ↪ Set M)
    {X : ι → Type w} [∀ i, TopologicalSpace (X i)] (ψ : ∀ i, M → X i)
    (hψ : ∀ i, DenseRange (ψ i)) : ∃ f : M → (∀ i, X i), DenseRange f := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨h, hh⟩ := exists_denseRange_discrete_pow e
  let Ψ : (ι → M) → (∀ i, X i) := fun g i => ψ i (g i)
  have hΨc : Continuous Ψ := continuous_pi fun i =>
    (continuous_of_discreteTopology (f := ψ i)).comp (continuous_apply i)
  have hΨd : DenseRange Ψ := by
    have : Dense (Set.pi univ fun i => range (ψ i)) := dense_pi _ (fun i _ => hψ i)
    refine this.mono ?_
    intro y hy
    choose m hm using fun i => hy i (mem_univ i)
    exact ⟨m, funext hm⟩
  exact ⟨Ψ ∘ h, hΨd.comp hh hΨc⟩

/-! ### Density character -/

/-- Morris, Topology Without Tears, Definition 10.3.37 (TP-301). The density character of a space
is the least cardinality of a dense subset. -/
@[kb "morris2024" "Definition 10.3.37, p. 289"]
noncomputable def densityCharacter (X : Type u) [TopologicalSpace X] : Cardinal.{u} :=
  sInf {c | ∃ s : Set X, Dense s ∧ #s = c}

/-- The density character is at most `m` iff some dense subset has cardinality at most `m`. -/
theorem densityCharacter_le_iff {X : Type u} [TopologicalSpace X] {m : Cardinal.{u}} :
    densityCharacter X ≤ m ↔ ∃ s : Set X, Dense s ∧ #s ≤ m := by
  constructor
  · intro h
    have hne : {c | ∃ s : Set X, Dense s ∧ #s = c}.Nonempty := ⟨#(univ : Set X), univ, dense_univ, rfl⟩
    obtain ⟨s, hs, hseq⟩ := csInf_mem hne
    have h' : #s = densityCharacter X := hseq
    exact ⟨s, hs, h' ▸ h⟩
  · rintro ⟨s, hs, hsm⟩
    have hmem : #s ∈ {c | ∃ s : Set X, Dense s ∧ #s = c} := ⟨s, hs, rfl⟩
    exact (csInf_le' hmem).trans hsm

theorem densityCharacter_le_card (X : Type u) [TopologicalSpace X] : densityCharacter X ≤ #X := by
  rw [densityCharacter_le_iff]
  exact ⟨univ, dense_univ, by simp⟩

theorem densityCharacter_le_of_finite (X : Type u) [TopologicalSpace X] [Finite X]
    {m : Cardinal.{u}} (hm : ℵ₀ ≤ m) : densityCharacter X ≤ m :=
  (densityCharacter_le_card X).trans (Cardinal.mk_lt_aleph0.le.trans hm)

/-- Morris, Topology Without Tears, Definition 10.3.37 (TP-301), remark after it: a space is
separable iff its density character is at most `ℵ₀`. -/
@[kb "morris2024" "Definition 10.3.37, p. 289"]
theorem separableSpace_iff_densityCharacter_le (X : Type u) [TopologicalSpace X] :
    TopologicalSpace.SeparableSpace X ↔ densityCharacter X ≤ ℵ₀ := by
  rw [densityCharacter_le_iff]
  constructor
  · intro h
    obtain ⟨s, hs, hd⟩ := h.exists_countable_dense
    exact ⟨s, hd, Cardinal.mk_le_aleph0_iff.mpr hs.to_subtype⟩
  · rintro ⟨s, hs, hle⟩
    exact ⟨⟨s, Set.countable_coe_iff.mp (Cardinal.mk_le_aleph0_iff.mp hle), hs⟩⟩

/-- A nonempty space has density character at most `m` iff it receives a map from `m.out` with
dense range. -/
theorem densityCharacter_le_iff_exists_denseRange {X : Type u} [TopologicalSpace X] [Nonempty X]
    {m : Cardinal.{u}} : densityCharacter X ≤ m ↔ ∃ f : m.out → X, DenseRange f := by
  rw [densityCharacter_le_iff]
  constructor
  · rintro ⟨s, hs, hsm⟩
    haveI : Nonempty s := hs.nonempty.to_subtype
    obtain ⟨emb⟩ := (Cardinal.le_def s m.out).mp (by rwa [Cardinal.mk_out])
    have hg : Function.Surjective (Function.invFun emb) :=
      Function.invFun_surjective emb.injective
    refine ⟨Subtype.val ∘ Function.invFun emb, ?_⟩
    rw [DenseRange, hg.range_comp, Subtype.range_coe]
    exact hs
  · rintro ⟨f, hf⟩
    exact ⟨range f, hf, Cardinal.mk_range_le.trans (Cardinal.mk_out m).le⟩

/-! ### The Hewitt-Marczewski-Pondiczery theorem and its precursors -/

/-- Morris, Topology Without Tears, Theorem 10.3.41 (Hewitt-Marczewski-Pondiczery) (TP-304).  Let
`m` be an infinite cardinal, `ι` an index set of cardinality at most `2^m`, and `X i` spaces of
density character at most `m`.  Then the product has density character at most `m`. -/
@[kb "morris2024" "Theorem 10.3.41, p. 290"]
theorem densityCharacter_pi_le {m : Cardinal.{u}} (hm : ℵ₀ ≤ m) {ι : Type u}
    (hι : #ι ≤ 2 ^ m) (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    (hX : ∀ i, densityCharacter (X i) ≤ m) : densityCharacter (∀ i, X i) ≤ m := by
  by_cases hne : ∀ i, Nonempty (X i)
  · haveI : Infinite m.out := Cardinal.infinite_iff.mpr (by rwa [Cardinal.mk_out])
    have hle : #ι ≤ #(Set m.out) := by
      rw [Cardinal.mk_set, Cardinal.mk_out]
      exact hι
    obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hle
    have hψ : ∀ i, ∃ ψ : m.out → X i, DenseRange ψ := fun i => by
      haveI := hne i
      exact densityCharacter_le_iff_exists_denseRange.mp (hX i)
    choose ψ hψ using hψ
    obtain ⟨f, hf⟩ := exists_denseRange_pi e ψ hψ
    exact densityCharacter_le_iff.mpr ⟨range f, hf, Cardinal.mk_range_le.trans (Cardinal.mk_out m).le⟩
  · obtain ⟨i, hi⟩ := not_forall.mp hne
    haveI : IsEmpty (X i) := not_nonempty_iff.mp hi
    haveI : IsEmpty (∀ i, X i) := ⟨fun x => isEmptyElim (x i)⟩
    exact densityCharacter_le_iff.mpr ⟨∅, dense_of_isEmpty' _, by simp⟩

/-- Morris, Topology Without Tears, Theorem 10.3.41 (TP-304), the "in particular" part: a power
`X^(2^m)` of a space of density character at most `m` has density character at most `m`. -/
@[kb "morris2024" "Theorem 10.3.41, p. 290"]
theorem densityCharacter_pow_le {m : Cardinal.{u}} (hm : ℵ₀ ≤ m) {ι : Type u}
    (hι : #ι ≤ 2 ^ m) (X : Type u) [TopologicalSpace X] (hX : densityCharacter X ≤ m) :
    densityCharacter (ι → X) ≤ m :=
  densityCharacter_pi_le hm hι (fun _ => X) (fun _ => hX)

/-- Morris, Topology Without Tears, Proposition 10.3.36 and Proposition 10.3.38 (TP-300). For an
infinite cardinal `m`, the product `{0,1}^(2^m)` has density character at most `m`; in other
words it has a dense subset of cardinality at most `m`. -/
@[kb "morris2024" "Proposition 10.3.38, p. 289"]
theorem densityCharacter_bool_pow_le {m : Cardinal.{0}} (hm : ℵ₀ ≤ m) {ι : Type}
    (hι : #ι ≤ 2 ^ m) : densityCharacter (ι → Bool) ≤ m :=
  densityCharacter_pow_le hm hι Bool (densityCharacter_le_of_finite Bool hm)

/-- Morris, Topology Without Tears, Proposition 10.3.36 (TP-300), the form with an explicit dense
subset: `{0,1}^(Set M)` has a dense subset of cardinality at most `#M`, for an infinite type `M`. -/
@[kb "morris2024" "Proposition 10.3.36, p. 288"]
theorem exists_dense_card_le_bool_pow (M : Type) [Infinite M] :
    ∃ D : Set (Set M → Bool), Dense D ∧ #D ≤ #M := by
  obtain ⟨f, hf⟩ := exists_denseRange_bool_pow (M := M) (ι := Set M) id Function.injective_id
  exact ⟨range f, hf, Cardinal.mk_range_le⟩

/-- Morris, Topology Without Tears, Corollary 10.3.39 (TP-302). For an infinite cardinal `m` and a
finite discrete space `F`, the product of `2^m` copies of `F` has density character at most `m`. -/
@[kb "morris2024" "Corollary 10.3.39, p. 289"]
theorem densityCharacter_finite_pow_le {m : Cardinal.{u}} (hm : ℵ₀ ≤ m) {ι : Type u}
    (hι : #ι ≤ 2 ^ m) (F : Type u) [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    densityCharacter (ι → F) ≤ m :=
  densityCharacter_pow_le hm hι F (densityCharacter_le_of_finite F hm)

/-- Morris, Topology Without Tears, Proposition 10.3.40 (TP-303). A discrete space `D` of
cardinality at most `m` (`m` infinite) has `D^(2^m)` of density character at most `m`. -/
@[kb "morris2024" "Proposition 10.3.40, p. 289"]
theorem densityCharacter_discrete_pow_le {m : Cardinal.{u}} (hm : ℵ₀ ≤ m) {ι : Type u}
    (hι : #ι ≤ 2 ^ m) (D : Type u) [TopologicalSpace D] [DiscreteTopology D] (hD : #D ≤ m) :
    densityCharacter (ι → D) ≤ m :=
  densityCharacter_pow_le hm hι D ((densityCharacter_le_card D).trans hD)

/-- Morris, Topology Without Tears, Corollary 10.3.42 (TP-305). If `X` is separable and `ι` has at
most the cardinality of the continuum, then `X^ι` is separable. -/
@[kb "morris2024" "Corollary 10.3.42, p. 290"]
theorem separableSpace_pi_of_card_le_continuum (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] {ι : Type} (hι : #ι ≤ 𝔠) :
    TopologicalSpace.SeparableSpace (ι → X) := by
  rcases isEmpty_or_nonempty ι with hι' | hι'
  · infer_instance
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : IsEmpty (ι → X) := ⟨fun f => isEmptyElim (f (Classical.choice hι'))⟩
    infer_instance
  have hle : #ι ≤ #(Set ℕ) := by
    rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0]
    exact hι
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hle
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨f, hf⟩ := exists_denseRange_pi (M := ℕ) e (fun _ => u) (fun _ => hu)
  exact ⟨⟨range f, countable_range f, hf⟩⟩

/-- Morris, Topology Without Tears, Corollary 10.3.42 (TP-305), as stated in the book: if `X` is
separable then so is `X^𝔠`, here with the real line as index set of size `𝔠`. -/
@[kb "morris2024" "Corollary 10.3.42, p. 290"]
theorem separableSpace_real_pow (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] : TopologicalSpace.SeparableSpace (ℝ → X) :=
  separableSpace_pi_of_card_le_continuum X (le_of_eq Cardinal.mk_real)

/-- Morris, Topology Without Tears, Corollary 10.3.42 (TP-305), the "in particular" part: the
product `ℝ^𝔠`, i.e. the space of all functions `ℝ → ℝ`, is separable. -/
@[kb "morris2024" "Corollary 10.3.42, p. 290"]
theorem separableSpace_real_pow_real : TopologicalSpace.SeparableSpace (ℝ → ℝ) :=
  separableSpace_real_pow ℝ

end UndergradKB.Topology
