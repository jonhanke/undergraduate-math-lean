import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Data.Fintype.Pi
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.ProblemsGroups

namespace UndergradKB.RepresentationTheory

section Count

/-- Integer-type root parameters: coordinates in `{-1,0,1}` (stored in `Fin 3` shifted by `1`)
with squared norm `2`. -/
def e8P1 (f : Fin 8 → Fin 3) : Prop := ∑ i, (((f i : ℕ) : ℤ) - 1) ^ 2 = 2

instance : DecidablePred e8P1 := fun f => by unfold e8P1; infer_instance

/-- Half-integer-type root parameters: signs of the coordinates `±1/2`, with `Σ 2vᵢ ≡ 0 (mod 4)`. -/
def e8P2 (g : Fin 8 → Bool) : Prop := (∑ i, (if g i then (1 : ℤ) else -1)) % 4 = 0

instance : DecidablePred e8P2 := fun g => by unfold e8P2; infer_instance

theorem card_P1 : (Finset.univ.filter fun f : Fin 8 → Fin 3 => e8P1 f).card = 112 := by
  decide +kernel

theorem card_P2 : (Finset.univ.filter fun g : Fin 8 → Bool => e8P2 g).card = 128 := by
  decide +kernel

theorem even_P1 (f : Fin 8 → Fin 3) (hf : e8P1 f) : (∑ i, (((f i : ℕ) : ℤ) - 1)) % 2 = 0 := by
  have h1 : (∑ i, (((f i : ℕ) : ℤ) - 1)) % 2 = (∑ i, (((f i : ℕ) : ℤ) - 1) ^ 2) % 2 := by
    rw [Finset.sum_int_mod, Finset.sum_int_mod (f := fun i => (((f i : ℕ) : ℤ) - 1) ^ 2)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize (((f i : ℕ) : ℤ) - 1) = z
    rcases Int.emod_two_eq_zero_or_one z with h | h <;> simp [pow_two, Int.mul_emod, h]
  rw [h1]
  unfold e8P1 at hf
  rw [hf]; rfl

/-- The integer-type root with parameters `f`. -/
def e8Phi1 (f : Fin 8 → Fin 3) : Fin 8 → ℚ := fun i => ((((f i : ℕ) : ℤ) - 1 : ℤ) : ℚ)

/-- The half-integer-type root with sign pattern `g`. -/
def e8Phi2 (g : Fin 8 → Bool) : Fin 8 → ℚ := fun i => if g i then 1 / 2 else -1 / 2

theorem e8Phi1_injective : Function.Injective e8Phi1 := by
  intro f f' h
  funext i
  have := congrFun h i
  simp only [e8Phi1, Int.cast_inj] at this
  exact Fin.ext (by omega)

theorem e8Phi2_injective : Function.Injective e8Phi2 := by
  intro g g' h
  funext i
  have := congrFun h i
  simp only [e8Phi2] at this
  cases hg : g i <;> cases hg' : g' i <;> simp [hg, hg'] at this ⊢ <;> norm_num at this

/-- The roots of `E₈`: vectors of the lattice `L` of squared length `2`. -/
def E8Root : Set (Fin 8 → ℚ) := {v | v ∈ E8Lattice ∧ ∑ i, v i ^ 2 = 2}

theorem e8Root_eq :
    E8Root = e8Phi1 '' {f | e8P1 f} ∪ e8Phi2 '' {g | e8P2 g} := by
  ext v
  constructor
  · rintro ⟨⟨hv | hv, s, hs⟩, hn⟩
    · left
      choose z hz using hv
      have hz2 : ∑ i, z i ^ 2 = 2 := by
        have : ((∑ i, z i ^ 2 : ℤ) : ℚ) = 2 := by
          push_cast; rw [← hn]; exact Finset.sum_congr rfl fun i _ => by rw [hz i]
        exact_mod_cast this
      have hb : ∀ i, -1 ≤ z i ∧ z i ≤ 1 := by
        intro i
        have h1 : z i ^ 2 ≤ 2 := by
          rw [← hz2]
          exact Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)
        constructor <;> nlinarith
      refine ⟨fun i => ⟨(z i + 1).toNat, by have := hb i; omega⟩, ?_, ?_⟩
      · show e8P1 _
        unfold e8P1
        rw [← hz2]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hb i
        congr 1
        simp only [Fin.val_mk]
        omega
      · funext i
        simp only [e8Phi1, Fin.val_mk]
        rw [hz i]
        have := hb i
        congr 1
        omega
    · right
      choose z hz using hv
      have hz2 : ∑ i, (2 * z i + 1) ^ 2 = 8 := by
        have : ((∑ i, (2 * z i + 1) ^ 2 : ℤ) : ℚ) = 8 := by
          push_cast
          have : ∑ i, ((2 * (z i : ℚ) + 1) ^ 2) = 4 * ∑ i, v i ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hz i]; ring
          rw [this, hn]; norm_num
        exact_mod_cast this
      have hzero : ∑ i, ((2 * z i + 1) ^ 2 - 1) = 0 := by
        rw [Finset.sum_sub_distrib, hz2]; simp
      have hz01 : ∀ i, z i = 0 ∨ z i = -1 := by
        intro i
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ (2 * z j + 1) ^ 2 - 1 := fun j _ => by
          rcases le_or_gt 0 (z j) with h | h <;> nlinarith
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero i (Finset.mem_univ i)
        have h2 : z i * (z i + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 h2 with h | h
        · left; exact h
        · right; omega
      have key : ∀ i, (((if decide (z i = 0) = true then (1 : ℤ) else -1 : ℤ)) : ℚ) = 2 * v i := by
        intro i
        rw [hz i]
        rcases hz01 i with h | h <;> simp [h] <;> norm_num
      refine ⟨fun i => decide (z i = 0), ?_, ?_⟩
      · show e8P2 _
        unfold e8P2
        have h4 : (∑ i, (if decide (z i = 0) = true then (1 : ℤ) else -1) : ℤ) = 4 * s := by
          have : (((∑ i, (if decide (z i = 0) = true then (1 : ℤ) else -1) : ℤ)) : ℚ) = 4 * s := by
            rw [Int.cast_sum, Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum, hs]; ring
          exact_mod_cast this
        show (∑ i, (if decide (z i = 0) = true then (1 : ℤ) else -1)) % 4 = 0
        rw [h4]; omega
      · funext i
        simp only [e8Phi2]
        rw [hz i]
        rcases hz01 i with h | h <;> simp [h] <;> norm_num
  · rintro (⟨f, hf, rfl⟩ | ⟨g, hg, rfl⟩)
    · have hf' : e8P1 f := hf
      refine ⟨⟨Or.inl fun i => ⟨_, rfl⟩, ?_⟩, ?_⟩
      · have := even_P1 f hf'
        refine ⟨(∑ i, (((f i : ℕ) : ℤ) - 1)) / 2, ?_⟩
        have h2 : (∑ i, (((f i : ℕ) : ℤ) - 1)) = 2 * ((∑ i, (((f i : ℕ) : ℤ) - 1)) / 2) := by omega
        have : (∑ i, e8Phi1 f i) = ((∑ i, (((f i : ℕ) : ℤ) - 1) : ℤ) : ℚ) := by
          simp [e8Phi1]
        rw [this]
        exact_mod_cast h2
      · have : ((∑ i, (((f i : ℕ) : ℤ) - 1) ^ 2 : ℤ) : ℚ) = 2 := by
          unfold e8P1 at hf'; rw [hf']; norm_num
        push_cast at this
        simpa [e8Phi1] using this
    · have hg' : e8P2 g := hg
      have key : ∀ i, e8Phi2 g i = (((if g i then (1 : ℤ) else -1 : ℤ)) : ℚ) / 2 := by
        intro i; unfold e8Phi2; split_ifs <;> norm_num
      refine ⟨⟨Or.inr fun i => ?_, ?_⟩, ?_⟩
      · by_cases h : g i
        · exact ⟨0, by simp [e8Phi2, h]⟩
        · exact ⟨-1, by simp [e8Phi2, h]; norm_num⟩
      · unfold e8P2 at hg'
        have h4 : (∑ i, (if g i then (1 : ℤ) else -1)) = 4 * ((∑ i, (if g i then (1 : ℤ) else -1)) / 4) := by
          omega
        refine ⟨(∑ i, (if g i then (1 : ℤ) else -1)) / 4, ?_⟩
        have : (∑ i, e8Phi2 g i) = ((∑ i, (if g i then (1 : ℤ) else -1) : ℤ) : ℚ) / 2 := by
          rw [Int.cast_sum, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => key i
        rw [this]
        conv_lhs => rw [h4]
        push_cast
        ring
      · have : ∀ i, e8Phi2 g i ^ 2 = 1 / 4 := by
          intro i; unfold e8Phi2; split_ifs <;> norm_num
        rw [Finset.sum_congr rfl fun i _ => this i]
        simp; norm_num

theorem e8Phi_disjoint (f : Fin 8 → Fin 3) (g : Fin 8 → Bool) : e8Phi1 f ≠ e8Phi2 g := by
  intro h
  have := congrFun h 0
  simp only [e8Phi1, e8Phi2] at this
  generalize (((f 0 : ℕ) : ℤ) - 1) = z at this
  cases hg : g 0 <;> simp only [hg] at this <;> norm_num at this
  · have h2 : ((2 * z : ℤ) : ℚ) = -1 := by push_cast; linarith
    have : 2 * z = -1 := by exact_mod_cast h2
    omega
  · have h2 : ((2 * z : ℤ) : ℚ) = 1 := by push_cast; linarith
    have : 2 * z = 1 := by exact_mod_cast h2
    omega

theorem ncard_root_filter (Q : (Fin 8 → ℚ) → Prop) (Q₁ : (Fin 8 → Fin 3) → Prop)
    (Q₂ : (Fin 8 → Bool) → Prop) [DecidablePred Q₁] [DecidablePred Q₂]
    (h₁ : ∀ f, Q (e8Phi1 f) ↔ Q₁ f) (h₂ : ∀ g, Q (e8Phi2 g) ↔ Q₂ g) :
    {v | v ∈ E8Root ∧ Q v}.ncard =
      (Finset.univ.filter fun f => e8P1 f ∧ Q₁ f).card +
        (Finset.univ.filter fun g => e8P2 g ∧ Q₂ g).card := by
  have hset : {v | v ∈ E8Root ∧ Q v} =
      e8Phi1 '' ((Finset.univ.filter fun f => e8P1 f ∧ Q₁ f : Finset _) : Set _) ∪
        e8Phi2 '' ((Finset.univ.filter fun g => e8P2 g ∧ Q₂ g : Finset _) : Set _) := by
    ext v
    simp only [Set.mem_setOf_eq, e8Root_eq, Set.mem_union, Set.mem_image, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨(⟨f, hf, rfl⟩ | ⟨g, hg, rfl⟩), hQ⟩
      · exact Or.inl ⟨f, ⟨hf, (h₁ f).1 hQ⟩, rfl⟩
      · exact Or.inr ⟨g, ⟨hg, (h₂ g).1 hQ⟩, rfl⟩
    · rintro (⟨f, ⟨hf, hq⟩, rfl⟩ | ⟨g, ⟨hg, hq⟩, rfl⟩)
      · exact ⟨Or.inl ⟨f, hf, rfl⟩, (h₁ f).2 hq⟩
      · exact ⟨Or.inr ⟨g, hg, rfl⟩, (h₂ g).2 hq⟩
  rw [hset, Set.ncard_union_eq, Set.ncard_image_of_injective _ e8Phi1_injective,
    Set.ncard_image_of_injective _ e8Phi2_injective, Set.ncard_coe_finset, Set.ncard_coe_finset]
  · rw [Set.disjoint_left]
    rintro _ ⟨f, _, rfl⟩ ⟨g, _, h⟩
    exact e8Phi_disjoint f g h.symm

/-- Problem 5.40(d): `E₈` has `240` roots. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem E8Root_ncard : E8Root.ncard = 240 := by
  have := ncard_root_filter (fun _ => True) (fun _ => True) (fun _ => True)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  simp only [and_true, Set.setOf_mem_eq] at this
  rw [this, card_P1, card_P2]

/-- The roots of `E₇`: roots of `E₈` whose first two coordinates agree. -/
def E7Root : Set (Fin 8 → ℚ) := {v | v ∈ E8Root ∧ v 0 = v 1}

/-- The roots of `E₆`: roots of `E₈` whose first three coordinates agree. -/
def E6Root : Set (Fin 8 → ℚ) := {v | v ∈ E8Root ∧ v 0 = v 1 ∧ v 1 = v 2}

theorem card_P1_E7 :
    (Finset.univ.filter fun f : Fin 8 → Fin 3 => e8P1 f ∧ f 0 = f 1).card = 62 := by
  decide +kernel

theorem card_P2_E7 :
    (Finset.univ.filter fun g : Fin 8 → Bool => e8P2 g ∧ g 0 = g 1).card = 64 := by
  decide +kernel

theorem card_P1_E6 :
    (Finset.univ.filter fun f : Fin 8 → Fin 3 => e8P1 f ∧ (f 0 = f 1 ∧ f 1 = f 2)).card = 40 := by
  decide +kernel

theorem card_P2_E6 :
    (Finset.univ.filter fun g : Fin 8 → Bool => e8P2 g ∧ (g 0 = g 1 ∧ g 1 = g 2)).card = 32 := by
  decide +kernel

/-- Problem 5.40(d): `E₇` has `126` roots. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem E7Root_ncard : E7Root.ncard = 126 := by
  have := ncard_root_filter (fun v => v 0 = v 1) (fun f => f 0 = f 1) (fun g => g 0 = g 1)
    (fun f => by
      simp only [e8Phi1, Int.cast_inj]
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; rw [h])
    (fun g => by
      simp only [e8Phi2]
      cases g 0 <;> cases g 1 <;> norm_num)
  unfold E7Root
  rw [this, card_P1_E7, card_P2_E7]

/-- Problem 5.40(d): `E₆` has `72` roots. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem E6Root_ncard : E6Root.ncard = 72 := by
  have := ncard_root_filter (fun v => v 0 = v 1 ∧ v 1 = v 2) (fun f => f 0 = f 1 ∧ f 1 = f 2)
    (fun g => g 0 = g 1 ∧ g 1 = g 2)
    (fun f => by
      simp only [e8Phi1, Int.cast_inj]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · rintro ⟨h, h'⟩; rw [h, h']; exact ⟨rfl, rfl⟩)
    (fun g => by
      simp only [e8Phi2]
      cases g 0 <;> cases g 1 <;> cases g 2 <;> norm_num)
  unfold E6Root
  rw [this, card_P1_E6, card_P2_E6]

end Count

section RootSystem

/-- The relabelling of the simple roots `α₁, …, α₈` (indexed from `0`) matching the node order of
Mathlib's `CartanMatrix.E 8` (branch node `3`, arms `{1}`, `{2, 0}`, `{4, 5, 6, 7}`). -/
def e8Perm : Fin 8 → Fin 8 := ![7, 6, 5, 4, 3, 1, 2, 0]

/-- Problem 5.40(b): the Gram matrix of the simple roots `α₁, …, α₈` is the Cartan matrix of type
`E₈` (after the node relabelling `e8Perm`). -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e8Simple_gram (i j : Fin 8) :
    e8Simple i ⬝ᵥ e8Simple j = ((CartanMatrix.E 8 (e8Perm i) (e8Perm j) : ℤ) : ℚ) := by
  rw [CartanMatrix.E_eight_eq]
  fin_cases i <;> fin_cases j <;>
    simp [dotProduct, e8Simple, e8Perm, Fin.sum_univ_succ] <;> norm_num

theorem e8Simple_mem_root (i : Fin 8) : e8Simple i ∈ E8Root := by
  refine ⟨?_, ?_⟩
  · have := e8_comb_mem (Pi.single i 1)
    simpa [Pi.single_apply] using this
  · have h := e8Simple_gram i i
    rw [CartanMatrix.E_eight_eq] at h
    have h2 : e8Simple i ⬝ᵥ e8Simple i = 2 := by
      rw [h]; fin_cases i <;> simp [e8Perm]
    simpa [dotProduct, sq] using h2

theorem inner_int {v w : Fin 8 → ℚ} (hv : v ∈ E8Lattice) (hw : w ∈ E8Lattice) :
    ∃ n : ℤ, v ⬝ᵥ w = n := by
  obtain ⟨c, hc⟩ := (e8Simple_isBasis.2 v hv).exists
  obtain ⟨d, hd⟩ := (e8Simple_isBasis.2 w hw).exists
  refine ⟨∑ i, ∑ j, c i * d j * CartanMatrix.E 8 (e8Perm i) (e8Perm j), ?_⟩
  rw [hc, hd, sum_dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_dotProduct, dotProduct_smul, e8Simple_gram]
  simp only [zsmul_eq_mul, smul_eq_mul]
  ring

theorem lattice_sub_zsmul {v w : Fin 8 → ℚ} (hv : v ∈ E8Lattice) (hw : w ∈ E8Lattice) (n : ℤ) :
    v - n • w ∈ E8Lattice := by
  obtain ⟨c, hc⟩ := (e8Simple_isBasis.2 v hv).exists
  obtain ⟨d, hd⟩ := (e8Simple_isBasis.2 w hw).exists
  have : v - n • w = ∑ i, (c i - n * d i) • e8Simple i := by
    rw [hc, hd]
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
  rw [this]
  exact e8_comb_mem _

/-- Problem 5.40(b): the roots are closed under the reflections `s_w(v) = v - (v, w) w`, and the
pairings `(v, w)` are integers. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e8Root_reflect {v w : Fin 8 → ℚ} (hv : v ∈ E8Root) (hw : w ∈ E8Root) :
    ∃ n : ℤ, v ⬝ᵥ w = n ∧ v - n • w ∈ E8Root := by
  obtain ⟨n, hn⟩ := inner_int hv.1 hw.1
  refine ⟨n, hn, lattice_sub_zsmul hv.1 hw.1 n, ?_⟩
  have hvv : v ⬝ᵥ v = 2 := by simpa [dotProduct, sq] using hv.2
  have hww : w ⬝ᵥ w = 2 := by simpa [dotProduct, sq] using hw.2
  have : (v - n • w) ⬝ᵥ (v - n • w) = 2 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, hvv, hww, dotProduct_comm w v, hn]
    simp only [zsmul_eq_mul, smul_eq_mul]
    ring
  simpa [dotProduct, sq] using this

theorem e8Root_neg {v : Fin 8 → ℚ} (hv : v ∈ E8Root) : -v ∈ E8Root := by
  obtain ⟨n, hn, hmem⟩ := e8Root_reflect hv hv
  have hvv : v ⬝ᵥ v = 2 := by simpa [dotProduct, sq] using hv.2
  have : (n : ℚ) = 2 := by rw [← hn, hvv]
  have hn2 : n = 2 := by exact_mod_cast this
  subst hn2
  have : v - (2 : ℤ) • v = -v := by
    funext i; simp; ring
  rwa [this] at hmem

theorem e8Root_finite : E8Root.Finite := by
  rw [e8Root_eq]
  exact (Set.toFinite _ |>.image _).union (Set.toFinite _ |>.image _)

theorem e8Root_zspan (v : Fin 8 → ℚ) (hv : v ∈ E8Root) :
    ∃ c : Fin 8 → ℤ, v = ∑ i, c i • e8Simple i :=
  (e8Simple_isBasis.2 v hv.1).exists

theorem e8Root_span : Submodule.span ℚ E8Root = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hsimple : ∀ i, e8Simple i ∈ Submodule.span ℚ E8Root := fun i =>
    Submodule.subset_span (e8Simple_mem_root i)
  have hmem : ∀ i : Fin 8, (Pi.single i (2 : ℚ)) ∈ Submodule.span ℚ E8Root := by
    intro i
    have hL : (Pi.single i (2 : ℚ) : Fin 8 → ℚ) ∈ E8Lattice := by
      refine ⟨Or.inl fun j => ⟨if j = i then 2 else 0, ?_⟩, 1, ?_⟩
      · by_cases h : j = i <;> simp [Pi.single_apply, h]
      · simp
    obtain ⟨c, hc⟩ := (e8Simple_isBasis.2 _ hL).exists
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => by
      rw [← Int.cast_smul_eq_zsmul ℚ]
      exact Submodule.smul_mem _ _ (hsimple j)
  have hx : x = ∑ i, (x i / 2) • (Pi.single i (2 : ℚ) : Fin 8 → ℚ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)

end RootSystem

section SubSystems

/-- Simple roots of `E₇` (inside the sublattice `v₀ = v₁`): `α₃, α₄, α₅, α₆, α₇, α₈` and `e₁ + e₂`. -/
def e7Simple : Fin 7 → Fin 8 → ℚ := ![
  ![0, 0, 1, -1, 0, 0, 0, 0], ![0, 0, 0, 1, -1, 0, 0, 0], ![0, 0, 0, 0, 1, -1, 0, 0],
  ![0, 0, 0, 0, 0, 1, -1, 0], ![0, 0, 0, 0, 0, 1, 1, 0],
  ![-1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2], ![1, 1, 0, 0, 0, 0, 0, 0]]

/-- Node relabelling matching `CartanMatrix.E 7`. -/
def e7Perm : Fin 7 → Fin 7 := ![0, 2, 3, 1, 4, 5, 6]

/-- Simple roots of `E₆` (inside the sublattice `v₀ = v₁ = v₂`). -/
def e6Simple : Fin 6 → Fin 8 → ℚ := ![
  ![0, 0, 0, 1, -1, 0, 0, 0], ![0, 0, 0, 0, 1, -1, 0, 0], ![0, 0, 0, 0, 0, 1, -1, 0],
  ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, -1],
  ![1 / 2, 1 / 2, 1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, 1 / 2]]

/-- Node relabelling matching `CartanMatrix.E 6`. -/
def e6Perm : Fin 6 → Fin 6 := ![0, 2, 3, 1, 4, 5]

/-- Problem 5.40(c): the Gram matrix of `e7Simple` is the `E₇` Cartan matrix. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e7Simple_gram (i j : Fin 7) :
    e7Simple i ⬝ᵥ e7Simple j = ((CartanMatrix.E 7 (e7Perm i) (e7Perm j) : ℤ) : ℚ) := by
  rw [CartanMatrix.E_seven_eq]
  fin_cases i <;> fin_cases j <;>
    simp [dotProduct, e7Simple, e7Perm, Fin.sum_univ_succ] <;> norm_num

/-- Problem 5.40(c): the Gram matrix of `e6Simple` is the `E₆` Cartan matrix. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e6Simple_gram (i j : Fin 6) :
    e6Simple i ⬝ᵥ e6Simple j = ((CartanMatrix.E 6 (e6Perm i) (e6Perm j) : ℤ) : ℚ) := by
  rw [CartanMatrix.E_six_eq]
  fin_cases i <;> fin_cases j <;>
    simp [dotProduct, e6Simple, e6Perm, Fin.sum_univ_succ] <;> norm_num

theorem mem_lattice_of_comb {v : Fin 8 → ℚ} (c : Fin 8 → ℤ) (h : v = ∑ i, c i • e8Simple i) :
    v ∈ E8Lattice := h ▸ e8_comb_mem c

/-- The `E₇` simple roots are roots of `E₈` with equal first two coordinates. -/
theorem e7Simple_mem (i : Fin 7) : e7Simple i ∈ E7Root := by
  have hL : e7Simple i ∈ E8Lattice := by
    fin_cases i
    · exact mem_lattice_of_comb ![0, 0, 1, 0, 0, 0, 0, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 1, 0, 0, 0, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 1, 0, 0, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 0, 1, 0, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 0, 0, 1, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 0, 0, 0, 1] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![1, 2, 2, 2, 2, 1, 1, 0] (by
        funext j; fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ] <;> norm_num)
  have hn : ∑ k, e7Simple i k ^ 2 = 2 := by
    have h := e7Simple_gram i i
    rw [CartanMatrix.E_seven_eq] at h
    have h2 : e7Simple i ⬝ᵥ e7Simple i = 2 := by
      rw [h]; fin_cases i <;> simp [e7Perm]
    simpa [dotProduct, sq] using h2
  refine ⟨⟨hL, hn⟩, ?_⟩
  fin_cases i <;> simp [e7Simple]

/-- The `E₆` simple roots are roots of `E₈` with equal first three coordinates. -/
theorem e6Simple_mem (i : Fin 6) : e6Simple i ∈ E6Root := by
  have hL : e6Simple i ∈ E8Lattice := by
    fin_cases i
    · exact mem_lattice_of_comb ![0, 0, 0, 1, 0, 0, 0, 0] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 1, 0, 0, 0] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![0, 0, 0, 0, 0, 1, 0, 0] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ])
    · exact mem_lattice_of_comb ![-1, -2, -3, -4, -5, -3, -3, -2] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ] <;> norm_num)
    · exact mem_lattice_of_comb ![1, 2, 3, 4, 5, 2, 4, 2] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ] <;> norm_num)
    · exact mem_lattice_of_comb ![0, 0, 0, -1, -2, -1, -2, -1] (by
        funext j; fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ] <;> norm_num)
  have hn : ∑ k, e6Simple i k ^ 2 = 2 := by
    have h := e6Simple_gram i i
    rw [CartanMatrix.E_six_eq] at h
    have h2 : e6Simple i ⬝ᵥ e6Simple i = 2 := by
      rw [h]; fin_cases i <;> simp [e6Perm]
    simpa [dotProduct, sq] using h2
  refine ⟨⟨hL, hn⟩, ?_⟩
  fin_cases i <;> simp [e6Simple]

/-- Problem 5.40(c): every vector of the lattice `L` with equal first two coordinates (the `E₇`
lattice) is an integer combination of the `E₇` simple roots. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e7_lattice_span {v : Fin 8 → ℚ} (hv : v ∈ E8Lattice) (h01 : v 0 = v 1) :
    ∃ d : Fin 7 → ℤ, v = ∑ i, d i • e7Simple i := by
  obtain ⟨c, hc⟩ := (e8Simple_isBasis.2 v hv).exists
  obtain ⟨h0, h1, -, -, -, -, -, -⟩ := e8_comb_apply c
  rw [hc, h0, h1] at h01
  have hc1 : (c 1 : ℚ) = 2 * c 0 := by linarith
  refine ⟨![c 2 - 2 * c 0, c 3 - 2 * c 0, c 4 - 2 * c 0, c 5 - c 0, c 6 - c 0, c 7, c 0], ?_⟩
  rw [hc]
  funext j
  fin_cases j <;> simp [e7Simple, e8Simple, Fin.sum_univ_succ] <;> push_cast <;> linarith

/-- Problem 5.40(c): every vector of the lattice `L` with equal first three coordinates (the `E₆`
lattice) is an integer combination of the `E₆` simple roots. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
theorem e6_lattice_span {v : Fin 8 → ℚ} (hv : v ∈ E8Lattice) (h01 : v 0 = v 1) (h12 : v 1 = v 2) :
    ∃ d : Fin 6 → ℤ, v = ∑ i, d i • e6Simple i := by
  obtain ⟨c, hc⟩ := (e8Simple_isBasis.2 v hv).exists
  obtain ⟨h0, h1, h2, -, -, -, -, -⟩ := e8_comb_apply c
  rw [hc, h0, h1] at h01
  rw [hc, h1, h2] at h12
  have hc1 : (c 1 : ℚ) = 2 * c 0 := by linarith
  have hc2 : (c 2 : ℚ) = 3 * c 0 := by linarith
  refine ⟨![c 3 - 2 * c 0 - c 7, c 4 - c 0 - 2 * c 7, c 5 + c 6 - 3 * c 7, c 6 - 2 * c 7,
    c 0 + c 6 - 2 * c 7, 2 * c 0 - c 7], ?_⟩
  rw [hc]
  funext j
  fin_cases j <;> simp [e6Simple, e8Simple, Fin.sum_univ_succ] <;> push_cast <;> linarith

end SubSystems

end UndergradKB.RepresentationTheory
