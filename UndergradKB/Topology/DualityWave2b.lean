import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-!
# A compact neighbourhood of the identity in the dual group (Morris, Appendix 5, A5.7.6 and A5.7.7)

For a locally compact abelian group `G`, a compact neighbourhood `K` of `1` and a small arc `V_a`
around `1` in the circle, the set `P(K, V_a)` of characters mapping `K` into `V_a` is an open
neighbourhood of `1` in the dual group whose closure is compact.  The proof follows Mathlib's proof
that the dual is locally compact (`PontryaginDual.instLocallyCompactSpace`), keeping track of the
compact set: equicontinuity by the halving argument, then the Arzela-Ascoli theorem.
-/

open Set Filter Topology Real Pointwise

namespace UndergradKB.Topology

section Equicontinuity

variable {X : Type*} [TopologicalSpace X] [Group X] [IsTopologicalGroup X]

/-- The compact set `{f | f(U) ⊆ W}` of continuous homomorphisms into a compact uniform group
(extracted from Mathlib's proof of local compactness of `ContinuousMonoidHom X Y`). -/
theorem isCompact_mapsTo_of_equicontinuousAt
    {Y : Type*} [UniformSpace Y] [CommGroup Y] [IsUniformGroup Y] [T0Space Y] [CompactSpace Y]
    (U : Set X) (V W : Set Y) (hU : IsCompact U) (hWc : IsCompact W) (hWV : W ⊆ V)
    (h : EquicontinuousAt (fun f : {f : X →* Y | Set.MapsTo f U V} ↦ (f : X → Y)) 1) :
    IsCompact {f : ContinuousMonoidHom X Y | Set.MapsTo f U W} := by
  replace h := equicontinuous_of_equicontinuousAt_one _ h
  let S1 : Set (X →* Y) := {f | Set.MapsTo f U W}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | Set.MapsTo f U W}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) :=
    h.comp (Subtype.map _root_.id fun f hf ↦ hf.mono_right hWV)
  have hS4 : S4 = (↑) '' S1 := by
    ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y) := by
    rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS4] at h
  replace hS4 : S4 = Set.pi U (fun _ ↦ W) ∩ Set.range ((↑) : (X →* Y) → (X → Y)) := by
    simp_rw [hS4, Set.ext_iff, Set.mem_image, S1, Set.mem_ofPred_eq]
    exact fun f ↦ ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  replace hS4 : IsClosed S4 :=
    hS4.symm ▸ (isClosed_set_pi (fun _ _ ↦ hWc.isClosed)).inter (MonoidHom.isClosed_range_coe X Y)
  exact (ContinuousMonoidHom.isInducing_toContinuousMap X Y).isCompact_iff.mpr
    (ArzelaAscoli.isCompact_of_equicontinuous S3 hS4.isCompact h)

/-- Characters mapping a neighbourhood `K` of `1` into the arc of radius `π / 2` form an
equicontinuous family (the halving argument). -/
theorem equicontinuousAt_mapsTo_arc (K : Set X) (hK : K ∈ 𝓝 (1 : X)) :
    EquicontinuousAt
      (fun f : {f : X →* Circle | Set.MapsTo f K (Circle.centeredArc (π / 2))} ↦ (f : X → Circle))
      1 := by
  let Vn : ℕ → Set Circle := fun n ↦ Circle.centeredArc (π / 2 ^ (n + 1))
  have hVn : ∀ n x, x ∈ Vn n ↔ |Complex.arg x| < π / 2 ^ (n + 1) :=
    fun n x ↦ Circle.mem_centeredArc (z := x)
      (div_le_self pi_nonneg (one_le_pow₀ one_le_two))
  have hV : ∀ {n x}, x ∈ Vn n → x * x ∈ Vn n → x ∈ Vn (n + 1) := by
    intro n x h1 h2
    rw [hVn] at h1 h2 ⊢
    rwa [Circle.coe_mul, Complex.arg_mul x.coe_ne_zero x.coe_ne_zero,
      ← two_mul, abs_mul, abs_two, ← lt_div_iff₀' two_pos, div_div, ← pow_succ] at h2
    apply Set.Ioo_subset_Ioc_self
    rw [← two_mul, Set.mem_Ioo, ← abs_lt, abs_mul, abs_two, ← lt_div_iff₀' two_pos]
    refine h1.trans_le ?_
    gcongr
    exact le_self_pow₀ one_le_two n.succ_ne_zero
  have hVo : (𝓝 (1 : Circle)).HasBasis (fun _ ↦ True) Vn := by
    simpa [Vn] using Circle.hasBasis_centeredArc_div_two_pow
  let U_aux : ℕ → {S : Set X | S ∈ 𝓝 1} :=
    Nat.rec ⟨K, hK⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ 𝓝 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  have hU4 : ∀ f : X →* Circle, Set.MapsTo f (U 0) (Vn 0) → ∀ n, Set.MapsTo f (U n) (Vn n) := by
    intro f hf n
    induction n with
    | zero => exact hf
    | succ n ih =>
      exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))
  have hV0 : Vn 0 = Circle.centeredArc (π / 2) := by simp [Vn]
  have hU0 : U 0 = K := rfl
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  intro n _
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ ?_⟩
  rw [Set.mem_ofPred_eq, map_one, div_one]
  have hf' : Set.MapsTo f (U 0) (Vn 0) := by rw [hV0, hU0]; exact hf
  exact hU4 f hf' n hx

end Equicontinuity

section Dual

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The set `P(K, V)` of the book: characters of `G` mapping `K` into `V`. -/
def charsMapping (K : Set G) (V : Set Circle) : Set (PontryaginDual G) :=
  {γ | Set.MapsTo γ K V}

/-- The arc `V_a = {exp(2πix) : 1 > x > 1 - a or a > x ≥ 0}` of Morris, Theorem A5.7.6. -/
def arcVa (a : ℝ) : Set Circle :=
  {t | ∃ x : ℝ, ((0 ≤ x ∧ x < a) ∨ (1 - a < x ∧ x < 1)) ∧ t = Circle.exp (2 * π * x)}

/-- The arc `V_a` of the book is Mathlib's centered arc of radius `2πa`. -/
theorem arcVa_eq_centeredArc (a : ℝ) : arcVa a = Circle.centeredArc (2 * π * a) := by
  ext t
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · refine ⟨2 * π * x, ?_, rfl⟩
      show |2 * π * x| < 2 * π * a
      rw [abs_of_nonneg (by have := Real.pi_pos; have := hx.1; positivity)]
      exact mul_lt_mul_of_pos_left hx.2 (by positivity)
    · refine ⟨2 * π * (x - 1), ?_, ?_⟩
      · show |2 * π * (x - 1)| < 2 * π * a
        rw [abs_of_nonpos (by nlinarith [Real.pi_pos, hx.2])]
        nlinarith [Real.pi_pos, hx.1]
      · rw [mul_sub, mul_one, Circle.exp_sub_two_pi]
  · rintro ⟨y, hy, rfl⟩
    have hy' : |y| < 2 * π * a := hy
    have h2π : 0 < 2 * π := by positivity
    rcases le_or_gt 0 y with h0 | h0
    · refine ⟨y / (2 * π), Or.inl ⟨by positivity, ?_⟩, ?_⟩
      · rw [abs_of_nonneg h0] at hy'
        rw [div_lt_iff₀ h2π]
        linarith
      · rw [mul_div_cancel₀ _ h2π.ne']
    · refine ⟨y / (2 * π) + 1, Or.inr ⟨?_, ?_⟩, ?_⟩
      · rw [abs_of_neg h0] at hy'
        have : -y / (2 * π) < a := by rw [div_lt_iff₀ h2π]; linarith
        have h3 : y / (2 * π) = -(-y / (2 * π)) := by ring
        linarith
      · have : y / (2 * π) < 0 := div_neg_of_neg_of_pos h0 h2π
        linarith
      · rw [mul_add, mul_div_cancel₀ _ h2π.ne', mul_one, Circle.exp_add_two_pi]

/-- Morris, Topology Without Tears, Theorem A5.7.6 and Corollary A5.7.7 (TP-569). Let `G` be a locally
compact abelian group, `K` a compact neighbourhood of the identity and `0 < a < 1/4`.  Then
`P(K, V_a)`, the set of characters sending `K` into the arc `V_a`, is a neighbourhood of the trivial
character in the dual group, and its closure is compact.  (So the dual group is locally compact.  The
book says `P(K, V_a)` itself is compact; what its proof gives, and what is proved here, is that its
closure is compact.) -/
@[kb "morris2024" "Corollary A5.7.7, p. 561"]
theorem compact_nhds_charsMapping [LocallyCompactSpace G] (K : Set G) (hK : IsCompact K)
    (hKn : K ∈ 𝓝 (1 : G)) {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 4) :
    charsMapping K (arcVa a) ∈ 𝓝 (1 : PontryaginDual G) ∧
      IsCompact (closure (charsMapping K (arcVa a))) := by
  rw [arcVa_eq_centeredArc]
  set r : ℝ := 2 * π * a with hr
  have hr0 : 0 < r := by positivity
  have hrπ : r < π / 2 := by
    rw [hr]; nlinarith [Real.pi_pos]
  have hopen : IsOpen (charsMapping K (Circle.centeredArc r)) :=
    isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hK (Circle.isOpen_centeredArc r))
  have hone : (1 : PontryaginDual G) ∈ charsMapping K (Circle.centeredArc r) := by
    intro x _
    show (1 : Circle) ∈ Circle.centeredArc r
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simpa using hr0
  refine ⟨hopen.mem_nhds hone, ?_⟩
  let W : Set Circle := Circle.exp '' Icc (-r) r
  have hWc : IsCompact W := isCompact_Icc.image Circle.exp.continuous
  have hWV : W ⊆ Circle.centeredArc (π / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxπ : |x| ≤ r := abs_le.2 ⟨hx.1, hx.2⟩
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos]), Circle.arg_exp]
    · exact lt_of_le_of_lt hxπ hrπ
    · linarith [hx.1, Real.pi_pos]
    · linarith [hx.2, Real.pi_pos]
  have hS : IsCompact {f : ContinuousMonoidHom G Circle | Set.MapsTo f K W} :=
    isCompact_mapsTo_of_equicontinuousAt K _ W hK hWc hWV (equicontinuousAt_mapsTo_arc K hKn)
  have hsub : charsMapping K (Circle.centeredArc r) ⊆
      {f : ContinuousMonoidHom G Circle | Set.MapsTo f K W} := by
    intro γ hγ x hx
    obtain ⟨y, hy, hyx⟩ := hγ hx
    exact ⟨y, ⟨(abs_lt.1 hy).1.le, (abs_lt.1 hy).2.le⟩, hyx⟩
  have hcl : closure (charsMapping K (Circle.centeredArc r)) ⊆
      {f : ContinuousMonoidHom G Circle | Set.MapsTo f K W} :=
    closure_minimal hsub hS.isClosed
  exact hS.of_isClosed_subset isClosed_closure hcl

end Dual

end UndergradKB.Topology
