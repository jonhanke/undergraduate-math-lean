import UndergradKB.Topology.ProductsQuotients
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import UndergradKB.Common.Attr

/-!
# Cones and suspensions of spheres; Hausdorff-Mazurkiewicz (easy direction)

Morris, *Topology Without Tears*, Chapter 11 (Propositions 11.2.10 and 11.2.12) and Theorem 9.5.12.
-/

open Set Topology TopologicalSpace Filter unitInterval

namespace UndergradKB.Topology

/-! ### TP-269: the cone on the sphere is the cell -/

section ConeSphere

variable (n : ℕ)

/-- The radial map `(x, t) ↦ t • x` from `S^(n-1) × [0,1]` to the cell `E^n`. -/
noncomputable def radialMap (p : ↥(UnitSphere n) × unitInterval) : ↥(Cell n) :=
  ⟨(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)), by
    rw [mem_cell_iff, norm_smul, (mem_unitSphere_iff _).mp p.1.2, mul_one, Real.norm_eq_abs,
      abs_of_nonneg p.2.2.1]
    exact p.2.2.2⟩

theorem continuous_radialMap : Continuous (radialMap n) := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun p : ↥(UnitSphere n) × unitInterval => ((p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have h2 : Continuous fun p : ↥(UnitSphere n) × unitInterval =>
      (p.1 : EuclideanSpace ℝ (Fin n)) := continuous_subtype_val.comp continuous_fst
  exact h1.smul h2

theorem radialMap_eq_iff (p q : ↥(UnitSphere n) × unitInterval) :
    radialMap n p = radialMap n q ↔ p = q ∨ (p.2 = 0 ∧ q.2 = 0) := by
  constructor
  · intro h
    have h' : (p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)) = (q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin n)) :=
      congrArg Subtype.val h
    have hnorm : ∀ r : ↥(UnitSphere n) × unitInterval,
        ‖(r.2 : ℝ) • (r.1 : EuclideanSpace ℝ (Fin n))‖ = r.2 := by
      intro r
      rw [norm_smul, (mem_unitSphere_iff _).mp r.1.2, mul_one, Real.norm_eq_abs,
        abs_of_nonneg r.2.2.1]
    have ht : (p.2 : ℝ) = q.2 := by rw [← hnorm p, ← hnorm q, h']
    by_cases h0 : (p.2 : ℝ) = 0
    · right
      exact ⟨Subtype.ext h0, Subtype.ext (by rw [← ht, h0]; rfl)⟩
    · left
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ht)
      rw [← ht] at h'
      exact smul_right_injective _ h0 h'
  · rintro (rfl | ⟨h1, h2⟩)
    · rfl
    · apply Subtype.ext
      have a1 : (p.2 : ℝ) = 0 := congrArg Subtype.val h1
      have a2 : (q.2 : ℝ) = 0 := congrArg Subtype.val h2
      show (p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin n)) = (q.2 : ℝ) • (q.1 : EuclideanSpace ℝ (Fin n))
      rw [a1, a2, zero_smul, zero_smul]

theorem surjective_radialMap [NeZero n] : Function.Surjective (radialMap n) := by
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  rintro ⟨y, hy⟩
  have hy' : ‖y‖ ≤ 1 := (mem_cell_iff y).mp hy
  by_cases h0 : y = 0
  · obtain ⟨x, hx⟩ := hne
    refine ⟨(⟨x, hx⟩, 0), Subtype.ext ?_⟩
    simp [radialMap, h0]
  · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr h0
    refine ⟨(⟨‖y‖⁻¹ • y, ?_⟩, ⟨‖y‖, hpos.le, hy'⟩), Subtype.ext ?_⟩
    · rw [mem_unitSphere_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    · show ‖y‖ • (‖y‖⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- Morris, Topology Without Tears, Proposition 11.2.10 (TP-269).  The cone on the sphere
`S^(n-1)` is homeomorphic to the cell `E^n` (for `n ≥ 1`, so that the sphere is nonempty), via
`⟨x, t⟩ ↦ t • x`. -/
@[kb "morris2024" "Proposition 11.2.10, p. 346"]
theorem nonempty_homeomorph_cone_unitSphere_cell [NeZero n] :
    Nonempty (Cone ↥(UnitSphere n) ≃ₜ ↥(Cell n)) := by
  have : CompactSpace ↥(UnitSphere n) := isCompact_iff_compactSpace.mp (isCompact_unitSphere n)
  let g : Cone ↥(UnitSphere n) → ↥(Cell n) :=
    Quotient.lift (s := coneSetoid ↥(UnitSphere n)) (radialMap n) (fun a b h => by
      rcases h with rfl | ⟨h1, h2⟩
      · rfl
      · exact (radialMap_eq_iff n a b).mpr (Or.inr ⟨h1, h2⟩))
  have hg : Continuous g := Continuous.quotient_lift (continuous_radialMap n) _
  have hbij : Function.Bijective g := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      intro h
      exact Quotient.sound ((radialMap_eq_iff n _ _).mp h)
    · intro y
      obtain ⟨p, hp⟩ := surjective_radialMap n y
      exact ⟨Quotient.mk _ p, hp⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hbij) hg⟩

end ConeSphere

/-! ### TP-271: the suspension of the sphere is the next sphere -/

section SuspensionSphere

/-- The vector `(v, s)` of `ℝ^(n+1)` obtained from `v ∈ ℝ^n` and `s ∈ ℝ`. -/
noncomputable def snocVec (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) v.ofLp s)

theorem continuous_snocVec (n : ℕ) :
    Continuous fun p : EuclideanSpace ℝ (Fin n) × ℝ => snocVec n p.1 p.2 := by
  unfold snocVec
  refine (PiLp.continuous_toLp 2 _).comp (Continuous.finSnoc ?_ continuous_snd)
  exact (PiLp.continuous_ofLp 2 _).comp continuous_fst

theorem norm_sq_snocVec (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    ‖snocVec n v s‖ ^ 2 = ‖v‖ ^ 2 + s ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc, EuclideanSpace.norm_sq_eq]
  simp [snocVec]

theorem snocVec_inj (n : ℕ) {v v' : EuclideanSpace ℝ (Fin n)} {s s' : ℝ}
    (h : snocVec n v s = snocVec n v' s') : v = v' ∧ s = s' := by
  constructor
  · ext i
    have := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w.ofLp i.castSucc) h
    simpa [snocVec] using this
  · have := congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) => w.ofLp (Fin.last n)) h
    simpa [snocVec] using this

/-- The angle `θ = π t - π/2` attached to `t ∈ [0,1]`. -/
noncomputable def sphAngle (t : unitInterval) : ℝ := Real.pi * (t : ℝ) - Real.pi / 2

theorem sphAngle_mem (t : unitInterval) : sphAngle t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have h0 := t.2.1
  have h1 := t.2.2
  have hp := Real.pi_pos
  constructor <;> unfold sphAngle <;> nlinarith

theorem cos_sphAngle_pos {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) : 0 < Real.cos (sphAngle t) := by
  have a : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm))
  have b : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))
  have hp := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> unfold sphAngle <;> nlinarith

theorem cos_sphAngle_zero {t : unitInterval} (h : t = 0 ∨ t = 1) :
    Real.cos (sphAngle t) = 0 := by
  rcases h with rfl | rfl
  · have : sphAngle 0 = -(Real.pi / 2) := by simp [sphAngle]
    rw [this, Real.cos_neg, Real.cos_pi_div_two]
  · have : sphAngle 1 = Real.pi / 2 := by simp [sphAngle]; ring
    rw [this, Real.cos_pi_div_two]

theorem sin_sphAngle_zero : Real.sin (sphAngle 0) = -1 := by
  have : sphAngle 0 = -(Real.pi / 2) := by simp [sphAngle]
  rw [this, Real.sin_neg, Real.sin_pi_div_two]

theorem sin_sphAngle_one : Real.sin (sphAngle 1) = 1 := by
  have : sphAngle 1 = Real.pi / 2 := by simp [sphAngle]; ring
  rw [this, Real.sin_pi_div_two]

variable (n : ℕ)

/-- The map `(x, t) ↦ (cos θ · x, sin θ)`, `θ = π t - π/2`, from `S^(n-1) × [0,1]` to `S^n`. -/
noncomputable def sphereMap (p : ↥(UnitSphere n) × unitInterval) : ↥(UnitSphere (n + 1)) :=
  ⟨snocVec n (Real.cos (sphAngle p.2) • (p.1 : EuclideanSpace ℝ (Fin n))) (Real.sin (sphAngle p.2)),
    by
      rw [mem_unitSphere_iff]
      have hx := (mem_unitSphere_iff _).mp p.1.2
      have h2 := norm_sq_snocVec n (Real.cos (sphAngle p.2) • (p.1 : EuclideanSpace ℝ (Fin n)))
        (Real.sin (sphAngle p.2))
      rw [norm_smul, hx, mul_one, Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq] at h2
      nlinarith [norm_nonneg (snocVec n (Real.cos (sphAngle p.2) • (p.1 : EuclideanSpace ℝ (Fin n)))
        (Real.sin (sphAngle p.2)))]⟩

theorem continuous_sphereMap : Continuous (sphereMap n) := by
  refine Continuous.subtype_mk ?_ _
  have hθ : Continuous fun p : ↥(UnitSphere n) × unitInterval => sphAngle p.2 := by
    unfold sphAngle
    exact (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  have h2 : Continuous fun p : ↥(UnitSphere n) × unitInterval =>
      (p.1 : EuclideanSpace ℝ (Fin n)) := continuous_subtype_val.comp continuous_fst
  exact (continuous_snocVec n).comp
    (((Real.continuous_cos.comp hθ).smul h2).prodMk (Real.continuous_sin.comp hθ))

theorem sphereMap_eq_of_rel (a b : ↥(UnitSphere n) × unitInterval) (h : SuspensionRel _ a b) :
    sphereMap n a = sphereMap n b := by
  apply Subtype.ext
  show snocVec n _ _ = snocVec n _ _
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [cos_sphAngle_zero (Or.inl h1), cos_sphAngle_zero (Or.inl h2), h1, h2]
    simp [sin_sphAngle_zero]
  · rw [cos_sphAngle_zero (Or.inr h1), cos_sphAngle_zero (Or.inr h2), h1, h2]
    simp [sin_sphAngle_one]

theorem sphereMap_injective_aux (a b : ↥(UnitSphere n) × unitInterval)
    (h : sphereMap n a = sphereMap n b) : a = b ∨ SuspensionRel _ a b := by
  have h' : snocVec n (Real.cos (sphAngle a.2) • (a.1 : EuclideanSpace ℝ (Fin n)))
      (Real.sin (sphAngle a.2)) = snocVec n (Real.cos (sphAngle b.2) • (b.1 : EuclideanSpace ℝ (Fin n)))
      (Real.sin (sphAngle b.2)) := congrArg Subtype.val h
  obtain ⟨hv, hs⟩ := snocVec_inj n h'
  have hθ : sphAngle a.2 = sphAngle b.2 :=
    Real.injOn_sin (sphAngle_mem a.2) (sphAngle_mem b.2) hs
  have hp := Real.pi_pos
  have ht : a.2 = b.2 := by
    apply Subtype.ext
    unfold sphAngle at hθ
    nlinarith
  by_cases h0 : a.2 = 0
  · right
    exact Or.inl ⟨h0, ht ▸ h0⟩
  by_cases h1 : a.2 = 1
  · right
    exact Or.inr ⟨h1, ht ▸ h1⟩
  left
  have hc := cos_sphAngle_pos h0 h1
  rw [← hθ] at hv
  refine Prod.ext (Subtype.ext (smul_right_injective _ hc.ne' hv)) ht

theorem surjective_sphereMap [NeZero n] : Function.Surjective (sphereMap n) := by
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  rintro ⟨w, hw⟩
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => w.ofLp i.castSucc) with hv
  set s : ℝ := w.ofLp (Fin.last n) with hs
  have hwv : w = snocVec n v s := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocVec, hv, hs]
  have hnorm : ‖v‖ ^ 2 + s ^ 2 = 1 := by
    have h1 := (mem_unitSphere_iff _).mp hw
    have := norm_sq_snocVec n v s
    rw [← hwv, h1] at this
    linarith
  have hs1 : |s| ≤ 1 := sq_le_one_iff_abs_le_one s |>.mp (by nlinarith [sq_nonneg ‖v‖])
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs1
  have hθ1 := Real.neg_pi_div_two_le_arcsin s
  have hθ2 := Real.arcsin_le_pi_div_two s
  have hp := Real.pi_pos
  let t : unitInterval := ⟨(Real.arcsin s + Real.pi / 2) / Real.pi,
    ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩⟩
  have hang : sphAngle t = Real.arcsin s := by
    simp only [sphAngle, t]
    field_simp
    ring
  have hsin : Real.sin (Real.arcsin s) = s := Real.sin_arcsin hsa hsb
  have hcos : Real.cos (Real.arcsin s) = ‖v‖ := by
    rw [Real.cos_arcsin]
    have : 1 - s ^ 2 = ‖v‖ ^ 2 := by linarith
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  by_cases hv0 : v = 0
  · obtain ⟨x, hx⟩ := hne
    refine ⟨(⟨x, hx⟩, t), Subtype.ext ?_⟩
    show snocVec n (Real.cos (sphAngle t) • x) (Real.sin (sphAngle t)) = w
    rw [hang, hsin, hcos, hwv, hv0]
    simp
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have hx : ‖v‖⁻¹ • v ∈ UnitSphere n := by
      rw [mem_unitSphere_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    refine ⟨(⟨‖v‖⁻¹ • v, hx⟩, t), Subtype.ext ?_⟩
    show snocVec n (Real.cos (sphAngle t) • (‖v‖⁻¹ • v)) (Real.sin (sphAngle t)) = w
    rw [hang, hsin, hcos, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, hwv]

/-- Morris, Topology Without Tears, Proposition 11.2.12 (TP-271).  The suspension of the sphere
`S^(n-1)` is homeomorphic to `S^n` (for `n ≥ 1`), via `⟨x, t⟩ ↦ (cos θ · x, sin θ)`,
`θ = π t - π/2`. -/
@[kb "morris2024" "Proposition 11.2.12, p. 347"]
theorem nonempty_homeomorph_suspension_unitSphere [NeZero n] :
    Nonempty (Suspension ↥(UnitSphere n) ≃ₜ ↥(UnitSphere (n + 1))) := by
  have : CompactSpace ↥(UnitSphere n) := isCompact_iff_compactSpace.mp (isCompact_unitSphere n)
  let g : Suspension ↥(UnitSphere n) → ↥(UnitSphere (n + 1)) :=
    Quot.lift (sphereMap n) (sphereMap_eq_of_rel n)
  have hg : Continuous g := continuous_quot_lift _ (continuous_sphereMap n)
  have hbij : Function.Bijective g := by
    constructor
    · intro a b
      induction a using Quot.inductionOn
      induction b using Quot.inductionOn
      intro h
      rcases sphereMap_injective_aux n _ _ h with rfl | hr
      · rfl
      · exact Quot.sound hr
    · intro y
      obtain ⟨p, hp⟩ := surjective_sphereMap n y
      exact ⟨Quot.mk _ p, hp⟩
  have : T2Space ↥(UnitSphere (n + 1)) := inferInstance
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hbij) hg⟩

end SuspensionSphere

/-! ### TP-235: Hausdorff images of the unit interval (the easy direction) -/

section HahnMazurkiewicz

/-- A continuous surjection from a compact second countable space onto a Hausdorff space has a
second countable codomain (the same argument as in `CountableProducts`, repeated privately). -/
private theorem secondCountable_of_surj {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : SecondCountableTopology Y := by
  have hcl : IsClosedMap f := hf.isClosedMap
  let 𝒰 : Set (Set X) := (fun t : Set (Set X) => ⋃₀ t) '' {t | t.Finite ∧ t ⊆ countableBasis X}
  have h𝒰 : 𝒰.Countable := (Set.countable_ofPred_finite_subset (countable_countableBasis X)).image _
  let 𝒱 : Set (Set Y) := (fun U => (f '' Uᶜ)ᶜ) '' 𝒰
  have h𝒱 : 𝒱.Countable := h𝒰.image _
  have hB : IsTopologicalBasis 𝒱 := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨U, ⟨t, ⟨htf, htB⟩, rfl⟩, rfl⟩
      refine (hcl _ ?_).isOpen_compl
      exact (isOpen_sUnion fun s hs => isOpen_of_mem_countableBasis (htB hs)).isClosed_compl
    · intro y W hyW hWo
      have hK : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      have hsub : f ⁻¹' {y} ⊆ ⋃ s ∈ {s | s ∈ countableBasis X ∧ s ⊆ f ⁻¹' W}, id s := by
        intro x hx
        have hxW : x ∈ f ⁻¹' W := by
          have : f x = y := hx
          simpa [this] using hyW
        obtain ⟨s, hsB, hxs, hsW⟩ :=
          (isBasis_countableBasis X).exists_subset_of_mem_open hxW (hWo.preimage hf)
        exact mem_iUnion₂.mpr ⟨s, ⟨hsB, hsW⟩, hxs⟩
      obtain ⟨b', hb'sub, hb'fin, hcov⟩ := hK.elim_finite_subcover_image
        (b := {s | s ∈ countableBasis X ∧ s ⊆ f ⁻¹' W}) (c := id)
        (fun s hs' => isOpen_of_mem_countableBasis hs'.1) hsub
      refine ⟨(f '' (⋃₀ b')ᶜ)ᶜ, ⟨⋃₀ b', ⟨b', ⟨hb'fin, fun s hs => (hb'sub hs).1⟩, rfl⟩, rfl⟩,
        ?_, ?_⟩
      · rintro ⟨x, hx, hxy⟩
        apply hx
        obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hcov (show x ∈ f ⁻¹' {y} from hxy))
        exact ⟨s, hs, hxs⟩
      · intro y' hy'
        obtain ⟨x, rfl⟩ := hs y'
        have hx : x ∈ ⋃₀ b' := by
          by_contra hn
          exact hy' ⟨x, hn, rfl⟩
        obtain ⟨s, hs, hxs⟩ := hx
        exact (hb'sub hs).2 hxs
  exact hB.secondCountableTopology h𝒱

/-- The unit interval is locally connected: it is a quotient of `ℝ` by `projIcc`. -/
theorem locallyConnectedSpace_unitInterval : LocallyConnectedSpace unitInterval := by
  have hco : IsCoinducing (Set.projIcc (0 : ℝ) 1 zero_le_one) := by
    rw [isCoinducing_iff]
    intro s
    refine ⟨fun hs => ?_, fun hs => hs.preimage continuous_projIcc⟩
    have : s = (fun x : unitInterval => (x : ℝ)) ⁻¹' (Set.projIcc (0 : ℝ) 1 zero_le_one ⁻¹' s) := by
      ext x
      simp [Set.projIcc_val]
    rw [this]
    exact hs.preimage continuous_subtype_val
  exact hco.locallyConnectedSpace

/-- Morris, Topology Without Tears, Theorem 9.5.12 (TP-235), the "only if" direction.  A Hausdorff
space that is a continuous image of `[0,1]` is compact, connected, locally connected and
metrizable.  (The converse, the Hahn-Mazurkiewicz theorem proper, is not proved here.) -/
@[kb "morris2024" "Theorem 9.5.12, p. 253"]
theorem compact_connected_locallyConnected_metrizable_of_continuous_surjective_unitInterval
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f : unitInterval → Y} (hf : Continuous f)
    (hs : Function.Surjective f) :
    CompactSpace Y ∧ ConnectedSpace Y ∧ LocallyConnectedSpace Y ∧ MetrizableSpace Y := by
  have hc : CompactSpace Y := ⟨hs.range_eq ▸ isCompact_range hf⟩
  have h2 := secondCountable_of_surj hf hs
  have h3 := locallyConnectedSpace_unitInterval
  have hq : IsQuotientMap f := hf.isClosedMap.isQuotientMap hf hs
  exact ⟨hc, hs.connectedSpace hf, hq.isCoinducing.locallyConnectedSpace, inferInstance⟩

end HahnMazurkiewicz

/-! ### TP-272 (continued): the surfaces are Hausdorff -/

section Surfaces

/-- A quotient of a compact Hausdorff space whose identification relation is closed is Hausdorff. -/
theorem t2Space_quot_of_closed_rel {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (r : X → X → Prop) (R : X → X → Prop) (hR : IsClosed {p : X × X | R p.1 p.2})
    (hiff : ∀ a b, Quot.mk r a = Quot.mk r b ↔ R a b) : T2Space (Quot r) := by
  have hq : IsQuotientMap (Quot.mk r : X → Quot r) := isQuotientMap_quot_mk
  have hsat : ∀ C : Set X, IsClosed C → IsClosed (Quot.mk r '' C) := by
    intro C hC
    rw [← hq.isClosed_preimage]
    have : (Quot.mk r) ⁻¹' (Quot.mk r '' C) = Prod.snd '' ({p : X × X | R p.1 p.2} ∩ (C ×ˢ univ)) := by
      ext y
      constructor
      · rintro ⟨c, hc, hcy⟩
        exact ⟨(c, y), ⟨(hiff c y).mp hcy, hc, trivial⟩, rfl⟩
      · rintro ⟨⟨c, y'⟩, ⟨hR', hc, -⟩, rfl⟩
        exact ⟨c, hc, (hiff c y').mpr hR'⟩
    rw [this]
    exact isClosedMap_snd_of_compactSpace _ (hR.inter (hC.prod isClosed_univ))
  rw [t2Space_iff]
  intro a b hab
  obtain ⟨p, rfl⟩ := Quot.exists_rep a
  obtain ⟨q, rfl⟩ := Quot.exists_rep b
  have hF : ∀ z : X, IsClosed {y | R z y} := fun z =>
    hR.preimage (Continuous.prodMk continuous_const continuous_id)
  have hd : Disjoint {y | R p y} {y | R q y} := by
    rw [Set.disjoint_left]
    intro y h1 h2
    exact hab (((hiff p y).mpr h1).trans ((hiff q y).mpr h2).symm)
  obtain ⟨U1, U2, o1, o2, s1, s2, hU⟩ := NormalSpace.normal _ _ (hF p) (hF q) hd
  refine ⟨(Quot.mk r '' U1ᶜ)ᶜ, (Quot.mk r '' U2ᶜ)ᶜ, (hsat _ o1.isClosed_compl).isOpen_compl,
    (hsat _ o2.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro ⟨c, hc, hcp⟩
    exact hc (s1 ((hiff p c).mp hcp.symm))
  · rintro ⟨c, hc, hcq⟩
    exact hc (s2 ((hiff q c).mp hcq.symm))
  · rw [Set.disjoint_left]
    intro y h1 h2
    obtain ⟨c, rfl⟩ := Quot.exists_rep y
    have c1 : c ∈ U1 := by_contra fun h => h1 ⟨c, h, rfl⟩
    have c2 : c ∈ U2 := by_contra fun h => h2 ⟨c, h, rfl⟩
    exact Set.disjoint_left.mp hU c1 c2

/-- Description of equality in `Quot r` by a relation `R` containing `r` and contained in the
equivalence relation generated by `r`. -/
theorem quot_mk_eq_iff_of_rel {α : Type*} (r R : α → α → Prop) (hrefl : ∀ a, R a a)
    (hr : ∀ a b, r a b → R a b) (hsymm : ∀ a b, R a b → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hback : ∀ a b, R a b → Relation.EqvGen r a b)
    (a b : α) : Quot.mk r a = Quot.mk r b ↔ R a b := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel x y h => exact hr x y h
    | refl x => exact hrefl x
    | symm x y _ ih => exact hsymm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact htrans _ _ _ ih1 ih2
  · intro h
    exact Quot.eqvGen_sound (hback a b h)

private theorem sigma_inj {a b : unitInterval} (h : σ a = σ b) : a = b := by
  have := congrArg Subtype.val h
  simp only [unitInterval.coe_symm_eq] at this
  exact Subtype.ext (by linarith)

private theorem sigma_eq_one {a : unitInterval} : σ a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [unitInterval.coe_symm_eq] at this
    exact Subtype.ext (by simpa using this)
  · rintro rfl; simp

private theorem sigma_eq_zero {a : unitInterval} : σ a = 0 ↔ a = 1 := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [unitInterval.coe_symm_eq] at this
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [h0] at this
    exact Subtype.ext (by rw [h1]; linarith)
  · rintro rfl; simp

private theorem one_eq_sigma {a : unitInterval} : 1 = σ a ↔ a = 0 := eq_comm.trans sigma_eq_one

private theorem zero_eq_sigma {a : unitInterval} : 0 = σ a ↔ a = 1 := eq_comm.trans sigma_eq_zero

private theorem zero_ne_one': (0 : unitInterval) ≠ 1 := zero_ne_one

/-- The explicit identification relation of the Moebius strip. -/
def MobiusR (p q : unitInterval × unitInterval) : Prop := p = q ∨ MobiusRel p q ∨ MobiusRel q p

theorem mobiusR_trans (p q r : unitInterval × unitInterval) (h1 : MobiusR p q) (h2 : MobiusR q r) :
    MobiusR p r := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  unfold MobiusR MobiusRel at *
  simp only [Prod.mk.injEq] at *
  rcases h1 with ⟨rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ <;>
  rcases h2 with ⟨rfl, rfl⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨h2, h3, h4⟩)
  · exact Or.inr (Or.inr ⟨h2, h3, h4⟩)
  · exact Or.inr (Or.inl ⟨h1, rfl, rfl⟩)
  · exact absurd h2 one_ne_zero
  · exact Or.inl ⟨sigma_inj h3, h1.trans h2.symm⟩
  · exact Or.inr (Or.inr ⟨h1, rfl, rfl⟩)
  · exact Or.inl ⟨h3.symm, h4.symm⟩
  · exact absurd (h1.symm.trans h4) zero_ne_one'

private theorem closed_prod_rel_aux {f g : (unitInterval × unitInterval) × (unitInterval × unitInterval) →
    unitInterval} (hf : Continuous f) (hg : Continuous g) :
    IsClosed {p : (unitInterval × unitInterval) × (unitInterval × unitInterval) | f p = g p} :=
  isClosed_eq hf hg

/-- Morris, Topology Without Tears, Example 11.3.3 (TP-272).  The Moebius strip is Hausdorff. -/
@[kb "morris2024" "Example 11.3.3, p. 350"]
theorem t2Space_mobiusStrip : T2Space MobiusStrip := by
  have hc1 : Continuous fun p : (unitInterval × unitInterval) × (unitInterval × unitInterval) =>
      σ p.1.1 := unitInterval.continuous_symm.comp (continuous_fst.comp continuous_fst)
  have hc2 : Continuous fun p : (unitInterval × unitInterval) × (unitInterval × unitInterval) =>
      σ p.2.1 := unitInterval.continuous_symm.comp (continuous_fst.comp continuous_snd)
  refine t2Space_quot_of_closed_rel MobiusRel MobiusR ?_
    (quot_mk_eq_iff_of_rel MobiusRel MobiusR (fun a => Or.inl rfl)
      (fun a b h => Or.inr (Or.inl h))
      (fun a b h => by
        rcases h with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h))
      mobiusR_trans
      (fun a b h => by
        rcases h with rfl | h | h
        · exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ h
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)))
  unfold MobiusR MobiusRel
  refine (isClosed_eq continuous_fst continuous_snd).union
    (((isClosed_eq (continuous_snd.comp (continuous_fst)) continuous_const).inter
      (isClosed_eq continuous_snd (hc1.prodMk continuous_const))).union
    ((isClosed_eq (continuous_snd.comp (continuous_snd)) continuous_const).inter
      (isClosed_eq continuous_fst (hc2.prodMk continuous_const))))

/-- The explicit identification relation of the real projective plane. -/
def ProjectivePlaneR (p q : unitInterval × unitInterval) : Prop :=
  p = q ∨ ProjectivePlaneRel p q ∨ ProjectivePlaneRel q p

theorem projectivePlaneR_trans (p q r : unitInterval × unitInterval) (h1 : ProjectivePlaneR p q)
    (h2 : ProjectivePlaneR q r) : ProjectivePlaneR p r := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  unfold ProjectivePlaneR ProjectivePlaneRel at *
  simp only [Prod.mk.injEq] at *
  rcases h1 with ⟨rfl, rfl⟩ | (⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩) | (⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩) <;>
  rcases h2 with ⟨rfl, rfl⟩ | (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩) | (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩) <;>
  simp_all [one_eq_sigma, unitInterval.symm_symm]

/-- Morris, Topology Without Tears, Example 11.3.4 (TP-272).  The real projective plane is
Hausdorff. -/
@[kb "morris2024" "Example 11.3.4, p. 351"]
theorem t2Space_projectivePlane : T2Space ProjectivePlane := by
  refine t2Space_quot_of_closed_rel ProjectivePlaneRel ProjectivePlaneR ?_
    (quot_mk_eq_iff_of_rel ProjectivePlaneRel ProjectivePlaneR (fun a => Or.inl rfl)
      (fun a b h => Or.inr (Or.inl h))
      (fun a b h => by
        rcases h with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h))
      projectivePlaneR_trans
      (fun a b h => by
        rcases h with rfl | h | h
        · exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ h
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)))
  unfold ProjectivePlaneR ProjectivePlaneRel
  simp only [Set.ofPred_or, Set.ofPred_and]
  repeat' first
    | exact isClosed_eq (by fun_prop) (by fun_prop)
    | apply IsClosed.union
    | apply IsClosed.inter

/-- The explicit identification relation of the Klein bottle: the generating identifications and
the four corners of the square all identified. -/
def KleinR (p q : unitInterval × unitInterval) : Prop :=
  p = q ∨ KleinRel p q ∨ KleinRel q p ∨
    (((p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 0 ∨ p.2 = 1)) ∧ ((q.1 = 0 ∨ q.1 = 1) ∧ (q.2 = 0 ∨ q.2 = 1)))

theorem kleinR_trans (p q r : unitInterval × unitInterval) (h1 : KleinR p q)
    (h2 : KleinR q r) : KleinR p r := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  unfold KleinR KleinRel at *
  simp only [Prod.mk.injEq] at *
  rcases h1 with ⟨rfl, rfl⟩ | (⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩) | (⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩) |
      ⟨hp, hq⟩ <;>
  rcases h2 with ⟨rfl, rfl⟩ | (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩) | (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩) |
      ⟨hq', hr⟩ <;>
  simp_all [one_eq_sigma, unitInterval.symm_symm]
  all_goals aesop (add norm simp [one_eq_sigma, sigma_eq_one, zero_eq_sigma, sigma_eq_zero,
    unitInterval.symm_symm])

/-- Morris, Topology Without Tears, Example 11.3.5 (TP-272).  The Klein bottle is Hausdorff. -/
@[kb "morris2024" "Example 11.3.5, p. 352"]
theorem t2Space_kleinBottle : T2Space KleinBottle := by
  have hback : ∀ a b, KleinR a b → Relation.EqvGen KleinRel a b := by
    intro a b h
    rcases h with rfl | h | h | ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)
    · have e1 : Relation.EqvGen KleinRel ((0 : unitInterval), (0 : unitInterval)) (1, 0) :=
        Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl⟩)
      have e2 : Relation.EqvGen KleinRel ((1 : unitInterval), (0 : unitInterval)) (0, 1) :=
        Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, by simp⟩)
      have e3 : Relation.EqvGen KleinRel ((0 : unitInterval), (0 : unitInterval)) (1, 1) :=
        Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, by simp⟩)
      have hc : ∀ c : unitInterval × unitInterval, ((c.1 = 0 ∨ c.1 = 1) ∧ (c.2 = 0 ∨ c.2 = 1)) →
          Relation.EqvGen KleinRel c (0, 0) := by
        rintro ⟨c1, c2⟩ ⟨h1 | h1, h2 | h2⟩ <;> subst h1 <;> subst h2
        · exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ e2) (Relation.EqvGen.symm _ _ e1)
        · exact Relation.EqvGen.symm _ _ e1
        · exact Relation.EqvGen.symm _ _ e3
      exact Relation.EqvGen.trans _ _ _ (hc _ ⟨ha1, ha2⟩) (Relation.EqvGen.symm _ _ (hc _ ⟨hb1, hb2⟩))
  refine t2Space_quot_of_closed_rel KleinRel KleinR ?_
    (quot_mk_eq_iff_of_rel KleinRel KleinR (fun a => Or.inl rfl)
      (fun a b h => Or.inr (Or.inl h))
      (fun a b h => by
        rcases h with h | h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))
      kleinR_trans hback)
  unfold KleinR KleinRel
  simp only [Set.ofPred_or, Set.ofPred_and]
  repeat' first
    | exact isClosed_eq (by fun_prop) (by fun_prop)
    | apply IsClosed.union
    | apply IsClosed.inter

end Surfaces

end UndergradKB.Topology
