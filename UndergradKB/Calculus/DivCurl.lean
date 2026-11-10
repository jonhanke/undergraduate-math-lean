import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import UndergradKB.Common.Attr
import UndergradKB.Calculus.LineIntegrals

/-! # Calculus: divergence and curl

Partial derivatives, divergence and curl of plane and space fields given by components (OpenStax Calculus 3,
§6.4–6.5), `curl (∇f) = 0`, `div (curl F) = 0`, the Poincare lemma in book form on open convex sets
(conservative iff the cross partials agree), the inverse-square field, stream functions, source-free
planar fields and harmonic potentials. Simply connected domains are replaced by convex ones, since this is
the generality of Mathlib's Poincare lemma. -/

namespace UndergradKB.Calculus
open Set MeasureTheory intervalIntegral

section Partials
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_apply_fderiv {g : E → ℝ} {p : E} (hg : ContDiffAt ℝ 2 g p) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ g q v) p w = fderiv ℝ (fderiv ℝ g) p w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p hd.hasFDerivAt)
  have h2 : (fun q => fderiv ℝ g q v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ g := rfl
  rw [h2, this.fderiv]
  rfl

lemma mixed_symm {g : E → ℝ} {p : E} (hg : ContDiffAt ℝ 2 g p) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ g q v) p w = fderiv ℝ (fun q => fderiv ℝ g q w) p v := by
  rw [fderiv_apply_fderiv hg, fderiv_apply_fderiv hg]
  exact (hg.isSymmSndFDerivAt (by simp)) w v

lemma differentiableAt_fderiv_apply {g : E → ℝ} {p : E} (hg : ContDiffAt ℝ 2 g p) (v : E) :
    DifferentiableAt ℝ (fun q => fderiv ℝ g q v) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hd.clm_apply (differentiableAt_const v)

lemma fderiv_apply_sub {g h : E → ℝ} {p : E} (hg : DifferentiableAt ℝ g p)
    (hh : DifferentiableAt ℝ h p) (v : E) :
    fderiv ℝ (fun q => g q - h q) p v = fderiv ℝ g p v - fderiv ℝ h p v := by
  rw [fderiv_fun_sub hg hh]; rfl

end Partials

section DivCurlDefs

/-- The partial derivative `∂g/∂x` of a function of the plane. -/
noncomputable def pdx2 (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ g p (1, 0)
/-- The partial derivative `∂g/∂y` of a function of the plane. -/
noncomputable def pdy2 (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ g p (0, 1)

/-- OpenStax Calculus 3:§6.5 Definition (CA-641). Divergence of a planar field `(P, Q)`: `P_x + Q_y`. -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (divergence), p. 668"]
noncomputable def div2 (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := pdx2 P p + pdy2 Q p
/-- OpenStax Calculus 3:§6.5 Definition (CA-644). Curl of a planar field `(P, Q)`: `Q_x - P_y`. -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (curl), p. 674"]
noncomputable def curl2 (P Q : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := pdx2 Q p - pdy2 P p

/-- The partial derivative `∂g/∂x` of a function of space. -/
noncomputable def pdx3 (g : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := fderiv ℝ g p (1, 0, 0)
/-- The partial derivative `∂g/∂y` of a function of space. -/
noncomputable def pdy3 (g : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := fderiv ℝ g p (0, 1, 0)
/-- The partial derivative `∂g/∂z` of a function of space. -/
noncomputable def pdz3 (g : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := fderiv ℝ g p (0, 0, 1)

/-- OpenStax Calculus 3:§6.5 Definition (CA-641). Divergence of a space field `(P, Q, R)`:
`P_x + Q_y + R_z`. -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (divergence), p. 668"]
noncomputable def div3 (P Q R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  pdx3 P p + pdy3 Q p + pdz3 R p

/-- OpenStax Calculus 3:§6.5 Definition (CA-644). Curl of a space field `(P, Q, R)`:
`(R_y - Q_z, P_z - R_x, Q_x - P_y)`. -/
@[kb "openstaxcalculus2016" "3:§6.5 Definition (curl), p. 674"]
noncomputable def curl3 (P Q R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (pdy3 R p - pdz3 Q p, pdz3 P p - pdx3 R p, pdx3 Q p - pdy3 P p)

/-- OpenStax Calculus 3:Theorem 6.17 (CA-647). The curl of the gradient of a `C²` function of the plane is
zero. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.17, p. 677"]
theorem curl2_grad {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    curl2 (pdx2 f) (pdy2 f) p = 0 := by
  have := mixed_symm hf (0, 1) (1, 0)
  exact sub_eq_zero.2 this

/-- OpenStax Calculus 3:Theorem 6.17 (CA-647). `curl (∇f) = 0` for a `C²` function `f` of space. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.17, p. 677"]
theorem curl3_grad {f : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ} (hf : ContDiffAt ℝ 2 f p) :
    curl3 (pdx3 f) (pdy3 f) (pdz3 f) p = 0 := by
  have h1 := mixed_symm hf (0, 0, 1) (0, 1, 0)
  have h2 := mixed_symm hf (1, 0, 0) (0, 0, 1)
  have h3 := mixed_symm hf (0, 1, 0) (1, 0, 0)
  simp only [curl3]
  refine Prod.ext (sub_eq_zero.2 h1) (Prod.ext (sub_eq_zero.2 h2) (sub_eq_zero.2 h3))

/-- OpenStax Calculus 3:Theorem 6.16 (CA-646). `div (curl F) = 0` for a space field with `C²`
components. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.16, p. 676"]
theorem div3_curl3 {P Q R : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ} (hP : ContDiffAt ℝ 2 P p)
    (hQ : ContDiffAt ℝ 2 Q p) (hR : ContDiffAt ℝ 2 R p) :
    div3 (fun q => (curl3 P Q R q).1) (fun q => (curl3 P Q R q).2.1)
      (fun q => (curl3 P Q R q).2.2) p = 0 := by
  have a1 := mixed_symm hR (0, 1, 0) (1, 0, 0)
  have a2 := mixed_symm hQ (0, 0, 1) (1, 0, 0)
  have a3 := mixed_symm hP (0, 0, 1) (0, 1, 0)
  simp only [div3, curl3, pdx3, pdy3, pdz3]
  rw [fderiv_apply_sub (differentiableAt_fderiv_apply hR _) (differentiableAt_fderiv_apply hQ _),
    fderiv_apply_sub (differentiableAt_fderiv_apply hP _) (differentiableAt_fderiv_apply hR _),
    fderiv_apply_sub (differentiableAt_fderiv_apply hQ _) (differentiableAt_fderiv_apply hP _)]
  linarith

end DivCurlDefs

section Poincare

lemma clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ) :
    L x = x.1 * L (1, 0) + x.2 * L (0, 1) := by
  have : x = x.1 • ((1, 0) : ℝ × ℝ) + x.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]

lemma clm_apply_triple (L : ℝ × ℝ × ℝ →L[ℝ] ℝ) (x : ℝ × ℝ × ℝ) :
    L x = x.1 * L (1, 0, 0) + x.2.1 * L (0, 1, 0) + x.2.2 * L (0, 0, 1) := by
  have : x = x.1 • ((1, 0, 0) : ℝ × ℝ × ℝ) + x.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) +
      x.2.2 • ((0, 0, 1) : ℝ × ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]

lemma hasFDerivAt_form2 {P Q : ℝ × ℝ → ℝ} {a : ℝ × ℝ} (hP : DifferentiableAt ℝ P a)
    (hQ : DifferentiableAt ℝ Q a) :
    HasFDerivAt (form2 P Q)
      ((fderiv ℝ P a).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (fderiv ℝ Q a).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) a :=
  (hP.hasFDerivAt.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
    (hQ.hasFDerivAt.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma form2_symm_iff {P Q : ℝ × ℝ → ℝ} {a : ℝ × ℝ} (hP : DifferentiableAt ℝ P a)
    (hQ : DifferentiableAt ℝ Q a) :
    (∀ x y, fderiv ℝ (form2 P Q) a x y = fderiv ℝ (form2 P Q) a y x) ↔ pdy2 P a = pdx2 Q a := by
  have key : ∀ x y : ℝ × ℝ, fderiv ℝ (form2 P Q) a x y =
      fderiv ℝ P a x * y.1 + fderiv ℝ Q a x * y.2 := by
    intro x y
    rw [(hasFDerivAt_form2 hP hQ).fderiv]
    simp
  simp only [key]
  unfold pdx2 pdy2
  constructor
  · intro h
    have := h (0, 1) (1, 0)
    simpa using this
  · intro h x y
    rw [clm_apply_pair (fderiv ℝ P a) x, clm_apply_pair (fderiv ℝ P a) y,
      clm_apply_pair (fderiv ℝ Q a) x, clm_apply_pair (fderiv ℝ Q a) y]
    linear_combination (x.2 * y.1 - x.1 * y.2) * h

/-- OpenStax Calculus 3:Theorem 6.10 (CA-630). A `C¹` planar field `(P, Q)` with `P_y = Q_x` on an open
*convex* set (the book states it for simply connected regions; Mathlib's Poincare lemma covers convex
sets only) is conservative. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.10, p. 636"]
theorem isConservative2_of_pdy_eq_pdx {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (h : ∀ p ∈ U, pdy2 P p = pdx2 Q p) : IsConservative2 P Q U := by
  have hPd : ∀ p ∈ U, DifferentiableAt ℝ P p := fun p hp =>
    (hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hQd : ∀ p ∈ U, DifferentiableAt ℝ Q p := fun p hp =>
    (hQ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  exact hc.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
    (fun p hp => (hasFDerivAt_form2 (hPd p hp) (hQd p hp)).differentiableAt.differentiableWithinAt)
    (fun p hp => (form2_symm_iff (hPd p hp) (hQd p hp)).2 (h p hp))

/-- OpenStax Calculus 3:Theorem 6.11 (CA-631), cross-partial property. A conservative `C¹` planar field
on an open set has `P_y = Q_x` (symmetry of second derivatives). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.11, p. 637"]
theorem pdy2_eq_pdx2_of_isConservative2 {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (h : IsConservative2 P Q U) :
    ∀ p ∈ U, pdy2 P p = pdx2 Q p := by
  intro p hp
  obtain ⟨f, hf⟩ := h
  have hPd : DifferentiableAt ℝ P p := (hP.differentiableOn one_ne_zero).differentiableAt
    (hU.mem_nhds hp)
  have hQd : DifferentiableAt ℝ Q p := (hQ.differentiableOn one_ne_zero).differentiableAt
    (hU.mem_nhds hp)
  rw [← form2_symm_iff hPd hQd]
  intro v w
  have := second_derivative_symmetric_of_eventually (f := f) (f' := form2 P Q)
    (Filter.eventually_of_mem (hU.mem_nhds hp) hf) (hasFDerivAt_form2 hPd hQd) v w
  rwa [(hasFDerivAt_form2 hPd hQd).fderiv]

lemma curl2_eq_zero_iff {P Q : ℝ × ℝ → ℝ} {p : ℝ × ℝ} :
    curl2 P Q p = 0 ↔ pdy2 P p = pdx2 Q p := by
  unfold curl2
  rw [sub_eq_zero, eq_comm]

/-- OpenStax Calculus 3:Theorem 6.11 (CA-631). On an open convex set, a `C¹` planar field is conservative
iff `P_y = Q_x` (the book assumes simply connected; here convex). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.11, p. 637"]
theorem isConservative2_iff_pdy_eq_pdx {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IsConservative2 P Q U ↔ ∀ p ∈ U, pdy2 P p = pdx2 Q p :=
  ⟨pdy2_eq_pdx2_of_isConservative2 hU hP hQ, isConservative2_of_pdy_eq_pdx hU hc hP hQ⟩

/-- OpenStax Calculus 3:Theorem 6.18 (CA-648). On an open convex set, a `C¹` planar field is conservative
iff its curl `Q_x - P_y` vanishes (the book assumes simply connected; here convex). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.18, p. 677"]
theorem isConservative2_iff_curl2_eq_zero {P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IsConservative2 P Q U ↔ ∀ p ∈ U, curl2 P Q p = 0 := by
  rw [isConservative2_iff_pdy_eq_pdx hU hc hP hQ]
  simp only [curl2_eq_zero_iff]

lemma hasFDerivAt_form3 {P Q R : ℝ × ℝ × ℝ → ℝ} {a : ℝ × ℝ × ℝ} (hP : DifferentiableAt ℝ P a)
    (hQ : DifferentiableAt ℝ Q a) (hR : DifferentiableAt ℝ R a) :
    HasFDerivAt (form3 P Q R)
      ((fderiv ℝ P a).smulRight (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
        (fderiv ℝ Q a).smulRight
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
        (fderiv ℝ R a).smulRight
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) a :=
  ((hP.hasFDerivAt.smul_const (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).add
    (hQ.hasFDerivAt.smul_const
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).add
    (hR.hasFDerivAt.smul_const
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

lemma form3_symm_iff {P Q R : ℝ × ℝ × ℝ → ℝ} {a : ℝ × ℝ × ℝ} (hP : DifferentiableAt ℝ P a)
    (hQ : DifferentiableAt ℝ Q a) (hR : DifferentiableAt ℝ R a) :
    (∀ x y, fderiv ℝ (form3 P Q R) a x y = fderiv ℝ (form3 P Q R) a y x) ↔
      pdy3 P a = pdx3 Q a ∧ pdz3 P a = pdx3 R a ∧ pdz3 Q a = pdy3 R a := by
  have key : ∀ x y : ℝ × ℝ × ℝ, fderiv ℝ (form3 P Q R) a x y =
      fderiv ℝ P a x * y.1 + fderiv ℝ Q a x * y.2.1 + fderiv ℝ R a x * y.2.2 := by
    intro x y
    rw [(hasFDerivAt_form3 hP hQ hR).fderiv]
    simp
  simp only [key]
  unfold pdx3 pdy3 pdz3
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h (0, 1, 0) (1, 0, 0)
    · simpa using h (0, 0, 1) (1, 0, 0)
    · simpa using h (0, 0, 1) (0, 1, 0)
  · rintro ⟨h1, h2, h3⟩ x y
    rw [clm_apply_triple (fderiv ℝ P a) x, clm_apply_triple (fderiv ℝ P a) y,
      clm_apply_triple (fderiv ℝ Q a) x, clm_apply_triple (fderiv ℝ Q a) y,
      clm_apply_triple (fderiv ℝ R a) x, clm_apply_triple (fderiv ℝ R a) y]
    linear_combination (x.2.1 * y.1 - x.1 * y.2.1) * h1 + (x.2.2 * y.1 - x.1 * y.2.2) * h2 +
      (x.2.2 * y.2.1 - x.2.1 * y.2.2) * h3

lemma curl3_eq_zero_iff {P Q R : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ} :
    curl3 P Q R p = 0 ↔ pdy3 P p = pdx3 Q p ∧ pdz3 P p = pdx3 R p ∧ pdz3 Q p = pdy3 R p := by
  unfold curl3
  simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3.symm, h2, h1.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3.symm, h2, h1.symm⟩

/-- OpenStax Calculus 3:Theorem 6.18 (CA-648; also CA-631 and CA-630 in space). On an open convex set, a
`C¹` space field is conservative iff its curl vanishes, i.e. the three cross partials agree
(`curl3_eq_zero_iff`). The book assumes simply connected; here convex. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.18, p. 677"]
theorem isConservative3_iff_curl3_eq_zero {P Q R : ℝ × ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ × ℝ)}
    (hU : IsOpen U) (hc : Convex ℝ U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hR : ContDiffOn ℝ 1 R U) :
    IsConservative3 P Q R U ↔ ∀ p ∈ U, curl3 P Q R p = 0 := by
  have hPd : ∀ p ∈ U, DifferentiableAt ℝ P p := fun p hp =>
    (hP.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hQd : ∀ p ∈ U, DifferentiableAt ℝ Q p := fun p hp =>
    (hQ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hRd : ∀ p ∈ U, DifferentiableAt ℝ R p := fun p hp =>
    (hR.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  constructor
  · rintro ⟨f, hf⟩ p hp
    rw [curl3_eq_zero_iff, ← form3_symm_iff (hPd p hp) (hQd p hp) (hRd p hp)]
    intro v w
    have := second_derivative_symmetric_of_eventually (f := f) (f' := form3 P Q R)
      (Filter.eventually_of_mem (hU.mem_nhds hp) hf)
      (hasFDerivAt_form3 (hPd p hp) (hQd p hp) (hRd p hp)) v w
    rwa [(hasFDerivAt_form3 (hPd p hp) (hQd p hp) (hRd p hp)).fderiv]
  · intro h
    exact hc.exists_forall_hasFDerivAt_of_fderiv_symmetric hU
      (fun p hp => (hasFDerivAt_form3 (hPd p hp) (hQd p hp)
        (hRd p hp)).differentiableAt.differentiableWithinAt)
      (fun p hp => (form3_symm_iff (hPd p hp) (hQd p hp) (hRd p hp)).2
        (curl3_eq_zero_iff.1 (h p hp)))

end Poincare

section InverseSquare

/-- `x² + y² + z²`. -/
noncomputable def sq3 (p : ℝ × ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

/-- The factor `(x² + y² + z²)^(-3/2)` of the inverse-square field. -/
noncomputable def invSqρ (p : ℝ × ℝ × ℝ) : ℝ := sq3 p ^ (-(3 / 2 : ℝ))

/-- First component of the inverse-square field `r / ‖r‖³`. -/
noncomputable def invSqP (p : ℝ × ℝ × ℝ) : ℝ := p.1 * invSqρ p
/-- Second component of the inverse-square field `r / ‖r‖³`. -/
noncomputable def invSqQ (p : ℝ × ℝ × ℝ) : ℝ := p.2.1 * invSqρ p
/-- Third component of the inverse-square field `r / ‖r‖³`. -/
noncomputable def invSqR (p : ℝ × ℝ × ℝ) : ℝ := p.2.2 * invSqρ p

lemma hasFDerivAt_sq3 (p : ℝ × ℝ × ℝ) :
    HasFDerivAt sq3 (form3 (fun q => 2 * q.1) (fun q => 2 * q.2.1) (fun q => 2 * q.2.2) p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_fst (p := p.2)).comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd (p := p.2)).comp p hasFDerivAt_snd
  have := ((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)
  have e : form3 (fun q => 2 * q.1) (fun q => 2 * q.2.1) (fun q => 2 * q.2.2) p =
      (2 • p.1 ^ (2 - 1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
        (2 • p.2.1 ^ (2 - 1)) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        (2 • p.2.2 ^ (2 - 1)) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  rw [e]
  exact this

lemma sq3_ne_zero {p : ℝ × ℝ × ℝ} (hp : p ≠ 0) : sq3 p ≠ 0 := by
  intro h
  apply hp
  unfold sq3 at h
  have h1 : p.1 ^ 2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1, sq_nonneg p.2.2]
  have h2 : p.2.1 ^ 2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1, sq_nonneg p.2.2]
  have h3 : p.2.2 ^ 2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1, sq_nonneg p.2.2]
  exact Prod.ext (pow_eq_zero_iff (two_ne_zero) |>.1 h1)
    (Prod.ext (pow_eq_zero_iff (two_ne_zero) |>.1 h2) (pow_eq_zero_iff (two_ne_zero) |>.1 h3))

lemma fderiv_coord_mul (l : ℝ × ℝ × ℝ →L[ℝ] ℝ) {g : ℝ × ℝ × ℝ → ℝ}
    (hg : ∀ q, g q = l q * invSqρ q) {p : ℝ × ℝ × ℝ} (hp : sq3 p ≠ 0) (v : ℝ × ℝ × ℝ) :
    fderiv ℝ g p v = l v * invSqρ p +
      l p * (-3 * sq3 p ^ (-(5 / 2 : ℝ)) * (p.1 * v.1 + p.2.1 * v.2.1 + p.2.2 * v.2.2)) := by
  have hρ : HasFDerivAt invSqρ ((-(3 / 2 : ℝ) * sq3 p ^ (-(3 / 2 : ℝ) - 1)) •
      form3 (fun q => 2 * q.1) (fun q => 2 * q.2.1) (fun q => 2 * q.2.2) p) p :=
    (hasFDerivAt_sq3 p).rpow_const (Or.inl hp)
  have hm0 := l.hasFDerivAt.mul hρ
  have hm : HasFDerivAt (fun q => l q * invSqρ q) _ p := hm0
  have hg' : g = fun q => l q * invSqρ q := funext hg
  rw [hg', hm.fderiv]
  have e : (-(3 / 2 : ℝ) - 1) = -(5 / 2) := by norm_num
  simp only [e, add_apply, smul_apply, form3_apply, smul_eq_mul]
  ring

lemma fderiv_invSqP {p : ℝ × ℝ × ℝ} (hp : sq3 p ≠ 0) (v : ℝ × ℝ × ℝ) :
    fderiv ℝ invSqP p v = v.1 * invSqρ p +
      p.1 * (-3 * sq3 p ^ (-(5 / 2 : ℝ)) * (p.1 * v.1 + p.2.1 * v.2.1 + p.2.2 * v.2.2)) := by
  have := fderiv_coord_mul (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (g := invSqP)
    (fun q => rfl) hp v
  simpa using this

lemma fderiv_invSqQ {p : ℝ × ℝ × ℝ} (hp : sq3 p ≠ 0) (v : ℝ × ℝ × ℝ) :
    fderiv ℝ invSqQ p v = v.2.1 * invSqρ p +
      p.2.1 * (-3 * sq3 p ^ (-(5 / 2 : ℝ)) * (p.1 * v.1 + p.2.1 * v.2.1 + p.2.2 * v.2.2)) := by
  have := fderiv_coord_mul ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (g := invSqQ) (fun q => rfl) hp v
  simpa using this

lemma fderiv_invSqR {p : ℝ × ℝ × ℝ} (hp : sq3 p ≠ 0) (v : ℝ × ℝ × ℝ) :
    fderiv ℝ invSqR p v = v.2.2 * invSqρ p +
      p.2.2 * (-3 * sq3 p ^ (-(5 / 2 : ℝ)) * (p.1 * v.1 + p.2.1 * v.2.1 + p.2.2 * v.2.2)) := by
  have := fderiv_coord_mul ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (g := invSqR) (fun q => rfl) hp v
  simpa using this

/-- OpenStax Calculus 3:Example 6.54 (CA-645). The inverse-square field
`F = ⟨x, y, z⟩ / (x² + y² + z²)^(3/2)` has zero curl away from the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.54, p. 676"]
theorem curl3_invSq {p : ℝ × ℝ × ℝ} (hp : p ≠ 0) : curl3 invSqP invSqQ invSqR p = 0 := by
  have hs := sq3_ne_zero hp
  simp only [curl3, pdx3, pdy3, pdz3, fderiv_invSqP hs, fderiv_invSqQ hs, fderiv_invSqR hs]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

/-- OpenStax Calculus 3:Example 6.80 (CA-663). The inverse-square field has zero divergence away from the
origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.80, p. 737"]
theorem div3_invSq {p : ℝ × ℝ × ℝ} (hp : p ≠ 0) : div3 invSqP invSqQ invSqR p = 0 := by
  have hs := sq3_ne_zero hp
  have key : sq3 p ^ (-(3 / 2 : ℝ)) = sq3 p ^ (-(5 / 2 : ℝ)) * sq3 p := by
    rw [← Real.rpow_add_one hs]; norm_num
  have hs' : sq3 p = p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := rfl
  simp only [div3, pdx3, pdy3, pdz3, fderiv_invSqP hs, fderiv_invSqQ hs, fderiv_invSqR hs,
    invSqρ, key]
  simp only [hs']
  simp
  ring

end InverseSquare

section Stream

/-- OpenStax Calculus 3:§6.4 Definition (CA-635). `g` is a stream function of `F = (P, Q)` on `U`:
`g_y = P` and `g_x = -Q`. -/
@[kb "openstaxcalculus2016" "3:§6.4 Definition (stream function), p. 654"]
def IsStreamFunction (g : ℝ × ℝ → ℝ) (P Q : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ U, HasFDerivAt g (form2 (fun q => -Q q) P p) p

/-- OpenStax Calculus 3:§6.4 (CA-635). The planar field `(P, Q)` is source free on `U` if its flux across
every closed regular `C¹` curve in `U` is zero. -/
@[kb "openstaxcalculus2016" "3:§6.4 text (source free), p. 653"]
def IsSourceFree2 (P Q : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ (x y : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 x → ContDiff ℝ 1 y →
    (∀ t ∈ uIcc a b, (x t, y t) ∈ U) → (x a, y a) = (x b, y b) →
    (∀ t ∈ uIcc a b, speed2 x y t ≠ 0) → flux2 P Q x y a b = 0

/-- OpenStax Calculus 3:§6.4 (CA-635). A planar field with a stream function is source free (its flux
across a closed curve is the change of the stream function). -/
@[kb "openstaxcalculus2016" "3:§6.4 Definition (stream function), p. 654"]
theorem IsStreamFunction.isSourceFree2 {g P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (h : IsStreamFunction g P Q U) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) :
    IsSourceFree2 P Q U := by
  intro x y a b hx hy hU hclosed hreg
  rw [flux2_eq_lineIntegral2 hreg, lineIntegral2_ftli (f := g) h hQ.neg hP hx hy hU, hclosed,
    sub_self]

lemma IsStreamFunction.pd {g P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (h : IsStreamFunction g P Q U)
    {q : ℝ × ℝ} (hq : q ∈ U) : pdx2 g q = -Q q ∧ pdy2 g q = P q := by
  have := (h q hq).fderiv
  simp [pdx2, pdy2, this]

/-- OpenStax Calculus 3:Theorem 6.14 (CA-642), stream-function form. If `F = (P, Q)` has a `C²` stream
function on an open set then `div F = 0` there. (The book's hypothesis is source free; deducing the
stream function from source freeness is not formalized.) -/
@[kb "openstaxcalculus2016" "3:Theorem 6.14, p. 671"]
theorem IsStreamFunction.div2_eq_zero {g P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : IsStreamFunction g P Q U) (hg : ContDiffOn ℝ 2 g U) {p : ℝ × ℝ} (hp : p ∈ U) :
    div2 P Q p = 0 := by
  have hgp : ContDiffAt ℝ 2 g p := hg.contDiffAt (hU.mem_nhds hp)
  have eP : pdy2 g =ᶠ[nhds p] P :=
    Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => (h.pd hq).2
  have eQ : (fun q => -pdx2 g q) =ᶠ[nhds p] Q :=
    Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => by
      show -pdx2 g q = Q q
      rw [(h.pd hq).1]; ring
  have hdx : pdx2 P p = fderiv ℝ (fun q => fderiv ℝ g q (0, 1)) p (1, 0) := by
    unfold pdx2; rw [← eP.fderiv_eq]; rfl
  have hdy : pdy2 Q p = - fderiv ℝ (fun q => fderiv ℝ g q (1, 0)) p (0, 1) := by
    unfold pdy2; rw [← eQ.fderiv_eq, fderiv_fun_neg]; rfl
  unfold div2
  rw [hdx, hdy, mixed_symm hgp (0, 1) (1, 0)]
  ring

end Stream

section Harmonic

/-- The Laplacian `f_xx + f_yy` of a function of the plane. -/
noncomputable def laplacian2 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := pdx2 (pdx2 f) p + pdy2 (pdy2 f) p

/-- OpenStax Calculus 3:§6.4 Fact (CA-638). A potential function `f` (`∇f = (P, Q)`) of a conservative
planar field with `div F = 0` on an open set is harmonic: `f_xx + f_yy = 0`. -/
@[kb "openstaxcalculus2016" "3:§6.4 Fact (potentials of source-free conservative fields are harmonic), p. 655"]
theorem laplacian2_eq_zero_of_potential {f P Q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ∀ p ∈ U, HasFDerivAt f (form2 P Q p) p) (hdiv : ∀ p ∈ U, div2 P Q p = 0) {p : ℝ × ℝ}
    (hp : p ∈ U) : laplacian2 f p = 0 := by
  have eP : pdx2 f =ᶠ[nhds p] P := Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => by
    simp [pdx2, (hf q hq).fderiv]
  have eQ : pdy2 f =ᶠ[nhds p] Q := Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => by
    simp [pdy2, (hf q hq).fderiv]
  have := hdiv p hp
  unfold laplacian2 div2 at *
  unfold pdx2 pdy2 at *
  rw [eP.fderiv_eq, eQ.fderiv_eq]
  exact this

end Harmonic
