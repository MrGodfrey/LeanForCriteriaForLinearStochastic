module

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted from the pinned MathFin WienerExponentialTotality module to arbitrary
finite real random coordinates with explicit, genuine L² exponential moments.
The same sample space and measure are retained; no Brownian natural-filtration
surjectivity is assumed here.
-/
public import MathFin.Foundations.WienerExponentialTotality

@[expose] public section

noncomputable section
namespace LinearStochastic.FiniteExponentialTotality
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem memLp_exp_linear {ι : Type*} (X : ι → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hXe : ∀ i c, MemLp (fun ω => Real.exp (c * X i ω)) 2 μ)
    (lam : ι → ℝ) (S : Finset ι) :
    ∀ c : ℝ, MemLp (fun ω ↦ Real.exp (c * ∑ i ∈ S, lam i * X i ω)) 2 μ := by
  classical
  induction S using Finset.induction_on with
  | empty => intro c; simpa using memLp_const (μ := μ) (1 : ℝ)
  | insert a S ha ih =>
    intro c
    have hsum : Measurable fun ω ↦ ∑ i ∈ insert a S, lam i * X i ω :=
      Finset.measurable_sum _ fun i _ ↦ (hXm i).const_mul _
    have hmeas : AEStronglyMeasurable
        (fun ω ↦ Real.exp (c * ∑ i ∈ insert a S, lam i * X i ω)) μ :=
      ((hsum.const_mul c).exp).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    have hrw : (fun ω ↦ Real.exp (c * ∑ i ∈ insert a S, lam i * X i ω) ^ 2)
        = fun ω ↦ Real.exp (2 * c * lam a * X a ω)
            * Real.exp (2 * c * ∑ i ∈ S, lam i * X i ω) := by
      funext ω
      rw [Finset.sum_insert ha, sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hrw]
    exact (hXe a (2 * c * lam a)).integrable_mul (ih (2 * c))

omit [IsProbabilityMeasure μ] in
/-- Integration against the density `ofReal ∘ f` is integration of the positive part of `f`
against the integrand: `∫ g d(f⁺·μ) = ∫ f⁺·g dμ`. -/
lemma integral_withDensity_ofReal_eq {f : Ω → ℝ} (hf : AEMeasurable f μ) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (f ω))
      = ∫ ω, max (f ω) 0 * g ω ∂μ := by
  have hnn : AEMeasurable (fun ω ↦ (f ω).toNNReal) μ :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hf
  rw [show (fun ω ↦ ENNReal.ofReal (f ω)) = fun ω ↦ (((f ω).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul₀ hnn]
  simp [NNReal.smul_def, Real.coe_toNNReal']

omit [IsProbabilityMeasure μ] in
/-- Integrability against the density `ofReal ∘ f`, in the same positive-part form. -/
lemma integrable_withDensity_ofReal_iff {f : Ω → ℝ} (hf : AEMeasurable f μ) (g : Ω → ℝ) :
    Integrable g (μ.withDensity fun ω ↦ ENNReal.ofReal (f ω))
      ↔ Integrable (fun ω ↦ max (f ω) 0 * g ω) μ := by
  have hnn : AEMeasurable (fun ω ↦ (f ω).toNNReal) μ :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hf
  rw [show (fun ω ↦ ENNReal.ofReal (f ω)) = fun ω ↦ (((f ω).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul₀ hnn]
  simp [NNReal.smul_def, Real.coe_toNNReal']

/-- Exponential totality for an actual finite coordinate vector with all real
exponential moments in L². Orthogonality implies every coordinate cylinder has
zero signed integral; the proof uses actual Jordan measures and Laplace uniqueness. -/
theorem setIntegral_eq_zero_of_iSup_comap {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXe : ∀ i c, MemLp (fun ω => Real.exp (c * X i ω)) 2 μ)
    {f : Ω → ℝ} (hfL2 : MemLp f 2 μ)
    (hperp : ∀ lam : ι → ℝ, ∫ ω, f ω * Real.exp (∑ i, lam i * X i ω) ∂μ = 0)
    {A : Set Ω} (hA : MeasurableSet[⨆ i : ι, MeasurableSpace.comap (X i) inferInstance] A) :
    ∫ ω in A, f ω ∂μ = 0 := by
  classical
  have hf0 : ∫ ω, f ω ∂μ = 0 := by simpa using hperp 0
  have hfae : AEMeasurable f μ := hfL2.aestronglyMeasurable.aemeasurable
  have hfaeneg : AEMeasurable (fun ω ↦ -f ω) μ := hfae.neg
  have hfint : Integrable f μ := memLp_one_iff_integrable.mp (hfL2.mono_exponent one_le_two)
  have hXmeas : Measurable fun (ω : Ω) (i : ι) ↦ X i ω :=
    measurable_pi_lambda fun i ↦ hXm i
  obtain ⟨G, hGmeas, hGA⟩ :
      ∃ G : Set (ι → ℝ), MeasurableSet G ∧ (fun (ω : Ω) (i : ι) ↦ X i ω) ⁻¹' G = A := by
    rw [← MeasurableSpace.comap_process_pi fun i ↦ X i] at hA
    exact hA
  have hAmeas : MeasurableSet A := hGA ▸ hXmeas hGmeas
  -- The Jordan pieces of `f·μ`, as finite measures.
  have hfnegL2 : MemLp (fun ω ↦ -f ω) 2 μ := hfL2.neg
  have hposL2 : MemLp (fun ω ↦ max (f ω) 0) 2 μ :=
    hfL2.mono (hfae.max aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rcases le_total 0 (f ω) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, norm_zero]; exact norm_nonneg _)
  have hnegL2 : MemLp (fun ω ↦ max (-f ω) 0) 2 μ :=
    hfnegL2.mono (hfae.neg.max aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rcases le_total 0 (-f ω) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, norm_zero]; exact norm_nonneg _)
  set nuPos : Measure Ω := μ.withDensity (fun ω ↦ ENNReal.ofReal (f ω)) with hnuPos
  set nuNeg : Measure Ω := μ.withDensity (fun ω ↦ ENNReal.ofReal (-f ω)) with hnuNeg
  haveI : IsFiniteMeasure nuPos := isFiniteMeasure_withDensity_ofReal hfint.2
  haveI : IsFiniteMeasure nuNeg := isFiniteMeasure_withDensity_ofReal hfint.neg.2
  -- The total masses agree, because `f` is centered.
  have huniv : nuPos Set.univ = nuNeg Set.univ := by
    have hp : nuPos Set.univ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
      rw [hnuPos, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hm : nuNeg Set.univ = ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ := by
      rw [hnuNeg, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hsub : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal
        = (∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ).toReal := by
      have hsplit := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfint
      rw [hf0] at hsplit
      linarith
    rw [hp, hm]
    exact (ENNReal.toReal_eq_toReal_iff' (hp ▸ measure_ne_top nuPos Set.univ)
      (hm ▸ measure_ne_top nuNeg Set.univ)).mp hsub
  -- Equality of the two laws of the coordinate vector.
  have hmap : nuPos.map (fun (ω : Ω) (i : ι) ↦ X i ω)
      = nuNeg.map (fun (ω : Ω) (i : ι) ↦ X i ω) := by
    haveI : IsFiniteMeasure (nuPos.map fun (ω : Ω) (i : ι) ↦ X i ω) :=
      Measure.isFiniteMeasure_map _ _
    haveI : IsFiniteMeasure (nuNeg.map fun (ω : Ω) (i : ι) ↦ X i ω) :=
      Measure.isFiniteMeasure_map _ _
    refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
    set lam : ι → ℝ := fun i ↦ L (fun j ↦ if i = j then (1 : ℝ) else 0) with hlam
    have hLX (ω : Ω) : L (fun i ↦ X i ω) = ∑ i, lam i * X i ω := by
      conv_lhs => rw [pi_eq_sum_univ fun i ↦ X i ω]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul]; simp [hlam, mul_comm]
    have hexpL2 (r : ℝ) : MemLp (fun ω ↦ Real.exp (r * ∑ i, lam i * X i ω)) 2 μ :=
      memLp_exp_linear X hXm hXe lam Finset.univ r
    have hmgf : mgf (fun ω ↦ ∑ i, lam i * X i ω) nuPos
        = mgf (fun ω ↦ ∑ i, lam i * X i ω) nuNeg := by
      funext r
      have hz := hperp fun i ↦ r * lam i
      have hre (ω : Ω) : ∑ i, r * lam i * X i ω = r * ∑ i, lam i * X i ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ mul_assoc _ _ _
      simp only [hre] at hz
      have hip : Integrable (fun ω ↦ max (f ω) 0
          * Real.exp (r * ∑ i, lam i * X i ω)) μ := hposL2.integrable_mul (hexpL2 r)
      have him : Integrable (fun ω ↦ max (-f ω) 0
          * Real.exp (r * ∑ i, lam i * X i ω)) μ := hnegL2.integrable_mul (hexpL2 r)
      have hp : mgf (fun ω ↦ ∑ i, lam i * X i ω) nuPos r
          = ∫ ω, max (f ω) 0 * Real.exp (r * ∑ i, lam i * X i ω) ∂μ := by
        rw [show mgf (fun ω ↦ ∑ i, lam i * X i ω) nuPos r
            = ∫ ω, Real.exp (r * ∑ i, lam i * X i ω) ∂nuPos from rfl, hnuPos,
          integral_withDensity_ofReal_eq hfae]
      have hm : mgf (fun ω ↦ ∑ i, lam i * X i ω) nuNeg r
          = ∫ ω, max (-f ω) 0 * Real.exp (r * ∑ i, lam i * X i ω) ∂μ := by
        rw [show mgf (fun ω ↦ ∑ i, lam i * X i ω) nuNeg r
            = ∫ ω, Real.exp (r * ∑ i, lam i * X i ω) ∂nuNeg from rfl, hnuNeg,
          integral_withDensity_ofReal_eq hfaeneg]
      rw [hp, hm, ← sub_eq_zero, ← integral_sub hip him]
      have hpt (ω : Ω) : max (f ω) 0 * Real.exp (r * ∑ i, lam i * X i ω)
          - max (-f ω) 0 * Real.exp (r * ∑ i, lam i * X i ω)
          = f ω * Real.exp (r * ∑ i, lam i * X i ω) := by
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      simp only [hpt]
      exact hz
    have hIES : integrableExpSet (fun ω ↦ ∑ i, lam i * X i ω) nuPos = Set.univ := by
      refine Set.eq_univ_of_forall fun r ↦ ?_
      show Integrable (fun ω ↦ Real.exp (r * ∑ i, lam i * X i ω)) nuPos
      rw [hnuPos, integrable_withDensity_ofReal_iff hfae]
      exact hposL2.integrable_mul (hexpL2 r)
    have hnull : nuPos = 0 ↔ nuNeg = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero, huniv]
    have hcx := eqOn_complexMGF_of_mgf' hmgf hnull
      (show Complex.I ∈ {z : ℂ | z.re ∈ interior
        (integrableExpSet (fun ω ↦ ∑ i, lam i * X i ω) nuPos)} by
        rw [Set.mem_ofPred_eq, hIES, interior_univ]; trivial)
    have hcfd (ν : Measure Ω) :
        charFunDual (ν.map fun (ω : Ω) (i : ι) ↦ X i ω) L
          = complexMGF (fun ω ↦ ∑ i, lam i * X i ω) ν Complex.I := by
      have hcont : Continuous fun v : ι → ℝ ↦ Complex.exp ((L v : ℂ) * Complex.I) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
      rw [charFunDual_apply, integral_map hXmeas.aemeasurable hcont.aestronglyMeasurable,
        show complexMGF (fun ω ↦ ∑ i, lam i * X i ω) ν Complex.I
          = ∫ ω, Complex.exp (Complex.I * ((∑ i, lam i * X i ω : ℝ) : ℂ)) ∂ν from rfl]
      exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
        simp only [hLX ω]; rw [mul_comm])
    rw [hcfd nuPos, hcfd nuNeg]
    exact hcx
  -- A coordinate cylinder is measured equally by the two pieces.
  have hnuA : nuPos A = nuNeg A := by
    rw [← hGA, ← Measure.map_apply hXmeas hGmeas, ← Measure.map_apply hXmeas hGmeas, hmap]
  have ep : ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ = nuPos A := by
    rw [hnuPos, withDensity_apply _ hAmeas]
  have em : ∫⁻ ω in A, ENNReal.ofReal (-f ω) ∂μ = nuNeg A := by
    rw [hnuNeg, withDensity_apply _ hAmeas]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfint.restrict, ep, em, hnuA, sub_self]


end LinearStochastic.FiniteExponentialTotality
