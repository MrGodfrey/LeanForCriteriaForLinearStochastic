import LinearStochastic.JointCylinderGeneration
import LinearStochastic.FiniteExponentialTotality

noncomputable section
namespace LinearStochastic.JointExponentialTotality
open MeasureTheory ProbabilityTheory Filter Topology JointCylinderGeneration
open scoped NNReal ENNReal
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))

include hW in
/-- Actual finite-channel Brownian natural L² variables are determined by
exponentials of their finite dyadic coordinate vectors. Neither a martingale
representation hypothesis nor an independence/totality oracle is used. -/
theorem eq_zero_of_orthogonal_finite_exponentials
    (hWc : ∀ i ω, Continuous fun t => W i t ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[natural W hWm T] (⇑F) μ)
    (hperp : ∀ k : ℕ,
      ∀ lam : (ι × {t : ℝ≥0 // t ∈ MathFin.dyadicGrid T k}) → ℝ,
      ∫ ω, F ω * Real.exp (∑ q, lam q * W q.1 q.2 ω) ∂μ = 0) : F = 0 := by
  let f : Ω → ℝ := hFm.mk (⇑F)
  have hfae : (⇑F) =ᵐ[μ] f := hFm.ae_eq_mk
  have hfsm : StronglyMeasurable[natural W hWm T] f := hFm.stronglyMeasurable_mk
  have hfL2 : MemLp f 2 μ := MemLp.ae_eq hfae (Lp.memLp F)
  have hfint : Integrable f μ := hfL2.integrable one_le_two
  have hcond (k : ℕ) : μ[f | cylinders W hWm T k] =ᵐ[μ] 0 := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq ((cylinders W hWm T).le k) hfint
      (fun A _ _ => integrable_zero _ _ _) (fun A hAm _ => ?_) aestronglyMeasurable_zero).symm
    let Q := ι × {t : ℝ≥0 // t ∈ MathFin.dyadicGrid T k}
    have hp (lam : Q → ℝ) :
        ∫ ω, f ω * Real.exp (∑ q, lam q * W q.1 q.2 ω) ∂μ = 0 := by
      have hh := hperp k lam
      rwa [integral_congr_ae (g := fun ω => f ω * Real.exp (∑ q, lam q * W q.1 q.2 ω))
        (by filter_upwards [hfae] with ω hω; rw [hω])] at hh
    have hAcyl : MeasurableSet[⨆ q : Q, MeasurableSpace.comap (W q.1 q.2) inferInstance] A := by
      change MeasurableSet[cylinderSigma W T k] A at hAm
      rwa [cylinderSigma_eq_coordinates] at hAm
    simp only [Pi.zero_apply, integral_zero]
    exact (FiniteExponentialTotality.setIntegral_eq_zero_of_iSup_comap
      (fun q : Q => W q.1 q.2) (fun q => hWm q.1 q.2)
      (fun q c => MathFin.memLp_exp_mul_eval (hW q.1) q.2 c)
      hfL2 hp hAcyl).symm
  have hsm : StronglyMeasurable[⨆ k : ℕ, cylinders W hWm T k] f := by
    rw [iSup_cylinders_eq_natural W hWm hWc T]
    exact hfsm
  have hlim := hfint.tendsto_eLpNorm_condExp (ℱ := cylinders W hWm T) hsm
  have heq (k : ℕ) :
      eLpNorm (μ[f | cylinders W hWm T k] - f) 1 μ = eLpNorm f 1 μ := by
    have hsub : (μ[f | cylinders W hWm T k] - f) =ᵐ[μ] -f := by
      filter_upwards [hcond k] with ω hω
      simp [hω]
    rw [eLpNorm_congr_ae hsub, eLpNorm_neg]
  simp only [heq] at hlim
  have hf0 : f =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff hfL2.aestronglyMeasurable one_ne_zero).mp
      (tendsto_nhds_unique hlim tendsto_const_nhds).symm
  exact Lp.ext_iff.mpr ((hfae.trans hf0).trans (Lp.coeFn_zero ℝ 2 μ).symm)

end LinearStochastic.JointExponentialTotality
