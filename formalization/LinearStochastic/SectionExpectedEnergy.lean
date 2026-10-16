import LinearStochastic.ProcessQuadraticInner
import LinearStochastic.ExpectedQuadraticGenerator
import LinearStochastic.SectionQuadraticEnergy

/-! The full time-indexed expected energy identity is deduced from the
actual integral equation on every prefix, with the same continuous S² path. -/
noncomputable section
namespace LinearStochastic.SectionExpectedEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality VectorHorizonRestriction
open ProcessQuadraticInner ExpectedQuadraticGenerator
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem prefix_energy
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (hH : H.IsSymmetric)
    (ξ : Ω → E) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E)
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X) (fun i => (C i).compLp X) X (R T))
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b hW hWm T ξ
      (A.compLp X) (fun i => (C i).compLp X) (t:ℝ))
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, inner ℝ (R t ω) (H (R t ω)) ∂μ) =
      (∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ) +
      ∫ s in Ioc 0 (t:ℝ), generator (μ:=μ) R H A C s.toNNReal := by
  have hs := SectionHorizonRestriction.section_restrict b hW hWm ht ξ (R T) (R t)
    (A.compLp X) X (fun i => (C i).compLp X) hX (he t ht)
  have ha : restrict ht (A.compLp X) = A.compLp (restrict ht X) := restrict_comp ht A X
  have hz : (fun i => restrict ht ((C i).compLp X)) =
      (fun i => (C i).compLp (restrict ht X)) := funext (fun i => restrict_comp ht (C i) X)
  rw [ha,hz] at hs
  have hi := SectionQuadraticEnergy.energy_identity b hW hWm hpair hchannels t H hH ξ (R t)
    hξ hξ0 (A.compLp (restrict ht X)) (restrict ht X) (fun i => (C i).compLp (restrict ht X)) hs
  simp_rw [comp_compLp] at hi
  rw [bilinear_restrict_inner ht X R hr A H] at hi
  have hd (i : ι) := bilinear_restrict_inner ht X R hr (C i) (H.comp (C i))
  simp_rw [hd] at hi
  rw [integral_generator T R hm hc h2 H A C t ht]
  simpa only [ContinuousLinearMap.comp_apply,add_assoc] using hi

end LinearStochastic.SectionExpectedEnergy
