import LinearStochastic.BSDEHilbertLocal
import LinearStochastic.ActualObservationDuality

/-! The actual local backward solution closes the terminal-annihilator
argument. Scalar martingale representation is an explicit separate premise. -/
noncomputable section
namespace LinearStochastic.BSDEAnnihilator
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel HilbertLocalSolution ActualObservationDuality

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include c hWc in
/-- Every actual F_T terminal annihilator is zero on a common local forward
and backward contraction horizon, provided the actual obstruction flag vanishes.
Both forward and backward solutions used in the argument are constructed. -/
theorem terminal_annihilator_eq_zero (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hf : CommonVectorPicard.rate (𝓕:=𝓕) (μ:=μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hb : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hMR : ∀ χ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 T] χ μ →
      BSDEIntegralRange.Represented hW hWm hpair hchannels T χ)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[𝓕 T] η μ)
    (hAnn : AnnihilatesForwardTerminals (𝓕:=𝓕) b hW hWm T A B C D η) : η = 0 := by
  obtain ⟨ξ,hξ,hξ2,Y,Z,hY,⟨r⟩⟩ := BSDEHilbertLocal.exists_section_backward b hW hWm
    hWc hpair hchannels i₀ T A C η hη hMR hb
  have he := local_annihilator_terminal_zero b hW hWm c hWc i₀ hpair hchannels T hT
    A B C D hf ξ η hξ2 hξ Y Z hY r hflag hAnn
  apply Lp.ext
  exact he.trans (Lp.coeFn_zero E 2 μ).symm

end LinearStochastic.BSDEAnnihilator
