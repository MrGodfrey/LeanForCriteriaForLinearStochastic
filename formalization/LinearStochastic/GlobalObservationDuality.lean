import LinearStochastic.HilbertGlobalSolution
import LinearStochastic.ActualObservationDuality

/-! Actual terminal-annihilator duality on every finite horizon, using the
proved global forward solution for the observation test control. -/
noncomputable section
namespace LinearStochastic.GlobalObservationDuality
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality ActualObservationDuality

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include c hWc hpair hchannels in
/-- On every horizon a true adjoint solution's terminal annihilates the
actual forward reachable set exactly when its actual observation is zero. -/
theorem annihilator_iff (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y YT) :
    AnnihilatesForwardTerminals (𝓕:=𝓕) b hW hWm T A B C D YT ↔
      B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i) = 0 := by
  constructor
  · intro hAnn
    let u := B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i)
    obtain ⟨X,XT,hX,_,_⟩ := HilbertGlobalSolution.exists_section_solution b c hW hWm hWc
      i₀ T A B C D 0 stronglyMeasurable_zero MemLp.zero u
    exact observation_zero_of_test_solution b hW hWm hpair hchannels T A B C D
      η YT hη hη0 Y Z hY hAnn X XT hX
  · exact annihilates_of_observation_zero b hW hWm hpair hchannels T A B C D η YT hη hη0 Y Z hY

include c hWc hpair hchannels in
/-- For every positive horizon, an actual continuous adjoint solution whose
terminal annihilates all forward terminals must vanish at the terminal when
the paper's actual obstruction flag vanishes. -/
theorem annihilator_terminal_zero [FiniteDimensional ℝ E] (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (r : ContinuousRealization T η Y YT)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (hAnn : AnnihilatesForwardTerminals (𝓕:=𝓕) b hW hWm T A B C D YT) : YT =ᵐ[μ] 0 := by
  apply ZeroObservationFlag.terminal_zero_of_flag_bot b hW hWm hpair hchannels T hT
    A B C D η YT Y Z hY r _ hflag
  exact (annihilator_iff b c hW hWm hWc hpair hchannels i₀ T A B C D η YT hη hη0 Y Z hY).mp hAnn

end LinearStochastic.GlobalObservationDuality
