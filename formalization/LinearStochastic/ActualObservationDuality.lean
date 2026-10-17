module

public import LinearStochastic.HilbertLocalSolution
public import LinearStochastic.ZeroObservationFlag

@[expose] public section

/-! Actual terminal annihilation and actual adjoint observation. In the local
theorem the required forward state is genuinely constructed, rather than
supplied as an abstract terminal-map/duality oracle. -/
noncomputable section
namespace LinearStochastic.ActualObservationDuality
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality HilbertLocalSolution

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Orthogonality to terminals of the actual forward SDE from zero initial
state. The quantifier ranges over the original coefficient equations. -/
def AnnihilatesForwardTerminals (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) (YT : Ω → E) : Prop :=
  ∀ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E),
    SectionIntegralSolution b hW hWm T 0 (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT →
      (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = 0

/-- A true zero observation annihilates all actual forward terminals. -/
theorem annihilates_of_observation_zero
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0) :
    AnnihilatesForwardTerminals (𝓕 := 𝓕) b hW hWm T A B C D YT := by
  intro u X XT hX
  have h := SectionLinearDuality.forward_backward_duality b hW hWm hpair hchannels T A B C D
    0 η XT YT MemLp.zero hη stronglyMeasurable_zero hη0 X Y u Z hX hY
  simpa only [Pi.zero_apply,inner_zero_left,integral_zero,hobs,inner_zero_right,add_zero] using h

/-- Testing a terminal annihilator against the actual observation as a
control proves zero observation through its genuine L² norm squared. -/
theorem observation_zero_of_test_solution
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (hAnn : AnnihilatesForwardTerminals (𝓕 := 𝓕) b hW hWm T A B C D YT)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E)
    (hX : SectionIntegralSolution b hW hWm T 0
      (A.compLp X + B.compLp (B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i)))
      (fun j => (C j).compLp X + (D j).compLp
        (B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i))) X XT) :
    B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0 := by
  let u := B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i)
  have h := SectionLinearDuality.forward_backward_duality b hW hWm hpair hchannels T A B C D
    0 η XT YT MemLp.zero hη stronglyMeasurable_zero hη0 X Y u Z hX hY
  rw [hAnn u X XT hX] at h
  have he : inner ℝ u u = 0 := by
    simpa only [Pi.zero_apply,inner_zero_left,integral_zero,zero_add] using h.symm
  exact (inner_self_eq_zero).mp he

/-- The terminal-annihilator characterization on the genuine short horizon.
The forward test solution is supplied by the constructed Picard theorem. -/
theorem local_annihilator_iff (c : OrthonormalBasis τ ℝ U)
    (hWc : ∀ i ω, Continuous fun t ↦ W i t ω) (i₀ : ι)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hc : CommonVectorPicard.rate (𝓕 := 𝓕) (μ := μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT) :
    AnnihilatesForwardTerminals (𝓕 := 𝓕) b hW hWm T A B C D YT ↔
      B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0 := by
  constructor
  · intro hAnn
    let u := B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i)
    obtain ⟨X,XT,hX,_,_⟩ := exists_section_solution b c hW hWm hWc i₀ T A B C D
      0 stronglyMeasurable_zero MemLp.zero u hc
    exact observation_zero_of_test_solution b hW hWm hpair hchannels T A B C D
      η YT hη hη0 Y Z hY hAnn X XT hX
  · exact annihilates_of_observation_zero b hW hWm hpair hchannels T A B C D η YT hη hη0 Y Z hY

/-- On the constructed short horizon, every actual continuous adjoint
solution whose terminal value annihilates the true forward SDE terminals has
zero terminal value when the paper's actual obstruction flag vanishes. -/
theorem local_annihilator_terminal_zero [FiniteDimensional ℝ E]
    (c : OrthonormalBasis τ ℝ U)
    (hWc : ∀ i ω, Continuous fun t ↦ W i t ω) (i₀ : ι)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hc : CommonVectorPicard.rate (𝓕 := 𝓕) (μ := μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (η YT : Ω → E) (hη : MemLp η 2 μ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (r : ContinuousRealization T η Y YT)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (hAnn : AnnihilatesForwardTerminals (𝓕 := 𝓕) b hW hWm T A B C D YT) : YT =ᵐ[μ] 0 := by
  apply ZeroObservationFlag.terminal_zero_of_flag_bot b hW hWm hpair hchannels T hT
    A B C D η YT Y Z hY r _ hflag
  exact (local_annihilator_iff b hW hWm c hWc i₀ hpair hchannels T A B C D hc
    η YT hη hη0 Y Z hY).mp hAnn

#print axioms local_annihilator_terminal_zero
end LinearStochastic.ActualObservationDuality
