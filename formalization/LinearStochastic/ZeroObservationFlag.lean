module

public import LinearStochastic.SubspaceIntegralSolution
public import LinearStochastic.ContinuousRealization

@[expose] public section

/-! The genuine zero-observation induction into the paper's obstruction flag.
The inputs are an actual backward integral solution and its actual continuous
path version. Existence for an arbitrary terminal datum is not presumed here. -/
noncomputable section
namespace LinearStochastic.ZeroObservationFlag
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι]

/-- Precisely the adjoints of the original forward coefficients. -/
def coefficients (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι) :=
  ⟨A.adjoint.toLinearMap,B.adjoint.toLinearMap,
    fun i => (C i).adjoint.toLinearMap,fun i => (D i).adjoint.toLinearMap⟩

variable (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- A zero observation advances actual state membership by one obstruction
step; the required diffusion/drift membership is proved analytically. -/
theorem obstruction_step
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (r : ContinuousRealization T η Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0)
    (V : Submodule ℝ E) (hV : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, Y z ∈ V) :
    ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, Y z ∈ (coefficients A B C D).obstruction V := by
  have hend := r.endpoints_mem T hT η YT Y V hV
  have hcoeff := SubspaceIntegralSolution.coefficients_mem b hW hWm hpair hchannels T hT V η YT
    (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Y Z hY hend.1 hend.2 hV
  have hZ : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, ∀ i, Z i z ∈ V := by
    rw [ae_all_iff]
    exact hcoeff.2
  have hobsae := observation_ae B D Y Z
  rw [hobs] at hobsae
  filter_upwards [hV,hZ,hcoeff.1,hobsae,Lp.coeFn_zero U 2 (spacetimeMeasure 𝓕 μ T),
    observation_ae A C Y Z,
    Lp.coeFn_neg (A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))]
    with z hy hz hf ho h0 ha hn
  refine ⟨hy,fun i => Z i z,hz,?_,?_⟩
  · exact ho.symm.trans h0
  · change A.adjoint (Y z) + ∑ i, (C i).adjoint (Z i z) ∈ V
    rw [hn,Pi.neg_apply,ha] at hf
    exact V.neg_mem_iff.mp hf

/-- Every zero-observation backward solution lies in every stage of the
actual, untruncated obstruction recursion. -/
theorem mem_flag
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (r : ContinuousRealization T η Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0) :
    ∀ k, ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, Y z ∈ (coefficients A B C D).flag k := by
  intro k
  induction k with
  | zero => exact Filter.Eventually.of_forall (fun _ => Submodule.mem_top)
  | succ k ih =>
    exact obstruction_step b hW hWm hpair hchannels T hT A B C D η YT Y Z hY r hobs _ ih

/-- If the actual terminal flag vanishes, a zero observation forces the
terminal random variable itself to vanish almost surely. -/
theorem terminal_zero_of_flag_bot
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (η YT : Ω → E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (r : ContinuousRealization T η Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0)
    (hflag : (coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) : YT =ᵐ[μ] 0 := by
  have hm := mem_flag b hW hWm hpair hchannels T hT A B C D η YT Y Z hY r hobs
    (Module.finrank ℝ E)
  have hend := (r.endpoints_mem T hT η YT Y _ hm).2
  change ∀ᵐ ω ∂μ, YT ω = 0
  simpa only [hflag,Submodule.mem_bot,Pi.zero_apply] using hend

#print axioms terminal_zero_of_flag_bot
end LinearStochastic.ZeroObservationFlag
