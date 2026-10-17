module

public import LinearStochastic.JointBrownianForward
public import LinearStochastic.CommonItoCLM

@[expose] public section

noncomputable section
namespace LinearStochastic.JointBrownian
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
variable (ι : Type*) [Fintype ι]

/-- One common predictable spacetime measure for all Brownian channels. -/
def predictableMeasure (T : ℝ≥0) :=
  ((CommonItoCLM.timeMeasure_T T).prod (law ι)).trim (filtration ι).predictable_le_prod

/-- Full predictable L² integration against channel i, under the common joint
filtration. This is the constructed dense extension, not a supplied operator. -/
def itoIntegral (i : ι) (T : ℝ≥0) :
    Lp ℝ 2 (predictableMeasure ι T) →L[ℝ] Lp ℝ 2 (law ι) :=
  CommonItoCLM.itoIntegralCLM_T (𝓕 := filtration ι)
    (process_isBrownian ι i).toIsPreBrownianReal T (process_measurable ι i)

theorem itoIntegral_norm (i : ι) (T : ℝ≥0) (f : Lp ℝ 2 (predictableMeasure ι T)) :
    ‖itoIntegral ι i T f‖ = ‖f‖ :=
  CommonItoCLM.itoIntegralCLM_T_norm (𝓕 := filtration ι)
    (process_isBrownian ι i).toIsPreBrownianReal T (process_measurable ι i) f

/-- Bilinear isometry for arbitrary joint-predictable L² integrands. -/
theorem itoIntegral_inner (i : ι) (T : ℝ≥0)
    (f g : Lp ℝ 2 (predictableMeasure ι T)) :
    ⟪itoIntegral ι i T f, itoIntegral ι i T g⟫_ℝ = ⟪f,g⟫_ℝ :=
  CommonItoCLM.itoIntegralCLM_T_inner (𝓕 := filtration ι)
    (process_isBrownian ι i).toIsPreBrownianReal T (process_measurable ι i) f g

/-- Consistency with the literal finite sum over arbitrary overlapping
predictable rectangles: there is no selected time grid in this definition. -/
theorem itoIntegral_simple (i : ι) (T : ℝ≥0)
    (V : CommonItoCLM.TBoundedSP (𝓕 := filtration ι) T (process_measurable ι i)) :
    itoIntegral ι i T
      (CommonItoCLM.simpleAssembly_T (𝓕 := filtration ι) (μ := law ι)
        T (process_measurable ι i) V) =
      CommonItoL2.itoSimpleLp (process_isBrownian ι i).toIsPreBrownianReal
        (process_measurable ι i) V.val :=
  CommonItoCLM.itoIntegralCLM_T_simpleAssembly_T (𝓕 := filtration ι)
    (process_isBrownian ι i).toIsPreBrownianReal T (process_measurable ι i) V

end LinearStochastic.JointBrownian
