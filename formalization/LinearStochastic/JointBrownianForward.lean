import LinearStochastic.JointBrownian
import LinearStochastic.CommonItoIsometry

noncomputable section
namespace LinearStochastic.JointBrownian
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable (ι : Type*) [Fintype ι]

/-- The full future process vector is independent of the complete joint past. -/
theorem joint_past_independent_forward (s : ℝ≥0) :
    IndepFun (pastPath ι s) (fun ω : ι → (ℝ≥0 → ℝ) ↦ fun i u ↦
      process ι i (s+u) ω - process ι i s ω) (law ι) := by
  apply indepFun_pi_pair (fun _ : ι ↦ gaussianLimit)
    (fun _ ω (u : Set.Iic s) ↦ brownian u ω)
    (fun _ ω u ↦ brownian (s+u) ω - brownian s ω)
    (fun _ ↦ measurable_pi_lambda _ (fun u ↦ measurable_brownian u))
    (fun _ ↦ measurable_pi_lambda _ (fun u ↦
      (measurable_brownian (s+u)).sub (measurable_brownian s)))
  intro i
  exact (isBrownianReal_brownian.toIsPreBrownianReal.indepFun_shift s).symm

/-- Genuine common-filtration Brownian assumptions for every coordinate,
proved from the constructed joint model rather than supplied by a user. -/
instance commonForwardIndependent (i : ι) :
    CommonItoIsometry.ForwardIndependent (process ι i) (filtration ι) (law ι) where
  adapted t := (process_measurable_past ι i le_rfl).stronglyMeasurable
  indep s := by
    have h := (joint_past_independent_forward ι s).comp measurable_id (measurable_pi_apply i)
    exact h

end LinearStochastic.JointBrownian
