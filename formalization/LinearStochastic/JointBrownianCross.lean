module

public import LinearStochastic.JointBrownianIntegral
public import LinearStochastic.CommonItoCross

@[expose] public section

noncomputable section
namespace LinearStochastic.JointBrownian
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoCross
open scoped NNReal InnerProductSpace BigOperators
variable (ι : Type*) [Fintype ι]

/-- Actual whole Brownian paths in distinct coordinates are independent. -/
theorem channels_independent {i j : ι} (hij : i ≠ j) :
    IndepFun (fun ω t ↦ process ι i t ω) (fun ω t ↦ process ι j t ω) (law ι) := by
  exact (iIndepFun_pi (fun _ : ι ↦
    (measurable_pi_lambda (fun t ↦ measurable_brownian t)).aemeasurable)).indepFun hij

/-- Independence of the entire pair of future paths from all channel histories. -/
theorem pair_forward_independent (i j : ι) :
    PairForwardIndependent (process ι i) (process ι j) (filtration ι) (law ι) := by
  intro s
  have h := (joint_past_independent_forward ι s).comp measurable_id
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  exact h

/-- Cross-channel orthogonality for arbitrary integrands adapted to the same
joint predictable sigma-algebra, obtained by density from actual increment sums. -/
theorem itoIntegral_cross_inner {i j : ι} (hij : i ≠ j) (T : ℝ≥0)
    (f g : Lp ℝ 2 (predictableMeasure ι T)) :
    ⟪itoIntegral ι i T f, itoIntegral ι j T g⟫_ℝ = 0 :=
  CommonItoCross.itoIntegral_cross_inner
    (process_isBrownian ι i).toIsPreBrownianReal (process_isBrownian ι j).toIsPreBrownianReal
    (pair_forward_independent ι i j) (channels_independent ι hij)
    (process_measurable ι i) (process_measurable ι j) T f g

/-- The complete finite-channel integral is the actual sum of the constructed
continuous channel integrals, on the common joint predictable L2 domain. -/
def sumIntegral (T : ℝ≥0) (f : ι → Lp ℝ 2 (predictableMeasure ι T)) : Lp ℝ 2 (law ι) :=
  ∑ i, itoIntegral ι i T (f i)

/-- Full bilinear multi-channel Itô isometry, with arbitrary overlapping-grid
limits and arbitrary common-predictable L2 integrands. -/
theorem sumIntegral_inner (T : ℝ≥0) (f g : ι → Lp ℝ 2 (predictableMeasure ι T)) :
    ⟪sumIntegral ι T f, sumIntegral ι T g⟫_ℝ = ∑ i, ⟪f i,g i⟫_ℝ := by
  classical
  simp only [sumIntegral, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact itoIntegral_inner ι i T (f i) (g i)
  · intro j hj hji
    exact itoIntegral_cross_inner ι hji T (f j) (g i)
  · simp

theorem sumIntegral_norm_sq (T : ℝ≥0) (f : ι → Lp ℝ 2 (predictableMeasure ι T)) :
    ‖sumIntegral ι T f‖^2 = ∑ i, ‖f i‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using sumIntegral_inner ι T f f

end LinearStochastic.JointBrownian
