import LinearStochastic.CommonItoIsometry
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

noncomputable section
namespace LinearStochastic.JointBrownianDirections
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)

def direction (c : ι → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ∑ i, c i * W i t ω

include hW hInd in
/-- Actual Gaussian finite-dimensional distributions of a linear combination
of independent Brownian coordinates, on the given probability space. -/
theorem direction_gaussian (c : ι → ℝ) : IsGaussianProcess (direction W c) μ := by
  constructor
  intro S
  have hg (i : ι) : HasGaussianLaw
      (fun ω => c i • S.restrict (fun t => W i t ω)) μ :=
    ((hW i).isGaussianProcess.hasGaussianLaw S).fun_smul (c i)
  have hi := hInd.comp (fun i f => c i • S.restrict f)
    (fun i => by fun_prop)
  have hh := hi.hasGaussianLaw_fun_sum hg
  convert! hh using 1
  ext ω t
  simp [direction]

include hW in
theorem direction_centered (c : ι → ℝ) (t : ℝ≥0) :
    ∫ ω, direction W c t ω ∂μ = 0 := by
  unfold direction
  rw [integral_finsetSum _ (fun i _ => ((hW i).integrable_eval t).const_mul (c i))]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul, (hW i).integral_eval, mul_zero]

include hW hInd in
theorem direction_covariance (c : ι → ℝ) (s t : ℝ≥0) :
    cov[direction W c s, direction W c t; μ] =
      (∑ i, c i ^ 2) * min (s : ℝ) (t : ℝ) := by
  classical
  have hLp (i : ι) (u : ℝ≥0) : MemLp (W i u) 2 μ :=
    ((hW i).isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  unfold direction
  rw [covariance_fun_sum_fun_sum
    (fun i => (hLp i s).const_mul (c i)) (fun i => (hLp i t).const_mul (c i))]
  calc
    _ = ∑ i, c i ^ 2 * min (s : ℝ) (t : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [covariance_const_mul_left,covariance_const_mul_right,(hW i).covariance_eval]
        push_cast
        ring
      · intro j _ hji
        rw [covariance_const_mul_left,covariance_const_mul_right]
        have hij := (hInd.indepFun hji.symm).comp (measurable_pi_apply s) (measurable_pi_apply t)
        change IndepFun (W i s) (W j t) μ at hij
        rw [hij.covariance_eq_zero (hLp i s) (hLp j t)]
        ring
      · simp
    _ = _ := (Finset.sum_mul _ _ _).symm

include hW hInd in
/-- A unit Euclidean direction of the actual independent coordinate Brownian
motion is a genuine scalar Brownian motion. -/
theorem direction_preBrownian (c : ι → ℝ) (hc : ∑ i, c i ^ 2 = 1) :
    IsPreBrownianReal (direction W c) μ := by
  apply (direction_gaussian W hW hInd c).isPreBrownianReal_of_covariance
    (direction_centered W hW c)
  intro s t hst
  rw [direction_covariance W hW hInd c s t,hc,one_mul,min_eq_left (NNReal.coe_le_coe.mpr hst)]

theorem direction_measurable (hWm : ∀ i t, Measurable (W i t)) (c : ι → ℝ) (t : ℝ≥0) :
    Measurable (direction W c t) := by unfold direction; fun_prop

theorem direction_continuous (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (c : ι → ℝ) (ω : Ω) : Continuous fun t => direction W c t ω := by
  unfold direction
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hWc i ω))

end LinearStochastic.JointBrownianDirections
