import LinearStochastic.CommonForwardBounds

/-! Actual small-time zero-initial SDE state estimates. The vanishing bound
comes from the constructed Picard operator and its actual integral norms. -/
noncomputable section
set_option maxHeartbeats 800000
namespace LinearStochastic.CommonSmallTimeBound
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Topology
open CommonVectorPicard CommonLocalSolution CommonSolutionData CommonForwardBounds CommonPicardHorizon
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- The actual zero-input Picard map fixes the zero state. -/
theorem picard_zero (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    picardMap (𝓕:=𝓕) hW hWm hWc i₀ T A B C D 0 0 0 = 0 := by
  have hi (i : ι) : itoVector (𝓕:=𝓕) (κ:=κ) hW hWm hWc i T 0 = 0 := by
    have hh := itoVector_sub (𝓕:=𝓕) (κ:=κ) hW hWm hWc i T 0 0
    simpa only [sub_self] using hh
  simp only [picardMap,map_zero,add_zero,hi,Finset.sum_const_zero]

include hWc in
/-- Every actual zero-initial solution satisfies the quantitative small-time
state bound. It does not need to be the particular fixed point selected by an
existence proof. -/
theorem state_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D 0 u)
    (hc : CommonUniformHorizon.bound T A C < 1) :
    ‖q.X‖ ≤ inputBound T B D*‖u‖/(1-CommonUniformHorizon.bound T A C) := by
  have hi : (fun j : κ ↦ CommonInitialPredictable.initialH2
      (show StronglyMeasurable[𝓕 0] ((0 : κ → Ω → ℝ) j) from stronglyMeasurable_zero)
      (show MemLp ((0 : κ → Ω → ℝ) j) 2 μ from MemLp.zero) T) = 0 := by
    funext j
    apply Lp.ext
    exact (CommonInitialPredictable.initialH2_ae stronglyMeasurable_zero MemLp.zero T).trans
      (Lp.coeFn_zero ℝ 2 _).symm
  have hf := CommonSolutionFixedPoint.solution_fixedPoint hW hWm hWc i₀ T A B C D
    0 (fun _ ↦ stronglyMeasurable_zero) (fun _ ↦ MemLp.zero) u q
  rw [hi] at hf
  have hb := fixedPoint_difference hW hWm hWc i₀ T A B C D 0 0 q.X 0 u 0 hc hf
    (picard_zero (𝓕:=𝓕) hW hWm hWc i₀ T A B C D)
  simpa only [sub_zero,sub_self,norm_zero,zero_add] using hb

/-- Explicit coefficient-only factor for an additive-noise system. -/
def additiveFactor (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (D : ι → Matrix κ ν ℝ) : ℝ := inputBound T B D/(1-(T:ℝ)*matrixSize A)

omit hW hWm hWc [IsProbabilityMeasure μ] in
/-- The actual quantitative factor tends to zero with the interval length. -/
theorem additiveFactor_tendsto (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (D : ι → Matrix κ ν ℝ) :
    Filter.Tendsto (fun T : ℝ≥0 ↦ additiveFactor T A B D) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun T : ℝ≥0 ↦ additiveFactor T A B D) 0 := by
    unfold additiveFactor inputBound
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp
  simpa only [additiveFactor,inputBound,NNReal.coe_zero,zero_mul,Real.sqrt_zero,zero_add,sub_zero,
    zero_div] using hc.tendsto

include hWc in
/-- Specialization to actual additive diffusion: no state-dependent diffusion
is used in the terminal spike construction. -/
theorem additive_state_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (D : ι → Matrix κ ν ℝ)
    (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B (fun _ ↦ 0) D 0 u)
    (hc : (T:ℝ)*matrixSize A < 1) :
    ‖q.X‖ ≤ additiveFactor T A B D*‖u‖ := by
  have hz : CommonUniformHorizon.bound T A (fun _ : ι ↦ (0 : Matrix κ κ ℝ)) =
      (T:ℝ)*matrixSize A := by simp [CommonUniformHorizon.bound,matrixSize]
  have hb := state_bound hW hWm hWc i₀ T A B (fun _ ↦ 0) D u q (by rw [hz]; exact hc)
  rw [hz] at hb
  simpa only [additiveFactor,div_mul_eq_mul_div] using hb
end LinearStochastic.CommonSmallTimeBound
