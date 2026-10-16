import LinearStochastic.CommonRealizationS2Bound
import LinearStochastic.CommonForwardBounds

/-! Explicit coefficient-only local S² bounds for every actual forward
solution, using its proved Picard identity and actual integral realization. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonLocalS2Bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonPicardHorizon CommonLocalSolution CommonSolutionData CommonForwardBounds
open CommonInitialPredictable CommonPicardRealization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t=>W i t ω)

def coefficientBound (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ) : ℝ :=
  Real.sqrt (T:ℝ)*matrixSize A+2*∑ i,matrixSize (C i)

theorem coefficientBound_nonneg (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ) :
    0≤coefficientBound T A C := by
  exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (matrixSize_nonneg A))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _=>matrixSize_nonneg (C i))))

def localBound (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) : ℝ :=
  1+coefficientBound T A C*((Real.sqrt (T:ℝ)+inputBound T B D)/(1-CommonUniformHorizon.bound T A C))+
    coefficientBound T B D

theorem localBound_ge_one (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hc : CommonUniformHorizon.bound T A C<1) : 1≤localBound T A B C D := by
  have hh := mul_nonneg (coefficientBound_nonneg T A C)
    (div_nonneg (add_nonneg (Real.sqrt_nonneg (T:ℝ)) (inputBound_nonneg T B D)) (sub_pos.mpr hc).le)
  have hi := coefficientBound_nonneg T B D
  unfold localBound
  linarith

omit [𝓕.IsComplete μ] [IsProbabilityMeasure μ] in
theorem matrix_coordinate_bound (T : ℝ≥0) (M : Matrix κ ν ℝ) (v : ν → H2 𝓕 μ T) (b : κ) :
    ‖matrixAction T M v b‖ ≤ matrixSize M*‖v‖ :=
  (norm_le_pi_norm (matrixAction T M v) b).trans (((matrixAction T M).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (matrixAction_norm_le T M) (norm_nonneg _)))

include hWc in
/-- Every genuine solution has the real full-path bound in terms of its
initial class, state H² class and control H² class, with literal matrix constants. -/
theorem raw_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (b : κ) :
    PathSupNorm.norm (μ:=μ) (q.path b) T ≤ ‖(hξ2 b).toLp (ξ b)‖+
      coefficientBound T A C*‖q.X‖+coefficientBound T B D*‖u‖ := by
  have hrc := realization_continuousOn hW hWm hWc i₀ T (ξ b)
    (driftInput T A B u q.X b) (fun i=>noiseInput T C D u q.X i b)
  have hset : Icc (0:ℝ≥0) T=Iic T := by ext t; simp
  rw [hset] at hrc
  have he := CommonDriftS2.indistinguishable_on_Iic T (q.path b)
    (stateProcess hWm i₀ T A B C D ξ u q.X b) (q.continuous b) hrc
    (fun t ht=>(q.equation b t ht).trans (realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ ht).symm)
  rw [PathSupNorm.congr T he]
  have hh := CommonRealizationS2Bound.realization_norm hW hWm hWc i₀ T (hξ b) (hξ2 b)
    (driftInput T A B u q.X b) (fun i=>noiseInput T C D u q.X i b)
  have hd : ‖driftInput T A B u q.X b‖ ≤ matrixSize A*‖q.X‖+matrixSize B*‖u‖ :=
    (norm_add_le _ _).trans (add_le_add (matrix_coordinate_bound T A q.X b) (matrix_coordinate_bound T B u b))
  have hn : ∑ i, ‖noiseInput T C D u q.X i b‖ ≤
      ∑ i, (matrixSize (C i)*‖q.X‖+matrixSize (D i)*‖u‖) :=
    Finset.sum_le_sum (fun i _=>(norm_add_le _ _).trans (add_le_add (matrix_coordinate_bound T (C i) q.X b) (matrix_coordinate_bound T (D i) u b)))
  apply hh.trans
  have hhd := mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg (T:ℝ))
  have hhn := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2)
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at hhn
  unfold coefficientBound
  nlinarith

omit [𝓕.IsComplete μ] in
include hWc in
/-- The local H² state bound follows from the genuine Picard equation,
comparing with the literal zero fixed point. -/
theorem state_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (hc : CommonUniformHorizon.bound T A C<1) :
    ‖q.X‖ ≤ ((Real.sqrt (T:ℝ)+inputBound T B D)/(1-CommonUniformHorizon.bound T A C))*
      (‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  have hz : picardMap (𝓕:=𝓕) (μ:=μ) hW hWm hWc i₀ T A B C D 0 0 0=0 := by
    have hi (i : ι) : itoVector (𝓕:=𝓕) (μ:=μ) hW hWm hWc i T (0:κ→H2 𝓕 μ T)=0 := by
      have hh := itoVector_sub hW hWm hWc i T (0:κ→H2 𝓕 μ T) 0
      simpa only [sub_self] using hh
    simp only [picardMap,map_zero,hi,Finset.sum_const_zero,add_zero]
  have hi : ‖fun b=>initialH2 (hξ b) (hξ2 b) T‖ ≤ Real.sqrt (T:ℝ)*‖fun b=>(hξ2 b).toLp (ξ b)‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
    intro b
    rw [initial_eq_lift T (hξ b) (hξ2 b)]
    exact (BSDEProcessLift.initialLift_norm T _).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun b=>(hξ2 b).toLp (ξ b)) b) (Real.sqrt_nonneg _))
  have hh := fixedPoint_difference hW hWm hWc i₀ T A B C D _ 0 q.X 0 u 0 hc
    (CommonSolutionFixedPoint.solution_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u q) hz
  simp only [sub_zero] at hh
  apply hh.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hc).le
  have hi0 := inputBound_nonneg T B D
  have hs0 := Real.sqrt_nonneg (T:ℝ)
  have hx0 := norm_nonneg (fun b=>(hξ2 b).toLp (ξ b))
  have hu0 := norm_nonneg u
  nlinarith [mul_nonneg hi0 hx0,mul_nonneg hs0 hu0]

include hWc in
/-- A coefficient-only full S² estimate for every actual local solution. -/
theorem local_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (hc : CommonUniformHorizon.bound T A C<1) (b : κ) :
    PathSupNorm.norm (μ:=μ) (q.path b) T ≤ localBound T A B C D*
      (‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  have hr := raw_bound hW hWm hWc i₀ T A B C D ξ hξ hξ2 u q b
  have hs := state_bound hW hWm hWc i₀ T A B C D ξ hξ hξ2 u q hc
  have hm := mul_le_mul_of_nonneg_left hs (coefficientBound_nonneg T A C)
  have hi := norm_le_pi_norm (fun b=>(hξ2 b).toLp (ξ b)) b
  have hc0 := coefficientBound_nonneg T B D
  have hI0 := norm_nonneg (fun b=>(hξ2 b).toLp (ξ b))
  have hU0 := norm_nonneg u
  unfold localBound
  nlinarith [mul_nonneg hc0 hI0]

end LinearStochastic.CommonLocalS2Bound
