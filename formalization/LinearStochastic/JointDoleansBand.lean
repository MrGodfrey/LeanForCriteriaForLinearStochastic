import LinearStochastic.JointNaturalForward
import LinearStochastic.CommonDirectionBand

noncomputable section
namespace LinearStochastic.JointDoleansBand
open MeasureTheory ProbabilityTheory CommonItoMultichannel
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)

def exponential (v : ι → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((∑ i, v i * W i t ω) - (∑ i, v i ^ 2) * (t : ℝ) / 2)

/-- Every actual vector exponential band, including the zero direction, is a
sum of constructed coordinate Itô integrals on the original joint natural
filtration, with each integrand supported on that same band. -/
theorem band_mem_range (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (v : ι → ℝ) (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    ∃ φ : ι → Lp ℝ 2 (spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T),
      (∀ i, ∀ᵐ p ∂spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T,
        p.1 ≤ a → φ i p = 0) ∧
      (∀ i, ∀ᵐ p ∂spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T,
        b < p.1 → φ i p = 0) ∧
      (fun ω => exponential W v b ω - exponential W v a ω) =ᵐ[μ]
        sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T φ := by
  classical
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  by_cases hv : ∑ i, v i ^ 2 = 0
  · have hv0 (i : ι) : v i = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp hv
      exact sq_eq_zero_iff.mp (hz i (Finset.mem_univ i))
    have he (t : ℝ≥0) (ω : Ω) : exponential W v t ω = 1 := by simp [exponential,hv0]
    refine ⟨fun _ => 0,fun _ => ?_,fun _ => ?_,?_⟩
    · exact (Lp.coeFn_zero ℝ 2 _).mono (fun p hp _ => hp)
    · exact (Lp.coeFn_zero ℝ 2 _).mono (fun p hp _ => hp)
    · have hz : sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T (fun _ => 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact (channelIntegral hW hWm i T).map_zero
      rw [hz]
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
      rw [he,he,sub_self,hω]
      rfl
  · let r := Real.sqrt (∑ i, v i ^ 2)
    have hpos : 0 < ∑ i, v i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))) (Ne.symm hv)
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hpos.le
    let c : ι → ℝ := fun i => v i / r
    have hc : ∑ i, c i ^ 2 = 1 := by
      simp only [c,div_pow]
      rw [←Finset.sum_div,←hr2,div_self (pow_ne_zero 2 hr.ne')]
    let B := JointBrownianDirections.direction W c
    have hB : IsPreBrownianReal B μ := JointBrownianDirections.direction_preBrownian W hW hInd c hc
    have hBm : ∀ t, Measurable (B t) := JointBrownianDirections.direction_measurable W hWm c
    have hBc : ∀ ω, Continuous fun t => B t ω := JointBrownianDirections.direction_continuous W hWc c
    letI : CommonItoIsometry.ForwardIndependent B (JointCylinderGeneration.natural W hWm) μ :=
      JointNaturalForward.directionForward W hW hWm hInd c
    obtain ⟨φ,ha,hb,he⟩ := CommonDirectionBand.band_mem_range
      (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm hB hBm c
      (fun _ _ => rfl) hBc a b T hab hbT r
    have halg (t : ℝ≥0) (ω : Ω) :
        Real.exp (r * B t ω - r ^ 2 * (t : ℝ) / 2) = exponential W v t ω := by
      have hm : r * B t ω = ∑ i, v i * W i t ω := by
        simp only [B,JointBrownianDirections.direction,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [c]
        field_simp
      rw [hm,hr2]
      rfl
    refine ⟨φ,ha,hb,?_⟩
    simpa only [halg] using he

/-- A past-measurable multiplier of a vector exponential band is an actual
multichannel integral when the actual sample-side product lies in L². -/
theorem factored_band_mem_range (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (v : ι → ℝ) (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (Z : Ω → ℝ) (hZm : Measurable[JointCylinderGeneration.natural W hWm a] Z)
    (hZ : MemLp (fun ω => Z ω * (exponential W v b ω - exponential W v a ω)) 2 μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    ∃ φ : ι → Lp ℝ 2 (spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T),
      (∀ i, ∀ᵐ p ∂spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T,
        p.1 ≤ a → φ i p = 0) ∧
      (∀ i, ∀ᵐ p ∂spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T,
        b < p.1 → φ i p = 0) ∧
      (fun ω => Z ω * (exponential W v b ω - exponential W v a ω)) =ᵐ[μ]
        sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T φ := by
  classical
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  by_cases hv : ∑ i, v i ^ 2 = 0
  · have hv0 (i : ι) : v i = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp hv
      exact sq_eq_zero_iff.mp (hz i (Finset.mem_univ i))
    have he (t : ℝ≥0) (ω : Ω) : exponential W v t ω = 1 := by simp [exponential,hv0]
    refine ⟨fun _ => 0,fun _ => ?_,fun _ => ?_,?_⟩
    · exact (Lp.coeFn_zero ℝ 2 _).mono (fun p hp _ => hp)
    · exact (Lp.coeFn_zero ℝ 2 _).mono (fun p hp _ => hp)
    · have hz : sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T (fun _ => 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact (channelIntegral hW hWm i T).map_zero
      rw [hz]
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
      rw [he,he,sub_self,mul_zero,hω]
      rfl
  · let r := Real.sqrt (∑ i, v i ^ 2)
    have hpos : 0 < ∑ i, v i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (v i))) (Ne.symm hv)
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hpos.le
    let c : ι → ℝ := fun i => v i / r
    have hc : ∑ i, c i ^ 2 = 1 := by
      simp only [c,div_pow]
      rw [←Finset.sum_div,←hr2,div_self (pow_ne_zero 2 hr.ne')]
    let B := JointBrownianDirections.direction W c
    have hB : IsPreBrownianReal B μ := JointBrownianDirections.direction_preBrownian W hW hInd c hc
    have hBm : ∀ t, Measurable (B t) := JointBrownianDirections.direction_measurable W hWm c
    have hBc : ∀ ω, Continuous fun t => B t ω := JointBrownianDirections.direction_continuous W hWc c
    letI : CommonItoIsometry.ForwardIndependent B (JointCylinderGeneration.natural W hWm) μ :=
      JointNaturalForward.directionForward W hW hWm hInd c
    have halg (t : ℝ≥0) (ω : Ω) :
        Real.exp (r * B t ω - r ^ 2 * (t : ℝ) / 2) = exponential W v t ω := by
      have hm : r * B t ω = ∑ i, v i * W i t ω := by
        simp only [B,JointBrownianDirections.direction,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [c]
        field_simp
      rw [hm,hr2]
      rfl
    have hZ' : MemLp (fun ω => Z ω * (Real.exp (r * B b ω - r ^ 2 * (b : ℝ) / 2) -
        Real.exp (r * B a ω - r ^ 2 * (a : ℝ) / 2))) 2 μ := by
      simpa only [halg] using hZ
    obtain ⟨φ,ha,hb,he⟩ := CommonDirectionBand.factored_band_mem_range
      (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm hB hBm c
      (fun _ _ => rfl) hBc a b T hab hbT r Z hZm hZ'
    refine ⟨φ,ha,hb,?_⟩
    simpa only [halg] using he

end LinearStochastic.JointDoleansBand
