import LinearStochastic.CommonForwardGlobalBound
import LinearStochastic.HilbertBrownianUniqueness
import LinearStochastic.SectionSolutionLinearity

/-! A quantitative bound on the actual vector-valued SDE endpoint, obtained
from the genuine coordinate SDE bound and orthonormal reconstruction. -/
noncomputable section
set_option maxHeartbeats 800000
namespace LinearStochastic.HilbertEndpointBound
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open LpFiniteTensor LpOrthonormalCoordinates VectorItoProduct
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution HilbertBrownianRealization

section Norms
variable {Λ E κ : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]

theorem coordinate_norm_le (b : OrthonormalBasis κ ℝ E) (a : κ) (f : Lp E 2 ν) :
    ‖coordinate b a f‖ ≤ ‖f‖ := by
  have h := (innerSL ℝ (b a)).norm_compLp_le f
  simpa only [coordinate,innerSL_apply_norm,b.orthonormal.norm_eq_one,one_mul] using h

theorem coordinates_norm_le (b : OrthonormalBasis κ ℝ E) (f : Lp E 2 ν) :
    ‖fun a ↦ coordinate b a f‖ ≤ ‖f‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun a ↦ coordinate_norm_le b a f)

theorem norm_le_card_coordinates (b : OrthonormalBasis κ ℝ E) (f : Lp E 2 ν) :
    ‖f‖ ≤ (Fintype.card κ : ℝ)*‖fun a ↦ coordinate b a f‖ := by
  calc
    ‖f‖ = ‖∑ a, injection ν (b a) (coordinate b a f)‖ := congrArg norm (lp_expansion ν b f).symm
    _ ≤ ∑ a, ‖injection ν (b a) (coordinate b a f)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖fun a ↦ coordinate b a f‖ := by
      apply Finset.sum_le_sum
      intro a _
      have h := (ContinuousLinearMap.toSpanSingleton ℝ (b a)).norm_compLp_le (coordinate b a f)
      have he : injection ν (b a) (coordinate b a f) =
          (ContinuousLinearMap.toSpanSingleton ℝ (b a)).compLp (coordinate b a f) := by
        apply Lp.ext
        filter_upwards [injection_ae ν (b a) (coordinate b a f),
          (ContinuousLinearMap.toSpanSingleton ℝ (b a)).coeFn_compLp (coordinate b a f)] with z h1 h2
        exact h1.trans h2.symm
      have h' : ‖injection ν (b a) (coordinate b a f)‖ ≤ ‖coordinate b a f‖ := by
        rw [he]
        simpa only [ContinuousLinearMap.norm_toSpanSingleton,b.orthonormal.norm_eq_one,one_mul] using h
      exact h'.trans (norm_le_pi_norm (fun a ↦ coordinate b a f) a)
    _ = _ := by simp
end Norms

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
/-- The original Hilbert SDE's genuine terminal map is bounded in L². This
applies to any supplied actual section solution, not only a chosen version. -/
theorem terminal_bound (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Lp E 2 μ),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T
        (0 : Ω → E) (A.compLp X+B.compLp u)
        (fun i ↦ (C i).compLp X+(D i).compLp u) X XT → ‖XT‖ ≤ K*‖u‖ := by
  let a := coefficientMatrix b b A
  let β := coefficientMatrix b c B
  let γ := fun i ↦ coefficientMatrix b b (C i)
  let δ := fun i ↦ coefficientMatrix b c (D i)
  obtain ⟨K,hK,hbound⟩ := CommonForwardGlobalBound.brownian_endpoint_continuous_dependence (𝓕:=𝓕)
    hWm hW i₀ T a β γ δ
  refine ⟨(Fintype.card κ : ℝ)*K,mul_nonneg (Nat.cast_nonneg _) hK,?_⟩
  intro u X XT hX
  have hz : SectionIntegralSolution (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T
      (0 : Ω → E) (A.compLp (0 : Lp E 2 (spacetimeMeasure 𝓕 μ T))+B.compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))
      (fun i ↦ (C i).compLp (0 : Lp E 2 (spacetimeMeasure 𝓕 μ T))+(D i).compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T))) 0 (0 : Lp E 2 μ) := by
    have hh := SectionSolutionLinearity.zero_solution (𝓕:=𝓕) b
      (fun i ↦ (hW i).toIsPreBrownianReal) hWm T
    have hh' := SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b
      (fun i ↦ (hW i).toIsPreBrownianReal) hWm T 0 0 (0 : Lp E 2 μ) 0 0 (fun _ ↦ 0) hh (Lp.coeFn_zero E 2 μ)
    simpa only [←ContinuousLinearMap.compLpₗ_apply,map_zero,add_zero] using hh'
  let q := coordinateSolution b c hW hWm i₀ T A B C D (0 : Ω → E)
    stronglyMeasurable_zero (MemLp.zero) u X XT hX
  let r := coordinateSolution b c hW hWm i₀ T A B C D (0 : Ω → E)
    stronglyMeasurable_zero (MemLp.zero) 0 0 (0 : Lp E 2 μ) hz
  have heq : CommonForwardTerminal.endpoint (fun i ↦ (hW i).toIsPreBrownianReal) hWm
      T a β γ δ (fun j ω ↦ inner ℝ (b j) ((0 : Ω → E) ω)) (fun j ↦ coordinate c j u) q =
      fun j ↦ coordinate b j XT := by
    funext j
    apply Lp.ext
    exact (CommonSolutionData.endpoint_memLp (fun i ↦ (hW i).toIsPreBrownianReal) hWm
      T a β γ δ _ _ q j).2.coeFn_toLp.trans
      ((coordinateSolution_terminal b c hW hWm i₀ T A B C D (0 : Ω → E)
        stronglyMeasurable_zero MemLp.zero u X XT hX j).symm.trans (coordinate_ae b j XT).symm)
  have heq0 : CommonForwardTerminal.endpoint (fun i ↦ (hW i).toIsPreBrownianReal) hWm
      T a β γ δ (fun j ω ↦ inner ℝ (b j) ((0 : Ω → E) ω)) (fun j ↦ coordinate c j 0) r = 0 := by
    funext j
    apply Lp.ext
    filter_upwards [(CommonSolutionData.endpoint_memLp (fun i ↦ (hW i).toIsPreBrownianReal) hWm
      T a β γ δ _ _ r j).2.coeFn_toLp,
      coordinateSolution_terminal b c hW hWm i₀ T A B C D (0 : Ω → E)
        stronglyMeasurable_zero MemLp.zero 0 0 (0 : Lp E 2 μ) hz j,Lp.coeFn_zero E 2 μ,
      Lp.coeFn_zero ℝ 2 μ] with ω he ht hz hz'
    simp only [Pi.zero_apply] at *
    change (CommonSolutionData.endpoint_memLp (fun i ↦ (hW i).toIsPreBrownianReal) hWm
      T a β γ δ _ _ r j).2.toLp (r.path j T) ω = _
    exact he.trans (ht.symm.trans (by rw [hz,inner_zero_right,hz']))
  let ξ : κ → Ω → ℝ := fun j ω ↦ inner ℝ (b j) ((0 : Ω → E) ω)
  have hξ (j : κ) : StronglyMeasurable[𝓕 0] (ξ j) := by
    simpa only [ξ,Pi.zero_apply,inner_zero_right] using (stronglyMeasurable_const : StronglyMeasurable[𝓕 0] (fun _ : Ω ↦ (0 : ℝ)))
  have hξ2 (j : κ) : MemLp (ξ j) 2 μ := by
    simpa only [ξ,Pi.zero_apply,inner_zero_right] using (memLp_const (0:ℝ) : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 μ)
  have hb := hbound ξ ξ hξ hξ hξ2 hξ2 _ _ q r
  rw [heq,heq0] at hb
  simp only [sub_zero,sub_self,norm_zero,zero_add,coordinate,←ContinuousLinearMap.compLpₗ_apply,map_zero,
    ←Pi.zero_def,sub_zero] at hb
  have hc : ‖fun j ↦ coordinate b j XT‖ ≤ K*‖u‖ :=
    hb.trans (mul_le_mul_of_nonneg_left (coordinates_norm_le (mΛ:=𝓕.predictable) c u) hK)
  exact (norm_le_card_coordinates b XT).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card κ)))
end LinearStochastic.HilbertEndpointBound
