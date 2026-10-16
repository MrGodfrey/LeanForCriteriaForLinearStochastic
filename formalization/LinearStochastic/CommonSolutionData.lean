import LinearStochastic.CommonPastedClasses

/-! Concrete coordinate solution data, with actual continuous S² paths and
actual Lebesgue/Itô integral equations. Local existence is constructed from
the proved Picard contraction, not included among the input fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSolutionData
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonPicardRealization CommonInitialPredictable CommonIntegralPaste
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- A genuine solution consists of actual paths, their predictable equivalence
classes and the literal coefficient integral equations. The record has no
existence, uniqueness, representation, or contraction assumption. -/
structure Solution (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) where
  X : κ → H2 𝓕 μ T
  path : κ → ℝ≥0 → Ω → ℝ
  progressive : ∀ b, IsProgressive 𝓕 (path b)
  continuous : ∀ b, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ path b t ω) (Iic T)
  squareSup : ∀ b, MemLp (ContinuousDoobL2.pathSup (path b) T) 2 μ
  representative : ∀ b, (X b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (path b)
  initial : ∀ b, path b 0 =ᵐ[μ] ξ b
  equation : ∀ b, IntegralEquation hW hWm T (ξ b)
    (driftInput T A B u X b) (fun i ↦ noiseInput T C D u X i b) (path b)

variable (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hWc in
/-- Actual local solution construction on the original sample space and common
complete filtration, for any genuine predictable H² control. -/
theorem exists_local [𝓕.IsComplete μ] (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1) :
    Nonempty (Solution hW hWm T A B C D ξ u) := by
  obtain ⟨X,hX,_⟩ := exists_unique_initial_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u hc
  refine ⟨⟨X, stateProcess hWm i₀ T A B C D ξ u X, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b
    exact (realization_predictable hW hWm hWc i₀ T (hξ b) _ _).isStronglyProgressive.isProgressive
  · intro b
    simpa only [stateProcess,←NNReal.bot_eq_zero,Icc_bot] using realization_continuousOn hW hWm hWc i₀ T (ξ b)
      (driftInput T A B u X b) (fun i ↦ noiseInput T C D u X i b)
  · intro b
    exact CommonStateS2.realization_S2 hW hWm hWc i₀ T (hξ b) (hξ2 b) _ _
  · intro b
    exact ae_of_ae_trim 𝓕.predictable_le_prod (fixedPoint_state_ae hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X hX b)
  · intro b
    exact realization_initial hW hWm hWc i₀ T (ξ b) _ _
  · intro b t ht
    exact realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ ht

/-- Every actual solution endpoint is a valid square-integrable initial datum
in its true endpoint sigma algebra. -/
theorem endpoint_memLp (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) (ξ : κ → Ω → ℝ)
    (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u) (b : κ) :
    StronglyMeasurable[𝓕 T] (q.path b T) ∧ MemLp (q.path b T) 2 μ :=
  ⟨q.progressive b |>.isStronglyProgressive.stronglyAdapted T,
    CommonProcessSpace.eval_memLp_of_s2 (q.progressive b).isStronglyProgressive.stronglyAdapted T
      (q.continuous b) (q.squareSup b) le_rfl⟩
end LinearStochastic.CommonSolutionData
