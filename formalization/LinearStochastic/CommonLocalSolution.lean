module

public import LinearStochastic.CommonPicardRealization
public import LinearStochastic.CommonPicardHorizon
public import LinearStochastic.ProgressivePredictable

@[expose] public section

/-! Local controlled matrix integral solutions with actual progressive controls
and F₀-measurable square-integrable initial coordinates. The pathwise realization
is strongly predictable, continuous almost surely, and represents the unique
predictable H² fixed point. Global concatenation and S² estimates of the complete
state, as opposed to its stochastic integral term, are not asserted here. -/
noncomputable section
namespace LinearStochastic.CommonLocalSolution
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open CommonItoMultichannel CommonVectorPicard CommonInitialPredictable CommonPicardRealization
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

def driftInput (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) : κ → H2 𝓕 μ T :=
  matrixAction T A X + matrixAction T B u

def noiseInput (T : ℝ≥0) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (i : ι) : κ → H2 𝓕 μ T :=
  matrixAction T (C i) X + matrixAction T (D i) u

def stateProcess (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (a : κ) : ℝ≥0 → Ω → ℝ :=
  realization hWm i₀ T (ξ a) (driftInput T A B u X a) (fun i ↦ noiseInput T C D u X i a)

theorem picardMap_coordinate (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (a : κ) :
    picardMap hW hWm hWc i₀ T A B C D η u X a =
      η a + driftScalar hWm i₀ T (driftInput T A B u X a) +
        ∑ i, itoScalar hW hWm hWc i T (noiseInput T C D u X i a) := by
  simp only [picardMap, Pi.add_apply, Finset.sum_apply, driftVector, driftScalar,
    driftInput, itoVector, itoScalar, noiseInput]
  rfl

/-- Every coordinate of the actual H² fixed point has the specified predictable,
a.s. continuous integral representative. -/
theorem fixedPoint_state_ae (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : picardMap hW hWm hWc i₀ T A B C D
      (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X = X) (a : κ) :
    X a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u X a) := by
  have ha := congrFun hX a
  rw [picardMap_coordinate] at ha
  rw [← ha]
  exact assembled_ae_realization hW hWm hWc i₀ T (hξ a) (hξ2 a) _ _

/-- Actual progressive input controls are retained modulo the genuine
space-time measure; existence of a predictable representative is proved,
then the genuine contraction theorem constructs the state fixed point. -/
theorem exists_progressive_control_solution (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ)
    (v : ν → ℝ≥0 → Ω → ℝ) (hv : ∀ b, IsProgressive 𝓕 (v b))
    (hv2 : ∀ b, MemLp (Function.uncurry (v b)) 2 ((CommonItoCLM.timeMeasure_T T).prod μ))
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1) :
    ∃ (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T),
      (∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (v b)) ∧
      (picardMap hW hWm hWc i₀ T A B C D (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X = X) ∧
      (∀ a, X a =ᵐ[spacetimeMeasure 𝓕 μ T]
        Function.uncurry (stateProcess hWm i₀ T A B C D ξ u X a)) ∧
      (∀ a, IsStronglyPredictable 𝓕 (stateProcess hWm i₀ T A B C D ξ u X a)) ∧
      (∀ᵐ ω ∂μ, ∀ a, ContinuousOn
        (fun t ↦ stateProcess hWm i₀ T A B C D ξ u X a t ω) (Set.Icc 0 T)) := by
  choose u hu using fun b ↦ ProgressivePredictable.exists_predictable_Lp_of_progressive
    μ (hv b) T 2 (hv2 b)
  obtain ⟨X,hX,_⟩ := exists_unique_initial_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u hc
  refine ⟨u,X,hu,hX,?_,?_,?_⟩
  · exact fun a ↦ fixedPoint_state_ae hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X hX a
  · exact fun a ↦ realization_predictable hW hWm hWc i₀ T (hξ a) _ _
  · rw [ae_all_iff]
    exact fun a ↦ realization_continuousOn hW hWm hWc i₀ T (ξ a) _ _

end LinearStochastic.CommonLocalSolution
