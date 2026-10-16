import LinearStochastic.CommonProgressiveComparison

/-! Actual continuous integral solution data implies the real H² Picard
equation. Fixed-time identities are converted using proven joint measurability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSolutionFixedPoint
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonInitialPredictable CommonPicardRealization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- A genuine solution satisfies Picard because its raw path and the actual
integral realization are equal in space-time; no fixed-point premise is used. -/
theorem solution_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) :
    picardMap hW hWm hWc i₀ T A B C D (fun b ↦ initialH2 (hξ b) (hξ2 b) T) u q.X = q.X := by
  funext b
  have he : ∀ t, t ≤ T → q.path b t =ᵐ[μ] stateProcess hWm i₀ T A B C D ξ u q.X b t := by
    intro t ht
    exact (q.equation b t ht).trans (realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ ht).symm
  have hprod := CommonProgressiveComparison.product_ae_of_modification T (q.progressive b)
    ((realization_predictable hW hWm hWc i₀ T (hξ b) _ _).isStronglyProgressive.isProgressive) he
  have hclass : picardMap hW hWm hWc i₀ T A B C D
      (fun b ↦ initialH2 (hξ b) (hξ2 b) T) u q.X b =ᵐ[CommonItoMultichannel.spacetimeMeasure 𝓕 μ T]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u q.X b) := by
    rw [picardMap_coordinate]
    exact assembled_ae_realization hW hWm hWc i₀ T (hξ b) (hξ2 b) _ _
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have ha : (picardMap hW hWm hWc i₀ T A B C D
      (fun b ↦ initialH2 (hξ b) (hξ2 b) T) u q.X b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u q.X b) := ae_of_ae_trim 𝓕.predictable_le_prod hclass
  exact ha.trans (hprod.symm.trans (q.representative b).symm)

/-- Changing an initial representative on a probability-zero set changes no
actual path, class or integral identity. This is a genuine constructor. -/
def withInitial (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ ζ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (he : ∀ b, ξ b =ᵐ[μ] ζ b) :
    Solution hW hWm T A B C D ζ u where
  X := q.X
  path := q.path
  progressive := q.progressive
  continuous := q.continuous
  squareSup := q.squareSup
  representative := q.representative
  initial b := (q.initial b).trans (he b)
  equation b t ht := by
    filter_upwards [q.equation b t ht,he b] with ω hω he
    exact hω.trans (by rw [he])

include hWc in
/-- Actual local path uniqueness, including the zero horizon, follows from
integral equations and genuine continuity rather than assumed fixed points. -/
theorem local_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q r : Solution hW hWm T A B C D ξ u) (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  by_cases hT : 0 < T
  · have hq := solution_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u q
    have hr := solution_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u r
    obtain ⟨Z,_,hz⟩ := exists_unique_fixedPoint hW hWm hWc i₀ T A B C D
      (fun b ↦ initialH2 (hξ b) (hξ2 b) T) u hc
    have hX : q.X = r.X := (hz q.X hq).trans (hz r.X hr).symm
    rw [ae_all_iff]
    intro b
    apply CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT
      (q.path b) (r.path b) (q.continuous b) (r.continuous b)
    have he := q.representative b
    rw [hX] at he
    exact he.symm.trans (r.representative b)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
    rw [ae_all_iff]
    intro b
    filter_upwards [q.initial b,r.initial b] with ω hq hr
    intro t ht
    have ht0 : t = 0 := le_antisymm (hz ▸ ht) zero_le
    rw [ht0]
    exact hq.trans hr.symm
end LinearStochastic.CommonSolutionFixedPoint
