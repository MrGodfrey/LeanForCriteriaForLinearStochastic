import LinearStochastic.CommonLocalSolution
import LinearStochastic.CommonContinuousUniqueness

/-! Indistinguishability of continuous representatives of the actual controlled
H² fixed point. A positive horizon and a single common probability-one set
are derived through the genuine time-probability product equality bridge. -/
noncomputable section
namespace LinearStochastic.CommonLocalUniqueness
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open CommonItoMultichannel CommonVectorPicard
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

theorem fixedPoint_representatives_indistinguishable (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T) (X Y : κ → H2 𝓕 μ T)
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1)
    (hX : picardMap hW hWm hWc i₀ T A B C D η u X = X)
    (hY : picardMap hW hWm hWc i₀ T A B C D η u Y = Y)
    (R S : κ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t ↦ R a t ω) (Set.Iic T))
    (hS : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t ↦ S a t ω) (Set.Iic T))
    (hXR : ∀ a, X a =ᵐ[spacetimeMeasure 𝓕 μ T] Function.uncurry (R a))
    (hYS : ∀ a, Y a =ᵐ[spacetimeMeasure 𝓕 μ T] Function.uncurry (S a)) :
    ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → R a t ω = S a t ω := by
  obtain ⟨Z,_,hu⟩ := exists_unique_fixedPoint hW hWm hWc i₀ T A B C D η u hc
  have he : X = Y := (hu X hX).trans (hu Y hY).symm
  rw [ae_all_iff]
  intro a
  apply CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT (R a) (S a)
    (hR.mono fun ω hω ↦ hω a) (hS.mono fun ω hω ↦ hω a)
  have hr := hXR a
  rw [he] at hr
  exact ae_eq_of_ae_eq_trim (hr.symm.trans (hYS a))

end LinearStochastic.CommonLocalUniqueness
