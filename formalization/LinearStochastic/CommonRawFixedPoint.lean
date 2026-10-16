import LinearStochastic.CommonLocalCoefficients
import LinearStochastic.CommonLocalUniqueness

/-! Actual raw integral-solution equations imply the H² Picard equation.
The premise is an initial-value Lebesgue/constructed-Itô decomposition, not a
fixed-point equality. One common probability-one set supplies the product-a.e.
identity without assuming arbitrary fixed-time representatives jointly measurable. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonRawFixedPoint
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonItoMultichannel CommonVectorPicard
open CommonPicardRealization CommonInitialPredictable CommonLocalSolution
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- A simultaneous horizon identity pulls back through the two product
projections. No joint measurability is inferred from separate time fibres. -/
theorem product_ae_of_horizon_indistinguishable (T : ℝ≥0)
    {E : Type*} {R S : ℝ≥0 → Ω → E}
    (h : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → R t ω = S t ω) :
    Function.uncurry R =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry S := by
  have ht : ∀ᵐ t ∂timeMeasure_T T, t ≤ T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ht.2
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae h,
    Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
  exact hz z.1 ht

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Any process represented by X and satisfying the genuine initial-value
integral equation has X as an actual Picard fixed point. Matrix coefficient
classes are the literal row sums, whose raw-state semantics is proved in
CommonLocalCoefficients.linearInput_ae. -/
theorem raw_integral_implies_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (R : κ → ℝ≥0 → Ω → ℝ)
    (hXR : ∀ a, (X a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (R a))
    (heq : ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → R a t ω =
      ξ a ω + (∫ s in Ioc (0 : ℝ≥0) t, driftInput T A B u X a (s,ω) ∂timeMeasure) +
      ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (noiseInput T C D u X i a) t ω) :
    picardMap hW hWm hWc i₀ T A B C D (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X = X := by
  funext a
  have hd := CommonDriftS2.driftContinuousMod_indistinguishable T (hWm i₀) (driftInput T A B u X a)
  have hr : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → R a t ω = stateProcess hWm i₀ T A B C D ξ u X a t ω := by
    filter_upwards [heq,hd] with ω he hd
    intro t ht
    change R a t ω = ξ a ω + CommonDriftPredictable.driftContinuousMod T (hWm i₀) (driftInput T A B u X a) t ω + _
    rw [hd t ht]
    exact he a t ht
  have hp : picardMap hW hWm hWc i₀ T A B C D
      (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u X a) := by
    rw [picardMap_coordinate]
    exact assembled_ae_realization hW hWm hWc i₀ T (hξ a) (hξ2 a) _ _
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod
    (Lp.stronglyMeasurable _)
  have hpamb : (picardMap hW hWm hWc i₀ T A B C D
      (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u X a) :=
    ae_of_ae_trim 𝓕.predictable_le_prod hp
  filter_upwards [hpamb,product_ae_of_horizon_indistinguishable T hr,hXR a] with z hp hr hx
  exact hp.trans (hr.symm.trans hx.symm)

/-- A raw-state drift equation has the identical fixed-point consequence;
the change from raw coefficients is proved by actual product-a.e. row identities
and simultaneous equality of their Lebesgue primitives. -/
theorem raw_coefficients_imply_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (R : κ → ℝ≥0 → Ω → ℝ)
    (hXR : ∀ a, (X a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (R a))
    (v : ν → ℝ≥0 → Ω → ℝ)
    (hu : ∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b))
    (heq : ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → R a t ω =
      ξ a ω + (∫ s in Ioc (0 : ℝ≥0) t,
        ((∑ b, A a b * R b s ω) + ∑ b, B a b * v b s ω) ∂timeMeasure) +
      ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (noiseInput T C D u X i a) t ω) :
    picardMap hW hWm hWc i₀ T A B C D (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X = X := by
  apply raw_integral_implies_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X R hXR
  have hall : ∀ᵐ ω ∂μ, ∀ a t, t ≤ T →
      (∫ s in Ioc (0 : ℝ≥0) t, driftInput T A B u X a (s,ω) ∂timeMeasure) =
      ∫ s in Ioc (0 : ℝ≥0) t, ((∑ b, A a b * R b s ω) + ∑ b, B a b * v b s ω) ∂timeMeasure := by
    rw [ae_all_iff]
    intro a
    exact CommonLocalCoefficients.primitive_congr_spacetime T
      (f := fun s ω ↦ driftInput T A B u X a (s,ω))
      (g := fun s ω ↦ (∑ b, A a b * R b s ω) + ∑ b, B a b * v b s ω)
      (CommonLocalCoefficients.linearInput_ae T A B X u R v hXR hu a)
  filter_upwards [hall,heq] with ω hh he
  intro a t ht
  rw [hh a t ht]
  exact he a t ht

include hW hWc in
/-- Two actual raw integral solutions with continuous paths coincide on one
probability-one set for every time. The fixed-point equations are derived from
the displayed Lebesgue/Itô equations, rather than required as assumptions. -/
theorem raw_solutions_indistinguishable (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X Y : κ → H2 𝓕 μ T)
    (R S : κ → ℝ≥0 → Ω → ℝ)
    (hXR : ∀ a, (X a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (R a))
    (hYS : ∀ a, (Y a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (S a))
    (hR : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t ↦ R a t ω) (Iic T))
    (hS : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t ↦ S a t ω) (Iic T))
    (v : ν → ℝ≥0 → Ω → ℝ)
    (hu : ∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b))
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1)
    (heR : ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → R a t ω =
      ξ a ω + (∫ s in Ioc (0 : ℝ≥0) t,
        ((∑ b, A a b * R b s ω) + ∑ b, B a b * v b s ω) ∂timeMeasure) +
      ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (noiseInput T C D u X i a) t ω)
    (heS : ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → S a t ω =
      ξ a ω + (∫ s in Ioc (0 : ℝ≥0) t,
        ((∑ b, A a b * S b s ω) + ∑ b, B a b * v b s ω) ∂timeMeasure) +
      ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (noiseInput T C D u Y i a) t ω) :
    ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → R a t ω = S a t ω := by
  have hX := raw_coefficients_imply_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X R hXR v hu heR
  have hY := raw_coefficients_imply_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u Y S hYS v hu heS
  obtain ⟨Z,_,hz⟩ := exists_unique_fixedPoint hW hWm hWc i₀ T A B C D
    (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u hc
  have he : X = Y := (hz X hX).trans (hz Y hY).symm
  rw [ae_all_iff]
  intro a
  apply CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT (R a) (S a)
    (hR.mono fun ω hω ↦ hω a) (hS.mono fun ω hω ↦ hω a)
  rw [he] at hXR
  exact (hXR a).symm.trans (hYS a)

end LinearStochastic.CommonRawFixedPoint
