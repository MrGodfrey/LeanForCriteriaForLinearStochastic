import LinearStochastic.BSDEEnergy
import LinearStochastic.ProgressivePredictable
import LinearStochastic.CommonItoMultichannel

noncomputable section
namespace LinearStochastic.BSDETerminal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open CommonItoMultichannel
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

/-- Actual inclusion of the predictable trimmed L² space into spacetime L². -/
def untrim : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ]
    Lp ℝ 2 ((CommonItoCLM.timeMeasure_T T).prod μ) :=
  (lpMeas ℝ ℝ 𝓕.predictable 2 ((CommonItoCLM.timeMeasure_T T).prod μ)).subtypeL.comp
    (lpMeasToLpTrimLie ℝ ℝ 2 ((CommonItoCLM.timeMeasure_T T).prod μ)
      𝓕.predictable_le_prod).symm.toLinearIsometry.toContinuousLinearMap

omit [IsProbabilityMeasure μ] in
theorem untrim_norm (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) : ‖untrim 𝓕 T f‖ = ‖f‖ := by
  exact (lpMeasToLpTrimLie ℝ ℝ 2 ((CommonItoCLM.timeMeasure_T T).prod μ)
    𝓕.predictable_le_prod).symm.norm_map f

omit [IsProbabilityMeasure μ] in
theorem untrim_ae (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    untrim 𝓕 T f =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] f :=
  lpTrimToLpMeas_ae_eq (𝕜 := ℝ) 𝓕.predictable_le_prod f

/-- Terminal Lebesgue integral of a genuine predictable H² drift. -/
def terminal : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ] Lp ℝ 2 μ :=
  (BSDEEnergy.terminalDriftCLM (CommonItoCLM.timeMeasure_T T) μ).comp (untrim 𝓕 T)

theorem terminal_ae (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    terminal 𝓕 T f =ᵐ[μ] fun ω => ∫ s, f (s,ω) ∂(CommonItoCLM.timeMeasure_T T) := by
  have hu := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (untrim_ae 𝓕 T f))
  filter_upwards [BSDEEnergy.terminalDrift_ae (CommonItoCLM.timeMeasure_T T) μ (untrim 𝓕 T f),hu]
    with ω hω hu
  exact hω.trans (integral_congr_ae hu)

theorem time_mass : (CommonItoCLM.timeMeasure_T T).real univ = T := by
  simp only [Measure.real,CommonItoCLM.timeMeasure_T,Measure.restrict_apply_univ]
  rw [CommonItoL2.timeMeasure_Ioc]
  simp

theorem terminal_norm (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖terminal 𝓕 T f‖ ≤ Real.sqrt (T : ℝ) * ‖f‖ := by
  have h := BSDEEnergy.terminalDrift_norm (CommonItoCLM.timeMeasure_T T) μ (untrim 𝓕 T f)
  rw [time_mass,untrim_norm] at h
  exact h

omit [IsProbabilityMeasure μ] in
/-- The raw terminal integral has true F_T strong measurability. -/
theorem terminal_stronglyMeasurable (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    StronglyMeasurable[𝓕 T] (fun ω => ∫ s, f (s,ω) ∂(CommonItoCLM.timeMeasure_T T)) := by
  have hp : IsStronglyPredictable 𝓕 (Function.curry f) := Lp.stronglyMeasurable f
  have h := ProgressivePredictable.primitive_stronglyAdapted hp.isStronglyProgressive T
  have he : ProgressivePredictable.primitive (Function.curry f) T =
      fun ω => ∫ s, f (s,ω) ∂(CommonItoCLM.timeMeasure_T T) := by
    funext ω
    exact RealTimeBridge.integral_real_extension T (fun s => f (s,ω))
  rwa [he] at h

/-- The actual terminal L² class belongs to the original F_T measurable subspace. -/
theorem terminal_aestronglyMeasurable (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    AEStronglyMeasurable[𝓕 T] (terminal 𝓕 T f) μ :=
  (terminal_stronglyMeasurable 𝓕 T f).aestronglyMeasurable.congr (terminal_ae 𝓕 T f).symm
/-- Exact identification with the manuscript's real Lebesgue interval. -/
theorem terminal_ae_real (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    terminal 𝓕 T f =ᵐ[μ] fun ω => ∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω) := by
  filter_upwards [terminal_ae 𝓕 T f] with ω hω
  exact hω.trans (RealTimeBridge.integral_real_extension T (fun s => f (s,ω))).symm

/-- The terminal drift has an actual bounded-operator norm at most sqrt(T). -/
theorem terminal_operator_norm : ‖terminal (μ := μ) 𝓕 T‖ ≤ Real.sqrt (T : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (terminal_norm 𝓕 T)
end LinearStochastic.BSDETerminal
