import LinearStochastic.CommonGlobalUniqueness
import LinearStochastic.RealTimeBridge

/-! An actual H² solution given only in almost-everywhere time sections has a
canonical continuous S² version. Measurability is established for the continuous
realization before applying Fubini; no joint measurability of raw conditional
expectation representatives is presumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSectionSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonPicardRealization CommonInitialPredictable
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Actual scalar integral sections, with the literal coefficient functions. -/
def Sections (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) : Prop :=
  ∀ b, ∀ᵐ t ∂timeMeasure_T T,
    (fun ω ↦ X b (t,ω)) =ᵐ[μ] fun ω ↦ ξ b ω +
      (∫ s in Ioc (0 : ℝ≥0) t, driftInput T A B u X b (s,ω) ∂timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
        (noiseInput T C D u X i b) ω

omit [𝓕.IsComplete μ] in
/-- The manuscript's actual real-time section identity transports to the
nonnegative clock by the genuine measure-preserving inclusion. -/
theorem sections_of_real (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : ∀ b, ∀ᵐ s ∂volume.restrict (Ioc 0 (T : ℝ)),
      (fun ω ↦ X b (s.toNNReal,ω)) =ᵐ[μ] fun ω ↦ ξ b ω +
        (∫ r in Ioc 0 s, driftInput T A B u X b (r.toNNReal,ω)) +
        ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T s.toNNReal (hWm i)
          (noiseInput T C D u X i b) ω) : Sections hW hWm T A B C D ξ u X := by
  intro b
  have he := (RealTimeBridge.coe_measurePreserving T).quasiMeasurePreserving.ae (hX b)
  filter_upwards [he] with t ht
  simp only [Real.toNNReal_coe] at ht
  filter_upwards [ht] with ω hω
  have hd := RealTimeBridge.integral_real_extension t
    (fun r ↦ driftInput T A B u X b (r,ω))
  exact hω.trans (by rw [hd]; rfl)

omit [𝓕.IsComplete μ] in
/-- The separate terminal equation transports through the same genuine clock. -/
theorem terminal_of_real (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (XT : κ → Ω → ℝ)
    (hXT : ∀ b, XT b =ᵐ[μ] fun ω ↦ ξ b ω +
      (∫ r in Ioc 0 (T : ℝ), driftInput T A B u X b (r.toNNReal,ω)) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i)
        (noiseInput T C D u X i b) ω) :
    ∀ b, XT b =ᵐ[μ] fun ω ↦ ξ b ω +
      (∫ r in Ioc (0 : ℝ≥0) T, driftInput T A B u X b (r,ω) ∂timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i)
        (noiseInput T C D u X i b) ω := by
  intro b
  filter_upwards [hXT b] with ω hω
  have hd := RealTimeBridge.integral_real_extension T
    (fun r ↦ driftInput T A B u X b (r,ω))
  exact hω.trans (by rw [hd]; rfl)

include hWc
omit [𝓕.IsComplete μ] in
/-- The actual class equals its continuous realization in the full product
measure; only measurable functions enter the converse Fubini step. -/
theorem sections_representative (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : Sections hW hWm T A B C D ξ u X) (b : κ) :
    (X b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
      Function.uncurry (stateProcess hWm i₀ T A B C D ξ u X b) := by
  have hx := (Lp.stronglyMeasurable (X b)).mono 𝓕.predictable_le_prod
  have hr := (realization_predictable hW hWm hWc i₀ T (hξ b)
    (driftInput T A B u X b) (fun i ↦ noiseInput T C D u X i b)).mono 𝓕.predictable_le_prod
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hx.measurable hr.measurable)).mpr
  filter_upwards [hX b, ae_restrict_mem measurableSet_Ioc] with t ht htime
  exact ht.trans (realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ htime.2).symm

/-- Genuine construction of an actual progressive continuous S² solution from
H² sections. Its class is exactly the supplied class, not a replacement input. -/
def ofSections (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : Sections hW hWm T A B C D ξ u X) : Solution hW hWm T A B C D ξ u where
  X := X
  path := stateProcess hWm i₀ T A B C D ξ u X
  progressive b := (realization_predictable hW hWm hWc i₀ T (hξ b) _ _).isStronglyProgressive.isProgressive
  continuous b := by
    simpa only [stateProcess,←NNReal.bot_eq_zero,Icc_bot] using
      realization_continuousOn hW hWm hWc i₀ T (ξ b) (driftInput T A B u X b)
        (fun i ↦ noiseInput T C D u X i b)
  squareSup b := CommonStateS2.realization_S2 hW hWm hWc i₀ T (hξ b) (hξ2 b) _ _
  representative b := sections_representative hW hWm hWc i₀ T A B C D ξ hξ u X hX b
  initial b := realization_initial hW hWm hWc i₀ T (ξ b) _ _
  equation b t ht := realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ ht

/-- A separately prescribed true terminal integral is the terminal value of
the constructed continuous version; time-a.e. sections alone are not used to
infer an endpoint identity. -/
theorem terminal_ofSections (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : Sections hW hWm T A B C D ξ u X) (XT : κ → Ω → ℝ)
    (hXT : ∀ b, XT b =ᵐ[μ] fun ω ↦ ξ b ω +
      (∫ s in Ioc (0 : ℝ≥0) T, driftInput T A B u X b (s,ω) ∂timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i)
        (noiseInput T C D u X i b) ω) (b : κ) :
    XT b =ᵐ[μ] (ofSections hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X hX).path b T :=
  (hXT b).trans (realization_integral_identity hW hWm hWc i₀ T (ξ b) _ _ le_rfl).symm

end LinearStochastic.CommonSectionSolution
