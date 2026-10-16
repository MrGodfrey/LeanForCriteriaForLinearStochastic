import LinearStochastic.CommonInitialPredictable
import LinearStochastic.CommonDriftPathwise

/-! A genuine pathwise realization of the controlled H² Picard map. The scalar
coordinate process is defined by the actual continuous-limit drift and Itô
integrals. Its predictable space-time class equals the assembled operator,
and its paths are continuous almost surely on the finite horizon. -/
noncomputable section
namespace LinearStochastic.CommonPicardRealization
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonItoContinuous CommonItoPredictable
open CommonDriftPredictable CommonDriftModification CommonDriftPathwise
open CommonItoMultichannel CommonVectorPicard CommonInitialPredictable
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

def realization (i₀ : ι) (T : ℝ≥0) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ξ ω + driftContinuousMod T (hWm i₀) g t ω + ∑ i, itoContinuousMod T (hWm i) (σ i) t ω

/-- The genuine drift CLM with the common predictable domain written explicitly. -/
def driftScalar (i₀ : ι) (T : ℝ≥0) : H2 𝓕 μ T →L[ℝ] H2 𝓕 μ T :=
  driftProcessAssembled (𝓕:=𝓕) (μ:=μ) T (hWm i₀)

/-- The genuine Itô space-time map with the same common predictable domain. -/
def itoScalar (i : ι) (T : ℝ≥0) (f : H2 𝓕 μ T) : H2 𝓕 μ T :=
  itoProcessAssembled (hW i) T (hWm i) (hWc i) f

include hW hWc

theorem realization_predictable (i₀ : ι) (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    IsStronglyPredictable 𝓕 (realization hWm i₀ T ξ g σ) := by
  exact ((initial_predictable hξ).add (driftContinuousMod_isStronglyPredictable T (hWm i₀) g)).add
    (by
      change StronglyMeasurable[𝓕.predictable]
        (fun z : ℝ≥0 × Ω ↦ ∑ i, itoContinuousMod T (hWm i) (σ i) z.1 z.2)
      convert (Finset.stronglyMeasurable_sum Finset.univ fun i _ ↦
          itoContinuousMod_isStronglyPredictable (hW i) T (hWm i) (hWc i) (σ i)) using 1
      funext z
      exact (Finset.sum_apply z Finset.univ (fun i ↦ Function.uncurry (itoContinuousMod T (hWm i) (σ i)))).symm)

theorem realization_continuousOn (i₀ : ι) (T : ℝ≥0) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ realization hWm i₀ T ξ g σ t ω) (Set.Icc 0 T) := by
  have hs : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn
      (fun t ↦ itoContinuousMod T (hWm i) (σ i) t ω) (Set.Icc 0 T) := by
    rw [ae_all_iff]
    exact fun i ↦ itoContinuousMod_continuousOn (hW i) T (hWm i) (hWc i) (σ i)
  filter_upwards [driftContinuousMod_continuousOn T (hWm i₀) g, hs] with ω hg hs
  exact (continuousOn_const.add hg).add (continuousOn_finsetSum _ fun i _ ↦ hs i)

/-- At each actual time, the drift is the raw Lebesgue integral and the
stochastic terms are the independently constructed per-time Itô operators. -/
theorem realization_integral_identity (i₀ : ι) (T : ℝ≥0) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) {t : ℝ≥0} (ht : t ≤ T) :
    realization hWm i₀ T ξ g σ t =ᵐ[μ] fun ω ↦
      ξ ω + (∫ s in Set.Ioc (0 : ℝ≥0) t, g (s,ω) ∂timeMeasure) +
        ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (σ i) ω := by
  have hs : ∀ᵐ ω ∂μ, ∀ i, itoContinuousMod T (hWm i) (σ i) t ω =
      CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (σ i) ω := by
    rw [ae_all_iff]
    exact fun i ↦ itoContinuousMod_modification (hW i) T (hWm i) (hWc i) (σ i) ht
  filter_upwards [driftContinuousMod_eq_setIntegral T (hWm i₀) g ht, hs] with ω hg hs
  simp only [realization, hg]
  exact congrArg (fun z : ℝ ↦ ξ ω + (∫ s in Set.Ioc (0 : ℝ≥0) t, g (s,ω) ∂timeMeasure) + z)
    (Finset.sum_congr rfl fun i _ ↦ hs i)

/-- The assembled drift and Itô terms have this exact predictable pathwise
representative. The identification is proved from the actual Lp representatives. -/
theorem assembled_ae_realization (i₀ : ι) (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    (initialH2 hξ hξ2 T + driftScalar hWm i₀ T g +
      ∑ i, itoScalar hW hWm hWc i T (σ i) : H2 𝓕 μ T) =ᵐ[spacetimeMeasure 𝓕 μ T]
        Function.uncurry (realization hWm i₀ T ξ g σ) := by
  let J := fun i ↦ itoScalar hW hWm hWc i T (σ i)
  have hj : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, ∀ i,
      J i z = itoContinuousMod T (hWm i) (σ i) z.1 z.2 := by
    rw [ae_all_iff]
    exact fun i ↦ (memLp_itoContinuousMod (hW i) T (hWm i) (hWc i) (σ i)).coeFn_toLp
  filter_upwards [Lp.coeFn_add (initialH2 hξ hξ2 T + driftScalar hWm i₀ T g) (∑ i, J i),
    Lp.coeFn_add (initialH2 hξ hξ2 T) (driftScalar hWm i₀ T g),
    initialH2_ae hξ hξ2 T, driftProcessAssembled_coeFn T (hWm i₀) g,
    Lp.coeFn_fun_finsetSum Finset.univ J, hj] with z ha hb hξz hgz hsum hjz
  change (initialH2 hξ hξ2 T + driftScalar hWm i₀ T g + ∑ i, J i) z = _
  change driftScalar hWm i₀ T g z = driftContinuousMod T (hWm i₀) g z.1 z.2 at hgz
  rw [ha, Pi.add_apply, hb, Pi.add_apply, hξz, hgz, hsum]
  exact congrArg (fun q : ℝ ↦ ξ z.2 + driftContinuousMod T (hWm i₀) g z.1 z.2 + q)
    (Finset.sum_congr rfl fun i _ ↦ hjz i)

/-- The constructed pathwise process has the prescribed actual random initial
value, not just its equivalence class under a time measure that ignores zero. -/
theorem realization_initial (i₀ : ι) (T : ℝ≥0) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    realization hWm i₀ T ξ g σ 0 =ᵐ[μ] ξ := by
  have h := realization_integral_identity hW hWm hWc i₀ T ξ g σ (t:=0) (by positivity)
  have hz : ∀ᵐ ω ∂μ, ∀ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T 0 (hWm i) (σ i) ω = 0 := by
    rw [ae_all_iff]
    intro i
    have he := CommonItoProcessGeneral.itoProcessCLM_zero_time (hW i) T (hWm i) (σ i)
    have hae : ∀ᵐ ω ∂μ, CommonItoProcessGeneral.itoProcessCLM (hW i) T 0 (hWm i) (σ i) ω =
        (0 : Lp ℝ 2 μ) ω :=
      ae_of_all μ (fun ω ↦ congrArg (fun z : Lp ℝ 2 μ ↦ z ω) he)
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 μ] with ω h1 h2
    exact h1.trans h2
  filter_upwards [h,hz] with ω he hz
  simpa only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
    add_zero, hz, Finset.sum_const_zero] using he

end LinearStochastic.CommonPicardRealization
