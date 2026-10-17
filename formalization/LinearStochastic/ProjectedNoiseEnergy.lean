module

public import LinearStochastic.SubspaceIntegralSolution

@[expose] public section

/-! The pathwise integrated projected-noise energy displayed in the paper is
zero, derived from the actual projected SDE rather than assumed variation. -/
noncomputable section
namespace LinearStochastic.ProjectedNoiseEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality SubspaceIntegralSolution
section DeterministicMeasure
variable {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [InnerProductSpace ℝ E] in
/-- Product-a.e. zero really implies a single probability-one event on which
all finitely many real-time path integrals are zero. -/
theorem sum_integral_zero (T : ℝ≥0) (Z : ι → ℝ≥0 → Ω → E)
    (hZ : ∀ i, Function.uncurry (Z i) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] 0) :
    ∀ᵐ ω ∂μ, (∑ i, ∫ t in Ioc (0:ℝ) (T:ℝ), ‖Z i t.toNNReal ω‖^2)=0 := by
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) (T:ℝ)), Z i t.toNNReal ω=0 := by
    have hr := ((RealTimeBridge.toNNReal_measurePreserving T).prod
      (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp (hZ i)
    have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hr)
    exact hs
  have hall : ∀ᵐ ω ∂μ, ∀ i, ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) (T:ℝ)), Z i t.toNNReal ω=0 := by
    rw [ae_all_iff]
    exact he
  filter_upwards [hall] with ω hω
  apply Finset.sum_eq_zero
  intro i _
  apply integral_eq_zero_of_ae
  filter_upwards [hω i] with t ht
  simp only [Pi.zero_apply,ht,norm_zero,zero_pow (by decide : 2≠0)]

variable [FiniteDimensional ℝ E]
/-- Genuine predictable H² membership gives exactly the displayed a.s.
energy identity for the actual orthogonal complementary projection. -/
theorem projected_sum_integral_zero (T : ℝ≥0) (V : Submodule ℝ E)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hφ : ∀ i, ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, φ i z∈V) :
    ∀ᵐ ω ∂μ, (∑ i, ∫ t in Ioc (0:ℝ) (T:ℝ),
      ‖complementProjection V (φ i (t.toNNReal,ω))‖^2)=0 := by
  apply sum_integral_zero T (fun i t ω=>complementProjection V (φ i (t,ω)))
  intro i
  have h := ae_of_ae_trim (hm:=𝓕.predictable_le_prod) (hφ i)
  filter_upwards [h] with z hz
  exact (complementProjection_eq_zero_iff V (φ i z)).mpr hz
end DeterministicMeasure

section ActualSDE
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual integral equation staying in V forces the precise pathwise
sum of projected diffusion energies to vanish, including arbitrary noise
representatives of its genuine H² classes. -/
theorem actual_projected_energy
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t=>W i t ω) (fun ω t=>W j t ω) μ)
    (T : ℝ≥0) (hT : 0<T) (V : Submodule ℝ E) (ξ XT : Ω→E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → ℝ≥0 → Ω → E)
    (hrep : ∀ i, φ i =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (Z i))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hξ : ∀ᵐ ω ∂μ, ξ ω∈V) (hXT : ∀ᵐ ω ∂μ, XT ω∈V)
    (hXV : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, X z∈V) :
    ∀ᵐ ω ∂μ, (∑ i, ∫ t in Ioc (0:ℝ) (T:ℝ),
      ‖complementProjection V (Z i t.toNNReal ω)‖^2)=0 := by
  have hφ := (coefficients_mem b hW hWm hpair hchannels T hT V ξ XT f X φ hX hξ hXT hXV).2
  apply sum_integral_zero T (fun i t ω=>complementProjection V (Z i t ω))
  intro i
  have h := ae_of_ae_trim (hm:=𝓕.predictable_le_prod) (hφ i)
  filter_upwards [h,hrep i] with z hz he
  rw [he] at hz
  exact (complementProjection_eq_zero_iff V (Z i z.1 z.2)).mpr hz
end ActualSDE
end LinearStochastic.ProjectedNoiseEnergy
