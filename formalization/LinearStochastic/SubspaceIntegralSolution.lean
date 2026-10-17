module

public import LinearStochastic.SectionSolutionNaturality
public import LinearStochastic.SectionZeroDecomposition
public import LinearStochastic.ContinuousSubspace
public import LinearStochastic.AlgebraFlag

@[expose] public section

/-! Genuine subspace constraints on an integral solution force its drift and
every diffusion coefficient into the same subspace. -/
noncomputable section
namespace LinearStochastic.SubspaceIntegralSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality

section Projection
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual orthogonal complementary projection, valued in the ambient
space so the same vector Itô construction applies. -/
def complementProjection (V : Submodule ℝ E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - V.starProjection

theorem complementProjection_eq_zero_iff (V : Submodule ℝ E) (x : E) :
    complementProjection V x = 0 ↔ x ∈ V := by
  change x - V.starProjection x = 0 ↔ x ∈ V
  rw [sub_eq_zero,eq_comm,V.starProjection_eq_self_iff]

theorem compLp_eq_zero_iff (V : Submodule ℝ E) (f : Lp E 2 μ) :
    (complementProjection V).compLp f = 0 ↔ ∀ᵐ ω ∂μ, f ω ∈ V := by
  constructor
  · intro h
    have he := (complementProjection V).coeFn_compLp f
    rw [h] at he
    filter_upwards [he,Lp.coeFn_zero E 2 μ] with ω he hz
    exact (complementProjection_eq_zero_iff V (f ω)).mp (he.symm.trans hz)
  · intro h
    apply Lp.ext
    filter_upwards [(complementProjection V).coeFn_compLp f,Lp.coeFn_zero E 2 μ,h]
      with ω he hz hm
    rw [he,hz]
    exact (complementProjection_eq_zero_iff V (f ω)).mpr hm
end Projection

section Stochastic
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Zero projection of the actual solution and both endpoint values gives a
literal zero solution of the projected drift/diffusion equation. -/
theorem projected_zero_solution (T : ℝ≥0) (V : Submodule ℝ E) (ξ XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hξ : ∀ᵐ ω ∂μ, ξ ω ∈ V) (hXT : ∀ᵐ ω ∂μ, XT ω ∈ V)
    (hXV : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, X z ∈ V) :
    SectionIntegralSolution b hW hWm T 0 ((complementProjection V).compLp f)
      (fun i => (complementProjection V).compLp (φ i)) 0 0 := by
  let Q := complementProjection V
  have hm := SectionSolutionNaturality.SectionIntegralSolution.map b hW hWm T Q ξ f φ X XT hX
  have hX0 : Q.compLp X = 0 := (compLp_eq_zero_iff (mΩ := 𝓕.predictable) V X).mpr hXV
  have hξ0 : (fun ω => Q (ξ ω)) =ᵐ[μ] 0 := by
    filter_upwards [hξ] with ω hω
    exact (complementProjection_eq_zero_iff V (ξ ω)).mpr hω
  have hXT0 : (fun ω => Q (XT ω)) =ᵐ[μ] 0 := by
    filter_upwards [hXT] with ω hω
    exact (complementProjection_eq_zero_iff V (XT ω)).mpr hω
  constructor
  · have hs := hm.sections
    rw [hX0] at hs
    filter_upwards [hs] with s hs
    filter_upwards [hs,hξ0] with ω hs hξ0
    simpa only [integralState,hξ0,Pi.zero_apply] using hs
  · filter_upwards [hm.terminal,hξ0,hXT0] with ω hs hξ0 hXT0
    simpa only [integralState,hξ0,hXT0,Pi.zero_apply] using hs

/-- True semimartingale subspace uniqueness, proved using the actual linear
projection, Itô energy identity, and Lebesgue differentiation. -/
theorem coefficients_mem
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (V : Submodule ℝ E) (ξ XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hξ : ∀ᵐ ω ∂μ, ξ ω ∈ V) (hXT : ∀ᵐ ω ∂μ, XT ω ∈ V)
    (hXV : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, X z ∈ V) :
    (∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, f z ∈ V) ∧
      ∀ i, ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, φ i z ∈ V := by
  have hz := projected_zero_solution b hW hWm T V ξ XT f X φ hX hξ hXT hXV
  have hcoeff := SectionZeroDecomposition.zero_decomposition b hW hWm hpair hchannels
    T hT ((complementProjection V).compLp f) (fun i => (complementProjection V).compLp (φ i)) hz
  exact ⟨(compLp_eq_zero_iff (mΩ := 𝓕.predictable) V f).mp hcoeff.1,
    fun i => (compLp_eq_zero_iff (mΩ := 𝓕.predictable) V (φ i)).mp (hcoeff.2 i)⟩
end Stochastic

#print axioms coefficients_mem
end LinearStochastic.SubspaceIntegralSolution
