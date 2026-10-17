module

public import LinearStochastic.HilbertSolutionZeroExtension
public import LinearStochastic.VectorExtensionNaturality
public import LinearStochastic.TerminalSpikeNoise

@[expose] public section

/-! Genuine adjoint solutions for the normalized terminal diffusion spike. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.TerminalSpikeState
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution PredictableConstant
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

def scalarBasis : OrthonormalBasis Unit ℝ ℝ := OrthonormalBasis.singleton Unit ℝ

def windowLinear (i₀ : ι) (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    E →ₗ[ℝ] Lp E 2 (spacetimeMeasure 𝓕 μ T) :=
  (VectorH2Extension.extendShift b (hWm i₀) a δ T h).toLinearMap.comp
    ((constantLinear (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ).comp
      ((Real.sqrt (δ:ℝ))⁻¹ • LinearMap.id))

def forcing (C : ι → E →L[ℝ] E) (q : ι → E) : ℝ →L[ℝ] E :=
  ContinuousLinearMap.toSpanSingleton ℝ (-(∑ i, (C i).adjoint (q i)))

def factor (δ : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (q : ι → E) : ℝ :=
  (Fintype.card κ : ℝ)*CommonSmallTimeBound.additiveFactor δ
    (coefficientMatrix b b (-A.adjoint)) (coefficientMatrix b scalarBasis (forcing C q))
    (fun i ↦ coefficientMatrix b scalarBasis (ContinuousLinearMap.toSpanSingleton ℝ (q i)))

include hWc in
/-- The prescribed noise is realized by an actual adjoint integral solution,
whose state norm has a coefficient-only bound tending to zero with δ. -/
theorem exists_solution (i₀ : ι) (a δ : ℝ≥0) (hδ : 0 < δ)
    (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (q : ι → E)
    (hc : (δ:ℝ)*CommonPicardHorizon.matrixSize (coefficientMatrix b b (-A.adjoint)) < 1) :
    ∃ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))) (η : lpMeas E ℝ (𝓕 (a+δ)) 2 μ),
      SectionIntegralSolution b hW hWm (a+δ) 0
        (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q i)))
        (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q) Y (η : Lp E 2 μ) ∧
      ‖Y‖ ≤ factor b δ A C q := by
  let u := constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • (1:ℝ))
  let ug := VectorH2Extension.extendShift scalarBasis (hWm i₀) a δ (a+δ) le_rfl u
  let D := fun i ↦ ContinuousLinearMap.toSpanSingleton ℝ (q i)
  obtain ⟨Y,η,hs,hbound⟩ := HilbertSolutionZeroExtension.exists_additive b scalarBasis hW hWm hWc i₀ a δ
    (-A.adjoint) (forcing C q) D u hc
  let Z := TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q
  let L := windowLinear (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl
  have hscalar (v : E) : (ContinuousLinearMap.toSpanSingleton ℝ v).compLp ug = L v := by
    have hh := VectorExtensionNaturality.normalized_constant (𝓕:=𝓕) (μ:=μ) scalarBasis b (hWm i₀) a δ (a+δ) le_rfl
      (ContinuousLinearMap.toSpanSingleton ℝ v) (1:ℝ)
    dsimp [L,windowLinear,ug,u,constantLinear]
    simpa only [ContinuousLinearMap.toSpanSingleton_apply,one_smul,smul_eq_mul,mul_one] using hh
  have hZ : (fun i ↦ (D i).compLp ug) = Z := by
    funext i
    exact hscalar (q i)
  have hC (i : ι) : (C i).adjoint.compLp (Z i) = L ((C i).adjoint (q i)) :=
    VectorExtensionNaturality.normalized_constant (𝓕:=𝓕) (μ:=μ) b b (hWm i₀) a δ (a+δ) le_rfl (C i).adjoint (q i)
  have hf : (forcing C q).compLp ug = -(∑ i, (C i).adjoint.compLp (Z i)) := by
    rw [show forcing C q = ContinuousLinearMap.toSpanSingleton ℝ (-(∑ i, (C i).adjoint (q i))) from rfl,hscalar,map_neg,map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ ↦ (hC i).symm)
  have hA : (-A.adjoint).compLp Y = -(A.adjoint.compLp Y) := by
    apply Lp.ext
    filter_upwards [(-A.adjoint).coeFn_compLp Y,A.adjoint.coeFn_compLp Y,Lp.coeFn_neg (A.adjoint.compLp Y)] with z hn hp hr
    rw [hn,hr,Pi.neg_apply,hp]
    rfl
  have hd : (-A.adjoint).compLp Y+(forcing C q).compLp ug =
      -(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i)) := by rw [hA,hf]; abel
  rw [show VectorH2Extension.extendShift scalarBasis (hWm i₀) a δ (a+δ) le_rfl u = ug from rfl,hd,hZ] at hs
  have hu : ‖u‖ = 1 := by
    have hh := normalized_norm_sq (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ hδ (1:ℝ)
    have hh' : ‖u‖^2 = 1 := by simpa only [norm_one,one_pow] using hh
    nlinarith [norm_nonneg u]
  refine ⟨Y,η,hs,?_⟩
  simpa only [factor,D,hu,mul_one] using hbound

omit hW hWm hWc [IsProbabilityMeasure μ] [𝓕.IsComplete μ] in
/-- Actual coefficient factor of the constructed state vanishes. -/
theorem factor_tendsto (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (q : ι → E) :
    Filter.Tendsto (fun δ : ℝ≥0 ↦ factor b δ A C q) (nhds 0) (nhds 0) := by
  have hh := (CommonSmallTimeBound.additiveFactor_tendsto
    (coefficientMatrix b b (-A.adjoint)) (coefficientMatrix b scalarBasis (forcing C q))
    (fun i ↦ coefficientMatrix b scalarBasis (ContinuousLinearMap.toSpanSingleton ℝ (q i)))).const_mul (Fintype.card κ : ℝ)
  simpa only [factor,mul_zero] using hh
end LinearStochastic.TerminalSpikeState
