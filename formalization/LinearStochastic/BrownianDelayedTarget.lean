module

public import LinearStochastic.JointUsualRepresentation
public import LinearStochastic.CommonConditionalContinuity
public import LinearStochastic.JointUsualBrownianGlobal
public import LinearStochastic.LpOrthonormalCoordinates

@[expose] public section

/-! Actual delayed conditional expectations converge in L² on the original
usual Brownian filtration. This is the conditional-expectation step in the
manuscript's zero-diffusion approximation construction. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianDelayedTarget
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonBrownianRepair LpOrthonormalCoordinates
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include hW hInd in
/-- Scalar conditional expectation is a genuinely continuous L²-valued
process, using the proved Brownian representation and continuous Itô map. -/
theorem continuous_scalar (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hF : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] F μ) :
    Continuous (fun t => (condExpL2 ℝ ℝ ((JointUsualNatural.usual (μ:=μ) W hWm).le t) F : Lp ℝ 2 μ)) := by
  let V := repaired hW
  let hV := fun i => (repaired_brownian hW i).toIsPreBrownianReal
  let hVm := repaired_measurable hW
  let hVi := repaired_independent hW hInd
  let hVc := repaired_continuous hW
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (V i) (JointCylinderGeneration.natural V hVm) μ :=
    fun i => JointNaturalForward.coordinateForward V hV hVm hVi i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (V i) (JointUsualNatural.usual (μ:=μ) V hVm) μ :=
    fun i => JointUsualIndependence.coordinateForward V hV hVm hVi hVc i
  have he : JointUsualNatural.usual (μ:=μ) W hWm = JointUsualNatural.usual (μ:=μ) V hVm :=
    UsualVersionFiltration.repaired_usual_eq hWm hW
  have hF' : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) V hVm T] F μ := by
    apply hF.mono
    rw [he]
  have hr := JointUsualRepresentation.represented V hV hVm hVi hVc T F hF'
  have hc := CommonConditionalContinuity.continuous_conditional_of_represented
    hV hVm (JointUsualIndependence.pairForward V hV hVm hVi hVc)
    (fun _ _ hij => hVi.indepFun hij) T F hr
  change Continuous (fun t => (condExpL2 ℝ ℝ ((JointUsualNatural.usual (μ:=μ) V hVm).le t) F : Lp ℝ 2 μ)) at hc
  rw [he]
  exact hc

variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] (b : OrthonormalBasis κ ℝ E)

/-- The actual Hilbert-valued conditional expectation, as an L² class. -/
def target (η : Lp E 2 μ) (t : ℝ≥0) : Lp E 2 μ :=
  condExpL2 E ℝ ((JointUsualNatural.usual (μ:=μ) W hWm).le t) η

omit [μ.IsComplete] [IsProbabilityMeasure μ] [Fintype ι] in
/-- Every delayed target is measurable at exactly the earlier information
sigma algebra and remains square-integrable by construction. -/
theorem target_measurable (η : Lp E 2 μ) (t : ℝ≥0) :
    AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm t] (target hWm η t) μ :=
  aestronglyMeasurable_condExpL2 _ η

omit [μ.IsComplete] [IsProbabilityMeasure μ] [Fintype ι] in
/-- The delay operation is a norm contraction, hence each target has finite
second moment without any uniform bound on the later control energies. -/
theorem target_norm_le (η : Lp E 2 μ) (t : ℝ≥0) : ‖target hWm η t‖ ≤ ‖η‖ :=
  norm_condExpL2_coe_le _ η

omit [μ.IsComplete] [IsProbabilityMeasure μ] [Fintype ι] in
theorem target_coordinates (η : Lp E 2 μ) (t : ℝ≥0) :
    target hWm η t = assemble b (fun j => (condExpL2 ℝ ℝ
      ((JointUsualNatural.usual (μ:=μ) W hWm).le t) (VectorItoProduct.coordinate b j η) : Lp ℝ 2 μ)) := by
  rw [←assemble_coordinates b (target hWm η t)]
  congr 1
  funext j
  apply Lp.ext
  exact (condExpL2_comp_continuousLinearMap ℝ ℝ
    ((JointUsualNatural.usual (μ:=μ) W hWm).le t) (innerSL ℝ (b j)) η).symm

include hW hInd b in
/-- Hilbert-valued Brownian conditional expectation is L²-continuous, using
actual finite basis reconstruction rather than coordinatewise convergence alone. -/
theorem continuous_target (T : ℝ≥0) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
    Continuous (target hWm η) := by
  have hc (j : κ) := continuous_scalar hW hWm hInd T (VectorItoProduct.coordinate b j η)
    (((innerSL ℝ (b j)).continuous.comp_aestronglyMeasurable hη).congr
      (VectorItoProduct.coordinate_ae b j η).symm)
  have he : target hWm η = fun t => assemble b (fun j => (condExpL2 ℝ ℝ
      ((JointUsualNatural.usual (μ:=μ) W hWm).le t) (VectorItoProduct.coordinate b j η) : Lp ℝ 2 μ)) :=
    funext (target_coordinates hWm b η)
  rw [he]
  change Continuous (fun t => ∑ j, (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 μ
    (condExpL2 ℝ ℝ ((JointUsualNatural.usual (μ:=μ) W hWm).le t) (VectorItoProduct.coordinate b j η) : Lp ℝ 2 μ))
  exact continuous_finsetSum _ (fun j _ => ((ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLpL 2 μ).continuous.comp (hc j))

omit [μ.IsComplete] [Fintype ι] in
theorem target_terminal (T : ℝ≥0) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
    target hWm η T = η := by
  apply Lp.ext
  have he := (Lp.memLp η).condExpL2_ae_eq_condExp (𝕜:=ℝ) ((JointUsualNatural.usual (μ:=μ) W hWm).le T)
  rw [Lp.toLp_coeFn] at he
  exact he.trans (condExp_of_aestronglyMeasurable' ((JointUsualNatural.usual (μ:=μ) W hWm).le T)
    hη ((Lp.memLp η).integrable one_le_two))

include hW hInd b in
/-- Precisely ξ_h=E[ξ|F_{T-h}] tends to ξ in L² as h decreases to zero;
nonnegative-time subtraction is harmless and the statement includes all h≥0. -/
theorem delayed_tendsto (T : ℝ≥0) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
    Filter.Tendsto (fun h : ℝ≥0 => target hWm η (T-h)) (nhds 0) (nhds η) := by
  have hc := (continuous_target hW hWm hInd b T η hη).comp ((continuous_const (y:=T)).sub continuous_id)
  change Continuous (fun h : ℝ≥0 => target hWm η (T-h)) at hc
  have ht := hc.tendsto 0
  change Filter.Tendsto (fun h : ℝ≥0 => target hWm η (T-h)) (nhds 0) (nhds (target hWm η (T-0))) at ht
  simpa only [tsub_zero,target_terminal hWm T η hη] using ht

end LinearStochastic.BrownianDelayedTarget
