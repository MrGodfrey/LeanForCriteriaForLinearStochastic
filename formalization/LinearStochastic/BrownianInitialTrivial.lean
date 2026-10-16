import LinearStochastic.JointUsualBrownianGlobal
import LinearStochastic.JointMartingaleRepresentation
import LinearStochastic.LpOrthonormalCoordinates

/-! The actual initial usual Brownian sigma algebra is trivial for L² random
variables. This follows from the proved raw representation at horizon zero,
not from a separate triviality or deterministic-initial-value assumption. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianInitialTrivial
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonBrownianRepair JointCylinderGeneration
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype ι]

/-- A raw-natural L² initial variable for continuous Brownian versions equals
its deterministic expectation almost surely. -/
theorem natural_initial_constant (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t => W i t ω) μ)
    (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (F : Lp ℝ 2 μ) (hF : AEStronglyMeasurable[natural W hWm 0] F μ) :
    (F : Ω → ℝ) =ᵐ[μ] fun _ => ∫ ω, F ω ∂μ := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  let d := ∫ ω, F ω ∂μ
  let ξ : Lp ℝ 2 μ := Lp.const 2 μ d
  have hξ : (ξ : Ω → ℝ) =ᵐ[μ] fun _ => d := Lp.coeFn_const 2 μ d
  have hξm : AEStronglyMeasurable[natural W hWm 0] ξ μ :=
    aestronglyMeasurable_const.congr hξ.symm
  have hsub : (F-ξ : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ω-d := by
    filter_upwards [Lp.coeFn_sub F ξ,hξ] with ω hs hc
    rw [hs,Pi.sub_apply,hc]
  have hm : AEStronglyMeasurable[natural W hWm 0] (F-ξ : Lp ℝ 2 μ) μ :=
    (hF.sub hξm).congr (Lp.coeFn_sub F ξ).symm
  have hz : (∫ ω, (F-ξ : Lp ℝ 2 μ) ω ∂μ) = 0 := by
    rw [integral_congr_ae hsub,integral_sub ((Lp.memLp F).integrable one_le_two) (integrable_const d),
      integral_const,probReal_univ,one_smul]
    exact sub_self d
  obtain ⟨f,hf⟩ := JointMartingaleRepresentation.centered_mem_range W hW hWm hInd hWc 0 (F-ξ) hm hz
  have hi : JointMartingaleRepresentation.integral W hW hWm hInd 0 f = 0 := by
    apply Lp.ext
    exact (ItoExpectedProduct.sumProcess_terminal_ae hW hWm 0 (fun i => f i)).symm.trans
      ((InitialExpectedProduct.sumProcess_zero_ae hW hWm 0 (fun i => f i)).trans
        (Lp.coeFn_zero ℝ 2 μ).symm)
  change JointMartingaleRepresentation.integral W hW hWm hInd 0 f = F-ξ at hf
  have he : F=ξ := sub_eq_zero.mp (hf.symm.trans hi)
  exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 μ => (f : Ω → ℝ)) he)).trans hξ

variable [μ.IsComplete] {W : ι → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include hW hInd in
/-- Triviality at time zero of the original usual Brownian filtration, with
only the original almost-sure Brownian continuity assumption. -/
theorem usual_initial_constant (F : Lp ℝ 2 μ)
    (hF : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] F μ) :
    (F : Ω → ℝ) =ᵐ[μ] fun _ => ∫ ω, F ω ∂μ := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (natural (repaired hW) (repaired_measurable hW)) μ :=
    fun i => JointNaturalForward.coordinateForward (repaired hW)
      (fun j => (repaired_brownian hW j).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) i
  have hFu : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) (repaired hW) (repaired_measurable hW) 0] F μ := by
    apply hF.mono
    rw [UsualVersionFiltration.repaired_usual_eq hWm hW]
  have hFn := JointUsualNatural.natural_measurable_of_usual (repaired hW) (repaired_measurable hW)
    (fun i => (repaired_brownian hW i).toIsPreBrownianReal) (repaired_independent hW hInd)
    (repaired_continuous hW) 0 F hFu
  exact natural_initial_constant (repaired hW) (fun i => (repaired_brownian hW i).toIsPreBrownianReal)
    (repaired_measurable hW) (repaired_independent hW hInd) (repaired_continuous hW) F hFn

include hW hInd in
/-- Every actual finite-dimensional F₀-measurable L² initial value is an
almost-sure deterministic vector, not merely a random starting parameter. -/
theorem vector_initial_constant {E κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]
    (b : OrthonormalBasis κ ℝ E) (ξ : Ω → E)
    (hξ : StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] ξ) (hξ2 : MemLp ξ 2 μ) :
    ∃ v : E, ξ =ᵐ[μ] fun _ => v := by
  let F := fun j => ((innerSL ℝ (b j)).comp_memLp' hξ2).toLp (fun ω => inner ℝ (b j) (ξ ω))
  have hFc (j : κ) : (F j : Ω → ℝ) =ᵐ[μ] fun ω => inner ℝ (b j) (ξ ω) :=
    ((innerSL ℝ (b j)).comp_memLp' hξ2).coeFn_toLp
  have hFm (j : κ) : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] (F j) μ :=
    ((innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ).aestronglyMeasurable.congr (hFc j).symm
  have hall : ∀ᵐ ω ∂μ, ∀ j, inner ℝ (b j) (ξ ω) = ∫ z, F j z ∂μ := by
    rw [ae_all_iff]
    intro j
    exact (hFc j).symm.trans (usual_initial_constant hW hWm hInd (F j) (hFm j))
  refine ⟨∑ j, (∫ z, F j z ∂μ) • b j,?_⟩
  filter_upwards [hall] with ω hω
  simpa only [←hω] using (b.sum_repr' (ξ ω)).symm

end LinearStochastic.BrownianInitialTrivial
