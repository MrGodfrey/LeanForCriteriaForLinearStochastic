module

public import LinearStochastic.JointUsualIndependence
public import LinearStochastic.CommonFiltrationTransport

@[expose] public section

noncomputable section
namespace LinearStochastic.JointUsualRepresentation
open MeasureTheory ProbabilityTheory CommonItoMultichannel
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

/-- Martingale representation on the actual usual augmentation of the joint
Brownian natural filtration. Both raw and usual future-independence instances
are constructed from the actual independent Brownian coordinates. -/
theorem represented (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[JointUsualNatural.usual (μ := μ) W hWm T] F μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ := μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    BSDEIntegralRange.Represented hW hWm
      (JointUsualIndependence.pairForward W hW hWm hInd hWc)
      (fun _ _ hij => hInd.indepFun hij) T F := by
  classical
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ := μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  have hraw := JointUsualNatural.natural_measurable_of_usual W hWm hW hInd hWc T F hFm
  obtain ⟨ξ,hξ,f,he⟩ := JointMartingaleRepresentation.represented W hW hWm hInd hWc T F hraw
  let hle := JointUsualNatural.natural_le_usual (μ := μ) W hWm
  let g : BSDEIntegralRange.ChannelH2 (ι := ι) (𝓕 := JointUsualNatural.usual (μ := μ) W hWm) (μ := μ) T :=
    WithLp.toLp 2 (fun i => CommonFiltrationTransport.integrandInclusion hle T (f i))
  refine ⟨ξ,hξ.mono (hle 0),g,?_⟩
  rw [he]
  congr 1
  change (∑ i, CommonItoCLM.itoIntegralCLM_T (𝓕 := JointCylinderGeneration.natural W hWm)
    (hW i) T (hWm i) (f i)) = ∑ i, CommonItoCLM.itoIntegralCLM_T
      (𝓕 := JointUsualNatural.usual (μ := μ) W hWm) (hW i) T (hWm i)
      (CommonFiltrationTransport.integrandInclusion hle T (f i))
  apply Finset.sum_congr rfl
  intro i _
  exact (CommonFiltrationTransport.integral_inclusion (hW i) (hWm i) hle T (f i)).symm

end LinearStochastic.JointUsualRepresentation
