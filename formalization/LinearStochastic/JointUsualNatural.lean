import LinearStochastic.JointMartingaleRepresentation
import LinearStochastic.CommonConditionalContinuity
import LinearStochastic.CommonNullL2

noncomputable section
namespace LinearStochastic.JointUsualNatural
open MeasureTheory ProbabilityTheory CommonNullAugmentation
open scoped NNReal BigOperators Topology
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hWm : ∀ i t, Measurable (W i t))

/-- Null augmentation of the actual joint natural filtration on the original
ambient probability space. -/
def augmented : Filtration ℝ≥0 mΩ := JointCylinderGeneration.natural W hWm ⊔
  Filtration.const ℝ≥0 (nullsAlg mΩ μ) nullsAlg_le

/-- The usual augmentation: null events followed by right continuation. -/
def usual : Filtration ℝ≥0 mΩ := (augmented (μ := μ) W hWm).rightCont

omit [Fintype ι] [IsProbabilityMeasure μ] in
theorem natural_le_usual : JointCylinderGeneration.natural W hWm ≤ usual (μ := μ) W hWm :=
  le_trans le_sup_left (augmented (μ := μ) W hWm).le_rightCont

instance usual_rightContinuous : (usual (μ := μ) W hWm).IsRightContinuous :=
  inferInstanceAs ((augmented (μ := μ) W hWm).rightCont.IsRightContinuous)

instance usual_complete [μ.IsComplete] : (usual (μ := μ) W hWm).IsComplete μ := by
  constructor
  intro s hs t
  apply (augmented (μ := μ) W hWm).le_rightCont t
  apply (show nullsAlg mΩ μ ≤ augmented (μ := μ) W hWm t from le_sup_right)
  exact MeasurableSpace.measurableSet_generateFrom ⟨measurableSet_of_null hs,hs⟩

omit [Fintype ι] [IsProbabilityMeasure μ] in
theorem usual_le_augmented {s t : ℝ≥0} (hst : s < t) :
    usual (μ := μ) W hWm s ≤ augmented (μ := μ) W hWm t := by
  unfold usual
  rw [Filtration.rightCont_eq]
  exact iInf_le_of_le t (iInf_le_of_le hst le_rfl)

omit [Fintype ι] in
/-- A variable measurable at usual time `s` is raw-natural measurable modulo
null events at every strictly later time `t`. -/
theorem natural_measurable_later {s t : ℝ≥0} (hst : s < t)
    (F : Lp ℝ 2 μ) (hF : AEStronglyMeasurable[usual (μ := μ) W hWm s] F μ) :
    AEStronglyMeasurable[JointCylinderGeneration.natural W hWm t] F μ :=
  CommonNullL2.measurable_of_null_augmented ((JointCylinderGeneration.natural W hWm).le t) F
    (hF.mono (usual_le_augmented W hWm hst))

variable (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointCylinderGeneration.natural W hWm) μ]

include hW hInd in
/-- Usual and raw joint-natural terminal L² variables coincide. This proves
the right-continuation step using the actual continuous L² conditional process
obtained from the already proved raw martingale representation. -/
theorem natural_measurable_of_usual
    (hWc : ∀ i ω, Continuous fun t => W i t ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ) (hF : AEStronglyMeasurable[usual (μ := μ) W hWm T] F μ) :
    AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T] F μ := by
  have hTU : T < T+1 := lt_add_one T
  have hFU := natural_measurable_later W hWm hTU F hF
  have hr := JointMartingaleRepresentation.represented W hW hWm hInd hWc (T+1) F hFU
  have hc := CommonConditionalContinuity.continuous_conditional_of_represented hW hWm
    (JointNaturalForward.pairForward W hW hWm hInd) (fun _ _ hij => hInd.indepFun hij)
    (T+1) F hr
  have hclosed : IsClosed {t | CommonConditionalContinuity.conditional
      (𝓕 := JointCylinderGeneration.natural W hWm) F t = F} :=
    isClosed_eq hc continuous_const
  have hsub : Set.Ioo T (T+1) ⊆ {t | CommonConditionalContinuity.conditional
      (𝓕 := JointCylinderGeneration.natural W hWm) F t = F} := by
    intro t ht
    exact CommonConditionalContinuity.conditional_of_measurable F t
      (natural_measurable_later W hWm ht.1 F hF)
  have he : CommonConditionalContinuity.conditional
      (𝓕 := JointCylinderGeneration.natural W hWm) F T = F :=
    (closure_minimal hsub hclosed) (by rw [closure_Ioo hTU.ne]; exact ⟨le_rfl,hTU.le⟩)
  have hm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T]
      (CommonConditionalContinuity.conditional (𝓕 := JointCylinderGeneration.natural W hWm) F T) μ :=
    aestronglyMeasurable_condExpL2 ((JointCylinderGeneration.natural W hWm).le T) F
  rwa [he] at hm

end LinearStochastic.JointUsualNatural
