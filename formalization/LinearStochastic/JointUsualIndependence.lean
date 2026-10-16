import LinearStochastic.JointUsualNatural

noncomputable section
namespace LinearStochastic.JointUsualIndependence
open MeasureTheory ProbabilityTheory JointUsualNatural
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointCylinderGeneration.natural W hWm) μ]
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

include hW hInd hWc in
/-- Every event in the actual usual Brownian filtration equals a raw-natural
event modulo the original probability measure. -/
theorem exists_natural_event (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[usual (μ := μ) W hWm t] A) :
    ∃ B, MeasurableSet[JointCylinderGeneration.natural W hWm t] B ∧ A =ᵐ[μ] B := by
  classical
  let f : Ω → ℝ := A.indicator (fun _ => 1)
  have hf2 : MemLp f 2 μ := (memLp_const (μ := μ) (1 : ℝ)).indicator ((usual (μ := μ) W hWm).le t A hA)
  let F : Lp ℝ 2 μ := hf2.toLp f
  have hFm : AEStronglyMeasurable[usual (μ := μ) W hWm t] F μ :=
    (stronglyMeasurable_const.indicator hA).aestronglyMeasurable.congr hf2.coeFn_toLp.symm
  have hm := natural_measurable_of_usual W hWm hW hInd hWc t F hFm
  refine ⟨{ω | hm.mk (F : Ω → ℝ) ω = 1},?_,?_⟩
  · exact measurableSet_eq_fun hm.stronglyMeasurable_mk.measurable measurable_const
  · filter_upwards [hf2.coeFn_toLp,hm.ae_eq_mk] with ω hf hg
    apply propext
    change (ω ∈ A) ↔ hm.mk (F : Ω → ℝ) ω = 1
    rw [←hg,hf]
    simp [f,Set.indicator_apply]

include hW hInd hWc in
/-- Genuine independence extends from the raw natural past to the usual
past because every such event has an actual raw representative. -/
theorem indep_usual {m : MeasurableSpace Ω} (t : ℝ≥0)
    (hi : Indep (JointCylinderGeneration.natural (mΩ := mΩ) W hWm t) m μ) :
    Indep (usual (mΩ := mΩ) (μ := μ) W hWm t) m μ := by
  rw [Indep_iff] at hi ⊢
  intro A B hA hB
  obtain ⟨A',hA',he⟩ := exists_natural_event (mΩ := mΩ) W hW hWm hInd hWc t hA
  rw [measure_congr (ae_eq_set_inter he (ae_eq_refl B)),measure_congr he]
  exact hi A' B hA' hB

include hW hInd hWc in
/-- Actual Brownian future independence and adaptation for the usual joint
filtration, derived rather than assumed. -/
theorem coordinateForward (i : ι) :
    CommonItoIsometry.ForwardIndependent (W i) (usual (μ := μ) W hWm) μ where
  adapted t := ((JointNaturalForward.coordinateForward W hW hWm hInd i).adapted t).mono
    (natural_le_usual W hWm t)
  indep t := indep_usual W hW hWm hInd hWc t
    ((JointNaturalForward.coordinateForward W hW hWm hInd i).indep t)

include hW hInd hWc in
/-- The genuine paired future independence needed by multichannel Ito
isometry also persists in the actual usual filtration. -/
theorem pairForward (i j : ι) :
    CommonItoCross.PairForwardIndependent (W i) (W j) (usual (μ := μ) W hWm) μ := by
  intro t
  exact indep_usual W hW hWm hInd hWc t (JointNaturalForward.pairForward W hW hWm hInd i j t)

end LinearStochastic.JointUsualIndependence
