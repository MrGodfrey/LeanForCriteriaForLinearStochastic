module

public import LinearStochastic.UsualGlobalBSDE
public import LinearStochastic.JointUsualBrownianGlobal

@[expose] public section

/-! Backward solution transport to the original Brownian paths and their
original usual filtration. No everywhere-continuous-path premise remains. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianGlobalBSDE
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonVectorPicard BSDEMatrixPicard BSDEPathData CommonBrownianRepair
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Actual backward data transports along indistinguishable drivers because
the constructed process-time Itô operators have already been proved equal. -/
def change_driver {W V : ι → ℝ≥0 → Ω → ℝ}
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (V i) 𝓕 μ]
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hV : ∀ i, IsPreBrownianReal (V i) μ)
    (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))
    (he : ∀ i, ∀ᵐ ω ∂μ, ∀ t, W i t ω = V i t ω)
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm T A C η) :
    Solution (𝓕:=𝓕) hV hVm T A C η := by
  refine ⟨q.X,q.path,q.progressive,q.continuous,q.squareSup,q.representative,q.terminal,?_⟩
  intro b t ht
  filter_upwards [q.equation b t ht] with ω hω
  apply hω.trans
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f : Lp ℝ 2 μ ↦ f ω)
    (CommonItoVersion.process_congr (hW i) (hV i) (hWm i) (hVm i) (he i) T t (q.X.2 b i))

/-- Equality of actual filtrations transports the entire dependent solution
record, including its predictable L² classes. -/
def change_filtration {𝓖 : Filtration ℝ≥0 mΩ} (he : 𝓕 = 𝓖)
    {W : ι → ℝ≥0 → Ω → ℝ}
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓖 μ]
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓖) hW hWm T A C η) :
    Solution (𝓕:=𝓕) hW hWm T A C η := by
  cases he
  exact q

variable [μ.IsComplete] {W : ι → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ)

/-- Actual arbitrary-horizon adjoint BSDE existence under the paper's Brownian
path and usual-filtration assumptions, with no strengthened continuity, MR,
small-time, or solution-existence premise. -/
theorem exists_global (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (hη : ∀ b, AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] (η b) μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    Nonempty (Solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A C η) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have he := UsualVersionFiltration.repaired_usual_eq hWm hW
  have hη' (b : κ) : AEStronglyMeasurable[
      JointUsualNatural.usual (μ:=μ) (repaired hW) (repaired_measurable hW) T] (η b) μ := by
    apply (hη b).mono
    rw [he]
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (JointCylinderGeneration.natural (repaired hW) (repaired_measurable hW)) μ :=
    fun i ↦ JointNaturalForward.coordinateForward (repaired hW)
      (fun j ↦ (repaired_brownian hW j).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (JointUsualNatural.usual (μ:=μ) (repaired hW) (repaired_measurable hW)) μ :=
    fun i ↦ JointUsualIndependence.coordinateForward (repaired hW)
      (fun j ↦ (repaired_brownian hW j).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) (repaired_continuous hW) i
  obtain ⟨q'⟩ := UsualGlobalBSDE.exists_global (repaired hW)
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    (repaired_measurable hW) (repaired_independent hW hInd) (repaired_continuous hW)
    i₀ T hT A C η hη'
  let q := change_filtration he
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    (repaired_measurable hW) T A C η q'
  exact ⟨change_driver
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    (fun i ↦ (hW i).toIsPreBrownianReal) (repaired_measurable hW) hWm
    (fun i ↦ (hW i).mk_ae_forall_eq) T A C η q⟩

end LinearStochastic.BrownianGlobalBSDE
