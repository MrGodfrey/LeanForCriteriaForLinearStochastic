module

public import LinearStochastic.CommonBrownianGlobal
public import LinearStochastic.UsualVersionFiltration
public import LinearStochastic.JointUsualIndependence

@[expose] public section

/-! Actual global controlled SDEs on the usual augmentation of the original
joint Brownian natural filtration. Brownian paths need only be almost surely
continuous; all repaired-driver and filtration identifications are proved. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.JointUsualBrownianGlobal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonVectorPicard CommonSolutionData CommonBrownianRepair
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ)

include hW hInd
/-- True whole-future independence for the original Brownian motion in its
original usual joint filtration, with no path-continuity strengthening. -/
theorem coordinateForward (i : ι) :
    CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ := by
  letI : ∀ j, CommonItoIsometry.ForwardIndependent (repaired hW j)
      (JointCylinderGeneration.natural (repaired hW) (repaired_measurable hW)) μ :=
    fun j ↦ JointNaturalForward.coordinateForward (repaired hW)
      (fun k ↦ (repaired_brownian hW k).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) j
  have he := UsualVersionFiltration.repaired_usual_eq hWm hW
  rw [he]
  letI : ∀ j, CommonItoIsometry.ForwardIndependent (repaired hW j)
      (JointUsualNatural.usual (μ:=μ) (repaired hW) (repaired_measurable hW)) μ :=
    fun j ↦ JointUsualIndependence.coordinateForward (repaired hW)
      (fun k ↦ (repaired_brownian hW k).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) (repaired_continuous hW) j
  exact UsualVersionFiltration.forward_congr (B:=repaired hW i) ((hW i).mk_ae_forall_eq)

/-- Genuine paired future independence on that same original usual filtration. -/
theorem pairForward (i j : ι) :
    CommonItoCross.PairForwardIndependent (W i) (W j) (JointUsualNatural.usual (μ:=μ) W hWm) μ := by
  letI : ∀ k, CommonItoIsometry.ForwardIndependent (repaired hW k)
      (JointCylinderGeneration.natural (repaired hW) (repaired_measurable hW)) μ :=
    fun k ↦ JointNaturalForward.coordinateForward (repaired hW)
      (fun l ↦ (repaired_brownian hW l).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) k
  have hp := JointUsualIndependence.pairForward (repaired hW)
    (fun k ↦ (repaired_brownian hW k).toIsPreBrownianReal) (repaired_measurable hW)
    (repaired_independent hW hInd) (repaired_continuous hW) i j
  have he := UsualVersionFiltration.repaired_usual_eq hWm hW
  rw [he]
  exact UsualVersionFiltration.pairForward_congr hp ((hW i).mk_ae_forall_eq) ((hW j).mk_ae_forall_eq)

/-- Global existence on the paper's actual usual Brownian filtration, for
ordinary progressive controls on the original complete probability space. -/
theorem exists_global_progressive_control (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ)
    (hξ : ∀ b, StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (v : ν → ℝ≥0 → Ω → ℝ)
    (hv : ∀ b, IsProgressive (JointUsualNatural.usual (μ:=μ) W hWm) (v b))
    (hv2 : ∀ b, MemLp (Function.uncurry (v b)) 2 ((CommonItoCLM.timeMeasure_T T).prod μ)) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ := coordinateForward hW hWm hInd
    ∃ u : ν → H2 (JointUsualNatural.usual (μ:=μ) W hWm) μ T,
      (∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (v b)) ∧
      Nonempty (Solution (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ := coordinateForward hW hWm hInd
  choose u hu using fun b ↦ ProgressivePredictable.exists_predictable_Lp_of_progressive μ (hv b) T 2 (hv2 b)
  exact ⟨u,hu,CommonBrownianGlobal.exists_global hW hWm i₀ T A B C D ξ hξ hξ2 u⟩

/-- Actual full-horizon pathwise uniqueness on the same usual filtration. -/
theorem global_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ)
    (hξ : ∀ b, StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 (JointUsualNatural.usual (μ:=μ) W hWm) μ T) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ := coordinateForward hW hWm hInd
    ∀ q r : Solution (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u,
      ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ := coordinateForward hW hWm hInd
  exact CommonBrownianGlobal.global_unique hW hWm i₀ T A B C D ξ hξ hξ2 u
end LinearStochastic.JointUsualBrownianGlobal
