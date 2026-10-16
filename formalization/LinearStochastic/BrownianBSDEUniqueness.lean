import LinearStochastic.BSDEGlobalUniqueness
import LinearStochastic.BrownianGlobalBSDE

/-! Global backward uniqueness for the original Brownian drivers and their
original usual filtration. Equality means actual H² classes and pathwise
indistinguishability, not equality of arbitrarily chosen representatives. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianBSDEUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard BSDEMatrixPicard BSDEPathData CommonBrownianRepair
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {W : ι → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Any two genuine backward solutions on a complete common filtration agree
in their H² classes and on one event throughout the horizon. -/
theorem global_unique {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ)
    (q r : Solution (𝓕:=𝓕) (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A C η) :
    q.X = r.X ∧ (∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω) := by
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t, W i t ω = repaired hW i t ω :=
    (hW i).mk_ae_forall_eq.mono (fun _ hω t ↦ (hω t).symm)
  have hi (i j : ι) (hij : i ≠ j) :
      IndepFun (fun ω t ↦ repaired hW i t ω) (fun ω t ↦ repaired hW j t ω) μ :=
    (hchannels i j hij).congr (repaired_paths_ae hW i).symm (repaired_paths_ae hW j).symm
  let q' := BrownianGlobalBSDE.change_driver (fun i ↦ (hW i).toIsPreBrownianReal)
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    hWm (repaired_measurable hW) he T A C η q
  let r' := BrownianGlobalBSDE.change_driver (fun i ↦ (hW i).toIsPreBrownianReal)
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    hWm (repaired_measurable hW) he T A C η r
  exact BSDEGlobalUniqueness.global_unique
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    (repaired_measurable hW) (repaired_continuous hW)
    (repaired_pairForward hW hpair) hi i₀ T A C η q' r'

variable [μ.IsComplete]
  (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ)

/-- Actual uniqueness on the original joint Brownian usual filtration needs
no separate independence, MR, continuity-version or small-horizon premise. -/
theorem usual_global_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∀ q r : Solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A C η,
      q.X = r.X ∧ (∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro q r
  exact global_unique hW hWm (JointUsualBrownianGlobal.pairForward hW hWm hInd)
    (fun _ _ hij ↦ hInd.indepFun hij) i₀ T A C η q r

/-- Every genuine F_T L² terminal datum has an actual global solution, and
all such solutions coincide in state/diffusion classes and continuous paths. -/
theorem exists_and_unique (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (hη : ∀ b, AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] (η b) μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ q : Solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A C η,
      ∀ r : Solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
        (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A C η,
        q.X = r.X ∧ (∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  obtain ⟨q⟩ := BrownianGlobalBSDE.exists_global hW hWm hInd i₀ T hT A C η hη
  exact ⟨q,fun r ↦ usual_global_unique hW hWm hInd i₀ T A C η q r⟩

end LinearStochastic.BrownianBSDEUniqueness
