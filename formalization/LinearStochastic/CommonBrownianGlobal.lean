import LinearStochastic.CommonGlobalExistence
import LinearStochastic.CommonGlobalUniqueness
import LinearStochastic.CommonBrownianRepair

/-! Global controlled SDE existence and pathwise uniqueness for actual Brownian
motions with almost-sure continuous paths. The continuous version is constructed
on the same probability space and every stochastic integral is transported back
to the original driver by a proved equality of the constructed operators. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonBrownianGlobal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution CommonSolutionData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- Genuine driver-version transport changes neither the actual path nor its
predictable class; compatibility is proved for the actual Itô process CLMs. -/
def change_driver {W V : ι → ℝ≥0 → Ω → ℝ}
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (V i) 𝓕 μ]
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hV : ∀ i, IsPreBrownianReal (V i) μ)
    (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))
    (he : ∀ i, ∀ᵐ ω ∂μ, ∀ t, W i t ω = V i t ω)
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u) :
    Solution hV hVm T A B C D ξ u := by
  refine ⟨q.X,q.path,q.progressive,q.continuous,q.squareSup,q.representative,q.initial,?_⟩
  intro b t ht
  filter_upwards [q.equation b t ht] with ω hω
  apply hω.trans
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f : Lp ℝ 2 μ ↦ f ω)
    (CommonItoVersion.process_congr (hW i) (hV i) (hWm i) (hVm i) (he i) T t
      (noiseInput T C D u q.X i b))

variable [𝓕.IsComplete μ] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Actual global existence for ordinary Brownian motions, with no every-path
continuity assumption and no canonical-space replacement. -/
theorem exists_global (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) :
    Nonempty (Solution (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u) := by
  obtain ⟨q⟩ := CommonGlobalExistence.exists_global
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hW i).toIsPreBrownianReal)
    (CommonBrownianRepair.repaired_measurable hW) (CommonBrownianRepair.repaired_continuous hW)
    i₀ T A B C D ξ hξ hξ2 u
  exact ⟨change_driver
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hW i).toIsPreBrownianReal)
    (fun i ↦ (hW i).toIsPreBrownianReal) (CommonBrownianRepair.repaired_measurable hW) hWm
    (fun i ↦ (hW i).mk_ae_forall_eq) T A B C D ξ u q⟩

/-- Every two actual continuous S² solutions driven by the original Brownian
motions are indistinguishable on the entire finite horizon. -/
theorem global_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q r : Solution (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t, W i t ω = CommonBrownianRepair.repaired hW i t ω :=
    (hW i).mk_ae_forall_eq.mono (fun _ hω t ↦ (hω t).symm)
  let q' := change_driver (fun i ↦ (hW i).toIsPreBrownianReal)
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hW i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hW) he T A B C D ξ u q
  let r' := change_driver (fun i ↦ (hW i).toIsPreBrownianReal)
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hW i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hW) he T A B C D ξ u r
  exact CommonGlobalUniqueness.global_unique
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hW i).toIsPreBrownianReal)
    (CommonBrownianRepair.repaired_measurable hW) (CommonBrownianRepair.repaired_continuous hW)
    i₀ T A B C D ξ hξ hξ2 u q' r'
end LinearStochastic.CommonBrownianGlobal
