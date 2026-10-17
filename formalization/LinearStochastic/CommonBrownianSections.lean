module

public import LinearStochastic.CommonSectionSolution
public import LinearStochastic.CommonBrownianGlobal

@[expose] public section

/-! Canonical continuous S² versions of actual section solutions for the
original Brownian motion, without an all-sample continuous-path assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonBrownianSections
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData CommonBrownianRepair
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- Genuine section equations transfer across indistinguishable drivers by
equality of the constructed process-time integral operators. -/
theorem sections_congr {W V : ι → ℝ≥0 → Ω → ℝ}
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (V i) 𝓕 μ]
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hV : ∀ i, IsPreBrownianReal (V i) μ)
    (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))
    (he : ∀ i, ∀ᵐ ω ∂μ, ∀ t, W i t ω = V i t ω)
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : CommonSectionSolution.Sections hW hWm T A B C D ξ u X) :
    CommonSectionSolution.Sections hV hVm T A B C D ξ u X := by
  intro b
  filter_upwards [hX b] with t ht
  filter_upwards [ht] with ω hω
  apply hω.trans
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f : Lp ℝ 2 μ ↦ f ω)
    (CommonItoVersion.process_congr (hW i) (hV i) (hWm i) (hVm i) (he i) T t
      (noiseInput T C D u X i b))

variable [𝓕.IsComplete μ] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Construct a continuous S² solution of the original-driver equation from
its genuine H² sections. The original predictable state class is retained. -/
def ofSections (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : CommonSectionSolution.Sections (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u X) :
    Solution (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u := by
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t, W i t ω = repaired hW i t ω :=
    (hW i).mk_ae_forall_eq.mono (fun _ hω t ↦ (hω t).symm)
  have hs := sections_congr (fun i ↦ (hW i).toIsPreBrownianReal)
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal) hWm (repaired_measurable hW)
    he T A B C D ξ u X hX
  let q := CommonSectionSolution.ofSections
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW)
    (repaired_continuous hW) i₀ T A B C D ξ hξ hξ2 u X hs
  exact CommonBrownianGlobal.change_driver
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
    (fun i ↦ (hW i).toIsPreBrownianReal) (repaired_measurable hW) hWm
    (fun i ↦ (hW i).mk_ae_forall_eq) T A B C D ξ u q

/-- The construction preserves the actual supplied H² class definitionally. -/
theorem ofSections_class (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : CommonSectionSolution.Sections (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u X) :
    (ofSections hW hWm i₀ T A B C D ξ hξ hξ2 u X hX).X = X := rfl

/-- The separately supplied true original-driver terminal identity agrees with
the terminal value of the constructed continuous version. -/
theorem terminal_ofSections (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : CommonSectionSolution.Sections (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D ξ u X)
    (XT : κ → Ω → ℝ)
    (hXT : ∀ b, XT b =ᵐ[μ] fun ω ↦ ξ b ω +
      (∫ s in Ioc (0 : ℝ≥0) T, driftInput T A B u X b (s,ω) ∂CommonItoL2.timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i).toIsPreBrownianReal T T (hWm i)
        (noiseInput T C D u X i b) ω) (b : κ) :
    XT b =ᵐ[μ] (ofSections hW hWm i₀ T A B C D ξ hξ hξ2 u X hX).path b T := by
  exact (hXT b).trans ((ofSections hW hWm i₀ T A B C D ξ hξ hξ2 u X hX).equation b T le_rfl).symm

end LinearStochastic.CommonBrownianSections
