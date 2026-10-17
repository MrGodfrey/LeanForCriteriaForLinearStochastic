module

public import LinearStochastic.ActualControlProperties
public import LinearStochastic.SectionDriverTransport

@[expose] public section

/-! The actual controllability predicates preserve their controls, state
classes and terminal variables when the Brownian driver is repaired on a
common null set. No abstract terminal-map identification is assumed. -/
noncomputable section
namespace LinearStochastic.ControlDriverTransport
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ActualControlProperties
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W V : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (V i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hV : ∀ i, IsPreBrownianReal (V i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))
  (he : ∀ i, ∀ᵐ ω ∂μ, ∀ t, W i t ω = V i t ω)
  (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

include he in
/-- The actual AC predicate is invariant under an indistinguishable repair. -/
theorem approximate_iff :
    Approximate (𝓕:=𝓕) b hW hWm T A B C D ↔ Approximate (𝓕:=𝓕) b hV hVm T A B C D := by
  constructor
  · intro h v η hη ε hε
    obtain ⟨u,X,XT,hX,herr⟩ := h v η hη ε hε
    exact ⟨u,X,XT,SectionDriverTransport.solution b hW hV hWm hVm he T _ _ _ _ _ hX,herr⟩
  · intro h v η hη ε hε
    obtain ⟨u,X,XT,hX,herr⟩ := h v η hη ε hε
    exact ⟨u,X,XT,SectionDriverTransport.solution b hV hW hVm hWm
      (fun i => (he i).mono (fun _ hω t => (hω t).symm)) T _ _ _ _ _ hX,herr⟩

include he in
/-- The actual ANC predicate preserves exactly the same controls and errors. -/
theorem approximateNull_iff :
    ApproximateNull (𝓕:=𝓕) b hW hWm T A B C D ↔ ApproximateNull (𝓕:=𝓕) b hV hVm T A B C D := by
  constructor
  · intro h v ε hε
    obtain ⟨u,X,XT,hX,herr⟩ := h v ε hε
    exact ⟨u,X,XT,SectionDriverTransport.solution b hW hV hWm hVm he T _ _ _ _ _ hX,herr⟩
  · intro h v ε hε
    obtain ⟨u,X,XT,hX,herr⟩ := h v ε hε
    exact ⟨u,X,XT,SectionDriverTransport.solution b hV hW hVm hWm
      (fun i => (he i).mono (fun _ hω t => (hω t).symm)) T _ _ _ _ _ hX,herr⟩

end LinearStochastic.ControlDriverTransport
