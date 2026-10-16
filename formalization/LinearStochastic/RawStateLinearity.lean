import LinearStochastic.HilbertStateUniqueness
import LinearStochastic.ProgressiveControlSection

/-! Linearity of the full original state process. Two arbitrary raw S²
solutions and any solution driven by the linear-combination data agree on one
probability-one event for the whole closed horizon. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.RawStateLinearity
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality SectionSolutionLinearity ProgressiveControlSection
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
/-- Genuine initial/control linearity as equality of H² state classes and
pathwise indistinguishability, with every actual initial and terminal retained. -/
theorem linear_combination (i₀ : ι) (T : ℝ≥0) (hT : 0<T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ η : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hη : StronglyMeasurable[𝓕 0] η)
    (hξ2 : MemLp ξ 2 μ) (hη2 : MemLp η 2 μ) (a d : ℝ)
    (v w : ℝ≥0 → Ω → U) (R S P : ℝ≥0 → Ω → E)
    (u z : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X Y H : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (q : RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X)
    (r : RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T η A B C D w S z Y)
    (p : RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (a • ξ+d • η) A B C D
      (fun t ω => a • v t ω+d • w t ω) P (a • u+d • z) H) :
    H=a • X+d • Y ∧ ∀ᵐ ω ∂μ, ∀ t, t≤T → P t ω=a • R t ω+d • S t ω := by
  have hx := q.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X
  have hy := r.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T η A B C D w S z Y
  have hx' := SectionSolutionLinearity.SectionIntegralSolution.smul b (fun i => (hW i).toIsPreBrownianReal) hWm T a ξ (R T) _ X _ hx
  have hy' := SectionSolutionLinearity.SectionIntegralSolution.smul b (fun i => (hW i).toIsPreBrownianReal) hWm T d η (S T) _ Y _ hy
  have hh := SectionSolutionLinearity.SectionIntegralSolution.add b (fun i => (hW i).toIsPreBrownianReal) hWm T (a • ξ) (d • η)
    _ _ _ _ _ _ (a • R T) (d • S T) hx' hy'
  have hd : A.compLp (a • X+d • Y)+B.compLp (a • u+d • z) =
      a • (A.compLp X+B.compLp u)+d • (A.compLp Y+B.compLp z) := by
    simp only [←ContinuousLinearMap.compLpₗ_apply,map_add,map_smul,smul_add]
    abel
  have hz : (fun i => (C i).compLp (a • X+d • Y)+(D i).compLp (a • u+d • z)) =
      a • (fun i => (C i).compLp X+(D i).compLp u)+d • (fun i => (C i).compLp Y+(D i).compLp z) := by
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,←ContinuousLinearMap.compLpₗ_apply,map_add,map_smul,smul_add]
    abel
  rw [←hd,←hz] at hh
  have hp := p.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T (a • ξ+d • η)
    A B C D _ P (a • u+d • z) H
  have he := HilbertStateUniqueness.state_unique b c hW hWm i₀ T A B C D
    (a • ξ+d • η) ((hξ.const_smul a).add (hη.const_smul d))
    ((hξ2.const_smul a).add (hη2.const_smul d)) (a • u+d • z)
    H (a • X+d • Y) (P T) (a • R T+d • S T) hp hh
  refine ⟨he,?_⟩
  have hs : (a • X+d • Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
      =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (fun t ω => a • R t ω+d • S t ω) := by
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_add (a • X) (d • Y)),
      ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_smul a X),
      ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_smul d Y),q.state_rep,r.state_rep]
      with z ha hx hy hR hS
    simp only [ha,Pi.add_apply,hx,hy,Pi.smul_apply,hR,hS]
    rfl
  have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => a • R t ω+d • S t ω) (Iic T) := by
    filter_upwards [q.continuous,r.continuous] with ω hR hS
    exact (hR.const_smul a).add (hS.const_smul d)
  apply CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT P _ p.continuous hc
  have hrep := p.state_rep
  rw [he] at hrep
  exact hrep.symm.trans hs
end LinearStochastic.RawStateLinearity
