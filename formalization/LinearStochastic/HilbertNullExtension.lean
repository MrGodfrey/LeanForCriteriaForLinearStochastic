import LinearStochastic.HilbertPrefixUniqueness
import LinearStochastic.HilbertRestartUniqueness
import LinearStochastic.HilbertBrownianPath
import LinearStochastic.SectionSolutionLinearity

/-! A real null control on a terminal time window extends by zero to a real
null control on the original full horizon. The restart initial value is the
actual uncontrolled state, measurable with respect to the full original past. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertNullExtension
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality LinearDuality VectorHorizonRestriction
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

include c in
theorem exists_null (i₀ : ι) (a δ T : ℝ≥0) (h : a+δ = T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (hnull : ∀ η : Ω → E, StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] η → MemLp η 2 μ →
      ∃ (v : Lp U 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
        (Y : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)),
        SectionIntegralSolution (𝓕:=CommonTimeShift.filtration 𝓕 a) b
          (fun i => ((hW i).shift a).toIsPreBrownianReal)
          (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ η
          (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) Y (0 : Ω → E)) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) X (0 : Ω → E) := by
  have ha : a ≤ T := by rw [←h]; exact le_add_right le_rfl
  obtain ⟨X₀,R₀,hp₀,hc₀,h2₀,hr₀,hi₀,hs₀,_,he₀⟩ :=
    HilbertBrownianPath.exists_full_solution b c hW hWm i₀ T A B C D ξ hξ hξ2 0
  have hprefix := HilbertSectionPrefix.controlled_prefix b (fun i => (hW i).toIsPreBrownianReal) hWm
    ha A B C D ξ (R₀ T) (R₀ a) 0 X₀ hs₀ (he₀ a ha)
  have hη : StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] (R₀ a) := by
    convert hp₀.stronglyAdapted a using 1
    simp [CommonTimeShift.filtration]
  have hη2 : MemLp (R₀ a) 2 μ := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp b
    (fun i => (hW i).toIsPreBrownianReal) hWm a ξ (R₀ a) _ _ _ hprefix hξ2
  obtain ⟨v,Y,hY⟩ := hnull (R₀ a) hη hη2
  let u := VectorH2Extension.extendShift c (hWm i₀) a δ T h.le v
  obtain ⟨X,R,hp,hc,h2,hr,hi,hs,_,he⟩ :=
    HilbertBrownianPath.exists_full_solution b c hW hWm i₀ T A B C D ξ hξ hξ2 u
  have hpzero : restrict ha u = restrict ha (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)) := by
    change restrict ha u = (VectorH2Series.restrictCLM ha) (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    rw [map_zero]
    exact VectorH2Extension.restriction_extendShift_zero c (hWm i₀) a δ T a h.le le_rfl v
  have hstart := HilbertPrefixUniqueness.at_prefix b c hW hWm i₀ ha A B C D ξ hξ hξ2
    u 0 X X₀ (R T) (R₀ T) (R a) (R₀ a) hs hs₀ (he a ha) (he₀ a ha) hpzero
  obtain ⟨S,hSp,hSc,hS2,hSr,hSi,hST,hSe⟩ := HilbertBrownianRealization.exists_realization b c
    (fun i => (hW i).shift a) (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
    i₀ δ A B C D (R₀ a) hη hη2 v Y 0 hY
  have hrestart := HilbertRestartUniqueness.restart b c hW hWm i₀ T A B C D ξ hξ hξ2
    u X (R T) hs a δ h.le (R₀ a) hη hη2 v Y 0 hY R S he hSe hstart
    (VectorH2Extension.shift_extendShift c (hWm i₀) a δ T h.le v)
  have hend : R T =ᵐ[μ] 0 := by
    have hh := (hrestart.2 δ le_rfl).trans hST
    rwa [h] at hh
  exact ⟨u,X,SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (R T) 0 _ X _ hs hend.symm⟩

end LinearStochastic.HilbertNullExtension
