module

public import LinearStochastic.ActualControlProperties

@[expose] public section

/-! Exact terminal controllability permits a target-dependent deterministic
initial state. Its combination with exact null controllability is proved for
actual stochastic integral solutions, retaining both endpoint equations. -/
noncomputable section
namespace LinearStochastic.ExactTerminalProperties
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonItoMultichannel LinearDuality SectionLinearDuality SectionSolutionLinearity

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- An almost-surely identical initial random variable gives exactly the same
actual solution, including its independently prescribed terminal value. -/
theorem initial_congr (T : ℝ≥0) (ξ η XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) (hξη : ξ =ᵐ[μ] η) :
    SectionIntegralSolution b hW hWm T η f φ X XT := by
  have he (s : ℝ) : integralState b hW hWm T ξ f φ s =ᵐ[μ]
      integralState b hW hWm T η f φ s := by
    filter_upwards [hξη] with ω hω
    simp only [integralState,hω]
  constructor
  · filter_upwards [hX.sections] with s hs
    exact hs.trans (he s)
  · exact hX.terminal.trans (he T)

variable (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

/-- Every actual F_T-measurable L² target is reached from some deterministic
initial point, selected together with the finite-energy control. -/
def ExactTerminal : Prop :=
  ∀ η : Lp E 2 μ, AEStronglyMeasurable[𝓕 T] η μ →
    ∃ v u X, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b hW hWm T A B C D v u X η

/-- The exact-terminal plus exact-null interpretation in the manuscript is a
literal equivalence for the controlled integral equation. -/
theorem exact_iff_terminal_and_null :
    ActualControlProperties.Exact (𝓕:=𝓕) b hW hWm T A B C D ↔
      ExactTerminal (𝓕:=𝓕) b hW hWm T A B C D ∧
      ActualControlProperties.ExactNull (𝓕:=𝓕) b hW hWm T A B C D := by
  constructor
  · intro h
    exact ⟨fun η hη => ⟨0,h 0 η hη⟩,
      ActualControlProperties.exact_implies_exactNull b hW hWm T A B C D h⟩
  · rintro ⟨ht,hn⟩ v η hη
    obtain ⟨v₀,u₀,X₀,h₀⟩ := ht η hη
    obtain ⟨u₁,X₁,h₁⟩ := hn (v-v₀)
    have hsum := SectionIntegralSolution.add b hW hWm T (fun _ => v₀) (fun _ => v-v₀)
      (A.compLp X₀+B.compLp u₀) (A.compLp X₁+B.compLp u₁) X₀ X₁
      (fun i => (C i).compLp X₀+(D i).compLp u₀)
      (fun i => (C i).compLp X₁+(D i).compLp u₁) η (0 : Lp E 2 μ) h₀ h₁
    have hi : (fun _ : Ω => v₀)+(fun _ => v-v₀) = fun _ => v := by ext ω; dsimp; abel
    have hd : (A.compLp X₀+B.compLp u₀)+(A.compLp X₁+B.compLp u₁) =
        A.compLp (X₀+X₁)+B.compLp (u₀+u₁) := by
      simp only [←ContinuousLinearMap.compLpₗ_apply,map_add]
      abel
    have hn' : (fun i => (C i).compLp X₀+(D i).compLp u₀)+
        (fun i => (C i).compLp X₁+(D i).compLp u₁) =
        fun i => (C i).compLp (X₀+X₁)+(D i).compLp (u₀+u₁) := by
      funext i
      simp only [Pi.add_apply,←ContinuousLinearMap.compLpₗ_apply,map_add]
      abel
    rw [hi,hd,hn'] at hsum
    refine ⟨u₀+u₁,X₀+X₁,?_⟩
    apply SectionIntegralSolution.terminal_congr b hW hWm T (fun _ => v)
      (η+(0 : Lp E 2 μ) : Ω → E) η _ _ _ hsum
    filter_upwards [Lp.coeFn_zero E 2 μ] with ω hω
    simp only [Pi.add_apply,hω,Pi.zero_apply,add_zero]

end LinearStochastic.ExactTerminalProperties
