import LinearStochastic.BrownianInitialTrivial
import LinearStochastic.ExactDiffusionAlgebra
import LinearStochastic.ExactTerminalProperties
import LinearStochastic.BSDEHilbertGlobal
import LinearStochastic.BrownianGlobalBSDE

/-! Surjective joint diffusion yields exact terminal controllability on the
original usual Brownian filtration. The initial value is proved deterministic
using actual F₀ triviality, and the control uses the canonical diffusion inverse. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianExactTerminal
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel HilbertLocalSolution SectionLinearDuality ExactDiffusionAlgebra
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

/-- At every prescribed positive horizon, every original F_T-measurable L²
target is attained from a deterministic initial point by the original equation.
There is no martingale-representation, backward-existence, or F₀-triviality premise. -/
theorem exact_terminal (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toLinearMap))) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ExactTerminalProperties.ExactTerminal (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro η hη
  let F := effectiveDrift D hD A B C
  let G := noiseDrift D hD B
  have hηc (j : κ) : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T]
      (VectorItoProduct.coordinate b j η) μ :=
    ((innerSL ℝ (b j)).continuous.comp_aestronglyMeasurable hη).congr
      (VectorItoProduct.coordinate_ae b j η).symm
  obtain ⟨q⟩ := BrownianGlobalBSDE.exists_global hW hWm hInd i₀ T hT
    (coefficientMatrix b b (-F.adjoint)) (fun i => coefficientMatrix b b (-(G i).adjoint))
    (fun j => VectorItoProduct.coordinate b j η) hηc
  obtain ⟨ξ,hξ,hξ2,Y,Z,hY,_⟩ := BSDEHilbertGlobal.section_backward b
    (fun i => (hW i).toIsPreBrownianReal) hWm T (-F.adjoint) (fun i => -(G i).adjoint) η q
  have hn (L : E →L[ℝ] E) (X : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)) :
      (-L).compLp X = -(L.compLp X) := by
    rw [←neg_one_smul ℝ L,ContinuousLinearMap.smul_compLp,neg_one_smul]
  have hd : -((-F.adjoint).adjoint.compLp Y+∑ i, (-(G i).adjoint).adjoint.compLp (Z i)) =
      F.compLp Y+∑ i, (G i).compLp (Z i) := by
    simp only [map_neg,ContinuousLinearMap.adjoint_adjoint,
      hn,Finset.sum_neg_distrib,neg_add_rev,neg_neg]
    abel
  rw [hd] at hY
  obtain ⟨v,hv⟩ := BrownianInitialTrivial.vector_initial_constant hW hWm hInd b ξ hξ hξ2
  have hconst := ExactTerminalProperties.initial_congr b
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (fun _ => v) η _ Y Z hY hv
  refine ⟨v,ExactDiffusionAlgebra.control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD C Y Z,Y,?_⟩
  change SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v)
    (A.compLp Y+B.compLp (ExactDiffusionAlgebra.control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD C Y Z))
    (fun i => (C i).compLp Y+(D i).compLp (ExactDiffusionAlgebra.control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD C Y Z)) Y η
  have hdiff : (fun i => (C i).compLp Y+(D i).compLp
      (ExactDiffusionAlgebra.control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD C Y Z)) = Z :=
    funext (diffusion_control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD C Y Z)
  rw [drift_control (mΛ:=(JointUsualNatural.usual (μ:=μ) W hWm).predictable) D hD A B C Y Z,hdiff]
  exact hconst

/-- Surjective joint diffusion and actual exact-null controllability imply
actual exact controllability. The only remaining controllability premise is
explicitly ENC, to be discharged by the separately proved switching theorem. -/
theorem exact_of_exactNull (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toLinearMap))) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ActualControlProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D →
    ActualControlProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro hn
  exact (ExactTerminalProperties.exact_iff_terminal_and_null b
    (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D).mpr
      ⟨exact_terminal b hW hWm hInd i₀ T hT A B C D hD,hn⟩

end LinearStochastic.BrownianExactTerminal
