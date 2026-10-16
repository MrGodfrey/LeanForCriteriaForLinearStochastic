import LinearStochastic.KnownTargetSolution

/-! Earlier-measurable L² target classes are attained by the concrete
Gramian control and true raw zero-diffusion solution. -/
noncomputable section
namespace LinearStochastic.KnownTargetLpReaching
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open CommonItoMultichannel ProgressiveControlSection
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (A : E →L[ℝ] E) (B : U →L[ℝ] E) (a T : ℝ≥0) (ha : a<T)
  (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v)=0) → v=0)

include ha hK in
/-- Every earlier-measurable L² class has a true ordinary-progressive
Gramian realization, including an exact terminal a.e. equality and zero prefix. -/
theorem exists_solution (x : E) (η : Lp E 2 μ) (hη : AEStronglyMeasurable[𝓕 a] η μ) :
    ∃ (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
      (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      RawSolution b hW hWm T (fun _=>x) A B (fun _=>0) (fun _=>0) v R u X ∧
      R T =ᵐ[μ] η ∧ (∀ t, t≤a → ∀ ω, v t ω=0) := by
  let ζ := hη.mk η
  have hζ : StronglyMeasurable[𝓕 a] ζ := hη.stronglyMeasurable_mk
  have hζae : (η : Ω → E) =ᵐ[μ] ζ := hη.ae_eq_mk
  have hζ2 : MemLp ζ 2 μ := (memLp_congr_ae hζae).mp (Lp.memLp η)
  obtain ⟨u,X,hsol,hterm,hzero⟩ := KnownTargetSolution.exists_solution b hW hWm A B a T ha hK x ζ hζ hζ2
  refine ⟨_,_,u,X,hsol,?_,hzero⟩
  filter_upwards [hζae] with ω hω
  exact (hterm ω).trans hω.symm

end LinearStochastic.KnownTargetLpReaching
