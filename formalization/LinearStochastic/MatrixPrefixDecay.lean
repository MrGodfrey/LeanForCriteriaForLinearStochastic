module

public import LinearStochastic.MatrixSectionDecay
public import LinearStochastic.ProcessHorizonS2

@[expose] public section

/-! The manuscript's actual mean-square decay formula with its exact spectral
condition number, for the genuine closed-loop SDE and ordinary matrix gain UP⁻¹. -/
noncomputable section
namespace LinearStochastic.MatrixPrefixDecay
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality MatrixGrowthBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem mean_square_decay_at
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (ρ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (hneg : (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ)
    (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hX : SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T ξ
      ((A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X)
      (fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X) X (R T))
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (hi : R 0 =ᵐ[μ] ξ)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] integralState (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T ξ
      ((A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X)
      (fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X) (t:ℝ))
    (ha : StronglyAdapted 𝓕 R)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖R t ω‖^2 ∂μ) ≤ conditionNumber P hP.isHermitian * Real.exp (-ρ*(t:ℝ)) *
      (∫ ω, ‖ξ ω‖^2 ∂μ) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let F := (A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  let N := fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  let Xt := VectorHorizonRestriction.restrict ht X
  have hs := SectionHorizonRestriction.section_restrict b hW hWm ht ξ (R T) (R t)
    (F.compLp X) X (fun i => (N i).compLp X) hX (he t ht)
  have hf : VectorHorizonRestriction.restrict ht (F.compLp X) = F.compLp Xt :=
    VectorHorizonRestriction.restrict_comp ht F X
  have hz : (fun i => VectorHorizonRestriction.restrict ht ((N i).compLp X)) =
      (fun i => (N i).compLp Xt) := funext (fun i => VectorHorizonRestriction.restrict_comp ht (N i) X)
  rw [hf,hz] at hs
  have het (s : ℝ≥0) (hs' : s ≤ t) : R s =ᵐ[μ] integralState b hW hWm t ξ
      (F.compLp Xt) (fun i => (N i).compLp Xt) (s:ℝ) := by
    have h := SectionHorizonRestriction.integralState_restrict b hW hWm ht s hs' ξ
      (F.compLp X) (fun i => (N i).compLp X)
    rw [hf,hz] at h
    exact (he s (hs'.trans ht)).trans h.symm
  exact MatrixSectionDecay.mean_square_decay hW hWm hpair hchannels t ρ A B C D P U hP hneg
    ξ hξ hξ0 Xt R hs (ProcessQuadraticInner.restrict_representative ht X R hr) hi het
    (fun s => ((ha s).mono (𝓕.le s)).aestronglyMeasurable)
    (hc.mono (fun _ hω => hω.mono (Iic_subset_Iic.mpr ht)))
    (ProcessHorizonS2.prefix_memLp ht R ha hc h2)

end LinearStochastic.MatrixPrefixDecay
