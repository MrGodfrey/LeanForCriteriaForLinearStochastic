module

public import LinearStochastic.HilbertBrownianPath
public import LinearStochastic.MatrixPrefixDecay
public import LinearStochastic.ExpectedStateEnergy

@[expose] public section

/-! Actual construction of a constant-feedback S² state on any finite
interval, with its original control equation, all-time mean-square decay and
finite feedback energy, for arbitrary measurable L² initial data. -/
noncomputable section
namespace LinearStochastic.MatrixFeedbackPath
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality MatrixGrowthBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [IsProbabilityMeasure μ] [𝓕.IsComplete μ] [Nonempty (Fin n)] in
theorem closed_loop_compLp (T : ℝ≥0)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (K : Matrix (Fin r) (Fin n) ℝ)
    (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)) :
    (A+B*K).toEuclideanLin.toContinuousLinearMap.compLp X =
      A.toEuclideanLin.toContinuousLinearMap.compLp X +
      B.toEuclideanLin.toContinuousLinearMap.compLp (K.toEuclideanLin.toContinuousLinearMap.compLp X) := by
  apply Lp.ext
  filter_upwards [(A+B*K).toEuclideanLin.toContinuousLinearMap.coeFn_compLp X,
    A.toEuclideanLin.toContinuousLinearMap.coeFn_compLp X,
    B.toEuclideanLin.toContinuousLinearMap.coeFn_compLp (K.toEuclideanLin.toContinuousLinearMap.compLp X),
    K.toEuclideanLin.toContinuousLinearMap.coeFn_compLp X,Lp.coeFn_add
      (A.toEuclideanLin.toContinuousLinearMap.compLp X)
      (B.toEuclideanLin.toContinuousLinearMap.compLp (K.toEuclideanLin.toContinuousLinearMap.compLp X))]
    with z hf ha hb hk he
  rw [hf,he]
  simp only [Pi.add_apply]
  rw [ha,hb,hk]
  change (A+B*K).toEuclideanLin (X z) = A.toEuclideanLin (X z) + B.toEuclideanLin (K.toEuclideanLin (X z))
  simp only [map_add,Matrix.toLpLin_mul_same,LinearMap.add_apply,LinearMap.comp_apply]

theorem exists_decay (i₀ : Fin m)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (hneg : (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ) :
    ∃ (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
      (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)),
      IsStronglyProgressive 𝓕 R ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T)) ∧
      MemLp (ContinuousDoobL2.pathSup R T) 2 μ ∧
      (X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) ∧
      (R 0 =ᵐ[μ] ξ) ∧
      SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        (A.toEuclideanLin.toContinuousLinearMap.compLp X +
          B.toEuclideanLin.toContinuousLinearMap.compLp ((U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X))
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X +
          (D i).toEuclideanLin.toContinuousLinearMap.compLp ((U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X)) X (R T) ∧
      (∀ t, t ≤ T → R t =ᵐ[μ] integralState (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        ((A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X)
        (fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X) (t:ℝ)) ∧
      (∀ t, t ≤ T → (∫ ω, ‖R t ω‖^2 ∂μ) ≤ conditionNumber P hP.isHermitian * Real.exp (-ρ*(t:ℝ)) *
        (∫ ω, ‖ξ ω‖^2 ∂μ)) ∧
      ‖(U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X‖^2 ≤
        ‖(U*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 *
        (conditionNumber P hP.isHermitian * (∫ ω, ‖ξ ω‖^2 ∂μ) / ρ) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let F := (A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  let N := fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  obtain ⟨X,R,hprog,hcont,hS2,hr,hi,hs,_,he⟩ := HilbertBrownianPath.exists_full_solution b b hW hWm
    i₀ T F 0 N (fun _ => 0) ξ hξ0 hξ 0
  simp only [←ContinuousLinearMap.compLpₗ_apply,map_zero,add_zero] at hs he
  have hd (t : ℝ≥0) (ht : t ≤ T) := MatrixPrefixDecay.mean_square_decay_at
    (fun i => (hW i).toIsPreBrownianReal) hWm hpair hchannels T ρ A B C D P U hP hneg
    ξ hξ hξ0 X R hs hr hi he hprog.stronglyAdapted hcont hS2 t ht
  have hκ : 0 ≤ conditionNumber P hP.isHermitian :=
    (div_pos (MatrixInverseEnergyBounds.max_eigen_pos P hP)
      (MatrixInverseEnergyBounds.min_eigen_pos P hP)).le
  have hM : 0 ≤ conditionNumber P hP.isHermitian * (∫ ω, ‖ξ ω‖^2 ∂μ) :=
    mul_nonneg hκ (integral_nonneg (fun ω => sq_nonneg _))
  have henergy := ExpectedStateEnergy.state_energy_le T X R hr
    (fun t => ((hprog.stronglyAdapted t).mono (𝓕.le t)).aestronglyMeasurable) hcont hS2
    _ ρ hM hρ (fun t ht => by
      convert hd t ht using 1; ring)
  have hcontrol := ExpectedStateEnergy.feedback_energy_le T X
    (U*P⁻¹).toEuclideanLin.toContinuousLinearMap _ ρ henergy
  refine ⟨X,R,hprog,hcont,hS2,hr,hi,?_,he,hd,hcontrol⟩
  have hf := closed_loop_compLp T A B (U*P⁻¹) X
  have hz : (fun i => (N i).compLp X) =
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X +
        (D i).toEuclideanLin.toContinuousLinearMap.compLp ((U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X)) :=
    funext (fun i => closed_loop_compLp T (C i) (D i) (U*P⁻¹) X)
  change SectionIntegralSolution b _ hWm T ξ (F.compLp X) (fun i => (N i).compLp X) X (R T) at hs
  rw [show F.compLp X = _ from hf,hz] at hs
  exact hs

end LinearStochastic.MatrixFeedbackPath
