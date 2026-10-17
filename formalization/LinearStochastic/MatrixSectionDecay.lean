module

public import LinearStochastic.SectionExponentialEnergy
public import LinearStochastic.MatrixInverseEnergyBounds
public import LinearStochastic.QuadraticMomentBounds

@[expose] public section

/-! The manuscript's actual mean-square decay formula with its exact spectral
condition number, for the genuine closed-loop SDE and ordinary matrix gain UP⁻¹. -/
noncomputable section
namespace LinearStochastic.MatrixSectionDecay
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality MatrixGrowthBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem mean_square_decay
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
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    (∫ ω, ‖R T ω‖^2 ∂μ) ≤ conditionNumber P hP.isHermitian * Real.exp (-ρ*(T:ℝ)) *
      (∫ ω, ‖ξ ω‖^2 ∂μ) := by
  let H := (P⁻¹).toEuclideanLin.toContinuousLinearMap
  let F := (A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  let N := fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap
  have hs : H.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.inv.isHermitian
  have hq (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, inner ℝ (N i x) (H (N i x))) + 2*inner ℝ (F x) (H x) ≤ -ρ*inner ℝ x (H x) := by
    by_cases hx : x = 0
    · subst x
      simp only [map_zero,inner_zero_left,mul_zero,Finset.sum_const_zero,add_zero,le_refl]
    · have h := MatrixFeedback.matrix_closed_loop_quadratic A B C D ρ P U hP hneg x hx
      change 2*inner ℝ (F x) (H x)+ρ*inner ℝ x (H x)+(∑ i, inner ℝ (N i x) (H (N i x))) < 0 at h
      linarith
  have hd := SectionExponentialEnergy.exponential_energy (EuclideanSpace.basisFun (Fin n) ℝ)
    hW hWm hpair hchannels T H F N ρ hs hq ξ hξ hξ0 X R hX hr hi he hm hc h2
  have ht := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp
    (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T ξ (R T) _ X _ hX hξ
  have hb := MatrixInverseEnergyBounds.inverse_quadratic_bounds P hP
  have hres := QuadraticMomentBounds.moment_le_of_energy_le H
    (maxEigenvalue P hP.isHermitian)⁻¹ (minEigenvalue P hP.isHermitian)⁻¹
    (Real.exp (-ρ*(T:ℝ))) (inv_pos.mpr (MatrixInverseEnergyBounds.max_eigen_pos P hP))
    (Real.exp_nonneg _) (fun x => (hb x).1) (fun x => (hb x).2) (R T) ξ ht hξ
    (by simpa only [mul_comm] using hd)
  simpa only [conditionNumber,div_eq_mul_inv,inv_inv,mul_comm,mul_left_comm,mul_assoc] using hres

end LinearStochastic.MatrixSectionDecay
