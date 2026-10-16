import LinearStochastic.InvariantAdjointDynamics
import LinearStochastic.AlgebraFlagTransport

/-! Exact real-matrix specialization of the genuine zero-observation flag
argument, using the same ordinary-coordinate flag as the rank criterion. -/
noncomputable section
namespace LinearStochastic.ZeroObservationMatrices
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality

variable {n r m : ℕ}

def matrixMap {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    EuclideanSpace ℝ (Fin b) →L[ℝ] EuclideanSpace ℝ (Fin a) :=
  M.toEuclideanLin.toContinuousLinearMap

/-- The literal transpose recursion and the actual Euclidean-adjoint SDE
coefficients have exactly the same vanishing flag at every iteration. -/
theorem matrix_flag_bot_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (k : ℕ) :
    (AdjointCoefficients.fromMatrices A B C D).flag k = ⊥ ↔
      (ZeroObservationFlag.coefficients (matrixMap A) (matrixMap B)
        (fun i => matrixMap (C i)) (fun i => matrixMap (D i))).flag k = ⊥ := by
  rw [InvariantAdjointDynamics.coefficients_eq_fromForward]
  exact AdjointCoefficients.matrix_flag_bot_iff_euclidean A B C D k

section Stochastic
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Literal real matrix flag zero implies terminal uniqueness for every
actual zero-observation adjoint solution of those same coefficient matrices. -/
theorem terminal_zero
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (η YT : Ω → EuclideanSpace ℝ (Fin n))
    (Y : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
    (Z : Fin m → Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T η
      (-((matrixMap A).adjoint.compLp Y + ∑ i, (matrixMap (C i)).adjoint.compLp (Z i))) Z Y YT)
    (realization : ContinuousRealization T η Y YT)
    (hobs : (matrixMap B).adjoint.compLp Y + ∑ i, (matrixMap (D i)).adjoint.compLp (Z i) = 0)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) : YT =ᵐ[μ] 0 := by
  apply ZeroObservationFlag.terminal_zero_of_flag_bot (EuclideanSpace.basisFun (Fin n) ℝ)
    hW hWm hpair hchannels T hT (matrixMap A) (matrixMap B)
    (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) η YT Y Z hY realization hobs
  simpa only [finrank_euclideanSpace_fin] using (matrix_flag_bot_iff A B C D n).mp hflag
end Stochastic

#print axioms terminal_zero
end LinearStochastic.ZeroObservationMatrices
