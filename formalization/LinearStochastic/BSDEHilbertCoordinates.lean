import LinearStochastic.BSDELocal
import LinearStochastic.HilbertLocalSolution

/-! The matrix backward driver is exactly the Hilbert adjoint driver after
orthonormal reconstruction; its signs and transposes are proved explicitly. -/
noncomputable section
namespace LinearStochastic.BSDEHilbertCoordinates
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard LpOrthonormalCoordinates HilbertLocalSolution

section Linear
variable {Λ E κ : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]

/-- Reconstruction preserves the actual negative L² class. -/
theorem assemble_neg (b : OrthonormalBasis κ ℝ E) (f : κ → Lp ℝ 2 ν) :
    assemble b (-f) = -assemble b f := by
  simp only [assemble,Pi.neg_apply,map_neg,Finset.sum_neg_distrib]

/-- Reconstruction commutes with every finite channel sum. -/
theorem assemble_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis κ ℝ E)
    (f : ι → κ → Lp ℝ 2 ν) :
    assemble b (∑ i, f i) = ∑ i, assemble b (f i) := by
  simp only [assemble,Finset.sum_apply,map_sum]
  exact Finset.sum_comm
end Linear

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Transposition in a real orthonormal basis is the actual Hilbert adjoint. -/
theorem coefficientMatrix_adjoint (A : E →L[ℝ] E) :
    coefficientMatrix b b A.adjoint = (coefficientMatrix b b A).transpose := by
  ext a j
  change inner ℝ (b a) (A.adjoint (b j)) = inner ℝ (b j) (A (b a))
  rw [A.adjoint_inner_right]
  exact real_inner_comm _ _

/-- The complete coordinate driver, including all diffusion-adjoint terms,
reconstructs to the literal Hilbert-valued backward drift. -/
theorem assemble_driver (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (X : BSDEMatrixPicard.PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    assemble (mΛ:=𝓕.predictable) b
      (BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i => coefficientMatrix b b (C i)) X) =
      A.adjoint.compLp (assemble (mΛ:=𝓕.predictable) b X.1) +
        ∑ i, (C i).adjoint.compLp (assemble (mΛ:=𝓕.predictable) b (fun a => X.2 a i)) := by
  rw [BSDEMatrixPicard.driver,assemble_add (mΛ:=𝓕.predictable),assemble_sum (mΛ:=𝓕.predictable)]
  rw [← coefficientMatrix_adjoint,assemble_matrixAction]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← coefficientMatrix_adjoint,assemble_matrixAction]

end LinearStochastic.BSDEHilbertCoordinates
