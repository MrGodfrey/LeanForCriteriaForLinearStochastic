import LinearStochastic.CommonFiltrationCompletion
import LinearStochastic.VectorItoProduct

/-! Continuous S² versions of the actual finite-channel vector Itô integral on
an arbitrary complete common filtration. The input space and terminal integral
are the same as in VectorItoProduct; no canonical probability-space replacement
or martingale representation hypothesis is introduced. -/
noncomputable section
namespace LinearStochastic.CommonVectorS2
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open CommonItoMultichannel CommonItoMartingaleVersion VectorItoProduct

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hWc

/-- A continuous true martingale version with an actual whole-interval S²
estimate, of the already constructed orthonormal-coordinate vector integral. -/
theorem exists_continuous_s2_vector (T : ℝ≥0)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ X : ℝ≥0 → Ω → E,
      (∀ t, t ≤ T → X t =ᵐ[μ] vectorProcess b hW hWm T φ t) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧ Martingale X 𝓕 μ ∧
      MemLp (ContinuousDoobL2.pathSup X T) 2 μ ∧
      eLpNorm (ContinuousDoobL2.pathSup X T) 2 μ ≤
        2 * eLpNorm (vectorProcess b hW hWm T φ T) 2 μ ∧
      Integrable (fun ω ↦ ContinuousDoobL2.pathSup X T ω ^ 2) μ := by
  classical
  have hex := fun (a : κ) (i : ι) ↦
    CommonFiltrationCompletion.exists_s2_on_complete_filtration
      (hW i) T (hWm i) (hWc i) (coordinate b a (φ i))
  choose Y hYeq hYc hYm hYlp hYbound hYint using hex
  let X : ℝ≥0 → Ω → E := fun t ω ↦ ∑ a, (∑ i, Y a i t ω) • b a
  have heq (t : ℝ≥0) (ht : t ≤ T) : X t =ᵐ[μ] vectorProcess b hW hWm T φ t := by
    have hall : ∀ᵐ ω ∂μ, ∀ a i, Y a i t ω =
        integralProcess (hW i) T (hWm i) (coordinate b a (φ i)) t ω := by
      simp only [ae_all_iff]
      intro a i
      exact (hYeq a i t ht).trans (integralProcess_ae_eq (hW i) T t (hWm i) _).symm
    filter_upwards [hall] with ω hω
    simp only [X, vectorProcess, ItoExpectedProduct.sumProcess]
    exact Finset.sum_congr rfl fun a _ ↦ congrArg (fun x : ℝ ↦ x • b a)
      (Finset.sum_congr rfl fun i _ ↦ hω a i)
  have hc (ω : Ω) : Continuous fun t ↦ X t ω := by
    apply continuous_finsetSum
    intro a _
    exact (continuous_finsetSum _ fun i _ ↦ hYc a i ω).smul continuous_const
  have hm : Martingale X 𝓕 μ := by
    apply martingale_sum
    intro a
    exact martingale_map _ (martingale_sum (fun i ↦ Y a i) (hYm a))
      (ContinuousLinearMap.toSpanSingleton ℝ (b a))
  have hT : MemLp (X T) 2 μ :=
    (memLp_congr_ae (heq T le_rfl)).mpr (vectorProcess_memLp b hW hWm T T φ)
  refine ⟨X, heq, hc, hm, ContinuousDoobL2.pathSup_memLp hm hc T hT, ?_,
    ContinuousDoobL2.integrable_pathSup_sq hm hc T hT⟩
  calc
    _ ≤ 2 * eLpNorm (X T) 2 μ := ContinuousDoobL2.pathSup_eLpNorm_le hm hc T
    _ = _ := by rw [eLpNorm_congr_ae (heq T le_rfl)]

end LinearStochastic.CommonVectorS2
