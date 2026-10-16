import LinearStochastic.ItoExpectedProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace LinearStochastic.VectorItoProduct
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel ItoExpectedProduct

section Basic
variable {Ω E F κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem martingale_map (M : ℝ≥0 → Ω → E) (hM : Martingale M 𝓕 μ)
    (L : E →L[ℝ] F) : Martingale (fun t ω => L (M t ω)) 𝓕 μ := by
  refine ⟨fun t => L.continuous.comp_stronglyMeasurable (hM.1 t), ?_⟩
  intro s t hst
  exact (L.comp_condExp_comm (hM.integrable t)).symm.trans
    ((hM.2 s t hst).fun_comp L)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem martingale_sum [Fintype κ] (M : κ → ℝ≥0 → Ω → E)
    (hM : ∀ a, Martingale (M a) 𝓕 μ) :
    Martingale (fun t ω => ∑ a, M a t ω) 𝓕 μ := by
  classical
  have hs (s : Finset κ) : Martingale (fun t ω => ∑ a ∈ s, M a t ω) 𝓕 μ := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero E 𝓕 μ
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hM a).add ih
  exact hs Finset.univ
end Basic

section Coordinates
variable {Ω E κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] (b : OrthonormalBasis κ ℝ E)

def coordinate (a : κ) (f : Lp E 2 μ) : Lp ℝ 2 μ :=
  (innerSL ℝ (b a)).compLp f

omit [CompleteSpace E] in
theorem coordinate_ae (a : κ) (f : Lp E 2 μ) :
    coordinate b a f =ᵐ[μ] fun ω => inner ℝ (b a) (f ω) :=
  (innerSL ℝ (b a)).coeFn_compLp f

omit [CompleteSpace E] in
theorem coordinate_inner_sum (f g : Lp E 2 μ) :
    (∑ a, inner ℝ (coordinate b a f) (coordinate b a g)) = inner ℝ f g := by
  simp only [L2.inner_def]
  rw [← integral_finsetSum Finset.univ (fun a _ => L2.integrable_inner (coordinate b a f) (coordinate b a g))]
  apply integral_congr_ae
  have hf : ∀ᵐ ω ∂μ, ∀ a, coordinate b a f ω = inner ℝ (b a) (f ω) := by
    rw [ae_all_iff]; exact fun a => coordinate_ae b a f
  have hg : ∀ᵐ ω ∂μ, ∀ a, coordinate b a g ω = inner ℝ (b a) (g ω) := by
    rw [ae_all_iff]; exact fun a => coordinate_ae b a g
  filter_upwards [hf,hg] with ω hf hg
  change (∑ a, inner ℝ (coordinate b a f ω) (coordinate b a g ω)) = inner ℝ (f ω) (g ω)
  calc
    _ = ∑ a, inner ℝ (f ω) (b a) * inner ℝ (b a) (g ω) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hf a, hg a, Real.inner_apply, real_inner_comm (b a) (f ω)]
    _ = _ := b.sum_inner_mul_inner (f ω) (g ω)

omit [CompleteSpace E] in
theorem inner_reconstruct (u v : κ → ℝ) :
    inner ℝ (∑ a, u a • b a) (∑ a, v a • b a) = ∑ a, inner ℝ (u a) (v a) := by
  simp only [sum_inner, real_inner_smul_left, b.orthonormal.inner_right_fintype]
  simp only [Real.inner_apply]
end Coordinates

section Processes
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Actual vector stochastic integral reconstructed from an orthonormal basis;
each coordinate is the previously constructed multi-channel Itô integral. -/
def vectorProcess (T : ℝ≥0) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (t : ℝ≥0) (ω : Ω) : E :=
  ∑ a, sumProcess hW hWm T (fun i => coordinate b a (φ i)) t ω • b a

theorem vectorProcess_martingale (T : ℝ≥0)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    Martingale (vectorProcess b hW hWm T φ) 𝓕 μ := by
  apply martingale_sum
  intro a
  exact martingale_map _ (sumProcess_martingale hW hWm T (fun i => coordinate b a (φ i)))
    (ContinuousLinearMap.toSpanSingleton ℝ (b a))

omit [CompleteSpace E] in
theorem vectorProcess_memLp (T t : ℝ≥0)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    MemLp (vectorProcess b hW hWm T φ t) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun a _ =>
    (ContinuousLinearMap.toSpanSingleton ℝ (b a)).comp_memLp'
      (sumProcess_memLp hW hWm T t (fun i => coordinate b a (φ i))))

omit [CompleteSpace E] in
/-- Genuine vector terminal Itô covariance; finite orthonormal reconstruction
and Parseval reduce it to the independently proved scalar channel isometries. -/
theorem vectorProcess_terminal_inner
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (∫ ω, inner ℝ (vectorProcess b hW hWm T φ T ω) (vectorProcess b hW hWm T ψ T ω) ∂μ) =
      ∑ i, inner ℝ (φ i) (ψ i) := by
  simp only [vectorProcess, inner_reconstruct]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    DriftMartingaleDuality.integrable_inner_of_memLp
      (sumProcess_memLp hW hWm T T (fun i => coordinate b a (φ i)))
      (sumProcess_memLp hW hWm T T (fun i => coordinate b a (ψ i))))]
  simp_rw [sumProcess_terminal_inner hW hWm hpair hchannels]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => coordinate_inner_sum b (φ i) (ψ i))

omit [Fintype κ] [Fintype ι] [CompleteSpace E] in
/-- Vector predictable L² covariance in the manuscript's actual real clock. -/
theorem predictable_inner_real_vector (T : ℝ≥0)
    (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    inner ℝ f g = ∫ s in Ioc 0 (T : ℝ),
      ∫ ω, inner ℝ (f (s.toNNReal,ω)) (g (s.toNNReal,ω)) ∂μ := by
  have hi : Integrable (fun z => inner ℝ (f z) (g z))
      ((CommonItoCLM.timeMeasure_T T).prod μ) :=
    integrable_of_integrable_trim 𝓕.predictable_le_prod (L2.integrable_inner f g)
  rw [L2.inner_def]
  change (∫ z, inner ℝ (f z) (g z) ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod)) = _
  rw [← integral_trim (μ := (CommonItoCLM.timeMeasure_T T).prod μ) 𝓕.predictable_le_prod
    ((Lp.stronglyMeasurable f).inner (Lp.stronglyMeasurable g)), integral_prod _ hi]
  exact (RealTimeBridge.integral_real_extension T
    (fun s => ∫ ω, inner ℝ (f (s,ω)) (g (s,ω)) ∂μ)).symm

/-- Actual vector expected-product identity for finite Brownian channels and
arbitrary vector common-predictable H² drifts/diffusions. No covariance identity
or stochastic differential equation is assumed as a premise. -/
theorem expected_vector_ito_product
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (∫ ω, inner ℝ
      ((∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) + vectorProcess b hW hWm T φ T ω)
      ((∫ s in Ioc 0 (T : ℝ), g (s.toNNReal,ω)) + vectorProcess b hW hWm T ψ T ω) ∂μ) =
      (∑ i, ∫ s in Ioc 0 (T : ℝ),
        ∫ ω, inner ℝ (φ i (s.toNNReal,ω)) (ψ i (s.toNNReal,ω)) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
        ((∫ t in Ioc 0 s, g (t.toNNReal,ω)) + vectorProcess b hW hWm T ψ s.toNNReal ω) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
        ((∫ t in Ioc 0 s, f (t.toNNReal,ω)) + vectorProcess b hW hWm T φ s.toNNReal ω)
          (g (s.toNNReal,ω)) ∂μ) := by
  have h := RealTimeBridge.predictable_expected_product T μ 𝓕
    (vectorProcess b hW hWm T φ) (vectorProcess b hW hWm T ψ)
    (vectorProcess_martingale b hW hWm T φ) (vectorProcess_martingale b hW hWm T ψ)
    (vectorProcess_memLp b hW hWm T T φ) (vectorProcess_memLp b hW hWm T T ψ) f g
  refine h.trans ?_
  rw [vectorProcess_terminal_inner b hW hWm hpair hchannels]
  simp_rw [predictable_inner_real_vector]
  rfl

end Processes
end LinearStochastic.VectorItoProduct
