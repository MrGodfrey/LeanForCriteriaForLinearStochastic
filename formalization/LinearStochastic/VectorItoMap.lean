module

public import LinearStochastic.VectorItoNaturality

@[expose] public section

/-! The actual vector Itô integral is natural also between different finite
state spaces and independently chosen orthonormal bases. -/
noncomputable section
namespace LinearStochastic.VectorItoMap
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LpFiniteTensor VectorItoNaturality

section Tensor
variable {Ω Λ E F κ τ : Type*} [mΩ : MeasurableSpace Ω] [mΛ : MeasurableSpace Λ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fintype κ] [Fintype τ]

theorem comp_injection (μ : Measure Ω) (L : E →L[ℝ] F) (v : E) (f : Lp ℝ 2 μ) :
    L.compLpₗ 2 μ (injection μ v f) = injection μ (L v) f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (injection μ v f),injection_ae μ v f,
    injection_ae μ (L v) f] with ω hL hv hLv
  change L.compLp (injection μ v f) ω = injection μ (L v) f ω
  rw [hL,hv,hLv,map_smul]

theorem lift_map (ν : Measure Λ) (μ : Measure Ω)
    (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ F)
    (S : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ) (L : E →L[ℝ] F) (f : Lp E 2 ν) :
    lift ν μ c S (L.compLpₗ 2 ν f) = L.compLpₗ 2 μ (lift ν μ b S f) := by
  rw [(lp_expansion ν b f).symm]
  simp only [map_sum,comp_injection,lift_injection]
end Tensor

section Ito
variable {Ω E F κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ F)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem vectorLp_map (T t : ℝ≥0) (L : E →L[ℝ] F)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorLp c hW hWm T t (fun i => L.compLp (φ i)) =
      L.compLp (vectorLp b hW hWm T t φ) := by
  change (∑ i, lift (mΛ := 𝓕.predictable) _ _ c _ (L.compLpₗ 2 _ (φ i))) =
    L.compLpₗ 2 μ (∑ i, lift (mΛ := 𝓕.predictable) _ _ b _ (φ i))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => lift_map (mΛ := 𝓕.predictable) _ _ b c _ L (φ i))

/-- No isometry is required of the state map; in particular this applies to
the actual inclusion of an invariant subspace into the original state space. -/
theorem vectorProcess_map_ae (T t : ℝ≥0) (L : E →L[ℝ] F)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess c hW hWm T (fun i => L.compLp (φ i)) t =ᵐ[μ]
      fun ω => L (vectorProcess b hW hWm T φ t ω) := by
  have hl := vectorProcess_ae_vectorLp c hW hWm T t (fun i => L.compLp (φ i))
  rw [vectorLp_map b c] at hl
  filter_upwards [hl,L.coeFn_compLp (vectorLp b hW hWm T t φ),
    vectorProcess_ae_vectorLp b hW hWm T t φ] with ω hl hL hr
  rw [hl,hL,hr]
end Ito

#print axioms vectorProcess_map_ae
end LinearStochastic.VectorItoMap
