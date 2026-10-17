module

public import LinearStochastic.VectorItoProduct

@[expose] public section

/-! Expected products with genuine nonzero F₀-measurable L² initial values.
The zero-initial covariance cross terms are derived from actual martingale
conditional expectations; the Itô specialization uses the constructed vector
integral and its genuine covariance theorem. -/
noncomputable section
namespace LinearStochastic.InitialExpectedProduct
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {𝓕 : Filtration ℝ≥0 mΩ}

section Finite
variable [IsFiniteMeasure μ]

/-- Actual conditional expectation removes the initial/terminal martingale
cross term when the martingale starts from zero. -/
theorem initial_martingale_pairing_zero (ξ : Ω → E)
    (hξ : MemLp ξ 2 μ) (hξ0 : AEStronglyMeasurable[𝓕 0] ξ μ)
    (M : ℝ≥0 → Ω → E) (hM : Martingale M 𝓕 μ)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 μ) (hM0 : M 0 =ᵐ[μ] 0) :
    (∫ ω, inner ℝ (ξ ω) (M T ω) ∂μ) = 0 := by
  have hint := DriftMartingaleDuality.integrable_inner_of_memLp hξ hMT
  have hpull := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ)
    hξ0 hint (hMT.integrable one_le_two)
  calc
    _ = ∫ ω, μ[fun ω => inner ℝ (ξ ω) (M T ω) | 𝓕 0] ω ∂μ :=
      (integral_condExp (𝓕.le 0)).symm
    _ = ∫ ω, inner ℝ (ξ ω) (μ[M T | 𝓕 0] ω) ∂μ := integral_congr_ae hpull
    _ = ∫ ω, inner ℝ (ξ ω) (0 : E) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hM.2 0 T (by positivity), hM0] with ω hm h0
      rw [hm, h0]
      rfl
    _ = 0 := by simp

/-- The initial and terminal martingale covariances split into their two
actual terms; both mixed terms are proved zero from F₀ measurability. -/
theorem shifted_covariance (ξ η : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : AEStronglyMeasurable[𝓕 0] ξ μ) (hη0 : AEStronglyMeasurable[𝓕 0] η μ)
    (M N : ℝ≥0 → Ω → E) (hM : Martingale M 𝓕 μ) (hN : Martingale N 𝓕 μ)
    (T : ℝ≥0) (hMT : MemLp (M T) 2 μ) (hNT : MemLp (N T) 2 μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hN0 : N 0 =ᵐ[μ] 0) :
    (∫ ω, inner ℝ (ξ ω + M T ω) (η ω + N T ω) ∂μ) =
      (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) + (∫ ω, inner ℝ (M T ω) (N T ω) ∂μ) := by
  have h11 := DriftMartingaleDuality.integrable_inner_of_memLp hξ hη
  have h12 := DriftMartingaleDuality.integrable_inner_of_memLp hξ hNT
  have h21 := DriftMartingaleDuality.integrable_inner_of_memLp hMT hη
  have h22 := DriftMartingaleDuality.integrable_inner_of_memLp hMT hNT
  have hz12 := initial_martingale_pairing_zero ξ hξ hξ0 N hN T hNT hN0
  have hz21 : (∫ ω, inner ℝ (M T ω) (η ω) ∂μ) = 0 := by
    simpa only [real_inner_comm] using initial_martingale_pairing_zero η hη hη0 M hM T hMT hM0
  simp_rw [inner_add_left, inner_add_right]
  have hsum := integral_add (h11.add h12) (h21.add h22)
  have hfirst := integral_add h11 h12
  have hsecond := integral_add h21 h22
  simp only [Pi.add_apply] at hsum hfirst hsecond
  rw [hsum, hfirst, hsecond, hz12, hz21, add_zero, zero_add]

/-- The full genuine expected product, including random initial values, for
actual Lebesgue drifts and genuine zero-initial L² martingales. -/
theorem expected_product_initial (T : ℝ≥0) (ξ η : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : StronglyMeasurable[𝓕 0] ξ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (M N : ℝ≥0 → Ω → E) (hM : Martingale M 𝓕 μ) (hN : Martingale N 𝓕 μ)
    (hMT : MemLp (M T) 2 μ) (hNT : MemLp (N T) 2 μ)
    (hM0 : M 0 =ᵐ[μ] 0) (hN0 : N 0 =ᵐ[μ] 0)
    (f g : Lp E 2 (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod)) :
    (∫ ω, inner ℝ
      ((∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) + (ξ ω + M T ω))
      ((∫ s in Ioc 0 (T : ℝ), g (s.toNNReal,ω)) + (η ω + N T ω)) ∂μ) =
      (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) + (∫ ω, inner ℝ (M T ω) (N T ω) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
        ((∫ t in Ioc 0 s, g (t.toNNReal,ω)) + (η ω + N s.toNNReal ω)) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
        ((∫ t in Ioc 0 s, f (t.toNNReal,ω)) + (ξ ω + M s.toNNReal ω))
          (g (s.toNNReal,ω)) ∂μ) := by
  have hξM : Martingale (fun t ω => ξ ω + M t ω) 𝓕 μ :=
    (martingale_const_fun 𝓕 μ hξ0 (hξ.integrable one_le_two)).add hM
  have hηN : Martingale (fun t ω => η ω + N t ω) 𝓕 μ :=
    (martingale_const_fun 𝓕 μ hη0 (hη.integrable one_le_two)).add hN
  have h := RealTimeBridge.predictable_expected_product T μ 𝓕
    (fun t ω => ξ ω + M t ω) (fun t ω => η ω + N t ω)
    hξM hηN (hξ.add hMT) (hη.add hNT) f g
  rw [shifted_covariance ξ η hξ hη hξ0.aestronglyMeasurable hη0.aestronglyMeasurable
    M N hM hN T hMT hNT hM0 hN0] at h
  exact h
end Finite

section Ito
open CommonItoMultichannel ItoExpectedProduct VectorItoProduct
variable [IsProbabilityMeasure μ] {κ ι : Type*} [Fintype κ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype κ] in
/-- The constructed sum of actual scalar integrals starts from zero a.s. -/
theorem sumProcess_zero_ae (T : ℝ≥0) (φ : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    sumProcess hW hWm T φ 0 =ᵐ[μ] 0 := by
  have hz : ∀ᵐ ω ∂μ, ∀ i, CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i) (φ i) 0 ω = 0 := by
    rw [ae_all_iff]
    exact fun i => CommonItoMartingaleVersion.integralProcess_zero_ae (hW i) T (hWm i) (φ i)
  filter_upwards [hz] with ω hω
  simp only [sumProcess, hω, Finset.sum_const_zero, Pi.zero_apply]

omit [CompleteSpace E] in
/-- Finite orthonormal reconstruction retains the genuine zero initial value. -/
theorem vectorProcess_zero_ae (T : ℝ≥0) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm T φ 0 =ᵐ[μ] 0 := by
  have hz : ∀ᵐ ω ∂μ, ∀ a, sumProcess hW hWm T (fun i => coordinate b a (φ i)) 0 ω = 0 := by
    rw [ae_all_iff]
    exact fun a => sumProcess_zero_ae hW hWm T (fun i => coordinate b a (φ i))
  filter_upwards [hz] with ω hω
  simp only [vectorProcess, hω, zero_smul, Finset.sum_const_zero, Pi.zero_apply]

/-- The actual vector multi-Brownian expected product with arbitrary F₀
square-integrable initial values. All martingale and covariance properties
are derived for the constructed integrals, not supplied as hypotheses. -/
theorem expected_vector_ito_product_initial
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (ξ η : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : StronglyMeasurable[𝓕 0] ξ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (∫ ω, inner ℝ
      ((∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) + (ξ ω + vectorProcess b hW hWm T φ T ω))
      ((∫ s in Ioc 0 (T : ℝ), g (s.toNNReal,ω)) + (η ω + vectorProcess b hW hWm T ψ T ω)) ∂μ) =
      (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) +
      (∑ i, ∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (φ i (s.toNNReal,ω)) (ψ i (s.toNNReal,ω)) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
        ((∫ t in Ioc 0 s, g (t.toNNReal,ω)) + (η ω + vectorProcess b hW hWm T ψ s.toNNReal ω)) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
        ((∫ t in Ioc 0 s, f (t.toNNReal,ω)) + (ξ ω + vectorProcess b hW hWm T φ s.toNNReal ω))
          (g (s.toNNReal,ω)) ∂μ) := by
  have h := expected_product_initial T ξ η hξ hη hξ0 hη0
    (vectorProcess b hW hWm T φ) (vectorProcess b hW hWm T ψ)
    (vectorProcess_martingale b hW hWm T φ) (vectorProcess_martingale b hW hWm T ψ)
    (vectorProcess_memLp b hW hWm T T φ) (vectorProcess_memLp b hW hWm T T ψ)
    (vectorProcess_zero_ae b hW hWm T φ) (vectorProcess_zero_ae b hW hWm T ψ) f g
  rw [vectorProcess_terminal_inner b hW hWm hpair hchannels] at h
  simp_rw [predictable_inner_real_vector] at h
  exact h
end Ito

#print axioms expected_vector_ito_product_initial
end LinearStochastic.InitialExpectedProduct
