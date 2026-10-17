module

public import LinearStochastic.LinearDuality

@[expose] public section

/-! Actual integral solutions with time-a.e. probability-a.e. sections.
This interface does not infer product-a.e. equality for the raw separately
chosen martingale representatives. The exact product and duality proofs need
only these sections and a separately specified terminal random variable. -/
noncomputable section
namespace LinearStochastic.SectionLinearDuality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality
section Processes
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual integral decomposition in iterated almost-everywhere sections,
with an independent terminal equality. -/
structure SectionIntegralSolution (T : ℝ≥0) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E) : Prop where
  sections : ∀ᵐ s ∂(volume.restrict (Ioc 0 (T : ℝ))),
    (fun ω => X (s.toNNReal,ω)) =ᵐ[μ] integralState b hW hWm T ξ f φ s
  terminal : XT =ᵐ[μ] integralState b hW hWm T ξ f φ (T : ℝ)

omit [CompleteSpace E] in
/-- The older, stronger spacetime interface supplies the required sections
by the forward direction of Fubini. No converse is asserted. -/
theorem IntegralSolution.toSections (T : ℝ≥0) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E)
    (h : LinearDuality.IntegralSolution b hW hWm T ξ f φ X XT) :
    SectionIntegralSolution b hW hWm T ξ f φ X XT :=
  ⟨Measure.ae_ae_of_ae_prod h.spacetime,h.terminal⟩

/-- Product rule for actual integral solutions, with every drift pairing
identified in the original predictable L² domain. -/
theorem integral_solution_product
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (ξ η : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : StronglyMeasurable[𝓕 0] ξ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (f g X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT YT : Ω → E)
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hY : SectionIntegralSolution b hW hWm T η g ψ Y YT) :
    (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) +
      (∑ i, inner ℝ (φ i) (ψ i)) + inner ℝ f Y + inner ℝ X g := by
  have h := InitialExpectedProduct.expected_vector_ito_product_initial b hW hWm
    hpair hchannels T ξ η hξ hη hξ0 hη0 f g φ ψ
  have hfY : (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
      (integralState b hW hWm T η g ψ s ω) ∂μ) = inner ℝ f Y := by
    rw [predictable_inner_real_vector]
    apply integral_congr_ae
    filter_upwards [hY.sections] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    rw [← hω]
  have hXg : (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
      (integralState b hW hWm T ξ f φ s ω) (g (s.toNNReal,ω)) ∂μ) = inner ℝ X g := by
    rw [predictable_inner_real_vector]
    apply integral_congr_ae
    filter_upwards [hX.sections] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    rw [← hω]
  have hterm : (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) =
      ∫ ω, inner ℝ (integralState b hW hWm T ξ f φ (T : ℝ) ω)
        (integralState b hW hWm T η g ψ (T : ℝ) ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX.terminal,hY.terminal] with ω hx hy
    rw [hx,hy]
  rw [hterm]
  simp only [integralState,Real.toNNReal_coe] at *
  rw [h, hfY,hXg]
  simp_rw [← predictable_inner_real_vector]

/-- The actual forward controlled / backward adjoint pairing identity. The
hypotheses are integral-solution decompositions for the original linear drift
and diffusion coefficients; the output is the control/observation pairing. -/
theorem forward_backward_duality
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ η XT YT : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : StronglyMeasurable[𝓕 0] ξ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT)
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT) :
    (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) +
      inner ℝ u (B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i)) := by
  have h := integral_solution_product b hW hWm hpair hchannels T ξ η hξ hη hξ0 hη0
    (A.compLp X + B.compLp u) (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i)))
    X Y (fun i => (C i).compLp X + (D i).compLp u) Z XT YT hX hY
  have hc := coefficient_cancellation A B C D X Y u Z
  linarith

/-- The same genuine duality identity, written with the actual pointwise
adjoint observation and the expectation outside the time integral. -/
theorem forward_backward_duality_real
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ η XT YT : Ω → E)
    (hξ : MemLp ξ 2 μ) (hη : MemLp η 2 μ)
    (hξ0 : StronglyMeasurable[𝓕 0] ξ) (hη0 : StronglyMeasurable[𝓕 0] η)
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT)
    (hY : SectionIntegralSolution b hW hWm T η
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT) :
    (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) +
      (∫ ω, (∫ s in Ioc 0 (T : ℝ), inner ℝ (u (s.toNNReal,ω))
        (B.adjoint (Y (s.toNNReal,ω)) + ∑ i, (D i).adjoint (Z i (s.toNNReal,ω)))) ∂μ) := by
  rw [forward_backward_duality b hW hWm hpair hchannels T A B C D ξ η XT YT
    hξ hη hξ0 hη0 X Y u Z hX hY, predictable_inner_expectation]
  congr 1
  have hobs := observation_ae B D Y Z
  have hamb := ae_of_ae_trim 𝓕.predictable_le_prod hobs
  have hreal := ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hamb
  have hswap := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hreal)
  apply integral_congr_ae
  filter_upwards [hswap] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  exact congrArg (inner ℝ (u (s.toNNReal,ω))) hs
end Processes
#print axioms forward_backward_duality_real
end LinearStochastic.SectionLinearDuality
