import LinearStochastic.InitialExpectedProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The genuine SDE/BSDE pairing identity for actual integral solutions.
An integral solution specifies actual Lebesgue/constructed Itô decompositions,
including a separate terminal random variable. Existence of such solutions
for arbitrary terminal data is not assumed proved by this conditional identity. -/
noncomputable section
namespace LinearStochastic.LinearDuality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct

section Algebra
variable {Λ E U : Type*} {mΛ : MeasurableSpace Λ} {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- The actual pointwise coefficient map and its actual Hilbert adjoint retain
the adjoint pairing on genuine L² random variables. -/
theorem compLp_adjoint (L : U →L[ℝ] E) (u : Lp U 2 ν) (y : Lp E 2 ν) :
    inner ℝ (L.compLp u) y = inner ℝ u (L.adjoint.compLp y) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLp u, L.adjoint.coeFn_compLp y] with z hu hy
  rw [hu,hy]
  exact (L.adjoint_inner_right (u z) (y z)).symm

/-- Literal forward/backward coefficient cancellation, including every
controlled diffusion term. No desired duality conclusion is a premise. -/
theorem coefficient_cancellation {ι : Type*} [Fintype ι]
    (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (X Y : Lp E 2 ν) (u : Lp U 2 ν) (Z : ι → Lp E 2 ν) :
    (∑ i, inner ℝ ((C i).compLp X + (D i).compLp u) (Z i)) +
      inner ℝ (A.compLp X + B.compLp u) Y +
      inner ℝ X (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) =
      inner ℝ u (B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i)) := by
  simp only [inner_add_left,inner_add_right,inner_neg_right,inner_sum,
    Finset.sum_add_distrib,compLp_adjoint]
  ring
/-- The observation L² class is represented by the literal adjoint expression. -/
theorem observation_ae {ι : Type*} [Fintype ι]
    (B : U →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (Y : Lp E 2 ν) (Z : ι → Lp E 2 ν) :
    (B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) : Lp U 2 ν) =ᵐ[ν]
      fun z => B.adjoint (Y z) + ∑ i, (D i).adjoint (Z i z) := by
  have hz : ∀ᵐ z ∂ν, ∀ i, ((D i).adjoint.compLp (Z i)) z = (D i).adjoint (Z i z) := by
    rw [ae_all_iff]
    exact fun i => (D i).adjoint.coeFn_compLp (Z i)
  filter_upwards [Lp.coeFn_add (B.adjoint.compLp Y) (∑ i, (D i).adjoint.compLp (Z i)),
    B.adjoint.coeFn_compLp Y, Lp.coeFn_fun_finsetSum Finset.univ (fun i => (D i).adjoint.compLp (Z i)),hz]
    with z ha hb hs hz
  simp only [Pi.add_apply] at ha
  rw [ha,hb,hs]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hz i)
end Algebra

section Pairing
variable {Ω U : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [CompleteSpace U] in
/-- The L² inner product is exactly the manuscript's expectation of the actual
Lebesgue time integral. Integrability and Fubini follow from the L² hypotheses. -/
theorem predictable_inner_expectation (T : ℝ≥0)
    (u v : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    inner ℝ u v = ∫ ω, (∫ s in Ioc 0 (T : ℝ),
      inner ℝ (u (s.toNNReal,ω)) (v (s.toNNReal,ω))) ∂μ := by
  rw [VectorItoProduct.predictable_inner_real_vector]
  have hi := DriftMartingaleDuality.integrable_inner_of_memLp
    (RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 u)
    (RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 v)
  exact integral_integral_swap hi
end Pairing

section Processes
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Actual process determined by its initial value, Lebesgue drift and the
constructed multi-channel vector Itô integral, in the manuscript's real clock. -/
def integralState (T : ℝ≥0) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) (s : ℝ) (ω : Ω) : E :=
  (∫ t in Ioc 0 s, f (t.toNNReal,ω)) + (ξ ω + vectorProcess b hW hWm T φ s.toNNReal ω)

/-- The terminal value is specified separately because a spacetime L² class
does not determine its value at the measure-zero terminal time. -/
structure IntegralSolution (T : ℝ≥0) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E) : Prop where
  spacetime : (fun z : ℝ × Ω => X (z.1.toNNReal,z.2)) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod μ]
    Function.uncurry (integralState b hW hWm T ξ f φ)
  terminal : XT =ᵐ[μ] integralState b hW hWm T ξ f φ (T : ℝ)

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
    (hX : IntegralSolution b hW hWm T ξ f φ X XT)
    (hY : IntegralSolution b hW hWm T η g ψ Y YT) :
    (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = (∫ ω, inner ℝ (ξ ω) (η ω) ∂μ) +
      (∑ i, inner ℝ (φ i) (ψ i)) + inner ℝ f Y + inner ℝ X g := by
  have h := InitialExpectedProduct.expected_vector_ito_product_initial b hW hWm
    hpair hchannels T ξ η hξ hη hξ0 hη0 f g φ ψ
  have hfY : (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
      (integralState b hW hWm T η g ψ s ω) ∂μ) = inner ℝ f Y := by
    rw [predictable_inner_real_vector]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hY.spacetime] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    simp only [Function.uncurry] at hω
    rw [← hω]
  have hXg : (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
      (integralState b hW hWm T ξ f φ s ω) (g (s.toNNReal,ω)) ∂μ) = inner ℝ X g := by
    rw [predictable_inner_real_vector]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hX.spacetime] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with ω hω
    simp only [Function.uncurry] at hω
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
    (hX : IntegralSolution b hW hWm T ξ (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT)
    (hY : IntegralSolution b hW hWm T η
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
    (hX : IntegralSolution b hW hWm T ξ (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT)
    (hY : IntegralSolution b hW hWm T η
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
#print axioms forward_backward_duality
end LinearStochastic.LinearDuality
