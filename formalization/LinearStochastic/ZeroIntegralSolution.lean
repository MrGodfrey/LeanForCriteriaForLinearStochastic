import LinearStochastic.LinearDuality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
namespace LinearStochastic.ZeroIntegralSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators Topology
open CommonItoMultichannel VectorItoProduct LinearDuality

section Drift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Genuine finite-variation uniqueness: an integrable real-time drift whose
primitive vanishes almost everywhere has zero density almost everywhere. -/
theorem drift_zero_of_primitive_zero (T : ℝ) (hT : 0 < T) (f : ℝ → E)
    (hf : IntegrableOn f (Ioc 0 T))
    (hz : (fun t => ∫ s in Ioc 0 t, f s) =ᵐ[volume.restrict (Ioc 0 T)] 0) :
    f =ᵐ[volume.restrict (Ioc 0 T)] 0 := by
  have hi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hf
  have hc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using
      intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
  have he : (fun t => ∫ s in (0 : ℝ)..t, f s) =ᵐ[volume.restrict (Ioc 0 T)] 0 := by
    filter_upwards [hz,ae_restrict_mem measurableSet_Ioc] with t ht htm
    rw [intervalIntegral.integral_of_le htm.1.le]
    exact ht
  have hall := Measure.eqOn_Ioc_of_ae_eq volume he (hc.mono Ioc_subset_Icc_self) continuousOn_const
  change ∀ᵐ t ∂volume.restrict (Ioc 0 T), f t = 0
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hi.ae_hasDerivAt_integral,show ∀ᵐ t : ℝ ∂volume, t ≠ T by simp [ae_iff]] with t ht hne
  intro htm
  have htu : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT.le] using Ioc_subset_Icc_self htm
  have hd := ht htu 0 left_mem_uIcc
  have hev : (fun t => ∫ s in (0 : ℝ)..t, f s) =ᶠ[nhds t] fun _ => (0 : E) := by
    filter_upwards [Ioo_mem_nhds htm.1 (lt_of_le_of_ne htm.2 hne)] with x hx
    exact hall ⟨hx.1,hx.2.le⟩
  have hd0 : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, f s) 0 t :=
    (hasDerivAt_const t (0 : E)).congr_of_eventuallyEq hev
  exact hd.unique hd0
end Drift

section Stochastic
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Diffusion uniqueness for an actual zero integral solution. The Itô energy
identity is derived from the constructed Brownian integral; neither uniqueness
nor zero quadratic variation is supplied as a premise. -/
theorem diffusion_zero_of_zero_solution
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hzero : IntegralSolution b hW hWm T 0 f φ 0 0) : ∀ i, φ i = 0 := by
  have h := integral_solution_product b hW hWm hpair hchannels T 0 0
    (MemLp.zero) (MemLp.zero) stronglyMeasurable_zero stronglyMeasurable_zero
    f f 0 0 φ φ 0 0 hzero hzero
  simp only [Pi.zero_apply,inner_zero_left,inner_zero_right,integral_zero,
    add_zero,zero_add,real_inner_self_eq_norm_sq] at h
  have hs : ∀ i, ‖φ i‖ ^ 2 = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖φ i‖)).mp h.symm
    exact fun i => hh i (Finset.mem_univ i)
  intro i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hs i))
end Stochastic

#print axioms drift_zero_of_primitive_zero
#print axioms diffusion_zero_of_zero_solution
end LinearStochastic.ZeroIntegralSolution
