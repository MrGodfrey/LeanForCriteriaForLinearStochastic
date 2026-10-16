import LinearStochastic.KnownTargetControl
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The final-interval exponential control acts pointwise on an earlier-known
random target and has the exact intended terminal convolution. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.KnownTargetGramian
open MeasureTheory Set
open scoped NNReal
open DeterministicGramianControl
variable {Ω E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] [FiniteDimensional ℝ E]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E) (a T : ℝ≥0) (ha : a < T)
  (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0)
  (ξ : Ω → E)

/-- The actual final-interval control, with no bound required uniformly as
its length shrinks to zero. -/
def steeringControl : ℝ≥0 → Ω → U :=
  KnownTargetControl.control a T (kernel A B ((T : ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) hK) ξ

/-- The end-interval endpoint integral equals the given random displacement
for every sample, before any passage to L² equivalence classes. -/
theorem terminal_last_interval (ω : Ω) :
    (∫ s in Ioc (a : ℝ) T, (NormedSpace.exp (((T : ℝ)-s) • A))
      (B (steeringControl A B a T ha hK ξ s.toNNReal ω))) = ξ ω := by
  let h : ℝ := (T : ℝ)-a
  have hh : 0 < h := sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)
  let K := kernel A B h hh hK
  let f := fun t : ℝ => (NormedSpace.exp ((h-t) • A)) (B (K t (ξ ω)))
  have he : (fun s : ℝ => (NormedSpace.exp (((T : ℝ)-s) • A))
      (B (steeringControl A B a T ha hK ξ s.toNNReal ω))) =ᵐ[volume.restrict (Ioc (a : ℝ) T)]
      fun s => f (s-a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 ≤ s := a.coe_nonneg.trans hs.1.le
    have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    have hmem : s.toNNReal ∈ Ioc a T := by
      constructor
      · apply NNReal.coe_lt_coe.mp
        simpa only [hcoe] using hs.1
      · apply NNReal.coe_le_coe.mp
        simpa only [hcoe] using hs.2
    simp only [steeringControl,KnownTargetControl.control,if_pos hmem,hcoe]
    change (NormedSpace.exp (((T : ℝ)-s) • A)) (B (K (s-a) (ξ ω))) =
      (NormedSpace.exp ((h-(s-a)) • A)) (B (K (s-a) (ξ ω)))
    congr 3
    dsimp [h]
    ring
  rw [integral_congr_ae he,←intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr ha.le),
    intervalIntegral.integral_comp_sub_right]
  simp only [sub_self]
  rw [intervalIntegral.integral_of_le hh.le,←integral_Icc_eq_integral_Ioc]
  exact DeterministicGramianControl.terminal_integral A B h hh hK (ξ ω)

section Admissibility
variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- The true Gramian control is progressive because the target is known at a. -/
theorem progressive (hξ : StronglyMeasurable[𝓕 a] ξ) :
    IsStronglyProgressive 𝓕 (steeringControl A B a T ha hK ξ) :=
  KnownTargetControl.progressive a T _ ξ (kernel_continuous A B _ _ hK) hξ

/-- Its expected energy is finite at each fixed positive remaining horizon. -/
theorem memLp (hξ : StronglyMeasurable[𝓕 a] ξ) (hξ2 : MemLp ξ 2 μ) :
    MemLp (Function.uncurry (steeringControl A B a T ha hK ξ)) 2 ((CommonItoCLM.timeMeasure_T T).prod μ) :=
  KnownTargetControl.memLp a T _ ξ (kernel_continuous A B _ _ hK) hξ hξ2
end Admissibility

end LinearStochastic.KnownTargetGramian
