module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Exponential decay follows from a genuine integral energy identity and a
pointwise dissipative generator bound. This deterministic lemma keeps both
inputs explicit; stochastic applications must prove them from the real SDE. -/
noncomputable section
namespace LinearStochastic.IntegralEnergyDecay
open Set MeasureTheory
open scoped Topology

theorem decay_of_integral_identity (e q : ℝ → ℝ) (ρ T : ℝ) (hT : 0 ≤ T)
    (hq : Continuous q)
    (he : ∀ t ∈ Icc 0 T, e t = e 0 + ∫ s in (0:ℝ)..t, q s)
    (hbound : ∀ t ∈ Ico 0 T, q t ≤ -ρ * e t) :
    e T ≤ e 0 * Real.exp (-ρ * T) := by
  let g : ℝ → ℝ := fun t => e 0 + ∫ s in (0:ℝ)..t, q s
  have hd (t : ℝ) : HasDerivAt g (q t) t := by
    simpa only [zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 t)
        hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt).const_add (e 0)
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hb : ∀ t ∈ Ico 0 T, q t ≤ (-ρ) * g t + 0 := by
    intro t ht
    have heq := he t ⟨ht.1,ht.2.le⟩
    change e t = g t at heq
    simpa only [add_zero,←heq] using hbound t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le hg.continuousOn
    (fun t _ r hr => (hd t).hasDerivWithinAt.liminf_right_slope_le hr)
    (show g 0 ≤ e 0 from by simp [g]) hb T ⟨hT,le_rfl⟩
  rw [gronwallBound_ε0,sub_zero] at h
  rw [he T ⟨hT,le_rfl⟩]
  exact h

end LinearStochastic.IntegralEnergyDecay
