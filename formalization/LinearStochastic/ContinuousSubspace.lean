import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace LinearStochastic.ContinuousSubspace
open MeasureTheory Set

variable {E : Type*} [MetricSpace E]

/-- A continuous path lying in a nonempty closed set at almost every time
lies in it at every time, including both endpoints. -/
theorem continuous_mem_closed_of_ae (T : ℝ) (hT : 0 < T)
    (S : Set E) (hS : IsClosed S) (hne : S.Nonempty)
    (f : ℝ → E) (hc : ContinuousOn f (Icc 0 T))
    (hf : ∀ᵐ t ∂volume.restrict (Ioc 0 T), f t ∈ S) :
    ∀ t ∈ Icc 0 T, f t ∈ S := by
  have hz : (fun t => Metric.infDist (f t) S) =ᵐ[volume.restrict (Icc 0 T)] 0 := by
    rw [←Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := T))]
    filter_upwards [hf] with t ht
    exact Metric.infDist_zero_of_mem ht
  have hall := Measure.eqOn_Icc_of_ae_eq volume hT.ne hz
    ((Metric.continuous_infDist_pt S).comp_continuousOn hc) continuousOn_const
  intro t ht
  exact (hS.mem_iff_infDist_zero hne).mpr (hall ht)

/-- Fubini and continuity give one probability-one event on which the entire
path lies in the closed set. This includes the terminal time, despite its zero
time measure; the conclusion is not merely an a.e.-in-time statement. -/
theorem process_mem_closed_every_time {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (T : ℝ) (hT : 0 < T)
    (S : Set E) (hS : IsClosed S) (hne : S.Nonempty)
    (X : ℝ → Ω → E)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hX : ∀ᵐ z ∂(volume.restrict (Ioc 0 T)).prod μ, X z.1 z.2 ∈ S) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, X t ω ∈ S := by
  have hs : ∀ᵐ z ∂μ.prod (volume.restrict (Ioc 0 T)), X z.2 z.1 ∈ S :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae hX
  filter_upwards [hc,Measure.ae_ae_of_ae_prod hs] with ω hcω hω
  exact continuous_mem_closed_of_ae T hT S hS hne (fun t => X t ω) hcω hω

/-- The exact finite-dimensional subspace specialization used at each stage
of the paper's obstruction flag induction. -/
theorem process_mem_subspace_every_time {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (μ : Measure Ω) [SFinite μ] (T : ℝ) (hT : 0 < T)
    (V : Submodule ℝ F) (X : ℝ → Ω → F)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hX : ∀ᵐ z ∂(volume.restrict (Ioc 0 T)).prod μ, X z.1 z.2 ∈ V) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, X t ω ∈ V :=
  process_mem_closed_every_time μ T hT V V.closed_of_finiteDimensional ⟨0,V.zero_mem⟩ X hc hX

#print axioms process_mem_subspace_every_time
end LinearStochastic.ContinuousSubspace
