import LinearStochastic.SwitchingTimeMesh
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! An actual deterministic measurable gain schedule with the manuscript's
half-open intervals. It is bounded on every compact prefix strictly before T. -/
noncomputable section
namespace LinearStochastic.SwitchingGain
open MeasureTheory Set Filter Topology
open scoped NNReal BigOperators
open SwitchingTimeMesh
variable {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

def gain (T : ℝ≥0) (K : ℕ → G) (t : ℝ≥0) : G :=
  ∑' j, (Ico (time T j) (time T (j+1))).indicator (fun _ => K j) t

theorem time_mono (T : ℝ≥0) (hT : 0 < T) {i j : ℕ} (hij : i ≤ j) : time T i ≤ time T j := by
  apply NNReal.coe_le_coe.mp
  rw [coe_time,coe_time]
  exact (Switching.switchTime_strictMono (show (0:ℝ)<T from hT)).monotone hij

/-- Every time strictly before the endpoint belongs to an actual mesh interval. -/
theorem covers (T t : ℝ≥0) (ht : t < T) :
    ∃ j : ℕ, t ∈ Ico (time T j) (time T (j+1)) := by
  have hT : 0 < T := lt_of_le_of_lt zero_le ht
  obtain ⟨N,hN⟩ := ((time_tendsto T).eventually (lt_mem_nhds ht)).exists
  have hex : ∃ j : ℕ, t < time T (j+1) :=
    ⟨N,hN.trans_le (time_mono T hT (Nat.le_succ N))⟩
  refine ⟨Nat.find hex,?_,Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · rw [hz,time_zero]
    exact zero_le
  · have he : Nat.find hex-1+1=Nat.find hex := by omega
    have hn := Nat.find_min hex (show Nat.find hex-1 < Nat.find hex by omega)
    rw [he] at hn
    exact le_of_not_gt hn

theorem measurable_gain (T : ℝ≥0) (K : ℕ → G) : Measurable (gain T K) :=
  Measurable.tsum (fun _ => measurable_const.indicator measurableSet_Ico)

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem gain_on (T : ℝ≥0) (hT : 0 < T) (K : ℕ → G) (j : ℕ) (t : ℝ≥0)
    (ht : t ∈ Ico (time T j) (time T (j+1))) : gain T K t = K j := by
  unfold gain
  rw [tsum_eq_single j,indicator_of_mem ht]
  intro k hkj
  apply indicator_of_notMem
  intro hk
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · exact (not_lt_of_ge ((time_mono T hT (Nat.succ_le_of_lt hlt)).trans ht.1)) hk.2
  · exact (not_lt_of_ge ((time_mono T hT (Nat.succ_le_of_lt hgt)).trans hk.1)) ht.2

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem gain_after (T : ℝ≥0) (K : ℕ → G) (t : ℝ≥0) (ht : T ≤ t) : gain T K t = 0 := by
  have hz (j : ℕ) : (Ico (time T j) (time T (j+1))).indicator (fun _ => K j) t = 0 := by
    apply indicator_of_notMem
    intro hj
    exact (not_lt_of_ge ((time_le T (j+1)).trans ht)) hj.2
  simp only [gain,hz,tsum_zero]

omit [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem prefix_bound (T : ℝ≥0) (K : ℕ → G) (s : ℝ≥0) (hs : s < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ≤ s → ‖gain T K t‖ ≤ M := by
  have hT : 0 < T := lt_of_le_of_lt zero_le hs
  obtain ⟨N,hN⟩ := ((time_tendsto T).eventually (lt_mem_nhds hs)).exists
  refine ⟨∑ j ∈ Finset.range N, ‖K j‖,Finset.sum_nonneg (fun _ _ => norm_nonneg _),?_⟩
  intro t ht
  have he : gain T K t = ∑ j ∈ Finset.range N,
      (Ico (time T j) (time T (j+1))).indicator (fun _ => K j) t := by
    apply tsum_eq_sum
    intro j hj
    apply indicator_of_notMem
    intro hjt
    have hjN : N ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
    exact (not_lt_of_ge (hjt.1.trans ht)) (hN.trans_le (time_mono T hT hjN))
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : t ∈ Ico (time T j) (time T (j+1))
  · rw [indicator_of_mem hj]
  · rw [indicator_of_notMem hj,norm_zero]
    exact norm_nonneg _

end LinearStochastic.SwitchingGain
