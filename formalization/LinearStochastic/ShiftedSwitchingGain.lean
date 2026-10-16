import LinearStochastic.SwitchingGain
import LinearStochastic.SwitchingFeedbackIdentity

/-! The actual long-horizon feedback schedule: zero on the waiting interval,
then the same deterministic short-horizon gain translated to the original clock. -/
noncomputable section
namespace LinearStochastic.ShiftedSwitchingGain
open MeasureTheory Set
open scoped NNReal
variable {G : Type*} [NormedAddCommGroup G]

def gain (a δ : ℝ≥0) (K : ℕ → G) (t : ℝ≥0) : G :=
  if a ≤ t then SwitchingGain.gain δ K (t-a) else 0

theorem gain_before (a δ : ℝ≥0) (K : ℕ → G) (t : ℝ≥0) (ht : t < a) : gain a δ K t = 0 := by
  simp only [gain,if_neg (not_le.mpr ht)]

theorem gain_shift (a δ : ℝ≥0) (K : ℕ → G) (s : ℝ≥0) :
    gain a δ K (a+s) = SwitchingGain.gain δ K s := by
  simp only [gain,le_add_right le_rfl,if_true,add_tsub_cancel_left]

theorem gain_on (a δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ → G) (j : ℕ) (t : ℝ≥0)
    (ht : t ∈ Ico (a+SwitchingTimeMesh.time δ j) (a+SwitchingTimeMesh.time δ (j+1))) :
    gain a δ K t = K j := by
  have ha : a ≤ t := (le_add_right le_rfl).trans ht.1
  have hj : t-a ∈ Ico (SwitchingTimeMesh.time δ j) (SwitchingTimeMesh.time δ (j+1)) := by
    constructor
    · exact (le_tsub_iff_right ha).mpr (by simpa only [add_comm] using ht.1)
    · exact (tsub_lt_iff_right ha).mpr (by simpa only [add_comm] using ht.2)
  rw [gain,if_pos ha]
  exact SwitchingGain.gain_on δ hδ K j (t-a) hj

theorem prefix_bound (a δ : ℝ≥0) (K : ℕ → G) (s : ℝ≥0) (hs : s < a+δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ≤ s → ‖gain a δ K t‖ ≤ M := by
  by_cases ha : a ≤ s
  · have hsd : s-a < δ := (tsub_lt_iff_right ha).mpr (by simpa only [add_comm] using hs)
    obtain ⟨M,hM,hbound⟩ := SwitchingGain.prefix_bound δ K (s-a) hsd
    refine ⟨M,hM,?_⟩
    intro t ht
    by_cases hat : a ≤ t
    · rw [gain,if_pos hat]
      exact hbound (t-a) (tsub_le_tsub_right ht a)
    · rw [gain,if_neg hat,norm_zero]
      exact hM
  · refine ⟨0,le_rfl,?_⟩
    intro t ht
    rw [gain_before a δ K t (ht.trans_lt (lt_of_not_ge ha)),norm_zero]

variable [CompleteSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

theorem measurable_gain (a δ : ℝ≥0) (K : ℕ → G) : Measurable (gain a δ K) :=
  Measurable.ite measurableSet_Ici
    ((SwitchingGain.measurable_gain δ K).comp (by fun_prop)) measurable_const

end LinearStochastic.ShiftedSwitchingGain
