import LinearStochastic.SwitchingRates

/-! The actual nonnegative deterministic mesh used to restart the feedback SDE. -/
noncomputable section
namespace LinearStochastic.SwitchingTimeMesh
open Filter Topology
open scoped NNReal

def time (T : ℝ≥0) (j : ℕ) : ℝ≥0 := T*(1-(1/2:ℝ≥0)^j)
def duration (T : ℝ≥0) (j : ℕ) : ℝ≥0 := T*(1/2:ℝ≥0)^(j+1)

theorem coe_time (T : ℝ≥0) (j : ℕ) : (time T j : ℝ) = Switching.switchTime (T:ℝ) j := by
  have hp : (1/2:ℝ≥0)^j ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  simp only [time,Switching.switchTime,NNReal.coe_mul,NNReal.coe_sub hp,NNReal.coe_one,
    NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat]

theorem coe_duration (T : ℝ≥0) (j : ℕ) : (duration T j : ℝ) = SwitchingRates.length (T:ℝ) j := by
  simp only [duration,SwitchingRates.length,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_div,
    NNReal.coe_one,NNReal.coe_ofNat]

theorem time_zero (T : ℝ≥0) : time T 0 = 0 := by simp [time]

theorem next_time (T : ℝ≥0) (j : ℕ) : time T j+duration T j=time T (j+1) := by
  apply NNReal.coe_injective
  rw [NNReal.coe_add,coe_time,coe_time,coe_duration]
  have h := Switching.switchTime_length (T:ℝ) j
  dsimp only [SwitchingRates.length]
  linarith

theorem time_le (T : ℝ≥0) (j : ℕ) : time T j ≤ T := by
  dsimp [time]
  exact (mul_le_mul_of_nonneg_left tsub_le_self (show (0:ℝ≥0) ≤ T from zero_le)).trans_eq (mul_one T)

theorem time_lt (T : ℝ≥0) (hT : 0 < T) (j : ℕ) : time T j < T := by
  have hp : 0 < (1/2:ℝ≥0)^j := pow_pos (by norm_num) j
  have hs : 1-(1/2:ℝ≥0)^j < 1 := tsub_lt_self zero_lt_one hp
  exact (mul_lt_mul_of_pos_left hs hT).trans_eq (mul_one T)

theorem duration_pos (T : ℝ≥0) (hT : 0 < T) (j : ℕ) : 0 < duration T j :=
  mul_pos hT (pow_pos (by norm_num) _)

theorem time_tendsto (T : ℝ≥0) : Tendsto (time T) atTop (𝓝 T) := by
  rw [← NNReal.tendsto_coe]
  simpa only [Function.comp_def,coe_time] using Switching.switchTime_tendsto (T:ℝ)

end LinearStochastic.SwitchingTimeMesh
