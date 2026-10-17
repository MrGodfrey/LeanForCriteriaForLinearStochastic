module

public import LinearStochastic.Switching

@[expose] public section

/-! The manuscript's concrete dyadic time mesh and quadratic-rate schedule
satisfy the scalar bounds needed for the actual switching construction. -/
noncomputable section
namespace LinearStochastic.SwitchingRates
open Switching

def rate (L T : ℝ) (j : ℕ) : ℝ := L * ((2:ℝ)^j / T)^2

def length (T : ℝ) (j : ℕ) : ℝ := T * (1/2:ℝ)^(j+1)

theorem rate_formula (L T : ℝ) (j : ℕ) : rate L T j = L / T^2 * (4:ℝ)^j := by
  rw [rate,div_pow,←pow_mul,pow_mul' (2:ℝ) j 2]
  norm_num
  ring

theorem rate_ratio (L T : ℝ) (j : ℕ) : rate L T (j+1) = 4 * rate L T j := by
  simp only [rate,pow_succ]
  ring

theorem dyadic_ratio_ge_one (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) : 1 ≤ (2:ℝ)^j / T := by
  apply (le_div_iff₀ hT).mpr
  simpa only [one_mul] using hT1.trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

theorem rate_ge_one (L T : ℝ) (hL : 1 ≤ L) (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    1 ≤ rate L T j := by
  have hx := dyadic_ratio_ge_one T hT hT1 j
  dsimp [rate]
  nlinarith [sq_nonneg ((2:ℝ)^j/T-1)]

theorem rate_length (L T : ℝ) (hT : T ≠ 0) (j : ℕ) :
    rate L T j * length T j = L*((2:ℝ)^j/T)/2 := by
  have hp : (2:ℝ)^j * (1/2:ℝ)^j = 1 := by rw [←mul_pow]; norm_num
  simp only [rate,length,pow_succ]
  field_simp
  nlinarith [congrArg (fun x : ℝ => L*x) hp]

theorem contraction_factor (L T M : ℝ) (p : ℕ) (hM : 0 ≤ M) (hL : 1 ≤ L)
    (hLp : 4*(p:ℝ) ≤ L)
    (hsmall : (4:ℝ)^(2*p)*M*L^p*Real.exp (-L/2) ≤ 1/2)
    (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    (4:ℝ)^(2*p)*M*(rate L T j)^p*Real.exp (-rate L T j * length T j) ≤ 1/2 := by
  have hx := dyadic_ratio_ge_one T hT hT1 j
  have hpoly := polynomial_exp_bound p hLp hx
  have hc : 0 ≤ (4:ℝ)^(2*p)*M*L^p := by positivity
  have hi := mul_le_mul_of_nonneg_left hpoly hc
  have he : -rate L T j * length T j = -L*((2:ℝ)^j/T)/2 := by
    rw [neg_mul,rate_length L T (ne_of_gt hT) j]
    ring
  rw [he]
  dsimp only [rate]
  rw [mul_pow,←pow_mul]
  calc
    (4:ℝ)^(2*p)*M*(L^p*((2:ℝ)^j/T)^(2*p))*Real.exp (-L*((2:ℝ)^j/T)/2) =
      ((4:ℝ)^(2*p)*M*L^p)*(((2:ℝ)^j/T)^(2*p)*Real.exp (-L*((2:ℝ)^j/T)/2)) := by ring
    _ ≤ ((4:ℝ)^(2*p)*M*L^p)*Real.exp (-L/2) := hi
    _ ≤ 1/2 := hsmall

end LinearStochastic.SwitchingRates
