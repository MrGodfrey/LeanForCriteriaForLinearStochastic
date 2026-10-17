module

public import LinearStochastic.SwitchingDynamics

@[expose] public section

/-! Summability and vanishing endpoint moments for the actually constructed
random switching solution, derived from its actual SDE estimates. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace LinearStochastic.SwitchingSummability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal InnerProductSpace BigOperators
open FeedbackIntervalRestart SwitchingFeedbackFamily SwitchingTimeMesh SwitchingRates SwitchingDynamics
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
  (f : Family (T:ℝ) A B C D)
  (ξ₀ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0))

variable (q : Run hW hWm T A B C D f ξ₀)

def weighted (j : ℕ) : ℝ := (rate f.L (T:ℝ) j)^(2*f.p)*moment hW hWm T A B C D f ξ₀ q j

def constant : ℝ := f.M^2*weighted hW hWm T A B C D f ξ₀ q 0/rate f.L (T:ℝ) 0

theorem rate_scaling (j : ℕ) : rate f.L (T:ℝ) j = (4:ℝ)^j*rate f.L (T:ℝ) 0 := by
  rw [rate_formula,rate_formula]
  simp only [pow_zero,mul_one]
  ring

theorem weighted_nonneg (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    0 ≤ weighted hW hWm T A B C D f ξ₀ q j :=
  mul_nonneg (pow_nonneg (zero_le_one.trans (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 j)) _)
    (moment_nonneg hW hWm T A B C D f ξ₀ q j)

theorem contraction (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    weighted hW hWm T A B C D f ξ₀ q (j+1) ≤ (1/2:ℝ)*weighted hW hWm T A B C D f ξ₀ q j := by
  exact Switching.rescaled_contraction (moment hW hWm T A B C D f ξ₀ q)
    (rate f.L (T:ℝ)) (length (T:ℝ)) f.M f.p
    (moment_nonneg hW hWm T A B C D f ξ₀ q)
    (fun j => zero_le_one.trans (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 j))
    (rate_ratio f.L (T:ℝ)) (moment_step hW hWm T A B C D f ξ₀ q)
    (uniform_contraction (T:ℝ) hT hT1 A B C D f) j

theorem energy_summable (hT : 0 < T) (hT1 : T ≤ 1) :
    Summable (fun j => ‖control hW hWm T A B C D f ξ₀ q j‖^2) ∧
    (∑' j, ‖control hW hWm T A B C D f ξ₀ q j‖^2) ≤
      (8/7:ℝ)*f.M^2*weighted hW hWm T A B C D f ξ₀ q 0/rate f.L (T:ℝ) 0 := by
  apply Switching.energy_summable_and_bound
    (weighted hW hWm T A B C D f ξ₀ q) _ f.M (rate f.L (T:ℝ) 0)
    (lt_of_lt_of_le zero_lt_one (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 0))
    (weighted_nonneg hW hWm T A B C D f ξ₀ q hT hT1) (fun _ => sq_nonneg _)
    (contraction hW hWm T A B C D f ξ₀ q hT hT1)
  intro j
  rw [←rate_scaling T A B C D f j]
  have h := control_energy hW hWm T A B C D f ξ₀ q hT hT1 j
  dsimp only [weighted]
  convert h using 1
  ring

theorem energy_geometric (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    ‖control hW hWm T A B C D f ξ₀ q j‖^2 ≤ constant hW hWm T A B C D f ξ₀ q*(1/8:ℝ)^j := by
  have hd := Switching.quotient_decay (weighted hW hWm T A B C D f ξ₀ q)
    (lt_of_lt_of_le zero_lt_one (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 0))
    (contraction hW hWm T A B C D f ξ₀ q hT hT1) j
  have hg := mul_le_mul_of_nonneg_left hd (sq_nonneg f.M)
  rw [←rate_scaling T A B C D f j] at hg
  have he := control_energy hW hWm T A B C D f ξ₀ q hT hT1 j
  dsimp only [weighted,constant] at *
  calc
    _ ≤ f.M^2*((rate f.L (T:ℝ) j)^(2*f.p)*moment hW hWm T A B C D f ξ₀ q j)/rate f.L (T:ℝ) j := he
    _ = f.M^2*(((rate f.L (T:ℝ) j)^(2*f.p)*moment hW hWm T A B C D f ξ₀ q j)/rate f.L (T:ℝ) j) := by ring
    _ ≤ _ := hg
    _ = _ := by ring

theorem norms_summable (hT : 0 < T) (hT1 : T ≤ 1) :
    Summable (fun j => ‖control hW hWm T A B C D f ξ₀ q j‖) := by
  let c := constant hW hWm T A B C D f ξ₀ q
  have hc : 0 ≤ c := div_nonneg
    (mul_nonneg (sq_nonneg f.M) (weighted_nonneg hW hWm T A B C D f ξ₀ q hT hT1 0))
    (zero_le_one.trans (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 0))
  have hs : Summable (fun j : ℕ => (c+1)*(1/2:ℝ)^j) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left (c+1)
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg (control hW hWm T A B C D f ξ₀ q j)) _ hs
  intro j
  have he := energy_geometric hW hWm T A B C D f ξ₀ q hT hT1 j
  have hg : (1/8:ℝ)^j ≤ (1/4:ℝ)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hb : c*(1/8:ℝ)^j ≤ (c+1)^2*(1/4:ℝ)^j :=
    mul_le_mul (by nlinarith : c ≤ (c+1)^2) hg (by positivity) (by positivity)
  have heq : ((c+1)*(1/2:ℝ)^j)^2 = (c+1)^2*(1/4:ℝ)^j := by
    rw [mul_pow,←pow_mul,pow_mul' (1/2:ℝ) j 2]
    norm_num
  have hbnd : ‖control hW hWm T A B C D f ξ₀ q j‖^2 ≤ ((c+1)*(1/2:ℝ)^j)^2 :=
    he.trans (hb.trans_eq heq.symm)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hbnd

theorem moment_tendsto_zero (hT : 0 < T) (hT1 : T ≤ 1) :
    Tendsto (moment hW hWm T A B C D f ξ₀ q) atTop (𝓝 0) := by
  apply Switching.state_sequence_tends_to_zero _ (weighted hW hWm T A B C D f ξ₀ q)
    (moment_nonneg hW hWm T A B C D f ξ₀ q)
  · intro j
    exact le_mul_of_one_le_left (moment_nonneg hW hWm T A B C D f ξ₀ q j)
      (one_le_pow₀ (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 j))
  · exact contraction hW hWm T A B C D f ξ₀ q hT hT1

end LinearStochastic.SwitchingSummability
