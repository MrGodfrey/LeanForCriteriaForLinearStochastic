import LinearStochastic.FeedbackRecursion
import LinearStochastic.SwitchingFeedbackFamily
import LinearStochastic.SwitchingTimeMesh

/-! Actual stochastic dynamics driven by the polynomially controlled family
on the manuscript's countable dyadic mesh. -/
noncomputable section
namespace LinearStochastic.SwitchingDynamics
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonTimeShift FeedbackIntervalData FeedbackIntervalRestart SwitchingFeedbackFamily
open SwitchingTimeMesh SwitchingRates MatrixGrowthBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
  (f : Family (T:ℝ) A B C D)
  (ξ₀ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0))

local instance shiftedForwardFamily (s : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (s+t) ω-W i s ω)
      (filtration 𝓕 s) μ := fun _ => CommonTimeShift.forwardIndependent s

structure Run where
  initials : (j : ℕ) → Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T j)
  initial_zero : initials 0 = ξ₀
  piece : (j : ℕ) → Data (𝓕:=filtration 𝓕 (time T j)) (fun i => (hW i).shift (time T j))
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) (time T j)) (duration T j) (rate f.L (T:ℝ) j)
    A B C D (f.P j) (f.U j) (f.positive j) (initials j).val
  next : ∀ j, (initials (j+1)).val = (piece j).path (duration T j)

theorem exists_run (i₀ : Fin m)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (hT : 0 < T) (hT1 : T ≤ 1) : Nonempty (Run hW hWm T A B C D f ξ₀) := by
  have hr (j : ℕ) : 0 < rate f.L (T:ℝ) j := lt_of_lt_of_le zero_lt_one
    (rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 j)
  exact ⟨⟨FeedbackRecursion.states hW hWm i₀ hpair hchannels (time T) (duration T)
      (next_time T) (rate f.L (T:ℝ)) hr A B C D f.P f.U f.positive f.feasible ξ₀,
    rfl,
    FeedbackRecursion.segment hW hWm i₀ hpair hchannels (time T) (duration T)
      (next_time T) (rate f.L (T:ℝ)) hr A B C D f.P f.U f.positive f.feasible ξ₀,
    fun _ => rfl⟩⟩

variable (q : Run hW hWm T A B C D f ξ₀)

def moment (j : ℕ) : ℝ := ∫ ω, ‖(q.initials j).val ω‖^2 ∂μ

def control (j : ℕ) : Lp (EuclideanSpace ℝ (Fin r)) 2
    (CommonItoMultichannel.spacetimeMeasure (filtration 𝓕 (time T j)) μ (duration T j)) :=
  (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap.compLp (q.piece j).X

omit [𝓕.IsComplete μ] in
theorem moment_nonneg (j : ℕ) : 0 ≤ moment hW hWm T A B C D f ξ₀ q j :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [𝓕.IsComplete μ] in
theorem moment_zero : moment hW hWm T A B C D f ξ₀ q 0 = ∫ ω, ‖ξ₀.val ω‖^2 ∂μ := by
  simp only [moment,q.initial_zero]

omit [𝓕.IsComplete μ] in
theorem moment_step (j : ℕ) :
    moment hW hWm T A B C D f ξ₀ q (j+1) ≤
    f.M*(rate f.L (T:ℝ) j)^f.p*Real.exp (-rate f.L (T:ℝ) j*length (T:ℝ) j)*
    moment hW hWm T A B C D f ξ₀ q j := by
  have hd := (q.piece j).decay (duration T j) le_rfl
  rw [coe_duration] at hd
  dsimp only [moment]
  rw [q.next]
  apply hd.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (f.condition j) (Real.exp_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

omit [𝓕.IsComplete μ] in
theorem control_energy (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    ‖control hW hWm T A B C D f ξ₀ q j‖^2 ≤
    f.M^2*((rate f.L (T:ℝ) j)^(2*f.p)*moment hW hWm T A B C D f ξ₀ q j)/rate f.L (T:ℝ) j := by
  have hr := rate_ge_one f.L (T:ℝ) f.L_ge_one hT hT1 j
  have hr0 : 0 < rate f.L (T:ℝ) j := lt_of_lt_of_le zero_lt_one hr
  have hm := moment_nonneg hW hWm T A B C D f ξ₀ q j
  have hc : 0 ≤ conditionNumber (f.P j) (f.positive j).isHermitian :=
    div_nonneg (MatrixInverseEnergyBounds.max_eigen_pos (f.P j) (f.positive j)).le
      (MatrixInverseEnergyBounds.min_eigen_pos (f.P j) (f.positive j)).le
  have hcond := f.condition j
  have hgain := f.gain j
  have hM : 0 ≤ f.M := zero_le_one.trans f.M_ge_one
  calc
    ‖control hW hWm T A B C D f ξ₀ q j‖^2 ≤
        ‖(f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 *
        (conditionNumber (f.P j) (f.positive j).isHermitian * moment hW hWm T A B C D f ξ₀ q j /
          rate f.L (T:ℝ) j) := (q.piece j).controlEnergy
    _ ≤ (f.M*(rate f.L (T:ℝ) j)^f.p) *
        ((f.M*(rate f.L (T:ℝ) j)^f.p)*moment hW hWm T A B C D f ξ₀ q j / rate f.L (T:ℝ) j) := by
      apply mul_le_mul hgain
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcond hm) hr0.le
      · exact div_nonneg (mul_nonneg hc hm) hr0.le
      · positivity
    _ = _ := by rw [pow_mul]; ring

end LinearStochastic.SwitchingDynamics
