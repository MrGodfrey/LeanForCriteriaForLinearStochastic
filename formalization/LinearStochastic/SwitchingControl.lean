import LinearStochastic.SwitchingSummability
import LinearStochastic.VectorH2Orthogonality

/-! A genuine admissible global switching control is the orthogonal sum of
its actual locally solved feedback controls. The exact paper energy constant
is retained and every actual shifted window recovers its local control. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingControl
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


theorem inside (j : ℕ) : time T j+duration T j ≤ T := by
  rw [next_time]
  exact time_le T (j+1)

theorem time_mono (hT : 0 < T) {i j : ℕ} (hij : i ≤ j) : time T i ≤ time T j := by
  apply NNReal.coe_le_coe.mp
  rw [coe_time,coe_time]
  exact (Switching.switchTime_strictMono (show (0:ℝ)<T from hT)).monotone hij

theorem separated (hT : 0 < T) (i j : ℕ) (hij : i ≠ j) :
    time T i+duration T i ≤ time T j ∨ time T j+duration T j ≤ time T i := by
  rw [next_time,next_time]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact Or.inl (time_mono T hT (Nat.succ_le_of_lt hlt))
  · exact Or.inr (time_mono T hT (Nat.succ_le_of_lt hgt))

def total (i₀ : Fin m) : Lp (EuclideanSpace ℝ (Fin r)) 2
    (CommonItoMultichannel.spacetimeMeasure 𝓕 μ T) :=
  ∑' j, VectorH2Extension.extendShift (EuclideanSpace.basisFun (Fin r) ℝ) (hWm i₀)
    (time T j) (duration T j) T (inside T j) (control hW hWm T A B C D f ξ₀ q j)

theorem energy_identity (i₀ : Fin m) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖total hW hWm T A B C D f ξ₀ q i₀‖^2 = ∑' j, ‖control hW hWm T A B C D f ξ₀ q j‖^2 :=
  VectorH2Orthogonality.extensions_norm_tsum_sq (EuclideanSpace.basisFun (Fin r) ℝ) (hWm i₀)
    T (time T) (duration T) (inside T) (control hW hWm T A B C D f ξ₀ q)
    (SwitchingSummability.norms_summable hW hWm T A B C D f ξ₀ q hT hT1) (separated T hT)

theorem energy_bound (i₀ : Fin m) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖total hW hWm T A B C D f ξ₀ q i₀‖^2 ≤
    (8/7:ℝ)*f.M^2*SwitchingSummability.weighted hW hWm T A B C D f ξ₀ q 0/rate f.L (T:ℝ) 0 := by
  rw [energy_identity hW hWm T A B C D f ξ₀ q i₀ hT hT1]
  exact (SwitchingSummability.energy_summable hW hWm T A B C D f ξ₀ q hT hT1).2

theorem recover_window (i₀ : Fin m) (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    VectorH2Extension.shift (EuclideanSpace.basisFun (Fin r) ℝ) (time T j) (duration T j) T (inside T j)
      (total hW hWm T A B C D f ξ₀ q i₀) = control hW hWm T A B C D f ξ₀ q j :=
  VectorH2Orthogonality.shift_tsum_extensions (EuclideanSpace.basisFun (Fin r) ℝ) (hWm i₀)
    T (time T) (duration T) (inside T) (control hW hWm T A B C D f ξ₀ q)
    (SwitchingSummability.norms_summable hW hWm T A B C D f ξ₀ q hT hT1) (separated T hT) j

theorem cost_formula (hT : 0 < T) :
    (8/7:ℝ)*f.M^2*SwitchingSummability.weighted hW hWm T A B C D f ξ₀ q 0/rate f.L (T:ℝ) 0 =
    ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*(∫ ω, ‖ξ₀.val ω‖^2 ∂μ) := by
  have hL : f.L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one f.L_ge_one)
  have hT0 : (T:ℝ) ≠ 0 := ne_of_gt (show (0:ℝ)<T from hT)
  have hp : 2*f.p = (2*f.p-1)+1 := by have := f.p_ge_one; omega
  have he : 2*(2*f.p-1) = 4*f.p-2 := by have := f.p_ge_one; omega
  have hr : rate f.L (T:ℝ) 0 = f.L/(T:ℝ)^2 := by rw [rate_formula]; simp
  dsimp only [SwitchingSummability.weighted]
  rw [SwitchingDynamics.moment_zero,hr]
  have hpow : (f.L/(T:ℝ)^2)^(2*f.p)/(f.L/(T:ℝ)^2) = f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2) := by
    rw [hp,pow_succ,mul_div_cancel_right₀ _ (div_ne_zero hL (pow_ne_zero _ hT0)),div_pow,←pow_mul,he]
    simp
  calc
    _ = (8/7:ℝ)*f.M^2*((f.L/(T:ℝ)^2)^(2*f.p)/(f.L/(T:ℝ)^2))*(∫ ω, ‖ξ₀.val ω‖^2 ∂μ) := by ring
    _ = _ := by rw [hpow]; ring

theorem paper_energy_bound (i₀ : Fin m) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖total hW hWm T A B C D f ξ₀ q i₀‖^2 ≤
      ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*(∫ ω, ‖ξ₀.val ω‖^2 ∂μ) := by
  have h := energy_bound hW hWm T A B C D f ξ₀ q i₀ hT hT1
  rwa [cost_formula hW hWm T A B C D f ξ₀ q hT] at h

end LinearStochastic.SwitchingControl
