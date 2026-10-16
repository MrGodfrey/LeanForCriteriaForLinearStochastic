import LinearStochastic.ScalarGramianEnergy
import LinearStochastic.JointUsualBrownianGlobal

/-! A genuine unbounded-energy delayed-target approximation for dy=u dt:
the target is W_T, its conditional targets are W_a, and the actual Gramian
controls have energy a/(T-a). -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianDelayedEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
open CommonItoMultichannel

section Common
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hW : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))

include hW hWm in
/-- The earlier Brownian value is the actual conditional expectation on the
specified common filtration, proved from future-increment independence. -/
theorem conditional_target (a T : ℝ≥0) (ha : a≤T) : μ[W T | 𝓕 a] =ᵐ[μ] W a := by
  have hi (t : ℝ≥0) : Integrable (W t) μ :=
    (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable (by norm_num)
  have hadapt : StronglyMeasurable[𝓕 a] (W a) :=
    (CommonItoIsometry.adaptedAt_eval (μ:=μ) (𝓕:=𝓕) (B:=W) (le_refl a)).stronglyMeasurable
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le a) (hi T)
    (fun s _ _=>(hi a).integrableOn) (fun s hs _=>?_) hadapt.aestronglyMeasurable
  have hz : (∫ ω in s, W T ω-W a ω ∂μ)=0 := by
    rw [←integral_indicator (𝓕.le a s hs)]
    have he : s.indicator (fun ω=>W T ω-W a ω)=
        fun ω=>s.indicator (1 : Ω→ℝ) ω*(W T ω-W a ω) := by
      funext ω
      by_cases hω : ω∈s <;> simp [hω]
    rw [he]
    exact CommonItoIsometry.integral_adapted_mul_increment hW hWm ha
      ((measurable_const : Measurable[𝓕 a] (1 : Ω→ℝ)).indicator hs)
  rw [integral_sub (hi T).integrableOn (hi a).integrableOn] at hz
  linarith
end Common

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)
  (i₀ : Fin m)

/-- Actual finite-energy progressive controls and continuous S² raw states
for the scalar zero-noise system, with exact conditional targets and error. -/
theorem delayed_solution (a T : ℝ≥0) (ha : a<T) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ (u X : Lp ℝ 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
      (R : ℝ≥0 → Ω → ℝ),
      ProgressiveControlSection.RawSolution (OrthonormalBasis.singleton Unit ℝ)
        (fun i=>(hW i).toIsPreBrownianReal) hWm T (fun _=>0) 0 (ContinuousLinearMap.id ℝ ℝ)
        (fun _ : Fin m=>0) (fun _=>0) (ScalarGramianEnergy.control (W:=W i₀) a T) R u X ∧
      R T =ᵐ[μ] W i₀ a ∧
      μ[W i₀ T | (JointUsualNatural.usual (μ:=μ) W hWm) a] =ᵐ[μ] W i₀ a ∧
      (∫ ω, ‖R T ω-W i₀ T ω‖^2 ∂μ)=(T:ℝ)-a ∧
      (∫ t in Ioc 0 (T:ℝ), ∫ ω, ‖ScalarGramianEnergy.control (W:=W i₀) a T t.toNNReal ω‖^2 ∂μ)=
        (a:ℝ)/((T:ℝ)-a) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have hη : StronglyMeasurable[(JointUsualNatural.usual (μ:=μ) W hWm) a] (W i₀ a) :=
    (CommonItoIsometry.adaptedAt_eval (μ:=μ) (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (B:=W i₀) (le_refl a)).stronglyMeasurable
  have hη2 : MemLp (W i₀ a) 2 μ := ((hW i₀).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
  obtain ⟨u,X,hr,hend,_⟩ := KnownTargetSolution.exists_solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    (OrthonormalBasis.singleton Unit ℝ) (fun i=>(hW i).toIsPreBrownianReal) hWm
    (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) a T ha ScalarGramianEnergy.observable 0 (W i₀ a) hη hη2
  simp only [map_zero,sub_zero] at hr hend
  let K := DeterministicGramianControl.kernel (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
    ((T:ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) ScalarGramianEnergy.observable
  let R := KnownTargetState.path (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) K a 0 (W i₀ a)
  have ht : R T =ᵐ[μ] W i₀ a := Filter.Eventually.of_forall hend
  refine ⟨u,X,R,?_,ht,conditional_target (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    (hW i₀).toIsPreBrownianReal (hWm i₀) a T ha.le,?_,
    ScalarGramianEnergy.energy (hW i₀).toIsPreBrownianReal (hWm i₀) a T ha⟩
  · rw [ScalarGramianEnergy.control_is_gramian a T ha]
    exact hr
  · calc
      _ = ∫ ω, (W i₀ T ω-W i₀ a ω)^2 ∂μ := integral_congr_ae (ht.mono (fun ω hω=>by
        rw [hω,Real.norm_eq_abs,sq_abs]; ring))
      _ = _ := CommonItoIsometry.integral_increment_sq (hW i₀).toIsPreBrownianReal ha.le

/-- The earlier times approach one through a_k=k/(k+1). -/
def earlier (k : ℕ) : ℝ≥0 := (k:ℝ≥0)/((k:ℝ≥0)+1)

theorem earlier_lt (k : ℕ) : earlier k<1 := by
  dsimp [earlier]
  apply (div_lt_one (by positivity)).mpr
  exact lt_add_one _

theorem earlier_gap (k : ℕ) : 1-(earlier k:ℝ)=1/((k:ℝ)+1) := by
  simp only [earlier,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  field_simp
  ring

/-- Discarding k=0 leaves strictly positive earlier times, as required by
0<h<T in the paper's delayed-target construction. -/
theorem earlier_pos (k : ℕ) (hk : 0<k) : 0<earlier k := by
  dsimp [earlier]
  positivity

/-- Its time-to-go really tends to zero. -/
theorem gap_tends_zero : Filter.Tendsto (fun k=>1-(earlier k:ℝ)) Filter.atTop (𝓝 0) := by
  simp only [earlier_gap]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

include hW hWm in
omit [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- The genuine control energies equal k, so they diverge along exactly the
same family whose terminal squared errors are 1/(k+1). -/
theorem energy_at_earlier (k : ℕ) :
    (∫ t in Ioc (0:ℝ) 1, ∫ ω,
      ‖ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1 t.toNNReal ω‖^2 ∂μ)=(k:ℝ) := by
  have he := ScalarGramianEnergy.energy (hW i₀).toIsPreBrownianReal (hWm i₀) (earlier k) 1 (earlier_lt k)
  simp only [NNReal.coe_one] at he
  rw [he,earlier_gap]
  simp only [earlier,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  field_simp

include hW hWm in
omit [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- Unbounded energy is an actual example, not an unproved possibility. -/
theorem energy_diverges : Filter.Tendsto (fun k=>∫ t in Ioc (0:ℝ) 1, ∫ ω,
    ‖ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1 t.toNNReal ω‖^2 ∂μ) Filter.atTop Filter.atTop := by
  simp only [energy_at_earlier hW hWm i₀]
  exact tendsto_natCast_atTop_atTop

include hW hWm in
omit [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- The paper's exact E∫dt order gives the same divergent energy k. -/
theorem expected_energy_at_earlier (k : ℕ) :
    (∫ ω,(∫ t in Ioc (0:ℝ) 1,
      ‖ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1 t.toNNReal ω‖^2) ∂μ)=(k:ℝ) := by
  have he := ScalarGramianEnergy.expected_energy (hW i₀).toIsPreBrownianReal (hWm i₀) (earlier k) 1 (earlier_lt k)
  simp only [NNReal.coe_one] at he
  rw [he,earlier_gap]
  simp only [earlier,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  field_simp

include hW hWm in
omit [IsProbabilityMeasure μ] [μ.IsComplete] in
theorem expected_energy_diverges : Filter.Tendsto (fun k=>∫ ω,(∫ t in Ioc (0:ℝ) 1,
    ‖ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1 t.toNNReal ω‖^2) ∂μ) Filter.atTop Filter.atTop := by
  simp only [expected_energy_at_earlier hW hWm i₀]
  exact tendsto_natCast_atTop_atTop

/-- One actual sequence has simultaneous vanishing terminal error and
unbounded control energy, for the fixed scalar target W₁ on the original usual
filtration. Every control is the literal delayed Gramian control above. -/
theorem unbounded_approximation :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ (u X : ℕ → Lp ℝ 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ 1))
      (R : ℕ → ℝ≥0 → Ω → ℝ),
      (∀ k, ProgressiveControlSection.RawSolution (OrthonormalBasis.singleton Unit ℝ)
        (fun i=>(hW i).toIsPreBrownianReal) hWm 1 (fun _=>0) 0 (ContinuousLinearMap.id ℝ ℝ)
        (fun _ : Fin m=>0) (fun _=>0) (ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1) (R k) (u k) (X k)) ∧
      (∀ k, R k 1 =ᵐ[μ] μ[W i₀ 1 | (JointUsualNatural.usual (μ:=μ) W hWm) (earlier k)]) ∧
      Filter.Tendsto (fun k=>∫ ω, ‖R k 1 ω-W i₀ 1 ω‖^2 ∂μ) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k=>∫ ω,(∫ t in Ioc (0:ℝ) 1,
        ‖ScalarGramianEnergy.control (W:=W i₀) (earlier k) 1 t.toNNReal ω‖^2) ∂μ) Filter.atTop Filter.atTop := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have hs (k : ℕ) := delayed_solution hW hWm hInd i₀ (earlier k) 1 (earlier_lt k)
  choose u X R hr ht hc he hE using hs
  refine ⟨u,X,R,hr,(fun k=>(ht k).trans (hc k).symm),?_,expected_energy_diverges hW hWm i₀⟩
  have he' : (fun k=>∫ ω, ‖R k 1 ω-W i₀ 1 ω‖^2 ∂μ)=fun k=>1-(earlier k:ℝ) := by
    funext k
    simpa only [NNReal.coe_one] using he k
  rw [he']
  exact gap_tends_zero

end LinearStochastic.BrownianDelayedEnergy
