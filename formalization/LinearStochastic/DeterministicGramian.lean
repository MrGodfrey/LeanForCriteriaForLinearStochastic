import LinearStochastic.DeterministicExponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The actual exponential controllability Gramian, its positivity under
Kalman observability, and the resulting genuine finite-dimensional inverse. -/
noncomputable section
namespace LinearStochastic.DeterministicGramian
open MeasureTheory Set
open scoped InnerProductSpace
variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E)

/-- The literal adjoint exponential observation B†e^{tA†}. -/
def observation (t : ℝ) : E →L[ℝ] U := B.adjoint.comp (NormedSpace.exp (t • A.adjoint))

theorem observation_continuous : Continuous (observation A B) :=
  continuous_const.clm_comp (differentiable_exp_smul_const ℝ A.adjoint).continuous

/-- The actual finite-interval Gramian, as a Bochner integral of operators. -/
def gramian (h : ℝ) : E →L[ℝ] E :=
  ∫ t in Icc 0 h, (observation A B t).adjoint.comp (observation A B t)

theorem integrand_continuous : Continuous (fun t : ℝ =>
    (observation A B t).adjoint.comp (observation A B t)) :=
  (ContinuousLinearMap.adjoint.continuous.comp (observation_continuous A B)).clm_comp
    (observation_continuous A B)

/-- The Gramian quadratic form equals the integrated squared observation. -/
theorem quadratic (h : ℝ) (v : E) :
    inner ℝ v (gramian A B h v) = ∫ t in Icc 0 h, ‖observation A B t v‖^2 := by
  have hi : IntegrableOn (fun t => (observation A B t).adjoint.comp (observation A B t)) (Icc 0 h) :=
    (integrand_continuous A B).continuousOn.integrableOn_Icc
  have ha := (ContinuousLinearMap.apply ℝ E v).integrable_comp hi
  change Integrable (fun t => ((observation A B t).adjoint.comp (observation A B t)) v) (volume.restrict (Icc 0 h)) at ha
  rw [gramian,ContinuousLinearMap.integral_apply hi v,←integral_inner ha]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq])

/-- Zero Gramian quadratic form forces all actual Kalman power observations
to vanish; positivity is not included among the assumptions. -/
theorem powers_zero_of_quadratic_zero (h : ℝ) (hh : 0 < h) (v : E)
    (hz : inner ℝ v (gramian A B h v) = 0) :
    ∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0 := by
  rw [quadratic] at hz
  have hc : Continuous (fun t : ℝ => ‖observation A B t v‖^2) :=
    ((observation_continuous A B).clm_apply continuous_const).norm.pow 2
  have hae : (fun t : ℝ => ‖observation A B t v‖^2) =ᵐ[volume.restrict (Icc 0 h)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hc.continuousOn.integrableOn_Icc).mp hz
  have hz' : EqOn (fun t : ℝ => ‖observation A B t v‖^2) (fun _ => 0) (Ioo 0 h) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae)
      isOpen_Ioo hc.continuousOn continuous_const.continuousOn
  apply DeterministicExponential.powers_zero_of_observe_zero A.adjoint B.adjoint h hh v
  intro t ht
  have ht' := hz' ht
  have hn : observation A B t v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp ht')
  simpa only [DeterministicExponential.observe,pow_zero,one_apply_eq_self,
    observation,ContinuousLinearMap.comp_apply] using hn

/-- The actual Gramian is strictly positive under the Kalman kernel condition,
which will be supplied by the literal finite Kalman matrix rank. -/
theorem quadratic_pos (h : ℝ) (hh : 0 < h)
    (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0)
    (v : E) (hv : v ≠ 0) : 0 < inner ℝ v (gramian A B h v) := by
  have hn : 0 ≤ inner ℝ v (gramian A B h v) := by
    rw [quadratic]
    exact integral_nonneg (fun t => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro he
  exact hv (hK v (powers_zero_of_quadratic_zero A B h hh v he.symm))

/-- Injectivity of the concrete integrated operator is proved from positivity. -/
theorem gramian_injective (h : ℝ) (hh : 0 < h)
    (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0) :
    Function.Injective (gramian A B h) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply hK (v-w)
  apply powers_zero_of_quadratic_zero A B h hh (v-w)
  rw [map_sub,hvw,sub_self,inner_zero_right]

variable [FiniteDimensional ℝ E]
/-- The genuine Gramian inverse, justified by its already proved injectivity. -/
def gramianEquiv (h : ℝ) (hh : 0 < h)
    (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (gramian A B h)
    (LinearMap.ker_eq_bot.mpr (gramian_injective A B h hh hK))
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective (f:=(gramian A B h).toLinearMap)).mp
      (gramian_injective A B h hh hK)))

/-- Applying the concrete Gramian to the constructed inverse recovers the
requested displacement exactly. -/
theorem gramian_inverse (h : ℝ) (hh : 0 < h)
    (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0) (v : E) :
    gramian A B h ((gramianEquiv A B h hh hK).symm v) = v :=
  (gramianEquiv A B h hh hK).apply_symm_apply v

end LinearStochastic.DeterministicGramian
