module

public import LinearStochastic.DeterministicGramian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! The classical exponential Gramian steering kernel and its exact terminal
integral identity, before random delayed targets are substituted into it. -/
noncomputable section
namespace LinearStochastic.DeterministicGramianControl
open MeasureTheory Set
open scoped InnerProductSpace
open DeterministicGramian
variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E)

/-- Taking the adjoint gives the actual forward exponential e^{tA}B. -/
theorem observation_adjoint (t : ℝ) :
    (observation A B t).adjoint = (NormedSpace.exp (t • A)).comp B := by
  rw [observation,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  congr 1
  rw [←ContinuousLinearMap.star_eq_adjoint,NormedSpace.star_exp]
  congr 1
  simp only [star_smul,star_trivial,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint]

/-- The integrated operator is literally the usual exponential Gramian. -/
theorem gramian_classical (h : ℝ) :
    gramian A B h = ∫ t in Icc 0 h,
      (NormedSpace.exp (t • A)).comp (B.comp (B.adjoint.comp (NormedSpace.exp (t • A.adjoint)))) := by
  unfold gramian
  apply integral_congr_ae
  filter_upwards [] with t
  rw [observation_adjoint]
  rfl

variable [FiniteDimensional ℝ E]
  (h : ℝ) (hh : 0 < h)
  (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v) = 0) → v=0)

/-- The actual last-interval steering kernel B†e^{(h−t)A†}G_h⁻¹. -/
def kernel (t : ℝ) : E →L[ℝ] U :=
  (observation A B (h-t)).comp (gramianEquiv A B h hh hK).symm.toContinuousLinearMap

theorem kernel_continuous : Continuous (kernel A B h hh hK) :=
  ((observation_continuous A B).comp (continuous_const.sub continuous_id)).clm_comp continuous_const

/-- The prescribed exponential kernel attains each deterministic displacement
exactly through the true endpoint integral. -/
theorem terminal_integral (v : E) :
    (∫ t in Icc 0 h, (NormedSpace.exp ((h-t) • A)) (B (kernel A B h hh hK t v))) = v := by
  let w := (gramianEquiv A B h hh hK).symm v
  let f := fun t : ℝ => ((observation A B t).adjoint.comp (observation A B t)) w
  have hi : IntegrableOn (fun t => (observation A B t).adjoint.comp (observation A B t)) (Icc 0 h) :=
    (integrand_continuous A B).continuousOn.integrableOn_Icc
  have he : (fun t => (NormedSpace.exp ((h-t) • A)) (B (kernel A B h hh hK t v))) =
      fun t => f (h-t) := by
    funext t
    simp only [f,kernel,observation_adjoint,ContinuousLinearMap.comp_apply]
    rfl
  rw [he]
  calc
    (∫ t in Icc 0 h, f (h-t)) = ∫ t in Icc 0 h, f t := by
      rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hh.le,
        intervalIntegral.integral_comp_sub_left]
      simp only [sub_self,sub_zero]
      rw [intervalIntegral.integral_of_le hh.le,←integral_Icc_eq_integral_Ioc]
    _ = gramian A B h w := (ContinuousLinearMap.integral_apply hi w).symm
    _ = v := gramian_inverse A B h hh hK v

/-- Each fixed positive interval has a finite deterministic kernel-energy
bound; no assertion of uniformity as h tends to zero is used. -/
theorem kernel_square_integrable (v : E) :
    IntegrableOn (fun t : ℝ => ‖kernel A B h hh hK t v‖^2) (Icc 0 h) :=
  (((kernel_continuous A B h hh hK).clm_apply continuous_const).norm.pow 2).continuousOn.integrableOn_Icc

end LinearStochastic.DeterministicGramianControl
