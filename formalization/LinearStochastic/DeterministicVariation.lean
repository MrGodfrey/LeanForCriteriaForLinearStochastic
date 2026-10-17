module

public import LinearStochastic.DeterministicExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! The actual variation-of-constants formula for a continuous forcing term,
with a proved derivative and original drift integral equation. -/
noncomputable section
namespace LinearStochastic.DeterministicVariation
open MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (A : E →L[ℝ] E) (x : E) (f : ℝ → E)

/-- Exponential semigroup identity in the real operator Banach algebra. -/
theorem exp_add (s t : ℝ) :
    NormedSpace.exp ((s+t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul]
  apply NormedSpace.exp_add_of_commute_of_mem_ball (𝕂:=ℝ)
    (((Commute.refl A).smul_left s).smul_right t)
  all_goals
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _

/-- The actual exponential-integral state, not a solution predicate. -/
def state (t : ℝ) : E :=
  (NormedSpace.exp (t • A)) (x + ∫ s in 0..t, (NormedSpace.exp ((-s) • A)) (f s))

theorem exp_inverse_apply (t : ℝ) (v : E) :
    (NormedSpace.exp (t • A)) ((NormedSpace.exp ((-t) • A)) v) = v := by
  rw [←mul_apply_eq_comp,←exp_add A,add_neg_cancel,zero_smul,
    NormedSpace.exp_zero,one_apply_eq_self]

/-- The exponential-integral state has precisely the intended derivative. -/
theorem derivative (hf : Continuous f) (t : ℝ) :
    HasDerivAt (state A x f) (A (state A x f t)+f t) t := by
  have hg : Continuous (fun s : ℝ => (NormedSpace.exp ((-s) • A)) (f s)) :=
    (((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply hf)
  have hp := intervalIntegral.integral_hasDerivAt_right (a:=0) (b:=t) (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hq := (hasDerivAt_const t x).add hp
  have hd := (hasDerivAt_exp_smul_const' A t).clm_apply hq
  change HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A))
    (x+∫ r in 0..s, (NormedSpace.exp ((-r) • A)) (f r))) _ t
  simpa only [state,mul_apply_eq_comp,Pi.add_apply,zero_add,exp_inverse_apply A] using hd

/-- In particular the constructed state is continuous at every real time. -/
theorem continuous_state (hf : Continuous f) : Continuous (state A x f) :=
  continuous_iff_continuousAt.mpr (fun t => (derivative A x f hf t).continuousAt)

omit [CompleteSpace E] in
theorem initial : state A x f 0 = x := by
  simp only [state,zero_smul,NormedSpace.exp_zero,intervalIntegral.integral_same,add_zero,one_apply_eq_self]

/-- This is the actual original integral equation, not just a terminal
convolution formula. -/
theorem integral_equation (hf : Continuous f) (t : ℝ) :
    state A x f t = x + ∫ s in 0..t, A (state A x f s)+f s := by
  have hc : Continuous (fun s => A (state A x f s)+f s) :=
    (A.continuous.comp (continuous_state A x f hf)).add hf
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=t) (fun s _ => derivative A x f hf s) (hc.intervalIntegrable 0 t)
  rw [initial] at he
  rw [he]
  abel

/-- The same actual state has the standard endpoint convolution formula. -/
theorem convolution (hf : Continuous f) (t : ℝ) :
    state A x f t = (NormedSpace.exp (t • A)) x +
      ∫ s in 0..t, (NormedSpace.exp ((t-s) • A)) (f s) := by
  have hg : Continuous (fun s : ℝ => (NormedSpace.exp ((-s) • A)) (f s)) :=
    (((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply hf)
  rw [state,map_add,←(NormedSpace.exp (t • A)).intervalIntegral_comp_comm (hg.intervalIntegrable 0 t)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [←mul_apply_eq_comp,←exp_add A]
  simp only [sub_eq_add_neg]

end LinearStochastic.DeterministicVariation
