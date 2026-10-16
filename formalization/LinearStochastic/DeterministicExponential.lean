import LinearStochastic.AlgebraDeterministic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A true exponential observation vanishing on a positive interval forces
all Kalman power observations to vanish. This supplies the analytic step in
the finite-horizon deterministic Gramian construction. -/
noncomputable section
namespace LinearStochastic.DeterministicExponential
open MeasureTheory Set
open scoped InnerProductSpace
variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : E →L[ℝ] E) (B : E →L[ℝ] U)

/-- The k-th actual exponential observation. Here A and B have adjoint
orientation, so k=0 is the usual Gramian observation Bᵀe^{tAᵀ}v. -/
def observe (k : ℕ) (v : E) (t : ℝ) : U := B ((NormedSpace.exp (t • A)) ((A^k) v))

omit [CompleteSpace U] in
/-- Differentiation increases the Kalman power by one. -/
theorem observe_derivative (k : ℕ) (v : E) (t : ℝ) :
    HasDerivAt (observe A B k v) (observe A B (k+1) v t) t := by
  have hx := (hasDerivAt_exp_smul_const A t).clm_apply (hasDerivAt_const t ((A^k) v))
  have hb := (B.hasFDerivAt).comp_hasDerivAt t hx
  change HasDerivAt (fun s : ℝ => B ((NormedSpace.exp (s • A)) ((A^k) v))) _ t
  simpa only [Function.comp_def,observe,map_zero,add_zero,mul_apply_eq_comp,pow_succ',
    ContinuousLinearMap.comp_apply] using hb

omit [CompleteSpace U] in
/-- Actual exponential observations are continuous, including at the left
endpoint needed to recover powers from their values on an open interval. -/
theorem observe_continuous (k : ℕ) (v : E) : Continuous (observe A B k v) :=
  continuous_iff_continuousAt.mpr (fun t => (observe_derivative A B k v t).continuousAt)

omit [CompleteSpace U] in
/-- Zero observation on any interval (0,h), h>0, implies every Kalman power
observation vanishes. No analyticity or controllability conclusion is assumed. -/
theorem powers_zero_of_observe_zero (h : ℝ) (hh : 0 < h) (v : E)
    (hz : ∀ t ∈ Ioo 0 h, observe A B 0 v t = 0) : ∀ k : ℕ, B ((A^k) v) = 0 := by
  have hall : ∀ k : ℕ, ∀ t ∈ Ioo 0 h, observe A B k v t = 0 := by
    intro k
    induction k with
    | zero => exact hz
    | succ k ih =>
      intro t ht
      have he : observe A B k v =ᶠ[nhds t] (fun _ => 0) :=
        by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact ih s hs
      have hd := (hasDerivAt_const t (0 : U)).congr_of_eventuallyEq he
      exact (observe_derivative A B k v t).unique hd
  intro k
  have he : EqOn (observe A B k v) (fun _ => 0) (Ioo 0 h) := hall k
  have hc := he.closure (observe_continuous A B k v) continuous_const
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 h) := by rw [closure_Ioo hh.ne]; exact ⟨le_rfl,hh.le⟩
  simpa only [observe,zero_smul,NormedSpace.exp_zero,one_apply_eq_self] using hc h0

end LinearStochastic.DeterministicExponential
