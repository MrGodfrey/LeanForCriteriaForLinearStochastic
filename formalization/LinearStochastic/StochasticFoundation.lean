module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# Gaussian increment integration

This is the single-interval analytic foundation of the Itô integral, on an
actual probability space. The coefficient is a random variable in L² and is
independent of a centered Gaussian increment. Theorems prove L² membership,
zero mean, and the Itô second-moment identity for their product.

Independence and the Gaussian law are explicit stochastic hypotheses. They
must subsequently be obtained from adaptedness and a Brownian filtration;
this module does not define controllability or assume an SDE theorem.
-/

namespace LinearStochastic.StochasticFoundation

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {increment coefficient : Ω → ℝ} {variance : ℝ≥0}

theorem gaussian_increment_memLp
    (hlaw : HasLaw increment (gaussianReal 0 variance) P) :
    MemLp increment 2 P := by
  have h : MemLp (id : ℝ → ℝ) 2 (Measure.map increment P) := by
    rw [hlaw.map_eq]
    exact memLp_id_gaussianReal 2
  simpa only [Function.id_comp] using h.comp_of_map hlaw.aemeasurable

theorem gaussian_increment_mean
    (hlaw : HasLaw increment (gaussianReal 0 variance) P) :
    (∫ ω, increment ω ∂P) = 0 := by
  simpa using hlaw.integral_eq

theorem gaussian_increment_second_moment
    (hlaw : HasLaw increment (gaussianReal 0 variance) P) :
    (∫ ω, increment ω ^ 2 ∂P) = variance := by
  have hvar := hlaw.variance_eq
  rw [variance_eq_integral hlaw.aemeasurable, gaussian_increment_mean hlaw] at hvar
  simpa using hvar

/-- The coefficient times a future independent increment is genuinely L². -/
theorem elementary_integral_memLp
    (hlaw : HasLaw increment (gaussianReal 0 variance) P)
    (hindep : IndepFun coefficient increment P)
    (hcoeff : MemLp coefficient 2 P) :
    MemLp (fun ω ↦ coefficient ω * increment ω) 2 P := by
  have hinc := gaussian_increment_memLp hlaw
  have hsq := hindep.comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2)
    (by fun_prop) (by fun_prop)
  have hprod := hsq.integrable_mul hcoeff.integrable_sq hinc.integrable_sq
  change Integrable (fun ω ↦ coefficient ω ^ 2 * increment ω ^ 2) P at hprod
  refine (memLp_two_iff_integrable_sq (hcoeff.aestronglyMeasurable.mul hinc.aestronglyMeasurable)).mpr ?_
  simpa only [Pi.mul_apply, mul_pow] using hprod

theorem elementary_integral_mean_zero
    (hlaw : HasLaw increment (gaussianReal 0 variance) P)
    (hindep : IndepFun coefficient increment P)
    (hcoeff : MemLp coefficient 2 P) :
    (∫ ω, coefficient ω * increment ω ∂P) = 0 := by
  rw [hindep.integral_fun_mul_eq_mul_integral hcoeff.aestronglyMeasurable
    (gaussian_increment_memLp hlaw).aestronglyMeasurable, gaussian_increment_mean hlaw, mul_zero]

/-- The elementary Itô isometry; integrability is separately proved above. -/
theorem elementary_integral_isometry
    (hlaw : HasLaw increment (gaussianReal 0 variance) P)
    (hindep : IndepFun coefficient increment P)
    (hcoeff : MemLp coefficient 2 P) :
    (∫ ω, (coefficient ω * increment ω) ^ 2 ∂P) =
      (∫ ω, coefficient ω ^ 2 ∂P) * variance := by
  have hsq := hindep.comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2)
    (by fun_prop) (by fun_prop)
  have h := hsq.integral_fun_mul_eq_mul_integral
    hcoeff.integrable_sq.1 (gaussian_increment_memLp hlaw).integrable_sq.1
  simpa only [Function.comp_apply, ← mul_pow, gaussian_increment_second_moment hlaw] using h

/-- Measurability with respect to the past gives the needed independence. -/
theorem adapted_independent_increment (past : MeasurableSpace Ω)
    (hfuture : Indep past (MeasurableSpace.comap increment inferInstance) P)
    (hadapted : @Measurable Ω ℝ past inferInstance coefficient) :
    IndepFun coefficient increment P := by
  change Indep (MeasurableSpace.comap coefficient inferInstance)
    (MeasurableSpace.comap increment inferInstance) P
  exact indep_of_indep_of_le_left hfuture (measurable_iff_comap_le.mp hadapted)

/-- The one-step adapted integral has finite energy, zero mean, and the exact isometry. -/
theorem adapted_increment_energy (past : MeasurableSpace Ω)
    (hfuture : Indep past (MeasurableSpace.comap increment inferInstance) P)
    (hadapted : @Measurable Ω ℝ past inferInstance coefficient)
    (hlaw : HasLaw increment (gaussianReal 0 variance) P)
    (hcoeff : MemLp coefficient 2 P) :
    MemLp (fun ω ↦ coefficient ω * increment ω) 2 P ∧
      (∫ ω, coefficient ω * increment ω ∂P) = 0 ∧
      (∫ ω, (coefficient ω * increment ω) ^ 2 ∂P) =
        (∫ ω, coefficient ω ^ 2 ∂P) * variance := by
  letI : MeasurableSpace Ω := mΩ
  have hindep := adapted_independent_increment past hfuture hadapted
  exact ⟨elementary_integral_memLp hlaw hindep hcoeff,
    elementary_integral_mean_zero hlaw hindep hcoeff,
    elementary_integral_isometry hlaw hindep hcoeff⟩

/-- Concrete Gaussian models satisfy the increment hypotheses for every variance. -/
theorem gaussian_increment_model (c : ℝ) (v : ℝ≥0) :
    HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) (gaussianReal 0 v) ∧
      IndepFun (fun _ : ℝ ↦ c) id (gaussianReal 0 v) ∧
      MemLp (fun _ : ℝ ↦ c) 2 (gaussianReal 0 v) :=
  ⟨HasLaw.id, indepFun_const_left c id, memLp_const c⟩

end LinearStochastic.StochasticFoundation
