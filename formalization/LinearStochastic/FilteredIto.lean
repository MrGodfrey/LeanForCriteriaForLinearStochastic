module

public import LinearStochastic.StochasticFoundation
public import Mathlib.Probability.Process.Filtration

@[expose] public section

/-!
The finite adapted-increment integral for an arbitrary common filtration.
No natural-filtration factorization, Itô isometry, or SDE existence is assumed.
The hypotheses are only adaptation, independent future Gaussian increments,
and L² coefficients. This is a discrete construction, not yet its L² closure.
-/
namespace LinearStochastic.FilteredIto
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open StochasticFoundation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]
  (𝓕 : Filtration ℕ mΩ)
  (φ Δ : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
  (hφ : ∀ k, Measurable[𝓕 k] (φ k))
  (hΔ : ∀ k, Measurable[𝓕 (k+1)] (Δ k))
  (hlaw : ∀ k, HasLaw (Δ k) (gaussianReal 0 (v k)) P)
  (hindep : ∀ k, Indep (𝓕 k) (MeasurableSpace.comap (Δ k) inferInstance) P)
  (hLp : ∀ k, MemLp (φ k) 2 P)

/-- Actual finite increment sum, with random adapted coefficients. -/
def integral (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, φ k ω * Δ k ω

include hφ hΔ hlaw hindep hLp

omit [IsProbabilityMeasure P] hΔ in
theorem step_memLp (k : ℕ) : MemLp (fun ω ↦ φ k ω * Δ k ω) 2 P := by
  exact elementary_integral_memLp (hlaw k)
    (adapted_independent_increment (𝓕 k) (hindep k) (hφ k)) (hLp k)

omit [IsProbabilityMeasure P] hΔ in
theorem step_mean_zero (k : ℕ) : (∫ ω, φ k ω * Δ k ω ∂P) = 0 := by
  exact elementary_integral_mean_zero (hlaw k)
    (adapted_independent_increment (𝓕 k) (hindep k) (hφ k)) (hLp k)

omit [IsProbabilityMeasure P] hΔ in
theorem step_isometry (k : ℕ) :
    (∫ ω, (φ k ω * Δ k ω) ^ 2 ∂P) = (∫ ω, φ k ω ^ 2 ∂P) * v k := by
  exact elementary_integral_isometry (hlaw k)
    (adapted_independent_increment (𝓕 k) (hindep k) (hφ k)) (hLp k)

omit [IsProbabilityMeasure P] hLp in
/-- Cross-time terms vanish because the earlier coefficient and increment
are in the past of the later increment. -/
theorem cross_integral_zero {i j : ℕ} (hij : i < j) :
    (∫ ω, (φ i ω * Δ i ω) * (φ j ω * Δ j ω) ∂P) = 0 := by
  have hp : Measurable[𝓕 j] (fun ω ↦ (φ i ω * Δ i ω) * φ j ω) :=
    ((hφ i).mono (𝓕.mono hij.le) le_rfl).mul
      ((hΔ i).mono (𝓕.mono (Nat.succ_le_iff.mpr hij)) le_rfl) |>.mul (hφ j)
  have hi := adapted_independent_increment (𝓕 j) (hindep j) hp
  have hp' := hp.mono (𝓕.le j) le_rfl
  calc
    (∫ ω, (φ i ω * Δ i ω) * (φ j ω * Δ j ω) ∂P) =
        ∫ ω, ((φ i ω * Δ i ω) * φ j ω) * Δ j ω ∂P := by
          congr 1; funext ω; ring
    _ = (∫ ω, (φ i ω * Δ i ω) * φ j ω ∂P) * (∫ ω, Δ j ω ∂P) :=
      hi.integral_fun_mul_eq_mul_integral hp'.aestronglyMeasurable
        (gaussian_increment_memLp (hlaw j)).aestronglyMeasurable
    _ = 0 := by rw [gaussian_increment_mean (hlaw j), mul_zero]

omit [IsProbabilityMeasure P] hΔ in
theorem integral_memLp (n : ℕ) : MemLp (integral φ Δ n) 2 P := by
  exact memLp_finsetSum _ (fun k _ ↦ step_memLp 𝓕 φ Δ v hφ hlaw hindep hLp k)

omit hΔ in
theorem integral_mean_zero (n : ℕ) : (∫ ω, integral φ Δ n ω ∂P) = 0 := by
  change (∫ ω, ∑ k ∈ Finset.range n, φ k ω * Δ k ω ∂P) = 0
  rw [integral_finsetSum _ (fun k _ ↦
    (step_memLp 𝓕 φ Δ v hφ hlaw hindep hLp k).integrable (by norm_num))]
  simp only [step_mean_zero 𝓕 φ Δ v hφ hlaw hindep hLp, Finset.sum_const_zero]

omit [IsProbabilityMeasure P] hLp in
/-- Cross-time orthogonality, without a chosen ordering of the two terms. -/
theorem cross_integral_zero_of_ne {i j : ℕ} (hij : i ≠ j) :
    (∫ ω, (φ i ω * Δ i ω) * (φ j ω * Δ j ω) ∂P) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact cross_integral_zero 𝓕 φ Δ v hφ hΔ hlaw hindep h
  · simpa only [mul_comm] using cross_integral_zero 𝓕 φ Δ v hφ hΔ hlaw hindep h

omit [IsProbabilityMeasure P] in
/-- Finite adapted Itô isometry for any common filtration. -/
theorem integral_isometry (n : ℕ) :
    (∫ ω, (integral φ Δ n ω) ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (∫ ω, φ k ω ^ 2 ∂P) * v k := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ φ k ω * Δ k ω
  have hf (k : ℕ) : MemLp (f k) 2 P := step_memLp 𝓕 φ Δ v hφ hlaw hindep hLp k
  have hmul (i j : ℕ) : Integrable (fun ω ↦ f i ω * f j ω) P :=
    (hf i).integrable_mul (hf j)
  have he (ω : Ω) : (integral φ Δ n ω) ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f i ω * f j ω := by
    simp only [integral, pow_two, Finset.sum_mul_sum, f]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hmul i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ ↦ hmul i j), Finset.sum_eq_single i]
  · simpa only [f, ← pow_two] using step_isometry 𝓕 φ Δ v hφ hlaw hindep hLp i
  · intro j hj hji
    exact cross_integral_zero_of_ne 𝓕 φ Δ v hφ hΔ hlaw hindep (Ne.symm hji)
  · exact fun h ↦ (h hi).elim

end LinearStochastic.FilteredIto

namespace LinearStochastic.FilteredIto
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open StochasticFoundation

section Channels
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  (past : MeasurableSpace Ω) (φ Δ : ι → Ω → ℝ)
  (hφ : ∀ i, Measurable[past] (φ i))
  (hfuture : Indep past
    (MeasurableSpace.comap (fun ω i ↦ Δ i ω) inferInstance) P)

include hφ hfuture
/-- The coefficient may depend on the entire common past, not only channel i. -/
theorem joint_indep_scalar (i : ι) : IndepFun (φ i) (Δ i) P := by
  letI : MeasurableSpace Ω := mΩ
  have hi : Measurable[MeasurableSpace.comap (fun ω i ↦ Δ i ω) inferInstance] (Δ i) :=
    (measurable_pi_apply i).comp (comap_measurable (fun ω i ↦ Δ i ω))
  change Indep (MeasurableSpace.comap (φ i) inferInstance)
    (MeasurableSpace.comap (Δ i) inferInstance) P
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hfuture (measurable_iff_comap_le.mp (hφ i)))
    (measurable_iff_comap_le.mp hi)

variable (v : ι → ℝ≥0)
  (hlaw : ∀ i, HasLaw (Δ i) (gaussianReal 0 (v i)) P)
  (hLp : ∀ i, MemLp (φ i) 2 P)
  (hpair : Pairwise (fun i j ↦ IndepFun (Δ i) (Δ j) P))
include hlaw hLp hpair

/-- Joint independence from the past and independent centered channels imply
zero cross-channel energy for arbitrary common-past random coefficients. -/
theorem channel_cross_zero {i j : ι} (hij : i ≠ j) :
    (∫ ω, (φ i ω * Δ i ω) * (φ j ω * Δ j ω) ∂P) = 0 := by
  letI : MeasurableSpace Ω := mΩ
  have hcoeff : Measurable[past] (fun ω ↦ φ i ω * φ j ω) := (hφ i).mul (hφ j)
  have hi : Measurable[MeasurableSpace.comap (fun ω i ↦ Δ i ω) inferInstance] (Δ i) :=
    (measurable_pi_apply i).comp (comap_measurable (fun ω i ↦ Δ i ω))
  have hj : Measurable[MeasurableSpace.comap (fun ω i ↦ Δ i ω) inferInstance] (Δ j) :=
    (measurable_pi_apply j).comp (comap_measurable (fun ω i ↦ Δ i ω))
  have hprod : IndepFun (fun ω ↦ φ i ω * φ j ω) (fun ω ↦ Δ i ω * Δ j ω) P :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hfuture (measurable_iff_comap_le.mp hcoeff))
      (measurable_iff_comap_le.mp (hi.mul hj))
  have hnoise : (∫ ω, Δ i ω * Δ j ω ∂P) = 0 := by
    rw [(hpair hij).integral_fun_mul_eq_mul_integral
      (gaussian_increment_memLp (hlaw i)).aestronglyMeasurable (gaussian_increment_memLp (hlaw j)).aestronglyMeasurable,
      gaussian_increment_mean (hlaw i), zero_mul]
  calc
    (∫ ω, (φ i ω * Δ i ω) * (φ j ω * Δ j ω) ∂P) =
        ∫ ω, (φ i ω * φ j ω) * (Δ i ω * Δ j ω) ∂P := by
          congr 1; funext ω; ring
    _ = (∫ ω, φ i ω * φ j ω ∂P) * (∫ ω, Δ i ω * Δ j ω ∂P) :=
      hprod.integral_fun_mul_eq_mul_integral ((hLp i).aestronglyMeasurable.mul (hLp j).aestronglyMeasurable)
        ((gaussian_increment_memLp (hlaw i)).aestronglyMeasurable.mul (gaussian_increment_memLp (hlaw j)).aestronglyMeasurable)
    _ = 0 := by rw [hnoise, mul_zero]

variable [Fintype ι]
omit hpair in
/-- The true finite multichannel integral is L² for jointly adapted controls. -/
theorem channel_sum_memLp :
    MemLp (fun ω ↦ ∑ i, φ i ω * Δ i ω) 2 P := by
  letI : MeasurableSpace Ω := mΩ
  exact memLp_finsetSum _ (fun i _ ↦ elementary_integral_memLp (hlaw i)
    (joint_indep_scalar past φ Δ hφ hfuture i) (hLp i))

/-- Multichannel Itô isometry from joint-past independence, with no assumption
that the random coefficient is measurable for each channel's own natural filtration. -/
theorem channel_sum_isometry :
    (∫ ω, (∑ i, φ i ω * Δ i ω) ^ 2 ∂P) =
      ∑ i, (∫ ω, φ i ω ^ 2 ∂P) * v i := by
  letI : MeasurableSpace Ω := mΩ
  let f : ι → Ω → ℝ := fun i ω ↦ φ i ω * Δ i ω
  have hf (i : ι) : MemLp (f i) 2 P := elementary_integral_memLp (hlaw i)
    (joint_indep_scalar past φ Δ hφ hfuture i) (hLp i)
  have hmul (i j : ι) : Integrable (fun ω ↦ f i ω * f j ω) P :=
    (hf i).integrable_mul (hf j)
  have he (ω : Ω) : (∑ i, φ i ω * Δ i ω) ^ 2 =
      ∑ i, ∑ j, f i ω * f j ω := by
    simp only [pow_two, Finset.sum_mul_sum, f]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hmul i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ ↦ hmul i j), Finset.sum_eq_single i]
  · simpa only [f, ← pow_two] using elementary_integral_isometry (hlaw i)
      (joint_indep_scalar past φ Δ hφ hfuture i) (hLp i)
  · intro j hj hji
    exact channel_cross_zero past φ Δ hφ hfuture v hlaw hLp hpair (Ne.symm hji)
  · simp

end Channels
end LinearStochastic.FilteredIto

namespace LinearStochastic.FilteredIto.Multichannel
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open LinearStochastic.StochasticFoundation

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  (𝓕 : Filtration ℕ mΩ) (φ Δ : ℕ → ι → Ω → ℝ) (v : ℕ → ι → ℝ≥0)
  (hφ : ∀ k i, Measurable[𝓕 k] (φ k i))
  (hΔ : ∀ k i, Measurable[𝓕 (k+1)] (Δ k i))
  (hlaw : ∀ k i, HasLaw (Δ k i) (gaussianReal 0 (v k i)) P)
  (hfuture : ∀ k, Indep (𝓕 k)
    (MeasurableSpace.comap (fun ω i ↦ Δ k i ω) inferInstance) P)
include hφ hΔ hlaw hfuture

theorem cross_time_zero {k l : ℕ} (hkl : k < l) (i j : ι) :
    (∫ ω, (φ k i ω * Δ k i ω) * (φ l j ω * Δ l j ω) ∂P) = 0 := by
  have hp : Measurable[𝓕 l] (fun ω ↦ (φ k i ω * Δ k i ω) * φ l j ω) :=
    ((hφ k i).mono (𝓕.mono hkl.le) le_rfl).mul
      ((hΔ k i).mono (𝓕.mono (Nat.succ_le_iff.mpr hkl)) le_rfl) |>.mul (hφ l j)
  have hi := joint_indep_scalar (𝓕 l)
    (fun _ : ι ↦ fun ω ↦ (φ k i ω * Δ k i ω) * φ l j ω)
    (Δ l) (fun _ ↦ hp) (hfuture l) j
  have hp' := hp.mono (𝓕.le l) le_rfl
  calc
    (∫ ω, (φ k i ω * Δ k i ω) * (φ l j ω * Δ l j ω) ∂P) =
        ∫ ω, ((φ k i ω * Δ k i ω) * φ l j ω) * Δ l j ω ∂P := by
          congr 1; funext ω; ring
    _ = (∫ ω, (φ k i ω * Δ k i ω) * φ l j ω ∂P) * (∫ ω, Δ l j ω ∂P) :=
      hi.integral_fun_mul_eq_mul_integral hp'.aestronglyMeasurable
        (gaussian_increment_memLp (hlaw l j)).aestronglyMeasurable
    _ = 0 := by rw [gaussian_increment_mean (hlaw l j), mul_zero]

variable (hLp : ∀ k i, MemLp (φ k i) 2 P)
  (hpair : ∀ k, Pairwise (fun i j ↦ IndepFun (Δ k i) (Δ k j) P))
include hLp hpair

/-- Every distinct time-channel pair is orthogonal; both kinds of cross term
are proved from the joint filtration assumptions. -/
theorem cross_pair_zero {n : ℕ} {a b : Fin n × ι} (hab : a ≠ b) :
    (∫ ω, (φ a.1 a.2 ω * Δ a.1 a.2 ω) * (φ b.1 b.2 ω * Δ b.1 b.2 ω) ∂P) = 0 := by
  rcases a with ⟨k,i⟩
  rcases b with ⟨l,j⟩
  rcases lt_trichotomy (k : ℕ) (l : ℕ) with hkl | heq | hlk
  · exact cross_time_zero 𝓕 φ Δ v hφ hΔ hlaw hfuture hkl i j
  · have hkl : k = l := Fin.ext heq
    subst l
    have hij : i ≠ j := by
      intro hij
      exact hab (Prod.ext rfl hij)
    exact channel_cross_zero (𝓕 k) (φ k) (Δ k) (hφ k) (hfuture k)
      (v k) (hlaw k) (hLp k) (hpair k) hij
  · simpa only [mul_comm] using cross_time_zero 𝓕 φ Δ v hφ hΔ hlaw hfuture hlk j i

variable [Fintype ι]

/-- The concrete discrete stochastic integral over n time intervals and all channels. -/
def sumIntegral (n : ℕ) (ω : Ω) : ℝ := ∑ k : Fin n, ∑ i, φ k i ω * Δ k i ω

omit hΔ hpair in
/-- The actual finite joint-filtration integral lies in L². -/
theorem sumIntegral_memLp (n : ℕ) : MemLp (sumIntegral φ Δ n) 2 P := by
  exact memLp_finsetSum _ (fun k _ ↦ channel_sum_memLp (𝓕 k) (φ k) (Δ k)
    (hφ k) (hfuture k) (v k) (hlaw k) (hLp k))

/-- Multichannel finite-time Itô isometry under one common filtration.
The joint-past condition allows each coefficient to depend on every channel's history. -/
theorem sumIntegral_isometry (n : ℕ) :
    (∫ ω, (sumIntegral φ Δ n ω) ^ 2 ∂P) =
      ∑ k : Fin n, ∑ i, (∫ ω, φ k i ω ^ 2 ∂P) * v k i := by
  let f : Fin n × ι → Ω → ℝ := fun a ω ↦ φ a.1 a.2 ω * Δ a.1 a.2 ω
  have hf (a : Fin n × ι) : MemLp (f a) 2 P := elementary_integral_memLp (hlaw a.1 a.2)
    (joint_indep_scalar (𝓕 a.1) (φ a.1) (Δ a.1) (hφ a.1) (hfuture a.1) a.2) (hLp a.1 a.2)
  have hmul (a b : Fin n × ι) : Integrable (fun ω ↦ f a ω * f b ω) P :=
    (hf a).integrable_mul (hf b)
  have he (ω : Ω) : (sumIntegral φ Δ n ω) ^ 2 =
      ∑ a : Fin n × ι, ∑ b : Fin n × ι, f a ω * f b ω := by
    rw [sumIntegral, ← Fintype.sum_prod_type']
    simp only [pow_two, Finset.sum_mul_sum, f]
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦ hmul a b)),
    ← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum _ (fun b _ ↦ hmul a b), Finset.sum_eq_single a]
  · simpa only [f, ← pow_two] using elementary_integral_isometry (hlaw a.1 a.2)
      (joint_indep_scalar (𝓕 a.1) (φ a.1) (Δ a.1) (hφ a.1) (hfuture a.1) a.2) (hLp a.1 a.2)
  · intro b hb hba
    exact cross_pair_zero 𝓕 φ Δ v hφ hΔ hlaw hfuture hLp hpair (Ne.symm hba)
  · simp

variable [IsProbabilityMeasure P]

omit hΔ hpair in
/-- The finite multichannel stochastic integral has mean zero. -/
theorem sumIntegral_mean_zero (n : ℕ) :
    (∫ ω, sumIntegral φ Δ n ω ∂P) = 0 := by
  have hf (k : ℕ) (i : ι) : MemLp (fun ω ↦ φ k i ω * Δ k i ω) 2 P :=
    elementary_integral_memLp (hlaw k i)
      (joint_indep_scalar (𝓕 k) (φ k) (Δ k) (hφ k) (hfuture k) i) (hLp k i)
  change (∫ ω, ∑ k : Fin n, ∑ i, φ k i ω * Δ k i ω ∂P) = 0
  rw [integral_finsetSum _ (fun (k : Fin n) _ ↦ (channel_sum_memLp (𝓕 k) (φ k) (Δ k)
    (hφ k) (hfuture k) (v k) (hlaw k) (hLp k)).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_finsetSum _ (fun i _ ↦ (hf k i).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro i _
  exact elementary_integral_mean_zero (hlaw k i)
    (joint_indep_scalar (𝓕 k) (φ k) (Δ k) (hφ k) (hfuture k) i) (hLp k i)

end LinearStochastic.FilteredIto.Multichannel
