import LinearStochastic.CommonDriftS2
import LinearStochastic.CommonLocalSolution

/-! The actual matrix coefficient processes of the constructed local solution.
Both the state and ordinary progressive controls are retained under the ambient
space-time measure. Drift identities hold on one common probability-one set;
no joint measurability is inferred merely from fixed-time modifications. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonLocalCoefficients
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
open CommonVectorPicard CommonItoMultichannel CommonItoCLM CommonItoL2 CommonLocalSolution
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- The continuous matrix action represents its literal finite row sums. -/
theorem matrixAction_ae {κ ν : Type*} [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ ν ℝ) (X : ν → H2 𝓕 μ T) (a : κ) :
    matrixAction T A X a =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ ∑ b, A a b * X b z := by
  rw [matrixAction_apply]
  have hmul : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, ∀ b, (A a b • X b) z = A a b * X b z := by
    rw [ae_all_iff]
    intro b
    exact Lp.coeFn_smul (A a b) (X b)
  apply ae_of_ae_trim 𝓕.predictable_le_prod
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun b ↦ A a b • X b),hmul] with z hs hm
  rw [hs]
  exact Finset.sum_congr rfl fun b _ ↦ hm b

omit [IsProbabilityMeasure μ] in
/-- Actual ambient space-time equality of the controlled linear coefficients. -/
theorem linearInput_ae {κ ν : Type*} [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (X : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T)
    (R : κ → ℝ≥0 → Ω → ℝ) (v : ν → ℝ≥0 → Ω → ℝ)
    (hX : ∀ a, (X a : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (R a))
    (hu : ∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b)) (a : κ) :
    (matrixAction T A X a + matrixAction T B u a : H2 𝓕 μ T) =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ (∑ b, A a b * R b z.1 z.2) + ∑ b, B a b * v b z.1 z.2 := by
  have hx : ∀ᵐ z ∂(timeMeasure_T T).prod μ, ∀ b, X b z = R b z.1 z.2 := by
    rw [ae_all_iff]; exact hX
  have hv : ∀ᵐ z ∂(timeMeasure_T T).prod μ, ∀ b, u b z = v b z.1 z.2 := by
    rw [ae_all_iff]; exact hu
  have hadd := ae_of_ae_trim 𝓕.predictable_le_prod
    (Lp.coeFn_add (matrixAction T A X a) (matrixAction T B u a))
  filter_upwards [matrixAction_ae T A X a,matrixAction_ae T B u a,hadd,hx,hv] with z hA hB hs hx hv
  rw [hs,Pi.add_apply,hA,hB]
  congr 1
  · exact Finset.sum_congr rfl fun b _ ↦ congrArg (fun q : ℝ ↦ A a b * q) (hx b)
  · exact Finset.sum_congr rfl fun b _ ↦ congrArg (fun q : ℝ ↦ B a b * q) (hv b)

/-- Product-a.e. equality gives one probability-one set on which the actual
Lebesgue primitives agree at every time in the horizon. -/
theorem primitive_congr_spacetime (T : ℝ≥0) {f g : ℝ≥0 → Ω → ℝ}
    (h : Function.uncurry f =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry g) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      (∫ s in Ioc (0 : ℝ≥0) t, f s ω ∂timeMeasure) =
        ∫ s in Ioc (0 : ℝ≥0) t, g s ω ∂timeMeasure := by
  have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae h)
  filter_upwards [hs] with ω hω
  intro t ht
  apply integral_congr_ae
  exact (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht) le_rfl)) hω

section Solution
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Every actual diffusion class is the literal C_i Y + D_i v of the
constructed state representative and original progressive control. -/
theorem noiseInput_actual (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : picardMap hW hWm hWc i₀ T A B C D
      (fun a ↦ CommonInitialPredictable.initialH2 (hξ a) (hξ2 a) T) u X = X)
    (v : ν → ℝ≥0 → Ω → ℝ)
    (hu : ∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b))
    (i : ι) (a : κ) :
    noiseInput T C D u X i a =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ (∑ b, C i a b * stateProcess hWm i₀ T A B C D ξ u X b z.1 z.2) +
        ∑ b, D i a b * v b z.1 z.2 := by
  exact linearInput_ae T (C i) (D i) X u _ v
    (fun b ↦ ae_of_ae_trim 𝓕.predictable_le_prod
      (fixedPoint_state_ae hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X hX b)) hu a

/-- The actual local matrix SDE equation on a single probability-one set.
The noise is the constructed continuous Itô integral of the preceding actual
coefficient classes; the drift is the literal raw-state Lebesgue integral. -/
theorem state_raw_integral_equation (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : picardMap hW hWm hWc i₀ T A B C D
      (fun a ↦ CommonInitialPredictable.initialH2 (hξ a) (hξ2 a) T) u X = X)
    (v : ν → ℝ≥0 → Ω → ℝ)
    (hu : ∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b)) :
    ∀ᵐ ω ∂μ, ∀ a t, t ≤ T → stateProcess hWm i₀ T A B C D ξ u X a t ω =
      ξ a ω + (∫ s in Ioc (0 : ℝ≥0) t,
        ((∑ b, A a b * stateProcess hWm i₀ T A B C D ξ u X b s ω) +
          ∑ b, B a b * v b s ω) ∂timeMeasure) +
      ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (noiseInput T C D u X i a) t ω := by
  rw [ae_all_iff]
  intro a
  have hin := linearInput_ae T A B X u (stateProcess hWm i₀ T A B C D ξ u X) v
    (fun b ↦ ae_of_ae_trim 𝓕.predictable_le_prod
      (fixedPoint_state_ae hW hWm hWc i₀ T A B C D ξ hξ hξ2 u X hX b)) hu a
  have hi := primitive_congr_spacetime T
    (f := fun s ω ↦ driftInput T A B u X a (s,ω))
    (g := fun s ω ↦ (∑ b, A a b * stateProcess hWm i₀ T A B C D ξ u X b s ω) + ∑ b, B a b * v b s ω) hin
  have hd := CommonDriftS2.driftContinuousMod_indistinguishable T (hWm i₀) (driftInput T A B u X a)
  filter_upwards [hi,hd] with ω hi hd
  intro t ht
  change ξ a ω + CommonDriftPredictable.driftContinuousMod T (hWm i₀) (driftInput T A B u X a) t ω + _ = _
  rw [hd t ht]
  rw [hi t ht]
end Solution
end LinearStochastic.CommonLocalCoefficients
