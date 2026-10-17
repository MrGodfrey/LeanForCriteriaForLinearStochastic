module
public import PalomarBridge

public section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LinearStochastic.Palomar
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include hW hInd in
/-- Full stochastic controllability classification, with existence of the
standard Itô integrals proved as part of the result. The integral is specified
by its action on every bounded predictable step process, not by an opaque
controllability predicate. All four properties use ordinary progressive
controls and actual continuous S² solutions on the usual Brownian filtration. -/
theorem classification (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    ∃ I : Fin m → Lp ℝ 2 (spacetime (usual (μ := μ) W hWm) μ T) →L[ℝ] Lp ℝ 2 μ,
      (∀ i, IsIto (usual (μ := μ) W hWm) (W i) T (I i)) ∧
      (AC (usual (μ := μ) W hWm) T I A B C D ↔ flag A B C D n = {0}) ∧
      (ANC (usual (μ := μ) W hWm) T I A B C D ↔ flag A B C D n = {0}) ∧
      (ENC (usual (μ := μ) W hWm) T I A B C D ↔ flag A B C D n = {0}) ∧
      (EC (usual (μ := μ) W hWm) T I A B C D ↔
        flag A B C D n = {0} ∧ (stack D).rank = m*n) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (usual (μ := μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  letI : (usual (μ := μ) W hWm).IsComplete μ :=
    JointUsualNatural.usual_complete (μ := μ) W hWm
  refine ⟨integrals (𝓕 := usual (μ := μ) W hWm) hW hWm T,
    (fun i => original_isIto (𝓕 := usual (μ := μ) W hWm) (hW i).toIsPreBrownianReal (hWm i) T), ?_⟩
  have result := RawCompleteClassification.classification hW hWm hInd hn hm T hT A B C D
  simpa only [AC, ANC, ENC, EC, flag_zero_iff, stack_eq_original, reachApprox_iff_raw, reachExact_iff_raw,
    RawControlProperties.Approximate, RawControlProperties.ApproximateNull,
    RawExactProperties.ExactNull, RawExactProperties.Exact, matrixMap,
    ZeroObservationMatrices.matrixMap] using result

include hW hInd in
/-- The step-process characterization fixes the Itô integral uniquely.
Consequently the integral witnesses in classification cannot change the
meaning of any controllability predicate. -/
theorem ito_unique (T : ℝ≥0) (i : Fin m)
    (I J : Lp ℝ 2 (spacetime (usual (μ := μ) W hWm) μ T) →L[ℝ] Lp ℝ 2 μ)
    (hI : IsIto (usual (μ := μ) W hWm) (W i) T I)
    (hJ : IsIto (usual (μ := μ) W hWm) (W i) T J) : I = J := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (usual (μ := μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact isIto_unique (𝓕 := usual (μ := μ) W hWm) (hWm i) T I J hI hJ

end LinearStochastic.Palomar
