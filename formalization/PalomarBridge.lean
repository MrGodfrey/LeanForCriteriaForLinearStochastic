module
public import LinearStochastic.RawCompleteClassification
public import PalomarDefinitions

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.Palomar
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoL2
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- The independently specified step data gives the existing elementary process. -/
def Step.toSimple {T : ℝ≥0} (V : Step 𝓕 T) : SimpleProcess ℝ 𝓕 where
  valueBot := V.valueBot
  value := V.value
  le_of_mem_support_value := V.ordered
  measurable_valueBot := V.measurableBot
  measurable_value' := V.measurableValue
  bounded_valueBot := V.boundedBot
  bounded_value := V.boundedValue

/-- Every existing bounded elementary process has the independent description. -/
def stepOfSimple (hWm : ∀ t, Measurable (W t)) (T : ℝ≥0)
    (V : TBoundedSP (𝓕 := 𝓕) T hWm) : Step 𝓕 T where
  valueBot := V.val.valueBot
  value := V.val.value
  ordered := V.val.le_of_mem_support_value
  horizon := V.property
  measurableBot := V.val.measurable_valueBot
  measurableValue := V.val.measurable_value'
  boundedBot := V.val.bounded_valueBot
  boundedValue := V.val.bounded_value

variable [CommonItoIsometry.ForwardIndependent W 𝓕 μ]

/-- The constructed Itô map satisfies the independent, explicit increment formula. -/
theorem original_isIto (hW : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (T : ℝ≥0) :
    IsIto 𝓕 W T (itoIntegralCLM_T (𝓕 := 𝓕) hW T hWm) := by
  intro V
  let V' : TBoundedSP (𝓕 := 𝓕) T hWm := ⟨V.toSimple, V.horizon⟩
  refine ⟨simpleAssembly_T (𝓕 := 𝓕) T hWm V', ?_, ?_⟩
  · exact (memLp_uncurry_trim_T (𝓕 := 𝓕) T hWm V'.val).coeFn_toLp
  · have he := congrArg (fun f : Lp ℝ 2 μ => (f : Ω → ℝ))
      (itoIntegralCLM_T_simpleAssembly_T (𝓕 := 𝓕) hW T hWm V')
    exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun ω => congrFun he ω))
      (memLp_itoSimple hW hWm V'.val).coeFn_toLp

/-- Equality on the dense step processes uniquely fixes the continuous map. -/
theorem isIto_unique (hWm : ∀ t, Measurable (W t)) (T : ℝ≥0)
    (I J : Lp ℝ 2 (spacetime 𝓕 μ T) →L[ℝ] Lp ℝ 2 μ)
    (hI : IsIto 𝓕 W T I) (hJ : IsIto 𝓕 W T J) : I = J := by
  apply ContinuousLinearMap.ext
  intro f
  refine (simpleAssembly_T_denseRange (𝓕 := 𝓕) (μ := μ) T hWm).induction_on f
    (isClosed_eq I.continuous J.continuous) ?_
  intro V
  obtain ⟨fi, hfi, hii⟩ := hI (stepOfSimple hWm T V)
  obtain ⟨fj, hfj, hjj⟩ := hJ (stepOfSimple hWm T V)
  have hi : fi = simpleAssembly_T (𝓕 := 𝓕) T hWm V :=
    Lp.ext (hfi.trans (memLp_uncurry_trim_T (𝓕 := 𝓕) T hWm V.val).coeFn_toLp.symm)
  have hj : fj = simpleAssembly_T (𝓕 := 𝓕) T hWm V :=
    Lp.ext (hfj.trans (memLp_uncurry_trim_T (𝓕 := 𝓕) T hWm V.val).coeFn_toLp.symm)
  rw [hi] at hii
  rw [hj] at hjj
  exact Lp.ext (hii.trans hjj.symm)

section RawBridge
variable {n r m : ℕ} {Wm : Fin m → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (Wm i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (Wm i) μ) (hWm : ∀ i t, Measurable (Wm i t))
  (T : ℝ≥0) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

abbrev integrals := fun i => itoIntegralCLM_T (𝓕 := 𝓕) (hW i).toIsPreBrownianReal T (hWm i)

theorem controlled_iff_raw (v₀ : EuclideanSpace ℝ (Fin n)) (v R u X) :
    Controlled 𝓕 T (integrals (𝓕 := 𝓕) hW hWm T) A B C D v₀ v R u X ↔
    ProgressiveControlSection.RawSolution (𝓕 := 𝓕) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v₀)
      (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) v R u X := by
  constructor <;> intro q
  · exact ⟨q.control_progressive, q.control_memLp, q.progressive, q.continuous,
      q.squareSup, q.control_rep, q.state_rep, q.equation⟩
  · exact ⟨q.control_progressive, q.control_memLp, q.progressive, q.continuous,
      q.squareSup, q.control_rep, q.state_rep, q.equation⟩

variable [𝓕.IsComplete μ]

theorem reachApprox_iff_raw (v₀ : EuclideanSpace ℝ (Fin n)) (η : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) (ε : ℝ) :
    ReachApprox 𝓕 T (integrals (𝓕 := 𝓕) hW hWm T) A B C D v₀ η ε ↔
    RawControlProperties.Reach (𝓕 := 𝓕) (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T
      (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) v₀ η ε := by
  unfold ReachApprox RawControlProperties.Reach
  simp only [controlled_iff_raw]
  rfl

theorem reachExact_iff_raw (v₀ : EuclideanSpace ℝ (Fin n)) (η : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) :
    ReachExact 𝓕 T (integrals (𝓕 := 𝓕) hW hWm T) A B C D v₀ η ↔
    RawExactProperties.Reach (𝓕 := 𝓕) (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T
      (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) v₀ η := by
  unfold ReachExact RawExactProperties.Reach
  simp only [controlled_iff_raw]
  rfl

end RawBridge
end LinearStochastic.Palomar
