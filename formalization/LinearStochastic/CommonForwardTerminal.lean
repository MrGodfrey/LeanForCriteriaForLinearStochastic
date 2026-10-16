import LinearStochastic.CommonForwardBounds

/-! Actual forward terminal random variables and quantitative bounds. The
terminal map is built from the genuine Bochner drift CLM and constructed Itô
operators, and then identified with the endpoint of an actual solution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonForwardTerminal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonPicardHorizon CommonLocalSolution CommonSolutionData CommonForwardBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- A uniform coefficient bound for genuine terminal integration. -/
def terminalBound (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ) : ℝ :=
  Real.sqrt (T:ℝ)*matrixSize A + ∑ i, matrixSize (C i)

theorem terminalBound_nonneg (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ) :
    0 ≤ terminalBound T A C :=
  add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (matrixSize_nonneg A))
    (Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C i))

/-- Actual drift and diffusion terminal contributions of a matrix input. -/
def dynamics (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ)
    (X : ν → H2 𝓕 μ T) : κ → Lp ℝ 2 μ := fun b ↦
  BSDETerminal.terminal 𝓕 T (matrixAction T A X b) +
    ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (matrixAction T (C i) X b)

theorem dynamics_sub (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ)
    (X Y : ν → H2 𝓕 μ T) :
    dynamics hW hWm T A C (X-Y) = dynamics hW hWm T A C X-dynamics hW hWm T A C Y := by
  funext b
  simp only [dynamics,map_sub,Pi.sub_apply,Finset.sum_sub_distrib]
  abel

/-- The bound comes from real terminal drift sqrt(T) and true Itô contraction. -/
theorem dynamics_norm (T : ℝ≥0) (A : Matrix κ ν ℝ) (C : ι → Matrix κ ν ℝ)
    (X : ν → H2 𝓕 μ T) : ‖dynamics hW hWm T A C X‖ ≤ terminalBound T A C*‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (terminalBound_nonneg T A C) (norm_nonneg _))).mpr
  intro b
  calc
    _ ≤ ‖BSDETerminal.terminal 𝓕 T (matrixAction T A X b)‖ +
        ‖∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (matrixAction T (C i) X b)‖ := norm_add_le _ _
    _ ≤ Real.sqrt (T:ℝ)*‖matrixAction T A X b‖ + ∑ i, ‖matrixAction T (C i) X b‖ :=
      add_le_add (BSDETerminal.terminal_norm 𝓕 T _)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
          CommonItoProcessGeneral.itoProcessCLM_norm_le (hW i) T T (hWm i) _))
    _ ≤ Real.sqrt (T:ℝ)*(matrixSize A*‖X‖) + ∑ i, matrixSize (C i)*‖X‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          ((norm_le_pi_norm (matrixAction T A X) b).trans (((matrixAction T A).le_opNorm X).trans
            (mul_le_mul_of_nonneg_right (matrixAction_norm_le T A) (norm_nonneg _)))) (Real.sqrt_nonneg _)
      · exact Finset.sum_le_sum fun i _ ↦
          (norm_le_pi_norm (matrixAction T (C i) X) b).trans (((matrixAction T (C i)).le_opNorm X).trans
            (mul_le_mul_of_nonneg_right (matrixAction_norm_le T (C i)) (norm_nonneg _)))
    _ = _ := by simp only [terminalBound,←Finset.sum_mul]; ring

/-- The literal actual terminal expression of a controlled forward equation. -/
def terminalValue (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → Lp ℝ 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) : κ → Lp ℝ 2 μ :=
  η + dynamics hW hWm T A C X + dynamics hW hWm T B D u

theorem terminalValue_coordinate (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → Lp ℝ 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (b : κ) :
    terminalValue hW hWm T A B C D η u X b = η b + BSDETerminal.terminal 𝓕 T (driftInput T A B u X b) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (noiseInput T C D u X i b) := by
  simp only [terminalValue,dynamics,driftInput,noiseInput,Pi.add_apply,map_add,Finset.sum_add_distrib]
  abel

/-- Actual endpoint continuity before using any fixed-point estimate. -/
theorem terminalValue_difference (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η θ : κ → Lp ℝ 2 μ) (u v : ν → H2 𝓕 μ T) (X Y : κ → H2 𝓕 μ T) :
    ‖terminalValue hW hWm T A B C D η u X-terminalValue hW hWm T A B C D θ v Y‖ ≤
      ‖η-θ‖+terminalBound T A C*‖X-Y‖+terminalBound T B D*‖u-v‖ := by
  have he : terminalValue hW hWm T A B C D η u X-terminalValue hW hWm T A B C D θ v Y =
      (η-θ)+dynamics hW hWm T A C (X-Y)+dynamics hW hWm T B D (u-v) := by
    simp only [terminalValue,dynamics_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add_right (dynamics_norm hW hWm T A C _) _))
    (dynamics_norm hW hWm T B D _))

/-- The true terminal expression is the actual raw Lebesgue/Itô expression. -/
theorem terminalValue_ae (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ2 : ∀ b, MemLp (ξ b) 2 μ)
    (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (b : κ) :
    terminalValue hW hWm T A B C D (fun b ↦ (hξ2 b).toLp (ξ b)) u X b =ᵐ[μ]
      fun ω ↦ ξ b ω + (∫ s in Ioc (0:ℝ≥0) T, driftInput T A B u X b (s,ω) ∂CommonItoL2.timeMeasure) +
        ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (noiseInput T C D u X i b) ω := by
  rw [terminalValue_coordinate]
  let J := fun i ↦ CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (noiseInput T C D u X i b)
  filter_upwards [Lp.coeFn_add ((hξ2 b).toLp (ξ b)+BSDETerminal.terminal 𝓕 T (driftInput T A B u X b)) (∑ i, J i),
    Lp.coeFn_add ((hξ2 b).toLp (ξ b)) (BSDETerminal.terminal 𝓕 T (driftInput T A B u X b)),
    (hξ2 b).coeFn_toLp,BSDETerminal.terminal_ae 𝓕 T (driftInput T A B u X b),
    Lp.coeFn_fun_finsetSum Finset.univ J] with ω hsum hadd hi hd hs
  rw [hsum,Pi.add_apply,hadd,Pi.add_apply,hi,hd,hs]
  rfl

/-- Identification with the genuine endpoint of any actual solution. -/
theorem solution_terminal (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (b : κ) :
    (endpoint_memLp hW hWm T A B C D ξ u q b).2.toLp (q.path b T) =
      terminalValue hW hWm T A B C D (fun b ↦ (hξ2 b).toLp (ξ b)) u q.X b := by
  apply Lp.ext
  exact (endpoint_memLp hW hWm T A B C D ξ u q b).2.coeFn_toLp.trans
    ((q.equation b T le_rfl).trans (terminalValue_ae hW hWm T A B C D ξ hξ2 u q.X b).symm)

/-- The endpoint as its genuine probability-space L² class. -/
def endpoint (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u) : κ → Lp ℝ 2 μ :=
  fun b ↦ (endpoint_memLp hW hWm T A B C D ξ u q b).2.toLp (q.path b T)

theorem endpoint_eq (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) :
    endpoint hW hWm T A B C D ξ u q =
      terminalValue hW hWm T A B C D (fun b ↦ (hξ2 b).toLp (ξ b)) u q.X :=
  funext (solution_terminal hW hWm T A B C D ξ hξ2 u q)

/-- A concrete finite coefficient-only endpoint Lipschitz constant whenever
the actual uniform local contraction bound is less than one. -/
def localBound (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) : ℝ :=
  1+terminalBound T A C*((Real.sqrt (T:ℝ)+inputBound T B D)/(1-CommonUniformHorizon.bound T A C))+
    terminalBound T B D

theorem one_le_localBound (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hc : CommonUniformHorizon.bound T A C < 1) : 1 ≤ localBound T A B C D := by
  have hm : 0 ≤ terminalBound T A C*((Real.sqrt (T:ℝ)+inputBound T B D)/(1-CommonUniformHorizon.bound T A C)) :=
    mul_nonneg (terminalBound_nonneg T A C)
      (div_nonneg (add_nonneg (Real.sqrt_nonneg _) (inputBound_nonneg T B D)) (sub_pos.mpr hc).le)
  have hn := terminalBound_nonneg T B D
  unfold localBound
  linarith

/-- Genuine local terminal dependence for every actual solution. The right
side uses the actual random-initial L² classes and actual control H² norm. -/
theorem local_endpoint_difference
    (hWc : ∀ i ω, Continuous fun t ↦ W i t ω) (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ ζ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hζ : ∀ b, StronglyMeasurable[𝓕 0] (ζ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (hζ2 : ∀ b, MemLp (ζ b) 2 μ)
    (u v : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u)
    (r : Solution hW hWm T A B C D ζ v)
    (hc : CommonUniformHorizon.bound T A C < 1) :
    ‖endpoint hW hWm T A B C D ξ u q-endpoint hW hWm T A B C D ζ v r‖ ≤
      localBound T A B C D *
        (‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖+‖u-v‖) := by
  let I := ‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖
  let U := ‖u-v‖
  have hI : 0 ≤ I := norm_nonneg _
  have hU : 0 ≤ U := norm_nonneg _
  have hi := inputBound_nonneg T B D
  have hs := Real.sqrt_nonneg (T:ℝ)
  have hd := sub_pos.mpr hc
  have hratio : (Real.sqrt (T:ℝ)*I+inputBound T B D*U)/(1-CommonUniformHorizon.bound T A C) ≤
      ((Real.sqrt (T:ℝ)+inputBound T B D)/(1-CommonUniformHorizon.bound T A C))*(I+U) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith [mul_nonneg hs hU,mul_nonneg hi hI]
  have hstate := (CommonForwardBounds.solution_difference hW hWm hWc i₀ T A B C D
    ξ ζ hξ hζ hξ2 hζ2 u v q r hc).trans hratio
  rw [endpoint_eq hW hWm T A B C D ξ hξ2 u q,endpoint_eq hW hWm T A B C D ζ hζ2 v r]
  have ht := terminalValue_difference hW hWm T A B C D
    (fun b ↦ (hξ2 b).toLp (ξ b)) (fun b ↦ (hζ2 b).toLp (ζ b)) u v q.X r.X
  have hm := mul_le_mul_of_nonneg_left hstate (terminalBound_nonneg T A C)
  have hn := terminalBound_nonneg T B D
  change _ ≤ localBound T A B C D*(I+U)
  change _ ≤ I+terminalBound T A C*‖q.X-r.X‖+terminalBound T B D*U at ht
  unfold localBound
  nlinarith [mul_nonneg hn hI]

end LinearStochastic.CommonForwardTerminal
