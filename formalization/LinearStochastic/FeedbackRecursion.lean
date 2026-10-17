module

public import LinearStochastic.FeedbackIntervalRestart

@[expose] public section

/-! Countably many genuine feedback solutions are recursively constructed on
the same probability space, retaining the original past at every restart.
No sequence of solutions or contraction estimate is assumed as input. -/
noncomputable section
namespace LinearStochastic.FeedbackRecursion
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonTimeShift FeedbackIntervalData FeedbackIntervalRestart
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : Fin m)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
  (a δ : ℕ → ℝ≥0) (ht : ∀ j, a j+δ j=a (j+1))
  (ρ : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
  (P : ℕ → Matrix (Fin n) (Fin n) ℝ) (U : ℕ → Matrix (Fin r) (Fin n) ℝ)
  (hP : ∀ j, (P j).PosDef)
  (hneg : ∀ j, (-LMIMatrixCoordinates.matrixLMI A B C D (ρ j) (P j) (U j)).PosDef)
  (ξ₀ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (a 0))

local instance shiftedForwardFamily (s : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (s+t) ω-W i s ω)
      (filtration 𝓕 s) μ := fun _ => CommonTimeShift.forwardIndependent s

/-- The next initial state is the actual endpoint of the actual chosen solution. -/
def step (j : ℕ) (ξ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (a j)) :
    Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (a (j+1)) :=
  nextInitial hW hWm (a j) (δ j) (a (j+1)) (ht j) (ρ j) A B C D (P j) (U j) (hP j) ξ
    (chooseInterval hW hWm i₀ hpair hchannels (a j) (δ j) (ρ j) (hρ j)
      A B C D (P j) (U j) (hP j) (hneg j) ξ)

/-- Actual measurable L² states at all switching times, built by recursion. -/
def states : (j : ℕ) → Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (a j)
  | 0 => ξ₀
  | j+1 => step hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg j
      (states j)

/-- The actual solution on interval j, started from the recursively constructed state. -/
def segment (j : ℕ) :
    Data (𝓕:=filtration 𝓕 (a j)) (fun i => (hW i).shift (a j))
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) (a j))
      (δ j) (ρ j) A B C D (P j) (U j) (hP j)
      (states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ j).val :=
  chooseInterval hW hWm i₀ hpair hchannels (a j) (δ j) (ρ j) (hρ j)
    A B C D (P j) (U j) (hP j) (hneg j)
    (states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ j)

theorem states_zero : states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ 0 = ξ₀ := rfl

theorem states_next (j : ℕ) :
    (states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ (j+1)).val =
    (segment hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ j).path (δ j) := rfl

/-- The recursion's moment contraction is proved from the constructed SDE solution. -/
theorem moment_step (j : ℕ) :
    (∫ ω, ‖(states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ (j+1)).val ω‖^2 ∂μ) ≤
    MatrixGrowthBounds.conditionNumber (P j) (hP j).isHermitian * Real.exp (-ρ j*(δ j:ℝ)) *
    (∫ ω, ‖(states hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ j).val ω‖^2 ∂μ) := by
  rw [states_next]
  exact (segment hW hWm i₀ hpair hchannels a δ ht ρ hρ A B C D P U hP hneg ξ₀ j).decay (δ j) le_rfl

end LinearStochastic.FeedbackRecursion
