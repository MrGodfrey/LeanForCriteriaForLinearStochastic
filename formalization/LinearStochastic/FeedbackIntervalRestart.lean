module

public import LinearStochastic.FeedbackIntervalData
public import LinearStochastic.CommonShiftRepresentation

@[expose] public section

/-! Genuine deterministic restart of constant matrix feedback on the original
probability space, with the full original F_a measurable initial value. -/
noncomputable section
namespace LinearStochastic.FeedbackIntervalRestart
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonTimeShift FeedbackIntervalData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

def Initial (a : ℝ≥0) := {ξ : Ω → EuclideanSpace ℝ (Fin n) //
  StronglyMeasurable[𝓕 a] ξ ∧ MemLp ξ 2 μ}

theorem exists_shifted (i₀ : Fin m)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (a δ : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (hneg : (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef)
    (ξ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) a) :
    Nonempty (Data (𝓕:=filtration 𝓕 a) (fun i => (hW i).shift a)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ ρ A B C D P U hP ξ.val) := by
  apply FeedbackIntervalData.exists_data (fun i => (hW i).shift a)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) i₀
    (CommonShiftRepresentation.pair_shift hpair a) (CommonShiftRepresentation.channels_shift hchannels a)
    δ ρ hρ A B C D P U hP hneg ξ.val ξ.property.2
  change StronglyMeasurable[𝓕 (a+0)] ξ.val
  convert ξ.property.1 using 1
  simp

def chooseInterval (i₀ : Fin m)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (a δ : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (hneg : (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef)
    (ξ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) a) :
    Data (𝓕:=filtration 𝓕 a) (fun i => (hW i).shift a)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ ρ A B C D P U hP ξ.val :=
  Classical.choice (exists_shifted hW hWm i₀ hpair hchannels a δ ρ hρ A B C D P U hP hneg ξ)

omit [𝓕.IsComplete μ] in
def nextInitial (a δ t : ℝ≥0) (ht : a+δ=t) (ρ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ) (hP : P.PosDef)
    (ξ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) a)
    (q : Data (𝓕:=filtration 𝓕 a) (fun i => (hW i).shift a)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ ρ A B C D P U hP ξ.val) :
    Initial (μ:=μ) (𝓕:=𝓕) (n:=n) t := by
  refine ⟨q.path δ,?_,FeedbackIntervalData.terminal_memLp _ _ δ ρ A B C D P U hP ξ.val ξ.property.2 q⟩
  have h := q.progressive.stronglyAdapted δ
  change StronglyMeasurable[𝓕 (a+δ)] (q.path δ) at h
  rwa [ht] at h

end LinearStochastic.FeedbackIntervalRestart
