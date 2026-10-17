module

public import LinearStochastic.PaperControlProperties
public import LinearStochastic.AlgebraDeterministic

@[expose] public section

/-! The zero-noise stochastic system has the precise Kalman reduction for
AC, ANC and ENC, while arbitrary-random-target EC fails when n,m>0. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.StochasticDeterministicReduction
open MeasureTheory ProbabilityTheory
open scoped NNReal
open PaperControlProperties
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- The original n-step zero-noise flag test is exactly classical Kalman rank. -/
theorem flag_iff_kalman (_hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ) :
    (AdjointCoefficients.fromMatrices A B (fun _ : Fin m=>0) (fun _=>0)).flag n=⊥ ↔
      (Deterministic.kalman A B n).rank=n := by
  rw [Deterministic.kalman_rank_codimension (m:=m) A B n]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have hl := Submodule.finrank_le ((AdjointCoefficients.fromMatrices A B
      (fun _ : Fin m=>0) (fun _=>0)).flag n)
    have hn' : Module.finrank ℝ (Fin n→ℝ)=n := by simp
    rw [hn'] at hl
    apply Submodule.finrank_eq_zero.mp
    omega

/-- In the zero-diffusion system, each of AC, ANC and ENC is equivalent to
the true finite Kalman matrix being onto. -/
theorem null_properties_iff_kalman (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (p : Property) (hp : p≠.EC) :
    Holds hW hWm hInd p T A B (fun _ : Fin m=>0) (fun _=>0) ↔
      (Deterministic.kalman A B n).rank=n := by
  apply (holds_iff hW hWm hInd hn hm T hT A B (fun _=>0) (fun _=>0) p).trans
  cases p with
  | EC=>exact (hp rfl).elim
  | AC=>exact flag_iff_kalman hn A B
  | ENC=>exact flag_iff_kalman hn A B
  | ANC=>exact flag_iff_kalman hn A B

/-- Positive-dimensional random terminal targets cannot all be reached with
zero controlled diffusion, even when Kalman rank is full. -/
theorem not_exact (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ) :
    ¬Holds hW hWm hInd .EC T A B (fun _ : Fin m=>0) (fun _=>0) := by
  intro h
  have hh := (holds_iff hW hWm hInd hn hm T hT A B (fun _=>0) (fun _=>0) .EC).mp h
  have hz : (SurjectiveMatrices.stack (fun _ : Fin m=>(0 : Matrix (Fin n) (Fin r) ℝ))).rank=0 := by
    change (0 : Matrix (Fin m×Fin n) (Fin r) ℝ).rank=0
    exact Matrix.rank_zero
  have he := hh.2
  rw [hz] at he
  exact (Nat.mul_pos hm hn).ne' he.symm

end LinearStochastic.StochasticDeterministicReduction
