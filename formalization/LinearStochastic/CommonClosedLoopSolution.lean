module

public import LinearStochastic.CommonBrownianGlobal

@[expose] public section

/-! Genuine solution transport from a constant state feedback to the actual
constant closed-loop coefficients. The control relation is an L² equality. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonClosedLoopSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ ν η : Type*} [Fintype κ] [Fintype ν] [Fintype η]

omit [IsProbabilityMeasure μ] in
theorem matrixAction_add (T : ℝ≥0) (A B : Matrix κ ν ℝ) (X : ν → H2 𝓕 μ T) :
    matrixAction T (A+B) X = matrixAction T A X+matrixAction T B X := by
  funext a
  simp only [matrixAction_apply,Matrix.add_apply,add_smul,Finset.sum_add_distrib,Pi.add_apply]

omit [IsProbabilityMeasure μ] in
theorem matrixAction_mul (T : ℝ≥0) (A : Matrix κ ν ℝ) (B : Matrix ν η ℝ) (X : η → H2 𝓕 μ T) :
    matrixAction T (A*B) X = matrixAction T A (matrixAction T B X) := by
  funext a
  simp only [matrixAction_apply,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

omit [IsProbabilityMeasure μ] in
theorem matrixAction_zero (T : ℝ≥0) (X : ν → H2 𝓕 μ T) : matrixAction T (0 : Matrix κ ν ℝ) X = 0 := by
  funext a
  simp only [matrixAction_apply,Matrix.zero_apply,zero_smul,Finset.sum_const_zero,Pi.zero_apply]

omit [IsProbabilityMeasure μ] in
theorem closed_loop_input (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (G : Matrix ν κ ℝ)
    (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (hu : u = matrixAction T G X) :
    driftInput T A B u X = driftInput T (A+B*G) (0 : Matrix κ ν ℝ) 0 X := by
  simp only [driftInput,hu,matrixAction_add,matrixAction_mul,matrixAction_zero,add_zero]

variable {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- All actual paths, H² classes and integral identities are retained; only
the already proved equal coefficients are rewritten into closed-loop form. -/
def closeLoop (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) (G : Matrix ν κ ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (hu : u = matrixAction T G q.X) :
    Solution (𝓕:=𝓕) hW hWm T (A+B*G) (0 : Matrix κ ν ℝ) (fun i => C i+D i*G) (fun _ => 0) ξ 0 where
  X := q.X
  path := q.path
  progressive := q.progressive
  continuous := q.continuous
  squareSup := q.squareSup
  representative := q.representative
  initial := q.initial
  equation b t ht := by
    have hd := congrFun (closed_loop_input T A B G u q.X hu) b
    have hz : (fun i => noiseInput T C D u q.X i b) =
        fun i => noiseInput T (fun i => C i+D i*G) (fun _ => (0 : Matrix κ ν ℝ)) 0 q.X i b := by
      funext i
      exact congrFun (closed_loop_input T (C i) (D i) G u q.X hu) b
    have he := q.equation b t ht
    rw [hd,hz] at he
    exact he

end LinearStochastic.CommonClosedLoopSolution
