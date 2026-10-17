module

public import LinearStochastic.PaperControlProperties

@[expose] public section

/-! The input-structure restriction is a necessary condition for the actual
four stochastic properties, not only for an auxiliary algebraic flag. -/
noncomputable section
namespace LinearStochastic.StochasticInputStructure
open MeasureTheory ProbabilityTheory Module
open scoped NNReal
open PaperControlProperties
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- Every one of EC, AC, ENC and ANC requires a genuine diffusion-free
input direction that acts nontrivially through the original drift matrix. -/
theorem drift_kernel_nonzero (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (p : Property) (h : Holds hW hWm hInd p T A B C D) :
    (InputStructure.jointDiffusion (fun i=>(D i).toEuclideanLin)).ker.map B.toEuclideanLin≠⊥ := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hf := flag_of_holds hW hWm hInd hn hm T hT A B C D p h
  have he := (AdjointCoefficients.matrix_flag_bot_iff_euclidean A B C D n).mp hf
  exact InputStructure.drift_kernel_ne_zero_of_flag_bot A.toEuclideanLin B.toEuclideanLin
    (fun i=>(C i).toEuclideanLin) (fun i=>(D i).toEuclideanLin) n he

/-- Exact controllability requires at least mn+1 actual input coordinates. -/
theorem exact_input_dimension (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (h : Holds hW hWm hInd .EC T A B C D) : m*n+1≤r := by
  have hc := (holds_iff hW hWm hInd hn hm T hT A B C D .EC).mp h
  have hd := InputStructure.input_dimension_lower_bound B.toEuclideanLin
    (InputStructure.jointDiffusion (fun i=>(D i).toEuclideanLin))
    ((SurjectiveMatrices.stack_full_rank_iff D).mp hc.2)
    (drift_kernel_nonzero hW hWm hInd hn hm T hT A B C D .EC h)
  have he : finrank ℝ (PiLp 2 (fun _ : Fin m=>EuclideanSpace ℝ (Fin n)))=m*n := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin m→EuclideanSpace ℝ (Fin n))).finrank_eq]
    simp [Module.finrank_pi_fintype]
  simpa only [he,finrank_euclideanSpace_fin] using hd

/-- If the drift vanishes on the diffusion kernel, all four properties fail. -/
theorem none_of_drift_kernel_zero (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (h : (InputStructure.jointDiffusion (fun i=>(D i).toEuclideanLin)).ker.map B.toEuclideanLin=⊥) :
    ∀ p, ¬Holds hW hWm hInd p T A B C D :=
  fun p hp=>drift_kernel_nonzero hW hWm hInd hn hm T hT A B C D p hp h

end LinearStochastic.StochasticInputStructure
