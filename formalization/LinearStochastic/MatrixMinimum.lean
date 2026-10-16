import LinearStochastic.MatrixNormalization
import LinearStochastic.QuadraticMinimum

set_option maxHeartbeats 800000
noncomputable section
namespace LinearStochastic.MatrixMinimum
open scoped BigOperators Matrix.Norms.Frobenius
open LMIMatrixCoordinates MatrixNormalization QuadraticMinimum
variable {n r m : ℕ}

theorem isClosed_symmetric {k : Type*} [Fintype k] [DecidableEq k] :
    IsClosed {P : Matrix k k ℝ | P.IsSymm} := by
  change IsClosed {P : Matrix k k ℝ | P.transpose = P}
  exact isClosed_eq continuous_id.matrix_transpose continuous_id

theorem isClosed_posSemidef {k : Type*} [Fintype k] [DecidableEq k] :
    IsClosed {P : Matrix k k ℝ | P.PosSemidef} := by
  have hc : IsClosed (⋂ x : k → ℝ,
      {P : Matrix k k ℝ | 0 ≤ dotProduct (star x) (P.mulVec x)}) := by
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct,Matrix.mulVec,star_trivial]
    fun_prop
  convert isClosed_symmetric.inter hc using 1
  ext P
  simp [Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.isHermitian_iff_isSymm]

theorem matrixLMI_continuous
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    Continuous (fun z : ℝ × (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) =>
      matrixLMI A B C D z.1 z.2.1 z.2.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  rcases a with ⟨a,a'⟩
  rcases b with ⟨b,b'⟩
  cases a <;> cases b
  all_goals simp only [matrixLMI_state_state,matrixLMI_noise_state,
    matrixLMI_state_noise,matrixLMI_noise_noise,Matrix.add_apply,
    Matrix.smul_apply,Matrix.transpose_apply,Matrix.mul_apply]
  all_goals (try split_ifs) <;> fun_prop

/-- The whole parameterized feasible graph is closed in the actual matrix topology. -/
theorem isClosed_feasible_graph
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    IsClosed {z : ℝ × (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) |
      Feasible A B C D z.1 z.2.1 z.2.2} :=
  (isClosed_symmetric.preimage (continuous_fst.comp continuous_snd)).inter
    (isClosed_posSemidef.preimage ((matrixLMI_continuous A B C D).neg.sub continuous_const))

theorem isClosed_feasible
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) : IsClosed {z : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ |
      Feasible A B C D ρ z.1 z.2} :=
  (isClosed_feasible_graph A B C D).preimage (continuous_const.prodMk continuous_id)

/-- The actual normalized feasible set attains its Frobenius minimum. -/
theorem exists_feasible_minimum
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (hne : ∃ P K, Feasible A B C D ρ P K) :
    ∃ P K, Feasible A B C D ρ P K ∧
      ∀ P' K', Feasible A B C D ρ P' K' →
        matrixObjective (P,K) ≤ matrixObjective (P',K') := by
  obtain ⟨P,K,h⟩ := hne
  obtain ⟨z,hz,hmin⟩ := matrix_minimum _ (isClosed_feasible A B C D ρ) ⟨(P,K),h⟩
  exact ⟨z.1,z.2,hz,fun P' K' h' => hmin (P',K') h'⟩

/-- Existence is derived from the paper's original zero-obstruction condition. -/
theorem zero_flag_minimum
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) (ρ : ℝ) :
    ∃ P K, Feasible A B C D ρ P K ∧
      ∀ P' K', Feasible A B C D ρ P' K' →
        matrixObjective (P,K) ≤ matrixObjective (P',K') :=
  exists_feasible_minimum A B C D ρ (feasible_of_zero_flag A B C D hflag ρ)

#print axioms zero_flag_minimum
#print axioms isClosed_feasible_graph
end LinearStochastic.MatrixMinimum
