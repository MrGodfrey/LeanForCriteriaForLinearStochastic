module

public import LinearStochastic.PaperControlProperties
public import LinearStochastic.AlgebraStaircaseTermination

@[expose] public section

/-! The actual orthogonal-elimination state returns exactly the stochastic
classification. Zero residual and zero retained width are actual computed
stopping conditions, not hypotheses about controllability. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.StaircaseControlClassification
open MeasureTheory ProbabilityTheory Module
open scoped NNReal
open PaperControlProperties Staircase

section General
variable {E U ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
  (s : AdjointCoefficients (𝕜:=ℝ) (E:=E) (U:=U) (ι:=ι))

/-- A genuine zero residual at any stage fixes the terminal returned space. -/
theorem residual_zero_final (k : ℕ) (hk : k≤finrank ℝ E)
    (hz : finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0) :
    s.flag (finrank ℝ E)=(iterate s k).V.range := by
  rw [iterate_residual_rank,←stepRank_eq_prescribedDelta_increment] at hz
  have hh := s.stationary_of_step_eq ((stepRank_zero_iff_stationary s k).mp hz) (finrank ℝ E-k)
  rw [Nat.add_sub_of_le hk] at hh
  simpa only [iterate_range] using hh

/-- An actual zero retained space also remains zero through the terminal stage. -/
theorem zero_space_final (k : ℕ) (hk : k≤finrank ℝ E)
    (hz : (iterate s k).V.range=⊥) : s.flag (finrank ℝ E)=⊥ := by
  rw [iterate_range] at hz
  exact bot_unique ((s.flag_antitone hk).trans_eq hz)

/-- In either actual stopping branch, the returned space is exactly V*. -/
theorem stop_returns_terminal (k : ℕ) (hk : k≤finrank ℝ E)
    (hstop : (iterate s k).V.range=⊥ ∨
      finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0) :
    s.flag (finrank ℝ E)=(iterate s k).V.range := by
  rcases hstop with hz|hz
  · exact (zero_space_final s k hk hz).trans hz.symm
  · exact residual_zero_final s k hk hz

/-- Having no retained columns is exactly a zero returned subspace. -/
theorem no_columns_iff (k : ℕ) :
    finrank ℝ (iterate s k).VSpace=0 ↔ (iterate s k).V.range=⊥ := by
  rw [←LinearMap.finrank_range_of_inj (iterate s k).V.injective]
  exact Submodule.finrank_eq_zero
end General

/-- The actual Euclidean adjoint coefficients used by the reduced algorithm. -/
def systemCoefficients {n r m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :=
  InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
    (fun i=>(C i).toEuclideanLin) (fun i=>(D i).toEuclideanLin)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- All four actual properties are read correctly from any actual stopped
orthogonal-elimination state, by the displayed zero-space and joint-rank tests. -/
theorem stopped_classification (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (k : ℕ) (hk : k≤n)
    (hstop : 
      (iterate (systemCoefficients A B C D) k).V.range=⊥ ∨ finrank ℝ (residual (systemCoefficients A B C D) (iterate (systemCoefficients A B C D) k).Q (iterate (systemCoefficients A B C D) k).V).range=0)
    (p : Property) :
    Holds hW hWm hInd p T A B C D ↔
      let s := systemCoefficients A B C D
      (iterate s k).V.range=⊥ ∧ (p=.EC → (SurjectiveMatrices.stack D).rank=m*n) := by
  let s := systemCoefficients A B C D
  have he := stop_returns_terminal s k (by simpa only [finrank_euclideanSpace_fin] using hk) hstop
  simp only [finrank_euclideanSpace_fin] at he
  have hf : (AdjointCoefficients.fromMatrices A B C D).flag n=⊥ ↔ (iterate s k).V.range=⊥ := by
    rw [AdjointCoefficients.matrix_flag_bot_iff_euclidean]
    change s.flag n=⊥ ↔ _
    rw [he]
  apply (holds_iff hW hWm hInd hn hm T hT A B C D p).trans
  cases p <;> simp [Criterion,hf,s]

/-- The pseudocode's n-stage bound supplies an actual stopped state whose
returned space and joint-rank check classify all four stochastic properties. -/
theorem terminates_and_classifies (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    let s := systemCoefficients A B C D
    ∃ k≤n, ((k<n ∧ finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0) ∨
      (iterate s k).V.range=⊥) ∧
      ∀ p, Holds hW hWm hInd p T A B C D ↔
        (iterate s k).V.range=⊥ ∧ (p=.EC → (SurjectiveMatrices.stack D).rank=m*n) := by
  let s := systemCoefficients A B C D
  have hs := stops_within_dimension s
  simp only [finrank_euclideanSpace_fin] at hs
  rcases hs with ⟨k,hk,hz⟩|hz
  · exact ⟨k,hk.le,Or.inl ⟨hk,hz⟩,stopped_classification hW hWm hInd hn hm T hT A B C D k hk.le (Or.inr hz)⟩
  · have hz' : (iterate (systemCoefficients A B C D) n).V.range=⊥ := by
      rw [iterate_range] at hz ⊢
      change s.flag n = ⊥
      simpa only [finrank_euclideanSpace_fin] using hz
    exact ⟨n,le_rfl,Or.inr hz',stopped_classification hW hWm hInd hn hm T hT A B C D n le_rfl (Or.inl hz')⟩

/-- The early zero-residual branch, when the current retained space is
nonzero as in the live loop, correctly returns failure of all four properties. -/
theorem zero_residual_nonzero_none (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (k : ℕ) (hk : k<n)
    (hz : 
      finrank ℝ (residual (systemCoefficients A B C D) (iterate (systemCoefficients A B C D) k).Q (iterate (systemCoefficients A B C D) k).V).range=0)
    (hne : 
      (iterate (systemCoefficients A B C D) k).V.range≠⊥) :
    ∀ p, ¬Holds hW hWm hInd p T A B C D := by
  intro p hp
  exact hne ((stopped_classification hW hWm hInd hn hm T hT A B C D k hk.le (Or.inr hz) p).mp hp).1

/-- The zero-column branch correctly returns AC, ANC and ENC, and its extra
joint-rank test decides EC for the actual stochastic system. -/
theorem zero_columns_success (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (k : ℕ) (hk : k≤n)
    (hz : 
      finrank ℝ (iterate (systemCoefficients A B C D) k).VSpace=0) :
    ∀ p, Holds hW hWm hInd p T A B C D ↔ (p=.EC → (SurjectiveMatrices.stack D).rank=m*n) := by
  let s := systemCoefficients A B C D
  have he := (no_columns_iff s k).mp hz
  intro p
  exact (stopped_classification hW hWm hInd hn hm T hT A B C D k hk (Or.inl he) p).trans
    (and_iff_right he)

end LinearStochastic.StaircaseControlClassification
