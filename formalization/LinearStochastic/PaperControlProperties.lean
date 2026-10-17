module

public import LinearStochastic.RawRankCriteria

@[expose] public section

/-! Named paper properties retain their actual raw-control meaning. This
finite index is only an interface for statements about all four properties;
the meanings are the original quantified stochastic definitions. -/
noncomputable section
namespace LinearStochastic.PaperControlProperties
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices

inductive Property
  | EC | AC | ENC | ANC
  deriving DecidableEq

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- The four original definitions, on the original Brownian usual filtration. -/
def Holds (p : Property) (T : ℝ≥0)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) : Prop :=
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  match p with
  | .EC=>RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i))
  | .AC=>RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i))
  | .ENC=>RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i))
  | .ANC=>RawControlProperties.ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i))

/-- The finite algebraic condition, separately defined from the actual
stochastic properties so that their equivalence is a theorem. -/
def Criterion (p : Property)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) : Prop :=
  match p with
  | .EC=>(AdjointCoefficients.fromMatrices A B C D).flag n=⊥ ∧ (SurjectiveMatrices.stack D).rank=m*n
  | _=>(AdjointCoefficients.fromMatrices A B C D).flag n=⊥

theorem holds_iff (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (p : Property) :
    Holds hW hWm hInd p T A B C D ↔ Criterion p A B C D := by
  have h := RawCompleteClassification.classification hW hWm hInd hn hm T hT A B C D
  cases p with
  | EC=>exact h.2.2.2
  | AC=>exact h.1
  | ENC=>exact h.2.2.1
  | ANC=>exact h.2.1

/-- Each of the four actual properties is independent of the positive horizon. -/
theorem horizon_independent (hn : 0 < n) (hm : 0 < m) (S T : ℝ≥0) (hS : 0 < S) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (p : Property) :
    Holds hW hWm hInd p S A B C D ↔ Holds hW hWm hInd p T A B C D :=
  (holds_iff hW hWm hInd hn hm S hS A B C D p).trans
    (holds_iff hW hWm hInd hn hm T hT A B C D p).symm

/-- Every property forces the same actual obstruction to vanish. -/
theorem flag_of_holds (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (p : Property)
    (h : Holds hW hWm hInd p T A B C D) : (AdjointCoefficients.fromMatrices A B C D).flag n=⊥ := by
  have hh := (holds_iff hW hWm hInd hn hm T hT A B C D p).mp h
  cases p with
  | EC=>exact hh.1
  | AC=>exact hh
  | ENC=>exact hh
  | ANC=>exact hh

/-- The first row of the classification table: a nonzero obstruction rules
out every one of the four actual properties. -/
theorem nonzero_flag_none (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n≠⊥) :
    ∀ p, ¬Holds hW hWm hInd p T A B C D :=
  fun p h=>hflag (flag_of_holds hW hWm hInd hn hm T hT A B C D p h)

/-- The two zero-obstruction rows: AC/ANC/ENC hold, and EC holds exactly
when the literal joint diffusion rank is full. -/
theorem zero_flag_regime (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n=⊥) :
    Holds hW hWm hInd .AC T A B C D ∧ Holds hW hWm hInd .ANC T A B C D ∧
    Holds hW hWm hInd .ENC T A B C D ∧
    (Holds hW hWm hInd .EC T A B C D ↔ (SurjectiveMatrices.stack D).rank=m*n) := by
  exact ⟨(holds_iff hW hWm hInd hn hm T hT A B C D .AC).mpr hflag,
    (holds_iff hW hWm hInd hn hm T hT A B C D .ANC).mpr hflag,
    (holds_iff hW hWm hInd hn hm T hT A B C D .ENC).mpr hflag,
    (holds_iff hW hWm hInd hn hm T hT A B C D .EC).trans (and_iff_right hflag)⟩

end LinearStochastic.PaperControlProperties
