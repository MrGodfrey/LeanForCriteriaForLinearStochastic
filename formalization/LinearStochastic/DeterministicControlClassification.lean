module

public import LinearStochastic.StochasticDeterministicReduction
public import LinearStochastic.KnownTargetSolution
public import LinearStochastic.DeterministicGramianMatrices

@[expose] public section

/-! The deterministic-control, deterministic-target reading in the paper is
kept separate from random-target EC. Controls and entire state paths here are
literal deterministic functions, satisfying the original zero-noise equation. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.DeterministicControlClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonItoMultichannel ZeroObservationMatrices PaperControlProperties
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)
  (T : ℝ≥0) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)

/-- Literal deterministic finite-energy control and continuous state, with
predictable classes used only to express the already constructed integral. -/
def Path (x : EuclideanSpace ℝ (Fin n)) (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) : Prop :=
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  ∃ (d : ℝ≥0 → EuclideanSpace ℝ (Fin r))
    (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
    (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)),
    ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i=>(hW i).toIsPreBrownianReal) hWm T (fun _=>x) (matrixMap A) (matrixMap B)
      (fun _ : Fin m=>0) (fun _=>0) (fun t _=>d t) (fun t _=>q t) u X

/-- The path predicate really entails the deterministic ODE, pointwise at
all times of the interval. No stochastic integral remains when C=D=0. -/
theorem path_original_ode (x : EuclideanSpace ℝ (Fin n))
    (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) (hq : Path hW hWm hInd T A B x q) :
    ContinuousOn q (Set.Iic T) ∧ ∃ d : ℝ≥0 → EuclideanSpace ℝ (Fin r),
      ∀ t, t≤T → q t=x+∫ s in Set.Ioc 0 (t:ℝ), matrixMap A (q s.toNNReal)+matrixMap B (d s.toNNReal) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  obtain ⟨d,u,X,hr⟩ := hq
  have hc : ContinuousOn q (Set.Iic T) := hr.continuous.exists.choose_spec
  refine ⟨hc,d,?_⟩
  have hzeroX : (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).compLp X=0 := by
    apply Lp.ext
    filter_upwards [(0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).coeFn_compLp X,
      Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)] with z hf hz
    simp only [hf,hz,zero_apply,Pi.zero_apply]
  have hzerou : (0 : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin n)).compLp u=0 := by
    apply Lp.ext
    filter_upwards [(0 : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin n)).coeFn_compLp u,
      Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)] with z hf hz
    simp only [hf,hz,zero_apply,Pi.zero_apply]
  intro t ht
  have he := hr.equation t ht
  rw [hzeroX,hzerou,add_zero] at he
  have hz := ZeroIntegralDrift.vectorProcess_zero_ae (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i=>(hW i).toIsPreBrownianReal) hWm T t
  obtain ⟨ω,he,hz⟩ := (he.and hz).exists
  simpa only [hz,Pi.zero_apply,add_zero,add_comm] using he

/-- Exact deterministic reachability, with no random initial or target. -/
def ExactReach (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ q, Path hW hWm hInd T A B x q ∧ q T=y

/-- Approximate deterministic reachability uses its actual Euclidean error. -/
def ApproxReach (x y : EuclideanSpace ℝ (Fin n)) (ε : ℝ) : Prop :=
  ∃ q, Path hW hWm hInd T A B x q ∧ ‖q T-y‖^2<ε

/-- The four classical notions, distinguished from the stochastic definitions. -/
def Holds (p : Property) : Prop :=
  match p with
  | .EC=>∀ x y, ExactReach hW hWm hInd T A B x y
  | .ENC=>∀ x, ExactReach hW hWm hInd T A B x 0
  | .AC=>∀ x y ε, 0<ε → ApproxReach hW hWm hInd T A B x y ε
  | .ANC=>∀ x ε, 0<ε → ApproxReach hW hWm hInd T A B x 0 ε

/-- The genuine Gramian formula supplies deterministic controls and states,
not merely a stochastic controllability existence statement. -/
theorem exact_reach_of_kalman (hT : 0 < T)
    (hK : (Deterministic.kalman A B n).rank=n) (x y : EuclideanSpace ℝ (Fin n)) :
    ExactReach hW hWm hInd T A B x y := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  let K := DeterministicGramianControl.kernel (matrixMap A) (matrixMap B) ((T:ℝ)-(0:ℝ≥0))
    (sub_pos.mpr (NNReal.coe_lt_coe.mpr hT)) (DeterministicGramianMatrices.observable_of_kalman_rank A B hK)
  let z := y-(NormedSpace.exp ((T:ℝ) • matrixMap A)) x
  let d := fun t=>KnownTargetControl.control 0 T K (fun _ : Unit=>z) t ()
  let q := fun t=>KnownTargetState.path (matrixMap A) (matrixMap B) K 0 x (fun _ : Unit=>z) t ()
  obtain ⟨u,X,hraw,_,_⟩ := KnownTargetSolution.exists_solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i=>(hW i).toIsPreBrownianReal) hWm
    (matrixMap A) (matrixMap B) 0 T hT (DeterministicGramianMatrices.observable_of_kalman_rank A B hK)
    x (fun _=>y) stronglyMeasurable_const (memLp_const y)
  refine ⟨q,⟨d,u,X,?_⟩,?_⟩
  · exact hraw
  · have he := KnownTargetSolution.terminal (matrixMap A) (matrixMap B) 0 T hT
      (DeterministicGramianMatrices.observable_of_kalman_rank A B hK) x z
    change q T=(NormedSpace.exp ((T:ℝ) • matrixMap A)) x+z at he
    rw [he]
    dsimp only [z]
    abel

/-- Any of the four literal deterministic notions implies classical ANC. -/
theorem implies_approximateNull (p : Property) (h : Holds hW hWm hInd T A B p) :
    Holds hW hWm hInd T A B .ANC := by
  have hex (x y) (h : ExactReach hW hWm hInd T A B x y) (ε : ℝ) (hε : 0<ε) :
      ApproxReach hW hWm hInd T A B x y ε := by
    obtain ⟨q,hq,he⟩ := h
    exact ⟨q,hq,by simpa [he] using hε⟩
  cases p with
  | EC=>exact fun x ε hε=>hex x 0 (h x 0) ε hε
  | AC=>exact fun x ε hε=>h x 0 ε hε
  | ENC=>exact fun x ε hε=>hex x 0 (h x) ε hε
  | ANC=>exact h

/-- A deterministic path is also an admissible ordinary-progressive path;
the deterministic norm error equals its expected error exactly. -/
theorem approximateNull_raw (h : Holds hW hWm hInd T A B .ANC) :
    PaperControlProperties.Holds hW hWm hInd .ANC T A B (fun _ : Fin m=>0) (fun _=>0) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro x ε hε
  obtain ⟨q,⟨d,u,X,hraw⟩,he⟩ := h x ε hε
  refine ⟨(fun t _=>d t),(fun t _=>q t),u,X,?_,?_⟩
  · simpa only [matrixMap,map_zero] using hraw
  · have hh : (∫ ω, ‖q T-(0 : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) ω‖^2 ∂μ)=‖q T‖^2 := by
      calc
        _ = ∫ _ω : Ω, ‖q T‖^2 ∂μ := integral_congr_ae ((Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 μ).mono
          (fun ω hω=>by simp only [hω,Pi.zero_apply,sub_zero]))
        _ = _ := by simp
    rw [hh]
    simpa only [sub_zero] using he

/-- All four classical deterministic-control/deterministic-target notions
are exactly Kalman rank. The target restriction is explicit in the type. -/
theorem holds_iff_kalman (hn : 0 < n) (hm : 0 < m) (hT : 0 < T) (p : Property) :
    Holds hW hWm hInd T A B p ↔ (Deterministic.kalman A B n).rank=n := by
  constructor
  · intro h
    exact (StochasticDeterministicReduction.null_properties_iff_kalman hW hWm hInd hn hm T hT A B
      .ANC (by decide)).mp (approximateNull_raw hW hWm hInd T A B
        (implies_approximateNull hW hWm hInd T A B p h))
  · intro hK
    have hec : Holds hW hWm hInd T A B .EC := exact_reach_of_kalman hW hWm hInd T A B hT hK
    cases p with
    | EC=>exact hec
    | ENC=>exact fun x=>hec x 0
    | ANC=>exact implies_approximateNull hW hWm hInd T A B .EC hec
    | AC=>
      intro x y ε hε
      obtain ⟨q,hq,he⟩ := hec x y
      exact ⟨q,hq,by simpa [he] using hε⟩

end LinearStochastic.DeterministicControlClassification
