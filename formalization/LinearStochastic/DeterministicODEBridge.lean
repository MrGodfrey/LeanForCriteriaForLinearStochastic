import LinearStochastic.DeterministicControlClassification

/-! Every classical deterministic measurable finite-energy ODE solution is
admitted by the raw-solution interface. This closes the reverse semantic bridge;
classical necessity is not restricted to specially constructed Gramian paths. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.DeterministicODEBridge
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open CommonItoMultichannel ZeroObservationMatrices
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)
  (T : ℝ≥0) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)

/-- A wholly deterministic ODE path, with its ordinary measurable L² control.
This definition has no probability space or Brownian motion parameter. -/
def OdePath (x : EuclideanSpace ℝ (Fin n)) (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ d : ℝ≥0 → EuclideanSpace ℝ (Fin r), StronglyMeasurable d ∧
    MemLp d 2 (CommonItoCLM.timeMeasure_T T) ∧ ContinuousOn q (Iic T) ∧
    ∀ t, t≤T → q t=x+∫ s in Ioc 0 (t:ℝ), matrixMap A (q s.toNNReal)+matrixMap B (d s.toNNReal)

/-- L² controls need only be measurable almost everywhere: replacing them
by a genuine measurable representative preserves every ODE integral. -/
theorem odePath_of_memLp_control (x : EuclideanSpace ℝ (Fin n))
    (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) (d : ℝ≥0 → EuclideanSpace ℝ (Fin r))
    (hd : MemLp d 2 (CommonItoCLM.timeMeasure_T T)) (hc : ContinuousOn q (Iic T))
    (heq : ∀ t, t≤T → q t=x+∫ s in Ioc 0 (t:ℝ), matrixMap A (q s.toNNReal)+matrixMap B (d s.toNNReal)) :
    OdePath T A B x q := by
  let d' := hd.aestronglyMeasurable.mk d
  have he : d=ᵐ[CommonItoCLM.timeMeasure_T T] d' := hd.aestronglyMeasurable.ae_eq_mk
  refine ⟨d',hd.aestronglyMeasurable.stronglyMeasurable_mk,(memLp_congr_ae he).mp hd,hc,?_⟩
  intro t ht
  rw [heq t ht]
  congr 1
  apply integral_congr_ae
  have hr := (RealTimeBridge.toNNReal_measurePreserving T).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr ht)) hr] with s hs
  change d s.toNNReal=d' s.toNNReal at hs
  rw [hs]

/-- The actual Gramian construction gives wholly deterministic classical
ODE paths and finite-energy controls, with exact arbitrary endpoints. -/
theorem ode_exact_of_kalman (hT : 0 < T) (hK : (Deterministic.kalman A B n).rank=n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ∃ q, OdePath T A B x q ∧ q T=y := by
  let hobs := DeterministicGramianMatrices.observable_of_kalman_rank A B hK
  let K := DeterministicGramianControl.kernel (matrixMap A) (matrixMap B) ((T:ℝ)-(0:ℝ≥0))
    (sub_pos.mpr (NNReal.coe_lt_coe.mpr hT)) hobs
  have hKc : Continuous K := DeterministicGramianControl.kernel_continuous _ _ _ _ hobs
  let z := y-(NormedSpace.exp ((T:ℝ) • matrixMap A)) x
  let d := fun t=>KnownTargetControl.control 0 T K (fun _ : Unit=>z) t ()
  let q := fun t=>KnownTargetState.path (matrixMap A) (matrixMap B) K 0 x (fun _ : Unit=>z) t ()
  have hd : StronglyMeasurable d :=
    (KnownTargetControl.measurable_template 0 T K (fun _ : Unit=>z) id measurable_id hKc stronglyMeasurable_const).comp_measurable (g:=fun t : ℝ≥0=>(t,()))
      (measurable_id.prodMk measurable_const)
  obtain ⟨M,_,hM⟩ := KnownTargetControl.exists_norm_bound 0 T K (fun _ : Unit=>z) hKc
  have hd2 : MemLp d 2 (CommonItoCLM.timeMeasure_T T) :=
    MemLp.of_bound hd.aestronglyMeasurable (M*‖z‖) (Filter.Eventually.of_forall (fun t=>hM t ()))
  refine ⟨q,⟨d,hd,hd2,(KnownTargetState.continuous (matrixMap A) (matrixMap B) K 0 x
    (fun _ : Unit=>z) hKc ()).continuousOn,?_⟩,?_⟩
  · intro t ht
    simpa only [add_comm] using KnownTargetState.equation (matrixMap A) (matrixMap B) K 0 T x
      (fun _ : Unit=>z) hKc t ht ()
  · have he := KnownTargetSolution.terminal (matrixMap A) (matrixMap B) 0 T hT hobs x z
    change q T=(NormedSpace.exp ((T:ℝ) • matrixMap A)) x+z at he
    rw [he]
    dsimp only [z]
    abel

/-- Extending a continuous interval path by its terminal value yields a
literal deterministic raw solution with the same interval values and endpoint. -/
theorem path_of_ode (x : EuclideanSpace ℝ (Fin n)) (q : ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (hq : OdePath T A B x q) :
    DeterministicControlClassification.Path hW hWm hInd T A B x (fun t=>q (min t T)) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  obtain ⟨d,hd,hd2,hc,heq⟩ := hq
  let v := fun t (_ : Ω)=>d t
  let R := fun t (_ : Ω)=>q (min t T)
  have hv : IsStronglyProgressive (JointUsualNatural.usual (μ:=μ) W hWm) v := by
    intro t
    exact hd.comp_measurable (measurable_subtype_coe.comp measurable_fst)
  have hv2 : MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ) := hd2.comp_fst μ
  have hc' : Continuous (fun t=>q (min t T)) :=
    hc.comp_continuous (continuous_id.min continuous_const) (fun t=>min_le_right t T)
  have hp : IsStronglyProgressive (JointUsualNatural.usual (μ:=μ) W hWm) R := by
    intro t
    exact hc'.stronglyMeasurable.comp_measurable (measurable_subtype_coe.comp measurable_fst)
  have hRc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>R t ω) (Iic T) :=
    Filter.Eventually.of_forall (fun _=>hc'.continuousOn)
  have hR2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ :=
    memLp_const (ContinuousDoobL2.pathSup (fun t (_ : Unit)=>q (min t T)) T ())
  obtain ⟨u,X,hu,hX⟩ := ProgressiveControlSection.representatives T v R hv hv2 hp hRc hR2
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
  refine ⟨d,u,X,⟨hv,hv2,hp,hRc,hR2,hu,hX,?_⟩⟩
  intro t ht
  rw [hzeroX,hzerou,add_zero]
  have hint : (∫ s in Ioc 0 (t:ℝ), matrixMap A (q (min s.toNNReal T))+matrixMap B (d s.toNNReal))=
      ∫ s in Ioc 0 (t:ℝ), matrixMap A (q s.toNNReal)+matrixMap B (d s.toNNReal) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsT : s.toNNReal≤T := (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans ht
    rw [min_eq_left hsT]
  filter_upwards [ZeroIntegralDrift.vectorProcess_zero_ae (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i=>(hW i).toIsPreBrownianReal) hWm T t] with ω hz
  simpa only [hz,Pi.zero_apply,add_zero,min_eq_left ht,hint,add_comm] using heq t ht

/-- The exact endpoint is unaffected by this honest deterministic extension. -/
theorem exact_of_ode (x y : EuclideanSpace ℝ (Fin n))
    (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) (hq : OdePath T A B x q) (hend : q T=y) :
    DeterministicControlClassification.ExactReach hW hWm hInd T A B x y :=
  ⟨(fun t=>q (min t T)),path_of_ode hW hWm hInd T A B x q hq,by simpa only [min_self] using hend⟩

/-- Likewise for arbitrary deterministic approximation errors. -/
theorem approximate_of_ode (x y : EuclideanSpace ℝ (Fin n)) (ε : ℝ)
    (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) (hq : OdePath T A B x q) (herr : ‖q T-y‖^2<ε) :
    DeterministicControlClassification.ApproxReach hW hWm hInd T A B x y ε :=
  ⟨(fun t=>q (min t T)),path_of_ode hW hWm hInd T A B x q hq,by simpa only [min_self] using herr⟩

/-- The four classical properties defined purely by deterministic ODE paths;
there is no Brownian or probability argument in this definition. -/
def OdeHolds (p : PaperControlProperties.Property) : Prop :=
  match p with
  | .EC=>∀ x y, ∃ q, OdePath T A B x q ∧ q T=y
  | .ENC=>∀ x, ∃ q, OdePath T A B x q ∧ q T=0
  | .AC=>∀ x y ε, 0<ε → ∃ q, OdePath T A B x q ∧ ‖q T-y‖^2<ε
  | .ANC=>∀ x ε, 0<ε → ∃ q, OdePath T A B x q ∧ ‖q T‖^2<ε

include hW hWm hInd in
/-- On the paper's standing setting, all four entirely deterministic ODE
properties are precisely Kalman rank. Necessity admits every measurable L²
classical control through path_of_ode; sufficiency is the genuine Gramian. -/
theorem ode_classification (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (p : PaperControlProperties.Property) :
    OdeHolds T A B p ↔ (Deterministic.kalman A B n).rank=n := by
  constructor
  · intro h
    have ha : DeterministicControlClassification.Holds hW hWm hInd T A B .ANC := by
      intro x ε hε
      have hex (q : ℝ≥0 → EuclideanSpace ℝ (Fin n)) (hq : OdePath T A B x q) (hend : q T=0) :=
        approximate_of_ode hW hWm hInd T A B x 0 ε q hq (by simpa [hend] using hε)
      cases p with
      | EC=>obtain ⟨q,hq,he⟩ := h x 0; exact hex q hq he
      | ENC=>obtain ⟨q,hq,he⟩ := h x; exact hex q hq he
      | AC=>obtain ⟨q,hq,he⟩ := h x 0 ε hε; exact approximate_of_ode hW hWm hInd T A B x 0 ε q hq he
      | ANC=>
        obtain ⟨q,hq,he⟩ := h x ε hε
        exact approximate_of_ode hW hWm hInd T A B x 0 ε q hq (by simpa only [sub_zero] using he)
    exact (DeterministicControlClassification.holds_iff_kalman hW hWm hInd T A B hn hm hT .ANC).mp ha
  · intro hK
    cases p with
    | EC=>exact ode_exact_of_kalman T A B hT hK
    | ENC=>exact fun x=>ode_exact_of_kalman T A B hT hK x 0
    | AC=>
      intro x y ε hε
      obtain ⟨q,hq,he⟩ := ode_exact_of_kalman T A B hT hK x y
      exact ⟨q,hq,by simpa [he] using hε⟩
    | ANC=>
      intro x ε hε
      obtain ⟨q,hq,he⟩ := ode_exact_of_kalman T A B hT hK x 0
      exact ⟨q,hq,by simpa [he] using hε⟩

end LinearStochastic.DeterministicODEBridge
