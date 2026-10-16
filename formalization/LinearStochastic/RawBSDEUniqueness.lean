import LinearStochastic.RawBSDECoordinates

/-! Actual Hilbert-valued backward existence and uniqueness, with arbitrary
raw solutions and original usual Brownian drivers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.RawBSDEUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LpOrthonormalCoordinates
open HilbertLocalSolution RawBSDECoordinates
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))

/-- Any two actual vector raw backward solutions agree in the entire state
and noise classes and on one probability-one event at every time. -/
theorem global_unique {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i≠j → IndepFun (fun ω t=>W i t ω) (fun ω t=>W j t ω) μ)
    (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ)
    (q r : RawSolution (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η) :
    q.Y=r.Y ∧ q.Z=r.Z ∧ ∀ᵐ ω ∂μ, ∀ t, t≤T → q.path t ω=r.path t ω := by
  have h := BrownianBSDEUniqueness.global_unique hW hWm hpair hchannels i₀ T
    (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) (fun a=>coordinate b a η)
    (toCoordinates b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η q)
    (toCoordinates b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η r)
  have hy : (fun a=>coordinate b a q.Y)=(fun a=>coordinate b a r.Y) := congrArg Prod.fst h.1
  have hY : q.Y=r.Y := by
    have he := congrArg (assemble (mΛ:=𝓕.predictable) b) hy
    simpa only [assemble_coordinates] using he
  have hZ : q.Z=r.Z := by
    funext i
    have hz : (fun a=>coordinate b a (q.Z i))=(fun a=>coordinate b a (r.Z i)) :=
      congrArg (fun X : BSDEMatrixPicard.PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T=>fun a=>X.2 a i) h.1
    have he := congrArg (assemble (mΛ:=𝓕.predictable) b) hz
    simpa only [assemble_coordinates] using he
  refine ⟨hY,hZ,?_⟩
  filter_upwards [h.2] with ω hω
  intro t ht
  apply b.repr.injective
  ext a
  have he : inner ℝ (b a) (q.path t ω)=inner ℝ (b a) (r.path t ω) := hω a t ht
  simpa only [OrthonormalBasis.repr_apply_apply] using he

variable [μ.IsComplete] (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- The paper's original usual filtration needs no extra MR, common-noise
independence or all-samples-continuity assumption. -/
theorem usual_global_unique (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∀ q r : RawSolution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η,
      q.Y=r.Y ∧ q.Z=r.Z ∧ ∀ᵐ ω ∂μ, ∀ t, t≤T → q.path t ω=r.path t ω := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro q r
  exact global_unique b hW hWm (JointUsualBrownianGlobal.pairForward hW hWm hInd)
    (fun _ _ hij=>hInd.indepFun hij) i₀ T A C η q r

/-- Every original FT L² target has a genuine vector raw S²×H² solution,
and this solution is unique among all such actual vector raw solutions. -/
theorem exists_and_unique (i₀ : ι) (T : ℝ≥0) (hT : 0<T)
    (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ)
    (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ q : RawSolution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η,
      ∀ r : RawSolution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
        b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η,
        q.Y=r.Y ∧ q.Z=r.Z ∧ ∀ᵐ ω ∂μ, ∀ t, t≤T → q.path t ω=r.path t ω := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have he (a : κ) : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] (coordinate b a η) μ :=
    ((innerSL ℝ (b a)).continuous.comp_aestronglyMeasurable hη).congr (coordinate_ae b a η).symm
  obtain ⟨q⟩ := BrownianGlobalBSDE.exists_global hW hWm hInd i₀ T hT
    (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) (fun a=>coordinate b a η) he
  let R := fromCoordinates b (fun i=>(hW i).toIsPreBrownianReal) hWm T A C η q
  exact ⟨R,fun r=>usual_global_unique b hW hWm hInd i₀ T A C η R r⟩
end LinearStochastic.RawBSDEUniqueness
