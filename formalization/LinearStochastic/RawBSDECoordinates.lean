module

public import LinearStochastic.BrownianBSDEUniqueness
public import LinearStochastic.HilbertSectionCoordinates
public import LinearStochastic.BSDEHilbertGlobal
public import LinearStochastic.ProgressivePredictable

@[expose] public section

/-! Arbitrary genuine Hilbert-valued raw backward solutions, rather than only
constructed solutions, give the coordinate record used by global uniqueness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStochastic.RawBSDECoordinates
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality LpOrthonormalCoordinates
open HilbertLocalSolution BSDEHilbertCoordinates ContinuousDoobL2
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual vector backward equation, with independent terminal condition
and arbitrary progressive continuous S² path and genuine H² noise. -/
structure RawSolution (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ) where
  Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)
  Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)
  path : ℝ≥0 → Ω → E
  progressive : IsStronglyProgressive 𝓕 path
  continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>path t ω) (Iic T)
  squareSup : MemLp (pathSup path T) 2 μ
  representative : Y =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry path
  terminal : path T =ᵐ[μ] η
  equation : ∀ t, t≤T → path t =ᵐ[μ] integralState b hW hWm T (path 0)
    (-(A.adjoint.compLp Y+∑ i,(C i).adjoint.compLp (Z i))) Z (t:ℝ)

omit hW hWm [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- A genuine vector S² path has S² scalar orthonormal coordinates. -/
theorem coordinate_squareSup (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hR : IsStronglyProgressive 𝓕 R)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>R t ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) (a : κ) :
    MemLp (pathSup (fun t ω=>inner ℝ (b a) (R t ω)) T) 2 μ := by
  have hcoord : IsStronglyProgressive 𝓕 (fun t ω=>inner ℝ (b a) (R t ω)) :=
    fun t=>(innerSL ℝ (b a)).continuous.comp_stronglyMeasurable (hR t)
  have hcc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>inner ℝ (b a) (R t ω)) (Iic T) := hc.mono (fun ω hω=>(innerSL ℝ (b a)).continuous.comp_continuousOn hω)
  apply h2.mono' (CommonStateS2.pathSup_measurableOn T hcoord.stronglyAdapted hcc)
  filter_upwards [hc,hcc] with ω hω ha
  have hcomp : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun t : Iic T=>‖R t.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hω.norm
  have hba : BddAbove (range (fun t : Iic T=>‖inner ℝ (b a) (R t.val ω)‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image ha.norm
  have hpa : 0≤pathSup (fun t ω=>inner ℝ (b a) (R t ω)) T ω :=
    le_ciSup_of_le hba ⟨0,show (0:ℝ≥0)≤T from bot_le⟩ (norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hpa]
  change (⨆ t : Iic T, ‖inner ℝ (b a) (R t.val ω)‖) ≤ _
  apply ciSup_le
  intro t
  apply (norm_inner_le_norm _ _).trans
  simpa only [b.norm_eq_one,one_mul,pathSup] using (le_ciSup hb t)

/-- No canonical-solution assumption: project any genuine raw vector solution
into the exact coordinate Solution record used by the global uniqueness proof. -/
def toCoordinates (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ)
    (q : RawSolution (𝓕:=𝓕) b hW hWm T A C η) :
    BSDEPathData.Solution (𝓕:=𝓕) hW hWm T (coefficientMatrix b b A)
      (fun i=>coefficientMatrix b b (C i)) (fun a=>coordinate b a η) := by
  let Q : BSDEMatrixPicard.PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T :=
    (fun a=>coordinate b a q.Y, fun a=>WithLp.toLp 2 (fun i=>coordinate b a (q.Z i)))
  have hf (a : κ) : coordinate b a (-(A.adjoint.compLp q.Y+∑ i,(C i).adjoint.compLp (q.Z i))) =
      -BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) Q a := by
    have h := assemble_neg (mΛ:=𝓕.predictable) b
      (BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) Q)
    rw [assemble_driver] at h
    simp only [Q,assemble_coordinates] at h
    have he := congrArg (coordinate (mΩ:=𝓕.predictable) b a) h
    rw [coordinate_assemble (mΛ:=𝓕.predictable)] at he
    exact he.symm
  refine ⟨Q,(fun a t ω=>inner ℝ (b a) (q.path t ω)),
    (fun a=>(show IsStronglyProgressive 𝓕 (fun t ω=>inner ℝ (b a) (q.path t ω)) from
      fun t=>(innerSL ℝ (b a)).continuous.comp_stronglyMeasurable (q.progressive t)).isProgressive),
    (fun a=>q.continuous.mono (fun _ h=>(innerSL ℝ (b a)).continuous.comp_continuousOn h)),
    coordinate_squareSup b T q.path q.progressive q.continuous q.squareSup,?_,?_,?_⟩
  · intro a
    exact Filter.EventuallyEq.trans (ae_of_ae_trim 𝓕.predictable_le_prod (coordinate_ae (mΩ:=𝓕.predictable) b a q.Y))
      (q.representative.fun_comp (innerSL ℝ (b a)))
  · intro a
    exact (q.terminal.fun_comp (innerSL ℝ (b a))).trans (coordinate_ae b a η).symm
  · intro a t ht
    have he := (q.equation t ht).fun_comp (innerSL ℝ (b a))
    have hi := HilbertSectionCoordinates.integral_coordinate_ae b hW hWm T t
      (by exact_mod_cast ht) (q.path 0)
      (-(A.adjoint.compLp q.Y+∑ i,(C i).adjoint.compLp (q.Z i))) q.Z a
    rw [hf a] at hi
    simp only [Real.toNNReal_coe] at hi
    filter_upwards [he,hi] with ω he hi
    rw [RealTimeBridge.integral_real_extension t
      (fun s=>(-BSDEMatrixPicard.driver T (coefficientMatrix b b A)
        (fun i=>coefficientMatrix b b (C i)) Q a) (s,ω))] at hi
    exact he.trans hi

/-- Conversely, reconstruct the actual full Hilbert raw path from any genuine
coordinate backward solution, preserving both independent terminal and equation. -/
def fromCoordinates (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (η : Lp E 2 μ)
    (q : BSDEPathData.Solution (𝓕:=𝓕) hW hWm T (coefficientMatrix b b A)
      (fun i=>coefficientMatrix b b (C i)) (fun a=>coordinate b a η)) :
    RawSolution (𝓕:=𝓕) b hW hWm T A C η := by
  let Y := assemble (mΛ:=𝓕.predictable) b q.X.1
  let Z := fun i=>assemble (mΛ:=𝓕.predictable) b (fun a=>q.X.2 a i)
  let R := CoordinatePathSolution.reconstruct b q.path
  have hp : IsStronglyProgressive 𝓕 R :=
    CoordinatePathSolution.reconstruct_progressive b q.path (fun a=>(q.progressive a).isStronglyProgressive)
  have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>R t ω) (Iic T) := by
    have hall : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t=>q.path a t ω) (Iic T) := by
      rw [ae_all_iff]; exact q.continuous
    filter_upwards [hall] with ω hω
    apply continuousOn_finsetSum
    exact fun a _=>(hω a).smul continuousOn_const
  have hf : assemble (mΛ:=𝓕.predictable) b
      (-BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) q.X) =
        -(A.adjoint.compLp Y+∑ i,(C i).adjoint.compLp (Z i)) := by
    rw [assemble_neg (mΛ:=𝓕.predictable),assemble_driver]
  refine ⟨Y,Z,R,hp,hc,?_,?_,?_,?_⟩
  · exact CoordinatePathSolution.reconstruct_S2 b T q.path
      (fun a=>(q.progressive a).isStronglyProgressive) q.continuous q.squareSup
  · have hall : ∀ᵐ z ∂(CommonItoCLM.timeMeasure_T T).prod μ, ∀ a, q.X.1 a z=q.path a z.1 z.2 := by
      rw [ae_all_iff]; exact q.representative
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (assemble_ae (mΛ:=𝓕.predictable) b q.X.1),hall] with z he hz
    exact he.trans (Finset.sum_congr rfl (fun a _=>congrArg (fun r:ℝ=>r • b a) (hz a)))
  · have hall : ∀ᵐ ω ∂μ, ∀ a, q.path a T ω=coordinate b a η ω := by
      rw [ae_all_iff]; exact q.terminal
    filter_upwards [hall,assemble_ae b (fun a=>coordinate b a η)] with ω hω he
    rw [assemble_coordinates] at he
    exact (Finset.sum_congr rfl (fun a _=>congrArg (fun r:ℝ=>r • b a) (hω a))).trans he.symm
  · intro t ht
    have he := CoordinatePathSolution.integral_ae b hW hWm T t ht (fun a=>q.path a 0)
      (-BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i=>coefficientMatrix b b (C i)) q.X)
      (fun i a=>q.X.2 a i) q.path q.equation
    rw [hf] at he
    exact he

omit b hW hWm [Fintype κ] [Fintype ι] in
/-- Every ordinary Euclidean/Hilbert strongly progressive finite-energy noise
family has true predictable classes. No noise solutions are lost by the record. -/
theorem ordinary_noise_classes (T : ℝ≥0) (V : ι → ℝ≥0 → Ω → E)
    (hV : ∀ i, IsStronglyProgressive 𝓕 (V i))
    (h2 : ∀ i, MemLp (Function.uncurry (V i)) 2 ((CommonItoCLM.timeMeasure_T T).prod μ)) :
    ∃ Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T), ∀ i,
      (Z i : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (V i) := by
  choose Z hZ using fun i=>ProgressivePredictable.exists_predictable_Lp μ (hV i) T 2 (h2 i)
  exact ⟨Z,hZ⟩

end LinearStochastic.RawBSDECoordinates
