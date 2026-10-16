import LinearStochastic.BrownianInitialTrivial
import LinearStochastic.ProgressiveControlSection

/-! The paper's original ordinary-progressive forward/adjoint duality, on
its original usual Brownian filtration. The random initial adjoint is proved
to be a deterministic vector almost surely; the control pairing is written
with the supplied ordinary progressive control, not a narrower control class. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.BrownianRawDuality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality ProgressiveControlSection
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit b hW hWm [Fintype κ] [Fintype ι] [CompleteSpace E] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Actual equality of a progressive control and its predictable L² class
preserves the real-time expected observation pairing. -/
theorem raw_pairing (T : ℝ≥0) (v : ℝ≥0 → Ω → U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (obs : ℝ≥0 → Ω → U)
    (hu : (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v) :
    (∫ ω, (∫ s in Ioc 0 (T:ℝ), inner ℝ (u (s.toNNReal,ω)) (obs s.toNNReal ω)) ∂μ) =
      ∫ ω, (∫ s in Ioc 0 (T:ℝ), inner ℝ (v s.toNNReal ω) (obs s.toNNReal ω)) ∂μ := by
  have he := ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp hu
  have hf := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae he)
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  exact congrArg (fun x => inner ℝ x (obs s.toNNReal ω)) hs

/-- Actual raw forward solutions satisfy the real duality formula for any
actual adjoint sections; when its initial value is constant a.s., the initial
term is the deterministic inner product appearing in the manuscript. -/
theorem raw_duality
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v₀ z₀ : E) (ζ η : Ω → E)
    (hζ : StronglyMeasurable[𝓕 0] ζ) (hζ2 : MemLp ζ 2 μ)
    (hz : ζ =ᵐ[μ] fun _ => z₀)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (q : RawSolution b hW hWm T (fun _ => v₀) A B C D v R u X)
    (hY : SectionIntegralSolution b hW hWm T ζ
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η) :
    (∫ ω, inner ℝ (R T ω) (η ω) ∂μ) - inner ℝ v₀ z₀ =
      ∫ ω, (∫ s in Ioc 0 (T:ℝ), inner ℝ (v s.toNNReal ω)
        (B.adjoint (Y (s.toNNReal,ω))+∑ i, (D i).adjoint (Z i (s.toNNReal,ω)))) ∂μ := by
  have hd := SectionLinearDuality.forward_backward_duality_real b hW hWm hpair hchannels
    T A B C D (fun _ => v₀) ζ (R T) η (memLp_const v₀) hζ2
    stronglyMeasurable_const hζ X Y u Z (q.to_section b hW hWm T _ A B C D v R u X) hY
  have hi : (∫ ω, inner ℝ v₀ (ζ ω) ∂μ) = inner ℝ v₀ z₀ := by
    rw [integral_congr_ae (hz.mono (fun _ h => congrArg (inner ℝ v₀) h))]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hi,raw_pairing T v u (fun t ω => B.adjoint (Y (t,ω))+∑ i, (D i).adjoint (Z i (t,ω))) q.control_rep] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hd)


/-- The original usual Brownian filtration supplies the deterministic initial
adjoint value and all real-channel independence. No stronger continuity
version, F₀-triviality or duality premise is added. -/
theorem usual_raw_duality [μ.IsComplete]
    (hB : ∀ i, IsBrownianReal (W i) μ)
    (hInd : iIndepFun (fun i ω t => W i t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v₀ : E) (ζ η : Ω → E)
    (hζ : StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] ζ) (hζ2 : MemLp ζ 2 μ)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
    (X Y : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hB hWm hInd
    RawSolution b (fun i => (hB i).toIsPreBrownianReal) hWm T (fun _ => v₀) A B C D v R u X →
    SectionIntegralSolution b (fun i => (hB i).toIsPreBrownianReal) hWm T ζ
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η →
    ∃ z₀ : E, ζ =ᵐ[μ] (fun _ => z₀) ∧
      (∫ ω, inner ℝ (R T ω) (η ω) ∂μ) - inner ℝ v₀ z₀ =
        ∫ ω, (∫ s in Ioc 0 (T:ℝ), inner ℝ (v s.toNNReal ω)
          (B.adjoint (Y (s.toNNReal,ω))+∑ i, (D i).adjoint (Z i (s.toNNReal,ω)))) ∂μ := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hB hWm hInd
  intro q hY
  obtain ⟨z₀,hz⟩ := BrownianInitialTrivial.vector_initial_constant hB hWm hInd b ζ hζ hζ2
  exact ⟨z₀,hz,raw_duality b (fun i => (hB i).toIsPreBrownianReal) hWm
    (JointUsualBrownianGlobal.pairForward hB hWm hInd) (fun _ _ hij => hInd.indepFun hij)
    T A B C D v₀ z₀ ζ η hζ hζ2 hz v R u X Y Z q hY⟩

end LinearStochastic.BrownianRawDuality

