module

public import LinearStochastic.CommonSolutionData

@[expose] public section

/-! Actual deterministic concatenation of two constructed matrix SDE solutions.
The pasted predictable class is obtained from the genuine continuous S² path;
its coefficient restrictions and translated coefficients are then proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSolutionPaste
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem exists_paste (i₀ : ι) (a δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ (a+δ))
    (q : Solution hW hWm a A B C D ξ
      (fun b ↦ restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (u b)))
    (r : Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A B C D (fun b ↦ q.path b a) (fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b))) :
    Nonempty (Solution hW hWm (a+δ) A B C D ξ u) := by
  let R := fun b ↦ CommonProcessPaste.paste a (q.path b) (r.path b)
  have hp (b : κ) : IsProgressive 𝓕 (R b) :=
    CommonProcessPaste.progressive a (q.progressive b) (r.progressive b)
  have hc (b : κ) : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R b t ω) (Iic (a+δ)) := by
    filter_upwards [q.continuous b,r.continuous b,r.initial b] with ω hq hr he
    exact CommonProcessPaste.continuousOn a δ (fun t ↦ q.path b t ω) (fun t ↦ r.path b t ω) hq hr he.symm
  have h2 (b : κ) : MemLp (ContinuousDoobL2.pathSup (R b) (a+δ)) 2 μ :=
    CommonProcessPaste.paste_S2 μ a δ (q.progressive b) (r.progressive b)
      (q.continuous b) (r.continuous b) (r.initial b).symm (q.squareSup b) (r.squareSup b)
  choose Z hZ using fun b ↦ CommonProcessSpace.exists_predictable_H2 (hp b) (a+δ) (hc b) (h2 b)
  have hpre (b : κ) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (Z b) = q.X b :=
    CommonPastedClasses.restriction_paste (hWm i₀) a δ (q.path b) (r.path b) (q.X b) (Z b) (q.representative b) (hZ b)
  have hshift (b : κ) : shiftCLM a δ (a+δ) le_rfl (Z b) = r.X b :=
    CommonPastedClasses.shift_paste a δ (q.path b) (r.path b) (r.X b) (Z b) (r.representative b) (hZ b)
  have hpc (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (b : κ) :
      restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (driftInput (a+δ) M N u Z b) =
      driftInput a M N (fun c ↦ restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (u c)) q.X b := by
    have he := CommonPastedClasses.map_linearInput a (a+δ)
      (show H2 𝓕 μ (a+δ) →L[ℝ] H2 𝓕 μ a from restriction (hWm i₀) (le_add_right le_rfl)) M N Z u b
    exact he.trans (congrArg (fun Y ↦ driftInput a M N
      (fun c ↦ restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (u c)) Y b) (funext hpre))
  have hsc (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (b : κ) :
      shiftCLM a δ (a+δ) le_rfl (driftInput (a+δ) M N u Z b) =
      driftInput δ M N (fun c ↦ shiftCLM a δ (a+δ) le_rfl (u c)) r.X b := by
    have he := CommonPastedClasses.map_linearInput δ (a+δ)
      (show H2 𝓕 μ (a+δ) →L[ℝ] H2 (CommonTimeShift.filtration 𝓕 a) μ δ from shiftCLM a δ (a+δ) le_rfl) M N Z u b
    exact he.trans (congrArg (fun Y ↦ driftInput δ M N
      (fun c ↦ shiftCLM a δ (a+δ) le_rfl (u c)) Y b) (funext hshift))
  refine ⟨⟨Z,R,hp,hc,h2,hZ,?_,?_⟩⟩
  · intro b
    change CommonProcessPaste.paste a (q.path b) (r.path b) 0 =ᵐ[μ] ξ b
    rw [CommonProcessPaste.paste_zero]
    exact q.initial b
  · intro b
    apply CommonIntegralPaste.paste_equation hW hWm i₀ a δ (ξ b)
      (driftInput (a+δ) A B u Z b) (fun i ↦ noiseInput (a+δ) C D u Z i b) (q.path b) (r.path b)
    · have he := q.equation b
      convert he using 1
      · exact hpc A B b
      · funext i
        exact hpc (C i) (D i) b
    · have he := r.equation b
      convert he using 1
      · exact hsc A B b
      · funext i
        exact hsc (C i) (D i) b
end LinearStochastic.CommonSolutionPaste
