import LinearStochastic.BSDEPathData

/-! Exact concatenation of actual backward solutions. Noise classes are pasted
using genuine predictable L² construction, not an assumed global coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEPathPaste
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard BSDEMatrixPicard BSDEPathData
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple CommonH2Paste
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [IsProbabilityMeasure μ] in
/-- Every actual scalar linear map commutes with the literal adjoint driver. -/
theorem map_driver {𝓖 : Filtration ℝ≥0 mΩ} (t T : ℝ≥0)
    (L : H2 𝓕 μ T →L[ℝ] H2 𝓖 μ t)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) (b : κ) :
    L (driver T A C X b) = driver t A C
      ((fun c ↦ L (X.1 c)),fun c ↦ WithLp.toLp 2 (fun i ↦ L (X.2 c i))) b := by
  simp only [driver_apply,map_add,map_sum,map_smul]

/-- Genuine backward solutions on adjacent deterministic intervals concatenate,
provided their actual endpoint sections coincide. -/
theorem exists_paste (i₀ : ι) (a δ : ℝ≥0) (hδ : 0 < δ)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η₀ η : κ → Lp ℝ 2 μ)
    (q : Solution (𝓕:=𝓕) hW hWm a A C η₀)
    (r : Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A C η)
    (he : ∀ b, q.path b a =ᵐ[μ] r.path b 0) :
    Nonempty (Solution (𝓕:=𝓕) hW hWm (a+δ) A C η) := by
  let R := fun b ↦ CommonProcessPaste.paste a (q.path b) (r.path b)
  have hp (b : κ) : IsProgressive 𝓕 (R b) :=
    CommonProcessPaste.progressive a (q.progressive b) (r.progressive b)
  have hc (b : κ) : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R b t ω) (Iic (a+δ)) := by
    filter_upwards [q.continuous b,r.continuous b,he b] with ω hq hr he
    exact CommonProcessPaste.continuousOn a δ (fun t ↦ q.path b t ω) (fun t ↦ r.path b t ω) hq hr he
  have h2 (b : κ) : MemLp (ContinuousDoobL2.pathSup (R b) (a+δ)) 2 μ :=
    CommonProcessPaste.paste_S2 μ a δ (q.progressive b) (r.progressive b)
      (q.continuous b) (r.continuous b) (he b) (q.squareSup b) (r.squareSup b)
  choose Z hZ using fun b ↦ CommonProcessSpace.exists_predictable_H2 (hp b) (a+δ) (hc b) (h2 b)
  let X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) (a+δ) :=
    (Z,fun b ↦ WithLp.toLp 2 (fun i ↦ pasteH2 a δ (q.X.2 b i) (r.X.2 b i)))
  have hpre (b : κ) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (X.1 b) = q.X.1 b :=
    CommonPastedClasses.restriction_paste (hWm i₀) a δ (q.path b) (r.path b) (q.X.1 b) (Z b) (q.representative b) (hZ b)
  have hshift (b : κ) : shiftCLM a δ (a+δ) le_rfl (X.1 b) = r.X.1 b :=
    CommonPastedClasses.shift_paste a δ (q.path b) (r.path b) (r.X.1 b) (Z b) (r.representative b) (hZ b)
  have hnpre (b : κ) (i j : ι) :
      restriction (hWm j) (show a ≤ a+δ from le_add_right le_rfl) (X.2 b i) = q.X.2 b i :=
    restriction_pasteH2 (hWm j) a δ (q.X.2 b i) (r.X.2 b i)
  have hnshift (b : κ) (i : ι) : shiftCLM a δ (a+δ) le_rfl (X.2 b i) = r.X.2 b i :=
    shift_pasteH2 a δ (q.X.2 b i) (r.X.2 b i)
  have hpc (b : κ) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl)
      (-driver (a+δ) A C X b) = -driver a A C q.X b := by
    simp only [map_neg,driver_apply,map_add,map_sum,map_smul,hpre,hnpre]
  have hsc (b : κ) : shiftCLM a δ (a+δ) le_rfl
      (-driver (a+δ) A C X b) = -driver δ A C r.X b := by
    simp only [map_neg,driver_apply,map_add,map_sum,map_smul,hshift,hnshift]
  refine ⟨⟨X,R,hp,hc,h2,hZ,?_,?_⟩⟩
  · intro b
    change CommonProcessPaste.paste a (q.path b) (r.path b) (a+δ) =ᵐ[μ] η b
    rw [CommonProcessPaste.paste_terminal a δ hδ]
    exact r.terminal b
  · intro b
    have hh := CommonIntegralPaste.paste_equation hW hWm i₀ a δ (q.path b 0)
      (-driver (a+δ) A C X b) (fun i ↦ X.2 b i) (q.path b) (r.path b)
    have hq : CommonIntegralPaste.IntegralEquation hW hWm a (q.path b 0)
        (restriction (hWm i₀) (le_add_right le_rfl) (-driver (a+δ) A C X b))
        (fun i ↦ restriction (hWm i) (le_add_right le_rfl) (X.2 b i)) (q.path b) := by
      simpa only [hpc,hnpre] using q.equation b
    have hr : CommonIntegralPaste.IntegralEquation (𝓕:=CommonTimeShift.filtration 𝓕 a)
        (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
        δ (q.path b a) (shiftCLM a δ (a+δ) le_rfl (-driver (a+δ) A C X b))
        (fun i ↦ shiftCLM a δ (a+δ) le_rfl (X.2 b i)) (r.path b) := by
      simp only [hsc,hnshift]
      intro t ht
      filter_upwards [r.equation b t ht,he b] with ω hr he
      exact hr.trans (by rw [he])
    have hh := hh hq hr
    simpa only [R,CommonProcessPaste.paste_zero] using hh

end LinearStochastic.BSDEPathPaste
