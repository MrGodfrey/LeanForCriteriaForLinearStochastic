import LinearStochastic.HilbertBrownianRealization
import LinearStochastic.VectorH2Extension
import LinearStochastic.CommonSolutionRestriction

/-! Deterministic restart of genuine Hilbert section solutions. The proof uses
actual coordinate integrals and the proved original-Brownian path uniqueness. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertRestartUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution LpOrthonormalCoordinates
open VectorItoProduct LinearDuality SectionLinearDuality HilbertLocalSolution
open HilbertSectionCoordinates HilbertBrownianRealization
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
  (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E)
  (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
    (fun i => (C i).compLp X+(D i).compLp u) X XT)

/-- Every fixed-time value of any supplied actual vector integral path has the
same coordinates as the genuine scalar solution constructed from its sections. -/
theorem coordinateSolution_time (R : ℝ≥0 → Ω → E)
    (hR : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ))
    (j : κ) (t : ℝ≥0) (ht : t ≤ T) :
    (fun ω => inner ℝ (b j) (R t ω)) =ᵐ[μ]
      (coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX).path j t := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  have he := integral_coordinate_ae b (fun i => (hW i).toIsPreBrownianReal) hWm T t
    (by exact_mod_cast ht) ξ (A.compLp X+B.compLp u)
    (fun i => (C i).compLp X+(D i).compLp u) j
  simp only [Real.toNNReal_coe,drift_coordinates b c T A B u X,
    noise_coordinates b c T C D u X] at he
  filter_upwards [hR t ht,he,q.equation j t ht] with ω hr he hq
  rw [hr,he]
  have hd := RealTimeBridge.integral_real_extension t (fun r =>
    driftInput T (coefficientMatrix b b A) (coefficientMatrix b c B)
      (fun j => coordinate c j u) q.X j (r,ω))
  exact (congrArg (fun z : ℝ => inner ℝ (b j) (ξ ω) + z +
    ∑ i, CommonItoProcessGeneral.itoProcessCLM ((hW i).toIsPreBrownianReal) T t (hWm i)
      (noiseInput T (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
        (fun j => coordinate c j u) q.X i j) ω) hd).trans hq.symm

omit hW hWm i₀ hξ hξ2 hX [𝓕.IsComplete μ] [CompleteSpace E] [Fintype ι] in
/-- Translation commutes with the actual orthonormal L² coordinates. -/
theorem coordinate_shift (a δ : ℝ≥0) (h : a+δ ≤ T) (j : κ) :
    coordinate b j (VectorH2Extension.shift b a δ T h X) =
      CommonShiftH2.shiftCLM a δ T h (coordinate b j X) :=
  coordinate_assemble (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b _ j

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

omit b c hξ hξ2 hX [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] in
include i₀ in
/-- Restarted actual scalar solutions are identified by the previously proved
global pathwise uniqueness theorem, with the original shifted Brownian motions. -/
theorem scalar_shift_unique (a δ : ℝ≥0) (h : a+δ ≤ T)
    (M : Matrix κ κ ℝ) (N : Matrix κ τ ℝ) (J : ι → Matrix κ κ ℝ) (K : ι → Matrix κ τ ℝ)
    (ξ₀ ζ : κ → Ω → ℝ)
    (hζ : ∀ j, StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] (ζ j))
    (hζ2 : ∀ j, MemLp (ζ j) 2 μ)
    (u₀ : τ → CommonVectorPicard.H2 𝓕 μ T)
    (v : τ → CommonVectorPicard.H2 (CommonTimeShift.filtration 𝓕 a) μ δ)
    (q : CommonSolutionData.Solution (fun i => (hW i).toIsPreBrownianReal) hWm T M N J K ξ₀ u₀)
    (r : CommonSolutionData.Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i => ((hW i).shift a).toIsPreBrownianReal)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ M N J K ζ v)
    (hi : ∀ j, q.path j a =ᵐ[μ] ζ j)
    (hu : (fun j => CommonShiftH2.shiftCLM a δ T h (u₀ j)) = v) :
    ∀ᵐ ω ∂μ, ∀ j s, s ≤ δ → q.path j (a+s) ω = r.path j s ω := by
  subst v
  let q₀ := CommonSolutionRestriction.shifted (fun i => (hW i).toIsPreBrownianReal) hWm
    a δ T h M N J K ξ₀ u₀ q
  let q₁ := CommonSolutionFixedPoint.withInitial
    (fun i => ((hW i).shift a).toIsPreBrownianReal)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
    δ M N J K (fun j => q.path j a) ζ _ q₀ hi
  exact CommonBrownianGlobal.global_unique (fun i => (hW i).shift a)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) i₀ δ M N J K ζ hζ hζ2 _ q₁ r


include i₀ hξ hξ2 hX in
/-- Actual Hilbert state and control translation identifies the local state
class and every fixed-time path value. No independent SDE or uniqueness
hypothesis is introduced: both paths satisfy the constructed integral equation. -/
theorem restart (a δ : ℝ≥0) (h : a+δ ≤ T)
    (η : Ω → E) (hη : StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] η)
    (hη2 : MemLp η 2 μ)
    (v : Lp U 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
    (Y : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) (YT : Ω → E)
    (hY : SectionIntegralSolution (𝓕:=CommonTimeShift.filtration 𝓕 a) b
      (fun i => ((hW i).shift a).toIsPreBrownianReal)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ η
      (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) Y YT)
    (R S : ℝ≥0 → Ω → E)
    (hR : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ))
    (hS : ∀ t, t ≤ δ → S t =ᵐ[μ] integralState (𝓕:=CommonTimeShift.filtration 𝓕 a) b
      (fun i => ((hW i).shift a).toIsPreBrownianReal)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ η
      (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) (t:ℝ))
    (hstart : R a =ᵐ[μ] η) (hu : VectorH2Extension.shift c a δ T h u = v) :
    VectorH2Extension.shift b a δ T h X = Y ∧
      ∀ s, s ≤ δ → R (a+s) =ᵐ[μ] S s := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  let r := coordinateSolution b c (fun i => (hW i).shift a)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) i₀ δ A B C D η hη hη2 v Y YT hY
  have ha : a ≤ T := (le_add_right le_rfl).trans h
  have hi j : q.path j a =ᵐ[μ] fun ω => inner ℝ (b j) (η ω) :=
    (coordinateSolution_time b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX R hR j a ha).symm.trans
      (hstart.fun_comp (innerSL ℝ (b j)))
  have huv : (fun j => CommonShiftH2.shiftCLM a δ T h (coordinate c j u)) =
      fun j => coordinate c j v := by
    funext j
    exact (coordinate_shift c T u a δ h j).symm.trans (congrArg (coordinate c j) hu)
  have hqr := scalar_shift_unique hW hWm i₀ T a δ h
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
    (fun j ω => inner ℝ (b j) (ξ ω)) (fun j ω => inner ℝ (b j) (η ω))
    (fun j => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hη)
    (fun j => (innerSL ℝ (b j)).comp_memLp' hη2) _ _ q r hi huv
  constructor
  · have heq : (fun j => coordinate b j (VectorH2Extension.shift b a δ T h X)) =
        fun j => coordinate b j Y := by
      funext j
      rw [coordinate_shift]
      let q₀ := CommonSolutionRestriction.shifted (fun i => (hW i).toIsPreBrownianReal) hWm
        a δ T h _ _ _ _ _ _ q
      have hm := CommonProgressiveComparison.product_ae_of_modification δ (q₀.progressive j)
        (r.progressive j) (fun s hs => hqr.mono (fun ω hω => hω j s hs))
      apply Lp.ext
      apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
        (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
      exact (q₀.representative j).trans (hm.trans (r.representative j).symm)
    exact (assemble_coordinates (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b _).symm.trans
      ((congrArg (assemble (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b) heq).trans
        (assemble_coordinates (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b Y))
  · intro s hs
    have hr : ∀ᵐ ω ∂μ, ∀ j, inner ℝ (b j) (R (a+s) ω) = q.path j (a+s) ω := by
      rw [ae_all_iff]
      exact fun j => coordinateSolution_time b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
        R hR j (a+s) ((add_le_add le_rfl hs).trans h)
    have hs' : ∀ᵐ ω ∂μ, ∀ j, inner ℝ (b j) (S s ω) = r.path j s ω := by
      rw [ae_all_iff]
      exact fun j => coordinateSolution_time b c (fun i => (hW i).shift a)
        (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) i₀ δ A B C D η hη hη2 v Y YT hY S hS j s hs
    filter_upwards [hr,hs',hqr] with ω hr hs' hqr
    calc
      R (a+s) ω = ∑ j, inner ℝ (b j) (R (a+s) ω) • b j := (b.sum_repr' _).symm
      _ = ∑ j, inner ℝ (b j) (S s ω) • b j := Finset.sum_congr rfl (fun j _ => by rw [hr j,hs' j,hqr j s hs])
      _ = S s ω := b.sum_repr' _

end LinearStochastic.HilbertRestartUniqueness
