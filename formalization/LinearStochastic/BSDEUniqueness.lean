import LinearStochastic.BSDELocal

/-! Genuine initial-value H² decomposition and terminal boundary imply the
actual backward Picard equation. Uniqueness is therefore not restricted to
objects that merely assume a fixed-point equation. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEUniqueness
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard BSDEIntegralRange BSDEProcessLift BSDEMatrixPicard
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Equality of genuine initial conditional projections determines the actual
constant predictable lifts. -/
theorem initialLift_eq_of_projection_eq (T : ℝ≥0) (χ ψ : Lp ℝ 2 μ)
    (h : initialProjection (𝓕:=𝓕) χ = initialProjection (𝓕:=𝓕) ψ) :
    initialLift (𝓕:=𝓕) T χ = initialLift (𝓕:=𝓕) T ψ := by
  have hz : initialProjection (𝓕:=𝓕) (χ-ψ) = 0 := by
    change ((condExpL2 ℝ ℝ (𝓕.le 0) (χ-ψ)) : Lp ℝ 2 μ) = 0
    rw [map_sub,Submodule.coe_sub]
    exact sub_eq_zero.mpr h
  have he := initialLift_norm_sq (𝓕:=𝓕) T (χ-ψ)
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,initialLift_sub] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (initialLift (𝓕:=𝓕) T χ-initialLift T ψ)]))

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- An actual initial-value integral decomposition and terminal boundary imply
Picard. The unknown initial F₀ variable is determined from the true Ito range,
not assumed to equal the desired conditional expectation. -/
theorem decomposition_implies_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η ξ : κ → Lp ℝ 2 μ)
    (hξ : ∀ a, AEStronglyMeasurable[𝓕 0] (ξ a) μ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (hstate : ∀ a, X.1 a = initialLift T (ξ a) + drift hWm i₀ T (-(driver T A C X a)) +
      ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (X.2 a i))
    (hterminal : ∀ a, η a = ξ a + BSDETerminal.terminal 𝓕 T (-(driver T A C X a)) +
      integral hW hWm hpair hchannels T (X.2 a)) :
    BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X := by
  have hd (a : κ) : terminalInput T (η a) (driver T A C X a) =
      ξ a + integral hW hWm hpair hchannels T (X.2 a) := by
    rw [terminalInput,hterminal a,map_neg]
    abel
  have hc (a : κ) : coefficients hW hWm hpair hchannels T
      (terminalInput T (η a) (driver T A C X a)) = X.2 a :=
    coefficients_of_decomposition hW hWm hpair hchannels T _ (ξ a) (hξ a) (X.2 a) (hd a)
  have hi (a : κ) : initialLift (𝓕:=𝓕) T (terminalInput T (η a) (driver T A C X a)) = initialLift T (ξ a) := by
    apply initialLift_eq_of_projection_eq
    rw [initial_of_decomposition hW hWm hpair hchannels T _ (ξ a) (hξ a) (X.2 a) (hd a),
      initialProjection_of_measurable (ξ a) (hξ a)]
  apply Prod.ext
  · funext a
    change stateStep hW hWm hWc hpair hchannels i₀ T (η a) (driver T A C X a) = X.1 a
    rw [stateStep,assembled,hi a,hc a,hstate a,map_neg]
    abel
  · funext a
    exact hc a

/-- Two actual H² backward integral solutions with the same terminal value have
identical state and channel-Hilbert diffusion classes on a contraction interval. -/
theorem decomposition_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η ξ ζ : κ → Lp ℝ 2 μ)
    (hξ : ∀ a, AEStronglyMeasurable[𝓕 0] (ξ a) μ)
    (hζ : ∀ a, AEStronglyMeasurable[𝓕 0] (ζ a) μ)
    (X Y : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (hc : BSDEMatrixPicard.rate T A C < 1)
    (hX : ∀ a, X.1 a = initialLift T (ξ a) + drift hWm i₀ T (-(driver T A C X a)) +
      ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (X.2 a i))
    (htX : ∀ a, η a = ξ a + BSDETerminal.terminal 𝓕 T (-(driver T A C X a)) +
      integral hW hWm hpair hchannels T (X.2 a))
    (hY : ∀ a, Y.1 a = initialLift T (ζ a) + drift hWm i₀ T (-(driver T A C Y a)) +
      ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (Y.2 a i))
    (htY : ∀ a, η a = ζ a + BSDETerminal.terminal 𝓕 T (-(driver T A C Y a)) +
      integral hW hWm hpair hchannels T (Y.2 a)) : X = Y := by
  have hx := decomposition_implies_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η ξ hξ X hX htX
  have hy := decomposition_implies_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η ζ hζ Y hY htY
  obtain ⟨Z,_,hz⟩ := BSDEMatrixPicard.exists_unique_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η hc
  exact (hz X hx).trans (hz Y hy).symm

end LinearStochastic.BSDEUniqueness
