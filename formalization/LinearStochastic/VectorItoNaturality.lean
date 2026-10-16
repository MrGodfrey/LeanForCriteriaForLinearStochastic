import LinearStochastic.LpFiniteTensor

/-! Naturality of the actual constructed vector Itô integral. All process
equalities below are explicitly fixed-time almost-everywhere equalities;
there is no assertion that raw chosen representatives are jointly measurable. -/
noncomputable section
namespace LinearStochastic.VectorItoNaturality
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel ItoExpectedProduct VectorItoProduct LpFiniteTensor

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual vector L² Itô integral: a finite tensor lift of each previously
constructed scalar Itô continuous linear map, summed over noise channels. -/
def vectorLp (T t : ℝ≥0) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) : Lp E 2 μ :=
  ∑ i, lift (mΛ := 𝓕.predictable) (spacetimeMeasure 𝓕 μ T) μ b
    (CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)).toLinearMap (φ i)

theorem vectorLp_coordinates (T t : ℝ≥0)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorLp b hW hWm T t φ = ∑ a, injection μ (b a)
      (∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (coordinate b a (φ i))) := by
  simp only [vectorLp,lift,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  rw [Finset.sum_comm]
  rfl

theorem vectorLp_comp (T t : ℝ≥0) (L : E →L[ℝ] E)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorLp b hW hWm T t (fun i => L.compLp (φ i)) =
      L.compLp (vectorLp b hW hWm T t φ) := by
  change (∑ i, lift (mΛ := 𝓕.predictable) _ _ b _ (L.compLpₗ 2 _ (φ i))) = L.compLpₗ 2 μ (∑ i, lift (mΛ := 𝓕.predictable) _ _ b _ (φ i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact lift_comp (mΛ := 𝓕.predictable) _ _ b _ L (φ i)

/-- The raw martingale version represents exactly the vector Itô L² class at
each fixed time. This does not claim a common null set over all times. -/
theorem vectorProcess_ae_vectorLp (T t : ℝ≥0)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm T φ t =ᵐ[μ] vectorLp b hW hWm T t φ := by
  have hs : ∀ᵐ ω ∂μ, ∀ a,
      sumProcess hW hWm T (fun i => coordinate b a (φ i)) t ω =
        (∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
          (coordinate b a (φ i)) : Lp ℝ 2 μ) ω := by
    rw [ae_all_iff]
    intro a
    have hi : ∀ᵐ ω ∂μ, ∀ i,
        CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i)
          (coordinate b a (φ i)) t ω =
        CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
          (coordinate b a (φ i)) ω := by
      rw [ae_all_iff]
      exact fun i => CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T t (hWm i) _
    filter_upwards [hi,Lp.coeFn_finsetSum Finset.univ
      (fun i => CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
        (coordinate b a (φ i)))] with ω hi hsum
    simp only [sumProcess,hsum,Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  let f : κ → Lp ℝ 2 μ := fun a => ∑ i,
    CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (coordinate b a (φ i))
  have hinj : ∀ᵐ ω ∂μ, ∀ a, injection μ (b a) (f a) ω = f a ω • b a := by
    rw [ae_all_iff]
    exact fun a => injection_ae μ (b a) (f a)
  rw [vectorLp_coordinates]
  filter_upwards [hs,hinj,Lp.coeFn_finsetSum Finset.univ
    (fun a => injection μ (b a) (f a))] with ω hs hinj hsum
  change (∑ a, sumProcess hW hWm T (fun i => coordinate b a (φ i)) t ω • b a) =
    (∑ a, injection μ (b a) (f a)) ω
  rw [hsum]
  simp only [Finset.sum_apply,hinj,hs,f]

/-- Actual Itô integration commutes with a state-space continuous linear map,
as an equality of random variables almost surely at every specified time. -/
theorem vectorProcess_comp_ae (T t : ℝ≥0) (L : E →L[ℝ] E)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm T (fun i => L.compLp (φ i)) t =ᵐ[μ]
      fun ω => L (vectorProcess b hW hWm T φ t ω) := by
  have hleft := vectorProcess_ae_vectorLp b hW hWm T t (fun i => L.compLp (φ i))
  rw [vectorLp_comp] at hleft
  filter_upwards [hleft,L.coeFn_compLp (vectorLp b hW hWm T t φ),
    vectorProcess_ae_vectorLp b hW hWm T t φ] with ω hl hL hr
  rw [hl,hL,hr]

#print axioms vectorProcess_comp_ae
end LinearStochastic.VectorItoNaturality
