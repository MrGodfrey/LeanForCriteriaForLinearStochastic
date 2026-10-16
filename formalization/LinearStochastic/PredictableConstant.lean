import LinearStochastic.BSDETerminal
import LinearStochastic.VectorItoProduct

/-! Genuine deterministic constants in the predictable H² space, with exact
norm and coefficient action. These will provide normalized terminal spikes. -/
noncomputable section
namespace LinearStochastic.PredictableConstant
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel
variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

instance finite_spacetime (T : ℝ≥0) : IsFiniteMeasure (spacetimeMeasure 𝓕 μ T) := by
  change IsFiniteMeasure (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod)
  infer_instance

/-- Literal constant, in the actual predictable trim measure. -/
def constant (T : ℝ≥0) (v : E) : Lp E 2 (spacetimeMeasure 𝓕 μ T) :=
  (memLp_const v).toLp (fun _ : ℝ≥0 × Ω ↦ v)

omit [InnerProductSpace ℝ E] in
theorem constant_ae (T : ℝ≥0) (v : E) :
    constant (𝓕:=𝓕) (μ:=μ) T v =ᵐ[spacetimeMeasure 𝓕 μ T] fun _ ↦ v :=
  (memLp_const v).coeFn_toLp

theorem constant_norm_sq (T : ℝ≥0) (v : E) :
    ‖constant (𝓕:=𝓕) (μ:=μ) T v‖^2 = (T : ℝ)*‖v‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  rw [integral_congr_ae ((constant_ae (𝓕:=𝓕) (μ:=μ) T v).mono
    (fun z hz ↦ by rw [hz]))]
  rw [integral_const,real_inner_self_eq_norm_sq,smul_eq_mul]
  congr 1
  change (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod).real univ = _
  rw [Measure.real,trim_measurableSet_eq _ MeasurableSet.univ]
  rw [←univ_prod_univ,Measure.prod_prod,measure_univ (μ:=μ),mul_one]
  exact BSDETerminal.time_mass T

theorem constant_compLp (T : ℝ≥0) (L : E →L[ℝ] F) (v : E) :
    L.compLp (constant (𝓕:=𝓕) (μ:=μ) T v) = constant (𝓕:=𝓕) (μ:=μ) T (L v) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (constant (𝓕:=𝓕) (μ:=μ) T v),
    constant_ae (𝓕:=𝓕) (μ:=μ) T v,constant_ae (𝓕:=𝓕) (μ:=μ) T (L v)] with z hL hv hLv
  rw [hL,hv,hLv]

omit [InnerProductSpace ℝ E] in
theorem constant_add (T : ℝ≥0) (u v : E) :
    constant (𝓕:=𝓕) (μ:=μ) T (u+v) = constant (𝓕:=𝓕) (μ:=μ) T u+constant (𝓕:=𝓕) (μ:=μ) T v := by
  apply Lp.ext
  filter_upwards [constant_ae (𝓕:=𝓕) (μ:=μ) T (u+v),constant_ae (𝓕:=𝓕) (μ:=μ) T u,
    constant_ae (𝓕:=𝓕) (μ:=μ) T v,Lp.coeFn_add (constant (𝓕:=𝓕) (μ:=μ) T u) (constant (𝓕:=𝓕) (μ:=μ) T v)]
    with z huv hu hv ha
  rw [huv,ha,Pi.add_apply,hu,hv]

omit [InnerProductSpace ℝ E] in
theorem constant_zero (T : ℝ≥0) : constant (𝓕:=𝓕) (μ:=μ) T (0:E) = 0 := by
  apply Lp.ext
  exact (constant_ae (𝓕:=𝓕) (μ:=μ) T (0:E)).trans (Lp.coeFn_zero E 2 _).symm

theorem constant_smul (T : ℝ≥0) (r : ℝ) (v : E) :
    constant (𝓕:=𝓕) (μ:=μ) T (r • v) = r • constant (𝓕:=𝓕) (μ:=μ) T v := by
  apply Lp.ext
  filter_upwards [constant_ae (𝓕:=𝓕) (μ:=μ) T (r • v),constant_ae (𝓕:=𝓕) (μ:=μ) T v,
    Lp.coeFn_smul r (constant (𝓕:=𝓕) (μ:=μ) T v)] with z hrv hv hs
  rw [hrv,hs,Pi.smul_apply,hv]

def constantLinear (T : ℝ≥0) : E →ₗ[ℝ] Lp E 2 (spacetimeMeasure 𝓕 μ T) where
  toFun := constant (𝓕:=𝓕) (μ:=μ) T
  map_add' := constant_add T
  map_smul' r v := by simpa only [RingHom.id_apply] using constant_smul (𝓕:=𝓕) (μ:=μ) T r v

/-- Normalizing by the actual time mass gives the exact unit L² energy. -/
theorem normalized_norm_sq (T : ℝ≥0) (hT : 0 < T) (v : E) :
    ‖constant (𝓕:=𝓕) (μ:=μ) T ((Real.sqrt (T:ℝ))⁻¹ • v)‖^2 = ‖v‖^2 := by
  rw [constant_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,
    Real.sq_sqrt T.coe_nonneg]
  have ht : (T:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hT)
  rw [←mul_assoc,mul_inv_cancel₀ ht,one_mul]

end LinearStochastic.PredictableConstant
