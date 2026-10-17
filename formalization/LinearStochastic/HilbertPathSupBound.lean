module

public import LinearStochastic.PathSupNorm
public import LinearStochastic.VectorItoProduct

@[expose] public section

/-! Exact orthonormal-coordinate estimates for the actual Hilbert S² norm.
The path norm is the original Hilbert norm, not the Pi maximum norm used in
intermediate finite-coordinate Picard estimates. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertPathSupBound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open ContinuousDoobL2 VectorItoProduct
variable {Ω E κ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] (b : OrthonormalBasis κ ℝ E)

omit [CompleteSpace E] in
/-- Each genuine orthonormal coordinate contracts the L² norm. -/
theorem coordinate_norm (j : κ) (f : Lp E 2 μ) : ‖coordinate b j f‖ ≤ ‖f‖ := by
  simpa only [coordinate,innerSL_apply_norm,b.norm_eq_one,one_mul] using
    (innerSL ℝ (b j)).norm_compLp_le f

omit [CompleteSpace E] in
/-- The intermediate Pi norm of all coordinates is bounded by the actual
Hilbert-valued L² norm, including zero-dimensional state or control spaces. -/
theorem coordinates_norm (f : Lp E 2 μ) : ‖fun j=>coordinate b j f‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr (fun j=>coordinate_norm b j f)

omit [CompleteSpace E] in
/-- The initial coordinate classes are exactly the coordinates of the given
random variable's own L² class. -/
theorem initial_coordinate (ξ : Ω → E) (hξ : MemLp ξ 2 μ) (j : κ) :
    ((innerSL ℝ (b j)).comp_memLp' hξ).toLp (fun ω=>inner ℝ (b j) (ξ ω)) =
      coordinate b j (hξ.toLp ξ) := by
  apply Lp.ext
  filter_upwards [((innerSL ℝ (b j)).comp_memLp' hξ).coeFn_toLp,
    coordinate_ae b j (hξ.toLp ξ),hξ.coeFn_toLp] with ω hi hc hξ
  simpa only [Function.comp_def,innerSL_apply_apply] using hi.trans (by rw [hc,hξ]; rfl)

omit mΩ [CompleteSpace E] in
/-- Multiplying a scalar path by an orthonormal basis vector preserves its
actual supremum, before any probability or expectation is taken. -/
theorem basis_pathSup (j : κ) (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    pathSup (fun t ω=>X t ω • b j) T=pathSup X T := by
  funext ω
  unfold pathSup
  congr 1
  funext t
  rw [norm_smul,b.norm_eq_one,mul_one]

omit [CompleteSpace E] in
/-- Reconstructing the actual Hilbert path gives a full S² norm bounded by
the sum of its scalar-coordinate S² norms. -/
theorem reconstruction {𝓕 : Filtration ℝ≥0 mΩ} [IsProbabilityMeasure μ]
    (T : ℝ≥0) (X : κ → ℝ≥0 → Ω → ℝ)
    (ha : ∀ j, StronglyAdapted 𝓕 (X j))
    (hc : ∀ j, ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X j t ω) (Iic T))
    (h2 : ∀ j, MemLp (pathSup (X j) T) 2 μ) :
    PathSupNorm.norm (μ:=μ) (fun t ω=>∑ j,X j t ω • b j) T ≤
      ∑ j, PathSupNorm.norm (μ:=μ) (X j) T := by
  have hc' (j : κ) : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X j t ω • b j) (Iic T) :=
    (hc j).mono (fun _ h=>(h.smul continuousOn_const))
  have hh := PathSupNorm.sum_le (𝓕:=𝓕) Finset.univ T (fun j t ω=>X j t ω • b j)
    (fun j _ t=>(ha j t).smul_const (b j)) (fun j _=>hc' j)
    (fun j _=>by rw [basis_pathSup b j]; exact h2 j)
  simpa only [PathSupNorm.norm,basis_pathSup] using hh

end LinearStochastic.HilbertPathSupBound
