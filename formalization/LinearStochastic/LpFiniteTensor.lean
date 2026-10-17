module

public import LinearStochastic.VectorItoProduct

@[expose] public section

/-! The actual finite-coordinate lift of a scalar L² linear map commutes with
finite-dimensional state-space linear maps. This will be instantiated with the
constructed scalar Itô maps, rather than assuming an Itô naturality axiom. -/
noncomputable section
namespace LinearStochastic.LpFiniteTensor
open MeasureTheory
open scoped InnerProductSpace BigOperators
variable {Ω Λ E κ : Type*} [mΩ : MeasurableSpace Ω] [mΛ : MeasurableSpace Λ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype κ]

/-- A fixed state vector times an actual scalar L² random variable, bilinear
in both arguments. -/
def injection (μ : Measure Ω) : E →ₗ[ℝ] Lp ℝ 2 μ →ₗ[ℝ] Lp E 2 μ :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).flip : E →L[ℝ] ℝ →L[ℝ] E).compLpₗ₂ 2 μ

theorem injection_ae (μ : Measure Ω) (v : E) (f : Lp ℝ 2 μ) :
    injection μ v f =ᵐ[μ] fun ω => f ω • v :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLp f

theorem comp_injection (μ : Measure Ω) (L : E →L[ℝ] E) (v : E) (f : Lp ℝ 2 μ) :
    L.compLpₗ 2 μ (injection μ v f) = injection μ (L v) f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (injection μ v f),injection_ae μ v f,
    injection_ae μ (L v) f] with ω hL hv hLv
  change L.compLp (injection μ v f) ω = injection μ (L v) f ω
  rw [hL,hv,hLv,map_smul]

theorem coordinate_injection (μ : Measure Ω) (b : OrthonormalBasis κ ℝ E)
    (a : κ) (v : E) (f : Lp ℝ 2 μ) :
    (innerSL ℝ (b a)).compLpₗ 2 μ (injection μ v f) = inner ℝ (b a) v • f := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ (b a)).coeFn_compLp (injection μ v f),
    injection_ae μ v f,Lp.coeFn_smul (inner ℝ (b a) v) f] with ω hc hv hs
  change (innerSL ℝ (b a)).compLp (injection μ v f) ω = (inner ℝ (b a) v • f) ω
  rw [hc,hv,hs]
  change inner ℝ (b a) (f ω • v) = inner ℝ (b a) v * f ω
  rw [inner_smul_right,mul_comm]

/-- Exact basis reconstruction of a vector-valued L² equivalence class. -/
theorem lp_expansion (μ : Measure Ω) (b : OrthonormalBasis κ ℝ E) (f : Lp E 2 μ) :
    (∑ a, injection μ (b a) ((innerSL ℝ (b a)).compLpₗ 2 μ f)) = f := by
  apply Lp.ext
  have hc : ∀ᵐ ω ∂μ, ∀ a, (innerSL ℝ (b a)).compLp f ω = inner ℝ (b a) (f ω) := by
    rw [ae_all_iff]
    exact fun a => (innerSL ℝ (b a)).coeFn_compLp f
  have hi : ∀ᵐ ω ∂μ, ∀ a, injection μ (b a) ((innerSL ℝ (b a)).compLpₗ 2 μ f) ω =
      ((innerSL ℝ (b a)).compLp f ω) • b a := by
    rw [ae_all_iff]
    exact fun a => injection_ae μ (b a) _
  filter_upwards [hc,hi,Lp.coeFn_finsetSum Finset.univ
    (fun a => injection μ (b a) ((innerSL ℝ (b a)).compLpₗ 2 μ f))] with ω hc hi hs
  rw [hs]
  simp only [Finset.sum_apply,hi,hc]
  exact b.sum_repr' (f ω)

/-- Actual finite-coordinate lift of a scalar L² map. -/
def lift (ν : Measure Λ) (μ : Measure Ω) (b : OrthonormalBasis κ ℝ E)
    (S : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ) : Lp E 2 ν →ₗ[ℝ] Lp E 2 μ :=
  ∑ a, (injection μ (b a)).comp (S.comp ((innerSL ℝ (b a)).compLpₗ 2 ν))

theorem lift_injection (ν : Measure Λ) (μ : Measure Ω) (b : OrthonormalBasis κ ℝ E)
    (S : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ) (v : E) (f : Lp ℝ 2 ν) :
    lift ν μ b S (injection ν v f) = injection μ v (S f) := by
  simp only [lift,LinearMap.sum_apply,LinearMap.comp_apply,coordinate_injection,map_smul]
  calc
    (∑ a, inner ℝ (b a) v • injection μ (b a) (S f)) =
        (injection μ).flip (S f) (∑ a, inner ℝ (b a) v • b a) := by
      simp only [map_sum,map_smul,LinearMap.flip_apply]
    _ = injection μ v (S f) := by rw [b.sum_repr']; rfl

/-- State-space linear maps commute with the actual coordinate lift. -/
theorem lift_comp (ν : Measure Λ) (μ : Measure Ω) (b : OrthonormalBasis κ ℝ E)
    (S : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ) (L : E →L[ℝ] E) (f : Lp E 2 ν) :
    lift ν μ b S (L.compLpₗ 2 ν f) = L.compLpₗ 2 μ (lift ν μ b S f) := by
  have he := (lp_expansion ν b f).symm
  rw [he]
  simp only [map_sum,comp_injection,lift_injection]

#print axioms lift_comp
end LinearStochastic.LpFiniteTensor
