module

public import LinearStochastic.ContinuousSubspace
public import LinearStochastic.VectorItoProduct

@[expose] public section

/-! An explicit continuous path version of a predictable L² state, including
its two separately specified endpoint values. This contains no equation or
controllability conclusion; actual SDE existence must construct this data. -/
noncomputable section
namespace LinearStochastic
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open CommonItoMultichannel

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 mΩ}

structure ContinuousRealization (T : ℝ≥0) (ξ : Ω → E)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E) where
  path : ℝ → Ω → E
  continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t => path t ω) (Icc 0 (T : ℝ))
  spacetime : Function.uncurry path =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod μ]
    fun z => X (z.1.toNNReal,z.2)
  initial : ξ =ᵐ[μ] path 0
  terminal : XT =ᵐ[μ] path (T : ℝ)

namespace ContinuousRealization
variable [IsProbabilityMeasure μ] [FiniteDimensional ℝ E]

/-- Subspace membership of the predictable equivalence class forces the
entire continuous version, on one event of probability one, into that space. -/
theorem path_mem (T : ℝ≥0) (hT : 0 < T) (ξ XT : Ω → E)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (r : ContinuousRealization T ξ X XT) (V : Submodule ℝ E)
    (hX : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, X z ∈ V) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 (T : ℝ), r.path t ω ∈ V := by
  have hamb := ae_of_ae_trim 𝓕.predictable_le_prod hX
  have hreal := ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hamb
  apply ContinuousSubspace.process_mem_subspace_every_time μ T (by exact_mod_cast hT) V
    r.path r.continuous
  filter_upwards [r.spacetime,hreal] with z he hm
  change r.path z.1 z.2 = X (z.1.toNNReal,z.2) at he
  rw [he]
  exact hm

/-- Both endpoints are recovered from the continuous representative; this
does not assign endpoint values to a mere spacetime equivalence class. -/
theorem endpoints_mem (T : ℝ≥0) (hT : 0 < T) (ξ XT : Ω → E)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (r : ContinuousRealization T ξ X XT) (V : Submodule ℝ E)
    (hX : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, X z ∈ V) :
    (∀ᵐ ω ∂μ, ξ ω ∈ V) ∧ ∀ᵐ ω ∂μ, XT ω ∈ V := by
  have hp := r.path_mem T hT ξ XT X V hX
  constructor
  · filter_upwards [hp,r.initial] with ω hp hi
    rw [hi]
    exact hp 0 ⟨le_rfl,T.coe_nonneg⟩
  · filter_upwards [hp,r.terminal] with ω hp ht
    rw [ht]
    exact hp T ⟨T.coe_nonneg,le_rfl⟩
end ContinuousRealization
end LinearStochastic
