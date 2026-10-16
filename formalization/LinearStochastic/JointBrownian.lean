import BrownianMotion.Gaussian.BrownianMotion
import LinearStochastic.FilteredIto
import Mathlib

/-!
A concrete finite family of independent continuous Brownian coordinates on the
product of the proved Gaussian Brownian path models. The common past contains
all channel histories. Its independence from the whole future increment vector
is derived from genuine product laws, not imposed as a model field.
The final theorem discharges every Gaussian-law and independence hypothesis
of the finite-grid multi-channel Itô isometry. No SDE or continuous-time
predictable-integral conclusion is asserted here.
-/
noncomputable section
namespace LinearStochastic.JointBrownian
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Independent pairs on independent coordinate spaces remain independent after
collecting all first components and all second components. -/
theorem indepFun_pi_pair {ι Ω X Y : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → Ω → X) (g : ι → Ω → Y)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hind : ∀ i, IndepFun (f i) (g i) (μ i)) :
    IndepFun (fun ω : ι → Ω ↦ fun i ↦ f i (ω i))
      (fun ω : ι → Ω ↦ fun i ↦ g i (ω i)) (Measure.pi μ) := by
  have hmap : (Measure.pi μ).map (fun ω i ↦ (f i (ω i), g i (ω i))) =
      Measure.pi (fun i ↦ ((μ i).map (f i)).prod ((μ i).map (g i))) := by
    rw [Measure.pi_map_pi (fun i ↦ ((hf i).prodMk (hg i)).aemeasurable)]
    congr 1
    funext i
    exact (hind i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun i ↦ (hf i).comp (measurable_pi_apply i))).aemeasurable
    (measurable_pi_lambda _ (fun i ↦ (hg i).comp (measurable_pi_apply i))).aemeasurable).mpr
  simp only [Function.comp_apply]
  rw [Measure.pi_map_pi (fun i ↦ (hf i).aemeasurable),
    Measure.pi_map_pi (fun i ↦ (hg i).aemeasurable)]
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y ι
  have hh := (measurePreserving_arrowProdEquivProdArrow X Y ι
    (fun i ↦ (μ i).map (f i)) (fun i ↦ (μ i).map (g i))).map_eq
  rw [← hmap, Measure.map_map e.measurable (by fun_prop)] at hh
  exact hh

variable (ι : Type*) [Fintype ι]

/-- Independent copies of the explicitly constructed continuous Brownian model. -/
def law : Measure (ι → (ℝ≥0 → ℝ)) := Measure.pi (fun _ : ι ↦ gaussianLimit)

instance : IsProbabilityMeasure (law ι) := by unfold law; infer_instance

def process (i : ι) (t : ℝ≥0) (ω : ι → (ℝ≥0 → ℝ)) : ℝ := brownian t (ω i)

def pastPath (t : ℝ≥0) (ω : ι → (ℝ≥0 → ℝ)) (i : ι) (u : Set.Iic t) : ℝ :=
  process ι i u ω

omit [Fintype ι] in
@[fun_prop]
theorem process_measurable (i : ι) (t : ℝ≥0) : Measurable (process ι i t) :=
  (measurable_brownian t).comp (measurable_pi_apply i)

omit [Fintype ι] in
@[fun_prop]
theorem pastPath_measurable (t : ℝ≥0) : Measurable (pastPath ι t) := by
  exact measurable_pi_lambda _ (fun i ↦ measurable_pi_lambda _ (fun u ↦ process_measurable ι i u))

/-- Every coordinate really is Brownian with continuous sample paths. -/
theorem process_isBrownian (i : ι) : IsBrownianReal (process ι i) (law ι) := by
  constructor
  · apply HasLaw.IsPreBrownianReal
    exact hasLaw_brownian.comp (measurePreserving_eval (fun _ : ι ↦ gaussianLimit) i).hasLaw
  · exact Filter.Eventually.of_forall (fun ω ↦ continuous_brownian (ω i))

/-- The entire vector of future increments is independent of the joint past,
including the histories of every Brownian coordinate. -/
theorem joint_past_independent_increment (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (pastPath ι s) (fun ω : ι → (ℝ≥0 → ℝ) ↦ fun i ↦
      process ι i t ω - process ι i s ω) (law ι) := by
  apply indepFun_pi_pair (fun _ : ι ↦ gaussianLimit)
    (fun _ ω (u : Set.Iic s) ↦ brownian u ω)
    (fun _ ω ↦ brownian t ω - brownian s ω)
    (fun _ ↦ measurable_pi_lambda _ (fun u ↦ measurable_brownian u))
    (fun _ ↦ (measurable_brownian t).sub (measurable_brownian s))
  intro i
  have h := isBrownianReal_brownian.toIsPreBrownianReal.indepFun_shift s
  have hh := h.symm.comp measurable_id (measurable_pi_apply (t-s))
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hh

/-- Actual independent channel increments under the same joint probability law. -/
theorem increments_independent (s t : ℝ≥0) :
    iIndepFun (fun i ω ↦ process ι i t ω - process ι i s ω) (law ι) :=
  iIndepFun_pi (fun _ ↦ ((measurable_brownian t).sub (measurable_brownian s)).aemeasurable)

/-- The joint natural past, with a proved monotonicity and ambient inclusion. -/
def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ι → (ℝ≥0 → ℝ))) where
  seq t := MeasurableSpace.comap (pastPath ι t) inferInstance
  mono' := by
    intro s t hst
    have hr : Measurable (fun f : ι → Set.Iic t → ℝ ↦
        fun i (u : Set.Iic s) ↦ f i ⟨u, u.property.trans hst⟩) := by fun_prop
    exact (hr.comp (comap_measurable (pastPath ι t))).comap_le
  le' t := (pastPath_measurable ι t).comap_le

omit [Fintype ι] in
/-- A coordinate at any earlier time is measurable for the common past. -/
theorem process_measurable_past (i : ι) {u t : ℝ≥0} (hut : u ≤ t) :
    Measurable[filtration ι t] (process ι i u) :=
  (measurable_pi_apply (⟨u,hut⟩ : Set.Iic t)).comp
    ((measurable_pi_apply i).comp (comap_measurable (pastPath ι t)))

def gridFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ι → (ℝ≥0 → ℝ))) where
  seq k := filtration ι (τ k)
  mono' _ _ h := (filtration ι).mono (hτ h)
  le' k := (filtration ι).le (τ k)

def gridIncrement (τ : ℕ → ℝ≥0) (k : ℕ) (i : ι) (ω : ι → (ℝ≥0 → ℝ)) : ℝ :=
  process ι i (τ (k+1)) ω - process ι i (τ k) ω

omit [Fintype ι] in
theorem gridIncrement_adapted (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (k : ℕ) (i : ι) :
    Measurable[gridFiltration ι τ hτ (k+1)] (gridIncrement ι τ k i) :=
  (process_measurable_past ι i le_rfl).sub (process_measurable_past ι i (hτ (Nat.le_succ k)))

theorem gridIncrement_law (τ : ℕ → ℝ≥0) (k : ℕ) (i : ι) :
    HasLaw (gridIncrement ι τ k i) (gaussianReal 0 (nndist (τ (k+1)) (τ k))) (law ι) :=
  (process_isBrownian ι i).hasLaw_sub (τ (k+1)) (τ k)

theorem gridIncrement_independent_past (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (k : ℕ) :
    Indep (gridFiltration ι τ hτ k)
      (MeasurableSpace.comap (fun ω i ↦ gridIncrement ι τ k i ω) inferInstance) (law ι) :=
  (joint_past_independent_increment ι (τ k) (τ (k+1)) (hτ (Nat.le_succ k)))

/-- Concrete finite-grid multi-Brownian Itô isometry: the user supplies only
adapted L² coefficients. All Brownian laws and all independence assumptions
are discharged by the actual joint Brownian model constructed above. -/
theorem actual_joint_isometry (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (φ : ℕ → ι → (ι → (ℝ≥0 → ℝ)) → ℝ)
    (hφ : ∀ k i, Measurable[gridFiltration ι τ hτ k] (φ k i))
    (hLp : ∀ k i, MemLp (φ k i) 2 (law ι)) (n : ℕ) :
    (∫ ω, (FilteredIto.Multichannel.sumIntegral φ (gridIncrement ι τ) n ω)^2 ∂law ι) =
      ∑ k : Fin n, ∑ i, (∫ ω, φ k i ω ^ 2 ∂law ι) * nndist (τ (k+1)) (τ k) := by
  exact FilteredIto.Multichannel.sumIntegral_isometry
    (gridFiltration ι τ hτ) φ (gridIncrement ι τ) (fun k _ ↦ nndist (τ (k+1)) (τ k))
    hφ (gridIncrement_adapted ι τ hτ) (gridIncrement_law ι τ)
    (gridIncrement_independent_past ι τ hτ) hLp
    (fun k i j hij ↦ (increments_independent ι (τ k) (τ (k+1))).indepFun hij) n

end LinearStochastic.JointBrownian
