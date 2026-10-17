module

public import LinearStochastic.JointCylinderGeneration
public import LinearStochastic.JointBrownianDirections
public import LinearStochastic.JointBrownian
public import LinearStochastic.CommonItoCross

@[expose] public section

noncomputable section
namespace LinearStochastic.JointNaturalForward
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

/-- Independent pairs can be regrouped into two independent vectors on the
original probability space; no canonical-space replacement is involved. -/
theorem regroup_independent_pairs {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : ι → Ω → X) (g : ι → Ω → Y)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hp : iIndepFun (fun i ω => (f i ω,g i ω)) μ)
    (hi : ∀ i, IndepFun (f i) (g i) μ) :
    IndepFun (fun ω i => f i ω) (fun ω i => g i ω) μ := by
  have hmap : μ.map (fun ω i => (f i ω,g i ω)) =
      Measure.pi (fun i => (μ.map (f i)).prod (μ.map (g i))) := by
    rw [hp.map_fun_eq_pi_map (fun i => ((hf i).prodMk (hg i)).aemeasurable)]
    congr 1
    funext i
    exact (hi i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
  have hfI : iIndepFun f μ := hp.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hgI : iIndepFun g μ := hp.comp (fun _ => Prod.snd) (fun _ => measurable_snd)
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_lambda hf).aemeasurable (measurable_pi_lambda hg).aemeasurable).mpr
  rw [hfI.map_fun_eq_pi_map (fun i => (hf i).aemeasurable),
    hgI.map_fun_eq_pi_map (fun i => (hg i).aemeasurable)]
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y ι
  have hh := (measurePreserving_arrowProdEquivProdArrow X Y ι
    (fun i => μ.map (f i)) (fun i => μ.map (g i))).map_eq
  rw [←hmap,Measure.map_map e.measurable (by fun_prop)] at hh
  exact hh

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include hW hWm hInd in
/-- The actual vector of all future increments is independent of all channel
histories, using independence of the whole coordinate Brownian processes. -/
theorem joint_future_past (s : ℝ≥0) :
    IndepFun (fun ω i (t : Set.Iic s) => W i t ω)
      (fun ω i (u : ℝ≥0) => W i (s+u) ω - W i s ω) μ := by
  apply regroup_independent_pairs
    (fun i ω (t : Set.Iic s) => W i t ω)
    (fun i ω (u : ℝ≥0) => W i (s+u) ω - W i s ω)
    (fun i => measurable_pi_lambda (fun t => hWm i t))
    (fun i => measurable_pi_lambda (fun u => (hWm i (s+u)).sub (hWm i s)))
  · exact hInd.comp (fun _ f => ((fun t : Set.Iic s => f t),fun u => f (s+u)-f s))
      (fun _ => by fun_prop)
  · intro i
    exact ((hW i).indepFun_shift s).symm

omit [Fintype ι] in
/-- The joint natural past is contained in the sigma algebra of its full past
path. This uses real coordinate evaluations, not a Gaussian law assumption. -/
theorem natural_le_past (s : ℝ≥0) :
    JointCylinderGeneration.natural W hWm s ≤
      MeasurableSpace.comap (fun ω i (t : Set.Iic s) => W i t ω) inferInstance := by
  rw [JointCylinderGeneration.natural_eq]
  refine iSup_le fun i => iSup_le fun t => iSup_le fun ht => ?_
  have he : W i t = (fun f : ι → Set.Iic s → ℝ => f i ⟨t,ht⟩) ∘
      (fun ω i (u : Set.Iic s) => W i u ω) := rfl
  rw [he,←MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (by fun_prop : Measurable (fun f : ι → Set.Iic s → ℝ => f i ⟨t,ht⟩)).comap_le

/-- Any actual linear direction is adapted to the joint natural filtration. -/
theorem direction_adapted (c : ι → ℝ) :
    StronglyAdapted (JointCylinderGeneration.natural W hWm)
      (JointBrownianDirections.direction W c) := by
  intro t
  apply Measurable.stronglyMeasurable
  exact Finset.measurable_sum _ (fun i _ =>
    (JointCylinderGeneration.measurable_natural W hWm i le_rfl).const_mul (c i))

include hW hInd in
/-- Whole-forward-process independence for every actual linear direction in
an arbitrary independent-coordinate Brownian realization. Unit length is only
needed separately when asserting that the direction is standard Brownian. -/
theorem directionForward (c : ι → ℝ) :
    CommonItoIsometry.ForwardIndependent (JointBrownianDirections.direction W c)
      (JointCylinderGeneration.natural W hWm) μ where
  adapted := direction_adapted W hWm c
  indep s := by
    have h := joint_future_past W hW hWm hInd s
    have hm : Measurable (fun f : ι → ℝ≥0 → ℝ => fun u => ∑ i, c i * f i u) := by fun_prop
    have hh := h.comp measurable_id hm
    apply indep_of_indep_of_le_left _ (natural_le_past W hWm s)
    have he : (fun ω u => JointBrownianDirections.direction W c (s+u) ω -
        JointBrownianDirections.direction W c s ω) =
        (fun f : ι → ℝ≥0 → ℝ => fun u => ∑ i, c i * f i u) ∘
          (fun ω i u => W i (s+u) ω - W i s ω) := by
      funext ω u
      simp only [Function.comp_apply,JointBrownianDirections.direction,
        ←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact hh

include hW hInd in
/-- Each actual coordinate has whole-future independence from the full joint past. -/
theorem coordinateForward (i : ι) :
    CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ where
  adapted t := (JointCylinderGeneration.measurable_natural W hWm i le_rfl).stronglyMeasurable
  indep s := by
    have h := (joint_future_past W hW hWm hInd s).comp measurable_id (measurable_pi_apply i)
    exact indep_of_indep_of_le_left h (natural_le_past W hWm s)

include hW hInd in
/-- Pairwise joint-forward independence required by the genuine cross-Itô isometry. -/
theorem pairForward (i j : ι) :
    CommonItoCross.PairForwardIndependent (W i) (W j)
      (JointCylinderGeneration.natural W hWm) μ := by
  intro s
  have h := (joint_future_past W hW hWm hInd s).comp measurable_id
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  exact indep_of_indep_of_le_left h (natural_le_past W hWm s)

end LinearStochastic.JointNaturalForward
