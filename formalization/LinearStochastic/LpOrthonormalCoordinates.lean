import LinearStochastic.VectorItoMap

/-! Honest reconstruction of finite scalar L² coordinates into a Hilbert
state, and exact comparison with pointwise coefficient maps. -/
noncomputable section
namespace LinearStochastic.LpOrthonormalCoordinates
open MeasureTheory
open scoped InnerProductSpace BigOperators
open LpFiniteTensor VectorItoProduct

variable {Λ E F κ τ : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fintype κ] [Fintype τ]

def assemble (b : OrthonormalBasis κ ℝ E) (f : κ → Lp ℝ 2 ν) : Lp E 2 ν :=
  ∑ a, injection ν (b a) (f a)

theorem assemble_ae (b : OrthonormalBasis κ ℝ E) (f : κ → Lp ℝ 2 ν) :
    assemble b f =ᵐ[ν] fun z => ∑ a, f a z • b a := by
  have hi : ∀ᵐ z ∂ν, ∀ a, injection ν (b a) (f a) z = f a z • b a := by
    rw [ae_all_iff]
    exact fun a => injection_ae ν (b a) (f a)
  filter_upwards [hi,Lp.coeFn_finsetSum Finset.univ (fun a => injection ν (b a) (f a))]
    with z hi hs
  change (∑ a, injection ν (b a) (f a)) z = _
  rw [hs]
  simp only [Finset.sum_apply,hi]

theorem coordinate_assemble (b : OrthonormalBasis κ ℝ E) (f : κ → Lp ℝ 2 ν) (a : κ) :
    coordinate b a (assemble b f) = f a := by
  apply Lp.ext
  filter_upwards [coordinate_ae b a (assemble b f),assemble_ae b f] with z hc hf
  rw [hc,hf]
  exact b.orthonormal.inner_right_fintype (fun a => f a z) a

theorem assemble_coordinates (b : OrthonormalBasis κ ℝ E) (f : Lp E 2 ν) :
    assemble b (fun a => coordinate b a f) = f := lp_expansion ν b f

/-- Literal matrix action obtained from the two orthonormal bases. -/
theorem assemble_matrix (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ F)
    (L : E →L[ℝ] F) (f : κ → Lp ℝ 2 ν) :
    assemble c (fun a => ∑ j, inner ℝ (c a) (L (b j)) • f j) = L.compLp (assemble b f) := by
  change (∑ a, injection ν (c a) (∑ j, inner ℝ (c a) (L (b j)) • f j)) =
    L.compLpₗ 2 ν (∑ j, injection ν (b j) (f j))
  simp only [map_sum,map_smul,VectorItoMap.comp_injection]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ a, inner ℝ (c a) (L (b j)) • injection ν (c a) (f j)) =
      (injection ν).flip (f j) (∑ a, inner ℝ (c a) (L (b j)) • c a) := by
        simp only [map_sum,map_smul,LinearMap.flip_apply]
    _ = injection ν (L (b j)) (f j) := by rw [c.sum_repr']; rfl

#print axioms assemble_matrix
end LinearStochastic.LpOrthonormalCoordinates
