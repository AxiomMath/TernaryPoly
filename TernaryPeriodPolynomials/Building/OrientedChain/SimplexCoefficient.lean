module

public import TernaryPeriodPolynomials.Building.OrientedChain.VertexChains
public import TernaryPeriodPolynomials.Building.OrientedChain.VertexExtraction
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedSimplexCoefficient
open OrientedListChains OrientedChainJoin OrientedVertexChains OrientedVertexExtraction
variable {V W I : Type*}

/-- Exact ordered simplex coefficient, obtained by vertex contractions and empty-list evaluation. -/
def coefficient (l : List V) : Chain V →ₗ[ℚ] ℚ := emptyCoefficient.comp (extract l)

theorem extract_simplex_self (l : List V) (hl : l.Nodup) :
    extract l (simplex l) = simplex [] := by
  have h := extract_join l hl (simplex [])
    (fun a _ => atVertex_simplex_of_not_mem a [] (by simp))
  simpa only [join_simplex,List.append_nil] using h

@[simp] theorem coefficient_self (l : List V) (hl : l.Nodup) :
    coefficient l (simplex l) = 1 := by
  simp only [coefficient,LinearMap.comp_apply,extract_simplex_self l hl,emptyCoefficient_nil]

/-- A nonrepeated simplex is genuinely nonzero in the alternating quotient. -/
theorem simplex_ne_zero (l : List V) (hl : l.Nodup) : simplex l ≠ 0 := by
  intro h
  have he := coefficient_self l hl
  rw [h,map_zero] at he
  exact zero_ne_one he

/-- Zero of a scalar multiple is detected without assuming a basis of the quotient. -/
theorem scalar_simplex_eq_zero_iff (l : List V) (hl : l.Nodup) (q : ℚ) :
    q • simplex l = 0 ↔ q = 0 := by
  rw [smul_eq_zero]
  exact or_iff_left (simplex_ne_zero l hl)

/-- A finite family with one literal projected orientation has projected chain equal to
its total coefficient times that nondegenerate base simplex. -/
theorem map_combination (f : V → W) (l : I → List V) (b : List W)
    (hl : ∀ i, (l i).map f = b) (z : I →₀ ℚ) :
    OrientedChainMap.map f (Finsupp.linearCombination ℚ (fun i => simplex (l i)) z) =
      coefficientSum z • simplex b := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw,add_smul]
  | single i q =>
    simp only [Finsupp.linearCombination_single,map_smul,OrientedChainMap.map_simplex,
      hl,coefficientSum_single]

/-- Projected zero forces the actual finite coherent coefficient sum to vanish. -/
theorem coefficientSum_eq_zero_of_map (f : V → W) (l : I → List V) (b : List W)
    (hb : b.Nodup) (hl : ∀ i, (l i).map f = b) (z : I →₀ ℚ)
    (hz : OrientedChainMap.map f
      (Finsupp.linearCombination ℚ (fun i => simplex (l i)) z) = 0) :
    coefficientSum z = 0 := by
  rw [map_combination f l b hl z] at hz
  exact (scalar_simplex_eq_zero_iff b hb _).mp hz

end TernaryPoly.OrientedSimplexCoefficient
