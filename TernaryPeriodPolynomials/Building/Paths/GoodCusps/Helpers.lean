module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers

def GoodVertex : BuildingVertices → Prop
  | .inl flag => GoodFlag .plane flag
  | .inr flag => GoodFlag .line flag

def vertexTranslation (matrix : RationalGL3) : VertexChains →ₗ[ℂ] VertexChains :=
  Finsupp.lmapDomain ℂ ℂ (translateVertex matrix)

theorem translateVertex_mul (left right : RationalGL3) (vertex : BuildingVertices) :
    translateVertex (left * right) vertex =
      translateVertex left (translateVertex right vertex) := by
  cases vertex <;> simp [translateVertex, mul_smul]

theorem translateVertex_one (vertex : BuildingVertices) :
    translateVertex 1 vertex = vertex := by
  cases vertex <;> simp [translateVertex]

theorem translateChain_mul (left right : RationalGL3) (chain : EdgeChains) :
    translateChain (left * right) chain =
      translateChain left (translateChain right chain) := by
  change Finsupp.mapDomain (fun edge => (left * right) • edge) chain =
    Finsupp.mapDomain (fun edge => left • edge)
      (Finsupp.mapDomain (fun edge => right • edge) chain)
  simpa only [Function.comp_def, mul_smul] using
    (Finsupp.mapDomain_comp (v := chain) (f := fun edge => right • edge)
      (g := fun edge => left • edge))

theorem translateChain_one (chain : EdgeChains) : translateChain 1 chain = chain := by
  change Finsupp.mapDomain (fun edge => (1 : RationalGL3) • edge) chain = chain
  have function_eq : (fun edge : Edges => (1 : RationalGL3) • edge) = id := by
    funext edge
    exact one_smul _ edge
  rw [function_eq]
  exact Finsupp.mapDomain_id

theorem chainBoundary_single (edge : Edges) (scalar : ℂ) :
    chainBoundary (Finsupp.single edge scalar) =
      scalar • (Finsupp.single (.inl (endpoint .plane edge)) 1 -
        Finsupp.single (.inr (endpoint .line edge)) 1) := by
  simp [chainBoundary]

theorem chainBoundary_translate (matrix : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain matrix chain) =
      vertexTranslation matrix (chainBoundary chain) := by
  induction chain using Finsupp.induction_linear with
  | zero => simp
  | add left right left_ind right_ind => simp_all
  | single edge scalar =>
    simp [translateChain, vertexTranslation, chainBoundary_single, Finsupp.lmapDomain,
      Finsupp.mapDomain_sub, Finsupp.mapDomain_single, translateVertex]

theorem goodChain_zero : GoodChain 0 := by simp [GoodChain]

theorem goodChain_add {left right : EdgeChains}
    (left_good : GoodChain left) (right_good : GoodChain right) :
    GoodChain (left + right) := by
  classical
  intro edge edge_mem
  have := Finsupp.support_add edge_mem
  rcases Finset.mem_union.mp this with left_mem | right_mem
  · exact left_good edge left_mem
  · exact right_good edge right_mem

theorem goodChain_neg {chain : EdgeChains} (chain_good : GoodChain chain) :
    GoodChain (-chain) := by
  simpa only [GoodChain, Finsupp.support_neg] using chain_good

theorem goodChain_sub {left right : EdgeChains}
    (left_good : GoodChain left) (right_good : GoodChain right) :
    GoodChain (left - right) := by
  rw [sub_eq_add_neg]
  exact goodChain_add left_good (goodChain_neg right_good)

theorem goodChain_single (edge : Edges)
    (plane_good : GoodFlag .plane (endpoint .plane edge))
    (line_good : GoodFlag .line (endpoint .line edge)) :
    GoodChain (Finsupp.single edge 1) := by
  intro other other_mem
  have : other = edge := by simpa using other_mem
  subst other
  exact ⟨plane_good, line_good⟩

end TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers
