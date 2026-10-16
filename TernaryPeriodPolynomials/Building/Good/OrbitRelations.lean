module

public import TernaryPeriodPolynomials.Building.Good.OrbitSpan
public import TernaryPeriodPolynomials.Building.Reference.ApartmentRelations

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodOrbitRelations
open GoodBuilding GoodChainComplex GoodUnimodularOrbit GoodOrbitSpan
open ReferenceCoefficientMatrices ReferenceApartmentRelations

abbrev FreeOrbit := K →₀ ℚ

def delta (g : K) : FreeOrbit := Finsupp.single g 1

/-- The actual orbit map from the free rational group module to graph cycles. -/
def orbitMap : FreeOrbit →ₗ[ℚ] GoodChainComplex.Cycles :=
  Finsupp.lsum ℚ fun g => LinearMap.toSpanSingleton ℚ _
    (complex.cyclesAction g referenceApartment)

@[simp] theorem orbitMap_delta (g : K) :
    orbitMap (delta g) = complex.cyclesAction g referenceApartment := by
  simp only [orbitMap,delta,Finsupp.lsum_single,LinearMap.toSpanSingleton_apply,one_smul]

/-- The three exact reference relations, translated on the left by an arbitrary element. -/
def normRelation (g : K) : FreeOrbit := delta g + delta (g*aK) + delta (g*aK^2)
def cyclicRelation (g : K) : FreeOrbit := delta (g*cK) - delta g
def swapRelation (g : K) : FreeOrbit := delta (g*sK) + delta g

def relations : Submodule ℚ FreeOrbit := Submodule.span ℚ
  (Set.range normRelation ∪ Set.range cyclicRelation ∪ Set.range swapRelation)

theorem normRelation_mem_ker (g : K) : normRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,normRelation,map_add,map_add,orbitMap_delta,
    orbitMap_delta,orbitMap_delta]
  simpa only [map_add,map_mul,Module.End.mul_apply,map_zero] using
    congrArg (complex.cyclesAction g) reference_norm

theorem cyclicRelation_mem_ker (g : K) : cyclicRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,cyclicRelation,map_sub,orbitMap_delta,orbitMap_delta,
    map_mul,Module.End.mul_apply,reference_c,sub_self]

theorem swapRelation_mem_ker (g : K) : swapRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,swapRelation,map_add,orbitMap_delta,orbitMap_delta,
    map_mul,Module.End.mul_apply,reference_s,map_neg,neg_add_cancel]

/-- The easy inclusion holds for the actual integral reference relations. -/
theorem relations_le_ker : relations ≤ LinearMap.ker orbitMap := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with (⟨g,rfl⟩ | ⟨g,rfl⟩) | ⟨g,rfl⟩
  · exact normRelation_mem_ker g
  · exact cyclicRelation_mem_ker g
  · exact swapRelation_mem_ker g

/-- Surjectivity is the proved all-determinant orbit spanning theorem. -/
theorem orbitMap_surjective : Function.Surjective orbitMap := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← orbitSpan_eq_top]
  apply Submodule.span_le.mpr
  rintro c ⟨g,rfl⟩
  exact ⟨delta g,orbitMap_delta g⟩

end TernaryPoly.GoodOrbitRelations
