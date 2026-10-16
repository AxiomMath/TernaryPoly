module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.GraphAction
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeExtObstructionSequences
open CategoryTheory
open OrdinaryIncidenceChains OrdinaryRelativeGraph OrdinaryRelativeGraphAction

abbrev K := GoodBuilding.K
abbrev GoodCyclesRep : Rep ℚ K := Rep.of GoodChainComplex.complex.cyclesAction
abbrev OrdinaryCyclesRep : Rep ℚ K := Rep.of complex.cyclesAction
abbrev QuotientCyclesRep : Rep ℚ K := Rep.of cycleAction
abbrev RelativeEdgesRep : Rep ℚ K := Rep.of edgeAction
abbrev RelativeVerticesRep : Rep ℚ K := Rep.of vertexAction

/-- The genuine equivariant Good-cycle inclusion, bundled in Rep. -/
def goodCycleInclusion : GoodCyclesRep ⟶ OrdinaryCyclesRep :=
  Rep.ofHom ⟨cycleInclusion,fun g => by
    apply LinearMap.ext
    intro c
    exact cycleInclusion_equivariant g c⟩

/-- The genuine quotient by the actual Good cycles. -/
def cycleQuotient : OrdinaryCyclesRep ⟶ QuotientCyclesRep :=
  Rep.ofHom ⟨goodCycles.mkQ,fun _ => rfl⟩

/-- The relative cycle inclusion bundled as an equivariant morphism. -/
def relativeCycleInclusion : QuotientCyclesRep ⟶ RelativeEdgesRep :=
  Rep.ofHom ⟨cycleToEdge,fun g => by
    apply LinearMap.ext
    intro c
    exact cycleToEdge_equivariant g c⟩

/-- The relative incidence boundary bundled as an equivariant morphism. -/
def relativeBoundaryHom : RelativeEdgesRep ⟶ RelativeVerticesRep :=
  Rep.ofHom ⟨relativeBoundary,fun g => by
    apply LinearMap.ext
    intro c
    exact relativeBoundary_equivariant g c⟩

/-- Actual Good cycles, ordinary cycles, and their quotient form a short complex in Rep. -/
def cycleSequence : ShortComplex (Rep ℚ K) :=
  ShortComplex.mk goodCycleInclusion cycleQuotient (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    change goodCycles.mkQ (cycleInclusion c) = 0
    exact (Submodule.Quotient.mk_eq_zero goodCycles).mpr ⟨c,rfl⟩)

/-- The actual relative graph short complex in Rep. -/
def relativeSequence : ShortComplex (Rep ℚ K) :=
  ShortComplex.mk relativeCycleInclusion relativeBoundaryHom (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    change relativeBoundary (cycleToEdge c) = 0
    exact (show cycleToEdge c ∈ relativeBoundary.ker from
      range_cycleToEdge ▸ ⟨c,rfl⟩))

/-- Forgetting the genuine representations reflects exactness, so kernel/range equality suffices. -/
theorem rep_exact_of_range_eq_ker (S : ShortComplex (Rep ℚ K))
    (h : S.f.hom.toLinearMap.range = S.g.hom.toLinearMap.ker) : S.Exact := by
  apply (forget₂ (Rep ℚ K) (ModuleCat ℚ)).reflects_exact_of_faithful S
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  exact h

/-- The Good-to-ordinary cycle sequence is genuinely short exact in the representation category. -/
theorem cycleSequence_shortExact : cycleSequence.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply rep_exact_of_range_eq_ker
    change cycleInclusion.range = LinearMap.ker goodCycles.mkQ
    exact goodCycles.ker_mkQ.symm
  · exact (Rep.mono_iff_injective goodCycleInclusion).mpr cycleInclusion_injective
  · exact (Rep.epi_iff_surjective cycleQuotient).mpr goodCycles.mkQ_surjective

/-- The relative graph sequence is genuinely short exact in the representation category. -/
theorem relativeSequence_shortExact : relativeSequence.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact rep_exact_of_range_eq_ker relativeSequence range_cycleToEdge
  · exact (Rep.mono_iff_injective relativeCycleInclusion).mpr cycleToEdge_injective
  · exact (Rep.epi_iff_surjective relativeBoundaryHom).mpr relativeBoundary_surjective

end TernaryPoly.RelativeExtObstructionSequences
