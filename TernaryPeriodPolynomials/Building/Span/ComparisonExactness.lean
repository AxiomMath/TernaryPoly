module

public import TernaryPeriodPolynomials.Building.Span.ChainComparison
public import TernaryPeriodPolynomials.Building.Ambient.TwoFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.SpanComparisonExactness
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open GoodRelativeChains SpanChainComparison

/-- The exact proper-span kernel needed by the relative comparison. -/
def ProperKernelFilling : Prop :=
  ∀ z : Chain RationalLine, z ∈ chains good 2 → boundary z = 0 → edgeMap z = 0 →
    ∃ q : Chain RationalLine, q ∈ chains properGood 3 ∧ boundary q = z

/-- Actual Good H2 filling identifies the relative null module once the proper edge kernel fills. -/
theorem ker_spanCycleMap (hproper : ProperKernelFilling) :
    LinearMap.ker spanCycleMap = nullSubmodule := by
  apply le_antisymm ?_ nullSubmodule_le_ker
  intro c hc
  have he : edgeMap (boundary c.val) = 0 := congrArg Subtype.val hc
  obtain ⟨q,hq,hdq⟩ := hproper (boundary c.val)
    (boundary_mem_chains good 2 c.property) (boundary_squared c.val) he
  have hqgood := chains_mono properGood_le_good 3 hq
  have hcycle : boundary (c.val-q) = 0 := by rw [map_sub,hdq,sub_self]
  obtain ⟨b,hb,hdb⟩ := AmbientTwoFilling.good_two_filling
    ((chains good 3).sub_mem c.property hqgood) hcycle
  have hqm : properInclusion ⟨q,hq⟩ ∈ nullSubmodule :=
    (show properSubmodule ≤ nullSubmodule from le_sup_left) ⟨⟨q,hq⟩,rfl⟩
  have hbm : differential good 3 ⟨b,hb⟩ ∈ nullSubmodule :=
    (show (differential good 3).range ≤ nullSubmodule from le_sup_right) ⟨⟨b,hb⟩,rfl⟩
  have hdecomp : c = properInclusion ⟨q,hq⟩ + differential good 3 ⟨b,hb⟩ := by
    apply Subtype.ext
    change c.val = q + boundary b
    rw [hdb]
    abel
  rw [hdecomp]
  exact nullSubmodule.add_mem hqm hbm

/-- The actual relative-to-incidence comparison is injective under precisely the proper-kernel input. -/
theorem comparison_injective (hproper : ProperKernelFilling) : Function.Injective comparison := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x
  refine Submodule.Quotient.induction_on nullSubmodule x ?_
  intro c hc
  apply (Submodule.Quotient.mk_eq_zero nullSubmodule).mpr
  rw [← ker_spanCycleMap hproper]
  exact hc

/-- The two actual orbit maps have the same kernel once comparison exactness is supplied. -/
theorem orbit_kernels_eq (hproper : ProperKernelFilling) :
    LinearMap.ker GoodOrbitRelations.orbitMap = LinearMap.ker GoodRelativeChains.orbitMap := by
  ext x
  change GoodOrbitRelations.orbitMap x = 0 ↔ GoodRelativeChains.orbitMap x = 0
  have he := LinearMap.congr_fun comparison_orbitMap x
  change comparison (GoodRelativeChains.orbitMap x) = GoodOrbitRelations.orbitMap x at he
  rw [← he]
  exact ⟨fun h => comparison_injective hproper (h.trans (map_zero comparison).symm),
    fun h => by rw [h,map_zero]⟩

/-- The final reference relation completeness follows from two explicit finite comparison inputs. -/
theorem orbit_kernel_eq_relations (hproper : ProperKernelFilling)
    (hrelative : LinearMap.ker GoodRelativeChains.orbitMap = GoodOrbitRelations.relations) :
    LinearMap.ker GoodOrbitRelations.orbitMap = GoodOrbitRelations.relations :=
  (orbit_kernels_eq hproper).trans hrelative

end TernaryPoly.SpanComparisonExactness
