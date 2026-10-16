module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.EdgeChainInjective

@[expose] public section


/-!
# The dual boundary `ℚ[Tri] → ℚ[OTE]`

Formalized by Claude Sonnet 5.5.

`bdryV t = ∑_{q leaves t} ([q.swap] - [q])` (the transpose of the boundary `dTilde` of the dual Farey tree, up to
sign), `bdryMap : P0 ⟶ PE` the induced `Γ`-map (`bdryV_smul`), with values in the antisymmetric chains
(`bdryMap_mem_antiSub`) and killed by the symbol map (`piT_bdryV`).  Its image is the kernel of the symbol map on
antisymmetric chains (`FareyKernel`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

/-- The dual boundary of a triangle: `∑_{q leaves t} ([q.swap] - [q])`. -/
def bdryV (t : Tri) : PE :=
  ∑ q ∈ nbF t, (MonoidAlgebra.single q.swap (1 : ℚ) - MonoidAlgebra.single q (1 : ℚ))

theorem bdryV_smul (g : IntegralGL) (t : Tri) : bdryV (g • t) = PE.ρ g (bdryV t) := by
  unfold bdryV
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sub]
  have h1 : PE.ρ g (MonoidAlgebra.single q.swap (1 : ℚ)) = MonoidAlgebra.single (g • q.swap) (1 : ℚ) :=
    Representation.ofMulAction_single g q.swap 1
  have h2 : PE.ρ g (MonoidAlgebra.single q (1 : ℚ)) = MonoidAlgebra.single (g • q) (1 : ℚ) :=
    Representation.ofMulAction_single g q 1
  rw [h1, h2, ← OTE.swap_smul]

/-- The dual boundary as a map of representations. -/
def bdryMap : P0 ⟶ PE := permLift PE bdryV (fun g t => bdryV_smul g t)

theorem bdryMap_single (t : Tri) (r : ℚ) :
    bdryMap.hom (MonoidAlgebra.single t r) = r • bdryV t := permLift_single _ _ _ _ _

theorem bdryV_mem_antiSub (t : Tri) : bdryV t ∈ antiSub := by
  rw [mem_antiSub]
  unfold bdryV
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  rw [map_sub, swapMap_single, swapMap_single, OTE.swap_swap]
  abel

theorem bdryMap_mem_antiSub (w : P0) : bdryMap.hom w ∈ antiSub := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact antiSub.add_mem ha hb
  | single t r => rw [bdryMap_single]; exact antiSub.smul_mem r (bdryV_mem_antiSub t)

theorem ref_sum : reference + stD rho reference + stD rho2 reference = 0 := by
  rw [reference_eq, stD_symbol, stD_symbol, rho_c1, rho_c2, rho2_c1, rho2_c2, detQ_rho, detQ_rho2,
    one_smul, one_smul, symbol_triangle cusp1 cusp2 cusp3, symbol_triangle cusp1 cusp3 cusp1, symbol_self]

theorem edgeSym_sum_nbF (g : IntegralGL) : ∑ q ∈ nbF (g • triPlus), edgeSym q = 0 := by
  rw [sum_nbF, edgeSym_apply, edgeSym_apply, edgeSym_apply, map_mul, map_mul]
  change stD g reference + stD g (stD rho reference) + stD g (stD rho2 reference) = 0
  rw [← map_add, ← map_add, ref_sum, map_zero]

theorem piT_bdryV (t : Tri) : piT.hom (bdryV t) = 0 := by
  obtain ⟨g, rfl⟩ := exists_smul_triPlus t
  unfold bdryV
  rw [map_sum]
  have : ∀ q ∈ nbF (g • triPlus), piT.hom (MonoidAlgebra.single q.swap (1 : ℚ) - MonoidAlgebra.single q 1)
      = (-2 : ℚ) • edgeSym q := by
    intro q _
    rw [map_sub, piT_single, piT_single, edgeSym_swap, one_smul, one_smul]
    module
  rw [Finset.sum_congr rfl this, ← Finset.smul_sum, edgeSym_sum_nbF, smul_zero]

end TernaryPeriodPolynomials.Argument.HeckeDuality
