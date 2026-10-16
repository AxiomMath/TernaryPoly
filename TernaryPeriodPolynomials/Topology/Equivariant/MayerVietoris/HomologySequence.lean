module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantMayerVietorisHomology
open CategoryTheory Limits HomologicalComplex

variable {G : Type} [Group G]

instance homologyPreservesBiproducts (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor (Rep ℚ G) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- Actual homology of the biproduct of two chain complexes is their homology biproduct. -/
def homologyBiprodIso (K L : ChainComplex (Rep ℚ G) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n :=
  (homologyFunctor (Rep ℚ G) (ComplexShape.down ℕ) n).mapBiprod K L

theorem homologyBiprod_isZero {K L : ChainComplex (Rep ℚ G) ℕ} (n : ℕ)
    (hK : IsZero (K.homology n)) (hL : IsZero (L.homology n)) : IsZero ((K ⊞ L).homology n) :=
  ((biprod_isZero_iff _ _).mpr ⟨hK,hL⟩).of_iso (homologyBiprodIso K L n)

variable (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (hS : S.ShortExact)

/-- The actual connecting map realizes H1 as the kernel of the induced H0 map when H1(X₂)=0. -/
def homologyOneKernelIso (hB : IsZero (S.X₂.homology 1)) :
    S.X₃.homology 1 ≅ kernel (homologyMap S.f 0) := by
  have : Mono (hS.δ 1 0 rfl) := hS.mono_δ 1 0 rfl hB
  exact (hS.homology_exact₁ 1 0 rfl).fIsKernel.conePointUniqueUpToIso
    (limit.isLimit (parallelPair (homologyMap S.f 0) 0))

/-- The kernel comparison retains exactly the genuine connecting morphism. -/
theorem homologyOneKernelIso_hom_ι (hB : IsZero (S.X₂.homology 1)) :
    (homologyOneKernelIso S hS hB).hom ≫ kernel.ι (homologyMap S.f 0)=hS.δ 1 0 rfl := by
  have : Mono (hS.δ 1 0 rfl) := hS.mono_δ 1 0 rfl hB
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (hS.homology_exact₁ 1 0 rfl).fIsKernel (limit.isLimit (parallelPair (homologyMap S.f 0) 0))
      WalkingParallelPair.zero

include hS in
/-- Exactness detects all higher-degree vanishing, with no dimension argument. -/
theorem homology_succ_succ_isZero (n : ℕ)
    (hA : IsZero (S.X₁.homology (n+1))) (hB : IsZero (S.X₂.homology (n+2))) :
    IsZero (S.X₃.homology (n+2)) := by
  have : Mono (hS.δ (n+2) (n+1) rfl) := hS.mono_δ (n+2) (n+1) rfl hB
  exact IsZero.of_mono (hS.δ (n+2) (n+1) rfl) hA

include hS in
/-- The degree-zero map in any short exact sequence of nonnegative chain complexes is epic. -/
theorem homologyZero_epi : Epi (homologyMap S.g 0) := by
  have := hS.epi_g
  exact epi_homologyMap_of_epi_of_not_rel S.g 0 (fun j => by
    change ¬ j+1=0
    exact Nat.succ_ne_zero j)

/-- H0 of the third complex is the actual cokernel of the induced H0 map. -/
def homologyZeroCokernelIso : S.X₃.homology 0 ≅ cokernel (homologyMap S.f 0) := by
  have := homologyZero_epi S hS
  exact (hS.homology_exact₂ 0).gIsCokernel.coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (homologyMap S.f 0) 0))

/-- The cokernel comparison retains the genuine homology map of the right chain arrow. -/
theorem homologyMap_homologyZeroCokernelIso :
    homologyMap S.g 0 ≫ (homologyZeroCokernelIso S hS).hom=cokernel.π (homologyMap S.f 0) := by
  have := homologyZero_epi S hS
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (hS.homology_exact₂ 0).gIsCokernel (colimit.isColimit (parallelPair (homologyMap S.f 0) 0))
      WalkingParallelPair.one

end TernaryPoly.EquivariantMayerVietorisHomology
