module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Injective
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.RealizationOfLike

@[expose] public section


/-!
# The realization of the holomorphic model

For a finite-adelic model `M` of weight `k ≥ 6`, the realization of the smooth vectors of the
holomorphic model `bergmanRep M` is a linear map (`realize`) which is injective
(`realize_injective`), right equivariant, has the four scalar cuspidal properties for the central
character `M.χ` and is real analytic along `GL₂(ℝ)`. Together these are a
`SubRepresentation.Realization` of `bergmanRep M` (`realization`), which `Realization.cuspidalOfInvariant` / `CyclicRepresentation.cyclicCuspidal` turn into
`CuspidalRepresentation`s on irreducible closed invariant subspaces. The lower lowest weight
vector of `e` realizes to `reproConst k • ε e` (`realizeU_lowestMinus`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
open TernaryPeriodPolynomials.Automorphic.SubRepresentation
open TernaryPeriodPolynomials.Automorphic.RealizationOfLike

namespace TernaryPeriodPolynomials.Regularity

variable {k : ℕ} (M : FiniteModel k) (hk : 6 ≤ k)

/-- The realization of the smooth vectors of the holomorphic model, as a linear map. -/
def realize : smoothSubmodule (bergmanRep M) →ₗ[ℂ] (BinaryAdelicGL → ℂ) where
  toFun := realizeFun
  map_add' F G := by
    have hU := (level_isOpenCompact F).inf (level_isOpenCompact G)
    have hF : ∀ w, (F.val : BergmanSpace k M.E) w ∈
        fixedSubmodule M.σ (level F ⊓ level G) := fun w =>
      fixedSubmodule_anti M.σ inf_le_left (apply_mem_fixed (level_fixed F) w)
    have hG : ∀ w, (G.val : BergmanSpace k M.E) w ∈
        fixedSubmodule M.σ (level F ⊓ level G) := fun w =>
      fixedSubmodule_anti M.σ inf_le_right (apply_mem_fixed (level_fixed G) w)
    have hFG : ∀ w, ((F + G).val : BergmanSpace k M.E) w ∈
        fixedSubmodule M.σ (level F ⊓ level G) := fun w => Submodule.add_mem _ (hF w) (hG w)
    rw [realizeFun_eq (F + G) hU hFG, realizeFun_eq F hU hF, realizeFun_eq G hU hG]
    exact realizeU_add M hU (l1Finite_of_smooth hk F) (l1Finite_of_smooth hk G)
  map_smul' c F := by
    have hU := level_isOpenCompact F
    have hF : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ (level F) :=
      apply_mem_fixed (level_fixed F)
    have hcF : ∀ w, ((c • F).val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ (level F) :=
      fun w => Submodule.smul_mem _ c (hF w)
    rw [realizeFun_eq (c • F) hU hcF, realizeFun_eq F hU hF]
    exact realizeU_smul M hU c F.val

theorem realize_apply (F : smoothSubmodule (bergmanRep M)) : realize M hk F = realizeFun F :=
  rfl

/-- The realization is injective. -/
theorem realize_injective : Function.Injective (realize M hk) := by
  intro F G h
  have h0 : realizeFun (F - G) = 0 := by
    change realize M hk (F - G) = 0
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_realizeFun_eq_zero M hk _ h0)

/-- **The realization of the holomorphic model** (`k ≥ 6`). -/
def realization : Realization (bergmanRep M) (bergmanRep_unitary M) :=
  ofLike M.χ M.χ_unitary (realize M hk) (realize_injective M hk)
    (fun g F x => realizeFun_equivariant M g F x)
    (fun F => realizeU_isCuspidalLike M (level_isOpenCompact F)
      (apply_mem_fixed (level_fixed F)) (l1Finite_of_smooth hk F))
    (fun F g => realizeFun_scalarSmooth M hk F g)

/-- The realization, for the unitarity proof coming from the `IsUnitary` instance (the form used
by `Automorphic.ModelFamily`). -/
def realizationUnitary : Realization (bergmanRep M)
    TernaryPeriodPolynomials.Automorphic.AbstractIrreducibility.IsUnitary.norm_map :=
  realization M hk

theorem realization_realize (F : smoothSubmodule (bergmanRep M)) :
    (realization M hk).realize F = realizeFun F :=
  rfl

/-- The realization of a smooth vector at any level fixing its values. -/
theorem realization_realize_eq (F : smoothSubmodule (bergmanRep M))
    {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    (hF : ∀ w, (F.val : BergmanSpace k M.E) w ∈ fixedSubmodule M.σ U) :
    (realization M hk).realize F = realizeU M hU F.val :=
  realizeFun_eq F hU hF

/-- A smooth lower lowest weight vector realizes to the model function, up to the nonzero
constant `reproConst k`. -/
theorem realization_lowestMinus {U : Subgroup BinaryFiniteGL} (hU : IsOpenCompact U)
    {e : M.E} (he : e ∈ fixedSubmodule M.σ U)
    (hs : lowestMinus (by omega) e ∈ smoothSubmodule (bergmanRep M)) :
    (realization M hk).realize ⟨lowestMinus (by omega) e, hs⟩ =
      reproConst k • M.ε ⟨e, fixed_le_finiteSmooth M hU he⟩ := by
  rw [realization_realize_eq M hk _ hU (lowestMinus_mem_fixed M (by omega) he)]
  funext x
  exact realizeU_lowestMinus M (by omega) hU he x

end TernaryPeriodPolynomials.Regularity

end
