module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.CupInd

@[expose] public section


/-!
# The induced module of `Γ(N)` along `Γ(M) ≤ Γ(N)` and the Shapiro map on `H¹`

Formalized by Claude Sonnet 5.5.

For `V : Rep ℂ Γ(N)`, `indRep M V = Fun(Γ(N)/Γ(M), V)` with `(s F)(x) = ρ(s) F(s⁻¹ x)`, `evHom` the evaluation at the base coset (a morphism of `Γ(M)`-modules from `indRep` to `V`)
and `shapiro` the induced map `H¹(Γ(N), Ind V) → H¹(Γ(M), V)` (restriction followed by evaluation).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section SL

variable {N : ℕ} (M : ℕ)

/-- The subgroup `Γ(M) ∩ Γ(N)` of `Γ(N)`. -/
abbrev subM (N M : ℕ) : Subgroup (Gamma N) := (Gamma M).subgroupOf (Gamma N)

/-- `Fun(Γ(N)/Γ(M), V)`. -/
def indRep (V : Rep ℂ (Gamma N)) : Rep ℂ (Gamma N) :=
  Rep.of (indRepQ (Q := Gamma N ⧸ subM N M) V.ρ)

theorem indRep_apply (V : Rep ℂ (Gamma N)) (s : Gamma N) (F : Gamma N ⧸ subM N M → V) (x : Gamma N ⧸ subM N M) :
    (indRep M V).ρ s F x = V.ρ s (F (s⁻¹ • x)) := rfl

variable {M} (hle : Gamma M ≤ Gamma N)

theorem inv_smul_base (δ : Gamma M) :
    ((Subgroup.inclusion hle δ)⁻¹ : Gamma N) • ((1 : Gamma N) : Gamma N ⧸ subM N M) = ((1 : Gamma N) : Gamma N ⧸ subM N M) := by
  change (QuotientGroup.mk (((Subgroup.inclusion hle δ)⁻¹ : Gamma N) * 1) : Gamma N ⧸ subM N M) = QuotientGroup.mk 1
  rw [mul_one]
  exact QuotientGroup.eq.mpr (by rw [inv_inv, mul_one]; exact δ.2)

/-- Evaluation at the base coset: a morphism of `Γ(M)`-modules `Ind V → V`. -/
def evHom (V : Rep ℂ (Gamma N)) :
    Rep.res (Subgroup.inclusion hle) (indRep M V) ⟶ Rep.res (Subgroup.inclusion hle) V :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.proj ((1 : Gamma N) : Gamma N ⧸ subM N M) : (Gamma N ⧸ subM N M → V) →ₗ[ℂ] V) (fun g v => by
      show (indRep M V).ρ (Subgroup.inclusion hle g) v ((1 : Gamma N) : Gamma N ⧸ subM N M) =
        V.ρ (Subgroup.inclusion hle g) (v ((1 : Gamma N) : Gamma N ⧸ subM N M))
      exact (indRep_apply M V _ v _).trans (congrArg _ (congrArg v (inv_smul_base hle g)))))

/-- **The Shapiro map** `H¹(Γ(N), Ind V) → H¹(Γ(M), V)`: restriction to `Γ(M)` followed by evaluation at the base coset. -/
def shapiro (V : Rep ℂ (Gamma N)) :
    groupCohomology.H1 (indRep M V) →ₗ[ℂ] groupCohomology.H1 (Rep.res (Subgroup.inclusion hle) V) :=
  (groupCohomology.map (Subgroup.inclusion hle) (evHom hle V) 1).hom

theorem shapiro_π (V : Rep ℂ (Gamma N)) (c : groupCohomology.cocycles₁ (indRep M V)) :
    shapiro hle V (groupCohomology.H1π (indRep M V) c) =
      groupCohomology.H1π (Rep.res (Subgroup.inclusion hle) V)
        (groupCohomology.mapCocycles₁ (Subgroup.inclusion hle) (evHom hle V) c) :=
  groupCohomology.H1π_comp_map_apply (Subgroup.inclusion hle) (evHom hle V) c

theorem shapiro_cocycle (V : Rep ℂ (Gamma N)) (c : groupCohomology.cocycles₁ (indRep M V)) (g : Gamma M) :
    (groupCohomology.mapCocycles₁ (Subgroup.inclusion hle) (evHom hle V) c).1 g =
      c.1 (Subgroup.inclusion hle g) ((1 : Gamma N) : Gamma N ⧸ subM N M) := rfl

end SL

end TernaryPeriodPolynomials.Argument.CuspidalInduction
