module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.ShapiroCochain

@[expose] public section


/-!
# Shapiro realization ("Step C" of `face_pairing_perfect`, part 2)

Lifts the Shapiro cochain construction of `ShapiroCochain.lean` from cochains to cocycles:
given a local 2-*cocycle* for `fixedPointLevel level q`, the Shapiro cochain built from it is
itself a cocycle (`shapiroCycle`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

/-- The Shapiro cochain is a cocycle whenever the local cochain is. -/
def shapiroCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cocycles (fixedPointLevel level q) representation) :
    cocycles level (functionRepresentation representation X) :=
  ⟨shapiroCochain level representation q local_.val, by
    apply LinearMap.mem_ker.mpr
    funext vertices
    funext point
    show shapiroCochainFun level representation q local_.val ![vertices 1, vertices 2, vertices 3]
        point -
      shapiroCochainFun level representation q local_.val ![vertices 0, vertices 2, vertices 3]
        point +
      shapiroCochainFun level representation q local_.val ![vertices 0, vertices 1, vertices 3]
        point -
      shapiroCochainFun level representation q local_.val ![vertices 0, vertices 1, vertices 2]
        point
      = 0
    by_cases h : ∃ g : level, g.val • q = point
    · rw [shapiroCochainFun_apply_pos _ _ _ _ _ _ h, shapiroCochainFun_apply_pos _ _ _ _ _ _ h,
        shapiroCochainFun_apply_pos _ _ _ _ _ _ h, shapiroCochainFun_apply_pos _ _ _ _ _ _ h]
      set T := shapiroTransport level q point h with hT_def
      have e1 : (fun i => T.val⁻¹ * ![vertices 1, vertices 2, vertices 3] i)
          = ![T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 2, T.val⁻¹ * vertices 3] := by
        funext i; fin_cases i <;> rfl
      have e2 : (fun i => T.val⁻¹ * ![vertices 0, vertices 2, vertices 3] i)
          = ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 2, T.val⁻¹ * vertices 3] := by
        funext i; fin_cases i <;> rfl
      have e3 : (fun i => T.val⁻¹ * ![vertices 0, vertices 1, vertices 3] i)
          = ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 3] := by
        funext i; fin_cases i <;> rfl
      have e4 : (fun i => T.val⁻¹ * ![vertices 0, vertices 1, vertices 2] i)
          = ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 2] := by
        funext i; fin_cases i <;> rfl
      rw [e1, e2, e3, e4, ← map_sub, ← map_add, ← map_sub]
      have key : local_.val.val ![T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 2, T.val⁻¹ * vertices 3] -
          local_.val.val ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 2, T.val⁻¹ * vertices 3] +
          local_.val.val ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 3] -
          local_.val.val ![T.val⁻¹ * vertices 0, T.val⁻¹ * vertices 1, T.val⁻¹ * vertices 2] = 0 :=
        congrFun (LinearMap.mem_ker.mp local_.property) (fun i => T.val⁻¹ * vertices i)
      rw [key, map_zero]
    · rw [shapiroCochainFun_apply_neg _ _ _ _ _ _ h, shapiroCochainFun_apply_neg _ _ _ _ _ _ h,
        shapiroCochainFun_apply_neg _ _ _ _ _ _ h, shapiroCochainFun_apply_neg _ _ _ _ _ _ h]
      abel⟩

theorem fixedPointCycle_shapiroCycle (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cocycles (fixedPointLevel level q) representation) :
    fixedPointCycle level representation q (shapiroCycle level representation q local_) =
      local_ := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  show shapiroCochainFun level representation q local_.val vertices q = local_.val.val vertices
  exact shapiroCochain_apply_self level representation q local_.val vertices

theorem fixedPointCycle_shapiroCycle_outside (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cocycles (fixedPointLevel level q) representation)
    (point : X) (h : ¬ ∃ g : level, g.val • q = point) :
    fixedPointCycle level representation point (shapiroCycle level representation q local_) =
      0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  show shapiroCochainFun level representation q local_.val vertices point = (0 : V)
  exact shapiroCochain_apply_outside level representation q local_.val vertices point h

/-- **Shapiro realization (Step C).** Every local cocycle at a point `q` is the local
restriction, at `q`, of a global cocycle class that moreover vanishes at every point of `X`
outside the `level`-orbit of `q`. This is the generic coinduction/Shapiro surjectivity
statement needed to realize cusp-local classes by global ones. -/
theorem shapiro_realization (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V) (q : X)
    (local_ : cocycles (fixedPointLevel level q) representation) :
    ∃ ξ : H2 level (functionRepresentation representation X),
      fixedPointH2 level representation q ξ =
        classOf (fixedPointLevel level q) representation local_ ∧
      ∀ point : X, ¬ (∃ g : level, g.val • q = point) →
        fixedPointH2 level representation point ξ = 0 := by
  refine ⟨classOf level (functionRepresentation representation X)
    (shapiroCycle level representation q local_), ?_, fun point hpoint => ?_⟩
  · rw [fixedPointH2_classOf, fixedPointCycle_shapiroCycle]
  · rw [fixedPointH2_classOf,
      fixedPointCycle_shapiroCycle_outside level representation q local_ point hpoint, map_zero]

end TernaryPeriodPolynomials.Argument.FacePairing
