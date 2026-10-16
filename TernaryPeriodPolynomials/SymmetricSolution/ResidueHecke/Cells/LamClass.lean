module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LamChain
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Push
public import TernaryPeriodPolynomials.GroupCohomology.Homology.ResolutionConj

@[expose] public section


/-!
# The top cycle attached to a class of the kernel `K_M`

Formalized by Claude Sonnet 5.5.

`lamChain x` is the chain of `(A ⊗ R₃)_P` corresponding under `ZIsoR` to the cycle `Λ x` of `(Z ⊗ 1)_{P/U}`; it is a cycle
(`lamChain_cycle`) and represents the image of `Λ x` in `H₃(P, A)` through the resolution `R` (`eKR_inv_LamH`).
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.GroupHomology

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (A : Rep.{0} ℚ P)
  [Representation.IsTrivial (A.ρ.comp U.subtype)] (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0')
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)

/-- The chain of `(CxK (A ⊗ R))₃` attached to a class of the kernel `K_M`. -/
def lamChain (x : KM P1' P0' d' (Abar U A ⊗ L)) : (CxK (YAR R A)).X 3 :=
  ((ZIsoR U R A).hom.f 3).hom ((Lam (Abar U A ⊗ L) (ZR U R A) P1' (ThetaIn U A R t3)).hom x.1)

include t2 hi in
theorem lamChain_cycle (x : KM P1' P0' d' (Abar U A ⊗ L)) :
    ((CxK (YAR R A)).d 3 2).hom (lamChain U A R d' t3 x) = 0 := by
  have h1 := Lam_cycle (ZR U R A) P1' P0' d' (Abar U A ⊗ L) (ThetaIn U A R t3)
    (ThetaIn U A R t2) (ThetaIn_comm U A R d' t3 t2 hi) x
  have h2 := congrArg (fun t => t.hom ((Lam (Abar U A ⊗ L) (ZR U R A) P1' (ThetaIn U A R t3)).hom x.1))
    ((ZIsoR U R A).hom.comm 3 2)
  refine h2.trans ?_
  have h3 : ((ZIsoR U R A).hom.f 2).hom (0 : (CxF (ZR U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))).X 2) = 0 := map_zero _
  refine Eq.trans (congrArg ((ZIsoR U R A).hom.f 2).hom h1) h3

include t2 hi in
/-- **The class of the chain `lamChain x` is the image of `Λ x` in `H₃(P, A)`.** -/
theorem eKR_inv_LamH (x : KM P1' P0' d' (Abar U A ⊗ L)) :
    (eKR R A 3).hom.hom ((groupHomologyZIsoR U R A 3).inv.hom
      (LamH (ZR U R A) P1' P0' d' (Abar U A ⊗ L) (ThetaIn U A R t3) (ThetaIn U A R t2)
        (ThetaIn_comm U A R d' t3 t2 hi) x)) =
      cycleClass (CxK (YAR R A)) (lamChain U A R d' t3 x) (lamChain_cycle U A R d' t3 t2 hi x) := by
  have h1 : ∀ y, (eKR R A 3).hom.hom ((groupHomologyZIsoR U R A 3).inv.hom y) =
      (HomologicalComplex.homologyMap (ZIsoR U R A).hom 3).hom y := by
    intro y
    have e : (groupHomologyZIsoR U R A 3).inv =
        HomologicalComplex.homologyMap (ZIsoR U R A).hom 3 ≫ (groupHomologyIso A 3 R).inv := rfl
    rw [e]
    have := congrArg (fun t => t.hom ((HomologicalComplex.homologyMap (ZIsoR U R A).hom 3).hom y))
      (groupHomologyIso A 3 R).inv_hom_id
    exact this
  rw [h1, LamH_apply]
  have h2 := homologyMap_cycleClass (ZIsoR U R A).hom ((Lam (Abar U A ⊗ L) (ZR U R A) P1' (ThetaIn U A R t3)).hom x.1)
    (Lam_cycle (ZR U R A) P1' P0' d' (Abar U A ⊗ L) (ThetaIn U A R t3) (ThetaIn U A R t2)
      (ThetaIn_comm U A R d' t3 t2 hi) x) (lamChain_cycle U A R d' t3 t2 hi x)
  exact h2

end TernaryPeriodPolynomials.Argument.AppendixBResidue
