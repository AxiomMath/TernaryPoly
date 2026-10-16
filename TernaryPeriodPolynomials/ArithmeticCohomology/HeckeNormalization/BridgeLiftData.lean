module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLift

@[expose] public section


/-!
# L2b: a `LiftData` over the identity is a lift `Res_S P• → Res_f P•` of the dual Farey resolution

Formalized by Claude Sonnet 5.5.

`liftOfData p l`: the chain map `Res_S P• → Res_f P•` (`LiftRes (binDatum p) farResolution`) with components `l.lam0`, `l.lam1` (and zero in
degrees `≥ 2`), `liftOfData_overId` (`LiftOverId` from `l.OverId`) and `L2b_holds : BridgeInterface.L2b p`.
-/

open CategoryTheory Representation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

section L2b

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol

variable (p : ℕ) [Fact p.Prime]

/-- The Rep-level morphism on `P0` attached to `LiftData`. -/
def liftRep0 (l : LiftData p) : Rep.res (binDatum p).S.subtype P0 ⟶ Rep.res (binDatum p).f P0 :=
  Rep.ofHom ⟨l.lam0, fun σ => LinearMap.ext fun x => l.eq0 σ x⟩

def liftRep1 (l : LiftData p) : Rep.res (binDatum p).S.subtype P1 ⟶ Rep.res (binDatum p).f P1 :=
  Rep.ofHom ⟨l.lam1, fun σ => LinearMap.ext fun x => l.eq1 σ x⟩

/-- The chain map `Res_S P• → Res_f P•` attached to `LiftData`. -/
def liftOfData (l : LiftData p) : LiftRes (binDatum p) farResolution where
  f n := match n with
    | 0 => liftRep0 p l
    | 1 => liftRep1 p l
    | _ + 2 => 0
  comm' i j hij := by
    have hij' : j + 1 = i := by simpa using hij
    subst hij'
    match j with
    | 0 =>
      change liftRep1 p l ≫ (Rep.resFunctor (binDatum p).f).map (farComplex.d 1 0) =
        (Rep.resFunctor (binDatum p).S.subtype).map (farComplex.d 1 0) ≫ liftRep0 p l
      rw [show farComplex.d 1 0 = d1 from ChainComplex.of_d farX farD 0]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact l.chain x
    | j + 1 =>
      have h0 : farComplex.d (j + 1 + 1) (j + 1) = 0 := ChainComplex.of_d farX farD (j + 1)
      have e1 : (Rep.resFunctor (binDatum p).f).map (farComplex.d (j + 1 + 1) (j + 1)) = 0 := by
        rw [h0]; exact Functor.map_zero _ _ _
      have e2 : (Rep.resFunctor (binDatum p).S.subtype).map (farComplex.d (j + 1 + 1) (j + 1)) = 0 := by
        rw [h0]; exact Functor.map_zero _ _ _
      change _ ≫ (Rep.resFunctor (binDatum p).f).map (farComplex.d (j + 1 + 1) (j + 1)) =
        (Rep.resFunctor (binDatum p).S.subtype).map (farComplex.d (j + 1 + 1) (j + 1)) ≫ _
      rw [e1, e2]
      exact Limits.comp_zero.trans Limits.zero_comp.symm

theorem liftOfData_f0 (l : LiftData p) (x : P0) : ((liftOfData p l).f 0).hom x = l.lam0 x := rfl

theorem liftOfData_f1 (l : LiftData p) (x : P1) : ((liftOfData p l).f 1).hom x = l.lam1 x := rfl

theorem liftOfData_overId (l : LiftData p) (hl : l.OverId) :
    LiftOverId (binDatum p) farResolution (liftOfData p l) := by
  unfold LiftOverId
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact hl x

/-- **L2b** (`BridgeInterface.L2b`): `LiftData` over the identity is a `LiftRes` over the identity. -/
theorem L2b_holds : L2b p := fun l hl =>
  ⟨liftOfData p l, liftOfData_overId p l hl, fun _ => rfl, fun _ => rfl⟩

end L2b

end TernaryPeriodPolynomials.Argument.HeckeNormalization
