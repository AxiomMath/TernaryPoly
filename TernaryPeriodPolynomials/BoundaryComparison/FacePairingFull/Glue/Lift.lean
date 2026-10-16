module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.LineEvalBasic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TwistRepP
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FacePairingComparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing

@[expose] public section


/-!
# Rep-level lifts of the function-level data of the face pairings

For a line cocycle `z` of the arithmetic level with an edge primitive `w` and a plane cocycle `y` with an edge primitive
`s`, the cone cochains of the paper's proof of Lemma C.2 (`(z, 0, w)` and its `φ`-twist `(y^φ, 0, s^φ)`) are
the morphisms `coneR.X 2 ⟶ V` and `coneR.X 2 ⟶ V^*` below, `V = coeffRep ρ`, `ρ = rationalCoefficientComponent n χ`:

* `lineLiftB z w = innerLineCochain ρ z|_{Γ(6)} w|_{Γ(6)}`, with coordinates `(w, z, 0)`;
* `lineLiftA T r y s = innerLineCochain (twistRep T) (y^φ) (s^φ) ≫ pairHom T r`, `r : ℂ →ₗ[ℚ] ℚ`;
* the plane analogues `planeLiftB`, `planeLiftA` (coordinates `(-w, 0, z)`).

Each is a cocycle (`lineLiftB_cocycle`, …).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPoly.SingularLocalDuality (dualRepresentation)
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

variable {n : ℕ} {χ : RankOneCharacter}

/-- The cone cochain `(w, z, 0)` of a line cocycle with an edge primitive. -/
def lineLiftB (z : MaximalCycles n χ .line) (w : EdgeCochains n χ 1) :
    coneR.X 2 ⟶ coeffRep (rationalCoefficientComponent n χ) :=
  innerLineCochain (rationalCoefficientComponent n χ)
    (restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .line) z.val)
    (restrictN6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) w)

/-- The cone cochain `(-w, 0, z)` of a plane cocycle with an edge primitive. -/
def planeLiftB (z : MaximalCycles n χ .plane) (w : EdgeCochains n χ 1) :
    coneR.X 2 ⟶ coeffRep (rationalCoefficientComponent n χ) :=
  innerPlaneCochain (rationalCoefficientComponent n χ)
    (restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .plane) z.val)
    (restrictN6 (functionRepresentation (rationalCoefficientComponent n χ) Edges) w)

/-- The `φ`-twist of a plane cocycle with an edge primitive, as a line-supported cone cochain with values in the
contragredient (through `r`). -/
def lineLiftA (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ) (y : MaximalCycles n χ .plane)
    (s : EdgeCochains n χ 1) :
    coneR.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n χ)) :=
  innerLineCochain (twistRep T) (twistCochain2 T y.val) (twistCochain1 T s) ≫ pairHom T r

/-- The `φ`-twist of a line cocycle with an edge primitive, as a plane-supported cone cochain with values in the
contragredient (through `r`). -/
def planeLiftA (T : DualityDataP n χ) (r : ℂ →ₗ[ℚ] ℚ) (y : MaximalCycles n χ .line)
    (s : EdgeCochains n χ 1) :
    coneR.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n χ)) :=
  innerPlaneCochain (twistRepP T) (twistCochain2P T y.val) (twistCochain1P T s) ≫ pairHomP T r

theorem lineLiftB_cocycle {z : MaximalCycles n χ .line} {w : EdgeCochains n χ 1} (hw : EdgePrimitive z w) :
    coneR.d 3 2 ≫ lineLiftB z w = 0 :=
  innerLineCochain_cocycle (rationalCoefficientComponent n χ)
    ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .line) z.val,
      restrictN6_cocycle _ z.val z.property⟩ _ (fun x e => hw x e)

theorem planeLiftB_cocycle {z : MaximalCycles n χ .plane} {w : EdgeCochains n χ 1} (hw : EdgePrimitiveP z w) :
    coneR.d 3 2 ≫ planeLiftB z w = 0 :=
  innerPlaneCochain_cocycle (rationalCoefficientComponent n χ)
    ⟨restrictN6 (flagRepresentation (rationalCoefficientComponent n χ) .plane) z.val,
      restrictN6_cocycle _ z.val z.property⟩ _ (fun x e => hw x e)

theorem lineLiftA_cocycle (T : DualityData n χ) (r : ℂ →ₗ[ℚ] ℚ) {y : MaximalCycles n χ .plane}
    {s : EdgeCochains n χ 1} (hs : ∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e) :
    coneR.d 3 2 ≫ lineLiftA T r y s = 0 := by
  unfold lineLiftA
  rw [← Category.assoc, innerLineCochain_cocycle (twistRep T)
    ⟨twistCochain2 T y.val, twistCochain2_cocycle T y.val y.property⟩ (twistCochain1 T s)
    (twist_edge_compat T y.val s hs), zero_comp]

theorem planeLiftA_cocycle (T : DualityDataP n χ) (r : ℂ →ₗ[ℚ] ℚ) {y : MaximalCycles n χ .line}
    {s : EdgeCochains n χ 1} (hs : ∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) :
    coneR.d 3 2 ≫ planeLiftA T r y s = 0 := by
  unfold planeLiftA
  rw [← Category.assoc, innerPlaneCochain_cocycle (twistRepP T)
    ⟨twistCochain2P T y.val, twistCochain2P_cocycle T y.val y.property⟩ (twistCochain1P T s)
    (twistP_edge_compat T y.val s hs), zero_comp]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
