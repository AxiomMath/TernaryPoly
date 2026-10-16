module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.ReynoldsAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic

@[expose] public section


/-!
# Sphericity of the Reynolds average of a level-three vector (Step (iii))

Step (iii) of `CuspidalSupply.lean`'s hypothesis `h`: the
pieces `p : levelThreeClassicalVectorsWt D.cusp wt` produced by
`TernaryPeriodPolynomials.Argument.Automorphic.Constituent.Covers.modelCoversForms` are, by the very definition of
`levelThreeClassicalVectorsWt`/`levelThreeValues` (`Proofs/AxiomCodeMultiplicityOne/Basic.lean`'s
`mem_levelThreeValues`), already fixed by every `PlaneLeviLevel` element — exactly the `leviFixed`
hypothesis `ReynoldsAverage.lean`'s `reynoldsAverage_fixed` needs.

The only ingredient missing from `ReynoldsCosets.lean` is that `PlaneLeviLevel` is closed under
inverse (it is the stabilizer of the row vector `(0,1)` under `GL₂(ZMod 3)`'s right action, hence a
subgroup); `planeLeviLevel_inv_iff` supplies this.

**What this does not address**: nonvanishing of `reynoldsAverage cusp p` (needed to package the
result as the bundled `∃ v ≠ 0, ...` Prop `SphericalCusp`). Averaging a nonzero Levi-fixed vector
can in principle collapse it; ruling that out for the specific pieces coming out of
`modelCoversForms` is tied up with Step (ii)'s global sum identity (`f ≠ 0` forcing some piece's
*average* nonzero), not a fact about one piece in isolation.
-/

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues mem_levelThreeValues)

/-- The bottom row of the `GL₂(ZMod 3)` identity is `(0,1)`. -/
theorem bottomRow3_one : bottomRow3 (1 : GeneralLinearGroup (Fin 2) (ZMod 3)) = ((0 : ZMod 3), 1) := by
  simp only [bottomRow3, Units.val_one, Prod.mk.injEq]
  exact ⟨Matrix.one_apply_ne (by decide), Matrix.one_apply_eq 1⟩

/-- **`PlaneLeviLevel` is closed under inverse** (it is the stabilizer of a vector under a group
action, hence a subgroup). -/
theorem planeLeviLevel_inv_iff (κ : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    PlaneLeviLevel κ⁻¹ ↔ PlaneLeviLevel κ := by
  rw [planeLeviLevel_iff, planeLeviLevel_iff, red_inv]
  constructor
  · intro hinv
    have h1 := (bottomRow3_eq_iff (1 : GeneralLinearGroup (Fin 2) (ZMod 3)) (red κ)).mp
      (by rwa [one_mul])
    rw [bottomRow3_one] at h1
    exact h1.symm
  · intro hκ
    have h1 : bottomRow3 ((1 : GeneralLinearGroup (Fin 2) (ZMod 3)) * (red κ)⁻¹) =
        ((0 : ZMod 3), 1) :=
      (bottomRow3_eq_iff (1 : GeneralLinearGroup (Fin 2) (ZMod 3)) (red κ)).mpr
        (by rw [bottomRow3_one]; exact hκ.symm)
    rwa [one_mul] at h1

/-- A `levelThreeValues`-member is `leviFixed` in the sense `reynoldsAverage_fixed` needs. -/
theorem leviFixed_of_mem_levelThreeValues (cusp : CuspidalRepresentation) (v : cusp.smooth)
    (hv : v.val ∈ levelThreeValues cusp) (κ : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (hκ : PlaneLeviLevel κ) : cuspAt cusp κ v = v := by
  apply Subtype.ext
  show cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding κ⁻¹)) v.val = v.val
  exact mem_levelThreeValues.mp hv κ⁻¹ ((planeLeviLevel_inv_iff κ).mpr hκ)

/-- **Step (iii).** The Reynolds average of a `levelThreeValues`-member is fixed by *all* of
`GL₂(ℤ̂)`. -/
theorem reynoldsAverage_mem_levelThreeValues_fixed (cusp : CuspidalRepresentation) (v : cusp.smooth)
    (hv : v.val ∈ levelThreeValues cusp) (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    cuspAt cusp k (reynoldsAverage cusp v) = reynoldsAverage cusp v :=
  reynoldsAverage_fixed cusp v (leviFixed_of_mem_levelThreeValues cusp v hv) k

/-- The same fact in `SphericalCusp`'s own native shape (no inverse on `k`). -/
theorem forall_cuspAt_eq_of_mem_levelThreeValues (cusp : CuspidalRepresentation) (v : cusp.smooth)
    (hv : v.val ∈ levelThreeValues cusp) (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding k))
      (reynoldsAverage cusp v).val = (reynoldsAverage cusp v).val := by
  have h : cuspAt cusp k⁻¹ (reynoldsAverage cusp v) = reynoldsAverage cusp v :=
    reynoldsAverage_mem_levelThreeValues_fixed cusp v hv k⁻¹
  have h2 : cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding (k⁻¹)⁻¹))
      (reynoldsAverage cusp v).val = (reynoldsAverage cusp v).val :=
    congrArg Subtype.val h
  rwa [inv_inv] at h2

end TernaryPeriodPolynomials.Argument.CuspidalSpan
