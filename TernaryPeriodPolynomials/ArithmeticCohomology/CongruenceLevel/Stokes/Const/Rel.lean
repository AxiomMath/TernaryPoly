module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Phi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.CoordNat

@[expose] public section


/-!
# Transport of the Shapiro coordinates along incidence maps and conjugation

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.GammaNFaceFactor
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section Generic

variable {Γ : Type} [Group Γ] {V Z Z' : Type} [MulAction Γ V] [MulAction Γ Z] [MulAction Γ Z']

theorem stabCoord_congr_pt (S : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v₀ : V) {z z' : Z} (h : z = z')
    (hz : ∀ g : S, g • z = z) (hz' : ∀ g : S, g • z' = z') :
    stabCoord S W v₀ z hz = stabCoord S W v₀ z' hz' := by
  subst h
  rfl

/-- **Coordinates along an equivariant map of label sets, with conjugation**: if `α z = γ • R`, the Shapiro coordinate at `z` (for a subgroup `S` fixing `z`) of the pullback
along `α` is the transport along `s ↦ γ⁻¹ s γ` of the Shapiro coordinate at `R` (for its stabilizer). -/
theorem faceCoord_pullback_conj (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
    (S : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z)
    (γ : Γ) (R : Z') (hR : α z = γ • R)
    (f : S →* MulAction.stabilizer Γ R) (hf : ∀ s : S, (f s : Γ) = γ⁻¹ * s * γ) (n : ℕ) :
    HomologicalComplex.homologyMap (homPullback (prodMapHom Γ V Z α hα) W) n ≫
        faceCoord S W v₀ z hz n =
      faceCoord (MulAction.stabilizer Γ R) W v₀ R (fun g => g.2) n ≫
        groupCohomology.map f (conjComparison W γ (MulAction.stabilizer Γ R) S f hf) n := by
  have hS' : ∀ g : S, g • α z = α z := fun g => (hα g z).symm.trans (congrArg α (hz g))
  have hS2 : ∀ g : S, g • (γ • R) = γ • R := fun g => hR ▸ hS' g
  rw [faceCoord_eq_homologyMap_stabCoord S W v₀ z hz n,
    faceCoord_eq_homologyMap_stabCoord (MulAction.stabilizer Γ R) W v₀ R (fun g => g.2) n, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, stabCoord_pullback α hα S W v₀ z hz hS',
    stabCoord_congr_pt S W v₀ hR hS' hS2,
    homologyMap_stabCoord_conj W v₀ R γ (MulAction.stabilizer Γ R) S (fun g => g.2) hS2 f hf hfree n,
    Category.assoc, Category.assoc]
  congr 1
  exact barChainMap_homology f (conjComparison W γ (MulAction.stabilizer Γ R) S f hf) n

/-- The conjugation homomorphism `s ↦ γ⁻¹ s γ` from a subgroup fixing `γ • R` to the stabilizer of `R`. -/
def conjStabHom (γ : Γ) (R : Z) (S : Subgroup Γ) (h : ∀ s : S, s • (γ • R) = γ • R) :
    S →* MulAction.stabilizer Γ R where
  toFun s := ⟨γ⁻¹ * s * γ, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
    exact h s⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem conjStabHom_apply (γ : Γ) (R : Z) (S : Subgroup Γ) (h : ∀ s : S, s • (γ • R) = γ • R) (s : S) :
    ((conjStabHom γ R S h s : MulAction.stabilizer Γ R) : Γ) = γ⁻¹ * s * γ := rfl

end Generic

section Flags

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

/-- The `Γ(6)`-orbit of the line of (the representative of) a flag orbit. -/
def flagLineOrbit (o : labelOrbits Γ6 Flag) : labelOrbits Γ6 Line := Quotient.mk'' (flagLineOf o.out)

/-- The `Γ(6)`-orbit of the plane of (the representative of) a flag orbit. -/
def flagPlaneOrbit (o : labelOrbits Γ6 Flag) : labelOrbits Γ6 Plane := Quotient.mk'' (flagPlaneOf o.out)

theorem exists_conj_of_orbit {Z : Type} [MulAction Γ6 Z] (z : Z) (a : labelOrbits Γ6 Z) (h : (Quotient.mk'' z : labelOrbits Γ6 Z) = a) :
    ∃ γ : Γ6, γ • a.out = z := by
  have hz : z ∈ labelOrbit Γ6 Z a := (mem_labelOrbit_iff a z).2 h
  obtain ⟨γ, hγ⟩ := hz
  exact ⟨γ, hγ⟩

/-- The element of `Γ(6)` carrying the representative of the line orbit of a flag orbit to the line of the representative flag. -/
def lineConj (o : labelOrbits Γ6 Flag) : Γ6 :=
  Classical.choose (exists_conj_of_orbit (flagLineOf o.out) (flagLineOrbit o) rfl)

theorem lineConj_smul (o : labelOrbits Γ6 Flag) : lineConj o • (flagLineOrbit o).out = flagLineOf o.out :=
  Classical.choose_spec (exists_conj_of_orbit (flagLineOf o.out) (flagLineOrbit o) rfl)

def planeConj (o : labelOrbits Γ6 Flag) : Γ6 :=
  Classical.choose (exists_conj_of_orbit (flagPlaneOf o.out) (flagPlaneOrbit o) rfl)

theorem planeConj_smul (o : labelOrbits Γ6 Flag) : planeConj o • (flagPlaneOrbit o).out = flagPlaneOf o.out :=
  Classical.choose_spec (exists_conj_of_orbit (flagPlaneOf o.out) (flagPlaneOrbit o) rfl)

theorem stab_fixes_line_of (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out)
    (g : MulAction.stabilizer Γ6 o.out) : g • (γ • (flagLineOrbit o).out) = γ • (flagLineOrbit o).out := by
  rw [hγ]
  exact (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant g o.out).symm.trans
    (congrArg flagLineOf g.2)

theorem stab_fixes_plane_of (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out)
    (g : MulAction.stabilizer Γ6 o.out) : g • (γ • (flagPlaneOrbit o).out) = γ • (flagPlaneOrbit o).out := by
  rw [hγ]
  exact (TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant g o.out).symm.trans
    (congrArg flagPlaneOf g.2)

/-- The transport of the cohomology of the stabilizer of the representative of the line orbit to the flag group of the representative of the flag orbit
(conjugation by `γ`, where `γ` carries the representative of the line orbit to the line of the flag). -/
def lineTransportAt (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out) :
    groupCohomology (Rep.res (MulAction.stabilizer Γ6 (flagLineOrbit o).out).subtype Wq) 3 ⟶
      groupCohomology (Rep.res (MulAction.stabilizer Γ6 o.out).subtype Wq) 3 :=
  groupCohomology.map (conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ))
    (conjComparison Wq γ (MulAction.stabilizer Γ6 (flagLineOrbit o).out) (MulAction.stabilizer Γ6 o.out)
      (conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ))
      (conjStabHom_apply γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ))) 3

/-- … and the same for planes. -/
def planeTransportAt (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out) :
    groupCohomology (Rep.res (MulAction.stabilizer Γ6 (flagPlaneOrbit o).out).subtype Wq) 3 ⟶
      groupCohomology (Rep.res (MulAction.stabilizer Γ6 o.out).subtype Wq) 3 :=
  groupCohomology.map (conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ))
    (conjComparison Wq γ (MulAction.stabilizer Γ6 (flagPlaneOrbit o).out) (MulAction.stabilizer Γ6 o.out)
      (conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ))
      (conjStabHom_apply γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ))) 3

/-- The product of the Shapiro coordinates over the line orbits, in degree three. -/
def lineCoordPi : lineK.homology 3 →ₗ[ℚ]
    (∀ a : labelOrbits Γ6 Line, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3) :=
  LinearMap.pi fun a => (faceCoord (MulAction.stabilizer Γ6 a.out) Wq (1 : RationalGL3) a.out (fun g => g.2) 3).hom

theorem lineCoordPi_bijective : Function.Bijective lineCoordPi :=
  faceCoord_product_bijective_succ 2 (1 : RationalGL3) vertexAction_free' Wq

/-- The product of the Shapiro coordinates over the plane orbits, in degree three. -/
def planeCoordPi : planeK.homology 3 →ₗ[ℚ]
    (∀ a : labelOrbits Γ6 Plane, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3) :=
  LinearMap.pi fun a => (faceCoord (MulAction.stabilizer Γ6 a.out) Wq (1 : RationalGL3) a.out (fun g => g.2) 3).hom

theorem planeCoordPi_bijective : Function.Bijective planeCoordPi :=
  faceCoord_product_bijective_succ 2 (1 : RationalGL3) vertexAction_free' Wq

theorem flagCoord_line (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out)
    (s : lineK.homology 3) :
    flagCoordPi Wq ((HomologicalComplex.homologyMap (homPullback flagLineHom.hom Wq) 3).hom s) o =
      (lineTransportAt o γ hγ).hom (lineCoordPi s (flagLineOrbit o)) :=
  congrArg (fun φ => φ.hom s)
    (faceCoord_pullback_conj flagLineOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant
      vertexAction_free' (MulAction.stabilizer Γ6 o.out) Wq (1 : RationalGL3) o.out (fun g => g.2) γ
      (flagLineOrbit o).out hγ.symm
      (conjStabHom γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ))
      (conjStabHom_apply γ (flagLineOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ)) 3)

theorem flagCoord_plane (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out)
    (s : planeK.homology 3) :
    flagCoordPi Wq ((HomologicalComplex.homologyMap (homPullback flagPlaneHom.hom Wq) 3).hom s) o =
      (planeTransportAt o γ hγ).hom (planeCoordPi s (flagPlaneOrbit o)) :=
  congrArg (fun φ => φ.hom s)
    (faceCoord_pullback_conj flagPlaneOf TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant
      vertexAction_free' (MulAction.stabilizer Γ6 o.out) Wq (1 : RationalGL3) o.out (fun g => g.2) γ
      (flagPlaneOrbit o).out hγ.symm
      (conjStabHom γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ))
      (conjStabHom_apply γ (flagPlaneOrbit o).out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ)) 3)

/-- **Relation (R) for lines**: for every choice of elements `γ o` of `Γ(6)` carrying the representative of the line orbit to the line of the representative flag, the corner functional kills
every family of classes of the line stabilizers transported to the flag groups. -/
theorem line_relation (γ : labelOrbits Γ6 Flag → Γ6) (hγ : ∀ o, γ o • (flagLineOrbit o).out = flagLineOf o.out)
    (σ : ∀ a : labelOrbits Γ6 Line, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3) :
    ∑ o, flagPhi o ((lineTransportAt o (γ o) (hγ o)).hom (σ (flagLineOrbit o))) = 0 := by
  obtain ⟨s, rfl⟩ := lineCoordPi_bijective.2 σ
  have h := flagPhi_line_pullback s
  rw [← h]
  exact Finset.sum_congr rfl fun o _ => by rw [flagCoord_line o (γ o) (hγ o) s]

/-- **Relation (R) for planes**. -/
theorem plane_relation (γ : labelOrbits Γ6 Flag → Γ6) (hγ : ∀ o, γ o • (flagPlaneOrbit o).out = flagPlaneOf o.out)
    (σ : ∀ a : labelOrbits Γ6 Plane, groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype Wq) 3) :
    ∑ o, flagPhi o ((planeTransportAt o (γ o) (hγ o)).hom (σ (flagPlaneOrbit o))) = 0 := by
  obtain ⟨s, rfl⟩ := planeCoordPi_bijective.2 σ
  have h := flagPhi_plane_pullback s
  rw [← h]
  exact Finset.sum_congr rfl fun o _ => by rw [flagCoord_plane o (γ o) (hγ o) s]

end Flags

end TernaryPeriodPolynomials.Argument.GammaNStokes
