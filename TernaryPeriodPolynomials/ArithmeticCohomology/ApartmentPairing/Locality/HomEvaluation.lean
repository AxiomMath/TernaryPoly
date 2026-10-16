module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonEvaluation
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapInterior
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


/-!
# The relative Hom class of a cocycle supported in a compact, and its two evaluations

Let `W` be a rational representation of `Γ(6)`, `K` a compact subset of the bordified orbit space
inside the interior, and `φh` a degree-two cocycle of the geometric local cochains supported in `K`.
Its image in the cohomology of the cochains supported in the interior is identified, through
`geometricSupportIso` and `relativeHomGeometricIso`, with a class `xHom` of the Hom cochains of the
relative chains of the pair `(M̄, ∂M̄)` (`xHom`).

* `xHom_cap`: the actual relative cap isomorphism `relativeHomCapIso` sends `xHom` to the relative cap
  of the interior class (`relativeCapMap`).
* `xHom_eval`: the Kronecker evaluation of `xHom` on the class of a relative cycle represented by a
  bordification chain `F` is the value on `F` of the ambient equivariant cochain `ambientCochain`
  (`xHom_eval_cycle` is the same for a chain with relative boundary zero).
* `ambientCochain_eval_generator`: on a singular generator `chainElement` the ambient cochain is the
  geometric coefficient `vertexToFunction` of the supported cochain.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TopologicalSpace HomologicalComplex TernaryPoly
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceBordifiedQuotient
  TernaryPoly.SymmetricSpaceBordifiedPrincipalSix TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SingularBoundaryRestriction TernaryPoly.SingularLocalSupport
  TernaryPoly.SingularLocalCoefficient TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceRelativeCapConnecting
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalCompactCap TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCap.Homology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.EquivariantSingularCohomology

variable (W : Rep.{0} ℚ principalSix) (K : Compacts BordifiedOrbit)
  (hKA : (K : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)

/-- The relative Hom-model class of a degree-two cocycle `φh` supported in `K`: the class of `φh`
is pushed to the cohomology of the cochains supported in the interior, then through
`geometricSupportIso` and `relativeHomGeometricIso` into the Hom cochains of the relative chains of
the pair `(M̄, ∂M̄)`. -/
def xHom (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1))) :
    (homCochains upstairsRelativeChains W).homology 2 :=
  homologyMap (relativeHomGeometricIso W).inv 2
    (homologyMap (geometricSupportIso W).inv 2
      (homologyMap (supportMap wholeProjection W (K : Set BordifiedOrbit)
        (boundary principalSix)ᶜ hKA) 2
        (cochainClass (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh)))

/-- The relative cap isomorphism sends `xHom` to the relative cap of the image of `φh` in the
cohomology of the cochains supported in the interior. -/
theorem xHom_cap (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1))) :
    (relativeHomCapIso W).hom (xHom W K hKA φh) =
      SymmetricSpaceRelativeCap.relativeCapMap W 2 3 rfl
        (homologyMap (supportMap wholeProjection W (K : Set BordifiedOrbit)
          (boundary principalSix)ᶜ hKA) 2
          (cochainClass (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh)) := by
  rw [relativeHomCapIso_hom]
  unfold xHom
  set γ0 := homologyMap (supportMap wholeProjection W (K : Set BordifiedOrbit)
    (boundary principalSix)ᶜ hKA) 2
    (cochainClass (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh) with hγ0
  have h := congrArg (fun f => f (homologyMap (geometricSupportIso W).inv 2 γ0))
    (relativeFundamentalCap_eq_boundaryCapMap W)
  have h1 : homologyMap (relativeHomGeometricIso W).hom 2
      (homologyMap (relativeHomGeometricIso W).inv 2
        (homologyMap (geometricSupportIso W).inv 2 γ0)) =
      homologyMap (geometricSupportIso W).inv 2 γ0 := by
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]
    rfl
  have h2 : homologyMap (geometricSupportIso W).hom 2
      (homologyMap (geometricSupportIso W).inv 2 γ0) = γ0 := by
    rw [← ModuleCat.comp_apply, ← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]
    rfl
  change relativeFundamentalCap W (homologyMap (relativeHomGeometricIso W).hom 2
      (homologyMap (relativeHomGeometricIso W).inv 2
        (homologyMap (geometricSupportIso W).inv 2 γ0))) = _
  rw [h1]
  change _ = SingularLocalBoundaryCap.boundaryCapMap wholeProjection W (boundary principalSix) 3
        SymmetricSpaceRelativeFundamental.fundamentalClass 2 3 rfl γ0
  refine h.symm.trans ?_
  rw [ModuleCat.comp_apply, h2]

/-- The relative Hom cochains include into the ambient geometric cochains as the precomposition
with the quotient map. -/
theorem relativeHomGeometricIso_inclusion :
    (relativeHomGeometricIso W).hom ≫ kernel.ι (geometricBoundaryRestriction W) =
      homPullback (cokernel.π upstairsBoundaryChainMap) W ≫
        (cochainIso wholeProjection wholeQuotientCovering W).hom := by
  unfold relativeHomGeometricIso relativeHomKernelIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [boundaryGeometricIso_inclusion, ← Category.assoc (kernelIsoOfEq _).hom,
    kernelIsoOfEq_hom_comp_ι, ← Category.assoc, HomCokernelKernel.cochainIso_hom_inclusion]

/-- The composite `supportMap ≫ geometricSupportIso⁻¹ ≫ relativeHomGeometricIso⁻¹` followed by the
quotient-precomposition is the supported inclusion followed by the inverse of the singular/geometric
cochain isomorphism. -/
theorem supportMap_geometric_pullback (S : Set BordifiedOrbit)
    (hS : S ⊆ (boundary principalSix)ᶜ) :
    (supportMap wholeProjection W S (boundary principalSix)ᶜ hS ≫ (geometricSupportIso W).inv ≫
        (relativeHomGeometricIso W).inv) ≫
        homPullback (cokernel.π upstairsBoundaryChainMap) W =
      supportInclusion wholeProjection W S ≫
        (cochainIso wholeProjection wholeQuotientCovering W).inv := by
  apply (cancel_mono (cochainIso wholeProjection wholeQuotientCovering W).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← relativeHomGeometricIso_inclusion, Iso.inv_hom_id_assoc,
    ← geometricSupportIso_inclusion, Iso.inv_hom_id_assoc]
  exact supportMap_inclusion wholeProjection W S _ hS

/-- A cochain cycle given in the `sc'` model represents the same class as the corresponding cycle
of the complex. -/
theorem cochainClass_eq_homologyπ (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (a : ℕ)
    (x : Cycles (C.sc' (a - 1) a (a + 1))) (x' : C.cycles a)
    (h : C.iCycles a x' = x.val) :
    cochainClass C a x = C.homologyπ a x' := by
  apply (ModuleCat.mono_iff_injective (C.homologyι a)).mp inferInstance
  have h1 := Algebra.represented_opcycles C (a - 1) a (a + 1) (up_prev _) (up_next _) x
  have h2 := congrArg (fun f => f x') (C.homology_π_ι a)
  change C.homologyι a (cochainClass C a x) = C.pOpcycles a x.val at h1
  change C.homologyι a (C.homologyπ a x') = C.pOpcycles a (C.iCycles a x') at h2
  rw [h1, h2, h]

/-- The ambient equivariant Hom cochain on the bordification determined by a cocycle supported in
`K`. -/
def ambientCochain (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1))) :
    (equivariantChains principalSix (TopCat.of Glued)).X 2 ⟶ W :=
  (cochainIso wholeProjection wholeQuotientCovering W).inv.f 2
    ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val)

/-- On a singular generator, the ambient cochain is the geometric coefficient of the supported
cochain at the lifted simplex. -/
theorem ambientCochain_eval_generator
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (τ : SingularSimplex (TopCat.of Glued) 2) :
    (ambientCochain W K φh).hom (chainElement principalSix (TopCat.of Glued) 2 τ) =
      vertexToFunction wholeProjection wholeQuotientCovering
        ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val) τ := by
  have h := vertexToFunction_homVertexEquiv wholeProjection wholeQuotientCovering W 2
    (ambientCochain W K φh) τ
  have h2 : homVertexEquiv wholeProjection wholeQuotientCovering W 2 (ambientCochain W K φh) =
      (supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val :=
    congrArg
      (fun f => f ((supportInclusion wholeProjection W (K : Set BordifiedOrbit)).f 2 φh.val))
      (congrArg (fun g => g.hom) (HomologicalComplex.congr_hom
        (Iso.inv_hom_id (cochainIso wholeProjection wholeQuotientCovering W)) 2))
  rw [h2] at h
  exact (h.trans (cochainFunctionEquiv_apply _ _ _ _ _ _)).symm

/-- **Kronecker evaluation of the relative Hom class.**  For a relative cycle `z` of the pair
`(M̄, ∂M̄)` represented by a chain `F` of the bordification, the class `xHom` evaluates on the class
of `z` as the ambient equivariant cochain `ambientCochain` evaluates on `F`. -/
theorem xHom_eval
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (z : upstairsRelativeChains.cycles 2)
    (F : (equivariantChains principalSix (TopCat.of Glued)).X 2)
    (hF : (upstairsRelativeSequence.g.f 2).hom F = (upstairsRelativeChains.iCycles 2).hom z) :
    (homologyEvaluation upstairsRelativeChains W 2 (xHom W K hKA φh)).hom
        (upstairsRelativeChains.homologyπ 2 z) = (ambientCochain W K φh).hom F := by
  have hd : (supportCochains wholeProjection W (K : Set BordifiedOrbit)).d 2 3 φh.val = 0 :=
    φh.property
  let x1 : (supportCochains wholeProjection W (K : Set BordifiedOrbit)).cycles 2 :=
    (supportCochains wholeProjection W (K : Set BordifiedOrbit)).cyclesMk φh.val 3
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)) hd
  have hx1 : (supportCochains wholeProjection W (K : Set BordifiedOrbit)).iCycles 2 x1 =
      φh.val :=
    (supportCochains wholeProjection W (K : Set BordifiedOrbit)).i_cyclesMk φh.val 3
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)) hd
  have hcl := cochainClass_eq_homologyπ
    (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh x1 hx1
  let T := supportMap wholeProjection W (K : Set BordifiedOrbit) (boundary principalSix)ᶜ hKA ≫
    (geometricSupportIso W).inv ≫ (relativeHomGeometricIso W).inv
  have hx : xHom W K hKA φh =
      (homCochains upstairsRelativeChains W).homologyπ 2 (cyclesMap T 2 x1) := by
    have hnat := congrArg (fun f => f x1) (HomologicalComplex.homologyπ_naturality T 2)
    have e1 : xHom W K hKA φh = homologyMap T 2
        (cochainClass (supportCochains wholeProjection W (K : Set BordifiedOrbit)) 2 φh) := by
      unfold xHom
      simp only [T, homologyMap_comp]
      rfl
    rw [e1, hcl]
    exact hnat
  have hc : (homCochains upstairsRelativeChains W).iCycles 2 (cyclesMap T 2 x1) =
      T.f 2 φh.val := by
    have h1 := congrArg (fun f => f x1) (HomologicalComplex.cyclesMap_i T 2)
    refine h1.trans ?_
    change T.f 2 ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).iCycles 2 x1) = _
    rw [hx1]
  rw [hx, homologyEvaluation_apply]
  change ((homCochains upstairsRelativeChains W).iCycles 2 (cyclesMap T 2 x1)).hom
    ((upstairsRelativeChains.iCycles 2).hom z) = _
  rw [hc, ← hF]
  have hE := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (supportMap_geometric_pullback W (K : Set BordifiedOrbit) hKA) 2) φh.val
  exact congrArg (fun c => c.hom F) hE

local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs
    ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- The evaluation formula for a bordification chain `F` whose image in the relative chains is a
cycle, with the relative cycle formed by `cyclesMk`. -/
theorem xHom_eval_cycle
    (φh : Cycles ((supportCochains wholeProjection W (K : Set BordifiedOrbit)).sc'
      (2 - 1) 2 (2 + 1)))
    (F : (equivariantChains principalSix (TopCat.of Glued)).X 2)
    (hF : (upstairsRelativeChains.d 2 1).hom ((upstairsRelativeSequence.g.f 2).hom F) = 0) :
    (homologyEvaluation upstairsRelativeChains W 2 (xHom W K hKA φh)).hom
        (upstairsRelativeChains.homologyπ 2
          (upstairsRelativeChains.cyclesMk ((upstairsRelativeSequence.g.f 2).hom F) 1
            ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)) hF)) =
      (ambientCochain W K φh).hom F :=
  xHom_eval W K hKA φh _ F
    (upstairsRelativeChains.i_cyclesMk ((upstairsRelativeSequence.g.f 2).hom F) 1
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)) hF).symm

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
