module

public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationTriple
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationContinuity
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationGlobal

@[expose] public section


noncomputable section
namespace TernaryPoly.HalfSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalLocalChartHomology

variable {X : Type} [TopologicalSpace X] (A : Set X) (x : A)

/-- The actual punctured boundary subtype is homeomorphic to the literal ambient punctured subset. -/
def puncturedSubspaceHomeomorph : ↥({x}ᶜ : Set A) ≃ₜ ↥(A \ {x.val}) where
  toFun a := ⟨a.val.val,a.val.property,fun h => a.property (Subtype.ext h)⟩
  invFun a := ⟨⟨a.val,a.property.1⟩,fun h => a.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The literal boundary-puncture chain inclusion followed by ambient inclusion is the
same map as its actual ambient-subspace inclusion, through the displayed homeomorphism. -/
theorem puncturedSubspace_square :
    inclusion ({x}ᶜ : Set A) ≫ inclusion A =
      (chainHomeomorphIso (puncturedSubspaceHomeomorph A x)).hom ≫ inclusion (A \ {x.val}) := by
  change RationalSingularAugmentation.chainMap _ ≫ RationalSingularAugmentation.chainMap _ =
    RationalSingularAugmentation.chainMap _ ≫ RationalSingularAugmentation.chainMap _
  rw [← RationalSingularAugmentation.chainMap_comp,← RationalSingularAugmentation.chainMap_comp]
  rfl

/-- The actual nested quotient equals the relative complex of the literal ambient punctured subset. -/
def puncturedRelativeIso :
    cokernel (inclusion ({x}ᶜ : Set A) ≫ inclusion A) ≅ relativeChains (A \ {x.val}) :=
  cokernel.mapIso _ _ (chainHomeomorphIso (puncturedSubspaceHomeomorph A x)) (Iso.refl _)
    (by simpa only [Iso.refl_hom,Category.comp_id] using puncturedSubspace_square A x)

/-- Literal forgetting of the boundary puncture. -/
def forgetPuncture : relativeChains (A \ {x.val}) ⟶ relativeChains A :=
  relativeMap (ContinuousMap.id X) _ _ (fun _ h => h.1)

/-- The punctured-relative comparison commutes with the actual nested quotient projection. -/
theorem puncturedRelativeIso_forget :
    (puncturedRelativeIso A x).hom ≫ forgetPuncture A x =
      (tripleSequence (inclusion ({x}ᶜ : Set A)) (inclusion A)).g := by
  apply (cancel_epi (cokernel.π (inclusion ({x}ᶜ : Set A) ≫ inclusion A))).mp
  simp [puncturedRelativeIso,forgetPuncture,tripleSequence,kernelCokernelCompSequence.snakeInput,
    relativeMap,cokernel.mapIso,cokernel.map,RationalSingularAugmentation.chainMap]

/-- Literal forgetting of the puncture preserves restriction to every ambient interior point. -/
theorem forgetPuncture_point (y : X) (hy : y ∉ A) :
    forgetPuncture A x ≫ pointRestriction A y hy =
      pointRestriction (A \ {x.val}) y (fun h => hy h.1) := by
  unfold forgetPuncture pointRestriction
  erw [RationalRelativeExcision.relativeMap_comp]
  rfl

variable [T2Space X]

/-- A nonzero interior germ in every boundary-point neighborhood forces the literal
boundary connecting image to be nonzero locally, provided ambient local homology vanishes there. -/
theorem boundaryPoint_nonzero_of_interior (n : ℕ) (c : (relativeChains A).homology (n+1))
    (hxzero : IsZero ((localChains x.val).homology (n+1)))
    (hnear : ∀ U : Set X, IsOpen U → x.val ∈ U →
      ∃ y ∈ U, ∃ hy : y ∉ A, homologyMap (pointRestriction A y hy) (n+1) c ≠ 0) :
    globalGenerator n (connecting A n c) x ≠ 0 := by
  intro hc
  have hδ : tripleConnecting (inclusion ({x}ᶜ : Set A)) (inclusion A) n c = 0 := by
    rw [tripleConnecting_eq]
    exact hc
  obtain ⟨b,hb⟩ := (tripleConnecting_zero_iff_lifts
    (inclusion ({x}ᶜ : Set A)) (inclusion A) n c).mp hδ
  let bS := homologyMap (puncturedRelativeIso A x).hom (n+1) b
  have hforget : homologyMap (forgetPuncture A x) (n+1) bS = c := by
    change (homologyMap (puncturedRelativeIso A x).hom (n+1) ≫
      homologyMap (forgetPuncture A x) (n+1)) b = c
    rw [← homologyMap_comp,puncturedRelativeIso_forget]
    exact hb
  have hxS : x.val ∉ A \ {x.val} := fun h => h.2 (Set.mem_singleton x.val)
  have hlocal : homologyMap (pointRestriction (A \ {x.val}) x.val hxS) (n+1) bS = 0 :=
    (ModuleCat.subsingleton_of_isZero hxzero).elim _ _
  obtain ⟨U,hU,hxU,hzero⟩ := pointRestriction_zero_near (A \ {x.val}) x.val hxS (n+1) bS hlocal
  obtain ⟨y,hyU,hyA,hy⟩ := hnear U hU hxU
  apply hy
  rw [← hforget]
  change (homologyMap (forgetPuncture A x) (n+1) ≫ homologyMap (pointRestriction A y hyA) (n+1)) bS = 0
  rw [← homologyMap_comp,forgetPuncture_point]
  exact hzero y hyU (fun h => hyA h.1)

end TernaryPoly.HalfSpaceBoundaryOrientation
