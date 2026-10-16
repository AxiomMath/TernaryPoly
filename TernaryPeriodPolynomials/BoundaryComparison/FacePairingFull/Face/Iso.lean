module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Surjective
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Uniform

@[expose] public section


/-!
# Locally inner classes are the mixed cuspidal classes `𝒞_F(E)` of the paper

For a flag `F` whose stabilizer splits as `N ⋊ L` with `L` embedding in `GL₂(ℤ) × ℤˣ` and the radical
fixing every complete flag over `F`, the Hochschild-Serre mixed map is a linear isomorphism from the
radical-zero part of `H²(Γ_F, E)` onto `H¹(L, H¹(N, E))` (injective since
`H²(L, E^N) = 0`, surjective by `Face/Surjective`), and under it the locally inner classes
correspond to the **mixed cuspidal subspace** `FaceCuspidal`: the classes of `H¹(L, H¹(N, E))`
whose pullback to the cusp subgroup of every complete flag over `F` vanishes. This is exactly the
group `𝒞_R(E)` of Appendix C.2 attached to the face `F`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

section Kernel

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

theorem radicalKernelMixedMap_injective (hL : LeviH2Vanishes Levi) :
    Function.Injective (radicalKernelMixedMap action representation) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro coordinate zero
  have mem := (radicalKernelMixedMap_zero_iff_mem_inflation action representation coordinate).mp zero
  obtain ⟨y, hy⟩ := mem
  rw [hL _ y, map_zero] at hy
  exact Subtype.ext hy.symm

/-- **The Hochschild-Serre isomorphism** `ker(res to N) ≃ H¹(L, H¹(N, E))`. -/
def radicalKernelMixedEquiv (hL : LeviH2Vanishes Levi) :
    (radicalRestrictionH2 action representation).ker ≃ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation action representation) :=
  LinearEquiv.ofBijective (radicalKernelMixedMap action representation)
    ⟨radicalKernelMixedMap_injective action representation hL,
      radicalKernelMixedMap_surjective action representation hL⟩

end Kernel

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- The radical-zero classes of `H²(Γ_F, E)`, in the ambient model. -/
def faceRadicalZero : Submodule ℂ (H2 (fixedPointLevel rationalLevel F)
    (rationalCoefficientComponent degree character)) :=
  (radicalRestrictionH2 action (faceRep action degree character F ι)).ker.comap
    (faceH2Equiv action degree character F ι).toLinearMap

/-- The mixed cuspidal subspace of `H¹(L, H¹(N, E))` attached to the face `F`. -/
def FaceCuspidal : Submodule ℂ
    (CrossedH1 (leviCrossedH1Representation action (faceRep action degree character F ι))) :=
  ⨅ e : {e : Edges // endpoint side e = F},
    LinearMap.ker (crossedPullbackH1 (faceCusp action F ι e.val).subtype
      (leviCrossedH1Representation action (faceRep action degree character F ι)))

theorem mem_faceCuspidal_iff
    (m : CrossedH1 (leviCrossedH1Representation action (faceRep action degree character F ι))) :
    m ∈ FaceCuspidal action degree character F ι ↔
      ∀ e : {e : Edges // endpoint side e = F},
        crossedPullbackH1 (faceCusp action F ι e.val).subtype
          (leviCrossedH1Representation action (faceRep action degree character F ι)) m = 0 := by
  unfold FaceCuspidal
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/-- The Hochschild-Serre isomorphism on the ambient `H²`. -/
def faceMixedEquiv (hL : LeviH2Vanishes Levi) :
    faceRadicalZero action degree character F ι ≃ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation action (faceRep action degree character F ι)) :=
  (LinearEquiv.ofSubmodules (faceH2Equiv action degree character F ι)
    (faceRadicalZero action degree character F ι)
    (radicalRestrictionH2 action (faceRep action degree character F ι)).ker
    (Submodule.map_comap_eq_of_surjective (faceH2Equiv action degree character F ι).surjective
      _)).trans (radicalKernelMixedEquiv action (faceRep action degree character F ι) hL)

theorem faceMixedEquiv_apply (hL : LeviH2Vanishes Levi)
    (x : faceRadicalZero action degree character F ι) :
    faceMixedEquiv action degree character F ι hL x =
      radicalKernelMixedMap action (faceRep action degree character F ι)
        ⟨faceH2Equiv action degree character F ι x.val, x.property⟩ :=
  rfl

/-- **Locally inner classes are the mixed cuspidal classes (`ar:eq:facepair` domain).**
Under the Hochschild-Serre isomorphism, the locally inner classes of `H²(Γ_F, E)` correspond to the
mixed cuspidal subspace `FaceCuspidal`. -/
theorem faceMixedEquiv_locallyInner (hL : LeviH2Vanishes Levi)
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ) :
    Submodule.map (faceMixedEquiv action degree character F ι hL).toLinearMap
      (Submodule.comap (faceRadicalZero action degree character F ι).subtype
        (locallyInnerClasses degree character side F)) =
      FaceCuspidal action degree character F ι := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x.val ∈ locallyInnerClasses degree character side F := hx
    obtain ⟨radicalZero, h⟩ := (face_locallyInner_iff_uniform action degree character F ι hfix ψ
      injective x.val).mp hx'
    refine (Submodule.mem_iInf _).mpr fun e => ?_
    exact h e.val e.property
  · intro hy
    obtain ⟨x, rfl⟩ := (faceMixedEquiv action degree character F ι hL).surjective y
    refine ⟨x, ?_, rfl⟩
    show x.val ∈ locallyInnerClasses degree character side F
    refine (face_locallyInner_iff_uniform action degree character F ι hfix ψ injective x.val).mpr
      ⟨x.property, fun e he => ?_⟩
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hy ⟨e, he⟩)

theorem locallyInner_le_faceRadicalZero
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ) :
    locallyInnerClasses degree character side F ≤ faceRadicalZero action degree character F ι :=
  fun x hx => ((face_locallyInner_iff_uniform action degree character F ι hfix ψ injective x).mp
    hx).1

/-- **The locally inner classes of `H²(Γ_F, E)` are isomorphic to the mixed cuspidal group
`𝒞_F(E) ⊂ H¹(L, H¹(N, E))`.** -/
def locallyInnerEquivCuspidal (hL : LeviH2Vanishes Levi)
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ) :
    locallyInnerClasses degree character side F ≃ₗ[ℂ]
      FaceCuspidal action degree character F ι :=
  ((Submodule.comapSubtypeEquivOfLe
    (locallyInner_le_faceRadicalZero action degree character F ι hfix ψ injective)).symm.trans
    ((faceMixedEquiv action degree character F ι hL).submoduleMap _)).trans
    (LinearEquiv.ofEq _ _
      (faceMixedEquiv_locallyInner action degree character F ι hL hfix ψ injective))

theorem finrank_locallyInner_eq (hL : LeviH2Vanishes Levi)
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ) :
    Module.finrank ℂ (locallyInnerClasses degree character side F) =
      Module.finrank ℂ (FaceCuspidal action degree character F ι) :=
  (locallyInnerEquivCuspidal action degree character F ι hL hfix ψ injective).finrank_eq

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
