module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Vanishing

@[expose] public section


/-!
# Locally inner iff mixed cuspidal: the uniform form

For a flag `F` with a split presentation `Γ_F ≃ Radical ⋊ Levi` (`ι`) whose radical fixes every
complete flag over `F` and whose Levi embeds in `GL₂(ℤ) × ℤˣ`, the cusp subgroup of the complete
flag `e` over `F` is `faceCusp e = {l : Levi | ι(l) ∈ Γ_e}` and a class `c ∈ H²(Γ_F, E)` is locally
inner (restricts to zero on every `Γ_e`, `e` over `F`) if and only if it has zero restriction to the
radical and its mixed class in `H¹(Levi, H¹(Radical, E))` restricts to zero on every cusp
subgroup (`face_locallyInner_iff_uniform`): the paper's mixed cuspidal condition (end of
Appendix C.4), with no restriction on the degree `n`. The vanishing of `H²(B, E^N)` needed for
the converse comes from the library's complex `H²`-vanishing for groups embedding in
`GL₂(ℤ) × ℤˣ` (`Face/Vanishing`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- The cusp subgroup of the complete flag `e`: the Levi elements stabilizing it. -/
def faceCusp (e : Edges) : Subgroup Levi :=
  (faceEdgeSubgroup action F ι e).comap SemidirectProduct.inr

/-- **The radical fixes the complete flag**, hence the stabilizer of the complete flag is described
by its Levi component. -/
theorem mem_faceEdgeSubgroup_iff (e : Edges)
    (hfix : ∀ radical : Radical, (ι (SemidirectProduct.inl radical)).val • e = e)
    (x : SemidirectProduct Radical Levi action) :
    x ∈ faceEdgeSubgroup action F ι e ↔ x.right ∈ faceCusp action F ι e := by
  have fact : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right := by
    apply SemidirectProduct.ext <;> simp
  have hl : faceAmbient action F ι (SemidirectProduct.inl x.left) ∈
      fixedPointLevel rationalLevel e :=
    ⟨(ι (SemidirectProduct.inl x.left)).property.1, MulAction.mem_stabilizer_iff.mpr (hfix _)⟩
  have split : faceAmbient action F ι x = faceAmbient action F ι
      (SemidirectProduct.inl x.left) * faceAmbient action F ι (SemidirectProduct.inr x.right) := by
    conv_lhs => rw [fact]
    rw [map_mul]
  change faceAmbient action F ι x ∈ fixedPointLevel rationalLevel e ↔
    faceAmbient action F ι (SemidirectProduct.inr x.right) ∈ fixedPointLevel rationalLevel e
  rw [split]
  exact Subgroup.mul_mem_cancel_left _ hl

/-- **Locally inner iff mixed cuspidal (uniform form).** -/
theorem face_locallyInner_iff_uniform
    (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
      (ι (SemidirectProduct.inl radical)).val • e = e)
    (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)
    (coordinate : H2 (fixedPointLevel rationalLevel F)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character side F ↔
      ∃ radicalZero : faceH2Equiv action degree character F ι coordinate ∈
          (radicalRestrictionH2 action (faceRep action degree character F ι)).ker,
        ∀ e : Edges, endpoint side e = F →
          crossedPullbackH1 (faceCusp action F ι e).subtype
            (leviCrossedH1Representation action (faceRep action degree character F ι))
            (radicalKernelMixedMap action (faceRep action degree character F ι)
              ⟨faceH2Equiv action degree character F ι coordinate, radicalZero⟩) = 0 := by
  have hedge : ∀ e : Edges, endpoint side e = F → EdgeData action degree character F ι e :=
    fun e he => ⟨faceCusp action F ι e, mem_faceEdgeSubgroup_iff action F ι e (hfix · e he),
      fun x => edgeVanishing_of_binary action (faceRep action degree character F ι) ψ injective
        (faceCusp action F ι e) x⟩
  rw [face_locallyInner_iff action degree character F ι hedge]
  constructor
  · rintro ⟨radicalZero, h⟩
    exact ⟨radicalZero, fun e he => h e he _ (mem_faceEdgeSubgroup_iff action F ι e (hfix · e he))⟩
  · rintro ⟨radicalZero, h⟩
    refine ⟨radicalZero, fun e he B hB => ?_⟩
    have hBeq : B = faceCusp action F ι e := by
      ext l
      have h1 := hB (SemidirectProduct.inr l)
      have h2 := mem_faceEdgeSubgroup_iff action F ι e (hfix · e he) (SemidirectProduct.inr l)
      simp only [SemidirectProduct.right_inr] at h1 h2
      exact h1.symm.trans h2
    subst hBeq
    exact h e he

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
