module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Generation

@[expose] public section


/-!
# Lemma A.1: dictionary between the sphere families and the paper's prisms

Formalized by Claude Sonnet 5.5.
Paper: Lemma A.1.

For an integral basis `g = (b, X, Y)` with `X, Y, X+Y` Good the triangles
`θ_{k,l} = [X + kb, Y + lb, X + Y + (k+l)b]` of the augmented base triangle are
`CoherentPrismReduction.coherent g (k,l)`.  The prism joining `θ_{k,l}` to `θ_{k+1,l}` is the
prism sphere of the basis `affineBasis g (k,l)`, and the prism joining `θ_{k,l}` to `θ_{k,l+1}`
is, up to sign, the prism sphere of `affineBasis (g * swapGL) (l,k)`; the lemmas below prove these
identities (the four side faces are the `horizontalResidual` and `verticalResidual`), and that all
of these spheres belong to `prismSpheres b`.  Hence the family `prismSpheres b`, which ranges over
all integral bases with first line `b`, contains the paper's prisms of both kinds.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction

local notation "res" => AugmentedPrismCaps.columnResidue

/-- The prism joining `θ_{k,l}` to `θ_{k+1,l}`: `∂(prism) = θ_{k+1,l} - θ_{k,l} - (side faces)`. -/
theorem prismSphere_affineBasis_eq (g : IntegralGL) (k l : ℤ) :
    AugmentedPrismCaps.prismSphere (affineBasis g (k,l)) =
      coherent g (k+1,l) - coherent g (k,l) - horizontalResidual g (k,l) := by
  have h := horizontal_identity g (k,l)
  rw [horizontalCap,AugmentedPrismCaps.boundary_prismCap] at h
  change coherent g (k+1,l) - coherent g (k,l) = _ at h
  rw [h]
  abel

/-- The prism joining `θ_{k,l}` to `θ_{k,l+1}`, the same construction after exchanging `X` and
`Y`. -/
theorem prismSphere_swap_eq (g : IntegralGL) (k l : ℤ) :
    coherent g (k,l+1) - coherent g (k,l) =
      -AugmentedPrismCaps.prismSphere (affineBasis (g * swapGL) (l,k)) + verticalResidual g (k,l) := by
  have h := vertical_identity g (k,l)
  rw [verticalCap,map_neg,AugmentedPrismCaps.boundary_prismCap] at h
  exact h

theorem good_residues_of_good (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hx : Good (xFiber g 0).val) (hy : Good (yFiber g 0).val) (hz : Good (zFiber g 0).val) :
    res g 0 = 0 ∧ res g 1 ≠ 0 ∧ res g 2 ≠ 0 ∧ res g 1 + res g 2 ≠ 0 := by
  have hb : res g 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue g 0 hbad
  exact ⟨hb,(BadVertexSimplexNormalForm.fiberLine_good_iff g hb 0 0).mp hx,
    (BadVertexSimplexNormalForm.fiberLine_good_iff g hb 1 0).mp hy,
    (BadVertexSimplexNormalForm.fiberLine_good_iff g hb 2 0).mp hz⟩

/-- Every horizontal prism sphere `θ_{k,l} → θ_{k+1,l}` lies in `prismSpheres b`. -/
theorem prismSphere_affineBasis_mem {b : RationalLine} (g : IntegralGL)
    (hgb : augmentedLine g 0 = b) (hbad : ¬Good b.val) (hx : Good (xFiber g 0).val)
    (hy : Good (yFiber g 0).val) (hz : Good (zFiber g 0).val) (p : ℤ × ℤ) :
    AugmentedPrismCaps.prismSphere (affineBasis g p) ∈ prismSpheres b := by
  obtain ⟨hb,hX,hY,hZ⟩ := good_residues_of_good g (by rw [hgb]; exact hbad) hx hy hz
  obtain ⟨h0,h1,h2,h3⟩ := affine_residues g hb hX hY hZ p
  exact ⟨affineBasis g p,(BadVertexPrismSupport.affineBasis_line_zero g p).trans hgb,
    fiberLine_good _ h0 h1 h2 h3 0 0,fiberLine_good _ h0 h1 h2 h3 1 0,
    fiberLine_good _ h0 h1 h2 h3 2 0,rfl⟩

/-- Every vertical prism sphere `θ_{k,l} → θ_{k,l+1}` lies in `prismSpheres b`. -/
theorem prismSphere_swap_mem {b : RationalLine} (g : IntegralGL)
    (hgb : augmentedLine g 0 = b) (hbad : ¬Good b.val) (hx : Good (xFiber g 0).val)
    (hy : Good (yFiber g 0).val) (hz : Good (zFiber g 0).val) (p : ℤ × ℤ) :
    AugmentedPrismCaps.prismSphere (affineBasis (g * swapGL) p) ∈ prismSpheres b := by
  obtain ⟨hb,hX,hY,hZ⟩ := good_residues_of_good g (by rw [hgb]; exact hbad) hx hy hz
  obtain ⟨s0,s1,s2,s3⟩ := swap_residues g hb hX hY hZ
  obtain ⟨h0,h1,h2,h3⟩ := affine_residues (g * swapGL) s0 s1 s2 s3 p
  exact ⟨affineBasis (g * swapGL) p,
    ((BadVertexPrismSupport.affineBasis_line_zero _ p).trans
      ((BadVertexMixedCharts.swap_base g).trans hgb)),
    fiberLine_good _ h0 h1 h2 h3 0 0,fiberLine_good _ h0 h1 h2 h3 1 0,
    fiberLine_good _ h0 h1 h2 h3 2 0,rfl⟩

end TernaryPeriodPolynomials.Argument.AppendixALink
