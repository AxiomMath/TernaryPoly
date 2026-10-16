module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Cohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Uniform

@[expose] public section


open scoped MatrixGroups

/-!
# The Hochschild-Serre right edge for the actual face groups

Formalized by Claude Sonnet 5.5.

The Levi groups of the faces are subgroups of `SL₂(ℤ)` (`Γ₂(N)`), so their complex `H²` vanishes (`GammaNFacesFull.leviH2Vanishes_subgroup`); the generic
`RightEdge.right_edge_iff` gives, for the plane cusp `h⁻¹Ph` (`faceExt N h`, `faceRep N h n`), the line cusp `h⁻¹Qh` (`lineFaceExt N h`, `lineFaceRep N h n`) and the standard faces
(`gammaNExt N`, `lineExt N`):

  `y ∈ range (res_{N_R} : H²(Γ_R, E) → H²(N_R, E))  ↔  y` is invariant under `L_R = Γ₂(N)` (`splitRadicalH2Action`).

Together with the left edge (`faceEdge_surjective` / `faceEdge_injective`, `lineFaceEdgeEquiv`) this is the full short exact sequence
`0 → H¹(L_R, H¹(N_R, E)) → H²(R, E) → H²(N_R, E)^{L_R} → 0` (`face_hochschild_serre`, `lineFace_hochschild_serre`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Faces

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

theorem levi_h2Vanishes (Λ : Subgroup SL(2, ℤ)) : H2Vanishes Λ :=
  h2Vanishes_of_leviH2Vanishes (leviH2Vanishes_subgroup Λ)

/-- **Right edge at the plane cusp `h⁻¹ P h` of `Γ(N)`.** -/
theorem face_right_edge (y : groupCohomology.H2 (Rep.res (faceExt N h).inl (faceRep N h n))) :
    y ∈ LinearMap.range (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)) ↔
      ∀ l, splitRadicalH2Action (faceSplitting N h) (faceRep N h n) l y = y :=
  right_edge_iff (faceSplitting N h) (faceRep N h n) (levi_h2Vanishes _) y

/-- **Right edge at the line cusp `h⁻¹ Q h` of `Γ(N)`.** -/
theorem lineFace_right_edge (y : groupCohomology.H2 (Rep.res (lineFaceExt N h).inl (lineFaceRep N h n))) :
    y ∈ LinearMap.range (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)) ↔
      ∀ l, splitRadicalH2Action (lineFaceSplitting N h) (lineFaceRep N h n) l y = y :=
  right_edge_iff (lineFaceSplitting N h) (lineFaceRep N h n) (levi_h2Vanishes _) y

/-- Right edge at the standard plane group. -/
theorem gammaN_right_edge (y : groupCohomology.H2 (Rep.res (gammaNExt N).inl (gammaNRep N n))) :
    y ∈ LinearMap.range (twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)) ↔
      ∀ l, splitRadicalH2Action (gammaNSplitting N) (gammaNRep N n) l y = y :=
  right_edge_iff (gammaNSplitting N) (gammaNRep N n) (levi_h2Vanishes _) y

/-- Right edge at the standard line group. -/
theorem line_right_edge (y : groupCohomology.H2 (Rep.res (lineExt N).inl (lineStdRep N n))) :
    y ∈ LinearMap.range (twoCohomologyRestriction (lineExt N).inl (lineStdRep N n)) ↔
      ∀ l, splitRadicalH2Action (lineSplitting N) (lineStdRep N n) l y = y :=
  right_edge_iff (lineSplitting N) (lineStdRep N n) (levi_h2Vanishes _) y

/-- **The Hochschild-Serre short exact sequence of the plane cusp `h⁻¹ P h`**:
`0 → H¹(L_R, H¹(N_R, E)) → H²(Γ_R, E) → H²(N_R, E)^{L_R} → 0`: the edge `ker res ≃ H¹(L_R, H¹(N_R, E))` is bijective and the image of `res` is the Levi-invariants. -/
theorem face_hochschild_serre :
    Function.Bijective (faceEdge N h n) ∧
      ∀ y : groupCohomology.H2 (Rep.res (faceExt N h).inl (faceRep N h n)),
        y ∈ LinearMap.range (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)) ↔
          ∀ l, splitRadicalH2Action (faceSplitting N h) (faceRep N h n) l y = y :=
  ⟨⟨faceEdge_injective N h n, faceEdge_surjective N h n⟩, face_right_edge N h n⟩

/-- **The Hochschild-Serre short exact sequence of the line cusp `h⁻¹ Q h`.** -/
theorem lineFace_hochschild_serre :
    Function.Bijective (lineFaceEdge N h n) ∧
      ∀ y : groupCohomology.H2 (Rep.res (lineFaceExt N h).inl (lineFaceRep N h n)),
        y ∈ LinearMap.range (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)) ↔
          ∀ l, splitRadicalH2Action (lineFaceSplitting N h) (lineFaceRep N h n) l y = y :=
  ⟨⟨lineFaceEdge_injective N h n, lineFaceEdge_surjective N h n⟩, lineFace_right_edge N h n⟩

end Faces

section Semidirect

/-- **The right edge for a semidirect face of the model** (`FacePairingFull.Face`): for `R = Radical ⋊ Levi` with the Levi embedded in `GL₂(ℤ) × ℤˣ`
(bad and good line, identity and good plane), and any complex representation of `R`, the image of the radical restriction is the Levi-invariants of `H²(Radical, ·)`. -/
theorem semidirect_right_edge {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
    (ψ : Levi →* Matrix.GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (hψ : Function.Injective ψ)
    (ρ : Rep ℂ (Radical ⋊[action] Levi))
    (y : groupCohomology.H2 (Rep.res (SemidirectProduct.toGroupExtension action).inl ρ)) :
    y ∈ LinearMap.range (twoCohomologyRestriction (SemidirectProduct.toGroupExtension action).inl ρ) ↔
      ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting action) ρ l y = y :=
  right_edge_iff (SemidirectProduct.inr_splitting action) ρ
    (h2Vanishes_of_leviH2Vanishes (TernaryPeriodPolynomials.Argument.FacePairingFull.Face.leviH2Vanishes_of_binary ψ hψ)) y

end Semidirect

end TernaryPeriodPolynomials.Argument.RightEdge
