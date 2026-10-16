module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso
public import TernaryPeriodPolynomials.BoundaryComparison.MixedCuspidal.FaceBridge

@[expose] public section


/-!
# Surjectivity of the Hochschild-Serre edge for the line and plane cusps of `Γ(N)`

Formalized by Claude Sonnet 5.5.
Paper: Appendix C,
(`0 → H¹(L_R, H¹(N_R, E)) → H²(Γ_R, E) → H²(N_R, E)^{L_R}`, "`L_R` has rational cohomological dimension one").

* `splitCohomologyEdge_surjective`: for any split extension whose Levi has vanishing complex `H²`, the library's edge
  `splitCohomologyEdge` is onto `H¹(L, H¹(N, E))`.  Proof: pass to the semidirect product model
  (`SeedC3S4c.semidirectH2Map`, `semidirect_edge`), use the face library's `radicalKernelMixedMap_surjective` and
  `MixedCuspidalFaceBridge.crossed_mixed_class_is_edge`.
* `leviH2Vanishes_subgroup`: every subgroup of `SL₂(ℤ)` (in particular `Γ₂(N)`) has vanishing `H²`.
* `lineFaceEdge_surjective`, `lineEdge_surjective`, `faceEdge_surjective` (with the existing `SeedC3S4c.faceEdge_injective`): edges of the line and plane cusps
  of `Γ(N)` are bijective; `lineFaceEdgeEquiv` is the Hochschild-Serre isomorphism.
* `lineFaceCuspidalEmbedding`: the paper's injection `𝒞_{Q'}(E) → H²(Γ_{Q'}, E)`, with `lineFaceCuspidalInH2_eq_range`:
  its image is exactly `lineFaceCuspidalInH2` (this is where surjectivity is used).
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFaces

/-- The embedding of a subgroup of `SL₂(ℤ)` into `GL₂(ℤ) × ℤˣ`. -/
def leviEmbedding (Λ : Subgroup SL(2, ℤ)) : Λ →* GL (Fin 2) ℤ × ℤˣ :=
  (Matrix.SpecialLinearGroup.toGL.comp Λ.subtype).prod 1

theorem leviEmbedding_injective (Λ : Subgroup SL(2, ℤ)) : Function.Injective (leviEmbedding Λ) := by
  intro a b hab
  have h1 := congrArg Prod.fst hab
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrArg (fun g : GL (Fin 2) ℤ => (g : Matrix (Fin 2) (Fin 2) ℤ) i j) h1
  simpa [leviEmbedding] using this

theorem leviH2Vanishes_subgroup (Λ : Subgroup SL(2, ℤ)) :
    TernaryPeriodPolynomials.Argument.FacePairingFull.Face.LeviH2Vanishes Λ :=
  TernaryPeriodPolynomials.Argument.FacePairingFull.Face.leviH2Vanishes_of_binary _
    (leviEmbedding_injective Λ)

section Generic

variable {N E L : Type} [Group N] [Group E] [Group L] {ext : GroupExtension N E L}
  (s : ext.Splitting) (ρ : Rep ℂ E)

/-- **Surjectivity of the Hochschild-Serre edge of a split extension** whose Levi has vanishing complex
`H²`: every class of `H¹(L, H¹(N, E))` is the edge of a class of `H²(E, ρ)` restricting to zero on the radical. -/
theorem splitCohomologyEdge_surjective
    (hL : TernaryPeriodPolynomials.Argument.FacePairingFull.Face.LeviH2Vanishes L) :
    Function.Surjective (splitCohomologyEdge s ρ) := by
  intro w
  set ρ' : Representation ℂ (N ⋊[s.conjAct] L) ρ := ρ.ρ.comp s.semidirectProductMulEquiv.toMonoidHom
  obtain ⟨x0, hx0⟩ := TernaryPeriodPolynomials.Argument.FacePairingFull.Face.radicalKernelMixedMap_surjective
    s.conjAct ρ' hL ((leviMixedEquiv s.conjAct ρ').symm (semidirectH1Equiv s ρ w))
  have h1 := TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalFaceBridge.crossed_mixed_class_is_edge
    s.conjAct ρ' x0
  rw [hx0, LinearEquiv.apply_symm_apply] at h1
  obtain ⟨y, hy⟩ := (semidirectH2Map_bijective s ρ).2 (h2Equiv ρ' x0.1)
  have hyker : y ∈ (twoCohomologyRestriction ext.inl ρ).ker := by
    rw [LinearMap.mem_ker, ← semidirectH2Map_restriction_eq_zero_iff s ρ y, hy]
    exact LinearMap.mem_ker.mp (h2Equiv_mem_ker s.conjAct ρ' x0)
  refine ⟨⟨y, hyker⟩, ?_⟩
  apply (semidirectH1Equiv s ρ).injective
  refine (semidirect_edge s ρ ⟨y, hyker⟩).symm.trans ?_
  refine Eq.trans ?_ h1.symm
  congr 1
  exact Subtype.ext hy

end Generic

section Faces

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- The edge of the standard line group is onto `H¹(Γ₂(N), H¹(N_Q, E))`. -/
theorem lineEdge_surjective : Function.Surjective (lineEdge N n) :=
  splitCohomologyEdge_surjective _ _ (leviH2Vanishes_subgroup _)

/-- **The Hochschild-Serre edge of the line cusp `h⁻¹ Q h` of `Γ(N)` is surjective**:
every class of `H¹(L_{Q'}, H¹(N_{Q'}, E))` is the mixed class of a class of `H²(Γ_{Q'}, E)` restricting to zero on the radical. -/
theorem lineFaceEdge_surjective : Function.Surjective (lineFaceEdge N h n) :=
  splitCohomologyEdge_surjective _ _ (leviH2Vanishes_subgroup _)

/-- The Hochschild-Serre isomorphism of the line cusp `h⁻¹ Q h`:
`ker(H²(Γ_{Q'}, E) → H²(N_{Q'}, E)) ≃ H¹(L_{Q'}, H¹(N_{Q'}, E))`. -/
def lineFaceEdgeEquiv : (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)).ker ≃ₗ[ℂ]
    groupCohomology.H1 (lineFaceRadH1 N h n) :=
  LinearEquiv.ofBijective (lineFaceEdge N h n) ⟨lineFaceEdge_injective N h n, lineFaceEdge_surjective N h n⟩

/-- The edge of the plane cusp `h⁻¹ P h` of `Γ(N)` is onto `H¹(Γ₂(N), H¹(N_{P'}, E))`. -/
theorem faceEdge_surjective : Function.Surjective (faceEdge N h n) :=
  splitCohomologyEdge_surjective _ _ (leviH2Vanishes_subgroup _)

/-- The injection `𝒞_{Q'}(E) → H²(Γ_{Q'}, E)` of the paper: the inverse of the edge on the mixed
cuspidal group, followed by the inclusion of the radical-zero classes. -/
def lineFaceCuspidalEmbedding : lineFaceCuspidal N h n →ₗ[ℂ] groupCohomology.H2 (lineFaceRep N h n) :=
  (LinearMap.ker (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n))).subtype ∘ₗ
    (lineFaceEdgeEquiv N h n).symm.toLinearMap ∘ₗ (lineFaceCuspidal N h n).subtype

theorem lineFaceCuspidalEmbedding_injective : Function.Injective (lineFaceCuspidalEmbedding N h n) := by
  intro a b hab
  have h1 : (lineFaceEdgeEquiv N h n).symm (a : groupCohomology.H1 (lineFaceRadH1 N h n)) =
      (lineFaceEdgeEquiv N h n).symm (b : groupCohomology.H1 (lineFaceRadH1 N h n)) :=
    Subtype.ext hab
  exact Subtype.ext ((lineFaceEdgeEquiv N h n).symm.injective h1)

/-- **`𝒞_{Q'}(E)` is exactly the image of the injection**: the group `lineFaceCuspidalInH2` of the library (defined through the
preimage of `𝒞_{Q'}(E)` under the edge) equals the range of the paper's injection `𝒞_{Q'}(E) → H²`, as the edge is onto. -/
theorem lineFaceCuspidalInH2_eq_range :
    lineFaceCuspidalInH2 N h n = LinearMap.range (lineFaceCuspidalEmbedding N h n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨lineFaceEdge N h n x, hx⟩, ?_⟩
    change ((lineFaceEdgeEquiv N h n).symm (lineFaceEdge N h n x) :
      (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)).ker).1 = x.1
    have : (lineFaceEdgeEquiv N h n).symm (lineFaceEdge N h n x) = x :=
      (lineFaceEdgeEquiv N h n).symm_apply_apply x
    rw [this]
  · rintro ⟨c, rfl⟩
    refine ⟨(lineFaceEdgeEquiv N h n).symm c.1, ?_, rfl⟩
    change lineFaceEdge N h n ((lineFaceEdgeEquiv N h n).symm c.1) ∈ lineFaceCuspidal N h n
    have : lineFaceEdge N h n ((lineFaceEdgeEquiv N h n).symm c.1) = c.1 :=
      (lineFaceEdgeEquiv N h n).apply_symm_apply c.1
    rw [this]
    exact c.2

/-- The same, in the direction used by the paper: a class of `H²(Γ_{Q'}, E)` lies in the image of `𝒞_{Q'}(E)` iff it has zero
radical restriction and cuspidal edge (the edge needs no surjectivity hypothesis for this statement). -/
theorem mem_lineFaceCuspidalInH2_iff (y : groupCohomology.H2 (lineFaceRep N h n)) :
    y ∈ lineFaceCuspidalInH2 N h n ↔
      ∃ hy : twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n) y = 0,
        lineFaceEdge N h n ⟨y, hy⟩ ∈ lineFaceCuspidal N h n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨⟨y, hy⟩, hx, rfl⟩

end Faces

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
