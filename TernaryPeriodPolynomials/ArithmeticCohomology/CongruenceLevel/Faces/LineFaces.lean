module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineGroup

@[expose] public section


/-!
# The mixed cuspidal groups of all line cusps of `Γ(N)` and their Hochschild-Serre edges

Formalized by Claude Sonnet 5.5.
Paper: Appendix C (`ar:sec:stokes`),:
"`𝒞_R(E)` is the direct sum over faces of type `R` of the subspaces `H¹(L_R, H¹(N_R, E))` whose restrictions at all rational cusps
of the binary Levi vanish ... They inject into degree-two face cohomology by Hochschild-Serre, since `L_R` has rational
cohomological dimension one", and "we use the same letters for rational conjugates at the other cusps".

This is the line analogue (`R = Q`) of `SeedC3S4c.PlaneCusps` (`gammaNPAt`, `faceExt`, `faceRep`, `faceCuspidal`, `faceEdge`).
For `h ∈ SL₃(ℤ)` the line cusp `Q' = h⁻¹ Q h` of `Γ(N)` has the line group `Γ_{Q'} = Γ(N) ∩ h⁻¹ Q(ℤ) h` (`gammaNQAt N h`; for
`N ≥ 3` this is the full stabilizer of the rational line, `mem_lineStab_of_gammaN`), radical `N_{Q'} = h⁻¹ N_Q h`, Levi `Γ₂(N)`, and the
coefficient module `E_n` restricted from `SL₃(ℤ)` (`lineFaceRep N h n`).  `lineFaceCuspidal N h n` is the literal `𝒞_{Q'}(E)`.

* `map_lineCuspidal_eq_lineFaceCuspidal`: conjugation carries `𝒞_Q(E)` onto `𝒞_{Q'}(E)`.
* `lineFaceEdge_kerMap`: the Hochschild-Serre edge is natural for conjugation; `lineFaceEdge_injective`: it is injective
  (`H²(Γ₂(N), W) = 0`), so `𝒞_{Q'}(E)` injects into degree-two cohomology of the line group.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaces

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.SeedC3S4c

section Conj

variable (N : ℕ) (h : SL(3, ℤ))

/-- The line group of the line cusp `h⁻¹ Q h`: the elements `p` of `SL₃(ℤ)` with `h p h⁻¹ ∈ Γ(N) ∩ Q(ℤ)`. -/
def gammaNQAt : Subgroup SL(3, ℤ) := (gammaNQ N).comap (MulAut.conj h).toMonoidHom

theorem mem_gammaNQAt {p : SL(3, ℤ)} : p ∈ gammaNQAt N h ↔ h * p * h⁻¹ ∈ gammaNQ N := Iff.rfl

/-- Conjugation by `h`: `Γ_{h⁻¹Qh} ≃ Γ_Q`. -/
def conjQ : gammaNQAt N h ≃* gammaNQ N where
  toFun p := ⟨h * p.1 * h⁻¹, p.2⟩
  invFun q := ⟨h⁻¹ * q.1 * h, by
    show h * (h⁻¹ * q.1 * h) * h⁻¹ ∈ gammaNQ N
    have : h * (h⁻¹ * q.1 * h) * h⁻¹ = q.1 := by group
    rw [this]; exact q.2⟩
  left_inv p := by apply Subtype.ext; simp [mul_assoc]
  right_inv q := by apply Subtype.ext; simp [mul_assoc]
  map_mul' p q := by apply Subtype.ext; simp [mul_assoc]

end Conj

section FaceData

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- The split extension `Nℤ² → Γ_{h⁻¹Qh} → Γ₂(N)` of the line cusp `h⁻¹ Q h`. -/
def lineFaceExt : GroupExtension RadicalLattice (gammaNQAt N h) (CongruenceSubgroup.Gamma N) :=
  FaceTransport.pullbackExt (lineExt N) (conjQ N h)

/-- The equivalence of the conjugate extension with the standard one. -/
def lineFaceEquiv : (lineFaceExt N h).Equiv (lineExt N) :=
  FaceTransport.pullbackEquiv (lineExt N) (conjQ N h)

/-- The Levi splitting of the conjugate line group. -/
def lineFaceSplitting : (lineFaceExt N h).Splitting :=
  FaceTransport.splitting (lineFaceEquiv N h) (lineSplitting N)

/-- The coefficient module `E_n` restricted to the standard line group `Γ(N) ∩ Q(ℤ)`. -/
def lineStdRep (n : ℕ) : Rep ℂ (gammaNQ N) := Rep.of ((ambRep n).comp (gammaNQ N).subtype)

/-- **The coefficient module `E_n` restricted to the line group of the cusp `h⁻¹ Q h`.** -/
def lineFaceRep (n : ℕ) : Rep ℂ (gammaNQAt N h) :=
  Rep.of ((ambRep n).comp (gammaNQAt N h).subtype)

theorem lineFaceT_intertwines (n : ℕ) (g : gammaNQAt N h) (v : GeneralEisenstein.HomogeneousPoly n) :
    faceT h n ((lineStdRep N n).ρ ((lineFaceEquiv N h).toMulEquiv g) v) =
      (lineFaceRep N h n).ρ g (faceT h n v) := by
  have e1 : (lineStdRep N n).ρ ((lineFaceEquiv N h).toMulEquiv g) v = ambRep n (h * g.1 * h⁻¹) v := rfl
  rw [e1, faceT_apply, faceT_apply]
  change ambRep n h⁻¹ (ambRep n (h * g.1 * h⁻¹) v) = ambRep n g.1 (ambRep n h⁻¹ v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- Transport of the radical-kernel classes of `H²` from the standard line group to that of `h⁻¹ Q h`. -/
def lineFaceKerMap (n : ℕ) :
    (twoCohomologyRestriction (lineExt N).inl (lineStdRep N n)).ker →ₗ[ℂ]
      (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n)).ker :=
  FaceTransport.kerMap (lineFaceEquiv N h) (lineStdRep N n) (lineFaceRep N h n) (faceT h n)
    (lineFaceT_intertwines N h n)

/-- The module `H¹(N_{Q'}, E_n)` of the line cusp `Q' = h⁻¹ Q h` over its Levi `Γ₂(N)`. -/
abbrev lineFaceRadH1 (n : ℕ) : Rep ℂ (CongruenceSubgroup.Gamma N) :=
  splitRadicalH1Representation (lineFaceSplitting N h) (lineFaceRep N h n)

/-- The module `H¹(N_Q, E_n)` of the standard line cusp over its Levi. -/
abbrev lineRadH1 (n : ℕ) : Rep ℂ (CongruenceSubgroup.Gamma N) :=
  splitRadicalH1Representation (lineSplitting N) (lineStdRep N n)

/-- **The mixed cuspidal group `𝒞_Q(E)` of the standard line cusp**. -/
def lineCuspidal (n : ℕ) : Submodule ℂ (groupCohomology.H1 (lineRadH1 N n)) :=
  cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineRadH1 N n)

/-- **The mixed cuspidal group `𝒞_{Q'}(E)` of the line cusp `Q' = h⁻¹ Q h`**: the classes of
`H¹(L_{Q'}, H¹(N_{Q'}, E))` (`L_{Q'} = Γ₂(N)`) restricting to zero at every rational cusp of the binary Levi. -/
def lineFaceCuspidal (n : ℕ) : Submodule ℂ (groupCohomology.H1 (lineFaceRadH1 N h n)) :=
  cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineFaceRadH1 N h n)

/-- The isomorphism of Levi modules `H¹(N_Q, E) ≅ H¹(N_{Q'}, E)` induced by the conjugation. -/
def lineFaceModIso (n : ℕ) : lineRadH1 N n ≅ lineFaceRadH1 N h n :=
  FaceTransport.modIso (lineFaceEquiv N h) (lineSplitting N) (lineStdRep N n) (lineFaceRep N h n)
    (faceT h n) (lineFaceT_intertwines N h n)

/-- The conjugation carries `𝒞_Q(E)` onto `𝒞_{Q'}(E)`. -/
theorem map_lineCuspidal_eq_lineFaceCuspidal (n : ℕ) :
    Submodule.map (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
      (lineFaceModIso N h n).hom 1).hom (lineCuspidal N n) = lineFaceCuspidal N h n :=
  FaceTransport.cuspidal_map_eq (lineFaceModIso N h n)

/-- The Hochschild-Serre edge of the standard line group. -/
abbrev lineEdge (n : ℕ) := splitCohomologyEdge (lineSplitting N) (lineStdRep N n)

/-- The Hochschild-Serre edge of the conjugate line group. -/
abbrev lineFaceEdge (n : ℕ) := splitCohomologyEdge (lineFaceSplitting N h) (lineFaceRep N h n)

theorem lineFaceEdge_kerMap (n : ℕ)
    (x : (twoCohomologyRestriction (lineExt N).inl (lineStdRep N n)).ker) :
    lineFaceEdge N h n (lineFaceKerMap N h n x) =
      (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N)) (lineFaceModIso N h n).hom 1).hom
        (lineEdge N n x) :=
  FaceTransport.edge_kerMap (lineFaceEquiv N h) (lineSplitting N) (lineStdRep N n) (lineFaceRep N h n)
    (faceT h n) (lineFaceT_intertwines N h n) x

/-- The Hochschild-Serre edge of the standard line group is injective (`H²(Γ₂(N), W) = 0`): the mixed
cuspidal group injects into degree-two cohomology of the line group. -/
theorem lineEdge_injective (n : ℕ) : Function.Injective (lineEdge N n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (lineSplitting N) (lineStdRep N n)
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)

/-- The Hochschild-Serre edge of the conjugate line group is injective. -/
theorem lineFaceEdge_injective (n : ℕ) : Function.Injective (lineFaceEdge N h n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (lineFaceSplitting N h) (lineFaceRep N h n)
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)

/-- The image of `𝒞_{Q'}(E)` in `H²(Γ_{Q'}, E)` under the inverse of the Hochschild-Serre edge: the classes with zero restriction
to the radical `N_{Q'}` whose mixed class lies in `𝒞_{Q'}(E)`. -/
def lineFaceCuspidalInH2 (n : ℕ) : Submodule ℂ (groupCohomology.H2 (lineFaceRep N h n)) :=
  Submodule.map (LinearMap.ker (twoCohomologyRestriction (lineFaceExt N h).inl
    (lineFaceRep N h n))).subtype (Submodule.comap (lineFaceEdge N h n) (lineFaceCuspidal N h n))

end FaceData

end TernaryPeriodPolynomials.Argument.GammaNFaces
