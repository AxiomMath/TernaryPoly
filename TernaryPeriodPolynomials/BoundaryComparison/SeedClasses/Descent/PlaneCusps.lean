module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Transport
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Cusp.Rational

@[expose] public section


/-!
# The mixed cuspidal groups of all plane cusps and the conjugated seeds that span them

Paper: Lemma C.3 (`ar:lem:seed`),: "the holomorphic and antiholomorphic seeds span `𝒞_P(E)` after including all plane
cusps ...", "Rationally conjugate the finitely many other plane cusps to `P` and sum the same
construction over them"; `𝒞_R(E)` is the direct sum over faces of type `R`, and
"we use the same letters for rational conjugates at the other cusps".

For `h ∈ SL₃(ℤ)` the plane cusp `P' = h⁻¹ P h` of `Γ(N)` has the plane group
`Γ_{P'} = Γ(N) ∩ h⁻¹ P(ℚ) h` (`gammaNPAt N h`; for `N ≥ 3` this is the full stabilizer of the
rational plane, `exists_face_of_rational_plane`; the other statements hold for every `N`), the radical `N_{P'} = h⁻¹ N_P h`, the Levi `Γ₂(N)`
(conjugation by `h` induces the identity on Levi blocks) and the coefficient module `E_n` restricted
from `SL₃(ℤ)` (`faceRep`, genuinely the restriction, compared with the standard cusp by `ρ(h⁻¹)`,
`faceT`). `faceCuspidal N h n` is the literal `𝒞_{P'}(E)`: the classes of
`H¹(Γ₂(N), H¹(N_{P'}, E))` (action of the Levi on the radical cohomology by conjugation) restricting
to zero at every rational cusp of the binary Levi (`cuspidalSubspace`). The seed classes at `P'` are
the pullbacks `h^* [ω_f]`, `h^* [\overline{ω_f}]` of the seeds at `P` (`faceSeedKerClass`,
`faceSeedConjKerClass`; `FaceTransport.h2Map` is the pullback of degree-two cohomology along the
conjugation).

* `map_gammaNCuspidal_eq_faceCuspidal`: the conjugation carries `𝒞_P(E)` onto `𝒞_{P'}(E)`
  (isomorphism of Levi modules `faceModIso`).
* `faceEdge_kerMap`: the Hochschild--Serre edge is natural for the conjugation;
  `faceEdge_injective`: it is injective (`H²(Γ₂(N), W) = 0`), so `𝒞_{P'}(E)` injects into degree-two
  cohomology.
* `faceSeed_map_edge_eq_cuspidal`, `faceSeedSpan_eq_cuspidalInH2` (hypothesis
  `ESSpan (Γ(N)) n`, discharged by `Statements.EichlerShimura.eichler_shimura_spanning_gammaN`): the
  conjugated seeds span `𝒞_{P'}(E)`, i.e. its image in `H²(Γ_{P'}, E)`.
* `exists_face_of_rational_plane`: every rational plane `g P g⁻¹` is of this form
  (`ConvergenceC4.rational_cusp_stabilizer`).

Scope: this transports the single-cusp result of `MixedCuspidal` along the integral conjugation; the
selection of one representative `h` in each `Γ(N)`-orbit of planes (the direct sum over faces), the
finite reflections and the comparison with the Borel--Serre face cohomology of the paper's
level-three group are not in this file.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

section Conj

variable (N : ℕ) (h : SL(3, ℤ))

/-- The plane group of the plane cusp `h⁻¹ P h`: the elements `p` of `SL₃(ℤ)` with
`h p h⁻¹ ∈ Γ(N) ∩ P(ℤ)`. -/
def gammaNPAt : Subgroup SL(3, ℤ) := (gammaNP N).comap (MulAut.conj h).toMonoidHom

theorem mem_gammaNPAt {p : SL(3, ℤ)} : p ∈ gammaNPAt N h ↔ h * p * h⁻¹ ∈ gammaNP N := Iff.rfl

/-- Conjugation by `h`: `Γ_{h⁻¹Ph} ≃ Γ_P`. -/
def conjP : gammaNPAt N h ≃* gammaNP N where
  toFun p := ⟨h * p.1 * h⁻¹, p.2⟩
  invFun q := ⟨h⁻¹ * q.1 * h, by
    show h * (h⁻¹ * q.1 * h) * h⁻¹ ∈ gammaNP N
    have : h * (h⁻¹ * q.1 * h) * h⁻¹ = q.1 := by group
    rw [this]; exact q.2⟩
  left_inv p := by apply Subtype.ext; simp [mul_assoc]
  right_inv q := by apply Subtype.ext; simp [mul_assoc]
  map_mul' p q := by apply Subtype.ext; simp [mul_assoc]



end Conj

section FaceData

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- The split extension `Nℤ² → Γ_{h⁻¹Ph} → Γ₂(N)` of the plane cusp `h⁻¹ P h`: the conjugate of
the extension of the standard plane group (radical `h⁻¹ N_P h`, Levi block of `h p h⁻¹`). -/
def faceExt : GroupExtension RadicalLattice (gammaNPAt N h) (CongruenceSubgroup.Gamma N) :=
  FaceTransport.pullbackExt (gammaNExt N) (conjP N h)

/-- The equivalence of the conjugate extension with the standard one. -/
def faceEquiv : (faceExt N h).Equiv (gammaNExt N) :=
  FaceTransport.pullbackEquiv (gammaNExt N) (conjP N h)

/-- The Levi splitting of the conjugate plane group. -/
def faceSplitting : (faceExt N h).Splitting :=
  FaceTransport.splitting (faceEquiv N h) (gammaNSplitting N)

/-- The ambient coefficient representation `E_n` of `SL₃(ℤ)` on `Sym^n((ℂ³)*) ⊗ det⁻¹`. -/
def ambRep (n : ℕ) : Representation ℂ SL(3, ℤ) (GeneralEisenstein.HomogeneousPoly n) :=
  (GeneralEisenstein.realCoefficient n).comp (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The coefficient module `E_n` restricted to the plane group of the cusp `h⁻¹ P h`. -/
def faceRep (n : ℕ) : Rep ℂ (gammaNPAt N h) :=
  Rep.of ((ambRep n).comp (gammaNPAt N h).subtype)

omit [NeZero N] in
theorem gammaNRep_ambient (n : ℕ) (g : gammaNP N) :
    (gammaNRep N n).ρ g = ambRep n g.1 := by
  change (GeneralEisenstein.realCoefficient n) ((gammaNPlaneData N).sigma g) = _
  have : (gammaNPlaneData N).sigma g = Matrix.SpecialLinearGroup.mapGL ℝ g.1 := by
    apply Units.ext
    rw [PlaneData.sigma_val, gammaNPlaneData_plm]
    exact (gammaNSigma_val N g).symm
  rw [this]
  rfl

/-- The coefficient comparison `E_n|_{Γ_P} ≃ E_n|_{Γ_{h⁻¹Ph}}`, `v ↦ ρ(h⁻¹) v`. -/
def faceT (n : ℕ) : GeneralEisenstein.HomogeneousPoly n ≃ₗ[ℂ] GeneralEisenstein.HomogeneousPoly n where
  toLinearMap := ambRep n h⁻¹
  invFun := ambRep n h
  left_inv v := by
    change ambRep n h (ambRep n h⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change ambRep n h⁻¹ (ambRep n h v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem faceT_apply (n : ℕ) (v : GeneralEisenstein.HomogeneousPoly n) :
    faceT h n v = ambRep n h⁻¹ v := rfl

theorem faceT_intertwines (n : ℕ) (g : gammaNPAt N h) (v : GeneralEisenstein.HomogeneousPoly n) :
    faceT h n ((gammaNRep N n).ρ ((faceEquiv N h).toMulEquiv g) v) =
      (faceRep N h n).ρ g (faceT h n v) := by
  have e1 : (gammaNRep N n).ρ ((faceEquiv N h).toMulEquiv g) v = ambRep n (h * g.1 * h⁻¹) v :=
    by rw [gammaNRep_ambient]; rfl
  rw [e1, faceT_apply, faceT_apply]
  change ambRep n h⁻¹ (ambRep n (h * g.1 * h⁻¹) v) = ambRep n g.1 (ambRep n h⁻¹ v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- The transport of the radical-kernel classes of `H²` from the standard plane group to the plane
group of the cusp `h⁻¹ P h` (pullback by the conjugation, `h^*`). -/
def faceKerMap (n : ℕ) : (twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker →ₗ[ℂ]
    (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker :=
  FaceTransport.kerMap (faceEquiv N h) (gammaNRep N n) (faceRep N h n) (faceT h n)
    (faceT_intertwines N h n)

/-- The module `H¹(N_{P'}, E_n)` of the plane cusp `P' = h⁻¹ P h` over its Levi `Γ₂(N)`. -/
abbrev faceRadH1 (n : ℕ) : Rep ℂ (CongruenceSubgroup.Gamma N) :=
  splitRadicalH1Representation (faceSplitting N h) (faceRep N h n)

/-- **The mixed cuspidal group `𝒞_{P'}(E)` of the plane cusp `P' = h⁻¹ P h`**: the
classes of `H¹(L_{P'}, H¹(N_{P'}, E))` (`L_{P'} = Γ₂(N)`, `N_{P'} = h⁻¹ N_P h`, `E` restricted to
`Γ_{P'} = Γ(N) ∩ h⁻¹ P h`) restricting to zero at every rational cusp of the binary Levi. -/
def faceCuspidal (n : ℕ) : Submodule ℂ (groupCohomology.H1 (faceRadH1 N h n)) :=
  cuspidalSubspace (CongruenceSubgroup.Gamma N) (faceRadH1 N h n)

/-- The isomorphism of Levi modules `H¹(N_P, E) ≅ H¹(N_{P'}, E)` induced by the conjugation. -/
def faceModIso (n : ℕ) : splitRadicalH1Representation (gammaNSplitting N) (gammaNRep N n) ≅
    faceRadH1 N h n :=
  FaceTransport.modIso (faceEquiv N h) (gammaNSplitting N) (gammaNRep N n) (faceRep N h n)
    (faceT h n) (faceT_intertwines N h n)

/-- The conjugation carries `𝒞_P(E)` onto `𝒞_{P'}(E)`. -/
theorem map_gammaNCuspidal_eq_faceCuspidal (n : ℕ) :
    Submodule.map (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
      (faceModIso N h n).hom 1).hom (gammaNCuspidal N n) = faceCuspidal N h n :=
  FaceTransport.cuspidal_map_eq (faceModIso N h n)

/-- The Hochschild--Serre edge of the conjugate plane group. -/
abbrev faceEdge (n : ℕ) := splitCohomologyEdge (faceSplitting N h) (faceRep N h n)

theorem faceEdge_kerMap (n : ℕ)
    (x : (twoCohomologyRestriction (gammaNExt N).inl (gammaNRep N n)).ker) :
    faceEdge N h n (faceKerMap N h n x) =
      (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N)) (faceModIso N h n).hom 1).hom
        (splitCohomologyEdge (gammaNSplitting N) (gammaNRep N n) x) :=
  FaceTransport.edge_kerMap (faceEquiv N h) (gammaNSplitting N) (gammaNRep N n) (faceRep N h n)
    (faceT h n) (faceT_intertwines N h n) x

/-- The Hochschild--Serre edge of the conjugate plane group is injective on the radical-kernel
classes (the paper's injection of the mixed cuspidal group into degree-two face cohomology). -/
theorem faceEdge_injective (n : ℕ) : Function.Injective (faceEdge N h n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (faceSplitting N h) (faceRep N h n)
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)

/-- The class of the holomorphic seed at the plane cusp `h⁻¹ P h`: the pullback `h^* [ω_f]` of the
seed class of `f ∈ S_{n+3}(Γ₂(N))` at `P` (the paper's "rationally conjugate the other plane
cusps to `P`"). -/
def faceSeedKerClass (n : ℕ)
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker :=
  faceKerMap N h n (gammaNSeedKerClass N n f)

/-- The class of the antiholomorphic seed at the plane cusp `h⁻¹ P h`. -/
def faceSeedConjKerClass (n : ℕ)
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker :=
  faceKerMap N h n (gammaNSeedConjKerClass N n f)

/-- The span of the holomorphic and antiholomorphic seeds at the plane cusp `h⁻¹ P h`. -/
def faceSeedKerSpan (n : ℕ) :
    Submodule ℂ (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)).ker :=
  Submodule.span ℂ
    (Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        faceSeedKerClass N h n f) ∪
      Set.range (fun f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ) =>
        faceSeedConjKerClass N h n f))

theorem faceSeedKerSpan_eq_map (n : ℕ) :
    faceSeedKerSpan N h n = Submodule.map (faceKerMap N h n) (gammaNSeedKerSpan N n) := by
  rw [gammaNSeedKerSpan, Submodule.map_span, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- The seeds at every plane cusp have edges in the mixed cuspidal group (unconditional). -/
theorem faceSeed_map_edge_le_cuspidal (n : ℕ) :
    Submodule.map (faceEdge N h n) (faceSeedKerSpan N h n) ≤ faceCuspidal N h n := by
  rw [faceSeedKerSpan_eq_map, ← map_gammaNCuspidal_eq_faceCuspidal]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨_, gammaNSeedKerSpan_map_edge_le_cuspidal N n ⟨x, hx, rfl⟩, ?_⟩
  exact (faceEdge_kerMap N h n x).symm

/-- **Lemma C.3, last sentence, at the plane cusp `h⁻¹ P h` (conditional on `ESSpan (Γ(N))`).** The images under the Hochschild--Serre edge of the conjugated holomorphic and
antiholomorphic seeds span exactly the mixed cuspidal group `𝒞_{P'}(E)` of the cusp. -/
theorem faceSeed_map_edge_eq_cuspidal (n : ℕ)
    (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    Submodule.map (faceEdge N h n) (faceSeedKerSpan N h n) = faceCuspidal N h n := by
  apply le_antisymm (faceSeed_map_edge_le_cuspidal N h n)
  intro y hy
  rw [← map_gammaNCuspidal_eq_faceCuspidal,
    ← gammaNSeedKerSpan_map_edge_eq_cuspidal N n hES] at hy
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  refine ⟨faceKerMap N h n x, ?_, faceEdge_kerMap N h n x⟩
  rw [faceSeedKerSpan_eq_map]
  exact ⟨x, hx, rfl⟩

theorem faceSeedKerSpan_eq_comap (n : ℕ)
    (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    faceSeedKerSpan N h n = Submodule.comap (faceEdge N h n) (faceCuspidal N h n) := by
  apply le_antisymm
  · intro x hx
    exact faceSeed_map_edge_le_cuspidal N h n ⟨x, hx, rfl⟩
  · intro x hx
    have hx' : faceEdge N h n x ∈ Submodule.map (faceEdge N h n) (faceSeedKerSpan N h n) := by
      rw [faceSeed_map_edge_eq_cuspidal N h n hES]; exact hx
    obtain ⟨x', hx', hxx⟩ := hx'
    rwa [← faceEdge_injective N h n hxx]

/-- The image of `𝒞_{P'}(E)` in `H²(Γ_{P'}, E)` under the inverse of the Hochschild--Serre edge:
the classes with zero restriction to the radical `N_{P'}` whose mixed class lies in `𝒞_{P'}(E)`. -/
def faceCuspidalInH2 (n : ℕ) : Submodule ℂ (groupCohomology.H2 (faceRep N h n)) :=
  Submodule.map (LinearMap.ker (twoCohomologyRestriction (faceExt N h).inl
    (faceRep N h n))).subtype (Submodule.comap (faceEdge N h n) (faceCuspidal N h n))

/-- The span, in `H²(Γ_{P'}, E)`, of the classes of the conjugated holomorphic and antiholomorphic
seeds at the plane cusp `P' = h⁻¹ P h`. -/
def faceSeedSpan (n : ℕ) : Submodule ℂ (groupCohomology.H2 (faceRep N h n)) :=
  Submodule.map (LinearMap.ker (twoCohomologyRestriction (faceExt N h).inl
    (faceRep N h n))).subtype (faceSeedKerSpan N h n)

/-- **Lemma C.3, last sentence, at the plane cusp `P' = h⁻¹ P h`, in degree-two cohomology
(conditional on `ESSpan (Γ(N))`).** For `N ≥ 3` the span of the classes of the conjugated seeds in
`H²(Γ_{P'}, E)` is the image of the mixed cuspidal group `𝒞_{P'}(E)`. -/
theorem faceSeedSpan_eq_cuspidalInH2 (n : ℕ)
    (hES : ESSpan (CongruenceSubgroup.Gamma N) n) :
    faceSeedSpan N h n = faceCuspidalInH2 N h n := by
  unfold faceSeedSpan faceCuspidalInH2
  rw [faceSeedKerSpan_eq_comap N h n hES]

end FaceData

section AllCusps

variable (N : ℕ) [NeZero N]

/-- **Every rational plane cusp is covered.** For `N ≥ 3` and every rational plane
`g P g⁻¹`, `g ∈ GL₃(ℚ)`, there is an integral change of basis `h ∈ SL₃(ℤ)` such that the stabilizer
of the plane in `Γ(N)` is the plane group `Γ_{h⁻¹Ph}` (`gammaNPAt N h`), and for every `n` and
cusp-form seeds the conjugated seeds span the mixed cuspidal group of that plane (conditional on
`ESSpan (Γ(N)) n`). -/
theorem exists_face_of_rational_plane (hN : 3 ≤ N) (g : GL (Fin 3) ℚ) :
    ∃ h : SL(3, ℤ),
      (∀ p ∈ gammaN N,
        InPQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ gammaNPAt N h) ∧
      ∀ n : ℕ, ESSpan (CongruenceSubgroup.Gamma N) n →
        Submodule.map (faceEdge N h n) (faceSeedKerSpan N h n) = faceCuspidal N h n := by
  obtain ⟨h, -, hiff⟩ := rational_cusp_stabilizer g
  refine ⟨h, fun p hp => ?_, fun n hES => faceSeed_map_edge_eq_cuspidal N h n hES⟩
  rw [hiff p, cast_conj, inPQ_cast_iff]
  rw [← mem_stabRow_ofSL_iff_rational hN h hp, mem_stabRow_ofSL]
  have hq : h * p * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem p hp h
    simpa [mul_assoc] using this
  exact ⟨fun hs => ⟨hq, hs⟩, fun hs => hs.2⟩

end AllCusps


end TernaryPeriodPolynomials.Argument.SeedC3S4c
