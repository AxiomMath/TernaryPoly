module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFacePairing

@[expose] public section


/-!
# The literal contragredient is the contragredient of the Levi module; conjugate plane cusps in binary coordinates

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, and Lemma C.3 (`ar:lem:seed`).

* `dualEquivOfPerfect`, `dualIsoOfPerfect`, `isoOfTwoPerfect`, `PerfectInv.comp_iso`: a finite-dimensional module and its perfect invariant
  partner are contragredient to each other; two partners of one module are isomorphic.
* `leviDualIso`: `H¹(N_R, E^*) ≅ H¹(N_R, E)^∨` as `Γ(N)`-modules (through the Levi-invariant Koszul pairing `radPairingOf`).  Hence
  `QDiLitEquiv`: the cuspidal group of the Levi module of the literal contragredient (`QDiLit`) is linearly isomorphic to the cuspidal
  group of the contragredient of the Levi module (`QDiDual` of `C5Wiring`), for every line face (`lineFaceLitCuspEquiv`) and plane face
  (`planeFaceLitCuspEquiv`).
* `faceBinaryIso`: every conjugate plane cusp has `H¹(N_{P'}, E_n) ≅ Sym^{n+1} ⊗ det⁻¹` as `Γ(N)`-modules; `planeFaceLitBinaryIso`:
  `H¹(N_{P'}, E_n^*) ≅ Sym^{n+1}` (for `Γ(N) ≤ SL₂(ℤ)` the determinant twist is invisible).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup
open scoped Classical MatrixGroups DirectSum

section DualIso

variable {G : Type} [Group G] {V W : Rep ℂ G} [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
  {e : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **A perfect invariant pairing identifies the second module with the contragredient of the first.** -/
def dualEquivOfPerfect (hp : PerfectInv e) : W.ρ.Equiv (dualRepG V).ρ := by
  have hinj : Function.Injective e.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hp.right w (fun v => by simpa using congrArg (fun f => f v) hw)
  have hinj' : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hp.left v (fun w => by simpa using congrArg (fun f => f w) hv)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj'
  rw [Subspace.dual_finrank_eq] at h1 h2
  have heq : Module.finrank ℂ W = Module.finrank ℂ (Module.Dual ℂ V) := by
    rw [Subspace.dual_finrank_eq]; exact le_antisymm h1 h2
  have hbij : Function.Bijective e.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj⟩
  exact Representation.Equiv.mk (LinearEquiv.ofBijective e.flip hbij) (fun g => by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change e v (W.ρ g w) = (dualRepG V).ρ g (e.flip w) v
    rw [dualRepG_inv]
    have h2 : W.ρ g⁻¹ (W.ρ g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have := hp.inv g⁻¹ v (W.ρ g w)
    rw [h2] at this
    exact this.symm)

/-- The isomorphism of representations furnished by `dualEquivOfPerfect`. -/
def dualIsoOfPerfect (hp : PerfectInv e) : W ≅ dualRepG V := Rep.mkIso (dualEquivOfPerfect hp)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- A perfect invariant pairing transports along an isomorphism of the first module. -/
theorem PerfectInv.comp_iso {V' : Rep ℂ G} (hp : PerfectInv e) (ι : V' ≅ V) :
    PerfectInv (e ∘ₗ ι.hom.hom.toLinearMap) where
  inv g a b := by
    change e (ι.hom.hom (V'.ρ g a)) (W.ρ g b) = e (ι.hom.hom a) b
    rw [Rep.hom_comm_apply]
    exact hp.inv g _ _
  left a ha := by
    have h0 : ι.hom.hom a = 0 := hp.left _ (fun w => ha w)
    have : ι.inv.hom (ι.hom.hom a) = a := Rep.inv_hom_apply _ _ ι a
    rw [← this, h0]
    exact map_zero _
  right w hw := hp.right w (fun v => by
    have := hw (ι.inv.hom v)
    rwa [show (e ∘ₗ ι.hom.hom.toLinearMap) (ι.inv.hom v) = e v from by
      change e (ι.hom.hom (ι.inv.hom v)) = e v
      rw [Rep.hom_inv_apply]] at this)

/-- Two perfectly paired partners of one module are isomorphic. -/
def isoOfTwoPerfect {S : Rep ℂ G} [FiniteDimensional ℂ S] {e₂ : V →ₗ[ℂ] S →ₗ[ℂ] ℂ} (hp : PerfectInv e) (hp₂ : PerfectInv e₂) :
    W ≅ S :=
  dualIsoOfPerfect hp ≪≫ (dualIsoOfPerfect hp₂).symm

end DualIso

section Levi

variable {N : ℕ}

theorem leviPerfect {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    PerfectInv (V := splitRadicalH1Representation s rep) (W := splitRadicalH1Representation s (dualRepG rep))
      (radPairingOf (ext := ext) (perfectInv_dual rep)) := by
  have hp := perfectInv_dual rep
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  exact ⟨fun γ x y => radPairingOf_levi hp s γ (hdet γ) x y, fun x hx => radPairingOf_left hp x hx,
    fun y hy => radPairingOf_right hp y hy⟩

/-- **The Levi module of the literal contragredient is the contragredient of the Levi module**:
`H¹(N_R, E^*) ≅ H¹(N_R, E)^∨` as `Γ(N)`-modules, through the Levi-invariant Koszul pairing. -/
def leviDualIso {E : Type} [Group E] {ext : GroupExtension RadicalLattice E (Gamma N)}
    (s : ext.Splitting) (hdet : ∀ A, radDet (splitRadicalInput s A) = 1) (rep : Rep ℂ E) [FiniteDimensional ℂ rep] :
    splitRadicalH1Representation s (dualRepG rep) ≅ dualRepG (splitRadicalH1Representation s rep) :=
  have : FiniteDimensional ℂ (splitRadicalH1Representation s rep) := finiteDimensional_H1 (Rep.res ext.inl rep)
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG rep)) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG rep))
  dualIsoOfPerfect (leviPerfect s hdet rep)

end Levi

section Faces

open TernaryPeriodPolynomials.Argument.SeedC3S4c (faceCuspidal faceRadH1 faceRep faceSplitting gammaNPAt faceModIso
  gammaNCoordinateIso)

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- **`H¹(N_{Q'}, E_n^*) ≅ H¹(N_{Q'}, E_n)^∨`** for the line cusp `Q' = h⁻¹ Q h`: the Levi module of the literal contragredient is the
contragredient of the Levi module. -/
def lineFaceLitIso : lineFaceRadH1Lit N n h ≅ dualRepG (lineFaceRadH1 N h n) :=
  leviDualIso (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineFaceRep N h n)

/-- **`H¹(N_{P'}, E_n^*) ≅ H¹(N_{P'}, E_n)^∨`** for the plane cusp `P' = h⁻¹ P h`. -/
def planeFaceLitIso : faceRadH1Lit N n h ≅ dualRepG (faceRadH1 N h n) :=
  leviDualIso (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n)

/-- The cuspidal group of the Levi module of the literal contragredient is the cuspidal group of the contragredient of the Levi module
(line faces). -/
def lineFaceLitCuspEquiv :
    cuspidalSubspace (Gamma N) (lineFaceRadH1Lit N n h) ≃ₗ[ℂ] cuspidalSubspace (Gamma N) (dualRepG (lineFaceRadH1 N h n)) :=
  cuspEquivOfIso (lineFaceLitIso N n h)

/-- The same for plane faces. -/
def planeFaceLitCuspEquiv :
    cuspidalSubspace (Gamma N) (faceRadH1Lit N n h) ≃ₗ[ℂ] cuspidalSubspace (Gamma N) (dualRepG (faceRadH1 N h n)) :=
  cuspEquivOfIso (planeFaceLitIso N n h)

/-- **`QDiLit` is the dual module `QDiDual` of the earlier wiring**: the cuspidal group of `H¹(N_{Q'_i}, E_n^*)` is linearly
isomorphic to that of the contragredient of `H¹(N_{Q'_i}, E_n)`. -/
def QDiLitEquiv (i : LineFaces N) : QDiLit N n i ≃ₗ[ℂ] QDiDual N n i :=
  lineFaceLitCuspEquiv N n i.rep

/-- **Every plane cusp in binary coordinates**: `H¹(N_{P'}, E_n) ≅ Sym^{n+1} ⊗ det⁻¹` as `Γ(N)`-modules for the conjugate plane cusp
`P' = h⁻¹ P h` (the conjugation `faceModIso` followed by the coordinate of Lemma C.3). -/
def faceBinaryIso : faceRadH1 N h n ≅ symRep N (n + 1) (-1) := (faceModIso N h n).symm ≪≫ gammaNCoordinateIso N n

/-- **Every plane cusp, literal contragredient, in binary coordinates**: `H¹(N_{P'}, E_n^*) ≅ Sym^{n+1}` as `Γ(N)`-modules
(`SL₂` kills the determinant twist). -/
def planeFaceLitBinaryIso : faceRadH1Lit N n h ≅ symRep N (n + 1) 0 :=
  have : FiniteDimensional ℂ (faceRadH1 N h n) := inferInstance
  have : FiniteDimensional ℂ (faceRadH1Lit N n h) :=
    finiteDimensional_H1 (Rep.res (TernaryPeriodPolynomials.Argument.SeedC3S4c.faceExt N h).inl (faceRepLit N n h))
  have hB := Classical.choose_spec (symRep_pairing (N := N) (n + 1) (-1) 0)
  isoOfTwoPerfect (V := faceRadH1 N h n)
    (leviPerfect (faceSplitting N h) (planeFaceRadicalInput_det N h) (faceRep N h n))
    (PerfectInv.comp_iso (V := symRep N (n + 1) (-1)) (W := symRep N (n + 1) 0)
      (e := Classical.choose (symRep_pairing (N := N) (n + 1) (-1) 0)) ⟨hB.1, hB.2.1, hB.2.2⟩ (faceBinaryIso N n h))

end Faces

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
