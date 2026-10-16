module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPlane2
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine4

@[expose] public section


/-!
# The value of `λ_{o.out}` on the transport of a plane class

Formalized by Claude Sonnet 5.5.

The plane version of `BLine3`/`BLine4`.  For a plane orbit `b` the matrix homomorphism `tau ∘ (s ↦ h s h⁻¹)` of the stabilizer of `b.out` has line type; `planeClass b φ` is the class of its cup cocycle.
`planeTransport_lam`: `λ_{o.out}` of the transport of `planeClass` to a flag group over `b` is `-432 φ(posPar (qVec (tau (qOfP o γ))))`.
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix CategoryTheory MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPeriodPolynomials.Argument.FlagH3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (planeBorel)

/-- The line-type matrix homomorphism of the stabilizer of the representative of a plane orbit. -/
def planeM (b : labelOrbits Γ6 Plane) : ↥(MulAction.stabilizer Γ6 b.out) →* SL(3, ℤ) :=
  tau.comp (conjIota (MulAction.stabilizer Γ6 b.out) (hOfP b))

theorem planeM_lineType (b : labelOrbits Γ6 Plane) : LineType (planeM b) :=
  lineType_tau (stab_planeType (hOfP b) b.out (planeOf_hOfP b))

theorem planeM_gammaN (b : labelOrbits Γ6 Plane) (s : ↥(MulAction.stabilizer Γ6 b.out)) : planeM b s ∈ gammaN 6 :=
  tau_mem_gammaN (stab_gammaN_P (hOfP b) b.out (planeOf_hOfP b) s)

/-- The additive function `s ↦ φ(block of tau(h s h⁻¹))` on the stabilizer of the representative of a plane orbit. -/
def planeU (b : labelOrbits Γ6 Plane) (φ : Gamma 6 → ℚ) (s : ↥(MulAction.stabilizer Γ6 b.out)) : ℚ :=
  φ (gammaOfM (planeM b) (planeM_lineType b) (planeM_gammaN b) s)

/-- The cup cocycle of the plane stabilizer of `b`. -/
def planeCochain (b : labelOrbits Γ6 Plane) (φ : Gamma 6 → ℚ) : (Fin 3 → ↥(MulAction.stabilizer Γ6 b.out)) → ℚ :=
  cupCochain (planeM b) (planeM_lineType b) (planeU b φ)

theorem planeCochain_cocycle (b : labelOrbits Γ6 Plane) (φ : Gamma 6 → ℚ) (hφ : ∀ x y, φ (x * y) = φ x + φ y) :
    dThree (planeCochain b φ) = 0 :=
  cupCochain_cocycle _ _ _ (fun s t => by simp only [planeU, gammaOfM_mul, hφ])

/-- **The class in `H³(Stab b.out; ℚ)` attached to an additive function on `Γ(6)`** (planes). -/
def planeClass (b : labelOrbits Γ6 Plane) (φ : Gamma 6 → ℚ) (hφ : ∀ x y, φ (x * y) = φ x + φ y) :
    groupCohomology (Rep.res (MulAction.stabilizer Γ6 b.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 :=
  clsRes _ (planeCochain b φ) (planeCochain_cocycle b φ hφ)

theorem planeTransport_lam (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagPlaneOrbit o).out = flagPlaneOf o.out)
    (φ : Gamma 6 → ℚ) (hφ : ∀ x y, φ (x * y) = φ x + φ y) :
    flagLam o.out ((planeTransportAt o γ hγ).hom (planeClass (flagPlaneOrbit o) φ hφ)) =
      -432 * φ (posParSL (qVec (tau (qOfP o γ)))) := by
  set a := flagPlaneOrbit o with ha
  set f := conjStabHom γ a.out (MulAction.stabilizer Γ6 o.out) (stab_fixes_plane_of o γ hγ) with hf
  set Ma := planeM a with hMa
  have hMaL : LineType Ma := planeM_lineType a
  have hMhL : LineType (Ma.comp f) := fun s => hMaL (f s)
  have hMhN : ∀ s, (Ma.comp f) s ∈ gammaN 6 := fun s => planeM_gammaN a (f s)
  obtain ⟨q, hq⟩ : ∃ q, q = tau (qOfP o γ) := ⟨_, rfl⟩
  have hqL : q ∈ lineBorel := hq ▸ tau_mem_lineBorel_of_planeBorel (qOfP_mem o γ hγ)
  obtain ⟨g, hg⟩ : ∃ g, g = gOf o := ⟨_, rfl⟩
  have hgF : flagOf g = o.out := hg ▸ flagOf_gOf o
  have hMg : LineType (tau.comp (conjIota (MulAction.stabilizer Γ6 o.out) g)) := tauFrame_lineType o.out g hgF
  have hMh : ∀ s, (Ma.comp f) s = tau (conjIota (MulAction.stabilizer Γ6 o.out) (hFrameP o γ) s) := fun s => by
    have := DFunLike.congr_fun (conjHom_compP o γ hγ) s
    simp only [hMa, planeM, MonoidHom.comp_apply] at this ⊢
    rw [this]
  have hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * ((Ma.comp f) s : Matrix (Fin 3) (Fin 3) ℤ) =
      (tau (conjIota (MulAction.stabilizer Γ6 o.out) g s) : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) := by
    intro s
    rw [hMh s]
    have : q * tau (conjIota (MulAction.stabilizer Γ6 o.out) (hFrameP o γ) s) = tau (conjIota (MulAction.stabilizer Γ6 o.out) g s) * q := by
      rw [hq, ← map_mul, ← map_mul]
      congr 1
      simp only [conjIota_apply, hg, qOfP]
      group
    exact congrArg (fun x : SL(3, ℤ) => (x : Matrix (Fin 3) (Fin 3) ℤ)) this
  have hrel' : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * ((Ma.comp f) s : Matrix (Fin 3) (Fin 3) ℤ) =
      ((tau.comp (conjIota (MulAction.stabilizer Γ6 o.out) g)) s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) := hrel
  obtain ⟨-, -, -, hA, -⟩ := frame_relation (tau.comp (conjIota (MulAction.stabilizer Γ6 o.out) g)) (Ma.comp f) hMg hMhL q hqL hrel'
  set c : ℚ := φ (PK q hqL 1) / 6 with hc
  have hu : ∀ s, planeU a φ (f s) = c * ((-((conjIota (MulAction.stabilizer Γ6 o.out) g s : Matrix (Fin 3) (Fin 3) ℤ) 0 1) : ℤ) : ℚ) := by
    intro s
    obtain ⟨-, -, -, -, -, -, d01⟩ := frame_entries_all o.out g hgF s
    obtain ⟨k, hk⟩ := d01
    have hk' : ((conjIota (MulAction.stabilizer Γ6 o.out) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 1 = 6 * k := hk
    have hG : gammaOfM (Ma.comp f) hMhL hMhN s = PK q hqL (-k) := by
      apply Subtype.ext
      apply Subtype.ext
      show (matLineData (Ma.comp f) hMhL).A s = PKmat q (-k)
      rw [hA s, PKmat, tauFrame_A o.out g hgF s, hk']
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have : planeU a φ (f s) = φ (gammaOfM (Ma.comp f) hMhL hMhN s) := rfl
    rw [this, hG, phi_PK φ hφ q hqL (-k), hk', hc]
    push_cast
    ring
  have hfun : (fun x : Fin 3 → ↥(MulAction.stabilizer Γ6 o.out) => planeCochain a φ (f ∘ x)) =
      cupCochain (Ma.comp f) hMhL (fun s => planeU a φ (f s)) := rfl
  rw [planeClass, planeTransportAt_cls o γ hγ, clsRes_congr _ hfun (dThree_comp _ _ (planeCochain_cocycle a φ hφ))
    (cupCochain_cocycle _ _ _ (fun s t => by simp only [map_mul, planeU, gammaOfM_mul, hφ]))]
  rw [flagLam_cup_value_tau o.out g hgF (Ma.comp f) hMhL q hqL hrel c (fun s => planeU a φ (f s)) hu]
  subst hq
  rw [phi_posPar φ hφ _ hqL, hc]
  ring

end TernaryPeriodPolynomials.Argument.GammaNStokes
