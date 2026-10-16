module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine3

@[expose] public section


/-!
# The value of `λ_{o.out}` on the transport of a line class

Formalized by Claude Sonnet 5.5.

`lineTransport_lam`: for a flag orbit `o`, `γ ∈ Γ(6)` carrying the representative of its line orbit to the line of `o.out`, and an additive `φ` on `Γ(6)`,
`λ_{o.out}` of the transport of `lineClass (flagLineOrbit o) φ` to the flag group is `-432 φ(posPar (qVec (qOf o γ)))`.
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

theorem lineTransport_lam (o : labelOrbits Γ6 Flag) (γ : Γ6) (hγ : γ • (flagLineOrbit o).out = flagLineOf o.out)
    (φ : Gamma 6 → ℚ) (hφ : ∀ x y, φ (x * y) = φ x + φ y) :
    flagLam o.out ((lineTransportAt o γ hγ).hom (lineClass (flagLineOrbit o) φ hφ)) =
      -432 * φ (posParSL (qVec (qOf o γ))) := by
  set a := flagLineOrbit o with ha
  set f := conjStabHom γ a.out (MulAction.stabilizer Γ6 o.out) (stab_fixes_line_of o γ hγ) with hf
  set Ma := conjIota (MulAction.stabilizer Γ6 a.out) (hOf a) with hMa
  have hMaL : LineType Ma := stab_lineType (hOf a) a.out (lineOf_hOf a)
  have hMaN : ∀ s, Ma s ∈ gammaN 6 := stab_gammaN (hOf a) a.out (lineOf_hOf a)
  have hMhL : LineType (Ma.comp f) := fun s => hMaL (f s)
  have hMhN : ∀ s, (Ma.comp f) s ∈ gammaN 6 := fun s => hMaN (f s)
  obtain ⟨q, hq⟩ : ∃ q, q = qOf o γ := ⟨_, rfl⟩
  have hqL : q ∈ lineBorel := hq ▸ qOf_mem o γ hγ
  obtain ⟨g, hg⟩ : ∃ g, g = gOf o := ⟨_, rfl⟩
  have hgF : flagOf g = o.out := hg ▸ flagOf_gOf o
  -- the frame relation
  have hMg : LineType (conjIota (MulAction.stabilizer Γ6 o.out) g) := fun s => by
    obtain ⟨e00, -, -, e10, e20, -⟩ := frame_entries o.out g hgF s
    exact ⟨e10, e20, e00⟩
  have hMh : ∀ s, (Ma.comp f) s = conjIota (MulAction.stabilizer Γ6 o.out) (hFrame o γ) s := fun s => DFunLike.congr_fun (conjHom_comp o γ hγ) s
  have hrel : ∀ s, (q : Matrix (Fin 3) (Fin 3) ℤ) * ((Ma.comp f) s : Matrix (Fin 3) (Fin 3) ℤ) =
      (conjIota (MulAction.stabilizer Γ6 o.out) g s : Matrix (Fin 3) (Fin 3) ℤ) * (q : Matrix (Fin 3) (Fin 3) ℤ) := by
    intro s
    rw [hMh s]
    have : q * conjIota (MulAction.stabilizer Γ6 o.out) (hFrame o γ) s = conjIota (MulAction.stabilizer Γ6 o.out) g s * q := by
      simp only [conjIota_apply, hq, hg, qOf]
      group
    exact congrArg (fun x : SL(3, ℤ) => (x : Matrix (Fin 3) (Fin 3) ℤ)) this
  obtain ⟨-, -, -, hA, -⟩ := frame_relation (conjIota (MulAction.stabilizer Γ6 o.out) g) (Ma.comp f) hMg hMhL q hqL hrel
  set c : ℚ := φ (PK q hqL 1) / 6 with hc
  have hu : ∀ s, lineU a φ (f s) = c * ((conjIota (MulAction.stabilizer Γ6 o.out) g s : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℤ) := by
    intro s
    obtain ⟨e00, e11, e22, e10, e20, e21, d12⟩ := frame_entries o.out g hgF s
    obtain ⟨k, hk⟩ := d12
    have hG : gammaOfM (Ma.comp f) hMhL hMhN s = PK q hqL k := by
      apply Subtype.ext
      apply Subtype.ext
      show (matLineData (Ma.comp f) hMhL).A s = PKmat q k
      rw [hA s, PKmat]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp [matLineData, e11, e22, e21, hk]
    have : lineU a φ (f s) = φ (gammaOfM (Ma.comp f) hMhL hMhN s) := rfl
    rw [this, hG, phi_PK φ hφ q hqL k, hk, hc]
    push_cast
    ring
  have hfun : (fun x : Fin 3 → (MulAction.stabilizer Γ6 o.out) => lineCochain a φ (f ∘ x)) = cupCochain (Ma.comp f) hMhL (fun s => lineU a φ (f s)) := rfl
  rw [lineClass, lineTransportAt_cls o γ hγ, clsRes_congr (MulAction.stabilizer Γ6 o.out) hfun (dThree_comp _ _ (lineCochain_cocycle a φ hφ))
    (cupCochain_cocycle _ _ _ (fun s t => by simp only [map_mul, lineU, gammaOfM_mul, hφ]))]
  rw [flagLam_cup_value o.out g hgF (Ma.comp f) hMhL q hqL hrel c (fun s => lineU a φ (f s)) hu]
  subst hq
  rw [phi_posPar φ hφ _ hqL, hc]
  ring

end TernaryPeriodPolynomials.Argument.GammaNStokes
