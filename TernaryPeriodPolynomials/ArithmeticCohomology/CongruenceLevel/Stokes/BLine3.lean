module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine2

@[expose] public section


/-!
# The value of `λ` on the transport of a line cup class

Formalized by Claude Sonnet 5.5.

For a homomorphism `M` of line type landing in `Γ(6)`, `gammaOfM M` is its lower right block as an element of `Γ(6) ⊂ SL₂(ℤ)`; for an additive `φ` on `Γ(6)`, `u = φ ∘ gammaOfM` is an additive function and
`cupCochain M · u` is a `3`-cocycle.  For a line orbit `a`, `lineClass a φ` is the class in `H³(Stab a.out; ℚ)` of the cup cocycle of the frame `hOf a`.
`lineTransport_lam`: the evaluation functional `λ_{o.out}` takes on the transport of `lineClass a φ` to the flag group of `o` over `a` the value `-432 φ(posPar (qVec (qOf o γ)))`.
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
open TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg (flagGroup flag_entries)

theorem lineBorel_of_lineType {K : Type} [Group K] {M : K →* SL(3, ℤ)} (hM : LineType M) (s : K) : M s ∈ lineBorel :=
  ⟨(hM s).1, (hM s).2.1⟩

/-- The lower right block of a homomorphism of line type landing in `Γ(6)`, as an element of `Γ(6)`. -/
def gammaOfM {K : Type} [Group K] (M : K →* SL(3, ℤ)) (hM : LineType M) (hN : ∀ s, M s ∈ gammaN 6) (s : K) : Gamma 6 :=
  ⟨blockSL (M s) (lineBorel_of_lineType hM s) (hN s), blockSL_mem _ _ _⟩

theorem gammaOfM_mul {K : Type} [Group K] (M : K →* SL(3, ℤ)) (hM : LineType M) (hN : ∀ s, M s ∈ gammaN 6) (s t : K) :
    gammaOfM M hM hN (s * t) = gammaOfM M hM hN s * gammaOfM M hM hN t := by
  apply Subtype.ext
  apply Subtype.ext
  show blockQ (M (s * t)) = blockQ (M s) * blockQ (M t)
  rw [map_mul]
  exact blockQ_mul _ _ (lineBorel_of_lineType hM s)

theorem gammaOfM_val {K : Type} [Group K] (M : K →* SL(3, ℤ)) (hM : LineType M) (hN : ∀ s, M s ∈ gammaN 6) (s : K) :
    (((gammaOfM M hM hN s : Gamma 6) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (matLineData M hM).A s := rfl

/-- The entries of the frame matrix of a flag stabilizer: unipotent, with the three coordinates divisible by `6`. -/
theorem frame_entries (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (s : ↥(MulAction.stabilizer Γ6 F)) :
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 0 = 1 ∧
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 1 = 1 ∧
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 ∧
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 0 = 0 ∧
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    (6 : ℤ) ∣ ((conjIota (MulAction.stabilizer Γ6 F) g s : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 2 := by
  have hmem := frameMat_mem F g hg s
  obtain ⟨e00, e11, e22, -, d12, -⟩ := flag_entries (by norm_num : 3 ≤ 6) hmem
  obtain ⟨-, e10, e20, e21⟩ := hmem
  exact ⟨e00, e11, e22, e10, e20, e21, by exact_mod_cast d12⟩

theorem clsRes_congr (S : Subgroup Γ6) {T1 T2 : (Fin 3 → S) → ℚ} (h : T1 = T2) (hT1 : dThree T1 = 0) (hT2 : dThree T2 = 0) :
    clsRes S T1 hT1 = clsRes S T2 hT2 := by
  subst h; rfl

section Value

variable (a : labelOrbits Γ6 Line) (φ : Gamma 6 → ℚ)

/-- The additive function `s ↦ φ(block of h s h⁻¹)` on the stabilizer of the representative of a line orbit. -/
def lineU (a : labelOrbits Γ6 Line) (φ : Gamma 6 → ℚ) (s : ↥(MulAction.stabilizer Γ6 a.out)) : ℚ :=
  φ (gammaOfM (conjIota (MulAction.stabilizer Γ6 a.out) (hOf a)) (stab_lineType (hOf a) a.out (lineOf_hOf a))
    (stab_gammaN (hOf a) a.out (lineOf_hOf a)) s)

/-- The cup cocycle of the line stabilizer of `a`. -/
def lineCochain (a : labelOrbits Γ6 Line) (φ : Gamma 6 → ℚ) : (Fin 3 → ↥(MulAction.stabilizer Γ6 a.out)) → ℚ :=
  cupCochain (conjIota (MulAction.stabilizer Γ6 a.out) (hOf a)) (stab_lineType (hOf a) a.out (lineOf_hOf a)) (lineU a φ)

theorem lineCochain_cocycle (hφ : ∀ x y, φ (x * y) = φ x + φ y) : dThree (lineCochain a φ) = 0 :=
  cupCochain_cocycle _ _ _ (fun s t => by simp only [lineU, gammaOfM_mul, hφ])

/-- **The class in `H³(Stab a.out; ℚ)` attached to an additive function on `Γ(6)`.** -/
def lineClass (hφ : ∀ x y, φ (x * y) = φ x + φ y) : groupCohomology (Rep.res (MulAction.stabilizer Γ6 a.out).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 :=
  clsRes _ (lineCochain a φ) (lineCochain_cocycle a φ hφ)

end Value

end TernaryPeriodPolynomials.Argument.GammaNStokes
