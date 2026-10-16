module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.LineClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedCusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedConj

@[expose] public section


/-!
# The class of the line seed of a cusp form, and the antiholomorphic seed (LS9)

Line mirror of `SeedC3.SeedCusp` and `SeedC3.SeedConj`.  For a cusp form `f` of weight `n + 3` for a determinant-one group `Λ ⊂ GL₂(ℝ)` and a line parabolic group
`D : LineData G` whose Levi block lands in `Λ`: the datum, the closed equivariant form, the class and the closed-form cocycle of the seed `σ_h`, `h = f ∘ ofComplex`
(for the moment primitives `momentPrim` of `h(z) z^j` normalized by `G_j(i) = 0`), and the same for the antiholomorphic seed `conj σ_h` (twist by `conjCLM`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane
open CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothSingularComparison ZigZag

namespace LineData

variable {G : Type} [Group G] (D : LineData G)

theorem conjCoef_rhoCoef (n : ℕ) (g : G) (q : Coef n) :
    D.rhoCoef n g (Coef.conjCoef q) = Coef.conjCoef (D.rhoCoef n g q) := by
  apply Coef.toPoly_injective
  rw [D.toPoly_rhoCoef, Coef.toPoly_conjCoef, Coef.toPoly_conjCoef, D.toPoly_rhoCoef, map_conj_rho]

theorem conjCLM_comm (n : ℕ) (g : G) :
    (conjCLM n).comp (repCLM (D.rhoR n) g) = (repCLM (D.rhoR n) g).comp (conjCLM n) := by
  ext q
  simp only [ContinuousLinearMap.comp_apply]
  exact (D.conjCoef_rhoCoef n g q).symm

end LineData

section Cusp

variable (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] (n : ℕ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ))
variable {Λ n f}
variable {G : Type} [Group G] (D : LineData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

include hΛ in
theorem cuspH_mod_line (g : G) (z : ℂ) (hz : 0 < z.im) :
    cuspH Λ n f (mob (D.lam g) z) = dnm (D.lam g) z ^ (n + 3) * cuspH Λ n f z :=
  modular_of_slashInvariant Λ (n + 3) f (D.lam g) (hΛ g) z hz

/-- **The zig-zag datum of the line seed of a cusp form.** -/
def cuspSeedDatum :=
  D.seedDatum (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod_line D hΛ)

/-- The line seed `σ_h` of a cusp form, as a closed `ρ`-equivariant 2-form on the line face. -/
def cuspSeedInv :=
  D.seedInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod_line D hΛ)

/-- **The class of the line seed of a cusp form** in `H²(G, E_n)`. -/
def cuspSeedClass : H2 (Rep.of (D.rhoR n)) :=
  D.seedClass (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod_line D hΛ)

theorem deRhamClass_cuspSeed :
    deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (cuspSeedInv D hΛ (f := f)) = cuspSeedClass D hΛ (f := f) :=
  D.deRhamClass_seedInv (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (cuspH_mod_line D hΛ)

/-- The zig-zag cochain of the line seed of a cusp form. -/
def cuspSeedCochain (g k : G) : Coef n :=
  cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (cuspSeedDatum D hΛ (f := f)) g k

theorem cuspSeedCochain_cocycle (g h j : G) :
    cuspSeedCochain D hΛ (f := f) (g * h) j + cuspSeedCochain D hΛ (f := f) g h =
      D.rhoR n g (cuspSeedCochain D hΛ (f := f) h j) + cuspSeedCochain D hΛ (f := f) g (h * j) :=
  cochain_isCocycle _ _ g h j

/-- **The closed-form cocycle of the line seed of a cusp form.** -/
theorem toPoly_cuspSeedCochain (g k : G) :
    Coef.toPoly (cuspSeedCochain D hΛ (f := f) g k) =
      ∑ j ∈ Finset.range (n + 1),
        C ((n.choose j : ℂ) * (-1) ^ (n - j) *
            ((D.v g 0 : ℂ) * momentPrim Λ n f (j + 1) (mob (D.lam k) Complex.I) +
              (D.v g 1 : ℂ) * momentPrim Λ n f j (mob (D.lam k) Complex.I))) *
          rho (D.lmat g) (X 2 ^ j * X 1 ^ (n - j)) :=
  D.toPoly_cochain (cuspH Λ n f) n (momentPrim Λ n f) (cuspH_holo Λ n f)
    (momentPrim_hasDerivAt Λ n f) (momentPrim_zero Λ n f) (cuspH_mod_line D hΛ) g k

/-! ### The antiholomorphic seed -/

/-- **The zig-zag datum of the antiholomorphic line seed** `conj σ_h`. -/
def cuspSeedConjDatum :=
  (cuspSeedDatum D hΛ (f := f)).twist isOpen_faceSet D.action (D.rhoR n) (conjCLM n)
    (fun g => D.conjCLM_comm n g)

/-- The antiholomorphic line seed as a closed equivariant 2-form. -/
def cuspSeedConjInv : invClosed isOpen_faceSet D.action (D.rhoR n) :=
  ⟨twForm (conjCLM n) 2 (cuspSeedInv D hΛ (f := f)).1, by
    rw [d_twForm, (cuspSeedInv D hΛ (f := f)).2.1, map_zero], fun g => by
    rw [pullForm_twForm, (cuspSeedInv D hΛ (f := f)).2.2 g, ← twForm_mul, ← twForm_mul,
      D.conjCLM_comm n g]⟩

/-- **The class of the antiholomorphic line seed** in `H²(G, E_n)`. -/
def cuspSeedConjClass : H2 (Rep.of (D.rhoR n)) :=
  zigzagClass (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (cuspSeedConjDatum D hΛ (f := f))

theorem deRhamClass_cuspSeedConj :
    deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
      (cuspSeedConjInv D hΛ (f := f)) = cuspSeedConjClass D hΛ (f := f) :=
  deRhamClass_eq isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)
    (cuspSeedConjInv D hΛ (f := f)) (cuspSeedConjDatum D hΛ (f := f))

/-- The zig-zag cochain of the antiholomorphic line seed. -/
def cuspSeedConjCochain (g k : G) : Coef n :=
  cochain (laws isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n))
    (cuspSeedConjDatum D hΛ (f := f)) g k

/-- The cochain of the antiholomorphic seed is the coefficientwise conjugate. -/
theorem cuspSeedConjCochain_eq (g k : G) :
    cuspSeedConjCochain D hΛ (f := f) g k = Coef.conjCoef (cuspSeedCochain D hΛ (f := f) g k) :=
  twist_cochain isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n) (conjCLM n)
    (fun g => D.conjCLM_comm n g) (cuspSeedDatum D hΛ (f := f)) g k

theorem cuspSeedConjCochain_cocycle (g h j : G) :
    cuspSeedConjCochain D hΛ (f := f) (g * h) j + cuspSeedConjCochain D hΛ (f := f) g h =
      D.rhoR n g (cuspSeedConjCochain D hΛ (f := f) h j) + cuspSeedConjCochain D hΛ (f := f) g (h * j) :=
  cochain_isCocycle _ _ g h j

end Cusp

end TernaryPeriodPolynomials.Argument.LineSeed
