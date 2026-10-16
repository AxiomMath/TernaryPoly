module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagReduction

@[expose] public section


/-!
# L1/L2: the standard-cusp base case of the series restrictions

Formalized by Claude Sonnet 5.5.
Paper: Proposition C.4 and Lemma C.3.

* `cuspCosetEquiv`: at the standard cusp `ofSL 1` the cosets `Γ_P\Γ` of the plane series and of the cusp series are the same
  (`stabRow (ofSL 1).r = planeStab`).
* `planeEisensteinAt_one_eq`: on `Ω`, the holomorphic series at the cusp `ofSL 1` is `planeEisenstein` (coefficientwise).
* `toInv_congr`, **`eisensteinAtClass_gammaN_one`**: `eisensteinAtClass_gammaN N n f 1 false hn = eisensteinClass_gammaN N n f hn`.
* `faceH2Map`, **`resAtC_one_complexify`**: `resAtC N 1 n ∘ complexify = faceH2Map N 1 n ∘ complexifyG ∘ resP` (complex-level bridge
  `resP` to `resAtC` at `h = 1`; the real-level version for `resTo` is the `resTo_standard`).
* **`baseRestriction_eq_faceSeed`**, **`baseRestriction_in_seedSpan`** (`3 ≤ N`, `4 ≤ n`): the restriction of the standard-cusp
  holomorphic series to `h = 1` is exactly `faceSeedKerClass N 1 n f`.  One series at one cusp: NOT `SeriesRestrictionInSeedSpan`.
* **`rB_standard`** (`3 ≤ N`, `4 ≤ n`): `r_B` of the complexified literal class vanishes at every complete flag over the standard plane.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem ofSL_one_r : (CuspData.ofSL 1).r = ![0, 0, 1] := by
  rw [ofSL_r]; simp

theorem stabRow_ofSL_one : stabRow (CuspData.ofSL 1).r = planeStab := by
  rw [ofSL_one_r, ← planeStab_eq_stabRow]

/-- At the standard cusp the cosets of the two series are the same. -/
def cuspCosetEquiv (Γ : Subgroup SL(3, ℤ)) : PlaneCoset Γ ≃ CuspCoset Γ (CuspData.ofSL 1).r :=
  Quotient.congr (Equiv.refl Γ) (fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, stabRow_ofSL_one]
    rfl)

theorem cuspCosetEquiv_mk (Γ : Subgroup SL(3, ℤ)) (a : Γ) :
    cuspCosetEquiv Γ (Quotient.mk _ a) = Quotient.mk _ a := rfl


section Series

variable (N : ℕ) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem termFunK_one_eq {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ)
    (c : PlaneCoset (gammaN N)) :
    termFunK false (CuspData.ofSL 1) (gammaN N) n f (cuspCosetEquiv (gammaN N) c) i j m x =
      termFun (gammaN N) n f c i j m x := by
  induction c using Quotient.inductionOn with
  | h a =>
    rw [termFunK_eq_cosetTermK false (CuspData.ofSL 1) (gammaN N) (leviGroup N) n f
      (leviInCusp_gammaN N 1) hx i j m, cuspCosetEquiv_mk,
      termFun_eq_cosetTerm (gammaN N) (leviGroup N) n f (leviIn_gammaN N) hx i j m,
      cosetTermK_mk, cosetTerm_mk, summandK_false]
    simp [CuspData.ofSL, realMat_one]
    rfl

theorem seriesCoeffK_one_eq {x : Fin 5 → ℝ} (hx : x ∈ Omega) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    seriesCoeffK false (CuspData.ofSL 1) (gammaN N) n f i j m x =
      seriesCoeff (gammaN N) n f i j m x := by
  unfold seriesCoeffK seriesCoeff
  rw [← (cuspCosetEquiv (gammaN N)).tsum_eq]
  exact tsum_congr fun c => termFunK_one_eq N n f hx i j m c

/-- **The holomorphic series at the standard cusp `ofSL 1` is the plane Eisenstein series** (on `Ω`). -/
theorem planeEisensteinAt_one_eq {y : Fin 5 → ℝ} (hy : y ∈ Omega) (a c : Fin 5) :
    planeEisensteinAt false (CuspData.ofSL 1) (gammaN N) n f y a c =
      planeEisenstein (gammaN N) n f y a c := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  have h1 := coeff_planeEisensteinAt false (CuspData.ofSL 1) (gammaN N) n f y a c m
  have h2 := coeff_planeEisenstein (gammaN N) n f y a c m
  rw [h1, h2]
  have := seriesCoeffK_one_eq N n f hy a c m
  unfold seriesCoeffK seriesCoeff at this
  exact this

end Series

section Class

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

/-- Components agreeing on `Ω` give the same element of `invClosed`. -/
theorem toInv_congr {Γ : Subgroup SL(3, ℤ)} {n : ℕ} (W W' : InvComponents Γ n)
    (h : ∀ y ∈ Omega, ∀ a b, W.comp y a b = W'.comp y a b) : W.toInv = W'.toInv := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  have e1 := W.toInv_val
  have e2 := W'.toInv_val
  rw [e1, e2, W.form_apply hx, W'.form_apply hx]
  unfold InvComponents.raw
  congr 1
  funext a b
  exact h x hx a b

theorem eisensteinAtClass_gammaN_one (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    Statements.EisensteinClass.eisensteinAtClass_gammaN N n f 1 false hn =
      Statements.EisensteinClass.eisensteinClass_gammaN N n f hn := by
  have e : Statements.EisensteinClass.planeEisensteinAtInv false (CuspData.ofSL 1) (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N 1) =
      Statements.EisensteinClass.planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N) :=
    toInv_congr _ _ fun y hy a b => congrArg Coef.mk (planeEisensteinAt_one_eq N n f hy a b)
  exact congrArg (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty
    (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) e

end Class


section Bridge

open CategoryTheory groupCohomology

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- The pullback of degree-two cohomology along the conjugation `Γ_{h⁻¹Ph} ≃ Γ_P`, with the coefficient
transport `faceT h`; `faceKerMap` is its restriction to the radical kernels. -/
def faceH2Map : H2 (gammaNRep N n) →ₗ[ℂ] H2 (faceRep N h n) :=
  FaceTransport.h2Map (faceEquiv N h) (gammaNRep N n) (faceRep N h n) (faceT h n)
    (faceT_intertwines N h n)

theorem faceKerMap_val' (x) : (faceKerMap N h n x).1 = faceH2Map N h n x.1 := rfl

theorem resAtC_one_complexify (c : H2 (Rep.of (gammaRho (gammaN N) n))) :
    resAtC N 1 n (EisensteinClass.complexify (gammaN N) n c) = faceH2Map N 1 n (complexifyG N n (resP N n c)) := by
  induction c using H2_induction_on with
  | h z =>
    rw [EisensteinClass.complexify_H2π]
    unfold resAtC resP
    rw [H2π_comp_map_apply]
    unfold faceH2Map
    rw [H2π_comp_map_apply, complexifyG_H2π]
    refine Eq.trans ?_ (FaceTransport.h2Map_π (faceEquiv N 1) (gammaNRep N n) (faceRep N 1 n)
      (faceT 1 n) (faceT_intertwines N 1 n) _).symm
    congr 1
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have e : ∀ a : gammaNPAt N (1 : SL(3, ℤ)),
        inclP N ((faceEquiv N 1).toMulEquiv a) = inclAt N 1 a := fun a =>
      Subtype.ext (by simp [faceEquiv, FaceTransport.pullbackEquiv, conjP]; rfl)
    have e2 : ∀ v, faceT (1 : SL(3, ℤ)) n v = v := fun v => by
      rw [faceT_apply]; simp
    change z.1 (inclAt N 1 a, inclAt N 1 b) =
      faceT 1 n (z.1 (inclP N ((faceEquiv N 1).toMulEquiv a), inclP N ((faceEquiv N 1).toMulEquiv b)))
    rw [e, e]
    exact (e2 _).symm

end Bridge

section Base

open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass (constant_term_identity)

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **Base-case restriction, exact value.** For `3 ≤ N`, `4 ≤ n`, the restriction to the plane group `Γ_{1⁻¹P1}` of the
standard cusp of the complexified class of the holomorphic series at `x = [1]` is exactly the conjugated holomorphic seed
`faceSeedKerClass N 1 n f` of `f` (so the series at this cusp has constant term the seed, no hypothesis).  This is a statement
about ONE series at ONE cusp, not `SeriesRestrictionInSeedSpan` for a whole series. -/
theorem baseRestriction_eq_faceSeed (hn : 4 ≤ n) (hN : 3 ≤ N) :
    resAtC N 1 n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f 1 false hn)) =
      (faceSeedKerClass N 1 n f).1 := by
  rw [eisensteinAtClass_gammaN_one, resAtC_one_complexify, constant_term_identity N n f hn hN,
    complexifyG_cuspSeedClass]
  rfl

/-- **The base-case seed-span statement**: the restriction of the standard-cusp holomorphic series class to `h = 1` lies in
`faceSeedSpan N 1 n`.  Only the pair (series at the standard cusp with the holomorphic seed, plane cusp `h = 1`). -/
theorem baseRestriction_in_seedSpan (hn : 4 ≤ n) (hN : 3 ≤ N) :
    resAtC N 1 n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f 1 false hn)) ∈ faceSeedSpan N 1 n := by
  rw [baseRestriction_eq_faceSeed N n f hn hN]
  exact ⟨faceSeedKerClass N 1 n f, Submodule.subset_span (Or.inl ⟨f, rfl⟩), rfl⟩

/-- **`r_B 𝓔_P(ω_f) = 0` over the standard plane, unconditional** (`3 ≤ N`, `4 ≤ n`): the restriction of the complexified
class of the literal series to the stabilizer of every complete flag over the standard plane vanishes. -/
theorem rB_standard (hn : 4 ≤ n) (hN : 3 ≤ N) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n)
      (complexifyG N n (resP N n (Statements.EisensteinClass.eisensteinClass_gammaN N n f hn))) = 0 :=
  flag_vanishing_of_constantTerm N n f hn
    ((resP_eisensteinClass_iff N n f hn).1 (constant_term_identity N n f hn hN)) F

end Base

end TernaryPeriodPolynomials.Argument.FormClassK
