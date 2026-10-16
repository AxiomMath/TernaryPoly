module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Principal
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison.Coordinates

@[expose] public section


/-!
# The form class transported to the principal subgroup of the level group, and its transfer to `K†`

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem componentCharacter_trivial (g : RealGL3) : componentCharacter trivialCharacter g = 1 := by
  simp [componentCharacter, trivialCharacter]

/-- The coefficient comparison for `Γ(N) ≅ Γ ∩ Γ(N)`. -/
theorem principalEquiv_val (N : ℕ) (h3 : 3 ∣ N) (hN : 3 ≤ N) (γ : gammaN N) :
    (principalEquiv N h3 hN γ : RationalGL3) = (toRationalLevel N h3 γ : RationalGL3) := by
  apply Units.ext
  ext i j
  rfl

theorem rho_principalEquiv (N : ℕ) (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (γ : gammaN N) :
    rationalCoefficientComponent n trivialCharacter (principalEquiv N h3 hN γ : RationalGL3) =
      gammaRhoC (gammaN N) n γ := by
  rw [principalEquiv_val]
  exact (rat_rep_eq N h3 n trivialCharacter componentCharacter_trivial γ).symm

section Class

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (n : ℕ)

/-- The coefficient comparison as an isomorphism of cohomology groups
`H²(Γ(N), E_n) ≅ H²(Γ ∩ Γ(N), E_n)`. -/
def principalIso (hN : 3 ≤ N) :
    groupCohomology (gammaRep (gammaN N) n) 2 ≅
      groupCohomology (Rep.of ((rationalCoefficientComponent n trivialCharacter).comp
        (levelPrincipal N).subtype)) 2 :=
  groupCohomology.mapIso (principalEquiv N h3 hN) (LinearEquiv.refl ℂ (HomogeneousPoly n))
    (fun g => LinearMap.ext fun v =>
      congrArg (fun L => L v) (rho_principalEquiv N h3 hN n g).symm) 2

/-- **Transport of a class of `Γ(N)` to the principal subgroup `Γ ∩ Γ(N)` of the level group** (homogeneous-cochain
model over `GL₃(ℚ)`), as a `ℂ`-linear map. -/
def classPrincipal (hN : 3 ≤ N) :
    groupCohomology.H2 (gammaRep (gammaN N) n) →ₗ[ℂ]
      H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter) :=
  (bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)).symm.toLinearMap ∘ₗ
    (principalIso N h3 n hN).hom.hom

/-- **The complexified form class `[𝓔_P(ω_h)] ∈ H²(Γ(N), E_n)_ℂ`, transported to the principal subgroup
`Γ ∩ Γ(N)` of the level group.** -/
def formClassPrincipal (hN : 3 ≤ N) (hn : 4 ≤ n)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    H2 (levelPrincipal N) (rationalCoefficientComponent n trivialCharacter) :=
  classPrincipal N h3 n hN
    (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn)

end Class

section Class2

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

omit [NeZero N] in
/-- The transport loses nothing: pulling `classPrincipal x` back along `Γ(N) ≅ Γ ∩ Γ(N)` recovers `x`. -/
theorem principalIso_inv_classPrincipal (x : groupCohomology.H2 (gammaRep (gammaN N) n)) :
    (principalIso N h3 n hN).inv.hom
        (bridge (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
          (classPrincipal N h3 n hN x)) = x := by
  unfold classPrincipal
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact congrArg (fun φ => φ.hom x) (principalIso N h3 n hN).hom_inv_id

/-- **The corestriction to `K†`** of a class of `Γ(N)`: the transfer `H²(Γ ∩ Γ(N), E_n) → H²(Γ, E_n)` of its
transport (`Γ = rationalLevel`).  `ℂ`-linear. -/
def classK : groupCohomology.H2 (gammaRep (gammaN N) n) →ₗ[ℂ]
    H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  trToLevel (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
    (levelPrincipal_le N) (levelPrincipal_norm N) ∘ₗ classPrincipal N h3 n hN

/-- **A class of `Γ(N)` is locally inner at every rational plane** (the statement `r_P x ∈ 𝒞_{P'}(E)` at
every plane cusp `P'`, in the homogeneous model): the restriction of its transport to `Γ_F ∩ Γ(N)` vanishes on the
stabilizer of every complete flag over `F`, for every rational plane `F`.  For the class of the form series this is
an OBLIGATION about the series (constant terms at all plane cusps: `r_P = ξ` with `ξ` mixed cuspidal); it is not
proved here. -/
def PlaneLocallyInner (x : groupCohomology.H2 (gammaRep (gammaN N) n)) : Prop :=
  ∀ F : Flags .plane,
    resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) F) (classPrincipal N h3 n hN x) ∈
      locallyInnerAt (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N) F

omit [NeZero N] in
/-- Local innerness at every plane gives vanishing on the stabilizer of every complete flag. -/
theorem classPrincipal_edge_vanishing (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (h : PlaneLocallyInner N h3 hN n x) (e : Edges) :
    resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) e) (classPrincipal N h3 n hN x) = 0 := by
  have h1 := h (endpoint .plane e)
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall] at h1
  have h2 := h1 e rfl
  rw [resH2_comp] at h2
  exact h2

/-- **The corestriction `classK x` restricts to zero on the stabilizer of every complete flag** once `x` is locally
inner at every plane. -/
theorem classK_edge_vanishing (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (h : PlaneLocallyInner N h3 hN n x) (e : Edges) :
    resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_level e) (classK N h3 hN n x) = 0 :=
  faceRestriction_trToLevel_eq_zero (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
    (levelPrincipal_le N) (levelPrincipal_norm N) (classPrincipal N h3 n hN x)
    (classPrincipal_edge_vanishing N h3 hN n x h) e

/-- **Honest alternative for `r_Q E_P(ξ) = T ξ` (conditional on the hypothesis `PlaneLocallyInner`).**  If a class
`x` of `Γ(N)` is locally inner at every rational plane, then any global cocycle `c` representing its `K†`-corestriction
has `InnerBoundary` plane and line coordinates, and its line coordinate is `T` applied to its plane coordinate, for the
canonical map `T` of `line_constant_term_comparison`.  This does NOT identify the plane coordinate with a cusp-form seed class `ξ` (the constant
term `r_P = ξ`; open), and says nothing about `Γ(N)`-level `r_Q`. -/
theorem classK_line_eq_T (hn : 4 ≤ n) (x : groupCohomology.H2 (gammaRep (gammaN N) n))
    (h : PlaneLocallyInner N h3 hN n x) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      BadPlaneInjectivity.IsUniquenessMap n trivialCharacter T ∧
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        InnerBoundary n trivialCharacter .line (T ξ) ∧
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
            classK N h3 hN n x →
          InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 ∧
          InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 ∧
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  obtain ⟨T, ha, hb⟩ := Classification.prop_C_5_proof n hn
  refine ⟨T, hb, ha, fun c hc => ?_⟩
  have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
    intro e
    rw [hc]
    exact classK_edge_vanishing N h3 hN n x h e
  exact ⟨innerBoundary_of_edgeVanishing n trivialCharacter .plane c he,
    innerBoundary_of_edgeVanishing n trivialCharacter .line c he,
    lineCoordinate_eq_of_edgeVanishing n T hb c he⟩

/-- The `K†`-corestriction of the form class `[𝓔_P(ω_h)]`. -/
def formClassK (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  classK N h3 hN n
    (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn)

/-- The `K†`-corestriction of the class of the series at the plane cusp `h` for the seed of type `b`
(complexified). -/
def formClassKAt (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (h : SL(3, ℤ)) (b : Bool) :
    H2 rationalLevel (rationalCoefficientComponent n trivialCharacter) :=
  classK N h3 hN n
    (complexify (gammaN N) n
      (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n f h b hn))

end Class2

end TernaryPeriodPolynomials.Argument.FormClassK
