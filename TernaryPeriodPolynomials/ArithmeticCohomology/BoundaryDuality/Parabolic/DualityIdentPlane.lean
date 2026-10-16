module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentGoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentSwap
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.GoodLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PAHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PlaneCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula

@[expose] public section


/-!
# The Levi cocycle of the dual plane is minus the transported edge image of the plane class

The dual involution `φ` carries the stabilizer of the good line `L₁` to the stabilizer `Λ₀` of the
identity plane `P₀ = dualFlag L₁`, the lattice `U` of `L₁` to the upper radical lattice, and the
Levi element `diag(γ, 1)` to `diag(γ^{-T}, 1)`.  The plane cocycle of the fiber integration,
`η(x) = y(φ x)(P₀)`, is therefore the pullback along `φ` of the cocycle `cp = y(·)(P₀)` of `Λ₀`, and
`θ_U ∘ φ` is an equivariant primitive of `cp` over the upper radical lattice.  The algebra of
`ParabolicDualityIdentCore` then shows, with `E` the mixed radical cocycle of the relative
representative of `cp` at the Levi element `diag(γ^{-T}, 1)`,

  `Ψ(A'(k_γ⁻¹)) = rot (Φ'(A'(k_γ⁻¹))) = - rot (E_{γ^{-T}})`

(`bridgeX'_apply_trivial`), i.e. the cocycle `bridgeX'` of the bridge is the pullback along `invT`
of minus the identity-plane edge cocycle, followed by the rotation.  By `ParabolicDualityIdentSwap`
its class is nonzero, and the cocycle parabolic, as soon as the edge image is
(`projectH1_bridgeX'_ne_zero_trivial`, `bridgeX'_mem_parabolicCocycles_trivial`, and the odd
character analogues).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (fixedPointCycle fixedPointH2)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates (Λ₀)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (leviCocycle pull1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (dualFlag_L₁)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (leviHom leviHom_eq lower_mem_sub det_upperRadicalLattice rho_radical_eq wCoc wCoc_apply
    upperTotal upperTotal_eq PsiTotal coord_upper_eq_of_shift uCocycle_leviCocycle_hom
    dualInvolution_leviHom invT binarySwap bridgeX' psiTwist_trivial psiTwist_odd
    dualInvolution_lowerRadicalLattice_mul)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-! ### The involution on the radical lattices -/

/-- `φ (lower p) = upper p⁻¹`: the level involution of the good-line radical element is the
identity-plane radical element with the inverse coordinates. -/
theorem dualInvolution_lowerRadicalLattice (p : RadicalLattice) :
    dualInvolution (lowerRadicalLattice p) = upperRadicalLattice p⁻¹ := by
  have h1 := dualInvolution_lowerRadicalLattice_mul p
  rw [mul_eq_one_iff_eq_inv] at h1
  rw [h1, ← map_inv]

/-- The upper radical lattice, as a subgroup of `GL₃(ℚ)`. -/
def planeRadical : Subgroup RationalGL3 := upperRadicalLattice.range

/-- The Levi embedding of `GL₂(ℤ)` lies in the arithmetic stabilizer of the identity plane. -/
theorem leviHom_mem_Λ₀ (γ : GL2Z) : leviHom γ ∈ Λ₀ :=
  arithmeticLevi_identityPlane γ

/-- `k⁻¹ u(p) k = u(p · γ)` on the upper radical lattice. -/
theorem upper_levi_inv_conj (γ : GL2Z) (p : RadicalLattice) :
    (leviHom γ)⁻¹ * upperRadicalLattice p * leviHom γ =
      upperRadicalLattice (upperLeviLatticeInput γ p) := by
  have h := upperLeviLatticeInput_conjugation γ p
  rw [leviHom_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h

/-- The Levi element normalizes the upper radical lattice. -/
theorem planeRadical_levi_normalizes (γ : GL2Z) :
    ∀ u ∈ planeRadical, leviHom γ * u * (leviHom γ)⁻¹ ∈ planeRadical := by
  rintro u ⟨q, rfl⟩
  have h := upper_levi_inv_conj γ⁻¹ q
  rw [map_inv, inv_inv] at h
  exact ⟨_, h.symm⟩

/-! ### The primitive `θ_U ∘ φ` -/

/-- The primitive of the plane cocycle obtained from `θ_U` by moving the vertices by `φ`. -/
def omegaP {n : ℕ} (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) :
    (Fin 2 → RationalGL3) → HomogeneousPoly n :=
  fun y => θU ![dualInvolution (y 0), dualInvolution (y 1)]

/-- **The Levi cocycle of the dual coefficients, transported by `φ`**:
`A'(h)(a, b) = A(φ h)(φ a, φ b)` for the primitive `θ_U ∘ φ`. -/
theorem leviCocycle_dual {n : ℕ} (χ : RankOneCharacter)
    (θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) (h a b : RationalGL3) :
    leviCocycle (dualRep (dualityData n χ)) θU h ![a, b] =
      leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (dualInvolution h)
        ![dualInvolution a, dualInvolution b] := by
  change rationalCoefficientComponent n χ (dualInvolution h⁻¹) (θU ![h * a, h * b]) - θU ![a, b] =
    rationalCoefficientComponent n χ (dualInvolution h)⁻¹
      (θU ![dualInvolution (dualInvolution h * dualInvolution a),
        dualInvolution (dualInvolution h * dualInvolution b)]) -
      θU ![dualInvolution (dualInvolution a), dualInvolution (dualInvolution b)]
  simp only [map_mul, map_inv, dualInvolution_involutive]

section Fiber

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- `θ_U ∘ φ` is a primitive of the plane cocycle `cp`. -/
theorem omegaP_d (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    ∀ a b c, differentialOneRaw (omegaP θU) ![a, b, c] = cp.val.val ![a, b, c] := by
  intro a b c
  have h1 := hF.thetaU_d (dualInvolution a) (dualInvolution b) (dualInvolution c)
  have h2 : η ![dualInvolution a, dualInvolution b, dualInvolution c] =
      cp.val.val ![dualInvolution (dualInvolution a), dualInvolution (dualInvolution b),
        dualInvolution (dualInvolution c)] := hη _
  simp only [dualInvolution_involutive] at h2
  exact h1.trans h2

/-- `θ_U ∘ φ` is equivariant over the upper radical lattice. -/
theorem omegaP_hω (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) :
    ∀ g ∈ planeRadical, ∀ a b, omegaP θU ![g * a, g * b] =
      rationalCoefficientComponent n χ g (omegaP θU ![a, b]) := by
  rintro g ⟨p, rfl⟩ a b
  have hu : dualInvolution (lowerRadicalLattice p⁻¹) = upperRadicalLattice p := by
    rw [dualInvolution_lowerRadicalLattice, inv_inv]
  have hu' : dualInvolution (upperRadicalLattice p) = lowerRadicalLattice p⁻¹ := by
    rw [← hu, dualInvolution_involutive]
  have h := hF.thetaU_eq (lowerRadicalLattice p⁻¹) (lower_mem_sub p⁻¹) (dualInvolution a)
    (dualInvolution b)
  change θU ![dualInvolution (upperRadicalLattice p * a),
      dualInvolution (upperRadicalLattice p * b)] =
    rationalCoefficientComponent n χ (upperRadicalLattice p)
      (θU ![dualInvolution a, dualInvolution b])
  rw [map_mul, map_mul, hu', h]
  change rationalCoefficientComponent n χ (dualInvolution (lowerRadicalLattice p⁻¹))
    (θU ![dualInvolution a, dualInvolution b]) = _
  rw [hu]

/-- The value of the relative representative on a pair, as an element of the coefficient module. -/
def relValOn (Γ : Subgroup RationalGL3) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (g h : Γ) : V :=
  relCocycleOn Γ ρ ω C (g, h)

theorem relValOn_apply (Γ : Subgroup RationalGL3) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ω : (Fin 2 → RationalGL3) → V) (C : cocycles Γ ρ)
    (hd : ∀ a b c, differentialOneRaw ω ![a, b, c] = C.val.val ![a, b, c]) (g h : Γ) :
    relValOn Γ ρ ω C g h = ω ![g.val, g.val * h.val] - ρ g.val (ω ![1, h.val]) :=
  relCocycleOn_apply Γ ρ ω C hd g h

/-- **The identity on the upper radical lattice.**  The mixed radical value of the relative
representative of `cp` at the Levi element `diag(γ', 1)` plus the Levi cocycle `A'(k⁻¹)(1, u)` is
the coboundary of `-w`. -/
theorem plane_edge_add_levi (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)])
    (γ' : GL2Z) (p : RadicalLattice) :
    (relValOn Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp
        (identityPlaneLeviSection γ') (identityPlaneRadicalInclusion (upperLeviLatticeInput γ' p)) -
      relValOn Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp
        (identityPlaneRadicalInclusion p) (identityPlaneLeviSection γ')) +
      leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom γ')⁻¹
        ![1, upperRadicalLattice p] =
    rationalCoefficientComponent n χ (upperRadicalLattice p)
        (-(rationalCoefficientComponent n χ (leviHom γ')
          (leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom γ')
            ![1, (leviHom γ')⁻¹]))) -
      (-(rationalCoefficientComponent n χ (leviHom γ')
          (leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom γ')
            ![1, (leviHom γ')⁻¹]))) := by
  have hd := omegaP_d hF cp hη
  have key := levi_identity (rationalCoefficientComponent n χ) (omegaP θU) cp.val.val hd
    (omegaP_hω hF)
    (cocycle_vec3 Λ₀ (rationalCoefficientComponent n χ) cp (leviHom_mem_Λ₀ γ'))
    (planeRadical_levi_normalizes γ') (u := upperRadicalLattice p)
    (u'' := upperRadicalLattice (upperLeviLatticeInput γ' p)) ⟨p, rfl⟩
    ⟨upperLeviLatticeInput γ' p, rfl⟩ (upperLeviLatticeInput_conjugation γ' p)
  rw [relValOn_apply Λ₀ _ _ cp hd, relValOn_apply Λ₀ _ _ cp hd]
  exact key

/-- The upper radical cocycle of the Levi cocycle of the dual coefficients at `k_γ⁻¹` is the Levi
cocycle of the primitive `θ_U ∘ φ` at `k_{γ^{-T}}⁻¹`. -/
theorem wCoc_eq_levi (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (γ : GL2Z) (p : RadicalLattice) :
    wCoc n χ (uCocycle_leviCocycle_hom hF γ).2 p =
      leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom (invT γ))⁻¹
        ![1, upperRadicalLattice p] := by
  have e1 : dualInvolution (leviHom γ)⁻¹ = (leviHom (invT γ))⁻¹ := by
    rw [map_inv, dualInvolution_leviHom]
  have e2 : dualInvolution (lowerRadicalLattice p⁻¹) = upperRadicalLattice p := by
    rw [dualInvolution_lowerRadicalLattice, inv_inv]
  rw [wCoc_apply, leviCocycle_dual, e1, e2, map_one]

/-- **The coordinate of the edge cocycle is minus the coordinate of the Levi cocycle** at the
identity plane. -/
theorem plane_coordinate_edge (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)])
    (γ : GL2Z) (E : groupCohomology.cocycles₁ (upperRadicalLatticeRep n))
    (hE : ∀ p, E p =
      relCocycleOn Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp
          (identityPlaneLeviSection (invT γ),
            identityPlaneRadicalInclusion (upperLeviLatticeInput (invT γ) p)) -
        relCocycleOn Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp
          (identityPlaneRadicalInclusion p, identityPlaneLeviSection (invT γ))) :
    upperRadicalCocycleCoordinate n E =
      -upperTotal n (leviCocycle (dualRep (dualityData n χ)) θU (leviHom γ)⁻¹) := by
  have hg := (uCocycle_leviCocycle_hom hF γ).2
  rw [upperTotal_eq n χ hg]
  refine (coord_upper_eq_of_shift n E (-wCoc n χ hg)
    (-(rationalCoefficientComponent n χ (leviHom (invT γ))
      (leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom (invT γ))
        ![1, (leviHom (invT γ))⁻¹]))) (fun p => ?_)).trans
    (map_neg (upperRadicalCocycleCoordinate n) (wCoc n χ hg))
  have key := plane_edge_add_levi hF cp hη (invT γ) p
  have e : (upperRadicalLatticeRep n).ρ p =
      rationalCoefficientComponent n χ (upperRadicalLattice p) :=
    (upperRadicalLatticeRep_rho n p).trans (rho_radical_eq n χ (det_upperRadicalLattice p)).symm
  have hz : (-wCoc n χ hg) p =
      -(leviCocycle (rationalCoefficientComponent n χ) (omegaP θU) (leviHom (invT γ))⁻¹
        ![1, upperRadicalLattice p]) := congrArg Neg.neg (wCoc_eq_levi hF γ p)
  rw [e, hz, hE p]
  exact (eq_sub_of_add_eq key).trans (sub_eq_neg_add _ _)

end Fiber

/-! ### The trivial character -/

section Trivial

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The relative two-cocycle of the identity plane** attached to the dual plane data, trivial
character. -/
def relOfP (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n trivialCharacter))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    Spectral.IdentityPlaneCoordinate.Rel n :=
  relOn Λ₀ (rationalCoefficientComponent n trivialCharacter) (omegaP θU) cp (omegaP_d hF cp hη)
    (omegaP_hω hF) identityPlaneRadicalInclusion (fun p => ⟨p, rfl⟩)

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOfP_H2 (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n trivialCharacter))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    groupCohomology.H2π (identityPlaneCoefficientRep n) (relOfP hF cp hη).val =
      groupCohomology.H2π (identityPlaneCoefficientRep n) (ambientCocycleToGroup Λ₀ (ρn n) cp) :=
  relOn_H2 Λ₀ (rationalCoefficientComponent n trivialCharacter) (omegaP θU) cp
    (omegaP_d hF cp hη) (omegaP_hω hF) identityPlaneRadicalInclusion (fun p => ⟨p, rfl⟩)

/-- **The edge cocycle of the plane class** has the class `edgeH2` of the plane class. -/
theorem projectH1_edgeCycle_eq_edgeH2 (hn : 0 < n) (hodd : Odd n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n trivialCharacter))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1))
        (identityPlaneBinaryEdgeCycle n (relOfP hF cp hη)) =
      Spectral.IdentityPlaneHecke.edgeH2 n hn hodd (classOf Λ₀ (ρn n) cp) :=
  ((congrArg (identityPlaneFullBinaryEdge n hn hodd) (relOfP_H2 hF cp hη).symm).trans
    (identityPlaneFullBinaryEdge_relative n hn hodd (relOfP hF cp hη))).symm

/-- **Identification, trivial character.**  The cocycle `bridgeX'` of the plane is the pullback
along `invT` of minus the identity-plane edge cocycle, followed by the rotation. -/
theorem bridgeX'_apply_trivial (hodd : Odd n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n trivialCharacter))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)])
    (γ : GL2Z) :
    bridgeX' (-1) (psiTwist_trivial hodd) hF γ =
      -binarySwap (n + 1) (identityPlaneBinaryEdgeCycle n (relOfP hF cp hη) (invT γ)) := by
  have hE := plane_coordinate_edge hF cp hη γ
    (identityPlaneRadicalEdgeCycle n (relOfP hF cp hη) (invT γ))
    (fun p => identityPlaneSplitEdgeCycle_apply n (relOfP hF cp hη) (invT γ) p)
  have h1 : bridgeX' (-1) (psiTwist_trivial hodd) hF γ =
      binarySwap (n + 1) (upperTotal n
        (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (leviHom γ)⁻¹)) := rfl
  rw [h1, identityPlaneBinaryEdgeCycle_apply, hE, map_neg, neg_neg]

end Trivial

/-! ### An odd character -/

section Odd

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The relative two-cocycle of the identity plane** attached to the dual plane data, twisted
coefficients. -/
def relOfPT (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    Twisted.RelT n χ :=
  relOn Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp (omegaP_d hF cp hη)
    (omegaP_hω hF) identityPlaneRadicalInclusion (fun p => ⟨p, rfl⟩)

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOfPT_H2 (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    groupCohomology.H2π (Twisted.identityPlaneCoefficientRepT n χ)
        (relOfPT hF cp hη).val =
      groupCohomology.H2π (Twisted.identityPlaneCoefficientRepT n χ)
        (ambientCocycleToGroup Λ₀ (rationalCoefficientComponent n χ) cp) :=
  relOn_H2 Λ₀ (rationalCoefficientComponent n χ) (omegaP θU) cp (omegaP_d hF cp hη)
    (omegaP_hω hF) identityPlaneRadicalInclusion (fun p => ⟨p, rfl⟩)

/-- **The twisted edge cocycle of the plane class** has the class `edgeH2T` of the plane class. -/
theorem projectH1_edgeCycleT_eq_edgeH2T (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)]) :
    projectH1 (arithmeticBinaryRep (n + 1) 0)
        (Twisted.identityPlaneBinaryEdgeCycleT n χ hχ (relOfPT hF cp hη)) =
      Twisted.edgeH2T n χ hχ hn hodd
        (classOf Λ₀ (rationalCoefficientComponent n χ) cp) :=
  ((congrArg (Twisted.identityPlaneFullBinaryEdgeT n χ hχ hn hodd)
      (relOfPT_H2 hF cp hη).symm).trans
    (Twisted.identityPlaneFullBinaryEdgeT_relative n χ hχ hn hodd
      (relOfPT hF cp hη))).symm

/-- **Identification, odd character.** -/
theorem bridgeX'_apply_odd (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hodd : Odd n)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (cp : cocycles Λ₀ (rationalCoefficientComponent n χ))
    (hη : ∀ x, η x =
      cp.val.val ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)])
    (γ : GL2Z) :
    bridgeX' 0 (psiTwist_odd hodd hχ) hF γ =
      -binarySwap (n + 1)
        (Twisted.identityPlaneBinaryEdgeCycleT n χ hχ (relOfPT hF cp hη) (invT γ)) := by
  have hE := plane_coordinate_edge hF cp hη γ
    (Twisted.identityPlaneRadicalEdgeCycleT n χ (relOfPT hF cp hη) (invT γ))
    (fun p => Twisted.identityPlaneSplitEdgeCycleT_apply n χ (relOfPT hF cp hη)
      (invT γ) p)
  have h1 : bridgeX' 0 (psiTwist_odd hodd hχ) hF γ =
      binarySwap (n + 1) (upperTotal n
        (leviCocycle (dualRep (dualityData n χ)) θU (leviHom γ)⁻¹)) := rfl
  rw [h1, Twisted.identityPlaneBinaryEdgeCycleT_apply, hE, map_neg, neg_neg]

end Odd

/-! ### From a class of the maximal stratum to the identity-plane cocycle -/

/-- **The cocycle of the identity-plane stabilizer** attached to a cocycle on the flags: its value at
the base plane `mk 1`. -/
def cocycleAtPlane (n : ℕ) (χ : RankOneCharacter)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .plane)) :
    cocycles Λ₀ (rationalCoefficientComponent n χ) :=
  fixedPointCycle rationalLevel (rationalCoefficientComponent n χ)
    (QuotientGroup.mk (1 : RationalGL3) : Flags .plane) y

/-- The fiber cocycle `η`, given by the value of `y ∘ φ` at the dual plane of `L₁`, is the
pullback along `φ` of the plane cocycle. -/
theorem eta_eq_cocycleAtPlane (n : ℕ) (χ : RankOneCharacter)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    {η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n χ).dualFlag L₁)) :
    ∀ x, η x = (cocycleAtPlane n χ y).val.val
      ![dualInvolution (x 0), dualInvolution (x 1), dualInvolution (x 2)] := fun x =>
  (hη x).trans (congrArg (fun F : Flags .plane => y.val.val ![dualInvolution (x 0),
    dualInvolution (x 1), dualInvolution (x 2)] F) dualFlag_L₁)

/-- The Shapiro coordinate of a class at the base plane is the class of `cocycleAtPlane`. -/
theorem cuspRes_plane_false_classOf (n : ℕ) (χ : RankOneCharacter)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .plane)) :
    Spectral.CuspReduction.cuspRes n χ .plane false
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) =
      classOf Λ₀ (rationalCoefficientComponent n χ) (cocycleAtPlane n χ y) :=
  rfl

/-! ### Consequences, trivial character -/

section TrivialStratum

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **`bridgeX'` is a parabolic cocycle** when the Shapiro coordinate of the plane class at the base
plane is a local joint generalized eigenclass with a small `T₂`-eigenvalue. -/
theorem bridgeX'_mem_parabolicCocycles_trivial (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hx : Spectral.CuspReduction.cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ∈
      Spectral.CuspReduction.localJoint n trivialCharacter c .plane false)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    bridgeX' (-1) (psiTwist_trivial hodd) hF ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) := by
  have hη' := eta_eq_cocycleAtPlane n trivialCharacter y hη
  rw [cuspRes_plane_false_classOf] at hx
  have hFpar : identityPlaneBinaryEdgeCycle n
      (relOfP hF (cocycleAtPlane n trivialCharacter y) hη') ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) := by
    apply mem_parabolicCocycles_of_projectH1_mem
    rw [projectH1_edgeCycle_eq_edgeH2 hn hodd hF _ hη']
    exact edgeH2_mem_parabolicH1 n hn hodd c hc hx
  exact swapPullback_mem_parabolicCocycles hodd (-1) hFpar
    (fun γ => bridgeX'_apply_trivial hodd hF _ hη' γ)

/-- **The class of `bridgeX'` is nonzero** when the Shapiro coordinate of the plane class at the
base plane is a nonzero local joint generalized eigenclass. -/
theorem projectH1_bridgeX'_ne_zero_trivial (hn : 0 < n) (hodd : Odd n)
    (y : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane))
    (hne : Spectral.CuspReduction.cuspRes n trivialCharacter .plane false
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y) ≠ 0)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n trivialCharacter).dualFlag L₁)) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX' (-1) (psiTwist_trivial hodd) hF) ≠ 0 := by
  have hη' := eta_eq_cocycleAtPlane n trivialCharacter y hη
  rw [cuspRes_plane_false_classOf] at hne
  have hFne : projectH1 (arithmeticBinaryRep (n + 1) (-1))
      (identityPlaneBinaryEdgeCycle n (relOfP hF (cocycleAtPlane n trivialCharacter y) hη')) ≠
      0 := by
    rw [projectH1_edgeCycle_eq_edgeH2 hn hodd hF _ hη']
    intro h0
    exact hne (Spectral.IdentityPlaneHecke.edgeH2_injective n hn hodd
      (h0.trans (map_zero (Spectral.IdentityPlaneHecke.edgeH2 n hn hodd)).symm))
  exact swapPullback_projectH1_ne_zero hodd (-1)
    (fun γ => bridgeX'_apply_trivial hodd hF _ hη' γ) hFne

end TrivialStratum

/-! ### Consequences, odd character -/

section OddStratum

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **`bridgeX'` is a parabolic cocycle for an odd character** when the Shapiro coordinate of the
plane class at the base plane is a local joint generalized eigenclass with `‖c(T₂) + 1‖ ≤ 3/4`. -/
theorem bridgeX'_mem_parabolicCocycles_odd (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    (hx : Spectral.CuspReduction.cuspRes n χ .plane false
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) ∈
      Spectral.CuspReduction.localJoint n χ c .plane false)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n χ).dualFlag L₁)) :
    bridgeX' 0 (psiTwist_odd hodd hχ) hF ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) 0) := by
  have hη' := eta_eq_cocycleAtPlane n χ y hη
  rw [cuspRes_plane_false_classOf] at hx
  have hFpar : Twisted.identityPlaneBinaryEdgeCycleT n χ hχ
      (relOfPT hF (cocycleAtPlane n χ y) hη') ∈
      parabolicCocycles (arithmeticBinaryRep (n + 1) 0) := by
    apply mem_parabolicCocycles_of_projectH1_mem
    rw [projectH1_edgeCycleT_eq_edgeH2T hχ hn hodd hF _ hη']
    exact edgeH2T_mem_parabolicH1 n χ hχ hn hodd c hc hx
  exact swapPullback_mem_parabolicCocycles hodd 0 hFpar
    (fun γ => bridgeX'_apply_odd hχ hodd hF _ hη' γ)

/-- **The class of `bridgeX'` is nonzero for an odd character** when the Shapiro coordinate of the
plane class at the base plane is nonzero. -/
theorem projectH1_bridgeX'_ne_zero_odd (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (hodd : Odd n)
    (y : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane))
    (hne : Spectral.CuspReduction.cuspRes n χ .plane false
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y) ≠
      0)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (hη : ∀ x, η x = y.val.val ![dualInvolution (x 0), dualInvolution (x 1),
      dualInvolution (x 2)] ((dualityData n χ).dualFlag L₁)) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX' 0 (psiTwist_odd hodd hχ) hF) ≠ 0 := by
  have hη' := eta_eq_cocycleAtPlane n χ y hη
  rw [cuspRes_plane_false_classOf] at hne
  have hFne : projectH1 (arithmeticBinaryRep (n + 1) 0)
      (Twisted.identityPlaneBinaryEdgeCycleT n χ hχ
        (relOfPT hF (cocycleAtPlane n χ y) hη')) ≠ 0 := by
    rw [projectH1_edgeCycleT_eq_edgeH2T hχ hn hodd hF _ hη']
    intro h0
    exact hne (Twisted.edgeH2T_injective n χ hχ hn hodd
      (h0.trans (map_zero (Twisted.edgeH2T n χ hχ hn hodd)).symm))
  exact swapPullback_projectH1_ne_zero hodd 0
    (fun γ => bridgeX'_apply_odd hχ hodd hF _ hη' γ) hFne

end OddStratum

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

end
