module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# Lifting a local class supported at one cusp, and necessity of the four local statements

A homogeneous cochain of the stabilizer `Γ_F` of a point `F` extends, by `Γ`-translation, to a
cochain of `Γ` with coefficients in functions on the `G(ℚ)`-set, supported on the orbit `ΓF`
(the inverse of Shapiro's isomorphism on one orbit). For the reference cusps this gives a class with
prescribed Shapiro coordinate at one cusp and zero coordinate at the other cusp of the same side.

Consequences:
* `cusps_of_eigenSeparated`: when the associate pair is nonzero, eigencharacter separation IMPLIES
  the four local statements of `CuspReduction.eigenSeparated_of_cusps`; so the four-cusp
  reduction is an equivalence.
* `localOp_eq_smul_of_eigenSeparated`: separation forces every local away-from-three Hecke
  operator to act by the scalar `c t` on the local joint generalized eigenspace. Thus a proof of the
  targets necessarily contains semisimplicity of the local Hecke action at every cusp
  (classically: Hecke semisimplicity on the `σ`-part of cusp forms, from the Petersson product).

Original work by Claude Opus 5.5 (AxiomCode, Sol).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SpectralSeparation

namespace TernaryPeriodPolynomials.Spectral.CuspLift

open CuspOrbits CuspReduction

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

section Extension

variable (rho : Representation ℂ RationalGL3 V) (point : X)

/-- The value of the extended cochain at a point of the orbit (zero off the orbit). -/
def extendValue {k : ℕ} (z : cochains (fixedPointLevel rationalLevel point) rho k)
    (vertices : Fin (k + 1) → RationalGL3) (q : X) : V := by
  classical
  exact if h : ∃ γ : rationalLevel, γ.val • point = q then
    rho h.choose.val (z.val (fun index => h.choose.val⁻¹ * vertices index)) else 0

theorem extendValue_of_mem {k : ℕ} (z : cochains (fixedPointLevel rationalLevel point) rho k)
    (vertices : Fin (k + 1) → RationalGL3) {q : X} (h : ∃ γ : rationalLevel, γ.val • point = q) :
    extendValue rho point z vertices q =
      rho h.choose.val (z.val (fun index => h.choose.val⁻¹ * vertices index)) := by
  classical
  unfold extendValue
  rw [dite_eq_left h]

theorem extendValue_of_not_mem {k : ℕ} (z : cochains (fixedPointLevel rationalLevel point) rho k)
    (vertices : Fin (k + 1) → RationalGL3) {q : X} (h : ¬ ∃ γ : rationalLevel, γ.val • point = q) :
    extendValue rho point z vertices q = 0 := by
  classical
  unfold extendValue
  rw [dite_eq_right h]

/-- Independence of the transporter: any `γ ∈ Γ` with `γ F = q` computes the value. -/
theorem extendValue_eq {k : ℕ} (z : cochains (fixedPointLevel rationalLevel point) rho k)
    (vertices : Fin (k + 1) → RationalGL3) (γ : rationalLevel) {q : X} (hγ : γ.val • point = q) :
    extendValue rho point z vertices q =
      rho γ.val (z.val (fun index => γ.val⁻¹ * vertices index)) := by
  have h : ∃ γ : rationalLevel, γ.val • point = q := ⟨γ, hγ⟩
  rw [extendValue_of_mem rho point z vertices h]
  set τ := h.choose with hτ
  have hτspec : τ.val • point = q := h.choose_spec
  let μ : RationalGL3 := τ.val⁻¹ * γ.val
  have hμ : μ ∈ fixedPointLevel rationalLevel point := by
    refine ⟨rationalLevel.mul_mem (rationalLevel.inv_mem τ.property) γ.property, ?_⟩
    apply MulAction.mem_stabilizer_iff.mpr
    change (τ.val⁻¹ * γ.val) • point = point
    rw [mul_smul, hγ, ← hτspec, inv_smul_smul]
  have hequiv := z.property ⟨μ, hμ⟩ (fun index => γ.val⁻¹ * vertices index)
  have hvert : (fun index => τ.val⁻¹ * vertices index) =
      (fun index => μ * (γ.val⁻¹ * vertices index)) := by
    funext index
    simp only [μ, mul_assoc, mul_inv_cancel_left]
  change rho τ.val (z.val (fun index => τ.val⁻¹ * vertices index)) = _
  rw [hvert]
  rw [hequiv, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp only [μ, mul_inv_cancel_left]

/-- The extension of a stabilizer cochain to a `Γ`-cochain supported on the orbit of the point. -/
def extendCochain (k : ℕ) :
    cochains (fixedPointLevel rationalLevel point) rho k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation rho X) k where
  toFun z := ⟨fun vertices q => extendValue rho point z vertices q, by
    intro element vertices
    funext q
    change extendValue rho point z (fun index => element.val * vertices index) q =
      rho element.val (extendValue rho point z vertices (element.val⁻¹ • q))
    by_cases h : ∃ γ : rationalLevel, γ.val • point = element.val⁻¹ • q
    · obtain ⟨γ, hγ⟩ := h
      have hq : (element * γ).val • point = q := by
        change (element.val * γ.val) • point = q
        rw [mul_smul, hγ, smul_inv_smul]
      rw [extendValue_eq rho point z _ (element * γ) hq, extendValue_eq rho point z _ γ hγ,
        ← Module.End.mul_apply, ← map_mul]
      congr 2
      exact congrArg z.val (funext fun index => by
        change (element.val * γ.val)⁻¹ * (element.val * vertices index) =
          γ.val⁻¹ * vertices index
        group)
    · have hq : ¬ ∃ γ : rationalLevel, γ.val • point = q := by
        rintro ⟨γ, hγ⟩
        exact h ⟨element⁻¹ * γ, by
          change (element.val⁻¹ * γ.val) • point = element.val⁻¹ • q
          rw [mul_smul, hγ]⟩
      rw [extendValue_of_not_mem rho point z _ hq, extendValue_of_not_mem rho point z _ h,
        map_zero]⟩
  map_add' z w := by
    apply Subtype.ext
    funext vertices q
    classical
    change extendValue rho point (z + w) vertices q =
      extendValue rho point z vertices q + extendValue rho point w vertices q
    unfold extendValue
    split_ifs
    · change rho _ (z.val _ + w.val _) = _
      rw [map_add]
    · rw [add_zero]
  map_smul' a z := by
    apply Subtype.ext
    funext vertices q
    classical
    change extendValue rho point (a • z) vertices q = a • extendValue rho point z vertices q
    unfold extendValue
    split_ifs
    · change rho _ (a • z.val _) = _
      rw [map_smul]
    · rw [smul_zero]

theorem extendCochain_apply {k : ℕ} (z : cochains (fixedPointLevel rationalLevel point) rho k)
    (vertices : Fin (k + 1) → RationalGL3) (q : X) :
    (extendCochain rho point k z).val vertices q = extendValue rho point z vertices q := rfl

theorem extendCochain_differentialOne (u : cochains (fixedPointLevel rationalLevel point) rho 1) :
    extendCochain rho point 2 (differentialOne (fixedPointLevel rationalLevel point) rho u) =
      differentialOne rationalLevel (functionRepresentation rho X) (extendCochain rho point 1 u) := by
  apply Subtype.ext
  funext vertices q
  change extendValue rho point _ vertices q =
    extendValue rho point u ![vertices 1, vertices 2] q -
      extendValue rho point u ![vertices 0, vertices 2] q +
      extendValue rho point u ![vertices 0, vertices 1] q
  by_cases h : ∃ γ : rationalLevel, γ.val • point = q
  · obtain ⟨γ, hγ⟩ := h
    rw [extendValue_eq rho point _ _ γ hγ, extendValue_eq rho point _ _ γ hγ,
      extendValue_eq rho point _ _ γ hγ, extendValue_eq rho point _ _ γ hγ,
      ← map_sub, ← map_add]
    congr 1
    change u.val ![γ.val⁻¹ * vertices 1, γ.val⁻¹ * vertices 2] -
        u.val ![γ.val⁻¹ * vertices 0, γ.val⁻¹ * vertices 2] +
        u.val ![γ.val⁻¹ * vertices 0, γ.val⁻¹ * vertices 1] = _
    simp only [LocalHecke.translate_pair]
  · rw [extendValue_of_not_mem rho point _ _ h, extendValue_of_not_mem rho point _ _ h,
      extendValue_of_not_mem rho point _ _ h, extendValue_of_not_mem rho point _ _ h]
    simp

theorem extendCochain_cocycle (z : cocycles (fixedPointLevel rationalLevel point) rho) :
    extendCochain rho point 2 z.val ∈ cocycles rationalLevel (functionRepresentation rho X) := by
  funext vertices q
  change extendValue rho point z.val ![vertices 1, vertices 2, vertices 3] q -
      extendValue rho point z.val ![vertices 0, vertices 2, vertices 3] q +
      extendValue rho point z.val ![vertices 0, vertices 1, vertices 3] q -
      extendValue rho point z.val ![vertices 0, vertices 1, vertices 2] q = 0
  by_cases h : ∃ γ : rationalLevel, γ.val • point = q
  · obtain ⟨γ, hγ⟩ := h
    rw [extendValue_eq rho point _ _ γ hγ, extendValue_eq rho point _ _ γ hγ,
      extendValue_eq rho point _ _ γ hγ, extendValue_eq rho point _ _ γ hγ,
      ← map_sub, ← map_add, ← map_sub]
    have hzero := congrFun z.property (fun index => γ.val⁻¹ * vertices index)
    change z.val.val ![γ.val⁻¹ * vertices 1, γ.val⁻¹ * vertices 2, γ.val⁻¹ * vertices 3] -
        z.val.val ![γ.val⁻¹ * vertices 0, γ.val⁻¹ * vertices 2, γ.val⁻¹ * vertices 3] +
        z.val.val ![γ.val⁻¹ * vertices 0, γ.val⁻¹ * vertices 1, γ.val⁻¹ * vertices 3] -
        z.val.val ![γ.val⁻¹ * vertices 0, γ.val⁻¹ * vertices 1, γ.val⁻¹ * vertices 2] = 0 at hzero
    simp only [LocalHecke.translate_triple]
    rw [hzero, map_zero]
  · rw [extendValue_of_not_mem rho point _ _ h, extendValue_of_not_mem rho point _ _ h,
      extendValue_of_not_mem rho point _ _ h, extendValue_of_not_mem rho point _ _ h]
    simp

/-- Extension on cocycles. -/
def extendCycle :
    cocycles (fixedPointLevel rationalLevel point) rho →ₗ[ℂ]
      cocycles rationalLevel (functionRepresentation rho X) :=
  ((extendCochain rho point 2).comp (cocycles (fixedPointLevel rationalLevel point) rho).subtype).codRestrict
    _ (extendCochain_cocycle rho point)

/-- Extension on cohomology. -/
def extendH2 :
    H2 (fixedPointLevel rationalLevel point) rho →ₗ[ℂ]
      H2 rationalLevel (functionRepresentation rho X) :=
  (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel point) rho)).mapQ
    (LinearMap.range (boundaryMap rationalLevel (functionRepresentation rho X)))
    (extendCycle rho point) (by
      rintro cycle ⟨u, rfl⟩
      refine ⟨extendCochain rho point 1 u, ?_⟩
      apply Subtype.ext
      exact (extendCochain_differentialOne rho point u).symm)

/-- The Shapiro coordinate at the point of the extension is the original class. -/
theorem fixedPointH2_extendH2 (y : H2 (fixedPointLevel rationalLevel point) rho) :
    fixedPointH2 rationalLevel rho point (extendH2 rho point y) = y := by
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
  change fixedPointH2 rationalLevel rho point
      (classOf rationalLevel (functionRepresentation rho X) (extendCycle rho point z)) =
    classOf (fixedPointLevel rationalLevel point) rho z
  rw [fixedPointH2_classOf]
  apply congrArg
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change extendValue rho point z.val vertices point = z.val.val vertices
  rw [extendValue_eq rho point z.val vertices 1 (by simp)]
  simp

/-- Off the orbit, the Shapiro coordinate of the extension vanishes. -/
theorem fixedPointH2_extendH2_of_not_mem (y : H2 (fixedPointLevel rationalLevel point) rho)
    {other : X} (hother : ¬ ∃ γ : rationalLevel, γ.val • point = other) :
    fixedPointH2 rationalLevel rho other (extendH2 rho point y) = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
  change fixedPointH2 rationalLevel rho other
      (classOf rationalLevel (functionRepresentation rho X) (extendCycle rho point z)) = 0
  rw [fixedPointH2_classOf]
  have hzero : fixedPointCycle rationalLevel rho other (extendCycle rho point z) = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact extendValue_of_not_mem rho point z.val vertices hother
  rw [hzero, map_zero]

end Extension

/-! ### The four cusps -/

variable {n : ℕ}

theorem not_mem_orbit_of_ne (side : Side) (good : Bool) :
    ¬ ∃ γ : rationalLevel, γ.val • cuspFlag side good = cuspFlag side (!good) := by
  rintro ⟨γ, hγ⟩
  have h1 := cuspFlag_good_iff side good
  have h2 := cuspFlag_good_iff side (!good)
  rw [← hγ, TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers.goodFlag_rationalLevel_smul_iff] at h2
  cases good <;> simp_all

/-- The class supported at one cusp with prescribed local coordinate. -/
def cuspLift (n : ℕ) (χ : RankOneCharacter) (side : Side) (good : Bool) :
    CuspH2 n χ side good →ₗ[ℂ] StratumH2 n χ side :=
  extendH2 (rationalCoefficientComponent n χ) (cuspFlag side good)

theorem cuspRes_cuspLift {χ : RankOneCharacter} (side : Side) (good : Bool)
    (y : CuspH2 n χ side good) : cuspRes n χ side good (cuspLift n χ side good y) = y :=
  fixedPointH2_extendH2 _ _ y

theorem cuspRes_not_cuspLift {χ : RankOneCharacter} (side : Side) (good : Bool)
    (y : CuspH2 n χ side good) : cuspRes n χ side (!good) (cuspLift n χ side good y) = 0 :=
  fixedPointH2_extendH2_of_not_mem _ _ y (not_mem_orbit_of_ne side good)

/-! ### Necessity of the four local statements -/

theorem embedSide_zero {χ : RankOneCharacter} (side : Side) :
    embedSide (n := n) (χ := χ) side 0 = 0 := by
  cases side <;> rfl

theorem associatePair_le_jointGenEigenspace (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    associatePair D ≤ jointGenEigenspace D hecke (pairCharacter D hecke hhecke) := by
  intro y hy
  simp only [jointGenEigenspace, Submodule.mem_iInf, Subtype.forall]
  intro t ht
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact pairCharacter_spec D hecke hhecke t ht y hy

/-- Under separation (and a nonzero associate pair) the joint generalized eigenspace of the pair
character is contained in the associate pair. -/
theorem jointGenEigenspace_le_of_eigenSeparated (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D))
    (hne : associatePair D ≠ ⊥) :
    jointGenEigenspace D hecke (pairCharacter D hecke hhecke) ≤ associatePair D := by
  have := BoundaryFiniteness.BoundaryDimension.boundary_finiteDimensional n D.chi
  rw [← Submodule.eq_of_le_of_finrank_le (associatePair_le_jointGenEigenspace D hecke hhecke)
    (finrank_le_of_eigenSeparated D hecke hhecke hsep hne)]

/-- A local joint generalized eigenclass, lifted to its cusp, is a joint generalized eigenvector of
the boundary. -/
theorem embedSide_cuspLift_mem (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (c : HeckeCorrespondence → ℂ) (side : Side)
    (good : Bool) {y : CuspH2 n D.chi side good} (hy : y ∈ localJoint n D.chi c side good) :
    embedSide side (cuspLift n D.chi side good y) ∈ jointGenEigenspace D hecke c := by
  simp only [jointGenEigenspace, Submodule.mem_iInf, Subtype.forall]
  intro t ht
  simp only [localJoint, Submodule.mem_iInf, Subtype.forall] at hy
  have hyt := hy t ht
  rw [Module.End.mem_maxGenEigenspace] at hyt ⊢
  obtain ⟨k, hk⟩ := hyt
  refine ⟨k, ?_⟩
  rw [pairHecke_pow_embedSide]
  have hzero : ((hecke side t - c t • 1) ^ k) (cuspLift n D.chi side good y) = 0 := by
    have hthis := cuspRes_hecke_sub_pow' hecke hhecke t ht side good (c t) k
      (cuspLift n D.chi side good y)
    have hother := cuspRes_hecke_sub_pow' hecke hhecke t ht side (!good) (c t) k
      (cuspLift n D.chi side good y)
    have h1 : cuspRes n D.chi side good
        (((hecke side t - c t • 1) ^ k) (cuspLift n D.chi side good y)) = 0 := by
      rw [hthis, cuspRes_cuspLift]
      exact hk
    have h2 : cuspRes n D.chi side (!good)
        (((hecke side t - c t • 1) ^ k) (cuspLift n D.chi side good y)) = 0 := by
      rw [hother, cuspRes_not_cuspLift, map_zero]
    cases good
    · exact (eq_zero_iff_cuspRes side _).mpr ⟨h2, h1⟩
    · exact (eq_zero_iff_cuspRes side _).mpr ⟨h1, h2⟩
  rw [hzero, embedSide_zero]

/-- **Necessity.** If the associate pair is nonzero and eigencharacter separated, then each local
joint generalized eigenclass at each cusp comes from the cuspidal summand, supported at that cusp. -/
theorem cusps_of_eigenSeparated (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D))
    (hne : associatePair D ≠ ⊥) (side : Side) (good : Bool)
    (y : CuspH2 n D.chi side good)
    (hy : y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good) :
    ∃ a ∈ boundarySummand D side,
      cuspRes n D.chi side good a = y ∧ cuspRes n D.chi side (!good) a = 0 := by
  refine ⟨cuspLift n D.chi side good y, ?_, cuspRes_cuspLift side good y,
    cuspRes_not_cuspLift side good y⟩
  exact mem_of_embedSide_mem D side _ (jointGenEigenspace_le_of_eigenSeparated D hecke hhecke
    hsep hne (embedSide_cuspLift_mem D hecke hhecke _ side good hy))

/-- **Separation forces local semisimplicity.** Under separation, every local away-from-three
Hecke operator acts on the local joint generalized eigenspace of the pair character by the scalar
`pairCharacter t`. -/
theorem localOp_eq_smul_of_eigenSeparated (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hsep : EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D))
    (hne : associatePair D ≠ ⊥) (side : Side) (good : Bool) (t : HeckeCorrespondence)
    (ht : AwayThree t) (y : CuspH2 n D.chi side good)
    (hy : y ∈ localJoint n D.chi (pairCharacter D hecke hhecke) side good) :
    localOp n D.chi t ht side good y = pairCharacter D hecke hhecke t • y := by
  obtain ⟨a, ha, hres, -⟩ := cusps_of_eigenSeparated D hecke hhecke hsep hne side good y hy
  have hpair : embedSide side a ∈ associatePair D := by
    cases side
    · exact ⟨ha, Submodule.zero_mem _⟩
    · exact ⟨Submodule.zero_mem _, ha⟩
  have heigen := pairCharacter_spec D hecke hhecke t ht _ hpair
  have hside : hecke side t a = pairCharacter D hecke hhecke t • a := by
    cases side
    · exact congrArg Prod.fst heigen
    · exact congrArg Prod.snd heigen
  rw [← hres, ← cuspRes_hecke hecke hhecke t ht, hside, map_smul]

end TernaryPeriodPolynomials.Spectral.CuspLift
