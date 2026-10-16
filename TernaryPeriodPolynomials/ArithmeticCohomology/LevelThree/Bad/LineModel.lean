module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineLocal

@[expose] public section


/-!
# The bad-line stabilizer cohomology in Sol's semidirect model

Relative two-cocycles `c` of `ΛB` (`c (Ux a, Ux b) = 0`) correspond to the radical-zero inhomogeneous
cycles `modelCycle c (a, b) = c (ψ a, ψ b)` of the split extension `ℤ² ⋊ (ℤˣ × Γ₁'(3))`
(`ψ = standardBadLineSemidirectEquiv`), on which Sol's Hochschild–Serre map to
`H¹(Γ₁'(3), Sym^{n+1})` is defined. This file identifies the mixed cochain of `modelCycle c` at the
Levi element `(1, A)` with `edgeB c A` (`mixedMap_val`), shows that every class of the radical
coordinates is represented by a linear cocycle plus a coboundary (`exists_pair`), computes the
coordinate of such a class (`wedge_of_pair`), and describes `badLineLeviMap` on a radical-zero cycle
(`leviMap_repr`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineModel

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineEdge BadLinePairs BadLineHecke BadLineLocal
open IdentityPlaneCoordinate
open AmbientHecke LocalHecke

variable (n : ℕ)

theorem cocycle_rearrange {M : Type*} [AddCommGroup M] {r y1 y2 y3 : M}
    (key : y1 + y3 = r + y2) : r - y1 + y2 - y3 = 0 := by
  have h : r - y1 + y2 - y3 = -(y1 + y3 - (r + y2)) := by abel
  rw [h, sub_eq_zero.mpr key, neg_zero]

theorem cocycle_rearrange' {M : Type*} [AddCommGroup M] {r y1 y2 y3 : M}
    (key : r - y1 + y2 - y3 = 0) : y1 + y3 = r + y2 := by
  have h : y1 + y3 - (r + y2) = -(r - y1 + y2 - y3) := by abel
  exact sub_eq_zero.mp (by rw [h, key, neg_zero])

/-- Sol's radical-zero cycles of the bad-line model. -/
abbrev RZ := radicalZeroTwoCycles integralBadLineSplitting.conjAct (standardBadLineRepresentation n)

theorem psi_inl_Ux (x : ℤ × ℤ) :
    ψ (SemidirectProduct.inl (Multiplicative.ofAdd x) : BadLineSemidirect) = Ux x := rfl

theorem psi_inr_Lm (A : binaryArithmeticLevel) :
    ψ (SemidirectProduct.inr ((1 : ℤˣ), A) : BadLineSemidirect) = Lm A := rfl

theorem rep_symm (g : ΛB) (v : HomogeneousPoly n) :
    standardBadLineRepresentation n (ψ.symm g) v = ρn n (g : RationalGL3) v := by
  change ρn n ((ψ (ψ.symm g) : ΛB) : RationalGL3) v = _
  rw [ψ.apply_symm_apply]

/-- The model cycle of a cocycle of `ΛB`. -/
def modelCycle (c : groupCohomology.cocycles₂ (Aρ (ρn n))) :
    inhomogeneousTwoCycles (standardBadLineRepresentation n) :=
  ⟨fun a b => c (ψ a, ψ b), by
    intro a b d
    have key := (groupCohomology.mem_cocycles₂_iff _).mp c.property (ψ a) (ψ b) (ψ d)
    simp only [map_mul]
    exact cocycle_rearrange key⟩

/-- The cocycle of `ΛB` of a model cycle. -/
def cocycleOfModel (z : inhomogeneousTwoCycles (standardBadLineRepresentation n)) :
    groupCohomology.cocycles₂ (Aρ (ρn n)) :=
  ⟨fun gh => z.val (ψ.symm gh.1) (ψ.symm gh.2), (groupCohomology.mem_cocycles₂_iff _).mpr (by
    intro g h k
    have key := z.property (ψ.symm g) (ψ.symm h) (ψ.symm k)
    rw [rep_symm] at key
    simp only [map_mul]
    exact cocycle_rearrange' key)⟩

theorem modelCycle_cocycleOfModel (z : inhomogeneousTwoCycles (standardBadLineRepresentation n)) :
    modelCycle n (cocycleOfModel n z) = z := by
  apply Subtype.ext
  funext a b
  change z.val (ψ.symm (ψ a)) (ψ.symm (ψ b)) = z.val a b
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem semidirect_eq_model (C : cocycles ΛB (ρn n)) :
    standardBadLineSemidirectCycle n C = modelCycle n (ambientCocycleToGroup ΛB (ρn n) C) := by
  apply Subtype.ext
  funext a b
  exact standardBadLineSemidirectCycle_apply n C a b

theorem modelCycle_rel (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hrel : ∀ a b, c (Ux a, Ux b) = 0) : modelCycle n c ∈ RZ n := by
  intro first second
  exact hrel first.toAdd second.toAdd

/-- The radical-zero cycle of a relative cocycle. -/
def wc (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (hrel : ∀ a b, c (Ux a, Ux b) = 0) : RZ n :=
  ⟨modelCycle n c, modelCycle_rel n c hrel⟩

theorem equiv_classOf_lift (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) :
    standardBadLineInhomogeneousH2Equiv n
        (classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c)) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (modelCycle n c) := by
  rw [standardBadLineInhomogeneousH2Equiv_classOf, semidirect_eq_model,
    ambientCocycleToGroup_lift]

theorem equiv_cohomologyAction (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (c : groupCohomology.cocycles₂ (Aρ (ρn n))) :
    standardBadLineInhomogeneousH2Equiv n
        (cohomologyAction (ρn n) (badLineCosets p hp3)
          (classOf ΛB (ρn n) (liftCocycle (badLineCosets p hp3) (ρn n) c))) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (modelCycle n (heckeTwo p hp3 (ρn n) c)) := by
  rw [cohomologyAction_classOf, standardBadLineInhomogeneousH2Equiv_classOf, semidirect_eq_model]
  rfl

/-! ### The mixed cochain -/

theorem conjAct_inv_one (A : binaryArithmeticLevel) (v : ℤ × ℤ) :
    integralBadLineSplitting.conjAct ((1 : ℤˣ), A)⁻¹ (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (ivmul v A.val.val) := by
  apply Multiplicative.toAdd.injective
  have h1 : (1 : ℤˣ).inv = 1 := rfl
  rw [integralBadLine_inverse_conjAct_coordinates]
  simp only [toAdd_ofAdd, ivmul, h1, one_mul]

theorem mixedMap_val (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hrel : ∀ a b, c (Ux a, Ux b) = 0) (A : binaryArithmeticLevel) (v : ℤ × ℤ) :
    (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
      ((1 : ℤˣ), A) (wc n c hrel)).val (Multiplicative.ofAdd v) = edgeB (ρn n) c A v := by
  change (modelCycle n c).val (SemidirectProduct.inr ((1 : ℤˣ), A))
      (SemidirectProduct.inl (integralBadLineSplitting.conjAct ((1 : ℤˣ), A)⁻¹
        (Multiplicative.ofAdd v))) -
    (modelCycle n c).val (SemidirectProduct.inl (Multiplicative.ofAdd v))
      (SemidirectProduct.inr ((1 : ℤˣ), A)) = _
  rw [conjAct_inv_one]
  change c (ψ (SemidirectProduct.inr ((1 : ℤˣ), A)), ψ (SemidirectProduct.inl
      (Multiplicative.ofAdd (ivmul v A.val.val)))) -
    c (ψ (SemidirectProduct.inl (Multiplicative.ofAdd v)), ψ (SemidirectProduct.inr ((1 : ℤˣ), A)))
    = _
  rw [psi_inr_Lm, psi_inl_Ux, psi_inl_Ux, edgeB]

/-! ### Pair representatives -/

theorem exists_pair (hn : 0 < n) (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hrel : ∀ a b, c (Ux a, Ux b) = 0) (A : binaryArithmeticLevel) :
    ∃ (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (S : Aρ (ρn n)),
      ∀ v : ℤ × ℤ, edgeB (ρn n) c A v = LPA n P v + (R1 (ρn n) (Ux v) S - S) := by
  obtain ⟨P, hP⟩ := standardRadicalH1_binaryPair_representative n hn
    ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
        ((1 : ℤˣ), A) (wc n c hrel)))
  obtain ⟨S₀, hS⟩ := (Submodule.Quotient.eq _).mp hP
  let S : Aρ (ρn n) := S₀
  refine ⟨P, -S, fun v => ?_⟩
  have h0 := congrFun (congrArg Subtype.val hS) (Multiplicative.ofAdd v)
  have h : R1 (ρn n) (Ux v) S - S = LPA n P v - edgeB (ρn n) c A v := by
    rw [← mixedMap_val n c hrel A v]
    exact h0
  have h2 : edgeB (ρn n) c A v = LPA n P v - (R1 (ρn n) (Ux v) S - S) := by
    rw [h]
    abel
  rw [h2, map_neg]
  abel

theorem wedge_of_pair (hn : 0 < n) (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hrel : ∀ a b, c (Ux a, Ux b) = 0) (A : binaryArithmeticLevel)
    (Q : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (S : Aρ (ρn n))
    (h : ∀ v : ℤ × ℤ, edgeB (ρn n) c A v = LPA n Q v + (R1 (ρn n) (Ux v) S - S)) :
    explicitRadicalBinaryEquiv n hn
      ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
          ((1 : ℤˣ), A) (wc n c hrel))) = binaryPairWedge n Q := by
  rw [← explicitBinaryPairCocycle_coordinate n hn Q]
  congr 1
  refine (Submodule.Quotient.eq _).mpr ⟨S, ?_⟩
  apply Subtype.ext
  funext r
  have hr := h (Multiplicative.toAdd r)
  rw [← mixedMap_val n c hrel A (Multiplicative.toAdd r)] at hr
  exact eq_sub_of_add_eq ((add_comm _ _).trans hr.symm)

/-! ### Sol's map on a radical-zero cycle -/

/-- The cocycle `A ↦ Φ[mixed cochain at (1, A)]` with values in `Sym^{n+1}`. -/
def eAz (hn : 0 < n) (z : RZ n) : crossedCocycles (binaryArithmeticRepresentation n) :=
  binaryLeviCrossedEquiv n
    (crossedRepresentationEqEquiv _ _ (explicitRadicalBinary_transport_eq n hn)
      (crossedCoefficientEquiv
        (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n))
        (explicitRadicalBinaryEquiv n hn) (mixedH1CocycleMap integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n) z)))

theorem eAz_val (hn : 0 < n) (z : RZ n) (A : binaryArithmeticLevel) :
    (eAz n hn z).val A = explicitRadicalBinaryEquiv n hn
      ((crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
          ((1 : ℤˣ), A) z)) := rfl

theorem leviMap_repr (hn : 0 < n) (z : RZ n) :
    badLineLeviMap n hn (radicalZeroH2ToKernel integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)
        ((radicalZeroBoundaries integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)).mkQ z)) =
      (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (eAz n hn z) := by
  change binaryLeviH1Equiv n (explicitBinaryMixedH1Equiv n hn (radicalKernelMixedMap
    integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
      (radicalZeroH2ToKernel integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
        ((radicalZeroBoundaries integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)).mkQ z)))) = _
  rw [radicalKernelMixedMap_representative]
  rfl

theorem localToModel_eq (z : RZ n) (x : H2 ΛB (ρn n)) (hxK : x ∈ badLineLocalRadicalKernel n)
    (hx : standardBadLineInhomogeneousH2Equiv n x =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ z.val) :
    localToModel n ⟨x, hxK⟩ = radicalZeroH2ToKernel integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n)
      ((radicalZeroBoundaries integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)).mkQ z) :=
  Subtype.ext hx

theorem binaryPairWedge_add (P Q : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) :
    binaryPairWedge n (P + Q) = binaryPairWedge n P + binaryPairWedge n Q := by
  apply Subtype.ext
  simp only [binaryPairWedge, Prod.fst_add, Prod.snd_add, Submodule.coe_add, mul_add]
  ring

/-- `binaryPairWedge` as an additive homomorphism. -/
def wedgeH : (Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) →+ Binary.HomogeneousPoly (n + 1) :=
  AddMonoidHom.mk' (binaryPairWedge n) (binaryPairWedge_add n)

end TernaryPeriodPolynomials.LevelThree.BadLineModel
