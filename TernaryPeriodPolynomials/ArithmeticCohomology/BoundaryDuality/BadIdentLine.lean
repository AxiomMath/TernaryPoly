module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree

@[expose] public section


/-!
# The Levi cocycle of the bad line is minus the edge image of the fiber class

Let `ζ` be the value at the bad line `L₀ = ⟨e₁⟩` of a line cocycle of the maximal stratum, a
homogeneous two-cocycle of the stabilizer `Λ_B` of `L₀` in the level, and `ω_U` an equivariant
primitive of `ζ` over the radical lattice `U`.  The relative representative
`c(g, h) = ω_U(g, g h) - ρ(g) ω_U(1, h)` of `ζ` vanishes on pairs of radical elements, and its mixed
(edge) cochain at the Levi element `k = diag(1, A)` is
`v ↦ c(k, u(v A⁻¹)) - c(u(v), k) = ρ(k) A(k)(1, u'')`, where `A(k) = k ⋆ ω_U - ω_U` is the Levi
cocycle and `u(v) k = k u''`.  The Levi identity of `ParabolicDualityIdentCore` gives
`edge(v) + A(k⁻¹)(1, u(v)) = (ρ(u(v)) - 1)(-w)` with `w = ρ(k) A(k)(1, k⁻¹)`.  Passing to the
explicit binary coordinate, which only depends on the class modulo the coboundaries, the crossed
cocycle of the Sol edge map `A ↦ Φ[edge_A]` is *exactly* minus the cocycle `badX`, `A ↦ Φ(A(k_A⁻¹))`,
of the level-three bridge.  Since the relative representative has the class of `ζ`, the class of
`badX` in `H¹(Γ₁'(3), Sym^{n+1})` is minus the image under `badLineEdge` of the Shapiro coordinate of
the line class at `L₀` (no transport: `L₀` is the bad-line reference cusp).

* `edge_add_levi_bad`: the Levi identity for the relative representative on `Λ_B`.
* `eAz_eq_neg_badX`: the cocycle of Sol's edge map is minus `badX`, exactly.
* `mkQ_badX_eq_neg_badLineEdge`: the class of `badX` is minus the bad-line edge of the class of `ζ`.
* `mkQ_badX_eq_neg_badLineEdge_cusp`: the same for the Shapiro coordinate of a maximal-stratum cocycle.
* `badX_mem_parabolicCrossed`: `badX` is parabolic for a local joint generalized eigenclass.
* `mkQ_badX_ne_zero`: its class is nonzero when the Shapiro coordinate at `L₀` is nonzero.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (ivmul)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB ψ)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Ux Lm)
open TernaryPeriodPolynomials.LevelThree.BadLineEdge (Aρ edgeB)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal (badLineLocalRadicalKernel)
open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge badLineEdge_injective)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains (leviCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (badLevi badLevi_mem_level badLevi_inv_normalizes badLevi_conj equiv_inl_val equiv_inr_val
    rhoS_radical zBad zBad_apply PhiBad PhiBad_eq uCocycle_leviCocycle_bad badX)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
  (cocycle_vec3 relCocycleOn relCocycleOn_apply relCocycleOn_vanish levi_identity)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

/-! ### The fiber data at the bad line -/

/-- The fiber hypotheses at the bad line `L₀` for the trivial character. -/
abbrev BadLineFiber (n : ℕ) (Λe : Subgroup RationalGL3)
    (ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) : Prop :=
  FiberHyp (rationalCoefficientComponent n trivialCharacter)
    (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
    (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU

/-- The stabilizer of the bad line `L₀` in the level is the arithmetic stabilizer `Λ_B`. -/
theorem levelStabilizer_L₀ : levelStabilizer L₀ = ΛB := rfl

/-- The Levi embedding lies in the arithmetic stabilizer of the bad line. -/
theorem badLevi_mem_ΛB (A : binaryArithmeticLevel) : badLevi A ∈ ΛB := badLevi_mem_level A

/-- The primitive `ω_U` is a primitive of the cocycle `C` when `ζ` is the underlying function. -/
theorem hd_of_fiber {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) :
    ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c] :=
  fun a b c => (hF.omegaU_d a b c).trans (hζ _)

/-! ### Radical and Levi elements of `Λ_B` as matrices -/

/-- The radical element `Ux x` of `Λ_B` is the lattice element `u(x)`. -/
theorem ux_val (x : ℤ × ℤ) :
    ((Ux x : ΛB) : RationalGL3) = latL0.hom (Multiplicative.ofAdd x) :=
  (congrArg Subtype.val (TernaryPeriodPolynomials.LevelThree.BadLineModel.psi_inl_Ux
    x)).symm.trans (equiv_inl_val (Multiplicative.ofAdd x))

/-- The Levi element `Lm A` of `Λ_B` is `diag(1, A)`. -/
theorem lm_val (A : binaryArithmeticLevel) : ((Lm A : ΛB) : RationalGL3) = badLevi A :=
  (congrArg Subtype.val (TernaryPeriodPolynomials.LevelThree.BadLineModel.psi_inr_Lm
    A)).symm.trans (equiv_inr_val A)

/-- The radical elements lie in the lattice `U`. -/
theorem ux_mem (x : ℤ × ℤ) : ((Ux x : ΛB) : RationalGL3) ∈ latL0.sub := by
  rw [ux_val]
  exact ⟨_, rfl⟩

/-- The Levi element normalizes the lattice `U`. -/
theorem badLevi_normalizes (A : binaryArithmeticLevel) :
    ∀ u ∈ latL0.sub, badLevi A * u * (badLevi A)⁻¹ ∈ latL0.sub := fun u hu => by
  simpa only [map_inv, inv_inv] using badLevi_inv_normalizes A⁻¹ u hu

/-- The conjugation relation `u(v) k = k u(v A⁻¹)` between the lattice and the Levi element. -/
theorem badLevi_conj_ux (A : binaryArithmeticLevel) (v : ℤ × ℤ) :
    latL0.hom (Multiplicative.ofAdd v) * badLevi A =
      badLevi A * latL0.hom (Multiplicative.ofAdd (ivmul v A.val.val)) := by
  have h := badLevi_conj A (Multiplicative.ofAdd v)
  rwa [TernaryPeriodPolynomials.LevelThree.BadLineModel.conjAct_inv_one] at h

/-! ### The relative representative on `Λ_B` -/

/-- **The relative representative vanishes on pairs of radical elements.** -/
theorem relCocycleOn_rel {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) (a b : ℤ × ℤ) :
    relCocycleOn ΛB (ρn n) ωU C (Ux a, Ux b) = 0 :=
  relCocycleOn_vanish ΛB (ρn n) ωU C (hd_of_fiber hF C hζ) hF.omegaU_eq (ux_mem a)

/-- The value of the relative representative on a pair, as a polynomial. -/
def relV {n : ℕ} (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n) (C : cocycles ΛB (ρn n))
    (g h : ΛB) : HomogeneousPoly n :=
  relCocycleOn ΛB (ρn n) ωU C (g, h)

/-- The value of the ambient cocycle of `Λ_B` on a pair, as a polynomial. -/
def ambV {n : ℕ} (C : cocycles ΛB (ρn n)) (g h : ΛB) : HomogeneousPoly n :=
  ambientCocycleToGroup ΛB (ρn n) C (g, h)

/-- The value of the mixed cochain of a two-cocycle of `Λ_B`, as a polynomial. -/
def edgeV {n : ℕ} (c : groupCohomology.cocycles₂ (Aρ (ρn n))) (A : binaryArithmeticLevel)
    (v : ℤ × ℤ) : HomogeneousPoly n :=
  edgeB (ρn n) c A v

/-- The value of the relative representative on a pair, in the form used for the model cycles. -/
theorem relCocycleOn_eq {n : ℕ} (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (C : cocycles ΛB (ρn n)) (g h : ΛB) :
    relV ωU C g h =
      ambV C g h - (ρn n g.val (ωU ![1, h.val]) - ωU ![1, g.val * h.val] + ωU ![1, g.val]) := rfl

/-- The semidirect representation at an element is the representation at its image in `Λ_B`. -/
theorem rep_psi (n : ℕ) (s : BadLineSemidirect) (v : HomogeneousPoly n) :
    standardBadLineRepresentation n s v = ρn n ((ψ s : ΛB) : RationalGL3) v := by
  have h := TernaryPeriodPolynomials.LevelThree.BadLineModel.rep_symm n (ψ s) v
  rwa [MulEquiv.symm_apply_apply] at h

/-- **The model cycle of the relative representative has the class of the model cycle of the
ambient cocycle**: they differ by the inhomogeneous boundary of `s ↦ -ω_U(1, ψ(s))`. -/
theorem modelCycle_relCocycleOn_class (n : ℕ)
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n) (C : cocycles ΛB (ρn n)) :
    (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.modelCycle n
          (relCocycleOn ΛB (ρn n) ωU C)) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.modelCycle n
          (ambientCocycleToGroup ΛB (ρn n) C)) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨fun s => -(ωU ![1, ((ψ s : ΛB) : RationalGL3)]), ?_⟩
  apply Subtype.ext
  funext s t
  change standardBadLineRepresentation n s (-(ωU ![1, ((ψ t : ΛB) : RationalGL3)])) -
      -(ωU ![1, ((ψ (s * t) : ΛB) : RationalGL3)]) + -(ωU ![1, ((ψ s : ΛB) : RationalGL3)]) =
    relV ωU C (ψ s) (ψ t) - ambV C (ψ s) (ψ t)
  rw [relCocycleOn_eq, rep_psi, map_mul ψ s t, map_neg]
  have e : ((ψ s * ψ t : ΛB) : RationalGL3) = ((ψ s : ΛB) : RationalGL3) * ((ψ t : ΛB) : RationalGL3) :=
    rfl
  rw [e]
  abel

/-- **The class of the cocycle `ζ` in the model**: it is represented by the radical-zero model cycle
of the relative representative. -/
theorem class_eq_model {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) :
    standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.wc n
          (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ)).val := by
  rw [standardBadLineInhomogeneousH2Equiv_classOf,
    TernaryPeriodPolynomials.LevelThree.BadLineModel.semidirect_eq_model]
  exact (modelCycle_relCocycleOn_class n ωU C).symm

/-- **The class of `ζ` has zero radical restriction**: it lies in the radical kernel of the bad
line. -/
theorem classOf_mem_kernel {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) :
    classOf ΛB (ρn n) C ∈ badLineLocalRadicalKernel n := by
  have hmem : standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) ∈
      LinearMap.ker (radicalRestrictionH2 integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)) := by
    rw [class_eq_model hF C hζ]
    exact radicalZeroH2ToFull_mem_ker integralBadLineSplitting.conjAct
      (standardBadLineRepresentation n)
      ((radicalZeroBoundaries integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)).mkQ
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.wc n
          (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ)))
  exact hmem

/-! ### The Levi identity on `Λ_B` -/

/-- **The Levi identity for the edge cochain of the relative representative.**  The mixed radical
value of the relative representative at the Levi element `diag(1, A)`, plus the Levi cocycle
`A(k⁻¹)(1, u(v))`, is the coboundary of `-w`. -/
theorem edge_add_levi_bad {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) (A : binaryArithmeticLevel) (v : ℤ × ℤ) :
    edgeV (relCocycleOn ΛB (ρn n) ωU C) A v +
        leviCocycle (ρn n) ωU (badLevi A)⁻¹ ![1, latL0.hom (Multiplicative.ofAdd v)] =
      ρn n (latL0.hom (Multiplicative.ofAdd v))
          (-(ρn n (badLevi A) (leviCocycle (ρn n) ωU (badLevi A) ![1, (badLevi A)⁻¹]))) -
        (-(ρn n (badLevi A) (leviCocycle (ρn n) ωU (badLevi A) ![1, (badLevi A)⁻¹]))) := by
  have hd := hd_of_fiber hF C hζ
  have key := levi_identity (ρn n) ωU C.val.val hd hF.omegaU_eq (k := badLevi A)
    (cocycle_vec3 ΛB (ρn n) C (badLevi_mem_ΛB A)) (badLevi_normalizes A)
    (u := latL0.hom (Multiplicative.ofAdd v))
    (u'' := latL0.hom (Multiplicative.ofAdd (ivmul v A.val.val))) ⟨_, rfl⟩ ⟨_, rfl⟩
    (badLevi_conj_ux A v)
  have e : edgeV (relCocycleOn ΛB (ρn n) ωU C) A v =
      (ωU ![((Lm A : ΛB) : RationalGL3), ((Lm A : ΛB) : RationalGL3) * ((Ux (ivmul v A.val.val) : ΛB) : RationalGL3)] -
        ρn n ((Lm A : ΛB) : RationalGL3) (ωU ![1, ((Ux (ivmul v A.val.val) : ΛB) : RationalGL3)])) -
      (ωU ![((Ux v : ΛB) : RationalGL3), ((Ux v : ΛB) : RationalGL3) * ((Lm A : ΛB) : RationalGL3)] -
        ρn n ((Ux v : ΛB) : RationalGL3) (ωU ![1, ((Lm A : ΛB) : RationalGL3)])) :=
    congrArg₂ (fun x y : HomogeneousPoly n => x - y)
      (relCocycleOn_apply ΛB (ρn n) ωU C hd (Lm A) (Ux (ivmul v A.val.val)))
      (relCocycleOn_apply ΛB (ρn n) ωU C hd (Ux v) (Lm A))
  rw [e, lm_val, ux_val v, ux_val (ivmul v A.val.val)]
  exact key

/-! ### The cocycle of Sol's edge map is minus `badX` -/

/-- **The inhomogeneous mixed cocycle of the relative representative is minus the crossed cocycle
of the Levi cocycle**, modulo the crossed boundaries of the radical. -/
theorem mixed_mkQ_eq_neg_zBad {n : ℕ} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) (A : binaryArithmeticLevel) :
    (crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
          ((1 : ℤˣ), A)
          (TernaryPeriodPolynomials.LevelThree.BadLineModel.wc n
            (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ))) =
      (crossedBoundaries ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
        (-(zBad n (uCocycle_leviCocycle_bad hF A).1)) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-(ρn n (badLevi A) (leviCocycle (ρn n) ωU (badLevi A) ![1, (badLevi A)⁻¹])), ?_⟩
  apply Subtype.ext
  funext r
  have hmix := TernaryPeriodPolynomials.LevelThree.BadLineModel.mixedMap_val n
    (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ) A r.toAdd
  rw [ofAdd_toAdd] at hmix
  have key := edge_add_levi_bad hF C hζ A r.toAdd
  rw [ofAdd_toAdd] at key
  change ((standardBadLineRepresentation n).comp SemidirectProduct.inl) r
      (-(ρn n (badLevi A) (leviCocycle (ρn n) ωU (badLevi A) ![1, (badLevi A)⁻¹]))) -
    -(ρn n (badLevi A) (leviCocycle (ρn n) ωU (badLevi A) ![1, (badLevi A)⁻¹])) =
    (mixedCrossedMap integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
        ((1 : ℤˣ), A)
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.wc n
          (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ))).val r -
      -((zBad n (uCocycle_leviCocycle_bad hF A).1).val r)
  rw [hmix, zBad_apply, rhoS_radical]
  exact key.symm.trans (sub_neg_eq_add _ _).symm

theorem equiv_map_neg {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℂ M] [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) (x : M) : e (-x) = -e x :=
  map_neg e x

/-- **The cocycle of Sol's edge map is minus the cocycle `badX` of the bridge**, exactly. -/
theorem eAz_eq_neg_badX {n : ℕ} (hn : 0 < n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) :
    TernaryPeriodPolynomials.LevelThree.BadLineModel.eAz n hn
        (TernaryPeriodPolynomials.LevelThree.BadLineModel.wc n
          (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ)) =
      -badX hn hF := by
  apply Subtype.ext
  funext A
  rw [TernaryPeriodPolynomials.LevelThree.BadLineModel.eAz_val,
    mixed_mkQ_eq_neg_zBad hF C hζ A, map_neg,
    equiv_map_neg (explicitRadicalBinaryEquiv n hn)]
  have h1 : (badX hn hF).val A = PhiBad n hn
      (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi A)⁻¹) := rfl
  rw [PhiBad_eq n hn (uCocycle_leviCocycle_bad hF A).1] at h1
  exact congrArg Neg.neg h1.symm

/-! ### The class of `badX` -/

/-- If `e = -b` in the crossed cocycles then the class of `b` is minus the class of `e`
(stated for an abstract representation so that no concrete carrier is unfolded). -/
theorem mkQ_eq_neg_of_eq_neg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (rep : Representation ℂ G V) (b e : crossedCocycles rep) (he : e = -b) :
    (crossedBoundaries rep).mkQ b = -(crossedBoundaries rep).mkQ e := by
  subst he
  rw [map_neg, neg_neg]

/-- **The class of `badX` is minus the bad-line edge of the class of the fiber cocycle.** -/
theorem mkQ_badX_eq_neg_badLineEdge {n : ℕ} (hn : 0 < n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU) (C : cocycles ΛB (ρn n))
    (hζ : ∀ x, ζ x = C.val.val x) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF) =
      -badLineEdge n hn ⟨classOf ΛB (ρn n) C, classOf_mem_kernel hF C hζ⟩ := by
  rw [TernaryPeriodPolynomials.LevelThree.BadLineFinal.levi_orig n hn
    (relCocycleOn ΛB (ρn n) ωU C) (relCocycleOn_rel hF C hζ) (classOf ΛB (ρn n) C)
    (classOf_mem_kernel hF C hζ) (class_eq_model hF C hζ)]
  exact mkQ_eq_neg_of_eq_neg _ _ _ (eAz_eq_neg_badX hn hF C hζ)

/-! ### From a cocycle of the maximal stratum to the cocycle of the bad line -/

/-- **The cocycle of the bad-line stabilizer** attached to a cocycle on the flags: its value at the
bad line `L₀`. -/
def cocycleAtBadLine (n : ℕ)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    cocycles ΛB (ρn n) :=
  fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter) (L₀ : Flags .line)
    cc

/-- The values of `cocycleAtBadLine`. -/
theorem cocycleAtBadLine_val (n : ℕ)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (x : Fin 3 → RationalGL3) : (cocycleAtBadLine n cc).val.val x = cc.val.val x L₀ := rfl

/-- The fiber cocycle `ζ`, given by the value of `cc` at `L₀`, is the underlying function of
`cocycleAtBadLine`. -/
theorem zeta_eq_cocycleAtBadLine (n : ℕ)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    {ζ : (Fin 3 → RationalGL3) → HomogeneousPoly n} (hζ : ∀ x, ζ x = cc.val.val x L₀) :
    ∀ x, ζ x = (cocycleAtBadLine n cc).val.val x := hζ

/-- **The Shapiro coordinate of a maximal-stratum class at the bad line** is the class of the
bad-line cocycle (no transport: `L₀` is the reference cusp). -/
theorem cuspRes_line_false_classOf (n : ℕ)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n trivialCharacter .line
        false (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) =
      classOf ΛB (ρn n) (cocycleAtBadLine n cc) := rfl

/-- **The class of `badX` is minus the bad-line edge of the Shapiro coordinate of the line class.**
Here `cc` is a cocycle of the maximal line stratum whose value at `L₀` is the fiber cocycle `ζ`. -/
theorem mkQ_badX_eq_neg_badLineEdge_cusp {n : ℕ} (hn : 0 < n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hζ : ∀ x, ζ x = cc.val.val x L₀) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF) =
      -badLineEdge n hn
        ⟨TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n
          trivialCharacter .line false (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc),
          classOf_mem_kernel hF (cocycleAtBadLine n cc) (zeta_eq_cocycleAtBadLine n cc hζ)⟩ :=
  mkQ_badX_eq_neg_badLineEdge hn hF (cocycleAtBadLine n cc) (zeta_eq_cocycleAtBadLine n cc hζ)

/-! ### Consequences -/

/-- **`badX` is a parabolic cocycle** when the Shapiro coordinate of the line class at `L₀` is a
local joint generalized eigenclass with `‖c(T₂) - 1‖ ≤ 3/4`. -/
theorem badX_mem_parabolicCrossed {n : ℕ} (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TernaryPeriodPolynomials.Spectral.TpExistence.tp
      TernaryPeriodPolynomials.Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hζ : ∀ x, ζ x = cc.val.val x L₀)
    (hy : TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n
        trivialCharacter .line false (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      TernaryPeriodPolynomials.Spectral.CuspReduction.localJoint n
        trivialCharacter c .line false) :
    badX (by omega : 0 < n) hF ∈
      ParabolicDuality.LevelThree.parabolicCrossed (binaryArithmeticRepresentation n) := by
  apply ParabolicDuality.LevelThree.mem_parabolicCrossed_of_mem
  rw [mkQ_badX_eq_neg_badLineEdge_cusp (by omega : 0 < n) hF cc hζ]
  exact Submodule.neg_mem _
    (ParabolicDuality.LevelThree.jointEdgeMap_mem_parabolicCrossedH1 n hn c hc ⟨_, hy⟩)

/-- **The class of `badX` is nonzero** when the Shapiro coordinate of the line class at `L₀` is
nonzero. -/
theorem mkQ_badX_ne_zero {n : ℕ} (hn : 0 < n) {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : BadLineFiber n Λe ζ η ω ωU θU)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hζ : ∀ x, ζ x = cc.val.val x L₀)
    (hne : TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n
        trivialCharacter .line false (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ≠ 0) :
    (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ (badX hn hF) ≠ 0 := by
  rw [mkQ_badX_eq_neg_badLineEdge_cusp hn hF cc hζ]
  refine neg_ne_zero.mpr (fun h => hne ?_)
  have h0 := badLineEdge_injective n hn (h.trans (map_zero (badLineEdge n hn)).symm)
  exact congrArg Subtype.val h0

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad

end
