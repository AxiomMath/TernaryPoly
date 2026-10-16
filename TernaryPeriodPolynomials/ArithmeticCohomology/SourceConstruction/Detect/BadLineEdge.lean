module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineModel

@[expose] public section


/-!
# The edge of a cup cocycle at the bad line

Let `ΛB = {R(x, ±1, A) : x ∈ ℤ², A ∈ Γ₁'(3)}` be the stabilizer of the bad line `ℤ e₁` in the
arithmetic level group.  A degree-two cocycle `C` of `ΛB` whose values on the vertex triples
`(1, g, g h)` are the cup product `(l (g h) - l g) (a g - a 1)` of two potentials
`a : GL₃(ℚ) → Sym^{n+1}` and `l : GL₃(ℚ) → Hom(Sym^{n+1}, V)` is a relative cocycle
(`a` does not see the radical `Ux`).  If the radical potential satisfies the cocycle law
`l (Ux v · g) = lam v + ρ(Ux v) ∘ l g` along the radical lattice with
`lam v Q = lineRadical (u(v₁, v₂)) Q`, then the mixed (edge) cochain of `C` at the Levi element
`Lm A` is the linear cocycle of the Euler pair of `δ_A = a (Lm A) - a 1` plus a radical
coboundary (`bd_edge_value`), hence the Hochschild–Serre coordinate of `C` at `A` is
`(n + 1) δ_A` (`bd_classOf_ne_zero`).  So `C` is not a coboundary as soon as
`A ↦ δ_A` has nonzero class in `H¹(Γ₁'(3), Sym^{n+1})` (`bd_classOf_ne_zero_of_cup`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (ambientCocycleToGroup ambientCocycleToGroup_apply)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (ivmul ivmul_inv_cancel)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Ux Lm Lm_Ux)
open TernaryPeriodPolynomials.LevelThree.BadLineEdge (Aρ R1 edgeB)
open TernaryPeriodPolynomials.LevelThree.BadLineHecke (LPA)
open TernaryPeriodPolynomials.LevelThree.BadLinePairs (LP)
open TernaryPeriodPolynomials.LevelThree.BadLineModel
  (wc eAz eAz_val wedge_of_pair semidirect_eq_model modelCycle leviMap_repr localToModel_eq)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
  (badLineLocalRadicalKernel badLineLeviMap localToModel)

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-! ## The radical cocycle and the Euler pair of a binary form -/

/-- The radical cocycle on the lattice `ℤ²`: `lam v = lineRadical (u(v₁, v₂))`. -/
def bdLam (n : ℕ) (v : ℤ × ℤ) : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n :=
  lineRadical n trivialCharacter (dlUnipotent (v.1 : ℝ) (v.2 : ℝ))

/-- The partial derivative of a binary form, as a binary form of degree one less. -/
def bdD (i : Fin 2) (δ : Binary.HomogeneousPoly (n + 1)) : Binary.HomogeneousPoly n :=
  ⟨pderiv i δ.val, by
    have h : δ.val.IsHomogeneous (n + 1) := (MvPolynomial.mem_homogeneousSubmodule _ _).mp δ.2
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by simpa using h.pderiv (i := i))⟩

/-- The pair `(-∂₁ δ, ∂₀ δ)`, the Euler pair of `(n + 1) δ`. -/
def bdPair (δ : Binary.HomogeneousPoly (n + 1)) :
    Binary.HomogeneousPoly n × Binary.HomogeneousPoly n :=
  (-(bdD 1 δ), bdD 0 δ)

/-- The wedge coordinate of the pair `(-∂₁ δ, ∂₀ δ)` is `(n + 1) δ` (Euler's identity). -/
theorem bdPair_wedge (δ : Binary.HomogeneousPoly (n + 1)) :
    binaryPairWedge n (bdPair δ) = ((n + 1 : ℕ) : ℂ) • δ := by
  apply Subtype.ext
  have h : δ.val.IsHomogeneous (n + 1) := (MvPolynomial.mem_homogeneousSubmodule _ _).mp δ.2
  have euler := h.sum_X_mul_pderiv
  have scalarEuler : X 0 * pderiv 0 δ.val + X 1 * pderiv 1 δ.val =
      ((n + 1 : ℕ) : ℂ) • δ.val := by
    simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using euler
  change X 0 * pderiv 0 δ.val - X 1 * (-pderiv 1 δ.val) = ((n + 1 : ℕ) : ℂ) • δ.val
  rw [mul_neg, sub_neg_eq_add]
  exact scalarEuler

/-- The coefficientwise formula of the linear cocycle `LP` of a pair. -/
theorem coe_LP (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    ((LP n P v : HomogeneousPoly n) : Poly) =
      (v.1 : ℂ) • MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) P.1.val +
        (v.2 : ℂ) • MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) P.2.val := by
  rfl

/-- **The radical cocycle at the lattice point `v` is the linear cocycle of the Euler pair.** -/
theorem bdLam_eq_LP (v : ℤ × ℤ) (δ : Binary.HomogeneousPoly (n + 1)) :
    bdLam n v δ = LP n (bdPair δ) v := by
  apply Subtype.ext
  have h : ((bdLam n v δ : HomogeneousPoly n) : Poly) =
      MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        (C (algebraMap ℝ ℂ (v.2 : ℝ)) * pderiv (0 : Fin 2) (δ : Binary.Poly) -
          C (algebraMap ℝ ℂ (v.1 : ℝ)) * pderiv (1 : Fin 2) (δ : Binary.Poly)) :=
    coe_lineRadical_unipotent n trivialCharacter (v.1 : ℝ) (v.2 : ℝ) δ
  rw [h, coe_LP]
  change _ = (v.1 : ℂ) • MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (-pderiv 1 δ.val) +
    (v.2 : ℂ) • MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (pderiv 0 δ.val)
  simp only [map_sub, map_mul, map_neg, MvPolynomial.smul_eq_C_mul,
    map_intCast]
  ring

/-! ## The edge value of a cup cocycle -/

/-- The relative-cocycle and potential hypotheses: a cocycle `C` of `ΛB` represents the cup
product of the potentials `a` and `l` on the vertex triples `(1, g, g h)`. -/
abbrev BadCupRepresents (n : ℕ) (C : cocycles ΛB (ρn n))
    (a : RationalGL3 → Binary.HomogeneousPoly (n + 1))
    (l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)) : Prop :=
  ∀ g h : ΛB, C.val.val ![1, g.val, g.val * h.val] =
    (l (g.val * h.val) - l g.val) (a g.val - a 1)

/-- The cocycle law of the radical potential along the radical lattice. -/
abbrev BadRadicalLaw (n : ℕ)
    (l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)) : Prop :=
  ∀ (v : ℤ × ℤ) (g : RationalGL3) (Q : Binary.HomogeneousPoly (n + 1)),
    l (((Ux v : ΛB) : RationalGL3) * g) Q =
      bdLam n v Q + ρn n ((Ux v : ΛB) : RationalGL3) (l g Q)

/-- The Levi potential does not see the radical lattice. -/
abbrev BadLeviRadical (n : ℕ) (a : RationalGL3 → Binary.HomogeneousPoly (n + 1)) : Prop :=
  ∀ v : ℤ × ℤ, a ((Ux v : ΛB) : RationalGL3) = a 1

/-- A ternary form as an element of the coefficient module of `ΛB`. -/
def bdAρ (n : ℕ) (x : HomogeneousPoly n) : Aρ (ρn n) := x

theorem bdAρ_add (x y : HomogeneousPoly n) : bdAρ n (x + y) = bdAρ n x + bdAρ n y := rfl

theorem bdAρ_sub (x y : HomogeneousPoly n) : bdAρ n (x - y) = bdAρ n x - bdAρ n y := rfl

theorem LPA_eq_bdAρ (P : Binary.HomogeneousPoly n × Binary.HomogeneousPoly n) (v : ℤ × ℤ) :
    LPA n P v = bdAρ n (LP n P v) := rfl

theorem R1_bdAρ (g : RationalGL3) (x : HomogeneousPoly n) :
    R1 (ρn n) g (bdAρ n x) = bdAρ n (ρn n g x) := rfl

theorem bd_relative {C : cocycles ΛB (ρn n)}
    {a : RationalGL3 → Binary.HomogeneousPoly (n + 1)}
    {l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)}
    (hrep : BadCupRepresents n C a l) (ha : BadLeviRadical n a) (x y : ℤ × ℤ) :
    ambientCocycleToGroup ΛB (ρn n) C (Ux x, Ux y) = 0 := by
  have hrep' : ∀ g h : ΛB, C.val.val ![1, g.val, g.val * h.val] =
      (l (g.val * h.val) - l g.val) (a g.val - a 1) := hrep
  have h : C.val.val ![1, ((Ux x : ΛB) : RationalGL3), ((Ux x : ΛB) : RationalGL3) *
      ((Ux y : ΛB) : RationalGL3)] = 0 := by
    rw [hrep', ha x, sub_self, map_zero]
  exact (ambientCocycleToGroup_apply ΛB (ρn n) C (Ux x) (Ux y)).trans h

/-- **The mixed (edge) cochain of a cup cocycle at the Levi element `Lm A`**: the linear cocycle of
the Euler pair of `δ_A = a (Lm A) - a 1` plus the radical coboundary of `l (Lm A) δ_A`. -/
theorem bd_edge_value {C : cocycles ΛB (ρn n)}
    {a : RationalGL3 → Binary.HomogeneousPoly (n + 1)}
    {l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n)}
    (hrep : BadCupRepresents n C a l) (ha : BadLeviRadical n a) (hl : BadRadicalLaw n l)
    (A : binaryArithmeticLevel) (v : ℤ × ℤ) :
    edgeB (ρn n) (ambientCocycleToGroup ΛB (ρn n) C) A v =
      LPA n (bdPair (a ((Lm A : ΛB) : RationalGL3) - a 1)) v +
        (R1 (ρn n) (Ux v)
            (bdAρ n (l ((Lm A : ΛB) : RationalGL3) (a ((Lm A : ΛB) : RationalGL3) - a 1))) -
          bdAρ n (l ((Lm A : ΛB) : RationalGL3) (a ((Lm A : ΛB) : RationalGL3) - a 1))) := by
  have hrep' : ∀ g h : ΛB, C.val.val ![1, g.val, g.val * h.val] =
      (l (g.val * h.val) - l g.val) (a g.val - a 1) := hrep
  have hLU' : Lm A * Ux (ivmul v A.val.val) = Ux v * Lm A := by
    rw [Lm_Ux, ivmul_inv_cancel]
  have hLU : ((Lm A : ΛB) : RationalGL3) * ((Ux (ivmul v A.val.val) : ΛB) : RationalGL3) =
      ((Ux v : ΛB) : RationalGL3) * ((Lm A : ΛB) : RationalGL3) :=
    congrArg Subtype.val hLU'
  have h1' : C.val.val ![1, ((Lm A : ΛB) : RationalGL3),
      ((Lm A : ΛB) : RationalGL3) * ((Ux (ivmul v A.val.val) : ΛB) : RationalGL3)] =
      (l (((Ux v : ΛB) : RationalGL3) * ((Lm A : ΛB) : RationalGL3)) -
          l ((Lm A : ΛB) : RationalGL3)) (a ((Lm A : ΛB) : RationalGL3) - a 1) := by
    rw [hrep', hLU]
  have h1 : ambientCocycleToGroup ΛB (ρn n) C (Lm A, Ux (ivmul v A.val.val)) =
      bdAρ n ((l (((Ux v : ΛB) : RationalGL3) * ((Lm A : ΛB) : RationalGL3)) -
          l ((Lm A : ΛB) : RationalGL3)) (a ((Lm A : ΛB) : RationalGL3) - a 1)) :=
    (ambientCocycleToGroup_apply ΛB (ρn n) C (Lm A) (Ux (ivmul v A.val.val))).trans h1'
  have h2' : C.val.val ![1, ((Ux v : ΛB) : RationalGL3),
      ((Ux v : ΛB) : RationalGL3) * ((Lm A : ΛB) : RationalGL3)] = 0 := by
    rw [hrep', ha v, sub_self, map_zero]
  have h2 : ambientCocycleToGroup ΛB (ρn n) C (Ux v, Lm A) = 0 :=
    (ambientCocycleToGroup_apply ΛB (ρn n) C (Ux v) (Lm A)).trans h2'
  unfold edgeB
  rw [h1, h2, sub_zero, LinearMap.sub_apply, hl v, bdLam_eq_LP, LPA_eq_bdAρ, R1_bdAρ,
    ← bdAρ_sub, ← bdAρ_add]
  exact congrArg (bdAρ n) (add_sub_assoc _ _ _)

/-! ## Nonvanishing of the class from the Levi coordinate -/

/-- **The class of a relative cocycle of `ΛB` whose Levi coordinates `(n + 1) δ_A` are not a
coboundary of `Γ₁'(3)` is nonzero.** -/
theorem bd_classOf_ne_zero (hn : 0 < n) (C : cocycles ΛB (ρn n))
    (δ : binaryArithmeticLevel → Binary.HomogeneousPoly (n + 1))
    (hrel : ∀ x y : ℤ × ℤ, ambientCocycleToGroup ΛB (ρn n) C (Ux x, Ux y) = 0)
    (hpair : ∀ A : binaryArithmeticLevel, ∃ S : Aρ (ρn n), ∀ v : ℤ × ℤ,
      edgeB (ρn n) (ambientCocycleToGroup ΛB (ρn n) C) A v =
        LPA n (bdPair (δ A)) v + (R1 (ρn n) (Ux v) S - S))
    (hδ : ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • δ A = binaryArithmeticRepresentation n A w - w) :
    classOf ΛB (ρn n) C ≠ 0 := by
  intro h0
  have hmodel : standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel).val :=
    (standardBadLineInhomogeneousH2Equiv_classOf n C).trans
      (congrArg (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (semidirect_eq_model n C))
  have hy : classOf ΛB (ρn n) C ∈ badLineLocalRadicalKernel n := by
    have h : standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) ∈
        LinearMap.ker (radicalRestrictionH2 integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)) := by
      rw [hmodel]
      exact radicalZeroH2ToFull_mem_ker integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)
        ((radicalZeroBoundaries integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)).mkQ
          (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel))
    exact h
  have hL := localToModel_eq n (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel)
    (classOf ΛB (ρn n) C) hy hmodel
  have hz : badLineLeviMap n hn (localToModel n ⟨classOf ΛB (ρn n) C, hy⟩) = 0 := by
    have hzero : (⟨classOf ΛB (ρn n) C, hy⟩ : badLineLocalRadicalKernel n) = 0 :=
      Subtype.ext h0
    rw [hzero, map_zero, map_zero]
  rw [hL, leviMap_repr n hn (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel)] at hz
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  apply hδ
  refine ⟨w, fun A => ?_⟩
  have h1 := congrFun (congrArg Subtype.val hw) A
  have h2 : (eAz n hn (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel)).val A =
      ((n + 1 : ℕ) : ℂ) • δ A := by
    obtain ⟨S, hS⟩ := hpair A
    rw [eAz_val]
    exact (wedge_of_pair n hn (ambientCocycleToGroup ΛB (ρn n) C) hrel A (bdPair (δ A)) S hS).trans
      (bdPair_wedge (δ A))
  exact h2.symm.trans (h1.symm.trans rfl)

/-- **A cocycle of `ΛB` representing the cup product of two potentials with the radical law is not
a coboundary** as soon as the Levi values `δ_A = a (Lm A) - a 1` have no common primitive
`w` with `(n + 1) δ_A = A w - w` on `Γ₁'(3)`. -/
theorem bd_classOf_ne_zero_of_cup (hn : 0 < n) (C : cocycles ΛB (ρn n))
    (a : RationalGL3 → Binary.HomogeneousPoly (n + 1))
    (l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n))
    (hrep : BadCupRepresents n C a l) (ha : BadLeviRadical n a) (hl : BadRadicalLaw n l)
    (hδ : ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (a ((Lm A : ΛB) : RationalGL3) - a 1) =
        binaryArithmeticRepresentation n A w - w) :
    classOf ΛB (ρn n) C ≠ 0 :=
  bd_classOf_ne_zero hn C (fun A => a ((Lm A : ΛB) : RationalGL3) - a 1)
    (fun x y => bd_relative hrep ha x y)
    (fun A => ⟨bdAρ n (l ((Lm A : ΛB) : RationalGL3) (a ((Lm A : ΛB) : RationalGL3) - a 1)),
      fun v => bd_edge_value hrep ha hl A v⟩) hδ

end TernaryPeriodPolynomials.SourceConstruction
