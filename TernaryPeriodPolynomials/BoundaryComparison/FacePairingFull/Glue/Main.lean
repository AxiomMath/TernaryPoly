module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.PlaneDict
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Aug
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Unique
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingCob
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FundamentalOmega
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TraceEvalV
public import TernaryPeriodPolynomials.Topology.TopHomology.CoinvariantCycle

@[expose] public section


/-!
# The model face pairings are nonzero multiples of the library's geometric pairing (up to the identification `Ψ`)

`facePairing_glue`.  There are a quasi-isomorphism `Ψ : coneR ⟶ boundaryChains` and a nonzero complex number `c`
such that, for the line pairing `facePairing n` (`⟨ , ⟩_Q`, `LineGlue`) and the plane pairing `Plane.facePairingP n`
(`⟨ , ⟩_P`, `PlaneGlue`, with the constant `-c`) on inner classes, every `ℚ`-linear functional `r : ℂ → ℚ` satisfies

`r (c⁻¹ * ⟨b, ξ⟩_Q) = geoPairingBoundary V [α] [β]`   and   `r ((-c)⁻¹ * ⟨ξ', b'⟩_P) = geoPairingBoundary V [α'] [β']`

whenever `β, α` (resp. `β', α'`) are boundary cocycles (singular chains of the boundary cover, with coefficients `V =
coeffRep ρ`, resp. its contragredient) whose `Ψ`-pullbacks are cohomologous to the cone cochains `(w, z, 0)`,
`(s^φ, y^φ, 0)` of lifts of the representatives (resp. `(-w, 0, z)`, `(-s^φ, 0, y^φ)`).  Such cocycles exist.
The constant is independent of the coefficient system, of `n`, of the classes and of `r`.  `V` is the complex module
`HomogeneousPoly n` viewed as a rational representation of `Γ(6)` and `r` transports the `ℂ`-valued model pairing to
the `ℚ`-valued Kronecker pairing with the full contragredient (`pairHom`, `pairHomP`).

Ingredients: `facePairing_comparison` (Rep-level cone pairing = `κ` times `geoPairingBoundary`), the dictionaries
`pair_lineLift`, `pair_planeLift` (Rep-level cone pairing of the lifts = `r` of the evaluation on the corner chain of
the model's boundary cup product), `traceValue_eq_evalCorner` for a spanning cycle, and the invariance of the cone
pairing under cohomologous cochains (`pair_cohomologous`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalDuality TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactCap.Algebra TernaryPoly.CompactOrdinaryCap TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.HalfSpaceBoundaryOrientation TernaryPoly.RelativeCapConnecting
  TernaryPoly.IntegralGL3Congruence
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.EquivariantSingularResolution TernaryPoly.RationalManifoldCompact
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.StabilizerVanishing (lineCupExact)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane
open TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.CoinvScalar

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

theorem exists_vertexPrimitive_line (n : ℕ) (z : MaximalCycles n trivialCharacter .line)
    (y : MaximalCycles n trivialCharacter .plane) :
    ∃ γ, VertexPrimitive (dualityData n trivialCharacter) z y γ :=
  lineCupExact (dualityData n trivialCharacter) z y

theorem exists_vertexPrimitive_plane (n : ℕ) (z : MaximalCycles n trivialCharacter .plane)
    (y : MaximalCycles n trivialCharacter .line) :
    ∃ γ, VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ :=
  planeCupExact_unconditionalP (dualityDataP n trivialCharacter) z y

attribute [local instance] Comparison.vertexAction

/-- `β` is a cochain of the boundary chains whose pullback along `Ψ` is cohomologous to the cone cochain `B`. -/
def PullsBackTo (Ψ : coneR ⟶ boundaryChains) {W : Rep.{0} ℚ Γ6} (β : boundaryChains.X 2 ⟶ W)
    (B : coneR.X 2 ⟶ W) : Prop :=
  ∃ η : coneR.X 1 ⟶ W, Ψ.f 2 ≫ β = B + coneR.d 2 1 ≫ η

/-- A quasi-isomorphism of complexes of projectives is a homotopy equivalence, so every cone cocycle is, up to a
coboundary, the pullback along `Ψ` of a cocycle of the boundary chains. -/
theorem exists_pullsBackTo {Ψ : coneR ⟶ boundaryChains} (hq : QuasiIso Ψ) {W : Rep.{0} ℚ Γ6}
    (B : coneR.X 2 ⟶ W) (hB : coneR.d 3 2 ≫ B = 0) :
    ∃ (β : boundaryChains.X 2 ⟶ W) (_ : boundaryChains.d (2 + 1) 2 ≫ β = 0), PullsBackTo Ψ β B := by
  have hp1 : ∀ n, Projective (coneR.X n) := coneR_projective
  have hp2 : ∀ n, Projective (boundaryChains.X n) := fun n => chainRep_projective principalSix ambient n
  obtain ⟨e, he⟩ : ∃ e : _root_.HomotopyEquiv coneR boundaryChains, e.hom = Ψ :=
    (ChainComplex.quasiIso_iff_of_projective Ψ).mp hq
  refine ⟨e.inv.f 2 ≫ B, ?_, ?_⟩
  · rw [← Category.assoc]
    have h := e.inv.comm 3 2
    rw [← h, Category.assoc, hB, comp_zero]
  · refine ⟨e.homotopyHomInvId.hom 1 2 ≫ B, ?_⟩
    have h := e.homotopyHomInvId.comm 2
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
    rw [← he]
    have h2 : (e.hom ≫ e.inv).f 2 = e.hom.f 2 ≫ e.inv.f 2 := rfl
    rw [← Category.assoc, ← h2, h]
    simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.id_f, Category.id_comp]
    have hB' : coneR.d (2 + 1) 2 ≫ B = 0 := hB
    rw [hB', comp_zero, add_zero, add_comm]

/-- A spanning coinvariant cycle of the model cone with all the properties used below. -/
theorem exists_spanning_cycle : ∃ Ω : coneR.X 4,
    coinvD coneR 4 3 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) = 0 ∧
    (∀ z : (coneR.X 4).ρ.Coinvariants, coinvD coneR 4 3 z = 0 →
      ∃ c : ℚ, z - c • Representation.Coinvariants.mk (coneR.X 4).ρ Ω ∈ LinearMap.range (coinvD coneR 5 4)) ∧
    (∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : coneR.X 4 ⟶ Rep.trivial ℚ Γ6 W),
      coneR.d 5 4 ≫ c = 0 →
      coinvHom (coneR.X 4) W c (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) = 0 →
      ∃ η : coneR.X 3 ⟶ Rep.trivial ℚ Γ6 W, c = coneR.d 4 3 ≫ η) := by
  obtain ⟨ω, hω0, hspan, hspan'⟩ := exists_fundamental_cycle coneR coneR_H4
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ ω
  exact ⟨v, hω0, hspan, hspan'⟩

/-- The value, in `ℚ`, of the geometric pairing of the classes of two cocycles of the boundary chains. -/
abbrev geoOf (V : Rep.{0} ℚ Γ6) (α : boundaryChains.X 2 ⟶ dualRepresentation V)
    (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0) (β : boundaryChains.X 2 ⟶ V)
    (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0) : ℚ :=
  geoPairingBoundary V
    (cochainClass _ 2 (cocycleOf boundaryProjection (dualRepresentation V) 2 α hα))
    (cochainClass _ 2 (cocycleOf boundaryProjection V 2 β hβ))

/-- **Line glue.**  For every inner line class `b`, inner plane class `ξ` with lifts `(z, w)`, `(y, s)`, and every
`ℚ`-linear `r : ℂ → ℚ`: `r (c⁻¹ ⟨b, ξ⟩_Q)` is the geometric pairing of any boundary cocycles pulling back along `Ψ` to
the cone lifts `(w, z, 0)`, `(s^φ, y^φ, 0)`; such cocycles exist. -/
def LineGlue (Ψ : coneR ⟶ boundaryChains) (c : ℂ) : Prop :=
  ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane) (s : EdgeCochains n trivialCharacter 1),
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val →
    EdgePrimitive z w →
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val →
    (∀ x e, y.val.val x (endpoint .plane e) = differentialOneRaw s.val x e) →
    (∃ (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
        (_ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
        (α : boundaryChains.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))
        (_ : boundaryChains.d (2 + 1) 2 ≫ α = 0),
        PullsBackTo Ψ β (lineLiftB z w) ∧
        PullsBackTo Ψ α (lineLiftA (dualityData n trivialCharacter) r y s)) ∧
    ∀ (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
      (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
      (α : boundaryChains.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))
      (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0),
      PullsBackTo Ψ β (lineLiftB z w) →
      PullsBackTo Ψ α (lineLiftA (dualityData n trivialCharacter) r y s) →
      r (c⁻¹ * facePairing n b ξ) = geoOf _ α hα β hβ

/-- **Plane glue** (the plane-supported twin). -/
def PlaneGlue (Ψ : coneR ⟶ boundaryChains) (c : ℂ) : Prop :=
  ∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane) (b : innerClasses n .line)
    (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .line) (s : EdgeCochains n trivialCharacter 1),
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = ξ.val →
    EdgePrimitiveP z w →
    classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) y = b.val →
    (∀ x e, y.val.val x (endpoint .line e) = differentialOneRaw s.val x e) →
    (∃ (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
        (_ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
        (α : boundaryChains.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))
        (_ : boundaryChains.d (2 + 1) 2 ≫ α = 0),
        PullsBackTo Ψ β (planeLiftB z w) ∧
        PullsBackTo Ψ α (planeLiftA (dualityDataP n trivialCharacter) r y s)) ∧
    ∀ (β : boundaryChains.X 2 ⟶ coeffRep (rationalCoefficientComponent n trivialCharacter))
      (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
      (α : boundaryChains.X 2 ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n trivialCharacter)))
      (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0),
      PullsBackTo Ψ β (planeLiftB z w) →
      PullsBackTo Ψ α (planeLiftA (dualityDataP n trivialCharacter) r y s) →
      r (c⁻¹ * facePairingP n ξ b) = geoOf _ α hα β hβ

/-- The Rep-level cone pairing of two cone cocycles which pull back along `Ψ` to cohomologous boundary cocycles is `κ`
times the geometric pairing of these boundary cocycles (the conclusion of `facePairing_comparison_aug`, in the form used
for the glue). -/
def PairGeo (Ψ : coneR ⟶ boundaryChains) (Ω : coneR.X 4) (κ : ℚ) : Prop :=
  ∀ {V : Rep.{0} ℚ Γ6} (B : coneR.X 2 ⟶ V) (A : coneR.X 2 ⟶ dualRepresentation V)
    (β : boundaryChains.X 2 ⟶ V) (hβ : boundaryChains.d (2 + 1) 2 ≫ β = 0)
    (α : boundaryChains.X 2 ⟶ dualRepresentation V) (hα : boundaryChains.d (2 + 1) 2 ≫ α = 0),
    coneR.d 3 2 ≫ A = 0 → PullsBackTo Ψ β B → PullsBackTo Ψ α A →
    (evalRep V).hom ((B ⊗ₘ A).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom Ω)) = κ * geoOf V α hα β hβ

/-- A spanning coinvariant cycle `Ω` of the model cone, with a comparison `Ψ` over the augmentation, the constants
`κ` of the comparison of the cone pairing with the geometric pairing and `c₀` of the comparison of the model trace with
the evaluation on the corner chain of `Ω`. -/
theorem exists_pairGeo : ∃ (Ω : coneR.X 4) (Ψ : coneR ⟶ boundaryChains) (κ : ℚ) (c₀ : ℂ),
    IsCoinvCycle Ω ∧ IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ κ ≠ 0 ∧ c₀ ≠ 0 ∧ PairGeo Ψ Ω κ ∧
    ∀ f : closedEdgeCochains rationalLevel, levelTrace f = c₀ * evalOmega (cornerChain Ω) f.1 := by
  obtain ⟨Ω, hΩ, hspan, hspan'⟩ := exists_spanning_cycle
  obtain ⟨Ψ, κ, hcar, hq, haug, hκ, Hcomp⟩ := facePairing_comparison_aug Ω hΩ hspan
  obtain ⟨c₀, hc₀, htr⟩ := levelTrace_eq_evalCorner Ω hspan'
  have hcyc : IsCoinvCycle Ω := (isCoinvCycle_iff_mk_d coneR Ω).2 hΩ
  refine ⟨Ω, Ψ, κ, c₀, hcyc, hcar, hq, haug, hκ, hc₀, ?_, htr⟩
  intro V B A β hβ α hα hA ⟨η, hη⟩ ⟨η', hη'⟩
  have hA' : coneR.d 3 2 ≫ (Ψ.f 2 ≫ α) = 0 := chainMap_cocycle Ψ α hα
  have hB : coneR.d 3 2 ≫ B = 0 := by
    have h := chainMap_cocycle Ψ β hβ
    rw [hη, Preadditive.comp_add, ← Category.assoc, coneR.d_comp_d, zero_comp, add_zero] at h
    exact h
  have h1 := pair_cohomologous modelDiagSystem (evalRep V) hB hA' η hη η' hη' Ω hcyc
  have h2 := Hcomp V β hβ α hα
  exact h1.symm.trans h2

/-- The line and plane glue for the constant `κ c₀` of any comparison data of `exists_pairGeo`. -/
theorem glue_of_pairGeo {Ω : coneR.X 4} {Ψ : coneR ⟶ boundaryChains} {κ : ℚ} {c₀ : ℂ}
    (hcyc : IsCoinvCycle Ω) (hq : QuasiIso Ψ) (hκ : κ ≠ 0) (hc₀ : c₀ ≠ 0) (pairGeo : PairGeo Ψ Ω κ)
    (htr : ∀ f : closedEdgeCochains rationalLevel, levelTrace f = c₀ * evalOmega (cornerChain Ω) f.1) :
    LineGlue Ψ ((κ : ℂ) * c₀) ∧ PlaneGlue Ψ (-((κ : ℂ) * c₀)) := by
  have hκ' : (κ : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hκ
  refine ⟨?_, ?_⟩
  · unfold LineGlue
    intro n r b ξ z w y s hz hw hy hs
    have hex : ∃ γ, VertexPrimitive (dualityData n trivialCharacter) z y γ := exists_vertexPrimitive_line n z y
    obtain ⟨γ, hγ⟩ := hex
    have hB := lineLiftB_cocycle hw
    have hA := lineLiftA_cocycle (dualityData n trivialCharacter) r hs
    refine ⟨?_, ?_⟩
    · obtain ⟨β, hβ, hPB⟩ := exists_pullsBackTo hq _ hB
      obtain ⟨α, hα, hPA⟩ := exists_pullsBackTo hq _ hA
      exact ⟨β, hβ, α, hα, hPB, hPA⟩
    · intro β hβ α hα hPB hPA
      have hfp : facePairing n b ξ = traceValue z w y := facePairing_apply_eq hz hw hy
      have htv : traceValue z w y = c₀ * evalOmega (cornerChain Ω)
          (boundaryValue (dualityData n trivialCharacter) w y γ) := by
        rw [← trace_boundaryValue_eq_traceValue hγ]
        exact htr ⟨boundaryValue (dualityData n trivialCharacter) w y γ, boundaryValue_mem_closed _ hw hγ⟩
      have hpair := pair_lineLift (dualityData n trivialCharacter) r Ω hcyc z w y s γ hγ
      have hG := pairGeo _ _ β hβ α hα hA hPB hPA
      rw [hpair] at hG
      rw [hfp, htv]
      have e1 : ((κ : ℂ) * c₀)⁻¹ * (c₀ * evalOmega (cornerChain Ω)
          (boundaryValue (dualityData n trivialCharacter) w y γ)) =
          ((κ⁻¹ : ℚ) : ℂ) * evalOmega (cornerChain Ω) (boundaryValue (dualityData n trivialCharacter) w y γ) := by
        push_cast
        field_simp
      rw [e1, ← Rat.smul_def, map_smul, hG, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
  · unfold PlaneGlue
    intro n r ξ b z w y s hz hw hy hs
    have hex : ∃ γ, VertexPrimitiveP (dualityDataP n trivialCharacter) z y γ := exists_vertexPrimitive_plane n z y
    obtain ⟨γ, hγ⟩ := hex
    have hB := planeLiftB_cocycle hw
    have hA := planeLiftA_cocycle (dualityDataP n trivialCharacter) r hs
    refine ⟨?_, ?_⟩
    · obtain ⟨β, hβ, hPB⟩ := exists_pullsBackTo hq _ hB
      obtain ⟨α, hα, hPA⟩ := exists_pullsBackTo hq _ hA
      exact ⟨β, hβ, α, hα, hPB, hPA⟩
    · intro β hβ α hα hPB hPA
      have hfp : facePairingP n ξ b = traceValueP z w y := facePairing_apply_eqP hz hw hy
      have htv : traceValueP z w y = c₀ * evalOmega (cornerChain Ω)
          (boundaryValueP (dualityDataP n trivialCharacter) w y γ) := by
        rw [← trace_boundaryValue_eq_traceValueP hγ]
        exact htr ⟨boundaryValueP (dualityDataP n trivialCharacter) w y γ, boundaryValueP_mem_closed _ hw hγ⟩
      have hpair := pair_planeLift (dualityDataP n trivialCharacter) r Ω hcyc z w hw y s hs γ hγ
      have hG := pairGeo _ _ β hβ α hα hA hPB hPA
      rw [hpair] at hG
      rw [hfp, htv]
      have e1 : (-((κ : ℂ) * c₀))⁻¹ * (c₀ * evalOmega (cornerChain Ω)
          (boundaryValueP (dualityDataP n trivialCharacter) w y γ)) =
          ((-κ⁻¹ : ℚ) : ℂ) * evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w y γ) := by
        push_cast
        field_simp
      rw [e1, ← Rat.smul_def, map_smul, smul_eq_mul]
      have hr : r (evalOmega (cornerChain Ω) (boundaryValueP (dualityDataP n trivialCharacter) w y γ)) =
          -(κ * geoOf _ α hα β hβ) := by
        rw [← hG, neg_neg]
      rw [hr]
      field_simp

/-- The face-wise glue, with the extra information that the comparison `Ψ` is `u ≫ faceConeToBoundary` for a carried
`u` (`IsCarriedPsi`), so that it is canonical (`CanonFull`). -/
theorem facePairing_glue_carried : ∃ (Ψ : coneR ⟶ boundaryChains) (c : ℂ), IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧
    Ψ ≫ augB = augR ∧ c ≠ 0 ∧ LineGlue Ψ c ∧ PlaneGlue Ψ (-c) := by
  obtain ⟨Ω, Ψ, κ, c₀, hcyc, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩ := exists_pairGeo
  exact ⟨Ψ, (κ : ℂ) * c₀, hcar, hq, haug, mul_ne_zero (Rat.cast_ne_zero.2 hκ) hc₀,
    (glue_of_pairGeo hcyc hq hκ hc₀ pairGeo htr).1, (glue_of_pairGeo hcyc hq hκ hc₀ pairGeo htr).2⟩

theorem facePairing_glue : ∃ (Ψ : coneR ⟶ boundaryChains) (c : ℂ), QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ c ≠ 0 ∧
    LineGlue Ψ c ∧ PlaneGlue Ψ (-c) := by
  obtain ⟨Ψ, c, -, hq, haug, hc, hL, hP⟩ := facePairing_glue_carried
  exact ⟨Ψ, c, hq, haug, hc, hL, hP⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
