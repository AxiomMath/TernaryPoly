module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PsiPrimePairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.GeoBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.CoinvScalar
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SpanTransfer
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.PairingClass
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoPairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryH4

@[expose] public section


/-!
# The model pairing on the cone is a nonzero multiple of the library's geometric pairing

`facePairing_comparison`.  Let `Ω` be a degree-four chain of the model cone whose coinvariant class is a
cycle spanning the cycles modulo boundaries (the fundamental cycle of `coneR`).  Then there are a quasi-isomorphism
`Ψ' : coneR ⟶ boundaryChains` and a nonzero rational `κ`, independent of the coefficients, such that for every
representation `V` of `Γ(6)` and all degree-two cocycles `b : C_2 ⟶ V`, `a : C_2 ⟶ V^*` of the singular chains of the
boundary cover, the model pairing `ev ∘ (Ψ'^*b ⊗ Ψ'^*a) ∘ Δ_{2,2}(Ω)` (the cochain `b` on the front face) equals
`κ · geoPairing V [a] [b]`, the Poincaré-duality pairing of the library's boundary `∂M` (`Comparison.GeoPairing`).

Ingredients: the cap homotopy compatibility `exists_PsiPrime_pairing`, the passage from `Ω` to the lift `ω_f` of a
cycle representing the ordinary fundamental class (`CoinvScalar`), the transfer of the spanning property along the
homotopy equivalence `Ψ'` (`span_transfer`), the identification of `geoPairing` with the invariant functional
`pairFun` (`GeoBridge`, via `ordinaryCap_eq_absolute`, `cap_bridge` and the Kronecker evaluation of `KroneckerRep`),
and `compactFundamentalClass_ne_zero` for `κ ≠ 0`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SingularLocalCap TernaryPoly.SingularLocalCap.Descent
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalDuality TernaryPoly.SingularLocalCompactCap
  TernaryPoly.SingularLocalCompactCap.Algebra TernaryPoly.CompactOrdinaryCap TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.SymmetricSpaceBoundaryOrientation
  TernaryPoly.HalfSpaceBoundaryOrientation TernaryPoly.RelativeCapConnecting
  TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.CoinvScalar
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.SymmetricSpaceBoundaryFull
  TernaryPoly.EquivariantSingularResolution TernaryPoly.RationalManifoldCompact

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

theorem chainClass_eq_zero_of_boundary (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (x : Homology.Cycles (K.sc' (n+1) n (n-1))) (τ : K.X (n+1)) (h : (K.d (n+1) n).hom τ = x.val) :
    chainClass K n x = 0 := by
  unfold chainClass
  have h0 : Homology.cycleClass (K.sc' (n+1) n (n-1)) x = 0 := by
    have hmem : x ∈ Homology.Boundaries (K.sc' (n+1) n (n-1)) := ⟨τ, Subtype.ext h⟩
    have hq0 : (Homology.Boundaries (K.sc' (n+1) n (n-1))).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hmem
    change (K.sc' (n+1) n (n-1)).moduleCatHomologyIso.inv.hom
      ((Homology.Boundaries (K.sc' (n+1) n (n-1))).mkQ x) = 0
    rw [hq0]
    exact map_zero _
  rw [h0, map_zero]

theorem facePairing_comparison (Ω : coneR.X 4)
    (hΩ : coinvD coneR 4 3 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) = 0)
    (hspan : ∀ z : (coneR.X 4).ρ.Coinvariants, coinvD coneR 4 3 z = 0 →
      ∃ c : ℚ, z - c • Representation.Coinvariants.mk (coneR.X 4).ρ Ω ∈ LinearMap.range (coinvD coneR 5 4)) :
    ∃ (Ψ : coneR ⟶ boundaryChains) (κ : ℚ), QuasiIso Ψ ∧ κ ≠ 0 ∧
      ∀ (V : Rep.{0} ℚ Γ6) (b : boundaryChains.X 2 ⟶ V) (hb : boundaryChains.d (2+1) 2 ≫ b = 0)
        (a : boundaryChains.X 2 ⟶ dualRepresentation V) (ha : boundaryChains.d (2+1) 2 ≫ a = 0),
        (evalRep V).hom (((Ψ.f 2 ≫ b) ⊗ₘ (Ψ.f 2 ≫ a)).hom ((modelDiagSystem.Δ 2 2 4 rfl).hom Ω)) =
          κ * geoPairingBoundary V
            (cochainClass _ 2 (cocycleOf boundaryProjection (dualRepresentation V) 2 a ha))
            (cochainClass _ 2 (cocycleOf boundaryProjection V 2 b hb)) := by
  obtain ⟨Ψ, hq, Hpair⟩ := exists_PsiPrime_pairing
  have h0 : ∀ n, Projective (resFlag.complex.X n) := fun n => resFlag.projective n
  have h00 : ∀ n, Projective ((resLine.complex ⊞ resPlane.complex).X n) := projective_middle
  have hp1 : ∀ n, Projective (coneR.X n) := fun n =>
    projectiveCone (signedArrow flagLineHom.hom flagPlaneHom.hom) n
  have hp2 : ∀ n, Projective (boundaryChains.X n) := fun n => chainRep_projective principalSix ambient n
  obtain ⟨e, he⟩ : ∃ e : _root_.HomotopyEquiv coneR boundaryChains, e.hom = Ψ :=
    (ChainComplex.quasiIso_iff_of_projective Ψ).mp hq
  set cls := homologyDegreeChange (scalarChains (TopCat.of BoundaryBase)) (2+2) (2+2) rfl
    (ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation) with hcls
  obtain ⟨c, hcc⟩ := chainClass_surjective (scalarChains (TopCat.of BoundaryBase)) (2+2) cls
  obtain ⟨ωf, hωf, hΦ⟩ := exists_coinvCycle_lift boundaryProjection boundaryQuotientCovering 3 c.val c.property
  have hωf' : coinvD boundaryChains 4 3 (Representation.Coinvariants.mk (boundaryChains.X 4).ρ ωf) = 0 :=
    (isCoinvCycle_iff_mk_d boundaryChains ωf).1 hωf
  obtain ⟨cc, hcc'⟩ := span_transfer e (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) hspan _ hωf'
  have hcoinv : coinvF e.hom 4 (Representation.Coinvariants.mk (coneR.X 4).ρ Ω) =
      Representation.Coinvariants.mk (boundaryChains.X 4).ρ ((Ψ.f 4).hom Ω) := by
    rw [← he]; rfl
  rw [hcoinv] at hcc'
  have hcc0 : cc ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero] at hcc'
    obtain ⟨τ, hτ⟩ := pushforward_sub_smul_boundary_four boundaryProjection boundaryQuotientCovering ωf 0 0
      (by rw [zero_smul, sub_zero]; exact hcc')
    rw [zero_smul, sub_zero, hΦ] at hτ
    have hz : chainClass (scalarChains (TopCat.of BoundaryBase)) (2+2) c = 0 :=
      chainClass_eq_zero_of_boundary _ _ c τ hτ
    rw [hcc, hcls] at hz
    have hord : ordinaryFundamentalClass 2 boundaryEuclidean boundaryOrientation = 0 := by
      simpa [homologyDegreeChange] using hz
    have hproj := ordinaryFundamentalClass_projection (B := TopCat.of BoundaryBase) 2 boundaryEuclidean
      boundaryOrientation
    rw [hord, map_zero] at hproj
    exact compactFundamentalClass_ne_zero 2 boundaryEuclidean boundaryOrientation Set.univ isCompact_univ
      Set.univ_nonempty hproj.symm
  refine ⟨Ψ, cc⁻¹, hq, inv_ne_zero hcc0, fun V b hb a ha => ?_⟩
  have hmodel := Hpair (evalRep V) b hb a ha Ω ((isCoinvCycle_iff_mk_d coneR Ω).2 hΩ)
  have hgeo := geoPairing_eq_pairFun boundaryProjection V boundaryEuclidean boundaryOrientation b hb a ha ωf c
    hΦ.symm hcc
  have hrel := pairFun_eq_of_mem_range boundaryDiagSystem (evalRep V) b hb a ha ωf ((Ψ.f 4).hom Ω) cc hcc'
  have hgeo' : geoPairingBoundary V
      (cochainClass _ 2 (cocycleOf boundaryProjection (dualRepresentation V) 2 a ha))
      (cochainClass _ 2 (cocycleOf boundaryProjection V 2 b hb)) =
      (pairFun boundaryDiagSystem (evalRep V) b a).hom ωf := hgeo
  rw [hgeo', hrel, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcc0, one_mul]
  exact hmodel




end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
