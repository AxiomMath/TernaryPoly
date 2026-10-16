module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge3a
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneQuot
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ExactLevel

@[expose] public section


/-!
# The good-plane edge map is an injection into `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`

Sol's Hochschild–Serre edge `splitCohomologyEdge` of the split extension
`1 → ℤ² → Λ → Γ₁'(3) × ℤˣ → 1` (`GoodPlaneModel`) is defined on all of `H²(Λ, V)` since every class
restricts to zero on the radical (`GoodPlaneRestriction`), and it is injective because the Levi
group embeds in `GL₂(ℤ) × ℤˣ` (`ModularH2.splitCohomologyEdge_injective_of_binary`). Composing with
the coordinate `Sym^{n+1}(δ) ∘ upperRadicalH1Coordinate` and restricting to `Γ₁'(3)` (the factor
`ℤˣ` acts trivially) gives the linear map

`goodPlaneEdge : H²(Γ_F, V) → H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`

defined on the local cohomology at the good-plane cusp (`CuspReduction.CuspH2`); it is injective
(`goodPlaneEdge_injective`), and on a class represented by a relative two-cocycle `c` it is the
class of `goodPlaneEdgeCocycle c` (`goodPlaneEdgeH2_apply`). With `ExactLevel` this bounds the
dimension of the local cohomology (`finrank_goodPlane_le`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel CuspH2)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3a
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot
open TernaryPeriodPolynomials.LevelThree.GoodPlaneRestriction
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

variable (n : ℕ)

/-! ### From Levi cocycles to crossed cocycles -/

/-- A cocycle of the Levi group with values in the radical cohomology gives a crossed cocycle of
`Γ₁'(3)` for `levelRep (n+1) (-1)`. -/
def T0 : groupCohomology.cocycles₁ (SplitRep n) →ₗ[ℂ] crossedCocycles (levelRep (n + 1) (-1)) where
  toFun z := ⟨fun m => Phi n (Jc n (z (m, 1))), by
    intro m m'
    have hz := (groupCohomology.mem_cocycles₁_iff z).mp z.2 (m, 1) (m', 1)
    have e : ((m * m' : binaryArithmeticLevel), (1 : ℤˣ)) = (m, 1) * (m', 1) :=
      Prod.ext rfl (mul_one (1 : ℤˣ)).symm
    change Phi n (Jc n (z (m * m', 1))) =
      Phi n (Jc n (z (m, 1))) + levelRep (n + 1) (-1) m (Phi n (Jc n (z (m', 1))))
    rw [e, hz, map_add, Jc_rho, map_add, levelRep_Phi]
    exact add_comm _ _⟩
  map_add' z z' := by
    apply Subtype.ext
    funext m
    change Phi n (Jc n ((z + z') (m, 1))) = _
    exact (congrArg (Phi n) (map_add (Jc n) (z (m, 1)) (z' (m, 1)))).trans (map_add (Phi n) _ _)
  map_smul' a z := by
    apply Subtype.ext
    funext m
    change Phi n (Jc n ((a • z) (m, 1))) = _
    exact (congrArg (Phi n) (map_smul (Jc n) a (z (m, 1)))).trans (map_smul (Phi n) a _)

theorem T0_apply (z : groupCohomology.cocycles₁ (SplitRep n)) (m : binaryArithmeticLevel) :
    (T0 n z).val m = Phi n (upperRadicalH1Coordinate n (z (m, 1))) := rfl

/-- If a Levi cocycle is a coboundary in `SplitRep n`, the crossed cocycle `T0` is a crossed
coboundary. -/
theorem T0_boundary (z z' : groupCohomology.cocycles₁ (SplitRep n))
    (h : (groupCohomology.H1π (SplitRep n)).hom (z - z') = 0) :
    T0 n z - T0 n z' ∈ crossedBoundaries (levelRep (n + 1) (-1)) := by
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff (z - z')).mp h
  refine ⟨Phi n (Jc n v), ?_⟩
  apply Subtype.ext
  funext m
  have hvm : (SplitRep n).ρ (m, 1) v - v = z (m, 1) - z' (m, 1) := congrFun hv (m, 1)
  change levelRep (n + 1) (-1) m (Phi n (Jc n v)) - Phi n (Jc n v) =
    Phi n (Jc n (z (m, 1))) - Phi n (Jc n (z' (m, 1)))
  calc levelRep (n + 1) (-1) m (Phi n (Jc n v)) - Phi n (Jc n v)
      = Phi n (Jc n ((SplitRep n).ρ (m, 1) v - v)) := by
        rw [map_sub, map_sub, Jc_rho, levelRep_Phi]
    _ = Phi n (Jc n (z (m, 1) - z' (m, 1))) := by rw [hvm]
    _ = Phi n (Jc n (z (m, 1))) - Phi n (Jc n (z' (m, 1))) := by rw [map_sub, map_sub]

/-- `T0` followed by the quotient map to `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def T1 := quotLin (levelRep (n + 1) (-1)) (T0 n)

theorem T1_apply (z : groupCohomology.cocycles₁ (SplitRep n)) :
    T1 n z = qcls (levelRep (n + 1) (-1)) (T0 n z) := rfl

theorem T1_fibers (z z' : groupCohomology.cocycles₁ (SplitRep n))
    (h : (groupCohomology.H1π (SplitRep n)).hom z = (groupCohomology.H1π (SplitRep n)).hom z') :
    T1 n z = T1 n z' := by
  have h0 : (groupCohomology.H1π (SplitRep n)).hom (z - z') = 0 :=
    (map_sub (groupCohomology.H1π (SplitRep n)).hom z z').trans (sub_eq_zero.mpr h)
  exact quotLin_eq (levelRep (n + 1) (-1)) (T0 n) z z' (T0_boundary n z z' h0)

/-- **Descent of `T0` to cohomology classes.** -/
def Tmap : groupCohomology.H1 (SplitRep n) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  surjectiveLinearDescent (groupCohomology.H1π (SplitRep n)).hom
    (oneCocycle_H1_surjective (SplitRep n)) (T1 n) (T1_fibers n)

theorem Tmap_apply (z : groupCohomology.cocycles₁ (SplitRep n)) :
    Tmap n (groupCohomology.H1π (SplitRep n) z) = qcls (levelRep (n + 1) (-1)) (T0 n z) :=
  surjectiveLinearDescent_apply (groupCohomology.H1π (SplitRep n)).hom
    (oneCocycle_H1_surjective (SplitRep n)) (T1 n) (T1_fibers n) z

/-! ### The ambient edge -/

variable {n}

/-- Every ambient two-cocycle gives a class in the kernel of the radical restriction. -/
def ambientEdgeKer (hn : 0 < n) :
    cocycles ΛG (IdentityPlaneCoordinate.ρn n) →ₗ[ℂ]
      (twoCohomologyRestriction goodPlaneExtension.inl (coefRep n)).ker :=
  ((groupCohomology.H2π (coefRep n)).hom.comp
    (ambientCocycleToGroup ΛG (IdentityPlaneCoordinate.ρn n))).codRestrict _
    (fun _ => LinearMap.mem_ker.mpr (goodPlaneH2_restriction_zero n hn _))

theorem ambientEdgeKer_val (hn : 0 < n) (C : cocycles ΛG (IdentityPlaneCoordinate.ρn n)) :
    (ambientEdgeKer hn C).val =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (IdentityPlaneCoordinate.ρn n) C) :=
  rfl

/-- The edge on ambient cocycles. -/
def edgeOnCocycles (hn : 0 < n) :
    cocycles ΛG (IdentityPlaneCoordinate.ρn n) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  (Tmap n).comp ((splitCohomologyEdge goodPlaneSplitting (coefRep n)).comp (ambientEdgeKer hn))

/-- **The good-plane edge on the ambient cohomology `H²(Λ, V)`.** -/
def goodPlaneEdgeH2 (hn : 0 < n) :
    H2 ΛG (IdentityPlaneCoordinate.ρn n) →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  (LinearMap.range (boundaryMap ΛG (IdentityPlaneCoordinate.ρn n))).liftQ (edgeOnCocycles hn) (by
    rintro _ ⟨P, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    have h0 : ambientEdgeKer hn (boundaryMap ΛG (IdentityPlaneCoordinate.ρn n) P) = 0 := by
      apply Subtype.ext
      exact ambientCocycle_H2_zero_of_primitive ΛG (IdentityPlaneCoordinate.ρn n)
        (boundaryMap ΛG (IdentityPlaneCoordinate.ρn n) P) P rfl
    change Tmap n (splitCohomologyEdge goodPlaneSplitting (coefRep n)
      (ambientEdgeKer hn (boundaryMap ΛG (IdentityPlaneCoordinate.ρn n) P))) = 0
    rw [h0, map_zero, map_zero])

theorem goodPlaneEdgeH2_classOf (hn : 0 < n) (C : cocycles ΛG (IdentityPlaneCoordinate.ρn n)) :
    goodPlaneEdgeH2 hn (classOf ΛG (IdentityPlaneCoordinate.ρn n) C) = edgeOnCocycles hn C := rfl

theorem T0_splitCocycleEdge (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n)) :
    T0 n (splitCocycleEdge goodPlaneSplitting (coefRep n) c) = goodPlaneEdgeCocycle c := by
  apply Subtype.ext
  funext m
  exact congrArg (fun x => Phi n x)
    (upperRadicalH1Coordinate_apply (degree := n)
      (splitEdgeCycle goodPlaneSplitting (coefRep n) (m, 1) c))

/-- **The edge of a class represented by a relative two-cocycle `c` is the class of its edge
cocycle.** -/
theorem goodPlaneEdgeH2_apply (hn : 0 < n) (C : cocycles ΛG (IdentityPlaneCoordinate.ρn n))
    (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (hc : groupCohomology.H2π (coefRep n) c.val =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (IdentityPlaneCoordinate.ρn n) C)) :
    goodPlaneEdgeH2 hn (classOf ΛG (IdentityPlaneCoordinate.ρn n) C) =
      qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle c) := by
  have hk : ambientEdgeKer hn C =
      relativeTwoCocycleClass goodPlaneExtension.inl (coefRep n) c :=
    Subtype.ext hc.symm
  rw [goodPlaneEdgeH2_classOf]
  change Tmap n (splitCohomologyEdge goodPlaneSplitting (coefRep n) (ambientEdgeKer hn C)) = _
  rw [hk, splitCohomologyEdge_apply, Tmap_apply, T0_splitCocycleEdge]

/-! ### Injectivity -/

/-- The Levi group embeds in `GL₂(ℤ) × ℤˣ`. -/
def leviEmbed : Levi →* GL (Fin 2) ℤ × ℤˣ := kap.prodMap (MonoidHom.id ℤˣ)

theorem leviEmbed_injective : Function.Injective leviEmbed := by
  intro a b h
  have h1' := congrArg Prod.fst h
  have h2' := congrArg Prod.snd h
  have h1 : kap a.1 = kap b.1 := h1'
  have h2 : a.2 = b.2 := h2'
  exact Prod.ext (kap_injective h1) h2

/-- If the edge cocycle is a crossed coboundary, the Levi edge class vanishes. -/
theorem edge_class_zero (c : relativeTwoCocycles goodPlaneExtension.inl (coefRep n))
    (h : qcls (levelRep (n + 1) (-1)) (goodPlaneEdgeCocycle c) = 0) :
    groupCohomology.H1π (SplitRep n) (splitCocycleEdge goodPlaneSplitting (coefRep n) c) = 0 := by
  rw [qcls_eq_zero_iff] at h
  obtain ⟨w, hw⟩ := h
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Binary.HomogeneousPoly (n + 1), Phi n w₀ = w :=
    ⟨PhiInv n w, Phi_PhiInv n w⟩
  have hedge : ∀ m : binaryArithmeticLevel, edgeVal c (m, 1) = Mk n m w₀ - w₀ := by
    intro m
    apply Phi_injective n
    have hm := congrFun (congrArg Subtype.val hw) m
    change levelRep (n + 1) (-1) m w - w = Phi n (edgeVal c (m, 1)) at hm
    rw [map_sub, ← levelRep_Phi, hw₀, ← hm]
  obtain ⟨y, hy⟩ : ∃ y : SplitRep n, Jc n y = w₀ :=
    ⟨(upperRadicalH1Coordinate n).symm w₀, (upperRadicalH1Coordinate n).apply_symm_apply w₀⟩
  rw [groupCohomology.H1π_eq_zero_iff]
  refine ⟨y, ?_⟩
  funext ℓ
  obtain ⟨m, d⟩ := ℓ
  apply (upperRadicalH1Coordinate n).injective
  have hJz : Jc n (splitCocycleEdge goodPlaneSplitting (coefRep n) c (m, d)) = edgeVal c (m, d) :=
    upperRadicalH1Coordinate_apply (degree := n)
      (splitEdgeCycle goodPlaneSplitting (coefRep n) (m, d) c)
  have hJd : Jc n ((SplitRep n).ρ (m, d) y - y) = Mk n m w₀ - w₀ := by
    rw [map_sub, Jc_rho, hy]
  exact hJd.trans (((edgeVal_unit_mul c m d).trans (hedge m)).symm.trans hJz.symm)

/-- **The good-plane edge is injective on `H²(Λ, V)`** (`n > 0`). -/
theorem goodPlaneEdgeH2_injective (hn : 0 < n) : Function.Injective (goodPlaneEdgeH2 hn) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  obtain ⟨c, hc⟩ := relativeTwoCocycleClass_surjective goodPlaneExtension.inl
    goodPlaneExtension.inl_injective (coefRep n) (ambientEdgeKer hn C)
  have hc' : groupCohomology.H2π (coefRep n) c.val =
      groupCohomology.H2π (coefRep n) (ambientCocycleToGroup ΛG (IdentityPlaneCoordinate.ρn n) C) :=
    congrArg Subtype.val hc
  change goodPlaneEdgeH2 hn (classOf ΛG (IdentityPlaneCoordinate.ρn n) C) = 0 at hx
  rw [goodPlaneEdgeH2_apply hn C c hc'] at hx
  have hz := edge_class_zero c hx
  have hinj := ModularH2.splitCohomologyEdge_injective_of_binary goodPlaneSplitting (coefRep n)
    leviEmbed leviEmbed_injective
  have hzero : relativeTwoCocycleClass goodPlaneExtension.inl (coefRep n) c = 0 := by
    apply hinj
    rw [map_zero, splitCohomologyEdge_apply]
    exact hz
  have hc0 : groupCohomology.H2π (coefRep n) c.val = 0 := congrArg Subtype.val hzero
  rw [hc0] at hc'
  change classOf ΛG (IdentityPlaneCoordinate.ρn n) C = 0
  exact (classOf_eq_zero_iff ΛG (IdentityPlaneCoordinate.ρn n) C).mpr
    ((ambientCocycle_H2_zero_iff ΛG (IdentityPlaneCoordinate.ρn n) C).mp hc'.symm)

/-! ### The edge on the local cohomology at the good-plane cusp -/

theorem hH_conj : ∀ h ∈ ΛG, gF * h * gF⁻¹ ∈ cuspLevel .plane true :=
  fun _ hh => (mem_ΛG _).mp hh

theorem hH'_conj : ∀ h ∈ cuspLevel .plane true, gF⁻¹ * h * gF⁻¹⁻¹ ∈ ΛG := by
  intro h hh
  rw [mem_ΛG]
  have e : gF * (gF⁻¹ * h * gF⁻¹⁻¹) * gF⁻¹ = h := by group
  rw [e]
  exact hh

/-- **Transport of the local cohomology at the good plane to the block coordinates.** -/
def psiG : CuspH2 n trivialCharacter .plane true ≃ₗ[ℂ] H2 ΛG (IdentityPlaneCoordinate.ρn n) :=
  GoodPlaneConj.conjH2Equiv (rationalCoefficientComponent n trivialCharacter) gF
    (cuspLevel .plane true) ΛG hH_conj hH'_conj

/-- **The edge map of the good-plane cusp** into `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def goodPlaneEdge (hn : 0 < n) :
    CuspH2 n trivialCharacter .plane true →ₗ[ℂ] CrossedH1 (levelRep (n + 1) (-1)) :=
  (goodPlaneEdgeH2 hn).comp (psiG (n := n)).toLinearMap

/-- **The good-plane edge map is injective.** -/
theorem goodPlaneEdge_injective (hn : 0 < n) : Function.Injective (goodPlaneEdge hn) :=
  (goodPlaneEdgeH2_injective hn).comp (psiG (n := n)).injective

/-- The local cohomology at the good plane is finite-dimensional. -/
theorem goodPlane_finiteDimensional (hn : 0 < n) :
    FiniteDimensional ℂ (CuspH2 n trivialCharacter .plane true) := by
  have : FiniteDimensional ℂ (CrossedH1 (levelRep (n + 1) (-1))) :=
    ParabolicBounds.level_H1_finiteDimensional (-1) (Nat.succ_pos n)
  exact Module.Finite.of_injective (goodPlaneEdge hn) (goodPlaneEdge_injective hn)

/-- **Dimension bound for the local cohomology at the good plane**:
`dim H²(Γ_F, V) ≤ ⌊(n + 3)/3⌋ + [n odd]`. -/
theorem finrank_goodPlane_le (hn : 0 < n) :
    Module.finrank ℂ (CuspH2 n trivialCharacter .plane true) ≤
      (n + 3) / 3 + (if Even n then 0 else 1) := by
  have : FiniteDimensional ℂ (CrossedH1 (levelRep (n + 1) (-1))) :=
    ParabolicBounds.level_H1_finiteDimensional (-1) (Nat.succ_pos n)
  have hle := LinearMap.finrank_le_finrank_of_injective (goodPlaneEdge_injective hn)
  have hex := ExactLevel.finrank_level_H1_eq (m := n + 1) (-1) (Nat.succ_pos n)
  have e1 : (-1 : ℤ) + ((n + 1 : ℕ) : ℤ) = n := by push_cast; ring
  have e2 : ¬ Even (-1 : ℤ) := by
    rw [Int.even_iff]
    norm_num
  have p1 : Even ((-1 : ℤ) + ((n + 1 : ℕ) : ℤ)) ↔ Even n := by
    rw [e1]
    exact Int.even_coe_nat n
  by_cases hne : Even n
  · have h1 : Even ((-1 : ℤ) + ((n + 1 : ℕ) : ℤ)) := p1.mpr hne
    rw [ite_eq_left h1, ite_eq_right e2] at hex
    rw [ite_eq_left hne]
    omega
  · have h1 : ¬ Even ((-1 : ℤ) + ((n + 1 : ℕ) : ℤ)) := fun h => hne (p1.mp h)
    rw [ite_eq_right h1, ite_eq_right e2] at hex
    rw [ite_eq_right hne]
    omega

end TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
