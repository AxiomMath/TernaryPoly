module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses
public import TernaryPeriodPolynomials.Topology.Rational.Relative.Connecting

@[expose] public section

noncomputable section
namespace TernaryPoly.HalfSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open ContractibleSingularHomology RationalRelativeSingular RationalLocalChartHomology
open RationalLocalOrientation

variable {X : Type} [TopologicalSpace X]

/-- Empty spaces have zero actual rational singular chains in every degree. -/
theorem empty_chains_isZero [IsEmpty X] : IsZero (chains X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro n
  apply Sigma.hom_ext
  intro σ
  exact False.elim (isEmptyElim
    ((TopCat.toSSetObjEquiv (TopCat.of X) _ σ) (Convexity.StdSimplex.single 0)))

/-- Absolute chains map to whole-support chains by the literal quotient projection. -/
abbrev absoluteSupportProjection : chains X ⟶ relativeChains (Set.univ : Set X)ᶜ :=
  cokernel.π (inclusion (Set.univ : Set X)ᶜ)

/-- The actual whole-support projection is an isomorphism, since the excluded subspace is empty. -/
instance absoluteSupportProjection_isIso : IsIso (absoluteSupportProjection (X := X)) := by
  let : IsEmpty ↥((Set.univ : Set X)ᶜ) := ⟨fun x => x.property (Set.mem_univ x.val)⟩
  have hz : inclusion ((Set.univ : Set X)ᶜ) = 0 :=
    (empty_chains_isZero (X := ↥((Set.univ : Set X)ᶜ))).eq_of_src _ _
  change IsIso (cokernel.π (inclusion ((Set.univ : Set X)ᶜ)))
  rw [hz]
  infer_instance

/-- The whole-support/absolute comparison retains the actual projection. -/
def absoluteSupportIso : chains X ≅ relativeChains (Set.univ : Set X)ᶜ :=
  asIso absoluteSupportProjection

/-- The literal absolute-to-point-relative projection. -/
abbrev absolutePointProjection (x : X) : chains X ⟶ localChains x :=
  cokernel.π (inclusion ({x}ᶜ : Set X))

/-- The whole-support projection followed by point restriction is the actual point projection. -/
theorem absoluteSupportProjection_point (x : X) :
    absoluteSupportProjection ≫ supportPointMap Set.univ x (Set.mem_univ x) =
      absolutePointProjection x := by
  simp [absoluteSupportProjection,supportPointMap,relativeMap,cokernel.map,
    RationalSingularAugmentation.chainMap]

/-- Every actual global class supplies its literal local homology family. -/
def globalGenerator (n : ℕ) (c : (chains X).homology n) (x : X) : (localChains x).homology n :=
  homologyMap (absolutePointProjection x) n c

/-- The local restrictions of any actual global class are genuinely locally represented. -/
theorem globalGenerator_locallyRepresented (n : ℕ) (c : (chains X).homology n) :
    LocallyRepresented n (globalGenerator n c) := by
  intro x
  refine ⟨⊤,Set.univ,Set.mem_univ x,Set.Subset.refl _,
    homologyMap absoluteSupportProjection n c,?_⟩
  intro y _ _
  change (homologyMap absoluteSupportProjection n ≫ homologyMap (supportPointMap Set.univ y _) n) c = _
  rw [← homologyMap_comp,absoluteSupportProjection_point]
  rfl

/-- Nonzero actual point restrictions equip a global class with its literal homological orientation. -/
def orientationOfGlobal (n : ℕ) (c : (chains X).homology n)
    (hc : ∀ x, globalGenerator n c x ≠ 0) : Orientation n X where
  generator := globalGenerator n c
  nonzero := hc
  locallyRepresented := globalGenerator_locallyRepresented n c

/-- The actual absolute/whole-support homology identification in every degree. -/
def absoluteSupportHomologyIso (n : ℕ) :
    (chains X).homology n ≅ (relativeChains (Set.univ : Set X)ᶜ).homology n :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso absoluteSupportIso

variable {H : Type} [TopologicalSpace H] [T2Space X] [CompactSpace X] [ChartedSpace H X]

/-- For the orientation defined by a global class, the compact whole-support fundamental class
is exactly its image under the actual quotient projection. -/
theorem compactFundamentalClass_eq_projection (n : ℕ)
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (c : (chains X).homology (n+2))
    (hc : ∀ x, globalGenerator (n+2) c x ≠ 0) :
    RationalManifoldCompact.compactFundamentalClass n e (orientationOfGlobal (n+2) c hc)
      Set.univ isCompact_univ = homologyMap absoluteSupportProjection (n+2) c := by
  symm
  apply RationalManifoldCompact.compactFundamentalClass_unique
  intro x _
  change (homologyMap absoluteSupportProjection (n+2) ≫
    homologyMap (supportPointMap Set.univ x _) (n+2)) c = _
  rw [← homologyMap_comp,absoluteSupportProjection_point]
  rfl

/-- The ordinary compact-manifold fundamental class through the literal inverse
absolute/whole-support identification. -/
def ordinaryFundamentalClass (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) : (chains X).homology (n+2) :=
  (absoluteSupportHomologyIso (n+2)).inv
    (RationalManifoldCompact.compactFundamentalClass n e o Set.univ isCompact_univ)

/-- The ordinary fundamental class of the literal global orientation is the original class. -/
theorem ordinaryFundamentalClass_orientationOfGlobal (n : ℕ)
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (c : (chains X).homology (n+2))
    (hc : ∀ x, globalGenerator (n+2) c x ≠ 0) :
    ordinaryFundamentalClass n e (orientationOfGlobal (n+2) c hc) = c := by
  unfold ordinaryFundamentalClass
  rw [compactFundamentalClass_eq_projection]
  exact (absoluteSupportHomologyIso (n+2)).toLinearEquiv.symm_apply_apply c

end TernaryPoly.HalfSpaceBoundaryOrientation
