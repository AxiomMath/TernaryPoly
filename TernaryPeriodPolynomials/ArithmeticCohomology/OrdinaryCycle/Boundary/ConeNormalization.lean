module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryConeActual
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeRepresentatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.Inflation

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology OrdinaryParabolicGroups
open OrdinaryBoundaryCommonRoot OrdinaryCovectors PolynomialGLAction
open LowDegreeHochschildSerre RadicalFirstCohomologyLattice

/-- The common-root parameter maps into the full P face exactly as it maps through B. -/
theorem commonRoot_plane_face (g : commonRoot) :
    planeEquiv (commonRootToPlane g) = BToP (commonRootToB g) := by
  apply Subtype.ext
  change planeLift (commonRootToPlane g) = g.val
  exact planeLift_commonRoot g

/-- The matching literal common-root inclusion in the full Q face. -/
theorem commonRoot_line_face (g : commonRoot) :
    lineEquiv (commonRootToLine g) = BToQ (commonRootToB g) := by
  apply Subtype.ext
  change lineLift (commonRootToLine g) = g.val
  exact lineLift_commonRoot g

/-- Under the two genuine radical-H1 vanishing premises, every actual cone cocycle has
radical-invariant face values and common-root-invariant corner after a genuine gauge change. -/
theorem actual_normalized_of_vanishing (n : ℕ) (e : ℤ)
    (hvanP : ∀ x : groupCohomology (radicalRep planeAction (Rep.of (planeCoefficients n e))) 1,
      (∀ q,(cohomologyRep planeAction (Rep.of (planeCoefficients n e)) 1).ρ q x=x) → x=0)
    (hvanQ : ∀ x : groupCohomology (radicalRep lineAction (Rep.of (lineCoefficients n e))) 1,
      (∀ q,(cohomologyRep lineAction (Rep.of (lineCoefficients n e)) 1).ρ q x=x) → x=0)
    (c : actualCycles n e) :
    ∃ v : Coefficients n × Coefficients n,
      (∀ r : planeRadical, (gauge (actualCoefficients n e) P Q c v).val.1
        (planeEquiv (SemidirectProduct.inl r)) = 0) ∧
      (∀ g : P, (gauge (actualCoefficients n e) P Q c v).val.1 g ∈
        Representation.invariants ((coefficientAction n e).comp planeRadical.subtype)) ∧
      (∀ r : lineRadical, (gauge (actualCoefficients n e) P Q c v).val.2.1
        (lineEquiv (SemidirectProduct.inl r)) = 0) ∧
      (∀ g : Q, (gauge (actualCoefficients n e) P Q c v).val.2.1 g ∈
        Representation.invariants ((coefficientAction n e).comp lineRadical.subtype)) ∧
      (gauge (actualCoefficients n e) P Q c v).val.2.2 ∈ (commonRepresentation n e).invariants := by
  let aP : cocycles₁ (Rep.of (planeParabolicCoefficients n e)) :=
    cycleP (actualCoefficients n e) P Q c
  let aQ : cocycles₁ (Rep.of (lineParabolicCoefficients n e)) :=
    cycleQ (actualCoefficients n e) P Q c
  obtain ⟨vP,hp0,hp⟩ := OrdinaryFaceInflation.plane_normalized n e hvanP aP
  obtain ⟨vQ,hq0,hq⟩ := OrdinaryFaceInflation.line_normalized n e hvanQ aQ
  refine ⟨(vP,vQ),hp0,hp,hq0,hq,?_⟩
  let d := gauge (actualCoefficients n e) P Q c (vP,vQ)
  have hP : ∀ g : commonRoot,d.val.1 (BToP (commonRootToB g)) = 0 := by
    intro g
    rw [← commonRoot_plane_face]
    exact hp0 ⟨g.val,commonRoot_le_planeRadical g.property⟩
  have hQ : ∀ g : commonRoot,d.val.2.1 (BToQ (commonRootToB g)) = 0 := by
    intro g
    rw [← commonRoot_line_face]
    exact hq0 ⟨g.val,commonRoot_le_lineRadical g.property⟩
  intro g
  have hc := ((actual_cycle_iff n e d.val).mp d.property).2.2 (commonRootToB g)
  change coefficientAction n e g.val d.val.2.2-d.val.2.2 =
    d.val.1 (BToP (commonRootToB g))-d.val.2.1 (BToQ (commonRootToB g)) at hc
  rw [hP,hQ,sub_self] at hc
  exact sub_eq_zero.mp hc

/-- Every actual cone H1 class has a representative whose distinguished face and corner
coefficients all have pairwise support, conditional only on the explicit actual vanishing gates. -/
theorem actual_class_pairwise_representative_of_vanishing (n : ℕ) (e : ℤ)
    (hvanP : ∀ x : groupCohomology (radicalRep planeAction (Rep.of (planeCoefficients n e))) 1,
      (∀ q,(cohomologyRep planeAction (Rep.of (planeCoefficients n e)) 1).ρ q x=x) → x=0)
    (hvanQ : ∀ x : groupCohomology (radicalRep lineAction (Rep.of (lineCoefficients n e))) 1,
      (∀ q,(cohomologyRep lineAction (Rep.of (lineCoefficients n e)) 1).ρ q x=x) → x=0)
    (x : actualH1 n e) :
    ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c = x ∧
      (∀ g : P, Pairwise (evaluation n (c.val.1 g) : Poly)) ∧
      (∀ g : Q, Pairwise (evaluation n (c.val.2.1 g) : Poly)) ∧
      Pairwise (evaluation n c.val.2.2 : Poly) := by
  have hs : ∃ c : actualCycles n e, classOf (actualCoefficients n e) P Q c = x :=
    classOf_surjective (actualCoefficients n e) P Q x
  obtain ⟨c,hc⟩ := hs
  obtain ⟨v,_hp0,hp,_hq0,hq,hu⟩ := actual_normalized_of_vanishing n e hvanP hvanQ c
  let d := gauge (actualCoefficients n e) P Q c v
  refine ⟨d,(classOf_gauge (actualCoefficients n e) P Q c v).trans hc,?_,?_,?_⟩
  · intro g
    apply invariant_evaluation_pairwise n e
    intro r
    exact hp g ⟨r.val,commonRoot_le_planeRadical r.property⟩
  · intro g
    apply invariant_evaluation_pairwise n e
    intro r
    exact hq g ⟨r.val,commonRoot_le_lineRadical r.property⟩
  · exact invariant_evaluation_pairwise n e d.val.2.2 hu

end TernaryPoly.OrdinaryBoundaryCone
