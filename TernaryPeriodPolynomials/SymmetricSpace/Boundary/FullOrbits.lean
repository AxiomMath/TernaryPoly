module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullStabilizers

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open ModThreeGoodAction IntegralGL3Congruence
open OrdinaryIncidence SymmetricSpaceBoundaryFaces SymmetricSpaceBoundaryMV OrdinaryParabolicGroups

section Generic
variable {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) (a : X)

/-- Orbit equivalence under H is exactly the actual H\G/Stab(a) double-coset relation. -/
theorem orbit_doubleCoset_iff (g k : G) :
    (Quotient.mk (MulAction.orbitRel H X) (g • a) =
      Quotient.mk (MulAction.orbitRel H X) (k • a)) ↔
      DoubleCoset.setoid (H : Set G) (MulAction.stabilizer G a) g k := by
  rw [DoubleCoset.rel_iff]
  constructor
  · intro he
    obtain ⟨h,hh⟩ := Quotient.exact he.symm
    change h.val • (g • a) = k • a at hh
    rw [← mul_smul] at hh
    refine ⟨h.val,h.property,(h.val*g)⁻¹*k,?_,?_⟩
    · change ((h.val*g)⁻¹*k) • a = a
      rw [mul_smul,← hh,inv_smul_smul]
    · group
  · rintro ⟨h,hh,b,hb,rfl⟩
    apply Eq.symm
    apply Quotient.sound
    refine ⟨⟨h,hh⟩,?_⟩
    change h • (g • a) = (h*g*b) • a
    rw [mul_smul,show b • a = a from hb,mul_smul]

/-- Every actual double coset determines its full boundary-label orbit. -/
def doubleCosetToOrbit : DoubleCoset.Quotient (H : Set G) (MulAction.stabilizer G a) →
    MulAction.orbitRel.Quotient H X :=
  Quotient.lift (fun g => Quotient.mk _ (g • a))
    (fun g k h => (orbit_doubleCoset_iff H a g k).mpr h)

@[simp] theorem doubleCosetToOrbit_mk (g : G) :
    doubleCosetToOrbit H a (Quotient.mk _ g) = Quotient.mk _ (g • a) := rfl

def doubleCosetOrbitEquiv (ha : ∀ x : X, ∃ g : G, g • a = x) :
    DoubleCoset.Quotient (H : Set G) (MulAction.stabilizer G a) ≃
      MulAction.orbitRel.Quotient H X :=
  Equiv.ofBijective (doubleCosetToOrbit H a) ⟨by
    intro q r
    induction q using Quotient.inductionOn with | h g =>
    induction r using Quotient.inductionOn with | h k =>
    intro h
    exact Quotient.sound ((orbit_doubleCoset_iff H a g k).mp h),by
    intro q
    induction q using Quotient.inductionOn with | h x =>
    obtain ⟨g,rfl⟩ := ha x
    exact ⟨Quotient.mk _ g,rfl⟩⟩

/-- Stabilizers in each actual cover orbit are the restricted conjugate parabolics. -/
theorem cover_stabilizer_conjugate (g : G) :
    MulAction.stabilizer H (g • a) =
      ((MulAction.stabilizer G a).map (MulAut.conj g).toMonoidHom).comap H.subtype := by
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rfl

end Generic

/-- The complete line orbit family is principalSix\IntegralGL/Q. -/
def lineDoubleCosetEquiv : DoubleCoset.Quotient (principalSix : Set IntegralGL) Q ≃
    MulAction.orbitRel.Quotient principalSix Line := by
  rw [← standardLine_stabilizer]
  exact doubleCosetOrbitEquiv principalSix standardLine fullLine_transitive

/-- The complete plane orbit family is principalSix\IntegralGL/P. -/
def planeDoubleCosetEquiv : DoubleCoset.Quotient (principalSix : Set IntegralGL) P ≃
    MulAction.orbitRel.Quotient principalSix Plane := by
  rw [← standardPlane_stabilizer]
  exact doubleCosetOrbitEquiv principalSix standardPlane fullPlane_transitive

/-- The complete corner orbit family is principalSix\IntegralGL/B. -/
def flagDoubleCosetEquiv : DoubleCoset.Quotient (principalSix : Set IntegralGL) B ≃
    MulAction.orbitRel.Quotient principalSix Flag := by
  rw [← standardFlag_stabilizer]
  exact doubleCosetOrbitEquiv principalSix standardFlag fullFlag_transitive

theorem cover_line_at (g : IntegralGL) :
    MulAction.stabilizer principalSix (g • standardLine) =
      (Q.map (MulAut.conj g).toMonoidHom).comap principalSix.subtype := by
  rw [← standardLine_stabilizer]
  exact cover_stabilizer_conjugate principalSix standardLine g

theorem cover_plane_at (g : IntegralGL) :
    MulAction.stabilizer principalSix (g • standardPlane) =
      (P.map (MulAut.conj g).toMonoidHom).comap principalSix.subtype := by
  rw [← standardPlane_stabilizer]
  exact cover_stabilizer_conjugate principalSix standardPlane g

theorem cover_flag_at (g : IntegralGL) :
    MulAction.stabilizer principalSix (g • standardFlag) =
      (B.map (MulAut.conj g).toMonoidHom).comap principalSix.subtype := by
  rw [← standardFlag_stabilizer]
  exact cover_stabilizer_conjugate principalSix standardFlag g

end TernaryPoly.SymmetricSpaceBoundaryFull
