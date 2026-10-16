module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryCone

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

def cycleP : Z1 A P Q →ₗ[ℚ] cocycles₁ (faceP A P) where
  toFun c := ⟨c.val.1, ((mem_Z1_iff A P Q c.val).mp c.property).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cycleQ : Z1 A P Q →ₗ[ℚ] cocycles₁ (faceQ A Q) where
  toFun c := ⟨c.val.2.1, ((mem_Z1_iff A P Q c.val).mp c.property).2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev FaceH1 := groupCohomology.H1 (faceP A P) × groupCohomology.H1 (faceQ A Q)

def faceClasses : Z1 A P Q →ₗ[ℚ] FaceH1 A P Q :=
  ((H1π (faceP A P)).hom.comp (cycleP A P Q)).prod
    ((H1π (faceQ A Q)).hom.comp (cycleQ A P Q))

@[simp] theorem faceClasses_coboundary (v : C0 A) :
    faceClasses A P Q (coboundary A P Q v) = 0 := by
  apply Prod.ext
  · exact (H1π_eq_zero_iff _).mpr ⟨v.1,rfl⟩
  · exact (H1π_eq_zero_iff _).mpr ⟨v.2,rfl⟩

/-- The actual face H1 classes, descended through cone gauge equivalence. -/
def toFaces : H1 A P Q →ₗ[ℚ] FaceH1 A P Q :=
  (boundaries A P Q).liftQ (faceClasses A P Q) (by
    rintro _ ⟨v,rfl⟩
    exact faceClasses_coboundary A P Q v)

@[simp] theorem toFaces_classOf (c : Z1 A P Q) :
    toFaces A P Q (classOf A P Q c) = faceClasses A P Q c := rfl

abbrev InvariantsB := (corner A P Q).ρ.invariants
abbrev InvariantsP := (faceP A P).ρ.invariants
abbrev InvariantsQ := (faceQ A Q).ρ.invariants

/-- A corner invariant gives the cone cocycle (0,0,u). -/
def cornerCycle : InvariantsB A P Q →ₗ[ℚ] Z1 A P Q where
  toFun u := ⟨(0,0,u.val),(mem_Z1_iff A P Q _).mpr ⟨(cocycles₁ _).zero_mem,
    (cocycles₁ _).zero_mem, fun b => by
      change A.ρ b.val u.val-u.val = 0-0
      have h : A.ρ b.val u.val = u.val := u.property b
      rw [h,sub_self,sub_self]⟩⟩
  map_add' u v := by
    apply Subtype.ext
    change (0,0,u.val+v.val) = ((0 : P → A)+0, (0 : Q → A)+0, u.val+v.val)
    simp only [add_zero]
  map_smul' r u := by
    apply Subtype.ext
    change (0,0,r • u.val) = (r • (0 : P → A), r • (0 : Q → A), r • u.val)
    simp only [smul_zero]

def connecting : InvariantsB A P Q →ₗ[ℚ] H1 A P Q :=
  (classOf A P Q).comp (cornerCycle A P Q)

@[simp] theorem toFaces_connecting (u : InvariantsB A P Q) :
    toFaces A P Q (connecting A P Q u) = 0 := by
  change (H1π (faceP A P) 0, H1π (faceQ A Q) 0) = 0
  simp only [map_zero]; rfl

/-- The zero-face part of any cone class has an invariant corner representative. -/
theorem zero_faces_iff (c : Z1 A P Q) :
    faceClasses A P Q c = 0 ↔ ∃ u, classOf A P Q c = connecting A P Q u := by
  constructor
  · intro h
    have hp : H1π (faceP A P) (cycleP A P Q c) = 0 := congrArg Prod.fst h
    have hq : H1π (faceQ A Q) (cycleQ A P Q c) = 0 := congrArg Prod.snd h
    obtain ⟨vP,hvP⟩ := (H1π_eq_zero_iff _).mp hp
    obtain ⟨vQ,hvQ⟩ := (H1π_eq_zero_iff _).mp hq
    have hgP : (gauge A P Q c (vP,vQ)).val.1 = 0 := by
      rw [gauge_val]
      change c.val.1 - d₀₁ (faceP A P) vP = 0
      exact sub_eq_zero.mpr hvP.symm
    have hgQ : (gauge A P Q c (vP,vQ)).val.2.1 = 0 := by
      rw [gauge_val]
      change c.val.2.1 - d₀₁ (faceQ A Q) vQ = 0
      exact sub_eq_zero.mpr hvQ.symm
    let g := gauge A P Q c (vP,vQ)
    have hu : g.val.2.2 ∈ InvariantsB A P Q := by
      intro b
      have hc := ((mem_Z1_iff A P Q g.val).mp g.property).2.2 b
      rw [hgP,hgQ] at hc
      have hc' : d₀₁ (corner A P Q) g.val.2.2 b = 0 := by
        simpa only [Pi.zero_apply,sub_self] using hc
      exact sub_eq_zero.mp hc'
    refine ⟨⟨g.val.2.2,hu⟩,?_⟩
    have hg : g = cornerCycle A P Q ⟨g.val.2.2,hu⟩ := by
      apply Subtype.ext
      exact Prod.ext hgP (Prod.ext hgQ rfl)
    rw [← classOf_gauge A P Q c (vP,vQ)]
    exact congrArg (classOf A P Q) hg
  · rintro ⟨u,hu⟩
    have := congrArg (toFaces A P Q) hu
    exact this.trans (toFaces_connecting A P Q u)

/-- Exactness of corner invariants → cone H1 → full face H1. -/
theorem range_connecting_eq_ker_toFaces :
    LinearMap.range (connecting A P Q) = LinearMap.ker (toFaces A P Q) := by
  ext x
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective (boundaries A P Q) x
  change (∃ u, connecting A P Q u = classOf A P Q c) ↔ faceClasses A P Q c = 0
  rw [zero_faces_iff]
  exact ⟨fun ⟨u,h⟩ => ⟨u,h.symm⟩, fun ⟨u,h⟩ => ⟨u,h.symm⟩⟩

/-- The map on H0 is the difference of the two actual invariant values. -/
def invariantDifference : (InvariantsP A P × InvariantsQ A Q) →ₗ[ℚ] InvariantsB A P Q where
  toFun v := ⟨v.1.val-v.2.val,fun b => by
    change A.ρ b.val (v.1.val-v.2.val) = v.1.val-v.2.val
    have hp : A.ρ b.val v.1.val = v.1.val := v.1.property (intoP P Q b)
    have hq : A.ρ b.val v.2.val = v.2.val := v.2.property (intoQ P Q b)
    rw [map_sub,hp,hq]⟩
  map_add' v w := by apply Subtype.ext; exact add_sub_add_comm _ _ _ _
  map_smul' r v := by apply Subtype.ext; exact (smul_sub r _ _).symm

/-- A pure corner class vanishes precisely when it is a difference of face invariants. -/
theorem connecting_eq_zero_iff (u : InvariantsB A P Q) :
    connecting A P Q u = 0 ↔ ∃ v, invariantDifference A P Q v = u := by
  change (boundaries A P Q).mkQ (cornerCycle A P Q u) = 0 ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v,hv⟩
    have hp := congrArg (fun z : Z1 A P Q => z.val.1) hv
    have hq := congrArg (fun z : Z1 A P Q => z.val.2.1) hv
    have hu := congrArg (fun z : Z1 A P Q => z.val.2.2) hv
    have hp' : v.1 ∈ InvariantsP A P := by
      intro g
      exact sub_eq_zero.mp (congrFun hp g)
    have hq' : v.2 ∈ InvariantsQ A Q := by
      intro g
      exact sub_eq_zero.mp (congrFun hq g)
    exact ⟨(⟨v.1,hp'⟩,⟨v.2,hq'⟩),Subtype.ext hu⟩
  · rintro ⟨v,hv⟩
    refine ⟨(v.1.val,v.2.val),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext g
      exact sub_eq_zero.mpr (v.1.property g)
    apply Prod.ext
    · funext g
      exact sub_eq_zero.mpr (v.2.property g)
    exact congrArg Subtype.val hv

/-- Exactness of full face invariants → corner invariants → cone H1. -/
theorem range_invariantDifference_eq_ker_connecting :
    LinearMap.range (invariantDifference A P Q) = LinearMap.ker (connecting A P Q) := by
  ext u
  exact (connecting_eq_zero_iff A P Q u).symm

end TernaryPoly.OrdinaryBoundaryCone
