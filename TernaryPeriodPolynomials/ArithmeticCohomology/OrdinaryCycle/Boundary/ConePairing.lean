module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeBar

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

abbrev Chains0 := DualCoefficients A × DualCoefficients A
abbrev Chains1 := Bar1 (faceP A P) × Bar1 (faceQ A Q) × DualCoefficients A
abbrev Chains2 := Bar2 (faceP A P) × Bar2 (faceQ A Q) × Bar1 (corner A P Q)

/-- The dual cone boundary, including the plus/minus endpoint terms. -/
def chainBoundary1 : Chains1 A P Q →ₗ[ℚ] Chains0 A where
  toFun z := (barBoundary1 (faceP A P) z.1 + z.2.2,
    barBoundary1 (faceQ A Q) z.2.1 - z.2.2)
  map_add' z w := by
    apply Prod.ext
    · change barBoundary1 (faceP A P) (z.1+w.1)+(z.2.2+w.2.2) = _
      rw [map_add]
      dsimp
      abel
    · change barBoundary1 (faceQ A Q) (z.2.1+w.2.1)-(z.2.2+w.2.2) = _
      rw [map_add]
      dsimp
      abel
  map_smul' r z := by
    apply Prod.ext
    · change barBoundary1 (faceP A P) (r • z.1)+r • z.2.2 =
        r • (barBoundary1 (faceP A P) z.1+z.2.2)
      rw [map_smul,smul_add]
    · change barBoundary1 (faceQ A Q) (r • z.2.1)-r • z.2.2 =
        r • (barBoundary1 (faceQ A Q) z.2.1-z.2.2)
      rw [map_smul,smul_sub]

/-- The corner chain enters P positively, Q negatively, and its own boundary negatively. -/
def chainBoundary2 : Chains2 A P Q →ₗ[ℚ] Chains1 A P Q where
  toFun z := (barBoundary2 (faceP A P) z.1 + barPush (intoP P Q) z.2.2,
    barBoundary2 (faceQ A Q) z.2.1 - barPush (intoQ P Q) z.2.2,
    -barBoundary1 (corner A P Q) z.2.2)
  map_add' z w := by
    dsimp
    simp only [map_add,neg_add]
    apply Prod.ext
    · abel_nf
    apply Prod.ext
    · abel_nf
    · rfl
  map_smul' r z := by
    dsimp
    simp only [map_smul,smul_add,smul_sub,smul_neg]

/-- These finite chains form a genuine chain complex. -/
@[simp] theorem chainBoundary1_chainBoundary2 (z : Chains2 A P Q) :
    chainBoundary1 A P Q (chainBoundary2 A P Q z) = 0 := by
  have hp : barBoundary1 (faceP A P) (barPush (intoP P Q) z.2.2) =
      barBoundary1 (corner A P Q) z.2.2 :=
    barBoundary1_push (faceP A P) (intoP P Q) z.2.2
  have hq : barBoundary1 (faceQ A Q) (barPush (intoQ P Q) z.2.2) =
      barBoundary1 (corner A P Q) z.2.2 :=
    barBoundary1_push (faceQ A Q) (intoQ P Q) z.2.2
  apply Prod.ext
  · change barBoundary1 (faceP A P)
      (barBoundary2 (faceP A P) z.1+barPush (intoP P Q) z.2.2) +
        -barBoundary1 (corner A P Q) z.2.2 = 0
    rw [map_add,barBoundary1_barBoundary2,hp,zero_add,add_neg_cancel]
  · change barBoundary1 (faceQ A Q)
      (barBoundary2 (faceQ A Q) z.2.1-barPush (intoQ P Q) z.2.2) -
        -barBoundary1 (corner A P Q) z.2.2 = 0
    rw [map_sub,barBoundary1_barBoundary2,hq,zero_sub,sub_self]

/-- The finite bar chain cone in degrees two, one, zero. -/
def chainComplex : ShortComplex (ModuleCat ℚ) :=
  ShortComplex.moduleCatMk (chainBoundary2 A P Q) (chainBoundary1 A P Q)
    (by apply LinearMap.ext; exact chainBoundary1_chainBoundary2 A P Q)

def pair0 (v : C0 A) (z : Chains0 A) : ℚ := z.1 v.1 + z.2 v.2

def pair1 (c : C1 A P Q) (z : Chains1 A P Q) : ℚ :=
  barPair c.1 z.1 + barPair c.2.1 z.2.1 + z.2.2 c.2.2

def pair2 (c : C2 A P Q) (z : Chains2 A P Q) : ℚ :=
  barPair c.1 z.1 + barPair c.2.1 z.2.1 + barPair c.2.2 z.2.2

/-- The finite cone pairing is adjoint to the actual cochain differential in degree zero. -/
theorem cone_adjunction0 (v : C0 A) (z : Chains1 A P Q) :
    pair1 A P Q (d0 A P Q v) z = pair0 A v (chainBoundary1 A P Q z) := by
  have hp := bar_adjunction0 (faceP A P) v.1 z.1
  have hq := bar_adjunction0 (faceQ A Q) v.2 z.2.1
  change barPair (d₀₁ (faceP A P) v.1) z.1 + barPair (d₀₁ (faceQ A Q) v.2) z.2.1 +
    z.2.2 (v.1-v.2) = (barBoundary1 (faceP A P) z.1+z.2.2) v.1 +
      (barBoundary1 (faceQ A Q) z.2.1-z.2.2) v.2
  rw [hp,hq,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
  abel

/-- The degree-one adjunction certifies every face and corner sign. -/
theorem cone_adjunction1 (c : C1 A P Q) (z : Chains2 A P Q) :
    pair2 A P Q (d1 A P Q c) z = pair1 A P Q c (chainBoundary2 A P Q z) := by
  have hp := bar_adjunction1 (faceP A P) c.1 z.1
  have hq := bar_adjunction1 (faceQ A Q) c.2.1 z.2.1
  have hb := bar_adjunction0 (corner A P Q) c.2.2 z.2.2
  have hiP := barPair_push c.1 (intoP P Q) z.2.2
  have hiQ := barPair_push c.2.1 (intoQ P Q) z.2.2
  change barPair (d₁₂ (faceP A P) c.1) z.1 + barPair (d₁₂ (faceQ A Q) c.2.1) z.2.1 +
    barPair ((c.1 ∘ intoP P Q)-(c.2.1 ∘ intoQ P Q)-d₀₁ (corner A P Q) c.2.2) z.2.2 =
      barPair c.1 (barBoundary2 (faceP A P) z.1+barPush (intoP P Q) z.2.2) +
      barPair c.2.1 (barBoundary2 (faceQ A Q) z.2.1-barPush (intoQ P Q) z.2.2) +
      (-barBoundary1 (corner A P Q) z.2.2) c.2.2
  rw [hp,hq,barPair_sub,barPair_sub,LinearMap.sub_apply,LinearMap.sub_apply,hb,
    map_add,map_sub,hiP,hiQ,LinearMap.neg_apply]
  abel

@[simp] theorem pair1_sub (c c' : C1 A P Q) (z : Chains1 A P Q) :
    pair1 A P Q (c-c') z = pair1 A P Q c z-pair1 A P Q c' z := by
  change barPair (c.1-c'.1) z.1 + barPair (c.2.1-c'.2.1) z.2.1 +
    z.2.2 (c.2.2-c'.2.2) = _
  rw [barPair_sub,barPair_sub,LinearMap.sub_apply,LinearMap.sub_apply,map_sub]
  dsimp [pair1]
  abel

@[simp] theorem pair2_zero (z : Chains2 A P Q) : pair2 A P Q 0 z = 0 := by
  change barPair (0 : P × P → A) z.1 + barPair (0 : Q × Q → A) z.2.1 +
    barPair (0 : (P ⊓ Q : Subgroup G) → A) z.2.2 = 0
  rw [barPair_zero,barPair_zero,barPair_zero]
  simp only [LinearMap.zero_apply,add_zero]

/-- Every genuine cone cocycle annihilates every finite cone boundary. -/
theorem cocycle_pair_boundary (c : Z1 A P Q) (z : Chains2 A P Q) :
    pair1 A P Q c.val (chainBoundary2 A P Q z) = 0 := by
  calc
    _ = pair2 A P Q (d1 A P Q c.val) z := (cone_adjunction1 A P Q c.val z).symm
    _ = 0 := by rw [c.property,pair2_zero]

/-- Gauge invariance holds on actual finite cone cycles, with no topology assumption. -/
theorem gauge_pair_cycle (c : Z1 A P Q) (v : C0 A) (z : Chains1 A P Q)
    (hz : chainBoundary1 A P Q z = 0) :
    pair1 A P Q (gauge A P Q c v).val z = pair1 A P Q c.val z := by
  change pair1 A P Q (c.val-d0 A P Q v) z = _
  rw [pair1_sub,cone_adjunction0,hz]
  change pair1 A P Q c.val z - (0+0) = pair1 A P Q c.val z
  abel

end TernaryPoly.OrdinaryBoundaryCone
