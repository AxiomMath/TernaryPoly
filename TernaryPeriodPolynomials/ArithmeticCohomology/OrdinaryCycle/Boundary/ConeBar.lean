module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryCone
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology

section FinitePairing
variable {M I J : Type} [AddCommGroup M] [Module ℚ M]

/-- Finite-support evaluation against algebraic dual coefficients. -/
def barPair (a : I → M) : (I →₀ Module.Dual ℚ M) →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun i => Module.Dual.eval ℚ M (a i))

@[simp] theorem barPair_single (a : I → M) (i : I) (l : Module.Dual ℚ M) :
    barPair a (Finsupp.single i l) = l (a i) := Finsupp.lsum_single ℚ _ _ _

@[simp] theorem barPair_add (a b : I → M) : barPair (a+b) = barPair a + barPair b := by
  apply Finsupp.lhom_ext
  intro i l
  simp only [barPair_single,LinearMap.add_apply,Pi.add_apply,map_add]

@[simp] theorem barPair_sub (a b : I → M) : barPair (a-b) = barPair a - barPair b := by
  apply Finsupp.lhom_ext
  intro i l
  simp only [barPair_single,LinearMap.sub_apply,Pi.sub_apply,map_sub]

@[simp] theorem barPair_zero : barPair (0 : I → M) = 0 := by
  apply Finsupp.lhom_ext
  intro i l
  simp only [barPair_single,Pi.zero_apply,map_zero,LinearMap.zero_apply]

/-- Pushforward of finite bar chains along the actual group inclusion. -/
def barPush (f : I → J) : (I →₀ Module.Dual ℚ M) →ₗ[ℚ] (J →₀ Module.Dual ℚ M) :=
  Finsupp.lsum ℚ (fun i => Finsupp.lsingle (f i))

@[simp] theorem barPush_single (f : I → J) (i : I) (l : Module.Dual ℚ M) :
    barPush f (Finsupp.single i l) = Finsupp.single (f i) l := Finsupp.lsum_single ℚ _ _ _

theorem barPair_push (a : J → M) (f : I → J) (c : I →₀ Module.Dual ℚ M) :
    barPair a (barPush f c) = barPair (a ∘ f) c := by
  have h : (barPair a).comp (barPush f) = barPair (a ∘ f) := by
    apply Finsupp.lhom_ext
    intro i l
    simp only [LinearMap.comp_apply,barPush_single,barPair_single,Function.comp_apply]
  exact LinearMap.congr_fun h c
end FinitePairing

variable {G : Type} [Group G] (A : Rep ℚ G)
abbrev DualCoefficients := Module.Dual ℚ A
abbrev Bar1 := G →₀ DualCoefficients A
abbrev Bar2 := G × G →₀ DualCoefficients A

/-- Dual right action: l·g = l ∘ ρ(g), the convention adjoint to d₀₁. -/
def dualRight (g : G) : DualCoefficients A →ₗ[ℚ] DualCoefficients A :=
  (A.ρ g).dualMap

@[simp] theorem dualRight_apply (g : G) (l : DualCoefficients A) (v : A) :
    dualRight A g l v = l (A.ρ g v) := rfl

/-- Degree-one finite bar boundary [g;l] ↦ l·g-l. -/
def barBoundary1 : Bar1 A →ₗ[ℚ] DualCoefficients A :=
  Finsupp.lsum ℚ (fun g => dualRight A g - LinearMap.id)

@[simp] theorem barBoundary1_single (g : G) (l : DualCoefficients A) :
    barBoundary1 A (Finsupp.single g l) = dualRight A g l-l := Finsupp.lsum_single ℚ _ _ _

/-- Degree-two boundary [g,h;l] ↦ [h;l·g]-[gh;l]+[g;l]. -/
def barBoundary2 : Bar2 A →ₗ[ℚ] Bar1 A :=
  Finsupp.lsum ℚ (fun gh => (Finsupp.lsingle gh.2).comp (dualRight A gh.1) -
    Finsupp.lsingle (gh.1*gh.2) + Finsupp.lsingle gh.1)

@[simp] theorem barBoundary2_single (g h : G) (l : DualCoefficients A) :
    barBoundary2 A (Finsupp.single (g,h) l) =
      Finsupp.single h (dualRight A g l)-Finsupp.single (g*h) l+Finsupp.single g l :=
  Finsupp.lsum_single ℚ _ _ _

/-- Cochain/chain adjunction in degrees zero and one, with the actual group differential. -/
theorem bar_adjunction0 (v : A) (c : Bar1 A) :
    barPair (d₀₁ A v) c = barBoundary1 A c v := by
  have h : barPair (d₀₁ A v) = (Module.Dual.eval ℚ A v).comp (barBoundary1 A) := by
    apply Finsupp.lhom_ext
    intro g l
    simp only [barPair_single,LinearMap.comp_apply,barBoundary1_single,
      Module.Dual.eval_apply,LinearMap.sub_apply,dualRight_apply]
    exact l.map_sub _ _
  exact LinearMap.congr_fun h c

/-- Cochain/chain adjunction in degrees one and two, including the multiplication face. -/
theorem bar_adjunction1 (a : G → A) (c : Bar2 A) :
    barPair (d₁₂ A a) c = barPair a (barBoundary2 A c) := by
  have h : barPair (d₁₂ A a) = (barPair a).comp (barBoundary2 A) := by
    apply Finsupp.lhom_ext
    intro gh l
    rcases gh with ⟨g,h⟩
    simp only [barPair_single,LinearMap.comp_apply,barBoundary2_single,map_add,map_sub,
      dualRight_apply]
    change l (A.ρ g (a h)-a (g*h)+a g) = l (A.ρ g (a h))-l (a (g*h))+l (a g)
    rw [map_add,map_sub]
  exact LinearMap.congr_fun h c

/-- The bar boundary commutes with literal restriction/inclusion on coefficients and chains. -/
theorem barBoundary1_push {H : Type} [Group H] (f : H →* G)
    (c : Bar1 (Rep.res f A)) :
    barBoundary1 A (barPush f c) = barBoundary1 (Rep.res f A) c := by
  have h : (barBoundary1 A).comp (barPush f) = barBoundary1 (Rep.res f A) := by
    apply Finsupp.lhom_ext
    intro g l
    simp only [LinearMap.comp_apply,barPush_single,barBoundary1_single]
    rfl
  exact LinearMap.congr_fun h c

/-- The finite bar boundaries square to zero, proved against every actual coefficient. -/
@[simp] theorem barBoundary1_barBoundary2 (c : Bar2 A) :
    barBoundary1 A (barBoundary2 A c) = 0 := by
  have h : (barBoundary1 A).comp (barBoundary2 A) = 0 := by
    apply Finsupp.lhom_ext
    intro gh l
    rcases gh with ⟨g,h⟩
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply,barBoundary2_single,map_add,map_sub,barBoundary1_single,
      LinearMap.add_apply,LinearMap.sub_apply,dualRight_apply,LinearMap.zero_apply]
    change l (A.ρ g (A.ρ h v)) - l (A.ρ g v) -
      (l (A.ρ (g*h) v)-l v) + (l (A.ρ g v)-l v) = 0
    rw [map_mul]
    change l (A.ρ g (A.ρ h v)) - l (A.ρ g v) -
      (l (A.ρ g (A.ρ h v))-l v) + (l (A.ρ g v)-l v) = 0
    abel
  exact LinearMap.congr_fun h c

end TernaryPoly.OrdinaryBoundaryCone
