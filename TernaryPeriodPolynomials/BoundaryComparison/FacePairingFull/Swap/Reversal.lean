module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.HomogeneousCohomology

@[expose] public section


/-!
# Vertex reversal on homogeneous cochains and cohomology

For a subgroup `Γ ≤ G` and a representation `ρ`, the reversal of the vertices of a homogeneous
cochain (`rev1 f (a, b) = f (b, a)`, `rev2 f (a, b, c) = f (c, b, a)`) preserves equivariance,
commutes with the differential from degree one to degree two (`differentialOne_rev1`), and carries
cocycles to cocycles up to the sign `(-1)^3` (`differentialTwo_rev2`). It therefore induces an
involution `revH2` of `H2 Γ ρ` (`revH2_classOf`, `revH2_revH2`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (Γ : Subgroup G)
  (ρ : Representation ℂ G V)

/-- Reversal of the two vertices of a homogeneous one-cochain. -/
def rev1 : cochains Γ ρ 1 →ₗ[ℂ] cochains Γ ρ 1 where
  toFun f := ⟨fun x => f.val ![x 1, x 0], by
    intro γ x
    have h := f.property γ ![x 1, x 0]
    have ht : (fun i => γ.val * ![x 1, x 0] i) = ![γ.val * x 1, γ.val * x 0] := by
      funext i
      fin_cases i <;> rfl
    rw [ht] at h
    exact h⟩
  map_add' f g := rfl
  map_smul' a f := rfl

/-- Reversal of the three vertices of a homogeneous two-cochain. -/
def rev2 : cochains Γ ρ 2 →ₗ[ℂ] cochains Γ ρ 2 where
  toFun f := ⟨fun x => f.val ![x 2, x 1, x 0], by
    intro γ x
    have h := f.property γ ![x 2, x 1, x 0]
    have ht : (fun i => γ.val * ![x 2, x 1, x 0] i) = ![γ.val * x 2, γ.val * x 1, γ.val * x 0] := by
      funext i
      fin_cases i <;> rfl
    rw [ht] at h
    exact h⟩
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] theorem rev1_apply (f : cochains Γ ρ 1) (x : Fin 2 → G) :
    (rev1 Γ ρ f).val x = f.val ![x 1, x 0] := rfl

@[simp] theorem rev2_apply (f : cochains Γ ρ 2) (x : Fin 3 → G) :
    (rev2 Γ ρ f).val x = f.val ![x 2, x 1, x 0] := rfl

theorem rev1_rev1 (f : cochains Γ ρ 1) : rev1 Γ ρ (rev1 Γ ρ f) = f := by
  apply Subtype.ext
  funext x
  have : (![x 0, x 1] : Fin 2 → G) = x := by
    funext i
    fin_cases i <;> rfl
  change f.val ![x 0, x 1] = f.val x
  rw [this]

theorem rev2_rev2 (f : cochains Γ ρ 2) : rev2 Γ ρ (rev2 Γ ρ f) = f := by
  apply Subtype.ext
  funext x
  have : (![x 0, x 1, x 2] : Fin 3 → G) = x := by
    funext i
    fin_cases i <;> rfl
  change f.val ![x 0, x 1, x 2] = f.val x
  rw [this]

/-- Reversal commutes with the differential from degree one to degree two. -/
theorem differentialOne_rev1 (f : cochains Γ ρ 1) :
    differentialOne Γ ρ (rev1 Γ ρ f) = rev2 Γ ρ (differentialOne Γ ρ f) := by
  apply Subtype.ext
  funext x
  change f.val ![x 2, x 1] - f.val ![x 2, x 0] + f.val ![x 1, x 0] =
    f.val ![x 1, x 0] - f.val ![x 2, x 0] + f.val ![x 2, x 1]
  abel

/-- Reversal carries cocycles to cocycles. -/
theorem differentialTwo_rev2 (f : cochains Γ ρ 2) (x : Fin 4 → G) :
    differentialTwo Γ ρ (rev2 Γ ρ f) x = -differentialTwo Γ ρ f ![x 3, x 2, x 1, x 0] := by
  change f.val ![x 3, x 2, x 1] - f.val ![x 3, x 2, x 0] + f.val ![x 3, x 1, x 0] -
      f.val ![x 2, x 1, x 0] =
    -(f.val ![x 2, x 1, x 0] - f.val ![x 3, x 1, x 0] + f.val ![x 3, x 2, x 0] -
      f.val ![x 3, x 2, x 1])
  abel

/-- Reversal as an endomorphism of the degree-two cocycles. -/
def revCocycle : cocycles Γ ρ →ₗ[ℂ] cocycles Γ ρ :=
  (rev2 Γ ρ).restrict (p := cocycles Γ ρ) (q := cocycles Γ ρ) (fun f hf => by
    have hf' : differentialTwo Γ ρ f = 0 := hf
    show differentialTwo Γ ρ (rev2 Γ ρ f) = 0
    funext x
    rw [differentialTwo_rev2, hf']
    simp)

@[simp] theorem revCocycle_val (c : cocycles Γ ρ) : (revCocycle Γ ρ c).val = rev2 Γ ρ c.val := rfl

theorem revCocycle_revCocycle (c : cocycles Γ ρ) : revCocycle Γ ρ (revCocycle Γ ρ c) = c :=
  Subtype.ext (rev2_rev2 Γ ρ c.val)

theorem revCocycle_boundaryMap (u : cochains Γ ρ 1) :
    revCocycle Γ ρ (boundaryMap Γ ρ u) = boundaryMap Γ ρ (rev1 Γ ρ u) := by
  apply Subtype.ext
  exact (differentialOne_rev1 Γ ρ u).symm

/-- Reversal as an involution of `H2`. -/
def revH2 : H2 Γ ρ →ₗ[ℂ] H2 Γ ρ :=
  Submodule.mapQ _ _ (revCocycle Γ ρ) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨rev1 Γ ρ u, (revCocycle_boundaryMap Γ ρ u).symm⟩)

theorem revH2_classOf (c : cocycles Γ ρ) :
    revH2 Γ ρ (classOf Γ ρ c) = classOf Γ ρ (revCocycle Γ ρ c) := rfl

theorem revH2_revH2 (a : H2 Γ ρ) : revH2 Γ ρ (revH2 Γ ρ a) = a := by
  induction a using Submodule.Quotient.induction_on with
  | H c => 
    change revH2 Γ ρ (revH2 Γ ρ (classOf Γ ρ c)) = classOf Γ ρ c
    rw [revH2_classOf, revH2_classOf, revCocycle_revCocycle]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
