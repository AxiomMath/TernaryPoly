module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LineCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# The edge cocycle at the good line is minus the Levi cocycle of the fiber data

Let `C` be a homogeneous two-cocycle of the good-line stabilizer `Λ₁` with coefficients in a
representation `ρ` of `GL₃(ℚ)`, and let `ω_U` be an equivariant primitive of `C` over the radical
lattice `U` of `Λ₁`.  The two-cocycle of the group `Λ₁`,
`(g, h) ↦ C(1, g, g h)`, differs from `(g, h) ↦ ω_U(g, g h) - ρ(g) ω_U(1, h)` by the boundary of
`g ↦ ω_U(1, g)`; the latter vanishes on pairs of radical elements, so it is a *relative*
two-cocycle with the same class.

The mixed radical one-cocycle of this relative representative at a Levi element `k = diag(γ, 1)` is
computed on the radical lattice from the conjugation formula for the pullback of the Levi cocycle
`A(k) = k ⋆ ω_U - ω_U`: it equals `u ↦ ρ(k) A(k)(1, u'')` with `u k = k u''`, and
`ρ(k) A(k)(1, u'') = -A(k⁻¹)(1, u) + (ρ(u) - 1)(-w)` for the constant `w = ρ(k) A(k)(1, k⁻¹)`.
Hence its coordinate in the binary forms is exactly the negative of the coordinate of the Levi
cocycle `A(k⁻¹)` of the fiber data (`coordinate_edge_eq_neg`).

* `relCocycle`, `relOf`, `relOf_H2`: the relative representative of an ambient two-cocycle.
* `radical_edge_add_levi`: the identity on the radical lattice.
* `coordinate_edge_eq_neg`: the identity of coordinates.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant (UCocycle)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (pull1 leviCocycle leviCocycle_inv leviCocycle_equivariant leviCocycle_closed rep_self_inv)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (leviHom lower_mem_sub levi_normalizes levi_inv_normalizes pull1_lattice rho_lower_eq zCoc
    PhiTotal PhiTotal_eq coord_lower_eq_of_shift)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (GL2Z)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

/-! ### Equivariance of a homogeneous cocycle at displayed vertices -/

/-- A homogeneous two-cocycle of a subgroup is equivariant at displayed vertices for every
element of the subgroup. -/
theorem cocycle_vec3 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (Γ : Subgroup G)
    (ρ : Representation ℂ G V) (C : cocycles Γ ρ) {g : G} (hg : g ∈ Γ) (a b c : G) :
    C.val.val ![g * a, g * b, g * c] = ρ g (C.val.val ![a, b, c]) := by
  have h : C.val.val (fun i => g * (![a, b, c] : Fin 3 → G) i) = ρ g (C.val.val ![a, b, c]) :=
    C.val.property ⟨g, hg⟩ ![a, b, c]
  have e : (fun i => g * (![a, b, c] : Fin 3 → G) i) = ![g * a, g * b, g * c] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  exact h

/-- The Levi embedding of `GL₂(ℤ)` lies in the arithmetic stabilizer of the good line. -/
theorem leviHom_mem_Λ₁ (γ : GL2Z) : leviHom γ ∈ Λ₁ :=
  arithmeticLevi_goodLine γ

/-! ### The relative representative -/

/-- **The relative representative** of the ambient two-cocycle `C` of `Λ₁` with the equivariant
primitive `ω_U` over the radical lattice: the ambient two-cocycle minus the boundary of
`g ↦ ω_U(1, g)`. -/
def relCocycle {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ) :
    groupCohomology.cocycles₂ (subgroupCoefficientRep Λ₁ ρ) :=
  ambientCocycleToGroup Λ₁ ρ C -
    twoBoundaryCycle (subgroupCoefficientRep Λ₁ ρ) (fun g : Λ₁ => ωU ![1, g.val])

/-- The value of the relative representative on a pair. -/
theorem relCocycle_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c]) (g h : Λ₁) :
    relCocycle ρ ωU C (g, h) = ωU ![g.val, g.val * h.val] - ρ g.val (ωU ![1, h.val]) := by
  have h1 : ωU ![g.val, g.val * h.val] - ωU ![1, g.val * h.val] + ωU ![1, g.val] =
      C.val.val ![1, g.val, g.val * h.val] := hd 1 g.val (g.val * h.val)
  change C.val.val ![1, g.val, g.val * h.val] -
      (ρ g.val (ωU ![1, h.val]) - ωU ![1, g.val * h.val] + ωU ![1, g.val]) = _
  rw [← h1]
  abel

/-- The value of the relative representative on a pair, as an element of the coefficient module. -/
def relVal {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ) (g h : Λ₁) : V :=
  relCocycle ρ ωU C (g, h)

/-- The value of the relative representative on a pair. -/
theorem relVal_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c]) (g h : Λ₁) :
    relVal ρ ωU C g h = ωU ![g.val, g.val * h.val] - ρ g.val (ωU ![1, h.val]) :=
  relCocycle_apply ρ ωU C hd g h

/-- The relative representative vanishes on pairs of radical elements. -/
theorem relCocycle_radical {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b]))
    (p q : RadicalLattice) :
    relCocycle ρ ωU C (goodLineRadicalInclusion p, goodLineRadicalInclusion q) = 0 := by
  rw [relCocycle_apply ρ ωU C hd]
  have h := hω (lowerRadicalLattice p) (lower_mem_sub p) 1 (lowerRadicalLattice q)
  rw [mul_one] at h
  change ωU ![lowerRadicalLattice p, lowerRadicalLattice p * lowerRadicalLattice q] -
    ρ (lowerRadicalLattice p) (ωU ![1, lowerRadicalLattice q]) = 0
  rw [h, sub_self]

/-- **The relative two-cocycle** attached to `C` and `ω_U`. -/
def relOf {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b])) :
    relativeTwoCocycles goodLineRadicalInclusion (subgroupCoefficientRep Λ₁ ρ) :=
  ⟨relCocycle ρ ωU C, relCocycle_radical ρ ωU C hd hω⟩

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOf_H2 {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b])) :
    groupCohomology.H2π (subgroupCoefficientRep Λ₁ ρ) (relOf ρ ωU C hd hω).val =
      groupCohomology.H2π (subgroupCoefficientRep Λ₁ ρ) (ambientCocycleToGroup Λ₁ ρ C) := by
  change groupCohomology.H2π (subgroupCoefficientRep Λ₁ ρ)
    (ambientCocycleToGroup Λ₁ ρ C -
      twoBoundaryCycle (subgroupCoefficientRep Λ₁ ρ) (fun g : Λ₁ => ωU ![1, g.val])) = _
  rw [map_sub]
  exact sub_eq_self.mpr (twoBoundaryCycle_H2_zero _ _)

/-! ### The Levi cocycles as radical-equivariant cocycles -/

/-- The Levi cocycle `A(k)` of the primitive is a `U`-equivariant one-cocycle. -/
theorem uCocycle_leviHom {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b])) (γ : GL2Z) :
    UCocycle ρ latL1.sub (leviCocycle ρ ωU (leviHom γ)) :=
  ⟨leviCocycle_equivariant ρ hω (levi_normalizes γ),
    leviCocycle_closed ρ (ζ := C.val.val) hd (cocycle_vec3 Λ₁ ρ C (leviHom_mem_Λ₁ γ))⟩

/-- The Levi cocycle `A(k⁻¹)` of the primitive is a `U`-equivariant one-cocycle. -/
theorem uCocycle_leviHom_inv {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (ωU : (Fin 2 → RationalGL3) → V) (C : cocycles Λ₁ ρ)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b])) (γ : GL2Z) :
    UCocycle ρ latL1.sub (leviCocycle ρ ωU (leviHom γ)⁻¹) :=
  ⟨leviCocycle_equivariant ρ hω (fun u hu => by
      simpa only [inv_inv] using levi_inv_normalizes γ u hu),
    leviCocycle_closed ρ (ζ := C.val.val) hd
      (cocycle_vec3 Λ₁ ρ C (Λ₁.inv_mem (leviHom_mem_Λ₁ γ)))⟩

/-- `ρ(k) A(k)(a, b) = ω(k a, k b) - ρ(k) ω(a, b)`. -/
theorem rho_leviCocycle_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ω : (Fin 2 → G) → V) (k a b : G) :
    ρ k (leviCocycle ρ ω k ![a, b]) = ω ![k * a, k * b] - ρ k (ω ![a, b]) := by
  change ρ k (ρ k⁻¹ (ω ![k * a, k * b]) - ω ![a, b]) = _
  rw [map_sub, rep_self_inv ρ]

/-! ### The identity on the radical lattice -/

/-- **The identity on the radical lattice.**  The mixed radical value of the relative
representative at the Levi element `k = diag(γ, 1)`, plus the Levi cocycle `A(k⁻¹)(1, u)`, is the
coboundary of `-w`, `w = ρ(k) A(k)(1, k⁻¹)`. -/
theorem radical_edge_add_levi {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) (C : cocycles Λ₁ ρ) (ωU : (Fin 2 → RationalGL3) → V)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b, ωU ![g * a, g * b] = ρ g (ωU ![a, b])) (γ : GL2Z)
    (p : RadicalLattice) :
    (relVal ρ ωU C (goodLineLeviSection γ) (goodLineRadicalInclusion (lowerLeviLatticeInput γ p)) -
      relVal ρ ωU C (goodLineRadicalInclusion p) (goodLineLeviSection γ)) +
      leviCocycle ρ ωU (leviHom γ)⁻¹ ![1, lowerRadicalLattice p] =
    ρ (lowerRadicalLattice p) (-(ρ (leviHom γ) (leviCocycle ρ ωU (leviHom γ) ![1, (leviHom γ)⁻¹]))) -
      (-(ρ (leviHom γ) (leviCocycle ρ ωU (leviHom γ) ![1, (leviHom γ)⁻¹]))) := by
  have hA := uCocycle_leviHom ρ ωU C hd hω γ
  have hP := pull1_lattice ρ hA (leviHom γ) (lowerRadicalLattice p)
    (lowerRadicalLattice (lowerLeviLatticeInput γ p)) (lower_mem_sub _)
    (lowerLeviLatticeInput_conjugation γ p)
  have hinv : leviCocycle ρ ωU (leviHom γ)⁻¹ ![1, lowerRadicalLattice p] =
      -(pull1 ρ (leviHom γ)⁻¹ (leviCocycle ρ ωU (leviHom γ)) ![1, lowerRadicalLattice p]) :=
    congrFun (leviCocycle_inv ρ ωU (leviHom γ)) ![1, lowerRadicalLattice p]
  have hr1 : relVal ρ ωU C (goodLineLeviSection γ)
      (goodLineRadicalInclusion (lowerLeviLatticeInput γ p)) =
      ρ (leviHom γ) (leviCocycle ρ ωU (leviHom γ)
        ![1, lowerRadicalLattice (lowerLeviLatticeInput γ p)]) := by
    rw [relVal_apply ρ ωU C hd]
    have h := rho_leviCocycle_apply ρ ωU (leviHom γ) 1
      (lowerRadicalLattice (lowerLeviLatticeInput γ p))
    rw [mul_one] at h
    exact h.symm
  have hr2 : relVal ρ ωU C (goodLineRadicalInclusion p) (goodLineLeviSection γ) = 0 := by
    rw [relVal_apply ρ ωU C hd]
    have h := hω (lowerRadicalLattice p) (lower_mem_sub p) 1 (leviHom γ)
    rw [mul_one] at h
    change ωU ![lowerRadicalLattice p, lowerRadicalLattice p * leviHom γ] -
      ρ (lowerRadicalLattice p) (ωU ![1, leviHom γ]) = 0
    rw [h, sub_self]
  rw [hr1, hr2, sub_zero, hinv, hP, map_neg]
  abel

/-! ### The identity of coordinates -/

/-- **The coordinate of the edge cocycle is minus the coordinate of the Levi cocycle.**  If the
mixed radical cocycle `E` of the Levi element `diag(γ, 1)` is given by the relative representative,
its good-line coordinate is `-Φ(A(k⁻¹))`. -/
theorem coordinate_edge_eq_neg (n : ℕ) (positive : 0 < n) (χ : RankOneCharacter)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ))
    (ωU : (Fin 2 → RationalGL3) → HomogeneousPoly n)
    (hd : ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c])
    (hω : ∀ g ∈ latL1.sub, ∀ a b,
      ωU ![g * a, g * b] = rationalCoefficientComponent n χ g (ωU ![a, b])) (γ : GL2Z)
    (E : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n))
    (hE : ∀ p, E p =
      relCocycle (rationalCoefficientComponent n χ) ωU C
          (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ p)) -
        relCocycle (rationalCoefficientComponent n χ) ωU C
          (goodLineRadicalInclusion p, goodLineLeviSection γ)) :
    lowerRadicalCocycleCoordinate n E =
      -PhiTotal n (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom γ)⁻¹) := by
  have hf := uCocycle_leviHom_inv (rationalCoefficientComponent n χ) ωU C hd hω γ
  rw [PhiTotal_eq n χ hf]
  refine (coord_lower_eq_of_shift n positive E (-zCoc n χ hf)
    (-(rationalCoefficientComponent n χ (leviHom γ)
      (leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom γ) ![1, (leviHom γ)⁻¹])))
    (fun p => ?_)).trans (map_neg (lowerRadicalCocycleCoordinate n) (zCoc n χ hf))
  have key := radical_edge_add_levi (rationalCoefficientComponent n χ) C ωU hd hω γ p
  have e : (lowerRadicalLatticeRep n).ρ p = rationalCoefficientComponent n χ (lowerRadicalLattice p) :=
    (rho_lower_eq n χ p).symm
  have hz : (-zCoc n χ hf) p =
      -(leviCocycle (rationalCoefficientComponent n χ) ωU (leviHom γ)⁻¹
        ![1, lowerRadicalLattice p]) := rfl
  rw [e, hz, hE p]
  exact (eq_sub_of_add_eq key).trans (sub_eq_neg_add _ _)

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

end
