module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ComplexLinear
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KConj
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# Additivity and homogeneity of the seed classes in the cusp form

Paper: Lemma C.3 (`ar:lem:seed`),, and the linear dependence of the classes on `f` used in the paper.

The seed `ω_f = dη` has coordinates `seedForm n (f ∘ ofComplex)` (`toPoly_d_etaForm`), additive and
homogeneous in `f`; hence the closed FORMS `cuspSeedInv` are additive and homogeneous (no choice of
moment primitives is involved), and so are their classes (`cuspSeedClass_add`, `cuspSeedClass_cmul`),
by `deRhamClass` and `deRhamClass_twist` with `T = ` multiplication by `c`. For the antiholomorphic
seed the scalar is conjugated. At the level `Γ(N)` this gives `gammaNSeedKerClass_add/_smul`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham

section Forms

variable {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {n : ℕ} {G : Type} [Group G]
  (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

/-- Two invariant closed forms on the face with the same coordinates are equal. -/
theorem invClosed_ext_coords {ρ : Representation ℝ G (Coef n)} {A : ZigZag.Action G faceSet}
    (X Y : ZigZag.invClosed isOpen_faceSet A ρ)
    (h : ∀ x ∈ faceSet, ∀ i j : Fin 4,
      Coef.toPoly (((X : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1]) =
      Coef.toPoly (((Y : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
        ![Pi.single i 1, Pi.single j 1])) : X = Y := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  apply ext2Face
  intro i j
  exact Coef.toPoly_injective (h x hx i j)

omit [Λ.HasDetOne] in
theorem cuspH_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspH Λ n (f + g) = fun z => cuspH Λ n f z + cuspH Λ n g z := by
  funext z; simp [cuspH]

theorem cuspH_smul (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspH Λ n (c • f) = fun z => c * cuspH Λ n f z := by
  funext z; simp [cuspH]

end Forms

section SeedForms

variable {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {n : ℕ} {G : Type} [Group G]
  (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

/-- Coordinates of the seed form. -/
theorem toPoly_cuspSeedInv (f' : CuspForm Λ ((n + 3 : ℕ) : ℤ)) {x : Face} (hx : x ∈ faceSet)
    (i j : Fin 4) :
    Coef.toPoly ((((cuspSeedInv D hΛ (f := f') : ZigZag.invClosed isOpen_faceSet D.action
        (D.rhoR n)) : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1]) =
      seedForm n (cuspH Λ n f') (ptOf x) i.castSucc j.castSucc :=
  PlaneData.toPoly_d_etaForm (cuspH Λ n f') n (cuspH_holo Λ n f') hx i j

/-- **The seed form is additive in the cusp form.** -/
theorem cuspSeedInv_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedInv D hΛ (f := f + g) = cuspSeedInv D hΛ (f := f) + cuspSeedInv D hΛ (f := g) := by
  refine invClosed_ext_coords _ _ fun x hx i j => ?_
  have e : (((cuspSeedInv D hΛ (f := f) + cuspSeedInv D hΛ (f := g) :
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1] =
      (((cuspSeedInv D hΛ (f := f) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
        Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1] +
      (((cuspSeedInv D hΛ (f := g) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
        Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1] := rfl
  rw [e, Coef.toPoly_add, toPoly_cuspSeedInv D hΛ (f + g) hx i j, toPoly_cuspSeedInv D hΛ f hx i j,
    toPoly_cuspSeedInv D hΛ g hx i j, cuspH_add]
  exact seedForm_add n _ _ _ _ _

omit [Λ.HasDetOne] in
/-- Multiplication by a complex scalar intertwines the coefficient representation of a plane group. -/
theorem intertwines_cmul_rhoR (c : ℂ) :
    Intertwines (cmulCLM n c) (D.rhoR n) (D.rhoR n) := by
  intro g v
  apply Coef.toPoly_injective
  rw [toPoly_rhoR, toPoly_cmulCLM, toPoly_cmulCLM, toPoly_rhoR, rho_C_mul]

/-- **The seed form is homogeneous in the cusp form**: `ω_{c f} = c ω_f` (twist by `c`). -/
theorem cuspSeedInv_cmul (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedInv D hΛ (f := c • f) =
      twInv (intertwines_cmul_rhoR D c) (cuspSeedInv D hΛ (f := f)) := by
  refine invClosed_ext_coords _ _ fun x hx i j => ?_
  have e : (((twInv (intertwines_cmul_rhoR D c) (cuspSeedInv D hΛ (f := f)) :
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1] =
      cmulCLM n c ((((cuspSeedInv D hΛ (f := f) : ZigZag.invClosed isOpen_faceSet D.action
        (D.rhoR n)) : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1]) := rfl
  rw [e, toPoly_cmulCLM, toPoly_cuspSeedInv D hΛ (c • f) hx i j, toPoly_cuspSeedInv D hΛ f hx i j,
    cuspH_smul, seedForm_smul]

/-- **The antiholomorphic seed form is additive in the cusp form.** -/
theorem cuspSeedConjInv_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedConjInv D hΛ (f := f + g) =
      cuspSeedConjInv D hΛ (f := f) + cuspSeedConjInv D hΛ (f := g) := by
  refine invClosed_ext_coords _ _ fun x hx i j => ?_
  have e : (((cuspSeedConjInv D hΛ (f := f) + cuspSeedConjInv D hΛ (f := g) :
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1] =
      (((cuspSeedConjInv D hΛ (f := f) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
        Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1] +
      (((cuspSeedConjInv D hΛ (f := g) : ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) :
        Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single i 1, Pi.single j 1] := rfl
  rw [e, Coef.toPoly_add, toPoly_cuspSeedConjInv n D hΛ (f + g) hx i j,
    toPoly_cuspSeedConjInv n D hΛ f hx i j, toPoly_cuspSeedConjInv n D hΛ g hx i j,
    cuspH_add, seedForm_add, map_add]

/-- **The antiholomorphic seed form is conjugate-homogeneous**: `conj ω_{c f} = c̄ conj ω_f`. -/
theorem cuspSeedConjInv_cmul (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedConjInv D hΛ (f := c • f) =
      twInv (intertwines_cmul_rhoR D (starRingEnd ℂ c)) (cuspSeedConjInv D hΛ (f := f)) := by
  refine invClosed_ext_coords _ _ fun x hx i j => ?_
  have e : (((twInv (intertwines_cmul_rhoR D (starRingEnd ℂ c)) (cuspSeedConjInv D hΛ (f := f)) :
      ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1] =
      cmulCLM n (starRingEnd ℂ c) ((((cuspSeedConjInv D hΛ (f := f) :
        ZigZag.invClosed isOpen_faceSet D.action (D.rhoR n)) : Form (F := Coef n) faceSet 2) :
          RawForm Face (Coef n) 2) x ![Pi.single i 1, Pi.single j 1]) := rfl
  rw [e, toPoly_cmulCLM, toPoly_cuspSeedConjInv n D hΛ (c • f) hx i j,
    toPoly_cuspSeedConjInv n D hΛ f hx i j, cuspH_smul, seedForm_smul]
  simp [MvPolynomial.map_C]

end SeedForms

section SeedClasses

variable {Λ : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] {n : ℕ} {G : Type} [Group G]
  (D : PlaneData G) (hΛ : ∀ g, (D.lam g : GL (Fin 2) ℝ) ∈ Λ)

/-- **The class of the seed is additive in the cusp form.** -/
theorem cuspSeedClass_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedClass D hΛ (f := f + g) = cuspSeedClass D hΛ (f := f) + cuspSeedClass D hΛ (f := g) := by
  rw [← deRhamClass_cuspSeed D hΛ (f := f + g), ← deRhamClass_cuspSeed D hΛ (f := f),
    ← deRhamClass_cuspSeed D hΛ (f := g), cuspSeedInv_add]
  exact (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)).map_add
    _ _

/-- **The class of the seed is homogeneous in the cusp form**, through the twist by `c`. -/
theorem cuspSeedClass_cmul (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedClass D hΛ (f := c • f) =
      (groupCohomology.map (MonoidHom.id G) (twMor (intertwines_cmul_rhoR D c)) 2).hom
        (cuspSeedClass D hΛ (f := f)) := by
  rw [← deRhamClass_cuspSeed D hΛ (f := c • f), ← deRhamClass_cuspSeed D hΛ (f := f),
    cuspSeedInv_cmul]
  exact deRhamClass_twist convex_faceSet faceSet_nonempty (intertwines_cmul_rhoR D c) _

/-- **The class of the antiholomorphic seed is additive in the cusp form.** -/
theorem cuspSeedConjClass_add (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedConjClass D hΛ (f := f + g) =
      cuspSeedConjClass D hΛ (f := f) + cuspSeedConjClass D hΛ (f := g) := by
  rw [← deRhamClass_cuspSeedConj D hΛ (f := f + g), ← deRhamClass_cuspSeedConj D hΛ (f := f),
    ← deRhamClass_cuspSeedConj D hΛ (f := g), cuspSeedConjInv_add]
  exact (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty D.action (D.rhoR n)).map_add
    _ _

/-- **The class of the antiholomorphic seed is conjugate-homogeneous**, through the twist by `c̄`. -/
theorem cuspSeedConjClass_cmul (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    cuspSeedConjClass D hΛ (f := c • f) =
      (groupCohomology.map (MonoidHom.id G) (twMor (intertwines_cmul_rhoR D (starRingEnd ℂ c))) 2).hom
        (cuspSeedConjClass D hΛ (f := f)) := by
  rw [← deRhamClass_cuspSeedConj D hΛ (f := c • f), ← deRhamClass_cuspSeedConj D hΛ (f := f),
    cuspSeedConjInv_cmul]
  exact deRhamClass_twist convex_faceSet faceSet_nonempty
    (intertwines_cmul_rhoR D (starRingEnd ℂ c)) _

end SeedClasses

section GammaNLevel

open CategoryTheory groupCohomology

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- Complexification intertwines the twist by `c` with multiplication by `c` (plane group `Γ_P`). -/
theorem complexifyG_map_cmul (c : ℂ) (x : H2 (Rep.of ((gammaNPlaneData N).rhoR n))) :
    complexifyG N n ((groupCohomology.map (MonoidHom.id (gammaNP N))
      (twMor (intertwines_cmul_rhoR (gammaNPlaneData N) c)) 2).hom x) = c • complexifyG N n x := by
  induction x using H2_induction_on with | _ c0 => ?_
  rw [groupCohomology.H2π_comp_map_apply, complexifyG_H2π, complexifyG_H2π, ← map_smul]
  congr 1

end GammaNLevel

section KerClasses

open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem gammaNSeedKerClass_val (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    ((gammaNSeedKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
      (gammaNRep N n)).ker) : H2 (gammaNRep N n)) =
      complexifyG N n (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) :=
  (complexifyG_cuspSeedClass f).symm

theorem gammaNSeedConjKerClass_val
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    ((gammaNSeedConjKerClass N n f : ↥(twoCohomologyRestriction (gammaNExt N).inl
      (gammaNRep N n)).ker) : H2 (gammaNRep N n)) =
      complexifyG N n (cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := f)) :=
  (complexifyG_cuspSeedConjClass f).symm

/-- **The holomorphic seed class at `Γ_P` is additive in the cusp form.** -/
theorem gammaNSeedKerClass_add
    (f g : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    gammaNSeedKerClass N n (f + g) = gammaNSeedKerClass N n f + gammaNSeedKerClass N n g := by
  apply Subtype.ext
  rw [Submodule.coe_add, gammaNSeedKerClass_val, gammaNSeedKerClass_val, gammaNSeedKerClass_val,
    cuspSeedClass_add, _root_.map_add]

/-- **The holomorphic seed class at `Γ_P` is complex-homogeneous in the cusp form.** -/
theorem gammaNSeedKerClass_smul (c : ℂ)
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    gammaNSeedKerClass N n (c • f) = c • gammaNSeedKerClass N n f := by
  apply Subtype.ext
  rw [Submodule.coe_smul, gammaNSeedKerClass_val, gammaNSeedKerClass_val, cuspSeedClass_cmul]
  exact complexifyG_map_cmul N n c _

/-- **The antiholomorphic seed class at `Γ_P` is additive in the cusp form.** -/
theorem gammaNSeedConjKerClass_add
    (f g : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    gammaNSeedConjKerClass N n (f + g) =
      gammaNSeedConjKerClass N n f + gammaNSeedConjKerClass N n g := by
  apply Subtype.ext
  rw [Submodule.coe_add, gammaNSeedConjKerClass_val, gammaNSeedConjKerClass_val,
    gammaNSeedConjKerClass_val, cuspSeedConjClass_add, _root_.map_add]

/-- **The antiholomorphic seed class at `Γ_P` is conjugate-homogeneous in the cusp form.** -/
theorem gammaNSeedConjKerClass_smul (c : ℂ)
    (f : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ)) :
    gammaNSeedConjKerClass N n (c • f) = (starRingEnd ℂ c) • gammaNSeedConjKerClass N n f := by
  apply Subtype.ext
  rw [Submodule.coe_smul, gammaNSeedConjKerClass_val, gammaNSeedConjKerClass_val,
    cuspSeedConjClass_cmul]
  exact complexifyG_map_cmul N n (starRingEnd ℂ c) _

end KerClasses

end TernaryPeriodPolynomials.Argument.EisensteinClass
