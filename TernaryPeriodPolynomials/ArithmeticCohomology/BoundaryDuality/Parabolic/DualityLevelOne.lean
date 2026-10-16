module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIndexTwo
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.LevelOneInstance
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BinaryPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.Reflection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.PositiveWords
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.Action

@[expose] public section


/-!
# Parabolic Poincaré duality for `GL₂(ℤ)`

For a complex representation `M` of `GL₂(ℤ)`, the *parabolic* classes of `H¹(GL₂(ℤ), M)` are the
classes of crossed homomorphisms `z` whose restriction to the unipotent subgroup `⟨T⟩` is a
coboundary (`z T = T u - u`).  Such a crossed homomorphism automatically has a primitive triple at the
three special elements `S`, `T⁻¹`, `(S T⁻¹)⁻¹` of `SL₂(ℤ)` (the first and the last have finite order),
so the cup product of two parabolic classes is defined on the fundamental two-chain of the
three-punctured sphere `SL₂(ℤ)\ℍ`, corrected by the primitives (the cup formula).

For a perfect pairing `B : M × M' → ℂ` which is `SL₂(ℤ)`-invariant, changes sign under
`ε = diag(-1, 1)` (the twist of the coefficient pairing by the determinant, which the orientation
reversal of `ε` requires) and for which `-1` acts trivially on `M'`, this cup pairing is a bilinear
form on the parabolic classes; it is well defined on classes, and it is left nondegenerate: a
parabolic class pairing to zero with every parabolic class is zero.  The proof restricts to
`SL₂(ℤ)`, where `ε` acts through the reflection `σ` inverting `S` and `T`, and uses the
nondegeneracy of the `σ`-invariant parabolic classes of `SL₂(ℤ) = ⟨S⟩ *_{⟨S²⟩} ⟨U⟩`.

The binary forms `Sym^m ⊗ det^e` with the classical pairing `binaryPairing m` satisfy the
hypotheses when `m` is even and `e + e' - m` is odd.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH1 (Modular)

namespace LevelOne

/-- The integral points of `GL₂`. -/
abbrev GL2Z : Type := GeneralLinearGroup (Fin 2) ℤ

/-- The inclusion `SL₂(ℤ) → GL₂(ℤ)`. -/
abbrev toGL : Modular →* GL2Z := SpecialLinearGroup.toGL

/-- The reflection `ε = diag(-1, 1)` in `GL₂(ℤ)`. -/
def epsGL : GL2Z :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by decide, by decide⟩

/-- `ε² = 1`. -/
theorem epsGL_mul_self : epsGL * epsGL = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [epsGL, Matrix.mul_apply, Fin.sum_univ_two]

/-- The determinant of `ε` is `-1`. -/
theorem det_epsGL : (epsGL : GL2Z).val.det = -1 := by
  simp [epsGL, Matrix.det_fin_two]

/-- Conjugation by `ε` on `SL₂(ℤ)` is the reflection. -/
theorem toGL_modularReflection (n : Modular) :
    toGL (modularReflection n) = epsGL * toGL n * epsGL := by
  ext i j
  change (modularReflection n).val i j = _
  rw [modularReflection_apply]
  fin_cases i <;> fin_cases j <;>
    simp [epsGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- `GL₂(ℤ)` is the union of `SL₂(ℤ)` and `SL₂(ℤ) ε`, with `ε` acting as the reflection. -/
theorem indexTwo : IndexTwo toGL epsGL modularReflection where
  inj := SpecialLinearGroup.toGL_injective
  sq := epsGL_mul_self
  conj := toGL_modularReflection
  cover := by
    intro g
    have hunit : (g.val).det = 1 ∨ (g.val).det = -1 :=
      Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)
    rcases hunit with hg | hg
    · left
      exact ⟨⟨g.val, hg⟩, Units.ext rfl⟩
    · right
      have hgε : ((g * epsGL).val).det = 1 := by
        simp [Matrix.det_mul, hg, det_epsGL]
      refine ⟨⟨(g * epsGL).val, hgε⟩, ?_⟩
      have h : toGL ⟨(g * epsGL).val, hgε⟩ = g * epsGL := Units.ext rfl
      rw [h, mul_assoc, epsGL_mul_self, mul_one]
  not_mem := by
    intro n h
    have h1 : ((toGL n : GL2Z).val).det = 1 := n.property
    rw [h, det_epsGL] at h1
    exact absurd h1 (by norm_num)

section Primitives

/-- The element `S T⁻¹` of `SL₂(ℤ)`, of order three. -/
def modularCone : Modular := ModularGroup.S * ModularGroup.T⁻¹

/-- The matrix of `S T⁻¹`. -/
theorem modularCone_matrix : (modularCone : Modular).val = !![0, -1; 1, -1] := by
  unfold modularCone
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- `S T⁻¹` has order three. -/
theorem modularCone_cube : modularCone ^ 3 = 1 := by
  rw [pow_three']
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, modularCone_matrix,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- A crossed homomorphism of `SL₂(ℤ)` whose value at `T` is a coboundary has a primitive triple at
`S`, `T⁻¹`, `(S T⁻¹)⁻¹`. -/
theorem exists_primitive_of_cusp {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ Modular V} {z : Modular → V} (hz : IsCocycle ρ z)
    (hT : ∃ u : V, z ModularGroup.T = (ρ ModularGroup.T - 1) u) :
    ∃ v : V × V × V, IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ z v := by
  have hcube : (ModularGroup.S * ModularGroup.T⁻¹ : Modular) ^ 3 = 1 := modularCone_cube
  exact exists_primitive_of_exists (exists_sub_of_pow hz (by norm_num : 0 < 4) modularOrderFour)
    (exists_sub_inv hz hT)
    (exists_sub_of_pow hz (by norm_num : 0 < 3) (by rw [inv_pow, hcube, inv_one]))

/-- Conversely a primitive triple gives a coboundary at `T`. -/
theorem exists_cusp_of_primitive {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ Modular V} {z : Modular → V} (hz : IsCocycle ρ z) {v : V × V × V}
    (hv : IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ z v) :
    ∃ u : V, z ModularGroup.T = (ρ ModularGroup.T - 1) u := by
  obtain ⟨u, hu⟩ := exists_sub_inv hz (g := ModularGroup.T⁻¹) ⟨v.2.1, hv.2.1⟩
  rw [inv_inv] at hu
  exact ⟨u, hu⟩

end Primitives

section Representations

variable (M M' : Rep.{0, 0, 0} ℂ GL2Z)

/-- `ε` acts as an involution. -/
theorem rep_eps_sq {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ GL2Z X) (x : X) :
    ρ epsGL (ρ epsGL x) = x := by
  rw [← rep_mul_apply, epsGL_mul_self, map_one, Module.End.one_apply]

/-- `ε` intertwines the action of `h` with that of its reflection. -/
theorem rep_eps_equiv {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ GL2Z X)
    (h : Modular) (x : X) :
    ρ epsGL (ρ (toGL h) x) = ρ (toGL (modularReflection h)) (ρ epsGL x) := by
  have key : epsGL * toGL h = epsGL * toGL h * epsGL * epsGL := by
    rw [mul_assoc (epsGL * toGL h) epsGL epsGL, epsGL_mul_self, mul_one]
  calc ρ epsGL (ρ (toGL h) x) = ρ (epsGL * toGL h) x := (rep_mul_apply ρ _ _ _).symm
    _ = ρ (epsGL * toGL h * epsGL * epsGL) x := congrArg (fun y => ρ y x) key
    _ = ρ (epsGL * toGL h * epsGL) (ρ epsGL x) := rep_mul_apply ρ _ _ _
    _ = ρ (toGL (modularReflection h)) (ρ epsGL x) := by rw [toGL_modularReflection]

instance instFiniteDimensionalRes [FiniteDimensional ℂ M] :
    FiniteDimensional ℂ (Rep.res (toGL : Modular →* GL2Z) M) :=
  inferInstanceAs (FiniteDimensional ℂ M)

/-- The hypotheses on a pairing `B : M × M' → ℂ` of representations of `GL₂(ℤ)`: perfect, invariant
under `SL₂(ℤ)`, odd under `ε = diag(-1, 1)` (twisted by the determinant), and `-1 = S²` acting
trivially on `M'`. -/
structure TwistedPairing (B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ) : Prop where
  left : ∀ v : M, (∀ w : M', B v w = 0) → v = 0
  right : ∀ w : M', (∀ v : M, B v w = 0) → w = 0
  special : ∀ (n : Modular) (v : M) (w : M'),
    B (M.ρ (toGL n) v) (M'.ρ (toGL n) w) = B v w
  odd : ∀ (v : M) (w : M'), B (M.ρ epsGL v) (M'.ρ epsGL w) = (-1 : ℂ) * B v w
  central : ∀ w : M', M'.ρ (toGL (ModularGroup.S * ModularGroup.S)) w = w

variable {M M'} {B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ}

/-- The reflection data of `ε` on the restrictions to `SL₂(ℤ)`. -/
def reflectData (P : TwistedPairing M M' B) :
    ReflectData (Rep.res (toGL : Modular →* GL2Z) M).ρ (Rep.res (toGL : Modular →* GL2Z) M').ρ B
      ModularGroup.S ModularGroup.T⁻¹ (-1 : ℂ) where
  σ := modularReflection
  e := M.ρ epsGL
  e' := M'.ρ epsGL
  σσ := fun h => modularReflection_involutive h
  ee := fun v => rep_eps_sq M.ρ v
  ee' := fun w => rep_eps_sq M'.ρ w
  equiv := fun h v => rep_eps_equiv M.ρ h v
  equiv' := fun h w => rep_eps_equiv M'.ρ h w
  sa := modularReflection_S
  sg := by rw [map_inv, modularReflection_T]
  pair := P.odd
  invA := fun v w => P.special ModularGroup.S v w
  invG := fun v w => P.special ModularGroup.T⁻¹ v w

/-- **Left nondegeneracy of the `σ`-invariant parabolic crossed homomorphisms of `SL₂(ℤ)`**, in the
form required by the descent to `GL₂(ℤ)`. -/
theorem nlevelND [FiniteDimensional ℂ M] [FiniteDimensional ℂ M'] (P : TwistedPairing M M' B) :
    NLevelND toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ epsGL modularReflection := by
  intro z hz v hv hinvz zero
  exact LevelOneInstance.left_nondegenerate_reflect (Rep.res (toGL : Modular →* GL2Z) M)
    (Rep.res (toGL : Modular →* GL2Z) M') P.left P.right P.special (reflectData P) P.central
    hz hv hinvz zero

end Representations

section Model

variable {M M' : Rep.{0, 0, 0} ℂ GL2Z} {B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ}

/-- The inclusion of the one-cocycles of `M` into the functions `GL₂(ℤ) → M`. -/
def cocycleInclusion (M : Rep.{0, 0, 0} ℂ GL2Z) : groupCohomology.cocycles₁ M →ₗ[ℂ] (GL2Z → M) :=
  (groupCohomology.cocycles₁ M).subtype

/-- The projection of the one-cocycles of `M` to `H¹(GL₂(ℤ), M)`, as a linear map. -/
def projectH1 (M : Rep.{0, 0, 0} ℂ GL2Z) :
    groupCohomology.cocycles₁ M →ₗ[ℂ] groupCohomology.H1 M :=
  (groupCohomology.H1π M).hom

/-- One-cocycles of Mathlib's convention are crossed homomorphisms. -/
theorem isCocycle_cocycleInclusion (M : Rep.{0, 0, 0} ℂ GL2Z) (x : groupCohomology.cocycles₁ M) :
    IsCocycle M.ρ (cocycleInclusion M x) := by
  intro g h
  exact ((groupCohomology.mem_cocycles₁_iff _).1 x.2 g h).trans (add_comm _ _)

/-- Every crossed homomorphism is a one-cocycle. -/
theorem exists_cocycle_of_isCocycle (M : Rep.{0, 0, 0} ℂ GL2Z) (Z : GL2Z → M)
    (hZ : IsCocycle M.ρ Z) : ∃ y : groupCohomology.cocycles₁ M, cocycleInclusion M y = Z :=
  ⟨⟨Z, (groupCohomology.mem_cocycles₁_iff Z).2 fun g h => (hZ g h).trans (add_comm _ _)⟩, rfl⟩

/-- A one-cocycle is zero in `H¹` iff it is a coboundary. -/
theorem projectH1_eq_zero_iff (M : Rep.{0, 0, 0} ℂ GL2Z) (x : groupCohomology.cocycles₁ M) :
    projectH1 M x = 0 ↔ ∃ u : M, ∀ γ, cocycleInclusion M x γ = M.ρ γ u - u := by
  change groupCohomology.H1π M x = 0 ↔ _
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, fun γ => (congrFun hu γ).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, funext fun γ => (hu γ).symm⟩

/-- **The parabolic one-cocycles of `GL₂(ℤ)`**: those whose restriction to `SL₂(ℤ)` has a primitive
triple at `S`, `T⁻¹`, `(S T⁻¹)⁻¹`; equivalently (`mem_parabolicCocycles_iff`) those whose value at
`T` is a coboundary. -/
abbrev parabolicCocycles (M : Rep.{0, 0, 0} ℂ GL2Z) : Submodule ℂ (groupCohomology.cocycles₁ M) :=
  parabolicSub toGL M.ρ ModularGroup.S ModularGroup.T⁻¹ (cocycleInclusion M)

/-- **The parabolic classes of `H¹(GL₂(ℤ), M)`**: the classes of the parabolic one-cocycles. -/
abbrev parabolicH1 (M : Rep.{0, 0, 0} ℂ GL2Z) : Submodule ℂ (groupCohomology.H1 M) :=
  parabolicClasses toGL M.ρ ModularGroup.S ModularGroup.T⁻¹ (cocycleInclusion M) (projectH1 M)

/-- A one-cocycle is parabolic iff its restriction to `⟨T⟩` is a coboundary. -/
theorem mem_parabolicCocycles_iff (M : Rep.{0, 0, 0} ℂ GL2Z) (x : groupCohomology.cocycles₁ M) :
    x ∈ parabolicCocycles M ↔
      ∃ u : M, cocycleInclusion M x (toGL ModularGroup.T) = M.ρ (toGL ModularGroup.T) u - u := by
  constructor
  · intro hx
    obtain ⟨hc, v, hv⟩ := mem_parabolicCochains.mp (mem_parabolicSub.mp hx)
    exact exists_cusp_of_primitive (isCocycle_comp hc toGL) hv
  · intro hx
    refine mem_parabolicSub.mpr (mem_parabolicCochains.mpr
      ⟨isCocycle_cocycleInclusion M x, ?_⟩)
    exact exists_primitive_of_cusp (isCocycle_comp (isCocycle_cocycleInclusion M x) toGL) hx

/-- A class is parabolic iff it has a representative whose restriction to `⟨T⟩` is a
coboundary. -/
theorem mem_parabolicH1_iff (M : Rep.{0, 0, 0} ℂ GL2Z) (c : groupCohomology.H1 M) :
    c ∈ parabolicH1 M ↔ ∃ x : groupCohomology.cocycles₁ M,
      (∃ u : M, cocycleInclusion M x (toGL ModularGroup.T) = M.ρ (toGL ModularGroup.T) u - u) ∧
        projectH1 M x = c := by
  constructor
  · intro hc
    obtain ⟨x, hx, hxc⟩ := Submodule.mem_map.mp hc
    exact ⟨x, (mem_parabolicCocycles_iff M x).mp hx, hxc⟩
  · rintro ⟨x, hx, hxc⟩
    exact Submodule.mem_map.mpr ⟨x, (mem_parabolicCocycles_iff M x).mpr hx, hxc⟩

/-- **The parabolic cup pairing on `H¹(GL₂(ℤ), ·)`**: the bilinear form on the parabolic classes
given on representatives by the cup formula of the restrictions to `SL₂(ℤ)`, computed from a primitive
triple of the first class (`parabolicPairing_apply`). -/
def parabolicPairing (P : TwistedPairing M M' B) :
    parabolicH1 M →ₗ[ℂ] parabolicH1 M' →ₗ[ℂ] ℂ :=
  classPairing toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ P.special (cocycleInclusion M)
    (cocycleInclusion M') (projectH1 M) (projectH1 M')
    (fun x h => (projectH1_eq_zero_iff M x).1 h) (fun y h => (projectH1_eq_zero_iff M' y).1 h)

/-- **The value of the parabolic cup pairing on representatives.** -/
theorem parabolicPairing_apply (P : TwistedPairing M M' B) (x : groupCohomology.cocycles₁ M)
    (y : groupCohomology.cocycles₁ M') (hx : x ∈ parabolicCocycles M)
    (hy : y ∈ parabolicCocycles M') {v : M × M × M}
    (hv : IsPrimitive (M.ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
      (fun n => cocycleInclusion M x (toGL n)) v) :
    parabolicPairing P ⟨projectH1 M x, Submodule.mem_map_of_mem hx⟩
        ⟨projectH1 M' y, Submodule.mem_map_of_mem hy⟩ =
      cupFormula B (M'.ρ.comp toGL) ModularGroup.S ModularGroup.T⁻¹
        (fun n => cocycleInclusion M x (toGL n)) (fun n => cocycleInclusion M' y (toGL n)) v :=
  classPairing_eq_cupFormula toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ P.special
    (cocycleInclusion M) (cocycleInclusion M') (projectH1 M) (projectH1 M')
    (fun x h => (projectH1_eq_zero_iff M x).1 h) (fun y h => (projectH1_eq_zero_iff M' y).1 h)
    ⟨x, hx⟩ ⟨y, hy⟩ (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) hv

/-- **Left nondegeneracy of the parabolic cup pairing of `GL₂(ℤ)`** (parabolic Poincaré duality): a
parabolic class of `H¹(GL₂(ℤ), M)` which pairs to zero with every parabolic class of
`H¹(GL₂(ℤ), M')` is zero. -/
theorem parabolicPairing_left_nondegenerate [FiniteDimensional ℂ M] [FiniteDimensional ℂ M']
    (P : TwistedPairing M M' B) (cl : parabolicH1 M)
    (h : ∀ cl' : parabolicH1 M', parabolicPairing P cl cl' = 0) : cl = 0 :=
  classPairing_left_nondegenerate toGL M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ P.special
    (cocycleInclusion M) (cocycleInclusion M') (projectH1 M) (projectH1 M')
    (fun x => projectH1_eq_zero_iff M x) (fun y h => (projectH1_eq_zero_iff M' y).1 h)
    (exists_cocycle_of_isCocycle M')
    (cochainNondegenerate_of_nd indexTwo M.ρ M'.ρ B ModularGroup.S ModularGroup.T⁻¹ P.special
      (nlevelND P))
    cl h

end Model

section BinaryForms

open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance instFiniteDimensionalArithmeticBinaryRep (m : ℕ) (e : ℤ) :
    FiniteDimensional ℂ (arithmeticBinaryRep m e) :=
  inferInstanceAs (FiniteDimensional ℂ (GeneralEisenstein.Binary.HomogeneousPoly m))

/-- Elements of `SL₂(ℤ)` have determinant one in `GL₂(ℂ)`. -/
theorem det_map_toGL (n : Modular) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL n)) = 1 := by
  apply Units.ext
  have h1 : (n.val.map (Int.castRingHom ℂ)).det = 1 := by
    have equality := (Int.castRingHom ℂ).map_det n.val
    rw [Matrix.SpecialLinearGroup.det_coe n, map_one] at equality
    exact equality.symm
  exact h1

/-- The determinant of `ε` in `GL₂(ℂ)` is `-1`. -/
theorem val_det_map_epsGL :
    ((Matrix.GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) epsGL) : ℂˣ) : ℂ) =
      -1 := by
  change ((epsGL.val).map (Int.castRingHom ℂ)).det = -1
  simp [epsGL, Matrix.det_fin_two]

/-- `S² = -1` as a scalar matrix. -/
theorem toGL_S_mul_S :
    toGL (ModularGroup.S * ModularGroup.S) = GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ) := by
  apply Units.ext
  have h : ((toGL (ModularGroup.S * ModularGroup.S) : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
      (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S := rfl
  rw [h, ModularGroup.S_mul_S_eq, GeneralLinearGroup.coe_scalar]
  simp

/-- `-1 = S²` acts trivially on binary forms of even degree. -/
theorem arithmeticBinaryRep_central (m : ℕ) (hm : Even m) (e : ℤ) (w : arithmeticBinaryRep m e) :
    (arithmeticBinaryRep m e).ρ (toGL (ModularGroup.S * ModularGroup.S)) w = w := by
  have h2 : GeneralLinearGroup.map (Int.castRingHom ℂ)
      (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) =
        GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ) := by
    rw [GeneralLinearGroup.map_scalar]
    congr 1
    apply Units.ext
    simp
  change GeneralEisenstein.Binary.homogeneousAction m e
    (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL (ModularGroup.S * ModularGroup.S))) w = w
  rw [toGL_S_mul_S, h2]
  suffices H : ∀ w' : GeneralEisenstein.Binary.HomogeneousPoly m,
      GeneralEisenstein.Binary.homogeneousAction m e
        (GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ)) w' = w' from H w
  intro w'
  rw [binary_homogeneous_action_scalar]
  have hc : (((-1 : ℂˣ) : ℂ)) = -1 := by simp
  rw [hc, inv_neg_one, hm.neg_one_pow, (even_two_mul e).neg_one_zpow, one_mul, one_smul]

/-- **The classical pairing of binary forms satisfies the hypotheses** when the degree `m` is even
and the total determinant twist `e + e' - m` is odd. -/
theorem twistedPairing_arithmeticBinaryRep (m : ℕ) (e e' : ℤ) (hm : Even m)
    (hodd : Odd (e + e' - (m : ℤ))) :
    TwistedPairing (arithmeticBinaryRep m e) (arithmeticBinaryRep m e')
      (BinaryPairing.binaryPairing m) where
  left := fun v h => BinaryPairing.binaryPairing_left_eq_zero m h
  right := fun w h => BinaryPairing.binaryPairing_right_eq_zero m h
  special := by
    intro n v w
    exact BinaryPairing.binaryPairing_homogeneousAction_of_det_eq_one m e e'
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (toGL n)) (det_map_toGL n) v w
  odd := by
    intro v w
    have h := BinaryPairing.binaryPairing_homogeneousAction m e e'
      (GeneralLinearGroup.map (Int.castRingHom ℂ) epsGL) v w
    rw [val_det_map_epsGL, hodd.neg_one_zpow] at h
    exact h
  central := fun w => arithmeticBinaryRep_central m hm e' w

/-- **Parabolic Poincaré duality for binary forms**: for `m` even and `e + e' - m` odd, a parabolic
class of `H¹(GL₂(ℤ), Sym^m ⊗ det^e)` pairing to zero (via `binaryPairing m`) with every parabolic class
of `H¹(GL₂(ℤ), Sym^m ⊗ det^{e'})` is zero. -/
theorem arithmeticBinaryRep_left_nondegenerate (m : ℕ) (e e' : ℤ) (hm : Even m)
    (hodd : Odd (e + e' - (m : ℤ))) (cl : parabolicH1 (arithmeticBinaryRep m e))
    (h : ∀ cl' : parabolicH1 (arithmeticBinaryRep m e'),
      parabolicPairing (twistedPairing_arithmeticBinaryRep m e e' hm hodd) cl cl' = 0) :
    cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_arithmeticBinaryRep m e e' hm hodd) cl h

end BinaryForms

end LevelOne

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
