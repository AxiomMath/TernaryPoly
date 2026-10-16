module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/- Ported from AxiomDeep (Claude Opus 5.5). -/
/-!
# Assembling coboundaries over the orbits of a coefficient set

For a subgroup `Γ` of `GL₃(ℚ)`, a `GL₃(ℚ)`-set `Y` and a representation `ρ`,
a degree-two homogeneous cocycle with values in functions `Y → V` is a coboundary
as soon as, for each point `y`, its `y`-coordinate is the coboundary of a cochain
that is equivariant for the stabilizer of `y` in `Γ`.  This is the elementary
half of Shapiro's lemma, proved directly in the ambient homogeneous model by
choosing orbit representatives.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.GraphPieces.EdgeOrbitAssembly

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Points of `Y` in the same `Γ`-orbit. -/
def orbitSetoid (Γ : Subgroup RationalGL3) (Y : Type) [MulAction RationalGL3 Y] : Setoid Y where
  r y y' := ∃ γ : Γ, γ.val • y' = y
  iseqv := by
    refine ⟨fun y => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro y y' ⟨γ, rfl⟩
      exact ⟨γ⁻¹, by simp [smul_smul]⟩
    · rintro y y' y'' ⟨γ, rfl⟩ ⟨δ, rfl⟩
      exact ⟨γ * δ, by simp [mul_smul]⟩

/-- The chosen representative of the orbit of `y`. -/
def representative (Γ : Subgroup RationalGL3) {Y : Type} [MulAction RationalGL3 Y] (y : Y) : Y :=
  (Quotient.mk (orbitSetoid Γ Y) y).out

theorem exists_transport (Γ : Subgroup RationalGL3) {Y : Type} [MulAction RationalGL3 Y] (y : Y) :
    ∃ γ : Γ, γ.val • representative Γ y = y := by
  have h : (orbitSetoid Γ Y).r (Quotient.mk (orbitSetoid Γ Y) y).out y :=
    Quotient.mk_out (s := orbitSetoid Γ Y) y
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ⁻¹, ?_⟩
  change (γ⁻¹ : Γ).val • (Quotient.mk (orbitSetoid Γ Y) y).out = y
  rw [← hγ]
  simp [smul_smul]

/-- A chosen element moving the representative to `y`. -/
def transport (Γ : Subgroup RationalGL3) {Y : Type} [MulAction RationalGL3 Y] (y : Y) : Γ :=
  Classical.choose (exists_transport Γ y)

theorem transport_spec (Γ : Subgroup RationalGL3) {Y : Type} [MulAction RationalGL3 Y] (y : Y) :
    (transport Γ y).val • representative Γ y = y :=
  Classical.choose_spec (exists_transport Γ y)

theorem representative_smul (Γ : Subgroup RationalGL3) {Y : Type} [MulAction RationalGL3 Y]
    (γ : Γ) (y : Y) : representative Γ (γ.val • y) = representative Γ y := by
  unfold representative
  congr 1
  exact Quotient.sound ⟨γ, rfl⟩

/-- The local hypothesis: every coordinate is a stabilizer-equivariant coboundary. -/
def LocallyExact (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V) (y : Y) : Prop :=
  ∃ b : (Fin 2 → RationalGL3) → V,
    (∀ γ : Γ, γ.val • y = y → ∀ x, b (fun i => γ.val * x i) = ρ γ.val (b x)) ∧
    ∀ x, z x y = b ![x 1, x 2] - b ![x 0, x 2] + b ![x 0, x 1]

/-- The chosen local primitive at the representative of the orbit of `y`. -/
def localPrimitive (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V)
    (exact : ∀ y, LocallyExact Γ ρ z y) (r : Y) : (Fin 2 → RationalGL3) → V :=
  Classical.choose (exact r)

theorem localPrimitive_equivariant (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V)
    (exact : ∀ y, LocallyExact Γ ρ z y) (r : Y) (γ : Γ) (fixed : γ.val • r = r)
    (x : Fin 2 → RationalGL3) :
    localPrimitive Γ ρ z exact r (fun i => γ.val * x i) =
      ρ γ.val (localPrimitive Γ ρ z exact r x) :=
  (Classical.choose_spec (exact r)).1 γ fixed x

theorem localPrimitive_boundary (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V)
    (exact : ∀ y, LocallyExact Γ ρ z y) (r : Y) (x : Fin 3 → RationalGL3) :
    z x r = localPrimitive Γ ρ z exact r ![x 1, x 2] -
      localPrimitive Γ ρ z exact r ![x 0, x 2] + localPrimitive Γ ρ z exact r ![x 0, x 1] :=
  (Classical.choose_spec (exact r)).2 x

/-- The assembled primitive. -/
def assembled (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V)
    (exact : ∀ y, LocallyExact Γ ρ z y) (x : Fin 2 → RationalGL3) (y : Y) : V :=
  ρ (transport Γ y).val
    (localPrimitive Γ ρ z exact (representative Γ y)
      (fun i => (transport Γ y).val⁻¹ * x i))

theorem assembled_equivariant (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : (Fin 3 → RationalGL3) → Y → V)
    (exact : ∀ y, LocallyExact Γ ρ z y) (γ : Γ) (x : Fin 2 → RationalGL3) (y : Y) :
    assembled Γ ρ z exact (fun i => γ.val * x i) y =
      ρ γ.val (assembled Γ ρ z exact x (γ.val⁻¹ • y)) := by
  have sameRep : representative Γ (γ.val⁻¹ • y) = representative Γ y := by
    have : γ.val⁻¹ • y = (γ⁻¹ : Γ).val • y := by simp
    rw [this, representative_smul]
  have haSpec := transport_spec Γ y
  have ha'Spec := transport_spec Γ (γ.val⁻¹ • y)
  rw [sameRep] at ha'Spec
  unfold assembled
  rw [sameRep]
  beta_reduce
  generalize transport Γ y = a at haSpec ⊢
  generalize transport Γ (γ.val⁻¹ • y) = a' at ha'Spec ⊢
  generalize representative Γ y = r at haSpec ha'Spec ⊢
  have fixed : (a⁻¹ * γ * a').val • r = r := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ha'Spec, smul_inv_smul]
    rw [← haSpec, inv_smul_smul]
  have vertices : (fun i => a.val⁻¹ * (γ.val * x i)) =
      (fun i => (a⁻¹ * γ * a').val * (a'.val⁻¹ * x i)) := by
    funext i
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [vertices, localPrimitive_equivariant Γ ρ z exact r (a⁻¹ * γ * a') fixed]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem assembled_boundary (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : cochains Γ (functionRepresentation ρ Y) 2)
    (exact : ∀ y, LocallyExact Γ ρ z.val y) (x : Fin 3 → RationalGL3) (y : Y) :
    z.val x y = assembled Γ ρ z.val exact ![x 1, x 2] y - assembled Γ ρ z.val exact ![x 0, x 2] y +
      assembled Γ ρ z.val exact ![x 0, x 1] y := by
  set a := transport Γ y with ha
  set r := representative Γ y with hr
  have haSpec : a.val • r = y := transport_spec Γ y
  have equivariant := congrFun (z.property a⁻¹ x) r
  change z.val (fun i => a.val⁻¹ * x i) r = ρ a.val⁻¹ (z.val x (a.val⁻¹⁻¹ • r)) at equivariant
  rw [inv_inv, haSpec] at equivariant
  have localEq := localPrimitive_boundary Γ ρ z.val exact r (fun i => a.val⁻¹ * x i)
  rw [equivariant] at localEq
  unfold assembled
  rw [← ha, ← hr]
  have v12 : (fun i => a.val⁻¹ * ![x 1, x 2] i) = ![(fun i => a.val⁻¹ * x i) 1, (fun i => a.val⁻¹ * x i) 2] := by
    funext i; fin_cases i <;> rfl
  have v02 : (fun i => a.val⁻¹ * ![x 0, x 2] i) = ![(fun i => a.val⁻¹ * x i) 0, (fun i => a.val⁻¹ * x i) 2] := by
    funext i; fin_cases i <;> rfl
  have v01 : (fun i => a.val⁻¹ * ![x 0, x 1] i) = ![(fun i => a.val⁻¹ * x i) 0, (fun i => a.val⁻¹ * x i) 1] := by
    funext i; fin_cases i <;> rfl
  rw [v12, v02, v01, ← map_sub, ← map_add, ← localEq, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

/-- **Orbit assembly.** Local stabilizer exactness at every point gives a global
`Γ`-equivariant primitive in functions on `Y`. -/
theorem exists_primitive (Γ : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    {Y : Type} [MulAction RationalGL3 Y] (z : cochains Γ (functionRepresentation ρ Y) 2)
    (exact : ∀ y, LocallyExact Γ ρ z.val y) :
    ∃ b : cochains Γ (functionRepresentation ρ Y) 1, differentialOne Γ _ b = z := by
  refine ⟨⟨fun x y => assembled Γ ρ z.val exact x y, ?_⟩, ?_⟩
  · intro γ x
    funext y
    exact assembled_equivariant Γ ρ z.val exact γ x y
  · apply Subtype.ext
    funext x y
    exact (assembled_boundary Γ ρ z exact x y).symm

end TernaryPeriodPolynomials.GraphPieces.EdgeOrbitAssembly
