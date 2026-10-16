module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneTransitions
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge

@[expose] public section


/-!
# The local `T_p` operator in edge coordinates at the identity plane

For a relative two-cocycle `c` of the identity-plane stabilizer `Λ₀ = ℤ² ⋊ GL₂(ℤ)`, the Hecke
image `T c` (for the explicit cosets of `IdentityPlaneCosets`) is again relative, and its edge
cocycle at `m ∈ GL₂(ℤ)` is
`ζ^{Tc}_m = κ₀ ζ_m + ∑_j m · κ_{k_j}(μ_j⁻¹ · ζ_{μ_j}) + (coboundary)`,
where `ζ` is the edge cocycle of `c`, `a_j m = μ_j a_{k_j}` are the `GL₂` Hecke transitions,
`κ₀ ξ (u) = ρ(σ₀) ξ(u^{εp})` and `κ_k` is the corestriction-type sum over the cosets of `B_k ℤ²`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneEdge

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets IdentityPlaneTransitions AmbientHecke

/-! ### Group relations in `Λ₀` -/

theorem Mel_eq (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : Mel b m = Uel b * Lel m := by
  apply Subtype.ext
  change P (icast b) (integralEmbed m) 1 = P (icast b) (integralEmbed 1) 1 * P (icast 0) (integralEmbed m) 1
  rw [P_mul]
  congr 1 <;> simp [bmul_zero]

theorem Uel_mul (b b' : ℤ × ℤ) : Uel b * Uel b' = Uel (b + b') := by
  apply Subtype.ext
  change P (icast b) (integralEmbed 1) 1 * P (icast b') (integralEmbed 1) 1 =
    P (icast (b + b')) (integralEmbed 1) 1
  rw [P_mul, icast_add]
  congr 1 <;> simp [bmul_one]

theorem Uel_zero : Uel 0 = 1 := by
  apply Subtype.ext
  change P (icast 0) (integralEmbed 1) 1 = 1
  rw [← P_one]
  congr 1
  simp

theorem Lel_mul (m m' : GL (Fin 2) ℤ) : Lel m * Lel m' = Lel (m * m') := by
  apply Subtype.ext
  change P (icast 0) (integralEmbed m) 1 * P (icast 0) (integralEmbed m') 1 =
    P (icast 0) (integralEmbed (m * m')) 1
  rw [P_mul]
  congr 1 <;> simp [bmul_zero]

theorem Lel_one : Lel 1 = 1 := by
  apply Subtype.ext
  change P (icast 0) (integralEmbed 1) 1 = 1
  rw [← P_one]
  congr 1
  simp

theorem Lel_Uel (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    Lel m * Uel b = Uel (imul m.val b) * Lel m := by
  apply Subtype.ext
  change P (icast 0) (integralEmbed m) 1 * P (icast b) (integralEmbed 1) 1 =
    P (icast (imul m.val b)) (integralEmbed 1) 1 * P (icast 0) (integralEmbed m) 1
  rw [P_mul, P_mul]
  congr 1 <;> simp [bmul_zero, bmul_integralEmbed]

theorem Uel_neg (b : ℤ × ℤ) : (Uel b)⁻¹ = Uel (-b) := by
  rw [inv_eq_iff_mul_eq_one, Uel_mul, add_neg_cancel, Uel_zero]

theorem inl_eq (u : RadicalLattice) :
    identityPlaneRadicalInclusion u = Uel (Multiplicative.toAdd u) := by
  apply Subtype.ext
  change upperRadicalLattice u = P (icast (Multiplicative.toAdd u)) (integralEmbed 1) 1
  apply Units.ext
  rw [P_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperRadicalLattice, planeUnipotent, icast]

theorem splitting_eq (m : GL (Fin 2) ℤ) : identityPlaneLeviSection m = Lel m := by
  apply Subtype.ext
  change arithmeticLevi m = P (icast 0) (integralEmbed m) 1
  apply Units.ext
  rw [P_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [arithmeticLevi, planeLevi, planeBlock, icast, GeneralLinearGroup.map_apply, integralEmbed]

/-! ### Relative two-cocycles on `Λ₀` -/

section Relative

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- The coefficient representation of `Λ₀`. -/
abbrev Aρ : Rep ℂ Λ₀ := subgroupCoefficientRep Λ₀ ρ

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (Uel a, Uel b) = 0)

/-- `F(μ, x) = c(u(x), L(μ))`. -/
def Fc (μ : GL (Fin 2) ℤ) (x : ℤ × ℤ) : Aρ ρ := c (Uel x, Lel μ)

/-- The edge cocycle `ζ_μ(u(b)) = c(L(μ), u(μ⁻¹b)) - c(u(b), L(μ))`. -/
def edgeFun (μ : GL (Fin 2) ℤ) (b : ℤ × ℤ) : Aρ ρ :=
  c (Lel μ, Uel (imul (μ⁻¹ : GL (Fin 2) ℤ).val b)) - c (Uel b, Lel μ)

include hrel in
/-- `c(u(x), u(z) L(μ)) = F(μ, x + z) - ρ(u(x)) F(μ, z)`. -/
theorem relative_right (x z : ℤ × ℤ) (μ : GL (Fin 2) ℤ) :
    c (Uel x, Mel z μ) = Fc ρ c μ (x + z) - (Aρ ρ).ρ (Uel x) (Fc ρ c μ z) := by
  have key := twoCocycle_relation (Aρ ρ) c (Uel x) (Uel z) (Lel μ)
  rw [Uel_mul, hrel, add_zero, ← Mel_eq] at key
  unfold Fc
  rw [key]
  abel

include hrel in
/-- `c(u(x) L(μ), u(y)) = ρ(u(x)) ζ_μ(μ y) + F(μ, x + μ y) - F(μ, x)`. -/
theorem relative_left (x y : ℤ × ℤ) (μ : GL (Fin 2) ℤ) :
    c (Mel x μ, Uel y) = (Aρ ρ).ρ (Uel x) (edgeFun ρ c μ (imul μ.val y)) +
      Fc ρ c μ (x + imul μ.val y) - Fc ρ c μ x := by
  have key := twoCocycle_relation (Aρ ρ) c (Uel x) (Lel μ) (Uel y)
  rw [Lel_Uel, ← Mel_eq, ← Mel_eq, relative_right ρ c hrel] at key
  unfold edgeFun
  rw [imul_inv_cancel', map_sub]
  unfold Fc at key ⊢
  have : c (Mel x μ, Uel y) = (Aρ ρ).ρ (Uel x) (c (Lel μ, Uel y)) +
      (c (Uel (x + imul μ.val y), Lel μ) - (Aρ ρ).ρ (Uel x) (c (Uel (imul μ.val y), Lel μ))) -
        c (Uel x, Lel μ) := by
    rw [← key]
    abel
  rw [this]
  abel

end Relative

/-! ### The Hecke image in inhomogeneous coordinates -/

section Hecke

variable (p : Nat.Primes) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- `ρ(g)` as an operator on the coefficient module of `Λ₀`. -/
abbrev R (g : RationalGL3) : Module.End ℂ (Aρ ρ) := ρ g

theorem toRep_bijective : Function.Bijective (toRep p) := by
  constructor
  · intro i i' h
    exact sExpl_injective p (congrArg Subtype.val h)
  · rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, rfl⟩

theorem reps_not_mem : ∀ s ∈ (identityPlaneCosets p).representatives, s ∉ Λ₀ := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  exact sExpl_not_mem p i

/-- The local Hecke image of an inhomogeneous cocycle. -/
def heckeTwo (c : groupCohomology.cocycles₂ (Aρ ρ)) : groupCohomology.cocycles₂ (Aρ ρ) :=
  ambientCocycleToGroup Λ₀ ρ (LocalHecke.cocycleAction ρ (identityPlaneCosets p)
    (liftCocycle (identityPlaneCosets p) ρ c))

theorem heckeTwo_apply (c : groupCohomology.cocycles₂ (Aρ ρ)) (g h : Λ₀) :
    heckeTwo p ρ c (g, h) = ∑ i : SIdx p, R ρ (sExpl p i)
      (c (deltaRep (identityPlaneCosets p) g (toRep p i),
        deltaRep (identityPlaneCosets p) h (nextRep (identityPlaneCosets p) g (toRep p i)))) := by
  rw [heckeTwo, ambientHecke_lift (identityPlaneCosets p) (reps_not_mem p) ρ c g h]
  exact (Fintype.sum_bijective (toRep p) (toRep_bijective p) _ _ (fun i => rfl)).symm

theorem Mel_one (x : ℤ × ℤ) : Mel x 1 = Uel x := rfl

theorem Mel_zero (m : GL (Fin 2) ℤ) : Mel 0 m = Lel m := rfl

theorem delta_U_some (x : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (identityPlaneCosets p) (Uel x) (toRep p (some (j, r))) =
      Uel (-quotVec p j (wint p j r - x)) := by
  rw [← Mel_one, delta_some, arithmeticDelta_one, transVec_one, Units.val_one, imul_one, Mel_one]

theorem next_U_some (x : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (identityPlaneCosets p) (Uel x) (toRep p (some (j, r))) =
      toRep p (some (j, repIdx p j (wint p j r - x))) := by
  rw [← Mel_one, next_some, nextIdx_one]

theorem delta_U_none (x : ℤ × ℤ) :
    deltaRep (identityPlaneCosets p) (Uel x) (toRep p none) = Uel (epsP p • x) := by
  rw [← Mel_one, delta_none, Mel_one]

theorem next_U_none (x : ℤ × ℤ) :
    nextRep (identityPlaneCosets p) (Uel x) (toRep p none) = toRep p none := by
  rw [← Mel_one, next_none]

theorem delta_L_none (m : GL (Fin 2) ℤ) :
    deltaRep (identityPlaneCosets p) (Lel m) (toRep p none) = Lel m := by
  rw [← Mel_zero, delta_none, smul_zero, Mel_zero]

theorem next_L_none (m : GL (Fin 2) ℤ) :
    nextRep (identityPlaneCosets p) (Lel m) (toRep p none) = toRep p none := by
  rw [← Mel_zero, next_none]

theorem delta_L_some (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (identityPlaneCosets p) (Lel m) (toRep p (some (j, r))) =
      Mel (-imul (arithmeticDelta p m j).val
        (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))))
        (arithmeticDelta p m j) := by
  rw [← Mel_zero, delta_some, transVec_zero]

theorem next_L_some (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (identityPlaneCosets p) (Lel m) (toRep p (some (j, r))) =
      toRep p (some (arithmeticNext p m j,
        repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)))) := by
  rw [← Mel_zero, next_some, nextIdx_zero]

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (Uel a, Uel b) = 0)

include hrel in
/-- **The Hecke image of a relative cocycle is relative.** -/
theorem heckeTwo_relative (a b : ℤ × ℤ) : heckeTwo p ρ c (Uel a, Uel b) = 0 := by
  rw [heckeTwo_apply]
  apply Finset.sum_eq_zero
  intro i _
  cases i with
  | none =>
    rw [delta_U_none, next_U_none, delta_U_none, hrel, map_zero]
  | some jr =>
    obtain ⟨j, r⟩ := jr
    rw [delta_U_some, next_U_some, delta_U_some, hrel, map_zero]

end Hecke

/-! ### The edge of the Hecke image -/

section Edge

variable (p : Nat.Primes) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- The corestriction-type sum `κ_k ξ (x) = ∑_{r} ρ(s_{k,r}) ξ(-B_k⁻¹(w_{k,r} - x))`. -/
def kappaFun (k : Option (Fin p.val)) (ξ : ℤ × ℤ → Aρ ρ) (x : ℤ × ℤ) : Aρ ρ :=
  ∑ r : Fin p.val, R ρ (sExpl p (some (k, r))) (ξ (-quotVec p k (wint p k r - x)))

/-- The Levi translate `(ν · ξ)(x) = ρ(L ν) ξ(ν⁻¹ x)`. -/
def conjFun (ν : GL (Fin 2) ℤ) (ξ : ℤ × ℤ → Aρ ρ) (x : ℤ × ℤ) : Aρ ρ :=
  R ρ (Pint 0 ν) (ξ (imul (ν⁻¹ : GL (Fin 2) ℤ).val x))

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (Uel a, Uel b) = 0)

/-- The terms `Φ_j(r) = ρ(s_{j,r}) F(μ, -μ q)` of the radical coboundary. -/
def phiFun (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) (r : Fin p.val) : Aρ ρ :=
  R ρ (sExpl p (some (j, r))) (Fc ρ c (arithmeticDelta p m j)
    (-imul (arithmeticDelta p m j).val
      (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)))))

theorem R_mul (g h : RationalGL3) (v : Aρ ρ) : R ρ g (R ρ h v) = R ρ (g * h) v := by
  change ρ g (ρ h v) = ρ (g * h) v
  rw [map_mul]
  rfl

include hrel in
/-- **One coset term of the edge of the Hecke image.** -/
theorem edge_term (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    R ρ (sExpl p (some (j, r)))
        (c (Mel (-imul (arithmeticDelta p m j).val
            (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))))
            (arithmeticDelta p m j),
          Uel (-quotVec p (arithmeticNext p m j)
            (wint p (arithmeticNext p m j)
                (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
              imul (m⁻¹ : GL (Fin 2) ℤ).val b)))) -
      R ρ (sExpl p (some (j, r)))
        (c (Uel (-quotVec p j (wint p j r - b)),
          Mel (-imul (arithmeticDelta p m j).val
              (quotVec p (arithmeticNext p m j)
                (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b))))))
            (arithmeticDelta p m j))) =
      R ρ (Pint 0 m) (R ρ (sExpl p (some (arithmeticNext p m j,
          repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)))))
        (conjFun ρ (arithmeticDelta p m j)⁻¹ (edgeFun ρ c (arithmeticDelta p m j))
          (-quotVec p (arithmeticNext p m j)
            (wint p (arithmeticNext p m j)
                (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
              imul (m⁻¹ : GL (Fin 2) ℤ).val b)))) -
        phiFun p ρ c m j r + R ρ (Pint b 1) (phiFun p ρ c m j (repIdx p j (wint p j r - b))) := by
  rw [relative_left ρ c hrel, relative_right ρ c hrel, mixed_cancel]
  have hlevi := levi_product p m j r
  have hrad := radical_product p b j r
  rw [transVec_zero, nextIdx_zero] at hlevi
  simp only [map_add, map_sub]
  have e1 : R ρ (sExpl p (some (j, r))) ((Aρ ρ).ρ (Uel (-imul (arithmeticDelta p m j).val
      (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)))))
      (edgeFun ρ c (arithmeticDelta p m j) (imul (arithmeticDelta p m j).val
        (-quotVec p (arithmeticNext p m j)
          (wint p (arithmeticNext p m j)
              (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
            imul (m⁻¹ : GL (Fin 2) ℤ).val b))))) =
      R ρ (Pint 0 m) (R ρ (sExpl p (some (arithmeticNext p m j,
          repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r)))))
        (conjFun ρ (arithmeticDelta p m j)⁻¹ (edgeFun ρ c (arithmeticDelta p m j))
          (-quotVec p (arithmeticNext p m j)
            (wint p (arithmeticNext p m j)
                (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
              imul (m⁻¹ : GL (Fin 2) ℤ).val b)))) := by
    change R ρ (sExpl p (some (j, r))) (R ρ (Pint _ 1) _) = _
    rw [R_mul, hlevi, conjFun, inv_inv, R_mul, R_mul]
  have e2 : R ρ (sExpl p (some (j, r))) ((Aρ ρ).ρ (Uel (-quotVec p j (wint p j r - b)))
      (Fc ρ c (arithmeticDelta p m j) (-imul (arithmeticDelta p m j).val
        (quotVec p (arithmeticNext p m j)
          (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b)))))))) =
      R ρ (Pint b 1) (phiFun p ρ c m j (repIdx p j (wint p j r - b))) := by
    change R ρ (sExpl p (some (j, r))) (R ρ (Pint _ 1) _) = _
    rw [R_mul, hrad, ← R_mul]
    rfl
  rw [e1, e2]
  unfold phiFun
  abel

theorem imul_smul (A : Matrix (Fin 2) (Fin 2) ℤ) (z : ℤ) (x : ℤ × ℤ) :
    imul A (z • x) = z • imul A x := by
  simp only [imul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  ext <;> simp <;> ring

include hrel in
/-- **The edge cocycle of the local Hecke image.** -/
theorem edge_heckeTwo (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    edgeFun ρ (heckeTwo p ρ c) m b =
      R ρ (sExpl p none) (edgeFun ρ c m (epsP p • b)) +
        ∑ j : Option (Fin p.val), R ρ (Pint 0 m)
          (kappaFun p ρ (arithmeticNext p m j)
            (conjFun ρ (arithmeticDelta p m j)⁻¹ (edgeFun ρ c (arithmeticDelta p m j)))
            (imul (m⁻¹ : GL (Fin 2) ℤ).val b)) +
        (R ρ (Pint b 1) (∑ j : Option (Fin p.val), ∑ r : Fin p.val, phiFun p ρ c m j r) -
          ∑ j : Option (Fin p.val), ∑ r : Fin p.val, phiFun p ρ c m j r) := by
  change heckeTwo p ρ c (Lel m, Uel (imul (m⁻¹ : GL (Fin 2) ℤ).val b)) -
    heckeTwo p ρ c (Uel b, Lel m) = _
  rw [heckeTwo_apply, heckeTwo_apply, Fintype.sum_option, Fintype.sum_option,
    delta_L_none, next_L_none, delta_U_none, delta_U_none, next_U_none, delta_L_none,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [delta_L_some, next_L_some, delta_U_some, next_U_some]
  have hsome : ∀ j : Option (Fin p.val),
      (∑ r : Fin p.val, R ρ (sExpl p (some (j, r)))
        (c (Mel (-imul (arithmeticDelta p m j).val
            (quotVec p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))))
            (arithmeticDelta p m j),
          Uel (-quotVec p (arithmeticNext p m j)
            (wint p (arithmeticNext p m j)
                (repIdx p (arithmeticNext p m j) (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j r))) -
              imul (m⁻¹ : GL (Fin 2) ℤ).val b))))) -
      (∑ r : Fin p.val, R ρ (sExpl p (some (j, r)))
        (c (Uel (-quotVec p j (wint p j r - b)),
          Mel (-imul (arithmeticDelta p m j).val
              (quotVec p (arithmeticNext p m j)
                (imul (m⁻¹ : GL (Fin 2) ℤ).val (wint p j (repIdx p j (wint p j r - b))))))
            (arithmeticDelta p m j)))) =
      R ρ (Pint 0 m) (kappaFun p ρ (arithmeticNext p m j)
          (conjFun ρ (arithmeticDelta p m j)⁻¹ (edgeFun ρ c (arithmeticDelta p m j)))
          (imul (m⁻¹ : GL (Fin 2) ℤ).val b)) +
        (R ρ (Pint b 1) (∑ r : Fin p.val, phiFun p ρ c m j r) -
          ∑ r : Fin p.val, phiFun p ρ c m j r) := by
    intro j
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl (fun r _ => edge_term p ρ c hrel m b j r)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum]
    have hlevi := (levi_bijective p m j).sum_comp (fun r' => R ρ (sExpl p (some (arithmeticNext p m j, r')))
      (conjFun ρ (arithmeticDelta p m j)⁻¹ (edgeFun ρ c (arithmeticDelta p m j))
        (-quotVec p (arithmeticNext p m j)
          (wint p (arithmeticNext p m j) r' - imul (m⁻¹ : GL (Fin 2) ℤ).val b))))
    have hrad := (radical_bijective p b j).sum_comp (phiFun p ρ c m j)
    rw [hlevi, hrad, kappaFun]
    abel
  rw [show ∀ (A B C D : Aρ ρ), A + C - (B + D) = (A - B) + (C - D) by intro A B C D; abel]
  rw [← Finset.sum_sub_distrib]
  simp only [hsome]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum]
  rw [edgeFun, imul_smul, map_sub, map_sum]
  abel

end Edge

end TernaryPeriodPolynomials.Spectral.IdentityPlaneEdge
