module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneTransitions

@[expose] public section


/-!
# The local `T_p` operator in edge coordinates at the good plane

For a relative two-cocycle `c` of the good-plane stabilizer `ΛG = {P(b, κ(m), d)}` (vanishing on
pairs of radical elements `u(b) = UK b`) the Hecke image `T c` for the explicit cosets of
`GoodPlaneCosets` is again relative, and its edge cocycle at a Levi element `L(m) = LK m`
(`m ∈ Γ₁'(3)`, acting on the radical through `κ(m) = δ⁻¹ m δ`) is
`ζ^{Tc}_m = σ₀ ζ_m + ∑_j L(m) κ_{k_j}(L(δ_j)⁻¹ · ζ_{δ_j}) + (coboundary)`,
where `ζ` is the edge cocycle of `c`, `α_j m = δ_j α_{k_j}` are the `Γ₁'(3)`-Hecke transitions
(`levelDelta`, `levelNext`), `σ₀` is the first coset representative and `κ_k` is the
corestriction-type sum over the cosets of `B_k ℤ²` (`kappaFun`). This is the exact good-plane
analogue of `IdentityPlaneEdge`, with `GL₂(ℤ)` replaced by `Γ₁'(3)` embedded through `κ`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeEdge

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open IdentityPlaneCosets (icast icast_add icast_sub icast_neg imul imul_one imul_neg imul_sub
  imul_mul epsP)
open GoodPlaneCosetData GoodPlaneFrame GoodPlaneModel GoodPlaneCosets GoodPlaneTransitions
open LevelThreeCosets (heckeRep levelNext levelDelta levelCosets levelEmbed levelEmbed_injective)
open AmbientHecke (nextRep deltaRep liftCocycle ambientHecke_lift)

/-! ### Group relations in `ΛG` -/

theorem UK_eq (b : ℤ × ℤ) : UK b = Gel b 1 1 := MK_eq_Gel b 1

theorem LK_eq (m : binaryArithmeticLevel) : LK m = Gel 0 m 1 := MK_eq_Gel 0 m

theorem MK_one (x : ℤ × ℤ) : MK x 1 = UK x := rfl

theorem MK_zero (m : binaryArithmeticLevel) : MK 0 m = LK m := rfl

theorem act_unit_one (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    act m 1 b = imul (kap m).val b := by
  simp [act]

theorem Mel_eq (b : ℤ × ℤ) (m : binaryArithmeticLevel) : MK b m = UK b * LK m := by
  simp only [MK_eq_Gel, UK_eq, LK_eq, Gel_mul, act_zero, add_zero, one_mul]

theorem Uel_mul (b b' : ℤ × ℤ) : UK b * UK b' = UK (b + b') := by
  simp only [UK_eq, Gel_mul, act_one, Units.val_one, one_smul, mul_one]

theorem Uel_zero : UK 0 = 1 := by
  rw [UK_eq]
  exact Gel_one

theorem Lel_mul (m m' : binaryArithmeticLevel) : LK m * LK m' = LK (m * m') := by
  simp only [LK_eq, Gel_mul, act_zero, add_zero, mul_one]

theorem Lel_one : LK 1 = 1 := by
  rw [LK_eq]
  exact Gel_one

theorem Lel_Uel (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    LK m * UK b = UK (imul (kap m).val b) * LK m := by
  rw [LK_eq, UK_eq, UK_eq, Gel_mul, Gel_mul, act_zero]
  simp only [act_unit_one, zero_add, add_zero, mul_one, one_mul]

theorem Uel_neg (b : ℤ × ℤ) : (UK b)⁻¹ = UK (-b) := by
  rw [inv_eq_iff_mul_eq_one, Uel_mul, add_neg_cancel, Uel_zero]

theorem inl_eq (u : RadicalLattice) : goodPlaneExtension.inl u = UK (Multiplicative.toAdd u) :=
  (radInc_eq u).trans (UK_eq _).symm

theorem splitting_eq (m : binaryArithmeticLevel) : goodPlaneSplitting (m, 1) = LK m :=
  (secL_apply m 1).trans (LK_eq m).symm

/-! ### Relative two-cocycles on `ΛG` -/

section Relative

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- The coefficient representation of `ΛG`. -/
abbrev Aρ : Rep ℂ ΛG := subgroupCoefficientRep ΛG ρ

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (UK a, UK b) = 0)

/-- `F(μ, x) = c(u(x), L(μ))`. -/
def Fc (μ : binaryArithmeticLevel) (x : ℤ × ℤ) : Aρ ρ := c (UK x, LK μ)

/-- The edge cocycle `ζ_μ(u(b)) = c(L(μ), u(κ(μ)⁻¹ b)) - c(u(b), L(μ))`. -/
def edgeFun (μ : binaryArithmeticLevel) (b : ℤ × ℤ) : Aρ ρ :=
  c (LK μ, UK (imul (kap μ⁻¹).val b)) - c (UK b, LK μ)

include hrel in
/-- `c(u(x), u(z) L(μ)) = F(μ, x + z) - ρ(u(x)) F(μ, z)`. -/
theorem relative_right (x z : ℤ × ℤ) (μ : binaryArithmeticLevel) :
    c (UK x, MK z μ) = Fc ρ c μ (x + z) - (Aρ ρ).ρ (UK x) (Fc ρ c μ z) := by
  have key := twoCocycle_relation (Aρ ρ) c (UK x) (UK z) (LK μ)
  rw [Uel_mul, hrel, add_zero, ← Mel_eq] at key
  unfold Fc
  rw [key]
  abel

include hrel in
/-- `c(u(x) L(μ), u(y)) = ρ(u(x)) ζ_μ(κ(μ) y) + F(μ, x + κ(μ) y) - F(μ, x)`. -/
theorem relative_left (x y : ℤ × ℤ) (μ : binaryArithmeticLevel) :
    c (MK x μ, UK y) = (Aρ ρ).ρ (UK x) (edgeFun ρ c μ (imul (kap μ).val y)) +
      Fc ρ c μ (x + imul (kap μ).val y) - Fc ρ c μ x := by
  have key := twoCocycle_relation (Aρ ρ) c (UK x) (LK μ) (UK y)
  rw [Lel_Uel, ← Mel_eq, ← Mel_eq, relative_right ρ c hrel] at key
  unfold edgeFun
  rw [imul_kap_cancel', map_sub]
  unfold Fc at key ⊢
  have : c (MK x μ, UK y) = (Aρ ρ).ρ (UK x) (c (LK μ, UK y)) +
      (c (UK (x + imul (kap μ).val y), LK μ) -
        (Aρ ρ).ρ (UK x) (c (UK (imul (kap μ).val y), LK μ))) - c (UK x, LK μ) := by
    rw [← key]
    abel
  rw [this]
  abel

end Relative

/-! ### The Hecke image in inhomogeneous coordinates -/

section Hecke

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- `ρ(g)` as an operator on the coefficient module of `ΛG`. -/
abbrev R (g : RationalGL3) : Module.End ℂ (Aρ ρ) := ρ g

theorem toRep_bijective : Function.Bijective (toRep p hp3) := by
  constructor
  · intro i i' h
    exact sExpl_injective p hp3 (congrArg Subtype.val h)
  · rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, rfl⟩

theorem reps_not_mem : ∀ s ∈ (goodPlaneCosets p hp3).representatives, s ∉ ΛG := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  exact sExpl_not_mem p i

/-- The local Hecke image of an inhomogeneous cocycle. -/
def heckeTwo (c : groupCohomology.cocycles₂ (Aρ ρ)) : groupCohomology.cocycles₂ (Aρ ρ) :=
  ambientCocycleToGroup ΛG ρ (LocalHecke.cocycleAction ρ (goodPlaneCosets p hp3)
    (liftCocycle (goodPlaneCosets p hp3) ρ c))

theorem heckeTwo_apply (c : groupCohomology.cocycles₂ (Aρ ρ)) (g h : ΛG) :
    heckeTwo p hp3 ρ c (g, h) = ∑ i : SIdx p, R ρ (sExpl p i)
      (c (deltaRep (goodPlaneCosets p hp3) g (toRep p hp3 i),
        deltaRep (goodPlaneCosets p hp3) h
          (nextRep (goodPlaneCosets p hp3) g (toRep p hp3 i)))) := by
  rw [heckeTwo, ambientHecke_lift (goodPlaneCosets p hp3) (reps_not_mem p hp3) ρ c g h]
  exact (Fintype.sum_bijective (toRep p hp3) (toRep_bijective p hp3) _ _ (fun i => rfl)).symm

theorem levelDelta_one' (j : Option (Fin p.val)) : levelDelta p hp3 1 j = 1 := by
  symm
  apply (levelCosets p hp3).delta_unique levelEmbed_injective
  change levelEmbed 1 = heckeRep p j * levelEmbed 1 * (heckeRep p (levelNext p hp3 1 j))⁻¹
  rw [levelNext_one]
  simp

theorem delta_U_some (x : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (goodPlaneCosets p hp3) (UK x) (toRep p hp3 (some (j, r))) =
      UK (-quotVec p j (wint p j r - x)) := by
  rw [show UK x = MK x 1 from rfl, delta_some, levelDelta_one', transVec_one, map_one,
    Units.val_one, imul_one, MK_one]

theorem next_U_some (x : ℤ × ℤ) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (goodPlaneCosets p hp3) (UK x) (toRep p hp3 (some (j, r))) =
      toRep p hp3 (some (j, repIdx p j (wint p j r - x))) := by
  rw [show UK x = MK x 1 from rfl, next_some, nextIdx_one]

theorem delta_U_none (x : ℤ × ℤ) :
    deltaRep (goodPlaneCosets p hp3) (UK x) (toRep p hp3 none) = UK (epsP p • x) := by
  rw [show UK x = MK x 1 from rfl, delta_none, MK_one]

theorem next_U_none (x : ℤ × ℤ) :
    nextRep (goodPlaneCosets p hp3) (UK x) (toRep p hp3 none) = toRep p hp3 none := by
  rw [show UK x = MK x 1 from rfl, next_none]

theorem delta_L_none (m : binaryArithmeticLevel) :
    deltaRep (goodPlaneCosets p hp3) (LK m) (toRep p hp3 none) = LK m := by
  rw [show LK m = MK 0 m from rfl, delta_none, smul_zero]

theorem next_L_none (m : binaryArithmeticLevel) :
    nextRep (goodPlaneCosets p hp3) (LK m) (toRep p hp3 none) = toRep p hp3 none := by
  rw [show LK m = MK 0 m from rfl, next_none]

theorem delta_L_some (m : binaryArithmeticLevel) (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (goodPlaneCosets p hp3) (LK m) (toRep p hp3 (some (j, r))) =
      MK (-imul (kap (levelDelta p hp3 m j)).val
        (quotVec p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))))
        (levelDelta p hp3 m j) := by
  rw [show LK m = MK 0 m from rfl, delta_some, transVec_zero]

theorem next_L_some (m : binaryArithmeticLevel) (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (goodPlaneCosets p hp3) (LK m) (toRep p hp3 (some (j, r))) =
      toRep p hp3 (some (levelNext p hp3 m j,
        repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r)))) := by
  rw [show LK m = MK 0 m from rfl, next_some, nextIdx_zero]

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (UK a, UK b) = 0)

include hrel in
/-- **The Hecke image of a relative cocycle is relative.** -/
theorem heckeTwo_relative (a b : ℤ × ℤ) : heckeTwo p hp3 ρ c (UK a, UK b) = 0 := by
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

variable (p : Nat.Primes) (hp3 : p.val ≠ 3) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- The corestriction-type sum `κ_k ξ (x) = ∑_{r} ρ(s_{k,r}) ξ(-B_k⁻¹(w_{k,r} - x))`. -/
def kappaFun (k : Option (Fin p.val)) (ξ : ℤ × ℤ → Aρ ρ) (x : ℤ × ℤ) : Aρ ρ :=
  ∑ r : Fin p.val, R ρ (sExpl p (some (k, r))) (ξ (-quotVec p k (wint p k r - x)))

/-- The Levi translate `(ν · ξ)(x) = ρ(L ν) ξ(κ(ν)⁻¹ x)`. -/
def conjFun (ν : binaryArithmeticLevel) (ξ : ℤ × ℤ → Aρ ρ) (x : ℤ × ℤ) : Aρ ρ :=
  R ρ (PK 0 ν) (ξ (imul (kap ν⁻¹).val x))

variable (c : groupCohomology.cocycles₂ (Aρ ρ)) (hrel : ∀ a b, c (UK a, UK b) = 0)

/-- The terms `Φ_j(r) = ρ(s_{j,r}) F(δ, -κ(δ) q)` of the radical coboundary. -/
def phiFun (m : binaryArithmeticLevel) (j : Option (Fin p.val)) (r : Fin p.val) : Aρ ρ :=
  R ρ (sExpl p (some (j, r))) (Fc ρ c (levelDelta p hp3 m j)
    (-imul (kap (levelDelta p hp3 m j)).val
      (quotVec p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r)))))

theorem R_mul (g h : RationalGL3) (v : Aρ ρ) : R ρ g (R ρ h v) = R ρ (g * h) v := by
  change ρ g (ρ h v) = ρ (g * h) v
  rw [map_mul]
  rfl

include hrel in
/-- **One coset term of the edge of the Hecke image.** -/
theorem edge_term (m : binaryArithmeticLevel) (b : ℤ × ℤ) (j : Option (Fin p.val))
    (r : Fin p.val) :
    R ρ (sExpl p (some (j, r)))
        (c (MK (-imul (kap (levelDelta p hp3 m j)).val
            (quotVec p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))))
            (levelDelta p hp3 m j),
          UK (-quotVec p (levelNext p hp3 m j)
            (wint p (levelNext p hp3 m j)
                (repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))) -
              imul (kap m⁻¹).val b)))) -
      R ρ (sExpl p (some (j, r)))
        (c (UK (-quotVec p j (wint p j r - b)),
          MK (-imul (kap (levelDelta p hp3 m j)).val
              (quotVec p (levelNext p hp3 m j)
                (imul (kap m⁻¹).val (wint p j (repIdx p j (wint p j r - b))))))
            (levelDelta p hp3 m j))) =
      R ρ (PK 0 m) (R ρ (sExpl p (some (levelNext p hp3 m j,
          repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r)))))
        (conjFun ρ (levelDelta p hp3 m j)⁻¹ (edgeFun ρ c (levelDelta p hp3 m j))
          (-quotVec p (levelNext p hp3 m j)
            (wint p (levelNext p hp3 m j)
                (repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))) -
              imul (kap m⁻¹).val b)))) -
        phiFun p hp3 ρ c m j r +
          R ρ (PK b 1) (phiFun p hp3 ρ c m j (repIdx p j (wint p j r - b))) := by
  rw [relative_left ρ c hrel, relative_right ρ c hrel, mixed_cancel]
  have hlevi := levi_product p hp3 m j r
  have hrad := radical_product p b j r
  rw [transVec_zero, nextIdx_zero] at hlevi
  simp only [map_add, map_sub]
  have e1 : R ρ (sExpl p (some (j, r))) ((Aρ ρ).ρ (UK (-imul (kap (levelDelta p hp3 m j)).val
      (quotVec p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r)))))
      (edgeFun ρ c (levelDelta p hp3 m j) (imul (kap (levelDelta p hp3 m j)).val
        (-quotVec p (levelNext p hp3 m j)
          (wint p (levelNext p hp3 m j)
              (repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))) -
            imul (kap m⁻¹).val b))))) =
      R ρ (PK 0 m) (R ρ (sExpl p (some (levelNext p hp3 m j,
          repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r)))))
        (conjFun ρ (levelDelta p hp3 m j)⁻¹ (edgeFun ρ c (levelDelta p hp3 m j))
          (-quotVec p (levelNext p hp3 m j)
            (wint p (levelNext p hp3 m j)
                (repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))) -
              imul (kap m⁻¹).val b)))) := by
    change R ρ (sExpl p (some (j, r))) (R ρ (PK _ 1) _) = _
    rw [R_mul, hlevi, conjFun, inv_inv, R_mul, R_mul]
  have e2 : R ρ (sExpl p (some (j, r))) ((Aρ ρ).ρ (UK (-quotVec p j (wint p j r - b)))
      (Fc ρ c (levelDelta p hp3 m j) (-imul (kap (levelDelta p hp3 m j)).val
        (quotVec p (levelNext p hp3 m j)
          (imul (kap m⁻¹).val (wint p j (repIdx p j (wint p j r - b)))))))) =
      R ρ (PK b 1) (phiFun p hp3 ρ c m j (repIdx p j (wint p j r - b))) := by
    change R ρ (sExpl p (some (j, r))) (R ρ (PK _ 1) _) = _
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
theorem edge_heckeTwo (m : binaryArithmeticLevel) (b : ℤ × ℤ) :
    edgeFun ρ (heckeTwo p hp3 ρ c) m b =
      R ρ (sExpl p none) (edgeFun ρ c m (epsP p • b)) +
        ∑ j : Option (Fin p.val), R ρ (PK 0 m)
          (kappaFun p ρ (levelNext p hp3 m j)
            (conjFun ρ (levelDelta p hp3 m j)⁻¹ (edgeFun ρ c (levelDelta p hp3 m j)))
            (imul (kap m⁻¹).val b)) +
        (R ρ (PK b 1) (∑ j : Option (Fin p.val), ∑ r : Fin p.val, phiFun p hp3 ρ c m j r) -
          ∑ j : Option (Fin p.val), ∑ r : Fin p.val, phiFun p hp3 ρ c m j r) := by
  change heckeTwo p hp3 ρ c (LK m, UK (imul (kap m⁻¹).val b)) -
    heckeTwo p hp3 ρ c (UK b, LK m) = _
  rw [heckeTwo_apply, heckeTwo_apply, Fintype.sum_option, Fintype.sum_option,
    delta_L_none, next_L_none, delta_U_none, delta_U_none, next_U_none, delta_L_none,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [delta_L_some, next_L_some, delta_U_some, next_U_some]
  have hsome : ∀ j : Option (Fin p.val),
      (∑ r : Fin p.val, R ρ (sExpl p (some (j, r)))
        (c (MK (-imul (kap (levelDelta p hp3 m j)).val
            (quotVec p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))))
            (levelDelta p hp3 m j),
          UK (-quotVec p (levelNext p hp3 m j)
            (wint p (levelNext p hp3 m j)
                (repIdx p (levelNext p hp3 m j) (imul (kap m⁻¹).val (wint p j r))) -
              imul (kap m⁻¹).val b))))) -
      (∑ r : Fin p.val, R ρ (sExpl p (some (j, r)))
        (c (UK (-quotVec p j (wint p j r - b)),
          MK (-imul (kap (levelDelta p hp3 m j)).val
              (quotVec p (levelNext p hp3 m j)
                (imul (kap m⁻¹).val (wint p j (repIdx p j (wint p j r - b))))))
            (levelDelta p hp3 m j)))) =
      R ρ (PK 0 m) (kappaFun p ρ (levelNext p hp3 m j)
          (conjFun ρ (levelDelta p hp3 m j)⁻¹ (edgeFun ρ c (levelDelta p hp3 m j)))
          (imul (kap m⁻¹).val b)) +
        (R ρ (PK b 1) (∑ r : Fin p.val, phiFun p hp3 ρ c m j r) -
          ∑ r : Fin p.val, phiFun p hp3 ρ c m j r) := by
    intro j
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl (fun r _ => edge_term p hp3 ρ c hrel m b j r)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum]
    have hlevi := (levi_bijective p hp3 m j).sum_comp
      (fun r' => R ρ (sExpl p (some (levelNext p hp3 m j, r')))
        (conjFun ρ (levelDelta p hp3 m j)⁻¹ (edgeFun ρ c (levelDelta p hp3 m j))
          (-quotVec p (levelNext p hp3 m j)
            (wint p (levelNext p hp3 m j) r' - imul (kap m⁻¹).val b))))
    have hrad := (radical_bijective p b j).sum_comp (phiFun p hp3 ρ c m j)
    rw [hlevi, hrad, kappaFun]
    abel
  rw [show ∀ (A B C D : Aρ ρ), A + C - (B + D) = (A - B) + (C - D) by intro A B C D; abel]
  rw [← Finset.sum_sub_distrib]
  simp only [hsome]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum]
  rw [edgeFun, imul_smul, map_sub, map_sum]
  abel

end Edge

end TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeEdge
