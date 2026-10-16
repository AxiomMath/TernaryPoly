module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Line
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Cocycle

@[expose] public section


/-!
# The good-line coordinate of the line source is nonzero (spherical, trivial character)

The headline `lineSource_cuspRes_goodLine_ne_zero` of `DetectLineSource` needs a one-cocycle `φ` of
`GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` with `φ m = Sw (α(σ m σ) 1)` and nonzero class, where
`σ = binaryPivotSwap` and `Sw = binarySwap`.  The period cocycle `ψ m = α(m) 1` of the sign-twisted
Eichler cocycle (`exists_lineLeviCocycleData_period_ne_zero`) is a cocycle of the same module with
nonzero class; the transported cocycle `m ↦ Sw (ψ (σ m σ))` (`dlCocycleOf`) has the required values
and nonzero class, because the swap of the binary variables intertwines the arithmetic action of
`σ g σ` with that of `g` (`dl_swap_rho`).  This gives the unconditional theorem
`lineSource_exists_cuspRes_goodLine_ne_zero`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (arithmeticBinaryRep binaryPivotSwap binaryPivotSwap_map)
open TernaryPeriodPolynomials.AnalyticClasses
  (binarySwap pivotConjugate binarySwap_binaryCoefficient)

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- The conjugation `m ↦ σ m σ` of `GL₂(ℤ)` by the pivot swap. -/
def dlIntPivot (m : GeneralLinearGroup (Fin 2) ℤ) : GeneralLinearGroup (Fin 2) ℤ :=
  binaryPivotSwap * m * binaryPivotSwap

theorem dl_pivot_mul_self {R : Type*} [CommRing R] :
    (binaryPivotSwap * binaryPivotSwap : GeneralLinearGroup (Fin 2) R) = 1 := by
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem dlIntPivot_mul (g h : GeneralLinearGroup (Fin 2) ℤ) :
    dlIntPivot (g * h) = dlIntPivot g * dlIntPivot h := by
  unfold dlIntPivot
  calc binaryPivotSwap * (g * h) * binaryPivotSwap
      = binaryPivotSwap * g * (binaryPivotSwap * binaryPivotSwap) * h * binaryPivotSwap := by
        rw [dl_pivot_mul_self, mul_one]
        simp only [mul_assoc]
    _ = (binaryPivotSwap * g * binaryPivotSwap) * (binaryPivotSwap * h * binaryPivotSwap) := by
        simp only [mul_assoc]

theorem dlIntPivot_involutive (m : GeneralLinearGroup (Fin 2) ℤ) :
    dlIntPivot (dlIntPivot m) = m := by
  unfold dlIntPivot
  calc binaryPivotSwap * (binaryPivotSwap * m * binaryPivotSwap) * binaryPivotSwap
      = (binaryPivotSwap * binaryPivotSwap) * m * (binaryPivotSwap * binaryPivotSwap) := by
        simp only [mul_assoc]
    _ = m := by rw [dl_pivot_mul_self, one_mul, mul_one]

theorem dlIntPivot_map (m : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (dlIntPivot m) =
      pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) m) := by
  unfold dlIntPivot pivotConjugate
  simp only [map_mul, binaryPivotSwap_map]

/-- The swap of the binary variables intertwines the arithmetic action of `σ g σ` with that of `g`,
in the determinant twist `-1`. -/
theorem dl_swap_rho_neg (g : GeneralLinearGroup (Fin 2) ℤ) (v : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (periodAct n (dlIntPivot g) v) = periodAct n g (binarySwap n v) := by
  have h1 := binaryCoefficient_map_int n (dlIntPivot g) v
  have h2 := binaryCoefficient_map_int n g (binarySwap n v)
  have h3 := binarySwap_binaryCoefficient (n := n)
    (GeneralLinearGroup.map (Int.castRingHom ℝ) g) v
  rw [dlIntPivot_map] at h1
  rw [h1, h2] at h3
  exact h3

/-- The arithmetic action of `GL₂(ℤ)` on binary forms in the determinant twist `0`, with values in
the forms. -/
abbrev dlAct (n : ℕ) (γ : GeneralLinearGroup (Fin 2) ℤ) (q : Binary.HomogeneousPoly (n + 1)) :
    Binary.HomogeneousPoly (n + 1) :=
  (arithmeticBinaryRep (n + 1) 0).ρ γ q

/-- The determinant twist `0` is the determinant twist `-1` times the determinant. -/
theorem dl_act_eq (g : GeneralLinearGroup (Fin 2) ℤ) (v : Binary.HomogeneousPoly (n + 1)) :
    dlAct n g v =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ) •
        periodAct n g v := by
  apply Subtype.ext
  change Binary.action 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) g) v.val =
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ) •
      Binary.action (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) g) v.val
  rw [Binary.action_apply, Binary.action_apply, smul_smul]
  congr 1
  have hne : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ)
      ≠ 0 := Units.ne_zero _
  change ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ) ^
      (0 : ℤ) = _ * ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) :
        ℂˣ) : ℂ) ^ (-1 : ℤ)
  rw [zpow_zero, _root_.zpow_neg_one, mul_inv_cancel₀ hne]

/-- Conjugation by the pivot swap preserves the complex determinant of an integral matrix. -/
theorem dl_det_pivot (g : GeneralLinearGroup (Fin 2) ℤ) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) (dlIntPivot g)) : ℂˣ) :
        ℂ) =
      ((GeneralLinearGroup.det (GeneralLinearGroup.map (Int.castRingHom ℂ) g) : ℂˣ) : ℂ) := by
  have hs : ((GeneralLinearGroup.det (binaryPivotSwap : GeneralLinearGroup (Fin 2) ℂ) : ℂˣ) :
      ℂ) = -1 := by
    rw [GeneralLinearGroup.val_det_apply]
    simp [binaryPivotSwap, Matrix.det_fin_two]
  unfold dlIntPivot
  simp only [map_mul, binaryPivotSwap_map, Units.val_mul, hs]
  ring

/-- The swap of the binary variables intertwines the arithmetic action of `σ g σ` with that of `g`,
in the determinant twist `0`. -/
theorem dl_swap_rho (g : GeneralLinearGroup (Fin 2) ℤ) (v : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (dlAct n (dlIntPivot g) v) = dlAct n g (binarySwap n v) := by
  rw [dl_act_eq (dlIntPivot g) v, dl_act_eq g (binarySwap n v), map_smul, dl_swap_rho_neg,
    dl_det_pivot]

/-- **The transported cocycle**: `m ↦ Sw (ψ (σ m σ))`. -/
def dlCocycleOf (n : ℕ) (ψ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0)) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  ⟨fun m => binarySwap n (lineCocyclePhi n ψ (dlIntPivot m)), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have hψ : lineCocyclePhi n ψ (dlIntPivot g * dlIntPivot h) =
        dlAct n (dlIntPivot g) (lineCocyclePhi n ψ (dlIntPivot h)) +
          lineCocyclePhi n ψ (dlIntPivot g) :=
      (groupCohomology.mem_cocycles₁_iff ψ).mp ψ.property (dlIntPivot g) (dlIntPivot h)
    change binarySwap n (lineCocyclePhi n ψ (dlIntPivot (g * h))) =
      dlAct n g (binarySwap n (lineCocyclePhi n ψ (dlIntPivot h))) +
        binarySwap n (lineCocyclePhi n ψ (dlIntPivot g))
    rw [dlIntPivot_mul, hψ, map_add, dl_swap_rho]⟩

theorem lineCocyclePhi_dlCocycleOf (ψ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (m : GeneralLinearGroup (Fin 2) ℤ) :
    lineCocyclePhi n (dlCocycleOf n ψ) m = binarySwap n (lineCocyclePhi n ψ (dlIntPivot m)) :=
  rfl

/-- **The transported cocycle has nonzero class** exactly when the original one has. -/
theorem dlCocycleOf_ne_zero (ψ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hψ : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) ψ ≠ 0) :
    groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n ψ) ≠ 0 := by
  intro h
  apply hψ
  obtain ⟨v₀, hv⟩ := (groupCohomology.H1π_eq_zero_iff _).mp h
  let v : Binary.HomogeneousPoly (n + 1) := v₀
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  refine ⟨binarySwap n v, ?_⟩
  funext m
  have hm : dlAct n (dlIntPivot m) v - v =
      binarySwap n (lineCocyclePhi n ψ (dlIntPivot (dlIntPivot m))) :=
    congrFun hv (dlIntPivot m)
  have hm2 : dlAct n (dlIntPivot m) v - v = binarySwap n (lineCocyclePhi n ψ m) := by
    rw [hm, dlIntPivot_involutive]
  have h3 := congrArg (binarySwap n) hm2
  rw [map_sub, dl_swap_rho, binarySwap_binarySwap'] at h3
  exact h3

/-- **The good-line coordinate of the line source is nonzero** (spherical cuspidal part, trivial
character, odd degree): there are line Levi cocycle data `E` such that every cocycle `z` evaluating
`lineSource D E` has nonzero good-line cusp coordinate. -/
theorem lineSource_exists_cuspRes_goodLine_ne_zero (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (hchi : D.chi = trivialCharacter) (odd : Odd n) :
    ∃ E : LineLeviCocycleData D.cusp n,
      ∀ {z : cocycles rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .line)},
        Evaluates D .line (lineSource D E) z →
          TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n D.chi .line
            true (classOf rationalLevel
              (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) ≠ 0 := by
  obtain ⟨E, ψ, hψ, hψ0⟩ := exists_lineLeviCocycleData_period_ne_zero D spherical odd
  refine ⟨E, fun {z} hz => ?_⟩
  refine lineSource_cuspRes_goodLine_ne_zero D E hchi odd.pos (dlCocycleOf n ψ) ?_
    (dlCocycleOf_ne_zero ψ hψ0) hz
  intro m
  exact congrArg (binarySwap n) ((hψ (dlIntPivot m)).trans
    (congrArg (fun A => E.α A 1) (dlIntPivot_map m)))

end TernaryPeriodPolynomials.SourceConstruction
