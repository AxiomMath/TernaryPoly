module

public import TernaryPeriodPolynomials.ModularForm.PeriodHecke.Symbol
public import TernaryPeriodPolynomials.ModularForm.Symbol.ComplexLift
public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Map

@[expose] public section

noncomputable section

namespace TernaryPoly.BinaryCuspPeriod
open BinaryCuspSymbol BinaryCuspHeckeEndomorphism BinaryRationalHeckePrime BinaryModularSymbol

/-- The actual odd analytic period map intertwines genuine standard cusp Hecke with the literal
complexified rational modular-symbol Hecke, with its proved exact scalar p^(d+1). -/
theorem periodMap_hecke {d : ℕ} (hd : Even d) (f : Forms d) (p : ℕ) [Fact p.Prime] :
    periodMap d hd (T d p f) = (p : ℂ)^(d+1) •
      BinaryComplexPeriod.complexHecke d (primeDiagonal p) (periodMap d hd f) := by
  have h := congrArg (fun F : FunctionHom => F.val reference) (oddHom_hecke f p)
  rw [oddHom_reference hd] at h
  simp only [Submodule.coe_smul, LinearMap.smul_apply] at h
  rw [functionHom_hecke_reference d p (oddHom f) (periodMap d hd f)
    (by simpa only [periodMap_coe] using oddHom_reference hd f)] at h
  apply Subtype.ext
  apply evaluate_injective
  change evaluate (oddPeriod (T d p f)) =
    evaluate ((p : ℂ)^(d+1) •
      (BinaryComplexPeriod.complexHecke d (primeDiagonal p) (periodMap d hd f)).val)
  have hs : (p : ℂ)^(d+1) •
      (BinaryComplexPeriod.complexHecke d (primeDiagonal p) (periodMap d hd f)).val =
    (p : ℚ)^(d+1) •
      (BinaryComplexPeriod.complexHecke d (primeDiagonal p) (periodMap d hd f)).val := by
    rw [←Nat.cast_pow, ←Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hs, map_smul]
  exact h

/-- The kernel of the actual period map is stable under every genuine prime Hecke operator. -/
theorem periodMap_kernel_hecke_stable {d : ℕ} (hd : Even d) (p : ℕ) [Fact p.Prime]
    (f : Forms d) (hf : f ∈ LinearMap.ker (periodMap d hd)) :
    T d p f ∈ LinearMap.ker (periodMap d hd) := by
  change periodMap d hd (T d p f) = 0
  change periodMap d hd f = 0 at hf
  rw [periodMap_hecke, hf, map_zero, smul_zero]

end TernaryPoly.BinaryCuspPeriod
