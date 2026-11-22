/-
Adapted from Yin-Kai Yu's classical zero-free region proof, originally released under
the Apache License, Version 2.0 in the repository zeta-zero-free-lean.
This version uses the upstream declaration of ZeroFreeRegion.
-/
import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.MellinRemainder
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.LogDeriv

/- The entire completion of (s−1)ζ(s) allows all three logarithmic derivatives
   to be estimated with the same disk lemma, including the real center. -/
open Complex Metric
noncomputable section
namespace Formalism.ZF.ClassicalZeroFreeProof
variable {s z : ℂ}
open Formalism.ZF.MellinRemainder

private lemma entireFormula (hs : 0 < s.re) :
    riemannZeta₁ s = s * (1 - (s - 1) * remainder s) := by
  rw [riemannZeta₁, regular_eq hs]
  ring

private lemma completed_growth (h : 1/2≤z.re) : ‖riemannZeta₁ z‖≤(2*‖z‖+2)^2 := by
  have hp : 0<z.re := by linarith
  grw [entireFormula hp,norm_mul,norm_sub_le,norm_mul,norm_sub_le,remainder_bound hp,←h];norm_num
  nlinarith [norm_nonneg z]


/-- At the centre, every zero in the left half-plane makes a nonnegative contribution
to the real part of the local zero sum. One may retain any one of those contributions. -/
theorem landauCentralEstimate (hlocal : LandauLocal) {f : ℂ → ℂ} {B x : ℝ}
    (hd : Differentiable ℂ f) (h₀ : f 0 ≠ 0)
    (hbound : ∀ w, ‖w‖ ≤ 2⁻¹ → ‖f w‖ ≤ B * ‖f 0‖)
    (hzeros : ∀ ρ, f ρ = 0 → ρ.re ≤ 0)
    (hx : x = 0 ∨ ∃ ρ, ‖ρ‖ ≤ 6⁻¹ ∧ f ρ = 0 ∧ x ≤ -(ρ⁻¹).re) :
    x - (logDeriv f 0).re ≤ 144 * Real.log B := by
  classical
  have hB := one_le_of_le_mul_right₀ (norm_pos_iff.mpr h₀) (hbound 0 (by simp))
  obtain ⟨Z, m, hZ, hm, _, herror⟩ :=
    hlocal f 0 (1 / 2) B (by norm_num) hB hd.differentiableOn h₀
      (fun w hw => hbound w (by simpa [mem_closedBall, one_div] using hw))
  let weight (ρ : ℂ) := -(ρ⁻¹).re
  have nonneg (ρ : ℂ) (hρ : ρ ∈ Z) : 0 ≤ weight ρ := by
    exact neg_nonneg.mpr (by
      rw [Complex.inv_re]
      exact div_nonpos_of_nonpos_of_nonneg (hzeros _ ((hZ ρ).mp hρ).2) (normSq_nonneg ρ))
  have positiveTerms (ρ : ℂ) (hρ : ρ ∈ Z) : 0 ≤ (m ρ : ℝ) * weight ρ :=
    mul_nonneg (Nat.cast_nonneg _) (nonneg ρ hρ)
  have lower : x ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * weight ρ := by
    rcases hx with rfl | ⟨ρ, hr, hz, hmark⟩
    · exact Finset.sum_nonneg positiveTerms
    · have hρ : ρ ∈ Z := (hZ ρ).mpr ⟨by
        rw [mem_closedBall, dist_zero_right]
        norm_num at hr ⊢
        exact hr, hz⟩
      have hone : 1 ≤ (m ρ : ℝ) := by exact_mod_cast hm ρ hρ
      exact hmark.trans ((le_mul_of_one_le_left (nonneg ρ hρ) hone).trans
        (Finset.single_le_sum positiveTerms hρ))
  have term (ρ : ℂ) : ((m ρ : ℂ) / (0 - ρ)).re = (m ρ : ℝ) * weight ρ := by
    simp [weight, div_eq_mul_inv, Complex.mul_re]
  have error := herror 0 (Metric.mem_closedBall_self (by norm_num)) h₀
  have realError := (abs_le.mp ((Complex.abs_re_le_norm _).trans error)).1
  simp only [Complex.sub_re, Complex.re_sum, term] at realError
  change x - (deriv f 0 / f 0).re ≤ _
  linarith


/-- The logarithmic derivative of the completed zeta function on the half-plane of
absolute convergence. The extra simple pole comes from differentiating the factor s−1. -/
private lemma completed_log_deriv (ha : 1 < z.re) :
    riemannZeta₁ z ≠ 0 ∧ deriv riemannZeta₁ z / riemannZeta₁ z =
      (z - 1)⁻¹ + deriv riemannZeta z / riemannZeta z := by
  have := riemannZeta_ne_zero_of_one_lt_re ha
  have hn : z ≠ 1 := by grind [one_re]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]

/-- Evaluate the local zero estimate at heights 0, t and 2t and combine the
three bounds with Mertens' inequality. At height t the assumed zero contributes
its full reciprocal distance from the centre. -/
theorem from_local_zero_expansion (hlocal : LandauLocal) (hmertens : ThreeFourOne) :
    Formalism.ZF.ZeroFreeRegion := by
  refine ⟨(2 ^ 20)⁻¹, by positivity, fun s hn hs hz => ?_⟩
  let R := |s.im| + 2
  have hR : 2 ≤ R := by simp [R]
  have hL := Real.log_two_gt_d9.trans_le (Real.log_le_log zero_lt_two hR)
  have hlogPos : 0 < Real.log R := by linarith
  let d := (2 ^ 20 : ℝ)⁻¹ / Real.log R
  have hdPos : 0 < d := by positivity
  have hwidth : d ≤ 1 / 100 := (div_le_iff₀ hlogPos).2 (by linarith)
  change 1 - d ≤ s.re at hs
  have hzero : riemannZeta₁ s = 0 := by grind [riemannZeta_eq_inv_sub_mul]
  -- The Mellin remainder rules out a zero close to the real pole.
  have hheight : 1 / 2 ≤ |s.im| := by
    have hp : 0 < s.re := by linarith
    have eq : remainder s = (s - 1)⁻¹ := by grind [entireFormula hp, zero_re]
    have h := remainder_bound hp
    simp [eq, one_div, inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) hp] at h
    have hb := norm_le_abs_re_add_abs_im (s - 1)
    simp at hb
    grind [abs_eq_max_neg]
  -- Move the centre to the right of both the suspected zero and the line Re s = 1.
  let a := s.re + 5 * d
  have hgap : 2 ^ 2 * d ≤ a - 1 := by grind
  have ha : 1 < a := by linarith
  have completedAt v := completed_log_deriv (z := ⟨a, v⟩) ha
  have window v x (hv : |v| ≤ 2 * |s.im|) := landauCentralEstimate hlocal
    (f := fun w => riemannZeta₁ (⟨a, v⟩ + w))
    (B := (2 ^ 4 * R) ^ 2 / ‖riemannZeta₁ ⟨a, v⟩‖) (x := x)
    (by fun_prop) (by simpa using (completedAt v).1) (fun w hw => by
      simp [(completedAt v).1]
      grw [completed_growth (by grind [add_re, abs_re_le_norm w, abs_eq_max_neg]), norm_add_le, norm_le_abs_re_add_abs_im (⟨a, v⟩ : ℂ)]
      gcongr
      grind [abs_eq_max_neg, riemannZeta_ne_zero_of_one_le_re])
    (fun w he => by grind [completed_log_deriv (z := ⟨a, v⟩ + w), add_re])
  have realEstimate := window 0 0 (by simp) (.inl rfl)
  have markedEstimate := window s.im (5 * d)⁻¹ (by linarith) (.inr ⟨(-(5 * d) : ℝ), by
    simp [abs_of_pos hdPos]
    linarith, by
    convert hzero using 2
    simp [Complex.ext_iff, a], by simp⟩)
  have doubleEstimate := window (2 * s.im) 0 (by simp [abs_mul]) (.inl rfl)
  -- The absolute-value form of the three-height product bounds the sum of
  -- the three normalization logarithms appearing in the disk estimates.
  have productEstimate := (1 : DirichletCharacter ℂ 1).norm_LFunction_product_ge_one (sub_pos.mpr ha) s.im
  have poleDistance v := hgap.trans (re_le_norm ((⟨a, v⟩ : ℂ) - 1))
  simp (disch := grind [one_re]) [DirichletCharacter.LFunctionTrivChar,
    show ∀ x y : ℂ, x + y = ⟨_, _⟩ from fun _ _ => rfl, ofReal_def, riemannZeta_eq_inv_sub_mul] at productEstimate
  repeat grw [←poleDistance] at productEstimate
  -- Taking a logarithm turns the product into the sum appearing in the estimates.
  apply Real.log_nonneg at productEstimate
  simp (disch := first | positivity | simp [hlogPos.ne', (completedAt _).1])
    [-inv_re, logDeriv_apply, deriv_comp_const_add, (completedAt _).2,
      Real.log_div, Real.log_mul, Real.log_pow, d] at productEstimate realEstimate markedEstimate doubleEstimate
  simp [inv_re, normSq_apply] at realEstimate
  have realPole := inv_anti₀ (by positivity) hgap
  have heightBound := inv_anti₀ (by positivity) hheight
  grw [re_le_norm, norm_inv, ←abs_im_le_norm ((⟨a, _⟩ : ℂ) - 1)] at markedEstimate doubleEstimate <;> try (simp;grind)
  simp [d, abs_mul, div_eq_mul_inv, mul_inv_rev] at markedEstimate doubleEstimate realPole heightBound
  -- Use the already proved 3-4-1 inequality for the ordinary zeta function.
  have positive := hmertens a s.im ha
  simp [show ∀ x y : ℂ, x + y = ⟨_, _⟩ from fun _ _ => rfl,
    Complex.ofReal_def, Complex.mul_re, Complex.mul_im] at positive
  linarith [Real.log_le_self hlogPos.le, Real.log_two_lt_d9]

end Formalism.ZF.ClassicalZeroFreeProof

namespace Formalism.ZF

/-- The completed zeta function and the local zero expansion suffice for the original
conditional statement. The growth and small-height estimates are supplied internally. -/
theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf :=
  fun hmertens _ _ _ _ hlocal => ClassicalZeroFreeProof.from_local_zero_expansion hlocal hmertens

end Formalism.ZF
