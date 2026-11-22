/-
Copyright (c) 2026 Yin-Kai Yu. Distributed under the Apache License, Version 2.0.
SPDX-License-Identifier: Apache-2.0
The Abel–Mellin identity and norm bound are adapted from Yin-Kai Yu's
https://github.com/YinkaiYu/zeta-zero-free-lean/blob/v1.2.0/Solution.lean.
This version reorganizes those proofs and adds a real-axis positivity lemma.
-/
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.SumCoeff

open Complex Set Filter MeasureTheory Asymptotics Topology

noncomputable section

namespace Formalism.ZF.MellinRemainder

private abbrev frac : ℝ → ℂ := ofReal ∘ Int.fract
private abbrev tail := (Ioi 1).indicator frac
abbrev remainder (s : ℂ) := ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * frac x

private lemma frac_bound (x : ℝ) : ‖frac x‖ ≤ 1 := by
  simpa [frac, Int.abs_fract] using (Int.fract_lt_one x).le

private lemma tail_smooth {s : ℂ} (hs : s.re < 0) : DifferentiableAt ℂ (mellin tail) s := by
  have hb x : ‖tail x‖ ≤ 1 := (norm_indicator_le_norm_self frac x).trans (frac_bound x)
  apply mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := s.re - 1)
  · exact (locallyIntegrableOn_const (1 : ℂ)).mono (by measurability)
      (by simpa using Eventually.of_forall hb)
  · exact isBigO_of_le _ (by simpa using hb)
  · exact hs
  · apply IsBigO.of_bound'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with x (hx : x < 1)
    simp [tail, hx.not_gt]
  · linarith

private lemma remainder_eq : remainder = fun s => mellin tail (-s) := by
  funext s
  rw [mellin, tail, ← indicator_smul, setIntegral_indicator measurableSet_Ioi]
  simp
  rfl

/-- Abel summation expresses the regular part of zeta using the fractional part. -/
lemma regular_eq {s : ℂ} (hs : 0 < s.re) : riemannZeta₀ s = 1 - s * remainder s := by
  apply (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd (isOpen_re_gt 0)).eqOn_of_preconnected_of_eventuallyEq
    (DifferentiableOn.analyticOnNhd (by
      intro z hz
      have := tail_smooth (s := -z) (by simpa using hz)
      rw [remainder_eq]
      fun_prop) (isOpen_re_gt 0))
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num) _ hs
  filter_upwards [(isOpen_re_gt 1).mem_nhds (x := 2) (by norm_num)] with z hz
  have h := LSeries_eq_mul_integral' 1 zero_le_one hz (by simp; rfl)
  simp [LSeries_one_eq_riemannZeta hz] at h
  have hi := integral_Ioi_cpow_of_lt (a := -z) (by simpa) zero_lt_one
  simp [← neg_sub z 1, neg_add_eq_sub, -neg_sub] at hi
  have hn : z ≠ 1 := by grind [one_re]
  suffices riemannZeta z = z * ((z - 1)⁻¹ - remainder z) by
    simp [riemannZeta₀, hn, this]
    field_simp
    ring
  rw [h, ← hi, ← integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa) zero_lt_one)
    ((integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).mul_bdd
      (by fun_prop : Measurable frac).aestronglyMeasurable (.of_forall frac_bound))]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxC := ofReal_ne_zero.mpr hx0.ne'
  simp [frac, Int.fract, ← Int.natCast_floor_eq_floor hx0.le,
    neg_add_eq_sub, cpow_neg, cpow_sub _ _ hxC]
  field [hxC]

lemma remainder_bound {s : ℂ} (hs : 0 < s.re) : ‖remainder s‖ ≤ 1 / s.re := by
  have he : -s.re - 1 < -1 := by linarith
  refine (norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt he zero_lt_one) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    grw [norm_mul, frac_bound]
    simp [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  · simp [integral_Ioi_rpow_of_lt he zero_lt_one]

/-- On the real axis the fractional-part remainder is real and nonnegative. -/
lemma remainder_ofReal (σ : ℝ) : ∃ r : ℝ, 0 ≤ r ∧ remainder (σ : ℂ) = (r : ℂ) := by
  refine ⟨∫ x in Ioi (1 : ℝ), x ^ (-σ - 1) * Int.fract x, ?_, ?_⟩
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (Int.fract_nonneg x)
  · rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have h := (zero_lt_one.trans hx : 0 < x).le
    push_cast [Complex.ofReal_cpow h]
    rfl

end Formalism.ZF.MellinRemainder
