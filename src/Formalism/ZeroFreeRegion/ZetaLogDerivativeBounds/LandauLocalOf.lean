import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZF

lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  trans ∑ ρ ∈ Z, logDeriv (fun w : ℂ => (w - ρ) ^ m ρ) z
  · simpa only [Finset.prod_fn] using logDeriv_prod (s := Z) (x := z)
      (f := fun ρ w : ℂ => (w - ρ) ^ m ρ)
      (fun ρ hρ => pow_ne_zero _ (hz ρ hρ)) (fun _ _ => by fun_prop)
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

private theorem deriv_sub_mul_at_self {g : ℂ → ℂ} {ρ : ℂ} (hg : DifferentiableAt ℂ g ρ) :
    deriv (fun z => (z - ρ) * g z) ρ = g ρ := by
  have h : HasDerivAt (fun z => (z - ρ) * g z) (1 * g ρ + (ρ - ρ) * deriv g ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hg.hasDerivAt
  rw [h.deriv]
  ring

private theorem deriv_eq_zero_iff_mult_of_local_factor {f k : ℂ → ℂ} {ρ : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hk : DifferentiableAt ℂ k ρ) (hk0 : k ρ ≠ 0)
    (hf : f =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ n * k w) :
    (deriv f ρ = 0 → 2 ≤ n) ∧ (deriv f ρ ≠ 0 → n = 1) := by
  rw [hf.deriv_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hfun : (fun w => (w - ρ) ^ (j + 1) * k w) = fun w => (w - ρ) * ((w - ρ) ^ j * k w) := by
    funext w
    ring
  have hg : DifferentiableAt ℂ (fun w => (w - ρ) ^ j * k w) ρ := by
    fun_prop
  rw [hfun, deriv_sub_mul_at_self hg]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [pow_zero, one_mul]
    exact ⟨fun h => absurd h hk0, fun _ => by simp⟩
  · have h0 : (ρ - ρ) ^ j = 0 := by
      rw [sub_self]
      exact zero_pow hj.ne'
    rw [h0, zero_mul]
    exact ⟨fun _ => by omega, fun h => absurd rfl h⟩

/-- The local logarithmic-derivative expansion, with zero multiplicities. -/
theorem localZeroExpansionWithMultiplicity (hfac : ZeroFactor) (hlog : LogDerivBound)
    (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hf0 : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  let P (w : ℂ) := ∏ ρ ∈ Z, (w - ρ) ^ m ρ
  have hP₀ : P z₀ ≠ 0 := fun hzero => hf0 (by change f z₀ = P z₀ * h z₀ at hfz₀; simpa [hzero] using hfz₀)
  -- On the outer circle, every zero factor grows by at least a factor of two.
  have key_sphere (w : ℂ) (hw : ‖w - z₀‖ = r) :
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    have factor (ρ) (hρ : ρ ∈ Z) : 2 * ‖z₀ - ρ‖ ≤ ‖w - ρ‖ := by
      rw [norm_sub_rev z₀ ρ]
      have ht := dist_triangle w ρ z₀
      simp only [dist_eq_norm, hw] at ht
      linarith [hZball ρ hρ]
    have hprod : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖P z₀‖ ≤ ‖P w‖ := by
      simp only [P, norm_prod, norm_pow, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← mul_pow]
      gcongr with ρ hρ
      exact factor ρ hρ
    have hwmem : w ∈ closedBall z₀ r := by simp [mem_closedBall, dist_eq_norm, hw]
    have hb := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at hb
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hP₀)).mp (calc
      ‖P z₀‖ * (2 ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 ^ (∑ ρ ∈ Z, m ρ) * ‖P z₀‖) * ‖h w‖ := by ring
      _ ≤ ‖P w‖ * ‖h w‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ ≤ M * (‖P z₀‖ * ‖h z₀‖) := hb
      _ = ‖P z₀‖ * (M * ‖h z₀‖) := by ring)
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    exact one_le_pow₀ one_le_two
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  have horder (ρ : ℂ) (hρ : ρ ∈ Z) :
      (deriv f ρ = 0 → 2 ≤ m ρ) ∧ (deriv f ρ ≠ 0 → m ρ = 1) := by
    have hρsmall := ((hZ ρ).mp hρ).1
    have hρbig : ρ ∈ ball z₀ r := (closedBall_subset_ball (by linarith : r/3 < r)) hρsmall
    have hnhds : closedBall z₀ r ∈ 𝓝 ρ :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hρbig) ball_subset_closedBall
    refine deriv_eq_zero_iff_mult_of_local_factor
      (k := fun w => (∏ a ∈ Z.erase ρ, (w-a)^m a) * h w) (hm ρ hρ)
      (DifferentiableAt.mul (by fun_prop) (hh.differentiableAt hnhds)) ?_ ?_
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha =>
        pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm)) (hh0 ρ hρsmall)
    · filter_upwards [hnhds] with w hw
      rw [hfeq w hw, ← mul_assoc, Finset.mul_prod_erase Z (fun a => (w-a)^m a) hρ]
  refine ⟨Z, m, hZ, hm, fun ρ hρ => (horder ρ hρ).1, fun ρ hρ => (horder ρ hρ).2, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hsplit := (logDeriv_congr_nhds hev).eq_of_nhds
  change logDeriv f z = logDeriv (fun w => P w * h w) z at hsplit
  have hmul := hsplit.trans (logDeriv_mul (f := P) (g := h) z hPz hhz
    (by dsimp [P]; fun_prop) (hh.differentiableAt hnhds))
  have hPlog : logDeriv P z = _ := landauLocal_logDeriv_prod Z m z hzρ
  rw [show deriv f z / f z = logDeriv f z from rfl, hmul, hPlog, add_sub_cancel_left]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

/-- The zeta argument needs the zero count and the error bound. -/
theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  intro hfactor hlog f z₀ r M hr hM hf hf₀ hb
  obtain ⟨Z, m, hZ, hm, _, _, hcount, herr⟩ :=
    localZeroExpansionWithMultiplicity hfactor hlog f z₀ r M hr hM hf hf₀ hb
  exact ⟨Z, m, hZ, hm, hcount, herr⟩

end Formalism.ZF
