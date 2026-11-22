import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Mathlib.Analysis.Calculus.LogDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBoundOfZeroFree
import Mathlib.Analysis.Complex.HasPrimitives

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  obtain ⟨g, hg₀, hg⟩ := ((hf.deriv isOpen_ball).div hf hne).isExactOn_ball.with_val_at z₀ 0
  refine ⟨g, hg₀, hg, ?_⟩
  have hd : DifferentiableOn ℂ g (ball z₀ R) :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hf hd.cexp isOpen_ball isPreconnected_ball
    (fun _ _ => Complex.exp_ne_zero _) hne).mp fun z hz => by
      simp [logDeriv_apply, (hg z hz).cexp.deriv]
  intro z hz
  have hcenter := hc (mem_ball_self (pos_of_mem_ball hz))
  have hfc : f z₀ = c := by simpa [hg₀] using hcenter
  simpa [hfc] using hc hz

theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  have hDL : PI.DiscLog := fun _ _ _ hf hne => zflb_exists_log hf hne
  -- The general disk estimate has constant 4 * (r + R) / (R - r)².
  -- At r = R/2 this is 24/R. Approach log M from above to include M = 1.
  apply le_of_forall_pos_le_add
  intro ε hε
  let A := Real.log M + ε * R / 24
  have hA : Real.log M < A := by dsimp [A]; linarith [mul_pos hε hR]
  have hb (w) (hw : w ∈ ball z₀ R) : ‖f w‖ ≤ Real.exp A * ‖f z₀‖ := by
    apply (hbd w (ball_subset_closedBall hw)).trans
    gcongr
    exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hM)).1 hA.le
  have h := PI.EF.Loc.logDeriv_bound_of_zero_free hDL (half_pos hR) (half_lt_self hR)
    ((Real.log_nonneg hM).trans_lt hA) (hf.mono ball_subset_closedBall)
    (fun w hw => hne w (ball_subset_closedBall hw)) hb z hz
  calc _ ≤ _ := h
       _ = 24 * Real.log M / R + ε := by dsimp [A]; field_simp; ring

end Formalism.ZF
