import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

private theorem closedBall_mem_nhds_of_mem_closedBall_lt {z₀ z : ℂ} {r R₁ : ℝ} (hR : R₁ < r)
    (hz : z ∈ Metric.closedBall z₀ R₁) : Metric.closedBall z₀ r ∈ 𝓝 z :=
  Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hR hz))
    Metric.ball_subset_closedBall

private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h

theorem exists_factorization_of_sum_order (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf hZ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, ?_, ?_⟩
    · intro z hz hfz
      have hzZ := hzero z hz hfz
      have han : AnalyticAt ℂ f z := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hz)
      have hord : analyticOrderAt f z = 0 := by
        rw [← natCast_analyticOrderNatAt_of_ne_top (htop z hzZ)]
        simp [h0 z hzZ]
      exact (han.analyticOrderAt_eq_zero.mp hord) hfz
    · intro z _
      rw [Finset.prod_eq_one (fun ρ hρ => by rw [h0 ρ hρ, pow_zero]), one_mul]
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hanρ₀ : AnalyticAt ℂ f ρ₀ := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := by
      by_contra hne
      apply hρ₀
      have h0 : analyticOrderAt f ρ₀ = 0 := hanρ₀.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0]
    let g := dslope f ρ₀
    have hfg (z : ℂ) : f z = (z - ρ₀) * g z := (sub_smul_dslope_of_zero hfρ₀ z).symm
    have hgd : DifferentiableOn ℂ g (Metric.closedBall z₀ r) :=
      (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)).mpr hf
    have hfeq : f = (fun z : ℂ => z - ρ₀) * g := funext hfg
    have keyN (ρ) (hρ : ρ ∈ Z) :
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := by
      have ha := hgd.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR (hZ ρ hρ))
      have ht := htop ρ hρ
      rw [hfeq] at ht ⊢
      have hgt : analyticOrderAt g ρ ≠ ⊤ :=
        fun h => ht (analyticOrderAt_mul_eq_top_of_right h)
      refine ⟨?_, hgt⟩
      rw [analyticOrderNatAt_mul (f := fun z : ℂ => z - ρ₀) (by fun_prop) ha (by
        by_cases h : ρ = ρ₀ <;> simp [h]) hgt]
      by_cases h : ρ = ρ₀ <;> simp [analyticOrderNatAt, h]
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, ((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ) :=
        Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib] at hsum
      simp [hρ₀Z] at hsum
      omega
    have hzg : ∀ z ∈ Metric.closedBall z₀ R₁, g z = 0 → z ∈ Z :=
      fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero])
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ hzg (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      calc _ = ∏ ρ ∈ Z, ((if ρ = ρ₀ then z - ρ₀ else 1) * (z - ρ) ^ analyticOrderNatAt g ρ) :=
                Finset.prod_congr rfl fun ρ hρ => by
                  rw [(keyN ρ hρ).1, pow_add]
                  split_ifs with h <;> simp_all
           _ = _ := by rw [Finset.prod_mul_distrib]; simp [hρ₀Z]
    rw [hfg z, hhf z hz, hprod, mul_assoc]

theorem zeroFactorization : ZeroFactor := by
  intro f z₀ r R₁ hR₁ hR hf hf0
  have hr : 0 < r := hR₁.trans hR
  have hU : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hpre : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have hnotzero : ∀ x ∈ Metric.ball z₀ r, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := by
    intro x hx hev
    have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hev
    exact hf0 (hEq hz₀)
  have htop : ∀ x ∈ Metric.ball z₀ r, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hnz := hU.preimage_zero_mem_codiscreteWithin hf0 hz₀ ⟨⟨z₀, hz₀⟩, hpre⟩
  have hfin : (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}).Finite := by
    simpa only [Set.sdiff_eq, Set.preimage_compl, compl_compl] using
      (isCompact_closedBall z₀ R₁).finite_sdiff_of_mem_codiscreteWithin
        (Filter.codiscreteWithin_mono (Metric.closedBall_subset_ball hR) hnz)
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ r R₁ hR _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (Metric.closedBall_subset_ball hR ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, analyticOrderNatAt f, h, hmem, ?_, hhd, hh0, hhf⟩
  intro ρ hρ
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball : ρ ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hR hB
  have hne : analyticOrderAt f ρ ≠ 0 := fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp h0) hfρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← natCast_analyticOrderNatAt_of_ne_top (htop ρ hball)]
  simp [h0]

end Formalism.ZF
