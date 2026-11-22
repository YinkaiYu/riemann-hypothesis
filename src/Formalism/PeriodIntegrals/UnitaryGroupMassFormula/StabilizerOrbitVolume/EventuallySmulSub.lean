import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos

noncomputable section

namespace PI.VolStabSW

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribMulAction.toAddMonoidHom W t)

omit [TopologicalSpace K] in
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp only [smulSub, AddSubgroup.mem_map, DistribMulAction.toAddMonoidHom_apply]

theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  rw [SetLike.mem_coe, mem_smulSub, Set.mem_image]
  rfl

theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact isOpenMap_smul₀ ht _ hP

theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact hP.image (continuous_const_smul t)

theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hev : ∀ᶠ c in 𝓝 (0 : K), ∀ p ∈ S, c • p ∈ N :=
    hS.eventually_forall_of_forall_eventually fun p _ => by
      have h0 : Tendsto (fun z : K × W => z.1 • z.2) (𝓝 ((0 : K), p)) (𝓝 ((0 : K) • p)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  exact (hs.eventually hev).exists

variable [T2Space X]

theorem reach_of_approx (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  classical
  have hbase' : ∀ p ∈ P, ∃ l ∈ L, ∃ q ∈ P, π • q = p - D l := fun p hp => by
    obtain ⟨l, hl, h⟩ := hbase p hp
    exact ⟨l, hl, (mem_smulSub π P _).1 h⟩
  choose! fl hfl fq hfq hrel using hbase'
  intro p hp

  let ps : ℕ → X := fun k => Nat.rec p (fun _ q => fq q) k
  have hpsS : ∀ k, ps (k + 1) = fq (ps k) := fun k => rfl
  have hpsP : ∀ k, ps k ∈ P := by
    intro k
    induction k with
    | zero => exact hp
    | succ k ih => rw [hpsS]; exact hfq _ ih
  have hπLk : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => intro w hw; rw [pow_succ, mul_smul]; exact ih _ (hπL w hw)
  let σ : ℕ → V := fun k => ∑ i ∈ Finset.range (k + 1), π ^ i • fl (ps i)
  have hσL : ∀ k, σ k ∈ L := fun k => L.sum_mem fun i _ => hπLk i _ (hfl _ (hpsP i))
  have hrem : ∀ k, p - D (σ k) = π ^ (k + 1) • ps (k + 1) := by
    intro k
    induction k with
    | zero =>
      show p - D (∑ i ∈ Finset.range 1, π ^ i • fl (ps i)) = π ^ 1 • fq p
      rw [Finset.sum_range_one, pow_zero, one_smul, pow_one, hrel p hp]
      rfl
    | succ k ih =>
      have e1 : σ (k + 1) = σ k + π ^ (k + 1) • fl (ps (k + 1)) := Finset.sum_range_succ _ _
      rw [hpsS (k + 1), e1, map_add, hDs, sub_add_eq_sub_sub, ih, ← smul_sub,
        ← hrel _ (hpsP (k + 1)), smul_smul, ← pow_succ]

  have hsmallP : ∀ N ∈ 𝓝 (0 : X), ∀ᶠ c in 𝓝 (0 : K), ∀ q ∈ P, c • q ∈ N := fun N hN =>
    hPc.eventually_forall_of_forall_eventually fun q _ => by
      have h0 : Tendsto (fun z : K × X => z.1 • z.2) (𝓝 ((0 : K), q)) (𝓝 ((0 : K) • q)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  have hπ1 : Tendsto (fun k : ℕ => π ^ (k + 1)) atTop (𝓝 0) := hπ.comp (tendsto_add_atTop_nat 1)
  have hremT : Tendsto (fun k => p - D (σ k)) atTop (𝓝 0) := by
    refine Tendsto.congr (fun k => (hrem k).symm) ?_
    intro N hN
    exact (hπ1.eventually (hsmallP N hN)).mono fun k hk => hk _ (hpsP (k + 1))
  have hDT : Tendsto (fun k => D (σ k)) atTop (𝓝 p) := by
    simpa using (tendsto_const_nhds (x := p)).sub hremT

  obtain ⟨l, hlL, hcl⟩ := hLc (f := Filter.map σ atTop)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' hσL)))
  refine ⟨l, hlL, ?_⟩
  have h2 : MapClusterPt (D l) atTop (D ∘ σ) := MapClusterPt.continuousAt_comp hDc.continuousAt hcl
  exact eq_of_nhds_neBot ((show ClusterPt (D l) (Filter.map (D ∘ σ) atTop) from h2).neBot.mono
    (inf_le_inf_left _ hDT))

theorem filt_abstract [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribMulAction.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) :=
  PI.VolStabS.filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall

end Abs

end PI.VolStabSW
