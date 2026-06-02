/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# A formalization of the counterexample to the strong Skorokhod representation 'theorem'

The article [brzezniak_2018] purports to provide a stronger version of the Skorokhod representation
theorem for weakly convergent probability measures. However, the article [ondrejat_seidler_2025]
shows that the proof is wrong and cannot be repaired, by constructing a simple counterexample which
refutes the 'theorem'. This file contains a formalization of the counterexample.

The example has the following structure. Given an arbitrary probability measure `ρ` on ℝ, we
construct a sequence of measures `μ n` and prove the following statements:

- `measure_tendsto`: The sequence of probability measures `μ n` converges weakly.
- `measure_eq_dirac_of_strong_skorokhod`: If the conclusion of the strong Skorohkod representation
  holds true for `μ n`, then `ρ` must be a Dirac measure.

By combining the two statements, it follows that the strong Skorokhod representation theorem
does not hold true for arbitraries measures.

## Tags

Skorokhod representation theorem, probability, weak convergence
-/

open MeasureTheory ProbabilityTheory Filter Function Measure Topology

noncomputable section

section Auxiliary

/-- Is this necessary? -/
lemma MeasureTheory.Measure.toProbabilityMeasure_inj {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure Ω} (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν) :
    μ = ν ↔ (⟨μ, hμ⟩ : ProbabilityMeasure Ω) = ⟨ν, hν⟩ := by simp

/-- Is this necessary? -/
def MeasureTheory.Measure.toProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : ProbabilityMeasure Ω := ⟨μ, inferInstance⟩

end Auxiliary

section StrongSkorokhod

-- We assume we are given some probability measure ρ on V = ℝ
abbrev V := ℝ
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

-- θ is the infinite product measure of ρ
abbrev Ω := ℕ → V
abbrev θ : Measure Ω := infinitePi (fun _ ↦ ρ)

-- Abbreviations for spaces and random variables
abbrev U := ℕ → V
abbrev A : Ω → U := id
abbrev B n (ω : Ω) := ω n

-- μ is the sequence of measures which forms the counterexample
def μ (n : ℕ) : Measure (U × V) := (θ ρ).map (f := fun ω ↦ (A ω, B n ω))
instance (n : ℕ) : IsProbabilityMeasure (μ ρ n) := isProbabilityMeasure_map (by fun_prop)

/-- The sequence of measures `μ n` constructed above converges weakly to `θ × ρ` -/
theorem measure_tendsto :
    letI : TopologicalSpace U := Pi.topologicalSpace
    letI : MeasurableSpace Ω := MeasurableSpace.pi
    Tendsto (fun n ↦ (μ ρ n).toProbabilityMeasure) atTop
    (𝓝 ((θ ρ).prod ρ).toProbabilityMeasure) := by
  -- Proof sketch:
  -- t n is a transformation of Ω, which permutes the sequence (B 0, B 1, ...) to
  -- (B 1, B 2, ..., B (n - 1), B 0, B n, B (n + 1))
  -- Since t n is measure preserving, (A, B n) ∘ t n has law μ n
  -- Moreover, (A, B n) ∘ t n converges almost surely to (A', B') = ((B_1, B_2, ...), B_0).
  -- Thus, μ n converges to the law of (A', B'), which is θ × ρ
  let t n (ω : Ω) : Ω := fun m ↦ ω (if m < n then m + 1 else if m = n then 0 else m)
  have : TendstoInDistribution (fun n ↦ (fun ω ↦ (A ω, B n ω)) ∘ t n) atTop
      (fun ω ↦ ((fun n ↦ ω (n + 1)), ω 0)) (fun _ ↦ θ ρ) (θ ρ) := by
    refine tendstoInDistribution_of_ae_tendsto (by fun_prop) (by fun_prop) <| .of_forall fun ω ↦ ?_
    refine (Prod.tendsto_iff _ _).mpr ⟨?_, ?_⟩
    · refine tendsto_pi_nhds.mpr fun n ↦ EventuallyEq.tendsto ?_
      filter_upwards [eventually_ge_atTop (n + 1)] with m hm using by aesop
    · convert tendsto_const_nhds using 1; grind
  convert this.tendsto with n
  all_goals symm
  · rw [μ, ← map_map (by fun_prop) (by fun_prop)]
    congr
    refine map_infinitePi_infinitePi_of_inj <| HasLeftInverse.injective ?_
    exact ⟨fun m ↦ if m = 0 then n else if m ≤ n then (m - 1) else m, by grind⟩
  · rw [IndepFun.map_prod_eq_prod_map_map]
    · congr
      · exact map_infinitePi_infinitePi_of_inj <| fun _ ↦ by grind
      · apply infinitePi_map_eval
    · exact Measurable.aemeasurable <| by fun_prop
    · exact Measurable.aemeasurable <| by fun_prop
    · refine (IndepFun.indepFun_process (by fun_prop) (by fun_prop) <| fun S ↦ ?_).symm
      have := iIndepFun_infinitePi (ι := ℕ) (P := fun _ ↦ ρ) (X := fun _ ω ↦ ω) (by fun_prop)
      have := iIndepFun.indepFun_finset {0} (S.image (fun n ↦ n + 1)) (by simp) this (by fun_prop)
      refine this.comp (φ := fun x ↦ x ⟨0, by simp⟩) (ψ := fun x (i : S) ↦ x ⟨i + 1, by simp⟩) ?_ ?_
      all_goals fun_prop

/-- If there exist random variables `A'` and `B' n` for which `(A', B' n)` has
law `μ n` and `B' n` converges almost surely, then `ρ` must be a Dirac measure. -/
theorem measure_eq_dirac_of_strong_skorokhod
    {Ω' : Type*} {hmΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {A' : Ω' → U} {B' : ℕ → Ω' → V} {B'_lim : Ω' → V}
    (h_law : ∀ n, HasLaw (fun ω' ↦ (A' ω', B' n ω')) (μ ρ n) P')
    (h_tt : ∀ᵐ ω' ∂P', Tendsto (fun n ↦ B' n ω') atTop (𝓝 (B'_lim ω'))) :
    ∃ x, ρ = dirac x := by
  -- Setup for measurability automation
  have (n : ℕ) := (h_law n).aemeasurable.snd
  have := aemeasurable_of_tendsto_metrizable_ae _ (by fun_prop) h_tt
  -- (A, B n) has the same distribution as (A', B' n)
  have h_idd n : IdentDistrib (fun ω ↦ (A ω, B n ω)) (fun ω' ↦ (A' ω', B' n ω')) (θ ρ) P' :=
    HasLaw.identDistrib (HasLaw.mk (by fun_prop) (by aesop)) (h_law n)
  -- It suffices to show that ρ × ρ is equal to the diagonal pushforward of ρ
  suffices (ρ.prod ρ) = (ρ.map (fun v ↦ (v, v))) by
    apply @IsZeroOneMeasure.exists_eq_dirac _ _ _ ?_ _ _
    refine .mk fun s hs₁ ↦ or_iff_not_imp_left.mpr <| fun hs₂ ↦ ?_
    have := Measure.ext_iff.mp this (s ×ˢ s) (by measurability)
    rw [map_apply (by fun_prop) (by measurability)] at this
    simpa [ENNReal.mul_eq_left hs₂ (by simp)] using this
  -- The law of (B'_lim, B'_lim) is equal to the LHS and the RHS
  -- We will prove this by approximating (B'_lim, B'_lim) in two different ways (see below)
  trans P'.map (fun ω' ↦ (B'_lim ω', B'_lim ω'))
  · symm; rw [toProbabilityMeasure_inj (isProbabilityMeasure_map (by fun_prop))
              (prod.instIsProbabilityMeasure ρ ρ)]
    -- Approximate by (B' n, B' (n + 1)) to get the the product measure as a limit
    apply tendsto_nhds_unique (l := atTop) (X := ProbabilityMeasure _)
      (f := fun n ↦ ⟨P'.map (fun ω ↦ (B' n ω, B' (n + 1) ω)), ?_⟩)
    rotate_right
    · exact isProbabilityMeasure_map <| by fun_prop
    · -- a.s. convergence of B' n implies convergence in distribution of (B' n, B' (n + 1))
      refine (tendstoInDistribution_of_ae_tendsto (by fun_prop) (by fun_prop) ?_).tendsto
      filter_upwards [h_tt] with ω hω
      refine (Prod.tendsto_iff _ _).mpr ⟨hω, ?_⟩
      exact (tendsto_add_atTop_iff_nat 1).mpr hω
    · -- Since B' n ω = A' ω' n almost surely and the components of A' ω' n are independent,
      -- the distribution of (B' n, B' (n + 1)) is given by ρ × ρ for every n.
      convert tendsto_const_nhds using 3 with n
      rw [map_congr (g := fun ω' ↦ (A' ω' n, A' ω' (n + 1)))]
      · refine IdentDistrib.hasLaw (μ := θ ρ) (f := fun ω ↦ (A ω n, A ω (n + 1))) ?_ ?_ |>.map_eq
        · exact (h_idd 0).comp (u := fun (u, v) ↦ (u n, u (n + 1))) (by fun_prop)
        exact .mk (by fun_prop) <| infinitePi_map_eval_prod (by simp)
      · have A'_eq_B' n : ∀ᵐ ω' ∂P', A' ω' n = B' n ω' := by
          simpa using (h_idd n).ae_snd (p := fun (A, B) ↦ A n = B) (by measurability)
        filter_upwards [A'_eq_B' n, A'_eq_B' (n + 1)] using by aesop
  · rw [toProbabilityMeasure_inj (isProbabilityMeasure_map (by fun_prop))
        (isProbabilityMeasure_map (by fun_prop))]
    -- Approximate by (B' n, B' n) to get the diagonal pushforward as a limit
    apply tendsto_nhds_unique (l := atTop) (X := ProbabilityMeasure _)
      (f := fun n ↦ ⟨P'.map ((fun v ↦ (v, v)) ∘ B' n), ?_⟩)
    rotate_right
    · exact isProbabilityMeasure_map <| by fun_prop
    · -- a.s. convergence of B' n implies convergence in distribution of (B' n, B' n)
      refine (tendstoInDistribution_of_ae_tendsto (by fun_prop) (by fun_prop) ?_).tendsto
      simpa [Prod.tendsto_iff]
    · -- For every n, the law of (B' n, B' n) is the diagonal pushforward of ρ
      conv in Measure.map _ _ =>
        rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      convert tendsto_const_nhds using 4 with n
      apply (h_idd n).comp (u := fun x ↦ x.snd) (by fun_prop) |>.hasLaw _ |>.map_eq
      exact MeasurePreserving.hasLaw <| measurePreserving_eval_infinitePi _ _

end StrongSkorokhod

end
