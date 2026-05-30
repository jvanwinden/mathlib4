import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory ProbabilityTheory Filter Function Measure

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
abbrev Ω := (ℕ → V)
abbrev θ : Measure Ω := infinitePi (fun _ ↦ ρ)

-- Abbreviations for spaces and random variables
abbrev U := (ℕ → V)
abbrev A : Ω → U := id
abbrev B (n : ℕ) (ω : Ω) : V := ω n

-- μ is the sequence of measures which will form the counterexample
def μ (n : ℕ) : Measure (U × V) := (θ ρ).map (f := fun ω ↦ (A ω, B n ω))
instance (n : ℕ) : IsProbabilityMeasure (μ ρ n) := isProbabilityMeasure_map (by fun_prop)

-- Theorem 1: The sequence n ↦ μ n converges weakly to θ × ρ
theorem tendsto_μ_θ :
    letI : TopologicalSpace U := Pi.topologicalSpace
    letI : MeasurableSpace Ω := MeasurableSpace.pi
    Tendsto (fun n ↦ (μ ρ n).toProbabilityMeasure) atTop
    (nhds ((θ ρ).prod ρ).toProbabilityMeasure) := by
  let P m (n : ℕ) :=
    if n < m then n + 1
    else if n = m then 0
    else n
  let Q m (ω : Ω) : Ω := fun n ↦ ω (P m n)
  have : TendstoInDistribution
      (fun n ↦ (fun ω ↦ (A ω, B n ω)) ∘ Q n)
      (atTop)
      (fun ω : Ω ↦ ((fun n ↦ ω (n + 1)), ω 0))
      (fun _ ↦ (θ ρ)) (θ ρ) := by
    apply MeasureTheory.tendstoInDistribution_of_ae_tendsto (by fun_prop) (by fun_prop)
    apply Eventually.of_forall
    intro ω
    rw [Prod.tendsto_iff]
    refine ⟨?_, ?_⟩
    · rw [tendsto_pi_nhds]
      intro n
      apply EventuallyEq.tendsto
      filter_upwards [eventually_ge_atTop (n + 1)] with m hm
      aesop
    apply EventuallyEq.tendsto
    apply Eventually.of_forall
    grind
  convert this.tendsto with n
  · rw [μ, ← map_map (by fun_prop) (by fun_prop)]
    congr; symm
    refine map_infinitePi_infinitePi_of_inj ?_
    apply Function.HasLeftInverse.injective
    refine ⟨fun m ↦
      if m = 0 then n
      else if m ≤ n then (m - 1)
      else m, ?_⟩
    grind
  · symm
    apply HasLaw.map_eq
    apply IndepFun.hasLaw_prod
    · refine ⟨?_, ?_⟩
      · apply Measurable.aemeasurable; fun_prop
      apply map_infinitePi_infinitePi_of_inj
      intro i j hij
      grind
    · apply MeasurePreserving.hasLaw
      apply measurePreserving_eval_infinitePi
    · symm;
      apply ProbabilityTheory.IndepFun.indepFun_process (by fun_prop) (by fun_prop)
      intro S
      let T : Finset ℕ := {0}
      have : (0 ∈ T) := by aesop
      have := iIndepFun_infinitePi (P := fun (i : ℕ) ↦ ρ) (X := fun _ ω ↦ ω) (by fun_prop)
      have := iIndepFun.indepFun_finset {0} (S.image (fun n ↦ n + 1)) (by simp) (this) (by fun_prop)
      rw [IndepFun_iff_Indep] at ⊢ this
      apply indep_of_indep_of_le_right (indep_of_indep_of_le_left this _)
      · let S' := (S.image (fun n ↦ n + 1))
        let g (u : (S' → V)) : (S → V) := fun m ↦ u (⟨(m : ℕ) + 1, by aesop⟩)
        have : (fun (ω : Ω) (i : S) ↦ ω (i + 1)) = g ∘ (fun (ω : Ω) i ↦ ω i) := by aesop
        rw [this, ← MeasurableSpace.comap_comp]
        apply MeasurableSpace.comap_mono ?_
        exact Measurable.comap_le <| by fun_prop
      · let g (u : T → V) : V := u ⟨0, by aesop⟩
        have : (fun ω ↦ ω 0) = g ∘ (fun (a : Ω) i ↦ a i) := by aesop
        rw [this, ← MeasurableSpace.comap_comp]
        apply MeasurableSpace.comap_mono ?_
        exact Measurable.comap_le <| by fun_prop

-- Theorem 2: If there exist random variables A' and B' n, such that
-- (A', B' n) has law μ n and B' n converges almost surely,
-- then ρ must be a Dirac measure.
-- TODO: show that convergence along a sequence suffices for the conclusion
theorem measure_const_of_strong_skorokhod
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {A' : Ω' → U} {B' : ℕ → Ω' → V} {B'_lim : Ω' → V}
    (h_law : ∀ n, HasLaw (fun ω' ↦ (A' ω', B' n ω')) (μ ρ n) P')
    (h_tt : ∀ᵐ ω' ∂P', Tendsto (fun n ↦ B' n ω') atTop (nhds (B'_lim ω'))) :
    ∃ x : V, ρ = dirac x := by
  -- Setup measurability automation
  have (n : ℕ) : AEMeasurable (B' n) P' := (h_law n).aemeasurable.snd
  have : AEMeasurable B'_lim P' := aemeasurable_of_tendsto_metrizable_ae _ (by fun_prop) h_tt
  -- (A, B n) has the same distribution as (A', B' n)
  have h_id n : IdentDistrib (fun ω ↦ (A ω, B n ω))
      (fun ω' ↦ (A' ω', B' n ω')) (θ ρ) P' :=
    HasLaw.identDistrib (HasLaw.mk (by fun_prop) (by aesop)) (h_law n)
  -- It suffices to show that ρ × ρ is equal to the diagonal pushforward of ρ
  suffices (ρ.prod ρ) = (ρ.map (fun v ↦ (v, v))) by
    apply @IsZeroOneMeasure.exists_eq_dirac _ _ _ ?_ _ _
    refine .mk fun s hs ↦ or_iff_not_imp_left.mpr (fun hρ ↦ ?_)
    have := Measure.ext_iff.mp this (s ×ˢ s) (by measurability)
    rw [map_apply (by fun_prop) (by measurability)] at this
    simpa [ENNReal.mul_eq_left hρ (by simp)] using this
  -- The law of (B'_lim, B'_lim) is equal to the LHS and the RHS
  -- We will prove this by approximating (B'_lim, B'_lim) in two different ways
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
      refine EventuallyEq.tendsto <| .of_forall fun n ↦ Subtype.ext <| HasLaw.map_eq ?_
      apply HasLaw.congr (X := fun ω' ↦ (A' ω' n, A' ω' (n + 1)))
      · apply IdentDistrib.hasLaw (f := fun ω ↦ (A ω n, A ω (n + 1)))
        · exact (h_id 0).comp (u := fun (u, v) ↦ (u n, u (n + 1))) (by fun_prop)
        apply IndepFun.hasLaw_prod
        · exact MeasurePreserving.hasLaw <| measurePreserving_eval_infinitePi _ _
        · exact MeasurePreserving.hasLaw <| measurePreserving_eval_infinitePi _ _
        apply iIndepFun.indepFun (f := fun n ω ↦ A ω n) _ (by simp)
        exact ProbabilityTheory.iIndepFun_infinitePi (X := fun n v ↦ v) (by fun_prop)
      · have A'_eq_B' n : ∀ᵐ ω' ∂P', A' ω' n = B' n ω' := by
          have := (h_id n).comp (u := fun u ↦ (u.1 n, u.2)) (by fun_prop)
          exact this.ae_snd (p := fun u ↦ u.1 = u.2) (by measurability) (by simp)
        filter_upwards [A'_eq_B' n, A'_eq_B' (n + 1)] using by aesop
  · rw [toProbabilityMeasure_inj (isProbabilityMeasure_map (by fun_prop))
        (isProbabilityMeasure_map (by fun_prop))]
    -- Approximate by (B' n, B' n) to get the diagonal pushforward as a limit
    apply tendsto_nhds_unique (l := atTop) (X := ProbabilityMeasure _)
      (f := fun n ↦ ⟨P'.map (fun ω ↦ (B' n ω, B' n ω)), ?_⟩)
    rotate_right
    · exact isProbabilityMeasure_map <| by fun_prop
    · -- a.s. convergence of B' n implies convergence in distribution of (B' n, B' n)
      refine (tendstoInDistribution_of_ae_tendsto (by fun_prop) (by fun_prop) ?_).tendsto
      simpa [Prod.tendsto_iff]
    · -- For every n, the law of (B' n, B' n) is the diagonal pushforward of ρ
      refine EventuallyEq.tendsto <| .of_forall fun n ↦ Subtype.ext <| HasLaw.map_eq ?_
      have := (h_id n).comp (u := fun (u, v) ↦ (v, v)) (by fun_prop)
      apply this.hasLaw
      apply HasLaw.fun_comp (Y := fun v ↦ (v, v)) (μ := ρ) <| .mk (by fun_prop) rfl
      exact MeasurePreserving.hasLaw <| measurePreserving_eval_infinitePi _ _

end StrongSkorokhod

end

#min_imports
