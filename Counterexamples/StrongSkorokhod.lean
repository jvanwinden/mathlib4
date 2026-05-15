import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Process.Basic

open MeasureTheory ProbabilityTheory Filter Function Measure

noncomputable section

section Auxiliary

lemma MeasureTheory.Measure.toProbabilityMeasure_inj {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure Ω} (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν) :
    μ = ν ↔ (⟨μ, hμ⟩ : ProbabilityMeasure Ω) = ⟨ν, hν⟩ := by simp

def MeasureTheory.Measure.toProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : ProbabilityMeasure Ω := ⟨μ, inferInstance⟩

theorem MeasureTheory.tendstoInDistribution_of_ae_tendsto
    {E Ω' : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} {Z : Ω' → E} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E]
    {X : ℕ → Ω' → E} (h : ∀ᵐ ω ∂μ', Tendsto (fun i ↦ X i ω) atTop (nhds (Z ω)))
    (hX : ∀ (i : ℕ), AEMeasurable (X i) μ') :
    TendstoInDistribution X atTop Z (fun _ ↦ μ') μ' := by
  have : AEMeasurable Z μ' := by
    apply aemeasurable_of_tendsto_metrizable_ae _ hX h
  apply TendstoInDistribution.mk (by measurability) (by measurability) _
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  obtain ⟨C, hC⟩ := f.bounded
  simp only [ProbabilityMeasure.coe_mk]
  rw [MeasureTheory.integral_map (by measurability) (by measurability)]
  conv in ∫ _, _ ∂_ =>
    rw [MeasureTheory.integral_map (by measurability) (by measurability)]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ ↦ ‖f‖)
  · apply Eventually.of_forall; intro n; apply AEMeasurable.aestronglyMeasurable
    measurability
  · exact Eventually.of_forall <| fun _ ↦ .of_forall <| fun _ ↦ by apply f.norm_coe_le_norm
  · simp
  filter_upwards [h] with ω hω using (f.continuous.tendsto (Z ω)).comp hω

theorem hasLaw_infinitePi_eval
    {ι : Type*} {Ω : ι → Type*} {mΩ : (i : ι) → MeasurableSpace (Ω i)} {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) : HasLaw (fun ω ↦ ω i) (μ i) (infinitePi (fun i ↦ μ i)) := by
  refine ⟨?_, by apply infinitePi_map_eval⟩
  apply Measurable.aemeasurable
  measurability

theorem hasLaw_infinitePi
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {e : ι → ι} (he : Injective e) :
    (infinitePi (fun (_ : ι) ↦ P)).map (fun ω i ↦ ω (e i)) = infinitePi (fun _ ↦ P) := by
  apply HasLaw.map_eq
  refine iIndepFun.hasLaw_infinitePi ?_ ?_ (by apply Measurable.aemeasurable; measurability)
  · exact fun _ ↦ by apply hasLaw_infinitePi_eval (μ := fun _ ↦ P)
  · have := iIndepFun_infinitePi (P := fun (_ : ι) ↦ P) (X := fun x ω ↦ ω) (by measurability)
    exact iIndepFun.precomp he this

-- If a sequence of random variables with laws μ n converges almost surely,
-- then μ n converges to μ iff the limit has law μ
lemma hasLaw_of_tendsto_tendsto''
    {Ω : Type*} {α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [TopologicalSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : ℕ → ProbabilityMeasure α}
    (ν_lim : ProbabilityMeasure α)
    {X : ℕ → Ω → α} {X_lim : Ω → α}
    (h_law : ∀ n, HasLaw (X n) (ν n) μ)
    (h_tt_ae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (nhds (X_lim ω))) :
    Tendsto (fun n ↦ (ν n)) atTop (nhds ν_lim) ↔
    HasLaw X_lim ν_lim μ := by
  have := aemeasurable_of_tendsto_metrizable_ae atTop (by measurability) h_tt_ae
  have := (tendstoInDistribution_of_ae_tendsto h_tt_ae (by measurability)).tendsto
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨by measurability, ?_⟩
    rw [toProbabilityMeasure_inj ?_ (inferInstance)]
    swap; · exact isProbabilityMeasure_map (by measurability)
    apply tendsto_nhds_unique this
    convert h with n
    · exact Subtype.ext (h_law n).map_eq
  · convert (tendstoInDistribution_of_ae_tendsto h_tt_ae (by measurability)).tendsto with n
    · exact Subtype.ext (h_law n).map_eq.symm
    · exact Subtype.ext h.map_eq.symm

-- Identify the law of the limit of a sequence of random variables
lemma hasLaw_of_tendsto_tendsto
    {Ω : Type*} {α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [SeminormedAddCommGroup α] [SecondCountableTopology α] [BorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : ℕ → Measure α} [hν : ∀ n, IsProbabilityMeasure (ν n)]
    {ν_lim : Measure α} [hν_lim : IsProbabilityMeasure ν_lim]
    {X : ℕ → Ω → α} {X_lim : Ω → α}
    (h_law : ∀ n, HasLaw (X n) (ν n) μ)
    (h_tt_ae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (nhds (X_lim ω)))
    (h_tt_law : Tendsto (fun n ↦ (ν n).toProbabilityMeasure) atTop
      (nhds ν_lim.toProbabilityMeasure)) :
    HasLaw X_lim ν_lim μ :=
  (hasLaw_of_tendsto_tendsto'' ν_lim.toProbabilityMeasure h_law h_tt_ae).mp h_tt_law

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

-- θ, θ × ρ, and μ n are probability measures
instance : IsProbabilityMeasure (θ ρ) := by apply instIsProbabilityMeasureForallInfinitePi

instance : IsProbabilityMeasure ((θ ρ).prod ρ) := prod.instIsProbabilityMeasure (θ ρ) ρ

instance (n : ℕ) : IsProbabilityMeasure (μ ρ n) := by
  apply isProbabilityMeasure_map; measurability

-- Theorem 1: The sequence n ↦ μ n converges weakly to θ × ρ
theorem tendsto_μ_θ : Tendsto
    (fun n ↦ (μ ρ n).toProbabilityMeasure) atTop
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
    apply MeasureTheory.tendstoInDistribution_of_ae_tendsto
    · apply Eventually.of_forall
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
    · measurability
  convert this.tendsto with n
  · rw [μ, ← map_map (by measurability) (by measurability)]
    congr; symm
    refine hasLaw_infinitePi ?_
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
      · apply Measurable.aemeasurable; measurability
      apply hasLaw_infinitePi
      intro i j hij
      grind
    · apply hasLaw_infinitePi_eval (μ := fun _ ↦ ρ)
    · symm;
      apply ProbabilityTheory.IndepFun.indepFun_process
      · measurability
      · measurability
      intro S
      let T : Finset ℕ := {0}
      have : (0 ∈ T) := by aesop
      have := iIndepFun_infinitePi (P := fun (i : ℕ) ↦ ρ) (X := fun _ ω ↦ ω) (by measurability)
      have := iIndepFun.indepFun_finset {0} (S.image (fun n ↦ n + 1)) (by simp) (this) (by measurability)
      simp only at this
      rw [IndepFun_iff_Indep] at ⊢ this
      apply indep_of_indep_of_le_right (indep_of_indep_of_le_left this _)
      · let S' := (S.image (fun n ↦ n + 1))
        let g (u : (S' → V)) : (S → V) := fun m ↦ u (⟨(m : ℕ) + 1, by aesop⟩)
        have : (fun (ω : Ω) (i : S) ↦ ω (i + 1)) = g ∘ (fun (ω : Ω) i ↦ ω i) := by aesop
        rw [this, ← MeasurableSpace.comap_comp]
        apply MeasurableSpace.comap_mono ?_
        apply Measurable.comap_le
        measurability
      · let g (u : T → V) : V := u ⟨0, by aesop⟩
        have : (fun ω ↦ ω 0) = g ∘ (fun (a : Ω) i ↦ a i) := by aesop
        rw [this, ← MeasurableSpace.comap_comp]
        apply MeasurableSpace.comap_mono ?_
        apply Measurable.comap_le
        measurability

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
  have : Measurable A := by measurability
  have (n : ℕ) : AEMeasurable (fun ω ↦ A ω n) (θ ρ) := Measurable.aemeasurable (by measurability)
  have (n : ℕ) : Measurable (B n) := by measurability
  have (n : ℕ) : AEMeasurable (B n) (θ ρ) := by measurability
  haveI : IsProbabilityMeasure (map (fun v ↦ (v, v)) ρ) :=
    isProbabilityMeasure_map (by measurability)
  -- (A, B n) has the same distribution as (A', B' n)
  have h_id n : IdentDistrib (fun ω ↦ (A ω, B n ω))
      (fun ω' ↦ (A' ω', B' n ω')) (θ ρ) P' :=
    HasLaw.identDistrib (HasLaw.mk (by measurability) (by aesop)) (h_law n)
  -- It suffices to show that ρ × ρ is equal to the diagonal pushforward of ρ
  suffices (ρ.prod ρ) = (ρ.map (fun v ↦ (v, v))) by
    apply @IsZeroOneMeasure.exists_eq_dirac _ _ _ ?_ _ _
    refine ⟨fun s hs ↦ ?_⟩
    have : (ρ s) * (ρ s) = ρ s := by
      rw [← prod_prod, this, map_apply (by measurability) (by measurability)]
      simp
    rw [or_iff_not_imp_left]
    exact fun hρ ↦ by simpa [ENNReal.mul_eq_left (hρ) (by aesop)] using this
  -- The law of (B'_lim, B'_lim) is equal to the LHS and the RHS
  -- We will prove this by approximating (B'_lim, B'_lim) in two different ways
  trans P'.map (fun ω' ↦ (B'_lim ω', B'_lim ω'))
  · symm
    apply HasLaw.map_eq
    -- Approximate using n ↦ (B n, B (n + 1))
    apply hasLaw_of_tendsto_tendsto (X := (fun n ω' ↦ (B' n ω', B' (n + 1) ω')))
        (ν := fun _ ↦ ρ.prod ρ)
    · intro n
      -- Exploit that A' ω' n = B' n ω almost surely
      apply HasLaw.congr (X := fun ω' ↦ (A' ω' n, A' ω' (n + 1)))
      · apply IdentDistrib.hasLaw (f := fun ω ↦ (A ω n, A ω (n + 1))) (μ := (θ ρ))
        · exact (h_id 0).comp (u := fun (u, v) ↦ (u n, u (n + 1))) (by measurability)
        apply IndepFun.hasLaw_prod
        · apply hasLaw_infinitePi_eval
        · apply hasLaw_infinitePi_eval (μ := fun _ ↦ ρ)
        apply iIndepFun.indepFun (f := fun n ω ↦ A ω n)
        · apply ProbabilityTheory.iIndepFun_infinitePi (X := fun n v ↦ v)
          measurability
        simp
      · have A'_eq_B' n : ∀ᵐ ω' ∂P', A' ω' n = B' n ω' := by
          have := (h_id n).comp (u := fun u ↦ (u.1 n, u.2)) (by measurability)
          apply this.ae_snd (p := fun u ↦ u.1 = u.2) (by measurability)
          simp
        filter_upwards [A'_eq_B' n, A'_eq_B' (n + 1)] using by aesop
    · filter_upwards [h_tt] with ω hω
      refine (Prod.tendsto_iff _ _).mpr ⟨hω, ?_⟩
      exact (Filter.tendsto_add_atTop_iff_nat 1).mpr hω
    · simp
  · apply HasLaw.map_eq
    -- Approximate using n ↦ (B n, B n)
    apply hasLaw_of_tendsto_tendsto (X := (fun n ω' ↦ (B' n ω', B' n ω')))
        (ν := fun _ ↦ ρ.map (fun v ↦ (v, v)))
    · intro n
      have := (h_id n).comp (u := fun (u, v) ↦ (v, v)) (by measurability)
      apply this.hasLaw
      apply HasLaw.fun_comp (Y := fun v ↦ (v, v)) (μ := ρ)
      · exact ⟨by measurability, rfl⟩
      apply hasLaw_infinitePi_eval
    · filter_upwards [h_tt] using by simp [Prod.tendsto_iff]
    · simp

end StrongSkorokhod

end


-- If the set of measures is tight, it suffices to check the limsup
-- condition for compact sets in the portmanteau theorem.
theorem MeasureTheory.tendsto_of_forall_isCompact_limsup_le
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [T2Space Ω]
    {L : Filter ι} [L.IsCountablyGenerated]
    [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h_tight : IsTightMeasureSet (μs '' Set.univ))
    (h : ∀ (F : Set Ω), IsCompact F → Filter.limsup
      (fun (i : ι) => (μs i) F) L ≤ μ F) :
    Filter.Tendsto (fun i ↦ (μs i).toProbabilityMeasure) L
      (nhds (μ.toProbabilityMeasure)) := by
  apply tendsto_of_forall_isClosed_limsup_le
  intro F hF_closed
  rw [← ENNReal.coe_le_coe, ENNReal.ofNNReal_limsup]
  swap; · exact isBoundedUnder_of_eventually_le (a := 1) (by aesop)
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h_tight
  obtain ⟨K, hKc, hK_le⟩ := h_tight ε (by positivity)
  specialize h (F ∩ K) <| hKc.inter_left hF_closed
  simp_rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  simp_rw [toProbabilityMeasure, ProbabilityMeasure.coe_mk]
  grw [limsup_le_limsup (v := fun i ↦ (μs i (F ∩ K)) + ε)]
  · rw [limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)]
    apply add_le_add _ (by rfl)
    grw [h]
    apply measure_mono
    simp
  · apply Eventually.of_forall
    intro i; simp only
    rw [← measure_inter_add_diff _ hKc.measurableSet]
    apply add_le_add (by rfl)
    specialize hK_le (μs i) (by simp)
    apply le_trans _ hK_le
    apply measure_mono
    simp

-- A set of measures on a product space is tight if both marginals are tight
lemma tight_of_marginals_tight
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace α] [TopologicalSpace β]
    [OpensMeasurableSpace α] [OpensMeasurableSpace β]
    [T2Space α] [T2Space β]
    (μ : Set (Measure (α × β)))
    (hμ_1 : IsTightMeasureSet {ν.map (fun x ↦ x.1) | ν ∈ μ})
    (hμ_2 : IsTightMeasureSet {ν.map (fun x ↦ x.2) | ν ∈ μ}) :
    IsTightMeasureSet μ := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at *
  intro ε hε
  specialize hμ_1 (ε / 2) (by aesop)
  specialize hμ_2 (ε / 2) (by aesop)
  obtain ⟨K1, hKc_1, hKm_le_1⟩ := hμ_1
  obtain ⟨K2, hKc_2, hKm_le_2⟩ := hμ_2
  refine ⟨K1 ×ˢ K2, ?_, ?_⟩
  · exact IsCompact.prod hKc_1 hKc_2
  intro κ hκ_mem
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  specialize hKm_le_1 κ hκ_mem
  specialize hKm_le_2 κ hκ_mem
  have : (K1 ×ˢ K2)ᶜ ⊆ (K1 ×ˢ Set.univ)ᶜ ∪ (Set.univ ×ˢ K2)ᶜ := by
    grind
  grw [measure_mono this, measure_union_le]
  rw [← ENNReal.add_halves (a := ε)]
  apply add_le_add
  · convert hKm_le_1
    rw [map_apply]
    · congr; aesop
    · measurability
    · exact MeasurableSet.compl hKc_1.measurableSet
  · convert hKm_le_2
    rw [map_apply]
    · congr; aesop
    · measurability
    · exact MeasurableSet.compl hKc_2.measurableSet
