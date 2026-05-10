import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

open MeasureTheory ProbabilityTheory Filter

lemma ae_eq_iff_map_meas_diag_comp_zero
    {Ω : Type*} {α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableEq α] {μ : Measure Ω}
    {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y) :
    X =ᵐ[μ] Y ↔ (μ.map (fun ω => (X ω, Y ω)) (Set.diagonal α)ᶜ = 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : (fun ω ↦ (X ω, Y ω)) =ᵐ[μ] (fun ω ↦ (X ω, X ω)) :=
      by filter_upwards [h] using by aesop
    rw [Measure.map_congr this]
    rw [Measure.map_apply (by measurability) (by measurability), Set.preimage_compl]
    rw [← mem_ae_iff, ← eventually_mem_set]
    exact Eventually.of_forall (by aesop)
  · rw [Measure.map_apply (by measurability) (by measurability)] at h
    simpa

abbrev V := ℝ
instance : MeasurableSpace V := inferInstance

variable (ρ : Measure V) [IsProbabilityMeasure ρ]

noncomputable section



-- our probability space, consisting of infinite copies of V
def Ω := (ℕ → V)

abbrev U₁ := (ℕ → V)
abbrev U₂ := V

-- product σ-algebra
instance : MeasurableSpace Ω := .pi
-- product measure
noncomputable def θ : Measure Ω := MeasureTheory.Measure.infinitePi (fun _ ↦ ρ)

instance : IsProbabilityMeasure (θ ρ) := by apply Measure.instIsProbabilityMeasureForallInfinitePi

-- the random varialbe A, which is just the identity
abbrev A : Ω → U₁ := id
-- the random varialbe B n is the n-th component of A
abbrev B (n : ℕ) (ω : Ω) : U₂ := ω n

-- the sequence of measures μ n which will form the contradiction
example n : Measurable (fun ω ↦ (A ω, B n ω)) := by measurability

def μ n := (θ ρ).map (fun ω ↦ (A ω, B n ω))

lemma hasLaw_proj_A (n : ℕ) : HasLaw (fun ω ↦ A ω n) ρ (θ ρ) := by
  sorry

-- theorem: μ n converges weakly to θ

-- theorem: if the strong skorokhod theorem conclusion holds, then ρ is a dirac measure
theorem measure_const_of_strong_skorokhod
    (Ω' : Type*) [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (A' : Ω' → U₁)
    (B' : ℕ → Ω' → U₂)
    (B'_lim : Ω' → U₂)
    (hmeas : Measurable A' ∧ ∀ n, Measurable (B' n) ∧ Measurable B'_lim)
    (h_law : ∀ n, IdentDistrib (fun ω ↦ (A ω, B n ω)) (fun ω' ↦ (A' ω', B' n ω')) (θ ρ) P')
    (h_conv : ∀ᵐ ω' ∂P', Tendsto (fun n ↦ B' n ω') atTop (nhds (B'_lim ω'))) :
    ∃ x : V, ρ = Measure.dirac x := by
  suffices IsZeroOneMeasure ρ by
    apply IsZeroOneMeasure.exists_eq_dirac
  -- the n-th component of A' agrees a.s. with B' n
  have A'_eq_B' : ∀ n, ∀ᵐ ω' ∂P', A' ω' n = B' n ω' := by
    intro n
    rw [← Filter.EventuallyEq]
    rw [ae_eq_iff_map_meas_diag_comp_zero (by measurability) (by measurability)]
    have : IdentDistrib (fun ω ↦ (A ω n, B n ω)) (fun ω' ↦ (A' ω' n, B' n ω')) (θ ρ) P' :=
      (h_law n).comp (u := fun (u, v) ↦ ((u n, v))) (by measurability)
    rw [← this.map_eq, ← ae_eq_iff_map_meas_diag_comp_zero (by measurability) (by measurability)]
    simp
  let G₁ : ProbabilityMeasure (U₂ × U₂) := ⟨Measure.prod ρ ρ, inferInstance⟩
  let G₂ : ProbabilityMeasure (U₂ × U₂) := ⟨ρ.map (fun x ↦ (x,x)), ?_⟩
  swap; · refine Measure.isProbabilityMeasure_map ?_; measurability
  let G n : ProbabilityMeasure (U₂ × U₂) := ⟨P'.map ((fun ω' ↦ (B' n ω', B' (n + 1) ω'))), ?_⟩
  swap; · refine Measure.isProbabilityMeasure_map ?_; sorry

  have h_tt_1 : Tendsto G atTop (nhds G₁) := by
    refine EventuallyEq.tendsto (Eventually.of_forall fun n ↦ ?_)
    apply Subtype.ext
    simp only [G, G₁]
    apply HasLaw.map_eq
    have : ∀ᵐ ω' ∂P', (B' n ω', B' (n + 1) ω') = (A' ω' n, A' ω' (n + 1)) := by
      filter_upwards [A'_eq_B' n, A'_eq_B' (n + 1)] using by aesop
    rw [← Filter.EventuallyEq] at this
    apply HasLaw.congr _ this
    have : IdentDistrib (fun ω ↦ (A ω n, A ω (n + 1)))
        (fun ω' ↦ (A' ω' n, A' ω' (n + 1))) (θ ρ) P' :=
      (h_law 0).comp (u := fun (u, v) ↦ (u n, u (n + 1))) (by measurability)
    apply this.hasLaw
    apply IndepFun.hasLaw_prod
    · apply hasLaw_proj_A
    · apply hasLaw_proj_A
    apply iIndepFun.indepFun (f := fun n ω ↦ A ω n)
    · apply ProbabilityTheory.iIndepFun_infinitePi (X := fun n v ↦ v)
      measurability
    simp
  have h_tt_2 : Tendsto G atTop (nhds G₂) := by
    sorry -- weak convergence to G₂
  have hG_eq := tendsto_nhds_unique h_tt_1 h_tt_2
  constructor
  intro s hs
  suffices (ρ s) * (ρ s) = ρ s by
    sorry
  have hs1 : ρ s * ρ s = G₁ (s ×ˢ s) := by simp [← Measure.prod_prod, G₁]
  have hs2 : ρ s = G₂ (s ×ˢ s) := by
    simp only [ProbabilityMeasure.mk_apply, G₂]
    rw [Measure.map_apply (by measurability) (by measurability)]
    simp
  rw [hs1, hs2]
  congr
end
