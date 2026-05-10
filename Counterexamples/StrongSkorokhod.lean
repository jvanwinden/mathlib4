import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Filter

/--
If the push-forward measure of `(X, Y)` assigns zero mass to the complement
of the diagonal, then `X = Y` almost everywhere.
-/
lemma ae_eq_of_map_supported_diagonal
    {Ω : Type*} {α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableEq α] {μ : Measure Ω}
    {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y)
    (h : μ.map (fun ω => (X ω, Y ω)) (Set.diagonal α)ᶜ = 0) :
    X =ᵐ[μ] Y := by
  rw [Measure.map_apply (by measurability) (by measurability)] at h
  simpa

lemma ae_eq_iff_map_meas_diag_comp_zero
    {Ω : Type*} {α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableEq α] {μ : Measure Ω}
    {X Y : Ω → α} (hX : Measurable X) (hY : Measurable Y) :
    X =ᵐ[μ] Y ↔ (μ.map (fun ω => (X ω, Y ω)) (Set.diagonal α)ᶜ = 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · sorry
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
    (Ω' : Type*) [MeasurableSpace Ω'] {P' : Measure Ω'}
    (A' : Ω' → U₁)
    (B' : ℕ → Ω' → U₂)
    (B'_lim : Ω' → U₂)
    (hmeas : Measurable A' ∧ ∀ n, Measurable (B' n) ∧ Measurable B'_lim)
    (h_law : ∀ n, IdentDistrib (fun ω ↦ (A ω, B n ω)) (fun ω' ↦ (A' ω', B' n ω')) (θ ρ) P')
    (h_conv : ∀ᵐ ω' ∂P', Tendsto (fun n ↦ B' n ω') atTop (nhds (B'_lim ω'))) :
    ∃ x : V, ρ = Measure.dirac x := by
  -- the n-th component of A' agrees a.s. with B' n
  have : ∀ n, ∀ᵐ ω' ∂P', A' ω' n = B' n ω' := by
    intro n
    rw [← Filter.EventuallyEq]
    rw [ae_eq_iff_map_meas_diag_comp_zero (by measurability) (by measurability)]
    have : IdentDistrib (fun ω ↦ (A ω n, B n ω)) (fun ω' ↦ (A' ω' n, B' n ω')) (θ ρ) P' :=
      (h_law n).comp (u := fun (u, v) ↦ ((u n, v))) (by measurability)
    rw [← this.map_eq, ← ae_eq_iff_map_meas_diag_comp_zero (by measurability) (by measurability)]
    simp
  -- the joint law of B' n × B' m is ρ × ρ
  have : ∀ n m, n ≠ m → HasLaw (fun ω' ↦ (B' n ω', B' m ω')) (Measure.prod ρ ρ) P' := by
    intro n m hmn
    have : ∀ᵐ ω' ∂P', (B' n ω', B' m ω') = (A' ω' n, A' ω' m) := by
      filter_upwards [this n, this m] with ω' hω'1 hω'2 using by aesop
    rw [← Filter.EventuallyEq] at this
    apply HasLaw.congr _ this
    have : IdentDistrib (fun ω ↦ (A ω n, A ω m)) (fun ω' ↦ (A' ω' n, A' ω' m)) (θ ρ) P' :=
      (h_law 0).comp (u := fun (u, v) ↦ (u n, u m)) (by measurability)
    apply this.hasLaw
    apply IndepFun.hasLaw_prod
    · apply hasLaw_proj_A
    · apply hasLaw_proj_A
    apply iIndepFun.indepFun (f := fun n ω ↦ A ω n)
    · apply ProbabilityTheory.iIndepFun_infinitePi (X := fun n v ↦ v)
      measurability
    exact hmn
  -- ρ × ρ is concentrated on the diagonal
  have : (Measure.prod ρ ρ) (Set.diagonal V) = 1 := by
    sorry
  -- thus ρ is a dirac measure
  sorry

end
