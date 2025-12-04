import Mathlib

open MeasureTheory

namespace ZkLinalg

@[simp] def ProbImplies {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R R' : Type*} (r : Ω → R) (P : R → Prop)
    (r' : Ω → R') (Q : R' → Prop) (p : ℝ) : Prop :=
  (0 ≤ p ∧ p ≤ 1) ∧ μ {ω | P (r ω) ∧ ¬ Q (r' ω)} ≤ ENNReal.ofReal p

/-- Chaining: if `μ {ω | P(r ω) ∧ ¬ Q(r' ω)} ≤ p` and `μ {ω | Q(r' ω) ∧ ¬ T(r'' ω)} ≤ p'`, with `p,p' ∈ [0,1]`, then `μ {ω | P(r ω) ∧ ¬ T(r'' ω)} ≤ p + p'`. -/
lemma chaining_probabilistic
    {Ω R R' R'' : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → R) (P : R → Prop)
    (r' : Ω → R') (Q : R' → Prop)
    (r'' : Ω → R'') (T : R'' → Prop)
    {p p' : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) (hp' : 0 ≤ p' ∧ p' ≤ 1)
    (h₁ : μ {ω | P (r ω) ∧ ¬ Q (r' ω)} ≤ ENNReal.ofReal p)
    (h₂ : μ {ω | Q (r' ω) ∧ ¬ T (r'' ω)} ≤ ENNReal.ofReal p') :
    μ {ω | P (r ω) ∧ ¬ T (r'' ω)} ≤ ENNReal.ofReal (p + p') :=
by classical
   simpa [ENNReal.ofReal_add hp.1 hp'.1] using (measure_mono fun _ h => if hQ : _ then .inr ⟨hQ, h.2⟩
     else .inl ⟨h.1, hQ⟩).trans ((measure_union_le _ _).trans (add_le_add h₁ h₂))

/-- Reed–Solomon matrix with evaluation points `αs : Fin m → α`: the entry is `(αs i)^(j)`, with column index `j` used as a natural exponent. -/
@[simp] def reedSolomonMatrix {α : Type*} [Semiring α]
    {m n : ℕ} (αs : Fin m → α) : Matrix (Fin m) (Fin n) α :=
  fun i j => (αs i) ^ (j : ℕ)

/-- Conjunction: for independent sources `r` and `r'`, if both `P(r)` and `T(r')` imply a deterministic statement `Q` with error probabilities `p` and `p'`, then `P(r) ∧ T(r')` implies `Q` with error at most `p * p'`. -/
lemma conjunction_probabilistic
    {Ω R R' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] [MeasurableSpace R']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → R) (P : R → Prop)
    (r' : Ω → R') (T : R' → Prop)
    (Q : Prop) {p p' : ℝ}
    (hP : MeasurableSet {x : R | P x})
    (hT : MeasurableSet {x : R' | T x})
    (hindep : ProbabilityTheory.IndepFun r r' μ)
    (hp : 0 ≤ p ∧ p ≤ 1)
    (h₁ : μ {ω | P (r ω) ∧ ¬ Q} ≤ ENNReal.ofReal p)
    (h₂ : μ {ω | T (r' ω) ∧ ¬ Q} ≤ ENNReal.ofReal p') :
    μ {ω | (P (r ω) ∧ T (r' ω)) ∧ ¬ Q} ≤ ENNReal.ofReal (p * p') :=
by
  by_cases hQ : Q <;> simp [hQ]
  calc μ {ω | P (r ω) ∧ T (r' ω)} = μ {ω | P (r ω)} * μ {ω | T (r' ω)} := by
        simpa using ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.1 hindep {x | P x} {x' | T x'} hP hT
    _ ≤ ENNReal.ofReal (p * p') := by
        simp [ENNReal.ofReal_mul hp.1, mul_le_mul' (by simpa [hQ] using h₁) (by simpa [hQ] using h₂)]

/-- A matrix (generator of a linear code) has distance at least `d` if every nonzero codeword has Hamming weight ≥ d. -/
@[simp] def codeHasDistanceAtLeast {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
    {m n : ℕ} (G : Matrix (Fin m) (Fin n) α) (d : ℕ) : Prop :=
  ∀ x : (Fin n → α), x ≠ 0 →
    (Finset.univ.filter (fun i : Fin m => Matrix.mulVec G x i ≠ 0)).card ≥ d

/-- Independence + finite-union bound: for any finite set `A` of values of `r'`,
`μ({r = i ∧ r' ∈ A}) ≤ μ({r = i}) * ∑_{j∈A} μ({r' = j})`.
This packages a union bound over `A` together with the product rule provided by `h_indep`.
-/
lemma measure_inter_preimage_finset_le_mul_sum
  {Ω α β : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (r : Ω → α) [DecidableEq α]
  (r' : Ω → β) [DecidableEq β]
  (h_indep : ∀ i : α, ∀ j : β,
    μ {ω | r ω = i ∧ r' ω = j} = μ {ω | r ω = i} * μ {ω | r' ω = j})
  (i : α) (A : Finset β) :
  μ {ω | r ω = i ∧ r' ω ∈ A}
    ≤ μ {ω | r ω = i} * ∑ j ∈ A, μ {ω | r' ω = j} :=
by
  rw [show {ω | r ω = i ∧ r' ω ∈ A} = ⋃ j ∈ A, {ω | r ω = i ∧ r' ω = j} from by
        ext; simp [Set.mem_iUnion], Finset.mul_sum]
  exact (measure_biUnion_finset_le A _).trans (by simp [h_indep])

/-- Zero-position bound from code distance: if `G'` has distance at least `d'`, then for any
nonzero message `y`, at most `m' - d'` rows of `G'` are orthogonal to `y`.
Equivalently, the zero-set of `G' · y` has cardinality ≤ `m' - d'`. -/
lemma zero_positions_card_le_of_distance
  {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
  {m' k : ℕ}
  (G' : Matrix (Fin m') (Fin k) α) {d' : ℕ}
  (hG' : codeHasDistanceAtLeast G' d')
  (y : Fin k → α) (hy : y ≠ 0) :
  (Finset.univ.filter (fun j : Fin m' => Matrix.mulVec G' y j = 0)).card ≤ m' - d' :=
by simp [Nat.eq_sub_of_add_eq $ Finset.filter_card_add_filter_neg_card_eq_card (G'.mulVec y · = 0), Nat.sub_le_sub_left (hG' y hy)]

/-- Reduced matrix zero check: sampling independent random rows `g_r` of `G` and `g'_{r'}` of `G'`, the scalar `g'_{r'}^T · (X · g_r)` being zero implies `X = 0` with error at most `(1 - d/m) + (1 - d'/m')`. -/
lemma reduced_matrix_zero_check
    {α : Type*} [CommSemiring α] [DecidableEq α] [Zero α]
    {m n k m' : ℕ}
    (G : Matrix (Fin m) (Fin n) α) {d : ℕ}
    (hG : codeHasDistanceAtLeast G d)
    (G' : Matrix (Fin m') (Fin k) α) {d' : ℕ}
    (hG' : codeHasDistanceAtLeast G' d')
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin m)
    (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
    (r' : Ω → Fin m')
    (h_unif' : ∀ i : Fin m', μ {ω | r' ω = i} = (1 : ENNReal) / (m' : ENNReal))
    (h_indep : ∀ i : Fin m, ∀ j : Fin m',
      μ {ω | r ω = i ∧ r' ω = j} = μ {ω | r ω = i} * μ {ω | r' ω = j})
    (X : Matrix (Fin k) (Fin n) α) :
    μ {ω | ((Finset.univ.sum fun j : Fin k => (G' (r' ω) j) * (Matrix.mulVec X (fun j => G (r ω) j) j)) = 0)
           ∧ ¬ (X = 0)}
      ≤ ENNReal.ofReal ((1 - (d : ℝ) / (m : ℝ)) + (1 - (d' : ℝ) / (m' : ℝ))) :=
by
  by_cases hX0 : X = 0; · simp [hX0]
  obtain ⟨i0, j0, hxij⟩ : ∃ i : Fin k, ∃ j : Fin n, X i j ≠ 0 := by by_contra h; push_neg at h; exact hX0 (by ext i j; simpa using h i j)
  set y := fun ω => Matrix.mulVec X (fun j => G (r ω) j); set E := {ω | (∑ j, G' (r' ω) j * y ω j) = 0 ∧ ¬X = 0}
  set E1 := {ω | y ω = 0 ∧ ¬X = 0}; set E2 := {ω | (∑ j, G' (r' ω) j * y ω j) = 0 ∧ y ω ≠ 0}
  have hx0_ne : (fun j => X i0 j) ≠ 0 := fun hx => hxij (by simpa using congrArg (· j0) hx)
  have hycol_ne : (fun i => X i j0) ≠ 0 := fun h => hxij (by simpa using congrArg (· i0) h)
  have hd_le_m : d ≤ m := by simpa [Fintype.card_fin] using (hG _ hx0_ne).trans (Finset.card_filter_le _ _)
  have hd'_le_m' : d' ≤ m' := by simpa [Fintype.card_fin] using (hG' _ hycol_ne).trans (Finset.card_filter_le _ _)
  have hE1_le : μ E1 ≤ ENNReal.ofReal (1 - (d : ℝ) / m) := by
    set yG := fun i => Matrix.mulVec G (fun j => X i0 j) i; set S := Finset.univ.filter fun i => yG i = 0
    have hE1_sub : E1 ⊆ {ω | yG (r ω) = 0} := fun ω hω => by simpa [yG, Matrix.mulVec, dotProduct, mul_comm] using (by simpa [y, Matrix.mulVec, dotProduct] using congrArg (· i0) hω.1 : (∑ j : Fin n, X i0 j * G (r ω) j) = 0)
    have hμ_yG0 : μ {ω | yG (r ω) = 0} ≤ ((m - d : ℕ) : ENNReal) / m := by
      have h_event : {ω | yG (r ω) = 0} = ⋃ i ∈ S, {ω | r ω = i} := by ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, S]; exact ⟨fun h => ⟨r ω, h, rfl⟩, fun ⟨i, hi, hri⟩ => by simp [hri, hi]⟩
      calc μ {ω | yG (r ω) = 0} ≤ ∑ i ∈ S, μ {ω | r ω = i} := by rw [h_event]; exact measure_biUnion_finset_le S _
        _ ≤ _ := by simp [h_unif, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]; exact mul_le_mul' (by exact_mod_cast ZkLinalg.zero_positions_card_le_of_distance G hG _ hx0_ne) le_rfl
    by_cases hm0 : m = 0; · simp [hm0]; exact prob_le_one
    simpa [one_sub_div (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)).ne', Nat.cast_sub hd_le_m, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0))] using (measure_mono hE1_sub).trans hμ_yG0
  have hE2_le : μ E2 ≤ ENNReal.ofReal (1 - (d' : ℝ) / m') := by
    set yrow := fun i => Matrix.mulVec X fun j => G i j; set Z := fun i => Finset.univ.filter fun j => (∑ t, G' j t * yrow i t) = 0
    set T := Finset.univ.filter fun i => yrow i ≠ 0; set C : ENNReal := (m' - d' : ℕ) / m'
    have hE2_le_C : μ E2 ≤ C := by
      have hμ_E2_le : μ E2 ≤ ∑ i ∈ T, μ {ω | r ω = i ∧ r' ω ∈ Z i} := (measure_mono fun ω hω => Set.mem_iUnion.2 ⟨r ω, Set.mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨by simp, by simpa [yrow, y] using hω.2⟩, by simp only [Set.mem_setOf_eq, true_and]; exact Finset.mem_filter.2 ⟨by simp, by simpa [y, yrow] using hω.1⟩⟩⟩).trans (measure_biUnion_finset_le T _)
      have hZ_bound : ∀ i ∈ T, (Z i).card ≤ m' - d' := fun i hi => ZkLinalg.zero_positions_card_le_of_distance G' hG' _ (Finset.mem_filter.mp hi).2
      calc μ E2 ≤ ∑ i ∈ T, μ {ω | r ω = i} * (∑ j ∈ Z i, μ {ω | r' ω = j}) := hμ_E2_le.trans (Finset.sum_le_sum fun i hi => ZkLinalg.measure_inter_preimage_finset_le_mul_sum μ r r' h_indep i (Z i))
        _ ≤ ∑ i ∈ T, μ {ω | r ω = i} * C := Finset.sum_le_sum fun i hi => by simp only [h_unif', Finset.sum_const, nsmul_eq_mul, C, div_eq_mul_inv, one_mul]; exact mul_le_mul_left' (mul_le_mul' (by exact_mod_cast hZ_bound i hi) le_rfl) _
        _ ≤ (∑ i ∈ T, μ {ω | r ω = i}) * C := by rw [Finset.sum_mul]
        _ ≤ 1 * C := mul_le_mul_right' (by
          by_cases hm0 : m = 0; · subst hm0; simp [T]
          simp only [h_unif, Finset.sum_const, nsmul_eq_mul]
          have hT_le : (T.card : ENNReal) ≤ m := by have := Finset.card_le_univ T; simp [Fintype.card_fin] at this; exact_mod_cast this
          exact (mul_le_mul' hT_le le_rfl).trans (by rw [ENNReal.mul_div_cancel' (by simp [hm0]) (by simp)])) _
        _ = C := one_mul C
    by_cases hm0' : m' = 0; · simp [hm0']; exact prob_le_one
    simpa [C, one_sub_div (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0')).ne', Nat.cast_sub hd'_le_m', ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0'))] using hE2_le_C
  have hnonneg1 : 0 ≤ 1 - (d : ℝ) / m := by rcases eq_or_ne m 0 with rfl | hm0; simp; exact sub_nonneg.mpr (div_le_one_of_le₀ (by exact_mod_cast hd_le_m) (by positivity))
  have hnonneg2 : 0 ≤ 1 - (d' : ℝ) / m' := by rcases eq_or_ne m' 0 with rfl | hm0'; simp; exact sub_nonneg.mpr (div_le_one_of_le₀ (by exact_mod_cast hd'_le_m') (by positivity))
  have hE_subset : E ⊆ E1 ∪ E2 := fun ω ⟨hs, hX⟩ => by by_cases hy : y ω = 0 <;> [exact Or.inl ⟨hy, hX⟩; exact Or.inr ⟨hs, hy⟩]
  simpa [E, ENNReal.ofReal_add hnonneg1 hnonneg2] using ((measure_mono hE_subset).trans (measure_union_le _ _)).trans (add_le_add hE1_le hE2_le)

/-- Matrix zero check: sampling a random row `g_r` of `G` and testing `X · g_r = 0` certifies `X = 0` with error probability at most `1 - d/m`. -/
lemma matrix_zero_check
    {α : Type*} [CommSemiring α] [DecidableEq α] [Zero α]
    {m n k : ℕ}
    (G : Matrix (Fin m) (Fin n) α) {d : ℕ}
    (hG : codeHasDistanceAtLeast G d)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin m)
    (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
    (X : Matrix (Fin k) (Fin n) α) :
    μ {ω | Matrix.mulVec X (fun j => G (r ω) j) = 0 ∧ ¬ (X = 0)}
      ≤ ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) :=
by
  by_cases hX : X = 0
  · simp [hX]
  obtain ⟨i0, j0, hxij⟩ : ∃ i : Fin k, ∃ j : Fin n, X i j ≠ 0 := by
    by_contra h; push_neg at h; exact hX (by ext i j; simpa using h i j)
  set x : Fin n → α := fun j => X i0 j
  have hx0 : x ≠ 0 := by
    intro hx; exact hxij (by simpa [x] using congrArg (fun f : Fin n → α => f j0) hx)
  set y : Fin m → α := fun i => Matrix.mulVec G x i
  have hmono :
      μ {ω | Matrix.mulVec X (fun j => G (r ω) j) = 0 ∧ X ≠ 0}
        ≤ μ {ω | Matrix.mulVec G x (r ω) = 0 ∧ ¬ (x = 0)} :=
    measure_mono (by
      intro ω hω
      have h0 : Matrix.mulVec X (fun j => G (r ω) j) i0 = 0 := by
        simpa using congrArg (fun f => f i0) hω.1
      have : Matrix.mulVec G x (r ω) = 0 := by
        simpa [x, Matrix.mulVec, dotProduct, mul_comm] using h0
      exact ⟨this, hx0⟩)
  set s : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => y i = 0)
  have hμ_div : μ {ω | y (r ω) = 0} ≤ ((m - d : ℕ) : ENNReal) / (m : ENNReal) := by
    have hsubset_union : {ω | y (r ω) = 0} ⊆ ⋃ i ∈ s, {ω | r ω = i} := by
      intro ω hω; refine Set.mem_iUnion.2 ?_; exact ⟨r ω, Set.mem_iUnion.2 ⟨by simpa [s, hω], by simp⟩⟩
    have h_s_le : s.card ≤ m - d := by
      simpa [s, y] using
        ZkLinalg.zero_positions_card_le_of_distance (G' := G) (hG' := hG) (y := x) (hy := hx0)
    calc
      μ {ω | y (r ω) = 0} ≤ μ (⋃ i ∈ s, {ω | r ω = i}) := measure_mono hsubset_union
      _ ≤ ∑ i ∈ s, μ {ω | r ω = i} := by
            simpa using
              (MeasureTheory.measure_biUnion_finset_le (μ := μ) s (fun i : Fin m => {ω | r ω = i}))
      _ = s.card • ((1 : ENNReal) / (m : ENNReal)) := by
            simp [h_unif, Finset.sum_const]
      _ ≤ ((m - d : ℕ) : ENNReal) * ((1 : ENNReal) / (m : ENNReal)) := by
            simpa [nsmul_eq_mul] using (mul_le_mul' (by exact_mod_cast h_s_le) le_rfl)
      _ = ((m - d : ℕ) : ENNReal) / (m : ENNReal) := by simp [div_eq_mul_inv]
  have htoY : μ {ω | Matrix.mulVec G x (r ω) = 0 ∧ ¬ x = 0} ≤ μ {ω | y (r ω) = 0} :=
    measure_mono (by intro ω hω; exact hω.1)
  by_cases hm0 : m = 0
  · have hof : ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) = 1 := by
      have : (m : ℝ) = 0 := by simpa using congrArg (fun n : ℕ => (n : ℝ)) hm0
      simp [this]
    have hμ_le_one : μ {ω | y (r ω) = 0} ≤ 1 := by
      simpa using
        (measure_mono (s := {ω | y (r ω) = 0}) (t := Set.univ) (by intro _ _; trivial) :
          μ {ω | y (r ω) = 0} ≤ μ (Set.univ : Set Ω))
    have : μ {ω | Matrix.mulVec X (fun j => G (r ω) j) = 0 ∧ X ≠ 0} ≤ 1 :=
      hmono.trans (htoY.trans hμ_le_one)
    simpa [hof] using this
  ·
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hd_le_m : d ≤ m := by
      have hge :
          (Finset.univ.filter (fun i : Fin m => y i ≠ 0)).card ≥ d := by
        simpa [y] using hG x hx0
      have hle :
          (Finset.univ.filter (fun i : Fin m => y i ≠ 0)).card ≤ m := by
        simpa [Fintype.card_fin] using
          (Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i : Fin m => y i ≠ 0))
      exact hge.trans hle
    have hof : ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ))
        = ((m - d : ℕ) : ENNReal) / (m : ENNReal) := by
      calc
        ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ))
            = ENNReal.ofReal (((m : ℝ) - (d : ℝ)) / (m : ℝ)) := by
              simp [one_sub_div (a := (d : ℝ)) (b := (m : ℝ)) hm_ne]
        _ = ENNReal.ofReal ((m : ℝ) - (d : ℝ)) / (m : ENNReal) := by
              simpa using ENNReal.ofReal_div_of_pos (x := ((m : ℝ) - (d : ℝ))) (y := (m : ℝ)) hm_pos
        _ = ((m - d : ℕ) : ENNReal) / (m : ENNReal) := by
          have : ENNReal.ofReal ((m : ℝ) - (d : ℝ)) = ((m - d : ℕ) : ENNReal) := by
            simpa using (show ENNReal.ofReal ((m : ℝ) - (d : ℝ)) = ENNReal.ofReal ((m - d : ℕ) : ℝ) by
              simp [Nat.cast_sub hd_le_m])
          simp [this]
    have : μ {ω | Matrix.mulVec X (fun j => G (r ω) j) = 0 ∧ X ≠ 0}
        ≤ ((m - d : ℕ) : ENNReal) / (m : ENNReal) :=
      (hmono.trans (htoY.trans hμ_div))
    simpa [hof] using this

/-- Cardinality bound from the complement: if at least `d` elements fail `p`, then
at most `|α| - d` elements satisfy `p`. -/
lemma filter_card_le_of_compl_card_ge
  {α : Type*} [Fintype α] [DecidableEq α]
  {p : α → Prop} [DecidablePred p] {d : ℕ} :
  (Finset.univ.filter (fun i => ¬ p i)).card ≥ d →
  (Finset.univ.filter (fun i => p i)).card ≤ Fintype.card α - d :=
by
  intro h
  exact
    (Nat.le_sub_iff_add_le (h.trans (Finset.card_filter_le Finset.univ _))).2
      (by
        simpa [Finset.filter_card_add_filter_neg_card_eq_card] using
          Nat.add_le_add_left h (Finset.univ.filter p).card)

/-- Zero check: if every nonzero codeword `G·z` has at least `d` nonzero coordinates, then sampling a random row index `r` and observing `(G·x)_r = 0` implies `x = 0` with error probability at most `1 - d/m` (for uniform `r`). -/
lemma zero_check
    {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
    {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) α) {d : ℕ}
    (hG : codeHasDistanceAtLeast G d)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin m)
    (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
    (x : Fin n → α) :
    μ {ω | (Matrix.mulVec G x (r ω) = 0) ∧ ¬ (x = 0)}
      ≤ ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) :=
by
  by_cases hx : x = 0; · simp [hx]
  set s := Finset.univ.filter fun i => Matrix.mulVec G x i = 0
  have hμ : μ {ω | Matrix.mulVec G x (r ω) = 0} ≤ ((m - d : ℕ) : ENNReal) / m := by
    rw [show {ω | Matrix.mulVec G x (r ω) = 0} = ⋃ i ∈ s, {ω | r ω = i} by ext; simp [s]]
    refine (measure_biUnion_finset_le s _).trans ?_; simp only [h_unif, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
    exact mul_le_mul' (by exact_mod_cast ZkLinalg.zero_positions_card_le_of_distance G hG x hx) le_rfl
  by_cases hm0 : m = 0; · simpa [hm0] using prob_le_one
  have hmp : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  simpa [one_sub_div hmp.ne', Nat.cast_sub (by simpa [Fintype.card_fin] using (hG x hx).trans (Finset.card_filter_le Finset.univ _) : d ≤ m), ENNReal.ofReal_div_of_pos hmp] using (measure_mono fun _ h => h.1).trans hμ

/-- If two vectors `y, y' : Fin n → α` agree on all coordinates except possibly at `k`,
and both have zero dot product with a fixed `x` with `x k ≠ 0`, then they are equal.
This is the key injectivity step used in the Hadamard distance bound. -/
lemma eq_of_dot_zero_agree_off
  {α : Type*} [Field α]
  {n : ℕ} {x y y' : Fin n → α} {k : Fin n}
  (hk : x k ≠ 0)
  (hy : Finset.univ.sum (fun j : Fin n => y j * x j) = 0)
  (hy' : Finset.univ.sum (fun j : Fin n => y' j * x j) = 0)
  (hrest : ∀ j : Fin n, j ≠ k → y j = y' j) :
  y = y' :=
by
  have hk0 : (y k - y' k) * x k = 0 := by
    have hsum : ∑ j, (y j - y' j) * x j = 0 := by
      simp [sub_mul, Finset.sum_sub_distrib, hy, hy']
    have hsingle : ∑ j : Fin n, (y j - y' j) * x j = (y k - y' k) * x k := by
      refine Finset.sum_eq_single k (fun j _ hj => ?_) (by simp)
      simp [hrest j hj]
    simpa [hsingle] using hsum
  have hkk : y k = y' k := sub_eq_zero.mp ((mul_eq_zero.mp hk0).resolve_right hk)
  ext j
  by_cases hj : j = k
  · simpa [hj] using hkk
  · simpa using hrest j hj

/-- Hadamard distance bound: for any nonzero message `x`, at most `|α|^{n-1}` rows are orthogonal to `x`, hence Hamming weight ≥ `|α|^n - |α|^{n-1}`. -/
lemma hadamard_distance
    {α : Type*} [Field α] [Fintype α] [DecidableEq α]
    {n : ℕ} :
    codeHasDistanceAtLeast
      ((fun (i : Fin (Fintype.card (Fin n → α))) (j : Fin n) =>
          ((Fintype.equivFin (Fin n → α)).symm i) j) :
        Matrix (Fin (Fintype.card (Fin n → α))) (Fin n) α)
      ((Fintype.card α) ^ n - (Fintype.card α) ^ (n - 1)) :=
by
  intro x hx; set e := (Fintype.equivFin (Fin n → α)).symm
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by by_contra h; push_neg at h; exact hx (funext fun _ => by simp_all)
  set Z := Finset.univ.filter fun i => (∑ j, e i j * x j) = 0
  have hZ_le : Z.card ≤ (Fintype.card α) ^ (n - 1) := by
    simpa [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective
      (fun (d : { i // i ∈ Z }) (s : { j : Fin n // j ≠ k }) => e d.1 s.1) fun z z' hφ =>
      Subtype.ext (e.injective (ZkLinalg.eq_of_dot_zero_agree_off hk (Finset.mem_filter.1 z.property).2
        (Finset.mem_filter.1 z'.property).2 fun j hj => congrArg (· ⟨j, hj⟩) hφ))
  have h_eq : (Finset.univ.filter fun i => (∑ j, e i j * x j) ≠ 0).card
      = (Finset.univ : Finset (Fin (Fintype.card (Fin n → α)))).card - Z.card := Nat.eq_sub_of_add_eq (by
    convert Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin (Fintype.card (Fin n → α)))))
      (p := fun i => (∑ j, e i j * x j) = 0) using 1; simp [Nat.add_comm, Z])
  simpa [Matrix.mulVec, dotProduct] using (by simp [h_eq, Finset.card_univ, Fintype.card_fin, Nat.sub_le_sub_left hZ_le] :
    (Finset.univ.filter fun i => (∑ j, e i j * x j) ≠ 0).card ≥ (Fintype.card α) ^ n - (Fintype.card α) ^ (n - 1))

/-- Hadamard matrix: rows enumerate all vectors in `α^n`. The number of rows is `|α|^n`. -/
@[simp] noncomputable def hadamardMatrix {α : Type*} [Semiring α] [Fintype α]
    {n : ℕ} :
    Matrix (Fin (Fintype.card (Fin n → α))) (Fin n) α :=
  fun i j => ((Fintype.equivFin (Fin n → α)).symm i) j

/-- Kronecker-delta collapse for sums over `Fin n` when the condition is on the natural coercions. -/
lemma sum_ite_coe_fin_eq
  {α : Type*} [AddCommMonoid α]
  {n : ℕ} (f : Fin n → α) (k : Fin n) :
  (∑ j : Fin n, (if ((k : ℕ) = (j : ℕ)) then f j else 0)) = f k :=
by
  refine (Finset.sum_eq_single k (fun j _ hj => by
    simp [show (k : ℕ) ≠ (j : ℕ) from fun h => hj (Fin.val_injective h.symm)]) (by simp)).trans ?_;
  simp

lemma card_eval_zero_le_natDegree_of_injective
  {α : Type*} [Field α] [DecidableEq α]
  {m : ℕ} (αs : Fin m → α) (h_inj : Function.Injective αs)
  (f : Polynomial α) (hf : f ≠ 0) :
  (Finset.univ.filter (fun i : Fin m => Polynomial.eval (αs i) f = 0)).card ≤ f.natDegree :=
by exact (Finset.card_image_of_injOn fun _ _ _ _ h => h_inj h).symm.trans_le (Polynomial.card_le_degree_of_subset_roots fun _ ha => by obtain ⟨_, hi, rfl⟩ := Finset.mem_image.1 ha; simp [Polynomial.mem_roots hf, (Finset.mem_filter.1 hi).2])

/-- Reed–Solomon distance bound: every nonzero codeword has Hamming weight ≥ `m - n + 1`. -/
lemma reed_solomon_distance
    {α : Type*} [Field α] [DecidableEq α]
    {m n : ℕ} (h_mn : n ≤ m)
    (αs : Fin m → α) (h_inj : Function.Injective αs) :
    codeHasDistanceAtLeast (reedSolomonMatrix (α:=α) (m:=m) (n:=n) αs) (m - n + 1) :=
by
  cases n with
  | zero => intro x hx; exact (hx (by ext j; exact Fin.elim0 j)).elim
  | succ k =>
      intro x hx
      let f : Polynomial α :=
        ∑ j : Fin (k + 1), Polynomial.C (x j) * (Polynomial.X : Polynomial α) ^ (j : ℕ)
      have h_eval : ∀ i : Fin m,
          Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i
            = Polynomial.eval (αs i) f := by
        intro i
        have hx1 :
            Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i
              = ∑ j : Fin (k+1), (αs i) ^ (j : ℕ) * x j := by
          simp [Matrix.mulVec, reedSolomonMatrix, dotProduct]
        have hx2 : ∑ j : Fin (k+1), (αs i) ^ (j : ℕ) * x j
              = ∑ j : Fin (k+1), x j * (αs i) ^ (j : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro j _; simp [mul_comm]
        have hx3 :
            Polynomial.eval (αs i) f
              = ∑ j : Fin (k+1), x j * (αs i) ^ (j : ℕ) := by
          simp [f, Polynomial.eval_finset_sum, Polynomial.eval_C, Polynomial.eval_X,
                Polynomial.eval_pow, Polynomial.eval_mul]
        calc
          Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i
              = ∑ j : Fin (k+1), (αs i) ^ (j : ℕ) * x j := hx1
          _ = ∑ j : Fin (k+1), x j * (αs i) ^ (j : ℕ) := hx2
          _ = Polynomial.eval (αs i) f := by simpa using hx3.symm
      have hf_ne : f ≠ 0 := by
        obtain ⟨j0, hj0⟩ : ∃ j : Fin (k + 1), x j ≠ 0 := by
          by_contra hall; push_neg at hall
          exact hx (funext (by intro j; simp [hall j]))
        have hcoeff : f.coeff (j0 : ℕ) = x j0 := by
          simpa [f] using
            (sum_ite_coe_fin_eq (f := x) (k := j0))
        intro hf0
        have : f.coeff (j0 : ℕ) = 0 := by
          simpa using congrArg (fun p : Polynomial α => p.coeff (j0 : ℕ)) hf0
        exact hj0 (by simpa [hcoeff] using this)
      have hdeg : f.natDegree ≤ k := by
        refine (Polynomial.natDegree_le_iff_coeff_eq_zero).2 ?_
        intro N hNk
        have hcoeff_sum : (∑ j : Fin (k+1), Polynomial.C (x j) * Polynomial.X ^ (j : ℕ)).coeff N = ∑ j : Fin (k+1), if N = (j : ℕ) then x j else 0 := by simp
        have hall_zero : ∀ j : Fin (k+1), (if N = (j : ℕ) then x j else 0 : α) = 0 := by
          intro j
          have hj : (j : ℕ) ≤ k := Nat.le_of_lt_succ j.is_lt
          have hNe : (N : ℕ) ≠ (j : ℕ) := ne_of_gt (lt_of_le_of_lt hj hNk)
          simp [hNe]
        have : (∑ j : Fin (k + 1), (if N = (j : ℕ) then x j else 0 : α)) = 0 := by
          simp [hall_zero]
        simpa [f, hcoeff_sum] using this
      have h_card_zeros_le :
        (Finset.univ.filter (fun i : Fin m =>
          Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i = 0)).card
          ≤ f.natDegree := by
        simpa [h_eval] using
          (card_eval_zero_le_natDegree_of_injective (αs := αs) (h_inj := h_inj)
            (f := f) (hf := hf_ne))
      set Z : Finset (Fin m) :=
        Finset.univ.filter (fun i : Fin m =>
          Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i = 0) with hZ
      set U : Finset (Fin m) :=
        Finset.univ.filter (fun i : Fin m =>
          Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i ≠ 0) with hU
      have hZ_le_k : Z.card ≤ k := by
        have : Z.card ≤ f.natDegree := by simpa [Z] using h_card_zeros_le
        exact this.trans hdeg
      have h_partition :=
        (Finset.filter_card_add_filter_neg_card_eq_card
          (s := (Finset.univ : Finset (Fin m)))
          (p := fun i : Fin m =>
            Matrix.mulVec (reedSolomonMatrix (α:=α) (m:=m) (n:=k+1) αs) x i = 0))
      have hZ_U : Z.card + U.card = m := by
        simpa [Z, U, Fintype.card_fin] using h_partition
      have hU_eq : U.card = m - Z.card := by
        have : U.card + Z.card = m := by simpa [Nat.add_comm] using hZ_U
        exact Nat.eq_sub_of_add_eq this
      have h_nonzero_ge : U.card ≥ m - k := by
        have : m - k ≤ m - Z.card := Nat.sub_le_sub_left hZ_le_k m
        simpa [hU_eq] using this
      have h_arith : m - k = m - (k + 1) + 1 := by
        have h1 : m - k = Nat.succ m - Nat.succ k := by simp
        have h2 : Nat.succ m - (k + 1) = Nat.succ (m - (k + 1)) := by
          have hk1m : k + 1 ≤ m := h_mn
          simpa [Nat.succ_eq_add_one] using (Nat.succ_sub (m := m) (n := k + 1) hk1m)
        calc
          m - k = Nat.succ m - (k + 1) := by simp [Nat.succ_eq_add_one]
          _ = Nat.succ (m - (k + 1)) := h2
          _ = m - (k + 1) + 1 := rfl
      simpa [U, h_arith] using h_nonzero_ge

/-- X is q-close to subspace V if there exists Y with columns in V and X−Y has ≤ q nonzero rows. -/
@[simp] def qCloseToSubspace
  {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
  {k n : ℕ} (V : Submodule α (Fin k → α)) (q : ℕ)
  (X : Matrix (Fin k) (Fin n) α) : Prop :=
  ∃ Y : Matrix (Fin k) (Fin n) α,
    (∀ j : Fin n, (fun i => Y i j) ∈ V) ∧
    (Finset.univ.filter (fun i : Fin k => ∃ j : Fin n, X i j ≠ Y i j)).card ≤ q

/-- Subspace distance: the minimum Hamming weight among nonzero vectors in `V ≤ (Fin k → α)`. -/
@[simp] noncomputable def subspaceDistance
    {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
    {k : ℕ} (V : Submodule α (Fin k → α)) : ℕ :=
  sInf {w : ℕ | ∃ x : (Fin k → α), x ∈ V ∧ x ≠ 0 ∧
    (Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card = w}

lemma measure_preimage_finset_le_sum_singletons
  {Ω β : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (r : Ω → β) [DecidableEq β]
  (A : Finset β) :
  μ {ω | r ω ∈ A} ≤ Finset.sum A (fun i => μ {ω | r ω = i}) :=
by rw [show {ω | r ω ∈ A} = ⋃ i ∈ A, {ω | r ω = i} by ext; simp [Set.mem_iUnion]]; exact measure_biUnion_finset_le A _

lemma sparsity_check
    {α : Type*} [DecidableEq α] [Zero α]
    {k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin k)
    (h_unif : ∀ i : Fin k, μ {ω | r ω = i} = (1 : ENNReal) / (k : ENNReal))
    (x : Fin k → α) (q : ℕ) :
    μ {ω | x (r ω) = 0 ∧ ¬ ((Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q)}
      ≤ ENNReal.ofReal (1 - ((q + 1 : ℝ) / (k : ℝ))) :=
by
  by_cases hk : k = 0
  · subst hk; simp
  set S := Finset.univ.filter (fun i : Fin k => x i ≠ 0)
  set Z := Finset.univ.filter (fun i : Fin k => x i = 0)
  by_cases hSle : S.card ≤ q
  · simp [S, hSle]
  have hZ_le : Z.card ≤ k - (q + 1) := by
    simpa [Z, S, Fintype.card_fin, not_not] using
      (ZkLinalg.filter_card_le_of_compl_card_ge
        (α := Fin k) (p := fun i : Fin k => x i = 0) (d := q + 1)
        (by simpa [S] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hSle)))
  refine (measure_mono (by intro _ h; exact h.1)).trans ?_
  calc
    μ {ω | x (r ω) = 0}
        ≤ Z.card • ((1 : ENNReal) / (k : ENNReal)) := by
          simpa [Z, h_unif, Finset.sum_const] using
            measure_preimage_finset_le_sum_singletons μ r Z
    _ ≤ (k - (q + 1)) • ((1 : ENNReal) / (k : ENNReal)) := by gcongr
    _ = ((k - (q + 1) : ENNReal) / (k : ENNReal)) := by simp [nsmul_eq_mul, div_eq_mul_inv]
    _ = ENNReal.ofReal (((k - (q + 1) : ℝ) / (k : ℝ))) := by
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      simpa [ENNReal.ofReal_natCast] using
        (ENNReal.ofReal_div_of_pos (x := ((k - (q + 1)) : ℝ)) (y := (k : ℝ)) hkpos).symm
    _ = ENNReal.ofReal (1 - ((q + 1 : ℝ) / (k : ℝ))) := by
      have : 1 - ((q + 1 : ℝ) / (k : ℝ)) = ((k : ℝ) - (q + 1 : ℝ)) / (k : ℝ) := by
        simpa using (one_sub_div (K := ℝ) (a := (q + 1 : ℝ)) (b := (k : ℝ))
          (by
            have : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
            exact ne_of_gt this))
      simp [this]

lemma matrix_sparsity_check
    {α : Type*} [CommSemiring α] [DecidableEq α] [Zero α]
    {m n k : ℕ}
    (G : Matrix (Fin m) (Fin n) α) {d : ℕ}
    (hG : codeHasDistanceAtLeast G d)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin m)
    (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
    (q : ℕ)
    (X : Matrix (Fin k) (Fin n) α) :
    μ {ω |
        ((Finset.univ.filter (fun i : Fin k =>
            Matrix.mulVec X (fun j => G (r ω) j) i ≠ 0)).card ≤ q)
        ∧
        ¬ ((Finset.univ.filter (fun i : Fin k => ∃ j : Fin n, X i j ≠ 0)).card ≤ q)
      }
      ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) :=
by
  set S := Finset.univ.filter fun i => ∃ j, X i j ≠ 0; by_cases hSle : S.card ≤ q; simp [hSle]
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt (Nat.lt_of_not_ge hSle)); set y := fun ω => X.mulVec fun j => G (r ω) j
  have hE : {ω | (Finset.univ.filter fun i => y ω i ≠ 0).card ≤ q ∧ ¬S.card ≤ q} ⊆ ⋃ i ∈ T, {ω | y ω i = 0} := fun ω ⟨hF, _⟩ => by by_contra hn; simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hn; exact (hTcard ▸ (Finset.card_le_card fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn i hi⟩).trans hF).not_gt (Nat.lt_succ_self _)
  calc μ _ ≤ ∑ i ∈ T, μ {ω | y ω i = 0} := (measure_mono hE).trans (measure_biUnion_finset_le T _)
    _ ≤ ∑ _ ∈ T, ENNReal.ofReal (1 - (d : ℝ) / m) := Finset.sum_le_sum fun i hi => by obtain ⟨j0, hj0⟩ := (Finset.mem_filter.mp (hTsub hi)).2; have hx : (fun j => X i j) ≠ 0 := fun h => hj0 (congrFun h j0); simpa [Matrix.mulVec, dotProduct, mul_comm, y] using (show μ {ω | G.mulVec (fun j => X i j) (r ω) = 0} ≤ _ by simpa [hx] using zero_check G hG μ r h_unif (fun j => X i j))
    _ = _ := by rw [Finset.sum_const, hTcard, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]; norm_cast

lemma polynomial_zero_check
    {α : Type*} [Field α] [Fintype α] [DecidableEq α]
    {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → α)
    (h_unif : ∀ a : α, μ {ω | r ω = a} = (1 : ENNReal) / (Fintype.card α : ENNReal))
    (f : Polynomial α)
    (hdeg : f.natDegree ≤ n - 1) :
    μ {ω | Polynomial.eval (r ω) f = 0 ∧ ¬ (f = 0)}
      ≤ ENNReal.ofReal ((n - 1 : ℝ) / (Fintype.card α : ℝ)) :=
by
  by_cases hf : f = 0
  · simp [hf]
  set S := f.roots.toFinset
  have hμ_le : μ {ω | Polynomial.eval (r ω) f = 0} ≤ ((n - 1 : ℕ) : ENNReal) / Fintype.card α := by
    have hScard_le : S.card ≤ n - 1 :=
      (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' f).trans hdeg)
    have hsub : {ω | Polynomial.eval (r ω) f = 0} ⊆ ⋃ a ∈ S, {ω | r ω = a} :=
      fun ω hω => Set.mem_iUnion.mpr ⟨r ω, Set.mem_iUnion.mpr ⟨by simpa [S, Polynomial.mem_roots hf] using hω, by simp⟩⟩
    calc μ {ω | Polynomial.eval (r ω) f = 0}
        ≤ ∑ a ∈ S, μ {ω | r ω = a} :=
          (measure_mono hsub).trans (by simpa using MeasureTheory.measure_biUnion_finset_le S fun a => {ω | r ω = a})
      _ = S.card • ((1 : ENNReal) / Fintype.card α) := by simp [h_unif, Finset.sum_const]
      _ ≤ ((n - 1 : ℕ) : ENNReal) / Fintype.card α := by
        simpa [nsmul_eq_mul, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (by exact_mod_cast hScard_le : (S.card : ENNReal) ≤ (n - 1)) bot_le
  have hpos : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary α⟩)
  have : μ {ω | Polynomial.eval (r ω) f = 0 ∧ ¬ f = 0} ≤ μ {ω | Polynomial.eval (r ω) f = 0} :=
    measure_mono fun ω h => h.1
  simpa [hf, ENNReal.ofReal_div_of_pos hpos] using this.trans hμ_le

/-- For `s ≤ z, s ≤ k`, the ratio of binomial coefficients equals the ratio of descending factorials (over `ℝ`). -/
lemma choose_ratio_eq_descFactorial_ratio_real
  {z k s : ℕ} :
  ((Nat.choose z s : ℝ) / (Nat.choose k s : ℝ))
    = ((z.descFactorial s : ℝ) / (k.descFactorial s : ℝ)) :=
by
  simpa [mul_comm,
    congrArg (fun n : ℕ => (n : ℝ)) (Nat.descFactorial_eq_factorial_mul_choose z s),
    congrArg (fun n : ℕ => (n : ℝ)) (Nat.descFactorial_eq_factorial_mul_choose k s)] using
      (mul_div_mul_right
        (a := (Nat.choose z s : ℝ))
        (b := (Nat.choose k s : ℝ))
        (c := (Nat.factorial s : ℝ))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))).symm

/-- Falling-factorial ratio bound by a power: assuming `s ≤ z ≤ k` and `k > 0`, the ratio
`z↓s / k↓s` is at most `(z/k)^s` over the reals. -/
lemma descFactorial_ratio_le_pow_div_real
  {z k s : ℕ} (hz : z ≤ k) (hsz : s ≤ z) (hkpos : 0 < k) :
  ((z.descFactorial s : ℝ) / (k.descFactorial s : ℝ))
    ≤ ((z : ℝ) / (k : ℝ)) ^ s :=
by
  induction' s with s ih generalizing z k
  · simp
  · have hsk : s < k := Nat.succ_le.1 (hsz.trans hz)
    have hkposR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have h1 :
        (((z - s : ℕ) : ℝ) / ((k - s : ℕ) : ℝ)) ≤ (z : ℝ) / (k : ℝ) := by
      have hkz : (z : ℝ) ≤ (k : ℝ) := by exact_mod_cast hz
      have hs0 : 0 ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le s
      have hcross :
          ((z : ℝ) - s) * (k : ℝ) ≤ (z : ℝ) * ((k : ℝ) - s) := by
        have h' := add_le_add_left (neg_le_neg (mul_le_mul_of_nonneg_left hkz hs0)) ((z : ℝ) * (k : ℝ))
        calc
          ((z : ℝ) - s) * (k : ℝ)
              = (z : ℝ) * (k : ℝ) - (s : ℝ) * (k : ℝ) := by ring
          _ ≤ (z : ℝ) * (k : ℝ) - (s : ℝ) * (z : ℝ) := by
            simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h'
          _ = (z : ℝ) * ((k : ℝ) - s) := by ring
      have hx :
          ((z : ℝ) - s) ≤ ((z : ℝ) * ((k : ℝ) - s)) / (k : ℝ) :=
        (le_div_iff₀ hkposR).2 hcross
      have hkms_pos : 0 < ((k : ℝ) - s) := by
        have : 0 < ((k - s : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hsk
        simpa [Nat.cast_sub (Nat.le_of_lt hsk)] using this
      have hdiv : ((z : ℝ) - s) / ((k : ℝ) - s) ≤ (z : ℝ) / (k : ℝ) :=
        (div_le_iff₀ hkms_pos).2 <|
          by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hx
      simpa [Nat.cast_sub ((Nat.le_succ s).trans hsz), Nat.cast_sub (Nat.le_of_lt hsk)] using hdiv
    have hmul :
        ((((z - s : ℕ) : ℝ) / ((k - s : ℕ) : ℝ)) *
            ((z.descFactorial s : ℝ) / (k.descFactorial s : ℝ)))
          ≤ ((z : ℝ) / (k : ℝ)) * (((z : ℝ) / (k : ℝ)) ^ s) :=
      mul_le_mul h1 (ih hz ((Nat.le_succ s).trans hsz) hkpos)
        (by
          exact div_nonneg
            (by exact_mod_cast (Nat.zero_le (z.descFactorial s)))
            (by exact_mod_cast (Nat.zero_le (k.descFactorial s))))
        (div_nonneg (by exact_mod_cast Nat.zero_le z) (le_of_lt hkposR))
    have hsucc :
        ((z.descFactorial (Nat.succ s) : ℝ) / (k.descFactorial (Nat.succ s) : ℝ))
          ≤ ((z : ℝ) / (k : ℝ)) ^ s * ((z : ℝ) / (k : ℝ)) := by
      simpa [Nat.descFactorial_succ, mul_div_mul_comm, mul_comm, mul_left_comm, mul_assoc] using
        hmul
    simpa [pow_succ, mul_comm] using hsucc

lemma binomial_ratio_le_pow_real
    {z k s : ℕ} (hz : z ≤ k) :
    ((Nat.choose z s : ℝ) / (Nat.choose k s : ℝ))
      ≤ (z : ℝ) ^ s / (k : ℝ) ^ s :=
by
  rcases em (s = 0) with rfl | hs0
  · simp
  by_cases hsz : s ≤ z
  · have hkpos : 0 < k := lt_of_lt_of_le (Nat.pos_of_ne_zero hs0) (hsz.trans hz)
    simpa [ZkLinalg.choose_ratio_eq_descFactorial_ratio_real, div_pow] using
      ZkLinalg.descFactorial_ratio_le_pow_div_real hz hsz hkpos
  · have hnum0 : (Nat.choose z s : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (lt_of_not_ge hsz)
    have : 0 ≤ (z : ℝ) ^ s / (k : ℝ) ^ s :=
      div_nonneg (pow_nonneg (by exact_mod_cast Nat.zero_le z) _)
                 (pow_nonneg (by exact_mod_cast Nat.zero_le k) _)
    simpa [hnum0] using this

lemma mask_zero_uniform_subset_bound
    {α : Type*} [DecidableEq α] [Zero α]
    {k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → Finset (Fin k)) (s : ℕ)
    (h_card : ∀ ω, (S ω).card = s)
    (h_unif_S :
      ∀ A : Finset (Fin k), A.card = s →
        μ {ω | S ω = A} =
          (1 : ENNReal) / ((Nat.choose k s : ℕ) : ENNReal))
    (x : Fin k → α) (q : ℕ) :
    μ {ω |
        (∀ i ∈ S ω, x i = 0) ∧
        ¬ ((Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q)}
      ≤ ENNReal.ofReal ((1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s) :=
by
  set Sx := Finset.univ.filter fun i : Fin k => x i ≠ 0
  set E : Set Ω := {ω | (∀ i ∈ S ω, x i = 0) ∧ ¬ Sx.card ≤ q}
  by_cases hsmall : Sx.card ≤ q; · simp [E, Sx, hsmall]
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt (Nat.lt_of_not_ge hsmall))
  set U := Finset.univ \ T; set c := (1 : ENNReal) / Nat.choose k s
  have hsubset : E ⊆ ⋃ A ∈ U.powersetCard s, {ω | S ω = A} := fun ω hω =>
    Set.mem_iUnion.2 ⟨S ω, Set.mem_iUnion.2 ⟨Finset.mem_powersetCard.2 ⟨fun i hiS =>
      Finset.mem_sdiff.2 ⟨by simp, fun hiT => (Finset.mem_filter.mp (hTsub hiT)).2 (hω.1 i hiS)⟩, h_card ω⟩, by simp⟩⟩
  have hμ_E_le_sum := (measure_mono hsubset).trans (MeasureTheory.measure_biUnion_finset_le (μ := μ) _ _)
  have hUcard : U.card = k - (q + 1) := by
    simp only [U]
    convert_to (Finset.univ \ T).card = k - (q + 1)
    simp [Finset.card_sdiff, hTcard, Fintype.card_fin]
  have hμ_E_le_ratio : μ E ≤ (Nat.choose (k - (q + 1)) s : ENNReal) / Nat.choose k s := by
    simpa [hUcard, c, nsmul_eq_mul, div_eq_mul_inv] using hμ_E_le_sum.trans (le_of_eq ((Finset.sum_congr rfl fun A hA => by simpa [c] using h_unif_S A (Finset.mem_powersetCard.1 hA).2).trans (Finset.sum_const c)))
  by_cases hden0 : Nat.choose k s = 0
  · exact (by simpa [Finset.card_eq_zero.1 (by simpa using Nat.choose_eq_zero_of_lt ((by simpa using Finset.card_le_univ U : U.card ≤ k).trans_lt (by by_contra hnk; exact ne_of_gt (Nat.choose_pos (le_of_not_gt hnk)) hden0)) : (U.powersetCard s).card = 0)] using hμ_E_le_sum : μ E ≤ 0).trans (by simp)
  by_cases hle : q + 1 ≤ k
  · have hkpos : 0 < k := lt_of_lt_of_le Nat.succ_pos' hle
    have hpow_eq : ENNReal.ofReal (((k - (q + 1) : ℕ) : ℝ) ^ s / (k : ℝ) ^ s) = ENNReal.ofReal ((1 - (q + 1 : ℝ) / k) ^ s) := by
      simp [div_pow, one_sub_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0), Nat.cast_sub hle]
    simpa [E] using hμ_E_le_ratio.trans ((by rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hden0)]; simp : ((Nat.choose (k - (q + 1)) s : ℕ) : ENNReal) / Nat.choose k s = ENNReal.ofReal ((Nat.choose (k - (q + 1)) s : ℝ) / Nat.choose k s)) ▸ (ENNReal.ofReal_le_ofReal (binomial_ratio_le_pow_real (Nat.sub_le _ _))).trans (hpow_eq ▸ le_rfl))
  · by_cases hs0 : s = 0; · simpa [hs0] using (measure_mono fun _ _ => trivial : μ E ≤ μ Set.univ)
    have hnum : Nat.choose (k - (q + 1)) s = 0 := by cases s with | zero => exact (hs0 rfl).elim | succ => simp [Nat.sub_eq_zero_of_le (lt_of_not_ge hle).le]
    exact (by simpa [hnum] using hμ_E_le_ratio : μ E ≤ 0).trans (by simp)

/-- Masking by a finset: the masked vector is zero iff all masked coordinates are zero. -/
lemma mask_eq_zero_iff_forall_mem
  {α ι : Type*} [Zero α] [DecidableEq ι]
  (x : ι → α) (A : Finset ι) :
  (fun i => if i ∈ A then x i else 0) = (0 : ι → α) ↔ ∀ i ∈ A, x i = 0 :=
by
  constructor
  · intro h i hi; simpa [hi] using congrArg (fun f => f i) h
  · intro h; funext i; by_cases hi : i ∈ A
    · simp [hi, h i hi]
    · simp [hi]

lemma sparsity_zero_composition
    {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
    {m k : ℕ}
    (G : Matrix (Fin m) (Fin k) α) {d : ℕ}
    (hG : codeHasDistanceAtLeast G d)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Fin m)
    (h_unif_r : ∀ i : Fin m,
      μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
    (S : Ω → Finset (Fin k)) (s : ℕ)
    (h_card : ∀ ω, (S ω).card = s)
    (h_unif_S :
      ∀ A : Finset (Fin k), A.card = s →
        μ {ω | S ω = A} =
          (1 : ENNReal) / ((Nat.choose k s : ℕ) : ENNReal))
    (h_indep :
      ∀ i A,
        μ {ω | r ω = i ∧ S ω = A}
          = μ {ω | r ω = i} * μ {ω | S ω = A})
    (x : Fin k → α) (q : ℕ) :
    μ {ω |
        (Matrix.mulVec G (fun i => if i ∈ S ω then x i else 0) (r ω) = 0)
        ∧ ¬ ((Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q)}
      ≤ ENNReal.ofReal
          ((1 - (d : ℝ) / (m : ℝ)) +
           (1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s) :=
by
  set y : Ω → (Fin k → α) := fun ω i => if i ∈ S ω then x i else 0
  set E : Set Ω := {ω |
      (Matrix.mulVec G (y ω) (r ω) = 0)
      ∧ ¬ ((Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q)}
  by_cases hqk : q + 1 ≤ k
  · by_cases hx_le : (Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q
    · have hμE : μ E = 0 := by simp [E, hx_le]
      simp [hμE]
    · have hx_ne : x ≠ 0 := by intro hx0; exact hx_le (by simp [hx0])
      have hdx_le_m : d ≤ m := by
        have h_ge := hG x hx_ne
        have h_le :=
          Finset.card_filter_le (Finset.univ : Finset (Fin m))
            (fun i : Fin m => Matrix.mulVec G x i ≠ 0)
        simpa [Fintype.card_fin] using h_ge.trans h_le
      set E1 : Set Ω := {ω | Matrix.mulVec G (y ω) (r ω) = 0 ∧ y ω ≠ 0}
      set E2 : Set Ω := {ω | y ω = 0 ∧ ¬ ((Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q)}
      have hμ_E_le : μ E ≤ μ E1 + μ E2 := by
        refine (measure_mono ?_).trans (by simpa using measure_union_le E1 E2)
        intro ω hω; rcases hω with ⟨hz, hnot⟩; by_cases hy : y ω = 0
        · exact Or.inr ⟨hy, hnot⟩
        · exact Or.inl ⟨hz, hy⟩
      have hE2_le : μ E2 ≤ ENNReal.ofReal ((1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s) := by
        simpa [E2, y, ZkLinalg.mask_eq_zero_iff_forall_mem] using
          (mask_zero_uniform_subset_bound (μ := μ) (S := S) (s := s)
            (h_card := h_card) (h_unif_S := h_unif_S) (x := x) (q := q))
      set As : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powersetCard s
      set yA : Finset (Fin k) → (Fin k → α) := fun A i => if i ∈ A then x i else 0
      set Zset : Finset (Fin k) → Finset (Fin m) := fun A =>
        (Finset.univ.filter (fun j : Fin m => Matrix.mulVec G (yA A) j = 0))
      set AsNZ : Finset (Finset (Fin k)) := As.filter (fun A => yA A ≠ 0)
      have E1_subset :
          {ω | Matrix.mulVec G (y ω) (r ω) = 0 ∧ y ω ≠ 0}
            ⊆ ⋃ A ∈ AsNZ, {ω | S ω = A ∧ r ω ∈ Zset A} := by
        intro ω hω
        have hA_mem_As : S ω ∈ As := by
          refine (Finset.mem_powersetCard.2 ?_)
          exact ⟨by intro i hi; simp, h_card ω⟩
        have hy_eq : y ω = yA (S ω) := by funext i; simp [y, yA]
        have hA_mem_AsNZ : S ω ∈ AsNZ := by
          refine Finset.mem_filter.mpr ?_;
          exact ⟨hA_mem_As, by simpa [hy_eq] using hω.2⟩
        have hrZ : r ω ∈ Zset (S ω) := by
          have : Matrix.mulVec G (yA (S ω)) (r ω) = 0 := by simpa [hy_eq] using hω.1
          simpa [Zset] using this
        refine Set.mem_iUnion.2 ?_;
        refine ⟨S ω, ?_⟩; refine Set.mem_iUnion.2 ?_;
        exact ⟨hA_mem_AsNZ, by simpa⟩
      have hμ_union : μ {ω | Matrix.mulVec G (y ω) (r ω) = 0 ∧ y ω ≠ 0}
          ≤ ∑ A ∈ AsNZ, μ {ω | S ω = A ∧ r ω ∈ Zset A} :=
        (measure_mono E1_subset).trans (by
          simpa using MeasureTheory.measure_biUnion_finset_le (μ := μ) AsNZ (fun A => {ω | S ω = A ∧ r ω ∈ Zset A}))
      have h_indep' : ∀ (A : Finset (Fin k)) (j : Fin m),
          μ {ω | S ω = A ∧ r ω = j}
            = μ {ω | S ω = A} * μ {ω | r ω = j} := by
        intro A j; simpa [and_comm, mul_comm] using h_indep j A
      have h_indep_bound : ∀ {A : Finset (Fin k)}, A ∈ AsNZ →
          μ {ω | S ω = A ∧ r ω ∈ Zset A}
            ≤ μ {ω | S ω = A} * ∑ j ∈ Zset A, μ {ω | r ω = j} := by
        intro A hA; simpa using
          (ZkLinalg.measure_inter_preimage_finset_le_mul_sum (μ := μ)
            (r := S) (r' := r) (h_indep := h_indep') (i := A) (A := Zset A))
      have hsum_r_const : ∀ A : Finset (Fin k),
          (∑ j ∈ Zset A, μ {ω | r ω = j})
            = (Zset A).card • ((1 : ENNReal) / (m : ENNReal)) := by
        intro A; simp [Finset.sum_congr rfl fun j hj => h_unif_r j, Finset.sum_const]
      have hZ_le : ∀ {A : Finset (Fin k)}, A ∈ AsNZ → (Zset A).card ≤ m - d := by
        intro A hA
        have hy_ne : yA A ≠ 0 := (Finset.mem_filter.mp hA).2
        simpa [Zset] using
          (ZkLinalg.zero_positions_card_le_of_distance (G' := G) (hG' := hG)
            (y := yA A) (hy := hy_ne))
      have hμ_union_le : μ {ω | Matrix.mulVec G (y ω) (r ω) = 0 ∧ y ω ≠ 0}
          ≤ ∑ A ∈ AsNZ,
              μ {ω | S ω = A} *
                (((m - d : ℕ) : ENNReal) * ((1 : ENNReal) / (m : ENNReal))) := by
        refine hμ_union.trans ?_
        refine Finset.sum_le_sum (by
          intro A hA
          have h1 := h_indep_bound (A := A) hA
          have hsum := hsum_r_const A
          have hsum_le :
              (∑ j ∈ Zset A, μ {ω | r ω = j})
                ≤ ((m - d : ℕ) : ENNReal) *
                    ((1 : ENNReal) / (m : ENNReal)) := by
            have : ((Zset A).card : ENNReal) ≤ ((m - d : ℕ) : ENNReal) := by exact_mod_cast hZ_le hA
            simpa [hsum, nsmul_eq_mul] using mul_le_mul' this le_rfl
          exact (le_trans h1 (mul_le_mul_left' hsum_le _)))
      let C : ENNReal := (((m - d : ℕ) : ENNReal) * ((1 : ENNReal) / (m : ENNReal)))
      have h1 : μ E1 ≤ ∑ A ∈ AsNZ, μ {ω | S ω = A} * C := by simpa [E1, C] using hμ_union_le
      have h2 : (∑ A ∈ AsNZ, μ {ω | S ω = A} * C) = C * (∑ A ∈ AsNZ, μ {ω | S ω = A}) := by
        simpa [C, mul_comm, mul_left_comm, mul_assoc] using
          (Finset.sum_mul (s := AsNZ) (f := fun A : Finset (Fin k) => μ {ω | S ω = A}) (a := C)).symm
      have hsum_AsNZ_le_As :
          (∑ A ∈ AsNZ, μ {ω | S ω = A}) ≤ (∑ A ∈ As, μ {ω | S ω = A}) := by
        have hrepr :
            (∑ A ∈ AsNZ, μ {ω | S ω = A})
              = ∑ A ∈ As, (if yA A = 0 then 0 else μ {ω | S ω = A}) := by
          simp [AsNZ, Finset.sum_filter, ite_not]
        have hpoint : ∀ A ∈ As,
            (if yA A = 0 then 0 else μ {ω | S ω = A}) ≤ μ {ω | S ω = A} := by
          intro A hA; by_cases h : yA A = 0 <;> simp [h]
        simpa [hrepr] using
          (Finset.sum_le_sum fun A hA => hpoint A hA)
      have h_unif_const : ∀ A ∈ As,
          μ {ω | S ω = A} = (1 : ENNReal) / ((Nat.choose k s : ℕ) : ENNReal) := by
        intro A hA; simpa using h_unif_S A ((Finset.mem_powersetCard.1 hA).2)
      have hsum_As :
          (∑ A ∈ As, μ {ω | S ω = A})
            = As.card • ((1 : ENNReal) / ((Nat.choose k s : ℕ) : ENNReal)) := by
        simp [Finset.sum_congr rfl fun A hA => h_unif_const A hA, Finset.sum_const]
      have hAs_card : As.card = Nat.choose k s := by
        simp [As, Finset.card_univ, Fintype.card_fin]
      have hsum_As_le_one : (∑ A ∈ As, μ {ω | S ω = A}) ≤ 1 := by
        have hrepr :
            (∑ A ∈ As, μ {ω | S ω = A}) = ((Nat.choose k s : ENNReal) * ((Nat.choose k s : ENNReal))⁻¹) := by
          simp [hsum_As, hAs_card, nsmul_eq_mul, div_eq_mul_inv]
        by_cases hc0 : Nat.choose k s = 0
        · have : (∑ A ∈ As, μ {ω | S ω = A}) = 0 := by simp [hrepr, hc0]
          simp [this]
        · have hpos : ((Nat.choose k s : ℕ) : ENNReal) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Nat.pos_of_ne_zero hc0))
          have hTop : ((Nat.choose k s : ℕ) : ENNReal) ≠ (⊤ : ENNReal) := by simp
          have hmul : ((Nat.choose k s : ENNReal) * ((Nat.choose k s : ENNReal))⁻¹) = 1 :=
            ENNReal.mul_inv_cancel hpos hTop
          simp [hrepr, hmul]
      have hsum_AsNZ_le_one : (∑ A ∈ AsNZ, μ {ω | S ω = A}) ≤ 1 := hsum_AsNZ_le_As.trans hsum_As_le_one
      have hE1_div : μ E1 ≤ (((m - d : ℕ) : ENNReal) / (m : ENNReal)) := by
        have h3 : μ E1 ≤ C * (∑ A ∈ AsNZ, μ {ω | S ω = A}) := by simpa [h2] using h1
        have h4 : μ E1 ≤ C * 1 := h3.trans (mul_le_mul_left' hsum_AsNZ_le_one _)
        simpa [E1, C, div_eq_mul_inv, one_mul] using h4
      have hE1_le : μ E1 ≤ ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) := by
        by_cases hm0 : m = 0
        · have hof : ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) = 1 := by
            have : (m : ℝ) = 0 := by simpa using congrArg (fun n : ℕ => (n : ℝ)) hm0
            simp [this]
          have hμ_le_one : μ E1 ≤ 1 := by
            have : E1 ⊆ (Set.univ : Set Ω) := by intro ω _; trivial
            simpa [E1] using (measure_mono this : μ E1 ≤ μ (Set.univ : Set Ω))
          exact hμ_le_one.trans (by simp [hof])
        · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
          have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
          have h_cast_add : (((m - d : ℕ) : ℝ) + (d : ℝ)) = (m : ℝ) := by
            simpa [Nat.cast_add] using congrArg (fun t : ℕ => (t : ℝ)) (Nat.sub_add_cancel hdx_le_m)
          have h_cast_sub : ((m - d : ℕ) : ℝ) = (m : ℝ) - (d : ℝ) :=
            (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h_cast_add)
          have h_ofReal_eq_div :
              ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ))
                = ((m - d : ℕ) : ENNReal) / (m : ENNReal) := by
            have h1 : ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ))
                = ENNReal.ofReal (((m - d : ℕ) : ℝ) / (m : ℝ)) := by
              simp [one_sub_div (K := ℝ) (a := (d : ℝ)) (b := (m : ℝ)) hm_ne, h_cast_sub]
            have h2 : ENNReal.ofReal (((m - d : ℕ) : ℝ) / (m : ℝ))
                = ENNReal.ofReal ((m - d : ℕ) : ℝ) / (m : ENNReal) := by
              simpa using ENNReal.ofReal_div_of_pos (x := ((m - d : ℕ) : ℝ)) (y := (m : ℝ)) hm_pos
            have h3 : ENNReal.ofReal ((m - d : ℕ) : ℝ) = ((m - d : ℕ) : ENNReal) := by simp
            simp [h1, h2, h3]
          exact hE1_div.trans (by simp [h_ofReal_eq_div])
      have hfinal' :
          μ E ≤ ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) + ENNReal.ofReal ((1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s) :=
        hμ_E_le.trans (add_le_add hE1_le hE2_le)
      have hnonneg1 : 0 ≤ 1 - (d : ℝ) / (m : ℝ) := by
        by_cases hm0 : m = 0
        · simp [hm0]
        · have : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdx_le_m
          have hm0' : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
          have : (d : ℝ) / (m : ℝ) ≤ 1 := by
            simpa using (div_le_one_of_le₀ (a := (d : ℝ)) (b := (m : ℝ)) this hm0')
          exact sub_nonneg.mpr this
      have hnonneg2 : 0 ≤ (1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s := by
        have : (q + 1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hqk
        have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
        have : (q + 1 : ℝ) / (k : ℝ) ≤ 1 := by
          simpa using (div_le_one_of_le₀ (a := (q + 1 : ℝ)) (b := (k : ℝ)) this hk0)
        exact pow_nonneg (sub_nonneg.mpr this) _
      have hsum_ofReal :
          ENNReal.ofReal (1 - (d : ℝ) / (m : ℝ)) + ENNReal.ofReal ((1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s)
            = ENNReal.ofReal ((1 - (d : ℝ) / (m : ℝ)) + (1 - ((q + 1 : ℝ) / (k : ℝ))) ^ s) := by
        simp [ENNReal.ofReal_add, hnonneg1, hnonneg2]
      simpa [E, hsum_ofReal] using hfinal'
  · have hk_le_q : k ≤ q := Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hqk)
    have h_support_le_q :
        (Finset.univ.filter (fun i : Fin k => x i ≠ 0)).card ≤ q :=
      (le_trans
        (by
          simpa [Fintype.card_fin] using
            (Finset.card_le_univ (Finset.univ.filter (fun i : Fin k => x i ≠ 0))))
        hk_le_q)
    have hμE : μ E = 0 := by simp [E, h_support_le_q]
    simp [hμE]

lemma kronecker_product_distance
  {α : Type*} [CommSemiring α] [DecidableEq α] [Zero α]
  {m n k m' : ℕ}
  (G : Matrix (Fin m) (Fin n) α) {d : ℕ} (hG : codeHasDistanceAtLeast G d)
  (G' : Matrix (Fin m') (Fin k) α) {d' : ℕ} (hG' : codeHasDistanceAtLeast G' d') :
  ∀ X : Matrix (Fin k) (Fin n) α, X ≠ 0 →
    (Finset.univ.filter (fun ij : (Fin m') × (Fin m) =>
      (Finset.univ.sum (fun j : Fin k => G' ij.1 j * (Matrix.mulVec X (fun t => G ij.2 t) j)) ≠ 0))).card ≥ d * d' :=
by
  intro X hXne
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hXne
  set S0 := Finset.univ.filter fun i => Matrix.mulVec G (fun j => X i0 j) i ≠ 0
  set yrow := fun i => Matrix.mulVec X fun t => G i t
  set T := fun i => Finset.univ.filter fun i' => Matrix.mulVec G' (yrow i) i' ≠ 0
  have hy i (hi : i ∈ S0) : yrow i ≠ 0 := fun h =>
    (Finset.mem_filter.1 hi).2 <| by simpa [yrow, Matrix.mulVec, dotProduct, mul_comm] using congrArg (· i0) h
  calc d * d' ≤ ∑ i ∈ S0, d' := by simp [Finset.sum_const]; exact Nat.mul_le_mul_right d' (by simpa using hG _ hi0)
      _ ≤ ∑ i ∈ S0, (T i).card := Finset.sum_le_sum fun i hi => by simpa using hG' _ (hy i hi)
      _ = ((S0.sigma T).map ⟨fun s => (s.2, s.1), fun a b h => by cases a; cases b; cases h; rfl⟩).card := by simp
      _ ≤ _ := Finset.card_le_card fun _ hp => by
        rcases Finset.mem_map.1 hp with ⟨⟨i, i'⟩, hi, rfl⟩
        simpa [yrow, Matrix.mulVec, dotProduct] using (Finset.mem_filter.1 (Finset.mem_sigma.1 hi).2).2


lemma kronecker_product_bound
  {α : Type*} [CommSemiring α] [DecidableEq α] [Zero α]
  {m n k m' : ℕ}
  (G : Matrix (Fin m) (Fin n) α) {d : ℕ} (hG : codeHasDistanceAtLeast G d)
  (G' : Matrix (Fin m') (Fin k) α) {d' : ℕ} (hG' : codeHasDistanceAtLeast G' d')
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
  (r : Ω → Fin m)
  (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
  (r' : Ω → Fin m')
  (h_unif' : ∀ i : Fin m', μ {ω | r' ω = i} = (1 : ENNReal) / (m' : ENNReal))
  (h_indep : ∀ i : Fin m, ∀ j : Fin m',
    μ {ω | r ω = i ∧ r' ω = j} = μ {ω | r ω = i} * μ {ω | r' ω = j})
  (X : Matrix (Fin k) (Fin n) α) :
  μ {ω |
      ((Finset.univ.sum (fun j : Fin k => G' (r' ω) j * (Matrix.mulVec X (fun t => G (r ω) t) j)) = 0)
        ∧ ¬ (X = 0))}
    ≤ ENNReal.ofReal (1 - ((d * d') : ℝ) / ((m * m') : ℝ)) :=
by
  haveI := hμ
  set S : (Fin m' × Fin m) → α :=
    fun ij => ∑ j : Fin k, G' ij.1 j * Matrix.mulVec X (fun t => G ij.2 t) j
  set s : Finset (Fin m' × Fin m) := Finset.univ.filter (fun ij => S ij = 0)
  have hs : ∀ ij, ij ∈ s ↔ S ij = 0 := by intro ij; simp [s]
  set c : ENNReal := ((1 : ENNReal) / (m : ENNReal)) * ((1 : ENNReal) / (m' : ENNReal))
  have h_atom_const : ∀ ij, μ {ω | (r' ω, r ω) = ij} = c := by
    rintro ⟨i', i⟩
    have : {ω | (r' ω, r ω) = (i', i)} = {ω | r' ω = i' ∧ r ω = i} := by
      ext ω; constructor
      · intro h; simpa [Prod.ext_iff] using h
      · intro h; rcases h with ⟨hr', hr⟩; simp [hr', hr]
    simpa [this, and_comm, c, h_unif i, h_unif' i'] using h_indep i i'
  have hsum : (∑ ij ∈ s, μ {ω | (r' ω, r ω) = ij}) = s.card • c := by
    simp [h_atom_const, Finset.sum_const]
  by_cases hX : X = 0
  · simp [hX]
  have h_main :
      μ {ω |
          ((∑ j : Fin k, G' (r' ω) j * Matrix.mulVec X (fun t => G (r ω) t) j) = 0) ∧ X ≠ 0}
        ≤ s.card • c := by
    refine (measure_mono (by intro ω hω; exact hω.1)).trans ?_
    have : μ {ω | S (r' ω, r ω) = 0}
        ≤ ∑ ij ∈ s, μ {ω | (r' ω, r ω) = ij} := by
      simpa [show {ω | S (r' ω, r ω) = 0} = ⋃ ij ∈ s, {ω | (r' ω, r ω) = ij} from by ext; simp [hs]] using
        (MeasureTheory.measure_biUnion_finset_le (μ := μ) s (fun ij => {ω | (r' ω, r ω) = ij}))
    exact this.trans (by simp [hsum])
  have hpos :
      (Finset.univ.filter
          (fun ij : Fin m' × Fin m =>
            (∑ j : Fin k, G' ij.1 j * Matrix.mulVec X (fun t => G ij.2 t) j) ≠ 0)).card
        ≥ d * d' := by
    simpa [S] using
      (kronecker_product_distance (G := G) (d := d) (hG := hG)
        (G' := G') (d' := d') (hG' := hG') X hX)
  have h_s_le : s.card ≤ Fintype.card (Fin m' × Fin m) - d * d' := by
    simpa [s] using
      ZkLinalg.filter_card_le_of_compl_card_ge
        (α := Fin m' × Fin m) (p := fun ij => S ij = 0)
        (d := d * d') (by simpa using hpos)
  have h_card_pairs : Fintype.card (Fin m' × Fin m) = m' * m := by
    simp [Fintype.card_fin, Nat.mul_comm]
  have h_s_le' : s.card ≤ m * m' - d * d' := by
    simpa [h_card_pairs, Nat.mul_comm] using h_s_le
  have hμ_div :
      μ {ω |
          ((∑ j : Fin k, G' (r' ω) j * Matrix.mulVec X (fun t => G (r ω) t) j) = 0) ∧ X ≠ 0}
        ≤ ((m * m' - d * d' : ℕ) : ENNReal) / (m * m' : ENNReal) := by
    have h_nsmul : s.card • c ≤ (m * m' - d * d' : ℕ) • c := by gcongr
    have := h_main.trans h_nsmul
    simpa [c, nsmul_eq_mul, div_eq_mul_inv, ENNReal.mul_inv] using this
  by_cases hmm0 : m * m' = 0
  · have hRHS : ENNReal.ofReal (1 - ((d * d') : ℝ) / ((m * m') : ℝ)) = 1 := by
      have : ((m * m') : ℝ) = 0 := by simpa using congrArg (fun t : ℕ => (t : ℝ)) hmm0
      simp [this]
    have hμ_le_one :
        μ {ω |
            ((∑ j : Fin k, G' (r' ω) j * Matrix.mulVec X (fun t => G (r ω) t) j) = 0) ∧ X ≠ 0} ≤ 1 := by
      simpa using
        (measure_mono (by intro _ _; trivial) :
          μ {ω |
              ((∑ j : Fin k, G' (r' ω) j * Matrix.mulVec X (fun t => G (r ω) t) j) = 0) ∧ X ≠ 0}
            ≤ μ (Set.univ : Set Ω))
    exact hμ_le_one.trans (by simp [hRHS])
  ·
    have hmm_pos_nat : 0 < m * m' := Nat.pos_of_ne_zero hmm0
    have hmm_pos : 0 < ((m * m') : ℝ) := by exact_mod_cast hmm_pos_nat
    have h_ident :
        ENNReal.ofReal (1 - ((d * d') : ℝ) / ((m * m') : ℝ))
          = ((m * m' - d * d' : ℕ) : ENNReal) / (m * m' : ENNReal) := by
      simpa [Nat.cast_mul, one_sub_div (ne_of_gt hmm_pos)] using
        ENNReal.ofReal_div_of_pos hmm_pos
    simpa [h_ident] using hμ_div

lemma linear_independence_from_distance
  {α : Type*} [Field α] [DecidableEq α]
  {m n : ℕ}
  (hn : 2 ≤ n)
  (G : Matrix (Fin m) (Fin n) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  (R : Finset (Fin m)) (hR : R.card > m - d) :
  ∃ r r' : Fin m, r ≠ r' ∧ r ∈ R ∧ r' ∈ R ∧
    LinearIndependent α ![ (fun j : Fin n => G r j), (fun j : Fin n => G r' j) ] :=
by
  by_contra hneg
  have : ∃ x : Fin n → α, x ≠ 0 ∧ ∀ r ∈ R, Matrix.mulVec G x r = 0 := by
    by_cases h0 : ∀ r ∈ R, (fun j => G r j) = 0
    · have : 1 < Fintype.card (Fin n) := by simpa [Fintype.card_fin] using hn
      obtain ⟨i⟩ := Fintype.card_pos_iff.1 (Nat.lt_trans Nat.zero_lt_one this)
      exact ⟨fun _ => 1, by intro h; exact one_ne_zero (congrArg (· i) h), by intro r hr; simp [Matrix.mulVec, dotProduct, h0 r hr]⟩
    · push_neg at h0
      obtain ⟨r0, hr0R, hv0⟩ := h0
      set v := fun j => G r0 j
      have h_dep : ∀ r ∈ R, r ≠ r0 → ∃ a, (fun j => G r j) = a • v := fun r hr hneq => by
        have : ¬ LinearIndependent α ![v, fun j => G r j] := fun hLI => hneg ⟨r0, r, hneq.symm, hr0R, hr, hLI⟩
        obtain ⟨a, ha⟩ : ∃ a, a • v = fun j => G r j := by
          simpa [LinearIndependent.pair_iff', hv0, not_forall] using this
        exact ⟨a, ha.symm⟩
      obtain ⟨i0, hvi0⟩ := Function.ne_iff.1 hv0
      obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by simpa [Fintype.card_fin] using hn : 1 < _) i0
      let x := fun j => (if j = i0 then v i1 else 0) + (if j = i1 then -v i0 else 0)
      have hx_ne : x ≠ 0 := by
        intro hx; exact neg_ne_zero.2 hvi0 (by simpa [x, hi1] using congrArg (· i1) hx)
      have hdot : ∑ j, v j * x j = 0 := by
        simp only [x, mul_add, Finset.sum_add_distrib]
        have : ∑ j, v j * (if j = i0 then v i1 else 0) = v i0 * v i1 :=
          (Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp)).trans (by simp)
        have : ∑ j, v j * (if j = i1 then -v i0 else 0) = v i1 * (-v i0) :=
          (Finset.sum_eq_single i1 (fun j _ hj => by simp [hj]) (by simp)).trans (by simp)
        simp [mul_comm]
      refine ⟨x, hx_ne, ?_⟩
      intro r hr
      by_cases hrr0 : r = r0
      · subst hrr0; simp [Matrix.mulVec, dotProduct, v, hdot]
      · obtain ⟨a, ha⟩ := h_dep r hr hrr0
        have : ∑ j, G r j * x j = a * ∑ j, v j * x j := by simp [ha, Finset.mul_sum, mul_assoc]
        simp [Matrix.mulVec, dotProduct, this, hdot]
  rcases this with ⟨x, hx_ne, hxR⟩
  exact absurd ((Finset.card_mono fun r hr => by simp [hxR r hr]).trans (ZkLinalg.zero_positions_card_le_of_distance G hG x hx_ne)) hR.not_ge

lemma unique_decoding_radius
  {α : Type*} [Ring α] [DecidableEq α]
  {k n : ℕ} (V : Submodule α (Fin k → α)) (q : ℕ)
  (X : Matrix (Fin k) (Fin n) α)
  (h_dist : 2 * q < subspaceDistance V)
  (h_close : qCloseToSubspace V q X) :
  ∃! Y : Matrix (Fin k) (Fin n) α,
    (∀ j : Fin n, (fun i => Y i j) ∈ V) ∧
    (Finset.univ.filter (fun i : Fin k => ∃ j : Fin n, X i j ≠ Y i j)).card ≤ q :=
by
  obtain ⟨Y0, hY0V, hY0q⟩ := h_close; use Y0, ⟨hY0V, hY0q⟩; intro Y' ⟨hY'V, hY'q⟩; ext i j; by_contra hneq
  set Sd := Finset.univ.filter fun t => Y0 t j ≠ Y' t j
  have hSd : Sd.card ≤ 2 * q := by
    refine (Finset.card_le_card fun t ht => ?_).trans <| (Finset.card_union_le _ _).trans (by simpa [two_mul] using add_le_add hY0q hY'q)
    rcases eq_or_ne (X t j) (Y0 t j) with h | h <;> [exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨by simp, j, by simpa [h] using (Finset.mem_filter.1 ht).2⟩); exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨by simp, j, h⟩)]
  have hdist : subspaceDistance V ≤ Sd.card := Nat.sInf_le ⟨_, V.sub_mem (hY0V j) (hY'V j), fun h => hneq (sub_eq_zero.1 (congrFun h i)).symm, by simp [Sd, sub_eq_zero]⟩
  exact not_le_of_gt h_dist (hdist.trans hSd)

lemma subspace_distance_contradiction
  {α : Type*} [Field α] [DecidableEq α]
  {m : ℕ}
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  (R : Finset (Fin m)) (hR : R.card > m - d)
  (Y1 Y2 : α) (hne : Y1 ≠ 0 ∨ Y2 ≠ 0)
  (h_zero : ∀ r ∈ R, G r 0 * Y1 + G r 1 * Y2 = 0) :
  False :=
by
  let y : Fin 2 → α := ![Y1, Y2]
  have hy_ne : y ≠ 0 := by
    intro hy; rcases hne with hY1 | hY2
    · exact hY1 (by simpa [y] using congrArg (fun f : Fin 2 → α => f 0) hy)
    · exact hY2 (by simpa [y] using congrArg (fun f : Fin 2 → α => f 1) hy)
  have hR_subset :
      R ⊆ Finset.univ.filter (fun r : Fin m => Matrix.mulVec G y r = 0) := by
    intro r hr
    refine Finset.mem_filter.2 ⟨by simp, ?_⟩
    simpa [y, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h_zero r hr
  have hZ_le :
      (Finset.univ.filter (fun r : Fin m => Matrix.mulVec G y r = 0)).card ≤ m - d := by
    simpa using
      zero_positions_card_le_of_distance (G' := G) (d' := d) (hG' := hG) (y := y) (hy := hy_ne)
  exact (not_le_of_gt hR) ((Finset.card_le_card hR_subset).trans hZ_le)

lemma subspace_distance_check_n2_deterministic_core
  {α : Type*} [Field α] [DecidableEq α]
  {m k : ℕ}
  (V : Submodule α (Fin k → α))
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  (X : Matrix (Fin k) (Fin 2) α)
  (q : ℕ)
  (h_q : 4 * q < subspaceDistance V) :
  ∀ S : Finset (Fin m),
    (∀ i : Fin m,
      i ∈ S ↔
        ∃ v ∈ V,
          (Finset.univ.filter
            (fun t : Fin k =>
              Matrix.mulVec X (fun j : Fin 2 => G i j) t ≠ v t)).card ≤ q) →
    S.card > m - d →
    ∃ Y : Matrix (Fin k) (Fin 2) α,
      (∀ j : Fin 2, (fun i => Y i j) ∈ V) ∧
      ∀ i ∈ S,
        (Finset.univ.filter
          (fun t : Fin k =>
            Matrix.mulVec (X - Y) (fun j : Fin 2 => G i j) t ≠ 0)).card ≤ q :=
by
  intro S hS hScard
  obtain ⟨r0, r1, hr01, hr0S, hr1S, hLI⟩ := linear_independence_from_distance (hn := by decide) (G := G) hG S hScard
  let g0 : Fin 2 → α := fun j => G r0 j; let g1 : Fin 2 → α := fun j => G r1 j
  have hLI' : LinearIndependent α ![g0, g1] := by simpa [g0, g1] using hLI
  obtain ⟨v0, hv0V, hv0q⟩ := (hS r0).mp hr0S; obtain ⟨v1, hv1V, hv1q⟩ := (hS r1).mp hr1S
  let B := basisOfLinearIndependentOfCardEqFinrank hLI' (by simp)
  have hB0 : B 0 = g0 := by simp [B, basisOfLinearIndependentOfCardEqFinrank]
  have hB1 : B 1 = g1 := by simp [B, basisOfLinearIndependentOfCardEqFinrank]
  let fVec : Fin 2 → (Fin k → α) := ![v0, v1]
  have hfVec_mem : ∀ j, fVec j ∈ V := by intro j; fin_cases j <;> simp [fVec, hv0V, hv1V]
  let T := B.constr (S := α) fVec
  have hT_memV : ∀ x, T x ∈ V := fun x => by
    have hx : Finset.univ.sum (fun j => (B.equivFun x j) • fVec j) ∈ V := V.sum_mem fun j _ => V.smul_mem _ (hfVec_mem j)
    simpa [T, Module.Basis.constr_apply_fintype] using hx
  let Y := LinearMap.toMatrix' T
  have hY_mulVec (g : Fin 2 → α) : Matrix.mulVec Y g = T g := by simp [Y]
  have hY_cols : ∀ j, (fun i => Y i j) ∈ V := fun j => by simpa [Y, LinearMap.toMatrix', Matrix.of_apply] using hT_memV (Pi.single j 1)
  have hY_g0 : Matrix.mulVec Y g0 = v0 := by simpa [T, fVec, hB0, hY_mulVec] using Module.Basis.constr_basis (b := B) (S := α) (f := fVec) (i := 0)
  have hY_g1 : Matrix.mulVec Y g1 = v1 := by simpa [T, fVec, hB1, hY_mulVec] using Module.Basis.constr_basis (b := B) (S := α) (f := fVec) (i := 1)
  let L := Matrix.toLin' X - T
  have hL_apply (g : Fin 2 → α) : L g = Matrix.mulVec X g - Matrix.mulVec Y g := by simp [L, hY_mulVec, Matrix.toLin'_apply]
  let e0 := L g0; let e1 := L g1
  have h_e_le_q (g v) (hYv : Matrix.mulVec Y g = v) (hvq : (Finset.univ.filter fun t => Matrix.mulVec X g t ≠ v t).card ≤ q) :
      (Finset.univ.filter fun t => L g t ≠ 0).card ≤ q := by
    refine (Finset.card_mono ?_).trans hvq
    intro t ht; rcases Finset.mem_filter.mp ht with ⟨htU, hne0⟩
    have hYval := congrArg (· t) hYv; have hLval := congrArg (· t) (hL_apply g)
    exact Finset.mem_filter.mpr ⟨htU, fun h => hne0 (by simp only [] at hYval hLval; simp [hLval, h, hYval])⟩
  have h_e0_le_q : (Finset.univ.filter fun t => e0 t ≠ 0).card ≤ q := by simpa [e0] using h_e_le_q g0 v0 hY_g0 (by simpa [g0] using hv0q)
  have h_e1_le_q : (Finset.univ.filter fun t => e1 t ≠ 0).card ≤ q := by simpa [e1] using h_e_le_q g1 v1 hY_g1 (by simpa [g1] using hv1q)
  have hL_two (g : Fin 2 → α) : L g = (B.repr g 0) • L (B 0) + (B.repr g 1) • L (B 1) := by
    have := congrArg L ((B.sum_repr g).symm.trans (by simpa using Fin.sum_univ_two fun j => (B.repr g j) • B j))
    simpa [LinearMap.map_add, LinearMap.map_smul] using this
  have hL_row_le_2q (i : Fin m) : (Finset.univ.filter fun t => L (fun j => G i j) t ≠ 0).card ≤ 2 * q := by
    let gi : Fin 2 → α := fun j => G i j
    have hcomb : L gi = (B.repr gi 0) • e0 + (B.repr gi 1) • e1 := by simpa [gi, e0, e1, g0, g1, hB0, hB1] using hL_two gi
    have hsubset : (Finset.univ.filter fun t => L gi t ≠ 0) ⊆ (Finset.univ.filter fun t => e0 t ≠ 0 ∨ e1 t ≠ 0) := fun t ht => by
      rcases Finset.mem_filter.mp ht with ⟨htU, hne0⟩
      exact Finset.mem_filter.mpr ⟨htU, by by_contra h; push_neg at h; exact hne0 (by simpa [h.1, h.2] using congrArg (· t) hcomb)⟩
    exact ((Finset.card_mono hsubset).trans (by simpa [Finset.filter_or] using Finset.card_union_le _ _)).trans (by simpa [two_mul] using add_le_add h_e0_le_q h_e1_le_q)
  have unique_vector {w v1 v2 : Fin k → α} (hv1 : v1 ∈ V) (hv2 : v2 ∈ V) (hwv1 : (Finset.univ.filter fun t => w t ≠ v1 t).card ≤ 2 * q) (hwv2 : (Finset.univ.filter fun t => w t ≠ v2 t).card ≤ 2 * q) : v1 = v2 := by
    by_contra hneq; let z : Fin k → α := fun t => v1 t - v2 t
    have hzV : z ∈ V := by simpa [z, Pi.sub_def] using V.sub_mem hv1 hv2
    have hz_ne0 : z ≠ 0 := fun hz0 => hneq (funext fun t => by simpa [z, sub_eq_zero] using congrArg (· t) hz0)
    let Sd : Finset (Fin k) := Finset.univ.filter fun t => z t ≠ 0
    have hsubset_sd : Sd ⊆ (Finset.univ.filter fun t => w t ≠ v1 t) ∪ (Finset.univ.filter fun t => w t ≠ v2 t) := fun t ht => by
      rcases Finset.mem_filter.mp ht with ⟨htU, hzne⟩
      have : w t ≠ v1 t ∨ w t ≠ v2 t := by by_contra h; push_neg at h; exact hzne (by simp [z, h.1.symm, h.2.symm])
      rcases this with h1 | h2 <;> [exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨htU, h1⟩)); exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨htU, h2⟩))]
    have hSd_le : Sd.card ≤ 4 * q := ((Finset.card_mono hsubset_sd).trans (Finset.card_union_le _ _)).trans (by linarith)
    have hdist_le : subspaceDistance V ≤ Sd.card := Nat.sInf_le ⟨z, hzV, hz_ne0, rfl⟩
    exact not_le_of_gt h_q (hdist_le.trans hSd_le)
  refine ⟨Y, hY_cols, fun i hiS => ?_⟩
  obtain ⟨vi, hviV, hviq⟩ := (hS i).mp hiS
  let gi : Fin 2 → α := fun j => G i j; let w := Matrix.mulVec X gi
  have hYgi_inV : Matrix.mulVec Y gi ∈ V := by simpa [hY_mulVec] using hT_memV gi
  have hY_le_2q : (Finset.univ.filter fun t => w t ≠ Matrix.mulVec Y gi t).card ≤ 2 * q := by
    have hsubset : (Finset.univ.filter fun t => w t ≠ Matrix.mulVec Y gi t) ⊆ (Finset.univ.filter fun t => L gi t ≠ 0) := fun t ht => by
      rcases Finset.mem_filter.mp ht with ⟨htU, hneq⟩
      exact Finset.mem_filter.mpr ⟨htU, fun h0 => hneq (sub_eq_zero.mp (by simpa [h0, w, gi] using (congrArg (· t) (hL_apply gi)).symm))⟩
    exact (Finset.card_mono hsubset).trans (hL_row_le_2q i)
  have h_eq : vi = Matrix.mulVec Y gi := unique_vector hviV hYgi_inV (hviq.trans (by simp [two_mul])) hY_le_2q
  have hsubset2 : (Finset.univ.filter fun t => Matrix.mulVec (X - Y) gi t ≠ 0) ⊆ (Finset.univ.filter fun t => Matrix.mulVec X gi t ≠ Matrix.mulVec Y gi t) := fun t ht => by
    rcases Finset.mem_filter.mp ht with ⟨htU, hneq0⟩
    exact Finset.mem_filter.mpr ⟨htU, fun h => hneq0 (by simp [congrArg (· t) (Matrix.sub_mulVec (A := X) (B := Y) (x := gi)), h])⟩
  simpa [gi] using (Finset.card_mono hsubset2).trans (by simpa [w, h_eq] using hviq)

lemma subspace_distance_check_n2_main_reduction
  {α : Type*} [Field α] [DecidableEq α]
  {m k : ℕ}
  (V : Submodule α (Fin k → α))
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  (X : Matrix (Fin k) (Fin 2) α)
  (q : ℕ)
  (h_q : 4 * q < subspaceDistance V)
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (r : Ω → Fin m)
  (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
  (h_not_close : ¬ qCloseToSubspace V q X) :
  μ {ω : Ω |
      (∃ v ∈ V,
        (Finset.univ.filter (fun i : Fin k =>
          (Matrix.mulVec X (fun j : Fin 2 => G (r ω) j) i ≠ v i))).card ≤ q)
      ∧ ¬ (qCloseToSubspace V q X) }
    ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) :=
by
  classical
  set S := Finset.univ.filter fun i => ∃ v ∈ V,
    (Finset.univ.filter fun t : Fin k => Matrix.mulVec X (fun j => G i j) t ≠ v t).card ≤ q
  have h_eq : {ω | ∃ v ∈ V, (Finset.univ.filter fun i =>
    Matrix.mulVec X (fun j => G (r ω) j) i ≠ v i).card ≤ q} = {ω | r ω ∈ S} := by ext; simp [S]
  suffices μ {ω | r ω ∈ S} ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) by
    simpa [h_eq] using (measure_mono fun ω hω => by simpa [← h_eq, S] using hω.1).trans this
  by_cases hScard : S.card ≤ m - d
  · have hμ : μ {ω | r ω ∈ S} ≤ S.card • ((1 : ENNReal) / m) := by
      simpa [Finset.sum_const, h_unif] using measure_preimage_finset_le_sum_singletons μ r S
    by_cases hm0 : m = 0
    · subst hm0; simp [S]
    · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
      have hd : d ≤ m := by
        simpa [Fintype.card_fin] using (hG (fun _ => 1) (fun h => one_ne_zero (congrFun h 0))).trans (Finset.card_filter_le _ _)
      calc μ {ω | r ω ∈ S}
        ≤ ((m - d : ℕ) : ENNReal) / m := by
            simpa [div_eq_mul_inv, nsmul_eq_mul] using hμ.trans (by simp [nsmul_eq_mul]; exact mul_le_mul' (by exact_mod_cast hScard) le_rfl)
        _ = ENNReal.ofReal (1 - (d : ℝ) / m) := by
            simpa [one_sub_div (ne_of_gt hm_pos), Nat.cast_sub hd] using (ENNReal.ofReal_div_of_pos hm_pos).symm
        _ ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / m)) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [show (1 : ℝ) ≤ q + 1 by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q),
              show 0 ≤ 1 - (d : ℝ) / m from sub_nonneg.mpr (div_le_one_of_le₀ (by exact_mod_cast hd) (by exact_mod_cast Nat.zero_le m))])
  · obtain ⟨Y, hY, hYerr⟩ := subspace_distance_check_n2_deterministic_core V G hG X q h_q S (fun i => by simp [S]) (Nat.lt_of_not_ge hScard)
    have h1 : ¬ (Finset.univ.filter fun i => ∃ j, (X - Y) i j ≠ 0).card ≤ q := by
      simpa [Matrix.sub_apply, sub_eq_zero] using fun h => h_not_close ⟨Y, hY, h⟩
    exact (measure_mono fun ω hω => And.intro (hYerr (r ω) hω) h1).trans (by simpa using matrix_sparsity_check G hG μ r h_unif q (X - Y))

lemma subspace_distance_check_n2
  {α : Type*} [Field α] [DecidableEq α]
  {m k : ℕ}
  (V : Submodule α (Fin k → α))
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (r : Ω → Fin m)
  (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
  (X : Matrix (Fin k) (Fin 2) α)
  (q : ℕ) (h_q : 4 * q < subspaceDistance V) :
  μ {ω |
      (∃ v ∈ V,
        (Finset.univ.filter (fun i : Fin k =>
          (Matrix.mulVec X (fun j : Fin 2 => G (r ω) j) i ≠ v i))).card ≤ q)
      ∧ ¬ (qCloseToSubspace V q X) }
    ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) :=
by
  by_cases h_close : qCloseToSubspace V q X
  ·
    have h_empty :
        {ω |
            (∃ v ∈ V,
              (Finset.univ.filter
                    (fun i : Fin k =>
                      Matrix.mulVec X (fun j : Fin 2 => G (r ω) j) i ≠ v i)).card ≤
                q) ∧
              ¬ qCloseToSubspace V q X} =
          (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro _; exact h_close
    rw [h_empty, measure_empty]
    exact bot_le
  · exact subspace_distance_check_n2_main_reduction V G hG X q h_q μ r h_unif h_close

/-- Basis Alignment for Diagonal Operators: if a two-column matrix `X = [x₁ x₂]` is `q`-close to a subspace `V'`, then for any diagonal weights `D : Fin k → α`, any linear combination `a · x₁ + D ⊙ x₂` is within Hamming distance ≤ `q` of `V'`. -/
lemma basis_alignment_diagonal
  {α : Type*} [Semiring α] [DecidableEq α] [Zero α]
  {k : ℕ}
  (V' : Submodule α (Fin k → α)) (q : ℕ)
  (X : Matrix (Fin k) (Fin 2) α)
  (hclose : qCloseToSubspace V' q X) :
  ∀ a b : α, ∃ v ∈ V',
    (Finset.univ.filter
      (fun i : Fin k => (a * X i 0 + b * X i 1) ≠ v i)).card ≤ q :=
by intro a b; obtain ⟨Y, hcols, hcard⟩ := hclose; exact ⟨_, V'.add_mem (V'.smul_mem a (hcols 0)) (V'.smul_mem b (hcols 1)), (Finset.card_le_card fun i hi => by simp at hi ⊢; exact if h : X i 0 = Y i 0 then Or.inr (fun heq => hi (by simp [h, heq])) else Or.inl h).trans hcard⟩

/-- FRI Basis Alignment: with `T1 = [I; I]` and `T2 = [D; −D]` (for a diagonal `D : Fin m → α`), if `X = [x₁ x₂] : Matrix (Fin m) (Fin 2) α` is `q`-close to `V'`, then `T1 x₁ + T2 x₂` is within Hamming distance ≤ `2q` of the larger space `V` (as a vector in `α^{2m}`). -/
lemma fri_basis_alignment
  {α : Type*} [Ring α] [DecidableEq α]
  {m : ℕ}
  (V : Submodule α (Fin (m + m) → α))
  (V' : Submodule α (Fin m → α))
  (D : Fin m → α)
  (X : Matrix (Fin m) (Fin 2) α)
  (q : ℕ)
  (hT1 : ∀ y ∈ V',
    (fun i : Fin (m + m) => Fin.addCases y y i) ∈ V)
  (hT2 : ∀ y ∈ V',
    (fun i : Fin (m + m) =>
      Fin.addCases (fun j => D j * y j) (fun j => - D j * y j) i) ∈ V)
  (hclose : qCloseToSubspace V' q X) :
  ∃ v ∈ V,
    (Finset.univ.filter (fun i : Fin (m + m) =>
      let top : Fin m → α := fun j => X j 0 + (D j) * X j 1
      let bot : Fin m → α := fun j => X j 0 - (D j) * X j 1
      (Fin.addCases top bot i) ≠ v i)).card ≤ 2 * q :=
by
  obtain ⟨Y, hcols, hS_le⟩ := hclose
  set S := Finset.univ.filter fun j => ∃ t : Fin 2, X j t ≠ Y j t
  set y0 := fun j => Y j 0; set y1 := fun j => Y j 1
  set v : Fin (m + m) → α := fun i => Fin.addCases y0 y0 i + Fin.addCases (fun j => D j * y1 j) (fun j => - D j * y1 j) i
  set Top := fun j => X j 0 + D j * X j 1; set Bot := fun j => X j 0 - D j * X j 1
  have hsubset : (Finset.univ.filter fun i => Fin.addCases Top Bot i ≠ v i) ⊆ S.image (Fin.castAdd m) ∪ S.image (Fin.addNat · m) := fun i hi => by
    have hagree : ∀ j ∉ S, ∀ t, X j t = Y j t := fun j hj t => by
      by_contra h
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hj
      exact hj t h
    obtain ⟨-, hneq⟩ := Finset.mem_filter.1 hi
    by_cases hlt : (i : ℕ) < m
    · set j := Fin.castLT i hlt
      have hij : (Fin.castAdd m j : Fin (m + m)) = i := by simp [j]
      by_cases hjS : j ∈ S
      · exact Finset.mem_union.2 (Or.inl (hij ▸ Finset.mem_image.mpr ⟨j, hjS, rfl⟩))
      · simp only [by simpa [hij] using Fin.addCases_left (m := m) (n := m) (motive := fun _ => α) (left := Top) (right := Bot) j, by simpa [hij] using (by simp [v] : v (Fin.castAdd m j) = y0 j + D j * y1 j), Top, y0, y1, hagree j hjS, ne_eq, not_true_eq_false] at hneq
    · let j : Fin m := ⟨i - m, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hlt) i.2⟩
      have hij : (j.addNat m : Fin (m + m)) = i := by simpa [Fin.ext_iff, Nat.add_comm] using Nat.add_sub_of_le (Nat.le_of_not_lt hlt)
      by_cases hjS : j ∈ S
      · exact Finset.mem_union.2 (Or.inr (hij ▸ Finset.mem_image.mpr ⟨j, hjS, rfl⟩))
      · have h2 : v i = y0 j - D j * y1 j := by simp [v, sub_eq_add_neg, by simpa [hij] using Fin.addCases_right (m := m) (n := m) (motive := fun _ => α) (left := y0) (right := y0) j, by simpa [hij] using Fin.addCases_right (m := m) (n := m) (motive := fun _ => α) (left := fun t => D t * y1 t) (right := fun t => - (D t * y1 t)) j]
        simp only [by simpa [hij] using Fin.addCases_right (m := m) (n := m) (motive := fun _ => α) (left := Top) (right := Bot) j, h2, Bot, y0, y1, hagree j hjS, ne_eq, not_true_eq_false] at hneq
  refine ⟨v, by simpa [v] using V.add_mem (hT1 y0 (by simpa using hcols 0)) (hT2 y1 (by simpa using hcols 1)), ?_⟩
  exact ((Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)).trans (by rw [Finset.card_image_of_injective _ (Fin.castAdd_injective _ _), Finset.card_image_of_injOn fun x _ y _ h => (Fin.addNat_inj (n := m) (m := m)).1 h]; omega)

/- FRI Reduction Step: union-of-failure-events; rows(G)=m as in the blueprint; includes `y` and assumes `S` is a uniformly random s-subset of `{0,…,2m-1}`. -/
lemma fri_reduction_step
  {α : Type*} [Field α] [DecidableEq α]
  {m : ℕ}
  (V : Submodule α (Fin (m + m) → α))
  (V' : Submodule α (Fin m → α))
  (D : Fin m → α)
  (hT1 : ∀ y ∈ V',
    (fun i : Fin (m + m) => Fin.addCases y y i) ∈ V)
  (hT2 : ∀ y ∈ V',
    (fun i : Fin (m + m) =>
      Fin.addCases (fun j => D j * y j) (fun j => - D j * y j) i) ∈ V)
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (r : Ω → Fin m) (h_unif : ∀ i : Fin m, μ {ω | r ω = i} = (1 : ENNReal) / (m : ENNReal))
  (X : Matrix (Fin m) (Fin 2) α)
  (y : Fin (m + m) → α)
  (q : ℕ)
  (h_q : 4 * q < subspaceDistance V')
  (h_close : qCloseToSubspace V' q X)
  (S : Ω → Finset (Fin (m + m))) (s : ℕ)
  (h_card : ∀ ω, (S ω).card = s)
  (hS_unif : ∀ A : Finset (Fin (m + m)), A.card = s →
      μ {ω | S ω = A} = (1 : ENNReal) / ((Nat.choose (2 * m) s : ℕ) : ENNReal)) :
  μ {ω |
      ((∃ v' ∈ V',
          (Finset.univ.filter (fun i : Fin m =>
             (Matrix.mulVec X (fun j : Fin 2 => G (r ω) j) i ≠ v' i))).card ≤ q)
        ∧ ¬ (qCloseToSubspace V' q X))
      ∨
      ((∀ i ∈ S ω,
          let top : Fin m → α := fun j => X j 0 + (D j) * X j 1
          let bot : Fin m → α := fun j => X j 0 - (D j) * X j 1
          y i = (Fin.addCases top bot i))
        ∧ ¬ (∃ v ∈ V,
            (Finset.univ.filter (fun i : Fin (m + m) => y i ≠ v i)).card ≤ 3 * q))}
    ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) +
      ENNReal.ofReal ((1 - ((q + 1 : ℝ) / ((2 * m) : ℝ))) ^ s) :=
by
  let t : Fin (m + m) → α := Fin.addCases (fun j => X j 0 + D j * X j 1) (fun j => X j 0 - D j * X j 1)
  let xmask := fun i => y i - t i
  have h_sub : {ω : Ω | (∀ i ∈ S ω, y i = t i) ∧ ¬∃ v ∈ V, (Finset.univ.filter fun i : Fin (m + m) => y i ≠ v i).card ≤ 3 * q} ⊆
      {ω | (∀ i ∈ S ω, xmask i = 0) ∧ ¬(Finset.univ.filter fun i : Fin (m + m) => xmask i ≠ 0).card ≤ q} := fun ω ⟨hall, hnot⟩ => by
    obtain ⟨v0, hv0V, hv0_le⟩ := fri_basis_alignment V V' D X q hT1 hT2 h_close
    refine ⟨fun i hi => by simp [xmask, hall i hi], fun hB => hnot ⟨v0, hv0V, ?_⟩⟩
    have := ((Finset.card_le_card (s := Finset.univ.filter fun i => y i ≠ v0 i) fun i hi => by
        rcases Finset.mem_filter.1 hi with ⟨_, hy⟩; by_cases hx : xmask i = 0 <;>
        [exact Finset.mem_union.2 <| .inr <| Finset.mem_filter.2 ⟨by simp, by simpa [sub_eq_zero.mp hx] using hy⟩;
         exact Finset.mem_union.2 <| .inl <| Finset.mem_filter.2 ⟨by simp, hx⟩]).trans (Finset.card_union_le _ _)).trans (add_le_add hB hv0_le)
    simp only [Nat.succ_mul, add_comm] at this ⊢; omega
  refine (measure_union_le _ _).trans (add_le_add (subspace_distance_check_n2 V' G hG μ r h_unif X q h_q)
    ((measure_mono h_sub).trans (by simpa [two_mul] using mask_zero_uniform_subset_bound μ S s h_card (fun A hA => by simpa [two_mul] using hS_unif A hA) xmask q)))

/-- The "Bad Event" for round `i`: the verifier ACCEPTS but data is BAD.

This is the correct formulation for soundness: we require BOTH checks to pass
(so the verifier accepts this round), AND the data is bad (X not close OR y not close).

The conjunction-based structure allows proving bounds WITHOUT assuming closeness:
- If X is close: the sampling check catches bad y (via fri_basis_alignment)
- If X is NOT close: Pr[folding passes] ≤ (q+1)(1-d/m), bounding the whole event

FRI Structure at round i (matching fri_reduction_step):
- m := folded dimension
- V: subspace of Fin (m + m) → α (current round)
- V': subspace of Fin m → α (folded)
- G: code matrix with m rows, 2 columns
- X: matrix m × 2 (the two columns being folded)
- D: Fin m → α (diagonal folding coefficients)
- y: Fin (m + m) → α (the current round's oracle, via Fin.addCases)
- S: random subset of Fin (m + m) for sampling check -/
def friRoundBadEvent
  {α : Type*} [Field α] [DecidableEq α]
  {Ω : Type*}
  (m : ℕ)
  (V : Submodule α (Fin (m + m) → α))
  (V' : Submodule α (Fin m → α))
  (G : Matrix (Fin m) (Fin 2) α)
  (r : Ω → Fin m)
  (X : Matrix (Fin m) (Fin 2) α)
  (D : Fin m → α)
  (y : Fin (m + m) → α)
  (q : ℕ)
  (S : Ω → Finset (Fin (m + m))) : Set Ω :=
  {ω |
      -- Verifier accepts: BOTH checks pass
      -- 1. Folding check passes: random linear combination is close to V'
      (∃ v' ∈ V',
          (Finset.univ.filter (fun t : Fin m =>
             Matrix.mulVec X (fun j : Fin 2 => G (r ω) j) t ≠ v' t)).card ≤ q)
      ∧
      -- 2. Sampling check passes: y agrees with expected folding on S
      (∀ t ∈ S ω,
          let top : Fin m → α := fun j => X j 0 + (D j) * X j 1
          let bot : Fin m → α := fun j => X j 0 - (D j) * X j 1
          y t = Fin.addCases top bot t)
      ∧
      -- But data is bad: X not close OR y not close
      (¬ (qCloseToSubspace V' q X) ∨
       ¬ (∃ v ∈ V, (Finset.univ.filter (fun t : Fin (m + m) => y t ≠ v t)).card ≤ 3 * q))
  }

/-- Round-wise Error: bounds the bad event for round i of FRI.
From blueprint lem:round_wise_error: "Direct from Lemma fri_reduction_step with substituted parameters."

With the conjunction-based friRoundBadEvent, this bound holds WITHOUT assuming closeness:
- If X is close to V': the "X not close" part of bad is false, so we only need to
  bound Pr[sampling passes ∧ y not close], which uses fri_basis_alignment + masking
- If X is NOT close: Pr[folding passes] ≤ (q+1)(1-d/m) by subspace_distance_check_n2,
  which bounds the entire event since both checks must pass -/
lemma round_wise_error
  {α : Type*} [Field α] [DecidableEq α]
  {m : ℕ}
  (V : Submodule α (Fin (m + m) → α))
  (V' : Submodule α (Fin m → α))
  (D : Fin m → α)
  -- FRI structural hypotheses (T1 and T2 from def:fri_subspace_structure)
  (hT1 : ∀ y ∈ V', (fun j : Fin (m + m) => Fin.addCases y y j) ∈ V)
  (hT2 : ∀ y ∈ V', (fun j : Fin (m + m) =>
      Fin.addCases (fun k => D k * y k) (fun k => - D k * y k) j) ∈ V)
  (G : Matrix (Fin m) (Fin 2) α) {d : ℕ}
  (hG : codeHasDistanceAtLeast G d)
  {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (r : Ω → Fin m) (h_unif : ∀ j : Fin m, μ {ω | r ω = j} = (1 : ENNReal) / (m : ENNReal))
  (X : Matrix (Fin m) (Fin 2) α)
  (y : Fin (m + m) → α)
  (q : ℕ)
  (h_q : 4 * q < subspaceDistance V')
  (s : ℕ)
  (S : Ω → Finset (Fin (m + m)))
  (h_card : ∀ ω, (S ω).card = s)
  (hS_unif : ∀ A : Finset (Fin (m + m)), A.card = s →
      μ {ω | S ω = A} = (1 : ENNReal) / ((Nat.choose (2 * m) s : ℕ) : ENNReal)) :
  μ (friRoundBadEvent m V V' G r X D y q S)
    ≤ ENNReal.ofReal ((q + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ))) +
      ENNReal.ofReal ((1 - ((q + 1 : ℝ) / ((2 * m) : ℝ))) ^ s) :=
by by_cases h : qCloseToSubspace V' q X <;>
  [exact (measure_mono <| by rintro _ ⟨-, s, b⟩; exact b.elim (absurd h) (.inr ⟨s, ·⟩)).trans
    (fri_reduction_step V V' D hT1 hT2 G hG μ r h_unif X y q h_q h S _ h_card hS_unif);
   exact (measure_mono <| by rintro _ ⟨f, -⟩; exact ⟨f, h⟩).trans
    ((subspace_distance_check_n2 V' G hG μ r h_unif X q h_q).trans le_self_add)]

lemma nat_div_ratio_lower_bound_two_thirds_pow (q n i : ℕ)
  (h_den_pos : 0 < n / 2 ^ i) :
  (((q / 3 ^ i : ℕ) : ℝ) + 1) / ((n / 2 ^ i : ℕ) : ℝ)
    ≥ (q : ℝ) / (n : ℝ) * ((2 : ℝ) / 3) ^ i :=
by
  have hB : 0 < (↑(n / 2 ^ i) : ℝ) := Nat.cast_pos.2 h_den_pos
  have hA : (q:ℝ)/3^i ≤ ↑(q/3^i)+1 := by
    have := Nat.div_add_mod' q (3^i); have := Nat.mod_lt q (pow_pos (by omega:0<3) i)
    rw [div_le_iff₀ (by positivity), add_mul, one_mul]; exact_mod_cast by omega
  have hC : (2:ℝ)^i/n*↑(n/2^i)≤1 := by
    have h := (le_div_iff₀ (by positivity:(0:ℝ)<2^i)).2 (by exact_mod_cast Nat.div_mul_le_self n (2^i):↑(n/2^i)*(2:ℝ)^i≤n)
    simpa [one_div, hB.ne'] using mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hB h) hB.le
  rw [ge_iff_le, le_div_iff₀ hB]
  linarith [(by simp [div_pow]; ring:(q:ℝ)/n*(2/3)^i*↑(n/2^i)=(q:ℝ)/3^i*((2:ℝ)^i/n*↑(n/2^i))).le.trans (mul_le_of_le_one_right (by positivity) hC)]

lemma sum_nat_div_pow3_add_one_le (k q : ℕ) :
  (Finset.sum (Finset.range k) (fun i => ((q / 3 ^ i : ℕ) : ℝ) + 1))
    ≤ ((3 : ℝ) / 2) * (q : ℝ) + (k : ℝ) :=
by
  have hg : ∑ i ∈ Finset.range k, (1/3:ℝ)^i ≤ 3/2 := Nat.Ico_zero_eq_range ▸ (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans_eq (by norm_num)
  calc _ ≤ ∑ i ∈ Finset.range k, ((q:ℝ)/3^i+1) := Finset.sum_le_sum fun i _ =>
      add_le_add_right ((le_div_iff₀ (by positivity)).2 (mod_cast q.div_mul_le_self (3^i))) _
    _ = q * ∑ i ∈ Finset.range k, (1/3:ℝ)^i + k := by simp [div_eq_mul_inv, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by nlinarith [hg, Nat.cast_nonneg (α := ℝ) q]


/-- Geometric Summation: suppose for each `i = 0,…,k−1` we have a per-round failure probability `p i` bounded by the round-wise expression with `qᵢ = q / 3^i`, `nᵢ = n / 2^i`, and sample sizes `s i = η · (3/2)^i`. Then the total failure probability `∑_{i=0}^{k-1} p i` is at most `((3/2)·q + k)·(1 - d/m) + k · exp(−η·q/n)`. -/
lemma geometric_summation (k η q d m n : ℕ)
  (s : ℕ → ℕ) (hs : ∀ i < k, (s i : ℝ) = η * ((3 : ℝ) / 2) ^ i)
  (p : ℕ → ℝ)
  (h_pi : ∀ i < k,
    p i ≤ (((q / 3 ^ i : ℕ) + 1 : ℝ) * (1 - (d : ℝ) / (m : ℝ)) +
            (1 - (((q / 3 ^ i : ℕ) + 1 : ℝ) / ((n / 2 ^ i : ℕ) : ℝ))) ^ (s i)))
  (h_d_le_m : d ≤ m)
  (h_den_pos : ∀ i < k, 0 < (n / 2 ^ i))
  (h_lambda_le_one :
    ∀ i < k,
      (((q / 3 ^ i : ℕ) + 1 : ℝ)
          ≤ ((n / 2 ^ i : ℕ) : ℝ))) :
  (Finset.sum (Finset.range k) (fun i => p i))
    ≤ ((3 : ℝ) / 2 * (q : ℝ) + (k : ℝ)) * (1 - (d : ℝ) / (m : ℝ)) +
      (k : ℝ) * Real.exp (-(η : ℝ) * (q : ℝ) / (n : ℝ)) :=
by
  set c := 1 - (d : ℝ) / (m : ℝ); have hc : 0 ≤ c := sub_nonneg.mpr (div_le_one_of_le₀ (Nat.cast_le.mpr h_d_le_m) (Nat.cast_nonneg m))
  have hsampling : (∑ i ∈ Finset.range k, (1 - (((q / 3 ^ i : ℕ) + 1 : ℝ) / ((n / 2 ^ i : ℕ) : ℝ))) ^ (s i)) ≤ k * Real.exp (-(η : ℝ) * q / n) := by
    have h : ∀ i ∈ Finset.range k, (1 - (((q / 3 ^ i : ℕ) + 1 : ℝ) / ((n / 2 ^ i : ℕ) : ℝ))) ^ (s i) ≤ Real.exp (-(η : ℝ) * q / n) := fun i hi => by
      set lam := (((q / 3 ^ i : ℕ) : ℝ) + 1) / ((n / 2 ^ i : ℕ) : ℝ); have hlam_le : lam ≤ 1 := div_le_one_of_le₀ (h_lambda_le_one i (Finset.mem_range.mp hi)) (Nat.cast_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left (nat_div_ratio_lower_bound_two_thirds_pow q n i (h_den_pos i (Finset.mem_range.mp hi))) (by positivity : (0:ℝ) ≤ η * ((3 : ℝ) / 2) ^ i)
      have hpow : ((3 : ℝ) / 2) ^ i * ((2 : ℝ) / 3) ^ i = 1 := by rw [← mul_pow]; norm_num
      have hEq : (s i : ℝ) * lam ≥ η * q / n := by
        rw [hs i (Finset.mem_range.mp hi)]
        calc η * ((3 : ℝ) / 2) ^ i * lam ≥ η * ((3 : ℝ) / 2) ^ i * (q / n * (2 / 3) ^ i) := h1
          _ = η * q / n * (((3 : ℝ) / 2) ^ i * (2 / 3) ^ i) := by ring
          _ = η * q / n := by rw [hpow]; ring
      exact (pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _).trans (by rw [← Real.exp_nat_mul]; simpa [mul_comm, mul_assoc, div_eq_mul_inv] using Real.exp_le_exp.mpr (neg_le_neg hEq))
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum h
  have h1 : ∑ i ∈ Finset.range k, p i ≤ c * ∑ i ∈ Finset.range k, (((q / 3 ^ i : ℕ) : ℝ) + 1) + ∑ i ∈ Finset.range k, (1 - (((q / 3 ^ i : ℕ) + 1 : ℝ) / ((n / 2 ^ i : ℕ) : ℝ))) ^ (s i) := by
    convert Finset.sum_le_sum fun i hi => h_pi i (Finset.mem_range.mp hi) using 1; simp [Finset.sum_add_distrib, mul_comm c, ← Finset.sum_mul]
  linarith [mul_le_mul_of_nonneg_left (sum_nat_div_pow3_add_one_le k q) hc]

lemma one_sub_pow_le_exp_neg_of_mul_ge
  {s : ℕ} {lam L : ℝ}
  (h_lam_le_one : lam ≤ 1)
  (h_mul_ge : (s : ℝ) * lam ≥ L) :
  (1 - lam) ^ s ≤ Real.exp (-L) :=
by
  refine (pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _).trans ?_
  simpa [← Real.exp_nat_mul] using neg_le_neg h_mul_ge

lemma sum_one_sub_pow_le_exp_neg_const
  (k : ℕ) (s : ℕ → ℕ) (lam : ℕ → ℝ) (L : ℝ)
  (h : ∀ i < k, lam i ≤ 1 ∧ (s i : ℝ) * lam i ≥ L) :
  (Finset.sum (Finset.range k) (fun i => (1 - lam i) ^ (s i))) ≤
    (k : ℝ) * Real.exp (-L) :=
by
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    (Finset.sum_le_sum fun i hi =>
      one_sub_pow_le_exp_neg_of_mul_ge (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2)

lemma concrete_parameters_analytic_bound
  (s : ℕ → ℕ) (p : ℕ → ℝ)
  (q n : ℕ)
  (hs : ∀ i < (28 : ℕ), (470 : ℝ) * ((3 : ℝ) / 2) ^ i ≤ (s i : ℝ))
  (h_pi : ∀ i < (28 : ℕ),
    p i ≤ (((q / 3 ^ i : ℕ) + 1 : ℝ) * (1 / ((2 : ℝ) ^ (128 : ℕ))) +
            (1 - (((q / 3 ^ i : ℕ) + 1 : ℝ) / ((n / 2 ^ i : ℕ) : ℝ))) ^ (s i)))
  (hq : q = (2 ^ 32 : ℕ) / 8)
  (hn : n = 2 ^ 32) :
  (Finset.sum (Finset.range (28 : ℕ)) (fun i => p i))
    ≤ (((3 : ℝ) / 2) * (q : ℝ) + (28 : ℝ)) * (1 / ((2 : ℝ) ^ (128 : ℕ))) +
      (28 : ℝ) * Real.exp (-(470 : ℝ) * (q : ℝ) / (n : ℝ)) :=
by
  have h_all : ∀ i < 28, (((2 ^ 32 : ℕ) / 8) / 3 ^ i + 1) ≤ (2 ^ 32 : ℕ) / 2 ^ i ∧ 0 < (2 ^ 32 : ℕ) / 2 ^ i := by decide
  set lam := fun i => (((q / 3 ^ i : ℕ) : ℝ) + 1) / ((n / 2 ^ i : ℕ) : ℝ); set c : ℝ := 1 / 2 ^ 128
  have h_mul_ge : ∀ i < 28, lam i ≤ 1 ∧ (s i : ℝ) * lam i ≥ 470 * (q : ℝ) / n := fun i hi => by
    have hlam_lb := nat_div_ratio_lower_bound_two_thirds_pow q n i (by simpa [hn] using (h_all i hi).2)
    have hpow : ((3 : ℝ) / 2) ^ i * ((2 : ℝ) / 3) ^ i = 1 := by rw [← mul_pow]; norm_num
    have hEq : 470 * ((3 : ℝ) / 2) ^ i * ((q : ℝ) / n * ((2 : ℝ) / 3) ^ i) = 470 * q / n := by
      calc _ = 470 * ((q : ℝ) / n) * (((3 : ℝ) / 2) ^ i * ((2 : ℝ) / 3) ^ i) := by ring
           _ = _ := by rw [hpow]; ring
    exact ⟨div_le_one_of_le₀ (mod_cast by simpa [hq, hn] using (h_all i hi).1) (Nat.cast_nonneg _), hEq ▸
      (mul_le_mul_of_nonneg_right (hs i hi) (by positivity)).trans (mul_le_mul_of_nonneg_left hlam_lb (Nat.cast_nonneg _))⟩
  calc ∑ i ∈ Finset.range 28, p i ≤ ∑ i ∈ Finset.range 28, ((((q / 3 ^ i : ℕ) + 1 : ℝ) * c) + (1 - lam i) ^ (s i)) :=
        Finset.sum_le_sum fun i hi => by simpa [c, lam] using h_pi i (Finset.mem_range.mp hi)
    _ = c * ∑ i ∈ Finset.range 28, (((q / 3 ^ i : ℕ) : ℝ) + 1) + ∑ i ∈ Finset.range 28, (1 - lam i) ^ (s i) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul]; ring
    _ ≤ c * (((3 : ℝ) / 2) * q + 28) + 28 * Real.exp (-470 * (q : ℝ) / n) := add_le_add
        (mul_le_mul_of_nonneg_left (sum_nat_div_pow3_add_one_le 28 q) (by positivity))
        (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using sum_one_sub_pow_le_exp_neg_const 28 s lam _ h_mul_ge)
    _ = _ := by simp [c, mul_comm]

/-- Query Count: if `|Sᵢ| = η · (3/2)^i` for i = 1,…,k, then the total number of queries is `∑_{i=1}^k |Sᵢ| = 2·η·((3/2)^{k+1} - 1)`. -/
lemma query_count (k : ℕ) (η : ℝ) :
  (Finset.sum (Finset.range k) (fun i => η * ((3 : ℝ) / 2) ^ i))
    = 2 * η * (((3 : ℝ) / 2) ^ k - 1) :=
by simp only [← Finset.mul_sum, Nat.Ico_zero_eq_range.symm]; rw [geom_sum_Ico (by norm_num) (Nat.zero_le k)]; ring

/-- Concrete Parameters: with `|F| = 2^128`, `n = 2^32`, `q = n/8`, `k = 28`, and `η = 470`, if each per-round failure `p i` satisfies the round-wise bound with `1 − d/m = 1/|F|` (Reed–Solomon), then the total failure probability is below `2^{-79}` (the blueprint’s earlier `2^{-80}` target was slightly too strong numerically). -/
lemma concrete_parameters
  (s : ℕ → ℕ) (p : ℕ → ℝ)
  (hs : ∀ i < (28 : ℕ), (470 : ℝ) * ((3 : ℝ) / 2) ^ i ≤ (s i : ℝ))
  (h_pi : ∀ i < (28 : ℕ),
    p i ≤ (((((2 ^ 32 : ℕ) / 8) / 3 ^ i : ℕ) + 1 : ℝ) * (1 / ((2 : ℝ) ^ (128 : ℕ))) +
            (1 - ((((((2 ^ 32 : ℕ) / 8) / 3 ^ i : ℕ) + 1 : ℝ) / (((2 ^ 32 : ℕ) / 2 ^ i : ℕ) : ℝ)))) ^ (s i))) :
  (Finset.sum (Finset.range (28 : ℕ)) (fun i => p i)) < 1 / ((2 : ℝ) ^ (79 : ℕ)) :=
by
  apply (concrete_parameters_analytic_bound s p _ _ hs h_pi rfl rfl).trans_lt
  suffices Real.exp (-(470/8)) ≤ 1/(2:ℝ)^84 by norm_num; linarith
  rw [← Real.le_log_iff_exp_le (by positivity)]; simp [Real.log_inv, Real.log_pow]; nlinarith [Real.log_two_lt_d9]

lemma kronecker_generalization {s : ℕ}
  (a : Fin s → ℝ)
  (ha : ∀ j, 0 ≤ a j ∧ a j ≤ 1)
  (h_two : ∃ i j : Fin s, i ≠ j ∧ 0 < a i ∧ a i < 1 ∧ 0 < a j ∧ a j < 1) :
  1 - (Finset.univ.prod (fun j : Fin s => a j))
    < (Finset.univ.sum (fun j : Fin s => (1 - a j))) :=
by
  classical
  rcases h_two with ⟨i, j, hij, _, hi1, _, hj1⟩
  set T := Finset.univ.erase i
  have union_bound : ∀ S : Finset (Fin s), 1 - ∏ t ∈ S, a t ≤ ∑ t ∈ S, (1 - a t) := by
    intro S; induction S using Finset.induction_on with
    | empty => simp
    | @insert x S hx ih =>
      have hprod := Finset.prod_le_one (s := S) (fun t _ => (ha t).1) (fun t _ => (ha t).2)
      calc 1 - ∏ t ∈ insert x S, a t = 1 - (a x * ∏ t ∈ S, a t) := by simp [Finset.prod_insert hx]
        _ = (1 - ∏ t ∈ S, a t) + (∏ t ∈ S, a t) * (1 - a x) := by ring
        _ ≤ (∑ t ∈ S, (1 - a t)) + (∏ t ∈ S, a t) * (1 - a x) := add_le_add_right ih _
        _ ≤ (∑ t ∈ S, (1 - a t)) + (1 - a x) := by
          linarith [mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr (ha x).2), one_mul (1 - a x)]
        _ = ∑ t ∈ insert x S, (1 - a t) := by simp [Finset.sum_insert hx, add_comm]
  have hjT : j ∈ T := by simp [T, hij.symm]
  have prod_split : ∏ t ∈ Finset.univ, a t = (∏ t ∈ T, a t) * a i := by
    simpa [T] using (Finset.prod_erase_mul Finset.univ (by simp) (f := a)).symm
  have hT_lt : ∏ t ∈ T, a t < 1 := by
    calc ∏ t ∈ T, a t = a j * ∏ t ∈ T.erase j, a t := (Finset.mul_prod_erase T (f := a) hjT).symm
      _ ≤ a j * 1 := mul_le_mul_of_nonneg_left
          (Finset.prod_le_one (s := T.erase j) (fun t _ => (ha t).1) (fun t _ => (ha t).2)) (ha j).1
      _ = a j := by simp
      _ < 1 := hj1
  have sum_split : ∑ t ∈ Finset.univ, (1 - a t) = (∑ t ∈ T, (1 - a t)) + (1 - a i) := by
    simpa [T] using (Finset.sum_erase_add Finset.univ (fun t => 1 - a t) (by simp)).symm
  calc 1 - ∏ t ∈ Finset.univ, a t = 1 - ((∏ t ∈ T, a t) * a i) := by rw [prod_split]
    _ = (1 - ∏ t ∈ T, a t) + (∏ t ∈ T, a t) * (1 - a i) := by ring
    _ < (∑ t ∈ T, (1 - a t)) + (1 - a i) := by
      linarith [union_bound T, mul_lt_mul_of_pos_right hT_lt (sub_pos.mpr hi1)]
    _ = ∑ t ∈ Finset.univ, (1 - a t) := sum_split.symm

/-- FRI Protocol Security (thm:fri_security_complete in blueprint):
The union of all k rounds' bad events has probability at most
`ε = ((3/2)·q + k)/|F| + k·exp(−η·q/n)`.

This is the main FRI soundness theorem: if the prover is cheating (some Xᵢ not close to V'ᵢ),
the verifier catches them with high probability.

FRI Structure at round i (from def:fri_subspace_structure):
- n := 2 * m_seq 0 is the initial dimension
- m_seq i := folded dimension at round i, satisfying m_seq i * 2^i = m_seq 0 (halving schedule)
- V_seq i: subspace of Fin (2 * m_seq i) → α (current round's codewords)
- V'_seq i: subspace of Fin (m_seq i) → α (folded codewords)
- X_seq i: the prover's matrix (m_seq i) × 2, being folded
- D_seq i: diagonal folding coefficients
- y_seq i: the prover's claimed next-round oracle

Per-round parameters (from lem:round_wise_error and lem:geometric_summation):
- q / 3^i: proximity parameter at round i (geometric decay)
- s i = η * (3/2)^i: sample size at round i (geometric growth)
- 2 * m_seq i = n / 2^i: ambient dimension at round i (halving)

The key hypotheses are:
1. h_m_seq: dimension halving schedule m_seq i * 2^i = m_seq 0
2. hT1, hT2: FRI subspace structure (V = T₁V' ⊕ T₂V' from def:fri_subspace_structure)
3. h_subspace_dist: 4 * (q / 3^i) < subspaceDistance(V'ᵢ) for unique decoding at round i
4. hG: Code has sufficient distance for folding checks
5. hs: Sample sizes follow the geometric growth schedule
6. Uniformity of random challenges and samples -/
theorem fri_security_complete
  {α : Type*} [Field α] [DecidableEq α]
  -- Basic parameters
  (k η q : ℕ)
  -- Probability space
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  -- m_seq i is the folded dimension at round i
  -- n = 2 * m_seq 0 is the initial dimension
  (m_seq : ℕ → ℕ)
  (hm0_pos : 0 < m_seq 0)
  -- FRI dimension schedule: dimension halves each round (m_seq i = m_seq 0 / 2^i)
  (h_m_seq : ∀ i < k, m_seq i * 2^i = m_seq 0)
  -- FRI subspace sequences
  (V_seq  : ∀ i : ℕ, Submodule α (Fin (m_seq i + m_seq i) → α))
  (V'_seq : ∀ i : ℕ, Submodule α (Fin (m_seq i) → α))
  -- Diagonal folding coefficients (from def:fri_subspace_structure)
  (D_seq : ∀ i : ℕ, Fin (m_seq i) → α)
  -- FRI structural hypotheses: V = T₁V' ⊕ T₂V' where T₁ = [I; I], T₂ = [D; -D]
  (hT1 : ∀ i < k, ∀ y ∈ V'_seq i,
      (fun j : Fin (m_seq i + m_seq i) => Fin.addCases y y j) ∈ V_seq i)
  (hT2 : ∀ i < k, ∀ y ∈ V'_seq i,
      (fun j : Fin (m_seq i + m_seq i) =>
        Fin.addCases (fun t => (D_seq i) t * y t) (fun t => - (D_seq i) t * y t) j) ∈ V_seq i)
  -- Subspace distance condition: 4 * q_i < d'(V'ᵢ) for unique decoding at round i
  -- where q_i = q / 3^i is the per-round proximity parameter
  (h_subspace_dist : ∀ i < k, 4 * (q / 3^i) < subspaceDistance (V'_seq i))
  -- Prover's matrices and oracles (what we're checking)
  -- NO closeness assumption needed! With the conjunction-based friRoundBadEvent,
  -- round_wise_error bounds the bad event unconditionally.
  (X_seq : ∀ i : ℕ, Matrix (Fin (m_seq i)) (Fin 2) α)
  (y_seq : ∀ i : ℕ, Fin (m_seq i + m_seq i) → α)
  -- Code matrices for folding checks (one per round due to dimension changes)
  (G_seq : ∀ i : ℕ, Matrix (Fin (m_seq i)) (Fin 2) α)
  (d : ℕ) -- Code distance (same for all rounds)
  (hd_le_m : d ≤ m_seq 0) -- Code distance bounded by initial dimension
  (hG : ∀ i < k, codeHasDistanceAtLeast (G_seq i) d)
  -- Random challenge selectors
  (r_seq : ∀ i : ℕ, Ω → Fin (m_seq i))
  (h_r_unif : ∀ i < k, ∀ j : Fin (m_seq i),
      μ {ω | r_seq i ω = j} = (1 : ENNReal) / (m_seq i : ENNReal))
  -- Sample sets for proximity checks
  -- Sample sizes follow the geometric growth: s i = η * (3/2)^i
  (s : ℕ → ℕ)
  (hs : ∀ i < k, (s i : ℝ) = (η : ℝ) * ((3 : ℝ) / 2) ^ i)
  -- Lambda condition: per-round proximity parameter bounded by dimension
  -- (q / 3^i + 1) ≤ (n / 2^i) where n = 2 * m_seq 0
  (h_lambda_le_one : ∀ i < k, (((q / 3^i : ℕ) + 1 : ℝ) ≤ ((2 * m_seq 0 / 2^i : ℕ) : ℝ)))
  -- Positivity of per-round dimensions
  (h_den_pos : ∀ i < k, 0 < (2 * m_seq 0) / 2^i)
  (S_seq : ∀ i : ℕ, Ω → Finset (Fin (m_seq i + m_seq i)))
  (h_S_card : ∀ i < k, ∀ ω, (S_seq i ω).card = s i)
  (hS_unif : ∀ i < k, ∀ A : Finset (Fin (m_seq i + m_seq i)), A.card = s i →
      μ {ω | S_seq i ω = A} = (1 : ENNReal) / ((Nat.choose (2 * m_seq i) (s i) : ℕ) : ENNReal)) :
  -- Conclusion: bad event probability is bounded
  -- Blueprint notation: ε = (3/2·q + k)/|F| + k·exp(-η·q/n)
  -- where 1/|F| = 1 - d/m (failure probability per challenge) and n = 2·m_seq 0
  let F : ℝ := (m_seq 0 : ℝ) / ((m_seq 0 : ℝ) - (d : ℝ))  -- Field size proxy: 1/F = 1 - d/m
  let n : ℝ := 2 * (m_seq 0 : ℝ)  -- Initial dimension
  μ (⋃ i ∈ Finset.range k,
      friRoundBadEvent (m_seq i) (V_seq i) (V'_seq i) (G_seq i) (r_seq i)
        (X_seq i) (D_seq i) (y_seq i) (q / 3^i) (S_seq i))
    ≤ ENNReal.ofReal
        (((3 : ℝ) / 2 * (q : ℝ) + (k : ℝ)) * (1 / F) +
          (k : ℝ) * Real.exp (-(η : ℝ) * (q : ℝ) / n)) :=
by
  simp only [one_div_div]; set nNat := 2 * m_seq 0
  let qR i := ((q / 3 ^ i : ℕ) + 1 : ℝ); let A i := qR i * (1 - (d : ℝ) / (m_seq 0 : ℝ))
  let B i := (1 - (qR i / ((nNat / 2 ^ i : ℕ) : ℝ))) ^ (s i); let p i := A i + B i
  have hqR_nonneg : ∀ i, 0 ≤ qR i := fun _ => by positivity
  have hA_nonneg : ∀ i, 0 ≤ A i := fun i => mul_nonneg (hqR_nonneg i) (sub_nonneg.mpr (div_le_one_of_le₀ (mod_cast hd_le_m) (by positivity)))
  have hB_nonneg : ∀ i < k, 0 ≤ B i := fun i hi => pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ (by simpa [qR, nNat] using h_lambda_le_one i hi) (by positivity))) _
  have hp_nonneg : ∀ i < k, 0 ≤ p i := fun i hi => add_nonneg (hA_nonneg i) (hB_nonneg i hi)
  have h_round_le : ∀ i < k, μ (friRoundBadEvent (m_seq i) (V_seq i) (V'_seq i) (G_seq i) (r_seq i) (X_seq i) (D_seq i) (y_seq i) (q / 3^i) (S_seq i)) ≤ ENNReal.ofReal (p i) := fun i hi => by
    have hmi_ne : m_seq i ≠ 0 := fun h => hm0_pos.ne' (by simpa [h] using (h_m_seq i hi).symm)
    have hmi_pos : 0 < (m_seq i : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hmi_ne)
    have hmi_le : (m_seq i : ℝ) ≤ (m_seq 0 : ℝ) := mod_cast by simpa [h_m_seq i hi] using Nat.le_mul_of_pos_right (m_seq i) (pow_pos (by decide : 0 < 2) i)
    have hfrac : (d : ℝ) / (m_seq 0 : ℝ) ≤ (d : ℝ) / (m_seq i : ℝ) := by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hmi_pos hmi_le) (by positivity)
    have h_nat_div : 2 * m_seq i = nNat / 2 ^ i := by
      have : (2 * m_seq i) * 2 ^ i = nNat := by simp [Nat.mul_assoc, h_m_seq i hi, nNat]
      have h_eq' : 2 ^ i * (2 * m_seq i) = nNat := by simp_all [Nat.mul_comm]
      exact Nat.mul_div_cancel_left (2 * m_seq i) (pow_pos (by decide : 0 < 2) i) ▸ congrArg (· / 2 ^ i) h_eq'
    have h_den_cast : ((2 * m_seq i : ℕ) : ℝ) = ((nNat / 2 ^ i : ℕ) : ℝ) := congrArg Nat.cast h_nat_div
    have hper : μ (friRoundBadEvent (m_seq i) (V_seq i) (V'_seq i) (G_seq i) (r_seq i) (X_seq i) (D_seq i) (y_seq i) (q / 3^i) (S_seq i)) ≤ ENNReal.ofReal (qR i * (1 - (d : ℝ) / (m_seq i : ℝ))) + ENNReal.ofReal ((1 - (qR i / ((2 * m_seq i : ℕ) : ℝ))) ^ (s i)) := by simpa [qR] using round_wise_error (V := V_seq i) (V' := V'_seq i) (D := D_seq i) (hT1 := hT1 i hi) (hT2 := hT2 i hi) (G := G_seq i) (hG := hG i hi) (μ := μ) (r := r_seq i) (h_unif := h_r_unif i hi) (X := X_seq i) (y := y_seq i) (q := q / 3^i) (h_q := h_subspace_dist i hi) (s := s i) (S := S_seq i) (h_card := h_S_card i hi) (hS_unif := hS_unif i hi)
    have hA' : ENNReal.ofReal (qR i * (1 - (d : ℝ) / (m_seq i : ℝ))) ≤ ENNReal.ofReal (A i) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sub_le_sub_left hfrac _) (hqR_nonneg i))
    have hB' : ENNReal.ofReal ((1 - (qR i / ((2 * m_seq i : ℕ) : ℝ))) ^ (s i)) ≤ ENNReal.ofReal (B i) := by simp [B, qR, h_den_cast]
    simpa [p, A, B, qR, ← ENNReal.ofReal_add (hA_nonneg i) (hB_nonneg i hi)] using hper.trans (add_le_add hA' hB')
  have h_sum : (∑ i ∈ Finset.range k, μ (friRoundBadEvent (m_seq i) (V_seq i) (V'_seq i) (G_seq i) (r_seq i) (X_seq i) (D_seq i) (y_seq i) (q / 3^i) (S_seq i))) ≤ ENNReal.ofReal (∑ i ∈ Finset.range k, p i) := (Finset.sum_le_sum fun i hi => h_round_le i (Finset.mem_range.mp hi)).trans (by rw [ENNReal.ofReal_sum_of_nonneg fun i hi => hp_nonneg i (Finset.mem_range.mp hi)])
  have h_geom := geometric_summation (k := k) (η := η) (q := q) (d := d) (m := m_seq 0) (n := nNat) (s := s) (hs := hs) (p := p) (h_pi := fun i _ => by simp [p, A, B, qR, nNat]) (h_d_le_m := hd_le_m) (h_den_pos := fun i hi => by simpa [nNat] using h_den_pos i hi) (h_lambda_le_one := fun i hi => by simpa [nNat] using h_lambda_le_one i hi)
  exact (measure_biUnion_finset_le _ _).trans (h_sum.trans (ENNReal.ofReal_le_ofReal (by simpa [(by field_simp : ((m_seq 0 : ℝ) - (d : ℝ)) / (m_seq 0 : ℝ) = 1 - (d : ℝ) / (m_seq 0 : ℝ)), nNat] using h_geom)))

end ZkLinalg
