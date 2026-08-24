import HeadComplexity.Separations.DistanceThreshold

set_option linter.style.header false

/-!
# Theorem B: an explicit linear additive gap `H* - deg±  = Ω(n)`

XOR-composition of `k` disjoint copies of `F_m`.  Under the all-left/all-right
partition the sign matrix is, up to reindexing and a global sign `(-1)^(k+1)`
(from `σ(XOR) = (-1)^(k+1) ∏ σ` in the `true ↦ +1` convention — affecting
neither spectral norm nor sign-rank), the Kronecker power of the base sign
matrix, and the Forster ratio is multiplicative (`specNorm_kronecker`), so the
sign-rank lower bound raises to `γ_m ^ k` while the threshold degree only
grows to `2 k`.  At `m = 29` this gives `H* - deg± ≥ n / 78.1 - 1`; at `m = 127` the
ratio `H* / deg± ≥ 1.908` (`audit/sources/EXPLICIT_GAP.md`, Theorem B).
-/

namespace HeadComplexity

/-- Block `j` of an input on `k * N` bits. -/
def blockOf {N k : ℕ} (z : Fin (k * N) → Bool) (j : Fin k) : Fin N → Bool :=
  fun i => z (finProdFinEquiv (j, i))

/-- XOR of `k` independent copies of `f` on disjoint blocks. -/
def xorPower (k : ℕ) {N : ℕ} (f : (Fin N → Bool) → Bool) :
    (Fin (k * N) → Bool) → Bool :=
  fun z => decide (Odd (Finset.univ.filter fun j : Fin k => f (blockOf z j)).card)

/-- The tensored distance-majority family `G_{m,k}` on `k * (m + m)` bits. -/
def tensorDistThreshold (m k : ℕ) : (Fin (k * (m + m)) → Bool) → Bool :=
  xorPower k (distThreshold m)

private theorem sign_xor_prod_helper {k : ℕ} (g : Fin k → Bool) :
    (if (decide (Odd (Finset.univ.filter fun j : Fin k => g j).card)) then (1 : ℝ) else -1)
      = (-1 : ℝ) ^ (k + 1) * ∏ j : Fin k, (if g j then (1 : ℝ) else -1) := by
  classical
  set T := Finset.univ.filter fun j : Fin k => g j = true
  set F := Finset.univ.filter fun j : Fin k => ¬ (g j = true)
  have hTF : Disjoint T F := Finset.disjoint_filter_filter_not Finset.univ Finset.univ (fun j => g j = true)
  have hTFU : T ∪ F = Finset.univ := by
    rw [← Finset.filter_union_filter_not_eq (fun j => g j = true) Finset.univ]
  have hcard : T.card + F.card = k := by
    rw [← Finset.card_union_of_disjoint hTF, hTFU, Finset.card_fin]
  have hprod : (∏ j : Fin k, (if g j then (1 : ℝ) else -1)) = (-1 : ℝ) ^ F.card := by
    have h1 : (∏ j ∈ T, (if g j then (1 : ℝ) else -1)) = 1 := by
      refine Finset.prod_eq_one (fun j hj => ?_)
      have hj' : g j = true := (Finset.mem_filter.mp hj).2
      simp [hj']
    have h2 : (∏ j ∈ F, (if g j then (1 : ℝ) else -1)) = (-1 : ℝ) ^ F.card := by
      have h2' : ∀ j ∈ F, (if g j then (1 : ℝ) else -1) = -1 := fun j hj => by
        have hj' : g j = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hj).2
        simp [hj']
      rw [Finset.prod_congr rfl h2', Finset.prod_const]
    have hsplit : (∏ j : Fin k, (if g j then (1 : ℝ) else -1)) =
        (∏ j ∈ T, (if g j then (1 : ℝ) else -1)) * (∏ j ∈ F, (if g j then (1 : ℝ) else -1)) := by
      rw [← Finset.prod_union hTF, hTFU]
    rw [hsplit, h1, h2, one_mul]
  rw [hprod]
  have hpow : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ F.card = (-1 : ℝ) ^ (T.card + 1) := by
    have h_exp : k + 1 + F.card = T.card + 1 + 2 * F.card := by omega
    have h_pow_eq : (-1 : ℝ) ^ (k + 1 + F.card) = (-1 : ℝ) ^ (T.card + 1 + 2 * F.card) := by rw [h_exp]
    rw [← pow_add, h_pow_eq, pow_add, pow_mul]
    have h_sq : ((-1 : ℝ) ^ 2) = 1 := by ring
    rw [h_sq, one_pow, mul_one]
  rw [hpow]
  by_cases h : Odd (Finset.univ.filter fun j : Fin k => g j).card
  · have h_dec : decide (Odd (Finset.univ.filter fun j : Fin k => g j).card) = true := decide_eq_true h
    rw [if_pos h_dec]
    obtain ⟨m, hm⟩ := h
    rw [hm]
    have h_exp2 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [h_exp2, pow_mul]
    have h_sq : ((-1 : ℝ) ^ 2) = 1 := by ring
    rw [h_sq, one_pow]
  · have h_dec : decide (Odd (Finset.univ.filter fun j : Fin k => g j).card) = false := decide_eq_false h
    rw [if_neg (by rw [h_dec]; norm_num)]
    have h_even : Even T.card := Nat.not_odd_iff_even.mp h
    obtain ⟨m, hm⟩ := h_even
    rw [hm]
    have h_exp : m + m + 1 = 2 * m + 1 := by omega
    rw [h_exp, pow_add, pow_mul]
    have h_sq : ((-1 : ℝ) ^ 2) = 1 := by ring
    rw [h_sq, one_pow, one_mul, pow_one]

open MvPolynomial in
private theorem blockSignRep_distThreshold_helper {m : ℕ} (hm : Odd m) {k : ℕ} (j : Fin k) :
    ∃ P : MvPolynomial (Fin (k * (m + m))) ℝ, P.totalDegree ≤ 2 ∧
      (∀ z : Fin (k * (m + m)) → Bool, eval (cubePoint z) P ≠ 0) ∧
      (∀ z : Fin (k * (m + m)) → Bool,
        (0 < eval (cubePoint z) P ↔ distThreshold m (blockOf z j) = true)) := by
  classical
  set P0 : MvPolynomial (Fin (m + m)) ℝ :=
    (∑ i : Fin m, (X (Fin.castAdd m i) + X (Fin.natAdd m i)
      - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))) - C ((m : ℝ) / 2) with hP0
  set σ : Fin (m + m) → Fin (k * (m + m)) := fun i => finProdFinEquiv (j, i)
  set P : MvPolynomial (Fin (k * (m + m))) ℝ := rename σ P0 with hP
  have hP0deg : P0.totalDegree ≤ 2 := by
    rw [hP0]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine totalDegree_finsetSum_le (fun i _ => ?_)
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_add _ _).trans
          (max_le (by rw [totalDegree_X]; norm_num) (by rw [totalDegree_X]; norm_num))
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X, totalDegree_X]
    · rw [totalDegree_C]; norm_num
  have hdeg : P.totalDegree ≤ 2 := (totalDegree_rename_le σ P0).trans hP0deg
  have hbool : ∀ a b : Bool,
      boolToReal a + boolToReal b - 2 * (boolToReal a * boolToReal b)
        = if a ≠ b then (1 : ℝ) else 0 := by
    intro a b; cases a <;> cases b <;> norm_num [boolToReal]
  have heval : ∀ z : Fin (k * (m + m)) → Bool,
      eval (cubePoint z) P = (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) - (m : ℝ) / 2 := by
    intro z
    rw [hP, eval_rename]
    have hcomp : (cubePoint z) ∘ σ = cubePoint (blockOf z j) := by
      ext i
      simp [cubePoint, σ, blockOf]
    rw [hcomp, hP0, map_sub, eval_C, map_sum]
    have hpair : ∀ i : Fin m,
        eval (cubePoint (blockOf z j)) (X (Fin.castAdd m i) + X (Fin.natAdd m i)
          - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))
          = if leftBits m m (blockOf z j) i ≠ rightBits m m (blockOf z j) i then (1 : ℝ) else 0 := by
      intro i
      simp only [map_sub, map_add, map_mul, eval_C, eval_X, cubePoint]
      exact hbool (blockOf z j (Fin.castAdd m i)) (blockOf z j (Fin.natAdd m i))
    rw [Finset.sum_congr rfl (fun i _ => hpair i)]
    congr 1
    rw [hammingDist, Finset.card_filter]
    have hsum_cast : (∑ i : Fin m, if leftBits m m (blockOf z j) i ≠ rightBits m m (blockOf z j) i then (1 : ℝ) else 0)
        = (∑ i : Fin m, if leftBits m m (blockOf z j) i ≠ rightBits m m (blockOf z j) i then 1 else 0 : ℕ) := by
      rw [Nat.cast_sum]
      congr 1 with i
      split_ifs <;> norm_num
    rw [hsum_cast]
  refine ⟨P, hdeg, fun z => ?_, fun z => ?_⟩
  · rw [heval z]
    intro h0
    have h_eq : (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) = (m : ℝ) / 2 := by linarith
    have h_two : 2 * (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) = (m : ℝ) := by linarith
    have h_even : Even m := by
      use hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j))
      have h_int : 2 * (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℤ) = (m : ℤ) := by exact_mod_cast h_two
      omega
    obtain ⟨k1, hk1⟩ := hm
    obtain ⟨k2, hk2⟩ := h_even
    omega
  · rw [heval z]
    rw [distThreshold, decide_eq_true_eq]
    constructor
    · intro h
      have h2 : (m : ℝ) / 2 < (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) := by linarith
      have h3 : (m : ℝ) < 2 * (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) := by linarith
      have h4 : m < 2 * hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) := by exact_mod_cast h3
      obtain ⟨k1, hk1⟩ := hm
      omega
    · intro h
      obtain ⟨k1, hk1⟩ := hm
      have h4 : m < 2 * hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) := by omega
      have h3 : (m : ℝ) < 2 * (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) := by exact_mod_cast h4
      linarith

open MvPolynomial in
/-- Degree upper bound: the product of the `k` quadratic block sign
polynomials (with the appropriate global sign) sign-represents `G_{m,k}`,
so `deg±(G_{m,k}) ≤ 2 k`. -/
theorem thresholdDegLE_tensorDistThreshold {m : ℕ} (hm : Odd m) (k : ℕ) :
    ThresholdDegLE (tensorDistThreshold m k) (2 * k) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨-1, by simp, fun z => ?_⟩
    simp [tensorDistThreshold, xorPower]
  · choose P_block hdeg_block hne_block hsign_block using fun j : Fin k => blockSignRep_distThreshold_helper hm j
    set Q : MvPolynomial (Fin (k * (m + m))) ℝ :=
      C ((-1 : ℝ) ^ (k + 1)) * ∏ j : Fin k, P_block j with hQ
    refine ⟨Q, ?_, ?_⟩
    · rw [hQ]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_finsetProd _ _).trans ?_
      have hsum : (∑ j : Fin k, (P_block j).totalDegree) ≤ ∑ j : Fin k, 2 :=
        Finset.sum_le_sum (fun j _ => hdeg_block j)
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
      linarith
    · intro z
      have h_decomp : ∀ j : Fin k, eval (cubePoint z) (P_block j) =
          |eval (cubePoint z) (P_block j)| * (if distThreshold m (blockOf z j) = true then (1 : ℝ) else -1) := by
        intro j
        have hne := hne_block j z
        have hiff := hsign_block j z
        by_cases hpos : 0 < eval (cubePoint z) (P_block j)
        · have hb : distThreshold m (blockOf z j) = true := hiff.mp hpos
          simp [abs_of_pos hpos, hb]
        · have hneg : eval (cubePoint z) (P_block j) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
          have hb : distThreshold m (blockOf z j) = false := by
            cases hbg : distThreshold m (blockOf z j)
            · rfl
            · exfalso; exact hpos (hiff.mpr hbg)
          simp [abs_of_neg hneg, hb]
      have hQ_eval : eval (cubePoint z) Q =
          (∏ j : Fin k, |eval (cubePoint z) (P_block j)|) *
          ((-1 : ℝ) ^ (k + 1) * ∏ j : Fin k, (if distThreshold m (blockOf z j) = true then (1 : ℝ) else -1)) := by
        rw [hQ, map_mul, eval_C, map_prod]
        have h_prod_eq : (∏ j : Fin k, eval (cubePoint z) (P_block j)) =
            (∏ j : Fin k, |eval (cubePoint z) (P_block j)|) *
            (∏ j : Fin k, (if distThreshold m (blockOf z j) = true then (1 : ℝ) else -1)) := by
          rw [← Finset.prod_mul_distrib]
          congr 1 with j
          exact h_decomp j
        rw [h_prod_eq]
        ring
      have h_pos_prod : 0 < ∏ j : Fin k, |eval (cubePoint z) (P_block j)| := by
        refine Finset.prod_pos (fun j _ => abs_pos.mpr (hne_block j z))
      have h_xor_sign := sign_xor_prod_helper (fun j => distThreshold m (blockOf z j))
      rw [hQ_eval]
      have h_sign_eq : ((-1 : ℝ) ^ (k + 1) * ∏ j : Fin k, (if distThreshold m (blockOf z j) = true then (1 : ℝ) else -1)) =
          if tensorDistThreshold m k z = true then (1 : ℝ) else -1 := by
        rw [tensorDistThreshold, xorPower]
        exact h_xor_sign.symm
      rw [h_sign_eq]
      constructor
      · intro h
        have h_mul_pos : 0 < if tensorDistThreshold m k z = true then (1 : ℝ) else -1 := by
          exact pos_of_mul_pos_right h (le_of_lt h_pos_prod)
        split_ifs at h_mul_pos with hG
        · exact hG
        · linarith
      · intro h
        simp [h, h_pos_prod]

/-- Model internals (PROOFS.md P1.3): a head family computing `f` transports
along a coordinate reindexing `e : Fin n' ≃ Fin n` to one computing
`f ∘ (· ∘ e.symm)`, by relabelling each head's `posEmbed` through `e` (all other
head data unchanged).  Matched positions have equal embeddings, hence equal
attention weights/values, and the finite sums reindex by `Equiv.optionCongr e`. -/
private theorem computableWithHeadsN_comp_equiv_forward {n n' H : ℕ} (e : Fin n' ≃ Fin n)
    (f : (Fin n → Bool) → Bool)
    (h : computableWithHeadsN n H f) :
    computableWithHeadsN n' H (fun z' => f (z' ∘ e.symm)) := by
  rcases h with ⟨d, Hs, w, τ, hw⟩
  let Hs' : HeadFamily n' d H := fun h =>
    { tokenEmbed := (Hs h).tokenEmbed
      posEmbed   := fun p' => (Hs h).posEmbed (p'.map e)
      WQ         := (Hs h).WQ
      WK         := (Hs h).WK
      WV         := (Hs h).WV }
  refine ⟨d, Hs', w, τ, ?_⟩
  intro z'
  have h_tok : ∀ (h : Fin H) (p' : SeqPos n'),
      Head.seqTok z' p' = Head.seqTok (z' ∘ e.symm) (p'.map e) := by
    intro h p'
    cases p' with
    | none => rfl
    | some i' =>
      simp only [Head.seqTok, Option.map_some, Function.comp_apply, Equiv.symm_apply_apply]
  have h_x : ∀ (h : Fin H) (p' : SeqPos n'),
      Head.x (Hs' h) z' p' = Head.x (Hs h) (z' ∘ e.symm) (p'.map e) := by
    intro h p'
    simp only [Head.x, h_tok h p']
    rfl
  have h_sigma : ∀ (h : Fin H) (p' : SeqPos n'),
      Head.sigma (Hs' h) z' p' = Head.sigma (Hs h) (z' ∘ e.symm) (p'.map e) := by
    intro h p'
    simp only [Head.sigma, h_x h p', h_x h none]
    rfl
  have h_val : ∀ (h : Fin H) (p' : SeqPos n'),
      Head.value (Hs' h) z' p' = Head.value (Hs h) (z' ∘ e.symm) (p'.map e) := by
    intro h p'
    simp only [Head.value, h_x h p']
    rfl
  have h_denom : ∀ (h : Fin H),
      Head.denominator (Hs' h) z' = Head.denominator (Hs h) (z' ∘ e.symm) := by
    intro h
    unfold Head.denominator
    simp_rw [h_sigma h]
    exact Equiv.sum_comp (Equiv.optionCongr e) (fun p => Head.sigma (Hs h) (z' ∘ e.symm) p)
  have h_num : ∀ (h : Fin H),
      Head.numerator (Hs' h) z' = Head.numerator (Hs h) (z' ∘ e.symm) := by
    intro h
    unfold Head.numerator
    simp_rw [h_sigma h, h_val h]
    exact Equiv.sum_comp (Equiv.optionCongr e)
      (fun p => Head.sigma (Hs h) (z' ∘ e.symm) p • Head.value (Hs h) (z' ∘ e.symm) p)
  have h_attn : ∀ (h : Fin H),
      Head.attnUpdate (Hs' h) z' = Head.attnUpdate (Hs h) (z' ∘ e.symm) := by
    intro h
    unfold Head.attnUpdate
    rw [h_denom h, h_num h]
  have h_sum : headFamilyAttnUpdate Hs' z' = headFamilyAttnUpdate Hs (z' ∘ e.symm) := by
    unfold headFamilyAttnUpdate
    simp_rw [h_attn]
  rw [h_sum]
  exact hw (z' ∘ e.symm)

/-- Model internals (PROOFS.md P1.3): head-computability is invariant under a
coordinate reindexing `e : Fin n' ≃ Fin n`. -/
theorem computableWithHeadsN_comp_equiv {n n' H : ℕ} (e : Fin n' ≃ Fin n)
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n H f ↔ computableWithHeadsN n' H (fun z' => f (z' ∘ e.symm)) := by
  constructor
  · exact computableWithHeadsN_comp_equiv_forward e f
  · intro h_comp'
    have h_fwd := computableWithHeadsN_comp_equiv_forward e.symm (fun z' => f (z' ∘ e.symm)) h_comp'
    have h_eq : (fun z => (fun z' => f (z' ∘ e.symm)) (z ∘ e.symm.symm)) = f := by
      ext z
      dsimp
      congr 1
      ext i
      simp
    rwa [h_eq] at h_fwd

/-- Head complexity `H*` is invariant under a coordinate reindexing
`e : Fin n' ≃ Fin n` (PROOFS.md P1.3): `HStar n' (f ∘ (· ∘ e.symm)) = HStar n f`.
This is the permutation-invariance lemma used silently in P8.1 to move to the
all-left/all-right partition. -/
theorem HStar_comp_equiv {n n' : ℕ} (e : Fin n' ≃ Fin n)
    (f : (Fin n → Bool) → Bool) :
    HStar n' (fun z' => f (z' ∘ e.symm)) = HStar n f := by
  unfold HStar
  have h_iff : (∃ k, computableWithHeadsN n' k (fun z' => f (z' ∘ e.symm))) ↔
      (∃ k, computableWithHeadsN n k f) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, (computableWithHeadsN_comp_equiv e f).mpr hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, (computableWithHeadsN_comp_equiv e f).mp hk⟩
  by_cases h1 : ∃ k, computableWithHeadsN n' k (fun z' => f (z' ∘ e.symm))
  · have h2 : ∃ k, computableWithHeadsN n k f := h_iff.mp h1
    rw [dif_pos h1, dif_pos h2]
    congr 1
    ext k
    exact (computableWithHeadsN_comp_equiv e f).symm
  · have h2 : ¬ (∃ k, computableWithHeadsN n k f) := fun h => h1 (h_iff.mpr h)
    rw [dif_neg h1, dif_neg h2]

/-- Standard block-reindexing equivalence mapping the all-`x`-blocks / all-`y`-blocks
layout `Fin (k·m + k·m)` to the interleaved-blocks layout `Fin (k·(m+m))`
(PROOFS.md P8.1).  Built from `finSumFinEquiv`, `finProdFinEquiv`,
`Equiv.prodSumDistrib`. -/
def tensorEquiv (m k : ℕ) : Fin (k * m + k * m) ≃ Fin (k * (m + m)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
      ((Equiv.prodSumDistrib (Fin k) (Fin m) (Fin m)).symm.trans
        ((Equiv.prodCongr (Equiv.refl (Fin k)) finSumFinEquiv).trans
          finProdFinEquiv)))

/-- The tensored family under the all-left / all-right input partition (PROOFS.md
P8.1): `G̃ z' := G (z' ∘ E.symm)` reads its first `k·m` bits as the `k` x-halves
and its last `k·m` bits as the `k` y-halves. -/
def tensorDistThreshold_reindexed (m k : ℕ) : (Fin (k * m + k * m) → Bool) → Bool :=
  fun z' => tensorDistThreshold m k (z' ∘ (tensorEquiv m k).symm)

/-- Arithmetic tail of the tensored Forster bound (PROOFS.md P8.3): once Forster
(`forster`) together with `specNorm (⊗^k S₁) = (2C)^k` and the index-type card
`N = 2^{k·m}` yield `2^{k·m} ≤ r · (2C)^k` (with `C := C(m-1,(m-1)/2)` and
`r := signRank S_k`), dividing by the positive `(2C)^k` gives
`forsterRatio m ^ k ≤ r`, using `forsterRatio m = 2^(m-1)/C = 2^m/(2C)` (valid for
`m ≥ 1`, hence `2^{k·m} = (2^m)^k` and `(2^m/(2C))^k = forsterRatio m ^ k`).  This
isolates the elementary real-arithmetic tail from the Kronecker spectral core. -/
theorem forsterRatio_pow_le_of_forster {m k r : ℕ} (hm : 1 ≤ m)
    (hle : (2 : ℝ) ^ (k * m) ≤ (r : ℝ) * (2 * ((m - 1).choose ((m - 1) / 2) : ℝ)) ^ k) :
    forsterRatio m ^ k ≤ (r : ℝ) := by
  sorry

/-- **Kronecker/Forster core** (PROOFS.md P8.1–P8.3): under the all-left/all-right
partition the sign matrix `S_k := signMatrix (k·m) (k·m) G̃` is `(-1)^(k+1)` times a
reindexed `k`-fold Kronecker power of the base sign matrix `S₁`, so
`signRank S_k = signRank (⊗^k S₁)` (`signRank_reindex`, `signRank_neg`) and
`specNorm (⊗^k S₁) = (2C)^k` (`specNorm_kronecker`); Forster (`forster`) with
`N = 2^{km}` then gives `forsterRatio m ^ k ≤ signRank S_k`. -/
theorem forsterRatio_pow_le_signRank_tensor {m : ℕ} (hm : Odd m) {k : ℕ} (hk : 1 ≤ k) :
    forsterRatio m ^ k ≤
      (signRank (signMatrix (k * m) (k * m) (tensorDistThreshold_reindexed m k)) : ℝ) := by
  sorry

/-- **Sign-rank bridge for the reindexed tensored family** (PROOFS.md P8.3): `G̃`
is nonconstant for `m ≥ 1`, `k ≥ 1` (set exactly one block to a distance-majority
input, giving an odd XOR-count `1`, versus the all-false input with count `0`), so
`1 ≤ H*` and the bridge `signRank_le_pow_HStar` applies.  Both hypotheses are
essential: at `k = 0` (or `m = 0`) the family is constant, `H* = 0`, and
`signRank = 1 > 2^1 - 2 = 0`. -/
theorem signRank_le_pow_HStar_tensor {m k : ℕ} (hm : Odd m) (hk : 1 ≤ k) :
    signRank (signMatrix (k * m) (k * m) (tensorDistThreshold_reindexed m k)) ≤
      2 ^ (HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) + 1) - 2 := by
  haveI : NeZero k := ⟨by omega⟩
  apply signRank_le_pow_HStar (k * m) (k * m) (tensorDistThreshold_reindexed m k)
  have hHeq : HStar (k * m + k * m) (tensorDistThreshold_reindexed m k)
      = HStar (k * (m + m)) (tensorDistThreshold m k) :=
    HStar_comp_equiv (tensorEquiv m k) (tensorDistThreshold m k)
  rw [hHeq]
  have hm1 : 1 ≤ m := by have := Nat.odd_iff.mp hm; omega
  -- `distThreshold` on the all-false block is `false`; on the majority pattern `true`.
  have hdt_false : distThreshold m (fun _ : Fin (m + m) => false) = false := by
    have hlb : leftBits m m (fun _ : Fin (m + m) => false) = fun _ => false := rfl
    have hrb : rightBits m m (fun _ : Fin (m + m) => false) = fun _ => false := rfl
    simp only [distThreshold, hlb, hrb, hammingDist_self]
    simp only [decide_eq_false_iff_not, not_le]; omega
  set patt : Fin (m + m) → Bool := blockJoin (fun _ => true) (fun _ => false) with hpatt
  have hdt_patt : distThreshold m patt = true := by
    rw [hpatt]
    simp only [distThreshold, leftBits_blockJoin, rightBits_blockJoin]
    have hd : hammingDist (fun _ : Fin m => true) (fun _ : Fin m => false) = m := by
      unfold hammingDist
      rw [Finset.filter_true_of_mem (fun i _ => by simp)]; simp
    rw [hd]; simp only [decide_eq_true_eq]; omega
  -- Witness input `z1`: block `0` is the majority pattern, all other blocks are false.
  set z1 : Fin (k * (m + m)) → Bool :=
    fun p => if (finProdFinEquiv.symm p).1 = 0 then patt (finProdFinEquiv.symm p).2 else false
    with hz1def
  have hboj_all : ∀ (j : Fin k) (i : Fin (m + m)),
      blockOf z1 j i = if j = 0 then patt i else false := by
    intro j i
    show z1 (finProdFinEquiv (j, i)) = _
    simp only [hz1def, Equiv.symm_apply_apply]
  have hbo_false : ∀ j : Fin k,
      blockOf (fun _ : Fin (k * (m + m)) => false) j = fun _ => false := fun _ => rfl
  -- XOR-count is `1` at `z1` (only block `0`), hence `G z1 = true`.
  have hG1 : tensorDistThreshold m k z1 = true := by
    simp only [tensorDistThreshold, xorPower, decide_eq_true_eq]
    have hfilter : (Finset.univ.filter fun j : Fin k => distThreshold m (blockOf z1 j)) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hjt
        by_contra hj0
        have hbo : blockOf z1 j = fun _ => false := by
          funext i; rw [hboj_all j i, if_neg hj0]
        rw [hbo, hdt_false] at hjt; exact absurd hjt (by simp)
      · intro hj0; subst hj0
        have hbo : blockOf z1 (0 : Fin k) = patt := by
          funext i; rw [hboj_all 0 i, if_pos rfl]
        rw [hbo]; exact hdt_patt
    rw [hfilter, Finset.card_singleton]; decide
  -- XOR-count is `0` at the all-false input, hence `G = false`.
  have hG0 : tensorDistThreshold m k (fun _ => false) = false := by
    simp only [tensorDistThreshold, xorPower, decide_eq_false_iff_not]
    have hfilter : (Finset.univ.filter fun j : Fin k =>
        distThreshold m (blockOf (fun _ : Fin (k * (m + m)) => false) j)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _
      rw [hbo_false j, hdt_false]; simp
    rw [hfilter]; simp
  rcases Nat.eq_zero_or_pos (HStar (k * (m + m)) (tensorDistThreshold m k)) with h0 | hpos
  · exfalso
    have hconst := (HStar_eq_zero_iff (tensorDistThreshold m k)).mp h0 z1 (fun _ => false)
    rw [hG1, hG0] at hconst
    exact absurd hconst (by simp)
  · exact hpos

/-- **Theorem B, lower half**: the Forster ratio tensors, so
`γ_m ^ k ≤ 2 ^ (H* + 1) - 2` for the `k`-fold XOR power.  (Route: the sign
matrix under the all-left/all-right partition is a reindexed Kronecker power
up to the global sign `(-1)^(k+1)`, which preserves spectral norm and
sign-rank; apply `specNorm_kronecker`, `signRank_reindex`, `forster`, and the
sign-rank bridge.  Assembled from `HStar_comp_equiv` (P1.3),
`forsterRatio_pow_le_signRank_tensor` (P8.1–P8.3), and
`signRank_le_pow_HStar_tensor` (P8.3).) -/
theorem theoremB_HStar {m : ℕ} (hm : Odd m) {k : ℕ} (hk : 1 ≤ k) :
    forsterRatio m ^ k ≤
      (2 : ℝ) ^ (HStar (k * (m + m)) (tensorDistThreshold m k) + 1) - 2 := by
  have h_eq : HStar (k * (m + m)) (tensorDistThreshold m k) =
      HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) :=
    (HStar_comp_equiv (tensorEquiv m k) (tensorDistThreshold m k)).symm
  rw [h_eq]
  have h1 := forsterRatio_pow_le_signRank_tensor hm hk
  have h2 := signRank_le_pow_HStar_tensor (m := m) (k := k) hm hk
  have h_two_le : 2 ≤ 2 ^ (HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2_R : (signRank (signMatrix (k * m) (k * m) (tensorDistThreshold_reindexed m k)) : ℝ) ≤
      (2 : ℝ) ^ (HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) + 1) - 2 := by
    have h2_cast : ((signRank (signMatrix (k * m) (k * m)
        (tensorDistThreshold_reindexed m k)) : ℕ) : ℝ) ≤
        ((2 ^ (HStar (k * m + k * m) (tensorDistThreshold_reindexed m k) + 1) - 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr h2
    rw [Nat.cast_sub h_two_le, Nat.cast_pow, Nat.cast_two] at h2_cast
    exact h2_cast
  exact h1.trans h2_R

/-- **XOR sign encoding** (PROOFS.md P8.2): with the `signMatrix` encoding
`e(true) = 1`, `e(false) = -1`, the sign of an XOR of `k` bits is
`(-1)^(k+1) · ∏ⱼ e(bⱼ)`.  This is the global-sign bookkeeping that lets the
product of the `k` block sign polynomials sign-represent the tensored family
(`thresholdDegLE_tensorDistThreshold`).  Induction on `k`: `k = 0` gives `-1 =
-1`; the step is `e(b ⊕ c) = -e(b)·e(c)`.  Equivalently `∏ⱼ e(gⱼ) =
(-1) ^ (#false)`, and `#true + #false = k`. -/
theorem sign_xor_prod {k : ℕ} (g : Fin k → Bool) :
    (if (decide (Odd (Finset.univ.filter fun j : Fin k => g j).card)) then (1 : ℝ) else -1)
      = (-1 : ℝ) ^ (k + 1) * ∏ j : Fin k, (if g j then (1 : ℝ) else -1) := by
  have hsplit := (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin k))
    (fun j => g j = true) (fun j => if g j then (1 : ℝ) else -1)).symm
  have hpos : ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => g j = true),
      (if g j then (1 : ℝ) else -1) = 1 := by
    have h1 : ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => g j = true),
        (if g j then (1 : ℝ) else -1) =
        ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => g j = true), (1 : ℝ) := by
      refine Finset.prod_congr rfl (fun x hx => ?_)
      have hg : g x = true := (Finset.mem_filter.mp hx).2
      simp [hg]
    rw [h1, Finset.prod_const_one]
  have hneg : ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => ¬(g j = true)),
      (if g j then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ ((Finset.univ : Finset (Fin k)).filter (fun j => ¬(g j = true))).card := by
    have h1 : ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => ¬(g j = true)),
        (if g j then (1 : ℝ) else -1) =
        ∏ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => ¬(g j = true)), (-1 : ℝ) := by
      refine Finset.prod_congr rfl (fun x hx => ?_)
      have hg : g x = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hx).2
      simp [hg]
    rw [h1, Finset.prod_const]
  rw [hsplit, hpos, one_mul, hneg]
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun j => g j = true)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  set n_true := ((Finset.univ : Finset (Fin k)).filter (fun j => g j = true)).card
  set n_false := ((Finset.univ : Finset (Fin k)).filter (fun j => ¬(g j = true))).card
  have hk : k = n_true + n_false := hcard.symm
  rw [hk]
  have hpow_eq : (-1 : ℝ) ^ (n_true + n_false + 1) * (-1 : ℝ) ^ n_false =
      (-1 : ℝ) ^ (n_true + 1) := by
    have h1 : (-1 : ℝ) ^ (n_true + n_false + 1) * (-1 : ℝ) ^ n_false =
        (-1 : ℝ) ^ (n_true + 1 + 2 * n_false) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h1, pow_add]
    have h_even : Even (2 * n_false) := even_two_mul n_false
    rw [h_even.neg_one_pow, mul_one]
  rw [hpow_eq]
  change (if (decide (Odd n_true)) then (1 : ℝ) else -1) = (-1 : ℝ) ^ (n_true + 1)
  by_cases h : Odd n_true
  · rw [decide_eq_true h, if_pos rfl]
    have h_even : Even (n_true + 1) := h.add_one
    exact h_even.neg_one_pow.symm
  · rw [decide_eq_false h, if_neg Bool.false_ne_true]
    have h_even : Even n_true := Nat.not_odd_iff_even.mp h
    have h_odd : Odd (n_true + 1) := h_even.add_one
    exact h_odd.neg_one_pow.symm

open MvPolynomial in
/-- **Per-block strict sign representation** (PROOFS.md P8.4): the block-`j` copy
of the P7.1 quadratic `Δ - m/2`, its variables renamed to block `j` along
`i ↦ finProdFinEquiv (j, i)`, sign-represents `z ↦ distThreshold m (blockOf z j)`
with **nonzero** cube values (half-integers for odd `m`) and total degree `≤ 2`.
Route: take the explicit polynomial of `thresholdDegLE_distThreshold` and apply
`MvPolynomial.rename (fun i => finProdFinEquiv (j, i))`; `eval_rename` rewrites
the cube value as the block's `hammingDist - m/2`, an element of `ℤ + 1/2`. -/
theorem blockSignRep_distThreshold {m : ℕ} (hm : Odd m) {k : ℕ} (j : Fin k) :
    ∃ P : MvPolynomial (Fin (k * (m + m))) ℝ, P.totalDegree ≤ 2 ∧
      (∀ z : Fin (k * (m + m)) → Bool, eval (cubePoint z) P ≠ 0) ∧
      (∀ z : Fin (k * (m + m)) → Bool,
        (0 < eval (cubePoint z) P ↔ distThreshold m (blockOf z j) = true)) := by
  set P_base : MvPolynomial (Fin (m + m)) ℝ :=
    (∑ i : Fin m, (X (Fin.castAdd m i) + X (Fin.natAdd m i)
      - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))) - C ((m : ℝ) / 2) with hP_base
  let σ : Fin (m + m) → Fin (k * (m + m)) := fun i => finProdFinEquiv (j, i)
  set P := rename σ P_base with hP
  have heval_base : ∀ x : Fin (m + m) → Bool,
      eval (cubePoint x) P_base = (hammingDist (leftBits m m x) (rightBits m m x) : ℝ) - (m : ℝ) / 2 := by
    intro x
    have hbool : ∀ a b : Bool,
        boolToReal a + boolToReal b - 2 * (boolToReal a * boolToReal b)
          = if a ≠ b then (1 : ℝ) else 0 := by
      intro a b; cases a <;> cases b <;> norm_num [boolToReal]
    have hpair : ∀ i : Fin m,
        eval (cubePoint x) (X (Fin.castAdd m i) + X (Fin.natAdd m i)
          - C 2 * (X (Fin.castAdd m i) * X (Fin.natAdd m i)))
          = if leftBits m m x i ≠ rightBits m m x i then (1 : ℝ) else 0 := by
      intro i
      simp only [map_sub, map_add, map_mul, eval_C, eval_X, cubePoint]
      exact hbool (x (Fin.castAdd m i)) (x (Fin.natAdd m i))
    rw [hP_base, map_sub, eval_C, map_sum]
    congr 1
    unfold hammingDist
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hpair i)
  have heval : ∀ z : Fin (k * (m + m)) → Bool,
      eval (cubePoint z) P = (hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j)) : ℝ) - (m : ℝ) / 2 := by
    intro z
    rw [hP, eval_rename]
    exact heval_base (blockOf z j)
  refine ⟨P, ?_, ?_, ?_⟩
  · -- degree ≤ 2
    rw [hP]
    refine (totalDegree_rename_le σ P_base).trans ?_
    rw [hP_base]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine totalDegree_finsetSum_le (fun i _ => ?_)
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_add _ _).trans
          (max_le (by rw [totalDegree_X]; norm_num) (by rw [totalDegree_X]; norm_num))
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X, totalDegree_X]
    · rw [totalDegree_C]; norm_num
  · -- non-zero
    intro z
    rw [heval]
    set D := hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j))
    intro hzero
    have h2D : 2 * (D : ℝ) = m := by linarith [hzero]
    have h2D' : 2 * D = m := by exact_mod_cast h2D
    have hodd := Nat.odd_iff.mp hm
    omega
  · -- sign representation
    intro z
    rw [heval, distThreshold, decide_eq_true_eq]
    set D := hammingDist (leftBits m m (blockOf z j)) (rightBits m m (blockOf z j))
    have hodd := Nat.odd_iff.mp hm
    constructor
    · intro h
      have hmD : (m : ℝ) < 2 * (D : ℝ) := by linarith
      have hmD' : m < 2 * D := by exact_mod_cast hmD
      omega
    · intro h
      have hmD' : m < 2 * D := by omega
      have hmD : (m : ℝ) < 2 * (D : ℝ) := by exact_mod_cast hmD'
      linarith

/-- **Theorem B** (`audit/sources/EXPLICIT_GAP.md`): explicit additive gap linear in
the input length: `H*(G_{m,k}) - deg±(G_{m,k}) ≥ k (log₂ γ_m - 2) - 1`,
positive for every odd `m ≥ 13`. -/
theorem theoremB_gap {m : ℕ} (hm : Odd m) (k : ℕ) :
    (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1 ≤
      (HStar (k * (m + m)) (tensorDistThreshold m k) : ℝ) -
        (thresholdDeg (tensorDistThreshold m k) : ℝ) := by
  -- Degree stays `≤ 2k`, and `thresholdDeg ≤ H*` always.
  have hdeg : thresholdDeg (tensorDistThreshold m k) ≤ 2 * k :=
    thresholdDeg_le_of (thresholdDegLE_tensorDistThreshold hm k)
  have hdegR : (thresholdDeg (tensorDistThreshold m k) : ℝ) ≤ 2 * (k : ℝ) := by
    exact_mod_cast hdeg
  have hDH : thresholdDeg (tensorDistThreshold m k)
      ≤ HStar (k * (m + m)) (tensorDistThreshold m k) := thresholdDeg_le_HStar _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: LHS `= -1 ≤ 0 ≤` RHS, since `thresholdDeg ≤ H*`.
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    have hDHR : (thresholdDeg (tensorDistThreshold m 0) : ℝ)
        ≤ (HStar (0 * (m + m)) (tensorDistThreshold m 0) : ℝ) := by exact_mod_cast hDH
    linarith
  · -- `k ≥ 1`: `γ^k ≤ 2^(H+1) - 2 < 2^(H+1)`, take `logb 2`.
    have hB := theoremB_HStar hm hk
    set H := HStar (k * (m + m)) (tensorDistThreshold m k) with hHdef
    have hγ : 0 < forsterRatio m := forsterRatio_pos m
    have hγk : 0 < forsterRatio m ^ k := pow_pos hγ k
    have hlt : forsterRatio m ^ k < (2 : ℝ) ^ (H + 1) := by linarith [hB]
    have hlog : (k : ℝ) * Real.logb 2 (forsterRatio m) < (H : ℝ) + 1 := by
      have h1 : Real.logb 2 (forsterRatio m ^ k) < Real.logb 2 ((2 : ℝ) ^ (H + 1)) :=
        Real.logb_lt_logb (by norm_num) hγk hlt
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h1
      push_cast at h1
      linarith [h1]
    have hexpand : (k : ℝ) * (Real.logb 2 (forsterRatio m) - 2) - 1
        = (k : ℝ) * Real.logb 2 (forsterRatio m) - 2 * (k : ℝ) - 1 := by ring
    rw [hexpand]
    linarith [hlog, hdegR]

end HeadComplexity
