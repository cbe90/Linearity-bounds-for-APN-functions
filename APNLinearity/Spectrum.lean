module

public import APNLinearity.Fourier

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Fourier
noncomputable section

theorem nonzero_index {n : ℕ} (hn : 1 ≤ n) : ∃ b : BinarySpace n, b ≠ 0 := by
  refine ⟨fun _ => 1, ?_⟩
  intro h
  have := congrFun h ⟨0, hn⟩
  exact one_ne_zero this

theorem coefficientIndices_nonempty {n : ℕ} (hn : 1 ≤ n) :
    (nonzeroWalshIndices n).Nonempty := by
  obtain ⟨b, hb⟩ := nonzero_index hn
  exact ⟨(0, b), by simp [nonzeroWalshIndices, hb]⟩

theorem mem_affineDistances {n : ℕ} (F : VectorialFunction n) (d : ℕ) :
    d ∈ affineDistances F ↔ ∃ b, b ≠ 0 ∧ ∃ a c,
      hammingDistance (component F b) (affineBoolean a c) = d := by
  classical
  constructor
  · rintro hd
    obtain ⟨⟨⟨a, b⟩, c⟩, hm, he⟩ := Finset.mem_image.mp hd
    have hb : b ≠ 0 := by simpa [nonzeroWalshIndices] using (Finset.mem_product.mp hm).1
    exact ⟨b, hb, a, c, he⟩
  · rintro ⟨b, hb, a, c, he⟩
    exact Finset.mem_image.mpr ⟨((a, b), c), by simp [nonzeroWalshIndices, hb], he⟩

theorem distance_le_size {n : ℕ} (f g : BooleanFunction n) : hammingDistance f g ≤ spaceSize n := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp only [Finset.card_univ, card_binary])

theorem fold_min_spec (B : ℕ) (s : Finset ℕ) :
    s.fold min B id ≤ B ∧ (∀ d ∈ s, s.fold min B id ≤ d) ∧
      (s.fold min B id = B ∨ s.fold min B id ∈ s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.fold_insert ha]
    simp only [id_eq] at *
    rcases ih with ⟨hB, hd, hm⟩
    by_cases h : a ≤ s.fold min B (fun x => x)
    · rw [min_eq_left h]
      refine ⟨h.trans hB, ?_, Or.inr (Finset.mem_insert_self _ _)⟩
      intro d hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact le_rfl
      · exact h.trans (hd d hmem)
    · rw [min_eq_right (le_of_not_ge h)]
      refine ⟨hB, ?_, ?_⟩
      · intro d hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact le_of_not_ge h
        · exact hd d hmem
      · exact hm.imp_right (fun hs => Finset.mem_insert_of_mem hs)

theorem nonlinearity_le_distance {n : ℕ} (F : VectorialFunction n) (b : BinarySpace n)
    (hb : b ≠ 0) (a : BinarySpace n) (c : Bit) :
    nonlinearity F ≤ hammingDistance (component F b) (affineBoolean a c) := by
  apply (fold_min_spec (spaceSize n) (affineDistances F)).2.1
  exact (mem_affineDistances _ _).2 ⟨b, hb, a, c, rfl⟩

theorem distance_attained : ∀ (n : ℕ), 1 ≤ n → ∀ F : VectorialFunction n,
    ∃ b : BinarySpace n, b ≠ 0 ∧ ∃ a c,
      hammingDistance (component F b) (affineBoolean a c) = nonlinearity F := by
  intro n hn F
  obtain ⟨b, hb⟩ := nonzero_index hn
  have hmem : hammingDistance (component F b) (affineBoolean 0 0) ∈ affineDistances F :=
    (mem_affineDistances _ _).2 ⟨b, hb, 0, 0, rfl⟩
  apply (mem_affineDistances F (nonlinearity F)).1
  rcases (fold_min_spec (spaceSize n) (affineDistances F)).2.2 with h | h
  · have hle := nonlinearity_le_distance F b hb 0 0
    have hge := distance_le_size (component F b) (affineBoolean 0 0)
    have he : hammingDistance (component F b) (affineBoolean 0 0) = nonlinearity F := by
      change nonlinearity F = spaceSize n at h
      omega
    exact he ▸ hmem
  · exact h


theorem coefficientIndices_card (n : ℕ) :
    (nonzeroWalshIndices n).card = spaceSize n * (spaceSize n - 1) := by
  classical
  have he : nonzeroWalshIndices n = (Finset.univ : Finset (BinarySpace n)) ×ˢ Finset.univ.erase 0 := by
    ext u
    simp [nonzeroWalshIndices]
  rw [he, Finset.card_product]
  simp only [Finset.card_univ, Finset.card_erase_of_mem (Finset.mem_univ _), card_binary]

theorem sortedIndices_perm {n : ℕ} (F : VectorialFunction n) :
    (sortedIndices F).Perm (nonzeroWalshIndices n).toList := List.mergeSort_perm _ _

theorem sortedSpectrum_length {n : ℕ} (F : VectorialFunction n) :
    (orderedWalshMagnitudes F).length = spaceSize n * (spaceSize n - 1) := by
  simp only [orderedWalshMagnitudes, Multiset.length_sort, Multiset.card_map,
    ← Finset.card_def, coefficientIndices_card]

theorem sortedSpectrum_pairwise {n : ℕ} (F : VectorialFunction n) :
    (orderedWalshMagnitudes F).Pairwise (fun a b => b ≤ a) :=
  Multiset.pairwise_sort _ _

/-- Sorting indices enumerates the same multiset, retaining all ties. -/
theorem orderedWalshMagnitudes_eq_map {n : ℕ} (F : VectorialFunction n) :
    orderedWalshMagnitudes F = (sortedIndices F).map (fun u => (walshAt F u).natAbs) := by
  have hs : ((sortedIndices F).map (fun u => (walshAt F u).natAbs)).Pairwise
      (fun a b => b ≤ a) := by
    apply List.pairwise_map.mpr
    have h := List.pairwise_mergeSort
      (le := fun u v => decide ((walshAt F v).natAbs ≤ (walshAt F u).natAbs))
      (by intro a b c h₁ h₂; simpa using
        (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (nonzeroWalshIndices n).toList
    simpa only [sortedIndices, decide_eq_true_eq] using h
  have hp : ((sortedIndices F).map (fun u => (walshAt F u).natAbs)).Perm
      (orderedWalshMagnitudes F) := by
    apply Multiset.coe_eq_coe.mp
    have hi := Multiset.coe_eq_coe.mpr (sortedIndices_perm F)
    simpa [orderedWalshMagnitudes, walshAt] using
      congrArg (Multiset.map (fun u => (walshAt F u).natAbs)) hi
  exact (hp.eq_of_pairwise' hs (sortedSpectrum_pairwise F)).symm

theorem mem_sortedSpectrum {n : ℕ} (F : VectorialFunction n) (d : ℕ) :
    d ∈ orderedWalshMagnitudes F ↔
      ∃ u ∈ nonzeroWalshIndices n, (walshAt F u).natAbs = d := by
  classical
  rw [orderedWalshMagnitudes_eq_map]
  simp only [List.mem_map, (sortedIndices_perm F).mem_iff, Finset.mem_toList]

theorem kthLinearity_eq_getD {n : ℕ} (F : VectorialFunction n) (k : ℕ) :
    kthLinearity F k =
      if k = 0 then 0 else ((orderedWalshMagnitudes F).getD (k - 1) 0 : ℝ) := by
  unfold kthLinearity
  dsimp only
  split_ifs with hk hi
  · rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · have hlen : (orderedWalshMagnitudes F).length ≤ k - 1 := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

theorem ranked_coefficient_attained {n : ℕ} (F : VectorialFunction n) (k : ℕ)
    (hk : 1 ≤ k) (hK : k ≤ spaceSize n * (spaceSize n - 1)) :
    ∃ u ∈ nonzeroWalshIndices n, kthLinearity F k = ((walshAt F u).natAbs : ℝ) := by
  have hi : k - 1 < (orderedWalshMagnitudes F).length := by
    rw [sortedSpectrum_length]; omega
  obtain ⟨u, hu, he⟩ := (mem_sortedSpectrum F _).1 (List.getElem_mem hi)
  refine ⟨u, hu, ?_⟩
  simp only [kthLinearity, show k ≠ 0 by omega, ↓reduceIte, hi]
  exact congrArg (fun d : ℕ => (d : ℝ)) he.symm

theorem linearity_eq_sup {n : ℕ} (F : VectorialFunction n) :
    linearity F = (((nonzeroWalshIndices n).sup (fun u => (walshAt F u).natAbs) : ℕ) : ℝ) := by
  cases he : orderedWalshMagnitudes F with
  | nil =>
    have hz : (nonzeroWalshIndices n).sup (fun u => (walshAt F u).natAbs) = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro u hu
      have hm := (mem_sortedSpectrum F _).2 ⟨u, hu, rfl⟩
      simp [he] at hm
    simp [linearity, kthLinearity, he, hz]
  | cons x xs =>
    have hx : x ∈ orderedWalshMagnitudes F := by rw [he]; simp
    obtain ⟨u, hu, huval⟩ := (mem_sortedSpectrum F x).1 hx
    have hlo : x ≤ (nonzeroWalshIndices n).sup (fun u => (walshAt F u).natAbs) := by
      rw [← huval]
      exact Finset.le_sup (f := fun u => (walshAt F u).natAbs) hu
    have hsorted := sortedSpectrum_pairwise F
    rw [he, List.pairwise_cons] at hsorted
    have hup : (nonzeroWalshIndices n).sup (fun u => (walshAt F u).natAbs) ≤ x := by
      apply Finset.sup_le
      intro v hv
      have hm := (mem_sortedSpectrum F _).2 ⟨v, hv, rfl⟩
      rw [he, List.mem_cons] at hm
      rcases hm with h | h
      · exact h.le
      · exact hsorted.1 _ h
    have hmax := le_antisymm hlo hup
    simp [linearity, kthLinearity, he, ← hmax]

theorem walsh_le_linearity {n : ℕ} (F : VectorialFunction n)
    (a b : BinarySpace n) (hb : b ≠ 0) :
    ((walsh (component F b) a).natAbs : ℝ) ≤ linearity F := by
  rw [linearity_eq_sup]
  exact_mod_cast (Finset.le_sup (s := nonzeroWalshIndices n)
    (f := fun u => (walshAt F u).natAbs) (b := (a,b))
    (by simp [nonzeroWalshIndices, hb]))

theorem linearity_attained {n : ℕ} (hn : 1 ≤ n) (F : VectorialFunction n) :
    ∃ a b, b ≠ 0 ∧ linearity F = ((walsh (component F b) a).natAbs : ℝ) := by
  obtain ⟨⟨a,b⟩, hu, he⟩ := Finset.exists_mem_eq_sup (nonzeroWalshIndices n)
    (coefficientIndices_nonempty hn) (fun u => (walshAt F u).natAbs)
  refine ⟨a,b,by simpa [nonzeroWalshIndices] using hu, ?_⟩
  rw [linearity_eq_sup, he]
  rfl

theorem exists_sign_abs (w : ℤ) : ∃ c : Bit, bitSign c * w = |w| := by
  by_cases h : 0 ≤ w
  · exact ⟨0, by simp [abs_of_nonneg h]⟩
  · exact ⟨1, by simp [abs_of_neg (lt_of_not_ge h)]⟩

theorem linearity_distance (n : ℕ) (hn : 1 ≤ n) (F : VectorialFunction n) :
    2 * (nonlinearity F : ℝ) + linearity F = (spaceSize n : ℝ) := by
  obtain ⟨a,b,hb,hM⟩ := linearity_attained hn F
  obtain ⟨c,hc⟩ := exists_sign_abs (walsh (component F b) a)
  have hlow := nonlinearity_le_distance F b hb a c
  have hD := distance_walsh n (component F b) a c
  rw [hc, ← Int.natCast_natAbs] at hD
  have hDR : 2 * (hammingDistance (component F b) (affineBoolean a c) : ℝ) +
      linearity F = spaceSize n := by
    rw [hM, natAbs_cast_real]
    have h := congrArg (fun z : ℤ => (z : ℝ)) hD
    push_cast at h ⊢
    linarith
  obtain ⟨b',hb',a',c',hmin⟩ := distance_attained n hn F
  have hD' := distance_walsh n (component F b') a' c'
  rw [hmin] at hD'
  have hs : bitSign c' * walsh (component F b') a' ≤ |walsh (component F b') a'| := by
    rcases sign_cases c' with h | h
    · simpa [h] using le_abs_self (walsh (component F b') a')
    · simpa [h] using neg_le_abs (walsh (component F b') a')
  have hmax := walsh_le_linearity F a' b' hb'
  have hsR : ((bitSign c' * walsh (component F b') a' : ℤ) : ℝ) ≤
      ((walsh (component F b') a').natAbs : ℝ) := by
    have hsZ : bitSign c' * walsh (component F b') a' ≤
        ((walsh (component F b') a').natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hs
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).2 hsZ
  have hD'R : 2 * (nonlinearity F : ℝ) +
      ((bitSign c' * walsh (component F b') a' : ℤ) : ℝ) = spaceSize n := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hD'
    push_cast at h ⊢
    linarith
  have hlowR : (nonlinearity F : ℝ) ≤ hammingDistance (component F b) (affineBoolean a c) := by
    exact_mod_cast hlow
  linarith

theorem rank_one (n : ℕ) (_hn : 1 ≤ n) (F : VectorialFunction n) :
    kthLinearity F 1 = linearity F := rfl

end
end APNLinearity.Fourier
