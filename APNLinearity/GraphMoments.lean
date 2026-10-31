module

public import APNLinearity.Spectrum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace APNLinearity.Sidon
noncomputable section

theorem graph_mem {n : ℕ} {Y : Type*} (F : BinarySpace n → Y) (x : BinarySpace n) :
    (x, F x) ∈ graph F := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem mem_restrictedGraph {n : ℕ} {Y : Type*} (E : Finset (BinarySpace n))
    (F : BinarySpace n → Y) (p : BinarySpace n × Y) :
    p ∈ restrictedGraph E F ↔ ∃ x ∈ E, (x, F x) = p := by
  classical
  exact Finset.mem_image

theorem derivative_pair {n : ℕ} {Y : Type*} [AddCommMonoid Y]
    (F : BinarySpace n → Y) (h x : BinarySpace n) : derivative F h (x + h) = derivative F h x := by
  simp [derivative, add_comm]

/-- The two members of a derivative fiber are the paper's pair `{x,x+h}`. -/
theorem apn_iff_collision {n : ℕ} {Y : Type*} [AddCommMonoid Y] (F : BinarySpace n → Y) :
    DerivativeBound F ↔ ∀ h, h ≠ 0 → ∀ x y,
      derivative F h x = derivative F h y → y = x ∨ y = x + h := by
  classical
  constructor
  · intro hF h hh x y hxy
    by_contra hy
    push Not at hy
    have hxh : x ≠ x + h := by
      intro he
      have : h = 0 := (add_left_cancel (show x + h = x + 0 by simpa using he.symm))
      exact hh this
    have hsub : ({x, x + h, y} : Finset (BinarySpace n)) ⊆
        Finset.univ.filter (fun z => derivative F h z = derivative F h x) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simp
      · simp [derivative_pair]
      · simp [hxy]
    have hc := (Finset.card_le_card hsub).trans (hF h (derivative F h x) hh)
    have hcard : ({x, x + h, y} : Finset (BinarySpace n)).card = 3 := by
      simp [hxh, hy.1.symm, hy.2.symm]
    omega
  · intro h h₀ y hh
    let S := Finset.univ.filter (fun x => derivative F h₀ x = y)
    change S.card ≤ 2
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      have hx' : derivative F h₀ x = y := (Finset.mem_filter.mp hx).2
      have hsub : S ⊆ {x, x + h₀} := by
        intro z hz
        have hz' : derivative F h₀ z = y := (Finset.mem_filter.mp hz).2
        simpa only [Finset.mem_insert, Finset.mem_singleton] using h h₀ hh x z (hx'.trans hz'.symm)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

theorem apn_iff_sidon_graph_general {n : ℕ} {Y : Type*} [AddCommMonoid Y]
    (F : BinarySpace n → Y) : DerivativeBound F ↔ IsBinarySidon (graph F) := by
  classical
  constructor
  · intro hF p hp q hq r hr s hs hpq hrs he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hs
    have hab : a ≠ b := by rintro rfl; exact hpq rfl
    have hinput : a + b = c + d := congrArg Prod.fst he
    have houtput : F a + F b = F c + F d := congrArg Prod.snd he
    have hh : a + b ≠ 0 := by
      intro h
      exact hab ((binary_add_eq_zero_iff a b).1 h)
    have hder : derivative F (a + b) a = derivative F (a + b) c := by
      calc
        derivative F (a + b) a = F b + F a := by simp [derivative]
        _ = F d + F c := by simpa only [add_comm] using houtput
        _ = derivative F (a + b) c := by simp [derivative, hinput]
    have hc := (apn_iff_collision F).1 hF (a + b) hh a c hder
    simp only [binary_add_cancel_left] at hc
    rcases hc with hca | hcb
    · subst c
      have hbd : b = d := add_left_cancel hinput
      subst d
      exact Or.inl ⟨rfl, rfl⟩
    · subst c
      have had : a = d := by
        apply add_left_cancel (a := b)
        simpa only [add_comm] using hinput
      subst d
      exact Or.inr ⟨rfl, rfl⟩
  · intro hS
    apply (apn_iff_collision F).2
    intro h hh x y he
    have hg (z : BinarySpace n) : (z, F z) ∈ graph F := by simp [graph]
    have hne (z : BinarySpace n) : (z, F z) ≠ (z + h, F (z + h)) := by
      intro hz
      have hz' := congrArg Prod.fst hz
      have : h = 0 := add_left_cancel (show z + h = z + 0 by simpa using hz'.symm)
      exact hh this
    have hs : (x, F x) + (x + h, F (x + h)) = (y, F y) + (y + h, F (y + h)) := by
      apply Prod.ext
      · simp
      · simpa only [Prod.snd_add, derivative, add_comm] using he
    rcases hS _ (hg x) _ (hg (x + h)) _ (hg y) _ (hg (y + h)) (hne x) (hne y) hs with hcase | hcase
    · exact Or.inl (congrArg Prod.fst hcase.1).symm
    · right
      have hx : x = y + h := congrArg Prod.fst hcase.1
      rw [hx, binary_add_cancel_right]

theorem apn_iff_sidon_graph : ∀ (n m : ℕ) (F : VectorialMap n m), DerivativeBound F ↔ IsBinarySidon (graph F) := by
  intro n m F
  exact apn_iff_sidon_graph_general F

theorem sidon_subset_general {G : Type*} [Add G] {A B : Finset G}
    (hAB : A ⊆ B) (hB : IsBinarySidon B) : IsBinarySidon A := by
  intro a ha b hb c hc d hd
  exact hB a (hAB ha) b (hAB hb) c (hAB hc) d (hAB hd)

theorem sidon_subset : ∀ (d : ℕ) (A B : Finset (BinarySpace d)), A ⊆ B → IsBinarySidon B → IsBinarySidon A := by
  intro d A B hAB hB
  exact sidon_subset_general hAB hB

end
end APNLinearity.Sidon

open scoped BigOperators

namespace APNLinearity.Sidon
noncomputable section

theorem character_sum {ι : Type*} {n : ℕ} (a : BinarySpace n) (s : Finset ι)
    (f : ι → BinarySpace n) : character a (∑ i ∈ s, f i) = ∏ i ∈ s, character a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem character_moments : ∀ (d j : ℕ), 1 ≤ j → ∀ A : Finset (BinarySpace d),
    (∑ a, characterSum A a ^ j) = (spaceSize d : ℤ) *
      ((Finset.univ.filter (fun z : Fin j → BinarySpace d =>
        (∀ i, z i ∈ A) ∧ ∑ i, z i = 0)).card : ℤ) := by
  intro d j _ A
  classical
  simp only [characterSum, Finset.sum_pow']
  rw [Finset.sum_comm]
  simp_rw [← character_sum, Fourier.character_orthogonality d]
  rw [← Finset.sum_filter]
  have hf : (Fintype.piFinset (fun _ : Fin j => A)).filter (fun z => ∑ i, z i = 0) =
      Finset.univ.filter (fun z : Fin j → BinarySpace d => (∀ i, z i ∈ A) ∧ ∑ i, z i = 0) := by
    ext z
    simp
  rw [hf]
  simp [mul_comm]

/-- The twisted second moment used by the small-support arguments. -/
theorem twisted_second_moment : ∀ (d : ℕ) (A : Finset (BinarySpace d)) (s : BinarySpace d),
    (∑ a, character a s * characterSum A a ^ 2) = (spaceSize d : ℤ) *
      (((A ×ˢ A).filter (fun z => z.1 + z.2 = s)).card : ℤ) := by
  intro d A s
  classical
  have hex (a : BinarySpace d) : character a s * characterSum A a ^ 2 =
      ∑ x ∈ A, ∑ y ∈ A, character a (s + (x + y)) := by
    simp only [characterSum, character_add_right, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hex]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  simp_rw [Fourier.character_orthogonality d, binary_add_eq_zero_iff]
  rw [← Finset.sum_product A A (fun z => if s = z.1 + z.2 then (spaceSize d : ℤ) else 0)]
  rw [← Finset.sum_filter]
  simp [eq_comm, mul_comm]

/-- Expanding a fourth power and applying character orthogonality. -/
theorem fourth_expansion {G I : Type*} [AddCommMonoid G] [DecidableEq G] [Fintype I]
    (χ : I → G → ℤ) (χadd : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (N : ℤ) (χorth : ∀ x, (∑ a, χ a x) = if x = 0 then N else 0)
    (A : Finset G) :
    (∑ a, (∑ x ∈ A, χ a x) ^ 4) =
      N * ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ w ∈ A,
        (if x + y + z + w = 0 then 1 else 0 : ℤ) := by
  classical
  have hex (a : I) : (∑ x ∈ A, χ a x) ^ 4 =
      ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ w ∈ A, χ a (x + y + z + w) := by
    rw [show (∑ x ∈ A, χ a x) ^ 4 =
      ((∑ x ∈ A, χ a x) * (∑ x ∈ A, χ a x)) *
        ((∑ x ∈ A, χ a x) * (∑ x ∈ A, χ a x)) by ring]
    simp only [χadd, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro w _
    ring
  simp_rw [hex]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := A)]
  simp_rw [χorth]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- Classification of zero-sum quadruples in a binary Sidon set. -/
theorem sidon_quadruple_sum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (htwo : ∀ x : G, x + x = 0) (A : Finset G) (hA : IsBinarySidon A) :
    (∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ w ∈ A,
      (if x + y + z + w = 0 then 1 else 0 : ℤ)) =
      3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ) := by
  classical
  have hz (x y : G) : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have hh := congrArg (fun t => t + y) h
      simpa only [add_assoc, htwo, add_zero, zero_add] using hh
    · rintro rfl
      exact htwo _
  have hquad (x y z w : G) : x + y + z + w = 0 ↔ x + y = z + w := by
    rw [add_assoc (x + y) z w, hz]
  simp_rw [hquad]
  have hpair (x : G) (hx : x ∈ A) (y : G) (hy : y ∈ A) :
      (∑ z ∈ A, ∑ w ∈ A, (if x + y = z + w then 1 else 0 : ℤ)) =
        if x = y then (A.card : ℤ) else 2 := by
    by_cases hxy : x = y
    · subst y
      simp only [htwo, eq_comm (a := (0 : G)), hz]
      simp only [Finset.sum_ite_eq, ite_true]
      simp
    · rw [ite_eq_right hxy]
      have hc (z : G) (hzA : z ∈ A) (w : G) (hwA : w ∈ A) :
          x + y = z + w ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
        constructor
        · intro h
          have hzw : z ≠ w := by
            rintro rfl
            rw [htwo] at h
            exact hxy ((hz x y).1 h)
          exact hA x hx y hy z hzA w hwA hxy hzw h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [add_comm]
      calc
        (∑ z ∈ A, ∑ w ∈ A, (if x + y = z + w then 1 else 0 : ℤ)) =
          ∑ z ∈ A, ∑ w ∈ A,
            ((if z = x ∧ w = y then 1 else 0) + (if z = y ∧ w = x then 1 else 0) : ℤ) := by
              apply Finset.sum_congr rfl
              intro z hzA
              apply Finset.sum_congr rfl
              intro w hwA
              simp only [hc z hzA w hwA]
              by_cases hzx : z = x <;> by_cases hzy : z = y <;>
                by_cases hwx : w = x <;> by_cases hwy : w = y <;> simp_all [eq_comm]
        _ = 2 := by
          simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
            Finset.sum_const_zero, Finset.sum_ite_eq', hx, hy, ite_true]
          norm_num
  have hout (x : G) (hx : x ∈ A) :
      (∑ y ∈ A, ∑ z ∈ A, ∑ w ∈ A, (if x + y = z + w then 1 else 0 : ℤ)) =
      3 * (A.card : ℤ) - 2 := by
    calc
      _ = ∑ y ∈ A, (if x = y then (A.card : ℤ) else 2) :=
        Finset.sum_congr rfl (fun y hy => hpair x hx y hy)
      _ = ∑ y ∈ A, ((if x = y then (A.card : ℤ) - 2 else 0) + 2) := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> ring
      _ = _ := by simp [Finset.sum_add_distrib, hx]; ring
  rw [Finset.sum_congr rfl (fun x hx => hout x hx)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem sidon_fourth_moment : ∀ (d : ℕ) (A : Finset (BinarySpace d)), IsBinarySidon A →
    (∑ a, characterSum A a ^ 4) = (spaceSize d : ℤ) *
      (3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ)) := by
  intro d A hA
  rw [show (∑ a, characterSum A a ^ 4) =
      (spaceSize d : ℤ) * ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ w ∈ A,
        (if x + y + z + w = 0 then 1 else 0 : ℤ) from
    fourth_expansion character character_add_right (spaceSize d : ℤ)
      (Fourier.character_orthogonality d) A]
  rw [sidon_quadruple_sum binary_add_self A hA]

end
end APNLinearity.Sidon

open scoped BigOperators

namespace APNLinearity.Sidon
noncomputable section

theorem product_character_eq {n m : ℕ} (a x : BinarySpace n × BinarySpace m) :
    productCharacter a x = character a.1 x.1 * character a.2 x.2 := by
  simp [productCharacter, character]

theorem product_character_add {n m : ℕ} (a x y : BinarySpace n × BinarySpace m) :
    productCharacter a (x + y) = productCharacter a x * productCharacter a y := by
  simp only [product_character_eq, Prod.fst_add, Prod.snd_add, character_add_right]
  ring

theorem product_orthogonality {n m : ℕ} (x : BinarySpace n × BinarySpace m) :
    (∑ a, productCharacter a x) =
      if x = 0 then (spaceSize n : ℤ) * (spaceSize m : ℤ) else 0 := by
  classical
  simp only [Fintype.sum_prod_type, product_character_eq]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Fourier.character_orthogonality n, Fourier.character_orthogonality m]
  by_cases hx : x.1 = 0 <;> by_cases hy : x.2 = 0 <;> simp [Prod.ext_iff, hx, hy]

theorem product_sidon_fourth_moment : ∀ (n m : ℕ) (A : Finset (BinarySpace n × BinarySpace m)), IsBinarySidon A →
    (∑ a, productCharacterSum A a ^ 4) =
      (spaceSize n : ℤ) * (spaceSize m : ℤ) *
        (3 * (A.card : ℤ) ^ 2 - 2 * (A.card : ℤ)) := by
  intro n m A hA
  classical
  have h := fourth_expansion productCharacter product_character_add
    ((spaceSize n : ℤ) * (spaceSize m : ℤ)) product_orthogonality A
  have ht (x : BinarySpace n × BinarySpace m) : x + x = 0 := by ext <;> simp
  rw [sidon_quadruple_sum ht A hA] at h
  exact h

theorem graph_card {n : ℕ} {Y : Type*} (F : BinarySpace n → Y) : (graph F).card = spaceSize n := by
  classical
  rw [graph, Finset.card_image_of_injective]
  · simp only [Finset.card_univ, card_binary]
  · intro x y h
    exact congrArg Prod.fst h

theorem sum_graph {n : ℕ} {Y R : Type*} [AddCommMonoid R] (F : BinarySpace n → Y)
    (g : BinarySpace n × Y → R) : (∑ p ∈ graph F, g p) = ∑ x, g (x, F x) := by
  classical
  unfold graph
  rw [Finset.sum_image]
  intro x _ y _ h
  exact congrArg Prod.fst h

theorem graph_character_sum {n : ℕ} (F : VectorialFunction n) (u : BinarySpace n × BinarySpace n) :
    productCharacterSum (graph F) u = walshAt F u := by
  unfold productCharacterSum
  rw [sum_graph]
  simp only [productCharacter, walshAt, walsh, component, add_comm]

theorem apn_fourth_moment : ∀ (n : ℕ) (F : VectorialFunction n), IsAPN F →
    (∑ b ∈ (Finset.univ.erase 0), fourthMoment (component F b)) =
      2 * (spaceSize n : ℤ) ^ 3 * ((spaceSize n : ℤ) - 1) := by
  intro n F hF
  classical
  have hfull := product_sidon_fourth_moment n n (graph F)
    ((apn_iff_sidon_graph n n F).1 hF.derivativeBound)
  simp only [graph_card, graph_character_sum, Fintype.sum_prod_type, walshAt] at hfull
  rw [Finset.sum_comm] at hfull
  change (∑ b, fourthMoment (component F b)) = _ at hfull
  have hz : fourthMoment (component F 0) = (spaceSize n : ℤ) ^ 4 := by
    simp only [fourthMoment, Fourier.walsh_zero_component]
    simp
  have hs := Finset.sum_erase_add Finset.univ (fun b => fourthMoment (component F b))
    (Finset.mem_univ (0 : BinarySpace n))
  rw [hz, hfull] at hs
  nlinarith

end
end APNLinearity.Sidon

open scoped BigOperators

namespace APNLinearity.Counts
noncomputable section
open _root_.APNLinearity.Fourier

theorem restricted_transform {n : ℕ} (F : VectorialFunction n) (E : Finset (BinarySpace n)) (b : BinarySpace n) :
    restrictedWalsh F E b = transform (fun x => if x ∈ E then bitSign (component F b x) else (0 : ℤ)) := by
  classical
  funext a
  simp [restrictedWalsh, transform, character]

theorem restricted_parseval : ∀ (n : ℕ) (F : VectorialFunction n) (E : Finset (BinarySpace n)) (b : BinarySpace n),
    (∑ a, restrictedWalsh F E b a ^ 2) = (spaceSize n : ℤ) * (E.card : ℤ) := by
  intro n F E b
  classical
  have h := transform_parseval (fun x => if x ∈ E then bitSign (component F b x) else (0 : ℤ))
  rw [← restricted_transform] at h
  have he (x : BinarySpace n) : (if x ∈ E then bitSign (component F b x) else (0 : ℤ)) ^ 2 =
      if x ∈ E then 1 else 0 := by split_ifs <;> simp
  simp only [he] at h
  simpa using h

theorem restricted_baseline : ∀ (n : ℕ) (F : VectorialFunction n) (E : Finset (BinarySpace n)) (b : BinarySpace n),
    (spaceSize n : ℤ) * (E.card : ℤ) ^ 2 ≤ restrictedFourth F E b := by
  intro n F E b
  have hN : (0 : ℤ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BinarySpace n => (1 : ℤ)) (fun a => restrictedWalsh F E b a ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, card_binary,
    nsmul_eq_mul, mul_one, ← pow_mul] at hh
  norm_num only [Nat.reduceMul] at hh
  rw [restricted_parseval n F E b] at hh
  change ((spaceSize n : ℤ) * E.card) ^ 2 ≤ (spaceSize n : ℤ) * restrictedFourth F E b at hh
  have he : (spaceSize n : ℤ) * ((spaceSize n : ℤ) * (E.card : ℤ) ^ 2) ≤
      (spaceSize n : ℤ) * restrictedFourth F E b := by nlinarith [hh]
  exact (mul_le_mul_iff_right₀ hN).mp he

theorem restricted_graph_card {n : ℕ} {Y : Type*} (F : BinarySpace n → Y) (E : Finset (BinarySpace n)) :
    (restrictedGraph E F).card = E.card := by
  classical
  rw [restrictedGraph, Finset.card_image_of_injective]
  intro x y h
  exact congrArg Prod.fst h

theorem sum_restricted_graph {n : ℕ} {Y R : Type*} [AddCommMonoid R]
    (F : BinarySpace n → Y) (E : Finset (BinarySpace n)) (g : BinarySpace n × Y → R) :
    (∑ p ∈ restrictedGraph E F, g p) = ∑ x ∈ E, g (x, F x) := by
  classical
  unfold restrictedGraph
  rw [Finset.sum_image]
  intro x _ y _ h
  exact congrArg Prod.fst h

theorem restricted_graph_character {n : ℕ} (F : VectorialFunction n) (E : Finset (BinarySpace n))
    (a b : BinarySpace n) : productCharacterSum (restrictedGraph E F) (a, b) = restrictedWalsh F E b a := by
  classical
  unfold productCharacterSum
  rw [sum_restricted_graph]
  simp only [productCharacter, restrictedWalsh, component, add_comm]

theorem restricted_fourth_total : ∀ (n : ℕ) (F : VectorialFunction n), IsAPN F → ∀ E : Finset (BinarySpace n),
    (∑ b, restrictedFourth F E b) =
      (spaceSize n : ℤ) ^ 2 * (3 * (E.card : ℤ) ^ 2 - 2 * (E.card : ℤ)) := by
  intro n F hF E
  classical
  have hsub : restrictedGraph E F ⊆ graph F := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := (Sidon.mem_restrictedGraph E F p).1 hp
    exact Sidon.graph_mem F x
  have hS := Sidon.sidon_subset_general hsub
    ((Sidon.apn_iff_sidon_graph n n F).1 hF.derivativeBound)
  have h := Sidon.product_sidon_fourth_moment n n (restrictedGraph E F) hS
  simp only [restricted_graph_card, Fintype.sum_prod_type, restricted_graph_character] at h
  rw [Finset.sum_comm] at h
  change (∑ b, restrictedFourth F E b) = _ at h
  nlinarith [h]

theorem exceptional_fourth : ∀ (n : ℕ) (F : VectorialFunction n) (E : Finset (BinarySpace n)),
    (E.card : ℤ) ^ 4 ≤ restrictedFourth F E 0 := by
  intro n F E
  classical
  have hz : restrictedWalsh F E 0 0 = E.card := by
    simp [restrictedWalsh, component]
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => restrictedWalsh F E 0 a ^ 4)
    (fun a _ => by positivity) (Finset.mem_univ (0 : BinarySpace n))
  rw [hz] at hh
  exact hh

end
end APNLinearity.Counts
