module

public import APNLinearity.GraphMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

/-!
# Elementary APN invariances and the coordinate split

The chosen nonzero component is completed by the coordinate functionals other
than one coordinate at which its coefficient is one. This explicitly supplies
the invertible change of output coordinates used in the article.
-/

namespace APNLinearity.Normalization
noncomputable section

open Sidon

theorem apn_postcompose_iff {n : ℕ} {Y Z : Type*} [AddCommMonoid Y] [AddCommMonoid Z]
    (F : BinarySpace n → Y) (L : Y →+ Z) (hi : Function.Injective L) :
    DerivativeBound (fun x => L (F x)) ↔ DerivativeBound F := by
  rw [apn_iff_collision, apn_iff_collision]
  have he (h x : BinarySpace n) : derivative (fun z => L (F z)) h x = L (derivative F h x) := by
    simp [derivative]
  simp_rw [he, hi.eq_iff]

theorem apn_input_translation {n : ℕ} {Y : Type*} [AddCommMonoid Y]
    (F : BinarySpace n → Y) (hF : DerivativeBound F) (t : BinarySpace n) : DerivativeBound (fun x => F (x + t)) := by
  apply (apn_iff_collision _).2
  intro h hh x y he
  have hd : derivative F h (x + t) = derivative F h (y + t) := by
    simpa only [derivative, add_assoc, add_comm, add_left_comm] using he
  rcases (apn_iff_collision F).1 hF h hh (x + t) (y + t) hd with hz | hz
  · exact Or.inl (add_right_cancel hz)
  · right
    apply add_right_cancel (b := t)
    simpa only [add_assoc, add_comm, add_left_comm] using hz

theorem input_translation_preserves_apn : ∀ (n m : ℕ) (F : VectorialMap n m) (t : BinarySpace n),
    DerivativeBound (fun x => F (x + t)) ↔ DerivativeBound F := by
  intro n m F t
  constructor
  · intro h
    simpa only [binary_add_cancel_right] using apn_input_translation _ h t
  · intro h
    exact apn_input_translation F h t

theorem output_linear_equiv_preserves_apn : ∀ (n m : ℕ) (F : VectorialMap n m) (e : BinarySpace m ≃ₗ[Bit] BinarySpace m),
    DerivativeBound (fun x => e (F x)) ↔ DerivativeBound F := by
  intro n m F e
  exact apn_postcompose_iff F e.toLinearMap.toAddMonoidHom e.injective

theorem derivative_affine_add {n : ℕ} {Y : Type*} [AddCommGroup Y]
    (htwo : ∀ y : Y, y + y = 0) (F : BinarySpace n → Y) (L : BinarySpace n →+ Y) (c : Y)
    (h x : BinarySpace n) :
    derivative (fun z => F z + L z + c) h x = derivative F h x + L h := by
  simp only [derivative, map_add]
  calc
    F (x + h) + (L x + L h) + c + (F x + L x + c) =
      (F (x + h) + F x) + L h + (L x + L x) + (c + c) := by abel
    _ = F (x + h) + F x + L h := by rw [htwo, htwo]; simp

theorem affine_addition_iff {n : ℕ} {Y : Type*} [AddCommGroup Y]
    (htwo : ∀ y : Y, y + y = 0) (F : BinarySpace n → Y) (L : BinarySpace n →+ Y) (c : Y) :
    DerivativeBound (fun x => F x + L x + c) ↔ DerivativeBound F := by
  rw [apn_iff_collision, apn_iff_collision]
  simp_rw [derivative_affine_add htwo, add_left_inj]

theorem affine_addition_preserves_apn : ∀ (n m : ℕ) (F : VectorialMap n m) (L : BinarySpace n →ₗ[Bit] BinarySpace m) (c : BinarySpace m),
    DerivativeBound (fun x => F x + L x + c) ↔ DerivativeBound F := by
  intro n m F L c
  exact affine_addition_iff binary_add_self F L.toAddMonoidHom c

def coordinateSplit {m : ℕ} (b : BinarySpace (m + 1)) (i : Fin (m + 1)) :
    BinarySpace (m + 1) →+ Bit × BinarySpace m where
  toFun y := (binaryDot b y, fun j => y (i.succAbove j))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

theorem coordinateSplit_injective {m : ℕ} (b : BinarySpace (m + 1)) (i : Fin (m + 1))
    (hi : b i = 1) : Function.Injective (coordinateSplit b i) := by
  intro y z he
  have hd : binaryDot b y = binaryDot b z := congrArg Prod.fst he
  have hp (j : Fin m) : y (i.succAbove j) = z (i.succAbove j) :=
    congrArg (fun p : Bit × BinarySpace m => p.2 j) he
  have hsum : (∑ j, b (i.succAbove j) * y (i.succAbove j)) =
      ∑ j, b (i.succAbove j) * z (i.succAbove j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hp]
  unfold binaryDot at hd
  rw [Fin.sum_univ_succAbove (fun j => b j * y j) i,
      Fin.sum_univ_succAbove (fun j => b j * z j) i, hi, one_mul, one_mul, hsum] at hd
  have hcoord : y i = z i := add_right_cancel hd
  ext j
  by_cases hj : j = i
  · simpa only [hj] using hcoord
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    exact hp k

theorem normalize_component : ∀ (n : ℕ), 1 ≤ n → ∀ (F : VectorialFunction n), IsAPN F →
    ∀ b : BinarySpace n, b ≠ 0 → ∀ a c,
      ∃ H : VectorialMap n (n - 1),
        DerivativeBound (splitMap (component F b + affineBoolean a c) H) := by
  intro n hn F hF b hb a c
  cases n with
  | zero => omega
  | succ m =>
    have hex : ∃ i, b i ≠ 0 := by
      by_contra h
      apply hb
      ext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hex
    have hbi : b i = 1 := (bit_eq_zero_or_one (b i)).resolve_left hi
    let H : VectorialMap (m + 1) m := fun x j => F x (i.succAbove j)
    let G := fun x => coordinateSplit b i (F x)
    have hG : DerivativeBound G := (apn_postcompose_iff F (coordinateSplit b i)
      (coordinateSplit_injective b i hbi)).2 hF.derivativeBound
    let L : BinarySpace (m + 1) →+ Bit × BinarySpace m :=
      { toFun := fun x => (binaryDot a x, 0)
        map_zero' := by simp
        map_add' := by intro x y; simp }
    have ht (y : Bit × BinarySpace m) : y + y = 0 := by ext <;> simp
    have hnew := (affine_addition_iff ht G L (c, 0)).2 hG
    refine ⟨H, ?_⟩
    change DerivativeBound (fun x => (component F b x + affineBoolean a c x, H x))
    simpa [component, mapComponent, affineBoolean, G, H, L, coordinateSplit, add_assoc] using hnew

theorem complement_graph_sidon : ∀ (n : ℕ) (E : Finset (BinarySpace n)) (H : VectorialMap n (n - 1)),
    DerivativeBound (splitMap (indicator E) H) →
      IsBinarySidon (restrictedGraph (Finset.univ \ E) H) := by
  intro n E H hF
  classical
  have hS := (apn_iff_sidon_graph_general (splitMap (indicator E) H)).1 hF
  intro p hp q hq r hr s hs hpq hrs he
  obtain ⟨a, ha, rfl⟩ := (mem_restrictedGraph _ _ _).1 hp
  obtain ⟨b, hb, rfl⟩ := (mem_restrictedGraph _ _ _).1 hq
  obtain ⟨c, hc, rfl⟩ := (mem_restrictedGraph _ _ _).1 hr
  obtain ⟨d, hd, rfl⟩ := (mem_restrictedGraph _ _ _).1 hs
  have hmem (x : BinarySpace n) (hx : x ∈ Finset.univ \ E) :
      (x, (0, H x)) ∈ graph (splitMap (indicator E) H) := by
    have hx' : x ∉ E := (Finset.mem_sdiff.mp hx).2
    simpa [splitMap, indicator, hx'] using graph_mem (splitMap (indicator E) H) x
  have hab : (a, ((0 : Bit), H a)) ≠ (b, (0, H b)) := by
    intro h
    apply hpq
    exact congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h
  have hcd : (c, ((0 : Bit), H c)) ≠ (d, (0, H d)) := by
    intro h
    apply hrs
    exact congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h
  have hsum : (a, ((0 : Bit), H a)) + (b, (0, H b)) = (c, (0, H c)) + (d, (0, H d)) := by
    apply Prod.ext
    · have hinput : a + b = c + d := congrArg Prod.fst he
      exact hinput
    · apply Prod.ext
      · rfl
      · have houtput : H a + H b = H c + H d := congrArg Prod.snd he
        exact houtput
  have hresult := hS _ (hmem a ha) _ (hmem b hb) _ (hmem c hc) _ (hmem d hd) hab hcd hsum
  rcases hresult with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    exact ⟨congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h₁,
      congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h₂⟩
  · right
    exact ⟨congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h₁,
      congrArg (fun p : BinarySpace n × (Bit × BinarySpace (n - 1)) => (p.1, p.2.2)) h₂⟩

end

end APNLinearity.Normalization

open scoped BigOperators

namespace APNLinearity.Fourier
noncomputable section

def convolution {n : ℕ} (u v : BinarySpace n → ℤ) (x : BinarySpace n) : ℤ :=
  ∑ y, u y * v (x + y)

theorem transform_injective {n : ℕ} : Function.Injective (@transform ℤ _ n) := by
  intro u v h
  funext x
  have he := congrArg (fun g => transform g x) h
  rw [transform_twice, transform_twice] at he
  exact mul_left_cancel₀ (by exact_mod_cast (spaceSize_pos n).ne') he

theorem transform_const_mul {n : ℕ} (c : ℤ) (u : BinarySpace n → ℤ) :
    transform (fun x => c * u x) = fun a => c * transform u a := by
  funext a
  simp only [transform, Finset.mul_sum, mul_assoc]

theorem transform_convolution {n : ℕ} (u v : BinarySpace n → ℤ) (a : BinarySpace n) :
    transform (convolution u v) a = transform u a * transform v a := by
  have hs (y : BinarySpace n) : (∑ x, v (x + y) * character a x) =
      transform v a * character a y := by
    have ht := sum_translate (fun x => v (x + y) * character a x) y
    simpa only [binary_add_cancel_right, character_add_right, transform,
      Finset.sum_mul, mul_assoc, Int.cast_id] using ht.symm
  unfold transform convolution
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, u y * v (x + y) * character a x) =
      ∑ y, u y * (∑ x, v (x + y) * character a x) := by
        simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ y, u y * (transform v a * character a y) := by simp only [hs]
    _ = _ := by
      simp only [transform, Finset.sum_mul, Int.cast_id]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul]
      ring

theorem convolution_sign_self {n : ℕ} (f : BooleanFunction n) (h : BinarySpace n) :
    convolution (fun x => bitSign (f x)) (fun x => bitSign (f x)) h =
      ∑ x, bitSign (derivative f h x) := by
  simp only [convolution, derivative, sign_add]
  apply Finset.sum_congr rfl
  intro x _
  rw [add_comm h x, mul_comm]





end
end APNLinearity.Fourier

open scoped BigOperators

namespace APNLinearity.Components
noncomputable section
open _root_.APNLinearity.Fourier

theorem sign_sum_eq_zero_iff_balanced {n : ℕ} (f : BooleanFunction n) :
    (∑ x, bitSign (f x)) = 0 ↔ IsBalanced f := by
  rw [sign_sum_weight]
  unfold IsBalanced
  constructor
  · intro h
    have he : 2 * (weight f : ℤ) = (spaceSize n : ℤ) := by omega
    exact_mod_cast he
  · intro h
    have he : 2 * (weight f : ℤ) = (spaceSize n : ℤ) := by exact_mod_cast h
    omega

theorem transform_delta {n : ℕ} (a : BinarySpace n) :
    transform (fun x : BinarySpace n => if x = 0 then (spaceSize n : ℤ) else 0) a = spaceSize n := by
  classical
  simp [transform]

theorem sign_autocorrelation_zero {n : ℕ} (f : BooleanFunction n) :
    convolution (fun x => bitSign (f x)) (fun x => bitSign (f x)) 0 = spaceSize n := by
  simp only [convolution, zero_add, ← pow_two, sign_sq]
  simp only [Finset.sum_const, Finset.card_univ, card_binary, nsmul_eq_mul, mul_one]

theorem bent_iff_balanced_derivatives : ∀ (n : ℕ) (f : BooleanFunction n), IsBent f ↔
    ∀ h, h ≠ 0 → IsBalanced (derivative f h) := by
  intro n f
  classical
  let s := fun x => bitSign (f x)
  have htransform (a : BinarySpace n) : transform (convolution s s) a = walsh f a ^ 2 := by
    rw [transform_convolution]
    simp only [s, ← walsh_eq_transform, pow_two]
  constructor
  · intro hf
    have he : convolution s s = fun x => if x = 0 then (spaceSize n : ℤ) else 0 := by
      apply transform_injective
      funext a
      rw [htransform, transform_delta]
      exact hf a
    intro h hh
    apply (sign_sum_eq_zero_iff_balanced _).1
    have he' := congrFun he h
    rw [ite_eq_right hh] at he'
    simpa only [s, convolution_sign_self] using he'
  · intro hd a
    have he : convolution s s = fun x => if x = 0 then (spaceSize n : ℤ) else 0 := by
      funext h
      by_cases hh : h = 0
      · subst h
        simpa only [s, ite_true] using sign_autocorrelation_zero f
      · rw [ite_eq_right hh]
        exact (convolution_sign_self f h).trans ((sign_sum_eq_zero_iff_balanced _).2 (hd h hh))
    rw [← htransform, he, transform_delta]

end
end APNLinearity.Components

open scoped BigOperators

namespace APNLinearity.Components
noncomputable section
open _root_.APNLinearity.Fourier

theorem plateaued_magnitude_power : ∀ (n : ℕ) (f : BooleanFunction n) (amplitude : ℤ), HasPlateauedMagnitude f amplitude →
    ∃ r : ℕ, amplitude = 2 ^ r := by
  intro n f amplitude h
  have hd : amplitude ∣ (spaceSize n : ℤ) ^ 2 := by
    rw [← walsh_parseval n f]
    apply Finset.dvd_sum
    intro a _
    rcases h.2 a with hw | hw | hw <;> rw [hw] <;> simp [pow_two]
  have hd' : amplitude.natAbs ∣ (2 : ℕ) ^ (n * 2) := by
    have ht := Int.natAbs_dvd_natAbs.mpr hd
    simpa [spaceSize, pow_mul] using ht
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd'
  refine ⟨r, ?_⟩
  have ha := Int.natAbs_of_nonneg h.1.le
  rw [hr] at ha
  exact_mod_cast ha.symm


theorem affine_of_full_walsh {n : ℕ} (f : BooleanFunction n) (a₀ : BinarySpace n)
    (hfull : |walsh f a₀| = (spaceSize n : ℤ)) : IsAffine f := by
  classical
  have hN : (0 : ℤ) < spaceSize n := by exact_mod_cast spaceSize_pos n
  have hsq : walsh f a₀ ^ 2 = (spaceSize n : ℤ) ^ 2 := by
    nlinarith [sq_abs (walsh f a₀)]
  have hsum := Finset.sum_erase_add Finset.univ (fun a => walsh f a ^ 2)
    (Finset.mem_univ a₀)
  rw [walsh_parseval n f, hsq] at hsum
  have hzero : ∑ a ∈ Finset.univ.erase a₀, walsh f a ^ 2 = 0 := by linarith
  have ho (a : BinarySpace n) (ha : a ≠ a₀) : walsh f a = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (walsh f a))).1
      hzero a (by simp [ha])
    nlinarith
  have hw : walsh f a₀ = (spaceSize n : ℤ) ∨ walsh f a₀ = -(spaceSize n : ℤ) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  obtain ⟨c, hc⟩ : ∃ c : Bit, walsh f a₀ = bitSign c * (spaceSize n : ℤ) := by
    rcases hw with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  refine ⟨a₀, c, ?_⟩
  funext x
  apply sign_injective
  have hi := transform_twice (fun y => bitSign (f y)) x
  rw [← walsh_eq_transform f] at hi
  change (∑ a, walsh f a * character x a) = (spaceSize n : ℤ) * bitSign (f x) at hi
  rw [Finset.sum_eq_single a₀] at hi
  · rw [hc, character_comm x a₀] at hi
    have hs : bitSign (f x) = bitSign c * character a₀ x := by
      apply (mul_left_cancel₀ hN.ne')
      calc
        (spaceSize n : ℤ) * bitSign (f x) = bitSign c * (spaceSize n : ℤ) * character a₀ x := hi.symm
        _ = (spaceSize n : ℤ) * (bitSign c * character a₀ x) := by ring
    simpa [affineBoolean, character, mul_comm] using hs
  · intro a _ ha
    rw [ho a ha, zero_mul]
  · simp

theorem plateaued_amplitude_le {n : ℕ} (f : BooleanFunction n) (amplitude : ℤ)
    (h : HasPlateauedMagnitude f amplitude) : amplitude ≤ (spaceSize n : ℤ) := by
  obtain ⟨a, ha⟩ := exists_walsh_ne_zero f
  have hm : |walsh f a| = amplitude := by
    rcases h.2 a with h₀ | hp | hn
    · exact False.elim (ha h₀)
    · rw [hp, abs_of_pos h.1]
    · rw [hn, abs_neg, abs_of_pos h.1]
  simpa only [hm] using walsh_abs_le f a

theorem plateaued_nonaffine_bound : ∀ (n : ℕ) (f : BooleanFunction n), IsPlateaued f → ¬ IsAffine f →
    ∀ a, |(walsh f a : ℝ)| ≤ (spaceSize n : ℝ) / 2 := by
  intro n f hf hnon a
  obtain ⟨amplitude, h⟩ := (integer_plateaued_magnitude _ _).2 hf
  obtain ⟨r, hr⟩ := plateaued_magnitude_power n f amplitude h
  have hle := plateaued_amplitude_le f amplitude h
  have hne : amplitude ≠ (spaceSize n : ℤ) := by
    intro he
    obtain ⟨a₀, ha₀⟩ := exists_walsh_ne_zero f
    apply hnon
    apply affine_of_full_walsh f a₀
    rcases h.2 a₀ with h₀ | hp | hn
    · exact False.elim (ha₀ h₀)
    · rw [hp, abs_of_pos h.1, he]
    · rw [hn, abs_neg, abs_of_pos h.1, he]
  have hlt : r < n := by
    have hpow : (2 : ℤ) ^ r < (2 : ℤ) ^ n := by
      simpa [hr, spaceSize] using lt_of_le_of_ne hle hne
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 hpow
  have hdouble : 2 * amplitude ≤ (spaceSize n : ℤ) := by
    have hp := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).2 (show r + 1 ≤ n by omega)
    simpa [pow_succ, hr, spaceSize, mul_comm] using hp
  have ha : |walsh f a| ≤ amplitude := by
    rcases h.2 a with h₀ | hp | hn
    · simp [h₀, h.1.le]
    · simp [hp, abs_of_pos h.1]
    · simp [hn, abs_of_pos h.1]
  have ha' : |(walsh f a : ℝ)| ≤ (amplitude : ℝ) := by exact_mod_cast ha
  have hd' : 2 * (amplitude : ℝ) ≤ (spaceSize n : ℝ) := by exact_mod_cast hdouble
  linarith

end
end APNLinearity.Components

open scoped BigOperators

namespace APNLinearity.Components
noncomputable section
open _root_.APNLinearity.Fourier

theorem square_power_two {n : ℕ} (w : ℤ) (h : w ^ 2 = (2 : ℤ) ^ n) :
    ∃ k : ℕ, n = k + k ∧ |w| = (2 : ℤ) ^ k := by
  have hn : w.natAbs ^ 2 = (2 : ℕ) ^ n := by
    have hh := congrArg Int.natAbs h
    simpa using hh
  have hd : w.natAbs ∣ (2 : ℕ) ^ n := by
    rw [← hn]
    exact dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hk, ← pow_mul] at hn
  have he : k * 2 = n := Nat.pow_right_injective (by decide) hn
  refine ⟨k, by omega, ?_⟩
  have hh : (w.natAbs : ℤ) = (2 : ℤ) ^ k := by exact_mod_cast hk
  simpa only [Int.natCast_natAbs] using hh

theorem sum_component_walsh_zero {n m : ℕ} (K : VectorialMap n m) :
    (∑ b, walsh (mapComponent K b) 0) =
      (spaceSize m : ℤ) * ((Finset.univ.filter (fun x => K x = 0)).card : ℤ) := by
  classical
  simp only [walsh, mapComponent, dot_zero_left, add_zero]
  change (∑ b, ∑ x, character b (K x)) = _
  rw [Finset.sum_comm]
  simp_rw [character_orthogonality m]
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Nyberg's dimension bound, using the fiber identity and parity as in the paper. -/
theorem vectorial_bent_dimension : ∀ (n m : ℕ), 0 < n → 0 < m → ∀ K : VectorialMap n m,
    (∀ b, b ≠ 0 → IsBent (mapComponent K b)) → Even n ∧ m ≤ n / 2 := by
  intro n m hn hm K hK
  classical
  obtain ⟨b₀, hb₀⟩ := nonzero_index hm
  have hsq : walsh (mapComponent K b₀) 0 ^ 2 = (2 : ℤ) ^ n := by
    simpa [spaceSize] using hK b₀ hb₀ 0
  obtain ⟨k, hnk, _⟩ := square_power_two _ hsq
  refine ⟨⟨k, hnk⟩, ?_⟩
  have hk : 0 < k := by omega
  have hhalf : n / 2 = k := by omega
  rw [hhalf]
  by_contra hmk
  have hkm : k < m := by omega
  let s : ℤ := 2 ^ k
  let ε : BinarySpace m → ℤ := fun b => if walsh (mapComponent K b) 0 = s then 1 else -1
  let S : Finset (BinarySpace m) := Finset.univ.erase 0
  have hs : 0 < s := pow_pos (by norm_num) _
  have hsquare : (spaceSize n : ℤ) = s ^ 2 := by
    simp [spaceSize, hnk, pow_add, s, pow_two]
  have hε (b : BinarySpace m) (hb : b ≠ 0) : walsh (mapComponent K b) 0 = s * ε b := by
    have hbent := hK b hb 0
    rw [hsquare] at hbent
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hbent with h | h
    · simp [ε, h]
    · have hne : walsh (mapComponent K b) 0 ≠ s := by rw [h]; omega
      simp only [ε, ite_eq_right hne, mul_neg_one]
      exact h
  have hzero : walsh (mapComponent K 0) 0 = (spaceSize n : ℤ) := by
    simp [walsh, mapComponent, spaceSize]
  have hsum := Finset.sum_erase_add Finset.univ (fun b => walsh (mapComponent K b) 0)
    (Finset.mem_univ (0 : BinarySpace m))
  have hnonzero : (∑ b ∈ S, walsh (mapComponent K b) 0) = s * ∑ b ∈ S, ε b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    exact hε b (Finset.mem_erase.mp hb).1
  change (∑ b ∈ S, walsh (mapComponent K b) 0) + walsh (mapComponent K 0) 0 = _ at hsum
  rw [hnonzero, hzero, sum_component_walsh_zero K] at hsum
  have hM : (spaceSize m : ℤ) = s * (2 : ℤ) ^ (m - k) := by
    simp only [spaceSize, Nat.cast_pow, Nat.cast_ofNat, s, ← pow_add]
    congr 1
    omega
  have he : (2 : ℤ) ^ (m - k) * ((Finset.univ.filter (fun x => K x = 0)).card : ℤ) =
      s + ∑ b ∈ S, ε b := by
    apply mul_left_cancel₀ hs.ne'
    rw [hM, hsquare] at hsum
    nlinarith
  have hεbit (b : BinarySpace m) : (ε b : Bit) = 1 := by
    dsimp [ε]
    split_ifs <;> decide
  have htwoBit : (2 : Bit) = 0 := rfl
  have hEbit : ((∑ b ∈ S, ε b : ℤ) : Bit) = 1 := by
    rw [Int.cast_sum]
    simp only [hεbit, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc : S.card = spaceSize m - 1 := by
      simp only [S, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_binary]
    rw [hc, Nat.cast_sub (spaceSize_pos m)]
    simp only [spaceSize, Nat.cast_pow, Nat.cast_ofNat, htwoBit, zero_pow hm.ne',
      Nat.cast_one, zero_sub, ZMod.neg_eq_self_mod_two]
  have hsbit : (s : Bit) = 0 := by
    simp only [s, Int.cast_pow, Int.cast_ofNat, htwoBit, zero_pow hk.ne']
  have heBit := congrArg (fun z : ℤ => (z : Bit)) he
  simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, htwoBit,
    zero_pow (show m - k ≠ 0 by omega), hsbit, hEbit, zero_mul, zero_add] at heBit
  exact zero_ne_one heBit

end
end APNLinearity.Components

open scoped BigOperators

namespace APNLinearity.Components
noncomputable section
open _root_.APNLinearity.Fourier Sidon

theorem projected_derivative_fibers {n m : ℕ} (K : VectorialMap n m) (hK : DerivativeBound K)
    (hsize : spaceSize n = 2 * spaceSize m) (h : BinarySpace n) (hh : h ≠ 0) (y : BinarySpace m) :
    (Finset.univ.filter (fun x => derivative K h x = y)).card = 2 := by
  classical
  have htotal := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (BinarySpace n)) (Finset.univ : Finset (BinarySpace m)) (derivative K h)
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, card_binary] at htotal
  have he : (∑ y, (Finset.univ.filter (fun x => derivative K h x = y)).card) =
      ∑ _y : BinarySpace m, (2 : ℕ) := by
    rw [htotal, hsize]
    simp only [Finset.sum_const, Finset.card_univ, card_binary, smul_eq_mul, mul_comm]
  have hle (z : BinarySpace m) (_ : z ∈ (Finset.univ : Finset (BinarySpace m))) :
      (Finset.univ.filter (fun x => derivative K h x = z)).card ≤ 2 := by
    convert hK h z hh using 1
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, derivative]
  exact (Finset.sum_eq_sum_iff_of_le hle).1 he y (Finset.mem_univ _)

theorem uniform_derivative_component_balanced {n m : ℕ} (K : VectorialMap n m) (h : BinarySpace n)
    (hfib : ∀ y, (Finset.univ.filter (fun x => derivative K h x = y)).card = 2)
    (b : BinarySpace m) (hb : b ≠ 0) : IsBalanced (derivative (mapComponent K b) h) := by
  classical
  apply (sign_sum_eq_zero_iff_balanced _).1
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := derivative K h)
    (fun _ _ => Finset.mem_univ _) (fun x => character b (derivative K h x))
  have hinner (y : BinarySpace m) :
      (∑ x ∈ Finset.univ.filter (fun x => derivative K h x = y), character b (derivative K h x)) =
      2 * character b y := by
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x => derivative K h x = y), character b y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp only [Finset.sum_const, hfib, nsmul_eq_mul, Nat.cast_ofNat]
  have hsum : (∑ x, character b (derivative K h x)) = 0 := by
    rw [← hpartition]
    simp_rw [hinner]
    rw [← Finset.mul_sum]
    have ho : (∑ y, character b y) = 0 := by
      simpa only [character_comm, ite_eq_right hb] using character_orthogonality m b
    rw [ho, mul_zero]
  simpa only [character, component, mapComponent, derivative, dot_add_right, sign_add] using hsum

theorem projected_graph_obstruction : ∀ (n : ℕ), 3 ≤ n → ∀ K : VectorialMap n (n - 1), ¬ IsBinarySidon (graph K) := by
  intro n hn K hS
  have hK : DerivativeBound K := (apn_iff_sidon_graph n (n - 1) K).2 hS
  have hsize : spaceSize n = 2 * spaceSize (n - 1) := by
    have he : n = n - 1 + 1 := by omega
    conv_lhs => rw [he]
    simp [spaceSize, pow_succ, mul_comm]
  have hbent (b : BinarySpace (n - 1)) (hb : b ≠ 0) : IsBent (mapComponent K b) := by
    apply (bent_iff_balanced_derivatives n (mapComponent K b)).2
    intro h hh
    exact uniform_derivative_component_balanced K h
      (projected_derivative_fibers K hK hsize h hh) b hb
  have hdim := (vectorial_bent_dimension n (n - 1) (by omega) (by omega) K hbent).2
  omega

theorem no_affine_component : ∀ (n : ℕ), 3 ≤ n → ∀ F : VectorialFunction n, IsAPN F →
    ∀ b, b ≠ 0 → ¬ IsAffine (component F b) := by
  intro n hn F hF b hb hAff
  obtain ⟨a, c, hAff⟩ := hAff
  obtain ⟨H, hH⟩ := Normalization.normalize_component n (by omega) F hF b hb a c
  have hg : component F b + affineBoolean a c = 0 := by
    rw [hAff]
    ext x
    exact bit_add_self _
  rw [hg] at hH
  have hK : DerivativeBound H := by
    apply (apn_iff_collision H).2
    intro h hh x y he
    apply (apn_iff_collision _).1 hH h hh x y
    apply Prod.ext
    · simp [derivative, splitMap]
    · exact he
  exact projected_graph_obstruction n hn H ((apn_iff_sidon_graph n (n - 1) H).1 hK)

/-- A nonzero APN component cannot have a Walsh coefficient of full magnitude. -/
theorem linearity_lt_size {n : ℕ} (hn : 3 ≤ n) (F : VectorialFunction n) (hF : IsAPN F) :
    linearity F < (spaceSize n : ℝ) := by
  obtain ⟨a, b, hb, hL⟩ := linearity_attained (by omega : 1 ≤ n) F
  have hle : linearity F ≤ (spaceSize n : ℝ) := by
    rw [hL, natAbs_cast_real]
    exact_mod_cast walsh_abs_le (component F b) a
  apply lt_of_le_of_ne hle
  intro he
  apply no_affine_component n hn F hF b hb
  apply affine_of_full_walsh (component F b) a
  have hr : |(walsh (component F b) a : ℝ)| = (spaceSize n : ℝ) := by
    rw [← natAbs_cast_real, ← hL, he]
  exact_mod_cast hr

end
end APNLinearity.Components
