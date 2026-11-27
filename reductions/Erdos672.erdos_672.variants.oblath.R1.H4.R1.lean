import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1

-- Reduction Erdos672.erdos_672.variants.oblath.R1.H4.R1 of step Erdos672.erdos_672.variants.oblath.R1.H4
-- Credit: @aqron7
--
-- The product of a 3-term AP n, n + d, n + 2d (n, d coprime) being a fifth power reduces to two
-- classical Diophantine equations. If n is odd the three terms are pairwise coprime fifth powers
-- a, b, c with a ^ 5 + c ^ 5 = 2 b ^ 5 (Denes 1952 for p = 5). If n = 2A is even then n + d = b ^ 5 and
-- A, A + d split as 8 u ^ 5 and w ^ 5, so b ^ 5 + (-w) ^ 5 = 8 u ^ 5 (a case of Ribet 1997,
-- a ^ p + 2 ^ k b ^ p + c ^ p = 0 has no nontrivial solutions for 2 <= k < p).

namespace OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1

/-- Denes (p = 5): `x ^ 5 + y ^ 5 = 2 z ^ 5` forces `x = y` or `z = 0`. -/
def H1 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0

/-- Ribet (p = 5, k = 3): `x ^ 5 + y ^ 5 = 8 z ^ 5` forces `z = 0`. -/
def H2 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 8 * z ^ 5 → z = 0

lemma fifth_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 5) :
    ∃ u, a = u ^ 5 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

lemma split_even5 {E O m : ℕ} (hc : Nat.Coprime E O) (hO : Odd O) (h : E * O = 8 * m ^ 5) :
    ∃ u w, E = 8 * u ^ 5 ∧ O = w ^ 5 := by
  have hO2 : Nat.Coprime 2 O := (Nat.coprime_two_left).mpr hO
  have step : ∀ F k : ℕ, F * O = 2 * k → ∃ F', F = 2 * F' := by
    intro F k hF
    have : 2 ∣ F * O := ⟨k, hF⟩
    exact hO2.dvd_of_dvd_mul_right this
  obtain ⟨E1, rfl⟩ := step E (4 * m ^ 5) (by rw [h]; ring)
  obtain ⟨E2, rfl⟩ := step E1 (2 * m ^ 5) (by nlinarith [h])
  obtain ⟨E3, rfl⟩ := step E2 (m ^ 5) (by nlinarith [h])
  have h3 : E3 * O = m ^ 5 := by nlinarith [h]
  have hc3 : Nat.Coprime E3 O := by
    have : E3 ∣ 2 * (2 * (2 * E3)) := ⟨8, by ring⟩
    exact Nat.Coprime.coprime_dvd_left this hc
  obtain ⟨u, hu⟩ := fifth_of_coprime hc3 h3
  obtain ⟨w, hw⟩ := fifth_of_coprime hc3.symm (by rw [mul_comm]; exact h3)
  exact ⟨u, w, by rw [hu]; ring, hw⟩

theorem ap3_ne_fifth (den : H1) (rib : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 5 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hmid : (n + d) * (n * (n + 2 * d)) = q ^ 5 := by rw [← hq]; ring
  obtain ⟨b, hb⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1 c2) hmid
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb; omega
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨A, hA⟩ := hev
    have hA' : n = 2 * A := by omega
    subst hA'
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
      · exfalso
        have : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, rfl⟩ ⟨k, by omega⟩
        rw [hnd] at this; omega
      · exact h
    have hcAC : Nat.Coprime A (A + d) := by
      rw [Nat.coprime_self_add_right]; exact Nat.Coprime.coprime_mul_left hnd
    have hBA : (2 * A * (2 * A + 2 * d)) * (2 * A + d) = q ^ 5 := by rw [← hmid]; ring
    obtain ⟨m, hm⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1 c2).symm hBA
    have hm2 : 2 ∣ m := by
      have : 2 ∣ m ^ 5 := ⟨2 * A * (A + d), by rw [← hm]; ring⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨m', rfl⟩ := hm2
    have hAC : A * (A + d) = 8 * m' ^ 5 := by nlinarith [hm]
    have hsum : 2 * A + d = A + (A + d) := by ring
    have hApos : 0 < A := by omega
    have key : ∀ E O : ℕ, Nat.Coprime E O → Odd O → E * O = 8 * m' ^ 5 → E + O = b ^ 5 →
        0 < E → False := by
      intro E O hc hO hEO hsum' hE
      obtain ⟨u, w, hu, hw⟩ := split_even5 hc hO hEO
      have k : (b : ℤ) ^ 5 + (-(w : ℤ)) ^ 5 = 8 * (u : ℤ) ^ 5 := by
        have : b ^ 5 = 8 * u ^ 5 + w ^ 5 := by rw [← hsum', hu, hw]
        have : ((b ^ 5 : ℕ) : ℤ) = ((8 * u ^ 5 + w ^ 5 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      have hu0 : (u : ℤ) = 0 := rib _ _ _ k
      have : u = 0 := by exact_mod_cast hu0
      subst this; simp at hu; omega
    rcases Nat.even_or_odd A with hAe | hAo
    · have hCo : Odd (A + d) := hAe.add_odd hdodd
      exact key A (A + d) hcAC hCo hAC (by rw [← hsum]; exact hb) hApos
    · exact key (A + d) A hcAC.symm hAo (by rw [mul_comm]; exact hAC)
        (by rw [add_comm, ← hsum]; exact hb) (by omega)
  · have c3 : Nat.Coprime n (n + 2 * d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.mul_right hodd.coprime_two_right hnd
    obtain ⟨a, ha⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1.symm c3) hq
    have hlast : (n + 2 * d) * (n * (n + d)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨c, hc⟩ := fifth_of_coprime (Nat.Coprime.mul_right c3.symm c2.symm) hlast
    have k : (a : ℤ) ^ 5 + (c : ℤ) ^ 5 = 2 * (b : ℤ) ^ 5 := by
      have : a ^ 5 + c ^ 5 = 2 * b ^ 5 := by rw [← ha, ← hb, ← hc]; ring
      exact_mod_cast this
    rcases den _ _ _ k with h | h
    · have : a = c := by exact_mod_cast h
      subst this; omega
    · exact hb0 (by exact_mod_cast h)

theorem main : H1 → H2 → OMA.R_Erdos672_erdos_672_variants_oblath_R1.H4 := by
  intro den rib
  show Erdos672.Erdos672With 3 5
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact ap3_ne_fifth den rib hn hd hnd hq

end OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1
