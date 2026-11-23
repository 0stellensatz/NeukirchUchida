import Mathlib

/-!
# Compatibility lemmas for the mathlib v4.36 port

Mathlib swapped `Ideal.ramificationIdx` (now the localization-length definition) with
`Ideal.ramificationIdx'` (the classical `sSup {n | map p ≤ P ^ n}` definition), and restated
some lemmas for the new definition. This file restores the pre-v4.36 statements that the
development relies on, for the classical index `Ideal.ramificationIdx'`.
-/

/-- The pre-v4.36 statement of `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`, for the
classical ramification index `Ideal.ramificationIdx'` (mathlib now states it for the new
`Ideal.ramificationIdx`). Proof copied from mathlib `360da6fa`. -/
lemma Ideal.ramificationIdx'_eq_one_of_isUnramifiedAt
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : Ideal S} [p.IsPrime] [IsNoetherianRing S] [Algebra.IsUnramifiedAt R p]
    (hp : p ≠ ⊥) [IsDomain S] [Algebra.EssFiniteType R S] :
    Ideal.ramificationIdx' (p.under R) p = 1 :=
  let := Localization.AtPrime.algebraOfLiesOver (p.under R) p
  (Ideal.ramificationIdx'_eq_one_of_map_localization Ideal.map_comap_le hp
    p.primeCompl_le_nonZeroDivisors
    ((Algebra.isUnramifiedAt_iff_map_eq R (p.under R) p).mp ‹_›).2)

/-- The pre-v4.36 statement of `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`, for the
classical ramification index `Ideal.ramificationIdx'`. Proof adapted from mathlib `360da6fa`. -/
lemma Algebra.isUnramifiedAt_iff_of_isDedekindDomain'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : Ideal S} [p.IsPrime] [IsDedekindDomain S] [Algebra.EssFiniteType R S] [IsDomain R]
    [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (hp : p ≠ ⊥) :
    Algebra.IsUnramifiedAt R p ↔ Ideal.ramificationIdx' (p.under R) p = 1 := by
  let := Localization.AtPrime.algebraOfLiesOver (p.under R) p
  rw [Algebra.isUnramifiedAt_iff_map_eq R (p.under R) p, and_iff_right,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hp Ideal.map_comap_le]
  have : Finite (R ⧸ p.under R) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (mt Ideal.eq_bot_of_under_eq_bot hp)
  have : Finite ((p.under R).ResidueField) := IsLocalization.finite _
    (nonZeroDivisors (R ⧸ p.under R))
  infer_instance

/-! ### The fundamental identity with the new inertia degree

Mathlib deprecated `Ideal.sum_ramification_inertia` and its corollaries (stated for the old
`Ideal.inertiaDeg'`) in favour of `Ideal.sum_ramification_inertia_eq_finrank`. The lemmas below
restate the corollaries used in this development with the classical ramification index
`Ideal.ramificationIdx'` and the new inertia degree `Ideal.inertiaDeg`. -/

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.IsTorsionFree R S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L]

/-- The fundamental identity `∑ e(P|p) f(P|p) = [L : K]` over the primes `P` above `p`. -/
theorem sum_ramificationIdx'_mul_inertiaDeg {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S, p.ramificationIdx' P * P.inertiaDeg R =
      Module.finrank K L := by
  rw [Finset.sum_subtype (p := (· ∈ p.primesOver S)) _
      (fun _ => IsDedekindDomain.mem_primesOverFinset_iff hp0 S),
    IsFractionRing.finrank_eq R K S L, ← sum_ramification_inertia_eq_finrank p S]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [ramificationIdx'_eq_ramificationIdx p P.1 hp0]

/-- The number of primes above `p` is at most `[L : K]`. -/
theorem card_primesOverFinset_le_finrank' {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p S).card ≤ Module.finrank K L := by
  rw [← sum_ramificationIdx'_mul_inertiaDeg (S := S) K L hp0, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun P hP => ?_
  have hP' := (IsDedekindDomain.mem_primesOverFinset_iff hp0 S).mp hP
  have : P.IsPrime := hP'.1
  have : P.LiesOver p := hP'.2
  exact Right.one_le_mul
    (Nat.pos_of_ne_zero (IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hp0))
    (inertiaDeg_pos P R)

/-- The classical ramification index is at most `[L : K]`. -/
theorem ramificationIdx'_le_finrank {p : Ideal R} [p.IsMaximal] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] : p.ramificationIdx' P ≤ Module.finrank K L := by
  by_cases hp0 : p = ⊥
  · simp [hp0]
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 S).mpr ⟨‹_›, ‹_›⟩
  rw [← sum_ramificationIdx'_mul_inertiaDeg (S := S) K L hp0, ← Finset.add_sum_erase _ _ hP]
  exact le_trans (Nat.le_mul_of_pos_right _ (inertiaDeg_pos P R)) (Nat.le_add_right _ _)

/-- The inertia degree is at most `[L : K]`. -/
theorem inertiaDeg_le_finrank' {p : Ideal R} [p.IsMaximal] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] (hp0 : p ≠ ⊥) : P.inertiaDeg R ≤ Module.finrank K L := by
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 S).mpr ⟨‹_›, ‹_›⟩
  rw [← sum_ramificationIdx'_mul_inertiaDeg (S := S) K L hp0, ← Finset.add_sum_erase _ _ hP]
  exact le_trans (Nat.le_mul_of_pos_left _
    (Nat.pos_of_ne_zero (IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hp0)))
    (Nat.le_add_right _ _)

/-- The fundamental identity `e f = [L : K]` when `S` is local. -/
theorem ramificationIdx'_mul_inertiaDeg_of_isLocalRing [IsLocalRing S] {p : Ideal R}
    [p.IsMaximal] (hp0 : p ≠ ⊥) :
    p.ramificationIdx' (IsLocalRing.maximalIdeal S) *
      (IsLocalRing.maximalIdeal S).inertiaDeg R = Module.finrank K L := by
  have := FaithfulSMul.of_field_isFractionRing R S K L
  rw [← sum_ramificationIdx'_mul_inertiaDeg (S := S) K L hp0, IsLocalRing.primesOverFinset_eq S hp0,
    Finset.sum_singleton]

end Ideal
