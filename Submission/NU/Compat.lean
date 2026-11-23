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
    Ideal.finiteQuotientOfFreeOfNeBot _ (mt Ideal.eq_bot_of_comap_eq_bot hp)
  have : Finite ((p.under R).ResidueField) := IsLocalization.finite _
    (nonZeroDivisors (R ⧸ p.under R))
  infer_instance
