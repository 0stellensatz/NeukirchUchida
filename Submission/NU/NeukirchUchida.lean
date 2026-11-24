import Submission.NU.NeukirchUchida.Main

/-!
# The Neukirch–Uchida theorem

Final assembly: the pointed theorem (every topological isomorphism `G_{F₁} ≃ G_{F₂}` of absolute
Galois groups of number fields inside a fixed `Ω = closure of ℚ` is conjugation by a unique
`α ∈ G_ℚ` with `α(F₂) = F₁`), the outer form, and the transport to arbitrary chosen separable
closures. The global argument uses `NU.LocalTheory`, `NU.Chebotarev` and `NU.LCFT` only through
the interface in `NU.NeukirchUchida.LocalInterface`.
-/
