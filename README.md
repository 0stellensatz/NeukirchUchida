# The Neukirch–Uchida theorem in Lean

A complete formalization, in Lean 4 and Mathlib, of the **Neukirch–Uchida theorem**: a number
field is determined by its absolute Galois group. More precisely, every topological isomorphism
between the absolute Galois groups of two number fields is induced by a unique isomorphism of
their separable closures.

The proof contains no `sorry` and depends only on the standard axioms (`propext`, `Quot.sound`,
`Classical.choice`). It is a solution to the `neukirch_uchida` problem of
[lean-eval](https://github.com/leanprover/lean-eval) and passes its comparator, which checks the
proof with both the Lean kernel and the independent `nanoda` kernel.

## The statement

```lean
theorem neukirch_uchida {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
```

Given separable closures $K_i'/K_i$ and a topological isomorphism
$\phi : G_{K_1} \to G_{K_2}$, there is a unique field isomorphism $\sigma : K_2' \to K_1'$
carrying $K_2$ onto $K_1$ with $\phi(g) = \sigma^{-1} g \sigma$ for all $g$.

## Building and checking

The toolchain is pinned to Lean `v4.36.0` and Mathlib `v4.36.0`.

```sh
lake exe cache get   # fetch prebuilt Mathlib
lake build           # build Challenge, Solution and Submission
lake test            # run the lean-eval comparator (requires bubblewrap)
```

`lake build` reports a single warning: the intentional `sorry` in `Challenge.lean`.

## Layout

| Path | Contents |
| --- | --- |
| `Challenge.lean` | The problem statement, as posed by lean-eval. |
| `Solution.lean` | The same statement, proved from `Submission`. |
| `config.json`, `WorkspaceTest.lean` | Comparator configuration and the test driver run by `lake test`. |
| `Submission/NU/NeukirchUchida/` | The global argument and the final assembly. |
| `Submission/NU/LocalTheory/` | Recovery of decomposition groups from the bare profinite group $G_K$. |
| `Submission/NU/AEJ/` | Arason–Elman–Jacob, *Rigid elements, valuations, and realization of Witt rings*, J. Algebra 110 (1987), §§1–3. |
| `Submission/NU/Chebotarev/` | The Chebotarev density theorem (Dirichlet density form). |
| `Submission/NU/LCFT/` | Local class field theory: Lubin–Tate theory, the local fundamental class, finite local reciprocity. |
| `Submission/NU/Compat.lean` | Compatibility lemmas for the current Mathlib API. |

The development is about 110,000 lines. Docstrings refer to labels such as `prop:cyclic` or
`thm:packet` in the informal blueprints that guided the formalization; those documents are not part
of this repository.

## Proof sketch

Fix $\Omega = \overline{\mathbb{Q}}$, regard number fields as subfields of $\Omega$, and write
$G_F = \mathrm{Gal}(\Omega/F) \le G_{\mathbb{Q}}$. The core theorem
(`NU.NeukirchUchida.neukirchUchida`) says that every topological isomorphism
$\theta : G_{F_1} \to G_{F_2}$ is $g \mapsto \alpha^{-1} g \alpha$ for a unique
$\alpha \in G_{\mathbb{Q}}$ with $\alpha(F_2) = F_1$; the statement above follows by transporting
along isomorphisms of separable closures.

As in the classical proof there is a local part, which recovers decomposition groups and local
invariants from $G_F$, and a global part, which turns this local information into an element of
$G_{\mathbb{Q}}$. The two meet in `NeukirchUchida/LocalInterface.lean`:

- **(L1, L2)** $\theta$ maps the decomposition group of each prime $P$ of $\Omega$ onto the
  decomposition group of a unique prime $P'$, and $P \mapsto P'$ is a $\theta$-equivariant
  bijection;
- **(L3)** $P$ and $P'$ lie over the same rational prime and have the same $e$ and $f$ over
  $\mathbb{Q}$;
- **(L4)** $\theta$ maps arithmetic Frobenius lifts at $P$ to arithmetic Frobenius lifts at $P'$.

Both parts depart from the classical route. Neukirch characterizes decomposition groups through
Galois cohomology and local class field theory, and Uchida then reconstructs the field itself.
Here decomposition groups are detected by mod-$\ell$ cup products and valuation theory, and the
reconstruction of the field is replaced by a linear-algebra argument about finite Galois quotients.

### Local part: decomposition groups from cup products

*(`LocalTheory/`, `AEJ/`)*

Let $G$ be a profinite group, $U \le G$ open normal, and $\ell$ an odd prime. A
2-dimensional subspace $P \subseteq U^{ab}/\ell$ is a **packet** if every pair of characters
$a, b : U \to \mathbb{Z}/\ell$ with $a \cup b = 0$ in $H^2(U, \mathbb{Z}/\ell)$ restricts to a
linearly dependent pair on $P$. Let $\mathcal{D}_\ell(G)$ be the set of closed, non-procyclic
subgroups $H \le G$ such that for cofinally many $U$ the image of $H$ in $G/U$ is the stabilizer
of a packet under conjugation. This definition is purely group-theoretic, and
`NU.LocalTheory.reconstruction` shows that $\bigcup_\ell \mathcal{D}_\ell(G_K)$ is exactly the set
of decomposition groups of finite places of $\overline{K}/K$. More precisely, $\mathcal{D}_\ell$
consists of those of residue characteristic $\neq \ell$.

- **Packets are local planes.** Over a number field $M \ni \zeta_\ell$, Kummer theory identifies
  $G_M^{ab}/\ell$ with the dual of $M^\times/M^{\times\ell}$, and $\chi_a \cup \chi_b = 0$ exactly
  when $b$ is a norm from $M(\sqrt[\ell]{a})$. The packet theorem says the packets are exactly the
  *local planes* of places $v \nmid \ell$, namely the characters killing the principal units at $v$.
  - **Local planes are packets.** This follows from a tame symbol computation in $M_v$.
  - **Packets are local planes.** The packet condition makes the dual pair of characters
    *alternating*: $p(x)q(y) = p(y)q(x)$ whenever $x + y = 1$. The Arason–Elman–Jacob theorem on
    rigid elements then produces a valuation, which in a number field is a prime.

  No Merkurjev–Suslin, local Tate duality or Brauer groups are needed.
- **Stabilizers.** By weak approximation distinct places have distinct local planes, so the
  stabilizer of the plane of $w$ is the decomposition group $D_w$.
- **Passing to the limit.** The criterion only needs to be evaluated at levels $U$ inside the
  mod-$\ell$ cyclotomic kernel, and these are cofinal. So no cyclotomic character has to be
  recovered. For $H \in \mathcal{D}_\ell(G_K)$, the places matching $H$ at each level form
  nonempty finite sets, because non-cyclic decomposition groups only occur above ramified primes.
  König's lemma then yields a place of $\overline{K}$ whose decomposition group is $H$.
- **Distinctness.** Distinct places have distinct decomposition groups by F. K. Schmidt's theorem:
  a field that is henselian for two independent valuations is separably closed. This gives the
  bijection in (L1); equivariance is formal.

### Local invariants

*(`NeukirchUchida/LocalInvariants.lean`)*

(L3) and (L4) are proved with the help of the global isomorphism $\theta$ and the packets above,
rather than intrinsically from the local Galois group.

- **Residue characteristic.** The odd primes $\ell$ with $D_P \in \mathcal{D}_\ell$ are exactly
  those different from the residue characteristic $p$, so $\theta$ preserves $p$.
- **Cyclotomic characters.** On a local packet plane an element $g \in D_P$ acts by a triangular
  matrix with diagonal $(1, \chi_\ell(g))$. Hence $\theta$ preserves the mod-$\ell$ cyclotomic
  character on decomposition groups, for every odd $\ell \neq p$.
- **Inertia and Frobenius.** A Chebotarev argument shows that for every prime power $\lambda^m$
  there are infinitely many primes $\ell$ with $\lambda^m \mid \mathrm{ord}_\ell(q)$. It follows
  that $g \in D_P$ acts on the residue field as $x \mapsto x^{p^A}$ if and only if
  $\chi_\ell(g) \equiv p^A \pmod{\ell}$ for all odd $\ell \neq p$. So $\theta$ preserves inertia,
  Frobenius lifts, the residue degree $f$ and the residue norm $q = p^f$.
- **Local degree.** The local degree $n = [K_v : \mathbb{Q}_p]$ is computed from
  $\dim H^1(G_{K_v}, \mathbb{F}_p) = 1 + n + \delta$, where $\delta = 1$ exactly when
  $\mu_p \subset K_v$.
  - This formula comes from the structure of $K_v^\times$ together with local class field theory
    (Lubin–Tate theory and finite local Artin maps).
  - Comparing these dimensions for corresponding open subgroups of index $m \ge 3$ forces
    $n_1 = n_2$, with no Euler characteristic formula needed. Then $e = n/f$.

### Global part

*(`NeukirchUchida/`)*

1. **Normal fields are fixed** (`ChebotarevContainment.lean`; this is Neukirch's classical step).
   The field corresponding to $K \supseteq F_1$ is the fixed field of $\theta(G_K)$. By (L3),
   corresponding fields have the same rational primes with a degree-one factor. Combined with the
   Chebotarev density theorem, this gives $\theta(G_N) = G_N$ for every finite Galois $N/\mathbb{Q}$
   containing $F_1$ and $F_2$. So $\theta$ induces isomorphisms
   $\theta_N : \mathrm{Gal}(N/F_1) \to \mathrm{Gal}(N/F_2)$.

2. **Cyclic quotients are induced by conjugation** (`CyclicStep.lean`). Suppose these groups are
   cyclic, with generator $s$.
   - Chebotarev gives a prime $P$ of absolute degree one ($e = f = 1$ over $\mathbb{Q}$),
     unramified in $N$, and a Frobenius lift $\varphi \in D_P$ that maps to $s$.
   - Degree one means that the full decomposition group of $P$ over $\mathbb{Q}$ lies in $G_{F_1}$,
     so $G_{F_1} = G_N D_P$.
   - By (L1)–(L4), $P'$ again has degree one and lies over the same rational prime, and
     $\theta(\varphi)$ is a Frobenius lift at $P'$. So $G_{F_2} = G_N D_{P'}$.
   - Primes over the same rational prime are conjugate, so $P' = \alpha^{-1} P$ for some
     $\alpha \in G_{\mathbb{Q}}$.
   - Comparing the two product decompositions shows $\alpha(F_2) = F_1$ and
     $\theta_N(s) = \alpha^{-1} s \alpha$. Hence $\theta_N$ is conjugation by $\alpha$.

3. **A regular auxiliary extension** (`RegularKernel.lean`). Let $N/\mathbb{Q}$ be finite Galois
   with group $G$, and let $p$ be an odd prime. Then there is a finite Galois $M/\mathbb{Q}$
   containing $N$ such that $A = \mathrm{Gal}(M/N)$ is the regular module $\mathbb{F}_p[G]$, with
   conjugation acting by left translation.
   - Kummer theory over $N(\mu_p)$, with an eigenspace projector for the cyclotomic character,
     produces a cyclic degree-$p$ extension $L/N$. It is ramified at one prime $v$ above a
     completely split rational prime, and completely split at all other $G$-conjugates of $v$.
   - $M$ is the compositum of the $G$-conjugates of $L$.

4. **Every finite quotient is induced by conjugation** (`FiniteConjugacy.lean`). Take $p > |G|$
   and $M$ as in step 3. As $M/\mathbb{Q}$ is Galois, $\theta$ induces $\theta_M$.
   - $\theta_M$ restricts to an automorphism $\tau$ of $A = \mathbb{F}_p[G]$. It is semilinear with
     respect to $\theta_N$: $\tau(g\lambda) = \theta_N(g)\,\tau(\lambda)$ for
     $g \in \mathrm{Gal}(N/F_1)$.
   - For each $\lambda \neq 0$ in $A$ the extension $M/M^{\langle\lambda\rangle}$ is cyclic. Step 2,
     applied to the fields corresponding to $M^{\langle\lambda\rangle}$, gives $h_\lambda \in G$
     with $\tau(\lambda) = h_\lambda \lambda$.
   - So $A$ is the union of the $|G| < p$ subspaces $\{x : \tau(x) = hx\}$. An
     $\mathbb{F}_p$-vector space is not a union of fewer than $p$ proper subspaces, so a single $h$
     works on all of $A$.
   - Faithfulness of the regular representation then gives $\theta_N(g) = h g h^{-1}$ for all $g$.

   Steps 2–4 take the place of Uchida's reconstruction of the field: instead of recovering
   $F^\times$ and its addition, they show directly that each $\theta_N$ is a conjugation.

5. **Compactness and uniqueness** (`Compactness.lean`).
   - For each finite Galois level $N$, the set of $\alpha \in G_{\mathbb{Q}}$ with
     $\alpha(F_2) = F_1$ that induce $\theta_N$ is nonempty and clopen, and these sets shrink as
     $N$ grows. By compactness of $G_{\mathbb{Q}}$ some $\alpha$ lies in all of them, so it induces
     $\theta$.
   - Two such elements differ by an element centralizing the open subgroup $G_{F_1}$, and these
     centralizers in $G_{\mathbb{Q}}$ are trivial.

### Supporting theories

The Chebotarev density theorem (`Chebotarev/`) is proved from scratch in its Dirichlet-density
form, by Deuring's reduction to the cyclic case and field crossing with cyclotomic extensions. The
cyclotomic case uses ray class groups and Weber $L$-series, without reciprocity. Local class field
theory (`LCFT/`) is developed through Lubin–Tate theory and Tate's abstract reciprocity theorem; in
the main proof it is used mainly for the local degree computation above.

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
