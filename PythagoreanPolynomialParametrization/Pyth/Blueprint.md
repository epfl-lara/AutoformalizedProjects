# Formalization Blueprint: docs/pyth.tex

- Source: `docs/pyth.tex`
- Target Lean entry file: `Pyth/Main.lean`
- Status: source-backed Lean development with all Lean declarations proved

## Current Rating

- Statement/source coverage: 9/10. The main theorem, obstruction, positive remark, 16-parameter follow-on, general finite-family definitions, cited finite-cover theorem, and non-UFD motivation are represented.
- Proof completeness: theorem declarations are proved; no project-local `sorry`, `admit`, or custom axiom remains.
- Model-readiness: 8/10. Externally cited and motivational material is isolated in `Pyth/Explanatory.lean`.

## Known Scope Gaps

- The full literature-level factorization discussion behind the non-UFD paragraph (`pyth.tex:179-189`) is intentionally not developed beyond the displayed identity, integer-valuedness of the binomial polynomial, and the stated non-UFD result. This is acceptable for this formalization because the paper uses the paragraph only as motivation for why integer-valued polynomial rings behave differently from `ℤ[x]`; it is not used in the obstruction proof or in the construction of the Pythagorean-triple parametrization.
- The externally cited finite-cover theorem (`pyth.tex:138-141`) is proved locally in `Pyth/Explanatory.lean` by clearing denominators and splitting integer inputs into finitely many residue classes.

## Planner Checklist

- [x] Identify definitions and notation that must exist before theorem statements.
- [x] Split large source theorems into Lean-sized lemmas.
- [x] Record source labels/pages/equations for every generated declaration.
- [x] Check local project and Mathlib names before introducing duplicates.
- [x] Verify drafted Lean statements against the source document.
- [x] Add missing source-level intermediate claims that were previously only in prose proof notes.
- [x] Attach the complete source proof text when available, or explicitly record why it is unavailable.
- [x] Record a natural-language proof strategy or source proof pointer for each theorem/lemma.
- [x] Resolve all construction stubs before proof handoff.
- [x] Reorganize Lean files into smaller model-facing proof targets.
- [x] Run independent statement/source verification review after the split.
- [x] Verify the externally cited theorem and all proof targets after independent review approves every source entry.

## Import Plan

Direct external import:
- `Pyth/Basic.lean` imports `Mathlib`.

Local import chain:
- `Pyth/SourceLemmas.lean` imports `Pyth.Basic`.
- `Pyth/Obstructions.lean` imports `Pyth.Basic`.
- `Pyth/IntegerValued.lean` imports `Pyth.SourceLemmas`.
- `Pyth/Positive.lean` imports `Pyth.IntegerValued`.
- `Pyth/Explanatory.lean` imports `Pyth.Basic`.
- `Pyth/Main.lean` imports the Pyth modules as an aggregator.

## Suggested Search Modules

Non-gating modules or namespaces to search while proving. Do not force these into `.lean` imports unless the prover actually needs them.
- `Mathlib.NumberTheory.PythagoreanTriples`
- `Mathlib.Algebra.MvPolynomial.Basic`
- `Mathlib.Algebra.MvPolynomial.Eval`
- `Mathlib.RingTheory.UniqueFactorizationDomain`
- `Mathlib.NumberTheory.SumFourSquares`

## Generated File Layout

- Aggregator entry file: `Pyth/Main.lean`
- Shared definitions: `Pyth/Basic.lean`
- Source proof handoff lemmas: `Pyth/SourceLemmas.lean`
- Integer-coefficient obstruction: `Pyth/Obstructions.lean`
- Four-variable integer-valued parametrization: `Pyth/IntegerValued.lean`
- Positive and 16-parameter parametrizations: `Pyth/Positive.lean`
- Externally cited and explanatory statements: `Pyth/Explanatory.lean`
- Auxiliary assumptions: none.

## Definitions (before theorems)

| Lean name | File | Source concept | Description |
|-----------|------|---------------|-------------|
| `IsPythagoreanTriple` | `Basic.lean` | PT in source | x² + y² = z² |
| `pythagoreanTriples` | `Basic.lean` | set of PTs | {(x,y,z) | x²+y²=z²} |
| `positivePythagoreanTriples` | `Basic.lean` | positive PTs | {(x,y,z) | x,y,z>0, x²+y²=z²} |
| `IntPoly n` | `Basic.lean` | ℤ[x₁,…,xₙ] | `MvPolynomial (Fin n) ℤ` |
| `RatPoly n` | `Basic.lean` | ℚ[x₁,…,xₙ] | `MvPolynomial (Fin n) ℚ` |
| `IsIntValued` | `Basic.lean` | Int(ℤⁿ) | rational poly evaluates to integer at all integer tuples |
| `IntValuedSubring` | `Basic.lean` | Int(ℤⁿ) as a ring | subring of `RatPoly n` used for factorization statements |
| `IntegerValuedPoly` | `Basic.lean` | Int(ℤⁿ) as a type | coercible type of integer-valued rational polynomials |
| `intPolyEval` | `Basic.lean` | evaluation | evaluate integer-coefficient poly at integer tuple |
| `ratPolyEval` | `Basic.lean` | evaluation | evaluate rational-coefficient poly at integer tuple |
| `IntPolyTupleParametrizes` | `Basic.lean` | single k-tuple over ℤ[x] | general `S ⊆ ℤᵏ` image predicate |
| `IntValuedTupleParametrizes` | `Basic.lean` | single k-tuple over Int(ℤⁿ) | general integer-valued image predicate |
| `FiniteIntPolyTupleParametrizes` | `Basic.lean` | finite family over ℤ[x] | finite union of integer-coefficient polynomial tuple images |
| `FiniteIntValuedTupleParametrizes` | `Basic.lean` | finite family over Int(ℤⁿ) | finite union of integer-valued polynomial tuple images |
| `IntPolyParametrizes` | `Basic.lean` | parametrization by ℤ[x] | image of polynomial map equals the set |
| `IntValuedParametrizes` | `Basic.lean` | parametrization by Int(ℤⁿ) | integer-valued + image equals the set |
| `fallingFactorialRatPoly` | `Explanatory.lean` | x(x-1)…(x-k+1) | displayed polynomial in the non-UFD discussion |
| `binomialRatPoly` | `Explanatory.lean` | (x choose k) | rational binomial polynomial |
| `TMap` | `SourceLemmas.lean` | T(a,b,c) | rational map c(a²-b²)/2, cab, c(a²+b²)/2 |
| `IsIntegralTValue` | `SourceLemmas.lean` | integer triples in range of T | all coordinates of `TMap a b c` are integers |
| `PaperParityCondition` | `SourceLemmas.lean` | c≡0 mod 2 or a≡b mod 2 | encoded as `Even c ∨ Even (a - b)` |
| `PositiveTParameters` | `SourceLemmas.lean` | a,b,c positive, a>b, parity condition | source condition for positive PTs |
| `x_var`, `y_var`, `z_var`, `w_var` | `IntegerValued.lean` | variables x,y,z,w | indeterminates in 4-variable rational poly ring |
| `a_param` | `IntegerValued.lean` | a = y+zw | substitution polynomial |
| `b_param` | `IntegerValued.lean` | b = z-yw | substitution polynomial |
| `c_param` | `IntegerValued.lean` | c = 2x-xw | substitution polynomial |
| `f_param` | `IntegerValued.lean` | f in theorem | c·(a²-b²)/2 |
| `g_param` | `IntegerValued.lean` | g in theorem | c·a·b |
| `h_param` | `IntegerValued.lean` | h in theorem | c·(a²+b²)/2 |
| `a_pos_param` | `Positive.lean` | a = y+(1+w)z | positive substitution polynomial |
| `b_pos_param` | `Positive.lean` | b = y | positive substitution polynomial |
| `c_pos_param` | `Positive.lean` | c = x+(1-w)²x | positive substitution polynomial |
| `f_pos_param` | `Positive.lean` | f in positive remark | c_pos·(a_pos²-b_pos²)/2 |
| `g_pos_param` | `Positive.lean` | g in positive remark | c_pos·a_pos·b_pos |
| `h_pos_param` | `Positive.lean` | h in positive remark | c_pos·(a_pos²+b_pos²)/2 |
| `x_sub` | `Positive.lean` | x substitution for 16-param | x₁²+x₂²+x₃²+x₄²+1 |
| `y_sub` | `Positive.lean` | y substitution for 16-param | y₁²+y₂²+y₃²+y₄²+1 |
| `z_sub` | `Positive.lean` | z substitution for 16-param | z₁²+z₂²+z₃²+z₄²+1 |
| `w_sub` | `Positive.lean` | w substitution for 16-param | w₁²+w₂²+w₃²+w₄² |
| `a_16_param` | `Positive.lean` | a = y_sub+(1+w_sub)·z_sub | 16-variable substitution |
| `b_16_param` | `Positive.lean` | b = y_sub | 16-variable substitution |
| `c_16_param` | `Positive.lean` | c = x_sub+(1-w_sub)²·x_sub | 16-variable substitution |
| `f_16_param` | `Positive.lean` | f in 16-param theorem | c_16·(a_16²-b_16²)/2 |
| `g_16_param` | `Positive.lean` | g in 16-param theorem | c_16·a_16·b_16 |
| `h_16_param` | `Positive.lean` | h in 16-param theorem | c_16·(a_16²+b_16²)/2 |

## Source Statement Inventory

### line-104

- Kind: definition block
- Source locator: `docs/pyth.tex:104-128`
- Lean declarations: `IntPolyTupleParametrizes`, `IntValuedTupleParametrizes`, `FiniteIntPolyTupleParametrizes`, `FiniteIntValuedTupleParametrizes`
- File: `Pyth/Basic.lean`
- Formal statement review: The source defines parametrization of `S ⊆ ℤᵏ` by one `k`-tuple of polynomials and by a finite union of such images. The Lean definitions encode `ℤᵏ` as `Fin k → ℤ` and finite families as `Fin m → Fin k → ...`.
- Scope changes: the specialized existing triple predicates remain for the Pythagorean theorem files.
- Statement verification status: added as definitions; no proof obligations.

### line-138

- Kind: externally cited theorem
- Source locator: `docs/pyth.tex:138-141`
- Lean declaration: `single_intValued_parametrization_yields_finite_intPoly_parametrization`
- File: `Pyth/Explanatory.lean`
- Formal statement review: The source says any set of integer tuples parametrized by a single integer-valued tuple is parametrizable by finitely many integer-coefficient tuples. The Lean statement uses the general `Fin k → ℤ` predicates and keeps the same number of variables `n`.
- Scope changes: although the proof is cited from external work and is not used by the paper's main proof, the Lean file proves the statement constructively by clearing denominators and using finitely many residue classes modulo the common denominator.
- Statement verification status: checks in `Pyth/Explanatory.lean`.

### line-179

- Kind: explanatory motivation
- Source locator: `docs/pyth.tex:179-192`
- Lean declarations: `IntValuedSubring`, `IntegerValuedPoly`, `fallingFactorialRatPoly`, `binomialRatPoly`, `binomialRatPoly_intValued`, `fallingFactorial_eq_factorial_mul_binomialRatPoly`, `integerValued_polynomial_ring_not_uniqueFactorization`
- Files: `Pyth/Basic.lean`, `Pyth/Explanatory.lean`
- Formal statement review: The source says `Int(ℤ)` lacks unique factorization and gives the displayed identity `x(x-1)…(x-k+1)=k! * (x choose k)`. The Lean file records the ring/type needed to state the non-UFD claim, the displayed polynomials, the identity, and integer-valuedness of the binomial polynomial.
- Scope changes: the detailed source discussion of factorization behavior is intentionally out of scope for the Pythagorean parametrization results. The paper does not use this proof later and points readers to separate references for factorization properties of integer-valued polynomial rings; the Lean file nevertheless proves the displayed identity, integer-valuedness statement, and stated non-UFD theorem.
- Statement verification status: checks in `Pyth/Explanatory.lean`.

### line-98

- Kind: introductory standard fact
- Source locator: `docs/PythagoreanPolynomialParametrization/pyth.tex:98-102`
- Planned Lean declarations: `pythagoreanTriple_two_integer_polynomial_families`
- File: `Pyth/SourceLemmas.lean`
- Dependencies: `IsPythagoreanTriple`
- Formal statement review: The source says every Pythagorean triple is either in the image of `(c(a²-b²), 2cab, c(a²+b²))` or in the image of `(2cab, c(a²-b²), c(a²+b²))`, with `a,b,c ∈ ℤ`. The Lean statement records this as an iff, adding the converse that each family value is Pythagorean; the converse is mathematically immediate and useful for proof handoff.
- Source qualifiers:
  - Mathematical object class: integer triples and integer-coefficient polynomial families
  - Quantifier order: ∀ x y z, PT(x,y,z) iff ∃ a b c, first family or second family
  - Parameter domain: a,b,c ∈ ℤ
  - Output codomain: ℤ³
  - Equality/image condition: union of two polynomial images
  - Side conditions: none
- Lean coverage: exact for the standard fact, with an intentional strengthened converse
- Scope changes: the paper cites the result rather than proving it; Lean keeps it as a proof obligation
- Statement verification status: locally reviewed; awaiting independent review
- Complete source proof: not included in the paper; source points to `HlaSch79ZT`
- Source proof / prover notes: Use Mathlib's Pythagorean triple classification if available. Otherwise prove via the standard primitive/nonprimitive classification and absorb signs into `a`, `b`, and `c`.

### line-143

- Kind: remark
- Source locator: `docs/PythagoreanPolynomialParametrization/pyth.tex:143-146`
- Planned Lean declarations: `no_int_poly_parametrization`
- File: `Pyth/Obstructions.lean`
- Dependencies: `IntPoly`, `IntPolyParametrizes`, `pythagoreanTriples`
- Formal statement review: The source states "There do not exist f,g,h ∈ ℤ[x₁,…,xₙ] for any n such that (f,g,h) parametrizes the set of PTs." The Lean statement quantifies over n and the triple (f,g,h), asserting no such parametrization exists.
- Source qualifiers:
  - Mathematical object class: multivariate polynomials with integer coefficients
  - Quantifier order: ∀n, ¬∃(f,g,h)
  - Parameter domain: n ∈ ℕ (number of variables)
  - Output codomain: ℤ³ (the parametrized set)
  - Equality/image condition: S = image of polynomial map
  - Side conditions: none
- Lean coverage: exact statement skeleton
- Scope changes: none
- Statement verification status: locally reviewed; awaiting independent review after file split
- Complete source proof: Available in source lines 146-172.
- Source proof / prover notes: The proof uses UFD property of ℤ[x], takes d = gcd(g,h), divides through to get primitive triple of polynomials (φ,ψ,θ), factors φ² = (θ+ψ)(θ-ψ), shows gcd is 1 (not 2, using (3,4,5)), deduces both factors are squares, writes θ = (s²+t²)/2 and ψ = (s²-t²)/2, then shows ψ is divisible by 2, contradicting (4,3,5).
- Source proof excerpt: Suppose $(f,g,h)$ parametrizes the \Pt s. As $\intz[\x]$ is a unique factorization domain, there exists $d=\gcd(g,h)$ (unique up to sign), which also divides $f$, since $f^2+g^2=h^2$. Let $\varphi=f/d$, $\psi=g/d$ and $\theta=h/d$. Then $$\varphi^2= \theta^2 - \psi^2=(\theta+\psi)(\theta-\psi)$$ and $\gcd((\theta+\psi), (\theta-\psi))$ is either $1$ or $2$, but it can't be $2$, because there exist \Pt s with odd first coordinate such as $(3,4,5)$. Since $(\theta+\psi)$ and $(\theta-\psi)$ are co-prime and their product is a square, $(\theta+\psi)$ and $(\theta-\psi)$ are either both squares, or both $(-1)$ times a square, and we can get rid of the latter alternative by retro-actively changing the sign of the polynomial $d$, if necessary. So there exist polynomials $s$ and $t$ with $(\theta+\psi)=s^2$ and $(\theta-\psi)=t^2$, and therefore $$\theta= {s^2+t^2\over 2}\quad \hbox{\rm and}\quad \psi = {s^2-t^2\over 2}.$$ Since $s^2-t^2 =(s+t)(s-t)$ is divisible by $2$, it is actually divisible by $4$, so that $\psi $ is divisible by $2$, which contradicts the existence of \Pt s with odd second coordinate such as $(4,3,5)$.

There do not exist $f,g,h\in \intz[x_1,\ldots,x_n]$ for any $n$ such that $(f,g,h)$ parametrizes the set of \Pt s.

### line-194

- Kind: theorem
- Source locator: `docs/PythagoreanPolynomialParametrization/pyth.tex:194-203`
- Planned Lean declarations:
  - `TMap` (definition)
  - `IsIntegralTValue` (definition)
  - `PaperParityCondition` (definition)
  - `pythagorean_iff_mem_TMap_range` (source handoff lemma)
  - `TMap_integral_iff_parity` (source handoff lemma)
  - `parity_condition_parametrized` (source handoff lemma)
  - `f_param_intValued` (lemma)
  - `g_param_intValued` (lemma)
  - `h_param_intValued` (lemma)
  - `exists_int_valued_parametrization` (main theorem)
- Files:
  - `Pyth/SourceLemmas.lean`
  - `Pyth/IntegerValued.lean`
- Dependencies: `RatPoly`, `IsIntValued`, `IntValuedParametrizes`, `pythagoreanTriples`, `TMap`, `PaperParityCondition`, `f_param`, `g_param`, `h_param`
- Formal statement review: The source states existence of f,g,h ∈ Int(ℤ⁴) parametrizing all PTs, with explicit formulas. The Lean statement constructs these as rational polynomials and proves they are integer-valued and parametrize the set.
- Source qualifiers:
  - Mathematical object class: integer-valued polynomials (rational coefficients, integer output on integer inputs)
  - Quantifier order: ∃(f,g,h)
  - Parameter domain: 4 variables (x,y,z,w) ranging over ℤ
  - Output codomain: ℤ³
  - Equality/image condition: S = image of polynomial map
  - Side conditions: each polynomial is integer-valued
- Lean coverage: exact statement skeleton for the explicit witness and image equality; proof decomposition now separately records the source's range and parity arguments
- Scope changes: none
- Statement verification status: locally reviewed; awaiting independent review after file split
- Complete source proof: Available in source lines 203-238.
- Source proof / prover notes: The proof first shows every primitive PT is of form T₁(a,b) or T₂(a,b). Since 2·T₂(a,b) = T₁(a+b,a-b), every primitive PT is c·T₁(a,b)/2 with c∈{1,2}. Define T(a,b,c) = (c(a²-b²)/2, cab, c(a²+b²)/2). Every PT is T(a,b,c) for a,b,c∈ℤ. T(a,b,c)∈ℤ³ iff c≡0 (mod 2) or a≡b (mod 2). The condition is parametrized by (y+zw, z-yw, 2x-xw). If w even then c≡0 (mod 2); if w odd then a≡b (mod 2). All such triples occur (set w=0 or w=1). Substituting gives the parametrization.
- Source proof excerpt: Every \Pt\ $(x,y,z)$ with $\gcd(x,y,z)=1$ and $z>0$ is either of the form $$T_1(a,b)=(a^2-b^2,\; 2ab,\; a^2+b^2),$$ or of the form $$T_2(a,b)=(2ab,\; a^2-b^2,\; a^2+b^2),$$ with $a,b\in \intz$. Since $$ 2\, T_2(a,b) = T_1(a+b,\> a-b),$$ every \Pt\ with $\gcd(x,y,z)=1$ and $z>0$ is of the form $c\, T_1(a,b)/2$ with $c\in\{1,2\}$ and $a,b\in \intz$. Let $$T(a,b,c)= \left({c(a^2-b^2)\over 2},\; cab,\; {c(a^2+b^2)\over 2}\right).$$ Then every \Pt\ is of the form $T(a,b,c)$ with $a,b,c\in\intz$. Also, every triple $T(a,b,c)$ with $a,b,c\in\intz$ is a rational solution of $x^2+y^2=z^2$. So, the set of \Pt s is precisely the set of integer triples in the range of the function $T\colon \intz^3\rightarrow \ratq^3$. Now $T(a,b,c)\in \intz^3$ if and only if $c\congr 0$ mod $2$ or $a\congr b$ mod $2$. Triples $(a,b,c)\in\intz^3$ satisfying this condition can be parametrized by (for instance) $$(y+zw,\; z-yw,\; 2x-xw).$$ Indeed, if $w$ is even then $c\congr 0$ mod $2$, if $w$ is odd then $a\congr b$ mod $2$, and all $(a,b,c)$ satisfying either congruence actually occur for some $(x,y,z,w)\in\intz^4$, as can be seen by setting $w=0$ or $w=1$. Therefore, substituting $y+zw$ for $a$, $z-yw$ for $b$, and $2x-xw$ for $c$ in $T(a,b,c)$ yields a parametrization of the set of \Pt s by a triple of integer-valued polynomials.

There exist $f,g,h\in \Int(\intz^4)$ such that $(f,g,h)$ parametrizes the set of \Pt s (as the variables range through $\intz$) namely, $$\displaylines{ \Biggl( {(2x-xw)((y+zw)^2-(z-yw)^2)\over 2},\hfill\cr \hfill \vphantom{\Biggl)} (2x-xw)(y+zw)(z-yw), \hfill\cr \hfill \vphantom{\Biggl(} {(2x-xw)((y+zw)^2+(z-yw)^2)\over 2}\Biggr).\cr }$$

### line-240

- Kind: remark
- Source locator: `docs/PythagoreanPolynomialParametrization/pyth.tex:240-253`
- Planned Lean declarations:
  - `PositiveTParameters` (definition)
  - `positive_T_parameters_parametrized` (source handoff lemma)
  - `f_pos_param_intValued` (lemma)
  - `g_pos_param_intValued` (lemma)
  - `h_pos_param_intValued` (lemma)
  - `positive_triples_parametrization` (main theorem)
  - `int_nonneg_iff_four_squares` (source handoff lemma)
  - `int_positive_iff_four_squares_add_one` (source handoff lemma)
  - `x_sub`, `y_sub`, `z_sub`, `w_sub` (16-variable substitution defs)
  - `a_16_param`, `b_16_param`, `c_16_param` (16-variable intermediate defs)
  - `f_16_param`, `g_16_param`, `h_16_param` (16-variable polynomial defs)
  - `exists_16_param_parametrization` (follow-on theorem)
- Files:
  - `Pyth/SourceLemmas.lean`
  - `Pyth/Positive.lean`
- Dependencies: `RatPoly`, `IsIntValued`, `positivePythagoreanTriples`, `PositiveTParameters`, `f_pos_param`, `g_pos_param`, `h_pos_param`, four-square handoff lemmas
- Formal statement review: The source states that positive PTs are parametrized by a specific triple of integer-valued polynomials, with x,y,z>0 and w≥0. It also mentions the 4-square theorem conversion to 16 integer parameters. The Lean statement captures the existence of such a parametrization.
- Source qualifiers:
  - Mathematical object class: integer-valued polynomials
  - Quantifier order: ∃(f,g,h)
  - Parameter domain: 4 variables, but with positivity constraints (x,y,z>0, w≥0)
  - Output codomain: positive integers in ℤ³
  - Equality/image condition: S = image of polynomial map restricted to positive inputs
  - Side conditions: each polynomial is integer-valued
  - Follow-on claims: can convert to 16 integer parameters using 4-square theorem
- Lean coverage: exact statement skeleton for the restricted 4-variable parametrization and the 16-variable unrestricted follow-on; proof decomposition now separately records the positive-parameter and four-square arguments
- Scope changes: none
- Statement verification status: locally reviewed; awaiting independent review after file split
- Complete source proof: Available in source lines 253-270.
- Source proof / prover notes: The proof uses the same T(a,b,c) as the main theorem. Positive PTs are integer triples in the range of T with positive coordinates. T(a,b,c) is positive iff a,b,c are positive integers with a>b and either c≡0 (mod 2) or a≡b (mod 2). Such triples are parametrized by (y+(1+w)z, y, x+(1-w)²x) with x,y,z>0 and w≥0. Substituting gives the parametrization. The 4-square theorem converts to 16 integer parameters.
- Source proof excerpt: As in the proof of the theorem above, the positive \Pt s are precisely the triples with positive integer coordinates in the range of the function $T\colon \intz^3\rightarrow \ratq^3$. Now $T(a,b,c)$ is a positive triple if and only if $a,b,c$ are positive integers with $a> b$ and either $c\congr 0$ mod $2$ or $a\congr b$ mod $2$. Such triples $(a,b,c)$ are parametrized by (for instance) $$(y+(1+w)z,\> y,\> x+(1-w)^2x)$$ with $x,y,z>0$ and $w\ge 0$. Therefore substituting $y+(1+w)z$ for $a$, $y$ for $b$ and $x+(1-w)^2x$ for $c$ in $T(a,b,c)$ gives a parametrization of positive \Pt s where $w$ ranges through non-negative integers and $x,y,z$ through positive integers. The 4-square theorem allows us to convert this to a parametrization with 16 integer parameters.

The set of positive \Pt s is parametrized by $$\displaylines{ \Biggl( {(x+(1-w)^2x)((y+(1+w)z)^2-y^2)\over 2} \vphantom{\Biggr)},\hfill\cr \hfill\vphantom{\Biggl({1\over f}} (x+(1-w)^2x)(y+(1+w)z)y, \hfill\cr \hfill \vphantom{\Biggl(} {(x+(1-w)^2x)((y+(1+w)z)^2+y^2)\over 2}\Biggr).\cr }$$ where $x,y,z$ range through the positive integers and $w$ through the non-negative integers. From this formula, a parametrization of positive \Pt s with integer parameters can be obtained (using the 4-square theorem) by replacing $w$ by $w_1^2+w_2^2+w_3^2+w_4^2$ and $x,\,y,\,z$ by $x_1^2+x_2^2+x_3^2+x_4^2+1$, $y_1^2+y_2^2+y_3^2+y_4^2+1$, and $z_1^2+z_2^2+z_3^2+z_4^2+1$, respectively.
