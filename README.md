# Parametrization of Pythagorean Triples by Polynomials

Lean 4 autoformalization experiment for Sophie Frisch and Leonid
Vaserstein's paper, *Parametrization of Pythagorean triples by a single
triple of polynomials*.

The formalization was produced with EPFLemma using Kimi K2.6 and then proved
through the managed Lean workflow. The main Lean file is:

- `Pyth/Main.lean`

The workflow logs are preserved in:

- `logs/`

## Formalization Status

The current formalization is proof-complete in Lean:

- `lake build` succeeds.
- There are no `sorry` or `admit` placeholders in `Pyth/Main.lean`.
- The final prover run is `logs/prove-20260428T211646Z-pid18850.log`.
- Earlier logs show several failed/partial proof-repair attempts, mainly around
  the UFD/gcd argument for the non-parametrizability theorem.

## What Was Formalized

The Lean development covers the main mathematical claims from `pyth.tex`.

### 1. No integer-coefficient single parametrization

Lean theorem:

- `no_integer_polynomial_parametrization`

Source claim:

- There do not exist `f, g, h in Z[x_1, ..., x_n]`, for any finite `n`, such
  that `(f, g, h)` parametrizes all Pythagorean triples.

Lean status:

- Fully proved.
- Uses bundled multivariate polynomials
  `MvPolynomial (Fin n) Z`.
- This is the strongest-mode part of the formalization: the theorem is stated
  directly with polynomial objects, not just functions.

### 2. Integer-valued 4-variable parametrization

Lean declarations:

- `f_param`, `g_param`, `h_param`
- `param_integer_valued`
- `integer_valued_parametrization`

Source claim:

- The paper gives one triple of integer-valued rational polynomials in four
  variables whose image is exactly the set of all Pythagorean triples.

Lean status:

- Fully proved at the level of evaluation and image equality.
- The formulas are shown to evaluate to integers on all integer inputs.
- The image is proved to be exactly the set of integer triples satisfying
  `x^2 + y^2 = z^2`.

### 3. Positive Pythagorean triples

Lean declarations:

- `f_pos`, `g_pos`, `h_pos`
- `positive_param_integer_valued`
- `positive_pythagorean_parametrization`

Source claim:

- The paper gives a parametrization of positive Pythagorean triples using
  positive parameters `x, y, z` and a nonnegative parameter `w`.

Lean status:

- Fully proved.
- The constrained parameter domain is represented explicitly:
  `x > 0`, `y > 0`, `z > 0`, `w >= 0`.
- The image equality for positive Pythagorean triples is proved.

### 4. Four-square unrestricted positive parametrization

Lean declarations:

- `fourSquares`, `fourSquaresPos`
- `f_pos16`, `g_pos16`, `h_pos16`
- `positive_pythagorean_parametrization_integer_parameters`

Source claim:

- The positive-parametrization domain can be converted to unrestricted integer
  parameters using the four-square theorem.

Lean status:

- Fully proved.
- The unrestricted parameter space is represented as `Fin 16 -> Z`.

## Weaker or Missing Links

The formalization is complete as a Lean proof of the main statements, but a few
definitions are weaker than the paper's algebraic presentation.

### Weaker definition of integer-valued polynomials

In the paper, integer-valued polynomials are elements of:

```text
Int(Z^n) = { f in Q[x_1, ..., x_n] | f(a) in Z for all a in Z^n }
```

In Lean, the integer-valued property is represented extensionally as:

```lean
def IntegerValued4 (F : Z -> Z -> Z -> Z -> Q) : Prop :=
  forall x y z w : Z, exists n : Z, (n : Q) = F x y z w
```

This proves the displayed formulas take integer values on integer inputs, but
it does not bundle them as elements of a formal ring `Int(Z^4)`.

### Rational polynomial object is not bundled

The formulas `f_param`, `g_param`, `h_param`, `f_pos`, `g_pos`, and `h_pos` are
defined as rational-valued functions on integers, not as explicit elements of
`MvPolynomial (Fin 4) Q`.

What is proved:

- evaluation is integer-valued;
- the image is exactly the intended set of triples.

What is not proved:

- the formulas are bundled rational polynomial objects;
- they belong to a formal subtype/subring of integer-valued polynomials;
- the ring structure of `Int(Z^n)` is developed.

### Bibliographic and surrounding prose not formalized

The Lean file focuses on the main theorem-level mathematical content. It does
not formalize:

- the historical/background discussion;
- bibliographic references;
- the example of non-unique factorization in `Int(Z)`;
- the general cited result that every single integer-valued parametrization
  gives a finite collection of integer-coefficient polynomial parametrizations.

## Overall Assessment

The theorem formalization is strong and proof-complete for the main results:

- no integer-coefficient single parametrization;
- existence of the explicit integer-valued parametrization of all triples;
- positive-triple parametrization;
- four-square unrestricted positive parametrization.

The main limitation is definitional fidelity: the Lean development proves the
right evaluation and image properties, but it does not yet model
integer-valued polynomials as first-class algebraic objects in a formal
`Int(Z^n)` ring.

In short: the core theorem content is formalized and verified; the remaining
gap is mostly packaging the rational formulas as bundled integer-valued
polynomial objects rather than rational-valued functions with an
integer-valuedness predicate.
