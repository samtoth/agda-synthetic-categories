# Contributing

> 🚧 This document is currently under construction. 🚧

## Mixfix operators

We follow
[the agda-unimath guidelines for mixfix operators](https://unimath.github.io/agda-unimath/MIXFIX-OPERATORS.html),
with some extensions.

### Full table of precedences

| Precedence level | Operators                                                                                                                                                         |
| ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 50               | Unary nonparametric operators                                                                                                                                     |
| 45               | Arithmetic exponential operators                                                                                                                                  |
| 43               | Arithmetic modulo operators                                                                                                                                       |
| 42               | Arithmetic division operators                                                                                                                                     |
| 40               | Arithmetic multiplication operators                                                                                                                               |
| 36               | Arithmetic subtraction operators                                                                                                                                  |
| 35               | Arithmetic addition operators                                                                                                                                     |
| 30               | Arithmetic relational operators                                                                                                                                   |
| 27               | Nonparametric pairing operators: `_:≥:_`                                                                                                                          |
| 25               | Parametric unary operators: `¬_`, `_h⁻¹`, `_e⁻¹`, `_q⁻¹`, `id:_`, `fst:_`, `refl:_`...                                                                            |
| 20               | Parametric exponentiative operators: `⟨_,_⟩`,                                                                                                                     |
| 17               | Left homotopy whiskering `_▸_`, `_▸e⁻¹_`                                                                                                                          |
| 16               | Right whiskering: `_◂_`, `_◂e⁻¹_`                                                                                                                                 |
| 15               | Parametric multiplicative operators: `_×_`,`_*_`, `_□_`. Composition operators: `_∘_`, `_∘[_]_`. Concatenation operators: `_∙_`, `_∙e_`, `_∙h_`, `_∙q_`, `_∙iff_` |
| 10               | Parametric additive operators: `_⊎_`. Monadic bind operators.                                                                                                     |
| 6                | Parametric relational operators: `_＝_`, `_~_`, `_≃_`, `_≊_`, `_↔_`, `_⊥_`, `_∈_`                                                                                |
| 5                | Directed function-like formation operators: `_→∗_`, `_⇒_`                                                                                                         |
| 3                | Parametric pairing operators: `_,_`, `_∷_`                                                                                                                        |
| 2                | Semantic brackets: `⟦_⟧₀`, `⟦_⟧₁`                                                                                                                                 |
| 0-1              | Reasoning syntaxes                                                                                                                                                |
| -∞               | Function type formation: `_→_`                                                                                                                                    |

### Wrappers for explicit type parameters

> **Note.** This is an experimental guideline. We invite you to try it out yourself
> and report any experience you have with it.

Sometimes Agda needs help inferring certain type parameters of a generic
construction. Instead of writing `id {A = X}`, we use a typed wrapper `id: X`, which
is both more aesthetic and avoids using the local name of the implicit type
parameter. To make these wrappers as ergonomic as possible we give guidelines for
defining them below.

- **Fixity.** If the wrapper has a single explicit type parameter that is expected to
  primarily be used by itself, we declare it as a unary prefix operator with
  precedence level 25:

  ```agda
  infix 25 id:_
  ```

  This lets us write `id: fibre f y` instead of `id: (fibre f y)`. Examples include
  `id:_`, `~refl:_`, `fst:_`, and `ε♭:_`.

  Note that while all of these return functions themselves, we rarely if ever have to
  provide the typing information when we evaluate them. For instance, if we evaluate
  `id: X` at `a`, then the typing argument `X` becomes redundant and we should've
  just written `id a`. Therefore it is safe to define these as unary prefix
  operators.

  We do not make wrappers prefix operators when they are normally used with further
  explicit arguments. For example, `♭-ind:` is not made a unary prefix operator,
  since the common use case would otherwise have to be parenthesized like
  `(♭-ind: B) f`.

- **Inlining.** Typed wrappers should be invisible in computations, so we mark them
  `INLINE`:

  ```agda
  {-# INLINE id:_ #-}
  ```

- **Display.** To avoid having the wrappers leak into goals, we use the `DISPLAY`
  pragma. If the wrapper returns a function, we include the first real argument in
  the `DISPLAY` pragma:

  ```agda
  {-# DISPLAY id:_ _ x = id x #-}
  {-# DISPLAY !:_ _ x = ! x #-}
  {-# DISPLAY const: _ _ x = const x #-}
  {-# DISPLAY ε♭:_ _ x = ε♭ x #-}
  ```

  Be sure to avoid display forms that only erase the type parameter of any
  function-valued wrapper:

  ```agda
  {-# DISPLAY f:_ _ = f #-}
  ```

  These can make partially-applied functions print incorrectly, for example if we had
  set `{-# DISPLAY id:_ _ = id #-}`, then `id: X` might print as `λ x → id`.

  Only when the wrapper returns a non-function value, the shorter form is fine:

  ```agda
  {-# DISPLAY refl:_ _ = refl #-}
  {-# DISPLAY id≃:_ _ = id≃ #-}
  ```

All in all, the definition of a typed wrapper should look like one of the following:

```agda
id:_ : ∀ {𝓤} (A : Type 𝓤) → A → A
id: A = id
infix 25 id:_
{-# INLINE id:_ #-}
{-# DISPLAY id:_ _ x = id x #-}
```

```agda
const: : ∀ {𝓤 𝓥} (A : Type 𝓤) (B : Type 𝓥) → A → B → A
const: A B = const
{-# INLINE const: #-}
{-# DISPLAY const: _ _ x = const x #-}
```

```agda
refl:_ : ∀ {𝓤} {A : Type 𝓤} → (a : A) → Id A a a
refl: a = refl
infix 25 refl:_
{-# INLINE refl:_ #-}
{-# DISPLAY refl:_ _ = refl #-}
```

## Assigning tree IDs

[Guidelines](http://agda-synthetic-categories.toth.co.uk/stt-00S2)
