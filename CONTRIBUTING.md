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
| 40               | Arithmetic mutliplication operators                                                                                                                               |
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
| 6                | Parametric relational operators: `_＝_`, `_~_`, `_≃_`, `_≊_`, `_↔_`, `_⊥_`, `_∈_`                                                                                 |
| 5                | Directed function-like formation operators: `_→∗_`, `_⇒_`                                                                                                         |
| 3                | Parametric pairing operators: `_,_`, `_∷_`                                                                                                                        |
| 0-1              | Reasoning syntaxes                                                                                                                                                |
| -∞               | Function type formation: `_→_`                                                                                                                                    |
