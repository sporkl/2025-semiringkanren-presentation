---
dimension: 16:9
---

{center="authors"}
{unreveal="repo-link"}

{#title}
# Committing to the bit: Relational programming with semiring arrays and SAT solving

{#authors}
{style="text-align:center"}
### Dmitri Volkov, Yafei Yang, Chung-Chieh Shan

{style="text-align:center"}
### Indiana University

<br />

{style="text-align:center"}
{#repo-link}
> [https://github.com/sporkl/semiringkanren](https://github.com/sporkl/semiringkanren)

<br /> <br /> <br /> <br /> <br /> <br /> <br />

{slip}
{pause}
-----
## Introducing *semiringKanren*:

**miniKanren**{style="float:left"} **semiringKanren**{style="float:right"}

<br />

{pause}
[top-down evaluation]{style="float:left"}
[bottom-up evaluation]{style="float:right"}

<br />

{pause}
[relations are functions on streams]{style="float:left"}
[relations are multidimensional arrays]{style="float:right"}

<br />

{pause}
[dynamically typed (s-expressions)]{style="float:left"}
[statically typed (algebraic data types)]{style="float:right"}

<br />

{pause}
[usually unweighted]{style="float:left"}
[weighted]{style="float:right"}

<br />

{pause}
[shallow embedding]{style="float:left"}
[deep embedding]{style="float:right"}

<br />

{style="float:none"}

<br />


{pause}
{#coin-flip-minikanren}
{unreveal="coin-flip-semiringkanren"}
{.example title="Coin flip - miniKanren"}
---
```
(defrel (coin-flip c)
    (disj
        (== c 'heads)
        (== c 'tails)))
(run* (coin) (coin-flip coin))
```
Returns `'heads` and `'tails`.

{#coin-flip-semiringkanren}
{.example title="Coin flip - semiringKanren"}
---
Represent heads as `(left sole)` and tails as `(right sole)`.
```
(defrel (coin-flip (c : (Sum Unit Unit)))
    (disj
        (fresh (u : Unit) (lefto (c : (Sum Unit Unit) (u : Unit))))
        (fresh (u : Unit) (righto (c : (Sum Unit Unit) (u : Unit))))))

(run ((coin : (Sum Unit Unit))) (coin-flip coin))
```
Returns `(left sole)` corresponding to heads, and `(right sole)` corresponding to tails.

{center}
{unreveal="weighted-coin-flip"}
---
semiringKanren variables are typed.

```
; x has type A, y has type B
(x : A)
(y : B)

; Unit type
(sole : Unit)

; Sum type
((left x) : (Sum A B))
((right y) : (Sum A B))

; Product type
((pair x y) : (Prod A B))
```

{reveal="coin-flip-semiringkanren"}
{up="coin-flip-minikanren"}

{pause}
{center="semirings"}
We can use `(factor w)` to "weight" branches of a semiringKanren program, where `w` is an arbitrary semiring element.

{#semirings}
{.definition title="Semirings"}
---
A *semiring* (or *rig*) is a set $R$ with $+$ and $*$ operations, with corresponding identity elements $0$ and $1$, such that:

```math
a * (b + c) = (a * b) + (b * c)
```

(and some additional properties).

Examples: real numbers with addition and multiplication, booleans with $\vee$ and $\wedge$.
 
---

{pause}
{up="semirings"}
{.example title="Weighted coin flip"}
---
Assuming some semiring over $\mathbb{R}$:

```
(defrel (unfair (coin : (Sum Unit Unit)))
    (disj
        (conj (factor 0.7) (fresh ((u : Unit)) (lefto coin u)))
        (conj (factor 0.3) (fresh ((u : Unit)) (righto coin u)))))

(run ((coin : (Sum Unit Unit))) (unfair coin))
```

This returns `(left sole)` with weight 0.7, and `(right sole)` with weight 0.3.

---

{up}
{pause}
semiringKanren supports recursion!

{.example title="Transitive closure"}
---

Note: this example uses pseudo-syntax for brevity.

Let nodes in a graph be represented as natural numbers using a sum type, where the number of "right" constructors used corresponds to the integer value:

```
(define Num (Sum Unit (Sum Unit (Sum Unit Unit))))

(define 0 ((left sole) : Num))
(define 1 ((right (left sole)) : Num))
(define 2 ((right (right (left sole))) : Num))
(define 3 ((right (right (right (left sole)))) : Num))
```

{pause}

Represent a graph as a relation between nodes:

![](transitive-closure-graph.png)

```
(defrel (graph (x : Num) (y : Num))
    (disj
        (conj (== x 0) (== y 1))
        (conj (== x 1) (== y 0))
        (conj (== x 1) (== y 2))
        (conj (== x 3) (== y 2))))
```

{pause}
{center}
We can express connectivity (or "transitive closure") in this graph as a recursive relation:

```
(defrel (connect (x : Num) (y : Num))
    (disj
        (graph x y)
        (fresh ((z : Num))
            (conj
                (connect x z)
                (connect z y)))))
```
{pause}
{center}
```
(run ((x : Num) (y : Num)) (connect x y))
```
The results change depending on the semiring. For the boolean semiring, we get reachability:

![](transitive-closure-graph.png){style="float:right"}

{style="float:none"}

| | **0** | **1** | **2** | **3** |
| **0**&nbsp; | $\top$ | $\top$ | $\top$ | $\bot$ |
| **1**&nbsp; | $\top$ | $\top$ | $\top$ | $\bot$ |
| **2**&nbsp; | $\bot$ | $\bot$ | $\bot$ | $\bot$ |
| **3**&nbsp; | $\bot$ | $\bot$ | $\top$ | $\bot$ |

(`x` is the row, `y` is the column)

{pause}
{center}
For the *min-tropical* semiring $(\mathbb{R}^\infty, \min, +)$, we get the shortest path length:

| | **0** | **1** | **2** | **3** |
| **0**&nbsp; | $2$ | $1$ | $2$ | $\infty$ |
| **1**&nbsp; | $1$ | $2$ | $1$ | $\infty$ |
| **2**&nbsp; | $\infty$ | $\infty$ | $\infty$ | $\infty$ |
| **3**&nbsp; | $\infty$ | $\infty$ | $1$ | $\infty$ |

{slip}
{pause}
-----

## Implementation

<br />

{pause}

{#relations-are-arrays}
> # Relations are (multidimensional) arrays.
> {style="text-align:center"}
> [(with associated types)]{#with-associated-types}

{#relations-variables-br}
<br />

{pause}
{#variables-are-dimensions}
# Variables are specific dimensions of relation arrays.

{#variables-goals-br}
<br />

{pause}
{#goals-are-operations}
# Goals are operations on relation arrays.

{#variable-vectors}
----

{static="relations-are-arrays variables-are-dimensions"}
{unstatic="goals-are-operations with-associated-types relations-variables-br variables-goals-br"}
{up="relations-are-arrays"}

{pause}
If we reduce a multidimensional array to a single dimension, we get a 1-dimensional array (vector).

{pause}
In semiringKanren, variables must be typed.

{pause}
How to represent a strongly-typed value as a vector?

<br />

{pause}
{#sole-to-one}
Unit-typed values turn into the vector with one entry:
```math
\text{sole}\;\leadsto [1] \\
```

{pause}
Sum-typed values are handled by Kronecker sum:
```math
(\text{left}\;x)\;\leadsto \vec{x} \oplus [0]^{\oplus |\vec{y}|}
```
```math
{(\text{right}\;y)} \leadsto [0]^{\oplus |\vec{x}|} \oplus\vec{y} 
```

{pause}
Product-typed values are handled by Kronecker product:
```math
{(\text{pair}\;x\;y)} \leadsto \vec{x} \otimes\vec{y} 
```

{.example title="Pair of booleans"}
{up="sole-to-one"}
{pause}
---
Let's transform the value `(pair (left sole) (right sole))` of type `(Prod (Sum Unit Unit) (Sum Unit Unit))` into a vector:

{pause}
```math
\text{sole} \leadsto [1]
```

{pause}
```math
(\text{left}\;\text{sole}) : (\text{Sum}\;\text{Unit}\;\text{Unit}) \leadsto [1] \oplus [0]^{\oplus 1} = [1] \oplus [0] = [1, 0]
```
```math
(\text{right}\;\text{sole}) : (\text{Sum}\;\text{Unit}\;\text{Unit}) \leadsto[0]^{\oplus 1} \oplus [1] = [0] \oplus [1] = [0, 1]
```

{pause}
```math
(\text{pair}\;(\text{left}\;\text{sole})\;(\text{right}\;\text{sole})) \leadsto [1, 0] \otimes [0, 1] = [1 * [0, 1], 0 * [0, 1]] = [0, 1, 0, 0]
```

{pause}
{center}
Here's the full list of encodings for the type:
```math
(\text{pair}\;(\text{left}\;\text{sole})\;(\text{left}\;\text{sole})) \leadsto [1, 0, 0, 0]
```
```math
(\text{pair}\;(\text{left}\;\text{sole})\;(\text{right}\;\text{sole})) \leadsto [0, 1, 0, 0]
```
```math
(\text{pair}\;(\text{right}\;\text{sole})\;(\text{left}\;\text{sole})) \leadsto [0, 0, 1, 0]
```
```math
(\text{pair}\;(\text{right}\;\text{sole})\;(\text{right}\;\text{sole})) \leadsto [0, 0, 0, 1]
```

---

{pause}
Each value is encoded as a *one-hot vector*. The size of the vector is the size of the type. The singular nonzero entry in the vector corresponds to a specific value of the type.

{#relation-arrays}
----
{center}
{pause}
... what if there is more than one non-zero entry in the vector?


{pause}
{.example title="Pair of equal booleans"}
---
Consider the vector $[1, 0, 0, 1]$ with associated type `(Prod (Sum Unit Unit) (Sum Unit Unit))`.

{pause}
This vector has entries corresponding to the values `(pair (left sole) (left sole))` and `(pair (right sole) (right sole))`.

{pause}
It seems to represent pairs where the first element is equal to the second...

{unstatic="variables-are-dimensions goals-are-operations with-associated-types relations-variables-br variables-goals-br variable-vectors"}
{static="relations-are-arrays"}
{up="relations-are-arrays"}

{pause}

This is the relation on pairs of `(Sum Unit Unit)`s (booleans) where the first boolean is equal to the second!

```
(defrel (equal-bool-pair (xy : (Prod (Sum Unit Unit) (Sum Unit Unit))))
    (fresh (x : (Sum Unit Unit))
        (fresh (y : (Sum Unit Unit))
            (conj
                (pairo bp x y)
                (== x y)))))
```

---

{pause}
Relations are arrays where nonzero entries correspond to values that succeed, and zero entries correspond to values that fail.

{pause}
{center}
How does this work for more than one argument?

{pause}
{center}
{#variables-are-dimensions-2}
# Variables are specific dimensions of relation arrays.

{pause}
{up="variables-are-dimensions-2"}

Consider some relation on two booleans:

```
(defrel (bool-rel (x : (Sum Unit Unit)) (y : (Sum Unit Unit)))
    ...)
```

{pause}
Then `x` and `y` each get a dimension of the relation's array:

```math
\begin{matrix}
    \quad \; \; y \rightarrow \\
    x \downarrow
    \begin{bmatrix}
        [a, b], \\
        [c, d] \\
    \end{bmatrix}
\end{matrix}
```

{pause}
{center}
{.example title="Equal booleans"}
---
If we consider the relation where `x` equals `y`...

```
(defrel (equal-bools (x : (Sum Unit Unit)) (y : (Sum Unit Unit)))
    (== x y))
```

{pause}
Then `x` should be `(left sole)` when `y` is `(left sole)`, and same for `(right sole)`.

{style="float:right"}
```math
\begin{bmatrix}
[1, 0], \\
[0, 1]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |
> | **`(right sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad 1$ |

{pause}
{center}
{.example title="Specific boolean, any trilean"}
---
If we consider a relation where only one variable is conditioned:

```
(defrel (any-trilean (b : (Sum Unit Unit)) (t : (Sum Unit (Sum Unit Unit))))
    (fresh (u : Unit)
        (lefto b u)))
```

{pause}
{unreveal="goals-are-operations-2"}
Then the values for each variable are restricted/unrestricted accordingly:

{style="float:right"}
```math
\begin{bmatrix}
[1, 1, 1], \\
[0, 0, 0]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right (left sole))` | `(right (right sole))` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad\quad\;\; 1$ | $\quad\quad\quad\quad\quad 1$ |
> | **`(right sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad\quad\;\; 0$ | $\quad\quad\quad\quad\quad 0$ |

{#goal-operations}
----

{#goals-are-operations-2}
# Goals are operations on relation arrays.

{center}
{pause}
How do we use these relation arrays in practice?

{pause}
{reveal="goals-are-operations-2"}
{up="goals-are-operations-2"}

{pause}
There are two types of goals:

{pause}
{#relation-goals}
> ## Goals which are essentially relations
> `soleo`, `lefto`, `righto`, `pairo`, `==`, `=/=`, `succeed`, `fail`, `factor`, and relation application.

{pause}
{#combine-goals}
> ## Goals which combine other goals
> `conj`, `disj`, `fresh`.

{pause}
{#goals-return-relations}
> <br />
> Goals return relations!

{static="relation-goals"}
{unstatic="combine-goals goals-return-relations"}
{up="relation-goals"}

{pause}
We saw earlier that `==` on booleans becomes:

{style="float:right"}
```math
\begin{bmatrix}
[1, 0], \\
[0, 1]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |
> | **`(right sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad 1$ |

{pause}
Essentially just sticking a $1$ where values are equal, and $0$ where they are not.

This is how semiringKanren accomplishes *unification*.

{pause}
`lefto`, `righto`, `pairo`, and `==` are implemented via unification; semiringKanren knows where to stick the $1$s so the component types unify.

{pause}
`=/=` is similar; just swap the $1$s and $0$s:

{style="float:right"}
```math
\begin{bmatrix}
[0, 1], \\
[1, 0]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad 1$ |
> | **`(right sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |

{pause}
Relation application is also powered by unification; it unifies the argument variables with the corresponding dimensions of the relation array.
<br />

{pause}
{center="factored-trilean"}
`factor` fills an array with the corresponding value:

{#factored-trilean}
{.example title="Factored trilean"}
---
```
(defrel (factored-trilean (b : (Sum Unit Unit)) (t : (Sum Unit (Sum Unit Unit))))
    (factor 120))
```
{pause}
{style="float:right"}
```math
\begin{bmatrix}
[120, 120, 120], \\
[120, 120, 120]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right (left sole))` | `(right (right sole))` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\; 120$ | $\quad\quad\quad\quad\; 120$ | $\quad\quad\quad\quad\; 120$ |
> | **`(right sole)`** | $\quad\quad\; 120$ | $\quad\quad\quad\quad\; 120$ | $\quad\quad\quad\quad\; 120$ |

---

{pause}
`succeed` is just `(factor 1)`, and `fail` is `(factor 0)`.

`sole` is the only `Unit`-typed value, so `soleo` is guaranteed to succeed; it becomes `(factor 1)` as well!

{pause}
{up}
> ## Goals which combine other goals
> `conj`, `disj`, `fresh`.

{pause}
`conj` is handled by semiring multiplication of the arrays returned by it's arguments.

{pause}
{.example title="Left x and y"}
---
Here using the usual semiring on $\mathbb{R}$.

```
(defrel (x-is-left ((x : (Sum Unit Unit)) (y : (Sum Unit Unit)))
    (fresh (u : Unit)
        (lefto x u)))
```

{style="float:right"}
```math
\begin{bmatrix}
[1, 1], \\
[0, 0]
\end{bmatrix}
```

{style="float:none"}
> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 1$ |
> | **`(right sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad 0$ |

{pause}
```
(defrel (y-is-left ((x : (Sum Unit Unit)) (y : (Sum Unit Unit))))
    (fresh (u : Unit)
        (lefto y u)))
```

{style="float:right"}
```math
\begin{bmatrix}
[1, 0], \\
[1, 0]
\end{bmatrix}
```
{#y-is-left-result}
{style="float:none"}
> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |
> | **`(right sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |

{pause}
{down="x-and-y-are-left-result"}
```
(defrel (x-and-y-are-left ((x : (Sum Unit Unit)) (y : (Sum Unit Unit))))
    (conj
        (x-is-left x y)
        (y-is-left x y)))
```

```math
\begin{bmatrix}
[1, 1], \\
[0, 0]
\end{bmatrix}
*
\begin{bmatrix}
[1, 0], \\
[1, 0]
\end{bmatrix}
=
\begin{bmatrix}
[1 * 1, 1 * 0], \\
[0 * 1, 0 * 0]
\end{bmatrix}
= 
\begin{bmatrix}
[1, 0], \\
[0, 0]
\end{bmatrix}
```

> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |
> | **`(right sole)`** | $\quad\quad\;\; 0$ | $\quad\quad\quad 0$ |

---

{pause}
{center="example-left-x-or-y"}
{#x-and-y-are-left-result}
Similarly, `disj` is handled by semiring addition.

{#example-left-x-or-y}
{.example title="Left x or y"}
---

```
(defrel (x-or-y-is-left  (x : (Sum Unit Unit)) (y : (Sum Unit Unit)))
    (disj
        (x-is-left x y)
        (y-is-left x y)))
```

{pause}
```math
\begin{bmatrix}
[1, 1], \\
[0, 0]
\end{bmatrix}
+
\begin{bmatrix}
[1, 0], \\
[1, 0]
\end{bmatrix}
=
\begin{bmatrix}
[1 + 1, 1 + 0], \\
[0 + 1, 0 * 0]
\end{bmatrix}
= 
\begin{bmatrix}
[2, 1], \\
[1, 0]
\end{bmatrix}
```

> | | `(left sole)` | `(right sole)` |
> | --- | --- | --- |
> | **`(left sole)`** | $\quad\quad\;\; 2$ | $\quad\quad\quad 1$ |
> | **`(right sole)`** | $\quad\quad\;\; 1$ | $\quad\quad\quad 0$ |

---

{pause}
{center}
`fresh` introduces a new variable (array dimension), then reduces it by semiring addition.
It can be thought of as a disjunction over all the values of the new variable's type.

{pause}
{center}
{.example title="Left y"}
---
```
(defrel (just-y-is-left (y : (Sum Unit Unit)))
    (fresh (x : (Sum Unit Unit))
        (y-is-left x y)))
```

{pause}
Remember how the dimensions are assigned:
```math
\begin{matrix}
    \quad \; \; y \rightarrow \\
    x \downarrow
    \begin{bmatrix}
        [a, b], \\
        [c, d] \\
    \end{bmatrix}
\end{matrix}
```

{pause}
It follows:

```math
\sum_x
\begin{bmatrix}
[1, 0], \\
[1, 0]
\end{bmatrix}
= [1 + 1, 0 + 0] = [2, 0]
```

> | `(left sole)` | `(right sole)` |
> | --- | --- |
> | $\quad\quad\;\; 2$ | $\quad\quad\quad 0$ |

----

{pause}
{center}
{#what-about-recursion}
## What about recursion?

{pause}
{up="what-about-recursion"}
Recall that relation application requires the applied relation to have an array.

{pause}
What if that array does not exist yet?

{pause}
*Assume it fails.*

{pause}
This can already handle some programs with certain semirings.

{.example title="Succeed or recurse 1"}
---
```
(defrel (succeed-or-recurse)
    (disj
        (succeed)
        (succeed-or-recurse)))
```
{pause}
becomes:
```
(defrel (succeed-or-recurse)
    (disj
        (succeed)
        (fail)))
```
{pause}
{center}
which is equivalent to:
```
(defrel (succeed-or-recurse)
    (succeed))
```

A relation over no variables is a 0-dimensional array, so evaluates to the scalar of the semiring's value for "$1$".

Which may already be correct depending on the semiring: e.g. $\top$ for the boolean semiring, or $0$ for the min-tropical semiring.

---

{pause}
{center}
Depending on the program and the semiring, this is likely not the correct answer.

{.example title="Succeed or recurse 2"}
---
Translating the above program to a non-relational one that directly computes over the usual semiring on $\mathbb{R}$:

```
(define (succeed-or-recurse)
    (+
        1
        (succeed-or-recurse)))
```

We would expect this to loop infinitely.

---

{pause}
{center}
We can try computing the relation again now that we have some value for it's recursive call.

{pause}
{center}
{.example title="Succeed or recurse 3"}
---
Assuming the usual semiring on $\mathbb{R}$.
```
(defrel (succeed-or-recurse)
    (disj
        (succeed)
        (succeed-or-recurse)))
```
{pause}
Plugging in the value we calculated last time:
```
(defrel (succeed-or-recurse)
    (disj
        (succeed)
        (factor 1)))
```
{pause}
Simplifying:
```
(defrel (succeed-or-recurse)
    (factor 2))
```

Which evaluates to $2$.

---

{pause}
{center}
If we continue to repeat this process, we get $3$, then $4$, and so on... which seems to match the desired "infinite loop" behavior!

{pause}
{#fixpoint-evaluation}
# Program evaluation by fixpoint.

{pause}
{up="fixpoint-evaluation"}
Start by assuming all relations fail, and generate the corresponding relation arrays.

{pause}
Compute new relation arrays, using the old ones for relation calls.

{pause}
Repeat until the relation arrays stop updating (find the fixpoint).

<br />

{pause}
This is "bottom-up evaluation", similar to how Datalog works!

{slip}
{pause}
-----

The end.

<br />

{pause}
## ...

<br />

{pause}
# But what about committing to the bit!?

{style="text-align:center"}
This presentation didn't really have any jokes...

<br />

{pause}
"The joke is that there are no jokes."

{pause}
"The joke is the meta-humor that 'the joke is that there are no jokes' isn't really that funny."

{pause}
"Something about the fixpoint of meta-humor."

<br />

{pause}
{up}
## Compiling ADTs to bitstrings

Instead of arbitrary sum types, what if we only have booleans?

(`Bool` can be though of as `(Sum Unit Unit)`, where `true` is `(left sole)` and `false` is `(right sole)`)

{pause}
Convert sum types to *tagged unions*:

```math
(\text{Sum}\;A\;B) \leadsto (\text{Prod}\;\text{Bool}\;\max(A', B'))
```
Where `A'` and `B'` are the bitstring representations of `A` and `B`.

The first element of this pair is a `Bool`, which is `true` when the sum was a `left`, and `false` otherwise. The second element's type is whichever compiled component type of the original sum type is larger.

{pause}
Assuming $|A'|>|B'|$:
```math
(\text{left}\;x) \leadsto (\text{pair}\;\text{true}\;x')
```
```math
(\text{right}\;y) \leadsto (\text{pair}\;\text{false}\;\text{proj}_{A'}(y'))
```

Note that we need to coerce the smaller component type of the sum type into the larger component type.

{pause}
{.example title="Quaternary values"}
---
Aim to compile the type `(Sum Unit (Sum Unit (Sum Unit Unit)))`.

{pause}
Start with the innermost:
```math
(\text{Sum}\;\text{Unit}\;\text{Unit})\leadsto\text{Bool}
```

{pause}
{center}
Stepping up, now we want to compile `(Sum Unit Bool)`. We either have `(left (sole : Unit))` or `(right (b : Bool))`. `Bool` is bigger than `Unit`, so we use it in the compiled type.
```math
(\text{Sum}\;\text{Unit}\;\text{Bool}) \leadsto (\text{Prod}\;\text{Bool}\;\text{Bool})
```

{pause}
One more step:
```math
(\text{Sum}\;\text{Unit}\;(\text{Prod}\;\text{Bool}\;\text{Bool})) \leadsto (\text{Prod}\;\text{Bool}\;(\text{Prod}\;\text{Bool}\;\text{Bool}))
```

{pause}
{center}
Here's how the values compile. Note that `sole`s which are projected into a larger type get coerced into `true`s.

```math
(\text{left}\;\text{sole}) \leadsto (\text{pair}\;\text{true}\;(\text{pair}\;\text{true}\;\text{true}))
```
```math
(\text{right}\;(\text{left}\;\text{sole})) \leadsto (\text{pair}\;\text{false}\;(\text{pair}\;\text{true}\;\text{true}))
```
```math
(\text{right}\;(\text{right}\;(\text{left}\;\text{sole}))) \leadsto (\text{pair}\;\text{false}\;(\text{pair}\;\text{false}\;\text{true}))
```
```math
(\text{right}\;(\text{right}\;(\text{right}\;\text{sole}))) \leadsto (\text{pair}\;\text{false}\;(\text{pair}\;\text{false}\;\text{false}))
```
---

{pause}
{center}
`(Sum Unit (Sum Unit (Sum Unit Unit)))` has four values.

`(Prod Bool (Prod Bool Bool))` has eight values.

Why don't we compile to `(Prod Bool Bool)` instead, which has four values? More space-efficient...

{pause}
... but harder to use.

{pause}
{up}
## Adapting semiringKanren code to use bitstrings

Assuming that the bitstring version of type `A` is larger than the bitstring version of type `B`.
```
(lefto (x : (Sum A B)) (y : A))
```
{pause}
becomes
```
(fresh (a : A')
    (fresh (tag : Bool)
        (conj
            (pairo (x : (Prod Bool A')) (tag : Bool) (a : A'))
            (trueo (tag : Bool))
            (== (a : A') (y : A')))))
```
<br />

{pause}
{center}
```
(righto (x : (Sum A B)) (y : B))
```
becomes
```
(fresh (b : A')
    (fresh (tag : Bool)
        (conj
            (pairo (x : (Prod Bool A')) (tag : Bool) (b : A)')
            (falseo (tag : Bool))
            (coerced-== (a : A') (y : B'))
```

{pause}
{center}
`lefto` and `righto` become `trueo` and `falseo`, plus (coerced) unification.

(semiringKanren generates type-safe code for each coerced unification).

All set?

{pause}
{center}
{.example title="Fresh trilean compiled"}
---
{pause}
Assume the usual semiring on $\mathbb{R}$.
```
(defrel (fresh-tril)
    (fresh (t : (Sum Unit (Sum Unit Unit)))
        (succeed)))

(run () (fresh-bool))
```

{pause}
```math
\sum [1, 1, 1] = 1 + 1 + 1 = 3
```

{pause}
Compile it. Remember `Bool` is essentially the same as `(Sum Unit Unit)`.
```
(define (fresh-tril-comp)
    (fresh (t : (Prod Bool Bool)) ; or (Prod (Sum Unit Unit) (Sum Unit Unit))
        (succeed)))

(run () (fresh-tril-comp))
```

{pause}
```math
\sum [1, 1, 1, 1] = 1 + 1 + 1 + 1 = 4
```

But $3 \neq 4$...

---

{pause}
{center}
When introducing a new variable (whether as a relation argument or with a fresh), semiringKanren generates code to constrain the compiled version to correspond to the original type.

{pause}
{unreveal="sat-solving-semiringkanren"}
{center}
{.example title="Fresh trilean compiled, fixed"}
---
Here are how trilean values map to compiled trilean values:
```math
(\text{left}\;\text{sole}) \leadsto (\text{pair}\;\text{true}\;\text{true})
```
```math
(\text{right}\;(\text{left}\;\text{sole})) \leadsto (\text{pair}\;\text{false}\;\text{true})
```
```math
(\text{right}\;(\text{right}\;\text{sole})) \leadsto (\text{pair}\;\text{false}\;\text{right})
```

{pause}
`(pair left right)` is a valid `(Prod Bool Bool)`, but not a valid compiled trilean, so we need to prevent it:
```
(define (fresh-tril-comp)
    (fresh (t : (Prod Bool Bool)) ; or (Prod (Sum Unit Unit) (Sum Unit Unit))
        (conj
            (=/= t (pair left right))
            (succeed))))

(run () (fresh-tril-comp))
```

{pause}
```math
\sum [1, 0, 1, 1] = 1 + 0 + 1 + 1 = 3
```
There's the $3$ we're looking for.

{slip}
-----

{#sat-solving-semiringkanren}
## SAT solving semiringKanren

Okay, all set now?

{pause}
{.example title="9x9 sudoku"}
---

Consider attempting to solve a 9x9 sudoku board with semiringKanren.

{pause}
We can compactly represent a digit 0-9 as a binary number with 4 digits. (Using boolean semiring for maximum compactness).

{pause}
To represent a 9x9 sudoku board, we need 81 of these digits, one for each square.

{pause}
Recall that in semiringKanren, each variable is a dimension of an array.

{pause}
So to represent the sudoku board, we need an 81-dimensional array where each dimension is size 4.

{pause}
$4^{81}$ bits $=$ $5846006549323611672814739330865132078623730171904$ bits $\approx$ $7 * 10^{23}$ yottabytes

{pause}
Not quite "number of atoms in the universe" level (would be for a larger semiring), but still about 24 orders of magnitude larger than the amount of data that exists (as of September 2025).

---

{pause}
What can we do?

{pause}
{reveal="sat-solving-semiringkanren"}

{pause}
Compile to bitstrings.

{pause}
Unroll/inline recursions (fail when recursion depth limit reached--false negatives, but no false positives).

{pause}
Generate a SAT variable for each boolean.

{pause}
{center}
Translate to SAT:
```math
(\text{trueo}\;x) \leadsto x
```
```math
(\text{falseo}\;x) \leadsto \neg x
```
```math
(\text{==}\;x\;y) \leadsto x\;\text{==}\;y
```
```math
(\text{conj}\;x\;y) \leadsto x \wedge y
```
```math
(\text{disj}\;x\;y) \leadsto x \vee y
```

{pause}
{unreveal="future-work"}
And plug it into a SAT solver to evaluate over the boolean semiring.

{pause}
{center}
Benchmarks:

| Sudoku program &nbsp;&nbsp; | semiringKanren&nbsp;&nbsp; | SAT solver&nbsp;&nbsp; | Faster miniKanren |
| --- | --- | --- | --- |
| 4x4 | Out of memory | 0.227 | 0.746 |
| 9x9, medium | Out of memory | 25.814 | Timeout |
| 9x9, hard | Out of memory | 28.043 | Timeout |
| 9x9, expert | Out of memory | 72.088 | Timeout |

{slip}
{reveal="future-work"}
-----

{#future-work}
## Future work

{pause}
- polymorphic relations
    - without generating a new relation for each type?
{pause}
- recursive types
{pause}
- hardware optimization?
{pause}
- quantum computing or annealing (oh yeah so cool)
    - relation arrays look like superpositions of argument variable values.
    - get reversibility "for free"
        - can do `(run (q) (some-relation 1 q))` or `(run (q) (some-relation q 1))`.

{center="~duration:10 authors"}
{reveal="repo-link"}


