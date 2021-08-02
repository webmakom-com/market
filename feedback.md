(Note: this is a secret gist, and I can remove it after you've downloaded it, on request.)

# Feedback for Market Spec

This is based on the version I downloaded on [June 17](https://github.com/onomyprotocol/market/commit/8085dd8183f5cdeb1a255f4433fdf71fded61c48#diff-1c8028c746df389fbbffc7b1ce032217cd492b7e45740309abc1821b2d514f6e).

## Minor Notes


5: What is `Denom` short for? Denominations?

```
Action: Removed Denom
```
---

17: You have

```
ASSUME Denominator \in Nat
```

You actually want

```
ASSUME Denominator \subseteq Nat
```

Because `Denominator` is a set (based on comments of `6`).

---

```
Action: Proposed change made
```

43: Does `LimitType` require different `ask` and `bid` coins? If so, we can restrict that in the type too.

```
Action: will be updating the Order Type to make more flexible.
```

---

68: `SwapType` was removed from this version, but is still in `Ordertype`.

```
Action: Removed SwapType
```
---

79: `PositionType` implies there exists a **channel invariant** in the code, which is a bit complex to write here so I'm making a note to discuss it nextime we pair.

Can two limit orders be identical?

```
Identical limit orders are allowed, but each order will be tied to a specific balance in a wallet.
``` 

---

93: Call this `TypeInvariant` for clarity.

```
Action: Added Invariate to Type
```

* Potential channel invariant:

```tla
\A p \in Pair: 
  Cardinality(orderQ[p]) == 
    Cardinality(books[p][1]) + 
    Cardinality(books[p][2])
```

* `bonds` should be `[PairPlusCoin -> Nat \union {NoVal}]` (othewise 109 breaks)
* `drops` is not explained.
* Is `bonds` the total bonds for that coin/pair combination, or that *coin*? IE if I had three coins, A B C, should `bonds[{A, B}, B] = bonds[{C, B}, B]`?

---

127: If `pair = {d, c}`, then `pair \ {c}` returns `{d}`, not `d`. This breaks `Stronger`. I recommend creating a separate operator called `Other(pair, c)` to extract the coin that is *not* `c`. You can use an `Assert` if you want to make it "safe" (we can talk about that in person).

---

225-238:

* `Weaker` is not defined.

* You  don't need to nest the `LETs` like that. You can just put all three definitions into a single `LET`.
* As part of `Provision`, you increment *both* coins in `bonds`. Why? Should one of the `+`s be a `-`?

---

262: Should `ProcessOrder` also `Tail` the `orderQ`? I don't think you ever do that, even in an implict way (see below)

## CASE statements

I see a lot of code where you're writing

```tla
\/ /\ x < y
   /\ Stuff
\/ /\ x = y
   /\ Stuff
\/ /\ x > y
   /\ Stuff
```

We use the `\/ /\` pattern when we have multiple possibilities that are *not mutually exclusive*. Here, they are, and only one branch can possible be true at a time. In these cases, it's much better to use `IF THEN` or, alternatively, a case statement:

```tla
CASE x < y -> Stuff
  [] x = y -> Stuff
  [] x > y -> Stuff
```

```
Action: Changed all \/ /\ to CASE
```

## Top Level Actions

`SubmitOrder`, `Liquidate` and `Provision` all have top level existentials, like this:

```
Action ==
  \E x \in set:
    ...

Next == Action \/ ...
```

In these cases, it's better to pull the existential out of the action, like this:

```
Action(x) == ...

Next ==
  \E x \in set:
    \/ Action(x)
    \/ ...
```

This makes it easier to have multiple actions work on the same thing, or parameterize actions for testing, or call actions from other actions, etc etc etc.


## Exchange Rates

You write a lot of numerator/denominator manipulations. For example:

 ```tla
GT(a, b) ==     IF a[1]*b[2] > a[2]*b[1] THEN TRUE ELSE FALSE
```

First of all, this can be rewritten as


```tla
GT(a, b) == a[1]*b[2] > a[2]*b[1]
```

The `IF` is unecessary, as `>` is a boolean. If you want to further simplify it, you could use an infix operator, like `prec`:

```tla
a/b == <<a, b>>
a \succ b == a[1] * b[2] > a[2] * b[1]
a \succeq b == a[1] * b[2] >= a[2] * b[1]
a \prec b == a[1] * b[2] < a[2] * b[1]
a \preceq b == a[1] * b[2] <= a[2] * b[1]
```

Then you could write

```tla
bookBid(j).exchrate \preceq bondBid/bondAsk
```

## ProcessOrder

On line 270 you write

> Internal variables are used to track intermediate changes to books bonds on copy of the working state

This is invalid TLA+. You cannot prime a `LET` and you cannot "update" a variable with priming multiple times in the same action. I believe, based on the comments and flow, that `ProcessOrder` is supposed to recursively update everything via the nested function on line 346 and `Reconcile` on line 472. Neither of these work. When you write (Reconcile, 155):

```tla
/\ bondAsk = bondAsk - bookAsk(i).amount
```

You are just saying "is bondAsk equal to itself minus this amount", which is going to just return `FALSE`.

Fortunately this is all unecessary, as  you don't need recursive functions any of this. TLA+ is powerful enough to make figuring it all out "in one fell swoop" simple. For example, here's a sketch of how I'd rewrite the function in 346:

```tla
\* indices gt than active exchange
LET igt ==
  {i in 0..Len(bookBid): bookBid[i].exchrate >= o.exchrate}
IN IF igt = {} THEN UNCHANGED books
ELSE books' = [books EXCEPT ![pair][o.bid] 
  = InsertAt(@, Min(igt), order)]
```

Much simpler, and it makes it clear whether you want the *minimum* indice or the *max* indice (I probably got it wrong)

For `Reconcile`, to my understanding what you're trying to do is "compute the maximal prefix of `bookAsk` that totals to less than our `bondAsk`, then the maximal prefix of `bookBid` that totals to less than the *updated* `bondBid`, and then chop both. Here's another rough sketch of what that would look like:

(Sum is from [here](https://github.com/tlaplus/CommunityModules/blob/master/modules/FiniteSetsExt.tla))

```tla
LET 
 SeqSum(seq, x) == -1 \* Sum of seq[i].amount from 1..x
 i == CHOOSE i \in 0..Len(bookAsk): 
  /\ SeqSum(BookAsk, i) <= bondAsk
  /\ \/ i = Len(bookAsk)
     \/ SeqSum(BookAsk, i+1) > bondAsk
 j == CHOOSE j \in 0..Len(bookBid):
  /\ -1 \* Same, except you have to do
        \* SeqSum <= bondAsk + SeqSum(BookAsk, i)
IN
  <<i, j>>
```

And then handle the actual priming in `ProcessOrder`. We'll probably need to work out the details in person.
