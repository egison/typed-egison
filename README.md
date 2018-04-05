# Typed Egison
This is a derivation of Egison.
The purpose of this project is to make Egison a static typed language.
This document is focused on the type system of Egison.

## Built-in Types
The bult-in types of Egison are
Char, String, Bool, Integer, Tuple, Collection, Fun, Pattern, Matcher, TypeVar and Any.

### Char, String, Bool, Integer
You can check the type of a expression using `print-type-of`.  
```
> (print-type-of c#a)
CharExpr 'a' :: Char

> (print-type-of "Hello")
StringExpr "Hello" :: String

> (print-type-of #t)
BoolExpr True :: Bool

> (print-type-of 42)
IntegerExpr 42 :: Integer
```
### Tuple
Tuple is a set of some types.
```
> (print-type-of [10 "hoge"])
TupleExpr [IntegerExpr 10,StringExpr "hoge"] :: (Tuple Integer String)
```

### Collection
Collection is used to represent a data which contains many same type datum.
```
> (print-type-of {10 20 40})
CollectionExpr [ElementExpr (IntegerExpr 10),ElementExpr (IntegerExpr 20),ElementExpr (IntegerExpr 40)] :: (Collection Integer)
```

## Fun
Fun is a abbreviation of function of curse.
Functions in Egison are take a tuple and return a value.
```
> (print-type-of (lambda [$x] (b.+ x 10)))
LambdaExpr [TensorArg "x"] (ApplyExpr (VarExpr (Var ["b","+"])) (TupleExpr [VarExpr (Var ["x"]),IntegerExpr 10])) :: (Fun (Tuple Integer) Integer)
```
This means `(lambda [$x] (b.+ x 10))` takes a tuple of integer and return integer.

### Pattern, Matcher
These two types are deeply related with `match-all` syntax.
In short, `match-all` looks like following.
```
(match-all "Data" "How to match" ["Pattern" "Result"])
"Collection of Result"
```

The following is an example of pattern matching in Egison.
```
> (match-all <Pair 2 5> (unorderd-pair integer) [<pair ,5 $x> x])
{2}
```
You don't have to understand details of `<Pair 2 5>`, `(unorderd-pair integer)` and `<pair ,5 $x>`.
What I want to teach in this section is types of these parts. These types are
```
<Pair 2 5> :: PairII
(unorderd-pair integer) :: Matcher PairII
<pair ,5 $x> :: Pattern PairII
```
PairII is user-defined ADT. I will explain about ADT in later section.

In this example, `match-all` takes 3 arguments and their types are PairII, (Matcher PairII), (Tuple (Pattern PairII) Integer) respectively and return (Collection Integer). More generally, `match-all` takes 3 arguments, a, (Matcher a), (Tuple (Pattern a, b)) and return (Collection b). a and b are variables which refer some types like Integer, Bool or PairII.

In rough words, `match-all` has this type
```
(Fun (Tuple (TypeVar a), (Matcher (TypeVar a)), (Tuple (Pattern (TypeVar a) (TypeVar b)))) (Collection (TypeVar b)))
```

Precisely, this is wrong but it is OK. I will explain details of `match-all` in later section.

## Abstract Data Type
As you can see in the previous section, you can define abstract data type in Egison.
`define-ADT` is a syntax for defining ADT.
```
(define-ADT "Name of type" <"Name of type constructor" "type1" "type2" ...> <"Name of type constructor" ...>)
```

For example, `PairII` is defined using following code.
```
(define-ADT PairII <Pair Integer Integer>)
```
After you execute above command, data constructor Pair and pattern constructor pair will be defined.
```
> (print-type-of Pair)
(Fun (Tuple Integer Integer) (TypeVar PairII))
> (print-type-of pair)
(Fun (Tuple (Pattern Integer) (Pattern Integer)) (Pattern (TypeVar PairII)))
```
Please be carefull. Pattern constructor is defined ***automatically***. When you define ADT, you must be carefull not to conflict names. You can use `print-type-of` to check whether a name is used or not.

## Implicit Conversion

## MatcherClause

## Details of `match-all`

## Let Polymorphism

## Type declaration for built-in functions
Built-in functions (ex. b.+, eq?) are defined in Egison interpreter
and we cannot infer the type of these functions.
So, we must give the type declaration of these functions to type checker.
For such purpose, we can use `define-type-of`.
When you write 
```
(define-type-of $b.+ (Fun (Tnple Integer Integer) Integer))
```
type checker believe `b.+` has `(Fun (Tnple Integer Integer) Integer)` type.
For more examples, please check lib/core/type-primitive.egi.
Type checker loads this file when it start.

