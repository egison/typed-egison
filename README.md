# Typed Egison
This is a derivation of Egison.
The purpose of this project is to make Egison a static typed language.
This document is focused on the type system of Egison.

## Built-in Types
The bult-in types of Egison are
Char, String, Bool, Integer, Tuple, Collection, Fun, Pattern, Matcher, MatcherClause, TypeVar and Any.

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

### Pattern, Matcher, MatcherClause

## Implicit Conversion

## Abstract Data Type

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

