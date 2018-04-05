# Typed Egison
This is a derivation of Egison.
The purpose of this project is to make Egison a static typed language.

## Primitive Types

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

