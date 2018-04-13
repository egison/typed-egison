# Typed Egison
This is a derivation of Egison.  
The purpose of this project is to make Egison a statically typed language.  
This document is focused on the type system of Egison and written for developers of Egison.  
You can test codes started with `>` in the Typed Egison interpreter.

## How to install and Run Interpreter
I assume you use Linux.
Please use following commands to build Typed Egison.
```
git clone git@github.com:egison/typed-egison.git
stack init
stack solver
stack build
```
After build, you can start repl by
```
stack exec egison
```
## Commands in the Interpreter
You can use these commands in the interpreter
- `print-type-of` &emsp;&nbsp;show the type of expression
- `define`&emsp;&emsp;&emsp;&emsp;&emsp;         define fucntions or constants
- `define-type-of` &nbsp;&nbsp;&nbsp;define type of functions or constants
- `define-ADT`&emsp;&emsp;&ensp;&nbsp;&nbsp;     define new ADT

## Built-in Types
The built-in types of Egison are
`Char`, `String`, `Bool`, `Integer`, `Tuple`, `Collection`, `Fun`, `Pattern` and `Matcher`.

### Char, String, Bool, Integer
You can check the type of a expression using `print-type-of`.  
```
> (print-type-of c#a)
c#a :: Char

> (print-type-of "Hello")
"Hello" :: String

> (print-type-of #t)
#t :: Bool

> (print-type-of 42)
42 :: Integer
```
### Tuple
Tuple is a set of some types.
```
> (print-type-of [10 "hoge"])
[10 "hoge"] :: (Tuple Integer String)
```

### Collection
Collection is used to represent a data which contains many same type datum.
```
> (print-type-of {10 20 40})
{10 20 40} :: (Collection Integer)
```

## Fun
Fun is an abbreviation of a function of course.
Functions in Egison are take a tuple and return a value.
```
> (print-type-of (lambda [$x] (b.+ x 10)))
(lambda [$x] (b.+ x 10)) :: (Fun (Tuple Integer) Integer)
```
This means `(lambda [$x] (b.+ x 10))` takes a tuple of integer and return integer.

### Pattern, Matcher
These two types are deeply related to `match-all` syntax.
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
(unordered-pair integer) :: Matcher PairII
<pair ,5 $x> :: Pattern PairII
```
`PairII` is user-defined ADT. I will explain about ADT in a later section.

In this example, `match-all` takes 3 arguments.  
Their types are `PairII`, `(Matcher PairII)`, `(Tuple (Pattern PairII) Integer)` respectively and return `(Collection Integer)`.   
More generally, `match-all` takes 3 arguments, `a`, `(Matcher a)`, `(Tuple (Pattern a, b))` and return `(Collection b)`.  
 `a` and `b` are variables which refer some types like `Integer`, `Bool` or `PairII`.

In rough words, `match-all` has this type
```
(Fun (Tuple a (Matcher a) (Tuple (Pattern a) b)) (Collection b))
```

## Abstract Data Type
As you can see in the previous section, you can define abstract data type in Egison.
`define-ADT` is a syntax for defining ADT.
```
(define-ADT "Name of type" <"Name of type constructor" "type1" "type2" ...> <"Name of type constructor" ...>)
```

The name of type and names of type constructors must start from a capital case.  
For example, `PairII` is defined using following code.
```
(define-ADT PairII <Pair Integer Integer>)
```
After you execute above command, data constructor `Pair` and pattern constructor `pair` will be defined.   
Names of pattern constructors are same with data constructors but pattern constructors are begun with small cases.
```
> (print-type-of Pair)
Pair :: (Fun (Tuple Integer Integer) PairII
> (print-type-of pair)
pair :: (Fun (Tuple (Pattern Integer) (Pattern Integer)) (Pattern PairII))
```
Please be careful. Pattern constructor has defined ***automatically***.   
When you define ADT, you must be careful not to conflict names.   
You can use `print-type-of` to check whether a name is used or not.
```
> (print-type-of unusedname)
Cannot decide the type of unusedname
```
## Advanced Topics
### Type declaration for built-in functions
Built-in functions (ex. `b.+`, `eq?`) are defined in Egison interpreter.  
So the type checker cannot infer the type of these functions.  
We must give the type declaration of these functions to type checker.  
For such purpose, we can use `define-type-of`.  
When you write
```
(define-type-of $b.+ (Fun (Tnple Integer Integer) Integer))
```
type checker believe `b.+` has `(Fun (Tnple Integer Integer) Integer)` type.  
For more examples, please check `lib/core/type-primitive.egi`.  
Type checker loads this file when it starts.  

***Caution***  
When you use ADT or type variables in `define-type-of`, you must write like `(TypeVar Pair)`.
For examples,
```
(define-type-of $eq? (Fun (Tuple (TypeVar a) (TypeVar a)) Bool))
(define-type-of somevalue (TypeVar PairII))
```

### Theoretical Base of Type System of Typed Egison
Theoretically, the type system of Egison is an extension of simply typed lambda calculus.  
I extended simply typed lambda calculus with let polymorphism, Collection, Pattern, Matcher.

### Implicit Conversion
I made implicit conversion for Egison.  
But it was not used now in the master branch.  
You can check the implementation in hs-src/Language/Egison/ImplConv.hs.  
Syntax for implicit conversion are `absolute-implicit-conversion` and `implicit-conversion`.  
`absolute-implicit-conversion` convert all possible variables absolutely.  
This means that when you define absolute implicit conversion from String to Integer,  
all values typed String is converted to Integer absolutely.  
`implicit-conversion` convert all possible variables so that the type check success.  
