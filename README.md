A simple s-expression compiler written in Rust

[Try it here](https://github.com/tim-sheung/s-compiler)

### Syntax
```
Arithmetic:
    +, -, *, /

Comparison:
    lt, gt, eq, ne, and, or, not

Condition:
    (if (condition) (true branch) (false branch))
    (? (condition) (true branch) (false branch))

Loop:
    (loop (condition) (body))
    (break)
    (continue)

Variables:
    (var name value)
    (set name value)

Functions:
    (def name (args) (body))
    (call name args)
    (return value)

Evaluate:
    (do (list 1)
        (list 2)
        (list 3) // Return last evaluated value
    )
```

### Sample programs
```
(def add (a b) (+ a b))
(call add 5 10)
```
```
(def fib (n) (do
    (var r 0)
    (loop (gt n 0) (do
        (set r (+ r n))
        (set n (- n 1))
    ))
    (return r)
))
(call fib 5)
```
```
(var a 1)
(var b 5)
(var c 10)
(loop (lt a b)
    (do
        (set a (+ a 1))
        (if (eq a 3) (break))
        (set c (+ c 1))
    )
)
(+ a c)
```
```
(var a 1)
(var b (+ a 1))
(do
    (var a (+ b 5))
    (set b (+ a 10))
)
(* a b)
```
