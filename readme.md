Scoundrel
=========

Scoundrel is a little language inspired by Lua, Pascal and Scheme and
implemented in Rust. My main goal was to learn a bit more about how
interpreters work and improve my Rust at the same time. If the language could
be used to solve the first dozen or so Project Euler problems, I would be
happy.

A lot of little languages end up looking like Lua. If you combine Algol syntax
syntax with dynamic typing, it is hard to avoid. To make things more
interesting for myself, I decided to implement a purely functional language.
Because of this, Scoundrel ended up with a strong Scheme influence, although
to be fair, Lua itself is quite influenced by Scheme. I chose Pascal syntax
elements for nostalgia, I learned Pascal in high school, it was my second
language after Commodore 64 Basic. This resulted in a language that looks
a bit like Standard ML.

The scanner and parser are hand written. The parser is recursive descent. The
interpreter recursively walks the Abstract Syntax Tree generated by the parser.
I wanted to keep things simple. The recursive interpreter implementation made
detecting tail calls difficult. Since Scoundrel otherwise lacks looping
constructs, recursive tail call optimization was required to make the language
usable. This problem was worked around by adding a recur keyword similar to
that used for the same purpose in Clojure.

Scoundrel is a synonym of git in the Oxford English Dictionary. At one point I
had planned to write a git client as an exercise to learn Rust, but that
rapidly became boring.

Keywords
--------

The following are reserved Keywords: *and*, *else*, *elsif*, *end*, *false*,
*fn*, *if*, *in*, *let*, *mod*, *or*, *$*, *then* and *true*.


Values
------

### Boolean

Booleans take the values `true` and `false`. The usual boolean operators are
supported: `and`, `or`, and `not`.

### Function

A function is value consisting of a list of parameters enclosed in parentheses
and a body which is evaluated when the function is called. Functions are
considered true in boolean expressions.

```
fn (a b c)
    a + b + c
end
```

### List

A list is a list of values contained in square brackets. The empty list is
false in boolean expressions, other lists are true. The `+` operator performs
list concatenation.

```
[] + [1] + [2 3]
```

### Number

Numbers are 64 bit floats. The usual arithmetic and comparison operators
are supported: `+`, `-`, `*`, `/`, `mod`, '<', '<=', '==', '<>', '>', and '>='.
The `|` operator returns true if the first value evenly divides the second,
false otherwise, e.g. `a | b` is true if `b % a == 0`. The number zero is false
in boolean expressions, other numbers are considered true.

```
2 + 3 / 4 * 5 mod 6
```

### Recur

A recur is a `$` followed by a list of arguments enclosed in parentheses. It
is used to implement recursive tail call optimization. If a function call
results in a Recur value, the function is re-evaluated using the arguments
provided to the Recur without having to make another recursive call.

```
fn(n, sum)
    if n == 1000 then
        sum
    else
        $(n + 1, sum + n)
    end
end (0, 0)
```

### String

A string is a list of characters enclosed by single quotes. The `+` operator
is used to do string concatenation. A empty string is false in boolean
expressions, other strings are true.

```
'hello' + ' world'
```

Expressions
-----------

### If/Then/Elsif/Else/End

If expressions are used to evaluate conditionals. The else clause is
non-optional because every expression must return a value.

```
if x == 0 then
    0
elsif x == 1 then
    1
elsif x == 2 then
    2
else
    3
end
```

### Let

Let expressions are used to introduce variables. Each variable can then be
used in the definition of a subsequent variable, like `let*` in Scheme. The
body of the let expression is then evaluated.

```
let x := 1
    y := x + 5
    z := y / 5
in
    x + y + z
end
```

### Function Calls

A function call consists of a list of arguments in parentheses, optionally
separated by commas.

```
fn(name) 'hello ' + name end ('world')
```

Standard Library
----------------

A small standard library was implemented in Rust. The functions are described
below:
* `car(v)`: Return the first element of a list or string.
* `cdr(v)`: Return the elements of a list or string excluding the first.
* `len(v)`: Return the length of a list or string.
* `map(fun, list)`: Return the list that results from applying fn to each item of the list.
* `num(s)`: Convert the string to a number.
* `prime?(n)`: Return true if the number is a prime.
* `reduce(fun, list)`: Return the value that results from applying fn cumulatively to each item of the list l, returning a single result. The function must take two arguments.
* `sqrt(n)`: Return the square root of a number.
* `str(v)`: Return the result of converting a value to a string.
