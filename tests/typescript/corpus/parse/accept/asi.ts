// Automatic semicolon insertion, as ECMAScript 12.10 defines it.
export function asi(a: number, b: number): number {
  let x = a
  let y = b
  // A line break before `++` ends the statement: this is `x; ++y`.
  x
  ++y
  // No line break is allowed after `return`: this returns nothing.
  if (a < 0) {
    return
  }
  // A line break does not end `x = y` here: `(b)` is a call argument list.
  x = y
  (b)
  return x + y
}

// A line break after the name `async` makes `async (…)` a call: no line break
// may come between `async` and the parameters of an async arrow function
// (ECMAScript 15.9), and tsc reads none there either. On one line, tsc could
// read `async (1) :` as the start of an async arrow function.
function async(a: number): number {
  return a
}

export function asyncCall(c: boolean): number {
  const x = c ? async
  (1) : 2
  return (x)
}

// With a ';', a block may follow a parenthesized expression.
export function block(a: number): number {
  (a);
  {
    a += 1
  }
  return a
}
