
succ / 1
succ / succ / 1
//│ res: int
//│ res: int

let foo = f => f 1
//│ foo: (1 -> 'a) -> 'a

foo / x => x
//│ res: 1

foo / x => succ x
//│ res: int

x => succ / x + 1
//│ res: int -> int

x => succ / succ / x + 1
//│ res: int -> int

:p
foo / x => succ / succ / x
//│ Parsed: (foo (x => (succ (succ x))));
//│ res: int

:e
foo / foo / x => succ / succ / x
//│ /!\ Type error: cannot constrain int <: 1 -> 'a
//│ l.28: 	foo / foo / x => succ / succ / x
//│       	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//│ res: ⊥