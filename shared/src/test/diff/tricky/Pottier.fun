

// Inspired by [Pottier 98, chap 13.4]

rec def f = fun x -> fun y -> add (f x.tail y) (f x y)
rec def f = fun x -> fun y -> add (f x.tail y) (f y x)
rec def f = fun x -> fun y -> add (f x.tail y) (f x y.tail)
rec def f = fun x -> fun y -> add (f x.tail y.tail) (f x.tail y.tail)
rec def f = fun x -> fun y -> add (f x.tail x.tail) (f y.tail y.tail)
rec def f = fun x -> fun y -> add (f x.tail x) (f y.tail y)
rec def f = fun x -> fun y -> add (f x.tail y) (f y.tail x)
//│ f: 'a -> anything -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}
//│ f: 'a -> 'a -> int
//│   where
//│     'a <: {tail: 'a}

def f = fun x -> fun y -> if true then { l = x; r = y } else { l = y; r = x } // 2-crown
//│ f: 'a -> 'a -> {l: 'a, r: 'a}


// Inspired by [Pottier 98, chap 13.5]

rec def f = fun x -> fun y -> if true then x else { t = f x.t y.t }
//│ f: 'a -> 'b -> 'a
//│   where
//│     'b <: {t: 'b}
//│     'a := {t: 'a}


