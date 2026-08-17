type location = { f : string; s : int * int; e : int * int }
type 'a located = location * 'a

let pp fmt l =
  Format.fprintf fmt "%s:%d.%d-%d.%d" l.f (fst l.s) (snd l.s) (fst l.e)
    (snd l.e)

let equal l1 l2 = l1 = l2
