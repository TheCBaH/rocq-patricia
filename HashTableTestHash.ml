let bound = 0x40000000
let mask = 0x3fffffff

let normalize raw = raw land mask

let int ~seed key = normalize (seed lxor key)

let string ~seed text =
  let state = ref (normalize seed) in
  String.iter
    (fun byte -> state := normalize ((!state * 65599) lxor Char.code byte))
    text;
  !state

let constant ~seed:_ _ = 0
