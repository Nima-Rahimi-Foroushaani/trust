type t = { name : string }

let make n = { name = n }

let name t = t.name

let dummy = { name = "" }