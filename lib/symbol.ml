type t = { name : string  (**symbol unique name*) }

let make n = { name = n }

let name s = s.name

let dummy = { name = "" }

let ( = ) (l : t) (r : t) = l = r
