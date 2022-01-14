open Exception

module Name = struct
  (**Creates a name based on a provided base name, and an index*)
  let create_name bn idx =
    let idx_str =
      match idx with
      | 0 -> ""
      | _ when idx > 0 -> "_" ^ string_of_int idx
      | _ -> raise (invalid_arg "Negative index")
    in
    bn ^ idx_str

  let fresh_name ctx bn =
    let rec helper ctx bn idx =
      let name = create_name bn idx in
      if not (List.exists (( = ) name) ctx) then name
      else if idx = Int.max_int then
        raise (Excp (SevError, "No more options to make a fresh name"))
      else helper ctx bn (idx + 1)
    in
    helper ctx bn 0
end

module ListAux = struct
  (**
  returns the "set" of members of its input
  *)
  let uniq l =
    let rec uniq_h l ul =
      match l with
      | [] -> ul
      | h :: tl ->
          if List.exists (( = ) h) tl then uniq_h tl ul else uniq_h tl (h :: ul)
    in
    uniq_h l []

  let rec has_duplicate l =
    match l with
    | [] -> false
    | hd :: tl -> if List.exists (( = ) hd) tl then true else has_duplicate tl

  let rec try_fold_left f p l =
    match l with
    | hd :: tl -> (
        match f p hd with Ok r -> try_fold_left f r tl | Error e -> Error e)
    | [] -> Ok p

  let rec try_fold_right f p l =
    match l with
    | hd :: tl -> (
        match try_fold_right f p tl with Error e -> Error e | Ok r -> f r hd)
    | [] -> Ok p

  let partition_before_after f l =
    let rec helper checked rest =
      match rest with
      | [] -> None
      | hd :: tl ->
          if f hd then Some (checked, hd, tl) else helper (hd :: checked) tl
    in
    match helper [] l with
    | None -> None
    | Some (rev_before, ent, after) -> Some (List.rev rev_before, ent, after)

  let try_map f l =
    let rec helper mpd rest =
      match rest with
      | [] -> Ok mpd
      | hd :: tl -> (
          match f hd with
          | Ok m -> helper (m :: mpd) tl
          | Error msg -> Error msg)
    in
    match helper [] l with
    | Error msg -> Error msg
    | Ok mpd -> Ok (List.rev mpd)
end

module PL = struct
  (**
    * There are two possible problems with the substitution of an argument in a parameter:
    * 1-If parameter name is same as one of the parameters of inner abstractions, substitution
    * cuts off the relation of that inner parameter with its occurrences. It would not happen here though
    * because for this multi-parameter abstraction it does not make sense to have similar parameter names.
    * 2-If the argument is equal to one of the inner abstraction parameters. In this case the substitution
    * causes the substituted parameter to get captured by the inner parameter which was not related in
    * the first place. We fix this by alpha conversion.
  *)
  let subs_multi_param fresh subs params args body =
    if ListAux.has_duplicate params then
      Error "The parameter list involves duplicate parameters"
    else
      let rec helper params args body =
        match (params, args) with
        | [], [] -> Ok body
        | phd :: ptl, ahd :: atl -> (
            match ListAux.partition_before_after (( = ) ahd) ptl with
            | None ->
                let body1 = subs phd ahd body in
                helper ptl atl body1
            | Some (lps, p, rps) ->
                let p1 = fresh params p in
                let body1 = subs p p1 body in
                let params1 = (phd :: lps) @ (p1 :: rps) in
                helper params1 args body1)
        | _ ->
            Error
              "The lists of parameters and arguments are not of the same length"
      in
      helper params args body
end

module Tree = struct
  type 'a t = Node of 'a * 'a t list
end

module type Color_T = sig
  type t

  (*Common colors to use*)
  (*https://en.wikipedia.org/wiki/ANSI_escape_code*)
  type ccolor =
    | Black
    | Red
    | Green
    | Yellow
    | Blue
    | Magenta
    | Cyan
    | White
    | Gray
    | BrBlack
    | BrRed
    | BrGreen
    | BrYellow
    | BrBlue
    | BrMagenta
    | BrCyan
    | BrWhite

  val make_rgb8 : int -> int -> int -> t

  val make_cc : ccolor -> t

  val ccolor_to_rgb8_string : ccolor -> string -> string
end

module Color : Color_T = struct
  type t = RGB_8 of int * int * int

  let make_rgb8 r g b =
    if r >= 0 && g >= 0 && b >= 0 && r <= 255 && g <= 255 && b <= 255 then
      RGB_8 (r, g, b)
    else
      raise
        (invalid_arg
           "attempt to make 8bit RGB color with at least one component out of \
            range")

  (*Common colors to use*)
  (*https://en.wikipedia.org/wiki/ANSI_escape_code*)
  type ccolor =
    | Black
    | Red
    | Green
    | Yellow
    | Blue
    | Magenta
    | Cyan
    | White
    | Gray
    | BrBlack
    | BrRed
    | BrGreen
    | BrYellow
    | BrBlue
    | BrMagenta
    | BrCyan
    | BrWhite

  let ccolor_to_rgb cc =
    match cc with
    | Black -> (0, 0, 0)
    | Red -> (170, 0, 0)
    | Green -> (0, 170, 0)
    | Yellow -> (170, 85, 0)
    | Blue -> (0, 0, 170)
    | Magenta -> (170, 0, 170)
    | Cyan -> (0, 170, 170)
    | White -> (170, 170, 170)
    | Gray | BrBlack -> (85, 85, 85)
    | BrRed -> (255, 85, 85)
    | BrGreen -> (85, 255, 85)
    | BrYellow -> (255, 255, 85)
    | BrBlue -> (85, 85, 255)
    | BrMagenta -> (255, 85, 255)
    | BrCyan -> (85, 255, 255)
    | BrWhite -> (255, 255, 255)

  let make_cc cc =
    let r, g, b = ccolor_to_rgb cc in
    make_rgb8 r g b

  let color_to_rgb8_string c sep =
    match c with
    | RGB_8 (r, g, b) ->
        string_of_int r ^ sep ^ string_of_int g ^ sep ^ string_of_int b

  let ccolor_to_rgb8_string cc sep = color_to_rgb8_string (make_cc cc) sep
end
