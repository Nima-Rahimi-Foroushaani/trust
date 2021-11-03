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
end

module ListAux = struct
  let uniq l =
    let rec uniq_h l ul =
      match l with
      | h :: tl ->
          if List.exists (( = ) h) tl then uniq_h tl ul else uniq_h tl (h :: ul)
      | [] -> ul
    in
    uniq_h l []
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
