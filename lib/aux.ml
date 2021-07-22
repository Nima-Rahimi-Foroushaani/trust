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
