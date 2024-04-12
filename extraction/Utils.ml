module List = struct
  let rec drop n ls = 
    if n <= 0 then
      ls
    else
      match ls with
      | _ :: ls' -> drop (n-1) ls'
      | [] -> []

  let rec take n ls = 
    if n <= 0 then
      []
    else
      match ls with
      | h :: ls' -> h :: (take (n-1) ls')
      | [] -> []

  let sublist ls s e = take (e - s) (drop s ls)

  let flat_map (type a b) (f: a -> b list) (ls: a list): b list =
    List.flatten (List.map f ls)

  let unique (type a) (ls: a list) = match ls with
    | h :: [] -> h
    | _ -> failwith "List is not a singleton"
end