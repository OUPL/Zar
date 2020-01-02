(* Paste this at the end of the the extracted ktree.ml *)

let empty : st = fun _ -> False

let t = pir_ktree empty

open Random
let _ = Random.self_init

let handle_get k = k (Obj.magic (Random.bool ()))

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (_, k) -> handle_get (fun x -> run (k x))

let n = 10000

let () =
  let cnt = ref 0 in
  for i = 0 to n do
    if run t then cnt := !cnt + 1 else ()
  done;
  print_endline @@ string_of_float @@ float_of_int !cnt /. float_of_int n
