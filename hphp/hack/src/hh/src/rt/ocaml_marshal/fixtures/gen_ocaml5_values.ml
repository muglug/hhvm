(* Fixtures for rt/ocaml_marshal.rs, written by OCaml 5.1.1: a sequence of Marshal.to_string outputs. *)
module IM = Map.Make (Int)
module SS = Set.Make (String)

let out = open_out_bin Sys.argv.(1)

let emit v = output_string out (Marshal.to_string v [])

let emit_ns v = output_string out (Marshal.to_string v [Marshal.No_sharing])

let rec random_value pool depth : Obj.t =
  let r = Random.int 100 in
  if r < 15 && !pool <> [] then List.nth !pool (Random.int (List.length !pool))
  else if depth > 3 || r < 35 then
    match Random.int 6 with
    | 0 -> Obj.repr (Random.int 100)
    | 1 -> Obj.repr (Random.int 1000000000 - 500000000)
    | 2 -> Obj.repr (String.make (Random.int 40) 'a')
    | 3 -> Obj.repr (Random.float 1000.)
    | 4 -> Obj.repr (Random.bits () lsl 30)
    | _ -> Obj.repr ""
  else begin
    let size = Random.int 10 in
    let tag = if Random.int 4 = 0 then Random.int 30 else Random.int 3 in
    let b = Obj.new_block tag size in
    for i = 0 to size - 1 do Obj.set_field b i (random_value pool (depth + 1)) done;
    let v = if size = 0 then Obj.repr 0 else b in
    pool := v :: !pool;
    v
  end

let () =
  Random.init 42;
  emit [0; 1; 63; 64; -1; -64; -128; 127; 128; -129; 255; 256; 32767; 32768; -32768; -32769;
        (1 lsl 30) - 1; 1 lsl 30; -(1 lsl 30); -(1 lsl 30) - 1; 1 lsl 31; max_int; min_int];
  emit (List.init 300 (fun n -> String.make n 'x'));
  emit (String.make 300 'y');
  emit [0.; -0.; 1.5; nan; infinity; neg_infinity; 1e300; 5e-324];
  emit [|1.; 2.; 3.|];
  emit (Array.make 300 1.5);
  emit ([||] : float array);
  emit (Array.make 20 7);
  for tag = 0 to 20 do
    List.iter (fun size ->
      let b = Obj.new_block tag size in
      for i = 0 to size - 1 do Obj.set_field b i (Obj.repr i) done;
      emit b) [1; 7; 8; 9; 300]
  done;
  let s = "shared" in
  emit [s; s; s];
  let b = (1, "x") in
  emit [b; b; (2, "y"); b];
  let x = "far" in
  emit (x, List.init 66000 (fun _ -> 0), x);
  emit (List.init 300 (fun i -> string_of_int i) @ ["0"]);
  emit_ns [s; s; s];
  emit [`Null; `Bool true; `Int 3; `Intlit "123"; `Float 1.5; `String "x";
        `Assoc [("a", `Float 1.5); ("b", `List [`Bool false; `Null])]; `List []; `Tuple [`Null]; `Variant ("v", None)];
  let orders = [
    List.init 50 (fun i -> i);
    List.init 50 (fun i -> 50 - i);
    List.init 200 (fun _ -> Random.int 1000);
    [5; 3; 8; 1; 4; 7; 9; 2; 6; 0];
  ] in
  List.iter (fun keys ->
    let m = List.fold_left (fun m k -> IM.add k (k * 2) m) IM.empty keys in
    emit (keys, m);
    emit (keys, IM.filter (fun k _ -> k mod 3 <> 0) m);
    let ss = List.fold_left (fun s k -> SS.add (string_of_int k) s) SS.empty keys in
    emit (keys, ss)) orders;
  for _ = 1 to 150 do
    let pool = ref [] in
    emit (random_value pool 0)
  done;
  close_out out
