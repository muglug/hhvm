(* Writes a NAMING_LOCAL_CHANGES blob (Naming_sqlite.blob_format) with the
   layouts of this OCaml version's types, by OCaml 5.1.1 Marshal. *)
type prefix = Root | Hhi | Dummy | Tmp
type rp = prefix * string
module RPMap = Map.Make (struct type t = rp let compare = compare end)
module S_set = Set.Make (String)
type mode = Mhhi | Mstrict
type saved_names = { sn_funs: S_set.t; sn_classes: S_set.t; sn_types: S_set.t; sn_consts: S_set.t; sn_modules: S_set.t }
type saved = { s_names: saved_names; s_position_free_decl_hash: Int64.t option; s_mode: mode option }
type 'a delta = Modified of 'a | Deleted
let set l = List.fold_left (fun s x -> S_set.add x s) S_set.empty l
let names ?(f=[]) ?(c=[]) ?(t=[]) ?(k=[]) ?(m=[]) () =
  { sn_funs = set f; sn_classes = set c; sn_types = set t; sn_consts = set k; sn_modules = set m }
let blob : saved delta RPMap.t =
  List.fold_left (fun m (k, v) -> RPMap.add k v m) RPMap.empty [
    ((Root, "z.php"), Deleted);
    ((Root, "a.php"), Modified { s_names = names ~f:["\\f"; "\\g"] ~c:["\\A"; "\\C"] (); s_position_free_decl_hash = Some 1234567890123L; s_mode = Some Mstrict });
    ((Root, "sub/b.php"), Modified { s_names = names ~t:["\\T"] ~k:["\\K"] ~m:["m"] (); s_position_free_decl_hash = Some (-5L); s_mode = Some Mhhi });
    ((Hhi, "x.hhi"), Modified { s_names = names (); s_position_free_decl_hash = None; s_mode = None });
    ((Root, "c.php"), Deleted);
    ((Root, "b.php"), Modified { s_names = names ~c:["\\B"] (); s_position_free_decl_hash = Some Int64.max_int; s_mode = Some Mstrict });
  ]
let () =
  let out = open_out_bin Sys.argv.(1) in
  output_string out (Marshal.to_string blob [Marshal.No_sharing]);
  close_out out;
  (* Also with sharing (the OCaml writes No_sharing; a reader must accept both). *)
  let out = open_out_bin Sys.argv.(2) in
  output_string out (Marshal.to_string blob []);
  close_out out
