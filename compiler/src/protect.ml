open Prog
open Autoslh_sct_checker

let protect_stmt mk_protect fname x i =
  let p = mk_protect fname (L.refresh_i_loc i.i_loc) x in
  match i.i_desc with
  | Cwhile (al, c1, e, c2) -> [ { i with i_desc = Cwhile (al, c1, e, c2 @ p) } ]
  | _ -> p @ [ i ]

(*TODO: stop searching when found*)
let protect_loc (mk_protect : 'a Slh_gen.mk_protectT)
    (fns : (unit, 'asm) func list) (info : info) : (unit, 'asm) func list =
  (* Format.printf "started protect gen with info = %a@." pp_info info; *)
  let rec do_i (fname : funname) (i : ('info, 'asm) instr) : ('info, 'asm) instr
      =
    match i.i_desc with
    | Cif (e, c1, c2) ->
        let c1 = do_c fname c1 in
        let c2 = do_c fname c2 in
        { i with i_desc = Cif (e, c1, c2) }
    | Cwhile (alignf, c1, e, c2) ->
        let c1 = do_c fname c1 in
        let c2 = do_c fname c2 in
        { i with i_desc = Cwhile (alignf, c1, e, c2) }
    | Cfor (it, rn, c) ->
        let c = do_c fname c in
        { i with i_desc = Cfor (it, rn, c) }
    | _ -> i
  and do_c (fname : funname) (body : (unit, _) stmt) : (unit, _) stmt =
    match body with
    | [] -> body
    | hd :: tl ->
        if info.loc = hd.i_loc.uid_loc then (
          Utils.warning Utils.Protect hd.i_loc "protect: %d %a@." info.loc
            Location.pp_loc hd.i_loc.base_loc;
          protect_stmt mk_protect fname info.var hd @ tl)
        else do_i fname hd :: do_c fname tl
  in
  let protect_fun f = { f with f_body = do_c f.f_name f.f_body } in
  List.map protect_fun fns

let protect_gen is_ct_sopn (mk_protect : 'a Slh_gen.mk_protectT)
    ((globs, fs) : (unit, 'asm) prog) (entries : Name.t list) :
    (unit, 'asm) prog =
  (* Stop at 1, decrease only if greater. *)
  let rec doit (n : int) (fs : (unit, 'asm) func list) : (unit, 'asm) func list
      =
    if n = 1 then (
      Format.eprintf "Out of fuel.@.";
      fs)
    else
      let n = if n = 0 then 0 else n - 1 in
      try
        ignore (ty_prog is_ct_sopn (globs, fs) entries);
        Format.eprintf "Done.@.";
        fs
      with SCTError e ->
        Format.eprintf "Found error:\n%a\n@." pp_sct_error e;
        match e.info with
        | Some info -> info |> protect_loc mk_protect fs |> doit n
        | None -> Format.eprintf "No info:\n%a\n@." pp_sct_error e; fs
  in
  let fs = doit 1000 fs in
  Format.eprintf "================================@.";
  (globs, fs)
