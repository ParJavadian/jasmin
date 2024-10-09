open Prog

type 'len slhvar = {
  gv : 'len gvar;
  gvi : 'len gvar_i;
  lv : 'len glval;
  gx : 'len gexpr;
}

let msf_count = ref 0

let mk_slhvar (name : string) (reg_kind : Wsize.reg_kind) : 'a slhvar =
  let msf_gvar =
    GV.mk
      ("slh." ^ name ^ "_" ^ string_of_int !msf_count)
      (Reg (reg_kind, Direct))
      (Bty (U U64)) L._dummy []
  in
  incr msf_count;
  let msf_gvar_i = Location.mk_loc L._dummy msf_gvar in
  let msf_lval = Lvar msf_gvar_i in
  let msf_expr = Pvar (gkvar msf_gvar_i) in
  { gv = msf_gvar; gvi = msf_gvar_i; lv = msf_lval; gx = msf_expr }

let mk_init (var : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ var.lv ], AT_keep, Sopn.Oslh SLHinit, []);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let mk_update (cond : 'len gexpr) (var : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ var.lv ], AT_none, Sopn.Oslh SLHupdate, [ cond; var.gx ]);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let mk_mov (lhs : 'len slhvar) (rhs : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ lhs.lv ], AT_none, Sopn.Oslh SLHmove, [ rhs.gx ]);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let eword_of_int ws x = Papp1 (Oword_of_int ws, Pconst x)
let eeq ws e0 e1 = Papp2 (E.Oeq (Op_w ws), e0, e1)

let mk_protect_aux
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (i_loc : L.i_loc) (gx : 'len ggvar) (msf : 'len slhvar) : (unit, 'asm) stmt
    =
  let decorate i_desc =
    { i_desc; i_loc = L.refresh_i_loc i_loc; i_info = (); i_annot = [] }
  in
  let mk_i (gy : 'len ggvar) op =
    decorate (Copn ([ Lvar gy.gv ], AT_none, Sopn.Oslh op, [ Pvar gy; msf.gx ]))
  in
  match (L.unloc gx.gv).v_ty with
  | Bty (U ws) -> [ mk_i gx (Slh_ops.SLHprotect ws) ]
  | Bty Bool ->
      let tmp = GV.mk "slh.tmp" (Reg (Normal, Direct)) u8 i_loc.L.base_loc [] in
      let gtmp = gkvar (L.mk_loc i_loc.L.base_loc tmp) in
      let i0 = decorate (reg_of_bool gtmp.gv gx) in
      let i1 = mk_i gtmp (Slh_ops.SLHprotect Wsize.U8) in
      let i2 =
        let e = eeq Wsize.U8 (Pvar gtmp) (eword_of_int Wsize.U8 Z.zero) in
        decorate (Cassgn (Lvar gx.gv, AT_none, Bty Bool, e))
      in
      [ i0; i1; i2 ]
  | Bty Int -> assert false
  | Arr (_, n) -> [ mk_i gx (SLHprotect_ptr (Conv.pos_of_int n)) ]

let mk_protect should_spill_msf unspill_instr
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r) i_loc (gx : int ggvar)
    msf : (unit, 'asm) stmt =
  let pre, pos, c =
    let x = L.unloc gx.gv in
    match x.v_kind with
    | Stack r ->
        let decorate i_desc =
          { i_desc; i_loc = L.refresh_i_loc i_loc; i_info = (); i_annot = [] }
        in
        let tmp = GV.mk "slh.tmp" (Reg (Normal, r)) x.v_ty i_loc.L.base_loc [] in
        let tmpi = L.mk_loc i_loc.L.base_loc tmp in
        let gtmp = gkvar tmpi in
        let pre = decorate (Cassgn (Lvar tmpi, AT_none, x.v_ty, Pvar gx)) in
        let pos = decorate (Cassgn (Lvar gx.gv, AT_none, x.v_ty, Pvar gtmp)) in
        ([pre], [pos], mk_protect_aux reg_of_bool i_loc gtmp msf)
    | _ ->
        ([], [], mk_protect_aux reg_of_bool i_loc gx msf)
  in
  pre @ (if should_spill_msf then unspill_instr i_loc :: c else c) @ pos

let add_slh_protect (msf : int slhvar) spill_instr unspill_instr
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (should_spill_msf : bool) (i : (unit, 'asm) instr) : (unit, 'asm) instr list
    =
  let check_i_annot i = Annotations.has_symbol "protect" i.i_annot in
  match i.i_desc with
  | Cassgn (_, _, _, Pvar gx) when check_i_annot i ->
      mk_protect should_spill_msf unspill_instr reg_of_bool
        (L.refresh_i_loc i.i_loc) gx msf
  | _ -> [ i ]

let is_export_fn (funcs : (unit, 'asm) func list) (fun_name : funname) : bool =
  List.find (fun f -> f.f_name = fun_name) funcs |> fun f ->
  FInfo.is_export f.f_cc

(*TODO clean up passing spill info*)
let rec add_setmsf_instr (msf : 'len slhvar) (mmx_msf : 'len slhvar) spill_instr
    unspill_instr
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (funcs : (unit, 'asm) func list) (should_spill_msf : bool)
    (i : (unit, 'asm) instr) : (unit, 'asm) instr list =
  (* TODO revert to count *)
  let name = "slh.bool" ^ string_of_int !msf_count in
  let b = GV.mk name Inline (Bty Bool) i.i_loc.L.base_loc [] in
  incr msf_count;
  let b_gvar_i = Location.mk_loc L._dummy b in
  let b_expr = Pvar { gv = b_gvar_i; gs = Slocal } in
  let b_lval = Lvar b_gvar_i in
  let add_slh_block body =
    add_slh_instrs msf mmx_msf spill_instr unspill_instr reg_of_bool body funcs
      should_spill_msf
  in
  let loc () = L.refresh_i_loc i.i_loc in
  let init_instr = mk_init msf (loc ()) in
  match i.i_desc with
  | Csyscall _ ->
      if should_spill_msf then [ i; init_instr; spill_instr (loc ()) ]
      else [ i; init_instr ]
  | Ccall (vars, func_name, inputs) ->
      let final_msf = if should_spill_msf then mmx_msf else msf in
      if is_export_fn funcs func_name then
        if should_spill_msf then [ i; init_instr; spill_instr (loc ()) ]
        else [ i; init_instr ]
      else
        [
          {
            i with
            i_desc =
              Ccall
                (vars @ [ final_msf.lv ], func_name, inputs @ [ final_msf.gx ]);
          };
        ]
  | Cif (cond, if_body, else_body) ->
      let cond_expr = b_expr in
      let init_b_instr =
        [
          {
            i_desc = Cassgn (b_lval, AT_inline, Bty Bool, cond);
            i_loc = loc ();
            i_info = ();
            i_annot = [];
          };
        ]
      in
      let update_msf_if = mk_update cond_expr msf (loc ()) in
      let update_msf_else =
        mk_update (Papp1 (E.Onot, cond_expr)) msf (loc ())
      in
      let if_block =
        if should_spill_msf then
          unspill_instr (loc ())
          :: update_msf_if
          :: spill_instr (loc ())
          :: add_slh_block if_body
        else update_msf_if :: add_slh_block if_body
      in
      let else_block =
        if should_spill_msf then
          unspill_instr (loc ())
          :: update_msf_else
          :: spill_instr (loc ())
          :: add_slh_block else_body
        else update_msf_else :: add_slh_block else_body
      in
      init_b_instr
      @ [ { i with i_desc = Cif (cond_expr, if_block, else_block) } ]
  | Cwhile (alignf, c1, cond, c2) ->
      let cond_expr = b_expr in
      let init_b_instr =
        [
          {
            i_desc = Cassgn (b_lval, AT_inline, Bty Bool, cond);
            i_loc = loc ();
            i_info = ();
            i_annot = [];
          };
        ]
      in
      let update_msf_body = mk_update cond_expr msf (loc ()) in
      let update_msf_after =
        mk_update (Papp1 (E.Onot, cond_expr)) msf (loc ())
      in
      let c1 = add_slh_block c1 @ init_b_instr in
      let c2 =
        if should_spill_msf then
          unspill_instr (loc ())
          :: update_msf_body
          :: spill_instr (loc ())
          :: add_slh_block c2
        else update_msf_body :: add_slh_block c2
      in
      let new_i = { i with i_desc = Cwhile (alignf, c1, cond_expr, c2) } in
      if should_spill_msf then
        [
          new_i; unspill_instr (loc ()); update_msf_after; spill_instr (loc ());
        ]
      else [ new_i; update_msf_after ]
  | Cfor (it, rn, body) ->
      [ { i with i_desc = Cfor (it, rn, add_slh_block body) } ]
  | _ -> [ i ]

and add_slh_instrs msf mmx_msf spill_instr unspill_instr
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (body : (unit, 'asm) stmt) (funcs : (unit, 'asm) func list)
    (should_spill_msf : bool) =
  let add_msf =
    add_setmsf_instr msf mmx_msf spill_instr unspill_instr reg_of_bool funcs
      should_spill_msf
  in
  let add_protect =
    add_slh_protect msf spill_instr unspill_instr reg_of_bool should_spill_msf
  in
  List.concat_map add_msf body |> List.concat_map add_protect

let add_slh_local msf (mmx_msf : 'len slhvar)
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (funcs : (unit, 'asm) func list) (func : (unit, 'asm) func)
    (should_spill_msf : bool) =
  let spill_instr loc = mk_mov mmx_msf msf loc in
  let unspill_instr loc = mk_mov msf mmx_msf loc in
  let final_msf = if should_spill_msf then mmx_msf else msf in
  let append_None prev_cc =
    match prev_cc with
    | FInfo.Subroutine prev_returned_params ->
        FInfo.Subroutine
          { returned_params = prev_returned_params.returned_params @ [ None ] }
    | _ -> prev_cc
  in
  {
    func with
    f_cc = append_None func.f_cc;
    f_tyin = func.f_tyin @ [ Bty (U U64) ];
    f_args = func.f_args @ [ final_msf.gv ];
    f_body =
      add_slh_instrs msf mmx_msf spill_instr unspill_instr reg_of_bool
        func.f_body funcs should_spill_msf;
    f_tyout = func.f_tyout @ [ Bty (U U64) ];
    f_outannot =
      func.f_outannot
      @ [
          (Location.mk_loc Location._dummy "msf", None) :: final_msf.gv.v_annot;
        ];
    f_ret = func.f_ret @ [ final_msf.gvi ];
  }

let add_slh_export
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (funcs : (unit, 'asm) func list) (msf : 'len slhvar) (mmx_msf : 'len slhvar)
    (func : (unit, 'asm) func) (should_spill_msf : bool) =
  let init_instr = mk_init msf L.i_dummy in
  let spill_instr = mk_mov mmx_msf msf in
  let unspill_instr = mk_mov msf mmx_msf in
  let loc = L.refresh_i_loc init_instr.i_loc in
  let init_instr =
    if should_spill_msf then [ init_instr; spill_instr loc ] else [ init_instr ]
  in
  let body =
    add_slh_instrs msf mmx_msf spill_instr unspill_instr reg_of_bool func.f_body
      funcs should_spill_msf
  in
  { func with f_body = init_instr @ body }

let add_slh_func
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r)
    (fs : (unit, 'asm) func list) (f : (unit, 'asm) func)
    (should_spill_msf : bool) tbl =
  let msf = mk_slhvar "msf" Normal in
  let mmx_msf = mk_slhvar "mmx_msf" Extra in
  Hf.add tbl f.f_name (msf, mmx_msf);
  if FInfo.is_export f.f_cc then
    add_slh_export reg_of_bool fs msf mmx_msf f should_spill_msf
  else add_slh_local msf mmx_msf reg_of_bool fs f should_spill_msf

type 'asm mk_protectT =
  funname -> Location.i_loc -> int ggvar -> (unit, 'asm) stmt

let add_slh ((globs, fs) : (unit, 'asm) prog) (should_spill_msf : bool)
    (reg_of_bool : var_i -> int ggvar -> (int, unit, 'asm) ginstr_r) :
    'asm mk_protectT * (unit, 'asm) prog =
  let tbl : ('a slhvar * 'b slhvar) Hf.t = Hf.create 17 in
  let doit f = add_slh_func reg_of_bool fs f should_spill_msf tbl in
  let mk_protect (f : funname) (loc : Location.i_loc) (gx : int ggvar) :
      (unit, 'asm) stmt =
    let msf, mmx_msf = Hf.find tbl f in
    let unspill = mk_mov msf mmx_msf in
    mk_protect should_spill_msf unspill reg_of_bool loc gx msf
  in
  (mk_protect, (globs, List.map doit fs))

let remove_msf_ret ((globs, fs) : (unit, 'asm) prog) : (unit, 'asm) prog =
  let rec sets_msf (msf_lval : lval) (hd :: tl : (unit, 'asm) stmt) : bool =
    match hd.i_desc with
    | Cassgn (x, _, _, _) -> x == msf_lval
    | Copn (xs, _, _, _) | Csyscall (xs, _, _) -> List.mem msf_lval xs
    | Cfor (_, _, c) -> sets_msf msf_lval c
    | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
        sets_msf msf_lval c1 || sets_msf msf_lval c2
    | Ccall (xs, _, _) -> false
  in
  let rec get_msf (f_rets : 'len gvar_i list) : 'len gvar_i =
    match f_rets with [] -> assert false | [ x ] -> x | hd :: tl -> get_msf tl
  in
  let remove_msf_fn (f : (unit, 'asm) func) : (unit, 'asm) func =
    let msf = get_msf f.f_ret in
    if sets_msf (Lvar msf) f.f_body then f else f
  in
  (globs, List.map remove_msf_fn fs)

let remove_msf_arg ((globs, fs) : (unit, 'asm) prog) : (unit, 'asm) prog =
  (globs, fs)
