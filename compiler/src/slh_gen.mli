open Prog

type 'len slhvar = {
  gv : 'len gvar;
  gvi : 'len gvar_i;
  lv : 'len glval;
  gx : 'len gexpr;
}

type 'asm mk_protectT =
  funname -> Location.i_loc -> int ggvar -> (unit, 'asm) stmt

val add_slh :
  (unit, 'asm) prog ->
  bool ->
  (var_i -> int ggvar -> (int, unit, 'asm) ginstr_r) ->
  'asm mk_protectT * (unit, 'asm) prog
