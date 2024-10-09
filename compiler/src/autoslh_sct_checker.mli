open Prog

type ty_fun
type info = { loc : int; var : int ggvar }
type sct_error = { err : Utils.hierror; info : info option }

exception SCTError of sct_error

val pp_info : Format.formatter -> info -> unit
val pp_sct_error : Format.formatter -> sct_error -> unit

val ty_prog :
  ('asm -> bool) -> ('info, 'asm) prog -> Name.t list -> (Name.t * ty_fun) list
