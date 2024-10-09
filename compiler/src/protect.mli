open Prog

val protect_gen :
  ('asm -> bool) ->
  'asm Slh_gen.mk_protectT ->
  (unit, 'asm) prog ->
  Name.t list ->
  (unit, 'asm) prog
