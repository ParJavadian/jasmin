(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
  
Section CMD.

  Variable dead_code_i : instr ->  Sv.t -> result unit (Sv.t * cmd).

  Fixpoint dead_code (c:cmd) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match c with
    | [::] => Ok unit (s, [::])
    | i::c =>
      dead_code c s >>= (fun (sc:Sv.t * cmd) => let (s, c) := sc in
      dead_code_i i s >>= (fun (si:Sv.t * cmd) => let (s,ic) := si in
      Ok unit (s, ic ++ c)))
    end.

End CMD.

Section LOOP.

  Variable dead_code_c : Sv.t -> result unit (Sv.t * cmd).

  Fixpoint loop (n:nat) (wx:Sv.t) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match n with
    | O => Error tt
    | S n =>
      dead_code_c s >>=  (fun (sc:Sv.t * cmd) => let (s', c') := sc in
      let s' := Sv.diff s' wx in
      if Sv.subset s' s then Ok unit (s,c') 
      else loop n wx (Sv.union s s'))
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match n with
    | O => Error tt
    | S n =>
      dead_code_c s >>=  (fun (sc:Sv.t * cmd) => let (s', c') := sc in
      if Sv.subset s' s then Ok unit (s,c') 
      else wloop n (Sv.union s s'))
    end.

End LOOP.

Definition dead_code_bcmd (i:bcmd) (s:Sv.t) :=
  match i with
  | Assgn t rv e =>
    let w := write_bcmd i in
    if disjoint s w then (s,[::])
    else (read_e_rec e (Sv.diff s w), [::Cbcmd i])
  | Load r e => 
    let w := write_bcmd i in
    (read_e_rec e (Sv.diff s w) , [::Cbcmd i])
  | Store e1 e2 =>
    (read_e_rec e1 (read_e_rec e2 s), [::Cbcmd i])
  end.

Definition nb_loop := 100%coq_nat.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : result unit (Sv.t * cmd) := 
  match i with
  | Cbcmd i     => Ok unit (dead_code_bcmd i s) 
  | Cif b c1 c2 => 
    dead_code dead_code_i c1 s >>= (fun (sc:Sv.t * cmd) => let (s1,c1) := sc in
    dead_code dead_code_i c2 s >>= (fun (sc:Sv.t * cmd) => let (s2,c2) := sc in
    Ok unit (read_e_rec b (Sv.union s1 s2), [:: Cif b c1 c2])))
  | Cfor x (dir, e1, e2) c =>
    loop (dead_code dead_code_i c) nb_loop (vrv x) s >>= 
    (fun (sc:Sv.t * cmd) => let (s, c) := sc in
    Ok unit (read_e_rec e1 (read_e_rec e2 s),[::Cfor x (dir,e1,e2) c]))
  | Cwhile e c =>
    wloop (dead_code dead_code_i c) nb_loop (read_e_rec e s) >>= 
    (fun (sc:Sv.t * cmd) => let (s, c) := sc in
    Ok unit (s,[::Cwhile e c]))
  | Ccall ta tr x fd arg =>
    dead_code_call fd >>= (fun fd => 
    Ok unit (read_e_rec arg (Sv.diff s (vrv x)), [::Ccall x fd arg]))
  end

with dead_code_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r =>
    dead_code dead_code_i c (vrv r) >>= (fun (sc:Sv.t * cmd) => let (_, c) := sc in
    Ok unit (FunDef p c r))
  end.

Section PROOF.

  Let Pi (i:instr) := 
    forall mem1 mem2 vm1 vm2, sem_i (Estate mem1 vm1) i (Estate mem2 vm2) ->
    forall s2, 
      match dead_code_i i s2 with
      | Ok (s1, c') =>
        forall vm1', vm1 =[s1] vm1' ->
        exists vm2', vm2 =[s2] vm2' /\ 
          sem (Estate mem1 vm1') c' (Estate mem2 vm2')
      | _ => True
      end.

  Let Pc (c:cmd) := 
    forall mem1 mem2 vm1 vm2, sem (Estate mem1 vm1) c (Estate mem2 vm2) ->
    forall s2, 
      match dead_code dead_code_i c s2 with
      | Ok (s1, c') =>
        forall vm1', vm1 =[s1] vm1' ->
        exists vm2', vm2 =[s2] vm2' /\ 
          sem (Estate mem1 vm1') c' (Estate mem2 vm2')
      | _ => True
      end.

  Let Pf ta tr (fd:fundef ta tr) := 
    forall mem mem' va vr, 
      match dead_code_call fd with
      | Ok fd' => 
        sem_call mem fd va mem' vr -> 
        sem_call mem fd' va mem' vr
      | _ => True
      end.

  Let Hskip : Pc [::].
  Proof. 
    move=> m1 m2 vm1 vm2 /= H;inversion H;subst=> s2 st1' Heq;exists st1';split=>//.
    constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc m1 m3 vm1 vm3 H;inversion H;clear H;subst=> /=.
    case: s2 H3 H5  => m2 vm2 H3 H5 s3.
    have := Hc _ _ _ _ H5 s3;case: (dead_code dead_code_i c s3) => /= [[s2 c'] | //] Hc'.
    have := Hi _ _ _ _ H3 s2;case: (dead_code_i i s2) => [[s1 i']|] //=Hi' vm1' /Hi'.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof. 
    move=> i m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /= s2.
    case: i H2=> /=.
    + move=> t r e;case He: (sem_pexpr _ e) => [v|]//= [] <- /=.
      change (vrv_rec Sv.empty r) with (vrv r).
      case : (boolP (disjoint s2 (vrv r))) => /= [Hd Heq| _ H] vm1' Hvm.
      + exists vm1';split;last by constructor.
        by rewrite -Heq;apply: eq_onT (disjoint_eq_on vm1 v Hd) Hvm.
      subst; exists (write_rval vm1' r v);split;last first.
      + by apply sem_seq1;constructor => /=;rewrite -(read_e_eq_on Hvm) He.
      apply write_rval_eq_on;apply: eq_onI Hvm.
      rewrite read_eE;SvD.fsetdec.
    + move=> r e;case He: (sem_pexpr _ e) => [v|]//=.
      case Hre : (read_mem m1 v) => [v'|]//= [] <- <- /= vm1'.
      change (vrv_rec Sv.empty r) with (vrv r) => Hr.
      exists (write_rval vm1' r v');split;last first.
      + by apply sem_seq1;constructor=> /=; rewrite -(read_e_eq_on Hr) He /= Hre.
      apply write_rval_eq_on;apply: eq_onI Hr.
      rewrite read_eE;SvD.fsetdec.
    move=> e1 e2;case He1: (sem_pexpr _ e1) => [v1|]//=.
    case He2: (sem_pexpr _ e2) => [v2|]//=.
    case Hw: (write_mem m1 v1 v2) => [m|]//= [] <- <- vm1' Hr.
    exists vm1';split. 
    + by apply: eq_onI Hr;rewrite read_eE (read_eE e2);SvD.fsetdec.
    apply sem_seq1;constructor => /=.
    rewrite -(read_e_eq_on Hr) He1 /=.
    have Hr' : vm1 =[read_e_rec e2 s2] vm1'.
    + by apply: eq_onI Hr;rewrite (read_eE e1);SvD.fsetdec.
    by rewrite -(read_e_eq_on Hr') He2 /= Hw.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> s3 /=.
    case Heq1 : (dead_code dead_code_i c1 s3) => [[s1 c1']|//].
    case Heq2 : (dead_code dead_code_i c2 s3) => [[s2 c2']|] //= vm1' Hr.
    case: cond H5 H6 => H5 H6.
    + have := Hc1 m1 m2 vm1 vm2 H6 s3; rewrite Heq1=> /(_ vm1') [].
      + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
      move=> vm2' [Heq' Hsem];exists vm2';split => //.
      by apply sem_seq1;apply Eif with true => //=; rewrite -(read_e_eq_on Hr).
    have := Hc2 m1 m2 vm1 vm2 H6 s3; rewrite Heq2=> /(_ vm1') [].
    + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
    move=> vm2' [Heq' Hsem];exists vm2';split => //.
    by apply sem_seq1;apply Eif with false => //=; rewrite -(read_e_eq_on Hr).
  Qed.

  Opaque nb_loop.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i [[dir low] hi] c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /=.
    elim: nb_loop => //=.
    move=> n Hrec s2.
    case Heq : (dead_code dead_code_i c s2) => [[s1 c']|] //=.
    case : (boolP (Sv.subset (Sv.diff s1 (vrv i)) s2)) => /=.
    + move=> /Sv.subset_spec Hsub.
      pose st1 := {| emem := m1; evm := vm1 |}; pose st2:= {| emem := m2; evm := vm2 |}.
      rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
      rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.
      have: sem_for i [seq n2w i | i <- wrange dir vlow vhi] st1 c st2 ->
            dead_code dead_code_i c s2 = Ok unit (s1, c') -> Pc c -> 
            Sv.Subset (Sv.diff s1 (vrv i)) s2 ->
            forall vm1',  evm st1 =[s2]  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2]  vm2' /\
             sem_for i [seq n2w i | i <- wrange dir vlow vhi]
                {| emem := emem st1; evm := vm1' |} c'
                {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {Hrec H7 H8 H9 Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 c i} [s i c
                             | [m1 vm1] [m2 vm2] [m3 vm3] i w ws c Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + exists vm1';split=> //;constructor.
        have := Hc m1 m2 _ vm2 Hsc s2;rewrite Heq=> /(_ (write_rval vm1' i w)) /= [].
        + by apply write_rval_eq_on;apply: eq_onI Hvm1.
        move=> /= vm2' [Hvm2 Hsem2].
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        by exists vm3';split=> //;apply: EForOne Hsem3.
      move=> /(_ H9 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1').
      + by apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      apply sem_seq1;apply EFor with vlow vhi => //=.
      + by rewrite -(read_e_eq_on Hvm1).
      have Hvm: evm st1 =[read_e_rec hi s2]  vm1'.
      + by apply: eq_onI Hvm1;rewrite (read_eE low);SvD.fsetdec.
      by rewrite -(read_e_eq_on Hvm).
    move=> _;have := Hrec (Sv.union s2 (Sv.diff s1 (vrv i))).
    case: loop => [[s c0] |] //= H vm1' /H [vm2' [Hvm Hsem]];exists vm2';split=> //.
    by apply : eq_onI Hvm;SvD.fsetdec.
  Qed.

  Let Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /= s2.
    set s2' := (read_e_rec e s2).
    have : Sv.Subset (read_e_rec e s2) s2'.
    + rewrite /s2' read_eE=> //.
    elim: nb_loop s2' => //= n Hrec s2' Hsub.
    case Heq : (dead_code dead_code_i c s2') => [[s1 c']|] //=.
    case : (boolP (Sv.subset s1 s2')) => /=.
    + move=> /Sv.subset_spec Hsub1.
      pose st1 := {| emem := m1; evm := vm1 |}; pose st2:= {| emem := m2; evm := vm2 |}.
      rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
      rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.
      have: sem_while st1 e c st2 ->
            dead_code dead_code_i c s2' = Ok unit (s1, c') -> Pc c -> 
            Sv.Subset (read_e_rec e s2) s2' ->
            forall vm1',  evm st1 =[s2']  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2']  vm2' /\
             sem_while {| emem := emem st1; evm := vm1' |} e c'
                       {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {H4 Hrec Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 e c}
          [ st e c He | [m1 vm1] [m2 vm2] [m3 vm3] e c He Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + exists vm1';split=> //;constructor.
          rewrite -He /=;symmetry.
          have /read_e_eq_on //: evm st =[read_e_rec e s2]  vm1'.
          by apply: eq_onI Hvm1.
        have := Hc m1 m2 _ vm2 Hsc s2';rewrite Heq => /(_ vm1') /= [].
        + by apply: eq_onI Hvm1.
        move=> /= vm2' [Hvm2 Hsem2].
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        exists vm3';split=> //;apply: EWhileOne Hsem3=> //.
        rewrite -He /=;symmetry.
        have /read_e_eq_on //: vm1 =[read_e_rec e s2]  vm1'.
        by apply: eq_onI Hvm1.
      move=> /(_ H4 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1')=> //.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      + by apply: eq_onI Hvm2;move: Hsub;rewrite read_eE;SvD.fsetdec.
      by apply sem_seq1;constructor.
    move=> _; have := Hrec (Sv.union s2' s1).
    case: wloop => [[s c0] |] //=  H vm1' /(H _) [];first by SvD.fsetdec.
    move=> vm2' [Hvm Hsem];exists vm2';split=> //.
  Qed.
     
  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H7;clear H7.
    inversion H6;clear H6;subst;inversion H1;clear H1;subst.
    case Heq: sem_pexpr H3 H10 => [va /=|//] _ Hsem s2.
    case Heq' : dead_code_call => [fd'|] //= vm1' Hvm.
    have := Hf m1 m2 va res;rewrite Heq'=> /(_ Hsem) Hsem'.
    exists (write_rval vm1' x res);split.
    + by apply write_rval_eq_on;apply: eq_onI Hvm;rewrite read_eE; SvD.fsetdec.
    by apply sem_seq1;constructor;rewrite -(read_e_eq_on Hvm) Heq.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc m1 m2 va vr /=.
    case Heq : dead_code => [[s1 c'] | ]//= H;inversion H;clear H;subst.
    inversion H0;clear H0;subst=> /=; constructor=> //= vm0 Hvm0.
    case: (H6 vm0 Hvm0)=> vm2 /= [Hsem Heqr]. 
    have := Hc m1 m2 (write_rval vm0 x va) vm2 Hsem (vrv re);rewrite Heq.
    move=> /(_ (write_rval vm0 x va)) [] // vm2' [Hvm2 Hsem'].
    exists vm2';split=> // {H6 H8 Heq}.
    elim: re vr Hvm2 Heqr => [z | ?? vr1 Hrec1 vr2 Hrec2] vr Hvm /= ->.
    + by rewrite Hvm // vrv_var;SvD.fsetdec.
    by f_equal;[apply Hrec1 | apply Hrec2]=> //;apply: eq_onI Hvm;
      rewrite vrv_pair;SvD.fsetdec.
  Qed.

  Lemma dead_code_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    match dead_code_call f with 
    | Ok fd' => 
      sem_call mem f va mem' vr -> 
      sem_call mem fd' va mem' vr
    | _      => True
    end.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
  Qed.

End PROOF.