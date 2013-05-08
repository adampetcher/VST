Require Import floyd.proofauto.
Require Import progs.sha.

Local Open Scope logic.


Definition big_endian_integer (contents: Z -> int) : int :=
  Int.or (Int.shl (contents 3) (Int.repr 24))
  (Int.or (Int.shl (contents 2) (Int.repr 16))
   (Int.or (Int.shl (contents 1) (Int.repr 8))
      (contents 0))).

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint ] 
        PROP() LOCAL (`(eq p) (eval_id 1%positive))
        SEP (`(array_at_range tuchar sh contents 0 4 p))
  POST [ tuint ] 
     local (`(eq (Vint (big_endian_integer contents))) retval) &&
     `(array_at_range tuchar sh contents 0 4 p).

(*        SEP (`(rangespec 0 4 (fun i => mapsto_ sh tuchar (add_ptr_int tuchar p i)))) *)

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint, 2%positive OF tuint ] 
        PROP(writable_share sh)
        LOCAL (`(eq p) (eval_id 1%positive);
                     `(eq (Vint(big_endian_integer contents))) (eval_id 2%positive))
        SEP (`(memory_block sh (Int.repr 4) p))
  POST [ tvoid ] 
     `(array_at_range tuchar sh contents 0 4 p).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: Z -> int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh))
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(array_at_range tuchar (fst sh) contents 0 n q);
              `(memory_block (snd sh) (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at_range tuchar (fst sh) contents 0 n q) *
        `(array_at_range tuchar (snd sh) contents 0 n p)).

Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh)
       LOCAL (`(eq p) (eval_id 1%positive); `(eq (Vint c)) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(memory_block sh (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at_range tuchar sh (fun _ => c) 0 n p)).

Definition sha256state_ (c: val) : mpred :=
   (EX r:_, typed_mapsto Tsh t_struct_SHA256state_st c r).

Definition arrayof_int sh t := arrayof int (fun (v : val) (v3 : int) => mapsto sh t v (Vint v3)) t.
Definition arrayof_float sh t := arrayof float (fun (v : val) v3 => mapsto sh t v (Vfloat v3)) t.

Ltac simpl_array_of_t :=
 repeat 
 match goal with 
 | |- appcontext [arrayof int (fun v v3 => mapsto ?sh ?t v (Vint v3)) ?t'] =>
   change (arrayof int (fun v v3 => mapsto sh t v (Vint v3)) t') 
      with (arrayof_int sh t')
 | |- appcontext [arrayof float (fun v v3 => mapsto ?sh ?t v (Vfloat v3)) ?t'] =>
   change (arrayof float (fun v v3 => mapsto sh t v (Vfloat v3)) t') 
      with (arrayof_float sh t')
 end.

Goal forall c r,  typed_mapsto Tsh t_struct_SHA256state_st c r = TT.
intros.
 simpl_typed_mapsto.
 simpl_array_of_t.
 simpl in r.
 destruct r as [r_h [r_Nl [r_Nh [r_data r_num]]]].
 simpl.
Abort.

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH ctx : val, data: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP() LOCAL (`(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
         SEP (`(sha256state_ ctx); `(memory_block sh (Int.repr 64) data))
   POST [ tvoid ]
          (`(sha256state_ ctx) * `(memory_block sh (Int.repr 64) data)).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val 
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP () LOCAL (`(eq c) (eval_id _c))
         SEP(`(typed_mapsto_ Tsh t_struct_SHA256state_st c))
  POST [ tvoid ] 
         SEP(`(sha256state_ c)).

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH c : val, d: val, len: Z, sh: share, A: mpred
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP () LOCAL (`(eq c) (eval_id _c); `(eq d) (eval_id _data_); 
                                  `(eq len) (`Int.unsigned (`force_int (eval_id _len))))
         SEP(`(sha256state_ c); `(A && memory_block sh (Int.repr len) d))
  POST [ tvoid ] 
         SEP(`(sha256state_ c); `A).

Definition SHA256_Final_spec :=
  DECLARE _SHA256_Final
   WITH md: val, c : val,  shmd: share, sh: share
   PRE [ _md OF tptr tuchar, _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); `(eq c) (eval_id _c))
         SEP(`(sha256state_ c); `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         SEP(`(sha256state_ c); 
                `(EX mdv:list int, arrayof_int shmd tuchar 32 md mdv)).

Definition SHA256_spec :=
  DECLARE _SHA256
   WITH d: val, len: Z, sh: share*share, A: mpred, md: val
   PRE [ _d OF tptr tuchar, _n OF tuint, _md OF tptr tuchar ]
         PROP (writable_share (snd sh)) LOCAL (`(eq d) (eval_id _data_);
                                  `(eq len) (`Int.unsigned (`force_int (eval_id _n)));
                                  `(eq md) (eval_id _md))
         SEP(`(A && memory_block (fst sh) (Int.repr len) d);
               `(memory_block (snd sh) (Int.repr 32) md))
  POST [ tvoid ] 
         SEP(`A;
               `(EX mdv:list int, arrayof_int (snd sh) tuchar 32 md mdv)).

Module Alternate.

Record sha256rep : Type :=  {
  sr_h: Z -> int; sr_lh: Z; sr_data: Z -> int; sr_num: Z
}.

Definition field_offset' (t: type) (fld: ident) (p: val) : val :=
 match t with
  | Tstruct id fList  att =>
     match field_offset fld fList with
     | Errors.OK delta => offset_val (Int.repr delta) p
     | _ =>  Vundef
     end
  | _  => Vundef
  end.

Definition sha256state (r: sha256rep) (p: val) : mpred :=
   array_at_range tuint Tsh (sr_h r) 0 8
      (field_offset' t_struct_SHA256state_st _h p) 
 * field_mapsto Tsh t_struct_SHA256state_st _Nl p 
                   (Vint (Int.repr (sr_lh r)))
 * field_mapsto Tsh t_struct_SHA256state_st _Nh p 
                   (Vint (Int.repr (Zdiv (sr_lh r) Int.modulus)))
 * array_at_range tuint Tsh (sr_data r) 0 16
      (field_offset' t_struct_SHA256state_st _data p) 
 * field_mapsto Tsh t_struct_SHA256state_st _num p 
                 (Vint (Int.repr (sr_num r))).


Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH ctx : val, b: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP() LOCAL (`(eq ctx) (eval_id _ctx); `(eq b) (eval_id _in))
         SEP (`(EX r:_, sha256state r ctx) * `(memory_block sh (Int.repr 64) b))
   POST [ tvoid ]
          (`(EX r:_, sha256state r ctx) * `(memory_block sh (Int.repr 64) b)).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val 
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP () LOCAL (`(eq c) (eval_id _c))
         SEP(`(typed_mapsto_ Tsh t_struct_SHA256state_st c))
  POST [ tvoid ] 
         SEP(`(EX r:_, sha256state r c)).

End Alternate.

Definition Vprog : varspecs := (_K256, tarray tuint 64)::nil.

Definition Gprog : funspecs := 
  __builtin_read32_reversed_spec::
  __builtin_write32_reversed_spec::
  memcpy_spec:: memset_spec::
  sha256_block_data_order_spec:: SHA256_Init_spec::
  SHA256_Update_spec:: SHA256_Final_spec::
  SHA256_spec:: nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma sha256state__isptr:
 forall c, sha256state_ c = !!(isptr c) && sha256state_ c.
Proof.
intros. unfold sha256state_. normalize. apply f_equal.
extensionality r.
simpl_typed_mapsto.
rewrite field_mapsto_isptr at 1. normalize.
Qed.


Lemma lift2more {A}{B}{T}:
  forall (v :A) (v': B) (F: A -> B -> T),
   @liftx (LiftEnviron T) (F v v') = 
     @liftx (Tarrow A (Tarrow B (LiftEnviron T))) F `v `v'.
Proof. reflexivity. Qed.

Lemma lift1more {A}{T}:
  forall (v :A) (F: A -> T),
   @liftx (LiftEnviron T) (F v) = 
     @liftx (Tarrow A (LiftEnviron T)) F `v.
Proof. reflexivity. Qed.



Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_typed_mapsto_. 

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
unfold sha256state_.
simpl_stackframe_of. 
simpl_typed_mapsto; simpl_array_of_t. simpl eval_expr.
match goal with |- semax _ _ ?C ?P => set (cmd:=C); set (Post:=P) end.
normalize.
intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
normalize.
unfold cmd; clear cmd.
forward. (* data=in; *)

Admitted.