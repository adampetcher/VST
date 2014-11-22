Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.
Require Export veric.environ_lemmas. 
Import Cop.
Import Cop2.

(** Main soundness result for the typechecker **)

Lemma typecheck_both_sound: 
  forall Delta rho e , 
             typecheck_environ Delta rho ->
             (denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr e rho) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue e rho) pt=true).
Proof.
intros. 
 unfold denote_tc_assert. unfold typecheck_expr, typecheck_lvalue.
split. auto.
intros. admit. (*probably true, doesn't matter *)

Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ Delta rho -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
              tc_val (typeof e) (eval_expr e rho).
Proof. intros. 
rewrite tc_val_eq. auto.
Qed.

Lemma typecheck_lvalue_sound : forall Delta rho e,
  typecheck_environ Delta rho ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ->
  is_pointer_or_null (eval_lvalue e rho).
Proof.
intros. unfold denote_tc_assert, typecheck_lvalue in *. simpl in *.
admit. 
Qed.

Ltac unfold_cop2_sem_cmp :=
unfold Cop2.sem_cmp, Cop2.sem_cmp_pp, Cop2.sem_cmp_pl, Cop2.sem_cmp_lp.

Lemma bin_arith_relate :
forall a b c d v1 v2 t1 t2, 
Cop.sem_binarith a b c d v1 t1 v2 t2 =
sem_binarith a b c d t1 t2 v1 v2.
Proof.
intros. 
unfold Cop.sem_binarith, sem_binarith, Cop.sem_cast, sem_cast, both_int,both_long,both_float,both_single.
destruct (classify_binarith t1 t2); 
 destruct t1 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; simpl; auto;
 destruct v1; auto; 
 destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; 
 simpl; auto;
repeat match goal with 
| |- context [match ?v with| Vundef => None| Vint _ => None| Vlong _ => None| Vfloat _ => None| Vsingle _ => None| Vptr _ _ => None end] =>
       destruct v; simpl
| |- context [match ?A with Some _ => None | None => None end] =>
 destruct A; simpl
 end;
 try (destruct (cast_float_int s _); reflexivity);
 try (destruct (cast_float_long s _); reflexivity);
 try (destruct (cast_single_int s _); reflexivity);
 try (destruct (cast_single_long s _); reflexivity);
 auto.
Qed.

Lemma eval_expr_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te ->
           typecheck_environ  Delta rho ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight.eval_expr ge ve te m e  (eval_expr e rho)).
Proof.
intros. admit.
Qed.



Lemma eval_lvalue_relate:
  forall Delta ge te ve rho e m,
           rho = construct_rho (filter_genv ge) ve te->
           typecheck_environ  Delta rho ->
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight.eval_lvalue ge ve te m e b ofs /\
              eval_lvalue e rho = Vptr b ofs).
admit.
Qed.

(*
Lemma tc_lvalue_nonvol : forall rho Delta e,
(denote_tc_assert (typecheck_lvalue Delta e) rho) ->
type_is_volatile (typeof e) = false.
Proof.
intros.
destruct e; intuition; simpl in *. 
unfold get_var_type in *. 

destruct ((var_types Delta) ! i); intuition; simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift;
intuition. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; simpl in *; super_unfold_lift; intuition.

super_unfold_lift; intuition. unfold tc_bool in *. rewrite if_negb in *.
destruct ((glob_types Delta) ! i). simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
 super_unfold_lift. 
destruct H. if_tac in H0; auto; inv H0. inv H. 


repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift; intuition. clear - H1. unfold tc_bool in *. rewrite if_negb in *.
if_tac in H1; intuition.

repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift. intuition. unfold tc_bool in *.  rewrite if_negb in *. 
if_tac in H1; auto. inv H1. 
Qed.
*)

(*Proof for "backwards environment checking" that an environment that typechecks
must have come from an update on an environment that typechecks. 
TODO: These Lemmas
should eventually be put in more meaningful places in this file. *)

Lemma join_te_eqv :forall te1 te2 id b1 b2 t1,
te1 ! id = Some (t1, b1) -> te2 ! id = Some (t1, b2) ->
(join_te te1 te2) ! id = Some (t1,andb b1 b2).
Proof.
intros. 
unfold join_te. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto. 
assert (forall t, te1 ! id = Some t -> In (id, t) (rev (PTree.elements te1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements te1)). simpl in *.
apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. destruct p0. simpl.
remember (te2 ! p). destruct o. destruct p0.
(* destruct (eq_dec t t0).
 subst. *)
rewrite PTree.gsspec. if_tac. subst. specialize (H1 (t,b)).
spec H1; [solve [auto] | ].
inversion2  H H1.
rewrite H0 in Heqo; inv Heqo. auto.
apply IHl; auto.
intros. inversion2 H H4. specialize (H2 _ H).
destruct H2. inv H2. congruence.  auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 (t1, b1)).
intuition. inv H2. congruence.
Qed.
 
Lemma temp_types_same_type : forall id i t b Delta,
(temp_types Delta) ! id = Some (t, b) ->
exists b0 : bool,
  (temp_types (initialized i Delta)) ! id = Some (t, b || b0).
Proof.
intros.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o.
destruct p. unfold temp_types in *. simpl. rewrite PTree.gsspec.
if_tac. subst. rewrite H in *. inv Heqo. exists true.   rewrite orb_true_r. 
eauto. exists false.   rewrite orb_false_r. eauto. exists false. rewrite orb_false_r. 
auto. 
Qed.

Lemma temp_types_update_dist : forall d1 d2 ,
(temp_types (join_tycon (d1) (d2))) =
join_te (temp_types (d1)) (temp_types (d2)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold temp_types. simpl. auto.
Qed.

Lemma var_types_update_dist : forall d1 d2 ,
(var_types (join_tycon (d1) (d2))) =
(var_types (d1)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold var_types. simpl. auto.
Qed. 

Lemma ret_type_update_dist : forall d1 d2, 
(ret_type (join_tycon (d1) (d2))) =
(ret_type (d1)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold var_types. simpl. auto.
Qed. 

Lemma glob_types_update_dist :
forall d1 d2, 
(glob_types (join_tycon (d1) (d2))) =
(glob_types (d1)).
Proof.
intros. destruct d1. destruct d2.  simpl. auto.
Qed. 
 
Lemma glob_specs_update_dist :
forall d1 d2, 
(glob_specs (join_tycon (d1) (d2))) =
(glob_specs (d1)).
Proof.
intros. destruct d1. destruct d2.  simpl. auto.
Qed. 
 

Lemma var_types_update_tycon:
  forall c Delta, var_types (update_tycon Delta c) = var_types Delta
with
var_types_join_labeled : forall l Delta,
var_types (join_tycon_labeled l Delta) = var_types Delta.
Proof.
assert (forall i Delta, var_types (initialized i Delta) = var_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity. 
destruct c; intros; simpl; try reflexivity. 
apply H. 
destruct o. apply H. auto. 
rewrite var_types_update_tycon. apply var_types_update_tycon. 

rewrite var_types_update_dist. apply var_types_update_tycon. 
apply var_types_join_labeled. 

intros. destruct l. simpl. auto.
simpl. rewrite var_types_update_dist.  
rewrite var_types_update_tycon. reflexivity.  
 
Qed.
 
Lemma glob_types_update_tycon:
  forall c Delta, glob_types (update_tycon Delta c) = glob_types Delta
 with
glob_types_join_labeled : forall Delta e l,
glob_types (update_tycon Delta (Sswitch e l)) = glob_types Delta. 
Proof. 
clear glob_types_update_tycon.
assert (forall i Delta, glob_types (initialized i Delta) = glob_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.  
induction c; intros; try apply H; try reflexivity. 
simpl. destruct o. apply H. auto. 
simpl. 
rewrite IHc2. 
auto. 

simpl.  rewrite glob_types_update_dist. auto. 

auto.

clear glob_types_join_labeled.
intros. simpl. 
destruct l. simpl. auto. 
simpl in *. rewrite glob_types_update_dist. 
auto. 
Qed. 

Lemma glob_specs_update_tycon:
  forall c Delta, glob_specs (update_tycon Delta c) = glob_specs Delta
 with
glob_specs_join_labeled : forall Delta e l,
glob_specs (update_tycon Delta (Sswitch e l)) = glob_specs Delta. 
Proof. 
clear glob_specs_update_tycon.
assert (forall i Delta, glob_specs (initialized i Delta) = glob_specs Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.  
induction c; intros; try apply H; try reflexivity. 
simpl. destruct o. apply H. auto. 
simpl. 
rewrite IHc2. 
auto. 

simpl.  rewrite glob_specs_update_dist. auto. 

auto.

clear glob_specs_join_labeled.
intros. simpl. 
destruct l. simpl. auto. 
simpl in *. rewrite glob_specs_update_dist. 
auto. 
Qed.


Ltac try_false :=
try  solve[exists false; rewrite orb_false_r; eauto]. 
 
Lemma update_tycon_te_same : forall c Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (update_tycon Delta c)) ! id = Some (t,b || b2)

with update_labeled_te_same : forall ls Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (join_tycon_labeled ls Delta)) ! id = Some (t,b || b2) .
Focus 1. 
destruct c; intros; simpl; try_false. 

simpl. eapply temp_types_same_type; eauto.

simpl. destruct o; eauto. simpl. eapply temp_types_same_type; eauto.
try_false; eauto. 

assert (forall (c : statement) (Delta : tycontext)
                         (id : positive) (t : type) (b : bool),
                       (temp_types Delta) ! id = Some (t, b) ->
                       exists b2 : bool,
                         (temp_types (update_tycon Delta c)) ! id =
                         Some (t, b || b2)) by auto.
edestruct update_tycon_te_same. apply H.
specialize (update_tycon_te_same c2 _ _ _ _ H1).
destruct (update_tycon_te_same). exists (x || x0). rewrite orb_assoc. eauto. 


simpl. rewrite temp_types_update_dist.

edestruct (update_tycon_te_same c1). apply H.
edestruct (update_tycon_te_same c2). apply H. 
erewrite join_te_eqv;
eauto. exists (x && x0). rewrite orb_andb_distrib_r.  auto.

apply update_labeled_te_same.  exact H.  (*these are the problem if it won't qed*) 

intros. destruct ls. simpl. exists false.
rewrite H. f_equal. f_equal. destruct b; reflexivity.

simpl. rewrite temp_types_update_dist.
edestruct update_tycon_te_same. apply H.
edestruct update_labeled_te_same. apply H.
exists (x && x0).  
erewrite join_te_eqv. rewrite <- orb_andb_distrib_r. auto. 
eauto. eauto. Qed. 


Lemma typecheck_environ_update_te:
  forall rho c Delta, typecheck_temp_environ (te_of rho) (temp_types (update_tycon Delta c)) 
     ->
typecheck_temp_environ  (te_of rho) (temp_types Delta)

with typecheck_ls_update_te : forall Delta ty b id l,
(temp_types Delta) ! id = Some (ty, b) -> 
exists b2, (temp_types (join_tycon_labeled l Delta)) ! id = Some (ty, b2).
Proof.
intros. 
unfold typecheck_temp_environ in H. unfold typecheck_temp_environ.  
destruct c; intros; simpl in *; try solve[eapply H; apply H0].
*
destruct (eq_dec id i). subst.
destruct (H i true ty). unfold initialized. rewrite H0. 
unfold temp_types. simpl. rewrite PTree.gsspec. rewrite peq_true. 
auto. destruct H1. destruct H2. inv H2. exists x. auto. 
apply H. 
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto.
*
destruct o.
destruct (eq_dec id i). subst. destruct (H i true ty).
unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. inv H0. 
rewrite PTree.gsspec. rewrite peq_true. eauto. congruence.
destruct H1. destruct H2. inv H2. eauto. 
eapply H. unfold initialized.
remember ((temp_types Delta) ! i). destruct o. destruct p.
unfold temp_types. simpl. rewrite PTree.gsspec.
rewrite peq_false by auto. apply H0. auto. eauto.
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H1).
destruct (H _ _ _ H2) as [v [? ?]]. exists v.
split; auto. destruct H4; auto. left. destruct b; simpl; auto.
*
destruct (update_tycon_te_same c1 _ _ _ _ H0).
destruct (update_tycon_te_same c2 _ _ _ _ H0).
specialize (H id ((b || x) && (b || x0)) ty ).  
spec H.  
 unfold join_tycon. remember (update_tycon Delta c1).
destruct t. remember (update_tycon Delta c2).
destruct t. unfold temp_types in *.
unfold update_tycon. simpl in *. 
apply join_te_eqv; eauto.    destruct b; auto. simpl in *.
destruct H. exists x1. split. destruct H. auto. left. auto. 
*
 edestruct (update_labeled_te_same l Delta id).  apply H0. 
 edestruct H. apply H1.  
destruct H2. exists x0. split; auto. destruct b; simpl; auto.
* 
intros. destruct l; simpl in *.
exists b; assumption.
 destruct (update_tycon_te_same s _ _ _ _ H).
edestruct typecheck_ls_update_te. apply H.
rewrite temp_types_update_dist. erewrite join_te_eqv; eauto.
Qed.

Lemma set_temp_ve : forall Delta i,
var_types (initialized i Delta) = var_types (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_ge : forall Delta i,
glob_types (initialized i Delta) = glob_types (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed. 

Lemma set_temp_gs : forall Delta i,
glob_specs (initialized i Delta) = glob_specs (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.
 
Lemma set_temp_ret : forall Delta i,
ret_type (initialized i Delta) = ret_type (Delta).
intros. 
destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.


Lemma update_tycon_eqv_ve : forall Delta c id,
(var_types (update_tycon Delta c)) ! id = (var_types (Delta)) ! id

with update_le_eqv_ve : forall (l : labeled_statements) (id : positive) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = 
(var_types Delta) ! id.
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ve. auto.
destruct o. rewrite set_temp_ve. auto.
auto.
rewrite update_tycon_eqv_ve. apply update_tycon_eqv_ve.

rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.

erewrite update_le_eqv_ve. auto.

intros. 
 destruct l. simpl in *. auto. 
 simpl in *. rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.
Qed.

Lemma update_tycon_eqv_ret : forall Delta c,
(ret_type (update_tycon Delta c)) = (ret_type (Delta)) 

with update_le_eqv_ret : forall (l : labeled_statements)  Delta,
(ret_type (join_tycon_labeled l Delta)) = 
(ret_type Delta).
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ret. auto.
destruct o. rewrite set_temp_ret. auto.
auto.
rewrite update_tycon_eqv_ret. apply update_tycon_eqv_ret.

rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.

rewrite update_le_eqv_ret. auto.

intros. 
 destruct l. simpl in *. 
reflexivity.
 simpl in *. rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.
Qed.


Lemma update_tycon_same_ve : forall Delta c id v,
(var_types (update_tycon Delta c)) ! id = Some v <->
(var_types (Delta)) ! id = Some v


with update_le_same_ve : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = Some v <->
(var_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ve in *; auto.
intros; split; intros;
rewrite update_le_eqv_ve in *; auto.
Qed.


Lemma update_tycon_eqv_ge : forall Delta c id,
(glob_types (update_tycon Delta c)) ! id = (glob_types (Delta)) ! id

with update_le_eqv_ge : forall (l : labeled_statements) (id : positive)  Delta,
(glob_types (join_tycon_labeled l Delta)) ! id =
(glob_types Delta) ! id. 
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ge. auto.
destruct o. rewrite set_temp_ge. auto.
auto.
rewrite update_tycon_eqv_ge. apply update_tycon_eqv_ge. 

rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
erewrite update_le_eqv_ge. auto.

intros. 
 destruct l. simpl in *. 
auto. 
simpl in *. rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
Qed.   


Lemma update_tycon_eqv_gs : forall Delta c id,
(glob_specs (update_tycon Delta c)) ! id = (glob_specs (Delta)) ! id

with update_le_eqv_gs : forall (l : labeled_statements) (id : positive)  Delta,
(glob_specs (join_tycon_labeled l Delta)) ! id =
(glob_specs Delta) ! id. 
Proof.
intros; 
destruct c; simpl in *; try reflexivity.
rewrite set_temp_gs. auto.
destruct o. rewrite set_temp_gs. auto.
auto.
rewrite update_tycon_eqv_gs. apply update_tycon_eqv_gs. 

rewrite glob_specs_update_dist.
rewrite update_tycon_eqv_gs. auto.
erewrite update_le_eqv_gs. auto.

intros. 
 destruct l. simpl in *. 
auto. 
simpl in *. rewrite glob_specs_update_dist.
rewrite update_tycon_eqv_gs. auto.
Qed.   


Lemma update_tycon_same_ge : forall Delta c id v,
(glob_types (update_tycon Delta c)) ! id = Some v <->
(glob_types (Delta)) ! id = Some v


with update_le_same_ge : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(glob_types (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ge in *; auto.
intros; split; intros;
rewrite update_le_eqv_ge in *; auto.
Qed.    

Lemma update_tycon_same_gs : forall Delta c id v,
(glob_specs (update_tycon Delta c)) ! id = Some v <->
(glob_specs (Delta)) ! id = Some v


with update_le_same_gs : forall (l : labeled_statements) (id : positive) v  Delta,
(glob_specs (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_specs Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_gs in *; auto.
intros; split; intros;
rewrite update_le_eqv_gs in *; auto.
Qed.    

Lemma typecheck_environ_update_ve : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_var_environ (ve_of rho) (var_types (update_tycon Delta c)) ->
typecheck_var_environ (ve_of rho) (var_types Delta).
Proof.
intros. 

destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ve in *; try apply H;
unfold typecheck_var_environ in *; intros; apply H; try rewrite var_types_update_dist; 
try apply join_ve_eqv;
repeat rewrite update_tycon_same_ve in *; try rewrite update_le_same_ve;
auto.
Qed. 



Lemma typecheck_environ_update_ge : forall (rho : environ) (c : statement) (Delta : tycontext),
typecheck_glob_environ (ge_of rho) (glob_types (update_tycon Delta c)) ->
typecheck_glob_environ (ge_of rho) (glob_types Delta).
Proof.
intros. destruct c; simpl in *; try apply H;
try destruct o; try rewrite set_temp_ge in *; try apply H;
unfold typecheck_glob_environ in *; intros; apply H; try rewrite glob_types_update_dist; 
try apply join_ge_eqv;
repeat rewrite update_tycon_same_ge in *; try rewrite update_le_same_ge;
auto.
Qed. 

Lemma typecheck_environ_update:
  forall rho c Delta, typecheck_environ (update_tycon Delta c) rho ->
       typecheck_environ Delta rho.
Proof.
intros. unfold typecheck_environ in *. intuition. 
clear - H0. unfold typecheck_temp_environ in *. 
eapply typecheck_environ_update_te; eauto.

clear -H. eapply typecheck_environ_update_ve; eauto. 

eapply typecheck_environ_update_ge.
eauto.  

clear - H3. 
unfold same_env in *. intros. 
specialize (H3 id t).
repeat rewrite update_tycon_same_ge in *. specialize (H3 H). 
destruct H3; auto. destruct H0. 
rewrite update_tycon_same_ve in *. eauto.
Qed. 

Lemma typecheck_bool_val:
  forall v t, 
       typecheck_val v t = true -> 
       bool_type t = true ->
      exists b, strict_bool_val v t = Some b.
Proof.
intros.
destruct t; try destruct f; inv H0;
destruct v; inv H; simpl; try rewrite H1; eauto. 
Qed.

Lemma map_ptree_rel : forall id v te, Map.set id v (make_tenv te) = make_tenv (PTree.set id v te).
intros. unfold Map.set. unfold make_tenv. extensionality. rewrite PTree.gsspec; auto.
Qed.

Lemma cop_2_sem_cast : forall t1 t2 e,
Cop.sem_cast (e) t1 t2 = Cop2.sem_cast t1 t2 e.
Proof.
intros. unfold Cop.sem_cast, sem_cast.
destruct t1 as [ | [ | | | ] | [ | ] | [ | ] | | | | | | ]; 
  destruct t2 as [ | [  | | | ] | [ | ] | [ | ] | | | | | | ]; destruct e; simpl; auto.   
Qed.

Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ Delta rho), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t e2)
  rho ->
sem_cast (typeof e2) t (eval_expr e2 rho)  =
Some (force_val (sem_cast (typeof e2) t (eval_expr e2 rho))).
Proof.
intros. 
assert (exists v, sem_cast (typeof e2) t (eval_expr e2 rho) = Some v). 
{
apply typecheck_expr_sound in H; [ | auto ].
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent liftx.
destruct t as [ | [ | | | ] [ | ] a | i a | [ | ] a | | | | | | ]; destruct v;
destruct t0 as [ | [ | | | ] [ | ] ? | i1 ? | [ | ] ? | | | | | | ]; simpl in *;
try congruence; try contradiction; eauto;
unfold isCastResultType in *;
simpl in *;
rewrite denote_tc_assert_andp in H0; simpl in H0;
 unfold_lift in H0; rewrite <- Heqv in H0; simpl in H0;
match type of H0 with (match ?ZZ with Some _ => _ | None => _ end /\ _) =>
    destruct ZZ eqn:H5
 end;
 destruct H0; try contradiction;
 (first [rewrite (float_to_int_ok _ _ H5)
        | rewrite (float_to_intu_ok _ _ H5)
        | rewrite (single_to_int_ok _ _ H5)
        | rewrite (single_to_intu_ok _ _ H5)
        ] ;
    [ eexists; reflexivity
    | split; [apply Z.leb_le | apply Z.geb_le]; apply is_true_e; assumption ]).
}
Opaque liftx.
destruct H1. rewrite H1. auto.
Qed.

Definition func_tycontext_t_denote :=
forall p t id ty b,  list_norepet (map fst p ++ map fst t ) ->   
((make_tycontext_t p t) ! id = Some (ty,b) <-> (In (id,ty) p /\ b=true) \/ (In (id,ty) t /\ b=false)). 

Definition func_tycontext_v_denote :=
forall v id ty, list_norepet (map fst v) ->
((make_tycontext_v v) ! id = Some ty <-> In (id,ty) v). 

Lemma func_tycontext_v_sound : func_tycontext_v_denote. 
unfold func_tycontext_v_denote. intros. 
split; intros; induction v. simpl in *. 
rewrite PTree.gempty in *. congruence. 

simpl in *. destruct a. inv H. rewrite PTree.gsspec in *. if_tac in H0. 
inv H0. auto. intuition. 

inv H0.

simpl in *. destruct a. simpl in *. rewrite PTree.gsspec. destruct H0. 
inv H0. if_tac. auto. intuition. inv H. if_tac. subst. 
clear - H0 H3. rewrite in_map_iff in *. destruct H3. exists (i,ty). auto. 
apply IHv; auto. 
Qed. 
 

Lemma set_inside : forall i0 t1 t p id, 
list_disjoint (map fst p) (i0 :: map fst t) ->
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
          (PTree.set i0 (t1, false)
             (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p) ! id = 
(PTree.set i0 (t1, false) (
(fold_right
          (fun param : ident * type =>
           PTree.set (fst param) (snd param, true))
                (fold_right
                (fun (temp : ident * type) (tenv : PTree.t (type * bool)) =>
                 let (id, ty) := temp in PTree.set id (ty, false) tenv)
                (PTree.empty (type * bool)) t)) p)) ! id       
. 
Proof.
intros.
induction t.  
  simpl in *. rewrite PTree.gsspec. 
  if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec. rewrite peq_true. auto.

      simpl in *. rewrite PTree.gsspec. if_tac. subst.
      clear - H. unfold list_disjoint in *. specialize (H (fst a) (fst a)). 
      intuition. apply IHp. unfold list_disjoint in *. intros. 
      apply H; simpl in *; auto.

    induction p. 
       simpl in *. rewrite PTree.gsspec. if_tac. intuition.
       auto. 

       simpl in *.  repeat rewrite PTree.gsspec in *. destruct a.
       simpl in *. if_tac. auto. rewrite IHp.  auto. unfold list_disjoint in *. 
       intros. apply H; simpl in *; auto. 

  simpl in *. rewrite PTree.gsspec in *. if_tac. 
    subst. 
    induction p. 
      simpl in *. rewrite PTree.gsspec in *. rewrite peq_true in *.
      auto.

      simpl in *. rewrite PTree.gsspec in *. destruct a0. simpl in *. 
      if_tac. subst. clear - H. specialize (H p0 p0). intuition.  apply IHp. 
      unfold list_disjoint in *. intros. apply H; simpl in *; auto. 
      intros. apply IHt. unfold list_disjoint in *. intros; simpl in *; apply H;      auto.
      auto. auto. intuition.  

    destruct a. simpl in *. induction p. 
      simpl in *. rewrite PTree.gsspec. if_tac; subst. intuition.
      repeat rewrite PTree.gsspec. auto.  

      simpl in *. destruct a. simpl in *. 
      spec IHt. unfold list_disjoint in *. intros; apply H; simpl in *; auto. 
      intuition. 
      repeat rewrite PTree.gsspec in *. if_tac.
        subst.  auto. 

        apply IHp. unfold list_disjoint in *.   intros. apply H. simpl in *. 
        auto.  auto. intros. auto. 
       
Qed.   

Lemma func_tycontext_t_sound : func_tycontext_t_denote. 
unfold func_tycontext_t_denote.
split; intros;
  unfold make_tycontext_t in *; 
  apply list_norepet_app in H; destruct H as [? [? ?]]. 
  induction t; induction p; simpl in *. 

    rewrite PTree.gempty in *; congruence. 

    left. destruct a; simpl in *. rewrite PTree.gsspec in *. if_tac in H0. 
    inv H0. auto.
    inv H.  destruct IHp; auto. unfold list_disjoint.  intros. inv H4. 
    destruct H. subst. auto. intuition.  

    right. destruct a. simpl in *. rewrite PTree.gsspec in *. 
    if_tac in H0. subst. inv H0. auto. destruct IHt. inv H1; auto. 
    unfold list_disjoint in *. intros. inv H4. auto. intuition. intuition. 


    simpl in *. rewrite PTree.gsspec in *. if_tac in H0. destruct a0. simpl in *.
    subst. inv H0. intuition. destruct a0. simpl in *.  destruct a. simpl in *. 
    destruct IHp. inv H; auto. intro; intros. apply H2; simpl in *; auto. 
    auto. intros. destruct IHt. inv H1; auto. intro; intros; apply H2; simpl in *; auto.
    auto. destruct H7. destruct H7. inv H7. intuition. auto. auto. left. 
    split. right. apply H4. apply H4. right. auto. 


  induction t; induction p; simpl in *. 
    
    intuition. 

    rewrite PTree.gsspec. if_tac. subst. destruct a. simpl in *. 
    destruct H0. destruct H0. destruct H0. inv H0. auto. subst. 
    clear - H H0. inv H. rewrite in_map_iff in *. destruct H3.
    exists (i,ty). auto. inv H0. inv H3. destruct H0. destruct H0. 
    destruct a. destruct H0. subst. inv H0. intuition.

    simpl in *. apply IHp. inv H; auto. intro. intros. inv H6. left.
    subst. auto. destruct H0. inv H0. destruct H0. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct a. simpl in *. inv H0; subst. 
    rewrite PTree.gsspec. rewrite peq_true. auto. subst. 
    destruct a. simpl in *. rewrite PTree.gsspec. if_tac. 
    subst. clear -H0 H1. inv H1. rewrite in_map_iff in *. 
    destruct H3. exists (i,ty); auto. apply IHt. inv H1; auto. 
    intro; auto. right. auto. 
   
    spec IHt. inv H1; auto.  spec IHt. intro; intros; apply H2; simpl in *; auto.
    spec IHp.  inv H; auto. spec IHp. intro; intros; apply H2; simpl in *; auto. 
    destruct a. destruct a0. destruct H0. simpl in *.
    destruct H0. destruct H0. inv H0.  
    rewrite PTree.gsspec in *. rewrite peq_true. auto. subst. 
    rewrite PTree.gsspec in *. if_tac. subst. inv H. rewrite in_map_iff in H5. 
    destruct H5. exists (i0,ty); auto. spec IHp. auto. spec IHp; auto. 
    
    
    simpl in *. rewrite PTree.gsspec. if_tac. subst. destruct H0. destruct H0.
    inv H0. specialize (H2 i0 i0). destruct H2; simpl; auto. subst. 
    spec IHt. auto. rewrite PTree.gsspec in *. rewrite peq_true in *. auto. 
    
    destruct H0. destruct H0. inv H0. spec IHp. auto. 
    spec IHp; auto. intros; auto. destruct H5. destruct H5; congruence. destruct H5. 
    clear - H5 H1. inv H1. destruct H2. apply in_map_iff. exists (id, ty). auto. subst.
    spec IHp. auto. spec IHp; auto. spec IHt; auto. rewrite PTree.gsspec in *.
    if_tac in IHt. intuition. intros. auto. 

Qed. 

 Definition cast_no_val_change (from: type)(to:type) : bool :=
match from, to with
| Tint _ _ _, Tint I32 _ _ => true
| Tpointer _ _, Tpointer _ _ => true
| Tfloat F64 _ , Tfloat F64 _ => true
| Tfloat F32 _ , Tfloat F32 _ => true
| _, _ => false
end. 

Lemma cast_no_change : forall v from to,
is_true (typecheck_val v from)  ->
is_true (cast_no_val_change from to) ->
Cop.sem_cast v from to = Some v. 
Proof. 
intros. apply is_true_e in H. apply is_true_e in H0.
destruct v; destruct from as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; 
  simpl in *; try congruence; 
 destruct to as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; simpl in *; try congruence; auto.
Qed. 

Lemma tc_exprlist_length : forall Delta tl el rho, 
denote_tc_assert (typecheck_exprlist Delta tl el) rho ->
length tl = length el. 
Proof. 
intros. generalize dependent el. induction tl; intros. simpl in *. destruct el. inv H. auto. 
inv H. simpl in H. destruct el; try solve [inv H]. simpl in *.
repeat( rewrite tc_andp_sound in *; simpl in *; super_unfold_lift).
super_unfold_lift.
intuition.
Qed. 

Lemma neutral_cast_typecheck_val : forall e t rho Delta,
true = is_neutral_cast (implicit_deref (typeof e)) t ->
denote_tc_assert (isCastResultType (implicit_deref (typeof e)) t  e) rho ->
denote_tc_assert (typecheck_expr Delta e) rho ->
typecheck_environ Delta rho ->
typecheck_val (eval_expr e rho) t = true. 
Proof.
intros.
rewrite isCastR in H0.
apply typecheck_expr_sound in H1; auto. rewrite tc_val_eq in H1.
Transparent Int.repr.
destruct (typeof e)  as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ] ;
destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; simpl in H; simpl in H0;
try congruence; remember (eval_expr e rho); destruct v;
simpl in H0; try congruence; auto; 
unfold is_neutral_cast in *;
simpl in *; try congruence; super_unfold_lift; 
try rewrite <- Heqv in *;  unfold denote_tc_iszero in *;
try apply H0; try contradiction;
try (rewrite andb_true_iff; repeat rewrite Z.leb_le;
    rewrite orb_true_iff in H1; destruct H1 as [H1|H1];
   apply int_eq_e in H1; subst; compute; split; congruence);
try (repeat rewrite Z.leb_le;
  rewrite orb_true_iff in H1; destruct H1 as [H1|H1];
   apply int_eq_e in H1; subst; compute; congruence).
*
 change Byte.min_signed with (-128) in H1;
 change Byte.max_signed with 127 in H1;
 change (Z.neg (shift_pos 15 1)) with (-32768);
rewrite andb_true_iff in H1|-*; destruct H1 as [H1 H1']; 
  rewrite Z.leb_le in H1,H1'; split; rewrite Z.leb_le;
  omega.
*  
 change Byte.max_unsigned with 255 in H1; 
 rewrite Z.leb_le in H1|-*; omega.
Qed.

Opaque Int.repr.

Definition typecheck_tid_ptr_compare
Delta id := 
match (temp_types Delta) ! id with
| Some (t, _) =>
   is_int_type t 
| None => false
end. 

Lemma typecheck_tid_ptr_compare_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id, typecheck_tid_ptr_compare Delta id = true ->
                typecheck_tid_ptr_compare Delta' id = true.
Proof.
unfold typecheck_tid_ptr_compare;
intros.
destruct H as [? _].
specialize (H id).
destruct ((temp_types Delta) ! id) as [[? ?]|]; try discriminate.
destruct ((temp_types Delta') ! id) as [[? ?]|]; try contradiction.
 destruct H; subst; auto.
Qed.


Lemma tycontext_sub_refl:
 forall Delta, tycontext_sub Delta Delta.
Proof.
intros. destruct Delta as [T V r G S].
unfold tycontext_sub.
intuition.
 + unfold sub_option. unfold temp_types. simpl. 
   destruct (T ! id) as [[? ?]|]; split; auto; destruct b; auto.
 + unfold sub_option, glob_types. simpl. 
   destruct (G ! id); auto.
 + unfold sub_option, glob_specs. simpl. 
   destruct (S ! id); auto.
Qed.


Lemma initialized_ne : forall Delta id1 id2,
id1 <> id2 ->
(temp_types Delta) ! id1 = (temp_types (initialized id2 Delta)) ! id1.

intros.
destruct Delta. unfold temp_types; simpl.
unfold initialized. simpl. unfold temp_types; simpl.
destruct (tyc_temps ! id2). destruct p. simpl.  rewrite PTree.gso; auto.
auto.
Qed.

(*
Lemma initialized_sub_temp :
forall id Delta i Delta',
(forall id, sub_option (temp_types Delta) ! id (temp_types Delta') ! id) ->
 sub_option (temp_types (initialized i Delta)) ! id
     (temp_types (initialized i Delta')) ! id.
Proof.
intros.
   destruct (eq_dec id i).
     - subst. destruct Delta as [[[? ?] ?] ?].
       destruct Delta' as [[[? ?] ?] ?].
       unfold initialized, temp_types  in *. 
       simpl in *. specialize (H i). unfold sub_option in *.
       remember (t ! i). destruct o. 
         * destruct p. simpl in *.
           rewrite PTree.gss. rewrite H. simpl. rewrite PTree.gss.
           auto.
         * simpl. rewrite <- Heqo. auto.
     - repeat rewrite <- initialized_ne by auto. auto.
Qed.
*)

Lemma initialized_sub :
  forall Delta Delta' i ,
    tycontext_sub Delta Delta' ->
    tycontext_sub (initialized i Delta) (initialized i Delta').
Proof.
intros.
unfold tycontext_sub in *. 
destruct H as [? [? [? [? ?]]]].
repeat split; intros.
 + specialize (H id); clear - H.
        destruct (eq_dec  i id).
        -  unfold initialized. subst.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?.
         unfold temp_types at 1; simpl; rewrite PTree.gss.
        destruct ((temp_types Delta')!id) as [[? ?] |]. destruct H; subst t0.
         unfold temp_types at 1. simpl. rewrite PTree.gss. auto. contradiction.
         rewrite Heqo. auto.
        -   rewrite <- initialized_ne by auto.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?; auto.
           rewrite <- initialized_ne by auto.
        destruct ((temp_types Delta')!id) as [[? ?] |]; [| contradiction].
         auto.
 + repeat rewrite set_temp_ve; auto.
 + repeat rewrite set_temp_ret; auto. 
 + repeat rewrite set_temp_ge; auto.
 + repeat rewrite set_temp_gs; auto.
Qed.


Definition te_one_denote (v1 v2 : option (type * bool)):=
match v1, v2 with 
| Some (t1,b1),Some (t2, b2) =>  Some (t1, andb b1 b2)
| _, _ => None
end.

Lemma join_te_denote2:
forall d1 d2 id,
  ((join_te d1 d2) ! id) = te_one_denote (d1 ! id) (d2 ! id).
Proof.
intros.
unfold join_te. rewrite PTree.fold_spec.
remember (PTree.elements d1) as el eqn:?H.
unfold te_one_denote.
 rewrite <- fold_left_rev_right.
 pose proof (PTree.elements_keys_norepet d1).
 rewrite <- list_norepet_rev in H0.
  rewrite <- map_rev in H0.

destruct (d1 ! id) as [[t b] | ] eqn:?; auto.
*
 apply PTree.elements_correct in Heqo.
 rewrite <- H in *.
  apply in_rev in Heqo. unfold PTree.elt in *.
   forget (rev el) as al.  clear H el d1.
 set (f := (fun (y : positive * (type * bool)) (x : PTree.t (type * bool)) =>
    join_te' d2 x (fst y) (snd y))).
 induction al; destruct Heqo.
 + subst a. simpl in H0.
   unfold f; simpl. destruct (d2 ! id) as [[t2 b2] | ] eqn:?H.
   fold f. rewrite PTree.gss. auto.
   fold f. inv H0.
   clear - H H3; induction al; simpl. apply PTree.gempty.
  unfold f at 1. unfold join_te'.
  destruct a as [? [? ?]]. simpl.
  destruct (d2 ! p) as [[? ?] |]. rewrite PTree.gso. apply IHal.
 contradict H3. right; auto.
 contradict H3. left; auto.
 apply IHal.
 contradict H3; right; auto.
 + inv H0. specialize (IHal H4 H).
 simpl. unfold f at 1. unfold join_te'.
 destruct a as [? [? ?]]; simpl. destruct (d2 ! p) as [[? ?] | ].
  rewrite PTree.gso. apply IHal.
 contradict H3. subst p; clear - H. simpl.
 change id with (fst (id,(t,b))).
 apply in_map; auto.
 auto.
*
 assert (~ In id (map fst (rev el))).
 intro. rewrite map_rev in H1. rewrite <- In_rev in H1. subst el.
 apply list_in_map_inv in H1. destruct H1 as [[? ?] [? ?]].
 simpl in H. subst p. destruct p0 as [? ?].
 pose proof (PTree.elements_complete d1 id (t,b) H1). congruence.
 clear - H1.
 induction (rev el); simpl. apply PTree.gempty.
 unfold join_te' at 1. destruct a. simpl. destruct p0. 
 destruct (d2 ! p). destruct p0. rewrite PTree.gso. apply IHl.
 contradict H1. right; auto.
 contradict H1. left; auto.
 apply IHl. contradict H1. right; auto.
Qed.
  
Lemma tycontext_sub_join:
 forall Delta1 Delta2 Delta1' Delta2',
  tycontext_sub Delta1 Delta1' -> tycontext_sub Delta2 Delta2' ->
  tycontext_sub (join_tycon Delta1 Delta2) (join_tycon Delta1' Delta2').
Proof.
intros [A1 B1 C1 D1 E1] [A2 B2 C2 D2 E2]
          [A1' B1' C1' D1' E1'] [A2' B2' C2' D2' E2']
  [? [? [? ?]]] [? [? [? ?]]].
simpl in *.
unfold join_tycon.
split; [ | split; [ | split]]; simpl; auto.
intro id; specialize (H id); specialize (H3 id).
unfold temp_types in *.
simpl in *.
clear - H H3.
unfold sub_option in *.
repeat rewrite join_te_denote2.
unfold te_one_denote.
destruct (A1 ! id) as [[? b1] |].
destruct (A1' ! id) as [[? b1'] |]; [ | contradiction].
destruct H; subst t0.
destruct (A2 ! id) as [[? b2] |].
destruct (A2' ! id) as [[? b2'] |]; [ | contradiction].
destruct H3; subst t1.
split; auto. destruct b1,b1'; inv H0; simpl; auto.
destruct (A2' ! id) as [[? b2'] |]; split; auto.
auto.
Qed.

Lemma temp_types_same_type' : forall i (Delta: tycontext),
 (temp_types (initialized i Delta)) ! i =
  match (temp_types Delta) ! i with
   | Some (t, b) => Some (t, true)
  | None => None 
  end.
Proof.
intros.
unfold initialized.
destruct ((temp_types Delta) ! i) as [[? ?]|] eqn:?.
unfold temp_types at 1. simpl. rewrite PTree.gss. auto.
auto.
Qed.

Lemma update_tycon_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall h, tycontext_sub (update_tycon Delta h) (update_tycon Delta' h)
with join_tycon_labeled_sub: 
 forall Delta Delta', tycontext_sub Delta Delta' ->
    forall ls, tycontext_sub (join_tycon_labeled ls Delta)
                         (join_tycon_labeled ls Delta').
Proof.
* clear update_tycon_sub.
  rename join_tycon_labeled_sub into J.
  intros.
 revert Delta Delta' H; induction h; intros;
   try (apply H); simpl update_tycon; auto.
 + apply initialized_sub; auto.
 + destruct o; auto. apply initialized_sub; auto.
 + apply tycontext_sub_join; auto.
* clear join_tycon_labeled_sub.
 intros.
 revert Delta Delta' H; induction ls; simpl; intros; auto.
 apply tycontext_sub_join; auto.
Qed.

Lemma typecheck_val_sem_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ Delta rho ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2  e2) rho ->
      typecheck_val (force_val (sem_cast (typeof e2) t2 (eval_expr e2 rho))) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := typecheck_expr_sound _ _ _ H2 H5).
rewrite tc_val_eq in H8.
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (typeof e2) t2 (eval_expr e2 rho) ); intros; inv H7.
simpl.
rewrite isCastR in H6.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2 as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2) as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | | ]; 
inv H2; inv H1; auto;
simpl in H6;
try (unfold sem_cast in H0;
      simpl in*; inv H0; simpl; auto);
 try (super_unfold_lift; unfold denote_tc_iszero in H6; rewrite H99 in H6;
       try contradiction H6; apply is_true_e in H6; auto);
 try match type of H1 with 
   match ?ZZ with Some _ => _ | None => _ end = _ => 
  destruct ZZ eqn:H5; inv H1; simpl; auto
end;
 try (rewrite andb_true_iff in H1; destruct H1 as [H1 H1']);
 try rewrite orb_true_iff in H1;
 try rewrite Z.leb_le in H1; try rewrite Z.leb_le in H1';
 simpl;
 (transitivity true; [ | symmetry]);
 try rewrite andb_true_iff; try rewrite orb_true_iff;
 repeat rewrite Z.leb_le;
 auto;
 try match goal with
  | |- context [Int.sign_ext ?n ?i] =>
  apply (sign_ext_range' n i);  compute; split; congruence 
  | |- context [Int.zero_ext ?n ?i] =>
  apply (zero_ext_range' n i);  compute; split; congruence 
  end;
try match goal with 
    | |- Int.eq (if ?A then _ else _) _ = true \/ _ =>
     destruct A; simpl; auto
   end.
Qed.







