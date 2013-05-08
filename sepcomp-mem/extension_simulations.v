Require Import ListSet.
Require Import Coq.Logic.Decidable.

Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.
Require Import sepcomp.extension.
Require Import sepcomp.compile_safe.
Require Import sepcomp.Coqlib2.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import sepcomp.Memory.
Require Import sepcomp.Globalenvs.
Require Import sepcomp.Events.

Set Implicit Arguments.

(**  "Compilable" Extensions *)

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (ge: Genv.t F V) := 
  (fun b => exists id, Genv.find_symbol ge id = Some b,
   fun b => exists gv, Genv.find_var_info ge b = Some gv).

Section CoreCompatibleDefs. Variables
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: EffectfulSemantics G xT D) (** extended semantics *)
 (esig: ef_ext_spec mem Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, EffectfulSemantics (gT i) (cT i) (dT i)) (** a set of core semantics *)
 (csig: ef_ext_spec mem Z). (** client signature *)

 Variables (ge: G) (genv_map : forall (u:nat), gT u).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.
 Variable core_compat: core_compatible ge genv_map E.

 Import Extension.

 Definition owned_valid s m := 
  forall i j c, proj_core E i j s = Some c -> 
  forall b ofs, effects (csem j) c AllocEffect b ofs -> 
    b < Mem.nextblock m.
  
 Definition owned_disjoint s :=
  forall i j i' j' (c: cT i') (d: cT j'),
  i<>j -> 
  proj_core E i i' s = Some c ->   
  proj_core E j j' s = Some d ->   
  forall b ofs, effects (csem i') c AllocEffect b ofs -> 
    ~effects (csem j') d AllocEffect b ofs.

 Definition owned_conserving := 
   forall s i j (c: cT j),
   proj_core E i j s = Some c -> 
   forall b ofs, effects (csem j) c AllocEffect b ofs -> 
     effects esem s AllocEffect b ofs.

 Definition new_effects_aligned :=
   forall j s c m s' c' m',
   proj_core E (active E s) j s = Some c -> 
   corestep (csem j) (genv_map j) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   (forall k b ofs, 
    new_effect esem k b ofs s s' <-> 
    new_effect (csem j) k b ofs c c').

End CoreCompatibleDefs.

Module CompilabilityInvariant. Section CompilabilityInvariant. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: forall i:nat, EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) 
 (** a set of core semantics *)
  (csemT: forall i:nat, EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat)
  (num_modules: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall (u:nat), Genv.t (fS u) (vS u))
  (genv_mapT: forall (u:nat), Genv.t (fT u) (vT u)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature). (*TODO: SHOULD PERHAPS BE GENERALIZED*)
 Variable core_data: forall u: nat, Type.
 Variable match_state: forall (u: nat), 
   core_data u -> meminj -> cS u -> mem -> cT u -> mem -> Prop.
 Variable core_ord: forall u: nat, (core_data u) -> (core_data u) -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation zint_invar_after_external := (Extension.zint_invar_after_external).

 Definition core_datas := forall u i: nat, core_data u.

 Definition core_ords (max_cores: nat) (cd1 cd2: core_datas) :=
  prod_ord' 
    (fun u => forall i:nat, core_data u)
    (fun u cd1' cd2' => 
      prod_ord' 
        (fun i => core_data u)
        (fun i => core_ord u)
        max_cores max_cores 
        (data_prod' _ _ _ cd1') (data_prod' _ max_cores max_cores cd2'))
    num_modules num_modules
    (data_prod' _ _ _ cd1) (data_prod' _ num_modules num_modules cd2).

 Variable (R: meminj -> xS -> mem -> xT -> mem -> Prop).

 Definition match_states (cd: core_datas) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   owned_valid esemS csemS E_S s1 m1 /\ 
   owned_disjoint esemS csemS E_S s1 /\ 
   owned_valid esemT csemT E_T s2 m2 /\ 
   owned_disjoint esemT csemT E_T s2 /\
   core_semantics.effects_valid esemS s1 m1 /\ 
   core_semantics.effects_valid esemT s2 m2 /\
   mem_wd m1 /\ mem_wd m2 /\
   effects_guarantee esemS s1 m1 /\ effects_guarantee esemT s2 m2 /\
   R j s1 m1 s2 m2 /\ 
   ACTIVE E_S s1=ACTIVE E_T s2 /\
   (forall b0 delta b ofs, 
     j b0 = Some (b, delta) -> 
     reserved m1 b0 (ofs-delta) -> reserved m2 b ofs) /\
   (*invariant on active cores*)
   (forall u c1, 
     PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
     effects_guarantee (csemS u) c1 m1 /\
     (exists z: Z, 
       compile_safe (csemS u) z c1 m1) /\
     exists c2, PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 /\ 
       effects_guarantee (csemT u) c2 m2 /\
       match_state u (cd u (ACTIVE E_S s1)) j c1 m1 c2 m2) /\
   (*invariant on inactive cores*)
   (forall i u c1, 
     i <> ACTIVE E_S s1 -> 
     PROJ_CORE E_S i u s1 = Some c1 -> 
     exists c2, PROJ_CORE E_T i u s2 = Some c2 /\ 
     exists cd0 j0 m10 m20,
       effects_guarantee (csemS u) c1 m10 /\
       (exists z: Z, compile_safe (csemS u) z c1 m10) /\
       effects_guarantee (csemT u) c2 m20 /\
       match_state u cd0 j0 c1 m10 c2 m20).

 Inductive Sig: Type := Make: forall  
 (corestep_rel: forall cd j j' u s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' s1' s2' n cd', 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   meminj_preserves_globals_ind (genv2blocks ge_S) j -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   corestep (csemS u) (genv_mapS u) c1 m1 c1' m1' -> 
   corestepN (csemT u) (genv_mapT u) n c2 m2 c2' m2' ->
   corestep esemS ge_S s1 m1 s1' m1' -> 
   corestepN esemT ge_T n s2 m2 s2' m2' -> 
   match_state u cd' j' c1' m1' c2' m2' -> 
   effects_guarantee (csemS u) c1' m1' -> 
   effects_guarantee (csemT u) c2' m2' -> 
   R j' s1' m1' s2' m2')

 (after_external_rel: 
   forall cd j j' s1 m1 s2 m2 s1' m1' s2' m2' ret1 ret2 ef sig args1,
   match_states cd j s1 m1 s2 m2 -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   Mem.inject j' m1' m2' -> 
   mem_forward m1 m1'-> 
   mem_forward m2 m2' -> 
   rely esemS s1' m1 m1' -> 
   rely esemT s2' m2 m2' -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   after_external esemS ret1 s1 = Some s1' -> 
   after_external esemT ret2 s2 = Some s2' -> 
   val_has_type_opt ret1 (ef_sig ef) -> 
   val_has_type_opt ret2 (ef_sig ef) -> 
   val_inject_opt j' ret1 ret2 -> 
   R j' s1' m1' s2' m2')   

 (extension_diagram: forall u s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd j,
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   runnable (csemS u) c1=false -> 
   runnable (csemT u) c2=false -> 
   at_external (csemS u) c1 = Some (ef, sig, args1) -> 
   at_external (csemT u) c2 = Some (ef, sig, args2) -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   corestep esemS ge_S s1 m1 s1' m1' -> 
   effects_guarantee esemS s1' m1' -> 
   exists s2', exists m2', exists cd', exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     effects_guarantee esemT s2' m2' /\
     match_states cd' j' s1' m1' s2' m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ords max_cores cd' cd))

 (at_external_match: forall u s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd j,
   ACTIVE E_S s1=ACTIVE E_T s2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   runnable (csemS u) c1=runnable (csemT u) c2 -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   at_external (csemS u) c1 = Some (ef, sig, args1) -> 
   match_state u cd j c1 m1 c2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args (ef_sig ef)) -> 
   at_external (csemT u) c2 = Some (ef, sig, args2) -> 
   at_external esemT s2 = Some (ef, sig, args2))

 (make_initial_core_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
   In (v1, v2, sig) entry_points -> 
   make_initial_core esemS ge_S v1 vals1 = Some s1 -> 
   Mem.inject j m1 m2 -> 
   mem_wd m1 -> 
   mem_wd m2 -> 
   Forall2 (val_inject j) vals1 vals2 -> 
   Forall2 Val.has_type vals2 (sig_args sig) -> 
   exists cd, exists s2, 
     make_initial_core esemT ge_T v2 vals2 = Some s2 /\
     match_states cd j s1 m1 s2 m2)
 
 (safely_halted_step: forall cd j c1 m1 c2 m2 v1 rty,
   match_states cd j c1 m1 c2 m2 -> 
   safely_halted esemS c1 = Some v1 -> 
   Val.has_type v1 rty -> 
   exists v2, val_inject j v1 v2 /\
     safely_halted esemT c2 = Some v2 /\ 
     Val.has_type v2 rty /\ 
     Mem.inject j m1 m2)

 (safely_halted_diagram: forall u cd j m1 m1' m2 rv1 s1 s2 s1' c1 c2,
   match_states cd j s1 m1 s2 m2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) u s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) u s2 = Some c2 -> 
   safely_halted (csemS u) c1 = Some rv1 -> 
   corestep esemS ge_S s1 m1 s1' m1' ->  
   effects_guarantee esemS s1' m1' -> 
   exists rv2, 
     safely_halted (csemT u) c2 = Some rv2 /\
     val_inject j rv1 rv2 /\ 
     exists s2', exists m2', exists cd', exists j', 
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       corestep esemT ge_T s2 m2 s2' m2' /\
       match_states cd' j' s1' m1' s2' m2' /\
       effects_guarantee esemT s2' m2'),
 Sig.

End CompilabilityInvariant. End CompilabilityInvariant.

Definition genvs_domain_eq {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall b, fst (genv2blocks ge1) b <-> fst (genv2blocks ge2) b) /\
  (forall b, snd (genv2blocks ge1) b <-> snd (genv2blocks ge2) b).

Module CompilableExtension. Section CompilableExtension. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) 
 (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat)
  (num_modules: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall (u:nat), Genv.t (fS u) (vS u))
  (genv_mapT: forall (u:nat), Genv.t (fT u) (vT u)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall (u: nat), 
   core_data u -> meminj -> cS u -> mem -> cT u -> mem -> Prop.
 Implicit Arguments match_state [].

 Import Forward_simulation_inj_exposed.

 Record Sig: Type := Make {
   core_datas: Type;
   core_ords: core_datas -> core_datas -> Prop;
   match_states: core_datas -> meminj -> xS -> mem -> xT -> mem -> Prop;
   _ : Forward_simulation_inject D_S D_T esemS esemT ge_S ge_T 
          entry_points core_datas match_states core_ords
 }.

End CompilableExtension. End CompilableExtension.

Module EXTENSION_COMPILABILITY. Section EXTENSION_COMPILABILITY.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: EffectfulSemantics (Genv.t F_S V_S) xS D_S) (** extended source semantics *)
  (esemT: EffectfulSemantics (Genv.t F_T V_T) xT D_T) (** extended target semantics *)
  (csemS: forall i:nat, 
    EffectfulSemantics (Genv.t (fS i) (vS i)) (cS i) (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, 
    EffectfulSemantics (Genv.t (fT i) (vT i)) (cT i) (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (max_cores: nat)
  (num_modules: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall (u:nat), Genv.t (fS u) (vS u))
  (genv_mapT: forall (u:nat), Genv.t (fT u) (vT u)).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) D_S xS esemS esig 
   _ _ cS csemS csig).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) D_T xT esemT esig 
   _ _ cT csemT csig).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall (u: nat), 
   core_data u -> meminj -> cS u -> mem -> cT u -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].

 Import Forward_simulation_inj_exposed.
 Import Extension.

 Definition core_datas := forall i:nat, core_data i.

 Variable (R: meminj -> xS -> mem -> xT -> mem -> Prop).

 Record Sig: Type := Make {
   _ : (forall (i u: nat), RelyGuaranteeSimulation.Sig (csemS u) (csemT u) 
         (genv_mapS u) (match_state u)) -> 
       genvs_domain_eq ge_S ge_T -> 
       (forall i u: nat, genvs_domain_eq ge_S (genv_mapS u)) -> 
       (forall i u: nat, genvs_domain_eq ge_T (genv_mapT u)) -> 
       core_compatible ge_S genv_mapS E_S -> 
       core_compatible ge_T genv_mapT E_T -> 
       owned_conserving esemS csemS E_S ->
       owned_conserving esemT csemT E_T ->
       (forall x, active E_S x < max_cores)%nat ->  
       (forall x, active E_T x < max_cores)%nat ->  
       new_effects_aligned esemT csemT ge_T genv_mapT E_T -> 
       (forall i u:nat, Forward_simulation_inject (dS u) (dT u) (csemS u) (csemT u) 
         (genv_mapS u) (genv_mapT u) entry_points 
         (core_data u) (@match_state u) (@core_ord u)) -> 
       CompilabilityInvariant.Sig fS fT vS vT 
         esemS esemT csemS csemT max_cores num_modules ge_S ge_T genv_mapS genv_mapT E_S E_T 
         entry_points core_data match_state core_ord R -> 
       CompilableExtension.Sig esemS esemT ge_S ge_T entry_points
 }.

End EXTENSION_COMPILABILITY. End EXTENSION_COMPILABILITY. 