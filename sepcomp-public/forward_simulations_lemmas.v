Load loadpath.

(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import msl.Axioms.
Require Import sepcomp.mem_lemmas. (*TODO: Is this import needed?*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.

(*Proofs that the individual cases of sim (sim_eq, sim_ext and sim_inj are closed under
   star and plus. Then (presumably) lift this to compilercorrectness.*)

(*SEVERAL HOLES IN THIS FILE!!!*)

Section Sim_EQ_SIMU_DIAGRAMS.

  Context {M G1 C1 D1 M2 G2 C2 D2:Type}
          {Sem1 : CoreSemantics G1 C1 M D1}
          {Sem2 : CoreSemantics G2 C2 M D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Let core_data := C1.

  Variable match_cores: core_data -> C1 -> C2 -> Prop.

  Hypothesis match_initial_cores: 
        forall v1 v2 sig, In (v1,v2,sig) entry_points ->
        forall vals,  Forall2 (Val.has_type) vals (sig_args sig) ->
        exists c1 : C1, exists c2 : C2,
                make_initial_core Sem1 ge1 v1 vals = Some c1 /\
                make_initial_core Sem2 ge2 v2 vals = Some c2 /\ match_cores c1 c1 c2.
(*Smallstep/old version of this file had
  Hypothesis match_initial_cores: 
        forall v1 v2 sig, In (v1,v2,sig) entry_points ->
        forall vals,  Forall2 (Val.has_type) vals (sig_args sig) ->
        forall c1, make_initial_core Sem1 ge1 v1 vals = Some c1 ->
                   exists c2, exists d, make_initial_core Sem2 ge2 v2 vals = Some c2 /\
                                                   match_cores d c1 c2.
But the core_initial axiom in the record Sim_eq.Forward_simulation_equals currently has an /\
  in place of the implication -- maybe that should be changed?
*)

  Hypothesis eq_safely_halted:
      forall (cd : core_data) (c1 : C1) (c2 : C2) v ,
      match_cores cd c1 c2 ->
      safely_halted Sem1 c1 = Some v -> safely_halted Sem2 c2 = Some v.

  Hypothesis eq_at_external: 
   forall (d : C1) (st1 : core_data) (st2 : C2) (e : external_function) 
          (args : list val) (ef_sig : signature),
    (d = st1 /\ match_cores d st1 st2) ->
    at_external Sem1 st1 = Some (e, ef_sig, args) ->
    (at_external Sem2 st2 = Some (e, ef_sig, args) /\
     Forall2 Val.has_type args (sig_args ef_sig)).

Hypothesis eq_after_external:
   forall (d : C1) (st1 : core_data) (st2 : C2) (ret : val) 
          (e : external_function) (args : list val) (ef_sig : signature),
    (d = st1 /\ match_cores d st1 st2) ->
    at_external Sem1 st1 = Some (e, ef_sig, args) ->
    at_external Sem2 st2 = Some (e, ef_sig, args) ->
    Forall2 Val.has_type args (sig_args ef_sig) ->
    Val.has_type ret (proj_sig_res ef_sig) ->
    exists st1', exists st2', exists d',
      after_external Sem1 (Some ret) st1 = Some st1' /\
      after_external Sem2 (Some ret) st2 = Some st2' /\
      d' = st1' /\ match_cores d' st1' st2'.

Section EQ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

  Hypothesis eq_simulation:
     forall c1 m c1' m',  corestep Sem1 ge1 c1 m c1' m' ->
     forall c2, match_cores c1 c1 c2 ->
      exists c2', match_cores c1' c1' c2' /\
        (corestep_plus Sem2 ge2  c2 m c2' m' \/ 
          (corestep_star Sem2 ge2 c2 m c2' m' /\ order c1' c1)).

Lemma  eq_simulation_star_wf: 
  Forward_simulation_eq.Forward_simulation_equals _ _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Forward_simulation_eq.Build_Forward_simulation_equals with
    (core_ord := order)
        (match_core := fun d c1 c2 => d = c1 /\ match_cores d c1 c2).
  apply order_wf.
  intros. destruct H0; subst.  destruct (eq_simulation _ _ _ _ H _ H1) as [c2' [MC' Step]].
  exists c2'.  exists st1'.  split; eauto. clear eq_simulation eq_after_external eq_at_external .
  intros. destruct (match_initial_cores _ _ _ H _ H0) as [c1' [c2' [MIC1 [MIC2 MC]]]].
  exists c1'. exists c1'. exists c2'. split; eauto.
  intros.  clear eq_simulation eq_after_external eq_at_external . destruct H; subst.
  eapply eq_safely_halted; eauto.
  apply eq_at_external.
  apply eq_after_external.
Qed.

End EQ_SIMULATION_STAR_WF.

Section EQ_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis eq_star_simulation:
    forall c1 m c1' m', corestep Sem1 ge1 c1 m c1' m'  -> 
    forall c2, match_cores c1 c1 c2 ->
      (exists c2', corestep_plus Sem2 ge2 c2 m c2' m' /\ match_cores c1' c1' c2')
      \/ (measure c1' < measure c1 /\ m=m' /\ match_cores c1' c1' c2)%nat.

Lemma  eq_simulation_star: 
  Forward_simulation_eq.Forward_simulation_equals _ _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply eq_simulation_star_wf. apply  (well_founded_ltof _ measure).
  intros. destruct (eq_star_simulation _ _ _ _ H _ H0).
  destruct H1 as [c2' [CSP MC']]. exists c2'. split; trivial. left; trivial.
  destruct H1 as [X1 [X2 X3]]; subst. exists c2. split; trivial. right. split; trivial.
  eapply corestep_star_zero. 
Qed.

End EQ_SIMULATION_STAR.

Section EQ_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis eq_plus_simulation:
    forall c1 m c1' m', corestep Sem1 ge1 c1 m c1' m'  -> 
    forall c2, match_cores c1 c1 c2 ->
      exists c2', corestep_plus Sem2 ge2 c2 m c2' m' /\ match_cores c1' c1' c2'.

Lemma eq_simulation_plus: 
  Forward_simulation_eq.Forward_simulation_equals _ _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply eq_simulation_star with (measure:=measure).
  intros. destruct (eq_plus_simulation _ _ _ _ H _ H0).
  left. eexists; eauto.
Qed.

End EQ_SIMULATION_PLUS.

End Sim_EQ_SIMU_DIAGRAMS.

Section Sim_EXT_SIMU_DIAGRAMS.
  Context {G1 C1 D1 G2 C2 D2:Type}
          {Sem1 : RelyGuaranteeSemantics G1 C1 D1}
          {Sem2 : RelyGuaranteeSemantics G2 C2 D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Let core_data := C1.

  Variable match_states: core_data -> C1 -> mem -> C2 -> mem -> Prop.

  Hypothesis match_initial_cores: forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_states c1 c1 m1 c2 m2.

  Hypothesis ext_safely_halted:
      forall cd st1 m1 st2 m2 v1,
        match_states cd st1 m1 st2 m2 ->
        safely_halted Sem1 st1 = Some v1 ->
        exists v2, Val.lessdef v1 v2 /\
            safely_halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2.

  Hypothesis ext_at_external: 
        forall d st1 m1 st2 m2 e vals1 sig,
          (d = st1 /\ match_states d st1 m1 st2 m2) ->
         at_external Sem1 st1 = Some (e, sig, vals1) ->
         exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args sig) /\
          at_external Sem2 st2 = Some (e,sig,vals2).

  Hypothesis ext_after_external:
      forall d st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' sig,
        (d=st1 /\ match_states d st1 m1 st2 m2) ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        at_external Sem2 st2 = Some (e,sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' -> 
       (*ie spill-locations didn't change*)        
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res sig) ->

        exists st1', exists st2', exists d',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          d' = st1' /\ match_states d' st1' m1' st2' m2'. 

Section EXT_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis ext_simulation:
  forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
    forall c2 m2, match_states c1 c1 m1 c2 m2 ->
      exists c2', exists m2', 
        match_states c1' c1' m1' c2' m2' /\
        mem_unchanged_on (fun b ofs => 
          loc_out_of_bounds m1 b ofs /\ ~private_block Sem1 c1 b) m1 m1' /\
        (corestep_plus Sem2 ge2  c2 m2 c2' m2' \/ 
          (corestep_star Sem2 ge2 c2 m2 c2' m2' /\ order c1' c1)).

Lemma ext_simulation_star_wf: 
  Forward_simulation_ext.Forward_simulation_extends _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Forward_simulation_ext.Build_Forward_simulation_extends with
        (core_ord := order)
        (match_state := fun d c1 m1 c2 m2 => d = c1 /\ match_states d c1 m1 c2 m2).
   apply order_wf.
   intros. destruct H0; subst.
              destruct (ext_simulation _ _ _ _ H _ _ H1) as [c2' [m2' [MC' Step]]].
              exists c2'. exists m2'. exists st1'.  split; eauto.
   intros. destruct (match_initial_cores _ _ _ H _ _ _ _ H0 H1 H2) 
    as [c1' [c2' [MIC1 [MIC2 MC]]]].
                 exists c1'. exists c1'. exists c2'. split; eauto.
   intros. destruct H; subst. eapply ext_safely_halted; eauto.
   intros.  destruct H. eapply ext_at_external; eauto.
   intros. destruct H. eapply ext_after_external; eauto.
Qed.

End EXT_SIMULATION_STAR_WF.

Section EXT_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis ext_star_simulation:
    forall (c1 : C1) (m1 : mem) (c1' : C1) (m1' : mem),
      corestep Sem1 ge1 c1 m1 c1' m1' ->
      forall (c2 : C2) (m2 : mem),
        match_states c1 c1 m1 c2 m2 ->
        exists c2' : C2,
          exists m2' : mem,
            match_states c1' c1' m1' c2' m2' /\
            mem_unchanged_on
            (fun (b : block) (ofs : Z) =>
              loc_out_of_bounds m1 b ofs /\ ~ private_block Sem1 c1 b) m1 m1' /\
            (corestep_plus Sem2 ge2 c2 m2 c2' m2' \/ 
             corestep_star Sem2 ge2 c2 m2 c2' m2' /\ ltof C1 measure c1' c1).

Lemma ext_simulation_star: 
  Forward_simulation_ext.Forward_simulation_extends _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply ext_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
  intros.
  destruct (ext_star_simulation _ _ _ _ H _ _ H0) as [c2' [m2' [CSP [? MC']]]].
  exists c2'; exists m2'; split; auto.
Qed.

End EXT_SIMULATION_STAR.

Section EXT_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis ext_plus_simulation:
    forall c1 m1 c1' m1', corestep Sem1 ge1 c1 m1 c1' m1'  -> 
    forall c2 m2, match_states c1 c1 m1 c2 m2 ->
      exists c2', exists m2', 
        corestep_plus Sem2 ge2 c2 m2 c2' m2' /\ 
        match_states c1' c1' m1' c2' m2' /\
        mem_unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_out_of_bounds m1 b ofs /\ ~ private_block Sem1 c1 b) m1 m1'.

Lemma ext_simulation_plus: 
  Forward_simulation_ext.Forward_simulation_extends _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply ext_simulation_star with (measure:=measure).
  intros. destruct (ext_plus_simulation _ _ _ _ H _ _ H0) as [c2' [m2' [MC [UNC STEP]]]].
  eexists; eexists; split; eauto.
Qed.

End EXT_SIMULATION_PLUS.

End Sim_EXT_SIMU_DIAGRAMS.

Section Sim_INJ_SIMU_DIAGRAMS.
  Context {F1 V1 C1 D1 G2 C2 D2:Type}
          {Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 D1}
          {Sem2 : RelyGuaranteeSemantics G2 C2 D2}

          {ge1: Genv.t F1 V1} 
          {ge2:G2}
          {entry_points : list (val * val * signature)}. 

  Let core_data := C1.

  Variable match_states: core_data -> kpair -> meminj -> C1 -> mem -> C2 -> mem -> Prop.

  Hypothesis match_initial_cores: forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 kp j vals2 m2,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          Forall2 (val_inject j) vals1 vals2 ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists c2, 
            make_initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_states c1 kp j c1 m1 c2 m2.

  Hypothesis inj_safely_halted: forall cd k1 k2 j c1 m1 c2 m2 v1 rty,
      match_states cd (k1, k2) j c1 m1 c2 m2 ->
      safely_halted Sem1 c1 = Some v1 ->
      Val.has_type v1 rty -> 
      exists v2, val_inject j v1 v2 /\
          safely_halted Sem2 c2 = Some v2 /\
          Val.has_type v2 rty /\
          Mem.inject j m1 m2.

  Hypothesis inj_at_external: 
      forall cd k1 k2 j st1 m1 st2 m2 e vals1 sig,
        cd = st1 /\ match_states cd (k1, k2) j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ 
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,sig,vals2)).

  Hypothesis inj_after_external:
      forall cd k1 k2 k1' k2' j j' st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 sig,
        Mem.inject j m1 m2->
        (cd = st1 /\ match_states cd (k1, k2) j st1 m1 st2 m2) ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        meminj_preserves_globals ge1 j -> 

        (*rely*)
        knowledge_incr2 (k1, k2) (k1', k2') -> 
        knowledge_separated2 (k1, k2) (k1', k2') m1 m2 -> 
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject_opt j' ret1 ret2 ->

        mem_forward m1 m1'  -> 
        mem_unchanged_on (fun b ofs => private_block Sem1 st1 b) m1 m1' ->
        mem_forward m2 m2' -> 
        mem_unchanged_on (fun b ofs => private_block Sem2 st2 b) m2 m2' ->
        val_has_type_opt' ret1 (proj_sig_res (ef_sig e)) -> 
        val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) -> 
        
        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          cd' = st1' /\ match_states cd' (k1', k2') j' st1' m1' st2' m2'.

  Hypothesis knowledge_disjoint: 
    forall cd k1 k2 j c1 m1 c2 m2,
      match_states cd (k1, k2) j c1 m1 c2 m2 -> 
      (forall b, k1 b -> ~private_block Sem1 c1 b) /\
      (forall b, k2 b -> ~private_block Sem2 c2 b).

  Hypothesis knowledge_injects:
    forall cd k1 k2 j c1 m1 c2 m2,
      match_states cd (k1, k2) j c1 m1 c2 m2 -> 
      forall b, k1 b -> 
        exists b', exists ofs, j b = Some (b', ofs) /\ k2 b'.

Section INJ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.
          
  Hypothesis inj_simulation:
     forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
     forall k1 k2 j c2 m2, match_states c1 (k1, k2) j c1 m1 c2 m2 ->
      exists k1', exists k2', exists c2', exists m2', exists j', 
        knowledge_incr2 (k1, k2) (k1', k2') /\
        knowledge_separated2 (k1, k2) (k1', k2') m1 m2 /\
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\
        match_states c1' (k1', k2') j' c1' m1' c2' m2' /\
        mem_unchanged_on (fun b ofs => 
          ~k1 b /\ ~private_block Sem1 c1 b) m1 m1' /\
        mem_unchanged_on (fun b ofs => 
          ~k2 b /\ ~private_block Sem2 c2 b) m2 m2' /\
        (corestep_plus Sem2 ge2 c2 m2 c2' m2' \/ 
          (corestep_star Sem2 ge2 c2 m2 c2' m2' /\ order c1' c1)).

Lemma  inj_simulation_star_wf: 
  Forward_simulation_inj.Forward_simulation_inject _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Forward_simulation_inj.Build_Forward_simulation_inject with
    (core_ord := order)
    (match_state := fun d k1k2 j c1 m1 c2 m2 => d = c1 /\ match_states d k1k2 j c1 m1 c2 m2).
  apply order_wf.
  intros. destruct H; subst; eauto.
  intros; eapply knowledge_injects; eauto.
  solve[destruct H; eauto].
  intros. destruct H0.
  subst cd; exploit inj_simulation; eauto.
   intros [k1' [k2' [c2' [m2' [j' [INC [SEP [MC' [UNCH1 [UNCH2 Step]]]]]]]]]].
  exists k1'; exists k2'; exists c2'. 
  exists m2'; exists st1'; exists j'; split; auto.
  split; auto.
  intros. 
  exploit match_initial_cores; eauto.
  intros [c2' [MIC MC]].
  exists c1; exists c2'; split; auto.
  intros. split; eauto.
  intros. destruct H; subst. eapply inj_safely_halted; eauto.
  intros. destruct H; subst. eapply inj_at_external; eauto.
  intros. clear inj_simulation.
  solve[eapply inj_after_external 
   with (cd := cd) (k1 := k1) (k2 := k2) (j := j) (m1 := m1) (e := e); eauto].
Qed.

End INJ_SIMULATION_STAR_WF.

Section INJ_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis inj_star_simulation:
     forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
     forall k1 k2 j c2 m2, match_states c1 (k1, k2) j c1 m1 c2 m2 ->
      exists k1', exists k2', exists c2', exists m2', exists j', 
        knowledge_incr2 (k1, k2) (k1', k2') /\
        knowledge_separated2 (k1, k2) (k1', k2') m1 m2 /\
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\
        match_states c1' (k1', k2') j' c1' m1' c2' m2' /\
        mem_unchanged_on (fun b ofs => 
          ~k1 b /\ ~private_block Sem1 c1 b) m1 m1' /\
        mem_unchanged_on (fun b ofs => 
          ~k2 b /\ ~private_block Sem2 c2 b) m2 m2' /\
        (corestep_plus Sem2 ge2 c2 m2 c2' m2' 
          \/ ((measure c1' < measure c1)%nat /\ corestep_star Sem2 ge2 c2 m2 c2' m2')).

Lemma inj_simulation_star: 
  Forward_simulation_inj.Forward_simulation_inject _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply inj_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
  intros. 
  exploit inj_star_simulation; eauto.
  intros [k1' [k2' [c2' [m2' [j' [KINC [KSEP [INC [SEP [UNCH1 [UNCH2 [MC' STEP]]]]]]]]]]]]. 
  exists k1'; exists k2'; exists c2'; exists m2'; exists j'; split; auto.
  destruct KINC; destruct KSEP.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  destruct STEP as [X1|X1]; subst. left; auto. 
  right. destruct X1. split; auto.
Qed.

End INJ_SIMULATION_STAR.

Section INJ_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis inj_plus_simulation:
     forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
     forall k1 k2 j c2 m2, match_states c1 (k1, k2) j c1 m1 c2 m2 ->
      exists k1', exists k2', exists c2', exists m2', exists j', 
        knowledge_incr2 (k1, k2) (k1', k2') /\
        knowledge_separated2 (k1, k2) (k1', k2') m1 m2 /\
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\
        match_states c1' (k1', k2') j' c1' m1' c2' m2' /\
        mem_unchanged_on (fun b ofs => 
          ~k1 b /\ ~private_block Sem1 c1 b) m1 m1' /\
        mem_unchanged_on (fun b ofs => 
          ~k2 b /\ ~private_block Sem2 c2 b) m2 m2' /\
        corestep_plus Sem2 ge2 c2 m2 c2' m2'.
  
Lemma inj_simulation_plus: 
  Forward_simulation_inj.Forward_simulation_inject _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply inj_simulation_star with (measure:=measure); eauto.
  intros. exploit inj_plus_simulation; eauto.
  intros [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
  do 5 eexists. 
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
Qed.

End INJ_SIMULATION_PLUS.

End Sim_INJ_SIMU_DIAGRAMS.