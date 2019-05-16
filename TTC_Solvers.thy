theory TTC_Solvers
  imports runningExample
          "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

(* 
We have implemented three solvers as methods: 
1.- "solver" that just try to solve TTC sequents 
2.- "solver_print_Big_Step" that tries to solve and prints the big-step proof.
3.- "solver_print_Small_Step" that tries to solve and prints the small-step proof.
The three solvers depend on the atoms and the names defined in "runningExample.thy". 
More research in Isabelle/HOL and Eisbach methods proof method is currently done for
using set of formulas and set of names as arguments in methods and method_setups, 
but, unfortunately, could be that low-level ML code would be required.
*)

(* THE BASIC SOLVER: solver *)

method try_Ctd  =
(* 
This  method is for the set of atoms of our running example.
*)
(
(solves \<open>((rule_tac phi = "(V ''a'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "(V ''b'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "(V ''c'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "(V ''d'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "\<circle>(V ''a'')" in TTC_Ctd1); simp)\<close>)|
(solves \<open>((rule_tac phi = "\<circle>(V ''b'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "\<circle>(V ''c'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule_tac phi = "\<circle>(V ''d'')" in TTC_Ctd1); simp)\<close>) |
(solves \<open>((rule TTC_Ctd2; simp); simp)\<close>)  
)    

method try_defer =
(
(rule TTC_Mark_Next; simp)+, 
(rule TTC_Unmark_Next; simp)?,  
(rule TTC_Mark_Next; simp)?, 
defer_tac
)

method one_step_solver = 
( 
(( (rule TTC_U_Sel; simp)  | 
  (rule TTC_U_Plus; simp)  | 
  (rule TTC_Evt_Plus; simp) 
)+)?
, ( (try_Ctd) | 
    (try_defer) |
    (rule TTC_Or; simp) | 
    (rule TTC_And; simp) | 
    (rule TTC_Imp; simp) |
    (rule TTC_Alw; simp) | 
    (rule TTC_U; simp)  | 
    (rule TTC_Evt; simp) 
)+
, (tactic {* distinct_subgoals_tac *}) 
)

method solver = 
(* This solver is for the set of names defined in our running example *)
( 
(rule TTC_Interchange, simp add: S_def TR_def T1_def T2_def T3_def T4_def Init_def),
(
one_step_solver;                                                                
((fold T1_def T2_def T3_def T4_def),                                              
(all \<open>rule TTC_Next_State; simp\<close>),                                              
(simp add: T1_def T2_def T3_def T4_def))
)+
)

(* THE SOLVER FOR THE BIG-STEP PROOF: solver_print_Big_Step *)

(* 
Problems with adding extra parameters in the method_setups of Isabelle/HOL 
force us to define a method for each string that we have to print. 
*)

(* Method_setups for printing strings (of big-step proofs) in a file Proof.txt *)

method_setup print_Interchange =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Interchange, simp add: S_def TR_def T1_def T2_def T3_def T4_def Init_def)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_one_step_solver =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply one_step_solver" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_fold =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (fold T1_def T2_def T3_def T4_def)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_all_Next_State =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (all \<open>rule TTC_Next_State\<close>; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_unfold  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (simp add: T1_def T2_def T3_def T4_def)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_done  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "done");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

(* The big-step solver *)

method solver_print_Big_Step = 
( 
(
print_Interchange,
(rule TTC_Interchange, simp add: S_def TR_def T1_def T2_def T3_def T4_def Init_def)
),
(
((print_one_step_solver, 
one_step_solver, print_all_Next_State, print_fold);                                                                                                           
(all \<open>rule TTC_Next_State; simp\<close>)), print_unfold
)+,
print_done
)

(* THE SOLVER FOR THE SMALL-STEP PROOF: solver_print_Big_Step *)

(* 
Problems with adding extra parameters in the method_setups of Isabelle/HOL 
force us to define a method for each string that we have to print. 
*)

(* Method_setups for printing additional strings of small-step proofs *)

method_setup print_Ctda =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034(V ''a'')\034 in TTC_Ctd1; simp)");
       val _ = TextIO.output (file, "\013") ;
       val _ = TextIO.closeOut(file);
    in 
      (Seq.make_results (Seq.single (ctxt', thm)))
    end))\<close>

method_setup print_Ctdb =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034(V ''b'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_Ctdc =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034(V ''c'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_Ctdd =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034(V ''d'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_CtdXa =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034\<circle>(V ''a'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_CtdXb =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034\<circle>(V ''b'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_CtdXc =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034\<circle>(V ''c'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_CtdXd =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule_tac phi = \034\<circle>(V ''d'')\034 in TTC_Ctd1; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>      

method_setup print_Ctd2 =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Ctd2; simp; simp)" );
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close> 

method_setup print_defer  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "defer");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_U_Sel  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_U_Sel; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_U_Plus  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_U_Plus; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_Evt_Plus  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Evt_Plus; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_Or  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Or; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_And  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_And; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_Imp  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Imp; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_Alw  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Alw; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_U  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_U; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_TTC_Evt  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (rule TTC_Evt; simp)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_distinct_subgoals  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "apply (tactic {* distinct_subgoals_tac *})");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

method_setup print_init_step  =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    (let 
       val file = TextIO.openAppend("Proof.txt");
       val _ = TextIO.output (file, "(* step *)");
       val _ = TextIO.output (file, ("\013") );
       val _ = TextIO.closeOut(file);
    in
     (Seq.make_results (Seq.single (ctxt', thm))) 
    end))\<close>

(* The small-step solver *)

method try_Ctd_print =
(
((solves \<open>((rule_tac phi = "(V ''a'')" in TTC_Ctd1); simp)\<close>), print_Ctda) |
((solves \<open>((rule_tac phi = "(V ''b'')" in TTC_Ctd1); simp)\<close>), print_Ctdb) |
((solves \<open>((rule_tac phi = "(V ''c'')" in TTC_Ctd1); simp)\<close>), print_Ctdc) |
((solves \<open>((rule_tac phi = "(V ''d'')" in TTC_Ctd1); simp)\<close>), print_Ctdd) |
((solves \<open>((rule_tac phi = "\<circle>(V ''a'')" in TTC_Ctd1); simp)\<close>), print_CtdXa)|
((solves \<open>((rule_tac phi = "\<circle>(V ''b'')" in TTC_Ctd1); simp)\<close>), print_CtdXb) |
((solves \<open>((rule_tac phi = "\<circle>(V ''c'')" in TTC_Ctd1); simp)\<close>), print_CtdXc) |
((solves \<open>((rule_tac phi = "\<circle>(V ''d'')" in TTC_Ctd1); simp)\<close>), print_CtdXd) |
((solves \<open>((rule TTC_Ctd2; simp); simp)\<close>); fail, print_Ctd2) 
)  

method try_defer_print =
(
(rule TTC_Mark_Next; simp)+, 
(rule TTC_Unmark_Next; simp)?,  
(rule TTC_Mark_Next; simp)?, 
print_defer, defer_tac
)

method one_step_solver_print =
( 
print_init_step,
(( ((rule TTC_U_Sel; simp),   print_TTC_U_Sel)  | 
   ((rule TTC_U_Plus; simp),  print_TTC_U_Plus)  | 
   ((rule TTC_Evt_Plus; simp), print_TTC_Evt_Plus)
)+)?
, ( (try_Ctd_print) | 
    (try_defer, print_defer) |
    ((rule TTC_Or; simp),  print_TTC_Or) | 
    ((rule TTC_And; simp),  print_TTC_And) | 
    ((rule TTC_Imp; simp),  print_TTC_Imp) |
    ((rule TTC_Alw; simp),  print_TTC_Alw) | 
    ((rule TTC_U; simp),  print_TTC_U)  | 
    ((rule TTC_Evt; simp),  print_TTC_Evt)
)+
, (tactic {* distinct_subgoals_tac *}), print_distinct_subgoals 
)

method solver_print_Small_Step = 
( 
(
print_Interchange,
(rule TTC_Interchange, simp add: S_def TR_def T1_def T2_def T3_def T4_def Init_def)
),
(
((
one_step_solver_print, print_all_Next_State, print_fold);                                                                                                           
(all \<open>rule TTC_Next_State; simp\<close>)), print_unfold
)+,
print_done
)



end