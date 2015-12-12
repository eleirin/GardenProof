Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat.
Require Import Ssreflect.ssrfun.

Ltac pop i := move : i.
Ltac clear i := move : i => _.

Ltac dependent_tac tac H := 
        let rec dt_rec H := match goal with
                |dis: appcontext [H] |- _ => dt_rec dis; dt_rec H
                |_ => tac H
        end in dt_rec H.

Ltac dependent_pop := dependent_tac pop.
Ltac dependent_clear := dependent_tac clear.

Ltac dependent_goal_tac tac :=
        repeat (
                match goal with
                        |[|- appcontext [_ ?P]] => idtac "trying" P; tac P 
                end).

Ltac tac_case_dependent_same_independent tac_dep tac_same tac_indep H1 H2 :=
        lazymatch H2 with
                |H1 => idtac H1 " IIIIIIS " H2; tac_same H1
                |_ =>
        let type_H1 := type of H1 in
        lazymatch type_H1 with 
                |appcontext[H2] => idtac H2 " is dependent of " H1; tac_dep H2
                |_ => idtac H2 "is NOT dependent of " H1; tac_indep H2
         end
         end.
Ltac tac_case_dependent tac_dep := tac_case_dependent_same_independent tac_dep tac_dep.
Ltac tac_if_independent:= tac_case_dependent fail.
Ltac tac_if_dependent tac := tac_case_dependent tac fail.

Ltac dependent_goal_tac_except tac H := 
       dependent_goal_tac ltac:(tac_if_independent tac H).

Ltac dependent_goal_pop := dependent_goal_tac_except dependent_pop.

Ltac general_pop H := 
        dependent_goal_pop H; dependent_pop H.

Ltac general_elim H :=
        general_pop H; elim.

Ltac intros_all := repeat match goal with
                        | [|- forall reserved, _] => move => reserved; 
                                        lazymatch goal with
                                        |[|- appcontext[reserved]] => idtac
                                        |_ => fail
                                        end
                        | |- _ -> _ => let i := fresh in move => i
                        end.

Ltac show_goal := match goal with
| [ |- ?G] => idtac "Goal : " G
end.

Ltac show_hypothesis H := let tH := type of H in idtac H " : " tH.

Ltac show_lemma := try match reverse goal with
| [H : _ |- _] => show_hypothesis H; fail
end; show_goal; idtac "EOT_COQ".

Ltac click n := apply: n. 

