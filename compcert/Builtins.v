From Hammer Require Import Hammer.


















Require Import String.
From compcert Require Import Coqlib.
From compcert Require Import AST.
From compcert Require Import Integers.
From compcert Require Import Floats.
From compcert Require Import Values.
From compcert Require Export Builtins0.
From compcert Require Export Builtins1.

Inductive builtin_function : Type :=
| BI_standard (b: standard_builtin)
| BI_platform (b: platform_builtin).

Definition builtin_function_sig (b: builtin_function) : signature :=
match b with
| BI_standard b => standard_builtin_sig b
| BI_platform b => platform_builtin_sig b
end.

Definition builtin_function_sem (b: builtin_function) : builtin_sem (proj_sig_res (builtin_function_sig b)) :=
match b with
| BI_standard b => standard_builtin_sem b
| BI_platform b => platform_builtin_sem b
end.

Definition lookup_builtin_function (name: string) (sg: signature) : option builtin_function :=
match lookup_builtin standard_builtin_sig name sg standard_builtin_table with
| Some b => Some (BI_standard b)
| None =>
match lookup_builtin platform_builtin_sig name sg platform_builtin_table with
| Some b => Some (BI_platform b)
| None => None
end end.

Lemma lookup_builtin_function_sig:
forall name sg b, lookup_builtin_function name sg = Some b -> builtin_function_sig b = sg.
Proof. hammer_hook "Builtins" "Builtins.lookup_builtin_function_sig".
unfold lookup_builtin_function; intros.
destruct (lookup_builtin standard_builtin_sig name sg standard_builtin_table) as [bs|] eqn:E.
inv H. simpl. eapply lookup_builtin_sig; eauto.
destruct (lookup_builtin platform_builtin_sig name sg platform_builtin_table) as [bp|] eqn:E'.
inv H. simpl. eapply lookup_builtin_sig; eauto.
discriminate.
Qed.


