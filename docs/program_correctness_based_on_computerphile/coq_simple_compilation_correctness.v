(* begin hide *)
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z.
(* end hide *)

(** * Correctness of a Simple Compiler *)
(* By Daniel Britten,  The University of Waikato *)

(**
Based upon the example discussed by Professor Graham Hutton on Computerphile on November 27: %\url{https://youtu.be/T_IINWzQhow}% #<a href='https://youtu.be/T_IINWzQhow'>https://youtu.be/T_IINWzQhow</a>#  

Proof based upon Associate Professor Adam Chlipala's proof: %\url{http://adam.chlipala.net/cpdt/html/StackMachine.html}% #<a href='http://adam.chlipala.net/cpdt/html/StackMachine.html'>http://adam.chlipala.net/cpdt/html/StackMachine.html</a># *)

(** ** Implementation *)

Inductive Expr := 
  | Val (n : Z)
  | Add (e1 e2 : Expr).

Inductive Op :=
  | PUSH (n : Z)
  | ADD.

Fixpoint eval (e : Expr) :=
  match e with
  | Val n => n
  | Add x y => eval x + eval y
  end.

Fixpoint comp (e : Expr) :=
  match e with
  | Val n => [PUSH n]
  | Add x y => comp x ++ comp y ++ [ADD]
  end.

Fixpoint exec (ops : list Op) (stack : list Z) : list Z :=
  match ops, stack with
  | PUSH n :: c, s => exec c (n :: s)
  | ADD :: c, (m::n::s) => exec c (n + m :: s)
  | _, s => s
  end.

(** ** Examples *)

Example eg1 : exec (comp (Add (Val 42) (Val 42))) [] = [84]. reflexivity. Qed.
Example eg2 : eval (Add (Val 42) (Val 42)) = 84. reflexivity. Qed.
Example eg3 : exec ([PUSH 1; PUSH 2; PUSH 3]) [] = [3;2;1]. reflexivity. Qed.
Example eg4 : exec ([ADD; PUSH 1; PUSH 2; PUSH 3]) [] = []. reflexivity. Qed.

(** ** Correctness Proof *)

(** First we need to strengthening the induction hypothesis as described in: Adam Chlipala's similar proof at %\url{http://adam.chlipala.net/cpdt/html/StackMachine.html}% #<a href='http://adam.chlipala.net/cpdt/html/StackMachine.html'>http://adam.chlipala.net/cpdt/html/StackMachine.html</a># *)

Lemma correct_helper : 
  forall e ops s, exec (comp e ++ ops) s = exec ops (eval e :: s).
  Proof.
    induction e.
     - simpl. reflexivity. 
     - intros. simpl. 
       rewrite app_assoc_reverse.
       rewrite IHe1.
       rewrite app_assoc_reverse. 
       rewrite IHe2.
       simpl. reflexivity.
  Qed.

(** Now the proof follows from the lemma. *)

Theorem correct : forall e, exec (comp e) [] = [eval e].
  Proof.
    intros.
    pose (correct_helper e [] []) as H.
    rewrite app_nil_r in H.
    assumption.
  Qed.

(** QED! - We now have the highest degree of certainty (proof) that our implementation meets the specification: [forall e, exec (comp e) [] = [eval e] ] *)

(** The Coq source file of this proof is available at: %\url{https://coda-coda.github.io/blog/program_correctness_based_on_computerphile/coq_simple_compilation_correctness.v}% #<a href='https://coda-coda.github.io/blog/program_correctness_based_on_computerphile/coq_simple_compilation_correctness.v'>https://coda-coda.github.io/blog/program_correctness_based_on_computerphile/coq_simple_compilation_correctness.v</a># *)