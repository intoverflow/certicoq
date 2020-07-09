Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
(* Require Import CertiCoq.Benchmarks.lib.sha256. *)

From CertiCoq.Plugin Require Import CertiCoq.

Open Scope string.

Import ListNotations.
Import VeriStar.

CertiCoq -help.

Fixpoint long_id n (x y z : nat) {struct n} :=
  match n with
  | 0 => 0
  | S n => S (long_id n x y z)
  end.

(* CertiCoq Show IR -anf -ext "_anf" long_id. *)
CertiCoq Show IR -ext "_cps" long_id.

Fixpoint leb (n m : nat) :=
  match n, m with
  | 0, _ => true
  | S _, 0 => false
  | S n, S m => leb n m
  end.

Fixpoint insert x xs :=
  match xs with
  | [] => [x]
  | x' :: xs => if leb x x' then x :: x' :: xs else x' :: insert x xs
  end.

Fixpoint insert' x xs :=
  match xs with
  | [] => [x]
  | x' :: xs => x' :: insert x xs
  end.

Fixpoint isort (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs => (*insert' x *)(isort xs)
  end.
Compute isort [1; 4; 3; 6; 2].

Fixpoint slow_zero (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n => slow_zero n
  end.

Fixpoint slow_nil (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs => slow_nil xs
  end.

(* CertiCoq Show IR -anf slow_nil. *)
CertiCoq Show IR -ext "_cps" isort.
CertiCoq Show IR -ext "_cps" slow_nil.

Definition easy_demo1 := 1 + 1.

(* CertiCoq Compile -ext "_cps" easy_demo1. *)
CertiCoq Show IR -ext "_cps" easy_demo1.

Definition demo1 := List.app (List.repeat true 5) (List.repeat false 3).
Definition demo2 := List.map negb [true; false; true].
Definition demo3 := andb. 
  
(* CertiCoq Compile -ext "_cps" demo1. *)
CertiCoq Show IR -ext "_cps" demo1.
(* CertiCoq Compile -anf demo1. *)

CertiCoq Show IR -ext "_cps" demo2.
(* CertiCoq Compile -anf demo2. *)

(* Also works for CPS, when choosing another number of arguments, e.g. -args 1 *)
CertiCoq Show IR -ext "_cps" demo3.
(* CertiCoq Compile -anf demo3. *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

CertiCoq Show IR -ext "_cps" list_sum.
(* CertiCoq Compile -anf list_sum. *)

Definition vs_easy :=
  match vs.main with
  | Valid => true
  | _ => false
  end.

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

(* CertiCoq Compile -ext "_cps" -time vs_easy. *)
(* CertiCoq Compile -anf  vs_easy. *)
(* CertiCoq Show IR -anf vs_easy. *)
(* CertiCoq Show IR -ext "_cps" -time vs_easy. *)
CertiCoq Show IR -ext "_cps" -time vs_hard.

(*
(* Zoe: Compiling with the CPS pipeline takes much longer for vs_easy.
   The overhead seems to come from the C translation: (maybe has to do with dbg/error messages?)

Timing for CPS:
Debug: Time elapsed in L1g:  8.835582
Debug: Time elapsed in L2k:  0.000454
Debug: Time elapsed in L2k_eta:  0.000620
Debug: Time elapsed in L4:  0.014821
Debug: Time elapsed in L4_2:  0.003420
Debug: Time elapsed in L4_5:  0.000780
Debug: Time elapsed in L5:  0.005000
Debug: Time elapsed in L6 CPS:  0.105993
Debug: Time elapsed in L6 Pipeline:  8.532707
Debug: Time elapsed in L7:  87.985509

Timing for ANF:
Debug: Time elapsed in L1g:  8.543669
Debug: Time elapsed in L2k:  0.000457
Debug: Time elapsed in L2k_eta:  0.000640
Debug: Time elapsed in L4:  0.013329
Debug: Time elapsed in L6 ANF:  0.020384
Debug: Time elapsed in L6 Pipeline:  0.148308
Debug: Time elapsed in L7:  2.394216 *)

(* CertiCoq Compile -ext "_cps" vs_hard. *)
CertiCoq Show IR -anf vs_hard.

Definition binom := Binom.main.

(* CertiCoq Compile -ext "_cps" binom. (* returns nat *) *)
CertiCoq Show IR -anf binom.  (* returns nat *)

Definition color := Color.main.
Definition color_run := Color.run.

(* CertiCoq Compile -ext "_cps" color. *)
CertiCoq Show IR -anf -time color_run.
*)
