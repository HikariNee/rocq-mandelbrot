From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.
From Stdlib Require Import Recdef.
From Stdlib Require Import FunInd.
From mathcomp Require Import path.
From Bignums Require Import BigZ.
From Bignums Require Import BigQ.

Open Scope bigQ_scope.
Declare Scope C_scope.

(* Yes, this isn't a vector, but its the most apt name I could come up with. *)
Section Aux.
  Record Vector T :=
    mkVec { val : list T; size : bigQ }.

  Definition C : Type := bigQ * bigQ.
  Definition Width : nat := 80.
  Definition Height : nat := 40.
  Definition Iterations : nat := 5.

  Definition notb (alpha : bool) : bool :=
    match alpha with
    | true => false
    | false => true
    end.

  Definition inject_nat (n : nat) : bigQ :=
    (BigZ.of_Z (Z.of_nat n)) # 1.

  Definition ltbQ (alpha : bigQ) (beta : bigQ) : bool :=
    match BigQ.compare alpha beta with
    | Lt => true
    | _ => false
    end.

  Definition lebQ (alpha : bigQ) (beta : bigQ) : bool :=
    match BigQ.compare alpha beta with
    | Lt | Eq => true
    | _ => false
    end.

  Open Scope string_scope.
  Definition toChar (q : bigQ) : string :=
    if (BigQ.eqb q 0) then "-" else
      if (BigQ.eqb q 1) then "#" else
        if (BigQ.eqb q 2) then "%" else
          " ".

  Definition scale (coord : C) : C :=
    (* 2 + 1 = 3, total X units for the mandelbrot, 2 for the Y axis *)
    let scaleX := 3 / inject_nat Width in
    let scaleY := 2 / inject_nat Height in
    let lowerX := -2 in
    let lowerY := -12 # 10 in
    ((fst coord * scaleX) + lowerX, (snd coord * scaleY) + lowerY).

  Definition points : list C :=
    sort (fun x y => lebQ (snd x) (snd y)) (map (fun x => scale x)
                                             (flat_map (fun x =>
                                                          map (fun y => (inject_nat x, inject_nat y)) (seq 0 Height))
                                                (seq 0 Width))).

  Close Scope string_scope.
End Aux.

Section Complex.
  Definition CPlus (c1 c2 : C) : C :=
    (fst c1 + fst c2, snd c1 + snd c2).

  Definition CInv (c0 : C) : C :=
    (- fst c0, - snd c0).

  Definition CMin (c1 c2 : C) : C :=
    CPlus c1 (CInv c2).

  Definition CMul (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

  Definition CEq (c1 c2 : C) : bool :=
    andb (BigQ.eqb (fst c1) (fst c2)) (BigQ.eqb (snd c1) (snd c2)).

  Definition CModSq (c1 : C) : bigQ :=
    let x := fst c1 in
    let y := snd c1 in
    (x * x + y * y).
End Complex.

Infix "+" := CPlus : C_scope.
Infix "-" := CMin  : C_scope.
Notation "- x" := (CInv x) : C_scope.
Infix "-?" := CMin (at level 20) : C_scope.
Infix "=?" := CEq : C_scope.
Infix "*" := CMul : C_scope.

Section ListOps.
  Definition nAppl {X : Type} (f : X -> X) (c : X) (n : nat) : Vector X :=
  let fix
        go (x : X) (n : nat) := let x' := f x in
                                match n with
                                | 0 => nil
                                | S n' => x' :: (go x' n')
                                end
  in
  mkVec X (go c n) (inject_nat n).
End ListOps.

Section Mandelbrot.
  Open Scope C_scope.
  Definition mandelbrotF (c : C) (z : C) : C :=
    (z * z) + c.


  Definition nApplMandelbrot (c : C) (z : C) (fuel : nat) : Vector C :=
    nAppl (mandelbrotF c) z fuel.

  Close Scope C_scope.
  Definition escapeCount (l0 : Vector C) : bigQ :=
    let llength := size C l0 in
    let sum' := fold_left (fun acc x => if (lebQ (CModSq x) 4) then acc else acc + 1) (val C l0) 0 in
    if (BigQ.eqb sum' 0) then 0 else llength - sum'.

  Open Scope string_scope.
  Function buildStr (pts : list C) (acc : string) {measure List.length pts} :=
    match pts with
    | nil => acc
    | _ =>   let charstr := append (concat "" (map (fun x => toChar (escapeCount (nApplMandelbrot x (0,0) Iterations))) (firstn Width pts))) (String (Ascii.ascii_of_N 10) EmptyString) in
            buildStr (skipn Width pts) (acc ++ charstr)
    end.
  Proof.
    intros * S p ptse H.
    set (length_skipn Width (p :: ptse)).
    rewrite e.
    simpl.
    lia.
  Defined.
  Close Scope string_scope.
End Mandelbrot.

Open Scope string_scope.
(* Compute map (fun x => toChar (escapeCount (nApplMandelbrot x (0,0) Iterations))) (firstn Width points). *)
Compute ((buildStr points "")).
