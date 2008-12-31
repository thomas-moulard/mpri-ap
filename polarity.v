(* Polarity definition *)
Require Import List.

Inductive polarity : Type :=
| Plus
| Minus
| NonMonotonic.

Definition mul_pol (a: polarity) (b: polarity): polarity :=
  match a, b with
    | NonMonotonic, _ => NonMonotonic
    | _, NonMonotonic => NonMonotonic
    | Plus, Plus => Plus
    | Minus, Minus => Plus
    | Plus, Minus => Minus
    | Minus, Plus => Minus
  end.

Lemma mul_pol_nm : forall x : polarity, mul_pol x NonMonotonic = NonMonotonic.
Proof.
  unfold mul_pol in |- *.
  intro x.
  induction x; reflexivity.
Qed.

Lemma mul_pol_pp_mm : forall x: polarity, mul_pol x x = Plus \/ x = NonMonotonic.
Proof.
  unfold mul_pol in |- *.
  intro x.
  induction x; [ left | left | right ]; reflexivity.
Qed.

Inductive typ : Type :=
| Nat : typ
| Fun : polarity -> typ -> typ -> typ.

Inductive cst : Type :=
| Zero
| Succ
| Addition
| Substraction
| Rec.

Inductive trm : Set :=
| Var : nat -> trm
| Cst : cst -> trm
| App : trm -> trm -> trm
| Abs : polarity -> typ -> trm -> trm.

Definition env := list (option (polarity * typ)).


(* Typing judgement *)

Definition sigma (x: cst) : typ :=
  match x with
    | Zero => Nat
    | Succ => Fun Plus Nat Nat
    | Addition => Fun Plus Nat (Fun Plus Nat Nat)
    | Substraction => Fun Plus Nat (Fun Plus Nat Nat)
    | Rec => Nat (* FIXME: *)
  end.

(*
Inductive type : env -> trm -> typ -> Prop :=
| type_cst : forall e t,
  match t with
    | Cst c => type e t (sigma c)
    | Var v => forall tau, type e t tau
    | App t1 t2 => forall tau, type e t tau
    | Abs p t1 t2 => forall tau, type e t tau
  end.
*)
