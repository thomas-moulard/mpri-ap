
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
| Fun : (*polarity -> *) typ -> typ -> typ.

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
    | Succ => Fun Nat Nat
    | Addition => Fun Nat (Fun Nat Nat)
    | Substraction => Fun Nat (Fun Nat Nat)
    | Rec => Nat (* FIXME: *)
  end.

Definition inv_env (p : polarity) (e : env) : env :=
  match p with
    | Plus => e
    | Minus => map (fun x => option_map
      (fun x : (polarity * typ) => let (p, t) := x in (mul_pol Minus p, t)) x) e
    | NonMonotonic => map (fun x : option (polarity * typ) =>
      match x with
        | Some (NonMonotonic, _) => x
        | Some (Plus, _) | Some (Minus, _) | None => None
      end) e
  end.

Inductive type : env -> trm -> typ -> Prop :=
| type_cst : forall e t,
  match t with
    | Cst c => type e t (sigma c)
    | Var v => match (nth v e None) with
                 | Some (Plus, tau) => type e t tau
                 | Some (NonMonotonic, tau) => type e t tau
                 | Some (Minus, tau) => forall tau, type e t tau (*FIXME: ?? *)
                 | None => forall tau, type e t tau (*FIXME: ?? *)
               end

    | App u v => forall tau1, forall tau2, forall p, type e (Abs p (Fun tau1 tau2) u) (Fun tau1 tau2) ->
      type (inv_env p e) v tau1 -> type e (App u v) tau2

    | Abs p tau1 m => forall tau2, type e m tau2 -> type e (Abs p tau1 m) (Fun tau1 tau2)
  end.




