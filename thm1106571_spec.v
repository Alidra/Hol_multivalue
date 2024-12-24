Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1106571 : forall {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594), (fun t' : list _25594 => (@FILTER _25594 P (@cons _25594 h t')) = (@COND (list _25594) (P h) (@cons _25594 h (@FILTER _25594 P t')) (@FILTER _25594 P t'))) t.
