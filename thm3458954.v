Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458954_term_abbrevs.
Require Import thm3458942_spec.
Lemma lem3458949 {_89646 _89670 _89671 _89672 : Type'} (P : type1517 _89670 _89671 _89672) : term0 _89646 _89670 _89671 _89672 P.
Proof. exact (fun f : type1524 _89646 _89670 _89671 _89672 => @lem3458942 _89646 _89670 _89671 _89672 P f). Qed.
Lemma lem3458954 {_89646 _89670 _89671 _89672 : Type'} : term1 _89646 _89670 _89671 _89672.
Proof. exact (fun P : type1517 _89670 _89671 _89672 => @lem3458949 _89646 _89670 _89671 _89672 P). Qed.
