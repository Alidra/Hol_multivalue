Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057199_term_abbrevs.
Require Import thm8057155_spec.
Lemma lem8057194 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) : term0 _143007 _143008 _143009 s.
Proof. exact (fun f : type56 _143007 _143009 => @lem8057155 _143007 _143008 _143009 f s). Qed.
Lemma lem8057199 {_143007 _143008 _143009 : Type'} : term1 _143007 _143008 _143009.
Proof. exact (fun s : type24 _143007 _143008 => @lem8057194 _143007 _143008 _143009 s). Qed.
