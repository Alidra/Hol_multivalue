Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057189_term_abbrevs.
Require Import thm8057143_spec.
Lemma lem8057184 {_143061 _143062 _143063 : Type'} (f : type56 _143061 _143062) : term0 _143061 _143062 _143063 f.
Proof. exact (fun t : type24 _143061 _143063 => @lem8057143 _143061 _143062 _143063 f t). Qed.
Lemma lem8057189 {_143061 _143062 _143063 : Type'} : term1 _143061 _143062 _143063.
Proof. exact (fun f : type56 _143061 _143062 => @lem8057184 _143061 _143062 _143063 f). Qed.
