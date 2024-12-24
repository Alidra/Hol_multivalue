Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_ELIM_THM_term_abbrevs.
Require Import thm3184741_spec.
Require Import thm3184746_spec.
Lemma lem3184751 {_83064 : Type'} : term0 _83064.
Proof. exact (fun P : type919 _83064 => @lem3184746 _83064 P). Qed.
Lemma lem3184752 {_83064 _83095 _83123 _83152 _83169 : Type'} : term1 _83064 _83095 _83123 _83152 _83169.
Proof. exact (conj (@lem3184751 _83064) (@lem3184741 _83095 _83123 _83152 _83169)). Qed.
