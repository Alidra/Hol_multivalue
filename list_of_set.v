Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import list_of_set_term_abbrevs.
Lemma lem4786544 {_110256 : Type'} : (@list_of_set _110256) = (term0 _110256).
Proof. exact (@list_of_set_def _110256). Qed.
Lemma lem4786545 {_110256 : Type'} (_59118 : _110256 -> Prop) : _59118 = _59118.
Proof. exact (eq_refl _59118). Qed.
Lemma lem4786546 {_110256 : Type'} (_59118 : _110256 -> Prop) : (@list_of_set _110256 _59118) = (term1 _110256 _59118).
Proof. exact (MK_COMB (@lem4786544 _110256) (@lem4786545 _110256 _59118)). Qed.
Lemma lem4786547 {_110256 : Type'} (_59118 : _110256 -> Prop) : (term1 _110256 _59118) = (term2 _110256 _59118).
Proof. exact (eq_refl (term1 _110256 _59118)). Qed.
Lemma lem4786548 {_110256 : Type'} (_59118 : _110256 -> Prop) : (@list_of_set _110256 _59118) = (term2 _110256 _59118).
Proof. exact (TRANS (@lem4786546 _110256 _59118) (@lem4786547 _110256 _59118)). Qed.
Lemma lem4786549 {_110256 : Type'} : term3 _110256.
Proof. exact (fun _59118 : _110256 -> Prop => @lem4786548 _110256 _59118). Qed.
Lemma lem4786550 {_110256 : Type'} (_59118 : _110256 -> Prop) : term4 _110256 _59118.
Proof. exact (@lem4786549 _110256 _59118). Qed.
Lemma lem4786551 {_110256 : Type'} (_59118 : _110256 -> Prop) : (term4 _110256 _59118) = ((@list_of_set _110256 _59118) = (term2 _110256 _59118)).
Proof. exact (eq_refl (term4 _110256 _59118)). Qed.
Lemma lem4786552 {_110256 : Type'} (_59118 : _110256 -> Prop) : (@list_of_set _110256 _59118) = (term2 _110256 _59118).
Proof. exact (EQ_MP (@lem4786551 _110256 _59118) (@lem4786550 _110256 _59118)). Qed.
Lemma lem4786582 {_110256 : Type'} (s : _110256 -> Prop) : (@list_of_set _110256 s) = (term2 _110256 s).
Proof. exact (@lem4786552 _110256 s). Qed.
Lemma lem4786583 {_110256 : Type'} : term3 _110256.
Proof. exact (fun s : _110256 -> Prop => @lem4786582 _110256 s). Qed.
