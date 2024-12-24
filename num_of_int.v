Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_of_int_term_abbrevs.
Lemma lem2833891 : num_of_int = term0.
Proof. exact (@num_of_int_def). Qed.
Lemma lem2833892 (_31107 : int) : _31107 = _31107.
Proof. exact (eq_refl _31107). Qed.
Lemma lem2833893 (_31107 : int) : (num_of_int _31107) = (term1 _31107).
Proof. exact (MK_COMB (@lem2833891) (@lem2833892 _31107)). Qed.
Lemma lem2833894 (_31107 : int) : (term1 _31107) = (term2 _31107).
Proof. exact (eq_refl (term1 _31107)). Qed.
Lemma lem2833895 (_31107 : int) : (num_of_int _31107) = (term2 _31107).
Proof. exact (TRANS (@lem2833893 _31107) (@lem2833894 _31107)). Qed.
Lemma lem2833896 : term3.
Proof. exact (fun _31107 : int => @lem2833895 _31107). Qed.
Lemma lem2833897 (_31107 : int) : term4 _31107.
Proof. exact (@lem2833896 _31107). Qed.
Lemma lem2833898 (_31107 : int) : (term4 _31107) = ((num_of_int _31107) = (term2 _31107)).
Proof. exact (eq_refl (term4 _31107)). Qed.
Lemma lem2833899 (_31107 : int) : (num_of_int _31107) = (term2 _31107).
Proof. exact (EQ_MP (@lem2833898 _31107) (@lem2833897 _31107)). Qed.
Lemma lem2833929 (x : int) : (num_of_int x) = (term2 x).
Proof. exact (@lem2833899 x). Qed.
Lemma lem2833930 : term3.
Proof. exact (fun x : int => @lem2833929 x). Qed.
