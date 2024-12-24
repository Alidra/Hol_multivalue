Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070997_term_abbrevs.
Require Import thm1070450_spec.
Lemma lem1070986 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1070987 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term1 A)) : (term2 A NIL') = (term3 A).
Proof. exact (MK_COMB (@lem1070986 A) (@lem1070450 A NIL' h1)). Qed.
Lemma lem1070988 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1070989 {A : Type'} (NIL' : recspace A) : (term5 A NIL') = (term5 A NIL').
Proof. exact (eq_refl (term5 A NIL')). Qed.
Lemma lem1070990 {A : Type'} (NIL' : recspace A) : ((term2 A NIL') = (term3 A)) = ((term2 A NIL') = (term4 A)).
Proof. exact (MK_COMB (@lem1070989 A NIL') (@lem1070988 A)). Qed.
Lemma lem1070991 {A : Type'} (NIL' : recspace A) : (term2 A NIL') = (@_mk_list A NIL').
Proof. exact (eq_refl (term2 A NIL')). Qed.
Lemma lem1070992 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1070993 {A : Type'} (NIL' : recspace A) : (term5 A NIL') = (term6 A NIL').
Proof. exact (MK_COMB (@lem1070992 A) (@lem1070991 A NIL')). Qed.
Lemma lem1070994 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1070995 {A : Type'} (NIL' : recspace A) : ((term2 A NIL') = (term4 A)) = ((@_mk_list A NIL') = (term4 A)).
Proof. exact (MK_COMB (@lem1070993 A NIL') (@lem1070994 A)). Qed.
Lemma lem1070996 {A : Type'} (NIL' : recspace A) : ((term2 A NIL') = (term3 A)) = ((@_mk_list A NIL') = (term4 A)).
Proof. exact (TRANS (@lem1070990 A NIL') (@lem1070995 A NIL')). Qed.
Lemma lem1070997 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term1 A)) : (@_mk_list A NIL') = (term4 A).
Proof. exact (EQ_MP (@lem1070996 A NIL') (@lem1070987 A NIL' h1)). Qed.
