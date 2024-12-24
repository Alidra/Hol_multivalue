Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070976_term_abbrevs.
Require Import thm1070930_spec.
Require Import thm1070961_spec.
Lemma lem1070962 {A : Type'} (NIL' : recspace A) : NIL' = NIL'.
Proof. exact (eq_refl NIL'). Qed.
Lemma lem1070963 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term0 A)) (h2 : list' = (term1 A NIL' CONS')) (h3 : NIL' = (term2 A)) : (list' NIL') = (term3 A NIL').
Proof. exact (MK_COMB (@lem1070961 A list' CONS' NIL' h1 h2 h3) (@lem1070962 A NIL')). Qed.
Lemma lem1070964 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term0 A)) (h2 : list' = (term1 A NIL' CONS')) (h3 : NIL' = (term2 A)) : term3 A NIL'.
Proof. exact (EQ_MP (@lem1070963 A list' CONS' NIL' h1 h2 h3) (@lem1070930 A list' NIL' CONS' h2)). Qed.
Lemma lem1070965 {A : Type'} : (term2 A) = (term2 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1070966 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) (h2 : list' = (term1 A NIL' CONS')) : term4 A NIL'.
Proof. exact (fun h0 : NIL' = (term2 A) => @lem1070964 A list' CONS' NIL' h1 h2 h0). Qed.
Lemma lem1070967 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) (h2 : list' = (term5 A CONS')) : term6 A.
Proof. exact (@lem1070966 A list' (term2 A) CONS' h1 h2). Qed.
Lemma lem1070968 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) (h2 : list' = (term5 A CONS')) : term7 A.
Proof. exact (@lem1070967 A list' CONS' h1 h2 (@lem1070965 A)). Qed.
Lemma lem1070969 {A : Type'} (CONS' : type1399 A) : (term5 A CONS') = (term5 A CONS').
Proof. exact (eq_refl (term5 A CONS')). Qed.
Lemma lem1070970 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : term8 A list' CONS'.
Proof. exact (fun h0 : list' = (term5 A CONS') => @lem1070968 A list' CONS' h1 h0). Qed.
Lemma lem1070971 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : term9 A CONS'.
Proof. exact (@lem1070970 A (term5 A CONS') CONS' h1). Qed.
Lemma lem1070972 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : term7 A.
Proof. exact (@lem1070971 A CONS' h1 (@lem1070969 A CONS')). Qed.
Lemma lem1070973 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1070974 {A : Type'} (CONS' : type1399 A) : term10 A CONS'.
Proof. exact (fun h0 : CONS' = (term0 A) => @lem1070972 A CONS' h0). Qed.
Lemma lem1070975 {A : Type'} : term11 A.
Proof. exact (@lem1070974 A (term0 A)). Qed.
Lemma lem1070976 {A : Type'} : term7 A.
Proof. exact (@lem1070975 A (@lem1070973 A)). Qed.
