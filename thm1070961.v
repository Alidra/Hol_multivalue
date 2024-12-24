Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070961_term_abbrevs.
Require Import thm1070450_spec.
Require Import thm1070451_spec.
Lemma lem1070937 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : list' = (term0 A NIL' CONS').
Proof. exact (h1). Qed.
Lemma lem1070938 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem1070939 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term2 A)) : (term3 A NIL') = (term4 A).
Proof. exact (MK_COMB (@lem1070938 A) (@lem1070450 A NIL' h1)). Qed.
Lemma lem1070940 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1070941 {A : Type'} (NIL' : recspace A) : (term6 A NIL') = (term6 A NIL').
Proof. exact (eq_refl (term6 A NIL')). Qed.
Lemma lem1070942 {A : Type'} (NIL' : recspace A) : ((term3 A NIL') = (term4 A)) = ((term3 A NIL') = (term5 A)).
Proof. exact (MK_COMB (@lem1070941 A NIL') (@lem1070940 A)). Qed.
Lemma lem1070943 {A : Type'} (NIL' : recspace A) : (term3 A NIL') = (term7 A NIL').
Proof. exact (eq_refl (term3 A NIL')). Qed.
Lemma lem1070944 {A : Type'} : (@eq ((A -> (recspace A) -> recspace A) -> (recspace A) -> Prop)) = (@eq ((A -> (recspace A) -> recspace A) -> (recspace A) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> (recspace A) -> recspace A) -> (recspace A) -> Prop))). Qed.
Lemma lem1070945 {A : Type'} (NIL' : recspace A) : (term6 A NIL') = (term8 A NIL').
Proof. exact (MK_COMB (@lem1070944 A) (@lem1070943 A NIL')). Qed.
Lemma lem1070946 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (eq_refl (term5 A)). Qed.
Lemma lem1070947 {A : Type'} (NIL' : recspace A) : ((term3 A NIL') = (term5 A)) = ((term7 A NIL') = (term5 A)).
Proof. exact (MK_COMB (@lem1070945 A NIL') (@lem1070946 A)). Qed.
Lemma lem1070948 {A : Type'} (NIL' : recspace A) : ((term3 A NIL') = (term4 A)) = ((term7 A NIL') = (term5 A)).
Proof. exact (TRANS (@lem1070942 A NIL') (@lem1070947 A NIL')). Qed.
Lemma lem1070949 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term2 A)) : (term7 A NIL') = (term5 A).
Proof. exact (EQ_MP (@lem1070948 A NIL') (@lem1070939 A NIL' h1)). Qed.
Lemma lem1070950 {A : Type'} (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term9 A)) (h2 : NIL' = (term2 A)) : (term10 A NIL' CONS') = (term11 A).
Proof. exact (MK_COMB (@lem1070949 A NIL' h2) (@lem1070451 A CONS' h1)). Qed.
Lemma lem1070951 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem1070952 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : (term13 A NIL' CONS') = (term13 A NIL' CONS').
Proof. exact (eq_refl (term13 A NIL' CONS')). Qed.
Lemma lem1070953 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : ((term10 A NIL' CONS') = (term11 A)) = ((term10 A NIL' CONS') = (term12 A)).
Proof. exact (MK_COMB (@lem1070952 A NIL' CONS') (@lem1070951 A)). Qed.
Lemma lem1070954 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : (term10 A NIL' CONS') = (term0 A NIL' CONS').
Proof. exact (eq_refl (term10 A NIL' CONS')). Qed.
Lemma lem1070955 {A : Type'} : (@eq ((recspace A) -> Prop)) = (@eq ((recspace A) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace A) -> Prop))). Qed.
Lemma lem1070956 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : (term13 A NIL' CONS') = (term14 A NIL' CONS').
Proof. exact (MK_COMB (@lem1070955 A) (@lem1070954 A NIL' CONS')). Qed.
Lemma lem1070957 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (eq_refl (term12 A)). Qed.
Lemma lem1070958 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : ((term10 A NIL' CONS') = (term12 A)) = ((term0 A NIL' CONS') = (term12 A)).
Proof. exact (MK_COMB (@lem1070956 A NIL' CONS') (@lem1070957 A)). Qed.
Lemma lem1070959 {A : Type'} (NIL' : recspace A) (CONS' : type1399 A) : ((term10 A NIL' CONS') = (term11 A)) = ((term0 A NIL' CONS') = (term12 A)).
Proof. exact (TRANS (@lem1070953 A NIL' CONS') (@lem1070958 A NIL' CONS')). Qed.
Lemma lem1070960 {A : Type'} (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term9 A)) (h2 : NIL' = (term2 A)) : (term0 A NIL' CONS') = (term12 A).
Proof. exact (EQ_MP (@lem1070959 A NIL' CONS') (@lem1070950 A CONS' NIL' h1 h2)). Qed.
Lemma lem1070961 {A : Type'} (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term9 A)) (h2 : list' = (term0 A NIL' CONS')) (h3 : NIL' = (term2 A)) : list' = (term12 A).
Proof. exact (TRANS (@lem1070937 A list' NIL' CONS' h2) (@lem1070960 A CONS' NIL' h1 h3)). Qed.
