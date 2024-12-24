Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069413_term_abbrevs.
Require Import thm1069370_spec.
Require Import thm1069398_spec.
Lemma lem1069399 {A : Type'} (NONE' : recspace A) : NONE' = NONE'.
Proof. exact (eq_refl NONE'). Qed.
Lemma lem1069400 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term0 A)) (h2 : option' = (term1 A NONE' SOME')) (h3 : NONE' = (term2 A)) : (option' NONE') = (term3 A NONE').
Proof. exact (MK_COMB (@lem1069398 A option' SOME' NONE' h1 h2 h3) (@lem1069399 A NONE')). Qed.
Lemma lem1069401 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term0 A)) (h2 : option' = (term1 A NONE' SOME')) (h3 : NONE' = (term2 A)) : term3 A NONE'.
Proof. exact (EQ_MP (@lem1069400 A option' SOME' NONE' h1 h2 h3) (@lem1069370 A option' NONE' SOME' h2)). Qed.
Lemma lem1069402 {A : Type'} : (term2 A) = (term2 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1069403 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) (h2 : option' = (term1 A NONE' SOME')) : term4 A NONE'.
Proof. exact (fun h0 : NONE' = (term2 A) => @lem1069401 A option' SOME' NONE' h1 h2 h0). Qed.
Lemma lem1069404 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) (h2 : option' = (term5 A SOME')) : term6 A.
Proof. exact (@lem1069403 A option' (term2 A) SOME' h1 h2). Qed.
Lemma lem1069405 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) (h2 : option' = (term5 A SOME')) : term7 A.
Proof. exact (@lem1069404 A option' SOME' h1 h2 (@lem1069402 A)). Qed.
Lemma lem1069406 {A : Type'} (SOME' : type1432 A) : (term5 A SOME') = (term5 A SOME').
Proof. exact (eq_refl (term5 A SOME')). Qed.
Lemma lem1069407 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : term8 A option' SOME'.
Proof. exact (fun h0 : option' = (term5 A SOME') => @lem1069405 A option' SOME' h1 h0). Qed.
Lemma lem1069408 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : term9 A SOME'.
Proof. exact (@lem1069407 A (term5 A SOME') SOME' h1). Qed.
Lemma lem1069409 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : term7 A.
Proof. exact (@lem1069408 A SOME' h1 (@lem1069406 A SOME')). Qed.
Lemma lem1069410 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1069411 {A : Type'} (SOME' : type1432 A) : term10 A SOME'.
Proof. exact (fun h0 : SOME' = (term0 A) => @lem1069409 A SOME' h0). Qed.
Lemma lem1069412 {A : Type'} : term11 A.
Proof. exact (@lem1069411 A (term0 A)). Qed.
Lemma lem1069413 {A : Type'} : term7 A.
Proof. exact (@lem1069412 A (@lem1069410 A)). Qed.
