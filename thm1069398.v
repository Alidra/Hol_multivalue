Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069398_term_abbrevs.
Require Import thm1069015_spec.
Require Import thm1069016_spec.
Lemma lem1069374 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : option' = (term0 A NONE' SOME').
Proof. exact (h1). Qed.
Lemma lem1069375 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem1069376 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term2 A)) : (term3 A NONE') = (term4 A).
Proof. exact (MK_COMB (@lem1069375 A) (@lem1069015 A NONE' h1)). Qed.
Lemma lem1069377 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1069378 {A : Type'} (NONE' : recspace A) : (term6 A NONE') = (term6 A NONE').
Proof. exact (eq_refl (term6 A NONE')). Qed.
Lemma lem1069379 {A : Type'} (NONE' : recspace A) : ((term3 A NONE') = (term4 A)) = ((term3 A NONE') = (term5 A)).
Proof. exact (MK_COMB (@lem1069378 A NONE') (@lem1069377 A)). Qed.
Lemma lem1069380 {A : Type'} (NONE' : recspace A) : (term3 A NONE') = (term7 A NONE').
Proof. exact (eq_refl (term3 A NONE')). Qed.
Lemma lem1069381 {A : Type'} : (@eq ((A -> recspace A) -> (recspace A) -> Prop)) = (@eq ((A -> recspace A) -> (recspace A) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> recspace A) -> (recspace A) -> Prop))). Qed.
Lemma lem1069382 {A : Type'} (NONE' : recspace A) : (term6 A NONE') = (term8 A NONE').
Proof. exact (MK_COMB (@lem1069381 A) (@lem1069380 A NONE')). Qed.
Lemma lem1069383 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (eq_refl (term5 A)). Qed.
Lemma lem1069384 {A : Type'} (NONE' : recspace A) : ((term3 A NONE') = (term5 A)) = ((term7 A NONE') = (term5 A)).
Proof. exact (MK_COMB (@lem1069382 A NONE') (@lem1069383 A)). Qed.
Lemma lem1069385 {A : Type'} (NONE' : recspace A) : ((term3 A NONE') = (term4 A)) = ((term7 A NONE') = (term5 A)).
Proof. exact (TRANS (@lem1069379 A NONE') (@lem1069384 A NONE')). Qed.
Lemma lem1069386 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term2 A)) : (term7 A NONE') = (term5 A).
Proof. exact (EQ_MP (@lem1069385 A NONE') (@lem1069376 A NONE' h1)). Qed.
Lemma lem1069387 {A : Type'} (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term9 A)) (h2 : NONE' = (term2 A)) : (term10 A NONE' SOME') = (term11 A).
Proof. exact (MK_COMB (@lem1069386 A NONE' h2) (@lem1069016 A SOME' h1)). Qed.
Lemma lem1069388 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem1069389 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term13 A NONE' SOME') = (term13 A NONE' SOME').
Proof. exact (eq_refl (term13 A NONE' SOME')). Qed.
Lemma lem1069390 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : ((term10 A NONE' SOME') = (term11 A)) = ((term10 A NONE' SOME') = (term12 A)).
Proof. exact (MK_COMB (@lem1069389 A NONE' SOME') (@lem1069388 A)). Qed.
Lemma lem1069391 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term10 A NONE' SOME') = (term0 A NONE' SOME').
Proof. exact (eq_refl (term10 A NONE' SOME')). Qed.
Lemma lem1069392 {A : Type'} : (@eq ((recspace A) -> Prop)) = (@eq ((recspace A) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace A) -> Prop))). Qed.
Lemma lem1069393 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : (term13 A NONE' SOME') = (term14 A NONE' SOME').
Proof. exact (MK_COMB (@lem1069392 A) (@lem1069391 A NONE' SOME')). Qed.
Lemma lem1069394 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (eq_refl (term12 A)). Qed.
Lemma lem1069395 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : ((term10 A NONE' SOME') = (term12 A)) = ((term0 A NONE' SOME') = (term12 A)).
Proof. exact (MK_COMB (@lem1069393 A NONE' SOME') (@lem1069394 A)). Qed.
Lemma lem1069396 {A : Type'} (NONE' : recspace A) (SOME' : type1432 A) : ((term10 A NONE' SOME') = (term11 A)) = ((term0 A NONE' SOME') = (term12 A)).
Proof. exact (TRANS (@lem1069390 A NONE' SOME') (@lem1069395 A NONE' SOME')). Qed.
Lemma lem1069397 {A : Type'} (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term9 A)) (h2 : NONE' = (term2 A)) : (term0 A NONE' SOME') = (term12 A).
Proof. exact (EQ_MP (@lem1069396 A NONE' SOME') (@lem1069387 A SOME' NONE' h1 h2)). Qed.
Lemma lem1069398 {A : Type'} (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term9 A)) (h2 : option' = (term0 A NONE' SOME')) (h3 : NONE' = (term2 A)) : option' = (term12 A).
Proof. exact (TRANS (@lem1069374 A option' NONE' SOME' h2) (@lem1069397 A SOME' NONE' h1 h3)). Qed.
