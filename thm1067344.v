Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067344_term_abbrevs.
Require Import thm1066572_spec.
Lemma lem1067333 {A B : Type'} : (term0 A B) = (term0 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1067334 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term1 A B)) : (term2 A B INR') = (term3 A B).
Proof. exact (MK_COMB (@lem1067333 A B) (@lem1066572 A B INR' h1)). Qed.
Lemma lem1067335 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (eq_refl (term3 A B)). Qed.
Lemma lem1067336 {A B : Type'} (INR' : type1479 A B) : (term5 A B INR') = (term5 A B INR').
Proof. exact (eq_refl (term5 A B INR')). Qed.
Lemma lem1067337 {A B : Type'} (INR' : type1479 A B) : ((term2 A B INR') = (term3 A B)) = ((term2 A B INR') = (term4 A B)).
Proof. exact (MK_COMB (@lem1067336 A B INR') (@lem1067335 A B)). Qed.
Lemma lem1067338 {A B : Type'} (INR' : type1479 A B) : (term2 A B INR') = (term6 A B INR').
Proof. exact (eq_refl (term2 A B INR')). Qed.
Lemma lem1067339 {A B : Type'} : (@eq (B -> Datatypes.sum A B)) = (@eq (B -> Datatypes.sum A B)).
Proof. exact (eq_refl (@eq (B -> Datatypes.sum A B))). Qed.
Lemma lem1067340 {A B : Type'} (INR' : type1479 A B) : (term5 A B INR') = (term7 A B INR').
Proof. exact (MK_COMB (@lem1067339 A B) (@lem1067338 A B INR')). Qed.
Lemma lem1067341 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (eq_refl (term4 A B)). Qed.
Lemma lem1067342 {A B : Type'} (INR' : type1479 A B) : ((term2 A B INR') = (term4 A B)) = ((term6 A B INR') = (term4 A B)).
Proof. exact (MK_COMB (@lem1067340 A B INR') (@lem1067341 A B)). Qed.
Lemma lem1067343 {A B : Type'} (INR' : type1479 A B) : ((term2 A B INR') = (term3 A B)) = ((term6 A B INR') = (term4 A B)).
Proof. exact (TRANS (@lem1067337 A B INR') (@lem1067342 A B INR')). Qed.
Lemma lem1067344 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term1 A B)) : (term6 A B INR') = (term4 A B).
Proof. exact (EQ_MP (@lem1067343 A B INR') (@lem1067334 A B INR' h1)). Qed.
