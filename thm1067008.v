Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067008_term_abbrevs.
Require Import thm1066571_spec.
Lemma lem1066997 {A B : Type'} : (term0 A B) = (term0 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1066998 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : (term2 A B INL') = (term3 A B).
Proof. exact (MK_COMB (@lem1066997 A B) (@lem1066571 A B INL' h1)). Qed.
Lemma lem1066999 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (eq_refl (term3 A B)). Qed.
Lemma lem1067000 {A B : Type'} (INL' : type1431 A B) : (term5 A B INL') = (term5 A B INL').
Proof. exact (eq_refl (term5 A B INL')). Qed.
Lemma lem1067001 {A B : Type'} (INL' : type1431 A B) : ((term2 A B INL') = (term3 A B)) = ((term2 A B INL') = (term4 A B)).
Proof. exact (MK_COMB (@lem1067000 A B INL') (@lem1066999 A B)). Qed.
Lemma lem1067002 {A B : Type'} (INL' : type1431 A B) : (term2 A B INL') = (term6 A B INL').
Proof. exact (eq_refl (term2 A B INL')). Qed.
Lemma lem1067003 {A B : Type'} : (@eq (A -> Datatypes.sum A B)) = (@eq (A -> Datatypes.sum A B)).
Proof. exact (eq_refl (@eq (A -> Datatypes.sum A B))). Qed.
Lemma lem1067004 {A B : Type'} (INL' : type1431 A B) : (term5 A B INL') = (term7 A B INL').
Proof. exact (MK_COMB (@lem1067003 A B) (@lem1067002 A B INL')). Qed.
Lemma lem1067005 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (eq_refl (term4 A B)). Qed.
Lemma lem1067006 {A B : Type'} (INL' : type1431 A B) : ((term2 A B INL') = (term4 A B)) = ((term6 A B INL') = (term4 A B)).
Proof. exact (MK_COMB (@lem1067004 A B INL') (@lem1067005 A B)). Qed.
Lemma lem1067007 {A B : Type'} (INL' : type1431 A B) : ((term2 A B INL') = (term3 A B)) = ((term6 A B INL') = (term4 A B)).
Proof. exact (TRANS (@lem1067001 A B INL') (@lem1067006 A B INL')). Qed.
Lemma lem1067008 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term1 A B)) : (term6 A B INL') = (term4 A B).
Proof. exact (EQ_MP (@lem1067007 A B INL') (@lem1066998 A B INL' h1)). Qed.
