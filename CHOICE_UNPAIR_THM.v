Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOICE_UNPAIR_THM_term_abbrevs.
Require Import LAMBDA_PAIR_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem56912 {A B C : Type'} (f : type1412 A B C) : term0 A B C f.
Proof. exact (@lem51406 A B C f). Qed.
Lemma lem56913 {A B C : Type'} (f : type1412 A B C) : (term0 A B C f) = ((term1 A B C f) = (term2 A B C f)).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem56922 {A B C : Type'} (f : type1412 A B C) : (term1 A B C f) = (term2 A B C f).
Proof. exact (EQ_MP (@lem56913 A B C f) (@lem56912 A B C f)). Qed.
Lemma lem56923 {A B : Type'} (f : type1413 A B) : (term3 A B f) = (term4 A B f).
Proof. exact (@lem56922 A B Prop f). Qed.
Lemma lem56924 {A B : Type'} (P : type1413 A B) : (term3 A B P) = (term4 A B P).
Proof. exact (@lem56923 A B P). Qed.
Lemma lem56925 {A B : Type'} : (@ε (prod A B)) = (@ε (prod A B)).
Proof. exact (eq_refl (@ε (prod A B))). Qed.
Lemma lem56926 {A B : Type'} (P : type1413 A B) : (term5 A B P) = (term6 A B P).
Proof. exact (MK_COMB (@lem56925 A B) (@lem56924 A B P)). Qed.
Lemma lem56927 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem56928 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (MK_COMB (@lem56927 A B) (@lem56926 A B P)). Qed.
Lemma lem56929 {A B : Type'} (P : type1413 A B) : (term6 A B P) = (term6 A B P).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem56930 {A B : Type'} (P : type1413 A B) : ((term5 A B P) = (term6 A B P)) = ((term6 A B P) = (term6 A B P)).
Proof. exact (MK_COMB (@lem56928 A B P) (@lem56929 A B P)). Qed.
Lemma lem56932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem56933 {A B : Type'} (x : prod A B) : (x = x) = True.
Proof. exact (@lem56932 (prod A B) x). Qed.
Lemma lem56934 {A B : Type'} (P : type1413 A B) : ((term6 A B P) = (term6 A B P)) = True.
Proof. exact (@lem56933 A B (term6 A B P)). Qed.
Lemma lem56935 {A B : Type'} (P : type1413 A B) : ((term5 A B P) = (term6 A B P)) = True.
Proof. exact (TRANS (@lem56930 A B P) (@lem56934 A B P)). Qed.
Lemma lem56936 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem56935 A B P)). Qed.
Lemma lem56937 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem56938 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem56937 A B) (@lem56936 A B)). Qed.
Lemma lem56940 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem56941 {A B : Type'} (t : Prop) : (term14 A B t) = t.
Proof. exact (@lem56940 (type1413 A B) t). Qed.
Lemma lem56942 {A B : Type'} : (term12 A B) = True.
Proof. exact (@lem56941 A B True). Qed.
Lemma lem56943 {A B : Type'} : (term11 A B) = True.
Proof. exact (TRANS (@lem56938 A B) (@lem56942 A B)). Qed.
Lemma lem56944 {A B : Type'} : True = (term11 A B).
Proof. exact (SYM (@lem56943 A B)). Qed.
Lemma lem56945 {A B : Type'} : term11 A B.
Proof. exact (EQ_MP (@lem56944 A B) (@lem0)). Qed.
