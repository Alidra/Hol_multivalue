Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_term_abbrevs.
Require Import FINITE_IMAGE_EXPAND_spec.
Require Import IMAGE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3615040 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem3615039 A B f). Qed.
Lemma lem3615041 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem3615042 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3615041 A B f) (@lem3615040 A B f)). Qed.
Lemma lem3615043 {A B : Type'} (f : A -> B) (s : A -> Prop) : term2 A B f s.
Proof. exact (@lem3615042 A B f s). Qed.
Lemma lem3615044 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B f s) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B f s)). Qed.
Lemma lem3615045 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem3615044 A B s f) (@lem3615043 A B f s)). Qed.
Lemma lem3615046 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B s f) = ((term3 A B s f) = True).
Proof. exact (@lem7 (term3 A B s f)). Qed.
Lemma lem3615048 {A B : Type'} (s : A -> Prop) : term4 A B s.
Proof. exact (@lem3199546 A B s). Qed.
Lemma lem3615049 {A B : Type'} (s : A -> Prop) : (term4 A B s) = (term5 A B s).
Proof. exact (eq_refl (term4 A B s)). Qed.
Lemma lem3615050 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (EQ_MP (@lem3615049 A B s) (@lem3615048 A B s)). Qed.
Lemma lem3615051 {A B : Type'} (s : A -> Prop) (f : A -> B) : term6 A B s f.
Proof. exact (@lem3615050 A B s f). Qed.
Lemma lem3615052 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term6 A B s f) = ((@IMAGE A B f s) = (term7 A B s f)).
Proof. exact (eq_refl (term6 A B s f)). Qed.
Lemma lem3615065 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term7 A B s f).
Proof. exact (EQ_MP (@lem3615052 A B s f) (@lem3615051 A B s f)). Qed.
Lemma lem3615066 {A B : Type'} (s : A -> Prop) (f : A -> B) : (@IMAGE A B f s) = (term7 A B s f).
Proof. exact (@lem3615065 A B s f). Qed.
Lemma lem3615079 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem3615080 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term8 A B f s) = (term9 A B s f).
Proof. exact (MK_COMB (@lem3615079 B) (@lem3615066 A B s f)). Qed.
Lemma lem3615081 {A : Type'} (s : A -> Prop) : (term10 A s) = (term10 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem3615082 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B f s) = (term3 A B s f).
Proof. exact (MK_COMB (@lem3615081 A s) (@lem3615080 A B s f)). Qed.
Lemma lem3615084 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B s f) = True.
Proof. exact (EQ_MP (@lem3615046 A B s f) (@lem3615045 A B s f)). Qed.
Lemma lem3615085 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term3 A B s f) = True.
Proof. exact (@lem3615084 A B s f). Qed.
Lemma lem3615086 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term11 A B f s) = True.
Proof. exact (TRANS (@lem3615082 A B s f) (@lem3615085 A B s f)). Qed.
Lemma lem3615087 {A B : Type'} (f : A -> B) : (term12 A B f) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3615086 A B f s)). Qed.
Lemma lem3615088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3615089 {A B : Type'} (f : A -> B) : (term14 A B f) = (term15 A).
Proof. exact (MK_COMB (@lem3615088 A) (@lem3615087 A B f)). Qed.
Lemma lem3615091 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3615092 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem3615091 (A -> Prop) t). Qed.
Lemma lem3615093 {A : Type'} : (term15 A) = True.
Proof. exact (@lem3615092 A True). Qed.
Lemma lem3615094 {A B : Type'} (f : A -> B) : (term14 A B f) = True.
Proof. exact (TRANS (@lem3615089 A B f) (@lem3615093 A)). Qed.
Lemma lem3615095 {A B : Type'} : (term18 A B) = (term19 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3615094 A B f)). Qed.
Lemma lem3615096 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3615097 {A B : Type'} : (term20 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem3615096 A B) (@lem3615095 A B)). Qed.
Lemma lem3615099 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3615100 {A B : Type'} (t : Prop) : (term22 A B t) = t.
Proof. exact (@lem3615099 (A -> B) t). Qed.
Lemma lem3615101 {A B : Type'} : (term21 A B) = True.
Proof. exact (@lem3615100 A B True). Qed.
Lemma lem3615102 {A B : Type'} : (term20 A B) = True.
Proof. exact (TRANS (@lem3615097 A B) (@lem3615101 A B)). Qed.
Lemma lem3615103 {A B : Type'} : True = (term20 A B).
Proof. exact (SYM (@lem3615102 A B)). Qed.
Lemma lem3615104 {A B : Type'} : term20 A B.
Proof. exact (EQ_MP (@lem3615103 A B) (@lem0)). Qed.
