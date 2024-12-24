Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ISO_term_abbrevs.
Lemma lem1075088 {A B : Type'} : (@ExtensionalityFacts.is_inverse A B) = (term0 A B).
Proof. exact (@ISO_def A B). Qed.
Lemma lem1075089 {A B : Type'} (_17569 : A -> B) : _17569 = _17569.
Proof. exact (eq_refl _17569). Qed.
Lemma lem1075090 {A B : Type'} (_17569 : A -> B) : (@ExtensionalityFacts.is_inverse A B _17569) = (term1 A B _17569).
Proof. exact (MK_COMB (@lem1075088 A B) (@lem1075089 A B _17569)). Qed.
Lemma lem1075091 {A B : Type'} (_17569 : A -> B) : (term1 A B _17569) = (term2 A B _17569).
Proof. exact (eq_refl (term1 A B _17569)). Qed.
Lemma lem1075092 {A B : Type'} (_17569 : A -> B) : (@ExtensionalityFacts.is_inverse A B _17569) = (term2 A B _17569).
Proof. exact (TRANS (@lem1075090 A B _17569) (@lem1075091 A B _17569)). Qed.
Lemma lem1075093 {A B : Type'} (_17570 : B -> A) : _17570 = _17570.
Proof. exact (eq_refl _17570). Qed.
Lemma lem1075094 {A B : Type'} (_17569 : A -> B) (_17570 : B -> A) : (@ExtensionalityFacts.is_inverse A B _17569 _17570) = (term3 A B _17569 _17570).
Proof. exact (MK_COMB (@lem1075092 A B _17569) (@lem1075093 A B _17570)). Qed.
Lemma lem1075095 {A B : Type'} (_17570 : B -> A) (_17569 : A -> B) : (term3 A B _17569 _17570) = (term4 A B _17570 _17569).
Proof. exact (eq_refl (term3 A B _17569 _17570)). Qed.
Lemma lem1075096 {A B : Type'} (_17570 : B -> A) (_17569 : A -> B) : (@ExtensionalityFacts.is_inverse A B _17569 _17570) = (term4 A B _17570 _17569).
Proof. exact (TRANS (@lem1075094 A B _17569 _17570) (@lem1075095 A B _17570 _17569)). Qed.
Lemma lem1075097 {A B : Type'} (_17569 : A -> B) : term5 A B _17569.
Proof. exact (fun _17570 : B -> A => @lem1075096 A B _17570 _17569). Qed.
Lemma lem1075098 {A B : Type'} : term6 A B.
Proof. exact (fun _17569 : A -> B => @lem1075097 A B _17569). Qed.
Lemma lem1075099 {A B : Type'} (_17569 : A -> B) : term7 A B _17569.
Proof. exact (@lem1075098 A B _17569). Qed.
Lemma lem1075100 {A B : Type'} (_17569 : A -> B) : (term7 A B _17569) = (term5 A B _17569).
Proof. exact (eq_refl (term7 A B _17569)). Qed.
Lemma lem1075101 {A B : Type'} (_17569 : A -> B) : term5 A B _17569.
Proof. exact (EQ_MP (@lem1075100 A B _17569) (@lem1075099 A B _17569)). Qed.
Lemma lem1075102 {A B : Type'} (_17569 : A -> B) (_17570 : B -> A) : term8 A B _17569 _17570.
Proof. exact (@lem1075101 A B _17569 _17570). Qed.
Lemma lem1075103 {A B : Type'} (_17570 : B -> A) (_17569 : A -> B) : (term8 A B _17569 _17570) = ((@ExtensionalityFacts.is_inverse A B _17569 _17570) = (term4 A B _17570 _17569)).
Proof. exact (eq_refl (term8 A B _17569 _17570)). Qed.
Lemma lem1075104 {A B : Type'} (_17570 : B -> A) (_17569 : A -> B) : (@ExtensionalityFacts.is_inverse A B _17569 _17570) = (term4 A B _17570 _17569).
Proof. exact (EQ_MP (@lem1075103 A B _17570 _17569) (@lem1075102 A B _17569 _17570)). Qed.
Lemma lem1075147 {A B : Type'} (g : B -> A) (f : A -> B) : (@ExtensionalityFacts.is_inverse A B f g) = (term4 A B g f).
Proof. exact (@lem1075104 A B g f). Qed.
Lemma lem1075148 {A B : Type'} (g : B -> A) : term9 A B g.
Proof. exact (fun f : A -> B => @lem1075147 A B g f). Qed.
Lemma lem1075149 {A B : Type'} : term10 A B.
Proof. exact (fun g : B -> A => @lem1075148 A B g). Qed.
