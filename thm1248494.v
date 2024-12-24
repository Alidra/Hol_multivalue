Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248494_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1248475 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1248476 (q : nat) (n : nat) (d : nat) (d' : nat) : (term0 d d' n q) = (term1 q n d d').
Proof. exact (@lem1248475 q n d d'). Qed.
Lemma lem1248477 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1248478 (q : nat) (n : nat) (d'' : nat) : (term5 q n d'') = (term5 q n d'').
Proof. exact (eq_refl (term5 q n d'')). Qed.
Lemma lem1248479 (q : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 q n d d' d'') = (term7 q n d d' d'').
Proof. exact (MK_COMB (@lem1248478 q n d'') (@lem1248477 d d' d'')). Qed.
Lemma lem1248480 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1248481 (n : nat) (q : nat) (d'' : nat) : (term5 n q d'') = (term5 n q d'').
Proof. exact (eq_refl (term5 n q d'')). Qed.
Lemma lem1248482 (n : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 n q d d' d'') = (term7 n q d d' d'').
Proof. exact (MK_COMB (@lem1248481 n q d'') (@lem1248480 d d' d'')). Qed.
Lemma lem1248483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1248484 (n : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) : (term8 n q d d' d'') = (term9 n q d d' d'').
Proof. exact (MK_COMB (@lem1248483) (@lem1248482 n q d d' d'')). Qed.
Lemma lem1248485 (q : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term10 q n d d' d'') = (term11 q n d d' d'').
Proof. exact (MK_COMB (@lem1248484 n q d d' d'') (@lem1248479 q n d d' d'')). Qed.
Lemma lem1248486 (q : nat) (n : nat) (d : nat) (d' : nat) : (term12 q n d d') = (term13 q n d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1248485 q n d d' d'')). Qed.
Lemma lem1248487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1248488 (q : nat) (n : nat) (d : nat) (d' : nat) : (term1 q n d d') = (term14 q n d d').
Proof. exact (MK_COMB (@lem1248487) (@lem1248486 q n d d')). Qed.
Lemma lem1248489 (d : nat) (d' : nat) (n : nat) (q : nat) : (term0 d d' n q) = (term15 d d' n q).
Proof. exact (eq_refl (term0 d d' n q)). Qed.
Lemma lem1248490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248491 (d : nat) (d' : nat) (n : nat) (q : nat) : (term16 d d' n q) = (term17 d d' n q).
Proof. exact (MK_COMB (@lem1248490) (@lem1248489 d d' n q)). Qed.
Lemma lem1248492 (q : nat) (n : nat) (d : nat) (d' : nat) : ((term0 d d' n q) = (term1 q n d d')) = ((term15 d d' n q) = (term14 q n d d')).
Proof. exact (MK_COMB (@lem1248491 d d' n q) (@lem1248488 q n d d')). Qed.
Lemma lem1248493 (q : nat) (n : nat) (d : nat) (d' : nat) : (term15 d d' n q) = (term14 q n d d').
Proof. exact (EQ_MP (@lem1248492 q n d d') (@lem1248476 q n d d')). Qed.
Lemma lem1248494 (d : nat) (d' : nat) (n : nat) (q : nat) : (term14 q n d d') = (term15 d d' n q).
Proof. exact (SYM (@lem1248493 q n d d')). Qed.
