Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248418_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1248399 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1248400 (q : nat) (n : nat) (d : nat) (d' : nat) : (term0 d d' n q) = (term1 q n d d').
Proof. exact (@lem1248399 q n d d'). Qed.
Lemma lem1248401 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1248402 (q : nat) (n : nat) (d'' : nat) : (term5 q n d'') = (term5 q n d'').
Proof. exact (eq_refl (term5 q n d'')). Qed.
Lemma lem1248403 (q : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 q n d d' d'') = (term7 q n d d' d'').
Proof. exact (MK_COMB (@lem1248402 q n d'') (@lem1248401 d d' d'')). Qed.
Lemma lem1248404 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1248405 (n : nat) (q : nat) (d'' : nat) : (term5 n q d'') = (term5 n q d'').
Proof. exact (eq_refl (term5 n q d'')). Qed.
Lemma lem1248406 (n : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 n q d d' d'') = (term7 n q d d' d'').
Proof. exact (MK_COMB (@lem1248405 n q d'') (@lem1248404 d d' d'')). Qed.
Lemma lem1248407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1248408 (n : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) : (term8 n q d d' d'') = (term9 n q d d' d'').
Proof. exact (MK_COMB (@lem1248407) (@lem1248406 n q d d' d'')). Qed.
Lemma lem1248409 (q : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term10 q n d d' d'') = (term11 q n d d' d'').
Proof. exact (MK_COMB (@lem1248408 n q d d' d'') (@lem1248403 q n d d' d'')). Qed.
Lemma lem1248410 (q : nat) (n : nat) (d : nat) (d' : nat) : (term12 q n d d') = (term13 q n d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1248409 q n d d' d'')). Qed.
Lemma lem1248411 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1248412 (q : nat) (n : nat) (d : nat) (d' : nat) : (term1 q n d d') = (term14 q n d d').
Proof. exact (MK_COMB (@lem1248411) (@lem1248410 q n d d')). Qed.
Lemma lem1248413 (d : nat) (d' : nat) (n : nat) (q : nat) : (term0 d d' n q) = (term15 d d' n q).
Proof. exact (eq_refl (term0 d d' n q)). Qed.
Lemma lem1248414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248415 (d : nat) (d' : nat) (n : nat) (q : nat) : (term16 d d' n q) = (term17 d d' n q).
Proof. exact (MK_COMB (@lem1248414) (@lem1248413 d d' n q)). Qed.
Lemma lem1248416 (q : nat) (n : nat) (d : nat) (d' : nat) : ((term0 d d' n q) = (term1 q n d d')) = ((term15 d d' n q) = (term14 q n d d')).
Proof. exact (MK_COMB (@lem1248415 d d' n q) (@lem1248412 q n d d')). Qed.
Lemma lem1248417 (q : nat) (n : nat) (d : nat) (d' : nat) : (term15 d d' n q) = (term14 q n d d').
Proof. exact (EQ_MP (@lem1248416 q n d d') (@lem1248400 q n d d')). Qed.
Lemma lem1248418 (d : nat) (d' : nat) (n : nat) (q : nat) : (term14 q n d d') = (term15 d d' n q).
Proof. exact (SYM (@lem1248417 q n d d')). Qed.
