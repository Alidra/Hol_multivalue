Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247512_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247493 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1247494 (n : nat) (d : nat) (d' : nat) : (term3 n d' d) = (term4 n d d').
Proof. exact (@lem1247493 (term5 n d' d) n d d'). Qed.
Lemma lem1247495 (d : nat) (d' : nat) (d'' : nat) : (term6 d d' d'') = (term7 d d' d'').
Proof. exact (eq_refl (term6 d d' d'')). Qed.
Lemma lem1247496 (d' : nat) (d : nat) (n : nat) (d'' : nat) : (term8 d' d n d'') = (term8 d' d n d'').
Proof. exact (eq_refl (term8 d' d n d'')). Qed.
Lemma lem1247497 (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term9 n d d' d'') = (term10 n d d' d'').
Proof. exact (MK_COMB (@lem1247496 d' d n d'') (@lem1247495 d d' d'')). Qed.
Lemma lem1247498 (d : nat) (d' : nat) (d'' : nat) : (term6 d d' d'') = (term7 d d' d'').
Proof. exact (eq_refl (term6 d d' d'')). Qed.
Lemma lem1247499 (n : nat) (d' : nat) (d : nat) (d'' : nat) : (term11 n d' d d'') = (term11 n d' d d'').
Proof. exact (eq_refl (term11 n d' d d'')). Qed.
Lemma lem1247500 (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term12 n d d' d'') = (term13 n d d' d'').
Proof. exact (MK_COMB (@lem1247499 n d' d d'') (@lem1247498 d d' d'')). Qed.
Lemma lem1247501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247502 (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term14 n d d' d'') = (term15 n d d' d'').
Proof. exact (MK_COMB (@lem1247501) (@lem1247500 n d d' d'')). Qed.
Lemma lem1247503 (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term16 n d d' d'') = (term17 n d d' d'').
Proof. exact (MK_COMB (@lem1247502 n d d' d'') (@lem1247497 n d d' d'')). Qed.
Lemma lem1247504 (n : nat) (d : nat) (d' : nat) : (term18 n d d') = (term19 n d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1247503 n d d' d'')). Qed.
Lemma lem1247505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247506 (n : nat) (d : nat) (d' : nat) : (term4 n d d') = (term20 n d d').
Proof. exact (MK_COMB (@lem1247505) (@lem1247504 n d d')). Qed.
Lemma lem1247507 (n : nat) (d' : nat) (d : nat) : (term3 n d' d) = (term21 n d' d).
Proof. exact (eq_refl (term3 n d' d)). Qed.
Lemma lem1247508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247509 (n : nat) (d' : nat) (d : nat) : (term22 n d' d) = (term23 n d' d).
Proof. exact (MK_COMB (@lem1247508) (@lem1247507 n d' d)). Qed.
Lemma lem1247510 (n : nat) (d : nat) (d' : nat) : ((term3 n d' d) = (term4 n d d')) = ((term21 n d' d) = (term20 n d d')).
Proof. exact (MK_COMB (@lem1247509 n d' d) (@lem1247506 n d d')). Qed.
Lemma lem1247511 (n : nat) (d : nat) (d' : nat) : (term21 n d' d) = (term20 n d d').
Proof. exact (EQ_MP (@lem1247510 n d d') (@lem1247494 n d d')). Qed.
Lemma lem1247512 (n : nat) (d' : nat) (d : nat) : (term20 n d d') = (term21 n d' d).
Proof. exact (SYM (@lem1247511 n d d')). Qed.
