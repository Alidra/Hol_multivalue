Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247414_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247395 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1247396 (p : nat) (d : nat) (d' : nat) : (term3 d d' p) = (term4 p d d').
Proof. exact (@lem1247395 p (term5 p d d') d d'). Qed.
Lemma lem1247397 (d : nat) (d' : nat) (d'' : nat) : (term6 d d' d'') = (term7 d d' d'').
Proof. exact (eq_refl (term6 d d' d'')). Qed.
Lemma lem1247398 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term8 p d d' d'') = (term8 p d d' d'').
Proof. exact (eq_refl (term8 p d d' d'')). Qed.
Lemma lem1247399 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term9 p d d' d'') = (term10 p d d' d'').
Proof. exact (MK_COMB (@lem1247398 p d d' d'') (@lem1247397 d d' d'')). Qed.
Lemma lem1247400 (d : nat) (d' : nat) (d'' : nat) : (term6 d d' d'') = (term7 d d' d'').
Proof. exact (eq_refl (term6 d d' d'')). Qed.
Lemma lem1247401 (d : nat) (d' : nat) (p : nat) (d'' : nat) : (term11 d d' p d'') = (term11 d d' p d'').
Proof. exact (eq_refl (term11 d d' p d'')). Qed.
Lemma lem1247402 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term12 p d d' d'') = (term13 p d d' d'').
Proof. exact (MK_COMB (@lem1247401 d d' p d'') (@lem1247400 d d' d'')). Qed.
Lemma lem1247403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247404 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term14 p d d' d'') = (term15 p d d' d'').
Proof. exact (MK_COMB (@lem1247403) (@lem1247402 p d d' d'')). Qed.
Lemma lem1247405 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term16 p d d' d'') = (term17 p d d' d'').
Proof. exact (MK_COMB (@lem1247404 p d d' d'') (@lem1247399 p d d' d'')). Qed.
Lemma lem1247406 (p : nat) (d : nat) (d' : nat) : (term18 p d d') = (term19 p d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1247405 p d d' d'')). Qed.
Lemma lem1247407 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247408 (p : nat) (d : nat) (d' : nat) : (term4 p d d') = (term20 p d d').
Proof. exact (MK_COMB (@lem1247407) (@lem1247406 p d d')). Qed.
Lemma lem1247409 (d : nat) (d' : nat) (p : nat) : (term3 d d' p) = (term21 d d' p).
Proof. exact (eq_refl (term3 d d' p)). Qed.
Lemma lem1247410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247411 (d : nat) (d' : nat) (p : nat) : (term22 d d' p) = (term23 d d' p).
Proof. exact (MK_COMB (@lem1247410) (@lem1247409 d d' p)). Qed.
Lemma lem1247412 (p : nat) (d : nat) (d' : nat) : ((term3 d d' p) = (term4 p d d')) = ((term21 d d' p) = (term20 p d d')).
Proof. exact (MK_COMB (@lem1247411 d d' p) (@lem1247408 p d d')). Qed.
Lemma lem1247413 (p : nat) (d : nat) (d' : nat) : (term21 d d' p) = (term20 p d d').
Proof. exact (EQ_MP (@lem1247412 p d d') (@lem1247396 p d d')). Qed.
Lemma lem1247414 (d : nat) (d' : nat) (p : nat) : (term20 p d d') = (term21 d d' p).
Proof. exact (SYM (@lem1247413 p d d')). Qed.
