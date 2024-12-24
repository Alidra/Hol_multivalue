Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247338_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247319 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1247320 (p : nat) (n : nat) (d : nat) (d' : nat) : (term0 d d' n p) = (term1 p n d d').
Proof. exact (@lem1247319 p n d d'). Qed.
Lemma lem1247321 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1247322 (p : nat) (n : nat) (d'' : nat) : (term5 p n d'') = (term5 p n d'').
Proof. exact (eq_refl (term5 p n d'')). Qed.
Lemma lem1247323 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 p n d d' d'') = (term7 p n d d' d'').
Proof. exact (MK_COMB (@lem1247322 p n d'') (@lem1247321 d d' d'')). Qed.
Lemma lem1247324 (d : nat) (d' : nat) (d'' : nat) : (term3 d d' d'') = (term4 d d' d'').
Proof. exact (eq_refl (term3 d d' d'')). Qed.
Lemma lem1247325 (n : nat) (p : nat) (d'' : nat) : (term5 n p d'') = (term5 n p d'').
Proof. exact (eq_refl (term5 n p d'')). Qed.
Lemma lem1247326 (n : nat) (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term6 n p d d' d'') = (term7 n p d d' d'').
Proof. exact (MK_COMB (@lem1247325 n p d'') (@lem1247324 d d' d'')). Qed.
Lemma lem1247327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247328 (n : nat) (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term8 n p d d' d'') = (term9 n p d d' d'').
Proof. exact (MK_COMB (@lem1247327) (@lem1247326 n p d d' d'')). Qed.
Lemma lem1247329 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) : (term10 p n d d' d'') = (term11 p n d d' d'').
Proof. exact (MK_COMB (@lem1247328 n p d d' d'') (@lem1247323 p n d d' d'')). Qed.
Lemma lem1247330 (p : nat) (n : nat) (d : nat) (d' : nat) : (term12 p n d d') = (term13 p n d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1247329 p n d d' d'')). Qed.
Lemma lem1247331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247332 (p : nat) (n : nat) (d : nat) (d' : nat) : (term1 p n d d') = (term14 p n d d').
Proof. exact (MK_COMB (@lem1247331) (@lem1247330 p n d d')). Qed.
Lemma lem1247333 (d : nat) (d' : nat) (n : nat) (p : nat) : (term0 d d' n p) = (term15 d d' n p).
Proof. exact (eq_refl (term0 d d' n p)). Qed.
Lemma lem1247334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247335 (d : nat) (d' : nat) (n : nat) (p : nat) : (term16 d d' n p) = (term17 d d' n p).
Proof. exact (MK_COMB (@lem1247334) (@lem1247333 d d' n p)). Qed.
Lemma lem1247336 (p : nat) (n : nat) (d : nat) (d' : nat) : ((term0 d d' n p) = (term1 p n d d')) = ((term15 d d' n p) = (term14 p n d d')).
Proof. exact (MK_COMB (@lem1247335 d d' n p) (@lem1247332 p n d d')). Qed.
Lemma lem1247337 (p : nat) (n : nat) (d : nat) (d' : nat) : (term15 d d' n p) = (term14 p n d d').
Proof. exact (EQ_MP (@lem1247336 p n d d') (@lem1247320 p n d d')). Qed.
Lemma lem1247338 (d : nat) (d' : nat) (n : nat) (p : nat) : (term14 p n d d') = (term15 d d' n p).
Proof. exact (SYM (@lem1247337 p n d d')). Qed.
