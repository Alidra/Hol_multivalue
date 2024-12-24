Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248368_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1248349 (_22840 : nat) (_22841 : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q _22841 _22840) = (term1 _22840 _22841 d n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 d n q)). Qed.
Lemma lem1248350 (m : nat) (d : nat) (n : nat) (q : nat) : (term3 n m d q) = (term4 m d n q).
Proof. exact (@lem1248349 (term5 m d q) (Nat.add m n) d n q). Qed.
Lemma lem1248351 (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 d n q d') = (term7 d d' n q).
Proof. exact (eq_refl (term6 d n q d')). Qed.
Lemma lem1248352 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) : (term8 d q m n d') = (term8 d q m n d').
Proof. exact (eq_refl (term8 d q m n d')). Qed.
Lemma lem1248353 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term9 m d n q d') = (term10 m d d' n q).
Proof. exact (MK_COMB (@lem1248352 d q m n d') (@lem1248351 d d' n q)). Qed.
Lemma lem1248354 (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 d n q d') = (term7 d d' n q).
Proof. exact (eq_refl (term6 d n q d')). Qed.
Lemma lem1248355 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term11 n m d q d') = (term11 n m d q d').
Proof. exact (eq_refl (term11 n m d q d')). Qed.
Lemma lem1248356 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term12 m d n q d') = (term13 m d d' n q).
Proof. exact (MK_COMB (@lem1248355 n m d q d') (@lem1248354 d d' n q)). Qed.
Lemma lem1248357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1248358 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term14 m d n q d') = (term15 m d d' n q).
Proof. exact (MK_COMB (@lem1248357) (@lem1248356 m d d' n q)). Qed.
Lemma lem1248359 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term16 m d n q d') = (term17 m d d' n q).
Proof. exact (MK_COMB (@lem1248358 m d d' n q) (@lem1248353 m d d' n q)). Qed.
Lemma lem1248360 (m : nat) (d : nat) (n : nat) (q : nat) : (term18 m d n q) = (term19 m d n q).
Proof. exact (fun_ext (fun d' : nat => @lem1248359 m d d' n q)). Qed.
Lemma lem1248361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1248362 (m : nat) (d : nat) (n : nat) (q : nat) : (term4 m d n q) = (term20 m d n q).
Proof. exact (MK_COMB (@lem1248361) (@lem1248360 m d n q)). Qed.
Lemma lem1248363 (m : nat) (d : nat) (n : nat) (q : nat) : (term3 n m d q) = (term21 m d n q).
Proof. exact (eq_refl (term3 n m d q)). Qed.
Lemma lem1248364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248365 (m : nat) (d : nat) (n : nat) (q : nat) : (term22 n m d q) = (term23 m d n q).
Proof. exact (MK_COMB (@lem1248364) (@lem1248363 m d n q)). Qed.
Lemma lem1248366 (m : nat) (d : nat) (n : nat) (q : nat) : ((term3 n m d q) = (term4 m d n q)) = ((term21 m d n q) = (term20 m d n q)).
Proof. exact (MK_COMB (@lem1248365 m d n q) (@lem1248362 m d n q)). Qed.
Lemma lem1248367 (m : nat) (d : nat) (n : nat) (q : nat) : (term21 m d n q) = (term20 m d n q).
Proof. exact (EQ_MP (@lem1248366 m d n q) (@lem1248350 m d n q)). Qed.
Lemma lem1248368 (m : nat) (d : nat) (n : nat) (q : nat) : (term20 m d n q) = (term21 m d n q).
Proof. exact (SYM (@lem1248367 m d n q)). Qed.
