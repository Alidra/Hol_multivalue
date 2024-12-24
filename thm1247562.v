Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247562_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247543 (_22840 : nat) (_22841 : nat) (d : nat) (d' : nat) : (term0 d d' _22841 _22840) = (term1 _22840 _22841 d d').
Proof. exact (@lem1246844 _22840 _22841 (term2 d d')). Qed.
Lemma lem1247544 (m : nat) (d : nat) (d' : nat) : (term3 d' m d) = (term4 m d d').
Proof. exact (@lem1247543 (Nat.add m d) (Nat.add m d') d d'). Qed.
Lemma lem1247545 (d : nat) (d' : nat) (d'' : nat) : (term5 d d' d'') = (term6 d d' d'').
Proof. exact (eq_refl (term5 d d' d'')). Qed.
Lemma lem1247546 (d : nat) (m : nat) (d' : nat) (d'' : nat) : (term7 d m d' d'') = (term7 d m d' d'').
Proof. exact (eq_refl (term7 d m d' d'')). Qed.
Lemma lem1247547 (m : nat) (d : nat) (d' : nat) (d'' : nat) : (term8 m d d' d'') = (term9 m d d' d'').
Proof. exact (MK_COMB (@lem1247546 d m d' d'') (@lem1247545 d d' d'')). Qed.
Lemma lem1247548 (d : nat) (d' : nat) (d'' : nat) : (term5 d d' d'') = (term6 d d' d'').
Proof. exact (eq_refl (term5 d d' d'')). Qed.
Lemma lem1247549 (d' : nat) (m : nat) (d : nat) (d'' : nat) : (term7 d' m d d'') = (term7 d' m d d'').
Proof. exact (eq_refl (term7 d' m d d'')). Qed.
Lemma lem1247550 (m : nat) (d : nat) (d' : nat) (d'' : nat) : (term10 m d d' d'') = (term11 m d d' d'').
Proof. exact (MK_COMB (@lem1247549 d' m d d'') (@lem1247548 d d' d'')). Qed.
Lemma lem1247551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247552 (m : nat) (d : nat) (d' : nat) (d'' : nat) : (term12 m d d' d'') = (term13 m d d' d'').
Proof. exact (MK_COMB (@lem1247551) (@lem1247550 m d d' d'')). Qed.
Lemma lem1247553 (m : nat) (d : nat) (d' : nat) (d'' : nat) : (term14 m d d' d'') = (term15 m d d' d'').
Proof. exact (MK_COMB (@lem1247552 m d d' d'') (@lem1247547 m d d' d'')). Qed.
Lemma lem1247554 (m : nat) (d : nat) (d' : nat) : (term16 m d d') = (term17 m d d').
Proof. exact (fun_ext (fun d'' : nat => @lem1247553 m d d' d'')). Qed.
Lemma lem1247555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247556 (m : nat) (d : nat) (d' : nat) : (term4 m d d') = (term18 m d d').
Proof. exact (MK_COMB (@lem1247555) (@lem1247554 m d d')). Qed.
Lemma lem1247557 (d' : nat) (m : nat) (d : nat) : (term3 d' m d) = (term19 d' m d).
Proof. exact (eq_refl (term3 d' m d)). Qed.
Lemma lem1247558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247559 (d' : nat) (m : nat) (d : nat) : (term20 d' m d) = (term21 d' m d).
Proof. exact (MK_COMB (@lem1247558) (@lem1247557 d' m d)). Qed.
Lemma lem1247560 (m : nat) (d : nat) (d' : nat) : ((term3 d' m d) = (term4 m d d')) = ((term19 d' m d) = (term18 m d d')).
Proof. exact (MK_COMB (@lem1247559 d' m d) (@lem1247556 m d d')). Qed.
Lemma lem1247561 (m : nat) (d : nat) (d' : nat) : (term19 d' m d) = (term18 m d d').
Proof. exact (EQ_MP (@lem1247560 m d d') (@lem1247544 m d d')). Qed.
Lemma lem1247562 (d' : nat) (m : nat) (d : nat) : (term18 m d d') = (term19 d' m d).
Proof. exact (SYM (@lem1247561 m d d')). Qed.
