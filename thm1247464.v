Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247464_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247445 (_22840 : nat) (_22841 : nat) (n : nat) (m : nat) (d : nat) : (term0 n m d _22841 _22840) = (term1 _22840 _22841 n m d).
Proof. exact (@lem1246844 _22840 _22841 (term2 n m d)). Qed.
Lemma lem1247446 (n : nat) (m : nat) (d : nat) : (term3 d m n) = (term4 n m d).
Proof. exact (@lem1247445 n m n m d). Qed.
Lemma lem1247447 (d' : nat) (n : nat) (m : nat) (d : nat) : (term5 n m d d') = (term6 d' n m d).
Proof. exact (eq_refl (term5 n m d d')). Qed.
Lemma lem1247448 (n : nat) (m : nat) (d' : nat) : (term7 n m d') = (term7 n m d').
Proof. exact (eq_refl (term7 n m d')). Qed.
Lemma lem1247449 (d' : nat) (n : nat) (m : nat) (d : nat) : (term8 n m d d') = (term9 d' n m d).
Proof. exact (MK_COMB (@lem1247448 n m d') (@lem1247447 d' n m d)). Qed.
Lemma lem1247450 (d' : nat) (n : nat) (m : nat) (d : nat) : (term5 n m d d') = (term6 d' n m d).
Proof. exact (eq_refl (term5 n m d d')). Qed.
Lemma lem1247451 (m : nat) (n : nat) (d' : nat) : (term7 m n d') = (term7 m n d').
Proof. exact (eq_refl (term7 m n d')). Qed.
Lemma lem1247452 (d' : nat) (n : nat) (m : nat) (d : nat) : (term10 n m d d') = (term11 d' n m d).
Proof. exact (MK_COMB (@lem1247451 m n d') (@lem1247450 d' n m d)). Qed.
Lemma lem1247453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247454 (d' : nat) (n : nat) (m : nat) (d : nat) : (term12 n m d d') = (term13 d' n m d).
Proof. exact (MK_COMB (@lem1247453) (@lem1247452 d' n m d)). Qed.
Lemma lem1247455 (d' : nat) (n : nat) (m : nat) (d : nat) : (term14 n m d d') = (term15 d' n m d).
Proof. exact (MK_COMB (@lem1247454 d' n m d) (@lem1247449 d' n m d)). Qed.
Lemma lem1247456 (n : nat) (m : nat) (d : nat) : (term16 n m d) = (term17 n m d).
Proof. exact (fun_ext (fun d' : nat => @lem1247455 d' n m d)). Qed.
Lemma lem1247457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247458 (n : nat) (m : nat) (d : nat) : (term4 n m d) = (term18 n m d).
Proof. exact (MK_COMB (@lem1247457) (@lem1247456 n m d)). Qed.
Lemma lem1247459 (n : nat) (m : nat) (d : nat) : (term3 d m n) = (term19 n m d).
Proof. exact (eq_refl (term3 d m n)). Qed.
Lemma lem1247460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247461 (n : nat) (m : nat) (d : nat) : (term20 d m n) = (term21 n m d).
Proof. exact (MK_COMB (@lem1247460) (@lem1247459 n m d)). Qed.
Lemma lem1247462 (n : nat) (m : nat) (d : nat) : ((term3 d m n) = (term4 n m d)) = ((term19 n m d) = (term18 n m d)).
Proof. exact (MK_COMB (@lem1247461 n m d) (@lem1247458 n m d)). Qed.
Lemma lem1247463 (n : nat) (m : nat) (d : nat) : (term19 n m d) = (term18 n m d).
Proof. exact (EQ_MP (@lem1247462 n m d) (@lem1247446 n m d)). Qed.
Lemma lem1247464 (n : nat) (m : nat) (d : nat) : (term18 n m d) = (term19 n m d).
Proof. exact (SYM (@lem1247463 n m d)). Qed.
