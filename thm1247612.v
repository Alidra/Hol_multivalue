Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247612_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247593 (_22840 : nat) (_22841 : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term0 m p n q _22841 _22840) = (term1 _22840 _22841 m p n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 m p n q)). Qed.
Lemma lem1247594 (m : nat) (p : nat) (n : nat) (q : nat) : (term3 m n p q) = (term4 m p n q).
Proof. exact (@lem1247593 (Nat.add p q) (Nat.add m n) m p n q). Qed.
Lemma lem1247595 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term5 m p n q d) = (term6 d m p n q).
Proof. exact (eq_refl (term5 m p n q d)). Qed.
Lemma lem1247596 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term7 p q m n d) = (term7 p q m n d).
Proof. exact (eq_refl (term7 p q m n d)). Qed.
Lemma lem1247597 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term8 m p n q d) = (term9 d m p n q).
Proof. exact (MK_COMB (@lem1247596 p q m n d) (@lem1247595 d m p n q)). Qed.
Lemma lem1247598 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term5 m p n q d) = (term6 d m p n q).
Proof. exact (eq_refl (term5 m p n q d)). Qed.
Lemma lem1247599 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term7 m n p q d) = (term7 m n p q d).
Proof. exact (eq_refl (term7 m n p q d)). Qed.
Lemma lem1247600 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term10 m p n q d) = (term11 d m p n q).
Proof. exact (MK_COMB (@lem1247599 m n p q d) (@lem1247598 d m p n q)). Qed.
Lemma lem1247601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247602 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term12 m p n q d) = (term13 d m p n q).
Proof. exact (MK_COMB (@lem1247601) (@lem1247600 d m p n q)). Qed.
Lemma lem1247603 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term14 m p n q d) = (term15 d m p n q).
Proof. exact (MK_COMB (@lem1247602 d m p n q) (@lem1247597 d m p n q)). Qed.
Lemma lem1247604 (m : nat) (p : nat) (n : nat) (q : nat) : (term16 m p n q) = (term17 m p n q).
Proof. exact (fun_ext (fun d : nat => @lem1247603 d m p n q)). Qed.
Lemma lem1247605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247606 (m : nat) (p : nat) (n : nat) (q : nat) : (term4 m p n q) = (term18 m p n q).
Proof. exact (MK_COMB (@lem1247605) (@lem1247604 m p n q)). Qed.
Lemma lem1247607 (m : nat) (p : nat) (n : nat) (q : nat) : (term3 m n p q) = (term19 m p n q).
Proof. exact (eq_refl (term3 m n p q)). Qed.
Lemma lem1247608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247609 (m : nat) (p : nat) (n : nat) (q : nat) : (term20 m n p q) = (term21 m p n q).
Proof. exact (MK_COMB (@lem1247608) (@lem1247607 m p n q)). Qed.
Lemma lem1247610 (m : nat) (p : nat) (n : nat) (q : nat) : ((term3 m n p q) = (term4 m p n q)) = ((term19 m p n q) = (term18 m p n q)).
Proof. exact (MK_COMB (@lem1247609 m p n q) (@lem1247606 m p n q)). Qed.
Lemma lem1247611 (m : nat) (p : nat) (n : nat) (q : nat) : (term19 m p n q) = (term18 m p n q).
Proof. exact (EQ_MP (@lem1247610 m p n q) (@lem1247594 m p n q)). Qed.
Lemma lem1247612 (m : nat) (p : nat) (n : nat) (q : nat) : (term18 m p n q) = (term19 m p n q).
Proof. exact (SYM (@lem1247611 m p n q)). Qed.
