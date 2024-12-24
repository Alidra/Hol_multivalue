Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247662_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247643 (_22840 : nat) (_22841 : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q _22841 _22840) = (term1 _22840 _22841 d n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 d n q)). Qed.
Lemma lem1247644 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q m p) = (term1 p m d n q).
Proof. exact (@lem1247643 p m d n q). Qed.
Lemma lem1247645 (d : nat) (d' : nat) (n : nat) (q : nat) : (term3 d n q d') = (term4 d d' n q).
Proof. exact (eq_refl (term3 d n q d')). Qed.
Lemma lem1247646 (p : nat) (m : nat) (d' : nat) : (term5 p m d') = (term5 p m d').
Proof. exact (eq_refl (term5 p m d')). Qed.
Lemma lem1247647 (p : nat) (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 p m d n q d') = (term7 p m d d' n q).
Proof. exact (MK_COMB (@lem1247646 p m d') (@lem1247645 d d' n q)). Qed.
Lemma lem1247648 (d : nat) (d' : nat) (n : nat) (q : nat) : (term3 d n q d') = (term4 d d' n q).
Proof. exact (eq_refl (term3 d n q d')). Qed.
Lemma lem1247649 (m : nat) (p : nat) (d' : nat) : (term5 m p d') = (term5 m p d').
Proof. exact (eq_refl (term5 m p d')). Qed.
Lemma lem1247650 (m : nat) (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 m p d n q d') = (term7 m p d d' n q).
Proof. exact (MK_COMB (@lem1247649 m p d') (@lem1247648 d d' n q)). Qed.
Lemma lem1247651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247652 (m : nat) (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term8 m p d n q d') = (term9 m p d d' n q).
Proof. exact (MK_COMB (@lem1247651) (@lem1247650 m p d d' n q)). Qed.
Lemma lem1247653 (p : nat) (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term10 p m d n q d') = (term11 p m d d' n q).
Proof. exact (MK_COMB (@lem1247652 m p d d' n q) (@lem1247647 p m d d' n q)). Qed.
Lemma lem1247654 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term12 p m d n q) = (term13 p m d n q).
Proof. exact (fun_ext (fun d' : nat => @lem1247653 p m d d' n q)). Qed.
Lemma lem1247655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247656 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term1 p m d n q) = (term14 p m d n q).
Proof. exact (MK_COMB (@lem1247655) (@lem1247654 p m d n q)). Qed.
Lemma lem1247657 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term0 d n q m p) = (term15 d m p n q).
Proof. exact (eq_refl (term0 d n q m p)). Qed.
Lemma lem1247658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247659 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term16 d n q m p) = (term17 d m p n q).
Proof. exact (MK_COMB (@lem1247658) (@lem1247657 d m p n q)). Qed.
Lemma lem1247660 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : ((term0 d n q m p) = (term1 p m d n q)) = ((term15 d m p n q) = (term14 p m d n q)).
Proof. exact (MK_COMB (@lem1247659 d m p n q) (@lem1247656 p m d n q)). Qed.
Lemma lem1247661 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term15 d m p n q) = (term14 p m d n q).
Proof. exact (EQ_MP (@lem1247660 p m d n q) (@lem1247644 p m d n q)). Qed.
Lemma lem1247662 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term14 p m d n q) = (term15 d m p n q).
Proof. exact (SYM (@lem1247661 p m d n q)). Qed.
