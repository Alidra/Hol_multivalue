Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248118_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1248099 (_22840 : nat) (_22841 : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term0 m p n q _22841 _22840) = (term1 _22840 _22841 m p n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 m p n q)). Qed.
Lemma lem1248100 (m : nat) (p : nat) (n : nat) (q : nat) : (term3 n q m p) = (term4 m p n q).
Proof. exact (@lem1248099 p m m p n q). Qed.
Lemma lem1248101 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term5 m p n q d) = (term6 d m p n q).
Proof. exact (eq_refl (term5 m p n q d)). Qed.
Lemma lem1248102 (p : nat) (m : nat) (d : nat) : (term7 p m d) = (term7 p m d).
Proof. exact (eq_refl (term7 p m d)). Qed.
Lemma lem1248103 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term8 m p n q d) = (term9 d m p n q).
Proof. exact (MK_COMB (@lem1248102 p m d) (@lem1248101 d m p n q)). Qed.
Lemma lem1248104 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term5 m p n q d) = (term6 d m p n q).
Proof. exact (eq_refl (term5 m p n q d)). Qed.
Lemma lem1248105 (m : nat) (p : nat) (d : nat) : (term7 m p d) = (term7 m p d).
Proof. exact (eq_refl (term7 m p d)). Qed.
Lemma lem1248106 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term10 m p n q d) = (term11 d m p n q).
Proof. exact (MK_COMB (@lem1248105 m p d) (@lem1248104 d m p n q)). Qed.
Lemma lem1248107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1248108 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term12 m p n q d) = (term13 d m p n q).
Proof. exact (MK_COMB (@lem1248107) (@lem1248106 d m p n q)). Qed.
Lemma lem1248109 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term14 m p n q d) = (term15 d m p n q).
Proof. exact (MK_COMB (@lem1248108 d m p n q) (@lem1248103 d m p n q)). Qed.
Lemma lem1248110 (m : nat) (p : nat) (n : nat) (q : nat) : (term16 m p n q) = (term17 m p n q).
Proof. exact (fun_ext (fun d : nat => @lem1248109 d m p n q)). Qed.
Lemma lem1248111 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1248112 (m : nat) (p : nat) (n : nat) (q : nat) : (term4 m p n q) = (term18 m p n q).
Proof. exact (MK_COMB (@lem1248111) (@lem1248110 m p n q)). Qed.
Lemma lem1248113 (m : nat) (p : nat) (n : nat) (q : nat) : (term3 n q m p) = (term19 m p n q).
Proof. exact (eq_refl (term3 n q m p)). Qed.
Lemma lem1248114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248115 (m : nat) (p : nat) (n : nat) (q : nat) : (term20 n q m p) = (term21 m p n q).
Proof. exact (MK_COMB (@lem1248114) (@lem1248113 m p n q)). Qed.
Lemma lem1248116 (m : nat) (p : nat) (n : nat) (q : nat) : ((term3 n q m p) = (term4 m p n q)) = ((term19 m p n q) = (term18 m p n q)).
Proof. exact (MK_COMB (@lem1248115 m p n q) (@lem1248112 m p n q)). Qed.
Lemma lem1248117 (m : nat) (p : nat) (n : nat) (q : nat) : (term19 m p n q) = (term18 m p n q).
Proof. exact (EQ_MP (@lem1248116 m p n q) (@lem1248100 m p n q)). Qed.
Lemma lem1248118 (m : nat) (p : nat) (n : nat) (q : nat) : (term18 m p n q) = (term19 m p n q).
Proof. exact (SYM (@lem1248117 m p n q)). Qed.
