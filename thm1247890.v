Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247890_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247871 (_22840 : nat) (_22841 : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q _22841 _22840) = (term1 _22840 _22841 d n q).
Proof. exact (@lem1246844 _22840 _22841 (term2 d n q)). Qed.
Lemma lem1247872 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term0 d n q m p) = (term1 p m d n q).
Proof. exact (@lem1247871 p m d n q). Qed.
Lemma lem1247873 (d : nat) (d' : nat) (n : nat) (q : nat) : (term3 d n q d') = (term4 d d' n q).
Proof. exact (eq_refl (term3 d n q d')). Qed.
Lemma lem1247874 (p : nat) (m : nat) (d' : nat) : (term5 p m d') = (term5 p m d').
Proof. exact (eq_refl (term5 p m d')). Qed.
Lemma lem1247875 (p : nat) (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 p m d n q d') = (term7 p m d d' n q).
Proof. exact (MK_COMB (@lem1247874 p m d') (@lem1247873 d d' n q)). Qed.
Lemma lem1247876 (d : nat) (d' : nat) (n : nat) (q : nat) : (term3 d n q d') = (term4 d d' n q).
Proof. exact (eq_refl (term3 d n q d')). Qed.
Lemma lem1247877 (m : nat) (p : nat) (d' : nat) : (term5 m p d') = (term5 m p d').
Proof. exact (eq_refl (term5 m p d')). Qed.
Lemma lem1247878 (m : nat) (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term6 m p d n q d') = (term7 m p d d' n q).
Proof. exact (MK_COMB (@lem1247877 m p d') (@lem1247876 d d' n q)). Qed.
Lemma lem1247879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247880 (m : nat) (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term8 m p d n q d') = (term9 m p d d' n q).
Proof. exact (MK_COMB (@lem1247879) (@lem1247878 m p d d' n q)). Qed.
Lemma lem1247881 (p : nat) (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : (term10 p m d n q d') = (term11 p m d d' n q).
Proof. exact (MK_COMB (@lem1247880 m p d d' n q) (@lem1247875 p m d d' n q)). Qed.
Lemma lem1247882 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term12 p m d n q) = (term13 p m d n q).
Proof. exact (fun_ext (fun d' : nat => @lem1247881 p m d d' n q)). Qed.
Lemma lem1247883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247884 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term1 p m d n q) = (term14 p m d n q).
Proof. exact (MK_COMB (@lem1247883) (@lem1247882 p m d n q)). Qed.
Lemma lem1247885 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term0 d n q m p) = (term15 d m p n q).
Proof. exact (eq_refl (term0 d n q m p)). Qed.
Lemma lem1247886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247887 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term16 d n q m p) = (term17 d m p n q).
Proof. exact (MK_COMB (@lem1247886) (@lem1247885 d m p n q)). Qed.
Lemma lem1247888 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : ((term0 d n q m p) = (term1 p m d n q)) = ((term15 d m p n q) = (term14 p m d n q)).
Proof. exact (MK_COMB (@lem1247887 d m p n q) (@lem1247884 p m d n q)). Qed.
Lemma lem1247889 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : (term15 d m p n q) = (term14 p m d n q).
Proof. exact (EQ_MP (@lem1247888 p m d n q) (@lem1247872 p m d n q)). Qed.
Lemma lem1247890 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term14 p m d n q) = (term15 d m p n q).
Proof. exact (SYM (@lem1247889 p m d n q)). Qed.
