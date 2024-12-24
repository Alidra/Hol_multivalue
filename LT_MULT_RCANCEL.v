Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_MULT_RCANCEL_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import LT_MULT_LCANCEL_spec.
Require Import MULT_SYM_spec.
Lemma lem105883 (t1 : Prop) : term0 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem105884 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem105885 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem105884 t1) (@lem105883 t1)). Qed.
Lemma lem105886 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem105885 t1 t2). Qed.
Lemma lem105887 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem105889 (m : nat) : term3 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem105890 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem105891 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem105890 m) (@lem105889 m)). Qed.
Lemma lem105892 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem105891 m n). Qed.
Lemma lem105893 (n : nat) (m : nat) : (term5 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem105910 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem105893 n m) (@lem105892 m n)). Qed.
Lemma lem105911 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem105910 p m). Qed.
Lemma lem105912 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105913 (p : nat) (m : nat) : (term6 m p) = (term6 p m).
Proof. exact (MK_COMB (@lem105912) (@lem105911 p m)). Qed.
Lemma lem105915 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem105893 n m) (@lem105892 m n)). Qed.
Lemma lem105916 (p : nat) (n : nat) : (Nat.mul n p) = (Nat.mul p n).
Proof. exact (@lem105915 p n). Qed.
Lemma lem105917 (m : nat) (p : nat) (n : nat) : (term7 m n p) = (term8 m p n).
Proof. exact (MK_COMB (@lem105913 p m) (@lem105916 p n)). Qed.
Lemma lem105918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105919 (m : nat) (p : nat) (n : nat) : (term9 m n p) = (term10 m p n).
Proof. exact (MK_COMB (@lem105918) (@lem105917 m p n)). Qed.
Lemma lem105923 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem105887 t2 t1) (@lem105886 t1 t2)). Qed.
Lemma lem105924 (p : nat) (m : nat) (n : nat) : (term11 m n p) = (term12 p m n).
Proof. exact (@lem105923 (term13 p) (Peano.lt m n)). Qed.
Lemma lem105925 (p : nat) (m : nat) (n : nat) : ((term7 m n p) = (term11 m n p)) = ((term8 m p n) = (term12 p m n)).
Proof. exact (MK_COMB (@lem105919 m p n) (@lem105924 p m n)). Qed.
Lemma lem105926 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (fun_ext (fun p : nat => @lem105925 p m n)). Qed.
Lemma lem105927 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem105928 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem105927) (@lem105926 m n)). Qed.
Lemma lem105929 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem105928 m n)). Qed.
Lemma lem105930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem105931 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem105930) (@lem105929 m)). Qed.
Lemma lem105932 : term22 = term23.
Proof. exact (fun_ext (fun m : nat => @lem105931 m)). Qed.
Lemma lem105933 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem105934 : term24 = term25.
Proof. exact (MK_COMB (@lem105933) (@lem105932)). Qed.
Lemma lem105935 : term25 = term24.
Proof. exact (SYM (@lem105934)). Qed.
Lemma lem105936 (m : nat) : term26 m.
Proof. exact (@lem105882 m). Qed.
Lemma lem105937 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem105938 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem105937 m) (@lem105936 m)). Qed.
Lemma lem105939 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem105938 m n). Qed.
Lemma lem105940 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem105941 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem105940 m n) (@lem105939 m n)). Qed.
Lemma lem105942 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem105941 m n p). Qed.
Lemma lem105943 (m : nat) (n : nat) (p : nat) : (term30 m n p) = ((term8 n m p) = (term12 m n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem105946 (m : nat) (n : nat) (p : nat) : (term8 n m p) = (term12 m n p).
Proof. exact (EQ_MP (@lem105943 m n p) (@lem105942 m n p)). Qed.
Lemma lem105947 (p : nat) (m : nat) (n : nat) : (term8 m p n) = (term12 p m n).
Proof. exact (@lem105946 p m n). Qed.
Lemma lem105952 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun p : nat => @lem105947 p m n). Qed.
Lemma lem105957 (m : nat) : term21 m.
Proof. exact (fun n : nat => @lem105952 m n). Qed.
Lemma lem105962 : term25.
Proof. exact (fun m : nat => @lem105957 m). Qed.
Lemma lem105963 : term24.
Proof. exact (EQ_MP (@lem105935) (@lem105962)). Qed.
