Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_MULT_RCANCEL_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import MULT_SYM_spec.
Lemma lem84831 (t1 : Prop) : term0 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem84832 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem84833 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem84832 t1) (@lem84831 t1)). Qed.
Lemma lem84834 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem84833 t1 t2). Qed.
Lemma lem84835 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem84837 (m : nat) : term3 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem84838 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem84839 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem84838 m) (@lem84837 m)). Qed.
Lemma lem84840 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem84839 m n). Qed.
Lemma lem84841 (n : nat) (m : nat) : (term5 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem84860 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem84841 n m) (@lem84840 m n)). Qed.
Lemma lem84861 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem84860 p m). Qed.
Lemma lem84862 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84863 (p : nat) (m : nat) : (term6 m p) = (term6 p m).
Proof. exact (MK_COMB (@lem84862) (@lem84861 p m)). Qed.
Lemma lem84865 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem84841 n m) (@lem84840 m n)). Qed.
Lemma lem84866 (p : nat) (n : nat) : (Nat.mul n p) = (Nat.mul p n).
Proof. exact (@lem84865 p n). Qed.
Lemma lem84867 (m : nat) (p : nat) (n : nat) : ((Nat.mul m p) = (Nat.mul n p)) = ((Nat.mul p m) = (Nat.mul p n)).
Proof. exact (MK_COMB (@lem84863 p m) (@lem84866 p n)). Qed.
Lemma lem84868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem84869 (m : nat) (p : nat) (n : nat) : (term7 m n p) = (term8 m p n).
Proof. exact (MK_COMB (@lem84868) (@lem84867 m p n)). Qed.
Lemma lem84873 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem84835 t2 t1) (@lem84834 t1 t2)). Qed.
Lemma lem84874 (p : nat) (m : nat) (n : nat) : (term9 m n p) = (term10 p m n).
Proof. exact (@lem84873 (p = (NUMERAL 0)) (m = n)). Qed.
Lemma lem84875 (p : nat) (m : nat) (n : nat) : (((Nat.mul m p) = (Nat.mul n p)) = (term9 m n p)) = (((Nat.mul p m) = (Nat.mul p n)) = (term10 p m n)).
Proof. exact (MK_COMB (@lem84869 m p n) (@lem84874 p m n)). Qed.
Lemma lem84876 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (fun_ext (fun p : nat => @lem84875 p m n)). Qed.
Lemma lem84877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84878 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem84877) (@lem84876 m n)). Qed.
Lemma lem84879 (m : nat) : (term15 m) = (term16 m).
Proof. exact (fun_ext (fun n : nat => @lem84878 m n)). Qed.
Lemma lem84880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84881 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem84880) (@lem84879 m)). Qed.
Lemma lem84882 : term19 = term20.
Proof. exact (fun_ext (fun m : nat => @lem84881 m)). Qed.
Lemma lem84883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem84884 : term21 = term22.
Proof. exact (MK_COMB (@lem84883) (@lem84882)). Qed.
Lemma lem84885 : term22 = term21.
Proof. exact (SYM (@lem84884)). Qed.
Lemma lem84886 (m : nat) : term23 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem84887 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem84888 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem84887 m) (@lem84886 m)). Qed.
Lemma lem84889 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem84888 m n). Qed.
Lemma lem84890 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem84891 (m : nat) (n : nat) : term26 m n.
Proof. exact (EQ_MP (@lem84890 m n) (@lem84889 m n)). Qed.
Lemma lem84892 (m : nat) (n : nat) (p : nat) : term27 m n p.
Proof. exact (@lem84891 m n p). Qed.
Lemma lem84893 (m : nat) (n : nat) (p : nat) : (term27 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term10 m n p)).
Proof. exact (eq_refl (term27 m n p)). Qed.
Lemma lem84896 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term10 m n p).
Proof. exact (EQ_MP (@lem84893 m n p) (@lem84892 m n p)). Qed.
Lemma lem84897 (p : nat) (m : nat) (n : nat) : ((Nat.mul p m) = (Nat.mul p n)) = (term10 p m n).
Proof. exact (@lem84896 p m n). Qed.
Lemma lem84902 (m : nat) (n : nat) : term14 m n.
Proof. exact (fun p : nat => @lem84897 p m n). Qed.
Lemma lem84907 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem84902 m n). Qed.
Lemma lem84912 : term22.
Proof. exact (fun m : nat => @lem84907 m). Qed.
Lemma lem84913 : term21.
Proof. exact (EQ_MP (@lem84885) (@lem84912)). Qed.
