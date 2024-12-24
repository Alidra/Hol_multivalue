Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_ADD_RCANCEL_0_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Lemma lem79891 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem79892 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem79893 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem79892 m) (@lem79891 m)). Qed.
Lemma lem79894 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem79893 m n). Qed.
Lemma lem79895 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem79910 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem79895 n m) (@lem79894 m n)). Qed.
Lemma lem79911 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem79912 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (MK_COMB (@lem79911) (@lem79910 n m)). Qed.
Lemma lem79913 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem79914 (m : nat) (n : nat) : ((Nat.add m n) = n) = ((Nat.add n m) = n).
Proof. exact (MK_COMB (@lem79912 n m) (@lem79913 n)). Qed.
Lemma lem79915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem79916 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem79915) (@lem79914 m n)). Qed.
Lemma lem79919 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem79920 (n : nat) (m : nat) : (((Nat.add m n) = n) = (m = (NUMERAL 0))) = (((Nat.add n m) = n) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem79916 m n) (@lem79919 m)). Qed.
Lemma lem79921 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem79920 n m)). Qed.
Lemma lem79922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79923 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem79922) (@lem79921 m)). Qed.
Lemma lem79924 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem79923 m)). Qed.
Lemma lem79925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem79926 : term12 = term13.
Proof. exact (MK_COMB (@lem79925) (@lem79924)). Qed.
Lemma lem79927 : term13 = term12.
Proof. exact (SYM (@lem79926)). Qed.
Lemma lem79928 (m : nat) : term14 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem79929 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem79930 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem79929 m) (@lem79928 m)). Qed.
Lemma lem79931 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem79930 m n). Qed.
Lemma lem79932 (m : nat) (n : nat) : (term16 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem79935 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem79932 m n) (@lem79931 m n)). Qed.
Lemma lem79936 (n : nat) (m : nat) : ((Nat.add n m) = n) = (m = (NUMERAL 0)).
Proof. exact (@lem79935 n m). Qed.
Lemma lem79941 (m : nat) : term9 m.
Proof. exact (fun n : nat => @lem79936 n m). Qed.
Lemma lem79946 : term13.
Proof. exact (fun m : nat => @lem79941 m). Qed.
Lemma lem79947 : term12.
Proof. exact (EQ_MP (@lem79927) (@lem79946)). Qed.
