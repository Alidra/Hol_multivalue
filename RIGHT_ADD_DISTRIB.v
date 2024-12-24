Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_ADD_DISTRIB_term_abbrevs.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_SYM_spec.
Lemma lem82056 (m : nat) : term0 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem82057 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem82058 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem82057 m) (@lem82056 m)). Qed.
Lemma lem82059 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem82058 m n). Qed.
Lemma lem82060 (n : nat) (m : nat) : (term2 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem82077 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem82060 n m) (@lem82059 m n)). Qed.
Lemma lem82078 (p : nat) (m : nat) (n : nat) : (term3 m n p) = (term4 p m n).
Proof. exact (@lem82077 p (Nat.add m n)). Qed.
Lemma lem82079 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem82080 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (term6 p m n).
Proof. exact (MK_COMB (@lem82079) (@lem82078 p m n)). Qed.
Lemma lem82082 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem82060 n m) (@lem82059 m n)). Qed.
Lemma lem82083 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem82082 p m). Qed.
Lemma lem82084 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem82085 (p : nat) (m : nat) : (term7 m p) = (term7 p m).
Proof. exact (MK_COMB (@lem82084) (@lem82083 p m)). Qed.
Lemma lem82087 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem82060 n m) (@lem82059 m n)). Qed.
Lemma lem82088 (p : nat) (n : nat) : (Nat.mul n p) = (Nat.mul p n).
Proof. exact (@lem82087 p n). Qed.
Lemma lem82089 (m : nat) (p : nat) (n : nat) : (term8 m n p) = (term9 m p n).
Proof. exact (MK_COMB (@lem82085 p m) (@lem82088 p n)). Qed.
Lemma lem82090 (m : nat) (p : nat) (n : nat) : ((term3 m n p) = (term8 m n p)) = ((term4 p m n) = (term9 m p n)).
Proof. exact (MK_COMB (@lem82080 p m n) (@lem82089 m p n)). Qed.
Lemma lem82091 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (fun_ext (fun p : nat => @lem82090 m p n)). Qed.
Lemma lem82092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82093 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem82092) (@lem82091 m n)). Qed.
Lemma lem82094 (m : nat) : (term14 m) = (term15 m).
Proof. exact (fun_ext (fun n : nat => @lem82093 m n)). Qed.
Lemma lem82095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82096 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem82095) (@lem82094 m)). Qed.
Lemma lem82097 : term18 = term19.
Proof. exact (fun_ext (fun m : nat => @lem82096 m)). Qed.
Lemma lem82098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem82099 : term20 = term21.
Proof. exact (MK_COMB (@lem82098) (@lem82097)). Qed.
Lemma lem82100 : term21 = term20.
Proof. exact (SYM (@lem82099)). Qed.
Lemma lem82101 (m : nat) : term22 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem82102 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem82103 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem82102 m) (@lem82101 m)). Qed.
Lemma lem82104 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem82103 m n). Qed.
Lemma lem82105 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem82106 (n : nat) (m : nat) : term25 n m.
Proof. exact (EQ_MP (@lem82105 n m) (@lem82104 m n)). Qed.
Lemma lem82107 (n : nat) (m : nat) (p : nat) : term26 n m p.
Proof. exact (@lem82106 n m p). Qed.
Lemma lem82108 (n : nat) (m : nat) (p : nat) : (term26 n m p) = ((term4 m n p) = (term9 n m p)).
Proof. exact (eq_refl (term26 n m p)). Qed.
Lemma lem82111 (n : nat) (m : nat) (p : nat) : (term4 m n p) = (term9 n m p).
Proof. exact (EQ_MP (@lem82108 n m p) (@lem82107 n m p)). Qed.
Lemma lem82112 (m : nat) (p : nat) (n : nat) : (term4 p m n) = (term9 m p n).
Proof. exact (@lem82111 m p n). Qed.
Lemma lem82117 (m : nat) (n : nat) : term13 m n.
Proof. exact (fun p : nat => @lem82112 m p n). Qed.
Lemma lem82122 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem82117 m n). Qed.
Lemma lem82127 : term21.
Proof. exact (fun m : nat => @lem82122 m). Qed.
Lemma lem82128 : term20.
Proof. exact (EQ_MP (@lem82100) (@lem82127)). Qed.
