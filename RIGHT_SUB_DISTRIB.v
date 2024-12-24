Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_SUB_DISTRIB_term_abbrevs.
Require Import LEFT_SUB_DISTRIB_spec.
Require Import MULT_SYM_spec.
Lemma lem137036 (m : nat) : term0 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem137037 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem137038 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem137037 m) (@lem137036 m)). Qed.
Lemma lem137039 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem137038 m n). Qed.
Lemma lem137040 (n : nat) (m : nat) : (term2 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem137057 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem137040 n m) (@lem137039 m n)). Qed.
Lemma lem137058 (p : nat) (m : nat) (n : nat) : (term3 m n p) = (term4 p m n).
Proof. exact (@lem137057 p (Nat.sub m n)). Qed.
Lemma lem137059 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem137060 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (term6 p m n).
Proof. exact (MK_COMB (@lem137059) (@lem137058 p m n)). Qed.
Lemma lem137062 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem137040 n m) (@lem137039 m n)). Qed.
Lemma lem137063 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem137062 p m). Qed.
Lemma lem137064 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem137065 (p : nat) (m : nat) : (term7 m p) = (term7 p m).
Proof. exact (MK_COMB (@lem137064) (@lem137063 p m)). Qed.
Lemma lem137067 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem137040 n m) (@lem137039 m n)). Qed.
Lemma lem137068 (p : nat) (n : nat) : (Nat.mul n p) = (Nat.mul p n).
Proof. exact (@lem137067 p n). Qed.
Lemma lem137069 (m : nat) (p : nat) (n : nat) : (term8 m n p) = (term9 m p n).
Proof. exact (MK_COMB (@lem137065 p m) (@lem137068 p n)). Qed.
Lemma lem137070 (m : nat) (p : nat) (n : nat) : ((term3 m n p) = (term8 m n p)) = ((term4 p m n) = (term9 m p n)).
Proof. exact (MK_COMB (@lem137060 p m n) (@lem137069 m p n)). Qed.
Lemma lem137071 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (fun_ext (fun p : nat => @lem137070 m p n)). Qed.
Lemma lem137072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137073 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem137072) (@lem137071 m n)). Qed.
Lemma lem137074 (m : nat) : (term14 m) = (term15 m).
Proof. exact (fun_ext (fun n : nat => @lem137073 m n)). Qed.
Lemma lem137075 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137076 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem137075) (@lem137074 m)). Qed.
Lemma lem137077 : term18 = term19.
Proof. exact (fun_ext (fun m : nat => @lem137076 m)). Qed.
Lemma lem137078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137079 : term20 = term21.
Proof. exact (MK_COMB (@lem137078) (@lem137077)). Qed.
Lemma lem137080 : term21 = term20.
Proof. exact (SYM (@lem137079)). Qed.
Lemma lem137081 (m : nat) : term22 m.
Proof. exact (@lem137035 m). Qed.
Lemma lem137082 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem137083 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem137082 m) (@lem137081 m)). Qed.
Lemma lem137084 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem137083 m n). Qed.
Lemma lem137085 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem137086 (n : nat) (m : nat) : term25 n m.
Proof. exact (EQ_MP (@lem137085 n m) (@lem137084 m n)). Qed.
Lemma lem137087 (n : nat) (m : nat) (p : nat) : term26 n m p.
Proof. exact (@lem137086 n m p). Qed.
Lemma lem137088 (n : nat) (m : nat) (p : nat) : (term26 n m p) = ((term4 m n p) = (term9 n m p)).
Proof. exact (eq_refl (term26 n m p)). Qed.
Lemma lem137091 (n : nat) (m : nat) (p : nat) : (term4 m n p) = (term9 n m p).
Proof. exact (EQ_MP (@lem137088 n m p) (@lem137087 n m p)). Qed.
Lemma lem137092 (m : nat) (p : nat) (n : nat) : (term4 p m n) = (term9 m p n).
Proof. exact (@lem137091 m p n). Qed.
Lemma lem137097 (m : nat) (n : nat) : term13 m n.
Proof. exact (fun p : nat => @lem137092 m p n). Qed.
Lemma lem137102 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem137097 m n). Qed.
Lemma lem137107 : term21.
Proof. exact (fun m : nat => @lem137102 m). Qed.
Lemma lem137108 : term20.
Proof. exact (EQ_MP (@lem137080) (@lem137107)). Qed.
