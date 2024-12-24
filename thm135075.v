Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm135075_term_abbrevs.
Require Import thm134805_spec.
Require Import thm135024_spec.
Lemma lem135025 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem135026 : term1.
Proof. exact (EQ_MP (@lem135025) (@lem134805)). Qed.
Lemma lem135027 : term2.
Proof. exact (@lem135026 term3). Qed.
Lemma lem135028 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem135029 : term4.
Proof. exact (EQ_MP (@lem135028) (@lem135027)). Qed.
Lemma lem135030 (h1 : Nat.sub = term5) : Nat.sub = term5.
Proof. exact (h1). Qed.
Lemma lem135031 (h1 : Nat.sub = term5) : term5 = Nat.sub.
Proof. exact (SYM (@lem135030 h1)). Qed.
Lemma lem135032 (h1 : term5 = Nat.sub) : term5 = Nat.sub.
Proof. exact (h1). Qed.
Lemma lem135033 (h1 : term5 = Nat.sub) : Nat.sub = term5.
Proof. exact (SYM (@lem135032 h1)). Qed.
Lemma lem135034 : (Nat.sub = term5) = (term5 = Nat.sub).
Proof. exact (prop_ext (fun h1 : Nat.sub = term5 => @lem135031 h1) (fun h1 : term5 = Nat.sub => @lem135033 h1)). Qed.
Lemma lem135037 : term5 = Nat.sub.
Proof. exact (EQ_MP (@lem135034) (@lem135024)). Qed.
Lemma lem135038 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135039 (m : nat) : (term6 m) = (Nat.sub m).
Proof. exact (MK_COMB (@lem135037) (@lem135038 m)). Qed.
Lemma lem135040 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem135041 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem135039 m) (@lem135040)). Qed.
Lemma lem135042 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135043 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem135042) (@lem135041 m)). Qed.
Lemma lem135044 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135045 (m : nat) : ((term7 m) = m) = ((term8 m) = m).
Proof. exact (MK_COMB (@lem135043 m) (@lem135044 m)). Qed.
Lemma lem135046 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem135045 m)). Qed.
Lemma lem135047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135048 : term13 = term14.
Proof. exact (MK_COMB (@lem135047) (@lem135046)). Qed.
Lemma lem135049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135050 : term15 = term16.
Proof. exact (MK_COMB (@lem135049) (@lem135048)). Qed.
Lemma lem135052 : term5 = Nat.sub.
Proof. exact (EQ_MP (@lem135034) (@lem135024)). Qed.
Lemma lem135053 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135054 (m : nat) : (term6 m) = (Nat.sub m).
Proof. exact (MK_COMB (@lem135052) (@lem135053 m)). Qed.
Lemma lem135055 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem135056 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem135054 m) (@lem135055 n)). Qed.
Lemma lem135057 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135058 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem135057) (@lem135056 m n)). Qed.
Lemma lem135060 : term5 = Nat.sub.
Proof. exact (EQ_MP (@lem135034) (@lem135024)). Qed.
Lemma lem135061 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135062 (m : nat) : (term6 m) = (Nat.sub m).
Proof. exact (MK_COMB (@lem135060) (@lem135061 m)). Qed.
Lemma lem135063 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem135064 (m : nat) (n : nat) : (term21 m n) = (Nat.sub m n).
Proof. exact (MK_COMB (@lem135062 m) (@lem135063 n)). Qed.
Lemma lem135065 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem135066 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem135065) (@lem135064 m n)). Qed.
Lemma lem135067 (m : nat) (n : nat) : ((term17 m n) = (term22 m n)) = ((term18 m n) = (term23 m n)).
Proof. exact (MK_COMB (@lem135058 m n) (@lem135066 m n)). Qed.
Lemma lem135068 (m : nat) : (term24 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem135067 m n)). Qed.
Lemma lem135069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135070 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem135069) (@lem135068 m)). Qed.
Lemma lem135071 : term28 = term29.
Proof. exact (fun_ext (fun m : nat => @lem135070 m)). Qed.
Lemma lem135072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135073 : term30 = term31.
Proof. exact (MK_COMB (@lem135072) (@lem135071)). Qed.
Lemma lem135074 : term4 = term32.
Proof. exact (MK_COMB (@lem135050) (@lem135073)). Qed.
Lemma lem135075 : term32.
Proof. exact (EQ_MP (@lem135074) (@lem135029)). Qed.
