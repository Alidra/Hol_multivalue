Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm80977_term_abbrevs.
Require Import thm80749_spec.
Require Import thm80924_spec.
Lemma lem80925 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem80926 : term1.
Proof. exact (EQ_MP (@lem80925) (@lem80749)). Qed.
Lemma lem80927 : term2.
Proof. exact (@lem80926 term3). Qed.
Lemma lem80928 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem80929 : term4.
Proof. exact (EQ_MP (@lem80928) (@lem80927)). Qed.
Lemma lem80930 (h1 : Nat.mul = term5) : Nat.mul = term5.
Proof. exact (h1). Qed.
Lemma lem80931 (h1 : Nat.mul = term5) : term5 = Nat.mul.
Proof. exact (SYM (@lem80930 h1)). Qed.
Lemma lem80932 (h1 : term5 = Nat.mul) : term5 = Nat.mul.
Proof. exact (h1). Qed.
Lemma lem80933 (h1 : term5 = Nat.mul) : Nat.mul = term5.
Proof. exact (SYM (@lem80932 h1)). Qed.
Lemma lem80934 : (Nat.mul = term5) = (term5 = Nat.mul).
Proof. exact (prop_ext (fun h1 : Nat.mul = term5 => @lem80931 h1) (fun h1 : term5 = Nat.mul => @lem80933 h1)). Qed.
Lemma lem80937 : term5 = Nat.mul.
Proof. exact (EQ_MP (@lem80934) (@lem80924)). Qed.
Lemma lem80938 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem80939 : term6 = term7.
Proof. exact (MK_COMB (@lem80937) (@lem80938)). Qed.
Lemma lem80940 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80941 (n : nat) : (term8 n) = (term9 n).
Proof. exact (MK_COMB (@lem80939) (@lem80940 n)). Qed.
Lemma lem80942 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80943 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem80942) (@lem80941 n)). Qed.
Lemma lem80944 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem80945 (n : nat) : ((term8 n) = (NUMERAL 0)) = ((term9 n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem80943 n) (@lem80944)). Qed.
Lemma lem80946 : term12 = term13.
Proof. exact (fun_ext (fun n : nat => @lem80945 n)). Qed.
Lemma lem80947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80948 : term14 = term15.
Proof. exact (MK_COMB (@lem80947) (@lem80946)). Qed.
Lemma lem80949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80950 : term16 = term17.
Proof. exact (MK_COMB (@lem80949) (@lem80948)). Qed.
Lemma lem80952 : term5 = Nat.mul.
Proof. exact (EQ_MP (@lem80934) (@lem80924)). Qed.
Lemma lem80953 (m : nat) : (S m) = (S m).
Proof. exact (eq_refl (S m)). Qed.
Lemma lem80954 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem80952) (@lem80953 m)). Qed.
Lemma lem80955 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80956 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem80954 m) (@lem80955 n)). Qed.
Lemma lem80957 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80958 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem80957) (@lem80956 m n)). Qed.
Lemma lem80960 : term5 = Nat.mul.
Proof. exact (EQ_MP (@lem80934) (@lem80924)). Qed.
Lemma lem80961 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem80962 (m : nat) : (term24 m) = (Nat.mul m).
Proof. exact (MK_COMB (@lem80960) (@lem80961 m)). Qed.
Lemma lem80963 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80964 (m : nat) (n : nat) : (term25 m n) = (Nat.mul m n).
Proof. exact (MK_COMB (@lem80962 m) (@lem80963 n)). Qed.
Lemma lem80965 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80966 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem80965) (@lem80964 m n)). Qed.
Lemma lem80967 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80968 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem80966 m n) (@lem80967 n)). Qed.
Lemma lem80969 (m : nat) (n : nat) : ((term20 m n) = (term28 m n)) = ((term21 m n) = (term29 m n)).
Proof. exact (MK_COMB (@lem80958 m n) (@lem80968 m n)). Qed.
Lemma lem80970 (m : nat) : (term30 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem80969 m n)). Qed.
Lemma lem80971 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80972 (m : nat) : (term32 m) = (term33 m).
Proof. exact (MK_COMB (@lem80971) (@lem80970 m)). Qed.
Lemma lem80973 : term34 = term35.
Proof. exact (fun_ext (fun m : nat => @lem80972 m)). Qed.
Lemma lem80974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80975 : term36 = term37.
Proof. exact (MK_COMB (@lem80974) (@lem80973)). Qed.
Lemma lem80976 : term4 = term38.
Proof. exact (MK_COMB (@lem80950) (@lem80975)). Qed.
Lemma lem80977 : term38.
Proof. exact (EQ_MP (@lem80976) (@lem80929)). Qed.
