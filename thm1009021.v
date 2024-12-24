Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009021_term_abbrevs.
Require Import BIT0_spec.
Require Import EXP_ADD_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1008953 (m : nat) : term0 m.
Proof. exact (@lem87724 m). Qed.
Lemma lem1008954 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1008955 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1008954 m) (@lem1008953 m)). Qed.
Lemma lem1008956 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1008955 m n). Qed.
Lemma lem1008957 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1008958 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem1008957 n m) (@lem1008956 m n)). Qed.
Lemma lem1008959 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem1008958 n m p). Qed.
Lemma lem1008960 (n : nat) (m : nat) (p : nat) : (term4 n m p) = ((term5 m n p) = (term6 n m p)).
Proof. exact (eq_refl (term4 n m p)). Qed.
Lemma lem1008962 (n : nat) : term7 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem1008963 (n : nat) : (term7 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1008965 (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (Nat.pow m n) = p.
Proof. exact (h1). Qed.
Lemma lem1008966 (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : p = (Nat.pow m n).
Proof. exact (SYM (@lem1008965 m n p h1)). Qed.
Lemma lem1008967 (m : nat) (n : nat) (a : nat) : (term8 m n a) = (term8 m n a).
Proof. exact (eq_refl (term8 m n a)). Qed.
Lemma lem1008968 (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term9 m n a p) = (term10 a m n).
Proof. exact (MK_COMB (@lem1008967 m n a) (@lem1008966 m n p h1)). Qed.
Lemma lem1008969 (m : nat) (n : nat) (a : nat) : (term10 a m n) = (term11 m n a).
Proof. exact (eq_refl (term10 a m n)). Qed.
Lemma lem1008970 (m : nat) (n : nat) (a : nat) (p : nat) : (term12 m n a p) = (term12 m n a p).
Proof. exact (eq_refl (term12 m n a p)). Qed.
Lemma lem1008971 (p : nat) (m : nat) (n : nat) (a : nat) : ((term9 m n a p) = (term10 a m n)) = ((term9 m n a p) = (term11 m n a)).
Proof. exact (MK_COMB (@lem1008970 m n a p) (@lem1008969 m n a)). Qed.
Lemma lem1008972 (p : nat) (m : nat) (n : nat) (a : nat) : (term9 m n a p) = (term13 p m n a).
Proof. exact (eq_refl (term9 m n a p)). Qed.
Lemma lem1008973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008974 (p : nat) (m : nat) (n : nat) (a : nat) : (term12 m n a p) = (term14 p m n a).
Proof. exact (MK_COMB (@lem1008973) (@lem1008972 p m n a)). Qed.
Lemma lem1008975 (m : nat) (n : nat) (a : nat) : (term11 m n a) = (term11 m n a).
Proof. exact (eq_refl (term11 m n a)). Qed.
Lemma lem1008976 (p : nat) (m : nat) (n : nat) (a : nat) : ((term9 m n a p) = (term11 m n a)) = ((term13 p m n a) = (term11 m n a)).
Proof. exact (MK_COMB (@lem1008974 p m n a) (@lem1008975 m n a)). Qed.
Lemma lem1008977 (p : nat) (m : nat) (n : nat) (a : nat) : ((term9 m n a p) = (term10 a m n)) = ((term13 p m n a) = (term11 m n a)).
Proof. exact (TRANS (@lem1008971 p m n a) (@lem1008976 p m n a)). Qed.
Lemma lem1008978 (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term13 p m n a) = (term11 m n a).
Proof. exact (EQ_MP (@lem1008977 p m n a) (@lem1008968 a m n p h1)). Qed.
Lemma lem1008979 (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term11 m n a) = (term13 p m n a).
Proof. exact (SYM (@lem1008978 a m n p h1)). Qed.
Lemma lem1008980 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : (term15 m n) = a.
Proof. exact (h1). Qed.
Lemma lem1008981 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : a = (term15 m n).
Proof. exact (SYM (@lem1008980 m n a h1)). Qed.
Lemma lem1008982 (m : nat) (n : nat) : (term16 m n) = (term16 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1008983 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : (term17 m n a) = (term18 m n).
Proof. exact (MK_COMB (@lem1008982 m n) (@lem1008981 m n a h1)). Qed.
Lemma lem1008984 (m : nat) (n : nat) : (term18 m n) = ((term19 m n) = (term15 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1008985 (m : nat) (n : nat) (a : nat) : (term20 m n a) = (term20 m n a).
Proof. exact (eq_refl (term20 m n a)). Qed.
Lemma lem1008986 (a : nat) (m : nat) (n : nat) : ((term17 m n a) = (term18 m n)) = ((term17 m n a) = ((term19 m n) = (term15 m n))).
Proof. exact (MK_COMB (@lem1008985 m n a) (@lem1008984 m n)). Qed.
Lemma lem1008987 (m : nat) (n : nat) (a : nat) : (term17 m n a) = ((term19 m n) = a).
Proof. exact (eq_refl (term17 m n a)). Qed.
Lemma lem1008988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008989 (m : nat) (n : nat) (a : nat) : (term20 m n a) = (term21 m n a).
Proof. exact (MK_COMB (@lem1008988) (@lem1008987 m n a)). Qed.
Lemma lem1008990 (m : nat) (n : nat) : ((term19 m n) = (term15 m n)) = ((term19 m n) = (term15 m n)).
Proof. exact (eq_refl ((term19 m n) = (term15 m n))). Qed.
Lemma lem1008991 (a : nat) (m : nat) (n : nat) : ((term17 m n a) = ((term19 m n) = (term15 m n))) = (((term19 m n) = a) = ((term19 m n) = (term15 m n))).
Proof. exact (MK_COMB (@lem1008989 m n a) (@lem1008990 m n)). Qed.
Lemma lem1008992 (a : nat) (m : nat) (n : nat) : ((term17 m n a) = (term18 m n)) = (((term19 m n) = a) = ((term19 m n) = (term15 m n))).
Proof. exact (TRANS (@lem1008986 a m n) (@lem1008991 a m n)). Qed.
Lemma lem1008993 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : ((term19 m n) = a) = ((term19 m n) = (term15 m n)).
Proof. exact (EQ_MP (@lem1008992 a m n) (@lem1008983 m n a h1)). Qed.
Lemma lem1008994 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : ((term19 m n) = (term15 m n)) = ((term19 m n) = a).
Proof. exact (SYM (@lem1008993 m n a h1)). Qed.
Lemma lem1008998 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem1008963 n) (@lem1008962 n)). Qed.
Lemma lem1008999 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem1009000 (m : nat) (n : nat) : (term19 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1008999 m) (@lem1008998 n)). Qed.
Lemma lem1009002 (n : nat) (m : nat) (p : nat) : (term5 m n p) = (term6 n m p).
Proof. exact (EQ_MP (@lem1008960 n m p) (@lem1008959 n m p)). Qed.
Lemma lem1009003 (m : nat) (n : nat) : (term22 m n) = (term15 m n).
Proof. exact (@lem1009002 n m n). Qed.
Lemma lem1009004 (m : nat) (n : nat) : (term19 m n) = (term15 m n).
Proof. exact (TRANS (@lem1009000 m n) (@lem1009003 m n)). Qed.
Lemma lem1009005 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1009006 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem1009005) (@lem1009004 m n)). Qed.
Lemma lem1009007 (m : nat) (n : nat) : (term15 m n) = (term15 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1009008 (m : nat) (n : nat) : ((term19 m n) = (term15 m n)) = ((term15 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem1009006 m n) (@lem1009007 m n)). Qed.
Lemma lem1009010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1009011 (x : nat) : (x = x) = True.
Proof. exact (@lem1009010 nat x). Qed.
Lemma lem1009012 (m : nat) (n : nat) : ((term15 m n) = (term15 m n)) = True.
Proof. exact (@lem1009011 (term15 m n)). Qed.
Lemma lem1009013 (m : nat) (n : nat) : ((term19 m n) = (term15 m n)) = True.
Proof. exact (TRANS (@lem1009008 m n) (@lem1009012 m n)). Qed.
Lemma lem1009014 (m : nat) (n : nat) : True = ((term19 m n) = (term15 m n)).
Proof. exact (SYM (@lem1009013 m n)). Qed.
Lemma lem1009015 (m : nat) (n : nat) : (term19 m n) = (term15 m n).
Proof. exact (EQ_MP (@lem1009014 m n) (@lem0)). Qed.
Lemma lem1009016 (m : nat) (n : nat) (a : nat) (h1 : (term15 m n) = a) : (term19 m n) = a.
Proof. exact (EQ_MP (@lem1008994 m n a h1) (@lem1009015 m n)). Qed.
Lemma lem1009017 (m : nat) (n : nat) (a : nat) : term11 m n a.
Proof. exact (fun h0 : (term15 m n) = a => @lem1009016 m n a h0). Qed.
Lemma lem1009018 (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : term13 p m n a.
Proof. exact (EQ_MP (@lem1008979 a m n p h1) (@lem1009017 m n a)). Qed.
Lemma lem1009021 (p : nat) (m : nat) (n : nat) (a : nat) : term25 p m n a.
Proof. exact (fun h0 : (Nat.pow m n) = p => @lem1009018 a m n p h0). Qed.
