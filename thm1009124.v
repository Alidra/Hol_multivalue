Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009124_term_abbrevs.
Require Import BIT1_spec.
Require Import EXP_ADD_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm86199_spec.
Lemma lem1009022 : term0.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem1009023 (m : nat) : term1 m.
Proof. exact (@lem1009022 m). Qed.
Lemma lem1009024 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1009025 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1009024 m) (@lem1009023 m)). Qed.
Lemma lem1009026 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1009025 m n). Qed.
Lemma lem1009027 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1009033 (m : nat) : term6 m.
Proof. exact (@lem87724 m). Qed.
Lemma lem1009034 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1009035 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem1009034 m) (@lem1009033 m)). Qed.
Lemma lem1009036 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem1009035 m n). Qed.
Lemma lem1009037 (n : nat) (m : nat) : (term8 m n) = (term9 n m).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem1009038 (n : nat) (m : nat) : term9 n m.
Proof. exact (EQ_MP (@lem1009037 n m) (@lem1009036 m n)). Qed.
Lemma lem1009039 (n : nat) (m : nat) (p : nat) : term10 n m p.
Proof. exact (@lem1009038 n m p). Qed.
Lemma lem1009040 (n : nat) (m : nat) (p : nat) : (term10 n m p) = ((term11 m n p) = (term12 n m p)).
Proof. exact (eq_refl (term10 n m p)). Qed.
Lemma lem1009042 (n : nat) : term13 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem1009043 (n : nat) : (term13 n) = ((BIT1 n) = (term14 n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem1009045 (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (Nat.pow m n) = p.
Proof. exact (h1). Qed.
Lemma lem1009046 (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : p = (Nat.pow m n).
Proof. exact (SYM (@lem1009045 m n p h1)). Qed.
Lemma lem1009047 (b : nat) (m : nat) (n : nat) (a : nat) : (term15 b m n a) = (term15 b m n a).
Proof. exact (eq_refl (term15 b m n a)). Qed.
Lemma lem1009048 (b : nat) (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term16 b m n a p) = (term17 b a m n).
Proof. exact (MK_COMB (@lem1009047 b m n a) (@lem1009046 m n p h1)). Qed.
Lemma lem1009049 (b : nat) (m : nat) (n : nat) (a : nat) : (term17 b a m n) = (term18 b m n a).
Proof. exact (eq_refl (term17 b a m n)). Qed.
Lemma lem1009050 (b : nat) (m : nat) (n : nat) (a : nat) (p : nat) : (term19 b m n a p) = (term19 b m n a p).
Proof. exact (eq_refl (term19 b m n a p)). Qed.
Lemma lem1009051 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : ((term16 b m n a p) = (term17 b a m n)) = ((term16 b m n a p) = (term18 b m n a)).
Proof. exact (MK_COMB (@lem1009050 b m n a p) (@lem1009049 b m n a)). Qed.
Lemma lem1009052 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : (term16 b m n a p) = (term20 p b m n a).
Proof. exact (eq_refl (term16 b m n a p)). Qed.
Lemma lem1009053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1009054 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : (term19 b m n a p) = (term21 p b m n a).
Proof. exact (MK_COMB (@lem1009053) (@lem1009052 p b m n a)). Qed.
Lemma lem1009055 (b : nat) (m : nat) (n : nat) (a : nat) : (term18 b m n a) = (term18 b m n a).
Proof. exact (eq_refl (term18 b m n a)). Qed.
Lemma lem1009056 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : ((term16 b m n a p) = (term18 b m n a)) = ((term20 p b m n a) = (term18 b m n a)).
Proof. exact (MK_COMB (@lem1009054 p b m n a) (@lem1009055 b m n a)). Qed.
Lemma lem1009057 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : ((term16 b m n a p) = (term17 b a m n)) = ((term20 p b m n a) = (term18 b m n a)).
Proof. exact (TRANS (@lem1009051 p b m n a) (@lem1009056 p b m n a)). Qed.
Lemma lem1009058 (b : nat) (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term20 p b m n a) = (term18 b m n a).
Proof. exact (EQ_MP (@lem1009057 p b m n a) (@lem1009048 b a m n p h1)). Qed.
Lemma lem1009059 (b : nat) (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : (term18 b m n a) = (term20 p b m n a).
Proof. exact (SYM (@lem1009058 b a m n p h1)). Qed.
Lemma lem1009060 (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : (term22 m n) = b.
Proof. exact (h1). Qed.
Lemma lem1009061 (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : b = (term22 m n).
Proof. exact (SYM (@lem1009060 m n b h1)). Qed.
Lemma lem1009062 (m : nat) (n : nat) (a : nat) : (term23 m n a) = (term23 m n a).
Proof. exact (eq_refl (term23 m n a)). Qed.
Lemma lem1009063 (a : nat) (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : (term24 m n a b) = (term25 a m n).
Proof. exact (MK_COMB (@lem1009062 m n a) (@lem1009061 m n b h1)). Qed.
Lemma lem1009064 (m : nat) (n : nat) (a : nat) : (term25 a m n) = (term26 m n a).
Proof. exact (eq_refl (term25 a m n)). Qed.
Lemma lem1009065 (m : nat) (n : nat) (a : nat) (b : nat) : (term27 m n a b) = (term27 m n a b).
Proof. exact (eq_refl (term27 m n a b)). Qed.
Lemma lem1009066 (b : nat) (m : nat) (n : nat) (a : nat) : ((term24 m n a b) = (term25 a m n)) = ((term24 m n a b) = (term26 m n a)).
Proof. exact (MK_COMB (@lem1009065 m n a b) (@lem1009064 m n a)). Qed.
Lemma lem1009067 (b : nat) (m : nat) (n : nat) (a : nat) : (term24 m n a b) = (term28 b m n a).
Proof. exact (eq_refl (term24 m n a b)). Qed.
Lemma lem1009068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1009069 (b : nat) (m : nat) (n : nat) (a : nat) : (term27 m n a b) = (term29 b m n a).
Proof. exact (MK_COMB (@lem1009068) (@lem1009067 b m n a)). Qed.
Lemma lem1009070 (m : nat) (n : nat) (a : nat) : (term26 m n a) = (term26 m n a).
Proof. exact (eq_refl (term26 m n a)). Qed.
Lemma lem1009071 (b : nat) (m : nat) (n : nat) (a : nat) : ((term24 m n a b) = (term26 m n a)) = ((term28 b m n a) = (term26 m n a)).
Proof. exact (MK_COMB (@lem1009069 b m n a) (@lem1009070 m n a)). Qed.
Lemma lem1009072 (b : nat) (m : nat) (n : nat) (a : nat) : ((term24 m n a b) = (term25 a m n)) = ((term28 b m n a) = (term26 m n a)).
Proof. exact (TRANS (@lem1009066 b m n a) (@lem1009071 b m n a)). Qed.
Lemma lem1009073 (a : nat) (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : (term28 b m n a) = (term26 m n a).
Proof. exact (EQ_MP (@lem1009072 b m n a) (@lem1009063 a m n b h1)). Qed.
Lemma lem1009074 (a : nat) (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : (term26 m n a) = (term28 b m n a).
Proof. exact (SYM (@lem1009073 a m n b h1)). Qed.
Lemma lem1009075 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : (term30 m n) = a.
Proof. exact (h1). Qed.
Lemma lem1009076 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : a = (term30 m n).
Proof. exact (SYM (@lem1009075 m n a h1)). Qed.
Lemma lem1009077 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1009078 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : (term32 m n a) = (term33 m n).
Proof. exact (MK_COMB (@lem1009077 m n) (@lem1009076 m n a h1)). Qed.
Lemma lem1009079 (m : nat) (n : nat) : (term33 m n) = ((term34 m n) = (term30 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1009080 (m : nat) (n : nat) (a : nat) : (term35 m n a) = (term35 m n a).
Proof. exact (eq_refl (term35 m n a)). Qed.
Lemma lem1009081 (a : nat) (m : nat) (n : nat) : ((term32 m n a) = (term33 m n)) = ((term32 m n a) = ((term34 m n) = (term30 m n))).
Proof. exact (MK_COMB (@lem1009080 m n a) (@lem1009079 m n)). Qed.
Lemma lem1009082 (m : nat) (n : nat) (a : nat) : (term32 m n a) = ((term34 m n) = a).
Proof. exact (eq_refl (term32 m n a)). Qed.
Lemma lem1009083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1009084 (m : nat) (n : nat) (a : nat) : (term35 m n a) = (term36 m n a).
Proof. exact (MK_COMB (@lem1009083) (@lem1009082 m n a)). Qed.
Lemma lem1009085 (m : nat) (n : nat) : ((term34 m n) = (term30 m n)) = ((term34 m n) = (term30 m n)).
Proof. exact (eq_refl ((term34 m n) = (term30 m n))). Qed.
Lemma lem1009086 (a : nat) (m : nat) (n : nat) : ((term32 m n a) = ((term34 m n) = (term30 m n))) = (((term34 m n) = a) = ((term34 m n) = (term30 m n))).
Proof. exact (MK_COMB (@lem1009084 m n a) (@lem1009085 m n)). Qed.
Lemma lem1009087 (a : nat) (m : nat) (n : nat) : ((term32 m n a) = (term33 m n)) = (((term34 m n) = a) = ((term34 m n) = (term30 m n))).
Proof. exact (TRANS (@lem1009081 a m n) (@lem1009086 a m n)). Qed.
Lemma lem1009088 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : ((term34 m n) = a) = ((term34 m n) = (term30 m n)).
Proof. exact (EQ_MP (@lem1009087 a m n) (@lem1009078 m n a h1)). Qed.
Lemma lem1009089 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : ((term34 m n) = (term30 m n)) = ((term34 m n) = a).
Proof. exact (SYM (@lem1009088 m n a h1)). Qed.
Lemma lem1009093 (n : nat) : (BIT1 n) = (term14 n).
Proof. exact (EQ_MP (@lem1009043 n) (@lem1009042 n)). Qed.
Lemma lem1009094 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem1009095 (m : nat) (n : nat) : (term34 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem1009094 m) (@lem1009093 n)). Qed.
Lemma lem1009097 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem1009027 m n) (@lem1009026 m n)). Qed.
Lemma lem1009098 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (@lem1009097 m (Nat.add n n)). Qed.
Lemma lem1009100 (n : nat) (m : nat) (p : nat) : (term11 m n p) = (term12 n m p).
Proof. exact (EQ_MP (@lem1009040 n m p) (@lem1009039 n m p)). Qed.
Lemma lem1009101 (m : nat) (n : nat) : (term39 m n) = (term22 m n).
Proof. exact (@lem1009100 n m n). Qed.
Lemma lem1009102 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1009103 (m : nat) (n : nat) : (term38 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem1009102 m) (@lem1009101 m n)). Qed.
Lemma lem1009104 (m : nat) (n : nat) : (term37 m n) = (term30 m n).
Proof. exact (TRANS (@lem1009098 m n) (@lem1009103 m n)). Qed.
Lemma lem1009105 (m : nat) (n : nat) : (term34 m n) = (term30 m n).
Proof. exact (TRANS (@lem1009095 m n) (@lem1009104 m n)). Qed.
Lemma lem1009106 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1009107 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem1009106) (@lem1009105 m n)). Qed.
Lemma lem1009108 (m : nat) (n : nat) : (term30 m n) = (term30 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1009109 (m : nat) (n : nat) : ((term34 m n) = (term30 m n)) = ((term30 m n) = (term30 m n)).
Proof. exact (MK_COMB (@lem1009107 m n) (@lem1009108 m n)). Qed.
Lemma lem1009111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1009112 (x : nat) : (x = x) = True.
Proof. exact (@lem1009111 nat x). Qed.
Lemma lem1009113 (m : nat) (n : nat) : ((term30 m n) = (term30 m n)) = True.
Proof. exact (@lem1009112 (term30 m n)). Qed.
Lemma lem1009114 (m : nat) (n : nat) : ((term34 m n) = (term30 m n)) = True.
Proof. exact (TRANS (@lem1009109 m n) (@lem1009113 m n)). Qed.
Lemma lem1009115 (m : nat) (n : nat) : True = ((term34 m n) = (term30 m n)).
Proof. exact (SYM (@lem1009114 m n)). Qed.
Lemma lem1009116 (m : nat) (n : nat) : (term34 m n) = (term30 m n).
Proof. exact (EQ_MP (@lem1009115 m n) (@lem0)). Qed.
Lemma lem1009117 (m : nat) (n : nat) (a : nat) (h1 : (term30 m n) = a) : (term34 m n) = a.
Proof. exact (EQ_MP (@lem1009089 m n a h1) (@lem1009116 m n)). Qed.
Lemma lem1009118 (m : nat) (n : nat) (a : nat) : term26 m n a.
Proof. exact (fun h0 : (term30 m n) = a => @lem1009117 m n a h0). Qed.
Lemma lem1009119 (a : nat) (m : nat) (n : nat) (b : nat) (h1 : (term22 m n) = b) : term28 b m n a.
Proof. exact (EQ_MP (@lem1009074 a m n b h1) (@lem1009118 m n a)). Qed.
Lemma lem1009120 (b : nat) (m : nat) (n : nat) (a : nat) : term18 b m n a.
Proof. exact (fun h0 : (term22 m n) = b => @lem1009119 a m n b h0). Qed.
Lemma lem1009121 (b : nat) (a : nat) (m : nat) (n : nat) (p : nat) (h1 : (Nat.pow m n) = p) : term20 p b m n a.
Proof. exact (EQ_MP (@lem1009059 b a m n p h1) (@lem1009120 b m n a)). Qed.
Lemma lem1009124 (p : nat) (b : nat) (m : nat) (n : nat) (a : nat) : term42 p b m n a.
Proof. exact (fun h0 : (Nat.pow m n) = p => @lem1009121 b a m n p h0). Qed.
