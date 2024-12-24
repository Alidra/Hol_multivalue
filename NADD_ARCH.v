Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ARCH_term_abbrevs.
Require Import NADD_BOUND_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1273056 (x : nadd) : term0 x.
Proof. exact (@lem1263160 x). Qed.
Lemma lem1273057 (x : nadd) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1273058 (x : nadd) : term1 x.
Proof. exact (EQ_MP (@lem1273057 x) (@lem1273056 x)). Qed.
Lemma lem1273059 (x : nadd) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1273061 (k : nat) : term2 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1273062 (k : nat) : (term2 k) = ((term3 k) = (term4 k)).
Proof. exact (eq_refl (term2 k)). Qed.
Lemma lem1273064 (x : nadd) : term5 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1273065 (x : nadd) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1273066 (x : nadd) : term6 x.
Proof. exact (EQ_MP (@lem1273065 x) (@lem1273064 x)). Qed.
Lemma lem1273067 (x : nadd) (y : nadd) : term7 x y.
Proof. exact (@lem1273066 x y). Qed.
Lemma lem1273068 (x : nadd) (y : nadd) : (term7 x y) = ((nadd_le x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1273079 (x : nadd) (y : nadd) : (nadd_le x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1273068 x y) (@lem1273067 x y)). Qed.
Lemma lem1273080 (x : nadd) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (@lem1273079 x (nadd_of_num n)). Qed.
Lemma lem1273090 (k : nat) : (term3 k) = (term4 k).
Proof. exact (EQ_MP (@lem1273062 k) (@lem1273061 k)). Qed.
Lemma lem1273091 (n : nat) : (term3 n) = (term4 n).
Proof. exact (@lem1273090 n). Qed.
Lemma lem1273092 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273093 (n : nat) (n' : nat) : (term11 n n') = (term12 n n').
Proof. exact (MK_COMB (@lem1273091 n) (@lem1273092 n')). Qed.
Lemma lem1273095 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1273096 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1273095 nat nat f y). Qed.
Lemma lem1273097 (n : nat) (n' : nat) : (term15 n n') = (term12 n n').
Proof. exact (@lem1273096 (term4 n) n'). Qed.
Lemma lem1273098 (n : nat) (n' : nat) : (term12 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term12 n n')). Qed.
Lemma lem1273099 (n : nat) : (term16 n) = (term4 n).
Proof. exact (fun_ext (fun n' : nat => @lem1273098 n n')). Qed.
Lemma lem1273100 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273101 (n : nat) (n' : nat) : (term15 n n') = (term12 n n').
Proof. exact (MK_COMB (@lem1273099 n) (@lem1273100 n')). Qed.
Lemma lem1273102 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1273103 (n : nat) (n' : nat) : (term17 n n') = (term18 n n').
Proof. exact (MK_COMB (@lem1273102) (@lem1273101 n n')). Qed.
Lemma lem1273104 (n : nat) (n' : nat) : (term12 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term12 n n')). Qed.
Lemma lem1273105 (n : nat) (n' : nat) : ((term15 n n') = (term12 n n')) = ((term12 n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem1273103 n n') (@lem1273104 n n')). Qed.
Lemma lem1273106 (n : nat) (n' : nat) : (term12 n n') = (Nat.mul n n').
Proof. exact (EQ_MP (@lem1273105 n n') (@lem1273097 n n')). Qed.
Lemma lem1273107 (n : nat) (n' : nat) : (term11 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem1273093 n n') (@lem1273106 n n')). Qed.
Lemma lem1273108 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1273109 (n : nat) (n' : nat) : (term19 n n') = (term20 n n').
Proof. exact (MK_COMB (@lem1273108) (@lem1273107 n n')). Qed.
Lemma lem1273110 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1273111 (n : nat) (n' : nat) (B : nat) : (term21 n n' B) = (term22 n n' B).
Proof. exact (MK_COMB (@lem1273109 n n') (@lem1273110 B)). Qed.
Lemma lem1273112 (x : nadd) (n' : nat) : (term23 x n') = (term23 x n').
Proof. exact (eq_refl (term23 x n')). Qed.
Lemma lem1273113 (x : nadd) (n : nat) (n' : nat) (B : nat) : (term24 x n n' B) = (term25 x n n' B).
Proof. exact (MK_COMB (@lem1273112 x n') (@lem1273111 n n' B)). Qed.
Lemma lem1273114 (x : nadd) (n : nat) (B : nat) : (term26 x n B) = (term27 x n B).
Proof. exact (fun_ext (fun n' : nat => @lem1273113 x n n' B)). Qed.
Lemma lem1273115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1273116 (x : nadd) (n : nat) (B : nat) : (term28 x n B) = (term29 x n B).
Proof. exact (MK_COMB (@lem1273115) (@lem1273114 x n B)). Qed.
Lemma lem1273121 (x : nadd) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (fun_ext (fun B : nat => @lem1273116 x n B)). Qed.
Lemma lem1273122 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1273123 (x : nadd) (n : nat) : (term10 x n) = (term32 x n).
Proof. exact (MK_COMB (@lem1273122) (@lem1273121 x n)). Qed.
Lemma lem1273128 (x : nadd) (n : nat) : (term9 x n) = (term32 x n).
Proof. exact (TRANS (@lem1273080 x n) (@lem1273123 x n)). Qed.
Lemma lem1273129 (x : nadd) : (term33 x) = (term34 x).
Proof. exact (fun_ext (fun n : nat => @lem1273128 x n)). Qed.
Lemma lem1273130 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1273131 (x : nadd) : (term35 x) = (term1 x).
Proof. exact (MK_COMB (@lem1273130) (@lem1273129 x)). Qed.
Lemma lem1273133 (x : nadd) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1273059 x) (@lem1273058 x)). Qed.
Lemma lem1273134 (x : nadd) : (term35 x) = True.
Proof. exact (TRANS (@lem1273131 x) (@lem1273133 x)). Qed.
Lemma lem1273135 : term36 = term37.
Proof. exact (fun_ext (fun x : nadd => @lem1273134 x)). Qed.
Lemma lem1273136 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1273137 : term38 = term39.
Proof. exact (MK_COMB (@lem1273136) (@lem1273135)). Qed.
Lemma lem1273139 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1273140 (t : Prop) : (term41 t) = t.
Proof. exact (@lem1273139 nadd t). Qed.
Lemma lem1273141 : term39 = True.
Proof. exact (@lem1273140 True). Qed.
Lemma lem1273142 : term38 = True.
Proof. exact (TRANS (@lem1273137) (@lem1273141)). Qed.
Lemma lem1273143 : True = term38.
Proof. exact (SYM (@lem1273142)). Qed.
Lemma lem1273144 : term38.
Proof. exact (EQ_MP (@lem1273143) (@lem0)). Qed.
