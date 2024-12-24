Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_LT_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIV_UNIQ_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem182044 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem182045 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem182044 h1 m). Qed.
Lemma lem182046 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem182047 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem182046 m) (@lem182045 m h1)). Qed.
Lemma lem182048 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem182047 m h1 n). Qed.
Lemma lem182049 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem182050 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem182049 m n) (@lem182048 m n h1)). Qed.
Lemma lem182051 (m : nat) (n : nat) (q : nat) (h1 : term0) : term5 m n q.
Proof. exact (@lem182050 m n h1 q). Qed.
Lemma lem182052 (m : nat) (n : nat) (q : nat) : (term5 m n q) = (term6 m n q).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem182053 (m : nat) (n : nat) (q : nat) (h1 : term0) : term6 m n q.
Proof. exact (EQ_MP (@lem182052 m n q) (@lem182051 m n q h1)). Qed.
Lemma lem182054 (m : nat) (n : nat) (q : nat) (r : nat) (h1 : term0) : term7 m n q r.
Proof. exact (@lem182053 m n q h1 r). Qed.
Lemma lem182055 (r : nat) (m : nat) (n : nat) (q : nat) : (term7 m n q r) = (term8 r m n q).
Proof. exact (eq_refl (term7 m n q r)). Qed.
Lemma lem182056 (r : nat) (m : nat) (n : nat) (q : nat) (h1 : term0) : term8 r m n q.
Proof. exact (EQ_MP (@lem182055 r m n q) (@lem182054 m n q r h1)). Qed.
Lemma lem182057 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem182058 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : (Nat.div m n) = q.
Proof. exact (@lem182056 r m n q h1 (@lem182057 m q r n h2)). Qed.
Lemma lem182059 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term10 m n q.
Proof. exact (fun h0 : term0 => @lem182058 m q r n h0 h1). Qed.
Lemma lem182060 (m : nat) (q : nat) (n : nat) (h1 : term11 m q n) : term11 m q n.
Proof. exact (h1). Qed.
Lemma lem182061 (m : nat) (q : nat) (n : nat) (h1 : term11 m q n) : term10 m n q.
Proof. exact (ex_elim (@lem182060 m q n h1) (fun r : nat => fun h0 : term12 m q n r => @lem182059 m q r n h0)). Qed.
Lemma lem182062 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem182063 (m : nat) (q : nat) (n : nat) (h1 : term0) (h2 : term11 m q n) : (Nat.div m n) = q.
Proof. exact (@lem182061 m q n h2 (@lem182062 h1)). Qed.
Lemma lem182064 (m : nat) (n : nat) (q : nat) (h1 : term0) : term13 m n q.
Proof. exact (fun h0 : term11 m q n => @lem182063 m q n h1 h0). Qed.
Lemma lem182065 (m : nat) (n : nat) (h1 : term0) : term14 m n.
Proof. exact (fun q : nat => @lem182064 m n q h1). Qed.
Lemma lem182066 (m : nat) (h1 : term0) : term15 m.
Proof. exact (fun n : nat => @lem182065 m n h1). Qed.
Lemma lem182067 (h1 : term0) : term16.
Proof. exact (fun m : nat => @lem182066 m h1). Qed.
Lemma lem182068 : term17.
Proof. exact (fun h0 : term0 => @lem182067 h0). Qed.
Lemma lem182069 : term16.
Proof. exact (@lem182068 (@lem169759)). Qed.
Lemma lem182070 (m : nat) : term18 m.
Proof. exact (@lem182069 m). Qed.
Lemma lem182071 (m : nat) : (term18 m) = (term15 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem182072 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem182071 m) (@lem182070 m)). Qed.
Lemma lem182073 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem182072 m n). Qed.
Lemma lem182074 (m : nat) (n : nat) : (term19 m n) = (term14 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem182075 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem182074 m n) (@lem182073 m n)). Qed.
Lemma lem182076 (m : nat) (n : nat) (q : nat) : term20 m n q.
Proof. exact (@lem182075 m n q). Qed.
Lemma lem182077 (m : nat) (n : nat) (q : nat) : (term20 m n q) = (term13 m n q).
Proof. exact (eq_refl (term20 m n q)). Qed.
Lemma lem182079 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem182081 (m : nat) (n : nat) (q : nat) : term13 m n q.
Proof. exact (EQ_MP (@lem182077 m n q) (@lem182076 m n q)). Qed.
Lemma lem182082 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem182081 m n (NUMERAL 0)). Qed.
Lemma lem182103 : term22.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem182104 (n : nat) : term23 n.
Proof. exact (@lem182103 n). Qed.
Lemma lem182105 (n : nat) : (term23 n) = ((term24 n) = n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem182137 : term25.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem182138 (n : nat) : term26 n.
Proof. exact (@lem182137 n). Qed.
Lemma lem182139 (n : nat) : (term26 n) = ((term27 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem182141 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem182148 (n : nat) : (term27 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem182139 n) (@lem182138 n)). Qed.
Lemma lem182149 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem182150 (n : nat) : (term28 n) = term29.
Proof. exact (MK_COMB (@lem182149) (@lem182148 n)). Qed.
Lemma lem182151 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem182152 (n : nat) (m : nat) : (term30 n m) = (term24 m).
Proof. exact (MK_COMB (@lem182150 n) (@lem182151 m)). Qed.
Lemma lem182154 (n : nat) : (term24 n) = n.
Proof. exact (EQ_MP (@lem182105 n) (@lem182104 n)). Qed.
Lemma lem182155 (m : nat) : (term24 m) = m.
Proof. exact (@lem182154 m). Qed.
Lemma lem182156 (n : nat) (m : nat) : (term30 n m) = m.
Proof. exact (TRANS (@lem182152 n m) (@lem182155 m)). Qed.
Lemma lem182157 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem182158 (n : nat) (m : nat) : (m = (term30 n m)) = (m = m).
Proof. exact (MK_COMB (@lem182157 m) (@lem182156 n m)). Qed.
Lemma lem182160 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem182161 (x : nat) : (x = x) = True.
Proof. exact (@lem182160 nat x). Qed.
Lemma lem182162 (m : nat) : (m = m) = True.
Proof. exact (@lem182161 m). Qed.
Lemma lem182163 (n : nat) (m : nat) : (m = (term30 n m)) = True.
Proof. exact (TRANS (@lem182158 n m) (@lem182162 m)). Qed.
Lemma lem182164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem182165 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem182164) (@lem182163 n m)). Qed.
Lemma lem182167 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem182141 m n) (@lem182079 m n h1)). Qed.
Lemma lem182168 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term32 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem182165 n m) (@lem182167 m n h1)). Qed.
Lemma lem182170 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem182171 : (True /\ True) = True.
Proof. exact (@lem182170 True). Qed.
Lemma lem182172 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term32 m n) = True.
Proof. exact (TRANS (@lem182168 m n h1) (@lem182171)). Qed.
Lemma lem182173 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (term32 m n).
Proof. exact (SYM (@lem182172 m n h1)). Qed.
Lemma lem182174 (m : nat) (n : nat) (h1 : Peano.lt m n) : term32 m n.
Proof. exact (EQ_MP (@lem182173 m n h1) (@lem0)). Qed.
Lemma lem182175 (m : nat) (n : nat) (h1 : Peano.lt m n) : term33 m n.
Proof. exact (ex_intro (term34 m n) m (@lem182174 m n h1)). Qed.
Lemma lem182176 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (@lem182082 m n (@lem182175 m n h1)). Qed.
Lemma lem182177 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = ((Nat.div m n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : Peano.lt m n => @lem182176 m n h1) (fun h2 : (Nat.div m n) = (NUMERAL 0) => @lem182079 m n h1)). Qed.
Lemma lem182178 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem182177 m n h1) (@lem182079 m n h1)). Qed.
Lemma lem182179 (m : nat) (n : nat) : term35 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem182178 m n h0). Qed.
Lemma lem182184 (m : nat) : term36 m.
Proof. exact (fun n : nat => @lem182179 m n). Qed.
Lemma lem182189 : term37.
Proof. exact (fun m : nat => @lem182184 m). Qed.
