Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EVENPOW_ABS_term_abbrevs.
Require Import REAL_ABS_ABS_spec.
Require Import REAL_POW_EQ_EQ_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1669004 (x : real) : term0 x.
Proof. exact (@lem1535666 x). Qed.
Lemma lem1669005 (x : real) : (term0 x) = ((term1 x) = (real_abs x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1669007 (n : nat) : term2 n.
Proof. exact (@lem1669003 n). Qed.
Lemma lem1669008 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1669009 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem1669008 n) (@lem1669007 n)). Qed.
Lemma lem1669010 (n : nat) (x : real) : term4 n x.
Proof. exact (@lem1669009 n x). Qed.
Lemma lem1669011 (n : nat) (x : real) : (term4 n x) = (term5 n x).
Proof. exact (eq_refl (term4 n x)). Qed.
Lemma lem1669012 (n : nat) (x : real) : term5 n x.
Proof. exact (EQ_MP (@lem1669011 n x) (@lem1669010 n x)). Qed.
Lemma lem1669013 (n : nat) (x : real) (y : real) : term6 n x y.
Proof. exact (@lem1669012 n x y). Qed.
Lemma lem1669014 (n : nat) (x : real) (y : real) : (term6 n x y) = (((real_pow x n) = (real_pow y n)) = (term7 n x y)).
Proof. exact (eq_refl (term6 n x y)). Qed.
Lemma lem1669027 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1669028 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem1669027 p q p' q'). Qed.
Lemma lem1669029 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem1669028 p q p'). Qed.
Lemma lem1669030 (x : real) (n : nat) : term11 x n.
Proof. exact (@lem1669029 (Coq.Arith.PeanoNat.Nat.Even n) ((term12 x n) = (real_pow x n))). Qed.
Lemma lem1669031 (x : real) (n : nat) (p' : Prop) : term13 x n p'.
Proof. exact (@lem1669030 x n p'). Qed.
Lemma lem1669032 (x : real) (n : nat) (p' : Prop) : (term13 x n p') = (term14 x n p').
Proof. exact (eq_refl (term13 x n p')). Qed.
Lemma lem1669033 (x : real) (n : nat) (p' : Prop) : term14 x n p'.
Proof. exact (EQ_MP (@lem1669032 x n p') (@lem1669031 x n p')). Qed.
Lemma lem1669034 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term15 x n p' q'.
Proof. exact (@lem1669033 x n p' q'). Qed.
Lemma lem1669035 (x : real) (n : nat) (p' : Prop) (q' : Prop) : (term15 x n p' q') = (term16 x n p' q').
Proof. exact (eq_refl (term15 x n p' q')). Qed.
Lemma lem1669036 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term16 x n p' q'.
Proof. exact (EQ_MP (@lem1669035 x n p' q') (@lem1669034 x n p' q')). Qed.
Lemma lem1669037 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1669038 (x : real) (n : nat) (q' : Prop) : term17 x n q'.
Proof. exact (@lem1669036 x n (Coq.Arith.PeanoNat.Nat.Even n) q'). Qed.
Lemma lem1669039 (x : real) (n : nat) (q' : Prop) : term18 x n q'.
Proof. exact (@lem1669038 x n q' (@lem1669037 n)). Qed.
Lemma lem1669040 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem1669041 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1669044 (n : nat) (x : real) (y : real) : ((real_pow x n) = (real_pow y n)) = (term7 n x y).
Proof. exact (EQ_MP (@lem1669014 n x y) (@lem1669013 n x y)). Qed.
Lemma lem1669045 (n : nat) (x : real) : ((term12 x n) = (real_pow x n)) = (term19 n x).
Proof. exact (@lem1669044 n (real_abs x) x). Qed.
Lemma lem1669047 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term20 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1669048 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term21 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1669047 _2963 g t e g' t' e'). Qed.
Lemma lem1669049 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term22 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1669048 _2963 g t e g' t'). Qed.
Lemma lem1669050 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term23 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1669049 _2963 g t e g'). Qed.
Lemma lem1669051 (g : Prop) (t : Prop) (e : Prop) : term24 g t e.
Proof. exact (@lem1669050 Prop g t e). Qed.
Lemma lem1669052 (n : nat) (x : real) : term25 n x.
Proof. exact (@lem1669051 (Coq.Arith.PeanoNat.Nat.Even n) (term26 n x) ((real_abs x) = x)). Qed.
Lemma lem1669053 (n : nat) (x : real) (g' : Prop) : term27 n x g'.
Proof. exact (@lem1669052 n x g'). Qed.
Lemma lem1669054 (n : nat) (x : real) (g' : Prop) : (term27 n x g') = (term28 n x g').
Proof. exact (eq_refl (term27 n x g')). Qed.
Lemma lem1669055 (n : nat) (x : real) (g' : Prop) : term28 n x g'.
Proof. exact (EQ_MP (@lem1669054 n x g') (@lem1669053 n x g')). Qed.
Lemma lem1669056 (n : nat) (x : real) (g' : Prop) (t' : Prop) : term29 n x g' t'.
Proof. exact (@lem1669055 n x g' t'). Qed.
Lemma lem1669057 (n : nat) (x : real) (g' : Prop) (t' : Prop) : (term29 n x g' t') = (term30 n x g' t').
Proof. exact (eq_refl (term29 n x g' t')). Qed.
Lemma lem1669058 (n : nat) (x : real) (g' : Prop) (t' : Prop) : term30 n x g' t'.
Proof. exact (EQ_MP (@lem1669057 n x g' t') (@lem1669056 n x g' t')). Qed.
Lemma lem1669059 (n : nat) (x : real) (g' : Prop) (t' : Prop) (e' : Prop) : term31 n x g' t' e'.
Proof. exact (@lem1669058 n x g' t' e'). Qed.
Lemma lem1669060 (n : nat) (x : real) (g' : Prop) (t' : Prop) (e' : Prop) : (term31 n x g' t' e') = (term32 n x g' t' e').
Proof. exact (eq_refl (term31 n x g' t' e')). Qed.
Lemma lem1669061 (n : nat) (x : real) (g' : Prop) (t' : Prop) (e' : Prop) : term32 n x g' t' e'.
Proof. exact (EQ_MP (@lem1669060 n x g' t' e') (@lem1669059 n x g' t' e')). Qed.
Lemma lem1669063 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem1669041 n) (@lem1669040 n h1)). Qed.
Lemma lem1669064 (n : nat) (x : real) (t' : Prop) (e' : Prop) : term33 n x t' e'.
Proof. exact (@lem1669061 n x True t' e'). Qed.
Lemma lem1669065 (x : real) (t' : Prop) (e' : Prop) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term34 n x t' e'.
Proof. exact (@lem1669064 n x t' e' (@lem1669063 n h1)). Qed.
Lemma lem1669078 (x : real) : (term1 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1669005 x) (@lem1669004 x)). Qed.
Lemma lem1669079 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1669080 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1669079) (@lem1669078 x)). Qed.
Lemma lem1669081 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1669082 (x : real) : ((term1 x) = (real_abs x)) = ((real_abs x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1669080 x) (@lem1669081 x)). Qed.
Lemma lem1669084 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1669085 (x : real) : (x = x) = True.
Proof. exact (@lem1669084 real x). Qed.
Lemma lem1669086 (x : real) : ((real_abs x) = (real_abs x)) = True.
Proof. exact (@lem1669085 (real_abs x)). Qed.
Lemma lem1669089 (x : real) : ((term1 x) = (real_abs x)) = True.
Proof. exact (TRANS (@lem1669082 x) (@lem1669086 x)). Qed.
Lemma lem1669090 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem1669091 (x : real) (n : nat) : (term26 n x) = (term38 n).
Proof. exact (MK_COMB (@lem1669090 n) (@lem1669089 x)). Qed.
Lemma lem1669093 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1669094 (n : nat) : (term38 n) = True.
Proof. exact (@lem1669093 (n = (NUMERAL 0))). Qed.
Lemma lem1669097 (n : nat) (x : real) : (term26 n x) = True.
Proof. exact (TRANS (@lem1669091 x n) (@lem1669094 n)). Qed.
Lemma lem1669098 (n : nat) (x : real) : term39 n x.
Proof. exact (fun h0 : True => @lem1669097 n x). Qed.
Lemma lem1669099 (x : real) (e' : Prop) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term40 n x e'.
Proof. exact (@lem1669065 x True e' n h1). Qed.
Lemma lem1669100 (x : real) (e' : Prop) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term41 n x e'.
Proof. exact (@lem1669099 x e' n h1 (@lem1669098 n x)). Qed.
Lemma lem1669106 (x : real) : ((real_abs x) = x) = ((real_abs x) = x).
Proof. exact (eq_refl ((real_abs x) = x)). Qed.
Lemma lem1669107 (x : real) : term42 x.
Proof. exact (fun h0 : ~ True => @lem1669106 x). Qed.
Lemma lem1669108 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term43 n x.
Proof. exact (@lem1669100 x ((real_abs x) = x) n h1). Qed.
Lemma lem1669109 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term19 n x) = (term44 x).
Proof. exact (@lem1669108 x n h1 (@lem1669107 x)). Qed.
Lemma lem1669111 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1669112 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem1669111 Prop t2 t1). Qed.
Lemma lem1669113 (x : real) : (term44 x) = True.
Proof. exact (@lem1669112 ((real_abs x) = x) True). Qed.
Lemma lem1669114 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term19 n x) = True.
Proof. exact (TRANS (@lem1669109 x n h1) (@lem1669113 x)). Qed.
Lemma lem1669115 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term12 x n) = (real_pow x n)) = True.
Proof. exact (TRANS (@lem1669045 n x) (@lem1669114 x n h1)). Qed.
Lemma lem1669116 (x : real) (n : nat) : term45 x n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1669115 x n h0). Qed.
Lemma lem1669117 (x : real) (n : nat) : term46 x n.
Proof. exact (@lem1669039 x n True). Qed.
Lemma lem1669118 (x : real) (n : nat) : (term47 x n) = (term48 n).
Proof. exact (@lem1669117 x n (@lem1669116 x n)). Qed.
Lemma lem1669120 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1669121 (n : nat) : (term48 n) = True.
Proof. exact (@lem1669120 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1669122 (x : real) (n : nat) : (term47 x n) = True.
Proof. exact (TRANS (@lem1669118 x n) (@lem1669121 n)). Qed.
Lemma lem1669123 (x : real) : (term49 x) = term50.
Proof. exact (fun_ext (fun n : nat => @lem1669122 x n)). Qed.
Lemma lem1669124 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1669125 (x : real) : (term51 x) = term52.
Proof. exact (MK_COMB (@lem1669124) (@lem1669123 x)). Qed.
Lemma lem1669127 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1669128 (t : Prop) : (term54 t) = t.
Proof. exact (@lem1669127 nat t). Qed.
Lemma lem1669129 : term52 = True.
Proof. exact (@lem1669128 True). Qed.
Lemma lem1669130 (x : real) : (term51 x) = True.
Proof. exact (TRANS (@lem1669125 x) (@lem1669129)). Qed.
Lemma lem1669131 : term55 = term56.
Proof. exact (fun_ext (fun x : real => @lem1669130 x)). Qed.
Lemma lem1669132 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1669133 : term57 = term58.
Proof. exact (MK_COMB (@lem1669132) (@lem1669131)). Qed.
Lemma lem1669135 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1669136 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1669135 real t). Qed.
Lemma lem1669137 : term58 = True.
Proof. exact (@lem1669136 True). Qed.
Lemma lem1669138 : term57 = True.
Proof. exact (TRANS (@lem1669133) (@lem1669137)). Qed.
Lemma lem1669139 : True = term57.
Proof. exact (SYM (@lem1669138)). Qed.
Lemma lem1669140 : term57.
Proof. exact (EQ_MP (@lem1669139) (@lem0)). Qed.
