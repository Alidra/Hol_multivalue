Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MONO_LT_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import EXP_MONO_LE_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem153231 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem153232 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem153231 n m h1)). Qed.
Lemma lem153233 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem153234 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem153233 m n h1)). Qed.
Lemma lem153235 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem153232 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem153234 m n h1)). Qed.
Lemma lem153236 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem153235 m n)). Qed.
Lemma lem153237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153238 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem153237) (@lem153236 m)). Qed.
Lemma lem153239 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem153238 m)). Qed.
Lemma lem153240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153241 : term7 = term8.
Proof. exact (MK_COMB (@lem153240) (@lem153239)). Qed.
Lemma lem153242 : term8.
Proof. exact (EQ_MP (@lem153241) (@lem97961)). Qed.
Lemma lem153243 (t1 : Prop) : term9 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem153244 (t1 : Prop) : (term9 t1) = (term10 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem153245 (t1 : Prop) : term10 t1.
Proof. exact (EQ_MP (@lem153244 t1) (@lem153243 t1)). Qed.
Lemma lem153246 (t1 : Prop) (t2 : Prop) : term11 t1 t2.
Proof. exact (@lem153245 t1 t2). Qed.
Lemma lem153247 (t1 : Prop) (t2 : Prop) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (eq_refl (term11 t1 t2)). Qed.
Lemma lem153248 (t1 : Prop) (t2 : Prop) : term12 t1 t2.
Proof. exact (EQ_MP (@lem153247 t1 t2) (@lem153246 t1 t2)). Qed.
Lemma lem153251 (x : nat) : term13 x.
Proof. exact (@lem153228 x). Qed.
Lemma lem153252 (x : nat) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem153253 (x : nat) : term14 x.
Proof. exact (EQ_MP (@lem153252 x) (@lem153251 x)). Qed.
Lemma lem153254 (x : nat) (y : nat) : term15 x y.
Proof. exact (@lem153253 x y). Qed.
Lemma lem153255 (x : nat) (y : nat) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem153256 (x : nat) (y : nat) : term16 x y.
Proof. exact (EQ_MP (@lem153255 x y) (@lem153254 x y)). Qed.
Lemma lem153257 (x : nat) (y : nat) (n : nat) : term17 x y n.
Proof. exact (@lem153256 x y n). Qed.
Lemma lem153258 (x : nat) (y : nat) (n : nat) : (term17 x y n) = ((term18 x y n) = (term19 x y n)).
Proof. exact (eq_refl (term17 x y n)). Qed.
Lemma lem153260 (m : nat) : term20 m.
Proof. exact (@lem153242 m). Qed.
Lemma lem153261 (m : nat) : (term20 m) = (term4 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem153262 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem153261 m) (@lem153260 m)). Qed.
Lemma lem153263 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem153262 m n). Qed.
Lemma lem153264 (m : nat) (n : nat) : (term21 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem153281 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem153264 m n) (@lem153263 m n)). Qed.
Lemma lem153282 (y : nat) (x : nat) (n : nat) : (term22 x y n) = (term23 y x n).
Proof. exact (@lem153281 (Nat.pow y n) (Nat.pow x n)). Qed.
Lemma lem153284 (x : nat) (y : nat) (n : nat) : (term18 x y n) = (term19 x y n).
Proof. exact (EQ_MP (@lem153258 x y n) (@lem153257 x y n)). Qed.
Lemma lem153285 (y : nat) (x : nat) (n : nat) : (term18 y x n) = (term19 y x n).
Proof. exact (@lem153284 y x n). Qed.
Lemma lem153290 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem153291 (y : nat) (x : nat) (n : nat) : (term23 y x n) = (term24 y x n).
Proof. exact (MK_COMB (@lem153290) (@lem153285 y x n)). Qed.
Lemma lem153293 (t1 : Prop) (t2 : Prop) : (term25 t1 t2) = (term26 t1 t2).
Proof. exact (proj2 (@lem153248 t1 t2)). Qed.
Lemma lem153294 (y : nat) (x : nat) (n : nat) : (term24 y x n) = (term27 y x n).
Proof. exact (@lem153293 (Peano.le y x) (n = (NUMERAL 0))). Qed.
Lemma lem153299 (y : nat) (x : nat) (n : nat) : (term23 y x n) = (term27 y x n).
Proof. exact (TRANS (@lem153291 y x n) (@lem153294 y x n)). Qed.
Lemma lem153300 (y : nat) (x : nat) (n : nat) : (term22 x y n) = (term27 y x n).
Proof. exact (TRANS (@lem153282 y x n) (@lem153299 y x n)). Qed.
Lemma lem153301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153302 (y : nat) (x : nat) (n : nat) : (term28 x y n) = (term29 y x n).
Proof. exact (MK_COMB (@lem153301) (@lem153300 y x n)). Qed.
Lemma lem153306 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem153264 m n) (@lem153263 m n)). Qed.
Lemma lem153307 (y : nat) (x : nat) : (Peano.lt x y) = (term0 y x).
Proof. exact (@lem153306 y x). Qed.
Lemma lem153308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem153309 (y : nat) (x : nat) : (term30 x y) = (term31 y x).
Proof. exact (MK_COMB (@lem153308) (@lem153307 y x)). Qed.
Lemma lem153312 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem153313 (y : nat) (x : nat) (n : nat) : (term33 x y n) = (term27 y x n).
Proof. exact (MK_COMB (@lem153309 y x) (@lem153312 n)). Qed.
Lemma lem153316 (y : nat) (x : nat) (n : nat) : ((term22 x y n) = (term33 x y n)) = ((term27 y x n) = (term27 y x n)).
Proof. exact (MK_COMB (@lem153302 y x n) (@lem153313 y x n)). Qed.
Lemma lem153318 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem153319 (x : Prop) : (x = x) = True.
Proof. exact (@lem153318 Prop x). Qed.
Lemma lem153320 (y : nat) (x : nat) (n : nat) : ((term27 y x n) = (term27 y x n)) = True.
Proof. exact (@lem153319 (term27 y x n)). Qed.
Lemma lem153321 (x : nat) (y : nat) (n : nat) : ((term22 x y n) = (term33 x y n)) = True.
Proof. exact (TRANS (@lem153316 y x n) (@lem153320 y x n)). Qed.
Lemma lem153322 (x : nat) (y : nat) : (term34 x y) = term35.
Proof. exact (fun_ext (fun n : nat => @lem153321 x y n)). Qed.
Lemma lem153323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153324 (x : nat) (y : nat) : (term36 x y) = term37.
Proof. exact (MK_COMB (@lem153323) (@lem153322 x y)). Qed.
Lemma lem153326 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem153327 (t : Prop) : (term39 t) = t.
Proof. exact (@lem153326 nat t). Qed.
Lemma lem153328 : term37 = True.
Proof. exact (@lem153327 True). Qed.
Lemma lem153329 (x : nat) (y : nat) : (term36 x y) = True.
Proof. exact (TRANS (@lem153324 x y) (@lem153328)). Qed.
Lemma lem153330 (x : nat) : (term40 x) = term35.
Proof. exact (fun_ext (fun y : nat => @lem153329 x y)). Qed.
Lemma lem153331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153332 (x : nat) : (term41 x) = term37.
Proof. exact (MK_COMB (@lem153331) (@lem153330 x)). Qed.
Lemma lem153334 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem153335 (t : Prop) : (term39 t) = t.
Proof. exact (@lem153334 nat t). Qed.
Lemma lem153336 : term37 = True.
Proof. exact (@lem153335 True). Qed.
Lemma lem153337 (x : nat) : (term41 x) = True.
Proof. exact (TRANS (@lem153332 x) (@lem153336)). Qed.
Lemma lem153338 : term42 = term35.
Proof. exact (fun_ext (fun x : nat => @lem153337 x)). Qed.
Lemma lem153339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem153340 : term43 = term37.
Proof. exact (MK_COMB (@lem153339) (@lem153338)). Qed.
Lemma lem153342 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem153343 (t : Prop) : (term39 t) = t.
Proof. exact (@lem153342 nat t). Qed.
Lemma lem153344 : term37 = True.
Proof. exact (@lem153343 True). Qed.
Lemma lem153345 : term43 = True.
Proof. exact (TRANS (@lem153340) (@lem153344)). Qed.
Lemma lem153346 : True = term43.
Proof. exact (SYM (@lem153345)). Qed.
Lemma lem153347 : term43.
Proof. exact (EQ_MP (@lem153346) (@lem0)). Qed.
