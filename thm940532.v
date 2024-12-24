Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm940532_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import BIT0_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXP_2_spec.
Require Import MULT_2_spec.
Require Import MULT_AC_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem940074 : term0.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem940075 : term1.
Proof. exact (proj2 (@lem940074)). Qed.
Lemma lem940076 : term2.
Proof. exact (proj2 (@lem940075)). Qed.
Lemma lem940118 : term3.
Proof. exact (proj1 (@lem940076)). Qed.
Lemma lem940119 (n : nat) : term4 n.
Proof. exact (@lem940118 n). Qed.
Lemma lem940120 (n : nat) : (term4 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem940122 : term5.
Proof. exact (proj1 (@lem940075)). Qed.
Lemma lem940123 (n : nat) : term6 n.
Proof. exact (@lem940122 n). Qed.
Lemma lem940124 (n : nat) : (term6 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem940127 : term7.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem940128 (m : nat) : term8 m.
Proof. exact (@lem940127 m). Qed.
Lemma lem940129 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem940130 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem940129 m) (@lem940128 m)). Qed.
Lemma lem940131 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem940130 m n). Qed.
Lemma lem940132 (m : nat) (n : nat) : (term10 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem940134 (m : nat) : term11 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem940135 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem940136 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem940135 m) (@lem940134 m)). Qed.
Lemma lem940137 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem940136 m n). Qed.
Lemma lem940138 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem940139 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem940138 m n) (@lem940137 m n)). Qed.
Lemma lem940140 (m : nat) (n : nat) (p : nat) : term15 m n p.
Proof. exact (@lem940139 m n p). Qed.
Lemma lem940141 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term16 m n p)).
Proof. exact (eq_refl (term15 m n p)). Qed.
Lemma lem940143 {A : Type'} (x : A) : term17 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem940144 {A : Type'} (x : A) : (term17 A x) = ((x = x) = True).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem940146 (n : nat) (m : nat) (p : nat) : term18 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem940153 (m : nat) (n : nat) (p : nat) : (term19 m n p) = (term20 m n p).
Proof. exact (proj1 (@lem940146 n m p)). Qed.
Lemma lem940154 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (@lem940153 term23 m (term24 n)). Qed.
Lemma lem940156 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term20 n m p).
Proof. exact (proj2 (@lem940146 n m p)). Qed.
Lemma lem940157 (m : nat) (n : nat) : (term22 m n) = (term25 m n).
Proof. exact (@lem940156 m term23 (term24 n)). Qed.
Lemma lem940164 (m : nat) (n : nat) : (term21 m n) = (term25 m n).
Proof. exact (TRANS (@lem940154 m n) (@lem940157 m n)). Qed.
Lemma lem940172 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem940173 (n : nat) : (term24 n) = (term26 n).
Proof. exact (@lem940172 n term23). Qed.
Lemma lem940177 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem940178 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem940177) (@lem940173 n)). Qed.
Lemma lem940180 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term20 n m p).
Proof. exact (proj2 (@lem940146 n m p)). Qed.
Lemma lem940181 (n : nat) : (term29 n) = (term30 n).
Proof. exact (@lem940180 n term23 term23). Qed.
Lemma lem940191 (n : nat) : (term28 n) = (term30 n).
Proof. exact (TRANS (@lem940178 n) (@lem940181 n)). Qed.
Lemma lem940192 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem940193 (m : nat) (n : nat) : (term25 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem940192 m) (@lem940191 n)). Qed.
Lemma lem940200 (m : nat) (n : nat) : (term21 m n) = (term31 m n).
Proof. exact (TRANS (@lem940164 m n) (@lem940193 m n)). Qed.
Lemma lem940201 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940202 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem940201) (@lem940200 m n)). Qed.
Lemma lem940210 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term20 n m p).
Proof. exact (proj2 (@lem940146 n m p)). Qed.
Lemma lem940211 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (@lem940210 m term23 n). Qed.
Lemma lem940219 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem940220 (n : nat) : (term24 n) = (term26 n).
Proof. exact (@lem940219 n term23). Qed.
Lemma lem940224 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem940225 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem940224 m) (@lem940220 n)). Qed.
Lemma lem940232 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem940211 m n) (@lem940225 m n)). Qed.
Lemma lem940233 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem940234 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem940233) (@lem940232 m n)). Qed.
Lemma lem940236 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term20 n m p).
Proof. exact (proj2 (@lem940146 n m p)). Qed.
Lemma lem940237 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (@lem940236 m term23 (term26 n)). Qed.
Lemma lem940245 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term20 n m p).
Proof. exact (proj2 (@lem940146 n m p)). Qed.
Lemma lem940246 (n : nat) : (term29 n) = (term30 n).
Proof. exact (@lem940245 n term23 term23). Qed.
Lemma lem940256 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem940257 (m : nat) (n : nat) : (term39 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem940256 m) (@lem940246 n)). Qed.
Lemma lem940264 (m : nat) (n : nat) : (term38 m n) = (term31 m n).
Proof. exact (TRANS (@lem940237 m n) (@lem940257 m n)). Qed.
Lemma lem940265 (m : nat) (n : nat) : (term37 m n) = (term31 m n).
Proof. exact (TRANS (@lem940234 m n) (@lem940264 m n)). Qed.
Lemma lem940266 (m : nat) (n : nat) : ((term21 m n) = (term37 m n)) = ((term31 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem940202 m n) (@lem940265 m n)). Qed.
Lemma lem940268 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem940144 A x) (@lem940143 A x)). Qed.
Lemma lem940269 (x : nat) : (x = x) = True.
Proof. exact (@lem940268 nat x). Qed.
Lemma lem940270 (m : nat) (n : nat) : ((term31 m n) = (term31 m n)) = True.
Proof. exact (@lem940269 (term31 m n)). Qed.
Lemma lem940271 (m : nat) (n : nat) : ((term21 m n) = (term37 m n)) = True.
Proof. exact (TRANS (@lem940266 m n) (@lem940270 m n)). Qed.
Lemma lem940272 (m : nat) (n : nat) : True = ((term21 m n) = (term37 m n)).
Proof. exact (SYM (@lem940271 m n)). Qed.
Lemma lem940274 (n : nat) : term40 n.
Proof. exact (@lem88196 n). Qed.
Lemma lem940275 (n : nat) : (term40 n) = ((term41 n) = (Nat.mul n n)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem940278 (n : nat) (h1 : (term24 n) = (Nat.add n n)) : (term24 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem940279 (n : nat) (h1 : (term24 n) = (Nat.add n n)) : (Nat.add n n) = (term24 n).
Proof. exact (SYM (@lem940278 n h1)). Qed.
Lemma lem940280 (n : nat) (h1 : (Nat.add n n) = (term24 n)) : (Nat.add n n) = (term24 n).
Proof. exact (h1). Qed.
Lemma lem940281 (n : nat) (h1 : (Nat.add n n) = (term24 n)) : (term24 n) = (Nat.add n n).
Proof. exact (SYM (@lem940280 n h1)). Qed.
Lemma lem940282 (n : nat) : ((term24 n) = (Nat.add n n)) = ((Nat.add n n) = (term24 n)).
Proof. exact (prop_ext (fun h1 : (term24 n) = (Nat.add n n) => @lem940279 n h1) (fun h1 : (Nat.add n n) = (term24 n) => @lem940281 n h1)). Qed.
Lemma lem940283 : term42 = term43.
Proof. exact (fun_ext (fun n : nat => @lem940282 n)). Qed.
Lemma lem940284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem940285 : term44 = term45.
Proof. exact (MK_COMB (@lem940284) (@lem940283)). Qed.
Lemma lem940286 : term45.
Proof. exact (EQ_MP (@lem940285) (@lem84996)). Qed.
Lemma lem940287 (n : nat) : term46 n.
Proof. exact (@lem940286 n). Qed.
Lemma lem940288 (n : nat) : (term46 n) = ((Nat.add n n) = (term24 n)).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem940290 (n : nat) : term47 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem940291 (n : nat) : (term47 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem940293 (two : nat) (h1 : term23 = two) : term23 = two.
Proof. exact (h1). Qed.
Lemma lem940294 (two : nat) (h1 : term23 = two) : term48.
Proof. exact (ex_intro term49 two (@lem940293 two h1)). Qed.
Lemma lem940295 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem940296 (h1 : term48) : term48.
Proof. exact (ex_elim (@lem940295 h1) (fun two : nat => fun h0 : term49 two => @lem940294 two h0)). Qed.
Lemma lem940297 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem940298 : term48.
Proof. exact (ex_intro term49 term23 (@lem940297)). Qed.
Lemma lem940299 : term48 = term48.
Proof. exact (prop_ext (fun h1 : term48 => @lem940296 h1) (fun h1 : term48 => @lem940298)). Qed.
Lemma lem940300 : term48.
Proof. exact (EQ_MP (@lem940299) (@lem940298)). Qed.
Lemma lem940301 (two : nat) (h1 : term23 = two) : term23 = two.
Proof. exact (h1). Qed.
Lemma lem940303 (two : nat) (h1 : term23 = two) : term23 = two.
Proof. exact (h1). Qed.
Lemma lem940304 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem940305 (m : nat) (two : nat) (h1 : term23 = two) : (term41 m) = (Nat.pow m two).
Proof. exact (MK_COMB (@lem940304 m) (@lem940303 two h1)). Qed.
Lemma lem940306 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940307 (m : nat) (two : nat) (h1 : term23 = two) : (term50 m) = (term51 m two).
Proof. exact (MK_COMB (@lem940306) (@lem940305 m two h1)). Qed.
Lemma lem940308 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem940309 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((term41 m) = n) = ((Nat.pow m two) = n).
Proof. exact (MK_COMB (@lem940307 m two h1) (@lem940308 n)). Qed.
Lemma lem940310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem940311 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (term52 m n) = (term53 m two n).
Proof. exact (MK_COMB (@lem940310) (@lem940309 m n two h1)). Qed.
Lemma lem940313 (two : nat) (h1 : term23 = two) : term23 = two.
Proof. exact (h1). Qed.
Lemma lem940314 (m : nat) : (term54 m) = (term54 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem940315 (m : nat) (two : nat) (h1 : term23 = two) : (term55 m) = (term56 m two).
Proof. exact (MK_COMB (@lem940314 m) (@lem940313 two h1)). Qed.
Lemma lem940316 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940317 (m : nat) (two : nat) (h1 : term23 = two) : (term57 m) = (term58 m two).
Proof. exact (MK_COMB (@lem940316) (@lem940315 m two h1)). Qed.
Lemma lem940318 (n : nat) : (term59 n) = (term59 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem940319 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((term55 m) = (term59 n)) = ((term56 m two) = (term59 n)).
Proof. exact (MK_COMB (@lem940317 m two h1) (@lem940318 n)). Qed.
Lemma lem940320 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (((term41 m) = n) = ((term55 m) = (term59 n))) = (((Nat.pow m two) = n) = ((term56 m two) = (term59 n))).
Proof. exact (MK_COMB (@lem940311 m n two h1) (@lem940319 m n two h1)). Qed.
Lemma lem940321 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (((Nat.pow m two) = n) = ((term56 m two) = (term59 n))) = (((term41 m) = n) = ((term55 m) = (term59 n))).
Proof. exact (SYM (@lem940320 m n two h1)). Qed.
Lemma lem940329 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940291 n) (@lem940290 n)). Qed.
Lemma lem940330 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem940329 m). Qed.
Lemma lem940331 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem940332 (m : nat) : (term54 m) = (term60 m).
Proof. exact (MK_COMB (@lem940331) (@lem940330 m)). Qed.
Lemma lem940333 (two : nat) : two = two.
Proof. exact (eq_refl two). Qed.
Lemma lem940334 (m : nat) (two : nat) : (term56 m two) = (term61 m two).
Proof. exact (MK_COMB (@lem940332 m) (@lem940333 two)). Qed.
Lemma lem940335 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940336 (m : nat) (two : nat) : (term58 m two) = (term62 m two).
Proof. exact (MK_COMB (@lem940335) (@lem940334 m two)). Qed.
Lemma lem940338 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940291 n) (@lem940290 n)). Qed.
Lemma lem940339 (n : nat) : (term59 n) = (term63 n).
Proof. exact (@lem940338 (BIT0 n)). Qed.
Lemma lem940341 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940291 n) (@lem940290 n)). Qed.
Lemma lem940342 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem940343 (n : nat) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem940342) (@lem940341 n)). Qed.
Lemma lem940345 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem940291 n) (@lem940290 n)). Qed.
Lemma lem940346 (n : nat) : (term63 n) = (term66 n).
Proof. exact (MK_COMB (@lem940343 n) (@lem940345 n)). Qed.
Lemma lem940347 (n : nat) : (term59 n) = (term66 n).
Proof. exact (TRANS (@lem940339 n) (@lem940346 n)). Qed.
Lemma lem940348 (m : nat) (two : nat) (n : nat) : ((term56 m two) = (term59 n)) = ((term61 m two) = (term66 n)).
Proof. exact (MK_COMB (@lem940336 m two) (@lem940347 n)). Qed.
Lemma lem940351 (m : nat) (two : nat) (n : nat) : (term53 m two n) = (term53 m two n).
Proof. exact (eq_refl (term53 m two n)). Qed.
Lemma lem940352 (m : nat) (two : nat) (n : nat) : (((Nat.pow m two) = n) = ((term56 m two) = (term59 n))) = (((Nat.pow m two) = n) = ((term61 m two) = (term66 n))).
Proof. exact (MK_COMB (@lem940351 m two n) (@lem940348 m two n)). Qed.
Lemma lem940355 (m : nat) (two : nat) (n : nat) : (((Nat.pow m two) = n) = ((term61 m two) = (term66 n))) = (((Nat.pow m two) = n) = ((term56 m two) = (term59 n))).
Proof. exact (SYM (@lem940352 m two n)). Qed.
Lemma lem940356 (two : nat) (h1 : term23 = two) : two = term23.
Proof. exact (SYM (@lem940301 two h1)). Qed.
Lemma lem940357 (m : nat) (n : nat) : (term67 m n) = (term67 m n).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem940358 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (term68 m n two) = (term69 m n).
Proof. exact (MK_COMB (@lem940357 m n) (@lem940356 two h1)). Qed.
Lemma lem940359 (m : nat) (n : nat) : (term69 m n) = (((term41 m) = n) = ((term70 m) = (term66 n))).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem940360 (m : nat) (n : nat) (two : nat) : (term71 m n two) = (term71 m n two).
Proof. exact (eq_refl (term71 m n two)). Qed.
Lemma lem940361 (two : nat) (m : nat) (n : nat) : ((term68 m n two) = (term69 m n)) = ((term68 m n two) = (((term41 m) = n) = ((term70 m) = (term66 n)))).
Proof. exact (MK_COMB (@lem940360 m n two) (@lem940359 m n)). Qed.
Lemma lem940362 (m : nat) (two : nat) (n : nat) : (term68 m n two) = (((Nat.pow m two) = n) = ((term61 m two) = (term66 n))).
Proof. exact (eq_refl (term68 m n two)). Qed.
Lemma lem940363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem940364 (m : nat) (two : nat) (n : nat) : (term71 m n two) = (term72 m two n).
Proof. exact (MK_COMB (@lem940363) (@lem940362 m two n)). Qed.
Lemma lem940365 (m : nat) (n : nat) : (((term41 m) = n) = ((term70 m) = (term66 n))) = (((term41 m) = n) = ((term70 m) = (term66 n))).
Proof. exact (eq_refl (((term41 m) = n) = ((term70 m) = (term66 n)))). Qed.
Lemma lem940366 (two : nat) (m : nat) (n : nat) : ((term68 m n two) = (((term41 m) = n) = ((term70 m) = (term66 n)))) = ((((Nat.pow m two) = n) = ((term61 m two) = (term66 n))) = (((term41 m) = n) = ((term70 m) = (term66 n)))).
Proof. exact (MK_COMB (@lem940364 m two n) (@lem940365 m n)). Qed.
Lemma lem940367 (two : nat) (m : nat) (n : nat) : ((term68 m n two) = (term69 m n)) = ((((Nat.pow m two) = n) = ((term61 m two) = (term66 n))) = (((term41 m) = n) = ((term70 m) = (term66 n)))).
Proof. exact (TRANS (@lem940361 two m n) (@lem940366 two m n)). Qed.
Lemma lem940368 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (((Nat.pow m two) = n) = ((term61 m two) = (term66 n))) = (((term41 m) = n) = ((term70 m) = (term66 n))).
Proof. exact (EQ_MP (@lem940367 two m n) (@lem940358 m n two h1)). Qed.
Lemma lem940369 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (((term41 m) = n) = ((term70 m) = (term66 n))) = (((Nat.pow m two) = n) = ((term61 m two) = (term66 n))).
Proof. exact (SYM (@lem940368 m n two h1)). Qed.
Lemma lem940379 (n : nat) : (Nat.add n n) = (term24 n).
Proof. exact (EQ_MP (@lem940288 n) (@lem940287 n)). Qed.
Lemma lem940380 (m : nat) : (Nat.add m m) = (term24 m).
Proof. exact (@lem940379 m). Qed.
Lemma lem940381 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem940382 (m : nat) : (term60 m) = (term73 m).
Proof. exact (MK_COMB (@lem940381) (@lem940380 m)). Qed.
Lemma lem940383 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem940384 (m : nat) : (term70 m) = (term74 m).
Proof. exact (MK_COMB (@lem940382 m) (@lem940383)). Qed.
Lemma lem940385 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940386 (m : nat) : (term75 m) = (term76 m).
Proof. exact (MK_COMB (@lem940385) (@lem940384 m)). Qed.
Lemma lem940388 (n : nat) : (Nat.add n n) = (term24 n).
Proof. exact (EQ_MP (@lem940288 n) (@lem940287 n)). Qed.
Lemma lem940389 (n : nat) : (term66 n) = (term77 n).
Proof. exact (@lem940388 (Nat.add n n)). Qed.
Lemma lem940391 (n : nat) : (Nat.add n n) = (term24 n).
Proof. exact (EQ_MP (@lem940288 n) (@lem940287 n)). Qed.
Lemma lem940392 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem940393 (n : nat) : (term77 n) = (term28 n).
Proof. exact (MK_COMB (@lem940392) (@lem940391 n)). Qed.
Lemma lem940394 (n : nat) : (term66 n) = (term28 n).
Proof. exact (TRANS (@lem940389 n) (@lem940393 n)). Qed.
Lemma lem940395 (m : nat) (n : nat) : ((term70 m) = (term66 n)) = ((term74 m) = (term28 n)).
Proof. exact (MK_COMB (@lem940386 m) (@lem940394 n)). Qed.
Lemma lem940398 (m : nat) (n : nat) : (term52 m n) = (term52 m n).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem940399 (m : nat) (n : nat) : (((term41 m) = n) = ((term70 m) = (term66 n))) = (((term41 m) = n) = ((term74 m) = (term28 n))).
Proof. exact (MK_COMB (@lem940398 m n) (@lem940395 m n)). Qed.
Lemma lem940402 (m : nat) (n : nat) : (((term41 m) = n) = ((term74 m) = (term28 n))) = (((term41 m) = n) = ((term70 m) = (term66 n))).
Proof. exact (SYM (@lem940399 m n)). Qed.
Lemma lem940408 (n : nat) : (term41 n) = (Nat.mul n n).
Proof. exact (EQ_MP (@lem940275 n) (@lem940274 n)). Qed.
Lemma lem940409 (m : nat) : (term41 m) = (Nat.mul m m).
Proof. exact (@lem940408 m). Qed.
Lemma lem940410 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940411 (m : nat) : (term50 m) = (term78 m).
Proof. exact (MK_COMB (@lem940410) (@lem940409 m)). Qed.
Lemma lem940412 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem940413 (m : nat) (n : nat) : ((term41 m) = n) = ((Nat.mul m m) = n).
Proof. exact (MK_COMB (@lem940411 m) (@lem940412 n)). Qed.
Lemma lem940416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem940417 (m : nat) (n : nat) : (term52 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem940416) (@lem940413 m n)). Qed.
Lemma lem940421 (n : nat) : (term41 n) = (Nat.mul n n).
Proof. exact (EQ_MP (@lem940275 n) (@lem940274 n)). Qed.
Lemma lem940422 (m : nat) : (term74 m) = (term80 m).
Proof. exact (@lem940421 (term24 m)). Qed.
Lemma lem940423 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940424 (m : nat) : (term76 m) = (term81 m).
Proof. exact (MK_COMB (@lem940423) (@lem940422 m)). Qed.
Lemma lem940425 (n : nat) : (term28 n) = (term28 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem940426 (m : nat) (n : nat) : ((term74 m) = (term28 n)) = ((term80 m) = (term28 n)).
Proof. exact (MK_COMB (@lem940424 m) (@lem940425 n)). Qed.
Lemma lem940429 (m : nat) (n : nat) : (((term41 m) = n) = ((term74 m) = (term28 n))) = (((Nat.mul m m) = n) = ((term80 m) = (term28 n))).
Proof. exact (MK_COMB (@lem940417 m n) (@lem940426 m n)). Qed.
Lemma lem940432 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term80 m) = (term28 n))) = (((term41 m) = n) = ((term74 m) = (term28 n))).
Proof. exact (SYM (@lem940429 m n)). Qed.
Lemma lem940440 (m : nat) (n : nat) : (term21 m n) = (term37 m n).
Proof. exact (EQ_MP (@lem940272 m n) (@lem0)). Qed.
Lemma lem940441 (m : nat) : (term80 m) = (term82 m).
Proof. exact (@lem940440 m m). Qed.
Lemma lem940442 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem940443 (m : nat) : (term81 m) = (term83 m).
Proof. exact (MK_COMB (@lem940442) (@lem940441 m)). Qed.
Lemma lem940444 (n : nat) : (term28 n) = (term28 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem940445 (m : nat) (n : nat) : ((term80 m) = (term28 n)) = ((term82 m) = (term28 n)).
Proof. exact (MK_COMB (@lem940443 m) (@lem940444 n)). Qed.
Lemma lem940448 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem940449 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term80 m) = (term28 n))) = (((Nat.mul m m) = n) = ((term82 m) = (term28 n))).
Proof. exact (MK_COMB (@lem940448 m n) (@lem940445 m n)). Qed.
Lemma lem940452 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term82 m) = (term28 n))) = (((Nat.mul m m) = n) = ((term80 m) = (term28 n))).
Proof. exact (SYM (@lem940449 m n)). Qed.
Lemma lem940458 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term16 m n p).
Proof. exact (EQ_MP (@lem940141 m n p) (@lem940140 m n p)). Qed.
Lemma lem940459 (m : nat) (n : nat) : ((term82 m) = (term28 n)) = (term84 m n).
Proof. exact (@lem940458 term23 (term85 m) (term24 n)). Qed.
Lemma lem940463 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem940132 m n) (@lem940131 m n)). Qed.
Lemma lem940464 : (term23 = (NUMERAL 0)) = (term86 = 0).
Proof. exact (@lem940463 term86 0). Qed.
Lemma lem940466 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem940124 n) (@lem940123 n)). Qed.
Lemma lem940467 : (term86 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem940466 (BIT1 0)). Qed.
Lemma lem940469 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem940120 n) (@lem940119 n)). Qed.
Lemma lem940470 : ((BIT1 0) = 0) = False.
Proof. exact (@lem940469 0). Qed.
Lemma lem940471 : (term86 = 0) = False.
Proof. exact (TRANS (@lem940467) (@lem940470)). Qed.
Lemma lem940472 : (term23 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem940464) (@lem940471)). Qed.
Lemma lem940473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem940474 : term87 = (or False).
Proof. exact (MK_COMB (@lem940473) (@lem940472)). Qed.
Lemma lem940476 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term16 m n p).
Proof. exact (EQ_MP (@lem940141 m n p) (@lem940140 m n p)). Qed.
Lemma lem940477 (m : nat) (n : nat) : ((term85 m) = (term24 n)) = (term88 m n).
Proof. exact (@lem940476 term23 (Nat.mul m m) n). Qed.
Lemma lem940481 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem940132 m n) (@lem940131 m n)). Qed.
Lemma lem940482 : (term23 = (NUMERAL 0)) = (term86 = 0).
Proof. exact (@lem940481 term86 0). Qed.
Lemma lem940484 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem940124 n) (@lem940123 n)). Qed.
Lemma lem940485 : (term86 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem940484 (BIT1 0)). Qed.
Lemma lem940487 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem940120 n) (@lem940119 n)). Qed.
Lemma lem940488 : ((BIT1 0) = 0) = False.
Proof. exact (@lem940487 0). Qed.
Lemma lem940489 : (term86 = 0) = False.
Proof. exact (TRANS (@lem940485) (@lem940488)). Qed.
Lemma lem940490 : (term23 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem940482) (@lem940489)). Qed.
Lemma lem940491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem940492 : term87 = (or False).
Proof. exact (MK_COMB (@lem940491) (@lem940490)). Qed.
Lemma lem940495 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((Nat.mul m m) = n).
Proof. exact (eq_refl ((Nat.mul m m) = n)). Qed.
Lemma lem940496 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem940492) (@lem940495 m n)). Qed.
Lemma lem940498 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem940499 (m : nat) (n : nat) : (term89 m n) = ((Nat.mul m m) = n).
Proof. exact (@lem940498 ((Nat.mul m m) = n)). Qed.
Lemma lem940502 (m : nat) (n : nat) : (term88 m n) = ((Nat.mul m m) = n).
Proof. exact (TRANS (@lem940496 m n) (@lem940499 m n)). Qed.
Lemma lem940503 (m : nat) (n : nat) : ((term85 m) = (term24 n)) = ((Nat.mul m m) = n).
Proof. exact (TRANS (@lem940477 m n) (@lem940502 m n)). Qed.
Lemma lem940504 (m : nat) (n : nat) : (term84 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem940474) (@lem940503 m n)). Qed.
Lemma lem940506 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem940507 (m : nat) (n : nat) : (term89 m n) = ((Nat.mul m m) = n).
Proof. exact (@lem940506 ((Nat.mul m m) = n)). Qed.
Lemma lem940510 (m : nat) (n : nat) : (term84 m n) = ((Nat.mul m m) = n).
Proof. exact (TRANS (@lem940504 m n) (@lem940507 m n)). Qed.
Lemma lem940511 (m : nat) (n : nat) : ((term82 m) = (term28 n)) = ((Nat.mul m m) = n).
Proof. exact (TRANS (@lem940459 m n) (@lem940510 m n)). Qed.
Lemma lem940512 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem940513 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term82 m) = (term28 n))) = (((Nat.mul m m) = n) = ((Nat.mul m m) = n)).
Proof. exact (MK_COMB (@lem940512 m n) (@lem940511 m n)). Qed.
Lemma lem940515 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem940516 (x : Prop) : (x = x) = True.
Proof. exact (@lem940515 Prop x). Qed.
Lemma lem940517 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((Nat.mul m m) = n)) = True.
Proof. exact (@lem940516 ((Nat.mul m m) = n)). Qed.
Lemma lem940518 (m : nat) (n : nat) : (((Nat.mul m m) = n) = ((term82 m) = (term28 n))) = True.
Proof. exact (TRANS (@lem940513 m n) (@lem940517 m n)). Qed.
Lemma lem940519 (m : nat) (n : nat) : True = (((Nat.mul m m) = n) = ((term82 m) = (term28 n))).
Proof. exact (SYM (@lem940518 m n)). Qed.
Lemma lem940520 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term82 m) = (term28 n)).
Proof. exact (EQ_MP (@lem940519 m n) (@lem0)). Qed.
Lemma lem940521 (m : nat) (n : nat) : ((Nat.mul m m) = n) = ((term80 m) = (term28 n)).
Proof. exact (EQ_MP (@lem940452 m n) (@lem940520 m n)). Qed.
Lemma lem940522 (m : nat) (n : nat) : ((term41 m) = n) = ((term74 m) = (term28 n)).
Proof. exact (EQ_MP (@lem940432 m n) (@lem940521 m n)). Qed.
Lemma lem940524 (m : nat) (n : nat) : ((term41 m) = n) = ((term70 m) = (term66 n)).
Proof. exact (EQ_MP (@lem940402 m n) (@lem940522 m n)). Qed.
Lemma lem940525 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((Nat.pow m two) = n) = ((term61 m two) = (term66 n)).
Proof. exact (EQ_MP (@lem940369 m n two h1) (@lem940524 m n)). Qed.
Lemma lem940526 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((Nat.pow m two) = n) = ((term56 m two) = (term59 n)).
Proof. exact (EQ_MP (@lem940355 m two n) (@lem940525 m n two h1)). Qed.
Lemma lem940527 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : (term23 = two) = (((Nat.pow m two) = n) = ((term56 m two) = (term59 n))).
Proof. exact (prop_ext (fun h2 : term23 = two => @lem940526 m n two h1) (fun h2 : ((Nat.pow m two) = n) = ((term56 m two) = (term59 n)) => @lem940301 two h1)). Qed.
Lemma lem940528 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((Nat.pow m two) = n) = ((term56 m two) = (term59 n)).
Proof. exact (EQ_MP (@lem940527 m n two h1) (@lem940301 two h1)). Qed.
Lemma lem940529 (m : nat) (n : nat) (two : nat) (h1 : term23 = two) : ((term41 m) = n) = ((term55 m) = (term59 n)).
Proof. exact (EQ_MP (@lem940321 m n two h1) (@lem940528 m n two h1)). Qed.
Lemma lem940532 (m : nat) (n : nat) : ((term41 m) = n) = ((term55 m) = (term59 n)).
Proof. exact (ex_elim (@lem940300) (fun two : nat => fun h0 : term49 two => @lem940529 m n two h0)). Qed.
