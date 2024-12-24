Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_ID_term_abbrevs.
Require Import LE_0_spec.
Require Import SUM_CLAUSES_NUMSEG_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm15249_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982777_spec.
Require Import thm1982779_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm513079_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7553969 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem7553970 : term1.
Proof. exact (proj2 (@lem7553969)). Qed.
Lemma lem7553971 : term2.
Proof. exact (proj2 (@lem7553970)). Qed.
Lemma lem7553972 : term3.
Proof. exact (proj2 (@lem7553971)). Qed.
Lemma lem7553973 : term4.
Proof. exact (proj2 (@lem7553972)). Qed.
Lemma lem7553974 : term5.
Proof. exact (proj2 (@lem7553973)). Qed.
Lemma lem7553975 : term6.
Proof. exact (proj2 (@lem7553974)). Qed.
Lemma lem7553976 : term7.
Proof. exact (proj2 (@lem7553975)). Qed.
Lemma lem7553977 : term8.
Proof. exact (proj2 (@lem7553976)). Qed.
Lemma lem7553978 : term9.
Proof. exact (proj2 (@lem7553977)). Qed.
Lemma lem7553979 (m : nat) : term10 m.
Proof. exact (@lem7553978 m). Qed.
Lemma lem7553980 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem7553981 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem7553980 m) (@lem7553979 m)). Qed.
Lemma lem7553982 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem7553981 m n). Qed.
Lemma lem7553983 (m : nat) (n : nat) : (term12 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem7554006 : term13.
Proof. exact (proj1 (@lem7553974)). Qed.
Lemma lem7554007 (n : nat) : term14 n.
Proof. exact (@lem7554006 n). Qed.
Lemma lem7554008 (n : nat) : (term14 n) = ((0 = (BIT1 n)) = False).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem7554023 : term15.
Proof. exact (proj1 (@lem7553969)). Qed.
Lemma lem7554024 (m : nat) : term16 m.
Proof. exact (@lem7554023 m). Qed.
Lemma lem7554025 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem7554026 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem7554025 m) (@lem7554024 m)). Qed.
Lemma lem7554027 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem7554026 m n). Qed.
Lemma lem7554028 (m : nat) (n : nat) : (term18 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem7554261 : term19.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem7554262 : term20.
Proof. exact (proj2 (@lem7554261)). Qed.
Lemma lem7554273 : term21.
Proof. exact (proj1 (@lem7554261)). Qed.
Lemma lem7554274 (n : nat) : term22 n.
Proof. exact (@lem7554273 n). Qed.
Lemma lem7554275 (n : nat) : (term22 n) = ((term23 n) = (term24 n)).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem7554280 (n : nat) : term25 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7554281 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem7554282 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem7554281 n) (@lem7554280 n)). Qed.
Lemma lem7554283 (n : nat) : (term26 n) = ((term26 n) = True).
Proof. exact (@lem7 (term26 n)). Qed.
Lemma lem7554285 (f : nat -> real) : term27 f.
Proof. exact (proj2 (@lem7221724 f)). Qed.
Lemma lem7554286 (f : nat -> real) (m : nat) : term28 f m.
Proof. exact (@lem7554285 f m). Qed.
Lemma lem7554287 (m : nat) (f : nat -> real) : (term28 f m) = (term29 m f).
Proof. exact (eq_refl (term28 f m)). Qed.
Lemma lem7554288 (m : nat) (f : nat -> real) : term29 m f.
Proof. exact (EQ_MP (@lem7554287 m f) (@lem7554286 f m)). Qed.
Lemma lem7554289 (m : nat) (f : nat -> real) (n : nat) : term30 m f n.
Proof. exact (@lem7554288 m f n). Qed.
Lemma lem7554290 (m : nat) (n : nat) (f : nat -> real) : (term30 m f n) = ((term31 m n f) = (term32 m n f)).
Proof. exact (eq_refl (term30 m f n)). Qed.
Lemma lem7554292 (f : nat -> real) : term33 f.
Proof. exact (proj1 (@lem7221724 f)). Qed.
Lemma lem7554293 (f : nat -> real) (m : nat) : term34 f m.
Proof. exact (@lem7554292 f m). Qed.
Lemma lem7554294 (m : nat) (f : nat -> real) : (term34 f m) = ((term35 m f) = (term36 m f)).
Proof. exact (eq_refl (term34 f m)). Qed.
Lemma lem7554296 (p : real -> real) : term37 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7554297 (p : real -> real) : (term37 p) = ((polynomial_function p) = (term38 p)).
Proof. exact (eq_refl (term37 p)). Qed.
Lemma lem7554300 (p : real -> real) : (polynomial_function p) = (term38 p).
Proof. exact (EQ_MP (@lem7554297 p) (@lem7554296 p)). Qed.
Lemma lem7554301 : term39 = term40.
Proof. exact (@lem7554300 term41). Qed.
Lemma lem7554317 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554318 (f : real -> real) (y : real) : (term43 f y) = (f y).
Proof. exact (@lem7554317 real real f y). Qed.
Lemma lem7554319 (x : real) : (term44 x) = (term45 x).
Proof. exact (@lem7554318 term41 x). Qed.
Lemma lem7554320 (x : real) : (term45 x) = x.
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem7554321 : term46 = term41.
Proof. exact (fun_ext (fun x : real => @lem7554320 x)). Qed.
Lemma lem7554322 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7554323 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem7554321) (@lem7554322 x)). Qed.
Lemma lem7554324 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554325 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem7554324) (@lem7554323 x)). Qed.
Lemma lem7554326 (x : real) : (term45 x) = x.
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem7554327 (x : real) : ((term44 x) = (term45 x)) = ((term45 x) = x).
Proof. exact (MK_COMB (@lem7554325 x) (@lem7554326 x)). Qed.
Lemma lem7554328 (x : real) : (term45 x) = x.
Proof. exact (EQ_MP (@lem7554327 x) (@lem7554319 x)). Qed.
Lemma lem7554329 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554330 (x : real) : (term48 x) = (@eq real x).
Proof. exact (MK_COMB (@lem7554329) (@lem7554328 x)). Qed.
Lemma lem7554331 (m : nat) (c : nat -> real) (x : real) : (term49 m c x) = (term49 m c x).
Proof. exact (eq_refl (term49 m c x)). Qed.
Lemma lem7554332 (m : nat) (c : nat -> real) (x : real) : ((term45 x) = (term49 m c x)) = (x = (term49 m c x)).
Proof. exact (MK_COMB (@lem7554330 x) (@lem7554331 m c x)). Qed.
Lemma lem7554335 (m : nat) (c : nat -> real) : (term50 m c) = (term51 m c).
Proof. exact (fun_ext (fun x : real => @lem7554332 m c x)). Qed.
Lemma lem7554336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7554337 (m : nat) (c : nat -> real) : (term52 m c) = (term53 m c).
Proof. exact (MK_COMB (@lem7554336) (@lem7554335 m c)). Qed.
Lemma lem7554342 (m : nat) : (term54 m) = (term55 m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7554337 m c)). Qed.
Lemma lem7554343 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7554344 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem7554343) (@lem7554342 m)). Qed.
Lemma lem7554349 : term58 = term59.
Proof. exact (fun_ext (fun m : nat => @lem7554344 m)). Qed.
Lemma lem7554350 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7554351 : term40 = term60.
Proof. exact (MK_COMB (@lem7554350) (@lem7554349)). Qed.
Lemma lem7554356 : term39 = term60.
Proof. exact (TRANS (@lem7554301) (@lem7554351)). Qed.
Lemma lem7554357 : term60 = term39.
Proof. exact (SYM (@lem7554356)). Qed.
Lemma lem7554365 (m : nat) (n : nat) (f : nat -> real) : (term31 m n f) = (term32 m n f).
Proof. exact (EQ_MP (@lem7554290 m n f) (@lem7554289 m f n)). Qed.
Lemma lem7554366 (x : real) : (term61 x) = (term62 x).
Proof. exact (@lem7554365 (NUMERAL 0) (NUMERAL 0) (term63 x)). Qed.
Lemma lem7554368 (n : nat) : (term26 n) = True.
Proof. exact (EQ_MP (@lem7554283 n) (@lem7554282 n)). Qed.
Lemma lem7554369 : term64 = True.
Proof. exact (@lem7554368 term65). Qed.
Lemma lem7554370 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7554371 : term66 = (@COND real True).
Proof. exact (MK_COMB (@lem7554370) (@lem7554369)). Qed.
Lemma lem7554373 (m : nat) (f : nat -> real) : (term35 m f) = (term36 m f).
Proof. exact (EQ_MP (@lem7554294 m f) (@lem7554293 f m)). Qed.
Lemma lem7554374 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem7554373 (NUMERAL 0) (term63 x)). Qed.
Lemma lem7554376 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term69 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem7554377 (x : nat) (z : real) (y : real) : (term70 x y z) = y.
Proof. exact (@lem7554376 real nat x z y). Qed.
Lemma lem7554378 (x : real) : (term68 x) = (term71 x).
Proof. exact (@lem7554377 (NUMERAL 0) term72 (term71 x)). Qed.
Lemma lem7554380 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554381 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554380 nat real f y). Qed.
Lemma lem7554382 (x : real) : (term74 x) = (term71 x).
Proof. exact (@lem7554381 (term63 x) (NUMERAL 0)). Qed.
Lemma lem7554383 (x : real) (i : nat) : (term75 x i) = (term76 x i).
Proof. exact (eq_refl (term75 x i)). Qed.
Lemma lem7554384 (x : real) : (term77 x) = (term63 x).
Proof. exact (fun_ext (fun i : nat => @lem7554383 x i)). Qed.
Lemma lem7554385 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7554386 (x : real) : (term74 x) = (term71 x).
Proof. exact (MK_COMB (@lem7554384 x) (@lem7554385)). Qed.
Lemma lem7554387 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554388 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem7554387) (@lem7554386 x)). Qed.
Lemma lem7554389 (x : real) : (term71 x) = (term80 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem7554390 (x : real) : ((term74 x) = (term71 x)) = ((term71 x) = (term80 x)).
Proof. exact (MK_COMB (@lem7554388 x) (@lem7554389 x)). Qed.
Lemma lem7554391 (x : real) : (term71 x) = (term80 x).
Proof. exact (EQ_MP (@lem7554390 x) (@lem7554382 x)). Qed.
Lemma lem7554392 (x : real) : (term68 x) = (term80 x).
Proof. exact (TRANS (@lem7554378 x) (@lem7554391 x)). Qed.
Lemma lem7554393 (x : real) : (term67 x) = (term80 x).
Proof. exact (TRANS (@lem7554374 x) (@lem7554392 x)). Qed.
Lemma lem7554395 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554396 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554395 nat real f y). Qed.
Lemma lem7554397 : term81 = term82.
Proof. exact (@lem7554396 term83 (NUMERAL 0)). Qed.
Lemma lem7554398 (i : nat) : (term84 i) = (term85 i).
Proof. exact (eq_refl (term84 i)). Qed.
Lemma lem7554399 : term86 = term83.
Proof. exact (fun_ext (fun i : nat => @lem7554398 i)). Qed.
Lemma lem7554400 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7554401 : term81 = term82.
Proof. exact (MK_COMB (@lem7554399) (@lem7554400)). Qed.
Lemma lem7554402 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554403 : term87 = term88.
Proof. exact (MK_COMB (@lem7554402) (@lem7554401)). Qed.
Lemma lem7554404 : term82 = term89.
Proof. exact (eq_refl term82). Qed.
Lemma lem7554405 : (term81 = term82) = (term82 = term89).
Proof. exact (MK_COMB (@lem7554403) (@lem7554404)). Qed.
Lemma lem7554406 : term82 = term89.
Proof. exact (EQ_MP (@lem7554405) (@lem7554397)). Qed.
Lemma lem7554410 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7554028 m n) (@lem7554027 m n)). Qed.
Lemma lem7554411 : ((NUMERAL 0) = term90) = (0 = (BIT1 0)).
Proof. exact (@lem7554410 0 (BIT1 0)). Qed.
Lemma lem7554413 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem7554008 n) (@lem7554007 n)). Qed.
Lemma lem7554414 : (0 = (BIT1 0)) = False.
Proof. exact (@lem7554413 0). Qed.
Lemma lem7554415 : ((NUMERAL 0) = term90) = False.
Proof. exact (TRANS (@lem7554411) (@lem7554414)). Qed.
Lemma lem7554416 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7554417 : term91 = (@COND real False).
Proof. exact (MK_COMB (@lem7554416) (@lem7554415)). Qed.
Lemma lem7554418 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem7554419 : term93 = term94.
Proof. exact (MK_COMB (@lem7554417) (@lem7554418)). Qed.
Lemma lem7554420 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem7554421 : term89 = term95.
Proof. exact (MK_COMB (@lem7554419) (@lem7554420)). Qed.
Lemma lem7554423 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7554424 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7554423 real t1 t2). Qed.
Lemma lem7554425 : term95 = term72.
Proof. exact (@lem7554424 term92 term72). Qed.
Lemma lem7554426 : term89 = term72.
Proof. exact (TRANS (@lem7554421) (@lem7554425)). Qed.
Lemma lem7554427 : term82 = term72.
Proof. exact (TRANS (@lem7554406) (@lem7554426)). Qed.
Lemma lem7554428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554429 : term96 = term97.
Proof. exact (MK_COMB (@lem7554428) (@lem7554427)). Qed.
Lemma lem7554430 (x : real) : (term98 x) = (term98 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem7554431 (x : real) : (term80 x) = (term99 x).
Proof. exact (MK_COMB (@lem7554429) (@lem7554430 x)). Qed.
Lemma lem7554432 (x : real) : (term67 x) = (term99 x).
Proof. exact (TRANS (@lem7554393 x) (@lem7554431 x)). Qed.
Lemma lem7554433 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7554434 (x : real) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem7554433) (@lem7554432 x)). Qed.
Lemma lem7554436 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554437 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554436 nat real f y). Qed.
Lemma lem7554438 (x : real) : (term102 x) = (term103 x).
Proof. exact (@lem7554437 (term63 x) term65). Qed.
Lemma lem7554439 (x : real) (i : nat) : (term75 x i) = (term76 x i).
Proof. exact (eq_refl (term75 x i)). Qed.
Lemma lem7554440 (x : real) : (term77 x) = (term63 x).
Proof. exact (fun_ext (fun i : nat => @lem7554439 x i)). Qed.
Lemma lem7554441 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem7554442 (x : real) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem7554440 x) (@lem7554441)). Qed.
Lemma lem7554443 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554444 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem7554443) (@lem7554442 x)). Qed.
Lemma lem7554445 (x : real) : (term103 x) = (term106 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem7554446 (x : real) : ((term102 x) = (term103 x)) = ((term103 x) = (term106 x)).
Proof. exact (MK_COMB (@lem7554444 x) (@lem7554445 x)). Qed.
Lemma lem7554447 (x : real) : (term103 x) = (term106 x).
Proof. exact (EQ_MP (@lem7554446 x) (@lem7554438 x)). Qed.
Lemma lem7554449 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554450 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554449 nat real f y). Qed.
Lemma lem7554451 : term107 = term108.
Proof. exact (@lem7554450 term83 term65). Qed.
Lemma lem7554452 (i : nat) : (term84 i) = (term85 i).
Proof. exact (eq_refl (term84 i)). Qed.
Lemma lem7554453 : term86 = term83.
Proof. exact (fun_ext (fun i : nat => @lem7554452 i)). Qed.
Lemma lem7554454 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem7554455 : term107 = term108.
Proof. exact (MK_COMB (@lem7554453) (@lem7554454)). Qed.
Lemma lem7554456 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554457 : term109 = term110.
Proof. exact (MK_COMB (@lem7554456) (@lem7554455)). Qed.
Lemma lem7554458 : term108 = term111.
Proof. exact (eq_refl term108). Qed.
Lemma lem7554459 : (term107 = term108) = (term108 = term111).
Proof. exact (MK_COMB (@lem7554457) (@lem7554458)). Qed.
Lemma lem7554460 : term108 = term111.
Proof. exact (EQ_MP (@lem7554459) (@lem7554451)). Qed.
Lemma lem7554466 (n : nat) : (term23 n) = (term24 n).
Proof. exact (EQ_MP (@lem7554275 n) (@lem7554274 n)). Qed.
Lemma lem7554467 : term65 = term112.
Proof. exact (@lem7554466 0). Qed.
Lemma lem7554469 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem7554262)). Qed.
Lemma lem7554470 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem7554471 : term112 = term90.
Proof. exact (MK_COMB (@lem7554470) (@lem7554469)). Qed.
Lemma lem7554472 : term65 = term90.
Proof. exact (TRANS (@lem7554467) (@lem7554471)). Qed.
Lemma lem7554473 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7554474 : term113 = term114.
Proof. exact (MK_COMB (@lem7554473) (@lem7554472)). Qed.
Lemma lem7554475 : term90 = term90.
Proof. exact (eq_refl term90). Qed.
Lemma lem7554476 : (term65 = term90) = (term90 = term90).
Proof. exact (MK_COMB (@lem7554474) (@lem7554475)). Qed.
Lemma lem7554478 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7554028 m n) (@lem7554027 m n)). Qed.
Lemma lem7554479 : (term90 = term90) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem7554478 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7554481 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem7553983 m n) (@lem7553982 m n)). Qed.
Lemma lem7554482 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem7554481 0 0). Qed.
Lemma lem7554484 : (0 = 0) = True.
Proof. exact (proj1 (@lem7553970)). Qed.
Lemma lem7554485 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem7554482) (@lem7554484)). Qed.
Lemma lem7554486 : (term90 = term90) = True.
Proof. exact (TRANS (@lem7554479) (@lem7554485)). Qed.
Lemma lem7554487 : (term65 = term90) = True.
Proof. exact (TRANS (@lem7554476) (@lem7554486)). Qed.
Lemma lem7554488 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7554489 : term115 = (@COND real True).
Proof. exact (MK_COMB (@lem7554488) (@lem7554487)). Qed.
Lemma lem7554490 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem7554491 : term116 = term117.
Proof. exact (MK_COMB (@lem7554489) (@lem7554490)). Qed.
Lemma lem7554492 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem7554493 : term111 = term118.
Proof. exact (MK_COMB (@lem7554491) (@lem7554492)). Qed.
Lemma lem7554495 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7554496 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7554495 real t2 t1). Qed.
Lemma lem7554497 : term118 = term92.
Proof. exact (@lem7554496 term72 term92). Qed.
Lemma lem7554498 : term111 = term92.
Proof. exact (TRANS (@lem7554493) (@lem7554497)). Qed.
Lemma lem7554499 : term108 = term92.
Proof. exact (TRANS (@lem7554460) (@lem7554498)). Qed.
Lemma lem7554500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554501 : term119 = term120.
Proof. exact (MK_COMB (@lem7554500) (@lem7554499)). Qed.
Lemma lem7554503 (n : nat) : (term23 n) = (term24 n).
Proof. exact (EQ_MP (@lem7554275 n) (@lem7554274 n)). Qed.
Lemma lem7554504 : term65 = term112.
Proof. exact (@lem7554503 0). Qed.
Lemma lem7554506 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem7554262)). Qed.
Lemma lem7554507 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem7554508 : term112 = term90.
Proof. exact (MK_COMB (@lem7554507) (@lem7554506)). Qed.
Lemma lem7554509 : term65 = term90.
Proof. exact (TRANS (@lem7554504) (@lem7554508)). Qed.
Lemma lem7554510 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem7554511 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem7554510 x) (@lem7554509)). Qed.
Lemma lem7554512 (x : real) : (term106 x) = (term123 x).
Proof. exact (MK_COMB (@lem7554501) (@lem7554511 x)). Qed.
Lemma lem7554513 (x : real) : (term103 x) = (term123 x).
Proof. exact (TRANS (@lem7554447 x) (@lem7554512 x)). Qed.
Lemma lem7554514 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem7554434 x) (@lem7554513 x)). Qed.
Lemma lem7554515 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem7554371) (@lem7554514 x)). Qed.
Lemma lem7554517 (m : nat) (f : nat -> real) : (term35 m f) = (term36 m f).
Proof. exact (EQ_MP (@lem7554294 m f) (@lem7554293 f m)). Qed.
Lemma lem7554518 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem7554517 (NUMERAL 0) (term63 x)). Qed.
Lemma lem7554520 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term69 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem7554521 (x : nat) (z : real) (y : real) : (term70 x y z) = y.
Proof. exact (@lem7554520 real nat x z y). Qed.
Lemma lem7554522 (x : real) : (term68 x) = (term71 x).
Proof. exact (@lem7554521 (NUMERAL 0) term72 (term71 x)). Qed.
Lemma lem7554524 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554525 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554524 nat real f y). Qed.
Lemma lem7554526 (x : real) : (term74 x) = (term71 x).
Proof. exact (@lem7554525 (term63 x) (NUMERAL 0)). Qed.
Lemma lem7554527 (x : real) (i : nat) : (term75 x i) = (term76 x i).
Proof. exact (eq_refl (term75 x i)). Qed.
Lemma lem7554528 (x : real) : (term77 x) = (term63 x).
Proof. exact (fun_ext (fun i : nat => @lem7554527 x i)). Qed.
Lemma lem7554529 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7554530 (x : real) : (term74 x) = (term71 x).
Proof. exact (MK_COMB (@lem7554528 x) (@lem7554529)). Qed.
Lemma lem7554531 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554532 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem7554531) (@lem7554530 x)). Qed.
Lemma lem7554533 (x : real) : (term71 x) = (term80 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem7554534 (x : real) : ((term74 x) = (term71 x)) = ((term71 x) = (term80 x)).
Proof. exact (MK_COMB (@lem7554532 x) (@lem7554533 x)). Qed.
Lemma lem7554535 (x : real) : (term71 x) = (term80 x).
Proof. exact (EQ_MP (@lem7554534 x) (@lem7554526 x)). Qed.
Lemma lem7554536 (x : real) : (term68 x) = (term80 x).
Proof. exact (TRANS (@lem7554522 x) (@lem7554535 x)). Qed.
Lemma lem7554537 (x : real) : (term67 x) = (term80 x).
Proof. exact (TRANS (@lem7554518 x) (@lem7554536 x)). Qed.
Lemma lem7554539 {A B : Type'} (f : A -> B) (y : A) : (term42 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7554540 (f : nat -> real) (y : nat) : (term73 f y) = (f y).
Proof. exact (@lem7554539 nat real f y). Qed.
Lemma lem7554541 : term81 = term82.
Proof. exact (@lem7554540 term83 (NUMERAL 0)). Qed.
Lemma lem7554542 (i : nat) : (term84 i) = (term85 i).
Proof. exact (eq_refl (term84 i)). Qed.
Lemma lem7554543 : term86 = term83.
Proof. exact (fun_ext (fun i : nat => @lem7554542 i)). Qed.
Lemma lem7554544 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7554545 : term81 = term82.
Proof. exact (MK_COMB (@lem7554543) (@lem7554544)). Qed.
Lemma lem7554546 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7554547 : term87 = term88.
Proof. exact (MK_COMB (@lem7554546) (@lem7554545)). Qed.
Lemma lem7554548 : term82 = term89.
Proof. exact (eq_refl term82). Qed.
Lemma lem7554549 : (term81 = term82) = (term82 = term89).
Proof. exact (MK_COMB (@lem7554547) (@lem7554548)). Qed.
Lemma lem7554550 : term82 = term89.
Proof. exact (EQ_MP (@lem7554549) (@lem7554541)). Qed.
Lemma lem7554554 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7554028 m n) (@lem7554027 m n)). Qed.
Lemma lem7554555 : ((NUMERAL 0) = term90) = (0 = (BIT1 0)).
Proof. exact (@lem7554554 0 (BIT1 0)). Qed.
Lemma lem7554557 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem7554008 n) (@lem7554007 n)). Qed.
Lemma lem7554558 : (0 = (BIT1 0)) = False.
Proof. exact (@lem7554557 0). Qed.
Lemma lem7554559 : ((NUMERAL 0) = term90) = False.
Proof. exact (TRANS (@lem7554555) (@lem7554558)). Qed.
Lemma lem7554560 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7554561 : term91 = (@COND real False).
Proof. exact (MK_COMB (@lem7554560) (@lem7554559)). Qed.
Lemma lem7554562 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem7554563 : term93 = term94.
Proof. exact (MK_COMB (@lem7554561) (@lem7554562)). Qed.
Lemma lem7554564 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem7554565 : term89 = term95.
Proof. exact (MK_COMB (@lem7554563) (@lem7554564)). Qed.
Lemma lem7554567 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7554568 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7554567 real t1 t2). Qed.
Lemma lem7554569 : term95 = term72.
Proof. exact (@lem7554568 term92 term72). Qed.
Lemma lem7554570 : term89 = term72.
Proof. exact (TRANS (@lem7554565) (@lem7554569)). Qed.
Lemma lem7554571 : term82 = term72.
Proof. exact (TRANS (@lem7554550) (@lem7554570)). Qed.
Lemma lem7554572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554573 : term96 = term97.
Proof. exact (MK_COMB (@lem7554572) (@lem7554571)). Qed.
Lemma lem7554574 (x : real) : (term98 x) = (term98 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem7554575 (x : real) : (term80 x) = (term99 x).
Proof. exact (MK_COMB (@lem7554573) (@lem7554574 x)). Qed.
Lemma lem7554576 (x : real) : (term67 x) = (term99 x).
Proof. exact (TRANS (@lem7554537 x) (@lem7554575 x)). Qed.
Lemma lem7554577 (x : real) : (term62 x) = (term128 x).
Proof. exact (MK_COMB (@lem7554515 x) (@lem7554576 x)). Qed.
Lemma lem7554579 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7554580 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7554579 real t2 t1). Qed.
Lemma lem7554581 (x : real) : (term128 x) = (term125 x).
Proof. exact (@lem7554580 (term99 x) (term125 x)). Qed.
Lemma lem7554582 (x : real) : (term62 x) = (term125 x).
Proof. exact (TRANS (@lem7554577 x) (@lem7554581 x)). Qed.
Lemma lem7554583 (x : real) : (term61 x) = (term125 x).
Proof. exact (TRANS (@lem7554366 x) (@lem7554582 x)). Qed.
Lemma lem7554584 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem7554585 (x : real) : (x = (term61 x)) = (x = (term125 x)).
Proof. exact (MK_COMB (@lem7554584 x) (@lem7554583 x)). Qed.
Lemma lem7554588 : term129 = term130.
Proof. exact (fun_ext (fun x : real => @lem7554585 x)). Qed.
Lemma lem7554589 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7554590 : term131 = term132.
Proof. exact (MK_COMB (@lem7554589) (@lem7554588)). Qed.
Lemma lem7554595 : term132 = term131.
Proof. exact (SYM (@lem7554590)). Qed.
Lemma lem7554605 (P : real -> Prop) : (term133 P) = (term134 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7554606 : term135 = term136.
Proof. exact (@lem7554605 term130). Qed.
Lemma lem7554607 (x : real) : (term137 x) = (x = (term125 x)).
Proof. exact (eq_refl (term137 x)). Qed.
Lemma lem7554608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7554610 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem7554608) (@lem7554607 x)). Qed.
Lemma lem7554611 : term140 = term141.
Proof. exact (fun_ext (fun x : real => @lem7554610 x)). Qed.
Lemma lem7554612 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554613 : term136 = term142.
Proof. exact (MK_COMB (@lem7554612) (@lem7554611)). Qed.
Lemma lem7554615 : term135 = term142.
Proof. exact (TRANS (@lem7554606) (@lem7554613)). Qed.
Lemma lem7554618 (x : real) : (term139 x) = (term139 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem7554619 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem7554618 x)). Qed.
Lemma lem7554620 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554621 : term142 = term142.
Proof. exact (MK_COMB (@lem7554620) (@lem7554619)). Qed.
Lemma lem7554622 : term135 = term142.
Proof. exact (TRANS (@lem7554615) (@lem7554621)). Qed.
Lemma lem7554623 (x : real) : (term139 x) = (term143 x).
Proof. exact (@lem1988318 x (term125 x)). Qed.
Lemma lem7554630 (x : real) : (term122 x) = x.
Proof. exact (@lem1982779 x). Qed.
Lemma lem7554633 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem7554634 (x : real) : (term123 x) = (term144 x).
Proof. exact (MK_COMB (@lem7554633) (@lem7554630 x)). Qed.
Lemma lem7554635 (x : real) : (term144 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7554636 (x : real) : (term123 x) = x.
Proof. exact (TRANS (@lem7554634 x) (@lem7554635 x)). Qed.
Lemma lem7554643 (x : real) : (term98 x) = term92.
Proof. exact (@lem1982777 x). Qed.
Lemma lem7554646 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem7554647 (x : real) : (term99 x) = term145.
Proof. exact (MK_COMB (@lem7554646) (@lem7554643 x)). Qed.
Lemma lem7554648 : term145 = term72.
Proof. exact (@lem1982729 term92). Qed.
Lemma lem7554649 (x : real) : (term99 x) = term72.
Proof. exact (TRANS (@lem7554647 x) (@lem7554648)). Qed.
Lemma lem7554650 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7554651 (x : real) : (term101 x) = term146.
Proof. exact (MK_COMB (@lem7554650) (@lem7554649 x)). Qed.
Lemma lem7554652 (x : real) : (term125 x) = (term147 x).
Proof. exact (MK_COMB (@lem7554651 x) (@lem7554636 x)). Qed.
Lemma lem7554653 (x : real) : (term147 x) = x.
Proof. exact (@lem1982721 x). Qed.
Lemma lem7554654 (x : real) : (term125 x) = x.
Proof. exact (TRANS (@lem7554652 x) (@lem7554653 x)). Qed.
Lemma lem7554657 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem7554658 (x : real) : (term148 x) = (real_sub x x).
Proof. exact (MK_COMB (@lem7554657 x) (@lem7554654 x)). Qed.
Lemma lem7554659 (x : real) : (real_sub x x) = (term149 x).
Proof. exact (@lem1982792 x x). Qed.
Lemma lem7554663 (x : real) : (term149 x) = (term150 x).
Proof. exact (@lem1982715 term151 x). Qed.
Lemma lem7554665 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554666 : term92 = term153.
Proof. exact (@lem7554665 term90). Qed.
Lemma lem7554668 (x : nat) : (term154 x) = (term155 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7554669 : term151 = term156.
Proof. exact (@lem7554668 term90). Qed.
Lemma lem7554670 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7554671 : term157 = term158.
Proof. exact (MK_COMB (@lem7554670) (@lem7554669)). Qed.
Lemma lem7554672 : term159 = term160.
Proof. exact (MK_COMB (@lem7554671) (@lem7554666)). Qed.
Lemma lem7554673 : term161.
Proof. exact (@lem1981473 term151 term92 term92 term92 term72 term92). Qed.
Lemma lem7554675 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554676 : term163 = term164.
Proof. exact (@lem7554675 (NUMERAL 0) term90). Qed.
Lemma lem7554677 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554678 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554679 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554678 h1) (fun h1 : term164 = True => @lem7554677)). Qed.
Lemma lem7554680 : term164 = True.
Proof. exact (EQ_MP (@lem7554679) (@lem7554677)). Qed.
Lemma lem7554681 : term163 = True.
Proof. exact (TRANS (@lem7554676) (@lem7554680)). Qed.
Lemma lem7554682 : True = term163.
Proof. exact (SYM (@lem7554681)). Qed.
Lemma lem7554683 : term163.
Proof. exact (EQ_MP (@lem7554682) (@lem0)). Qed.
Lemma lem7554684 : term166.
Proof. exact (@lem7554673 (@lem7554683)). Qed.
Lemma lem7554686 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554687 : term163 = term164.
Proof. exact (@lem7554686 (NUMERAL 0) term90). Qed.
Lemma lem7554688 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554689 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554690 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554689 h1) (fun h1 : term164 = True => @lem7554688)). Qed.
Lemma lem7554691 : term164 = True.
Proof. exact (EQ_MP (@lem7554690) (@lem7554688)). Qed.
Lemma lem7554692 : term163 = True.
Proof. exact (TRANS (@lem7554687) (@lem7554691)). Qed.
Lemma lem7554693 : True = term163.
Proof. exact (SYM (@lem7554692)). Qed.
Lemma lem7554694 : term163.
Proof. exact (EQ_MP (@lem7554693) (@lem0)). Qed.
Lemma lem7554695 : term167.
Proof. exact (@lem7554684 (@lem7554694)). Qed.
Lemma lem7554697 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554698 : term163 = term164.
Proof. exact (@lem7554697 (NUMERAL 0) term90). Qed.
Lemma lem7554699 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554700 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554701 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554700 h1) (fun h1 : term164 = True => @lem7554699)). Qed.
Lemma lem7554702 : term164 = True.
Proof. exact (EQ_MP (@lem7554701) (@lem7554699)). Qed.
Lemma lem7554703 : term163 = True.
Proof. exact (TRANS (@lem7554698) (@lem7554702)). Qed.
Lemma lem7554704 : True = term163.
Proof. exact (SYM (@lem7554703)). Qed.
Lemma lem7554705 : term163.
Proof. exact (EQ_MP (@lem7554704) (@lem0)). Qed.
Lemma lem7554706 : term168.
Proof. exact (@lem7554695 (@lem7554705)). Qed.
Lemma lem7554708 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7554709 : term171 = term172.
Proof. exact (@lem7554708 term90 term90). Qed.
Lemma lem7554710 : (term173 = (BIT1 0)) = (term174 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7554711 : term174 = term90.
Proof. exact (EQ_MP (@lem7554710) (@lem940073)). Qed.
Lemma lem7554712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7554713 : term172 = term92.
Proof. exact (MK_COMB (@lem7554712) (@lem7554711)). Qed.
Lemma lem7554714 : term171 = term92.
Proof. exact (TRANS (@lem7554709) (@lem7554713)). Qed.
Lemma lem7554716 (m : nat) (n : nat) : (term175 m n) = (term176 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7554717 : term177 = term178.
Proof. exact (@lem7554716 term90 term90). Qed.
Lemma lem7554718 : (term173 = (BIT1 0)) = (term174 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7554719 : term174 = term90.
Proof. exact (EQ_MP (@lem7554718) (@lem940073)). Qed.
Lemma lem7554720 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7554721 : term172 = term92.
Proof. exact (MK_COMB (@lem7554720) (@lem7554719)). Qed.
Lemma lem7554722 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7554723 : term178 = term151.
Proof. exact (MK_COMB (@lem7554722) (@lem7554721)). Qed.
Lemma lem7554724 : term177 = term151.
Proof. exact (TRANS (@lem7554717) (@lem7554723)). Qed.
Lemma lem7554725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7554726 : term179 = term157.
Proof. exact (MK_COMB (@lem7554725) (@lem7554724)). Qed.
Lemma lem7554727 : term180 = term159.
Proof. exact (MK_COMB (@lem7554726) (@lem7554714)). Qed.
Lemma lem7554729 (m : nat) : (term181 m) = term72.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7554730 : term159 = term72.
Proof. exact (@lem7554729 term90). Qed.
Lemma lem7554731 : term180 = term72.
Proof. exact (TRANS (@lem7554727) (@lem7554730)). Qed.
Lemma lem7554732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554733 : term182 = term97.
Proof. exact (MK_COMB (@lem7554732) (@lem7554731)). Qed.
Lemma lem7554734 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem7554735 : term183 = term145.
Proof. exact (MK_COMB (@lem7554733) (@lem7554734)). Qed.
Lemma lem7554737 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554738 : term145 = term72.
Proof. exact (@lem7554737 term90). Qed.
Lemma lem7554739 : term183 = term72.
Proof. exact (TRANS (@lem7554735) (@lem7554738)). Qed.
Lemma lem7554741 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7554742 : term171 = term172.
Proof. exact (@lem7554741 term90 term90). Qed.
Lemma lem7554743 : (term173 = (BIT1 0)) = (term174 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7554744 : term174 = term90.
Proof. exact (EQ_MP (@lem7554743) (@lem940073)). Qed.
Lemma lem7554745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7554746 : term172 = term92.
Proof. exact (MK_COMB (@lem7554745) (@lem7554744)). Qed.
Lemma lem7554747 : term171 = term92.
Proof. exact (TRANS (@lem7554742) (@lem7554746)). Qed.
Lemma lem7554748 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem7554749 : term185 = term145.
Proof. exact (MK_COMB (@lem7554748) (@lem7554747)). Qed.
Lemma lem7554751 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554752 : term145 = term72.
Proof. exact (@lem7554751 term90). Qed.
Lemma lem7554753 : term185 = term72.
Proof. exact (TRANS (@lem7554749) (@lem7554752)). Qed.
Lemma lem7554754 : term72 = term185.
Proof. exact (SYM (@lem7554753)). Qed.
Lemma lem7554755 : term183 = term185.
Proof. exact (TRANS (@lem7554739) (@lem7554754)). Qed.
Lemma lem7554756 : term160 = term186.
Proof. exact (@lem7554706 (@lem7554755)). Qed.
Lemma lem7554757 : term159 = term186.
Proof. exact (TRANS (@lem7554672) (@lem7554756)). Qed.
Lemma lem7554759 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7554760 : term186 = term72.
Proof. exact (@lem7554759 term72). Qed.
Lemma lem7554761 : term159 = term72.
Proof. exact (TRANS (@lem7554757) (@lem7554760)). Qed.
Lemma lem7554762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554763 : term188 = term97.
Proof. exact (MK_COMB (@lem7554762) (@lem7554761)). Qed.
Lemma lem7554764 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7554765 (x : real) : (term150 x) = (term189 x).
Proof. exact (MK_COMB (@lem7554763) (@lem7554764 x)). Qed.
Lemma lem7554766 (x : real) : (term149 x) = (term189 x).
Proof. exact (TRANS (@lem7554663 x) (@lem7554765 x)). Qed.
Lemma lem7554767 (x : real) : (term189 x) = term72.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7554769 (x : real) : (term149 x) = term72.
Proof. exact (TRANS (@lem7554766 x) (@lem7554767 x)). Qed.
Lemma lem7554770 (x : real) : (real_sub x x) = term72.
Proof. exact (TRANS (@lem7554659 x) (@lem7554769 x)). Qed.
Lemma lem7554771 (x : real) : (term148 x) = term72.
Proof. exact (TRANS (@lem7554658 x) (@lem7554770 x)). Qed.
Lemma lem7554772 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7554773 (x : real) : (term190 x) = term191.
Proof. exact (MK_COMB (@lem7554772) (@lem7554771 x)). Qed.
Lemma lem7554774 : term191 = term192.
Proof. exact (@lem1982785 term72). Qed.
Lemma lem7554776 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554777 : term72 = term186.
Proof. exact (@lem7554776 (NUMERAL 0)). Qed.
Lemma lem7554779 (x : nat) : (term154 x) = (term155 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7554780 : term151 = term156.
Proof. exact (@lem7554779 term90). Qed.
Lemma lem7554781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7554782 : term193 = term194.
Proof. exact (MK_COMB (@lem7554781) (@lem7554780)). Qed.
Lemma lem7554783 : term192 = term195.
Proof. exact (MK_COMB (@lem7554782) (@lem7554777)). Qed.
Lemma lem7554784 : term195 = term196.
Proof. exact (@lem1981613 term151 term72 term92 term92). Qed.
Lemma lem7554786 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7554787 : term171 = term172.
Proof. exact (@lem7554786 term90 term90). Qed.
Lemma lem7554788 : (term173 = (BIT1 0)) = (term174 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7554789 : term174 = term90.
Proof. exact (EQ_MP (@lem7554788) (@lem940073)). Qed.
Lemma lem7554790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7554791 : term172 = term92.
Proof. exact (MK_COMB (@lem7554790) (@lem7554789)). Qed.
Lemma lem7554792 : term171 = term92.
Proof. exact (TRANS (@lem7554787) (@lem7554791)). Qed.
Lemma lem7554794 (x : nat) : (term197 x) = term72.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7554795 : term192 = term72.
Proof. exact (@lem7554794 term90). Qed.
Lemma lem7554796 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7554797 : term198 = term199.
Proof. exact (MK_COMB (@lem7554796) (@lem7554795)). Qed.
Lemma lem7554798 : term196 = term186.
Proof. exact (MK_COMB (@lem7554797) (@lem7554792)). Qed.
Lemma lem7554799 : term195 = term186.
Proof. exact (TRANS (@lem7554784) (@lem7554798)). Qed.
Lemma lem7554800 : term192 = term186.
Proof. exact (TRANS (@lem7554783) (@lem7554799)). Qed.
Lemma lem7554802 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7554803 : term186 = term72.
Proof. exact (@lem7554802 term72). Qed.
Lemma lem7554804 : term192 = term72.
Proof. exact (TRANS (@lem7554800) (@lem7554803)). Qed.
Lemma lem7554805 : term191 = term72.
Proof. exact (TRANS (@lem7554774) (@lem7554804)). Qed.
Lemma lem7554806 (x : real) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem7554807 (x : real) : ((term190 x) = term191) = ((term190 x) = term72).
Proof. exact (MK_COMB (@lem7554806 x) (@lem7554805)). Qed.
Lemma lem7554808 (x : real) : (term190 x) = term72.
Proof. exact (EQ_MP (@lem7554807 x) (@lem7554773 x)). Qed.
Lemma lem7554809 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7554810 (x : real) : (term201 x) = term202.
Proof. exact (MK_COMB (@lem7554809) (@lem7554808 x)). Qed.
Lemma lem7554811 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem7554812 (x : real) : (term203 x) = term204.
Proof. exact (MK_COMB (@lem7554810 x) (@lem7554811)). Qed.
Lemma lem7554813 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7554814 (x : real) : (term205 x) = term202.
Proof. exact (MK_COMB (@lem7554813) (@lem7554771 x)). Qed.
Lemma lem7554815 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem7554816 (x : real) : (term206 x) = term204.
Proof. exact (MK_COMB (@lem7554814 x) (@lem7554815)). Qed.
Lemma lem7554817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7554818 (x : real) : (term207 x) = term208.
Proof. exact (MK_COMB (@lem7554817) (@lem7554816 x)). Qed.
Lemma lem7554819 (x : real) : (term143 x) = term209.
Proof. exact (MK_COMB (@lem7554818 x) (@lem7554812 x)). Qed.
Lemma lem7554820 (x : real) : (term139 x) = term209.
Proof. exact (TRANS (@lem7554623 x) (@lem7554819 x)). Qed.
Lemma lem7554821 : term141 = term210.
Proof. exact (fun_ext (fun x : real => @lem7554820 x)). Qed.
Lemma lem7554822 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554823 : term142 = term211.
Proof. exact (MK_COMB (@lem7554822) (@lem7554821)). Qed.
Lemma lem7554824 : term135 = term211.
Proof. exact (TRANS (@lem7554622) (@lem7554823)). Qed.
Lemma lem7554826 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7554827 (P : real -> Prop) (Q : real -> Prop) : (term214 P Q) = (term215 P Q).
Proof. exact (@lem7554826 real P Q). Qed.
Lemma lem7554828 : term216 = term217.
Proof. exact (@lem7554827 term218 term218). Qed.
Lemma lem7554829 (x : real) : (term219 x) = term204.
Proof. exact (eq_refl (term219 x)). Qed.
Lemma lem7554830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7554831 (x : real) : (term220 x) = term208.
Proof. exact (MK_COMB (@lem7554830) (@lem7554829 x)). Qed.
Lemma lem7554832 (x : real) : (term219 x) = term204.
Proof. exact (eq_refl (term219 x)). Qed.
Lemma lem7554833 (x : real) : (term221 x) = term209.
Proof. exact (MK_COMB (@lem7554831 x) (@lem7554832 x)). Qed.
Lemma lem7554834 : term222 = term210.
Proof. exact (fun_ext (fun x : real => @lem7554833 x)). Qed.
Lemma lem7554835 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554836 : term216 = term211.
Proof. exact (MK_COMB (@lem7554835) (@lem7554834)). Qed.
Lemma lem7554837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7554838 : term223 = term224.
Proof. exact (MK_COMB (@lem7554837) (@lem7554836)). Qed.
Lemma lem7554839 (x : real) : (term219 x) = term204.
Proof. exact (eq_refl (term219 x)). Qed.
Lemma lem7554840 : term225 = term218.
Proof. exact (fun_ext (fun x : real => @lem7554839 x)). Qed.
Lemma lem7554841 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554842 : term226 = term227.
Proof. exact (MK_COMB (@lem7554841) (@lem7554840)). Qed.
Lemma lem7554843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7554844 : term228 = term229.
Proof. exact (MK_COMB (@lem7554843) (@lem7554842)). Qed.
Lemma lem7554845 (x : real) : (term219 x) = term204.
Proof. exact (eq_refl (term219 x)). Qed.
Lemma lem7554846 : term225 = term218.
Proof. exact (fun_ext (fun x : real => @lem7554845 x)). Qed.
Lemma lem7554847 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7554848 : term226 = term227.
Proof. exact (MK_COMB (@lem7554847) (@lem7554846)). Qed.
Lemma lem7554849 : term217 = term230.
Proof. exact (MK_COMB (@lem7554844) (@lem7554848)). Qed.
Lemma lem7554850 : (term216 = term217) = (term211 = term230).
Proof. exact (MK_COMB (@lem7554838) (@lem7554849)). Qed.
Lemma lem7554851 : term211 = term230.
Proof. exact (EQ_MP (@lem7554850) (@lem7554828)). Qed.
Lemma lem7554853 {A : Type'} (t : Prop) : (term231 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7554854 (t : Prop) : (term232 t) = t.
Proof. exact (@lem7554853 real t). Qed.
Lemma lem7554855 : term227 = term204.
Proof. exact (@lem7554854 term204). Qed.
Lemma lem7554856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7554857 : term229 = term208.
Proof. exact (MK_COMB (@lem7554856) (@lem7554855)). Qed.
Lemma lem7554859 {A : Type'} (t : Prop) : (term231 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7554860 (t : Prop) : (term232 t) = t.
Proof. exact (@lem7554859 real t). Qed.
Lemma lem7554861 : term227 = term204.
Proof. exact (@lem7554860 term204). Qed.
Lemma lem7554862 : term230 = term209.
Proof. exact (MK_COMB (@lem7554857) (@lem7554861)). Qed.
Lemma lem7554865 : term211 = term209.
Proof. exact (TRANS (@lem7554851) (@lem7554862)). Qed.
Lemma lem7554874 : term135 = term209.
Proof. exact (TRANS (@lem7554824) (@lem7554865)). Qed.
Lemma lem7554884 (h1 : term209) : term209.
Proof. exact (h1). Qed.
Lemma lem7554885 (h1 : term204) : term204.
Proof. exact (h1). Qed.
Lemma lem7554887 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7554888 : term204 = term233.
Proof. exact (@lem7554887 term72 term72). Qed.
Lemma lem7554890 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554891 : term72 = term186.
Proof. exact (@lem7554890 (NUMERAL 0)). Qed.
Lemma lem7554893 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554894 : term72 = term186.
Proof. exact (@lem7554893 (NUMERAL 0)). Qed.
Lemma lem7554895 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7554896 : term234 = term235.
Proof. exact (MK_COMB (@lem7554895) (@lem7554894)). Qed.
Lemma lem7554897 : term233 = term236.
Proof. exact (MK_COMB (@lem7554896) (@lem7554891)). Qed.
Lemma lem7554898 : term237.
Proof. exact (@lem1980255 term72 term92 term72 term92). Qed.
Lemma lem7554900 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554901 : term163 = term164.
Proof. exact (@lem7554900 (NUMERAL 0) term90). Qed.
Lemma lem7554902 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554903 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554904 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554903 h1) (fun h1 : term164 = True => @lem7554902)). Qed.
Lemma lem7554905 : term164 = True.
Proof. exact (EQ_MP (@lem7554904) (@lem7554902)). Qed.
Lemma lem7554906 : term163 = True.
Proof. exact (TRANS (@lem7554901) (@lem7554905)). Qed.
Lemma lem7554907 : True = term163.
Proof. exact (SYM (@lem7554906)). Qed.
Lemma lem7554908 : term163.
Proof. exact (EQ_MP (@lem7554907) (@lem0)). Qed.
Lemma lem7554909 : term238.
Proof. exact (@lem7554898 (@lem7554908)). Qed.
Lemma lem7554911 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554912 : term163 = term164.
Proof. exact (@lem7554911 (NUMERAL 0) term90). Qed.
Lemma lem7554913 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554914 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554915 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554914 h1) (fun h1 : term164 = True => @lem7554913)). Qed.
Lemma lem7554916 : term164 = True.
Proof. exact (EQ_MP (@lem7554915) (@lem7554913)). Qed.
Lemma lem7554917 : term163 = True.
Proof. exact (TRANS (@lem7554912) (@lem7554916)). Qed.
Lemma lem7554918 : True = term163.
Proof. exact (SYM (@lem7554917)). Qed.
Lemma lem7554919 : term163.
Proof. exact (EQ_MP (@lem7554918) (@lem0)). Qed.
Lemma lem7554920 : term236 = term239.
Proof. exact (@lem7554909 (@lem7554919)). Qed.
Lemma lem7554922 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554923 : term145 = term72.
Proof. exact (@lem7554922 term90). Qed.
Lemma lem7554925 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554926 : term145 = term72.
Proof. exact (@lem7554925 term90). Qed.
Lemma lem7554927 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7554928 : term240 = term234.
Proof. exact (MK_COMB (@lem7554927) (@lem7554926)). Qed.
Lemma lem7554929 : term239 = term233.
Proof. exact (MK_COMB (@lem7554928) (@lem7554923)). Qed.
Lemma lem7554931 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554932 : term233 = term241.
Proof. exact (@lem7554931 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7554933 : term241 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7554934 : term233 = False.
Proof. exact (TRANS (@lem7554932) (@lem7554933)). Qed.
Lemma lem7554935 : term239 = False.
Proof. exact (TRANS (@lem7554929) (@lem7554934)). Qed.
Lemma lem7554936 : term236 = False.
Proof. exact (TRANS (@lem7554920) (@lem7554935)). Qed.
Lemma lem7554937 : term233 = False.
Proof. exact (TRANS (@lem7554897) (@lem7554936)). Qed.
Lemma lem7554938 : term204 = False.
Proof. exact (TRANS (@lem7554888) (@lem7554937)). Qed.
Lemma lem7554939 (h1 : term204) : False.
Proof. exact (EQ_MP (@lem7554938) (@lem7554885 h1)). Qed.
Lemma lem7554940 (h1 : term204) : term204.
Proof. exact (h1). Qed.
Lemma lem7554942 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7554943 : term204 = term233.
Proof. exact (@lem7554942 term72 term72). Qed.
Lemma lem7554945 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554946 : term72 = term186.
Proof. exact (@lem7554945 (NUMERAL 0)). Qed.
Lemma lem7554948 (x : nat) : (real_of_num x) = (term152 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7554949 : term72 = term186.
Proof. exact (@lem7554948 (NUMERAL 0)). Qed.
Lemma lem7554950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7554951 : term234 = term235.
Proof. exact (MK_COMB (@lem7554950) (@lem7554949)). Qed.
Lemma lem7554952 : term233 = term236.
Proof. exact (MK_COMB (@lem7554951) (@lem7554946)). Qed.
Lemma lem7554953 : term237.
Proof. exact (@lem1980255 term72 term92 term72 term92). Qed.
Lemma lem7554955 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554956 : term163 = term164.
Proof. exact (@lem7554955 (NUMERAL 0) term90). Qed.
Lemma lem7554957 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554958 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554959 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554958 h1) (fun h1 : term164 = True => @lem7554957)). Qed.
Lemma lem7554960 : term164 = True.
Proof. exact (EQ_MP (@lem7554959) (@lem7554957)). Qed.
Lemma lem7554961 : term163 = True.
Proof. exact (TRANS (@lem7554956) (@lem7554960)). Qed.
Lemma lem7554962 : True = term163.
Proof. exact (SYM (@lem7554961)). Qed.
Lemma lem7554963 : term163.
Proof. exact (EQ_MP (@lem7554962) (@lem0)). Qed.
Lemma lem7554964 : term238.
Proof. exact (@lem7554953 (@lem7554963)). Qed.
Lemma lem7554966 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554967 : term163 = term164.
Proof. exact (@lem7554966 (NUMERAL 0) term90). Qed.
Lemma lem7554968 : term165 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7554969 (h1 : term165 = (BIT1 0)) : term164 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7554970 : (term165 = (BIT1 0)) = (term164 = True).
Proof. exact (prop_ext (fun h1 : term165 = (BIT1 0) => @lem7554969 h1) (fun h1 : term164 = True => @lem7554968)). Qed.
Lemma lem7554971 : term164 = True.
Proof. exact (EQ_MP (@lem7554970) (@lem7554968)). Qed.
Lemma lem7554972 : term163 = True.
Proof. exact (TRANS (@lem7554967) (@lem7554971)). Qed.
Lemma lem7554973 : True = term163.
Proof. exact (SYM (@lem7554972)). Qed.
Lemma lem7554974 : term163.
Proof. exact (EQ_MP (@lem7554973) (@lem0)). Qed.
Lemma lem7554975 : term236 = term239.
Proof. exact (@lem7554964 (@lem7554974)). Qed.
Lemma lem7554977 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554978 : term145 = term72.
Proof. exact (@lem7554977 term90). Qed.
Lemma lem7554980 (x : nat) : (term184 x) = term72.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7554981 : term145 = term72.
Proof. exact (@lem7554980 term90). Qed.
Lemma lem7554982 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7554983 : term240 = term234.
Proof. exact (MK_COMB (@lem7554982) (@lem7554981)). Qed.
Lemma lem7554984 : term239 = term233.
Proof. exact (MK_COMB (@lem7554983) (@lem7554978)). Qed.
Lemma lem7554986 (m : nat) (n : nat) : (term162 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7554987 : term233 = term241.
Proof. exact (@lem7554986 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7554988 : term241 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7554989 : term233 = False.
Proof. exact (TRANS (@lem7554987) (@lem7554988)). Qed.
Lemma lem7554990 : term239 = False.
Proof. exact (TRANS (@lem7554984) (@lem7554989)). Qed.
Lemma lem7554991 : term236 = False.
Proof. exact (TRANS (@lem7554975) (@lem7554990)). Qed.
Lemma lem7554992 : term233 = False.
Proof. exact (TRANS (@lem7554952) (@lem7554991)). Qed.
Lemma lem7554993 : term204 = False.
Proof. exact (TRANS (@lem7554943) (@lem7554992)). Qed.
Lemma lem7554994 (h1 : term204) : False.
Proof. exact (EQ_MP (@lem7554993) (@lem7554940 h1)). Qed.
Lemma lem7554995 (h1 : term209) : False.
Proof. exact (or_elim (@lem7554884 h1) (fun h0 : term204 => @lem7554939 h0) (fun h0 : term204 => @lem7554994 h0)). Qed.
Lemma lem7554997 (h1 : term209) : term209.
Proof. exact (h1). Qed.
Lemma lem7554998 (h1 : term209) : term209 = False.
Proof. exact (prop_ext (fun h2 : term209 => @lem7554995 h1) (fun h2 : False => @lem7554997 h1)). Qed.
Lemma lem7554999 (h1 : term209) : False.
Proof. exact (EQ_MP (@lem7554998 h1) (@lem7554997 h1)). Qed.
Lemma lem7555000 (h1 : term135) : term135.
Proof. exact (h1). Qed.
Lemma lem7555001 (h1 : term135) : term209.
Proof. exact (EQ_MP (@lem7554874) (@lem7555000 h1)). Qed.
Lemma lem7555002 (h1 : term135) : term209 = False.
Proof. exact (prop_ext (fun h2 : term209 => @lem7554999 h2) (fun h2 : False => @lem7555001 h1)). Qed.
Lemma lem7555003 (h1 : term135) : False.
Proof. exact (EQ_MP (@lem7555002 h1) (@lem7555001 h1)). Qed.
Lemma lem7555004 : term242.
Proof. exact (fun h0 : term135 => @lem7555003 h0). Qed.
Lemma lem7555005 : term243.
Proof. exact (@lem1386578 term132). Qed.
Lemma lem7555008 : term132.
Proof. exact (@lem7555005 (@lem7555004)). Qed.
Lemma lem7555009 : term131.
Proof. exact (EQ_MP (@lem7554595) (@lem7555008)). Qed.
Lemma lem7555010 : term244.
Proof. exact (ex_intro term245 term83 (@lem7555009)). Qed.
Lemma lem7555011 : term60.
Proof. exact (ex_intro term59 term65 (@lem7555010)). Qed.
Lemma lem7555012 : term39.
Proof. exact (EQ_MP (@lem7554357) (@lem7555011)). Qed.
