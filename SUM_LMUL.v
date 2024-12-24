Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LMUL_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import ITERATE_EXPAND_CASES_spec.
Require Import REAL_ENTIRE_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import SUM_0_spec.
Require Import SUM_CLAUSES_spec.
Require Import sum_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1339188_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Require Import thm82_spec.
Lemma lem7069400 (x : real) : term0 x.
Proof. exact (@lem1339188 x). Qed.
Lemma lem7069401 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7069402 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem7069401 x) (@lem7069400 x)). Qed.
Lemma lem7069403 (x : real) (y : real) : term2 x y.
Proof. exact (@lem7069402 x y). Qed.
Lemma lem7069404 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem7069405 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem7069404 y x) (@lem7069403 x y)). Qed.
Lemma lem7069406 (y : real) (x : real) (z : real) : term4 y x z.
Proof. exact (@lem7069405 y x z). Qed.
Lemma lem7069407 (y : real) (x : real) (z : real) : (term4 y x z) = ((term5 x y z) = (term6 y x z)).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem7069412 (x : real) : term7 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem7069413 (x : real) : (term7 x) = ((term8 x) = term9).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7069415 {_131524 : Type'} : term10 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7069416 {_131524 : Type'} (x : _131524) : term11 _131524 x.
Proof. exact (@lem7069415 _131524 x). Qed.
Lemma lem7069417 {_131524 : Type'} (x : _131524) : (term11 _131524 x) = (term12 _131524 x).
Proof. exact (eq_refl (term11 _131524 x)). Qed.
Lemma lem7069418 {_131524 : Type'} (x : _131524) : term12 _131524 x.
Proof. exact (EQ_MP (@lem7069417 _131524 x) (@lem7069416 _131524 x)). Qed.
Lemma lem7069419 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term13 _131524 x f.
Proof. exact (@lem7069418 _131524 x f). Qed.
Lemma lem7069420 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term13 _131524 x f) = (term14 _131524 x f).
Proof. exact (eq_refl (term13 _131524 x f)). Qed.
Lemma lem7069421 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term14 _131524 x f.
Proof. exact (EQ_MP (@lem7069420 _131524 x f) (@lem7069419 _131524 x f)). Qed.
Lemma lem7069422 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term15 _131524 x f s.
Proof. exact (@lem7069421 _131524 x f s). Qed.
Lemma lem7069423 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term15 _131524 x f s) = (term16 _131524 x s f).
Proof. exact (eq_refl (term15 _131524 x f s)). Qed.
Lemma lem7069424 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term16 _131524 x s f.
Proof. exact (EQ_MP (@lem7069423 _131524 x s f) (@lem7069422 _131524 x f s)). Qed.
Lemma lem7069425 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7069426 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term17 _131524 x s f) = (term18 _131524 x s f).
Proof. exact (@lem7069424 _131524 x s f (@lem7069425 _131524 s h1)). Qed.
Lemma lem7069432 {_131483 : Type'} : term19 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7069433 {_131483 : Type'} (f : _131483 -> real) : term20 _131483 f.
Proof. exact (@lem7069432 _131483 f). Qed.
Lemma lem7069434 {_131483 : Type'} (f : _131483 -> real) : (term20 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term9).
Proof. exact (eq_refl (term20 _131483 f)). Qed.
Lemma lem7069436 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem7069437 {A : Type'} (P : type686 A) (h1 : term21 A) : term22 A P.
Proof. exact (@lem7069436 A h1 P). Qed.
Lemma lem7069438 {A : Type'} (P : type686 A) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem7069439 {A : Type'} (P : type686 A) (h1 : term21 A) : term23 A P.
Proof. exact (EQ_MP (@lem7069438 A P) (@lem7069437 A P h1)). Qed.
Lemma lem7069440 {A : Type'} (P : type686 A) (h1 : term24 A P) : term24 A P.
Proof. exact (h1). Qed.
Lemma lem7069441 {A : Type'} (P : type686 A) (h1 : term21 A) (h2 : term24 A P) : term25 A P.
Proof. exact (@lem7069439 A P h1 (@lem7069440 A P h2)). Qed.
Lemma lem7069442 {A : Type'} (P : type686 A) (h1 : term24 A P) : term26 A P.
Proof. exact (fun h0 : term21 A => @lem7069441 A P h0 h1). Qed.
Lemma lem7069443 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem7069444 {A : Type'} (P : type686 A) (h1 : term21 A) (h2 : term24 A P) : term25 A P.
Proof. exact (@lem7069442 A P h2 (@lem7069443 A h1)). Qed.
Lemma lem7069445 {A : Type'} (P : type686 A) (h1 : term21 A) : term23 A P.
Proof. exact (fun h0 : term24 A P => @lem7069444 A P h1 h0). Qed.
Lemma lem7069446 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (fun P : type686 A => @lem7069445 A P h1). Qed.
Lemma lem7069447 {A : Type'} : term27 A.
Proof. exact (fun h0 : term21 A => @lem7069446 A h0). Qed.
Lemma lem7069448 {A : Type'} : term21 A.
Proof. exact (@lem7069447 A (@lem3558722 A)). Qed.
Lemma lem7069449 {A : Type'} (P : type686 A) : term22 A P.
Proof. exact (@lem7069448 A P). Qed.
Lemma lem7069450 {A : Type'} (P : type686 A) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem7069452 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (h1). Qed.
Lemma lem7069453 {_131408 : Type'} (h1 : (@sum _131408) = (@iterate real _131408 real_add)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (SYM (@lem7069452 _131408 h1)). Qed.
Lemma lem7069454 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (h1). Qed.
Lemma lem7069455 {_131408 : Type'} (h1 : (@iterate real _131408 real_add) = (@sum _131408)) : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (SYM (@lem7069454 _131408 h1)). Qed.
Lemma lem7069456 {_131408 : Type'} : ((@sum _131408) = (@iterate real _131408 real_add)) = ((@iterate real _131408 real_add) = (@sum _131408)).
Proof. exact (prop_ext (fun h1 : (@sum _131408) = (@iterate real _131408 real_add) => @lem7069453 _131408 h1) (fun h1 : (@iterate real _131408 real_add) = (@sum _131408) => @lem7069455 _131408 h1)). Qed.
Lemma lem7069458 (x : real) : term7 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem7069459 (x : real) : (term7 x) = ((term8 x) = term9).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7069461 {_120327 _120333 : Type'} (op : type1400 _120327) : term28 _120327 _120333 op.
Proof. exact (@lem5738118 _120327 _120333 op). Qed.
Lemma lem7069462 {_120327 _120333 : Type'} (op : type1400 _120327) : (term28 _120327 _120333 op) = (term29 _120327 _120333 op).
Proof. exact (eq_refl (term28 _120327 _120333 op)). Qed.
Lemma lem7069463 {_120327 _120333 : Type'} (op : type1400 _120327) : term29 _120327 _120333 op.
Proof. exact (EQ_MP (@lem7069462 _120327 _120333 op) (@lem7069461 _120327 _120333 op)). Qed.
Lemma lem7069464 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : term30 _120327 _120333 op f.
Proof. exact (@lem7069463 _120327 _120333 op f). Qed.
Lemma lem7069465 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term30 _120327 _120333 op f) = (term31 _120327 _120333 f op).
Proof. exact (eq_refl (term30 _120327 _120333 op f)). Qed.
Lemma lem7069466 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : term31 _120327 _120333 f op.
Proof. exact (EQ_MP (@lem7069465 _120327 _120333 f op) (@lem7069464 _120327 _120333 op f)). Qed.
Lemma lem7069467 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) (s : _120333 -> Prop) : term32 _120327 _120333 f op s.
Proof. exact (@lem7069466 _120327 _120333 f op s). Qed.
Lemma lem7069468 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (term32 _120327 _120333 f op s) = ((@iterate _120327 _120333 op s f) = (term33 _120327 _120333 s f op)).
Proof. exact (eq_refl (term32 _120327 _120333 f op s)). Qed.
Lemma lem7069470 (c : real) : term34 c.
Proof. exact (@lem9784 (c = term9)). Qed.
Lemma lem7069471 (c : real) : (term34 c) = (term35 c).
Proof. exact (eq_refl (term34 c)). Qed.
Lemma lem7069472 (c : real) : term35 c.
Proof. exact (EQ_MP (@lem7069471 c) (@lem7069470 c)). Qed.
Lemma lem7069474 (c : real) (h1 : term36 c) : term36 c.
Proof. exact (h1). Qed.
Lemma lem7069475 {A : Type'} (s : A -> Prop) : term37 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7069476 {A : Type'} (s : A -> Prop) : (term37 A s) = ((term38 A s) = term9).
Proof. exact (eq_refl (term37 A s)). Qed.
Lemma lem7069478 (x : real) : term39 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem7069479 (x : real) : (term39 x) = ((term40 x) = term9).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem7069484 (c : real) (h1 : c = term9) : c = term9.
Proof. exact (h1). Qed.
Lemma lem7069485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7069486 (c : real) (h1 : c = term9) : (real_mul c) = term41.
Proof. exact (MK_COMB (@lem7069485) (@lem7069484 c h1)). Qed.
Lemma lem7069487 {A : Type'} (f : A -> real) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7069488 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : c = term9) : (term42 A c f x) = (term43 A f x).
Proof. exact (MK_COMB (@lem7069486 c h1) (@lem7069487 A f x)). Qed.
Lemma lem7069490 (x : real) : (term40 x) = term9.
Proof. exact (EQ_MP (@lem7069479 x) (@lem7069478 x)). Qed.
Lemma lem7069491 {A : Type'} (f : A -> real) (x : A) : (term43 A f x) = term9.
Proof. exact (@lem7069490 (f x)). Qed.
Lemma lem7069492 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : c = term9) : (term42 A c f x) = term9.
Proof. exact (TRANS (@lem7069488 A f x c h1) (@lem7069491 A f x)). Qed.
Lemma lem7069493 {A : Type'} (f : A -> real) (c : real) (h1 : c = term9) : (term44 A c f) = (term45 A).
Proof. exact (fun_ext (fun x : A => @lem7069492 A f x c h1)). Qed.
Lemma lem7069494 {A : Type'} (s : A -> Prop) : (@sum A s) = (@sum A s).
Proof. exact (eq_refl (@sum A s)). Qed.
Lemma lem7069495 {A : Type'} (f : A -> real) (s : A -> Prop) (c : real) (h1 : c = term9) : (term46 A s c f) = (term38 A s).
Proof. exact (MK_COMB (@lem7069494 A s) (@lem7069493 A f c h1)). Qed.
Lemma lem7069497 {A : Type'} (s : A -> Prop) : (term38 A s) = term9.
Proof. exact (EQ_MP (@lem7069476 A s) (@lem7069475 A s)). Qed.
Lemma lem7069498 {A : Type'} (s : A -> Prop) : (term38 A s) = term9.
Proof. exact (@lem7069497 A s). Qed.
Lemma lem7069499 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : (term46 A s c f) = term9.
Proof. exact (TRANS (@lem7069495 A f s c h1) (@lem7069498 A s)). Qed.
Lemma lem7069500 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069501 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : (term47 A s c f) = term48.
Proof. exact (MK_COMB (@lem7069500) (@lem7069499 A s f c h1)). Qed.
Lemma lem7069503 (c : real) (h1 : c = term9) : c = term9.
Proof. exact (h1). Qed.
Lemma lem7069504 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7069505 (c : real) (h1 : c = term9) : (real_mul c) = term41.
Proof. exact (MK_COMB (@lem7069504) (@lem7069503 c h1)). Qed.
Lemma lem7069506 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@sum A s f).
Proof. exact (eq_refl (@sum A s f)). Qed.
Lemma lem7069507 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : (term49 A c s f) = (term50 A s f).
Proof. exact (MK_COMB (@lem7069505 c h1) (@lem7069506 A s f)). Qed.
Lemma lem7069509 (x : real) : (term40 x) = term9.
Proof. exact (EQ_MP (@lem7069479 x) (@lem7069478 x)). Qed.
Lemma lem7069510 {A : Type'} (s : A -> Prop) (f : A -> real) : (term50 A s f) = term9.
Proof. exact (@lem7069509 (@sum A s f)). Qed.
Lemma lem7069511 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : (term49 A c s f) = term9.
Proof. exact (TRANS (@lem7069507 A s f c h1) (@lem7069510 A s f)). Qed.
Lemma lem7069512 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : ((term46 A s c f) = (term49 A c s f)) = (term9 = term9).
Proof. exact (MK_COMB (@lem7069501 A s f c h1) (@lem7069511 A s f c h1)). Qed.
Lemma lem7069514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069515 (x : real) : (x = x) = True.
Proof. exact (@lem7069514 real x). Qed.
Lemma lem7069516 : (term9 = term9) = True.
Proof. exact (@lem7069515 term9). Qed.
Lemma lem7069517 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : ((term46 A s c f) = (term49 A c s f)) = True.
Proof. exact (TRANS (@lem7069512 A s f c h1) (@lem7069516)). Qed.
Lemma lem7069518 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : True = ((term46 A s c f) = (term49 A c s f)).
Proof. exact (SYM (@lem7069517 A s f c h1)). Qed.
Lemma lem7069519 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : c = term9) : (term46 A s c f) = (term49 A c s f).
Proof. exact (EQ_MP (@lem7069518 A s f c h1) (@lem0)). Qed.
Lemma lem7069546 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7069547 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7069546 A). Qed.
Lemma lem7069548 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7069549 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7069547 A) (@lem7069548 A s)). Qed.
Lemma lem7069550 {A : Type'} (c : real) (f : A -> real) : (term44 A c f) = (term44 A c f).
Proof. exact (eq_refl (term44 A c f)). Qed.
Lemma lem7069551 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term46 A s c f) = (term51 A s c f).
Proof. exact (MK_COMB (@lem7069549 A s) (@lem7069550 A c f)). Qed.
Lemma lem7069552 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069553 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term47 A s c f) = (term52 A s c f).
Proof. exact (MK_COMB (@lem7069552) (@lem7069551 A s c f)). Qed.
Lemma lem7069555 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7069556 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7069555 A). Qed.
Lemma lem7069557 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7069558 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7069556 A) (@lem7069557 A s)). Qed.
Lemma lem7069559 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7069560 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7069558 A s) (@lem7069559 A f)). Qed.
Lemma lem7069561 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7069562 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term49 A c s f) = (term53 A c s f).
Proof. exact (MK_COMB (@lem7069561 c) (@lem7069560 A s f)). Qed.
Lemma lem7069563 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term46 A s c f) = (term49 A c s f)) = ((term51 A s c f) = (term53 A c s f)).
Proof. exact (MK_COMB (@lem7069553 A s c f) (@lem7069562 A c s f)). Qed.
Lemma lem7069566 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term51 A s c f) = (term53 A c s f)) = ((term46 A s c f) = (term49 A c s f)).
Proof. exact (SYM (@lem7069563 A c s f)). Qed.
Lemma lem7069570 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term33 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem7069468 _120327 _120333 s f op) (@lem7069467 _120327 _120333 f op s)). Qed.
Lemma lem7069571 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@iterate real A op s f) = (term54 A s f op).
Proof. exact (@lem7069570 real A s f op). Qed.
Lemma lem7069572 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term51 A s c f) = (term55 A s c f).
Proof. exact (@lem7069571 A s (term44 A c f) real_add). Qed.
Lemma lem7069573 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069574 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term52 A s c f) = (term56 A s c f).
Proof. exact (MK_COMB (@lem7069573) (@lem7069572 A s c f)). Qed.
Lemma lem7069576 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term33 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem7069468 _120327 _120333 s f op) (@lem7069467 _120327 _120333 f op s)). Qed.
Lemma lem7069577 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@iterate real A op s f) = (term54 A s f op).
Proof. exact (@lem7069576 real A s f op). Qed.
Lemma lem7069578 {A : Type'} (s : A -> Prop) (f : A -> real) : (@iterate real A real_add s f) = (term57 A s f).
Proof. exact (@lem7069577 A s f real_add). Qed.
Lemma lem7069579 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7069580 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term53 A c s f) = (term58 A c s f).
Proof. exact (MK_COMB (@lem7069579 c) (@lem7069578 A s f)). Qed.
Lemma lem7069581 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term51 A s c f) = (term53 A c s f)) = ((term55 A s c f) = (term58 A c s f)).
Proof. exact (MK_COMB (@lem7069574 A s c f) (@lem7069580 A c s f)). Qed.
Lemma lem7069582 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term55 A s c f) = (term58 A c s f)) = ((term51 A s c f) = (term53 A c s f)).
Proof. exact (SYM (@lem7069581 A c s f)). Qed.
Lemma lem7069583 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : (term59 A c f s) = (@support A real real_add f s)) : (term59 A c f s) = (@support A real real_add f s).
Proof. exact (h1). Qed.
Lemma lem7069584 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term60 A c s f) = (term60 A c s f).
Proof. exact (eq_refl (term60 A c s f)). Qed.
Lemma lem7069585 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : (term59 A c f s) = (@support A real real_add f s)) : (term61 A c f s) = (term62 A c f s).
Proof. exact (MK_COMB (@lem7069584 A c s f) (@lem7069583 A c f s h1)). Qed.
Lemma lem7069586 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term62 A c f s) = ((term63 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl (term62 A c f s)). Qed.
Lemma lem7069587 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : (term64 A c f s) = (term64 A c f s).
Proof. exact (eq_refl (term64 A c f s)). Qed.
Lemma lem7069588 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term61 A c f s) = (term62 A c f s)) = ((term61 A c f s) = ((term63 A s c f) = (term58 A c s f))).
Proof. exact (MK_COMB (@lem7069587 A c f s) (@lem7069586 A c s f)). Qed.
Lemma lem7069589 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term61 A c f s) = ((term55 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl (term61 A c f s)). Qed.
Lemma lem7069590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7069591 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term64 A c f s) = (term65 A c s f).
Proof. exact (MK_COMB (@lem7069590) (@lem7069589 A c s f)). Qed.
Lemma lem7069592 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term63 A s c f) = (term58 A c s f)) = ((term63 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl ((term63 A s c f) = (term58 A c s f))). Qed.
Lemma lem7069593 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term61 A c f s) = ((term63 A s c f) = (term58 A c s f))) = (((term55 A s c f) = (term58 A c s f)) = ((term63 A s c f) = (term58 A c s f))).
Proof. exact (MK_COMB (@lem7069591 A c s f) (@lem7069592 A c s f)). Qed.
Lemma lem7069594 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term61 A c f s) = (term62 A c f s)) = (((term55 A s c f) = (term58 A c s f)) = ((term63 A s c f) = (term58 A c s f))).
Proof. exact (TRANS (@lem7069588 A c s f) (@lem7069593 A c s f)). Qed.
Lemma lem7069595 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : (term59 A c f s) = (@support A real real_add f s)) : ((term55 A s c f) = (term58 A c s f)) = ((term63 A s c f) = (term58 A c s f)).
Proof. exact (EQ_MP (@lem7069594 A c s f) (@lem7069585 A c f s h1)). Qed.
Lemma lem7069596 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : (term59 A c f s) = (@support A real real_add f s)) : ((term63 A s c f) = (term58 A c s f)) = ((term55 A s c f) = (term58 A c s f)).
Proof. exact (SYM (@lem7069595 A c f s h1)). Qed.
Lemma lem7069597 (x : real) : term66 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem7069598 (x : real) : (term66 x) = (term67 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem7069599 (x : real) : term67 x.
Proof. exact (EQ_MP (@lem7069598 x) (@lem7069597 x)). Qed.
Lemma lem7069600 (x : real) (y : real) : term68 x y.
Proof. exact (@lem7069599 x y). Qed.
Lemma lem7069601 (x : real) (y : real) : (term68 x y) = (((real_mul x y) = term9) = (term69 x y)).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem7069603 {A B : Type'} (s : A -> Prop) : term70 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem7069604 {A B : Type'} (s : A -> Prop) : (term70 A B s) = (term71 A B s).
Proof. exact (eq_refl (term70 A B s)). Qed.
Lemma lem7069605 {A B : Type'} (s : A -> Prop) : term71 A B s.
Proof. exact (EQ_MP (@lem7069604 A B s) (@lem7069603 A B s)). Qed.
Lemma lem7069606 {A B : Type'} (s : A -> Prop) (f : A -> B) : term72 A B s f.
Proof. exact (@lem7069605 A B s f). Qed.
Lemma lem7069607 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term73 A B s f).
Proof. exact (eq_refl (term72 A B s f)). Qed.
Lemma lem7069608 {A B : Type'} (s : A -> Prop) (f : A -> B) : term73 A B s f.
Proof. exact (EQ_MP (@lem7069607 A B s f) (@lem7069606 A B s f)). Qed.
Lemma lem7069609 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term74 A B s f op.
Proof. exact (@lem7069608 A B s f op). Qed.
Lemma lem7069610 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term74 A B s f op) = ((@support A B op f s) = (term75 A B s f op)).
Proof. exact (eq_refl (term74 A B s f op)). Qed.
Lemma lem7069612 (c : real) : term76 c.
Proof. exact (@lem82 (c = term9)). Qed.
Lemma lem7069628 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term75 A B s f op).
Proof. exact (EQ_MP (@lem7069610 A B s f op) (@lem7069609 A B s f op)). Qed.
Lemma lem7069629 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@support A real op f s) = (term77 A s f op).
Proof. exact (@lem7069628 A real s f op). Qed.
Lemma lem7069630 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term59 A c f s) = (term78 A s c f).
Proof. exact (@lem7069629 A s (term44 A c f) real_add). Qed.
Lemma lem7069640 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7069641 {A : Type'} (f : A -> real) (y : A) : (term80 A f y) = (f y).
Proof. exact (@lem7069640 A real f y). Qed.
Lemma lem7069642 {A : Type'} (c : real) (f : A -> real) (x : A) : (term81 A c f x) = (term82 A c f x).
Proof. exact (@lem7069641 A (term44 A c f) x). Qed.
Lemma lem7069643 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (eq_refl (term82 A c f x)). Qed.
Lemma lem7069644 {A : Type'} (c : real) (f : A -> real) : (term83 A c f) = (term44 A c f).
Proof. exact (fun_ext (fun x : A => @lem7069643 A c f x)). Qed.
Lemma lem7069645 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7069646 {A : Type'} (c : real) (f : A -> real) (x : A) : (term81 A c f x) = (term82 A c f x).
Proof. exact (MK_COMB (@lem7069644 A c f) (@lem7069645 A x)). Qed.
Lemma lem7069647 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069648 {A : Type'} (c : real) (f : A -> real) (x : A) : (term84 A c f x) = (term85 A c f x).
Proof. exact (MK_COMB (@lem7069647) (@lem7069646 A c f x)). Qed.
Lemma lem7069649 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (eq_refl (term82 A c f x)). Qed.
Lemma lem7069650 {A : Type'} (c : real) (f : A -> real) (x : A) : ((term81 A c f x) = (term82 A c f x)) = ((term82 A c f x) = (term42 A c f x)).
Proof. exact (MK_COMB (@lem7069648 A c f x) (@lem7069649 A c f x)). Qed.
Lemma lem7069651 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (EQ_MP (@lem7069650 A c f x) (@lem7069642 A c f x)). Qed.
Lemma lem7069652 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069653 {A : Type'} (c : real) (f : A -> real) (x : A) : (term85 A c f x) = (term86 A c f x).
Proof. exact (MK_COMB (@lem7069652) (@lem7069651 A c f x)). Qed.
Lemma lem7069655 : (@neutral real real_add) = term9.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7069656 {A : Type'} (c : real) (f : A -> real) (x : A) : ((term82 A c f x) = (@neutral real real_add)) = ((term42 A c f x) = term9).
Proof. exact (MK_COMB (@lem7069653 A c f x) (@lem7069655)). Qed.
Lemma lem7069658 (x : real) (y : real) : ((real_mul x y) = term9) = (term69 x y).
Proof. exact (EQ_MP (@lem7069601 x y) (@lem7069600 x y)). Qed.
Lemma lem7069659 {A : Type'} (c : real) (f : A -> real) (x : A) : ((term42 A c f x) = term9) = (term87 A c f x).
Proof. exact (@lem7069658 c (f x)). Qed.
Lemma lem7069663 (c : real) (h1 : term36 c) : (c = term9) = False.
Proof. exact (@lem7069612 c (@lem7069474 c h1)). Qed.
Lemma lem7069664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7069665 (c : real) (h1 : term36 c) : (term88 c) = (or False).
Proof. exact (MK_COMB (@lem7069664) (@lem7069663 c h1)). Qed.
Lemma lem7069668 {A : Type'} (f : A -> real) (x : A) : ((f x) = term9) = ((f x) = term9).
Proof. exact (eq_refl ((f x) = term9)). Qed.
Lemma lem7069669 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term87 A c f x) = (term89 A f x).
Proof. exact (MK_COMB (@lem7069665 c h1) (@lem7069668 A f x)). Qed.
Lemma lem7069671 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem7069672 {A : Type'} (f : A -> real) (x : A) : (term89 A f x) = ((f x) = term9).
Proof. exact (@lem7069671 ((f x) = term9)). Qed.
Lemma lem7069675 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term87 A c f x) = ((f x) = term9).
Proof. exact (TRANS (@lem7069669 A f x c h1) (@lem7069672 A f x)). Qed.
Lemma lem7069676 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : term36 c) : ((term42 A c f x) = term9) = ((f x) = term9).
Proof. exact (TRANS (@lem7069659 A c f x) (@lem7069675 A f x c h1)). Qed.
Lemma lem7069677 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : term36 c) : ((term82 A c f x) = (@neutral real real_add)) = ((f x) = term9).
Proof. exact (TRANS (@lem7069656 A c f x) (@lem7069676 A f x c h1)). Qed.
Lemma lem7069678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7069679 {A : Type'} (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term90 A c f x) = (term91 A f x).
Proof. exact (MK_COMB (@lem7069678) (@lem7069677 A f x c h1)). Qed.
Lemma lem7069682 {A : Type'} (x : A) (s : A -> Prop) : (term92 A x s) = (term92 A x s).
Proof. exact (eq_refl (term92 A x s)). Qed.
Lemma lem7069683 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term93 A s c f x) = (term94 A s f x).
Proof. exact (MK_COMB (@lem7069682 A x s) (@lem7069679 A f x c h1)). Qed.
Lemma lem7069688 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7069689 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term95 A GEN_PVAR_237 s c f x) = (term96 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7069688 A GEN_PVAR_237) (@lem7069683 A s f x c h1)). Qed.
Lemma lem7069694 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7069695 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) (c : real) (h1 : term36 c) : (term97 A GEN_PVAR_237 s c f x) = (term98 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7069689 A GEN_PVAR_237 s f x c h1) (@lem7069694 A x)). Qed.
Lemma lem7069700 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term99 A GEN_PVAR_237 s c f) = (term100 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7069695 A GEN_PVAR_237 s f x c h1)). Qed.
Lemma lem7069705 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7069706 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term101 A GEN_PVAR_237 s c f) = (term102 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7069705 A) (@lem7069700 A GEN_PVAR_237 s f c h1)). Qed.
Lemma lem7069715 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term103 A s c f) = (term104 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7069706 A GEN_PVAR_237 s f c h1)). Qed.
Lemma lem7069724 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7069725 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term78 A s c f) = (term105 A s f).
Proof. exact (MK_COMB (@lem7069724 A) (@lem7069715 A s f c h1)). Qed.
Lemma lem7069734 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term59 A c f s) = (term105 A s f).
Proof. exact (TRANS (@lem7069630 A s c f) (@lem7069725 A s f c h1)). Qed.
Lemma lem7069735 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem7069736 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term106 A c f s) = (term107 A s f).
Proof. exact (MK_COMB (@lem7069735 A) (@lem7069734 A s f c h1)). Qed.
Lemma lem7069746 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term75 A B s f op).
Proof. exact (EQ_MP (@lem7069610 A B s f op) (@lem7069609 A B s f op)). Qed.
Lemma lem7069747 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@support A real op f s) = (term77 A s f op).
Proof. exact (@lem7069746 A real s f op). Qed.
Lemma lem7069748 {A : Type'} (s : A -> Prop) (f : A -> real) : (@support A real real_add f s) = (term108 A s f).
Proof. exact (@lem7069747 A s f real_add). Qed.
Lemma lem7069758 : (@neutral real real_add) = term9.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7069759 {A : Type'} (f : A -> real) (x : A) : (term109 A f x) = (term109 A f x).
Proof. exact (eq_refl (term109 A f x)). Qed.
Lemma lem7069760 {A : Type'} (f : A -> real) (x : A) : ((f x) = (@neutral real real_add)) = ((f x) = term9).
Proof. exact (MK_COMB (@lem7069759 A f x) (@lem7069758)). Qed.
Lemma lem7069763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7069764 {A : Type'} (f : A -> real) (x : A) : (term110 A f x) = (term91 A f x).
Proof. exact (MK_COMB (@lem7069763) (@lem7069760 A f x)). Qed.
Lemma lem7069767 {A : Type'} (x : A) (s : A -> Prop) : (term92 A x s) = (term92 A x s).
Proof. exact (eq_refl (term92 A x s)). Qed.
Lemma lem7069768 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term111 A s f x) = (term94 A s f x).
Proof. exact (MK_COMB (@lem7069767 A x s) (@lem7069764 A f x)). Qed.
Lemma lem7069773 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7069774 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term112 A GEN_PVAR_237 s f x) = (term96 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7069773 A GEN_PVAR_237) (@lem7069768 A s f x)). Qed.
Lemma lem7069779 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7069780 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term113 A GEN_PVAR_237 s f x) = (term98 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7069774 A GEN_PVAR_237 s f x) (@lem7069779 A x)). Qed.
Lemma lem7069785 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) : (term114 A GEN_PVAR_237 s f) = (term100 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7069780 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7069790 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7069791 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) : (term115 A GEN_PVAR_237 s f) = (term102 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7069790 A) (@lem7069785 A GEN_PVAR_237 s f)). Qed.
Lemma lem7069800 {A : Type'} (s : A -> Prop) (f : A -> real) : (term116 A s f) = (term104 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7069791 A GEN_PVAR_237 s f)). Qed.
Lemma lem7069809 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7069810 {A : Type'} (s : A -> Prop) (f : A -> real) : (term108 A s f) = (term105 A s f).
Proof. exact (MK_COMB (@lem7069809 A) (@lem7069800 A s f)). Qed.
Lemma lem7069819 {A : Type'} (s : A -> Prop) (f : A -> real) : (@support A real real_add f s) = (term105 A s f).
Proof. exact (TRANS (@lem7069748 A s f) (@lem7069810 A s f)). Qed.
Lemma lem7069820 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : ((term59 A c f s) = (@support A real real_add f s)) = ((term105 A s f) = (term105 A s f)).
Proof. exact (MK_COMB (@lem7069736 A s f c h1) (@lem7069819 A s f)). Qed.
Lemma lem7069822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069823 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7069822 (A -> Prop) x). Qed.
Lemma lem7069824 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term105 A s f) = (term105 A s f)) = True.
Proof. exact (@lem7069823 A (term105 A s f)). Qed.
Lemma lem7069825 {A : Type'} (f : A -> real) (s : A -> Prop) (c : real) (h1 : term36 c) : ((term59 A c f s) = (@support A real real_add f s)) = True.
Proof. exact (TRANS (@lem7069820 A s f c h1) (@lem7069824 A s f)). Qed.
Lemma lem7069826 {A : Type'} (f : A -> real) (s : A -> Prop) (c : real) (h1 : term36 c) : True = ((term59 A c f s) = (@support A real real_add f s)).
Proof. exact (SYM (@lem7069825 A f s c h1)). Qed.
Lemma lem7069827 {A : Type'} (f : A -> real) (s : A -> Prop) (c : real) (h1 : term36 c) : (term59 A c f s) = (@support A real real_add f s).
Proof. exact (EQ_MP (@lem7069826 A f s c h1) (@lem0)). Qed.
Lemma lem7069828 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term117 _476 _475 _474 _477) = (term118 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem7069829 {A : Type'} (_474 : real) (_475 : Prop) (c : real) (s : A -> Prop) (f : A -> real) (_477 : real) : (term119 A c s f _475 _474 _477) = (term120 A _474 _475 c s f _477).
Proof. exact (@lem7069828 _474 _475 (term121 A c s f) _477). Qed.
Lemma lem7069830 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term122 A s c f) = (term123 A c s f).
Proof. exact (@lem7069829 A (term124 A s c f) (term125 A f s) c s f (@neutral real real_add)). Qed.
Lemma lem7069831 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term126 A c s f) = ((@neutral real real_add) = (term58 A c s f)).
Proof. exact (eq_refl (term126 A c s f)). Qed.
Lemma lem7069832 {A : Type'} (f : A -> real) (s : A -> Prop) : (term127 A f s) = (term127 A f s).
Proof. exact (eq_refl (term127 A f s)). Qed.
Lemma lem7069833 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term128 A c s f) = (term129 A c s f).
Proof. exact (MK_COMB (@lem7069832 A f s) (@lem7069831 A c s f)). Qed.
Lemma lem7069834 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term130 A s c f) = ((term124 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl (term130 A s c f)). Qed.
Lemma lem7069835 {A : Type'} (f : A -> real) (s : A -> Prop) : (term131 A f s) = (term131 A f s).
Proof. exact (eq_refl (term131 A f s)). Qed.
Lemma lem7069836 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term132 A s c f) = (term133 A c s f).
Proof. exact (MK_COMB (@lem7069835 A f s) (@lem7069834 A c s f)). Qed.
Lemma lem7069837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7069838 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term134 A s c f) = (term135 A c s f).
Proof. exact (MK_COMB (@lem7069837) (@lem7069836 A c s f)). Qed.
Lemma lem7069839 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term123 A c s f) = (term136 A c s f).
Proof. exact (MK_COMB (@lem7069838 A c s f) (@lem7069833 A c s f)). Qed.
Lemma lem7069840 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term122 A s c f) = ((term63 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl (term122 A s c f)). Qed.
Lemma lem7069841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7069842 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term137 A s c f) = (term138 A c s f).
Proof. exact (MK_COMB (@lem7069841) (@lem7069840 A c s f)). Qed.
Lemma lem7069843 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term122 A s c f) = (term123 A c s f)) = (((term63 A s c f) = (term58 A c s f)) = (term136 A c s f)).
Proof. exact (MK_COMB (@lem7069842 A c s f) (@lem7069839 A c s f)). Qed.
Lemma lem7069844 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term63 A s c f) = (term58 A c s f)) = (term136 A c s f).
Proof. exact (EQ_MP (@lem7069843 A c s f) (@lem7069830 A c s f)). Qed.
Lemma lem7069845 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term136 A c s f) = ((term63 A s c f) = (term58 A c s f)).
Proof. exact (SYM (@lem7069844 A c s f)). Qed.
Lemma lem7069846 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : term125 A f s.
Proof. exact (h1). Qed.
Lemma lem7069847 {A : Type'} (f : A -> real) (s : A -> Prop) : (term125 A f s) = ((term125 A f s) = True).
Proof. exact (@lem7 (term125 A f s)). Qed.
Lemma lem7069848 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term125 A f s) = True.
Proof. exact (EQ_MP (@lem7069847 A f s) (@lem7069846 A f s h1)). Qed.
Lemma lem7069849 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term139 A c s f) = (term139 A c s f).
Proof. exact (eq_refl (term139 A c s f)). Qed.
Lemma lem7069850 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term140 A c f s) = (term141 A c s f).
Proof. exact (MK_COMB (@lem7069849 A c s f) (@lem7069848 A f s h1)). Qed.
Lemma lem7069851 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term141 A c s f) = ((term124 A s c f) = (term142 A c s f)).
Proof. exact (eq_refl (term141 A c s f)). Qed.
Lemma lem7069852 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : (term143 A c f s) = (term143 A c f s).
Proof. exact (eq_refl (term143 A c f s)). Qed.
Lemma lem7069853 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term140 A c f s) = (term141 A c s f)) = ((term140 A c f s) = ((term124 A s c f) = (term142 A c s f))).
Proof. exact (MK_COMB (@lem7069852 A c f s) (@lem7069851 A c s f)). Qed.
Lemma lem7069854 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term140 A c f s) = ((term124 A s c f) = (term58 A c s f)).
Proof. exact (eq_refl (term140 A c f s)). Qed.
Lemma lem7069855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7069856 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term143 A c f s) = (term144 A c s f).
Proof. exact (MK_COMB (@lem7069855) (@lem7069854 A c s f)). Qed.
Lemma lem7069857 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term124 A s c f) = (term142 A c s f)) = ((term124 A s c f) = (term142 A c s f)).
Proof. exact (eq_refl ((term124 A s c f) = (term142 A c s f))). Qed.
Lemma lem7069858 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term140 A c f s) = ((term124 A s c f) = (term142 A c s f))) = (((term124 A s c f) = (term58 A c s f)) = ((term124 A s c f) = (term142 A c s f))).
Proof. exact (MK_COMB (@lem7069856 A c s f) (@lem7069857 A c s f)). Qed.
Lemma lem7069859 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term140 A c f s) = (term141 A c s f)) = (((term124 A s c f) = (term58 A c s f)) = ((term124 A s c f) = (term142 A c s f))).
Proof. exact (TRANS (@lem7069853 A c s f) (@lem7069858 A c s f)). Qed.
Lemma lem7069860 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : ((term124 A s c f) = (term58 A c s f)) = ((term124 A s c f) = (term142 A c s f)).
Proof. exact (EQ_MP (@lem7069859 A c s f) (@lem7069850 A c f s h1)). Qed.
Lemma lem7069861 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : ((term124 A s c f) = (term142 A c s f)) = ((term124 A s c f) = (term58 A c s f)).
Proof. exact (SYM (@lem7069860 A c f s h1)). Qed.
Lemma lem7069862 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : term145 A f s.
Proof. exact (h1). Qed.
Lemma lem7069863 {A : Type'} (f : A -> real) (s : A -> Prop) : term146 A f s.
Proof. exact (@lem82 (term125 A f s)). Qed.
Lemma lem7069864 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : (term125 A f s) = False.
Proof. exact (@lem7069863 A f s (@lem7069862 A f s h1)). Qed.
Lemma lem7069865 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term147 A c s f) = (term147 A c s f).
Proof. exact (eq_refl (term147 A c s f)). Qed.
Lemma lem7069866 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : (term148 A c f s) = (term149 A c s f).
Proof. exact (MK_COMB (@lem7069865 A c s f) (@lem7069864 A f s h1)). Qed.
Lemma lem7069867 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term149 A c s f) = ((@neutral real real_add) = (term150 A c s f)).
Proof. exact (eq_refl (term149 A c s f)). Qed.
Lemma lem7069868 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : (term151 A c f s) = (term151 A c f s).
Proof. exact (eq_refl (term151 A c f s)). Qed.
Lemma lem7069869 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term148 A c f s) = (term149 A c s f)) = ((term148 A c f s) = ((@neutral real real_add) = (term150 A c s f))).
Proof. exact (MK_COMB (@lem7069868 A c f s) (@lem7069867 A c s f)). Qed.
Lemma lem7069870 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term148 A c f s) = ((@neutral real real_add) = (term58 A c s f)).
Proof. exact (eq_refl (term148 A c f s)). Qed.
Lemma lem7069871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7069872 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term151 A c f s) = (term152 A c s f).
Proof. exact (MK_COMB (@lem7069871) (@lem7069870 A c s f)). Qed.
Lemma lem7069873 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((@neutral real real_add) = (term150 A c s f)) = ((@neutral real real_add) = (term150 A c s f)).
Proof. exact (eq_refl ((@neutral real real_add) = (term150 A c s f))). Qed.
Lemma lem7069874 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term148 A c f s) = ((@neutral real real_add) = (term150 A c s f))) = (((@neutral real real_add) = (term58 A c s f)) = ((@neutral real real_add) = (term150 A c s f))).
Proof. exact (MK_COMB (@lem7069872 A c s f) (@lem7069873 A c s f)). Qed.
Lemma lem7069875 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term148 A c f s) = (term149 A c s f)) = (((@neutral real real_add) = (term58 A c s f)) = ((@neutral real real_add) = (term150 A c s f))).
Proof. exact (TRANS (@lem7069869 A c s f) (@lem7069874 A c s f)). Qed.
Lemma lem7069876 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : ((@neutral real real_add) = (term58 A c s f)) = ((@neutral real real_add) = (term150 A c s f)).
Proof. exact (EQ_MP (@lem7069875 A c s f) (@lem7069866 A c f s h1)). Qed.
Lemma lem7069877 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : ((@neutral real real_add) = (term150 A c s f)) = ((@neutral real real_add) = (term58 A c s f)).
Proof. exact (SYM (@lem7069876 A c f s h1)). Qed.
Lemma lem7069881 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7069882 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7069881 real t2 t1). Qed.
Lemma lem7069883 {A : Type'} (s : A -> Prop) (f : A -> real) : (term153 A s f) = (term154 A s f).
Proof. exact (@lem7069882 (@neutral real real_add) (term154 A s f)). Qed.
Lemma lem7069884 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7069885 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term142 A c s f) = (term155 A c s f).
Proof. exact (MK_COMB (@lem7069884 c) (@lem7069883 A s f)). Qed.
Lemma lem7069886 {A : Type'} (s : A -> Prop) (c : real) (f : A -> real) : (term156 A s c f) = (term156 A s c f).
Proof. exact (eq_refl (term156 A s c f)). Qed.
Lemma lem7069887 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term124 A s c f) = (term142 A c s f)) = ((term124 A s c f) = (term155 A c s f)).
Proof. exact (MK_COMB (@lem7069886 A s c f) (@lem7069885 A c s f)). Qed.
Lemma lem7069890 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((term124 A s c f) = (term155 A c s f)) = ((term124 A s c f) = (term142 A c s f)).
Proof. exact (SYM (@lem7069887 A c s f)). Qed.
Lemma lem7069894 : (@neutral real real_add) = term9.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7069895 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069896 : term157 = term48.
Proof. exact (MK_COMB (@lem7069895) (@lem7069894)). Qed.
Lemma lem7069898 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7069899 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7069898 real t1 t2). Qed.
Lemma lem7069900 {A : Type'} (s : A -> Prop) (f : A -> real) : (term158 A s f) = (@neutral real real_add).
Proof. exact (@lem7069899 (term154 A s f) (@neutral real real_add)). Qed.
Lemma lem7069902 : (@neutral real real_add) = term9.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7069903 {A : Type'} (s : A -> Prop) (f : A -> real) : (term158 A s f) = term9.
Proof. exact (TRANS (@lem7069900 A s f) (@lem7069902)). Qed.
Lemma lem7069904 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7069905 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term150 A c s f) = (term8 c).
Proof. exact (MK_COMB (@lem7069904 c) (@lem7069903 A s f)). Qed.
Lemma lem7069907 (x : real) : (term8 x) = term9.
Proof. exact (EQ_MP (@lem7069459 x) (@lem7069458 x)). Qed.
Lemma lem7069908 (c : real) : (term8 c) = term9.
Proof. exact (@lem7069907 c). Qed.
Lemma lem7069909 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term150 A c s f) = term9.
Proof. exact (TRANS (@lem7069905 A s f c) (@lem7069908 c)). Qed.
Lemma lem7069910 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((@neutral real real_add) = (term150 A c s f)) = (term9 = term9).
Proof. exact (MK_COMB (@lem7069896) (@lem7069909 A c s f)). Qed.
Lemma lem7069912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069913 (x : real) : (x = x) = True.
Proof. exact (@lem7069912 real x). Qed.
Lemma lem7069914 : (term9 = term9) = True.
Proof. exact (@lem7069913 term9). Qed.
Lemma lem7069915 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : ((@neutral real real_add) = (term150 A c s f)) = True.
Proof. exact (TRANS (@lem7069910 A c s f) (@lem7069914)). Qed.
Lemma lem7069916 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : True = ((@neutral real real_add) = (term150 A c s f)).
Proof. exact (SYM (@lem7069915 A c s f)). Qed.
Lemma lem7069917 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (@neutral real real_add) = (term150 A c s f).
Proof. exact (EQ_MP (@lem7069916 A c s f) (@lem0)). Qed.
Lemma lem7069927 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7069456 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7069928 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7069927 A). Qed.
Lemma lem7069929 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7069930 {A : Type'} (t : A -> Prop) : (@iterate real A real_add t) = (@sum A t).
Proof. exact (MK_COMB (@lem7069928 A) (@lem7069929 A t)). Qed.
Lemma lem7069931 {A : Type'} (c : real) (f : A -> real) : (term44 A c f) = (term44 A c f).
Proof. exact (eq_refl (term44 A c f)). Qed.
Lemma lem7069932 {A : Type'} (t : A -> Prop) (c : real) (f : A -> real) : (term51 A t c f) = (term46 A t c f).
Proof. exact (MK_COMB (@lem7069930 A t) (@lem7069931 A c f)). Qed.
Lemma lem7069933 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069934 {A : Type'} (t : A -> Prop) (c : real) (f : A -> real) : (term52 A t c f) = (term47 A t c f).
Proof. exact (MK_COMB (@lem7069933) (@lem7069932 A t c f)). Qed.
Lemma lem7069936 {_131408 : Type'} : (@iterate real _131408 real_add) = (@sum _131408).
Proof. exact (EQ_MP (@lem7069456 _131408) (@lem7064112 _131408)). Qed.
Lemma lem7069937 {A : Type'} : (@iterate real A real_add) = (@sum A).
Proof. exact (@lem7069936 A). Qed.
Lemma lem7069938 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7069939 {A : Type'} (t : A -> Prop) : (@iterate real A real_add t) = (@sum A t).
Proof. exact (MK_COMB (@lem7069937 A) (@lem7069938 A t)). Qed.
Lemma lem7069940 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7069941 {A : Type'} (t : A -> Prop) (f : A -> real) : (@iterate real A real_add t f) = (@sum A t f).
Proof. exact (MK_COMB (@lem7069939 A t) (@lem7069940 A f)). Qed.
Lemma lem7069942 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7069943 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term53 A c t f) = (term49 A c t f).
Proof. exact (MK_COMB (@lem7069942 c) (@lem7069941 A t f)). Qed.
Lemma lem7069944 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : ((term51 A t c f) = (term53 A c t f)) = ((term46 A t c f) = (term49 A c t f)).
Proof. exact (MK_COMB (@lem7069934 A t c f) (@lem7069943 A c t f)). Qed.
Lemma lem7069947 {A : Type'} (t : A -> Prop) : (term159 A t) = (term159 A t).
Proof. exact (eq_refl (term159 A t)). Qed.
Lemma lem7069948 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term160 A c t f) = (term161 A c t f).
Proof. exact (MK_COMB (@lem7069947 A t) (@lem7069944 A c t f)). Qed.
Lemma lem7069951 {A : Type'} (c : real) (f : A -> real) : (term162 A c f) = (term163 A c f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7069948 A c t f)). Qed.
Lemma lem7069952 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069953 {A : Type'} (c : real) (f : A -> real) : (term164 A c f) = (term165 A c f).
Proof. exact (MK_COMB (@lem7069952 A) (@lem7069951 A c f)). Qed.
Lemma lem7069958 {A : Type'} (c : real) (f : A -> real) : (term165 A c f) = (term164 A c f).
Proof. exact (SYM (@lem7069953 A c f)). Qed.
Lemma lem7069960 {A : Type'} (P : type686 A) : term23 A P.
Proof. exact (EQ_MP (@lem7069450 A P) (@lem7069449 A P)). Qed.
Lemma lem7069961 {A : Type'} (P : type686 A) : term23 A P.
Proof. exact (@lem7069960 A P). Qed.
Lemma lem7069962 {A : Type'} (c : real) (f : A -> real) : term166 A c f.
Proof. exact (@lem7069961 A (term167 A c f)). Qed.
Lemma lem7069963 {A : Type'} (c : real) (f : A -> real) : (term168 A c f) = ((term169 A c f) = (term170 A c f)).
Proof. exact (eq_refl (term168 A c f)). Qed.
Lemma lem7069964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7069965 {A : Type'} (c : real) (f : A -> real) : (term171 A c f) = (term172 A c f).
Proof. exact (MK_COMB (@lem7069964) (@lem7069963 A c f)). Qed.
Lemma lem7069966 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term173 A c f t) = ((term46 A t c f) = (term49 A c t f)).
Proof. exact (eq_refl (term173 A c f t)). Qed.
Lemma lem7069967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7069968 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term174 A c f t) = (term175 A c t f).
Proof. exact (MK_COMB (@lem7069967) (@lem7069966 A c t f)). Qed.
Lemma lem7069969 {A : Type'} (x : A) (t : A -> Prop) : (term176 A x t) = (term176 A x t).
Proof. exact (eq_refl (term176 A x t)). Qed.
Lemma lem7069970 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : (term177 A c f x t) = (term178 A c f x t).
Proof. exact (MK_COMB (@lem7069968 A c t f) (@lem7069969 A x t)). Qed.
Lemma lem7069971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7069972 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : (term179 A c f x t) = (term180 A c f x t).
Proof. exact (MK_COMB (@lem7069971) (@lem7069970 A c f x t)). Qed.
Lemma lem7069973 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) : (term181 A c f x t) = ((term182 A x t c f) = (term183 A c x t f)).
Proof. exact (eq_refl (term181 A c f x t)). Qed.
Lemma lem7069974 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) : (term184 A c f x t) = (term185 A c x t f).
Proof. exact (MK_COMB (@lem7069972 A c f x t) (@lem7069973 A c x t f)). Qed.
Lemma lem7069975 {A : Type'} (c : real) (x : A) (f : A -> real) : (term186 A c f x) = (term187 A c x f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7069974 A c x t f)). Qed.
Lemma lem7069976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069977 {A : Type'} (c : real) (x : A) (f : A -> real) : (term188 A c f x) = (term189 A c x f).
Proof. exact (MK_COMB (@lem7069976 A) (@lem7069975 A c x f)). Qed.
Lemma lem7069978 {A : Type'} (c : real) (f : A -> real) : (term190 A c f) = (term191 A c f).
Proof. exact (fun_ext (fun x : A => @lem7069977 A c x f)). Qed.
Lemma lem7069979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7069980 {A : Type'} (c : real) (f : A -> real) : (term192 A c f) = (term193 A c f).
Proof. exact (MK_COMB (@lem7069979 A) (@lem7069978 A c f)). Qed.
Lemma lem7069981 {A : Type'} (c : real) (f : A -> real) : (term194 A c f) = (term195 A c f).
Proof. exact (MK_COMB (@lem7069965 A c f) (@lem7069980 A c f)). Qed.
Lemma lem7069982 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7069983 {A : Type'} (c : real) (f : A -> real) : (term196 A c f) = (term197 A c f).
Proof. exact (MK_COMB (@lem7069982) (@lem7069981 A c f)). Qed.
Lemma lem7069984 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term173 A c f t) = ((term46 A t c f) = (term49 A c t f)).
Proof. exact (eq_refl (term173 A c f t)). Qed.
Lemma lem7069985 {A : Type'} (t : A -> Prop) : (term159 A t) = (term159 A t).
Proof. exact (eq_refl (term159 A t)). Qed.
Lemma lem7069986 {A : Type'} (c : real) (t : A -> Prop) (f : A -> real) : (term198 A c f t) = (term161 A c t f).
Proof. exact (MK_COMB (@lem7069985 A t) (@lem7069984 A c t f)). Qed.
Lemma lem7069987 {A : Type'} (c : real) (f : A -> real) : (term199 A c f) = (term163 A c f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7069986 A c t f)). Qed.
Lemma lem7069988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069989 {A : Type'} (c : real) (f : A -> real) : (term200 A c f) = (term165 A c f).
Proof. exact (MK_COMB (@lem7069988 A) (@lem7069987 A c f)). Qed.
Lemma lem7069990 {A : Type'} (c : real) (f : A -> real) : (term166 A c f) = (term201 A c f).
Proof. exact (MK_COMB (@lem7069983 A c f) (@lem7069989 A c f)). Qed.
Lemma lem7069991 {A : Type'} (c : real) (f : A -> real) : term201 A c f.
Proof. exact (EQ_MP (@lem7069990 A c f) (@lem7069962 A c f)). Qed.
Lemma lem7069997 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term9.
Proof. exact (EQ_MP (@lem7069434 _131483 f) (@lem7069433 _131483 f)). Qed.
Lemma lem7069998 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term9.
Proof. exact (@lem7069997 A f). Qed.
Lemma lem7069999 {A : Type'} (c : real) (f : A -> real) : (term169 A c f) = term9.
Proof. exact (@lem7069998 A (term44 A c f)). Qed.
Lemma lem7070000 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070001 {A : Type'} (c : real) (f : A -> real) : (term202 A c f) = term48.
Proof. exact (MK_COMB (@lem7070000) (@lem7069999 A c f)). Qed.
Lemma lem7070003 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term9.
Proof. exact (EQ_MP (@lem7069434 _131483 f) (@lem7069433 _131483 f)). Qed.
Lemma lem7070004 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term9.
Proof. exact (@lem7070003 A f). Qed.
Lemma lem7070005 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7070006 {A : Type'} (f : A -> real) (c : real) : (term170 A c f) = (term8 c).
Proof. exact (MK_COMB (@lem7070005 c) (@lem7070004 A f)). Qed.
Lemma lem7070008 (x : real) : (term8 x) = term9.
Proof. exact (EQ_MP (@lem7069413 x) (@lem7069412 x)). Qed.
Lemma lem7070009 (c : real) : (term8 c) = term9.
Proof. exact (@lem7070008 c). Qed.
Lemma lem7070010 {A : Type'} (c : real) (f : A -> real) : (term170 A c f) = term9.
Proof. exact (TRANS (@lem7070006 A f c) (@lem7070009 c)). Qed.
Lemma lem7070011 {A : Type'} (c : real) (f : A -> real) : ((term169 A c f) = (term170 A c f)) = (term9 = term9).
Proof. exact (MK_COMB (@lem7070001 A c f) (@lem7070010 A c f)). Qed.
Lemma lem7070013 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7070014 (x : real) : (x = x) = True.
Proof. exact (@lem7070013 real x). Qed.
Lemma lem7070015 : (term9 = term9) = True.
Proof. exact (@lem7070014 term9). Qed.
Lemma lem7070016 {A : Type'} (c : real) (f : A -> real) : ((term169 A c f) = (term170 A c f)) = True.
Proof. exact (TRANS (@lem7070011 A c f) (@lem7070015)). Qed.
Lemma lem7070017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7070018 {A : Type'} (c : real) (f : A -> real) : (term172 A c f) = (and True).
Proof. exact (MK_COMB (@lem7070017) (@lem7070016 A c f)). Qed.
Lemma lem7070030 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term203 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7070031 (p : Prop) (q : Prop) (p' : Prop) : term204 p q p'.
Proof. exact (fun q' : Prop => @lem7070030 p q p' q'). Qed.
Lemma lem7070032 (p : Prop) (q : Prop) : term205 p q.
Proof. exact (fun p' : Prop => @lem7070031 p q p'). Qed.
Lemma lem7070033 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) : term206 A c x t f.
Proof. exact (@lem7070032 (term178 A c f x t) ((term182 A x t c f) = (term183 A c x t f))). Qed.
Lemma lem7070034 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) : term207 A c x t f p'.
Proof. exact (@lem7070033 A c x t f p'). Qed.
Lemma lem7070035 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) : (term207 A c x t f p') = (term208 A c x t f p').
Proof. exact (eq_refl (term207 A c x t f p')). Qed.
Lemma lem7070036 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) : term208 A c x t f p'.
Proof. exact (EQ_MP (@lem7070035 A c x t f p') (@lem7070034 A c x t f p')). Qed.
Lemma lem7070037 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term209 A c x t f p' q'.
Proof. exact (@lem7070036 A c x t f p' q'). Qed.
Lemma lem7070038 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term209 A c x t f p' q') = (term210 A c x t f p' q').
Proof. exact (eq_refl (term209 A c x t f p' q')). Qed.
Lemma lem7070039 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term210 A c x t f p' q'.
Proof. exact (EQ_MP (@lem7070038 A c x t f p' q') (@lem7070037 A c x t f p' q')). Qed.
Lemma lem7070046 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : (term178 A c f x t) = (term178 A c f x t).
Proof. exact (eq_refl (term178 A c f x t)). Qed.
Lemma lem7070047 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (q' : Prop) : term211 A c f x t q'.
Proof. exact (@lem7070039 A c x t f (term178 A c f x t) q'). Qed.
Lemma lem7070048 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (q' : Prop) : term212 A c f x t q'.
Proof. exact (@lem7070047 A c f x t q' (@lem7070046 A c f x t)). Qed.
Lemma lem7070049 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term178 A c f x t.
Proof. exact (h1). Qed.
Lemma lem7070050 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term176 A x t.
Proof. exact (proj2 (@lem7070049 A c f x t h1)). Qed.
Lemma lem7070051 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : @FINITE A t.
Proof. exact (proj2 (@lem7070050 A c f x t h1)). Qed.
Lemma lem7070052 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem7070054 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term213 A x t.
Proof. exact (proj1 (@lem7070050 A c f x t h1)). Qed.
Lemma lem7070055 {A : Type'} (x : A) (t : A -> Prop) : term214 A x t.
Proof. exact (@lem82 (@IN A x t)). Qed.
Lemma lem7070061 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term16 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7069426 _131524 x f s h0). Qed.
Lemma lem7070062 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term16 A x s f.
Proof. exact (@lem7070061 A x s f). Qed.
Lemma lem7070063 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) : term215 A x t c f.
Proof. exact (@lem7070062 A x t (term44 A c f)). Qed.
Lemma lem7070065 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem7070052 A t) (@lem7070051 A c f x t h1)). Qed.
Lemma lem7070066 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : True = (@FINITE A t).
Proof. exact (SYM (@lem7070065 A c f x t h1)). Qed.
Lemma lem7070067 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : @FINITE A t.
Proof. exact (EQ_MP (@lem7070066 A c f x t h1) (@lem0)). Qed.
Lemma lem7070068 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term182 A x t c f) = (term216 A x t c f).
Proof. exact (@lem7070063 A x t c f (@lem7070067 A c f x t h1)). Qed.
Lemma lem7070070 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term217 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7070071 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term218 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7070070 _2963 g t e g' t' e'). Qed.
Lemma lem7070072 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term219 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7070071 _2963 g t e g' t'). Qed.
Lemma lem7070073 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term220 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7070072 _2963 g t e g'). Qed.
Lemma lem7070074 (g : Prop) (t : real) (e : real) : term221 g t e.
Proof. exact (@lem7070073 real g t e). Qed.
Lemma lem7070075 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) : term222 A x t c f.
Proof. exact (@lem7070074 (@IN A x t) (term46 A t c f) (term223 A x t c f)). Qed.
Lemma lem7070076 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) : term224 A x t c f g'.
Proof. exact (@lem7070075 A x t c f g'). Qed.
Lemma lem7070077 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) : (term224 A x t c f g') = (term225 A x t c f g').
Proof. exact (eq_refl (term224 A x t c f g')). Qed.
Lemma lem7070078 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) : term225 A x t c f g'.
Proof. exact (EQ_MP (@lem7070077 A x t c f g') (@lem7070076 A x t c f g')). Qed.
Lemma lem7070079 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) : term226 A x t c f g' t'.
Proof. exact (@lem7070078 A x t c f g' t'). Qed.
Lemma lem7070080 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) : (term226 A x t c f g' t') = (term227 A x t c f g' t').
Proof. exact (eq_refl (term226 A x t c f g' t')). Qed.
Lemma lem7070081 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) : term227 A x t c f g' t'.
Proof. exact (EQ_MP (@lem7070080 A x t c f g' t') (@lem7070079 A x t c f g' t')). Qed.
Lemma lem7070082 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term228 A x t c f g' t' e'.
Proof. exact (@lem7070081 A x t c f g' t' e'). Qed.
Lemma lem7070083 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : (term228 A x t c f g' t' e') = (term229 A x t c f g' t' e').
Proof. exact (eq_refl (term228 A x t c f g' t' e')). Qed.
Lemma lem7070084 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term229 A x t c f g' t' e'.
Proof. exact (EQ_MP (@lem7070083 A x t c f g' t' e') (@lem7070082 A x t c f g' t' e')). Qed.
Lemma lem7070086 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (@IN A x t) = False.
Proof. exact (@lem7070055 A x t (@lem7070054 A c f x t h1)). Qed.
Lemma lem7070087 {A : Type'} (x : A) (t : A -> Prop) (c : real) (f : A -> real) (t' : real) (e' : real) : term230 A x t c f t' e'.
Proof. exact (@lem7070084 A x t c f False t' e'). Qed.
Lemma lem7070088 {A : Type'} (t' : real) (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term231 A x t c f t' e'.
Proof. exact (@lem7070087 A x t c f t' e' (@lem7070086 A c f x t h1)). Qed.
Lemma lem7070093 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term46 A t c f) = (term49 A c t f).
Proof. exact (proj1 (@lem7070049 A c f x t h1)). Qed.
Lemma lem7070094 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term46 A t c f) = (term49 A c t f).
Proof. exact (@lem7070093 A c f x t h1). Qed.
Lemma lem7070095 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term232 A c t f.
Proof. exact (fun h0 : False => @lem7070094 A c f x t h1). Qed.
Lemma lem7070096 {A : Type'} (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term233 A x c t f e'.
Proof. exact (@lem7070088 A (term49 A c t f) e' c f x t h1). Qed.
Lemma lem7070097 {A : Type'} (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term234 A x c t f e'.
Proof. exact (@lem7070096 A e' c f x t h1 (@lem7070095 A c f x t h1)). Qed.
Lemma lem7070104 {A B : Type'} (f : A -> B) (y : A) : (term79 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7070105 {A : Type'} (f : A -> real) (y : A) : (term80 A f y) = (f y).
Proof. exact (@lem7070104 A real f y). Qed.
Lemma lem7070106 {A : Type'} (c : real) (f : A -> real) (x : A) : (term81 A c f x) = (term82 A c f x).
Proof. exact (@lem7070105 A (term44 A c f) x). Qed.
Lemma lem7070107 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (eq_refl (term82 A c f x)). Qed.
Lemma lem7070108 {A : Type'} (c : real) (f : A -> real) : (term83 A c f) = (term44 A c f).
Proof. exact (fun_ext (fun x : A => @lem7070107 A c f x)). Qed.
Lemma lem7070109 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7070110 {A : Type'} (c : real) (f : A -> real) (x : A) : (term81 A c f x) = (term82 A c f x).
Proof. exact (MK_COMB (@lem7070108 A c f) (@lem7070109 A x)). Qed.
Lemma lem7070111 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070112 {A : Type'} (c : real) (f : A -> real) (x : A) : (term84 A c f x) = (term85 A c f x).
Proof. exact (MK_COMB (@lem7070111) (@lem7070110 A c f x)). Qed.
Lemma lem7070113 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (eq_refl (term82 A c f x)). Qed.
Lemma lem7070114 {A : Type'} (c : real) (f : A -> real) (x : A) : ((term81 A c f x) = (term82 A c f x)) = ((term82 A c f x) = (term42 A c f x)).
Proof. exact (MK_COMB (@lem7070112 A c f x) (@lem7070113 A c f x)). Qed.
Lemma lem7070115 {A : Type'} (c : real) (f : A -> real) (x : A) : (term82 A c f x) = (term42 A c f x).
Proof. exact (EQ_MP (@lem7070114 A c f x) (@lem7070106 A c f x)). Qed.
Lemma lem7070116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7070117 {A : Type'} (c : real) (f : A -> real) (x : A) : (term235 A c f x) = (term236 A c f x).
Proof. exact (MK_COMB (@lem7070116) (@lem7070115 A c f x)). Qed.
Lemma lem7070119 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term46 A t c f) = (term49 A c t f).
Proof. exact (proj1 (@lem7070049 A c f x t h1)). Qed.
Lemma lem7070120 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term46 A t c f) = (term49 A c t f).
Proof. exact (@lem7070119 A c f x t h1). Qed.
Lemma lem7070121 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term223 A x t c f) = (term237 A x c t f).
Proof. exact (MK_COMB (@lem7070117 A c f x) (@lem7070120 A c f x t h1)). Qed.
Lemma lem7070122 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term238 A x c t f.
Proof. exact (fun h0 : ~ False => @lem7070121 A c f x t h1). Qed.
Lemma lem7070123 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term239 A x c t f.
Proof. exact (@lem7070097 A (term237 A x c t f) c f x t h1). Qed.
Lemma lem7070124 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term216 A x t c f) = (term240 A x c t f).
Proof. exact (@lem7070123 A c f x t h1 (@lem7070122 A c f x t h1)). Qed.
Lemma lem7070126 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7070127 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7070126 real t1 t2). Qed.
Lemma lem7070128 {A : Type'} (x : A) (c : real) (t : A -> Prop) (f : A -> real) : (term240 A x c t f) = (term237 A x c t f).
Proof. exact (@lem7070127 (term49 A c t f) (term237 A x c t f)). Qed.
Lemma lem7070129 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term216 A x t c f) = (term237 A x c t f).
Proof. exact (TRANS (@lem7070124 A c f x t h1) (@lem7070128 A x c t f)). Qed.
Lemma lem7070130 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term182 A x t c f) = (term237 A x c t f).
Proof. exact (TRANS (@lem7070068 A c f x t h1) (@lem7070129 A c f x t h1)). Qed.
Lemma lem7070131 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070132 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term241 A x t c f) = (term242 A x c t f).
Proof. exact (MK_COMB (@lem7070131) (@lem7070130 A c f x t h1)). Qed.
Lemma lem7070134 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term16 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7069426 _131524 x f s h0). Qed.
Lemma lem7070135 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term16 A x s f.
Proof. exact (@lem7070134 A x s f). Qed.
Lemma lem7070136 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) : term16 A x t f.
Proof. exact (@lem7070135 A x t f). Qed.
Lemma lem7070138 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem7070052 A t) (@lem7070051 A c f x t h1)). Qed.
Lemma lem7070139 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : True = (@FINITE A t).
Proof. exact (SYM (@lem7070138 A c f x t h1)). Qed.
Lemma lem7070140 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : @FINITE A t.
Proof. exact (EQ_MP (@lem7070139 A c f x t h1) (@lem0)). Qed.
Lemma lem7070141 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term17 A x t f) = (term18 A x t f).
Proof. exact (@lem7070136 A x t f (@lem7070140 A c f x t h1)). Qed.
Lemma lem7070143 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term217 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7070144 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term218 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7070143 _2963 g t e g' t' e'). Qed.
Lemma lem7070145 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term219 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7070144 _2963 g t e g' t'). Qed.
Lemma lem7070146 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term220 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7070145 _2963 g t e g'). Qed.
Lemma lem7070147 (g : Prop) (t : real) (e : real) : term221 g t e.
Proof. exact (@lem7070146 real g t e). Qed.
Lemma lem7070148 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) : term243 A x t f.
Proof. exact (@lem7070147 (@IN A x t) (@sum A t f) (term244 A x t f)). Qed.
Lemma lem7070149 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) : term245 A x t f g'.
Proof. exact (@lem7070148 A x t f g'). Qed.
Lemma lem7070150 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) : (term245 A x t f g') = (term246 A x t f g').
Proof. exact (eq_refl (term245 A x t f g')). Qed.
Lemma lem7070151 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) : term246 A x t f g'.
Proof. exact (EQ_MP (@lem7070150 A x t f g') (@lem7070149 A x t f g')). Qed.
Lemma lem7070152 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : term247 A x t f g' t'.
Proof. exact (@lem7070151 A x t f g' t'). Qed.
Lemma lem7070153 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : (term247 A x t f g' t') = (term248 A x t f g' t').
Proof. exact (eq_refl (term247 A x t f g' t')). Qed.
Lemma lem7070154 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) : term248 A x t f g' t'.
Proof. exact (EQ_MP (@lem7070153 A x t f g' t') (@lem7070152 A x t f g' t')). Qed.
Lemma lem7070155 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term249 A x t f g' t' e'.
Proof. exact (@lem7070154 A x t f g' t' e'). Qed.
Lemma lem7070156 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : (term249 A x t f g' t' e') = (term250 A x t f g' t' e').
Proof. exact (eq_refl (term249 A x t f g' t' e')). Qed.
Lemma lem7070157 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term250 A x t f g' t' e'.
Proof. exact (EQ_MP (@lem7070156 A x t f g' t' e') (@lem7070155 A x t f g' t' e')). Qed.
Lemma lem7070159 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (@IN A x t) = False.
Proof. exact (@lem7070055 A x t (@lem7070054 A c f x t h1)). Qed.
Lemma lem7070160 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) (t' : real) (e' : real) : term251 A x t f t' e'.
Proof. exact (@lem7070157 A x t f False t' e'). Qed.
Lemma lem7070161 {A : Type'} (t' : real) (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term252 A x t f t' e'.
Proof. exact (@lem7070160 A x t f t' e' (@lem7070159 A c f x t h1)). Qed.
Lemma lem7070165 {A : Type'} (t : A -> Prop) (f : A -> real) : (@sum A t f) = (@sum A t f).
Proof. exact (eq_refl (@sum A t f)). Qed.
Lemma lem7070166 {A : Type'} (t : A -> Prop) (f : A -> real) : term253 A t f.
Proof. exact (fun h0 : False => @lem7070165 A t f). Qed.
Lemma lem7070167 {A : Type'} (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term254 A x t f e'.
Proof. exact (@lem7070161 A (@sum A t f) e' c f x t h1). Qed.
Lemma lem7070168 {A : Type'} (e' : real) (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term255 A x t f e'.
Proof. exact (@lem7070167 A e' c f x t h1 (@lem7070166 A t f)). Qed.
Lemma lem7070174 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) : (term244 A x t f) = (term244 A x t f).
Proof. exact (eq_refl (term244 A x t f)). Qed.
Lemma lem7070175 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) : term256 A x t f.
Proof. exact (fun h0 : ~ False => @lem7070174 A x t f). Qed.
Lemma lem7070176 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : term257 A x t f.
Proof. exact (@lem7070168 A (term244 A x t f) c f x t h1). Qed.
Lemma lem7070177 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term18 A x t f) = (term258 A x t f).
Proof. exact (@lem7070176 A c f x t h1 (@lem7070175 A x t f)). Qed.
Lemma lem7070179 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7070180 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7070179 real t1 t2). Qed.
Lemma lem7070181 {A : Type'} (x : A) (t : A -> Prop) (f : A -> real) : (term258 A x t f) = (term244 A x t f).
Proof. exact (@lem7070180 (@sum A t f) (term244 A x t f)). Qed.
Lemma lem7070182 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term18 A x t f) = (term244 A x t f).
Proof. exact (TRANS (@lem7070177 A c f x t h1) (@lem7070181 A x t f)). Qed.
Lemma lem7070183 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term17 A x t f) = (term244 A x t f).
Proof. exact (TRANS (@lem7070141 A c f x t h1) (@lem7070182 A c f x t h1)). Qed.
Lemma lem7070184 (c : real) : (real_mul c) = (real_mul c).
Proof. exact (eq_refl (real_mul c)). Qed.
Lemma lem7070185 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term183 A c x t f) = (term259 A c x t f).
Proof. exact (MK_COMB (@lem7070184 c) (@lem7070183 A c f x t h1)). Qed.
Lemma lem7070187 (y : real) (x : real) (z : real) : (term5 x y z) = (term6 y x z).
Proof. exact (EQ_MP (@lem7069407 y x z) (@lem7069406 y x z)). Qed.
Lemma lem7070188 {A : Type'} (x : A) (c : real) (t : A -> Prop) (f : A -> real) : (term259 A c x t f) = (term237 A x c t f).
Proof. exact (@lem7070187 (f x) c (@sum A t f)). Qed.
Lemma lem7070189 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : (term183 A c x t f) = (term237 A x c t f).
Proof. exact (TRANS (@lem7070185 A c f x t h1) (@lem7070188 A x c t f)). Qed.
Lemma lem7070190 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : ((term182 A x t c f) = (term183 A c x t f)) = ((term237 A x c t f) = (term237 A x c t f)).
Proof. exact (MK_COMB (@lem7070132 A c f x t h1) (@lem7070189 A c f x t h1)). Qed.
Lemma lem7070192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7070193 (x : real) : (x = x) = True.
Proof. exact (@lem7070192 real x). Qed.
Lemma lem7070194 {A : Type'} (x : A) (c : real) (t : A -> Prop) (f : A -> real) : ((term237 A x c t f) = (term237 A x c t f)) = True.
Proof. exact (@lem7070193 (term237 A x c t f)). Qed.
Lemma lem7070195 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) (h1 : term178 A c f x t) : ((term182 A x t c f) = (term183 A c x t f)) = True.
Proof. exact (TRANS (@lem7070190 A c f x t h1) (@lem7070194 A x c t f)). Qed.
Lemma lem7070196 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) : term260 A c x t f.
Proof. exact (fun h0 : term178 A c f x t => @lem7070195 A c f x t h0). Qed.
Lemma lem7070197 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : term261 A c f x t.
Proof. exact (@lem7070048 A c f x t True). Qed.
Lemma lem7070198 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : (term185 A c x t f) = (term262 A c f x t).
Proof. exact (@lem7070197 A c f x t (@lem7070196 A c x t f)). Qed.
Lemma lem7070200 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7070201 {A : Type'} (c : real) (f : A -> real) (x : A) (t : A -> Prop) : (term262 A c f x t) = True.
Proof. exact (@lem7070200 (term178 A c f x t)). Qed.
Lemma lem7070202 {A : Type'} (c : real) (x : A) (t : A -> Prop) (f : A -> real) : (term185 A c x t f) = True.
Proof. exact (TRANS (@lem7070198 A c f x t) (@lem7070201 A c f x t)). Qed.
Lemma lem7070203 {A : Type'} (c : real) (x : A) (f : A -> real) : (term187 A c x f) = (term263 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7070202 A c x t f)). Qed.
Lemma lem7070204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7070205 {A : Type'} (c : real) (x : A) (f : A -> real) : (term189 A c x f) = (term264 A).
Proof. exact (MK_COMB (@lem7070204 A) (@lem7070203 A c x f)). Qed.
Lemma lem7070207 {A : Type'} (t : Prop) : (term265 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070208 {A : Type'} (t : Prop) : (term266 A t) = t.
Proof. exact (@lem7070207 (A -> Prop) t). Qed.
Lemma lem7070209 {A : Type'} : (term264 A) = True.
Proof. exact (@lem7070208 A True). Qed.
Lemma lem7070210 {A : Type'} (c : real) (x : A) (f : A -> real) : (term189 A c x f) = True.
Proof. exact (TRANS (@lem7070205 A c x f) (@lem7070209 A)). Qed.
Lemma lem7070211 {A : Type'} (c : real) (f : A -> real) : (term191 A c f) = (term267 A).
Proof. exact (fun_ext (fun x : A => @lem7070210 A c x f)). Qed.
Lemma lem7070212 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7070213 {A : Type'} (c : real) (f : A -> real) : (term193 A c f) = (term268 A).
Proof. exact (MK_COMB (@lem7070212 A) (@lem7070211 A c f)). Qed.
Lemma lem7070215 {A : Type'} (t : Prop) : (term265 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070216 {A : Type'} (t : Prop) : (term265 A t) = t.
Proof. exact (@lem7070215 A t). Qed.
Lemma lem7070217 {A : Type'} : (term268 A) = True.
Proof. exact (@lem7070216 A True). Qed.
Lemma lem7070218 {A : Type'} (c : real) (f : A -> real) : (term193 A c f) = True.
Proof. exact (TRANS (@lem7070213 A c f) (@lem7070217 A)). Qed.
Lemma lem7070219 {A : Type'} (c : real) (f : A -> real) : (term195 A c f) = (True /\ True).
Proof. exact (MK_COMB (@lem7070018 A c f) (@lem7070218 A c f)). Qed.
Lemma lem7070221 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7070222 : (True /\ True) = True.
Proof. exact (@lem7070221 True). Qed.
Lemma lem7070223 {A : Type'} (c : real) (f : A -> real) : (term195 A c f) = True.
Proof. exact (TRANS (@lem7070219 A c f) (@lem7070222)). Qed.
Lemma lem7070224 {A : Type'} (c : real) (f : A -> real) : True = (term195 A c f).
Proof. exact (SYM (@lem7070223 A c f)). Qed.
Lemma lem7070225 {A : Type'} (c : real) (f : A -> real) : term195 A c f.
Proof. exact (EQ_MP (@lem7070224 A c f) (@lem0)). Qed.
Lemma lem7070226 {A : Type'} (c : real) (f : A -> real) : term165 A c f.
Proof. exact (@lem7069991 A c f (@lem7070225 A c f)). Qed.
Lemma lem7070227 {A : Type'} (c : real) (f : A -> real) : term164 A c f.
Proof. exact (EQ_MP (@lem7069958 A c f) (@lem7070226 A c f)). Qed.
Lemma lem7070228 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) : term269 A c f s.
Proof. exact (@lem7070227 A c f (@support A real real_add f s)). Qed.
Lemma lem7070229 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term269 A c f s) = (term270 A c s f).
Proof. exact (eq_refl (term269 A c f s)). Qed.
Lemma lem7070230 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : term270 A c s f.
Proof. exact (EQ_MP (@lem7070229 A c s f) (@lem7070228 A c f s)). Qed.
Lemma lem7070231 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term124 A s c f) = (term155 A c s f).
Proof. exact (@lem7070230 A c s f (@lem7069846 A f s h1)). Qed.
Lemma lem7070232 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term124 A s c f) = (term142 A c s f).
Proof. exact (EQ_MP (@lem7069890 A c s f) (@lem7070231 A c f s h1)). Qed.
Lemma lem7070233 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : (@neutral real real_add) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7069877 A c f s h1) (@lem7069917 A c s f)). Qed.
Lemma lem7070234 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : (term145 A f s) = ((@neutral real real_add) = (term58 A c s f)).
Proof. exact (prop_ext (fun h2 : term145 A f s => @lem7070233 A c f s h1) (fun h2 : (@neutral real real_add) = (term58 A c s f) => @lem7069862 A f s h1)). Qed.
Lemma lem7070235 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term145 A f s) : (@neutral real real_add) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7070234 A c f s h1) (@lem7069862 A f s h1)). Qed.
Lemma lem7070236 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : term129 A c s f.
Proof. exact (fun h0 : term145 A f s => @lem7070235 A c f s h0). Qed.
Lemma lem7070237 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term124 A s c f) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7069861 A c f s h1) (@lem7070232 A c f s h1)). Qed.
Lemma lem7070238 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term125 A f s) = ((term124 A s c f) = (term58 A c s f)).
Proof. exact (prop_ext (fun h2 : term125 A f s => @lem7070237 A c f s h1) (fun h2 : (term124 A s c f) = (term58 A c s f) => @lem7069846 A f s h1)). Qed.
Lemma lem7070239 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : term125 A f s) : (term124 A s c f) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7070238 A c f s h1) (@lem7069846 A f s h1)). Qed.
Lemma lem7070240 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : term133 A c s f.
Proof. exact (fun h0 : term125 A f s => @lem7070239 A c f s h0). Qed.
Lemma lem7070241 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : term136 A c s f.
Proof. exact (conj (@lem7070240 A c s f) (@lem7070236 A c s f)). Qed.
Lemma lem7070242 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term63 A s c f) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7069845 A c s f) (@lem7070241 A c s f)). Qed.
Lemma lem7070243 {A : Type'} (c : real) (f : A -> real) (s : A -> Prop) (h1 : (term59 A c f s) = (@support A real real_add f s)) : (term55 A s c f) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7069596 A c f s h1) (@lem7070242 A c s f)). Qed.
Lemma lem7070244 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : ((term59 A c f s) = (@support A real real_add f s)) = ((term55 A s c f) = (term58 A c s f)).
Proof. exact (prop_ext (fun h2 : (term59 A c f s) = (@support A real real_add f s) => @lem7070243 A c f s h2) (fun h2 : (term55 A s c f) = (term58 A c s f) => @lem7069827 A f s c h1)). Qed.
Lemma lem7070245 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term55 A s c f) = (term58 A c s f).
Proof. exact (EQ_MP (@lem7070244 A s f c h1) (@lem7069827 A f s c h1)). Qed.
Lemma lem7070246 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term51 A s c f) = (term53 A c s f).
Proof. exact (EQ_MP (@lem7069582 A c s f) (@lem7070245 A s f c h1)). Qed.
Lemma lem7070248 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) (h1 : term36 c) : (term46 A s c f) = (term49 A c s f).
Proof. exact (EQ_MP (@lem7069566 A c s f) (@lem7070246 A s f c h1)). Qed.
Lemma lem7070249 {A : Type'} (c : real) (s : A -> Prop) (f : A -> real) : (term46 A s c f) = (term49 A c s f).
Proof. exact (or_elim (@lem7069472 c) (fun h0 : c = term9 => @lem7069519 A s f c h0) (fun h0 : term36 c => @lem7070248 A s f c h0)). Qed.
Lemma lem7070254 {A : Type'} (c : real) (f : A -> real) : term271 A c f.
Proof. exact (fun s : A -> Prop => @lem7070249 A c s f). Qed.
Lemma lem7070259 {A : Type'} (f : A -> real) : term272 A f.
Proof. exact (fun c : real => @lem7070254 A c f). Qed.
Lemma lem7070264 {A : Type'} : term273 A.
Proof. exact (fun f : A -> real => @lem7070259 A f). Qed.
