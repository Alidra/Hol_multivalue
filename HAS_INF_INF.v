Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_INF_INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INF_spec.
Require Import INF_UNIQUE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import has_inf_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5293353 (s : real -> Prop) : term0 s.
Proof. exact (@lem5214027 s). Qed.
Lemma lem5293354 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5293355 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5293354 s) (@lem5293353 s)). Qed.
Lemma lem5293356 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem5293357 (s : real -> Prop) (h1 : term2) : term3 s.
Proof. exact (@lem5293356 h1 s). Qed.
Lemma lem5293358 (s : real -> Prop) : (term3 s) = (term4 s).
Proof. exact (eq_refl (term3 s)). Qed.
Lemma lem5293359 (s : real -> Prop) (h1 : term2) : term4 s.
Proof. exact (EQ_MP (@lem5293358 s) (@lem5293357 s h1)). Qed.
Lemma lem5293360 (s : real -> Prop) (b : real) (h1 : term2) : term5 s b.
Proof. exact (@lem5293359 s h1 b). Qed.
Lemma lem5293361 (s : real -> Prop) (b : real) : (term5 s b) = (term6 s b).
Proof. exact (eq_refl (term5 s b)). Qed.
Lemma lem5293362 (s : real -> Prop) (b : real) (h1 : term2) : term6 s b.
Proof. exact (EQ_MP (@lem5293361 s b) (@lem5293360 s b h1)). Qed.
Lemma lem5293363 (s : real -> Prop) (b : real) (h1 : term7 s b) : term7 s b.
Proof. exact (h1). Qed.
Lemma lem5293364 (s : real -> Prop) (b : real) (h1 : term2) (h2 : term7 s b) : (inf s) = b.
Proof. exact (@lem5293362 s b h1 (@lem5293363 s b h2)). Qed.
Lemma lem5293365 (s : real -> Prop) (b : real) (h1 : term7 s b) : term8 s b.
Proof. exact (fun h0 : term2 => @lem5293364 s b h0 h1). Qed.
Lemma lem5293366 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem5293367 (s : real -> Prop) (b : real) (h1 : term2) (h2 : term7 s b) : (inf s) = b.
Proof. exact (@lem5293365 s b h2 (@lem5293366 h1)). Qed.
Lemma lem5293368 (s : real -> Prop) (b : real) (h1 : term2) : term6 s b.
Proof. exact (fun h0 : term7 s b => @lem5293367 s b h1 h0). Qed.
Lemma lem5293369 (s : real -> Prop) (h1 : term2) : term4 s.
Proof. exact (fun b : real => @lem5293368 s b h1). Qed.
Lemma lem5293370 (h1 : term2) : term2.
Proof. exact (fun s : real -> Prop => @lem5293369 s h1). Qed.
Lemma lem5293371 : term9.
Proof. exact (fun h0 : term2 => @lem5293370 h0). Qed.
Lemma lem5293372 : term2.
Proof. exact (@lem5293371 (@lem5275334)). Qed.
Lemma lem5293373 (s : real -> Prop) : term3 s.
Proof. exact (@lem5293372 s). Qed.
Lemma lem5293374 (s : real -> Prop) : (term3 s) = (term4 s).
Proof. exact (eq_refl (term3 s)). Qed.
Lemma lem5293375 (s : real -> Prop) : term4 s.
Proof. exact (EQ_MP (@lem5293374 s) (@lem5293373 s)). Qed.
Lemma lem5293376 (s : real -> Prop) (b : real) : term5 s b.
Proof. exact (@lem5293375 s b). Qed.
Lemma lem5293377 (s : real -> Prop) (b : real) : (term5 s b) = (term6 s b).
Proof. exact (eq_refl (term5 s b)). Qed.
Lemma lem5293389 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem5293390 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem5293392 {A : Type'} (x : A) : term13 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5293393 {A : Type'} (x : A) : (term13 A x) = (term14 A x).
Proof. exact (eq_refl (term13 A x)). Qed.
Lemma lem5293394 {A : Type'} (x : A) : term14 A x.
Proof. exact (EQ_MP (@lem5293393 A x) (@lem5293392 A x)). Qed.
Lemma lem5293395 {A : Type'} (x : A) : term15 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5293397 (s : real -> Prop) : term16 s.
Proof. exact (@lem5289985 s). Qed.
Lemma lem5293398 (s : real -> Prop) : (term16 s) = (term17 s).
Proof. exact (eq_refl (term16 s)). Qed.
Lemma lem5293399 (s : real -> Prop) : term17 s.
Proof. exact (EQ_MP (@lem5293398 s) (@lem5293397 s)). Qed.
Lemma lem5293400 (s : real -> Prop) (b : real) : term18 s b.
Proof. exact (@lem5293399 s b). Qed.
Lemma lem5293401 (s : real -> Prop) (b : real) : (term18 s b) = ((has_inf s b) = (term7 s b)).
Proof. exact (eq_refl (term18 s b)). Qed.
Lemma lem5293406 (s : real -> Prop) (b : real) : (has_inf s b) = (term7 s b).
Proof. exact (EQ_MP (@lem5293401 s b) (@lem5293400 s b)). Qed.
Lemma lem5293407 (s : real -> Prop) (l : real) : (has_inf s l) = (term7 s l).
Proof. exact (@lem5293406 s l). Qed.
Lemma lem5293420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293421 (s : real -> Prop) (l : real) : (term19 s l) = (term20 s l).
Proof. exact (MK_COMB (@lem5293420) (@lem5293407 s l)). Qed.
Lemma lem5293440 (s : real -> Prop) (l : real) : (term21 s l) = (term21 s l).
Proof. exact (eq_refl (term21 s l)). Qed.
Lemma lem5293441 (s : real -> Prop) (l : real) : ((has_inf s l) = (term21 s l)) = ((term7 s l) = (term21 s l)).
Proof. exact (MK_COMB (@lem5293421 s l) (@lem5293440 s l)). Qed.
Lemma lem5293444 (s : real -> Prop) (l : real) : ((term7 s l) = (term21 s l)) = ((has_inf s l) = (term21 s l)).
Proof. exact (SYM (@lem5293441 s l)). Qed.
Lemma lem5293445 (s : real -> Prop) (l : real) (h1 : term7 s l) : term7 s l.
Proof. exact (h1). Qed.
Lemma lem5293446 (s : real -> Prop) (l : real) (h1 : term21 s l) : term21 s l.
Proof. exact (h1). Qed.
Lemma lem5293447 (s : real -> Prop) (l : real) (h1 : term22 s l) : term22 s l.
Proof. exact (h1). Qed.
Lemma lem5293448 (s : real -> Prop) (h1 : term23 s) : term23 s.
Proof. exact (h1). Qed.
Lemma lem5293449 (s : real -> Prop) (l : real) (h1 : (inf s) = l) : (inf s) = l.
Proof. exact (h1). Qed.
Lemma lem5293450 (s : real -> Prop) (h1 : term24 s) : term24 s.
Proof. exact (h1). Qed.
Lemma lem5293451 (s : real -> Prop) (b : real) (h1 : term25 s b) : term25 s b.
Proof. exact (h1). Qed.
Lemma lem5293452 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5293467 (l : real) : (term26 l) = (term26 l).
Proof. exact (eq_refl (term26 l)). Qed.
Lemma lem5293468 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term27 l s) = (term28 l).
Proof. exact (MK_COMB (@lem5293467 l) (@lem5293452 s h1)). Qed.
Lemma lem5293469 (l : real) : (term28 l) = (term29 l).
Proof. exact (eq_refl (term28 l)). Qed.
Lemma lem5293470 (l : real) (s : real -> Prop) : (term30 l s) = (term30 l s).
Proof. exact (eq_refl (term30 l s)). Qed.
Lemma lem5293471 (s : real -> Prop) (l : real) : ((term27 l s) = (term28 l)) = ((term27 l s) = (term29 l)).
Proof. exact (MK_COMB (@lem5293470 l s) (@lem5293469 l)). Qed.
Lemma lem5293472 (s : real -> Prop) (l : real) : (term27 l s) = (term7 s l).
Proof. exact (eq_refl (term27 l s)). Qed.
Lemma lem5293473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293474 (s : real -> Prop) (l : real) : (term30 l s) = (term20 s l).
Proof. exact (MK_COMB (@lem5293473) (@lem5293472 s l)). Qed.
Lemma lem5293475 (l : real) : (term29 l) = (term29 l).
Proof. exact (eq_refl (term29 l)). Qed.
Lemma lem5293476 (s : real -> Prop) (l : real) : ((term27 l s) = (term29 l)) = ((term7 s l) = (term29 l)).
Proof. exact (MK_COMB (@lem5293474 s l) (@lem5293475 l)). Qed.
Lemma lem5293477 (s : real -> Prop) (l : real) : ((term27 l s) = (term28 l)) = ((term7 s l) = (term29 l)).
Proof. exact (TRANS (@lem5293471 s l) (@lem5293476 s l)). Qed.
Lemma lem5293478 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term7 s l) = (term29 l).
Proof. exact (EQ_MP (@lem5293477 s l) (@lem5293468 l s h1)). Qed.
Lemma lem5293479 (l : real) (s : real -> Prop) (h1 : term7 s l) (h2 : s = (@EMPTY real)) : term29 l.
Proof. exact (EQ_MP (@lem5293478 l s h2) (@lem5293445 s l h1)). Qed.
Lemma lem5293481 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5293482 (l : real) : (term31 l) = (term32 l).
Proof. exact (@lem5293481 (term29 l)). Qed.
Lemma lem5293484 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem5293390 A P) (@lem5293389 A P)). Qed.
Lemma lem5293485 (P : real -> Prop) : (term33 P) = (term34 P).
Proof. exact (@lem5293484 real P). Qed.
Lemma lem5293486 (l : real) : (term35 l) = (term36 l).
Proof. exact (@lem5293485 (term37 l)). Qed.
Lemma lem5293487 (c : real) (l : real) : (term38 l c) = ((term39 c) = (real_le c l)).
Proof. exact (eq_refl (term38 l c)). Qed.
Lemma lem5293488 (l : real) : (term40 l) = (term37 l).
Proof. exact (fun_ext (fun c : real => @lem5293487 c l)). Qed.
Lemma lem5293489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293490 (l : real) : (term41 l) = (term29 l).
Proof. exact (MK_COMB (@lem5293489) (@lem5293488 l)). Qed.
Lemma lem5293491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293492 (l : real) : (term35 l) = (term32 l).
Proof. exact (MK_COMB (@lem5293491) (@lem5293490 l)). Qed.
Lemma lem5293493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293494 (l : real) : (term42 l) = (term43 l).
Proof. exact (MK_COMB (@lem5293493) (@lem5293492 l)). Qed.
Lemma lem5293495 (c : real) (l : real) : (term38 l c) = ((term39 c) = (real_le c l)).
Proof. exact (eq_refl (term38 l c)). Qed.
Lemma lem5293496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293497 (c : real) (l : real) : (term44 l c) = (term45 c l).
Proof. exact (MK_COMB (@lem5293496) (@lem5293495 c l)). Qed.
Lemma lem5293498 (l : real) : (term46 l) = (term47 l).
Proof. exact (fun_ext (fun c : real => @lem5293497 c l)). Qed.
Lemma lem5293499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5293500 (l : real) : (term36 l) = (term48 l).
Proof. exact (MK_COMB (@lem5293499) (@lem5293498 l)). Qed.
Lemma lem5293501 (l : real) : ((term35 l) = (term36 l)) = ((term32 l) = (term48 l)).
Proof. exact (MK_COMB (@lem5293494 l) (@lem5293500 l)). Qed.
Lemma lem5293502 (l : real) : (term32 l) = (term48 l).
Proof. exact (EQ_MP (@lem5293501 l) (@lem5293486 l)). Qed.
Lemma lem5293507 (l : real) : (term31 l) = (term48 l).
Proof. exact (TRANS (@lem5293482 l) (@lem5293502 l)). Qed.
Lemma lem5293517 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5293395 A x (@lem5293394 A x)). Qed.
Lemma lem5293518 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5293517 real x). Qed.
Lemma lem5293519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5293520 (x : real) : (term49 x) = (imp False).
Proof. exact (MK_COMB (@lem5293519) (@lem5293518 x)). Qed.
Lemma lem5293521 (c : real) (x : real) : (real_le c x) = (real_le c x).
Proof. exact (eq_refl (real_le c x)). Qed.
Lemma lem5293522 (c : real) (x : real) : (term50 c x) = (term51 c x).
Proof. exact (MK_COMB (@lem5293520 x) (@lem5293521 c x)). Qed.
Lemma lem5293524 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5293525 (c : real) (x : real) : (term51 c x) = True.
Proof. exact (@lem5293524 (real_le c x)). Qed.
Lemma lem5293526 (c : real) (x : real) : (term50 c x) = True.
Proof. exact (TRANS (@lem5293522 c x) (@lem5293525 c x)). Qed.
Lemma lem5293527 (c : real) : (term52 c) = term53.
Proof. exact (fun_ext (fun x : real => @lem5293526 c x)). Qed.
Lemma lem5293528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293529 (c : real) : (term39 c) = term54.
Proof. exact (MK_COMB (@lem5293528) (@lem5293527 c)). Qed.
Lemma lem5293531 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5293532 (t : Prop) : (term56 t) = t.
Proof. exact (@lem5293531 real t). Qed.
Lemma lem5293533 : term54 = True.
Proof. exact (@lem5293532 True). Qed.
Lemma lem5293534 (c : real) : (term39 c) = True.
Proof. exact (TRANS (@lem5293529 c) (@lem5293533)). Qed.
Lemma lem5293535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293536 (c : real) : (term57 c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem5293535) (@lem5293534 c)). Qed.
Lemma lem5293537 (c : real) (l : real) : (real_le c l) = (real_le c l).
Proof. exact (eq_refl (real_le c l)). Qed.
Lemma lem5293538 (c : real) (l : real) : ((term39 c) = (real_le c l)) = (True = (real_le c l)).
Proof. exact (MK_COMB (@lem5293536 c) (@lem5293537 c l)). Qed.
Lemma lem5293540 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem5293541 (c : real) (l : real) : (True = (real_le c l)) = (real_le c l).
Proof. exact (@lem5293540 (real_le c l)). Qed.
Lemma lem5293542 (c : real) (l : real) : ((term39 c) = (real_le c l)) = (real_le c l).
Proof. exact (TRANS (@lem5293538 c l) (@lem5293541 c l)). Qed.
Lemma lem5293543 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293544 (c : real) (l : real) : (term45 c l) = (term58 c l).
Proof. exact (MK_COMB (@lem5293543) (@lem5293542 c l)). Qed.
Lemma lem5293545 (l : real) : (term47 l) = (term59 l).
Proof. exact (fun_ext (fun c : real => @lem5293544 c l)). Qed.
Lemma lem5293546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5293547 (l : real) : (term48 l) = (term60 l).
Proof. exact (MK_COMB (@lem5293546) (@lem5293545 l)). Qed.
Lemma lem5293552 (l : real) : (term31 l) = (term60 l).
Proof. exact (TRANS (@lem5293507 l) (@lem5293547 l)). Qed.
Lemma lem5293553 (l : real) : (term60 l) = (term31 l).
Proof. exact (SYM (@lem5293552 l)). Qed.
Lemma lem5293557 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5293563 (l : real) : (term62 l) = (term63 l).
Proof. exact (@lem5293557 (term63 l)). Qed.
Lemma lem5293564 (l : real) : (term63 l) = (term64 l).
Proof. exact (@lem1988287 l (term65 l)). Qed.
Lemma lem5293576 (l : real) : (term66 l) = (term67 l).
Proof. exact (@lem1982792 l (term65 l)). Qed.
Lemma lem5293577 (l : real) : (term68 l) = (term69 l).
Proof. exact (@lem1982781 l term70 term71). Qed.
Lemma lem5293579 (x : nat) : (real_of_num x) = (term72 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5293580 : term71 = term73.
Proof. exact (@lem5293579 term74). Qed.
Lemma lem5293582 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5293583 : term70 = term77.
Proof. exact (@lem5293582 term74). Qed.
Lemma lem5293584 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5293585 : term78 = term79.
Proof. exact (MK_COMB (@lem5293584) (@lem5293583)). Qed.
Lemma lem5293586 : term80 = term81.
Proof. exact (MK_COMB (@lem5293585) (@lem5293580)). Qed.
Lemma lem5293587 : term81 = term82.
Proof. exact (@lem1981613 term70 term71 term71 term71). Qed.
Lemma lem5293589 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5293590 : term85 = term86.
Proof. exact (@lem5293589 term74 term74). Qed.
Lemma lem5293591 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293592 : term88 = term74.
Proof. exact (EQ_MP (@lem5293591) (@lem940073)). Qed.
Lemma lem5293593 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293594 : term86 = term71.
Proof. exact (MK_COMB (@lem5293593) (@lem5293592)). Qed.
Lemma lem5293595 : term85 = term71.
Proof. exact (TRANS (@lem5293590) (@lem5293594)). Qed.
Lemma lem5293597 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5293598 : term80 = term91.
Proof. exact (@lem5293597 term74 term74). Qed.
Lemma lem5293599 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293600 : term88 = term74.
Proof. exact (EQ_MP (@lem5293599) (@lem940073)). Qed.
Lemma lem5293601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293602 : term86 = term71.
Proof. exact (MK_COMB (@lem5293601) (@lem5293600)). Qed.
Lemma lem5293603 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5293604 : term91 = term70.
Proof. exact (MK_COMB (@lem5293603) (@lem5293602)). Qed.
Lemma lem5293605 : term80 = term70.
Proof. exact (TRANS (@lem5293598) (@lem5293604)). Qed.
Lemma lem5293606 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5293607 : term92 = term93.
Proof. exact (MK_COMB (@lem5293606) (@lem5293605)). Qed.
Lemma lem5293608 : term82 = term77.
Proof. exact (MK_COMB (@lem5293607) (@lem5293595)). Qed.
Lemma lem5293609 : term81 = term77.
Proof. exact (TRANS (@lem5293587) (@lem5293608)). Qed.
Lemma lem5293610 : term80 = term77.
Proof. exact (TRANS (@lem5293586) (@lem5293609)). Qed.
Lemma lem5293612 (x : real) : (term94 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5293613 : term77 = term70.
Proof. exact (@lem5293612 term70). Qed.
Lemma lem5293614 : term80 = term70.
Proof. exact (TRANS (@lem5293610) (@lem5293613)). Qed.
Lemma lem5293617 (l : real) : (term95 l) = (term95 l).
Proof. exact (eq_refl (term95 l)). Qed.
Lemma lem5293618 (l : real) : (term69 l) = (term96 l).
Proof. exact (MK_COMB (@lem5293617 l) (@lem5293614)). Qed.
Lemma lem5293619 (l : real) : (term68 l) = (term96 l).
Proof. exact (TRANS (@lem5293577 l) (@lem5293618 l)). Qed.
Lemma lem5293620 (l : real) : (real_add l) = (real_add l).
Proof. exact (eq_refl (real_add l)). Qed.
Lemma lem5293621 (l : real) : (term67 l) = (term97 l).
Proof. exact (MK_COMB (@lem5293620 l) (@lem5293619 l)). Qed.
Lemma lem5293622 (l : real) : (term97 l) = (term98 l).
Proof. exact (@lem1982763 l (term99 l) term70). Qed.
Lemma lem5293623 (l : real) : (term100 l) = (term101 l).
Proof. exact (@lem1982715 term70 l). Qed.
Lemma lem5293625 (x : nat) : (real_of_num x) = (term72 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5293626 : term71 = term73.
Proof. exact (@lem5293625 term74). Qed.
Lemma lem5293628 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5293629 : term70 = term77.
Proof. exact (@lem5293628 term74). Qed.
Lemma lem5293630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5293631 : term102 = term103.
Proof. exact (MK_COMB (@lem5293630) (@lem5293629)). Qed.
Lemma lem5293632 : term104 = term105.
Proof. exact (MK_COMB (@lem5293631) (@lem5293626)). Qed.
Lemma lem5293633 : term106.
Proof. exact (@lem1981473 term70 term71 term71 term71 term107 term71). Qed.
Lemma lem5293635 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5293636 : term109 = term110.
Proof. exact (@lem5293635 (NUMERAL 0) term74). Qed.
Lemma lem5293637 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293638 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5293639 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293638 h1) (fun h1 : term110 = True => @lem5293637)). Qed.
Lemma lem5293640 : term110 = True.
Proof. exact (EQ_MP (@lem5293639) (@lem5293637)). Qed.
Lemma lem5293641 : term109 = True.
Proof. exact (TRANS (@lem5293636) (@lem5293640)). Qed.
Lemma lem5293642 : True = term109.
Proof. exact (SYM (@lem5293641)). Qed.
Lemma lem5293643 : term109.
Proof. exact (EQ_MP (@lem5293642) (@lem0)). Qed.
Lemma lem5293644 : term112.
Proof. exact (@lem5293633 (@lem5293643)). Qed.
Lemma lem5293646 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5293647 : term109 = term110.
Proof. exact (@lem5293646 (NUMERAL 0) term74). Qed.
Lemma lem5293648 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293649 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5293650 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293649 h1) (fun h1 : term110 = True => @lem5293648)). Qed.
Lemma lem5293651 : term110 = True.
Proof. exact (EQ_MP (@lem5293650) (@lem5293648)). Qed.
Lemma lem5293652 : term109 = True.
Proof. exact (TRANS (@lem5293647) (@lem5293651)). Qed.
Lemma lem5293653 : True = term109.
Proof. exact (SYM (@lem5293652)). Qed.
Lemma lem5293654 : term109.
Proof. exact (EQ_MP (@lem5293653) (@lem0)). Qed.
Lemma lem5293655 : term113.
Proof. exact (@lem5293644 (@lem5293654)). Qed.
Lemma lem5293657 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5293658 : term109 = term110.
Proof. exact (@lem5293657 (NUMERAL 0) term74). Qed.
Lemma lem5293659 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293660 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5293661 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293660 h1) (fun h1 : term110 = True => @lem5293659)). Qed.
Lemma lem5293662 : term110 = True.
Proof. exact (EQ_MP (@lem5293661) (@lem5293659)). Qed.
Lemma lem5293663 : term109 = True.
Proof. exact (TRANS (@lem5293658) (@lem5293662)). Qed.
Lemma lem5293664 : True = term109.
Proof. exact (SYM (@lem5293663)). Qed.
Lemma lem5293665 : term109.
Proof. exact (EQ_MP (@lem5293664) (@lem0)). Qed.
Lemma lem5293666 : term114.
Proof. exact (@lem5293655 (@lem5293665)). Qed.
Lemma lem5293668 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5293669 : term85 = term86.
Proof. exact (@lem5293668 term74 term74). Qed.
Lemma lem5293670 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293671 : term88 = term74.
Proof. exact (EQ_MP (@lem5293670) (@lem940073)). Qed.
Lemma lem5293672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293673 : term86 = term71.
Proof. exact (MK_COMB (@lem5293672) (@lem5293671)). Qed.
Lemma lem5293674 : term85 = term71.
Proof. exact (TRANS (@lem5293669) (@lem5293673)). Qed.
Lemma lem5293676 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5293677 : term80 = term91.
Proof. exact (@lem5293676 term74 term74). Qed.
Lemma lem5293678 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293679 : term88 = term74.
Proof. exact (EQ_MP (@lem5293678) (@lem940073)). Qed.
Lemma lem5293680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293681 : term86 = term71.
Proof. exact (MK_COMB (@lem5293680) (@lem5293679)). Qed.
Lemma lem5293682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5293683 : term91 = term70.
Proof. exact (MK_COMB (@lem5293682) (@lem5293681)). Qed.
Lemma lem5293684 : term80 = term70.
Proof. exact (TRANS (@lem5293677) (@lem5293683)). Qed.
Lemma lem5293685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5293686 : term115 = term102.
Proof. exact (MK_COMB (@lem5293685) (@lem5293684)). Qed.
Lemma lem5293687 : term116 = term104.
Proof. exact (MK_COMB (@lem5293686) (@lem5293674)). Qed.
Lemma lem5293689 (m : nat) : (term117 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5293690 : term104 = term107.
Proof. exact (@lem5293689 term74). Qed.
Lemma lem5293691 : term116 = term107.
Proof. exact (TRANS (@lem5293687) (@lem5293690)). Qed.
Lemma lem5293692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5293693 : term118 = term119.
Proof. exact (MK_COMB (@lem5293692) (@lem5293691)). Qed.
Lemma lem5293694 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem5293695 : term120 = term121.
Proof. exact (MK_COMB (@lem5293693) (@lem5293694)). Qed.
Lemma lem5293697 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5293698 : term121 = term107.
Proof. exact (@lem5293697 term74). Qed.
Lemma lem5293699 : term120 = term107.
Proof. exact (TRANS (@lem5293695) (@lem5293698)). Qed.
Lemma lem5293701 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5293702 : term85 = term86.
Proof. exact (@lem5293701 term74 term74). Qed.
Lemma lem5293703 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293704 : term88 = term74.
Proof. exact (EQ_MP (@lem5293703) (@lem940073)). Qed.
Lemma lem5293705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293706 : term86 = term71.
Proof. exact (MK_COMB (@lem5293705) (@lem5293704)). Qed.
Lemma lem5293707 : term85 = term71.
Proof. exact (TRANS (@lem5293702) (@lem5293706)). Qed.
Lemma lem5293708 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem5293709 : term123 = term121.
Proof. exact (MK_COMB (@lem5293708) (@lem5293707)). Qed.
Lemma lem5293711 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5293712 : term121 = term107.
Proof. exact (@lem5293711 term74). Qed.
Lemma lem5293713 : term123 = term107.
Proof. exact (TRANS (@lem5293709) (@lem5293712)). Qed.
Lemma lem5293714 : term107 = term123.
Proof. exact (SYM (@lem5293713)). Qed.
Lemma lem5293715 : term120 = term123.
Proof. exact (TRANS (@lem5293699) (@lem5293714)). Qed.
Lemma lem5293716 : term105 = term124.
Proof. exact (@lem5293666 (@lem5293715)). Qed.
Lemma lem5293717 : term104 = term124.
Proof. exact (TRANS (@lem5293632) (@lem5293716)). Qed.
Lemma lem5293719 (x : real) : (term94 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5293720 : term124 = term107.
Proof. exact (@lem5293719 term107). Qed.
Lemma lem5293721 : term104 = term107.
Proof. exact (TRANS (@lem5293717) (@lem5293720)). Qed.
Lemma lem5293722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5293723 : term125 = term119.
Proof. exact (MK_COMB (@lem5293722) (@lem5293721)). Qed.
Lemma lem5293724 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5293725 (l : real) : (term101 l) = (term126 l).
Proof. exact (MK_COMB (@lem5293723) (@lem5293724 l)). Qed.
Lemma lem5293726 (l : real) : (term100 l) = (term126 l).
Proof. exact (TRANS (@lem5293623 l) (@lem5293725 l)). Qed.
Lemma lem5293727 (l : real) : (term126 l) = term107.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5293728 (l : real) : (term100 l) = term107.
Proof. exact (TRANS (@lem5293726 l) (@lem5293727 l)). Qed.
Lemma lem5293729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5293730 (l : real) : (term127 l) = term128.
Proof. exact (MK_COMB (@lem5293729) (@lem5293728 l)). Qed.
Lemma lem5293731 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem5293732 (l : real) : (term98 l) = term129.
Proof. exact (MK_COMB (@lem5293730 l) (@lem5293731)). Qed.
Lemma lem5293733 (l : real) : (term97 l) = term129.
Proof. exact (TRANS (@lem5293622 l) (@lem5293732 l)). Qed.
Lemma lem5293734 : term129 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem5293735 (l : real) : (term97 l) = term70.
Proof. exact (TRANS (@lem5293733 l) (@lem5293734)). Qed.
Lemma lem5293736 (l : real) : (term67 l) = term70.
Proof. exact (TRANS (@lem5293621 l) (@lem5293735 l)). Qed.
Lemma lem5293738 (l : real) : (term66 l) = term70.
Proof. exact (TRANS (@lem5293576 l) (@lem5293736 l)). Qed.
Lemma lem5293739 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5293740 (l : real) : (term130 l) = term131.
Proof. exact (MK_COMB (@lem5293739) (@lem5293738 l)). Qed.
Lemma lem5293741 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem5293742 (l : real) : (term64 l) = term132.
Proof. exact (MK_COMB (@lem5293740 l) (@lem5293741)). Qed.
Lemma lem5293743 (l : real) : (term63 l) = term132.
Proof. exact (TRANS (@lem5293564 l) (@lem5293742 l)). Qed.
Lemma lem5293752 (l : real) : (term62 l) = term132.
Proof. exact (TRANS (@lem5293563 l) (@lem5293743 l)). Qed.
Lemma lem5293756 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5293758 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5293759 : term132 = term133.
Proof. exact (@lem5293758 term107 term70). Qed.
Lemma lem5293761 (x : nat) : (term75 x) = (term76 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5293762 : term70 = term77.
Proof. exact (@lem5293761 term74). Qed.
Lemma lem5293764 (x : nat) : (real_of_num x) = (term72 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5293765 : term107 = term124.
Proof. exact (@lem5293764 (NUMERAL 0)). Qed.
Lemma lem5293766 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5293767 : term134 = term135.
Proof. exact (MK_COMB (@lem5293766) (@lem5293765)). Qed.
Lemma lem5293768 : term133 = term136.
Proof. exact (MK_COMB (@lem5293767) (@lem5293762)). Qed.
Lemma lem5293769 : term137.
Proof. exact (@lem1980026 term107 term71 term70 term71). Qed.
Lemma lem5293771 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5293772 : term109 = term110.
Proof. exact (@lem5293771 (NUMERAL 0) term74). Qed.
Lemma lem5293773 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293774 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5293775 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293774 h1) (fun h1 : term110 = True => @lem5293773)). Qed.
Lemma lem5293776 : term110 = True.
Proof. exact (EQ_MP (@lem5293775) (@lem5293773)). Qed.
Lemma lem5293777 : term109 = True.
Proof. exact (TRANS (@lem5293772) (@lem5293776)). Qed.
Lemma lem5293778 : True = term109.
Proof. exact (SYM (@lem5293777)). Qed.
Lemma lem5293779 : term109.
Proof. exact (EQ_MP (@lem5293778) (@lem0)). Qed.
Lemma lem5293780 : term138.
Proof. exact (@lem5293769 (@lem5293779)). Qed.
Lemma lem5293782 (m : nat) (n : nat) : (term108 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5293783 : term109 = term110.
Proof. exact (@lem5293782 (NUMERAL 0) term74). Qed.
Lemma lem5293784 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293785 (h1 : term111 = (BIT1 0)) : term110 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5293786 : (term111 = (BIT1 0)) = (term110 = True).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293785 h1) (fun h1 : term110 = True => @lem5293784)). Qed.
Lemma lem5293787 : term110 = True.
Proof. exact (EQ_MP (@lem5293786) (@lem5293784)). Qed.
Lemma lem5293788 : term109 = True.
Proof. exact (TRANS (@lem5293783) (@lem5293787)). Qed.
Lemma lem5293789 : True = term109.
Proof. exact (SYM (@lem5293788)). Qed.
Lemma lem5293790 : term109.
Proof. exact (EQ_MP (@lem5293789) (@lem0)). Qed.
Lemma lem5293791 : term136 = term139.
Proof. exact (@lem5293780 (@lem5293790)). Qed.
Lemma lem5293793 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5293794 : term80 = term91.
Proof. exact (@lem5293793 term74 term74). Qed.
Lemma lem5293795 : (term87 = (BIT1 0)) = (term88 = term74).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5293796 : term88 = term74.
Proof. exact (EQ_MP (@lem5293795) (@lem940073)). Qed.
Lemma lem5293797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5293798 : term86 = term71.
Proof. exact (MK_COMB (@lem5293797) (@lem5293796)). Qed.
Lemma lem5293799 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5293800 : term91 = term70.
Proof. exact (MK_COMB (@lem5293799) (@lem5293798)). Qed.
Lemma lem5293801 : term80 = term70.
Proof. exact (TRANS (@lem5293794) (@lem5293800)). Qed.
Lemma lem5293803 (x : nat) : (term122 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5293804 : term121 = term107.
Proof. exact (@lem5293803 term74). Qed.
Lemma lem5293805 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5293806 : term140 = term134.
Proof. exact (MK_COMB (@lem5293805) (@lem5293804)). Qed.
Lemma lem5293807 : term139 = term133.
Proof. exact (MK_COMB (@lem5293806) (@lem5293801)). Qed.
Lemma lem5293809 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5293810 : term133 = term143.
Proof. exact (@lem5293809 (NUMERAL 0) term74). Qed.
Lemma lem5293811 : term111 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5293812 (h1 : term111 = (BIT1 0)) : (term74 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5293813 : (term111 = (BIT1 0)) = ((term74 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term111 = (BIT1 0) => @lem5293812 h1) (fun h1 : (term74 = (NUMERAL 0)) = False => @lem5293811)). Qed.
Lemma lem5293814 : (term74 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5293813) (@lem5293811)). Qed.
Lemma lem5293815 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5293816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5293817 : term144 = (and True).
Proof. exact (MK_COMB (@lem5293816) (@lem5293815)). Qed.
Lemma lem5293818 : term143 = (True /\ False).
Proof. exact (MK_COMB (@lem5293817) (@lem5293814)). Qed.
Lemma lem5293820 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5293821 : term143 = False.
Proof. exact (TRANS (@lem5293818) (@lem5293820)). Qed.
Lemma lem5293822 : term133 = False.
Proof. exact (TRANS (@lem5293810) (@lem5293821)). Qed.
Lemma lem5293823 : term139 = False.
Proof. exact (TRANS (@lem5293807) (@lem5293822)). Qed.
Lemma lem5293824 : term136 = False.
Proof. exact (TRANS (@lem5293791) (@lem5293823)). Qed.
Lemma lem5293825 : term133 = False.
Proof. exact (TRANS (@lem5293768) (@lem5293824)). Qed.
Lemma lem5293826 : term132 = False.
Proof. exact (TRANS (@lem5293759) (@lem5293825)). Qed.
Lemma lem5293827 (h1 : term132) : False.
Proof. exact (EQ_MP (@lem5293826) (@lem5293756 h1)). Qed.
Lemma lem5293829 (h1 : term132) : term132.
Proof. exact (h1). Qed.
Lemma lem5293830 (h1 : term132) : term132 = False.
Proof. exact (prop_ext (fun h2 : term132 => @lem5293827 h1) (fun h2 : False => @lem5293829 h1)). Qed.
Lemma lem5293831 (h1 : term132) : False.
Proof. exact (EQ_MP (@lem5293830 h1) (@lem5293829 h1)). Qed.
Lemma lem5293832 (l : real) (h1 : term62 l) : term62 l.
Proof. exact (h1). Qed.
Lemma lem5293833 (l : real) (h1 : term62 l) : term132.
Proof. exact (EQ_MP (@lem5293752 l) (@lem5293832 l h1)). Qed.
Lemma lem5293834 (l : real) (h1 : term62 l) : term132 = False.
Proof. exact (prop_ext (fun h2 : term132 => @lem5293831 h2) (fun h2 : False => @lem5293833 l h1)). Qed.
Lemma lem5293835 (l : real) (h1 : term62 l) : False.
Proof. exact (EQ_MP (@lem5293834 l h1) (@lem5293833 l h1)). Qed.
Lemma lem5293836 (l : real) : term145 l.
Proof. exact (fun h0 : term62 l => @lem5293835 l h0). Qed.
Lemma lem5293837 (l : real) : term146 l.
Proof. exact (@lem1386578 (term147 l)). Qed.
Lemma lem5293840 (l : real) : term147 l.
Proof. exact (@lem5293837 l (@lem5293836 l)). Qed.
Lemma lem5293841 (l : real) : term60 l.
Proof. exact (ex_intro (term59 l) (term65 l) (@lem5293840 l)). Qed.
Lemma lem5293842 (l : real) : term31 l.
Proof. exact (EQ_MP (@lem5293553 l) (@lem5293841 l)). Qed.
Lemma lem5293844 (l : real) (s : real -> Prop) (h1 : term7 s l) (h2 : s = (@EMPTY real)) : False.
Proof. exact (@lem5293842 l (@lem5293479 l s h1 h2)). Qed.
Lemma lem5293845 (s : real -> Prop) (l : real) (h1 : term7 s l) : term148 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5293844 l s h1 h0). Qed.
Lemma lem5293846 (s : real -> Prop) : (term148 s) = (term23 s).
Proof. exact (@lem69 (s = (@EMPTY real))). Qed.
Lemma lem5293847 (s : real -> Prop) (l : real) (h1 : term7 s l) : term23 s.
Proof. exact (EQ_MP (@lem5293846 s) (@lem5293845 s l h1)). Qed.
Lemma lem5293848 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : term149 s l c.
Proof. exact (@lem5293445 s l h1 c). Qed.
Lemma lem5293849 (s : real -> Prop) (c : real) (l : real) : (term149 s l c) = ((term25 s c) = (real_le c l)).
Proof. exact (eq_refl (term149 s l c)). Qed.
Lemma lem5293856 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5293849 s c l) (@lem5293848 c s l h1)). Qed.
Lemma lem5293857 (b : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s b) = (real_le b l).
Proof. exact (@lem5293856 b s l h1). Qed.
Lemma lem5293858 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term150 s) = (term151 l).
Proof. exact (fun_ext (fun b : real => @lem5293857 b s l h1)). Qed.
Lemma lem5293859 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5293860 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term24 s) = (term152 l).
Proof. exact (MK_COMB (@lem5293859) (@lem5293858 s l h1)). Qed.
Lemma lem5293865 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term152 l) = (term24 s).
Proof. exact (SYM (@lem5293860 s l h1)). Qed.
Lemma lem5293867 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5293868 (l : real) : (term152 l) = (term154 l).
Proof. exact (@lem5293867 (term152 l)). Qed.
Lemma lem5293869 (l : real) : (term154 l) = (term152 l).
Proof. exact (SYM (@lem5293868 l)). Qed.
Lemma lem5293870 (l : real) (h1 : term155 l) : term155 l.
Proof. exact (h1). Qed.
Lemma lem5293873 (l : real) (h1 : term156 l) : term156 l.
Proof. exact (h1). Qed.
Lemma lem5293874 (l : real) : term157 l.
Proof. exact (fun h0 : term156 l => @lem5293873 l h0). Qed.
Lemma lem5293875 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (h1). Qed.
Lemma lem5293876 (l : real) (h1 : term156 l) : term156 l.
Proof. exact (h1). Qed.
Lemma lem5293877 (l : real) (h1 : term156 l) (h2 : term157 l) : term156 l.
Proof. exact (@lem5293875 l h2 (@lem5293876 l h1)). Qed.
Lemma lem5293878 (l : real) (h1 : term156 l) : term158 l.
Proof. exact (fun h0 : term157 l => @lem5293877 l h1 h0). Qed.
Lemma lem5293879 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (h1). Qed.
Lemma lem5293880 (l : real) (h1 : term156 l) (h2 : term157 l) : term156 l.
Proof. exact (@lem5293878 l h1 (@lem5293879 l h2)). Qed.
Lemma lem5293881 (l : real) (h1 : term157 l) : term157 l.
Proof. exact (fun h0 : term156 l => @lem5293880 l h0 h1). Qed.
Lemma lem5293882 (l : real) : term159 l.
Proof. exact (fun h0 : term157 l => @lem5293881 l h0). Qed.
Lemma lem5293885 (l : real) : term157 l.
Proof. exact (@lem5293882 l (@lem5293874 l)). Qed.
Lemma lem5293897 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5293898 : term160 = term161.
Proof. exact (@lem5293897 term162). Qed.
Lemma lem5293903 (l : real) : (term163 l) = (term163 l).
Proof. exact (eq_refl (term163 l)). Qed.
Lemma lem5293904 (l : real) : (term156 l) = (term164 l).
Proof. exact (MK_COMB (@lem5293903 l) (@lem5293898)). Qed.
Lemma lem5293907 : term165 = term166.
Proof. exact (fun_ext (fun l : real => @lem5293904 l)). Qed.
Lemma lem5293908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293917 : term167 = term168.
Proof. exact (MK_COMB (@lem5293908) (@lem5293907)). Qed.
Lemma lem5293918 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5293919 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5293918 x)). Qed.
Lemma lem5293920 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293921 : term162 = term162.
Proof. exact (MK_COMB (@lem5293920) (@lem5293919)). Qed.
Lemma lem5293922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293923 : term161 = term161.
Proof. exact (MK_COMB (@lem5293922) (@lem5293921)). Qed.
Lemma lem5293924 (b : real) (l : real) : (real_le b l) = (real_le b l).
Proof. exact (eq_refl (real_le b l)). Qed.
Lemma lem5293925 (l : real) : (term151 l) = (term151 l).
Proof. exact (fun_ext (fun b : real => @lem5293924 b l)). Qed.
Lemma lem5293926 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5293927 (l : real) : (term152 l) = (term152 l).
Proof. exact (MK_COMB (@lem5293926) (@lem5293925 l)). Qed.
Lemma lem5293928 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293929 (l : real) : (term155 l) = (term155 l).
Proof. exact (MK_COMB (@lem5293928) (@lem5293927 l)). Qed.
Lemma lem5293930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5293931 (l : real) : (term163 l) = (term163 l).
Proof. exact (MK_COMB (@lem5293930) (@lem5293929 l)). Qed.
Lemma lem5293932 (l : real) : (term164 l) = (term164 l).
Proof. exact (MK_COMB (@lem5293931 l) (@lem5293923)). Qed.
Lemma lem5293933 : term166 = term166.
Proof. exact (fun_ext (fun l : real => @lem5293932 l)). Qed.
Lemma lem5293934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293935 : term168 = term168.
Proof. exact (MK_COMB (@lem5293934) (@lem5293933)). Qed.
Lemma lem5293958 : term167 = term168.
Proof. exact (TRANS (@lem5293917) (@lem5293935)). Qed.
Lemma lem5293959 : term168 = term167.
Proof. exact (SYM (@lem5293958)). Qed.
Lemma lem5293960 (l : real) (h1 : term155 l) : term155 l.
Proof. exact (h1). Qed.
Lemma lem5293961 (h1 : term162) : term162.
Proof. exact (h1). Qed.
Lemma lem5293963 (P : real -> Prop) : (term170 P) = (term171 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5293964 (l : real) : (term155 l) = (term172 l).
Proof. exact (@lem5293963 (term151 l)). Qed.
Lemma lem5293965 (b : real) (l : real) : (term173 l b) = (real_le b l).
Proof. exact (eq_refl (term173 l b)). Qed.
Lemma lem5293966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5293968 (b : real) (l : real) : (term174 l b) = (term58 b l).
Proof. exact (MK_COMB (@lem5293966) (@lem5293965 b l)). Qed.
Lemma lem5293969 (l : real) : (term175 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5293968 b l)). Qed.
Lemma lem5293970 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293971 (l : real) : (term172 l) = (term176 l).
Proof. exact (MK_COMB (@lem5293970) (@lem5293969 l)). Qed.
Lemma lem5293980 (l : real) : (term155 l) = (term176 l).
Proof. exact (TRANS (@lem5293964 l) (@lem5293971 l)). Qed.
Lemma lem5293981 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5293980 l) (@lem5293960 l h1)). Qed.
Lemma lem5293982 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5293983 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5293982 x)). Qed.
Lemma lem5293984 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293993 : term162 = term162.
Proof. exact (MK_COMB (@lem5293984) (@lem5293983)). Qed.
Lemma lem5293994 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5293993) (@lem5293961 h1)). Qed.
Lemma lem5294001 (b : real) (l : real) : (term58 b l) = (term58 b l).
Proof. exact (eq_refl (term58 b l)). Qed.
Lemma lem5294002 (l : real) : (term59 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5294001 b l)). Qed.
Lemma lem5294003 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294004 (l : real) : (term176 l) = (term176 l).
Proof. exact (MK_COMB (@lem5294003) (@lem5294002 l)). Qed.
Lemma lem5294005 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5294004 l) (@lem5293981 l h1)). Qed.
Lemma lem5294010 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5294011 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5294010 x)). Qed.
Lemma lem5294012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294013 : term162 = term162.
Proof. exact (MK_COMB (@lem5294012) (@lem5294011)). Qed.
Lemma lem5294014 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5294013) (@lem5293994 h1)). Qed.
Lemma lem5294016 (b : real) (l : real) : (term58 b l) = (term58 b l).
Proof. exact (eq_refl (term58 b l)). Qed.
Lemma lem5294017 (l : real) : (term59 l) = (term59 l).
Proof. exact (fun_ext (fun b : real => @lem5294016 b l)). Qed.
Lemma lem5294018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294020 (l : real) : (term176 l) = (term176 l).
Proof. exact (MK_COMB (@lem5294018) (@lem5294017 l)). Qed.
Lemma lem5294021 (l : real) (h1 : term155 l) : term176 l.
Proof. exact (EQ_MP (@lem5294020 l) (@lem5294005 l h1)). Qed.
Lemma lem5294023 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5294024 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem5294023 x)). Qed.
Lemma lem5294025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294027 : term162 = term162.
Proof. exact (MK_COMB (@lem5294025) (@lem5294024)). Qed.
Lemma lem5294028 (h1 : term162) : term162.
Proof. exact (EQ_MP (@lem5294027) (@lem5294014 h1)). Qed.
Lemma lem5294029 (_69290 : real) (l : real) (h1 : term155 l) : term177 l _69290.
Proof. exact (@lem5294021 l h1 _69290). Qed.
Lemma lem5294030 (_69290 : real) (l : real) : (term177 l _69290) = (term58 _69290 l).
Proof. exact (eq_refl (term177 l _69290)). Qed.
Lemma lem5294032 (_69291 : real) (h1 : term162) : term178 _69291.
Proof. exact (@lem5294028 h1 _69291). Qed.
Lemma lem5294033 (_69291 : real) : (term178 _69291) = (real_le _69291 _69291).
Proof. exact (eq_refl (term178 _69291)). Qed.
Lemma lem5294036 (_69290 : real) (l : real) (h1 : term155 l) : term58 _69290 l.
Proof. exact (EQ_MP (@lem5294030 _69290 l) (@lem5294029 _69290 l h1)). Qed.
Lemma lem5294040 (_69291 : real) (h1 : term162) : real_le _69291 _69291.
Proof. exact (EQ_MP (@lem5294033 _69291) (@lem5294032 _69291 h1)). Qed.
Lemma lem5294041 (l : real) (h1 : term162) : real_le l l.
Proof. exact (@lem5294040 l h1). Qed.
Lemma lem5294042 (l : real) (h1 : term162) : term179 l.
Proof. exact (fun h0 : term180 l => @lem5294041 l h1). Qed.
Lemma lem5294044 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5294045 (l : real) : (term179 l) = (real_le l l).
Proof. exact (@lem5294044 (real_le l l)). Qed.
Lemma lem5294046 (l : real) (h1 : term162) : real_le l l.
Proof. exact (EQ_MP (@lem5294045 l) (@lem5294042 l h1)). Qed.
Lemma lem5294049 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5294051 (_69290 : real) (l : real) : (term58 _69290 l) = (term182 _69290 l).
Proof. exact (@lem5294049 (real_le _69290 l)). Qed.
Lemma lem5294054 (_69290 : real) (l : real) (h1 : term155 l) : term182 _69290 l.
Proof. exact (EQ_MP (@lem5294051 _69290 l) (@lem5294036 _69290 l h1)). Qed.
Lemma lem5294055 (l : real) (h1 : term155 l) : term183 l.
Proof. exact (@lem5294054 l l h1). Qed.
Lemma lem5294058 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (@lem5294055 l h2 (@lem5294046 l h1)). Qed.
Lemma lem5294059 (l : real) (h1 : term162) (h2 : term155 l) : term184.
Proof. exact (fun h0 : ~ False => @lem5294058 l h1 h2). Qed.
Lemma lem5294061 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5294062 : term184 = False.
Proof. exact (@lem5294061 False). Qed.
Lemma lem5294063 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5294062) (@lem5294059 l h1 h2)). Qed.
Lemma lem5294064 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5294063 l h1 h2) (fun h3 : False => @lem5294028 h1)). Qed.
Lemma lem5294065 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5294064 l h1 h2) (@lem5294028 h1)). Qed.
Lemma lem5294066 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5294065 l h1 h2) (fun h3 : False => @lem5294014 h1)). Qed.
Lemma lem5294067 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5294066 l h1 h2) (@lem5294014 h1)). Qed.
Lemma lem5294068 (l : real) (h1 : term162) (h2 : term155 l) : term162 = False.
Proof. exact (prop_ext (fun h3 : term162 => @lem5294067 l h1 h2) (fun h3 : False => @lem5293994 h1)). Qed.
Lemma lem5294069 (l : real) (h1 : term162) (h2 : term155 l) : False.
Proof. exact (EQ_MP (@lem5294068 l h1 h2) (@lem5293994 h1)). Qed.
Lemma lem5294070 (l : real) (h1 : term155 l) : term160.
Proof. exact (fun h0 : term162 => @lem5294069 l h0 h1). Qed.
Lemma lem5294071 : term160 = term161.
Proof. exact (@lem69 term162). Qed.
Lemma lem5294072 (l : real) (h1 : term155 l) : term161.
Proof. exact (EQ_MP (@lem5294071) (@lem5294070 l h1)). Qed.
Lemma lem5294073 (l : real) : term164 l.
Proof. exact (fun h0 : term155 l => @lem5294072 l h0). Qed.
Lemma lem5294078 : term168.
Proof. exact (fun l : real => @lem5294073 l). Qed.
Lemma lem5294079 : term167.
Proof. exact (EQ_MP (@lem5293959) (@lem5294078)). Qed.
Lemma lem5294080 (l : real) : term185 l.
Proof. exact (@lem5294079 l). Qed.
Lemma lem5294081 (l : real) : (term185 l) = (term156 l).
Proof. exact (eq_refl (term185 l)). Qed.
Lemma lem5294082 (l : real) : term156 l.
Proof. exact (EQ_MP (@lem5294081 l) (@lem5294080 l)). Qed.
Lemma lem5294084 (l : real) : term156 l.
Proof. exact (@lem5293885 l (@lem5294082 l)). Qed.
Lemma lem5294085 (l : real) (h1 : term155 l) : term160.
Proof. exact (@lem5294084 l (@lem5293870 l h1)). Qed.
Lemma lem5294086 (l : real) (h1 : term155 l) : False.
Proof. exact (@lem5294085 l h1 (@lem1339240)). Qed.
Lemma lem5294087 (l : real) (h1 : term155 l) : (term155 l) = False.
Proof. exact (prop_ext (fun h2 : term155 l => @lem5294086 l h1) (fun h2 : False => @lem5293870 l h1)). Qed.
Lemma lem5294088 (l : real) (h1 : term155 l) : False.
Proof. exact (EQ_MP (@lem5294087 l h1) (@lem5293870 l h1)). Qed.
Lemma lem5294089 (l : real) : term154 l.
Proof. exact (fun h0 : term155 l => @lem5294088 l h0). Qed.
Lemma lem5294090 (l : real) : term152 l.
Proof. exact (EQ_MP (@lem5293869 l) (@lem5294089 l)). Qed.
Lemma lem5294091 (s : real -> Prop) (l : real) (h1 : term7 s l) : term24 s.
Proof. exact (EQ_MP (@lem5293865 s l h1) (@lem5294090 l)). Qed.
Lemma lem5294093 (s : real -> Prop) (b : real) : term6 s b.
Proof. exact (EQ_MP (@lem5293377 s b) (@lem5293376 s b)). Qed.
Lemma lem5294094 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5294093 s l). Qed.
Lemma lem5294095 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : term149 s l c.
Proof. exact (@lem5293445 s l h1 c). Qed.
Lemma lem5294096 (s : real -> Prop) (c : real) (l : real) : (term149 s l c) = ((term25 s c) = (real_le c l)).
Proof. exact (eq_refl (term149 s l c)). Qed.
Lemma lem5294105 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5294096 s c l) (@lem5294095 c s l h1)). Qed.
Lemma lem5294106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5294107 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : (term186 s c) = (term187 c l).
Proof. exact (MK_COMB (@lem5294106) (@lem5294105 c s l h1)). Qed.
Lemma lem5294108 (c : real) (l : real) : (real_le c l) = (real_le c l).
Proof. exact (eq_refl (real_le c l)). Qed.
Lemma lem5294109 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : ((term25 s c) = (real_le c l)) = ((real_le c l) = (real_le c l)).
Proof. exact (MK_COMB (@lem5294107 c s l h1) (@lem5294108 c l)). Qed.
Lemma lem5294111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5294112 (x : Prop) : (x = x) = True.
Proof. exact (@lem5294111 Prop x). Qed.
Lemma lem5294113 (c : real) (l : real) : ((real_le c l) = (real_le c l)) = True.
Proof. exact (@lem5294112 (real_le c l)). Qed.
Lemma lem5294114 (c : real) (s : real -> Prop) (l : real) (h1 : term7 s l) : ((term25 s c) = (real_le c l)) = True.
Proof. exact (TRANS (@lem5294109 c s l h1) (@lem5294113 c l)). Qed.
Lemma lem5294115 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term188 s l) = term53.
Proof. exact (fun_ext (fun c : real => @lem5294114 c s l h1)). Qed.
Lemma lem5294116 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294117 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = term54.
Proof. exact (MK_COMB (@lem5294116) (@lem5294115 s l h1)). Qed.
Lemma lem5294119 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5294120 (t : Prop) : (term56 t) = t.
Proof. exact (@lem5294119 real t). Qed.
Lemma lem5294121 : term54 = True.
Proof. exact (@lem5294120 True). Qed.
Lemma lem5294122 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = True.
Proof. exact (TRANS (@lem5294117 s l h1) (@lem5294121)). Qed.
Lemma lem5294123 (s : real -> Prop) (l : real) (h1 : term7 s l) : True = (term7 s l).
Proof. exact (SYM (@lem5294122 s l h1)). Qed.
Lemma lem5294124 (s : real -> Prop) (l : real) (h1 : term7 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5294123 s l h1) (@lem0)). Qed.
Lemma lem5294125 (s : real -> Prop) (l : real) (h1 : term7 s l) : (inf s) = l.
Proof. exact (@lem5294094 s l (@lem5294124 s l h1)). Qed.
Lemma lem5294126 (s : real -> Prop) (l : real) (h1 : term7 s l) : term22 s l.
Proof. exact (conj (@lem5294091 s l h1) (@lem5294125 s l h1)). Qed.
Lemma lem5294127 (s : real -> Prop) (l : real) (h1 : term7 s l) : term21 s l.
Proof. exact (conj (@lem5293847 s l h1) (@lem5294126 s l h1)). Qed.
Lemma lem5294129 (p : Prop) (q : Prop) (r : Prop) : term189 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5294130 (s : real -> Prop) (c : real) (l : real) : term190 s c l.
Proof. exact (@lem5294129 (term191 s) (term192 s) ((term25 s c) = (real_le c l))). Qed.
Lemma lem5294131 (s : real -> Prop) : term193 s.
Proof. exact (@lem82 (s = (@EMPTY real))). Qed.
Lemma lem5294152 (s : real -> Prop) (h1 : term23 s) : (s = (@EMPTY real)) = False.
Proof. exact (@lem5294131 s (@lem5293448 s h1)). Qed.
Lemma lem5294153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5294154 (s : real -> Prop) (h1 : term23 s) : (term23 s) = (~ False).
Proof. exact (MK_COMB (@lem5294153) (@lem5294152 s h1)). Qed.
Lemma lem5294156 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5294157 (s : real -> Prop) (h1 : term23 s) : (term23 s) = True.
Proof. exact (TRANS (@lem5294154 s h1) (@lem5294156)). Qed.
Lemma lem5294158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5294159 (s : real -> Prop) (h1 : term23 s) : (term194 s) = (and True).
Proof. exact (MK_COMB (@lem5294158) (@lem5294157 s h1)). Qed.
Lemma lem5294184 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (eq_refl (term24 s)). Qed.
Lemma lem5294185 (s : real -> Prop) (h1 : term23 s) : (term191 s) = (term195 s).
Proof. exact (MK_COMB (@lem5294159 s h1) (@lem5294184 s)). Qed.
Lemma lem5294187 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5294188 (s : real -> Prop) : (term195 s) = (term24 s).
Proof. exact (@lem5294187 (term24 s)). Qed.
Lemma lem5294213 (s : real -> Prop) (h1 : term23 s) : (term191 s) = (term24 s).
Proof. exact (TRANS (@lem5294185 s h1) (@lem5294188 s)). Qed.
Lemma lem5294214 (s : real -> Prop) (h1 : term23 s) : (term24 s) = (term191 s).
Proof. exact (SYM (@lem5294213 s h1)). Qed.
Lemma lem5294216 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5294217 (s : real -> Prop) : (term24 s) = (term196 s).
Proof. exact (@lem5294216 (term24 s)). Qed.
Lemma lem5294218 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (SYM (@lem5294217 s)). Qed.
Lemma lem5294219 (s : real -> Prop) (h1 : term197 s) : term197 s.
Proof. exact (h1). Qed.
Lemma lem5294222 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term198 b l s.
Proof. exact (h1). Qed.
Lemma lem5294223 (b : real) (l : real) (s : real -> Prop) : term199 b l s.
Proof. exact (fun h0 : term198 b l s => @lem5294222 b l s h0). Qed.
Lemma lem5294224 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (h1). Qed.
Lemma lem5294225 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term198 b l s.
Proof. exact (h1). Qed.
Lemma lem5294226 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) (h2 : term199 b l s) : term198 b l s.
Proof. exact (@lem5294224 b l s h2 (@lem5294225 b l s h1)). Qed.
Lemma lem5294227 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) : term200 b l s.
Proof. exact (fun h0 : term199 b l s => @lem5294226 b l s h1 h0). Qed.
Lemma lem5294228 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (h1). Qed.
Lemma lem5294229 (b : real) (l : real) (s : real -> Prop) (h1 : term198 b l s) (h2 : term199 b l s) : term198 b l s.
Proof. exact (@lem5294227 b l s h1 (@lem5294228 b l s h2)). Qed.
Lemma lem5294230 (b : real) (l : real) (s : real -> Prop) (h1 : term199 b l s) : term199 b l s.
Proof. exact (fun h0 : term198 b l s => @lem5294229 b l s h0 h1). Qed.
Lemma lem5294231 (b : real) (l : real) (s : real -> Prop) : term201 b l s.
Proof. exact (fun h0 : term199 b l s => @lem5294230 b l s h0). Qed.
Lemma lem5294234 (b : real) (l : real) (s : real -> Prop) : term199 b l s.
Proof. exact (@lem5294231 b l s (@lem5294223 b l s)). Qed.
Lemma lem5294260 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5294261 (s : real -> Prop) : (term196 s) = (term202 s).
Proof. exact (@lem5294260 (term197 s)). Qed.
Lemma lem5294263 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5294264 (s : real -> Prop) : (term202 s) = (term24 s).
Proof. exact (@lem5294263 (term24 s)). Qed.
Lemma lem5294269 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (TRANS (@lem5294261 s) (@lem5294264 s)). Qed.
Lemma lem5294276 (s : real -> Prop) (l : real) : (term203 s l) = (term203 s l).
Proof. exact (eq_refl (term203 s l)). Qed.
Lemma lem5294277 (l : real) (s : real -> Prop) : (term204 l s) = (term205 l s).
Proof. exact (MK_COMB (@lem5294276 s l) (@lem5294269 s)). Qed.
Lemma lem5294280 (s : real -> Prop) (b : real) : (term206 s b) = (term206 s b).
Proof. exact (eq_refl (term206 s b)). Qed.
Lemma lem5294281 (b : real) (l : real) (s : real -> Prop) : (term207 b l s) = (term208 b l s).
Proof. exact (MK_COMB (@lem5294280 s b) (@lem5294277 l s)). Qed.
Lemma lem5294284 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (eq_refl (term209 s)). Qed.
Lemma lem5294285 (b : real) (l : real) (s : real -> Prop) : (term198 b l s) = (term210 b l s).
Proof. exact (MK_COMB (@lem5294284 s) (@lem5294281 b l s)). Qed.
Lemma lem5294288 (l : real) (s : real -> Prop) : (term211 l s) = (term212 l s).
Proof. exact (fun_ext (fun b : real => @lem5294285 b l s)). Qed.
Lemma lem5294289 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294290 (l : real) (s : real -> Prop) : (term213 l s) = (term214 l s).
Proof. exact (MK_COMB (@lem5294289) (@lem5294288 l s)). Qed.
Lemma lem5294295 (s : real -> Prop) : (term215 s) = (term216 s).
Proof. exact (fun_ext (fun l : real => @lem5294290 l s)). Qed.
Lemma lem5294296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294297 (s : real -> Prop) : (term217 s) = (term218 s).
Proof. exact (MK_COMB (@lem5294296) (@lem5294295 s)). Qed.
Lemma lem5294302 : term219 = term220.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5294297 s)). Qed.
Lemma lem5294303 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5294312 : term221 = term222.
Proof. exact (MK_COMB (@lem5294303) (@lem5294302)). Qed.
Lemma lem5294317 (s : real -> Prop) (b : real) (x : real) : (term223 s b x) = (term223 s b x).
Proof. exact (eq_refl (term223 s b x)). Qed.
Lemma lem5294318 (s : real -> Prop) (b : real) : (term224 s b) = (term224 s b).
Proof. exact (fun_ext (fun x : real => @lem5294317 s b x)). Qed.
Lemma lem5294319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294320 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (MK_COMB (@lem5294319) (@lem5294318 s b)). Qed.
Lemma lem5294321 (s : real -> Prop) : (term150 s) = (term150 s).
Proof. exact (fun_ext (fun b : real => @lem5294320 s b)). Qed.
Lemma lem5294322 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5294323 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (MK_COMB (@lem5294322) (@lem5294321 s)). Qed.
Lemma lem5294326 (s : real -> Prop) (l : real) : (term203 s l) = (term203 s l).
Proof. exact (eq_refl (term203 s l)). Qed.
Lemma lem5294327 (l : real) (s : real -> Prop) : (term205 l s) = (term205 l s).
Proof. exact (MK_COMB (@lem5294326 s l) (@lem5294323 s)). Qed.
Lemma lem5294332 (s : real -> Prop) (b : real) (x : real) : (term223 s b x) = (term223 s b x).
Proof. exact (eq_refl (term223 s b x)). Qed.
Lemma lem5294333 (s : real -> Prop) (b : real) : (term224 s b) = (term224 s b).
Proof. exact (fun_ext (fun x : real => @lem5294332 s b x)). Qed.
Lemma lem5294334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294335 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (MK_COMB (@lem5294334) (@lem5294333 s b)). Qed.
Lemma lem5294336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5294337 (s : real -> Prop) (b : real) : (term206 s b) = (term206 s b).
Proof. exact (MK_COMB (@lem5294336) (@lem5294335 s b)). Qed.
Lemma lem5294338 (b : real) (l : real) (s : real -> Prop) : (term208 b l s) = (term208 b l s).
Proof. exact (MK_COMB (@lem5294337 s b) (@lem5294327 l s)). Qed.
Lemma lem5294343 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (eq_refl (term209 s)). Qed.
Lemma lem5294344 (b : real) (l : real) (s : real -> Prop) : (term210 b l s) = (term210 b l s).
Proof. exact (MK_COMB (@lem5294343 s) (@lem5294338 b l s)). Qed.
Lemma lem5294345 (l : real) (s : real -> Prop) : (term212 l s) = (term212 l s).
Proof. exact (fun_ext (fun b : real => @lem5294344 b l s)). Qed.
Lemma lem5294346 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294347 (l : real) (s : real -> Prop) : (term214 l s) = (term214 l s).
Proof. exact (MK_COMB (@lem5294346) (@lem5294345 l s)). Qed.
Lemma lem5294348 (s : real -> Prop) : (term216 s) = (term216 s).
Proof. exact (fun_ext (fun l : real => @lem5294347 l s)). Qed.
Lemma lem5294349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294350 (s : real -> Prop) : (term218 s) = (term218 s).
Proof. exact (MK_COMB (@lem5294349) (@lem5294348 s)). Qed.
Lemma lem5294351 : term220 = term220.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5294350 s)). Qed.
Lemma lem5294352 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5294353 : term222 = term222.
Proof. exact (MK_COMB (@lem5294352) (@lem5294351)). Qed.
Lemma lem5294402 : term221 = term222.
Proof. exact (TRANS (@lem5294312) (@lem5294353)). Qed.
Lemma lem5294403 : term222 = term221.
Proof. exact (SYM (@lem5294402)). Qed.
Lemma lem5294405 (s : real -> Prop) (b : real) (h1 : term25 s b) : term25 s b.
Proof. exact (h1). Qed.
Lemma lem5294408 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5294409 (s : real -> Prop) : (term24 s) = (term196 s).
Proof. exact (@lem5294408 (term24 s)). Qed.
Lemma lem5294410 (s : real -> Prop) : (term196 s) = (term24 s).
Proof. exact (SYM (@lem5294409 s)). Qed.
Lemma lem5294411 (s : real -> Prop) (h1 : term197 s) : term197 s.
Proof. exact (h1). Qed.
Lemma lem5294424 (s : real -> Prop) (b : real) (x : real) : (term223 s b x) = (term225 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5294425 (s : real -> Prop) (b : real) : (term224 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5294424 s b x)). Qed.
Lemma lem5294426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294479 (s : real -> Prop) (b : real) : (term25 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5294426) (@lem5294425 s b)). Qed.
Lemma lem5294480 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5294479 s b) (@lem5294405 s b h1)). Qed.
Lemma lem5294493 (s : real -> Prop) (b : real) (x : real) : (term228 s b x) = (term229 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5294494 (P : real -> Prop) : (term230 P) = (term34 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5294495 (s : real -> Prop) (b : real) : (term231 s b) = (term232 s b).
Proof. exact (@lem5294494 (term224 s b)). Qed.
Lemma lem5294496 (s : real -> Prop) (b : real) (x : real) : (term233 s b x) = (term223 s b x).
Proof. exact (eq_refl (term233 s b x)). Qed.
Lemma lem5294497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5294498 (s : real -> Prop) (b : real) (x : real) : (term234 s b x) = (term228 s b x).
Proof. exact (MK_COMB (@lem5294497) (@lem5294496 s b x)). Qed.
Lemma lem5294499 (s : real -> Prop) (b : real) (x : real) : (term234 s b x) = (term229 s b x).
Proof. exact (TRANS (@lem5294498 s b x) (@lem5294493 s b x)). Qed.
Lemma lem5294500 (s : real -> Prop) (b : real) : (term235 s b) = (term236 s b).
Proof. exact (fun_ext (fun x : real => @lem5294499 s b x)). Qed.
Lemma lem5294501 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5294502 (s : real -> Prop) (b : real) : (term232 s b) = (term237 s b).
Proof. exact (MK_COMB (@lem5294501) (@lem5294500 s b)). Qed.
Lemma lem5294503 (s : real -> Prop) (b : real) : (term231 s b) = (term237 s b).
Proof. exact (TRANS (@lem5294495 s b) (@lem5294502 s b)). Qed.
Lemma lem5294504 (P : real -> Prop) : (term170 P) = (term171 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5294505 (s : real -> Prop) : (term197 s) = (term238 s).
Proof. exact (@lem5294504 (term150 s)). Qed.
Lemma lem5294506 (s : real -> Prop) (b : real) : (term239 s b) = (term25 s b).
Proof. exact (eq_refl (term239 s b)). Qed.
Lemma lem5294507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5294508 (s : real -> Prop) (b : real) : (term240 s b) = (term231 s b).
Proof. exact (MK_COMB (@lem5294507) (@lem5294506 s b)). Qed.
Lemma lem5294509 (s : real -> Prop) (b : real) : (term240 s b) = (term237 s b).
Proof. exact (TRANS (@lem5294508 s b) (@lem5294503 s b)). Qed.
Lemma lem5294510 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (fun_ext (fun b : real => @lem5294509 s b)). Qed.
Lemma lem5294511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294512 (s : real -> Prop) : (term238 s) = (term243 s).
Proof. exact (MK_COMB (@lem5294511) (@lem5294510 s)). Qed.
Lemma lem5294513 (s : real -> Prop) : (term197 s) = (term243 s).
Proof. exact (TRANS (@lem5294505 s) (@lem5294512 s)). Qed.
Lemma lem5294568 {A B : Type'} (P : type1413 A B) : (term244 A B P) = (term245 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5294569 (P : type1626) : (term246 P) = (term247 P).
Proof. exact (@lem5294568 real real P). Qed.
Lemma lem5294570 (s : real -> Prop) : (term248 s) = (term249 s).
Proof. exact (@lem5294569 (term250 s)). Qed.
Lemma lem5294571 (s : real -> Prop) (b : real) : (term251 s b) = (term236 s b).
Proof. exact (eq_refl (term251 s b)). Qed.
Lemma lem5294572 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5294573 (s : real -> Prop) (b : real) (x : real) : (term252 s b x) = (term253 s b x).
Proof. exact (MK_COMB (@lem5294571 s b) (@lem5294572 x)). Qed.
Lemma lem5294574 (s : real -> Prop) (b : real) (x : real) : (term253 s b x) = (term229 s b x).
Proof. exact (eq_refl (term253 s b x)). Qed.
Lemma lem5294575 (s : real -> Prop) (b : real) (x : real) : (term252 s b x) = (term229 s b x).
Proof. exact (TRANS (@lem5294573 s b x) (@lem5294574 s b x)). Qed.
Lemma lem5294576 (s : real -> Prop) (b : real) : (term254 s b) = (term236 s b).
Proof. exact (fun_ext (fun x : real => @lem5294575 s b x)). Qed.
Lemma lem5294577 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5294578 (s : real -> Prop) (b : real) : (term255 s b) = (term237 s b).
Proof. exact (MK_COMB (@lem5294577) (@lem5294576 s b)). Qed.
Lemma lem5294579 (s : real -> Prop) : (term256 s) = (term242 s).
Proof. exact (fun_ext (fun b : real => @lem5294578 s b)). Qed.
Lemma lem5294580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294581 (s : real -> Prop) : (term248 s) = (term243 s).
Proof. exact (MK_COMB (@lem5294580) (@lem5294579 s)). Qed.
Lemma lem5294582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5294583 (s : real -> Prop) : (term257 s) = (term258 s).
Proof. exact (MK_COMB (@lem5294582) (@lem5294581 s)). Qed.
Lemma lem5294584 (s : real -> Prop) (b : real) : (term251 s b) = (term236 s b).
Proof. exact (eq_refl (term251 s b)). Qed.
Lemma lem5294585 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5294586 (s : real -> Prop) (x : real -> real) (b : real) : (term259 s x b) = (term260 s x b).
Proof. exact (MK_COMB (@lem5294584 s b) (@lem5294585 x b)). Qed.
Lemma lem5294587 (s : real -> Prop) (x : real -> real) (b : real) : (term260 s x b) = (term261 s x b).
Proof. exact (eq_refl (term260 s x b)). Qed.
Lemma lem5294588 (s : real -> Prop) (x : real -> real) (b : real) : (term259 s x b) = (term261 s x b).
Proof. exact (TRANS (@lem5294586 s x b) (@lem5294587 s x b)). Qed.
Lemma lem5294589 (s : real -> Prop) (x : real -> real) : (term262 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5294588 s x b)). Qed.
Lemma lem5294590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294591 (s : real -> Prop) (x : real -> real) : (term264 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5294590) (@lem5294589 s x)). Qed.
Lemma lem5294592 (s : real -> Prop) : (term266 s) = (term267 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5294591 s x)). Qed.
Lemma lem5294593 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5294594 (s : real -> Prop) : (term249 s) = (term268 s).
Proof. exact (MK_COMB (@lem5294593) (@lem5294592 s)). Qed.
Lemma lem5294595 (s : real -> Prop) : ((term248 s) = (term249 s)) = ((term243 s) = (term268 s)).
Proof. exact (MK_COMB (@lem5294583 s) (@lem5294594 s)). Qed.
Lemma lem5294597 (s : real -> Prop) : (term243 s) = (term268 s).
Proof. exact (EQ_MP (@lem5294595 s) (@lem5294570 s)). Qed.
Lemma lem5294598 (s : real -> Prop) : (term197 s) = (term268 s).
Proof. exact (TRANS (@lem5294513 s) (@lem5294597 s)). Qed.
Lemma lem5294599 (s : real -> Prop) (h1 : term197 s) : term268 s.
Proof. exact (EQ_MP (@lem5294598 s) (@lem5294411 s h1)). Qed.
Lemma lem5294600 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (h1). Qed.
Lemma lem5294623 (s : real -> Prop) (b : real) (x : real) : (term225 s b x) = (term225 s b x).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5294624 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5294623 s b x)). Qed.
Lemma lem5294625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294626 (s : real -> Prop) (b : real) : (term227 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5294625) (@lem5294624 s b)). Qed.
Lemma lem5294627 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5294626 s b) (@lem5294480 s b h1)). Qed.
Lemma lem5294654 (s : real -> Prop) (x : real -> real) (b : real) : (term261 s x b) = (term261 s x b).
Proof. exact (eq_refl (term261 s x b)). Qed.
Lemma lem5294655 (s : real -> Prop) (x : real -> real) : (term263 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5294654 s x b)). Qed.
Lemma lem5294656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294657 (s : real -> Prop) (x : real -> real) : (term265 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5294656) (@lem5294655 s x)). Qed.
Lemma lem5294658 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (EQ_MP (@lem5294657 s x) (@lem5294600 s x h1)). Qed.
Lemma lem5294670 (s : real -> Prop) (b : real) (x : real) : (term225 s b x) = (term225 s b x).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5294671 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (fun_ext (fun x : real => @lem5294670 s b x)). Qed.
Lemma lem5294672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294674 (s : real -> Prop) (b : real) : (term227 s b) = (term227 s b).
Proof. exact (MK_COMB (@lem5294672) (@lem5294671 s b)). Qed.
Lemma lem5294675 (s : real -> Prop) (b : real) (h1 : term25 s b) : term227 s b.
Proof. exact (EQ_MP (@lem5294674 s b) (@lem5294627 s b h1)). Qed.
Lemma lem5294685 (s : real -> Prop) (x : real -> real) (b : real) : (term261 s x b) = (term261 s x b).
Proof. exact (eq_refl (term261 s x b)). Qed.
Lemma lem5294686 (s : real -> Prop) (x : real -> real) : (term263 s x) = (term263 s x).
Proof. exact (fun_ext (fun b : real => @lem5294685 s x b)). Qed.
Lemma lem5294687 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5294689 (s : real -> Prop) (x : real -> real) : (term265 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5294687) (@lem5294686 s x)). Qed.
Lemma lem5294690 (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term265 s x.
Proof. exact (EQ_MP (@lem5294689 s x) (@lem5294658 s x h1)). Qed.
Lemma lem5294691 (_69294 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term269 s b _69294.
Proof. exact (@lem5294675 s b h1 _69294). Qed.
Lemma lem5294692 (s : real -> Prop) (b : real) (_69294 : real) : (term269 s b _69294) = (term225 s b _69294).
Proof. exact (eq_refl (term269 s b _69294)). Qed.
Lemma lem5294694 (_69295 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term270 s x _69295.
Proof. exact (@lem5294690 s x h1 _69295). Qed.
Lemma lem5294695 (s : real -> Prop) (x : real -> real) (_69295 : real) : (term270 s x _69295) = (term261 s x _69295).
Proof. exact (eq_refl (term270 s x _69295)). Qed.
Lemma lem5294696 (_69295 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term261 s x _69295.
Proof. exact (EQ_MP (@lem5294695 s x _69295) (@lem5294694 _69295 s x h1)). Qed.
Lemma lem5294755 (_69294 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term225 s b _69294.
Proof. exact (EQ_MP (@lem5294692 s b _69294) (@lem5294691 _69294 s b h1)). Qed.
Lemma lem5294783 (_69295 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term271 x _69295.
Proof. exact (proj2 (@lem5294696 _69295 s x h1)). Qed.
Lemma lem5294835 (_69295 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x _69295 s.
Proof. exact (proj1 (@lem5294696 _69295 s x h1)). Qed.
Lemma lem5294836 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x b s.
Proof. exact (@lem5294835 b s x h1). Qed.
Lemma lem5294837 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term273 x b s.
Proof. exact (fun h0 : term274 x b s => @lem5294836 b s x h1). Qed.
Lemma lem5294839 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5294840 (x : real -> real) (b : real) (s : real -> Prop) : (term273 x b s) = (term272 x b s).
Proof. exact (@lem5294839 (term272 x b s)). Qed.
Lemma lem5294841 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term272 x b s.
Proof. exact (EQ_MP (@lem5294840 x b s) (@lem5294837 b s x h1)). Qed.
Lemma lem5294847 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5294848 (b : real) (_69294 : real) (s : real -> Prop) : (term225 s b _69294) = (term275 b _69294 s).
Proof. exact (@lem5294847 (real_le b _69294) (term276 _69294 s)). Qed.
Lemma lem5294854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5294855 (b : real) (_69294 : real) (s : real -> Prop) : (term277 s b _69294) = (term278 b _69294 s).
Proof. exact (MK_COMB (@lem5294854) (@lem5294848 b _69294 s)). Qed.
Lemma lem5294861 (b : real) (_69294 : real) (s : real -> Prop) : (term275 b _69294 s) = (term275 b _69294 s).
Proof. exact (eq_refl (term275 b _69294 s)). Qed.
Lemma lem5294862 (b : real) (_69294 : real) (s : real -> Prop) : ((term225 s b _69294) = (term275 b _69294 s)) = ((term275 b _69294 s) = (term275 b _69294 s)).
Proof. exact (MK_COMB (@lem5294855 b _69294 s) (@lem5294861 b _69294 s)). Qed.
Lemma lem5294864 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5294865 (x : Prop) : (x = x) = True.
Proof. exact (@lem5294864 Prop x). Qed.
Lemma lem5294866 (b : real) (_69294 : real) (s : real -> Prop) : ((term275 b _69294 s) = (term275 b _69294 s)) = True.
Proof. exact (@lem5294865 (term275 b _69294 s)). Qed.
Lemma lem5294867 (b : real) (_69294 : real) (s : real -> Prop) : ((term225 s b _69294) = (term275 b _69294 s)) = True.
Proof. exact (TRANS (@lem5294862 b _69294 s) (@lem5294866 b _69294 s)). Qed.
Lemma lem5294868 (b : real) (_69294 : real) (s : real -> Prop) : True = ((term225 s b _69294) = (term275 b _69294 s)).
Proof. exact (SYM (@lem5294867 b _69294 s)). Qed.
Lemma lem5294869 (b : real) (_69294 : real) (s : real -> Prop) : (term225 s b _69294) = (term275 b _69294 s).
Proof. exact (EQ_MP (@lem5294868 b _69294 s) (@lem0)). Qed.
Lemma lem5294870 (_69294 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term275 b _69294 s.
Proof. exact (EQ_MP (@lem5294869 b _69294 s) (@lem5294755 _69294 s b h1)). Qed.
Lemma lem5294872 (b : Prop) (a : Prop) : (a \/ b) = (term279 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5294873 (s : real -> Prop) (b : real) (_69294 : real) : (term275 b _69294 s) = (term280 s b _69294).
Proof. exact (@lem5294872 (term276 _69294 s) (real_le b _69294)). Qed.
Lemma lem5294875 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5294876 (_69294 : real) (s : real -> Prop) : (term281 _69294 s) = (@IN real _69294 s).
Proof. exact (@lem5294875 (@IN real _69294 s)). Qed.
Lemma lem5294877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5294878 (_69294 : real) (s : real -> Prop) : (term282 _69294 s) = (term283 _69294 s).
Proof. exact (MK_COMB (@lem5294877) (@lem5294876 _69294 s)). Qed.
Lemma lem5294879 (b : real) (_69294 : real) : (real_le b _69294) = (real_le b _69294).
Proof. exact (eq_refl (real_le b _69294)). Qed.
Lemma lem5294880 (s : real -> Prop) (b : real) (_69294 : real) : (term280 s b _69294) = (term223 s b _69294).
Proof. exact (MK_COMB (@lem5294878 _69294 s) (@lem5294879 b _69294)). Qed.
Lemma lem5294881 (s : real -> Prop) (b : real) (_69294 : real) : (term275 b _69294 s) = (term223 s b _69294).
Proof. exact (TRANS (@lem5294873 s b _69294) (@lem5294880 s b _69294)). Qed.
Lemma lem5294884 (_69294 : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term223 s b _69294.
Proof. exact (EQ_MP (@lem5294881 s b _69294) (@lem5294870 _69294 s b h1)). Qed.
Lemma lem5294885 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term284 s x b.
Proof. exact (@lem5294884 (x b) s b h1). Qed.
Lemma lem5294888 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term285 x b.
Proof. exact (@lem5294885 x s b h2 (@lem5294841 b s x h1)). Qed.
Lemma lem5294889 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term286 x b.
Proof. exact (fun h0 : term271 x b => @lem5294888 x s b h1 h2). Qed.
Lemma lem5294891 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5294892 (x : real -> real) (b : real) : (term286 x b) = (term285 x b).
Proof. exact (@lem5294891 (term285 x b)). Qed.
Lemma lem5294893 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term285 x b.
Proof. exact (EQ_MP (@lem5294892 x b) (@lem5294889 x s b h1 h2)). Qed.
Lemma lem5294896 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5294898 (x : real -> real) (_69295 : real) : (term271 x _69295) = (term287 x _69295).
Proof. exact (@lem5294896 (term285 x _69295)). Qed.
Lemma lem5294901 (_69295 : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term287 x _69295.
Proof. exact (EQ_MP (@lem5294898 x _69295) (@lem5294783 _69295 s x h1)). Qed.
Lemma lem5294902 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term265 s x) : term287 x b.
Proof. exact (@lem5294901 b s x h1). Qed.
Lemma lem5294905 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (@lem5294902 b s x h1 (@lem5294893 x s b h1 h2)). Qed.
Lemma lem5294906 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : term184.
Proof. exact (fun h0 : ~ False => @lem5294905 x s b h1 h2). Qed.
Lemma lem5294908 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5294909 : term184 = False.
Proof. exact (@lem5294908 False). Qed.
Lemma lem5294911 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5294909) (@lem5294906 x s b h1 h2)). Qed.
Lemma lem5294912 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : (term265 s x) = False.
Proof. exact (prop_ext (fun h3 : term265 s x => @lem5294911 x s b h1 h2) (fun h3 : False => @lem5294690 s x h1)). Qed.
Lemma lem5294913 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5294912 x s b h1 h2) (@lem5294690 s x h1)). Qed.
Lemma lem5294914 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : (term265 s x) = False.
Proof. exact (prop_ext (fun h3 : term265 s x => @lem5294913 x s b h1 h2) (fun h3 : False => @lem5294658 s x h1)). Qed.
Lemma lem5294915 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term265 s x) (h2 : term25 s b) : False.
Proof. exact (EQ_MP (@lem5294914 x s b h1 h2) (@lem5294658 s x h1)). Qed.
Lemma lem5294916 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : False.
Proof. exact (ex_elim (@lem5294599 s h2) (fun x : real -> real => fun h0 : term267 s x => @lem5294915 x s b h0 h1)). Qed.
Lemma lem5294917 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : (term197 s) = False.
Proof. exact (prop_ext (fun h3 : term197 s => @lem5294916 b s h1 h2) (fun h3 : False => @lem5294411 s h2)). Qed.
Lemma lem5294918 (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term197 s) : False.
Proof. exact (EQ_MP (@lem5294917 b s h1 h2) (@lem5294411 s h2)). Qed.
Lemma lem5294919 (s : real -> Prop) (b : real) (h1 : term25 s b) : term196 s.
Proof. exact (fun h0 : term197 s => @lem5294918 b s h1 h0). Qed.
Lemma lem5294920 (s : real -> Prop) (b : real) (h1 : term25 s b) : term24 s.
Proof. exact (EQ_MP (@lem5294410 s) (@lem5294919 s b h1)). Qed.
Lemma lem5294921 (l : real) (s : real -> Prop) (b : real) (h1 : term25 s b) : term205 l s.
Proof. exact (fun h0 : (inf s) = l => @lem5294920 s b h1). Qed.
Lemma lem5294922 (b : real) (l : real) (s : real -> Prop) : term208 b l s.
Proof. exact (fun h0 : term25 s b => @lem5294921 l s b h0). Qed.
Lemma lem5294923 (b : real) (l : real) (s : real -> Prop) : term210 b l s.
Proof. exact (fun h0 : term23 s => @lem5294922 b l s). Qed.
Lemma lem5294928 (l : real) (s : real -> Prop) : term214 l s.
Proof. exact (fun b : real => @lem5294923 b l s). Qed.
Lemma lem5294933 (s : real -> Prop) : term218 s.
Proof. exact (fun l : real => @lem5294928 l s). Qed.
Lemma lem5294938 : term222.
Proof. exact (fun s : real -> Prop => @lem5294933 s). Qed.
Lemma lem5294939 : term221.
Proof. exact (EQ_MP (@lem5294403) (@lem5294938)). Qed.
Lemma lem5294940 (s : real -> Prop) : term288 s.
Proof. exact (@lem5294939 s). Qed.
Lemma lem5294941 (s : real -> Prop) : (term288 s) = (term217 s).
Proof. exact (eq_refl (term288 s)). Qed.
Lemma lem5294942 (s : real -> Prop) : term217 s.
Proof. exact (EQ_MP (@lem5294941 s) (@lem5294940 s)). Qed.
Lemma lem5294943 (s : real -> Prop) (l : real) : term289 s l.
Proof. exact (@lem5294942 s l). Qed.
Lemma lem5294944 (l : real) (s : real -> Prop) : (term289 s l) = (term213 l s).
Proof. exact (eq_refl (term289 s l)). Qed.
Lemma lem5294945 (l : real) (s : real -> Prop) : term213 l s.
Proof. exact (EQ_MP (@lem5294944 l s) (@lem5294943 s l)). Qed.
Lemma lem5294946 (l : real) (s : real -> Prop) (b : real) : term290 l s b.
Proof. exact (@lem5294945 l s b). Qed.
Lemma lem5294947 (b : real) (l : real) (s : real -> Prop) : (term290 l s b) = (term198 b l s).
Proof. exact (eq_refl (term290 l s b)). Qed.
Lemma lem5294948 (b : real) (l : real) (s : real -> Prop) : term198 b l s.
Proof. exact (EQ_MP (@lem5294947 b l s) (@lem5294946 l s b)). Qed.
Lemma lem5294950 (b : real) (l : real) (s : real -> Prop) : term198 b l s.
Proof. exact (@lem5294234 b l s (@lem5294948 b l s)). Qed.
Lemma lem5294951 (b : real) (l : real) (s : real -> Prop) (h1 : term23 s) : term207 b l s.
Proof. exact (@lem5294950 b l s (@lem5293448 s h1)). Qed.
Lemma lem5294952 (l : real) (b : real) (s : real -> Prop) (h1 : term25 s b) (h2 : term23 s) : term204 l s.
Proof. exact (@lem5294951 b l s h2 (@lem5293451 s b h1)). Qed.
Lemma lem5294953 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term196 s.
Proof. exact (@lem5294952 l b s h1 h2 (@lem5293449 s l h3)). Qed.
Lemma lem5294954 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (inf s) = l) : False.
Proof. exact (@lem5294953 b s l h1 h3 h4 (@lem5294219 s h2)). Qed.
Lemma lem5294955 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (inf s) = l) : (term197 s) = False.
Proof. exact (prop_ext (fun h5 : term197 s => @lem5294954 b s l h1 h2 h3 h4) (fun h5 : False => @lem5294219 s h2)). Qed.
Lemma lem5294956 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term197 s) (h3 : term23 s) (h4 : (inf s) = l) : False.
Proof. exact (EQ_MP (@lem5294955 b s l h1 h2 h3 h4) (@lem5294219 s h2)). Qed.
Lemma lem5294957 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term196 s.
Proof. exact (fun h0 : term197 s => @lem5294956 b s l h1 h0 h2 h3). Qed.
Lemma lem5294958 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term24 s.
Proof. exact (EQ_MP (@lem5294218 s) (@lem5294957 b s l h1 h2 h3)). Qed.
Lemma lem5294959 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term191 s.
Proof. exact (EQ_MP (@lem5294214 s h2) (@lem5294958 b s l h1 h2 h3)). Qed.
Lemma lem5294960 (s : real -> Prop) (c : real) (l : real) : (term291 s c l) = (term291 s c l).
Proof. exact (eq_refl (term291 s c l)). Qed.
Lemma lem5294961 (c : real) (s : real -> Prop) (l : real) (h1 : (inf s) = l) : (term292 c l s) = (term293 s c l).
Proof. exact (MK_COMB (@lem5294960 s c l) (@lem5293449 s l h1)). Qed.
Lemma lem5294962 (s : real -> Prop) (c : real) (l : real) : (term293 s c l) = (term294 s c l).
Proof. exact (eq_refl (term293 s c l)). Qed.
Lemma lem5294963 (c : real) (l : real) (s : real -> Prop) : (term295 c l s) = (term295 c l s).
Proof. exact (eq_refl (term295 c l s)). Qed.
Lemma lem5294964 (s : real -> Prop) (c : real) (l : real) : ((term292 c l s) = (term293 s c l)) = ((term292 c l s) = (term294 s c l)).
Proof. exact (MK_COMB (@lem5294963 c l s) (@lem5294962 s c l)). Qed.
Lemma lem5294965 (s : real -> Prop) (c : real) (l : real) : (term292 c l s) = (term296 s c l).
Proof. exact (eq_refl (term292 c l s)). Qed.
Lemma lem5294966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5294967 (s : real -> Prop) (c : real) (l : real) : (term295 c l s) = (term297 s c l).
Proof. exact (MK_COMB (@lem5294966) (@lem5294965 s c l)). Qed.
Lemma lem5294968 (s : real -> Prop) (c : real) (l : real) : (term294 s c l) = (term294 s c l).
Proof. exact (eq_refl (term294 s c l)). Qed.
Lemma lem5294969 (s : real -> Prop) (c : real) (l : real) : ((term292 c l s) = (term294 s c l)) = ((term296 s c l) = (term294 s c l)).
Proof. exact (MK_COMB (@lem5294967 s c l) (@lem5294968 s c l)). Qed.
Lemma lem5294970 (s : real -> Prop) (c : real) (l : real) : ((term292 c l s) = (term293 s c l)) = ((term296 s c l) = (term294 s c l)).
Proof. exact (TRANS (@lem5294964 s c l) (@lem5294969 s c l)). Qed.
Lemma lem5294971 (c : real) (s : real -> Prop) (l : real) (h1 : (inf s) = l) : (term296 s c l) = (term294 s c l).
Proof. exact (EQ_MP (@lem5294970 s c l) (@lem5294961 c s l h1)). Qed.
Lemma lem5294972 (c : real) (s : real -> Prop) (l : real) (h1 : (inf s) = l) : (term294 s c l) = (term296 s c l).
Proof. exact (SYM (@lem5294971 c s l h1)). Qed.
Lemma lem5295001 (s : real -> Prop) (l : real) (h1 : term298 s l) : term298 s l.
Proof. exact (h1). Qed.
Lemma lem5295002 (s : real -> Prop) (l : real) (h1 : term299 s l) : term299 s l.
Proof. exact (h1). Qed.
Lemma lem5295003 (s : real -> Prop) (l : real) (h1 : term25 s l) : term25 s l.
Proof. exact (h1). Qed.
Lemma lem5295027 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term300 s l b.
Proof. exact (@lem5295002 s l h1 b). Qed.
Lemma lem5295028 (s : real -> Prop) (b : real) (l : real) : (term300 s l b) = (term301 s b l).
Proof. exact (eq_refl (term300 s l b)). Qed.
Lemma lem5295029 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term301 s b l.
Proof. exact (EQ_MP (@lem5295028 s b l) (@lem5295027 b s l h1)). Qed.
Lemma lem5295030 (s : real -> Prop) (b : real) (l : real) : (term301 s b l) = ((term301 s b l) = True).
Proof. exact (@lem7 (term301 s b l)). Qed.
Lemma lem5295033 (b : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : (term301 s b l) = True.
Proof. exact (EQ_MP (@lem5295030 s b l) (@lem5295029 b s l h1)). Qed.
Lemma lem5295034 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : (term301 s c l) = True.
Proof. exact (@lem5295033 c s l h1). Qed.
Lemma lem5295035 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : True = (term301 s c l).
Proof. exact (SYM (@lem5295034 c s l h1)). Qed.
Lemma lem5295036 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) : term301 s c l.
Proof. exact (EQ_MP (@lem5295035 c s l h1) (@lem0)). Qed.
Lemma lem5295075 (c : real) (l : real) (h1 : real_le c l) : real_le c l.
Proof. exact (h1). Qed.
Lemma lem5295076 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5295077 (h1 : term302) : term302.
Proof. exact (h1). Qed.
Lemma lem5295078 (x : real) (h1 : term302) : term303 x.
Proof. exact (@lem5295077 h1 x). Qed.
Lemma lem5295079 (x : real) : (term303 x) = (term304 x).
Proof. exact (eq_refl (term303 x)). Qed.
Lemma lem5295080 (x : real) (h1 : term302) : term304 x.
Proof. exact (EQ_MP (@lem5295079 x) (@lem5295078 x h1)). Qed.
Lemma lem5295081 (x : real) (y : real) (h1 : term302) : term305 x y.
Proof. exact (@lem5295080 x h1 y). Qed.
Lemma lem5295082 (y : real) (x : real) : (term305 x y) = (term306 y x).
Proof. exact (eq_refl (term305 x y)). Qed.
Lemma lem5295083 (y : real) (x : real) (h1 : term302) : term306 y x.
Proof. exact (EQ_MP (@lem5295082 y x) (@lem5295081 x y h1)). Qed.
Lemma lem5295084 (y : real) (x : real) (z : real) (h1 : term302) : term307 y x z.
Proof. exact (@lem5295083 y x h1 z). Qed.
Lemma lem5295085 (y : real) (x : real) (z : real) : (term307 y x z) = (term308 y x z).
Proof. exact (eq_refl (term307 y x z)). Qed.
Lemma lem5295086 (y : real) (x : real) (z : real) (h1 : term302) : term308 y x z.
Proof. exact (EQ_MP (@lem5295085 y x z) (@lem5295084 y x z h1)). Qed.
Lemma lem5295087 (x : real) (y : real) (z : real) (h1 : term309 x y z) : term309 x y z.
Proof. exact (h1). Qed.
Lemma lem5295088 (x : real) (y : real) (z : real) (h1 : term302) (h2 : term309 x y z) : real_le x z.
Proof. exact (@lem5295086 y x z h1 (@lem5295087 x y z h2)). Qed.
Lemma lem5295089 (x : real) (y : real) (z : real) (h1 : term309 x y z) : term310 x z.
Proof. exact (fun h0 : term302 => @lem5295088 x y z h0 h1). Qed.
Lemma lem5295090 (x : real) (z : real) (h1 : term311 x z) : term311 x z.
Proof. exact (h1). Qed.
Lemma lem5295091 (x : real) (z : real) (h1 : term311 x z) : term310 x z.
Proof. exact (ex_elim (@lem5295090 x z h1) (fun y : real => fun h0 : term312 x z y => @lem5295089 x y z h0)). Qed.
Lemma lem5295092 (h1 : term302) : term302.
Proof. exact (h1). Qed.
Lemma lem5295093 (x : real) (z : real) (h1 : term302) (h2 : term311 x z) : real_le x z.
Proof. exact (@lem5295091 x z h2 (@lem5295092 h1)). Qed.
Lemma lem5295094 (x : real) (z : real) (h1 : term302) : term313 x z.
Proof. exact (fun h0 : term311 x z => @lem5295093 x z h1 h0). Qed.
Lemma lem5295095 (x : real) (h1 : term302) : term314 x.
Proof. exact (fun z : real => @lem5295094 x z h1). Qed.
Lemma lem5295096 (h1 : term302) : term315.
Proof. exact (fun x : real => @lem5295095 x h1). Qed.
Lemma lem5295097 : term316.
Proof. exact (fun h0 : term302 => @lem5295096 h0). Qed.
Lemma lem5295098 : term315.
Proof. exact (@lem5295097 (@lem1339577)). Qed.
Lemma lem5295099 (x : real) : term317 x.
Proof. exact (@lem5295098 x). Qed.
Lemma lem5295100 (x : real) : (term317 x) = (term314 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem5295101 (x : real) : term314 x.
Proof. exact (EQ_MP (@lem5295100 x) (@lem5295099 x)). Qed.
Lemma lem5295102 (x : real) (z : real) : term318 x z.
Proof. exact (@lem5295101 x z). Qed.
Lemma lem5295103 (x : real) (z : real) : (term318 x z) = (term313 x z).
Proof. exact (eq_refl (term318 x z)). Qed.
Lemma lem5295106 (x : real) (z : real) : term313 x z.
Proof. exact (EQ_MP (@lem5295103 x z) (@lem5295102 x z)). Qed.
Lemma lem5295107 (c : real) (x : real) : term313 c x.
Proof. exact (@lem5295106 c x). Qed.
Lemma lem5295133 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term233 s l x.
Proof. exact (@lem5295003 s l h1 x). Qed.
Lemma lem5295134 (s : real -> Prop) (l : real) (x : real) : (term233 s l x) = (term223 s l x).
Proof. exact (eq_refl (term233 s l x)). Qed.
Lemma lem5295135 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term223 s l x.
Proof. exact (EQ_MP (@lem5295134 s l x) (@lem5295133 x s l h1)). Qed.
Lemma lem5295136 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5295137 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : real_le l x.
Proof. exact (@lem5295135 x s l h1 (@lem5295136 x s h2)). Qed.
Lemma lem5295138 (l : real) (x : real) : (real_le l x) = ((real_le l x) = True).
Proof. exact (@lem7 (real_le l x)). Qed.
Lemma lem5295139 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le l x) = True.
Proof. exact (EQ_MP (@lem5295138 l x) (@lem5295137 l x s h1 h2)). Qed.
Lemma lem5295157 (c : real) (l : real) : (real_le c l) = ((real_le c l) = True).
Proof. exact (@lem7 (real_le c l)). Qed.
Lemma lem5295159 (x : real) (s : real -> Prop) : (@IN real x s) = ((@IN real x s) = True).
Proof. exact (@lem7 (@IN real x s)). Qed.
Lemma lem5295164 (c : real) (l : real) (h1 : real_le c l) : (real_le c l) = True.
Proof. exact (EQ_MP (@lem5295157 c l) (@lem5295075 c l h1)). Qed.
Lemma lem5295165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5295166 (c : real) (l : real) (h1 : real_le c l) : (term319 c l) = (and True).
Proof. exact (MK_COMB (@lem5295165) (@lem5295164 c l h1)). Qed.
Lemma lem5295168 (x : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term320 s l x.
Proof. exact (fun h0 : @IN real x s => @lem5295139 l x s h1 h0). Qed.
Lemma lem5295170 (x : real) (s : real -> Prop) (h1 : @IN real x s) : (@IN real x s) = True.
Proof. exact (EQ_MP (@lem5295159 x s) (@lem5295076 x s h1)). Qed.
Lemma lem5295171 (x : real) (s : real -> Prop) (h1 : @IN real x s) : True = (@IN real x s).
Proof. exact (SYM (@lem5295170 x s h1)). Qed.
Lemma lem5295172 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5295171 x s h1) (@lem0)). Qed.
Lemma lem5295173 (l : real) (x : real) (s : real -> Prop) (h1 : term25 s l) (h2 : @IN real x s) : (real_le l x) = True.
Proof. exact (@lem5295168 x s l h1 (@lem5295172 x s h2)). Qed.
Lemma lem5295174 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (term309 c l x) = (True /\ True).
Proof. exact (MK_COMB (@lem5295166 c l h3) (@lem5295173 l x s h1 h2)). Qed.
Lemma lem5295176 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5295177 : (True /\ True) = True.
Proof. exact (@lem5295176 True). Qed.
Lemma lem5295178 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (term309 c l x) = True.
Proof. exact (TRANS (@lem5295174 x s c l h1 h2 h3) (@lem5295177)). Qed.
Lemma lem5295179 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : True = (term309 c l x).
Proof. exact (SYM (@lem5295178 x s c l h1 h2 h3)). Qed.
Lemma lem5295180 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : term309 c l x.
Proof. exact (EQ_MP (@lem5295179 x s c l h1 h2 h3) (@lem0)). Qed.
Lemma lem5295181 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : term311 c x.
Proof. exact (ex_intro (term312 c x) l (@lem5295180 x s c l h1 h2 h3)). Qed.
Lemma lem5295182 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : real_le c x.
Proof. exact (@lem5295107 c x (@lem5295181 x s c l h1 h2 h3)). Qed.
Lemma lem5295183 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : (@IN real x s) = (real_le c x).
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5295182 x s c l h1 h2 h3) (fun h4 : real_le c x => @lem5295076 x s h2)). Qed.
Lemma lem5295184 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : @IN real x s) (h3 : real_le c l) : real_le c x.
Proof. exact (EQ_MP (@lem5295183 x s c l h1 h2 h3) (@lem5295076 x s h2)). Qed.
Lemma lem5295185 (x : real) (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term223 s c x.
Proof. exact (fun h0 : @IN real x s => @lem5295184 x s c l h1 h0 h2). Qed.
Lemma lem5295190 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term25 s c.
Proof. exact (fun x : real => @lem5295185 x s c l h1 h2). Qed.
Lemma lem5295191 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : (real_le c l) = (term25 s c).
Proof. exact (prop_ext (fun h3 : real_le c l => @lem5295190 s c l h1 h2) (fun h3 : term25 s c => @lem5295075 c l h2)). Qed.
Lemma lem5295192 (s : real -> Prop) (c : real) (l : real) (h1 : term25 s l) (h2 : real_le c l) : term25 s c.
Proof. exact (EQ_MP (@lem5295191 s c l h1 h2) (@lem5295075 c l h2)). Qed.
Lemma lem5295194 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) : term321 l s c.
Proof. exact (fun h0 : real_le c l => @lem5295192 s c l h1 h0). Qed.
Lemma lem5295195 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : term322 l s c.
Proof. exact (conj (@lem5295036 c s l h1) (@lem5295194 c s l h2)). Qed.
Lemma lem5295196 (s : real -> Prop) (c : real) (l : real) : (term322 l s c) = ((term25 s c) = (real_le c l)).
Proof. exact (@lem32 (term25 s c) (real_le c l)). Qed.
Lemma lem5295197 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5295196 s c l) (@lem5295195 c s l h1 h2)). Qed.
Lemma lem5295198 (s : real -> Prop) (l : real) (h1 : term298 s l) : term299 s l.
Proof. exact (proj2 (@lem5295001 s l h1)). Qed.
Lemma lem5295199 (s : real -> Prop) (l : real) (h1 : term298 s l) : term25 s l.
Proof. exact (proj1 (@lem5295001 s l h1)). Qed.
Lemma lem5295200 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term299 s l) = ((term25 s c) = (real_le c l)).
Proof. exact (prop_ext (fun h3 : term299 s l => @lem5295197 c s l h1 h2) (fun h3 : (term25 s c) = (real_le c l) => @lem5295002 s l h1)). Qed.
Lemma lem5295201 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5295200 c s l h1 h2) (@lem5295002 s l h1)). Qed.
Lemma lem5295202 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s l) = ((term25 s c) = (real_le c l)).
Proof. exact (prop_ext (fun h3 : term25 s l => @lem5295201 c s l h1 h2) (fun h3 : (term25 s c) = (real_le c l) => @lem5295003 s l h2)). Qed.
Lemma lem5295203 (c : real) (s : real -> Prop) (l : real) (h1 : term299 s l) (h2 : term25 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5295202 c s l h1 h2) (@lem5295003 s l h2)). Qed.
Lemma lem5295204 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) (h2 : term298 s l) : (term299 s l) = ((term25 s c) = (real_le c l)).
Proof. exact (prop_ext (fun h3 : term299 s l => @lem5295203 c s l h3 h1) (fun h3 : (term25 s c) = (real_le c l) => @lem5295198 s l h2)). Qed.
Lemma lem5295205 (c : real) (s : real -> Prop) (l : real) (h1 : term25 s l) (h2 : term298 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5295204 c s l h1 h2) (@lem5295198 s l h2)). Qed.
Lemma lem5295206 (c : real) (s : real -> Prop) (l : real) (h1 : term298 s l) : (term25 s l) = ((term25 s c) = (real_le c l)).
Proof. exact (prop_ext (fun h2 : term25 s l => @lem5295205 c s l h2 h1) (fun h2 : (term25 s c) = (real_le c l) => @lem5295199 s l h1)). Qed.
Lemma lem5295207 (c : real) (s : real -> Prop) (l : real) (h1 : term298 s l) : (term25 s c) = (real_le c l).
Proof. exact (EQ_MP (@lem5295206 c s l h1) (@lem5295199 s l h1)). Qed.
Lemma lem5295208 (s : real -> Prop) (c : real) (l : real) : term294 s c l.
Proof. exact (fun h0 : term298 s l => @lem5295207 c s l h0). Qed.
Lemma lem5295209 (c : real) (s : real -> Prop) (l : real) (h1 : (inf s) = l) : term296 s c l.
Proof. exact (EQ_MP (@lem5294972 c s l h1) (@lem5295208 s c l)). Qed.
Lemma lem5295210 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term323 s c l.
Proof. exact (conj (@lem5294959 b s l h1 h2 h3) (@lem5295209 c s l h3)). Qed.
Lemma lem5295211 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term324 s c l.
Proof. exact (@lem5294130 s c l (@lem5295210 c b s l h1 h2 h3)). Qed.
Lemma lem5295212 (c : real) (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : (term25 s c) = (real_le c l).
Proof. exact (@lem5295211 c b s l h1 h2 h3 (@lem5293355 s)). Qed.
Lemma lem5295217 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term7 s l.
Proof. exact (fun c : real => @lem5295212 c b s l h1 h2 h3). Qed.
Lemma lem5295218 (s : real -> Prop) (l : real) (h1 : term21 s l) : term22 s l.
Proof. exact (proj2 (@lem5293446 s l h1)). Qed.
Lemma lem5295219 (s : real -> Prop) (l : real) (h1 : term21 s l) : term23 s.
Proof. exact (proj1 (@lem5293446 s l h1)). Qed.
Lemma lem5295220 (s : real -> Prop) (l : real) (h1 : term22 s l) : (inf s) = l.
Proof. exact (proj2 (@lem5293447 s l h1)). Qed.
Lemma lem5295221 (s : real -> Prop) (l : real) (h1 : term22 s l) : term24 s.
Proof. exact (proj1 (@lem5293447 s l h1)). Qed.
Lemma lem5295222 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : ((inf s) = l) = (term7 s l).
Proof. exact (prop_ext (fun h4 : (inf s) = l => @lem5295217 b s l h1 h2 h3) (fun h4 : term7 s l => @lem5293449 s l h3)). Qed.
Lemma lem5295223 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term7 s l.
Proof. exact (EQ_MP (@lem5295222 b s l h1 h2 h3) (@lem5293449 s l h3)). Qed.
Lemma lem5295224 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : (term25 s b) = (term7 s l).
Proof. exact (prop_ext (fun h4 : term25 s b => @lem5295223 b s l h1 h2 h3) (fun h4 : term7 s l => @lem5293451 s b h1)). Qed.
Lemma lem5295225 (b : real) (s : real -> Prop) (l : real) (h1 : term25 s b) (h2 : term23 s) (h3 : (inf s) = l) : term7 s l.
Proof. exact (EQ_MP (@lem5295224 b s l h1 h2 h3) (@lem5293451 s b h1)). Qed.
Lemma lem5295226 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : (inf s) = l) : term7 s l.
Proof. exact (ex_elim (@lem5293450 s h1) (fun b : real => fun h0 : term150 s b => @lem5295225 b s l h0 h2 h3)). Qed.
Lemma lem5295227 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : term22 s l) : ((inf s) = l) = (term7 s l).
Proof. exact (prop_ext (fun h4 : (inf s) = l => @lem5295226 s l h1 h2 h4) (fun h4 : term7 s l => @lem5295220 s l h3)). Qed.
Lemma lem5295228 (s : real -> Prop) (l : real) (h1 : term24 s) (h2 : term23 s) (h3 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5295227 s l h1 h2 h3) (@lem5295220 s l h3)). Qed.
Lemma lem5295229 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : (term24 s) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term24 s => @lem5295228 s l h3 h1 h2) (fun h3 : term7 s l => @lem5295221 s l h2)). Qed.
Lemma lem5295230 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5295229 s l h1 h2) (@lem5295221 s l h2)). Qed.
Lemma lem5295231 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : (term23 s) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term23 s => @lem5295230 s l h1 h2) (fun h3 : term7 s l => @lem5293448 s h1)). Qed.
Lemma lem5295232 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term22 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5295231 s l h1 h2) (@lem5293448 s h1)). Qed.
Lemma lem5295233 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term21 s l) : (term22 s l) = (term7 s l).
Proof. exact (prop_ext (fun h3 : term22 s l => @lem5295232 s l h1 h3) (fun h3 : term7 s l => @lem5295218 s l h2)). Qed.
Lemma lem5295234 (s : real -> Prop) (l : real) (h1 : term23 s) (h2 : term21 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5295233 s l h1 h2) (@lem5295218 s l h2)). Qed.
Lemma lem5295235 (s : real -> Prop) (l : real) (h1 : term21 s l) : (term23 s) = (term7 s l).
Proof. exact (prop_ext (fun h2 : term23 s => @lem5295234 s l h2 h1) (fun h2 : term7 s l => @lem5295219 s l h1)). Qed.
Lemma lem5295236 (s : real -> Prop) (l : real) (h1 : term21 s l) : term7 s l.
Proof. exact (EQ_MP (@lem5295235 s l h1) (@lem5295219 s l h1)). Qed.
Lemma lem5295237 (s : real -> Prop) (l : real) : term325 s l.
Proof. exact (fun h0 : term21 s l => @lem5295236 s l h0). Qed.
Lemma lem5295238 (s : real -> Prop) (l : real) (h1 : term7 s l) : (term7 s l) = (term21 s l).
Proof. exact (prop_ext (fun h2 : term7 s l => @lem5294127 s l h1) (fun h2 : term21 s l => @lem5293445 s l h1)). Qed.
Lemma lem5295239 (s : real -> Prop) (l : real) (h1 : term7 s l) : term21 s l.
Proof. exact (EQ_MP (@lem5295238 s l h1) (@lem5293445 s l h1)). Qed.
Lemma lem5295240 (s : real -> Prop) (l : real) : term326 s l.
Proof. exact (fun h0 : term7 s l => @lem5295239 s l h0). Qed.
Lemma lem5295241 (s : real -> Prop) (l : real) : term327 s l.
Proof. exact (conj (@lem5295240 s l) (@lem5295237 s l)). Qed.
Lemma lem5295242 (s : real -> Prop) (l : real) : (term327 s l) = ((term7 s l) = (term21 s l)).
Proof. exact (@lem32 (term7 s l) (term21 s l)). Qed.
Lemma lem5295243 (s : real -> Prop) (l : real) : (term7 s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5295242 s l) (@lem5295241 s l)). Qed.
Lemma lem5295244 (s : real -> Prop) (l : real) : (has_inf s l) = (term21 s l).
Proof. exact (EQ_MP (@lem5293444 s l) (@lem5295243 s l)). Qed.
Lemma lem5295249 (s : real -> Prop) : term328 s.
Proof. exact (fun l : real => @lem5295244 s l). Qed.
Lemma lem5295254 : term329.
Proof. exact (fun s : real -> Prop => @lem5295249 s). Qed.
