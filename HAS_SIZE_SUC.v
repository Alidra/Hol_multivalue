Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_SUC_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_DELETE_spec.
Require Import FINITE_RULES_spec.
Require Import HAS_SIZE_spec.
Require Import IN_DELETE_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3864315 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3864316 {A : Type'} : term0 A.
Proof. exact (@lem3864315 A). Qed.
Lemma lem3864317 {A : Type'} (a : A) : term1 A a.
Proof. exact (@lem3864316 A a). Qed.
Lemma lem3864318 {A : Type'} (a : A) : (term1 A a) = (term2 A a).
Proof. exact (eq_refl (term1 A a)). Qed.
Lemma lem3864319 {A : Type'} (a : A) : term2 A a.
Proof. exact (EQ_MP (@lem3864318 A a) (@lem3864317 A a)). Qed.
Lemma lem3864320 {A : Type'} (s : A -> Prop) (a : A) : term3 A s a.
Proof. exact (@lem3864319 A a (@DELETE A s a)). Qed.
Lemma lem3864321 {A : Type'} (s : A -> Prop) (a : A) : (term3 A s a) = (term4 A s a).
Proof. exact (eq_refl (term3 A s a)). Qed.
Lemma lem3864322 {A : Type'} (s : A -> Prop) (a : A) : term4 A s a.
Proof. exact (EQ_MP (@lem3864321 A s a) (@lem3864320 A s a)). Qed.
Lemma lem3864324 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = (term6 A s)) : (term5 A s) = (term6 A s).
Proof. exact (h1). Qed.
Lemma lem3864325 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = (term6 A s)) : (term6 A s) = (term5 A s).
Proof. exact (SYM (@lem3864324 A s h1)). Qed.
Lemma lem3864326 {A : Type'} (s : A -> Prop) (h1 : (term6 A s) = (term5 A s)) : (term6 A s) = (term5 A s).
Proof. exact (h1). Qed.
Lemma lem3864327 {A : Type'} (s : A -> Prop) (h1 : (term6 A s) = (term5 A s)) : (term5 A s) = (term6 A s).
Proof. exact (SYM (@lem3864326 A s h1)). Qed.
Lemma lem3864328 {A : Type'} (s : A -> Prop) : ((term5 A s) = (term6 A s)) = ((term6 A s) = (term5 A s)).
Proof. exact (prop_ext (fun h1 : (term5 A s) = (term6 A s) => @lem3864325 A s h1) (fun h1 : (term6 A s) = (term5 A s) => @lem3864327 A s h1)). Qed.
Lemma lem3864329 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3864328 A s)). Qed.
Lemma lem3864330 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3864331 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3864330 A) (@lem3864329 A)). Qed.
Lemma lem3864332 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3864331 A) (@lem3216368 A)). Qed.
Lemma lem3864333 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3864332 A s). Qed.
Lemma lem3864334 {A : Type'} (s : A -> Prop) : (term11 A s) = ((term6 A s) = (term5 A s)).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem3864356 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3864357 {A : Type'} : term0 A.
Proof. exact (@lem3864356 A). Qed.
Lemma lem3864358 {A : Type'} (a : A) : term1 A a.
Proof. exact (@lem3864357 A a). Qed.
Lemma lem3864359 {A : Type'} (a : A) : (term1 A a) = (term2 A a).
Proof. exact (eq_refl (term1 A a)). Qed.
Lemma lem3864360 {A : Type'} (a : A) : term2 A a.
Proof. exact (EQ_MP (@lem3864359 A a) (@lem3864358 A a)). Qed.
Lemma lem3864361 {A : Type'} (s : A -> Prop) (a : A) : term3 A s a.
Proof. exact (@lem3864360 A a (@DELETE A s a)). Qed.
Lemma lem3864362 {A : Type'} (s : A -> Prop) (a : A) : (term3 A s a) = (term4 A s a).
Proof. exact (eq_refl (term3 A s a)). Qed.
Lemma lem3864363 {A : Type'} (s : A -> Prop) (a : A) : term4 A s a.
Proof. exact (EQ_MP (@lem3864362 A s a) (@lem3864361 A s a)). Qed.
Lemma lem3864364 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem9784 (@FINITE A s)). Qed.
Lemma lem3864365 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3864366 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem3864365 A s) (@lem3864364 A s)). Qed.
Lemma lem3864367 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3864368 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : term14 A s.
Proof. exact (h1). Qed.
Lemma lem3864369 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3864370 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem3864371 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem3864370 A s) (@lem3864369 A s)). Qed.
Lemma lem3864372 {A : Type'} (s : A -> Prop) (x : A) : term17 A s x.
Proof. exact (@lem3864371 A s x). Qed.
Lemma lem3864373 {A : Type'} (x : A) (s : A -> Prop) : (term17 A s x) = ((term18 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3864375 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (@lem9784 (s = (@EMPTY A))). Qed.
Lemma lem3864376 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem3864377 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (EQ_MP (@lem3864376 A s) (@lem3864375 A s)). Qed.
Lemma lem3864379 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term6 A s.
Proof. exact (h1). Qed.
Lemma lem3864380 {_100044 : Type'} (s : _100044 -> Prop) : term21 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3864381 {_100044 : Type'} (s : _100044 -> Prop) : (term21 _100044 s) = (term22 _100044 s).
Proof. exact (eq_refl (term21 _100044 s)). Qed.
Lemma lem3864382 {_100044 : Type'} (s : _100044 -> Prop) : term22 _100044 s.
Proof. exact (EQ_MP (@lem3864381 _100044 s) (@lem3864380 _100044 s)). Qed.
Lemma lem3864383 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term23 _100044 s n.
Proof. exact (@lem3864382 _100044 s n). Qed.
Lemma lem3864384 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term23 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term24 _100044 s n)).
Proof. exact (eq_refl (term23 _100044 s n)). Qed.
Lemma lem3864389 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term24 _100044 s n).
Proof. exact (EQ_MP (@lem3864384 _100044 s n) (@lem3864383 _100044 s n)). Qed.
Lemma lem3864390 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term24 A s n).
Proof. exact (@lem3864389 A s n). Qed.
Lemma lem3864391 {A : Type'} (s : A -> Prop) (n : nat) : (term25 A s n) = (term26 A s n).
Proof. exact (@lem3864390 A s (S n)). Qed.
Lemma lem3864396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3864397 {A : Type'} (s : A -> Prop) (n : nat) : (term27 A s n) = (term28 A s n).
Proof. exact (MK_COMB (@lem3864396) (@lem3864391 A s n)). Qed.
Lemma lem3864409 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term24 _100044 s n).
Proof. exact (EQ_MP (@lem3864384 _100044 s n) (@lem3864383 _100044 s n)). Qed.
Lemma lem3864410 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term24 A s n).
Proof. exact (@lem3864409 A s n). Qed.
Lemma lem3864411 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term29 A s a n) = (term30 A s a n).
Proof. exact (@lem3864410 A (@DELETE A s a) n). Qed.
Lemma lem3864416 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3864417 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term32 A s a n) = (term33 A s a n).
Proof. exact (MK_COMB (@lem3864416 A a s) (@lem3864411 A s a n)). Qed.
Lemma lem3864420 {A : Type'} (s : A -> Prop) (n : nat) : (term34 A s n) = (term35 A s n).
Proof. exact (fun_ext (fun a : A => @lem3864417 A s a n)). Qed.
Lemma lem3864421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864422 {A : Type'} (s : A -> Prop) (n : nat) : (term36 A s n) = (term37 A s n).
Proof. exact (MK_COMB (@lem3864421 A) (@lem3864420 A s n)). Qed.
Lemma lem3864427 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (eq_refl (term38 A s)). Qed.
Lemma lem3864428 {A : Type'} (s : A -> Prop) (n : nat) : (term39 A s n) = (term40 A s n).
Proof. exact (MK_COMB (@lem3864427 A s) (@lem3864422 A s n)). Qed.
Lemma lem3864431 {A : Type'} (s : A -> Prop) (n : nat) : ((term25 A s n) = (term39 A s n)) = ((term26 A s n) = (term40 A s n)).
Proof. exact (MK_COMB (@lem3864397 A s n) (@lem3864428 A s n)). Qed.
Lemma lem3864434 {A : Type'} (s : A -> Prop) (n : nat) : ((term26 A s n) = (term40 A s n)) = ((term25 A s n) = (term39 A s n)).
Proof. exact (SYM (@lem3864431 A s n)). Qed.
Lemma lem3864435 (n : nat) : term41 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem3864436 (n : nat) : (term41 n) = (term42 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem3864437 (n : nat) : term42 n.
Proof. exact (EQ_MP (@lem3864436 n) (@lem3864435 n)). Qed.
Lemma lem3864441 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3864442 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem3864441 n h1)). Qed.
Lemma lem3864443 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem3864444 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem3864443 n h1)). Qed.
Lemma lem3864445 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem3864442 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem3864444 n h1)). Qed.
Lemma lem3864446 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864447 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem3864446) (@lem3864445 n)). Qed.
Lemma lem3864448 (n : nat) : term43 n.
Proof. exact (EQ_MP (@lem3864447 n) (@lem3864437 n)). Qed.
Lemma lem3864449 (n : nat) : term44 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem3864451 {A : Type'} (x : A) : term45 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3864452 {A : Type'} (x : A) : (term45 A x) = (term46 A x).
Proof. exact (eq_refl (term45 A x)). Qed.
Lemma lem3864453 {A : Type'} (x : A) : term46 A x.
Proof. exact (EQ_MP (@lem3864452 A x) (@lem3864451 A x)). Qed.
Lemma lem3864454 {A : Type'} (x : A) : term47 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3864465 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem3864466 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3864483 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864484 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3864485 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864484 A) (@lem3864483 A s h1)). Qed.
Lemma lem3864487 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3864466 A) (@lem3864465 A)). Qed.
Lemma lem3864488 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = True.
Proof. exact (TRANS (@lem3864485 A s h1) (@lem3864487 A)). Qed.
Lemma lem3864489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864490 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term48 A s) = (and True).
Proof. exact (MK_COMB (@lem3864489) (@lem3864488 A s h1)). Qed.
Lemma lem3864494 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864495 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3864496 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CARD A s) = (@CARD A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864495 A) (@lem3864494 A s h1)). Qed.
Lemma lem3864498 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3864499 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@CARD A s) = (NUMERAL 0).
Proof. exact (TRANS (@lem3864496 A s h1) (@lem3864498 A)). Qed.
Lemma lem3864500 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3864501 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term49 A s) = term50.
Proof. exact (MK_COMB (@lem3864500) (@lem3864499 A s h1)). Qed.
Lemma lem3864502 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3864503 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((@CARD A s) = (S n)) = ((NUMERAL 0) = (S n)).
Proof. exact (MK_COMB (@lem3864501 A s h1) (@lem3864502 n)). Qed.
Lemma lem3864505 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem3864449 n (@lem3864448 n)). Qed.
Lemma lem3864506 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((@CARD A s) = (S n)) = False.
Proof. exact (TRANS (@lem3864503 A n s h1) (@lem3864505 n)). Qed.
Lemma lem3864507 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term26 A s n) = (True /\ False).
Proof. exact (MK_COMB (@lem3864490 A s h1) (@lem3864506 A n s h1)). Qed.
Lemma lem3864509 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3864510 : (True /\ False) = False.
Proof. exact (@lem3864509 False). Qed.
Lemma lem3864511 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term26 A s n) = False.
Proof. exact (TRANS (@lem3864507 A n s h1) (@lem3864510)). Qed.
Lemma lem3864512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3864513 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term28 A s n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3864512) (@lem3864511 A n s h1)). Qed.
Lemma lem3864519 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864520 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3864521 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@eq (A -> Prop) s) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864520 A) (@lem3864519 A s h1)). Qed.
Lemma lem3864522 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem3864523 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (s = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864521 A s h1) (@lem3864522 A)). Qed.
Lemma lem3864525 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3864526 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3864525 (A -> Prop) x). Qed.
Lemma lem3864527 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3864526 A (@EMPTY A)). Qed.
Lemma lem3864528 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (s = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem3864523 A s h1) (@lem3864527 A)). Qed.
Lemma lem3864529 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864530 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term6 A s) = (~ True).
Proof. exact (MK_COMB (@lem3864529) (@lem3864528 A s h1)). Qed.
Lemma lem3864532 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3864533 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term6 A s) = False.
Proof. exact (TRANS (@lem3864530 A s h1) (@lem3864532)). Qed.
Lemma lem3864534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864535 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term38 A s) = (and False).
Proof. exact (MK_COMB (@lem3864534) (@lem3864533 A s h1)). Qed.
Lemma lem3864543 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864544 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem3864545 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@IN A a s) = (@IN A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864544 A a) (@lem3864543 A s h1)). Qed.
Lemma lem3864547 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3864454 A x (@lem3864453 A x)). Qed.
Lemma lem3864548 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3864547 A x). Qed.
Lemma lem3864549 {A : Type'} (a : A) : (@IN A a (@EMPTY A)) = False.
Proof. exact (@lem3864548 A a). Qed.
Lemma lem3864550 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@IN A a s) = False.
Proof. exact (TRANS (@lem3864545 A a s h1) (@lem3864549 A a)). Qed.
Lemma lem3864551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3864552 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term31 A a s) = (imp False).
Proof. exact (MK_COMB (@lem3864551) (@lem3864550 A a s h1)). Qed.
Lemma lem3864556 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864557 {A : Type'} : (@DELETE A) = (@DELETE A).
Proof. exact (eq_refl (@DELETE A)). Qed.
Lemma lem3864558 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@DELETE A s) = (@DELETE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864557 A) (@lem3864556 A s h1)). Qed.
Lemma lem3864559 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3864560 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@DELETE A s a) = (@DELETE A (@EMPTY A) a).
Proof. exact (MK_COMB (@lem3864558 A s h1) (@lem3864559 A a)). Qed.
Lemma lem3864561 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3864562 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term18 A s a) = (term51 A a).
Proof. exact (MK_COMB (@lem3864561 A) (@lem3864560 A a s h1)). Qed.
Lemma lem3864563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864564 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term52 A s a) = (term53 A a).
Proof. exact (MK_COMB (@lem3864563) (@lem3864562 A a s h1)). Qed.
Lemma lem3864568 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3864569 {A : Type'} : (@DELETE A) = (@DELETE A).
Proof. exact (eq_refl (@DELETE A)). Qed.
Lemma lem3864570 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@DELETE A s) = (@DELETE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3864569 A) (@lem3864568 A s h1)). Qed.
Lemma lem3864571 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3864572 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@DELETE A s a) = (@DELETE A (@EMPTY A) a).
Proof. exact (MK_COMB (@lem3864570 A s h1) (@lem3864571 A a)). Qed.
Lemma lem3864573 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3864574 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term54 A s a) = (term55 A a).
Proof. exact (MK_COMB (@lem3864573 A) (@lem3864572 A a s h1)). Qed.
Lemma lem3864575 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3864576 {A : Type'} (a : A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term56 A s a) = (term57 A a).
Proof. exact (MK_COMB (@lem3864575) (@lem3864574 A a s h1)). Qed.
Lemma lem3864577 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3864578 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term54 A s a) = n) = ((term55 A a) = n).
Proof. exact (MK_COMB (@lem3864576 A a s h1) (@lem3864577 n)). Qed.
Lemma lem3864581 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term30 A s a n) = (term58 A a n).
Proof. exact (MK_COMB (@lem3864564 A a s h1) (@lem3864578 A a n s h1)). Qed.
Lemma lem3864584 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term33 A s a n) = (term59 A a n).
Proof. exact (MK_COMB (@lem3864552 A a s h1) (@lem3864581 A a n s h1)). Qed.
Lemma lem3864586 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3864587 {A : Type'} (a : A) (n : nat) : (term59 A a n) = True.
Proof. exact (@lem3864586 (term58 A a n)). Qed.
Lemma lem3864588 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term33 A s a n) = True.
Proof. exact (TRANS (@lem3864584 A a n s h1) (@lem3864587 A a n)). Qed.
Lemma lem3864589 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term35 A s n) = (term60 A).
Proof. exact (fun_ext (fun a : A => @lem3864588 A a n s h1)). Qed.
Lemma lem3864590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864591 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term37 A s n) = (term61 A).
Proof. exact (MK_COMB (@lem3864590 A) (@lem3864589 A n s h1)). Qed.
Lemma lem3864593 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3864594 {A : Type'} (t : Prop) : (term62 A t) = t.
Proof. exact (@lem3864593 A t). Qed.
Lemma lem3864595 {A : Type'} : (term61 A) = True.
Proof. exact (@lem3864594 A True). Qed.
Lemma lem3864596 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term37 A s n) = True.
Proof. exact (TRANS (@lem3864591 A n s h1) (@lem3864595 A)). Qed.
Lemma lem3864597 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term40 A s n) = (False /\ True).
Proof. exact (MK_COMB (@lem3864535 A s h1) (@lem3864596 A n s h1)). Qed.
Lemma lem3864599 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3864600 : (False /\ True) = False.
Proof. exact (@lem3864599 True). Qed.
Lemma lem3864601 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term40 A s n) = False.
Proof. exact (TRANS (@lem3864597 A n s h1) (@lem3864600)). Qed.
Lemma lem3864602 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term26 A s n) = (term40 A s n)) = (False = False).
Proof. exact (MK_COMB (@lem3864513 A n s h1) (@lem3864601 A n s h1)). Qed.
Lemma lem3864604 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3864605 : (False = False) = (~ False).
Proof. exact (@lem3864604 False). Qed.
Lemma lem3864607 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3864608 : (False = False) = True.
Proof. exact (TRANS (@lem3864605) (@lem3864607)). Qed.
Lemma lem3864609 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : ((term26 A s n) = (term40 A s n)) = True.
Proof. exact (TRANS (@lem3864602 A n s h1) (@lem3864608)). Qed.
Lemma lem3864610 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : True = ((term26 A s n) = (term40 A s n)).
Proof. exact (SYM (@lem3864609 A n s h1)). Qed.
Lemma lem3864611 {A : Type'} (n : nat) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term26 A s n) = (term40 A s n).
Proof. exact (EQ_MP (@lem3864610 A n s h1) (@lem0)). Qed.
Lemma lem3864655 {A : Type'} (s : A -> Prop) : term63 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem3864677 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem3864655 A s (@lem3864379 A s h1)). Qed.
Lemma lem3864678 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864679 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term6 A s) = (~ False).
Proof. exact (MK_COMB (@lem3864678) (@lem3864677 A s h1)). Qed.
Lemma lem3864681 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3864682 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term6 A s) = True.
Proof. exact (TRANS (@lem3864679 A s h1) (@lem3864681)). Qed.
Lemma lem3864683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864684 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term38 A s) = (and True).
Proof. exact (MK_COMB (@lem3864683) (@lem3864682 A s h1)). Qed.
Lemma lem3864695 {A : Type'} (s : A -> Prop) (n : nat) : (term37 A s n) = (term37 A s n).
Proof. exact (eq_refl (term37 A s n)). Qed.
Lemma lem3864696 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : (term40 A s n) = (term64 A s n).
Proof. exact (MK_COMB (@lem3864684 A s h1) (@lem3864695 A s n)). Qed.
Lemma lem3864698 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3864699 {A : Type'} (s : A -> Prop) (n : nat) : (term64 A s n) = (term37 A s n).
Proof. exact (@lem3864698 (term37 A s n)). Qed.
Lemma lem3864710 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : (term40 A s n) = (term37 A s n).
Proof. exact (TRANS (@lem3864696 A n s h1) (@lem3864699 A s n)). Qed.
Lemma lem3864711 {A : Type'} (s : A -> Prop) (n : nat) : (term28 A s n) = (term28 A s n).
Proof. exact (eq_refl (term28 A s n)). Qed.
Lemma lem3864712 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : ((term26 A s n) = (term40 A s n)) = ((term26 A s n) = (term37 A s n)).
Proof. exact (MK_COMB (@lem3864711 A s n) (@lem3864710 A n s h1)). Qed.
Lemma lem3864715 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : ((term26 A s n) = (term37 A s n)) = ((term26 A s n) = (term40 A s n)).
Proof. exact (SYM (@lem3864712 A n s h1)). Qed.
Lemma lem3864731 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3864373 A x s) (@lem3864372 A s x)). Qed.
Lemma lem3864732 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (@lem3864731 A x s). Qed.
Lemma lem3864733 {A : Type'} (a : A) (s : A -> Prop) : (term18 A s a) = (@FINITE A s).
Proof. exact (@lem3864732 A a s). Qed.
Lemma lem3864734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864735 {A : Type'} (a : A) (s : A -> Prop) : (term52 A s a) = (term48 A s).
Proof. exact (MK_COMB (@lem3864734) (@lem3864733 A a s)). Qed.
Lemma lem3864738 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = ((term54 A s a) = n).
Proof. exact (eq_refl ((term54 A s a) = n)). Qed.
Lemma lem3864739 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term30 A s a n) = (term65 A s a n).
Proof. exact (MK_COMB (@lem3864735 A a s) (@lem3864738 A s a n)). Qed.
Lemma lem3864742 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3864743 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term33 A s a n) = (term66 A s a n).
Proof. exact (MK_COMB (@lem3864742 A a s) (@lem3864739 A s a n)). Qed.
Lemma lem3864746 {A : Type'} (s : A -> Prop) (n : nat) : (term35 A s n) = (term67 A s n).
Proof. exact (fun_ext (fun a : A => @lem3864743 A s a n)). Qed.
Lemma lem3864747 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864748 {A : Type'} (s : A -> Prop) (n : nat) : (term37 A s n) = (term68 A s n).
Proof. exact (MK_COMB (@lem3864747 A) (@lem3864746 A s n)). Qed.
Lemma lem3864753 {A : Type'} (s : A -> Prop) (n : nat) : (term28 A s n) = (term28 A s n).
Proof. exact (eq_refl (term28 A s n)). Qed.
Lemma lem3864754 {A : Type'} (s : A -> Prop) (n : nat) : ((term26 A s n) = (term37 A s n)) = ((term26 A s n) = (term68 A s n)).
Proof. exact (MK_COMB (@lem3864753 A s n) (@lem3864748 A s n)). Qed.
Lemma lem3864757 {A : Type'} (s : A -> Prop) (n : nat) : ((term26 A s n) = (term68 A s n)) = ((term26 A s n) = (term37 A s n)).
Proof. exact (SYM (@lem3864754 A s n)). Qed.
Lemma lem3864777 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3864784 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3864777 A s) (@lem3864367 A s h1)). Qed.
Lemma lem3864785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864786 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term48 A s) = (and True).
Proof. exact (MK_COMB (@lem3864785) (@lem3864784 A s h1)). Qed.
Lemma lem3864789 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = (S n)) = ((@CARD A s) = (S n)).
Proof. exact (eq_refl ((@CARD A s) = (S n))). Qed.
Lemma lem3864790 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term26 A s n) = (term69 A s n).
Proof. exact (MK_COMB (@lem3864786 A s h1) (@lem3864789 A s n)). Qed.
Lemma lem3864792 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3864793 {A : Type'} (s : A -> Prop) (n : nat) : (term69 A s n) = ((@CARD A s) = (S n)).
Proof. exact (@lem3864792 ((@CARD A s) = (S n))). Qed.
Lemma lem3864796 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term26 A s n) = ((@CARD A s) = (S n)).
Proof. exact (TRANS (@lem3864790 A n s h1) (@lem3864793 A s n)). Qed.
Lemma lem3864797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3864798 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term28 A s n) = (term70 A s n).
Proof. exact (MK_COMB (@lem3864797) (@lem3864796 A n s h1)). Qed.
Lemma lem3864808 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3864777 A s) (@lem3864367 A s h1)). Qed.
Lemma lem3864809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864810 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term48 A s) = (and True).
Proof. exact (MK_COMB (@lem3864809) (@lem3864808 A s h1)). Qed.
Lemma lem3864813 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = ((term54 A s a) = n).
Proof. exact (eq_refl ((term54 A s a) = n)). Qed.
Lemma lem3864814 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term65 A s a n) = (term71 A s a n).
Proof. exact (MK_COMB (@lem3864810 A s h1) (@lem3864813 A s a n)). Qed.
Lemma lem3864816 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3864817 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term71 A s a n) = ((term54 A s a) = n).
Proof. exact (@lem3864816 ((term54 A s a) = n)). Qed.
Lemma lem3864820 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term65 A s a n) = ((term54 A s a) = n).
Proof. exact (TRANS (@lem3864814 A a n s h1) (@lem3864817 A s a n)). Qed.
Lemma lem3864821 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3864822 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term66 A s a n) = (term72 A s a n).
Proof. exact (MK_COMB (@lem3864821 A a s) (@lem3864820 A a n s h1)). Qed.
Lemma lem3864825 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term67 A s n) = (term73 A s n).
Proof. exact (fun_ext (fun a : A => @lem3864822 A a n s h1)). Qed.
Lemma lem3864826 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864827 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (term68 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem3864826 A) (@lem3864825 A n s h1)). Qed.
Lemma lem3864832 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : ((term26 A s n) = (term68 A s n)) = (((@CARD A s) = (S n)) = (term74 A s n)).
Proof. exact (MK_COMB (@lem3864798 A n s h1) (@lem3864827 A n s h1)). Qed.
Lemma lem3864835 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : (((@CARD A s) = (S n)) = (term74 A s n)) = ((term26 A s n) = (term68 A s n)).
Proof. exact (SYM (@lem3864832 A n s h1)). Qed.
Lemma lem3864836 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (@lem3216368 A s). Qed.
Lemma lem3864837 {A : Type'} (s : A -> Prop) : (term75 A s) = ((term5 A s) = (term6 A s)).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem3864839 {A : Type'} (P : A -> Prop) : term76 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem3864840 {A : Type'} (P : A -> Prop) : (term76 A P) = ((term77 A P) = (term78 A P)).
Proof. exact (eq_refl (term76 A P)). Qed.
Lemma lem3864842 {A : Type'} (s : A -> Prop) : term63 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem3864855 {A : Type'} (s : A -> Prop) : term79 A s.
Proof. exact (@lem82 (@FINITE A s)). Qed.
Lemma lem3864862 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : (@FINITE A s) = False.
Proof. exact (@lem3864855 A s (@lem3864368 A s h1)). Qed.
Lemma lem3864863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864864 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : (term48 A s) = (and False).
Proof. exact (MK_COMB (@lem3864863) (@lem3864862 A s h1)). Qed.
Lemma lem3864867 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = (S n)) = ((@CARD A s) = (S n)).
Proof. exact (eq_refl ((@CARD A s) = (S n))). Qed.
Lemma lem3864868 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term26 A s n) = (term80 A s n).
Proof. exact (MK_COMB (@lem3864864 A s h1) (@lem3864867 A s n)). Qed.
Lemma lem3864870 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3864871 {A : Type'} (s : A -> Prop) (n : nat) : (term80 A s n) = False.
Proof. exact (@lem3864870 ((@CARD A s) = (S n))). Qed.
Lemma lem3864872 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term26 A s n) = False.
Proof. exact (TRANS (@lem3864868 A n s h1) (@lem3864871 A s n)). Qed.
Lemma lem3864873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3864874 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term28 A s n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3864873) (@lem3864872 A n s h1)). Qed.
Lemma lem3864884 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : (@FINITE A s) = False.
Proof. exact (@lem3864855 A s (@lem3864368 A s h1)). Qed.
Lemma lem3864885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3864886 {A : Type'} (s : A -> Prop) (h1 : term14 A s) : (term48 A s) = (and False).
Proof. exact (MK_COMB (@lem3864885) (@lem3864884 A s h1)). Qed.
Lemma lem3864889 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = ((term54 A s a) = n).
Proof. exact (eq_refl ((term54 A s a) = n)). Qed.
Lemma lem3864890 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term65 A s a n) = (term81 A s a n).
Proof. exact (MK_COMB (@lem3864886 A s h1) (@lem3864889 A s a n)). Qed.
Lemma lem3864892 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3864893 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term81 A s a n) = False.
Proof. exact (@lem3864892 ((term54 A s a) = n)). Qed.
Lemma lem3864894 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term65 A s a n) = False.
Proof. exact (TRANS (@lem3864890 A a n s h1) (@lem3864893 A s a n)). Qed.
Lemma lem3864895 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3864896 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term14 A s) : (term66 A s a n) = (term82 A a s).
Proof. exact (MK_COMB (@lem3864895 A a s) (@lem3864894 A a n s h1)). Qed.
Lemma lem3864898 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem3864899 {A : Type'} (a : A) (s : A -> Prop) : (term82 A a s) = (term83 A a s).
Proof. exact (@lem3864898 (@IN A a s)). Qed.
Lemma lem3864900 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term14 A s) : (term66 A s a n) = (term83 A a s).
Proof. exact (TRANS (@lem3864896 A n a s h1) (@lem3864899 A a s)). Qed.
Lemma lem3864901 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term67 A s n) = (term84 A s).
Proof. exact (fun_ext (fun a : A => @lem3864900 A n a s h1)). Qed.
Lemma lem3864902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864903 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : (term68 A s n) = (term85 A s).
Proof. exact (MK_COMB (@lem3864902 A) (@lem3864901 A n s h1)). Qed.
Lemma lem3864908 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) : ((term26 A s n) = (term68 A s n)) = (False = (term85 A s)).
Proof. exact (MK_COMB (@lem3864874 A n s h1) (@lem3864903 A n s h1)). Qed.
Lemma lem3864910 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3864911 {A : Type'} (s : A -> Prop) : (False = (term85 A s)) = (term86 A s).
Proof. exact (@lem3864910 (term85 A s)). Qed.
Lemma lem3864913 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (EQ_MP (@lem3864840 A P) (@lem3864839 A P)). Qed.
Lemma lem3864914 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem3864913 A P). Qed.
Lemma lem3864915 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (@lem3864914 A (term84 A s)). Qed.
Lemma lem3864916 {A : Type'} (a : A) (s : A -> Prop) : (term89 A s a) = (term83 A a s).
Proof. exact (eq_refl (term89 A s a)). Qed.
Lemma lem3864917 {A : Type'} (s : A -> Prop) : (term90 A s) = (term84 A s).
Proof. exact (fun_ext (fun a : A => @lem3864916 A a s)). Qed.
Lemma lem3864918 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3864919 {A : Type'} (s : A -> Prop) : (term91 A s) = (term85 A s).
Proof. exact (MK_COMB (@lem3864918 A) (@lem3864917 A s)). Qed.
Lemma lem3864920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864921 {A : Type'} (s : A -> Prop) : (term87 A s) = (term86 A s).
Proof. exact (MK_COMB (@lem3864920) (@lem3864919 A s)). Qed.
Lemma lem3864922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3864923 {A : Type'} (s : A -> Prop) : (term92 A s) = (term93 A s).
Proof. exact (MK_COMB (@lem3864922) (@lem3864921 A s)). Qed.
Lemma lem3864924 {A : Type'} (a : A) (s : A -> Prop) : (term89 A s a) = (term83 A a s).
Proof. exact (eq_refl (term89 A s a)). Qed.
Lemma lem3864925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864926 {A : Type'} (a : A) (s : A -> Prop) : (term94 A s a) = (term95 A a s).
Proof. exact (MK_COMB (@lem3864925) (@lem3864924 A a s)). Qed.
Lemma lem3864927 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (fun_ext (fun a : A => @lem3864926 A a s)). Qed.
Lemma lem3864928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3864929 {A : Type'} (s : A -> Prop) : (term88 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem3864928 A) (@lem3864927 A s)). Qed.
Lemma lem3864930 {A : Type'} (s : A -> Prop) : ((term87 A s) = (term88 A s)) = ((term86 A s) = (term98 A s)).
Proof. exact (MK_COMB (@lem3864923 A s) (@lem3864929 A s)). Qed.
Lemma lem3864931 {A : Type'} (s : A -> Prop) : (term86 A s) = (term98 A s).
Proof. exact (EQ_MP (@lem3864930 A s) (@lem3864915 A s)). Qed.
Lemma lem3864937 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3864938 {A : Type'} (a : A) (s : A -> Prop) : (term95 A a s) = (@IN A a s).
Proof. exact (@lem3864937 (@IN A a s)). Qed.
Lemma lem3864939 {A : Type'} (s : A -> Prop) : (term97 A s) = (term100 A s).
Proof. exact (fun_ext (fun a : A => @lem3864938 A a s)). Qed.
Lemma lem3864940 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3864941 {A : Type'} (s : A -> Prop) : (term98 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3864940 A) (@lem3864939 A s)). Qed.
Lemma lem3864943 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (EQ_MP (@lem3864837 A s) (@lem3864836 A s)). Qed.
Lemma lem3864944 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (@lem3864943 A s). Qed.
Lemma lem3864946 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem3864842 A s (@lem3864379 A s h1)). Qed.
Lemma lem3864947 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3864948 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term6 A s) = (~ False).
Proof. exact (MK_COMB (@lem3864947) (@lem3864946 A s h1)). Qed.
Lemma lem3864950 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3864951 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term6 A s) = True.
Proof. exact (TRANS (@lem3864948 A s h1) (@lem3864950)). Qed.
Lemma lem3864952 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term5 A s) = True.
Proof. exact (TRANS (@lem3864944 A s) (@lem3864951 A s h1)). Qed.
Lemma lem3864953 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term98 A s) = True.
Proof. exact (TRANS (@lem3864941 A s) (@lem3864952 A s h1)). Qed.
Lemma lem3864954 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (term86 A s) = True.
Proof. exact (TRANS (@lem3864931 A s) (@lem3864953 A s h1)). Qed.
Lemma lem3864955 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : (False = (term85 A s)) = True.
Proof. exact (TRANS (@lem3864911 A s) (@lem3864954 A s h1)). Qed.
Lemma lem3864956 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) (h2 : term6 A s) : ((term26 A s n) = (term68 A s n)) = True.
Proof. exact (TRANS (@lem3864908 A n s h1) (@lem3864955 A s h2)). Qed.
Lemma lem3864957 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) (h2 : term6 A s) : True = ((term26 A s n) = (term68 A s n)).
Proof. exact (SYM (@lem3864956 A n s h1 h2)). Qed.
Lemma lem3864958 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term14 A s) (h2 : term6 A s) : (term26 A s n) = (term68 A s n).
Proof. exact (EQ_MP (@lem3864957 A n s h1 h2) (@lem0)). Qed.
Lemma lem3864959 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (@CARD A s) = (S n).
Proof. exact (h1). Qed.
Lemma lem3864960 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3864961 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term74 A s n.
Proof. exact (h1). Qed.
Lemma lem3864962 {A : Type'} (s : A -> Prop) : term101 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3864963 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem3864964 {A : Type'} (s : A -> Prop) : term102 A s.
Proof. exact (EQ_MP (@lem3864963 A s) (@lem3864962 A s)). Qed.
Lemma lem3864965 {A : Type'} (s : A -> Prop) (x : A) : term103 A s x.
Proof. exact (@lem3864964 A s x). Qed.
Lemma lem3864966 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (term104 A s x).
Proof. exact (eq_refl (term103 A s x)). Qed.
Lemma lem3864967 {A : Type'} (s : A -> Prop) (x : A) : term104 A s x.
Proof. exact (EQ_MP (@lem3864966 A s x) (@lem3864965 A s x)). Qed.
Lemma lem3864968 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term105 A s x y.
Proof. exact (@lem3864967 A s x y). Qed.
Lemma lem3864969 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term105 A s x y) = ((term106 A x s y) = (term107 A s x y)).
Proof. exact (eq_refl (term105 A s x y)). Qed.
Lemma lem3864971 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3864972 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem3864973 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem3864972 A s) (@lem3864971 A s)). Qed.
Lemma lem3864974 {A : Type'} (s : A -> Prop) (x : A) : term17 A s x.
Proof. exact (@lem3864973 A s x). Qed.
Lemma lem3864975 {A : Type'} (x : A) (s : A -> Prop) : (term17 A s x) = ((term18 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3864990 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3864992 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem3864999 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3864975 A x s) (@lem3864974 A s x)). Qed.
Lemma lem3865000 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (@lem3864999 A x s). Qed.
Lemma lem3865001 {A : Type'} (a : A) (s : A -> Prop) : (term18 A s a) = (@FINITE A s).
Proof. exact (@lem3865000 A a s). Qed.
Lemma lem3865003 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3864990 A s) (@lem3864367 A s h1)). Qed.
Lemma lem3865004 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term18 A s a) = True.
Proof. exact (TRANS (@lem3865001 A a s) (@lem3865003 A s h1)). Qed.
Lemma lem3865005 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3865006 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term108 A s a) = (imp True).
Proof. exact (MK_COMB (@lem3865005) (@lem3865004 A a s h1)). Qed.
Lemma lem3865010 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (EQ_MP (@lem3864969 A s x y) (@lem3864968 A s x y)). Qed.
Lemma lem3865011 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (@lem3865010 A s x y). Qed.
Lemma lem3865012 {A : Type'} (s : A -> Prop) (a : A) : (term109 A s a) = (term110 A s a).
Proof. exact (@lem3865011 A s a a). Qed.
Lemma lem3865016 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem3864992 A a s) (@lem3864960 A a s h1)). Qed.
Lemma lem3865017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3865018 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A a s) = (and True).
Proof. exact (MK_COMB (@lem3865017) (@lem3865016 A a s h1)). Qed.
Lemma lem3865020 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3865021 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3865020 A x). Qed.
Lemma lem3865022 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem3865021 A a). Qed.
Lemma lem3865023 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3865024 {A : Type'} (a : A) : (term112 A a) = (~ True).
Proof. exact (MK_COMB (@lem3865023) (@lem3865022 A a)). Qed.
Lemma lem3865026 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3865027 {A : Type'} (a : A) : (term112 A a) = False.
Proof. exact (TRANS (@lem3865024 A a) (@lem3865026)). Qed.
Lemma lem3865028 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term110 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem3865018 A a s h1) (@lem3865027 A a)). Qed.
Lemma lem3865030 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3865031 : (True /\ False) = False.
Proof. exact (@lem3865030 False). Qed.
Lemma lem3865032 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term110 A s a) = False.
Proof. exact (TRANS (@lem3865028 A a s h1) (@lem3865031)). Qed.
Lemma lem3865033 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term109 A s a) = False.
Proof. exact (TRANS (@lem3865012 A s a) (@lem3865032 A a s h1)). Qed.
Lemma lem3865034 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem3865035 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term113 A s a) = (@COND nat False).
Proof. exact (MK_COMB (@lem3865034) (@lem3865033 A a s h1)). Qed.
Lemma lem3865036 {A : Type'} (s : A -> Prop) (a : A) : (term54 A s a) = (term54 A s a).
Proof. exact (eq_refl (term54 A s a)). Qed.
Lemma lem3865037 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term114 A s a) = (term115 A s a).
Proof. exact (MK_COMB (@lem3865035 A a s h1) (@lem3865036 A s a)). Qed.
Lemma lem3865038 {A : Type'} (s : A -> Prop) (a : A) : (term116 A s a) = (term116 A s a).
Proof. exact (eq_refl (term116 A s a)). Qed.
Lemma lem3865039 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term117 A s a) = (term118 A s a).
Proof. exact (MK_COMB (@lem3865037 A a s h1) (@lem3865038 A s a)). Qed.
Lemma lem3865041 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3865042 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3865041 nat t1 t2). Qed.
Lemma lem3865043 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term116 A s a).
Proof. exact (@lem3865042 (term54 A s a) (term116 A s a)). Qed.
Lemma lem3865044 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term117 A s a) = (term116 A s a).
Proof. exact (TRANS (@lem3865039 A a s h1) (@lem3865043 A s a)). Qed.
Lemma lem3865045 {A : Type'} (s : A -> Prop) (a : A) : (term119 A s a) = (term119 A s a).
Proof. exact (eq_refl (term119 A s a)). Qed.
Lemma lem3865046 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : ((term120 A s a) = (term117 A s a)) = ((term120 A s a) = (term116 A s a)).
Proof. exact (MK_COMB (@lem3865045 A s a) (@lem3865044 A a s h1)). Qed.
Lemma lem3865049 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term4 A s a) = (term121 A s a).
Proof. exact (MK_COMB (@lem3865006 A a s h1) (@lem3865046 A a s h2)). Qed.
Lemma lem3865051 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3865052 {A : Type'} (s : A -> Prop) (a : A) : (term121 A s a) = ((term120 A s a) = (term116 A s a)).
Proof. exact (@lem3865051 ((term120 A s a) = (term116 A s a))). Qed.
Lemma lem3865055 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term4 A s a) = ((term120 A s a) = (term116 A s a)).
Proof. exact (TRANS (@lem3865049 A a s h1 h2) (@lem3865052 A s a)). Qed.
Lemma lem3865056 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3865057 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term122 A s a) = (term123 A s a).
Proof. exact (MK_COMB (@lem3865056) (@lem3865055 A a s h1 h2)). Qed.
Lemma lem3865060 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = ((term54 A s a) = n).
Proof. exact (eq_refl ((term54 A s a) = n)). Qed.
Lemma lem3865061 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term124 A s a n) = (term125 A s a n).
Proof. exact (MK_COMB (@lem3865057 A a s h1 h2) (@lem3865060 A s a n)). Qed.
Lemma lem3865066 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term125 A s a n) = (term124 A s a n).
Proof. exact (SYM (@lem3865061 A n a s h1 h2)). Qed.
Lemma lem3865067 {A : Type'} (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term126 A s a) = s.
Proof. exact (h1). Qed.
Lemma lem3865068 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term127 A s a n) = (term127 A s a n).
Proof. exact (eq_refl (term127 A s a n)). Qed.
Lemma lem3865069 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term128 A n s a) = (term129 A a n s).
Proof. exact (MK_COMB (@lem3865068 A s a n) (@lem3865067 A a s h1)). Qed.
Lemma lem3865070 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term129 A a n s) = (term130 A s a n).
Proof. exact (eq_refl (term129 A a n s)). Qed.
Lemma lem3865071 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term131 A n s a) = (term131 A n s a).
Proof. exact (eq_refl (term131 A n s a)). Qed.
Lemma lem3865072 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term128 A n s a) = (term129 A a n s)) = ((term128 A n s a) = (term130 A s a n)).
Proof. exact (MK_COMB (@lem3865071 A n s a) (@lem3865070 A s a n)). Qed.
Lemma lem3865073 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term128 A n s a) = (term125 A s a n).
Proof. exact (eq_refl (term128 A n s a)). Qed.
Lemma lem3865074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3865075 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term131 A n s a) = (term132 A s a n).
Proof. exact (MK_COMB (@lem3865074) (@lem3865073 A s a n)). Qed.
Lemma lem3865076 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term130 A s a n) = (term130 A s a n).
Proof. exact (eq_refl (term130 A s a n)). Qed.
Lemma lem3865077 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term128 A n s a) = (term130 A s a n)) = ((term125 A s a n) = (term130 A s a n)).
Proof. exact (MK_COMB (@lem3865075 A s a n) (@lem3865076 A s a n)). Qed.
Lemma lem3865078 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term128 A n s a) = (term129 A a n s)) = ((term125 A s a n) = (term130 A s a n)).
Proof. exact (TRANS (@lem3865072 A s a n) (@lem3865077 A s a n)). Qed.
Lemma lem3865079 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term125 A s a n) = (term130 A s a n).
Proof. exact (EQ_MP (@lem3865078 A s a n) (@lem3865069 A n a s h1)). Qed.
Lemma lem3865080 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term130 A s a n) = (term125 A s a n).
Proof. exact (SYM (@lem3865079 A n a s h1)). Qed.
Lemma lem3865086 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3865087 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (@lem3865086 A s t). Qed.
Lemma lem3865088 {A : Type'} (a : A) (s : A -> Prop) : ((term126 A s a) = s) = (term134 A a s).
Proof. exact (@lem3865087 A (term126 A s a) s). Qed.
Lemma lem3865097 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3865098 {A : Type'} (a : A) (s : A -> Prop) : (term135 A a s) = (term136 A a s).
Proof. exact (MK_COMB (@lem3865097 A a s) (@lem3865088 A a s)). Qed.
Lemma lem3865101 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term135 A a s).
Proof. exact (SYM (@lem3865098 A a s)). Qed.
Lemma lem3865105 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3865106 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3865105 A P x). Qed.
Lemma lem3865107 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3865106 A s a). Qed.
Lemma lem3865108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3865109 {A : Type'} (s : A -> Prop) (a : A) : (term31 A a s) = (term137 A s a).
Proof. exact (MK_COMB (@lem3865108) (@lem3865107 A s a)). Qed.
Lemma lem3865117 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term138 A x y s) = (term139 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3865118 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term138 A x y s) = (term139 A y x s).
Proof. exact (@lem3865117 A y x s). Qed.
Lemma lem3865119 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term140 A x s a) = (term141 A x s a).
Proof. exact (@lem3865118 A a x (@DELETE A s a)). Qed.
Lemma lem3865125 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3865126 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (@lem3865125 A s x y). Qed.
Lemma lem3865127 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term106 A x s a) = (term107 A s x a).
Proof. exact (@lem3865126 A s x a). Qed.
Lemma lem3865131 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3865132 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3865131 A P x). Qed.
Lemma lem3865133 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3865132 A s x). Qed.
Lemma lem3865134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3865135 {A : Type'} (s : A -> Prop) (x : A) : (term111 A x s) = (term142 A s x).
Proof. exact (MK_COMB (@lem3865134) (@lem3865133 A s x)). Qed.
Lemma lem3865138 {A : Type'} (x : A) (a : A) : (term143 A x a) = (term143 A x a).
Proof. exact (eq_refl (term143 A x a)). Qed.
Lemma lem3865139 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term107 A s x a) = (term144 A s x a).
Proof. exact (MK_COMB (@lem3865135 A s x) (@lem3865138 A x a)). Qed.
Lemma lem3865142 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term106 A x s a) = (term144 A s x a).
Proof. exact (TRANS (@lem3865127 A s x a) (@lem3865139 A s x a)). Qed.
Lemma lem3865143 {A : Type'} (x : A) (a : A) : (term145 A x a) = (term145 A x a).
Proof. exact (eq_refl (term145 A x a)). Qed.
Lemma lem3865144 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term141 A x s a) = (term146 A s x a).
Proof. exact (MK_COMB (@lem3865143 A x a) (@lem3865142 A s x a)). Qed.
Lemma lem3865147 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term140 A x s a) = (term146 A s x a).
Proof. exact (TRANS (@lem3865119 A x s a) (@lem3865144 A s x a)). Qed.
Lemma lem3865148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3865149 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term147 A x s a) = (term148 A s x a).
Proof. exact (MK_COMB (@lem3865148) (@lem3865147 A s x a)). Qed.
Lemma lem3865151 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3865152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3865151 A P x). Qed.
Lemma lem3865153 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3865152 A s x). Qed.
Lemma lem3865154 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term140 A x s a) = (@IN A x s)) = ((term146 A s x a) = (s x)).
Proof. exact (MK_COMB (@lem3865149 A s x a) (@lem3865153 A s x)). Qed.
Lemma lem3865157 {A : Type'} (a : A) (s : A -> Prop) : (term149 A a s) = (term150 A a s).
Proof. exact (fun_ext (fun x : A => @lem3865154 A a s x)). Qed.
Lemma lem3865158 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865159 {A : Type'} (a : A) (s : A -> Prop) : (term134 A a s) = (term151 A a s).
Proof. exact (MK_COMB (@lem3865158 A) (@lem3865157 A a s)). Qed.
Lemma lem3865164 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term152 A a s).
Proof. exact (MK_COMB (@lem3865109 A s a) (@lem3865159 A a s)). Qed.
Lemma lem3865167 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term136 A a s).
Proof. exact (SYM (@lem3865164 A a s)). Qed.
Lemma lem3865169 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3865170 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term154 A a s).
Proof. exact (@lem3865169 (term152 A a s)). Qed.
Lemma lem3865171 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term152 A a s).
Proof. exact (SYM (@lem3865170 A a s)). Qed.
Lemma lem3865172 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : term155 A a s.
Proof. exact (h1). Qed.
Lemma lem3865175 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term154 A a s.
Proof. exact (h1). Qed.
Lemma lem3865176 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (fun h0 : term154 A a s => @lem3865175 A a s h0). Qed.
Lemma lem3865177 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (h1). Qed.
Lemma lem3865178 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term154 A a s.
Proof. exact (h1). Qed.
Lemma lem3865179 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) (h2 : term156 A a s) : term154 A a s.
Proof. exact (@lem3865177 A a s h2 (@lem3865178 A a s h1)). Qed.
Lemma lem3865180 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term157 A a s.
Proof. exact (fun h0 : term156 A a s => @lem3865179 A a s h1 h0). Qed.
Lemma lem3865181 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (h1). Qed.
Lemma lem3865182 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) (h2 : term156 A a s) : term154 A a s.
Proof. exact (@lem3865180 A a s h1 (@lem3865181 A a s h2)). Qed.
Lemma lem3865183 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (fun h0 : term154 A a s => @lem3865182 A a s h0 h1). Qed.
Lemma lem3865184 {A : Type'} (a : A) (s : A -> Prop) : term158 A a s.
Proof. exact (fun h0 : term156 A a s => @lem3865183 A a s h0). Qed.
Lemma lem3865187 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (@lem3865184 A a s (@lem3865176 A a s)). Qed.
Lemma lem3865188 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (@lem3865187 A a s). Qed.
Lemma lem3865198 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3865199 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term159 A a s).
Proof. exact (@lem3865198 (term155 A a s)). Qed.
Lemma lem3865201 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3865202 {A : Type'} (a : A) (s : A -> Prop) : (term159 A a s) = (term152 A a s).
Proof. exact (@lem3865201 (term152 A a s)). Qed.
Lemma lem3865205 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term152 A a s).
Proof. exact (TRANS (@lem3865199 A a s) (@lem3865202 A a s)). Qed.
Lemma lem3865214 {A : Type'} (s : A -> Prop) : (term160 A s) = (term161 A s).
Proof. exact (fun_ext (fun a : A => @lem3865205 A a s)). Qed.
Lemma lem3865215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865216 {A : Type'} (s : A -> Prop) : (term162 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem3865215 A) (@lem3865214 A s)). Qed.
Lemma lem3865221 {A : Type'} : (term164 A) = (term165 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3865216 A s)). Qed.
Lemma lem3865222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3865231 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (MK_COMB (@lem3865222 A) (@lem3865221 A)). Qed.
Lemma lem3865246 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term146 A s x a) = (s x)) = ((term146 A s x a) = (s x)).
Proof. exact (eq_refl ((term146 A s x a) = (s x))). Qed.
Lemma lem3865247 {A : Type'} (a : A) (s : A -> Prop) : (term150 A a s) = (term150 A a s).
Proof. exact (fun_ext (fun x : A => @lem3865246 A a s x)). Qed.
Lemma lem3865248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865249 {A : Type'} (a : A) (s : A -> Prop) : (term151 A a s) = (term151 A a s).
Proof. exact (MK_COMB (@lem3865248 A) (@lem3865247 A a s)). Qed.
Lemma lem3865252 {A : Type'} (s : A -> Prop) (a : A) : (term137 A s a) = (term137 A s a).
Proof. exact (eq_refl (term137 A s a)). Qed.
Lemma lem3865253 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term152 A a s).
Proof. exact (MK_COMB (@lem3865252 A s a) (@lem3865249 A a s)). Qed.
Lemma lem3865254 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun a : A => @lem3865253 A a s)). Qed.
Lemma lem3865255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865256 {A : Type'} (s : A -> Prop) : (term163 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem3865255 A) (@lem3865254 A s)). Qed.
Lemma lem3865257 {A : Type'} : (term165 A) = (term165 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3865256 A s)). Qed.
Lemma lem3865258 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3865259 {A : Type'} : (term167 A) = (term167 A).
Proof. exact (MK_COMB (@lem3865258 A) (@lem3865257 A)). Qed.
Lemma lem3865286 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (TRANS (@lem3865231 A) (@lem3865259 A)). Qed.
Lemma lem3865287 {A : Type'} : (term167 A) = (term166 A).
Proof. exact (SYM (@lem3865286 A)). Qed.
Lemma lem3865290 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3865291 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term146 A s x a) = (s x)) = (term168 A a s x).
Proof. exact (@lem3865290 ((term146 A s x a) = (s x))). Qed.
Lemma lem3865292 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term168 A a s x) = ((term146 A s x a) = (s x)).
Proof. exact (SYM (@lem3865291 A a s x)). Qed.
Lemma lem3865293 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term169 A a s x) : term169 A a s x.
Proof. exact (h1). Qed.
Lemma lem3865299 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865307 {A : Type'} (x : A) (a : A) : (term170 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem3865309 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (term171 A s x).
Proof. exact (eq_refl (term171 A s x)). Qed.
Lemma lem3865310 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term172 A s x a) = (term173 A s x a).
Proof. exact (MK_COMB (@lem3865309 A s x) (@lem3865307 A x a)). Qed.
Lemma lem3865311 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term174 A s x a) = (term172 A s x a).
Proof. exact (@lem17045 (s x) (term143 A x a)). Qed.
Lemma lem3865312 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term174 A s x a) = (term173 A s x a).
Proof. exact (TRANS (@lem3865311 A s x a) (@lem3865310 A s x a)). Qed.
Lemma lem3865317 {A : Type'} (x : A) (a : A) : (term175 A x a) = (term175 A x a).
Proof. exact (eq_refl (term175 A x a)). Qed.
Lemma lem3865318 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term176 A s x a) = (term177 A s x a).
Proof. exact (MK_COMB (@lem3865317 A x a) (@lem3865312 A s x a)). Qed.
Lemma lem3865319 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term178 A s x a) = (term176 A s x a).
Proof. exact (@lem17160 (x = a) (term144 A s x a)). Qed.
Lemma lem3865320 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term178 A s x a) = (term177 A s x a).
Proof. exact (TRANS (@lem3865319 A s x a) (@lem3865318 A s x a)). Qed.
Lemma lem3865325 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3865326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3865327 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term179 A s x a) = (term180 A s x a).
Proof. exact (MK_COMB (@lem3865326) (@lem3865320 A s x a)). Qed.
Lemma lem3865328 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term181 A a s x) = (term182 A a s x).
Proof. exact (MK_COMB (@lem3865327 A s x a) (@lem3865325 A s x)). Qed.
Lemma lem3865333 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term183 A a s x) = (term183 A a s x).
Proof. exact (eq_refl (term183 A a s x)). Qed.
Lemma lem3865334 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term184 A a s x) = (term185 A a s x).
Proof. exact (MK_COMB (@lem3865333 A a s x) (@lem3865328 A a s x)). Qed.
Lemma lem3865335 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term169 A a s x) = (term184 A a s x).
Proof. exact (@lem17646 (term146 A s x a) (s x)). Qed.
Lemma lem3865340 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term169 A a s x) = (term185 A a s x).
Proof. exact (TRANS (@lem3865335 A a s x) (@lem3865334 A a s x)). Qed.
Lemma lem3865345 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865407 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term169 A a s x) : term185 A a s x.
Proof. exact (EQ_MP (@lem3865340 A a s x) (@lem3865293 A a s x h1)). Qed.
Lemma lem3865408 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term186 A a s x.
Proof. exact (h1). Qed.
Lemma lem3865409 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term182 A a s x.
Proof. exact (h1). Qed.
Lemma lem3865411 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term146 A s x a.
Proof. exact (proj1 (@lem3865408 A a s x h1)). Qed.
Lemma lem3865413 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : term144 A s x a.
Proof. exact (h1). Qed.
Lemma lem3865417 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term177 A s x a.
Proof. exact (proj1 (@lem3865409 A a s x h1)). Qed.
Lemma lem3865418 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term173 A s x a.
Proof. exact (proj2 (@lem3865417 A a s x h1)). Qed.
Lemma lem3865425 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865433 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3865465 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term187 A s x.
Proof. exact (h1). Qed.
Lemma lem3865481 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3865483 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865485 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term187 A s x.
Proof. exact (proj2 (@lem3865408 A a s x h1)). Qed.
Lemma lem3865487 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3865491 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term187 A s x.
Proof. exact (proj2 (@lem3865408 A a s x h1)). Qed.
Lemma lem3865503 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term187 A s x.
Proof. exact (h1). Qed.
Lemma lem3865509 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term143 A x a.
Proof. exact (proj1 (@lem3865417 A a s x h1)). Qed.
Lemma lem3865511 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3865539 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865540 {A : Type'} (s : A -> Prop) : (term188 A s) = (term188 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem3865541 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term189 A s x) = (term189 A s a).
Proof. exact (MK_COMB (@lem3865540 A s) (@lem3865487 A x a h1)). Qed.
Lemma lem3865542 {A : Type'} (s : A -> Prop) (a : A) : (term189 A s a) = (term187 A s a).
Proof. exact (eq_refl (term189 A s a)). Qed.
Lemma lem3865543 {A : Type'} (s : A -> Prop) (x : A) : (term190 A s x) = (term190 A s x).
Proof. exact (eq_refl (term190 A s x)). Qed.
Lemma lem3865544 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term189 A s a)) = ((term189 A s x) = (term187 A s a)).
Proof. exact (MK_COMB (@lem3865543 A s x) (@lem3865542 A s a)). Qed.
Lemma lem3865545 {A : Type'} (s : A -> Prop) (x : A) : (term189 A s x) = (term187 A s x).
Proof. exact (eq_refl (term189 A s x)). Qed.
Lemma lem3865546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3865547 {A : Type'} (s : A -> Prop) (x : A) : (term190 A s x) = (term191 A s x).
Proof. exact (MK_COMB (@lem3865546) (@lem3865545 A s x)). Qed.
Lemma lem3865548 {A : Type'} (s : A -> Prop) (a : A) : (term187 A s a) = (term187 A s a).
Proof. exact (eq_refl (term187 A s a)). Qed.
Lemma lem3865549 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term187 A s a)) = ((term187 A s x) = (term187 A s a)).
Proof. exact (MK_COMB (@lem3865547 A s x) (@lem3865548 A s a)). Qed.
Lemma lem3865550 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term189 A s a)) = ((term187 A s x) = (term187 A s a)).
Proof. exact (TRANS (@lem3865544 A x s a) (@lem3865549 A x s a)). Qed.
Lemma lem3865551 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term187 A s x) = (term187 A s a).
Proof. exact (EQ_MP (@lem3865550 A x s a) (@lem3865541 A s x a h1)). Qed.
Lemma lem3865552 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term186 A a s x) (h2 : x = a) : term187 A s a.
Proof. exact (EQ_MP (@lem3865551 A s x a h2) (@lem3865485 A a s x h1)). Qed.
Lemma lem3865594 {A : Type'} (a : A) : (term192 A a) = (term192 A a).
Proof. exact (eq_refl (term192 A a)). Qed.
Lemma lem3865595 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term193 A a x) = (term194 A a).
Proof. exact (MK_COMB (@lem3865594 A a) (@lem3865511 A x a h1)). Qed.
Lemma lem3865596 {A : Type'} (a : A) : (term194 A a) = (term112 A a).
Proof. exact (eq_refl (term194 A a)). Qed.
Lemma lem3865597 {A : Type'} (a : A) (x : A) : (term195 A a x) = (term195 A a x).
Proof. exact (eq_refl (term195 A a x)). Qed.
Lemma lem3865598 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term194 A a)) = ((term193 A a x) = (term112 A a)).
Proof. exact (MK_COMB (@lem3865597 A a x) (@lem3865596 A a)). Qed.
Lemma lem3865599 {A : Type'} (x : A) (a : A) : (term193 A a x) = (term143 A x a).
Proof. exact (eq_refl (term193 A a x)). Qed.
Lemma lem3865600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3865601 {A : Type'} (x : A) (a : A) : (term195 A a x) = (term196 A x a).
Proof. exact (MK_COMB (@lem3865600) (@lem3865599 A x a)). Qed.
Lemma lem3865602 {A : Type'} (a : A) : (term112 A a) = (term112 A a).
Proof. exact (eq_refl (term112 A a)). Qed.
Lemma lem3865603 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term112 A a)) = ((term143 A x a) = (term112 A a)).
Proof. exact (MK_COMB (@lem3865601 A x a) (@lem3865602 A a)). Qed.
Lemma lem3865604 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term194 A a)) = ((term143 A x a) = (term112 A a)).
Proof. exact (TRANS (@lem3865598 A x a) (@lem3865603 A x a)). Qed.
Lemma lem3865605 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term143 A x a) = (term112 A a).
Proof. exact (EQ_MP (@lem3865604 A x a) (@lem3865595 A x a h1)). Qed.
Lemma lem3865606 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term112 A a.
Proof. exact (EQ_MP (@lem3865605 A x a h2) (@lem3865509 A a s x h1)). Qed.
Lemma lem3865608 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3865609 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term197 A s a.
Proof. exact (fun h0 : term187 A s a => @lem3865608 A s a h1). Qed.
Lemma lem3865611 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865612 {A : Type'} (s : A -> Prop) (a : A) : (term197 A s a) = (s a).
Proof. exact (@lem3865611 (s a)). Qed.
Lemma lem3865613 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem3865612 A s a) (@lem3865609 A s a h1)). Qed.
Lemma lem3865616 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3865618 {A : Type'} (s : A -> Prop) (a : A) : (term187 A s a) = (term199 A s a).
Proof. exact (@lem3865616 (s a)). Qed.
Lemma lem3865621 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term186 A a s x) (h2 : x = a) : term199 A s a.
Proof. exact (EQ_MP (@lem3865618 A s a) (@lem3865552 A s x a h1 h2)). Qed.
Lemma lem3865624 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (@lem3865621 A s x a h2 h3 (@lem3865613 A s a h1)). Qed.
Lemma lem3865625 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : term200.
Proof. exact (fun h0 : ~ False => @lem3865624 A s x a h1 h2 h3). Qed.
Lemma lem3865627 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865628 : term200 = False.
Proof. exact (@lem3865627 False). Qed.
Lemma lem3865629 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865628) (@lem3865625 A s x a h1 h2 h3)). Qed.
Lemma lem3865645 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : s x.
Proof. exact (proj1 (@lem3865413 A s x a h1)). Qed.
Lemma lem3865646 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : term197 A s x.
Proof. exact (fun h0 : term187 A s x => @lem3865645 A s x a h1). Qed.
Lemma lem3865648 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865649 {A : Type'} (s : A -> Prop) (x : A) : (term197 A s x) = (s x).
Proof. exact (@lem3865648 (s x)). Qed.
Lemma lem3865650 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : s x.
Proof. exact (EQ_MP (@lem3865649 A s x) (@lem3865646 A s x a h1)). Qed.
Lemma lem3865653 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3865655 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term199 A s x).
Proof. exact (@lem3865653 (s x)). Qed.
Lemma lem3865658 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term199 A s x.
Proof. exact (EQ_MP (@lem3865655 A s x) (@lem3865491 A a s x h1)). Qed.
Lemma lem3865661 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : False.
Proof. exact (@lem3865658 A a s x h2 (@lem3865650 A s x a h1)). Qed.
Lemma lem3865662 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : term200.
Proof. exact (fun h0 : ~ False => @lem3865661 A a s x h1 h2). Qed.
Lemma lem3865664 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865665 : term200 = False.
Proof. exact (@lem3865664 False). Qed.
Lemma lem3865666 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : False.
Proof. exact (EQ_MP (@lem3865665) (@lem3865662 A a s x h1 h2)). Qed.
Lemma lem3865682 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : s x.
Proof. exact (proj2 (@lem3865409 A a s x h1)). Qed.
Lemma lem3865683 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term197 A s x.
Proof. exact (fun h0 : term187 A s x => @lem3865682 A a s x h1). Qed.
Lemma lem3865685 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865686 {A : Type'} (s : A -> Prop) (x : A) : (term197 A s x) = (s x).
Proof. exact (@lem3865685 (s x)). Qed.
Lemma lem3865687 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : s x.
Proof. exact (EQ_MP (@lem3865686 A s x) (@lem3865683 A a s x h1)). Qed.
Lemma lem3865690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3865692 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term199 A s x).
Proof. exact (@lem3865690 (s x)). Qed.
Lemma lem3865695 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term199 A s x.
Proof. exact (EQ_MP (@lem3865692 A s x) (@lem3865503 A s x h1)). Qed.
Lemma lem3865698 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (@lem3865695 A s x h1 (@lem3865687 A a s x h2)). Qed.
Lemma lem3865699 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : term200.
Proof. exact (fun h0 : ~ False => @lem3865698 A a s x h1 h2). Qed.
Lemma lem3865701 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865702 : term200 = False.
Proof. exact (@lem3865701 False). Qed.
Lemma lem3865703 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3865702) (@lem3865699 A a s x h1 h2)). Qed.
Lemma lem3865719 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3865720 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3865719 A x). Qed.
Lemma lem3865721 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3865720 A a). Qed.
Lemma lem3865722 {A : Type'} (a : A) : term201 A a.
Proof. exact (fun h0 : term112 A a => @lem3865721 A a). Qed.
Lemma lem3865724 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865725 {A : Type'} (a : A) : (term201 A a) = (a = a).
Proof. exact (@lem3865724 (a = a)). Qed.
Lemma lem3865726 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3865725 A a) (@lem3865722 A a)). Qed.
Lemma lem3865729 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3865731 {A : Type'} (a : A) : (term112 A a) = (term202 A a).
Proof. exact (@lem3865729 (a = a)). Qed.
Lemma lem3865734 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term202 A a.
Proof. exact (EQ_MP (@lem3865731 A a) (@lem3865606 A s x a h1 h2)). Qed.
Lemma lem3865737 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (@lem3865734 A s x a h1 h2 (@lem3865726 A a)). Qed.
Lemma lem3865738 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term200.
Proof. exact (fun h0 : ~ False => @lem3865737 A s x a h1 h2). Qed.
Lemma lem3865740 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3865741 : term200 = False.
Proof. exact (@lem3865740 False). Qed.
Lemma lem3865743 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3865741) (@lem3865738 A s x a h1 h2)). Qed.
Lemma lem3865744 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3865629 A s x a h1 h2 h3) (fun h4 : False => @lem3865539 A s a h1)). Qed.
Lemma lem3865746 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865744 A s x a h1 h2 h3) (@lem3865539 A s a h1)). Qed.
Lemma lem3865747 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3865743 A s x a h1 h2) (fun h3 : False => @lem3865511 A x a h2)). Qed.
Lemma lem3865748 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3865747 A s x a h1 h2) (@lem3865511 A x a h2)). Qed.
Lemma lem3865749 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3865703 A a s x h1 h2) (fun h3 : False => @lem3865503 A s x h1)). Qed.
Lemma lem3865750 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3865749 A a s x h1 h2) (@lem3865503 A s x h1)). Qed.
Lemma lem3865751 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3865746 A s x a h1 h2 h3) (fun h4 : False => @lem3865487 A x a h3)). Qed.
Lemma lem3865752 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865751 A s x a h1 h2 h3) (@lem3865487 A x a h3)). Qed.
Lemma lem3865753 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3865752 A s x a h1 h2 h3) (fun h4 : False => @lem3865483 A s a h1)). Qed.
Lemma lem3865754 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865753 A s x a h1 h2 h3) (@lem3865483 A s a h1)). Qed.
Lemma lem3865755 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3865748 A s x a h1 h2) (fun h3 : False => @lem3865481 A x a h2)). Qed.
Lemma lem3865756 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3865755 A s x a h1 h2) (@lem3865481 A x a h2)). Qed.
Lemma lem3865757 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3865750 A a s x h1 h2) (fun h3 : False => @lem3865465 A s x h1)). Qed.
Lemma lem3865758 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3865757 A a s x h1 h2) (@lem3865465 A s x h1)). Qed.
Lemma lem3865759 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3865754 A s x a h1 h2 h3) (fun h4 : False => @lem3865433 A x a h3)). Qed.
Lemma lem3865760 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865759 A s x a h1 h2 h3) (@lem3865433 A x a h3)). Qed.
Lemma lem3865761 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3865760 A s x a h1 h2 h3) (fun h4 : False => @lem3865425 A s a h1)). Qed.
Lemma lem3865762 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865761 A s x a h1 h2 h3) (@lem3865425 A s a h1)). Qed.
Lemma lem3865763 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3865756 A s x a h1 h2) (fun h3 : False => @lem3865481 A x a h2)). Qed.
Lemma lem3865764 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3865763 A s x a h1 h2) (@lem3865481 A x a h2)). Qed.
Lemma lem3865765 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3865758 A a s x h1 h2) (fun h3 : False => @lem3865465 A s x h1)). Qed.
Lemma lem3865766 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3865765 A a s x h1 h2) (@lem3865465 A s x h1)). Qed.
Lemma lem3865767 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3865762 A s x a h1 h2 h3) (fun h4 : False => @lem3865433 A x a h3)). Qed.
Lemma lem3865768 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865767 A s x a h1 h2 h3) (@lem3865433 A x a h3)). Qed.
Lemma lem3865769 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3865768 A s x a h1 h2 h3) (fun h4 : False => @lem3865425 A s a h1)). Qed.
Lemma lem3865770 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3865769 A s x a h1 h2 h3) (@lem3865425 A s a h1)). Qed.
Lemma lem3865771 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : False.
Proof. exact (or_elim (@lem3865418 A a s x h1) (fun h0 : term187 A s x => @lem3865766 A a s x h0 h1) (fun h0 : x = a => @lem3865764 A s x a h1 h0)). Qed.
Lemma lem3865772 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : s a) (h2 : term186 A a s x) : False.
Proof. exact (or_elim (@lem3865411 A a s x h2) (fun h0 : x = a => @lem3865770 A s x a h1 h2 h0) (fun h0 : term144 A s x a => @lem3865666 A a s x h0 h2)). Qed.
Lemma lem3865773 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (or_elim (@lem3865407 A a s x h1) (fun h0 : term186 A a s x => @lem3865772 A a s x h2 h0) (fun h0 : term182 A a s x => @lem3865771 A a s x h0)). Qed.
Lemma lem3865774 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3865773 A x s a h1 h2) (fun h3 : False => @lem3865345 A s a h2)). Qed.
Lemma lem3865775 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3865774 A x s a h1 h2) (@lem3865345 A s a h2)). Qed.
Lemma lem3865776 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3865775 A x s a h1 h2) (fun h3 : False => @lem3865299 A s a h2)). Qed.
Lemma lem3865777 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3865776 A x s a h1 h2) (@lem3865299 A s a h2)). Qed.
Lemma lem3865778 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (term169 A a s x) = False.
Proof. exact (prop_ext (fun h3 : term169 A a s x => @lem3865777 A x s a h1 h2) (fun h3 : False => @lem3865293 A a s x h1)). Qed.
Lemma lem3865779 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3865778 A x s a h1 h2) (@lem3865293 A a s x h1)). Qed.
Lemma lem3865780 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : term168 A a s x.
Proof. exact (fun h0 : term169 A a s x => @lem3865779 A x s a h0 h1). Qed.
Lemma lem3865781 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : (term146 A s x a) = (s x).
Proof. exact (EQ_MP (@lem3865292 A a s x) (@lem3865780 A x s a h1)). Qed.
Lemma lem3865786 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term151 A a s.
Proof. exact (fun x : A => @lem3865781 A x s a h1). Qed.
Lemma lem3865787 {A : Type'} (a : A) (s : A -> Prop) : term152 A a s.
Proof. exact (fun h0 : s a => @lem3865786 A s a h0). Qed.
Lemma lem3865792 {A : Type'} (s : A -> Prop) : term163 A s.
Proof. exact (fun a : A => @lem3865787 A a s). Qed.
Lemma lem3865797 {A : Type'} : term167 A.
Proof. exact (fun s : A -> Prop => @lem3865792 A s). Qed.
Lemma lem3865798 {A : Type'} : term166 A.
Proof. exact (EQ_MP (@lem3865287 A) (@lem3865797 A)). Qed.
Lemma lem3865799 {A : Type'} (s : A -> Prop) : term203 A s.
Proof. exact (@lem3865798 A s). Qed.
Lemma lem3865800 {A : Type'} (s : A -> Prop) : (term203 A s) = (term162 A s).
Proof. exact (eq_refl (term203 A s)). Qed.
Lemma lem3865801 {A : Type'} (s : A -> Prop) : term162 A s.
Proof. exact (EQ_MP (@lem3865800 A s) (@lem3865799 A s)). Qed.
Lemma lem3865802 {A : Type'} (s : A -> Prop) (a : A) : term204 A s a.
Proof. exact (@lem3865801 A s a). Qed.
Lemma lem3865803 {A : Type'} (a : A) (s : A -> Prop) : (term204 A s a) = (term154 A a s).
Proof. exact (eq_refl (term204 A s a)). Qed.
Lemma lem3865804 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (EQ_MP (@lem3865803 A a s) (@lem3865802 A s a)). Qed.
Lemma lem3865806 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (@lem3865188 A a s (@lem3865804 A a s)). Qed.
Lemma lem3865807 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : False.
Proof. exact (@lem3865806 A a s (@lem3865172 A a s h1)). Qed.
Lemma lem3865808 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : (term155 A a s) = False.
Proof. exact (prop_ext (fun h2 : term155 A a s => @lem3865807 A a s h1) (fun h2 : False => @lem3865172 A a s h1)). Qed.
Lemma lem3865809 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : False.
Proof. exact (EQ_MP (@lem3865808 A a s h1) (@lem3865172 A a s h1)). Qed.
Lemma lem3865810 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (fun h0 : term155 A a s => @lem3865809 A a s h0). Qed.
Lemma lem3865811 {A : Type'} (a : A) (s : A -> Prop) : term152 A a s.
Proof. exact (EQ_MP (@lem3865171 A a s) (@lem3865810 A a s)). Qed.
Lemma lem3865812 {A : Type'} (a : A) (s : A -> Prop) : term136 A a s.
Proof. exact (EQ_MP (@lem3865167 A a s) (@lem3865811 A a s)). Qed.
Lemma lem3865813 {A : Type'} (a : A) (s : A -> Prop) : term135 A a s.
Proof. exact (EQ_MP (@lem3865101 A a s) (@lem3865812 A a s)). Qed.
Lemma lem3865814 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term126 A s a) = s.
Proof. exact (@lem3865813 A a s (@lem3864960 A a s h1)). Qed.
Lemma lem3865815 (m : nat) : term205 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem3865816 (m : nat) : (term205 m) = (term206 m).
Proof. exact (eq_refl (term205 m)). Qed.
Lemma lem3865817 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem3865816 m) (@lem3865815 m)). Qed.
Lemma lem3865818 (m : nat) (n : nat) : term207 m n.
Proof. exact (@lem3865817 m n). Qed.
Lemma lem3865819 (m : nat) (n : nat) : (term207 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem3865845 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (@CARD A s) = (S n).
Proof. exact (h1). Qed.
Lemma lem3865846 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3865847 {A : Type'} (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (term49 A s) = (term208 n).
Proof. exact (MK_COMB (@lem3865846) (@lem3865845 A s n h1)). Qed.
Lemma lem3865848 {A : Type'} (s : A -> Prop) (a : A) : (term116 A s a) = (term116 A s a).
Proof. exact (eq_refl (term116 A s a)). Qed.
Lemma lem3865849 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : ((@CARD A s) = (term116 A s a)) = ((S n) = (term116 A s a)).
Proof. exact (MK_COMB (@lem3865847 A s n h1) (@lem3865848 A s a)). Qed.
Lemma lem3865851 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem3865819 m n) (@lem3865818 m n)). Qed.
Lemma lem3865852 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : ((S n) = (term116 A s a)) = (n = (term54 A s a)).
Proof. exact (@lem3865851 n (term54 A s a)). Qed.
Lemma lem3865855 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : ((@CARD A s) = (term116 A s a)) = (n = (term54 A s a)).
Proof. exact (TRANS (@lem3865849 A a s n h1) (@lem3865852 A n s a)). Qed.
Lemma lem3865856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3865857 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (term209 A s a) = (term210 A n s a).
Proof. exact (MK_COMB (@lem3865856) (@lem3865855 A a s n h1)). Qed.
Lemma lem3865860 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = ((term54 A s a) = n).
Proof. exact (eq_refl ((term54 A s a) = n)). Qed.
Lemma lem3865861 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (term130 A s a n) = (term211 A s a n).
Proof. exact (MK_COMB (@lem3865857 A a s n h1) (@lem3865860 A s a n)). Qed.
Lemma lem3865866 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : (term211 A s a n) = (term130 A s a n).
Proof. exact (SYM (@lem3865861 A a s n h1)). Qed.
Lemma lem3865868 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3865869 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term211 A s a n) = (term212 A s a n).
Proof. exact (@lem3865868 (term211 A s a n)). Qed.
Lemma lem3865870 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term212 A s a n) = (term211 A s a n).
Proof. exact (SYM (@lem3865869 A s a n)). Qed.
Lemma lem3865871 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term213 A s a n) : term213 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865874 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term212 A s a n) : term212 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865875 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term214 A s a n.
Proof. exact (fun h0 : term212 A s a n => @lem3865874 A s a n h0). Qed.
Lemma lem3865876 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term214 A s a n) : term214 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865877 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term212 A s a n) : term212 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865878 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term212 A s a n) (h2 : term214 A s a n) : term212 A s a n.
Proof. exact (@lem3865876 A s a n h2 (@lem3865877 A s a n h1)). Qed.
Lemma lem3865879 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term212 A s a n) : term215 A s a n.
Proof. exact (fun h0 : term214 A s a n => @lem3865878 A s a n h1 h0). Qed.
Lemma lem3865880 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term214 A s a n) : term214 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865881 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term212 A s a n) (h2 : term214 A s a n) : term212 A s a n.
Proof. exact (@lem3865879 A s a n h1 (@lem3865880 A s a n h2)). Qed.
Lemma lem3865882 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term214 A s a n) : term214 A s a n.
Proof. exact (fun h0 : term212 A s a n => @lem3865881 A s a n h0 h1). Qed.
Lemma lem3865883 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term216 A s a n.
Proof. exact (fun h0 : term214 A s a n => @lem3865882 A s a n h0). Qed.
Lemma lem3865886 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term214 A s a n.
Proof. exact (@lem3865883 A s a n (@lem3865875 A s a n)). Qed.
Lemma lem3865887 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term214 A s a n.
Proof. exact (@lem3865886 A s a n). Qed.
Lemma lem3865901 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3865902 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term212 A s a n) = (term217 A s a n).
Proof. exact (@lem3865901 (term213 A s a n)). Qed.
Lemma lem3865904 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3865905 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term217 A s a n) = (term211 A s a n).
Proof. exact (@lem3865904 (term211 A s a n)). Qed.
Lemma lem3865908 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term212 A s a n) = (term211 A s a n).
Proof. exact (TRANS (@lem3865902 A s a n) (@lem3865905 A s a n)). Qed.
Lemma lem3865909 {A : Type'} (a : A) (n : nat) : (term218 A a n) = (term219 A a n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3865908 A s a n)). Qed.
Lemma lem3865910 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3865911 {A : Type'} (a : A) (n : nat) : (term220 A a n) = (term221 A a n).
Proof. exact (MK_COMB (@lem3865910 A) (@lem3865909 A a n)). Qed.
Lemma lem3865916 {A : Type'} (n : nat) : (term222 A n) = (term223 A n).
Proof. exact (fun_ext (fun a : A => @lem3865911 A a n)). Qed.
Lemma lem3865917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865918 {A : Type'} (n : nat) : (term224 A n) = (term225 A n).
Proof. exact (MK_COMB (@lem3865917 A) (@lem3865916 A n)). Qed.
Lemma lem3865923 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (fun_ext (fun n : nat => @lem3865918 A n)). Qed.
Lemma lem3865924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3865933 {A : Type'} : (term228 A) = (term229 A).
Proof. exact (MK_COMB (@lem3865924) (@lem3865923 A)). Qed.
Lemma lem3865938 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term211 A s a n) = (term211 A s a n).
Proof. exact (eq_refl (term211 A s a n)). Qed.
Lemma lem3865939 {A : Type'} (a : A) (n : nat) : (term219 A a n) = (term219 A a n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3865938 A s a n)). Qed.
Lemma lem3865940 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3865941 {A : Type'} (a : A) (n : nat) : (term221 A a n) = (term221 A a n).
Proof. exact (MK_COMB (@lem3865940 A) (@lem3865939 A a n)). Qed.
Lemma lem3865942 {A : Type'} (n : nat) : (term223 A n) = (term223 A n).
Proof. exact (fun_ext (fun a : A => @lem3865941 A a n)). Qed.
Lemma lem3865943 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3865944 {A : Type'} (n : nat) : (term225 A n) = (term225 A n).
Proof. exact (MK_COMB (@lem3865943 A) (@lem3865942 A n)). Qed.
Lemma lem3865945 {A : Type'} : (term227 A) = (term227 A).
Proof. exact (fun_ext (fun n : nat => @lem3865944 A n)). Qed.
Lemma lem3865946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3865947 {A : Type'} : (term229 A) = (term229 A).
Proof. exact (MK_COMB (@lem3865946) (@lem3865945 A)). Qed.
Lemma lem3865970 {A : Type'} : (term228 A) = (term229 A).
Proof. exact (TRANS (@lem3865933 A) (@lem3865947 A)). Qed.
Lemma lem3865971 {A : Type'} : (term229 A) = (term228 A).
Proof. exact (SYM (@lem3865970 A)). Qed.
Lemma lem3865974 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3865975 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : ((term54 A s a) = n) = (term230 A s a n).
Proof. exact (@lem3865974 ((term54 A s a) = n)). Qed.
Lemma lem3865976 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term230 A s a n) = ((term54 A s a) = n).
Proof. exact (SYM (@lem3865975 A s a n)). Qed.
Lemma lem3865977 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term231 A s a n) : term231 A s a n.
Proof. exact (h1). Qed.
Lemma lem3865983 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : n = (term54 A s a).
Proof. exact (h1). Qed.
Lemma lem3865989 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term231 A s a n) : term231 A s a n.
Proof. exact (h1). Qed.
Lemma lem3866001 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : n = (term54 A s a).
Proof. exact (h1). Qed.
Lemma lem3866015 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term231 A s a n) : term231 A s a n.
Proof. exact (h1). Qed.
Lemma lem3866019 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : n = (term54 A s a).
Proof. exact (h1). Qed.
Lemma lem3866023 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term231 A s a n) : term231 A s a n.
Proof. exact (h1). Qed.
Lemma lem3866025 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : n = (term54 A s a).
Proof. exact (h1). Qed.
Lemma lem3866027 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term231 A s a n) : term231 A s a n.
Proof. exact (h1). Qed.
Lemma lem3866042 {A : Type'} (s : A -> Prop) (a : A) : (term232 A s a) = (term232 A s a).
Proof. exact (eq_refl (term232 A s a)). Qed.
Lemma lem3866043 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : (term233 A s a n) = (term234 A s a).
Proof. exact (MK_COMB (@lem3866042 A s a) (@lem3866025 A n s a h1)). Qed.
Lemma lem3866044 {A : Type'} (s : A -> Prop) (a : A) : (term234 A s a) = (term235 A s a).
Proof. exact (eq_refl (term234 A s a)). Qed.
Lemma lem3866045 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term236 A s a n) = (term236 A s a n).
Proof. exact (eq_refl (term236 A s a n)). Qed.
Lemma lem3866046 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : ((term233 A s a n) = (term234 A s a)) = ((term233 A s a n) = (term235 A s a)).
Proof. exact (MK_COMB (@lem3866045 A s a n) (@lem3866044 A s a)). Qed.
Lemma lem3866047 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term233 A s a n) = (term231 A s a n).
Proof. exact (eq_refl (term233 A s a n)). Qed.
Lemma lem3866048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3866049 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term236 A s a n) = (term237 A s a n).
Proof. exact (MK_COMB (@lem3866048) (@lem3866047 A s a n)). Qed.
Lemma lem3866050 {A : Type'} (s : A -> Prop) (a : A) : (term235 A s a) = (term235 A s a).
Proof. exact (eq_refl (term235 A s a)). Qed.
Lemma lem3866051 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : ((term233 A s a n) = (term235 A s a)) = ((term231 A s a n) = (term235 A s a)).
Proof. exact (MK_COMB (@lem3866049 A s a n) (@lem3866050 A s a)). Qed.
Lemma lem3866052 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : ((term233 A s a n) = (term234 A s a)) = ((term231 A s a n) = (term235 A s a)).
Proof. exact (TRANS (@lem3866046 A n s a) (@lem3866051 A n s a)). Qed.
Lemma lem3866053 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : (term231 A s a n) = (term235 A s a).
Proof. exact (EQ_MP (@lem3866052 A n s a) (@lem3866043 A n s a h1)). Qed.
Lemma lem3866054 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : term235 A s a.
Proof. exact (EQ_MP (@lem3866053 A n s a h2) (@lem3866027 A s a n h1)). Qed.
Lemma lem3866085 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3866086 {A : Type'} (s : A -> Prop) (a : A) : (term54 A s a) = (term54 A s a).
Proof. exact (@lem3866085 (term54 A s a)). Qed.
Lemma lem3866087 {A : Type'} (s : A -> Prop) (a : A) : term238 A s a.
Proof. exact (fun h0 : term235 A s a => @lem3866086 A s a). Qed.
Lemma lem3866089 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866090 {A : Type'} (s : A -> Prop) (a : A) : (term238 A s a) = ((term54 A s a) = (term54 A s a)).
Proof. exact (@lem3866089 ((term54 A s a) = (term54 A s a))). Qed.
Lemma lem3866091 {A : Type'} (s : A -> Prop) (a : A) : (term54 A s a) = (term54 A s a).
Proof. exact (EQ_MP (@lem3866090 A s a) (@lem3866087 A s a)). Qed.
Lemma lem3866094 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3866096 {A : Type'} (s : A -> Prop) (a : A) : (term235 A s a) = (term239 A s a).
Proof. exact (@lem3866094 ((term54 A s a) = (term54 A s a))). Qed.
Lemma lem3866099 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : term239 A s a.
Proof. exact (EQ_MP (@lem3866096 A s a) (@lem3866054 A n s a h1 h2)). Qed.
Lemma lem3866102 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (@lem3866099 A n s a h1 h2 (@lem3866091 A s a)). Qed.
Lemma lem3866103 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : term200.
Proof. exact (fun h0 : ~ False => @lem3866102 A n s a h1 h2). Qed.
Lemma lem3866105 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866106 : term200 = False.
Proof. exact (@lem3866105 False). Qed.
Lemma lem3866108 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866106) (@lem3866103 A n s a h1 h2)). Qed.
Lemma lem3866109 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866108 A n s a h1 h2) (fun h3 : False => @lem3866027 A s a n h1)). Qed.
Lemma lem3866110 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866109 A n s a h1 h2) (@lem3866027 A s a n h1)). Qed.
Lemma lem3866111 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (n = (term54 A s a)) = False.
Proof. exact (prop_ext (fun h3 : n = (term54 A s a) => @lem3866110 A n s a h1 h2) (fun h3 : False => @lem3866025 A n s a h2)). Qed.
Lemma lem3866112 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866111 A n s a h1 h2) (@lem3866025 A n s a h2)). Qed.
Lemma lem3866113 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866112 A n s a h1 h2) (fun h3 : False => @lem3866023 A s a n h1)). Qed.
Lemma lem3866114 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866113 A n s a h1 h2) (@lem3866023 A s a n h1)). Qed.
Lemma lem3866115 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (n = (term54 A s a)) = False.
Proof. exact (prop_ext (fun h3 : n = (term54 A s a) => @lem3866114 A n s a h1 h2) (fun h3 : False => @lem3866019 A n s a h2)). Qed.
Lemma lem3866116 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866115 A n s a h1 h2) (@lem3866019 A n s a h2)). Qed.
Lemma lem3866117 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866116 A n s a h1 h2) (fun h3 : False => @lem3866023 A s a n h1)). Qed.
Lemma lem3866118 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866117 A n s a h1 h2) (@lem3866023 A s a n h1)). Qed.
Lemma lem3866119 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (n = (term54 A s a)) = False.
Proof. exact (prop_ext (fun h3 : n = (term54 A s a) => @lem3866118 A n s a h1 h2) (fun h3 : False => @lem3866019 A n s a h2)). Qed.
Lemma lem3866120 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866119 A n s a h1 h2) (@lem3866019 A n s a h2)). Qed.
Lemma lem3866121 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866120 A n s a h1 h2) (fun h3 : False => @lem3866015 A s a n h1)). Qed.
Lemma lem3866122 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866121 A n s a h1 h2) (@lem3866015 A s a n h1)). Qed.
Lemma lem3866123 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (n = (term54 A s a)) = False.
Proof. exact (prop_ext (fun h3 : n = (term54 A s a) => @lem3866122 A n s a h1 h2) (fun h3 : False => @lem3866001 A n s a h2)). Qed.
Lemma lem3866124 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866123 A n s a h1 h2) (@lem3866001 A n s a h2)). Qed.
Lemma lem3866125 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866124 A n s a h1 h2) (fun h3 : False => @lem3865989 A s a n h1)). Qed.
Lemma lem3866126 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866125 A n s a h1 h2) (@lem3865989 A s a n h1)). Qed.
Lemma lem3866127 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (n = (term54 A s a)) = False.
Proof. exact (prop_ext (fun h3 : n = (term54 A s a) => @lem3866126 A n s a h1 h2) (fun h3 : False => @lem3865983 A n s a h2)). Qed.
Lemma lem3866128 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866127 A n s a h1 h2) (@lem3865983 A n s a h2)). Qed.
Lemma lem3866129 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : (term231 A s a n) = False.
Proof. exact (prop_ext (fun h3 : term231 A s a n => @lem3866128 A n s a h1 h2) (fun h3 : False => @lem3865977 A s a n h1)). Qed.
Lemma lem3866130 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : term231 A s a n) (h2 : n = (term54 A s a)) : False.
Proof. exact (EQ_MP (@lem3866129 A n s a h1 h2) (@lem3865977 A s a n h1)). Qed.
Lemma lem3866131 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : term230 A s a n.
Proof. exact (fun h0 : term231 A s a n => @lem3866130 A n s a h0 h1). Qed.
Lemma lem3866132 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (h1 : n = (term54 A s a)) : (term54 A s a) = n.
Proof. exact (EQ_MP (@lem3865976 A s a n) (@lem3866131 A n s a h1)). Qed.
Lemma lem3866133 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term211 A s a n.
Proof. exact (fun h0 : n = (term54 A s a) => @lem3866132 A n s a h0). Qed.
Lemma lem3866138 {A : Type'} (a : A) (n : nat) : term221 A a n.
Proof. exact (fun s : A -> Prop => @lem3866133 A s a n). Qed.
Lemma lem3866143 {A : Type'} (n : nat) : term225 A n.
Proof. exact (fun a : A => @lem3866138 A a n). Qed.
Lemma lem3866148 {A : Type'} : term229 A.
Proof. exact (fun n : nat => @lem3866143 A n). Qed.
Lemma lem3866149 {A : Type'} : term228 A.
Proof. exact (EQ_MP (@lem3865971 A) (@lem3866148 A)). Qed.
Lemma lem3866150 {A : Type'} (n : nat) : term240 A n.
Proof. exact (@lem3866149 A n). Qed.
Lemma lem3866151 {A : Type'} (n : nat) : (term240 A n) = (term224 A n).
Proof. exact (eq_refl (term240 A n)). Qed.
Lemma lem3866152 {A : Type'} (n : nat) : term224 A n.
Proof. exact (EQ_MP (@lem3866151 A n) (@lem3866150 A n)). Qed.
Lemma lem3866153 {A : Type'} (n : nat) (a : A) : term241 A n a.
Proof. exact (@lem3866152 A n a). Qed.
Lemma lem3866154 {A : Type'} (a : A) (n : nat) : (term241 A n a) = (term220 A a n).
Proof. exact (eq_refl (term241 A n a)). Qed.
Lemma lem3866155 {A : Type'} (a : A) (n : nat) : term220 A a n.
Proof. exact (EQ_MP (@lem3866154 A a n) (@lem3866153 A n a)). Qed.
Lemma lem3866156 {A : Type'} (a : A) (n : nat) (s : A -> Prop) : term242 A a n s.
Proof. exact (@lem3866155 A a n s). Qed.
Lemma lem3866157 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term242 A a n s) = (term212 A s a n).
Proof. exact (eq_refl (term242 A a n s)). Qed.
Lemma lem3866158 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term212 A s a n.
Proof. exact (EQ_MP (@lem3866157 A s a n) (@lem3866156 A a n s)). Qed.
Lemma lem3866160 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term212 A s a n.
Proof. exact (@lem3865887 A s a n (@lem3866158 A s a n)). Qed.
Lemma lem3866161 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term213 A s a n) : False.
Proof. exact (@lem3866160 A s a n (@lem3865871 A s a n h1)). Qed.
Lemma lem3866162 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term213 A s a n) : (term213 A s a n) = False.
Proof. exact (prop_ext (fun h2 : term213 A s a n => @lem3866161 A s a n h1) (fun h2 : False => @lem3865871 A s a n h1)). Qed.
Lemma lem3866163 {A : Type'} (s : A -> Prop) (a : A) (n : nat) (h1 : term213 A s a n) : False.
Proof. exact (EQ_MP (@lem3866162 A s a n h1) (@lem3865871 A s a n h1)). Qed.
Lemma lem3866164 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term212 A s a n.
Proof. exact (fun h0 : term213 A s a n => @lem3866163 A s a n h0). Qed.
Lemma lem3866165 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term211 A s a n.
Proof. exact (EQ_MP (@lem3865870 A s a n) (@lem3866164 A s a n)). Qed.
Lemma lem3866166 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (@CARD A s) = (S n)) : term130 A s a n.
Proof. exact (EQ_MP (@lem3865866 A a s n h1) (@lem3866165 A s a n)). Qed.
Lemma lem3866167 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : (term126 A s a) = s) (h2 : (@CARD A s) = (S n)) : term125 A s a n.
Proof. exact (EQ_MP (@lem3865080 A n a s h1) (@lem3866166 A a s n h2)). Qed.
Lemma lem3866168 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (S n)) (h2 : @IN A a s) : ((term126 A s a) = s) = (term125 A s a n).
Proof. exact (prop_ext (fun h3 : (term126 A s a) = s => @lem3866167 A a s n h3 h1) (fun h3 : term125 A s a n => @lem3865814 A a s h2)). Qed.
Lemma lem3866169 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (S n)) (h2 : @IN A a s) : term125 A s a n.
Proof. exact (EQ_MP (@lem3866168 A n a s h1 h2) (@lem3865814 A a s h2)). Qed.
Lemma lem3866170 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) (h3 : @IN A a s) : term124 A s a n.
Proof. exact (EQ_MP (@lem3865066 A n a s h1 h3) (@lem3866169 A n a s h2 h3)). Qed.
Lemma lem3866171 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) (h3 : @IN A a s) : (term54 A s a) = n.
Proof. exact (@lem3866170 A n a s h1 h2 h3 (@lem3864363 A s a)). Qed.
Lemma lem3866173 {A : Type'} (s : A -> Prop) : (term6 A s) = (term5 A s).
Proof. exact (EQ_MP (@lem3864334 A s) (@lem3864333 A s)). Qed.
Lemma lem3866174 {A : Type'} (s : A -> Prop) : (term6 A s) = (term5 A s).
Proof. exact (@lem3866173 A s). Qed.
Lemma lem3866175 {A : Type'} (s : A -> Prop) (h1 : term6 A s) : term5 A s.
Proof. exact (EQ_MP (@lem3866174 A s) (@lem3864379 A s h1)). Qed.
Lemma lem3866176 {A : Type'} (s : A -> Prop) (h1 : term5 A s) : term5 A s.
Proof. exact (h1). Qed.
Lemma lem3866177 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3866178 {A : Type'} (s : A -> Prop) : term101 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem3866179 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem3866180 {A : Type'} (s : A -> Prop) : term102 A s.
Proof. exact (EQ_MP (@lem3866179 A s) (@lem3866178 A s)). Qed.
Lemma lem3866181 {A : Type'} (s : A -> Prop) (x : A) : term103 A s x.
Proof. exact (@lem3866180 A s x). Qed.
Lemma lem3866182 {A : Type'} (s : A -> Prop) (x : A) : (term103 A s x) = (term104 A s x).
Proof. exact (eq_refl (term103 A s x)). Qed.
Lemma lem3866183 {A : Type'} (s : A -> Prop) (x : A) : term104 A s x.
Proof. exact (EQ_MP (@lem3866182 A s x) (@lem3866181 A s x)). Qed.
Lemma lem3866184 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term105 A s x y.
Proof. exact (@lem3866183 A s x y). Qed.
Lemma lem3866185 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term105 A s x y) = ((term106 A x s y) = (term107 A s x y)).
Proof. exact (eq_refl (term105 A s x y)). Qed.
Lemma lem3866187 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3866188 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem3866189 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem3866188 A s) (@lem3866187 A s)). Qed.
Lemma lem3866190 {A : Type'} (s : A -> Prop) (x : A) : term17 A s x.
Proof. exact (@lem3866189 A s x). Qed.
Lemma lem3866191 {A : Type'} (x : A) (s : A -> Prop) : (term17 A s x) = ((term18 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term17 A s x)). Qed.
Lemma lem3866206 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3866213 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem3866220 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3866191 A x s) (@lem3866190 A s x)). Qed.
Lemma lem3866221 {A : Type'} (x : A) (s : A -> Prop) : (term18 A s x) = (@FINITE A s).
Proof. exact (@lem3866220 A x s). Qed.
Lemma lem3866222 {A : Type'} (a : A) (s : A -> Prop) : (term18 A s a) = (@FINITE A s).
Proof. exact (@lem3866221 A a s). Qed.
Lemma lem3866224 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3866206 A s) (@lem3864367 A s h1)). Qed.
Lemma lem3866225 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term18 A s a) = True.
Proof. exact (TRANS (@lem3866222 A a s) (@lem3866224 A s h1)). Qed.
Lemma lem3866226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3866227 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term108 A s a) = (imp True).
Proof. exact (MK_COMB (@lem3866226) (@lem3866225 A a s h1)). Qed.
Lemma lem3866231 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (EQ_MP (@lem3866185 A s x y) (@lem3866184 A s x y)). Qed.
Lemma lem3866232 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (@lem3866231 A s x y). Qed.
Lemma lem3866233 {A : Type'} (s : A -> Prop) (a : A) : (term109 A s a) = (term110 A s a).
Proof. exact (@lem3866232 A s a a). Qed.
Lemma lem3866237 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem3866213 A a s) (@lem3866177 A a s h1)). Qed.
Lemma lem3866238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3866239 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term111 A a s) = (and True).
Proof. exact (MK_COMB (@lem3866238) (@lem3866237 A a s h1)). Qed.
Lemma lem3866241 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3866242 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3866241 A x). Qed.
Lemma lem3866243 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem3866242 A a). Qed.
Lemma lem3866244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3866245 {A : Type'} (a : A) : (term112 A a) = (~ True).
Proof. exact (MK_COMB (@lem3866244) (@lem3866243 A a)). Qed.
Lemma lem3866247 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3866248 {A : Type'} (a : A) : (term112 A a) = False.
Proof. exact (TRANS (@lem3866245 A a) (@lem3866247)). Qed.
Lemma lem3866249 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term110 A s a) = (True /\ False).
Proof. exact (MK_COMB (@lem3866239 A a s h1) (@lem3866248 A a)). Qed.
Lemma lem3866251 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3866252 : (True /\ False) = False.
Proof. exact (@lem3866251 False). Qed.
Lemma lem3866253 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term110 A s a) = False.
Proof. exact (TRANS (@lem3866249 A a s h1) (@lem3866252)). Qed.
Lemma lem3866254 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term109 A s a) = False.
Proof. exact (TRANS (@lem3866233 A s a) (@lem3866253 A a s h1)). Qed.
Lemma lem3866255 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem3866256 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term113 A s a) = (@COND nat False).
Proof. exact (MK_COMB (@lem3866255) (@lem3866254 A a s h1)). Qed.
Lemma lem3866257 {A : Type'} (s : A -> Prop) (a : A) : (term54 A s a) = (term54 A s a).
Proof. exact (eq_refl (term54 A s a)). Qed.
Lemma lem3866258 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term114 A s a) = (term115 A s a).
Proof. exact (MK_COMB (@lem3866256 A a s h1) (@lem3866257 A s a)). Qed.
Lemma lem3866259 {A : Type'} (s : A -> Prop) (a : A) : (term116 A s a) = (term116 A s a).
Proof. exact (eq_refl (term116 A s a)). Qed.
Lemma lem3866260 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term117 A s a) = (term118 A s a).
Proof. exact (MK_COMB (@lem3866258 A a s h1) (@lem3866259 A s a)). Qed.
Lemma lem3866262 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3866263 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3866262 nat t1 t2). Qed.
Lemma lem3866264 {A : Type'} (s : A -> Prop) (a : A) : (term118 A s a) = (term116 A s a).
Proof. exact (@lem3866263 (term54 A s a) (term116 A s a)). Qed.
Lemma lem3866265 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term117 A s a) = (term116 A s a).
Proof. exact (TRANS (@lem3866260 A a s h1) (@lem3866264 A s a)). Qed.
Lemma lem3866266 {A : Type'} (s : A -> Prop) (a : A) : (term119 A s a) = (term119 A s a).
Proof. exact (eq_refl (term119 A s a)). Qed.
Lemma lem3866267 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : ((term120 A s a) = (term117 A s a)) = ((term120 A s a) = (term116 A s a)).
Proof. exact (MK_COMB (@lem3866266 A s a) (@lem3866265 A a s h1)). Qed.
Lemma lem3866270 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term4 A s a) = (term121 A s a).
Proof. exact (MK_COMB (@lem3866227 A a s h1) (@lem3866267 A a s h2)). Qed.
Lemma lem3866272 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3866273 {A : Type'} (s : A -> Prop) (a : A) : (term121 A s a) = ((term120 A s a) = (term116 A s a)).
Proof. exact (@lem3866272 ((term120 A s a) = (term116 A s a))). Qed.
Lemma lem3866276 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term4 A s a) = ((term120 A s a) = (term116 A s a)).
Proof. exact (TRANS (@lem3866270 A a s h1 h2) (@lem3866273 A s a)). Qed.
Lemma lem3866277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3866278 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term122 A s a) = (term123 A s a).
Proof. exact (MK_COMB (@lem3866277) (@lem3866276 A a s h1 h2)). Qed.
Lemma lem3866281 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = (S n)) = ((@CARD A s) = (S n)).
Proof. exact (eq_refl ((@CARD A s) = (S n))). Qed.
Lemma lem3866282 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term243 A a s n) = (term244 A a s n).
Proof. exact (MK_COMB (@lem3866278 A a s h1 h2) (@lem3866281 A s n)). Qed.
Lemma lem3866287 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A a s) : (term244 A a s n) = (term243 A a s n).
Proof. exact (SYM (@lem3866282 A n a s h1 h2)). Qed.
Lemma lem3866288 {A : Type'} (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term126 A s a) = s.
Proof. exact (h1). Qed.
Lemma lem3866289 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term245 A a s n) = (term245 A a s n).
Proof. exact (eq_refl (term245 A a s n)). Qed.
Lemma lem3866290 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term246 A n s a) = (term247 A a n s).
Proof. exact (MK_COMB (@lem3866289 A a s n) (@lem3866288 A a s h1)). Qed.
Lemma lem3866291 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term247 A a n s) = (term248 A a s n).
Proof. exact (eq_refl (term247 A a n s)). Qed.
Lemma lem3866292 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term249 A n s a) = (term249 A n s a).
Proof. exact (eq_refl (term249 A n s a)). Qed.
Lemma lem3866293 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : ((term246 A n s a) = (term247 A a n s)) = ((term246 A n s a) = (term248 A a s n)).
Proof. exact (MK_COMB (@lem3866292 A n s a) (@lem3866291 A a s n)). Qed.
Lemma lem3866294 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term246 A n s a) = (term244 A a s n).
Proof. exact (eq_refl (term246 A n s a)). Qed.
Lemma lem3866295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3866296 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term249 A n s a) = (term250 A a s n).
Proof. exact (MK_COMB (@lem3866295) (@lem3866294 A a s n)). Qed.
Lemma lem3866297 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term248 A a s n) = (term248 A a s n).
Proof. exact (eq_refl (term248 A a s n)). Qed.
Lemma lem3866298 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : ((term246 A n s a) = (term248 A a s n)) = ((term244 A a s n) = (term248 A a s n)).
Proof. exact (MK_COMB (@lem3866296 A a s n) (@lem3866297 A a s n)). Qed.
Lemma lem3866299 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : ((term246 A n s a) = (term247 A a n s)) = ((term244 A a s n) = (term248 A a s n)).
Proof. exact (TRANS (@lem3866293 A a s n) (@lem3866298 A a s n)). Qed.
Lemma lem3866300 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term244 A a s n) = (term248 A a s n).
Proof. exact (EQ_MP (@lem3866299 A a s n) (@lem3866290 A n a s h1)). Qed.
Lemma lem3866301 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : (term126 A s a) = s) : (term248 A a s n) = (term244 A a s n).
Proof. exact (SYM (@lem3866300 A n a s h1)). Qed.
Lemma lem3866307 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3866308 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term133 A s t).
Proof. exact (@lem3866307 A s t). Qed.
Lemma lem3866309 {A : Type'} (a : A) (s : A -> Prop) : ((term126 A s a) = s) = (term134 A a s).
Proof. exact (@lem3866308 A (term126 A s a) s). Qed.
Lemma lem3866318 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3866319 {A : Type'} (a : A) (s : A -> Prop) : (term135 A a s) = (term136 A a s).
Proof. exact (MK_COMB (@lem3866318 A a s) (@lem3866309 A a s)). Qed.
Lemma lem3866322 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term135 A a s).
Proof. exact (SYM (@lem3866319 A a s)). Qed.
Lemma lem3866326 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3866327 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3866326 A P x). Qed.
Lemma lem3866328 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3866327 A s a). Qed.
Lemma lem3866329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3866330 {A : Type'} (s : A -> Prop) (a : A) : (term31 A a s) = (term137 A s a).
Proof. exact (MK_COMB (@lem3866329) (@lem3866328 A s a)). Qed.
Lemma lem3866338 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term138 A x y s) = (term139 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3866339 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term138 A x y s) = (term139 A y x s).
Proof. exact (@lem3866338 A y x s). Qed.
Lemma lem3866340 {A : Type'} (x : A) (s : A -> Prop) (a : A) : (term140 A x s a) = (term141 A x s a).
Proof. exact (@lem3866339 A a x (@DELETE A s a)). Qed.
Lemma lem3866346 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3866347 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term106 A x s y) = (term107 A s x y).
Proof. exact (@lem3866346 A s x y). Qed.
Lemma lem3866348 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term106 A x s a) = (term107 A s x a).
Proof. exact (@lem3866347 A s x a). Qed.
Lemma lem3866352 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3866353 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3866352 A P x). Qed.
Lemma lem3866354 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3866353 A s x). Qed.
Lemma lem3866355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3866356 {A : Type'} (s : A -> Prop) (x : A) : (term111 A x s) = (term142 A s x).
Proof. exact (MK_COMB (@lem3866355) (@lem3866354 A s x)). Qed.
Lemma lem3866359 {A : Type'} (x : A) (a : A) : (term143 A x a) = (term143 A x a).
Proof. exact (eq_refl (term143 A x a)). Qed.
Lemma lem3866360 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term107 A s x a) = (term144 A s x a).
Proof. exact (MK_COMB (@lem3866356 A s x) (@lem3866359 A x a)). Qed.
Lemma lem3866363 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term106 A x s a) = (term144 A s x a).
Proof. exact (TRANS (@lem3866348 A s x a) (@lem3866360 A s x a)). Qed.
Lemma lem3866364 {A : Type'} (x : A) (a : A) : (term145 A x a) = (term145 A x a).
Proof. exact (eq_refl (term145 A x a)). Qed.
Lemma lem3866365 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term141 A x s a) = (term146 A s x a).
Proof. exact (MK_COMB (@lem3866364 A x a) (@lem3866363 A s x a)). Qed.
Lemma lem3866368 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term140 A x s a) = (term146 A s x a).
Proof. exact (TRANS (@lem3866340 A x s a) (@lem3866365 A s x a)). Qed.
Lemma lem3866369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3866370 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term147 A x s a) = (term148 A s x a).
Proof. exact (MK_COMB (@lem3866369) (@lem3866368 A s x a)). Qed.
Lemma lem3866372 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3866373 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3866372 A P x). Qed.
Lemma lem3866374 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3866373 A s x). Qed.
Lemma lem3866375 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term140 A x s a) = (@IN A x s)) = ((term146 A s x a) = (s x)).
Proof. exact (MK_COMB (@lem3866370 A s x a) (@lem3866374 A s x)). Qed.
Lemma lem3866378 {A : Type'} (a : A) (s : A -> Prop) : (term149 A a s) = (term150 A a s).
Proof. exact (fun_ext (fun x : A => @lem3866375 A a s x)). Qed.
Lemma lem3866379 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3866380 {A : Type'} (a : A) (s : A -> Prop) : (term134 A a s) = (term151 A a s).
Proof. exact (MK_COMB (@lem3866379 A) (@lem3866378 A a s)). Qed.
Lemma lem3866385 {A : Type'} (a : A) (s : A -> Prop) : (term136 A a s) = (term152 A a s).
Proof. exact (MK_COMB (@lem3866330 A s a) (@lem3866380 A a s)). Qed.
Lemma lem3866388 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term136 A a s).
Proof. exact (SYM (@lem3866385 A a s)). Qed.
Lemma lem3866390 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3866391 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term154 A a s).
Proof. exact (@lem3866390 (term152 A a s)). Qed.
Lemma lem3866392 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term152 A a s).
Proof. exact (SYM (@lem3866391 A a s)). Qed.
Lemma lem3866393 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : term155 A a s.
Proof. exact (h1). Qed.
Lemma lem3866396 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term154 A a s.
Proof. exact (h1). Qed.
Lemma lem3866397 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (fun h0 : term154 A a s => @lem3866396 A a s h0). Qed.
Lemma lem3866398 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (h1). Qed.
Lemma lem3866399 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term154 A a s.
Proof. exact (h1). Qed.
Lemma lem3866400 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) (h2 : term156 A a s) : term154 A a s.
Proof. exact (@lem3866398 A a s h2 (@lem3866399 A a s h1)). Qed.
Lemma lem3866401 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) : term157 A a s.
Proof. exact (fun h0 : term156 A a s => @lem3866400 A a s h1 h0). Qed.
Lemma lem3866402 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (h1). Qed.
Lemma lem3866403 {A : Type'} (a : A) (s : A -> Prop) (h1 : term154 A a s) (h2 : term156 A a s) : term154 A a s.
Proof. exact (@lem3866401 A a s h1 (@lem3866402 A a s h2)). Qed.
Lemma lem3866404 {A : Type'} (a : A) (s : A -> Prop) (h1 : term156 A a s) : term156 A a s.
Proof. exact (fun h0 : term154 A a s => @lem3866403 A a s h0 h1). Qed.
Lemma lem3866405 {A : Type'} (a : A) (s : A -> Prop) : term158 A a s.
Proof. exact (fun h0 : term156 A a s => @lem3866404 A a s h0). Qed.
Lemma lem3866408 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (@lem3866405 A a s (@lem3866397 A a s)). Qed.
Lemma lem3866409 {A : Type'} (a : A) (s : A -> Prop) : term156 A a s.
Proof. exact (@lem3866408 A a s). Qed.
Lemma lem3866419 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3866420 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term159 A a s).
Proof. exact (@lem3866419 (term155 A a s)). Qed.
Lemma lem3866422 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3866423 {A : Type'} (a : A) (s : A -> Prop) : (term159 A a s) = (term152 A a s).
Proof. exact (@lem3866422 (term152 A a s)). Qed.
Lemma lem3866426 {A : Type'} (a : A) (s : A -> Prop) : (term154 A a s) = (term152 A a s).
Proof. exact (TRANS (@lem3866420 A a s) (@lem3866423 A a s)). Qed.
Lemma lem3866435 {A : Type'} (s : A -> Prop) : (term160 A s) = (term161 A s).
Proof. exact (fun_ext (fun a : A => @lem3866426 A a s)). Qed.
Lemma lem3866436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3866437 {A : Type'} (s : A -> Prop) : (term162 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem3866436 A) (@lem3866435 A s)). Qed.
Lemma lem3866442 {A : Type'} : (term164 A) = (term165 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3866437 A s)). Qed.
Lemma lem3866443 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3866452 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (MK_COMB (@lem3866443 A) (@lem3866442 A)). Qed.
Lemma lem3866467 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term146 A s x a) = (s x)) = ((term146 A s x a) = (s x)).
Proof. exact (eq_refl ((term146 A s x a) = (s x))). Qed.
Lemma lem3866468 {A : Type'} (a : A) (s : A -> Prop) : (term150 A a s) = (term150 A a s).
Proof. exact (fun_ext (fun x : A => @lem3866467 A a s x)). Qed.
Lemma lem3866469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3866470 {A : Type'} (a : A) (s : A -> Prop) : (term151 A a s) = (term151 A a s).
Proof. exact (MK_COMB (@lem3866469 A) (@lem3866468 A a s)). Qed.
Lemma lem3866473 {A : Type'} (s : A -> Prop) (a : A) : (term137 A s a) = (term137 A s a).
Proof. exact (eq_refl (term137 A s a)). Qed.
Lemma lem3866474 {A : Type'} (a : A) (s : A -> Prop) : (term152 A a s) = (term152 A a s).
Proof. exact (MK_COMB (@lem3866473 A s a) (@lem3866470 A a s)). Qed.
Lemma lem3866475 {A : Type'} (s : A -> Prop) : (term161 A s) = (term161 A s).
Proof. exact (fun_ext (fun a : A => @lem3866474 A a s)). Qed.
Lemma lem3866476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3866477 {A : Type'} (s : A -> Prop) : (term163 A s) = (term163 A s).
Proof. exact (MK_COMB (@lem3866476 A) (@lem3866475 A s)). Qed.
Lemma lem3866478 {A : Type'} : (term165 A) = (term165 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3866477 A s)). Qed.
Lemma lem3866479 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3866480 {A : Type'} : (term167 A) = (term167 A).
Proof. exact (MK_COMB (@lem3866479 A) (@lem3866478 A)). Qed.
Lemma lem3866507 {A : Type'} : (term166 A) = (term167 A).
Proof. exact (TRANS (@lem3866452 A) (@lem3866480 A)). Qed.
Lemma lem3866508 {A : Type'} : (term167 A) = (term166 A).
Proof. exact (SYM (@lem3866507 A)). Qed.
Lemma lem3866511 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3866512 {A : Type'} (a : A) (s : A -> Prop) (x : A) : ((term146 A s x a) = (s x)) = (term168 A a s x).
Proof. exact (@lem3866511 ((term146 A s x a) = (s x))). Qed.
Lemma lem3866513 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term168 A a s x) = ((term146 A s x a) = (s x)).
Proof. exact (SYM (@lem3866512 A a s x)). Qed.
Lemma lem3866514 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term169 A a s x) : term169 A a s x.
Proof. exact (h1). Qed.
Lemma lem3866520 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866528 {A : Type'} (x : A) (a : A) : (term170 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem3866530 {A : Type'} (s : A -> Prop) (x : A) : (term171 A s x) = (term171 A s x).
Proof. exact (eq_refl (term171 A s x)). Qed.
Lemma lem3866531 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term172 A s x a) = (term173 A s x a).
Proof. exact (MK_COMB (@lem3866530 A s x) (@lem3866528 A x a)). Qed.
Lemma lem3866532 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term174 A s x a) = (term172 A s x a).
Proof. exact (@lem17045 (s x) (term143 A x a)). Qed.
Lemma lem3866533 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term174 A s x a) = (term173 A s x a).
Proof. exact (TRANS (@lem3866532 A s x a) (@lem3866531 A s x a)). Qed.
Lemma lem3866538 {A : Type'} (x : A) (a : A) : (term175 A x a) = (term175 A x a).
Proof. exact (eq_refl (term175 A x a)). Qed.
Lemma lem3866539 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term176 A s x a) = (term177 A s x a).
Proof. exact (MK_COMB (@lem3866538 A x a) (@lem3866533 A s x a)). Qed.
Lemma lem3866540 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term178 A s x a) = (term176 A s x a).
Proof. exact (@lem17160 (x = a) (term144 A s x a)). Qed.
Lemma lem3866541 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term178 A s x a) = (term177 A s x a).
Proof. exact (TRANS (@lem3866540 A s x a) (@lem3866539 A s x a)). Qed.
Lemma lem3866546 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3866547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3866548 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term179 A s x a) = (term180 A s x a).
Proof. exact (MK_COMB (@lem3866547) (@lem3866541 A s x a)). Qed.
Lemma lem3866549 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term181 A a s x) = (term182 A a s x).
Proof. exact (MK_COMB (@lem3866548 A s x a) (@lem3866546 A s x)). Qed.
Lemma lem3866554 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term183 A a s x) = (term183 A a s x).
Proof. exact (eq_refl (term183 A a s x)). Qed.
Lemma lem3866555 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term184 A a s x) = (term185 A a s x).
Proof. exact (MK_COMB (@lem3866554 A a s x) (@lem3866549 A a s x)). Qed.
Lemma lem3866556 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term169 A a s x) = (term184 A a s x).
Proof. exact (@lem17646 (term146 A s x a) (s x)). Qed.
Lemma lem3866561 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term169 A a s x) = (term185 A a s x).
Proof. exact (TRANS (@lem3866556 A a s x) (@lem3866555 A a s x)). Qed.
Lemma lem3866566 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866628 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term169 A a s x) : term185 A a s x.
Proof. exact (EQ_MP (@lem3866561 A a s x) (@lem3866514 A a s x h1)). Qed.
Lemma lem3866629 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term186 A a s x.
Proof. exact (h1). Qed.
Lemma lem3866630 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term182 A a s x.
Proof. exact (h1). Qed.
Lemma lem3866632 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term146 A s x a.
Proof. exact (proj1 (@lem3866629 A a s x h1)). Qed.
Lemma lem3866634 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : term144 A s x a.
Proof. exact (h1). Qed.
Lemma lem3866638 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term177 A s x a.
Proof. exact (proj1 (@lem3866630 A a s x h1)). Qed.
Lemma lem3866639 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term173 A s x a.
Proof. exact (proj2 (@lem3866638 A a s x h1)). Qed.
Lemma lem3866646 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866654 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3866686 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term187 A s x.
Proof. exact (h1). Qed.
Lemma lem3866702 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3866704 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866706 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term187 A s x.
Proof. exact (proj2 (@lem3866629 A a s x h1)). Qed.
Lemma lem3866708 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3866712 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term187 A s x.
Proof. exact (proj2 (@lem3866629 A a s x h1)). Qed.
Lemma lem3866724 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term187 A s x.
Proof. exact (h1). Qed.
Lemma lem3866730 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term143 A x a.
Proof. exact (proj1 (@lem3866638 A a s x h1)). Qed.
Lemma lem3866732 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3866760 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866761 {A : Type'} (s : A -> Prop) : (term188 A s) = (term188 A s).
Proof. exact (eq_refl (term188 A s)). Qed.
Lemma lem3866762 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term189 A s x) = (term189 A s a).
Proof. exact (MK_COMB (@lem3866761 A s) (@lem3866708 A x a h1)). Qed.
Lemma lem3866763 {A : Type'} (s : A -> Prop) (a : A) : (term189 A s a) = (term187 A s a).
Proof. exact (eq_refl (term189 A s a)). Qed.
Lemma lem3866764 {A : Type'} (s : A -> Prop) (x : A) : (term190 A s x) = (term190 A s x).
Proof. exact (eq_refl (term190 A s x)). Qed.
Lemma lem3866765 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term189 A s a)) = ((term189 A s x) = (term187 A s a)).
Proof. exact (MK_COMB (@lem3866764 A s x) (@lem3866763 A s a)). Qed.
Lemma lem3866766 {A : Type'} (s : A -> Prop) (x : A) : (term189 A s x) = (term187 A s x).
Proof. exact (eq_refl (term189 A s x)). Qed.
Lemma lem3866767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3866768 {A : Type'} (s : A -> Prop) (x : A) : (term190 A s x) = (term191 A s x).
Proof. exact (MK_COMB (@lem3866767) (@lem3866766 A s x)). Qed.
Lemma lem3866769 {A : Type'} (s : A -> Prop) (a : A) : (term187 A s a) = (term187 A s a).
Proof. exact (eq_refl (term187 A s a)). Qed.
Lemma lem3866770 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term187 A s a)) = ((term187 A s x) = (term187 A s a)).
Proof. exact (MK_COMB (@lem3866768 A s x) (@lem3866769 A s a)). Qed.
Lemma lem3866771 {A : Type'} (x : A) (s : A -> Prop) (a : A) : ((term189 A s x) = (term189 A s a)) = ((term187 A s x) = (term187 A s a)).
Proof. exact (TRANS (@lem3866765 A x s a) (@lem3866770 A x s a)). Qed.
Lemma lem3866772 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : x = a) : (term187 A s x) = (term187 A s a).
Proof. exact (EQ_MP (@lem3866771 A x s a) (@lem3866762 A s x a h1)). Qed.
Lemma lem3866773 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term186 A a s x) (h2 : x = a) : term187 A s a.
Proof. exact (EQ_MP (@lem3866772 A s x a h2) (@lem3866706 A a s x h1)). Qed.
Lemma lem3866815 {A : Type'} (a : A) : (term192 A a) = (term192 A a).
Proof. exact (eq_refl (term192 A a)). Qed.
Lemma lem3866816 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term193 A a x) = (term194 A a).
Proof. exact (MK_COMB (@lem3866815 A a) (@lem3866732 A x a h1)). Qed.
Lemma lem3866817 {A : Type'} (a : A) : (term194 A a) = (term112 A a).
Proof. exact (eq_refl (term194 A a)). Qed.
Lemma lem3866818 {A : Type'} (a : A) (x : A) : (term195 A a x) = (term195 A a x).
Proof. exact (eq_refl (term195 A a x)). Qed.
Lemma lem3866819 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term194 A a)) = ((term193 A a x) = (term112 A a)).
Proof. exact (MK_COMB (@lem3866818 A a x) (@lem3866817 A a)). Qed.
Lemma lem3866820 {A : Type'} (x : A) (a : A) : (term193 A a x) = (term143 A x a).
Proof. exact (eq_refl (term193 A a x)). Qed.
Lemma lem3866821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3866822 {A : Type'} (x : A) (a : A) : (term195 A a x) = (term196 A x a).
Proof. exact (MK_COMB (@lem3866821) (@lem3866820 A x a)). Qed.
Lemma lem3866823 {A : Type'} (a : A) : (term112 A a) = (term112 A a).
Proof. exact (eq_refl (term112 A a)). Qed.
Lemma lem3866824 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term112 A a)) = ((term143 A x a) = (term112 A a)).
Proof. exact (MK_COMB (@lem3866822 A x a) (@lem3866823 A a)). Qed.
Lemma lem3866825 {A : Type'} (x : A) (a : A) : ((term193 A a x) = (term194 A a)) = ((term143 A x a) = (term112 A a)).
Proof. exact (TRANS (@lem3866819 A x a) (@lem3866824 A x a)). Qed.
Lemma lem3866826 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term143 A x a) = (term112 A a).
Proof. exact (EQ_MP (@lem3866825 A x a) (@lem3866816 A x a h1)). Qed.
Lemma lem3866827 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term112 A a.
Proof. exact (EQ_MP (@lem3866826 A x a h2) (@lem3866730 A a s x h1)). Qed.
Lemma lem3866829 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (h1). Qed.
Lemma lem3866830 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term197 A s a.
Proof. exact (fun h0 : term187 A s a => @lem3866829 A s a h1). Qed.
Lemma lem3866832 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866833 {A : Type'} (s : A -> Prop) (a : A) : (term197 A s a) = (s a).
Proof. exact (@lem3866832 (s a)). Qed.
Lemma lem3866834 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : s a.
Proof. exact (EQ_MP (@lem3866833 A s a) (@lem3866830 A s a h1)). Qed.
Lemma lem3866837 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3866839 {A : Type'} (s : A -> Prop) (a : A) : (term187 A s a) = (term199 A s a).
Proof. exact (@lem3866837 (s a)). Qed.
Lemma lem3866842 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term186 A a s x) (h2 : x = a) : term199 A s a.
Proof. exact (EQ_MP (@lem3866839 A s a) (@lem3866773 A s x a h1 h2)). Qed.
Lemma lem3866845 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (@lem3866842 A s x a h2 h3 (@lem3866834 A s a h1)). Qed.
Lemma lem3866846 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : term200.
Proof. exact (fun h0 : ~ False => @lem3866845 A s x a h1 h2 h3). Qed.
Lemma lem3866848 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866849 : term200 = False.
Proof. exact (@lem3866848 False). Qed.
Lemma lem3866850 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866849) (@lem3866846 A s x a h1 h2 h3)). Qed.
Lemma lem3866866 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : s x.
Proof. exact (proj1 (@lem3866634 A s x a h1)). Qed.
Lemma lem3866867 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : term197 A s x.
Proof. exact (fun h0 : term187 A s x => @lem3866866 A s x a h1). Qed.
Lemma lem3866869 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866870 {A : Type'} (s : A -> Prop) (x : A) : (term197 A s x) = (s x).
Proof. exact (@lem3866869 (s x)). Qed.
Lemma lem3866871 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term144 A s x a) : s x.
Proof. exact (EQ_MP (@lem3866870 A s x) (@lem3866867 A s x a h1)). Qed.
Lemma lem3866874 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3866876 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term199 A s x).
Proof. exact (@lem3866874 (s x)). Qed.
Lemma lem3866879 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term186 A a s x) : term199 A s x.
Proof. exact (EQ_MP (@lem3866876 A s x) (@lem3866712 A a s x h1)). Qed.
Lemma lem3866882 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : False.
Proof. exact (@lem3866879 A a s x h2 (@lem3866871 A s x a h1)). Qed.
Lemma lem3866883 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : term200.
Proof. exact (fun h0 : ~ False => @lem3866882 A a s x h1 h2). Qed.
Lemma lem3866885 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866886 : term200 = False.
Proof. exact (@lem3866885 False). Qed.
Lemma lem3866887 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term144 A s x a) (h2 : term186 A a s x) : False.
Proof. exact (EQ_MP (@lem3866886) (@lem3866883 A a s x h1 h2)). Qed.
Lemma lem3866903 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : s x.
Proof. exact (proj2 (@lem3866630 A a s x h1)). Qed.
Lemma lem3866904 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : term197 A s x.
Proof. exact (fun h0 : term187 A s x => @lem3866903 A a s x h1). Qed.
Lemma lem3866906 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866907 {A : Type'} (s : A -> Prop) (x : A) : (term197 A s x) = (s x).
Proof. exact (@lem3866906 (s x)). Qed.
Lemma lem3866908 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : s x.
Proof. exact (EQ_MP (@lem3866907 A s x) (@lem3866904 A a s x h1)). Qed.
Lemma lem3866911 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3866913 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (term199 A s x).
Proof. exact (@lem3866911 (s x)). Qed.
Lemma lem3866916 {A : Type'} (s : A -> Prop) (x : A) (h1 : term187 A s x) : term199 A s x.
Proof. exact (EQ_MP (@lem3866913 A s x) (@lem3866724 A s x h1)). Qed.
Lemma lem3866919 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (@lem3866916 A s x h1 (@lem3866908 A a s x h2)). Qed.
Lemma lem3866920 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : term200.
Proof. exact (fun h0 : ~ False => @lem3866919 A a s x h1 h2). Qed.
Lemma lem3866922 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866923 : term200 = False.
Proof. exact (@lem3866922 False). Qed.
Lemma lem3866924 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3866923) (@lem3866920 A a s x h1 h2)). Qed.
Lemma lem3866940 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3866941 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3866940 A x). Qed.
Lemma lem3866942 {A : Type'} (a : A) : a = a.
Proof. exact (@lem3866941 A a). Qed.
Lemma lem3866943 {A : Type'} (a : A) : term201 A a.
Proof. exact (fun h0 : term112 A a => @lem3866942 A a). Qed.
Lemma lem3866945 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866946 {A : Type'} (a : A) : (term201 A a) = (a = a).
Proof. exact (@lem3866945 (a = a)). Qed.
Lemma lem3866947 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem3866946 A a) (@lem3866943 A a)). Qed.
Lemma lem3866950 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3866952 {A : Type'} (a : A) : (term112 A a) = (term202 A a).
Proof. exact (@lem3866950 (a = a)). Qed.
Lemma lem3866955 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term202 A a.
Proof. exact (EQ_MP (@lem3866952 A a) (@lem3866827 A s x a h1 h2)). Qed.
Lemma lem3866958 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (@lem3866955 A s x a h1 h2 (@lem3866947 A a)). Qed.
Lemma lem3866959 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : term200.
Proof. exact (fun h0 : ~ False => @lem3866958 A s x a h1 h2). Qed.
Lemma lem3866961 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3866962 : term200 = False.
Proof. exact (@lem3866961 False). Qed.
Lemma lem3866964 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3866962) (@lem3866959 A s x a h1 h2)). Qed.
Lemma lem3866965 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3866850 A s x a h1 h2 h3) (fun h4 : False => @lem3866760 A s a h1)). Qed.
Lemma lem3866967 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866965 A s x a h1 h2 h3) (@lem3866760 A s a h1)). Qed.
Lemma lem3866968 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3866964 A s x a h1 h2) (fun h3 : False => @lem3866732 A x a h2)). Qed.
Lemma lem3866969 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3866968 A s x a h1 h2) (@lem3866732 A x a h2)). Qed.
Lemma lem3866970 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3866924 A a s x h1 h2) (fun h3 : False => @lem3866724 A s x h1)). Qed.
Lemma lem3866971 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3866970 A a s x h1 h2) (@lem3866724 A s x h1)). Qed.
Lemma lem3866972 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3866967 A s x a h1 h2 h3) (fun h4 : False => @lem3866708 A x a h3)). Qed.
Lemma lem3866973 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866972 A s x a h1 h2 h3) (@lem3866708 A x a h3)). Qed.
Lemma lem3866974 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3866973 A s x a h1 h2 h3) (fun h4 : False => @lem3866704 A s a h1)). Qed.
Lemma lem3866975 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866974 A s x a h1 h2 h3) (@lem3866704 A s a h1)). Qed.
Lemma lem3866976 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3866969 A s x a h1 h2) (fun h3 : False => @lem3866702 A x a h2)). Qed.
Lemma lem3866977 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3866976 A s x a h1 h2) (@lem3866702 A x a h2)). Qed.
Lemma lem3866978 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3866971 A a s x h1 h2) (fun h3 : False => @lem3866686 A s x h1)). Qed.
Lemma lem3866979 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3866978 A a s x h1 h2) (@lem3866686 A s x h1)). Qed.
Lemma lem3866980 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3866975 A s x a h1 h2 h3) (fun h4 : False => @lem3866654 A x a h3)). Qed.
Lemma lem3866981 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866980 A s x a h1 h2 h3) (@lem3866654 A x a h3)). Qed.
Lemma lem3866982 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3866981 A s x a h1 h2 h3) (fun h4 : False => @lem3866646 A s a h1)). Qed.
Lemma lem3866983 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866982 A s x a h1 h2 h3) (@lem3866646 A s a h1)). Qed.
Lemma lem3866984 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3866977 A s x a h1 h2) (fun h3 : False => @lem3866702 A x a h2)). Qed.
Lemma lem3866985 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term182 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3866984 A s x a h1 h2) (@lem3866702 A x a h2)). Qed.
Lemma lem3866986 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : (term187 A s x) = False.
Proof. exact (prop_ext (fun h3 : term187 A s x => @lem3866979 A a s x h1 h2) (fun h3 : False => @lem3866686 A s x h1)). Qed.
Lemma lem3866987 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term187 A s x) (h2 : term182 A a s x) : False.
Proof. exact (EQ_MP (@lem3866986 A a s x h1 h2) (@lem3866686 A s x h1)). Qed.
Lemma lem3866988 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h4 : x = a => @lem3866983 A s x a h1 h2 h3) (fun h4 : False => @lem3866654 A x a h3)). Qed.
Lemma lem3866989 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866988 A s x a h1 h2 h3) (@lem3866654 A x a h3)). Qed.
Lemma lem3866990 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : (s a) = False.
Proof. exact (prop_ext (fun h4 : s a => @lem3866989 A s x a h1 h2 h3) (fun h4 : False => @lem3866646 A s a h1)). Qed.
Lemma lem3866991 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : s a) (h2 : term186 A a s x) (h3 : x = a) : False.
Proof. exact (EQ_MP (@lem3866990 A s x a h1 h2 h3) (@lem3866646 A s a h1)). Qed.
Lemma lem3866992 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term182 A a s x) : False.
Proof. exact (or_elim (@lem3866639 A a s x h1) (fun h0 : term187 A s x => @lem3866987 A a s x h0 h1) (fun h0 : x = a => @lem3866985 A s x a h1 h0)). Qed.
Lemma lem3866993 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : s a) (h2 : term186 A a s x) : False.
Proof. exact (or_elim (@lem3866632 A a s x h2) (fun h0 : x = a => @lem3866991 A s x a h1 h2 h0) (fun h0 : term144 A s x a => @lem3866887 A a s x h0 h2)). Qed.
Lemma lem3866994 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (or_elim (@lem3866628 A a s x h1) (fun h0 : term186 A a s x => @lem3866993 A a s x h2 h0) (fun h0 : term182 A a s x => @lem3866992 A a s x h0)). Qed.
Lemma lem3866995 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3866994 A x s a h1 h2) (fun h3 : False => @lem3866566 A s a h2)). Qed.
Lemma lem3866996 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3866995 A x s a h1 h2) (@lem3866566 A s a h2)). Qed.
Lemma lem3866997 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (s a) = False.
Proof. exact (prop_ext (fun h3 : s a => @lem3866996 A x s a h1 h2) (fun h3 : False => @lem3866520 A s a h2)). Qed.
Lemma lem3866998 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3866997 A x s a h1 h2) (@lem3866520 A s a h2)). Qed.
Lemma lem3866999 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : (term169 A a s x) = False.
Proof. exact (prop_ext (fun h3 : term169 A a s x => @lem3866998 A x s a h1 h2) (fun h3 : False => @lem3866514 A a s x h1)). Qed.
Lemma lem3867000 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : term169 A a s x) (h2 : s a) : False.
Proof. exact (EQ_MP (@lem3866999 A x s a h1 h2) (@lem3866514 A a s x h1)). Qed.
Lemma lem3867001 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : term168 A a s x.
Proof. exact (fun h0 : term169 A a s x => @lem3867000 A x s a h0 h1). Qed.
Lemma lem3867002 {A : Type'} (x : A) (s : A -> Prop) (a : A) (h1 : s a) : (term146 A s x a) = (s x).
Proof. exact (EQ_MP (@lem3866513 A a s x) (@lem3867001 A x s a h1)). Qed.
Lemma lem3867007 {A : Type'} (s : A -> Prop) (a : A) (h1 : s a) : term151 A a s.
Proof. exact (fun x : A => @lem3867002 A x s a h1). Qed.
Lemma lem3867008 {A : Type'} (a : A) (s : A -> Prop) : term152 A a s.
Proof. exact (fun h0 : s a => @lem3867007 A s a h0). Qed.
Lemma lem3867013 {A : Type'} (s : A -> Prop) : term163 A s.
Proof. exact (fun a : A => @lem3867008 A a s). Qed.
Lemma lem3867018 {A : Type'} : term167 A.
Proof. exact (fun s : A -> Prop => @lem3867013 A s). Qed.
Lemma lem3867019 {A : Type'} : term166 A.
Proof. exact (EQ_MP (@lem3866508 A) (@lem3867018 A)). Qed.
Lemma lem3867020 {A : Type'} (s : A -> Prop) : term203 A s.
Proof. exact (@lem3867019 A s). Qed.
Lemma lem3867021 {A : Type'} (s : A -> Prop) : (term203 A s) = (term162 A s).
Proof. exact (eq_refl (term203 A s)). Qed.
Lemma lem3867022 {A : Type'} (s : A -> Prop) : term162 A s.
Proof. exact (EQ_MP (@lem3867021 A s) (@lem3867020 A s)). Qed.
Lemma lem3867023 {A : Type'} (s : A -> Prop) (a : A) : term204 A s a.
Proof. exact (@lem3867022 A s a). Qed.
Lemma lem3867024 {A : Type'} (a : A) (s : A -> Prop) : (term204 A s a) = (term154 A a s).
Proof. exact (eq_refl (term204 A s a)). Qed.
Lemma lem3867025 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (EQ_MP (@lem3867024 A a s) (@lem3867023 A s a)). Qed.
Lemma lem3867027 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (@lem3866409 A a s (@lem3867025 A a s)). Qed.
Lemma lem3867028 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : False.
Proof. exact (@lem3867027 A a s (@lem3866393 A a s h1)). Qed.
Lemma lem3867029 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : (term155 A a s) = False.
Proof. exact (prop_ext (fun h2 : term155 A a s => @lem3867028 A a s h1) (fun h2 : False => @lem3866393 A a s h1)). Qed.
Lemma lem3867030 {A : Type'} (a : A) (s : A -> Prop) (h1 : term155 A a s) : False.
Proof. exact (EQ_MP (@lem3867029 A a s h1) (@lem3866393 A a s h1)). Qed.
Lemma lem3867031 {A : Type'} (a : A) (s : A -> Prop) : term154 A a s.
Proof. exact (fun h0 : term155 A a s => @lem3867030 A a s h0). Qed.
Lemma lem3867032 {A : Type'} (a : A) (s : A -> Prop) : term152 A a s.
Proof. exact (EQ_MP (@lem3866392 A a s) (@lem3867031 A a s)). Qed.
Lemma lem3867033 {A : Type'} (a : A) (s : A -> Prop) : term136 A a s.
Proof. exact (EQ_MP (@lem3866388 A a s) (@lem3867032 A a s)). Qed.
Lemma lem3867034 {A : Type'} (a : A) (s : A -> Prop) : term135 A a s.
Proof. exact (EQ_MP (@lem3866322 A a s) (@lem3867033 A a s)). Qed.
Lemma lem3867035 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (term126 A s a) = s.
Proof. exact (@lem3867034 A a s (@lem3866177 A a s h1)). Qed.
Lemma lem3867037 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3867038 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term248 A a s n) = (term251 A a s n).
Proof. exact (@lem3867037 (term248 A a s n)). Qed.
Lemma lem3867039 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term251 A a s n) = (term248 A a s n).
Proof. exact (SYM (@lem3867038 A a s n)). Qed.
Lemma lem3867040 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term252 A a s n) : term252 A a s n.
Proof. exact (h1). Qed.
Lemma lem3867043 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term253 A a s n) : term253 A a s n.
Proof. exact (h1). Qed.
Lemma lem3867044 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term254 A a s n.
Proof. exact (fun h0 : term253 A a s n => @lem3867043 A a s n h0). Qed.
Lemma lem3867045 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term254 A a s n) : term254 A a s n.
Proof. exact (h1). Qed.
Lemma lem3867046 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term253 A a s n) : term253 A a s n.
Proof. exact (h1). Qed.
Lemma lem3867047 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term253 A a s n) (h2 : term254 A a s n) : term253 A a s n.
Proof. exact (@lem3867045 A a s n h2 (@lem3867046 A a s n h1)). Qed.
Lemma lem3867048 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term253 A a s n) : term255 A a s n.
Proof. exact (fun h0 : term254 A a s n => @lem3867047 A a s n h1 h0). Qed.
Lemma lem3867049 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term254 A a s n) : term254 A a s n.
Proof. exact (h1). Qed.
Lemma lem3867050 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term253 A a s n) (h2 : term254 A a s n) : term253 A a s n.
Proof. exact (@lem3867048 A a s n h1 (@lem3867049 A a s n h2)). Qed.
Lemma lem3867051 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term254 A a s n) : term254 A a s n.
Proof. exact (fun h0 : term253 A a s n => @lem3867050 A a s n h0 h1). Qed.
Lemma lem3867052 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term256 A a s n.
Proof. exact (fun h0 : term254 A a s n => @lem3867051 A a s n h0). Qed.
Lemma lem3867055 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term254 A a s n.
Proof. exact (@lem3867052 A a s n (@lem3867044 A a s n)). Qed.
Lemma lem3867056 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term254 A a s n.
Proof. exact (@lem3867055 A a s n). Qed.
Lemma lem3867084 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3867085 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term251 A a s n) = (term257 A a s n).
Proof. exact (@lem3867084 (term252 A a s n)). Qed.
Lemma lem3867087 (t : Prop) : (term99 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3867088 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term257 A a s n) = (term248 A a s n).
Proof. exact (@lem3867087 (term248 A a s n)). Qed.
Lemma lem3867091 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term251 A a s n) = (term248 A a s n).
Proof. exact (TRANS (@lem3867085 A a s n) (@lem3867088 A a s n)). Qed.
Lemma lem3867092 {A : Type'} (a : A) (s : A -> Prop) : (term31 A a s) = (term31 A a s).
Proof. exact (eq_refl (term31 A a s)). Qed.
Lemma lem3867093 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term258 A a s n) = (term259 A a s n).
Proof. exact (MK_COMB (@lem3867092 A a s) (@lem3867091 A a s n)). Qed.
Lemma lem3867096 {A : Type'} (s : A -> Prop) (n : nat) : (term260 A s n) = (term260 A s n).
Proof. exact (eq_refl (term260 A s n)). Qed.
Lemma lem3867097 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term261 A a s n) = (term262 A a s n).
Proof. exact (MK_COMB (@lem3867096 A s n) (@lem3867093 A a s n)). Qed.
Lemma lem3867100 {A : Type'} (s : A -> Prop) : (term263 A s) = (term263 A s).
Proof. exact (eq_refl (term263 A s)). Qed.
Lemma lem3867101 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term264 A a s n) = (term265 A a s n).
Proof. exact (MK_COMB (@lem3867100 A s) (@lem3867097 A a s n)). Qed.
Lemma lem3867104 {A : Type'} (s : A -> Prop) : (term266 A s) = (term266 A s).
Proof. exact (eq_refl (term266 A s)). Qed.
Lemma lem3867105 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term253 A a s n) = (term267 A a s n).
Proof. exact (MK_COMB (@lem3867104 A s) (@lem3867101 A a s n)). Qed.
Lemma lem3867108 {A : Type'} (s : A -> Prop) (n : nat) : (term268 A s n) = (term269 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867105 A a s n)). Qed.
Lemma lem3867109 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867110 {A : Type'} (s : A -> Prop) (n : nat) : (term270 A s n) = (term271 A s n).
Proof. exact (MK_COMB (@lem3867109 A) (@lem3867108 A s n)). Qed.
Lemma lem3867115 {A : Type'} (n : nat) : (term272 A n) = (term273 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3867110 A s n)). Qed.
Lemma lem3867116 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3867117 {A : Type'} (n : nat) : (term274 A n) = (term275 A n).
Proof. exact (MK_COMB (@lem3867116 A) (@lem3867115 A n)). Qed.
Lemma lem3867122 {A : Type'} : (term276 A) = (term277 A).
Proof. exact (fun_ext (fun n : nat => @lem3867117 A n)). Qed.
Lemma lem3867123 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3867132 {A : Type'} : (term278 A) = (term279 A).
Proof. exact (MK_COMB (@lem3867123) (@lem3867122 A)). Qed.
Lemma lem3867141 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term259 A a s n) = (term259 A a s n).
Proof. exact (eq_refl (term259 A a s n)). Qed.
Lemma lem3867146 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term72 A s a n) = (term72 A s a n).
Proof. exact (eq_refl (term72 A s a n)). Qed.
Lemma lem3867147 {A : Type'} (s : A -> Prop) (n : nat) : (term73 A s n) = (term73 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867146 A s a n)). Qed.
Lemma lem3867148 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867149 {A : Type'} (s : A -> Prop) (n : nat) : (term74 A s n) = (term74 A s n).
Proof. exact (MK_COMB (@lem3867148 A) (@lem3867147 A s n)). Qed.
Lemma lem3867150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3867151 {A : Type'} (s : A -> Prop) (n : nat) : (term260 A s n) = (term260 A s n).
Proof. exact (MK_COMB (@lem3867150) (@lem3867149 A s n)). Qed.
Lemma lem3867152 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term262 A a s n) = (term262 A a s n).
Proof. exact (MK_COMB (@lem3867151 A s n) (@lem3867141 A a s n)). Qed.
Lemma lem3867155 {A : Type'} (s : A -> Prop) : (term263 A s) = (term263 A s).
Proof. exact (eq_refl (term263 A s)). Qed.
Lemma lem3867156 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term265 A a s n) = (term265 A a s n).
Proof. exact (MK_COMB (@lem3867155 A s) (@lem3867152 A a s n)). Qed.
Lemma lem3867161 {A : Type'} (s : A -> Prop) : (term266 A s) = (term266 A s).
Proof. exact (eq_refl (term266 A s)). Qed.
Lemma lem3867162 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term267 A a s n) = (term267 A a s n).
Proof. exact (MK_COMB (@lem3867161 A s) (@lem3867156 A a s n)). Qed.
Lemma lem3867163 {A : Type'} (s : A -> Prop) (n : nat) : (term269 A s n) = (term269 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867162 A a s n)). Qed.
Lemma lem3867164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867165 {A : Type'} (s : A -> Prop) (n : nat) : (term271 A s n) = (term271 A s n).
Proof. exact (MK_COMB (@lem3867164 A) (@lem3867163 A s n)). Qed.
Lemma lem3867166 {A : Type'} (n : nat) : (term273 A n) = (term273 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3867165 A s n)). Qed.
Lemma lem3867167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3867168 {A : Type'} (n : nat) : (term275 A n) = (term275 A n).
Proof. exact (MK_COMB (@lem3867167 A) (@lem3867166 A n)). Qed.
Lemma lem3867169 {A : Type'} : (term277 A) = (term277 A).
Proof. exact (fun_ext (fun n : nat => @lem3867168 A n)). Qed.
Lemma lem3867170 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3867171 {A : Type'} : (term279 A) = (term279 A).
Proof. exact (MK_COMB (@lem3867170) (@lem3867169 A)). Qed.
Lemma lem3867210 {A : Type'} : (term278 A) = (term279 A).
Proof. exact (TRANS (@lem3867132 A) (@lem3867171 A)). Qed.
Lemma lem3867211 {A : Type'} : (term279 A) = (term278 A).
Proof. exact (SYM (@lem3867210 A)). Qed.
Lemma lem3867214 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term74 A s n.
Proof. exact (h1). Qed.
Lemma lem3867218 (p : Prop) : p = (term153 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3867219 {A : Type'} (s : A -> Prop) (n : nat) : ((@CARD A s) = (S n)) = (term280 A s n).
Proof. exact (@lem3867218 ((@CARD A s) = (S n))). Qed.
Lemma lem3867220 {A : Type'} (s : A -> Prop) (n : nat) : (term280 A s n) = ((@CARD A s) = (S n)).
Proof. exact (SYM (@lem3867219 A s n)). Qed.
Lemma lem3867221 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term281 A s n.
Proof. exact (h1). Qed.
Lemma lem3867240 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term72 A s a n) = (term282 A s a n).
Proof. exact (@lem17265 (@IN A a s) ((term54 A s a) = n)). Qed.
Lemma lem3867241 {A : Type'} (s : A -> Prop) (n : nat) : (term73 A s n) = (term283 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867240 A s a n)). Qed.
Lemma lem3867242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867295 {A : Type'} (s : A -> Prop) (n : nat) : (term74 A s n) = (term284 A s n).
Proof. exact (MK_COMB (@lem3867242 A) (@lem3867241 A s n)). Qed.
Lemma lem3867296 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term284 A s n.
Proof. exact (EQ_MP (@lem3867295 A s n) (@lem3867214 A s n h1)). Qed.
Lemma lem3867302 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3867308 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (h1). Qed.
Lemma lem3867314 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term281 A s n.
Proof. exact (h1). Qed.
Lemma lem3867347 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term282 A s a n) = (term282 A s a n).
Proof. exact (eq_refl (term282 A s a n)). Qed.
Lemma lem3867348 {A : Type'} (s : A -> Prop) (n : nat) : (term283 A s n) = (term283 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867347 A s a n)). Qed.
Lemma lem3867349 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867350 {A : Type'} (s : A -> Prop) (n : nat) : (term284 A s n) = (term284 A s n).
Proof. exact (MK_COMB (@lem3867349 A) (@lem3867348 A s n)). Qed.
Lemma lem3867351 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term284 A s n.
Proof. exact (EQ_MP (@lem3867350 A s n) (@lem3867296 A s n h1)). Qed.
Lemma lem3867357 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3867373 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (h1). Qed.
Lemma lem3867385 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term281 A s n.
Proof. exact (h1). Qed.
Lemma lem3867401 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term282 A s a n) = (term282 A s a n).
Proof. exact (eq_refl (term282 A s a n)). Qed.
Lemma lem3867402 {A : Type'} (s : A -> Prop) (n : nat) : (term283 A s n) = (term283 A s n).
Proof. exact (fun_ext (fun a : A => @lem3867401 A s a n)). Qed.
Lemma lem3867403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3867405 {A : Type'} (s : A -> Prop) (n : nat) : (term284 A s n) = (term284 A s n).
Proof. exact (MK_COMB (@lem3867403 A) (@lem3867402 A s n)). Qed.
Lemma lem3867406 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term284 A s n.
Proof. exact (EQ_MP (@lem3867405 A s n) (@lem3867351 A s n h1)). Qed.
Lemma lem3867410 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3867414 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (h1). Qed.
Lemma lem3867418 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term281 A s n.
Proof. exact (h1). Qed.
Lemma lem3867419 {A : Type'} (_44820 : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term285 A s n _44820.
Proof. exact (@lem3867406 A s n h1 _44820). Qed.
Lemma lem3867420 {A : Type'} (s : A -> Prop) (_44820 : A) (n : nat) : (term285 A s n _44820) = (term282 A s _44820 n).
Proof. exact (eq_refl (term285 A s n _44820)). Qed.
Lemma lem3867431 {A : Type'} (_44820 : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term282 A s _44820 n.
Proof. exact (EQ_MP (@lem3867420 A s _44820 n) (@lem3867419 A _44820 s n h1)). Qed.
Lemma lem3867433 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3867435 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (h1). Qed.
Lemma lem3867437 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term281 A s n.
Proof. exact (h1). Qed.
Lemma lem3867469 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3867470 (_44827 : nat) (_44828 : nat) (h1 : _44827 = _44828) : _44827 = _44828.
Proof. exact (h1). Qed.
Lemma lem3867471 (_44827 : nat) (_44828 : nat) (h1 : _44827 = _44828) : (S _44827) = (S _44828).
Proof. exact (MK_COMB (@lem3867469) (@lem3867470 _44827 _44828 h1)). Qed.
Lemma lem3867472 (_44827 : nat) (_44828 : nat) : term286 _44827 _44828.
Proof. exact (fun h0 : _44827 = _44828 => @lem3867471 _44827 _44828 h0). Qed.
Lemma lem3867474 (a : Prop) (b : Prop) : (a -> b) = (term287 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3867475 (_44827 : nat) (_44828 : nat) : (term286 _44827 _44828) = (term288 _44827 _44828).
Proof. exact (@lem3867474 (_44827 = _44828) ((S _44827) = (S _44828))). Qed.
Lemma lem3867476 (_44827 : nat) (_44828 : nat) : term288 _44827 _44828.
Proof. exact (EQ_MP (@lem3867475 _44827 _44828) (@lem3867472 _44827 _44828)). Qed.
Lemma lem3867501 (x : nat) (y : nat) (z : nat) : term289 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem3867507 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (h1). Qed.
Lemma lem3867508 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : term290 A s a.
Proof. exact (fun h0 : term291 A s a => @lem3867507 A s a h1). Qed.
Lemma lem3867510 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867511 {A : Type'} (s : A -> Prop) (a : A) : (term290 A s a) = ((@CARD A s) = (term116 A s a)).
Proof. exact (@lem3867510 ((@CARD A s) = (term116 A s a))). Qed.
Lemma lem3867512 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (@CARD A s) = (term116 A s a).
Proof. exact (EQ_MP (@lem3867511 A s a) (@lem3867508 A s a h1)). Qed.
Lemma lem3867514 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3867515 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (@lem3867514 (@CARD A s)). Qed.
Lemma lem3867516 {A : Type'} (s : A -> Prop) : term292 A s.
Proof. exact (fun h0 : term293 A s => @lem3867515 A s). Qed.
Lemma lem3867518 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867519 {A : Type'} (s : A -> Prop) : (term292 A s) = ((@CARD A s) = (@CARD A s)).
Proof. exact (@lem3867518 ((@CARD A s) = (@CARD A s))). Qed.
Lemma lem3867520 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (EQ_MP (@lem3867519 A s) (@lem3867516 A s)). Qed.
Lemma lem3867538 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3867539 (y : nat) (x : nat) (z : nat) : (term294 x y z) = (term295 y x z).
Proof. exact (@lem3867538 (y = z) (term296 x z)). Qed.
Lemma lem3867549 (x : nat) (y : nat) : (term297 x y) = (term297 x y).
Proof. exact (eq_refl (term297 x y)). Qed.
Lemma lem3867550 (y : nat) (x : nat) (z : nat) : (term289 x y z) = (term298 y x z).
Proof. exact (MK_COMB (@lem3867549 x y) (@lem3867539 y x z)). Qed.
Lemma lem3867554 (q : Prop) (p : Prop) (r : Prop) : (term299 p q r) = (term299 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3867555 (y : nat) (x : nat) (z : nat) : (term298 y x z) = (term300 y x z).
Proof. exact (@lem3867554 (y = z) (term296 x y) (term296 x z)). Qed.
Lemma lem3867577 (y : nat) (x : nat) (z : nat) : (term289 x y z) = (term300 y x z).
Proof. exact (TRANS (@lem3867550 y x z) (@lem3867555 y x z)). Qed.
Lemma lem3867578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3867579 (y : nat) (x : nat) (z : nat) : (term301 x y z) = (term302 y x z).
Proof. exact (MK_COMB (@lem3867578) (@lem3867577 y x z)). Qed.
Lemma lem3867601 (y : nat) (x : nat) (z : nat) : (term300 y x z) = (term300 y x z).
Proof. exact (eq_refl (term300 y x z)). Qed.
Lemma lem3867602 (y : nat) (x : nat) (z : nat) : ((term289 x y z) = (term300 y x z)) = ((term300 y x z) = (term300 y x z)).
Proof. exact (MK_COMB (@lem3867579 y x z) (@lem3867601 y x z)). Qed.
Lemma lem3867604 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3867605 (x : Prop) : (x = x) = True.
Proof. exact (@lem3867604 Prop x). Qed.
Lemma lem3867606 (y : nat) (x : nat) (z : nat) : ((term300 y x z) = (term300 y x z)) = True.
Proof. exact (@lem3867605 (term300 y x z)). Qed.
Lemma lem3867607 (y : nat) (x : nat) (z : nat) : ((term289 x y z) = (term300 y x z)) = True.
Proof. exact (TRANS (@lem3867602 y x z) (@lem3867606 y x z)). Qed.
Lemma lem3867608 (y : nat) (x : nat) (z : nat) : True = ((term289 x y z) = (term300 y x z)).
Proof. exact (SYM (@lem3867607 y x z)). Qed.
Lemma lem3867609 (y : nat) (x : nat) (z : nat) : (term289 x y z) = (term300 y x z).
Proof. exact (EQ_MP (@lem3867608 y x z) (@lem0)). Qed.
Lemma lem3867610 (y : nat) (x : nat) (z : nat) : term300 y x z.
Proof. exact (EQ_MP (@lem3867609 y x z) (@lem3867501 x y z)). Qed.
Lemma lem3867612 (b : Prop) (a : Prop) : (a \/ b) = (term303 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3867613 (x : nat) (y : nat) (z : nat) : (term300 y x z) = (term304 x y z).
Proof. exact (@lem3867612 (term305 y x z) (y = z)). Qed.
Lemma lem3867615 (a : Prop) (b : Prop) : (term306 a b) = (term307 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3867616 (y : nat) (x : nat) (z : nat) : (term308 y x z) = (term309 y x z).
Proof. exact (@lem3867615 (term296 x y) (term296 x z)). Qed.
Lemma lem3867618 (a : Prop) : (term99 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3867619 (x : nat) (y : nat) : (term310 x y) = (x = y).
Proof. exact (@lem3867618 (x = y)). Qed.
Lemma lem3867620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3867621 (x : nat) (y : nat) : (term311 x y) = (term312 x y).
Proof. exact (MK_COMB (@lem3867620) (@lem3867619 x y)). Qed.
Lemma lem3867623 (a : Prop) : (term99 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3867624 (x : nat) (z : nat) : (term310 x z) = (x = z).
Proof. exact (@lem3867623 (x = z)). Qed.
Lemma lem3867625 (y : nat) (x : nat) (z : nat) : (term309 y x z) = (term313 y x z).
Proof. exact (MK_COMB (@lem3867621 x y) (@lem3867624 x z)). Qed.
Lemma lem3867626 (y : nat) (x : nat) (z : nat) : (term308 y x z) = (term313 y x z).
Proof. exact (TRANS (@lem3867616 y x z) (@lem3867625 y x z)). Qed.
Lemma lem3867627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3867628 (y : nat) (x : nat) (z : nat) : (term314 y x z) = (term315 y x z).
Proof. exact (MK_COMB (@lem3867627) (@lem3867626 y x z)). Qed.
Lemma lem3867629 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3867630 (x : nat) (y : nat) (z : nat) : (term304 x y z) = (term316 x y z).
Proof. exact (MK_COMB (@lem3867628 y x z) (@lem3867629 y z)). Qed.
Lemma lem3867631 (x : nat) (y : nat) (z : nat) : (term300 y x z) = (term316 x y z).
Proof. exact (TRANS (@lem3867613 x y z) (@lem3867630 x y z)). Qed.
Lemma lem3867633 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : term317 A a s.
Proof. exact (conj (@lem3867512 A s a h1) (@lem3867520 A s)). Qed.
Lemma lem3867635 (x : nat) (y : nat) (z : nat) : term316 x y z.
Proof. exact (EQ_MP (@lem3867631 x y z) (@lem3867610 y x z)). Qed.
Lemma lem3867636 {A : Type'} (a : A) (s : A -> Prop) : term318 A a s.
Proof. exact (@lem3867635 (@CARD A s) (term116 A s a) (@CARD A s)). Qed.
Lemma lem3867639 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (term116 A s a) = (@CARD A s).
Proof. exact (@lem3867636 A a s (@lem3867633 A s a h1)). Qed.
Lemma lem3867640 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : term319 A a s.
Proof. exact (fun h0 : term320 A a s => @lem3867639 A s a h1). Qed.
Lemma lem3867642 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867643 {A : Type'} (a : A) (s : A -> Prop) : (term319 A a s) = ((term116 A s a) = (@CARD A s)).
Proof. exact (@lem3867642 ((term116 A s a) = (@CARD A s))). Qed.
Lemma lem3867644 {A : Type'} (s : A -> Prop) (a : A) (h1 : (@CARD A s) = (term116 A s a)) : (term116 A s a) = (@CARD A s).
Proof. exact (EQ_MP (@lem3867643 A a s) (@lem3867640 A s a h1)). Qed.
Lemma lem3867646 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem3867647 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : term321 A a s.
Proof. exact (fun h0 : term83 A a s => @lem3867646 A a s h1). Qed.
Lemma lem3867649 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867650 {A : Type'} (a : A) (s : A -> Prop) : (term321 A a s) = (@IN A a s).
Proof. exact (@lem3867649 (@IN A a s)). Qed.
Lemma lem3867651 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (EQ_MP (@lem3867650 A a s) (@lem3867647 A a s h1)). Qed.
Lemma lem3867657 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3867658 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : (term282 A s _44820 n) = (term322 A n _44820 s).
Proof. exact (@lem3867657 ((term54 A s _44820) = n) (term83 A _44820 s)). Qed.
Lemma lem3867666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3867667 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : (term323 A s _44820 n) = (term324 A n _44820 s).
Proof. exact (MK_COMB (@lem3867666) (@lem3867658 A n _44820 s)). Qed.
Lemma lem3867675 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : (term322 A n _44820 s) = (term322 A n _44820 s).
Proof. exact (eq_refl (term322 A n _44820 s)). Qed.
Lemma lem3867676 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : ((term282 A s _44820 n) = (term322 A n _44820 s)) = ((term322 A n _44820 s) = (term322 A n _44820 s)).
Proof. exact (MK_COMB (@lem3867667 A n _44820 s) (@lem3867675 A n _44820 s)). Qed.
Lemma lem3867678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3867679 (x : Prop) : (x = x) = True.
Proof. exact (@lem3867678 Prop x). Qed.
Lemma lem3867680 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : ((term322 A n _44820 s) = (term322 A n _44820 s)) = True.
Proof. exact (@lem3867679 (term322 A n _44820 s)). Qed.
Lemma lem3867681 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : ((term282 A s _44820 n) = (term322 A n _44820 s)) = True.
Proof. exact (TRANS (@lem3867676 A n _44820 s) (@lem3867680 A n _44820 s)). Qed.
Lemma lem3867682 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : True = ((term282 A s _44820 n) = (term322 A n _44820 s)).
Proof. exact (SYM (@lem3867681 A n _44820 s)). Qed.
Lemma lem3867683 {A : Type'} (n : nat) (_44820 : A) (s : A -> Prop) : (term282 A s _44820 n) = (term322 A n _44820 s).
Proof. exact (EQ_MP (@lem3867682 A n _44820 s) (@lem0)). Qed.
Lemma lem3867684 {A : Type'} (_44820 : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term322 A n _44820 s.
Proof. exact (EQ_MP (@lem3867683 A n _44820 s) (@lem3867431 A _44820 s n h1)). Qed.
Lemma lem3867686 (b : Prop) (a : Prop) : (a \/ b) = (term303 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3867687 {A : Type'} (s : A -> Prop) (_44820 : A) (n : nat) : (term322 A n _44820 s) = (term325 A s _44820 n).
Proof. exact (@lem3867686 (term83 A _44820 s) ((term54 A s _44820) = n)). Qed.
Lemma lem3867689 (a : Prop) : (term99 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3867690 {A : Type'} (_44820 : A) (s : A -> Prop) : (term95 A _44820 s) = (@IN A _44820 s).
Proof. exact (@lem3867689 (@IN A _44820 s)). Qed.
Lemma lem3867691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3867692 {A : Type'} (_44820 : A) (s : A -> Prop) : (term326 A _44820 s) = (term31 A _44820 s).
Proof. exact (MK_COMB (@lem3867691) (@lem3867690 A _44820 s)). Qed.
Lemma lem3867693 {A : Type'} (s : A -> Prop) (_44820 : A) (n : nat) : ((term54 A s _44820) = n) = ((term54 A s _44820) = n).
Proof. exact (eq_refl ((term54 A s _44820) = n)). Qed.
Lemma lem3867694 {A : Type'} (s : A -> Prop) (_44820 : A) (n : nat) : (term325 A s _44820 n) = (term72 A s _44820 n).
Proof. exact (MK_COMB (@lem3867692 A _44820 s) (@lem3867693 A s _44820 n)). Qed.
Lemma lem3867695 {A : Type'} (s : A -> Prop) (_44820 : A) (n : nat) : (term322 A n _44820 s) = (term72 A s _44820 n).
Proof. exact (TRANS (@lem3867687 A s _44820 n) (@lem3867694 A s _44820 n)). Qed.
Lemma lem3867698 {A : Type'} (_44820 : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term72 A s _44820 n.
Proof. exact (EQ_MP (@lem3867695 A s _44820 n) (@lem3867684 A _44820 s n h1)). Qed.
Lemma lem3867699 {A : Type'} (_44820 : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term72 A s _44820 n.
Proof. exact (@lem3867698 A _44820 s n h1). Qed.
Lemma lem3867700 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term72 A s a n.
Proof. exact (@lem3867699 A a s n h1). Qed.
Lemma lem3867703 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : (term54 A s a) = n.
Proof. exact (@lem3867700 A a s n h1 (@lem3867651 A a s h2)). Qed.
Lemma lem3867704 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : term327 A s a n.
Proof. exact (fun h0 : term231 A s a n => @lem3867703 A n a s h1 h2). Qed.
Lemma lem3867706 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867707 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term327 A s a n) = ((term54 A s a) = n).
Proof. exact (@lem3867706 ((term54 A s a) = n)). Qed.
Lemma lem3867708 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : (term54 A s a) = n.
Proof. exact (EQ_MP (@lem3867707 A s a n) (@lem3867704 A n a s h1 h2)). Qed.
Lemma lem3867714 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3867715 (_44827 : nat) (_44828 : nat) : (term288 _44827 _44828) = (term328 _44827 _44828).
Proof. exact (@lem3867714 ((S _44827) = (S _44828)) (term296 _44827 _44828)). Qed.
Lemma lem3867725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3867726 (_44827 : nat) (_44828 : nat) : (term329 _44827 _44828) = (term330 _44827 _44828).
Proof. exact (MK_COMB (@lem3867725) (@lem3867715 _44827 _44828)). Qed.
Lemma lem3867736 (_44827 : nat) (_44828 : nat) : (term328 _44827 _44828) = (term328 _44827 _44828).
Proof. exact (eq_refl (term328 _44827 _44828)). Qed.
Lemma lem3867737 (_44827 : nat) (_44828 : nat) : ((term288 _44827 _44828) = (term328 _44827 _44828)) = ((term328 _44827 _44828) = (term328 _44827 _44828)).
Proof. exact (MK_COMB (@lem3867726 _44827 _44828) (@lem3867736 _44827 _44828)). Qed.
Lemma lem3867739 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3867740 (x : Prop) : (x = x) = True.
Proof. exact (@lem3867739 Prop x). Qed.
Lemma lem3867741 (_44827 : nat) (_44828 : nat) : ((term328 _44827 _44828) = (term328 _44827 _44828)) = True.
Proof. exact (@lem3867740 (term328 _44827 _44828)). Qed.
Lemma lem3867742 (_44827 : nat) (_44828 : nat) : ((term288 _44827 _44828) = (term328 _44827 _44828)) = True.
Proof. exact (TRANS (@lem3867737 _44827 _44828) (@lem3867741 _44827 _44828)). Qed.
Lemma lem3867743 (_44827 : nat) (_44828 : nat) : True = ((term288 _44827 _44828) = (term328 _44827 _44828)).
Proof. exact (SYM (@lem3867742 _44827 _44828)). Qed.
Lemma lem3867744 (_44827 : nat) (_44828 : nat) : (term288 _44827 _44828) = (term328 _44827 _44828).
Proof. exact (EQ_MP (@lem3867743 _44827 _44828) (@lem0)). Qed.
Lemma lem3867745 (_44827 : nat) (_44828 : nat) : term328 _44827 _44828.
Proof. exact (EQ_MP (@lem3867744 _44827 _44828) (@lem3867476 _44827 _44828)). Qed.
Lemma lem3867747 (b : Prop) (a : Prop) : (a \/ b) = (term303 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3867748 (_44827 : nat) (_44828 : nat) : (term328 _44827 _44828) = (term331 _44827 _44828).
Proof. exact (@lem3867747 (term296 _44827 _44828) ((S _44827) = (S _44828))). Qed.
Lemma lem3867750 (a : Prop) : (term99 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3867751 (_44827 : nat) (_44828 : nat) : (term310 _44827 _44828) = (_44827 = _44828).
Proof. exact (@lem3867750 (_44827 = _44828)). Qed.
Lemma lem3867752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3867753 (_44827 : nat) (_44828 : nat) : (term332 _44827 _44828) = (term333 _44827 _44828).
Proof. exact (MK_COMB (@lem3867752) (@lem3867751 _44827 _44828)). Qed.
Lemma lem3867754 (_44827 : nat) (_44828 : nat) : ((S _44827) = (S _44828)) = ((S _44827) = (S _44828)).
Proof. exact (eq_refl ((S _44827) = (S _44828))). Qed.
Lemma lem3867755 (_44827 : nat) (_44828 : nat) : (term331 _44827 _44828) = (term286 _44827 _44828).
Proof. exact (MK_COMB (@lem3867753 _44827 _44828) (@lem3867754 _44827 _44828)). Qed.
Lemma lem3867756 (_44827 : nat) (_44828 : nat) : (term328 _44827 _44828) = (term286 _44827 _44828).
Proof. exact (TRANS (@lem3867748 _44827 _44828) (@lem3867755 _44827 _44828)). Qed.
Lemma lem3867759 (_44827 : nat) (_44828 : nat) : term286 _44827 _44828.
Proof. exact (EQ_MP (@lem3867756 _44827 _44828) (@lem3867745 _44827 _44828)). Qed.
Lemma lem3867760 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : term334 A s a n.
Proof. exact (@lem3867759 (term54 A s a) n). Qed.
Lemma lem3867763 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : (term116 A s a) = (S n).
Proof. exact (@lem3867760 A s a n (@lem3867708 A n a s h1 h2)). Qed.
Lemma lem3867764 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : term335 A s a n.
Proof. exact (fun h0 : term336 A s a n => @lem3867763 A n a s h1 h2). Qed.
Lemma lem3867766 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867767 {A : Type'} (s : A -> Prop) (a : A) (n : nat) : (term335 A s a n) = ((term116 A s a) = (S n)).
Proof. exact (@lem3867766 ((term116 A s a) = (S n))). Qed.
Lemma lem3867768 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : (term116 A s a) = (S n).
Proof. exact (EQ_MP (@lem3867767 A s a n) (@lem3867764 A n a s h1 h2)). Qed.
Lemma lem3867769 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : term337 A s a n.
Proof. exact (conj (@lem3867644 A s a h2) (@lem3867768 A n a s h1 h3)). Qed.
Lemma lem3867771 (x : nat) (y : nat) (z : nat) : term316 x y z.
Proof. exact (EQ_MP (@lem3867631 x y z) (@lem3867610 y x z)). Qed.
Lemma lem3867772 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term338 A a s n.
Proof. exact (@lem3867771 (term116 A s a) (@CARD A s) (S n)). Qed.
Lemma lem3867775 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : (@CARD A s) = (S n).
Proof. exact (@lem3867772 A a s n (@lem3867769 A n a s h1 h2 h3)). Qed.
Lemma lem3867776 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : term339 A s n.
Proof. exact (fun h0 : term281 A s n => @lem3867775 A n a s h1 h2 h3). Qed.
Lemma lem3867778 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867779 {A : Type'} (s : A -> Prop) (n : nat) : (term339 A s n) = ((@CARD A s) = (S n)).
Proof. exact (@lem3867778 ((@CARD A s) = (S n))). Qed.
Lemma lem3867780 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : (@CARD A s) = (S n).
Proof. exact (EQ_MP (@lem3867779 A s n) (@lem3867776 A n a s h1 h2 h3)). Qed.
Lemma lem3867783 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3867785 {A : Type'} (s : A -> Prop) (n : nat) : (term281 A s n) = (term340 A s n).
Proof. exact (@lem3867783 ((@CARD A s) = (S n))). Qed.
Lemma lem3867788 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term281 A s n) : term340 A s n.
Proof. exact (EQ_MP (@lem3867785 A s n) (@lem3867437 A s n h1)). Qed.
Lemma lem3867791 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (@lem3867788 A s n h2 (@lem3867780 A n a s h1 h3 h4)). Qed.
Lemma lem3867792 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : term200.
Proof. exact (fun h0 : ~ False => @lem3867791 A n a s h1 h2 h3 h4). Qed.
Lemma lem3867794 (p : Prop) : (term198 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3867795 : term200 = False.
Proof. exact (@lem3867794 False). Qed.
Lemma lem3867796 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867795) (@lem3867792 A n a s h1 h2 h3 h4)). Qed.
Lemma lem3867797 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867796 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867437 A s n h2)). Qed.
Lemma lem3867798 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867797 A n a s h1 h2 h3 h4) (@lem3867437 A s n h2)). Qed.
Lemma lem3867799 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : ((@CARD A s) = (term116 A s a)) = False.
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (term116 A s a) => @lem3867798 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867435 A s a h3)). Qed.
Lemma lem3867800 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867799 A n a s h1 h2 h3 h4) (@lem3867435 A s a h3)). Qed.
Lemma lem3867801 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem3867800 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867433 A a s h4)). Qed.
Lemma lem3867802 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867801 A n a s h1 h2 h3 h4) (@lem3867433 A a s h4)). Qed.
Lemma lem3867803 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867802 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867418 A s n h2)). Qed.
Lemma lem3867804 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867803 A n a s h1 h2 h3 h4) (@lem3867418 A s n h2)). Qed.
Lemma lem3867805 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : ((@CARD A s) = (term116 A s a)) = False.
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (term116 A s a) => @lem3867804 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867414 A s a h3)). Qed.
Lemma lem3867806 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867805 A n a s h1 h2 h3 h4) (@lem3867414 A s a h3)). Qed.
Lemma lem3867807 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem3867806 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867410 A a s h4)). Qed.
Lemma lem3867808 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867807 A n a s h1 h2 h3 h4) (@lem3867410 A a s h4)). Qed.
Lemma lem3867809 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867808 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867418 A s n h2)). Qed.
Lemma lem3867810 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867809 A n a s h1 h2 h3 h4) (@lem3867418 A s n h2)). Qed.
Lemma lem3867811 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : ((@CARD A s) = (term116 A s a)) = False.
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (term116 A s a) => @lem3867810 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867414 A s a h3)). Qed.
Lemma lem3867812 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867811 A n a s h1 h2 h3 h4) (@lem3867414 A s a h3)). Qed.
Lemma lem3867813 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem3867812 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867410 A a s h4)). Qed.
Lemma lem3867814 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867813 A n a s h1 h2 h3 h4) (@lem3867410 A a s h4)). Qed.
Lemma lem3867815 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867814 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867385 A s n h2)). Qed.
Lemma lem3867816 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867815 A n a s h1 h2 h3 h4) (@lem3867385 A s n h2)). Qed.
Lemma lem3867817 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : ((@CARD A s) = (term116 A s a)) = False.
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (term116 A s a) => @lem3867816 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867373 A s a h3)). Qed.
Lemma lem3867818 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867817 A n a s h1 h2 h3 h4) (@lem3867373 A s a h3)). Qed.
Lemma lem3867819 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem3867818 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867357 A a s h4)). Qed.
Lemma lem3867820 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867819 A n a s h1 h2 h3 h4) (@lem3867357 A a s h4)). Qed.
Lemma lem3867821 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867820 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867314 A s n h2)). Qed.
Lemma lem3867822 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867821 A n a s h1 h2 h3 h4) (@lem3867314 A s n h2)). Qed.
Lemma lem3867823 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : ((@CARD A s) = (term116 A s a)) = False.
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (term116 A s a) => @lem3867822 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867308 A s a h3)). Qed.
Lemma lem3867824 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867823 A n a s h1 h2 h3 h4) (@lem3867308 A s a h3)). Qed.
Lemma lem3867825 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (@IN A a s) = False.
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem3867824 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867302 A a s h4)). Qed.
Lemma lem3867826 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867825 A n a s h1 h2 h3 h4) (@lem3867302 A a s h4)). Qed.
Lemma lem3867827 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : (term281 A s n) = False.
Proof. exact (prop_ext (fun h5 : term281 A s n => @lem3867826 A n a s h1 h2 h3 h4) (fun h5 : False => @lem3867221 A s n h2)). Qed.
Lemma lem3867828 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : term281 A s n) (h3 : (@CARD A s) = (term116 A s a)) (h4 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867827 A n a s h1 h2 h3 h4) (@lem3867221 A s n h2)). Qed.
Lemma lem3867829 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : term280 A s n.
Proof. exact (fun h0 : term281 A s n => @lem3867828 A n a s h1 h0 h2 h3). Qed.
Lemma lem3867830 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : (@CARD A s) = (term116 A s a)) (h3 : @IN A a s) : (@CARD A s) = (S n).
Proof. exact (EQ_MP (@lem3867220 A s n) (@lem3867829 A n a s h1 h2 h3)). Qed.
Lemma lem3867831 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @IN A a s) : term248 A a s n.
Proof. exact (fun h0 : (@CARD A s) = (term116 A s a) => @lem3867830 A n a s h1 h0 h2). Qed.
Lemma lem3867832 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term74 A s n) : term259 A a s n.
Proof. exact (fun h0 : @IN A a s => @lem3867831 A n a s h1 h0). Qed.
Lemma lem3867833 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term262 A a s n.
Proof. exact (fun h0 : term74 A s n => @lem3867832 A a s n h0). Qed.
Lemma lem3867834 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term265 A a s n.
Proof. exact (fun h0 : @FINITE A s => @lem3867833 A a s n). Qed.
Lemma lem3867835 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term267 A a s n.
Proof. exact (fun h0 : term6 A s => @lem3867834 A a s n). Qed.
Lemma lem3867840 {A : Type'} (s : A -> Prop) (n : nat) : term271 A s n.
Proof. exact (fun a : A => @lem3867835 A a s n). Qed.
Lemma lem3867845 {A : Type'} (n : nat) : term275 A n.
Proof. exact (fun s : A -> Prop => @lem3867840 A s n). Qed.
Lemma lem3867850 {A : Type'} : term279 A.
Proof. exact (fun n : nat => @lem3867845 A n). Qed.
Lemma lem3867851 {A : Type'} : term278 A.
Proof. exact (EQ_MP (@lem3867211 A) (@lem3867850 A)). Qed.
Lemma lem3867852 {A : Type'} (n : nat) : term341 A n.
Proof. exact (@lem3867851 A n). Qed.
Lemma lem3867853 {A : Type'} (n : nat) : (term341 A n) = (term274 A n).
Proof. exact (eq_refl (term341 A n)). Qed.
Lemma lem3867854 {A : Type'} (n : nat) : term274 A n.
Proof. exact (EQ_MP (@lem3867853 A n) (@lem3867852 A n)). Qed.
Lemma lem3867855 {A : Type'} (n : nat) (s : A -> Prop) : term342 A n s.
Proof. exact (@lem3867854 A n s). Qed.
Lemma lem3867856 {A : Type'} (s : A -> Prop) (n : nat) : (term342 A n s) = (term270 A s n).
Proof. exact (eq_refl (term342 A n s)). Qed.
Lemma lem3867857 {A : Type'} (s : A -> Prop) (n : nat) : term270 A s n.
Proof. exact (EQ_MP (@lem3867856 A s n) (@lem3867855 A n s)). Qed.
Lemma lem3867858 {A : Type'} (s : A -> Prop) (n : nat) (a : A) : term343 A s n a.
Proof. exact (@lem3867857 A s n a). Qed.
Lemma lem3867859 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term343 A s n a) = (term253 A a s n).
Proof. exact (eq_refl (term343 A s n a)). Qed.
Lemma lem3867860 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term253 A a s n.
Proof. exact (EQ_MP (@lem3867859 A a s n) (@lem3867858 A s n a)). Qed.
Lemma lem3867862 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term253 A a s n.
Proof. exact (@lem3867056 A a s n (@lem3867860 A a s n)). Qed.
Lemma lem3867863 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term6 A s) : term264 A a s n.
Proof. exact (@lem3867862 A a s n (@lem3864379 A s h1)). Qed.
Lemma lem3867864 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : term261 A a s n.
Proof. exact (@lem3867863 A a n s h2 (@lem3864367 A s h1)). Qed.
Lemma lem3867865 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) : term258 A a s n.
Proof. exact (@lem3867864 A a n s h2 h3 (@lem3864961 A s n h1)). Qed.
Lemma lem3867866 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : term251 A a s n.
Proof. exact (@lem3867865 A a n s h1 h2 h3 (@lem3866177 A a s h4)). Qed.
Lemma lem3867867 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : term252 A a s n) (h5 : @IN A a s) : False.
Proof. exact (@lem3867866 A n a s h1 h2 h3 h5 (@lem3867040 A a s n h4)). Qed.
Lemma lem3867868 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : term252 A a s n) (h5 : @IN A a s) : (term252 A a s n) = False.
Proof. exact (prop_ext (fun h6 : term252 A a s n => @lem3867867 A n a s h1 h2 h3 h4 h5) (fun h6 : False => @lem3867040 A a s n h4)). Qed.
Lemma lem3867869 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : term252 A a s n) (h5 : @IN A a s) : False.
Proof. exact (EQ_MP (@lem3867868 A n a s h1 h2 h3 h4 h5) (@lem3867040 A a s n h4)). Qed.
Lemma lem3867870 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : term251 A a s n.
Proof. exact (fun h0 : term252 A a s n => @lem3867869 A n a s h1 h2 h3 h0 h4). Qed.
Lemma lem3867871 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : term248 A a s n.
Proof. exact (EQ_MP (@lem3867039 A a s n) (@lem3867870 A n a s h1 h2 h3 h4)). Qed.
Lemma lem3867872 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : (term126 A s a) = s) (h5 : @IN A a s) : term244 A a s n.
Proof. exact (EQ_MP (@lem3866301 A n a s h4) (@lem3867871 A n a s h1 h2 h3 h5)). Qed.
Lemma lem3867873 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : ((term126 A s a) = s) = (term244 A a s n).
Proof. exact (prop_ext (fun h5 : (term126 A s a) = s => @lem3867872 A n a s h1 h2 h3 h5 h4) (fun h5 : term244 A a s n => @lem3867035 A a s h4)). Qed.
Lemma lem3867874 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : term244 A a s n.
Proof. exact (EQ_MP (@lem3867873 A n a s h1 h2 h3 h4) (@lem3867035 A a s h4)). Qed.
Lemma lem3867875 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : term243 A a s n.
Proof. exact (EQ_MP (@lem3866287 A n a s h2 h4) (@lem3867874 A n a s h1 h2 h3 h4)). Qed.
Lemma lem3867876 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) (h4 : @IN A a s) : (@CARD A s) = (S n).
Proof. exact (@lem3867875 A n a s h1 h2 h3 h4 (@lem3864322 A s a)). Qed.
Lemma lem3867877 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : term5 A s) (h3 : @FINITE A s) (h4 : term6 A s) : (@CARD A s) = (S n).
Proof. exact (ex_elim (@lem3866176 A s h2) (fun a : A => fun h0 : term100 A s a => @lem3867876 A n a s h1 h3 h4 h0)). Qed.
Lemma lem3867878 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) : term344 A s n.
Proof. exact (fun h0 : term5 A s => @lem3867877 A n s h1 h0 h2 h3). Qed.
Lemma lem3867879 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) : (@CARD A s) = (S n).
Proof. exact (@lem3867878 A n s h1 h2 h3 (@lem3866175 A s h3)). Qed.
Lemma lem3867880 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) : (term74 A s n) = ((@CARD A s) = (S n)).
Proof. exact (prop_ext (fun h4 : term74 A s n => @lem3867879 A n s h1 h2 h3) (fun h4 : (@CARD A s) = (S n) => @lem3864961 A s n h1)). Qed.
Lemma lem3867881 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term74 A s n) (h2 : @FINITE A s) (h3 : term6 A s) : (@CARD A s) = (S n).
Proof. exact (EQ_MP (@lem3867880 A n s h1 h2 h3) (@lem3864961 A s n h1)). Qed.
Lemma lem3867882 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : term345 A s n.
Proof. exact (fun h0 : term74 A s n => @lem3867881 A n s h0 h1 h2). Qed.
Lemma lem3867883 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) (h3 : @IN A a s) : (@IN A a s) = ((term54 A s a) = n).
Proof. exact (prop_ext (fun h4 : @IN A a s => @lem3866171 A n a s h1 h2 h3) (fun h4 : (term54 A s a) = n => @lem3864960 A a s h3)). Qed.
Lemma lem3867884 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) (h3 : @IN A a s) : (term54 A s a) = n.
Proof. exact (EQ_MP (@lem3867883 A n a s h1 h2 h3) (@lem3864960 A a s h3)). Qed.
Lemma lem3867885 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : term72 A s a n.
Proof. exact (fun h0 : @IN A a s => @lem3867884 A n a s h1 h2 h0). Qed.
Lemma lem3867890 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : term74 A s n.
Proof. exact (fun a : A => @lem3867885 A a s n h1 h2). Qed.
Lemma lem3867891 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : ((@CARD A s) = (S n)) = (term74 A s n).
Proof. exact (prop_ext (fun h3 : (@CARD A s) = (S n) => @lem3867890 A s n h1 h2) (fun h3 : term74 A s n => @lem3864959 A s n h2)). Qed.
Lemma lem3867892 {A : Type'} (s : A -> Prop) (n : nat) (h1 : @FINITE A s) (h2 : (@CARD A s) = (S n)) : term74 A s n.
Proof. exact (EQ_MP (@lem3867891 A s n h1 h2) (@lem3864959 A s n h2)). Qed.
Lemma lem3867893 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) : term346 A s n.
Proof. exact (fun h0 : (@CARD A s) = (S n) => @lem3867892 A s n h1 h0). Qed.
Lemma lem3867894 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : term347 A s n.
Proof. exact (conj (@lem3867893 A n s h1) (@lem3867882 A n s h1 h2)). Qed.
Lemma lem3867895 {A : Type'} (s : A -> Prop) (n : nat) : (term347 A s n) = (((@CARD A s) = (S n)) = (term74 A s n)).
Proof. exact (@lem32 ((@CARD A s) = (S n)) (term74 A s n)). Qed.
Lemma lem3867896 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : ((@CARD A s) = (S n)) = (term74 A s n).
Proof. exact (EQ_MP (@lem3867895 A s n) (@lem3867894 A n s h1 h2)). Qed.
Lemma lem3867897 {A : Type'} (n : nat) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term6 A s) : (term26 A s n) = (term68 A s n).
Proof. exact (EQ_MP (@lem3864835 A n s h1) (@lem3867896 A n s h1 h2)). Qed.
Lemma lem3867898 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : (term26 A s n) = (term68 A s n).
Proof. exact (or_elim (@lem3864366 A s) (fun h0 : @FINITE A s => @lem3867897 A n s h0 h1) (fun h0 : term14 A s => @lem3864958 A n s h0 h1)). Qed.
Lemma lem3867899 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : (term26 A s n) = (term37 A s n).
Proof. exact (EQ_MP (@lem3864757 A s n) (@lem3867898 A n s h1)). Qed.
Lemma lem3867900 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term6 A s) : (term26 A s n) = (term40 A s n).
Proof. exact (EQ_MP (@lem3864715 A n s h1) (@lem3867899 A n s h1)). Qed.
Lemma lem3867901 {A : Type'} (s : A -> Prop) (n : nat) : (term26 A s n) = (term40 A s n).
Proof. exact (or_elim (@lem3864377 A s) (fun h0 : s = (@EMPTY A) => @lem3864611 A n s h0) (fun h0 : term6 A s => @lem3867900 A n s h0)). Qed.
Lemma lem3867902 {A : Type'} (s : A -> Prop) (n : nat) : (term25 A s n) = (term39 A s n).
Proof. exact (EQ_MP (@lem3864434 A s n) (@lem3867901 A s n)). Qed.
Lemma lem3867907 {A : Type'} (s : A -> Prop) : term348 A s.
Proof. exact (fun n : nat => @lem3867902 A s n). Qed.
Lemma lem3867912 {A : Type'} : term349 A.
Proof. exact (fun s : A -> Prop => @lem3867907 A s). Qed.
