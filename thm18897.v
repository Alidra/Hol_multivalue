Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18897_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EQ_SYM_EQ_spec.
Require Import ETA_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem18395 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem18396 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem18397 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem18396 A x) (@lem18395 A x)). Qed.
Lemma lem18398 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem18397 A x y). Qed.
Lemma lem18399 {A : Type'} (y : A) (x : A) : (term2 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem18413 (a : Prop) : term3 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem18414 (a : Prop) : (term3 a) = (term4 a).
Proof. exact (eq_refl (term3 a)). Qed.
Lemma lem18415 (a : Prop) : term4 a.
Proof. exact (EQ_MP (@lem18414 a) (@lem18413 a)). Qed.
Lemma lem18416 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem18417 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem18430 (b : Prop) (c : Prop) : (term5 b c) = (term5 b c).
Proof. exact (eq_refl (term5 b c)). Qed.
Lemma lem18431 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term6 b c a) = (term7 b c).
Proof. exact (MK_COMB (@lem18430 b c) (@lem18416 a h1)). Qed.
Lemma lem18432 (b : Prop) (c : Prop) : (term7 b c) = ((term8 b c) = (term9 b c)).
Proof. exact (eq_refl (term7 b c)). Qed.
Lemma lem18433 (b : Prop) (c : Prop) (a : Prop) : (term10 b c a) = (term10 b c a).
Proof. exact (eq_refl (term10 b c a)). Qed.
Lemma lem18434 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = (term7 b c)) = ((term6 b c a) = ((term8 b c) = (term9 b c))).
Proof. exact (MK_COMB (@lem18433 b c a) (@lem18432 b c)). Qed.
Lemma lem18435 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = ((term11 a b c) = (term12 a b c)).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem18436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18437 (a : Prop) (b : Prop) (c : Prop) : (term10 b c a) = (term13 a b c).
Proof. exact (MK_COMB (@lem18436) (@lem18435 a b c)). Qed.
Lemma lem18438 (b : Prop) (c : Prop) : ((term8 b c) = (term9 b c)) = ((term8 b c) = (term9 b c)).
Proof. exact (eq_refl ((term8 b c) = (term9 b c))). Qed.
Lemma lem18439 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = ((term8 b c) = (term9 b c))) = (((term11 a b c) = (term12 a b c)) = ((term8 b c) = (term9 b c))).
Proof. exact (MK_COMB (@lem18437 a b c) (@lem18438 b c)). Qed.
Lemma lem18440 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = (term7 b c)) = (((term11 a b c) = (term12 a b c)) = ((term8 b c) = (term9 b c))).
Proof. exact (TRANS (@lem18434 a b c) (@lem18439 a b c)). Qed.
Lemma lem18441 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term11 a b c) = (term12 a b c)) = ((term8 b c) = (term9 b c)).
Proof. exact (EQ_MP (@lem18440 a b c) (@lem18431 b c a h1)). Qed.
Lemma lem18442 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term8 b c) = (term9 b c)) = ((term11 a b c) = (term12 a b c)).
Proof. exact (SYM (@lem18441 b c a h1)). Qed.
Lemma lem18443 (b : Prop) (c : Prop) : (term5 b c) = (term5 b c).
Proof. exact (eq_refl (term5 b c)). Qed.
Lemma lem18444 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term6 b c a) = (term14 b c).
Proof. exact (MK_COMB (@lem18443 b c) (@lem18417 a h1)). Qed.
Lemma lem18445 (b : Prop) (c : Prop) : (term14 b c) = ((term15 b c) = (term16 b c)).
Proof. exact (eq_refl (term14 b c)). Qed.
Lemma lem18446 (b : Prop) (c : Prop) (a : Prop) : (term10 b c a) = (term10 b c a).
Proof. exact (eq_refl (term10 b c a)). Qed.
Lemma lem18447 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = (term14 b c)) = ((term6 b c a) = ((term15 b c) = (term16 b c))).
Proof. exact (MK_COMB (@lem18446 b c a) (@lem18445 b c)). Qed.
Lemma lem18448 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = ((term11 a b c) = (term12 a b c)).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem18449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18450 (a : Prop) (b : Prop) (c : Prop) : (term10 b c a) = (term13 a b c).
Proof. exact (MK_COMB (@lem18449) (@lem18448 a b c)). Qed.
Lemma lem18451 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = ((term15 b c) = (term16 b c)).
Proof. exact (eq_refl ((term15 b c) = (term16 b c))). Qed.
Lemma lem18452 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = ((term15 b c) = (term16 b c))) = (((term11 a b c) = (term12 a b c)) = ((term15 b c) = (term16 b c))).
Proof. exact (MK_COMB (@lem18450 a b c) (@lem18451 b c)). Qed.
Lemma lem18453 (a : Prop) (b : Prop) (c : Prop) : ((term6 b c a) = (term14 b c)) = (((term11 a b c) = (term12 a b c)) = ((term15 b c) = (term16 b c))).
Proof. exact (TRANS (@lem18447 a b c) (@lem18452 a b c)). Qed.
Lemma lem18454 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term11 a b c) = (term12 a b c)) = ((term15 b c) = (term16 b c)).
Proof. exact (EQ_MP (@lem18453 a b c) (@lem18444 b c a h1)). Qed.
Lemma lem18455 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term15 b c) = (term16 b c)) = ((term11 a b c) = (term12 a b c)).
Proof. exact (SYM (@lem18454 b c a h1)). Qed.
Lemma lem18461 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem18462 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem18461 b). Qed.
Lemma lem18463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem18464 (b : Prop) : (term17 b) = (imp b).
Proof. exact (MK_COMB (@lem18463) (@lem18462 b)). Qed.
Lemma lem18465 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem18466 (b : Prop) (c : Prop) : (term8 b c) = (b -> c).
Proof. exact (MK_COMB (@lem18464 b) (@lem18465 c)). Qed.
Lemma lem18469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18470 (b : Prop) (c : Prop) : (term18 b c) = (term19 b c).
Proof. exact (MK_COMB (@lem18469) (@lem18466 b c)). Qed.
Lemma lem18474 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem18475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18476 : term20 = (or False).
Proof. exact (MK_COMB (@lem18475) (@lem18474)). Qed.
Lemma lem18479 (b : Prop) (c : Prop) : (term21 b c) = (term21 b c).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem18480 (b : Prop) (c : Prop) : (term9 b c) = (term22 b c).
Proof. exact (MK_COMB (@lem18476) (@lem18479 b c)). Qed.
Lemma lem18482 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem18483 (b : Prop) (c : Prop) : (term22 b c) = (term21 b c).
Proof. exact (@lem18482 (term21 b c)). Qed.
Lemma lem18486 (b : Prop) (c : Prop) : (term9 b c) = (term21 b c).
Proof. exact (TRANS (@lem18480 b c) (@lem18483 b c)). Qed.
Lemma lem18487 (b : Prop) (c : Prop) : ((term8 b c) = (term9 b c)) = ((b -> c) = (term21 b c)).
Proof. exact (MK_COMB (@lem18470 b c) (@lem18486 b c)). Qed.
Lemma lem18490 (b : Prop) (c : Prop) : ((b -> c) = (term21 b c)) = ((term8 b c) = (term9 b c)).
Proof. exact (SYM (@lem18487 b c)). Qed.
Lemma lem18491 (b : Prop) : term3 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem18492 (b : Prop) : (term3 b) = (term4 b).
Proof. exact (eq_refl (term3 b)). Qed.
Lemma lem18493 (b : Prop) : term4 b.
Proof. exact (EQ_MP (@lem18492 b) (@lem18491 b)). Qed.
Lemma lem18494 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem18495 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem18504 (c : Prop) : (term23 c) = (term23 c).
Proof. exact (eq_refl (term23 c)). Qed.
Lemma lem18505 (c : Prop) (b : Prop) (h1 : b = True) : (term24 c b) = (term25 c).
Proof. exact (MK_COMB (@lem18504 c) (@lem18494 b h1)). Qed.
Lemma lem18506 (c : Prop) : (term25 c) = ((True -> c) = (term26 c)).
Proof. exact (eq_refl (term25 c)). Qed.
Lemma lem18507 (c : Prop) (b : Prop) : (term27 c b) = (term27 c b).
Proof. exact (eq_refl (term27 c b)). Qed.
Lemma lem18508 (b : Prop) (c : Prop) : ((term24 c b) = (term25 c)) = ((term24 c b) = ((True -> c) = (term26 c))).
Proof. exact (MK_COMB (@lem18507 c b) (@lem18506 c)). Qed.
Lemma lem18509 (b : Prop) (c : Prop) : (term24 c b) = ((b -> c) = (term21 b c)).
Proof. exact (eq_refl (term24 c b)). Qed.
Lemma lem18510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18511 (b : Prop) (c : Prop) : (term27 c b) = (term28 b c).
Proof. exact (MK_COMB (@lem18510) (@lem18509 b c)). Qed.
Lemma lem18512 (c : Prop) : ((True -> c) = (term26 c)) = ((True -> c) = (term26 c)).
Proof. exact (eq_refl ((True -> c) = (term26 c))). Qed.
Lemma lem18513 (b : Prop) (c : Prop) : ((term24 c b) = ((True -> c) = (term26 c))) = (((b -> c) = (term21 b c)) = ((True -> c) = (term26 c))).
Proof. exact (MK_COMB (@lem18511 b c) (@lem18512 c)). Qed.
Lemma lem18514 (b : Prop) (c : Prop) : ((term24 c b) = (term25 c)) = (((b -> c) = (term21 b c)) = ((True -> c) = (term26 c))).
Proof. exact (TRANS (@lem18508 b c) (@lem18513 b c)). Qed.
Lemma lem18515 (c : Prop) (b : Prop) (h1 : b = True) : ((b -> c) = (term21 b c)) = ((True -> c) = (term26 c)).
Proof. exact (EQ_MP (@lem18514 b c) (@lem18505 c b h1)). Qed.
Lemma lem18516 (c : Prop) (b : Prop) (h1 : b = True) : ((True -> c) = (term26 c)) = ((b -> c) = (term21 b c)).
Proof. exact (SYM (@lem18515 c b h1)). Qed.
Lemma lem18517 (c : Prop) : (term23 c) = (term23 c).
Proof. exact (eq_refl (term23 c)). Qed.
Lemma lem18518 (c : Prop) (b : Prop) (h1 : b = False) : (term24 c b) = (term29 c).
Proof. exact (MK_COMB (@lem18517 c) (@lem18495 b h1)). Qed.
Lemma lem18519 (c : Prop) : (term29 c) = ((False -> c) = (term30 c)).
Proof. exact (eq_refl (term29 c)). Qed.
Lemma lem18520 (c : Prop) (b : Prop) : (term27 c b) = (term27 c b).
Proof. exact (eq_refl (term27 c b)). Qed.
Lemma lem18521 (b : Prop) (c : Prop) : ((term24 c b) = (term29 c)) = ((term24 c b) = ((False -> c) = (term30 c))).
Proof. exact (MK_COMB (@lem18520 c b) (@lem18519 c)). Qed.
Lemma lem18522 (b : Prop) (c : Prop) : (term24 c b) = ((b -> c) = (term21 b c)).
Proof. exact (eq_refl (term24 c b)). Qed.
Lemma lem18523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18524 (b : Prop) (c : Prop) : (term27 c b) = (term28 b c).
Proof. exact (MK_COMB (@lem18523) (@lem18522 b c)). Qed.
Lemma lem18525 (c : Prop) : ((False -> c) = (term30 c)) = ((False -> c) = (term30 c)).
Proof. exact (eq_refl ((False -> c) = (term30 c))). Qed.
Lemma lem18526 (b : Prop) (c : Prop) : ((term24 c b) = ((False -> c) = (term30 c))) = (((b -> c) = (term21 b c)) = ((False -> c) = (term30 c))).
Proof. exact (MK_COMB (@lem18524 b c) (@lem18525 c)). Qed.
Lemma lem18527 (b : Prop) (c : Prop) : ((term24 c b) = (term29 c)) = (((b -> c) = (term21 b c)) = ((False -> c) = (term30 c))).
Proof. exact (TRANS (@lem18521 b c) (@lem18526 b c)). Qed.
Lemma lem18528 (c : Prop) (b : Prop) (h1 : b = False) : ((b -> c) = (term21 b c)) = ((False -> c) = (term30 c)).
Proof. exact (EQ_MP (@lem18527 b c) (@lem18518 c b h1)). Qed.
Lemma lem18529 (c : Prop) (b : Prop) (h1 : b = False) : ((False -> c) = (term30 c)) = ((b -> c) = (term21 b c)).
Proof. exact (SYM (@lem18528 c b h1)). Qed.
Lemma lem18533 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem18534 (c : Prop) : (True -> c) = c.
Proof. exact (@lem18533 c). Qed.
Lemma lem18535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18536 (c : Prop) : (term31 c) = (@eq Prop c).
Proof. exact (MK_COMB (@lem18535) (@lem18534 c)). Qed.
Lemma lem18540 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem18541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18542 : term20 = (or False).
Proof. exact (MK_COMB (@lem18541) (@lem18540)). Qed.
Lemma lem18543 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem18544 (c : Prop) : (term26 c) = (False \/ c).
Proof. exact (MK_COMB (@lem18542) (@lem18543 c)). Qed.
Lemma lem18546 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem18547 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem18546 c). Qed.
Lemma lem18548 (c : Prop) : (term26 c) = c.
Proof. exact (TRANS (@lem18544 c) (@lem18547 c)). Qed.
Lemma lem18549 (c : Prop) : ((True -> c) = (term26 c)) = (c = c).
Proof. exact (MK_COMB (@lem18536 c) (@lem18548 c)). Qed.
Lemma lem18551 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem18552 (x : Prop) : (x = x) = True.
Proof. exact (@lem18551 Prop x). Qed.
Lemma lem18553 (c : Prop) : (c = c) = True.
Proof. exact (@lem18552 c). Qed.
Lemma lem18554 (c : Prop) : ((True -> c) = (term26 c)) = True.
Proof. exact (TRANS (@lem18549 c) (@lem18553 c)). Qed.
Lemma lem18555 (c : Prop) : True = ((True -> c) = (term26 c)).
Proof. exact (SYM (@lem18554 c)). Qed.
Lemma lem18556 (c : Prop) : (True -> c) = (term26 c).
Proof. exact (EQ_MP (@lem18555 c) (@lem0)). Qed.
Lemma lem18560 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem18561 (c : Prop) : (False -> c) = True.
Proof. exact (@lem18560 c). Qed.
Lemma lem18562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18563 (c : Prop) : (term32 c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem18562) (@lem18561 c)). Qed.
Lemma lem18567 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem18568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18569 : term33 = (or True).
Proof. exact (MK_COMB (@lem18568) (@lem18567)). Qed.
Lemma lem18570 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem18571 (c : Prop) : (term30 c) = (True \/ c).
Proof. exact (MK_COMB (@lem18569) (@lem18570 c)). Qed.
Lemma lem18573 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem18574 (c : Prop) : (True \/ c) = True.
Proof. exact (@lem18573 c). Qed.
Lemma lem18575 (c : Prop) : (term30 c) = True.
Proof. exact (TRANS (@lem18571 c) (@lem18574 c)). Qed.
Lemma lem18576 (c : Prop) : ((False -> c) = (term30 c)) = (True = True).
Proof. exact (MK_COMB (@lem18563 c) (@lem18575 c)). Qed.
Lemma lem18578 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem18579 : (True = True) = True.
Proof. exact (@lem18578 True). Qed.
Lemma lem18580 (c : Prop) : ((False -> c) = (term30 c)) = True.
Proof. exact (TRANS (@lem18576 c) (@lem18579)). Qed.
Lemma lem18581 (c : Prop) : True = ((False -> c) = (term30 c)).
Proof. exact (SYM (@lem18580 c)). Qed.
Lemma lem18582 (c : Prop) : (False -> c) = (term30 c).
Proof. exact (EQ_MP (@lem18581 c) (@lem0)). Qed.
Lemma lem18583 (c : Prop) (b : Prop) (h1 : b = False) : (b -> c) = (term21 b c).
Proof. exact (EQ_MP (@lem18529 c b h1) (@lem18582 c)). Qed.
Lemma lem18584 (c : Prop) (b : Prop) (h1 : b = True) : (b -> c) = (term21 b c).
Proof. exact (EQ_MP (@lem18516 c b h1) (@lem18556 c)). Qed.
Lemma lem18586 (b : Prop) (c : Prop) : (b -> c) = (term21 b c).
Proof. exact (or_elim (@lem18493 b) (fun h0 : b = True => @lem18584 c b h0) (fun h0 : b = False => @lem18583 c b h0)). Qed.
Lemma lem18587 (b : Prop) (c : Prop) : (term8 b c) = (term9 b c).
Proof. exact (EQ_MP (@lem18490 b c) (@lem18586 b c)). Qed.
Lemma lem18593 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem18594 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem18593 b). Qed.
Lemma lem18595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem18596 (b : Prop) : (term34 b) = (imp False).
Proof. exact (MK_COMB (@lem18595) (@lem18594 b)). Qed.
Lemma lem18597 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem18598 (b : Prop) (c : Prop) : (term15 b c) = (False -> c).
Proof. exact (MK_COMB (@lem18596 b) (@lem18597 c)). Qed.
Lemma lem18600 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem18601 (c : Prop) : (False -> c) = True.
Proof. exact (@lem18600 c). Qed.
Lemma lem18602 (b : Prop) (c : Prop) : (term15 b c) = True.
Proof. exact (TRANS (@lem18598 b c) (@lem18601 c)). Qed.
Lemma lem18603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18604 (b : Prop) (c : Prop) : (term35 b c) = (@eq Prop True).
Proof. exact (MK_COMB (@lem18603) (@lem18602 b c)). Qed.
Lemma lem18608 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem18609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18610 : term33 = (or True).
Proof. exact (MK_COMB (@lem18609) (@lem18608)). Qed.
Lemma lem18613 (b : Prop) (c : Prop) : (term21 b c) = (term21 b c).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem18614 (b : Prop) (c : Prop) : (term16 b c) = (term36 b c).
Proof. exact (MK_COMB (@lem18610) (@lem18613 b c)). Qed.
Lemma lem18616 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem18617 (b : Prop) (c : Prop) : (term36 b c) = True.
Proof. exact (@lem18616 (term21 b c)). Qed.
Lemma lem18618 (b : Prop) (c : Prop) : (term16 b c) = True.
Proof. exact (TRANS (@lem18614 b c) (@lem18617 b c)). Qed.
Lemma lem18619 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = (True = True).
Proof. exact (MK_COMB (@lem18604 b c) (@lem18618 b c)). Qed.
Lemma lem18621 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem18622 : (True = True) = True.
Proof. exact (@lem18621 True). Qed.
Lemma lem18623 (b : Prop) (c : Prop) : ((term15 b c) = (term16 b c)) = True.
Proof. exact (TRANS (@lem18619 b c) (@lem18622)). Qed.
Lemma lem18624 (b : Prop) (c : Prop) : True = ((term15 b c) = (term16 b c)).
Proof. exact (SYM (@lem18623 b c)). Qed.
Lemma lem18625 (b : Prop) (c : Prop) : (term15 b c) = (term16 b c).
Proof. exact (EQ_MP (@lem18624 b c) (@lem0)). Qed.
Lemma lem18626 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term11 a b c) = (term12 a b c).
Proof. exact (EQ_MP (@lem18455 b c a h1) (@lem18625 b c)). Qed.
Lemma lem18627 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term11 a b c) = (term12 a b c).
Proof. exact (EQ_MP (@lem18442 b c a h1) (@lem18587 b c)). Qed.
Lemma lem18632 {A B : Type'} (t : A -> B) (h1 : (term37 A B t) = t) : (term37 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem18633 {A B : Type'} (t : A -> B) (h1 : (term37 A B t) = t) : t = (term37 A B t).
Proof. exact (SYM (@lem18632 A B t h1)). Qed.
Lemma lem18634 {A B : Type'} (t : A -> B) (h1 : t = (term37 A B t)) : t = (term37 A B t).
Proof. exact (h1). Qed.
Lemma lem18635 {A B : Type'} (t : A -> B) (h1 : t = (term37 A B t)) : (term37 A B t) = t.
Proof. exact (SYM (@lem18634 A B t h1)). Qed.
Lemma lem18636 {A B : Type'} (t : A -> B) : ((term37 A B t) = t) = (t = (term37 A B t)).
Proof. exact (prop_ext (fun h1 : (term37 A B t) = t => @lem18633 A B t h1) (fun h1 : t = (term37 A B t) => @lem18635 A B t h1)). Qed.
Lemma lem18637 {A B : Type'} : (term38 A B) = (term39 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem18636 A B t)). Qed.
Lemma lem18638 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem18639 {A B : Type'} : (term40 A B) = (term41 A B).
Proof. exact (MK_COMB (@lem18638 A B) (@lem18637 A B)). Qed.
Lemma lem18640 {A B : Type'} : term41 A B.
Proof. exact (EQ_MP (@lem18639 A B) (@lem9121 A B)). Qed.
Lemma lem18641 {A B : Type'} (t : A -> B) : term42 A B t.
Proof. exact (@lem18640 A B t). Qed.
Lemma lem18642 {A B : Type'} (t : A -> B) : (term42 A B t) = (t = (term37 A B t)).
Proof. exact (eq_refl (term42 A B t)). Qed.
Lemma lem18645 {A B : Type'} (t : A -> B) : t = (term37 A B t).
Proof. exact (EQ_MP (@lem18642 A B t) (@lem18641 A B t)). Qed.
Lemma lem18646 {A : Type'} (t : A -> Prop) : t = (term43 A t).
Proof. exact (@lem18645 A Prop t). Qed.
Lemma lem18647 {A : Type'} (P : A -> Prop) : P = (term43 A P).
Proof. exact (@lem18646 A P). Qed.
Lemma lem18648 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem18649 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term44 A P).
Proof. exact (MK_COMB (@lem18648 A) (@lem18647 A P)). Qed.
Lemma lem18650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18651 {A : Type'} (P : A -> Prop) : (term45 A P) = (term46 A P).
Proof. exact (MK_COMB (@lem18650) (@lem18649 A P)). Qed.
Lemma lem18652 {A : Type'} (P : A -> Prop) : (term47 A P) = (term47 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem18653 {A : Type'} (P : A -> Prop) : ((@ex1 A P) = (term47 A P)) = ((term44 A P) = (term47 A P)).
Proof. exact (MK_COMB (@lem18651 A P) (@lem18652 A P)). Qed.
Lemma lem18654 {A : Type'} (P : A -> Prop) : ((term44 A P) = (term47 A P)) = ((@ex1 A P) = (term47 A P)).
Proof. exact (SYM (@lem18653 A P)). Qed.
Lemma lem18658 {A : Type'} : (@ex1 A) = (term48 A).
Proof. exact (@ex1_def A). Qed.
Lemma lem18670 (a : Prop) (b : Prop) (c : Prop) : (term11 a b c) = (term12 a b c).
Proof. exact (or_elim (@lem18415 a) (fun h0 : a = True => @lem18627 b c a h0) (fun h0 : a = False => @lem18626 b c a h0)). Qed.
Lemma lem18671 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term49 A P x y) = (term50 A P x y).
Proof. exact (@lem18670 (P x) (P y) (x = y)). Qed.
Lemma lem18678 {A : Type'} (P : A -> Prop) (x : A) : (term51 A P x) = (term52 A P x).
Proof. exact (fun_ext (fun y : A => @lem18671 A P x y)). Qed.
Lemma lem18679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18680 {A : Type'} (P : A -> Prop) (x : A) : (term53 A P x) = (term54 A P x).
Proof. exact (MK_COMB (@lem18679 A) (@lem18678 A P x)). Qed.
Lemma lem18685 {A : Type'} (P : A -> Prop) : (term55 A P) = (term56 A P).
Proof. exact (fun_ext (fun x : A => @lem18680 A P x)). Qed.
Lemma lem18686 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18687 {A : Type'} (P : A -> Prop) : (term57 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem18686 A) (@lem18685 A P)). Qed.
Lemma lem18692 {A : Type'} (P : A -> Prop) : (term59 A P) = (term59 A P).
Proof. exact (eq_refl (term59 A P)). Qed.
Lemma lem18693 {A : Type'} (P : A -> Prop) : (term60 A P) = (term61 A P).
Proof. exact (MK_COMB (@lem18692 A P) (@lem18687 A P)). Qed.
Lemma lem18696 {A : Type'} : (term48 A) = (term62 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem18693 A P)). Qed.
Lemma lem18697 {A : Type'} : (@ex1 A) = (term62 A).
Proof. exact (TRANS (@lem18658 A) (@lem18696 A)). Qed.
Lemma lem18698 {A : Type'} (P : A -> Prop) : (term43 A P) = (term43 A P).
Proof. exact (eq_refl (term43 A P)). Qed.
Lemma lem18699 {A : Type'} (P : A -> Prop) : (term44 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem18697 A) (@lem18698 A P)). Qed.
Lemma lem18701 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18702 {A : Type'} (f : type686 A) (y : A -> Prop) : (term65 A f y) = (f y).
Proof. exact (@lem18701 (A -> Prop) Prop f y). Qed.
Lemma lem18703 {A : Type'} (P : A -> Prop) : (term66 A P) = (term63 A P).
Proof. exact (@lem18702 A (term62 A) (term43 A P)). Qed.
Lemma lem18704 {A : Type'} (P : A -> Prop) : (term67 A P) = (term61 A P).
Proof. exact (eq_refl (term67 A P)). Qed.
Lemma lem18705 {A : Type'} : (term68 A) = (term62 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem18704 A P)). Qed.
Lemma lem18706 {A : Type'} (P : A -> Prop) : (term43 A P) = (term43 A P).
Proof. exact (eq_refl (term43 A P)). Qed.
Lemma lem18707 {A : Type'} (P : A -> Prop) : (term66 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem18705 A) (@lem18706 A P)). Qed.
Lemma lem18708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18709 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (MK_COMB (@lem18708) (@lem18707 A P)). Qed.
Lemma lem18710 {A : Type'} (P : A -> Prop) : (term63 A P) = (term71 A P).
Proof. exact (eq_refl (term63 A P)). Qed.
Lemma lem18711 {A : Type'} (P : A -> Prop) : ((term66 A P) = (term63 A P)) = ((term63 A P) = (term71 A P)).
Proof. exact (MK_COMB (@lem18709 A P) (@lem18710 A P)). Qed.
Lemma lem18712 {A : Type'} (P : A -> Prop) : (term63 A P) = (term71 A P).
Proof. exact (EQ_MP (@lem18711 A P) (@lem18703 A P)). Qed.
Lemma lem18730 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18731 {A : Type'} (f : A -> Prop) (y : A) : (term72 A f y) = (f y).
Proof. exact (@lem18730 A Prop f y). Qed.
Lemma lem18732 {A : Type'} (P : A -> Prop) (x : A) : (term72 A P x) = (P x).
Proof. exact (@lem18731 A P x). Qed.
Lemma lem18733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18734 {A : Type'} (P : A -> Prop) (x : A) : (term73 A P x) = (term74 A P x).
Proof. exact (MK_COMB (@lem18733) (@lem18732 A P x)). Qed.
Lemma lem18735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18736 {A : Type'} (P : A -> Prop) (x : A) : (term75 A P x) = (term76 A P x).
Proof. exact (MK_COMB (@lem18735) (@lem18734 A P x)). Qed.
Lemma lem18740 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem18741 {A : Type'} (f : A -> Prop) (y : A) : (term72 A f y) = (f y).
Proof. exact (@lem18740 A Prop f y). Qed.
Lemma lem18742 {A : Type'} (P : A -> Prop) (y : A) : (term72 A P y) = (P y).
Proof. exact (@lem18741 A P y). Qed.
Lemma lem18743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem18744 {A : Type'} (P : A -> Prop) (y : A) : (term73 A P y) = (term74 A P y).
Proof. exact (MK_COMB (@lem18743) (@lem18742 A P y)). Qed.
Lemma lem18745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem18746 {A : Type'} (P : A -> Prop) (y : A) : (term75 A P y) = (term76 A P y).
Proof. exact (MK_COMB (@lem18745) (@lem18744 A P y)). Qed.
Lemma lem18749 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem18750 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term77 A P x y) = (term78 A P x y).
Proof. exact (MK_COMB (@lem18746 A P y) (@lem18749 A x y)). Qed.
Lemma lem18753 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term79 A P x y) = (term50 A P x y).
Proof. exact (MK_COMB (@lem18736 A P x) (@lem18750 A P x y)). Qed.
Lemma lem18756 {A : Type'} (P : A -> Prop) (x : A) : (term80 A P x) = (term52 A P x).
Proof. exact (fun_ext (fun y : A => @lem18753 A P x y)). Qed.
Lemma lem18757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18758 {A : Type'} (P : A -> Prop) (x : A) : (term81 A P x) = (term54 A P x).
Proof. exact (MK_COMB (@lem18757 A) (@lem18756 A P x)). Qed.
Lemma lem18763 {A : Type'} (P : A -> Prop) : (term82 A P) = (term56 A P).
Proof. exact (fun_ext (fun x : A => @lem18758 A P x)). Qed.
Lemma lem18764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18765 {A : Type'} (P : A -> Prop) : (term83 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem18764 A) (@lem18763 A P)). Qed.
Lemma lem18770 {A : Type'} (P : A -> Prop) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem18771 {A : Type'} (P : A -> Prop) : (term71 A P) = (term85 A P).
Proof. exact (MK_COMB (@lem18770 A P) (@lem18765 A P)). Qed.
Lemma lem18774 {A : Type'} (P : A -> Prop) : (term63 A P) = (term85 A P).
Proof. exact (TRANS (@lem18712 A P) (@lem18771 A P)). Qed.
Lemma lem18775 {A : Type'} (P : A -> Prop) : (term44 A P) = (term85 A P).
Proof. exact (TRANS (@lem18699 A P) (@lem18774 A P)). Qed.
Lemma lem18776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem18777 {A : Type'} (P : A -> Prop) : (term46 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem18776) (@lem18775 A P)). Qed.
Lemma lem18798 {A : Type'} (P : A -> Prop) : (term47 A P) = (term47 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem18799 {A : Type'} (P : A -> Prop) : ((term44 A P) = (term47 A P)) = ((term85 A P) = (term47 A P)).
Proof. exact (MK_COMB (@lem18777 A P) (@lem18798 A P)). Qed.
Lemma lem18802 {A : Type'} (P : A -> Prop) : ((term85 A P) = (term47 A P)) = ((term44 A P) = (term47 A P)).
Proof. exact (SYM (@lem18799 A P)). Qed.
Lemma lem18853 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem18399 A y x) (@lem18398 A x y)). Qed.
Lemma lem18854 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem18853 A y x). Qed.
Lemma lem18855 {A : Type'} (x : A) (y : A) : (y = x) = (x = y).
Proof. exact (@lem18854 A x y). Qed.
Lemma lem18861 {A : Type'} (P : A -> Prop) (y : A) : (term76 A P y) = (term76 A P y).
Proof. exact (eq_refl (term76 A P y)). Qed.
Lemma lem18862 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term87 A P y x) = (term78 A P x y).
Proof. exact (MK_COMB (@lem18861 A P y) (@lem18855 A x y)). Qed.
Lemma lem18865 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = (term76 A P x).
Proof. exact (eq_refl (term76 A P x)). Qed.
Lemma lem18866 {A : Type'} (P : A -> Prop) (x : A) (y : A) : (term88 A P y x) = (term50 A P x y).
Proof. exact (MK_COMB (@lem18865 A P x) (@lem18862 A P x y)). Qed.
Lemma lem18869 {A : Type'} (P : A -> Prop) (x : A) : (term89 A P x) = (term52 A P x).
Proof. exact (fun_ext (fun y : A => @lem18866 A P x y)). Qed.
Lemma lem18870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18871 {A : Type'} (P : A -> Prop) (x : A) : (term90 A P x) = (term54 A P x).
Proof. exact (MK_COMB (@lem18870 A) (@lem18869 A P x)). Qed.
Lemma lem18876 {A : Type'} (P : A -> Prop) : (term91 A P) = (term56 A P).
Proof. exact (fun_ext (fun x : A => @lem18871 A P x)). Qed.
Lemma lem18877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem18878 {A : Type'} (P : A -> Prop) : (term92 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem18877 A) (@lem18876 A P)). Qed.
Lemma lem18883 {A : Type'} (P : A -> Prop) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem18884 {A : Type'} (P : A -> Prop) : (term47 A P) = (term85 A P).
Proof. exact (MK_COMB (@lem18883 A P) (@lem18878 A P)). Qed.
Lemma lem18887 {A : Type'} (P : A -> Prop) : (term86 A P) = (term86 A P).
Proof. exact (eq_refl (term86 A P)). Qed.
Lemma lem18888 {A : Type'} (P : A -> Prop) : ((term85 A P) = (term47 A P)) = ((term85 A P) = (term85 A P)).
Proof. exact (MK_COMB (@lem18887 A P) (@lem18884 A P)). Qed.
Lemma lem18890 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem18891 (x : Prop) : (x = x) = True.
Proof. exact (@lem18890 Prop x). Qed.
Lemma lem18892 {A : Type'} (P : A -> Prop) : ((term85 A P) = (term85 A P)) = True.
Proof. exact (@lem18891 (term85 A P)). Qed.
Lemma lem18893 {A : Type'} (P : A -> Prop) : ((term85 A P) = (term47 A P)) = True.
Proof. exact (TRANS (@lem18888 A P) (@lem18892 A P)). Qed.
Lemma lem18894 {A : Type'} (P : A -> Prop) : True = ((term85 A P) = (term47 A P)).
Proof. exact (SYM (@lem18893 A P)). Qed.
Lemma lem18895 {A : Type'} (P : A -> Prop) : (term85 A P) = (term47 A P).
Proof. exact (EQ_MP (@lem18894 A P) (@lem0)). Qed.
Lemma lem18896 {A : Type'} (P : A -> Prop) : (term44 A P) = (term47 A P).
Proof. exact (EQ_MP (@lem18802 A P) (@lem18895 A P)). Qed.
Lemma lem18897 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term47 A P).
Proof. exact (EQ_MP (@lem18654 A P) (@lem18896 A P)). Qed.
