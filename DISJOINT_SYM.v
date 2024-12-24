Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_SYM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3264370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3264371 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3264370 A s t). Qed.
Lemma lem3264375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3264376 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3264375 A s t). Qed.
Lemma lem3264377 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@INTER A s t) = (@EMPTY A)) = (term1 A s t).
Proof. exact (@lem3264376 A (@INTER A s t) (@EMPTY A)). Qed.
Lemma lem3264382 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = (term1 A s t).
Proof. exact (TRANS (@lem3264371 A s t) (@lem3264377 A s t)). Qed.
Lemma lem3264387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264388 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3264387) (@lem3264382 A s t)). Qed.
Lemma lem3264390 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3264391 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3264390 A s t). Qed.
Lemma lem3264392 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@DISJOINT A t s) = ((@INTER A t s) = (@EMPTY A)).
Proof. exact (@lem3264391 A t s). Qed.
Lemma lem3264396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3264397 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3264396 A s t). Qed.
Lemma lem3264398 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@INTER A t s) = (@EMPTY A)) = (term1 A t s).
Proof. exact (@lem3264397 A (@INTER A t s) (@EMPTY A)). Qed.
Lemma lem3264403 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@DISJOINT A t s) = (term1 A t s).
Proof. exact (TRANS (@lem3264392 A t s) (@lem3264398 A t s)). Qed.
Lemma lem3264408 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@DISJOINT A s t) = (@DISJOINT A t s)) = ((term1 A s t) = (term1 A t s)).
Proof. exact (MK_COMB (@lem3264388 A s t) (@lem3264403 A t s)). Qed.
Lemma lem3264413 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3264408 A t s)). Qed.
Lemma lem3264414 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264415 {A : Type'} (s : A -> Prop) : (term6 A s) = (term7 A s).
Proof. exact (MK_COMB (@lem3264414 A) (@lem3264413 A s)). Qed.
Lemma lem3264420 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3264415 A s)). Qed.
Lemma lem3264421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264422 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem3264421 A) (@lem3264420 A)). Qed.
Lemma lem3264427 {A : Type'} : (term11 A) = (term10 A).
Proof. exact (SYM (@lem3264422 A)). Qed.
Lemma lem3264445 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3264446 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (@lem3264445 A s x t). Qed.
Lemma lem3264450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3264451 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3264450 A P x). Qed.
Lemma lem3264452 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3264451 A s x). Qed.
Lemma lem3264453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264454 {A : Type'} (s : A -> Prop) (x : A) : (term14 A x s) = (term15 A s x).
Proof. exact (MK_COMB (@lem3264453) (@lem3264452 A s x)). Qed.
Lemma lem3264456 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3264457 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3264456 A P x). Qed.
Lemma lem3264458 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3264457 A t x). Qed.
Lemma lem3264459 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term13 A s x t) = (term16 A s t x).
Proof. exact (MK_COMB (@lem3264454 A s x) (@lem3264458 A t x)). Qed.
Lemma lem3264462 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term12 A x s t) = (term16 A s t x).
Proof. exact (TRANS (@lem3264446 A s x t) (@lem3264459 A s t x)). Qed.
Lemma lem3264463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264464 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A x s t) = (term18 A s t x).
Proof. exact (MK_COMB (@lem3264463) (@lem3264462 A s t x)). Qed.
Lemma lem3264466 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3264467 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3264466 A x). Qed.
Lemma lem3264468 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term12 A x s t) = (@IN A x (@EMPTY A))) = ((term16 A s t x) = False).
Proof. exact (MK_COMB (@lem3264464 A s t x) (@lem3264467 A x)). Qed.
Lemma lem3264470 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3264471 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term16 A s t x) = False) = (term19 A s t x).
Proof. exact (@lem3264470 (term16 A s t x)). Qed.
Lemma lem3264474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term12 A x s t) = (@IN A x (@EMPTY A))) = (term19 A s t x).
Proof. exact (TRANS (@lem3264468 A s t x) (@lem3264471 A s t x)). Qed.
Lemma lem3264475 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term21 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264474 A s t x)). Qed.
Lemma lem3264476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term22 A s t).
Proof. exact (MK_COMB (@lem3264476 A) (@lem3264475 A s t)). Qed.
Lemma lem3264482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264483 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3264482) (@lem3264477 A s t)). Qed.
Lemma lem3264491 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3264492 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (@lem3264491 A s x t). Qed.
Lemma lem3264493 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term12 A x t s) = (term13 A t x s).
Proof. exact (@lem3264492 A t x s). Qed.
Lemma lem3264497 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3264498 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3264497 A P x). Qed.
Lemma lem3264499 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3264498 A t x). Qed.
Lemma lem3264500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264501 {A : Type'} (t : A -> Prop) (x : A) : (term14 A x t) = (term15 A t x).
Proof. exact (MK_COMB (@lem3264500) (@lem3264499 A t x)). Qed.
Lemma lem3264503 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3264504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3264503 A P x). Qed.
Lemma lem3264505 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3264504 A s x). Qed.
Lemma lem3264506 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term13 A t x s) = (term16 A t s x).
Proof. exact (MK_COMB (@lem3264501 A t x) (@lem3264505 A s x)). Qed.
Lemma lem3264509 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term12 A x t s) = (term16 A t s x).
Proof. exact (TRANS (@lem3264493 A t x s) (@lem3264506 A t s x)). Qed.
Lemma lem3264510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264511 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term17 A x t s) = (term18 A t s x).
Proof. exact (MK_COMB (@lem3264510) (@lem3264509 A t s x)). Qed.
Lemma lem3264513 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3264514 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3264513 A x). Qed.
Lemma lem3264515 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term12 A x t s) = (@IN A x (@EMPTY A))) = ((term16 A t s x) = False).
Proof. exact (MK_COMB (@lem3264511 A t s x) (@lem3264514 A x)). Qed.
Lemma lem3264517 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3264518 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term16 A t s x) = False) = (term19 A t s x).
Proof. exact (@lem3264517 (term16 A t s x)). Qed.
Lemma lem3264521 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term12 A x t s) = (@IN A x (@EMPTY A))) = (term19 A t s x).
Proof. exact (TRANS (@lem3264515 A t s x) (@lem3264518 A t s x)). Qed.
Lemma lem3264522 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term20 A t s) = (term21 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264521 A t s x)). Qed.
Lemma lem3264523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264524 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1 A t s) = (term22 A t s).
Proof. exact (MK_COMB (@lem3264523 A) (@lem3264522 A t s)). Qed.
Lemma lem3264529 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term1 A s t) = (term1 A t s)) = ((term22 A s t) = (term22 A t s)).
Proof. exact (MK_COMB (@lem3264483 A s t) (@lem3264524 A t s)). Qed.
Lemma lem3264532 {A : Type'} (s : A -> Prop) : (term5 A s) = (term24 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3264529 A t s)). Qed.
Lemma lem3264533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264534 {A : Type'} (s : A -> Prop) : (term7 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3264533 A) (@lem3264532 A s)). Qed.
Lemma lem3264539 {A : Type'} : (term9 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3264534 A s)). Qed.
Lemma lem3264540 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264541 {A : Type'} : (term11 A) = (term27 A).
Proof. exact (MK_COMB (@lem3264540 A) (@lem3264539 A)). Qed.
Lemma lem3264546 {A : Type'} : (term27 A) = (term11 A).
Proof. exact (SYM (@lem3264541 A)). Qed.
Lemma lem3264548 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3264549 {A : Type'} : (term27 A) = (term29 A).
Proof. exact (@lem3264548 (term27 A)). Qed.
Lemma lem3264550 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (SYM (@lem3264549 A)). Qed.
Lemma lem3264551 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3264554 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3264555 {A : Type'} : term31 A.
Proof. exact (fun h0 : term29 A => @lem3264554 A h0). Qed.
Lemma lem3264556 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3264557 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3264558 {A : Type'} (h1 : term29 A) (h2 : term31 A) : term29 A.
Proof. exact (@lem3264556 A h2 (@lem3264557 A h1)). Qed.
Lemma lem3264559 {A : Type'} (h1 : term29 A) : term32 A.
Proof. exact (fun h0 : term31 A => @lem3264558 A h1 h0). Qed.
Lemma lem3264560 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3264561 {A : Type'} (h1 : term29 A) (h2 : term31 A) : term29 A.
Proof. exact (@lem3264559 A h1 (@lem3264560 A h2)). Qed.
Lemma lem3264562 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (fun h0 : term29 A => @lem3264561 A h0 h1). Qed.
Lemma lem3264563 {A : Type'} : term33 A.
Proof. exact (fun h0 : term31 A => @lem3264562 A h0). Qed.
Lemma lem3264566 {A : Type'} : term31 A.
Proof. exact (@lem3264563 A (@lem3264555 A)). Qed.
Lemma lem3264567 {A : Type'} : term31 A.
Proof. exact (@lem3264566 A). Qed.
Lemma lem3264569 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3264570 {A : Type'} : (term29 A) = (term34 A).
Proof. exact (@lem3264569 (term30 A)). Qed.
Lemma lem3264572 (t : Prop) : (term35 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3264573 {A : Type'} : (term34 A) = (term27 A).
Proof. exact (@lem3264572 (term27 A)). Qed.
Lemma lem3264598 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (TRANS (@lem3264570 A) (@lem3264573 A)). Qed.
Lemma lem3264605 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term19 A t s x) = (term19 A t s x).
Proof. exact (eq_refl (term19 A t s x)). Qed.
Lemma lem3264606 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term21 A t s) = (term21 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264605 A t s x)). Qed.
Lemma lem3264607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264608 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A t s) = (term22 A t s).
Proof. exact (MK_COMB (@lem3264607 A) (@lem3264606 A t s)). Qed.
Lemma lem3264615 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term19 A s t x) = (term19 A s t x).
Proof. exact (eq_refl (term19 A s t x)). Qed.
Lemma lem3264616 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term21 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264615 A s t x)). Qed.
Lemma lem3264617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264618 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term22 A s t).
Proof. exact (MK_COMB (@lem3264617 A) (@lem3264616 A s t)). Qed.
Lemma lem3264619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264620 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3264619) (@lem3264618 A s t)). Qed.
Lemma lem3264621 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term22 A s t) = (term22 A t s)) = ((term22 A s t) = (term22 A t s)).
Proof. exact (MK_COMB (@lem3264620 A s t) (@lem3264608 A t s)). Qed.
Lemma lem3264622 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3264621 A t s)). Qed.
Lemma lem3264623 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264624 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3264623 A) (@lem3264622 A s)). Qed.
Lemma lem3264625 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3264624 A s)). Qed.
Lemma lem3264626 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3264627 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem3264626 A) (@lem3264625 A)). Qed.
Lemma lem3264658 {A : Type'} : (term29 A) = (term27 A).
Proof. exact (TRANS (@lem3264598 A) (@lem3264627 A)). Qed.
Lemma lem3264659 {A : Type'} : (term27 A) = (term29 A).
Proof. exact (SYM (@lem3264658 A)). Qed.
Lemma lem3264661 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3264662 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term22 A s t) = (term22 A t s)) = (term36 A t s).
Proof. exact (@lem3264661 ((term22 A s t) = (term22 A t s))). Qed.
Lemma lem3264663 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term36 A t s) = ((term22 A s t) = (term22 A t s)).
Proof. exact (SYM (@lem3264662 A t s)). Qed.
Lemma lem3264664 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A t s) : term37 A t s.
Proof. exact (h1). Qed.
Lemma lem3264673 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term19 A s t x) = (term38 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3264678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term39 A s t x) = (term16 A s t x).
Proof. exact (@lem16933 (term16 A s t x)). Qed.
Lemma lem3264679 {A : Type'} (P : A -> Prop) : (term40 A P) = (term41 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3264680 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term43 A s t).
Proof. exact (@lem3264679 A (term21 A s t)). Qed.
Lemma lem3264681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term44 A s t x) = (term19 A s t x).
Proof. exact (eq_refl (term44 A s t x)). Qed.
Lemma lem3264682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3264683 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term39 A s t x).
Proof. exact (MK_COMB (@lem3264682) (@lem3264681 A s t x)). Qed.
Lemma lem3264684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term16 A s t x).
Proof. exact (TRANS (@lem3264683 A s t x) (@lem3264678 A s t x)). Qed.
Lemma lem3264685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term46 A s t) = (term47 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264684 A s t x)). Qed.
Lemma lem3264686 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term48 A s t).
Proof. exact (MK_COMB (@lem3264686 A) (@lem3264685 A s t)). Qed.
Lemma lem3264688 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term48 A s t).
Proof. exact (TRANS (@lem3264680 A s t) (@lem3264687 A s t)). Qed.
Lemma lem3264689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264673 A s t x)). Qed.
Lemma lem3264690 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264691 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3264690 A) (@lem3264689 A s t)). Qed.
Lemma lem3264700 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term19 A t s x) = (term38 A t s x).
Proof. exact (@lem17045 (t x) (s x)). Qed.
Lemma lem3264705 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term39 A t s x) = (term16 A t s x).
Proof. exact (@lem16933 (term16 A t s x)). Qed.
Lemma lem3264706 {A : Type'} (P : A -> Prop) : (term40 A P) = (term41 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3264707 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term42 A t s) = (term43 A t s).
Proof. exact (@lem3264706 A (term21 A t s)). Qed.
Lemma lem3264708 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term44 A t s x) = (term19 A t s x).
Proof. exact (eq_refl (term44 A t s x)). Qed.
Lemma lem3264709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3264710 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term45 A t s x) = (term39 A t s x).
Proof. exact (MK_COMB (@lem3264709) (@lem3264708 A t s x)). Qed.
Lemma lem3264711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term45 A t s x) = (term16 A t s x).
Proof. exact (TRANS (@lem3264710 A t s x) (@lem3264705 A t s x)). Qed.
Lemma lem3264712 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264711 A t s x)). Qed.
Lemma lem3264713 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264714 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3264713 A) (@lem3264712 A t s)). Qed.
Lemma lem3264715 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term42 A t s) = (term48 A t s).
Proof. exact (TRANS (@lem3264707 A t s) (@lem3264714 A t s)). Qed.
Lemma lem3264716 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term21 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264700 A t s x)). Qed.
Lemma lem3264717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264718 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3264717 A) (@lem3264716 A t s)). Qed.
Lemma lem3264719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term52 A s t).
Proof. exact (MK_COMB (@lem3264719) (@lem3264688 A s t)). Qed.
Lemma lem3264721 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term53 A t s) = (term54 A t s).
Proof. exact (MK_COMB (@lem3264720 A s t) (@lem3264718 A t s)). Qed.
Lemma lem3264722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264723 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term55 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3264722) (@lem3264691 A s t)). Qed.
Lemma lem3264724 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term57 A t s) = (term58 A t s).
Proof. exact (MK_COMB (@lem3264723 A s t) (@lem3264715 A t s)). Qed.
Lemma lem3264725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264726 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term59 A t s) = (term60 A t s).
Proof. exact (MK_COMB (@lem3264725) (@lem3264724 A t s)). Qed.
Lemma lem3264727 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term61 A t s) = (term62 A t s).
Proof. exact (MK_COMB (@lem3264726 A t s) (@lem3264721 A t s)). Qed.
Lemma lem3264728 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term37 A t s) = (term61 A t s).
Proof. exact (@lem17646 (term22 A s t) (term22 A t s)). Qed.
Lemma lem3264729 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term37 A t s) = (term62 A t s).
Proof. exact (TRANS (@lem3264728 A t s) (@lem3264727 A t s)). Qed.
Lemma lem3264852 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3264853 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (@lem3264852 A P Q). Qed.
Lemma lem3264854 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term65 A t s) = (term66 A t s).
Proof. exact (@lem3264853 A (term50 A s t) (term47 A t s)). Qed.
Lemma lem3264855 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term16 A t s x).
Proof. exact (eq_refl (term67 A t s x)). Qed.
Lemma lem3264856 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term68 A t s) = (term47 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264855 A t s x)). Qed.
Lemma lem3264857 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264858 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term69 A t s) = (term48 A t s).
Proof. exact (MK_COMB (@lem3264857 A) (@lem3264856 A t s)). Qed.
Lemma lem3264859 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term56 A s t) = (term56 A s t).
Proof. exact (eq_refl (term56 A s t)). Qed.
Lemma lem3264860 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term65 A t s) = (term58 A t s).
Proof. exact (MK_COMB (@lem3264859 A s t) (@lem3264858 A t s)). Qed.
Lemma lem3264861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264862 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term70 A t s) = (term71 A t s).
Proof. exact (MK_COMB (@lem3264861) (@lem3264860 A t s)). Qed.
Lemma lem3264863 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term67 A t s x) = (term16 A t s x).
Proof. exact (eq_refl (term67 A t s x)). Qed.
Lemma lem3264864 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term56 A s t) = (term56 A s t).
Proof. exact (eq_refl (term56 A s t)). Qed.
Lemma lem3264865 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term72 A t s x) = (term73 A t s x).
Proof. exact (MK_COMB (@lem3264864 A s t) (@lem3264863 A t s x)). Qed.
Lemma lem3264866 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term74 A t s) = (term75 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264865 A t s x)). Qed.
Lemma lem3264867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264868 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term66 A t s) = (term76 A t s).
Proof. exact (MK_COMB (@lem3264867 A) (@lem3264866 A t s)). Qed.
Lemma lem3264869 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term65 A t s) = (term66 A t s)) = ((term58 A t s) = (term76 A t s)).
Proof. exact (MK_COMB (@lem3264862 A t s) (@lem3264868 A t s)). Qed.
Lemma lem3264870 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term58 A t s) = (term76 A t s).
Proof. exact (EQ_MP (@lem3264869 A t s) (@lem3264854 A t s)). Qed.
Lemma lem3264871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264872 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term60 A t s) = (term77 A t s).
Proof. exact (MK_COMB (@lem3264871) (@lem3264870 A t s)). Qed.
Lemma lem3264874 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3264875 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (@lem3264874 A P Q). Qed.
Lemma lem3264876 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term80 A t s) = (term81 A t s).
Proof. exact (@lem3264875 A (term47 A s t) (term50 A t s)). Qed.
Lemma lem3264877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term67 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term67 A s t x)). Qed.
Lemma lem3264878 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = (term47 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264877 A s t x)). Qed.
Lemma lem3264879 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = (term48 A s t).
Proof. exact (MK_COMB (@lem3264879 A) (@lem3264878 A s t)). Qed.
Lemma lem3264881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264882 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term82 A s t) = (term52 A s t).
Proof. exact (MK_COMB (@lem3264881) (@lem3264880 A s t)). Qed.
Lemma lem3264883 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (eq_refl (term50 A t s)). Qed.
Lemma lem3264884 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term80 A t s) = (term54 A t s).
Proof. exact (MK_COMB (@lem3264882 A s t) (@lem3264883 A t s)). Qed.
Lemma lem3264885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264886 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term84 A t s).
Proof. exact (MK_COMB (@lem3264885) (@lem3264884 A t s)). Qed.
Lemma lem3264887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term67 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term67 A s t x)). Qed.
Lemma lem3264888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term85 A s t x) = (term86 A s t x).
Proof. exact (MK_COMB (@lem3264888) (@lem3264887 A s t x)). Qed.
Lemma lem3264890 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (eq_refl (term50 A t s)). Qed.
Lemma lem3264891 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term87 A x t s) = (term88 A x t s).
Proof. exact (MK_COMB (@lem3264889 A s t x) (@lem3264890 A t s)). Qed.
Lemma lem3264892 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term89 A t s) = (term90 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264891 A x t s)). Qed.
Lemma lem3264893 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264894 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term81 A t s) = (term91 A t s).
Proof. exact (MK_COMB (@lem3264893 A) (@lem3264892 A t s)). Qed.
Lemma lem3264895 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term80 A t s) = (term81 A t s)) = ((term54 A t s) = (term91 A t s)).
Proof. exact (MK_COMB (@lem3264886 A t s) (@lem3264894 A t s)). Qed.
Lemma lem3264896 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term91 A t s).
Proof. exact (EQ_MP (@lem3264895 A t s) (@lem3264876 A t s)). Qed.
Lemma lem3264897 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term62 A t s) = (term92 A t s).
Proof. exact (MK_COMB (@lem3264872 A t s) (@lem3264896 A t s)). Qed.
Lemma lem3264899 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3264900 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (@lem3264899 A P Q). Qed.
Lemma lem3264901 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term96 A t s).
Proof. exact (@lem3264900 A (term75 A t s) (term90 A t s)). Qed.
Lemma lem3264902 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term97 A t s x) = (term73 A t s x).
Proof. exact (eq_refl (term97 A t s x)). Qed.
Lemma lem3264903 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term98 A t s) = (term75 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264902 A t s x)). Qed.
Lemma lem3264904 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264905 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term99 A t s) = (term76 A t s).
Proof. exact (MK_COMB (@lem3264904 A) (@lem3264903 A t s)). Qed.
Lemma lem3264906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264907 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term100 A t s) = (term77 A t s).
Proof. exact (MK_COMB (@lem3264906) (@lem3264905 A t s)). Qed.
Lemma lem3264908 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term101 A t s x) = (term88 A x t s).
Proof. exact (eq_refl (term101 A t s x)). Qed.
Lemma lem3264909 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term102 A t s) = (term90 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264908 A x t s)). Qed.
Lemma lem3264910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264911 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term103 A t s) = (term91 A t s).
Proof. exact (MK_COMB (@lem3264910 A) (@lem3264909 A t s)). Qed.
Lemma lem3264912 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term92 A t s).
Proof. exact (MK_COMB (@lem3264907 A t s) (@lem3264911 A t s)). Qed.
Lemma lem3264913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3264914 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term104 A t s) = (term105 A t s).
Proof. exact (MK_COMB (@lem3264913) (@lem3264912 A t s)). Qed.
Lemma lem3264915 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term97 A t s x) = (term73 A t s x).
Proof. exact (eq_refl (term97 A t s x)). Qed.
Lemma lem3264916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264917 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term106 A t s x) = (term107 A t s x).
Proof. exact (MK_COMB (@lem3264916) (@lem3264915 A t s x)). Qed.
Lemma lem3264918 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term101 A t s x) = (term88 A x t s).
Proof. exact (eq_refl (term101 A t s x)). Qed.
Lemma lem3264919 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term108 A t s x) = (term109 A x t s).
Proof. exact (MK_COMB (@lem3264917 A t s x) (@lem3264918 A x t s)). Qed.
Lemma lem3264920 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term110 A t s) = (term111 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264919 A x t s)). Qed.
Lemma lem3264921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3264922 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term96 A t s) = (term112 A t s).
Proof. exact (MK_COMB (@lem3264921 A) (@lem3264920 A t s)). Qed.
Lemma lem3264923 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term95 A t s) = (term96 A t s)) = ((term92 A t s) = (term112 A t s)).
Proof. exact (MK_COMB (@lem3264914 A t s) (@lem3264922 A t s)). Qed.
Lemma lem3264924 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term112 A t s).
Proof. exact (EQ_MP (@lem3264923 A t s) (@lem3264901 A t s)). Qed.
Lemma lem3264926 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term62 A t s) = (term112 A t s).
Proof. exact (TRANS (@lem3264897 A t s) (@lem3264924 A t s)). Qed.
Lemma lem3264927 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term37 A t s) = (term112 A t s).
Proof. exact (TRANS (@lem3264729 A t s) (@lem3264926 A t s)). Qed.
Lemma lem3264928 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A t s) : term112 A t s.
Proof. exact (EQ_MP (@lem3264927 A t s) (@lem3264664 A t s h1)). Qed.
Lemma lem3264929 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term109 A x t s) : term109 A x t s.
Proof. exact (h1). Qed.
Lemma lem3264942 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term38 A t s x) = (term38 A t s x).
Proof. exact (eq_refl (term38 A t s x)). Qed.
Lemma lem3264943 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term49 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3264942 A t s x)). Qed.
Lemma lem3264944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264945 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3264944 A) (@lem3264943 A t s)). Qed.
Lemma lem3264956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term86 A s t x).
Proof. exact (eq_refl (term86 A s t x)). Qed.
Lemma lem3264957 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term88 A x t s) = (term88 A x t s).
Proof. exact (MK_COMB (@lem3264956 A s t x) (@lem3264945 A t s)). Qed.
Lemma lem3264966 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term16 A t s x) = (term16 A t s x).
Proof. exact (eq_refl (term16 A t s x)). Qed.
Lemma lem3264979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term38 A s t x) = (term38 A s t x).
Proof. exact (eq_refl (term38 A s t x)). Qed.
Lemma lem3264980 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3264979 A s t x)). Qed.
Lemma lem3264981 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3264982 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3264981 A) (@lem3264980 A s t)). Qed.
Lemma lem3264983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3264984 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term56 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3264983) (@lem3264982 A s t)). Qed.
Lemma lem3264985 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term73 A t s x) = (term73 A t s x).
Proof. exact (MK_COMB (@lem3264984 A s t) (@lem3264966 A t s x)). Qed.
Lemma lem3264986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3264987 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term107 A t s x) = (term107 A t s x).
Proof. exact (MK_COMB (@lem3264986) (@lem3264985 A t s x)). Qed.
Lemma lem3264988 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term109 A x t s) = (term109 A x t s).
Proof. exact (MK_COMB (@lem3264987 A t s x) (@lem3264957 A x t s)). Qed.
Lemma lem3264989 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term109 A x t s) : term109 A x t s.
Proof. exact (EQ_MP (@lem3264988 A x t s) (@lem3264929 A x t s h1)). Qed.
Lemma lem3264990 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term73 A t s x.
Proof. exact (h1). Qed.
Lemma lem3264991 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term88 A x t s.
Proof. exact (h1). Qed.
Lemma lem3264992 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term16 A t s x.
Proof. exact (proj2 (@lem3264990 A t s x h1)). Qed.
Lemma lem3264993 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term50 A s t.
Proof. exact (proj1 (@lem3264990 A t s x h1)). Qed.
Lemma lem3264996 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term50 A t s.
Proof. exact (proj2 (@lem3264991 A x t s h1)). Qed.
Lemma lem3264997 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term16 A s t x.
Proof. exact (proj1 (@lem3264991 A x t s h1)). Qed.
Lemma lem3265007 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term38 A s t x) = (term38 A s t x).
Proof. exact (eq_refl (term38 A s t x)). Qed.
Lemma lem3265008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3265007 A s t x)). Qed.
Lemma lem3265009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265011 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3265009 A) (@lem3265008 A s t)). Qed.
Lemma lem3265012 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term50 A s t.
Proof. exact (EQ_MP (@lem3265011 A s t) (@lem3264993 A t s x h1)). Qed.
Lemma lem3265028 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term38 A t s x) = (term38 A t s x).
Proof. exact (eq_refl (term38 A t s x)). Qed.
Lemma lem3265029 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term49 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3265028 A t s x)). Qed.
Lemma lem3265030 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3265032 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3265030 A) (@lem3265029 A t s)). Qed.
Lemma lem3265033 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term50 A t s.
Proof. exact (EQ_MP (@lem3265032 A t s) (@lem3264996 A x t s h1)). Qed.
Lemma lem3265042 {A : Type'} (_33410 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term113 A s t _33410.
Proof. exact (@lem3265012 A t s x h1 _33410). Qed.
Lemma lem3265043 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33410 : A) : (term113 A s t _33410) = (term38 A s t _33410).
Proof. exact (eq_refl (term113 A s t _33410)). Qed.
Lemma lem3265045 {A : Type'} (_33411 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term113 A t s _33411.
Proof. exact (@lem3265033 A x t s h1 _33411). Qed.
Lemma lem3265046 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33411 : A) : (term113 A t s _33411) = (term38 A t s _33411).
Proof. exact (eq_refl (term113 A t s _33411)). Qed.
Lemma lem3265053 {A : Type'} (_33410 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term38 A s t _33410.
Proof. exact (EQ_MP (@lem3265043 A s t _33410) (@lem3265042 A _33410 t s x h1)). Qed.
Lemma lem3265063 {A : Type'} (_33411 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term38 A t s _33411.
Proof. exact (EQ_MP (@lem3265046 A t s _33411) (@lem3265045 A _33411 x t s h1)). Qed.
Lemma lem3265069 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : s x.
Proof. exact (proj2 (@lem3264992 A t s x h1)). Qed.
Lemma lem3265070 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term114 A s x.
Proof. exact (fun h0 : term115 A s x => @lem3265069 A t s x h1). Qed.
Lemma lem3265072 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265073 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (s x).
Proof. exact (@lem3265072 (s x)). Qed.
Lemma lem3265074 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : s x.
Proof. exact (EQ_MP (@lem3265073 A s x) (@lem3265070 A t s x h1)). Qed.
Lemma lem3265076 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : t x.
Proof. exact (proj1 (@lem3264992 A t s x h1)). Qed.
Lemma lem3265077 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term114 A t x.
Proof. exact (fun h0 : term115 A t x => @lem3265076 A t s x h1). Qed.
Lemma lem3265079 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265080 {A : Type'} (t : A -> Prop) (x : A) : (term114 A t x) = (t x).
Proof. exact (@lem3265079 (t x)). Qed.
Lemma lem3265081 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : t x.
Proof. exact (EQ_MP (@lem3265080 A t x) (@lem3265077 A t s x h1)). Qed.
Lemma lem3265083 (a : Prop) (b : Prop) : (term117 a b) = (term118 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3265084 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33410 : A) : (term38 A s t _33410) = (term19 A s t _33410).
Proof. exact (@lem3265083 (s _33410) (t _33410)). Qed.
Lemma lem3265086 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3265087 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33410 : A) : (term19 A s t _33410) = (term119 A s t _33410).
Proof. exact (@lem3265086 (term16 A s t _33410)). Qed.
Lemma lem3265088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33410 : A) : (term38 A s t _33410) = (term119 A s t _33410).
Proof. exact (TRANS (@lem3265084 A s t _33410) (@lem3265087 A s t _33410)). Qed.
Lemma lem3265090 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term16 A s t x.
Proof. exact (conj (@lem3265074 A t s x h1) (@lem3265081 A t s x h1)). Qed.
Lemma lem3265092 {A : Type'} (_33410 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term119 A s t _33410.
Proof. exact (EQ_MP (@lem3265088 A s t _33410) (@lem3265053 A _33410 t s x h1)). Qed.
Lemma lem3265093 {A : Type'} (_33410 : A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term119 A s t _33410.
Proof. exact (@lem3265092 A _33410 t s x h1). Qed.
Lemma lem3265094 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term119 A s t x.
Proof. exact (@lem3265093 A x t s x h1). Qed.
Lemma lem3265097 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : False.
Proof. exact (@lem3265094 A t s x h1 (@lem3265090 A t s x h1)). Qed.
Lemma lem3265098 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : term120.
Proof. exact (fun h0 : ~ False => @lem3265097 A t s x h1). Qed.
Lemma lem3265100 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265101 : term120 = False.
Proof. exact (@lem3265100 False). Qed.
Lemma lem3265102 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term73 A t s x) : False.
Proof. exact (EQ_MP (@lem3265101) (@lem3265098 A t s x h1)). Qed.
Lemma lem3265104 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : t x.
Proof. exact (proj2 (@lem3264997 A x t s h1)). Qed.
Lemma lem3265105 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term114 A t x.
Proof. exact (fun h0 : term115 A t x => @lem3265104 A x t s h1). Qed.
Lemma lem3265107 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265108 {A : Type'} (t : A -> Prop) (x : A) : (term114 A t x) = (t x).
Proof. exact (@lem3265107 (t x)). Qed.
Lemma lem3265109 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : t x.
Proof. exact (EQ_MP (@lem3265108 A t x) (@lem3265105 A x t s h1)). Qed.
Lemma lem3265111 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : s x.
Proof. exact (proj1 (@lem3264997 A x t s h1)). Qed.
Lemma lem3265112 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term114 A s x.
Proof. exact (fun h0 : term115 A s x => @lem3265111 A x t s h1). Qed.
Lemma lem3265114 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265115 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (s x).
Proof. exact (@lem3265114 (s x)). Qed.
Lemma lem3265116 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : s x.
Proof. exact (EQ_MP (@lem3265115 A s x) (@lem3265112 A x t s h1)). Qed.
Lemma lem3265118 (a : Prop) (b : Prop) : (term117 a b) = (term118 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3265119 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33411 : A) : (term38 A t s _33411) = (term19 A t s _33411).
Proof. exact (@lem3265118 (t _33411) (s _33411)). Qed.
Lemma lem3265121 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3265122 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33411 : A) : (term19 A t s _33411) = (term119 A t s _33411).
Proof. exact (@lem3265121 (term16 A t s _33411)). Qed.
Lemma lem3265123 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33411 : A) : (term38 A t s _33411) = (term119 A t s _33411).
Proof. exact (TRANS (@lem3265119 A t s _33411) (@lem3265122 A t s _33411)). Qed.
Lemma lem3265125 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term16 A t s x.
Proof. exact (conj (@lem3265109 A x t s h1) (@lem3265116 A x t s h1)). Qed.
Lemma lem3265127 {A : Type'} (_33411 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term119 A t s _33411.
Proof. exact (EQ_MP (@lem3265123 A t s _33411) (@lem3265063 A _33411 x t s h1)). Qed.
Lemma lem3265128 {A : Type'} (_33411 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term119 A t s _33411.
Proof. exact (@lem3265127 A _33411 x t s h1). Qed.
Lemma lem3265129 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term119 A t s x.
Proof. exact (@lem3265128 A x x t s h1). Qed.
Lemma lem3265132 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : False.
Proof. exact (@lem3265129 A x t s h1 (@lem3265125 A x t s h1)). Qed.
Lemma lem3265133 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : term120.
Proof. exact (fun h0 : ~ False => @lem3265132 A x t s h1). Qed.
Lemma lem3265135 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3265136 : term120 = False.
Proof. exact (@lem3265135 False). Qed.
Lemma lem3265137 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term88 A x t s) : False.
Proof. exact (EQ_MP (@lem3265136) (@lem3265133 A x t s h1)). Qed.
Lemma lem3265138 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term109 A x t s) : False.
Proof. exact (or_elim (@lem3264989 A x t s h1) (fun h0 : term73 A t s x => @lem3265102 A t s x h0) (fun h0 : term88 A x t s => @lem3265137 A x t s h0)). Qed.
Lemma lem3265139 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term109 A x t s) : (term109 A x t s) = False.
Proof. exact (prop_ext (fun h2 : term109 A x t s => @lem3265138 A x t s h1) (fun h2 : False => @lem3264989 A x t s h1)). Qed.
Lemma lem3265140 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term109 A x t s) : False.
Proof. exact (EQ_MP (@lem3265139 A x t s h1) (@lem3264989 A x t s h1)). Qed.
Lemma lem3265141 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A t s) : False.
Proof. exact (ex_elim (@lem3264928 A t s h1) (fun x : A => fun h0 : term111 A t s x => @lem3265140 A x t s h0)). Qed.
Lemma lem3265142 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A t s) : (term37 A t s) = False.
Proof. exact (prop_ext (fun h2 : term37 A t s => @lem3265141 A t s h1) (fun h2 : False => @lem3264664 A t s h1)). Qed.
Lemma lem3265143 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term37 A t s) : False.
Proof. exact (EQ_MP (@lem3265142 A t s h1) (@lem3264664 A t s h1)). Qed.
Lemma lem3265144 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term36 A t s.
Proof. exact (fun h0 : term37 A t s => @lem3265143 A t s h0). Qed.
Lemma lem3265145 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A s t) = (term22 A t s).
Proof. exact (EQ_MP (@lem3264663 A t s) (@lem3265144 A t s)). Qed.
Lemma lem3265150 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (fun t : A -> Prop => @lem3265145 A t s). Qed.
Lemma lem3265155 {A : Type'} : term27 A.
Proof. exact (fun s : A -> Prop => @lem3265150 A s). Qed.
Lemma lem3265156 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3264659 A) (@lem3265155 A)). Qed.
Lemma lem3265158 {A : Type'} : term29 A.
Proof. exact (@lem3264567 A (@lem3265156 A)). Qed.
Lemma lem3265159 {A : Type'} (h1 : term30 A) : False.
Proof. exact (@lem3265158 A (@lem3264551 A h1)). Qed.
Lemma lem3265160 {A : Type'} (h1 : term30 A) : (term30 A) = False.
Proof. exact (prop_ext (fun h2 : term30 A => @lem3265159 A h1) (fun h2 : False => @lem3264551 A h1)). Qed.
Lemma lem3265161 {A : Type'} (h1 : term30 A) : False.
Proof. exact (EQ_MP (@lem3265160 A h1) (@lem3264551 A h1)). Qed.
Lemma lem3265162 {A : Type'} : term29 A.
Proof. exact (fun h0 : term30 A => @lem3265161 A h0). Qed.
Lemma lem3265163 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem3264550 A) (@lem3265162 A)). Qed.
Lemma lem3265164 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3264546 A) (@lem3265163 A)). Qed.
Lemma lem3265165 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3264427 A) (@lem3265164 A)). Qed.
