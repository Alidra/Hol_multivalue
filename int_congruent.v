Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_congruent_term_abbrevs.
Require Import cong_spec.
Require Import int_divides_spec.
Require Import int_mod_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2437409 (b : int) : term0 b.
Proof. exact (@lem2429416 b). Qed.
Lemma lem2437410 (b : int) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem2437411 (b : int) : term1 b.
Proof. exact (EQ_MP (@lem2437410 b) (@lem2437409 b)). Qed.
Lemma lem2437412 (b : int) (a : int) : term2 b a.
Proof. exact (@lem2437411 b a). Qed.
Lemma lem2437413 (b : int) (a : int) : (term2 b a) = ((int_divides a b) = (term3 b a)).
Proof. exact (eq_refl (term2 b a)). Qed.
Lemma lem2437415 {A : Type'} (rel : type1402 A) : term4 A rel.
Proof. exact (@lem2427819 A rel). Qed.
Lemma lem2437416 {A : Type'} (rel : type1402 A) : (term4 A rel) = (term5 A rel).
Proof. exact (eq_refl (term4 A rel)). Qed.
Lemma lem2437417 {A : Type'} (rel : type1402 A) : term5 A rel.
Proof. exact (EQ_MP (@lem2437416 A rel) (@lem2437415 A rel)). Qed.
Lemma lem2437418 {A : Type'} (rel : type1402 A) (x : A) : term6 A rel x.
Proof. exact (@lem2437417 A rel x). Qed.
Lemma lem2437419 {A : Type'} (rel : type1402 A) (x : A) : (term6 A rel x) = (term7 A rel x).
Proof. exact (eq_refl (term6 A rel x)). Qed.
Lemma lem2437420 {A : Type'} (rel : type1402 A) (x : A) : term7 A rel x.
Proof. exact (EQ_MP (@lem2437419 A rel x) (@lem2437418 A rel x)). Qed.
Lemma lem2437421 {A : Type'} (rel : type1402 A) (x : A) (y : A) : term8 A rel x y.
Proof. exact (@lem2437420 A rel x y). Qed.
Lemma lem2437422 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (term8 A rel x y) = ((@eq2 A x y rel) = (rel x y)).
Proof. exact (eq_refl (term8 A rel x y)). Qed.
Lemma lem2437424 (n : int) : term9 n.
Proof. exact (@lem2437408 n). Qed.
Lemma lem2437425 (n : int) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem2437426 (n : int) : term10 n.
Proof. exact (EQ_MP (@lem2437425 n) (@lem2437424 n)). Qed.
Lemma lem2437427 (n : int) (x : int) : term11 n x.
Proof. exact (@lem2437426 n x). Qed.
Lemma lem2437428 (n : int) (x : int) : (term11 n x) = (term12 n x).
Proof. exact (eq_refl (term11 n x)). Qed.
Lemma lem2437429 (n : int) (x : int) : term12 n x.
Proof. exact (EQ_MP (@lem2437428 n x) (@lem2437427 n x)). Qed.
Lemma lem2437430 (n : int) (x : int) (y : int) : term13 n x y.
Proof. exact (@lem2437429 n x y). Qed.
Lemma lem2437431 (n : int) (x : int) (y : int) : (term13 n x y) = ((int_mod n x y) = (term14 n x y)).
Proof. exact (eq_refl (term13 n x y)). Qed.
Lemma lem2437448 {A : Type'} (rel : type1402 A) (x : A) (y : A) : (@eq2 A x y rel) = (rel x y).
Proof. exact (EQ_MP (@lem2437422 A rel x y) (@lem2437421 A rel x y)). Qed.
Lemma lem2437449 (rel : type1550) (x : int) (y : int) : (@eq2 int x y rel) = (rel x y).
Proof. exact (@lem2437448 int rel x y). Qed.
Lemma lem2437450 (n : int) (x : int) (y : int) : (term15 x y n) = (int_mod n x y).
Proof. exact (@lem2437449 (int_mod n) x y). Qed.
Lemma lem2437452 (n : int) (x : int) (y : int) : (int_mod n x y) = (term14 n x y).
Proof. exact (EQ_MP (@lem2437431 n x y) (@lem2437430 n x y)). Qed.
Lemma lem2437454 (b : int) (a : int) : (int_divides a b) = (term3 b a).
Proof. exact (EQ_MP (@lem2437413 b a) (@lem2437412 b a)). Qed.
Lemma lem2437455 (x : int) (y : int) (n : int) : (term14 n x y) = (term16 x y n).
Proof. exact (@lem2437454 (int_sub x y) n). Qed.
Lemma lem2437460 (x : int) (y : int) (n : int) : (int_mod n x y) = (term16 x y n).
Proof. exact (TRANS (@lem2437452 n x y) (@lem2437455 x y n)). Qed.
Lemma lem2437461 (x : int) (y : int) (n : int) : (term15 x y n) = (term16 x y n).
Proof. exact (TRANS (@lem2437450 n x y) (@lem2437460 x y n)). Qed.
Lemma lem2437464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2437465 (x : int) (y : int) (n : int) : (term17 x y n) = (term18 x y n).
Proof. exact (MK_COMB (@lem2437464) (@lem2437461 x y n)). Qed.
Lemma lem2437472 (x : int) (y : int) (n : int) : (term16 x y n) = (term16 x y n).
Proof. exact (eq_refl (term16 x y n)). Qed.
Lemma lem2437473 (x : int) (y : int) (n : int) : ((term15 x y n) = (term16 x y n)) = ((term16 x y n) = (term16 x y n)).
Proof. exact (MK_COMB (@lem2437465 x y n) (@lem2437472 x y n)). Qed.
Lemma lem2437475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2437476 (x : Prop) : (x = x) = True.
Proof. exact (@lem2437475 Prop x). Qed.
Lemma lem2437477 (x : int) (y : int) (n : int) : ((term16 x y n) = (term16 x y n)) = True.
Proof. exact (@lem2437476 (term16 x y n)). Qed.
Lemma lem2437480 (x : int) (y : int) (n : int) : (term19 x y n) = (term19 x y n).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem2437481 (x : int) (y : int) (n : int) : (term19 x y n) = (((term16 x y n) = (term16 x y n)) = True).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem2437482 (x : int) (y : int) (n : int) : (term20 x y n) = (term20 x y n).
Proof. exact (eq_refl (term20 x y n)). Qed.
Lemma lem2437483 (x : int) (y : int) (n : int) : ((term19 x y n) = (term19 x y n)) = ((term19 x y n) = (((term16 x y n) = (term16 x y n)) = True)).
Proof. exact (MK_COMB (@lem2437482 x y n) (@lem2437481 x y n)). Qed.
Lemma lem2437484 (x : int) (y : int) (n : int) : (term19 x y n) = (((term16 x y n) = (term16 x y n)) = True).
Proof. exact (eq_refl (term19 x y n)). Qed.
Lemma lem2437485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2437486 (x : int) (y : int) (n : int) : (term20 x y n) = (term21 x y n).
Proof. exact (MK_COMB (@lem2437485) (@lem2437484 x y n)). Qed.
Lemma lem2437487 (x : int) (y : int) (n : int) : (((term16 x y n) = (term16 x y n)) = True) = (((term16 x y n) = (term16 x y n)) = True).
Proof. exact (eq_refl (((term16 x y n) = (term16 x y n)) = True)). Qed.
Lemma lem2437488 (x : int) (y : int) (n : int) : ((term19 x y n) = (((term16 x y n) = (term16 x y n)) = True)) = ((((term16 x y n) = (term16 x y n)) = True) = (((term16 x y n) = (term16 x y n)) = True)).
Proof. exact (MK_COMB (@lem2437486 x y n) (@lem2437487 x y n)). Qed.
Lemma lem2437489 (x : int) (y : int) (n : int) : ((term19 x y n) = (term19 x y n)) = ((((term16 x y n) = (term16 x y n)) = True) = (((term16 x y n) = (term16 x y n)) = True)).
Proof. exact (TRANS (@lem2437483 x y n) (@lem2437488 x y n)). Qed.
Lemma lem2437490 (x : int) (y : int) (n : int) : (((term16 x y n) = (term16 x y n)) = True) = (((term16 x y n) = (term16 x y n)) = True).
Proof. exact (EQ_MP (@lem2437489 x y n) (@lem2437480 x y n)). Qed.
Lemma lem2437491 (x : int) (y : int) (n : int) : ((term16 x y n) = (term16 x y n)) = True.
Proof. exact (EQ_MP (@lem2437490 x y n) (@lem2437477 x y n)). Qed.
Lemma lem2437492 (x : int) (y : int) (n : int) : ((term15 x y n) = (term16 x y n)) = True.
Proof. exact (TRANS (@lem2437473 x y n) (@lem2437491 x y n)). Qed.
Lemma lem2437493 (x : int) (y : int) : (term22 x y) = term23.
Proof. exact (fun_ext (fun n : int => @lem2437492 x y n)). Qed.
Lemma lem2437494 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437495 (x : int) (y : int) : (term24 x y) = term25.
Proof. exact (MK_COMB (@lem2437494) (@lem2437493 x y)). Qed.
Lemma lem2437497 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2437498 (t : Prop) : (term27 t) = t.
Proof. exact (@lem2437497 int t). Qed.
Lemma lem2437499 : term25 = True.
Proof. exact (@lem2437498 True). Qed.
Lemma lem2437500 (x : int) (y : int) : (term24 x y) = True.
Proof. exact (TRANS (@lem2437495 x y) (@lem2437499)). Qed.
Lemma lem2437501 (x : int) : (term28 x) = term23.
Proof. exact (fun_ext (fun y : int => @lem2437500 x y)). Qed.
Lemma lem2437502 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437503 (x : int) : (term29 x) = term25.
Proof. exact (MK_COMB (@lem2437502) (@lem2437501 x)). Qed.
Lemma lem2437505 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2437506 (t : Prop) : (term27 t) = t.
Proof. exact (@lem2437505 int t). Qed.
Lemma lem2437507 : term25 = True.
Proof. exact (@lem2437506 True). Qed.
Lemma lem2437508 (x : int) : (term29 x) = True.
Proof. exact (TRANS (@lem2437503 x) (@lem2437507)). Qed.
Lemma lem2437509 : term30 = term23.
Proof. exact (fun_ext (fun x : int => @lem2437508 x)). Qed.
Lemma lem2437510 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2437511 : term31 = term25.
Proof. exact (MK_COMB (@lem2437510) (@lem2437509)). Qed.
Lemma lem2437513 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2437514 (t : Prop) : (term27 t) = t.
Proof. exact (@lem2437513 int t). Qed.
Lemma lem2437515 : term25 = True.
Proof. exact (@lem2437514 True). Qed.
Lemma lem2437516 : term31 = True.
Proof. exact (TRANS (@lem2437511) (@lem2437515)). Qed.
Lemma lem2437517 : True = term31.
Proof. exact (SYM (@lem2437516)). Qed.
Lemma lem2437518 : term31.
Proof. exact (EQ_MP (@lem2437517) (@lem0)). Qed.
