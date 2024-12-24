Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_TYBIT1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_TYBIT1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7935394 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7935395 {A : Type'} : (@FINITE (tybit1 A) (@UNIV (tybit1 A))) = (term1 A).
Proof. exact (@lem7935394 (@FINITE (tybit1 A) (@UNIV (tybit1 A)))). Qed.
Lemma lem7935396 {A : Type'} : (term1 A) = (@FINITE (tybit1 A) (@UNIV (tybit1 A))).
Proof. exact (SYM (@lem7935395 A)). Qed.
Lemma lem7935397 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7935398 {A : Type'} : term3 A.
Proof. exact (@lem7933087 A). Qed.
Lemma lem7935399 {A : Type'} : term4 A.
Proof. exact (@lem7933087 (tybit1 A)). Qed.
Lemma lem7935400 {A : Type'} : term5 A.
Proof. exact (@lem3863773 (type1681 A)). Qed.
Lemma lem7935401 {A : Type'} : term6 A.
Proof. exact (@lem3863773 (tybit1 A)). Qed.
Lemma lem7935405 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7935406 {A : Type'} : term8 A.
Proof. exact (fun h0 : term7 A => @lem7935405 A h0). Qed.
Lemma lem7935407 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem7935408 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7935409 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem7935407 A h2 (@lem7935408 A h1)). Qed.
Lemma lem7935410 {A : Type'} (h1 : term7 A) : term9 A.
Proof. exact (fun h0 : term8 A => @lem7935409 A h1 h0). Qed.
Lemma lem7935411 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem7935412 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem7935410 A h1 (@lem7935411 A h2)). Qed.
Lemma lem7935413 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun h0 : term7 A => @lem7935412 A h0 h1). Qed.
Lemma lem7935414 {A : Type'} : term10 A.
Proof. exact (fun h0 : term8 A => @lem7935413 A h0). Qed.
Lemma lem7935417 {A : Type'} : term8 A.
Proof. exact (@lem7935414 A (@lem7935406 A)). Qed.
Lemma lem7935418 {A : Type'} : term8 A.
Proof. exact (@lem7935417 A). Qed.
Lemma lem7935448 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7935449 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem7935448 (term4 A)). Qed.
Lemma lem7935450 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (eq_refl (term13 A)). Qed.
Lemma lem7935451 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem7935450 A) (@lem7935449 A)). Qed.
Lemma lem7935454 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem7935455 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7935454 A) (@lem7935451 A)). Qed.
Lemma lem7935458 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7935459 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7935458 A) (@lem7935455 A)). Qed.
Lemma lem7935462 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7935469 {A : Type'} : (term7 A) = (term23 A).
Proof. exact (MK_COMB (@lem7935462 A) (@lem7935459 A)). Qed.
Lemma lem7935476 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7935485 {A : Type'} (s : type1346 A) (n : nat) : ((@HAS_SIZE (tybit1 (tybit1 A)) s n) = (term24 A s n)) = ((@HAS_SIZE (tybit1 (tybit1 A)) s n) = (term24 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (tybit1 (tybit1 A)) s n) = (term24 A s n))). Qed.
Lemma lem7935486 {A : Type'} (s : type1346 A) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935485 A s n)). Qed.
Lemma lem7935487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935488 {A : Type'} (s : type1346 A) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem7935487) (@lem7935486 A s)). Qed.
Lemma lem7935489 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : type1346 A => @lem7935488 A s)). Qed.
Lemma lem7935490 {A : Type'} : (@all ((tybit1 (tybit1 A)) -> Prop)) = (@all ((tybit1 (tybit1 A)) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 (tybit1 A)) -> Prop))). Qed.
Lemma lem7935491 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem7935490 A) (@lem7935489 A)). Qed.
Lemma lem7935492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7935493 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem7935492) (@lem7935491 A)). Qed.
Lemma lem7935494 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7935493 A) (@lem7935476 A)). Qed.
Lemma lem7935503 {A : Type'} (s : type1351 A) (n : nat) : ((@HAS_SIZE (tybit1 A) s n) = (term28 A s n)) = ((@HAS_SIZE (tybit1 A) s n) = (term28 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (tybit1 A) s n) = (term28 A s n))). Qed.
Lemma lem7935504 {A : Type'} (s : type1351 A) : (term29 A s) = (term29 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935503 A s n)). Qed.
Lemma lem7935505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935506 {A : Type'} (s : type1351 A) : (term30 A s) = (term30 A s).
Proof. exact (MK_COMB (@lem7935505) (@lem7935504 A s)). Qed.
Lemma lem7935507 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935506 A s)). Qed.
Lemma lem7935508 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935509 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem7935508 A) (@lem7935507 A)). Qed.
Lemma lem7935510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7935511 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7935510) (@lem7935509 A)). Qed.
Lemma lem7935512 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem7935511 A) (@lem7935494 A)). Qed.
Lemma lem7935517 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7935518 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem7935517 A) (@lem7935512 A)). Qed.
Lemma lem7935557 {A : Type'} : (term7 A) = (term23 A).
Proof. exact (TRANS (@lem7935469 A) (@lem7935518 A)). Qed.
Lemma lem7935558 {A : Type'} : (term23 A) = (term7 A).
Proof. exact (SYM (@lem7935557 A)). Qed.
Lemma lem7935560 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem7935569 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7935580 {A : Type'} (s : type1351 A) (n : nat) : (term32 A s n) = (term33 A s n).
Proof. exact (@lem17045 (@FINITE (tybit1 A) s) ((@CARD (tybit1 A) s) = n)). Qed.
Lemma lem7935586 {A : Type'} (s : type1351 A) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem7935588 {A : Type'} (s : type1351 A) (n : nat) : (term35 A s n) = (term35 A s n).
Proof. exact (eq_refl (term35 A s n)). Qed.
Lemma lem7935589 {A : Type'} (s : type1351 A) (n : nat) : (term36 A s n) = (term37 A s n).
Proof. exact (MK_COMB (@lem7935588 A s n) (@lem7935580 A s n)). Qed.
Lemma lem7935590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7935591 {A : Type'} (s : type1351 A) (n : nat) : (term38 A s n) = (term39 A s n).
Proof. exact (MK_COMB (@lem7935590) (@lem7935589 A s n)). Qed.
Lemma lem7935592 {A : Type'} (s : type1351 A) (n : nat) : (term40 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem7935591 A s n) (@lem7935586 A s n)). Qed.
Lemma lem7935593 {A : Type'} (s : type1351 A) (n : nat) : ((@HAS_SIZE (tybit1 A) s n) = (term28 A s n)) = (term40 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (tybit1 A) s n) (term28 A s n)). Qed.
Lemma lem7935594 {A : Type'} (s : type1351 A) (n : nat) : ((@HAS_SIZE (tybit1 A) s n) = (term28 A s n)) = (term41 A s n).
Proof. exact (TRANS (@lem7935593 A s n) (@lem7935592 A s n)). Qed.
Lemma lem7935595 {A : Type'} (s : type1351 A) : (term29 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935594 A s n)). Qed.
Lemma lem7935596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935597 {A : Type'} (s : type1351 A) : (term30 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem7935596) (@lem7935595 A s)). Qed.
Lemma lem7935598 {A : Type'} : (term31 A) = (term44 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935597 A s)). Qed.
Lemma lem7935599 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935600 {A : Type'} : (term6 A) = (term45 A).
Proof. exact (MK_COMB (@lem7935599 A) (@lem7935598 A)). Qed.
Lemma lem7935606 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7935607 (P : nat -> Prop) (Q : nat -> Prop) : (term48 P Q) = (term49 P Q).
Proof. exact (@lem7935606 nat P Q). Qed.
Lemma lem7935608 {A : Type'} (s : type1351 A) : (term50 A s) = (term51 A s).
Proof. exact (@lem7935607 (term52 A s) (term53 A s)). Qed.
Lemma lem7935609 {A : Type'} (s : type1351 A) (n : nat) : (term54 A s n) = (term37 A s n).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem7935610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7935611 {A : Type'} (s : type1351 A) (n : nat) : (term55 A s n) = (term39 A s n).
Proof. exact (MK_COMB (@lem7935610) (@lem7935609 A s n)). Qed.
Lemma lem7935612 {A : Type'} (s : type1351 A) (n : nat) : (term56 A s n) = (term34 A s n).
Proof. exact (eq_refl (term56 A s n)). Qed.
Lemma lem7935613 {A : Type'} (s : type1351 A) (n : nat) : (term57 A s n) = (term41 A s n).
Proof. exact (MK_COMB (@lem7935611 A s n) (@lem7935612 A s n)). Qed.
Lemma lem7935614 {A : Type'} (s : type1351 A) : (term58 A s) = (term42 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935613 A s n)). Qed.
Lemma lem7935615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935616 {A : Type'} (s : type1351 A) : (term50 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem7935615) (@lem7935614 A s)). Qed.
Lemma lem7935617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7935618 {A : Type'} (s : type1351 A) : (term59 A s) = (term60 A s).
Proof. exact (MK_COMB (@lem7935617) (@lem7935616 A s)). Qed.
Lemma lem7935619 {A : Type'} (s : type1351 A) (n : nat) : (term54 A s n) = (term37 A s n).
Proof. exact (eq_refl (term54 A s n)). Qed.
Lemma lem7935620 {A : Type'} (s : type1351 A) : (term61 A s) = (term52 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935619 A s n)). Qed.
Lemma lem7935621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935622 {A : Type'} (s : type1351 A) : (term62 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem7935621) (@lem7935620 A s)). Qed.
Lemma lem7935623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7935624 {A : Type'} (s : type1351 A) : (term64 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem7935623) (@lem7935622 A s)). Qed.
Lemma lem7935625 {A : Type'} (s : type1351 A) (n : nat) : (term56 A s n) = (term34 A s n).
Proof. exact (eq_refl (term56 A s n)). Qed.
Lemma lem7935626 {A : Type'} (s : type1351 A) : (term66 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7935625 A s n)). Qed.
Lemma lem7935627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7935628 {A : Type'} (s : type1351 A) : (term67 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem7935627) (@lem7935626 A s)). Qed.
Lemma lem7935629 {A : Type'} (s : type1351 A) : (term51 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem7935624 A s) (@lem7935628 A s)). Qed.
Lemma lem7935630 {A : Type'} (s : type1351 A) : ((term50 A s) = (term51 A s)) = ((term43 A s) = (term69 A s)).
Proof. exact (MK_COMB (@lem7935618 A s) (@lem7935629 A s)). Qed.
Lemma lem7935631 {A : Type'} (s : type1351 A) : (term43 A s) = (term69 A s).
Proof. exact (EQ_MP (@lem7935630 A s) (@lem7935608 A s)). Qed.
Lemma lem7935728 {A : Type'} : (term44 A) = (term70 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935631 A s)). Qed.
Lemma lem7935729 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935730 {A : Type'} : (term45 A) = (term71 A).
Proof. exact (MK_COMB (@lem7935729 A) (@lem7935728 A)). Qed.
Lemma lem7935732 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term46 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7935733 {A : Type'} (P : type387 A) (Q : type387 A) : (term72 A P Q) = (term73 A P Q).
Proof. exact (@lem7935732 (type1351 A) P Q). Qed.
Lemma lem7935734 {A : Type'} : (term74 A) = (term75 A).
Proof. exact (@lem7935733 A (term76 A) (term77 A)). Qed.
Lemma lem7935735 {A : Type'} (s : type1351 A) : (term78 A s) = (term63 A s).
Proof. exact (eq_refl (term78 A s)). Qed.
Lemma lem7935736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7935737 {A : Type'} (s : type1351 A) : (term79 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem7935736) (@lem7935735 A s)). Qed.
Lemma lem7935738 {A : Type'} (s : type1351 A) : (term80 A s) = (term68 A s).
Proof. exact (eq_refl (term80 A s)). Qed.
Lemma lem7935739 {A : Type'} (s : type1351 A) : (term81 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem7935737 A s) (@lem7935738 A s)). Qed.
Lemma lem7935740 {A : Type'} : (term82 A) = (term70 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935739 A s)). Qed.
Lemma lem7935741 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935742 {A : Type'} : (term74 A) = (term71 A).
Proof. exact (MK_COMB (@lem7935741 A) (@lem7935740 A)). Qed.
Lemma lem7935743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7935744 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem7935743) (@lem7935742 A)). Qed.
Lemma lem7935745 {A : Type'} (s : type1351 A) : (term78 A s) = (term63 A s).
Proof. exact (eq_refl (term78 A s)). Qed.
Lemma lem7935746 {A : Type'} : (term85 A) = (term76 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935745 A s)). Qed.
Lemma lem7935747 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935748 {A : Type'} : (term86 A) = (term87 A).
Proof. exact (MK_COMB (@lem7935747 A) (@lem7935746 A)). Qed.
Lemma lem7935749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7935750 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem7935749) (@lem7935748 A)). Qed.
Lemma lem7935751 {A : Type'} (s : type1351 A) : (term80 A s) = (term68 A s).
Proof. exact (eq_refl (term80 A s)). Qed.
Lemma lem7935752 {A : Type'} : (term90 A) = (term77 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7935751 A s)). Qed.
Lemma lem7935753 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7935754 {A : Type'} : (term91 A) = (term92 A).
Proof. exact (MK_COMB (@lem7935753 A) (@lem7935752 A)). Qed.
Lemma lem7935755 {A : Type'} : (term75 A) = (term93 A).
Proof. exact (MK_COMB (@lem7935750 A) (@lem7935754 A)). Qed.
Lemma lem7935756 {A : Type'} : ((term74 A) = (term75 A)) = ((term71 A) = (term93 A)).
Proof. exact (MK_COMB (@lem7935744 A) (@lem7935755 A)). Qed.
Lemma lem7935757 {A : Type'} : (term71 A) = (term93 A).
Proof. exact (EQ_MP (@lem7935756 A) (@lem7935734 A)). Qed.
Lemma lem7935864 {A : Type'} : (term45 A) = (term93 A).
Proof. exact (TRANS (@lem7935730 A) (@lem7935757 A)). Qed.
Lemma lem7935865 {A : Type'} : (term6 A) = (term93 A).
Proof. exact (TRANS (@lem7935600 A) (@lem7935864 A)). Qed.
Lemma lem7935866 {A : Type'} (h1 : term6 A) : term93 A.
Proof. exact (EQ_MP (@lem7935865 A) (@lem7935560 A h1)). Qed.
Lemma lem7936169 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7936181 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7936204 {A : Type'} (s : type1351 A) (n : nat) : (term34 A s n) = (term34 A s n).
Proof. exact (eq_refl (term34 A s n)). Qed.
Lemma lem7936205 {A : Type'} (s : type1351 A) : (term53 A s) = (term53 A s).
Proof. exact (fun_ext (fun n : nat => @lem7936204 A s n)). Qed.
Lemma lem7936206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7936207 {A : Type'} (s : type1351 A) : (term68 A s) = (term68 A s).
Proof. exact (MK_COMB (@lem7936206) (@lem7936205 A s)). Qed.
Lemma lem7936208 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7936207 A s)). Qed.
Lemma lem7936209 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7936210 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (MK_COMB (@lem7936209 A) (@lem7936208 A)). Qed.
Lemma lem7936235 {A : Type'} (s : type1351 A) (n : nat) : (term37 A s n) = (term37 A s n).
Proof. exact (eq_refl (term37 A s n)). Qed.
Lemma lem7936236 {A : Type'} (s : type1351 A) : (term52 A s) = (term52 A s).
Proof. exact (fun_ext (fun n : nat => @lem7936235 A s n)). Qed.
Lemma lem7936237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7936238 {A : Type'} (s : type1351 A) : (term63 A s) = (term63 A s).
Proof. exact (MK_COMB (@lem7936237) (@lem7936236 A s)). Qed.
Lemma lem7936239 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7936238 A s)). Qed.
Lemma lem7936240 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7936241 {A : Type'} : (term87 A) = (term87 A).
Proof. exact (MK_COMB (@lem7936240 A) (@lem7936239 A)). Qed.
Lemma lem7936242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7936243 {A : Type'} : (term89 A) = (term89 A).
Proof. exact (MK_COMB (@lem7936242) (@lem7936241 A)). Qed.
Lemma lem7936244 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (MK_COMB (@lem7936243 A) (@lem7936210 A)). Qed.
Lemma lem7936245 {A : Type'} (h1 : term6 A) : term93 A.
Proof. exact (EQ_MP (@lem7936244 A) (@lem7935866 A h1)). Qed.
Lemma lem7936335 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7936364 {A : Type'} (h1 : term6 A) : term92 A.
Proof. exact (proj2 (@lem7936245 A h1)). Qed.
Lemma lem7936369 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7936373 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7936465 {A : Type'} (s : type1351 A) (n : nat) : (term34 A s n) = (term94 A s n).
Proof. exact (@lem19490 (@FINITE (tybit1 A) s) (term95 A s n) ((@CARD (tybit1 A) s) = n)). Qed.
Lemma lem7936466 {A : Type'} (s : type1351 A) : (term53 A s) = (term96 A s).
Proof. exact (fun_ext (fun n : nat => @lem7936465 A s n)). Qed.
Lemma lem7936467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7936468 {A : Type'} (s : type1351 A) : (term68 A s) = (term97 A s).
Proof. exact (MK_COMB (@lem7936467) (@lem7936466 A s)). Qed.
Lemma lem7936469 {A : Type'} : (term77 A) = (term98 A).
Proof. exact (fun_ext (fun s : type1351 A => @lem7936468 A s)). Qed.
Lemma lem7936470 {A : Type'} : (@all ((tybit1 A) -> Prop)) = (@all ((tybit1 A) -> Prop)).
Proof. exact (eq_refl (@all ((tybit1 A) -> Prop))). Qed.
Lemma lem7936472 {A : Type'} : (term92 A) = (term99 A).
Proof. exact (MK_COMB (@lem7936470 A) (@lem7936469 A)). Qed.
Lemma lem7936473 {A : Type'} (h1 : term6 A) : term99 A.
Proof. exact (EQ_MP (@lem7936472 A) (@lem7936364 A h1)). Qed.
Lemma lem7936492 {A : Type'} (_103897 : type1351 A) (h1 : term6 A) : term100 A _103897.
Proof. exact (@lem7936473 A h1 _103897). Qed.
Lemma lem7936493 {A : Type'} (_103897 : type1351 A) : (term100 A _103897) = (term97 A _103897).
Proof. exact (eq_refl (term100 A _103897)). Qed.
Lemma lem7936494 {A : Type'} (_103897 : type1351 A) (h1 : term6 A) : term97 A _103897.
Proof. exact (EQ_MP (@lem7936493 A _103897) (@lem7936492 A _103897 h1)). Qed.
Lemma lem7936495 {A : Type'} (_103897 : type1351 A) (_103898 : nat) (h1 : term6 A) : term101 A _103897 _103898.
Proof. exact (@lem7936494 A _103897 h1 _103898). Qed.
Lemma lem7936496 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term101 A _103897 _103898) = (term94 A _103897 _103898).
Proof. exact (eq_refl (term101 A _103897 _103898)). Qed.
Lemma lem7936497 {A : Type'} (_103897 : type1351 A) (_103898 : nat) (h1 : term6 A) : term94 A _103897 _103898.
Proof. exact (EQ_MP (@lem7936496 A _103897 _103898) (@lem7936495 A _103897 _103898 h1)). Qed.
Lemma lem7936503 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem7936505 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7936533 {A : Type'} (_103898 : nat) (_103897 : type1351 A) (h1 : term6 A) : term102 A _103898 _103897.
Proof. exact (proj1 (@lem7936497 A _103897 _103898 h1)). Qed.
Lemma lem7936709 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem7936710 {A : Type'} (h1 : term3 A) : term103 A.
Proof. exact (fun h0 : term104 A => @lem7936709 A h1). Qed.
Lemma lem7936712 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7936713 {A : Type'} : (term103 A) = (term3 A).
Proof. exact (@lem7936712 (term3 A)). Qed.
Lemma lem7936714 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (EQ_MP (@lem7936713 A) (@lem7936710 A h1)). Qed.
Lemma lem7936720 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7936721 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term102 A _103898 _103897) = (term106 A _103897 _103898).
Proof. exact (@lem7936720 (@FINITE (tybit1 A) _103897) (term95 A _103897 _103898)). Qed.
Lemma lem7936727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7936728 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term107 A _103898 _103897) = (term108 A _103897 _103898).
Proof. exact (MK_COMB (@lem7936727) (@lem7936721 A _103897 _103898)). Qed.
Lemma lem7936734 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term106 A _103897 _103898) = (term106 A _103897 _103898).
Proof. exact (eq_refl (term106 A _103897 _103898)). Qed.
Lemma lem7936735 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : ((term102 A _103898 _103897) = (term106 A _103897 _103898)) = ((term106 A _103897 _103898) = (term106 A _103897 _103898)).
Proof. exact (MK_COMB (@lem7936728 A _103897 _103898) (@lem7936734 A _103897 _103898)). Qed.
Lemma lem7936737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7936738 (x : Prop) : (x = x) = True.
Proof. exact (@lem7936737 Prop x). Qed.
Lemma lem7936739 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : ((term106 A _103897 _103898) = (term106 A _103897 _103898)) = True.
Proof. exact (@lem7936738 (term106 A _103897 _103898)). Qed.
Lemma lem7936740 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : ((term102 A _103898 _103897) = (term106 A _103897 _103898)) = True.
Proof. exact (TRANS (@lem7936735 A _103897 _103898) (@lem7936739 A _103897 _103898)). Qed.
Lemma lem7936741 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : True = ((term102 A _103898 _103897) = (term106 A _103897 _103898)).
Proof. exact (SYM (@lem7936740 A _103897 _103898)). Qed.
Lemma lem7936742 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term102 A _103898 _103897) = (term106 A _103897 _103898).
Proof. exact (EQ_MP (@lem7936741 A _103897 _103898) (@lem0)). Qed.
Lemma lem7936743 {A : Type'} (_103897 : type1351 A) (_103898 : nat) (h1 : term6 A) : term106 A _103897 _103898.
Proof. exact (EQ_MP (@lem7936742 A _103897 _103898) (@lem7936533 A _103898 _103897 h1)). Qed.
Lemma lem7936745 (b : Prop) (a : Prop) : (a \/ b) = (term109 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7936746 {A : Type'} (_103898 : nat) (_103897 : type1351 A) : (term106 A _103897 _103898) = (term110 A _103898 _103897).
Proof. exact (@lem7936745 (term95 A _103897 _103898) (@FINITE (tybit1 A) _103897)). Qed.
Lemma lem7936748 (a : Prop) : (term111 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7936749 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term112 A _103897 _103898) = (@HAS_SIZE (tybit1 A) _103897 _103898).
Proof. exact (@lem7936748 (@HAS_SIZE (tybit1 A) _103897 _103898)). Qed.
Lemma lem7936750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7936751 {A : Type'} (_103897 : type1351 A) (_103898 : nat) : (term113 A _103897 _103898) = (term114 A _103897 _103898).
Proof. exact (MK_COMB (@lem7936750) (@lem7936749 A _103897 _103898)). Qed.
Lemma lem7936752 {A : Type'} (_103897 : type1351 A) : (@FINITE (tybit1 A) _103897) = (@FINITE (tybit1 A) _103897).
Proof. exact (eq_refl (@FINITE (tybit1 A) _103897)). Qed.
Lemma lem7936753 {A : Type'} (_103898 : nat) (_103897 : type1351 A) : (term110 A _103898 _103897) = (term115 A _103898 _103897).
Proof. exact (MK_COMB (@lem7936751 A _103897 _103898) (@lem7936752 A _103897)). Qed.
Lemma lem7936754 {A : Type'} (_103898 : nat) (_103897 : type1351 A) : (term106 A _103897 _103898) = (term115 A _103898 _103897).
Proof. exact (TRANS (@lem7936746 A _103898 _103897) (@lem7936753 A _103898 _103897)). Qed.
Lemma lem7936757 {A : Type'} (_103898 : nat) (_103897 : type1351 A) (h1 : term6 A) : term115 A _103898 _103897.
Proof. exact (EQ_MP (@lem7936754 A _103898 _103897) (@lem7936743 A _103897 _103898 h1)). Qed.
Lemma lem7936758 {A : Type'} (_103898 : nat) (_103897 : type1351 A) (h1 : term6 A) : term115 A _103898 _103897.
Proof. exact (@lem7936757 A _103898 _103897 h1). Qed.
Lemma lem7936759 {A : Type'} (h1 : term6 A) : term116 A.
Proof. exact (@lem7936758 A (term117 A) (@UNIV (tybit1 A)) h1). Qed.
Lemma lem7936762 {A : Type'} (h1 : term6 A) (h2 : term3 A) : @FINITE (tybit1 A) (@UNIV (tybit1 A)).
Proof. exact (@lem7936759 A h1 (@lem7936714 A h2)). Qed.
Lemma lem7936763 {A : Type'} (h1 : term6 A) (h2 : term3 A) : term118 A.
Proof. exact (fun h0 : term2 A => @lem7936762 A h1 h2). Qed.
Lemma lem7936765 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7936766 {A : Type'} : (term118 A) = (@FINITE (tybit1 A) (@UNIV (tybit1 A))).
Proof. exact (@lem7936765 (@FINITE (tybit1 A) (@UNIV (tybit1 A)))). Qed.
Lemma lem7936767 {A : Type'} (h1 : term6 A) (h2 : term3 A) : @FINITE (tybit1 A) (@UNIV (tybit1 A)).
Proof. exact (EQ_MP (@lem7936766 A) (@lem7936763 A h1 h2)). Qed.
Lemma lem7936770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7936772 {A : Type'} : (term2 A) = (term119 A).
Proof. exact (@lem7936770 (@FINITE (tybit1 A) (@UNIV (tybit1 A)))). Qed.
Lemma lem7936775 {A : Type'} (h1 : term2 A) : term119 A.
Proof. exact (EQ_MP (@lem7936772 A) (@lem7936503 A h1)). Qed.
Lemma lem7936778 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (@lem7936775 A h2 (@lem7936767 A h1 h3)). Qed.
Lemma lem7936779 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term120.
Proof. exact (fun h0 : ~ False => @lem7936778 A h1 h2 h3). Qed.
Lemma lem7936781 (p : Prop) : (term105 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7936782 : term120 = False.
Proof. exact (@lem7936781 False). Qed.
Lemma lem7936783 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936782) (@lem7936779 A h1 h2 h3)). Qed.
Lemma lem7936784 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7936783 A h1 h2 h3) (fun h4 : False => @lem7936505 A h3)). Qed.
Lemma lem7936785 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936784 A h1 h2 h3) (@lem7936505 A h3)). Qed.
Lemma lem7936786 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7936785 A h1 h2 h3) (fun h4 : False => @lem7936503 A h2)). Qed.
Lemma lem7936787 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936786 A h1 h2 h3) (@lem7936503 A h2)). Qed.
Lemma lem7936788 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7936787 A h1 h2 h3) (fun h4 : False => @lem7936373 A h3)). Qed.
Lemma lem7936789 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936788 A h1 h2 h3) (@lem7936373 A h3)). Qed.
Lemma lem7936790 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7936789 A h1 h2 h3) (fun h4 : False => @lem7936369 A h2)). Qed.
Lemma lem7936791 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936790 A h1 h2 h3) (@lem7936369 A h2)). Qed.
Lemma lem7936792 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7936791 A h1 h2 h3) (fun h4 : False => @lem7936373 A h3)). Qed.
Lemma lem7936793 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936792 A h1 h2 h3) (@lem7936373 A h3)). Qed.
Lemma lem7936794 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7936793 A h1 h2 h3) (fun h4 : False => @lem7936369 A h2)). Qed.
Lemma lem7936795 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936794 A h1 h2 h3) (@lem7936369 A h2)). Qed.
Lemma lem7936796 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7936795 A h1 h2 h3) (fun h4 : False => @lem7936335 A h3)). Qed.
Lemma lem7936797 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936796 A h1 h2 h3) (@lem7936335 A h3)). Qed.
Lemma lem7936798 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7936797 A h1 h2 h3) (fun h4 : False => @lem7936181 A h2)). Qed.
Lemma lem7936799 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936798 A h1 h2 h3) (@lem7936181 A h2)). Qed.
Lemma lem7936800 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h4 : term3 A => @lem7936799 A h1 h2 h3) (fun h4 : False => @lem7936169 A h3)). Qed.
Lemma lem7936801 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936800 A h1 h2 h3) (@lem7936169 A h3)). Qed.
Lemma lem7936802 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h4 : term2 A => @lem7936801 A h1 h2 h3) (fun h4 : False => @lem7935569 A h2)). Qed.
Lemma lem7936803 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : False.
Proof. exact (EQ_MP (@lem7936802 A h1 h2 h3) (@lem7935569 A h2)). Qed.
Lemma lem7936804 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term11 A.
Proof. exact (fun h0 : term4 A => @lem7936803 A h1 h2 h3). Qed.
Lemma lem7936805 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem7936806 {A : Type'} (h1 : term6 A) (h2 : term2 A) (h3 : term3 A) : term12 A.
Proof. exact (EQ_MP (@lem7936805 A) (@lem7936804 A h1 h2 h3)). Qed.
Lemma lem7936807 {A : Type'} (h1 : term6 A) (h2 : term2 A) : term15 A.
Proof. exact (fun h0 : term3 A => @lem7936806 A h1 h2 h0). Qed.
Lemma lem7936808 {A : Type'} (h1 : term6 A) (h2 : term2 A) : term18 A.
Proof. exact (fun h0 : term5 A => @lem7936807 A h1 h2). Qed.
Lemma lem7936809 {A : Type'} (h1 : term2 A) : term21 A.
Proof. exact (fun h0 : term6 A => @lem7936808 A h0 h1). Qed.
Lemma lem7936810 {A : Type'} : term23 A.
Proof. exact (fun h0 : term2 A => @lem7936809 A h0). Qed.
Lemma lem7936811 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem7935558 A) (@lem7936810 A)). Qed.
Lemma lem7936813 {A : Type'} : term7 A.
Proof. exact (@lem7935418 A (@lem7936811 A)). Qed.
Lemma lem7936814 {A : Type'} (h1 : term2 A) : term20 A.
Proof. exact (@lem7936813 A (@lem7935397 A h1)). Qed.
Lemma lem7936815 {A : Type'} (h1 : term2 A) : term17 A.
Proof. exact (@lem7936814 A h1 (@lem7935401 A)). Qed.
Lemma lem7936816 {A : Type'} (h1 : term2 A) : term14 A.
Proof. exact (@lem7936815 A h1 (@lem7935400 A)). Qed.
Lemma lem7936817 {A : Type'} (h1 : term2 A) : term11 A.
Proof. exact (@lem7936816 A h1 (@lem7935398 A)). Qed.
Lemma lem7936818 {A : Type'} (h1 : term2 A) : False.
Proof. exact (@lem7936817 A h1 (@lem7935399 A)). Qed.
Lemma lem7936819 {A : Type'} (h1 : term2 A) : (term2 A) = False.
Proof. exact (prop_ext (fun h2 : term2 A => @lem7936818 A h1) (fun h2 : False => @lem7935397 A h1)). Qed.
Lemma lem7936820 {A : Type'} (h1 : term2 A) : False.
Proof. exact (EQ_MP (@lem7936819 A h1) (@lem7935397 A h1)). Qed.
Lemma lem7936821 {A : Type'} : term1 A.
Proof. exact (fun h0 : term2 A => @lem7936820 A h0). Qed.
Lemma lem7936822 {A : Type'} : @FINITE (tybit1 A) (@UNIV (tybit1 A)).
Proof. exact (EQ_MP (@lem7935396 A) (@lem7936821 A)). Qed.
