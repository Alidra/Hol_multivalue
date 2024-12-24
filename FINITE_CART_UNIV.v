Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CART_UNIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_CART_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem7996388 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7996389 {A N : Type'} : (term1 A N) = (term2 A N).
Proof. exact (@lem7996388 (term1 A N)). Qed.
Lemma lem7996390 {A N : Type'} : (term2 A N) = (term1 A N).
Proof. exact (SYM (@lem7996389 A N)). Qed.
Lemma lem7996391 {A N : Type'} (h1 : term3 A N) : term3 A N.
Proof. exact (h1). Qed.
Lemma lem7996392 {A N : Type'} : term4 A N.
Proof. exact (@lem7990967 A N). Qed.
Lemma lem7996393 {A N : Type'} : term5 A N.
Proof. exact (@lem7990967 (cart A N) N). Qed.
Lemma lem7996395 {A : Type'} : term6 A.
Proof. exact (@lem7990967 A A). Qed.
Lemma lem7996396 {A N : Type'} : term7 A N.
Proof. exact (@lem7990967 A (cart A N)). Qed.
Lemma lem7996397 {A N : Type'} : term8 A N.
Proof. exact (@lem3863773 (cart A N)). Qed.
Lemma lem7996398 {A N : Type'} : term9 A N.
Proof. exact (@lem3863773 (type0 A N)). Qed.
Lemma lem7996399 {A : Type'} : term10 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem7996400 {A N : Type'} : term11 A N.
Proof. exact (@lem3863773 (type1 A N)). Qed.
Lemma lem7996401 {A : Type'} : term12 A.
Proof. exact (@lem3863773 (cart A A)). Qed.
Lemma lem7996406 {A N : Type'} (h1 : term13 A N) : term13 A N.
Proof. exact (h1). Qed.
Lemma lem7996407 {A N : Type'} : term14 A N.
Proof. exact (fun h0 : term13 A N => @lem7996406 A N h0). Qed.
Lemma lem7996408 {A N : Type'} (h1 : term14 A N) : term14 A N.
Proof. exact (h1). Qed.
Lemma lem7996409 {A N : Type'} (h1 : term13 A N) : term13 A N.
Proof. exact (h1). Qed.
Lemma lem7996410 {A N : Type'} (h1 : term13 A N) (h2 : term14 A N) : term13 A N.
Proof. exact (@lem7996408 A N h2 (@lem7996409 A N h1)). Qed.
Lemma lem7996411 {A N : Type'} (h1 : term13 A N) : term15 A N.
Proof. exact (fun h0 : term14 A N => @lem7996410 A N h1 h0). Qed.
Lemma lem7996412 {A N : Type'} (h1 : term14 A N) : term14 A N.
Proof. exact (h1). Qed.
Lemma lem7996413 {A N : Type'} (h1 : term13 A N) (h2 : term14 A N) : term13 A N.
Proof. exact (@lem7996411 A N h1 (@lem7996412 A N h2)). Qed.
Lemma lem7996414 {A N : Type'} (h1 : term14 A N) : term14 A N.
Proof. exact (fun h0 : term13 A N => @lem7996413 A N h0 h1). Qed.
Lemma lem7996415 {A N : Type'} : term16 A N.
Proof. exact (fun h0 : term14 A N => @lem7996414 A N h0). Qed.
Lemma lem7996418 {A N : Type'} : term14 A N.
Proof. exact (@lem7996415 A N (@lem7996407 A N)). Qed.
Lemma lem7996419 {A N : Type'} : term14 A N.
Proof. exact (@lem7996418 A N). Qed.
Lemma lem7996509 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7996510 {A N : Type'} : (term17 A N) = (term18 A N).
Proof. exact (@lem7996509 (term5 A N)). Qed.
Lemma lem7996517 {A N : Type'} : (term19 A N) = (term19 A N).
Proof. exact (eq_refl (term19 A N)). Qed.
Lemma lem7996518 {A N : Type'} : (term20 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7996517 A N) (@lem7996510 A N)). Qed.
Lemma lem7996521 {A N : Type'} : (term22 A N) = (term22 A N).
Proof. exact (eq_refl (term22 A N)). Qed.
Lemma lem7996522 {A N : Type'} : (term23 A N) = (term24 A N).
Proof. exact (MK_COMB (@lem7996521 A N) (@lem7996518 A N)). Qed.
Lemma lem7996525 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem7996526 {A N : Type'} : (term26 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7996525 A) (@lem7996522 A N)). Qed.
Lemma lem7996529 {A N : Type'} : (term28 A N) = (term28 A N).
Proof. exact (eq_refl (term28 A N)). Qed.
Lemma lem7996530 {A N : Type'} : (term29 A N) = (term30 A N).
Proof. exact (MK_COMB (@lem7996529 A N) (@lem7996526 A N)). Qed.
Lemma lem7996533 {A N : Type'} : (term31 A N) = (term31 A N).
Proof. exact (eq_refl (term31 A N)). Qed.
Lemma lem7996534 {A N : Type'} : (term32 A N) = (term33 A N).
Proof. exact (MK_COMB (@lem7996533 A N) (@lem7996530 A N)). Qed.
Lemma lem7996537 {A N : Type'} : (term34 A N) = (term34 A N).
Proof. exact (eq_refl (term34 A N)). Qed.
Lemma lem7996538 {A N : Type'} : (term35 A N) = (term36 A N).
Proof. exact (MK_COMB (@lem7996537 A N) (@lem7996534 A N)). Qed.
Lemma lem7996541 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (eq_refl (term37 A)). Qed.
Lemma lem7996542 {A N : Type'} : (term38 A N) = (term39 A N).
Proof. exact (MK_COMB (@lem7996541 A) (@lem7996538 A N)). Qed.
Lemma lem7996545 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (eq_refl (term40 A)). Qed.
Lemma lem7996546 {A N : Type'} : (term41 A N) = (term42 A N).
Proof. exact (MK_COMB (@lem7996545 A) (@lem7996542 A N)). Qed.
Lemma lem7996549 {A N : Type'} : (term43 A N) = (term43 A N).
Proof. exact (eq_refl (term43 A N)). Qed.
Lemma lem7996556 {A N : Type'} : (term13 A N) = (term44 A N).
Proof. exact (MK_COMB (@lem7996549 A N) (@lem7996546 A N)). Qed.
Lemma lem7996561 {A N : Type'} (m : nat) : (term45 A N m) = (term45 A N m).
Proof. exact (eq_refl (term45 A N m)). Qed.
Lemma lem7996562 {A N : Type'} : (term46 A N) = (term46 A N).
Proof. exact (fun_ext (fun m : nat => @lem7996561 A N m)). Qed.
Lemma lem7996563 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996564 {A N : Type'} : (term5 A N) = (term5 A N).
Proof. exact (MK_COMB (@lem7996563) (@lem7996562 A N)). Qed.
Lemma lem7996565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7996566 {A N : Type'} : (term18 A N) = (term18 A N).
Proof. exact (MK_COMB (@lem7996565) (@lem7996564 A N)). Qed.
Lemma lem7996571 {A N : Type'} (m : nat) : (term47 A N m) = (term47 A N m).
Proof. exact (eq_refl (term47 A N m)). Qed.
Lemma lem7996572 {A N : Type'} : (term48 A N) = (term48 A N).
Proof. exact (fun_ext (fun m : nat => @lem7996571 A N m)). Qed.
Lemma lem7996573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996574 {A N : Type'} : (term7 A N) = (term7 A N).
Proof. exact (MK_COMB (@lem7996573) (@lem7996572 A N)). Qed.
Lemma lem7996575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996576 {A N : Type'} : (term19 A N) = (term19 A N).
Proof. exact (MK_COMB (@lem7996575) (@lem7996574 A N)). Qed.
Lemma lem7996577 {A N : Type'} : (term21 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7996576 A N) (@lem7996566 A N)). Qed.
Lemma lem7996582 {A N : Type'} (m : nat) : (term49 A N m) = (term49 A N m).
Proof. exact (eq_refl (term49 A N m)). Qed.
Lemma lem7996583 {A N : Type'} : (term50 A N) = (term50 A N).
Proof. exact (fun_ext (fun m : nat => @lem7996582 A N m)). Qed.
Lemma lem7996584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996585 {A N : Type'} : (term4 A N) = (term4 A N).
Proof. exact (MK_COMB (@lem7996584) (@lem7996583 A N)). Qed.
Lemma lem7996586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996587 {A N : Type'} : (term22 A N) = (term22 A N).
Proof. exact (MK_COMB (@lem7996586) (@lem7996585 A N)). Qed.
Lemma lem7996588 {A N : Type'} : (term24 A N) = (term24 A N).
Proof. exact (MK_COMB (@lem7996587 A N) (@lem7996577 A N)). Qed.
Lemma lem7996593 {A : Type'} (m : nat) : (term51 A m) = (term51 A m).
Proof. exact (eq_refl (term51 A m)). Qed.
Lemma lem7996594 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (fun_ext (fun m : nat => @lem7996593 A m)). Qed.
Lemma lem7996595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996596 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem7996595) (@lem7996594 A)). Qed.
Lemma lem7996597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996598 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem7996597) (@lem7996596 A)). Qed.
Lemma lem7996599 {A N : Type'} : (term27 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7996598 A) (@lem7996588 A N)). Qed.
Lemma lem7996608 {A N : Type'} (s : type11 A N) (n : nat) : ((@HAS_SIZE (cart (cart A N) N) s n) = (term53 A N s n)) = ((@HAS_SIZE (cart (cart A N) N) s n) = (term53 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart (cart A N) N) s n) = (term53 A N s n))). Qed.
Lemma lem7996609 {A N : Type'} (s : type11 A N) : (term54 A N s) = (term54 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7996608 A N s n)). Qed.
Lemma lem7996610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996611 {A N : Type'} (s : type11 A N) : (term55 A N s) = (term55 A N s).
Proof. exact (MK_COMB (@lem7996610) (@lem7996609 A N s)). Qed.
Lemma lem7996612 {A N : Type'} : (term56 A N) = (term56 A N).
Proof. exact (fun_ext (fun s : type11 A N => @lem7996611 A N s)). Qed.
Lemma lem7996613 {A N : Type'} : (@all ((cart (cart A N) N) -> Prop)) = (@all ((cart (cart A N) N) -> Prop)).
Proof. exact (eq_refl (@all ((cart (cart A N) N) -> Prop))). Qed.
Lemma lem7996614 {A N : Type'} : (term9 A N) = (term9 A N).
Proof. exact (MK_COMB (@lem7996613 A N) (@lem7996612 A N)). Qed.
Lemma lem7996615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996616 {A N : Type'} : (term28 A N) = (term28 A N).
Proof. exact (MK_COMB (@lem7996615) (@lem7996614 A N)). Qed.
Lemma lem7996617 {A N : Type'} : (term30 A N) = (term30 A N).
Proof. exact (MK_COMB (@lem7996616 A N) (@lem7996599 A N)). Qed.
Lemma lem7996626 {A N : Type'} (s : type12 A N) (n : nat) : ((@HAS_SIZE (cart A (cart A N)) s n) = (term57 A N s n)) = ((@HAS_SIZE (cart A (cart A N)) s n) = (term57 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A (cart A N)) s n) = (term57 A N s n))). Qed.
Lemma lem7996627 {A N : Type'} (s : type12 A N) : (term58 A N s) = (term58 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7996626 A N s n)). Qed.
Lemma lem7996628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996629 {A N : Type'} (s : type12 A N) : (term59 A N s) = (term59 A N s).
Proof. exact (MK_COMB (@lem7996628) (@lem7996627 A N s)). Qed.
Lemma lem7996630 {A N : Type'} : (term60 A N) = (term60 A N).
Proof. exact (fun_ext (fun s : type12 A N => @lem7996629 A N s)). Qed.
Lemma lem7996631 {A N : Type'} : (@all ((cart A (cart A N)) -> Prop)) = (@all ((cart A (cart A N)) -> Prop)).
Proof. exact (eq_refl (@all ((cart A (cart A N)) -> Prop))). Qed.
Lemma lem7996632 {A N : Type'} : (term11 A N) = (term11 A N).
Proof. exact (MK_COMB (@lem7996631 A N) (@lem7996630 A N)). Qed.
Lemma lem7996633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996634 {A N : Type'} : (term31 A N) = (term31 A N).
Proof. exact (MK_COMB (@lem7996633) (@lem7996632 A N)). Qed.
Lemma lem7996635 {A N : Type'} : (term33 A N) = (term33 A N).
Proof. exact (MK_COMB (@lem7996634 A N) (@lem7996617 A N)). Qed.
Lemma lem7996644 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term61 A N s n)) = ((@HAS_SIZE (cart A N) s n) = (term61 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A N) s n) = (term61 A N s n))). Qed.
Lemma lem7996645 {A N : Type'} (s : type24 A N) : (term62 A N s) = (term62 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7996644 A N s n)). Qed.
Lemma lem7996646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996647 {A N : Type'} (s : type24 A N) : (term63 A N s) = (term63 A N s).
Proof. exact (MK_COMB (@lem7996646) (@lem7996645 A N s)). Qed.
Lemma lem7996648 {A N : Type'} : (term64 A N) = (term64 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7996647 A N s)). Qed.
Lemma lem7996649 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7996650 {A N : Type'} : (term8 A N) = (term8 A N).
Proof. exact (MK_COMB (@lem7996649 A N) (@lem7996648 A N)). Qed.
Lemma lem7996651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996652 {A N : Type'} : (term34 A N) = (term34 A N).
Proof. exact (MK_COMB (@lem7996651) (@lem7996650 A N)). Qed.
Lemma lem7996653 {A N : Type'} : (term36 A N) = (term36 A N).
Proof. exact (MK_COMB (@lem7996652 A N) (@lem7996635 A N)). Qed.
Lemma lem7996662 {A : Type'} (s : type17 A) (n : nat) : ((@HAS_SIZE (cart A A) s n) = (term65 A s n)) = ((@HAS_SIZE (cart A A) s n) = (term65 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A A) s n) = (term65 A s n))). Qed.
Lemma lem7996663 {A : Type'} (s : type17 A) : (term66 A s) = (term66 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996662 A s n)). Qed.
Lemma lem7996664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996665 {A : Type'} (s : type17 A) : (term67 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem7996664) (@lem7996663 A s)). Qed.
Lemma lem7996666 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (fun_ext (fun s : type17 A => @lem7996665 A s)). Qed.
Lemma lem7996667 {A : Type'} : (@all ((cart A A) -> Prop)) = (@all ((cart A A) -> Prop)).
Proof. exact (eq_refl (@all ((cart A A) -> Prop))). Qed.
Lemma lem7996668 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7996667 A) (@lem7996666 A)). Qed.
Lemma lem7996669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996670 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (MK_COMB (@lem7996669) (@lem7996668 A)). Qed.
Lemma lem7996671 {A N : Type'} : (term39 A N) = (term39 A N).
Proof. exact (MK_COMB (@lem7996670 A) (@lem7996653 A N)). Qed.
Lemma lem7996680 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = ((@HAS_SIZE A s n) = (term69 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term69 A s n))). Qed.
Lemma lem7996681 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996680 A s n)). Qed.
Lemma lem7996682 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996683 {A : Type'} (s : A -> Prop) : (term71 A s) = (term71 A s).
Proof. exact (MK_COMB (@lem7996682) (@lem7996681 A s)). Qed.
Lemma lem7996684 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7996683 A s)). Qed.
Lemma lem7996685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7996686 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7996685 A) (@lem7996684 A)). Qed.
Lemma lem7996687 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996688 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem7996687) (@lem7996686 A)). Qed.
Lemma lem7996689 {A N : Type'} : (term42 A N) = (term42 A N).
Proof. exact (MK_COMB (@lem7996688 A) (@lem7996671 A N)). Qed.
Lemma lem7996698 {A N : Type'} : (term43 A N) = (term43 A N).
Proof. exact (eq_refl (term43 A N)). Qed.
Lemma lem7996699 {A N : Type'} : (term44 A N) = (term44 A N).
Proof. exact (MK_COMB (@lem7996698 A N) (@lem7996689 A N)). Qed.
Lemma lem7996824 {A N : Type'} : (term13 A N) = (term44 A N).
Proof. exact (TRANS (@lem7996556 A N) (@lem7996699 A N)). Qed.
Lemma lem7996825 {A N : Type'} : (term44 A N) = (term13 A N).
Proof. exact (SYM (@lem7996824 A N)). Qed.
Lemma lem7996826 {A N : Type'} (h1 : term3 A N) : term3 A N.
Proof. exact (h1). Qed.
Lemma lem7996827 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7996829 {A N : Type'} (h1 : term8 A N) : term8 A N.
Proof. exact (h1). Qed.
Lemma lem7996833 {A N : Type'} (h1 : term4 A N) : term4 A N.
Proof. exact (h1). Qed.
Lemma lem7996846 {A N : Type'} : (term3 A N) = (term73 A N).
Proof. exact (@lem17362 (@FINITE A (@UNIV A)) (@FINITE (cart A N) (@UNIV (cart A N)))). Qed.
Lemma lem7996858 {A : Type'} (s : A -> Prop) (n : nat) : (term74 A s n) = (term75 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7996864 {A : Type'} (s : A -> Prop) (n : nat) : (term76 A s n) = (term76 A s n).
Proof. exact (eq_refl (term76 A s n)). Qed.
Lemma lem7996866 {A : Type'} (s : A -> Prop) (n : nat) : (term77 A s n) = (term77 A s n).
Proof. exact (eq_refl (term77 A s n)). Qed.
Lemma lem7996867 {A : Type'} (s : A -> Prop) (n : nat) : (term78 A s n) = (term79 A s n).
Proof. exact (MK_COMB (@lem7996866 A s n) (@lem7996858 A s n)). Qed.
Lemma lem7996868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7996869 {A : Type'} (s : A -> Prop) (n : nat) : (term80 A s n) = (term81 A s n).
Proof. exact (MK_COMB (@lem7996868) (@lem7996867 A s n)). Qed.
Lemma lem7996870 {A : Type'} (s : A -> Prop) (n : nat) : (term82 A s n) = (term83 A s n).
Proof. exact (MK_COMB (@lem7996869 A s n) (@lem7996864 A s n)). Qed.
Lemma lem7996871 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = (term82 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term69 A s n)). Qed.
Lemma lem7996872 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term69 A s n)) = (term83 A s n).
Proof. exact (TRANS (@lem7996871 A s n) (@lem7996870 A s n)). Qed.
Lemma lem7996873 {A : Type'} (s : A -> Prop) : (term70 A s) = (term84 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996872 A s n)). Qed.
Lemma lem7996874 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996875 {A : Type'} (s : A -> Prop) : (term71 A s) = (term85 A s).
Proof. exact (MK_COMB (@lem7996874) (@lem7996873 A s)). Qed.
Lemma lem7996876 {A : Type'} : (term72 A) = (term86 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7996875 A s)). Qed.
Lemma lem7996877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7996878 {A : Type'} : (term10 A) = (term87 A).
Proof. exact (MK_COMB (@lem7996877 A) (@lem7996876 A)). Qed.
Lemma lem7996884 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7996885 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem7996884 nat P Q). Qed.
Lemma lem7996886 {A : Type'} (s : A -> Prop) : (term92 A s) = (term93 A s).
Proof. exact (@lem7996885 (term94 A s) (term95 A s)). Qed.
Lemma lem7996887 {A : Type'} (s : A -> Prop) (n : nat) : (term96 A s n) = (term79 A s n).
Proof. exact (eq_refl (term96 A s n)). Qed.
Lemma lem7996888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7996889 {A : Type'} (s : A -> Prop) (n : nat) : (term97 A s n) = (term81 A s n).
Proof. exact (MK_COMB (@lem7996888) (@lem7996887 A s n)). Qed.
Lemma lem7996890 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term76 A s n).
Proof. exact (eq_refl (term98 A s n)). Qed.
Lemma lem7996891 {A : Type'} (s : A -> Prop) (n : nat) : (term99 A s n) = (term83 A s n).
Proof. exact (MK_COMB (@lem7996889 A s n) (@lem7996890 A s n)). Qed.
Lemma lem7996892 {A : Type'} (s : A -> Prop) : (term100 A s) = (term84 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996891 A s n)). Qed.
Lemma lem7996893 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996894 {A : Type'} (s : A -> Prop) : (term92 A s) = (term85 A s).
Proof. exact (MK_COMB (@lem7996893) (@lem7996892 A s)). Qed.
Lemma lem7996895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7996896 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem7996895) (@lem7996894 A s)). Qed.
Lemma lem7996897 {A : Type'} (s : A -> Prop) (n : nat) : (term96 A s n) = (term79 A s n).
Proof. exact (eq_refl (term96 A s n)). Qed.
Lemma lem7996898 {A : Type'} (s : A -> Prop) : (term103 A s) = (term94 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996897 A s n)). Qed.
Lemma lem7996899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996900 {A : Type'} (s : A -> Prop) : (term104 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem7996899) (@lem7996898 A s)). Qed.
Lemma lem7996901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7996902 {A : Type'} (s : A -> Prop) : (term106 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem7996901) (@lem7996900 A s)). Qed.
Lemma lem7996903 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term76 A s n).
Proof. exact (eq_refl (term98 A s n)). Qed.
Lemma lem7996904 {A : Type'} (s : A -> Prop) : (term108 A s) = (term95 A s).
Proof. exact (fun_ext (fun n : nat => @lem7996903 A s n)). Qed.
Lemma lem7996905 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7996906 {A : Type'} (s : A -> Prop) : (term109 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem7996905) (@lem7996904 A s)). Qed.
Lemma lem7996907 {A : Type'} (s : A -> Prop) : (term93 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem7996902 A s) (@lem7996906 A s)). Qed.
Lemma lem7996908 {A : Type'} (s : A -> Prop) : ((term92 A s) = (term93 A s)) = ((term85 A s) = (term111 A s)).
Proof. exact (MK_COMB (@lem7996896 A s) (@lem7996907 A s)). Qed.
Lemma lem7996909 {A : Type'} (s : A -> Prop) : (term85 A s) = (term111 A s).
Proof. exact (EQ_MP (@lem7996908 A s) (@lem7996886 A s)). Qed.
Lemma lem7997006 {A : Type'} : (term86 A) = (term112 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7996909 A s)). Qed.
Lemma lem7997007 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7997008 {A : Type'} : (term87 A) = (term113 A).
Proof. exact (MK_COMB (@lem7997007 A) (@lem7997006 A)). Qed.
Lemma lem7997010 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7997011 {A : Type'} (P : type686 A) (Q : type686 A) : (term114 A P Q) = (term115 A P Q).
Proof. exact (@lem7997010 (A -> Prop) P Q). Qed.
Lemma lem7997012 {A : Type'} : (term116 A) = (term117 A).
Proof. exact (@lem7997011 A (term118 A) (term119 A)). Qed.
Lemma lem7997013 {A : Type'} (s : A -> Prop) : (term120 A s) = (term105 A s).
Proof. exact (eq_refl (term120 A s)). Qed.
Lemma lem7997014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997015 {A : Type'} (s : A -> Prop) : (term121 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem7997014) (@lem7997013 A s)). Qed.
Lemma lem7997016 {A : Type'} (s : A -> Prop) : (term122 A s) = (term110 A s).
Proof. exact (eq_refl (term122 A s)). Qed.
Lemma lem7997017 {A : Type'} (s : A -> Prop) : (term123 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem7997015 A s) (@lem7997016 A s)). Qed.
Lemma lem7997018 {A : Type'} : (term124 A) = (term112 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7997017 A s)). Qed.
Lemma lem7997019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7997020 {A : Type'} : (term116 A) = (term113 A).
Proof. exact (MK_COMB (@lem7997019 A) (@lem7997018 A)). Qed.
Lemma lem7997021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7997022 {A : Type'} : (term125 A) = (term126 A).
Proof. exact (MK_COMB (@lem7997021) (@lem7997020 A)). Qed.
Lemma lem7997023 {A : Type'} (s : A -> Prop) : (term120 A s) = (term105 A s).
Proof. exact (eq_refl (term120 A s)). Qed.
Lemma lem7997024 {A : Type'} : (term127 A) = (term118 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7997023 A s)). Qed.
Lemma lem7997025 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7997026 {A : Type'} : (term128 A) = (term129 A).
Proof. exact (MK_COMB (@lem7997025 A) (@lem7997024 A)). Qed.
Lemma lem7997027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997028 {A : Type'} : (term130 A) = (term131 A).
Proof. exact (MK_COMB (@lem7997027) (@lem7997026 A)). Qed.
Lemma lem7997029 {A : Type'} (s : A -> Prop) : (term122 A s) = (term110 A s).
Proof. exact (eq_refl (term122 A s)). Qed.
Lemma lem7997030 {A : Type'} : (term132 A) = (term119 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7997029 A s)). Qed.
Lemma lem7997031 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7997032 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (MK_COMB (@lem7997031 A) (@lem7997030 A)). Qed.
Lemma lem7997033 {A : Type'} : (term117 A) = (term135 A).
Proof. exact (MK_COMB (@lem7997028 A) (@lem7997032 A)). Qed.
Lemma lem7997034 {A : Type'} : ((term116 A) = (term117 A)) = ((term113 A) = (term135 A)).
Proof. exact (MK_COMB (@lem7997022 A) (@lem7997033 A)). Qed.
Lemma lem7997035 {A : Type'} : (term113 A) = (term135 A).
Proof. exact (EQ_MP (@lem7997034 A) (@lem7997012 A)). Qed.
Lemma lem7997142 {A : Type'} : (term87 A) = (term135 A).
Proof. exact (TRANS (@lem7997008 A) (@lem7997035 A)). Qed.
Lemma lem7997143 {A : Type'} : (term10 A) = (term135 A).
Proof. exact (TRANS (@lem7996878 A) (@lem7997142 A)). Qed.
Lemma lem7997144 {A : Type'} (h1 : term10 A) : term135 A.
Proof. exact (EQ_MP (@lem7997143 A) (@lem7996827 A h1)). Qed.
Lemma lem7997452 {A N : Type'} (s : type24 A N) (n : nat) : (term136 A N s n) = (term137 A N s n).
Proof. exact (@lem17045 (@FINITE (cart A N) s) ((@CARD (cart A N) s) = n)). Qed.
Lemma lem7997458 {A N : Type'} (s : type24 A N) (n : nat) : (term138 A N s n) = (term138 A N s n).
Proof. exact (eq_refl (term138 A N s n)). Qed.
Lemma lem7997460 {A N : Type'} (s : type24 A N) (n : nat) : (term139 A N s n) = (term139 A N s n).
Proof. exact (eq_refl (term139 A N s n)). Qed.
Lemma lem7997461 {A N : Type'} (s : type24 A N) (n : nat) : (term140 A N s n) = (term141 A N s n).
Proof. exact (MK_COMB (@lem7997460 A N s n) (@lem7997452 A N s n)). Qed.
Lemma lem7997462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997463 {A N : Type'} (s : type24 A N) (n : nat) : (term142 A N s n) = (term143 A N s n).
Proof. exact (MK_COMB (@lem7997462) (@lem7997461 A N s n)). Qed.
Lemma lem7997464 {A N : Type'} (s : type24 A N) (n : nat) : (term144 A N s n) = (term145 A N s n).
Proof. exact (MK_COMB (@lem7997463 A N s n) (@lem7997458 A N s n)). Qed.
Lemma lem7997465 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term61 A N s n)) = (term144 A N s n).
Proof. exact (@lem17784 (@HAS_SIZE (cart A N) s n) (term61 A N s n)). Qed.
Lemma lem7997466 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term61 A N s n)) = (term145 A N s n).
Proof. exact (TRANS (@lem7997465 A N s n) (@lem7997464 A N s n)). Qed.
Lemma lem7997467 {A N : Type'} (s : type24 A N) : (term62 A N s) = (term146 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7997466 A N s n)). Qed.
Lemma lem7997468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7997469 {A N : Type'} (s : type24 A N) : (term63 A N s) = (term147 A N s).
Proof. exact (MK_COMB (@lem7997468) (@lem7997467 A N s)). Qed.
Lemma lem7997470 {A N : Type'} : (term64 A N) = (term148 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7997469 A N s)). Qed.
Lemma lem7997471 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7997472 {A N : Type'} : (term8 A N) = (term149 A N).
Proof. exact (MK_COMB (@lem7997471 A N) (@lem7997470 A N)). Qed.
Lemma lem7997478 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7997479 (P : nat -> Prop) (Q : nat -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem7997478 nat P Q). Qed.
Lemma lem7997480 {A N : Type'} (s : type24 A N) : (term150 A N s) = (term151 A N s).
Proof. exact (@lem7997479 (term152 A N s) (term153 A N s)). Qed.
Lemma lem7997481 {A N : Type'} (s : type24 A N) (n : nat) : (term154 A N s n) = (term141 A N s n).
Proof. exact (eq_refl (term154 A N s n)). Qed.
Lemma lem7997482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997483 {A N : Type'} (s : type24 A N) (n : nat) : (term155 A N s n) = (term143 A N s n).
Proof. exact (MK_COMB (@lem7997482) (@lem7997481 A N s n)). Qed.
Lemma lem7997484 {A N : Type'} (s : type24 A N) (n : nat) : (term156 A N s n) = (term138 A N s n).
Proof. exact (eq_refl (term156 A N s n)). Qed.
Lemma lem7997485 {A N : Type'} (s : type24 A N) (n : nat) : (term157 A N s n) = (term145 A N s n).
Proof. exact (MK_COMB (@lem7997483 A N s n) (@lem7997484 A N s n)). Qed.
Lemma lem7997486 {A N : Type'} (s : type24 A N) : (term158 A N s) = (term146 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7997485 A N s n)). Qed.
Lemma lem7997487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7997488 {A N : Type'} (s : type24 A N) : (term150 A N s) = (term147 A N s).
Proof. exact (MK_COMB (@lem7997487) (@lem7997486 A N s)). Qed.
Lemma lem7997489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7997490 {A N : Type'} (s : type24 A N) : (term159 A N s) = (term160 A N s).
Proof. exact (MK_COMB (@lem7997489) (@lem7997488 A N s)). Qed.
Lemma lem7997491 {A N : Type'} (s : type24 A N) (n : nat) : (term154 A N s n) = (term141 A N s n).
Proof. exact (eq_refl (term154 A N s n)). Qed.
Lemma lem7997492 {A N : Type'} (s : type24 A N) : (term161 A N s) = (term152 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7997491 A N s n)). Qed.
Lemma lem7997493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7997494 {A N : Type'} (s : type24 A N) : (term162 A N s) = (term163 A N s).
Proof. exact (MK_COMB (@lem7997493) (@lem7997492 A N s)). Qed.
Lemma lem7997495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997496 {A N : Type'} (s : type24 A N) : (term164 A N s) = (term165 A N s).
Proof. exact (MK_COMB (@lem7997495) (@lem7997494 A N s)). Qed.
Lemma lem7997497 {A N : Type'} (s : type24 A N) (n : nat) : (term156 A N s n) = (term138 A N s n).
Proof. exact (eq_refl (term156 A N s n)). Qed.
Lemma lem7997498 {A N : Type'} (s : type24 A N) : (term166 A N s) = (term153 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7997497 A N s n)). Qed.
Lemma lem7997499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7997500 {A N : Type'} (s : type24 A N) : (term167 A N s) = (term168 A N s).
Proof. exact (MK_COMB (@lem7997499) (@lem7997498 A N s)). Qed.
Lemma lem7997501 {A N : Type'} (s : type24 A N) : (term151 A N s) = (term169 A N s).
Proof. exact (MK_COMB (@lem7997496 A N s) (@lem7997500 A N s)). Qed.
Lemma lem7997502 {A N : Type'} (s : type24 A N) : ((term150 A N s) = (term151 A N s)) = ((term147 A N s) = (term169 A N s)).
Proof. exact (MK_COMB (@lem7997490 A N s) (@lem7997501 A N s)). Qed.
Lemma lem7997503 {A N : Type'} (s : type24 A N) : (term147 A N s) = (term169 A N s).
Proof. exact (EQ_MP (@lem7997502 A N s) (@lem7997480 A N s)). Qed.
Lemma lem7997600 {A N : Type'} : (term148 A N) = (term170 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7997503 A N s)). Qed.
Lemma lem7997601 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7997602 {A N : Type'} : (term149 A N) = (term171 A N).
Proof. exact (MK_COMB (@lem7997601 A N) (@lem7997600 A N)). Qed.
Lemma lem7997604 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7997605 {A N : Type'} (P : type56 A N) (Q : type56 A N) : (term172 A N P Q) = (term173 A N P Q).
Proof. exact (@lem7997604 (type24 A N) P Q). Qed.
Lemma lem7997606 {A N : Type'} : (term174 A N) = (term175 A N).
Proof. exact (@lem7997605 A N (term176 A N) (term177 A N)). Qed.
Lemma lem7997607 {A N : Type'} (s : type24 A N) : (term178 A N s) = (term163 A N s).
Proof. exact (eq_refl (term178 A N s)). Qed.
Lemma lem7997608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997609 {A N : Type'} (s : type24 A N) : (term179 A N s) = (term165 A N s).
Proof. exact (MK_COMB (@lem7997608) (@lem7997607 A N s)). Qed.
Lemma lem7997610 {A N : Type'} (s : type24 A N) : (term180 A N s) = (term168 A N s).
Proof. exact (eq_refl (term180 A N s)). Qed.
Lemma lem7997611 {A N : Type'} (s : type24 A N) : (term181 A N s) = (term169 A N s).
Proof. exact (MK_COMB (@lem7997609 A N s) (@lem7997610 A N s)). Qed.
Lemma lem7997612 {A N : Type'} : (term182 A N) = (term170 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7997611 A N s)). Qed.
Lemma lem7997613 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7997614 {A N : Type'} : (term174 A N) = (term171 A N).
Proof. exact (MK_COMB (@lem7997613 A N) (@lem7997612 A N)). Qed.
Lemma lem7997615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7997616 {A N : Type'} : (term183 A N) = (term184 A N).
Proof. exact (MK_COMB (@lem7997615) (@lem7997614 A N)). Qed.
Lemma lem7997617 {A N : Type'} (s : type24 A N) : (term178 A N s) = (term163 A N s).
Proof. exact (eq_refl (term178 A N s)). Qed.
Lemma lem7997618 {A N : Type'} : (term185 A N) = (term176 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7997617 A N s)). Qed.
Lemma lem7997619 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7997620 {A N : Type'} : (term186 A N) = (term187 A N).
Proof. exact (MK_COMB (@lem7997619 A N) (@lem7997618 A N)). Qed.
Lemma lem7997621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7997622 {A N : Type'} : (term188 A N) = (term189 A N).
Proof. exact (MK_COMB (@lem7997621) (@lem7997620 A N)). Qed.
Lemma lem7997623 {A N : Type'} (s : type24 A N) : (term180 A N s) = (term168 A N s).
Proof. exact (eq_refl (term180 A N s)). Qed.
Lemma lem7997624 {A N : Type'} : (term190 A N) = (term177 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7997623 A N s)). Qed.
Lemma lem7997625 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7997626 {A N : Type'} : (term191 A N) = (term192 A N).
Proof. exact (MK_COMB (@lem7997625 A N) (@lem7997624 A N)). Qed.
Lemma lem7997627 {A N : Type'} : (term175 A N) = (term193 A N).
Proof. exact (MK_COMB (@lem7997622 A N) (@lem7997626 A N)). Qed.
Lemma lem7997628 {A N : Type'} : ((term174 A N) = (term175 A N)) = ((term171 A N) = (term193 A N)).
Proof. exact (MK_COMB (@lem7997616 A N) (@lem7997627 A N)). Qed.
Lemma lem7997629 {A N : Type'} : (term171 A N) = (term193 A N).
Proof. exact (EQ_MP (@lem7997628 A N) (@lem7997606 A N)). Qed.
Lemma lem7997736 {A N : Type'} : (term149 A N) = (term193 A N).
Proof. exact (TRANS (@lem7997602 A N) (@lem7997629 A N)). Qed.
Lemma lem7997737 {A N : Type'} : (term8 A N) = (term193 A N).
Proof. exact (TRANS (@lem7997472 A N) (@lem7997736 A N)). Qed.
Lemma lem7997738 {A N : Type'} (h1 : term8 A N) : term193 A N.
Proof. exact (EQ_MP (@lem7997737 A N) (@lem7996829 A N h1)). Qed.
Lemma lem7998402 {A N : Type'} (m : nat) : (term49 A N m) = (term194 A N m).
Proof. exact (@lem17265 (@HAS_SIZE A (@UNIV A) m) (term195 A N m)). Qed.
Lemma lem7998403 {A N : Type'} : (term50 A N) = (term196 A N).
Proof. exact (fun_ext (fun m : nat => @lem7998402 A N m)). Qed.
Lemma lem7998404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998457 {A N : Type'} : (term4 A N) = (term197 A N).
Proof. exact (MK_COMB (@lem7998404) (@lem7998403 A N)). Qed.
Lemma lem7998458 {A N : Type'} (h1 : term4 A N) : term197 A N.
Proof. exact (EQ_MP (@lem7998457 A N) (@lem7996833 A N h1)). Qed.
Lemma lem7998596 {A N : Type'} (h1 : term3 A N) : term73 A N.
Proof. exact (EQ_MP (@lem7996846 A N) (@lem7996826 A N h1)). Qed.
Lemma lem7998619 {A : Type'} (s : A -> Prop) (n : nat) : (term76 A s n) = (term76 A s n).
Proof. exact (eq_refl (term76 A s n)). Qed.
Lemma lem7998620 {A : Type'} (s : A -> Prop) : (term95 A s) = (term95 A s).
Proof. exact (fun_ext (fun n : nat => @lem7998619 A s n)). Qed.
Lemma lem7998621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998622 {A : Type'} (s : A -> Prop) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem7998621) (@lem7998620 A s)). Qed.
Lemma lem7998623 {A : Type'} : (term119 A) = (term119 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7998622 A s)). Qed.
Lemma lem7998624 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7998625 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem7998624 A) (@lem7998623 A)). Qed.
Lemma lem7998650 {A : Type'} (s : A -> Prop) (n : nat) : (term79 A s n) = (term79 A s n).
Proof. exact (eq_refl (term79 A s n)). Qed.
Lemma lem7998651 {A : Type'} (s : A -> Prop) : (term94 A s) = (term94 A s).
Proof. exact (fun_ext (fun n : nat => @lem7998650 A s n)). Qed.
Lemma lem7998652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998653 {A : Type'} (s : A -> Prop) : (term105 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem7998652) (@lem7998651 A s)). Qed.
Lemma lem7998654 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7998653 A s)). Qed.
Lemma lem7998655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7998656 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (MK_COMB (@lem7998655 A) (@lem7998654 A)). Qed.
Lemma lem7998657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7998658 {A : Type'} : (term131 A) = (term131 A).
Proof. exact (MK_COMB (@lem7998657) (@lem7998656 A)). Qed.
Lemma lem7998659 {A : Type'} : (term135 A) = (term135 A).
Proof. exact (MK_COMB (@lem7998658 A) (@lem7998625 A)). Qed.
Lemma lem7998660 {A : Type'} (h1 : term10 A) : term135 A.
Proof. exact (EQ_MP (@lem7998659 A) (@lem7997144 A h1)). Qed.
Lemma lem7998747 {A N : Type'} (s : type24 A N) (n : nat) : (term138 A N s n) = (term138 A N s n).
Proof. exact (eq_refl (term138 A N s n)). Qed.
Lemma lem7998748 {A N : Type'} (s : type24 A N) : (term153 A N s) = (term153 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7998747 A N s n)). Qed.
Lemma lem7998749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998750 {A N : Type'} (s : type24 A N) : (term168 A N s) = (term168 A N s).
Proof. exact (MK_COMB (@lem7998749) (@lem7998748 A N s)). Qed.
Lemma lem7998751 {A N : Type'} : (term177 A N) = (term177 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7998750 A N s)). Qed.
Lemma lem7998752 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7998753 {A N : Type'} : (term192 A N) = (term192 A N).
Proof. exact (MK_COMB (@lem7998752 A N) (@lem7998751 A N)). Qed.
Lemma lem7998778 {A N : Type'} (s : type24 A N) (n : nat) : (term141 A N s n) = (term141 A N s n).
Proof. exact (eq_refl (term141 A N s n)). Qed.
Lemma lem7998779 {A N : Type'} (s : type24 A N) : (term152 A N s) = (term152 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7998778 A N s n)). Qed.
Lemma lem7998780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998781 {A N : Type'} (s : type24 A N) : (term163 A N s) = (term163 A N s).
Proof. exact (MK_COMB (@lem7998780) (@lem7998779 A N s)). Qed.
Lemma lem7998782 {A N : Type'} : (term176 A N) = (term176 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7998781 A N s)). Qed.
Lemma lem7998783 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7998784 {A N : Type'} : (term187 A N) = (term187 A N).
Proof. exact (MK_COMB (@lem7998783 A N) (@lem7998782 A N)). Qed.
Lemma lem7998785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7998786 {A N : Type'} : (term189 A N) = (term189 A N).
Proof. exact (MK_COMB (@lem7998785) (@lem7998784 A N)). Qed.
Lemma lem7998787 {A N : Type'} : (term193 A N) = (term193 A N).
Proof. exact (MK_COMB (@lem7998786 A N) (@lem7998753 A N)). Qed.
Lemma lem7998788 {A N : Type'} (h1 : term8 A N) : term193 A N.
Proof. exact (EQ_MP (@lem7998787 A N) (@lem7997738 A N h1)). Qed.
Lemma lem7998962 {A N : Type'} (m : nat) : (term194 A N m) = (term194 A N m).
Proof. exact (eq_refl (term194 A N m)). Qed.
Lemma lem7998963 {A N : Type'} : (term196 A N) = (term196 A N).
Proof. exact (fun_ext (fun m : nat => @lem7998962 A N m)). Qed.
Lemma lem7998964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7998965 {A N : Type'} : (term197 A N) = (term197 A N).
Proof. exact (MK_COMB (@lem7998964) (@lem7998963 A N)). Qed.
Lemma lem7998966 {A N : Type'} (h1 : term4 A N) : term197 A N.
Proof. exact (EQ_MP (@lem7998965 A N) (@lem7998458 A N h1)). Qed.
Lemma lem7999021 {A N : Type'} (h1 : term8 A N) : term192 A N.
Proof. exact (proj2 (@lem7998788 A N h1)). Qed.
Lemma lem7999026 {A : Type'} (h1 : term10 A) : term129 A.
Proof. exact (proj1 (@lem7998660 A h1)). Qed.
Lemma lem7999049 {A N : Type'} (m : nat) : (term194 A N m) = (term194 A N m).
Proof. exact (eq_refl (term194 A N m)). Qed.
Lemma lem7999050 {A N : Type'} : (term196 A N) = (term196 A N).
Proof. exact (fun_ext (fun m : nat => @lem7999049 A N m)). Qed.
Lemma lem7999051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7999053 {A N : Type'} : (term197 A N) = (term197 A N).
Proof. exact (MK_COMB (@lem7999051) (@lem7999050 A N)). Qed.
Lemma lem7999054 {A N : Type'} (h1 : term4 A N) : term197 A N.
Proof. exact (EQ_MP (@lem7999053 A N) (@lem7998966 A N h1)). Qed.
Lemma lem7999216 {A N : Type'} (s : type24 A N) (n : nat) : (term138 A N s n) = (term198 A N s n).
Proof. exact (@lem19490 (@FINITE (cart A N) s) (term199 A N s n) ((@CARD (cart A N) s) = n)). Qed.
Lemma lem7999217 {A N : Type'} (s : type24 A N) : (term153 A N s) = (term200 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7999216 A N s n)). Qed.
Lemma lem7999218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7999219 {A N : Type'} (s : type24 A N) : (term168 A N s) = (term201 A N s).
Proof. exact (MK_COMB (@lem7999218) (@lem7999217 A N s)). Qed.
Lemma lem7999220 {A N : Type'} : (term177 A N) = (term202 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7999219 A N s)). Qed.
Lemma lem7999221 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7999223 {A N : Type'} : (term192 A N) = (term203 A N).
Proof. exact (MK_COMB (@lem7999221 A N) (@lem7999220 A N)). Qed.
Lemma lem7999224 {A N : Type'} (h1 : term8 A N) : term203 A N.
Proof. exact (EQ_MP (@lem7999223 A N) (@lem7999021 A N h1)). Qed.
Lemma lem7999286 {A : Type'} (s : A -> Prop) (n : nat) : (term79 A s n) = (term79 A s n).
Proof. exact (eq_refl (term79 A s n)). Qed.
Lemma lem7999287 {A : Type'} (s : A -> Prop) : (term94 A s) = (term94 A s).
Proof. exact (fun_ext (fun n : nat => @lem7999286 A s n)). Qed.
Lemma lem7999288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7999289 {A : Type'} (s : A -> Prop) : (term105 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem7999288) (@lem7999287 A s)). Qed.
Lemma lem7999290 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7999289 A s)). Qed.
Lemma lem7999291 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7999293 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (MK_COMB (@lem7999291 A) (@lem7999290 A)). Qed.
Lemma lem7999294 {A : Type'} (h1 : term10 A) : term129 A.
Proof. exact (EQ_MP (@lem7999293 A) (@lem7999026 A h1)). Qed.
Lemma lem7999332 {A N : Type'} (_105519 : nat) (h1 : term4 A N) : term204 A N _105519.
Proof. exact (@lem7999054 A N h1 _105519). Qed.
Lemma lem7999333 {A N : Type'} (_105519 : nat) : (term204 A N _105519) = (term194 A N _105519).
Proof. exact (eq_refl (term204 A N _105519)). Qed.
Lemma lem7999371 {A N : Type'} (_105532 : type24 A N) (h1 : term8 A N) : term205 A N _105532.
Proof. exact (@lem7999224 A N h1 _105532). Qed.
Lemma lem7999372 {A N : Type'} (_105532 : type24 A N) : (term205 A N _105532) = (term201 A N _105532).
Proof. exact (eq_refl (term205 A N _105532)). Qed.
Lemma lem7999373 {A N : Type'} (_105532 : type24 A N) (h1 : term8 A N) : term201 A N _105532.
Proof. exact (EQ_MP (@lem7999372 A N _105532) (@lem7999371 A N _105532 h1)). Qed.
Lemma lem7999374 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) (h1 : term8 A N) : term206 A N _105532 _105533.
Proof. exact (@lem7999373 A N _105532 h1 _105533). Qed.
Lemma lem7999375 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term206 A N _105532 _105533) = (term198 A N _105532 _105533).
Proof. exact (eq_refl (term206 A N _105532 _105533)). Qed.
Lemma lem7999376 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) (h1 : term8 A N) : term198 A N _105532 _105533.
Proof. exact (EQ_MP (@lem7999375 A N _105532 _105533) (@lem7999374 A N _105532 _105533 h1)). Qed.
Lemma lem7999389 {A : Type'} (_105538 : A -> Prop) (h1 : term10 A) : term120 A _105538.
Proof. exact (@lem7999294 A h1 _105538). Qed.
Lemma lem7999390 {A : Type'} (_105538 : A -> Prop) : (term120 A _105538) = (term105 A _105538).
Proof. exact (eq_refl (term120 A _105538)). Qed.
Lemma lem7999391 {A : Type'} (_105538 : A -> Prop) (h1 : term10 A) : term105 A _105538.
Proof. exact (EQ_MP (@lem7999390 A _105538) (@lem7999389 A _105538 h1)). Qed.
Lemma lem7999392 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) (h1 : term10 A) : term96 A _105538 _105539.
Proof. exact (@lem7999391 A _105538 h1 _105539). Qed.
Lemma lem7999393 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term96 A _105538 _105539) = (term79 A _105538 _105539).
Proof. exact (eq_refl (term96 A _105538 _105539)). Qed.
Lemma lem7999422 {A N : Type'} (_105519 : nat) (h1 : term4 A N) : term194 A N _105519.
Proof. exact (EQ_MP (@lem7999333 A N _105519) (@lem7999332 A N _105519 h1)). Qed.
Lemma lem7999484 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) (h1 : term10 A) : term79 A _105538 _105539.
Proof. exact (EQ_MP (@lem7999393 A _105538 _105539) (@lem7999392 A _105538 _105539 h1)). Qed.
Lemma lem7999488 {A N : Type'} (h1 : term3 A N) : term207 A N.
Proof. exact (proj2 (@lem7998596 A N h1)). Qed.
Lemma lem7999518 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) (h1 : term8 A N) : term208 A N _105533 _105532.
Proof. exact (proj1 (@lem7999376 A N _105532 _105533 h1)). Qed.
Lemma lem7999798 {A N : Type'} (h1 : term3 A N) : @FINITE A (@UNIV A).
Proof. exact (proj1 (@lem7998596 A N h1)). Qed.
Lemma lem7999799 {A N : Type'} (h1 : term3 A N) : term209 A.
Proof. exact (fun h0 : term210 A => @lem7999798 A N h1). Qed.
Lemma lem7999801 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999802 {A : Type'} : (term209 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem7999801 (@FINITE A (@UNIV A))). Qed.
Lemma lem7999803 {A N : Type'} (h1 : term3 A N) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem7999802 A) (@lem7999799 A N h1)). Qed.
Lemma lem7999805 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7999806 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (@lem7999805 (@CARD A (@UNIV A))). Qed.
Lemma lem7999807 {A : Type'} : term212 A.
Proof. exact (fun h0 : term213 A => @lem7999806 A). Qed.
Lemma lem7999809 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999810 {A : Type'} : (term212 A) = ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A))).
Proof. exact (@lem7999809 ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7999811 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem7999810 A) (@lem7999807 A)). Qed.
Lemma lem7999813 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7999814 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term79 A _105538 _105539) = (term215 A _105538 _105539).
Proof. exact (@lem7999813 (term75 A _105538 _105539) (@HAS_SIZE A _105538 _105539)). Qed.
Lemma lem7999816 (a : Prop) (b : Prop) : (term216 a b) = (term217 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7999817 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term218 A _105538 _105539) = (term219 A _105538 _105539).
Proof. exact (@lem7999816 (term220 A _105538) (term221 A _105538 _105539)). Qed.
Lemma lem7999819 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7999820 {A : Type'} (_105538 : A -> Prop) : (term223 A _105538) = (@FINITE A _105538).
Proof. exact (@lem7999819 (@FINITE A _105538)). Qed.
Lemma lem7999821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7999822 {A : Type'} (_105538 : A -> Prop) : (term224 A _105538) = (term225 A _105538).
Proof. exact (MK_COMB (@lem7999821) (@lem7999820 A _105538)). Qed.
Lemma lem7999824 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7999825 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term226 A _105538 _105539) = ((@CARD A _105538) = _105539).
Proof. exact (@lem7999824 ((@CARD A _105538) = _105539)). Qed.
Lemma lem7999826 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term219 A _105538 _105539) = (term69 A _105538 _105539).
Proof. exact (MK_COMB (@lem7999822 A _105538) (@lem7999825 A _105538 _105539)). Qed.
Lemma lem7999827 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term218 A _105538 _105539) = (term69 A _105538 _105539).
Proof. exact (TRANS (@lem7999817 A _105538 _105539) (@lem7999826 A _105538 _105539)). Qed.
Lemma lem7999828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7999829 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term227 A _105538 _105539) = (term228 A _105538 _105539).
Proof. exact (MK_COMB (@lem7999828) (@lem7999827 A _105538 _105539)). Qed.
Lemma lem7999830 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (@HAS_SIZE A _105538 _105539) = (@HAS_SIZE A _105538 _105539).
Proof. exact (eq_refl (@HAS_SIZE A _105538 _105539)). Qed.
Lemma lem7999831 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term215 A _105538 _105539) = (term229 A _105538 _105539).
Proof. exact (MK_COMB (@lem7999829 A _105538 _105539) (@lem7999830 A _105538 _105539)). Qed.
Lemma lem7999832 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) : (term79 A _105538 _105539) = (term229 A _105538 _105539).
Proof. exact (TRANS (@lem7999814 A _105538 _105539) (@lem7999831 A _105538 _105539)). Qed.
Lemma lem7999834 {A N : Type'} (h1 : term3 A N) : term230 A.
Proof. exact (conj (@lem7999803 A N h1) (@lem7999811 A)). Qed.
Lemma lem7999836 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) (h1 : term10 A) : term229 A _105538 _105539.
Proof. exact (EQ_MP (@lem7999832 A _105538 _105539) (@lem7999484 A _105538 _105539 h1)). Qed.
Lemma lem7999837 {A : Type'} (_105538 : A -> Prop) (_105539 : nat) (h1 : term10 A) : term229 A _105538 _105539.
Proof. exact (@lem7999836 A _105538 _105539 h1). Qed.
Lemma lem7999838 {A : Type'} (h1 : term10 A) : term231 A.
Proof. exact (@lem7999837 A (@UNIV A) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem7999841 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term232 A.
Proof. exact (@lem7999838 A h1 (@lem7999834 A N h2)). Qed.
Lemma lem7999842 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term233 A.
Proof. exact (fun h0 : term234 A => @lem7999841 A N h1 h2). Qed.
Lemma lem7999844 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999845 {A : Type'} : (term233 A) = (term232 A).
Proof. exact (@lem7999844 (term232 A)). Qed.
Lemma lem7999846 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term232 A.
Proof. exact (EQ_MP (@lem7999845 A) (@lem7999842 A N h1 h2)). Qed.
Lemma lem7999852 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7999853 {A N : Type'} (_105519 : nat) : (term194 A N _105519) = (term235 A N _105519).
Proof. exact (@lem7999852 (term195 A N _105519) (term236 A _105519)). Qed.
Lemma lem7999859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7999860 {A N : Type'} (_105519 : nat) : (term237 A N _105519) = (term238 A N _105519).
Proof. exact (MK_COMB (@lem7999859) (@lem7999853 A N _105519)). Qed.
Lemma lem7999866 {A N : Type'} (_105519 : nat) : (term235 A N _105519) = (term235 A N _105519).
Proof. exact (eq_refl (term235 A N _105519)). Qed.
Lemma lem7999867 {A N : Type'} (_105519 : nat) : ((term194 A N _105519) = (term235 A N _105519)) = ((term235 A N _105519) = (term235 A N _105519)).
Proof. exact (MK_COMB (@lem7999860 A N _105519) (@lem7999866 A N _105519)). Qed.
Lemma lem7999869 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7999870 (x : Prop) : (x = x) = True.
Proof. exact (@lem7999869 Prop x). Qed.
Lemma lem7999871 {A N : Type'} (_105519 : nat) : ((term235 A N _105519) = (term235 A N _105519)) = True.
Proof. exact (@lem7999870 (term235 A N _105519)). Qed.
Lemma lem7999872 {A N : Type'} (_105519 : nat) : ((term194 A N _105519) = (term235 A N _105519)) = True.
Proof. exact (TRANS (@lem7999867 A N _105519) (@lem7999871 A N _105519)). Qed.
Lemma lem7999873 {A N : Type'} (_105519 : nat) : True = ((term194 A N _105519) = (term235 A N _105519)).
Proof. exact (SYM (@lem7999872 A N _105519)). Qed.
Lemma lem7999874 {A N : Type'} (_105519 : nat) : (term194 A N _105519) = (term235 A N _105519).
Proof. exact (EQ_MP (@lem7999873 A N _105519) (@lem0)). Qed.
Lemma lem7999875 {A N : Type'} (_105519 : nat) (h1 : term4 A N) : term235 A N _105519.
Proof. exact (EQ_MP (@lem7999874 A N _105519) (@lem7999422 A N _105519 h1)). Qed.
Lemma lem7999877 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7999878 {A N : Type'} (_105519 : nat) : (term235 A N _105519) = (term239 A N _105519).
Proof. exact (@lem7999877 (term236 A _105519) (term195 A N _105519)). Qed.
Lemma lem7999880 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7999881 {A : Type'} (_105519 : nat) : (term240 A _105519) = (@HAS_SIZE A (@UNIV A) _105519).
Proof. exact (@lem7999880 (@HAS_SIZE A (@UNIV A) _105519)). Qed.
Lemma lem7999882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7999883 {A : Type'} (_105519 : nat) : (term241 A _105519) = (term242 A _105519).
Proof. exact (MK_COMB (@lem7999882) (@lem7999881 A _105519)). Qed.
Lemma lem7999884 {A N : Type'} (_105519 : nat) : (term195 A N _105519) = (term195 A N _105519).
Proof. exact (eq_refl (term195 A N _105519)). Qed.
Lemma lem7999885 {A N : Type'} (_105519 : nat) : (term239 A N _105519) = (term49 A N _105519).
Proof. exact (MK_COMB (@lem7999883 A _105519) (@lem7999884 A N _105519)). Qed.
Lemma lem7999886 {A N : Type'} (_105519 : nat) : (term235 A N _105519) = (term49 A N _105519).
Proof. exact (TRANS (@lem7999878 A N _105519) (@lem7999885 A N _105519)). Qed.
Lemma lem7999889 {A N : Type'} (_105519 : nat) (h1 : term4 A N) : term49 A N _105519.
Proof. exact (EQ_MP (@lem7999886 A N _105519) (@lem7999875 A N _105519 h1)). Qed.
Lemma lem7999890 {A N : Type'} (h1 : term4 A N) : term243 A N.
Proof. exact (@lem7999889 A N (@CARD A (@UNIV A)) h1). Qed.
Lemma lem7999893 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term244 A N.
Proof. exact (@lem7999890 A N h2 (@lem7999846 A N h1 h3)). Qed.
Lemma lem7999894 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term245 A N.
Proof. exact (fun h0 : term246 A N => @lem7999893 A N h1 h2 h3). Qed.
Lemma lem7999896 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999897 {A N : Type'} : (term245 A N) = (term244 A N).
Proof. exact (@lem7999896 (term244 A N)). Qed.
Lemma lem7999898 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term244 A N.
Proof. exact (EQ_MP (@lem7999897 A N) (@lem7999894 A N h1 h2 h3)). Qed.
Lemma lem7999904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7999905 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term208 A N _105533 _105532) = (term247 A N _105532 _105533).
Proof. exact (@lem7999904 (@FINITE (cart A N) _105532) (term199 A N _105532 _105533)). Qed.
Lemma lem7999911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7999912 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term248 A N _105533 _105532) = (term249 A N _105532 _105533).
Proof. exact (MK_COMB (@lem7999911) (@lem7999905 A N _105532 _105533)). Qed.
Lemma lem7999918 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term247 A N _105532 _105533) = (term247 A N _105532 _105533).
Proof. exact (eq_refl (term247 A N _105532 _105533)). Qed.
Lemma lem7999919 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : ((term208 A N _105533 _105532) = (term247 A N _105532 _105533)) = ((term247 A N _105532 _105533) = (term247 A N _105532 _105533)).
Proof. exact (MK_COMB (@lem7999912 A N _105532 _105533) (@lem7999918 A N _105532 _105533)). Qed.
Lemma lem7999921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7999922 (x : Prop) : (x = x) = True.
Proof. exact (@lem7999921 Prop x). Qed.
Lemma lem7999923 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : ((term247 A N _105532 _105533) = (term247 A N _105532 _105533)) = True.
Proof. exact (@lem7999922 (term247 A N _105532 _105533)). Qed.
Lemma lem7999924 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : ((term208 A N _105533 _105532) = (term247 A N _105532 _105533)) = True.
Proof. exact (TRANS (@lem7999919 A N _105532 _105533) (@lem7999923 A N _105532 _105533)). Qed.
Lemma lem7999925 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : True = ((term208 A N _105533 _105532) = (term247 A N _105532 _105533)).
Proof. exact (SYM (@lem7999924 A N _105532 _105533)). Qed.
Lemma lem7999926 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term208 A N _105533 _105532) = (term247 A N _105532 _105533).
Proof. exact (EQ_MP (@lem7999925 A N _105532 _105533) (@lem0)). Qed.
Lemma lem7999927 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) (h1 : term8 A N) : term247 A N _105532 _105533.
Proof. exact (EQ_MP (@lem7999926 A N _105532 _105533) (@lem7999518 A N _105533 _105532 h1)). Qed.
Lemma lem7999929 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7999930 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) : (term247 A N _105532 _105533) = (term250 A N _105533 _105532).
Proof. exact (@lem7999929 (term199 A N _105532 _105533) (@FINITE (cart A N) _105532)). Qed.
Lemma lem7999932 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7999933 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term251 A N _105532 _105533) = (@HAS_SIZE (cart A N) _105532 _105533).
Proof. exact (@lem7999932 (@HAS_SIZE (cart A N) _105532 _105533)). Qed.
Lemma lem7999934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7999935 {A N : Type'} (_105532 : type24 A N) (_105533 : nat) : (term252 A N _105532 _105533) = (term253 A N _105532 _105533).
Proof. exact (MK_COMB (@lem7999934) (@lem7999933 A N _105532 _105533)). Qed.
Lemma lem7999936 {A N : Type'} (_105532 : type24 A N) : (@FINITE (cart A N) _105532) = (@FINITE (cart A N) _105532).
Proof. exact (eq_refl (@FINITE (cart A N) _105532)). Qed.
Lemma lem7999937 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) : (term250 A N _105533 _105532) = (term254 A N _105533 _105532).
Proof. exact (MK_COMB (@lem7999935 A N _105532 _105533) (@lem7999936 A N _105532)). Qed.
Lemma lem7999938 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) : (term247 A N _105532 _105533) = (term254 A N _105533 _105532).
Proof. exact (TRANS (@lem7999930 A N _105533 _105532) (@lem7999937 A N _105533 _105532)). Qed.
Lemma lem7999941 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) (h1 : term8 A N) : term254 A N _105533 _105532.
Proof. exact (EQ_MP (@lem7999938 A N _105533 _105532) (@lem7999927 A N _105532 _105533 h1)). Qed.
Lemma lem7999942 {A N : Type'} (_105533 : nat) (_105532 : type24 A N) (h1 : term8 A N) : term254 A N _105533 _105532.
Proof. exact (@lem7999941 A N _105533 _105532 h1). Qed.
Lemma lem7999943 {A N : Type'} (h1 : term8 A N) : term255 A N.
Proof. exact (@lem7999942 A N (term256 A N) (@UNIV (cart A N)) h1). Qed.
Lemma lem7999946 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : @FINITE (cart A N) (@UNIV (cart A N)).
Proof. exact (@lem7999943 A N h2 (@lem7999898 A N h1 h3 h4)). Qed.
Lemma lem7999947 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term257 A N.
Proof. exact (fun h0 : term207 A N => @lem7999946 A N h1 h2 h3 h4). Qed.
Lemma lem7999949 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999950 {A N : Type'} : (term257 A N) = (@FINITE (cart A N) (@UNIV (cart A N))).
Proof. exact (@lem7999949 (@FINITE (cart A N) (@UNIV (cart A N)))). Qed.
Lemma lem7999951 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : @FINITE (cart A N) (@UNIV (cart A N)).
Proof. exact (EQ_MP (@lem7999950 A N) (@lem7999947 A N h1 h2 h3 h4)). Qed.
Lemma lem7999954 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7999956 {A N : Type'} : (term207 A N) = (term258 A N).
Proof. exact (@lem7999954 (@FINITE (cart A N) (@UNIV (cart A N)))). Qed.
Lemma lem7999959 {A N : Type'} (h1 : term3 A N) : term258 A N.
Proof. exact (EQ_MP (@lem7999956 A N) (@lem7999488 A N h1)). Qed.
Lemma lem7999962 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : False.
Proof. exact (@lem7999959 A N h4 (@lem7999951 A N h1 h2 h3 h4)). Qed.
Lemma lem7999963 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term259.
Proof. exact (fun h0 : ~ False => @lem7999962 A N h1 h2 h3 h4). Qed.
Lemma lem7999965 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7999966 : term259 = False.
Proof. exact (@lem7999965 False). Qed.
Lemma lem7999967 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : False.
Proof. exact (EQ_MP (@lem7999966) (@lem7999963 A N h1 h2 h3 h4)). Qed.
Lemma lem7999968 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term17 A N.
Proof. exact (fun h0 : term5 A N => @lem7999967 A N h1 h2 h3 h4). Qed.
Lemma lem7999969 {A N : Type'} : (term17 A N) = (term18 A N).
Proof. exact (@lem69 (term5 A N)). Qed.
Lemma lem7999970 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term18 A N.
Proof. exact (EQ_MP (@lem7999969 A N) (@lem7999968 A N h1 h2 h3 h4)). Qed.
Lemma lem7999971 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term21 A N.
Proof. exact (fun h0 : term7 A N => @lem7999970 A N h1 h2 h3 h4). Qed.
Lemma lem7999972 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term24 A N.
Proof. exact (fun h0 : term4 A N => @lem7999971 A N h1 h2 h0 h3). Qed.
Lemma lem7999973 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term27 A N.
Proof. exact (fun h0 : term6 A => @lem7999972 A N h1 h2 h3). Qed.
Lemma lem7999974 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term30 A N.
Proof. exact (fun h0 : term9 A N => @lem7999973 A N h1 h2 h3). Qed.
Lemma lem7999975 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term33 A N.
Proof. exact (fun h0 : term11 A N => @lem7999974 A N h1 h2 h3). Qed.
Lemma lem7999976 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term36 A N.
Proof. exact (fun h0 : term8 A N => @lem7999975 A N h1 h0 h2). Qed.
Lemma lem7999977 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term39 A N.
Proof. exact (fun h0 : term12 A => @lem7999976 A N h1 h2). Qed.
Lemma lem7999978 {A N : Type'} (h1 : term3 A N) : term42 A N.
Proof. exact (fun h0 : term10 A => @lem7999977 A N h0 h1). Qed.
Lemma lem7999979 {A N : Type'} : term44 A N.
Proof. exact (fun h0 : term3 A N => @lem7999978 A N h0). Qed.
Lemma lem7999980 {A N : Type'} : term13 A N.
Proof. exact (EQ_MP (@lem7996825 A N) (@lem7999979 A N)). Qed.
Lemma lem7999982 {A N : Type'} : term13 A N.
Proof. exact (@lem7996419 A N (@lem7999980 A N)). Qed.
Lemma lem7999983 {A N : Type'} (h1 : term3 A N) : term41 A N.
Proof. exact (@lem7999982 A N (@lem7996391 A N h1)). Qed.
Lemma lem7999984 {A N : Type'} (h1 : term3 A N) : term38 A N.
Proof. exact (@lem7999983 A N h1 (@lem7996399 A)). Qed.
Lemma lem7999985 {A N : Type'} (h1 : term3 A N) : term35 A N.
Proof. exact (@lem7999984 A N h1 (@lem7996401 A)). Qed.
Lemma lem7999986 {A N : Type'} (h1 : term3 A N) : term32 A N.
Proof. exact (@lem7999985 A N h1 (@lem7996397 A N)). Qed.
Lemma lem7999987 {A N : Type'} (h1 : term3 A N) : term29 A N.
Proof. exact (@lem7999986 A N h1 (@lem7996400 A N)). Qed.
Lemma lem7999988 {A N : Type'} (h1 : term3 A N) : term26 A N.
Proof. exact (@lem7999987 A N h1 (@lem7996398 A N)). Qed.
Lemma lem7999989 {A N : Type'} (h1 : term3 A N) : term23 A N.
Proof. exact (@lem7999988 A N h1 (@lem7996395 A)). Qed.
Lemma lem7999990 {A N : Type'} (h1 : term3 A N) : term20 A N.
Proof. exact (@lem7999989 A N h1 (@lem7996392 A N)). Qed.
Lemma lem7999991 {A N : Type'} (h1 : term3 A N) : term17 A N.
Proof. exact (@lem7999990 A N h1 (@lem7996396 A N)). Qed.
Lemma lem7999992 {A N : Type'} (h1 : term3 A N) : False.
Proof. exact (@lem7999991 A N h1 (@lem7996393 A N)). Qed.
Lemma lem7999993 {A N : Type'} (h1 : term3 A N) : (term3 A N) = False.
Proof. exact (prop_ext (fun h2 : term3 A N => @lem7999992 A N h1) (fun h2 : False => @lem7996391 A N h1)). Qed.
Lemma lem7999994 {A N : Type'} (h1 : term3 A N) : False.
Proof. exact (EQ_MP (@lem7999993 A N h1) (@lem7996391 A N h1)). Qed.
Lemma lem7999995 {A N : Type'} : term2 A N.
Proof. exact (fun h0 : term3 A N => @lem7999994 A N h0). Qed.
Lemma lem7999996 {A N : Type'} : term1 A N.
Proof. exact (EQ_MP (@lem7996390 A N) (@lem7999995 A N)). Qed.
