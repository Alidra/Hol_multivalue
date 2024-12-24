Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_INSERT_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3207464 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3207465 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3207466 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3207465 A x) (@lem3207464 A x)). Qed.
Lemma lem3207467 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem3207466 A x y). Qed.
Lemma lem3207468 {A : Type'} (y : A) (x : A) : (term2 A x y) = (term3 A y x).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem3207469 {A : Type'} (y : A) (x : A) : term3 A y x.
Proof. exact (EQ_MP (@lem3207468 A y x) (@lem3207467 A x y)). Qed.
Lemma lem3207470 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term4 A y x s.
Proof. exact (@lem3207469 A y x s). Qed.
Lemma lem3207471 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A y x s) = ((term5 A x y s) = (term6 A y x s)).
Proof. exact (eq_refl (term4 A y x s)). Qed.
Lemma lem3207494 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3207471 A y x s) (@lem3207470 A y x s)). Qed.
Lemma lem3207495 {_84024 : Type'} (y : _84024) (x : _84024) (s : _84024 -> Prop) : (term5 _84024 x y s) = (term6 _84024 y x s).
Proof. exact (@lem3207494 _84024 y x s). Qed.
Lemma lem3207496 {_84024 : Type'} (a : _84024) (x : _84024) (s : _84024 -> Prop) : (term5 _84024 x a s) = (term6 _84024 a x s).
Proof. exact (@lem3207495 _84024 a x s). Qed.
Lemma lem3207501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3207502 {_84024 : Type'} (a : _84024) (x : _84024) (s : _84024 -> Prop) : (term7 _84024 x a s) = (term8 _84024 a x s).
Proof. exact (MK_COMB (@lem3207501) (@lem3207496 _84024 a x s)). Qed.
Lemma lem3207503 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3207504 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term9 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (MK_COMB (@lem3207502 _84024 a x s) (@lem3207503 _84024 P x)). Qed.
Lemma lem3207507 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term11 _84024 a s P) = (term12 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207504 _84024 a s P x)). Qed.
Lemma lem3207508 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207509 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term13 _84024 a s P) = (term14 _84024 a s P).
Proof. exact (MK_COMB (@lem3207508 _84024) (@lem3207507 _84024 a s P)). Qed.
Lemma lem3207514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207515 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term15 _84024 a s P) = (term16 _84024 a s P).
Proof. exact (MK_COMB (@lem3207514) (@lem3207509 _84024 a s P)). Qed.
Lemma lem3207524 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term17 _84024 a s P) = (term17 _84024 a s P).
Proof. exact (eq_refl (term17 _84024 a s P)). Qed.
Lemma lem3207525 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term13 _84024 a s P) = (term17 _84024 a s P)) = ((term14 _84024 a s P) = (term17 _84024 a s P)).
Proof. exact (MK_COMB (@lem3207515 _84024 a s P) (@lem3207524 _84024 a s P)). Qed.
Lemma lem3207528 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) : (term18 _84024 a P) = (term19 _84024 a P).
Proof. exact (fun_ext (fun s : _84024 -> Prop => @lem3207525 _84024 a s P)). Qed.
Lemma lem3207529 {_84024 : Type'} : (@all (_84024 -> Prop)) = (@all (_84024 -> Prop)).
Proof. exact (eq_refl (@all (_84024 -> Prop))). Qed.
Lemma lem3207530 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) : (term20 _84024 a P) = (term21 _84024 a P).
Proof. exact (MK_COMB (@lem3207529 _84024) (@lem3207528 _84024 a P)). Qed.
Lemma lem3207535 {_84024 : Type'} (P : _84024 -> Prop) : (term22 _84024 P) = (term23 _84024 P).
Proof. exact (fun_ext (fun a : _84024 => @lem3207530 _84024 a P)). Qed.
Lemma lem3207536 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3207537 {_84024 : Type'} (P : _84024 -> Prop) : (term24 _84024 P) = (term25 _84024 P).
Proof. exact (MK_COMB (@lem3207536 _84024) (@lem3207535 _84024 P)). Qed.
Lemma lem3207542 {_84024 : Type'} : (term26 _84024) = (term27 _84024).
Proof. exact (fun_ext (fun P : _84024 -> Prop => @lem3207537 _84024 P)). Qed.
Lemma lem3207543 {_84024 : Type'} : (@all (_84024 -> Prop)) = (@all (_84024 -> Prop)).
Proof. exact (eq_refl (@all (_84024 -> Prop))). Qed.
Lemma lem3207544 {_84024 : Type'} : (term28 _84024) = (term29 _84024).
Proof. exact (MK_COMB (@lem3207543 _84024) (@lem3207542 _84024)). Qed.
Lemma lem3207549 {_84024 : Type'} : (term29 _84024) = (term28 _84024).
Proof. exact (SYM (@lem3207544 _84024)). Qed.
Lemma lem3207551 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3207552 {_84024 : Type'} : (term29 _84024) = (term31 _84024).
Proof. exact (@lem3207551 (term29 _84024)). Qed.
Lemma lem3207553 {_84024 : Type'} : (term31 _84024) = (term29 _84024).
Proof. exact (SYM (@lem3207552 _84024)). Qed.
Lemma lem3207554 {_84024 : Type'} (h1 : term32 _84024) : term32 _84024.
Proof. exact (h1). Qed.
Lemma lem3207557 {_84024 : Type'} (h1 : term31 _84024) : term31 _84024.
Proof. exact (h1). Qed.
Lemma lem3207558 {_84024 : Type'} : term33 _84024.
Proof. exact (fun h0 : term31 _84024 => @lem3207557 _84024 h0). Qed.
Lemma lem3207559 {_84024 : Type'} (h1 : term33 _84024) : term33 _84024.
Proof. exact (h1). Qed.
Lemma lem3207560 {_84024 : Type'} (h1 : term31 _84024) : term31 _84024.
Proof. exact (h1). Qed.
Lemma lem3207561 {_84024 : Type'} (h1 : term31 _84024) (h2 : term33 _84024) : term31 _84024.
Proof. exact (@lem3207559 _84024 h2 (@lem3207560 _84024 h1)). Qed.
Lemma lem3207562 {_84024 : Type'} (h1 : term31 _84024) : term34 _84024.
Proof. exact (fun h0 : term33 _84024 => @lem3207561 _84024 h1 h0). Qed.
Lemma lem3207563 {_84024 : Type'} (h1 : term33 _84024) : term33 _84024.
Proof. exact (h1). Qed.
Lemma lem3207564 {_84024 : Type'} (h1 : term31 _84024) (h2 : term33 _84024) : term31 _84024.
Proof. exact (@lem3207562 _84024 h1 (@lem3207563 _84024 h2)). Qed.
Lemma lem3207565 {_84024 : Type'} (h1 : term33 _84024) : term33 _84024.
Proof. exact (fun h0 : term31 _84024 => @lem3207564 _84024 h0 h1). Qed.
Lemma lem3207566 {_84024 : Type'} : term35 _84024.
Proof. exact (fun h0 : term33 _84024 => @lem3207565 _84024 h0). Qed.
Lemma lem3207569 {_84024 : Type'} : term33 _84024.
Proof. exact (@lem3207566 _84024 (@lem3207558 _84024)). Qed.
Lemma lem3207570 {_84024 : Type'} : term33 _84024.
Proof. exact (@lem3207569 _84024). Qed.
Lemma lem3207572 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3207573 {_84024 : Type'} : (term31 _84024) = (term36 _84024).
Proof. exact (@lem3207572 (term32 _84024)). Qed.
Lemma lem3207575 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3207576 {_84024 : Type'} : (term36 _84024) = (term29 _84024).
Proof. exact (@lem3207575 (term29 _84024)). Qed.
Lemma lem3207665 {_84024 : Type'} : (term31 _84024) = (term29 _84024).
Proof. exact (TRANS (@lem3207573 _84024) (@lem3207576 _84024)). Qed.
Lemma lem3207670 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term38 _84024 s P x) = (term38 _84024 s P x).
Proof. exact (eq_refl (term38 _84024 s P x)). Qed.
Lemma lem3207671 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term39 _84024 s P) = (term39 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207670 _84024 s P x)). Qed.
Lemma lem3207672 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207673 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term40 _84024 s P) = (term40 _84024 s P).
Proof. exact (MK_COMB (@lem3207672 _84024) (@lem3207671 _84024 s P)). Qed.
Lemma lem3207676 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term41 _84024 P a) = (term41 _84024 P a).
Proof. exact (eq_refl (term41 _84024 P a)). Qed.
Lemma lem3207677 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term17 _84024 a s P) = (term17 _84024 a s P).
Proof. exact (MK_COMB (@lem3207676 _84024 P a) (@lem3207673 _84024 s P)). Qed.
Lemma lem3207686 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term10 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (eq_refl (term10 _84024 a s P x)). Qed.
Lemma lem3207687 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term12 _84024 a s P) = (term12 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207686 _84024 a s P x)). Qed.
Lemma lem3207688 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207689 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term14 _84024 a s P) = (term14 _84024 a s P).
Proof. exact (MK_COMB (@lem3207688 _84024) (@lem3207687 _84024 a s P)). Qed.
Lemma lem3207690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3207691 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term16 _84024 a s P) = (term16 _84024 a s P).
Proof. exact (MK_COMB (@lem3207690) (@lem3207689 _84024 a s P)). Qed.
Lemma lem3207692 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term14 _84024 a s P) = (term17 _84024 a s P)) = ((term14 _84024 a s P) = (term17 _84024 a s P)).
Proof. exact (MK_COMB (@lem3207691 _84024 a s P) (@lem3207677 _84024 a s P)). Qed.
Lemma lem3207693 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) : (term19 _84024 a P) = (term19 _84024 a P).
Proof. exact (fun_ext (fun s : _84024 -> Prop => @lem3207692 _84024 a s P)). Qed.
Lemma lem3207694 {_84024 : Type'} : (@all (_84024 -> Prop)) = (@all (_84024 -> Prop)).
Proof. exact (eq_refl (@all (_84024 -> Prop))). Qed.
Lemma lem3207695 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) : (term21 _84024 a P) = (term21 _84024 a P).
Proof. exact (MK_COMB (@lem3207694 _84024) (@lem3207693 _84024 a P)). Qed.
Lemma lem3207696 {_84024 : Type'} (P : _84024 -> Prop) : (term23 _84024 P) = (term23 _84024 P).
Proof. exact (fun_ext (fun a : _84024 => @lem3207695 _84024 a P)). Qed.
Lemma lem3207697 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3207698 {_84024 : Type'} (P : _84024 -> Prop) : (term25 _84024 P) = (term25 _84024 P).
Proof. exact (MK_COMB (@lem3207697 _84024) (@lem3207696 _84024 P)). Qed.
Lemma lem3207699 {_84024 : Type'} : (term27 _84024) = (term27 _84024).
Proof. exact (fun_ext (fun P : _84024 -> Prop => @lem3207698 _84024 P)). Qed.
Lemma lem3207700 {_84024 : Type'} : (@all (_84024 -> Prop)) = (@all (_84024 -> Prop)).
Proof. exact (eq_refl (@all (_84024 -> Prop))). Qed.
Lemma lem3207701 {_84024 : Type'} : (term29 _84024) = (term29 _84024).
Proof. exact (MK_COMB (@lem3207700 _84024) (@lem3207699 _84024)). Qed.
Lemma lem3207742 {_84024 : Type'} : (term31 _84024) = (term29 _84024).
Proof. exact (TRANS (@lem3207665 _84024) (@lem3207701 _84024)). Qed.
Lemma lem3207743 {_84024 : Type'} : (term29 _84024) = (term31 _84024).
Proof. exact (SYM (@lem3207742 _84024)). Qed.
Lemma lem3207745 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3207746 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term14 _84024 a s P) = (term17 _84024 a s P)) = (term42 _84024 a s P).
Proof. exact (@lem3207745 ((term14 _84024 a s P) = (term17 _84024 a s P))). Qed.
Lemma lem3207747 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term42 _84024 a s P) = ((term14 _84024 a s P) = (term17 _84024 a s P)).
Proof. exact (SYM (@lem3207746 _84024 a s P)). Qed.
Lemma lem3207748 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term43 _84024 a s P) : term43 _84024 a s P.
Proof. exact (h1). Qed.
Lemma lem3207757 {_84024 : Type'} (a : _84024) (x : _84024) (s : _84024 -> Prop) : (term44 _84024 a x s) = (term45 _84024 a x s).
Proof. exact (@lem17160 (x = a) (@IN _84024 x s)). Qed.
Lemma lem3207761 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term46 _84024 P x) = (term46 _84024 P x).
Proof. exact (eq_refl (term46 _84024 P x)). Qed.
Lemma lem3207763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3207764 {_84024 : Type'} (a : _84024) (x : _84024) (s : _84024 -> Prop) : (term47 _84024 a x s) = (term48 _84024 a x s).
Proof. exact (MK_COMB (@lem3207763) (@lem3207757 _84024 a x s)). Qed.
Lemma lem3207765 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term49 _84024 a s P x) = (term50 _84024 a s P x).
Proof. exact (MK_COMB (@lem3207764 _84024 a x s) (@lem3207761 _84024 P x)). Qed.
Lemma lem3207766 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term51 _84024 a s P x) = (term49 _84024 a s P x).
Proof. exact (@lem17045 (term6 _84024 a x s) (P x)). Qed.
Lemma lem3207767 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term51 _84024 a s P x) = (term50 _84024 a s P x).
Proof. exact (TRANS (@lem3207766 _84024 a s P x) (@lem3207765 _84024 a s P x)). Qed.
Lemma lem3207770 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term10 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (eq_refl (term10 _84024 a s P x)). Qed.
Lemma lem3207771 {_84024 : Type'} (P : _84024 -> Prop) : (term52 _84024 P) = (term53 _84024 P).
Proof. exact (@lem18394 _84024 P). Qed.
Lemma lem3207772 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term54 _84024 a s P) = (term55 _84024 a s P).
Proof. exact (@lem3207771 _84024 (term12 _84024 a s P)). Qed.
Lemma lem3207773 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term56 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (eq_refl (term56 _84024 a s P x)). Qed.
Lemma lem3207774 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3207775 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term57 _84024 a s P x) = (term51 _84024 a s P x).
Proof. exact (MK_COMB (@lem3207774) (@lem3207773 _84024 a s P x)). Qed.
Lemma lem3207776 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term57 _84024 a s P x) = (term50 _84024 a s P x).
Proof. exact (TRANS (@lem3207775 _84024 a s P x) (@lem3207767 _84024 a s P x)). Qed.
Lemma lem3207777 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term58 _84024 a s P) = (term59 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207776 _84024 a s P x)). Qed.
Lemma lem3207778 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3207779 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term55 _84024 a s P) = (term60 _84024 a s P).
Proof. exact (MK_COMB (@lem3207778 _84024) (@lem3207777 _84024 a s P)). Qed.
Lemma lem3207780 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term54 _84024 a s P) = (term60 _84024 a s P).
Proof. exact (TRANS (@lem3207772 _84024 a s P) (@lem3207779 _84024 a s P)). Qed.
Lemma lem3207781 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term12 _84024 a s P) = (term12 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207770 _84024 a s P x)). Qed.
Lemma lem3207782 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207783 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term14 _84024 a s P) = (term14 _84024 a s P).
Proof. exact (MK_COMB (@lem3207782 _84024) (@lem3207781 _84024 a s P)). Qed.
Lemma lem3207794 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term61 _84024 s P x) = (term62 _84024 s P x).
Proof. exact (@lem17045 (@IN _84024 x s) (P x)). Qed.
Lemma lem3207797 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term38 _84024 s P x) = (term38 _84024 s P x).
Proof. exact (eq_refl (term38 _84024 s P x)). Qed.
Lemma lem3207798 {_84024 : Type'} (P : _84024 -> Prop) : (term52 _84024 P) = (term53 _84024 P).
Proof. exact (@lem18394 _84024 P). Qed.
Lemma lem3207799 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term63 _84024 s P) = (term64 _84024 s P).
Proof. exact (@lem3207798 _84024 (term39 _84024 s P)). Qed.
Lemma lem3207800 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term65 _84024 s P x) = (term38 _84024 s P x).
Proof. exact (eq_refl (term65 _84024 s P x)). Qed.
Lemma lem3207801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3207802 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term66 _84024 s P x) = (term61 _84024 s P x).
Proof. exact (MK_COMB (@lem3207801) (@lem3207800 _84024 s P x)). Qed.
Lemma lem3207803 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term66 _84024 s P x) = (term62 _84024 s P x).
Proof. exact (TRANS (@lem3207802 _84024 s P x) (@lem3207794 _84024 s P x)). Qed.
Lemma lem3207804 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term67 _84024 s P) = (term68 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207803 _84024 s P x)). Qed.
Lemma lem3207805 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3207806 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term64 _84024 s P) = (term69 _84024 s P).
Proof. exact (MK_COMB (@lem3207805 _84024) (@lem3207804 _84024 s P)). Qed.
Lemma lem3207807 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term63 _84024 s P) = (term69 _84024 s P).
Proof. exact (TRANS (@lem3207799 _84024 s P) (@lem3207806 _84024 s P)). Qed.
Lemma lem3207808 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term39 _84024 s P) = (term39 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207797 _84024 s P x)). Qed.
Lemma lem3207809 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207810 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term40 _84024 s P) = (term40 _84024 s P).
Proof. exact (MK_COMB (@lem3207809 _84024) (@lem3207808 _84024 s P)). Qed.
Lemma lem3207812 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term70 _84024 P a) = (term70 _84024 P a).
Proof. exact (eq_refl (term70 _84024 P a)). Qed.
Lemma lem3207813 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term71 _84024 a s P) = (term72 _84024 a s P).
Proof. exact (MK_COMB (@lem3207812 _84024 P a) (@lem3207807 _84024 s P)). Qed.
Lemma lem3207814 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term73 _84024 a s P) = (term71 _84024 a s P).
Proof. exact (@lem17160 (P a) (term40 _84024 s P)). Qed.
Lemma lem3207815 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term73 _84024 a s P) = (term72 _84024 a s P).
Proof. exact (TRANS (@lem3207814 _84024 a s P) (@lem3207813 _84024 a s P)). Qed.
Lemma lem3207817 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term41 _84024 P a) = (term41 _84024 P a).
Proof. exact (eq_refl (term41 _84024 P a)). Qed.
Lemma lem3207818 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term17 _84024 a s P) = (term17 _84024 a s P).
Proof. exact (MK_COMB (@lem3207817 _84024 P a) (@lem3207810 _84024 s P)). Qed.
Lemma lem3207819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3207820 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term74 _84024 a s P) = (term75 _84024 a s P).
Proof. exact (MK_COMB (@lem3207819) (@lem3207780 _84024 a s P)). Qed.
Lemma lem3207821 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term76 _84024 a s P) = (term77 _84024 a s P).
Proof. exact (MK_COMB (@lem3207820 _84024 a s P) (@lem3207818 _84024 a s P)). Qed.
Lemma lem3207822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3207823 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term78 _84024 a s P) = (term78 _84024 a s P).
Proof. exact (MK_COMB (@lem3207822) (@lem3207783 _84024 a s P)). Qed.
Lemma lem3207824 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term79 _84024 a s P) = (term80 _84024 a s P).
Proof. exact (MK_COMB (@lem3207823 _84024 a s P) (@lem3207815 _84024 a s P)). Qed.
Lemma lem3207825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3207826 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term81 _84024 a s P) = (term82 _84024 a s P).
Proof. exact (MK_COMB (@lem3207825) (@lem3207824 _84024 a s P)). Qed.
Lemma lem3207827 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term83 _84024 a s P) = (term84 _84024 a s P).
Proof. exact (MK_COMB (@lem3207826 _84024 a s P) (@lem3207821 _84024 a s P)). Qed.
Lemma lem3207828 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term43 _84024 a s P) = (term83 _84024 a s P).
Proof. exact (@lem17646 (term14 _84024 a s P) (term17 _84024 a s P)). Qed.
Lemma lem3207829 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term43 _84024 a s P) = (term84 _84024 a s P).
Proof. exact (TRANS (@lem3207828 _84024 a s P) (@lem3207827 _84024 a s P)). Qed.
Lemma lem3207992 {A : Type'} (P : A -> Prop) (Q : Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3207993 {_84024 : Type'} (P : _84024 -> Prop) (Q : Prop) : (term85 _84024 P Q) = (term86 _84024 P Q).
Proof. exact (@lem3207992 _84024 P Q). Qed.
Lemma lem3207994 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term87 _84024 a s P) = (term88 _84024 a s P).
Proof. exact (@lem3207993 _84024 (term12 _84024 a s P) (term72 _84024 a s P)). Qed.
Lemma lem3207995 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term56 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (eq_refl (term56 _84024 a s P x)). Qed.
Lemma lem3207996 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term89 _84024 a s P) = (term12 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3207995 _84024 a s P x)). Qed.
Lemma lem3207997 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3207998 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term90 _84024 a s P) = (term14 _84024 a s P).
Proof. exact (MK_COMB (@lem3207997 _84024) (@lem3207996 _84024 a s P)). Qed.
Lemma lem3207999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3208000 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term91 _84024 a s P) = (term78 _84024 a s P).
Proof. exact (MK_COMB (@lem3207999) (@lem3207998 _84024 a s P)). Qed.
Lemma lem3208001 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term72 _84024 a s P) = (term72 _84024 a s P).
Proof. exact (eq_refl (term72 _84024 a s P)). Qed.
Lemma lem3208002 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term87 _84024 a s P) = (term80 _84024 a s P).
Proof. exact (MK_COMB (@lem3208000 _84024 a s P) (@lem3208001 _84024 a s P)). Qed.
Lemma lem3208003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208004 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term92 _84024 a s P) = (term93 _84024 a s P).
Proof. exact (MK_COMB (@lem3208003) (@lem3208002 _84024 a s P)). Qed.
Lemma lem3208005 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term56 _84024 a s P x) = (term10 _84024 a s P x).
Proof. exact (eq_refl (term56 _84024 a s P x)). Qed.
Lemma lem3208006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3208007 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term94 _84024 a s P x) = (term95 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208006) (@lem3208005 _84024 a s P x)). Qed.
Lemma lem3208008 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term72 _84024 a s P) = (term72 _84024 a s P).
Proof. exact (eq_refl (term72 _84024 a s P)). Qed.
Lemma lem3208009 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term96 _84024 x a s P) = (term97 _84024 x a s P).
Proof. exact (MK_COMB (@lem3208007 _84024 a s P x) (@lem3208008 _84024 a s P)). Qed.
Lemma lem3208010 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term98 _84024 a s P) = (term99 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208009 _84024 x a s P)). Qed.
Lemma lem3208011 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208012 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term88 _84024 a s P) = (term100 _84024 a s P).
Proof. exact (MK_COMB (@lem3208011 _84024) (@lem3208010 _84024 a s P)). Qed.
Lemma lem3208013 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term87 _84024 a s P) = (term88 _84024 a s P)) = ((term80 _84024 a s P) = (term100 _84024 a s P)).
Proof. exact (MK_COMB (@lem3208004 _84024 a s P) (@lem3208012 _84024 a s P)). Qed.
Lemma lem3208014 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term80 _84024 a s P) = (term100 _84024 a s P).
Proof. exact (EQ_MP (@lem3208013 _84024 a s P) (@lem3207994 _84024 a s P)). Qed.
Lemma lem3208015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3208016 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term82 _84024 a s P) = (term101 _84024 a s P).
Proof. exact (MK_COMB (@lem3208015) (@lem3208014 _84024 a s P)). Qed.
Lemma lem3208018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3208019 {_84024 : Type'} (P : Prop) (Q : _84024 -> Prop) : (term102 _84024 P Q) = (term103 _84024 P Q).
Proof. exact (@lem3208018 _84024 P Q). Qed.
Lemma lem3208020 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term104 _84024 a s P) = (term105 _84024 a s P).
Proof. exact (@lem3208019 _84024 (P a) (term39 _84024 s P)). Qed.
Lemma lem3208021 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term65 _84024 s P x) = (term38 _84024 s P x).
Proof. exact (eq_refl (term65 _84024 s P x)). Qed.
Lemma lem3208022 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term106 _84024 s P) = (term39 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208021 _84024 s P x)). Qed.
Lemma lem3208023 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208024 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term107 _84024 s P) = (term40 _84024 s P).
Proof. exact (MK_COMB (@lem3208023 _84024) (@lem3208022 _84024 s P)). Qed.
Lemma lem3208025 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term41 _84024 P a) = (term41 _84024 P a).
Proof. exact (eq_refl (term41 _84024 P a)). Qed.
Lemma lem3208026 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term104 _84024 a s P) = (term17 _84024 a s P).
Proof. exact (MK_COMB (@lem3208025 _84024 P a) (@lem3208024 _84024 s P)). Qed.
Lemma lem3208027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208028 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term108 _84024 a s P) = (term109 _84024 a s P).
Proof. exact (MK_COMB (@lem3208027) (@lem3208026 _84024 a s P)). Qed.
Lemma lem3208029 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term65 _84024 s P x) = (term38 _84024 s P x).
Proof. exact (eq_refl (term65 _84024 s P x)). Qed.
Lemma lem3208030 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term41 _84024 P a) = (term41 _84024 P a).
Proof. exact (eq_refl (term41 _84024 P a)). Qed.
Lemma lem3208031 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term110 _84024 a s P x) = (term111 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208030 _84024 P a) (@lem3208029 _84024 s P x)). Qed.
Lemma lem3208032 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term112 _84024 a s P) = (term113 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208031 _84024 a s P x)). Qed.
Lemma lem3208033 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208034 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term105 _84024 a s P) = (term114 _84024 a s P).
Proof. exact (MK_COMB (@lem3208033 _84024) (@lem3208032 _84024 a s P)). Qed.
Lemma lem3208035 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term104 _84024 a s P) = (term105 _84024 a s P)) = ((term17 _84024 a s P) = (term114 _84024 a s P)).
Proof. exact (MK_COMB (@lem3208028 _84024 a s P) (@lem3208034 _84024 a s P)). Qed.
Lemma lem3208036 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term17 _84024 a s P) = (term114 _84024 a s P).
Proof. exact (EQ_MP (@lem3208035 _84024 a s P) (@lem3208020 _84024 a s P)). Qed.
Lemma lem3208037 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term75 _84024 a s P) = (term75 _84024 a s P).
Proof. exact (eq_refl (term75 _84024 a s P)). Qed.
Lemma lem3208038 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term77 _84024 a s P) = (term115 _84024 a s P).
Proof. exact (MK_COMB (@lem3208037 _84024 a s P) (@lem3208036 _84024 a s P)). Qed.
Lemma lem3208040 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3208041 {_84024 : Type'} (P : Prop) (Q : _84024 -> Prop) : (term116 _84024 P Q) = (term117 _84024 P Q).
Proof. exact (@lem3208040 _84024 P Q). Qed.
Lemma lem3208042 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term118 _84024 a s P) = (term119 _84024 a s P).
Proof. exact (@lem3208041 _84024 (term60 _84024 a s P) (term113 _84024 a s P)). Qed.
Lemma lem3208043 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term120 _84024 a s P x) = (term111 _84024 a s P x).
Proof. exact (eq_refl (term120 _84024 a s P x)). Qed.
Lemma lem3208044 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term121 _84024 a s P) = (term113 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208043 _84024 a s P x)). Qed.
Lemma lem3208045 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208046 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term122 _84024 a s P) = (term114 _84024 a s P).
Proof. exact (MK_COMB (@lem3208045 _84024) (@lem3208044 _84024 a s P)). Qed.
Lemma lem3208047 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term75 _84024 a s P) = (term75 _84024 a s P).
Proof. exact (eq_refl (term75 _84024 a s P)). Qed.
Lemma lem3208048 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term118 _84024 a s P) = (term115 _84024 a s P).
Proof. exact (MK_COMB (@lem3208047 _84024 a s P) (@lem3208046 _84024 a s P)). Qed.
Lemma lem3208049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208050 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term123 _84024 a s P) = (term124 _84024 a s P).
Proof. exact (MK_COMB (@lem3208049) (@lem3208048 _84024 a s P)). Qed.
Lemma lem3208051 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term120 _84024 a s P x) = (term111 _84024 a s P x).
Proof. exact (eq_refl (term120 _84024 a s P x)). Qed.
Lemma lem3208052 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term75 _84024 a s P) = (term75 _84024 a s P).
Proof. exact (eq_refl (term75 _84024 a s P)). Qed.
Lemma lem3208053 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term125 _84024 a s P x) = (term126 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208052 _84024 a s P) (@lem3208051 _84024 a s P x)). Qed.
Lemma lem3208054 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term127 _84024 a s P) = (term128 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208053 _84024 a s P x)). Qed.
Lemma lem3208055 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208056 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term119 _84024 a s P) = (term129 _84024 a s P).
Proof. exact (MK_COMB (@lem3208055 _84024) (@lem3208054 _84024 a s P)). Qed.
Lemma lem3208057 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term118 _84024 a s P) = (term119 _84024 a s P)) = ((term115 _84024 a s P) = (term129 _84024 a s P)).
Proof. exact (MK_COMB (@lem3208050 _84024 a s P) (@lem3208056 _84024 a s P)). Qed.
Lemma lem3208058 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term115 _84024 a s P) = (term129 _84024 a s P).
Proof. exact (EQ_MP (@lem3208057 _84024 a s P) (@lem3208042 _84024 a s P)). Qed.
Lemma lem3208059 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term77 _84024 a s P) = (term129 _84024 a s P).
Proof. exact (TRANS (@lem3208038 _84024 a s P) (@lem3208058 _84024 a s P)). Qed.
Lemma lem3208060 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term84 _84024 a s P) = (term130 _84024 a s P).
Proof. exact (MK_COMB (@lem3208016 _84024 a s P) (@lem3208059 _84024 a s P)). Qed.
Lemma lem3208062 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3208063 {_84024 : Type'} (P : _84024 -> Prop) (Q : _84024 -> Prop) : (term131 _84024 P Q) = (term132 _84024 P Q).
Proof. exact (@lem3208062 _84024 P Q). Qed.
Lemma lem3208064 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term133 _84024 a s P) = (term134 _84024 a s P).
Proof. exact (@lem3208063 _84024 (term99 _84024 a s P) (term128 _84024 a s P)). Qed.
Lemma lem3208065 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term135 _84024 a s P x) = (term97 _84024 x a s P).
Proof. exact (eq_refl (term135 _84024 a s P x)). Qed.
Lemma lem3208066 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term136 _84024 a s P) = (term99 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208065 _84024 x a s P)). Qed.
Lemma lem3208067 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208068 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term137 _84024 a s P) = (term100 _84024 a s P).
Proof. exact (MK_COMB (@lem3208067 _84024) (@lem3208066 _84024 a s P)). Qed.
Lemma lem3208069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3208070 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term138 _84024 a s P) = (term101 _84024 a s P).
Proof. exact (MK_COMB (@lem3208069) (@lem3208068 _84024 a s P)). Qed.
Lemma lem3208071 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term139 _84024 a s P x) = (term126 _84024 a s P x).
Proof. exact (eq_refl (term139 _84024 a s P x)). Qed.
Lemma lem3208072 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term140 _84024 a s P) = (term128 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208071 _84024 a s P x)). Qed.
Lemma lem3208073 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208074 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term141 _84024 a s P) = (term129 _84024 a s P).
Proof. exact (MK_COMB (@lem3208073 _84024) (@lem3208072 _84024 a s P)). Qed.
Lemma lem3208075 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term133 _84024 a s P) = (term130 _84024 a s P).
Proof. exact (MK_COMB (@lem3208070 _84024 a s P) (@lem3208074 _84024 a s P)). Qed.
Lemma lem3208076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208077 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term142 _84024 a s P) = (term143 _84024 a s P).
Proof. exact (MK_COMB (@lem3208076) (@lem3208075 _84024 a s P)). Qed.
Lemma lem3208078 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term135 _84024 a s P x) = (term97 _84024 x a s P).
Proof. exact (eq_refl (term135 _84024 a s P x)). Qed.
Lemma lem3208079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3208080 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term144 _84024 a s P x) = (term145 _84024 x a s P).
Proof. exact (MK_COMB (@lem3208079) (@lem3208078 _84024 x a s P)). Qed.
Lemma lem3208081 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term139 _84024 a s P x) = (term126 _84024 a s P x).
Proof. exact (eq_refl (term139 _84024 a s P x)). Qed.
Lemma lem3208082 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term146 _84024 a s P x) = (term147 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208080 _84024 x a s P) (@lem3208081 _84024 a s P x)). Qed.
Lemma lem3208083 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term148 _84024 a s P) = (term149 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208082 _84024 a s P x)). Qed.
Lemma lem3208084 {_84024 : Type'} : (@ex _84024) = (@ex _84024).
Proof. exact (eq_refl (@ex _84024)). Qed.
Lemma lem3208085 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term134 _84024 a s P) = (term150 _84024 a s P).
Proof. exact (MK_COMB (@lem3208084 _84024) (@lem3208083 _84024 a s P)). Qed.
Lemma lem3208086 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : ((term133 _84024 a s P) = (term134 _84024 a s P)) = ((term130 _84024 a s P) = (term150 _84024 a s P)).
Proof. exact (MK_COMB (@lem3208077 _84024 a s P) (@lem3208085 _84024 a s P)). Qed.
Lemma lem3208087 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term130 _84024 a s P) = (term150 _84024 a s P).
Proof. exact (EQ_MP (@lem3208086 _84024 a s P) (@lem3208064 _84024 a s P)). Qed.
Lemma lem3208089 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term84 _84024 a s P) = (term150 _84024 a s P).
Proof. exact (TRANS (@lem3208060 _84024 a s P) (@lem3208087 _84024 a s P)). Qed.
Lemma lem3208090 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term43 _84024 a s P) = (term150 _84024 a s P).
Proof. exact (TRANS (@lem3207829 _84024 a s P) (@lem3208089 _84024 a s P)). Qed.
Lemma lem3208091 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term43 _84024 a s P) : term150 _84024 a s P.
Proof. exact (EQ_MP (@lem3208090 _84024 a s P) (@lem3207748 _84024 a s P h1)). Qed.
Lemma lem3208092 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term147 _84024 a s P x) : term147 _84024 a s P x.
Proof. exact (h1). Qed.
Lemma lem3208109 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term111 _84024 a s P x) = (term111 _84024 a s P x).
Proof. exact (eq_refl (term111 _84024 a s P x)). Qed.
Lemma lem3208134 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term50 _84024 a s P x) = (term50 _84024 a s P x).
Proof. exact (eq_refl (term50 _84024 a s P x)). Qed.
Lemma lem3208135 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term59 _84024 a s P) = (term59 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208134 _84024 a s P x)). Qed.
Lemma lem3208136 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3208137 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term60 _84024 a s P) = (term60 _84024 a s P).
Proof. exact (MK_COMB (@lem3208136 _84024) (@lem3208135 _84024 a s P)). Qed.
Lemma lem3208138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3208139 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term75 _84024 a s P) = (term75 _84024 a s P).
Proof. exact (MK_COMB (@lem3208138) (@lem3208137 _84024 a s P)). Qed.
Lemma lem3208140 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term126 _84024 a s P x) = (term126 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208139 _84024 a s P) (@lem3208109 _84024 a s P x)). Qed.
Lemma lem3208155 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term62 _84024 s P x) = (term62 _84024 s P x).
Proof. exact (eq_refl (term62 _84024 s P x)). Qed.
Lemma lem3208156 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term68 _84024 s P) = (term68 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208155 _84024 s P x)). Qed.
Lemma lem3208157 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3208158 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term69 _84024 s P) = (term69 _84024 s P).
Proof. exact (MK_COMB (@lem3208157 _84024) (@lem3208156 _84024 s P)). Qed.
Lemma lem3208165 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term70 _84024 P a) = (term70 _84024 P a).
Proof. exact (eq_refl (term70 _84024 P a)). Qed.
Lemma lem3208166 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term72 _84024 a s P) = (term72 _84024 a s P).
Proof. exact (MK_COMB (@lem3208165 _84024 P a) (@lem3208158 _84024 s P)). Qed.
Lemma lem3208187 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term95 _84024 a s P x) = (term95 _84024 a s P x).
Proof. exact (eq_refl (term95 _84024 a s P x)). Qed.
Lemma lem3208188 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term97 _84024 x a s P) = (term97 _84024 x a s P).
Proof. exact (MK_COMB (@lem3208187 _84024 a s P x) (@lem3208166 _84024 a s P)). Qed.
Lemma lem3208189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3208190 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term145 _84024 x a s P) = (term145 _84024 x a s P).
Proof. exact (MK_COMB (@lem3208189) (@lem3208188 _84024 x a s P)). Qed.
Lemma lem3208191 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term147 _84024 a s P x) = (term147 _84024 a s P x).
Proof. exact (MK_COMB (@lem3208190 _84024 x a s P) (@lem3208140 _84024 a s P x)). Qed.
Lemma lem3208192 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term147 _84024 a s P x) : term147 _84024 a s P x.
Proof. exact (EQ_MP (@lem3208191 _84024 a s P x) (@lem3208092 _84024 a s P x h1)). Qed.
Lemma lem3208193 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term97 _84024 x a s P.
Proof. exact (h1). Qed.
Lemma lem3208194 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term126 _84024 a s P x.
Proof. exact (h1). Qed.
Lemma lem3208195 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term72 _84024 a s P.
Proof. exact (proj2 (@lem3208193 _84024 x a s P h1)). Qed.
Lemma lem3208196 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term10 _84024 a s P x.
Proof. exact (proj1 (@lem3208193 _84024 x a s P h1)). Qed.
Lemma lem3208197 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term69 _84024 s P.
Proof. exact (proj2 (@lem3208195 _84024 x a s P h1)). Qed.
Lemma lem3208200 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term6 _84024 a x s.
Proof. exact (proj1 (@lem3208196 _84024 x a s P h1)). Qed.
Lemma lem3208203 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term111 _84024 a s P x.
Proof. exact (proj2 (@lem3208194 _84024 a s P x h1)). Qed.
Lemma lem3208204 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term60 _84024 a s P.
Proof. exact (proj1 (@lem3208194 _84024 a s P x h1)). Qed.
Lemma lem3208206 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : term38 _84024 s P x.
Proof. exact (h1). Qed.
Lemma lem3208233 {_84024 : Type'} (x : _84024) (a : _84024) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3208245 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term62 _84024 s P x) = (term62 _84024 s P x).
Proof. exact (eq_refl (term62 _84024 s P x)). Qed.
Lemma lem3208246 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term68 _84024 s P) = (term68 _84024 s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208245 _84024 s P x)). Qed.
Lemma lem3208247 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3208249 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) : (term69 _84024 s P) = (term69 _84024 s P).
Proof. exact (MK_COMB (@lem3208247 _84024) (@lem3208246 _84024 s P)). Qed.
Lemma lem3208250 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term69 _84024 s P.
Proof. exact (EQ_MP (@lem3208249 _84024 s P) (@lem3208197 _84024 x a s P h1)). Qed.
Lemma lem3208258 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) (h1 : @IN _84024 x s) : @IN _84024 x s.
Proof. exact (h1). Qed.
Lemma lem3208276 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term50 _84024 a s P x) = (term151 _84024 a s P x).
Proof. exact (@lem19699 (term152 _84024 x a) (term153 _84024 x s) (term46 _84024 P x)). Qed.
Lemma lem3208277 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term59 _84024 a s P) = (term154 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208276 _84024 a s P x)). Qed.
Lemma lem3208278 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3208280 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term60 _84024 a s P) = (term155 _84024 a s P).
Proof. exact (MK_COMB (@lem3208278 _84024) (@lem3208277 _84024 a s P)). Qed.
Lemma lem3208281 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term155 _84024 a s P.
Proof. exact (EQ_MP (@lem3208280 _84024 a s P) (@lem3208204 _84024 a s P x h1)). Qed.
Lemma lem3208285 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3208303 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) : (term50 _84024 a s P x) = (term151 _84024 a s P x).
Proof. exact (@lem19699 (term152 _84024 x a) (term153 _84024 x s) (term46 _84024 P x)). Qed.
Lemma lem3208304 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term59 _84024 a s P) = (term154 _84024 a s P).
Proof. exact (fun_ext (fun x : _84024 => @lem3208303 _84024 a s P x)). Qed.
Lemma lem3208305 {_84024 : Type'} : (@all _84024) = (@all _84024).
Proof. exact (eq_refl (@all _84024)). Qed.
Lemma lem3208307 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term60 _84024 a s P) = (term155 _84024 a s P).
Proof. exact (MK_COMB (@lem3208305 _84024) (@lem3208304 _84024 a s P)). Qed.
Lemma lem3208308 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term155 _84024 a s P.
Proof. exact (EQ_MP (@lem3208307 _84024 a s P) (@lem3208204 _84024 a s P x h1)). Qed.
Lemma lem3208320 {_84024 : Type'} (_32973 : _84024) (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term156 _84024 s P _32973.
Proof. exact (@lem3208250 _84024 x a s P h1 _32973). Qed.
Lemma lem3208321 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32973 : _84024) : (term156 _84024 s P _32973) = (term62 _84024 s P _32973).
Proof. exact (eq_refl (term156 _84024 s P _32973)). Qed.
Lemma lem3208323 {_84024 : Type'} (_32974 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term157 _84024 a s P _32974.
Proof. exact (@lem3208281 _84024 a s P x h1 _32974). Qed.
Lemma lem3208324 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (_32974 : _84024) : (term157 _84024 a s P _32974) = (term151 _84024 a s P _32974).
Proof. exact (eq_refl (term157 _84024 a s P _32974)). Qed.
Lemma lem3208325 {_84024 : Type'} (_32974 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term151 _84024 a s P _32974.
Proof. exact (EQ_MP (@lem3208324 _84024 a s P _32974) (@lem3208323 _84024 _32974 a s P x h1)). Qed.
Lemma lem3208326 {_84024 : Type'} (_32975 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term157 _84024 a s P _32975.
Proof. exact (@lem3208308 _84024 a s P x h1 _32975). Qed.
Lemma lem3208327 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (_32975 : _84024) : (term157 _84024 a s P _32975) = (term151 _84024 a s P _32975).
Proof. exact (eq_refl (term157 _84024 a s P _32975)). Qed.
Lemma lem3208328 {_84024 : Type'} (_32975 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term151 _84024 a s P _32975.
Proof. exact (EQ_MP (@lem3208327 _84024 a s P _32975) (@lem3208326 _84024 _32975 a s P x h1)). Qed.
Lemma lem3208342 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : P x.
Proof. exact (proj2 (@lem3208196 _84024 x a s P h1)). Qed.
Lemma lem3208344 {_84024 : Type'} (x : _84024) (a : _84024) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem3208352 {_84024 : Type'} (_32973 : _84024) (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term62 _84024 s P _32973.
Proof. exact (EQ_MP (@lem3208321 _84024 s P _32973) (@lem3208320 _84024 _32973 x a s P h1)). Qed.
Lemma lem3208356 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) (h1 : @IN _84024 x s) : @IN _84024 x s.
Proof. exact (h1). Qed.
Lemma lem3208358 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3208364 {_84024 : Type'} (_32974 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term158 _84024 a P _32974.
Proof. exact (proj1 (@lem3208325 _84024 _32974 a s P x h1)). Qed.
Lemma lem3208386 {_84024 : Type'} (_32975 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term62 _84024 s P _32975.
Proof. exact (proj2 (@lem3208328 _84024 _32975 a s P x h1)). Qed.
Lemma lem3208414 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term46 _84024 P a.
Proof. exact (proj1 (@lem3208195 _84024 x a s P h1)). Qed.
Lemma lem3208429 {_84024 : Type'} (P : _84024 -> Prop) : (term159 _84024 P) = (term159 _84024 P).
Proof. exact (eq_refl (term159 _84024 P)). Qed.
Lemma lem3208430 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : x = a) : (term160 _84024 P x) = (term160 _84024 P a).
Proof. exact (MK_COMB (@lem3208429 _84024 P) (@lem3208344 _84024 x a h1)). Qed.
Lemma lem3208431 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term160 _84024 P a) = (P a).
Proof. exact (eq_refl (term160 _84024 P a)). Qed.
Lemma lem3208432 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term161 _84024 P x) = (term161 _84024 P x).
Proof. exact (eq_refl (term161 _84024 P x)). Qed.
Lemma lem3208433 {_84024 : Type'} (x : _84024) (P : _84024 -> Prop) (a : _84024) : ((term160 _84024 P x) = (term160 _84024 P a)) = ((term160 _84024 P x) = (P a)).
Proof. exact (MK_COMB (@lem3208432 _84024 P x) (@lem3208431 _84024 P a)). Qed.
Lemma lem3208434 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term160 _84024 P x) = (P x).
Proof. exact (eq_refl (term160 _84024 P x)). Qed.
Lemma lem3208435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3208436 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term161 _84024 P x) = (term162 _84024 P x).
Proof. exact (MK_COMB (@lem3208435) (@lem3208434 _84024 P x)). Qed.
Lemma lem3208437 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem3208438 {_84024 : Type'} (x : _84024) (P : _84024 -> Prop) (a : _84024) : ((term160 _84024 P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem3208436 _84024 P x) (@lem3208437 _84024 P a)). Qed.
Lemma lem3208439 {_84024 : Type'} (x : _84024) (P : _84024 -> Prop) (a : _84024) : ((term160 _84024 P x) = (term160 _84024 P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem3208433 _84024 x P a) (@lem3208438 _84024 x P a)). Qed.
Lemma lem3208440 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem3208439 _84024 x P a) (@lem3208430 _84024 P x a h1)). Qed.
Lemma lem3208443 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3208440 _84024 P x a h2) (@lem3208342 _84024 x a s P h1)). Qed.
Lemma lem3208444 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : term163 _84024 P a.
Proof. exact (fun h0 : term46 _84024 P a => @lem3208443 _84024 s P x a h1 h2). Qed.
Lemma lem3208446 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208447 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term163 _84024 P a) = (P a).
Proof. exact (@lem3208446 (P a)). Qed.
Lemma lem3208448 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem3208447 _84024 P a) (@lem3208444 _84024 s P x a h1 h2)). Qed.
Lemma lem3208451 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3208453 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term46 _84024 P a) = (term165 _84024 P a).
Proof. exact (@lem3208451 (P a)). Qed.
Lemma lem3208456 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term165 _84024 P a.
Proof. exact (EQ_MP (@lem3208453 _84024 P a) (@lem3208414 _84024 x a s P h1)). Qed.
Lemma lem3208459 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : False.
Proof. exact (@lem3208456 _84024 x a s P h1 (@lem3208448 _84024 s P x a h1 h2)). Qed.
Lemma lem3208460 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : term166.
Proof. exact (fun h0 : ~ False => @lem3208459 _84024 s P x a h1 h2). Qed.
Lemma lem3208462 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208463 : term166 = False.
Proof. exact (@lem3208462 False). Qed.
Lemma lem3208466 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) (h1 : @IN _84024 x s) : @IN _84024 x s.
Proof. exact (h1). Qed.
Lemma lem3208467 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) (h1 : @IN _84024 x s) : term167 _84024 x s.
Proof. exact (fun h0 : term153 _84024 x s => @lem3208466 _84024 x s h1). Qed.
Lemma lem3208469 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208470 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) : (term167 _84024 x s) = (@IN _84024 x s).
Proof. exact (@lem3208469 (@IN _84024 x s)). Qed.
Lemma lem3208471 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) (h1 : @IN _84024 x s) : @IN _84024 x s.
Proof. exact (EQ_MP (@lem3208470 _84024 x s) (@lem3208467 _84024 x s h1)). Qed.
Lemma lem3208473 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : P x.
Proof. exact (proj2 (@lem3208196 _84024 x a s P h1)). Qed.
Lemma lem3208474 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term163 _84024 P x.
Proof. exact (fun h0 : term46 _84024 P x => @lem3208473 _84024 x a s P h1). Qed.
Lemma lem3208476 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208477 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term163 _84024 P x) = (P x).
Proof. exact (@lem3208476 (P x)). Qed.
Lemma lem3208478 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : P x.
Proof. exact (EQ_MP (@lem3208477 _84024 P x) (@lem3208474 _84024 x a s P h1)). Qed.
Lemma lem3208480 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3208481 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32973 : _84024) : (term62 _84024 s P _32973) = (term61 _84024 s P _32973).
Proof. exact (@lem3208480 (@IN _84024 _32973 s) (P _32973)). Qed.
Lemma lem3208483 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3208484 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32973 : _84024) : (term61 _84024 s P _32973) = (term170 _84024 s P _32973).
Proof. exact (@lem3208483 (term38 _84024 s P _32973)). Qed.
Lemma lem3208485 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32973 : _84024) : (term62 _84024 s P _32973) = (term170 _84024 s P _32973).
Proof. exact (TRANS (@lem3208481 _84024 s P _32973) (@lem3208484 _84024 s P _32973)). Qed.
Lemma lem3208487 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : term38 _84024 s P x.
Proof. exact (conj (@lem3208471 _84024 x s h2) (@lem3208478 _84024 x a s P h1)). Qed.
Lemma lem3208489 {_84024 : Type'} (_32973 : _84024) (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term170 _84024 s P _32973.
Proof. exact (EQ_MP (@lem3208485 _84024 s P _32973) (@lem3208352 _84024 _32973 x a s P h1)). Qed.
Lemma lem3208490 {_84024 : Type'} (_32973 : _84024) (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term170 _84024 s P _32973.
Proof. exact (@lem3208489 _84024 _32973 x a s P h1). Qed.
Lemma lem3208491 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : term170 _84024 s P x.
Proof. exact (@lem3208490 _84024 x x a s P h1). Qed.
Lemma lem3208494 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : False.
Proof. exact (@lem3208491 _84024 x a s P h1 (@lem3208487 _84024 a P x s h1 h2)). Qed.
Lemma lem3208495 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : term166.
Proof. exact (fun h0 : ~ False => @lem3208494 _84024 a P x s h1 h2). Qed.
Lemma lem3208497 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208498 : term166 = False.
Proof. exact (@lem3208497 False). Qed.
Lemma lem3208499 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : False.
Proof. exact (EQ_MP (@lem3208498) (@lem3208495 _84024 a P x s h1 h2)). Qed.
Lemma lem3208536 {_84024 : Type'} (x : _84024) : x = x.
Proof. exact (@lem21386 _84024 x). Qed.
Lemma lem3208537 {_84024 : Type'} (x : _84024) : x = x.
Proof. exact (@lem3208536 _84024 x). Qed.
Lemma lem3208538 {_84024 : Type'} (a : _84024) : a = a.
Proof. exact (@lem3208537 _84024 a). Qed.
Lemma lem3208539 {_84024 : Type'} (a : _84024) : term171 _84024 a.
Proof. exact (fun h0 : term172 _84024 a => @lem3208538 _84024 a). Qed.
Lemma lem3208541 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208542 {_84024 : Type'} (a : _84024) : (term171 _84024 a) = (a = a).
Proof. exact (@lem3208541 (a = a)). Qed.
Lemma lem3208543 {_84024 : Type'} (a : _84024) : a = a.
Proof. exact (EQ_MP (@lem3208542 _84024 a) (@lem3208539 _84024 a)). Qed.
Lemma lem3208545 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem3208546 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : term163 _84024 P a.
Proof. exact (fun h0 : term46 _84024 P a => @lem3208545 _84024 P a h1). Qed.
Lemma lem3208548 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208549 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) : (term163 _84024 P a) = (P a).
Proof. exact (@lem3208548 (P a)). Qed.
Lemma lem3208550 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : P a.
Proof. exact (EQ_MP (@lem3208549 _84024 P a) (@lem3208546 _84024 P a h1)). Qed.
Lemma lem3208552 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3208553 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (_32974 : _84024) : (term158 _84024 a P _32974) = (term173 _84024 a P _32974).
Proof. exact (@lem3208552 (_32974 = a) (P _32974)). Qed.
Lemma lem3208555 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3208556 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (_32974 : _84024) : (term173 _84024 a P _32974) = (term174 _84024 a P _32974).
Proof. exact (@lem3208555 (term175 _84024 a P _32974)). Qed.
Lemma lem3208557 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (_32974 : _84024) : (term158 _84024 a P _32974) = (term174 _84024 a P _32974).
Proof. exact (TRANS (@lem3208553 _84024 a P _32974) (@lem3208556 _84024 a P _32974)). Qed.
Lemma lem3208559 {_84024 : Type'} (P : _84024 -> Prop) (a : _84024) (h1 : P a) : term176 _84024 P a.
Proof. exact (conj (@lem3208543 _84024 a) (@lem3208550 _84024 P a h1)). Qed.
Lemma lem3208561 {_84024 : Type'} (_32974 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term174 _84024 a P _32974.
Proof. exact (EQ_MP (@lem3208557 _84024 a P _32974) (@lem3208364 _84024 _32974 a s P x h1)). Qed.
Lemma lem3208562 {_84024 : Type'} (_32974 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term174 _84024 a P _32974.
Proof. exact (@lem3208561 _84024 _32974 a s P x h1). Qed.
Lemma lem3208563 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term177 _84024 P a.
Proof. exact (@lem3208562 _84024 a a s P x h1). Qed.
Lemma lem3208566 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : False.
Proof. exact (@lem3208563 _84024 a s P x h2 (@lem3208559 _84024 P a h1)). Qed.
Lemma lem3208567 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : term166.
Proof. exact (fun h0 : ~ False => @lem3208566 _84024 a s P x h1 h2). Qed.
Lemma lem3208569 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208570 : term166 = False.
Proof. exact (@lem3208569 False). Qed.
Lemma lem3208571 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : False.
Proof. exact (EQ_MP (@lem3208570) (@lem3208567 _84024 a s P x h1 h2)). Qed.
Lemma lem3208608 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : @IN _84024 x s.
Proof. exact (proj1 (@lem3208206 _84024 s P x h1)). Qed.
Lemma lem3208609 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : term167 _84024 x s.
Proof. exact (fun h0 : term153 _84024 x s => @lem3208608 _84024 s P x h1). Qed.
Lemma lem3208611 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208612 {_84024 : Type'} (x : _84024) (s : _84024 -> Prop) : (term167 _84024 x s) = (@IN _84024 x s).
Proof. exact (@lem3208611 (@IN _84024 x s)). Qed.
Lemma lem3208613 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : @IN _84024 x s.
Proof. exact (EQ_MP (@lem3208612 _84024 x s) (@lem3208609 _84024 s P x h1)). Qed.
Lemma lem3208615 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : P x.
Proof. exact (proj2 (@lem3208206 _84024 s P x h1)). Qed.
Lemma lem3208616 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : term163 _84024 P x.
Proof. exact (fun h0 : term46 _84024 P x => @lem3208615 _84024 s P x h1). Qed.
Lemma lem3208618 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208619 {_84024 : Type'} (P : _84024 -> Prop) (x : _84024) : (term163 _84024 P x) = (P x).
Proof. exact (@lem3208618 (P x)). Qed.
Lemma lem3208620 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : P x.
Proof. exact (EQ_MP (@lem3208619 _84024 P x) (@lem3208616 _84024 s P x h1)). Qed.
Lemma lem3208622 (a : Prop) (b : Prop) : (term168 a b) = (term169 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3208623 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32975 : _84024) : (term62 _84024 s P _32975) = (term61 _84024 s P _32975).
Proof. exact (@lem3208622 (@IN _84024 _32975 s) (P _32975)). Qed.
Lemma lem3208625 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3208626 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32975 : _84024) : (term61 _84024 s P _32975) = (term170 _84024 s P _32975).
Proof. exact (@lem3208625 (term38 _84024 s P _32975)). Qed.
Lemma lem3208627 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (_32975 : _84024) : (term62 _84024 s P _32975) = (term170 _84024 s P _32975).
Proof. exact (TRANS (@lem3208623 _84024 s P _32975) (@lem3208626 _84024 s P _32975)). Qed.
Lemma lem3208629 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term38 _84024 s P x) : term38 _84024 s P x.
Proof. exact (conj (@lem3208613 _84024 s P x h1) (@lem3208620 _84024 s P x h1)). Qed.
Lemma lem3208631 {_84024 : Type'} (_32975 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term170 _84024 s P _32975.
Proof. exact (EQ_MP (@lem3208627 _84024 s P _32975) (@lem3208386 _84024 _32975 a s P x h1)). Qed.
Lemma lem3208632 {_84024 : Type'} (_32975 : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term170 _84024 s P _32975.
Proof. exact (@lem3208631 _84024 _32975 a s P x h1). Qed.
Lemma lem3208633 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : term170 _84024 s P x.
Proof. exact (@lem3208632 _84024 x a s P x h1). Qed.
Lemma lem3208636 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) (h2 : term38 _84024 s P x) : False.
Proof. exact (@lem3208633 _84024 a s P x h1 (@lem3208629 _84024 s P x h2)). Qed.
Lemma lem3208637 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) (h2 : term38 _84024 s P x) : term166.
Proof. exact (fun h0 : ~ False => @lem3208636 _84024 a s P x h1 h2). Qed.
Lemma lem3208639 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3208640 : term166 = False.
Proof. exact (@lem3208639 False). Qed.
Lemma lem3208641 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) (h2 : term38 _84024 s P x) : False.
Proof. exact (EQ_MP (@lem3208640) (@lem3208637 _84024 a s P x h1 h2)). Qed.
Lemma lem3208642 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3208463) (@lem3208460 _84024 s P x a h1 h2)). Qed.
Lemma lem3208643 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem3208571 _84024 a s P x h1 h2) (fun h3 : False => @lem3208358 _84024 P a h1)). Qed.
Lemma lem3208644 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : False.
Proof. exact (EQ_MP (@lem3208643 _84024 a s P x h1 h2) (@lem3208358 _84024 P a h1)). Qed.
Lemma lem3208645 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : (@IN _84024 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _84024 x s => @lem3208499 _84024 a P x s h1 h2) (fun h3 : False => @lem3208356 _84024 x s h2)). Qed.
Lemma lem3208646 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : False.
Proof. exact (EQ_MP (@lem3208645 _84024 a P x s h1 h2) (@lem3208356 _84024 x s h2)). Qed.
Lemma lem3208647 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3208642 _84024 s P x a h1 h2) (fun h3 : False => @lem3208344 _84024 x a h2)). Qed.
Lemma lem3208648 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3208647 _84024 s P x a h1 h2) (@lem3208344 _84024 x a h2)). Qed.
Lemma lem3208649 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem3208644 _84024 a s P x h1 h2) (fun h3 : False => @lem3208285 _84024 P a h1)). Qed.
Lemma lem3208650 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : False.
Proof. exact (EQ_MP (@lem3208649 _84024 a s P x h1 h2) (@lem3208285 _84024 P a h1)). Qed.
Lemma lem3208651 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : (@IN _84024 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _84024 x s => @lem3208646 _84024 a P x s h1 h2) (fun h3 : False => @lem3208258 _84024 x s h2)). Qed.
Lemma lem3208652 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : False.
Proof. exact (EQ_MP (@lem3208651 _84024 a P x s h1 h2) (@lem3208258 _84024 x s h2)). Qed.
Lemma lem3208653 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3208648 _84024 s P x a h1 h2) (fun h3 : False => @lem3208233 _84024 x a h2)). Qed.
Lemma lem3208654 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3208653 _84024 s P x a h1 h2) (@lem3208233 _84024 x a h2)). Qed.
Lemma lem3208655 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem3208650 _84024 a s P x h1 h2) (fun h3 : False => @lem3208285 _84024 P a h1)). Qed.
Lemma lem3208656 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : P a) (h2 : term126 _84024 a s P x) : False.
Proof. exact (EQ_MP (@lem3208655 _84024 a s P x h1 h2) (@lem3208285 _84024 P a h1)). Qed.
Lemma lem3208657 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : (@IN _84024 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _84024 x s => @lem3208652 _84024 a P x s h1 h2) (fun h3 : False => @lem3208258 _84024 x s h2)). Qed.
Lemma lem3208658 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) (x : _84024) (s : _84024 -> Prop) (h1 : term97 _84024 x a s P) (h2 : @IN _84024 x s) : False.
Proof. exact (EQ_MP (@lem3208657 _84024 a P x s h1 h2) (@lem3208258 _84024 x s h2)). Qed.
Lemma lem3208659 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem3208654 _84024 s P x a h1 h2) (fun h3 : False => @lem3208233 _84024 x a h2)). Qed.
Lemma lem3208660 {_84024 : Type'} (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (a : _84024) (h1 : term97 _84024 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem3208659 _84024 s P x a h1 h2) (@lem3208233 _84024 x a h2)). Qed.
Lemma lem3208661 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term126 _84024 a s P x) : False.
Proof. exact (or_elim (@lem3208203 _84024 a s P x h1) (fun h0 : P a => @lem3208656 _84024 a s P x h0 h1) (fun h0 : term38 _84024 s P x => @lem3208641 _84024 a s P x h1 h0)). Qed.
Lemma lem3208662 {_84024 : Type'} (x : _84024) (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term97 _84024 x a s P) : False.
Proof. exact (or_elim (@lem3208200 _84024 x a s P h1) (fun h0 : x = a => @lem3208660 _84024 s P x a h1 h0) (fun h0 : @IN _84024 x s => @lem3208658 _84024 a P x s h1 h0)). Qed.
Lemma lem3208663 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term147 _84024 a s P x) : False.
Proof. exact (or_elim (@lem3208192 _84024 a s P x h1) (fun h0 : term97 _84024 x a s P => @lem3208662 _84024 x a s P h0) (fun h0 : term126 _84024 a s P x => @lem3208661 _84024 a s P x h0)). Qed.
Lemma lem3208664 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term147 _84024 a s P x) : (term147 _84024 a s P x) = False.
Proof. exact (prop_ext (fun h2 : term147 _84024 a s P x => @lem3208663 _84024 a s P x h1) (fun h2 : False => @lem3208192 _84024 a s P x h1)). Qed.
Lemma lem3208665 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (x : _84024) (h1 : term147 _84024 a s P x) : False.
Proof. exact (EQ_MP (@lem3208664 _84024 a s P x h1) (@lem3208192 _84024 a s P x h1)). Qed.
Lemma lem3208666 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term43 _84024 a s P) : False.
Proof. exact (ex_elim (@lem3208091 _84024 a s P h1) (fun x : _84024 => fun h0 : term149 _84024 a s P x => @lem3208665 _84024 a s P x h0)). Qed.
Lemma lem3208667 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term43 _84024 a s P) : (term43 _84024 a s P) = False.
Proof. exact (prop_ext (fun h2 : term43 _84024 a s P => @lem3208666 _84024 a s P h1) (fun h2 : False => @lem3207748 _84024 a s P h1)). Qed.
Lemma lem3208668 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) (h1 : term43 _84024 a s P) : False.
Proof. exact (EQ_MP (@lem3208667 _84024 a s P h1) (@lem3207748 _84024 a s P h1)). Qed.
Lemma lem3208669 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : term42 _84024 a s P.
Proof. exact (fun h0 : term43 _84024 a s P => @lem3208668 _84024 a s P h0). Qed.
Lemma lem3208670 {_84024 : Type'} (a : _84024) (s : _84024 -> Prop) (P : _84024 -> Prop) : (term14 _84024 a s P) = (term17 _84024 a s P).
Proof. exact (EQ_MP (@lem3207747 _84024 a s P) (@lem3208669 _84024 a s P)). Qed.
Lemma lem3208675 {_84024 : Type'} (a : _84024) (P : _84024 -> Prop) : term21 _84024 a P.
Proof. exact (fun s : _84024 -> Prop => @lem3208670 _84024 a s P). Qed.
Lemma lem3208680 {_84024 : Type'} (P : _84024 -> Prop) : term25 _84024 P.
Proof. exact (fun a : _84024 => @lem3208675 _84024 a P). Qed.
Lemma lem3208685 {_84024 : Type'} : term29 _84024.
Proof. exact (fun P : _84024 -> Prop => @lem3208680 _84024 P). Qed.
Lemma lem3208686 {_84024 : Type'} : term31 _84024.
Proof. exact (EQ_MP (@lem3207743 _84024) (@lem3208685 _84024)). Qed.
Lemma lem3208688 {_84024 : Type'} : term31 _84024.
Proof. exact (@lem3207570 _84024 (@lem3208686 _84024)). Qed.
Lemma lem3208689 {_84024 : Type'} (h1 : term32 _84024) : False.
Proof. exact (@lem3208688 _84024 (@lem3207554 _84024 h1)). Qed.
Lemma lem3208690 {_84024 : Type'} (h1 : term32 _84024) : (term32 _84024) = False.
Proof. exact (prop_ext (fun h2 : term32 _84024 => @lem3208689 _84024 h1) (fun h2 : False => @lem3207554 _84024 h1)). Qed.
Lemma lem3208691 {_84024 : Type'} (h1 : term32 _84024) : False.
Proof. exact (EQ_MP (@lem3208690 _84024 h1) (@lem3207554 _84024 h1)). Qed.
Lemma lem3208692 {_84024 : Type'} : term31 _84024.
Proof. exact (fun h0 : term32 _84024 => @lem3208691 _84024 h0). Qed.
Lemma lem3208693 {_84024 : Type'} : term29 _84024.
Proof. exact (EQ_MP (@lem3207553 _84024) (@lem3208692 _84024)). Qed.
Lemma lem3208694 {_84024 : Type'} : term28 _84024.
Proof. exact (EQ_MP (@lem3207549 _84024) (@lem3208693 _84024)). Qed.
