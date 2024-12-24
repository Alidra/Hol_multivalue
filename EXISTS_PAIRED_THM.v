Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_PAIRED_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import ETA_AX_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem55508 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem55509 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem55510 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem55509 A B t) (@lem55508 A B t)). Qed.
Lemma lem55521 {A : Type'} (t : A -> Prop) : (term2 A t) = t.
Proof. exact (@lem55510 A Prop t). Qed.
Lemma lem55522 {A : Type'} (P : A -> Prop) : (term2 A P) = P.
Proof. exact (@lem55521 A P). Qed.
Lemma lem55523 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem55524 {A : Type'} (P : A -> Prop) : (term3 A P) = (ex P).
Proof. exact (MK_COMB (@lem55523 A) (@lem55522 A P)). Qed.
Lemma lem55525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem55526 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem55525) (@lem55524 A P)). Qed.
Lemma lem55527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55528 {A : Type'} (P : A -> Prop) : (term6 A P) = (term7 A P).
Proof. exact (MK_COMB (@lem55527) (@lem55526 A P)). Qed.
Lemma lem55533 {A : Type'} (P : A -> Prop) : (term8 A P) = (term8 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem55534 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term8 A P)) = ((term5 A P) = (term8 A P)).
Proof. exact (MK_COMB (@lem55528 A P) (@lem55533 A P)). Qed.
Lemma lem55537 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem55534 A P)). Qed.
Lemma lem55538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem55539 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem55538 A) (@lem55537 A)). Qed.
Lemma lem55544 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem55539 A) (@lem10660 A)). Qed.
Lemma lem55545 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term13 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem55546 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term13 _5106 _5107 P) = ((term14 _5106 _5107 P) = (term15 _5106 _5107 P)).
Proof. exact (eq_refl (term13 _5106 _5107 P)). Qed.
Lemma lem55548 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (@lem55544 A P). Qed.
Lemma lem55549 {A : Type'} (P : A -> Prop) : (term16 A P) = ((term5 A P) = (term8 A P)).
Proof. exact (eq_refl (term16 A P)). Qed.
Lemma lem55561 (p : Prop) : term17 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem55562 (p : Prop) : (term17 p) = (term18 p).
Proof. exact (eq_refl (term17 p)). Qed.
Lemma lem55563 (p : Prop) : term18 p.
Proof. exact (EQ_MP (@lem55562 p) (@lem55561 p)). Qed.
Lemma lem55564 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem55565 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem55576 (q : Prop) : (term19 q) = (term19 q).
Proof. exact (eq_refl (term19 q)). Qed.
Lemma lem55577 (q : Prop) (p : Prop) (h1 : p = True) : (term20 q p) = (term21 q).
Proof. exact (MK_COMB (@lem55576 q) (@lem55564 p h1)). Qed.
Lemma lem55578 (q : Prop) : (term21 q) = (term22 q).
Proof. exact (eq_refl (term21 q)). Qed.
Lemma lem55579 (q : Prop) (p : Prop) : (term23 q p) = (term23 q p).
Proof. exact (eq_refl (term23 q p)). Qed.
Lemma lem55580 (p : Prop) (q : Prop) : ((term20 q p) = (term21 q)) = ((term20 q p) = (term22 q)).
Proof. exact (MK_COMB (@lem55579 q p) (@lem55578 q)). Qed.
Lemma lem55581 (p : Prop) (q : Prop) : (term20 q p) = (term24 p q).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem55582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55583 (p : Prop) (q : Prop) : (term23 q p) = (term25 p q).
Proof. exact (MK_COMB (@lem55582) (@lem55581 p q)). Qed.
Lemma lem55584 (q : Prop) : (term22 q) = (term22 q).
Proof. exact (eq_refl (term22 q)). Qed.
Lemma lem55585 (p : Prop) (q : Prop) : ((term20 q p) = (term22 q)) = ((term24 p q) = (term22 q)).
Proof. exact (MK_COMB (@lem55583 p q) (@lem55584 q)). Qed.
Lemma lem55586 (p : Prop) (q : Prop) : ((term20 q p) = (term21 q)) = ((term24 p q) = (term22 q)).
Proof. exact (TRANS (@lem55580 p q) (@lem55585 p q)). Qed.
Lemma lem55587 (q : Prop) (p : Prop) (h1 : p = True) : (term24 p q) = (term22 q).
Proof. exact (EQ_MP (@lem55586 p q) (@lem55577 q p h1)). Qed.
Lemma lem55588 (q : Prop) (p : Prop) (h1 : p = True) : (term22 q) = (term24 p q).
Proof. exact (SYM (@lem55587 q p h1)). Qed.
Lemma lem55589 (q : Prop) : (term19 q) = (term19 q).
Proof. exact (eq_refl (term19 q)). Qed.
Lemma lem55590 (q : Prop) (p : Prop) (h1 : p = False) : (term20 q p) = (term26 q).
Proof. exact (MK_COMB (@lem55589 q) (@lem55565 p h1)). Qed.
Lemma lem55591 (q : Prop) : (term26 q) = (term27 q).
Proof. exact (eq_refl (term26 q)). Qed.
Lemma lem55592 (q : Prop) (p : Prop) : (term23 q p) = (term23 q p).
Proof. exact (eq_refl (term23 q p)). Qed.
Lemma lem55593 (p : Prop) (q : Prop) : ((term20 q p) = (term26 q)) = ((term20 q p) = (term27 q)).
Proof. exact (MK_COMB (@lem55592 q p) (@lem55591 q)). Qed.
Lemma lem55594 (p : Prop) (q : Prop) : (term20 q p) = (term24 p q).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem55595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55596 (p : Prop) (q : Prop) : (term23 q p) = (term25 p q).
Proof. exact (MK_COMB (@lem55595) (@lem55594 p q)). Qed.
Lemma lem55597 (q : Prop) : (term27 q) = (term27 q).
Proof. exact (eq_refl (term27 q)). Qed.
Lemma lem55598 (p : Prop) (q : Prop) : ((term20 q p) = (term27 q)) = ((term24 p q) = (term27 q)).
Proof. exact (MK_COMB (@lem55596 p q) (@lem55597 q)). Qed.
Lemma lem55599 (p : Prop) (q : Prop) : ((term20 q p) = (term26 q)) = ((term24 p q) = (term27 q)).
Proof. exact (TRANS (@lem55593 p q) (@lem55598 p q)). Qed.
Lemma lem55600 (q : Prop) (p : Prop) (h1 : p = False) : (term24 p q) = (term27 q).
Proof. exact (EQ_MP (@lem55599 p q) (@lem55590 q p h1)). Qed.
Lemma lem55601 (q : Prop) (p : Prop) (h1 : p = False) : (term27 q) = (term24 p q).
Proof. exact (SYM (@lem55600 q p h1)). Qed.
Lemma lem55609 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem55610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55611 : term28 = (@eq Prop False).
Proof. exact (MK_COMB (@lem55610) (@lem55609)). Qed.
Lemma lem55612 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem55613 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem55611) (@lem55612 q)). Qed.
Lemma lem55615 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem55616 (q : Prop) : (False = (~ q)) = (term29 q).
Proof. exact (@lem55615 (~ q)). Qed.
Lemma lem55618 (t : Prop) : (term29 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem55619 (q : Prop) : (term29 q) = q.
Proof. exact (@lem55618 q). Qed.
Lemma lem55620 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem55616 q) (@lem55619 q)). Qed.
Lemma lem55621 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem55613 q) (@lem55620 q)). Qed.
Lemma lem55622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem55623 (q : Prop) : (term30 q) = (imp q).
Proof. exact (MK_COMB (@lem55622) (@lem55621 q)). Qed.
Lemma lem55625 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem55626 (q : Prop) : (True = q) = q.
Proof. exact (@lem55625 q). Qed.
Lemma lem55627 (q : Prop) : (term22 q) = (q -> q).
Proof. exact (MK_COMB (@lem55623 q) (@lem55626 q)). Qed.
Lemma lem55629 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem55630 (q : Prop) : (q -> q) = True.
Proof. exact (@lem55629 q). Qed.
Lemma lem55631 (q : Prop) : (term22 q) = True.
Proof. exact (TRANS (@lem55627 q) (@lem55630 q)). Qed.
Lemma lem55632 (q : Prop) : True = (term22 q).
Proof. exact (SYM (@lem55631 q)). Qed.
Lemma lem55633 (q : Prop) : term22 q.
Proof. exact (EQ_MP (@lem55632 q) (@lem0)). Qed.
Lemma lem55641 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem55642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55643 : term31 = (@eq Prop True).
Proof. exact (MK_COMB (@lem55642) (@lem55641)). Qed.
Lemma lem55644 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem55645 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem55643) (@lem55644 q)). Qed.
Lemma lem55647 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem55648 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem55647 (~ q)). Qed.
Lemma lem55649 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem55645 q) (@lem55648 q)). Qed.
Lemma lem55650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem55651 (q : Prop) : (term32 q) = (term33 q).
Proof. exact (MK_COMB (@lem55650) (@lem55649 q)). Qed.
Lemma lem55653 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem55654 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem55653 q). Qed.
Lemma lem55655 (q : Prop) : (term27 q) = (term34 q).
Proof. exact (MK_COMB (@lem55651 q) (@lem55654 q)). Qed.
Lemma lem55657 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem55658 (q : Prop) : (term34 q) = True.
Proof. exact (@lem55657 (~ q)). Qed.
Lemma lem55659 (q : Prop) : (term27 q) = True.
Proof. exact (TRANS (@lem55655 q) (@lem55658 q)). Qed.
Lemma lem55660 (q : Prop) : True = (term27 q).
Proof. exact (SYM (@lem55659 q)). Qed.
Lemma lem55661 (q : Prop) : term27 q.
Proof. exact (EQ_MP (@lem55660 q) (@lem0)). Qed.
Lemma lem55662 (q : Prop) (p : Prop) (h1 : p = False) : term24 p q.
Proof. exact (EQ_MP (@lem55601 q p h1) (@lem55661 q)). Qed.
Lemma lem55663 (q : Prop) (p : Prop) (h1 : p = True) : term24 p q.
Proof. exact (EQ_MP (@lem55588 q p h1) (@lem55633 q)). Qed.
Lemma lem55666 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (or_elim (@lem55563 p) (fun h0 : p = True => @lem55663 q p h0) (fun h0 : p = False => @lem55662 q p h0)). Qed.
Lemma lem55667 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (h1). Qed.
Lemma lem55668 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : (~ p) = (~ q).
Proof. exact (h1). Qed.
Lemma lem55669 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term24 p q) : p = q.
Proof. exact (@lem55667 p q h2 (@lem55668 p q h1)). Qed.
Lemma lem55670 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : term35 p q.
Proof. exact (fun h0 : term24 p q => @lem55669 p q h1 h0). Qed.
Lemma lem55671 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (h1). Qed.
Lemma lem55672 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term24 p q) : p = q.
Proof. exact (@lem55670 p q h1 (@lem55671 p q h2)). Qed.
Lemma lem55673 (p : Prop) (q : Prop) (h1 : term24 p q) : term24 p q.
Proof. exact (fun h0 : (~ p) = (~ q) => @lem55672 p q h0 h1). Qed.
Lemma lem55674 (p : Prop) (q : Prop) : term36 p q.
Proof. exact (fun h0 : term24 p q => @lem55673 p q h0). Qed.
Lemma lem55677 (p : Prop) (q : Prop) : term24 p q.
Proof. exact (@lem55674 p q (@lem55666 p q)). Qed.
Lemma lem55678 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term37 _5769 _5770 P.
Proof. exact (@lem55677 (term38 _5769 _5770 P) (term39 _5769 _5770 P)). Qed.
Lemma lem55682 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem55549 A P) (@lem55548 A P)). Qed.
Lemma lem55683 {_5769 _5770 : Type'} (P : type1223 _5769 _5770) : (term40 _5769 _5770 P) = (term41 _5769 _5770 P).
Proof. exact (@lem55682 (prod _5770 _5769) P). Qed.
Lemma lem55684 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term42 _5769 _5770 P) = (term43 _5769 _5770 P).
Proof. exact (@lem55683 _5769 _5770 (term44 _5769 _5770 P)). Qed.
Lemma lem55690 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem55546 _5106 _5107 P) (@lem55545 _5106 _5107 P)). Qed.
Lemma lem55691 {_5769 _5770 : Type'} (P : type1223 _5769 _5770) : (term14 _5769 _5770 P) = (term15 _5769 _5770 P).
Proof. exact (@lem55690 _5769 _5770 P). Qed.
Lemma lem55692 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term45 _5769 _5770 P) = (term46 _5769 _5770 P).
Proof. exact (@lem55691 _5769 _5770 (term47 _5769 _5770 P)). Qed.
Lemma lem55693 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : prod _5770 _5769) : (term48 _5769 _5770 P x) = (term49 _5769 _5770 P x).
Proof. exact (eq_refl (term48 _5769 _5770 P x)). Qed.
Lemma lem55694 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term50 _5769 _5770 P) = (term47 _5769 _5770 P).
Proof. exact (fun_ext (fun x : prod _5770 _5769 => @lem55693 _5769 _5770 P x)). Qed.
Lemma lem55695 {_5769 _5770 : Type'} : (@all (prod _5770 _5769)) = (@all (prod _5770 _5769)).
Proof. exact (eq_refl (@all (prod _5770 _5769))). Qed.
Lemma lem55696 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term45 _5769 _5770 P) = (term43 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55695 _5769 _5770) (@lem55694 _5769 _5770 P)). Qed.
Lemma lem55697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55698 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term51 _5769 _5770 P) = (term52 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55697) (@lem55696 _5769 _5770 P)). Qed.
Lemma lem55699 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) (p2 : _5769) : (term53 _5769 _5770 P p1 p2) = (term54 _5769 _5770 P p1 p2).
Proof. exact (eq_refl (term53 _5769 _5770 P p1 p2)). Qed.
Lemma lem55700 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) : (term55 _5769 _5770 P p1) = (term56 _5769 _5770 P p1).
Proof. exact (fun_ext (fun p2 : _5769 => @lem55699 _5769 _5770 P p1 p2)). Qed.
Lemma lem55701 {_5769 : Type'} : (@all _5769) = (@all _5769).
Proof. exact (eq_refl (@all _5769)). Qed.
Lemma lem55702 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) : (term57 _5769 _5770 P p1) = (term58 _5769 _5770 P p1).
Proof. exact (MK_COMB (@lem55701 _5769) (@lem55700 _5769 _5770 P p1)). Qed.
Lemma lem55703 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term59 _5769 _5770 P) = (term60 _5769 _5770 P).
Proof. exact (fun_ext (fun p1 : _5770 => @lem55702 _5769 _5770 P p1)). Qed.
Lemma lem55704 {_5770 : Type'} : (@all _5770) = (@all _5770).
Proof. exact (eq_refl (@all _5770)). Qed.
Lemma lem55705 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term46 _5769 _5770 P) = (term61 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55704 _5770) (@lem55703 _5769 _5770 P)). Qed.
Lemma lem55706 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term45 _5769 _5770 P) = (term46 _5769 _5770 P)) = ((term43 _5769 _5770 P) = (term61 _5769 _5770 P)).
Proof. exact (MK_COMB (@lem55698 _5769 _5770 P) (@lem55705 _5769 _5770 P)). Qed.
Lemma lem55707 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term43 _5769 _5770 P) = (term61 _5769 _5770 P).
Proof. exact (EQ_MP (@lem55706 _5769 _5770 P) (@lem55692 _5769 _5770 P)). Qed.
Lemma lem55714 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term42 _5769 _5770 P) = (term61 _5769 _5770 P).
Proof. exact (TRANS (@lem55684 _5769 _5770 P) (@lem55707 _5769 _5770 P)). Qed.
Lemma lem55721 {_5769 _5770 : Type'} (a0 : _5770) (a1 : _5769) : a0 = (term62 _5769 _5770 a0 a1).
Proof. exact (@lem51128 _5770 _5769 a0 a1). Qed.
Lemma lem55722 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : x = (term62 _5769 _5770 x y).
Proof. exact (@lem55721 _5769 _5770 x y). Qed.
Lemma lem55723 {_5769 _5770 : Type'} (a0 : _5770) (a1 : _5769) : a1 = (term63 _5769 _5770 a0 a1).
Proof. exact (@lem51159 _5770 _5769 a0 a1). Qed.
Lemma lem55724 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : y = (term63 _5769 _5770 x y).
Proof. exact (@lem55723 _5769 _5770 x y). Qed.
Lemma lem55725 {_5770 : Type'} (x : _5770) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55726 {_5770 : Type'} : (term64 _5770) = (term64 _5770).
Proof. exact (eq_refl (term64 _5770)). Qed.
Lemma lem55727 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term65 _5770 x) = (term66 _5769 _5770 x y).
Proof. exact (MK_COMB (@lem55726 _5770) (@lem55722 _5769 _5770 x y)). Qed.
Lemma lem55728 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term66 _5769 _5770 x y) = (term62 _5769 _5770 x y).
Proof. exact (eq_refl (term66 _5769 _5770 x y)). Qed.
Lemma lem55729 {_5770 : Type'} (x : _5770) : (term67 _5770 x) = (term67 _5770 x).
Proof. exact (eq_refl (term67 _5770 x)). Qed.
Lemma lem55730 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5770 x) = (term66 _5769 _5770 x y)) = ((term65 _5770 x) = (term62 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55729 _5770 x) (@lem55728 _5769 _5770 x y)). Qed.
Lemma lem55731 {_5770 : Type'} (x : _5770) : (term65 _5770 x) = x.
Proof. exact (eq_refl (term65 _5770 x)). Qed.
Lemma lem55732 {_5770 : Type'} : (@eq _5770) = (@eq _5770).
Proof. exact (eq_refl (@eq _5770)). Qed.
Lemma lem55733 {_5770 : Type'} (x : _5770) : (term67 _5770 x) = (@eq _5770 x).
Proof. exact (MK_COMB (@lem55732 _5770) (@lem55731 _5770 x)). Qed.
Lemma lem55734 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term62 _5769 _5770 x y) = (term62 _5769 _5770 x y).
Proof. exact (eq_refl (term62 _5769 _5770 x y)). Qed.
Lemma lem55735 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5770 x) = (term62 _5769 _5770 x y)) = (x = (term62 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55733 _5770 x) (@lem55734 _5769 _5770 x y)). Qed.
Lemma lem55736 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5770 x) = (term66 _5769 _5770 x y)) = (x = (term62 _5769 _5770 x y)).
Proof. exact (TRANS (@lem55730 _5769 _5770 x y) (@lem55735 _5769 _5770 x y)). Qed.
Lemma lem55737 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : x = (term62 _5769 _5770 x y).
Proof. exact (EQ_MP (@lem55736 _5769 _5770 x y) (@lem55727 _5769 _5770 x y)). Qed.
Lemma lem55738 {_5770 : Type'} (x : _5770) : (@eq _5770 x) = (@eq _5770 x).
Proof. exact (eq_refl (@eq _5770 x)). Qed.
Lemma lem55739 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (x = x) = (x = (term62 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55738 _5770 x) (@lem55737 _5769 _5770 x y)). Qed.
Lemma lem55740 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : x = (term62 _5769 _5770 x y).
Proof. exact (EQ_MP (@lem55739 _5769 _5770 x y) (@lem55725 _5770 x)). Qed.
Lemma lem55741 {_5769 : Type'} (y : _5769) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem55742 {_5769 : Type'} : (term64 _5769) = (term64 _5769).
Proof. exact (eq_refl (term64 _5769)). Qed.
Lemma lem55743 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term65 _5769 y) = (term68 _5769 _5770 x y).
Proof. exact (MK_COMB (@lem55742 _5769) (@lem55724 _5769 _5770 x y)). Qed.
Lemma lem55744 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term68 _5769 _5770 x y) = (term63 _5769 _5770 x y).
Proof. exact (eq_refl (term68 _5769 _5770 x y)). Qed.
Lemma lem55745 {_5769 : Type'} (y : _5769) : (term67 _5769 y) = (term67 _5769 y).
Proof. exact (eq_refl (term67 _5769 y)). Qed.
Lemma lem55746 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5769 y) = (term68 _5769 _5770 x y)) = ((term65 _5769 y) = (term63 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55745 _5769 y) (@lem55744 _5769 _5770 x y)). Qed.
Lemma lem55747 {_5769 : Type'} (y : _5769) : (term65 _5769 y) = y.
Proof. exact (eq_refl (term65 _5769 y)). Qed.
Lemma lem55748 {_5769 : Type'} : (@eq _5769) = (@eq _5769).
Proof. exact (eq_refl (@eq _5769)). Qed.
Lemma lem55749 {_5769 : Type'} (y : _5769) : (term67 _5769 y) = (@eq _5769 y).
Proof. exact (MK_COMB (@lem55748 _5769) (@lem55747 _5769 y)). Qed.
Lemma lem55750 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (term63 _5769 _5770 x y) = (term63 _5769 _5770 x y).
Proof. exact (eq_refl (term63 _5769 _5770 x y)). Qed.
Lemma lem55751 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5769 y) = (term63 _5769 _5770 x y)) = (y = (term63 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55749 _5769 y) (@lem55750 _5769 _5770 x y)). Qed.
Lemma lem55752 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : ((term65 _5769 y) = (term68 _5769 _5770 x y)) = (y = (term63 _5769 _5770 x y)).
Proof. exact (TRANS (@lem55746 _5769 _5770 x y) (@lem55751 _5769 _5770 x y)). Qed.
Lemma lem55753 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : y = (term63 _5769 _5770 x y).
Proof. exact (EQ_MP (@lem55752 _5769 _5770 x y) (@lem55743 _5769 _5770 x y)). Qed.
Lemma lem55754 {_5769 : Type'} (y : _5769) : (@eq _5769 y) = (@eq _5769 y).
Proof. exact (eq_refl (@eq _5769 y)). Qed.
Lemma lem55755 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : (y = y) = (y = (term63 _5769 _5770 x y)).
Proof. exact (MK_COMB (@lem55754 _5769 y) (@lem55753 _5769 _5770 x y)). Qed.
Lemma lem55756 {_5769 _5770 : Type'} (x : _5770) (y : _5769) : y = (term63 _5769 _5770 x y).
Proof. exact (EQ_MP (@lem55755 _5769 _5770 x y) (@lem55741 _5769 y)). Qed.
Lemma lem55757 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term69 _5769 _5770 P) = (term69 _5769 _5770 P).
Proof. exact (eq_refl (term69 _5769 _5770 P)). Qed.
Lemma lem55758 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term70 _5769 _5770 P x) = (term71 _5769 _5770 P x y).
Proof. exact (MK_COMB (@lem55757 _5769 _5770 P) (@lem55740 _5769 _5770 x y)). Qed.
Lemma lem55759 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term71 _5769 _5770 P x y) = (term72 _5769 _5770 P x y).
Proof. exact (eq_refl (term71 _5769 _5770 P x y)). Qed.
Lemma lem55760 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term73 _5769 _5770 P x) = (term73 _5769 _5770 P x).
Proof. exact (eq_refl (term73 _5769 _5770 P x)). Qed.
Lemma lem55761 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term70 _5769 _5770 P x) = (term71 _5769 _5770 P x y)) = ((term70 _5769 _5770 P x) = (term72 _5769 _5770 P x y)).
Proof. exact (MK_COMB (@lem55760 _5769 _5770 P x) (@lem55759 _5769 _5770 P x y)). Qed.
Lemma lem55762 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term70 _5769 _5770 P x) = (term74 _5769 _5770 P x).
Proof. exact (eq_refl (term70 _5769 _5770 P x)). Qed.
Lemma lem55763 {_5769 : Type'} : (@eq (_5769 -> Prop)) = (@eq (_5769 -> Prop)).
Proof. exact (eq_refl (@eq (_5769 -> Prop))). Qed.
Lemma lem55764 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term73 _5769 _5770 P x) = (term75 _5769 _5770 P x).
Proof. exact (MK_COMB (@lem55763 _5769) (@lem55762 _5769 _5770 P x)). Qed.
Lemma lem55765 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term72 _5769 _5770 P x y) = (term72 _5769 _5770 P x y).
Proof. exact (eq_refl (term72 _5769 _5770 P x y)). Qed.
Lemma lem55766 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term70 _5769 _5770 P x) = (term72 _5769 _5770 P x y)) = ((term74 _5769 _5770 P x) = (term72 _5769 _5770 P x y)).
Proof. exact (MK_COMB (@lem55764 _5769 _5770 P x) (@lem55765 _5769 _5770 P x y)). Qed.
Lemma lem55767 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term70 _5769 _5770 P x) = (term71 _5769 _5770 P x y)) = ((term74 _5769 _5770 P x) = (term72 _5769 _5770 P x y)).
Proof. exact (TRANS (@lem55761 _5769 _5770 P x y) (@lem55766 _5769 _5770 P x y)). Qed.
Lemma lem55768 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term74 _5769 _5770 P x) = (term72 _5769 _5770 P x y).
Proof. exact (EQ_MP (@lem55767 _5769 _5770 P x y) (@lem55758 _5769 _5770 P x y)). Qed.
Lemma lem55769 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term76 _5769 _5770 P x y) = (term77 _5769 _5770 P x y).
Proof. exact (MK_COMB (@lem55768 _5769 _5770 P x y) (@lem55756 _5769 _5770 x y)). Qed.
Lemma lem55770 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term77 _5769 _5770 P x y) = (term78 _5769 _5770 P x y).
Proof. exact (eq_refl (term77 _5769 _5770 P x y)). Qed.
Lemma lem55771 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term79 _5769 _5770 P x y) = (term79 _5769 _5770 P x y).
Proof. exact (eq_refl (term79 _5769 _5770 P x y)). Qed.
Lemma lem55772 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term76 _5769 _5770 P x y) = (term77 _5769 _5770 P x y)) = ((term76 _5769 _5770 P x y) = (term78 _5769 _5770 P x y)).
Proof. exact (MK_COMB (@lem55771 _5769 _5770 P x y) (@lem55770 _5769 _5770 P x y)). Qed.
Lemma lem55773 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term76 _5769 _5770 P x y) = (P x y).
Proof. exact (eq_refl (term76 _5769 _5770 P x y)). Qed.
Lemma lem55774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55775 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term79 _5769 _5770 P x y) = (term80 _5769 _5770 P x y).
Proof. exact (MK_COMB (@lem55774) (@lem55773 _5769 _5770 P x y)). Qed.
Lemma lem55776 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term78 _5769 _5770 P x y) = (term78 _5769 _5770 P x y).
Proof. exact (eq_refl (term78 _5769 _5770 P x y)). Qed.
Lemma lem55777 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term76 _5769 _5770 P x y) = (term78 _5769 _5770 P x y)) = ((P x y) = (term78 _5769 _5770 P x y)).
Proof. exact (MK_COMB (@lem55775 _5769 _5770 P x y) (@lem55776 _5769 _5770 P x y)). Qed.
Lemma lem55778 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term76 _5769 _5770 P x y) = (term77 _5769 _5770 P x y)) = ((P x y) = (term78 _5769 _5770 P x y)).
Proof. exact (TRANS (@lem55772 _5769 _5770 P x y) (@lem55777 _5769 _5770 P x y)). Qed.
Lemma lem55779 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (P x y) = (term78 _5769 _5770 P x y).
Proof. exact (EQ_MP (@lem55778 _5769 _5770 P x y) (@lem55769 _5769 _5770 P x y)). Qed.
Lemma lem55780 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term78 _5769 _5770 P x y) = (P x y).
Proof. exact (SYM (@lem55779 _5769 _5770 P x y)). Qed.
Lemma lem55781 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term81 _5769 _5770 P x y) = (term78 _5769 _5770 P x y).
Proof. exact (eq_refl (term81 _5769 _5770 P x y)). Qed.
Lemma lem55782 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term81 _5769 _5770 P x y) = (P x y).
Proof. exact (TRANS (@lem55781 _5769 _5770 P x y) (@lem55780 _5769 _5770 P x y)). Qed.
Lemma lem55783 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : term82 _5769 _5770 P x.
Proof. exact (fun y : _5769 => @lem55782 _5769 _5770 P x y). Qed.
Lemma lem55784 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term83 _5769 _5770 P.
Proof. exact (fun x : _5770 => @lem55783 _5769 _5770 P x). Qed.
Lemma lem55785 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term84 _5769 _5770 P.
Proof. exact (ex_intro (term85 _5769 _5770 P) (term86 _5769 _5770 P) (@lem55784 _5769 _5770 P)). Qed.
Lemma lem55787 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem55788 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem55787 Prop a b). Qed.
Lemma lem55789 {_5769 _5770 : Type'} (_1546 : type1223 _5769 _5770) (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : ((term87 _5769 _5770 _1546 x y) = (P x y)) = (term88 _5769 _5770 _1546 P x y).
Proof. exact (@lem55788 (term87 _5769 _5770 _1546 x y) (P x y)). Qed.
Lemma lem55790 {_5769 _5770 : Type'} (_1546 : type1223 _5769 _5770) (P : type1470 _5769 _5770) (x : _5770) : (term89 _5769 _5770 _1546 P x) = (term90 _5769 _5770 _1546 P x).
Proof. exact (fun_ext (fun y : _5769 => @lem55789 _5769 _5770 _1546 P x y)). Qed.
Lemma lem55791 {_5769 : Type'} : (@all _5769) = (@all _5769).
Proof. exact (eq_refl (@all _5769)). Qed.
Lemma lem55792 {_5769 _5770 : Type'} (_1546 : type1223 _5769 _5770) (P : type1470 _5769 _5770) (x : _5770) : (term91 _5769 _5770 _1546 P x) = (term92 _5769 _5770 _1546 P x).
Proof. exact (MK_COMB (@lem55791 _5769) (@lem55790 _5769 _5770 _1546 P x)). Qed.
Lemma lem55793 {_5769 _5770 : Type'} (_1546 : type1223 _5769 _5770) (P : type1470 _5769 _5770) : (term93 _5769 _5770 _1546 P) = (term94 _5769 _5770 _1546 P).
Proof. exact (fun_ext (fun x : _5770 => @lem55792 _5769 _5770 _1546 P x)). Qed.
Lemma lem55794 {_5770 : Type'} : (@all _5770) = (@all _5770).
Proof. exact (eq_refl (@all _5770)). Qed.
Lemma lem55795 {_5769 _5770 : Type'} (_1546 : type1223 _5769 _5770) (P : type1470 _5769 _5770) : (term95 _5769 _5770 _1546 P) = (term96 _5769 _5770 _1546 P).
Proof. exact (MK_COMB (@lem55794 _5770) (@lem55793 _5769 _5770 _1546 P)). Qed.
Lemma lem55796 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term85 _5769 _5770 P) = (term97 _5769 _5770 P).
Proof. exact (fun_ext (fun _1546 : type1223 _5769 _5770 => @lem55795 _5769 _5770 _1546 P)). Qed.
Lemma lem55797 {_5769 _5770 : Type'} : (@ex ((prod _5770 _5769) -> Prop)) = (@ex ((prod _5770 _5769) -> Prop)).
Proof. exact (eq_refl (@ex ((prod _5770 _5769) -> Prop))). Qed.
Lemma lem55798 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term84 _5769 _5770 P) = (term98 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55797 _5769 _5770) (@lem55796 _5769 _5770 P)). Qed.
Lemma lem55799 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term98 _5769 _5770 P.
Proof. exact (EQ_MP (@lem55798 _5769 _5770 P) (@lem55785 _5769 _5770 P)). Qed.
Lemma lem55801 {_5076 : Type'} (P : _5076 -> Prop) : term99 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem55802 {_5769 _5770 : Type'} (P : type330 _5769 _5770) : term100 _5769 _5770 P.
Proof. exact (@lem55801 (type1223 _5769 _5770) P). Qed.
Lemma lem55803 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term101 _5769 _5770 P.
Proof. exact (@lem55802 _5769 _5770 (term97 _5769 _5770 P)). Qed.
Lemma lem55804 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term102 _5769 _5770 P.
Proof. exact (@lem55803 _5769 _5770 P (@lem55799 _5769 _5770 P)). Qed.
Lemma lem55805 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term102 _5769 _5770 P) = (term103 _5769 _5770 P).
Proof. exact (eq_refl (term102 _5769 _5770 P)). Qed.
Lemma lem55806 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : term103 _5769 _5770 P.
Proof. exact (EQ_MP (@lem55805 _5769 _5770 P) (@lem55804 _5769 _5770 P)). Qed.
Lemma lem55807 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : term104 _5769 _5770 P x.
Proof. exact (@lem55806 _5769 _5770 P x). Qed.
Lemma lem55808 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term104 _5769 _5770 P x) = (term105 _5769 _5770 P x).
Proof. exact (eq_refl (term104 _5769 _5770 P x)). Qed.
Lemma lem55809 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : term105 _5769 _5770 P x.
Proof. exact (EQ_MP (@lem55808 _5769 _5770 P x) (@lem55807 _5769 _5770 P x)). Qed.
Lemma lem55810 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : term106 _5769 _5770 P x y.
Proof. exact (@lem55809 _5769 _5770 P x y). Qed.
Lemma lem55811 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term106 _5769 _5770 P x y) = (term107 _5769 _5770 P x y).
Proof. exact (eq_refl (term106 _5769 _5770 P x y)). Qed.
Lemma lem55812 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : term107 _5769 _5770 P x y.
Proof. exact (EQ_MP (@lem55811 _5769 _5770 P x y) (@lem55810 _5769 _5770 P x y)). Qed.
Lemma lem55814 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem55815 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem55814 Prop a b). Qed.
Lemma lem55816 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term107 _5769 _5770 P x y) = ((term108 _5769 _5770 P x y) = (P x y)).
Proof. exact (@lem55815 (term108 _5769 _5770 P x y) (P x y)). Qed.
Lemma lem55817 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term108 _5769 _5770 P x y) = (P x y).
Proof. exact (EQ_MP (@lem55816 _5769 _5770 P x y) (@lem55812 _5769 _5770 P x y)). Qed.
Lemma lem55818 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term108 _5769 _5770 P x y) = (P x y).
Proof. exact (@lem55817 _5769 _5770 P x y). Qed.
Lemma lem55819 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) (p2 : _5769) : (term108 _5769 _5770 P p1 p2) = (P p1 p2).
Proof. exact (@lem55818 _5769 _5770 P p1 p2). Qed.
Lemma lem55820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem55821 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) (p2 : _5769) : (term54 _5769 _5770 P p1 p2) = (term109 _5769 _5770 P p1 p2).
Proof. exact (MK_COMB (@lem55820) (@lem55819 _5769 _5770 P p1 p2)). Qed.
Lemma lem55822 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) : (term56 _5769 _5770 P p1) = (term110 _5769 _5770 P p1).
Proof. exact (fun_ext (fun p2 : _5769 => @lem55821 _5769 _5770 P p1 p2)). Qed.
Lemma lem55823 {_5769 : Type'} : (@all _5769) = (@all _5769).
Proof. exact (eq_refl (@all _5769)). Qed.
Lemma lem55824 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (p1 : _5770) : (term58 _5769 _5770 P p1) = (term111 _5769 _5770 P p1).
Proof. exact (MK_COMB (@lem55823 _5769) (@lem55822 _5769 _5770 P p1)). Qed.
Lemma lem55831 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term60 _5769 _5770 P) = (term112 _5769 _5770 P).
Proof. exact (fun_ext (fun p1 : _5770 => @lem55824 _5769 _5770 P p1)). Qed.
Lemma lem55832 {_5770 : Type'} : (@all _5770) = (@all _5770).
Proof. exact (eq_refl (@all _5770)). Qed.
Lemma lem55833 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term61 _5769 _5770 P) = (term113 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55832 _5770) (@lem55831 _5769 _5770 P)). Qed.
Lemma lem55840 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term42 _5769 _5770 P) = (term113 _5769 _5770 P).
Proof. exact (TRANS (@lem55714 _5769 _5770 P) (@lem55833 _5769 _5770 P)). Qed.
Lemma lem55841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55842 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term114 _5769 _5770 P) = (term115 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55841) (@lem55840 _5769 _5770 P)). Qed.
Lemma lem55844 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem55549 A P) (@lem55548 A P)). Qed.
Lemma lem55845 {_5770 : Type'} (P : _5770 -> Prop) : (term5 _5770 P) = (term8 _5770 P).
Proof. exact (@lem55844 _5770 P). Qed.
Lemma lem55846 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term116 _5769 _5770 P) = (term117 _5769 _5770 P).
Proof. exact (@lem55845 _5770 (term118 _5769 _5770 P)). Qed.
Lemma lem55854 {A B : Type'} (f : A -> B) (y : A) : (term119 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55855 {_5770 : Type'} (f : _5770 -> Prop) (y : _5770) : (term120 _5770 f y) = (f y).
Proof. exact (@lem55854 _5770 Prop f y). Qed.
Lemma lem55856 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term121 _5769 _5770 P x) = (term122 _5769 _5770 P x).
Proof. exact (@lem55855 _5770 (term118 _5769 _5770 P) x). Qed.
Lemma lem55857 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term122 _5769 _5770 P x) = (term123 _5769 _5770 P x).
Proof. exact (eq_refl (term122 _5769 _5770 P x)). Qed.
Lemma lem55858 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term124 _5769 _5770 P) = (term118 _5769 _5770 P).
Proof. exact (fun_ext (fun x : _5770 => @lem55857 _5769 _5770 P x)). Qed.
Lemma lem55859 {_5770 : Type'} (x : _5770) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55860 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term121 _5769 _5770 P x) = (term122 _5769 _5770 P x).
Proof. exact (MK_COMB (@lem55858 _5769 _5770 P) (@lem55859 _5770 x)). Qed.
Lemma lem55861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55862 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term125 _5769 _5770 P x) = (term126 _5769 _5770 P x).
Proof. exact (MK_COMB (@lem55861) (@lem55860 _5769 _5770 P x)). Qed.
Lemma lem55863 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term122 _5769 _5770 P x) = (term123 _5769 _5770 P x).
Proof. exact (eq_refl (term122 _5769 _5770 P x)). Qed.
Lemma lem55864 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : ((term121 _5769 _5770 P x) = (term122 _5769 _5770 P x)) = ((term122 _5769 _5770 P x) = (term123 _5769 _5770 P x)).
Proof. exact (MK_COMB (@lem55862 _5769 _5770 P x) (@lem55863 _5769 _5770 P x)). Qed.
Lemma lem55865 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term122 _5769 _5770 P x) = (term123 _5769 _5770 P x).
Proof. exact (EQ_MP (@lem55864 _5769 _5770 P x) (@lem55856 _5769 _5770 P x)). Qed.
Lemma lem55870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem55871 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term127 _5769 _5770 P x) = (term128 _5769 _5770 P x).
Proof. exact (MK_COMB (@lem55870) (@lem55865 _5769 _5770 P x)). Qed.
Lemma lem55873 {A : Type'} (P : A -> Prop) : (term5 A P) = (term8 A P).
Proof. exact (EQ_MP (@lem55549 A P) (@lem55548 A P)). Qed.
Lemma lem55874 {_5769 : Type'} (P : _5769 -> Prop) : (term5 _5769 P) = (term8 _5769 P).
Proof. exact (@lem55873 _5769 P). Qed.
Lemma lem55875 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term128 _5769 _5770 P x) = (term129 _5769 _5770 P x).
Proof. exact (@lem55874 _5769 (term74 _5769 _5770 P x)). Qed.
Lemma lem55883 {A B : Type'} (f : A -> B) (y : A) : (term119 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem55884 {_5769 : Type'} (f : _5769 -> Prop) (y : _5769) : (term120 _5769 f y) = (f y).
Proof. exact (@lem55883 _5769 Prop f y). Qed.
Lemma lem55885 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term130 _5769 _5770 P x x') = (term76 _5769 _5770 P x x').
Proof. exact (@lem55884 _5769 (term74 _5769 _5770 P x) x'). Qed.
Lemma lem55886 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (y : _5769) : (term76 _5769 _5770 P x y) = (P x y).
Proof. exact (eq_refl (term76 _5769 _5770 P x y)). Qed.
Lemma lem55887 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term131 _5769 _5770 P x) = (term74 _5769 _5770 P x).
Proof. exact (fun_ext (fun y : _5769 => @lem55886 _5769 _5770 P x y)). Qed.
Lemma lem55888 {_5769 : Type'} (x : _5769) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem55889 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term130 _5769 _5770 P x x') = (term76 _5769 _5770 P x x').
Proof. exact (MK_COMB (@lem55887 _5769 _5770 P x) (@lem55888 _5769 x')). Qed.
Lemma lem55890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55891 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term132 _5769 _5770 P x x') = (term79 _5769 _5770 P x x').
Proof. exact (MK_COMB (@lem55890) (@lem55889 _5769 _5770 P x x')). Qed.
Lemma lem55892 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term76 _5769 _5770 P x x') = (P x x').
Proof. exact (eq_refl (term76 _5769 _5770 P x x')). Qed.
Lemma lem55893 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : ((term130 _5769 _5770 P x x') = (term76 _5769 _5770 P x x')) = ((term76 _5769 _5770 P x x') = (P x x')).
Proof. exact (MK_COMB (@lem55891 _5769 _5770 P x x') (@lem55892 _5769 _5770 P x x')). Qed.
Lemma lem55894 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term76 _5769 _5770 P x x') = (P x x').
Proof. exact (EQ_MP (@lem55893 _5769 _5770 P x x') (@lem55885 _5769 _5770 P x x')). Qed.
Lemma lem55895 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem55896 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) (x' : _5769) : (term133 _5769 _5770 P x x') = (term109 _5769 _5770 P x x').
Proof. exact (MK_COMB (@lem55895) (@lem55894 _5769 _5770 P x x')). Qed.
Lemma lem55897 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term134 _5769 _5770 P x) = (term110 _5769 _5770 P x).
Proof. exact (fun_ext (fun x' : _5769 => @lem55896 _5769 _5770 P x x')). Qed.
Lemma lem55898 {_5769 : Type'} : (@all _5769) = (@all _5769).
Proof. exact (eq_refl (@all _5769)). Qed.
Lemma lem55899 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term129 _5769 _5770 P x) = (term111 _5769 _5770 P x).
Proof. exact (MK_COMB (@lem55898 _5769) (@lem55897 _5769 _5770 P x)). Qed.
Lemma lem55906 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term128 _5769 _5770 P x) = (term111 _5769 _5770 P x).
Proof. exact (TRANS (@lem55875 _5769 _5770 P x) (@lem55899 _5769 _5770 P x)). Qed.
Lemma lem55907 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) (x : _5770) : (term127 _5769 _5770 P x) = (term111 _5769 _5770 P x).
Proof. exact (TRANS (@lem55871 _5769 _5770 P x) (@lem55906 _5769 _5770 P x)). Qed.
Lemma lem55908 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term135 _5769 _5770 P) = (term112 _5769 _5770 P).
Proof. exact (fun_ext (fun x : _5770 => @lem55907 _5769 _5770 P x)). Qed.
Lemma lem55909 {_5770 : Type'} : (@all _5770) = (@all _5770).
Proof. exact (eq_refl (@all _5770)). Qed.
Lemma lem55910 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term117 _5769 _5770 P) = (term113 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55909 _5770) (@lem55908 _5769 _5770 P)). Qed.
Lemma lem55917 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term116 _5769 _5770 P) = (term113 _5769 _5770 P).
Proof. exact (TRANS (@lem55846 _5769 _5770 P) (@lem55910 _5769 _5770 P)). Qed.
Lemma lem55918 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term42 _5769 _5770 P) = (term116 _5769 _5770 P)) = ((term113 _5769 _5770 P) = (term113 _5769 _5770 P)).
Proof. exact (MK_COMB (@lem55842 _5769 _5770 P) (@lem55917 _5769 _5770 P)). Qed.
Lemma lem55920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem55921 (x : Prop) : (x = x) = True.
Proof. exact (@lem55920 Prop x). Qed.
Lemma lem55922 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True.
Proof. exact (@lem55921 (term113 _5769 _5770 P)). Qed.
Lemma lem55925 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term136 _5769 _5770 P) = (term136 _5769 _5770 P).
Proof. exact (eq_refl (term136 _5769 _5770 P)). Qed.
Lemma lem55926 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term136 _5769 _5770 P) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True).
Proof. exact (eq_refl (term136 _5769 _5770 P)). Qed.
Lemma lem55927 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term137 _5769 _5770 P) = (term137 _5769 _5770 P).
Proof. exact (eq_refl (term137 _5769 _5770 P)). Qed.
Lemma lem55928 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term136 _5769 _5770 P) = (term136 _5769 _5770 P)) = ((term136 _5769 _5770 P) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True)).
Proof. exact (MK_COMB (@lem55927 _5769 _5770 P) (@lem55926 _5769 _5770 P)). Qed.
Lemma lem55929 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term136 _5769 _5770 P) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True).
Proof. exact (eq_refl (term136 _5769 _5770 P)). Qed.
Lemma lem55930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem55931 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term137 _5769 _5770 P) = (term138 _5769 _5770 P).
Proof. exact (MK_COMB (@lem55930) (@lem55929 _5769 _5770 P)). Qed.
Lemma lem55932 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True).
Proof. exact (eq_refl (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True)). Qed.
Lemma lem55933 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term136 _5769 _5770 P) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True)) = ((((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True)).
Proof. exact (MK_COMB (@lem55931 _5769 _5770 P) (@lem55932 _5769 _5770 P)). Qed.
Lemma lem55934 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term136 _5769 _5770 P) = (term136 _5769 _5770 P)) = ((((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True)).
Proof. exact (TRANS (@lem55928 _5769 _5770 P) (@lem55933 _5769 _5770 P)). Qed.
Lemma lem55935 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True) = (((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True).
Proof. exact (EQ_MP (@lem55934 _5769 _5770 P) (@lem55925 _5769 _5770 P)). Qed.
Lemma lem55936 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term113 _5769 _5770 P) = (term113 _5769 _5770 P)) = True.
Proof. exact (EQ_MP (@lem55935 _5769 _5770 P) (@lem55922 _5769 _5770 P)). Qed.
Lemma lem55937 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : ((term42 _5769 _5770 P) = (term116 _5769 _5770 P)) = True.
Proof. exact (TRANS (@lem55918 _5769 _5770 P) (@lem55936 _5769 _5770 P)). Qed.
Lemma lem55938 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : True = ((term42 _5769 _5770 P) = (term116 _5769 _5770 P)).
Proof. exact (SYM (@lem55937 _5769 _5770 P)). Qed.
Lemma lem55939 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term42 _5769 _5770 P) = (term116 _5769 _5770 P).
Proof. exact (EQ_MP (@lem55938 _5769 _5770 P) (@lem0)). Qed.
Lemma lem55940 {_5769 _5770 : Type'} (P : type1470 _5769 _5770) : (term38 _5769 _5770 P) = (term39 _5769 _5770 P).
Proof. exact (@lem55678 _5769 _5770 P (@lem55939 _5769 _5770 P)). Qed.
Lemma lem55945 {_5769 _5770 : Type'} : term139 _5769 _5770.
Proof. exact (fun P : type1470 _5769 _5770 => @lem55940 _5769 _5770 P). Qed.
