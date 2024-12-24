Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONO_ALL2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1104043_spec.
Require Import thm1104044_spec.
Require Import thm1104055_spec.
Require Import thm1104056_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1238520 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term0 A B P Q.
Proof. exact (h1). Qed.
Lemma lem1238522 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1238523 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (@lem1238522 A P). Qed.
Lemma lem1238524 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : term2 A B P Q.
Proof. exact (@lem1238523 A (term3 A B P Q)). Qed.
Lemma lem1238525 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term4 A B P Q) = (term5 A B P Q).
Proof. exact (eq_refl (term4 A B P Q)). Qed.
Lemma lem1238526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1238527 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term6 A B P Q) = (term7 A B P Q).
Proof. exact (MK_COMB (@lem1238526) (@lem1238525 A B P Q)). Qed.
Lemma lem1238528 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term8 A B P Q t) = (term9 A B P Q t).
Proof. exact (eq_refl (term8 A B P Q t)). Qed.
Lemma lem1238529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238530 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term10 A B P Q t) = (term11 A B P Q t).
Proof. exact (MK_COMB (@lem1238529) (@lem1238528 A B P Q t)). Qed.
Lemma lem1238531 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h : A) (t : list A) : (term12 A B P Q h t) = (term13 A B P Q h t).
Proof. exact (eq_refl (term12 A B P Q h t)). Qed.
Lemma lem1238532 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h : A) (t : list A) : (term14 A B P Q h t) = (term15 A B P Q h t).
Proof. exact (MK_COMB (@lem1238530 A B P Q t) (@lem1238531 A B P Q h t)). Qed.
Lemma lem1238533 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h : A) : (term16 A B P Q h) = (term17 A B P Q h).
Proof. exact (fun_ext (fun t : list A => @lem1238532 A B P Q h t)). Qed.
Lemma lem1238534 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1238535 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h : A) : (term18 A B P Q h) = (term19 A B P Q h).
Proof. exact (MK_COMB (@lem1238534 A) (@lem1238533 A B P Q h)). Qed.
Lemma lem1238536 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term20 A B P Q) = (term21 A B P Q).
Proof. exact (fun_ext (fun h : A => @lem1238535 A B P Q h)). Qed.
Lemma lem1238537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238538 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term22 A B P Q) = (term23 A B P Q).
Proof. exact (MK_COMB (@lem1238537 A) (@lem1238536 A B P Q)). Qed.
Lemma lem1238539 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term24 A B P Q) = (term25 A B P Q).
Proof. exact (MK_COMB (@lem1238527 A B P Q) (@lem1238538 A B P Q)). Qed.
Lemma lem1238540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238541 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term26 A B P Q) = (term27 A B P Q).
Proof. exact (MK_COMB (@lem1238540) (@lem1238539 A B P Q)). Qed.
Lemma lem1238542 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l : list A) : (term8 A B P Q l) = (term9 A B P Q l).
Proof. exact (eq_refl (term8 A B P Q l)). Qed.
Lemma lem1238543 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term28 A B P Q) = (term3 A B P Q).
Proof. exact (fun_ext (fun l : list A => @lem1238542 A B P Q l)). Qed.
Lemma lem1238544 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1238545 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term29 A B P Q) = (term30 A B P Q).
Proof. exact (MK_COMB (@lem1238544 A) (@lem1238543 A B P Q)). Qed.
Lemma lem1238546 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term2 A B P Q) = (term31 A B P Q).
Proof. exact (MK_COMB (@lem1238541 A B P Q) (@lem1238545 A B P Q)). Qed.
Lemma lem1238547 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : term31 A B P Q.
Proof. exact (EQ_MP (@lem1238546 A B P Q) (@lem1238524 A B P Q)). Qed.
Lemma lem1238548 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term9 A B P Q t.
Proof. exact (h1). Qed.
Lemma lem1238556 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2)). Qed.
Lemma lem1238557 {A B : Type'} (P : type1413 A B) (l2 : list B) : (@ALL2 A B P (@nil A) l2) = (l2 = (@nil B)).
Proof. exact (@lem1238556 A B P l2). Qed.
Lemma lem1238558 {A B : Type'} (P : type1413 A B) (l' : list B) : (@ALL2 A B P (@nil A) l') = (l' = (@nil B)).
Proof. exact (@lem1238557 A B P l'). Qed.
Lemma lem1238561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238562 {A B : Type'} (P : type1413 A B) (l' : list B) : (term32 A B P l') = (term33 B l').
Proof. exact (MK_COMB (@lem1238561) (@lem1238558 A B P l')). Qed.
Lemma lem1238564 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2)). Qed.
Lemma lem1238565 {A B : Type'} (P : type1413 A B) (l2 : list B) : (@ALL2 A B P (@nil A) l2) = (l2 = (@nil B)).
Proof. exact (@lem1238564 A B P l2). Qed.
Lemma lem1238566 {A B : Type'} (Q : type1413 A B) (l' : list B) : (@ALL2 A B Q (@nil A) l') = (l' = (@nil B)).
Proof. exact (@lem1238565 A B Q l'). Qed.
Lemma lem1238569 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l' : list B) : (term34 A B P Q l') = (term35 B l').
Proof. exact (MK_COMB (@lem1238562 A B P l') (@lem1238566 A B Q l')). Qed.
Lemma lem1238573 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1238574 {B : Type'} (l' : list B) : (term35 B l') = True.
Proof. exact (@lem1238573 (l' = (@nil B))). Qed.
Lemma lem1238575 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l' : list B) : (term34 A B P Q l') = True.
Proof. exact (TRANS (@lem1238569 A B P Q l') (@lem1238574 B l')). Qed.
Lemma lem1238576 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term36 A B P Q) = (term37 B).
Proof. exact (fun_ext (fun l' : list B => @lem1238575 A B P Q l')). Qed.
Lemma lem1238577 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1238578 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term5 A B P Q) = (term38 B).
Proof. exact (MK_COMB (@lem1238577 B) (@lem1238576 A B P Q)). Qed.
Lemma lem1238580 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1238581 {B : Type'} (t : Prop) : (term40 B t) = t.
Proof. exact (@lem1238580 (list B) t). Qed.
Lemma lem1238582 {B : Type'} : (term38 B) = True.
Proof. exact (@lem1238581 B True). Qed.
Lemma lem1238583 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term5 A B P Q) = True.
Proof. exact (TRANS (@lem1238578 A B P Q) (@lem1238582 B)). Qed.
Lemma lem1238584 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : True = (term5 A B P Q).
Proof. exact (SYM (@lem1238583 A B P Q)). Qed.
Lemma lem1238585 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : term5 A B P Q.
Proof. exact (EQ_MP (@lem1238584 A B P Q) (@lem0)). Qed.
Lemma lem1238593 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term41 _25409 _25416 P h1' t1 l2) = (term42 _25409 _25416 h1' P t1 l2).
Proof. exact (EQ_MP (@lem1104056 _25409 _25416 h1' P t1 l2) (@lem1104055 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1238594 {A B : Type'} (h1' : A) (P : type1413 A B) (t1 : list A) (l2 : list B) : (term41 A B P h1' t1 l2) = (term42 A B h1' P t1 l2).
Proof. exact (@lem1238593 A B h1' P t1 l2). Qed.
Lemma lem1238595 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) : (term41 A B P h t l') = (term42 A B h P t l').
Proof. exact (@lem1238594 A B h P t l'). Qed.
Lemma lem1238602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238603 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) : (term43 A B P h t l') = (term44 A B h P t l').
Proof. exact (MK_COMB (@lem1238602) (@lem1238595 A B h P t l')). Qed.
Lemma lem1238605 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term41 _25409 _25416 P h1' t1 l2) = (term42 _25409 _25416 h1' P t1 l2).
Proof. exact (EQ_MP (@lem1104056 _25409 _25416 h1' P t1 l2) (@lem1104055 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1238606 {A B : Type'} (h1' : A) (P : type1413 A B) (t1 : list A) (l2 : list B) : (term41 A B P h1' t1 l2) = (term42 A B h1' P t1 l2).
Proof. exact (@lem1238605 A B h1' P t1 l2). Qed.
Lemma lem1238607 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term41 A B Q h t l') = (term42 A B h Q t l').
Proof. exact (@lem1238606 A B h Q t l'). Qed.
Lemma lem1238614 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term45 A B P Q h t l') = (term46 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238603 A B h P t l') (@lem1238607 A B h Q t l')). Qed.
Lemma lem1238617 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) : (term47 A B P Q h t) = (term48 A B P h Q t).
Proof. exact (fun_ext (fun l' : list B => @lem1238614 A B P h Q t l')). Qed.
Lemma lem1238618 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1238619 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) : (term13 A B P Q h t) = (term49 A B P h Q t).
Proof. exact (MK_COMB (@lem1238618 B) (@lem1238617 A B P h Q t)). Qed.
Lemma lem1238624 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h : A) (t : list A) : (term49 A B P h Q t) = (term13 A B P Q h t).
Proof. exact (SYM (@lem1238619 A B P h Q t)). Qed.
Lemma lem1238625 (_474 : Prop) (_475 : Prop) (_476 : Prop -> Prop) (_477 : Prop) : (term50 _476 _475 _474 _477) = (term51 _474 _475 _476 _477).
Proof. exact (@lem13473 Prop _474 _475 _476 _477). Qed.
Lemma lem1238626 {A B : Type'} (_474 : Prop) (_475 : Prop) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (_477 : Prop) : (term52 A B h Q t l' _475 _474 _477) = (term53 A B _474 _475 h Q t l' _477).
Proof. exact (@lem1238625 _474 _475 (term54 A B h Q t l') _477). Qed.
Lemma lem1238627 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) : (term55 A B Q h P t l') = (term56 A B Q h P t l').
Proof. exact (@lem1238626 A B False (l' = (@nil B)) h Q t l' (term57 A B h P t l')). Qed.
Lemma lem1238628 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term58 A B Q h P t l') = (term59 A B P h Q t l').
Proof. exact (eq_refl (term58 A B Q h P t l')). Qed.
Lemma lem1238629 {B : Type'} (l' : list B) : (term60 B l') = (term60 B l').
Proof. exact (eq_refl (term60 B l')). Qed.
Lemma lem1238630 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term61 A B Q h P t l') = (term62 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238629 B l') (@lem1238628 A B P h Q t l')). Qed.
Lemma lem1238631 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term63 A B h Q t l') = (term64 A B h Q t l').
Proof. exact (eq_refl (term63 A B h Q t l')). Qed.
Lemma lem1238632 {B : Type'} (l' : list B) : (term33 B l') = (term33 B l').
Proof. exact (eq_refl (term33 B l')). Qed.
Lemma lem1238633 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term65 A B h Q t l') = (term66 A B h Q t l').
Proof. exact (MK_COMB (@lem1238632 B l') (@lem1238631 A B h Q t l')). Qed.
Lemma lem1238634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1238635 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term67 A B h Q t l') = (term68 A B h Q t l').
Proof. exact (MK_COMB (@lem1238634) (@lem1238633 A B h Q t l')). Qed.
Lemma lem1238636 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term56 A B Q h P t l') = (term69 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238635 A B h Q t l') (@lem1238630 A B P h Q t l')). Qed.
Lemma lem1238637 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term55 A B Q h P t l') = (term46 A B P h Q t l').
Proof. exact (eq_refl (term55 A B Q h P t l')). Qed.
Lemma lem1238638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1238639 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term70 A B Q h P t l') = (term71 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238638) (@lem1238637 A B P h Q t l')). Qed.
Lemma lem1238640 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term55 A B Q h P t l') = (term56 A B Q h P t l')) = ((term46 A B P h Q t l') = (term69 A B P h Q t l')).
Proof. exact (MK_COMB (@lem1238639 A B P h Q t l') (@lem1238636 A B P h Q t l')). Qed.
Lemma lem1238641 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term46 A B P h Q t l') = (term69 A B P h Q t l').
Proof. exact (EQ_MP (@lem1238640 A B P h Q t l') (@lem1238627 A B Q h P t l')). Qed.
Lemma lem1238642 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term69 A B P h Q t l') = (term46 A B P h Q t l').
Proof. exact (SYM (@lem1238641 A B P h Q t l')). Qed.
Lemma lem1238643 {B : Type'} (l' : list B) (h1 : l' = (@nil B)) : l' = (@nil B).
Proof. exact (h1). Qed.
Lemma lem1238644 {B : Type'} (l' : list B) : (l' = (@nil B)) = ((l' = (@nil B)) = True).
Proof. exact (@lem7 (l' = (@nil B))). Qed.
Lemma lem1238645 {B : Type'} (l' : list B) (h1 : l' = (@nil B)) : (l' = (@nil B)) = True.
Proof. exact (EQ_MP (@lem1238644 B l') (@lem1238643 B l' h1)). Qed.
Lemma lem1238646 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term72 A B h Q t l') = (term72 A B h Q t l').
Proof. exact (eq_refl (term72 A B h Q t l')). Qed.
Lemma lem1238647 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : (term73 A B h Q t l') = (term74 A B h Q t l').
Proof. exact (MK_COMB (@lem1238646 A B h Q t l') (@lem1238645 B l' h1)). Qed.
Lemma lem1238648 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term74 A B h Q t l') = (term75 A B h Q t l').
Proof. exact (eq_refl (term74 A B h Q t l')). Qed.
Lemma lem1238649 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term76 A B h Q t l') = (term76 A B h Q t l').
Proof. exact (eq_refl (term76 A B h Q t l')). Qed.
Lemma lem1238650 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term73 A B h Q t l') = (term74 A B h Q t l')) = ((term73 A B h Q t l') = (term75 A B h Q t l')).
Proof. exact (MK_COMB (@lem1238649 A B h Q t l') (@lem1238648 A B h Q t l')). Qed.
Lemma lem1238651 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term73 A B h Q t l') = (term64 A B h Q t l').
Proof. exact (eq_refl (term73 A B h Q t l')). Qed.
Lemma lem1238652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1238653 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term76 A B h Q t l') = (term77 A B h Q t l').
Proof. exact (MK_COMB (@lem1238652) (@lem1238651 A B h Q t l')). Qed.
Lemma lem1238654 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term75 A B h Q t l') = (term75 A B h Q t l').
Proof. exact (eq_refl (term75 A B h Q t l')). Qed.
Lemma lem1238655 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term73 A B h Q t l') = (term75 A B h Q t l')) = ((term64 A B h Q t l') = (term75 A B h Q t l')).
Proof. exact (MK_COMB (@lem1238653 A B h Q t l') (@lem1238654 A B h Q t l')). Qed.
Lemma lem1238656 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term73 A B h Q t l') = (term74 A B h Q t l')) = ((term64 A B h Q t l') = (term75 A B h Q t l')).
Proof. exact (TRANS (@lem1238650 A B h Q t l') (@lem1238655 A B h Q t l')). Qed.
Lemma lem1238657 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : (term64 A B h Q t l') = (term75 A B h Q t l').
Proof. exact (EQ_MP (@lem1238656 A B h Q t l') (@lem1238647 A B h Q t l' h1)). Qed.
Lemma lem1238658 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : (term75 A B h Q t l') = (term64 A B h Q t l').
Proof. exact (SYM (@lem1238657 A B h Q t l' h1)). Qed.
Lemma lem1238659 {B : Type'} (l' : list B) (h1 : term78 B l') : term78 B l'.
Proof. exact (h1). Qed.
Lemma lem1238660 {B : Type'} (l' : list B) : term79 B l'.
Proof. exact (@lem82 (l' = (@nil B))). Qed.
Lemma lem1238661 {B : Type'} (l' : list B) (h1 : term78 B l') : (l' = (@nil B)) = False.
Proof. exact (@lem1238660 B l' (@lem1238659 B l' h1)). Qed.
Lemma lem1238662 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term80 A B P h Q t l') = (term80 A B P h Q t l').
Proof. exact (eq_refl (term80 A B P h Q t l')). Qed.
Lemma lem1238663 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term78 B l') : (term81 A B P h Q t l') = (term82 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238662 A B P h Q t l') (@lem1238661 B l' h1)). Qed.
Lemma lem1238664 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term82 A B P h Q t l') = (term83 A B P h Q t l').
Proof. exact (eq_refl (term82 A B P h Q t l')). Qed.
Lemma lem1238665 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term84 A B P h Q t l') = (term84 A B P h Q t l').
Proof. exact (eq_refl (term84 A B P h Q t l')). Qed.
Lemma lem1238666 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term81 A B P h Q t l') = (term82 A B P h Q t l')) = ((term81 A B P h Q t l') = (term83 A B P h Q t l')).
Proof. exact (MK_COMB (@lem1238665 A B P h Q t l') (@lem1238664 A B P h Q t l')). Qed.
Lemma lem1238667 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term81 A B P h Q t l') = (term59 A B P h Q t l').
Proof. exact (eq_refl (term81 A B P h Q t l')). Qed.
Lemma lem1238668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1238669 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term84 A B P h Q t l') = (term85 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238668) (@lem1238667 A B P h Q t l')). Qed.
Lemma lem1238670 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term83 A B P h Q t l') = (term83 A B P h Q t l').
Proof. exact (eq_refl (term83 A B P h Q t l')). Qed.
Lemma lem1238671 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term81 A B P h Q t l') = (term83 A B P h Q t l')) = ((term59 A B P h Q t l') = (term83 A B P h Q t l')).
Proof. exact (MK_COMB (@lem1238669 A B P h Q t l') (@lem1238670 A B P h Q t l')). Qed.
Lemma lem1238672 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : ((term81 A B P h Q t l') = (term82 A B P h Q t l')) = ((term59 A B P h Q t l') = (term83 A B P h Q t l')).
Proof. exact (TRANS (@lem1238666 A B P h Q t l') (@lem1238671 A B P h Q t l')). Qed.
Lemma lem1238673 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term78 B l') : (term59 A B P h Q t l') = (term83 A B P h Q t l').
Proof. exact (EQ_MP (@lem1238672 A B P h Q t l') (@lem1238663 A B P h Q t l' h1)). Qed.
Lemma lem1238674 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term78 B l') : (term83 A B P h Q t l') = (term59 A B P h Q t l').
Proof. exact (SYM (@lem1238673 A B P h Q t l' h1)). Qed.
Lemma lem1238676 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1238677 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term75 A B h Q t l') = True.
Proof. exact (@lem1238676 (term86 A B h Q t l')). Qed.
Lemma lem1238678 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : True = (term75 A B h Q t l').
Proof. exact (SYM (@lem1238677 A B h Q t l')). Qed.
Lemma lem1238679 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term75 A B h Q t l'.
Proof. exact (EQ_MP (@lem1238678 A B h Q t l') (@lem0)). Qed.
Lemma lem1238685 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1238686 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem1238685 Prop t1 t2). Qed.
Lemma lem1238687 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term87 A B h Q t l') = (term57 A B h Q t l').
Proof. exact (@lem1238686 False (term57 A B h Q t l')). Qed.
Lemma lem1238690 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) : (term88 A B h P t l') = (term88 A B h P t l').
Proof. exact (eq_refl (term88 A B h P t l')). Qed.
Lemma lem1238691 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term83 A B P h Q t l') = (term89 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238690 A B h P t l') (@lem1238687 A B h Q t l')). Qed.
Lemma lem1238694 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term89 A B P h Q t l') = (term83 A B P h Q t l').
Proof. exact (SYM (@lem1238691 A B P h Q t l')). Qed.
Lemma lem1238696 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1238697 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term89 A B P h Q t l') = (term91 A B P h Q t l').
Proof. exact (@lem1238696 (term89 A B P h Q t l')). Qed.
Lemma lem1238698 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term91 A B P h Q t l') = (term89 A B P h Q t l').
Proof. exact (SYM (@lem1238697 A B P h Q t l')). Qed.
Lemma lem1238699 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term92 A B P h Q t l') : term92 A B P h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238702 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term93 A B P h Q t l') : term93 A B P h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238703 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term94 A B P h Q t l'.
Proof. exact (fun h0 : term93 A B P h Q t l' => @lem1238702 A B P h Q t l' h0). Qed.
Lemma lem1238704 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term94 A B P h Q t l') : term94 A B P h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238705 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term93 A B P h Q t l') : term93 A B P h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238706 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term93 A B P h Q t l') (h2 : term94 A B P h Q t l') : term93 A B P h Q t l'.
Proof. exact (@lem1238704 A B P h Q t l' h2 (@lem1238705 A B P h Q t l' h1)). Qed.
Lemma lem1238707 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term93 A B P h Q t l') : term95 A B P h Q t l'.
Proof. exact (fun h0 : term94 A B P h Q t l' => @lem1238706 A B P h Q t l' h1 h0). Qed.
Lemma lem1238708 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term94 A B P h Q t l') : term94 A B P h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238709 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term93 A B P h Q t l') (h2 : term94 A B P h Q t l') : term93 A B P h Q t l'.
Proof. exact (@lem1238707 A B P h Q t l' h1 (@lem1238708 A B P h Q t l' h2)). Qed.
Lemma lem1238710 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term94 A B P h Q t l') : term94 A B P h Q t l'.
Proof. exact (fun h0 : term93 A B P h Q t l' => @lem1238709 A B P h Q t l' h0 h1). Qed.
Lemma lem1238711 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term96 A B P h Q t l'.
Proof. exact (fun h0 : term94 A B P h Q t l' => @lem1238710 A B P h Q t l' h0). Qed.
Lemma lem1238714 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term94 A B P h Q t l'.
Proof. exact (@lem1238711 A B P h Q t l' (@lem1238703 A B P h Q t l')). Qed.
Lemma lem1238715 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term94 A B P h Q t l'.
Proof. exact (@lem1238714 A B P h Q t l'). Qed.
Lemma lem1238759 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1238760 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term91 A B P h Q t l') = (term97 A B P h Q t l').
Proof. exact (@lem1238759 (term92 A B P h Q t l')). Qed.
Lemma lem1238762 (t : Prop) : (term98 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1238763 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term97 A B P h Q t l') = (term89 A B P h Q t l').
Proof. exact (@lem1238762 (term89 A B P h Q t l')). Qed.
Lemma lem1238766 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term91 A B P h Q t l') = (term89 A B P h Q t l').
Proof. exact (TRANS (@lem1238760 A B P h Q t l') (@lem1238763 A B P h Q t l')). Qed.
Lemma lem1238771 {B : Type'} (l' : list B) : (term60 B l') = (term60 B l').
Proof. exact (eq_refl (term60 B l')). Qed.
Lemma lem1238772 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term99 A B P h Q t l') = (term100 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238771 B l') (@lem1238766 A B P h Q t l')). Qed.
Lemma lem1238775 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term11 A B P Q t) = (term11 A B P Q t).
Proof. exact (eq_refl (term11 A B P Q t)). Qed.
Lemma lem1238776 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term101 A B P h Q t l') = (term102 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238775 A B P Q t) (@lem1238772 A B P h Q t l')). Qed.
Lemma lem1238779 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term103 A B P Q) = (term103 A B P Q).
Proof. exact (eq_refl (term103 A B P Q)). Qed.
Lemma lem1238780 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term93 A B P h Q t l') = (term104 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238779 A B P Q) (@lem1238776 A B P h Q t l')). Qed.
Lemma lem1238783 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term105 A B h Q t l') = (term106 A B h Q t l').
Proof. exact (fun_ext (fun P : type1413 A B => @lem1238780 A B P h Q t l')). Qed.
Lemma lem1238784 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1238785 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term107 A B h Q t l') = (term108 A B h Q t l').
Proof. exact (MK_COMB (@lem1238784 A B) (@lem1238783 A B h Q t l')). Qed.
Lemma lem1238790 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term109 A B Q t l') = (term110 A B Q t l').
Proof. exact (fun_ext (fun h : A => @lem1238785 A B h Q t l')). Qed.
Lemma lem1238791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238792 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term111 A B Q t l') = (term112 A B Q t l').
Proof. exact (MK_COMB (@lem1238791 A) (@lem1238790 A B Q t l')). Qed.
Lemma lem1238797 {A B : Type'} (t : list A) (l' : list B) : (term113 A B t l') = (term114 A B t l').
Proof. exact (fun_ext (fun Q : type1413 A B => @lem1238792 A B Q t l')). Qed.
Lemma lem1238798 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1238799 {A B : Type'} (t : list A) (l' : list B) : (term115 A B t l') = (term116 A B t l').
Proof. exact (MK_COMB (@lem1238798 A B) (@lem1238797 A B t l')). Qed.
Lemma lem1238804 {A B : Type'} (l' : list B) : (term117 A B l') = (term118 A B l').
Proof. exact (fun_ext (fun t : list A => @lem1238799 A B t l')). Qed.
Lemma lem1238805 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1238806 {A B : Type'} (l' : list B) : (term119 A B l') = (term120 A B l').
Proof. exact (MK_COMB (@lem1238805 A) (@lem1238804 A B l')). Qed.
Lemma lem1238811 {A B : Type'} : (term121 A B) = (term122 A B).
Proof. exact (fun_ext (fun l' : list B => @lem1238806 A B l')). Qed.
Lemma lem1238812 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1238821 {A B : Type'} : (term123 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem1238812 B) (@lem1238811 A B)). Qed.
Lemma lem1238840 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term100 A B P h Q t l') = (term100 A B P h Q t l').
Proof. exact (eq_refl (term100 A B P h Q t l')). Qed.
Lemma lem1238845 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) : (term125 A B P Q t l') = (term125 A B P Q t l').
Proof. exact (eq_refl (term125 A B P Q t l')). Qed.
Lemma lem1238846 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term126 A B P Q t) = (term126 A B P Q t).
Proof. exact (fun_ext (fun l' : list B => @lem1238845 A B P Q t l')). Qed.
Lemma lem1238847 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1238848 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term9 A B P Q t) = (term9 A B P Q t).
Proof. exact (MK_COMB (@lem1238847 B) (@lem1238846 A B P Q t)). Qed.
Lemma lem1238849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238850 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term11 A B P Q t) = (term11 A B P Q t).
Proof. exact (MK_COMB (@lem1238849) (@lem1238848 A B P Q t)). Qed.
Lemma lem1238851 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term102 A B P h Q t l') = (term102 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238850 A B P Q t) (@lem1238840 A B P h Q t l')). Qed.
Lemma lem1238856 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) (y : B) : (term127 A B P Q x y) = (term127 A B P Q x y).
Proof. exact (eq_refl (term127 A B P Q x y)). Qed.
Lemma lem1238857 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term128 A B P Q x) = (term128 A B P Q x).
Proof. exact (fun_ext (fun y : B => @lem1238856 A B P Q x y)). Qed.
Lemma lem1238858 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1238859 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term129 A B P Q x) = (term129 A B P Q x).
Proof. exact (MK_COMB (@lem1238858 B) (@lem1238857 A B P Q x)). Qed.
Lemma lem1238860 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term130 A B P Q) = (term130 A B P Q).
Proof. exact (fun_ext (fun x : A => @lem1238859 A B P Q x)). Qed.
Lemma lem1238861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238862 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term0 A B P Q) = (term0 A B P Q).
Proof. exact (MK_COMB (@lem1238861 A) (@lem1238860 A B P Q)). Qed.
Lemma lem1238863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238864 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term103 A B P Q) = (term103 A B P Q).
Proof. exact (MK_COMB (@lem1238863) (@lem1238862 A B P Q)). Qed.
Lemma lem1238865 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term104 A B P h Q t l') = (term104 A B P h Q t l').
Proof. exact (MK_COMB (@lem1238864 A B P Q) (@lem1238851 A B P h Q t l')). Qed.
Lemma lem1238866 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term106 A B h Q t l') = (term106 A B h Q t l').
Proof. exact (fun_ext (fun P : type1413 A B => @lem1238865 A B P h Q t l')). Qed.
Lemma lem1238867 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1238868 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term108 A B h Q t l') = (term108 A B h Q t l').
Proof. exact (MK_COMB (@lem1238867 A B) (@lem1238866 A B h Q t l')). Qed.
Lemma lem1238869 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term110 A B Q t l') = (term110 A B Q t l').
Proof. exact (fun_ext (fun h : A => @lem1238868 A B h Q t l')). Qed.
Lemma lem1238870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238871 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term112 A B Q t l') = (term112 A B Q t l').
Proof. exact (MK_COMB (@lem1238870 A) (@lem1238869 A B Q t l')). Qed.
Lemma lem1238872 {A B : Type'} (t : list A) (l' : list B) : (term114 A B t l') = (term114 A B t l').
Proof. exact (fun_ext (fun Q : type1413 A B => @lem1238871 A B Q t l')). Qed.
Lemma lem1238873 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1238874 {A B : Type'} (t : list A) (l' : list B) : (term116 A B t l') = (term116 A B t l').
Proof. exact (MK_COMB (@lem1238873 A B) (@lem1238872 A B t l')). Qed.
Lemma lem1238875 {A B : Type'} (l' : list B) : (term118 A B l') = (term118 A B l').
Proof. exact (fun_ext (fun t : list A => @lem1238874 A B t l')). Qed.
Lemma lem1238876 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1238877 {A B : Type'} (l' : list B) : (term120 A B l') = (term120 A B l').
Proof. exact (MK_COMB (@lem1238876 A) (@lem1238875 A B l')). Qed.
Lemma lem1238878 {A B : Type'} : (term122 A B) = (term122 A B).
Proof. exact (fun_ext (fun l' : list B => @lem1238877 A B l')). Qed.
Lemma lem1238879 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1238880 {A B : Type'} : (term124 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem1238879 B) (@lem1238878 A B)). Qed.
Lemma lem1238947 {A B : Type'} : (term123 A B) = (term124 A B).
Proof. exact (TRANS (@lem1238821 A B) (@lem1238880 A B)). Qed.
Lemma lem1238948 {A B : Type'} : (term124 A B) = (term123 A B).
Proof. exact (SYM (@lem1238947 A B)). Qed.
Lemma lem1238949 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term0 A B P Q.
Proof. exact (h1). Qed.
Lemma lem1238950 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term9 A B P Q t.
Proof. exact (h1). Qed.
Lemma lem1238954 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1238955 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term57 A B h Q t l') = (term131 A B h Q t l').
Proof. exact (@lem1238954 (term57 A B h Q t l')). Qed.
Lemma lem1238956 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term131 A B h Q t l') = (term57 A B h Q t l').
Proof. exact (SYM (@lem1238955 A B h Q t l')). Qed.
Lemma lem1238957 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term132 A B h Q t l') : term132 A B h Q t l'.
Proof. exact (h1). Qed.
Lemma lem1238964 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) (y : B) : (term127 A B P Q x y) = (term133 A B P Q x y).
Proof. exact (@lem17265 (P x y) (Q x y)). Qed.
Lemma lem1238965 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term128 A B P Q x) = (term134 A B P Q x).
Proof. exact (fun_ext (fun y : B => @lem1238964 A B P Q x y)). Qed.
Lemma lem1238966 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1238967 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term129 A B P Q x) = (term135 A B P Q x).
Proof. exact (MK_COMB (@lem1238966 B) (@lem1238965 A B P Q x)). Qed.
Lemma lem1238968 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term130 A B P Q) = (term136 A B P Q).
Proof. exact (fun_ext (fun x : A => @lem1238967 A B P Q x)). Qed.
Lemma lem1238969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1239026 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term0 A B P Q) = (term137 A B P Q).
Proof. exact (MK_COMB (@lem1238969 A) (@lem1238968 A B P Q)). Qed.
Lemma lem1239027 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term137 A B P Q.
Proof. exact (EQ_MP (@lem1239026 A B P Q) (@lem1238949 A B P Q h1)). Qed.
Lemma lem1239034 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) : (term125 A B P Q t l') = (term138 A B P Q t l').
Proof. exact (@lem17265 (@ALL2 A B P t l') (@ALL2 A B Q t l')). Qed.
Lemma lem1239035 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term126 A B P Q t) = (term139 A B P Q t).
Proof. exact (fun_ext (fun l' : list B => @lem1239034 A B P Q t l')). Qed.
Lemma lem1239036 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1239089 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term9 A B P Q t) = (term140 A B P Q t).
Proof. exact (MK_COMB (@lem1239036 B) (@lem1239035 A B P Q t)). Qed.
Lemma lem1239090 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term140 A B P Q t.
Proof. exact (EQ_MP (@lem1239089 A B P Q t) (@lem1238950 A B P Q t h1)). Qed.
Lemma lem1239106 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term57 A B h P t l'.
Proof. exact (h1). Qed.
Lemma lem1239117 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term132 A B h Q t l') = (term141 A B h Q t l').
Proof. exact (@lem17045 (term142 A B Q h l') (term143 A B Q t l')). Qed.
Lemma lem1239118 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term132 A B h Q t l') : term141 A B h Q t l'.
Proof. exact (EQ_MP (@lem1239117 A B h Q t l') (@lem1238957 A B h Q t l' h1)). Qed.
Lemma lem1239125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239126 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem1239125 A (B -> Prop) f x). Qed.
Lemma lem1239127 {A B : Type'} (Q : type1413 A B) (x : A) : (Q x) = (@I (A -> B -> Prop) Q x).
Proof. exact (@lem1239126 A B Q x). Qed.
Lemma lem1239128 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1239129 {A B : Type'} (Q : type1413 A B) (x : A) (y : B) : (Q x y) = (@I (A -> B -> Prop) Q x y).
Proof. exact (MK_COMB (@lem1239127 A B Q x) (@lem1239128 B y)). Qed.
Lemma lem1239131 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239132 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem1239131 B Prop f x). Qed.
Lemma lem1239133 {A B : Type'} (Q : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) Q x y) = (term144 A B Q x y).
Proof. exact (@lem1239132 B (@I (A -> B -> Prop) Q x) y). Qed.
Lemma lem1239135 {A B : Type'} (Q : type1413 A B) (x : A) (y : B) : (Q x y) = (term144 A B Q x y).
Proof. exact (TRANS (@lem1239129 A B Q x y) (@lem1239133 A B Q x y)). Qed.
Lemma lem1239136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1239143 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239144 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem1239143 A (B -> Prop) f x). Qed.
Lemma lem1239145 {A B : Type'} (P : type1413 A B) (x : A) : (P x) = (@I (A -> B -> Prop) P x).
Proof. exact (@lem1239144 A B P x). Qed.
Lemma lem1239146 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1239147 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (P x y) = (@I (A -> B -> Prop) P x y).
Proof. exact (MK_COMB (@lem1239145 A B P x) (@lem1239146 B y)). Qed.
Lemma lem1239149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239150 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem1239149 B Prop f x). Qed.
Lemma lem1239151 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (@I (A -> B -> Prop) P x y) = (term144 A B P x y).
Proof. exact (@lem1239150 B (@I (A -> B -> Prop) P x) y). Qed.
Lemma lem1239153 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (P x y) = (term144 A B P x y).
Proof. exact (TRANS (@lem1239147 A B P x y) (@lem1239151 A B P x y)). Qed.
Lemma lem1239154 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term145 A B P x y) = (term146 A B P x y).
Proof. exact (MK_COMB (@lem1239136) (@lem1239153 A B P x y)). Qed.
Lemma lem1239155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1239156 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term147 A B P x y) = (term148 A B P x y).
Proof. exact (MK_COMB (@lem1239155) (@lem1239154 A B P x y)). Qed.
Lemma lem1239157 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) (y : B) : (term133 A B P Q x y) = (term149 A B P Q x y).
Proof. exact (MK_COMB (@lem1239156 A B P x y) (@lem1239135 A B Q x y)). Qed.
Lemma lem1239158 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term134 A B P Q x) = (term150 A B P Q x).
Proof. exact (fun_ext (fun y : B => @lem1239157 A B P Q x y)). Qed.
Lemma lem1239159 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1239160 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term135 A B P Q x) = (term151 A B P Q x).
Proof. exact (MK_COMB (@lem1239159 B) (@lem1239158 A B P Q x)). Qed.
Lemma lem1239161 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term136 A B P Q) = (term152 A B P Q).
Proof. exact (fun_ext (fun x : A => @lem1239160 A B P Q x)). Qed.
Lemma lem1239162 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1239163 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term137 A B P Q) = (term153 A B P Q).
Proof. exact (MK_COMB (@lem1239162 A) (@lem1239161 A B P Q)). Qed.
Lemma lem1239164 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term153 A B P Q.
Proof. exact (EQ_MP (@lem1239163 A B P Q) (@lem1239027 A B P Q h1)). Qed.
Lemma lem1239183 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) : (term138 A B P Q t l') = (term138 A B P Q t l').
Proof. exact (eq_refl (term138 A B P Q t l')). Qed.
Lemma lem1239184 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term139 A B P Q t) = (term139 A B P Q t).
Proof. exact (fun_ext (fun l' : list B => @lem1239183 A B P Q t l')). Qed.
Lemma lem1239185 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1239186 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term140 A B P Q t) = (term140 A B P Q t).
Proof. exact (MK_COMB (@lem1239185 B) (@lem1239184 A B P Q t)). Qed.
Lemma lem1239187 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term140 A B P Q t.
Proof. exact (EQ_MP (@lem1239186 A B P Q t) (@lem1239090 A B P Q t h1)). Qed.
Lemma lem1239204 {A B : Type'} (P : type1413 A B) (t : list A) (l' : list B) : (term143 A B P t l') = (term143 A B P t l').
Proof. exact (eq_refl (term143 A B P t l')). Qed.
Lemma lem1239213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239214 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem1239213 A (B -> Prop) f x). Qed.
Lemma lem1239215 {A B : Type'} (P : type1413 A B) (h : A) : (P h) = (@I (A -> B -> Prop) P h).
Proof. exact (@lem1239214 A B P h). Qed.
Lemma lem1239216 {B : Type'} (l' : list B) : (@hd B l') = (@hd B l').
Proof. exact (eq_refl (@hd B l')). Qed.
Lemma lem1239217 {A B : Type'} (P : type1413 A B) (h : A) (l' : list B) : (term142 A B P h l') = (term154 A B P h l').
Proof. exact (MK_COMB (@lem1239215 A B P h) (@lem1239216 B l')). Qed.
Lemma lem1239219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239220 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem1239219 B Prop f x). Qed.
Lemma lem1239221 {A B : Type'} (P : type1413 A B) (h : A) (l' : list B) : (term154 A B P h l') = (term155 A B P h l').
Proof. exact (@lem1239220 B (@I (A -> B -> Prop) P h) (@hd B l')). Qed.
Lemma lem1239223 {A B : Type'} (P : type1413 A B) (h : A) (l' : list B) : (term142 A B P h l') = (term155 A B P h l').
Proof. exact (TRANS (@lem1239217 A B P h l') (@lem1239221 A B P h l')). Qed.
Lemma lem1239224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1239225 {A B : Type'} (P : type1413 A B) (h : A) (l' : list B) : (term156 A B P h l') = (term157 A B P h l').
Proof. exact (MK_COMB (@lem1239224) (@lem1239223 A B P h l')). Qed.
Lemma lem1239226 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) : (term57 A B h P t l') = (term158 A B h P t l').
Proof. exact (MK_COMB (@lem1239225 A B P h l') (@lem1239204 A B P t l')). Qed.
Lemma lem1239227 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term158 A B h P t l'.
Proof. exact (EQ_MP (@lem1239226 A B h P t l') (@lem1239106 A B h P t l' h1)). Qed.
Lemma lem1239238 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term159 A B Q t l') = (term159 A B Q t l').
Proof. exact (eq_refl (term159 A B Q t l')). Qed.
Lemma lem1239239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1239248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239249 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem1239248 A (B -> Prop) f x). Qed.
Lemma lem1239250 {A B : Type'} (Q : type1413 A B) (h : A) : (Q h) = (@I (A -> B -> Prop) Q h).
Proof. exact (@lem1239249 A B Q h). Qed.
Lemma lem1239251 {B : Type'} (l' : list B) : (@hd B l') = (@hd B l').
Proof. exact (eq_refl (@hd B l')). Qed.
Lemma lem1239252 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term142 A B Q h l') = (term154 A B Q h l').
Proof. exact (MK_COMB (@lem1239250 A B Q h) (@lem1239251 B l')). Qed.
Lemma lem1239254 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1239255 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem1239254 B Prop f x). Qed.
Lemma lem1239256 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term154 A B Q h l') = (term155 A B Q h l').
Proof. exact (@lem1239255 B (@I (A -> B -> Prop) Q h) (@hd B l')). Qed.
Lemma lem1239258 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term142 A B Q h l') = (term155 A B Q h l').
Proof. exact (TRANS (@lem1239252 A B Q h l') (@lem1239256 A B Q h l')). Qed.
Lemma lem1239259 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term160 A B Q h l') = (term161 A B Q h l').
Proof. exact (MK_COMB (@lem1239239) (@lem1239258 A B Q h l')). Qed.
Lemma lem1239260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1239261 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term162 A B Q h l') = (term163 A B Q h l').
Proof. exact (MK_COMB (@lem1239260) (@lem1239259 A B Q h l')). Qed.
Lemma lem1239262 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term141 A B h Q t l') = (term164 A B h Q t l').
Proof. exact (MK_COMB (@lem1239261 A B Q h l') (@lem1239238 A B Q t l')). Qed.
Lemma lem1239263 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term132 A B h Q t l') : term164 A B h Q t l'.
Proof. exact (EQ_MP (@lem1239262 A B h Q t l') (@lem1239118 A B h Q t l' h1)). Qed.
Lemma lem1239275 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) (y : B) : (term149 A B P Q x y) = (term149 A B P Q x y).
Proof. exact (eq_refl (term149 A B P Q x y)). Qed.
Lemma lem1239276 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term150 A B P Q x) = (term150 A B P Q x).
Proof. exact (fun_ext (fun y : B => @lem1239275 A B P Q x y)). Qed.
Lemma lem1239277 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1239278 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (x : A) : (term151 A B P Q x) = (term151 A B P Q x).
Proof. exact (MK_COMB (@lem1239277 B) (@lem1239276 A B P Q x)). Qed.
Lemma lem1239279 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term152 A B P Q) = (term152 A B P Q).
Proof. exact (fun_ext (fun x : A => @lem1239278 A B P Q x)). Qed.
Lemma lem1239280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1239282 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) : (term153 A B P Q) = (term153 A B P Q).
Proof. exact (MK_COMB (@lem1239280 A) (@lem1239279 A B P Q)). Qed.
Lemma lem1239283 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term153 A B P Q.
Proof. exact (EQ_MP (@lem1239282 A B P Q) (@lem1239164 A B P Q h1)). Qed.
Lemma lem1239312 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) (h1 : term161 A B Q h l') : term161 A B Q h l'.
Proof. exact (h1). Qed.
Lemma lem1239336 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) : (term138 A B P Q t l') = (term138 A B P Q t l').
Proof. exact (eq_refl (term138 A B P Q t l')). Qed.
Lemma lem1239337 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term139 A B P Q t) = (term139 A B P Q t).
Proof. exact (fun_ext (fun l' : list B => @lem1239336 A B P Q t l')). Qed.
Lemma lem1239338 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1239340 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) : (term140 A B P Q t) = (term140 A B P Q t).
Proof. exact (MK_COMB (@lem1239338 B) (@lem1239337 A B P Q t)). Qed.
Lemma lem1239341 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term140 A B P Q t.
Proof. exact (EQ_MP (@lem1239340 A B P Q t) (@lem1239187 A B P Q t h1)). Qed.
Lemma lem1239357 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term159 A B Q t l') : term159 A B Q t l'.
Proof. exact (h1). Qed.
Lemma lem1239358 {A B : Type'} (_22688 : A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term165 A B P Q _22688.
Proof. exact (@lem1239283 A B P Q h1 _22688). Qed.
Lemma lem1239359 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (_22688 : A) : (term165 A B P Q _22688) = (term151 A B P Q _22688).
Proof. exact (eq_refl (term165 A B P Q _22688)). Qed.
Lemma lem1239360 {A B : Type'} (_22688 : A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term151 A B P Q _22688.
Proof. exact (EQ_MP (@lem1239359 A B P Q _22688) (@lem1239358 A B _22688 P Q h1)). Qed.
Lemma lem1239361 {A B : Type'} (_22688 : A) (_22689 : B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term166 A B P Q _22688 _22689.
Proof. exact (@lem1239360 A B _22688 P Q h1 _22689). Qed.
Lemma lem1239362 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (_22688 : A) (_22689 : B) : (term166 A B P Q _22688 _22689) = (term149 A B P Q _22688 _22689).
Proof. exact (eq_refl (term166 A B P Q _22688 _22689)). Qed.
Lemma lem1239373 {A B : Type'} (_22693 : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term167 A B P Q t _22693.
Proof. exact (@lem1239341 A B P Q t h1 _22693). Qed.
Lemma lem1239374 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (_22693 : list B) : (term167 A B P Q t _22693) = (term138 A B P Q t _22693).
Proof. exact (eq_refl (term167 A B P Q t _22693)). Qed.
Lemma lem1239381 {A B : Type'} (_22688 : A) (_22689 : B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term149 A B P Q _22688 _22689.
Proof. exact (EQ_MP (@lem1239362 A B P Q _22688 _22689) (@lem1239361 A B _22688 _22689 P Q h1)). Qed.
Lemma lem1239395 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) (h1 : term161 A B Q h l') : term161 A B Q h l'.
Proof. exact (h1). Qed.
Lemma lem1239407 {A B : Type'} (_22693 : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term138 A B P Q t _22693.
Proof. exact (EQ_MP (@lem1239374 A B P Q t _22693) (@lem1239373 A B _22693 P Q t h1)). Qed.
Lemma lem1239415 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term159 A B Q t l') : term159 A B Q t l'.
Proof. exact (h1). Qed.
Lemma lem1239505 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term155 A B P h l'.
Proof. exact (proj1 (@lem1239227 A B h P t l' h1)). Qed.
Lemma lem1239506 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term168 A B P h l'.
Proof. exact (fun h0 : term161 A B P h l' => @lem1239505 A B h P t l' h1). Qed.
Lemma lem1239508 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239509 {A B : Type'} (P : type1413 A B) (h : A) (l' : list B) : (term168 A B P h l') = (term155 A B P h l').
Proof. exact (@lem1239508 (term155 A B P h l')). Qed.
Lemma lem1239510 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term155 A B P h l'.
Proof. exact (EQ_MP (@lem1239509 A B P h l') (@lem1239506 A B h P t l' h1)). Qed.
Lemma lem1239516 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1239517 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : (term149 A B P Q _22688 _22689) = (term170 A B Q P _22688 _22689).
Proof. exact (@lem1239516 (term144 A B Q _22688 _22689) (term146 A B P _22688 _22689)). Qed.
Lemma lem1239523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1239524 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : (term171 A B P Q _22688 _22689) = (term172 A B Q P _22688 _22689).
Proof. exact (MK_COMB (@lem1239523) (@lem1239517 A B Q P _22688 _22689)). Qed.
Lemma lem1239530 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : (term170 A B Q P _22688 _22689) = (term170 A B Q P _22688 _22689).
Proof. exact (eq_refl (term170 A B Q P _22688 _22689)). Qed.
Lemma lem1239531 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : ((term149 A B P Q _22688 _22689) = (term170 A B Q P _22688 _22689)) = ((term170 A B Q P _22688 _22689) = (term170 A B Q P _22688 _22689)).
Proof. exact (MK_COMB (@lem1239524 A B Q P _22688 _22689) (@lem1239530 A B Q P _22688 _22689)). Qed.
Lemma lem1239533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1239534 (x : Prop) : (x = x) = True.
Proof. exact (@lem1239533 Prop x). Qed.
Lemma lem1239535 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : ((term170 A B Q P _22688 _22689) = (term170 A B Q P _22688 _22689)) = True.
Proof. exact (@lem1239534 (term170 A B Q P _22688 _22689)). Qed.
Lemma lem1239536 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : ((term149 A B P Q _22688 _22689) = (term170 A B Q P _22688 _22689)) = True.
Proof. exact (TRANS (@lem1239531 A B Q P _22688 _22689) (@lem1239535 A B Q P _22688 _22689)). Qed.
Lemma lem1239537 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : True = ((term149 A B P Q _22688 _22689) = (term170 A B Q P _22688 _22689)).
Proof. exact (SYM (@lem1239536 A B Q P _22688 _22689)). Qed.
Lemma lem1239538 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (_22688 : A) (_22689 : B) : (term149 A B P Q _22688 _22689) = (term170 A B Q P _22688 _22689).
Proof. exact (EQ_MP (@lem1239537 A B Q P _22688 _22689) (@lem0)). Qed.
Lemma lem1239539 {A B : Type'} (_22688 : A) (_22689 : B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term170 A B Q P _22688 _22689.
Proof. exact (EQ_MP (@lem1239538 A B Q P _22688 _22689) (@lem1239381 A B _22688 _22689 P Q h1)). Qed.
Lemma lem1239541 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1239542 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (_22688 : A) (_22689 : B) : (term170 A B Q P _22688 _22689) = (term174 A B P Q _22688 _22689).
Proof. exact (@lem1239541 (term146 A B P _22688 _22689) (term144 A B Q _22688 _22689)). Qed.
Lemma lem1239544 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1239545 {A B : Type'} (P : type1413 A B) (_22688 : A) (_22689 : B) : (term175 A B P _22688 _22689) = (term144 A B P _22688 _22689).
Proof. exact (@lem1239544 (term144 A B P _22688 _22689)). Qed.
Lemma lem1239546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1239547 {A B : Type'} (P : type1413 A B) (_22688 : A) (_22689 : B) : (term176 A B P _22688 _22689) = (term177 A B P _22688 _22689).
Proof. exact (MK_COMB (@lem1239546) (@lem1239545 A B P _22688 _22689)). Qed.
Lemma lem1239548 {A B : Type'} (Q : type1413 A B) (_22688 : A) (_22689 : B) : (term144 A B Q _22688 _22689) = (term144 A B Q _22688 _22689).
Proof. exact (eq_refl (term144 A B Q _22688 _22689)). Qed.
Lemma lem1239549 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (_22688 : A) (_22689 : B) : (term174 A B P Q _22688 _22689) = (term178 A B P Q _22688 _22689).
Proof. exact (MK_COMB (@lem1239547 A B P _22688 _22689) (@lem1239548 A B Q _22688 _22689)). Qed.
Lemma lem1239550 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (_22688 : A) (_22689 : B) : (term170 A B Q P _22688 _22689) = (term178 A B P Q _22688 _22689).
Proof. exact (TRANS (@lem1239542 A B P Q _22688 _22689) (@lem1239549 A B P Q _22688 _22689)). Qed.
Lemma lem1239553 {A B : Type'} (_22688 : A) (_22689 : B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term178 A B P Q _22688 _22689.
Proof. exact (EQ_MP (@lem1239550 A B P Q _22688 _22689) (@lem1239539 A B _22688 _22689 P Q h1)). Qed.
Lemma lem1239554 {A B : Type'} (_22688 : A) (_22689 : B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term178 A B P Q _22688 _22689.
Proof. exact (@lem1239553 A B _22688 _22689 P Q h1). Qed.
Lemma lem1239555 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term179 A B P Q h l'.
Proof. exact (@lem1239554 A B h (@hd B l') P Q h1). Qed.
Lemma lem1239558 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term57 A B h P t l') : term155 A B Q h l'.
Proof. exact (@lem1239555 A B h l' P Q h1 (@lem1239510 A B h P t l' h2)). Qed.
Lemma lem1239559 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term57 A B h P t l') : term168 A B Q h l'.
Proof. exact (fun h0 : term161 A B Q h l' => @lem1239558 A B Q h P t l' h1 h2). Qed.
Lemma lem1239561 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239562 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term168 A B Q h l') = (term155 A B Q h l').
Proof. exact (@lem1239561 (term155 A B Q h l')). Qed.
Lemma lem1239563 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term57 A B h P t l') : term155 A B Q h l'.
Proof. exact (EQ_MP (@lem1239562 A B Q h l') (@lem1239559 A B Q h P t l' h1 h2)). Qed.
Lemma lem1239566 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1239568 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) : (term161 A B Q h l') = (term180 A B Q h l').
Proof. exact (@lem1239566 (term155 A B Q h l')). Qed.
Lemma lem1239571 {A B : Type'} (Q : type1413 A B) (h : A) (l' : list B) (h1 : term161 A B Q h l') : term180 A B Q h l'.
Proof. exact (EQ_MP (@lem1239568 A B Q h l') (@lem1239395 A B Q h l' h1)). Qed.
Lemma lem1239574 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : False.
Proof. exact (@lem1239571 A B Q h l' h2 (@lem1239563 A B Q h P t l' h1 h3)). Qed.
Lemma lem1239575 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : term181.
Proof. exact (fun h0 : ~ False => @lem1239574 A B Q h P t l' h1 h2 h3). Qed.
Lemma lem1239577 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239578 : term181 = False.
Proof. exact (@lem1239577 False). Qed.
Lemma lem1239579 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239578) (@lem1239575 A B Q h P t l' h1 h2 h3)). Qed.
Lemma lem1239669 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term143 A B P t l'.
Proof. exact (proj2 (@lem1239227 A B h P t l' h1)). Qed.
Lemma lem1239670 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term182 A B P t l'.
Proof. exact (fun h0 : term159 A B P t l' => @lem1239669 A B h P t l' h1). Qed.
Lemma lem1239672 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239673 {A B : Type'} (P : type1413 A B) (t : list A) (l' : list B) : (term182 A B P t l') = (term143 A B P t l').
Proof. exact (@lem1239672 (term143 A B P t l')). Qed.
Lemma lem1239674 {A B : Type'} (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term57 A B h P t l') : term143 A B P t l'.
Proof. exact (EQ_MP (@lem1239673 A B P t l') (@lem1239670 A B h P t l' h1)). Qed.
Lemma lem1239680 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1239681 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : (term138 A B P Q t _22693) = (term183 A B Q P t _22693).
Proof. exact (@lem1239680 (@ALL2 A B Q t _22693) (term184 A B P t _22693)). Qed.
Lemma lem1239687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1239688 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : (term185 A B P Q t _22693) = (term186 A B Q P t _22693).
Proof. exact (MK_COMB (@lem1239687) (@lem1239681 A B Q P t _22693)). Qed.
Lemma lem1239694 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : (term183 A B Q P t _22693) = (term183 A B Q P t _22693).
Proof. exact (eq_refl (term183 A B Q P t _22693)). Qed.
Lemma lem1239695 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : ((term138 A B P Q t _22693) = (term183 A B Q P t _22693)) = ((term183 A B Q P t _22693) = (term183 A B Q P t _22693)).
Proof. exact (MK_COMB (@lem1239688 A B Q P t _22693) (@lem1239694 A B Q P t _22693)). Qed.
Lemma lem1239697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1239698 (x : Prop) : (x = x) = True.
Proof. exact (@lem1239697 Prop x). Qed.
Lemma lem1239699 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : ((term183 A B Q P t _22693) = (term183 A B Q P t _22693)) = True.
Proof. exact (@lem1239698 (term183 A B Q P t _22693)). Qed.
Lemma lem1239700 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : ((term138 A B P Q t _22693) = (term183 A B Q P t _22693)) = True.
Proof. exact (TRANS (@lem1239695 A B Q P t _22693) (@lem1239699 A B Q P t _22693)). Qed.
Lemma lem1239701 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : True = ((term138 A B P Q t _22693) = (term183 A B Q P t _22693)).
Proof. exact (SYM (@lem1239700 A B Q P t _22693)). Qed.
Lemma lem1239702 {A B : Type'} (Q : type1413 A B) (P : type1413 A B) (t : list A) (_22693 : list B) : (term138 A B P Q t _22693) = (term183 A B Q P t _22693).
Proof. exact (EQ_MP (@lem1239701 A B Q P t _22693) (@lem0)). Qed.
Lemma lem1239703 {A B : Type'} (_22693 : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term183 A B Q P t _22693.
Proof. exact (EQ_MP (@lem1239702 A B Q P t _22693) (@lem1239407 A B _22693 P Q t h1)). Qed.
Lemma lem1239705 (b : Prop) (a : Prop) : (a \/ b) = (term173 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1239706 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (_22693 : list B) : (term183 A B Q P t _22693) = (term187 A B P Q t _22693).
Proof. exact (@lem1239705 (term184 A B P t _22693) (@ALL2 A B Q t _22693)). Qed.
Lemma lem1239708 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1239709 {A B : Type'} (P : type1413 A B) (t : list A) (_22693 : list B) : (term188 A B P t _22693) = (@ALL2 A B P t _22693).
Proof. exact (@lem1239708 (@ALL2 A B P t _22693)). Qed.
Lemma lem1239710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1239711 {A B : Type'} (P : type1413 A B) (t : list A) (_22693 : list B) : (term189 A B P t _22693) = (term190 A B P t _22693).
Proof. exact (MK_COMB (@lem1239710) (@lem1239709 A B P t _22693)). Qed.
Lemma lem1239712 {A B : Type'} (Q : type1413 A B) (t : list A) (_22693 : list B) : (@ALL2 A B Q t _22693) = (@ALL2 A B Q t _22693).
Proof. exact (eq_refl (@ALL2 A B Q t _22693)). Qed.
Lemma lem1239713 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (_22693 : list B) : (term187 A B P Q t _22693) = (term125 A B P Q t _22693).
Proof. exact (MK_COMB (@lem1239711 A B P t _22693) (@lem1239712 A B Q t _22693)). Qed.
Lemma lem1239714 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (t : list A) (_22693 : list B) : (term183 A B Q P t _22693) = (term125 A B P Q t _22693).
Proof. exact (TRANS (@lem1239706 A B P Q t _22693) (@lem1239713 A B P Q t _22693)). Qed.
Lemma lem1239717 {A B : Type'} (_22693 : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term125 A B P Q t _22693.
Proof. exact (EQ_MP (@lem1239714 A B P Q t _22693) (@lem1239703 A B _22693 P Q t h1)). Qed.
Lemma lem1239718 {A B : Type'} (_22693 : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term125 A B P Q t _22693.
Proof. exact (@lem1239717 A B _22693 P Q t h1). Qed.
Lemma lem1239719 {A B : Type'} (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term9 A B P Q t) : term191 A B P Q t l'.
Proof. exact (@lem1239718 A B (@tl B l') P Q t h1). Qed.
Lemma lem1239722 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term57 A B h P t l') : term143 A B Q t l'.
Proof. exact (@lem1239719 A B l' P Q t h1 (@lem1239674 A B h P t l' h2)). Qed.
Lemma lem1239723 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term57 A B h P t l') : term182 A B Q t l'.
Proof. exact (fun h0 : term159 A B Q t l' => @lem1239722 A B Q h P t l' h1 h2). Qed.
Lemma lem1239725 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239726 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term182 A B Q t l') = (term143 A B Q t l').
Proof. exact (@lem1239725 (term143 A B Q t l')). Qed.
Lemma lem1239727 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term57 A B h P t l') : term143 A B Q t l'.
Proof. exact (EQ_MP (@lem1239726 A B Q t l') (@lem1239723 A B Q h P t l' h1 h2)). Qed.
Lemma lem1239730 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1239732 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term159 A B Q t l') = (term192 A B Q t l').
Proof. exact (@lem1239730 (term143 A B Q t l')). Qed.
Lemma lem1239735 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term159 A B Q t l') : term192 A B Q t l'.
Proof. exact (EQ_MP (@lem1239732 A B Q t l') (@lem1239415 A B Q t l' h1)). Qed.
Lemma lem1239738 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : False.
Proof. exact (@lem1239735 A B Q t l' h2 (@lem1239727 A B Q h P t l' h1 h3)). Qed.
Lemma lem1239739 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : term181.
Proof. exact (fun h0 : ~ False => @lem1239738 A B Q h P t l' h1 h2 h3). Qed.
Lemma lem1239741 (p : Prop) : (term169 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1239742 : term181 = False.
Proof. exact (@lem1239741 False). Qed.
Lemma lem1239743 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239742) (@lem1239739 A B Q h P t l' h1 h2 h3)). Qed.
Lemma lem1239744 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : (term159 A B Q t l') = False.
Proof. exact (prop_ext (fun h4 : term159 A B Q t l' => @lem1239743 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239415 A B Q t l' h2)). Qed.
Lemma lem1239745 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239744 A B Q h P t l' h1 h2 h3) (@lem1239415 A B Q t l' h2)). Qed.
Lemma lem1239746 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : (term161 A B Q h l') = False.
Proof. exact (prop_ext (fun h4 : term161 A B Q h l' => @lem1239579 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239395 A B Q h l' h2)). Qed.
Lemma lem1239747 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239746 A B Q h P t l' h1 h2 h3) (@lem1239395 A B Q h l' h2)). Qed.
Lemma lem1239748 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : (term159 A B Q t l') = False.
Proof. exact (prop_ext (fun h4 : term159 A B Q t l' => @lem1239745 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239357 A B Q t l' h2)). Qed.
Lemma lem1239749 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239748 A B Q h P t l' h1 h2 h3) (@lem1239357 A B Q t l' h2)). Qed.
Lemma lem1239750 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : (term161 A B Q h l') = False.
Proof. exact (prop_ext (fun h4 : term161 A B Q h l' => @lem1239747 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239312 A B Q h l' h2)). Qed.
Lemma lem1239751 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239750 A B Q h P t l' h1 h2 h3) (@lem1239312 A B Q h l' h2)). Qed.
Lemma lem1239752 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : (term159 A B Q t l') = False.
Proof. exact (prop_ext (fun h4 : term159 A B Q t l' => @lem1239749 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239357 A B Q t l' h2)). Qed.
Lemma lem1239753 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term9 A B P Q t) (h2 : term159 A B Q t l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239752 A B Q h P t l' h1 h2 h3) (@lem1239357 A B Q t l' h2)). Qed.
Lemma lem1239754 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : (term161 A B Q h l') = False.
Proof. exact (prop_ext (fun h4 : term161 A B Q h l' => @lem1239751 A B Q h P t l' h1 h2 h3) (fun h4 : False => @lem1239312 A B Q h l' h2)). Qed.
Lemma lem1239755 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term161 A B Q h l') (h3 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239754 A B Q h P t l' h1 h2 h3) (@lem1239312 A B Q h l' h2)). Qed.
Lemma lem1239756 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term132 A B h Q t l') (h4 : term57 A B h P t l') : False.
Proof. exact (or_elim (@lem1239263 A B h Q t l' h3) (fun h0 : term161 A B Q h l' => @lem1239755 A B Q h P t l' h1 h0 h4) (fun h0 : term159 A B Q t l' => @lem1239753 A B Q h P t l' h2 h0 h4)). Qed.
Lemma lem1239757 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term132 A B h Q t l') (h4 : term57 A B h P t l') : (term57 A B h P t l') = False.
Proof. exact (prop_ext (fun h5 : term57 A B h P t l' => @lem1239756 A B Q h P t l' h1 h2 h3 h4) (fun h5 : False => @lem1239106 A B h P t l' h4)). Qed.
Lemma lem1239758 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term132 A B h Q t l') (h4 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239757 A B Q h P t l' h1 h2 h3 h4) (@lem1239106 A B h P t l' h4)). Qed.
Lemma lem1239759 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term132 A B h Q t l') (h4 : term57 A B h P t l') : (term132 A B h Q t l') = False.
Proof. exact (prop_ext (fun h5 : term132 A B h Q t l' => @lem1239758 A B Q h P t l' h1 h2 h3 h4) (fun h5 : False => @lem1238957 A B h Q t l' h3)). Qed.
Lemma lem1239760 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term132 A B h Q t l') (h4 : term57 A B h P t l') : False.
Proof. exact (EQ_MP (@lem1239759 A B Q h P t l' h1 h2 h3 h4) (@lem1238957 A B h Q t l' h3)). Qed.
Lemma lem1239761 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term57 A B h P t l') : term131 A B h Q t l'.
Proof. exact (fun h0 : term132 A B h Q t l' => @lem1239760 A B Q h P t l' h1 h2 h0 h3). Qed.
Lemma lem1239762 {A B : Type'} (Q : type1413 A B) (h : A) (P : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term57 A B h P t l') : term57 A B h Q t l'.
Proof. exact (EQ_MP (@lem1238956 A B h Q t l') (@lem1239761 A B Q h P t l' h1 h2 h3)). Qed.
Lemma lem1239763 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term89 A B P h Q t l'.
Proof. exact (fun h0 : term57 A B h P t l' => @lem1239762 A B Q h P t l' h1 h2 h0). Qed.
Lemma lem1239764 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term100 A B P h Q t l'.
Proof. exact (fun h0 : term78 B l' => @lem1239763 A B h l' P Q t h1 h2). Qed.
Lemma lem1239765 {A B : Type'} (h : A) (t : list A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term102 A B P h Q t l'.
Proof. exact (fun h0 : term9 A B P Q t => @lem1239764 A B h l' P Q t h1 h0). Qed.
Lemma lem1239766 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term104 A B P h Q t l'.
Proof. exact (fun h0 : term0 A B P Q => @lem1239765 A B h t l' P Q h0). Qed.
Lemma lem1239771 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term108 A B h Q t l'.
Proof. exact (fun P : type1413 A B => @lem1239766 A B P h Q t l'). Qed.
Lemma lem1239776 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : term112 A B Q t l'.
Proof. exact (fun h : A => @lem1239771 A B h Q t l'). Qed.
Lemma lem1239781 {A B : Type'} (t : list A) (l' : list B) : term116 A B t l'.
Proof. exact (fun Q : type1413 A B => @lem1239776 A B Q t l'). Qed.
Lemma lem1239786 {A B : Type'} (l' : list B) : term120 A B l'.
Proof. exact (fun t : list A => @lem1239781 A B t l'). Qed.
Lemma lem1239791 {A B : Type'} : term124 A B.
Proof. exact (fun l' : list B => @lem1239786 A B l'). Qed.
Lemma lem1239792 {A B : Type'} : term123 A B.
Proof. exact (EQ_MP (@lem1238948 A B) (@lem1239791 A B)). Qed.
Lemma lem1239793 {A B : Type'} (l' : list B) : term193 A B l'.
Proof. exact (@lem1239792 A B l'). Qed.
Lemma lem1239794 {A B : Type'} (l' : list B) : (term193 A B l') = (term119 A B l').
Proof. exact (eq_refl (term193 A B l')). Qed.
Lemma lem1239795 {A B : Type'} (l' : list B) : term119 A B l'.
Proof. exact (EQ_MP (@lem1239794 A B l') (@lem1239793 A B l')). Qed.
Lemma lem1239796 {A B : Type'} (l' : list B) (t : list A) : term194 A B l' t.
Proof. exact (@lem1239795 A B l' t). Qed.
Lemma lem1239797 {A B : Type'} (t : list A) (l' : list B) : (term194 A B l' t) = (term115 A B t l').
Proof. exact (eq_refl (term194 A B l' t)). Qed.
Lemma lem1239798 {A B : Type'} (t : list A) (l' : list B) : term115 A B t l'.
Proof. exact (EQ_MP (@lem1239797 A B t l') (@lem1239796 A B l' t)). Qed.
Lemma lem1239799 {A B : Type'} (t : list A) (l' : list B) (Q : type1413 A B) : term195 A B t l' Q.
Proof. exact (@lem1239798 A B t l' Q). Qed.
Lemma lem1239800 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : (term195 A B t l' Q) = (term111 A B Q t l').
Proof. exact (eq_refl (term195 A B t l' Q)). Qed.
Lemma lem1239801 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) : term111 A B Q t l'.
Proof. exact (EQ_MP (@lem1239800 A B Q t l') (@lem1239799 A B t l' Q)). Qed.
Lemma lem1239802 {A B : Type'} (Q : type1413 A B) (t : list A) (l' : list B) (h : A) : term196 A B Q t l' h.
Proof. exact (@lem1239801 A B Q t l' h). Qed.
Lemma lem1239803 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term196 A B Q t l' h) = (term107 A B h Q t l').
Proof. exact (eq_refl (term196 A B Q t l' h)). Qed.
Lemma lem1239804 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term107 A B h Q t l'.
Proof. exact (EQ_MP (@lem1239803 A B h Q t l') (@lem1239802 A B Q t l' h)). Qed.
Lemma lem1239805 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (P : type1413 A B) : term197 A B h Q t l' P.
Proof. exact (@lem1239804 A B h Q t l' P). Qed.
Lemma lem1239806 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : (term197 A B h Q t l' P) = (term93 A B P h Q t l').
Proof. exact (eq_refl (term197 A B h Q t l' P)). Qed.
Lemma lem1239807 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term93 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1239806 A B P h Q t l') (@lem1239805 A B h Q t l' P)). Qed.
Lemma lem1239809 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term93 A B P h Q t l'.
Proof. exact (@lem1238715 A B P h Q t l' (@lem1239807 A B P h Q t l')). Qed.
Lemma lem1239810 {A B : Type'} (h : A) (t : list A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term101 A B P h Q t l'.
Proof. exact (@lem1239809 A B P h Q t l' (@lem1238520 A B P Q h1)). Qed.
Lemma lem1239811 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term99 A B P h Q t l'.
Proof. exact (@lem1239810 A B h t l' P Q h1 (@lem1238548 A B P Q t h2)). Qed.
Lemma lem1239812 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term91 A B P h Q t l'.
Proof. exact (@lem1239811 A B h l' P Q t h1 h2 (@lem1238659 B l' h3)). Qed.
Lemma lem1239813 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') (h4 : term92 A B P h Q t l') : False.
Proof. exact (@lem1239812 A B h P Q t l' h1 h2 h3 (@lem1238699 A B P h Q t l' h4)). Qed.
Lemma lem1239814 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') (h4 : term92 A B P h Q t l') : (term92 A B P h Q t l') = False.
Proof. exact (prop_ext (fun h5 : term92 A B P h Q t l' => @lem1239813 A B P h Q t l' h1 h2 h3 h4) (fun h5 : False => @lem1238699 A B P h Q t l' h4)). Qed.
Lemma lem1239815 {A B : Type'} (P : type1413 A B) (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') (h4 : term92 A B P h Q t l') : False.
Proof. exact (EQ_MP (@lem1239814 A B P h Q t l' h1 h2 h3 h4) (@lem1238699 A B P h Q t l' h4)). Qed.
Lemma lem1239816 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term91 A B P h Q t l'.
Proof. exact (fun h0 : term92 A B P h Q t l' => @lem1239815 A B P h Q t l' h1 h2 h3 h0). Qed.
Lemma lem1239817 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term89 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1238698 A B P h Q t l') (@lem1239816 A B h P Q t l' h1 h2 h3)). Qed.
Lemma lem1239818 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term83 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1238694 A B P h Q t l') (@lem1239817 A B h P Q t l' h1 h2 h3)). Qed.
Lemma lem1239819 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term59 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1238674 A B P h Q t l' h3) (@lem1239818 A B h P Q t l' h1 h2 h3)). Qed.
Lemma lem1239820 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : (term78 B l') = (term59 A B P h Q t l').
Proof. exact (prop_ext (fun h4 : term78 B l' => @lem1239819 A B h P Q t l' h1 h2 h3) (fun h4 : term59 A B P h Q t l' => @lem1238659 B l' h3)). Qed.
Lemma lem1239821 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) (h3 : term78 B l') : term59 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1239820 A B h P Q t l' h1 h2 h3) (@lem1238659 B l' h3)). Qed.
Lemma lem1239822 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term62 A B P h Q t l'.
Proof. exact (fun h0 : term78 B l' => @lem1239821 A B h P Q t l' h1 h2 h0). Qed.
Lemma lem1239823 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : term64 A B h Q t l'.
Proof. exact (EQ_MP (@lem1238658 A B h Q t l' h1) (@lem1238679 A B h Q t l')). Qed.
Lemma lem1239824 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : (l' = (@nil B)) = (term64 A B h Q t l').
Proof. exact (prop_ext (fun h2 : l' = (@nil B) => @lem1239823 A B h Q t l' h1) (fun h2 : term64 A B h Q t l' => @lem1238643 B l' h1)). Qed.
Lemma lem1239825 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) (h1 : l' = (@nil B)) : term64 A B h Q t l'.
Proof. exact (EQ_MP (@lem1239824 A B h Q t l' h1) (@lem1238643 B l' h1)). Qed.
Lemma lem1239826 {A B : Type'} (h : A) (Q : type1413 A B) (t : list A) (l' : list B) : term66 A B h Q t l'.
Proof. exact (fun h0 : l' = (@nil B) => @lem1239825 A B h Q t l' h0). Qed.
Lemma lem1239827 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term69 A B P h Q t l'.
Proof. exact (conj (@lem1239826 A B h Q t l') (@lem1239822 A B h l' P Q t h1 h2)). Qed.
Lemma lem1239828 {A B : Type'} (h : A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term46 A B P h Q t l'.
Proof. exact (EQ_MP (@lem1238642 A B P h Q t l') (@lem1239827 A B h l' P Q t h1 h2)). Qed.
Lemma lem1239833 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term49 A B P h Q t.
Proof. exact (fun l' : list B => @lem1239828 A B h l' P Q t h1 h2). Qed.
Lemma lem1239834 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (t : list A) (h1 : term0 A B P Q) (h2 : term9 A B P Q t) : term13 A B P Q h t.
Proof. exact (EQ_MP (@lem1238624 A B P Q h t) (@lem1239833 A B h P Q t h1 h2)). Qed.
Lemma lem1239835 {A B : Type'} (h : A) (t : list A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term15 A B P Q h t.
Proof. exact (fun h0 : term9 A B P Q t => @lem1239834 A B h P Q t h1 h0). Qed.
Lemma lem1239840 {A B : Type'} (h : A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term19 A B P Q h.
Proof. exact (fun t : list A => @lem1239835 A B h t P Q h1). Qed.
Lemma lem1239845 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term23 A B P Q.
Proof. exact (fun h : A => @lem1239840 A B h P Q h1). Qed.
Lemma lem1239846 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term25 A B P Q.
Proof. exact (conj (@lem1238585 A B P Q) (@lem1239845 A B P Q h1)). Qed.
Lemma lem1239847 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term30 A B P Q.
Proof. exact (@lem1238547 A B P Q (@lem1239846 A B P Q h1)). Qed.
Lemma lem1239848 {A B : Type'} (l : list A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term8 A B P Q l.
Proof. exact (@lem1239847 A B P Q h1 l). Qed.
Lemma lem1239849 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l : list A) : (term8 A B P Q l) = (term9 A B P Q l).
Proof. exact (eq_refl (term8 A B P Q l)). Qed.
Lemma lem1239850 {A B : Type'} (l : list A) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term9 A B P Q l.
Proof. exact (EQ_MP (@lem1239849 A B P Q l) (@lem1239848 A B l P Q h1)). Qed.
Lemma lem1239851 {A B : Type'} (l : list A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term198 A B P Q l l'.
Proof. exact (@lem1239850 A B l P Q h1 l'). Qed.
Lemma lem1239852 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l : list A) (l' : list B) : (term198 A B P Q l l') = (term125 A B P Q l l').
Proof. exact (eq_refl (term198 A B P Q l l')). Qed.
Lemma lem1239853 {A B : Type'} (l : list A) (l' : list B) (P : type1413 A B) (Q : type1413 A B) (h1 : term0 A B P Q) : term125 A B P Q l l'.
Proof. exact (EQ_MP (@lem1239852 A B P Q l l') (@lem1239851 A B l l' P Q h1)). Qed.
Lemma lem1239854 {A B : Type'} (P : type1413 A B) (Q : type1413 A B) (l : list A) (l' : list B) : term199 A B P Q l l'.
Proof. exact (fun h0 : term0 A B P Q => @lem1239853 A B l l' P Q h0). Qed.
