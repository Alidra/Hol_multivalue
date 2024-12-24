Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_RELATED_NONEMPTY_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_SING_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5809500 {A : Type'} (t : A -> Prop) : term0 A t.
Proof. exact (@lem9784 (t = (@EMPTY A))). Qed.
Lemma lem5809501 {A : Type'} (t : A -> Prop) : (term0 A t) = (term1 A t).
Proof. exact (eq_refl (term0 A t)). Qed.
Lemma lem5809502 {A : Type'} (t : A -> Prop) : term1 A t.
Proof. exact (EQ_MP (@lem5809501 A t) (@lem5809500 A t)). Qed.
Lemma lem5809504 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : term2 A t.
Proof. exact (h1). Qed.
Lemma lem5809505 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem5809506 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5809507 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5809506 A x) (@lem5809505 A x)). Qed.
Lemma lem5809508 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (@lem5809507 A x s). Qed.
Lemma lem5809509 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem5809510 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (EQ_MP (@lem5809509 A x s) (@lem5809508 A x s)). Qed.
Lemma lem5809511 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem5809524 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5809525 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem5809526 {A : Type'} (x : A) : term9 A x.
Proof. exact (EQ_MP (@lem5809525 A x) (@lem5809524 A x)). Qed.
Lemma lem5809527 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5809529 {_83983 : Type'} (P : _83983 -> Prop) : term11 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5809530 {_83983 : Type'} (P : _83983 -> Prop) : (term11 _83983 P) = (term12 _83983 P).
Proof. exact (eq_refl (term11 _83983 P)). Qed.
Lemma lem5809531 {_83983 : Type'} (P : _83983 -> Prop) : term12 _83983 P.
Proof. exact (EQ_MP (@lem5809530 _83983 P) (@lem5809529 _83983 P)). Qed.
Lemma lem5809532 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term13 _83983 P a.
Proof. exact (@lem5809531 _83983 P a). Qed.
Lemma lem5809533 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term13 _83983 P a) = (term14 _83983 a P).
Proof. exact (eq_refl (term13 _83983 P a)). Qed.
Lemma lem5809534 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term14 _83983 a P.
Proof. exact (EQ_MP (@lem5809533 _83983 a P) (@lem5809532 _83983 P a)). Qed.
Lemma lem5809535 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term15 _83983 a P s.
Proof. exact (@lem5809534 _83983 a P s). Qed.
Lemma lem5809536 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term15 _83983 a P s) = ((term16 _83983 a s P) = (term17 _83983 a s P)).
Proof. exact (eq_refl (term15 _83983 a P s)). Qed.
Lemma lem5809538 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem5809539 {A : Type'} (P : type686 A) (h1 : term18 A) : term19 A P.
Proof. exact (@lem5809538 A h1 P). Qed.
Lemma lem5809540 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem5809541 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (EQ_MP (@lem5809540 A P) (@lem5809539 A P h1)). Qed.
Lemma lem5809542 {A : Type'} (P : type686 A) (h1 : term21 A P) : term21 A P.
Proof. exact (h1). Qed.
Lemma lem5809543 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem5809541 A P h1 (@lem5809542 A P h2)). Qed.
Lemma lem5809544 {A : Type'} (P : type686 A) (h1 : term21 A P) : term23 A P.
Proof. exact (fun h0 : term18 A => @lem5809543 A P h0 h1). Qed.
Lemma lem5809545 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem5809546 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem5809544 A P h2 (@lem5809545 A h1)). Qed.
Lemma lem5809547 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (fun h0 : term21 A P => @lem5809546 A P h1 h0). Qed.
Lemma lem5809548 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (fun P : type686 A => @lem5809547 A P h1). Qed.
Lemma lem5809549 {A : Type'} : term24 A.
Proof. exact (fun h0 : term18 A => @lem5809548 A h0). Qed.
Lemma lem5809550 {A : Type'} : term18 A.
Proof. exact (@lem5809549 A (@lem3558722 A)). Qed.
Lemma lem5809551 {A : Type'} (P : type686 A) : term19 A P.
Proof. exact (@lem5809550 A P). Qed.
Lemma lem5809552 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem5809554 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5809555 {B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term25 B R op.
Proof. exact (h1). Qed.
Lemma lem5809561 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5809562 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term28 A B R f op s g) = (term29 A B R f op s g).
Proof. exact (@lem5809561 (@FINITE A s) (term30 A B s R f g) (term31 A B R f op s g)). Qed.
Lemma lem5809566 (p : Prop) (q : Prop) (r : Prop) : (term26 p q r) = (term27 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5809567 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term32 A B R f op s g) = (term33 A B R f op s g).
Proof. exact (@lem5809566 (term2 A s) (term34 A B s R f g) (term31 A B R f op s g)). Qed.
Lemma lem5809580 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5809581 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term29 A B R f op s g) = (term36 A B R f op s g).
Proof. exact (MK_COMB (@lem5809580 A s) (@lem5809567 A B R f op s g)). Qed.
Lemma lem5809584 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term28 A B R f op s g) = (term36 A B R f op s g).
Proof. exact (TRANS (@lem5809562 A B R f op s g) (@lem5809581 A B R f op s g)). Qed.
Lemma lem5809585 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term37 A B R f op g) = (term38 A B R f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5809584 A B R f op s g)). Qed.
Lemma lem5809586 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5809587 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term39 A B R f op g) = (term40 A B R f op g).
Proof. exact (MK_COMB (@lem5809586 A) (@lem5809585 A B R f op g)). Qed.
Lemma lem5809592 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term40 A B R f op g) = (term39 A B R f op g).
Proof. exact (SYM (@lem5809587 A B R f op g)). Qed.
Lemma lem5809594 {A : Type'} (P : type686 A) : term20 A P.
Proof. exact (EQ_MP (@lem5809552 A P) (@lem5809551 A P)). Qed.
Lemma lem5809595 {A : Type'} (P : type686 A) : term20 A P.
Proof. exact (@lem5809594 A P). Qed.
Lemma lem5809596 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : term41 A B R f op g.
Proof. exact (@lem5809595 A (term42 A B R f op g)). Qed.
Lemma lem5809597 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term43 A B R f op g) = (term44 A B R f op g).
Proof. exact (eq_refl (term43 A B R f op g)). Qed.
Lemma lem5809598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809599 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term45 A B R f op g) = (term46 A B R f op g).
Proof. exact (MK_COMB (@lem5809598) (@lem5809597 A B R f op g)). Qed.
Lemma lem5809600 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term47 A B R f op g s) = (term33 A B R f op s g).
Proof. exact (eq_refl (term47 A B R f op g s)). Qed.
Lemma lem5809601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809602 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term48 A B R f op g s) = (term49 A B R f op s g).
Proof. exact (MK_COMB (@lem5809601) (@lem5809600 A B R f op s g)). Qed.
Lemma lem5809603 {A : Type'} (x : A) (s : A -> Prop) : (term50 A x s) = (term50 A x s).
Proof. exact (eq_refl (term50 A x s)). Qed.
Lemma lem5809604 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term51 A B R f op g x s) = (term52 A B R f op g x s).
Proof. exact (MK_COMB (@lem5809602 A B R f op s g) (@lem5809603 A x s)). Qed.
Lemma lem5809605 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809606 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term53 A B R f op g x s) = (term54 A B R f op g x s).
Proof. exact (MK_COMB (@lem5809605) (@lem5809604 A B R f op g x s)). Qed.
Lemma lem5809607 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term55 A B R f op g x s) = (term56 A B R f op x s g).
Proof. exact (eq_refl (term55 A B R f op g x s)). Qed.
Lemma lem5809608 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term57 A B R f op g x s) = (term58 A B R f op x s g).
Proof. exact (MK_COMB (@lem5809606 A B R f op g x s) (@lem5809607 A B R f op x s g)). Qed.
Lemma lem5809609 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term59 A B R f op g x) = (term60 A B R f op x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5809608 A B R f op x s g)). Qed.
Lemma lem5809610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5809611 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term61 A B R f op g x) = (term62 A B R f op x g).
Proof. exact (MK_COMB (@lem5809610 A) (@lem5809609 A B R f op x g)). Qed.
Lemma lem5809612 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term63 A B R f op g) = (term64 A B R f op g).
Proof. exact (fun_ext (fun x : A => @lem5809611 A B R f op x g)). Qed.
Lemma lem5809613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809614 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term65 A B R f op g) = (term66 A B R f op g).
Proof. exact (MK_COMB (@lem5809613 A) (@lem5809612 A B R f op g)). Qed.
Lemma lem5809615 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term67 A B R f op g) = (term68 A B R f op g).
Proof. exact (MK_COMB (@lem5809599 A B R f op g) (@lem5809614 A B R f op g)). Qed.
Lemma lem5809616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809617 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term69 A B R f op g) = (term70 A B R f op g).
Proof. exact (MK_COMB (@lem5809616) (@lem5809615 A B R f op g)). Qed.
Lemma lem5809618 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term47 A B R f op g s) = (term33 A B R f op s g).
Proof. exact (eq_refl (term47 A B R f op g s)). Qed.
Lemma lem5809619 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5809620 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term71 A B R f op g s) = (term36 A B R f op s g).
Proof. exact (MK_COMB (@lem5809619 A s) (@lem5809618 A B R f op s g)). Qed.
Lemma lem5809621 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term72 A B R f op g) = (term38 A B R f op g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5809620 A B R f op s g)). Qed.
Lemma lem5809622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5809623 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term73 A B R f op g) = (term40 A B R f op g).
Proof. exact (MK_COMB (@lem5809622 A) (@lem5809621 A B R f op g)). Qed.
Lemma lem5809624 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term41 A B R f op g) = (term74 A B R f op g).
Proof. exact (MK_COMB (@lem5809617 A B R f op g) (@lem5809623 A B R f op g)). Qed.
Lemma lem5809625 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : term74 A B R f op g.
Proof. exact (EQ_MP (@lem5809624 A B R f op g) (@lem5809596 A B R f op g)). Qed.
Lemma lem5809631 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5809632 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem5809631 (A -> Prop) x). Qed.
Lemma lem5809633 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem5809632 A (@EMPTY A)). Qed.
Lemma lem5809634 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5809635 {A : Type'} : (term75 A) = (~ True).
Proof. exact (MK_COMB (@lem5809634) (@lem5809633 A)). Qed.
Lemma lem5809637 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5809638 {A : Type'} : (term75 A) = False.
Proof. exact (TRANS (@lem5809635 A) (@lem5809637)). Qed.
Lemma lem5809639 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809640 {A : Type'} : (term76 A) = (imp False).
Proof. exact (MK_COMB (@lem5809639) (@lem5809638 A)). Qed.
Lemma lem5809650 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5809527 A x (@lem5809526 A x)). Qed.
Lemma lem5809651 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5809650 A x). Qed.
Lemma lem5809652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809653 {A : Type'} (x : A) : (term77 A x) = (imp False).
Proof. exact (MK_COMB (@lem5809652) (@lem5809651 A x)). Qed.
Lemma lem5809654 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term78 A B R f g x) = (term78 A B R f g x).
Proof. exact (eq_refl (term78 A B R f g x)). Qed.
Lemma lem5809655 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term79 A B R f g x) = (term80 A B R f g x).
Proof. exact (MK_COMB (@lem5809653 A x) (@lem5809654 A B R f g x)). Qed.
Lemma lem5809657 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5809658 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term80 A B R f g x) = True.
Proof. exact (@lem5809657 (term78 A B R f g x)). Qed.
Lemma lem5809659 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term79 A B R f g x) = True.
Proof. exact (TRANS (@lem5809655 A B R f g x) (@lem5809658 A B R f g x)). Qed.
Lemma lem5809660 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term81 A B R f g) = (term82 A).
Proof. exact (fun_ext (fun x : A => @lem5809659 A B R f g x)). Qed.
Lemma lem5809661 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809662 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term83 A B R f g) = (term84 A).
Proof. exact (MK_COMB (@lem5809661 A) (@lem5809660 A B R f g)). Qed.
Lemma lem5809664 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5809665 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem5809664 A t). Qed.
Lemma lem5809666 {A : Type'} : (term84 A) = True.
Proof. exact (@lem5809665 A True). Qed.
Lemma lem5809667 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term83 A B R f g) = True.
Proof. exact (TRANS (@lem5809662 A B R f g) (@lem5809666 A)). Qed.
Lemma lem5809668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809669 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) : (term86 A B R f g) = (imp True).
Proof. exact (MK_COMB (@lem5809668) (@lem5809667 A B R f g)). Qed.
Lemma lem5809670 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term87 A B R f op g) = (term87 A B R f op g).
Proof. exact (eq_refl (term87 A B R f op g)). Qed.
Lemma lem5809671 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term88 A B R f op g) = (term89 A B R f op g).
Proof. exact (MK_COMB (@lem5809669 A B R f g) (@lem5809670 A B R f op g)). Qed.
Lemma lem5809673 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5809674 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term89 A B R f op g) = (term87 A B R f op g).
Proof. exact (@lem5809673 (term87 A B R f op g)). Qed.
Lemma lem5809675 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term88 A B R f op g) = (term87 A B R f op g).
Proof. exact (TRANS (@lem5809671 A B R f op g) (@lem5809674 A B R f op g)). Qed.
Lemma lem5809676 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term44 A B R f op g) = (term90 A B R f op g).
Proof. exact (MK_COMB (@lem5809640 A) (@lem5809675 A B R f op g)). Qed.
Lemma lem5809678 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5809679 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term90 A B R f op g) = True.
Proof. exact (@lem5809678 (term87 A B R f op g)). Qed.
Lemma lem5809680 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term44 A B R f op g) = True.
Proof. exact (TRANS (@lem5809676 A B R f op g) (@lem5809679 A B R f op g)). Qed.
Lemma lem5809681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809682 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term46 A B R f op g) = (and True).
Proof. exact (MK_COMB (@lem5809681) (@lem5809680 A B R f op g)). Qed.
Lemma lem5809712 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5809511 A x s (@lem5809510 A x s)). Qed.
Lemma lem5809713 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem5809712 A x s). Qed.
Lemma lem5809714 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5809715 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (~ False).
Proof. exact (MK_COMB (@lem5809714) (@lem5809713 A x s)). Qed.
Lemma lem5809717 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5809718 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = True.
Proof. exact (TRANS (@lem5809715 A x s) (@lem5809717)). Qed.
Lemma lem5809719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809720 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = (imp True).
Proof. exact (MK_COMB (@lem5809719) (@lem5809718 A x s)). Qed.
Lemma lem5809724 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term16 _83983 a s P) = (term17 _83983 a s P).
Proof. exact (EQ_MP (@lem5809536 _83983 a s P) (@lem5809535 _83983 a P s)). Qed.
Lemma lem5809725 {A : Type'} (a : A) (s : A -> Prop) (P : A -> Prop) : (term16 A a s P) = (term17 A a s P).
Proof. exact (@lem5809724 A a s P). Qed.
Lemma lem5809726 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term92 A B x s R f g) = (term93 A B x s R f g).
Proof. exact (@lem5809725 A x s (term94 A B R f g)). Qed.
Lemma lem5809727 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term95 A B R f g x') = (term78 A B R f g x').
Proof. exact (eq_refl (term95 A B R f g x')). Qed.
Lemma lem5809728 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term96 A x' x s) = (term96 A x' x s).
Proof. exact (eq_refl (term96 A x' x s)). Qed.
Lemma lem5809729 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term97 A B x s R f g x') = (term98 A B x s R f g x').
Proof. exact (MK_COMB (@lem5809728 A x' x s) (@lem5809727 A B R f g x')). Qed.
Lemma lem5809730 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term99 A B x s R f g) = (term100 A B x s R f g).
Proof. exact (fun_ext (fun x' : A => @lem5809729 A B x s R f g x')). Qed.
Lemma lem5809731 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809732 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term92 A B x s R f g) = (term101 A B x s R f g).
Proof. exact (MK_COMB (@lem5809731 A) (@lem5809730 A B x s R f g)). Qed.
Lemma lem5809733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5809734 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term102 A B x s R f g) = (term103 A B x s R f g).
Proof. exact (MK_COMB (@lem5809733) (@lem5809732 A B x s R f g)). Qed.
Lemma lem5809735 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term95 A B R f g x) = (term78 A B R f g x).
Proof. exact (eq_refl (term95 A B R f g x)). Qed.
Lemma lem5809736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5809737 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term104 A B R f g x) = (term105 A B R f g x).
Proof. exact (MK_COMB (@lem5809736) (@lem5809735 A B R f g x)). Qed.
Lemma lem5809738 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term95 A B R f g x') = (term78 A B R f g x').
Proof. exact (eq_refl (term95 A B R f g x')). Qed.
Lemma lem5809739 {A : Type'} (x' : A) (s : A -> Prop) : (term106 A x' s) = (term106 A x' s).
Proof. exact (eq_refl (term106 A x' s)). Qed.
Lemma lem5809740 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term107 A B s R f g x') = (term108 A B s R f g x').
Proof. exact (MK_COMB (@lem5809739 A x' s) (@lem5809738 A B R f g x')). Qed.
Lemma lem5809741 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term109 A B s R f g) = (term110 A B s R f g).
Proof. exact (fun_ext (fun x' : A => @lem5809740 A B s R f g x')). Qed.
Lemma lem5809742 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809743 {A B : Type'} (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term111 A B s R f g) = (term34 A B s R f g).
Proof. exact (MK_COMB (@lem5809742 A) (@lem5809741 A B s R f g)). Qed.
Lemma lem5809744 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term93 A B x s R f g) = (term112 A B x s R f g).
Proof. exact (MK_COMB (@lem5809737 A B R f g x) (@lem5809743 A B s R f g)). Qed.
Lemma lem5809745 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : ((term92 A B x s R f g) = (term93 A B x s R f g)) = ((term101 A B x s R f g) = (term112 A B x s R f g)).
Proof. exact (MK_COMB (@lem5809734 A B x s R f g) (@lem5809744 A B x s R f g)). Qed.
Lemma lem5809746 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term101 A B x s R f g) = (term112 A B x s R f g).
Proof. exact (EQ_MP (@lem5809745 A B x s R f g) (@lem5809726 A B x s R f g)). Qed.
Lemma lem5809755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5809756 {A B : Type'} (x : A) (s : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term113 A B x s R f g) = (term114 A B x s R f g).
Proof. exact (MK_COMB (@lem5809755) (@lem5809746 A B x s R f g)). Qed.
Lemma lem5809757 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term115 A B R f op x s g) = (term115 A B R f op x s g).
Proof. exact (eq_refl (term115 A B R f op x s g)). Qed.
Lemma lem5809758 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term116 A B R f op x s g) = (term117 A B R f op x s g).
Proof. exact (MK_COMB (@lem5809756 A B x s R f g) (@lem5809757 A B R f op x s g)). Qed.
Lemma lem5809761 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term56 A B R f op x s g) = (term118 A B R f op x s g).
Proof. exact (MK_COMB (@lem5809720 A x s) (@lem5809758 A B R f op x s g)). Qed.
Lemma lem5809763 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5809764 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term118 A B R f op x s g) = (term117 A B R f op x s g).
Proof. exact (@lem5809763 (term117 A B R f op x s g)). Qed.
Lemma lem5809775 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term56 A B R f op x s g) = (term117 A B R f op x s g).
Proof. exact (TRANS (@lem5809761 A B R f op x s g) (@lem5809764 A B R f op x s g)). Qed.
Lemma lem5809776 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (s : A -> Prop) : (term54 A B R f op g x s) = (term54 A B R f op g x s).
Proof. exact (eq_refl (term54 A B R f op g x s)). Qed.
Lemma lem5809777 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (s : A -> Prop) (g : A -> B) : (term58 A B R f op x s g) = (term119 A B R f op x s g).
Proof. exact (MK_COMB (@lem5809776 A B R f op g x s) (@lem5809775 A B R f op x s g)). Qed.
Lemma lem5809780 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term60 A B R f op x g) = (term120 A B R f op x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5809777 A B R f op x s g)). Qed.
Lemma lem5809781 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5809782 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term62 A B R f op x g) = (term121 A B R f op x g).
Proof. exact (MK_COMB (@lem5809781 A) (@lem5809780 A B R f op x g)). Qed.
Lemma lem5809787 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term64 A B R f op g) = (term122 A B R f op g).
Proof. exact (fun_ext (fun x : A => @lem5809782 A B R f op x g)). Qed.
Lemma lem5809788 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5809789 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term66 A B R f op g) = (term123 A B R f op g).
Proof. exact (MK_COMB (@lem5809788 A) (@lem5809787 A B R f op g)). Qed.
Lemma lem5809794 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term68 A B R f op g) = (term124 A B R f op g).
Proof. exact (MK_COMB (@lem5809682 A B R f op g) (@lem5809789 A B R f op g)). Qed.
Lemma lem5809796 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5809797 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term124 A B R f op g) = (term123 A B R f op g).
Proof. exact (@lem5809796 (term123 A B R f op g)). Qed.
Lemma lem5809834 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term68 A B R f op g) = (term123 A B R f op g).
Proof. exact (TRANS (@lem5809794 A B R f op g) (@lem5809797 A B R f op g)). Qed.
Lemma lem5809835 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term123 A B R f op g) = (term68 A B R f op g).
Proof. exact (SYM (@lem5809834 A B R f op g)). Qed.
Lemma lem5809836 {A B : Type'} (op : type1400 B) : term125 A B op.
Proof. exact (@lem5807175 A B op). Qed.
Lemma lem5809837 {A B : Type'} (op : type1400 B) : (term125 A B op) = (term126 A B op).
Proof. exact (eq_refl (term125 A B op)). Qed.
Lemma lem5809838 {A B : Type'} (op : type1400 B) : term126 A B op.
Proof. exact (EQ_MP (@lem5809837 A B op) (@lem5809836 A B op)). Qed.
Lemma lem5809839 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5809840 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term127 A B op.
Proof. exact (@lem5809838 A B op (@lem5809839 B op h1)). Qed.
Lemma lem5809841 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term128 A B op f.
Proof. exact (@lem5809840 A B op h1 f). Qed.
Lemma lem5809842 {A B : Type'} (op : type1400 B) (f : A -> B) : (term128 A B op f) = (term129 A B op f).
Proof. exact (eq_refl (term128 A B op f)). Qed.
Lemma lem5809843 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term129 A B op f.
Proof. exact (EQ_MP (@lem5809842 A B op f) (@lem5809841 A B f op h1)). Qed.
Lemma lem5809844 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term130 A B op f x.
Proof. exact (@lem5809843 A B f op h1 x). Qed.
Lemma lem5809845 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term130 A B op f x) = ((term131 A B op x f) = (f x)).
Proof. exact (eq_refl (term130 A B op f x)). Qed.
Lemma lem5809846 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term131 A B op x f) = (f x).
Proof. exact (EQ_MP (@lem5809845 A B op f x) (@lem5809844 A B f x op h1)). Qed.
Lemma lem5809852 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5809878 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809879 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809878 p q p' q'). Qed.
Lemma lem5809880 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809879 p q p'). Qed.
Lemma lem5809881 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term135 A B R f op a t g.
Proof. exact (@lem5809880 (term52 A B R f op g a t) (term117 A B R f op a t g)). Qed.
Lemma lem5809882 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term136 A B R f op a t g p'.
Proof. exact (@lem5809881 A B R f op a t g p'). Qed.
Lemma lem5809883 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term136 A B R f op a t g p') = (term137 A B R f op a t g p').
Proof. exact (eq_refl (term136 A B R f op a t g p')). Qed.
Lemma lem5809884 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term137 A B R f op a t g p'.
Proof. exact (EQ_MP (@lem5809883 A B R f op a t g p') (@lem5809882 A B R f op a t g p')). Qed.
Lemma lem5809885 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term138 A B R f op a t g p' q'.
Proof. exact (@lem5809884 A B R f op a t g p' q'). Qed.
Lemma lem5809886 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term138 A B R f op a t g p' q') = (term139 A B R f op a t g p' q').
Proof. exact (eq_refl (term138 A B R f op a t g p' q')). Qed.
Lemma lem5809887 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term139 A B R f op a t g p' q'.
Proof. exact (EQ_MP (@lem5809886 A B R f op a t g p' q') (@lem5809885 A B R f op a t g p' q')). Qed.
Lemma lem5809893 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809894 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809893 p q p' q'). Qed.
Lemma lem5809895 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809894 p q p'). Qed.
Lemma lem5809896 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term140 A B R f op t g.
Proof. exact (@lem5809895 (term2 A t) (term141 A B R f op t g)). Qed.
Lemma lem5809897 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term142 A B R f op t g p'.
Proof. exact (@lem5809896 A B R f op t g p'). Qed.
Lemma lem5809898 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term142 A B R f op t g p') = (term143 A B R f op t g p').
Proof. exact (eq_refl (term142 A B R f op t g p')). Qed.
Lemma lem5809899 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term143 A B R f op t g p'.
Proof. exact (EQ_MP (@lem5809898 A B R f op t g p') (@lem5809897 A B R f op t g p')). Qed.
Lemma lem5809900 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term144 A B R f op t g p' q'.
Proof. exact (@lem5809899 A B R f op t g p' q'). Qed.
Lemma lem5809901 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term144 A B R f op t g p' q') = (term145 A B R f op t g p' q').
Proof. exact (eq_refl (term144 A B R f op t g p' q')). Qed.
Lemma lem5809902 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term145 A B R f op t g p' q'.
Proof. exact (EQ_MP (@lem5809901 A B R f op t g p' q') (@lem5809900 A B R f op t g p' q')). Qed.
Lemma lem5809906 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5809907 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem5809908 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@eq (A -> Prop) t) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem5809907 A) (@lem5809906 A t h1)). Qed.
Lemma lem5809909 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem5809910 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (t = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem5809908 A t h1) (@lem5809909 A)). Qed.
Lemma lem5809912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5809913 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem5809912 (A -> Prop) x). Qed.
Lemma lem5809914 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem5809913 A (@EMPTY A)). Qed.
Lemma lem5809915 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (t = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem5809910 A t h1) (@lem5809914 A)). Qed.
Lemma lem5809916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5809917 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term2 A t) = (~ True).
Proof. exact (MK_COMB (@lem5809916) (@lem5809915 A t h1)). Qed.
Lemma lem5809919 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5809920 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term2 A t) = False.
Proof. exact (TRANS (@lem5809917 A t h1) (@lem5809919)). Qed.
Lemma lem5809921 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (q' : Prop) : term146 A B R f op t g q'.
Proof. exact (@lem5809902 A B R f op t g False q'). Qed.
Lemma lem5809922 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term147 A B R f op t g q'.
Proof. exact (@lem5809921 A B R f op t g q' (@lem5809920 A t h1)). Qed.
Lemma lem5809929 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809930 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809929 p q p' q'). Qed.
Lemma lem5809931 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809930 p q p'). Qed.
Lemma lem5809932 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term148 A B R f op t g.
Proof. exact (@lem5809931 (term34 A B t R f g) (term31 A B R f op t g)). Qed.
Lemma lem5809933 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term149 A B R f op t g p'.
Proof. exact (@lem5809932 A B R f op t g p'). Qed.
Lemma lem5809934 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term149 A B R f op t g p') = (term150 A B R f op t g p').
Proof. exact (eq_refl (term149 A B R f op t g p')). Qed.
Lemma lem5809935 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term150 A B R f op t g p'.
Proof. exact (EQ_MP (@lem5809934 A B R f op t g p') (@lem5809933 A B R f op t g p')). Qed.
Lemma lem5809936 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term151 A B R f op t g p' q'.
Proof. exact (@lem5809935 A B R f op t g p' q'). Qed.
Lemma lem5809937 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term151 A B R f op t g p' q') = (term152 A B R f op t g p' q').
Proof. exact (eq_refl (term151 A B R f op t g p' q')). Qed.
Lemma lem5809938 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term152 A B R f op t g p' q'.
Proof. exact (EQ_MP (@lem5809937 A B R f op t g p' q') (@lem5809936 A B R f op t g p' q')). Qed.
Lemma lem5809946 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5809947 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5809946 p q p' q'). Qed.
Lemma lem5809948 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5809947 p q p'). Qed.
Lemma lem5809949 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : term153 A B t R f g x.
Proof. exact (@lem5809948 (@IN A x t) (term78 A B R f g x)). Qed.
Lemma lem5809950 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term154 A B t R f g x p'.
Proof. exact (@lem5809949 A B t R f g x p'). Qed.
Lemma lem5809951 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : (term154 A B t R f g x p') = (term155 A B t R f g x p').
Proof. exact (eq_refl (term154 A B t R f g x p')). Qed.
Lemma lem5809952 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term155 A B t R f g x p'.
Proof. exact (EQ_MP (@lem5809951 A B t R f g x p') (@lem5809950 A B t R f g x p')). Qed.
Lemma lem5809953 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term156 A B t R f g x p' q'.
Proof. exact (@lem5809952 A B t R f g x p' q'). Qed.
Lemma lem5809954 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term156 A B t R f g x p' q') = (term157 A B t R f g x p' q').
Proof. exact (eq_refl (term156 A B t R f g x p' q')). Qed.
Lemma lem5809955 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term157 A B t R f g x p' q'.
Proof. exact (EQ_MP (@lem5809954 A B t R f g x p' q') (@lem5809953 A B t R f g x p' q')). Qed.
Lemma lem5809957 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5809958 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5809959 {A : Type'} (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A x t) = (@IN A x (@EMPTY A)).
Proof. exact (MK_COMB (@lem5809958 A x) (@lem5809957 A t h1)). Qed.
Lemma lem5809960 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (q' : Prop) : term158 A B t R f g x q'.
Proof. exact (@lem5809955 A B t R f g x (@IN A x (@EMPTY A)) q'). Qed.
Lemma lem5809961 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term159 A B t R f g x q'.
Proof. exact (@lem5809960 A B t R f g x q' (@lem5809959 A x t h1)). Qed.
Lemma lem5809965 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : (term78 A B R f g x) = (term78 A B R f g x).
Proof. exact (eq_refl (term78 A B R f g x)). Qed.
Lemma lem5809966 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : term160 A B R f g x.
Proof. exact (fun h0 : @IN A x (@EMPTY A) => @lem5809965 A B R f g x). Qed.
Lemma lem5809967 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term161 A B t R f g x.
Proof. exact (@lem5809961 A B R f g x (term78 A B R f g x) t h1). Qed.
Lemma lem5809968 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term108 A B t R f g x) = (term79 A B R f g x).
Proof. exact (@lem5809967 A B R f g x t h1 (@lem5809966 A B R f g x)). Qed.
Lemma lem5809992 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term110 A B t R f g) = (term81 A B R f g).
Proof. exact (fun_ext (fun x : A => @lem5809968 A B R f g x t h1)). Qed.
Lemma lem5810016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5810017 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term34 A B t R f g) = (term83 A B R f g).
Proof. exact (MK_COMB (@lem5810016 A) (@lem5809992 A B R f g t h1)). Qed.
Lemma lem5810045 {A B : Type'} (op : type1400 B) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term162 A B op t R f g q'.
Proof. exact (@lem5809938 A B R f op t g (term83 A B R f g) q'). Qed.
Lemma lem5810046 {A B : Type'} (op : type1400 B) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term163 A B op t R f g q'.
Proof. exact (@lem5810045 A B op t R f g q' (@lem5810017 A B R f g t h1)). Qed.
Lemma lem5810061 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810062 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5810063 {A B : Type'} (op : type1400 B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t) = (@iterate B A op (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810062 A B op) (@lem5810061 A t h1)). Qed.
Lemma lem5810064 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5810065 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t f) = (@iterate B A op (@EMPTY A) f).
Proof. exact (MK_COMB (@lem5810063 A B op t h1) (@lem5810064 A B f)). Qed.
Lemma lem5810066 {B : Type'} (R : type1402 B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem5810067 {A B : Type'} (R : type1402 B) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term164 A B R op t f) = (term165 A B R op f).
Proof. exact (MK_COMB (@lem5810066 B R) (@lem5810065 A B op f t h1)). Qed.
Lemma lem5810069 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810070 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5810071 {A B : Type'} (op : type1400 B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t) = (@iterate B A op (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810070 A B op) (@lem5810069 A t h1)). Qed.
Lemma lem5810072 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5810073 {A B : Type'} (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@iterate B A op t g) = (@iterate B A op (@EMPTY A) g).
Proof. exact (MK_COMB (@lem5810071 A B op t h1) (@lem5810072 A B g)). Qed.
Lemma lem5810074 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term31 A B R f op t g) = (term87 A B R f op g).
Proof. exact (MK_COMB (@lem5810067 A B R op f t h1) (@lem5810073 A B op g t h1)). Qed.
Lemma lem5810075 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term166 A B t R f op g.
Proof. exact (fun h0 : term83 A B R f g => @lem5810074 A B R f op g t h1). Qed.
Lemma lem5810076 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term167 A B t R f op g.
Proof. exact (@lem5810046 A B op R f g (term87 A B R f op g) t h1). Qed.
Lemma lem5810077 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term141 A B R f op t g) = (term88 A B R f op g).
Proof. exact (@lem5810076 A B R f op g t h1 (@lem5810075 A B R f op g t h1)). Qed.
Lemma lem5810165 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term168 A B t R f op g.
Proof. exact (fun h0 : False => @lem5810077 A B R f op g t h1). Qed.
Lemma lem5810166 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term169 A B t R f op g.
Proof. exact (@lem5809922 A B R f op g (term88 A B R f op g) t h1). Qed.
Lemma lem5810167 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term33 A B R f op t g) = (term170 A B R f op g).
Proof. exact (@lem5810166 A B R f op g t h1 (@lem5810165 A B R f op g t h1)). Qed.
Lemma lem5810169 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5810170 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) : (term170 A B R f op g) = True.
Proof. exact (@lem5810169 (term88 A B R f op g)). Qed.
Lemma lem5810171 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term33 A B R f op t g) = True.
Proof. exact (TRANS (@lem5810167 A B R f op g t h1) (@lem5810170 A B R f op g)). Qed.
Lemma lem5810172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5810173 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term49 A B R f op t g) = (and True).
Proof. exact (MK_COMB (@lem5810172) (@lem5810171 A B R f op g t h1)). Qed.
Lemma lem5810177 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810178 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem5810179 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A a t) = (@IN A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810178 A a) (@lem5810177 A t h1)). Qed.
Lemma lem5810180 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5810181 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term171 A a t) = (term9 A a).
Proof. exact (MK_COMB (@lem5810180) (@lem5810179 A a t h1)). Qed.
Lemma lem5810182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5810183 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term172 A a t) = (term173 A a).
Proof. exact (MK_COMB (@lem5810182) (@lem5810181 A a t h1)). Qed.
Lemma lem5810185 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810186 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5810187 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@FINITE A t) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810186 A) (@lem5810185 A t h1)). Qed.
Lemma lem5810188 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term50 A a t) = (term174 A a).
Proof. exact (MK_COMB (@lem5810183 A a t h1) (@lem5810187 A t h1)). Qed.
Lemma lem5810191 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term52 A B R f op g a t) = (term175 A a).
Proof. exact (MK_COMB (@lem5810173 A B R f op g t h1) (@lem5810188 A a t h1)). Qed.
Lemma lem5810193 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5810194 {A : Type'} (a : A) : (term175 A a) = (term174 A a).
Proof. exact (@lem5810193 (term174 A a)). Qed.
Lemma lem5810197 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term52 A B R f op g a t) = (term174 A a).
Proof. exact (TRANS (@lem5810191 A B R f op g a t h1) (@lem5810194 A a)). Qed.
Lemma lem5810198 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (a : A) (q' : Prop) : term176 A B R f op t g a q'.
Proof. exact (@lem5809887 A B R f op a t g (term174 A a) q'). Qed.
Lemma lem5810199 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term177 A B R f op t g a q'.
Proof. exact (@lem5810198 A B R f op t g a q' (@lem5810197 A B R f op g a t h1)). Qed.
Lemma lem5810210 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5810211 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5810210 p q p' q'). Qed.
Lemma lem5810212 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5810211 p q p'). Qed.
Lemma lem5810213 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term178 A B R f op a t g.
Proof. exact (@lem5810212 (term112 A B a t R f g) (term115 A B R f op a t g)). Qed.
Lemma lem5810214 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term179 A B R f op a t g p'.
Proof. exact (@lem5810213 A B R f op a t g p'). Qed.
Lemma lem5810215 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term179 A B R f op a t g p') = (term180 A B R f op a t g p').
Proof. exact (eq_refl (term179 A B R f op a t g p')). Qed.
Lemma lem5810216 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term180 A B R f op a t g p'.
Proof. exact (EQ_MP (@lem5810215 A B R f op a t g p') (@lem5810214 A B R f op a t g p')). Qed.
Lemma lem5810217 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term181 A B R f op a t g p' q'.
Proof. exact (@lem5810216 A B R f op a t g p' q'). Qed.
Lemma lem5810218 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term181 A B R f op a t g p' q') = (term182 A B R f op a t g p' q').
Proof. exact (eq_refl (term181 A B R f op a t g p' q')). Qed.
Lemma lem5810219 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term182 A B R f op a t g p' q'.
Proof. exact (EQ_MP (@lem5810218 A B R f op a t g p' q') (@lem5810217 A B R f op a t g p' q')). Qed.
Lemma lem5810229 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5810230 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5810229 p q p' q'). Qed.
Lemma lem5810231 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5810230 p q p'). Qed.
Lemma lem5810232 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : term153 A B t R f g x'.
Proof. exact (@lem5810231 (@IN A x' t) (term78 A B R f g x')). Qed.
Lemma lem5810233 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : term154 A B t R f g x' p'.
Proof. exact (@lem5810232 A B t R f g x' p'). Qed.
Lemma lem5810234 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : (term154 A B t R f g x' p') = (term155 A B t R f g x' p').
Proof. exact (eq_refl (term154 A B t R f g x' p')). Qed.
Lemma lem5810235 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) : term155 A B t R f g x' p'.
Proof. exact (EQ_MP (@lem5810234 A B t R f g x' p') (@lem5810233 A B t R f g x' p')). Qed.
Lemma lem5810236 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term156 A B t R f g x' p' q'.
Proof. exact (@lem5810235 A B t R f g x' p' q'). Qed.
Lemma lem5810237 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : (term156 A B t R f g x' p' q') = (term157 A B t R f g x' p' q').
Proof. exact (eq_refl (term156 A B t R f g x' p' q')). Qed.
Lemma lem5810238 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term157 A B t R f g x' p' q'.
Proof. exact (EQ_MP (@lem5810237 A B t R f g x' p' q') (@lem5810236 A B t R f g x' p' q')). Qed.
Lemma lem5810240 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810241 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem5810242 {A : Type'} (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@IN A x' t) = (@IN A x' (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810241 A x') (@lem5810240 A t h1)). Qed.
Lemma lem5810243 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (q' : Prop) : term158 A B t R f g x' q'.
Proof. exact (@lem5810238 A B t R f g x' (@IN A x' (@EMPTY A)) q'). Qed.
Lemma lem5810244 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term159 A B t R f g x' q'.
Proof. exact (@lem5810243 A B t R f g x' q' (@lem5810242 A x' t h1)). Qed.
Lemma lem5810248 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term78 A B R f g x') = (term78 A B R f g x').
Proof. exact (eq_refl (term78 A B R f g x')). Qed.
Lemma lem5810249 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : term160 A B R f g x'.
Proof. exact (fun h0 : @IN A x' (@EMPTY A) => @lem5810248 A B R f g x'). Qed.
Lemma lem5810250 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term161 A B t R f g x'.
Proof. exact (@lem5810244 A B R f g x' (term78 A B R f g x') t h1). Qed.
Lemma lem5810251 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term108 A B t R f g x') = (term79 A B R f g x').
Proof. exact (@lem5810250 A B R f g x' t h1 (@lem5810249 A B R f g x')). Qed.
Lemma lem5810275 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term110 A B t R f g) = (term81 A B R f g).
Proof. exact (fun_ext (fun x' : A => @lem5810251 A B R f g x' t h1)). Qed.
Lemma lem5810299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5810300 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term34 A B t R f g) = (term83 A B R f g).
Proof. exact (MK_COMB (@lem5810299 A) (@lem5810275 A B R f g t h1)). Qed.
Lemma lem5810328 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (a : A) : (term105 A B R f g a) = (term105 A B R f g a).
Proof. exact (eq_refl (term105 A B R f g a)). Qed.
Lemma lem5810329 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term112 A B a t R f g) = (term183 A B a R f g).
Proof. exact (MK_COMB (@lem5810328 A B R f g a) (@lem5810300 A B R f g t h1)). Qed.
Lemma lem5810359 {A B : Type'} (op : type1400 B) (t : A -> Prop) (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term184 A B op t a R f g q'.
Proof. exact (@lem5810219 A B R f op a t g (term183 A B a R f g) q'). Qed.
Lemma lem5810360 {A B : Type'} (op : type1400 B) (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term185 A B op t a R f g q'.
Proof. exact (@lem5810359 A B op t a R f g q' (@lem5810329 A B a R f g t h1)). Qed.
Lemma lem5810361 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term183 A B a R f g) : term183 A B a R f g.
Proof. exact (h1). Qed.
Lemma lem5810375 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term183 A B a R f g) : term78 A B R f g a.
Proof. exact (proj1 (@lem5810361 A B a R f g h1)). Qed.
Lemma lem5810376 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (a : A) : (term78 A B R f g a) = ((term78 A B R f g a) = True).
Proof. exact (@lem7 (term78 A B R f g a)). Qed.
Lemma lem5810379 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810380 {A : Type'} (a : A) : (@INSERT A a) = (@INSERT A a).
Proof. exact (eq_refl (@INSERT A a)). Qed.
Lemma lem5810381 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@INSERT A a t) = (@INSERT A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810380 A a) (@lem5810379 A t h1)). Qed.
Lemma lem5810382 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5810383 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term186 A B op a t) = (term187 A B op a).
Proof. exact (MK_COMB (@lem5810382 A B op) (@lem5810381 A a t h1)). Qed.
Lemma lem5810384 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5810385 {A B : Type'} (op : type1400 B) (a : A) (f : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term188 A B op a t f) = (term131 A B op a f).
Proof. exact (MK_COMB (@lem5810383 A B op a t h1) (@lem5810384 A B f)). Qed.
Lemma lem5810387 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term189 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem5809846 A B f x op h0). Qed.
Lemma lem5810388 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term189 A B op f x.
Proof. exact (@lem5810387 A B op f x). Qed.
Lemma lem5810389 {A B : Type'} (op : type1400 B) (f : A -> B) (a : A) : term189 A B op f a.
Proof. exact (@lem5810388 A B op f a). Qed.
Lemma lem5810391 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5809852 B op) (@lem5809554 B op h1)). Qed.
Lemma lem5810392 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5810391 B op h1)). Qed.
Lemma lem5810393 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5810392 B op h1) (@lem0)). Qed.
Lemma lem5810394 {A B : Type'} (f : A -> B) (a : A) (op : type1400 B) (h1 : @monoidal B op) : (term131 A B op a f) = (f a).
Proof. exact (@lem5810389 A B op f a (@lem5810393 B op h1)). Qed.
Lemma lem5810395 {A B : Type'} (f : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term188 A B op a t f) = (f a).
Proof. exact (TRANS (@lem5810385 A B op a f t h2) (@lem5810394 A B f a op h1)). Qed.
Lemma lem5810396 {B : Type'} (R : type1402 B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem5810397 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term190 A B R op a t f) = (term191 A B R f a).
Proof. exact (MK_COMB (@lem5810396 B R) (@lem5810395 A B f a op t h1 h2)). Qed.
Lemma lem5810399 {A : Type'} (t : A -> Prop) (h1 : t = (@EMPTY A)) : t = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem5810400 {A : Type'} (a : A) : (@INSERT A a) = (@INSERT A a).
Proof. exact (eq_refl (@INSERT A a)). Qed.
Lemma lem5810401 {A : Type'} (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (@INSERT A a t) = (@INSERT A a (@EMPTY A)).
Proof. exact (MK_COMB (@lem5810400 A a) (@lem5810399 A t h1)). Qed.
Lemma lem5810402 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5810403 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term186 A B op a t) = (term187 A B op a).
Proof. exact (MK_COMB (@lem5810402 A B op) (@lem5810401 A a t h1)). Qed.
Lemma lem5810404 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5810405 {A B : Type'} (op : type1400 B) (a : A) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : (term188 A B op a t g) = (term131 A B op a g).
Proof. exact (MK_COMB (@lem5810403 A B op a t h1) (@lem5810404 A B g)). Qed.
Lemma lem5810407 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term189 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem5809846 A B f x op h0). Qed.
Lemma lem5810408 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term189 A B op f x.
Proof. exact (@lem5810407 A B op f x). Qed.
Lemma lem5810409 {A B : Type'} (op : type1400 B) (g : A -> B) (a : A) : term189 A B op g a.
Proof. exact (@lem5810408 A B op g a). Qed.
Lemma lem5810411 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5809852 B op) (@lem5809554 B op h1)). Qed.
Lemma lem5810412 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5810411 B op h1)). Qed.
Lemma lem5810413 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5810412 B op h1) (@lem0)). Qed.
Lemma lem5810414 {A B : Type'} (g : A -> B) (a : A) (op : type1400 B) (h1 : @monoidal B op) : (term131 A B op a g) = (g a).
Proof. exact (@lem5810409 A B op g a (@lem5810413 B op h1)). Qed.
Lemma lem5810415 {A B : Type'} (g : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term188 A B op a t g) = (g a).
Proof. exact (TRANS (@lem5810405 A B op a g t h2) (@lem5810414 A B g a op h1)). Qed.
Lemma lem5810416 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term115 A B R f op a t g) = (term78 A B R f g a).
Proof. exact (MK_COMB (@lem5810397 A B R f a op t h1 h2) (@lem5810415 A B g a op t h1 h2)). Qed.
Lemma lem5810418 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term183 A B a R f g) : (term78 A B R f g a) = True.
Proof. exact (EQ_MP (@lem5810376 A B R f g a) (@lem5810375 A B a R f g h1)). Qed.
Lemma lem5810419 {A B : Type'} (op : type1400 B) (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term183 A B a R f g) (h3 : t = (@EMPTY A)) : (term115 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5810416 A B R f g a op t h1 h3) (@lem5810418 A B a R f g h2)). Qed.
Lemma lem5810420 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term192 A B R f op a t g.
Proof. exact (fun h0 : term183 A B a R f g => @lem5810419 A B op a R f g t h1 h0 h2). Qed.
Lemma lem5810421 {A B : Type'} (op : type1400 B) (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term193 A B op t a R f g.
Proof. exact (@lem5810360 A B op a R f g True t h1). Qed.
Lemma lem5810422 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term117 A B R f op a t g) = (term194 A B a R f g).
Proof. exact (@lem5810421 A B op a R f g t h2 (@lem5810420 A B R f a g op t h1 h2)). Qed.
Lemma lem5810424 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5810425 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) : (term194 A B a R f g) = True.
Proof. exact (@lem5810424 (term183 A B a R f g)). Qed.
Lemma lem5810426 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term117 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5810422 A B a R f g op t h1 h2) (@lem5810425 A B a R f g)). Qed.
Lemma lem5810427 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term195 A B R f op a t g.
Proof. exact (fun h0 : term174 A a => @lem5810426 A B R f a g op t h1 h2). Qed.
Lemma lem5810428 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : t = (@EMPTY A)) : term196 A B R f op t g a.
Proof. exact (@lem5810199 A B R f op g a True t h1). Qed.
Lemma lem5810429 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (a : A) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term119 A B R f op a t g) = (term197 A a).
Proof. exact (@lem5810428 A B R f op g a t h2 (@lem5810427 A B R f a g op t h1 h2)). Qed.
Lemma lem5810431 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5810432 {A : Type'} (a : A) : (term197 A a) = True.
Proof. exact (@lem5810431 (term174 A a)). Qed.
Lemma lem5810433 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : (term119 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5810429 A B R f g a op t h1 h2) (@lem5810432 A a)). Qed.
Lemma lem5810434 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : True = (term119 A B R f op a t g).
Proof. exact (SYM (@lem5810433 A B R f a g op t h1 h2)). Qed.
Lemma lem5810435 {A B : Type'} (R : type1402 B) (f : A -> B) (a : A) (g : A -> B) (op : type1400 B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : t = (@EMPTY A)) : term119 A B R f op a t g.
Proof. exact (EQ_MP (@lem5810434 A B R f a g op t h1 h2) (@lem0)). Qed.
Lemma lem5810475 {A : Type'} (t : A -> Prop) : term198 A t.
Proof. exact (@lem82 (t = (@EMPTY A))). Qed.
Lemma lem5810491 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5810492 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5810491 p q p' q'). Qed.
Lemma lem5810493 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5810492 p q p'). Qed.
Lemma lem5810494 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term135 A B R f op a t g.
Proof. exact (@lem5810493 (term52 A B R f op g a t) (term117 A B R f op a t g)). Qed.
Lemma lem5810495 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term136 A B R f op a t g p'.
Proof. exact (@lem5810494 A B R f op a t g p'). Qed.
Lemma lem5810496 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term136 A B R f op a t g p') = (term137 A B R f op a t g p').
Proof. exact (eq_refl (term136 A B R f op a t g p')). Qed.
Lemma lem5810497 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term137 A B R f op a t g p'.
Proof. exact (EQ_MP (@lem5810496 A B R f op a t g p') (@lem5810495 A B R f op a t g p')). Qed.
Lemma lem5810498 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term138 A B R f op a t g p' q'.
Proof. exact (@lem5810497 A B R f op a t g p' q'). Qed.
Lemma lem5810499 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term138 A B R f op a t g p' q') = (term139 A B R f op a t g p' q').
Proof. exact (eq_refl (term138 A B R f op a t g p' q')). Qed.
Lemma lem5810500 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term139 A B R f op a t g p' q'.
Proof. exact (EQ_MP (@lem5810499 A B R f op a t g p' q') (@lem5810498 A B R f op a t g p' q')). Qed.
Lemma lem5810506 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5810507 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5810506 p q p' q'). Qed.
Lemma lem5810508 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5810507 p q p'). Qed.
Lemma lem5810509 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term140 A B R f op t g.
Proof. exact (@lem5810508 (term2 A t) (term141 A B R f op t g)). Qed.
Lemma lem5810510 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term142 A B R f op t g p'.
Proof. exact (@lem5810509 A B R f op t g p'). Qed.
Lemma lem5810511 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term142 A B R f op t g p') = (term143 A B R f op t g p').
Proof. exact (eq_refl (term142 A B R f op t g p')). Qed.
Lemma lem5810512 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) : term143 A B R f op t g p'.
Proof. exact (EQ_MP (@lem5810511 A B R f op t g p') (@lem5810510 A B R f op t g p')). Qed.
Lemma lem5810513 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term144 A B R f op t g p' q'.
Proof. exact (@lem5810512 A B R f op t g p' q'). Qed.
Lemma lem5810514 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term144 A B R f op t g p' q') = (term145 A B R f op t g p' q').
Proof. exact (eq_refl (term144 A B R f op t g p' q')). Qed.
Lemma lem5810515 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term145 A B R f op t g p' q'.
Proof. exact (EQ_MP (@lem5810514 A B R f op t g p' q') (@lem5810513 A B R f op t g p' q')). Qed.
Lemma lem5810517 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (t = (@EMPTY A)) = False.
Proof. exact (@lem5810475 A t (@lem5809504 A t h1)). Qed.
Lemma lem5810518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5810519 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (term2 A t) = (~ False).
Proof. exact (MK_COMB (@lem5810518) (@lem5810517 A t h1)). Qed.
Lemma lem5810521 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5810522 {A : Type'} (t : A -> Prop) (h1 : term2 A t) : (term2 A t) = True.
Proof. exact (TRANS (@lem5810519 A t h1) (@lem5810521)). Qed.
Lemma lem5810523 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (q' : Prop) : term199 A B R f op t g q'.
Proof. exact (@lem5810515 A B R f op t g True q'). Qed.
Lemma lem5810524 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (q' : Prop) (t : A -> Prop) (h1 : term2 A t) : term200 A B R f op t g q'.
Proof. exact (@lem5810523 A B R f op t g q' (@lem5810522 A t h1)). Qed.
Lemma lem5810617 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term141 A B R f op t g) = (term141 A B R f op t g).
Proof. exact (eq_refl (term141 A B R f op t g)). Qed.
Lemma lem5810618 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term201 A B R f op t g.
Proof. exact (fun h0 : True => @lem5810617 A B R f op t g). Qed.
Lemma lem5810619 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : term202 A B R f op t g.
Proof. exact (@lem5810524 A B R f op g (term141 A B R f op t g) t h1). Qed.
Lemma lem5810620 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term33 A B R f op t g) = (term203 A B R f op t g).
Proof. exact (@lem5810619 A B R f op g t h1 (@lem5810618 A B R f op t g)). Qed.
Lemma lem5810622 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5810623 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term203 A B R f op t g) = (term141 A B R f op t g).
Proof. exact (@lem5810622 (term141 A B R f op t g)). Qed.
Lemma lem5810711 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term33 A B R f op t g) = (term141 A B R f op t g).
Proof. exact (TRANS (@lem5810620 A B R f op g t h1) (@lem5810623 A B R f op t g)). Qed.
Lemma lem5810712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5810713 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term49 A B R f op t g) = (term204 A B R f op t g).
Proof. exact (MK_COMB (@lem5810712) (@lem5810711 A B R f op g t h1)). Qed.
Lemma lem5810803 {A : Type'} (a : A) (t : A -> Prop) : (term50 A a t) = (term50 A a t).
Proof. exact (eq_refl (term50 A a t)). Qed.
Lemma lem5810804 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term2 A t) : (term52 A B R f op g a t) = (term205 A B R f op g a t).
Proof. exact (MK_COMB (@lem5810713 A B R f op g t h1) (@lem5810803 A a t)). Qed.
Lemma lem5810896 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term206 A B R f op g a t q'.
Proof. exact (@lem5810500 A B R f op a t g (term205 A B R f op g a t) q'). Qed.
Lemma lem5810897 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (q' : Prop) (t : A -> Prop) (h1 : term2 A t) : term207 A B R f op g a t q'.
Proof. exact (@lem5810896 A B R f op g a t q' (@lem5810804 A B R f op g a t h1)). Qed.
Lemma lem5811011 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : (term117 A B R f op a t g) = (term117 A B R f op a t g).
Proof. exact (eq_refl (term117 A B R f op a t g)). Qed.
Lemma lem5811012 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term208 A B R f op a t g.
Proof. exact (fun h0 : term205 A B R f op g a t => @lem5811011 A B R f op a t g). Qed.
Lemma lem5811013 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : term209 A B R f op a t g.
Proof. exact (@lem5810897 A B R f op g a (term117 A B R f op a t g) t h1). Qed.
Lemma lem5811014 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term119 A B R f op a t g) = (term210 A B R f op a t g).
Proof. exact (@lem5811013 A B R f op a g t h1 (@lem5811012 A B R f op a t g)). Qed.
Lemma lem5811425 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (g : A -> B) (t : A -> Prop) (h1 : term2 A t) : (term210 A B R f op a t g) = (term119 A B R f op a t g).
Proof. exact (SYM (@lem5811014 A B R f op a g t h1)). Qed.
Lemma lem5811426 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term211 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5811427 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term211 _120477 _120519 _120521 op) = (term212 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term211 _120477 _120519 _120521 op)). Qed.
Lemma lem5811428 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term212 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5811427 _120477 _120519 _120521 op) (@lem5811426 _120477 _120519 _120521 op)). Qed.
Lemma lem5811429 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5811430 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term213 _120477 _120519 _120521 op.
Proof. exact (@lem5811428 _120477 _120519 _120521 op (@lem5811429 _120519 op h1)). Qed.
Lemma lem5811431 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term214 _120519 _120521 op.
Proof. exact (proj2 (@lem5811430 Prop _120519 _120521 op h1)). Qed.
Lemma lem5811432 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term215 _120519 _120521 op f.
Proof. exact (@lem5811431 _120519 _120521 op h1 f). Qed.
Lemma lem5811433 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term215 _120519 _120521 op f) = (term216 _120519 _120521 op f).
Proof. exact (eq_refl (term215 _120519 _120521 op f)). Qed.
Lemma lem5811434 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term216 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5811433 _120519 _120521 op f) (@lem5811432 _120519 _120521 f op h1)). Qed.
Lemma lem5811435 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term217 _120519 _120521 op f x.
Proof. exact (@lem5811434 _120519 _120521 f op h1 x). Qed.
Lemma lem5811436 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term217 _120519 _120521 op f x) = (term218 _120519 _120521 x op f).
Proof. exact (eq_refl (term217 _120519 _120521 op f x)). Qed.
Lemma lem5811437 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term218 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5811436 _120519 _120521 x op f) (@lem5811435 _120519 _120521 f x op h1)). Qed.
Lemma lem5811438 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term219 _120519 _120521 x op f s.
Proof. exact (@lem5811437 _120519 _120521 x f op h1 s). Qed.
Lemma lem5811439 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term219 _120519 _120521 x op f s) = (term220 _120519 _120521 x op s f).
Proof. exact (eq_refl (term219 _120519 _120521 x op f s)). Qed.
Lemma lem5811440 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term220 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5811439 _120519 _120521 x op s f) (@lem5811438 _120519 _120521 x f s op h1)). Qed.
Lemma lem5811441 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5811442 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term221 _120519 _120521 op x s f) = (term222 _120519 _120521 x op s f).
Proof. exact (@lem5811440 _120519 _120521 x s f op h2 (@lem5811441 _120521 s h1)). Qed.
Lemma lem5811443 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term223 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5811442 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5811444 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term224 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5811443 _120519 _120521 x op f s h0). Qed.
Lemma lem5811446 (p : Prop) (q : Prop) (r : Prop) : (term27 p q r) = (term26 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5811451 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term224 _120519 _120521 x op s f) = (term225 _120519 _120521 x op s f).
Proof. exact (@lem5811446 (@FINITE _120521 s) (@monoidal _120519 op) ((term221 _120519 _120521 op x s f) = (term222 _120519 _120521 x op s f))). Qed.
Lemma lem5811462 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5811464 {B : Type'} (x1 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term226 B R op x1.
Proof. exact (@lem5809555 B R op h1 x1). Qed.
Lemma lem5811465 {B : Type'} (R : type1402 B) (x1 : B) (op : type1400 B) : (term226 B R op x1) = (term227 B R x1 op).
Proof. exact (eq_refl (term226 B R op x1)). Qed.
Lemma lem5811466 {B : Type'} (x1 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term227 B R x1 op.
Proof. exact (EQ_MP (@lem5811465 B R x1 op) (@lem5811464 B x1 R op h1)). Qed.
Lemma lem5811467 {B : Type'} (x1 : B) (y1 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term228 B R x1 op y1.
Proof. exact (@lem5811466 B x1 R op h1 y1). Qed.
Lemma lem5811468 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) : (term228 B R x1 op y1) = (term229 B R x1 y1 op).
Proof. exact (eq_refl (term228 B R x1 op y1)). Qed.
Lemma lem5811469 {B : Type'} (x1 : B) (y1 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term229 B R x1 y1 op.
Proof. exact (EQ_MP (@lem5811468 B R x1 y1 op) (@lem5811467 B x1 y1 R op h1)). Qed.
Lemma lem5811470 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term230 B R x1 y1 op x2.
Proof. exact (@lem5811469 B x1 y1 R op h1 x2). Qed.
Lemma lem5811471 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) : (term230 B R x1 y1 op x2) = (term231 B R x1 y1 op x2).
Proof. exact (eq_refl (term230 B R x1 y1 op x2)). Qed.
Lemma lem5811472 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term231 B R x1 y1 op x2.
Proof. exact (EQ_MP (@lem5811471 B R x1 y1 op x2) (@lem5811470 B x1 y1 x2 R op h1)). Qed.
Lemma lem5811473 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term232 B R x1 y1 op x2 y2.
Proof. exact (@lem5811472 B x1 y1 x2 R op h1 y2). Qed.
Lemma lem5811474 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) (y2 : B) : (term232 B R x1 y1 op x2 y2) = (term233 B R x1 y1 op x2 y2).
Proof. exact (eq_refl (term232 B R x1 y1 op x2 y2)). Qed.
Lemma lem5811475 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term233 B R x1 y1 op x2 y2.
Proof. exact (EQ_MP (@lem5811474 B R x1 y1 op x2 y2) (@lem5811473 B x1 y1 x2 y2 R op h1)). Qed.
Lemma lem5811476 {B : Type'} (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term234 B x1 x2 R y1 y2) : term234 B x1 x2 R y1 y2.
Proof. exact (h1). Qed.
Lemma lem5811477 {B : Type'} (op : type1400 B) (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term25 B R op) (h2 : term234 B x1 x2 R y1 y2) : term235 B R x1 y1 op x2 y2.
Proof. exact (@lem5811475 B x1 y1 x2 y2 R op h1 (@lem5811476 B x1 x2 R y1 y2 h2)). Qed.
Lemma lem5811478 {B : Type'} (R : type1402 B) (x1 : B) (y1 : B) (op : type1400 B) (x2 : B) (y2 : B) : (term235 B R x1 y1 op x2 y2) = ((term235 B R x1 y1 op x2 y2) = True).
Proof. exact (@lem7 (term235 B R x1 y1 op x2 y2)). Qed.
Lemma lem5811479 {B : Type'} (op : type1400 B) (x1 : B) (x2 : B) (R : type1402 B) (y1 : B) (y2 : B) (h1 : term25 B R op) (h2 : term234 B x1 x2 R y1 y2) : (term235 B R x1 y1 op x2 y2) = True.
Proof. exact (EQ_MP (@lem5811478 B R x1 y1 op x2 y2) (@lem5811477 B op x1 x2 R y1 y2 h1 h2)). Qed.
Lemma lem5811501 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5811502 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5811501 p q p' q'). Qed.
Lemma lem5811503 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5811502 p q p'). Qed.
Lemma lem5811504 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term236 A B R f op a t g.
Proof. exact (@lem5811503 (term205 A B R f op g a t) (term117 A B R f op a t g)). Qed.
Lemma lem5811505 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term237 A B R f op a t g p'.
Proof. exact (@lem5811504 A B R f op a t g p'). Qed.
Lemma lem5811506 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term237 A B R f op a t g p') = (term238 A B R f op a t g p').
Proof. exact (eq_refl (term237 A B R f op a t g p')). Qed.
Lemma lem5811507 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term238 A B R f op a t g p'.
Proof. exact (EQ_MP (@lem5811506 A B R f op a t g p') (@lem5811505 A B R f op a t g p')). Qed.
Lemma lem5811508 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term239 A B R f op a t g p' q'.
Proof. exact (@lem5811507 A B R f op a t g p' q'). Qed.
Lemma lem5811509 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term239 A B R f op a t g p' q') = (term240 A B R f op a t g p' q').
Proof. exact (eq_refl (term239 A B R f op a t g p' q')). Qed.
Lemma lem5811510 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term240 A B R f op a t g p' q'.
Proof. exact (EQ_MP (@lem5811509 A B R f op a t g p' q') (@lem5811508 A B R f op a t g p' q')). Qed.
Lemma lem5811602 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) : (term205 A B R f op g a t) = (term205 A B R f op g a t).
Proof. exact (eq_refl (term205 A B R f op g a t)). Qed.
Lemma lem5811603 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term241 A B R f op g a t q'.
Proof. exact (@lem5811510 A B R f op a t g (term205 A B R f op g a t) q'). Qed.
Lemma lem5811604 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (q' : Prop) : term242 A B R f op g a t q'.
Proof. exact (@lem5811603 A B R f op g a t q' (@lem5811602 A B R f op g a t)). Qed.
Lemma lem5811605 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term205 A B R f op g a t.
Proof. exact (h1). Qed.
Lemma lem5811606 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term50 A a t.
Proof. exact (proj2 (@lem5811605 A B R f op g a t h1)). Qed.
Lemma lem5811607 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : @FINITE A t.
Proof. exact (proj2 (@lem5811606 A B R f op g a t h1)). Qed.
Lemma lem5811608 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem5811610 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term171 A a t.
Proof. exact (proj1 (@lem5811606 A B R f op g a t h1)). Qed.
Lemma lem5811611 {A : Type'} (a : A) (t : A -> Prop) : term243 A a t.
Proof. exact (@lem82 (@IN A a t)). Qed.
Lemma lem5811613 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term141 A B R f op t g.
Proof. exact (proj1 (@lem5811605 A B R f op g a t h1)). Qed.
Lemma lem5811614 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term34 A B t R f g) : term34 A B t R f g.
Proof. exact (h1). Qed.
Lemma lem5811615 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term34 A B t R f g) (h2 : term205 A B R f op g a t) : term31 A B R f op t g.
Proof. exact (@lem5811613 A B R f op g a t h2 (@lem5811614 A B t R f g h1)). Qed.
Lemma lem5811616 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term31 A B R f op t g) = ((term31 A B R f op t g) = True).
Proof. exact (@lem7 (term31 A B R f op t g)). Qed.
Lemma lem5811617 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term34 A B t R f g) (h2 : term205 A B R f op g a t) : (term31 A B R f op t g) = True.
Proof. exact (EQ_MP (@lem5811616 A B R f op t g) (@lem5811615 A B R f op g a t h1 h2)). Qed.
Lemma lem5811626 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5811627 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5811626 p q p' q'). Qed.
Lemma lem5811628 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5811627 p q p'). Qed.
Lemma lem5811629 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) : term178 A B R f op a t g.
Proof. exact (@lem5811628 (term112 A B a t R f g) (term115 A B R f op a t g)). Qed.
Lemma lem5811630 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term179 A B R f op a t g p'.
Proof. exact (@lem5811629 A B R f op a t g p'). Qed.
Lemma lem5811631 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term179 A B R f op a t g p') = (term180 A B R f op a t g p').
Proof. exact (eq_refl (term179 A B R f op a t g p')). Qed.
Lemma lem5811632 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term180 A B R f op a t g p'.
Proof. exact (EQ_MP (@lem5811631 A B R f op a t g p') (@lem5811630 A B R f op a t g p')). Qed.
Lemma lem5811633 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term181 A B R f op a t g p' q'.
Proof. exact (@lem5811632 A B R f op a t g p' q'). Qed.
Lemma lem5811634 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term181 A B R f op a t g p' q') = (term182 A B R f op a t g p' q').
Proof. exact (eq_refl (term181 A B R f op a t g p' q')). Qed.
Lemma lem5811635 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (a : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term182 A B R f op a t g p' q'.
Proof. exact (EQ_MP (@lem5811634 A B R f op a t g p' q') (@lem5811633 A B R f op a t g p' q')). Qed.
Lemma lem5811665 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term112 A B a t R f g) = (term112 A B a t R f g).
Proof. exact (eq_refl (term112 A B a t R f g)). Qed.
Lemma lem5811666 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term244 A B op a t R f g q'.
Proof. exact (@lem5811635 A B R f op a t g (term112 A B a t R f g) q'). Qed.
Lemma lem5811667 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (q' : Prop) : term245 A B op a t R f g q'.
Proof. exact (@lem5811666 A B op a t R f g q' (@lem5811665 A B a t R f g)). Qed.
Lemma lem5811668 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term112 A B a t R f g.
Proof. exact (h1). Qed.
Lemma lem5811669 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term34 A B t R f g.
Proof. exact (proj2 (@lem5811668 A B a t R f g h1)). Qed.
Lemma lem5811670 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term246 A B t R f g x'.
Proof. exact (@lem5811669 A B a t R f g h1 x'). Qed.
Lemma lem5811671 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term246 A B t R f g x') = (term108 A B t R f g x').
Proof. exact (eq_refl (term246 A B t R f g x')). Qed.
Lemma lem5811672 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term108 A B t R f g x'.
Proof. exact (EQ_MP (@lem5811671 A B t R f g x') (@lem5811670 A B x' a t R f g h1)). Qed.
Lemma lem5811673 {A : Type'} (x' : A) (t : A -> Prop) (h1 : @IN A x' t) : @IN A x' t.
Proof. exact (h1). Qed.
Lemma lem5811674 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (t : A -> Prop) (h1 : term112 A B a t R f g) (h2 : @IN A x' t) : term78 A B R f g x'.
Proof. exact (@lem5811672 A B x' a t R f g h1 (@lem5811673 A x' t h2)). Qed.
Lemma lem5811675 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) : (term78 A B R f g x') = ((term78 A B R f g x') = True).
Proof. exact (@lem7 (term78 A B R f g x')). Qed.
Lemma lem5811676 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (x' : A) (t : A -> Prop) (h1 : term112 A B a t R f g) (h2 : @IN A x' t) : (term78 A B R f g x') = True.
Proof. exact (EQ_MP (@lem5811675 A B R f g x') (@lem5811674 A B a R f g x' t h1 h2)). Qed.
Lemma lem5811682 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term78 A B R f g a.
Proof. exact (proj1 (@lem5811668 A B a t R f g h1)). Qed.
Lemma lem5811683 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (a : A) : (term78 A B R f g a) = ((term78 A B R f g a) = True).
Proof. exact (@lem7 (term78 A B R f g a)). Qed.
Lemma lem5811686 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term225 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5811451 _120519 _120521 x op s f) (@lem5811444 _120519 _120521 x op s f)). Qed.
Lemma lem5811687 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term247 A B x op s f.
Proof. exact (@lem5811686 B A x op s f). Qed.
Lemma lem5811688 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term247 A B a op t f.
Proof. exact (@lem5811687 A B a op t f). Qed.
Lemma lem5811692 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem5811608 A t) (@lem5811607 A B R f op g a t h1)). Qed.
Lemma lem5811693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5811694 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term248 A t) = (and True).
Proof. exact (MK_COMB (@lem5811693) (@lem5811692 A B R f op g a t h1)). Qed.
Lemma lem5811696 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5811462 B op) (@lem5809554 B op h1)). Qed.
Lemma lem5811697 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term249 A B t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5811694 A B R f op g a t h2) (@lem5811696 B op h1)). Qed.
Lemma lem5811699 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5811700 : (True /\ True) = True.
Proof. exact (@lem5811699 True). Qed.
Lemma lem5811701 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term249 A B t op) = True.
Proof. exact (TRANS (@lem5811697 A B R f op g a t h1 h2) (@lem5811700)). Qed.
Lemma lem5811702 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : True = (term249 A B t op).
Proof. exact (SYM (@lem5811701 A B R f op g a t h1 h2)). Qed.
Lemma lem5811703 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : term249 A B t op.
Proof. exact (EQ_MP (@lem5811702 A B R f op g a t h1 h2) (@lem0)). Qed.
Lemma lem5811704 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term188 A B op a t f) = (term250 A B a op t f).
Proof. exact (@lem5811688 A B a op t f (@lem5811703 A B R f op g a t h1 h2)). Qed.
Lemma lem5811706 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term251 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5811707 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term252 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5811706 _2963 g t e g' t' e'). Qed.
Lemma lem5811708 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term253 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5811707 _2963 g t e g' t'). Qed.
Lemma lem5811709 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term254 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5811708 _2963 g t e g'). Qed.
Lemma lem5811710 {B : Type'} (g : Prop) (t : B) (e : B) : term254 B g t e.
Proof. exact (@lem5811709 B g t e). Qed.
Lemma lem5811711 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term255 A B a op t f.
Proof. exact (@lem5811710 B (@IN A a t) (@iterate B A op t f) (term256 A B a op t f)). Qed.
Lemma lem5811712 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term257 A B a op t f g'.
Proof. exact (@lem5811711 A B a op t f g'). Qed.
Lemma lem5811713 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : (term257 A B a op t f g') = (term258 A B a op t f g').
Proof. exact (eq_refl (term257 A B a op t f g')). Qed.
Lemma lem5811714 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term258 A B a op t f g'.
Proof. exact (EQ_MP (@lem5811713 A B a op t f g') (@lem5811712 A B a op t f g')). Qed.
Lemma lem5811715 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term259 A B a op t f g' t'.
Proof. exact (@lem5811714 A B a op t f g' t'). Qed.
Lemma lem5811716 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : (term259 A B a op t f g' t') = (term260 A B a op t f g' t').
Proof. exact (eq_refl (term259 A B a op t f g' t')). Qed.
Lemma lem5811717 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term260 A B a op t f g' t'.
Proof. exact (EQ_MP (@lem5811716 A B a op t f g' t') (@lem5811715 A B a op t f g' t')). Qed.
Lemma lem5811718 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term261 A B a op t f g' t' e'.
Proof. exact (@lem5811717 A B a op t f g' t' e'). Qed.
Lemma lem5811719 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term261 A B a op t f g' t' e') = (term262 A B a op t f g' t' e').
Proof. exact (eq_refl (term261 A B a op t f g' t' e')). Qed.
Lemma lem5811720 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term262 A B a op t f g' t' e'.
Proof. exact (EQ_MP (@lem5811719 A B a op t f g' t' e') (@lem5811718 A B a op t f g' t' e')). Qed.
Lemma lem5811722 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (@IN A a t) = False.
Proof. exact (@lem5811611 A a t (@lem5811610 A B R f op g a t h1)). Qed.
Lemma lem5811723 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (t' : B) (e' : B) : term263 A B a op t f t' e'.
Proof. exact (@lem5811720 A B a op t f False t' e'). Qed.
Lemma lem5811724 {A B : Type'} (t' : B) (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term264 A B a op t f t' e'.
Proof. exact (@lem5811723 A B a op t f t' e' (@lem5811722 A B R f op g a t h1)). Qed.
Lemma lem5811728 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (@iterate B A op t f).
Proof. exact (eq_refl (@iterate B A op t f)). Qed.
Lemma lem5811729 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : term265 A B op t f.
Proof. exact (fun h0 : False => @lem5811728 A B op t f). Qed.
Lemma lem5811730 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term266 A B a op t f e'.
Proof. exact (@lem5811724 A B (@iterate B A op t f) e' R f op g a t h1). Qed.
Lemma lem5811731 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term267 A B a op t f e'.
Proof. exact (@lem5811730 A B e' R f op g a t h1 (@lem5811729 A B op t f)). Qed.
Lemma lem5811737 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term256 A B a op t f) = (term256 A B a op t f).
Proof. exact (eq_refl (term256 A B a op t f)). Qed.
Lemma lem5811738 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term268 A B a op t f.
Proof. exact (fun h0 : ~ False => @lem5811737 A B a op t f). Qed.
Lemma lem5811739 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term269 A B a op t f.
Proof. exact (@lem5811731 A B (term256 A B a op t f) R f op g a t h1). Qed.
Lemma lem5811740 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term250 A B a op t f) = (term270 A B a op t f).
Proof. exact (@lem5811739 A B R f op g a t h1 (@lem5811738 A B a op t f)). Qed.
Lemma lem5811742 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5811743 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5811742 B t1 t2). Qed.
Lemma lem5811744 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term270 A B a op t f) = (term256 A B a op t f).
Proof. exact (@lem5811743 B (@iterate B A op t f) (term256 A B a op t f)). Qed.
Lemma lem5811745 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term250 A B a op t f) = (term256 A B a op t f).
Proof. exact (TRANS (@lem5811740 A B R f op g a t h1) (@lem5811744 A B a op t f)). Qed.
Lemma lem5811746 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term188 A B op a t f) = (term256 A B a op t f).
Proof. exact (TRANS (@lem5811704 A B R f op g a t h1 h2) (@lem5811745 A B R f op g a t h2)). Qed.
Lemma lem5811747 {B : Type'} (R : type1402 B) : R = R.
Proof. exact (eq_refl R). Qed.
Lemma lem5811748 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term190 A B R op a t f) = (term271 A B R a op t f).
Proof. exact (MK_COMB (@lem5811747 B R) (@lem5811746 A B R f op g a t h1 h2)). Qed.
Lemma lem5811750 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term225 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5811451 _120519 _120521 x op s f) (@lem5811444 _120519 _120521 x op s f)). Qed.
Lemma lem5811751 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term247 A B x op s f.
Proof. exact (@lem5811750 B A x op s f). Qed.
Lemma lem5811752 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term247 A B a op t g.
Proof. exact (@lem5811751 A B a op t g). Qed.
Lemma lem5811756 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem5811608 A t) (@lem5811607 A B R f op g a t h1)). Qed.
Lemma lem5811757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5811758 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term248 A t) = (and True).
Proof. exact (MK_COMB (@lem5811757) (@lem5811756 A B R f op g a t h1)). Qed.
Lemma lem5811760 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5811462 B op) (@lem5809554 B op h1)). Qed.
Lemma lem5811761 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term249 A B t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5811758 A B R f op g a t h2) (@lem5811760 B op h1)). Qed.
Lemma lem5811763 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5811764 : (True /\ True) = True.
Proof. exact (@lem5811763 True). Qed.
Lemma lem5811765 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term249 A B t op) = True.
Proof. exact (TRANS (@lem5811761 A B R f op g a t h1 h2) (@lem5811764)). Qed.
Lemma lem5811766 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : True = (term249 A B t op).
Proof. exact (SYM (@lem5811765 A B R f op g a t h1 h2)). Qed.
Lemma lem5811767 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : term249 A B t op.
Proof. exact (EQ_MP (@lem5811766 A B R f op g a t h1 h2) (@lem0)). Qed.
Lemma lem5811768 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term188 A B op a t g) = (term250 A B a op t g).
Proof. exact (@lem5811752 A B a op t g (@lem5811767 A B R f op g a t h1 h2)). Qed.
Lemma lem5811770 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term251 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5811771 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term252 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5811770 _2963 g t e g' t' e'). Qed.
Lemma lem5811772 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term253 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5811771 _2963 g t e g' t'). Qed.
Lemma lem5811773 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term254 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5811772 _2963 g t e g'). Qed.
Lemma lem5811774 {B : Type'} (g : Prop) (t : B) (e : B) : term254 B g t e.
Proof. exact (@lem5811773 B g t e). Qed.
Lemma lem5811775 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term255 A B a op t g.
Proof. exact (@lem5811774 B (@IN A a t) (@iterate B A op t g) (term256 A B a op t g)). Qed.
Lemma lem5811776 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : term257 A B a op t g g'.
Proof. exact (@lem5811775 A B a op t g g'). Qed.
Lemma lem5811777 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : (term257 A B a op t g g') = (term258 A B a op t g g').
Proof. exact (eq_refl (term257 A B a op t g g')). Qed.
Lemma lem5811778 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : term258 A B a op t g g'.
Proof. exact (EQ_MP (@lem5811777 A B a op t g g') (@lem5811776 A B a op t g g')). Qed.
Lemma lem5811779 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term259 A B a op t g g' t'.
Proof. exact (@lem5811778 A B a op t g g' t'). Qed.
Lemma lem5811780 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : (term259 A B a op t g g' t') = (term260 A B a op t g g' t').
Proof. exact (eq_refl (term259 A B a op t g g' t')). Qed.
Lemma lem5811781 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term260 A B a op t g g' t'.
Proof. exact (EQ_MP (@lem5811780 A B a op t g g' t') (@lem5811779 A B a op t g g' t')). Qed.
Lemma lem5811782 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term261 A B a op t g g' t' e'.
Proof. exact (@lem5811781 A B a op t g g' t' e'). Qed.
Lemma lem5811783 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : (term261 A B a op t g g' t' e') = (term262 A B a op t g g' t' e').
Proof. exact (eq_refl (term261 A B a op t g g' t' e')). Qed.
Lemma lem5811784 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term262 A B a op t g g' t' e'.
Proof. exact (EQ_MP (@lem5811783 A B a op t g g' t' e') (@lem5811782 A B a op t g g' t' e')). Qed.
Lemma lem5811786 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (@IN A a t) = False.
Proof. exact (@lem5811611 A a t (@lem5811610 A B R f op g a t h1)). Qed.
Lemma lem5811787 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (t' : B) (e' : B) : term263 A B a op t g t' e'.
Proof. exact (@lem5811784 A B a op t g False t' e'). Qed.
Lemma lem5811788 {A B : Type'} (t' : B) (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term264 A B a op t g t' e'.
Proof. exact (@lem5811787 A B a op t g t' e' (@lem5811786 A B R f op g a t h1)). Qed.
Lemma lem5811792 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : (@iterate B A op t g) = (@iterate B A op t g).
Proof. exact (eq_refl (@iterate B A op t g)). Qed.
Lemma lem5811793 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : term265 A B op t g.
Proof. exact (fun h0 : False => @lem5811792 A B op t g). Qed.
Lemma lem5811794 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term266 A B a op t g e'.
Proof. exact (@lem5811788 A B (@iterate B A op t g) e' R f op g a t h1). Qed.
Lemma lem5811795 {A B : Type'} (e' : B) (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term267 A B a op t g e'.
Proof. exact (@lem5811794 A B e' R f op g a t h1 (@lem5811793 A B op t g)). Qed.
Lemma lem5811801 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term256 A B a op t g) = (term256 A B a op t g).
Proof. exact (eq_refl (term256 A B a op t g)). Qed.
Lemma lem5811802 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term268 A B a op t g.
Proof. exact (fun h0 : ~ False => @lem5811801 A B a op t g). Qed.
Lemma lem5811803 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term269 A B a op t g.
Proof. exact (@lem5811795 A B (term256 A B a op t g) R f op g a t h1). Qed.
Lemma lem5811804 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term250 A B a op t g) = (term270 A B a op t g).
Proof. exact (@lem5811803 A B R f op g a t h1 (@lem5811802 A B a op t g)). Qed.
Lemma lem5811806 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5811807 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5811806 B t1 t2). Qed.
Lemma lem5811808 {A B : Type'} (a : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term270 A B a op t g) = (term256 A B a op t g).
Proof. exact (@lem5811807 B (@iterate B A op t g) (term256 A B a op t g)). Qed.
Lemma lem5811809 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : (term250 A B a op t g) = (term256 A B a op t g).
Proof. exact (TRANS (@lem5811804 A B R f op g a t h1) (@lem5811808 A B a op t g)). Qed.
Lemma lem5811810 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term188 A B op a t g) = (term256 A B a op t g).
Proof. exact (TRANS (@lem5811768 A B R f op g a t h1 h2) (@lem5811809 A B R f op g a t h2)). Qed.
Lemma lem5811811 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term205 A B R f op g a t) : (term115 A B R f op a t g) = (term272 A B R f a op t g).
Proof. exact (MK_COMB (@lem5811748 A B R f op g a t h1 h2) (@lem5811810 A B R f op g a t h1 h2)). Qed.
Lemma lem5811813 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term273 B R x1 y1 op x2 y2.
Proof. exact (fun h0 : term234 B x1 x2 R y1 y2 => @lem5811479 B op x1 x2 R y1 y2 h1 h0). Qed.
Lemma lem5811814 {B : Type'} (x1 : B) (y1 : B) (x2 : B) (y2 : B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term273 B R x1 y1 op x2 y2.
Proof. exact (@lem5811813 B x1 y1 x2 y2 R op h1). Qed.
Lemma lem5811815 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) : term274 A B R f a op t g.
Proof. exact (@lem5811814 B (f a) (@iterate B A op t f) (g a) (@iterate B A op t g) R op h1). Qed.
Lemma lem5811819 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term78 A B R f g a) = True.
Proof. exact (EQ_MP (@lem5811683 A B R f g a) (@lem5811682 A B a t R f g h1)). Qed.
Lemma lem5811820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5811821 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term105 A B R f g a) = (and True).
Proof. exact (MK_COMB (@lem5811820) (@lem5811819 A B a t R f g h1)). Qed.
Lemma lem5811823 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term205 A B R f op g a t) : term275 A B R f op t g.
Proof. exact (fun h0 : term34 A B t R f g => @lem5811617 A B R f op g a t h0 h1). Qed.
Lemma lem5811831 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term132 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5811832 (p : Prop) (q : Prop) (p' : Prop) : term133 p q p'.
Proof. exact (fun q' : Prop => @lem5811831 p q p' q'). Qed.
Lemma lem5811833 (p : Prop) (q : Prop) : term134 p q.
Proof. exact (fun p' : Prop => @lem5811832 p q p'). Qed.
Lemma lem5811834 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) : term153 A B t R f g x.
Proof. exact (@lem5811833 (@IN A x t) (term78 A B R f g x)). Qed.
Lemma lem5811835 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term154 A B t R f g x p'.
Proof. exact (@lem5811834 A B t R f g x p'). Qed.
Lemma lem5811836 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : (term154 A B t R f g x p') = (term155 A B t R f g x p').
Proof. exact (eq_refl (term154 A B t R f g x p')). Qed.
Lemma lem5811837 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) : term155 A B t R f g x p'.
Proof. exact (EQ_MP (@lem5811836 A B t R f g x p') (@lem5811835 A B t R f g x p')). Qed.
Lemma lem5811838 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term156 A B t R f g x p' q'.
Proof. exact (@lem5811837 A B t R f g x p' q'). Qed.
Lemma lem5811839 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term156 A B t R f g x p' q') = (term157 A B t R f g x p' q').
Proof. exact (eq_refl (term156 A B t R f g x p' q')). Qed.
Lemma lem5811840 {A B : Type'} (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (p' : Prop) (q' : Prop) : term157 A B t R f g x p' q'.
Proof. exact (EQ_MP (@lem5811839 A B t R f g x p' q') (@lem5811838 A B t R f g x p' q')). Qed.
Lemma lem5811841 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem5811842 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term276 A B R f g x t q'.
Proof. exact (@lem5811840 A B t R f g x (@IN A x t) q'). Qed.
Lemma lem5811843 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term277 A B R f g x t q'.
Proof. exact (@lem5811842 A B R f g x t q' (@lem5811841 A x t)). Qed.
Lemma lem5811844 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem5811845 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = ((@IN A x t) = True).
Proof. exact (@lem7 (@IN A x t)). Qed.
Lemma lem5811848 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term278 A B t R f g x'.
Proof. exact (fun h0 : @IN A x' t => @lem5811676 A B a R f g x' t h1 h0). Qed.
Lemma lem5811849 {A B : Type'} (x' : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term278 A B t R f g x'.
Proof. exact (@lem5811848 A B x' a t R f g h1). Qed.
Lemma lem5811850 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term278 A B t R f g x.
Proof. exact (@lem5811849 A B x a t R f g h1). Qed.
Lemma lem5811852 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : (@IN A x t) = True.
Proof. exact (EQ_MP (@lem5811845 A x t) (@lem5811844 A x t h1)). Qed.
Lemma lem5811853 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : True = (@IN A x t).
Proof. exact (SYM (@lem5811852 A x t h1)). Qed.
Lemma lem5811854 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (EQ_MP (@lem5811853 A x t h1) (@lem0)). Qed.
Lemma lem5811855 {A B : Type'} (a : A) (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term112 A B a t R f g) (h2 : @IN A x t) : (term78 A B R f g x) = True.
Proof. exact (@lem5811850 A B x a t R f g h1 (@lem5811854 A x t h2)). Qed.
Lemma lem5811856 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term278 A B t R f g x.
Proof. exact (fun h0 : @IN A x t => @lem5811855 A B a R f g x t h1 h0). Qed.
Lemma lem5811857 {A B : Type'} (R : type1402 B) (f : A -> B) (g : A -> B) (x : A) (t : A -> Prop) : term279 A B R f g x t.
Proof. exact (@lem5811843 A B R f g x t True). Qed.
Lemma lem5811858 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term108 A B t R f g x) = (term280 A x t).
Proof. exact (@lem5811857 A B R f g x t (@lem5811856 A B x a t R f g h1)). Qed.
Lemma lem5811860 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5811861 {A : Type'} (x : A) (t : A -> Prop) : (term280 A x t) = True.
Proof. exact (@lem5811860 (@IN A x t)). Qed.
Lemma lem5811862 {A B : Type'} (x : A) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term108 A B t R f g x) = True.
Proof. exact (TRANS (@lem5811858 A B x a t R f g h1) (@lem5811861 A x t)). Qed.
Lemma lem5811863 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term110 A B t R f g) = (term82 A).
Proof. exact (fun_ext (fun x : A => @lem5811862 A B x a t R f g h1)). Qed.
Lemma lem5811864 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5811865 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term34 A B t R f g) = (term84 A).
Proof. exact (MK_COMB (@lem5811864 A) (@lem5811863 A B a t R f g h1)). Qed.
Lemma lem5811867 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5811868 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem5811867 A t). Qed.
Lemma lem5811869 {A : Type'} : (term84 A) = True.
Proof. exact (@lem5811868 A True). Qed.
Lemma lem5811870 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : (term34 A B t R f g) = True.
Proof. exact (TRANS (@lem5811865 A B a t R f g h1) (@lem5811869 A)). Qed.
Lemma lem5811871 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : True = (term34 A B t R f g).
Proof. exact (SYM (@lem5811870 A B a t R f g h1)). Qed.
Lemma lem5811872 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term112 A B a t R f g) : term34 A B t R f g.
Proof. exact (EQ_MP (@lem5811871 A B a t R f g h1) (@lem0)). Qed.
Lemma lem5811873 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term205 A B R f op g a t) (h2 : term112 A B a t R f g) : (term31 A B R f op t g) = True.
Proof. exact (@lem5811823 A B R f op g a t h1 (@lem5811872 A B a t R f g h2)). Qed.
Lemma lem5811874 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term205 A B R f op g a t) (h2 : term112 A B a t R f g) : (term281 A B a R f op t g) = (True /\ True).
Proof. exact (MK_COMB (@lem5811821 A B a t R f g h2) (@lem5811873 A B op a t R f g h1 h2)). Qed.
Lemma lem5811876 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5811877 : (True /\ True) = True.
Proof. exact (@lem5811876 True). Qed.
Lemma lem5811878 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term205 A B R f op g a t) (h2 : term112 A B a t R f g) : (term281 A B a R f op t g) = True.
Proof. exact (TRANS (@lem5811874 A B op a t R f g h1 h2) (@lem5811877)). Qed.
Lemma lem5811879 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term205 A B R f op g a t) (h2 : term112 A B a t R f g) : True = (term281 A B a R f op t g).
Proof. exact (SYM (@lem5811878 A B op a t R f g h1 h2)). Qed.
Lemma lem5811880 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term205 A B R f op g a t) (h2 : term112 A B a t R f g) : term281 A B a R f op t g.
Proof. exact (EQ_MP (@lem5811879 A B op a t R f g h1 h2) (@lem0)). Qed.
Lemma lem5811881 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term25 B R op) (h2 : term205 A B R f op g a t) (h3 : term112 A B a t R f g) : (term272 A B R f a op t g) = True.
Proof. exact (@lem5811815 A B f a t g R op h1 (@lem5811880 A B op a t R f g h2 h3)). Qed.
Lemma lem5811882 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) (h1 : term25 B R op) (h2 : @monoidal B op) (h3 : term205 A B R f op g a t) (h4 : term112 A B a t R f g) : (term115 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5811811 A B R f op g a t h2 h3) (@lem5811881 A B op a t R f g h1 h3 h4)). Qed.
Lemma lem5811883 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B R op) (h2 : @monoidal B op) (h3 : term205 A B R f op g a t) : term282 A B R f op a t g.
Proof. exact (fun h0 : term112 A B a t R f g => @lem5811882 A B op a t R f g h1 h2 h3 h0). Qed.
Lemma lem5811884 {A B : Type'} (op : type1400 B) (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : term283 A B op a t R f g.
Proof. exact (@lem5811667 A B op a t R f g True). Qed.
Lemma lem5811885 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B R op) (h2 : @monoidal B op) (h3 : term205 A B R f op g a t) : (term117 A B R f op a t g) = (term284 A B a t R f g).
Proof. exact (@lem5811884 A B op a t R f g (@lem5811883 A B R f op g a t h1 h2 h3)). Qed.
Lemma lem5811887 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5811888 {A B : Type'} (a : A) (t : A -> Prop) (R : type1402 B) (f : A -> B) (g : A -> B) : (term284 A B a t R f g) = True.
Proof. exact (@lem5811887 (term112 A B a t R f g)). Qed.
Lemma lem5811889 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) (h1 : term25 B R op) (h2 : @monoidal B op) (h3 : term205 A B R f op g a t) : (term117 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5811885 A B R f op g a t h1 h2 h3) (@lem5811888 A B a t R f g)). Qed.
Lemma lem5811890 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term285 A B R f op a t g.
Proof. exact (fun h0 : term205 A B R f op g a t => @lem5811889 A B R f op g a t h1 h2 h0). Qed.
Lemma lem5811891 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) : term286 A B R f op g a t.
Proof. exact (@lem5811604 A B R f op g a t True). Qed.
Lemma lem5811892 {A B : Type'} (f : A -> B) (g : A -> B) (a : A) (t : A -> Prop) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : (term210 A B R f op a t g) = (term287 A B R f op g a t).
Proof. exact (@lem5811891 A B R f op g a t (@lem5811890 A B f a t g R op h1 h2)). Qed.
Lemma lem5811894 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5811895 {A B : Type'} (R : type1402 B) (f : A -> B) (op : type1400 B) (g : A -> B) (a : A) (t : A -> Prop) : (term287 A B R f op g a t) = True.
Proof. exact (@lem5811894 (term205 A B R f op g a t)). Qed.
Lemma lem5811896 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : (term210 A B R f op a t g) = True.
Proof. exact (TRANS (@lem5811892 A B f g a t R op h1 h2) (@lem5811895 A B R f op g a t)). Qed.
Lemma lem5811897 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : True = (term210 A B R f op a t g).
Proof. exact (SYM (@lem5811896 A B f a t g R op h1 h2)). Qed.
Lemma lem5811898 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term210 A B R f op a t g.
Proof. exact (EQ_MP (@lem5811897 A B f a t g R op h1 h2) (@lem0)). Qed.
Lemma lem5811899 {A B : Type'} (f : A -> B) (a : A) (g : A -> B) (R : type1402 B) (op : type1400 B) (t : A -> Prop) (h1 : term25 B R op) (h2 : @monoidal B op) (h3 : term2 A t) : term119 A B R f op a t g.
Proof. exact (EQ_MP (@lem5811425 A B R f op a g t h3) (@lem5811898 A B f a t g R op h1 h2)). Qed.
Lemma lem5811900 {A B : Type'} (f : A -> B) (a : A) (t : A -> Prop) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term119 A B R f op a t g.
Proof. exact (or_elim (@lem5809502 A t) (fun h0 : t = (@EMPTY A) => @lem5810435 A B R f a g op t h2 h0) (fun h0 : term2 A t => @lem5811899 A B f a g R op t h1 h2 h0)). Qed.
Lemma lem5811905 {A B : Type'} (f : A -> B) (a : A) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term121 A B R f op a g.
Proof. exact (fun t : A -> Prop => @lem5811900 A B f a t g R op h1 h2). Qed.
Lemma lem5811910 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term123 A B R f op g.
Proof. exact (fun a : A => @lem5811905 A B f a g R op h1 h2). Qed.
Lemma lem5811911 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term68 A B R f op g.
Proof. exact (EQ_MP (@lem5809835 A B R f op g) (@lem5811910 A B f g R op h1 h2)). Qed.
Lemma lem5811912 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term40 A B R f op g.
Proof. exact (@lem5809625 A B R f op g (@lem5811911 A B f g R op h1 h2)). Qed.
Lemma lem5811913 {A B : Type'} (f : A -> B) (g : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term39 A B R f op g.
Proof. exact (EQ_MP (@lem5809592 A B R f op g) (@lem5811912 A B f g R op h1 h2)). Qed.
Lemma lem5811918 {A B : Type'} (f : A -> B) (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term288 A B R f op.
Proof. exact (fun g : A -> B => @lem5811913 A B f g R op h1 h2). Qed.
Lemma lem5811923 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : term25 B R op) (h2 : @monoidal B op) : term289 A B R op.
Proof. exact (fun f : A -> B => @lem5811918 A B f R op h1 h2). Qed.
Lemma lem5811924 {A B : Type'} (R : type1402 B) (op : type1400 B) (h1 : @monoidal B op) : term290 A B R op.
Proof. exact (fun h0 : term25 B R op => @lem5811923 A B R op h0 h1). Qed.
Lemma lem5811929 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term291 A B op.
Proof. exact (fun R : type1402 B => @lem5811924 A B R op h1). Qed.
Lemma lem5811930 {A B : Type'} (op : type1400 B) : term292 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5811929 A B op h0). Qed.
Lemma lem5811935 {A B : Type'} : term293 A B.
Proof. exact (fun op : type1400 B => @lem5811930 A B op). Qed.
