Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALLPAIRS_EQ_term_abbrevs.
Require Import ALLPAIRS_MEM_spec.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
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
Lemma lem1184480 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1184481 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1184482 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1184481 t1) (@lem1184480 t1)). Qed.
Lemma lem1184483 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1184482 t1 t2). Qed.
Lemma lem1184484 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1184485 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1184484 t1 t2) (@lem1184483 t1 t2)). Qed.
Lemma lem1184486 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1184485 t1 t2 t3). Qed.
Lemma lem1184487 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1184488 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1184487 t1 t2 t3) (@lem1184486 t1 t2 t3)). Qed.
Lemma lem1184489 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1184488 t1 t2 t3)). Qed.
Lemma lem1184492 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem1184493 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem1184492 _26777 P l h1)). Qed.
Lemma lem1184494 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem1184495 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem1184494 _26777 l P h1)). Qed.
Lemma lem1184496 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem1184493 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem1184495 _26777 l P h1)). Qed.
Lemma lem1184497 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1184496 _26777 l P)). Qed.
Lemma lem1184498 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1184499 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem1184498 _26777) (@lem1184497 _26777 P)). Qed.
Lemma lem1184500 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1184499 _26777 P)). Qed.
Lemma lem1184501 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1184502 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem1184501 _26777) (@lem1184500 _26777)). Qed.
Lemma lem1184503 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem1184502 _26777) (@lem1138070 _26777)). Qed.
Lemma lem1184507 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) (m : list _27494) (h1 : (term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) : (term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m).
Proof. exact (h1). Qed.
Lemma lem1184508 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) (m : list _27494) (h1 : (term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P).
Proof. exact (SYM (@lem1184507 _27494 _27495 P l m h1)). Qed.
Lemma lem1184509 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h1 : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P)) : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P).
Proof. exact (h1). Qed.
Lemma lem1184510 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h1 : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P)) : (term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m).
Proof. exact (SYM (@lem1184509 _27494 _27495 l m P h1)). Qed.
Lemma lem1184511 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : ((term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) = ((@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P)).
Proof. exact (prop_ext (fun h1 : (term16 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m) => @lem1184508 _27494 _27495 P l m h1) (fun h1 : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P) => @lem1184510 _27494 _27495 l m P h1)). Qed.
Lemma lem1184512 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term17 _27494 _27495 P l) = (term18 _27494 _27495 l P).
Proof. exact (fun_ext (fun m : list _27494 => @lem1184511 _27494 _27495 l m P)). Qed.
Lemma lem1184513 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1184514 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term19 _27494 _27495 P l) = (term20 _27494 _27495 l P).
Proof. exact (MK_COMB (@lem1184513 _27494) (@lem1184512 _27494 _27495 l P)). Qed.
Lemma lem1184515 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term21 _27494 _27495 P) = (term22 _27494 _27495 P).
Proof. exact (fun_ext (fun l : list _27495 => @lem1184514 _27494 _27495 l P)). Qed.
Lemma lem1184516 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1184517 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term23 _27494 _27495 P) = (term24 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1184516 _27495) (@lem1184515 _27494 _27495 P)). Qed.
Lemma lem1184518 {_27494 _27495 : Type'} : (term25 _27494 _27495) = (term26 _27494 _27495).
Proof. exact (fun_ext (fun P : type1470 _27494 _27495 => @lem1184517 _27494 _27495 P)). Qed.
Lemma lem1184519 {_27494 _27495 : Type'} : (@all (_27495 -> _27494 -> Prop)) = (@all (_27495 -> _27494 -> Prop)).
Proof. exact (eq_refl (@all (_27495 -> _27494 -> Prop))). Qed.
Lemma lem1184520 {_27494 _27495 : Type'} : (term27 _27494 _27495) = (term28 _27494 _27495).
Proof. exact (MK_COMB (@lem1184519 _27494 _27495) (@lem1184518 _27494 _27495)). Qed.
Lemma lem1184521 {_27494 _27495 : Type'} : term28 _27494 _27495.
Proof. exact (EQ_MP (@lem1184520 _27494 _27495) (@lem1181594 _27494 _27495)). Qed.
Lemma lem1184522 {_26777 : Type'} (P : _26777 -> Prop) : term29 _26777 P.
Proof. exact (@lem1184503 _26777 P). Qed.
Lemma lem1184523 {_26777 : Type'} (P : _26777 -> Prop) : (term29 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term29 _26777 P)). Qed.
Lemma lem1184524 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem1184523 _26777 P) (@lem1184522 _26777 P)). Qed.
Lemma lem1184525 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term30 _26777 P l.
Proof. exact (@lem1184524 _26777 P l). Qed.
Lemma lem1184526 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term30 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term30 _26777 P l)). Qed.
Lemma lem1184528 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term31 _27494 _27495 P.
Proof. exact (@lem1184521 _27494 _27495 P). Qed.
Lemma lem1184529 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term31 _27494 _27495 P) = (term24 _27494 _27495 P).
Proof. exact (eq_refl (term31 _27494 _27495 P)). Qed.
Lemma lem1184530 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term24 _27494 _27495 P.
Proof. exact (EQ_MP (@lem1184529 _27494 _27495 P) (@lem1184528 _27494 _27495 P)). Qed.
Lemma lem1184531 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) : term32 _27494 _27495 P l.
Proof. exact (@lem1184530 _27494 _27495 P l). Qed.
Lemma lem1184532 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term32 _27494 _27495 P l) = (term20 _27494 _27495 l P).
Proof. exact (eq_refl (term32 _27494 _27495 P l)). Qed.
Lemma lem1184533 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : term20 _27494 _27495 l P.
Proof. exact (EQ_MP (@lem1184532 _27494 _27495 l P) (@lem1184531 _27494 _27495 P l)). Qed.
Lemma lem1184534 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) (m : list _27494) : term33 _27494 _27495 l P m.
Proof. exact (@lem1184533 _27494 _27495 l P m). Qed.
Lemma lem1184535 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term33 _27494 _27495 l P m) = ((@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P)).
Proof. exact (eq_refl (term33 _27494 _27495 l P m)). Qed.
Lemma lem1184558 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1184526 _26777 l P) (@lem1184525 _26777 P l)). Qed.
Lemma lem1184559 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1184558 A l P). Qed.
Lemma lem1184566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184567 {A : Type'} (l : list A) (P : A -> Prop) : (term34 A P l) = (term35 A l P).
Proof. exact (MK_COMB (@lem1184566) (@lem1184559 A l P)). Qed.
Lemma lem1184571 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1184526 _26777 l P) (@lem1184525 _26777 P l)). Qed.
Lemma lem1184572 {B : Type'} (l : list B) (P : B -> Prop) : (@List.Forall B P l) = (term7 B l P).
Proof. exact (@lem1184571 B l P). Qed.
Lemma lem1184573 {B : Type'} (m : list B) (Q : B -> Prop) : (@List.Forall B Q m) = (term7 B m Q).
Proof. exact (@lem1184572 B m Q). Qed.
Lemma lem1184580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184581 {B : Type'} (m : list B) (Q : B -> Prop) : (term34 B Q m) = (term35 B m Q).
Proof. exact (MK_COMB (@lem1184580) (@lem1184573 B m Q)). Qed.
Lemma lem1184596 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term36 A B P Q R R') = (term36 A B P Q R R').
Proof. exact (eq_refl (term36 A B P Q R R')). Qed.
Lemma lem1184597 {A B : Type'} (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term37 A B m P Q R R') = (term38 A B m P Q R R').
Proof. exact (MK_COMB (@lem1184581 B m Q) (@lem1184596 A B P Q R R')). Qed.
Lemma lem1184600 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term39 A B l m P Q R R') = (term40 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1184567 A l P) (@lem1184597 A B m P Q R R')). Qed.
Lemma lem1184603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1184604 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term41 A B l m P Q R R') = (term42 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1184603) (@lem1184600 A B l m P Q R R')). Qed.
Lemma lem1184608 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P).
Proof. exact (EQ_MP (@lem1184535 _27494 _27495 l m P) (@lem1184534 _27494 _27495 l P m)). Qed.
Lemma lem1184609 {A B : Type'} (l : list A) (m : list B) (P : type1413 A B) : (@ALLPAIRS B A P l m) = (term43 A B l m P).
Proof. exact (@lem1184608 B A l m P). Qed.
Lemma lem1184610 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (@ALLPAIRS B A R l m) = (term43 A B l m R).
Proof. exact (@lem1184609 A B l m R). Qed.
Lemma lem1184623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1184624 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term44 A B R l m) = (term45 A B l m R).
Proof. exact (MK_COMB (@lem1184623) (@lem1184610 A B l m R)). Qed.
Lemma lem1184626 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (@ALLPAIRS _27494 _27495 P l m) = (term16 _27494 _27495 l m P).
Proof. exact (EQ_MP (@lem1184535 _27494 _27495 l m P) (@lem1184534 _27494 _27495 l P m)). Qed.
Lemma lem1184627 {A B : Type'} (l : list A) (m : list B) (P : type1413 A B) : (@ALLPAIRS B A P l m) = (term43 A B l m P).
Proof. exact (@lem1184626 B A l m P). Qed.
Lemma lem1184628 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (@ALLPAIRS B A R' l m) = (term43 A B l m R').
Proof. exact (@lem1184627 A B l m R'). Qed.
Lemma lem1184641 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((@ALLPAIRS B A R l m) = (@ALLPAIRS B A R' l m)) = ((term43 A B l m R) = (term43 A B l m R')).
Proof. exact (MK_COMB (@lem1184624 A B l m R) (@lem1184628 A B l m R')). Qed.
Lemma lem1184644 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term46 A B P Q R R' l m) = (term47 A B P Q R l m R').
Proof. exact (MK_COMB (@lem1184604 A B l m P Q R R') (@lem1184641 A B R l m R')). Qed.
Lemma lem1184647 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term48 A B P R R' l m) = (term49 A B P R l m R').
Proof. exact (fun_ext (fun Q : B -> Prop => @lem1184644 A B P Q R l m R')). Qed.
Lemma lem1184648 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem1184649 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term50 A B P R R' l m) = (term51 A B P R l m R').
Proof. exact (MK_COMB (@lem1184648 B) (@lem1184647 A B P R l m R')). Qed.
Lemma lem1184654 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term52 A B R R' l m) = (term53 A B R l m R').
Proof. exact (fun_ext (fun P : A -> Prop => @lem1184649 A B P R l m R')). Qed.
Lemma lem1184655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1184656 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term54 A B R R' l m) = (term55 A B R l m R').
Proof. exact (MK_COMB (@lem1184655 A) (@lem1184654 A B R l m R')). Qed.
Lemma lem1184661 {A B : Type'} (R : type1413 A B) (l : list A) (R' : type1413 A B) : (term56 A B R R' l) = (term57 A B R l R').
Proof. exact (fun_ext (fun m : list B => @lem1184656 A B R l m R')). Qed.
Lemma lem1184662 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1184663 {A B : Type'} (R : type1413 A B) (l : list A) (R' : type1413 A B) : (term58 A B R R' l) = (term59 A B R l R').
Proof. exact (MK_COMB (@lem1184662 B) (@lem1184661 A B R l R')). Qed.
Lemma lem1184668 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term60 A B R R') = (term61 A B R R').
Proof. exact (fun_ext (fun l : list A => @lem1184663 A B R l R')). Qed.
Lemma lem1184669 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1184670 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term62 A B R R') = (term63 A B R R').
Proof. exact (MK_COMB (@lem1184669 A) (@lem1184668 A B R R')). Qed.
Lemma lem1184675 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term63 A B R R') = (term62 A B R R').
Proof. exact (SYM (@lem1184670 A B R R')). Qed.
Lemma lem1184677 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1184678 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term63 A B R R') = (term65 A B R R').
Proof. exact (@lem1184677 (term63 A B R R')). Qed.
Lemma lem1184679 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term65 A B R R') = (term63 A B R R').
Proof. exact (SYM (@lem1184678 A B R R')). Qed.
Lemma lem1184680 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term66 A B R R') : term66 A B R R'.
Proof. exact (h1). Qed.
Lemma lem1184683 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term65 A B R R') : term65 A B R R'.
Proof. exact (h1). Qed.
Lemma lem1184684 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term67 A B R R'.
Proof. exact (fun h0 : term65 A B R R' => @lem1184683 A B R R' h0). Qed.
Lemma lem1184685 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term67 A B R R') : term67 A B R R'.
Proof. exact (h1). Qed.
Lemma lem1184686 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term65 A B R R') : term65 A B R R'.
Proof. exact (h1). Qed.
Lemma lem1184687 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term65 A B R R') (h2 : term67 A B R R') : term65 A B R R'.
Proof. exact (@lem1184685 A B R R' h2 (@lem1184686 A B R R' h1)). Qed.
Lemma lem1184688 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term65 A B R R') : term68 A B R R'.
Proof. exact (fun h0 : term67 A B R R' => @lem1184687 A B R R' h1 h0). Qed.
Lemma lem1184689 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term67 A B R R') : term67 A B R R'.
Proof. exact (h1). Qed.
Lemma lem1184690 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term65 A B R R') (h2 : term67 A B R R') : term65 A B R R'.
Proof. exact (@lem1184688 A B R R' h1 (@lem1184689 A B R R' h2)). Qed.
Lemma lem1184691 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term67 A B R R') : term67 A B R R'.
Proof. exact (fun h0 : term65 A B R R' => @lem1184690 A B R R' h0 h1). Qed.
Lemma lem1184692 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term69 A B R R'.
Proof. exact (fun h0 : term67 A B R R' => @lem1184691 A B R R' h0). Qed.
Lemma lem1184695 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term67 A B R R'.
Proof. exact (@lem1184692 A B R R' (@lem1184684 A B R R')). Qed.
Lemma lem1184696 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term67 A B R R'.
Proof. exact (@lem1184695 A B R R'). Qed.
Lemma lem1184706 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1184707 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term65 A B R R') = (term70 A B R R').
Proof. exact (@lem1184706 (term66 A B R R')). Qed.
Lemma lem1184709 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1184710 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term70 A B R R') = (term63 A B R R').
Proof. exact (@lem1184709 (term63 A B R R')). Qed.
Lemma lem1184715 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term65 A B R R') = (term63 A B R R').
Proof. exact (TRANS (@lem1184707 A B R R') (@lem1184710 A B R R')). Qed.
Lemma lem1184782 {A B : Type'} (R' : type1413 A B) : (term72 A B R') = (term73 A B R').
Proof. exact (fun_ext (fun R : type1413 A B => @lem1184715 A B R R')). Qed.
Lemma lem1184783 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1184784 {A B : Type'} (R' : type1413 A B) : (term74 A B R') = (term75 A B R').
Proof. exact (MK_COMB (@lem1184783 A B) (@lem1184782 A B R')). Qed.
Lemma lem1184789 {A B : Type'} : (term76 A B) = (term77 A B).
Proof. exact (fun_ext (fun R' : type1413 A B => @lem1184784 A B R')). Qed.
Lemma lem1184790 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1184799 {A B : Type'} : (term78 A B) = (term79 A B).
Proof. exact (MK_COMB (@lem1184790 A B) (@lem1184789 A B)). Qed.
Lemma lem1184808 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term80 A B l m R' x y) = (term80 A B l m R' x y).
Proof. exact (eq_refl (term80 A B l m R' x y)). Qed.
Lemma lem1184809 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term81 A B l m R' x) = (term81 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1184808 A B l m R' x y)). Qed.
Lemma lem1184810 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1184811 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term82 A B l m R' x) = (term82 A B l m R' x).
Proof. exact (MK_COMB (@lem1184810 B) (@lem1184809 A B l m R' x)). Qed.
Lemma lem1184812 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term83 A B l m R') = (term83 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1184811 A B l m R' x)). Qed.
Lemma lem1184813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1184814 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term43 A B l m R') = (term43 A B l m R').
Proof. exact (MK_COMB (@lem1184813 A) (@lem1184812 A B l m R')). Qed.
Lemma lem1184823 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term80 A B l m R x y) = (term80 A B l m R x y).
Proof. exact (eq_refl (term80 A B l m R x y)). Qed.
Lemma lem1184824 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term81 A B l m R x) = (term81 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1184823 A B l m R x y)). Qed.
Lemma lem1184825 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1184826 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term82 A B l m R x) = (term82 A B l m R x).
Proof. exact (MK_COMB (@lem1184825 B) (@lem1184824 A B l m R x)). Qed.
Lemma lem1184827 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term83 A B l m R) = (term83 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1184826 A B l m R x)). Qed.
Lemma lem1184828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1184829 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term43 A B l m R) = (term43 A B l m R).
Proof. exact (MK_COMB (@lem1184828 A) (@lem1184827 A B l m R)). Qed.
Lemma lem1184830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1184831 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term45 A B l m R) = (term45 A B l m R).
Proof. exact (MK_COMB (@lem1184830) (@lem1184829 A B l m R)). Qed.
Lemma lem1184832 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((term43 A B l m R) = (term43 A B l m R')) = ((term43 A B l m R) = (term43 A B l m R')).
Proof. exact (MK_COMB (@lem1184831 A B l m R) (@lem1184814 A B l m R')). Qed.
Lemma lem1184845 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term84 A B P Q R R' p q) = (term84 A B P Q R R' p q).
Proof. exact (eq_refl (term84 A B P Q R R' p q)). Qed.
Lemma lem1184846 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term85 A B P Q R R' p) = (term85 A B P Q R R' p).
Proof. exact (fun_ext (fun q : B => @lem1184845 A B P Q R R' p q)). Qed.
Lemma lem1184847 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1184848 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term86 A B P Q R R' p) = (term86 A B P Q R R' p).
Proof. exact (MK_COMB (@lem1184847 B) (@lem1184846 A B P Q R R' p)). Qed.
Lemma lem1184849 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term87 A B P Q R R') = (term87 A B P Q R R').
Proof. exact (fun_ext (fun p : A => @lem1184848 A B P Q R R' p)). Qed.
Lemma lem1184850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1184851 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term36 A B P Q R R') = (term36 A B P Q R R').
Proof. exact (MK_COMB (@lem1184850 A) (@lem1184849 A B P Q R R')). Qed.
Lemma lem1184856 {B : Type'} (m : list B) (Q : B -> Prop) (x : B) : (term88 B m Q x) = (term88 B m Q x).
Proof. exact (eq_refl (term88 B m Q x)). Qed.
Lemma lem1184857 {B : Type'} (m : list B) (Q : B -> Prop) : (term89 B m Q) = (term89 B m Q).
Proof. exact (fun_ext (fun x : B => @lem1184856 B m Q x)). Qed.
Lemma lem1184858 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1184859 {B : Type'} (m : list B) (Q : B -> Prop) : (term7 B m Q) = (term7 B m Q).
Proof. exact (MK_COMB (@lem1184858 B) (@lem1184857 B m Q)). Qed.
Lemma lem1184860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184861 {B : Type'} (m : list B) (Q : B -> Prop) : (term35 B m Q) = (term35 B m Q).
Proof. exact (MK_COMB (@lem1184860) (@lem1184859 B m Q)). Qed.
Lemma lem1184862 {A B : Type'} (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term38 A B m P Q R R') = (term38 A B m P Q R R').
Proof. exact (MK_COMB (@lem1184861 B m Q) (@lem1184851 A B P Q R R')). Qed.
Lemma lem1184867 {A : Type'} (l : list A) (P : A -> Prop) (x : A) : (term88 A l P x) = (term88 A l P x).
Proof. exact (eq_refl (term88 A l P x)). Qed.
Lemma lem1184868 {A : Type'} (l : list A) (P : A -> Prop) : (term89 A l P) = (term89 A l P).
Proof. exact (fun_ext (fun x : A => @lem1184867 A l P x)). Qed.
Lemma lem1184869 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1184870 {A : Type'} (l : list A) (P : A -> Prop) : (term7 A l P) = (term7 A l P).
Proof. exact (MK_COMB (@lem1184869 A) (@lem1184868 A l P)). Qed.
Lemma lem1184871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184872 {A : Type'} (l : list A) (P : A -> Prop) : (term35 A l P) = (term35 A l P).
Proof. exact (MK_COMB (@lem1184871) (@lem1184870 A l P)). Qed.
Lemma lem1184873 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term40 A B l m P Q R R') = (term40 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1184872 A l P) (@lem1184862 A B m P Q R R')). Qed.
Lemma lem1184874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1184875 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term42 A B l m P Q R R') = (term42 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1184874) (@lem1184873 A B l m P Q R R')). Qed.
Lemma lem1184876 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term47 A B P Q R l m R') = (term47 A B P Q R l m R').
Proof. exact (MK_COMB (@lem1184875 A B l m P Q R R') (@lem1184832 A B R l m R')). Qed.
Lemma lem1184877 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term49 A B P R l m R') = (term49 A B P R l m R').
Proof. exact (fun_ext (fun Q : B -> Prop => @lem1184876 A B P Q R l m R')). Qed.
Lemma lem1184878 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem1184879 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term51 A B P R l m R') = (term51 A B P R l m R').
Proof. exact (MK_COMB (@lem1184878 B) (@lem1184877 A B P R l m R')). Qed.
Lemma lem1184880 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term53 A B R l m R') = (term53 A B R l m R').
Proof. exact (fun_ext (fun P : A -> Prop => @lem1184879 A B P R l m R')). Qed.
Lemma lem1184881 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1184882 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term55 A B R l m R') = (term55 A B R l m R').
Proof. exact (MK_COMB (@lem1184881 A) (@lem1184880 A B R l m R')). Qed.
Lemma lem1184883 {A B : Type'} (R : type1413 A B) (l : list A) (R' : type1413 A B) : (term57 A B R l R') = (term57 A B R l R').
Proof. exact (fun_ext (fun m : list B => @lem1184882 A B R l m R')). Qed.
Lemma lem1184884 {B : Type'} : (@all (list B)) = (@all (list B)).
Proof. exact (eq_refl (@all (list B))). Qed.
Lemma lem1184885 {A B : Type'} (R : type1413 A B) (l : list A) (R' : type1413 A B) : (term59 A B R l R') = (term59 A B R l R').
Proof. exact (MK_COMB (@lem1184884 B) (@lem1184883 A B R l R')). Qed.
Lemma lem1184886 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term61 A B R R') = (term61 A B R R').
Proof. exact (fun_ext (fun l : list A => @lem1184885 A B R l R')). Qed.
Lemma lem1184887 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1184888 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term63 A B R R') = (term63 A B R R').
Proof. exact (MK_COMB (@lem1184887 A) (@lem1184886 A B R R')). Qed.
Lemma lem1184889 {A B : Type'} (R' : type1413 A B) : (term73 A B R') = (term73 A B R').
Proof. exact (fun_ext (fun R : type1413 A B => @lem1184888 A B R R')). Qed.
Lemma lem1184890 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1184891 {A B : Type'} (R' : type1413 A B) : (term75 A B R') = (term75 A B R').
Proof. exact (MK_COMB (@lem1184890 A B) (@lem1184889 A B R')). Qed.
Lemma lem1184892 {A B : Type'} : (term77 A B) = (term77 A B).
Proof. exact (fun_ext (fun R' : type1413 A B => @lem1184891 A B R')). Qed.
Lemma lem1184893 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem1184894 {A B : Type'} : (term79 A B) = (term79 A B).
Proof. exact (MK_COMB (@lem1184893 A B) (@lem1184892 A B)). Qed.
Lemma lem1185003 {A B : Type'} : (term78 A B) = (term79 A B).
Proof. exact (TRANS (@lem1184799 A B) (@lem1184894 A B)). Qed.
Lemma lem1185004 {A B : Type'} : (term79 A B) = (term78 A B).
Proof. exact (SYM (@lem1185003 A B)). Qed.
Lemma lem1185005 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term40 A B l m P Q R R'.
Proof. exact (h1). Qed.
Lemma lem1185007 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1185008 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((term43 A B l m R) = (term43 A B l m R')) = (term90 A B R l m R').
Proof. exact (@lem1185007 ((term43 A B l m R) = (term43 A B l m R'))). Qed.
Lemma lem1185009 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term90 A B R l m R') = ((term43 A B l m R) = (term43 A B l m R')).
Proof. exact (SYM (@lem1185008 A B R l m R')). Qed.
Lemma lem1185010 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term91 A B R l m R') : term91 A B R l m R'.
Proof. exact (h1). Qed.
Lemma lem1185017 {A : Type'} (l : list A) (P : A -> Prop) (x : A) : (term88 A l P x) = (term92 A l P x).
Proof. exact (@lem17265 (@List.In A x l) (P x)). Qed.
Lemma lem1185018 {A : Type'} (l : list A) (P : A -> Prop) : (term89 A l P) = (term93 A l P).
Proof. exact (fun_ext (fun x : A => @lem1185017 A l P x)). Qed.
Lemma lem1185019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185020 {A : Type'} (l : list A) (P : A -> Prop) : (term7 A l P) = (term94 A l P).
Proof. exact (MK_COMB (@lem1185019 A) (@lem1185018 A l P)). Qed.
Lemma lem1185027 {B : Type'} (m : list B) (Q : B -> Prop) (x : B) : (term88 B m Q x) = (term92 B m Q x).
Proof. exact (@lem17265 (@List.In B x m) (Q x)). Qed.
Lemma lem1185028 {B : Type'} (m : list B) (Q : B -> Prop) : (term89 B m Q) = (term93 B m Q).
Proof. exact (fun_ext (fun x : B => @lem1185027 B m Q x)). Qed.
Lemma lem1185029 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185030 {B : Type'} (m : list B) (Q : B -> Prop) : (term7 B m Q) = (term94 B m Q).
Proof. exact (MK_COMB (@lem1185029 B) (@lem1185028 B m Q)). Qed.
Lemma lem1185037 {A B : Type'} (P : A -> Prop) (p : A) (Q : B -> Prop) (q : B) : (term95 A B P p Q q) = (term96 A B P p Q q).
Proof. exact (@lem17045 (P p) (Q q)). Qed.
Lemma lem1185052 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : ((R p q) = (R' p q)) = (term97 A B R R' p q).
Proof. exact (@lem17784 (R p q) (R' p q)). Qed.
Lemma lem1185053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185054 {A B : Type'} (P : A -> Prop) (p : A) (Q : B -> Prop) (q : B) : (term98 A B P p Q q) = (term99 A B P p Q q).
Proof. exact (MK_COMB (@lem1185053) (@lem1185037 A B P p Q q)). Qed.
Lemma lem1185055 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term100 A B P Q R R' p q) = (term101 A B P Q R R' p q).
Proof. exact (MK_COMB (@lem1185054 A B P p Q q) (@lem1185052 A B R R' p q)). Qed.
Lemma lem1185056 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term84 A B P Q R R' p q) = (term100 A B P Q R R' p q).
Proof. exact (@lem17265 (term102 A B P p Q q) ((R p q) = (R' p q))). Qed.
Lemma lem1185057 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term84 A B P Q R R' p q) = (term101 A B P Q R R' p q).
Proof. exact (TRANS (@lem1185056 A B P Q R R' p q) (@lem1185055 A B P Q R R' p q)). Qed.
Lemma lem1185058 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term85 A B P Q R R' p) = (term103 A B P Q R R' p).
Proof. exact (fun_ext (fun q : B => @lem1185057 A B P Q R R' p q)). Qed.
Lemma lem1185059 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185060 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term86 A B P Q R R' p) = (term104 A B P Q R R' p).
Proof. exact (MK_COMB (@lem1185059 B) (@lem1185058 A B P Q R R' p)). Qed.
Lemma lem1185061 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term87 A B P Q R R') = (term105 A B P Q R R').
Proof. exact (fun_ext (fun p : A => @lem1185060 A B P Q R R' p)). Qed.
Lemma lem1185062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185063 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term36 A B P Q R R') = (term106 A B P Q R R').
Proof. exact (MK_COMB (@lem1185062 A) (@lem1185061 A B P Q R R')). Qed.
Lemma lem1185064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185065 {B : Type'} (m : list B) (Q : B -> Prop) : (term35 B m Q) = (term107 B m Q).
Proof. exact (MK_COMB (@lem1185064) (@lem1185030 B m Q)). Qed.
Lemma lem1185066 {A B : Type'} (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term38 A B m P Q R R') = (term108 A B m P Q R R').
Proof. exact (MK_COMB (@lem1185065 B m Q) (@lem1185063 A B P Q R R')). Qed.
Lemma lem1185067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185068 {A : Type'} (l : list A) (P : A -> Prop) : (term35 A l P) = (term107 A l P).
Proof. exact (MK_COMB (@lem1185067) (@lem1185020 A l P)). Qed.
Lemma lem1185189 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term40 A B l m P Q R R') = (term109 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1185068 A l P) (@lem1185066 A B m P Q R R')). Qed.
Lemma lem1185190 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term109 A B l m P Q R R'.
Proof. exact (EQ_MP (@lem1185189 A B l m P Q R R') (@lem1185005 A B l m P Q R R' h1)). Qed.
Lemma lem1185199 {A B : Type'} (x : A) (l : list A) (y : B) (m : list B) : (term110 A B x l y m) = (term111 A B x l y m).
Proof. exact (@lem17045 (@List.In A x l) (@List.In B y m)). Qed.
Lemma lem1185204 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1185209 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term112 A B l m R x y) = (term113 A B l m R x y).
Proof. exact (@lem17362 (term114 A B x l y m) (R x y)). Qed.
Lemma lem1185210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185211 {A B : Type'} (x : A) (l : list A) (y : B) (m : list B) : (term115 A B x l y m) = (term116 A B x l y m).
Proof. exact (MK_COMB (@lem1185210) (@lem1185199 A B x l y m)). Qed.
Lemma lem1185212 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term117 A B l m R x y) = (term118 A B l m R x y).
Proof. exact (MK_COMB (@lem1185211 A B x l y m) (@lem1185204 A B R x y)). Qed.
Lemma lem1185213 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term80 A B l m R x y) = (term117 A B l m R x y).
Proof. exact (@lem17265 (term114 A B x l y m) (R x y)). Qed.
Lemma lem1185214 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term80 A B l m R x y) = (term118 A B l m R x y).
Proof. exact (TRANS (@lem1185213 A B l m R x y) (@lem1185212 A B l m R x y)). Qed.
Lemma lem1185215 {B : Type'} (P : B -> Prop) : (term119 B P) = (term120 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem1185216 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term121 A B l m R x) = (term122 A B l m R x).
Proof. exact (@lem1185215 B (term81 A B l m R x)). Qed.
Lemma lem1185217 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term123 A B l m R x y) = (term80 A B l m R x y).
Proof. exact (eq_refl (term123 A B l m R x y)). Qed.
Lemma lem1185218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1185219 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term124 A B l m R x y) = (term112 A B l m R x y).
Proof. exact (MK_COMB (@lem1185218) (@lem1185217 A B l m R x y)). Qed.
Lemma lem1185220 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term124 A B l m R x y) = (term113 A B l m R x y).
Proof. exact (TRANS (@lem1185219 A B l m R x y) (@lem1185209 A B l m R x y)). Qed.
Lemma lem1185221 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term125 A B l m R x) = (term126 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1185220 A B l m R x y)). Qed.
Lemma lem1185222 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185223 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term122 A B l m R x) = (term127 A B l m R x).
Proof. exact (MK_COMB (@lem1185222 B) (@lem1185221 A B l m R x)). Qed.
Lemma lem1185224 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term121 A B l m R x) = (term127 A B l m R x).
Proof. exact (TRANS (@lem1185216 A B l m R x) (@lem1185223 A B l m R x)). Qed.
Lemma lem1185225 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term81 A B l m R x) = (term128 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1185214 A B l m R x y)). Qed.
Lemma lem1185226 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185227 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term82 A B l m R x) = (term129 A B l m R x).
Proof. exact (MK_COMB (@lem1185226 B) (@lem1185225 A B l m R x)). Qed.
Lemma lem1185228 {A : Type'} (P : A -> Prop) : (term119 A P) = (term120 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1185229 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term130 A B l m R) = (term131 A B l m R).
Proof. exact (@lem1185228 A (term83 A B l m R)). Qed.
Lemma lem1185230 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term132 A B l m R x) = (term82 A B l m R x).
Proof. exact (eq_refl (term132 A B l m R x)). Qed.
Lemma lem1185231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1185232 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term133 A B l m R x) = (term121 A B l m R x).
Proof. exact (MK_COMB (@lem1185231) (@lem1185230 A B l m R x)). Qed.
Lemma lem1185233 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term133 A B l m R x) = (term127 A B l m R x).
Proof. exact (TRANS (@lem1185232 A B l m R x) (@lem1185224 A B l m R x)). Qed.
Lemma lem1185234 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term134 A B l m R) = (term135 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1185233 A B l m R x)). Qed.
Lemma lem1185235 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185236 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term131 A B l m R) = (term136 A B l m R).
Proof. exact (MK_COMB (@lem1185235 A) (@lem1185234 A B l m R)). Qed.
Lemma lem1185237 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term130 A B l m R) = (term136 A B l m R).
Proof. exact (TRANS (@lem1185229 A B l m R) (@lem1185236 A B l m R)). Qed.
Lemma lem1185238 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term83 A B l m R) = (term137 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1185227 A B l m R x)). Qed.
Lemma lem1185239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185240 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term43 A B l m R) = (term138 A B l m R).
Proof. exact (MK_COMB (@lem1185239 A) (@lem1185238 A B l m R)). Qed.
Lemma lem1185249 {A B : Type'} (x : A) (l : list A) (y : B) (m : list B) : (term110 A B x l y m) = (term111 A B x l y m).
Proof. exact (@lem17045 (@List.In A x l) (@List.In B y m)). Qed.
Lemma lem1185254 {A B : Type'} (R' : type1413 A B) (x : A) (y : B) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem1185259 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term112 A B l m R' x y) = (term113 A B l m R' x y).
Proof. exact (@lem17362 (term114 A B x l y m) (R' x y)). Qed.
Lemma lem1185260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185261 {A B : Type'} (x : A) (l : list A) (y : B) (m : list B) : (term115 A B x l y m) = (term116 A B x l y m).
Proof. exact (MK_COMB (@lem1185260) (@lem1185249 A B x l y m)). Qed.
Lemma lem1185262 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term117 A B l m R' x y) = (term118 A B l m R' x y).
Proof. exact (MK_COMB (@lem1185261 A B x l y m) (@lem1185254 A B R' x y)). Qed.
Lemma lem1185263 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term80 A B l m R' x y) = (term117 A B l m R' x y).
Proof. exact (@lem17265 (term114 A B x l y m) (R' x y)). Qed.
Lemma lem1185264 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term80 A B l m R' x y) = (term118 A B l m R' x y).
Proof. exact (TRANS (@lem1185263 A B l m R' x y) (@lem1185262 A B l m R' x y)). Qed.
Lemma lem1185265 {B : Type'} (P : B -> Prop) : (term119 B P) = (term120 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem1185266 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term121 A B l m R' x) = (term122 A B l m R' x).
Proof. exact (@lem1185265 B (term81 A B l m R' x)). Qed.
Lemma lem1185267 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term123 A B l m R' x y) = (term80 A B l m R' x y).
Proof. exact (eq_refl (term123 A B l m R' x y)). Qed.
Lemma lem1185268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1185269 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term124 A B l m R' x y) = (term112 A B l m R' x y).
Proof. exact (MK_COMB (@lem1185268) (@lem1185267 A B l m R' x y)). Qed.
Lemma lem1185270 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term124 A B l m R' x y) = (term113 A B l m R' x y).
Proof. exact (TRANS (@lem1185269 A B l m R' x y) (@lem1185259 A B l m R' x y)). Qed.
Lemma lem1185271 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term125 A B l m R' x) = (term126 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185270 A B l m R' x y)). Qed.
Lemma lem1185272 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185273 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term122 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (MK_COMB (@lem1185272 B) (@lem1185271 A B l m R' x)). Qed.
Lemma lem1185274 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term121 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (TRANS (@lem1185266 A B l m R' x) (@lem1185273 A B l m R' x)). Qed.
Lemma lem1185275 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term81 A B l m R' x) = (term128 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185264 A B l m R' x y)). Qed.
Lemma lem1185276 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185277 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term82 A B l m R' x) = (term129 A B l m R' x).
Proof. exact (MK_COMB (@lem1185276 B) (@lem1185275 A B l m R' x)). Qed.
Lemma lem1185278 {A : Type'} (P : A -> Prop) : (term119 A P) = (term120 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1185279 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term130 A B l m R') = (term131 A B l m R').
Proof. exact (@lem1185278 A (term83 A B l m R')). Qed.
Lemma lem1185280 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term132 A B l m R' x) = (term82 A B l m R' x).
Proof. exact (eq_refl (term132 A B l m R' x)). Qed.
Lemma lem1185281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1185282 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term133 A B l m R' x) = (term121 A B l m R' x).
Proof. exact (MK_COMB (@lem1185281) (@lem1185280 A B l m R' x)). Qed.
Lemma lem1185283 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term133 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (TRANS (@lem1185282 A B l m R' x) (@lem1185274 A B l m R' x)). Qed.
Lemma lem1185284 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term134 A B l m R') = (term135 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1185283 A B l m R' x)). Qed.
Lemma lem1185285 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185286 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term131 A B l m R') = (term136 A B l m R').
Proof. exact (MK_COMB (@lem1185285 A) (@lem1185284 A B l m R')). Qed.
Lemma lem1185287 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term130 A B l m R') = (term136 A B l m R').
Proof. exact (TRANS (@lem1185279 A B l m R') (@lem1185286 A B l m R')). Qed.
Lemma lem1185288 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term83 A B l m R') = (term137 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1185277 A B l m R' x)). Qed.
Lemma lem1185289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185290 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term43 A B l m R') = (term138 A B l m R').
Proof. exact (MK_COMB (@lem1185289 A) (@lem1185288 A B l m R')). Qed.
Lemma lem1185291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185292 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term139 A B l m R) = (term140 A B l m R).
Proof. exact (MK_COMB (@lem1185291) (@lem1185237 A B l m R)). Qed.
Lemma lem1185293 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term141 A B R l m R') = (term142 A B R l m R').
Proof. exact (MK_COMB (@lem1185292 A B l m R) (@lem1185290 A B l m R')). Qed.
Lemma lem1185294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185295 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term143 A B l m R) = (term144 A B l m R).
Proof. exact (MK_COMB (@lem1185294) (@lem1185240 A B l m R)). Qed.
Lemma lem1185296 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term145 A B R l m R') = (term146 A B R l m R').
Proof. exact (MK_COMB (@lem1185295 A B l m R) (@lem1185287 A B l m R')). Qed.
Lemma lem1185297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185298 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term147 A B R l m R') = (term148 A B R l m R').
Proof. exact (MK_COMB (@lem1185297) (@lem1185296 A B R l m R')). Qed.
Lemma lem1185299 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term149 A B R l m R') = (term150 A B R l m R').
Proof. exact (MK_COMB (@lem1185298 A B R l m R') (@lem1185293 A B R l m R')). Qed.
Lemma lem1185300 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term91 A B R l m R') = (term149 A B R l m R').
Proof. exact (@lem17646 (term43 A B l m R) (term43 A B l m R')). Qed.
Lemma lem1185301 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term91 A B R l m R') = (term150 A B R l m R').
Proof. exact (TRANS (@lem1185300 A B R l m R') (@lem1185299 A B R l m R')). Qed.
Lemma lem1185512 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1185513 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (@lem1185512 A P Q). Qed.
Lemma lem1185514 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term153 A B R l m R') = (term154 A B R l m R').
Proof. exact (@lem1185513 A (term138 A B l m R) (term135 A B l m R')). Qed.
Lemma lem1185515 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term155 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (eq_refl (term155 A B l m R' x)). Qed.
Lemma lem1185516 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term156 A B l m R') = (term135 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1185515 A B l m R' x)). Qed.
Lemma lem1185517 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185518 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term157 A B l m R') = (term136 A B l m R').
Proof. exact (MK_COMB (@lem1185517 A) (@lem1185516 A B l m R')). Qed.
Lemma lem1185519 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term144 A B l m R) = (term144 A B l m R).
Proof. exact (eq_refl (term144 A B l m R)). Qed.
Lemma lem1185520 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term153 A B R l m R') = (term146 A B R l m R').
Proof. exact (MK_COMB (@lem1185519 A B l m R) (@lem1185518 A B l m R')). Qed.
Lemma lem1185521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185522 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term158 A B R l m R') = (term159 A B R l m R').
Proof. exact (MK_COMB (@lem1185521) (@lem1185520 A B R l m R')). Qed.
Lemma lem1185523 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term155 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (eq_refl (term155 A B l m R' x)). Qed.
Lemma lem1185524 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term144 A B l m R) = (term144 A B l m R).
Proof. exact (eq_refl (term144 A B l m R)). Qed.
Lemma lem1185525 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term160 A B R l m R' x) = (term161 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185524 A B l m R) (@lem1185523 A B l m R' x)). Qed.
Lemma lem1185526 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term162 A B R l m R') = (term163 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185525 A B R l m R' x)). Qed.
Lemma lem1185527 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185528 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term154 A B R l m R') = (term164 A B R l m R').
Proof. exact (MK_COMB (@lem1185527 A) (@lem1185526 A B R l m R')). Qed.
Lemma lem1185529 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((term153 A B R l m R') = (term154 A B R l m R')) = ((term146 A B R l m R') = (term164 A B R l m R')).
Proof. exact (MK_COMB (@lem1185522 A B R l m R') (@lem1185528 A B R l m R')). Qed.
Lemma lem1185530 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term146 A B R l m R') = (term164 A B R l m R').
Proof. exact (EQ_MP (@lem1185529 A B R l m R') (@lem1185514 A B R l m R')). Qed.
Lemma lem1185532 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1185533 {B : Type'} (P : Prop) (Q : B -> Prop) : (term151 B P Q) = (term152 B P Q).
Proof. exact (@lem1185532 B P Q). Qed.
Lemma lem1185534 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term165 A B R l m R' x) = (term166 A B R l m R' x).
Proof. exact (@lem1185533 B (term138 A B l m R) (term126 A B l m R' x)). Qed.
Lemma lem1185535 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term167 A B l m R' x y) = (term113 A B l m R' x y).
Proof. exact (eq_refl (term167 A B l m R' x y)). Qed.
Lemma lem1185536 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term168 A B l m R' x) = (term126 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185535 A B l m R' x y)). Qed.
Lemma lem1185537 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185538 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term169 A B l m R' x) = (term127 A B l m R' x).
Proof. exact (MK_COMB (@lem1185537 B) (@lem1185536 A B l m R' x)). Qed.
Lemma lem1185539 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term144 A B l m R) = (term144 A B l m R).
Proof. exact (eq_refl (term144 A B l m R)). Qed.
Lemma lem1185540 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term165 A B R l m R' x) = (term161 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185539 A B l m R) (@lem1185538 A B l m R' x)). Qed.
Lemma lem1185541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185542 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term170 A B R l m R' x) = (term171 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185541) (@lem1185540 A B R l m R' x)). Qed.
Lemma lem1185543 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term167 A B l m R' x y) = (term113 A B l m R' x y).
Proof. exact (eq_refl (term167 A B l m R' x y)). Qed.
Lemma lem1185544 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term144 A B l m R) = (term144 A B l m R).
Proof. exact (eq_refl (term144 A B l m R)). Qed.
Lemma lem1185545 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term172 A B R l m R' x y) = (term173 A B R l m R' x y).
Proof. exact (MK_COMB (@lem1185544 A B l m R) (@lem1185543 A B l m R' x y)). Qed.
Lemma lem1185546 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term174 A B R l m R' x) = (term175 A B R l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185545 A B R l m R' x y)). Qed.
Lemma lem1185547 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185548 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term166 A B R l m R' x) = (term176 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185547 B) (@lem1185546 A B R l m R' x)). Qed.
Lemma lem1185549 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : ((term165 A B R l m R' x) = (term166 A B R l m R' x)) = ((term161 A B R l m R' x) = (term176 A B R l m R' x)).
Proof. exact (MK_COMB (@lem1185542 A B R l m R' x) (@lem1185548 A B R l m R' x)). Qed.
Lemma lem1185550 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term161 A B R l m R' x) = (term176 A B R l m R' x).
Proof. exact (EQ_MP (@lem1185549 A B R l m R' x) (@lem1185534 A B R l m R' x)). Qed.
Lemma lem1185551 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term163 A B R l m R') = (term177 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185550 A B R l m R' x)). Qed.
Lemma lem1185552 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185553 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term164 A B R l m R') = (term178 A B R l m R').
Proof. exact (MK_COMB (@lem1185552 A) (@lem1185551 A B R l m R')). Qed.
Lemma lem1185554 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term146 A B R l m R') = (term178 A B R l m R').
Proof. exact (TRANS (@lem1185530 A B R l m R') (@lem1185553 A B R l m R')). Qed.
Lemma lem1185555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185556 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term148 A B R l m R') = (term179 A B R l m R').
Proof. exact (MK_COMB (@lem1185555) (@lem1185554 A B R l m R')). Qed.
Lemma lem1185558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1185559 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem1185558 A P Q). Qed.
Lemma lem1185560 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term182 A B R l m R') = (term183 A B R l m R').
Proof. exact (@lem1185559 A (term135 A B l m R) (term138 A B l m R')). Qed.
Lemma lem1185561 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term155 A B l m R x) = (term127 A B l m R x).
Proof. exact (eq_refl (term155 A B l m R x)). Qed.
Lemma lem1185562 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term156 A B l m R) = (term135 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1185561 A B l m R x)). Qed.
Lemma lem1185563 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185564 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term157 A B l m R) = (term136 A B l m R).
Proof. exact (MK_COMB (@lem1185563 A) (@lem1185562 A B l m R)). Qed.
Lemma lem1185565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185566 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term184 A B l m R) = (term140 A B l m R).
Proof. exact (MK_COMB (@lem1185565) (@lem1185564 A B l m R)). Qed.
Lemma lem1185567 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (eq_refl (term138 A B l m R')). Qed.
Lemma lem1185568 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term182 A B R l m R') = (term142 A B R l m R').
Proof. exact (MK_COMB (@lem1185566 A B l m R) (@lem1185567 A B l m R')). Qed.
Lemma lem1185569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185570 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term185 A B R l m R') = (term186 A B R l m R').
Proof. exact (MK_COMB (@lem1185569) (@lem1185568 A B R l m R')). Qed.
Lemma lem1185571 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term155 A B l m R x) = (term127 A B l m R x).
Proof. exact (eq_refl (term155 A B l m R x)). Qed.
Lemma lem1185572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185573 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term187 A B l m R x) = (term188 A B l m R x).
Proof. exact (MK_COMB (@lem1185572) (@lem1185571 A B l m R x)). Qed.
Lemma lem1185574 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (eq_refl (term138 A B l m R')). Qed.
Lemma lem1185575 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term189 A B R x l m R') = (term190 A B R x l m R').
Proof. exact (MK_COMB (@lem1185573 A B l m R x) (@lem1185574 A B l m R')). Qed.
Lemma lem1185576 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term191 A B R l m R') = (term192 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185575 A B R x l m R')). Qed.
Lemma lem1185577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185578 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term183 A B R l m R') = (term193 A B R l m R').
Proof. exact (MK_COMB (@lem1185577 A) (@lem1185576 A B R l m R')). Qed.
Lemma lem1185579 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((term182 A B R l m R') = (term183 A B R l m R')) = ((term142 A B R l m R') = (term193 A B R l m R')).
Proof. exact (MK_COMB (@lem1185570 A B R l m R') (@lem1185578 A B R l m R')). Qed.
Lemma lem1185580 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term142 A B R l m R') = (term193 A B R l m R').
Proof. exact (EQ_MP (@lem1185579 A B R l m R') (@lem1185560 A B R l m R')). Qed.
Lemma lem1185582 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1185583 {B : Type'} (P : B -> Prop) (Q : Prop) : (term180 B P Q) = (term181 B P Q).
Proof. exact (@lem1185582 B P Q). Qed.
Lemma lem1185584 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term194 A B R x l m R') = (term195 A B R x l m R').
Proof. exact (@lem1185583 B (term126 A B l m R x) (term138 A B l m R')). Qed.
Lemma lem1185585 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term167 A B l m R x y) = (term113 A B l m R x y).
Proof. exact (eq_refl (term167 A B l m R x y)). Qed.
Lemma lem1185586 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term168 A B l m R x) = (term126 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1185585 A B l m R x y)). Qed.
Lemma lem1185587 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185588 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term169 A B l m R x) = (term127 A B l m R x).
Proof. exact (MK_COMB (@lem1185587 B) (@lem1185586 A B l m R x)). Qed.
Lemma lem1185589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185590 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term196 A B l m R x) = (term188 A B l m R x).
Proof. exact (MK_COMB (@lem1185589) (@lem1185588 A B l m R x)). Qed.
Lemma lem1185591 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (eq_refl (term138 A B l m R')). Qed.
Lemma lem1185592 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term194 A B R x l m R') = (term190 A B R x l m R').
Proof. exact (MK_COMB (@lem1185590 A B l m R x) (@lem1185591 A B l m R')). Qed.
Lemma lem1185593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185594 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term197 A B R x l m R') = (term198 A B R x l m R').
Proof. exact (MK_COMB (@lem1185593) (@lem1185592 A B R x l m R')). Qed.
Lemma lem1185595 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term167 A B l m R x y) = (term113 A B l m R x y).
Proof. exact (eq_refl (term167 A B l m R x y)). Qed.
Lemma lem1185596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185597 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term199 A B l m R x y) = (term200 A B l m R x y).
Proof. exact (MK_COMB (@lem1185596) (@lem1185595 A B l m R x y)). Qed.
Lemma lem1185598 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (eq_refl (term138 A B l m R')). Qed.
Lemma lem1185599 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term201 A B R x y l m R') = (term202 A B R x y l m R').
Proof. exact (MK_COMB (@lem1185597 A B l m R x y) (@lem1185598 A B l m R')). Qed.
Lemma lem1185600 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term203 A B R x l m R') = (term204 A B R x l m R').
Proof. exact (fun_ext (fun y : B => @lem1185599 A B R x y l m R')). Qed.
Lemma lem1185601 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185602 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term195 A B R x l m R') = (term205 A B R x l m R').
Proof. exact (MK_COMB (@lem1185601 B) (@lem1185600 A B R x l m R')). Qed.
Lemma lem1185603 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : ((term194 A B R x l m R') = (term195 A B R x l m R')) = ((term190 A B R x l m R') = (term205 A B R x l m R')).
Proof. exact (MK_COMB (@lem1185594 A B R x l m R') (@lem1185602 A B R x l m R')). Qed.
Lemma lem1185604 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term190 A B R x l m R') = (term205 A B R x l m R').
Proof. exact (EQ_MP (@lem1185603 A B R x l m R') (@lem1185584 A B R x l m R')). Qed.
Lemma lem1185605 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term192 A B R l m R') = (term206 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185604 A B R x l m R')). Qed.
Lemma lem1185606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185607 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term193 A B R l m R') = (term207 A B R l m R').
Proof. exact (MK_COMB (@lem1185606 A) (@lem1185605 A B R l m R')). Qed.
Lemma lem1185608 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term142 A B R l m R') = (term207 A B R l m R').
Proof. exact (TRANS (@lem1185580 A B R l m R') (@lem1185607 A B R l m R')). Qed.
Lemma lem1185609 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term150 A B R l m R') = (term208 A B R l m R').
Proof. exact (MK_COMB (@lem1185556 A B R l m R') (@lem1185608 A B R l m R')). Qed.
Lemma lem1185611 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1185612 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (@lem1185611 A P Q). Qed.
Lemma lem1185613 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term211 A B R l m R') = (term212 A B R l m R').
Proof. exact (@lem1185612 A (term177 A B R l m R') (term206 A B R l m R')). Qed.
Lemma lem1185614 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term213 A B R l m R' x) = (term176 A B R l m R' x).
Proof. exact (eq_refl (term213 A B R l m R' x)). Qed.
Lemma lem1185615 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term214 A B R l m R') = (term177 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185614 A B R l m R' x)). Qed.
Lemma lem1185616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185617 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term215 A B R l m R') = (term178 A B R l m R').
Proof. exact (MK_COMB (@lem1185616 A) (@lem1185615 A B R l m R')). Qed.
Lemma lem1185618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185619 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term216 A B R l m R') = (term179 A B R l m R').
Proof. exact (MK_COMB (@lem1185618) (@lem1185617 A B R l m R')). Qed.
Lemma lem1185620 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term217 A B R l m R' x) = (term205 A B R x l m R').
Proof. exact (eq_refl (term217 A B R l m R' x)). Qed.
Lemma lem1185621 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term218 A B R l m R') = (term206 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185620 A B R x l m R')). Qed.
Lemma lem1185622 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185623 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term219 A B R l m R') = (term207 A B R l m R').
Proof. exact (MK_COMB (@lem1185622 A) (@lem1185621 A B R l m R')). Qed.
Lemma lem1185624 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term211 A B R l m R') = (term208 A B R l m R').
Proof. exact (MK_COMB (@lem1185619 A B R l m R') (@lem1185623 A B R l m R')). Qed.
Lemma lem1185625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185626 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term220 A B R l m R') = (term221 A B R l m R').
Proof. exact (MK_COMB (@lem1185625) (@lem1185624 A B R l m R')). Qed.
Lemma lem1185627 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term213 A B R l m R' x) = (term176 A B R l m R' x).
Proof. exact (eq_refl (term213 A B R l m R' x)). Qed.
Lemma lem1185628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185629 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term222 A B R l m R' x) = (term223 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185628) (@lem1185627 A B R l m R' x)). Qed.
Lemma lem1185630 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term217 A B R l m R' x) = (term205 A B R x l m R').
Proof. exact (eq_refl (term217 A B R l m R' x)). Qed.
Lemma lem1185631 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term224 A B R l m R' x) = (term225 A B R x l m R').
Proof. exact (MK_COMB (@lem1185629 A B R l m R' x) (@lem1185630 A B R x l m R')). Qed.
Lemma lem1185632 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term226 A B R l m R') = (term227 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185631 A B R x l m R')). Qed.
Lemma lem1185633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185634 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term212 A B R l m R') = (term228 A B R l m R').
Proof. exact (MK_COMB (@lem1185633 A) (@lem1185632 A B R l m R')). Qed.
Lemma lem1185635 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : ((term211 A B R l m R') = (term212 A B R l m R')) = ((term208 A B R l m R') = (term228 A B R l m R')).
Proof. exact (MK_COMB (@lem1185626 A B R l m R') (@lem1185634 A B R l m R')). Qed.
Lemma lem1185636 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term208 A B R l m R') = (term228 A B R l m R').
Proof. exact (EQ_MP (@lem1185635 A B R l m R') (@lem1185613 A B R l m R')). Qed.
Lemma lem1185638 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1185639 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term209 B P Q) = (term210 B P Q).
Proof. exact (@lem1185638 B P Q). Qed.
Lemma lem1185640 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term229 A B R x l m R') = (term230 A B R x l m R').
Proof. exact (@lem1185639 B (term175 A B R l m R' x) (term204 A B R x l m R')). Qed.
Lemma lem1185641 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term231 A B R l m R' x y) = (term173 A B R l m R' x y).
Proof. exact (eq_refl (term231 A B R l m R' x y)). Qed.
Lemma lem1185642 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term232 A B R l m R' x) = (term175 A B R l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185641 A B R l m R' x y)). Qed.
Lemma lem1185643 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185644 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term233 A B R l m R' x) = (term176 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185643 B) (@lem1185642 A B R l m R' x)). Qed.
Lemma lem1185645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185646 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term234 A B R l m R' x) = (term223 A B R l m R' x).
Proof. exact (MK_COMB (@lem1185645) (@lem1185644 A B R l m R' x)). Qed.
Lemma lem1185647 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term235 A B R x l m R' y) = (term202 A B R x y l m R').
Proof. exact (eq_refl (term235 A B R x l m R' y)). Qed.
Lemma lem1185648 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term236 A B R x l m R') = (term204 A B R x l m R').
Proof. exact (fun_ext (fun y : B => @lem1185647 A B R x y l m R')). Qed.
Lemma lem1185649 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185650 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term237 A B R x l m R') = (term205 A B R x l m R').
Proof. exact (MK_COMB (@lem1185649 B) (@lem1185648 A B R x l m R')). Qed.
Lemma lem1185651 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term229 A B R x l m R') = (term225 A B R x l m R').
Proof. exact (MK_COMB (@lem1185646 A B R l m R' x) (@lem1185650 A B R x l m R')). Qed.
Lemma lem1185652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1185653 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term238 A B R x l m R') = (term239 A B R x l m R').
Proof. exact (MK_COMB (@lem1185652) (@lem1185651 A B R x l m R')). Qed.
Lemma lem1185654 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term231 A B R l m R' x y) = (term173 A B R l m R' x y).
Proof. exact (eq_refl (term231 A B R l m R' x y)). Qed.
Lemma lem1185655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185656 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term240 A B R l m R' x y) = (term241 A B R l m R' x y).
Proof. exact (MK_COMB (@lem1185655) (@lem1185654 A B R l m R' x y)). Qed.
Lemma lem1185657 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term235 A B R x l m R' y) = (term202 A B R x y l m R').
Proof. exact (eq_refl (term235 A B R x l m R' y)). Qed.
Lemma lem1185658 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term242 A B R x l m R' y) = (term243 A B R x y l m R').
Proof. exact (MK_COMB (@lem1185656 A B R l m R' x y) (@lem1185657 A B R x y l m R')). Qed.
Lemma lem1185659 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term244 A B R x l m R') = (term245 A B R x l m R').
Proof. exact (fun_ext (fun y : B => @lem1185658 A B R x y l m R')). Qed.
Lemma lem1185660 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem1185661 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term230 A B R x l m R') = (term246 A B R x l m R').
Proof. exact (MK_COMB (@lem1185660 B) (@lem1185659 A B R x l m R')). Qed.
Lemma lem1185662 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : ((term229 A B R x l m R') = (term230 A B R x l m R')) = ((term225 A B R x l m R') = (term246 A B R x l m R')).
Proof. exact (MK_COMB (@lem1185653 A B R x l m R') (@lem1185661 A B R x l m R')). Qed.
Lemma lem1185663 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) : (term225 A B R x l m R') = (term246 A B R x l m R').
Proof. exact (EQ_MP (@lem1185662 A B R x l m R') (@lem1185640 A B R x l m R')). Qed.
Lemma lem1185664 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term227 A B R l m R') = (term247 A B R l m R').
Proof. exact (fun_ext (fun x : A => @lem1185663 A B R x l m R')). Qed.
Lemma lem1185665 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1185666 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term228 A B R l m R') = (term248 A B R l m R').
Proof. exact (MK_COMB (@lem1185665 A) (@lem1185664 A B R l m R')). Qed.
Lemma lem1185667 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term208 A B R l m R') = (term248 A B R l m R').
Proof. exact (TRANS (@lem1185636 A B R l m R') (@lem1185666 A B R l m R')). Qed.
Lemma lem1185669 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term150 A B R l m R') = (term248 A B R l m R').
Proof. exact (TRANS (@lem1185609 A B R l m R') (@lem1185667 A B R l m R')). Qed.
Lemma lem1185670 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : (term91 A B R l m R') = (term248 A B R l m R').
Proof. exact (TRANS (@lem1185301 A B R l m R') (@lem1185669 A B R l m R')). Qed.
Lemma lem1185671 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term91 A B R l m R') : term248 A B R l m R'.
Proof. exact (EQ_MP (@lem1185670 A B R l m R') (@lem1185010 A B R l m R' h1)). Qed.
Lemma lem1185672 {A B : Type'} (R : type1413 A B) (x : A) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term246 A B R x l m R') : term246 A B R x l m R'.
Proof. exact (h1). Qed.
Lemma lem1185673 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term243 A B R x y l m R') : term243 A B R x y l m R'.
Proof. exact (h1). Qed.
Lemma lem1185722 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term101 A B P Q R R' p q) = (term101 A B P Q R R' p q).
Proof. exact (eq_refl (term101 A B P Q R R' p q)). Qed.
Lemma lem1185723 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term103 A B P Q R R' p) = (term103 A B P Q R R' p).
Proof. exact (fun_ext (fun q : B => @lem1185722 A B P Q R R' p q)). Qed.
Lemma lem1185724 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185725 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term104 A B P Q R R' p) = (term104 A B P Q R R' p).
Proof. exact (MK_COMB (@lem1185724 B) (@lem1185723 A B P Q R R' p)). Qed.
Lemma lem1185726 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term105 A B P Q R R') = (term105 A B P Q R R').
Proof. exact (fun_ext (fun p : A => @lem1185725 A B P Q R R' p)). Qed.
Lemma lem1185727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185728 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term106 A B P Q R R') = (term106 A B P Q R R').
Proof. exact (MK_COMB (@lem1185727 A) (@lem1185726 A B P Q R R')). Qed.
Lemma lem1185741 {B : Type'} (m : list B) (Q : B -> Prop) (x : B) : (term92 B m Q x) = (term92 B m Q x).
Proof. exact (eq_refl (term92 B m Q x)). Qed.
Lemma lem1185742 {B : Type'} (m : list B) (Q : B -> Prop) : (term93 B m Q) = (term93 B m Q).
Proof. exact (fun_ext (fun x : B => @lem1185741 B m Q x)). Qed.
Lemma lem1185743 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185744 {B : Type'} (m : list B) (Q : B -> Prop) : (term94 B m Q) = (term94 B m Q).
Proof. exact (MK_COMB (@lem1185743 B) (@lem1185742 B m Q)). Qed.
Lemma lem1185745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185746 {B : Type'} (m : list B) (Q : B -> Prop) : (term107 B m Q) = (term107 B m Q).
Proof. exact (MK_COMB (@lem1185745) (@lem1185744 B m Q)). Qed.
Lemma lem1185747 {A B : Type'} (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term108 A B m P Q R R') = (term108 A B m P Q R R').
Proof. exact (MK_COMB (@lem1185746 B m Q) (@lem1185728 A B P Q R R')). Qed.
Lemma lem1185760 {A : Type'} (l : list A) (P : A -> Prop) (x : A) : (term92 A l P x) = (term92 A l P x).
Proof. exact (eq_refl (term92 A l P x)). Qed.
Lemma lem1185761 {A : Type'} (l : list A) (P : A -> Prop) : (term93 A l P) = (term93 A l P).
Proof. exact (fun_ext (fun x : A => @lem1185760 A l P x)). Qed.
Lemma lem1185762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185763 {A : Type'} (l : list A) (P : A -> Prop) : (term94 A l P) = (term94 A l P).
Proof. exact (MK_COMB (@lem1185762 A) (@lem1185761 A l P)). Qed.
Lemma lem1185764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185765 {A : Type'} (l : list A) (P : A -> Prop) : (term107 A l P) = (term107 A l P).
Proof. exact (MK_COMB (@lem1185764) (@lem1185763 A l P)). Qed.
Lemma lem1185766 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term109 A B l m P Q R R') = (term109 A B l m P Q R R').
Proof. exact (MK_COMB (@lem1185765 A l P) (@lem1185747 A B m P Q R R')). Qed.
Lemma lem1185767 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term109 A B l m P Q R R'.
Proof. exact (EQ_MP (@lem1185766 A B l m P Q R R') (@lem1185190 A B l m P Q R R' h1)). Qed.
Lemma lem1185792 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term118 A B l m R' x y) = (term118 A B l m R' x y).
Proof. exact (eq_refl (term118 A B l m R' x y)). Qed.
Lemma lem1185793 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term128 A B l m R' x) = (term128 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1185792 A B l m R' x y)). Qed.
Lemma lem1185794 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185795 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term129 A B l m R' x) = (term129 A B l m R' x).
Proof. exact (MK_COMB (@lem1185794 B) (@lem1185793 A B l m R' x)). Qed.
Lemma lem1185796 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term137 A B l m R') = (term137 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1185795 A B l m R' x)). Qed.
Lemma lem1185797 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185798 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (MK_COMB (@lem1185797 A) (@lem1185796 A B l m R')). Qed.
Lemma lem1185823 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term200 A B l m R x y) = (term200 A B l m R x y).
Proof. exact (eq_refl (term200 A B l m R x y)). Qed.
Lemma lem1185824 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term202 A B R x y l m R') = (term202 A B R x y l m R').
Proof. exact (MK_COMB (@lem1185823 A B l m R x y) (@lem1185798 A B l m R')). Qed.
Lemma lem1185847 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term113 A B l m R' x y) = (term113 A B l m R' x y).
Proof. exact (eq_refl (term113 A B l m R' x y)). Qed.
Lemma lem1185872 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term118 A B l m R x y) = (term118 A B l m R x y).
Proof. exact (eq_refl (term118 A B l m R x y)). Qed.
Lemma lem1185873 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term128 A B l m R x) = (term128 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1185872 A B l m R x y)). Qed.
Lemma lem1185874 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185875 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term129 A B l m R x) = (term129 A B l m R x).
Proof. exact (MK_COMB (@lem1185874 B) (@lem1185873 A B l m R x)). Qed.
Lemma lem1185876 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term137 A B l m R) = (term137 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1185875 A B l m R x)). Qed.
Lemma lem1185877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185878 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term138 A B l m R) = (term138 A B l m R).
Proof. exact (MK_COMB (@lem1185877 A) (@lem1185876 A B l m R)). Qed.
Lemma lem1185879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1185880 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term144 A B l m R) = (term144 A B l m R).
Proof. exact (MK_COMB (@lem1185879) (@lem1185878 A B l m R)). Qed.
Lemma lem1185881 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term173 A B R l m R' x y) = (term173 A B R l m R' x y).
Proof. exact (MK_COMB (@lem1185880 A B l m R) (@lem1185847 A B l m R' x y)). Qed.
Lemma lem1185882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1185883 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term241 A B R l m R' x y) = (term241 A B R l m R' x y).
Proof. exact (MK_COMB (@lem1185882) (@lem1185881 A B R l m R' x y)). Qed.
Lemma lem1185884 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) : (term243 A B R x y l m R') = (term243 A B R x y l m R').
Proof. exact (MK_COMB (@lem1185883 A B R l m R' x y) (@lem1185824 A B R x y l m R')). Qed.
Lemma lem1185885 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term243 A B R x y l m R') : term243 A B R x y l m R'.
Proof. exact (EQ_MP (@lem1185884 A B R x y l m R') (@lem1185673 A B R x y l m R' h1)). Qed.
Lemma lem1185886 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term108 A B m P Q R R'.
Proof. exact (proj2 (@lem1185767 A B l m P Q R R' h1)). Qed.
Lemma lem1185887 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 A l P.
Proof. exact (proj1 (@lem1185767 A B l m P Q R R' h1)). Qed.
Lemma lem1185888 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term106 A B P Q R R'.
Proof. exact (proj2 (@lem1185886 A B l m P Q R R' h1)). Qed.
Lemma lem1185889 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 B m Q.
Proof. exact (proj1 (@lem1185886 A B l m P Q R R' h1)). Qed.
Lemma lem1185890 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term173 A B R l m R' x y.
Proof. exact (h1). Qed.
Lemma lem1185891 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term202 A B R x y l m R'.
Proof. exact (h1). Qed.
Lemma lem1185892 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term113 A B l m R' x y.
Proof. exact (proj2 (@lem1185890 A B R l m R' x y h1)). Qed.
Lemma lem1185893 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term138 A B l m R.
Proof. exact (proj1 (@lem1185890 A B R l m R' x y h1)). Qed.
Lemma lem1185895 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term114 A B x l y m.
Proof. exact (proj1 (@lem1185892 A B R l m R' x y h1)). Qed.
Lemma lem1185898 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term138 A B l m R'.
Proof. exact (proj2 (@lem1185891 A B R x y l m R' h1)). Qed.
Lemma lem1185899 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term113 A B l m R x y.
Proof. exact (proj1 (@lem1185891 A B R x y l m R' h1)). Qed.
Lemma lem1185901 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term114 A B x l y m.
Proof. exact (proj1 (@lem1185899 A B R x y l m R' h1)). Qed.
Lemma lem1185911 {A : Type'} (l : list A) (P : A -> Prop) (x : A) : (term92 A l P x) = (term92 A l P x).
Proof. exact (eq_refl (term92 A l P x)). Qed.
Lemma lem1185912 {A : Type'} (l : list A) (P : A -> Prop) : (term93 A l P) = (term93 A l P).
Proof. exact (fun_ext (fun x : A => @lem1185911 A l P x)). Qed.
Lemma lem1185913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185915 {A : Type'} (l : list A) (P : A -> Prop) : (term94 A l P) = (term94 A l P).
Proof. exact (MK_COMB (@lem1185913 A) (@lem1185912 A l P)). Qed.
Lemma lem1185916 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 A l P.
Proof. exact (EQ_MP (@lem1185915 A l P) (@lem1185887 A B l m P Q R R' h1)). Qed.
Lemma lem1185924 {B : Type'} (m : list B) (Q : B -> Prop) (x : B) : (term92 B m Q x) = (term92 B m Q x).
Proof. exact (eq_refl (term92 B m Q x)). Qed.
Lemma lem1185925 {B : Type'} (m : list B) (Q : B -> Prop) : (term93 B m Q) = (term93 B m Q).
Proof. exact (fun_ext (fun x : B => @lem1185924 B m Q x)). Qed.
Lemma lem1185926 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185928 {B : Type'} (m : list B) (Q : B -> Prop) : (term94 B m Q) = (term94 B m Q).
Proof. exact (MK_COMB (@lem1185926 B) (@lem1185925 B m Q)). Qed.
Lemma lem1185929 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 B m Q.
Proof. exact (EQ_MP (@lem1185928 B m Q) (@lem1185889 A B l m P Q R R' h1)). Qed.
Lemma lem1185965 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term101 A B P Q R R' p q) = (term249 A B P Q R R' p q).
Proof. exact (@lem19490 (term250 A B R R' p q) (term96 A B P p Q q) (term251 A B R R' p q)). Qed.
Lemma lem1185966 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term103 A B P Q R R' p) = (term252 A B P Q R R' p).
Proof. exact (fun_ext (fun q : B => @lem1185965 A B P Q R R' p q)). Qed.
Lemma lem1185967 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185968 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term104 A B P Q R R' p) = (term253 A B P Q R R' p).
Proof. exact (MK_COMB (@lem1185967 B) (@lem1185966 A B P Q R R' p)). Qed.
Lemma lem1185969 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term105 A B P Q R R') = (term254 A B P Q R R').
Proof. exact (fun_ext (fun p : A => @lem1185968 A B P Q R R' p)). Qed.
Lemma lem1185970 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185972 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term106 A B P Q R R') = (term255 A B P Q R R').
Proof. exact (MK_COMB (@lem1185970 A) (@lem1185969 A B P Q R R')). Qed.
Lemma lem1185973 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term255 A B P Q R R'.
Proof. exact (EQ_MP (@lem1185972 A B P Q R R') (@lem1185888 A B l m P Q R R' h1)). Qed.
Lemma lem1185987 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) (y : B) : (term118 A B l m R x y) = (term118 A B l m R x y).
Proof. exact (eq_refl (term118 A B l m R x y)). Qed.
Lemma lem1185988 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term128 A B l m R x) = (term128 A B l m R x).
Proof. exact (fun_ext (fun y : B => @lem1185987 A B l m R x y)). Qed.
Lemma lem1185989 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1185990 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (x : A) : (term129 A B l m R x) = (term129 A B l m R x).
Proof. exact (MK_COMB (@lem1185989 B) (@lem1185988 A B l m R x)). Qed.
Lemma lem1185991 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term137 A B l m R) = (term137 A B l m R).
Proof. exact (fun_ext (fun x : A => @lem1185990 A B l m R x)). Qed.
Lemma lem1185992 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1185994 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) : (term138 A B l m R) = (term138 A B l m R).
Proof. exact (MK_COMB (@lem1185992 A) (@lem1185991 A B l m R)). Qed.
Lemma lem1185995 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term138 A B l m R.
Proof. exact (EQ_MP (@lem1185994 A B l m R) (@lem1185893 A B R l m R' x y h1)). Qed.
Lemma lem1186015 {A : Type'} (l : list A) (P : A -> Prop) (x : A) : (term92 A l P x) = (term92 A l P x).
Proof. exact (eq_refl (term92 A l P x)). Qed.
Lemma lem1186016 {A : Type'} (l : list A) (P : A -> Prop) : (term93 A l P) = (term93 A l P).
Proof. exact (fun_ext (fun x : A => @lem1186015 A l P x)). Qed.
Lemma lem1186017 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1186019 {A : Type'} (l : list A) (P : A -> Prop) : (term94 A l P) = (term94 A l P).
Proof. exact (MK_COMB (@lem1186017 A) (@lem1186016 A l P)). Qed.
Lemma lem1186020 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 A l P.
Proof. exact (EQ_MP (@lem1186019 A l P) (@lem1185887 A B l m P Q R R' h1)). Qed.
Lemma lem1186028 {B : Type'} (m : list B) (Q : B -> Prop) (x : B) : (term92 B m Q x) = (term92 B m Q x).
Proof. exact (eq_refl (term92 B m Q x)). Qed.
Lemma lem1186029 {B : Type'} (m : list B) (Q : B -> Prop) : (term93 B m Q) = (term93 B m Q).
Proof. exact (fun_ext (fun x : B => @lem1186028 B m Q x)). Qed.
Lemma lem1186030 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1186032 {B : Type'} (m : list B) (Q : B -> Prop) : (term94 B m Q) = (term94 B m Q).
Proof. exact (MK_COMB (@lem1186030 B) (@lem1186029 B m Q)). Qed.
Lemma lem1186033 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term94 B m Q.
Proof. exact (EQ_MP (@lem1186032 B m Q) (@lem1185889 A B l m P Q R R' h1)). Qed.
Lemma lem1186069 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) (q : B) : (term101 A B P Q R R' p q) = (term249 A B P Q R R' p q).
Proof. exact (@lem19490 (term250 A B R R' p q) (term96 A B P p Q q) (term251 A B R R' p q)). Qed.
Lemma lem1186070 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term103 A B P Q R R' p) = (term252 A B P Q R R' p).
Proof. exact (fun_ext (fun q : B => @lem1186069 A B P Q R R' p q)). Qed.
Lemma lem1186071 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1186072 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (p : A) : (term104 A B P Q R R' p) = (term253 A B P Q R R' p).
Proof. exact (MK_COMB (@lem1186071 B) (@lem1186070 A B P Q R R' p)). Qed.
Lemma lem1186073 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term105 A B P Q R R') = (term254 A B P Q R R').
Proof. exact (fun_ext (fun p : A => @lem1186072 A B P Q R R' p)). Qed.
Lemma lem1186074 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1186076 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) : (term106 A B P Q R R') = (term255 A B P Q R R').
Proof. exact (MK_COMB (@lem1186074 A) (@lem1186073 A B P Q R R')). Qed.
Lemma lem1186077 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term255 A B P Q R R'.
Proof. exact (EQ_MP (@lem1186076 A B P Q R R') (@lem1185888 A B l m P Q R R' h1)). Qed.
Lemma lem1186091 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) : (term118 A B l m R' x y) = (term118 A B l m R' x y).
Proof. exact (eq_refl (term118 A B l m R' x y)). Qed.
Lemma lem1186092 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term128 A B l m R' x) = (term128 A B l m R' x).
Proof. exact (fun_ext (fun y : B => @lem1186091 A B l m R' x y)). Qed.
Lemma lem1186093 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1186094 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (x : A) : (term129 A B l m R' x) = (term129 A B l m R' x).
Proof. exact (MK_COMB (@lem1186093 B) (@lem1186092 A B l m R' x)). Qed.
Lemma lem1186095 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term137 A B l m R') = (term137 A B l m R').
Proof. exact (fun_ext (fun x : A => @lem1186094 A B l m R' x)). Qed.
Lemma lem1186096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1186098 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) : (term138 A B l m R') = (term138 A B l m R').
Proof. exact (MK_COMB (@lem1186096 A) (@lem1186095 A B l m R')). Qed.
Lemma lem1186099 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term138 A B l m R'.
Proof. exact (EQ_MP (@lem1186098 A B l m R') (@lem1185898 A B R x y l m R' h1)). Qed.
Lemma lem1186112 {A B : Type'} (_21204 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term256 A l P _21204.
Proof. exact (@lem1185916 A B l m P Q R R' h1 _21204). Qed.
Lemma lem1186113 {A : Type'} (l : list A) (P : A -> Prop) (_21204 : A) : (term256 A l P _21204) = (term92 A l P _21204).
Proof. exact (eq_refl (term256 A l P _21204)). Qed.
Lemma lem1186115 {A B : Type'} (_21205 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term256 B m Q _21205.
Proof. exact (@lem1185929 A B l m P Q R R' h1 _21205). Qed.
Lemma lem1186116 {B : Type'} (m : list B) (Q : B -> Prop) (_21205 : B) : (term256 B m Q _21205) = (term92 B m Q _21205).
Proof. exact (eq_refl (term256 B m Q _21205)). Qed.
Lemma lem1186118 {A B : Type'} (_21206 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term257 A B P Q R R' _21206.
Proof. exact (@lem1185973 A B l m P Q R R' h1 _21206). Qed.
Lemma lem1186119 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) : (term257 A B P Q R R' _21206) = (term253 A B P Q R R' _21206).
Proof. exact (eq_refl (term257 A B P Q R R' _21206)). Qed.
Lemma lem1186120 {A B : Type'} (_21206 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term253 A B P Q R R' _21206.
Proof. exact (EQ_MP (@lem1186119 A B P Q R R' _21206) (@lem1186118 A B _21206 l m P Q R R' h1)). Qed.
Lemma lem1186121 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term258 A B P Q R R' _21206 _21207.
Proof. exact (@lem1186120 A B _21206 l m P Q R R' h1 _21207). Qed.
Lemma lem1186122 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) (_21207 : B) : (term258 A B P Q R R' _21206 _21207) = (term249 A B P Q R R' _21206 _21207).
Proof. exact (eq_refl (term258 A B P Q R R' _21206 _21207)). Qed.
Lemma lem1186123 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term249 A B P Q R R' _21206 _21207.
Proof. exact (EQ_MP (@lem1186122 A B P Q R R' _21206 _21207) (@lem1186121 A B _21206 _21207 l m P Q R R' h1)). Qed.
Lemma lem1186124 {A B : Type'} (_21208 : A) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term259 A B l m R _21208.
Proof. exact (@lem1185995 A B R l m R' x y h1 _21208). Qed.
Lemma lem1186125 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) : (term259 A B l m R _21208) = (term129 A B l m R _21208).
Proof. exact (eq_refl (term259 A B l m R _21208)). Qed.
Lemma lem1186126 {A B : Type'} (_21208 : A) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term129 A B l m R _21208.
Proof. exact (EQ_MP (@lem1186125 A B l m R _21208) (@lem1186124 A B _21208 R l m R' x y h1)). Qed.
Lemma lem1186127 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term260 A B l m R _21208 _21209.
Proof. exact (@lem1186126 A B _21208 R l m R' x y h1 _21209). Qed.
Lemma lem1186128 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) (_21209 : B) : (term260 A B l m R _21208 _21209) = (term118 A B l m R _21208 _21209).
Proof. exact (eq_refl (term260 A B l m R _21208 _21209)). Qed.
Lemma lem1186129 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term118 A B l m R _21208 _21209.
Proof. exact (EQ_MP (@lem1186128 A B l m R _21208 _21209) (@lem1186127 A B _21208 _21209 R l m R' x y h1)). Qed.
Lemma lem1186130 {A B : Type'} (_21210 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term256 A l P _21210.
Proof. exact (@lem1186020 A B l m P Q R R' h1 _21210). Qed.
Lemma lem1186131 {A : Type'} (l : list A) (P : A -> Prop) (_21210 : A) : (term256 A l P _21210) = (term92 A l P _21210).
Proof. exact (eq_refl (term256 A l P _21210)). Qed.
Lemma lem1186133 {A B : Type'} (_21211 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term256 B m Q _21211.
Proof. exact (@lem1186033 A B l m P Q R R' h1 _21211). Qed.
Lemma lem1186134 {B : Type'} (m : list B) (Q : B -> Prop) (_21211 : B) : (term256 B m Q _21211) = (term92 B m Q _21211).
Proof. exact (eq_refl (term256 B m Q _21211)). Qed.
Lemma lem1186136 {A B : Type'} (_21212 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term257 A B P Q R R' _21212.
Proof. exact (@lem1186077 A B l m P Q R R' h1 _21212). Qed.
Lemma lem1186137 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21212 : A) : (term257 A B P Q R R' _21212) = (term253 A B P Q R R' _21212).
Proof. exact (eq_refl (term257 A B P Q R R' _21212)). Qed.
Lemma lem1186138 {A B : Type'} (_21212 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term253 A B P Q R R' _21212.
Proof. exact (EQ_MP (@lem1186137 A B P Q R R' _21212) (@lem1186136 A B _21212 l m P Q R R' h1)). Qed.
Lemma lem1186139 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term258 A B P Q R R' _21212 _21213.
Proof. exact (@lem1186138 A B _21212 l m P Q R R' h1 _21213). Qed.
Lemma lem1186140 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term258 A B P Q R R' _21212 _21213) = (term249 A B P Q R R' _21212 _21213).
Proof. exact (eq_refl (term258 A B P Q R R' _21212 _21213)). Qed.
Lemma lem1186141 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term249 A B P Q R R' _21212 _21213.
Proof. exact (EQ_MP (@lem1186140 A B P Q R R' _21212 _21213) (@lem1186139 A B _21212 _21213 l m P Q R R' h1)). Qed.
Lemma lem1186142 {A B : Type'} (_21214 : A) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term259 A B l m R' _21214.
Proof. exact (@lem1186099 A B R x y l m R' h1 _21214). Qed.
Lemma lem1186143 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) : (term259 A B l m R' _21214) = (term129 A B l m R' _21214).
Proof. exact (eq_refl (term259 A B l m R' _21214)). Qed.
Lemma lem1186144 {A B : Type'} (_21214 : A) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term129 A B l m R' _21214.
Proof. exact (EQ_MP (@lem1186143 A B l m R' _21214) (@lem1186142 A B _21214 R x y l m R' h1)). Qed.
Lemma lem1186145 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term260 A B l m R' _21214 _21215.
Proof. exact (@lem1186144 A B _21214 R x y l m R' h1 _21215). Qed.
Lemma lem1186146 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) (_21215 : B) : (term260 A B l m R' _21214 _21215) = (term118 A B l m R' _21214 _21215).
Proof. exact (eq_refl (term260 A B l m R' _21214 _21215)). Qed.
Lemma lem1186147 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term118 A B l m R' _21214 _21215.
Proof. exact (EQ_MP (@lem1186146 A B l m R' _21214 _21215) (@lem1186145 A B _21214 _21215 R x y l m R' h1)). Qed.
Lemma lem1186148 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term261 A B P Q R R' _21206 _21207.
Proof. exact (proj2 (@lem1186123 A B _21206 _21207 l m P Q R R' h1)). Qed.
Lemma lem1186151 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term262 A B P Q R R' _21212 _21213.
Proof. exact (proj1 (@lem1186141 A B _21212 _21213 l m P Q R R' h1)). Qed.
Lemma lem1186157 {A B : Type'} (_21204 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term92 A l P _21204.
Proof. exact (EQ_MP (@lem1186113 A l P _21204) (@lem1186112 A B _21204 l m P Q R R' h1)). Qed.
Lemma lem1186163 {A B : Type'} (_21205 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term92 B m Q _21205.
Proof. exact (EQ_MP (@lem1186116 B m Q _21205) (@lem1186115 A B _21205 l m P Q R R' h1)). Qed.
Lemma lem1186174 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) (_21209 : B) : (term118 A B l m R _21208 _21209) = (term263 A B l m R _21208 _21209).
Proof. exact (@lem1184489 (term264 A _21208 l) (term264 B _21209 m) (R _21208 _21209)). Qed.
Lemma lem1186175 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term263 A B l m R _21208 _21209.
Proof. exact (EQ_MP (@lem1186174 A B l m R _21208 _21209) (@lem1186129 A B _21208 _21209 R l m R' x y h1)). Qed.
Lemma lem1186177 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term265 A B R' x y.
Proof. exact (proj2 (@lem1185892 A B R l m R' x y h1)). Qed.
Lemma lem1186212 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) (_21207 : B) : (term261 A B P Q R R' _21206 _21207) = (term266 A B P Q R R' _21206 _21207).
Proof. exact (@lem1184489 (term267 A P _21206) (term267 B Q _21207) (term251 A B R R' _21206 _21207)). Qed.
Lemma lem1186213 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term266 A B P Q R R' _21206 _21207.
Proof. exact (EQ_MP (@lem1186212 A B P Q R R' _21206 _21207) (@lem1186148 A B _21206 _21207 l m P Q R R' h1)). Qed.
Lemma lem1186219 {A B : Type'} (_21210 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term92 A l P _21210.
Proof. exact (EQ_MP (@lem1186131 A l P _21210) (@lem1186130 A B _21210 l m P Q R R' h1)). Qed.
Lemma lem1186225 {A B : Type'} (_21211 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term92 B m Q _21211.
Proof. exact (EQ_MP (@lem1186134 B m Q _21211) (@lem1186133 A B _21211 l m P Q R R' h1)). Qed.
Lemma lem1186236 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) (_21215 : B) : (term118 A B l m R' _21214 _21215) = (term263 A B l m R' _21214 _21215).
Proof. exact (@lem1184489 (term264 A _21214 l) (term264 B _21215 m) (R' _21214 _21215)). Qed.
Lemma lem1186237 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term263 A B l m R' _21214 _21215.
Proof. exact (EQ_MP (@lem1186236 A B l m R' _21214 _21215) (@lem1186147 A B _21214 _21215 R x y l m R' h1)). Qed.
Lemma lem1186239 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term265 A B R x y.
Proof. exact (proj2 (@lem1185899 A B R x y l m R' h1)). Qed.
Lemma lem1186258 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term262 A B P Q R R' _21212 _21213) = (term268 A B P Q R R' _21212 _21213).
Proof. exact (@lem1184489 (term267 A P _21212) (term267 B Q _21213) (term250 A B R R' _21212 _21213)). Qed.
Lemma lem1186259 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term268 A B P Q R R' _21212 _21213.
Proof. exact (EQ_MP (@lem1186258 A B P Q R R' _21212 _21213) (@lem1186151 A B _21212 _21213 l m P Q R R' h1)). Qed.
Lemma lem1186277 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In A x l.
Proof. exact (proj1 (@lem1185895 A B R l m R' x y h1)). Qed.
Lemma lem1186278 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term269 A x l.
Proof. exact (fun h0 : term264 A x l => @lem1186277 A B R l m R' x y h1). Qed.
Lemma lem1186280 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186281 {A : Type'} (x : A) (l : list A) : (term269 A x l) = (@List.In A x l).
Proof. exact (@lem1186280 (@List.In A x l)). Qed.
Lemma lem1186282 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In A x l.
Proof. exact (EQ_MP (@lem1186281 A x l) (@lem1186278 A B R l m R' x y h1)). Qed.
Lemma lem1186288 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186289 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : (term92 A l P _21204) = (term271 A P _21204 l).
Proof. exact (@lem1186288 (P _21204) (term264 A _21204 l)). Qed.
Lemma lem1186295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186296 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : (term272 A l P _21204) = (term273 A P _21204 l).
Proof. exact (MK_COMB (@lem1186295) (@lem1186289 A P _21204 l)). Qed.
Lemma lem1186302 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : (term271 A P _21204 l) = (term271 A P _21204 l).
Proof. exact (eq_refl (term271 A P _21204 l)). Qed.
Lemma lem1186303 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : ((term92 A l P _21204) = (term271 A P _21204 l)) = ((term271 A P _21204 l) = (term271 A P _21204 l)).
Proof. exact (MK_COMB (@lem1186296 A P _21204 l) (@lem1186302 A P _21204 l)). Qed.
Lemma lem1186305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186306 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186305 Prop x). Qed.
Lemma lem1186307 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : ((term271 A P _21204 l) = (term271 A P _21204 l)) = True.
Proof. exact (@lem1186306 (term271 A P _21204 l)). Qed.
Lemma lem1186308 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : ((term92 A l P _21204) = (term271 A P _21204 l)) = True.
Proof. exact (TRANS (@lem1186303 A P _21204 l) (@lem1186307 A P _21204 l)). Qed.
Lemma lem1186309 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : True = ((term92 A l P _21204) = (term271 A P _21204 l)).
Proof. exact (SYM (@lem1186308 A P _21204 l)). Qed.
Lemma lem1186310 {A : Type'} (P : A -> Prop) (_21204 : A) (l : list A) : (term92 A l P _21204) = (term271 A P _21204 l).
Proof. exact (EQ_MP (@lem1186309 A P _21204 l) (@lem0)). Qed.
Lemma lem1186311 {A B : Type'} (_21204 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term271 A P _21204 l.
Proof. exact (EQ_MP (@lem1186310 A P _21204 l) (@lem1186157 A B _21204 l m P Q R R' h1)). Qed.
Lemma lem1186313 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186314 {A : Type'} (l : list A) (P : A -> Prop) (_21204 : A) : (term271 A P _21204 l) = (term275 A l P _21204).
Proof. exact (@lem1186313 (term264 A _21204 l) (P _21204)). Qed.
Lemma lem1186316 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186317 {A : Type'} (_21204 : A) (l : list A) : (term276 A _21204 l) = (@List.In A _21204 l).
Proof. exact (@lem1186316 (@List.In A _21204 l)). Qed.
Lemma lem1186318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186319 {A : Type'} (_21204 : A) (l : list A) : (term277 A _21204 l) = (term278 A _21204 l).
Proof. exact (MK_COMB (@lem1186318) (@lem1186317 A _21204 l)). Qed.
Lemma lem1186320 {A : Type'} (P : A -> Prop) (_21204 : A) : (P _21204) = (P _21204).
Proof. exact (eq_refl (P _21204)). Qed.
Lemma lem1186321 {A : Type'} (l : list A) (P : A -> Prop) (_21204 : A) : (term275 A l P _21204) = (term88 A l P _21204).
Proof. exact (MK_COMB (@lem1186319 A _21204 l) (@lem1186320 A P _21204)). Qed.
Lemma lem1186322 {A : Type'} (l : list A) (P : A -> Prop) (_21204 : A) : (term271 A P _21204 l) = (term88 A l P _21204).
Proof. exact (TRANS (@lem1186314 A l P _21204) (@lem1186321 A l P _21204)). Qed.
Lemma lem1186325 {A B : Type'} (_21204 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P _21204.
Proof. exact (EQ_MP (@lem1186322 A l P _21204) (@lem1186311 A B _21204 l m P Q R R' h1)). Qed.
Lemma lem1186326 {A B : Type'} (_21204 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P _21204.
Proof. exact (@lem1186325 A B _21204 l m P Q R R' h1). Qed.
Lemma lem1186327 {A B : Type'} (x : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P x.
Proof. exact (@lem1186326 A B x l m P Q R R' h1). Qed.
Lemma lem1186330 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : P x.
Proof. exact (@lem1186327 A B x l m P Q R R' h2 (@lem1186282 A B R l m R' x y h1)). Qed.
Lemma lem1186331 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term279 A P x.
Proof. exact (fun h0 : term267 A P x => @lem1186330 A B x y l m P Q R R' h1 h2). Qed.
Lemma lem1186333 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186334 {A : Type'} (P : A -> Prop) (x : A) : (term279 A P x) = (P x).
Proof. exact (@lem1186333 (P x)). Qed.
Lemma lem1186335 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : P x.
Proof. exact (EQ_MP (@lem1186334 A P x) (@lem1186331 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186337 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In B y m.
Proof. exact (proj2 (@lem1185895 A B R l m R' x y h1)). Qed.
Lemma lem1186338 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term269 B y m.
Proof. exact (fun h0 : term264 B y m => @lem1186337 A B R l m R' x y h1). Qed.
Lemma lem1186340 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186341 {B : Type'} (y : B) (m : list B) : (term269 B y m) = (@List.In B y m).
Proof. exact (@lem1186340 (@List.In B y m)). Qed.
Lemma lem1186342 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In B y m.
Proof. exact (EQ_MP (@lem1186341 B y m) (@lem1186338 A B R l m R' x y h1)). Qed.
Lemma lem1186348 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186349 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : (term92 B m Q _21205) = (term271 B Q _21205 m).
Proof. exact (@lem1186348 (Q _21205) (term264 B _21205 m)). Qed.
Lemma lem1186355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186356 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : (term272 B m Q _21205) = (term273 B Q _21205 m).
Proof. exact (MK_COMB (@lem1186355) (@lem1186349 B Q _21205 m)). Qed.
Lemma lem1186362 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : (term271 B Q _21205 m) = (term271 B Q _21205 m).
Proof. exact (eq_refl (term271 B Q _21205 m)). Qed.
Lemma lem1186363 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : ((term92 B m Q _21205) = (term271 B Q _21205 m)) = ((term271 B Q _21205 m) = (term271 B Q _21205 m)).
Proof. exact (MK_COMB (@lem1186356 B Q _21205 m) (@lem1186362 B Q _21205 m)). Qed.
Lemma lem1186365 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186366 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186365 Prop x). Qed.
Lemma lem1186367 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : ((term271 B Q _21205 m) = (term271 B Q _21205 m)) = True.
Proof. exact (@lem1186366 (term271 B Q _21205 m)). Qed.
Lemma lem1186368 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : ((term92 B m Q _21205) = (term271 B Q _21205 m)) = True.
Proof. exact (TRANS (@lem1186363 B Q _21205 m) (@lem1186367 B Q _21205 m)). Qed.
Lemma lem1186369 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : True = ((term92 B m Q _21205) = (term271 B Q _21205 m)).
Proof. exact (SYM (@lem1186368 B Q _21205 m)). Qed.
Lemma lem1186370 {B : Type'} (Q : B -> Prop) (_21205 : B) (m : list B) : (term92 B m Q _21205) = (term271 B Q _21205 m).
Proof. exact (EQ_MP (@lem1186369 B Q _21205 m) (@lem0)). Qed.
Lemma lem1186371 {A B : Type'} (_21205 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term271 B Q _21205 m.
Proof. exact (EQ_MP (@lem1186370 B Q _21205 m) (@lem1186163 A B _21205 l m P Q R R' h1)). Qed.
Lemma lem1186373 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186374 {B : Type'} (m : list B) (Q : B -> Prop) (_21205 : B) : (term271 B Q _21205 m) = (term275 B m Q _21205).
Proof. exact (@lem1186373 (term264 B _21205 m) (Q _21205)). Qed.
Lemma lem1186376 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186377 {B : Type'} (_21205 : B) (m : list B) : (term276 B _21205 m) = (@List.In B _21205 m).
Proof. exact (@lem1186376 (@List.In B _21205 m)). Qed.
Lemma lem1186378 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186379 {B : Type'} (_21205 : B) (m : list B) : (term277 B _21205 m) = (term278 B _21205 m).
Proof. exact (MK_COMB (@lem1186378) (@lem1186377 B _21205 m)). Qed.
Lemma lem1186380 {B : Type'} (Q : B -> Prop) (_21205 : B) : (Q _21205) = (Q _21205).
Proof. exact (eq_refl (Q _21205)). Qed.
Lemma lem1186381 {B : Type'} (m : list B) (Q : B -> Prop) (_21205 : B) : (term275 B m Q _21205) = (term88 B m Q _21205).
Proof. exact (MK_COMB (@lem1186379 B _21205 m) (@lem1186380 B Q _21205)). Qed.
Lemma lem1186382 {B : Type'} (m : list B) (Q : B -> Prop) (_21205 : B) : (term271 B Q _21205 m) = (term88 B m Q _21205).
Proof. exact (TRANS (@lem1186374 B m Q _21205) (@lem1186381 B m Q _21205)). Qed.
Lemma lem1186385 {A B : Type'} (_21205 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q _21205.
Proof. exact (EQ_MP (@lem1186382 B m Q _21205) (@lem1186371 A B _21205 l m P Q R R' h1)). Qed.
Lemma lem1186386 {A B : Type'} (_21205 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q _21205.
Proof. exact (@lem1186385 A B _21205 l m P Q R R' h1). Qed.
Lemma lem1186387 {A B : Type'} (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q y.
Proof. exact (@lem1186386 A B y l m P Q R R' h1). Qed.
Lemma lem1186390 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : Q y.
Proof. exact (@lem1186387 A B y l m P Q R R' h2 (@lem1186342 A B R l m R' x y h1)). Qed.
Lemma lem1186391 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term279 B Q y.
Proof. exact (fun h0 : term267 B Q y => @lem1186390 A B x y l m P Q R R' h1 h2). Qed.
Lemma lem1186393 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186394 {B : Type'} (Q : B -> Prop) (y : B) : (term279 B Q y) = (Q y).
Proof. exact (@lem1186393 (Q y)). Qed.
Lemma lem1186395 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : Q y.
Proof. exact (EQ_MP (@lem1186394 B Q y) (@lem1186391 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186397 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In A x l.
Proof. exact (proj1 (@lem1185895 A B R l m R' x y h1)). Qed.
Lemma lem1186398 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term269 A x l.
Proof. exact (fun h0 : term264 A x l => @lem1186397 A B R l m R' x y h1). Qed.
Lemma lem1186400 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186401 {A : Type'} (x : A) (l : list A) : (term269 A x l) = (@List.In A x l).
Proof. exact (@lem1186400 (@List.In A x l)). Qed.
Lemma lem1186402 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In A x l.
Proof. exact (EQ_MP (@lem1186401 A x l) (@lem1186398 A B R l m R' x y h1)). Qed.
Lemma lem1186404 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In B y m.
Proof. exact (proj2 (@lem1185895 A B R l m R' x y h1)). Qed.
Lemma lem1186405 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term269 B y m.
Proof. exact (fun h0 : term264 B y m => @lem1186404 A B R l m R' x y h1). Qed.
Lemma lem1186407 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186408 {B : Type'} (y : B) (m : list B) : (term269 B y m) = (@List.In B y m).
Proof. exact (@lem1186407 (@List.In B y m)). Qed.
Lemma lem1186409 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : @List.In B y m.
Proof. exact (EQ_MP (@lem1186408 B y m) (@lem1186405 A B R l m R' x y h1)). Qed.
Lemma lem1186425 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186426 {A B : Type'} (R : type1413 A B) (_21208 : A) (_21209 : B) (m : list B) : (term280 A B m R _21208 _21209) = (term281 A B R _21208 _21209 m).
Proof. exact (@lem1186425 (R _21208 _21209) (term264 B _21209 m)). Qed.
Lemma lem1186432 {A : Type'} (_21208 : A) (l : list A) : (term282 A _21208 l) = (term282 A _21208 l).
Proof. exact (eq_refl (term282 A _21208 l)). Qed.
Lemma lem1186433 {A B : Type'} (l : list A) (R : type1413 A B) (_21208 : A) (_21209 : B) (m : list B) : (term263 A B l m R _21208 _21209) = (term283 A B l R _21208 _21209 m).
Proof. exact (MK_COMB (@lem1186432 A _21208 l) (@lem1186426 A B R _21208 _21209 m)). Qed.
Lemma lem1186437 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186438 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term283 A B l R _21208 _21209 m) = (term284 A B R _21208 l _21209 m).
Proof. exact (@lem1186437 (R _21208 _21209) (term264 A _21208 l) (term264 B _21209 m)). Qed.
Lemma lem1186454 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term263 A B l m R _21208 _21209) = (term284 A B R _21208 l _21209 m).
Proof. exact (TRANS (@lem1186433 A B l R _21208 _21209 m) (@lem1186438 A B R _21208 l _21209 m)). Qed.
Lemma lem1186455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186456 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term285 A B l m R _21208 _21209) = (term286 A B R _21208 l _21209 m).
Proof. exact (MK_COMB (@lem1186455) (@lem1186454 A B R _21208 l _21209 m)). Qed.
Lemma lem1186472 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term284 A B R _21208 l _21209 m) = (term284 A B R _21208 l _21209 m).
Proof. exact (eq_refl (term284 A B R _21208 l _21209 m)). Qed.
Lemma lem1186473 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : ((term263 A B l m R _21208 _21209) = (term284 A B R _21208 l _21209 m)) = ((term284 A B R _21208 l _21209 m) = (term284 A B R _21208 l _21209 m)).
Proof. exact (MK_COMB (@lem1186456 A B R _21208 l _21209 m) (@lem1186472 A B R _21208 l _21209 m)). Qed.
Lemma lem1186475 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186476 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186475 Prop x). Qed.
Lemma lem1186477 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : ((term284 A B R _21208 l _21209 m) = (term284 A B R _21208 l _21209 m)) = True.
Proof. exact (@lem1186476 (term284 A B R _21208 l _21209 m)). Qed.
Lemma lem1186478 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : ((term263 A B l m R _21208 _21209) = (term284 A B R _21208 l _21209 m)) = True.
Proof. exact (TRANS (@lem1186473 A B R _21208 l _21209 m) (@lem1186477 A B R _21208 l _21209 m)). Qed.
Lemma lem1186479 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : True = ((term263 A B l m R _21208 _21209) = (term284 A B R _21208 l _21209 m)).
Proof. exact (SYM (@lem1186478 A B R _21208 l _21209 m)). Qed.
Lemma lem1186480 {A B : Type'} (R : type1413 A B) (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term263 A B l m R _21208 _21209) = (term284 A B R _21208 l _21209 m).
Proof. exact (EQ_MP (@lem1186479 A B R _21208 l _21209 m) (@lem0)). Qed.
Lemma lem1186481 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term284 A B R _21208 l _21209 m.
Proof. exact (EQ_MP (@lem1186480 A B R _21208 l _21209 m) (@lem1186175 A B _21208 _21209 R l m R' x y h1)). Qed.
Lemma lem1186483 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186484 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) (_21209 : B) : (term284 A B R _21208 l _21209 m) = (term287 A B l m R _21208 _21209).
Proof. exact (@lem1186483 (term111 A B _21208 l _21209 m) (R _21208 _21209)). Qed.
Lemma lem1186486 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1186487 {A B : Type'} (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term290 A B _21208 l _21209 m) = (term291 A B _21208 l _21209 m).
Proof. exact (@lem1186486 (term264 A _21208 l) (term264 B _21209 m)). Qed.
Lemma lem1186489 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186490 {A : Type'} (_21208 : A) (l : list A) : (term276 A _21208 l) = (@List.In A _21208 l).
Proof. exact (@lem1186489 (@List.In A _21208 l)). Qed.
Lemma lem1186491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1186492 {A : Type'} (_21208 : A) (l : list A) : (term292 A _21208 l) = (term293 A _21208 l).
Proof. exact (MK_COMB (@lem1186491) (@lem1186490 A _21208 l)). Qed.
Lemma lem1186494 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186495 {B : Type'} (_21209 : B) (m : list B) : (term276 B _21209 m) = (@List.In B _21209 m).
Proof. exact (@lem1186494 (@List.In B _21209 m)). Qed.
Lemma lem1186496 {A B : Type'} (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term291 A B _21208 l _21209 m) = (term114 A B _21208 l _21209 m).
Proof. exact (MK_COMB (@lem1186492 A _21208 l) (@lem1186495 B _21209 m)). Qed.
Lemma lem1186497 {A B : Type'} (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term290 A B _21208 l _21209 m) = (term114 A B _21208 l _21209 m).
Proof. exact (TRANS (@lem1186487 A B _21208 l _21209 m) (@lem1186496 A B _21208 l _21209 m)). Qed.
Lemma lem1186498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186499 {A B : Type'} (_21208 : A) (l : list A) (_21209 : B) (m : list B) : (term294 A B _21208 l _21209 m) = (term295 A B _21208 l _21209 m).
Proof. exact (MK_COMB (@lem1186498) (@lem1186497 A B _21208 l _21209 m)). Qed.
Lemma lem1186500 {A B : Type'} (R : type1413 A B) (_21208 : A) (_21209 : B) : (R _21208 _21209) = (R _21208 _21209).
Proof. exact (eq_refl (R _21208 _21209)). Qed.
Lemma lem1186501 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) (_21209 : B) : (term287 A B l m R _21208 _21209) = (term80 A B l m R _21208 _21209).
Proof. exact (MK_COMB (@lem1186499 A B _21208 l _21209 m) (@lem1186500 A B R _21208 _21209)). Qed.
Lemma lem1186502 {A B : Type'} (l : list A) (m : list B) (R : type1413 A B) (_21208 : A) (_21209 : B) : (term284 A B R _21208 l _21209 m) = (term80 A B l m R _21208 _21209).
Proof. exact (TRANS (@lem1186484 A B l m R _21208 _21209) (@lem1186501 A B l m R _21208 _21209)). Qed.
Lemma lem1186504 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term114 A B x l y m.
Proof. exact (conj (@lem1186402 A B R l m R' x y h1) (@lem1186409 A B R l m R' x y h1)). Qed.
Lemma lem1186506 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term80 A B l m R _21208 _21209.
Proof. exact (EQ_MP (@lem1186502 A B l m R _21208 _21209) (@lem1186481 A B _21208 _21209 R l m R' x y h1)). Qed.
Lemma lem1186507 {A B : Type'} (_21208 : A) (_21209 : B) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term80 A B l m R _21208 _21209.
Proof. exact (@lem1186506 A B _21208 _21209 R l m R' x y h1). Qed.
Lemma lem1186508 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term80 A B l m R x y.
Proof. exact (@lem1186507 A B x y R l m R' x y h1). Qed.
Lemma lem1186511 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : R x y.
Proof. exact (@lem1186508 A B R l m R' x y h1 (@lem1186504 A B R l m R' x y h1)). Qed.
Lemma lem1186512 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term296 A B R x y.
Proof. exact (fun h0 : term265 A B R x y => @lem1186511 A B R l m R' x y h1). Qed.
Lemma lem1186514 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186515 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term296 A B R x y) = (R x y).
Proof. exact (@lem1186514 (R x y)). Qed.
Lemma lem1186516 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : R x y.
Proof. exact (EQ_MP (@lem1186515 A B R x y) (@lem1186512 A B R l m R' x y h1)). Qed.
Lemma lem1186542 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186543 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term251 A B R R' _21206 _21207) = (term250 A B R' R _21206 _21207).
Proof. exact (@lem1186542 (R' _21206 _21207) (term265 A B R _21206 _21207)). Qed.
Lemma lem1186549 {B : Type'} (Q : B -> Prop) (_21207 : B) : (term297 B Q _21207) = (term297 B Q _21207).
Proof. exact (eq_refl (term297 B Q _21207)). Qed.
Lemma lem1186550 {A B : Type'} (Q : B -> Prop) (R' : type1413 A B) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term298 A B Q R R' _21206 _21207) = (term299 A B Q R' R _21206 _21207).
Proof. exact (MK_COMB (@lem1186549 B Q _21207) (@lem1186543 A B R' R _21206 _21207)). Qed.
Lemma lem1186554 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186555 {A B : Type'} (R' : type1413 A B) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term299 A B Q R' R _21206 _21207) = (term300 A B R' Q R _21206 _21207).
Proof. exact (@lem1186554 (R' _21206 _21207) (term267 B Q _21207) (term265 A B R _21206 _21207)). Qed.
Lemma lem1186571 {A B : Type'} (R' : type1413 A B) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term298 A B Q R R' _21206 _21207) = (term300 A B R' Q R _21206 _21207).
Proof. exact (TRANS (@lem1186550 A B Q R' R _21206 _21207) (@lem1186555 A B R' Q R _21206 _21207)). Qed.
Lemma lem1186572 {A : Type'} (P : A -> Prop) (_21206 : A) : (term297 A P _21206) = (term297 A P _21206).
Proof. exact (eq_refl (term297 A P _21206)). Qed.
Lemma lem1186573 {A B : Type'} (P : A -> Prop) (R' : type1413 A B) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term266 A B P Q R R' _21206 _21207) = (term301 A B P R' Q R _21206 _21207).
Proof. exact (MK_COMB (@lem1186572 A P _21206) (@lem1186571 A B R' Q R _21206 _21207)). Qed.
Lemma lem1186577 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186578 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term301 A B P R' Q R _21206 _21207) = (term302 A B R' P Q R _21206 _21207).
Proof. exact (@lem1186577 (R' _21206 _21207) (term267 A P _21206) (term303 A B Q R _21206 _21207)). Qed.
Lemma lem1186604 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term266 A B P Q R R' _21206 _21207) = (term302 A B R' P Q R _21206 _21207).
Proof. exact (TRANS (@lem1186573 A B P R' Q R _21206 _21207) (@lem1186578 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186606 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term304 A B P Q R R' _21206 _21207) = (term305 A B R' P Q R _21206 _21207).
Proof. exact (MK_COMB (@lem1186605) (@lem1186604 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186632 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term302 A B R' P Q R _21206 _21207) = (term302 A B R' P Q R _21206 _21207).
Proof. exact (eq_refl (term302 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186633 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : ((term266 A B P Q R R' _21206 _21207) = (term302 A B R' P Q R _21206 _21207)) = ((term302 A B R' P Q R _21206 _21207) = (term302 A B R' P Q R _21206 _21207)).
Proof. exact (MK_COMB (@lem1186606 A B R' P Q R _21206 _21207) (@lem1186632 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186636 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186635 Prop x). Qed.
Lemma lem1186637 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : ((term302 A B R' P Q R _21206 _21207) = (term302 A B R' P Q R _21206 _21207)) = True.
Proof. exact (@lem1186636 (term302 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186638 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : ((term266 A B P Q R R' _21206 _21207) = (term302 A B R' P Q R _21206 _21207)) = True.
Proof. exact (TRANS (@lem1186633 A B R' P Q R _21206 _21207) (@lem1186637 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186639 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : True = ((term266 A B P Q R R' _21206 _21207) = (term302 A B R' P Q R _21206 _21207)).
Proof. exact (SYM (@lem1186638 A B R' P Q R _21206 _21207)). Qed.
Lemma lem1186640 {A B : Type'} (R' : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term266 A B P Q R R' _21206 _21207) = (term302 A B R' P Q R _21206 _21207).
Proof. exact (EQ_MP (@lem1186639 A B R' P Q R _21206 _21207) (@lem0)). Qed.
Lemma lem1186641 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term302 A B R' P Q R _21206 _21207.
Proof. exact (EQ_MP (@lem1186640 A B R' P Q R _21206 _21207) (@lem1186213 A B _21206 _21207 l m P Q R R' h1)). Qed.
Lemma lem1186643 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186644 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) (_21207 : B) : (term302 A B R' P Q R _21206 _21207) = (term306 A B P Q R R' _21206 _21207).
Proof. exact (@lem1186643 (term307 A B P Q R _21206 _21207) (R' _21206 _21207)). Qed.
Lemma lem1186646 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1186647 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term308 A B P Q R _21206 _21207) = (term309 A B P Q R _21206 _21207).
Proof. exact (@lem1186646 (term267 A P _21206) (term303 A B Q R _21206 _21207)). Qed.
Lemma lem1186649 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186650 {A : Type'} (P : A -> Prop) (_21206 : A) : (term310 A P _21206) = (P _21206).
Proof. exact (@lem1186649 (P _21206)). Qed.
Lemma lem1186651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1186652 {A : Type'} (P : A -> Prop) (_21206 : A) : (term311 A P _21206) = (term312 A P _21206).
Proof. exact (MK_COMB (@lem1186651) (@lem1186650 A P _21206)). Qed.
Lemma lem1186654 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1186655 {A B : Type'} (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term313 A B Q R _21206 _21207) = (term314 A B Q R _21206 _21207).
Proof. exact (@lem1186654 (term267 B Q _21207) (term265 A B R _21206 _21207)). Qed.
Lemma lem1186657 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186658 {B : Type'} (Q : B -> Prop) (_21207 : B) : (term310 B Q _21207) = (Q _21207).
Proof. exact (@lem1186657 (Q _21207)). Qed.
Lemma lem1186659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1186660 {B : Type'} (Q : B -> Prop) (_21207 : B) : (term311 B Q _21207) = (term312 B Q _21207).
Proof. exact (MK_COMB (@lem1186659) (@lem1186658 B Q _21207)). Qed.
Lemma lem1186662 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186663 {A B : Type'} (R : type1413 A B) (_21206 : A) (_21207 : B) : (term315 A B R _21206 _21207) = (R _21206 _21207).
Proof. exact (@lem1186662 (R _21206 _21207)). Qed.
Lemma lem1186664 {A B : Type'} (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term314 A B Q R _21206 _21207) = (term316 A B Q R _21206 _21207).
Proof. exact (MK_COMB (@lem1186660 B Q _21207) (@lem1186663 A B R _21206 _21207)). Qed.
Lemma lem1186665 {A B : Type'} (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term313 A B Q R _21206 _21207) = (term316 A B Q R _21206 _21207).
Proof. exact (TRANS (@lem1186655 A B Q R _21206 _21207) (@lem1186664 A B Q R _21206 _21207)). Qed.
Lemma lem1186666 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term309 A B P Q R _21206 _21207) = (term317 A B P Q R _21206 _21207).
Proof. exact (MK_COMB (@lem1186652 A P _21206) (@lem1186665 A B Q R _21206 _21207)). Qed.
Lemma lem1186667 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term308 A B P Q R _21206 _21207) = (term317 A B P Q R _21206 _21207).
Proof. exact (TRANS (@lem1186647 A B P Q R _21206 _21207) (@lem1186666 A B P Q R _21206 _21207)). Qed.
Lemma lem1186668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186669 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (_21206 : A) (_21207 : B) : (term318 A B P Q R _21206 _21207) = (term319 A B P Q R _21206 _21207).
Proof. exact (MK_COMB (@lem1186668) (@lem1186667 A B P Q R _21206 _21207)). Qed.
Lemma lem1186670 {A B : Type'} (R' : type1413 A B) (_21206 : A) (_21207 : B) : (R' _21206 _21207) = (R' _21206 _21207).
Proof. exact (eq_refl (R' _21206 _21207)). Qed.
Lemma lem1186671 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) (_21207 : B) : (term306 A B P Q R R' _21206 _21207) = (term320 A B P Q R R' _21206 _21207).
Proof. exact (MK_COMB (@lem1186669 A B P Q R _21206 _21207) (@lem1186670 A B R' _21206 _21207)). Qed.
Lemma lem1186672 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (_21206 : A) (_21207 : B) : (term302 A B R' P Q R _21206 _21207) = (term320 A B P Q R R' _21206 _21207).
Proof. exact (TRANS (@lem1186644 A B P Q R R' _21206 _21207) (@lem1186671 A B P Q R R' _21206 _21207)). Qed.
Lemma lem1186674 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term316 A B Q R x y.
Proof. exact (conj (@lem1186395 A B x y l m P Q R R' h1 h2) (@lem1186516 A B R l m R' x y h1)). Qed.
Lemma lem1186675 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term317 A B P Q R x y.
Proof. exact (conj (@lem1186335 A B x y l m P Q R R' h1 h2) (@lem1186674 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186677 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R R' _21206 _21207.
Proof. exact (EQ_MP (@lem1186672 A B P Q R R' _21206 _21207) (@lem1186641 A B _21206 _21207 l m P Q R R' h1)). Qed.
Lemma lem1186678 {A B : Type'} (_21206 : A) (_21207 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R R' _21206 _21207.
Proof. exact (@lem1186677 A B _21206 _21207 l m P Q R R' h1). Qed.
Lemma lem1186679 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R R' x y.
Proof. exact (@lem1186678 A B x y l m P Q R R' h1). Qed.
Lemma lem1186682 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : R' x y.
Proof. exact (@lem1186679 A B x y l m P Q R R' h2 (@lem1186675 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186683 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term296 A B R' x y.
Proof. exact (fun h0 : term265 A B R' x y => @lem1186682 A B x y l m P Q R R' h1 h2). Qed.
Lemma lem1186685 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186686 {A B : Type'} (R' : type1413 A B) (x : A) (y : B) : (term296 A B R' x y) = (R' x y).
Proof. exact (@lem1186685 (R' x y)). Qed.
Lemma lem1186687 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : R' x y.
Proof. exact (EQ_MP (@lem1186686 A B R' x y) (@lem1186683 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1186692 {A B : Type'} (R' : type1413 A B) (x : A) (y : B) : (term265 A B R' x y) = (term321 A B R' x y).
Proof. exact (@lem1186690 (R' x y)). Qed.
Lemma lem1186695 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) (x : A) (y : B) (h1 : term173 A B R l m R' x y) : term321 A B R' x y.
Proof. exact (EQ_MP (@lem1186692 A B R' x y) (@lem1186177 A B R l m R' x y h1)). Qed.
Lemma lem1186698 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : False.
Proof. exact (@lem1186695 A B R l m R' x y h1 (@lem1186687 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186699 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : term322.
Proof. exact (fun h0 : ~ False => @lem1186698 A B x y l m P Q R R' h1 h2). Qed.
Lemma lem1186701 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186702 : term322 = False.
Proof. exact (@lem1186701 False). Qed.
Lemma lem1186703 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term173 A B R l m R' x y) (h2 : term40 A B l m P Q R R') : False.
Proof. exact (EQ_MP (@lem1186702) (@lem1186699 A B x y l m P Q R R' h1 h2)). Qed.
Lemma lem1186705 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In A x l.
Proof. exact (proj1 (@lem1185901 A B R x y l m R' h1)). Qed.
Lemma lem1186706 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term269 A x l.
Proof. exact (fun h0 : term264 A x l => @lem1186705 A B R x y l m R' h1). Qed.
Lemma lem1186708 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186709 {A : Type'} (x : A) (l : list A) : (term269 A x l) = (@List.In A x l).
Proof. exact (@lem1186708 (@List.In A x l)). Qed.
Lemma lem1186710 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In A x l.
Proof. exact (EQ_MP (@lem1186709 A x l) (@lem1186706 A B R x y l m R' h1)). Qed.
Lemma lem1186716 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186717 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : (term92 A l P _21210) = (term271 A P _21210 l).
Proof. exact (@lem1186716 (P _21210) (term264 A _21210 l)). Qed.
Lemma lem1186723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186724 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : (term272 A l P _21210) = (term273 A P _21210 l).
Proof. exact (MK_COMB (@lem1186723) (@lem1186717 A P _21210 l)). Qed.
Lemma lem1186730 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : (term271 A P _21210 l) = (term271 A P _21210 l).
Proof. exact (eq_refl (term271 A P _21210 l)). Qed.
Lemma lem1186731 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : ((term92 A l P _21210) = (term271 A P _21210 l)) = ((term271 A P _21210 l) = (term271 A P _21210 l)).
Proof. exact (MK_COMB (@lem1186724 A P _21210 l) (@lem1186730 A P _21210 l)). Qed.
Lemma lem1186733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186734 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186733 Prop x). Qed.
Lemma lem1186735 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : ((term271 A P _21210 l) = (term271 A P _21210 l)) = True.
Proof. exact (@lem1186734 (term271 A P _21210 l)). Qed.
Lemma lem1186736 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : ((term92 A l P _21210) = (term271 A P _21210 l)) = True.
Proof. exact (TRANS (@lem1186731 A P _21210 l) (@lem1186735 A P _21210 l)). Qed.
Lemma lem1186737 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : True = ((term92 A l P _21210) = (term271 A P _21210 l)).
Proof. exact (SYM (@lem1186736 A P _21210 l)). Qed.
Lemma lem1186738 {A : Type'} (P : A -> Prop) (_21210 : A) (l : list A) : (term92 A l P _21210) = (term271 A P _21210 l).
Proof. exact (EQ_MP (@lem1186737 A P _21210 l) (@lem0)). Qed.
Lemma lem1186739 {A B : Type'} (_21210 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term271 A P _21210 l.
Proof. exact (EQ_MP (@lem1186738 A P _21210 l) (@lem1186219 A B _21210 l m P Q R R' h1)). Qed.
Lemma lem1186741 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186742 {A : Type'} (l : list A) (P : A -> Prop) (_21210 : A) : (term271 A P _21210 l) = (term275 A l P _21210).
Proof. exact (@lem1186741 (term264 A _21210 l) (P _21210)). Qed.
Lemma lem1186744 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186745 {A : Type'} (_21210 : A) (l : list A) : (term276 A _21210 l) = (@List.In A _21210 l).
Proof. exact (@lem1186744 (@List.In A _21210 l)). Qed.
Lemma lem1186746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186747 {A : Type'} (_21210 : A) (l : list A) : (term277 A _21210 l) = (term278 A _21210 l).
Proof. exact (MK_COMB (@lem1186746) (@lem1186745 A _21210 l)). Qed.
Lemma lem1186748 {A : Type'} (P : A -> Prop) (_21210 : A) : (P _21210) = (P _21210).
Proof. exact (eq_refl (P _21210)). Qed.
Lemma lem1186749 {A : Type'} (l : list A) (P : A -> Prop) (_21210 : A) : (term275 A l P _21210) = (term88 A l P _21210).
Proof. exact (MK_COMB (@lem1186747 A _21210 l) (@lem1186748 A P _21210)). Qed.
Lemma lem1186750 {A : Type'} (l : list A) (P : A -> Prop) (_21210 : A) : (term271 A P _21210 l) = (term88 A l P _21210).
Proof. exact (TRANS (@lem1186742 A l P _21210) (@lem1186749 A l P _21210)). Qed.
Lemma lem1186753 {A B : Type'} (_21210 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P _21210.
Proof. exact (EQ_MP (@lem1186750 A l P _21210) (@lem1186739 A B _21210 l m P Q R R' h1)). Qed.
Lemma lem1186754 {A B : Type'} (_21210 : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P _21210.
Proof. exact (@lem1186753 A B _21210 l m P Q R R' h1). Qed.
Lemma lem1186755 {A B : Type'} (x : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 A l P x.
Proof. exact (@lem1186754 A B x l m P Q R R' h1). Qed.
Lemma lem1186758 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : P x.
Proof. exact (@lem1186755 A B x l m P Q R R' h1 (@lem1186710 A B R x y l m R' h2)). Qed.
Lemma lem1186759 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term279 A P x.
Proof. exact (fun h0 : term267 A P x => @lem1186758 A B P Q R x y l m R' h1 h2). Qed.
Lemma lem1186761 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186762 {A : Type'} (P : A -> Prop) (x : A) : (term279 A P x) = (P x).
Proof. exact (@lem1186761 (P x)). Qed.
Lemma lem1186763 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : P x.
Proof. exact (EQ_MP (@lem1186762 A P x) (@lem1186759 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1186765 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In B y m.
Proof. exact (proj2 (@lem1185901 A B R x y l m R' h1)). Qed.
Lemma lem1186766 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term269 B y m.
Proof. exact (fun h0 : term264 B y m => @lem1186765 A B R x y l m R' h1). Qed.
Lemma lem1186768 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186769 {B : Type'} (y : B) (m : list B) : (term269 B y m) = (@List.In B y m).
Proof. exact (@lem1186768 (@List.In B y m)). Qed.
Lemma lem1186770 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In B y m.
Proof. exact (EQ_MP (@lem1186769 B y m) (@lem1186766 A B R x y l m R' h1)). Qed.
Lemma lem1186776 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186777 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : (term92 B m Q _21211) = (term271 B Q _21211 m).
Proof. exact (@lem1186776 (Q _21211) (term264 B _21211 m)). Qed.
Lemma lem1186783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186784 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : (term272 B m Q _21211) = (term273 B Q _21211 m).
Proof. exact (MK_COMB (@lem1186783) (@lem1186777 B Q _21211 m)). Qed.
Lemma lem1186790 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : (term271 B Q _21211 m) = (term271 B Q _21211 m).
Proof. exact (eq_refl (term271 B Q _21211 m)). Qed.
Lemma lem1186791 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : ((term92 B m Q _21211) = (term271 B Q _21211 m)) = ((term271 B Q _21211 m) = (term271 B Q _21211 m)).
Proof. exact (MK_COMB (@lem1186784 B Q _21211 m) (@lem1186790 B Q _21211 m)). Qed.
Lemma lem1186793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186794 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186793 Prop x). Qed.
Lemma lem1186795 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : ((term271 B Q _21211 m) = (term271 B Q _21211 m)) = True.
Proof. exact (@lem1186794 (term271 B Q _21211 m)). Qed.
Lemma lem1186796 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : ((term92 B m Q _21211) = (term271 B Q _21211 m)) = True.
Proof. exact (TRANS (@lem1186791 B Q _21211 m) (@lem1186795 B Q _21211 m)). Qed.
Lemma lem1186797 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : True = ((term92 B m Q _21211) = (term271 B Q _21211 m)).
Proof. exact (SYM (@lem1186796 B Q _21211 m)). Qed.
Lemma lem1186798 {B : Type'} (Q : B -> Prop) (_21211 : B) (m : list B) : (term92 B m Q _21211) = (term271 B Q _21211 m).
Proof. exact (EQ_MP (@lem1186797 B Q _21211 m) (@lem0)). Qed.
Lemma lem1186799 {A B : Type'} (_21211 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term271 B Q _21211 m.
Proof. exact (EQ_MP (@lem1186798 B Q _21211 m) (@lem1186225 A B _21211 l m P Q R R' h1)). Qed.
Lemma lem1186801 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186802 {B : Type'} (m : list B) (Q : B -> Prop) (_21211 : B) : (term271 B Q _21211 m) = (term275 B m Q _21211).
Proof. exact (@lem1186801 (term264 B _21211 m) (Q _21211)). Qed.
Lemma lem1186804 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186805 {B : Type'} (_21211 : B) (m : list B) : (term276 B _21211 m) = (@List.In B _21211 m).
Proof. exact (@lem1186804 (@List.In B _21211 m)). Qed.
Lemma lem1186806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186807 {B : Type'} (_21211 : B) (m : list B) : (term277 B _21211 m) = (term278 B _21211 m).
Proof. exact (MK_COMB (@lem1186806) (@lem1186805 B _21211 m)). Qed.
Lemma lem1186808 {B : Type'} (Q : B -> Prop) (_21211 : B) : (Q _21211) = (Q _21211).
Proof. exact (eq_refl (Q _21211)). Qed.
Lemma lem1186809 {B : Type'} (m : list B) (Q : B -> Prop) (_21211 : B) : (term275 B m Q _21211) = (term88 B m Q _21211).
Proof. exact (MK_COMB (@lem1186807 B _21211 m) (@lem1186808 B Q _21211)). Qed.
Lemma lem1186810 {B : Type'} (m : list B) (Q : B -> Prop) (_21211 : B) : (term271 B Q _21211 m) = (term88 B m Q _21211).
Proof. exact (TRANS (@lem1186802 B m Q _21211) (@lem1186809 B m Q _21211)). Qed.
Lemma lem1186813 {A B : Type'} (_21211 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q _21211.
Proof. exact (EQ_MP (@lem1186810 B m Q _21211) (@lem1186799 A B _21211 l m P Q R R' h1)). Qed.
Lemma lem1186814 {A B : Type'} (_21211 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q _21211.
Proof. exact (@lem1186813 A B _21211 l m P Q R R' h1). Qed.
Lemma lem1186815 {A B : Type'} (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term88 B m Q y.
Proof. exact (@lem1186814 A B y l m P Q R R' h1). Qed.
Lemma lem1186818 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : Q y.
Proof. exact (@lem1186815 A B y l m P Q R R' h1 (@lem1186770 A B R x y l m R' h2)). Qed.
Lemma lem1186819 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term279 B Q y.
Proof. exact (fun h0 : term267 B Q y => @lem1186818 A B P Q R x y l m R' h1 h2). Qed.
Lemma lem1186821 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186822 {B : Type'} (Q : B -> Prop) (y : B) : (term279 B Q y) = (Q y).
Proof. exact (@lem1186821 (Q y)). Qed.
Lemma lem1186823 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : Q y.
Proof. exact (EQ_MP (@lem1186822 B Q y) (@lem1186819 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1186825 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In A x l.
Proof. exact (proj1 (@lem1185901 A B R x y l m R' h1)). Qed.
Lemma lem1186826 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term269 A x l.
Proof. exact (fun h0 : term264 A x l => @lem1186825 A B R x y l m R' h1). Qed.
Lemma lem1186828 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186829 {A : Type'} (x : A) (l : list A) : (term269 A x l) = (@List.In A x l).
Proof. exact (@lem1186828 (@List.In A x l)). Qed.
Lemma lem1186830 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In A x l.
Proof. exact (EQ_MP (@lem1186829 A x l) (@lem1186826 A B R x y l m R' h1)). Qed.
Lemma lem1186832 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In B y m.
Proof. exact (proj2 (@lem1185901 A B R x y l m R' h1)). Qed.
Lemma lem1186833 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term269 B y m.
Proof. exact (fun h0 : term264 B y m => @lem1186832 A B R x y l m R' h1). Qed.
Lemma lem1186835 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186836 {B : Type'} (y : B) (m : list B) : (term269 B y m) = (@List.In B y m).
Proof. exact (@lem1186835 (@List.In B y m)). Qed.
Lemma lem1186837 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : @List.In B y m.
Proof. exact (EQ_MP (@lem1186836 B y m) (@lem1186833 A B R x y l m R' h1)). Qed.
Lemma lem1186853 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1186854 {A B : Type'} (R' : type1413 A B) (_21214 : A) (_21215 : B) (m : list B) : (term280 A B m R' _21214 _21215) = (term281 A B R' _21214 _21215 m).
Proof. exact (@lem1186853 (R' _21214 _21215) (term264 B _21215 m)). Qed.
Lemma lem1186860 {A : Type'} (_21214 : A) (l : list A) : (term282 A _21214 l) = (term282 A _21214 l).
Proof. exact (eq_refl (term282 A _21214 l)). Qed.
Lemma lem1186861 {A B : Type'} (l : list A) (R' : type1413 A B) (_21214 : A) (_21215 : B) (m : list B) : (term263 A B l m R' _21214 _21215) = (term283 A B l R' _21214 _21215 m).
Proof. exact (MK_COMB (@lem1186860 A _21214 l) (@lem1186854 A B R' _21214 _21215 m)). Qed.
Lemma lem1186865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186866 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term283 A B l R' _21214 _21215 m) = (term284 A B R' _21214 l _21215 m).
Proof. exact (@lem1186865 (R' _21214 _21215) (term264 A _21214 l) (term264 B _21215 m)). Qed.
Lemma lem1186882 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term263 A B l m R' _21214 _21215) = (term284 A B R' _21214 l _21215 m).
Proof. exact (TRANS (@lem1186861 A B l R' _21214 _21215 m) (@lem1186866 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1186884 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term285 A B l m R' _21214 _21215) = (term286 A B R' _21214 l _21215 m).
Proof. exact (MK_COMB (@lem1186883) (@lem1186882 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186900 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term284 A B R' _21214 l _21215 m) = (term284 A B R' _21214 l _21215 m).
Proof. exact (eq_refl (term284 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186901 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : ((term263 A B l m R' _21214 _21215) = (term284 A B R' _21214 l _21215 m)) = ((term284 A B R' _21214 l _21215 m) = (term284 A B R' _21214 l _21215 m)).
Proof. exact (MK_COMB (@lem1186884 A B R' _21214 l _21215 m) (@lem1186900 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1186904 (x : Prop) : (x = x) = True.
Proof. exact (@lem1186903 Prop x). Qed.
Lemma lem1186905 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : ((term284 A B R' _21214 l _21215 m) = (term284 A B R' _21214 l _21215 m)) = True.
Proof. exact (@lem1186904 (term284 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186906 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : ((term263 A B l m R' _21214 _21215) = (term284 A B R' _21214 l _21215 m)) = True.
Proof. exact (TRANS (@lem1186901 A B R' _21214 l _21215 m) (@lem1186905 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186907 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : True = ((term263 A B l m R' _21214 _21215) = (term284 A B R' _21214 l _21215 m)).
Proof. exact (SYM (@lem1186906 A B R' _21214 l _21215 m)). Qed.
Lemma lem1186908 {A B : Type'} (R' : type1413 A B) (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term263 A B l m R' _21214 _21215) = (term284 A B R' _21214 l _21215 m).
Proof. exact (EQ_MP (@lem1186907 A B R' _21214 l _21215 m) (@lem0)). Qed.
Lemma lem1186909 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term284 A B R' _21214 l _21215 m.
Proof. exact (EQ_MP (@lem1186908 A B R' _21214 l _21215 m) (@lem1186237 A B _21214 _21215 R x y l m R' h1)). Qed.
Lemma lem1186911 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1186912 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) (_21215 : B) : (term284 A B R' _21214 l _21215 m) = (term287 A B l m R' _21214 _21215).
Proof. exact (@lem1186911 (term111 A B _21214 l _21215 m) (R' _21214 _21215)). Qed.
Lemma lem1186914 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1186915 {A B : Type'} (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term290 A B _21214 l _21215 m) = (term291 A B _21214 l _21215 m).
Proof. exact (@lem1186914 (term264 A _21214 l) (term264 B _21215 m)). Qed.
Lemma lem1186917 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186918 {A : Type'} (_21214 : A) (l : list A) : (term276 A _21214 l) = (@List.In A _21214 l).
Proof. exact (@lem1186917 (@List.In A _21214 l)). Qed.
Lemma lem1186919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1186920 {A : Type'} (_21214 : A) (l : list A) : (term292 A _21214 l) = (term293 A _21214 l).
Proof. exact (MK_COMB (@lem1186919) (@lem1186918 A _21214 l)). Qed.
Lemma lem1186922 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1186923 {B : Type'} (_21215 : B) (m : list B) : (term276 B _21215 m) = (@List.In B _21215 m).
Proof. exact (@lem1186922 (@List.In B _21215 m)). Qed.
Lemma lem1186924 {A B : Type'} (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term291 A B _21214 l _21215 m) = (term114 A B _21214 l _21215 m).
Proof. exact (MK_COMB (@lem1186920 A _21214 l) (@lem1186923 B _21215 m)). Qed.
Lemma lem1186925 {A B : Type'} (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term290 A B _21214 l _21215 m) = (term114 A B _21214 l _21215 m).
Proof. exact (TRANS (@lem1186915 A B _21214 l _21215 m) (@lem1186924 A B _21214 l _21215 m)). Qed.
Lemma lem1186926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1186927 {A B : Type'} (_21214 : A) (l : list A) (_21215 : B) (m : list B) : (term294 A B _21214 l _21215 m) = (term295 A B _21214 l _21215 m).
Proof. exact (MK_COMB (@lem1186926) (@lem1186925 A B _21214 l _21215 m)). Qed.
Lemma lem1186928 {A B : Type'} (R' : type1413 A B) (_21214 : A) (_21215 : B) : (R' _21214 _21215) = (R' _21214 _21215).
Proof. exact (eq_refl (R' _21214 _21215)). Qed.
Lemma lem1186929 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) (_21215 : B) : (term287 A B l m R' _21214 _21215) = (term80 A B l m R' _21214 _21215).
Proof. exact (MK_COMB (@lem1186927 A B _21214 l _21215 m) (@lem1186928 A B R' _21214 _21215)). Qed.
Lemma lem1186930 {A B : Type'} (l : list A) (m : list B) (R' : type1413 A B) (_21214 : A) (_21215 : B) : (term284 A B R' _21214 l _21215 m) = (term80 A B l m R' _21214 _21215).
Proof. exact (TRANS (@lem1186912 A B l m R' _21214 _21215) (@lem1186929 A B l m R' _21214 _21215)). Qed.
Lemma lem1186932 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term114 A B x l y m.
Proof. exact (conj (@lem1186830 A B R x y l m R' h1) (@lem1186837 A B R x y l m R' h1)). Qed.
Lemma lem1186934 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term80 A B l m R' _21214 _21215.
Proof. exact (EQ_MP (@lem1186930 A B l m R' _21214 _21215) (@lem1186909 A B _21214 _21215 R x y l m R' h1)). Qed.
Lemma lem1186935 {A B : Type'} (_21214 : A) (_21215 : B) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term80 A B l m R' _21214 _21215.
Proof. exact (@lem1186934 A B _21214 _21215 R x y l m R' h1). Qed.
Lemma lem1186936 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term80 A B l m R' x y.
Proof. exact (@lem1186935 A B x y R x y l m R' h1). Qed.
Lemma lem1186939 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : R' x y.
Proof. exact (@lem1186936 A B R x y l m R' h1 (@lem1186932 A B R x y l m R' h1)). Qed.
Lemma lem1186940 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term296 A B R' x y.
Proof. exact (fun h0 : term265 A B R' x y => @lem1186939 A B R x y l m R' h1). Qed.
Lemma lem1186942 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1186943 {A B : Type'} (R' : type1413 A B) (x : A) (y : B) : (term296 A B R' x y) = (R' x y).
Proof. exact (@lem1186942 (R' x y)). Qed.
Lemma lem1186944 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : R' x y.
Proof. exact (EQ_MP (@lem1186943 A B R' x y) (@lem1186940 A B R x y l m R' h1)). Qed.
Lemma lem1186960 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186961 {A B : Type'} (R : type1413 A B) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term299 A B Q R R' _21212 _21213) = (term300 A B R Q R' _21212 _21213).
Proof. exact (@lem1186960 (R _21212 _21213) (term267 B Q _21213) (term265 A B R' _21212 _21213)). Qed.
Lemma lem1186977 {A : Type'} (P : A -> Prop) (_21212 : A) : (term297 A P _21212) = (term297 A P _21212).
Proof. exact (eq_refl (term297 A P _21212)). Qed.
Lemma lem1186978 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term268 A B P Q R R' _21212 _21213) = (term301 A B P R Q R' _21212 _21213).
Proof. exact (MK_COMB (@lem1186977 A P _21212) (@lem1186961 A B R Q R' _21212 _21213)). Qed.
Lemma lem1186982 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1186983 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term301 A B P R Q R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213).
Proof. exact (@lem1186982 (R _21212 _21213) (term267 A P _21212) (term303 A B Q R' _21212 _21213)). Qed.
Lemma lem1187009 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term268 A B P Q R R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213).
Proof. exact (TRANS (@lem1186978 A B P R Q R' _21212 _21213) (@lem1186983 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187011 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term323 A B P Q R R' _21212 _21213) = (term305 A B R P Q R' _21212 _21213).
Proof. exact (MK_COMB (@lem1187010) (@lem1187009 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187037 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term302 A B R P Q R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213).
Proof. exact (eq_refl (term302 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187038 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : ((term268 A B P Q R R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213)) = ((term302 A B R P Q R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213)).
Proof. exact (MK_COMB (@lem1187011 A B R P Q R' _21212 _21213) (@lem1187037 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1187041 (x : Prop) : (x = x) = True.
Proof. exact (@lem1187040 Prop x). Qed.
Lemma lem1187042 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : ((term302 A B R P Q R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213)) = True.
Proof. exact (@lem1187041 (term302 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187043 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : ((term268 A B P Q R R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213)) = True.
Proof. exact (TRANS (@lem1187038 A B R P Q R' _21212 _21213) (@lem1187042 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187044 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : True = ((term268 A B P Q R R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213)).
Proof. exact (SYM (@lem1187043 A B R P Q R' _21212 _21213)). Qed.
Lemma lem1187045 {A B : Type'} (R : type1413 A B) (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term268 A B P Q R R' _21212 _21213) = (term302 A B R P Q R' _21212 _21213).
Proof. exact (EQ_MP (@lem1187044 A B R P Q R' _21212 _21213) (@lem0)). Qed.
Lemma lem1187046 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term302 A B R P Q R' _21212 _21213.
Proof. exact (EQ_MP (@lem1187045 A B R P Q R' _21212 _21213) (@lem1186259 A B _21212 _21213 l m P Q R R' h1)). Qed.
Lemma lem1187048 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1187049 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (R : type1413 A B) (_21212 : A) (_21213 : B) : (term302 A B R P Q R' _21212 _21213) = (term306 A B P Q R' R _21212 _21213).
Proof. exact (@lem1187048 (term307 A B P Q R' _21212 _21213) (R _21212 _21213)). Qed.
Lemma lem1187051 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1187052 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term308 A B P Q R' _21212 _21213) = (term309 A B P Q R' _21212 _21213).
Proof. exact (@lem1187051 (term267 A P _21212) (term303 A B Q R' _21212 _21213)). Qed.
Lemma lem1187054 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1187055 {A : Type'} (P : A -> Prop) (_21212 : A) : (term310 A P _21212) = (P _21212).
Proof. exact (@lem1187054 (P _21212)). Qed.
Lemma lem1187056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187057 {A : Type'} (P : A -> Prop) (_21212 : A) : (term311 A P _21212) = (term312 A P _21212).
Proof. exact (MK_COMB (@lem1187056) (@lem1187055 A P _21212)). Qed.
Lemma lem1187059 (a : Prop) (b : Prop) : (term288 a b) = (term289 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1187060 {A B : Type'} (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term313 A B Q R' _21212 _21213) = (term314 A B Q R' _21212 _21213).
Proof. exact (@lem1187059 (term267 B Q _21213) (term265 A B R' _21212 _21213)). Qed.
Lemma lem1187062 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1187063 {B : Type'} (Q : B -> Prop) (_21213 : B) : (term310 B Q _21213) = (Q _21213).
Proof. exact (@lem1187062 (Q _21213)). Qed.
Lemma lem1187064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187065 {B : Type'} (Q : B -> Prop) (_21213 : B) : (term311 B Q _21213) = (term312 B Q _21213).
Proof. exact (MK_COMB (@lem1187064) (@lem1187063 B Q _21213)). Qed.
Lemma lem1187067 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1187068 {A B : Type'} (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term315 A B R' _21212 _21213) = (R' _21212 _21213).
Proof. exact (@lem1187067 (R' _21212 _21213)). Qed.
Lemma lem1187069 {A B : Type'} (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term314 A B Q R' _21212 _21213) = (term316 A B Q R' _21212 _21213).
Proof. exact (MK_COMB (@lem1187065 B Q _21213) (@lem1187068 A B R' _21212 _21213)). Qed.
Lemma lem1187070 {A B : Type'} (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term313 A B Q R' _21212 _21213) = (term316 A B Q R' _21212 _21213).
Proof. exact (TRANS (@lem1187060 A B Q R' _21212 _21213) (@lem1187069 A B Q R' _21212 _21213)). Qed.
Lemma lem1187071 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term309 A B P Q R' _21212 _21213) = (term317 A B P Q R' _21212 _21213).
Proof. exact (MK_COMB (@lem1187057 A P _21212) (@lem1187070 A B Q R' _21212 _21213)). Qed.
Lemma lem1187072 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term308 A B P Q R' _21212 _21213) = (term317 A B P Q R' _21212 _21213).
Proof. exact (TRANS (@lem1187052 A B P Q R' _21212 _21213) (@lem1187071 A B P Q R' _21212 _21213)). Qed.
Lemma lem1187073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1187074 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (_21212 : A) (_21213 : B) : (term318 A B P Q R' _21212 _21213) = (term319 A B P Q R' _21212 _21213).
Proof. exact (MK_COMB (@lem1187073) (@lem1187072 A B P Q R' _21212 _21213)). Qed.
Lemma lem1187075 {A B : Type'} (R : type1413 A B) (_21212 : A) (_21213 : B) : (R _21212 _21213) = (R _21212 _21213).
Proof. exact (eq_refl (R _21212 _21213)). Qed.
Lemma lem1187076 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (R : type1413 A B) (_21212 : A) (_21213 : B) : (term306 A B P Q R' R _21212 _21213) = (term320 A B P Q R' R _21212 _21213).
Proof. exact (MK_COMB (@lem1187074 A B P Q R' _21212 _21213) (@lem1187075 A B R _21212 _21213)). Qed.
Lemma lem1187077 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R' : type1413 A B) (R : type1413 A B) (_21212 : A) (_21213 : B) : (term302 A B R P Q R' _21212 _21213) = (term320 A B P Q R' R _21212 _21213).
Proof. exact (TRANS (@lem1187049 A B P Q R' R _21212 _21213) (@lem1187076 A B P Q R' R _21212 _21213)). Qed.
Lemma lem1187079 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term316 A B Q R' x y.
Proof. exact (conj (@lem1186823 A B P Q R x y l m R' h1 h2) (@lem1186944 A B R x y l m R' h2)). Qed.
Lemma lem1187080 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term317 A B P Q R' x y.
Proof. exact (conj (@lem1186763 A B P Q R x y l m R' h1 h2) (@lem1187079 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1187082 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R' R _21212 _21213.
Proof. exact (EQ_MP (@lem1187077 A B P Q R' R _21212 _21213) (@lem1187046 A B _21212 _21213 l m P Q R R' h1)). Qed.
Lemma lem1187083 {A B : Type'} (_21212 : A) (_21213 : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R' R _21212 _21213.
Proof. exact (@lem1187082 A B _21212 _21213 l m P Q R R' h1). Qed.
Lemma lem1187084 {A B : Type'} (x : A) (y : B) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term320 A B P Q R' R x y.
Proof. exact (@lem1187083 A B x y l m P Q R R' h1). Qed.
Lemma lem1187087 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : R x y.
Proof. exact (@lem1187084 A B x y l m P Q R R' h1 (@lem1187080 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1187088 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term296 A B R x y.
Proof. exact (fun h0 : term265 A B R x y => @lem1187087 A B P Q R x y l m R' h1 h2). Qed.
Lemma lem1187090 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1187091 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term296 A B R x y) = (R x y).
Proof. exact (@lem1187090 (R x y)). Qed.
Lemma lem1187092 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : R x y.
Proof. exact (EQ_MP (@lem1187091 A B R x y) (@lem1187088 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1187095 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1187097 {A B : Type'} (R : type1413 A B) (x : A) (y : B) : (term265 A B R x y) = (term321 A B R x y).
Proof. exact (@lem1187095 (R x y)). Qed.
Lemma lem1187100 {A B : Type'} (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term202 A B R x y l m R') : term321 A B R x y.
Proof. exact (EQ_MP (@lem1187097 A B R x y) (@lem1186239 A B R x y l m R' h1)). Qed.
Lemma lem1187103 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : False.
Proof. exact (@lem1187100 A B R x y l m R' h2 (@lem1187092 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1187104 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : term322.
Proof. exact (fun h0 : ~ False => @lem1187103 A B P Q R x y l m R' h1 h2). Qed.
Lemma lem1187106 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1187107 : term322 = False.
Proof. exact (@lem1187106 False). Qed.
Lemma lem1187108 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term202 A B R x y l m R') : False.
Proof. exact (EQ_MP (@lem1187107) (@lem1187104 A B P Q R x y l m R' h1 h2)). Qed.
Lemma lem1187109 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term243 A B R x y l m R') : False.
Proof. exact (or_elim (@lem1185885 A B R x y l m R' h2) (fun h0 : term173 A B R l m R' x y => @lem1186703 A B x y l m P Q R R' h0 h1) (fun h0 : term202 A B R x y l m R' => @lem1187108 A B P Q R x y l m R' h1 h0)). Qed.
Lemma lem1187110 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term243 A B R x y l m R') : (term243 A B R x y l m R') = False.
Proof. exact (prop_ext (fun h3 : term243 A B R x y l m R' => @lem1187109 A B P Q R x y l m R' h1 h2) (fun h3 : False => @lem1185885 A B R x y l m R' h2)). Qed.
Lemma lem1187111 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (x : A) (y : B) (l : list A) (m : list B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') (h2 : term243 A B R x y l m R') : False.
Proof. exact (EQ_MP (@lem1187110 A B P Q R x y l m R' h1 h2) (@lem1185885 A B R x y l m R' h2)). Qed.
Lemma lem1187112 {A B : Type'} (x : A) (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term246 A B R x l m R') (h2 : term40 A B l m P Q R R') : False.
Proof. exact (ex_elim (@lem1185672 A B R x l m R' h1) (fun y : B => fun h0 : term245 A B R x l m R' y => @lem1187111 A B P Q R x y l m R' h2 h0)). Qed.
Lemma lem1187113 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term91 A B R l m R') (h2 : term40 A B l m P Q R R') : False.
Proof. exact (ex_elim (@lem1185671 A B R l m R' h1) (fun x : A => fun h0 : term247 A B R l m R' x => @lem1187112 A B x l m P Q R R' h0 h2)). Qed.
Lemma lem1187114 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term91 A B R l m R') (h2 : term40 A B l m P Q R R') : (term91 A B R l m R') = False.
Proof. exact (prop_ext (fun h3 : term91 A B R l m R' => @lem1187113 A B l m P Q R R' h1 h2) (fun h3 : False => @lem1185010 A B R l m R' h1)). Qed.
Lemma lem1187115 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term91 A B R l m R') (h2 : term40 A B l m P Q R R') : False.
Proof. exact (EQ_MP (@lem1187114 A B l m P Q R R' h1 h2) (@lem1185010 A B R l m R' h1)). Qed.
Lemma lem1187116 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : term90 A B R l m R'.
Proof. exact (fun h0 : term91 A B R l m R' => @lem1187115 A B l m P Q R R' h0 h1). Qed.
Lemma lem1187117 {A B : Type'} (l : list A) (m : list B) (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (R' : type1413 A B) (h1 : term40 A B l m P Q R R') : (term43 A B l m R) = (term43 A B l m R').
Proof. exact (EQ_MP (@lem1185009 A B R l m R') (@lem1187116 A B l m P Q R R' h1)). Qed.
Lemma lem1187118 {A B : Type'} (P : A -> Prop) (Q : B -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : term47 A B P Q R l m R'.
Proof. exact (fun h0 : term40 A B l m P Q R R' => @lem1187117 A B l m P Q R R' h0). Qed.
Lemma lem1187123 {A B : Type'} (P : A -> Prop) (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : term51 A B P R l m R'.
Proof. exact (fun Q : B -> Prop => @lem1187118 A B P Q R l m R'). Qed.
Lemma lem1187128 {A B : Type'} (R : type1413 A B) (l : list A) (m : list B) (R' : type1413 A B) : term55 A B R l m R'.
Proof. exact (fun P : A -> Prop => @lem1187123 A B P R l m R'). Qed.
Lemma lem1187133 {A B : Type'} (R : type1413 A B) (l : list A) (R' : type1413 A B) : term59 A B R l R'.
Proof. exact (fun m : list B => @lem1187128 A B R l m R'). Qed.
Lemma lem1187138 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term63 A B R R'.
Proof. exact (fun l : list A => @lem1187133 A B R l R'). Qed.
Lemma lem1187143 {A B : Type'} (R' : type1413 A B) : term75 A B R'.
Proof. exact (fun R : type1413 A B => @lem1187138 A B R R'). Qed.
Lemma lem1187148 {A B : Type'} : term79 A B.
Proof. exact (fun R' : type1413 A B => @lem1187143 A B R'). Qed.
Lemma lem1187149 {A B : Type'} : term78 A B.
Proof. exact (EQ_MP (@lem1185004 A B) (@lem1187148 A B)). Qed.
Lemma lem1187150 {A B : Type'} (R' : type1413 A B) : term324 A B R'.
Proof. exact (@lem1187149 A B R'). Qed.
Lemma lem1187151 {A B : Type'} (R' : type1413 A B) : (term324 A B R') = (term74 A B R').
Proof. exact (eq_refl (term324 A B R')). Qed.
Lemma lem1187152 {A B : Type'} (R' : type1413 A B) : term74 A B R'.
Proof. exact (EQ_MP (@lem1187151 A B R') (@lem1187150 A B R')). Qed.
Lemma lem1187153 {A B : Type'} (R' : type1413 A B) (R : type1413 A B) : term325 A B R' R.
Proof. exact (@lem1187152 A B R' R). Qed.
Lemma lem1187154 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : (term325 A B R' R) = (term65 A B R R').
Proof. exact (eq_refl (term325 A B R' R)). Qed.
Lemma lem1187155 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term65 A B R R'.
Proof. exact (EQ_MP (@lem1187154 A B R R') (@lem1187153 A B R' R)). Qed.
Lemma lem1187157 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term65 A B R R'.
Proof. exact (@lem1184696 A B R R' (@lem1187155 A B R R')). Qed.
Lemma lem1187158 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term66 A B R R') : False.
Proof. exact (@lem1187157 A B R R' (@lem1184680 A B R R' h1)). Qed.
Lemma lem1187159 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term66 A B R R') : (term66 A B R R') = False.
Proof. exact (prop_ext (fun h2 : term66 A B R R' => @lem1187158 A B R R' h1) (fun h2 : False => @lem1184680 A B R R' h1)). Qed.
Lemma lem1187160 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) (h1 : term66 A B R R') : False.
Proof. exact (EQ_MP (@lem1187159 A B R R' h1) (@lem1184680 A B R R' h1)). Qed.
Lemma lem1187161 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term65 A B R R'.
Proof. exact (fun h0 : term66 A B R R' => @lem1187160 A B R R' h0). Qed.
Lemma lem1187162 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term63 A B R R'.
Proof. exact (EQ_MP (@lem1184679 A B R R') (@lem1187161 A B R R')). Qed.
Lemma lem1187163 {A B : Type'} (R : type1413 A B) (R' : type1413 A B) : term62 A B R R'.
Proof. exact (EQ_MP (@lem1184675 A B R R') (@lem1187162 A B R R')). Qed.
