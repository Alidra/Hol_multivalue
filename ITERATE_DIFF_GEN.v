Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_DIFF_GEN_term_abbrevs.
Require Import ITERATE_DIFF_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import SUPPORT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5772505 {_120745 _120749 : Type'} (op : type1400 _120749) : term0 _120745 _120749 op.
Proof. exact (@lem5772504 _120745 _120749 op). Qed.
Lemma lem5772506 {_120745 _120749 : Type'} (op : type1400 _120749) : (term0 _120745 _120749 op) = (term1 _120745 _120749 op).
Proof. exact (eq_refl (term0 _120745 _120749 op)). Qed.
Lemma lem5772507 {_120745 _120749 : Type'} (op : type1400 _120749) : term1 _120745 _120749 op.
Proof. exact (EQ_MP (@lem5772506 _120745 _120749 op) (@lem5772505 _120745 _120749 op)). Qed.
Lemma lem5772508 {_120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : @monoidal _120749 op.
Proof. exact (h1). Qed.
Lemma lem5772509 {_120745 _120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : term2 _120745 _120749 op.
Proof. exact (@lem5772507 _120745 _120749 op (@lem5772508 _120749 op h1)). Qed.
Lemma lem5772510 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term3 _120745 _120749 op f.
Proof. exact (@lem5772509 _120745 _120749 op h1 f). Qed.
Lemma lem5772511 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term3 _120745 _120749 op f) = (term4 _120745 _120749 op f).
Proof. exact (eq_refl (term3 _120745 _120749 op f)). Qed.
Lemma lem5772512 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term4 _120745 _120749 op f.
Proof. exact (EQ_MP (@lem5772511 _120745 _120749 op f) (@lem5772510 _120745 _120749 f op h1)). Qed.
Lemma lem5772513 {_120745 _120749 : Type'} (f : _120745 -> _120749) (s : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term5 _120745 _120749 op f s.
Proof. exact (@lem5772512 _120745 _120749 f op h1 s). Qed.
Lemma lem5772514 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term5 _120745 _120749 op f s) = (term6 _120745 _120749 op s f).
Proof. exact (eq_refl (term5 _120745 _120749 op f s)). Qed.
Lemma lem5772515 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term6 _120745 _120749 op s f.
Proof. exact (EQ_MP (@lem5772514 _120745 _120749 op s f) (@lem5772513 _120745 _120749 f s op h1)). Qed.
Lemma lem5772516 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (t : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term7 _120745 _120749 op s f t.
Proof. exact (@lem5772515 _120745 _120749 s f op h1 t). Qed.
Lemma lem5772517 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term7 _120745 _120749 op s f t) = (term8 _120745 _120749 t op s f).
Proof. exact (eq_refl (term7 _120745 _120749 op s f t)). Qed.
Lemma lem5772518 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term8 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem5772517 _120745 _120749 t op s f) (@lem5772516 _120745 _120749 s f t op h1)). Qed.
Lemma lem5772519 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term9 _120745 t s) : term9 _120745 t s.
Proof. exact (h1). Qed.
Lemma lem5772520 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : @monoidal _120749 op) (h2 : term9 _120745 t s) : (term10 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f).
Proof. exact (@lem5772518 _120745 _120749 t s f op h1 (@lem5772519 _120745 t s h2)). Qed.
Lemma lem5772521 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term8 _120745 _120749 t op s f.
Proof. exact (fun h0 : term9 _120745 t s => @lem5772520 _120745 _120749 f op t s h1 h0). Qed.
Lemma lem5772522 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term11 _120745 _120749 t op s f.
Proof. exact (fun h0 : @monoidal _120749 op => @lem5772521 _120745 _120749 t s f op h0). Qed.
Lemma lem5772524 (p : Prop) (q : Prop) (r : Prop) : (term12 p q r) = (term13 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5772529 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term11 _120745 _120749 t op s f) = (term14 _120745 _120749 t op s f).
Proof. exact (@lem5772524 (@monoidal _120749 op) (term9 _120745 t s) ((term10 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f))). Qed.
Lemma lem5772531 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term15 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5736505 Prop _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5772532 {_120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term16 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5772531 Prop _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5772533 {_120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term17 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5772532 Prop _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5772534 {_120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term18 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5772533 Prop _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5772535 {_120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term19 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5772534 Prop _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5772546 {_120158 _120196 : Type'} (op : type1400 _120196) : term20 _120158 _120196 op.
Proof. exact (proj1 (@lem5772535 _120158 Prop Prop _120196 op)). Qed.
Lemma lem5772547 {_120158 _120196 : Type'} (op : type1400 _120196) (f : _120158 -> _120196) : term21 _120158 _120196 op f.
Proof. exact (@lem5772546 _120158 _120196 op f). Qed.
Lemma lem5772548 {_120158 _120196 : Type'} (op : type1400 _120196) (f : _120158 -> _120196) : (term21 _120158 _120196 op f) = (term22 _120158 _120196 op f).
Proof. exact (eq_refl (term21 _120158 _120196 op f)). Qed.
Lemma lem5772549 {_120158 _120196 : Type'} (op : type1400 _120196) (f : _120158 -> _120196) : term22 _120158 _120196 op f.
Proof. exact (EQ_MP (@lem5772548 _120158 _120196 op f) (@lem5772547 _120158 _120196 op f)). Qed.
Lemma lem5772550 {_120158 _120196 : Type'} (op : type1400 _120196) (f : _120158 -> _120196) (s : _120158 -> Prop) : term23 _120158 _120196 op f s.
Proof. exact (@lem5772549 _120158 _120196 op f s). Qed.
Lemma lem5772551 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) : (term23 _120158 _120196 op f s) = (term24 _120158 _120196 s op f).
Proof. exact (eq_refl (term23 _120158 _120196 op f s)). Qed.
Lemma lem5772552 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) : term24 _120158 _120196 s op f.
Proof. exact (EQ_MP (@lem5772551 _120158 _120196 s op f) (@lem5772550 _120158 _120196 op f s)). Qed.
Lemma lem5772553 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) (t : _120158 -> Prop) : term25 _120158 _120196 s op f t.
Proof. exact (@lem5772552 _120158 _120196 s op f t). Qed.
Lemma lem5772554 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) (t : _120158 -> Prop) : (term25 _120158 _120196 s op f t) = ((term26 _120158 _120196 op f s t) = (term27 _120158 _120196 s op f t)).
Proof. exact (eq_refl (term25 _120158 _120196 s op f t)). Qed.
Lemma lem5772603 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5772604 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f).
Proof. exact (SYM (@lem5772603 _120296 _120308 op s f h1)). Qed.
Lemma lem5772605 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5772606 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f)) : (term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem5772605 _120296 _120308 op s f h1)). Qed.
Lemma lem5772607 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term28 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem5772604 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f) => @lem5772606 _120296 _120308 op s f h1)). Qed.
Lemma lem5772608 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term29 _120296 _120308 op f) = (term30 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5772607 _120296 _120308 op s f)). Qed.
Lemma lem5772609 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5772610 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term31 _120296 _120308 op f) = (term32 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem5772609 _120308) (@lem5772608 _120296 _120308 op f)). Qed.
Lemma lem5772611 {_120296 _120308 : Type'} (op : type1400 _120296) : (term33 _120296 _120308 op) = (term34 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem5772610 _120296 _120308 op f)). Qed.
Lemma lem5772612 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem5772613 {_120296 _120308 : Type'} (op : type1400 _120296) : (term35 _120296 _120308 op) = (term36 _120296 _120308 op).
Proof. exact (MK_COMB (@lem5772612 _120296 _120308) (@lem5772611 _120296 _120308 op)). Qed.
Lemma lem5772614 {_120296 _120308 : Type'} : (term37 _120296 _120308) = (term38 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem5772613 _120296 _120308 op)). Qed.
Lemma lem5772615 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem5772616 {_120296 _120308 : Type'} : (term39 _120296 _120308) = (term40 _120296 _120308).
Proof. exact (MK_COMB (@lem5772615 _120296) (@lem5772614 _120296 _120308)). Qed.
Lemma lem5772617 {_120296 _120308 : Type'} : term40 _120296 _120308.
Proof. exact (EQ_MP (@lem5772616 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem5772618 {_120296 _120308 : Type'} (op : type1400 _120296) : term41 _120296 _120308 op.
Proof. exact (@lem5772617 _120296 _120308 op). Qed.
Lemma lem5772619 {_120296 _120308 : Type'} (op : type1400 _120296) : (term41 _120296 _120308 op) = (term36 _120296 _120308 op).
Proof. exact (eq_refl (term41 _120296 _120308 op)). Qed.
Lemma lem5772620 {_120296 _120308 : Type'} (op : type1400 _120296) : term36 _120296 _120308 op.
Proof. exact (EQ_MP (@lem5772619 _120296 _120308 op) (@lem5772618 _120296 _120308 op)). Qed.
Lemma lem5772621 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term42 _120296 _120308 op f.
Proof. exact (@lem5772620 _120296 _120308 op f). Qed.
Lemma lem5772622 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term42 _120296 _120308 op f) = (term32 _120296 _120308 op f).
Proof. exact (eq_refl (term42 _120296 _120308 op f)). Qed.
Lemma lem5772623 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term32 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem5772622 _120296 _120308 op f) (@lem5772621 _120296 _120308 op f)). Qed.
Lemma lem5772624 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term43 _120296 _120308 op f s.
Proof. exact (@lem5772623 _120296 _120308 op f s). Qed.
Lemma lem5772625 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term43 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f)).
Proof. exact (eq_refl (term43 _120296 _120308 op f s)). Qed.
Lemma lem5772652 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5772625 _120296 _120308 op s f) (@lem5772624 _120296 _120308 op f s)). Qed.
Lemma lem5772653 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term44 A B op s f).
Proof. exact (@lem5772652 B A op s f). Qed.
Lemma lem5772654 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term45 A B op s t f) = (term46 A B op s t f).
Proof. exact (@lem5772653 A B op (@DIFF A s t) f). Qed.
Lemma lem5772655 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5772656 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term47 A B op s t f) = (term48 A B op s t f).
Proof. exact (MK_COMB (@lem5772655 B op) (@lem5772654 A B op s t f)). Qed.
Lemma lem5772658 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5772625 _120296 _120308 op s f) (@lem5772624 _120296 _120308 op f s)). Qed.
Lemma lem5772659 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term44 A B op s f).
Proof. exact (@lem5772658 B A op s f). Qed.
Lemma lem5772660 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (term44 A B op t f).
Proof. exact (@lem5772659 A B op t f). Qed.
Lemma lem5772661 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term10 A B s op t f) = (term49 A B s op t f).
Proof. exact (MK_COMB (@lem5772656 A B op s t f) (@lem5772660 A B op t f)). Qed.
Lemma lem5772662 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5772663 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term50 A B s op t f) = (term51 A B s op t f).
Proof. exact (MK_COMB (@lem5772662 B) (@lem5772661 A B s op t f)). Qed.
Lemma lem5772665 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term28 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5772625 _120296 _120308 op s f) (@lem5772624 _120296 _120308 op f s)). Qed.
Lemma lem5772666 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term44 A B op s f).
Proof. exact (@lem5772665 B A op s f). Qed.
Lemma lem5772667 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term10 A B s op t f) = (@iterate B A op s f)) = ((term49 A B s op t f) = (term44 A B op s f)).
Proof. exact (MK_COMB (@lem5772663 A B s op t f) (@lem5772666 A B op s f)). Qed.
Lemma lem5772668 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term52 A B t op f s) = (term52 A B t op f s).
Proof. exact (eq_refl (term52 A B t op f s)). Qed.
Lemma lem5772669 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term53 A B t op s f) = (term54 A B t op s f).
Proof. exact (MK_COMB (@lem5772668 A B t op f s) (@lem5772667 A B t op s f)). Qed.
Lemma lem5772670 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term55 A B op s f) = (term56 A B op s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5772669 A B t op s f)). Qed.
Lemma lem5772671 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5772672 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term57 A B op s f) = (term58 A B op s f).
Proof. exact (MK_COMB (@lem5772671 A) (@lem5772670 A B op s f)). Qed.
Lemma lem5772673 {A B : Type'} (op : type1400 B) (f : A -> B) : (term59 A B op f) = (term60 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5772672 A B op s f)). Qed.
Lemma lem5772674 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5772675 {A B : Type'} (op : type1400 B) (f : A -> B) : (term61 A B op f) = (term62 A B op f).
Proof. exact (MK_COMB (@lem5772674 A) (@lem5772673 A B op f)). Qed.
Lemma lem5772676 {A B : Type'} (op : type1400 B) : (term63 A B op) = (term64 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5772675 A B op f)). Qed.
Lemma lem5772677 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5772678 {A B : Type'} (op : type1400 B) : (term65 A B op) = (term66 A B op).
Proof. exact (MK_COMB (@lem5772677 A B) (@lem5772676 A B op)). Qed.
Lemma lem5772679 {B : Type'} (op : type1400 B) : (term67 B op) = (term67 B op).
Proof. exact (eq_refl (term67 B op)). Qed.
Lemma lem5772680 {A B : Type'} (op : type1400 B) : (term68 A B op) = (term69 A B op).
Proof. exact (MK_COMB (@lem5772679 B op) (@lem5772678 A B op)). Qed.
Lemma lem5772681 {A B : Type'} : (term70 A B) = (term71 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5772680 A B op)). Qed.
Lemma lem5772682 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5772683 {A B : Type'} : (term72 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem5772682 B) (@lem5772681 A B)). Qed.
Lemma lem5772684 {A B : Type'} : (term73 A B) = (term72 A B).
Proof. exact (SYM (@lem5772683 A B)). Qed.
Lemma lem5772700 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5772701 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem5772700 p q p' q'). Qed.
Lemma lem5772702 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem5772701 p q p'). Qed.
Lemma lem5772703 {A B : Type'} (op : type1400 B) : term77 A B op.
Proof. exact (@lem5772702 (@monoidal B op) (term66 A B op)). Qed.
Lemma lem5772704 {A B : Type'} (op : type1400 B) (p' : Prop) : term78 A B op p'.
Proof. exact (@lem5772703 A B op p'). Qed.
Lemma lem5772705 {A B : Type'} (op : type1400 B) (p' : Prop) : (term78 A B op p') = (term79 A B op p').
Proof. exact (eq_refl (term78 A B op p')). Qed.
Lemma lem5772706 {A B : Type'} (op : type1400 B) (p' : Prop) : term79 A B op p'.
Proof. exact (EQ_MP (@lem5772705 A B op p') (@lem5772704 A B op p')). Qed.
Lemma lem5772707 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term80 A B op p' q'.
Proof. exact (@lem5772706 A B op p' q'). Qed.
Lemma lem5772708 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : (term80 A B op p' q') = (term81 A B op p' q').
Proof. exact (eq_refl (term80 A B op p' q')). Qed.
Lemma lem5772709 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term81 A B op p' q'.
Proof. exact (EQ_MP (@lem5772708 A B op p' q') (@lem5772707 A B op p' q')). Qed.
Lemma lem5772716 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5772717 {A B : Type'} (op : type1400 B) (q' : Prop) : term82 A B op q'.
Proof. exact (@lem5772709 A B op (@monoidal B op) q'). Qed.
Lemma lem5772718 {A B : Type'} (op : type1400 B) (q' : Prop) : term83 A B op q'.
Proof. exact (@lem5772717 A B op q' (@lem5772716 B op)). Qed.
Lemma lem5772719 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5772720 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5772757 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5772758 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem5772757 p q p' q'). Qed.
Lemma lem5772759 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem5772758 p q p'). Qed.
Lemma lem5772760 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term84 A B t op s f.
Proof. exact (@lem5772759 (term85 A B t op f s) ((term49 A B s op t f) = (term44 A B op s f))). Qed.
Lemma lem5772761 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) : term86 A B t op s f p'.
Proof. exact (@lem5772760 A B t op s f p'). Qed.
Lemma lem5772762 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term86 A B t op s f p') = (term87 A B t op s f p').
Proof. exact (eq_refl (term86 A B t op s f p')). Qed.
Lemma lem5772763 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) : term87 A B t op s f p'.
Proof. exact (EQ_MP (@lem5772762 A B t op s f p') (@lem5772761 A B t op s f p')). Qed.
Lemma lem5772764 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term88 A B t op s f p' q'.
Proof. exact (@lem5772763 A B t op s f p' q'). Qed.
Lemma lem5772765 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term88 A B t op s f p' q') = (term89 A B t op s f p' q').
Proof. exact (eq_refl (term88 A B t op s f p' q')). Qed.
Lemma lem5772766 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term89 A B t op s f p' q'.
Proof. exact (EQ_MP (@lem5772765 A B t op s f p' q') (@lem5772764 A B t op s f p' q')). Qed.
Lemma lem5772827 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term85 A B t op f s) = (term85 A B t op f s).
Proof. exact (eq_refl (term85 A B t op f s)). Qed.
Lemma lem5772828 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (q' : Prop) : term90 A B t op f s q'.
Proof. exact (@lem5772766 A B t op s f (term85 A B t op f s) q'). Qed.
Lemma lem5772829 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (q' : Prop) : term91 A B t op f s q'.
Proof. exact (@lem5772828 A B t op f s q' (@lem5772827 A B t op f s)). Qed.
Lemma lem5772830 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : term85 A B t op f s.
Proof. exact (h1). Qed.
Lemma lem5772831 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : term92 A B t op f s.
Proof. exact (proj2 (@lem5772830 A B t op f s h1)). Qed.
Lemma lem5772832 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term92 A B t op f s) = ((term92 A B t op f s) = True).
Proof. exact (@lem7 (term92 A B t op f s)). Qed.
Lemma lem5772834 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : term93 A B op f s.
Proof. exact (proj1 (@lem5772830 A B t op f s h1)). Qed.
Lemma lem5772835 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term93 A B op f s) = ((term93 A B op f s) = True).
Proof. exact (@lem7 (term93 A B op f s)). Qed.
Lemma lem5772862 {_120158 _120196 : Type'} (s : _120158 -> Prop) (op : type1400 _120196) (f : _120158 -> _120196) (t : _120158 -> Prop) : (term26 _120158 _120196 op f s t) = (term27 _120158 _120196 s op f t).
Proof. exact (EQ_MP (@lem5772554 _120158 _120196 s op f t) (@lem5772553 _120158 _120196 s op f t)). Qed.
Lemma lem5772863 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term26 A B op f s t) = (term27 A B s op f t).
Proof. exact (@lem5772862 A B s op f t). Qed.
Lemma lem5772898 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5772899 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term94 A B op f s t) = (term95 A B s op f t).
Proof. exact (MK_COMB (@lem5772898 A B op) (@lem5772863 A B s op f t)). Qed.
Lemma lem5772944 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5772945 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term46 A B op s t f) = (term96 A B s op t f).
Proof. exact (MK_COMB (@lem5772899 A B s op f t) (@lem5772944 A B f)). Qed.
Lemma lem5772992 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5772993 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term48 A B op s t f) = (term97 A B s op t f).
Proof. exact (MK_COMB (@lem5772992 B op) (@lem5772945 A B s op t f)). Qed.
Lemma lem5773070 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term44 A B op t f) = (term44 A B op t f).
Proof. exact (eq_refl (term44 A B op t f)). Qed.
Lemma lem5773071 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term49 A B s op t f) = (term98 A B s op t f).
Proof. exact (MK_COMB (@lem5772993 A B s op t f) (@lem5773070 A B op t f)). Qed.
Lemma lem5773073 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term14 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem5772529 _120745 _120749 t op s f) (@lem5772522 _120745 _120749 t op s f)). Qed.
Lemma lem5773074 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term14 A B t op s f.
Proof. exact (@lem5773073 A B t op s f). Qed.
Lemma lem5773075 {A B : Type'} (t : A -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term99 A B t op s f.
Proof. exact (@lem5773074 A B (@support A B op f t) op (@support A B op f s) f). Qed.
Lemma lem5773085 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5772720 B op) (@lem5772719 B op h1)). Qed.
Lemma lem5773088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773089 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term100 B op) = (and True).
Proof. exact (MK_COMB (@lem5773088) (@lem5773085 B op h1)). Qed.
Lemma lem5773105 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : (term93 A B op f s) = True.
Proof. exact (EQ_MP (@lem5772835 A B op f s) (@lem5772834 A B t op f s h1)). Qed.
Lemma lem5773108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5773109 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : (term101 A B op f s) = (and True).
Proof. exact (MK_COMB (@lem5773108) (@lem5773105 A B t op f s h1)). Qed.
Lemma lem5773117 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : (term92 A B t op f s) = True.
Proof. exact (EQ_MP (@lem5772832 A B t op f s) (@lem5772831 A B t op f s h1)). Qed.
Lemma lem5773120 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : (term85 A B t op f s) = (True /\ True).
Proof. exact (MK_COMB (@lem5773109 A B t op f s h1) (@lem5773117 A B t op f s h1)). Qed.
Lemma lem5773122 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5773123 : (True /\ True) = True.
Proof. exact (@lem5773122 True). Qed.
Lemma lem5773126 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term85 A B t op f s) : (term85 A B t op f s) = True.
Proof. exact (TRANS (@lem5773120 A B t op f s h1) (@lem5773123)). Qed.
Lemma lem5773127 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : (term102 A B t op f s) = (True /\ True).
Proof. exact (MK_COMB (@lem5773089 B op h1) (@lem5773126 A B t op f s h2)). Qed.
Lemma lem5773129 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5773130 : (True /\ True) = True.
Proof. exact (@lem5773129 True). Qed.
Lemma lem5773133 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : (term102 A B t op f s) = True.
Proof. exact (TRANS (@lem5773127 A B t op f s h1 h2) (@lem5773130)). Qed.
Lemma lem5773134 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : True = (term102 A B t op f s).
Proof. exact (SYM (@lem5773133 A B t op f s h1 h2)). Qed.
Lemma lem5773135 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : term102 A B t op f s.
Proof. exact (EQ_MP (@lem5773134 A B t op f s h1 h2) (@lem0)). Qed.
Lemma lem5773136 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : (term98 A B s op t f) = (term44 A B op s f).
Proof. exact (@lem5773075 A B t op s f (@lem5773135 A B t op f s h1 h2)). Qed.
Lemma lem5773163 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : (term49 A B s op t f) = (term44 A B op s f).
Proof. exact (TRANS (@lem5773071 A B s op t f) (@lem5773136 A B t op f s h1 h2)). Qed.
Lemma lem5773164 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5773165 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : (term51 A B s op t f) = (term103 A B op s f).
Proof. exact (MK_COMB (@lem5773164 B) (@lem5773163 A B t op f s h1 h2)). Qed.
Lemma lem5773222 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term44 A B op s f) = (term44 A B op s f).
Proof. exact (eq_refl (term44 A B op s f)). Qed.
Lemma lem5773223 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : ((term49 A B s op t f) = (term44 A B op s f)) = ((term44 A B op s f) = (term44 A B op s f)).
Proof. exact (MK_COMB (@lem5773165 A B t op f s h1 h2) (@lem5773222 A B op s f)). Qed.
Lemma lem5773225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5773226 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5773225 B x). Qed.
Lemma lem5773227 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : ((term44 A B op s f) = (term44 A B op s f)) = True.
Proof. exact (@lem5773226 B (term44 A B op s f)). Qed.
Lemma lem5773230 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term85 A B t op f s) : ((term49 A B s op t f) = (term44 A B op s f)) = True.
Proof. exact (TRANS (@lem5773223 A B t op f s h1 h2) (@lem5773227 A B op s f)). Qed.
Lemma lem5773231 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term104 A B t op s f.
Proof. exact (fun h0 : term85 A B t op f s => @lem5773230 A B t op f s h1 h0). Qed.
Lemma lem5773232 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : term105 A B t op f s.
Proof. exact (@lem5772829 A B t op f s True). Qed.
Lemma lem5773233 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : (term54 A B t op s f) = (term106 A B t op f s).
Proof. exact (@lem5773232 A B t op f s (@lem5773231 A B t s f op h1)). Qed.
Lemma lem5773235 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5773236 {A B : Type'} (t : A -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term106 A B t op f s) = True.
Proof. exact (@lem5773235 (term85 A B t op f s)). Qed.
Lemma lem5773239 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term54 A B t op s f) = True.
Proof. exact (TRANS (@lem5773233 A B t f s op h1) (@lem5773236 A B t op f s)). Qed.
Lemma lem5773240 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term56 A B op s f) = (term107 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5773239 A B t s f op h1)). Qed.
Lemma lem5773245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5773246 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term58 A B op s f) = (term108 A).
Proof. exact (MK_COMB (@lem5773245 A) (@lem5773240 A B s f op h1)). Qed.
Lemma lem5773248 {A : Type'} (t : Prop) : (term109 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5773249 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem5773248 (A -> Prop) t). Qed.
Lemma lem5773250 {A : Type'} : (term108 A) = True.
Proof. exact (@lem5773249 A True). Qed.
Lemma lem5773253 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term58 A B op s f) = True.
Proof. exact (TRANS (@lem5773246 A B s f op h1) (@lem5773250 A)). Qed.
Lemma lem5773254 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term60 A B op f) = (term107 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5773253 A B s f op h1)). Qed.
Lemma lem5773259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5773260 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term62 A B op f) = (term108 A).
Proof. exact (MK_COMB (@lem5773259 A) (@lem5773254 A B f op h1)). Qed.
Lemma lem5773262 {A : Type'} (t : Prop) : (term109 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5773263 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem5773262 (A -> Prop) t). Qed.
Lemma lem5773264 {A : Type'} : (term108 A) = True.
Proof. exact (@lem5773263 A True). Qed.
Lemma lem5773267 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term62 A B op f) = True.
Proof. exact (TRANS (@lem5773260 A B f op h1) (@lem5773264 A)). Qed.
Lemma lem5773268 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term64 A B op) = (term111 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5773267 A B f op h1)). Qed.
Lemma lem5773273 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5773274 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term66 A B op) = (term112 A B).
Proof. exact (MK_COMB (@lem5773273 A B) (@lem5773268 A B op h1)). Qed.
Lemma lem5773276 {A : Type'} (t : Prop) : (term109 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5773277 {A B : Type'} (t : Prop) : (term113 A B t) = t.
Proof. exact (@lem5773276 (A -> B) t). Qed.
Lemma lem5773278 {A B : Type'} : (term112 A B) = True.
Proof. exact (@lem5773277 A B True). Qed.
Lemma lem5773281 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term66 A B op) = True.
Proof. exact (TRANS (@lem5773274 A B op h1) (@lem5773278 A B)). Qed.
Lemma lem5773282 {A B : Type'} (op : type1400 B) : term114 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5773281 A B op h0). Qed.
Lemma lem5773283 {A B : Type'} (op : type1400 B) : term115 A B op.
Proof. exact (@lem5772718 A B op True). Qed.
Lemma lem5773284 {A B : Type'} (op : type1400 B) : (term69 A B op) = (term116 B op).
Proof. exact (@lem5773283 A B op (@lem5773282 A B op)). Qed.
Lemma lem5773286 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5773287 {B : Type'} (op : type1400 B) : (term116 B op) = True.
Proof. exact (@lem5773286 (@monoidal B op)). Qed.
Lemma lem5773290 {A B : Type'} (op : type1400 B) : (term69 A B op) = True.
Proof. exact (TRANS (@lem5773284 A B op) (@lem5773287 B op)). Qed.
Lemma lem5773291 {A B : Type'} : (term71 A B) = (term117 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5773290 A B op)). Qed.
Lemma lem5773296 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5773297 {A B : Type'} : (term73 A B) = (term118 B).
Proof. exact (MK_COMB (@lem5773296 B) (@lem5773291 A B)). Qed.
Lemma lem5773299 {A : Type'} (t : Prop) : (term109 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5773300 {B : Type'} (t : Prop) : (term119 B t) = t.
Proof. exact (@lem5773299 (type1400 B) t). Qed.
Lemma lem5773301 {B : Type'} : (term118 B) = True.
Proof. exact (@lem5773300 B True). Qed.
Lemma lem5773304 {A B : Type'} : (term73 A B) = True.
Proof. exact (TRANS (@lem5773297 A B) (@lem5773301 B)). Qed.
Lemma lem5773305 {A B : Type'} : True = (term73 A B).
Proof. exact (SYM (@lem5773304 A B)). Qed.
Lemma lem5773306 {A B : Type'} : term73 A B.
Proof. exact (EQ_MP (@lem5773305 A B) (@lem0)). Qed.
Lemma lem5773307 {A B : Type'} : term72 A B.
Proof. exact (EQ_MP (@lem5772684 A B) (@lem5773306 A B)). Qed.
