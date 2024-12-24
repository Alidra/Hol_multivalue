Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_ELIM_PAIR_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import PAIR_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm69_spec.
Lemma lem3400535 {_83064 : Type'} : term0 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3400536 {_83064 : Type'} (P : type919 _83064) : term1 _83064 P.
Proof. exact (@lem3400535 _83064 P). Qed.
Lemma lem3400537 {_83064 : Type'} (P : type919 _83064) : (term1 _83064 P) = (term2 _83064 P).
Proof. exact (eq_refl (term1 _83064 P)). Qed.
Lemma lem3400538 {_83064 : Type'} (P : type919 _83064) : term2 _83064 P.
Proof. exact (EQ_MP (@lem3400537 _83064 P) (@lem3400536 _83064 P)). Qed.
Lemma lem3400539 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term3 _83064 P x.
Proof. exact (@lem3400538 _83064 P x). Qed.
Lemma lem3400540 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term3 _83064 P x) = ((term4 _83064 x P) = (term5 _83064 P x)).
Proof. exact (eq_refl (term3 _83064 P x)). Qed.
Lemma lem3400557 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term4 _83064 x P) = (term5 _83064 P x).
Proof. exact (EQ_MP (@lem3400540 _83064 P x) (@lem3400539 _83064 P x)). Qed.
Lemma lem3400558 {_88435 _88436 : Type'} (P : type916 _88435 _88436) (x : prod _88436 _88435) : (term6 _88435 _88436 x P) = (term7 _88435 _88436 P x).
Proof. exact (@lem3400557 (prod _88436 _88435) P x). Qed.
Lemma lem3400559 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term8 _88435 _88436 a b P) = (term9 _88435 _88436 P a b).
Proof. exact (@lem3400558 _88435 _88436 (term10 _88435 _88436 P) (@pair _88436 _88435 a b)). Qed.
Lemma lem3400560 {_88435 _88436 : Type'} (GEN_PVAR_31 : prod _88436 _88435) (P : type1470 _88435 _88436) : (term11 _88435 _88436 P GEN_PVAR_31) = (term12 _88435 _88436 GEN_PVAR_31 P).
Proof. exact (eq_refl (term11 _88435 _88436 P GEN_PVAR_31)). Qed.
Lemma lem3400561 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term13 _88435 _88436 P) = (term14 _88435 _88436 P).
Proof. exact (fun_ext (fun GEN_PVAR_31 : prod _88436 _88435 => @lem3400560 _88435 _88436 GEN_PVAR_31 P)). Qed.
Lemma lem3400562 {_88435 _88436 : Type'} : (@GSPEC (prod _88436 _88435)) = (@GSPEC (prod _88436 _88435)).
Proof. exact (eq_refl (@GSPEC (prod _88436 _88435))). Qed.
Lemma lem3400563 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term15 _88435 _88436 P) = (term16 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3400562 _88435 _88436) (@lem3400561 _88435 _88436 P)). Qed.
Lemma lem3400564 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (term17 _88435 _88436 a b) = (term17 _88435 _88436 a b).
Proof. exact (eq_refl (term17 _88435 _88436 a b)). Qed.
Lemma lem3400565 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) : (term8 _88435 _88436 a b P) = (term18 _88435 _88436 a b P).
Proof. exact (MK_COMB (@lem3400564 _88435 _88436 a b) (@lem3400563 _88435 _88436 P)). Qed.
Lemma lem3400566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400567 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) : (term19 _88435 _88436 a b P) = (term20 _88435 _88436 a b P).
Proof. exact (MK_COMB (@lem3400566) (@lem3400565 _88435 _88436 a b P)). Qed.
Lemma lem3400568 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) : (term9 _88435 _88436 P a b) = (term21 _88435 _88436 a b P).
Proof. exact (eq_refl (term9 _88435 _88436 P a b)). Qed.
Lemma lem3400569 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) : ((term8 _88435 _88436 a b P) = (term9 _88435 _88436 P a b)) = ((term18 _88435 _88436 a b P) = (term21 _88435 _88436 a b P)).
Proof. exact (MK_COMB (@lem3400567 _88435 _88436 a b P) (@lem3400568 _88435 _88436 a b P)). Qed.
Lemma lem3400570 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) : (term18 _88435 _88436 a b P) = (term21 _88435 _88436 a b P).
Proof. exact (EQ_MP (@lem3400569 _88435 _88436 a b P) (@lem3400559 _88435 _88436 P a b)). Qed.
Lemma lem3400580 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3400581 {_88435 _88436 : Type'} (f : type1534 _88435 _88436) (y : Prop) : (term23 _88435 _88436 f y) = (f y).
Proof. exact (@lem3400580 Prop (type1223 _88435 _88436) f y). Qed.
Lemma lem3400582 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) (x : _88436) (y : _88435) : (term24 _88435 _88436 a b P x y) = (term25 _88435 _88436 a b P x y).
Proof. exact (@lem3400581 _88435 _88436 (term26 _88435 _88436 a b) (P x y)). Qed.
Lemma lem3400583 {_88435 _88436 : Type'} (p : Prop) (a : _88436) (b : _88435) : (term27 _88435 _88436 a b p) = (term28 _88435 _88436 p a b).
Proof. exact (eq_refl (term27 _88435 _88436 a b p)). Qed.
Lemma lem3400584 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (term29 _88435 _88436 a b) = (term26 _88435 _88436 a b).
Proof. exact (fun_ext (fun p : Prop => @lem3400583 _88435 _88436 p a b)). Qed.
Lemma lem3400585 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3400586 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) (x : _88436) (y : _88435) : (term24 _88435 _88436 a b P x y) = (term25 _88435 _88436 a b P x y).
Proof. exact (MK_COMB (@lem3400584 _88435 _88436 a b) (@lem3400585 _88435 _88436 P x y)). Qed.
Lemma lem3400587 {_88435 _88436 : Type'} : (@eq ((prod _88436 _88435) -> Prop)) = (@eq ((prod _88436 _88435) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _88436 _88435) -> Prop))). Qed.
Lemma lem3400588 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (P : type1470 _88435 _88436) (x : _88436) (y : _88435) : (term30 _88435 _88436 a b P x y) = (term31 _88435 _88436 a b P x y).
Proof. exact (MK_COMB (@lem3400587 _88435 _88436) (@lem3400586 _88435 _88436 a b P x y)). Qed.
Lemma lem3400589 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term25 _88435 _88436 a b P x y) = (term32 _88435 _88436 P x y a b).
Proof. exact (eq_refl (term25 _88435 _88436 a b P x y)). Qed.
Lemma lem3400590 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) (a : _88436) (b : _88435) : ((term24 _88435 _88436 a b P x y) = (term25 _88435 _88436 a b P x y)) = ((term25 _88435 _88436 a b P x y) = (term32 _88435 _88436 P x y a b)).
Proof. exact (MK_COMB (@lem3400588 _88435 _88436 a b P x y) (@lem3400589 _88435 _88436 P x y a b)). Qed.
Lemma lem3400591 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term25 _88435 _88436 a b P x y) = (term32 _88435 _88436 P x y a b).
Proof. exact (EQ_MP (@lem3400590 _88435 _88436 P x y a b) (@lem3400582 _88435 _88436 a b P x y)). Qed.
Lemma lem3400596 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 x y).
Proof. exact (eq_refl (@pair _88436 _88435 x y)). Qed.
Lemma lem3400597 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term33 _88435 _88436 a b P x y) = (term34 _88435 _88436 P a b x y).
Proof. exact (MK_COMB (@lem3400591 _88435 _88436 P x y a b) (@lem3400596 _88435 _88436 x y)). Qed.
Lemma lem3400599 {A B : Type'} (f : A -> B) (y : A) : (term22 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3400600 {_88435 _88436 : Type'} (f : type1223 _88435 _88436) (y : prod _88436 _88435) : (term35 _88435 _88436 f y) = (f y).
Proof. exact (@lem3400599 (prod _88436 _88435) Prop f y). Qed.
Lemma lem3400601 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term36 _88435 _88436 P a b x y) = (term34 _88435 _88436 P a b x y).
Proof. exact (@lem3400600 _88435 _88436 (term32 _88435 _88436 P x y a b) (@pair _88436 _88435 x y)). Qed.
Lemma lem3400602 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) (a : _88436) (b : _88435) (t : prod _88436 _88435) : (term37 _88435 _88436 P x y a b t) = (term38 _88435 _88436 P x y a b t).
Proof. exact (eq_refl (term37 _88435 _88436 P x y a b t)). Qed.
Lemma lem3400603 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term39 _88435 _88436 P x y a b) = (term32 _88435 _88436 P x y a b).
Proof. exact (fun_ext (fun t : prod _88436 _88435 => @lem3400602 _88435 _88436 P x y a b t)). Qed.
Lemma lem3400604 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 x y).
Proof. exact (eq_refl (@pair _88436 _88435 x y)). Qed.
Lemma lem3400605 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term36 _88435 _88436 P a b x y) = (term34 _88435 _88436 P a b x y).
Proof. exact (MK_COMB (@lem3400603 _88435 _88436 P x y a b) (@lem3400604 _88435 _88436 x y)). Qed.
Lemma lem3400606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400607 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term40 _88435 _88436 P a b x y) = (term41 _88435 _88436 P a b x y).
Proof. exact (MK_COMB (@lem3400606) (@lem3400605 _88435 _88436 P a b x y)). Qed.
Lemma lem3400608 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term34 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term34 _88435 _88436 P a b x y)). Qed.
Lemma lem3400609 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : ((term36 _88435 _88436 P a b x y) = (term34 _88435 _88436 P a b x y)) = ((term34 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y)).
Proof. exact (MK_COMB (@lem3400607 _88435 _88436 P a b x y) (@lem3400608 _88435 _88436 P a b x y)). Qed.
Lemma lem3400610 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term34 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (EQ_MP (@lem3400609 _88435 _88436 P a b x y) (@lem3400601 _88435 _88436 P a b x y)). Qed.
Lemma lem3400615 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term33 _88435 _88436 a b P x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (TRANS (@lem3400597 _88435 _88436 P a b x y) (@lem3400610 _88435 _88436 P a b x y)). Qed.
Lemma lem3400616 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term43 _88435 _88436 a b P x) = (term44 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3400615 _88435 _88436 P a b x y)). Qed.
Lemma lem3400617 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3400618 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term45 _88435 _88436 a b P x) = (term46 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3400617 _88435) (@lem3400616 _88435 _88436 P a b x)). Qed.
Lemma lem3400623 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term47 _88435 _88436 a b P) = (term48 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3400618 _88435 _88436 P a b x)). Qed.
Lemma lem3400624 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3400625 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term21 _88435 _88436 a b P) = (term49 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3400624 _88436) (@lem3400623 _88435 _88436 P a b)). Qed.
Lemma lem3400630 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term18 _88435 _88436 a b P) = (term49 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3400570 _88435 _88436 a b P) (@lem3400625 _88435 _88436 P a b)). Qed.
Lemma lem3400631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400632 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term20 _88435 _88436 a b P) = (term50 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3400631) (@lem3400630 _88435 _88436 P a b)). Qed.
Lemma lem3400633 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem3400634 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term18 _88435 _88436 a b P) = (P a b)) = ((term49 _88435 _88436 P a b) = (P a b)).
Proof. exact (MK_COMB (@lem3400632 _88435 _88436 P a b) (@lem3400633 _88435 _88436 P a b)). Qed.
Lemma lem3400637 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term51 _88435 _88436 P a) = (term52 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3400634 _88435 _88436 P a b)). Qed.
Lemma lem3400638 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3400639 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term53 _88435 _88436 P a) = (term54 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3400638 _88435) (@lem3400637 _88435 _88436 P a)). Qed.
Lemma lem3400644 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term55 _88435 _88436 P) = (term56 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3400639 _88435 _88436 P a)). Qed.
Lemma lem3400645 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3400646 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term57 _88435 _88436 P) = (term58 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3400645 _88436) (@lem3400644 _88435 _88436 P)). Qed.
Lemma lem3400651 {_88435 _88436 : Type'} : (term59 _88435 _88436) = (term60 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3400646 _88435 _88436 P)). Qed.
Lemma lem3400652 {_88435 _88436 : Type'} : (@all (_88436 -> _88435 -> Prop)) = (@all (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@all (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3400653 {_88435 _88436 : Type'} : (term61 _88435 _88436) = (term62 _88435 _88436).
Proof. exact (MK_COMB (@lem3400652 _88435 _88436) (@lem3400651 _88435 _88436)). Qed.
Lemma lem3400658 {_88435 _88436 : Type'} : (term62 _88435 _88436) = (term61 _88435 _88436).
Proof. exact (SYM (@lem3400653 _88435 _88436)). Qed.
Lemma lem3400660 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3400661 {_88435 _88436 : Type'} : (term62 _88435 _88436) = (term64 _88435 _88436).
Proof. exact (@lem3400660 (term62 _88435 _88436)). Qed.
Lemma lem3400662 {_88435 _88436 : Type'} : (term64 _88435 _88436) = (term62 _88435 _88436).
Proof. exact (SYM (@lem3400661 _88435 _88436)). Qed.
Lemma lem3400663 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : term65 _88435 _88436.
Proof. exact (h1). Qed.
Lemma lem3400664 {_88435 _88436 : Type'} : term66 _88435 _88436.
Proof. exact (@lem47438 _88436 _88435). Qed.
Lemma lem3400666 {_88435 _88436 B : Type'} : term67 _88435 _88436 B.
Proof. exact (@lem47438 (prod _88436 _88435) B). Qed.
Lemma lem3400667 {_88435 _88436 A : Type'} : term68 _88435 _88436 A.
Proof. exact (@lem47438 A (prod _88436 _88435)). Qed.
Lemma lem3400670 {_88435 _88436 A B : Type'} (h1 : term69 _88435 _88436 A B) : term69 _88435 _88436 A B.
Proof. exact (h1). Qed.
Lemma lem3400671 {_88435 _88436 A B : Type'} : term70 _88435 _88436 A B.
Proof. exact (fun h0 : term69 _88435 _88436 A B => @lem3400670 _88435 _88436 A B h0). Qed.
Lemma lem3400672 {_88435 _88436 A B : Type'} (h1 : term70 _88435 _88436 A B) : term70 _88435 _88436 A B.
Proof. exact (h1). Qed.
Lemma lem3400673 {_88435 _88436 A B : Type'} (h1 : term69 _88435 _88436 A B) : term69 _88435 _88436 A B.
Proof. exact (h1). Qed.
Lemma lem3400674 {_88435 _88436 A B : Type'} (h1 : term69 _88435 _88436 A B) (h2 : term70 _88435 _88436 A B) : term69 _88435 _88436 A B.
Proof. exact (@lem3400672 _88435 _88436 A B h2 (@lem3400673 _88435 _88436 A B h1)). Qed.
Lemma lem3400675 {_88435 _88436 A B : Type'} (h1 : term69 _88435 _88436 A B) : term71 _88435 _88436 A B.
Proof. exact (fun h0 : term70 _88435 _88436 A B => @lem3400674 _88435 _88436 A B h1 h0). Qed.
Lemma lem3400676 {_88435 _88436 A B : Type'} (h1 : term70 _88435 _88436 A B) : term70 _88435 _88436 A B.
Proof. exact (h1). Qed.
Lemma lem3400677 {_88435 _88436 A B : Type'} (h1 : term69 _88435 _88436 A B) (h2 : term70 _88435 _88436 A B) : term69 _88435 _88436 A B.
Proof. exact (@lem3400675 _88435 _88436 A B h1 (@lem3400676 _88435 _88436 A B h2)). Qed.
Lemma lem3400678 {_88435 _88436 A B : Type'} (h1 : term70 _88435 _88436 A B) : term70 _88435 _88436 A B.
Proof. exact (fun h0 : term69 _88435 _88436 A B => @lem3400677 _88435 _88436 A B h0 h1). Qed.
Lemma lem3400679 {_88435 _88436 A B : Type'} : term72 _88435 _88436 A B.
Proof. exact (fun h0 : term70 _88435 _88436 A B => @lem3400678 _88435 _88436 A B h0). Qed.
Lemma lem3400682 {_88435 _88436 A B : Type'} : term70 _88435 _88436 A B.
Proof. exact (@lem3400679 _88435 _88436 A B (@lem3400671 _88435 _88436 A B)). Qed.
Lemma lem3400683 {_88435 _88436 A B : Type'} : term70 _88435 _88436 A B.
Proof. exact (@lem3400682 _88435 _88436 A B). Qed.
Lemma lem3400793 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3400794 {_88435 _88436 B : Type'} : (term73 _88435 _88436 B) = (term74 _88435 _88436 B).
Proof. exact (@lem3400793 (term67 _88435 _88436 B)). Qed.
Lemma lem3400813 {_88435 _88436 A : Type'} : (term75 _88435 _88436 A) = (term75 _88435 _88436 A).
Proof. exact (eq_refl (term75 _88435 _88436 A)). Qed.
Lemma lem3400814 {_88435 _88436 A B : Type'} : (term76 _88435 _88436 A B) = (term77 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400813 _88435 _88436 A) (@lem3400794 _88435 _88436 B)). Qed.
Lemma lem3400817 {_88435 _88436 : Type'} : (term78 _88435 _88436) = (term78 _88435 _88436).
Proof. exact (eq_refl (term78 _88435 _88436)). Qed.
Lemma lem3400818 {_88435 _88436 A B : Type'} : (term79 _88435 _88436 A B) = (term80 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400817 _88435 _88436) (@lem3400814 _88435 _88436 A B)). Qed.
Lemma lem3400821 {_88435 _88436 : Type'} : (term81 _88435 _88436) = (term81 _88435 _88436).
Proof. exact (eq_refl (term81 _88435 _88436)). Qed.
Lemma lem3400828 {_88435 _88436 A B : Type'} : (term69 _88435 _88436 A B) = (term82 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400821 _88435 _88436) (@lem3400818 _88435 _88436 A B)). Qed.
Lemma lem3400837 {_88435 _88436 B : Type'} (x : prod _88436 _88435) (a : prod _88436 _88435) (y : B) (b : B) : (((@pair (prod _88436 _88435) B x y) = (@pair (prod _88436 _88435) B a b)) = (term83 _88435 _88436 B x a y b)) = (((@pair (prod _88436 _88435) B x y) = (@pair (prod _88436 _88435) B a b)) = (term83 _88435 _88436 B x a y b)).
Proof. exact (eq_refl (((@pair (prod _88436 _88435) B x y) = (@pair (prod _88436 _88435) B a b)) = (term83 _88435 _88436 B x a y b))). Qed.
Lemma lem3400838 {_88435 _88436 B : Type'} (x : prod _88436 _88435) (a : prod _88436 _88435) (y : B) : (term84 _88435 _88436 B x a y) = (term84 _88435 _88436 B x a y).
Proof. exact (fun_ext (fun b : B => @lem3400837 _88435 _88436 B x a y b)). Qed.
Lemma lem3400839 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3400840 {_88435 _88436 B : Type'} (x : prod _88436 _88435) (a : prod _88436 _88435) (y : B) : (term85 _88435 _88436 B x a y) = (term85 _88435 _88436 B x a y).
Proof. exact (MK_COMB (@lem3400839 B) (@lem3400838 _88435 _88436 B x a y)). Qed.
Lemma lem3400841 {_88435 _88436 B : Type'} (x : prod _88436 _88435) (y : B) : (term86 _88435 _88436 B x y) = (term86 _88435 _88436 B x y).
Proof. exact (fun_ext (fun a : prod _88436 _88435 => @lem3400840 _88435 _88436 B x a y)). Qed.
Lemma lem3400842 {_88435 _88436 : Type'} : (@all (prod _88436 _88435)) = (@all (prod _88436 _88435)).
Proof. exact (eq_refl (@all (prod _88436 _88435))). Qed.
Lemma lem3400843 {_88435 _88436 B : Type'} (x : prod _88436 _88435) (y : B) : (term87 _88435 _88436 B x y) = (term87 _88435 _88436 B x y).
Proof. exact (MK_COMB (@lem3400842 _88435 _88436) (@lem3400841 _88435 _88436 B x y)). Qed.
Lemma lem3400844 {_88435 _88436 B : Type'} (x : prod _88436 _88435) : (term88 _88435 _88436 B x) = (term88 _88435 _88436 B x).
Proof. exact (fun_ext (fun y : B => @lem3400843 _88435 _88436 B x y)). Qed.
Lemma lem3400845 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3400846 {_88435 _88436 B : Type'} (x : prod _88436 _88435) : (term89 _88435 _88436 B x) = (term89 _88435 _88436 B x).
Proof. exact (MK_COMB (@lem3400845 B) (@lem3400844 _88435 _88436 B x)). Qed.
Lemma lem3400847 {_88435 _88436 B : Type'} : (term90 _88435 _88436 B) = (term90 _88435 _88436 B).
Proof. exact (fun_ext (fun x : prod _88436 _88435 => @lem3400846 _88435 _88436 B x)). Qed.
Lemma lem3400848 {_88435 _88436 : Type'} : (@all (prod _88436 _88435)) = (@all (prod _88436 _88435)).
Proof. exact (eq_refl (@all (prod _88436 _88435))). Qed.
Lemma lem3400849 {_88435 _88436 B : Type'} : (term67 _88435 _88436 B) = (term67 _88435 _88436 B).
Proof. exact (MK_COMB (@lem3400848 _88435 _88436) (@lem3400847 _88435 _88436 B)). Qed.
Lemma lem3400850 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3400851 {_88435 _88436 B : Type'} : (term74 _88435 _88436 B) = (term74 _88435 _88436 B).
Proof. exact (MK_COMB (@lem3400850) (@lem3400849 _88435 _88436 B)). Qed.
Lemma lem3400860 {_88435 _88436 A : Type'} (x : A) (a : A) (y : prod _88436 _88435) (b : prod _88436 _88435) : (((@pair A (prod _88436 _88435) x y) = (@pair A (prod _88436 _88435) a b)) = (term91 _88435 _88436 A x a y b)) = (((@pair A (prod _88436 _88435) x y) = (@pair A (prod _88436 _88435) a b)) = (term91 _88435 _88436 A x a y b)).
Proof. exact (eq_refl (((@pair A (prod _88436 _88435) x y) = (@pair A (prod _88436 _88435) a b)) = (term91 _88435 _88436 A x a y b))). Qed.
Lemma lem3400861 {_88435 _88436 A : Type'} (x : A) (a : A) (y : prod _88436 _88435) : (term92 _88435 _88436 A x a y) = (term92 _88435 _88436 A x a y).
Proof. exact (fun_ext (fun b : prod _88436 _88435 => @lem3400860 _88435 _88436 A x a y b)). Qed.
Lemma lem3400862 {_88435 _88436 : Type'} : (@all (prod _88436 _88435)) = (@all (prod _88436 _88435)).
Proof. exact (eq_refl (@all (prod _88436 _88435))). Qed.
Lemma lem3400863 {_88435 _88436 A : Type'} (x : A) (a : A) (y : prod _88436 _88435) : (term93 _88435 _88436 A x a y) = (term93 _88435 _88436 A x a y).
Proof. exact (MK_COMB (@lem3400862 _88435 _88436) (@lem3400861 _88435 _88436 A x a y)). Qed.
Lemma lem3400864 {_88435 _88436 A : Type'} (x : A) (y : prod _88436 _88435) : (term94 _88435 _88436 A x y) = (term94 _88435 _88436 A x y).
Proof. exact (fun_ext (fun a : A => @lem3400863 _88435 _88436 A x a y)). Qed.
Lemma lem3400865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3400866 {_88435 _88436 A : Type'} (x : A) (y : prod _88436 _88435) : (term95 _88435 _88436 A x y) = (term95 _88435 _88436 A x y).
Proof. exact (MK_COMB (@lem3400865 A) (@lem3400864 _88435 _88436 A x y)). Qed.
Lemma lem3400867 {_88435 _88436 A : Type'} (x : A) : (term96 _88435 _88436 A x) = (term96 _88435 _88436 A x).
Proof. exact (fun_ext (fun y : prod _88436 _88435 => @lem3400866 _88435 _88436 A x y)). Qed.
Lemma lem3400868 {_88435 _88436 : Type'} : (@all (prod _88436 _88435)) = (@all (prod _88436 _88435)).
Proof. exact (eq_refl (@all (prod _88436 _88435))). Qed.
Lemma lem3400869 {_88435 _88436 A : Type'} (x : A) : (term97 _88435 _88436 A x) = (term97 _88435 _88436 A x).
Proof. exact (MK_COMB (@lem3400868 _88435 _88436) (@lem3400867 _88435 _88436 A x)). Qed.
Lemma lem3400870 {_88435 _88436 A : Type'} : (term98 _88435 _88436 A) = (term98 _88435 _88436 A).
Proof. exact (fun_ext (fun x : A => @lem3400869 _88435 _88436 A x)). Qed.
Lemma lem3400871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3400872 {_88435 _88436 A : Type'} : (term68 _88435 _88436 A) = (term68 _88435 _88436 A).
Proof. exact (MK_COMB (@lem3400871 A) (@lem3400870 _88435 _88436 A)). Qed.
Lemma lem3400873 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3400874 {_88435 _88436 A : Type'} : (term75 _88435 _88436 A) = (term75 _88435 _88436 A).
Proof. exact (MK_COMB (@lem3400873) (@lem3400872 _88435 _88436 A)). Qed.
Lemma lem3400875 {_88435 _88436 A B : Type'} : (term77 _88435 _88436 A B) = (term77 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400874 _88435 _88436 A) (@lem3400851 _88435 _88436 B)). Qed.
Lemma lem3400884 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) = (term99 _88435 _88436 x a y b)) = (((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) = (term99 _88435 _88436 x a y b)).
Proof. exact (eq_refl (((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) = (term99 _88435 _88436 x a y b))). Qed.
Lemma lem3400885 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term100 _88435 _88436 x a y) = (term100 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3400884 _88435 _88436 x a y b)). Qed.
Lemma lem3400886 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3400887 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term101 _88435 _88436 x a y) = (term101 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3400886 _88435) (@lem3400885 _88435 _88436 x a y)). Qed.
Lemma lem3400888 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term102 _88435 _88436 x y) = (term102 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3400887 _88435 _88436 x a y)). Qed.
Lemma lem3400889 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3400890 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term103 _88435 _88436 x y) = (term103 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3400889 _88436) (@lem3400888 _88435 _88436 x y)). Qed.
Lemma lem3400891 {_88435 _88436 : Type'} (x : _88436) : (term104 _88435 _88436 x) = (term104 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3400890 _88435 _88436 x y)). Qed.
Lemma lem3400892 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3400893 {_88435 _88436 : Type'} (x : _88436) : (term105 _88435 _88436 x) = (term105 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3400892 _88435) (@lem3400891 _88435 _88436 x)). Qed.
Lemma lem3400894 {_88435 _88436 : Type'} : (term106 _88435 _88436) = (term106 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3400893 _88435 _88436 x)). Qed.
Lemma lem3400895 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3400896 {_88435 _88436 : Type'} : (term66 _88435 _88436) = (term66 _88435 _88436).
Proof. exact (MK_COMB (@lem3400895 _88436) (@lem3400894 _88435 _88436)). Qed.
Lemma lem3400897 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3400898 {_88435 _88436 : Type'} : (term78 _88435 _88436) = (term78 _88435 _88436).
Proof. exact (MK_COMB (@lem3400897) (@lem3400896 _88435 _88436)). Qed.
Lemma lem3400899 {_88435 _88436 A B : Type'} : (term80 _88435 _88436 A B) = (term80 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400898 _88435 _88436) (@lem3400875 _88435 _88436 A B)). Qed.
Lemma lem3400900 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem3400905 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term42 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term42 _88435 _88436 P a b x y)). Qed.
Lemma lem3400906 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term44 _88435 _88436 P a b x) = (term44 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3400905 _88435 _88436 P a b x y)). Qed.
Lemma lem3400907 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3400908 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term46 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3400907 _88435) (@lem3400906 _88435 _88436 P a b x)). Qed.
Lemma lem3400909 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term48 _88435 _88436 P a b) = (term48 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3400908 _88435 _88436 P a b x)). Qed.
Lemma lem3400910 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3400911 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term49 _88435 _88436 P a b) = (term49 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3400910 _88436) (@lem3400909 _88435 _88436 P a b)). Qed.
Lemma lem3400912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3400913 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term50 _88435 _88436 P a b) = (term50 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3400912) (@lem3400911 _88435 _88436 P a b)). Qed.
Lemma lem3400914 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term49 _88435 _88436 P a b) = (P a b)) = ((term49 _88435 _88436 P a b) = (P a b)).
Proof. exact (MK_COMB (@lem3400913 _88435 _88436 P a b) (@lem3400900 _88435 _88436 P a b)). Qed.
Lemma lem3400915 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term52 _88435 _88436 P a) = (term52 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3400914 _88435 _88436 P a b)). Qed.
Lemma lem3400916 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3400917 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term54 _88435 _88436 P a) = (term54 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3400916 _88435) (@lem3400915 _88435 _88436 P a)). Qed.
Lemma lem3400918 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term56 _88435 _88436 P) = (term56 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3400917 _88435 _88436 P a)). Qed.
Lemma lem3400919 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3400920 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term58 _88435 _88436 P) = (term58 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3400919 _88436) (@lem3400918 _88435 _88436 P)). Qed.
Lemma lem3400921 {_88435 _88436 : Type'} : (term60 _88435 _88436) = (term60 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3400920 _88435 _88436 P)). Qed.
Lemma lem3400922 {_88435 _88436 : Type'} : (@all (_88436 -> _88435 -> Prop)) = (@all (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@all (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3400923 {_88435 _88436 : Type'} : (term62 _88435 _88436) = (term62 _88435 _88436).
Proof. exact (MK_COMB (@lem3400922 _88435 _88436) (@lem3400921 _88435 _88436)). Qed.
Lemma lem3400924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3400925 {_88435 _88436 : Type'} : (term65 _88435 _88436) = (term65 _88435 _88436).
Proof. exact (MK_COMB (@lem3400924) (@lem3400923 _88435 _88436)). Qed.
Lemma lem3400926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3400927 {_88435 _88436 : Type'} : (term81 _88435 _88436) = (term81 _88435 _88436).
Proof. exact (MK_COMB (@lem3400926) (@lem3400925 _88435 _88436)). Qed.
Lemma lem3400928 {_88435 _88436 A B : Type'} : (term82 _88435 _88436 A B) = (term82 _88435 _88436 A B).
Proof. exact (MK_COMB (@lem3400927 _88435 _88436) (@lem3400899 _88435 _88436 A B)). Qed.
Lemma lem3401047 {_88435 _88436 A B : Type'} : (term69 _88435 _88436 A B) = (term82 _88435 _88436 A B).
Proof. exact (TRANS (@lem3400828 _88435 _88436 A B) (@lem3400928 _88435 _88436 A B)). Qed.
Lemma lem3401048 {_88435 _88436 A B : Type'} : (term82 _88435 _88436 A B) = (term69 _88435 _88436 A B).
Proof. exact (SYM (@lem3401047 _88435 _88436 A B)). Qed.
Lemma lem3401049 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : term65 _88435 _88436.
Proof. exact (h1). Qed.
Lemma lem3401050 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) : term66 _88435 _88436.
Proof. exact (h1). Qed.
Lemma lem3401061 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term107 _88435 _88436 P a b x y) = (term108 _88435 _88436 P a b x y).
Proof. exact (@lem17045 (P x y) ((@pair _88436 _88435 a b) = (@pair _88436 _88435 x y))). Qed.
Lemma lem3401064 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term42 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term42 _88435 _88436 P a b x y)). Qed.
Lemma lem3401065 {_88435 : Type'} (P : _88435 -> Prop) : (term109 _88435 P) = (term110 _88435 P).
Proof. exact (@lem18394 _88435 P). Qed.
Lemma lem3401066 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term111 _88435 _88436 P a b x) = (term112 _88435 _88436 P a b x).
Proof. exact (@lem3401065 _88435 (term44 _88435 _88436 P a b x)). Qed.
Lemma lem3401067 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term113 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term113 _88435 _88436 P a b x y)). Qed.
Lemma lem3401068 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3401069 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term114 _88435 _88436 P a b x y) = (term107 _88435 _88436 P a b x y).
Proof. exact (MK_COMB (@lem3401068) (@lem3401067 _88435 _88436 P a b x y)). Qed.
Lemma lem3401070 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term114 _88435 _88436 P a b x y) = (term108 _88435 _88436 P a b x y).
Proof. exact (TRANS (@lem3401069 _88435 _88436 P a b x y) (@lem3401061 _88435 _88436 P a b x y)). Qed.
Lemma lem3401071 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term115 _88435 _88436 P a b x) = (term116 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3401070 _88435 _88436 P a b x y)). Qed.
Lemma lem3401072 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3401073 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term112 _88435 _88436 P a b x) = (term117 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401072 _88435) (@lem3401071 _88435 _88436 P a b x)). Qed.
Lemma lem3401074 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term111 _88435 _88436 P a b x) = (term117 _88435 _88436 P a b x).
Proof. exact (TRANS (@lem3401066 _88435 _88436 P a b x) (@lem3401073 _88435 _88436 P a b x)). Qed.
Lemma lem3401075 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term44 _88435 _88436 P a b x) = (term44 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3401064 _88435 _88436 P a b x y)). Qed.
Lemma lem3401076 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401077 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term46 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401076 _88435) (@lem3401075 _88435 _88436 P a b x)). Qed.
Lemma lem3401078 {_88436 : Type'} (P : _88436 -> Prop) : (term109 _88436 P) = (term110 _88436 P).
Proof. exact (@lem18394 _88436 P). Qed.
Lemma lem3401079 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term118 _88435 _88436 P a b) = (term119 _88435 _88436 P a b).
Proof. exact (@lem3401078 _88436 (term48 _88435 _88436 P a b)). Qed.
Lemma lem3401080 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term120 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (eq_refl (term120 _88435 _88436 P a b x)). Qed.
Lemma lem3401081 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3401082 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term121 _88435 _88436 P a b x) = (term111 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401081) (@lem3401080 _88435 _88436 P a b x)). Qed.
Lemma lem3401083 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term121 _88435 _88436 P a b x) = (term117 _88435 _88436 P a b x).
Proof. exact (TRANS (@lem3401082 _88435 _88436 P a b x) (@lem3401074 _88435 _88436 P a b x)). Qed.
Lemma lem3401084 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term122 _88435 _88436 P a b) = (term123 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3401083 _88435 _88436 P a b x)). Qed.
Lemma lem3401085 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3401086 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term119 _88435 _88436 P a b) = (term124 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401085 _88436) (@lem3401084 _88435 _88436 P a b)). Qed.
Lemma lem3401087 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term118 _88435 _88436 P a b) = (term124 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3401079 _88435 _88436 P a b) (@lem3401086 _88435 _88436 P a b)). Qed.
Lemma lem3401088 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term48 _88435 _88436 P a b) = (term48 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3401077 _88435 _88436 P a b x)). Qed.
Lemma lem3401089 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401090 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term49 _88435 _88436 P a b) = (term49 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401089 _88436) (@lem3401088 _88435 _88436 P a b)). Qed.
Lemma lem3401091 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term125 _88435 _88436 P a b).
Proof. exact (eq_refl (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401092 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem3401093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401094 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term126 _88435 _88436 P a b) = (term127 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401093) (@lem3401087 _88435 _88436 P a b)). Qed.
Lemma lem3401095 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term128 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401094 _88435 _88436 P a b) (@lem3401092 _88435 _88436 P a b)). Qed.
Lemma lem3401096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401097 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term130 _88435 _88436 P a b) = (term130 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401096) (@lem3401090 _88435 _88436 P a b)). Qed.
Lemma lem3401098 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term131 _88435 _88436 P a b) = (term131 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401097 _88435 _88436 P a b) (@lem3401091 _88435 _88436 P a b)). Qed.
Lemma lem3401099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401100 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term132 _88435 _88436 P a b) = (term132 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401099) (@lem3401098 _88435 _88436 P a b)). Qed.
Lemma lem3401101 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term133 _88435 _88436 P a b) = (term134 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401100 _88435 _88436 P a b) (@lem3401095 _88435 _88436 P a b)). Qed.
Lemma lem3401102 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term135 _88435 _88436 P a b) = (term133 _88435 _88436 P a b).
Proof. exact (@lem17646 (term49 _88435 _88436 P a b) (P a b)). Qed.
Lemma lem3401103 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term135 _88435 _88436 P a b) = (term134 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3401102 _88435 _88436 P a b) (@lem3401101 _88435 _88436 P a b)). Qed.
Lemma lem3401104 {_88435 : Type'} (P : _88435 -> Prop) : (term136 _88435 P) = (term137 _88435 P).
Proof. exact (@lem18392 _88435 P). Qed.
Lemma lem3401105 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term138 _88435 _88436 P a) = (term139 _88435 _88436 P a).
Proof. exact (@lem3401104 _88435 (term52 _88435 _88436 P a)). Qed.
Lemma lem3401106 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term140 _88435 _88436 P a b) = ((term49 _88435 _88436 P a b) = (P a b)).
Proof. exact (eq_refl (term140 _88435 _88436 P a b)). Qed.
Lemma lem3401107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3401108 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term141 _88435 _88436 P a b) = (term135 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401107) (@lem3401106 _88435 _88436 P a b)). Qed.
Lemma lem3401109 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term141 _88435 _88436 P a b) = (term134 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3401108 _88435 _88436 P a b) (@lem3401103 _88435 _88436 P a b)). Qed.
Lemma lem3401110 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term142 _88435 _88436 P a) = (term143 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401109 _88435 _88436 P a b)). Qed.
Lemma lem3401111 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401112 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term139 _88435 _88436 P a) = (term144 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401111 _88435) (@lem3401110 _88435 _88436 P a)). Qed.
Lemma lem3401113 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term138 _88435 _88436 P a) = (term144 _88435 _88436 P a).
Proof. exact (TRANS (@lem3401105 _88435 _88436 P a) (@lem3401112 _88435 _88436 P a)). Qed.
Lemma lem3401114 {_88436 : Type'} (P : _88436 -> Prop) : (term136 _88436 P) = (term137 _88436 P).
Proof. exact (@lem18392 _88436 P). Qed.
Lemma lem3401115 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term145 _88435 _88436 P) = (term146 _88435 _88436 P).
Proof. exact (@lem3401114 _88436 (term56 _88435 _88436 P)). Qed.
Lemma lem3401116 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term147 _88435 _88436 P a) = (term54 _88435 _88436 P a).
Proof. exact (eq_refl (term147 _88435 _88436 P a)). Qed.
Lemma lem3401117 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3401118 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term148 _88435 _88436 P a) = (term138 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401117) (@lem3401116 _88435 _88436 P a)). Qed.
Lemma lem3401119 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term148 _88435 _88436 P a) = (term144 _88435 _88436 P a).
Proof. exact (TRANS (@lem3401118 _88435 _88436 P a) (@lem3401113 _88435 _88436 P a)). Qed.
Lemma lem3401120 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term149 _88435 _88436 P) = (term150 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401119 _88435 _88436 P a)). Qed.
Lemma lem3401121 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401122 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term146 _88435 _88436 P) = (term151 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401121 _88436) (@lem3401120 _88435 _88436 P)). Qed.
Lemma lem3401123 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term145 _88435 _88436 P) = (term151 _88435 _88436 P).
Proof. exact (TRANS (@lem3401115 _88435 _88436 P) (@lem3401122 _88435 _88436 P)). Qed.
Lemma lem3401124 {_88435 _88436 : Type'} (P : type745 _88435 _88436) : (term152 _88435 _88436 P) = (term153 _88435 _88436 P).
Proof. exact (@lem18392 (type1470 _88435 _88436) P). Qed.
Lemma lem3401125 {_88435 _88436 : Type'} : (term65 _88435 _88436) = (term154 _88435 _88436).
Proof. exact (@lem3401124 _88435 _88436 (term60 _88435 _88436)). Qed.
Lemma lem3401126 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term155 _88435 _88436 P) = (term58 _88435 _88436 P).
Proof. exact (eq_refl (term155 _88435 _88436 P)). Qed.
Lemma lem3401127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3401128 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term156 _88435 _88436 P) = (term145 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401127) (@lem3401126 _88435 _88436 P)). Qed.
Lemma lem3401129 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term156 _88435 _88436 P) = (term151 _88435 _88436 P).
Proof. exact (TRANS (@lem3401128 _88435 _88436 P) (@lem3401123 _88435 _88436 P)). Qed.
Lemma lem3401130 {_88435 _88436 : Type'} : (term157 _88435 _88436) = (term158 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401129 _88435 _88436 P)). Qed.
Lemma lem3401131 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401132 {_88435 _88436 : Type'} : (term154 _88435 _88436) = (term159 _88435 _88436).
Proof. exact (MK_COMB (@lem3401131 _88435 _88436) (@lem3401130 _88435 _88436)). Qed.
Lemma lem3401133 {_88435 _88436 : Type'} : (term65 _88435 _88436) = (term159 _88435 _88436).
Proof. exact (TRANS (@lem3401125 _88435 _88436) (@lem3401132 _88435 _88436)). Qed.
Lemma lem3401143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3401144 {_88435 : Type'} (P : _88435 -> Prop) (Q : _88435 -> Prop) : (term160 _88435 P Q) = (term161 _88435 P Q).
Proof. exact (@lem3401143 _88435 P Q). Qed.
Lemma lem3401145 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term162 _88435 _88436 P a) = (term163 _88435 _88436 P a).
Proof. exact (@lem3401144 _88435 (term164 _88435 _88436 P a) (term165 _88435 _88436 P a)). Qed.
Lemma lem3401146 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term166 _88435 _88436 P a b) = (term131 _88435 _88436 P a b).
Proof. exact (eq_refl (term166 _88435 _88436 P a b)). Qed.
Lemma lem3401147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401148 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term167 _88435 _88436 P a b) = (term132 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401147) (@lem3401146 _88435 _88436 P a b)). Qed.
Lemma lem3401149 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term168 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term168 _88435 _88436 P a b)). Qed.
Lemma lem3401150 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term169 _88435 _88436 P a b) = (term134 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401148 _88435 _88436 P a b) (@lem3401149 _88435 _88436 P a b)). Qed.
Lemma lem3401151 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term170 _88435 _88436 P a) = (term143 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401150 _88435 _88436 P a b)). Qed.
Lemma lem3401152 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401153 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term162 _88435 _88436 P a) = (term144 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401152 _88435) (@lem3401151 _88435 _88436 P a)). Qed.
Lemma lem3401154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401155 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term171 _88435 _88436 P a) = (term172 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401154) (@lem3401153 _88435 _88436 P a)). Qed.
Lemma lem3401156 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term166 _88435 _88436 P a b) = (term131 _88435 _88436 P a b).
Proof. exact (eq_refl (term166 _88435 _88436 P a b)). Qed.
Lemma lem3401157 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term173 _88435 _88436 P a) = (term164 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401156 _88435 _88436 P a b)). Qed.
Lemma lem3401158 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401159 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term174 _88435 _88436 P a) = (term175 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401158 _88435) (@lem3401157 _88435 _88436 P a)). Qed.
Lemma lem3401160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401161 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term176 _88435 _88436 P a) = (term177 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401160) (@lem3401159 _88435 _88436 P a)). Qed.
Lemma lem3401162 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term168 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term168 _88435 _88436 P a b)). Qed.
Lemma lem3401163 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term178 _88435 _88436 P a) = (term165 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401162 _88435 _88436 P a b)). Qed.
Lemma lem3401164 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401165 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term179 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401164 _88435) (@lem3401163 _88435 _88436 P a)). Qed.
Lemma lem3401166 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term163 _88435 _88436 P a) = (term181 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401161 _88435 _88436 P a) (@lem3401165 _88435 _88436 P a)). Qed.
Lemma lem3401167 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : ((term162 _88435 _88436 P a) = (term163 _88435 _88436 P a)) = ((term144 _88435 _88436 P a) = (term181 _88435 _88436 P a)).
Proof. exact (MK_COMB (@lem3401155 _88435 _88436 P a) (@lem3401166 _88435 _88436 P a)). Qed.
Lemma lem3401168 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term144 _88435 _88436 P a) = (term181 _88435 _88436 P a).
Proof. exact (EQ_MP (@lem3401167 _88435 _88436 P a) (@lem3401145 _88435 _88436 P a)). Qed.
Lemma lem3401369 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term150 _88435 _88436 P) = (term182 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401168 _88435 _88436 P a)). Qed.
Lemma lem3401370 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401371 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term151 _88435 _88436 P) = (term183 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401370 _88436) (@lem3401369 _88435 _88436 P)). Qed.
Lemma lem3401373 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3401374 {_88436 : Type'} (P : _88436 -> Prop) (Q : _88436 -> Prop) : (term160 _88436 P Q) = (term161 _88436 P Q).
Proof. exact (@lem3401373 _88436 P Q). Qed.
Lemma lem3401375 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term184 _88435 _88436 P) = (term185 _88435 _88436 P).
Proof. exact (@lem3401374 _88436 (term186 _88435 _88436 P) (term187 _88435 _88436 P)). Qed.
Lemma lem3401376 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term188 _88435 _88436 P a) = (term175 _88435 _88436 P a).
Proof. exact (eq_refl (term188 _88435 _88436 P a)). Qed.
Lemma lem3401377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401378 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term189 _88435 _88436 P a) = (term177 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401377) (@lem3401376 _88435 _88436 P a)). Qed.
Lemma lem3401379 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term190 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (eq_refl (term190 _88435 _88436 P a)). Qed.
Lemma lem3401380 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term191 _88435 _88436 P a) = (term181 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401378 _88435 _88436 P a) (@lem3401379 _88435 _88436 P a)). Qed.
Lemma lem3401381 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term192 _88435 _88436 P) = (term182 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401380 _88435 _88436 P a)). Qed.
Lemma lem3401382 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401383 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term184 _88435 _88436 P) = (term183 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401382 _88436) (@lem3401381 _88435 _88436 P)). Qed.
Lemma lem3401384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401385 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term193 _88435 _88436 P) = (term194 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401384) (@lem3401383 _88435 _88436 P)). Qed.
Lemma lem3401386 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term188 _88435 _88436 P a) = (term175 _88435 _88436 P a).
Proof. exact (eq_refl (term188 _88435 _88436 P a)). Qed.
Lemma lem3401387 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term195 _88435 _88436 P) = (term186 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401386 _88435 _88436 P a)). Qed.
Lemma lem3401388 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401389 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term196 _88435 _88436 P) = (term197 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401388 _88436) (@lem3401387 _88435 _88436 P)). Qed.
Lemma lem3401390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401391 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term198 _88435 _88436 P) = (term199 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401390) (@lem3401389 _88435 _88436 P)). Qed.
Lemma lem3401392 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term190 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (eq_refl (term190 _88435 _88436 P a)). Qed.
Lemma lem3401393 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term200 _88435 _88436 P) = (term187 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401392 _88435 _88436 P a)). Qed.
Lemma lem3401394 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401395 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term201 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401394 _88436) (@lem3401393 _88435 _88436 P)). Qed.
Lemma lem3401396 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term185 _88435 _88436 P) = (term203 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401391 _88435 _88436 P) (@lem3401395 _88435 _88436 P)). Qed.
Lemma lem3401397 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : ((term184 _88435 _88436 P) = (term185 _88435 _88436 P)) = ((term183 _88435 _88436 P) = (term203 _88435 _88436 P)).
Proof. exact (MK_COMB (@lem3401385 _88435 _88436 P) (@lem3401396 _88435 _88436 P)). Qed.
Lemma lem3401398 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term183 _88435 _88436 P) = (term203 _88435 _88436 P).
Proof. exact (EQ_MP (@lem3401397 _88435 _88436 P) (@lem3401375 _88435 _88436 P)). Qed.
Lemma lem3401607 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term151 _88435 _88436 P) = (term203 _88435 _88436 P).
Proof. exact (TRANS (@lem3401371 _88435 _88436 P) (@lem3401398 _88435 _88436 P)). Qed.
Lemma lem3401608 {_88435 _88436 : Type'} : (term158 _88435 _88436) = (term204 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401607 _88435 _88436 P)). Qed.
Lemma lem3401609 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401610 {_88435 _88436 : Type'} : (term159 _88435 _88436) = (term205 _88435 _88436).
Proof. exact (MK_COMB (@lem3401609 _88435 _88436) (@lem3401608 _88435 _88436)). Qed.
Lemma lem3401612 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3401613 {_88435 _88436 : Type'} (P : type745 _88435 _88436) (Q : type745 _88435 _88436) : (term206 _88435 _88436 P Q) = (term207 _88435 _88436 P Q).
Proof. exact (@lem3401612 (type1470 _88435 _88436) P Q). Qed.
Lemma lem3401614 {_88435 _88436 : Type'} : (term208 _88435 _88436) = (term209 _88435 _88436).
Proof. exact (@lem3401613 _88435 _88436 (term210 _88435 _88436) (term211 _88435 _88436)). Qed.
Lemma lem3401615 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term212 _88435 _88436 P) = (term197 _88435 _88436 P).
Proof. exact (eq_refl (term212 _88435 _88436 P)). Qed.
Lemma lem3401616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401617 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term213 _88435 _88436 P) = (term199 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401616) (@lem3401615 _88435 _88436 P)). Qed.
Lemma lem3401618 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term214 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (eq_refl (term214 _88435 _88436 P)). Qed.
Lemma lem3401619 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term215 _88435 _88436 P) = (term203 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401617 _88435 _88436 P) (@lem3401618 _88435 _88436 P)). Qed.
Lemma lem3401620 {_88435 _88436 : Type'} : (term216 _88435 _88436) = (term204 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401619 _88435 _88436 P)). Qed.
Lemma lem3401621 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401622 {_88435 _88436 : Type'} : (term208 _88435 _88436) = (term205 _88435 _88436).
Proof. exact (MK_COMB (@lem3401621 _88435 _88436) (@lem3401620 _88435 _88436)). Qed.
Lemma lem3401623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401624 {_88435 _88436 : Type'} : (term217 _88435 _88436) = (term218 _88435 _88436).
Proof. exact (MK_COMB (@lem3401623) (@lem3401622 _88435 _88436)). Qed.
Lemma lem3401625 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term212 _88435 _88436 P) = (term197 _88435 _88436 P).
Proof. exact (eq_refl (term212 _88435 _88436 P)). Qed.
Lemma lem3401626 {_88435 _88436 : Type'} : (term219 _88435 _88436) = (term210 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401625 _88435 _88436 P)). Qed.
Lemma lem3401627 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401628 {_88435 _88436 : Type'} : (term220 _88435 _88436) = (term221 _88435 _88436).
Proof. exact (MK_COMB (@lem3401627 _88435 _88436) (@lem3401626 _88435 _88436)). Qed.
Lemma lem3401629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401630 {_88435 _88436 : Type'} : (term222 _88435 _88436) = (term223 _88435 _88436).
Proof. exact (MK_COMB (@lem3401629) (@lem3401628 _88435 _88436)). Qed.
Lemma lem3401631 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term214 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (eq_refl (term214 _88435 _88436 P)). Qed.
Lemma lem3401632 {_88435 _88436 : Type'} : (term224 _88435 _88436) = (term211 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401631 _88435 _88436 P)). Qed.
Lemma lem3401633 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401634 {_88435 _88436 : Type'} : (term225 _88435 _88436) = (term226 _88435 _88436).
Proof. exact (MK_COMB (@lem3401633 _88435 _88436) (@lem3401632 _88435 _88436)). Qed.
Lemma lem3401635 {_88435 _88436 : Type'} : (term209 _88435 _88436) = (term227 _88435 _88436).
Proof. exact (MK_COMB (@lem3401630 _88435 _88436) (@lem3401634 _88435 _88436)). Qed.
Lemma lem3401636 {_88435 _88436 : Type'} : ((term208 _88435 _88436) = (term209 _88435 _88436)) = ((term205 _88435 _88436) = (term227 _88435 _88436)).
Proof. exact (MK_COMB (@lem3401624 _88435 _88436) (@lem3401635 _88435 _88436)). Qed.
Lemma lem3401637 {_88435 _88436 : Type'} : (term205 _88435 _88436) = (term227 _88435 _88436).
Proof. exact (EQ_MP (@lem3401636 _88435 _88436) (@lem3401614 _88435 _88436)). Qed.
Lemma lem3401854 {_88435 _88436 : Type'} : (term159 _88435 _88436) = (term227 _88435 _88436).
Proof. exact (TRANS (@lem3401610 _88435 _88436) (@lem3401637 _88435 _88436)). Qed.
Lemma lem3401856 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3401857 {_88436 : Type'} (P : _88436 -> Prop) (Q : Prop) : (term228 _88436 P Q) = (term229 _88436 P Q).
Proof. exact (@lem3401856 _88436 P Q). Qed.
Lemma lem3401858 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term230 _88435 _88436 P a b) = (term231 _88435 _88436 P a b).
Proof. exact (@lem3401857 _88436 (term48 _88435 _88436 P a b) (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401859 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term120 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (eq_refl (term120 _88435 _88436 P a b x)). Qed.
Lemma lem3401860 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term232 _88435 _88436 P a b) = (term48 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3401859 _88435 _88436 P a b x)). Qed.
Lemma lem3401861 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401862 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term233 _88435 _88436 P a b) = (term49 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401861 _88436) (@lem3401860 _88435 _88436 P a b)). Qed.
Lemma lem3401863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401864 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term234 _88435 _88436 P a b) = (term130 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401863) (@lem3401862 _88435 _88436 P a b)). Qed.
Lemma lem3401865 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term125 _88435 _88436 P a b).
Proof. exact (eq_refl (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401866 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term230 _88435 _88436 P a b) = (term131 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401864 _88435 _88436 P a b) (@lem3401865 _88435 _88436 P a b)). Qed.
Lemma lem3401867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401868 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term235 _88435 _88436 P a b) = (term236 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401867) (@lem3401866 _88435 _88436 P a b)). Qed.
Lemma lem3401869 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term120 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (eq_refl (term120 _88435 _88436 P a b x)). Qed.
Lemma lem3401870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401871 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term237 _88435 _88436 P a b x) = (term238 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401870) (@lem3401869 _88435 _88436 P a b x)). Qed.
Lemma lem3401872 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term125 _88435 _88436 P a b).
Proof. exact (eq_refl (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401873 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term239 _88435 _88436 x P a b) = (term240 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3401871 _88435 _88436 P a b x) (@lem3401872 _88435 _88436 P a b)). Qed.
Lemma lem3401874 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term241 _88435 _88436 P a b) = (term242 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3401873 _88435 _88436 x P a b)). Qed.
Lemma lem3401875 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401876 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term231 _88435 _88436 P a b) = (term243 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401875 _88436) (@lem3401874 _88435 _88436 P a b)). Qed.
Lemma lem3401877 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term230 _88435 _88436 P a b) = (term231 _88435 _88436 P a b)) = ((term131 _88435 _88436 P a b) = (term243 _88435 _88436 P a b)).
Proof. exact (MK_COMB (@lem3401868 _88435 _88436 P a b) (@lem3401876 _88435 _88436 P a b)). Qed.
Lemma lem3401878 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term131 _88435 _88436 P a b) = (term243 _88435 _88436 P a b).
Proof. exact (EQ_MP (@lem3401877 _88435 _88436 P a b) (@lem3401858 _88435 _88436 P a b)). Qed.
Lemma lem3401880 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3401881 {_88435 : Type'} (P : _88435 -> Prop) (Q : Prop) : (term228 _88435 P Q) = (term229 _88435 P Q).
Proof. exact (@lem3401880 _88435 P Q). Qed.
Lemma lem3401882 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term244 _88435 _88436 x P a b) = (term245 _88435 _88436 x P a b).
Proof. exact (@lem3401881 _88435 (term44 _88435 _88436 P a b x) (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401883 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term113 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term113 _88435 _88436 P a b x y)). Qed.
Lemma lem3401884 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term246 _88435 _88436 P a b x) = (term44 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3401883 _88435 _88436 P a b x y)). Qed.
Lemma lem3401885 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401886 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term247 _88435 _88436 P a b x) = (term46 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401885 _88435) (@lem3401884 _88435 _88436 P a b x)). Qed.
Lemma lem3401887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401888 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term248 _88435 _88436 P a b x) = (term238 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3401887) (@lem3401886 _88435 _88436 P a b x)). Qed.
Lemma lem3401889 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term125 _88435 _88436 P a b).
Proof. exact (eq_refl (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401890 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term244 _88435 _88436 x P a b) = (term240 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3401888 _88435 _88436 P a b x) (@lem3401889 _88435 _88436 P a b)). Qed.
Lemma lem3401891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401892 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term249 _88435 _88436 x P a b) = (term250 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3401891) (@lem3401890 _88435 _88436 x P a b)). Qed.
Lemma lem3401893 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term113 _88435 _88436 P a b x y) = (term42 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term113 _88435 _88436 P a b x y)). Qed.
Lemma lem3401894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3401895 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term251 _88435 _88436 P a b x y) = (term252 _88435 _88436 P a b x y).
Proof. exact (MK_COMB (@lem3401894) (@lem3401893 _88435 _88436 P a b x y)). Qed.
Lemma lem3401896 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term125 _88435 _88436 P a b).
Proof. exact (eq_refl (term125 _88435 _88436 P a b)). Qed.
Lemma lem3401897 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term253 _88435 _88436 x y P a b) = (term254 _88435 _88436 x y P a b).
Proof. exact (MK_COMB (@lem3401895 _88435 _88436 P a b x y) (@lem3401896 _88435 _88436 P a b)). Qed.
Lemma lem3401898 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term255 _88435 _88436 x P a b) = (term256 _88435 _88436 x P a b).
Proof. exact (fun_ext (fun y : _88435 => @lem3401897 _88435 _88436 x y P a b)). Qed.
Lemma lem3401899 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401900 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term245 _88435 _88436 x P a b) = (term257 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3401899 _88435) (@lem3401898 _88435 _88436 x P a b)). Qed.
Lemma lem3401901 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term244 _88435 _88436 x P a b) = (term245 _88435 _88436 x P a b)) = ((term240 _88435 _88436 x P a b) = (term257 _88435 _88436 x P a b)).
Proof. exact (MK_COMB (@lem3401892 _88435 _88436 x P a b) (@lem3401900 _88435 _88436 x P a b)). Qed.
Lemma lem3401902 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term240 _88435 _88436 x P a b) = (term257 _88435 _88436 x P a b).
Proof. exact (EQ_MP (@lem3401901 _88435 _88436 x P a b) (@lem3401882 _88435 _88436 x P a b)). Qed.
Lemma lem3401903 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term242 _88435 _88436 P a b) = (term258 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3401902 _88435 _88436 x P a b)). Qed.
Lemma lem3401904 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401905 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term243 _88435 _88436 P a b) = (term259 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401904 _88436) (@lem3401903 _88435 _88436 P a b)). Qed.
Lemma lem3401906 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term131 _88435 _88436 P a b) = (term259 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3401878 _88435 _88436 P a b) (@lem3401905 _88435 _88436 P a b)). Qed.
Lemma lem3401907 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term164 _88435 _88436 P a) = (term260 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401906 _88435 _88436 P a b)). Qed.
Lemma lem3401908 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401909 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term175 _88435 _88436 P a) = (term261 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401908 _88435) (@lem3401907 _88435 _88436 P a)). Qed.
Lemma lem3401910 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term186 _88435 _88436 P) = (term262 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401909 _88435 _88436 P a)). Qed.
Lemma lem3401911 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401912 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term197 _88435 _88436 P) = (term263 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401911 _88436) (@lem3401910 _88435 _88436 P)). Qed.
Lemma lem3401913 {_88435 _88436 : Type'} : (term210 _88435 _88436) = (term264 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401912 _88435 _88436 P)). Qed.
Lemma lem3401914 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401915 {_88435 _88436 : Type'} : (term221 _88435 _88436) = (term265 _88435 _88436).
Proof. exact (MK_COMB (@lem3401914 _88435 _88436) (@lem3401913 _88435 _88436)). Qed.
Lemma lem3401916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401917 {_88435 _88436 : Type'} : (term223 _88435 _88436) = (term266 _88435 _88436).
Proof. exact (MK_COMB (@lem3401916) (@lem3401915 _88435 _88436)). Qed.
Lemma lem3401918 {_88435 _88436 : Type'} : (term226 _88435 _88436) = (term226 _88435 _88436).
Proof. exact (eq_refl (term226 _88435 _88436)). Qed.
Lemma lem3401919 {_88435 _88436 : Type'} : (term227 _88435 _88436) = (term267 _88435 _88436).
Proof. exact (MK_COMB (@lem3401917 _88435 _88436) (@lem3401918 _88435 _88436)). Qed.
Lemma lem3401921 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term161 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3401922 {_88435 _88436 : Type'} (P : type745 _88435 _88436) (Q : type745 _88435 _88436) : (term207 _88435 _88436 P Q) = (term206 _88435 _88436 P Q).
Proof. exact (@lem3401921 (type1470 _88435 _88436) P Q). Qed.
Lemma lem3401923 {_88435 _88436 : Type'} : (term268 _88435 _88436) = (term269 _88435 _88436).
Proof. exact (@lem3401922 _88435 _88436 (term264 _88435 _88436) (term211 _88435 _88436)). Qed.
Lemma lem3401924 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term270 _88435 _88436 P) = (term263 _88435 _88436 P).
Proof. exact (eq_refl (term270 _88435 _88436 P)). Qed.
Lemma lem3401925 {_88435 _88436 : Type'} : (term271 _88435 _88436) = (term264 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401924 _88435 _88436 P)). Qed.
Lemma lem3401926 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401927 {_88435 _88436 : Type'} : (term272 _88435 _88436) = (term265 _88435 _88436).
Proof. exact (MK_COMB (@lem3401926 _88435 _88436) (@lem3401925 _88435 _88436)). Qed.
Lemma lem3401928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401929 {_88435 _88436 : Type'} : (term273 _88435 _88436) = (term266 _88435 _88436).
Proof. exact (MK_COMB (@lem3401928) (@lem3401927 _88435 _88436)). Qed.
Lemma lem3401930 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term214 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (eq_refl (term214 _88435 _88436 P)). Qed.
Lemma lem3401931 {_88435 _88436 : Type'} : (term224 _88435 _88436) = (term211 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401930 _88435 _88436 P)). Qed.
Lemma lem3401932 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401933 {_88435 _88436 : Type'} : (term225 _88435 _88436) = (term226 _88435 _88436).
Proof. exact (MK_COMB (@lem3401932 _88435 _88436) (@lem3401931 _88435 _88436)). Qed.
Lemma lem3401934 {_88435 _88436 : Type'} : (term268 _88435 _88436) = (term267 _88435 _88436).
Proof. exact (MK_COMB (@lem3401929 _88435 _88436) (@lem3401933 _88435 _88436)). Qed.
Lemma lem3401935 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401936 {_88435 _88436 : Type'} : (term274 _88435 _88436) = (term275 _88435 _88436).
Proof. exact (MK_COMB (@lem3401935) (@lem3401934 _88435 _88436)). Qed.
Lemma lem3401937 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term270 _88435 _88436 P) = (term263 _88435 _88436 P).
Proof. exact (eq_refl (term270 _88435 _88436 P)). Qed.
Lemma lem3401938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401939 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term276 _88435 _88436 P) = (term277 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401938) (@lem3401937 _88435 _88436 P)). Qed.
Lemma lem3401940 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term214 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (eq_refl (term214 _88435 _88436 P)). Qed.
Lemma lem3401941 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term278 _88435 _88436 P) = (term279 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401939 _88435 _88436 P) (@lem3401940 _88435 _88436 P)). Qed.
Lemma lem3401942 {_88435 _88436 : Type'} : (term280 _88435 _88436) = (term281 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3401941 _88435 _88436 P)). Qed.
Lemma lem3401943 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3401944 {_88435 _88436 : Type'} : (term269 _88435 _88436) = (term282 _88435 _88436).
Proof. exact (MK_COMB (@lem3401943 _88435 _88436) (@lem3401942 _88435 _88436)). Qed.
Lemma lem3401945 {_88435 _88436 : Type'} : ((term268 _88435 _88436) = (term269 _88435 _88436)) = ((term267 _88435 _88436) = (term282 _88435 _88436)).
Proof. exact (MK_COMB (@lem3401936 _88435 _88436) (@lem3401944 _88435 _88436)). Qed.
Lemma lem3401946 {_88435 _88436 : Type'} : (term267 _88435 _88436) = (term282 _88435 _88436).
Proof. exact (EQ_MP (@lem3401945 _88435 _88436) (@lem3401923 _88435 _88436)). Qed.
Lemma lem3401948 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term161 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3401949 {_88436 : Type'} (P : _88436 -> Prop) (Q : _88436 -> Prop) : (term161 _88436 P Q) = (term160 _88436 P Q).
Proof. exact (@lem3401948 _88436 P Q). Qed.
Lemma lem3401950 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term283 _88435 _88436 P) = (term284 _88435 _88436 P).
Proof. exact (@lem3401949 _88436 (term262 _88435 _88436 P) (term187 _88435 _88436 P)). Qed.
Lemma lem3401951 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term285 _88435 _88436 P a) = (term261 _88435 _88436 P a).
Proof. exact (eq_refl (term285 _88435 _88436 P a)). Qed.
Lemma lem3401952 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term286 _88435 _88436 P) = (term262 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401951 _88435 _88436 P a)). Qed.
Lemma lem3401953 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401954 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term287 _88435 _88436 P) = (term263 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401953 _88436) (@lem3401952 _88435 _88436 P)). Qed.
Lemma lem3401955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401956 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term288 _88435 _88436 P) = (term277 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401955) (@lem3401954 _88435 _88436 P)). Qed.
Lemma lem3401957 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term190 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (eq_refl (term190 _88435 _88436 P a)). Qed.
Lemma lem3401958 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term200 _88435 _88436 P) = (term187 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401957 _88435 _88436 P a)). Qed.
Lemma lem3401959 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401960 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term201 _88435 _88436 P) = (term202 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401959 _88436) (@lem3401958 _88435 _88436 P)). Qed.
Lemma lem3401961 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term283 _88435 _88436 P) = (term279 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401956 _88435 _88436 P) (@lem3401960 _88435 _88436 P)). Qed.
Lemma lem3401962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401963 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term289 _88435 _88436 P) = (term290 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401962) (@lem3401961 _88435 _88436 P)). Qed.
Lemma lem3401964 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term285 _88435 _88436 P a) = (term261 _88435 _88436 P a).
Proof. exact (eq_refl (term285 _88435 _88436 P a)). Qed.
Lemma lem3401965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401966 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term291 _88435 _88436 P a) = (term292 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401965) (@lem3401964 _88435 _88436 P a)). Qed.
Lemma lem3401967 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term190 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (eq_refl (term190 _88435 _88436 P a)). Qed.
Lemma lem3401968 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term293 _88435 _88436 P a) = (term294 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401966 _88435 _88436 P a) (@lem3401967 _88435 _88436 P a)). Qed.
Lemma lem3401969 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term295 _88435 _88436 P) = (term296 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3401968 _88435 _88436 P a)). Qed.
Lemma lem3401970 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3401971 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term284 _88435 _88436 P) = (term297 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3401970 _88436) (@lem3401969 _88435 _88436 P)). Qed.
Lemma lem3401972 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : ((term283 _88435 _88436 P) = (term284 _88435 _88436 P)) = ((term279 _88435 _88436 P) = (term297 _88435 _88436 P)).
Proof. exact (MK_COMB (@lem3401963 _88435 _88436 P) (@lem3401971 _88435 _88436 P)). Qed.
Lemma lem3401973 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term279 _88435 _88436 P) = (term297 _88435 _88436 P).
Proof. exact (EQ_MP (@lem3401972 _88435 _88436 P) (@lem3401950 _88435 _88436 P)). Qed.
Lemma lem3401975 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term161 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3401976 {_88435 : Type'} (P : _88435 -> Prop) (Q : _88435 -> Prop) : (term161 _88435 P Q) = (term160 _88435 P Q).
Proof. exact (@lem3401975 _88435 P Q). Qed.
Lemma lem3401977 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term298 _88435 _88436 P a) = (term299 _88435 _88436 P a).
Proof. exact (@lem3401976 _88435 (term260 _88435 _88436 P a) (term165 _88435 _88436 P a)). Qed.
Lemma lem3401978 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term300 _88435 _88436 P a b) = (term259 _88435 _88436 P a b).
Proof. exact (eq_refl (term300 _88435 _88436 P a b)). Qed.
Lemma lem3401979 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term301 _88435 _88436 P a) = (term260 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401978 _88435 _88436 P a b)). Qed.
Lemma lem3401980 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401981 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term302 _88435 _88436 P a) = (term261 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401980 _88435) (@lem3401979 _88435 _88436 P a)). Qed.
Lemma lem3401982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401983 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term303 _88435 _88436 P a) = (term292 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401982) (@lem3401981 _88435 _88436 P a)). Qed.
Lemma lem3401984 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term168 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term168 _88435 _88436 P a b)). Qed.
Lemma lem3401985 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term178 _88435 _88436 P a) = (term165 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401984 _88435 _88436 P a b)). Qed.
Lemma lem3401986 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401987 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term179 _88435 _88436 P a) = (term180 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401986 _88435) (@lem3401985 _88435 _88436 P a)). Qed.
Lemma lem3401988 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term298 _88435 _88436 P a) = (term294 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401983 _88435 _88436 P a) (@lem3401987 _88435 _88436 P a)). Qed.
Lemma lem3401989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3401990 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term304 _88435 _88436 P a) = (term305 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401989) (@lem3401988 _88435 _88436 P a)). Qed.
Lemma lem3401991 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term300 _88435 _88436 P a b) = (term259 _88435 _88436 P a b).
Proof. exact (eq_refl (term300 _88435 _88436 P a b)). Qed.
Lemma lem3401992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3401993 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term306 _88435 _88436 P a b) = (term307 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401992) (@lem3401991 _88435 _88436 P a b)). Qed.
Lemma lem3401994 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term168 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term168 _88435 _88436 P a b)). Qed.
Lemma lem3401995 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term308 _88435 _88436 P a b) = (term309 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3401993 _88435 _88436 P a b) (@lem3401994 _88435 _88436 P a b)). Qed.
Lemma lem3401996 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term310 _88435 _88436 P a) = (term311 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3401995 _88435 _88436 P a b)). Qed.
Lemma lem3401997 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3401998 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term299 _88435 _88436 P a) = (term312 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3401997 _88435) (@lem3401996 _88435 _88436 P a)). Qed.
Lemma lem3401999 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : ((term298 _88435 _88436 P a) = (term299 _88435 _88436 P a)) = ((term294 _88435 _88436 P a) = (term312 _88435 _88436 P a)).
Proof. exact (MK_COMB (@lem3401990 _88435 _88436 P a) (@lem3401998 _88435 _88436 P a)). Qed.
Lemma lem3402000 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term294 _88435 _88436 P a) = (term312 _88435 _88436 P a).
Proof. exact (EQ_MP (@lem3401999 _88435 _88436 P a) (@lem3401977 _88435 _88436 P a)). Qed.
Lemma lem3402002 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3402003 {_88436 : Type'} (P : _88436 -> Prop) (Q : Prop) : (term313 _88436 P Q) = (term314 _88436 P Q).
Proof. exact (@lem3402002 _88436 P Q). Qed.
Lemma lem3402004 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term315 _88435 _88436 P a b) = (term316 _88435 _88436 P a b).
Proof. exact (@lem3402003 _88436 (term258 _88435 _88436 P a b) (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402005 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term317 _88435 _88436 P a b x) = (term257 _88435 _88436 x P a b).
Proof. exact (eq_refl (term317 _88435 _88436 P a b x)). Qed.
Lemma lem3402006 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term318 _88435 _88436 P a b) = (term258 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3402005 _88435 _88436 x P a b)). Qed.
Lemma lem3402007 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3402008 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term319 _88435 _88436 P a b) = (term259 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402007 _88436) (@lem3402006 _88435 _88436 P a b)). Qed.
Lemma lem3402009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3402010 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term320 _88435 _88436 P a b) = (term307 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402009) (@lem3402008 _88435 _88436 P a b)). Qed.
Lemma lem3402011 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term129 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402012 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term315 _88435 _88436 P a b) = (term309 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402010 _88435 _88436 P a b) (@lem3402011 _88435 _88436 P a b)). Qed.
Lemma lem3402013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402014 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term321 _88435 _88436 P a b) = (term322 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402013) (@lem3402012 _88435 _88436 P a b)). Qed.
Lemma lem3402015 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term317 _88435 _88436 P a b x) = (term257 _88435 _88436 x P a b).
Proof. exact (eq_refl (term317 _88435 _88436 P a b x)). Qed.
Lemma lem3402016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3402017 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term323 _88435 _88436 P a b x) = (term324 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402016) (@lem3402015 _88435 _88436 x P a b)). Qed.
Lemma lem3402018 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term129 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402019 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term325 _88435 _88436 x P a b) = (term326 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402017 _88435 _88436 x P a b) (@lem3402018 _88435 _88436 P a b)). Qed.
Lemma lem3402020 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term327 _88435 _88436 P a b) = (term328 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3402019 _88435 _88436 x P a b)). Qed.
Lemma lem3402021 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3402022 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term316 _88435 _88436 P a b) = (term329 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402021 _88436) (@lem3402020 _88435 _88436 P a b)). Qed.
Lemma lem3402023 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term315 _88435 _88436 P a b) = (term316 _88435 _88436 P a b)) = ((term309 _88435 _88436 P a b) = (term329 _88435 _88436 P a b)).
Proof. exact (MK_COMB (@lem3402014 _88435 _88436 P a b) (@lem3402022 _88435 _88436 P a b)). Qed.
Lemma lem3402024 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term309 _88435 _88436 P a b) = (term329 _88435 _88436 P a b).
Proof. exact (EQ_MP (@lem3402023 _88435 _88436 P a b) (@lem3402004 _88435 _88436 P a b)). Qed.
Lemma lem3402026 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3402027 {_88435 : Type'} (P : _88435 -> Prop) (Q : Prop) : (term313 _88435 P Q) = (term314 _88435 P Q).
Proof. exact (@lem3402026 _88435 P Q). Qed.
Lemma lem3402028 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term330 _88435 _88436 x P a b) = (term331 _88435 _88436 x P a b).
Proof. exact (@lem3402027 _88435 (term256 _88435 _88436 x P a b) (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402029 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term332 _88435 _88436 x P a b y) = (term254 _88435 _88436 x y P a b).
Proof. exact (eq_refl (term332 _88435 _88436 x P a b y)). Qed.
Lemma lem3402030 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term333 _88435 _88436 x P a b) = (term256 _88435 _88436 x P a b).
Proof. exact (fun_ext (fun y : _88435 => @lem3402029 _88435 _88436 x y P a b)). Qed.
Lemma lem3402031 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3402032 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term334 _88435 _88436 x P a b) = (term257 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402031 _88435) (@lem3402030 _88435 _88436 x P a b)). Qed.
Lemma lem3402033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3402034 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term335 _88435 _88436 x P a b) = (term324 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402033) (@lem3402032 _88435 _88436 x P a b)). Qed.
Lemma lem3402035 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term129 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402036 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term330 _88435 _88436 x P a b) = (term326 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402034 _88435 _88436 x P a b) (@lem3402035 _88435 _88436 P a b)). Qed.
Lemma lem3402037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402038 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term336 _88435 _88436 x P a b) = (term337 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402037) (@lem3402036 _88435 _88436 x P a b)). Qed.
Lemma lem3402039 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term332 _88435 _88436 x P a b y) = (term254 _88435 _88436 x y P a b).
Proof. exact (eq_refl (term332 _88435 _88436 x P a b y)). Qed.
Lemma lem3402040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3402041 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term338 _88435 _88436 x P a b y) = (term339 _88435 _88436 x y P a b).
Proof. exact (MK_COMB (@lem3402040) (@lem3402039 _88435 _88436 x y P a b)). Qed.
Lemma lem3402042 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term129 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (eq_refl (term129 _88435 _88436 P a b)). Qed.
Lemma lem3402043 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term340 _88435 _88436 x y P a b) = (term341 _88435 _88436 x y P a b).
Proof. exact (MK_COMB (@lem3402041 _88435 _88436 x y P a b) (@lem3402042 _88435 _88436 P a b)). Qed.
Lemma lem3402044 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term342 _88435 _88436 x P a b) = (term343 _88435 _88436 x P a b).
Proof. exact (fun_ext (fun y : _88435 => @lem3402043 _88435 _88436 x y P a b)). Qed.
Lemma lem3402045 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3402046 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term331 _88435 _88436 x P a b) = (term344 _88435 _88436 x P a b).
Proof. exact (MK_COMB (@lem3402045 _88435) (@lem3402044 _88435 _88436 x P a b)). Qed.
Lemma lem3402047 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : ((term330 _88435 _88436 x P a b) = (term331 _88435 _88436 x P a b)) = ((term326 _88435 _88436 x P a b) = (term344 _88435 _88436 x P a b)).
Proof. exact (MK_COMB (@lem3402038 _88435 _88436 x P a b) (@lem3402046 _88435 _88436 x P a b)). Qed.
Lemma lem3402048 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term326 _88435 _88436 x P a b) = (term344 _88435 _88436 x P a b).
Proof. exact (EQ_MP (@lem3402047 _88435 _88436 x P a b) (@lem3402028 _88435 _88436 x P a b)). Qed.
Lemma lem3402049 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term328 _88435 _88436 P a b) = (term345 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3402048 _88435 _88436 x P a b)). Qed.
Lemma lem3402050 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3402051 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term329 _88435 _88436 P a b) = (term346 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3402050 _88436) (@lem3402049 _88435 _88436 P a b)). Qed.
Lemma lem3402052 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term309 _88435 _88436 P a b) = (term346 _88435 _88436 P a b).
Proof. exact (TRANS (@lem3402024 _88435 _88436 P a b) (@lem3402051 _88435 _88436 P a b)). Qed.
Lemma lem3402053 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term311 _88435 _88436 P a) = (term347 _88435 _88436 P a).
Proof. exact (fun_ext (fun b : _88435 => @lem3402052 _88435 _88436 P a b)). Qed.
Lemma lem3402054 {_88435 : Type'} : (@ex _88435) = (@ex _88435).
Proof. exact (eq_refl (@ex _88435)). Qed.
Lemma lem3402055 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term312 _88435 _88436 P a) = (term348 _88435 _88436 P a).
Proof. exact (MK_COMB (@lem3402054 _88435) (@lem3402053 _88435 _88436 P a)). Qed.
Lemma lem3402056 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term294 _88435 _88436 P a) = (term348 _88435 _88436 P a).
Proof. exact (TRANS (@lem3402000 _88435 _88436 P a) (@lem3402055 _88435 _88436 P a)). Qed.
Lemma lem3402057 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term296 _88435 _88436 P) = (term349 _88435 _88436 P).
Proof. exact (fun_ext (fun a : _88436 => @lem3402056 _88435 _88436 P a)). Qed.
Lemma lem3402058 {_88436 : Type'} : (@ex _88436) = (@ex _88436).
Proof. exact (eq_refl (@ex _88436)). Qed.
Lemma lem3402059 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term297 _88435 _88436 P) = (term350 _88435 _88436 P).
Proof. exact (MK_COMB (@lem3402058 _88436) (@lem3402057 _88435 _88436 P)). Qed.
Lemma lem3402060 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term279 _88435 _88436 P) = (term350 _88435 _88436 P).
Proof. exact (TRANS (@lem3401973 _88435 _88436 P) (@lem3402059 _88435 _88436 P)). Qed.
Lemma lem3402061 {_88435 _88436 : Type'} : (term281 _88435 _88436) = (term351 _88435 _88436).
Proof. exact (fun_ext (fun P : type1470 _88435 _88436 => @lem3402060 _88435 _88436 P)). Qed.
Lemma lem3402062 {_88435 _88436 : Type'} : (@ex (_88436 -> _88435 -> Prop)) = (@ex (_88436 -> _88435 -> Prop)).
Proof. exact (eq_refl (@ex (_88436 -> _88435 -> Prop))). Qed.
Lemma lem3402063 {_88435 _88436 : Type'} : (term282 _88435 _88436) = (term352 _88435 _88436).
Proof. exact (MK_COMB (@lem3402062 _88435 _88436) (@lem3402061 _88435 _88436)). Qed.
Lemma lem3402064 {_88435 _88436 : Type'} : (term267 _88435 _88436) = (term352 _88435 _88436).
Proof. exact (TRANS (@lem3401946 _88435 _88436) (@lem3402063 _88435 _88436)). Qed.
Lemma lem3402065 {_88435 _88436 : Type'} : (term227 _88435 _88436) = (term352 _88435 _88436).
Proof. exact (TRANS (@lem3401919 _88435 _88436) (@lem3402064 _88435 _88436)). Qed.
Lemma lem3402066 {_88435 _88436 : Type'} : (term159 _88435 _88436) = (term352 _88435 _88436).
Proof. exact (TRANS (@lem3401854 _88435 _88436) (@lem3402065 _88435 _88436)). Qed.
Lemma lem3402067 {_88435 _88436 : Type'} : (term65 _88435 _88436) = (term352 _88435 _88436).
Proof. exact (TRANS (@lem3401133 _88435 _88436) (@lem3402066 _88435 _88436)). Qed.
Lemma lem3402068 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : term352 _88435 _88436.
Proof. exact (EQ_MP (@lem3402067 _88435 _88436) (@lem3401049 _88435 _88436 h1)). Qed.
Lemma lem3402079 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term353 _88435 _88436 x a y b) = (term354 _88435 _88436 x a y b).
Proof. exact (@lem17045 (x = a) (y = b)). Qed.
Lemma lem3402085 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term355 _88435 _88436 x a y b) = (term355 _88435 _88436 x a y b).
Proof. exact (eq_refl (term355 _88435 _88436 x a y b)). Qed.
Lemma lem3402087 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term356 _88435 _88436 x y a b) = (term356 _88435 _88436 x y a b).
Proof. exact (eq_refl (term356 _88435 _88436 x y a b)). Qed.
Lemma lem3402088 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term357 _88435 _88436 x a y b) = (term358 _88435 _88436 x a y b).
Proof. exact (MK_COMB (@lem3402087 _88435 _88436 x y a b) (@lem3402079 _88435 _88436 x a y b)). Qed.
Lemma lem3402089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402090 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term359 _88435 _88436 x a y b) = (term360 _88435 _88436 x a y b).
Proof. exact (MK_COMB (@lem3402089) (@lem3402088 _88435 _88436 x a y b)). Qed.
Lemma lem3402091 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term361 _88435 _88436 x a y b) = (term362 _88435 _88436 x a y b).
Proof. exact (MK_COMB (@lem3402090 _88435 _88436 x a y b) (@lem3402085 _88435 _88436 x a y b)). Qed.
Lemma lem3402092 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) = (term99 _88435 _88436 x a y b)) = (term361 _88435 _88436 x a y b).
Proof. exact (@lem17784 ((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) (term99 _88435 _88436 x a y b)). Qed.
Lemma lem3402093 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)) = (term99 _88435 _88436 x a y b)) = (term362 _88435 _88436 x a y b).
Proof. exact (TRANS (@lem3402092 _88435 _88436 x a y b) (@lem3402091 _88435 _88436 x a y b)). Qed.
Lemma lem3402094 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term100 _88435 _88436 x a y) = (term363 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3402093 _88435 _88436 x a y b)). Qed.
Lemma lem3402095 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402096 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term101 _88435 _88436 x a y) = (term364 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402095 _88435) (@lem3402094 _88435 _88436 x a y)). Qed.
Lemma lem3402097 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term102 _88435 _88436 x y) = (term365 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3402096 _88435 _88436 x a y)). Qed.
Lemma lem3402098 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402099 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term103 _88435 _88436 x y) = (term366 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402098 _88436) (@lem3402097 _88435 _88436 x y)). Qed.
Lemma lem3402100 {_88435 _88436 : Type'} (x : _88436) : (term104 _88435 _88436 x) = (term367 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3402099 _88435 _88436 x y)). Qed.
Lemma lem3402101 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402102 {_88435 _88436 : Type'} (x : _88436) : (term105 _88435 _88436 x) = (term368 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402101 _88435) (@lem3402100 _88435 _88436 x)). Qed.
Lemma lem3402103 {_88435 _88436 : Type'} : (term106 _88435 _88436) = (term369 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3402102 _88435 _88436 x)). Qed.
Lemma lem3402104 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402105 {_88435 _88436 : Type'} : (term66 _88435 _88436) = (term370 _88435 _88436).
Proof. exact (MK_COMB (@lem3402104 _88436) (@lem3402103 _88435 _88436)). Qed.
Lemma lem3402119 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term371 A P Q) = (term372 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3402120 {_88435 : Type'} (P : _88435 -> Prop) (Q : _88435 -> Prop) : (term371 _88435 P Q) = (term372 _88435 P Q).
Proof. exact (@lem3402119 _88435 P Q). Qed.
Lemma lem3402121 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term373 _88435 _88436 x a y) = (term374 _88435 _88436 x a y).
Proof. exact (@lem3402120 _88435 (term375 _88435 _88436 x a y) (term376 _88435 _88436 x a y)). Qed.
Lemma lem3402122 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term377 _88435 _88436 x a y b) = (term358 _88435 _88436 x a y b).
Proof. exact (eq_refl (term377 _88435 _88436 x a y b)). Qed.
Lemma lem3402123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402124 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term378 _88435 _88436 x a y b) = (term360 _88435 _88436 x a y b).
Proof. exact (MK_COMB (@lem3402123) (@lem3402122 _88435 _88436 x a y b)). Qed.
Lemma lem3402125 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term379 _88435 _88436 x a y b) = (term355 _88435 _88436 x a y b).
Proof. exact (eq_refl (term379 _88435 _88436 x a y b)). Qed.
Lemma lem3402126 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term380 _88435 _88436 x a y b) = (term362 _88435 _88436 x a y b).
Proof. exact (MK_COMB (@lem3402124 _88435 _88436 x a y b) (@lem3402125 _88435 _88436 x a y b)). Qed.
Lemma lem3402127 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term381 _88435 _88436 x a y) = (term363 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3402126 _88435 _88436 x a y b)). Qed.
Lemma lem3402128 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402129 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term373 _88435 _88436 x a y) = (term364 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402128 _88435) (@lem3402127 _88435 _88436 x a y)). Qed.
Lemma lem3402130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402131 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term382 _88435 _88436 x a y) = (term383 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402130) (@lem3402129 _88435 _88436 x a y)). Qed.
Lemma lem3402132 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term377 _88435 _88436 x a y b) = (term358 _88435 _88436 x a y b).
Proof. exact (eq_refl (term377 _88435 _88436 x a y b)). Qed.
Lemma lem3402133 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term384 _88435 _88436 x a y) = (term375 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3402132 _88435 _88436 x a y b)). Qed.
Lemma lem3402134 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402135 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term385 _88435 _88436 x a y) = (term386 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402134 _88435) (@lem3402133 _88435 _88436 x a y)). Qed.
Lemma lem3402136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402137 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term387 _88435 _88436 x a y) = (term388 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402136) (@lem3402135 _88435 _88436 x a y)). Qed.
Lemma lem3402138 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term379 _88435 _88436 x a y b) = (term355 _88435 _88436 x a y b).
Proof. exact (eq_refl (term379 _88435 _88436 x a y b)). Qed.
Lemma lem3402139 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term389 _88435 _88436 x a y) = (term376 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3402138 _88435 _88436 x a y b)). Qed.
Lemma lem3402140 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402141 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term390 _88435 _88436 x a y) = (term391 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402140 _88435) (@lem3402139 _88435 _88436 x a y)). Qed.
Lemma lem3402142 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term374 _88435 _88436 x a y) = (term392 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402137 _88435 _88436 x a y) (@lem3402141 _88435 _88436 x a y)). Qed.
Lemma lem3402143 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : ((term373 _88435 _88436 x a y) = (term374 _88435 _88436 x a y)) = ((term364 _88435 _88436 x a y) = (term392 _88435 _88436 x a y)).
Proof. exact (MK_COMB (@lem3402131 _88435 _88436 x a y) (@lem3402142 _88435 _88436 x a y)). Qed.
Lemma lem3402144 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term364 _88435 _88436 x a y) = (term392 _88435 _88436 x a y).
Proof. exact (EQ_MP (@lem3402143 _88435 _88436 x a y) (@lem3402121 _88435 _88436 x a y)). Qed.
Lemma lem3402241 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term365 _88435 _88436 x y) = (term393 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3402144 _88435 _88436 x a y)). Qed.
Lemma lem3402242 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402243 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term366 _88435 _88436 x y) = (term394 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402242 _88436) (@lem3402241 _88435 _88436 x y)). Qed.
Lemma lem3402245 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term371 A P Q) = (term372 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3402246 {_88436 : Type'} (P : _88436 -> Prop) (Q : _88436 -> Prop) : (term371 _88436 P Q) = (term372 _88436 P Q).
Proof. exact (@lem3402245 _88436 P Q). Qed.
Lemma lem3402247 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term395 _88435 _88436 x y) = (term396 _88435 _88436 x y).
Proof. exact (@lem3402246 _88436 (term397 _88435 _88436 x y) (term398 _88435 _88436 x y)). Qed.
Lemma lem3402248 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term399 _88435 _88436 x y a) = (term386 _88435 _88436 x a y).
Proof. exact (eq_refl (term399 _88435 _88436 x y a)). Qed.
Lemma lem3402249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402250 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term400 _88435 _88436 x y a) = (term388 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402249) (@lem3402248 _88435 _88436 x a y)). Qed.
Lemma lem3402251 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term401 _88435 _88436 x y a) = (term391 _88435 _88436 x a y).
Proof. exact (eq_refl (term401 _88435 _88436 x y a)). Qed.
Lemma lem3402252 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term402 _88435 _88436 x y a) = (term392 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3402250 _88435 _88436 x a y) (@lem3402251 _88435 _88436 x a y)). Qed.
Lemma lem3402253 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term403 _88435 _88436 x y) = (term393 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3402252 _88435 _88436 x a y)). Qed.
Lemma lem3402254 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402255 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term395 _88435 _88436 x y) = (term394 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402254 _88436) (@lem3402253 _88435 _88436 x y)). Qed.
Lemma lem3402256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402257 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term404 _88435 _88436 x y) = (term405 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402256) (@lem3402255 _88435 _88436 x y)). Qed.
Lemma lem3402258 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term399 _88435 _88436 x y a) = (term386 _88435 _88436 x a y).
Proof. exact (eq_refl (term399 _88435 _88436 x y a)). Qed.
Lemma lem3402259 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term406 _88435 _88436 x y) = (term397 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3402258 _88435 _88436 x a y)). Qed.
Lemma lem3402260 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402261 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term407 _88435 _88436 x y) = (term408 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402260 _88436) (@lem3402259 _88435 _88436 x y)). Qed.
Lemma lem3402262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402263 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term409 _88435 _88436 x y) = (term410 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402262) (@lem3402261 _88435 _88436 x y)). Qed.
Lemma lem3402264 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term401 _88435 _88436 x y a) = (term391 _88435 _88436 x a y).
Proof. exact (eq_refl (term401 _88435 _88436 x y a)). Qed.
Lemma lem3402265 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term411 _88435 _88436 x y) = (term398 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3402264 _88435 _88436 x a y)). Qed.
Lemma lem3402266 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402267 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term412 _88435 _88436 x y) = (term413 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402266 _88436) (@lem3402265 _88435 _88436 x y)). Qed.
Lemma lem3402268 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term396 _88435 _88436 x y) = (term414 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402263 _88435 _88436 x y) (@lem3402267 _88435 _88436 x y)). Qed.
Lemma lem3402269 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : ((term395 _88435 _88436 x y) = (term396 _88435 _88436 x y)) = ((term394 _88435 _88436 x y) = (term414 _88435 _88436 x y)).
Proof. exact (MK_COMB (@lem3402257 _88435 _88436 x y) (@lem3402268 _88435 _88436 x y)). Qed.
Lemma lem3402270 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term394 _88435 _88436 x y) = (term414 _88435 _88436 x y).
Proof. exact (EQ_MP (@lem3402269 _88435 _88436 x y) (@lem3402247 _88435 _88436 x y)). Qed.
Lemma lem3402375 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term366 _88435 _88436 x y) = (term414 _88435 _88436 x y).
Proof. exact (TRANS (@lem3402243 _88435 _88436 x y) (@lem3402270 _88435 _88436 x y)). Qed.
Lemma lem3402376 {_88435 _88436 : Type'} (x : _88436) : (term367 _88435 _88436 x) = (term415 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3402375 _88435 _88436 x y)). Qed.
Lemma lem3402377 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402378 {_88435 _88436 : Type'} (x : _88436) : (term368 _88435 _88436 x) = (term416 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402377 _88435) (@lem3402376 _88435 _88436 x)). Qed.
Lemma lem3402380 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term371 A P Q) = (term372 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3402381 {_88435 : Type'} (P : _88435 -> Prop) (Q : _88435 -> Prop) : (term371 _88435 P Q) = (term372 _88435 P Q).
Proof. exact (@lem3402380 _88435 P Q). Qed.
Lemma lem3402382 {_88435 _88436 : Type'} (x : _88436) : (term417 _88435 _88436 x) = (term418 _88435 _88436 x).
Proof. exact (@lem3402381 _88435 (term419 _88435 _88436 x) (term420 _88435 _88436 x)). Qed.
Lemma lem3402383 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term421 _88435 _88436 x y) = (term408 _88435 _88436 x y).
Proof. exact (eq_refl (term421 _88435 _88436 x y)). Qed.
Lemma lem3402384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402385 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term422 _88435 _88436 x y) = (term410 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402384) (@lem3402383 _88435 _88436 x y)). Qed.
Lemma lem3402386 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term423 _88435 _88436 x y) = (term413 _88435 _88436 x y).
Proof. exact (eq_refl (term423 _88435 _88436 x y)). Qed.
Lemma lem3402387 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term424 _88435 _88436 x y) = (term414 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3402385 _88435 _88436 x y) (@lem3402386 _88435 _88436 x y)). Qed.
Lemma lem3402388 {_88435 _88436 : Type'} (x : _88436) : (term425 _88435 _88436 x) = (term415 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3402387 _88435 _88436 x y)). Qed.
Lemma lem3402389 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402390 {_88435 _88436 : Type'} (x : _88436) : (term417 _88435 _88436 x) = (term416 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402389 _88435) (@lem3402388 _88435 _88436 x)). Qed.
Lemma lem3402391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402392 {_88435 _88436 : Type'} (x : _88436) : (term426 _88435 _88436 x) = (term427 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402391) (@lem3402390 _88435 _88436 x)). Qed.
Lemma lem3402393 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term421 _88435 _88436 x y) = (term408 _88435 _88436 x y).
Proof. exact (eq_refl (term421 _88435 _88436 x y)). Qed.
Lemma lem3402394 {_88435 _88436 : Type'} (x : _88436) : (term428 _88435 _88436 x) = (term419 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3402393 _88435 _88436 x y)). Qed.
Lemma lem3402395 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402396 {_88435 _88436 : Type'} (x : _88436) : (term429 _88435 _88436 x) = (term430 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402395 _88435) (@lem3402394 _88435 _88436 x)). Qed.
Lemma lem3402397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402398 {_88435 _88436 : Type'} (x : _88436) : (term431 _88435 _88436 x) = (term432 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402397) (@lem3402396 _88435 _88436 x)). Qed.
Lemma lem3402399 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term423 _88435 _88436 x y) = (term413 _88435 _88436 x y).
Proof. exact (eq_refl (term423 _88435 _88436 x y)). Qed.
Lemma lem3402400 {_88435 _88436 : Type'} (x : _88436) : (term433 _88435 _88436 x) = (term420 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3402399 _88435 _88436 x y)). Qed.
Lemma lem3402401 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3402402 {_88435 _88436 : Type'} (x : _88436) : (term434 _88435 _88436 x) = (term435 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402401 _88435) (@lem3402400 _88435 _88436 x)). Qed.
Lemma lem3402403 {_88435 _88436 : Type'} (x : _88436) : (term418 _88435 _88436 x) = (term436 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402398 _88435 _88436 x) (@lem3402402 _88435 _88436 x)). Qed.
Lemma lem3402404 {_88435 _88436 : Type'} (x : _88436) : ((term417 _88435 _88436 x) = (term418 _88435 _88436 x)) = ((term416 _88435 _88436 x) = (term436 _88435 _88436 x)).
Proof. exact (MK_COMB (@lem3402392 _88435 _88436 x) (@lem3402403 _88435 _88436 x)). Qed.
Lemma lem3402405 {_88435 _88436 : Type'} (x : _88436) : (term416 _88435 _88436 x) = (term436 _88435 _88436 x).
Proof. exact (EQ_MP (@lem3402404 _88435 _88436 x) (@lem3402382 _88435 _88436 x)). Qed.
Lemma lem3402518 {_88435 _88436 : Type'} (x : _88436) : (term368 _88435 _88436 x) = (term436 _88435 _88436 x).
Proof. exact (TRANS (@lem3402378 _88435 _88436 x) (@lem3402405 _88435 _88436 x)). Qed.
Lemma lem3402519 {_88435 _88436 : Type'} : (term369 _88435 _88436) = (term437 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3402518 _88435 _88436 x)). Qed.
Lemma lem3402520 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402521 {_88435 _88436 : Type'} : (term370 _88435 _88436) = (term438 _88435 _88436).
Proof. exact (MK_COMB (@lem3402520 _88436) (@lem3402519 _88435 _88436)). Qed.
Lemma lem3402523 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term371 A P Q) = (term372 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3402524 {_88436 : Type'} (P : _88436 -> Prop) (Q : _88436 -> Prop) : (term371 _88436 P Q) = (term372 _88436 P Q).
Proof. exact (@lem3402523 _88436 P Q). Qed.
Lemma lem3402525 {_88435 _88436 : Type'} : (term439 _88435 _88436) = (term440 _88435 _88436).
Proof. exact (@lem3402524 _88436 (term441 _88435 _88436) (term442 _88435 _88436)). Qed.
Lemma lem3402526 {_88435 _88436 : Type'} (x : _88436) : (term443 _88435 _88436 x) = (term430 _88435 _88436 x).
Proof. exact (eq_refl (term443 _88435 _88436 x)). Qed.
Lemma lem3402527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402528 {_88435 _88436 : Type'} (x : _88436) : (term444 _88435 _88436 x) = (term432 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402527) (@lem3402526 _88435 _88436 x)). Qed.
Lemma lem3402529 {_88435 _88436 : Type'} (x : _88436) : (term445 _88435 _88436 x) = (term435 _88435 _88436 x).
Proof. exact (eq_refl (term445 _88435 _88436 x)). Qed.
Lemma lem3402530 {_88435 _88436 : Type'} (x : _88436) : (term446 _88435 _88436 x) = (term436 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3402528 _88435 _88436 x) (@lem3402529 _88435 _88436 x)). Qed.
Lemma lem3402531 {_88435 _88436 : Type'} : (term447 _88435 _88436) = (term437 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3402530 _88435 _88436 x)). Qed.
Lemma lem3402532 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402533 {_88435 _88436 : Type'} : (term439 _88435 _88436) = (term438 _88435 _88436).
Proof. exact (MK_COMB (@lem3402532 _88436) (@lem3402531 _88435 _88436)). Qed.
Lemma lem3402534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3402535 {_88435 _88436 : Type'} : (term448 _88435 _88436) = (term449 _88435 _88436).
Proof. exact (MK_COMB (@lem3402534) (@lem3402533 _88435 _88436)). Qed.
Lemma lem3402536 {_88435 _88436 : Type'} (x : _88436) : (term443 _88435 _88436 x) = (term430 _88435 _88436 x).
Proof. exact (eq_refl (term443 _88435 _88436 x)). Qed.
Lemma lem3402537 {_88435 _88436 : Type'} : (term450 _88435 _88436) = (term441 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3402536 _88435 _88436 x)). Qed.
Lemma lem3402538 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402539 {_88435 _88436 : Type'} : (term451 _88435 _88436) = (term452 _88435 _88436).
Proof. exact (MK_COMB (@lem3402538 _88436) (@lem3402537 _88435 _88436)). Qed.
Lemma lem3402540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3402541 {_88435 _88436 : Type'} : (term453 _88435 _88436) = (term454 _88435 _88436).
Proof. exact (MK_COMB (@lem3402540) (@lem3402539 _88435 _88436)). Qed.
Lemma lem3402542 {_88435 _88436 : Type'} (x : _88436) : (term445 _88435 _88436 x) = (term435 _88435 _88436 x).
Proof. exact (eq_refl (term445 _88435 _88436 x)). Qed.
Lemma lem3402543 {_88435 _88436 : Type'} : (term455 _88435 _88436) = (term442 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3402542 _88435 _88436 x)). Qed.
Lemma lem3402544 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3402545 {_88435 _88436 : Type'} : (term456 _88435 _88436) = (term457 _88435 _88436).
Proof. exact (MK_COMB (@lem3402544 _88436) (@lem3402543 _88435 _88436)). Qed.
Lemma lem3402546 {_88435 _88436 : Type'} : (term440 _88435 _88436) = (term458 _88435 _88436).
Proof. exact (MK_COMB (@lem3402541 _88435 _88436) (@lem3402545 _88435 _88436)). Qed.
Lemma lem3402547 {_88435 _88436 : Type'} : ((term439 _88435 _88436) = (term440 _88435 _88436)) = ((term438 _88435 _88436) = (term458 _88435 _88436)).
Proof. exact (MK_COMB (@lem3402535 _88435 _88436) (@lem3402546 _88435 _88436)). Qed.
Lemma lem3402548 {_88435 _88436 : Type'} : (term438 _88435 _88436) = (term458 _88435 _88436).
Proof. exact (EQ_MP (@lem3402547 _88435 _88436) (@lem3402525 _88435 _88436)). Qed.
Lemma lem3402671 {_88435 _88436 : Type'} : (term370 _88435 _88436) = (term458 _88435 _88436).
Proof. exact (TRANS (@lem3402521 _88435 _88436) (@lem3402548 _88435 _88436)). Qed.
Lemma lem3402672 {_88435 _88436 : Type'} : (term66 _88435 _88436) = (term458 _88435 _88436).
Proof. exact (TRANS (@lem3402105 _88435 _88436) (@lem3402671 _88435 _88436)). Qed.
Lemma lem3402673 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) : term458 _88435 _88436.
Proof. exact (EQ_MP (@lem3402672 _88435 _88436) (@lem3401050 _88435 _88436 h1)). Qed.
Lemma lem3403884 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (h1 : term350 _88435 _88436 P) : term350 _88435 _88436 P.
Proof. exact (h1). Qed.
Lemma lem3403885 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (h1 : term348 _88435 _88436 P a) : term348 _88435 _88436 P a.
Proof. exact (h1). Qed.
Lemma lem3403886 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term346 _88435 _88436 P a b) : term346 _88435 _88436 P a b.
Proof. exact (h1). Qed.
Lemma lem3403887 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term344 _88435 _88436 x P a b) : term344 _88435 _88436 x P a b.
Proof. exact (h1). Qed.
Lemma lem3403888 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term341 _88435 _88436 x y P a b) : term341 _88435 _88436 x y P a b.
Proof. exact (h1). Qed.
Lemma lem3403919 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term355 _88435 _88436 x a y b) = (term355 _88435 _88436 x a y b).
Proof. exact (eq_refl (term355 _88435 _88436 x a y b)). Qed.
Lemma lem3403920 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term376 _88435 _88436 x a y) = (term376 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3403919 _88435 _88436 x a y b)). Qed.
Lemma lem3403921 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3403922 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term391 _88435 _88436 x a y) = (term391 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3403921 _88435) (@lem3403920 _88435 _88436 x a y)). Qed.
Lemma lem3403923 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term398 _88435 _88436 x y) = (term398 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3403922 _88435 _88436 x a y)). Qed.
Lemma lem3403924 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3403925 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term413 _88435 _88436 x y) = (term413 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3403924 _88436) (@lem3403923 _88435 _88436 x y)). Qed.
Lemma lem3403926 {_88435 _88436 : Type'} (x : _88436) : (term420 _88435 _88436 x) = (term420 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3403925 _88435 _88436 x y)). Qed.
Lemma lem3403927 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3403928 {_88435 _88436 : Type'} (x : _88436) : (term435 _88435 _88436 x) = (term435 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3403927 _88435) (@lem3403926 _88435 _88436 x)). Qed.
Lemma lem3403929 {_88435 _88436 : Type'} : (term442 _88435 _88436) = (term442 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3403928 _88435 _88436 x)). Qed.
Lemma lem3403930 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3403931 {_88435 _88436 : Type'} : (term457 _88435 _88436) = (term457 _88435 _88436).
Proof. exact (MK_COMB (@lem3403930 _88436) (@lem3403929 _88435 _88436)). Qed.
Lemma lem3403964 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term358 _88435 _88436 x a y b) = (term358 _88435 _88436 x a y b).
Proof. exact (eq_refl (term358 _88435 _88436 x a y b)). Qed.
Lemma lem3403965 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term375 _88435 _88436 x a y) = (term375 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3403964 _88435 _88436 x a y b)). Qed.
Lemma lem3403966 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3403967 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term386 _88435 _88436 x a y) = (term386 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3403966 _88435) (@lem3403965 _88435 _88436 x a y)). Qed.
Lemma lem3403968 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term397 _88435 _88436 x y) = (term397 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3403967 _88435 _88436 x a y)). Qed.
Lemma lem3403969 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3403970 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term408 _88435 _88436 x y) = (term408 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3403969 _88436) (@lem3403968 _88435 _88436 x y)). Qed.
Lemma lem3403971 {_88435 _88436 : Type'} (x : _88436) : (term419 _88435 _88436 x) = (term419 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3403970 _88435 _88436 x y)). Qed.
Lemma lem3403972 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3403973 {_88435 _88436 : Type'} (x : _88436) : (term430 _88435 _88436 x) = (term430 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3403972 _88435) (@lem3403971 _88435 _88436 x)). Qed.
Lemma lem3403974 {_88435 _88436 : Type'} : (term441 _88435 _88436) = (term441 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3403973 _88435 _88436 x)). Qed.
Lemma lem3403975 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3403976 {_88435 _88436 : Type'} : (term452 _88435 _88436) = (term452 _88435 _88436).
Proof. exact (MK_COMB (@lem3403975 _88436) (@lem3403974 _88435 _88436)). Qed.
Lemma lem3403977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3403978 {_88435 _88436 : Type'} : (term454 _88435 _88436) = (term454 _88435 _88436).
Proof. exact (MK_COMB (@lem3403977) (@lem3403976 _88435 _88436)). Qed.
Lemma lem3403979 {_88435 _88436 : Type'} : (term458 _88435 _88436) = (term458 _88435 _88436).
Proof. exact (MK_COMB (@lem3403978 _88435 _88436) (@lem3403931 _88435 _88436)). Qed.
Lemma lem3403980 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) : term458 _88435 _88436.
Proof. exact (EQ_MP (@lem3403979 _88435 _88436) (@lem3402673 _88435 _88436 h1)). Qed.
Lemma lem3404169 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem3404194 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term108 _88435 _88436 P a b x y) = (term108 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term108 _88435 _88436 P a b x y)). Qed.
Lemma lem3404195 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term116 _88435 _88436 P a b x) = (term116 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3404194 _88435 _88436 P a b x y)). Qed.
Lemma lem3404196 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3404197 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term117 _88435 _88436 P a b x) = (term117 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3404196 _88435) (@lem3404195 _88435 _88436 P a b x)). Qed.
Lemma lem3404198 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term123 _88435 _88436 P a b) = (term123 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3404197 _88435 _88436 P a b x)). Qed.
Lemma lem3404199 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3404200 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term124 _88435 _88436 P a b) = (term124 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3404199 _88436) (@lem3404198 _88435 _88436 P a b)). Qed.
Lemma lem3404201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3404202 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term127 _88435 _88436 P a b) = (term127 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3404201) (@lem3404200 _88435 _88436 P a b)). Qed.
Lemma lem3404203 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term129 _88435 _88436 P a b) = (term129 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3404202 _88435 _88436 P a b) (@lem3404169 _88435 _88436 P a b)). Qed.
Lemma lem3404236 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term339 _88435 _88436 x y P a b) = (term339 _88435 _88436 x y P a b).
Proof. exact (eq_refl (term339 _88435 _88436 x y P a b)). Qed.
Lemma lem3404237 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term341 _88435 _88436 x y P a b) = (term341 _88435 _88436 x y P a b).
Proof. exact (MK_COMB (@lem3404236 _88435 _88436 x y P a b) (@lem3404203 _88435 _88436 P a b)). Qed.
Lemma lem3404238 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term341 _88435 _88436 x y P a b) : term341 _88435 _88436 x y P a b.
Proof. exact (EQ_MP (@lem3404237 _88435 _88436 x y P a b) (@lem3403888 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3404243 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) : term457 _88435 _88436.
Proof. exact (proj2 (@lem3403980 _88435 _88436 h1)). Qed.
Lemma lem3404245 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term254 _88435 _88436 x y P a b.
Proof. exact (h1). Qed.
Lemma lem3404246 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term129 _88435 _88436 P a b.
Proof. exact (h1). Qed.
Lemma lem3404248 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term42 _88435 _88436 P a b x y.
Proof. exact (proj1 (@lem3404245 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3404252 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term124 _88435 _88436 P a b.
Proof. exact (proj1 (@lem3404246 _88435 _88436 P a b h1)). Qed.
Lemma lem3404418 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) : (term355 _88435 _88436 x a y b) = (term459 _88435 _88436 x a y b).
Proof. exact (@lem19490 (x = a) (term460 _88435 _88436 x y a b) (y = b)). Qed.
Lemma lem3404419 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term376 _88435 _88436 x a y) = (term461 _88435 _88436 x a y).
Proof. exact (fun_ext (fun b : _88435 => @lem3404418 _88435 _88436 x a y b)). Qed.
Lemma lem3404420 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3404421 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) : (term391 _88435 _88436 x a y) = (term462 _88435 _88436 x a y).
Proof. exact (MK_COMB (@lem3404420 _88435) (@lem3404419 _88435 _88436 x a y)). Qed.
Lemma lem3404422 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term398 _88435 _88436 x y) = (term463 _88435 _88436 x y).
Proof. exact (fun_ext (fun a : _88436 => @lem3404421 _88435 _88436 x a y)). Qed.
Lemma lem3404423 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3404424 {_88435 _88436 : Type'} (x : _88436) (y : _88435) : (term413 _88435 _88436 x y) = (term464 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3404423 _88436) (@lem3404422 _88435 _88436 x y)). Qed.
Lemma lem3404425 {_88435 _88436 : Type'} (x : _88436) : (term420 _88435 _88436 x) = (term465 _88435 _88436 x).
Proof. exact (fun_ext (fun y : _88435 => @lem3404424 _88435 _88436 x y)). Qed.
Lemma lem3404426 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3404427 {_88435 _88436 : Type'} (x : _88436) : (term435 _88435 _88436 x) = (term466 _88435 _88436 x).
Proof. exact (MK_COMB (@lem3404426 _88435) (@lem3404425 _88435 _88436 x)). Qed.
Lemma lem3404428 {_88435 _88436 : Type'} : (term442 _88435 _88436) = (term467 _88435 _88436).
Proof. exact (fun_ext (fun x : _88436 => @lem3404427 _88435 _88436 x)). Qed.
Lemma lem3404429 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3404431 {_88435 _88436 : Type'} : (term457 _88435 _88436) = (term468 _88435 _88436).
Proof. exact (MK_COMB (@lem3404429 _88436) (@lem3404428 _88435 _88436)). Qed.
Lemma lem3404432 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) : term468 _88435 _88436.
Proof. exact (EQ_MP (@lem3404431 _88435 _88436) (@lem3404243 _88435 _88436 h1)). Qed.
Lemma lem3404632 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term108 _88435 _88436 P a b x y) = (term108 _88435 _88436 P a b x y).
Proof. exact (eq_refl (term108 _88435 _88436 P a b x y)). Qed.
Lemma lem3404633 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term116 _88435 _88436 P a b x) = (term116 _88435 _88436 P a b x).
Proof. exact (fun_ext (fun y : _88435 => @lem3404632 _88435 _88436 P a b x y)). Qed.
Lemma lem3404634 {_88435 : Type'} : (@all _88435) = (@all _88435).
Proof. exact (eq_refl (@all _88435)). Qed.
Lemma lem3404635 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (x : _88436) : (term117 _88435 _88436 P a b x) = (term117 _88435 _88436 P a b x).
Proof. exact (MK_COMB (@lem3404634 _88435) (@lem3404633 _88435 _88436 P a b x)). Qed.
Lemma lem3404636 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term123 _88435 _88436 P a b) = (term123 _88435 _88436 P a b).
Proof. exact (fun_ext (fun x : _88436 => @lem3404635 _88435 _88436 P a b x)). Qed.
Lemma lem3404637 {_88436 : Type'} : (@all _88436) = (@all _88436).
Proof. exact (eq_refl (@all _88436)). Qed.
Lemma lem3404639 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term124 _88435 _88436 P a b) = (term124 _88435 _88436 P a b).
Proof. exact (MK_COMB (@lem3404637 _88436) (@lem3404636 _88435 _88436 P a b)). Qed.
Lemma lem3404640 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term124 _88435 _88436 P a b.
Proof. exact (EQ_MP (@lem3404639 _88435 _88436 P a b) (@lem3404252 _88435 _88436 P a b h1)). Qed.
Lemma lem3404705 {_88435 _88436 : Type'} (_35868 : _88436) (h1 : term66 _88435 _88436) : term469 _88435 _88436 _35868.
Proof. exact (@lem3404432 _88435 _88436 h1 _35868). Qed.
Lemma lem3404706 {_88435 _88436 : Type'} (_35868 : _88436) : (term469 _88435 _88436 _35868) = (term466 _88435 _88436 _35868).
Proof. exact (eq_refl (term469 _88435 _88436 _35868)). Qed.
Lemma lem3404707 {_88435 _88436 : Type'} (_35868 : _88436) (h1 : term66 _88435 _88436) : term466 _88435 _88436 _35868.
Proof. exact (EQ_MP (@lem3404706 _88435 _88436 _35868) (@lem3404705 _88435 _88436 _35868 h1)). Qed.
Lemma lem3404708 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (h1 : term66 _88435 _88436) : term470 _88435 _88436 _35868 _35869.
Proof. exact (@lem3404707 _88435 _88436 _35868 h1 _35869). Qed.
Lemma lem3404709 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) : (term470 _88435 _88436 _35868 _35869) = (term464 _88435 _88436 _35868 _35869).
Proof. exact (eq_refl (term470 _88435 _88436 _35868 _35869)). Qed.
Lemma lem3404710 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (h1 : term66 _88435 _88436) : term464 _88435 _88436 _35868 _35869.
Proof. exact (EQ_MP (@lem3404709 _88435 _88436 _35868 _35869) (@lem3404708 _88435 _88436 _35868 _35869 h1)). Qed.
Lemma lem3404711 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (h1 : term66 _88435 _88436) : term471 _88435 _88436 _35868 _35869 _35870.
Proof. exact (@lem3404710 _88435 _88436 _35868 _35869 h1 _35870). Qed.
Lemma lem3404712 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) : (term471 _88435 _88436 _35868 _35869 _35870) = (term462 _88435 _88436 _35868 _35870 _35869).
Proof. exact (eq_refl (term471 _88435 _88436 _35868 _35869 _35870)). Qed.
Lemma lem3404713 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (h1 : term66 _88435 _88436) : term462 _88435 _88436 _35868 _35870 _35869.
Proof. exact (EQ_MP (@lem3404712 _88435 _88436 _35868 _35870 _35869) (@lem3404711 _88435 _88436 _35868 _35869 _35870 h1)). Qed.
Lemma lem3404714 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) (h1 : term66 _88435 _88436) : term472 _88435 _88436 _35868 _35870 _35869 _35871.
Proof. exact (@lem3404713 _88435 _88436 _35868 _35870 _35869 h1 _35871). Qed.
Lemma lem3404715 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) : (term472 _88435 _88436 _35868 _35870 _35869 _35871) = (term459 _88435 _88436 _35868 _35870 _35869 _35871).
Proof. exact (eq_refl (term472 _88435 _88436 _35868 _35870 _35869 _35871)). Qed.
Lemma lem3404716 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) (h1 : term66 _88435 _88436) : term459 _88435 _88436 _35868 _35870 _35869 _35871.
Proof. exact (EQ_MP (@lem3404715 _88435 _88436 _35868 _35870 _35869 _35871) (@lem3404714 _88435 _88436 _35868 _35870 _35869 _35871 h1)). Qed.
Lemma lem3404789 {_88435 _88436 : Type'} (_35896 : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term473 _88435 _88436 P a b _35896.
Proof. exact (@lem3404640 _88435 _88436 P a b h1 _35896). Qed.
Lemma lem3404790 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (_35896 : _88436) : (term473 _88435 _88436 P a b _35896) = (term117 _88435 _88436 P a b _35896).
Proof. exact (eq_refl (term473 _88435 _88436 P a b _35896)). Qed.
Lemma lem3404791 {_88435 _88436 : Type'} (_35896 : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term117 _88435 _88436 P a b _35896.
Proof. exact (EQ_MP (@lem3404790 _88435 _88436 P a b _35896) (@lem3404789 _88435 _88436 _35896 P a b h1)). Qed.
Lemma lem3404792 {_88435 _88436 : Type'} (_35896 : _88436) (_35897 : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term474 _88435 _88436 P a b _35896 _35897.
Proof. exact (@lem3404791 _88435 _88436 _35896 P a b h1 _35897). Qed.
Lemma lem3404793 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (_35896 : _88436) (_35897 : _88435) : (term474 _88435 _88436 P a b _35896 _35897) = (term108 _88435 _88436 P a b _35896 _35897).
Proof. exact (eq_refl (term474 _88435 _88436 P a b _35896 _35897)). Qed.
Lemma lem3404838 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term125 _88435 _88436 P a b.
Proof. exact (proj2 (@lem3404245 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3404848 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) (h1 : term66 _88435 _88436) : term475 _88435 _88436 _35869 _35871 _35868 _35870.
Proof. exact (proj1 (@lem3404716 _88435 _88436 _35868 _35870 _35869 _35871 h1)). Qed.
Lemma lem3404854 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) (h1 : term66 _88435 _88436) : term476 _88435 _88436 _35868 _35870 _35869 _35871.
Proof. exact (proj2 (@lem3404716 _88435 _88436 _35868 _35870 _35869 _35871 h1)). Qed.
Lemma lem3404914 {_88435 _88436 : Type'} (_35896 : _88436) (_35897 : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term108 _88435 _88436 P a b _35896 _35897.
Proof. exact (EQ_MP (@lem3404793 _88435 _88436 P a b _35896 _35897) (@lem3404792 _88435 _88436 _35896 _35897 P a b h1)). Qed.
Lemma lem3404953 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3404954 {_88436 : Type'} (_35898 : _88436) (_35900 : _88436) (h1 : _35898 = _35900) : _35898 = _35900.
Proof. exact (h1). Qed.
Lemma lem3404955 {_88435 : Type'} (_35899 : _88435) (_35901 : _88435) (h1 : _35899 = _35901) : _35899 = _35901.
Proof. exact (h1). Qed.
Lemma lem3404956 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35898 : _88436) (_35900 : _88436) (h1 : _35898 = _35900) : (P _35898) = (P _35900).
Proof. exact (MK_COMB (@lem3404953 _88435 _88436 P) (@lem3404954 _88436 _35898 _35900 h1)). Qed.
Lemma lem3404957 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) (h1 : _35899 = _35901) (h2 : _35898 = _35900) : (P _35898 _35899) = (P _35900 _35901).
Proof. exact (MK_COMB (@lem3404956 _88435 _88436 P _35898 _35900 h2) (@lem3404955 _88435 _35899 _35901 h1)). Qed.
Lemma lem3404959 (b : Prop) (a : Prop) : term477 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3404960 {_88435 _88436 : Type'} (_35900 : _88436) (_35901 : _88435) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : term478 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (@lem3404959 (P _35900 _35901) (P _35898 _35899)). Qed.
Lemma lem3404961 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) (h1 : _35899 = _35901) (h2 : _35898 = _35900) : term479 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (@lem3404960 _88435 _88436 _35900 _35901 P _35898 _35899 (@lem3404957 _88435 _88436 P _35899 _35901 _35898 _35900 h1 h2)). Qed.
Lemma lem3404962 {_88435 _88436 : Type'} (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) (_35901 : _88435) (h1 : _35899 = _35901) : term480 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (fun h0 : _35898 = _35900 => @lem3404961 _88435 _88436 P _35899 _35901 _35898 _35900 h1 h0). Qed.
Lemma lem3404964 (a : Prop) (b : Prop) : (a -> b) = (term481 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3404965 {_88435 _88436 : Type'} (_35900 : _88436) (_35901 : _88435) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term480 _88435 _88436 _35900 _35901 P _35898 _35899) = (term482 _88435 _88436 _35900 _35901 P _35898 _35899).
Proof. exact (@lem3404964 (_35898 = _35900) (term479 _88435 _88436 _35900 _35901 P _35898 _35899)). Qed.
Lemma lem3404966 {_88435 _88436 : Type'} (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) (_35901 : _88435) (h1 : _35899 = _35901) : term482 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (EQ_MP (@lem3404965 _88435 _88436 _35900 _35901 P _35898 _35899) (@lem3404962 _88435 _88436 _35900 P _35898 _35899 _35901 h1)). Qed.
Lemma lem3404967 {_88435 _88436 : Type'} (_35900 : _88436) (_35901 : _88435) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : term483 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (fun h0 : _35899 = _35901 => @lem3404966 _88435 _88436 _35900 P _35898 _35899 _35901 h0). Qed.
Lemma lem3404969 (a : Prop) (b : Prop) : (a -> b) = (term481 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3404970 {_88435 _88436 : Type'} (_35900 : _88436) (_35901 : _88435) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term483 _88435 _88436 _35900 _35901 P _35898 _35899) = (term484 _88435 _88436 _35900 _35901 P _35898 _35899).
Proof. exact (@lem3404969 (_35899 = _35901) (term482 _88435 _88436 _35900 _35901 P _35898 _35899)). Qed.
Lemma lem3404971 {_88435 _88436 : Type'} (_35900 : _88436) (_35901 : _88435) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : term484 _88435 _88436 _35900 _35901 P _35898 _35899.
Proof. exact (EQ_MP (@lem3404970 _88435 _88436 _35900 _35901 P _35898 _35899) (@lem3404967 _88435 _88436 _35900 _35901 P _35898 _35899)). Qed.
Lemma lem3405020 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : term485 _88435 _88436 x y z.
Proof. exact (@lem21385 (prod _88436 _88435) x y z). Qed.
Lemma lem3405032 {_88435 : Type'} (x : _88435) : x = x.
Proof. exact (@lem21386 _88435 x). Qed.
Lemma lem3405033 {_88435 : Type'} (x : _88435) : x = x.
Proof. exact (@lem3405032 _88435 x). Qed.
Lemma lem3405034 {_88435 : Type'} (b : _88435) : b = b.
Proof. exact (@lem3405033 _88435 b). Qed.
Lemma lem3405035 {_88435 : Type'} (b : _88435) : term486 _88435 b.
Proof. exact (fun h0 : term487 _88435 b => @lem3405034 _88435 b). Qed.
Lemma lem3405037 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405038 {_88435 : Type'} (b : _88435) : (term486 _88435 b) = (b = b).
Proof. exact (@lem3405037 (b = b)). Qed.
Lemma lem3405039 {_88435 : Type'} (b : _88435) : b = b.
Proof. exact (EQ_MP (@lem3405038 _88435 b) (@lem3405035 _88435 b)). Qed.
Lemma lem3405041 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 x y).
Proof. exact (proj2 (@lem3404248 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405042 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term489 _88435 _88436 a b x y.
Proof. exact (fun h0 : term460 _88435 _88436 a b x y => @lem3405041 _88435 _88436 x y P a b h1). Qed.
Lemma lem3405044 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405045 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term489 _88435 _88436 a b x y) = ((@pair _88436 _88435 a b) = (@pair _88436 _88435 x y)).
Proof. exact (@lem3405044 ((@pair _88436 _88435 a b) = (@pair _88436 _88435 x y))). Qed.
Lemma lem3405046 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 x y).
Proof. exact (EQ_MP (@lem3405045 _88435 _88436 a b x y) (@lem3405042 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405048 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem21386 (prod _88436 _88435) x). Qed.
Lemma lem3405049 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem3405048 _88435 _88436 x). Qed.
Lemma lem3405050 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (@lem3405049 _88435 _88436 (@pair _88436 _88435 a b)). Qed.
Lemma lem3405051 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : term490 _88435 _88436 a b.
Proof. exact (fun h0 : term491 _88435 _88436 a b => @lem3405050 _88435 _88436 a b). Qed.
Lemma lem3405053 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405054 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (term490 _88435 _88436 a b) = ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b)).
Proof. exact (@lem3405053 ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b))). Qed.
Lemma lem3405055 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (EQ_MP (@lem3405054 _88435 _88436 a b) (@lem3405051 _88435 _88436 a b)). Qed.
Lemma lem3405073 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3405074 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term492 _88435 _88436 x y z) = (term493 _88435 _88436 y x z).
Proof. exact (@lem3405073 (y = z) (term494 _88435 _88436 x z)). Qed.
Lemma lem3405084 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) : (term495 _88435 _88436 x y) = (term495 _88435 _88436 x y).
Proof. exact (eq_refl (term495 _88435 _88436 x y)). Qed.
Lemma lem3405085 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term485 _88435 _88436 x y z) = (term496 _88435 _88436 y x z).
Proof. exact (MK_COMB (@lem3405084 _88435 _88436 x y) (@lem3405074 _88435 _88436 y x z)). Qed.
Lemma lem3405089 (q : Prop) (p : Prop) (r : Prop) : (term497 p q r) = (term497 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3405090 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term496 _88435 _88436 y x z) = (term498 _88435 _88436 y x z).
Proof. exact (@lem3405089 (y = z) (term494 _88435 _88436 x y) (term494 _88435 _88436 x z)). Qed.
Lemma lem3405112 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term485 _88435 _88436 x y z) = (term498 _88435 _88436 y x z).
Proof. exact (TRANS (@lem3405085 _88435 _88436 y x z) (@lem3405090 _88435 _88436 y x z)). Qed.
Lemma lem3405113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405114 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term499 _88435 _88436 x y z) = (term500 _88435 _88436 y x z).
Proof. exact (MK_COMB (@lem3405113) (@lem3405112 _88435 _88436 y x z)). Qed.
Lemma lem3405136 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term498 _88435 _88436 y x z) = (term498 _88435 _88436 y x z).
Proof. exact (eq_refl (term498 _88435 _88436 y x z)). Qed.
Lemma lem3405137 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : ((term485 _88435 _88436 x y z) = (term498 _88435 _88436 y x z)) = ((term498 _88435 _88436 y x z) = (term498 _88435 _88436 y x z)).
Proof. exact (MK_COMB (@lem3405114 _88435 _88436 y x z) (@lem3405136 _88435 _88436 y x z)). Qed.
Lemma lem3405139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3405140 (x : Prop) : (x = x) = True.
Proof. exact (@lem3405139 Prop x). Qed.
Lemma lem3405141 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : ((term498 _88435 _88436 y x z) = (term498 _88435 _88436 y x z)) = True.
Proof. exact (@lem3405140 (term498 _88435 _88436 y x z)). Qed.
Lemma lem3405142 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : ((term485 _88435 _88436 x y z) = (term498 _88435 _88436 y x z)) = True.
Proof. exact (TRANS (@lem3405137 _88435 _88436 y x z) (@lem3405141 _88435 _88436 y x z)). Qed.
Lemma lem3405143 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : True = ((term485 _88435 _88436 x y z) = (term498 _88435 _88436 y x z)).
Proof. exact (SYM (@lem3405142 _88435 _88436 y x z)). Qed.
Lemma lem3405144 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term485 _88435 _88436 x y z) = (term498 _88435 _88436 y x z).
Proof. exact (EQ_MP (@lem3405143 _88435 _88436 y x z) (@lem0)). Qed.
Lemma lem3405145 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : term498 _88435 _88436 y x z.
Proof. exact (EQ_MP (@lem3405144 _88435 _88436 y x z) (@lem3405020 _88435 _88436 x y z)). Qed.
Lemma lem3405147 (b : Prop) (a : Prop) : (a \/ b) = (term501 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3405148 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : (term498 _88435 _88436 y x z) = (term502 _88435 _88436 x y z).
Proof. exact (@lem3405147 (term503 _88435 _88436 y x z) (y = z)). Qed.
Lemma lem3405150 (a : Prop) (b : Prop) : (term504 a b) = (term505 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3405151 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term506 _88435 _88436 y x z) = (term507 _88435 _88436 y x z).
Proof. exact (@lem3405150 (term494 _88435 _88436 x y) (term494 _88435 _88436 x z)). Qed.
Lemma lem3405153 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405154 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) : (term509 _88435 _88436 x y) = (x = y).
Proof. exact (@lem3405153 (x = y)). Qed.
Lemma lem3405155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3405156 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) : (term510 _88435 _88436 x y) = (term511 _88435 _88436 x y).
Proof. exact (MK_COMB (@lem3405155) (@lem3405154 _88435 _88436 x y)). Qed.
Lemma lem3405158 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405159 {_88435 _88436 : Type'} (x : prod _88436 _88435) (z : prod _88436 _88435) : (term509 _88435 _88436 x z) = (x = z).
Proof. exact (@lem3405158 (x = z)). Qed.
Lemma lem3405160 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term507 _88435 _88436 y x z) = (term512 _88435 _88436 y x z).
Proof. exact (MK_COMB (@lem3405156 _88435 _88436 x y) (@lem3405159 _88435 _88436 x z)). Qed.
Lemma lem3405161 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term506 _88435 _88436 y x z) = (term512 _88435 _88436 y x z).
Proof. exact (TRANS (@lem3405151 _88435 _88436 y x z) (@lem3405160 _88435 _88436 y x z)). Qed.
Lemma lem3405162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3405163 {_88435 _88436 : Type'} (y : prod _88436 _88435) (x : prod _88436 _88435) (z : prod _88436 _88435) : (term513 _88435 _88436 y x z) = (term514 _88435 _88436 y x z).
Proof. exact (MK_COMB (@lem3405162) (@lem3405161 _88435 _88436 y x z)). Qed.
Lemma lem3405164 {_88435 _88436 : Type'} (y : prod _88436 _88435) (z : prod _88436 _88435) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3405165 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : (term502 _88435 _88436 x y z) = (term515 _88435 _88436 x y z).
Proof. exact (MK_COMB (@lem3405163 _88435 _88436 y x z) (@lem3405164 _88435 _88436 y z)). Qed.
Lemma lem3405166 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : (term498 _88435 _88436 y x z) = (term515 _88435 _88436 x y z).
Proof. exact (TRANS (@lem3405148 _88435 _88436 x y z) (@lem3405165 _88435 _88436 x y z)). Qed.
Lemma lem3405168 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term516 _88435 _88436 x y a b.
Proof. exact (conj (@lem3405046 _88435 _88436 x y P a b h1) (@lem3405055 _88435 _88436 a b)). Qed.
Lemma lem3405170 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : term515 _88435 _88436 x y z.
Proof. exact (EQ_MP (@lem3405166 _88435 _88436 x y z) (@lem3405145 _88435 _88436 y x z)). Qed.
Lemma lem3405171 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : term515 _88435 _88436 x y z.
Proof. exact (@lem3405170 _88435 _88436 x y z). Qed.
Lemma lem3405172 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (a : _88436) (b : _88435) : term517 _88435 _88436 x y a b.
Proof. exact (@lem3405171 _88435 _88436 (@pair _88436 _88435 a b) (@pair _88436 _88435 x y) (@pair _88436 _88435 a b)). Qed.
Lemma lem3405175 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 a b).
Proof. exact (@lem3405172 _88435 _88436 x y a b (@lem3405168 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405176 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term489 _88435 _88436 x y a b.
Proof. exact (fun h0 : term460 _88435 _88436 x y a b => @lem3405175 _88435 _88436 x y P a b h1). Qed.
Lemma lem3405178 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405179 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term489 _88435 _88436 x y a b) = ((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)).
Proof. exact (@lem3405178 ((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b))). Qed.
Lemma lem3405180 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 a b).
Proof. exact (EQ_MP (@lem3405179 _88435 _88436 x y a b) (@lem3405176 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405186 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3405187 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term475 _88435 _88436 _35869 _35871 _35868 _35870) = (term518 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (@lem3405186 (_35868 = _35870) (term460 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405198 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term519 _88435 _88436 _35869 _35871 _35868 _35870) = (term520 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (MK_COMB (@lem3405197) (@lem3405187 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405208 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term518 _88435 _88436 _35868 _35869 _35870 _35871) = (term518 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (eq_refl (term518 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405209 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term475 _88435 _88436 _35869 _35871 _35868 _35870) = (term518 _88435 _88436 _35868 _35869 _35870 _35871)) = ((term518 _88435 _88436 _35868 _35869 _35870 _35871) = (term518 _88435 _88436 _35868 _35869 _35870 _35871)).
Proof. exact (MK_COMB (@lem3405198 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405208 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3405212 (x : Prop) : (x = x) = True.
Proof. exact (@lem3405211 Prop x). Qed.
Lemma lem3405213 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term518 _88435 _88436 _35868 _35869 _35870 _35871) = (term518 _88435 _88436 _35868 _35869 _35870 _35871)) = True.
Proof. exact (@lem3405212 (term518 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405214 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term475 _88435 _88436 _35869 _35871 _35868 _35870) = (term518 _88435 _88436 _35868 _35869 _35870 _35871)) = True.
Proof. exact (TRANS (@lem3405209 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405213 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405215 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : True = ((term475 _88435 _88436 _35869 _35871 _35868 _35870) = (term518 _88435 _88436 _35868 _35869 _35870 _35871)).
Proof. exact (SYM (@lem3405214 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405216 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term475 _88435 _88436 _35869 _35871 _35868 _35870) = (term518 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (EQ_MP (@lem3405215 _88435 _88436 _35868 _35869 _35870 _35871) (@lem0)). Qed.
Lemma lem3405217 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) (h1 : term66 _88435 _88436) : term518 _88435 _88436 _35868 _35869 _35870 _35871.
Proof. exact (EQ_MP (@lem3405216 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3404848 _88435 _88436 _35869 _35871 _35868 _35870 h1)). Qed.
Lemma lem3405219 (b : Prop) (a : Prop) : (a \/ b) = (term501 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3405220 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) : (term518 _88435 _88436 _35868 _35869 _35870 _35871) = (term521 _88435 _88436 _35869 _35871 _35868 _35870).
Proof. exact (@lem3405219 (term460 _88435 _88436 _35868 _35869 _35870 _35871) (_35868 = _35870)). Qed.
Lemma lem3405222 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405223 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term522 _88435 _88436 _35868 _35869 _35870 _35871) = ((@pair _88436 _88435 _35868 _35869) = (@pair _88436 _88435 _35870 _35871)).
Proof. exact (@lem3405222 ((@pair _88436 _88435 _35868 _35869) = (@pair _88436 _88435 _35870 _35871))). Qed.
Lemma lem3405224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3405225 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term523 _88435 _88436 _35868 _35869 _35870 _35871) = (term524 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (MK_COMB (@lem3405224) (@lem3405223 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405226 {_88436 : Type'} (_35868 : _88436) (_35870 : _88436) : (_35868 = _35870) = (_35868 = _35870).
Proof. exact (eq_refl (_35868 = _35870)). Qed.
Lemma lem3405227 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) : (term521 _88435 _88436 _35869 _35871 _35868 _35870) = (term525 _88435 _88436 _35869 _35871 _35868 _35870).
Proof. exact (MK_COMB (@lem3405225 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405226 _88436 _35868 _35870)). Qed.
Lemma lem3405228 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) : (term518 _88435 _88436 _35868 _35869 _35870 _35871) = (term525 _88435 _88436 _35869 _35871 _35868 _35870).
Proof. exact (TRANS (@lem3405220 _88435 _88436 _35869 _35871 _35868 _35870) (@lem3405227 _88435 _88436 _35869 _35871 _35868 _35870)). Qed.
Lemma lem3405231 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) (h1 : term66 _88435 _88436) : term525 _88435 _88436 _35869 _35871 _35868 _35870.
Proof. exact (EQ_MP (@lem3405228 _88435 _88436 _35869 _35871 _35868 _35870) (@lem3405217 _88435 _88436 _35868 _35869 _35870 _35871 h1)). Qed.
Lemma lem3405232 {_88435 _88436 : Type'} (_35869 : _88435) (_35871 : _88435) (_35868 : _88436) (_35870 : _88436) (h1 : term66 _88435 _88436) : term525 _88435 _88436 _35869 _35871 _35868 _35870.
Proof. exact (@lem3405231 _88435 _88436 _35869 _35871 _35868 _35870 h1). Qed.
Lemma lem3405233 {_88435 _88436 : Type'} (y : _88435) (b : _88435) (x : _88436) (a : _88436) (h1 : term66 _88435 _88436) : term525 _88435 _88436 y b x a.
Proof. exact (@lem3405232 _88435 _88436 y b x a h1). Qed.
Lemma lem3405236 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : x = a.
Proof. exact (@lem3405233 _88435 _88436 y b x a h1 (@lem3405180 _88435 _88436 x y P a b h2)). Qed.
Lemma lem3405237 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term526 _88436 x a.
Proof. exact (fun h0 : term527 _88436 x a => @lem3405236 _88435 _88436 x y P a b h1 h2). Qed.
Lemma lem3405239 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405240 {_88436 : Type'} (x : _88436) (a : _88436) : (term526 _88436 x a) = (x = a).
Proof. exact (@lem3405239 (x = a)). Qed.
Lemma lem3405241 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : x = a.
Proof. exact (EQ_MP (@lem3405240 _88436 x a) (@lem3405237 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405243 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 x y).
Proof. exact (proj2 (@lem3404248 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405244 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term489 _88435 _88436 a b x y.
Proof. exact (fun h0 : term460 _88435 _88436 a b x y => @lem3405243 _88435 _88436 x y P a b h1). Qed.
Lemma lem3405246 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405247 {_88435 _88436 : Type'} (a : _88436) (b : _88435) (x : _88436) (y : _88435) : (term489 _88435 _88436 a b x y) = ((@pair _88436 _88435 a b) = (@pair _88436 _88435 x y)).
Proof. exact (@lem3405246 ((@pair _88436 _88435 a b) = (@pair _88436 _88435 x y))). Qed.
Lemma lem3405248 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 x y).
Proof. exact (EQ_MP (@lem3405247 _88435 _88436 a b x y) (@lem3405244 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405250 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem21386 (prod _88436 _88435) x). Qed.
Lemma lem3405251 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem3405250 _88435 _88436 x). Qed.
Lemma lem3405252 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (@lem3405251 _88435 _88436 (@pair _88436 _88435 a b)). Qed.
Lemma lem3405253 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : term490 _88435 _88436 a b.
Proof. exact (fun h0 : term491 _88435 _88436 a b => @lem3405252 _88435 _88436 a b). Qed.
Lemma lem3405255 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405256 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (term490 _88435 _88436 a b) = ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b)).
Proof. exact (@lem3405255 ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b))). Qed.
Lemma lem3405257 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (EQ_MP (@lem3405256 _88435 _88436 a b) (@lem3405253 _88435 _88436 a b)). Qed.
Lemma lem3405258 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term516 _88435 _88436 x y a b.
Proof. exact (conj (@lem3405248 _88435 _88436 x y P a b h1) (@lem3405257 _88435 _88436 a b)). Qed.
Lemma lem3405260 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : term515 _88435 _88436 x y z.
Proof. exact (EQ_MP (@lem3405166 _88435 _88436 x y z) (@lem3405145 _88435 _88436 y x z)). Qed.
Lemma lem3405261 {_88435 _88436 : Type'} (x : prod _88436 _88435) (y : prod _88436 _88435) (z : prod _88436 _88435) : term515 _88435 _88436 x y z.
Proof. exact (@lem3405260 _88435 _88436 x y z). Qed.
Lemma lem3405262 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (a : _88436) (b : _88435) : term517 _88435 _88436 x y a b.
Proof. exact (@lem3405261 _88435 _88436 (@pair _88436 _88435 a b) (@pair _88436 _88435 x y) (@pair _88436 _88435 a b)). Qed.
Lemma lem3405265 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 a b).
Proof. exact (@lem3405262 _88435 _88436 x y a b (@lem3405258 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405266 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term489 _88435 _88436 x y a b.
Proof. exact (fun h0 : term460 _88435 _88436 x y a b => @lem3405265 _88435 _88436 x y P a b h1). Qed.
Lemma lem3405268 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405269 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (a : _88436) (b : _88435) : (term489 _88435 _88436 x y a b) = ((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b)).
Proof. exact (@lem3405268 ((@pair _88436 _88435 x y) = (@pair _88436 _88435 a b))). Qed.
Lemma lem3405270 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : (@pair _88436 _88435 x y) = (@pair _88436 _88435 a b).
Proof. exact (EQ_MP (@lem3405269 _88435 _88436 x y a b) (@lem3405266 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405276 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3405277 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term476 _88435 _88436 _35868 _35870 _35869 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (@lem3405276 (_35869 = _35871) (term460 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405288 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term529 _88435 _88436 _35868 _35870 _35869 _35871) = (term530 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (MK_COMB (@lem3405287) (@lem3405277 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405298 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term528 _88435 _88436 _35868 _35869 _35870 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (eq_refl (term528 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405299 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term476 _88435 _88436 _35868 _35870 _35869 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871)) = ((term528 _88435 _88436 _35868 _35869 _35870 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871)).
Proof. exact (MK_COMB (@lem3405288 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405298 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405301 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3405302 (x : Prop) : (x = x) = True.
Proof. exact (@lem3405301 Prop x). Qed.
Lemma lem3405303 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term528 _88435 _88436 _35868 _35869 _35870 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871)) = True.
Proof. exact (@lem3405302 (term528 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405304 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : ((term476 _88435 _88436 _35868 _35870 _35869 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871)) = True.
Proof. exact (TRANS (@lem3405299 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405303 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405305 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : True = ((term476 _88435 _88436 _35868 _35870 _35869 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871)).
Proof. exact (SYM (@lem3405304 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405306 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term476 _88435 _88436 _35868 _35870 _35869 _35871) = (term528 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (EQ_MP (@lem3405305 _88435 _88436 _35868 _35869 _35870 _35871) (@lem0)). Qed.
Lemma lem3405307 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) (h1 : term66 _88435 _88436) : term528 _88435 _88436 _35868 _35869 _35870 _35871.
Proof. exact (EQ_MP (@lem3405306 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3404854 _88435 _88436 _35868 _35870 _35869 _35871 h1)). Qed.
Lemma lem3405309 (b : Prop) (a : Prop) : (a \/ b) = (term501 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3405310 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) : (term528 _88435 _88436 _35868 _35869 _35870 _35871) = (term531 _88435 _88436 _35868 _35870 _35869 _35871).
Proof. exact (@lem3405309 (term460 _88435 _88436 _35868 _35869 _35870 _35871) (_35869 = _35871)). Qed.
Lemma lem3405312 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405313 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term522 _88435 _88436 _35868 _35869 _35870 _35871) = ((@pair _88436 _88435 _35868 _35869) = (@pair _88436 _88435 _35870 _35871)).
Proof. exact (@lem3405312 ((@pair _88436 _88435 _35868 _35869) = (@pair _88436 _88435 _35870 _35871))). Qed.
Lemma lem3405314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3405315 {_88435 _88436 : Type'} (_35868 : _88436) (_35869 : _88435) (_35870 : _88436) (_35871 : _88435) : (term523 _88435 _88436 _35868 _35869 _35870 _35871) = (term524 _88435 _88436 _35868 _35869 _35870 _35871).
Proof. exact (MK_COMB (@lem3405314) (@lem3405313 _88435 _88436 _35868 _35869 _35870 _35871)). Qed.
Lemma lem3405316 {_88435 : Type'} (_35869 : _88435) (_35871 : _88435) : (_35869 = _35871) = (_35869 = _35871).
Proof. exact (eq_refl (_35869 = _35871)). Qed.
Lemma lem3405317 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) : (term531 _88435 _88436 _35868 _35870 _35869 _35871) = (term532 _88435 _88436 _35868 _35870 _35869 _35871).
Proof. exact (MK_COMB (@lem3405315 _88435 _88436 _35868 _35869 _35870 _35871) (@lem3405316 _88435 _35869 _35871)). Qed.
Lemma lem3405318 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) : (term528 _88435 _88436 _35868 _35869 _35870 _35871) = (term532 _88435 _88436 _35868 _35870 _35869 _35871).
Proof. exact (TRANS (@lem3405310 _88435 _88436 _35868 _35870 _35869 _35871) (@lem3405317 _88435 _88436 _35868 _35870 _35869 _35871)). Qed.
Lemma lem3405321 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) (h1 : term66 _88435 _88436) : term532 _88435 _88436 _35868 _35870 _35869 _35871.
Proof. exact (EQ_MP (@lem3405318 _88435 _88436 _35868 _35870 _35869 _35871) (@lem3405307 _88435 _88436 _35868 _35869 _35870 _35871 h1)). Qed.
Lemma lem3405322 {_88435 _88436 : Type'} (_35868 : _88436) (_35870 : _88436) (_35869 : _88435) (_35871 : _88435) (h1 : term66 _88435 _88436) : term532 _88435 _88436 _35868 _35870 _35869 _35871.
Proof. exact (@lem3405321 _88435 _88436 _35868 _35870 _35869 _35871 h1). Qed.
Lemma lem3405323 {_88435 _88436 : Type'} (x : _88436) (a : _88436) (y : _88435) (b : _88435) (h1 : term66 _88435 _88436) : term532 _88435 _88436 x a y b.
Proof. exact (@lem3405322 _88435 _88436 x a y b h1). Qed.
Lemma lem3405326 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : y = b.
Proof. exact (@lem3405323 _88435 _88436 x a y b h1 (@lem3405270 _88435 _88436 x y P a b h2)). Qed.
Lemma lem3405327 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term526 _88435 y b.
Proof. exact (fun h0 : term527 _88435 y b => @lem3405326 _88435 _88436 x y P a b h1 h2). Qed.
Lemma lem3405329 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405330 {_88435 : Type'} (y : _88435) (b : _88435) : (term526 _88435 y b) = (y = b).
Proof. exact (@lem3405329 (y = b)). Qed.
Lemma lem3405331 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : y = b.
Proof. exact (EQ_MP (@lem3405330 _88435 y b) (@lem3405327 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405333 {_88436 : Type'} (x : _88436) : x = x.
Proof. exact (@lem21386 _88436 x). Qed.
Lemma lem3405334 {_88436 : Type'} (x : _88436) : x = x.
Proof. exact (@lem3405333 _88436 x). Qed.
Lemma lem3405335 {_88436 : Type'} (x : _88436) : term486 _88436 x.
Proof. exact (fun h0 : term487 _88436 x => @lem3405334 _88436 x). Qed.
Lemma lem3405337 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405338 {_88436 : Type'} (x : _88436) : (term486 _88436 x) = (x = x).
Proof. exact (@lem3405337 (x = x)). Qed.
Lemma lem3405339 {_88436 : Type'} (x : _88436) : x = x.
Proof. exact (EQ_MP (@lem3405338 _88436 x) (@lem3405335 _88436 x)). Qed.
Lemma lem3405341 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : P x y.
Proof. exact (proj1 (@lem3404248 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405342 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term533 _88435 _88436 P x y.
Proof. exact (fun h0 : term125 _88435 _88436 P x y => @lem3405341 _88435 _88436 x y P a b h1). Qed.
Lemma lem3405344 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405345 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (y : _88435) : (term533 _88435 _88436 P x y) = (P x y).
Proof. exact (@lem3405344 (P x y)). Qed.
Lemma lem3405346 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : P x y.
Proof. exact (EQ_MP (@lem3405345 _88435 _88436 P x y) (@lem3405342 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405364 (q : Prop) (p : Prop) (r : Prop) : (term497 p q r) = (term497 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3405365 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term482 _88435 _88436 _35900 _35901 P _35898 _35899) = (term534 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (@lem3405364 (P _35900 _35901) (term527 _88436 _35898 _35900) (term125 _88435 _88436 P _35898 _35899)). Qed.
Lemma lem3405379 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3405380 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term535 _88435 _88436 _35900 P _35898 _35899) = (term536 _88435 _88436 P _35899 _35898 _35900).
Proof. exact (@lem3405379 (term125 _88435 _88436 P _35898 _35899) (term527 _88436 _35898 _35900)). Qed.
Lemma lem3405388 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term537 _88435 _88436 P _35900 _35901) = (term537 _88435 _88436 P _35900 _35901).
Proof. exact (eq_refl (term537 _88435 _88436 P _35900 _35901)). Qed.
Lemma lem3405389 {_88435 _88436 : Type'} (_35901 : _88435) (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term534 _88435 _88436 _35901 _35900 P _35898 _35899) = (term538 _88435 _88436 _35901 P _35899 _35898 _35900).
Proof. exact (MK_COMB (@lem3405388 _88435 _88436 P _35900 _35901) (@lem3405380 _88435 _88436 P _35899 _35898 _35900)). Qed.
Lemma lem3405400 {_88435 _88436 : Type'} (_35901 : _88435) (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term482 _88435 _88436 _35900 _35901 P _35898 _35899) = (term538 _88435 _88436 _35901 P _35899 _35898 _35900).
Proof. exact (TRANS (@lem3405365 _88435 _88436 _35901 _35900 P _35898 _35899) (@lem3405389 _88435 _88436 _35901 P _35899 _35898 _35900)). Qed.
Lemma lem3405401 {_88435 : Type'} (_35899 : _88435) (_35901 : _88435) : (term539 _88435 _35899 _35901) = (term539 _88435 _35899 _35901).
Proof. exact (eq_refl (term539 _88435 _35899 _35901)). Qed.
Lemma lem3405402 {_88435 _88436 : Type'} (_35901 : _88435) (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term540 _88435 _88436 _35901 P _35899 _35898 _35900).
Proof. exact (MK_COMB (@lem3405401 _88435 _35899 _35901) (@lem3405400 _88435 _88436 _35901 P _35899 _35898 _35900)). Qed.
Lemma lem3405406 (q : Prop) (p : Prop) (r : Prop) : (term497 p q r) = (term497 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3405407 {_88435 _88436 : Type'} (_35901 : _88435) (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term540 _88435 _88436 _35901 P _35899 _35898 _35900) = (term541 _88435 _88436 _35901 P _35899 _35898 _35900).
Proof. exact (@lem3405406 (P _35900 _35901) (term527 _88435 _35899 _35901) (term536 _88435 _88436 P _35899 _35898 _35900)). Qed.
Lemma lem3405421 (q : Prop) (p : Prop) (r : Prop) : (term497 p q r) = (term497 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3405422 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term542 _88435 _88436 _35901 P _35899 _35898 _35900) = (term543 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (@lem3405421 (term125 _88435 _88436 P _35898 _35899) (term527 _88435 _35899 _35901) (term527 _88436 _35898 _35900)). Qed.
Lemma lem3405442 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term537 _88435 _88436 P _35900 _35901) = (term537 _88435 _88436 P _35900 _35901).
Proof. exact (eq_refl (term537 _88435 _88436 P _35900 _35901)). Qed.
Lemma lem3405443 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term541 _88435 _88436 _35901 P _35899 _35898 _35900) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (MK_COMB (@lem3405442 _88435 _88436 P _35900 _35901) (@lem3405422 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405454 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term540 _88435 _88436 _35901 P _35899 _35898 _35900) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (TRANS (@lem3405407 _88435 _88436 _35901 P _35899 _35898 _35900) (@lem3405443 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405455 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (TRANS (@lem3405402 _88435 _88436 _35901 P _35899 _35898 _35900) (@lem3405454 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405457 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term545 _88435 _88436 _35900 _35901 P _35898 _35899) = (term546 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (MK_COMB (@lem3405456) (@lem3405455 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405483 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3405484 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term535 _88435 _88436 _35900 P _35898 _35899) = (term536 _88435 _88436 P _35899 _35898 _35900).
Proof. exact (@lem3405483 (term125 _88435 _88436 P _35898 _35899) (term527 _88436 _35898 _35900)). Qed.
Lemma lem3405492 {_88435 : Type'} (_35899 : _88435) (_35901 : _88435) : (term539 _88435 _35899 _35901) = (term539 _88435 _35899 _35901).
Proof. exact (eq_refl (term539 _88435 _35899 _35901)). Qed.
Lemma lem3405493 {_88435 _88436 : Type'} (_35901 : _88435) (P : type1470 _88435 _88436) (_35899 : _88435) (_35898 : _88436) (_35900 : _88436) : (term547 _88435 _88436 _35901 _35900 P _35898 _35899) = (term542 _88435 _88436 _35901 P _35899 _35898 _35900).
Proof. exact (MK_COMB (@lem3405492 _88435 _35899 _35901) (@lem3405484 _88435 _88436 P _35899 _35898 _35900)). Qed.
Lemma lem3405497 (q : Prop) (p : Prop) (r : Prop) : (term497 p q r) = (term497 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3405498 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term542 _88435 _88436 _35901 P _35899 _35898 _35900) = (term543 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (@lem3405497 (term125 _88435 _88436 P _35898 _35899) (term527 _88435 _35899 _35901) (term527 _88436 _35898 _35900)). Qed.
Lemma lem3405518 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term547 _88435 _88436 _35901 _35900 P _35898 _35899) = (term543 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (TRANS (@lem3405493 _88435 _88436 _35901 P _35899 _35898 _35900) (@lem3405498 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405519 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term537 _88435 _88436 P _35900 _35901) = (term537 _88435 _88436 P _35900 _35901).
Proof. exact (eq_refl (term537 _88435 _88436 P _35900 _35901)). Qed.
Lemma lem3405520 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : (term548 _88435 _88436 _35901 _35900 P _35898 _35899) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900).
Proof. exact (MK_COMB (@lem3405519 _88435 _88436 P _35900 _35901) (@lem3405518 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405531 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : ((term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term548 _88435 _88436 _35901 _35900 P _35898 _35899)) = ((term544 _88435 _88436 P _35899 _35901 _35898 _35900) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900)).
Proof. exact (MK_COMB (@lem3405457 _88435 _88436 P _35899 _35901 _35898 _35900) (@lem3405520 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3405534 (x : Prop) : (x = x) = True.
Proof. exact (@lem3405533 Prop x). Qed.
Lemma lem3405535 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35899 : _88435) (_35901 : _88435) (_35898 : _88436) (_35900 : _88436) : ((term544 _88435 _88436 P _35899 _35901 _35898 _35900) = (term544 _88435 _88436 P _35899 _35901 _35898 _35900)) = True.
Proof. exact (@lem3405534 (term544 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405536 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : ((term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term548 _88435 _88436 _35901 _35900 P _35898 _35899)) = True.
Proof. exact (TRANS (@lem3405531 _88435 _88436 P _35899 _35901 _35898 _35900) (@lem3405535 _88435 _88436 P _35899 _35901 _35898 _35900)). Qed.
Lemma lem3405537 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : True = ((term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term548 _88435 _88436 _35901 _35900 P _35898 _35899)).
Proof. exact (SYM (@lem3405536 _88435 _88436 _35901 _35900 P _35898 _35899)). Qed.
Lemma lem3405538 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term484 _88435 _88436 _35900 _35901 P _35898 _35899) = (term548 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (EQ_MP (@lem3405537 _88435 _88436 _35901 _35900 P _35898 _35899) (@lem0)). Qed.
Lemma lem3405539 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : term548 _88435 _88436 _35901 _35900 P _35898 _35899.
Proof. exact (EQ_MP (@lem3405538 _88435 _88436 _35901 _35900 P _35898 _35899) (@lem3404971 _88435 _88436 _35900 _35901 P _35898 _35899)). Qed.
Lemma lem3405541 (b : Prop) (a : Prop) : (a \/ b) = (term501 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3405542 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term548 _88435 _88436 _35901 _35900 P _35898 _35899) = (term549 _88435 _88436 _35898 _35899 P _35900 _35901).
Proof. exact (@lem3405541 (term547 _88435 _88436 _35901 _35900 P _35898 _35899) (P _35900 _35901)). Qed.
Lemma lem3405544 (a : Prop) (b : Prop) : (term504 a b) = (term505 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3405545 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term550 _88435 _88436 _35901 _35900 P _35898 _35899) = (term551 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (@lem3405544 (term527 _88435 _35899 _35901) (term535 _88435 _88436 _35900 P _35898 _35899)). Qed.
Lemma lem3405547 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405548 {_88435 : Type'} (_35899 : _88435) (_35901 : _88435) : (term552 _88435 _35899 _35901) = (_35899 = _35901).
Proof. exact (@lem3405547 (_35899 = _35901)). Qed.
Lemma lem3405549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3405550 {_88435 : Type'} (_35899 : _88435) (_35901 : _88435) : (term553 _88435 _35899 _35901) = (term554 _88435 _35899 _35901).
Proof. exact (MK_COMB (@lem3405549) (@lem3405548 _88435 _35899 _35901)). Qed.
Lemma lem3405552 (a : Prop) (b : Prop) : (term504 a b) = (term505 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3405553 {_88435 _88436 : Type'} (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term555 _88435 _88436 _35900 P _35898 _35899) = (term556 _88435 _88436 _35900 P _35898 _35899).
Proof. exact (@lem3405552 (term527 _88436 _35898 _35900) (term125 _88435 _88436 P _35898 _35899)). Qed.
Lemma lem3405555 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405556 {_88436 : Type'} (_35898 : _88436) (_35900 : _88436) : (term552 _88436 _35898 _35900) = (_35898 = _35900).
Proof. exact (@lem3405555 (_35898 = _35900)). Qed.
Lemma lem3405557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3405558 {_88436 : Type'} (_35898 : _88436) (_35900 : _88436) : (term553 _88436 _35898 _35900) = (term554 _88436 _35898 _35900).
Proof. exact (MK_COMB (@lem3405557) (@lem3405556 _88436 _35898 _35900)). Qed.
Lemma lem3405560 (a : Prop) : (term508 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3405561 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term557 _88435 _88436 P _35898 _35899) = (P _35898 _35899).
Proof. exact (@lem3405560 (P _35898 _35899)). Qed.
Lemma lem3405562 {_88435 _88436 : Type'} (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term556 _88435 _88436 _35900 P _35898 _35899) = (term558 _88435 _88436 _35900 P _35898 _35899).
Proof. exact (MK_COMB (@lem3405558 _88436 _35898 _35900) (@lem3405561 _88435 _88436 P _35898 _35899)). Qed.
Lemma lem3405563 {_88435 _88436 : Type'} (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term555 _88435 _88436 _35900 P _35898 _35899) = (term558 _88435 _88436 _35900 P _35898 _35899).
Proof. exact (TRANS (@lem3405553 _88435 _88436 _35900 P _35898 _35899) (@lem3405562 _88435 _88436 _35900 P _35898 _35899)). Qed.
Lemma lem3405564 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term551 _88435 _88436 _35901 _35900 P _35898 _35899) = (term559 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (MK_COMB (@lem3405550 _88435 _35899 _35901) (@lem3405563 _88435 _88436 _35900 P _35898 _35899)). Qed.
Lemma lem3405565 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term550 _88435 _88436 _35901 _35900 P _35898 _35899) = (term559 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (TRANS (@lem3405545 _88435 _88436 _35901 _35900 P _35898 _35899) (@lem3405564 _88435 _88436 _35901 _35900 P _35898 _35899)). Qed.
Lemma lem3405566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3405567 {_88435 _88436 : Type'} (_35901 : _88435) (_35900 : _88436) (P : type1470 _88435 _88436) (_35898 : _88436) (_35899 : _88435) : (term560 _88435 _88436 _35901 _35900 P _35898 _35899) = (term561 _88435 _88436 _35901 _35900 P _35898 _35899).
Proof. exact (MK_COMB (@lem3405566) (@lem3405565 _88435 _88436 _35901 _35900 P _35898 _35899)). Qed.
Lemma lem3405568 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (P _35900 _35901) = (P _35900 _35901).
Proof. exact (eq_refl (P _35900 _35901)). Qed.
Lemma lem3405569 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term549 _88435 _88436 _35898 _35899 P _35900 _35901) = (term562 _88435 _88436 _35898 _35899 P _35900 _35901).
Proof. exact (MK_COMB (@lem3405567 _88435 _88436 _35901 _35900 P _35898 _35899) (@lem3405568 _88435 _88436 P _35900 _35901)). Qed.
Lemma lem3405570 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : (term548 _88435 _88436 _35901 _35900 P _35898 _35899) = (term562 _88435 _88436 _35898 _35899 P _35900 _35901).
Proof. exact (TRANS (@lem3405542 _88435 _88436 _35898 _35899 P _35900 _35901) (@lem3405569 _88435 _88436 _35898 _35899 P _35900 _35901)). Qed.
Lemma lem3405572 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term563 _88435 _88436 P x y.
Proof. exact (conj (@lem3405339 _88436 x) (@lem3405346 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405573 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term564 _88435 _88436 b P x y.
Proof. exact (conj (@lem3405331 _88435 _88436 x y P a b h1 h2) (@lem3405572 _88435 _88436 x y P a b h2)). Qed.
Lemma lem3405575 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : term562 _88435 _88436 _35898 _35899 P _35900 _35901.
Proof. exact (EQ_MP (@lem3405570 _88435 _88436 _35898 _35899 P _35900 _35901) (@lem3405539 _88435 _88436 _35901 _35900 P _35898 _35899)). Qed.
Lemma lem3405576 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : term562 _88435 _88436 _35898 _35899 P _35900 _35901.
Proof. exact (@lem3405575 _88435 _88436 _35898 _35899 P _35900 _35901). Qed.
Lemma lem3405577 {_88435 _88436 : Type'} (y : _88435) (P : type1470 _88435 _88436) (x : _88436) (b : _88435) : term565 _88435 _88436 y P x b.
Proof. exact (@lem3405576 _88435 _88436 x y P x b). Qed.
Lemma lem3405580 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : P x b.
Proof. exact (@lem3405577 _88435 _88436 y P x b (@lem3405573 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405581 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term533 _88435 _88436 P x b.
Proof. exact (fun h0 : term125 _88435 _88436 P x b => @lem3405580 _88435 _88436 x y P a b h1 h2). Qed.
Lemma lem3405583 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405584 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (x : _88436) (b : _88435) : (term533 _88435 _88436 P x b) = (P x b).
Proof. exact (@lem3405583 (P x b)). Qed.
Lemma lem3405585 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : P x b.
Proof. exact (EQ_MP (@lem3405584 _88435 _88436 P x b) (@lem3405581 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405586 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term558 _88435 _88436 a P x b.
Proof. exact (conj (@lem3405241 _88435 _88436 x y P a b h1 h2) (@lem3405585 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405587 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term566 _88435 _88436 a P x b.
Proof. exact (conj (@lem3405039 _88435 b) (@lem3405586 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405589 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : term562 _88435 _88436 _35898 _35899 P _35900 _35901.
Proof. exact (EQ_MP (@lem3405570 _88435 _88436 _35898 _35899 P _35900 _35901) (@lem3405539 _88435 _88436 _35901 _35900 P _35898 _35899)). Qed.
Lemma lem3405590 {_88435 _88436 : Type'} (_35898 : _88436) (_35899 : _88435) (P : type1470 _88435 _88436) (_35900 : _88436) (_35901 : _88435) : term562 _88435 _88436 _35898 _35899 P _35900 _35901.
Proof. exact (@lem3405589 _88435 _88436 _35898 _35899 P _35900 _35901). Qed.
Lemma lem3405591 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term567 _88435 _88436 x P a b.
Proof. exact (@lem3405590 _88435 _88436 x b P a b). Qed.
Lemma lem3405594 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : P a b.
Proof. exact (@lem3405591 _88435 _88436 x P a b (@lem3405587 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405595 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term533 _88435 _88436 P a b.
Proof. exact (fun h0 : term125 _88435 _88436 P a b => @lem3405594 _88435 _88436 x y P a b h1 h2). Qed.
Lemma lem3405597 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405598 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term533 _88435 _88436 P a b) = (P a b).
Proof. exact (@lem3405597 (P a b)). Qed.
Lemma lem3405599 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : P a b.
Proof. exact (EQ_MP (@lem3405598 _88435 _88436 P a b) (@lem3405595 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405602 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3405604 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term125 _88435 _88436 P a b) = (term568 _88435 _88436 P a b).
Proof. exact (@lem3405602 (P a b)). Qed.
Lemma lem3405607 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term254 _88435 _88436 x y P a b) : term568 _88435 _88436 P a b.
Proof. exact (EQ_MP (@lem3405604 _88435 _88436 P a b) (@lem3404838 _88435 _88436 x y P a b h1)). Qed.
Lemma lem3405610 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : False.
Proof. exact (@lem3405607 _88435 _88436 x y P a b h2 (@lem3405599 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405611 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : term569.
Proof. exact (fun h0 : ~ False => @lem3405610 _88435 _88436 x y P a b h1 h2). Qed.
Lemma lem3405613 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405614 : term569 = False.
Proof. exact (@lem3405613 False). Qed.
Lemma lem3405615 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term254 _88435 _88436 x y P a b) : False.
Proof. exact (EQ_MP (@lem3405614) (@lem3405611 _88435 _88436 x y P a b h1 h2)). Qed.
Lemma lem3405695 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : P a b.
Proof. exact (proj2 (@lem3404246 _88435 _88436 P a b h1)). Qed.
Lemma lem3405696 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term533 _88435 _88436 P a b.
Proof. exact (fun h0 : term125 _88435 _88436 P a b => @lem3405695 _88435 _88436 P a b h1). Qed.
Lemma lem3405698 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405699 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term533 _88435 _88436 P a b) = (P a b).
Proof. exact (@lem3405698 (P a b)). Qed.
Lemma lem3405700 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : P a b.
Proof. exact (EQ_MP (@lem3405699 _88435 _88436 P a b) (@lem3405696 _88435 _88436 P a b h1)). Qed.
Lemma lem3405702 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem21386 (prod _88436 _88435) x). Qed.
Lemma lem3405703 {_88435 _88436 : Type'} (x : prod _88436 _88435) : x = x.
Proof. exact (@lem3405702 _88435 _88436 x). Qed.
Lemma lem3405704 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (@lem3405703 _88435 _88436 (@pair _88436 _88435 a b)). Qed.
Lemma lem3405705 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : term490 _88435 _88436 a b.
Proof. exact (fun h0 : term491 _88435 _88436 a b => @lem3405704 _88435 _88436 a b). Qed.
Lemma lem3405707 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405708 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (term490 _88435 _88436 a b) = ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b)).
Proof. exact (@lem3405707 ((@pair _88436 _88435 a b) = (@pair _88436 _88435 a b))). Qed.
Lemma lem3405709 {_88435 _88436 : Type'} (a : _88436) (b : _88435) : (@pair _88436 _88435 a b) = (@pair _88436 _88435 a b).
Proof. exact (EQ_MP (@lem3405708 _88435 _88436 a b) (@lem3405705 _88435 _88436 a b)). Qed.
Lemma lem3405711 (a : Prop) (b : Prop) : (term570 a b) = (term571 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3405712 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (_35896 : _88436) (_35897 : _88435) : (term108 _88435 _88436 P a b _35896 _35897) = (term107 _88435 _88436 P a b _35896 _35897).
Proof. exact (@lem3405711 (P _35896 _35897) ((@pair _88436 _88435 a b) = (@pair _88436 _88435 _35896 _35897))). Qed.
Lemma lem3405714 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3405715 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (_35896 : _88436) (_35897 : _88435) : (term107 _88435 _88436 P a b _35896 _35897) = (term572 _88435 _88436 P a b _35896 _35897).
Proof. exact (@lem3405714 (term42 _88435 _88436 P a b _35896 _35897)). Qed.
Lemma lem3405716 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (_35896 : _88436) (_35897 : _88435) : (term108 _88435 _88436 P a b _35896 _35897) = (term572 _88435 _88436 P a b _35896 _35897).
Proof. exact (TRANS (@lem3405712 _88435 _88436 P a b _35896 _35897) (@lem3405715 _88435 _88436 P a b _35896 _35897)). Qed.
Lemma lem3405718 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term573 _88435 _88436 P a b.
Proof. exact (conj (@lem3405700 _88435 _88436 P a b h1) (@lem3405709 _88435 _88436 a b)). Qed.
Lemma lem3405720 {_88435 _88436 : Type'} (_35896 : _88436) (_35897 : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term572 _88435 _88436 P a b _35896 _35897.
Proof. exact (EQ_MP (@lem3405716 _88435 _88436 P a b _35896 _35897) (@lem3404914 _88435 _88436 _35896 _35897 P a b h1)). Qed.
Lemma lem3405721 {_88435 _88436 : Type'} (_35896 : _88436) (_35897 : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term572 _88435 _88436 P a b _35896 _35897.
Proof. exact (@lem3405720 _88435 _88436 _35896 _35897 P a b h1). Qed.
Lemma lem3405722 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term574 _88435 _88436 P a b.
Proof. exact (@lem3405721 _88435 _88436 a b P a b h1). Qed.
Lemma lem3405725 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : False.
Proof. exact (@lem3405722 _88435 _88436 P a b h1 (@lem3405718 _88435 _88436 P a b h1)). Qed.
Lemma lem3405726 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : term569.
Proof. exact (fun h0 : ~ False => @lem3405725 _88435 _88436 P a b h1). Qed.
Lemma lem3405728 (p : Prop) : (term488 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3405729 : term569 = False.
Proof. exact (@lem3405728 False). Qed.
Lemma lem3405730 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term129 _88435 _88436 P a b) : False.
Proof. exact (EQ_MP (@lem3405729) (@lem3405726 _88435 _88436 P a b h1)). Qed.
Lemma lem3405731 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term341 _88435 _88436 x y P a b) : False.
Proof. exact (or_elim (@lem3404238 _88435 _88436 x y P a b h2) (fun h0 : term254 _88435 _88436 x y P a b => @lem3405615 _88435 _88436 x y P a b h1 h0) (fun h0 : term129 _88435 _88436 P a b => @lem3405730 _88435 _88436 P a b h0)). Qed.
Lemma lem3405732 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term341 _88435 _88436 x y P a b) : (term341 _88435 _88436 x y P a b) = False.
Proof. exact (prop_ext (fun h3 : term341 _88435 _88436 x y P a b => @lem3405731 _88435 _88436 x y P a b h1 h2) (fun h3 : False => @lem3404238 _88435 _88436 x y P a b h2)). Qed.
Lemma lem3405733 {_88435 _88436 : Type'} (x : _88436) (y : _88435) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term341 _88435 _88436 x y P a b) : False.
Proof. exact (EQ_MP (@lem3405732 _88435 _88436 x y P a b h1 h2) (@lem3404238 _88435 _88436 x y P a b h2)). Qed.
Lemma lem3405734 {_88435 _88436 : Type'} (x : _88436) (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term344 _88435 _88436 x P a b) : False.
Proof. exact (ex_elim (@lem3403887 _88435 _88436 x P a b h2) (fun y : _88435 => fun h0 : term343 _88435 _88436 x P a b y => @lem3405733 _88435 _88436 x y P a b h1 h0)). Qed.
Lemma lem3405735 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) (h1 : term66 _88435 _88436) (h2 : term346 _88435 _88436 P a b) : False.
Proof. exact (ex_elim (@lem3403886 _88435 _88436 P a b h2) (fun x : _88436 => fun h0 : term345 _88435 _88436 P a b x => @lem3405734 _88435 _88436 x P a b h1 h0)). Qed.
Lemma lem3405736 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (h1 : term66 _88435 _88436) (h2 : term348 _88435 _88436 P a) : False.
Proof. exact (ex_elim (@lem3403885 _88435 _88436 P a h2) (fun b : _88435 => fun h0 : term347 _88435 _88436 P a b => @lem3405735 _88435 _88436 P a b h1 h0)). Qed.
Lemma lem3405737 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (h1 : term66 _88435 _88436) (h2 : term350 _88435 _88436 P) : False.
Proof. exact (ex_elim (@lem3403884 _88435 _88436 P h2) (fun a : _88436 => fun h0 : term349 _88435 _88436 P a => @lem3405736 _88435 _88436 P a h1 h0)). Qed.
Lemma lem3405738 {_88435 _88436 : Type'} (h1 : term66 _88435 _88436) (h2 : term65 _88435 _88436) : False.
Proof. exact (ex_elim (@lem3402068 _88435 _88436 h2) (fun P : type1470 _88435 _88436 => fun h0 : term351 _88435 _88436 P => @lem3405737 _88435 _88436 P h1 h0)). Qed.
Lemma lem3405739 {_88435 _88436 B : Type'} (h1 : term66 _88435 _88436) (h2 : term65 _88435 _88436) : term73 _88435 _88436 B.
Proof. exact (fun h0 : term67 _88435 _88436 B => @lem3405738 _88435 _88436 h1 h2). Qed.
Lemma lem3405740 {_88435 _88436 B : Type'} : (term73 _88435 _88436 B) = (term74 _88435 _88436 B).
Proof. exact (@lem69 (term67 _88435 _88436 B)). Qed.
Lemma lem3405741 {_88435 _88436 B : Type'} (h1 : term66 _88435 _88436) (h2 : term65 _88435 _88436) : term74 _88435 _88436 B.
Proof. exact (EQ_MP (@lem3405740 _88435 _88436 B) (@lem3405739 _88435 _88436 B h1 h2)). Qed.
Lemma lem3405742 {_88435 _88436 A B : Type'} (h1 : term66 _88435 _88436) (h2 : term65 _88435 _88436) : term77 _88435 _88436 A B.
Proof. exact (fun h0 : term68 _88435 _88436 A => @lem3405741 _88435 _88436 B h1 h2). Qed.
Lemma lem3405743 {_88435 _88436 A B : Type'} (h1 : term65 _88435 _88436) : term80 _88435 _88436 A B.
Proof. exact (fun h0 : term66 _88435 _88436 => @lem3405742 _88435 _88436 A B h0 h1). Qed.
Lemma lem3405744 {_88435 _88436 A B : Type'} : term82 _88435 _88436 A B.
Proof. exact (fun h0 : term65 _88435 _88436 => @lem3405743 _88435 _88436 A B h0). Qed.
Lemma lem3405745 {_88435 _88436 A B : Type'} : term69 _88435 _88436 A B.
Proof. exact (EQ_MP (@lem3401048 _88435 _88436 A B) (@lem3405744 _88435 _88436 A B)). Qed.
Lemma lem3405747 {_88435 _88436 A B : Type'} : term69 _88435 _88436 A B.
Proof. exact (@lem3400683 _88435 _88436 A B (@lem3405745 _88435 _88436 A B)). Qed.
Lemma lem3405748 {_88435 _88436 A B : Type'} (h1 : term65 _88435 _88436) : term79 _88435 _88436 A B.
Proof. exact (@lem3405747 _88435 _88436 A B (@lem3400663 _88435 _88436 h1)). Qed.
Lemma lem3405749 {_88435 _88436 A B : Type'} (h1 : term65 _88435 _88436) : term76 _88435 _88436 A B.
Proof. exact (@lem3405748 _88435 _88436 A B h1 (@lem3400664 _88435 _88436)). Qed.
Lemma lem3405750 {_88435 _88436 B : Type'} (h1 : term65 _88435 _88436) : term73 _88435 _88436 B.
Proof. exact (@lem3405749 _88435 _88436 Prop B h1 (@lem3400667 _88435 _88436 Prop)). Qed.
Lemma lem3405751 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : False.
Proof. exact (@lem3405750 _88435 _88436 Prop h1 (@lem3400666 _88435 _88436 Prop)). Qed.
Lemma lem3405752 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : (term65 _88435 _88436) = False.
Proof. exact (prop_ext (fun h2 : term65 _88435 _88436 => @lem3405751 _88435 _88436 h1) (fun h2 : False => @lem3400663 _88435 _88436 h1)). Qed.
Lemma lem3405753 {_88435 _88436 : Type'} (h1 : term65 _88435 _88436) : False.
Proof. exact (EQ_MP (@lem3405752 _88435 _88436 h1) (@lem3400663 _88435 _88436 h1)). Qed.
Lemma lem3405754 {_88435 _88436 : Type'} : term64 _88435 _88436.
Proof. exact (fun h0 : term65 _88435 _88436 => @lem3405753 _88435 _88436 h0). Qed.
Lemma lem3405755 {_88435 _88436 : Type'} : term62 _88435 _88436.
Proof. exact (EQ_MP (@lem3400662 _88435 _88436) (@lem3405754 _88435 _88436)). Qed.
Lemma lem3405756 {_88435 _88436 : Type'} : term61 _88435 _88436.
Proof. exact (EQ_MP (@lem3400658 _88435 _88436) (@lem3405755 _88435 _88436)). Qed.
