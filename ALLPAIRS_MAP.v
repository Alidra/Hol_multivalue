Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALLPAIRS_MAP_term_abbrevs.
Require Import ALLPAIRS_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEM_MAP_spec.
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
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21386_spec.
Lemma lem1181595 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1181596 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1181597 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1181596 t1) (@lem1181595 t1)). Qed.
Lemma lem1181598 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1181597 t1 t2). Qed.
Lemma lem1181599 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1181600 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1181599 t1 t2) (@lem1181598 t1 t2)). Qed.
Lemma lem1181601 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1181600 t1 t2 t3). Qed.
Lemma lem1181602 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1181603 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1181602 t1 t2 t3) (@lem1181601 t1 t2 t3)). Qed.
Lemma lem1181604 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1181603 t1 t2 t3)). Qed.
Lemma lem1181608 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) (m : list _27494) (h1 : (term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) : (term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m).
Proof. exact (h1). Qed.
Lemma lem1181609 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) (m : list _27494) (h1 : (term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P).
Proof. exact (SYM (@lem1181608 _27494 _27495 P l m h1)). Qed.
Lemma lem1181610 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h1 : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P)) : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P).
Proof. exact (h1). Qed.
Lemma lem1181611 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) (h1 : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P)) : (term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m).
Proof. exact (SYM (@lem1181610 _27494 _27495 l m P h1)). Qed.
Lemma lem1181612 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : ((term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m)) = ((@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P)).
Proof. exact (prop_ext (fun h1 : (term7 _27494 _27495 l m P) = (@ALLPAIRS _27494 _27495 P l m) => @lem1181609 _27494 _27495 P l m h1) (fun h1 : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P) => @lem1181611 _27494 _27495 l m P h1)). Qed.
Lemma lem1181613 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term8 _27494 _27495 P l) = (term9 _27494 _27495 l P).
Proof. exact (fun_ext (fun m : list _27494 => @lem1181612 _27494 _27495 l m P)). Qed.
Lemma lem1181614 {_27494 : Type'} : (@all (list _27494)) = (@all (list _27494)).
Proof. exact (eq_refl (@all (list _27494))). Qed.
Lemma lem1181615 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term10 _27494 _27495 P l) = (term11 _27494 _27495 l P).
Proof. exact (MK_COMB (@lem1181614 _27494) (@lem1181613 _27494 _27495 l P)). Qed.
Lemma lem1181616 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term12 _27494 _27495 P) = (term13 _27494 _27495 P).
Proof. exact (fun_ext (fun l : list _27495 => @lem1181615 _27494 _27495 l P)). Qed.
Lemma lem1181617 {_27495 : Type'} : (@all (list _27495)) = (@all (list _27495)).
Proof. exact (eq_refl (@all (list _27495))). Qed.
Lemma lem1181618 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term14 _27494 _27495 P) = (term15 _27494 _27495 P).
Proof. exact (MK_COMB (@lem1181617 _27495) (@lem1181616 _27494 _27495 P)). Qed.
Lemma lem1181619 {_27494 _27495 : Type'} : (term16 _27494 _27495) = (term17 _27494 _27495).
Proof. exact (fun_ext (fun P : type1470 _27494 _27495 => @lem1181618 _27494 _27495 P)). Qed.
Lemma lem1181620 {_27494 _27495 : Type'} : (@all (_27495 -> _27494 -> Prop)) = (@all (_27495 -> _27494 -> Prop)).
Proof. exact (eq_refl (@all (_27495 -> _27494 -> Prop))). Qed.
Lemma lem1181621 {_27494 _27495 : Type'} : (term18 _27494 _27495) = (term19 _27494 _27495).
Proof. exact (MK_COMB (@lem1181620 _27494 _27495) (@lem1181619 _27494 _27495)). Qed.
Lemma lem1181622 {_27494 _27495 : Type'} : term19 _27494 _27495.
Proof. exact (EQ_MP (@lem1181621 _27494 _27495) (@lem1181594 _27494 _27495)). Qed.
Lemma lem1181623 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term20 _26978 _26981 f.
Proof. exact (@lem1147568 _26978 _26981 f). Qed.
Lemma lem1181624 {_26978 _26981 : Type'} (f : _26981 -> _26978) : (term20 _26978 _26981 f) = (term21 _26978 _26981 f).
Proof. exact (eq_refl (term20 _26978 _26981 f)). Qed.
Lemma lem1181625 {_26978 _26981 : Type'} (f : _26981 -> _26978) : term21 _26978 _26981 f.
Proof. exact (EQ_MP (@lem1181624 _26978 _26981 f) (@lem1181623 _26978 _26981 f)). Qed.
Lemma lem1181626 {_26978 _26981 : Type'} (f : _26981 -> _26978) (y : _26978) : term22 _26978 _26981 f y.
Proof. exact (@lem1181625 _26978 _26981 f y). Qed.
Lemma lem1181627 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : (term22 _26978 _26981 f y) = (term23 _26978 _26981 y f).
Proof. exact (eq_refl (term22 _26978 _26981 f y)). Qed.
Lemma lem1181628 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) : term23 _26978 _26981 y f.
Proof. exact (EQ_MP (@lem1181627 _26978 _26981 y f) (@lem1181626 _26978 _26981 f y)). Qed.
Lemma lem1181629 {_26978 _26981 : Type'} (y : _26978) (f : _26981 -> _26978) (l : list _26981) : term24 _26978 _26981 y f l.
Proof. exact (@lem1181628 _26978 _26981 y f l). Qed.
Lemma lem1181630 {_26978 _26981 : Type'} (l : list _26981) (y : _26978) (f : _26981 -> _26978) : (term24 _26978 _26981 y f l) = ((term25 _26978 _26981 y f l) = (term26 _26978 _26981 l y f)).
Proof. exact (eq_refl (term24 _26978 _26981 y f l)). Qed.
Lemma lem1181632 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term27 _27494 _27495 P.
Proof. exact (@lem1181622 _27494 _27495 P). Qed.
Lemma lem1181633 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : (term27 _27494 _27495 P) = (term15 _27494 _27495 P).
Proof. exact (eq_refl (term27 _27494 _27495 P)). Qed.
Lemma lem1181634 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) : term15 _27494 _27495 P.
Proof. exact (EQ_MP (@lem1181633 _27494 _27495 P) (@lem1181632 _27494 _27495 P)). Qed.
Lemma lem1181635 {_27494 _27495 : Type'} (P : type1470 _27494 _27495) (l : list _27495) : term28 _27494 _27495 P l.
Proof. exact (@lem1181634 _27494 _27495 P l). Qed.
Lemma lem1181636 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : (term28 _27494 _27495 P l) = (term11 _27494 _27495 l P).
Proof. exact (eq_refl (term28 _27494 _27495 P l)). Qed.
Lemma lem1181637 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) : term11 _27494 _27495 l P.
Proof. exact (EQ_MP (@lem1181636 _27494 _27495 l P) (@lem1181635 _27494 _27495 P l)). Qed.
Lemma lem1181638 {_27494 _27495 : Type'} (l : list _27495) (P : type1470 _27494 _27495) (m : list _27494) : term29 _27494 _27495 l P m.
Proof. exact (@lem1181637 _27494 _27495 l P m). Qed.
Lemma lem1181639 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (term29 _27494 _27495 l P m) = ((@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P)).
Proof. exact (eq_refl (term29 _27494 _27495 l P m)). Qed.
Lemma lem1181656 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P).
Proof. exact (EQ_MP (@lem1181639 _27494 _27495 l m P) (@lem1181638 _27494 _27495 l P m)). Qed.
Lemma lem1181657 {_27538 _27539 : Type'} (l : list _27539) (m : list _27538) (P : type1470 _27538 _27539) : (@ALLPAIRS _27538 _27539 P l m) = (term7 _27538 _27539 l m P).
Proof. exact (@lem1181656 _27538 _27539 l m P). Qed.
Lemma lem1181658 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (l : list _27540) (g : _27541 -> _27538) (m : list _27541) (P : type1470 _27538 _27539) : (term30 _27538 _27539 _27540 _27541 P f l g m) = (term31 _27538 _27539 _27540 _27541 f l g m P).
Proof. exact (@lem1181657 _27538 _27539 (@List.map _27540 _27539 f l) (@List.map _27541 _27538 g m) P). Qed.
Lemma lem1181672 {_26978 _26981 : Type'} (l : list _26981) (y : _26978) (f : _26981 -> _26978) : (term25 _26978 _26981 y f l) = (term26 _26978 _26981 l y f).
Proof. exact (EQ_MP (@lem1181630 _26978 _26981 l y f) (@lem1181629 _26978 _26981 y f l)). Qed.
Lemma lem1181673 {_27539 _27540 : Type'} (l : list _27540) (y : _27539) (f : _27540 -> _27539) : (term25 _27539 _27540 y f l) = (term26 _27539 _27540 l y f).
Proof. exact (@lem1181672 _27539 _27540 l y f). Qed.
Lemma lem1181674 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term25 _27539 _27540 x f l) = (term26 _27539 _27540 l x f).
Proof. exact (@lem1181673 _27539 _27540 l x f). Qed.
Lemma lem1181683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1181684 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term32 _27539 _27540 x f l) = (term33 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1181683) (@lem1181674 _27539 _27540 l x f)). Qed.
Lemma lem1181686 {_26978 _26981 : Type'} (l : list _26981) (y : _26978) (f : _26981 -> _26978) : (term25 _26978 _26981 y f l) = (term26 _26978 _26981 l y f).
Proof. exact (EQ_MP (@lem1181630 _26978 _26981 l y f) (@lem1181629 _26978 _26981 y f l)). Qed.
Lemma lem1181687 {_27538 _27541 : Type'} (l : list _27541) (y : _27538) (f : _27541 -> _27538) : (term25 _27538 _27541 y f l) = (term26 _27538 _27541 l y f).
Proof. exact (@lem1181686 _27538 _27541 l y f). Qed.
Lemma lem1181688 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term25 _27538 _27541 y g m) = (term26 _27538 _27541 m y g).
Proof. exact (@lem1181687 _27538 _27541 m y g). Qed.
Lemma lem1181697 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term34 _27538 _27539 _27540 _27541 x f l y g m) = (term35 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1181684 _27539 _27540 l x f) (@lem1181688 _27538 _27541 m y g)). Qed.
Lemma lem1181700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1181701 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term36 _27538 _27539 _27540 _27541 x f l y g m) = (term37 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1181700) (@lem1181697 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1181702 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1181703 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term38 _27538 _27539 _27540 _27541 f l g m P x y) = (term39 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1181701 _27538 _27539 _27540 _27541 l x f m y g) (@lem1181702 _27538 _27539 P x y)). Qed.
Lemma lem1181706 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term40 _27538 _27539 _27540 _27541 f l g m P x) = (term41 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1181703 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1181707 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1181708 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term42 _27538 _27539 _27540 _27541 f l g m P x) = (term43 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1181707 _27538) (@lem1181706 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1181713 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term44 _27538 _27539 _27540 _27541 f l g m P) = (term45 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1181708 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1181714 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1181715 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term31 _27538 _27539 _27540 _27541 f l g m P) = (term46 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1181714 _27539) (@lem1181713 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1181720 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term30 _27538 _27539 _27540 _27541 P f l g m) = (term46 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (TRANS (@lem1181658 _27538 _27539 _27540 _27541 f l g m P) (@lem1181715 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1181721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181722 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term47 _27538 _27539 _27540 _27541 P f l g m) = (term48 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1181721) (@lem1181720 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1181724 {_27494 _27495 : Type'} (l : list _27495) (m : list _27494) (P : type1470 _27494 _27495) : (@ALLPAIRS _27494 _27495 P l m) = (term7 _27494 _27495 l m P).
Proof. exact (EQ_MP (@lem1181639 _27494 _27495 l m P) (@lem1181638 _27494 _27495 l P m)). Qed.
Lemma lem1181725 {_27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1413 _27540 _27541) : (@ALLPAIRS _27541 _27540 P l m) = (term49 _27540 _27541 l m P).
Proof. exact (@lem1181724 _27541 _27540 l m P). Qed.
Lemma lem1181726 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term50 _27538 _27539 _27540 _27541 P f g l m) = (term51 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1181725 _27540 _27541 l m (term52 _27538 _27539 _27540 _27541 P f g)). Qed.
Lemma lem1181740 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1181741 {_27540 _27541 : Type'} (f : type1413 _27540 _27541) (y : _27540) : (term54 _27540 _27541 f y) = (f y).
Proof. exact (@lem1181740 _27540 (_27541 -> Prop) f y). Qed.
Lemma lem1181742 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (x : _27540) : (term55 _27538 _27539 _27540 _27541 P f g x) = (term56 _27538 _27539 _27540 _27541 P f g x).
Proof. exact (@lem1181741 _27540 _27541 (term52 _27538 _27539 _27540 _27541 P f g) x). Qed.
Lemma lem1181743 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term56 _27538 _27539 _27540 _27541 P f g x) = (term57 _27538 _27539 _27540 _27541 P f x g).
Proof. exact (eq_refl (term56 _27538 _27539 _27540 _27541 P f g x)). Qed.
Lemma lem1181744 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term58 _27538 _27539 _27540 _27541 P f g) = (term52 _27538 _27539 _27540 _27541 P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1181743 _27538 _27539 _27540 _27541 P f x g)). Qed.
Lemma lem1181745 {_27540 : Type'} (x : _27540) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1181746 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (x : _27540) : (term55 _27538 _27539 _27540 _27541 P f g x) = (term56 _27538 _27539 _27540 _27541 P f g x).
Proof. exact (MK_COMB (@lem1181744 _27538 _27539 _27540 _27541 P f g) (@lem1181745 _27540 x)). Qed.
Lemma lem1181747 {_27541 : Type'} : (@eq (_27541 -> Prop)) = (@eq (_27541 -> Prop)).
Proof. exact (eq_refl (@eq (_27541 -> Prop))). Qed.
Lemma lem1181748 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (x : _27540) : (term59 _27538 _27539 _27540 _27541 P f g x) = (term60 _27538 _27539 _27540 _27541 P f g x).
Proof. exact (MK_COMB (@lem1181747 _27541) (@lem1181746 _27538 _27539 _27540 _27541 P f g x)). Qed.
Lemma lem1181749 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term56 _27538 _27539 _27540 _27541 P f g x) = (term57 _27538 _27539 _27540 _27541 P f x g).
Proof. exact (eq_refl (term56 _27538 _27539 _27540 _27541 P f g x)). Qed.
Lemma lem1181750 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : ((term55 _27538 _27539 _27540 _27541 P f g x) = (term56 _27538 _27539 _27540 _27541 P f g x)) = ((term56 _27538 _27539 _27540 _27541 P f g x) = (term57 _27538 _27539 _27540 _27541 P f x g)).
Proof. exact (MK_COMB (@lem1181748 _27538 _27539 _27540 _27541 P f g x) (@lem1181749 _27538 _27539 _27540 _27541 P f x g)). Qed.
Lemma lem1181751 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term56 _27538 _27539 _27540 _27541 P f g x) = (term57 _27538 _27539 _27540 _27541 P f x g).
Proof. exact (EQ_MP (@lem1181750 _27538 _27539 _27540 _27541 P f x g) (@lem1181742 _27538 _27539 _27540 _27541 P f g x)). Qed.
Lemma lem1181752 {_27541 : Type'} (y : _27541) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1181753 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term61 _27538 _27539 _27540 _27541 P f g x y) = (term62 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (MK_COMB (@lem1181751 _27538 _27539 _27540 _27541 P f x g) (@lem1181752 _27541 y)). Qed.
Lemma lem1181755 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1181756 {_27541 : Type'} (f : _27541 -> Prop) (y : _27541) : (term63 _27541 f y) = (f y).
Proof. exact (@lem1181755 _27541 Prop f y). Qed.
Lemma lem1181757 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term64 _27538 _27539 _27540 _27541 P f x g y) = (term62 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (@lem1181756 _27541 (term57 _27538 _27539 _27540 _27541 P f x g) y). Qed.
Lemma lem1181758 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term62 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (eq_refl (term62 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181759 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term66 _27538 _27539 _27540 _27541 P f x g) = (term57 _27538 _27539 _27540 _27541 P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1181758 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181760 {_27541 : Type'} (y : _27541) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1181761 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term64 _27538 _27539 _27540 _27541 P f x g y) = (term62 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (MK_COMB (@lem1181759 _27538 _27539 _27540 _27541 P f x g) (@lem1181760 _27541 y)). Qed.
Lemma lem1181762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1181763 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term67 _27538 _27539 _27540 _27541 P f x g y) = (term68 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (MK_COMB (@lem1181762) (@lem1181761 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181764 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term62 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (eq_refl (term62 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181765 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : ((term64 _27538 _27539 _27540 _27541 P f x g y) = (term62 _27538 _27539 _27540 _27541 P f x g y)) = ((term62 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y)).
Proof. exact (MK_COMB (@lem1181763 _27538 _27539 _27540 _27541 P f x g y) (@lem1181764 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181766 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term62 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (EQ_MP (@lem1181765 _27538 _27539 _27540 _27541 P f x g y) (@lem1181757 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181767 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term61 _27538 _27539 _27540 _27541 P f g x y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (TRANS (@lem1181753 _27538 _27539 _27540 _27541 P f x g y) (@lem1181766 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181768 {_27540 _27541 : Type'} (x : _27540) (l : list _27540) (y : _27541) (m : list _27541) : (term69 _27540 _27541 x l y m) = (term69 _27540 _27541 x l y m).
Proof. exact (eq_refl (term69 _27540 _27541 x l y m)). Qed.
Lemma lem1181769 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term70 _27538 _27539 _27540 _27541 l m P f g x y) = (term71 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1181768 _27540 _27541 x l y m) (@lem1181767 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1181772 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term72 _27538 _27539 _27540 _27541 l m P f g x) = (term73 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1181769 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1181773 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1181774 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term74 _27538 _27539 _27540 _27541 l m P f g x) = (term75 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1181773 _27541) (@lem1181772 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1181779 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term76 _27538 _27539 _27540 _27541 l m P f g) = (term77 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1181774 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1181780 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1181781 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term51 _27538 _27539 _27540 _27541 l m P f g) = (term78 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1181780 _27540) (@lem1181779 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1181786 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term50 _27538 _27539 _27540 _27541 P f g l m) = (term78 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1181726 _27538 _27539 _27540 _27541 l m P f g) (@lem1181781 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1181787 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term30 _27538 _27539 _27540 _27541 P f l g m) = (term50 _27538 _27539 _27540 _27541 P f g l m)) = ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (MK_COMB (@lem1181722 _27538 _27539 _27540 _27541 l f m g P) (@lem1181786 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1181790 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term79 _27538 _27539 _27540 _27541 P f g l) = (term80 _27538 _27539 _27540 _27541 l P f g).
Proof. exact (fun_ext (fun m : list _27541 => @lem1181787 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1181791 {_27541 : Type'} : (@all (list _27541)) = (@all (list _27541)).
Proof. exact (eq_refl (@all (list _27541))). Qed.
Lemma lem1181792 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term81 _27538 _27539 _27540 _27541 P f g l) = (term82 _27538 _27539 _27540 _27541 l P f g).
Proof. exact (MK_COMB (@lem1181791 _27541) (@lem1181790 _27538 _27539 _27540 _27541 l P f g)). Qed.
Lemma lem1181797 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term83 _27538 _27539 _27540 _27541 P f g) = (term84 _27538 _27539 _27540 _27541 P f g).
Proof. exact (fun_ext (fun l : list _27540 => @lem1181792 _27538 _27539 _27540 _27541 l P f g)). Qed.
Lemma lem1181798 {_27540 : Type'} : (@all (list _27540)) = (@all (list _27540)).
Proof. exact (eq_refl (@all (list _27540))). Qed.
Lemma lem1181799 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term85 _27538 _27539 _27540 _27541 P f g) = (term86 _27538 _27539 _27540 _27541 P f g).
Proof. exact (MK_COMB (@lem1181798 _27540) (@lem1181797 _27538 _27539 _27540 _27541 P f g)). Qed.
Lemma lem1181804 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term87 _27538 _27539 _27540 _27541 f g) = (term88 _27538 _27539 _27540 _27541 f g).
Proof. exact (fun_ext (fun P : type1470 _27538 _27539 => @lem1181799 _27538 _27539 _27540 _27541 P f g)). Qed.
Lemma lem1181805 {_27538 _27539 : Type'} : (@all (_27539 -> _27538 -> Prop)) = (@all (_27539 -> _27538 -> Prop)).
Proof. exact (eq_refl (@all (_27539 -> _27538 -> Prop))). Qed.
Lemma lem1181806 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term89 _27538 _27539 _27540 _27541 f g) = (term90 _27538 _27539 _27540 _27541 f g).
Proof. exact (MK_COMB (@lem1181805 _27538 _27539) (@lem1181804 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181811 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term90 _27538 _27539 _27540 _27541 f g) = (term89 _27538 _27539 _27540 _27541 f g).
Proof. exact (SYM (@lem1181806 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181813 (p : Prop) : p = (term91 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1181814 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term90 _27538 _27539 _27540 _27541 f g) = (term92 _27538 _27539 _27540 _27541 f g).
Proof. exact (@lem1181813 (term90 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181815 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term92 _27538 _27539 _27540 _27541 f g) = (term90 _27538 _27539 _27540 _27541 f g).
Proof. exact (SYM (@lem1181814 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181816 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term93 _27538 _27539 _27540 _27541 f g) : term93 _27538 _27539 _27540 _27541 f g.
Proof. exact (h1). Qed.
Lemma lem1181819 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term92 _27538 _27539 _27540 _27541 f g) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (h1). Qed.
Lemma lem1181820 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun h0 : term92 _27538 _27539 _27540 _27541 f g => @lem1181819 _27538 _27539 _27540 _27541 f g h0). Qed.
Lemma lem1181821 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term94 _27538 _27539 _27540 _27541 f g) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (h1). Qed.
Lemma lem1181822 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term92 _27538 _27539 _27540 _27541 f g) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (h1). Qed.
Lemma lem1181823 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term92 _27538 _27539 _27540 _27541 f g) (h2 : term94 _27538 _27539 _27540 _27541 f g) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (@lem1181821 _27538 _27539 _27540 _27541 f g h2 (@lem1181822 _27538 _27539 _27540 _27541 f g h1)). Qed.
Lemma lem1181824 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term92 _27538 _27539 _27540 _27541 f g) : term95 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun h0 : term94 _27538 _27539 _27540 _27541 f g => @lem1181823 _27538 _27539 _27540 _27541 f g h1 h0). Qed.
Lemma lem1181825 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term94 _27538 _27539 _27540 _27541 f g) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (h1). Qed.
Lemma lem1181826 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term92 _27538 _27539 _27540 _27541 f g) (h2 : term94 _27538 _27539 _27540 _27541 f g) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (@lem1181824 _27538 _27539 _27540 _27541 f g h1 (@lem1181825 _27538 _27539 _27540 _27541 f g h2)). Qed.
Lemma lem1181827 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term94 _27538 _27539 _27540 _27541 f g) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun h0 : term92 _27538 _27539 _27540 _27541 f g => @lem1181826 _27538 _27539 _27540 _27541 f g h0 h1). Qed.
Lemma lem1181828 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term96 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun h0 : term94 _27538 _27539 _27540 _27541 f g => @lem1181827 _27538 _27539 _27540 _27541 f g h0). Qed.
Lemma lem1181831 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (@lem1181828 _27538 _27539 _27540 _27541 f g (@lem1181820 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181832 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term94 _27538 _27539 _27540 _27541 f g.
Proof. exact (@lem1181831 _27538 _27539 _27540 _27541 f g). Qed.
Lemma lem1181842 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1181843 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term92 _27538 _27539 _27540 _27541 f g) = (term97 _27538 _27539 _27540 _27541 f g).
Proof. exact (@lem1181842 (term93 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181845 (t : Prop) : (term98 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1181846 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term97 _27538 _27539 _27540 _27541 f g) = (term90 _27538 _27539 _27540 _27541 f g).
Proof. exact (@lem1181845 (term90 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181851 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term92 _27538 _27539 _27540 _27541 f g) = (term90 _27538 _27539 _27540 _27541 f g).
Proof. exact (TRANS (@lem1181843 _27538 _27539 _27540 _27541 f g) (@lem1181846 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181984 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : (term99 _27538 _27539 _27540 _27541 g) = (term100 _27538 _27539 _27540 _27541 g).
Proof. exact (fun_ext (fun f : _27540 -> _27539 => @lem1181851 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1181985 {_27539 _27540 : Type'} : (@all (_27540 -> _27539)) = (@all (_27540 -> _27539)).
Proof. exact (eq_refl (@all (_27540 -> _27539))). Qed.
Lemma lem1181986 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : (term101 _27538 _27539 _27540 _27541 g) = (term102 _27538 _27539 _27540 _27541 g).
Proof. exact (MK_COMB (@lem1181985 _27539 _27540) (@lem1181984 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1181991 {_27538 _27539 _27540 _27541 : Type'} : (term103 _27538 _27539 _27540 _27541) = (term104 _27538 _27539 _27540 _27541).
Proof. exact (fun_ext (fun g : _27541 -> _27538 => @lem1181986 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1181992 {_27538 _27541 : Type'} : (@all (_27541 -> _27538)) = (@all (_27541 -> _27538)).
Proof. exact (eq_refl (@all (_27541 -> _27538))). Qed.
Lemma lem1182001 {_27538 _27539 _27540 _27541 : Type'} : (term105 _27538 _27539 _27540 _27541) = (term106 _27538 _27539 _27540 _27541).
Proof. exact (MK_COMB (@lem1181992 _27538 _27541) (@lem1181991 _27538 _27539 _27540 _27541)). Qed.
Lemma lem1182010 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term71 _27538 _27539 _27540 _27541 l m P f x g y) = (term71 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term71 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182011 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term73 _27538 _27539 _27540 _27541 l m P f x g) = (term73 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1182010 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182012 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1182013 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term75 _27538 _27539 _27540 _27541 l m P f x g) = (term75 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182012 _27541) (@lem1182011 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182014 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term77 _27538 _27539 _27540 _27541 l m P f g) = (term77 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182013 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182015 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1182016 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term78 _27538 _27539 _27540 _27541 l m P f g) = (term78 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182015 _27540) (@lem1182014 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182017 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1182022 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term107 _27538 _27541 m y g x) = (term107 _27538 _27541 m y g x).
Proof. exact (eq_refl (term107 _27538 _27541 m y g x)). Qed.
Lemma lem1182023 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term108 _27538 _27541 m y g) = (term108 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1182022 _27538 _27541 m y g x)). Qed.
Lemma lem1182024 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182025 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term26 _27538 _27541 m y g) = (term26 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1182024 _27541) (@lem1182023 _27538 _27541 m y g)). Qed.
Lemma lem1182030 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term107 _27539 _27540 l x f x') = (term107 _27539 _27540 l x f x').
Proof. exact (eq_refl (term107 _27539 _27540 l x f x')). Qed.
Lemma lem1182031 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term108 _27539 _27540 l x f) = (term108 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182030 _27539 _27540 l x f x')). Qed.
Lemma lem1182032 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182033 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term26 _27539 _27540 l x f) = (term26 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182032 _27540) (@lem1182031 _27539 _27540 l x f)). Qed.
Lemma lem1182034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182035 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term33 _27539 _27540 l x f) = (term33 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182034) (@lem1182033 _27539 _27540 l x f)). Qed.
Lemma lem1182036 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term35 _27538 _27539 _27540 _27541 l x f m y g) = (term35 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182035 _27539 _27540 l x f) (@lem1182025 _27538 _27541 m y g)). Qed.
Lemma lem1182037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1182038 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term37 _27538 _27539 _27540 _27541 l x f m y g) = (term37 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182037) (@lem1182036 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182039 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term39 _27538 _27539 _27540 _27541 l f m g P x y) = (term39 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182038 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182017 _27538 _27539 P x y)). Qed.
Lemma lem1182040 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term41 _27538 _27539 _27540 _27541 l f m g P x) = (term41 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1182039 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182041 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1182042 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term43 _27538 _27539 _27540 _27541 l f m g P x) = (term43 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182041 _27538) (@lem1182040 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182043 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term45 _27538 _27539 _27540 _27541 l f m g P) = (term45 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1182042 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182044 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1182045 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term46 _27538 _27539 _27540 _27541 l f m g P) = (term46 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182044 _27539) (@lem1182043 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182047 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term48 _27538 _27539 _27540 _27541 l f m g P) = (term48 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182046) (@lem1182045 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182048 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g)) = ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (MK_COMB (@lem1182047 _27538 _27539 _27540 _27541 l f m g P) (@lem1182016 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182049 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term80 _27538 _27539 _27540 _27541 l P f g) = (term80 _27538 _27539 _27540 _27541 l P f g).
Proof. exact (fun_ext (fun m : list _27541 => @lem1182048 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182050 {_27541 : Type'} : (@all (list _27541)) = (@all (list _27541)).
Proof. exact (eq_refl (@all (list _27541))). Qed.
Lemma lem1182051 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term82 _27538 _27539 _27540 _27541 l P f g) = (term82 _27538 _27539 _27540 _27541 l P f g).
Proof. exact (MK_COMB (@lem1182050 _27541) (@lem1182049 _27538 _27539 _27540 _27541 l P f g)). Qed.
Lemma lem1182052 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term84 _27538 _27539 _27540 _27541 P f g) = (term84 _27538 _27539 _27540 _27541 P f g).
Proof. exact (fun_ext (fun l : list _27540 => @lem1182051 _27538 _27539 _27540 _27541 l P f g)). Qed.
Lemma lem1182053 {_27540 : Type'} : (@all (list _27540)) = (@all (list _27540)).
Proof. exact (eq_refl (@all (list _27540))). Qed.
Lemma lem1182054 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term86 _27538 _27539 _27540 _27541 P f g) = (term86 _27538 _27539 _27540 _27541 P f g).
Proof. exact (MK_COMB (@lem1182053 _27540) (@lem1182052 _27538 _27539 _27540 _27541 P f g)). Qed.
Lemma lem1182055 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term88 _27538 _27539 _27540 _27541 f g) = (term88 _27538 _27539 _27540 _27541 f g).
Proof. exact (fun_ext (fun P : type1470 _27538 _27539 => @lem1182054 _27538 _27539 _27540 _27541 P f g)). Qed.
Lemma lem1182056 {_27538 _27539 : Type'} : (@all (_27539 -> _27538 -> Prop)) = (@all (_27539 -> _27538 -> Prop)).
Proof. exact (eq_refl (@all (_27539 -> _27538 -> Prop))). Qed.
Lemma lem1182057 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term90 _27538 _27539 _27540 _27541 f g) = (term90 _27538 _27539 _27540 _27541 f g).
Proof. exact (MK_COMB (@lem1182056 _27538 _27539) (@lem1182055 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1182058 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : (term100 _27538 _27539 _27540 _27541 g) = (term100 _27538 _27539 _27540 _27541 g).
Proof. exact (fun_ext (fun f : _27540 -> _27539 => @lem1182057 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1182059 {_27539 _27540 : Type'} : (@all (_27540 -> _27539)) = (@all (_27540 -> _27539)).
Proof. exact (eq_refl (@all (_27540 -> _27539))). Qed.
Lemma lem1182060 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : (term102 _27538 _27539 _27540 _27541 g) = (term102 _27538 _27539 _27540 _27541 g).
Proof. exact (MK_COMB (@lem1182059 _27539 _27540) (@lem1182058 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1182061 {_27538 _27539 _27540 _27541 : Type'} : (term104 _27538 _27539 _27540 _27541) = (term104 _27538 _27539 _27540 _27541).
Proof. exact (fun_ext (fun g : _27541 -> _27538 => @lem1182060 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1182062 {_27538 _27541 : Type'} : (@all (_27541 -> _27538)) = (@all (_27541 -> _27538)).
Proof. exact (eq_refl (@all (_27541 -> _27538))). Qed.
Lemma lem1182063 {_27538 _27539 _27540 _27541 : Type'} : (term106 _27538 _27539 _27540 _27541) = (term106 _27538 _27539 _27540 _27541).
Proof. exact (MK_COMB (@lem1182062 _27538 _27541) (@lem1182061 _27538 _27539 _27540 _27541)). Qed.
Lemma lem1182144 {_27538 _27539 _27540 _27541 : Type'} : (term105 _27538 _27539 _27540 _27541) = (term106 _27538 _27539 _27540 _27541).
Proof. exact (TRANS (@lem1182001 _27538 _27539 _27540 _27541) (@lem1182063 _27538 _27539 _27540 _27541)). Qed.
Lemma lem1182145 {_27538 _27539 _27540 _27541 : Type'} : (term106 _27538 _27539 _27540 _27541) = (term105 _27538 _27539 _27540 _27541).
Proof. exact (SYM (@lem1182144 _27538 _27539 _27540 _27541)). Qed.
Lemma lem1182147 (p : Prop) : p = (term91 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1182148 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g)) = (term109 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1182147 ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g))). Qed.
Lemma lem1182149 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term109 _27538 _27539 _27540 _27541 l m P f g) = ((term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (SYM (@lem1182148 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182150 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term110 _27538 _27539 _27540 _27541 l m P f g) : term110 _27538 _27539 _27540 _27541 l m P f g.
Proof. exact (h1). Qed.
Lemma lem1182159 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term111 _27539 _27540 l x f x') = (term112 _27539 _27540 l x f x').
Proof. exact (@lem17045 (@List.In _27540 x' l) (x = (f x'))). Qed.
Lemma lem1182162 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term107 _27539 _27540 l x f x') = (term107 _27539 _27540 l x f x').
Proof. exact (eq_refl (term107 _27539 _27540 l x f x')). Qed.
Lemma lem1182163 {_27540 : Type'} (P : _27540 -> Prop) : (term113 _27540 P) = (term114 _27540 P).
Proof. exact (@lem18394 _27540 P). Qed.
Lemma lem1182164 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term115 _27539 _27540 l x f) = (term116 _27539 _27540 l x f).
Proof. exact (@lem1182163 _27540 (term108 _27539 _27540 l x f)). Qed.
Lemma lem1182165 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term117 _27539 _27540 l x f x') = (term107 _27539 _27540 l x f x').
Proof. exact (eq_refl (term117 _27539 _27540 l x f x')). Qed.
Lemma lem1182166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182167 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term118 _27539 _27540 l x f x') = (term111 _27539 _27540 l x f x').
Proof. exact (MK_COMB (@lem1182166) (@lem1182165 _27539 _27540 l x f x')). Qed.
Lemma lem1182168 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term118 _27539 _27540 l x f x') = (term112 _27539 _27540 l x f x').
Proof. exact (TRANS (@lem1182167 _27539 _27540 l x f x') (@lem1182159 _27539 _27540 l x f x')). Qed.
Lemma lem1182169 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term119 _27539 _27540 l x f) = (term120 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182168 _27539 _27540 l x f x')). Qed.
Lemma lem1182170 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1182171 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term116 _27539 _27540 l x f) = (term121 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182170 _27540) (@lem1182169 _27539 _27540 l x f)). Qed.
Lemma lem1182172 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term115 _27539 _27540 l x f) = (term121 _27539 _27540 l x f).
Proof. exact (TRANS (@lem1182164 _27539 _27540 l x f) (@lem1182171 _27539 _27540 l x f)). Qed.
Lemma lem1182173 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term108 _27539 _27540 l x f) = (term108 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182162 _27539 _27540 l x f x')). Qed.
Lemma lem1182174 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182175 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term26 _27539 _27540 l x f) = (term26 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182174 _27540) (@lem1182173 _27539 _27540 l x f)). Qed.
Lemma lem1182184 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term111 _27538 _27541 m y g x) = (term112 _27538 _27541 m y g x).
Proof. exact (@lem17045 (@List.In _27541 x m) (y = (g x))). Qed.
Lemma lem1182187 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term107 _27538 _27541 m y g x) = (term107 _27538 _27541 m y g x).
Proof. exact (eq_refl (term107 _27538 _27541 m y g x)). Qed.
Lemma lem1182188 {_27541 : Type'} (P : _27541 -> Prop) : (term113 _27541 P) = (term114 _27541 P).
Proof. exact (@lem18394 _27541 P). Qed.
Lemma lem1182189 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term115 _27538 _27541 m y g) = (term116 _27538 _27541 m y g).
Proof. exact (@lem1182188 _27541 (term108 _27538 _27541 m y g)). Qed.
Lemma lem1182190 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term117 _27538 _27541 m y g x) = (term107 _27538 _27541 m y g x).
Proof. exact (eq_refl (term117 _27538 _27541 m y g x)). Qed.
Lemma lem1182191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182192 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term118 _27538 _27541 m y g x) = (term111 _27538 _27541 m y g x).
Proof. exact (MK_COMB (@lem1182191) (@lem1182190 _27538 _27541 m y g x)). Qed.
Lemma lem1182193 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term118 _27538 _27541 m y g x) = (term112 _27538 _27541 m y g x).
Proof. exact (TRANS (@lem1182192 _27538 _27541 m y g x) (@lem1182184 _27538 _27541 m y g x)). Qed.
Lemma lem1182194 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term119 _27538 _27541 m y g) = (term120 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1182193 _27538 _27541 m y g x)). Qed.
Lemma lem1182195 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1182196 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term116 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1182195 _27541) (@lem1182194 _27538 _27541 m y g)). Qed.
Lemma lem1182197 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term115 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (TRANS (@lem1182189 _27538 _27541 m y g) (@lem1182196 _27538 _27541 m y g)). Qed.
Lemma lem1182198 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term108 _27538 _27541 m y g) = (term108 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1182187 _27538 _27541 m y g x)). Qed.
Lemma lem1182199 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182200 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term26 _27538 _27541 m y g) = (term26 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1182199 _27541) (@lem1182198 _27538 _27541 m y g)). Qed.
Lemma lem1182201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182202 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term122 _27539 _27540 l x f) = (term123 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182201) (@lem1182172 _27539 _27540 l x f)). Qed.
Lemma lem1182203 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term124 _27538 _27539 _27540 _27541 l x f m y g) = (term125 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182202 _27539 _27540 l x f) (@lem1182197 _27538 _27541 m y g)). Qed.
Lemma lem1182204 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term126 _27538 _27539 _27540 _27541 l x f m y g) = (term124 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (@lem17045 (term26 _27539 _27540 l x f) (term26 _27538 _27541 m y g)). Qed.
Lemma lem1182205 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term126 _27538 _27539 _27540 _27541 l x f m y g) = (term125 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (TRANS (@lem1182204 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182203 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182207 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term33 _27539 _27540 l x f) = (term33 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182206) (@lem1182175 _27539 _27540 l x f)). Qed.
Lemma lem1182208 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term35 _27538 _27539 _27540 _27541 l x f m y g) = (term35 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182207 _27539 _27540 l x f) (@lem1182200 _27538 _27541 m y g)). Qed.
Lemma lem1182209 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182210 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1182211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182212 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term128 _27538 _27539 _27540 _27541 l x f m y g) = (term128 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182211) (@lem1182208 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182213 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term129 _27538 _27539 _27540 _27541 l f m g P x y) = (term129 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182212 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182209 _27538 _27539 P x y)). Qed.
Lemma lem1182214 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term130 _27538 _27539 _27540 _27541 l f m g P x y) = (term129 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (@lem17362 (term35 _27538 _27539 _27540 _27541 l x f m y g) (P x y)). Qed.
Lemma lem1182215 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term130 _27538 _27539 _27540 _27541 l f m g P x y) = (term129 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1182214 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182213 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182217 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term131 _27538 _27539 _27540 _27541 l x f m y g) = (term132 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182216) (@lem1182205 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182218 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term133 _27538 _27539 _27540 _27541 l f m g P x y) = (term134 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182217 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182210 _27538 _27539 P x y)). Qed.
Lemma lem1182219 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term39 _27538 _27539 _27540 _27541 l f m g P x y) = (term133 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (@lem17265 (term35 _27538 _27539 _27540 _27541 l x f m y g) (P x y)). Qed.
Lemma lem1182220 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term39 _27538 _27539 _27540 _27541 l f m g P x y) = (term134 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1182219 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182218 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182221 {_27538 : Type'} (P : _27538 -> Prop) : (term135 _27538 P) = (term136 _27538 P).
Proof. exact (@lem18392 _27538 P). Qed.
Lemma lem1182222 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term137 _27538 _27539 _27540 _27541 l f m g P x) = (term138 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (@lem1182221 _27538 (term41 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182223 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term139 _27538 _27539 _27540 _27541 l f m g P x y) = (term39 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (eq_refl (term139 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182225 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term140 _27538 _27539 _27540 _27541 l f m g P x y) = (term130 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182224) (@lem1182223 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182226 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term140 _27538 _27539 _27540 _27541 l f m g P x y) = (term129 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1182225 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182215 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182227 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term141 _27538 _27539 _27540 _27541 l f m g P x) = (term142 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1182226 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182228 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1182229 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term138 _27538 _27539 _27540 _27541 l f m g P x) = (term143 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182228 _27538) (@lem1182227 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182230 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term137 _27538 _27539 _27540 _27541 l f m g P x) = (term143 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (TRANS (@lem1182222 _27538 _27539 _27540 _27541 l f m g P x) (@lem1182229 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182231 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term41 _27538 _27539 _27540 _27541 l f m g P x) = (term144 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1182220 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182232 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1182233 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term43 _27538 _27539 _27540 _27541 l f m g P x) = (term145 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182232 _27538) (@lem1182231 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182234 {_27539 : Type'} (P : _27539 -> Prop) : (term135 _27539 P) = (term136 _27539 P).
Proof. exact (@lem18392 _27539 P). Qed.
Lemma lem1182235 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term146 _27538 _27539 _27540 _27541 l f m g P) = (term147 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (@lem1182234 _27539 (term45 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182236 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term148 _27538 _27539 _27540 _27541 l f m g P x) = (term43 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (eq_refl (term148 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182238 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term149 _27538 _27539 _27540 _27541 l f m g P x) = (term137 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182237) (@lem1182236 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182239 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term149 _27538 _27539 _27540 _27541 l f m g P x) = (term143 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (TRANS (@lem1182238 _27538 _27539 _27540 _27541 l f m g P x) (@lem1182230 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182240 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term150 _27538 _27539 _27540 _27541 l f m g P) = (term151 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1182239 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182241 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1182242 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term147 _27538 _27539 _27540 _27541 l f m g P) = (term152 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182241 _27539) (@lem1182240 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182243 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term146 _27538 _27539 _27540 _27541 l f m g P) = (term152 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (TRANS (@lem1182235 _27538 _27539 _27540 _27541 l f m g P) (@lem1182242 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182244 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term45 _27538 _27539 _27540 _27541 l f m g P) = (term153 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1182233 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182245 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1182246 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term46 _27538 _27539 _27540 _27541 l f m g P) = (term154 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182245 _27539) (@lem1182244 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182255 {_27540 _27541 : Type'} (x : _27540) (l : list _27540) (y : _27541) (m : list _27541) : (term155 _27540 _27541 x l y m) = (term156 _27540 _27541 x l y m).
Proof. exact (@lem17045 (@List.In _27540 x l) (@List.In _27541 y m)). Qed.
Lemma lem1182260 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term65 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (eq_refl (term65 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1182265 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term157 _27538 _27539 _27540 _27541 l m P f x g y) = (term158 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (@lem17362 (term159 _27540 _27541 x l y m) (term65 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1182266 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182267 {_27540 _27541 : Type'} (x : _27540) (l : list _27540) (y : _27541) (m : list _27541) : (term160 _27540 _27541 x l y m) = (term161 _27540 _27541 x l y m).
Proof. exact (MK_COMB (@lem1182266) (@lem1182255 _27540 _27541 x l y m)). Qed.
Lemma lem1182268 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term162 _27538 _27539 _27540 _27541 l m P f x g y) = (term163 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1182267 _27540 _27541 x l y m) (@lem1182260 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1182269 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term71 _27538 _27539 _27540 _27541 l m P f x g y) = (term162 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (@lem17265 (term159 _27540 _27541 x l y m) (term65 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1182270 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term71 _27538 _27539 _27540 _27541 l m P f x g y) = (term163 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (TRANS (@lem1182269 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1182268 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182271 {_27541 : Type'} (P : _27541 -> Prop) : (term135 _27541 P) = (term136 _27541 P).
Proof. exact (@lem18392 _27541 P). Qed.
Lemma lem1182272 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term164 _27538 _27539 _27540 _27541 l m P f x g) = (term165 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (@lem1182271 _27541 (term73 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182273 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term166 _27538 _27539 _27540 _27541 l m P f x g y) = (term71 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term166 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182274 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182275 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term167 _27538 _27539 _27540 _27541 l m P f x g y) = (term157 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1182274) (@lem1182273 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182276 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term167 _27538 _27539 _27540 _27541 l m P f x g y) = (term158 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (TRANS (@lem1182275 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1182265 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182277 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term168 _27538 _27539 _27540 _27541 l m P f x g) = (term169 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1182276 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182278 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182279 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term165 _27538 _27539 _27540 _27541 l m P f x g) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182278 _27541) (@lem1182277 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182280 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term164 _27538 _27539 _27540 _27541 l m P f x g) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (TRANS (@lem1182272 _27538 _27539 _27540 _27541 l m P f x g) (@lem1182279 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182281 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term73 _27538 _27539 _27540 _27541 l m P f x g) = (term171 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1182270 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182282 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1182283 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term75 _27538 _27539 _27540 _27541 l m P f x g) = (term172 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182282 _27541) (@lem1182281 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182284 {_27540 : Type'} (P : _27540 -> Prop) : (term135 _27540 P) = (term136 _27540 P).
Proof. exact (@lem18392 _27540 P). Qed.
Lemma lem1182285 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term173 _27538 _27539 _27540 _27541 l m P f g) = (term174 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1182284 _27540 (term77 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182286 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term175 _27538 _27539 _27540 _27541 l m P f g x) = (term75 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (eq_refl (term175 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1182287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1182288 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term176 _27538 _27539 _27540 _27541 l m P f g x) = (term164 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182287) (@lem1182286 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182289 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term176 _27538 _27539 _27540 _27541 l m P f g x) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (TRANS (@lem1182288 _27538 _27539 _27540 _27541 l m P f x g) (@lem1182280 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182290 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term177 _27538 _27539 _27540 _27541 l m P f g) = (term178 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182289 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182291 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182292 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term174 _27538 _27539 _27540 _27541 l m P f g) = (term179 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182291 _27540) (@lem1182290 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182293 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term173 _27538 _27539 _27540 _27541 l m P f g) = (term179 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182285 _27538 _27539 _27540 _27541 l m P f g) (@lem1182292 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182294 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term77 _27538 _27539 _27540 _27541 l m P f g) = (term180 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182283 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182295 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1182296 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term78 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182295 _27540) (@lem1182294 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182298 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term182 _27538 _27539 _27540 _27541 l f m g P) = (term183 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182297) (@lem1182243 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182299 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term184 _27538 _27539 _27540 _27541 l m P f g) = (term185 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182298 _27538 _27539 _27540 _27541 l f m g P) (@lem1182296 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182301 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term186 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182300) (@lem1182246 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182302 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term188 _27538 _27539 _27540 _27541 l m P f g) = (term189 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182301 _27538 _27539 _27540 _27541 l f m g P) (@lem1182293 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182304 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term190 _27538 _27539 _27540 _27541 l m P f g) = (term191 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182303) (@lem1182302 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182305 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term192 _27538 _27539 _27540 _27541 l m P f g) = (term193 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182304 _27538 _27539 _27540 _27541 l m P f g) (@lem1182299 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182306 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term110 _27538 _27539 _27540 _27541 l m P f g) = (term192 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem17646 (term46 _27538 _27539 _27540 _27541 l f m g P) (term78 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182307 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term110 _27538 _27539 _27540 _27541 l m P f g) = (term193 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182306 _27538 _27539 _27540 _27541 l m P f g) (@lem1182305 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182710 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1182711 {_27540 : Type'} (P : Prop) (Q : _27540 -> Prop) : (term194 _27540 P Q) = (term195 _27540 P Q).
Proof. exact (@lem1182710 _27540 P Q). Qed.
Lemma lem1182712 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term196 _27538 _27539 _27540 _27541 l m P f g) = (term197 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1182711 _27540 (term154 _27538 _27539 _27540 _27541 l f m g P) (term178 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182713 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term198 _27538 _27539 _27540 _27541 l m P f g x) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (eq_refl (term198 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1182714 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term199 _27538 _27539 _27540 _27541 l m P f g) = (term178 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182713 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182715 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182716 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term200 _27538 _27539 _27540 _27541 l m P f g) = (term179 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182715 _27540) (@lem1182714 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182717 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term187 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (eq_refl (term187 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182718 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term196 _27538 _27539 _27540 _27541 l m P f g) = (term189 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182717 _27538 _27539 _27540 _27541 l f m g P) (@lem1182716 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182720 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term201 _27538 _27539 _27540 _27541 l m P f g) = (term202 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182719) (@lem1182718 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182721 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term198 _27538 _27539 _27540 _27541 l m P f g x) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (eq_refl (term198 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1182722 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term187 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (eq_refl (term187 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182723 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term203 _27538 _27539 _27540 _27541 l m P f g x) = (term204 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182722 _27538 _27539 _27540 _27541 l f m g P) (@lem1182721 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182724 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term205 _27538 _27539 _27540 _27541 l m P f g) = (term206 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182723 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182725 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182726 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term197 _27538 _27539 _27540 _27541 l m P f g) = (term207 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182725 _27540) (@lem1182724 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182727 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term196 _27538 _27539 _27540 _27541 l m P f g) = (term197 _27538 _27539 _27540 _27541 l m P f g)) = ((term189 _27538 _27539 _27540 _27541 l m P f g) = (term207 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (MK_COMB (@lem1182720 _27538 _27539 _27540 _27541 l m P f g) (@lem1182726 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182728 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term189 _27538 _27539 _27540 _27541 l m P f g) = (term207 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (EQ_MP (@lem1182727 _27538 _27539 _27540 _27541 l m P f g) (@lem1182712 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182730 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1182731 {_27541 : Type'} (P : Prop) (Q : _27541 -> Prop) : (term194 _27541 P Q) = (term195 _27541 P Q).
Proof. exact (@lem1182730 _27541 P Q). Qed.
Lemma lem1182732 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term208 _27538 _27539 _27540 _27541 l m P f x g) = (term209 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (@lem1182731 _27541 (term154 _27538 _27539 _27540 _27541 l f m g P) (term169 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182733 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term210 _27538 _27539 _27540 _27541 l m P f x g y) = (term158 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term210 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182734 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term211 _27538 _27539 _27540 _27541 l m P f x g) = (term169 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1182733 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182735 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182736 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term212 _27538 _27539 _27540 _27541 l m P f x g) = (term170 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182735 _27541) (@lem1182734 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182737 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term187 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (eq_refl (term187 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182738 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term208 _27538 _27539 _27540 _27541 l m P f x g) = (term204 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182737 _27538 _27539 _27540 _27541 l f m g P) (@lem1182736 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182740 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term213 _27538 _27539 _27540 _27541 l m P f x g) = (term214 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182739) (@lem1182738 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182741 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term210 _27538 _27539 _27540 _27541 l m P f x g y) = (term158 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term210 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182742 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term187 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (eq_refl (term187 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182743 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term215 _27538 _27539 _27540 _27541 l m P f x g y) = (term216 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1182742 _27538 _27539 _27540 _27541 l f m g P) (@lem1182741 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182744 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term217 _27538 _27539 _27540 _27541 l m P f x g) = (term218 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1182743 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1182745 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182746 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term209 _27538 _27539 _27540 _27541 l m P f x g) = (term219 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182745 _27541) (@lem1182744 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182747 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : ((term208 _27538 _27539 _27540 _27541 l m P f x g) = (term209 _27538 _27539 _27540 _27541 l m P f x g)) = ((term204 _27538 _27539 _27540 _27541 l m P f x g) = (term219 _27538 _27539 _27540 _27541 l m P f x g)).
Proof. exact (MK_COMB (@lem1182740 _27538 _27539 _27540 _27541 l m P f x g) (@lem1182746 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182748 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term204 _27538 _27539 _27540 _27541 l m P f x g) = (term219 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (EQ_MP (@lem1182747 _27538 _27539 _27540 _27541 l m P f x g) (@lem1182732 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182749 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term206 _27538 _27539 _27540 _27541 l m P f g) = (term220 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182748 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182750 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182751 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term207 _27538 _27539 _27540 _27541 l m P f g) = (term221 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182750 _27540) (@lem1182749 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182752 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term189 _27538 _27539 _27540 _27541 l m P f g) = (term221 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182728 _27538 _27539 _27540 _27541 l m P f g) (@lem1182751 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182754 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term191 _27538 _27539 _27540 _27541 l m P f g) = (term222 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182753) (@lem1182752 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182756 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182757 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term223 _27540 P Q) = (term224 _27540 P Q).
Proof. exact (@lem1182756 _27540 P Q). Qed.
Lemma lem1182758 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term225 _27538 _27539 _27540 _27541 l x f m y g) = (term226 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (@lem1182757 _27540 (term108 _27539 _27540 l x f) (term26 _27538 _27541 m y g)). Qed.
Lemma lem1182759 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term117 _27539 _27540 l x f x') = (term107 _27539 _27540 l x f x').
Proof. exact (eq_refl (term117 _27539 _27540 l x f x')). Qed.
Lemma lem1182760 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term227 _27539 _27540 l x f) = (term108 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182759 _27539 _27540 l x f x')). Qed.
Lemma lem1182761 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182762 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term228 _27539 _27540 l x f) = (term26 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182761 _27540) (@lem1182760 _27539 _27540 l x f)). Qed.
Lemma lem1182763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182764 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term229 _27539 _27540 l x f) = (term33 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1182763) (@lem1182762 _27539 _27540 l x f)). Qed.
Lemma lem1182765 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term26 _27538 _27541 m y g) = (term26 _27538 _27541 m y g).
Proof. exact (eq_refl (term26 _27538 _27541 m y g)). Qed.
Lemma lem1182766 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term225 _27538 _27539 _27540 _27541 l x f m y g) = (term35 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182764 _27539 _27540 l x f) (@lem1182765 _27538 _27541 m y g)). Qed.
Lemma lem1182767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182768 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term230 _27538 _27539 _27540 _27541 l x f m y g) = (term231 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182767) (@lem1182766 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182769 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term117 _27539 _27540 l x f x') = (term107 _27539 _27540 l x f x').
Proof. exact (eq_refl (term117 _27539 _27540 l x f x')). Qed.
Lemma lem1182770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182771 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term232 _27539 _27540 l x f x') = (term233 _27539 _27540 l x f x').
Proof. exact (MK_COMB (@lem1182770) (@lem1182769 _27539 _27540 l x f x')). Qed.
Lemma lem1182772 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term26 _27538 _27541 m y g) = (term26 _27538 _27541 m y g).
Proof. exact (eq_refl (term26 _27538 _27541 m y g)). Qed.
Lemma lem1182773 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term234 _27538 _27539 _27540 _27541 l x f x' m y g) = (term235 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182771 _27539 _27540 l x f x') (@lem1182772 _27538 _27541 m y g)). Qed.
Lemma lem1182774 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term236 _27538 _27539 _27540 _27541 l x f m y g) = (term237 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182773 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182775 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182776 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term226 _27538 _27539 _27540 _27541 l x f m y g) = (term238 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182775 _27540) (@lem1182774 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182777 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : ((term225 _27538 _27539 _27540 _27541 l x f m y g) = (term226 _27538 _27539 _27540 _27541 l x f m y g)) = ((term35 _27538 _27539 _27540 _27541 l x f m y g) = (term238 _27538 _27539 _27540 _27541 l x f m y g)).
Proof. exact (MK_COMB (@lem1182768 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182776 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182778 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term35 _27538 _27539 _27540 _27541 l x f m y g) = (term238 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (EQ_MP (@lem1182777 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182758 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182780 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1182781 {_27541 : Type'} (P : Prop) (Q : _27541 -> Prop) : (term194 _27541 P Q) = (term195 _27541 P Q).
Proof. exact (@lem1182780 _27541 P Q). Qed.
Lemma lem1182782 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term239 _27538 _27539 _27540 _27541 l x f x' m y g) = (term240 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (@lem1182781 _27541 (term107 _27539 _27540 l x f x') (term108 _27538 _27541 m y g)). Qed.
Lemma lem1182783 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term117 _27538 _27541 m y g x) = (term107 _27538 _27541 m y g x).
Proof. exact (eq_refl (term117 _27538 _27541 m y g x)). Qed.
Lemma lem1182784 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term227 _27538 _27541 m y g) = (term108 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1182783 _27538 _27541 m y g x)). Qed.
Lemma lem1182785 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182786 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term228 _27538 _27541 m y g) = (term26 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1182785 _27541) (@lem1182784 _27538 _27541 m y g)). Qed.
Lemma lem1182787 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term233 _27539 _27540 l x f x') = (term233 _27539 _27540 l x f x').
Proof. exact (eq_refl (term233 _27539 _27540 l x f x')). Qed.
Lemma lem1182788 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term239 _27538 _27539 _27540 _27541 l x f x' m y g) = (term235 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182787 _27539 _27540 l x f x') (@lem1182786 _27538 _27541 m y g)). Qed.
Lemma lem1182789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182790 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term241 _27538 _27539 _27540 _27541 l x f x' m y g) = (term242 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182789) (@lem1182788 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182791 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term117 _27538 _27541 m y g x) = (term107 _27538 _27541 m y g x).
Proof. exact (eq_refl (term117 _27538 _27541 m y g x)). Qed.
Lemma lem1182792 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term233 _27539 _27540 l x f x') = (term233 _27539 _27540 l x f x').
Proof. exact (eq_refl (term233 _27539 _27540 l x f x')). Qed.
Lemma lem1182793 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term243 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term244 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (MK_COMB (@lem1182792 _27539 _27540 l x f x') (@lem1182791 _27538 _27541 m y g x'')). Qed.
Lemma lem1182794 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term245 _27538 _27539 _27540 _27541 l x f x' m y g) = (term246 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1182793 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1182795 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182796 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term240 _27538 _27539 _27540 _27541 l x f x' m y g) = (term247 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182795 _27541) (@lem1182794 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182797 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : ((term239 _27538 _27539 _27540 _27541 l x f x' m y g) = (term240 _27538 _27539 _27540 _27541 l x f x' m y g)) = ((term235 _27538 _27539 _27540 _27541 l x f x' m y g) = (term247 _27538 _27539 _27540 _27541 l x f x' m y g)).
Proof. exact (MK_COMB (@lem1182790 _27538 _27539 _27540 _27541 l x f x' m y g) (@lem1182796 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182798 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term235 _27538 _27539 _27540 _27541 l x f x' m y g) = (term247 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (EQ_MP (@lem1182797 _27538 _27539 _27540 _27541 l x f x' m y g) (@lem1182782 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182799 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term237 _27538 _27539 _27540 _27541 l x f m y g) = (term248 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182798 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182800 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182801 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term238 _27538 _27539 _27540 _27541 l x f m y g) = (term249 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182800 _27540) (@lem1182799 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182802 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term35 _27538 _27539 _27540 _27541 l x f m y g) = (term249 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (TRANS (@lem1182778 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182801 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182804 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term128 _27538 _27539 _27540 _27541 l x f m y g) = (term250 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182803) (@lem1182802 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182805 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182806 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term129 _27538 _27539 _27540 _27541 l f m g P x y) = (term251 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182804 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182805 _27538 _27539 P x y)). Qed.
Lemma lem1182808 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182809 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term223 _27540 P Q) = (term224 _27540 P Q).
Proof. exact (@lem1182808 _27540 P Q). Qed.
Lemma lem1182810 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term252 _27538 _27539 _27540 _27541 l f m g P x y) = (term253 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (@lem1182809 _27540 (term248 _27538 _27539 _27540 _27541 l x f m y g) (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182811 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term254 _27538 _27539 _27540 _27541 l x f m y g x') = (term247 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (eq_refl (term254 _27538 _27539 _27540 _27541 l x f m y g x')). Qed.
Lemma lem1182812 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term255 _27538 _27539 _27540 _27541 l x f m y g) = (term248 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182811 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182813 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182814 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term256 _27538 _27539 _27540 _27541 l x f m y g) = (term249 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182813 _27540) (@lem1182812 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182816 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term257 _27538 _27539 _27540 _27541 l x f m y g) = (term250 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1182815) (@lem1182814 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1182817 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182818 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term252 _27538 _27539 _27540 _27541 l f m g P x y) = (term251 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182816 _27538 _27539 _27540 _27541 l x f m y g) (@lem1182817 _27538 _27539 P x y)). Qed.
Lemma lem1182819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182820 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term258 _27538 _27539 _27540 _27541 l f m g P x y) = (term259 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182819) (@lem1182818 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182821 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term254 _27538 _27539 _27540 _27541 l x f m y g x') = (term247 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (eq_refl (term254 _27538 _27539 _27540 _27541 l x f m y g x')). Qed.
Lemma lem1182822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182823 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term260 _27538 _27539 _27540 _27541 l x f m y g x') = (term261 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182822) (@lem1182821 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182824 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182825 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term262 _27538 _27539 _27540 _27541 l f m g x P x' y) = (term263 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182823 _27538 _27539 _27540 _27541 l x' f x m y g) (@lem1182824 _27538 _27539 P x' y)). Qed.
Lemma lem1182826 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term264 _27538 _27539 _27540 _27541 l f m g P x y) = (term265 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182825 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1182827 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182828 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term253 _27538 _27539 _27540 _27541 l f m g P x y) = (term266 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182827 _27540) (@lem1182826 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182829 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : ((term252 _27538 _27539 _27540 _27541 l f m g P x y) = (term253 _27538 _27539 _27540 _27541 l f m g P x y)) = ((term251 _27538 _27539 _27540 _27541 l f m g P x y) = (term266 _27538 _27539 _27540 _27541 l f m g P x y)).
Proof. exact (MK_COMB (@lem1182820 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182828 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182830 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term251 _27538 _27539 _27540 _27541 l f m g P x y) = (term266 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (EQ_MP (@lem1182829 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182810 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182832 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182833 {_27541 : Type'} (P : _27541 -> Prop) (Q : Prop) : (term223 _27541 P Q) = (term224 _27541 P Q).
Proof. exact (@lem1182832 _27541 P Q). Qed.
Lemma lem1182834 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term267 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term268 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (@lem1182833 _27541 (term246 _27538 _27539 _27540 _27541 l x' f x m y g) (term127 _27538 _27539 P x' y)). Qed.
Lemma lem1182835 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term269 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term244 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (eq_refl (term269 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1182836 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term270 _27538 _27539 _27540 _27541 l x f x' m y g) = (term246 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1182835 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1182837 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182838 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term271 _27538 _27539 _27540 _27541 l x f x' m y g) = (term247 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182837 _27541) (@lem1182836 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182840 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term272 _27538 _27539 _27540 _27541 l x f x' m y g) = (term261 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1182839) (@lem1182838 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1182841 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182842 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term267 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term263 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182840 _27538 _27539 _27540 _27541 l x' f x m y g) (@lem1182841 _27538 _27539 P x' y)). Qed.
Lemma lem1182843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182844 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term273 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term274 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182843) (@lem1182842 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182845 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term269 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term244 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (eq_refl (term269 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1182846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182847 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term275 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term276 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (MK_COMB (@lem1182846) (@lem1182845 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1182848 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term127 _27538 _27539 P x y) = (term127 _27538 _27539 P x y).
Proof. exact (eq_refl (term127 _27538 _27539 P x y)). Qed.
Lemma lem1182849 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term277 _27538 _27539 _27540 _27541 l f x m g x' P x'' y) = (term278 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (MK_COMB (@lem1182847 _27538 _27539 _27540 _27541 l x'' f x m y g x') (@lem1182848 _27538 _27539 P x'' y)). Qed.
Lemma lem1182850 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term279 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term280 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1182849 _27538 _27539 _27540 _27541 l f x m g x'' P x' y)). Qed.
Lemma lem1182851 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182852 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term268 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182851 _27541) (@lem1182850 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182853 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : ((term267 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term268 _27538 _27539 _27540 _27541 l f x m g P x' y)) = ((term263 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y)).
Proof. exact (MK_COMB (@lem1182844 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1182852 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182854 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term263 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (EQ_MP (@lem1182853 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1182834 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182855 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term265 _27538 _27539 _27540 _27541 l f m g P x y) = (term282 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182854 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1182856 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182857 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term266 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182856 _27540) (@lem1182855 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182858 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term251 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1182830 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182857 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182859 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term129 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1182806 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182858 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182860 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term142 _27538 _27539 _27540 _27541 l f m g P x) = (term284 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1182859 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182861 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1182862 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term143 _27538 _27539 _27540 _27541 l f m g P x) = (term285 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182861 _27538) (@lem1182860 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182863 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term151 _27538 _27539 _27540 _27541 l f m g P) = (term286 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1182862 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182864 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1182865 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term152 _27538 _27539 _27540 _27541 l f m g P) = (term287 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182864 _27539) (@lem1182863 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182867 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term183 _27538 _27539 _27540 _27541 l f m g P) = (term288 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182866) (@lem1182865 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182868 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182869 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term185 _27538 _27539 _27540 _27541 l m P f g) = (term289 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182867 _27538 _27539 _27540 _27541 l f m g P) (@lem1182868 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182871 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182872 {_27539 : Type'} (P : _27539 -> Prop) (Q : Prop) : (term223 _27539 P Q) = (term224 _27539 P Q).
Proof. exact (@lem1182871 _27539 P Q). Qed.
Lemma lem1182873 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term290 _27538 _27539 _27540 _27541 l m P f g) = (term291 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1182872 _27539 (term286 _27538 _27539 _27540 _27541 l f m g P) (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182874 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term292 _27538 _27539 _27540 _27541 l f m g P x) = (term285 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (eq_refl (term292 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182875 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term293 _27538 _27539 _27540 _27541 l f m g P) = (term286 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1182874 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182876 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1182877 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term294 _27538 _27539 _27540 _27541 l f m g P) = (term287 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182876 _27539) (@lem1182875 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182879 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term295 _27538 _27539 _27540 _27541 l f m g P) = (term288 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1182878) (@lem1182877 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1182880 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182881 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term290 _27538 _27539 _27540 _27541 l m P f g) = (term289 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182879 _27538 _27539 _27540 _27541 l f m g P) (@lem1182880 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182883 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term296 _27538 _27539 _27540 _27541 l m P f g) = (term297 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182882) (@lem1182881 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182884 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term292 _27538 _27539 _27540 _27541 l f m g P x) = (term285 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (eq_refl (term292 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182886 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term298 _27538 _27539 _27540 _27541 l f m g P x) = (term299 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182885) (@lem1182884 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182887 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182888 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term300 _27538 _27539 _27540 _27541 x l m P f g) = (term301 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182886 _27538 _27539 _27540 _27541 l f m g P x) (@lem1182887 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182889 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term302 _27538 _27539 _27540 _27541 l m P f g) = (term303 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27539 => @lem1182888 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182890 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1182891 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term291 _27538 _27539 _27540 _27541 l m P f g) = (term304 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182890 _27539) (@lem1182889 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182892 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term290 _27538 _27539 _27540 _27541 l m P f g) = (term291 _27538 _27539 _27540 _27541 l m P f g)) = ((term289 _27538 _27539 _27540 _27541 l m P f g) = (term304 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (MK_COMB (@lem1182883 _27538 _27539 _27540 _27541 l m P f g) (@lem1182891 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182893 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term289 _27538 _27539 _27540 _27541 l m P f g) = (term304 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (EQ_MP (@lem1182892 _27538 _27539 _27540 _27541 l m P f g) (@lem1182873 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182895 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182896 {_27538 : Type'} (P : _27538 -> Prop) (Q : Prop) : (term223 _27538 P Q) = (term224 _27538 P Q).
Proof. exact (@lem1182895 _27538 P Q). Qed.
Lemma lem1182897 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term305 _27538 _27539 _27540 _27541 x l m P f g) = (term306 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (@lem1182896 _27538 (term284 _27538 _27539 _27540 _27541 l f m g P x) (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182898 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term307 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (eq_refl (term307 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182899 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term308 _27538 _27539 _27540 _27541 l f m g P x) = (term284 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1182898 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182900 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1182901 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term309 _27538 _27539 _27540 _27541 l f m g P x) = (term285 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182900 _27538) (@lem1182899 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182903 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term310 _27538 _27539 _27540 _27541 l f m g P x) = (term299 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1182902) (@lem1182901 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1182904 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182905 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term305 _27538 _27539 _27540 _27541 x l m P f g) = (term301 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182903 _27538 _27539 _27540 _27541 l f m g P x) (@lem1182904 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182907 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term311 _27538 _27539 _27540 _27541 x l m P f g) = (term312 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182906) (@lem1182905 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182908 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term307 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (eq_refl (term307 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182910 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term313 _27538 _27539 _27540 _27541 l f m g P x y) = (term314 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182909) (@lem1182908 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182911 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182912 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term315 _27538 _27539 _27540 _27541 x y l m P f g) = (term316 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1182910 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182911 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182913 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term317 _27538 _27539 _27540 _27541 x l m P f g) = (term318 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (fun_ext (fun y : _27538 => @lem1182912 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182914 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1182915 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term306 _27538 _27539 _27540 _27541 x l m P f g) = (term319 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182914 _27538) (@lem1182913 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182916 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term305 _27538 _27539 _27540 _27541 x l m P f g) = (term306 _27538 _27539 _27540 _27541 x l m P f g)) = ((term301 _27538 _27539 _27540 _27541 x l m P f g) = (term319 _27538 _27539 _27540 _27541 x l m P f g)).
Proof. exact (MK_COMB (@lem1182907 _27538 _27539 _27540 _27541 x l m P f g) (@lem1182915 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182917 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term301 _27538 _27539 _27540 _27541 x l m P f g) = (term319 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (EQ_MP (@lem1182916 _27538 _27539 _27540 _27541 x l m P f g) (@lem1182897 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182919 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182920 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term223 _27540 P Q) = (term224 _27540 P Q).
Proof. exact (@lem1182919 _27540 P Q). Qed.
Lemma lem1182921 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term320 _27538 _27539 _27540 _27541 x y l m P f g) = (term321 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (@lem1182920 _27540 (term282 _27538 _27539 _27540 _27541 l f m g P x y) (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182922 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term322 _27538 _27539 _27540 _27541 l f m g P x' y x) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (eq_refl (term322 _27538 _27539 _27540 _27541 l f m g P x' y x)). Qed.
Lemma lem1182923 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term323 _27538 _27539 _27540 _27541 l f m g P x y) = (term282 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182922 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1182924 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182925 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term324 _27538 _27539 _27540 _27541 l f m g P x y) = (term283 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182924 _27540) (@lem1182923 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182927 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term325 _27538 _27539 _27540 _27541 l f m g P x y) = (term314 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1182926) (@lem1182925 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1182928 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182929 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term320 _27538 _27539 _27540 _27541 x y l m P f g) = (term316 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1182927 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1182928 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182931 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term326 _27538 _27539 _27540 _27541 x y l m P f g) = (term327 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1182930) (@lem1182929 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182932 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term322 _27538 _27539 _27540 _27541 l f m g P x' y x) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (eq_refl (term322 _27538 _27539 _27540 _27541 l f m g P x' y x)). Qed.
Lemma lem1182933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182934 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term328 _27538 _27539 _27540 _27541 l f m g P x' y x) = (term329 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182933) (@lem1182932 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182935 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182936 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term330 _27538 _27539 _27540 _27541 x' y x l m P f g) = (term331 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (MK_COMB (@lem1182934 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1182935 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182937 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term332 _27538 _27539 _27540 _27541 x y l m P f g) = (term333 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182936 _27538 _27539 _27540 _27541 x' x y l m P f g)). Qed.
Lemma lem1182938 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182939 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term321 _27538 _27539 _27540 _27541 x y l m P f g) = (term334 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1182938 _27540) (@lem1182937 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182940 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term320 _27538 _27539 _27540 _27541 x y l m P f g) = (term321 _27538 _27539 _27540 _27541 x y l m P f g)) = ((term316 _27538 _27539 _27540 _27541 x y l m P f g) = (term334 _27538 _27539 _27540 _27541 x y l m P f g)).
Proof. exact (MK_COMB (@lem1182931 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1182939 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182941 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term316 _27538 _27539 _27540 _27541 x y l m P f g) = (term334 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (EQ_MP (@lem1182940 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1182921 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182943 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1182944 {_27541 : Type'} (P : _27541 -> Prop) (Q : Prop) : (term223 _27541 P Q) = (term224 _27541 P Q).
Proof. exact (@lem1182943 _27541 P Q). Qed.
Lemma lem1182945 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term335 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term336 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (@lem1182944 _27541 (term280 _27538 _27539 _27540 _27541 l f x m g P x' y) (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182946 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term337 _27538 _27539 _27540 _27541 l f x m g P x'' y x') = (term278 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (eq_refl (term337 _27538 _27539 _27540 _27541 l f x m g P x'' y x')). Qed.
Lemma lem1182947 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term338 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term280 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1182946 _27538 _27539 _27540 _27541 l f x m g x'' P x' y)). Qed.
Lemma lem1182948 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182949 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term339 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term281 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182948 _27541) (@lem1182947 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182951 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term340 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term329 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1182950) (@lem1182949 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1182952 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182953 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term335 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term331 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (MK_COMB (@lem1182951 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1182952 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182955 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term341 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term342 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (MK_COMB (@lem1182954) (@lem1182953 _27538 _27539 _27540 _27541 x x' y l m P f g)). Qed.
Lemma lem1182956 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term337 _27538 _27539 _27540 _27541 l f x m g P x'' y x') = (term278 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (eq_refl (term337 _27538 _27539 _27540 _27541 l f x m g P x'' y x')). Qed.
Lemma lem1182957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1182958 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term343 _27538 _27539 _27540 _27541 l f x m g P x'' y x') = (term344 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (MK_COMB (@lem1182957) (@lem1182956 _27538 _27539 _27540 _27541 l f x m g x' P x'' y)). Qed.
Lemma lem1182959 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term181 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182960 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27541) (x'' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term345 _27538 _27539 _27540 _27541 x x'' y x' l m P f g) = (term346 _27538 _27539 _27540 _27541 x x' x'' y l m P f g).
Proof. exact (MK_COMB (@lem1182958 _27538 _27539 _27540 _27541 l f x m g x' P x'' y) (@lem1182959 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182961 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term347 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term348 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1182960 _27538 _27539 _27540 _27541 x x'' x' y l m P f g)). Qed.
Lemma lem1182962 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1182963 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term336 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term349 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (MK_COMB (@lem1182962 _27541) (@lem1182961 _27538 _27539 _27540 _27541 x x' y l m P f g)). Qed.
Lemma lem1182964 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term335 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term336 _27538 _27539 _27540 _27541 x x' y l m P f g)) = ((term331 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term349 _27538 _27539 _27540 _27541 x x' y l m P f g)).
Proof. exact (MK_COMB (@lem1182955 _27538 _27539 _27540 _27541 x x' y l m P f g) (@lem1182963 _27538 _27539 _27540 _27541 x x' y l m P f g)). Qed.
Lemma lem1182965 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term331 _27538 _27539 _27540 _27541 x x' y l m P f g) = (term349 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (EQ_MP (@lem1182964 _27538 _27539 _27540 _27541 x x' y l m P f g) (@lem1182945 _27538 _27539 _27540 _27541 x x' y l m P f g)). Qed.
Lemma lem1182966 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term333 _27538 _27539 _27540 _27541 x y l m P f g) = (term350 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1182965 _27538 _27539 _27540 _27541 x' x y l m P f g)). Qed.
Lemma lem1182967 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182968 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term334 _27538 _27539 _27540 _27541 x y l m P f g) = (term351 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1182967 _27540) (@lem1182966 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182969 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term316 _27538 _27539 _27540 _27541 x y l m P f g) = (term351 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (TRANS (@lem1182941 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1182968 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182970 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term318 _27538 _27539 _27540 _27541 x l m P f g) = (term352 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (fun_ext (fun y : _27538 => @lem1182969 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1182971 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1182972 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term319 _27538 _27539 _27540 _27541 x l m P f g) = (term353 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182971 _27538) (@lem1182970 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182973 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term301 _27538 _27539 _27540 _27541 x l m P f g) = (term353 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (TRANS (@lem1182917 _27538 _27539 _27540 _27541 x l m P f g) (@lem1182972 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182974 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term303 _27538 _27539 _27540 _27541 l m P f g) = (term354 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27539 => @lem1182973 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1182975 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1182976 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term304 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182975 _27539) (@lem1182974 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182977 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term289 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182893 _27538 _27539 _27540 _27541 l m P f g) (@lem1182976 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182978 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term185 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182869 _27538 _27539 _27540 _27541 l m P f g) (@lem1182977 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182979 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term193 _27538 _27539 _27540 _27541 l m P f g) = (term356 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182754 _27538 _27539 _27540 _27541 l m P f g) (@lem1182978 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182983 {A : Type'} (P : A -> Prop) (Q : Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1182984 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term357 _27540 P Q) = (term358 _27540 P Q).
Proof. exact (@lem1182983 _27540 P Q). Qed.
Lemma lem1182985 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term359 _27538 _27539 _27540 _27541 l m P f g) = (term360 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (@lem1182984 _27540 (term220 _27538 _27539 _27540 _27541 l m P f g) (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182986 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term361 _27538 _27539 _27540 _27541 l m P f g x) = (term219 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (eq_refl (term361 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1182987 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term362 _27538 _27539 _27540 _27541 l m P f g) = (term220 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1182986 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182988 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1182989 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term363 _27538 _27539 _27540 _27541 l m P f g) = (term221 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182988 _27540) (@lem1182987 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182991 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term364 _27538 _27539 _27540 _27541 l m P f g) = (term222 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182990) (@lem1182989 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182992 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term355 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182993 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term359 _27538 _27539 _27540 _27541 l m P f g) = (term356 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182991 _27538 _27539 _27540 _27541 l m P f g) (@lem1182992 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1182995 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term365 _27538 _27539 _27540 _27541 l m P f g) = (term366 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1182994) (@lem1182993 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1182996 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term361 _27538 _27539 _27540 _27541 l m P f g x) = (term219 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (eq_refl (term361 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1182997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1182998 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term367 _27538 _27539 _27540 _27541 l m P f g x) = (term368 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1182997) (@lem1182996 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1182999 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term355 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183000 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term369 _27538 _27539 _27540 _27541 x l m P f g) = (term370 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1182998 _27538 _27539 _27540 _27541 l m P f x g) (@lem1182999 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183001 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term371 _27538 _27539 _27540 _27541 l m P f g) = (term372 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1183000 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183002 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1183003 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term360 _27538 _27539 _27540 _27541 l m P f g) = (term373 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1183002 _27540) (@lem1183001 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183004 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term359 _27538 _27539 _27540 _27541 l m P f g) = (term360 _27538 _27539 _27540 _27541 l m P f g)) = ((term356 _27538 _27539 _27540 _27541 l m P f g) = (term373 _27538 _27539 _27540 _27541 l m P f g)).
Proof. exact (MK_COMB (@lem1182995 _27538 _27539 _27540 _27541 l m P f g) (@lem1183003 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183005 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term356 _27538 _27539 _27540 _27541 l m P f g) = (term373 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (EQ_MP (@lem1183004 _27538 _27539 _27540 _27541 l m P f g) (@lem1182985 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183009 {A : Type'} (P : A -> Prop) (Q : Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1183010 {_27541 : Type'} (P : _27541 -> Prop) (Q : Prop) : (term357 _27541 P Q) = (term358 _27541 P Q).
Proof. exact (@lem1183009 _27541 P Q). Qed.
Lemma lem1183011 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term374 _27538 _27539 _27540 _27541 x l m P f g) = (term375 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (@lem1183010 _27541 (term218 _27538 _27539 _27540 _27541 l m P f x g) (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183012 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term376 _27538 _27539 _27540 _27541 l m P f x g y) = (term216 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term376 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183013 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term377 _27538 _27539 _27540 _27541 l m P f x g) = (term218 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1183012 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183014 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1183015 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term378 _27538 _27539 _27540 _27541 l m P f x g) = (term219 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1183014 _27541) (@lem1183013 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183017 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term379 _27538 _27539 _27540 _27541 l m P f x g) = (term368 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1183016) (@lem1183015 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183018 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term355 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183019 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term374 _27538 _27539 _27540 _27541 x l m P f g) = (term370 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1183017 _27538 _27539 _27540 _27541 l m P f x g) (@lem1183018 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183021 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term380 _27538 _27539 _27540 _27541 x l m P f g) = (term381 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1183020) (@lem1183019 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183022 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term376 _27538 _27539 _27540 _27541 l m P f x g y) = (term216 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term376 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183024 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term382 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1183023) (@lem1183022 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183025 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term355 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (eq_refl (term355 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183026 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term384 _27538 _27539 _27540 _27541 x y l m P f g) = (term385 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183024 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183025 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183027 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term386 _27538 _27539 _27540 _27541 x l m P f g) = (term387 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (fun_ext (fun y : _27541 => @lem1183026 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183028 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1183029 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term375 _27538 _27539 _27540 _27541 x l m P f g) = (term388 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1183028 _27541) (@lem1183027 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183030 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term374 _27538 _27539 _27540 _27541 x l m P f g) = (term375 _27538 _27539 _27540 _27541 x l m P f g)) = ((term370 _27538 _27539 _27540 _27541 x l m P f g) = (term388 _27538 _27539 _27540 _27541 x l m P f g)).
Proof. exact (MK_COMB (@lem1183021 _27538 _27539 _27540 _27541 x l m P f g) (@lem1183029 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183031 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term370 _27538 _27539 _27540 _27541 x l m P f g) = (term388 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (EQ_MP (@lem1183030 _27538 _27539 _27540 _27541 x l m P f g) (@lem1183011 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term389 A P Q) = (term390 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1183034 {_27539 : Type'} (P : Prop) (Q : _27539 -> Prop) : (term389 _27539 P Q) = (term390 _27539 P Q).
Proof. exact (@lem1183033 _27539 P Q). Qed.
Lemma lem1183035 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term391 _27538 _27539 _27540 _27541 x y l m P f g) = (term392 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (@lem1183034 _27539 (term216 _27538 _27539 _27540 _27541 l m P f x g y) (term354 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183036 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term393 _27538 _27539 _27540 _27541 l m P f g x) = (term353 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (eq_refl (term393 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1183037 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term394 _27538 _27539 _27540 _27541 l m P f g) = (term354 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27539 => @lem1183036 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183038 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1183039 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term395 _27538 _27539 _27540 _27541 l m P f g) = (term355 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1183038 _27539) (@lem1183037 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183040 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183041 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term391 _27538 _27539 _27540 _27541 x y l m P f g) = (term385 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183040 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183039 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183043 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term396 _27538 _27539 _27540 _27541 x y l m P f g) = (term397 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183042) (@lem1183041 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183044 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term393 _27538 _27539 _27540 _27541 l m P f g x) = (term353 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (eq_refl (term393 _27538 _27539 _27540 _27541 l m P f g x)). Qed.
Lemma lem1183045 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183046 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term398 _27538 _27539 _27540 _27541 x y l m P f g x') = (term399 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (MK_COMB (@lem1183045 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183044 _27538 _27539 _27540 _27541 x' l m P f g)). Qed.
Lemma lem1183047 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term400 _27538 _27539 _27540 _27541 x y l m P f g) = (term401 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (fun_ext (fun x' : _27539 => @lem1183046 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183048 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1183049 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term392 _27538 _27539 _27540 _27541 x y l m P f g) = (term402 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183048 _27539) (@lem1183047 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183050 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term391 _27538 _27539 _27540 _27541 x y l m P f g) = (term392 _27538 _27539 _27540 _27541 x y l m P f g)) = ((term385 _27538 _27539 _27540 _27541 x y l m P f g) = (term402 _27538 _27539 _27540 _27541 x y l m P f g)).
Proof. exact (MK_COMB (@lem1183043 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1183049 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183051 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term385 _27538 _27539 _27540 _27541 x y l m P f g) = (term402 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (EQ_MP (@lem1183050 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1183035 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183053 {A : Type'} (P : Prop) (Q : A -> Prop) : (term389 A P Q) = (term390 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1183054 {_27538 : Type'} (P : Prop) (Q : _27538 -> Prop) : (term389 _27538 P Q) = (term390 _27538 P Q).
Proof. exact (@lem1183053 _27538 P Q). Qed.
Lemma lem1183055 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term403 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term404 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (@lem1183054 _27538 (term216 _27538 _27539 _27540 _27541 l m P f x g y) (term352 _27538 _27539 _27540 _27541 x' l m P f g)). Qed.
Lemma lem1183056 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term405 _27538 _27539 _27540 _27541 x l m P f g y) = (term351 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (eq_refl (term405 _27538 _27539 _27540 _27541 x l m P f g y)). Qed.
Lemma lem1183057 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term406 _27538 _27539 _27540 _27541 x l m P f g) = (term352 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (fun_ext (fun y : _27538 => @lem1183056 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183058 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1183059 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term407 _27538 _27539 _27540 _27541 x l m P f g) = (term353 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1183058 _27538) (@lem1183057 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183060 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183061 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term403 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term399 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (MK_COMB (@lem1183060 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183059 _27538 _27539 _27540 _27541 x' l m P f g)). Qed.
Lemma lem1183062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183063 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term408 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term409 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (MK_COMB (@lem1183062) (@lem1183061 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183064 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term405 _27538 _27539 _27540 _27541 x l m P f g y) = (term351 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (eq_refl (term405 _27538 _27539 _27540 _27541 x l m P f g y)). Qed.
Lemma lem1183065 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183066 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term410 _27538 _27539 _27540 _27541 x y x' l m P f g y') = (term411 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183065 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183064 _27538 _27539 _27540 _27541 x' y' l m P f g)). Qed.
Lemma lem1183067 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term412 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term413 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (fun_ext (fun y' : _27538 => @lem1183066 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183068 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1183069 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term404 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term414 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (MK_COMB (@lem1183068 _27538) (@lem1183067 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183070 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term403 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term404 _27538 _27539 _27540 _27541 x y x' l m P f g)) = ((term399 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term414 _27538 _27539 _27540 _27541 x y x' l m P f g)).
Proof. exact (MK_COMB (@lem1183063 _27538 _27539 _27540 _27541 x y x' l m P f g) (@lem1183069 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183071 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term399 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term414 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (EQ_MP (@lem1183070 _27538 _27539 _27540 _27541 x y x' l m P f g) (@lem1183055 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183073 {A : Type'} (P : Prop) (Q : A -> Prop) : (term389 A P Q) = (term390 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1183074 {_27540 : Type'} (P : Prop) (Q : _27540 -> Prop) : (term389 _27540 P Q) = (term390 _27540 P Q).
Proof. exact (@lem1183073 _27540 P Q). Qed.
Lemma lem1183075 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term415 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term416 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (@lem1183074 _27540 (term216 _27538 _27539 _27540 _27541 l m P f x g y) (term350 _27538 _27539 _27540 _27541 x' y' l m P f g)). Qed.
Lemma lem1183076 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (x' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term417 _27538 _27539 _27540 _27541 x' y l m P f g x) = (term349 _27538 _27539 _27540 _27541 x x' y l m P f g).
Proof. exact (eq_refl (term417 _27538 _27539 _27540 _27541 x' y l m P f g x)). Qed.
Lemma lem1183077 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term418 _27538 _27539 _27540 _27541 x y l m P f g) = (term350 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183076 _27538 _27539 _27540 _27541 x' x y l m P f g)). Qed.
Lemma lem1183078 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1183079 {_27538 _27539 _27540 _27541 : Type'} (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term419 _27538 _27539 _27540 _27541 x y l m P f g) = (term351 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183078 _27540) (@lem1183077 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183080 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183081 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term415 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term411 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183080 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183079 _27538 _27539 _27540 _27541 x' y' l m P f g)). Qed.
Lemma lem1183082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183083 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term420 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term421 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183082) (@lem1183081 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183084 {_27538 _27539 _27540 _27541 : Type'} (x' : _27540) (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term417 _27538 _27539 _27540 _27541 x y l m P f g x') = (term349 _27538 _27539 _27540 _27541 x' x y l m P f g).
Proof. exact (eq_refl (term417 _27538 _27539 _27540 _27541 x y l m P f g x')). Qed.
Lemma lem1183085 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183086 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term422 _27538 _27539 _27540 _27541 x y x'' y' l m P f g x') = (term423 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (MK_COMB (@lem1183085 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183084 _27538 _27539 _27540 _27541 x' x'' y' l m P f g)). Qed.
Lemma lem1183087 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term424 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term425 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (fun_ext (fun x'' : _27540 => @lem1183086 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g)). Qed.
Lemma lem1183088 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1183089 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term416 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term426 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183088 _27540) (@lem1183087 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183090 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term415 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term416 _27538 _27539 _27540 _27541 x y x' y' l m P f g)) = ((term411 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term426 _27538 _27539 _27540 _27541 x y x' y' l m P f g)).
Proof. exact (MK_COMB (@lem1183083 _27538 _27539 _27540 _27541 x y x' y' l m P f g) (@lem1183089 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183091 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term411 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term426 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (EQ_MP (@lem1183090 _27538 _27539 _27540 _27541 x y x' y' l m P f g) (@lem1183075 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183093 {A : Type'} (P : Prop) (Q : A -> Prop) : (term389 A P Q) = (term390 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1183094 {_27541 : Type'} (P : Prop) (Q : _27541 -> Prop) : (term389 _27541 P Q) = (term390 _27541 P Q).
Proof. exact (@lem1183093 _27541 P Q). Qed.
Lemma lem1183095 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term427 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term428 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (@lem1183094 _27541 (term216 _27538 _27539 _27540 _27541 l m P f x g y) (term348 _27538 _27539 _27540 _27541 x' x'' y' l m P f g)). Qed.
Lemma lem1183096 {_27538 _27539 _27540 _27541 : Type'} (x' : _27540) (x : _27541) (x'' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term429 _27538 _27539 _27540 _27541 x' x'' y l m P f g x) = (term346 _27538 _27539 _27540 _27541 x' x x'' y l m P f g).
Proof. exact (eq_refl (term429 _27538 _27539 _27540 _27541 x' x'' y l m P f g x)). Qed.
Lemma lem1183097 {_27538 _27539 _27540 _27541 : Type'} (x' : _27540) (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term430 _27538 _27539 _27540 _27541 x' x y l m P f g) = (term348 _27538 _27539 _27540 _27541 x' x y l m P f g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1183096 _27538 _27539 _27540 _27541 x' x'' x y l m P f g)). Qed.
Lemma lem1183098 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1183099 {_27538 _27539 _27540 _27541 : Type'} (x' : _27540) (x : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term431 _27538 _27539 _27540 _27541 x' x y l m P f g) = (term349 _27538 _27539 _27540 _27541 x' x y l m P f g).
Proof. exact (MK_COMB (@lem1183098 _27541) (@lem1183097 _27538 _27539 _27540 _27541 x' x y l m P f g)). Qed.
Lemma lem1183100 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183101 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term427 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term423 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (MK_COMB (@lem1183100 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183099 _27538 _27539 _27540 _27541 x' x'' y' l m P f g)). Qed.
Lemma lem1183102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183103 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term432 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term433 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (MK_COMB (@lem1183102) (@lem1183101 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)). Qed.
Lemma lem1183104 {_27538 _27539 _27540 _27541 : Type'} (x' : _27540) (x : _27541) (x'' : _27539) (y : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term429 _27538 _27539 _27540 _27541 x' x'' y l m P f g x) = (term346 _27538 _27539 _27540 _27541 x' x x'' y l m P f g).
Proof. exact (eq_refl (term429 _27538 _27539 _27540 _27541 x' x'' y l m P f g x)). Qed.
Lemma lem1183105 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term383 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183106 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27541) (x''' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term434 _27538 _27539 _27540 _27541 x y x' x''' y' l m P f g x'') = (term435 _27538 _27539 _27540 _27541 x y x' x'' x''' y' l m P f g).
Proof. exact (MK_COMB (@lem1183105 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183104 _27538 _27539 _27540 _27541 x' x'' x''' y' l m P f g)). Qed.
Lemma lem1183107 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term436 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term437 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (fun_ext (fun x''' : _27541 => @lem1183106 _27538 _27539 _27540 _27541 x y x' x''' x'' y' l m P f g)). Qed.
Lemma lem1183108 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1183109 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term428 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term438 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (MK_COMB (@lem1183108 _27541) (@lem1183107 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)). Qed.
Lemma lem1183110 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : ((term427 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term428 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)) = ((term423 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term438 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)).
Proof. exact (MK_COMB (@lem1183103 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) (@lem1183109 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)). Qed.
Lemma lem1183111 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27540) (x'' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term423 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) = (term438 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g).
Proof. exact (EQ_MP (@lem1183110 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g) (@lem1183095 _27538 _27539 _27540 _27541 x y x' x'' y' l m P f g)). Qed.
Lemma lem1183112 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term425 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term439 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (fun_ext (fun x'' : _27540 => @lem1183111 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g)). Qed.
Lemma lem1183113 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1183114 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term426 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term440 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183113 _27540) (@lem1183112 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183115 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term411 _27538 _27539 _27540 _27541 x y x' y' l m P f g) = (term440 _27538 _27539 _27540 _27541 x y x' y' l m P f g).
Proof. exact (TRANS (@lem1183091 _27538 _27539 _27540 _27541 x y x' y' l m P f g) (@lem1183114 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183116 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term413 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term441 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (fun_ext (fun y' : _27538 => @lem1183115 _27538 _27539 _27540 _27541 x y x' y' l m P f g)). Qed.
Lemma lem1183117 {_27538 : Type'} : (@ex _27538) = (@ex _27538).
Proof. exact (eq_refl (@ex _27538)). Qed.
Lemma lem1183118 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term414 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term442 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (MK_COMB (@lem1183117 _27538) (@lem1183116 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183119 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term399 _27538 _27539 _27540 _27541 x y x' l m P f g) = (term442 _27538 _27539 _27540 _27541 x y x' l m P f g).
Proof. exact (TRANS (@lem1183071 _27538 _27539 _27540 _27541 x y x' l m P f g) (@lem1183118 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183120 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term401 _27538 _27539 _27540 _27541 x y l m P f g) = (term443 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (fun_ext (fun x' : _27539 => @lem1183119 _27538 _27539 _27540 _27541 x y x' l m P f g)). Qed.
Lemma lem1183121 {_27539 : Type'} : (@ex _27539) = (@ex _27539).
Proof. exact (eq_refl (@ex _27539)). Qed.
Lemma lem1183122 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term402 _27538 _27539 _27540 _27541 x y l m P f g) = (term444 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (MK_COMB (@lem1183121 _27539) (@lem1183120 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183123 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term385 _27538 _27539 _27540 _27541 x y l m P f g) = (term444 _27538 _27539 _27540 _27541 x y l m P f g).
Proof. exact (TRANS (@lem1183051 _27538 _27539 _27540 _27541 x y l m P f g) (@lem1183122 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183124 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term387 _27538 _27539 _27540 _27541 x l m P f g) = (term445 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (fun_ext (fun y : _27541 => @lem1183123 _27538 _27539 _27540 _27541 x y l m P f g)). Qed.
Lemma lem1183125 {_27541 : Type'} : (@ex _27541) = (@ex _27541).
Proof. exact (eq_refl (@ex _27541)). Qed.
Lemma lem1183126 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term388 _27538 _27539 _27540 _27541 x l m P f g) = (term446 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (MK_COMB (@lem1183125 _27541) (@lem1183124 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183127 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term370 _27538 _27539 _27540 _27541 x l m P f g) = (term446 _27538 _27539 _27540 _27541 x l m P f g).
Proof. exact (TRANS (@lem1183031 _27538 _27539 _27540 _27541 x l m P f g) (@lem1183126 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183128 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term372 _27538 _27539 _27540 _27541 l m P f g) = (term447 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1183127 _27538 _27539 _27540 _27541 x l m P f g)). Qed.
Lemma lem1183129 {_27540 : Type'} : (@ex _27540) = (@ex _27540).
Proof. exact (eq_refl (@ex _27540)). Qed.
Lemma lem1183130 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term373 _27538 _27539 _27540 _27541 l m P f g) = (term448 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1183129 _27540) (@lem1183128 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183131 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term356 _27538 _27539 _27540 _27541 l m P f g) = (term448 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1183005 _27538 _27539 _27540 _27541 l m P f g) (@lem1183130 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183133 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term193 _27538 _27539 _27540 _27541 l m P f g) = (term448 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182979 _27538 _27539 _27540 _27541 l m P f g) (@lem1183131 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183134 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term110 _27538 _27539 _27540 _27541 l m P f g) = (term448 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (TRANS (@lem1182307 _27538 _27539 _27540 _27541 l m P f g) (@lem1183133 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183135 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term110 _27538 _27539 _27540 _27541 l m P f g) : term448 _27538 _27539 _27540 _27541 l m P f g.
Proof. exact (EQ_MP (@lem1183134 _27538 _27539 _27540 _27541 l m P f g) (@lem1182150 _27538 _27539 _27540 _27541 l m P f g h1)). Qed.
Lemma lem1183136 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term446 _27538 _27539 _27540 _27541 x l m P f g) : term446 _27538 _27539 _27540 _27541 x l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183137 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term444 _27538 _27539 _27540 _27541 x y l m P f g) : term444 _27538 _27539 _27540 _27541 x y l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183138 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term442 _27538 _27539 _27540 _27541 x y x' l m P f g) : term442 _27538 _27539 _27540 _27541 x y x' l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183139 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term440 _27538 _27539 _27540 _27541 x y x' y' l m P f g) : term440 _27538 _27539 _27540 _27541 x y x' y' l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183140 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term438 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g) : term438 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183141 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183170 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term163 _27538 _27539 _27540 _27541 l m P f x g y) = (term163 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term163 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183171 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term171 _27538 _27539 _27540 _27541 l m P f x g) = (term171 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1183170 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183172 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183173 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term172 _27538 _27539 _27540 _27541 l m P f x g) = (term172 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1183172 _27541) (@lem1183171 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183174 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term180 _27538 _27539 _27540 _27541 l m P f g) = (term180 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1183173 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183175 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183176 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1183175 _27540) (@lem1183174 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183221 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x'' : _27540) (m : list _27541) (g : _27541 -> _27538) (x''' : _27541) (P : type1470 _27538 _27539) (x' : _27539) (y' : _27538) : (term344 _27538 _27539 _27540 _27541 l f x'' m g x''' P x' y') = (term344 _27538 _27539 _27540 _27541 l f x'' m g x''' P x' y').
Proof. exact (eq_refl (term344 _27538 _27539 _27540 _27541 l f x'' m g x''' P x' y')). Qed.
Lemma lem1183222 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) = (term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183221 _27538 _27539 _27540 _27541 l f x'' m g x''' P x' y') (@lem1183176 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183249 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term158 _27538 _27539 _27540 _27541 l m P f x g y) = (term158 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term158 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183254 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183273 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term112 _27538 _27541 m y g x) = (term112 _27538 _27541 m y g x).
Proof. exact (eq_refl (term112 _27538 _27541 m y g x)). Qed.
Lemma lem1183274 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term120 _27538 _27541 m y g) = (term120 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1183273 _27538 _27541 m y g x)). Qed.
Lemma lem1183275 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183276 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term121 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1183275 _27541) (@lem1183274 _27538 _27541 m y g)). Qed.
Lemma lem1183295 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term112 _27539 _27540 l x f x') = (term112 _27539 _27540 l x f x').
Proof. exact (eq_refl (term112 _27539 _27540 l x f x')). Qed.
Lemma lem1183296 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term120 _27539 _27540 l x f) = (term120 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183295 _27539 _27540 l x f x')). Qed.
Lemma lem1183297 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183298 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term121 _27539 _27540 l x f) = (term121 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1183297 _27540) (@lem1183296 _27539 _27540 l x f)). Qed.
Lemma lem1183299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183300 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term123 _27539 _27540 l x f) = (term123 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1183299) (@lem1183298 _27539 _27540 l x f)). Qed.
Lemma lem1183301 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term125 _27538 _27539 _27540 _27541 l x f m y g) = (term125 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183300 _27539 _27540 l x f) (@lem1183276 _27538 _27541 m y g)). Qed.
Lemma lem1183302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183303 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term132 _27538 _27539 _27540 _27541 l x f m y g) = (term132 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183302) (@lem1183301 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183304 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term134 _27538 _27539 _27540 _27541 l f m g P x y) = (term134 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183303 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183254 _27538 _27539 P x y)). Qed.
Lemma lem1183305 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term144 _27538 _27539 _27540 _27541 l f m g P x) = (term144 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1183304 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183306 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1183307 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term145 _27538 _27539 _27540 _27541 l f m g P x) = (term145 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1183306 _27538) (@lem1183305 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183308 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term153 _27538 _27539 _27540 _27541 l f m g P) = (term153 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1183307 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183309 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1183310 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term154 _27538 _27539 _27540 _27541 l f m g P) = (term154 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1183309 _27539) (@lem1183308 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1183311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1183312 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term187 _27538 _27539 _27540 _27541 l f m g P) = (term187 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1183311) (@lem1183310 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1183313 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term216 _27538 _27539 _27540 _27541 l m P f x g y) = (term216 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1183312 _27538 _27539 _27540 _27541 l f m g P) (@lem1183249 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183315 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term383 _27538 _27539 _27540 _27541 l m P f x g y) = (term383 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (MK_COMB (@lem1183314) (@lem1183313 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183316 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) = (term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g).
Proof. exact (MK_COMB (@lem1183315 _27538 _27539 _27540 _27541 l m P f x g y) (@lem1183222 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g)). Qed.
Lemma lem1183317 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g.
Proof. exact (EQ_MP (@lem1183316 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) (@lem1183141 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183318 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term216 _27538 _27539 _27540 _27541 l m P f x g y.
Proof. exact (h1). Qed.
Lemma lem1183319 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g.
Proof. exact (h1). Qed.
Lemma lem1183320 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term158 _27538 _27539 _27540 _27541 l m P f x g y.
Proof. exact (proj2 (@lem1183318 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183321 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term154 _27538 _27539 _27540 _27541 l f m g P.
Proof. exact (proj1 (@lem1183318 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183323 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term159 _27540 _27541 x l y m.
Proof. exact (proj1 (@lem1183320 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183326 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term181 _27538 _27539 _27540 _27541 l m P f g.
Proof. exact (proj2 (@lem1183319 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183327 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term278 _27538 _27539 _27540 _27541 l f x'' m g x''' P x' y'.
Proof. exact (proj1 (@lem1183319 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183329 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term244 _27538 _27539 _27540 _27541 l x' f x'' m y' g x'''.
Proof. exact (proj1 (@lem1183327 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183330 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term107 _27538 _27541 m y' g x'''.
Proof. exact (proj2 (@lem1183329 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183331 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term107 _27539 _27540 l x' f x''.
Proof. exact (proj1 (@lem1183329 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183337 {A : Type'} (P : A -> Prop) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1183338 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term449 _27540 P Q) = (term450 _27540 P Q).
Proof. exact (@lem1183337 _27540 P Q). Qed.
Lemma lem1183339 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term451 _27538 _27539 _27540 _27541 l x f m y g) = (term452 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (@lem1183338 _27540 (term120 _27539 _27540 l x f) (term121 _27538 _27541 m y g)). Qed.
Lemma lem1183340 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term453 _27539 _27540 l x f x') = (term112 _27539 _27540 l x f x').
Proof. exact (eq_refl (term453 _27539 _27540 l x f x')). Qed.
Lemma lem1183341 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term454 _27539 _27540 l x f) = (term120 _27539 _27540 l x f).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183340 _27539 _27540 l x f x')). Qed.
Lemma lem1183342 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183343 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term455 _27539 _27540 l x f) = (term121 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1183342 _27540) (@lem1183341 _27539 _27540 l x f)). Qed.
Lemma lem1183344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183345 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) : (term456 _27539 _27540 l x f) = (term123 _27539 _27540 l x f).
Proof. exact (MK_COMB (@lem1183344) (@lem1183343 _27539 _27540 l x f)). Qed.
Lemma lem1183346 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term121 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (eq_refl (term121 _27538 _27541 m y g)). Qed.
Lemma lem1183347 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term451 _27538 _27539 _27540 _27541 l x f m y g) = (term125 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183345 _27539 _27540 l x f) (@lem1183346 _27538 _27541 m y g)). Qed.
Lemma lem1183348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183349 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term457 _27538 _27539 _27540 _27541 l x f m y g) = (term458 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183348) (@lem1183347 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183350 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term453 _27539 _27540 l x f x') = (term112 _27539 _27540 l x f x').
Proof. exact (eq_refl (term453 _27539 _27540 l x f x')). Qed.
Lemma lem1183351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183352 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term459 _27539 _27540 l x f x') = (term460 _27539 _27540 l x f x').
Proof. exact (MK_COMB (@lem1183351) (@lem1183350 _27539 _27540 l x f x')). Qed.
Lemma lem1183353 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term121 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (eq_refl (term121 _27538 _27541 m y g)). Qed.
Lemma lem1183354 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term461 _27538 _27539 _27540 _27541 l x f x' m y g) = (term462 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183352 _27539 _27540 l x f x') (@lem1183353 _27538 _27541 m y g)). Qed.
Lemma lem1183355 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term463 _27538 _27539 _27540 _27541 l x f m y g) = (term464 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183354 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183356 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183357 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term452 _27538 _27539 _27540 _27541 l x f m y g) = (term465 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183356 _27540) (@lem1183355 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183358 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : ((term451 _27538 _27539 _27540 _27541 l x f m y g) = (term452 _27538 _27539 _27540 _27541 l x f m y g)) = ((term125 _27538 _27539 _27540 _27541 l x f m y g) = (term465 _27538 _27539 _27540 _27541 l x f m y g)).
Proof. exact (MK_COMB (@lem1183349 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183357 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183359 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term125 _27538 _27539 _27540 _27541 l x f m y g) = (term465 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (EQ_MP (@lem1183358 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183339 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183361 {A : Type'} (P : Prop) (Q : A -> Prop) : (term466 A P Q) = (term467 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1183362 {_27541 : Type'} (P : Prop) (Q : _27541 -> Prop) : (term466 _27541 P Q) = (term467 _27541 P Q).
Proof. exact (@lem1183361 _27541 P Q). Qed.
Lemma lem1183363 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term468 _27538 _27539 _27540 _27541 l x f x' m y g) = (term469 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (@lem1183362 _27541 (term112 _27539 _27540 l x f x') (term120 _27538 _27541 m y g)). Qed.
Lemma lem1183364 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term453 _27538 _27541 m y g x) = (term112 _27538 _27541 m y g x).
Proof. exact (eq_refl (term453 _27538 _27541 m y g x)). Qed.
Lemma lem1183365 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term454 _27538 _27541 m y g) = (term120 _27538 _27541 m y g).
Proof. exact (fun_ext (fun x : _27541 => @lem1183364 _27538 _27541 m y g x)). Qed.
Lemma lem1183366 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183367 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term455 _27538 _27541 m y g) = (term121 _27538 _27541 m y g).
Proof. exact (MK_COMB (@lem1183366 _27541) (@lem1183365 _27538 _27541 m y g)). Qed.
Lemma lem1183368 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term460 _27539 _27540 l x f x') = (term460 _27539 _27540 l x f x').
Proof. exact (eq_refl (term460 _27539 _27540 l x f x')). Qed.
Lemma lem1183369 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term468 _27538 _27539 _27540 _27541 l x f x' m y g) = (term462 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183368 _27539 _27540 l x f x') (@lem1183367 _27538 _27541 m y g)). Qed.
Lemma lem1183370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183371 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term470 _27538 _27539 _27540 _27541 l x f x' m y g) = (term471 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183370) (@lem1183369 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183372 {_27538 _27541 : Type'} (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x : _27541) : (term453 _27538 _27541 m y g x) = (term112 _27538 _27541 m y g x).
Proof. exact (eq_refl (term453 _27538 _27541 m y g x)). Qed.
Lemma lem1183373 {_27539 _27540 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) : (term460 _27539 _27540 l x f x') = (term460 _27539 _27540 l x f x').
Proof. exact (eq_refl (term460 _27539 _27540 l x f x')). Qed.
Lemma lem1183374 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term472 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term473 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (MK_COMB (@lem1183373 _27539 _27540 l x f x') (@lem1183372 _27538 _27541 m y g x'')). Qed.
Lemma lem1183375 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term474 _27538 _27539 _27540 _27541 l x f x' m y g) = (term475 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1183374 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1183376 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183377 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term469 _27538 _27539 _27540 _27541 l x f x' m y g) = (term476 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183376 _27541) (@lem1183375 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183378 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : ((term468 _27538 _27539 _27540 _27541 l x f x' m y g) = (term469 _27538 _27539 _27540 _27541 l x f x' m y g)) = ((term462 _27538 _27539 _27540 _27541 l x f x' m y g) = (term476 _27538 _27539 _27540 _27541 l x f x' m y g)).
Proof. exact (MK_COMB (@lem1183371 _27538 _27539 _27540 _27541 l x f x' m y g) (@lem1183377 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183379 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term462 _27538 _27539 _27540 _27541 l x f x' m y g) = (term476 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (EQ_MP (@lem1183378 _27538 _27539 _27540 _27541 l x f x' m y g) (@lem1183363 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183380 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term464 _27538 _27539 _27540 _27541 l x f m y g) = (term477 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183379 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183381 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183382 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term465 _27538 _27539 _27540 _27541 l x f m y g) = (term478 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183381 _27540) (@lem1183380 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183383 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term125 _27538 _27539 _27540 _27541 l x f m y g) = (term478 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (TRANS (@lem1183359 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183382 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183385 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term132 _27538 _27539 _27540 _27541 l x f m y g) = (term479 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183384) (@lem1183383 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183386 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183387 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term134 _27538 _27539 _27540 _27541 l f m g P x y) = (term480 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183385 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183386 _27538 _27539 P x y)). Qed.
Lemma lem1183389 {A : Type'} (P : A -> Prop) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1183390 {_27540 : Type'} (P : _27540 -> Prop) (Q : Prop) : (term449 _27540 P Q) = (term450 _27540 P Q).
Proof. exact (@lem1183389 _27540 P Q). Qed.
Lemma lem1183391 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term481 _27538 _27539 _27540 _27541 l f m g P x y) = (term482 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (@lem1183390 _27540 (term477 _27538 _27539 _27540 _27541 l x f m y g) (P x y)). Qed.
Lemma lem1183392 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term483 _27538 _27539 _27540 _27541 l x f m y g x') = (term476 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (eq_refl (term483 _27538 _27539 _27540 _27541 l x f m y g x')). Qed.
Lemma lem1183393 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term484 _27538 _27539 _27540 _27541 l x f m y g) = (term477 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183392 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183394 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183395 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term485 _27538 _27539 _27540 _27541 l x f m y g) = (term478 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183394 _27540) (@lem1183393 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183397 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term486 _27538 _27539 _27540 _27541 l x f m y g) = (term479 _27538 _27539 _27540 _27541 l x f m y g).
Proof. exact (MK_COMB (@lem1183396) (@lem1183395 _27538 _27539 _27540 _27541 l x f m y g)). Qed.
Lemma lem1183398 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183399 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term481 _27538 _27539 _27540 _27541 l f m g P x y) = (term480 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183397 _27538 _27539 _27540 _27541 l x f m y g) (@lem1183398 _27538 _27539 P x y)). Qed.
Lemma lem1183400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183401 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term487 _27538 _27539 _27540 _27541 l f m g P x y) = (term488 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183400) (@lem1183399 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183402 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term483 _27538 _27539 _27540 _27541 l x f m y g x') = (term476 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (eq_refl (term483 _27538 _27539 _27540 _27541 l x f m y g x')). Qed.
Lemma lem1183403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183404 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term489 _27538 _27539 _27540 _27541 l x f m y g x') = (term490 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183403) (@lem1183402 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183405 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183406 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term491 _27538 _27539 _27540 _27541 l f m g x P x' y) = (term492 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1183404 _27538 _27539 _27540 _27541 l x' f x m y g) (@lem1183405 _27538 _27539 P x' y)). Qed.
Lemma lem1183407 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term493 _27538 _27539 _27540 _27541 l f m g P x y) = (term494 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183406 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1183408 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183409 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term482 _27538 _27539 _27540 _27541 l f m g P x y) = (term495 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183408 _27540) (@lem1183407 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183410 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : ((term481 _27538 _27539 _27540 _27541 l f m g P x y) = (term482 _27538 _27539 _27540 _27541 l f m g P x y)) = ((term480 _27538 _27539 _27540 _27541 l f m g P x y) = (term495 _27538 _27539 _27540 _27541 l f m g P x y)).
Proof. exact (MK_COMB (@lem1183401 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1183409 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183411 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term480 _27538 _27539 _27540 _27541 l f m g P x y) = (term495 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (EQ_MP (@lem1183410 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1183391 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183413 {A : Type'} (P : A -> Prop) (Q : Prop) : (term449 A P Q) = (term450 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1183414 {_27541 : Type'} (P : _27541 -> Prop) (Q : Prop) : (term449 _27541 P Q) = (term450 _27541 P Q).
Proof. exact (@lem1183413 _27541 P Q). Qed.
Lemma lem1183415 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term496 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term497 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (@lem1183414 _27541 (term475 _27538 _27539 _27540 _27541 l x' f x m y g) (P x' y)). Qed.
Lemma lem1183416 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term498 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term473 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (eq_refl (term498 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1183417 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term499 _27538 _27539 _27540 _27541 l x f x' m y g) = (term475 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1183416 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1183418 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183419 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term500 _27538 _27539 _27540 _27541 l x f x' m y g) = (term476 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183418 _27541) (@lem1183417 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183421 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) : (term501 _27538 _27539 _27540 _27541 l x f x' m y g) = (term490 _27538 _27539 _27540 _27541 l x f x' m y g).
Proof. exact (MK_COMB (@lem1183420) (@lem1183419 _27538 _27539 _27540 _27541 l x f x' m y g)). Qed.
Lemma lem1183422 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183423 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term496 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term492 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1183421 _27538 _27539 _27540 _27541 l x' f x m y g) (@lem1183422 _27538 _27539 P x' y)). Qed.
Lemma lem1183424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183425 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term502 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term503 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1183424) (@lem1183423 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1183426 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term498 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term473 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (eq_refl (term498 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1183427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1183428 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (x : _27539) (f : _27540 -> _27539) (x' : _27540) (m : list _27541) (y : _27538) (g : _27541 -> _27538) (x'' : _27541) : (term504 _27538 _27539 _27540 _27541 l x f x' m y g x'') = (term505 _27538 _27539 _27540 _27541 l x f x' m y g x'').
Proof. exact (MK_COMB (@lem1183427) (@lem1183426 _27538 _27539 _27540 _27541 l x f x' m y g x'')). Qed.
Lemma lem1183429 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1183430 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term506 _27538 _27539 _27540 _27541 l f x m g x' P x'' y) = (term507 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (MK_COMB (@lem1183428 _27538 _27539 _27540 _27541 l x'' f x m y g x') (@lem1183429 _27538 _27539 P x'' y)). Qed.
Lemma lem1183431 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term508 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term509 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1183430 _27538 _27539 _27540 _27541 l f x m g x'' P x' y)). Qed.
Lemma lem1183432 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183433 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term497 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term510 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1183432 _27541) (@lem1183431 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1183434 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : ((term496 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term497 _27538 _27539 _27540 _27541 l f x m g P x' y)) = ((term492 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term510 _27538 _27539 _27540 _27541 l f x m g P x' y)).
Proof. exact (MK_COMB (@lem1183425 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1183433 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1183435 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term492 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term510 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (EQ_MP (@lem1183434 _27538 _27539 _27540 _27541 l f x m g P x' y) (@lem1183415 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1183436 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term494 _27538 _27539 _27540 _27541 l f m g P x y) = (term511 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183435 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1183437 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183438 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term495 _27538 _27539 _27540 _27541 l f m g P x y) = (term512 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183437 _27540) (@lem1183436 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183439 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term480 _27538 _27539 _27540 _27541 l f m g P x y) = (term512 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1183411 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1183438 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183440 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term134 _27538 _27539 _27540 _27541 l f m g P x y) = (term512 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (TRANS (@lem1183387 _27538 _27539 _27540 _27541 l f m g P x y) (@lem1183439 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183441 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term144 _27538 _27539 _27540 _27541 l f m g P x) = (term513 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1183440 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183442 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1183443 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term145 _27538 _27539 _27540 _27541 l f m g P x) = (term514 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1183442 _27538) (@lem1183441 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183444 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term153 _27538 _27539 _27540 _27541 l f m g P) = (term515 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1183443 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183445 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1183446 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term154 _27538 _27539 _27540 _27541 l f m g P) = (term516 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1183445 _27539) (@lem1183444 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1183471 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (x' : _27541) (P : type1470 _27538 _27539) (x'' : _27539) (y : _27538) : (term507 _27538 _27539 _27540 _27541 l f x m g x' P x'' y) = (term507 _27538 _27539 _27540 _27541 l f x m g x' P x'' y).
Proof. exact (eq_refl (term507 _27538 _27539 _27540 _27541 l f x m g x' P x'' y)). Qed.
Lemma lem1183472 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term509 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term509 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (fun_ext (fun x'' : _27541 => @lem1183471 _27538 _27539 _27540 _27541 l f x m g x'' P x' y)). Qed.
Lemma lem1183473 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183474 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (x : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x' : _27539) (y : _27538) : (term510 _27538 _27539 _27540 _27541 l f x m g P x' y) = (term510 _27538 _27539 _27540 _27541 l f x m g P x' y).
Proof. exact (MK_COMB (@lem1183473 _27541) (@lem1183472 _27538 _27539 _27540 _27541 l f x m g P x' y)). Qed.
Lemma lem1183475 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term511 _27538 _27539 _27540 _27541 l f m g P x y) = (term511 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (fun_ext (fun x' : _27540 => @lem1183474 _27538 _27539 _27540 _27541 l f x' m g P x y)). Qed.
Lemma lem1183476 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183477 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) (y : _27538) : (term512 _27538 _27539 _27540 _27541 l f m g P x y) = (term512 _27538 _27539 _27540 _27541 l f m g P x y).
Proof. exact (MK_COMB (@lem1183476 _27540) (@lem1183475 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183478 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term513 _27538 _27539 _27540 _27541 l f m g P x) = (term513 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (fun_ext (fun y : _27538 => @lem1183477 _27538 _27539 _27540 _27541 l f m g P x y)). Qed.
Lemma lem1183479 {_27538 : Type'} : (@all _27538) = (@all _27538).
Proof. exact (eq_refl (@all _27538)). Qed.
Lemma lem1183480 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (x : _27539) : (term514 _27538 _27539 _27540 _27541 l f m g P x) = (term514 _27538 _27539 _27540 _27541 l f m g P x).
Proof. exact (MK_COMB (@lem1183479 _27538) (@lem1183478 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183481 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term515 _27538 _27539 _27540 _27541 l f m g P) = (term515 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (fun_ext (fun x : _27539 => @lem1183480 _27538 _27539 _27540 _27541 l f m g P x)). Qed.
Lemma lem1183482 {_27539 : Type'} : (@all _27539) = (@all _27539).
Proof. exact (eq_refl (@all _27539)). Qed.
Lemma lem1183483 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term516 _27538 _27539 _27540 _27541 l f m g P) = (term516 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (MK_COMB (@lem1183482 _27539) (@lem1183481 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1183484 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) : (term154 _27538 _27539 _27540 _27541 l f m g P) = (term516 _27538 _27539 _27540 _27541 l f m g P).
Proof. exact (TRANS (@lem1183446 _27538 _27539 _27540 _27541 l f m g P) (@lem1183483 _27538 _27539 _27540 _27541 l f m g P)). Qed.
Lemma lem1183485 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term516 _27538 _27539 _27540 _27541 l f m g P.
Proof. exact (EQ_MP (@lem1183484 _27538 _27539 _27540 _27541 l f m g P) (@lem1183321 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183511 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term163 _27538 _27539 _27540 _27541 l m P f x g y) = (term163 _27538 _27539 _27540 _27541 l m P f x g y).
Proof. exact (eq_refl (term163 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183512 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term171 _27538 _27539 _27540 _27541 l m P f x g) = (term171 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (fun_ext (fun y : _27541 => @lem1183511 _27538 _27539 _27540 _27541 l m P f x g y)). Qed.
Lemma lem1183513 {_27541 : Type'} : (@all _27541) = (@all _27541).
Proof. exact (eq_refl (@all _27541)). Qed.
Lemma lem1183514 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) : (term172 _27538 _27539 _27540 _27541 l m P f x g) = (term172 _27538 _27539 _27540 _27541 l m P f x g).
Proof. exact (MK_COMB (@lem1183513 _27541) (@lem1183512 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183515 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term180 _27538 _27539 _27540 _27541 l m P f g) = (term180 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (fun_ext (fun x : _27540 => @lem1183514 _27538 _27539 _27540 _27541 l m P f x g)). Qed.
Lemma lem1183516 {_27540 : Type'} : (@all _27540) = (@all _27540).
Proof. exact (eq_refl (@all _27540)). Qed.
Lemma lem1183518 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term181 _27538 _27539 _27540 _27541 l m P f g) = (term181 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (MK_COMB (@lem1183516 _27540) (@lem1183515 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1183519 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term181 _27538 _27539 _27540 _27541 l m P f g.
Proof. exact (EQ_MP (@lem1183518 _27538 _27539 _27540 _27541 l m P f g) (@lem1183326 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183540 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term517 _27538 _27539 _27540 _27541 l f m g P _21160.
Proof. exact (@lem1183485 _27538 _27539 _27540 _27541 l m P f x g y h1 _21160). Qed.
Lemma lem1183541 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (_21160 : _27539) : (term517 _27538 _27539 _27540 _27541 l f m g P _21160) = (term514 _27538 _27539 _27540 _27541 l f m g P _21160).
Proof. exact (eq_refl (term517 _27538 _27539 _27540 _27541 l f m g P _21160)). Qed.
Lemma lem1183542 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term514 _27538 _27539 _27540 _27541 l f m g P _21160.
Proof. exact (EQ_MP (@lem1183541 _27538 _27539 _27540 _27541 l f m g P _21160) (@lem1183540 _27538 _27539 _27540 _27541 _21160 l m P f x g y h1)). Qed.
Lemma lem1183543 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term518 _27538 _27539 _27540 _27541 l f m g P _21160 _21161.
Proof. exact (@lem1183542 _27538 _27539 _27540 _27541 _21160 l m P f x g y h1 _21161). Qed.
Lemma lem1183544 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term518 _27538 _27539 _27540 _27541 l f m g P _21160 _21161) = (term512 _27538 _27539 _27540 _27541 l f m g P _21160 _21161).
Proof. exact (eq_refl (term518 _27538 _27539 _27540 _27541 l f m g P _21160 _21161)). Qed.
Lemma lem1183545 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term512 _27538 _27539 _27540 _27541 l f m g P _21160 _21161.
Proof. exact (EQ_MP (@lem1183544 _27538 _27539 _27540 _27541 l f m g P _21160 _21161) (@lem1183543 _27538 _27539 _27540 _27541 _21160 _21161 l m P f x g y h1)). Qed.
Lemma lem1183546 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (_21161 : _27538) (_21162 : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term519 _27538 _27539 _27540 _27541 l f m g P _21160 _21161 _21162.
Proof. exact (@lem1183545 _27538 _27539 _27540 _27541 _21160 _21161 l m P f x g y h1 _21162). Qed.
Lemma lem1183547 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term519 _27538 _27539 _27540 _27541 l f m g P _21160 _21161 _21162) = (term510 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161).
Proof. exact (eq_refl (term519 _27538 _27539 _27540 _27541 l f m g P _21160 _21161 _21162)). Qed.
Lemma lem1183548 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term510 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161.
Proof. exact (EQ_MP (@lem1183547 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161) (@lem1183546 _27538 _27539 _27540 _27541 _21160 _21161 _21162 l m P f x g y h1)). Qed.
Lemma lem1183549 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21160 : _27539) (_21161 : _27538) (_21163 : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term520 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161 _21163.
Proof. exact (@lem1183548 _27538 _27539 _27540 _27541 _21162 _21160 _21161 l m P f x g y h1 _21163). Qed.
Lemma lem1183550 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term520 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161 _21163) = (term507 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (eq_refl (term520 _27538 _27539 _27540 _27541 l f _21162 m g P _21160 _21161 _21163)). Qed.
Lemma lem1183551 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21163 : _27541) (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term507 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161.
Proof. exact (EQ_MP (@lem1183550 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1183549 _27538 _27539 _27540 _27541 _21162 _21160 _21161 _21163 l m P f x g y h1)). Qed.
Lemma lem1183552 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term521 _27538 _27539 _27540 _27541 l m P f g _21164.
Proof. exact (@lem1183519 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1 _21164). Qed.
Lemma lem1183553 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) : (term521 _27538 _27539 _27540 _27541 l m P f g _21164) = (term172 _27538 _27539 _27540 _27541 l m P f _21164 g).
Proof. exact (eq_refl (term521 _27538 _27539 _27540 _27541 l m P f g _21164)). Qed.
Lemma lem1183554 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term172 _27538 _27539 _27540 _27541 l m P f _21164 g.
Proof. exact (EQ_MP (@lem1183553 _27538 _27539 _27540 _27541 l m P f _21164 g) (@lem1183552 _27538 _27539 _27540 _27541 _21164 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183555 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term522 _27538 _27539 _27540 _27541 l m P f _21164 g _21165.
Proof. exact (@lem1183554 _27538 _27539 _27540 _27541 _21164 x'' x''' x' y' l m P f g h1 _21165). Qed.
Lemma lem1183556 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term522 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term163 _27538 _27539 _27540 _27541 l m P f _21164 g _21165).
Proof. exact (eq_refl (term522 _27538 _27539 _27540 _27541 l m P f _21164 g _21165)). Qed.
Lemma lem1183557 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term163 _27538 _27539 _27540 _27541 l m P f _21164 g _21165.
Proof. exact (EQ_MP (@lem1183556 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) (@lem1183555 _27538 _27539 _27540 _27541 _21164 _21165 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183561 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term507 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term523 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (@lem1181604 (term112 _27539 _27540 l _21160 f _21162) (term112 _27538 _27541 m _21161 g _21163) (P _21160 _21161)). Qed.
Lemma lem1183568 {_27538 _27539 _27541 : Type'} (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term524 _27538 _27539 _27541 m g _21163 P _21160 _21161) = (term525 _27538 _27539 _27541 m g _21163 P _21160 _21161).
Proof. exact (@lem1181604 (term526 _27541 _21163 m) (term527 _27538 _27541 _21161 g _21163) (P _21160 _21161)). Qed.
Lemma lem1183569 {_27539 _27540 : Type'} (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) : (term460 _27539 _27540 l _21160 f _21162) = (term460 _27539 _27540 l _21160 f _21162).
Proof. exact (eq_refl (term460 _27539 _27540 l _21160 f _21162)). Qed.
Lemma lem1183570 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term523 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term528 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (MK_COMB (@lem1183569 _27539 _27540 l _21160 f _21162) (@lem1183568 _27538 _27539 _27541 m g _21163 P _21160 _21161)). Qed.
Lemma lem1183577 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term528 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (@lem1181604 (term526 _27540 _21162 l) (term527 _27539 _27540 _21160 f _21162) (term525 _27538 _27539 _27541 m g _21163 P _21160 _21161)). Qed.
Lemma lem1183578 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term523 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (TRANS (@lem1183570 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1183577 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161)). Qed.
Lemma lem1183580 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term507 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (TRANS (@lem1183561 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1183578 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161)). Qed.
Lemma lem1183581 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21163 : _27541) (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161.
Proof. exact (EQ_MP (@lem1183580 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1183551 _27538 _27539 _27540 _27541 _21162 _21163 _21160 _21161 l m P f x g y h1)). Qed.
Lemma lem1183583 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term530 _27538 _27539 _27540 _27541 P f x g y.
Proof. exact (proj2 (@lem1183320 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183598 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term163 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165).
Proof. exact (@lem1181604 (term526 _27540 _21164 l) (term526 _27541 _21165 m) (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165)). Qed.
Lemma lem1183601 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term127 _27538 _27539 P x' y'.
Proof. exact (proj2 (@lem1183327 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183609 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : x' = (f x'').
Proof. exact (proj2 (@lem1183331 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183638 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (y' : _27538) : (term532 _27538 _27539 P y') = (term532 _27538 _27539 P y').
Proof. exact (eq_refl (term532 _27538 _27539 P y')). Qed.
Lemma lem1183639 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : (term533 _27538 _27539 P y' x') = (term534 _27538 _27539 _27540 P y' f x'').
Proof. exact (MK_COMB (@lem1183638 _27538 _27539 P y') (@lem1183609 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183640 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : (term534 _27538 _27539 _27540 P y' f x'') = (term535 _27538 _27539 _27540 P f x'' y').
Proof. exact (eq_refl (term534 _27538 _27539 _27540 P y' f x'')). Qed.
Lemma lem1183641 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (y' : _27538) (x' : _27539) : (term536 _27538 _27539 P y' x') = (term536 _27538 _27539 P y' x').
Proof. exact (eq_refl (term536 _27538 _27539 P y' x')). Qed.
Lemma lem1183642 {_27538 _27539 _27540 : Type'} (x' : _27539) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : ((term533 _27538 _27539 P y' x') = (term534 _27538 _27539 _27540 P y' f x'')) = ((term533 _27538 _27539 P y' x') = (term535 _27538 _27539 _27540 P f x'' y')).
Proof. exact (MK_COMB (@lem1183641 _27538 _27539 P y' x') (@lem1183640 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183643 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x' : _27539) (y' : _27538) : (term533 _27538 _27539 P y' x') = (term127 _27538 _27539 P x' y').
Proof. exact (eq_refl (term533 _27538 _27539 P y' x')). Qed.
Lemma lem1183644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183645 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (x' : _27539) (y' : _27538) : (term536 _27538 _27539 P y' x') = (term537 _27538 _27539 P x' y').
Proof. exact (MK_COMB (@lem1183644) (@lem1183643 _27538 _27539 P x' y')). Qed.
Lemma lem1183646 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : (term535 _27538 _27539 _27540 P f x'' y') = (term535 _27538 _27539 _27540 P f x'' y').
Proof. exact (eq_refl (term535 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183647 {_27538 _27539 _27540 : Type'} (x' : _27539) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : ((term533 _27538 _27539 P y' x') = (term535 _27538 _27539 _27540 P f x'' y')) = ((term127 _27538 _27539 P x' y') = (term535 _27538 _27539 _27540 P f x'' y')).
Proof. exact (MK_COMB (@lem1183645 _27538 _27539 P x' y') (@lem1183646 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183648 {_27538 _27539 _27540 : Type'} (x' : _27539) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : ((term533 _27538 _27539 P y' x') = (term534 _27538 _27539 _27540 P y' f x'')) = ((term127 _27538 _27539 P x' y') = (term535 _27538 _27539 _27540 P f x'' y')).
Proof. exact (TRANS (@lem1183642 _27538 _27539 _27540 x' P f x'' y') (@lem1183647 _27538 _27539 _27540 x' P f x'' y')). Qed.
Lemma lem1183649 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : (term127 _27538 _27539 P x' y') = (term535 _27538 _27539 _27540 P f x'' y').
Proof. exact (EQ_MP (@lem1183648 _27538 _27539 _27540 x' P f x'' y') (@lem1183639 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183650 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term535 _27538 _27539 _27540 P f x'' y'.
Proof. exact (EQ_MP (@lem1183649 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1) (@lem1183601 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183678 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : y' = (g x''').
Proof. exact (proj2 (@lem1183330 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183720 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165.
Proof. exact (EQ_MP (@lem1183598 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) (@lem1183557 _27538 _27539 _27540 _27541 _21164 _21165 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183721 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) : (term538 _27538 _27539 _27540 P f x'') = (term538 _27538 _27539 _27540 P f x'').
Proof. exact (eq_refl (term538 _27538 _27539 _27540 P f x'')). Qed.
Lemma lem1183722 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : (term539 _27538 _27539 _27540 P f x'' y') = (term540 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (MK_COMB (@lem1183721 _27538 _27539 _27540 P f x'') (@lem1183678 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183723 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : (term540 _27538 _27539 _27540 _27541 P f x'' g x''') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (eq_refl (term540 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1183724 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : (term541 _27538 _27539 _27540 P f x'' y') = (term541 _27538 _27539 _27540 P f x'' y').
Proof. exact (eq_refl (term541 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183725 {_27538 _27539 _27540 _27541 : Type'} (y' : _27538) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : ((term539 _27538 _27539 _27540 P f x'' y') = (term540 _27538 _27539 _27540 _27541 P f x'' g x''')) = ((term539 _27538 _27539 _27540 P f x'' y') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''')).
Proof. exact (MK_COMB (@lem1183724 _27538 _27539 _27540 P f x'' y') (@lem1183723 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1183726 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : (term539 _27538 _27539 _27540 P f x'' y') = (term535 _27538 _27539 _27540 P f x'' y').
Proof. exact (eq_refl (term539 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1183728 {_27538 _27539 _27540 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (y' : _27538) : (term541 _27538 _27539 _27540 P f x'' y') = (term542 _27538 _27539 _27540 P f x'' y').
Proof. exact (MK_COMB (@lem1183727) (@lem1183726 _27538 _27539 _27540 P f x'' y')). Qed.
Lemma lem1183729 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : (term530 _27538 _27539 _27540 _27541 P f x'' g x''') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (eq_refl (term530 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1183730 {_27538 _27539 _27540 _27541 : Type'} (y' : _27538) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : ((term539 _27538 _27539 _27540 P f x'' y') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''')) = ((term535 _27538 _27539 _27540 P f x'' y') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''')).
Proof. exact (MK_COMB (@lem1183728 _27538 _27539 _27540 P f x'' y') (@lem1183729 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1183731 {_27538 _27539 _27540 _27541 : Type'} (y' : _27538) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : ((term539 _27538 _27539 _27540 P f x'' y') = (term540 _27538 _27539 _27540 _27541 P f x'' g x''')) = ((term535 _27538 _27539 _27540 P f x'' y') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''')).
Proof. exact (TRANS (@lem1183725 _27538 _27539 _27540 _27541 y' P f x'' g x''') (@lem1183730 _27538 _27539 _27540 _27541 y' P f x'' g x''')). Qed.
Lemma lem1183732 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : (term535 _27538 _27539 _27540 P f x'' y') = (term530 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (EQ_MP (@lem1183731 _27538 _27539 _27540 _27541 y' P f x'' g x''') (@lem1183722 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183733 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term530 _27538 _27539 _27540 _27541 P f x'' g x'''.
Proof. exact (EQ_MP (@lem1183732 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1) (@lem1183650 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1183848 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : @List.In _27540 x l.
Proof. exact (proj1 (@lem1183323 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183849 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term543 _27540 x l.
Proof. exact (fun h0 : term526 _27540 x l => @lem1183848 _27538 _27539 _27540 _27541 l m P f x g y h1). Qed.
Lemma lem1183851 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1183852 {_27540 : Type'} (x : _27540) (l : list _27540) : (term543 _27540 x l) = (@List.In _27540 x l).
Proof. exact (@lem1183851 (@List.In _27540 x l)). Qed.
Lemma lem1183853 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : @List.In _27540 x l.
Proof. exact (EQ_MP (@lem1183852 _27540 x l) (@lem1183849 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183855 {_27539 : Type'} (x : _27539) : x = x.
Proof. exact (@lem21386 _27539 x). Qed.
Lemma lem1183856 {_27539 : Type'} (x : _27539) : x = x.
Proof. exact (@lem1183855 _27539 x). Qed.
Lemma lem1183857 {_27539 _27540 : Type'} (f : _27540 -> _27539) (x : _27540) : (f x) = (f x).
Proof. exact (@lem1183856 _27539 (f x)). Qed.
Lemma lem1183858 {_27539 _27540 : Type'} (f : _27540 -> _27539) (x : _27540) : term545 _27539 _27540 f x.
Proof. exact (fun h0 : term546 _27539 _27540 f x => @lem1183857 _27539 _27540 f x). Qed.
Lemma lem1183860 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1183861 {_27539 _27540 : Type'} (f : _27540 -> _27539) (x : _27540) : (term545 _27539 _27540 f x) = ((f x) = (f x)).
Proof. exact (@lem1183860 ((f x) = (f x))). Qed.
Lemma lem1183862 {_27539 _27540 : Type'} (f : _27540 -> _27539) (x : _27540) : (f x) = (f x).
Proof. exact (EQ_MP (@lem1183861 _27539 _27540 f x) (@lem1183858 _27539 _27540 f x)). Qed.
Lemma lem1183864 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : @List.In _27541 y m.
Proof. exact (proj2 (@lem1183323 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183865 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term543 _27541 y m.
Proof. exact (fun h0 : term526 _27541 y m => @lem1183864 _27538 _27539 _27540 _27541 l m P f x g y h1). Qed.
Lemma lem1183867 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1183868 {_27541 : Type'} (y : _27541) (m : list _27541) : (term543 _27541 y m) = (@List.In _27541 y m).
Proof. exact (@lem1183867 (@List.In _27541 y m)). Qed.
Lemma lem1183869 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : @List.In _27541 y m.
Proof. exact (EQ_MP (@lem1183868 _27541 y m) (@lem1183865 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1183871 {_27538 : Type'} (x : _27538) : x = x.
Proof. exact (@lem21386 _27538 x). Qed.
Lemma lem1183872 {_27538 : Type'} (x : _27538) : x = x.
Proof. exact (@lem1183871 _27538 x). Qed.
Lemma lem1183873 {_27538 _27541 : Type'} (g : _27541 -> _27538) (y : _27541) : (g y) = (g y).
Proof. exact (@lem1183872 _27538 (g y)). Qed.
Lemma lem1183874 {_27538 _27541 : Type'} (g : _27541 -> _27538) (y : _27541) : term545 _27538 _27541 g y.
Proof. exact (fun h0 : term546 _27538 _27541 g y => @lem1183873 _27538 _27541 g y). Qed.
Lemma lem1183876 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1183877 {_27538 _27541 : Type'} (g : _27541 -> _27538) (y : _27541) : (term545 _27538 _27541 g y) = ((g y) = (g y)).
Proof. exact (@lem1183876 ((g y) = (g y))). Qed.
Lemma lem1183878 {_27538 _27541 : Type'} (g : _27541 -> _27538) (y : _27541) : (g y) = (g y).
Proof. exact (EQ_MP (@lem1183877 _27538 _27541 g y) (@lem1183874 _27538 _27541 g y)). Qed.
Lemma lem1183884 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1183885 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term547 _27538 _27539 _27540 _27541 f _21162 l m g _21163 P _21160 _21161).
Proof. exact (@lem1183884 (term527 _27539 _27540 _21160 f _21162) (term526 _27540 _21162 l) (term525 _27538 _27539 _27541 m g _21163 P _21160 _21161)). Qed.
Lemma lem1183911 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1183912 {_27538 _27539 _27541 : Type'} (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term525 _27538 _27539 _27541 m g _21163 P _21160 _21161) = (term548 _27538 _27539 _27541 g _21163 m P _21160 _21161).
Proof. exact (@lem1183911 (term527 _27538 _27541 _21161 g _21163) (term526 _27541 _21163 m) (P _21160 _21161)). Qed.
Lemma lem1183928 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1183929 {_27538 _27539 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (_21163 : _27541) (m : list _27541) : (term549 _27538 _27539 _27541 _21163 m P _21160 _21161) = (term550 _27538 _27539 _27541 P _21160 _21161 _21163 m).
Proof. exact (@lem1183928 (P _21160 _21161) (term526 _27541 _21163 m)). Qed.
Lemma lem1183935 {_27538 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term551 _27538 _27541 _21161 g _21163) = (term551 _27538 _27541 _21161 g _21163).
Proof. exact (eq_refl (term551 _27538 _27541 _21161 g _21163)). Qed.
Lemma lem1183936 {_27538 _27539 _27541 : Type'} (g : _27541 -> _27538) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (_21163 : _27541) (m : list _27541) : (term548 _27538 _27539 _27541 g _21163 m P _21160 _21161) = (term552 _27538 _27539 _27541 g P _21160 _21161 _21163 m).
Proof. exact (MK_COMB (@lem1183935 _27538 _27541 _21161 g _21163) (@lem1183929 _27538 _27539 _27541 P _21160 _21161 _21163 m)). Qed.
Lemma lem1183940 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1183941 {_27538 _27539 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term552 _27538 _27539 _27541 g P _21160 _21161 _21163 m) = (term553 _27538 _27539 _27541 P _21160 _21161 g _21163 m).
Proof. exact (@lem1183940 (P _21160 _21161) (term527 _27538 _27541 _21161 g _21163) (term526 _27541 _21163 m)). Qed.
Lemma lem1183959 {_27538 _27539 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term548 _27538 _27539 _27541 g _21163 m P _21160 _21161) = (term553 _27538 _27539 _27541 P _21160 _21161 g _21163 m).
Proof. exact (TRANS (@lem1183936 _27538 _27539 _27541 g P _21160 _21161 _21163 m) (@lem1183941 _27538 _27539 _27541 P _21160 _21161 g _21163 m)). Qed.
Lemma lem1183960 {_27538 _27539 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term525 _27538 _27539 _27541 m g _21163 P _21160 _21161) = (term553 _27538 _27539 _27541 P _21160 _21161 g _21163 m).
Proof. exact (TRANS (@lem1183912 _27538 _27539 _27541 g _21163 m P _21160 _21161) (@lem1183959 _27538 _27539 _27541 P _21160 _21161 g _21163 m)). Qed.
Lemma lem1183961 {_27540 : Type'} (_21162 : _27540) (l : list _27540) : (term554 _27540 _21162 l) = (term554 _27540 _21162 l).
Proof. exact (eq_refl (term554 _27540 _21162 l)). Qed.
Lemma lem1183962 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (l : list _27540) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term555 _27538 _27539 _27540 _27541 _21162 l m g _21163 P _21160 _21161) = (term556 _27538 _27539 _27540 _27541 _21162 l P _21160 _21161 g _21163 m).
Proof. exact (MK_COMB (@lem1183961 _27540 _21162 l) (@lem1183960 _27538 _27539 _27541 P _21160 _21161 g _21163 m)). Qed.
Lemma lem1183966 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1183967 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21162 : _27540) (l : list _27540) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term556 _27538 _27539 _27540 _27541 _21162 l P _21160 _21161 g _21163 m) = (term557 _27538 _27539 _27540 _27541 P _21160 _21162 l _21161 g _21163 m).
Proof. exact (@lem1183966 (P _21160 _21161) (term526 _27540 _21162 l) (term558 _27538 _27541 _21161 g _21163 m)). Qed.
Lemma lem1183981 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1183982 {_27538 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term559 _27538 _27540 _27541 _21162 l _21161 g _21163 m) = (term560 _27538 _27540 _27541 _21161 g _21162 l _21163 m).
Proof. exact (@lem1183981 (term527 _27538 _27541 _21161 g _21163) (term526 _27540 _21162 l) (term526 _27541 _21163 m)). Qed.
Lemma lem1184000 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term561 _27538 _27539 P _21160 _21161) = (term561 _27538 _27539 P _21160 _21161).
Proof. exact (eq_refl (term561 _27538 _27539 P _21160 _21161)). Qed.
Lemma lem1184001 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term557 _27538 _27539 _27540 _27541 P _21160 _21162 l _21161 g _21163 m) = (term562 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184000 _27538 _27539 P _21160 _21161) (@lem1183982 _27538 _27540 _27541 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184012 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term556 _27538 _27539 _27540 _27541 _21162 l P _21160 _21161 g _21163 m) = (term562 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m).
Proof. exact (TRANS (@lem1183967 _27538 _27539 _27540 _27541 P _21160 _21162 l _21161 g _21163 m) (@lem1184001 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184013 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term555 _27538 _27539 _27540 _27541 _21162 l m g _21163 P _21160 _21161) = (term562 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m).
Proof. exact (TRANS (@lem1183962 _27538 _27539 _27540 _27541 _21162 l P _21160 _21161 g _21163 m) (@lem1184012 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184014 {_27539 _27540 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) : (term551 _27539 _27540 _21160 f _21162) = (term551 _27539 _27540 _21160 f _21162).
Proof. exact (eq_refl (term551 _27539 _27540 _21160 f _21162)). Qed.
Lemma lem1184015 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term547 _27538 _27539 _27540 _27541 f _21162 l m g _21163 P _21160 _21161) = (term563 _27538 _27539 _27540 _27541 f P _21160 _21161 g _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184014 _27539 _27540 _21160 f _21162) (@lem1184013 _27538 _27539 _27540 _27541 P _21160 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184019 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184020 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (f : _27540 -> _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term563 _27538 _27539 _27540 _27541 f P _21160 _21161 g _21162 l _21163 m) = (term564 _27538 _27539 _27540 _27541 P _21160 f _21161 g _21162 l _21163 m).
Proof. exact (@lem1184019 (P _21160 _21161) (term527 _27539 _27540 _21160 f _21162) (term560 _27538 _27540 _27541 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184034 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184035 {_27538 _27539 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term565 _27538 _27539 _27540 _27541 _21160 f _21161 g _21162 l _21163 m) = (term566 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m).
Proof. exact (@lem1184034 (term527 _27538 _27541 _21161 g _21163) (term527 _27539 _27540 _21160 f _21162) (term156 _27540 _27541 _21162 l _21163 m)). Qed.
Lemma lem1184065 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term561 _27538 _27539 P _21160 _21161) = (term561 _27538 _27539 P _21160 _21161).
Proof. exact (eq_refl (term561 _27538 _27539 P _21160 _21161)). Qed.
Lemma lem1184066 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term564 _27538 _27539 _27540 _27541 P _21160 f _21161 g _21162 l _21163 m) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184065 _27538 _27539 P _21160 _21161) (@lem1184035 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184077 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term563 _27538 _27539 _27540 _27541 f P _21160 _21161 g _21162 l _21163 m) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (TRANS (@lem1184020 _27538 _27539 _27540 _27541 P _21160 f _21161 g _21162 l _21163 m) (@lem1184066 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184078 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term547 _27538 _27539 _27540 _27541 f _21162 l m g _21163 P _21160 _21161) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (TRANS (@lem1184015 _27538 _27539 _27540 _27541 f P _21160 _21161 g _21162 l _21163 m) (@lem1184077 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184079 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (TRANS (@lem1183885 _27538 _27539 _27540 _27541 f _21162 l m g _21163 P _21160 _21161) (@lem1184078 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1184081 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term568 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term569 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184080) (@lem1184079 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184095 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184096 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term570 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term571 _27538 _27539 _27540 _27541 _21160 f _21162 l m _21161 g _21163).
Proof. exact (@lem1184095 (term527 _27539 _27540 _21160 f _21162) (term526 _27540 _21162 l) (term112 _27538 _27541 m _21161 g _21163)). Qed.
Lemma lem1184122 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1184123 {_27538 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term112 _27538 _27541 m _21161 g _21163) = (term558 _27538 _27541 _21161 g _21163 m).
Proof. exact (@lem1184122 (term527 _27538 _27541 _21161 g _21163) (term526 _27541 _21163 m)). Qed.
Lemma lem1184131 {_27540 : Type'} (_21162 : _27540) (l : list _27540) : (term554 _27540 _21162 l) = (term554 _27540 _21162 l).
Proof. exact (eq_refl (term554 _27540 _21162 l)). Qed.
Lemma lem1184132 {_27538 _27540 _27541 : Type'} (_21162 : _27540) (l : list _27540) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) (m : list _27541) : (term572 _27538 _27540 _27541 _21162 l m _21161 g _21163) = (term559 _27538 _27540 _27541 _21162 l _21161 g _21163 m).
Proof. exact (MK_COMB (@lem1184131 _27540 _21162 l) (@lem1184123 _27538 _27541 _21161 g _21163 m)). Qed.
Lemma lem1184136 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184137 {_27538 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term559 _27538 _27540 _27541 _21162 l _21161 g _21163 m) = (term560 _27538 _27540 _27541 _21161 g _21162 l _21163 m).
Proof. exact (@lem1184136 (term527 _27538 _27541 _21161 g _21163) (term526 _27540 _21162 l) (term526 _27541 _21163 m)). Qed.
Lemma lem1184155 {_27538 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term572 _27538 _27540 _27541 _21162 l m _21161 g _21163) = (term560 _27538 _27540 _27541 _21161 g _21162 l _21163 m).
Proof. exact (TRANS (@lem1184132 _27538 _27540 _27541 _21162 l _21161 g _21163 m) (@lem1184137 _27538 _27540 _27541 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184156 {_27539 _27540 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) : (term551 _27539 _27540 _21160 f _21162) = (term551 _27539 _27540 _21160 f _21162).
Proof. exact (eq_refl (term551 _27539 _27540 _21160 f _21162)). Qed.
Lemma lem1184157 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term571 _27538 _27539 _27540 _27541 _21160 f _21162 l m _21161 g _21163) = (term565 _27538 _27539 _27540 _27541 _21160 f _21161 g _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184156 _27539 _27540 _21160 f _21162) (@lem1184155 _27538 _27540 _27541 _21161 g _21162 l _21163 m)). Qed.
Lemma lem1184161 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184162 {_27538 _27539 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term565 _27538 _27539 _27540 _27541 _21160 f _21161 g _21162 l _21163 m) = (term566 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m).
Proof. exact (@lem1184161 (term527 _27538 _27541 _21161 g _21163) (term527 _27539 _27540 _21160 f _21162) (term156 _27540 _27541 _21162 l _21163 m)). Qed.
Lemma lem1184192 {_27538 _27539 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term571 _27538 _27539 _27540 _27541 _21160 f _21162 l m _21161 g _21163) = (term566 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m).
Proof. exact (TRANS (@lem1184157 _27538 _27539 _27540 _27541 _21160 f _21161 g _21162 l _21163 m) (@lem1184162 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184193 {_27538 _27539 _27540 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term570 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term566 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m).
Proof. exact (TRANS (@lem1184096 _27538 _27539 _27540 _27541 _21160 f _21162 l m _21161 g _21163) (@lem1184192 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184194 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term561 _27538 _27539 P _21160 _21161) = (term561 _27538 _27539 P _21160 _21161).
Proof. exact (eq_refl (term561 _27538 _27539 P _21160 _21161)). Qed.
Lemma lem1184195 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m).
Proof. exact (MK_COMB (@lem1184194 _27538 _27539 P _21160 _21161) (@lem1184193 _27538 _27539 _27540 _27541 _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184206 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : ((term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163)) = ((term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)).
Proof. exact (MK_COMB (@lem1184081 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m) (@lem1184195 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184208 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1184209 (x : Prop) : (x = x) = True.
Proof. exact (@lem1184208 Prop x). Qed.
Lemma lem1184210 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (_21161 : _27538) (g : _27541 -> _27538) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (l : list _27540) (_21163 : _27541) (m : list _27541) : ((term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m) = (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)) = True.
Proof. exact (@lem1184209 (term567 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184211 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : ((term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163)) = True.
Proof. exact (TRANS (@lem1184206 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m) (@lem1184210 _27538 _27539 _27540 _27541 P _21161 g _21160 f _21162 l _21163 m)). Qed.
Lemma lem1184212 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : True = ((term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163)).
Proof. exact (SYM (@lem1184211 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184213 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term529 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163).
Proof. exact (EQ_MP (@lem1184212 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163) (@lem0)). Qed.
Lemma lem1184214 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (_21162 : _27540) (_21161 : _27538) (_21163 : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163.
Proof. exact (EQ_MP (@lem1184213 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163) (@lem1183581 _27538 _27539 _27540 _27541 _21162 _21163 _21160 _21161 l m P f x g y h1)). Qed.
Lemma lem1184216 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1184217 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163) = (term575 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (@lem1184216 (term570 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) (P _21160 _21161)). Qed.
Lemma lem1184219 (a : Prop) (b : Prop) : (term576 a b) = (term577 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1184220 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term578 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term579 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163).
Proof. exact (@lem1184219 (term526 _27540 _21162 l) (term580 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184222 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184223 {_27540 : Type'} (_21162 : _27540) (l : list _27540) : (term581 _27540 _21162 l) = (@List.In _27540 _21162 l).
Proof. exact (@lem1184222 (@List.In _27540 _21162 l)). Qed.
Lemma lem1184224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184225 {_27540 : Type'} (_21162 : _27540) (l : list _27540) : (term582 _27540 _21162 l) = (term583 _27540 _21162 l).
Proof. exact (MK_COMB (@lem1184224) (@lem1184223 _27540 _21162 l)). Qed.
Lemma lem1184227 (a : Prop) (b : Prop) : (term576 a b) = (term577 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1184228 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term584 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163) = (term585 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163).
Proof. exact (@lem1184227 (term527 _27539 _27540 _21160 f _21162) (term112 _27538 _27541 m _21161 g _21163)). Qed.
Lemma lem1184230 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184231 {_27539 _27540 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) : (term586 _27539 _27540 _21160 f _21162) = (_21160 = (f _21162)).
Proof. exact (@lem1184230 (_21160 = (f _21162))). Qed.
Lemma lem1184232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184233 {_27539 _27540 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) : (term587 _27539 _27540 _21160 f _21162) = (term588 _27539 _27540 _21160 f _21162).
Proof. exact (MK_COMB (@lem1184232) (@lem1184231 _27539 _27540 _21160 f _21162)). Qed.
Lemma lem1184235 (a : Prop) (b : Prop) : (term576 a b) = (term577 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1184236 {_27538 _27541 : Type'} (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term589 _27538 _27541 m _21161 g _21163) = (term590 _27538 _27541 m _21161 g _21163).
Proof. exact (@lem1184235 (term526 _27541 _21163 m) (term527 _27538 _27541 _21161 g _21163)). Qed.
Lemma lem1184238 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184239 {_27541 : Type'} (_21163 : _27541) (m : list _27541) : (term581 _27541 _21163 m) = (@List.In _27541 _21163 m).
Proof. exact (@lem1184238 (@List.In _27541 _21163 m)). Qed.
Lemma lem1184240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184241 {_27541 : Type'} (_21163 : _27541) (m : list _27541) : (term582 _27541 _21163 m) = (term583 _27541 _21163 m).
Proof. exact (MK_COMB (@lem1184240) (@lem1184239 _27541 _21163 m)). Qed.
Lemma lem1184243 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184244 {_27538 _27541 : Type'} (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term586 _27538 _27541 _21161 g _21163) = (_21161 = (g _21163)).
Proof. exact (@lem1184243 (_21161 = (g _21163))). Qed.
Lemma lem1184245 {_27538 _27541 : Type'} (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term590 _27538 _27541 m _21161 g _21163) = (term107 _27538 _27541 m _21161 g _21163).
Proof. exact (MK_COMB (@lem1184241 _27541 _21163 m) (@lem1184244 _27538 _27541 _21161 g _21163)). Qed.
Lemma lem1184246 {_27538 _27541 : Type'} (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term589 _27538 _27541 m _21161 g _21163) = (term107 _27538 _27541 m _21161 g _21163).
Proof. exact (TRANS (@lem1184236 _27538 _27541 m _21161 g _21163) (@lem1184245 _27538 _27541 m _21161 g _21163)). Qed.
Lemma lem1184247 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term585 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163) = (term591 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163).
Proof. exact (MK_COMB (@lem1184233 _27539 _27540 _21160 f _21162) (@lem1184246 _27538 _27541 m _21161 g _21163)). Qed.
Lemma lem1184248 {_27538 _27539 _27540 _27541 : Type'} (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term584 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163) = (term591 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163).
Proof. exact (TRANS (@lem1184228 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163) (@lem1184247 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184249 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term579 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term592 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163).
Proof. exact (MK_COMB (@lem1184225 _27540 _21162 l) (@lem1184248 _27538 _27539 _27540 _27541 _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184250 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term578 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term592 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163).
Proof. exact (TRANS (@lem1184220 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) (@lem1184249 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1184252 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (_21160 : _27539) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (_21161 : _27538) (g : _27541 -> _27538) (_21163 : _27541) : (term593 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) = (term594 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163).
Proof. exact (MK_COMB (@lem1184251) (@lem1184250 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163)). Qed.
Lemma lem1184253 {_27538 _27539 : Type'} (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (P _21160 _21161) = (P _21160 _21161).
Proof. exact (eq_refl (P _21160 _21161)). Qed.
Lemma lem1184254 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term575 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) = (term595 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (MK_COMB (@lem1184252 _27538 _27539 _27540 _27541 l _21160 f _21162 m _21161 g _21163) (@lem1184253 _27538 _27539 P _21160 _21161)). Qed.
Lemma lem1184255 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (f : _27540 -> _27539) (_21162 : _27540) (m : list _27541) (g : _27541 -> _27538) (_21163 : _27541) (P : type1470 _27538 _27539) (_21160 : _27539) (_21161 : _27538) : (term573 _27538 _27539 _27540 _27541 P l _21160 f _21162 m _21161 g _21163) = (term595 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161).
Proof. exact (TRANS (@lem1184217 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1184254 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161)). Qed.
Lemma lem1184257 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term596 _27538 _27541 m g y.
Proof. exact (conj (@lem1183869 _27538 _27539 _27540 _27541 l m P f x g y h1) (@lem1183878 _27538 _27541 g y)). Qed.
Lemma lem1184258 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term597 _27538 _27539 _27540 _27541 f x m g y.
Proof. exact (conj (@lem1183862 _27539 _27540 f x) (@lem1184257 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184259 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term598 _27538 _27539 _27540 _27541 l f x m g y.
Proof. exact (conj (@lem1183853 _27538 _27539 _27540 _27541 l m P f x g y h1) (@lem1184258 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184261 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21163 : _27541) (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term595 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161.
Proof. exact (EQ_MP (@lem1184255 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161) (@lem1184214 _27538 _27539 _27540 _27541 _21160 _21162 _21161 _21163 l m P f x g y h1)). Qed.
Lemma lem1184262 {_27538 _27539 _27540 _27541 : Type'} (_21162 : _27540) (_21163 : _27541) (_21160 : _27539) (_21161 : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term595 _27538 _27539 _27540 _27541 l f _21162 m g _21163 P _21160 _21161.
Proof. exact (@lem1184261 _27538 _27539 _27540 _27541 _21162 _21163 _21160 _21161 l m P f x g y h1). Qed.
Lemma lem1184263 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term599 _27538 _27539 _27540 _27541 l m P f x g y.
Proof. exact (@lem1184262 _27538 _27539 _27540 _27541 x y (f x) (g y) l m P f x g y h1). Qed.
Lemma lem1184266 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term65 _27538 _27539 _27540 _27541 P f x g y.
Proof. exact (@lem1184263 _27538 _27539 _27540 _27541 l m P f x g y h1 (@lem1184259 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184267 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term600 _27538 _27539 _27540 _27541 P f x g y.
Proof. exact (fun h0 : term530 _27538 _27539 _27540 _27541 P f x g y => @lem1184266 _27538 _27539 _27540 _27541 l m P f x g y h1). Qed.
Lemma lem1184269 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184270 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term600 _27538 _27539 _27540 _27541 P f x g y) = (term65 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (@lem1184269 (term65 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1184271 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term65 _27538 _27539 _27540 _27541 P f x g y.
Proof. exact (EQ_MP (@lem1184270 _27538 _27539 _27540 _27541 P f x g y) (@lem1184267 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184274 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1184276 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) : (term530 _27538 _27539 _27540 _27541 P f x g y) = (term601 _27538 _27539 _27540 _27541 P f x g y).
Proof. exact (@lem1184274 (term65 _27538 _27539 _27540 _27541 P f x g y)). Qed.
Lemma lem1184279 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term601 _27538 _27539 _27540 _27541 P f x g y.
Proof. exact (EQ_MP (@lem1184276 _27538 _27539 _27540 _27541 P f x g y) (@lem1183583 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184282 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : False.
Proof. exact (@lem1184279 _27538 _27539 _27540 _27541 l m P f x g y h1 (@lem1184271 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184283 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : term602.
Proof. exact (fun h0 : ~ False => @lem1184282 _27538 _27539 _27540 _27541 l m P f x g y h1). Qed.
Lemma lem1184285 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184286 : term602 = False.
Proof. exact (@lem1184285 False). Qed.
Lemma lem1184287 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x : _27540) (g : _27541 -> _27538) (y : _27541) (h1 : term216 _27538 _27539 _27540 _27541 l m P f x g y) : False.
Proof. exact (EQ_MP (@lem1184286) (@lem1184283 _27538 _27539 _27540 _27541 l m P f x g y h1)). Qed.
Lemma lem1184289 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : @List.In _27540 x'' l.
Proof. exact (proj1 (@lem1183331 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184290 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term543 _27540 x'' l.
Proof. exact (fun h0 : term526 _27540 x'' l => @lem1184289 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184292 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184293 {_27540 : Type'} (x'' : _27540) (l : list _27540) : (term543 _27540 x'' l) = (@List.In _27540 x'' l).
Proof. exact (@lem1184292 (@List.In _27540 x'' l)). Qed.
Lemma lem1184294 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : @List.In _27540 x'' l.
Proof. exact (EQ_MP (@lem1184293 _27540 x'' l) (@lem1184290 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184296 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : @List.In _27541 x''' m.
Proof. exact (proj1 (@lem1183330 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184297 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term543 _27541 x''' m.
Proof. exact (fun h0 : term526 _27541 x''' m => @lem1184296 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184299 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184300 {_27541 : Type'} (x''' : _27541) (m : list _27541) : (term543 _27541 x''' m) = (@List.In _27541 x''' m).
Proof. exact (@lem1184299 (@List.In _27541 x''' m)). Qed.
Lemma lem1184301 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : @List.In _27541 x''' m.
Proof. exact (EQ_MP (@lem1184300 _27541 x''' m) (@lem1184297 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184317 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1184318 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) (m : list _27541) : (term603 _27538 _27539 _27540 _27541 m P f _21164 g _21165) = (term604 _27538 _27539 _27540 _27541 P f _21164 g _21165 m).
Proof. exact (@lem1184317 (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165) (term526 _27541 _21165 m)). Qed.
Lemma lem1184324 {_27540 : Type'} (_21164 : _27540) (l : list _27540) : (term554 _27540 _21164 l) = (term554 _27540 _21164 l).
Proof. exact (eq_refl (term554 _27540 _21164 l)). Qed.
Lemma lem1184325 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) (m : list _27541) : (term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term605 _27538 _27539 _27540 _27541 l P f _21164 g _21165 m).
Proof. exact (MK_COMB (@lem1184324 _27540 _21164 l) (@lem1184318 _27538 _27539 _27540 _27541 P f _21164 g _21165 m)). Qed.
Lemma lem1184329 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1184330 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term605 _27538 _27539 _27540 _27541 l P f _21164 g _21165 m) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m).
Proof. exact (@lem1184329 (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165) (term526 _27540 _21164 l) (term526 _27541 _21165 m)). Qed.
Lemma lem1184346 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m).
Proof. exact (TRANS (@lem1184325 _27538 _27539 _27540 _27541 l P f _21164 g _21165 m) (@lem1184330 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1184348 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term607 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term608 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m).
Proof. exact (MK_COMB (@lem1184347) (@lem1184346 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184364 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m).
Proof. exact (eq_refl (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184365 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : ((term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)) = ((term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)).
Proof. exact (MK_COMB (@lem1184348 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) (@lem1184364 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184367 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1184368 (x : Prop) : (x = x) = True.
Proof. exact (@lem1184367 Prop x). Qed.
Lemma lem1184369 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : ((term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)) = True.
Proof. exact (@lem1184368 (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184370 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : ((term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)) = True.
Proof. exact (TRANS (@lem1184365 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) (@lem1184369 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184371 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : True = ((term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)).
Proof. exact (SYM (@lem1184370 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m)). Qed.
Lemma lem1184372 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term531 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m).
Proof. exact (EQ_MP (@lem1184371 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) (@lem0)). Qed.
Lemma lem1184373 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m.
Proof. exact (EQ_MP (@lem1184372 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) (@lem1183720 _27538 _27539 _27540 _27541 _21164 _21165 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184375 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1184376 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) = (term609 _27538 _27539 _27540 _27541 l m P f _21164 g _21165).
Proof. exact (@lem1184375 (term156 _27540 _27541 _21164 l _21165 m) (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165)). Qed.
Lemma lem1184378 (a : Prop) (b : Prop) : (term576 a b) = (term577 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1184379 {_27540 _27541 : Type'} (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term610 _27540 _27541 _21164 l _21165 m) = (term611 _27540 _27541 _21164 l _21165 m).
Proof. exact (@lem1184378 (term526 _27540 _21164 l) (term526 _27541 _21165 m)). Qed.
Lemma lem1184381 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184382 {_27540 : Type'} (_21164 : _27540) (l : list _27540) : (term581 _27540 _21164 l) = (@List.In _27540 _21164 l).
Proof. exact (@lem1184381 (@List.In _27540 _21164 l)). Qed.
Lemma lem1184383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1184384 {_27540 : Type'} (_21164 : _27540) (l : list _27540) : (term582 _27540 _21164 l) = (term583 _27540 _21164 l).
Proof. exact (MK_COMB (@lem1184383) (@lem1184382 _27540 _21164 l)). Qed.
Lemma lem1184386 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1184387 {_27541 : Type'} (_21165 : _27541) (m : list _27541) : (term581 _27541 _21165 m) = (@List.In _27541 _21165 m).
Proof. exact (@lem1184386 (@List.In _27541 _21165 m)). Qed.
Lemma lem1184388 {_27540 _27541 : Type'} (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term611 _27540 _27541 _21164 l _21165 m) = (term159 _27540 _27541 _21164 l _21165 m).
Proof. exact (MK_COMB (@lem1184384 _27540 _21164 l) (@lem1184387 _27541 _21165 m)). Qed.
Lemma lem1184389 {_27540 _27541 : Type'} (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term610 _27540 _27541 _21164 l _21165 m) = (term159 _27540 _27541 _21164 l _21165 m).
Proof. exact (TRANS (@lem1184379 _27540 _27541 _21164 l _21165 m) (@lem1184388 _27540 _27541 _21164 l _21165 m)). Qed.
Lemma lem1184390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1184391 {_27540 _27541 : Type'} (_21164 : _27540) (l : list _27540) (_21165 : _27541) (m : list _27541) : (term612 _27540 _27541 _21164 l _21165 m) = (term69 _27540 _27541 _21164 l _21165 m).
Proof. exact (MK_COMB (@lem1184390) (@lem1184389 _27540 _27541 _21164 l _21165 m)). Qed.
Lemma lem1184392 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165) = (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165).
Proof. exact (eq_refl (term65 _27538 _27539 _27540 _27541 P f _21164 g _21165)). Qed.
Lemma lem1184393 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term609 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) = (term71 _27538 _27539 _27540 _27541 l m P f _21164 g _21165).
Proof. exact (MK_COMB (@lem1184391 _27540 _27541 _21164 l _21165 m) (@lem1184392 _27538 _27539 _27540 _27541 P f _21164 g _21165)). Qed.
Lemma lem1184394 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (_21164 : _27540) (g : _27541 -> _27538) (_21165 : _27541) : (term606 _27538 _27539 _27540 _27541 P f g _21164 l _21165 m) = (term71 _27538 _27539 _27540 _27541 l m P f _21164 g _21165).
Proof. exact (TRANS (@lem1184376 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) (@lem1184393 _27538 _27539 _27540 _27541 l m P f _21164 g _21165)). Qed.
Lemma lem1184396 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term159 _27540 _27541 x'' l x''' m.
Proof. exact (conj (@lem1184294 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1) (@lem1184301 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184398 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term71 _27538 _27539 _27540 _27541 l m P f _21164 g _21165.
Proof. exact (EQ_MP (@lem1184394 _27538 _27539 _27540 _27541 l m P f _21164 g _21165) (@lem1184373 _27538 _27539 _27540 _27541 _21164 _21165 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184399 {_27538 _27539 _27540 _27541 : Type'} (_21164 : _27540) (_21165 : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term71 _27538 _27539 _27540 _27541 l m P f _21164 g _21165.
Proof. exact (@lem1184398 _27538 _27539 _27540 _27541 _21164 _21165 x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184400 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term71 _27538 _27539 _27540 _27541 l m P f x'' g x'''.
Proof. exact (@lem1184399 _27538 _27539 _27540 _27541 x'' x''' x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184403 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term65 _27538 _27539 _27540 _27541 P f x'' g x'''.
Proof. exact (@lem1184400 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1 (@lem1184396 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184404 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term600 _27538 _27539 _27540 _27541 P f x'' g x'''.
Proof. exact (fun h0 : term530 _27538 _27539 _27540 _27541 P f x'' g x''' => @lem1184403 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184406 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184407 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : (term600 _27538 _27539 _27540 _27541 P f x'' g x''') = (term65 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (@lem1184406 (term65 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1184408 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term65 _27538 _27539 _27540 _27541 P f x'' g x'''.
Proof. exact (EQ_MP (@lem1184407 _27538 _27539 _27540 _27541 P f x'' g x''') (@lem1184404 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184411 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1184413 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (x'' : _27540) (g : _27541 -> _27538) (x''' : _27541) : (term530 _27538 _27539 _27540 _27541 P f x'' g x''') = (term601 _27538 _27539 _27540 _27541 P f x'' g x''').
Proof. exact (@lem1184411 (term65 _27538 _27539 _27540 _27541 P f x'' g x''')). Qed.
Lemma lem1184416 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term601 _27538 _27539 _27540 _27541 P f x'' g x'''.
Proof. exact (EQ_MP (@lem1184413 _27538 _27539 _27540 _27541 P f x'' g x''') (@lem1183733 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184419 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : False.
Proof. exact (@lem1184416 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1 (@lem1184408 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184420 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : term602.
Proof. exact (fun h0 : ~ False => @lem1184419 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1). Qed.
Lemma lem1184422 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1184423 : term602 = False.
Proof. exact (@lem1184422 False). Qed.
Lemma lem1184426 {_27538 _27539 _27540 _27541 : Type'} (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g) : False.
Proof. exact (EQ_MP (@lem1184423) (@lem1184420 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184427 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) : False.
Proof. exact (or_elim (@lem1183317 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1) (fun h0 : term216 _27538 _27539 _27540 _27541 l m P f x g y => @lem1184287 _27538 _27539 _27540 _27541 l m P f x g y h0) (fun h0 : term346 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g => @lem1184426 _27538 _27539 _27540 _27541 x'' x''' x' y' l m P f g h0)). Qed.
Lemma lem1184428 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) : (term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) = False.
Proof. exact (prop_ext (fun h2 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g => @lem1184427 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1) (fun h2 : False => @lem1183317 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184429 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x''' : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term435 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g) : False.
Proof. exact (EQ_MP (@lem1184428 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1) (@lem1183317 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h1)). Qed.
Lemma lem1184430 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x'' : _27540) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term438 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g) : False.
Proof. exact (ex_elim (@lem1183140 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g h1) (fun x''' : _27541 => fun h0 : term437 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g x''' => @lem1184429 _27538 _27539 _27540 _27541 x y x'' x''' x' y' l m P f g h0)). Qed.
Lemma lem1184431 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (y' : _27538) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term440 _27538 _27539 _27540 _27541 x y x' y' l m P f g) : False.
Proof. exact (ex_elim (@lem1183139 _27538 _27539 _27540 _27541 x y x' y' l m P f g h1) (fun x'' : _27540 => fun h0 : term439 _27538 _27539 _27540 _27541 x y x' y' l m P f g x'' => @lem1184430 _27538 _27539 _27540 _27541 x y x'' x' y' l m P f g h0)). Qed.
Lemma lem1184432 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (x' : _27539) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term442 _27538 _27539 _27540 _27541 x y x' l m P f g) : False.
Proof. exact (ex_elim (@lem1183138 _27538 _27539 _27540 _27541 x y x' l m P f g h1) (fun y' : _27538 => fun h0 : term441 _27538 _27539 _27540 _27541 x y x' l m P f g y' => @lem1184431 _27538 _27539 _27540 _27541 x y x' y' l m P f g h0)). Qed.
Lemma lem1184433 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (y : _27541) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term444 _27538 _27539 _27540 _27541 x y l m P f g) : False.
Proof. exact (ex_elim (@lem1183137 _27538 _27539 _27540 _27541 x y l m P f g h1) (fun x' : _27539 => fun h0 : term443 _27538 _27539 _27540 _27541 x y l m P f g x' => @lem1184432 _27538 _27539 _27540 _27541 x y x' l m P f g h0)). Qed.
Lemma lem1184434 {_27538 _27539 _27540 _27541 : Type'} (x : _27540) (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term446 _27538 _27539 _27540 _27541 x l m P f g) : False.
Proof. exact (ex_elim (@lem1183136 _27538 _27539 _27540 _27541 x l m P f g h1) (fun y : _27541 => fun h0 : term445 _27538 _27539 _27540 _27541 x l m P f g y => @lem1184433 _27538 _27539 _27540 _27541 x y l m P f g h0)). Qed.
Lemma lem1184435 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term110 _27538 _27539 _27540 _27541 l m P f g) : False.
Proof. exact (ex_elim (@lem1183135 _27538 _27539 _27540 _27541 l m P f g h1) (fun x : _27540 => fun h0 : term447 _27538 _27539 _27540 _27541 l m P f g x => @lem1184434 _27538 _27539 _27540 _27541 x l m P f g h0)). Qed.
Lemma lem1184436 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term110 _27538 _27539 _27540 _27541 l m P f g) : (term110 _27538 _27539 _27540 _27541 l m P f g) = False.
Proof. exact (prop_ext (fun h2 : term110 _27538 _27539 _27540 _27541 l m P f g => @lem1184435 _27538 _27539 _27540 _27541 l m P f g h1) (fun h2 : False => @lem1182150 _27538 _27539 _27540 _27541 l m P f g h1)). Qed.
Lemma lem1184437 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term110 _27538 _27539 _27540 _27541 l m P f g) : False.
Proof. exact (EQ_MP (@lem1184436 _27538 _27539 _27540 _27541 l m P f g h1) (@lem1182150 _27538 _27539 _27540 _27541 l m P f g h1)). Qed.
Lemma lem1184438 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : term109 _27538 _27539 _27540 _27541 l m P f g.
Proof. exact (fun h0 : term110 _27538 _27539 _27540 _27541 l m P f g => @lem1184437 _27538 _27539 _27540 _27541 l m P f g h0). Qed.
Lemma lem1184439 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (m : list _27541) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : (term46 _27538 _27539 _27540 _27541 l f m g P) = (term78 _27538 _27539 _27540 _27541 l m P f g).
Proof. exact (EQ_MP (@lem1182149 _27538 _27539 _27540 _27541 l m P f g) (@lem1184438 _27538 _27539 _27540 _27541 l m P f g)). Qed.
Lemma lem1184444 {_27538 _27539 _27540 _27541 : Type'} (l : list _27540) (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : term82 _27538 _27539 _27540 _27541 l P f g.
Proof. exact (fun m : list _27541 => @lem1184439 _27538 _27539 _27540 _27541 l m P f g). Qed.
Lemma lem1184449 {_27538 _27539 _27540 _27541 : Type'} (P : type1470 _27538 _27539) (f : _27540 -> _27539) (g : _27541 -> _27538) : term86 _27538 _27539 _27540 _27541 P f g.
Proof. exact (fun l : list _27540 => @lem1184444 _27538 _27539 _27540 _27541 l P f g). Qed.
Lemma lem1184454 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term90 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun P : type1470 _27538 _27539 => @lem1184449 _27538 _27539 _27540 _27541 P f g). Qed.
Lemma lem1184459 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : term102 _27538 _27539 _27540 _27541 g.
Proof. exact (fun f : _27540 -> _27539 => @lem1184454 _27538 _27539 _27540 _27541 f g). Qed.
Lemma lem1184464 {_27538 _27539 _27540 _27541 : Type'} : term106 _27538 _27539 _27540 _27541.
Proof. exact (fun g : _27541 -> _27538 => @lem1184459 _27538 _27539 _27540 _27541 g). Qed.
Lemma lem1184465 {_27538 _27539 _27540 _27541 : Type'} : term105 _27538 _27539 _27540 _27541.
Proof. exact (EQ_MP (@lem1182145 _27538 _27539 _27540 _27541) (@lem1184464 _27538 _27539 _27540 _27541)). Qed.
Lemma lem1184466 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : term613 _27538 _27539 _27540 _27541 g.
Proof. exact (@lem1184465 _27538 _27539 _27540 _27541 g). Qed.
Lemma lem1184467 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : (term613 _27538 _27539 _27540 _27541 g) = (term101 _27538 _27539 _27540 _27541 g).
Proof. exact (eq_refl (term613 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1184468 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) : term101 _27538 _27539 _27540 _27541 g.
Proof. exact (EQ_MP (@lem1184467 _27538 _27539 _27540 _27541 g) (@lem1184466 _27538 _27539 _27540 _27541 g)). Qed.
Lemma lem1184469 {_27538 _27539 _27540 _27541 : Type'} (g : _27541 -> _27538) (f : _27540 -> _27539) : term614 _27538 _27539 _27540 _27541 g f.
Proof. exact (@lem1184468 _27538 _27539 _27540 _27541 g f). Qed.
Lemma lem1184470 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : (term614 _27538 _27539 _27540 _27541 g f) = (term92 _27538 _27539 _27540 _27541 f g).
Proof. exact (eq_refl (term614 _27538 _27539 _27540 _27541 g f)). Qed.
Lemma lem1184471 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (EQ_MP (@lem1184470 _27538 _27539 _27540 _27541 f g) (@lem1184469 _27538 _27539 _27540 _27541 g f)). Qed.
Lemma lem1184473 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (@lem1181832 _27538 _27539 _27540 _27541 f g (@lem1184471 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1184474 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term93 _27538 _27539 _27540 _27541 f g) : False.
Proof. exact (@lem1184473 _27538 _27539 _27540 _27541 f g (@lem1181816 _27538 _27539 _27540 _27541 f g h1)). Qed.
Lemma lem1184475 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term93 _27538 _27539 _27540 _27541 f g) : (term93 _27538 _27539 _27540 _27541 f g) = False.
Proof. exact (prop_ext (fun h2 : term93 _27538 _27539 _27540 _27541 f g => @lem1184474 _27538 _27539 _27540 _27541 f g h1) (fun h2 : False => @lem1181816 _27538 _27539 _27540 _27541 f g h1)). Qed.
Lemma lem1184476 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) (h1 : term93 _27538 _27539 _27540 _27541 f g) : False.
Proof. exact (EQ_MP (@lem1184475 _27538 _27539 _27540 _27541 f g h1) (@lem1181816 _27538 _27539 _27540 _27541 f g h1)). Qed.
Lemma lem1184477 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term92 _27538 _27539 _27540 _27541 f g.
Proof. exact (fun h0 : term93 _27538 _27539 _27540 _27541 f g => @lem1184476 _27538 _27539 _27540 _27541 f g h0). Qed.
Lemma lem1184478 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term90 _27538 _27539 _27540 _27541 f g.
Proof. exact (EQ_MP (@lem1181815 _27538 _27539 _27540 _27541 f g) (@lem1184477 _27538 _27539 _27540 _27541 f g)). Qed.
Lemma lem1184479 {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538) : term89 _27538 _27539 _27540 _27541 f g.
Proof. exact (EQ_MP (@lem1181811 _27538 _27539 _27540 _27541 f g) (@lem1184478 _27538 _27539 _27540 _27541 f g)). Qed.
