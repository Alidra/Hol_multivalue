Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNION_LZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUM_UNION_RZERO_spec.
Require Import UNION_COMM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem7129617 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7129618 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7129619 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7129618 t1) (@lem7129617 t1)). Qed.
Lemma lem7129620 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7129619 t1 t2). Qed.
Lemma lem7129621 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7129622 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7129621 t1 t2) (@lem7129620 t1 t2)). Qed.
Lemma lem7129623 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7129622 t1 t2 t3). Qed.
Lemma lem7129624 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7129625 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7129624 t1 t2 t3) (@lem7129623 t1 t2 t3)). Qed.
Lemma lem7129626 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7129625 t1 t2 t3)). Qed.
Lemma lem7129628 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7129629 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem7129628 (term8 A)). Qed.
Lemma lem7129630 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem7129629 A)). Qed.
Lemma lem7129631 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7129632 {A : Type'} : term11 A.
Proof. exact (@lem7129616 A). Qed.
Lemma lem7129636 {A : Type'} : term12 A.
Proof. exact (@lem3233393 A). Qed.
Lemma lem7129639 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem7129640 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem7129639 A h0). Qed.
Lemma lem7129641 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem7129642 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem7129643 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem7129641 A h2 (@lem7129642 A h1)). Qed.
Lemma lem7129644 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem7129643 A h1 h0). Qed.
Lemma lem7129645 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem7129646 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem7129644 A h1 (@lem7129645 A h2)). Qed.
Lemma lem7129647 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem7129646 A h0 h1). Qed.
Lemma lem7129648 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem7129647 A h0). Qed.
Lemma lem7129651 {A : Type'} : term14 A.
Proof. exact (@lem7129648 A (@lem7129640 A)). Qed.
Lemma lem7129652 {A : Type'} : term14 A.
Proof. exact (@lem7129651 A). Qed.
Lemma lem7129690 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7129691 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem7129690 (term11 A)). Qed.
Lemma lem7129716 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7129717 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7129716 A) (@lem7129691 A)). Qed.
Lemma lem7129720 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7129727 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (MK_COMB (@lem7129720 A) (@lem7129717 A)). Qed.
Lemma lem7129728 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term24 A u v f) = (@sum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7129739 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term25 A v u f x) = (term25 A v u f x).
Proof. exact (eq_refl (term25 A v u f x)). Qed.
Lemma lem7129740 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term26 A v u f) = (term26 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7129739 A v u f x)). Qed.
Lemma lem7129741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7129742 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term27 A v u f) = (term27 A v u f).
Proof. exact (MK_COMB (@lem7129741 A) (@lem7129740 A v u f)). Qed.
Lemma lem7129745 {A : Type'} (u : A -> Prop) : (term28 A u) = (term28 A u).
Proof. exact (eq_refl (term28 A u)). Qed.
Lemma lem7129746 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term29 A v u f) = (term29 A v u f).
Proof. exact (MK_COMB (@lem7129745 A u) (@lem7129742 A v u f)). Qed.
Lemma lem7129747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129748 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term30 A v u f) = (term30 A v u f).
Proof. exact (MK_COMB (@lem7129747) (@lem7129746 A v u f)). Qed.
Lemma lem7129749 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term31 A v u f) = (term31 A v u f).
Proof. exact (MK_COMB (@lem7129748 A v u f) (@lem7129728 A v u f)). Qed.
Lemma lem7129750 {A : Type'} (u : A -> Prop) (f : A -> real) : (term32 A u f) = (term32 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7129749 A v u f)). Qed.
Lemma lem7129751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129752 {A : Type'} (u : A -> Prop) (f : A -> real) : (term33 A u f) = (term33 A u f).
Proof. exact (MK_COMB (@lem7129751 A) (@lem7129750 A u f)). Qed.
Lemma lem7129753 {A : Type'} (f : A -> real) : (term34 A f) = (term34 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7129752 A u f)). Qed.
Lemma lem7129754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129755 {A : Type'} (f : A -> real) : (term35 A f) = (term35 A f).
Proof. exact (MK_COMB (@lem7129754 A) (@lem7129753 A f)). Qed.
Lemma lem7129756 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7129755 A f)). Qed.
Lemma lem7129757 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7129758 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7129757 A) (@lem7129756 A)). Qed.
Lemma lem7129759 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7129760 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7129759) (@lem7129758 A)). Qed.
Lemma lem7129761 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((@UNION A s t) = (@UNION A t s)).
Proof. exact (eq_refl ((@UNION A s t) = (@UNION A t s))). Qed.
Lemma lem7129762 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7129761 A t s)). Qed.
Lemma lem7129763 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129764 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem7129763 A) (@lem7129762 A s)). Qed.
Lemma lem7129765 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7129764 A s)). Qed.
Lemma lem7129766 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129767 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7129766 A) (@lem7129765 A)). Qed.
Lemma lem7129768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129769 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7129768) (@lem7129767 A)). Qed.
Lemma lem7129770 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem7129769 A) (@lem7129760 A)). Qed.
Lemma lem7129771 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A v f)) = ((term24 A u v f) = (@sum A v f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A v f))). Qed.
Lemma lem7129782 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term25 A u v f x) = (term25 A u v f x).
Proof. exact (eq_refl (term25 A u v f x)). Qed.
Lemma lem7129783 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term26 A u v f) = (term26 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7129782 A u v f x)). Qed.
Lemma lem7129784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7129785 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term27 A u v f) = (term27 A u v f).
Proof. exact (MK_COMB (@lem7129784 A) (@lem7129783 A u v f)). Qed.
Lemma lem7129788 {A : Type'} (v : A -> Prop) : (term28 A v) = (term28 A v).
Proof. exact (eq_refl (term28 A v)). Qed.
Lemma lem7129789 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term29 A u v f) = (term29 A u v f).
Proof. exact (MK_COMB (@lem7129788 A v) (@lem7129785 A u v f)). Qed.
Lemma lem7129790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129791 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term30 A u v f) = (term30 A u v f).
Proof. exact (MK_COMB (@lem7129790) (@lem7129789 A u v f)). Qed.
Lemma lem7129792 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term40 A u v f) = (term40 A u v f).
Proof. exact (MK_COMB (@lem7129791 A u v f) (@lem7129771 A u v f)). Qed.
Lemma lem7129793 {A : Type'} (u : A -> Prop) (f : A -> real) : (term41 A u f) = (term41 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7129792 A u v f)). Qed.
Lemma lem7129794 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129795 {A : Type'} (u : A -> Prop) (f : A -> real) : (term42 A u f) = (term42 A u f).
Proof. exact (MK_COMB (@lem7129794 A) (@lem7129793 A u f)). Qed.
Lemma lem7129796 {A : Type'} (f : A -> real) : (term43 A f) = (term43 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7129795 A u f)). Qed.
Lemma lem7129797 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7129798 {A : Type'} (f : A -> real) : (term44 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem7129797 A) (@lem7129796 A f)). Qed.
Lemma lem7129799 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7129798 A f)). Qed.
Lemma lem7129800 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7129801 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem7129800 A) (@lem7129799 A)). Qed.
Lemma lem7129802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7129803 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7129802) (@lem7129801 A)). Qed.
Lemma lem7129804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7129805 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem7129804) (@lem7129803 A)). Qed.
Lemma lem7129806 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem7129805 A) (@lem7129770 A)). Qed.
Lemma lem7129889 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (TRANS (@lem7129727 A) (@lem7129806 A)). Qed.
Lemma lem7129890 {A : Type'} : (term23 A) = (term13 A).
Proof. exact (SYM (@lem7129889 A)). Qed.
Lemma lem7129891 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7129892 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7129893 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7129898 {A : Type'} (x : A) (v : A -> Prop) : (term46 A x v) = (@IN A x v).
Proof. exact (@lem16933 (@IN A x v)). Qed.
Lemma lem7129900 {A : Type'} (x : A) (u : A -> Prop) : (term47 A x u) = (term47 A x u).
Proof. exact (eq_refl (term47 A x u)). Qed.
Lemma lem7129901 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term48 A u x v) = (term49 A u x v).
Proof. exact (MK_COMB (@lem7129900 A x u) (@lem7129898 A x v)). Qed.
Lemma lem7129902 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term50 A u x v) = (term48 A u x v).
Proof. exact (@lem17045 (@IN A x u) (term51 A x v)). Qed.
Lemma lem7129903 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term50 A u x v) = (term49 A u x v).
Proof. exact (TRANS (@lem7129902 A u x v) (@lem7129901 A u x v)). Qed.
Lemma lem7129904 {A : Type'} (f : A -> real) (x : A) : ((f x) = term52) = ((f x) = term52).
Proof. exact (eq_refl ((f x) = term52)). Qed.
Lemma lem7129905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7129906 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term53 A u x v) = (term54 A u x v).
Proof. exact (MK_COMB (@lem7129905) (@lem7129903 A u x v)). Qed.
Lemma lem7129907 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term55 A u v f x) = (term56 A u v f x).
Proof. exact (MK_COMB (@lem7129906 A u x v) (@lem7129904 A f x)). Qed.
Lemma lem7129908 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term25 A u v f x) = (term55 A u v f x).
Proof. exact (@lem17265 (term57 A u x v) ((f x) = term52)). Qed.
Lemma lem7129909 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term25 A u v f x) = (term56 A u v f x).
Proof. exact (TRANS (@lem7129908 A u v f x) (@lem7129907 A u v f x)). Qed.
Lemma lem7129910 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term26 A u v f) = (term58 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7129909 A u v f x)). Qed.
Lemma lem7129911 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7129912 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term27 A u v f) = (term59 A u v f).
Proof. exact (MK_COMB (@lem7129911 A) (@lem7129910 A u v f)). Qed.
Lemma lem7129914 {A : Type'} (v : A -> Prop) : (term28 A v) = (term28 A v).
Proof. exact (eq_refl (term28 A v)). Qed.
Lemma lem7129915 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term29 A u v f) = (term60 A u v f).
Proof. exact (MK_COMB (@lem7129914 A v) (@lem7129912 A u v f)). Qed.
Lemma lem7129916 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term61 A u v f) = (term61 A u v f).
Proof. exact (eq_refl (term61 A u v f)). Qed.
Lemma lem7129917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7129918 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term62 A u v f) = (term63 A u v f).
Proof. exact (MK_COMB (@lem7129917) (@lem7129915 A u v f)). Qed.
Lemma lem7129919 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term64 A u v f) = (term65 A u v f).
Proof. exact (MK_COMB (@lem7129918 A u v f) (@lem7129916 A u v f)). Qed.
Lemma lem7129920 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term66 A u v f) = (term64 A u v f).
Proof. exact (@lem17362 (term29 A u v f) ((term24 A u v f) = (@sum A v f))). Qed.
Lemma lem7129921 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term66 A u v f) = (term65 A u v f).
Proof. exact (TRANS (@lem7129920 A u v f) (@lem7129919 A u v f)). Qed.
Lemma lem7129922 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7129923 {A : Type'} (u : A -> Prop) (f : A -> real) : (term69 A u f) = (term70 A u f).
Proof. exact (@lem7129922 A (term41 A u f)). Qed.
Lemma lem7129924 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term71 A u f v) = (term40 A u v f).
Proof. exact (eq_refl (term71 A u f v)). Qed.
Lemma lem7129925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7129926 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term72 A u f v) = (term66 A u v f).
Proof. exact (MK_COMB (@lem7129925) (@lem7129924 A u v f)). Qed.
Lemma lem7129927 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term72 A u f v) = (term65 A u v f).
Proof. exact (TRANS (@lem7129926 A u v f) (@lem7129921 A u v f)). Qed.
Lemma lem7129928 {A : Type'} (u : A -> Prop) (f : A -> real) : (term73 A u f) = (term74 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7129927 A u v f)). Qed.
Lemma lem7129929 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7129930 {A : Type'} (u : A -> Prop) (f : A -> real) : (term70 A u f) = (term75 A u f).
Proof. exact (MK_COMB (@lem7129929 A) (@lem7129928 A u f)). Qed.
Lemma lem7129931 {A : Type'} (u : A -> Prop) (f : A -> real) : (term69 A u f) = (term75 A u f).
Proof. exact (TRANS (@lem7129923 A u f) (@lem7129930 A u f)). Qed.
Lemma lem7129932 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7129933 {A : Type'} (f : A -> real) : (term76 A f) = (term77 A f).
Proof. exact (@lem7129932 A (term43 A f)). Qed.
Lemma lem7129934 {A : Type'} (u : A -> Prop) (f : A -> real) : (term78 A f u) = (term42 A u f).
Proof. exact (eq_refl (term78 A f u)). Qed.
Lemma lem7129935 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7129936 {A : Type'} (u : A -> Prop) (f : A -> real) : (term79 A f u) = (term69 A u f).
Proof. exact (MK_COMB (@lem7129935) (@lem7129934 A u f)). Qed.
Lemma lem7129937 {A : Type'} (u : A -> Prop) (f : A -> real) : (term79 A f u) = (term75 A u f).
Proof. exact (TRANS (@lem7129936 A u f) (@lem7129931 A u f)). Qed.
Lemma lem7129938 {A : Type'} (f : A -> real) : (term80 A f) = (term81 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7129937 A u f)). Qed.
Lemma lem7129939 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7129940 {A : Type'} (f : A -> real) : (term77 A f) = (term82 A f).
Proof. exact (MK_COMB (@lem7129939 A) (@lem7129938 A f)). Qed.
Lemma lem7129941 {A : Type'} (f : A -> real) : (term76 A f) = (term82 A f).
Proof. exact (TRANS (@lem7129933 A f) (@lem7129940 A f)). Qed.
Lemma lem7129942 {A : Type'} (P : type716 A) : (term83 A P) = (term84 A P).
Proof. exact (@lem18392 (A -> real) P). Qed.
Lemma lem7129943 {A : Type'} : (term10 A) = (term85 A).
Proof. exact (@lem7129942 A (term45 A)). Qed.
Lemma lem7129944 {A : Type'} (f : A -> real) : (term86 A f) = (term44 A f).
Proof. exact (eq_refl (term86 A f)). Qed.
Lemma lem7129945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7129946 {A : Type'} (f : A -> real) : (term87 A f) = (term76 A f).
Proof. exact (MK_COMB (@lem7129945) (@lem7129944 A f)). Qed.
Lemma lem7129947 {A : Type'} (f : A -> real) : (term87 A f) = (term82 A f).
Proof. exact (TRANS (@lem7129946 A f) (@lem7129941 A f)). Qed.
Lemma lem7129948 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7129947 A f)). Qed.
Lemma lem7129949 {A : Type'} : (@ex (A -> real)) = (@ex (A -> real)).
Proof. exact (eq_refl (@ex (A -> real))). Qed.
Lemma lem7129950 {A : Type'} : (term85 A) = (term90 A).
Proof. exact (MK_COMB (@lem7129949 A) (@lem7129948 A)). Qed.
Lemma lem7130059 {A : Type'} : (term10 A) = (term90 A).
Proof. exact (TRANS (@lem7129943 A) (@lem7129950 A)). Qed.
Lemma lem7130060 {A : Type'} (h1 : term10 A) : term90 A.
Proof. exact (EQ_MP (@lem7130059 A) (@lem7129891 A h1)). Qed.
Lemma lem7130061 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((@UNION A s t) = (@UNION A t s)).
Proof. exact (eq_refl ((@UNION A s t) = (@UNION A t s))). Qed.
Lemma lem7130062 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7130061 A t s)). Qed.
Lemma lem7130063 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130064 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem7130063 A) (@lem7130062 A s)). Qed.
Lemma lem7130065 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7130064 A s)). Qed.
Lemma lem7130066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130079 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7130066 A) (@lem7130065 A)). Qed.
Lemma lem7130080 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (EQ_MP (@lem7130079 A) (@lem7129892 A h1)). Qed.
Lemma lem7130092 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term91 A v u f x) = (term92 A v u f x).
Proof. exact (@lem17362 (term57 A v x u) ((f x) = term52)). Qed.
Lemma lem7130093 {A : Type'} (P : A -> Prop) : (term93 A P) = (term94 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7130094 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term95 A v u f) = (term96 A v u f).
Proof. exact (@lem7130093 A (term26 A v u f)). Qed.
Lemma lem7130095 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term97 A v u f x) = (term25 A v u f x).
Proof. exact (eq_refl (term97 A v u f x)). Qed.
Lemma lem7130096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130097 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term98 A v u f x) = (term91 A v u f x).
Proof. exact (MK_COMB (@lem7130096) (@lem7130095 A v u f x)). Qed.
Lemma lem7130098 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term98 A v u f x) = (term92 A v u f x).
Proof. exact (TRANS (@lem7130097 A v u f x) (@lem7130092 A v u f x)). Qed.
Lemma lem7130099 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term99 A v u f) = (term100 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130098 A v u f x)). Qed.
Lemma lem7130100 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130101 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term96 A v u f) = (term101 A v u f).
Proof. exact (MK_COMB (@lem7130100 A) (@lem7130099 A v u f)). Qed.
Lemma lem7130102 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term95 A v u f) = (term101 A v u f).
Proof. exact (TRANS (@lem7130094 A v u f) (@lem7130101 A v u f)). Qed.
Lemma lem7130104 {A : Type'} (u : A -> Prop) : (term102 A u) = (term102 A u).
Proof. exact (eq_refl (term102 A u)). Qed.
Lemma lem7130105 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term103 A v u f) = (term104 A v u f).
Proof. exact (MK_COMB (@lem7130104 A u) (@lem7130102 A v u f)). Qed.
Lemma lem7130106 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term105 A v u f) = (term103 A v u f).
Proof. exact (@lem17045 (@FINITE A u) (term27 A v u f)). Qed.
Lemma lem7130107 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term105 A v u f) = (term104 A v u f).
Proof. exact (TRANS (@lem7130106 A v u f) (@lem7130105 A v u f)). Qed.
Lemma lem7130108 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term24 A u v f) = (@sum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130110 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term106 A v u f) = (term107 A v u f).
Proof. exact (MK_COMB (@lem7130109) (@lem7130107 A v u f)). Qed.
Lemma lem7130111 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term108 A v u f) = (term109 A v u f).
Proof. exact (MK_COMB (@lem7130110 A v u f) (@lem7130108 A v u f)). Qed.
Lemma lem7130112 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term31 A v u f) = (term108 A v u f).
Proof. exact (@lem17265 (term29 A v u f) ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130113 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term31 A v u f) = (term109 A v u f).
Proof. exact (TRANS (@lem7130112 A v u f) (@lem7130111 A v u f)). Qed.
Lemma lem7130114 {A : Type'} (u : A -> Prop) (f : A -> real) : (term32 A u f) = (term110 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130113 A v u f)). Qed.
Lemma lem7130115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130116 {A : Type'} (u : A -> Prop) (f : A -> real) : (term33 A u f) = (term111 A u f).
Proof. exact (MK_COMB (@lem7130115 A) (@lem7130114 A u f)). Qed.
Lemma lem7130117 {A : Type'} (f : A -> real) : (term34 A f) = (term112 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130116 A u f)). Qed.
Lemma lem7130118 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130119 {A : Type'} (f : A -> real) : (term35 A f) = (term113 A f).
Proof. exact (MK_COMB (@lem7130118 A) (@lem7130117 A f)). Qed.
Lemma lem7130120 {A : Type'} : (term36 A) = (term114 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7130119 A f)). Qed.
Lemma lem7130121 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130122 {A : Type'} : (term11 A) = (term115 A).
Proof. exact (MK_COMB (@lem7130121 A) (@lem7130120 A)). Qed.
Lemma lem7130229 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7130230 {A : Type'} (P : Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem7130229 A P Q). Qed.
Lemma lem7130231 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term118 A v u f) = (term119 A v u f).
Proof. exact (@lem7130230 A (term120 A u) (term100 A v u f)). Qed.
Lemma lem7130232 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term121 A v u f x) = (term92 A v u f x).
Proof. exact (eq_refl (term121 A v u f x)). Qed.
Lemma lem7130233 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term122 A v u f) = (term100 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130232 A v u f x)). Qed.
Lemma lem7130234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130235 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term123 A v u f) = (term101 A v u f).
Proof. exact (MK_COMB (@lem7130234 A) (@lem7130233 A v u f)). Qed.
Lemma lem7130236 {A : Type'} (u : A -> Prop) : (term102 A u) = (term102 A u).
Proof. exact (eq_refl (term102 A u)). Qed.
Lemma lem7130237 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term118 A v u f) = (term104 A v u f).
Proof. exact (MK_COMB (@lem7130236 A u) (@lem7130235 A v u f)). Qed.
Lemma lem7130238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7130239 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term124 A v u f) = (term125 A v u f).
Proof. exact (MK_COMB (@lem7130238) (@lem7130237 A v u f)). Qed.
Lemma lem7130240 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term121 A v u f x) = (term92 A v u f x).
Proof. exact (eq_refl (term121 A v u f x)). Qed.
Lemma lem7130241 {A : Type'} (u : A -> Prop) : (term102 A u) = (term102 A u).
Proof. exact (eq_refl (term102 A u)). Qed.
Lemma lem7130242 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term126 A v u f x) = (term127 A v u f x).
Proof. exact (MK_COMB (@lem7130241 A u) (@lem7130240 A v u f x)). Qed.
Lemma lem7130243 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term128 A v u f) = (term129 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130242 A v u f x)). Qed.
Lemma lem7130244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130245 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term119 A v u f) = (term130 A v u f).
Proof. exact (MK_COMB (@lem7130244 A) (@lem7130243 A v u f)). Qed.
Lemma lem7130246 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term118 A v u f) = (term119 A v u f)) = ((term104 A v u f) = (term130 A v u f)).
Proof. exact (MK_COMB (@lem7130239 A v u f) (@lem7130245 A v u f)). Qed.
Lemma lem7130247 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term104 A v u f) = (term130 A v u f).
Proof. exact (EQ_MP (@lem7130246 A v u f) (@lem7130231 A v u f)). Qed.
Lemma lem7130248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130249 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term107 A v u f) = (term131 A v u f).
Proof. exact (MK_COMB (@lem7130248) (@lem7130247 A v u f)). Qed.
Lemma lem7130250 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term24 A u v f) = (@sum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130251 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term109 A v u f) = (term132 A v u f).
Proof. exact (MK_COMB (@lem7130249 A v u f) (@lem7130250 A v u f)). Qed.
Lemma lem7130253 {A : Type'} (P : A -> Prop) (Q : Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7130254 {A : Type'} (P : A -> Prop) (Q : Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (@lem7130253 A P Q). Qed.
Lemma lem7130255 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term135 A v u f) = (term136 A v u f).
Proof. exact (@lem7130254 A (term129 A v u f) ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130256 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term137 A v u f x) = (term127 A v u f x).
Proof. exact (eq_refl (term137 A v u f x)). Qed.
Lemma lem7130257 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term138 A v u f) = (term129 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130256 A v u f x)). Qed.
Lemma lem7130258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130259 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term139 A v u f) = (term130 A v u f).
Proof. exact (MK_COMB (@lem7130258 A) (@lem7130257 A v u f)). Qed.
Lemma lem7130260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130261 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term140 A v u f) = (term131 A v u f).
Proof. exact (MK_COMB (@lem7130260) (@lem7130259 A v u f)). Qed.
Lemma lem7130262 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term24 A u v f) = (@sum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130263 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term135 A v u f) = (term132 A v u f).
Proof. exact (MK_COMB (@lem7130261 A v u f) (@lem7130262 A v u f)). Qed.
Lemma lem7130264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7130265 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term141 A v u f) = (term142 A v u f).
Proof. exact (MK_COMB (@lem7130264) (@lem7130263 A v u f)). Qed.
Lemma lem7130266 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term137 A v u f x) = (term127 A v u f x).
Proof. exact (eq_refl (term137 A v u f x)). Qed.
Lemma lem7130267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130268 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term143 A v u f x) = (term144 A v u f x).
Proof. exact (MK_COMB (@lem7130267) (@lem7130266 A v u f x)). Qed.
Lemma lem7130269 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term24 A u v f) = (@sum A u f)).
Proof. exact (eq_refl ((term24 A u v f) = (@sum A u f))). Qed.
Lemma lem7130270 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term145 A x v u f) = (term146 A x v u f).
Proof. exact (MK_COMB (@lem7130268 A v u f x) (@lem7130269 A v u f)). Qed.
Lemma lem7130271 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term147 A v u f) = (term148 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130270 A x v u f)). Qed.
Lemma lem7130272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130273 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term136 A v u f) = (term149 A v u f).
Proof. exact (MK_COMB (@lem7130272 A) (@lem7130271 A v u f)). Qed.
Lemma lem7130274 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term135 A v u f) = (term136 A v u f)) = ((term132 A v u f) = (term149 A v u f)).
Proof. exact (MK_COMB (@lem7130265 A v u f) (@lem7130273 A v u f)). Qed.
Lemma lem7130275 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term132 A v u f) = (term149 A v u f).
Proof. exact (EQ_MP (@lem7130274 A v u f) (@lem7130255 A v u f)). Qed.
Lemma lem7130276 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term109 A v u f) = (term149 A v u f).
Proof. exact (TRANS (@lem7130251 A v u f) (@lem7130275 A v u f)). Qed.
Lemma lem7130277 {A : Type'} (u : A -> Prop) (f : A -> real) : (term110 A u f) = (term150 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130276 A v u f)). Qed.
Lemma lem7130278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130279 {A : Type'} (u : A -> Prop) (f : A -> real) : (term111 A u f) = (term151 A u f).
Proof. exact (MK_COMB (@lem7130278 A) (@lem7130277 A u f)). Qed.
Lemma lem7130281 {A B : Type'} (P : type1413 A B) : (term152 A B P) = (term153 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7130282 {A : Type'} (P : type672 A) : (term154 A P) = (term155 A P).
Proof. exact (@lem7130281 (A -> Prop) A P). Qed.
Lemma lem7130283 {A : Type'} (u : A -> Prop) (f : A -> real) : (term156 A u f) = (term157 A u f).
Proof. exact (@lem7130282 A (term158 A u f)). Qed.
Lemma lem7130284 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term159 A u f v) = (term148 A v u f).
Proof. exact (eq_refl (term159 A u f v)). Qed.
Lemma lem7130285 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7130286 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term160 A u f v x) = (term161 A v u f x).
Proof. exact (MK_COMB (@lem7130284 A v u f) (@lem7130285 A x)). Qed.
Lemma lem7130287 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term161 A v u f x) = (term146 A x v u f).
Proof. exact (eq_refl (term161 A v u f x)). Qed.
Lemma lem7130288 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term160 A u f v x) = (term146 A x v u f).
Proof. exact (TRANS (@lem7130286 A v u f x) (@lem7130287 A x v u f)). Qed.
Lemma lem7130289 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term162 A u f v) = (term148 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7130288 A x v u f)). Qed.
Lemma lem7130290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7130291 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term163 A u f v) = (term149 A v u f).
Proof. exact (MK_COMB (@lem7130290 A) (@lem7130289 A v u f)). Qed.
Lemma lem7130292 {A : Type'} (u : A -> Prop) (f : A -> real) : (term164 A u f) = (term150 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130291 A v u f)). Qed.
Lemma lem7130293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130294 {A : Type'} (u : A -> Prop) (f : A -> real) : (term156 A u f) = (term151 A u f).
Proof. exact (MK_COMB (@lem7130293 A) (@lem7130292 A u f)). Qed.
Lemma lem7130295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7130296 {A : Type'} (u : A -> Prop) (f : A -> real) : (term165 A u f) = (term166 A u f).
Proof. exact (MK_COMB (@lem7130295) (@lem7130294 A u f)). Qed.
Lemma lem7130297 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term159 A u f v) = (term148 A v u f).
Proof. exact (eq_refl (term159 A u f v)). Qed.
Lemma lem7130298 {A : Type'} (x : type684 A) (v : A -> Prop) : (x v) = (x v).
Proof. exact (eq_refl (x v)). Qed.
Lemma lem7130299 {A : Type'} (u : A -> Prop) (f : A -> real) (x : type684 A) (v : A -> Prop) : (term167 A u f x v) = (term168 A u f x v).
Proof. exact (MK_COMB (@lem7130297 A v u f) (@lem7130298 A x v)). Qed.
Lemma lem7130300 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term168 A u f x v) = (term169 A x v u f).
Proof. exact (eq_refl (term168 A u f x v)). Qed.
Lemma lem7130301 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term167 A u f x v) = (term169 A x v u f).
Proof. exact (TRANS (@lem7130299 A u f x v) (@lem7130300 A x v u f)). Qed.
Lemma lem7130302 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term170 A u f x) = (term171 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130301 A x v u f)). Qed.
Lemma lem7130303 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130304 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term172 A u f x) = (term173 A x u f).
Proof. exact (MK_COMB (@lem7130303 A) (@lem7130302 A x u f)). Qed.
Lemma lem7130305 {A : Type'} (u : A -> Prop) (f : A -> real) : (term174 A u f) = (term175 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem7130304 A x u f)). Qed.
Lemma lem7130306 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7130307 {A : Type'} (u : A -> Prop) (f : A -> real) : (term157 A u f) = (term176 A u f).
Proof. exact (MK_COMB (@lem7130306 A) (@lem7130305 A u f)). Qed.
Lemma lem7130308 {A : Type'} (u : A -> Prop) (f : A -> real) : ((term156 A u f) = (term157 A u f)) = ((term151 A u f) = (term176 A u f)).
Proof. exact (MK_COMB (@lem7130296 A u f) (@lem7130307 A u f)). Qed.
Lemma lem7130309 {A : Type'} (u : A -> Prop) (f : A -> real) : (term151 A u f) = (term176 A u f).
Proof. exact (EQ_MP (@lem7130308 A u f) (@lem7130283 A u f)). Qed.
Lemma lem7130310 {A : Type'} (u : A -> Prop) (f : A -> real) : (term111 A u f) = (term176 A u f).
Proof. exact (TRANS (@lem7130279 A u f) (@lem7130309 A u f)). Qed.
Lemma lem7130311 {A : Type'} (f : A -> real) : (term112 A f) = (term177 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130310 A u f)). Qed.
Lemma lem7130312 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130313 {A : Type'} (f : A -> real) : (term113 A f) = (term178 A f).
Proof. exact (MK_COMB (@lem7130312 A) (@lem7130311 A f)). Qed.
Lemma lem7130315 {A B : Type'} (P : type1413 A B) : (term152 A B P) = (term153 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7130316 {A : Type'} (P : type597 A) : (term179 A P) = (term180 A P).
Proof. exact (@lem7130315 (A -> Prop) (type684 A) P). Qed.
Lemma lem7130317 {A : Type'} (f : A -> real) : (term181 A f) = (term182 A f).
Proof. exact (@lem7130316 A (term183 A f)). Qed.
Lemma lem7130318 {A : Type'} (u : A -> Prop) (f : A -> real) : (term184 A f u) = (term175 A u f).
Proof. exact (eq_refl (term184 A f u)). Qed.
Lemma lem7130319 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7130320 {A : Type'} (u : A -> Prop) (f : A -> real) (x : type684 A) : (term185 A f u x) = (term186 A u f x).
Proof. exact (MK_COMB (@lem7130318 A u f) (@lem7130319 A x)). Qed.
Lemma lem7130321 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term186 A u f x) = (term173 A x u f).
Proof. exact (eq_refl (term186 A u f x)). Qed.
Lemma lem7130322 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term185 A f u x) = (term173 A x u f).
Proof. exact (TRANS (@lem7130320 A u f x) (@lem7130321 A x u f)). Qed.
Lemma lem7130323 {A : Type'} (u : A -> Prop) (f : A -> real) : (term187 A f u) = (term175 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem7130322 A x u f)). Qed.
Lemma lem7130324 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7130325 {A : Type'} (u : A -> Prop) (f : A -> real) : (term188 A f u) = (term176 A u f).
Proof. exact (MK_COMB (@lem7130324 A) (@lem7130323 A u f)). Qed.
Lemma lem7130326 {A : Type'} (f : A -> real) : (term189 A f) = (term177 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130325 A u f)). Qed.
Lemma lem7130327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130328 {A : Type'} (f : A -> real) : (term181 A f) = (term178 A f).
Proof. exact (MK_COMB (@lem7130327 A) (@lem7130326 A f)). Qed.
Lemma lem7130329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7130330 {A : Type'} (f : A -> real) : (term190 A f) = (term191 A f).
Proof. exact (MK_COMB (@lem7130329) (@lem7130328 A f)). Qed.
Lemma lem7130331 {A : Type'} (u : A -> Prop) (f : A -> real) : (term184 A f u) = (term175 A u f).
Proof. exact (eq_refl (term184 A f u)). Qed.
Lemma lem7130332 {A : Type'} (x : type638 A) (u : A -> Prop) : (x u) = (x u).
Proof. exact (eq_refl (x u)). Qed.
Lemma lem7130333 {A : Type'} (f : A -> real) (x : type638 A) (u : A -> Prop) : (term192 A f x u) = (term193 A f x u).
Proof. exact (MK_COMB (@lem7130331 A u f) (@lem7130332 A x u)). Qed.
Lemma lem7130334 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> real) : (term193 A f x u) = (term194 A x u f).
Proof. exact (eq_refl (term193 A f x u)). Qed.
Lemma lem7130335 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> real) : (term192 A f x u) = (term194 A x u f).
Proof. exact (TRANS (@lem7130333 A f x u) (@lem7130334 A x u f)). Qed.
Lemma lem7130336 {A : Type'} (x : type638 A) (f : A -> real) : (term195 A f x) = (term196 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130335 A x u f)). Qed.
Lemma lem7130337 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130338 {A : Type'} (x : type638 A) (f : A -> real) : (term197 A f x) = (term198 A x f).
Proof. exact (MK_COMB (@lem7130337 A) (@lem7130336 A x f)). Qed.
Lemma lem7130339 {A : Type'} (f : A -> real) : (term199 A f) = (term200 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem7130338 A x f)). Qed.
Lemma lem7130340 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7130341 {A : Type'} (f : A -> real) : (term182 A f) = (term201 A f).
Proof. exact (MK_COMB (@lem7130340 A) (@lem7130339 A f)). Qed.
Lemma lem7130342 {A : Type'} (f : A -> real) : ((term181 A f) = (term182 A f)) = ((term178 A f) = (term201 A f)).
Proof. exact (MK_COMB (@lem7130330 A f) (@lem7130341 A f)). Qed.
Lemma lem7130343 {A : Type'} (f : A -> real) : (term178 A f) = (term201 A f).
Proof. exact (EQ_MP (@lem7130342 A f) (@lem7130317 A f)). Qed.
Lemma lem7130344 {A : Type'} (f : A -> real) : (term113 A f) = (term201 A f).
Proof. exact (TRANS (@lem7130313 A f) (@lem7130343 A f)). Qed.
Lemma lem7130345 {A : Type'} : (term114 A) = (term202 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7130344 A f)). Qed.
Lemma lem7130346 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130347 {A : Type'} : (term115 A) = (term203 A).
Proof. exact (MK_COMB (@lem7130346 A) (@lem7130345 A)). Qed.
Lemma lem7130349 {A B : Type'} (P : type1413 A B) : (term152 A B P) = (term153 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7130350 {A : Type'} (P : type706 A) : (term204 A P) = (term205 A P).
Proof. exact (@lem7130349 (A -> real) (type638 A) P). Qed.
Lemma lem7130351 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (@lem7130350 A (term208 A)). Qed.
Lemma lem7130352 {A : Type'} (f : A -> real) : (term209 A f) = (term200 A f).
Proof. exact (eq_refl (term209 A f)). Qed.
Lemma lem7130353 {A : Type'} (x : type638 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7130354 {A : Type'} (f : A -> real) (x : type638 A) : (term210 A f x) = (term211 A f x).
Proof. exact (MK_COMB (@lem7130352 A f) (@lem7130353 A x)). Qed.
Lemma lem7130355 {A : Type'} (x : type638 A) (f : A -> real) : (term211 A f x) = (term198 A x f).
Proof. exact (eq_refl (term211 A f x)). Qed.
Lemma lem7130356 {A : Type'} (x : type638 A) (f : A -> real) : (term210 A f x) = (term198 A x f).
Proof. exact (TRANS (@lem7130354 A f x) (@lem7130355 A x f)). Qed.
Lemma lem7130357 {A : Type'} (f : A -> real) : (term212 A f) = (term200 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem7130356 A x f)). Qed.
Lemma lem7130358 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7130359 {A : Type'} (f : A -> real) : (term213 A f) = (term201 A f).
Proof. exact (MK_COMB (@lem7130358 A) (@lem7130357 A f)). Qed.
Lemma lem7130360 {A : Type'} : (term214 A) = (term202 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7130359 A f)). Qed.
Lemma lem7130361 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130362 {A : Type'} : (term206 A) = (term203 A).
Proof. exact (MK_COMB (@lem7130361 A) (@lem7130360 A)). Qed.
Lemma lem7130363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7130364 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (MK_COMB (@lem7130363) (@lem7130362 A)). Qed.
Lemma lem7130365 {A : Type'} (f : A -> real) : (term209 A f) = (term200 A f).
Proof. exact (eq_refl (term209 A f)). Qed.
Lemma lem7130366 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7130367 {A : Type'} (x : type709 A) (f : A -> real) : (term217 A x f) = (term218 A x f).
Proof. exact (MK_COMB (@lem7130365 A f) (@lem7130366 A x f)). Qed.
Lemma lem7130368 {A : Type'} (x : type709 A) (f : A -> real) : (term218 A x f) = (term219 A x f).
Proof. exact (eq_refl (term218 A x f)). Qed.
Lemma lem7130369 {A : Type'} (x : type709 A) (f : A -> real) : (term217 A x f) = (term219 A x f).
Proof. exact (TRANS (@lem7130367 A x f) (@lem7130368 A x f)). Qed.
Lemma lem7130370 {A : Type'} (x : type709 A) : (term220 A x) = (term221 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7130369 A x f)). Qed.
Lemma lem7130371 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130372 {A : Type'} (x : type709 A) : (term222 A x) = (term223 A x).
Proof. exact (MK_COMB (@lem7130371 A) (@lem7130370 A x)). Qed.
Lemma lem7130373 {A : Type'} : (term224 A) = (term225 A).
Proof. exact (fun_ext (fun x : type709 A => @lem7130372 A x)). Qed.
Lemma lem7130374 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7130375 {A : Type'} : (term207 A) = (term226 A).
Proof. exact (MK_COMB (@lem7130374 A) (@lem7130373 A)). Qed.
Lemma lem7130376 {A : Type'} : ((term206 A) = (term207 A)) = ((term203 A) = (term226 A)).
Proof. exact (MK_COMB (@lem7130364 A) (@lem7130375 A)). Qed.
Lemma lem7130377 {A : Type'} : (term203 A) = (term226 A).
Proof. exact (EQ_MP (@lem7130376 A) (@lem7130351 A)). Qed.
Lemma lem7130379 {A : Type'} : (term115 A) = (term226 A).
Proof. exact (TRANS (@lem7130347 A) (@lem7130377 A)). Qed.
Lemma lem7130380 {A : Type'} : (term11 A) = (term226 A).
Proof. exact (TRANS (@lem7130122 A) (@lem7130379 A)). Qed.
Lemma lem7130381 {A : Type'} (h1 : term11 A) : term226 A.
Proof. exact (EQ_MP (@lem7130380 A) (@lem7129893 A h1)). Qed.
Lemma lem7130382 {A : Type'} (x : type709 A) (h1 : term223 A x) : term223 A x.
Proof. exact (h1). Qed.
Lemma lem7130383 {A : Type'} (f : A -> real) (h1 : term82 A f) : term82 A f.
Proof. exact (h1). Qed.
Lemma lem7130384 {A : Type'} (u : A -> Prop) (f : A -> real) (h1 : term75 A u f) : term75 A u f.
Proof. exact (h1). Qed.
Lemma lem7130385 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term65 A u v f.
Proof. exact (h1). Qed.
Lemma lem7130386 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem7130393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130394 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130393 (A -> Prop) (type672 A) f x). Qed.
Lemma lem7130395 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem7130394 A (@UNION A) s). Qed.
Lemma lem7130396 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7130397 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem7130395 A s) (@lem7130396 A t)). Qed.
Lemma lem7130399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130400 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130399 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem7130401 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term227 A s t).
Proof. exact (@lem7130400 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem7130403 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term227 A s t).
Proof. exact (TRANS (@lem7130397 A s t) (@lem7130401 A s t)). Qed.
Lemma lem7130410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130411 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130410 (A -> Prop) (type672 A) f x). Qed.
Lemma lem7130412 {A : Type'} (t : A -> Prop) : (@UNION A t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t).
Proof. exact (@lem7130411 A (@UNION A) t). Qed.
Lemma lem7130413 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7130414 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@UNION A t s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t s).
Proof. exact (MK_COMB (@lem7130412 A t) (@lem7130413 A s)). Qed.
Lemma lem7130416 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130417 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130416 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem7130418 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t s) = (term227 A t s).
Proof. exact (@lem7130417 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) t) s). Qed.
Lemma lem7130420 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@UNION A t s) = (term227 A t s).
Proof. exact (TRANS (@lem7130414 A t s) (@lem7130418 A t s)). Qed.
Lemma lem7130421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term228 A s t) = (term229 A s t).
Proof. exact (MK_COMB (@lem7130386 A) (@lem7130403 A s t)). Qed.
Lemma lem7130422 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@UNION A s t) = (@UNION A t s)) = ((term227 A s t) = (term227 A t s)).
Proof. exact (MK_COMB (@lem7130421 A s t) (@lem7130420 A t s)). Qed.
Lemma lem7130423 {A : Type'} (s : A -> Prop) : (term37 A s) = (term230 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7130422 A t s)). Qed.
Lemma lem7130424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130425 {A : Type'} (s : A -> Prop) : (term38 A s) = (term231 A s).
Proof. exact (MK_COMB (@lem7130424 A) (@lem7130423 A s)). Qed.
Lemma lem7130426 {A : Type'} : (term39 A) = (term232 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7130425 A s)). Qed.
Lemma lem7130427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130428 {A : Type'} : (term12 A) = (term233 A).
Proof. exact (MK_COMB (@lem7130427 A) (@lem7130426 A)). Qed.
Lemma lem7130429 {A : Type'} (h1 : term12 A) : term233 A.
Proof. exact (EQ_MP (@lem7130428 A) (@lem7130080 A h1)). Qed.
Lemma lem7130430 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7130431 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7130438 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130439 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130438 (A -> Prop) (type672 A) f x). Qed.
Lemma lem7130440 {A : Type'} (u : A -> Prop) : (@UNION A u) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u).
Proof. exact (@lem7130439 A (@UNION A) u). Qed.
Lemma lem7130441 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130442 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v).
Proof. exact (MK_COMB (@lem7130440 A u) (@lem7130441 A v)). Qed.
Lemma lem7130444 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130445 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130444 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem7130446 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v) = (term227 A u v).
Proof. exact (@lem7130445 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u) v). Qed.
Lemma lem7130448 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (term227 A u v).
Proof. exact (TRANS (@lem7130442 A u v) (@lem7130446 A u v)). Qed.
Lemma lem7130449 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130450 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term234 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem7130431 A) (@lem7130448 A u v)). Qed.
Lemma lem7130451 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term24 A u v f) = (term236 A u v f).
Proof. exact (MK_COMB (@lem7130450 A u v) (@lem7130449 A f)). Qed.
Lemma lem7130453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130454 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7130453 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7130455 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term235 A u v) = (term237 A u v).
Proof. exact (@lem7130454 A (@sum A) (term227 A u v)). Qed.
Lemma lem7130456 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130457 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term236 A u v f) = (term238 A u v f).
Proof. exact (MK_COMB (@lem7130455 A u v) (@lem7130456 A f)). Qed.
Lemma lem7130459 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130460 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7130459 (A -> real) real f x). Qed.
Lemma lem7130461 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term238 A u v f) = (term239 A u v f).
Proof. exact (@lem7130460 A (term237 A u v) f). Qed.
Lemma lem7130462 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term236 A u v f) = (term239 A u v f).
Proof. exact (TRANS (@lem7130457 A u v f) (@lem7130461 A u v f)). Qed.
Lemma lem7130463 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term24 A u v f) = (term239 A u v f).
Proof. exact (TRANS (@lem7130451 A u v f) (@lem7130462 A u v f)). Qed.
Lemma lem7130470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130471 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7130470 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7130472 {A : Type'} (u : A -> Prop) : (@sum A u) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u).
Proof. exact (@lem7130471 A (@sum A) u). Qed.
Lemma lem7130473 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130474 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u f).
Proof. exact (MK_COMB (@lem7130472 A u) (@lem7130473 A f)). Qed.
Lemma lem7130476 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130477 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7130476 (A -> real) real f x). Qed.
Lemma lem7130478 {A : Type'} (u : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u f) = (term240 A u f).
Proof. exact (@lem7130477 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u) f). Qed.
Lemma lem7130480 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (term240 A u f).
Proof. exact (TRANS (@lem7130474 A u f) (@lem7130478 A u f)). Qed.
Lemma lem7130481 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term241 A u v f) = (term242 A u v f).
Proof. exact (MK_COMB (@lem7130430) (@lem7130463 A u v f)). Qed.
Lemma lem7130482 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A u f)) = ((term239 A u v f) = (term240 A u f)).
Proof. exact (MK_COMB (@lem7130481 A u v f) (@lem7130480 A u f)). Qed.
Lemma lem7130483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130484 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7130485 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130494 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130495 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130494 (A -> real) (type638 A) f x). Qed.
Lemma lem7130496 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7130495 A x f). Qed.
Lemma lem7130497 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130498 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7130496 A x f) (@lem7130497 A u)). Qed.
Lemma lem7130500 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130501 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130500 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7130502 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term243 A x f u).
Proof. exact (@lem7130501 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7130503 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term243 A x f u).
Proof. exact (TRANS (@lem7130498 A x f u) (@lem7130502 A x f u)). Qed.
Lemma lem7130504 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130505 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (MK_COMB (@lem7130503 A x f u) (@lem7130504 A v)). Qed.
Lemma lem7130507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130508 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7130507 (A -> Prop) A f x). Qed.
Lemma lem7130509 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term244 A x f u v) = (term245 A x f u v).
Proof. exact (@lem7130508 A (term243 A x f u) v). Qed.
Lemma lem7130511 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term245 A x f u v).
Proof. exact (TRANS (@lem7130505 A x f u v) (@lem7130509 A x f u v)). Qed.
Lemma lem7130512 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term246 A x f u v) = (term247 A x f u v).
Proof. exact (MK_COMB (@lem7130485 A f) (@lem7130511 A x f u v)). Qed.
Lemma lem7130514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130515 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7130514 A real f x). Qed.
Lemma lem7130516 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term247 A x f u v) = (term248 A x f u v).
Proof. exact (@lem7130515 A f (term245 A x f u v)). Qed.
Lemma lem7130517 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term246 A x f u v) = (term248 A x f u v).
Proof. exact (TRANS (@lem7130512 A x f u v) (@lem7130516 A x f u v)). Qed.
Lemma lem7130518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7130523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130524 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7130523 nat nat f x). Qed.
Lemma lem7130526 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7130524 NUMERAL 0). Qed.
Lemma lem7130527 : term52 = term249.
Proof. exact (MK_COMB (@lem7130518) (@lem7130526)). Qed.
Lemma lem7130529 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130530 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7130529 nat real f x). Qed.
Lemma lem7130531 : term249 = term250.
Proof. exact (@lem7130530 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7130532 : term52 = term250.
Proof. exact (TRANS (@lem7130527) (@lem7130531)). Qed.
Lemma lem7130533 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term251 A x f u v) = (term252 A x f u v).
Proof. exact (MK_COMB (@lem7130484) (@lem7130517 A x f u v)). Qed.
Lemma lem7130534 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : ((term246 A x f u v) = term52) = ((term248 A x f u v) = term250).
Proof. exact (MK_COMB (@lem7130533 A x f u v) (@lem7130532)). Qed.
Lemma lem7130535 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term253 A x f u v) = (term254 A x f u v).
Proof. exact (MK_COMB (@lem7130483) (@lem7130534 A x f u v)). Qed.
Lemma lem7130536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130537 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7130546 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130547 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130546 (A -> real) (type638 A) f x). Qed.
Lemma lem7130548 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7130547 A x f). Qed.
Lemma lem7130549 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130550 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7130548 A x f) (@lem7130549 A u)). Qed.
Lemma lem7130552 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130553 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130552 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7130554 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term243 A x f u).
Proof. exact (@lem7130553 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7130555 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term243 A x f u).
Proof. exact (TRANS (@lem7130550 A x f u) (@lem7130554 A x f u)). Qed.
Lemma lem7130556 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130557 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (MK_COMB (@lem7130555 A x f u) (@lem7130556 A v)). Qed.
Lemma lem7130559 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130560 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7130559 (A -> Prop) A f x). Qed.
Lemma lem7130561 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term244 A x f u v) = (term245 A x f u v).
Proof. exact (@lem7130560 A (term243 A x f u) v). Qed.
Lemma lem7130563 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term245 A x f u v).
Proof. exact (TRANS (@lem7130557 A x f u v) (@lem7130561 A x f u v)). Qed.
Lemma lem7130564 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130565 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term255 A x f u v) = (term256 A x f u v).
Proof. exact (MK_COMB (@lem7130537 A) (@lem7130563 A x f u v)). Qed.
Lemma lem7130566 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term257 A x f v u) = (term258 A x f v u).
Proof. exact (MK_COMB (@lem7130565 A x f u v) (@lem7130564 A u)). Qed.
Lemma lem7130568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130569 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7130568 A (type686 A) f x). Qed.
Lemma lem7130570 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term256 A x f u v) = (term259 A x f u v).
Proof. exact (@lem7130569 A (@IN A) (term245 A x f u v)). Qed.
Lemma lem7130571 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130572 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term258 A x f v u) = (term260 A x f v u).
Proof. exact (MK_COMB (@lem7130570 A x f u v) (@lem7130571 A u)). Qed.
Lemma lem7130574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130575 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130574 (A -> Prop) Prop f x). Qed.
Lemma lem7130576 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term260 A x f v u) = (term261 A x f v u).
Proof. exact (@lem7130575 A (term259 A x f u v) u). Qed.
Lemma lem7130577 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term258 A x f v u) = (term261 A x f v u).
Proof. exact (TRANS (@lem7130572 A x f v u) (@lem7130576 A x f v u)). Qed.
Lemma lem7130578 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term257 A x f v u) = (term261 A x f v u).
Proof. exact (TRANS (@lem7130566 A x f v u) (@lem7130577 A x f v u)). Qed.
Lemma lem7130579 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term262 A x f v u) = (term263 A x f v u).
Proof. exact (MK_COMB (@lem7130536) (@lem7130578 A x f v u)). Qed.
Lemma lem7130580 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7130589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130590 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130589 (A -> real) (type638 A) f x). Qed.
Lemma lem7130591 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7130590 A x f). Qed.
Lemma lem7130592 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130593 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7130591 A x f) (@lem7130592 A u)). Qed.
Lemma lem7130595 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130596 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7130595 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7130597 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term243 A x f u).
Proof. exact (@lem7130596 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7130598 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term243 A x f u).
Proof. exact (TRANS (@lem7130593 A x f u) (@lem7130597 A x f u)). Qed.
Lemma lem7130599 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130600 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term244 A x f u v).
Proof. exact (MK_COMB (@lem7130598 A x f u) (@lem7130599 A v)). Qed.
Lemma lem7130602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130603 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7130602 (A -> Prop) A f x). Qed.
Lemma lem7130604 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term244 A x f u v) = (term245 A x f u v).
Proof. exact (@lem7130603 A (term243 A x f u) v). Qed.
Lemma lem7130606 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term245 A x f u v).
Proof. exact (TRANS (@lem7130600 A x f u v) (@lem7130604 A x f u v)). Qed.
Lemma lem7130607 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130608 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term255 A x f u v) = (term256 A x f u v).
Proof. exact (MK_COMB (@lem7130580 A) (@lem7130606 A x f u v)). Qed.
Lemma lem7130609 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term264 A x f u v) = (term265 A x f u v).
Proof. exact (MK_COMB (@lem7130608 A x f u v) (@lem7130607 A v)). Qed.
Lemma lem7130611 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130612 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7130611 A (type686 A) f x). Qed.
Lemma lem7130613 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term256 A x f u v) = (term259 A x f u v).
Proof. exact (@lem7130612 A (@IN A) (term245 A x f u v)). Qed.
Lemma lem7130614 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130615 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term265 A x f u v) = (term266 A x f u v).
Proof. exact (MK_COMB (@lem7130613 A x f u v) (@lem7130614 A v)). Qed.
Lemma lem7130617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130618 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130617 (A -> Prop) Prop f x). Qed.
Lemma lem7130619 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term266 A x f u v) = (term267 A x f u v).
Proof. exact (@lem7130618 A (term259 A x f u v) v). Qed.
Lemma lem7130620 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term265 A x f u v) = (term267 A x f u v).
Proof. exact (TRANS (@lem7130615 A x f u v) (@lem7130619 A x f u v)). Qed.
Lemma lem7130621 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term264 A x f u v) = (term267 A x f u v).
Proof. exact (TRANS (@lem7130609 A x f u v) (@lem7130620 A x f u v)). Qed.
Lemma lem7130622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130623 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term268 A x f u v) = (term269 A x f u v).
Proof. exact (MK_COMB (@lem7130622) (@lem7130621 A x f u v)). Qed.
Lemma lem7130624 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term270 A x f v u) = (term271 A x f v u).
Proof. exact (MK_COMB (@lem7130623 A x f u v) (@lem7130579 A x f v u)). Qed.
Lemma lem7130625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130626 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term272 A x f v u) = (term273 A x f v u).
Proof. exact (MK_COMB (@lem7130625) (@lem7130624 A x f v u)). Qed.
Lemma lem7130627 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term274 A x f u v) = (term275 A x f u v).
Proof. exact (MK_COMB (@lem7130626 A x f v u) (@lem7130535 A x f u v)). Qed.
Lemma lem7130628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130633 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130634 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130633 (A -> Prop) Prop f x). Qed.
Lemma lem7130636 {A : Type'} (u : A -> Prop) : (@FINITE A u) = (@I ((A -> Prop) -> Prop) (@FINITE A) u).
Proof. exact (@lem7130634 A (@FINITE A) u). Qed.
Lemma lem7130637 {A : Type'} (u : A -> Prop) : (term120 A u) = (term276 A u).
Proof. exact (MK_COMB (@lem7130628) (@lem7130636 A u)). Qed.
Lemma lem7130638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130639 {A : Type'} (u : A -> Prop) : (term102 A u) = (term277 A u).
Proof. exact (MK_COMB (@lem7130638) (@lem7130637 A u)). Qed.
Lemma lem7130640 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term278 A x f u v) = (term279 A x f u v).
Proof. exact (MK_COMB (@lem7130639 A u) (@lem7130627 A x f u v)). Qed.
Lemma lem7130641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130642 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term280 A x f u v) = (term281 A x f u v).
Proof. exact (MK_COMB (@lem7130641) (@lem7130640 A x f u v)). Qed.
Lemma lem7130643 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term282 A x v u f) = (term283 A x v u f).
Proof. exact (MK_COMB (@lem7130642 A x f u v) (@lem7130482 A v u f)). Qed.
Lemma lem7130644 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term284 A x u f) = (term285 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130643 A x v u f)). Qed.
Lemma lem7130645 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130646 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term286 A x u f) = (term287 A x u f).
Proof. exact (MK_COMB (@lem7130645 A) (@lem7130644 A x u f)). Qed.
Lemma lem7130647 {A : Type'} (x : type709 A) (f : A -> real) : (term288 A x f) = (term289 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130646 A x u f)). Qed.
Lemma lem7130648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130649 {A : Type'} (x : type709 A) (f : A -> real) : (term219 A x f) = (term290 A x f).
Proof. exact (MK_COMB (@lem7130648 A) (@lem7130647 A x f)). Qed.
Lemma lem7130650 {A : Type'} (x : type709 A) : (term221 A x) = (term291 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7130649 A x f)). Qed.
Lemma lem7130651 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130652 {A : Type'} (x : type709 A) : (term223 A x) = (term292 A x).
Proof. exact (MK_COMB (@lem7130651 A) (@lem7130650 A x)). Qed.
Lemma lem7130653 {A : Type'} (x : type709 A) (h1 : term223 A x) : term292 A x.
Proof. exact (EQ_MP (@lem7130652 A x) (@lem7130382 A x h1)). Qed.
Lemma lem7130654 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130655 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7130656 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7130663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130664 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130663 (A -> Prop) (type672 A) f x). Qed.
Lemma lem7130665 {A : Type'} (u : A -> Prop) : (@UNION A u) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u).
Proof. exact (@lem7130664 A (@UNION A) u). Qed.
Lemma lem7130666 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130667 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v).
Proof. exact (MK_COMB (@lem7130665 A u) (@lem7130666 A v)). Qed.
Lemma lem7130669 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130670 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem7130669 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem7130671 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u v) = (term227 A u v).
Proof. exact (@lem7130670 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) u) v). Qed.
Lemma lem7130673 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@UNION A u v) = (term227 A u v).
Proof. exact (TRANS (@lem7130667 A u v) (@lem7130671 A u v)). Qed.
Lemma lem7130674 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130675 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term234 A u v) = (term235 A u v).
Proof. exact (MK_COMB (@lem7130656 A) (@lem7130673 A u v)). Qed.
Lemma lem7130676 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term24 A u v f) = (term236 A u v f).
Proof. exact (MK_COMB (@lem7130675 A u v) (@lem7130674 A f)). Qed.
Lemma lem7130678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130679 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7130678 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7130680 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term235 A u v) = (term237 A u v).
Proof. exact (@lem7130679 A (@sum A) (term227 A u v)). Qed.
Lemma lem7130681 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130682 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term236 A u v f) = (term238 A u v f).
Proof. exact (MK_COMB (@lem7130680 A u v) (@lem7130681 A f)). Qed.
Lemma lem7130684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130685 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7130684 (A -> real) real f x). Qed.
Lemma lem7130686 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term238 A u v f) = (term239 A u v f).
Proof. exact (@lem7130685 A (term237 A u v) f). Qed.
Lemma lem7130687 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term236 A u v f) = (term239 A u v f).
Proof. exact (TRANS (@lem7130682 A u v f) (@lem7130686 A u v f)). Qed.
Lemma lem7130688 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term24 A u v f) = (term239 A u v f).
Proof. exact (TRANS (@lem7130676 A u v f) (@lem7130687 A u v f)). Qed.
Lemma lem7130695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130696 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7130695 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7130697 {A : Type'} (v : A -> Prop) : (@sum A v) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v).
Proof. exact (@lem7130696 A (@sum A) v). Qed.
Lemma lem7130698 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7130699 {A : Type'} (v : A -> Prop) (f : A -> real) : (@sum A v f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v f).
Proof. exact (MK_COMB (@lem7130697 A v) (@lem7130698 A f)). Qed.
Lemma lem7130701 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130702 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7130701 (A -> real) real f x). Qed.
Lemma lem7130703 {A : Type'} (v : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v f) = (term240 A v f).
Proof. exact (@lem7130702 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v) f). Qed.
Lemma lem7130705 {A : Type'} (v : A -> Prop) (f : A -> real) : (@sum A v f) = (term240 A v f).
Proof. exact (TRANS (@lem7130699 A v f) (@lem7130703 A v f)). Qed.
Lemma lem7130706 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term241 A u v f) = (term242 A u v f).
Proof. exact (MK_COMB (@lem7130655) (@lem7130688 A u v f)). Qed.
Lemma lem7130707 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term24 A u v f) = (@sum A v f)) = ((term239 A u v f) = (term240 A v f)).
Proof. exact (MK_COMB (@lem7130706 A u v f) (@lem7130705 A v f)). Qed.
Lemma lem7130708 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term61 A u v f) = (term293 A u v f).
Proof. exact (MK_COMB (@lem7130654) (@lem7130707 A u v f)). Qed.
Lemma lem7130709 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7130714 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130716 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7130714 A real f x). Qed.
Lemma lem7130717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7130722 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130723 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7130722 nat nat f x). Qed.
Lemma lem7130725 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7130723 NUMERAL 0). Qed.
Lemma lem7130726 : term52 = term249.
Proof. exact (MK_COMB (@lem7130717) (@lem7130725)). Qed.
Lemma lem7130728 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130729 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7130728 nat real f x). Qed.
Lemma lem7130730 : term249 = term250.
Proof. exact (@lem7130729 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7130731 : term52 = term250.
Proof. exact (TRANS (@lem7130726) (@lem7130730)). Qed.
Lemma lem7130732 {A : Type'} (f : A -> real) (x : A) : (term294 A f x) = (term295 A f x).
Proof. exact (MK_COMB (@lem7130709) (@lem7130716 A f x)). Qed.
Lemma lem7130733 {A : Type'} (f : A -> real) (x : A) : ((f x) = term52) = ((@I (A -> real) f x) = term250).
Proof. exact (MK_COMB (@lem7130732 A f x) (@lem7130731)). Qed.
Lemma lem7130740 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130741 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7130740 A (type686 A) f x). Qed.
Lemma lem7130742 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7130741 A (@IN A) x). Qed.
Lemma lem7130743 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7130744 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x v).
Proof. exact (MK_COMB (@lem7130742 A x) (@lem7130743 A v)). Qed.
Lemma lem7130746 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130747 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130746 (A -> Prop) Prop f x). Qed.
Lemma lem7130748 {A : Type'} (x : A) (v : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x v) = (term296 A x v).
Proof. exact (@lem7130747 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) v). Qed.
Lemma lem7130750 {A : Type'} (x : A) (v : A -> Prop) : (@IN A x v) = (term296 A x v).
Proof. exact (TRANS (@lem7130744 A x v) (@lem7130748 A x v)). Qed.
Lemma lem7130751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7130758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130759 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7130758 A (type686 A) f x). Qed.
Lemma lem7130760 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7130759 A (@IN A) x). Qed.
Lemma lem7130761 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7130762 {A : Type'} (x : A) (u : A -> Prop) : (@IN A x u) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x u).
Proof. exact (MK_COMB (@lem7130760 A x) (@lem7130761 A u)). Qed.
Lemma lem7130764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130765 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130764 (A -> Prop) Prop f x). Qed.
Lemma lem7130766 {A : Type'} (x : A) (u : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x u) = (term296 A x u).
Proof. exact (@lem7130765 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) u). Qed.
Lemma lem7130768 {A : Type'} (x : A) (u : A -> Prop) : (@IN A x u) = (term296 A x u).
Proof. exact (TRANS (@lem7130762 A x u) (@lem7130766 A x u)). Qed.
Lemma lem7130769 {A : Type'} (x : A) (u : A -> Prop) : (term51 A x u) = (term297 A x u).
Proof. exact (MK_COMB (@lem7130751) (@lem7130768 A x u)). Qed.
Lemma lem7130770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130771 {A : Type'} (x : A) (u : A -> Prop) : (term47 A x u) = (term298 A x u).
Proof. exact (MK_COMB (@lem7130770) (@lem7130769 A x u)). Qed.
Lemma lem7130772 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term49 A u x v) = (term299 A u x v).
Proof. exact (MK_COMB (@lem7130771 A x u) (@lem7130750 A x v)). Qed.
Lemma lem7130773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130774 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term54 A u x v) = (term300 A u x v).
Proof. exact (MK_COMB (@lem7130773) (@lem7130772 A u x v)). Qed.
Lemma lem7130775 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term56 A u v f x) = (term301 A u v f x).
Proof. exact (MK_COMB (@lem7130774 A u x v) (@lem7130733 A f x)). Qed.
Lemma lem7130776 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term58 A u v f) = (term302 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7130775 A u v f x)). Qed.
Lemma lem7130777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7130778 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term59 A u v f) = (term303 A u v f).
Proof. exact (MK_COMB (@lem7130777 A) (@lem7130776 A u v f)). Qed.
Lemma lem7130783 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7130784 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7130783 (A -> Prop) Prop f x). Qed.
Lemma lem7130786 {A : Type'} (v : A -> Prop) : (@FINITE A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem7130784 A (@FINITE A) v). Qed.
Lemma lem7130787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130788 {A : Type'} (v : A -> Prop) : (term28 A v) = (term304 A v).
Proof. exact (MK_COMB (@lem7130787) (@lem7130786 A v)). Qed.
Lemma lem7130789 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term60 A u v f) = (term305 A u v f).
Proof. exact (MK_COMB (@lem7130788 A v) (@lem7130778 A u v f)). Qed.
Lemma lem7130790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130791 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term63 A u v f) = (term306 A u v f).
Proof. exact (MK_COMB (@lem7130790) (@lem7130789 A u v f)). Qed.
Lemma lem7130792 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term65 A u v f) = (term307 A u v f).
Proof. exact (MK_COMB (@lem7130791 A u v f) (@lem7130708 A u v f)). Qed.
Lemma lem7130793 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term307 A u v f.
Proof. exact (EQ_MP (@lem7130792 A u v f) (@lem7130385 A u v f h1)). Qed.
Lemma lem7130795 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term305 A u v f.
Proof. exact (proj1 (@lem7130793 A u v f h1)). Qed.
Lemma lem7130796 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term303 A u v f.
Proof. exact (proj2 (@lem7130795 A u v f h1)). Qed.
Lemma lem7130799 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term227 A s t) = (term227 A t s)) = ((term227 A s t) = (term227 A t s)).
Proof. exact (eq_refl ((term227 A s t) = (term227 A t s))). Qed.
Lemma lem7130800 {A : Type'} (s : A -> Prop) : (term230 A s) = (term230 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7130799 A t s)). Qed.
Lemma lem7130801 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130802 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (MK_COMB (@lem7130801 A) (@lem7130800 A s)). Qed.
Lemma lem7130803 {A : Type'} : (term232 A) = (term232 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7130802 A s)). Qed.
Lemma lem7130804 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130806 {A : Type'} : (term233 A) = (term233 A).
Proof. exact (MK_COMB (@lem7130804 A) (@lem7130803 A)). Qed.
Lemma lem7130807 {A : Type'} (h1 : term12 A) : term233 A.
Proof. exact (EQ_MP (@lem7130806 A) (@lem7130429 A h1)). Qed.
Lemma lem7130809 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term239 A u v f) = (term240 A u f)) = ((term239 A u v f) = (term240 A u f)).
Proof. exact (eq_refl ((term239 A u v f) = (term240 A u f))). Qed.
Lemma lem7130823 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term279 A x f u v) = (term308 A x f u v).
Proof. exact (@lem19490 (term271 A x f v u) (term276 A u) (term254 A x f u v)). Qed.
Lemma lem7130824 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term309 A x f u v) = (term309 A x f u v).
Proof. exact (eq_refl (term309 A x f u v)). Qed.
Lemma lem7130831 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term310 A x f v u) = (term311 A x f v u).
Proof. exact (@lem19490 (term267 A x f u v) (term276 A u) (term263 A x f v u)). Qed.
Lemma lem7130832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130833 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term312 A x f v u) = (term313 A x f v u).
Proof. exact (MK_COMB (@lem7130832) (@lem7130831 A x f v u)). Qed.
Lemma lem7130834 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term308 A x f u v) = (term314 A x f u v).
Proof. exact (MK_COMB (@lem7130833 A x f v u) (@lem7130824 A x f u v)). Qed.
Lemma lem7130836 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term279 A x f u v) = (term314 A x f u v).
Proof. exact (TRANS (@lem7130823 A x f u v) (@lem7130834 A x f u v)). Qed.
Lemma lem7130837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7130838 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term281 A x f u v) = (term315 A x f u v).
Proof. exact (MK_COMB (@lem7130837) (@lem7130836 A x f u v)). Qed.
Lemma lem7130839 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term283 A x v u f) = (term316 A x v u f).
Proof. exact (MK_COMB (@lem7130838 A x f u v) (@lem7130809 A v u f)). Qed.
Lemma lem7130840 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term316 A x v u f) = (term317 A x v u f).
Proof. exact (@lem19699 (term311 A x f v u) (term309 A x f u v) ((term239 A u v f) = (term240 A u f))). Qed.
Lemma lem7130841 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term318 A x v u f) = (term318 A x v u f).
Proof. exact (eq_refl (term318 A x v u f)). Qed.
Lemma lem7130848 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term319 A x v u f) = (term320 A x v u f).
Proof. exact (@lem19699 (term321 A x f u v) (term322 A x f v u) ((term239 A u v f) = (term240 A u f))). Qed.
Lemma lem7130849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7130850 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term323 A x v u f) = (term324 A x v u f).
Proof. exact (MK_COMB (@lem7130849) (@lem7130848 A x v u f)). Qed.
Lemma lem7130851 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term317 A x v u f) = (term325 A x v u f).
Proof. exact (MK_COMB (@lem7130850 A x v u f) (@lem7130841 A x v u f)). Qed.
Lemma lem7130852 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term316 A x v u f) = (term325 A x v u f).
Proof. exact (TRANS (@lem7130840 A x v u f) (@lem7130851 A x v u f)). Qed.
Lemma lem7130853 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term283 A x v u f) = (term325 A x v u f).
Proof. exact (TRANS (@lem7130839 A x v u f) (@lem7130852 A x v u f)). Qed.
Lemma lem7130854 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term285 A x u f) = (term326 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7130853 A x v u f)). Qed.
Lemma lem7130855 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130856 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term287 A x u f) = (term327 A x u f).
Proof. exact (MK_COMB (@lem7130855 A) (@lem7130854 A x u f)). Qed.
Lemma lem7130857 {A : Type'} (x : type709 A) (f : A -> real) : (term289 A x f) = (term328 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7130856 A x u f)). Qed.
Lemma lem7130858 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7130859 {A : Type'} (x : type709 A) (f : A -> real) : (term290 A x f) = (term329 A x f).
Proof. exact (MK_COMB (@lem7130858 A) (@lem7130857 A x f)). Qed.
Lemma lem7130860 {A : Type'} (x : type709 A) : (term291 A x) = (term330 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7130859 A x f)). Qed.
Lemma lem7130861 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7130863 {A : Type'} (x : type709 A) : (term292 A x) = (term331 A x).
Proof. exact (MK_COMB (@lem7130861 A) (@lem7130860 A x)). Qed.
Lemma lem7130864 {A : Type'} (x : type709 A) (h1 : term223 A x) : term331 A x.
Proof. exact (EQ_MP (@lem7130863 A x) (@lem7130653 A x h1)). Qed.
Lemma lem7130886 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term301 A u v f x) = (term301 A u v f x).
Proof. exact (eq_refl (term301 A u v f x)). Qed.
Lemma lem7130887 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term302 A u v f) = (term302 A u v f).
Proof. exact (fun_ext (fun x : A => @lem7130886 A u v f x)). Qed.
Lemma lem7130888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7130890 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term303 A u v f) = (term303 A u v f).
Proof. exact (MK_COMB (@lem7130888 A) (@lem7130887 A u v f)). Qed.
Lemma lem7130891 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term303 A u v f.
Proof. exact (EQ_MP (@lem7130890 A u v f) (@lem7130796 A u v f h1)). Qed.
Lemma lem7130892 {A : Type'} (_95176 : A -> Prop) (h1 : term12 A) : term332 A _95176.
Proof. exact (@lem7130807 A h1 _95176). Qed.
Lemma lem7130893 {A : Type'} (_95176 : A -> Prop) : (term332 A _95176) = (term231 A _95176).
Proof. exact (eq_refl (term332 A _95176)). Qed.
Lemma lem7130894 {A : Type'} (_95176 : A -> Prop) (h1 : term12 A) : term231 A _95176.
Proof. exact (EQ_MP (@lem7130893 A _95176) (@lem7130892 A _95176 h1)). Qed.
Lemma lem7130895 {A : Type'} (_95176 : A -> Prop) (_95177 : A -> Prop) (h1 : term12 A) : term333 A _95176 _95177.
Proof. exact (@lem7130894 A _95176 h1 _95177). Qed.
Lemma lem7130896 {A : Type'} (_95177 : A -> Prop) (_95176 : A -> Prop) : (term333 A _95176 _95177) = ((term227 A _95176 _95177) = (term227 A _95177 _95176)).
Proof. exact (eq_refl (term333 A _95176 _95177)). Qed.
Lemma lem7130898 {A : Type'} (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term334 A x _95178.
Proof. exact (@lem7130864 A x h1 _95178). Qed.
Lemma lem7130899 {A : Type'} (x : type709 A) (_95178 : A -> real) : (term334 A x _95178) = (term329 A x _95178).
Proof. exact (eq_refl (term334 A x _95178)). Qed.
Lemma lem7130900 {A : Type'} (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term329 A x _95178.
Proof. exact (EQ_MP (@lem7130899 A x _95178) (@lem7130898 A _95178 x h1)). Qed.
Lemma lem7130901 {A : Type'} (_95178 : A -> real) (_95179 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term335 A x _95178 _95179.
Proof. exact (@lem7130900 A _95178 x h1 _95179). Qed.
Lemma lem7130902 {A : Type'} (x : type709 A) (_95179 : A -> Prop) (_95178 : A -> real) : (term335 A x _95178 _95179) = (term327 A x _95179 _95178).
Proof. exact (eq_refl (term335 A x _95178 _95179)). Qed.
Lemma lem7130903 {A : Type'} (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term327 A x _95179 _95178.
Proof. exact (EQ_MP (@lem7130902 A x _95179 _95178) (@lem7130901 A _95178 _95179 x h1)). Qed.
Lemma lem7130904 {A : Type'} (_95179 : A -> Prop) (_95178 : A -> real) (_95180 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term336 A x _95179 _95178 _95180.
Proof. exact (@lem7130903 A _95179 _95178 x h1 _95180). Qed.
Lemma lem7130905 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term336 A x _95179 _95178 _95180) = (term325 A x _95180 _95179 _95178).
Proof. exact (eq_refl (term336 A x _95179 _95178 _95180)). Qed.
Lemma lem7130906 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term325 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7130905 A x _95180 _95179 _95178) (@lem7130904 A _95179 _95178 _95180 x h1)). Qed.
Lemma lem7130907 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term337 A u v f _95181.
Proof. exact (@lem7130891 A u v f h1 _95181). Qed.
Lemma lem7130908 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (_95181 : A) : (term337 A u v f _95181) = (term301 A u v f _95181).
Proof. exact (eq_refl (term337 A u v f _95181)). Qed.
Lemma lem7130909 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term301 A u v f _95181.
Proof. exact (EQ_MP (@lem7130908 A u v f _95181) (@lem7130907 A _95181 u v f h1)). Qed.
Lemma lem7130910 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term318 A x _95180 _95179 _95178.
Proof. exact (proj2 (@lem7130906 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130911 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term320 A x _95180 _95179 _95178.
Proof. exact (proj1 (@lem7130906 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130912 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term338 A x _95180 _95179 _95178.
Proof. exact (proj2 (@lem7130911 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130913 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term339 A x _95180 _95179 _95178.
Proof. exact (proj1 (@lem7130911 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130917 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term293 A u v f.
Proof. exact (proj2 (@lem7130793 A u v f h1)). Qed.
Lemma lem7130930 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (_95181 : A) : (term301 A u v f _95181) = (term340 A u v f _95181).
Proof. exact (@lem7129626 (term297 A _95181 u) (term296 A _95181 v) ((@I (A -> real) f _95181) = term250)). Qed.
Lemma lem7130931 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term340 A u v f _95181.
Proof. exact (EQ_MP (@lem7130930 A u v f _95181) (@lem7130909 A _95181 u v f h1)). Qed.
Lemma lem7130942 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term318 A x _95180 _95179 _95178) = (term341 A x _95180 _95179 _95178).
Proof. exact (@lem7129626 (term276 A _95179) (term254 A x _95178 _95179 _95180) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7130943 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term341 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7130942 A x _95180 _95179 _95178) (@lem7130910 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130954 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term339 A x _95180 _95179 _95178) = (term342 A x _95180 _95179 _95178).
Proof. exact (@lem7129626 (term276 A _95179) (term267 A x _95178 _95179 _95180) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7130955 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term342 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7130954 A x _95180 _95179 _95178) (@lem7130913 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7130966 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term338 A x _95180 _95179 _95178) = (term343 A x _95180 _95179 _95178).
Proof. exact (@lem7129626 (term276 A _95179) (term263 A x _95178 _95180 _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7130967 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term343 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7130966 A x _95180 _95179 _95178) (@lem7130912 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7131092 {A : Type'} : (@I ((A -> Prop) -> (A -> real) -> real)) = (@I ((A -> Prop) -> (A -> real) -> real)).
Proof. exact (eq_refl (@I ((A -> Prop) -> (A -> real) -> real))). Qed.
Lemma lem7131093 {A : Type'} (_95214 : type646 A) (_95216 : type646 A) (h1 : _95214 = _95216) : _95214 = _95216.
Proof. exact (h1). Qed.
Lemma lem7131094 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (h1 : _95215 = _95217) : _95215 = _95217.
Proof. exact (h1). Qed.
Lemma lem7131095 {A : Type'} (_95214 : type646 A) (_95216 : type646 A) (h1 : _95214 = _95216) : (@I ((A -> Prop) -> (A -> real) -> real) _95214) = (@I ((A -> Prop) -> (A -> real) -> real) _95216).
Proof. exact (MK_COMB (@lem7131092 A) (@lem7131093 A _95214 _95216 h1)). Qed.
Lemma lem7131096 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) (h1 : _95215 = _95217) (h2 : _95214 = _95216) : (@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217).
Proof. exact (MK_COMB (@lem7131095 A _95214 _95216 h2) (@lem7131094 A _95215 _95217 h1)). Qed.
Lemma lem7131097 {A : Type'} (_95214 : type646 A) (_95216 : type646 A) (_95215 : A -> Prop) (_95217 : A -> Prop) (h1 : _95215 = _95217) : term344 A _95214 _95215 _95216 _95217.
Proof. exact (fun h0 : _95214 = _95216 => @lem7131096 A _95215 _95217 _95214 _95216 h1 h0). Qed.
Lemma lem7131099 (a : Prop) (b : Prop) : (a -> b) = (term345 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7131100 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : (term344 A _95214 _95215 _95216 _95217) = (term346 A _95214 _95215 _95216 _95217).
Proof. exact (@lem7131099 (_95214 = _95216) ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217))). Qed.
Lemma lem7131101 {A : Type'} (_95214 : type646 A) (_95216 : type646 A) (_95215 : A -> Prop) (_95217 : A -> Prop) (h1 : _95215 = _95217) : term346 A _95214 _95215 _95216 _95217.
Proof. exact (EQ_MP (@lem7131100 A _95214 _95215 _95216 _95217) (@lem7131097 A _95214 _95216 _95215 _95217 h1)). Qed.
Lemma lem7131102 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : term347 A _95214 _95215 _95216 _95217.
Proof. exact (fun h0 : _95215 = _95217 => @lem7131101 A _95214 _95216 _95215 _95217 h0). Qed.
Lemma lem7131104 (a : Prop) (b : Prop) : (a -> b) = (term345 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7131105 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : (term347 A _95214 _95215 _95216 _95217) = (term348 A _95214 _95215 _95216 _95217).
Proof. exact (@lem7131104 (_95215 = _95217) (term346 A _95214 _95215 _95216 _95217)). Qed.
Lemma lem7131106 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : term348 A _95214 _95215 _95216 _95217.
Proof. exact (EQ_MP (@lem7131105 A _95214 _95215 _95216 _95217) (@lem7131102 A _95214 _95215 _95216 _95217)). Qed.
Lemma lem7131107 {A : Type'} : (@I ((A -> real) -> real)) = (@I ((A -> real) -> real)).
Proof. exact (eq_refl (@I ((A -> real) -> real))). Qed.
Lemma lem7131108 {A : Type'} (_95218 : type717 A) (_95220 : type717 A) (h1 : _95218 = _95220) : _95218 = _95220.
Proof. exact (h1). Qed.
Lemma lem7131109 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (h1 : _95219 = _95221) : _95219 = _95221.
Proof. exact (h1). Qed.
Lemma lem7131110 {A : Type'} (_95218 : type717 A) (_95220 : type717 A) (h1 : _95218 = _95220) : (@I ((A -> real) -> real) _95218) = (@I ((A -> real) -> real) _95220).
Proof. exact (MK_COMB (@lem7131107 A) (@lem7131108 A _95218 _95220 h1)). Qed.
Lemma lem7131111 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) (h1 : _95219 = _95221) (h2 : _95218 = _95220) : (@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221).
Proof. exact (MK_COMB (@lem7131110 A _95218 _95220 h2) (@lem7131109 A _95219 _95221 h1)). Qed.
Lemma lem7131112 {A : Type'} (_95218 : type717 A) (_95220 : type717 A) (_95219 : A -> real) (_95221 : A -> real) (h1 : _95219 = _95221) : term349 A _95218 _95219 _95220 _95221.
Proof. exact (fun h0 : _95218 = _95220 => @lem7131111 A _95219 _95221 _95218 _95220 h1 h0). Qed.
Lemma lem7131114 (a : Prop) (b : Prop) : (a -> b) = (term345 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7131115 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : (term349 A _95218 _95219 _95220 _95221) = (term350 A _95218 _95219 _95220 _95221).
Proof. exact (@lem7131114 (_95218 = _95220) ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221))). Qed.
Lemma lem7131116 {A : Type'} (_95218 : type717 A) (_95220 : type717 A) (_95219 : A -> real) (_95221 : A -> real) (h1 : _95219 = _95221) : term350 A _95218 _95219 _95220 _95221.
Proof. exact (EQ_MP (@lem7131115 A _95218 _95219 _95220 _95221) (@lem7131112 A _95218 _95220 _95219 _95221 h1)). Qed.
Lemma lem7131117 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : term351 A _95218 _95219 _95220 _95221.
Proof. exact (fun h0 : _95219 = _95221 => @lem7131116 A _95218 _95220 _95219 _95221 h0). Qed.
Lemma lem7131119 (a : Prop) (b : Prop) : (a -> b) = (term345 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7131120 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : (term351 A _95218 _95219 _95220 _95221) = (term352 A _95218 _95219 _95220 _95221).
Proof. exact (@lem7131119 (_95219 = _95221) (term350 A _95218 _95219 _95220 _95221)). Qed.
Lemma lem7131121 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : term352 A _95218 _95219 _95220 _95221.
Proof. exact (EQ_MP (@lem7131120 A _95218 _95219 _95220 _95221) (@lem7131117 A _95218 _95219 _95220 _95221)). Qed.
Lemma lem7131159 (x : real) (y : real) (z : real) : term353 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem7131185 {A : Type'} (x : A -> real) : x = x.
Proof. exact (@lem21386 (A -> real) x). Qed.
Lemma lem7131186 {A : Type'} (x : A -> real) : x = x.
Proof. exact (@lem7131185 A x). Qed.
Lemma lem7131187 {A : Type'} (f : A -> real) : f = f.
Proof. exact (@lem7131186 A f). Qed.
Lemma lem7131188 {A : Type'} (f : A -> real) : term354 A f.
Proof. exact (fun h0 : term355 A f => @lem7131187 A f). Qed.
Lemma lem7131190 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131191 {A : Type'} (f : A -> real) : (term354 A f) = (f = f).
Proof. exact (@lem7131190 (f = f)). Qed.
Lemma lem7131192 {A : Type'} (f : A -> real) : f = f.
Proof. exact (EQ_MP (@lem7131191 A f) (@lem7131188 A f)). Qed.
Lemma lem7131194 {A : Type'} (_95177 : A -> Prop) (_95176 : A -> Prop) (h1 : term12 A) : (term227 A _95176 _95177) = (term227 A _95177 _95176).
Proof. exact (EQ_MP (@lem7130896 A _95177 _95176) (@lem7130895 A _95176 _95177 h1)). Qed.
Lemma lem7131195 {A : Type'} (_95177 : A -> Prop) (_95176 : A -> Prop) (h1 : term12 A) : (term227 A _95176 _95177) = (term227 A _95177 _95176).
Proof. exact (@lem7131194 A _95177 _95176 h1). Qed.
Lemma lem7131196 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term227 A v u) = (term227 A u v).
Proof. exact (@lem7131195 A u v h1). Qed.
Lemma lem7131197 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term357 A u v.
Proof. exact (fun h0 : term358 A u v => @lem7131196 A u v h1). Qed.
Lemma lem7131199 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131200 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term357 A u v) = ((term227 A v u) = (term227 A u v)).
Proof. exact (@lem7131199 ((term227 A v u) = (term227 A u v))). Qed.
Lemma lem7131201 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term227 A v u) = (term227 A u v).
Proof. exact (EQ_MP (@lem7131200 A u v) (@lem7131197 A u v h1)). Qed.
Lemma lem7131203 {A : Type'} (x : type646 A) : x = x.
Proof. exact (@lem21386 (type646 A) x). Qed.
Lemma lem7131204 {A : Type'} (x : type646 A) : x = x.
Proof. exact (@lem7131203 A x). Qed.
Lemma lem7131205 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (@lem7131204 A (@sum A)). Qed.
Lemma lem7131206 {A : Type'} : term359 A.
Proof. exact (fun h0 : term360 A => @lem7131205 A). Qed.
Lemma lem7131208 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131209 {A : Type'} : (term359 A) = ((@sum A) = (@sum A)).
Proof. exact (@lem7131208 ((@sum A) = (@sum A))). Qed.
Lemma lem7131210 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (EQ_MP (@lem7131209 A) (@lem7131206 A)). Qed.
Lemma lem7131228 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131229 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term346 A _95214 _95215 _95216 _95217) = (term361 A _95215 _95217 _95214 _95216).
Proof. exact (@lem7131228 ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217)) (term362 A _95214 _95216)). Qed.
Lemma lem7131239 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) : (term363 A _95215 _95217) = (term363 A _95215 _95217).
Proof. exact (eq_refl (term363 A _95215 _95217)). Qed.
Lemma lem7131240 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term348 A _95214 _95215 _95216 _95217) = (term364 A _95215 _95217 _95214 _95216).
Proof. exact (MK_COMB (@lem7131239 A _95215 _95217) (@lem7131229 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131244 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131245 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term364 A _95215 _95217 _95214 _95216) = (term365 A _95215 _95217 _95214 _95216).
Proof. exact (@lem7131244 ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217)) (term366 A _95215 _95217) (term362 A _95214 _95216)). Qed.
Lemma lem7131267 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term348 A _95214 _95215 _95216 _95217) = (term365 A _95215 _95217 _95214 _95216).
Proof. exact (TRANS (@lem7131240 A _95215 _95217 _95214 _95216) (@lem7131245 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131269 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term367 A _95214 _95215 _95216 _95217) = (term368 A _95215 _95217 _95214 _95216).
Proof. exact (MK_COMB (@lem7131268) (@lem7131267 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131291 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term365 A _95215 _95217 _95214 _95216) = (term365 A _95215 _95217 _95214 _95216).
Proof. exact (eq_refl (term365 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131292 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : ((term348 A _95214 _95215 _95216 _95217) = (term365 A _95215 _95217 _95214 _95216)) = ((term365 A _95215 _95217 _95214 _95216) = (term365 A _95215 _95217 _95214 _95216)).
Proof. exact (MK_COMB (@lem7131269 A _95215 _95217 _95214 _95216) (@lem7131291 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131294 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7131295 (x : Prop) : (x = x) = True.
Proof. exact (@lem7131294 Prop x). Qed.
Lemma lem7131296 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : ((term365 A _95215 _95217 _95214 _95216) = (term365 A _95215 _95217 _95214 _95216)) = True.
Proof. exact (@lem7131295 (term365 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131297 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : ((term348 A _95214 _95215 _95216 _95217) = (term365 A _95215 _95217 _95214 _95216)) = True.
Proof. exact (TRANS (@lem7131292 A _95215 _95217 _95214 _95216) (@lem7131296 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131298 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : True = ((term348 A _95214 _95215 _95216 _95217) = (term365 A _95215 _95217 _95214 _95216)).
Proof. exact (SYM (@lem7131297 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131299 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term348 A _95214 _95215 _95216 _95217) = (term365 A _95215 _95217 _95214 _95216).
Proof. exact (EQ_MP (@lem7131298 A _95215 _95217 _95214 _95216) (@lem0)). Qed.
Lemma lem7131300 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : term365 A _95215 _95217 _95214 _95216.
Proof. exact (EQ_MP (@lem7131299 A _95215 _95217 _95214 _95216) (@lem7131106 A _95214 _95215 _95216 _95217)). Qed.
Lemma lem7131302 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7131303 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : (term365 A _95215 _95217 _95214 _95216) = (term370 A _95214 _95215 _95216 _95217).
Proof. exact (@lem7131302 (term371 A _95215 _95217 _95214 _95216) ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217))). Qed.
Lemma lem7131305 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7131306 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term374 A _95215 _95217 _95214 _95216) = (term375 A _95215 _95217 _95214 _95216).
Proof. exact (@lem7131305 (term366 A _95215 _95217) (term362 A _95214 _95216)). Qed.
Lemma lem7131308 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131309 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) : (term377 A _95215 _95217) = (_95215 = _95217).
Proof. exact (@lem7131308 (_95215 = _95217)). Qed.
Lemma lem7131310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7131311 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) : (term378 A _95215 _95217) = (term379 A _95215 _95217).
Proof. exact (MK_COMB (@lem7131310) (@lem7131309 A _95215 _95217)). Qed.
Lemma lem7131313 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131314 {A : Type'} (_95214 : type646 A) (_95216 : type646 A) : (term380 A _95214 _95216) = (_95214 = _95216).
Proof. exact (@lem7131313 (_95214 = _95216)). Qed.
Lemma lem7131315 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term375 A _95215 _95217 _95214 _95216) = (term381 A _95215 _95217 _95214 _95216).
Proof. exact (MK_COMB (@lem7131311 A _95215 _95217) (@lem7131314 A _95214 _95216)). Qed.
Lemma lem7131316 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term374 A _95215 _95217 _95214 _95216) = (term381 A _95215 _95217 _95214 _95216).
Proof. exact (TRANS (@lem7131306 A _95215 _95217 _95214 _95216) (@lem7131315 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7131318 {A : Type'} (_95215 : A -> Prop) (_95217 : A -> Prop) (_95214 : type646 A) (_95216 : type646 A) : (term382 A _95215 _95217 _95214 _95216) = (term383 A _95215 _95217 _95214 _95216).
Proof. exact (MK_COMB (@lem7131317) (@lem7131316 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131319 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217)) = ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217)).
Proof. exact (eq_refl ((@I ((A -> Prop) -> (A -> real) -> real) _95214 _95215) = (@I ((A -> Prop) -> (A -> real) -> real) _95216 _95217))). Qed.
Lemma lem7131320 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : (term370 A _95214 _95215 _95216 _95217) = (term384 A _95214 _95215 _95216 _95217).
Proof. exact (MK_COMB (@lem7131318 A _95215 _95217 _95214 _95216) (@lem7131319 A _95214 _95215 _95216 _95217)). Qed.
Lemma lem7131321 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : (term365 A _95215 _95217 _95214 _95216) = (term384 A _95214 _95215 _95216 _95217).
Proof. exact (TRANS (@lem7131303 A _95214 _95215 _95216 _95217) (@lem7131320 A _95214 _95215 _95216 _95217)). Qed.
Lemma lem7131323 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term385 A u v.
Proof. exact (conj (@lem7131201 A u v h1) (@lem7131210 A)). Qed.
Lemma lem7131325 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : term384 A _95214 _95215 _95216 _95217.
Proof. exact (EQ_MP (@lem7131321 A _95214 _95215 _95216 _95217) (@lem7131300 A _95215 _95217 _95214 _95216)). Qed.
Lemma lem7131326 {A : Type'} (_95214 : type646 A) (_95215 : A -> Prop) (_95216 : type646 A) (_95217 : A -> Prop) : term384 A _95214 _95215 _95216 _95217.
Proof. exact (@lem7131325 A _95214 _95215 _95216 _95217). Qed.
Lemma lem7131327 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term386 A u v.
Proof. exact (@lem7131326 A (@sum A) (term227 A v u) (@sum A) (term227 A u v)). Qed.
Lemma lem7131330 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term237 A v u) = (term237 A u v).
Proof. exact (@lem7131327 A u v (@lem7131323 A u v h1)). Qed.
Lemma lem7131331 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term237 A v u) = (term237 A u v).
Proof. exact (@lem7131330 A u v h1). Qed.
Lemma lem7131332 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term387 A u v.
Proof. exact (fun h0 : term388 A u v => @lem7131331 A u v h1). Qed.
Lemma lem7131334 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131335 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term387 A u v) = ((term237 A v u) = (term237 A u v)).
Proof. exact (@lem7131334 ((term237 A v u) = (term237 A u v))). Qed.
Lemma lem7131336 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : (term237 A v u) = (term237 A u v).
Proof. exact (EQ_MP (@lem7131335 A u v) (@lem7131332 A u v h1)). Qed.
Lemma lem7131354 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131355 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term350 A _95218 _95219 _95220 _95221) = (term389 A _95219 _95221 _95218 _95220).
Proof. exact (@lem7131354 ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221)) (term390 A _95218 _95220)). Qed.
Lemma lem7131365 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) : (term391 A _95219 _95221) = (term391 A _95219 _95221).
Proof. exact (eq_refl (term391 A _95219 _95221)). Qed.
Lemma lem7131366 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term352 A _95218 _95219 _95220 _95221) = (term392 A _95219 _95221 _95218 _95220).
Proof. exact (MK_COMB (@lem7131365 A _95219 _95221) (@lem7131355 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131370 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131371 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term392 A _95219 _95221 _95218 _95220) = (term393 A _95219 _95221 _95218 _95220).
Proof. exact (@lem7131370 ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221)) (term394 A _95219 _95221) (term390 A _95218 _95220)). Qed.
Lemma lem7131393 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term352 A _95218 _95219 _95220 _95221) = (term393 A _95219 _95221 _95218 _95220).
Proof. exact (TRANS (@lem7131366 A _95219 _95221 _95218 _95220) (@lem7131371 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131395 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term395 A _95218 _95219 _95220 _95221) = (term396 A _95219 _95221 _95218 _95220).
Proof. exact (MK_COMB (@lem7131394) (@lem7131393 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131417 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term393 A _95219 _95221 _95218 _95220) = (term393 A _95219 _95221 _95218 _95220).
Proof. exact (eq_refl (term393 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131418 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : ((term352 A _95218 _95219 _95220 _95221) = (term393 A _95219 _95221 _95218 _95220)) = ((term393 A _95219 _95221 _95218 _95220) = (term393 A _95219 _95221 _95218 _95220)).
Proof. exact (MK_COMB (@lem7131395 A _95219 _95221 _95218 _95220) (@lem7131417 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131420 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7131421 (x : Prop) : (x = x) = True.
Proof. exact (@lem7131420 Prop x). Qed.
Lemma lem7131422 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : ((term393 A _95219 _95221 _95218 _95220) = (term393 A _95219 _95221 _95218 _95220)) = True.
Proof. exact (@lem7131421 (term393 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131423 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : ((term352 A _95218 _95219 _95220 _95221) = (term393 A _95219 _95221 _95218 _95220)) = True.
Proof. exact (TRANS (@lem7131418 A _95219 _95221 _95218 _95220) (@lem7131422 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131424 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : True = ((term352 A _95218 _95219 _95220 _95221) = (term393 A _95219 _95221 _95218 _95220)).
Proof. exact (SYM (@lem7131423 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131425 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term352 A _95218 _95219 _95220 _95221) = (term393 A _95219 _95221 _95218 _95220).
Proof. exact (EQ_MP (@lem7131424 A _95219 _95221 _95218 _95220) (@lem0)). Qed.
Lemma lem7131426 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : term393 A _95219 _95221 _95218 _95220.
Proof. exact (EQ_MP (@lem7131425 A _95219 _95221 _95218 _95220) (@lem7131121 A _95218 _95219 _95220 _95221)). Qed.
Lemma lem7131428 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7131429 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : (term393 A _95219 _95221 _95218 _95220) = (term397 A _95218 _95219 _95220 _95221).
Proof. exact (@lem7131428 (term398 A _95219 _95221 _95218 _95220) ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221))). Qed.
Lemma lem7131431 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7131432 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term399 A _95219 _95221 _95218 _95220) = (term400 A _95219 _95221 _95218 _95220).
Proof. exact (@lem7131431 (term394 A _95219 _95221) (term390 A _95218 _95220)). Qed.
Lemma lem7131434 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131435 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) : (term401 A _95219 _95221) = (_95219 = _95221).
Proof. exact (@lem7131434 (_95219 = _95221)). Qed.
Lemma lem7131436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7131437 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) : (term402 A _95219 _95221) = (term403 A _95219 _95221).
Proof. exact (MK_COMB (@lem7131436) (@lem7131435 A _95219 _95221)). Qed.
Lemma lem7131439 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131440 {A : Type'} (_95218 : type717 A) (_95220 : type717 A) : (term404 A _95218 _95220) = (_95218 = _95220).
Proof. exact (@lem7131439 (_95218 = _95220)). Qed.
Lemma lem7131441 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term400 A _95219 _95221 _95218 _95220) = (term405 A _95219 _95221 _95218 _95220).
Proof. exact (MK_COMB (@lem7131437 A _95219 _95221) (@lem7131440 A _95218 _95220)). Qed.
Lemma lem7131442 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term399 A _95219 _95221 _95218 _95220) = (term405 A _95219 _95221 _95218 _95220).
Proof. exact (TRANS (@lem7131432 A _95219 _95221 _95218 _95220) (@lem7131441 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7131444 {A : Type'} (_95219 : A -> real) (_95221 : A -> real) (_95218 : type717 A) (_95220 : type717 A) : (term406 A _95219 _95221 _95218 _95220) = (term407 A _95219 _95221 _95218 _95220).
Proof. exact (MK_COMB (@lem7131443) (@lem7131442 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131445 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221)) = ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221)).
Proof. exact (eq_refl ((@I ((A -> real) -> real) _95218 _95219) = (@I ((A -> real) -> real) _95220 _95221))). Qed.
Lemma lem7131446 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : (term397 A _95218 _95219 _95220 _95221) = (term408 A _95218 _95219 _95220 _95221).
Proof. exact (MK_COMB (@lem7131444 A _95219 _95221 _95218 _95220) (@lem7131445 A _95218 _95219 _95220 _95221)). Qed.
Lemma lem7131447 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : (term393 A _95219 _95221 _95218 _95220) = (term408 A _95218 _95219 _95220 _95221).
Proof. exact (TRANS (@lem7131429 A _95218 _95219 _95220 _95221) (@lem7131446 A _95218 _95219 _95220 _95221)). Qed.
Lemma lem7131449 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term12 A) : term409 A f u v.
Proof. exact (conj (@lem7131192 A f) (@lem7131336 A u v h1)). Qed.
Lemma lem7131451 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : term408 A _95218 _95219 _95220 _95221.
Proof. exact (EQ_MP (@lem7131447 A _95218 _95219 _95220 _95221) (@lem7131426 A _95219 _95221 _95218 _95220)). Qed.
Lemma lem7131452 {A : Type'} (_95218 : type717 A) (_95219 : A -> real) (_95220 : type717 A) (_95221 : A -> real) : term408 A _95218 _95219 _95220 _95221.
Proof. exact (@lem7131451 A _95218 _95219 _95220 _95221). Qed.
Lemma lem7131453 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term410 A u v f.
Proof. exact (@lem7131452 A (term237 A v u) f (term237 A u v) f). Qed.
Lemma lem7131456 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) : (term239 A v u f) = (term239 A u v f).
Proof. exact (@lem7131453 A u v f (@lem7131449 A f u v h1)). Qed.
Lemma lem7131457 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) : (term239 A v u f) = (term239 A u v f).
Proof. exact (@lem7131456 A u v f h1). Qed.
Lemma lem7131458 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) : term411 A u v f.
Proof. exact (fun h0 : term412 A u v f => @lem7131457 A u v f h1). Qed.
Lemma lem7131460 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131461 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term411 A u v f) = ((term239 A v u f) = (term239 A u v f)).
Proof. exact (@lem7131460 ((term239 A v u f) = (term239 A u v f))). Qed.
Lemma lem7131462 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) : (term239 A v u f) = (term239 A u v f).
Proof. exact (EQ_MP (@lem7131461 A u v f) (@lem7131458 A u v f h1)). Qed.
Lemma lem7131464 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem7130795 A u v f h1)). Qed.
Lemma lem7131465 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term413 A v.
Proof. exact (fun h0 : term276 A v => @lem7131464 A u v f h1). Qed.
Lemma lem7131467 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131468 {A : Type'} (v : A -> Prop) : (term413 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem7131467 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem7131469 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem7131468 A v) (@lem7131465 A u v f h1)). Qed.
Lemma lem7131471 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem7130795 A u v f h1)). Qed.
Lemma lem7131472 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term413 A v.
Proof. exact (fun h0 : term276 A v => @lem7131471 A u v f h1). Qed.
Lemma lem7131474 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131475 {A : Type'} (v : A -> Prop) : (term413 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem7131474 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem7131476 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem7131475 A v) (@lem7131472 A u v f h1)). Qed.
Lemma lem7131479 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term414 A u v f.
Proof. exact (h1). Qed.
Lemma lem7131480 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term415 A u v f.
Proof. exact (fun h0 : (term239 A v u f) = (term240 A v f) => @lem7131479 A u v f h1). Qed.
Lemma lem7131482 (p : Prop) : (term416 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7131483 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term415 A u v f) = (term414 A u v f).
Proof. exact (@lem7131482 ((term239 A v u f) = (term240 A v f))). Qed.
Lemma lem7131484 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term414 A u v f.
Proof. exact (EQ_MP (@lem7131483 A u v f) (@lem7131480 A u v f h1)). Qed.
Lemma lem7131490 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131491 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term342 A x _95180 _95179 _95178) = (term417 A x _95180 _95179 _95178).
Proof. exact (@lem7131490 (term267 A x _95178 _95179 _95180) (term276 A _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7131505 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131506 {A : Type'} (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term418 A _95180 _95179 _95178) = (term419 A _95180 _95178 _95179).
Proof. exact (@lem7131505 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term276 A _95179)). Qed.
Lemma lem7131514 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term420 A x _95178 _95179 _95180) = (term420 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term420 A x _95178 _95179 _95180)). Qed.
Lemma lem7131515 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term421 A x _95180 _95178 _95179).
Proof. exact (MK_COMB (@lem7131514 A x _95178 _95179 _95180) (@lem7131506 A _95180 _95178 _95179)). Qed.
Lemma lem7131519 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131520 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term421 A x _95180 _95178 _95179) = (term422 A x _95178 _95180 _95179).
Proof. exact (@lem7131519 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term267 A x _95178 _95179 _95180) (term276 A _95179)). Qed.
Lemma lem7131538 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term422 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131515 A x _95180 _95178 _95179) (@lem7131520 A x _95178 _95180 _95179)). Qed.
Lemma lem7131539 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term342 A x _95180 _95179 _95178) = (term422 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131491 A x _95180 _95179 _95178) (@lem7131538 A x _95178 _95180 _95179)). Qed.
Lemma lem7131540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131541 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term423 A x _95180 _95179 _95178) = (term424 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7131540) (@lem7131539 A x _95178 _95180 _95179)). Qed.
Lemma lem7131555 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131556 {A : Type'} (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term418 A _95180 _95179 _95178) = (term419 A _95180 _95178 _95179).
Proof. exact (@lem7131555 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term276 A _95179)). Qed.
Lemma lem7131564 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term420 A x _95178 _95179 _95180) = (term420 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term420 A x _95178 _95179 _95180)). Qed.
Lemma lem7131565 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term421 A x _95180 _95178 _95179).
Proof. exact (MK_COMB (@lem7131564 A x _95178 _95179 _95180) (@lem7131556 A _95180 _95178 _95179)). Qed.
Lemma lem7131569 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131570 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term421 A x _95180 _95178 _95179) = (term422 A x _95178 _95180 _95179).
Proof. exact (@lem7131569 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term267 A x _95178 _95179 _95180) (term276 A _95179)). Qed.
Lemma lem7131588 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term422 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131565 A x _95180 _95178 _95179) (@lem7131570 A x _95178 _95180 _95179)). Qed.
Lemma lem7131589 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term342 A x _95180 _95179 _95178) = (term417 A x _95180 _95179 _95178)) = ((term422 A x _95178 _95180 _95179) = (term422 A x _95178 _95180 _95179)).
Proof. exact (MK_COMB (@lem7131541 A x _95178 _95180 _95179) (@lem7131588 A x _95178 _95180 _95179)). Qed.
Lemma lem7131591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7131592 (x : Prop) : (x = x) = True.
Proof. exact (@lem7131591 Prop x). Qed.
Lemma lem7131593 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term422 A x _95178 _95180 _95179) = (term422 A x _95178 _95180 _95179)) = True.
Proof. exact (@lem7131592 (term422 A x _95178 _95180 _95179)). Qed.
Lemma lem7131594 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : ((term342 A x _95180 _95179 _95178) = (term417 A x _95180 _95179 _95178)) = True.
Proof. exact (TRANS (@lem7131589 A x _95178 _95180 _95179) (@lem7131593 A x _95178 _95180 _95179)). Qed.
Lemma lem7131595 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : True = ((term342 A x _95180 _95179 _95178) = (term417 A x _95180 _95179 _95178)).
Proof. exact (SYM (@lem7131594 A x _95180 _95179 _95178)). Qed.
Lemma lem7131596 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term342 A x _95180 _95179 _95178) = (term417 A x _95180 _95179 _95178).
Proof. exact (EQ_MP (@lem7131595 A x _95180 _95179 _95178) (@lem0)). Qed.
Lemma lem7131597 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term417 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7131596 A x _95180 _95179 _95178) (@lem7130955 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7131599 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7131600 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term425 A x _95178 _95179 _95180).
Proof. exact (@lem7131599 (term418 A _95180 _95179 _95178) (term267 A x _95178 _95179 _95180)). Qed.
Lemma lem7131602 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7131603 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term426 A _95180 _95179 _95178) = (term427 A _95180 _95179 _95178).
Proof. exact (@lem7131602 (term276 A _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7131605 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131606 {A : Type'} (_95179 : A -> Prop) : (term428 A _95179) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95179).
Proof. exact (@lem7131605 (@I ((A -> Prop) -> Prop) (@FINITE A) _95179)). Qed.
Lemma lem7131607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7131608 {A : Type'} (_95179 : A -> Prop) : (term429 A _95179) = (term304 A _95179).
Proof. exact (MK_COMB (@lem7131607) (@lem7131606 A _95179)). Qed.
Lemma lem7131609 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term414 A _95180 _95179 _95178) = (term414 A _95180 _95179 _95178).
Proof. exact (eq_refl (term414 A _95180 _95179 _95178)). Qed.
Lemma lem7131610 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term427 A _95180 _95179 _95178) = (term430 A _95180 _95179 _95178).
Proof. exact (MK_COMB (@lem7131608 A _95179) (@lem7131609 A _95180 _95179 _95178)). Qed.
Lemma lem7131611 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term426 A _95180 _95179 _95178) = (term430 A _95180 _95179 _95178).
Proof. exact (TRANS (@lem7131603 A _95180 _95179 _95178) (@lem7131610 A _95180 _95179 _95178)). Qed.
Lemma lem7131612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7131613 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term431 A _95180 _95179 _95178) = (term432 A _95180 _95179 _95178).
Proof. exact (MK_COMB (@lem7131612) (@lem7131611 A _95180 _95179 _95178)). Qed.
Lemma lem7131614 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term267 A x _95178 _95179 _95180) = (term267 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term267 A x _95178 _95179 _95180)). Qed.
Lemma lem7131615 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term425 A x _95178 _95179 _95180) = (term433 A x _95178 _95179 _95180).
Proof. exact (MK_COMB (@lem7131613 A _95180 _95179 _95178) (@lem7131614 A x _95178 _95179 _95180)). Qed.
Lemma lem7131616 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term417 A x _95180 _95179 _95178) = (term433 A x _95178 _95179 _95180).
Proof. exact (TRANS (@lem7131600 A x _95178 _95179 _95180) (@lem7131615 A x _95178 _95179 _95180)). Qed.
Lemma lem7131618 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) (h2 : term65 A u v f) : term430 A u v f.
Proof. exact (conj (@lem7131476 A u v f h2) (@lem7131484 A u v f h1)). Qed.
Lemma lem7131620 {A : Type'} (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term433 A x _95178 _95179 _95180.
Proof. exact (EQ_MP (@lem7131616 A x _95178 _95179 _95180) (@lem7131597 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7131621 {A : Type'} (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term433 A x _95178 _95179 _95180.
Proof. exact (@lem7131620 A _95178 _95179 _95180 x h1). Qed.
Lemma lem7131622 {A : Type'} (f : A -> real) (v : A -> Prop) (u : A -> Prop) (x : type709 A) (h1 : term223 A x) : term433 A x f v u.
Proof. exact (@lem7131621 A f v u x h1). Qed.
Lemma lem7131625 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term267 A x f v u.
Proof. exact (@lem7131622 A f v u x h1 (@lem7131618 A u v f h2 h3)). Qed.
Lemma lem7131626 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term434 A x f v u.
Proof. exact (fun h0 : term435 A x f v u => @lem7131625 A x u v f h1 h2 h3). Qed.
Lemma lem7131628 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131629 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term434 A x f v u) = (term267 A x f v u).
Proof. exact (@lem7131628 (term267 A x f v u)). Qed.
Lemma lem7131630 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term267 A x f v u.
Proof. exact (EQ_MP (@lem7131629 A x f v u) (@lem7131626 A x u v f h1 h2 h3)). Qed.
Lemma lem7131632 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (proj1 (@lem7130795 A u v f h1)). Qed.
Lemma lem7131633 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term413 A v.
Proof. exact (fun h0 : term276 A v => @lem7131632 A u v f h1). Qed.
Lemma lem7131635 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131636 {A : Type'} (v : A -> Prop) : (term413 A v) = (@I ((A -> Prop) -> Prop) (@FINITE A) v).
Proof. exact (@lem7131635 (@I ((A -> Prop) -> Prop) (@FINITE A) v)). Qed.
Lemma lem7131637 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : @I ((A -> Prop) -> Prop) (@FINITE A) v.
Proof. exact (EQ_MP (@lem7131636 A v) (@lem7131633 A u v f h1)). Qed.
Lemma lem7131640 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term414 A u v f.
Proof. exact (h1). Qed.
Lemma lem7131641 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term415 A u v f.
Proof. exact (fun h0 : (term239 A v u f) = (term240 A v f) => @lem7131640 A u v f h1). Qed.
Lemma lem7131643 (p : Prop) : (term416 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7131644 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term415 A u v f) = (term414 A u v f).
Proof. exact (@lem7131643 ((term239 A v u f) = (term240 A v f))). Qed.
Lemma lem7131645 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) : term414 A u v f.
Proof. exact (EQ_MP (@lem7131644 A u v f) (@lem7131641 A u v f h1)). Qed.
Lemma lem7131651 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131652 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term341 A x _95180 _95179 _95178) = (term436 A x _95180 _95179 _95178).
Proof. exact (@lem7131651 (term254 A x _95178 _95179 _95180) (term276 A _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7131668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131669 {A : Type'} (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term418 A _95180 _95179 _95178) = (term419 A _95180 _95178 _95179).
Proof. exact (@lem7131668 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term276 A _95179)). Qed.
Lemma lem7131677 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term437 A x _95178 _95179 _95180) = (term437 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term437 A x _95178 _95179 _95180)). Qed.
Lemma lem7131678 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term438 A x _95180 _95178 _95179).
Proof. exact (MK_COMB (@lem7131677 A x _95178 _95179 _95180) (@lem7131669 A _95180 _95178 _95179)). Qed.
Lemma lem7131682 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131683 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term438 A x _95180 _95178 _95179) = (term439 A x _95178 _95180 _95179).
Proof. exact (@lem7131682 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term254 A x _95178 _95179 _95180) (term276 A _95179)). Qed.
Lemma lem7131703 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term439 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131678 A x _95180 _95178 _95179) (@lem7131683 A x _95178 _95180 _95179)). Qed.
Lemma lem7131704 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term341 A x _95180 _95179 _95178) = (term439 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131652 A x _95180 _95179 _95178) (@lem7131703 A x _95178 _95180 _95179)). Qed.
Lemma lem7131705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131706 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term440 A x _95180 _95179 _95178) = (term441 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7131705) (@lem7131704 A x _95178 _95180 _95179)). Qed.
Lemma lem7131722 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131723 {A : Type'} (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term418 A _95180 _95179 _95178) = (term419 A _95180 _95178 _95179).
Proof. exact (@lem7131722 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term276 A _95179)). Qed.
Lemma lem7131731 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term437 A x _95178 _95179 _95180) = (term437 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term437 A x _95178 _95179 _95180)). Qed.
Lemma lem7131732 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95178 : A -> real) (_95179 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term438 A x _95180 _95178 _95179).
Proof. exact (MK_COMB (@lem7131731 A x _95178 _95179 _95180) (@lem7131723 A _95180 _95178 _95179)). Qed.
Lemma lem7131736 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131737 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term438 A x _95180 _95178 _95179) = (term439 A x _95178 _95180 _95179).
Proof. exact (@lem7131736 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term254 A x _95178 _95179 _95180) (term276 A _95179)). Qed.
Lemma lem7131757 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term439 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131732 A x _95180 _95178 _95179) (@lem7131737 A x _95178 _95180 _95179)). Qed.
Lemma lem7131758 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term341 A x _95180 _95179 _95178) = (term436 A x _95180 _95179 _95178)) = ((term439 A x _95178 _95180 _95179) = (term439 A x _95178 _95180 _95179)).
Proof. exact (MK_COMB (@lem7131706 A x _95178 _95180 _95179) (@lem7131757 A x _95178 _95180 _95179)). Qed.
Lemma lem7131760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7131761 (x : Prop) : (x = x) = True.
Proof. exact (@lem7131760 Prop x). Qed.
Lemma lem7131762 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term439 A x _95178 _95180 _95179) = (term439 A x _95178 _95180 _95179)) = True.
Proof. exact (@lem7131761 (term439 A x _95178 _95180 _95179)). Qed.
Lemma lem7131763 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : ((term341 A x _95180 _95179 _95178) = (term436 A x _95180 _95179 _95178)) = True.
Proof. exact (TRANS (@lem7131758 A x _95178 _95180 _95179) (@lem7131762 A x _95178 _95180 _95179)). Qed.
Lemma lem7131764 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : True = ((term341 A x _95180 _95179 _95178) = (term436 A x _95180 _95179 _95178)).
Proof. exact (SYM (@lem7131763 A x _95180 _95179 _95178)). Qed.
Lemma lem7131765 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term341 A x _95180 _95179 _95178) = (term436 A x _95180 _95179 _95178).
Proof. exact (EQ_MP (@lem7131764 A x _95180 _95179 _95178) (@lem0)). Qed.
Lemma lem7131766 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term436 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7131765 A x _95180 _95179 _95178) (@lem7130943 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7131768 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7131769 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term442 A x _95178 _95179 _95180).
Proof. exact (@lem7131768 (term418 A _95180 _95179 _95178) (term254 A x _95178 _95179 _95180)). Qed.
Lemma lem7131771 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7131772 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term426 A _95180 _95179 _95178) = (term427 A _95180 _95179 _95178).
Proof. exact (@lem7131771 (term276 A _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7131774 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131775 {A : Type'} (_95179 : A -> Prop) : (term428 A _95179) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95179).
Proof. exact (@lem7131774 (@I ((A -> Prop) -> Prop) (@FINITE A) _95179)). Qed.
Lemma lem7131776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7131777 {A : Type'} (_95179 : A -> Prop) : (term429 A _95179) = (term304 A _95179).
Proof. exact (MK_COMB (@lem7131776) (@lem7131775 A _95179)). Qed.
Lemma lem7131778 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term414 A _95180 _95179 _95178) = (term414 A _95180 _95179 _95178).
Proof. exact (eq_refl (term414 A _95180 _95179 _95178)). Qed.
Lemma lem7131779 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term427 A _95180 _95179 _95178) = (term430 A _95180 _95179 _95178).
Proof. exact (MK_COMB (@lem7131777 A _95179) (@lem7131778 A _95180 _95179 _95178)). Qed.
Lemma lem7131780 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term426 A _95180 _95179 _95178) = (term430 A _95180 _95179 _95178).
Proof. exact (TRANS (@lem7131772 A _95180 _95179 _95178) (@lem7131779 A _95180 _95179 _95178)). Qed.
Lemma lem7131781 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7131782 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term431 A _95180 _95179 _95178) = (term432 A _95180 _95179 _95178).
Proof. exact (MK_COMB (@lem7131781) (@lem7131780 A _95180 _95179 _95178)). Qed.
Lemma lem7131783 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term254 A x _95178 _95179 _95180) = (term254 A x _95178 _95179 _95180).
Proof. exact (eq_refl (term254 A x _95178 _95179 _95180)). Qed.
Lemma lem7131784 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term442 A x _95178 _95179 _95180) = (term443 A x _95178 _95179 _95180).
Proof. exact (MK_COMB (@lem7131782 A _95180 _95179 _95178) (@lem7131783 A x _95178 _95179 _95180)). Qed.
Lemma lem7131785 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) : (term436 A x _95180 _95179 _95178) = (term443 A x _95178 _95179 _95180).
Proof. exact (TRANS (@lem7131769 A x _95178 _95179 _95180) (@lem7131784 A x _95178 _95179 _95180)). Qed.
Lemma lem7131787 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term414 A u v f) (h2 : term65 A u v f) : term430 A u v f.
Proof. exact (conj (@lem7131637 A u v f h2) (@lem7131645 A u v f h1)). Qed.
Lemma lem7131789 {A : Type'} (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term443 A x _95178 _95179 _95180.
Proof. exact (EQ_MP (@lem7131785 A x _95178 _95179 _95180) (@lem7131766 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7131790 {A : Type'} (_95178 : A -> real) (_95179 : A -> Prop) (_95180 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term443 A x _95178 _95179 _95180.
Proof. exact (@lem7131789 A _95178 _95179 _95180 x h1). Qed.
Lemma lem7131791 {A : Type'} (f : A -> real) (v : A -> Prop) (u : A -> Prop) (x : type709 A) (h1 : term223 A x) : term443 A x f v u.
Proof. exact (@lem7131790 A f v u x h1). Qed.
Lemma lem7131794 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term254 A x f v u.
Proof. exact (@lem7131791 A f v u x h1 (@lem7131787 A u v f h2 h3)). Qed.
Lemma lem7131795 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term444 A x f v u.
Proof. exact (fun h0 : (term248 A x f v u) = term250 => @lem7131794 A x u v f h1 h2 h3). Qed.
Lemma lem7131797 (p : Prop) : (term416 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7131798 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term444 A x f v u) = (term254 A x f v u).
Proof. exact (@lem7131797 ((term248 A x f v u) = term250)). Qed.
Lemma lem7131799 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term254 A x f v u.
Proof. exact (EQ_MP (@lem7131798 A x f v u) (@lem7131795 A x u v f h1 h2 h3)). Qed.
Lemma lem7131805 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131806 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95181 : A) : (term340 A u v f _95181) = (term445 A v u f _95181).
Proof. exact (@lem7131805 (term296 A _95181 v) (term297 A _95181 u) ((@I (A -> real) f _95181) = term250)). Qed.
Lemma lem7131820 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131821 {A : Type'} (f : A -> real) (_95181 : A) (u : A -> Prop) : (term446 A u f _95181) = (term447 A f _95181 u).
Proof. exact (@lem7131820 ((@I (A -> real) f _95181) = term250) (term297 A _95181 u)). Qed.
Lemma lem7131829 {A : Type'} (_95181 : A) (v : A -> Prop) : (term448 A _95181 v) = (term448 A _95181 v).
Proof. exact (eq_refl (term448 A _95181 v)). Qed.
Lemma lem7131830 {A : Type'} (v : A -> Prop) (f : A -> real) (_95181 : A) (u : A -> Prop) : (term445 A v u f _95181) = (term449 A v f _95181 u).
Proof. exact (MK_COMB (@lem7131829 A _95181 v) (@lem7131821 A f _95181 u)). Qed.
Lemma lem7131834 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131835 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term449 A v f _95181 u) = (term450 A f v _95181 u).
Proof. exact (@lem7131834 ((@I (A -> real) f _95181) = term250) (term296 A _95181 v) (term297 A _95181 u)). Qed.
Lemma lem7131853 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term445 A v u f _95181) = (term450 A f v _95181 u).
Proof. exact (TRANS (@lem7131830 A v f _95181 u) (@lem7131835 A f v _95181 u)). Qed.
Lemma lem7131854 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term340 A u v f _95181) = (term450 A f v _95181 u).
Proof. exact (TRANS (@lem7131806 A v u f _95181) (@lem7131853 A f v _95181 u)). Qed.
Lemma lem7131855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131856 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term451 A u v f _95181) = (term452 A f v _95181 u).
Proof. exact (MK_COMB (@lem7131855) (@lem7131854 A f v _95181 u)). Qed.
Lemma lem7131870 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131871 {A : Type'} (f : A -> real) (_95181 : A) (u : A -> Prop) : (term446 A u f _95181) = (term447 A f _95181 u).
Proof. exact (@lem7131870 ((@I (A -> real) f _95181) = term250) (term297 A _95181 u)). Qed.
Lemma lem7131879 {A : Type'} (_95181 : A) (v : A -> Prop) : (term448 A _95181 v) = (term448 A _95181 v).
Proof. exact (eq_refl (term448 A _95181 v)). Qed.
Lemma lem7131880 {A : Type'} (v : A -> Prop) (f : A -> real) (_95181 : A) (u : A -> Prop) : (term445 A v u f _95181) = (term449 A v f _95181 u).
Proof. exact (MK_COMB (@lem7131879 A _95181 v) (@lem7131871 A f _95181 u)). Qed.
Lemma lem7131884 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131885 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term449 A v f _95181 u) = (term450 A f v _95181 u).
Proof. exact (@lem7131884 ((@I (A -> real) f _95181) = term250) (term296 A _95181 v) (term297 A _95181 u)). Qed.
Lemma lem7131903 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : (term445 A v u f _95181) = (term450 A f v _95181 u).
Proof. exact (TRANS (@lem7131880 A v f _95181 u) (@lem7131885 A f v _95181 u)). Qed.
Lemma lem7131904 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : ((term340 A u v f _95181) = (term445 A v u f _95181)) = ((term450 A f v _95181 u) = (term450 A f v _95181 u)).
Proof. exact (MK_COMB (@lem7131856 A f v _95181 u) (@lem7131903 A f v _95181 u)). Qed.
Lemma lem7131906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7131907 (x : Prop) : (x = x) = True.
Proof. exact (@lem7131906 Prop x). Qed.
Lemma lem7131908 {A : Type'} (f : A -> real) (v : A -> Prop) (_95181 : A) (u : A -> Prop) : ((term450 A f v _95181 u) = (term450 A f v _95181 u)) = True.
Proof. exact (@lem7131907 (term450 A f v _95181 u)). Qed.
Lemma lem7131909 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95181 : A) : ((term340 A u v f _95181) = (term445 A v u f _95181)) = True.
Proof. exact (TRANS (@lem7131904 A f v _95181 u) (@lem7131908 A f v _95181 u)). Qed.
Lemma lem7131910 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95181 : A) : True = ((term340 A u v f _95181) = (term445 A v u f _95181)).
Proof. exact (SYM (@lem7131909 A v u f _95181)). Qed.
Lemma lem7131911 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (_95181 : A) : (term340 A u v f _95181) = (term445 A v u f _95181).
Proof. exact (EQ_MP (@lem7131910 A v u f _95181) (@lem0)). Qed.
Lemma lem7131912 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term445 A v u f _95181.
Proof. exact (EQ_MP (@lem7131911 A v u f _95181) (@lem7130931 A _95181 u v f h1)). Qed.
Lemma lem7131914 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7131915 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) (v : A -> Prop) : (term445 A v u f _95181) = (term453 A u f _95181 v).
Proof. exact (@lem7131914 (term446 A u f _95181) (term296 A _95181 v)). Qed.
Lemma lem7131917 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7131918 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) : (term454 A u f _95181) = (term455 A u f _95181).
Proof. exact (@lem7131917 (term297 A _95181 u) ((@I (A -> real) f _95181) = term250)). Qed.
Lemma lem7131920 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7131921 {A : Type'} (_95181 : A) (u : A -> Prop) : (term456 A _95181 u) = (term296 A _95181 u).
Proof. exact (@lem7131920 (term296 A _95181 u)). Qed.
Lemma lem7131922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7131923 {A : Type'} (_95181 : A) (u : A -> Prop) : (term457 A _95181 u) = (term458 A _95181 u).
Proof. exact (MK_COMB (@lem7131922) (@lem7131921 A _95181 u)). Qed.
Lemma lem7131924 {A : Type'} (f : A -> real) (_95181 : A) : (term459 A f _95181) = (term459 A f _95181).
Proof. exact (eq_refl (term459 A f _95181)). Qed.
Lemma lem7131925 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) : (term455 A u f _95181) = (term460 A u f _95181).
Proof. exact (MK_COMB (@lem7131923 A _95181 u) (@lem7131924 A f _95181)). Qed.
Lemma lem7131926 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) : (term454 A u f _95181) = (term460 A u f _95181).
Proof. exact (TRANS (@lem7131918 A u f _95181) (@lem7131925 A u f _95181)). Qed.
Lemma lem7131927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7131928 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) : (term461 A u f _95181) = (term462 A u f _95181).
Proof. exact (MK_COMB (@lem7131927) (@lem7131926 A u f _95181)). Qed.
Lemma lem7131929 {A : Type'} (_95181 : A) (v : A -> Prop) : (term296 A _95181 v) = (term296 A _95181 v).
Proof. exact (eq_refl (term296 A _95181 v)). Qed.
Lemma lem7131930 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) (v : A -> Prop) : (term453 A u f _95181 v) = (term463 A u f _95181 v).
Proof. exact (MK_COMB (@lem7131928 A u f _95181) (@lem7131929 A _95181 v)). Qed.
Lemma lem7131931 {A : Type'} (u : A -> Prop) (f : A -> real) (_95181 : A) (v : A -> Prop) : (term445 A v u f _95181) = (term463 A u f _95181 v).
Proof. exact (TRANS (@lem7131915 A u f _95181 v) (@lem7131930 A u f _95181 v)). Qed.
Lemma lem7131933 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term464 A x f v u.
Proof. exact (conj (@lem7131630 A x u v f h1 h2 h3) (@lem7131799 A x u v f h1 h2 h3)). Qed.
Lemma lem7131935 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term463 A u f _95181 v.
Proof. exact (EQ_MP (@lem7131931 A u f _95181 v) (@lem7131912 A _95181 u v f h1)). Qed.
Lemma lem7131936 {A : Type'} (_95181 : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term463 A u f _95181 v.
Proof. exact (@lem7131935 A _95181 u v f h1). Qed.
Lemma lem7131937 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term465 A x f u v.
Proof. exact (@lem7131936 A (term245 A x f v u) u v f h1). Qed.
Lemma lem7131940 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term261 A x f u v.
Proof. exact (@lem7131937 A x u v f h3 (@lem7131933 A x u v f h1 h2 h3)). Qed.
Lemma lem7131941 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term466 A x f u v.
Proof. exact (fun h0 : term263 A x f u v => @lem7131940 A x u v f h1 h2 h3). Qed.
Lemma lem7131943 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7131944 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term466 A x f u v) = (term261 A x f u v).
Proof. exact (@lem7131943 (term261 A x f u v)). Qed.
Lemma lem7131945 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term261 A x f u v.
Proof. exact (EQ_MP (@lem7131944 A x f u v) (@lem7131941 A x u v f h1 h2 h3)). Qed.
Lemma lem7131961 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7131962 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term467 A x _95180 _95179 _95178) = (term468 A x _95178 _95180 _95179).
Proof. exact (@lem7131961 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term263 A x _95178 _95180 _95179)). Qed.
Lemma lem7131970 {A : Type'} (_95179 : A -> Prop) : (term277 A _95179) = (term277 A _95179).
Proof. exact (eq_refl (term277 A _95179)). Qed.
Lemma lem7131971 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term343 A x _95180 _95179 _95178) = (term469 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7131970 A _95179) (@lem7131962 A x _95178 _95180 _95179)). Qed.
Lemma lem7131975 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7131976 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term469 A x _95178 _95180 _95179) = (term470 A x _95178 _95180 _95179).
Proof. exact (@lem7131975 ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) (term276 A _95179) (term263 A x _95178 _95180 _95179)). Qed.
Lemma lem7131994 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term343 A x _95180 _95179 _95178) = (term470 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7131971 A x _95178 _95180 _95179) (@lem7131976 A x _95178 _95180 _95179)). Qed.
Lemma lem7131995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7131996 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term471 A x _95180 _95179 _95178) = (term472 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7131995) (@lem7131994 A x _95178 _95180 _95179)). Qed.
Lemma lem7132014 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term470 A x _95178 _95180 _95179) = (term470 A x _95178 _95180 _95179).
Proof. exact (eq_refl (term470 A x _95178 _95180 _95179)). Qed.
Lemma lem7132015 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term343 A x _95180 _95179 _95178) = (term470 A x _95178 _95180 _95179)) = ((term470 A x _95178 _95180 _95179) = (term470 A x _95178 _95180 _95179)).
Proof. exact (MK_COMB (@lem7131996 A x _95178 _95180 _95179) (@lem7132014 A x _95178 _95180 _95179)). Qed.
Lemma lem7132017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7132018 (x : Prop) : (x = x) = True.
Proof. exact (@lem7132017 Prop x). Qed.
Lemma lem7132019 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term470 A x _95178 _95180 _95179) = (term470 A x _95178 _95180 _95179)) = True.
Proof. exact (@lem7132018 (term470 A x _95178 _95180 _95179)). Qed.
Lemma lem7132020 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : ((term343 A x _95180 _95179 _95178) = (term470 A x _95178 _95180 _95179)) = True.
Proof. exact (TRANS (@lem7132015 A x _95178 _95180 _95179) (@lem7132019 A x _95178 _95180 _95179)). Qed.
Lemma lem7132021 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : True = ((term343 A x _95180 _95179 _95178) = (term470 A x _95178 _95180 _95179)).
Proof. exact (SYM (@lem7132020 A x _95178 _95180 _95179)). Qed.
Lemma lem7132022 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term343 A x _95180 _95179 _95178) = (term470 A x _95178 _95180 _95179).
Proof. exact (EQ_MP (@lem7132021 A x _95178 _95180 _95179) (@lem0)). Qed.
Lemma lem7132023 {A : Type'} (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) (x : type709 A) (h1 : term223 A x) : term470 A x _95178 _95180 _95179.
Proof. exact (EQ_MP (@lem7132022 A x _95178 _95180 _95179) (@lem7130967 A _95180 _95179 _95178 x h1)). Qed.
Lemma lem7132025 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7132026 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term470 A x _95178 _95180 _95179) = (term473 A x _95180 _95179 _95178).
Proof. exact (@lem7132025 (term322 A x _95178 _95180 _95179) ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7132028 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7132029 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term474 A x _95178 _95180 _95179) = (term475 A x _95178 _95180 _95179).
Proof. exact (@lem7132028 (term276 A _95179) (term263 A x _95178 _95180 _95179)). Qed.
Lemma lem7132031 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7132032 {A : Type'} (_95179 : A -> Prop) : (term428 A _95179) = (@I ((A -> Prop) -> Prop) (@FINITE A) _95179).
Proof. exact (@lem7132031 (@I ((A -> Prop) -> Prop) (@FINITE A) _95179)). Qed.
Lemma lem7132033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7132034 {A : Type'} (_95179 : A -> Prop) : (term429 A _95179) = (term304 A _95179).
Proof. exact (MK_COMB (@lem7132033) (@lem7132032 A _95179)). Qed.
Lemma lem7132036 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7132037 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term476 A x _95178 _95180 _95179) = (term261 A x _95178 _95180 _95179).
Proof. exact (@lem7132036 (term261 A x _95178 _95180 _95179)). Qed.
Lemma lem7132038 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term475 A x _95178 _95180 _95179) = (term477 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7132034 A _95179) (@lem7132037 A x _95178 _95180 _95179)). Qed.
Lemma lem7132039 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term474 A x _95178 _95180 _95179) = (term477 A x _95178 _95180 _95179).
Proof. exact (TRANS (@lem7132029 A x _95178 _95180 _95179) (@lem7132038 A x _95178 _95180 _95179)). Qed.
Lemma lem7132040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132041 {A : Type'} (x : type709 A) (_95178 : A -> real) (_95180 : A -> Prop) (_95179 : A -> Prop) : (term478 A x _95178 _95180 _95179) = (term479 A x _95178 _95180 _95179).
Proof. exact (MK_COMB (@lem7132040) (@lem7132039 A x _95178 _95180 _95179)). Qed.
Lemma lem7132042 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)) = ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178)).
Proof. exact (eq_refl ((term239 A _95179 _95180 _95178) = (term240 A _95179 _95178))). Qed.
Lemma lem7132043 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term473 A x _95180 _95179 _95178) = (term480 A x _95180 _95179 _95178).
Proof. exact (MK_COMB (@lem7132041 A x _95178 _95180 _95179) (@lem7132042 A _95180 _95179 _95178)). Qed.
Lemma lem7132044 {A : Type'} (x : type709 A) (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) : (term470 A x _95178 _95180 _95179) = (term480 A x _95180 _95179 _95178).
Proof. exact (TRANS (@lem7132026 A x _95180 _95179 _95178) (@lem7132043 A x _95180 _95179 _95178)). Qed.
Lemma lem7132046 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : term477 A x f u v.
Proof. exact (conj (@lem7131469 A u v f h3) (@lem7131945 A x u v f h1 h2 h3)). Qed.
Lemma lem7132048 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term480 A x _95180 _95179 _95178.
Proof. exact (EQ_MP (@lem7132044 A x _95180 _95179 _95178) (@lem7132023 A _95178 _95180 _95179 x h1)). Qed.
Lemma lem7132049 {A : Type'} (_95180 : A -> Prop) (_95179 : A -> Prop) (_95178 : A -> real) (x : type709 A) (h1 : term223 A x) : term480 A x _95180 _95179 _95178.
Proof. exact (@lem7132048 A _95180 _95179 _95178 x h1). Qed.
Lemma lem7132050 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : type709 A) (h1 : term223 A x) : term480 A x u v f.
Proof. exact (@lem7132049 A u v f x h1). Qed.
Lemma lem7132053 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term414 A u v f) (h3 : term65 A u v f) : (term239 A v u f) = (term240 A v f).
Proof. exact (@lem7132050 A u v f x h1 (@lem7132046 A x u v f h1 h2 h3)). Qed.
Lemma lem7132054 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term65 A u v f) : term481 A u v f.
Proof. exact (fun h0 : term414 A u v f => @lem7132053 A x u v f h1 h0 h2). Qed.
Lemma lem7132056 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7132057 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term481 A u v f) = ((term239 A v u f) = (term240 A v f)).
Proof. exact (@lem7132056 ((term239 A v u f) = (term240 A v f))). Qed.
Lemma lem7132058 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term223 A x) (h2 : term65 A u v f) : (term239 A v u f) = (term240 A v f).
Proof. exact (EQ_MP (@lem7132057 A u v f) (@lem7132054 A x u v f h1 h2)). Qed.
Lemma lem7132076 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7132077 (y : real) (x : real) (z : real) : (term482 x y z) = (term483 y x z).
Proof. exact (@lem7132076 (y = z) (term484 x z)). Qed.
Lemma lem7132087 (x : real) (y : real) : (term485 x y) = (term485 x y).
Proof. exact (eq_refl (term485 x y)). Qed.
Lemma lem7132088 (y : real) (x : real) (z : real) : (term353 x y z) = (term486 y x z).
Proof. exact (MK_COMB (@lem7132087 x y) (@lem7132077 y x z)). Qed.
Lemma lem7132092 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7132093 (y : real) (x : real) (z : real) : (term486 y x z) = (term487 y x z).
Proof. exact (@lem7132092 (y = z) (term484 x y) (term484 x z)). Qed.
Lemma lem7132115 (y : real) (x : real) (z : real) : (term353 x y z) = (term487 y x z).
Proof. exact (TRANS (@lem7132088 y x z) (@lem7132093 y x z)). Qed.
Lemma lem7132116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7132117 (y : real) (x : real) (z : real) : (term488 x y z) = (term489 y x z).
Proof. exact (MK_COMB (@lem7132116) (@lem7132115 y x z)). Qed.
Lemma lem7132139 (y : real) (x : real) (z : real) : (term487 y x z) = (term487 y x z).
Proof. exact (eq_refl (term487 y x z)). Qed.
Lemma lem7132140 (y : real) (x : real) (z : real) : ((term353 x y z) = (term487 y x z)) = ((term487 y x z) = (term487 y x z)).
Proof. exact (MK_COMB (@lem7132117 y x z) (@lem7132139 y x z)). Qed.
Lemma lem7132142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7132143 (x : Prop) : (x = x) = True.
Proof. exact (@lem7132142 Prop x). Qed.
Lemma lem7132144 (y : real) (x : real) (z : real) : ((term487 y x z) = (term487 y x z)) = True.
Proof. exact (@lem7132143 (term487 y x z)). Qed.
Lemma lem7132145 (y : real) (x : real) (z : real) : ((term353 x y z) = (term487 y x z)) = True.
Proof. exact (TRANS (@lem7132140 y x z) (@lem7132144 y x z)). Qed.
Lemma lem7132146 (y : real) (x : real) (z : real) : True = ((term353 x y z) = (term487 y x z)).
Proof. exact (SYM (@lem7132145 y x z)). Qed.
Lemma lem7132147 (y : real) (x : real) (z : real) : (term353 x y z) = (term487 y x z).
Proof. exact (EQ_MP (@lem7132146 y x z) (@lem0)). Qed.
Lemma lem7132148 (y : real) (x : real) (z : real) : term487 y x z.
Proof. exact (EQ_MP (@lem7132147 y x z) (@lem7131159 x y z)). Qed.
Lemma lem7132150 (b : Prop) (a : Prop) : (a \/ b) = (term369 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7132151 (x : real) (y : real) (z : real) : (term487 y x z) = (term490 x y z).
Proof. exact (@lem7132150 (term491 y x z) (y = z)). Qed.
Lemma lem7132153 (a : Prop) (b : Prop) : (term372 a b) = (term373 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7132154 (y : real) (x : real) (z : real) : (term492 y x z) = (term493 y x z).
Proof. exact (@lem7132153 (term484 x y) (term484 x z)). Qed.
Lemma lem7132156 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7132157 (x : real) (y : real) : (term494 x y) = (x = y).
Proof. exact (@lem7132156 (x = y)). Qed.
Lemma lem7132158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7132159 (x : real) (y : real) : (term495 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem7132158) (@lem7132157 x y)). Qed.
Lemma lem7132161 (a : Prop) : (term376 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7132162 (x : real) (z : real) : (term494 x z) = (x = z).
Proof. exact (@lem7132161 (x = z)). Qed.
Lemma lem7132163 (y : real) (x : real) (z : real) : (term493 y x z) = (term497 y x z).
Proof. exact (MK_COMB (@lem7132159 x y) (@lem7132162 x z)). Qed.
Lemma lem7132164 (y : real) (x : real) (z : real) : (term492 y x z) = (term497 y x z).
Proof. exact (TRANS (@lem7132154 y x z) (@lem7132163 y x z)). Qed.
Lemma lem7132165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7132166 (y : real) (x : real) (z : real) : (term498 y x z) = (term499 y x z).
Proof. exact (MK_COMB (@lem7132165) (@lem7132164 y x z)). Qed.
Lemma lem7132167 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7132168 (x : real) (y : real) (z : real) : (term490 x y z) = (term500 x y z).
Proof. exact (MK_COMB (@lem7132166 y x z) (@lem7132167 y z)). Qed.
Lemma lem7132169 (x : real) (y : real) (z : real) : (term487 y x z) = (term500 x y z).
Proof. exact (TRANS (@lem7132151 x y z) (@lem7132168 x y z)). Qed.
Lemma lem7132171 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : term501 A u v f.
Proof. exact (conj (@lem7131462 A u v f h1) (@lem7132058 A x u v f h2 h3)). Qed.
Lemma lem7132173 (x : real) (y : real) (z : real) : term500 x y z.
Proof. exact (EQ_MP (@lem7132169 x y z) (@lem7132148 y x z)). Qed.
Lemma lem7132174 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term502 A u v f.
Proof. exact (@lem7132173 (term239 A v u f) (term239 A u v f) (term240 A v f)). Qed.
Lemma lem7132177 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : (term239 A u v f) = (term240 A v f).
Proof. exact (@lem7132174 A u v f (@lem7132171 A x u v f h1 h2 h3)). Qed.
Lemma lem7132178 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : term503 A u v f.
Proof. exact (fun h0 : term293 A u v f => @lem7132177 A x u v f h1 h2 h3). Qed.
Lemma lem7132180 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7132181 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term503 A u v f) = ((term239 A u v f) = (term240 A v f)).
Proof. exact (@lem7132180 ((term239 A u v f) = (term240 A v f))). Qed.
Lemma lem7132182 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : (term239 A u v f) = (term240 A v f).
Proof. exact (EQ_MP (@lem7132181 A u v f) (@lem7132178 A x u v f h1 h2 h3)). Qed.
Lemma lem7132185 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7132187 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term293 A u v f) = (term504 A u v f).
Proof. exact (@lem7132185 ((term239 A u v f) = (term240 A v f))). Qed.
Lemma lem7132190 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term65 A u v f) : term504 A u v f.
Proof. exact (EQ_MP (@lem7132187 A u v f) (@lem7130917 A u v f h1)). Qed.
Lemma lem7132193 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : False.
Proof. exact (@lem7132190 A u v f h3 (@lem7132182 A x u v f h1 h2 h3)). Qed.
Lemma lem7132194 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : term505.
Proof. exact (fun h0 : ~ False => @lem7132193 A x u v f h1 h2 h3). Qed.
Lemma lem7132196 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7132197 : term505 = False.
Proof. exact (@lem7132196 False). Qed.
Lemma lem7132198 {A : Type'} (x : type709 A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term65 A u v f) : False.
Proof. exact (EQ_MP (@lem7132197) (@lem7132194 A x u v f h1 h2 h3)). Qed.
Lemma lem7132199 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term75 A u f) : False.
Proof. exact (ex_elim (@lem7130384 A u f h3) (fun v : A -> Prop => fun h0 : term74 A u f v => @lem7132198 A x u v f h1 h2 h0)). Qed.
Lemma lem7132200 {A : Type'} (x : type709 A) (f : A -> real) (h1 : term12 A) (h2 : term223 A x) (h3 : term82 A f) : False.
Proof. exact (ex_elim (@lem7130383 A f h3) (fun u : A -> Prop => fun h0 : term81 A f u => @lem7132199 A x u f h1 h2 h0)). Qed.
Lemma lem7132201 {A : Type'} (x : type709 A) (h1 : term12 A) (h2 : term223 A x) (h3 : term10 A) : False.
Proof. exact (ex_elim (@lem7130060 A h3) (fun f : A -> real => fun h0 : term89 A f => @lem7132200 A x f h1 h2 h0)). Qed.
Lemma lem7132202 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : False.
Proof. exact (ex_elim (@lem7130381 A h2) (fun x : type709 A => fun h0 : term225 A x => @lem7132201 A x h1 h0 h3)). Qed.
Lemma lem7132203 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : (term12 A) = False.
Proof. exact (prop_ext (fun h4 : term12 A => @lem7132202 A h1 h2 h3) (fun h4 : False => @lem7130080 A h1)). Qed.
Lemma lem7132204 {A : Type'} (h1 : term12 A) (h2 : term11 A) (h3 : term10 A) : False.
Proof. exact (EQ_MP (@lem7132203 A h1 h2 h3) (@lem7130080 A h1)). Qed.
Lemma lem7132205 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem7132204 A h1 h0 h2). Qed.
Lemma lem7132206 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem7132207 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem7132206 A) (@lem7132205 A h1 h2)). Qed.
Lemma lem7132208 {A : Type'} (h1 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem7132207 A h0 h1). Qed.
Lemma lem7132209 {A : Type'} : term23 A.
Proof. exact (fun h0 : term10 A => @lem7132208 A h0). Qed.
Lemma lem7132210 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem7129890 A) (@lem7132209 A)). Qed.
Lemma lem7132212 {A : Type'} : term13 A.
Proof. exact (@lem7129652 A (@lem7132210 A)). Qed.
Lemma lem7132213 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem7132212 A (@lem7129631 A h1)). Qed.
Lemma lem7132214 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem7132213 A h1 (@lem7129636 A)). Qed.
Lemma lem7132215 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem7132214 A h1 (@lem7129632 A)). Qed.
Lemma lem7132216 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem7132215 A h1) (fun h2 : False => @lem7129631 A h1)). Qed.
Lemma lem7132217 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem7132216 A h1) (@lem7129631 A h1)). Qed.
Lemma lem7132218 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem7132217 A h0). Qed.
Lemma lem7132219 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem7129630 A) (@lem7132218 A)). Qed.
