Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_ELIM_TRIPLE_THM_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import PAIR_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Lemma lem3405757 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3405758 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3405759 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3405758 t1) (@lem3405757 t1)). Qed.
Lemma lem3405760 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3405759 t1 t2). Qed.
Lemma lem3405761 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3405762 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3405761 t1 t2) (@lem3405760 t1 t2)). Qed.
Lemma lem3405763 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3405762 t1 t2 t3). Qed.
Lemma lem3405764 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3405765 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3405764 t1 t2 t3) (@lem3405763 t1 t2 t3)). Qed.
Lemma lem3405766 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3405765 t1 t2 t3)). Qed.
Lemma lem3405767 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem3405768 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem3405769 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem3405768 A B x) (@lem3405767 A B x)). Qed.
Lemma lem3405770 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem3405769 A B x y). Qed.
Lemma lem3405771 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = (term10 A B x y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem3405772 {A B : Type'} (x : A) (y : B) : term10 A B x y.
Proof. exact (EQ_MP (@lem3405771 A B x y) (@lem3405770 A B x y)). Qed.
Lemma lem3405773 {A B : Type'} (x : A) (y : B) (a : A) : term11 A B x y a.
Proof. exact (@lem3405772 A B x y a). Qed.
Lemma lem3405774 {A B : Type'} (x : A) (a : A) (y : B) : (term11 A B x y a) = (term12 A B x a y).
Proof. exact (eq_refl (term11 A B x y a)). Qed.
Lemma lem3405775 {A B : Type'} (x : A) (a : A) (y : B) : term12 A B x a y.
Proof. exact (EQ_MP (@lem3405774 A B x a y) (@lem3405773 A B x y a)). Qed.
Lemma lem3405776 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term13 A B x a y b.
Proof. exact (@lem3405775 A B x a y b). Qed.
Lemma lem3405777 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term13 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b)).
Proof. exact (eq_refl (term13 A B x a y b)). Qed.
Lemma lem3405810 {_83064 : Type'} : term15 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3405811 {_83064 : Type'} (P : type919 _83064) : term16 _83064 P.
Proof. exact (@lem3405810 _83064 P). Qed.
Lemma lem3405812 {_83064 : Type'} (P : type919 _83064) : (term16 _83064 P) = (term17 _83064 P).
Proof. exact (eq_refl (term16 _83064 P)). Qed.
Lemma lem3405813 {_83064 : Type'} (P : type919 _83064) : term17 _83064 P.
Proof. exact (EQ_MP (@lem3405812 _83064 P) (@lem3405811 _83064 P)). Qed.
Lemma lem3405814 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term18 _83064 P x.
Proof. exact (@lem3405813 _83064 P x). Qed.
Lemma lem3405815 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 P x) = ((term19 _83064 x P) = (term20 _83064 P x)).
Proof. exact (eq_refl (term18 _83064 P x)). Qed.
Lemma lem3405838 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term19 _83064 x P) = (term20 _83064 P x).
Proof. exact (EQ_MP (@lem3405815 _83064 P x) (@lem3405814 _83064 P x)). Qed.
Lemma lem3405839 {_88500 _88501 _88502 : Type'} (P : type917 _88500 _88501 _88502) (x : type1659 _88500 _88501 _88502) : (term21 _88500 _88501 _88502 x P) = (term22 _88500 _88501 _88502 P x).
Proof. exact (@lem3405838 (type1659 _88500 _88501 _88502) P x). Qed.
Lemma lem3405840 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term23 _88500 _88501 _88502 a b c P) = (term24 _88500 _88501 _88502 P a b c).
Proof. exact (@lem3405839 _88500 _88501 _88502 (term25 _88500 _88501 _88502 P) (term26 _88500 _88501 _88502 a b c)). Qed.
Lemma lem3405841 {_88500 _88501 _88502 : Type'} (GEN_PVAR_32 : type1659 _88500 _88501 _88502) (P : type1517 _88500 _88501 _88502) : (term27 _88500 _88501 _88502 P GEN_PVAR_32) = (term28 _88500 _88501 _88502 GEN_PVAR_32 P).
Proof. exact (eq_refl (term27 _88500 _88501 _88502 P GEN_PVAR_32)). Qed.
Lemma lem3405842 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term29 _88500 _88501 _88502 P) = (term30 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun GEN_PVAR_32 : type1659 _88500 _88501 _88502 => @lem3405841 _88500 _88501 _88502 GEN_PVAR_32 P)). Qed.
Lemma lem3405843 {_88500 _88501 _88502 : Type'} : (@GSPEC (prod _88502 (prod _88501 _88500))) = (@GSPEC (prod _88502 (prod _88501 _88500))).
Proof. exact (eq_refl (@GSPEC (prod _88502 (prod _88501 _88500)))). Qed.
Lemma lem3405844 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term31 _88500 _88501 _88502 P) = (term32 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3405843 _88500 _88501 _88502) (@lem3405842 _88500 _88501 _88502 P)). Qed.
Lemma lem3405845 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) : (term33 _88500 _88501 _88502 a b c) = (term33 _88500 _88501 _88502 a b c).
Proof. exact (eq_refl (term33 _88500 _88501 _88502 a b c)). Qed.
Lemma lem3405846 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) : (term23 _88500 _88501 _88502 a b c P) = (term34 _88500 _88501 _88502 a b c P).
Proof. exact (MK_COMB (@lem3405845 _88500 _88501 _88502 a b c) (@lem3405844 _88500 _88501 _88502 P)). Qed.
Lemma lem3405847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405848 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) : (term35 _88500 _88501 _88502 a b c P) = (term36 _88500 _88501 _88502 a b c P).
Proof. exact (MK_COMB (@lem3405847) (@lem3405846 _88500 _88501 _88502 a b c P)). Qed.
Lemma lem3405849 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) : (term24 _88500 _88501 _88502 P a b c) = (term37 _88500 _88501 _88502 a b c P).
Proof. exact (eq_refl (term24 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405850 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) : ((term23 _88500 _88501 _88502 a b c P) = (term24 _88500 _88501 _88502 P a b c)) = ((term34 _88500 _88501 _88502 a b c P) = (term37 _88500 _88501 _88502 a b c P)).
Proof. exact (MK_COMB (@lem3405848 _88500 _88501 _88502 a b c P) (@lem3405849 _88500 _88501 _88502 a b c P)). Qed.
Lemma lem3405851 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) : (term34 _88500 _88501 _88502 a b c P) = (term37 _88500 _88501 _88502 a b c P).
Proof. exact (EQ_MP (@lem3405850 _88500 _88501 _88502 a b c P) (@lem3405840 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405865 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3405866 {_88500 _88501 _88502 : Type'} (f : type1535 _88500 _88501 _88502) (y : Prop) : (term39 _88500 _88501 _88502 f y) = (f y).
Proof. exact (@lem3405865 Prop (type1227 _88500 _88501 _88502) f y). Qed.
Lemma lem3405867 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term40 _88500 _88501 _88502 a b c P x y z) = (term41 _88500 _88501 _88502 a b c P x y z).
Proof. exact (@lem3405866 _88500 _88501 _88502 (term42 _88500 _88501 _88502 a b c) (P x y z)). Qed.
Lemma lem3405868 {_88500 _88501 _88502 : Type'} (p : Prop) (a : _88502) (b : _88501) (c : _88500) : (term43 _88500 _88501 _88502 a b c p) = (term44 _88500 _88501 _88502 p a b c).
Proof. exact (eq_refl (term43 _88500 _88501 _88502 a b c p)). Qed.
Lemma lem3405869 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) : (term45 _88500 _88501 _88502 a b c) = (term42 _88500 _88501 _88502 a b c).
Proof. exact (fun_ext (fun p : Prop => @lem3405868 _88500 _88501 _88502 p a b c)). Qed.
Lemma lem3405870 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem3405871 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term40 _88500 _88501 _88502 a b c P x y z) = (term41 _88500 _88501 _88502 a b c P x y z).
Proof. exact (MK_COMB (@lem3405869 _88500 _88501 _88502 a b c) (@lem3405870 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3405872 {_88500 _88501 _88502 : Type'} : (@eq ((prod _88502 (prod _88501 _88500)) -> Prop)) = (@eq ((prod _88502 (prod _88501 _88500)) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _88502 (prod _88501 _88500)) -> Prop))). Qed.
Lemma lem3405873 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term46 _88500 _88501 _88502 a b c P x y z) = (term47 _88500 _88501 _88502 a b c P x y z).
Proof. exact (MK_COMB (@lem3405872 _88500 _88501 _88502) (@lem3405871 _88500 _88501 _88502 a b c P x y z)). Qed.
Lemma lem3405874 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) (a : _88502) (b : _88501) (c : _88500) : (term41 _88500 _88501 _88502 a b c P x y z) = (term48 _88500 _88501 _88502 P x y z a b c).
Proof. exact (eq_refl (term41 _88500 _88501 _88502 a b c P x y z)). Qed.
Lemma lem3405875 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) (a : _88502) (b : _88501) (c : _88500) : ((term40 _88500 _88501 _88502 a b c P x y z) = (term41 _88500 _88501 _88502 a b c P x y z)) = ((term41 _88500 _88501 _88502 a b c P x y z) = (term48 _88500 _88501 _88502 P x y z a b c)).
Proof. exact (MK_COMB (@lem3405873 _88500 _88501 _88502 a b c P x y z) (@lem3405874 _88500 _88501 _88502 P x y z a b c)). Qed.
Lemma lem3405876 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) (a : _88502) (b : _88501) (c : _88500) : (term41 _88500 _88501 _88502 a b c P x y z) = (term48 _88500 _88501 _88502 P x y z a b c).
Proof. exact (EQ_MP (@lem3405875 _88500 _88501 _88502 P x y z a b c) (@lem3405867 _88500 _88501 _88502 a b c P x y z)). Qed.
Lemma lem3405881 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) : (term26 _88500 _88501 _88502 x y z) = (term26 _88500 _88501 _88502 x y z).
Proof. exact (eq_refl (term26 _88500 _88501 _88502 x y z)). Qed.
Lemma lem3405882 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term49 _88500 _88501 _88502 a b c P x y z) = (term50 _88500 _88501 _88502 P a b c x y z).
Proof. exact (MK_COMB (@lem3405876 _88500 _88501 _88502 P x y z a b c) (@lem3405881 _88500 _88501 _88502 x y z)). Qed.
Lemma lem3405884 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3405885 {_88500 _88501 _88502 : Type'} (f : type1227 _88500 _88501 _88502) (y : type1659 _88500 _88501 _88502) : (term51 _88500 _88501 _88502 f y) = (f y).
Proof. exact (@lem3405884 (type1659 _88500 _88501 _88502) Prop f y). Qed.
Lemma lem3405886 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term52 _88500 _88501 _88502 P a b c x y z) = (term50 _88500 _88501 _88502 P a b c x y z).
Proof. exact (@lem3405885 _88500 _88501 _88502 (term48 _88500 _88501 _88502 P x y z a b c) (term26 _88500 _88501 _88502 x y z)). Qed.
Lemma lem3405887 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) (a : _88502) (b : _88501) (c : _88500) (t : type1659 _88500 _88501 _88502) : (term53 _88500 _88501 _88502 P x y z a b c t) = (term54 _88500 _88501 _88502 P x y z a b c t).
Proof. exact (eq_refl (term53 _88500 _88501 _88502 P x y z a b c t)). Qed.
Lemma lem3405888 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) (a : _88502) (b : _88501) (c : _88500) : (term55 _88500 _88501 _88502 P x y z a b c) = (term48 _88500 _88501 _88502 P x y z a b c).
Proof. exact (fun_ext (fun t : type1659 _88500 _88501 _88502 => @lem3405887 _88500 _88501 _88502 P x y z a b c t)). Qed.
Lemma lem3405889 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) : (term26 _88500 _88501 _88502 x y z) = (term26 _88500 _88501 _88502 x y z).
Proof. exact (eq_refl (term26 _88500 _88501 _88502 x y z)). Qed.
Lemma lem3405890 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term52 _88500 _88501 _88502 P a b c x y z) = (term50 _88500 _88501 _88502 P a b c x y z).
Proof. exact (MK_COMB (@lem3405888 _88500 _88501 _88502 P x y z a b c) (@lem3405889 _88500 _88501 _88502 x y z)). Qed.
Lemma lem3405891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405892 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term56 _88500 _88501 _88502 P a b c x y z) = (term57 _88500 _88501 _88502 P a b c x y z).
Proof. exact (MK_COMB (@lem3405891) (@lem3405890 _88500 _88501 _88502 P a b c x y z)). Qed.
Lemma lem3405893 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term50 _88500 _88501 _88502 P a b c x y z) = (term58 _88500 _88501 _88502 P a b c x y z).
Proof. exact (eq_refl (term50 _88500 _88501 _88502 P a b c x y z)). Qed.
Lemma lem3405894 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : ((term52 _88500 _88501 _88502 P a b c x y z) = (term50 _88500 _88501 _88502 P a b c x y z)) = ((term50 _88500 _88501 _88502 P a b c x y z) = (term58 _88500 _88501 _88502 P a b c x y z)).
Proof. exact (MK_COMB (@lem3405892 _88500 _88501 _88502 P a b c x y z) (@lem3405893 _88500 _88501 _88502 P a b c x y z)). Qed.
Lemma lem3405895 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x : _88502) (y : _88501) (z : _88500) : (term50 _88500 _88501 _88502 P a b c x y z) = (term58 _88500 _88501 _88502 P a b c x y z).
Proof. exact (EQ_MP (@lem3405894 _88500 _88501 _88502 P a b c x y z) (@lem3405886 _88500 _88501 _88502 P a b c x y z)). Qed.
Lemma lem3405899 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b).
Proof. exact (EQ_MP (@lem3405777 A B x a y b) (@lem3405776 A B x a y b)). Qed.
Lemma lem3405900 {_88500 _88501 _88502 : Type'} (x : _88502) (a : _88502) (y : prod _88501 _88500) (b : prod _88501 _88500) : ((@pair _88502 (prod _88501 _88500) x y) = (@pair _88502 (prod _88501 _88500) a b)) = (term59 _88500 _88501 _88502 x a y b).
Proof. exact (@lem3405899 _88502 (prod _88501 _88500) x a y b). Qed.
Lemma lem3405901 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (c : _88500) (y : _88501) (z : _88500) : ((term26 _88500 _88501 _88502 a b c) = (term26 _88500 _88501 _88502 x y z)) = (term60 _88500 _88501 _88502 a x b c y z).
Proof. exact (@lem3405900 _88500 _88501 _88502 a x (@pair _88501 _88500 b c) (@pair _88501 _88500 y z)). Qed.
Lemma lem3405907 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b).
Proof. exact (EQ_MP (@lem3405777 A B x a y b) (@lem3405776 A B x a y b)). Qed.
Lemma lem3405908 {_88500 _88501 : Type'} (x : _88501) (a : _88501) (y : _88500) (b : _88500) : ((@pair _88501 _88500 x y) = (@pair _88501 _88500 a b)) = (term61 _88500 _88501 x a y b).
Proof. exact (@lem3405907 _88501 _88500 x a y b). Qed.
Lemma lem3405909 {_88500 _88501 : Type'} (b : _88501) (y : _88501) (c : _88500) (z : _88500) : ((@pair _88501 _88500 b c) = (@pair _88501 _88500 y z)) = (term61 _88500 _88501 b y c z).
Proof. exact (@lem3405908 _88500 _88501 b y c z). Qed.
Lemma lem3405916 {_88502 : Type'} (a : _88502) (x : _88502) : (term62 _88502 a x) = (term62 _88502 a x).
Proof. exact (eq_refl (term62 _88502 a x)). Qed.
Lemma lem3405917 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term60 _88500 _88501 _88502 a x b c y z) = (term63 _88500 _88501 _88502 a x b y c z).
Proof. exact (MK_COMB (@lem3405916 _88502 a x) (@lem3405909 _88500 _88501 b y c z)). Qed.
Lemma lem3405920 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : ((term26 _88500 _88501 _88502 a b c) = (term26 _88500 _88501 _88502 x y z)) = (term63 _88500 _88501 _88502 a x b y c z).
Proof. exact (TRANS (@lem3405901 _88500 _88501 _88502 a x b c y z) (@lem3405917 _88500 _88501 _88502 a x b y c z)). Qed.
Lemma lem3405921 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term64 _88500 _88501 _88502 P x y z) = (term64 _88500 _88501 _88502 P x y z).
Proof. exact (eq_refl (term64 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3405922 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term58 _88500 _88501 _88502 P a b c x y z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (MK_COMB (@lem3405921 _88500 _88501 _88502 P x y z) (@lem3405920 _88500 _88501 _88502 a x b y c z)). Qed.
Lemma lem3405925 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term50 _88500 _88501 _88502 P a b c x y z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (TRANS (@lem3405895 _88500 _88501 _88502 P a b c x y z) (@lem3405922 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3405926 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term49 _88500 _88501 _88502 a b c P x y z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (TRANS (@lem3405882 _88500 _88501 _88502 P a b c x y z) (@lem3405925 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3405927 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term66 _88500 _88501 _88502 a b c P x y) = (term67 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3405926 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3405928 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3405929 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term68 _88500 _88501 _88502 a b c P x y) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3405928 _88500) (@lem3405927 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3405934 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term70 _88500 _88501 _88502 a b c P x) = (term71 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3405929 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3405935 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3405936 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term72 _88500 _88501 _88502 a b c P x) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3405935 _88501) (@lem3405934 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3405941 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term74 _88500 _88501 _88502 a b c P) = (term75 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3405936 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3405942 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3405943 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term37 _88500 _88501 _88502 a b c P) = (term76 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3405942 _88502) (@lem3405941 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405948 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term34 _88500 _88501 _88502 a b c P) = (term76 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3405851 _88500 _88501 _88502 a b c P) (@lem3405943 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3405950 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term36 _88500 _88501 _88502 a b c P) = (term77 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3405949) (@lem3405948 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405951 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3405952 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term34 _88500 _88501 _88502 a b c P) = (P a b c)) = ((term76 _88500 _88501 _88502 P a b c) = (P a b c)).
Proof. exact (MK_COMB (@lem3405950 _88500 _88501 _88502 P a b c) (@lem3405951 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405955 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term78 _88500 _88501 _88502 P a b) = (term79 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3405952 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3405956 {_88500 : Type'} : (@all _88500) = (@all _88500).
Proof. exact (eq_refl (@all _88500)). Qed.
Lemma lem3405957 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term80 _88500 _88501 _88502 P a b) = (term81 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3405956 _88500) (@lem3405955 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3405962 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term82 _88500 _88501 _88502 P a) = (term83 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3405957 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3405963 {_88501 : Type'} : (@all _88501) = (@all _88501).
Proof. exact (eq_refl (@all _88501)). Qed.
Lemma lem3405964 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term84 _88500 _88501 _88502 P a) = (term85 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3405963 _88501) (@lem3405962 _88500 _88501 _88502 P a)). Qed.
Lemma lem3405969 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term86 _88500 _88501 _88502 P) = (term87 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3405964 _88500 _88501 _88502 P a)). Qed.
Lemma lem3405970 {_88502 : Type'} : (@all _88502) = (@all _88502).
Proof. exact (eq_refl (@all _88502)). Qed.
Lemma lem3405971 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term88 _88500 _88501 _88502 P) = (term89 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3405970 _88502) (@lem3405969 _88500 _88501 _88502 P)). Qed.
Lemma lem3405976 {_88500 _88501 _88502 : Type'} : (term90 _88500 _88501 _88502) = (term91 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3405971 _88500 _88501 _88502 P)). Qed.
Lemma lem3405977 {_88500 _88501 _88502 : Type'} : (@all (_88502 -> _88501 -> _88500 -> Prop)) = (@all (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@all (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3405978 {_88500 _88501 _88502 : Type'} : (term92 _88500 _88501 _88502) = (term93 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3405977 _88500 _88501 _88502) (@lem3405976 _88500 _88501 _88502)). Qed.
Lemma lem3405983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3405984 {_88500 _88501 _88502 : Type'} : (term94 _88500 _88501 _88502) = (term95 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3405983) (@lem3405978 _88500 _88501 _88502)). Qed.
Lemma lem3406004 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term19 _83064 x P) = (term20 _83064 P x).
Proof. exact (EQ_MP (@lem3405815 _83064 P x) (@lem3405814 _83064 P x)). Qed.
Lemma lem3406005 {_88563 _88564 _88565 : Type'} (P : type912 _88563 _88564 _88565) (x : type1651 _88563 _88564 _88565) : (term96 _88563 _88564 _88565 x P) = (term97 _88563 _88564 _88565 P x).
Proof. exact (@lem3406004 (type1651 _88563 _88564 _88565) P x). Qed.
Lemma lem3406006 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term98 _88563 _88564 _88565 a b c P) = (term99 _88563 _88564 _88565 P a b c).
Proof. exact (@lem3406005 _88563 _88564 _88565 (term100 _88563 _88564 _88565 P) (term101 _88563 _88564 _88565 a b c)). Qed.
Lemma lem3406007 {_88563 _88564 _88565 : Type'} (GEN_PVAR_33 : type1651 _88563 _88564 _88565) (P : type1517 _88563 _88564 _88565) : (term102 _88563 _88564 _88565 P GEN_PVAR_33) = (term103 _88563 _88564 _88565 GEN_PVAR_33 P).
Proof. exact (eq_refl (term102 _88563 _88564 _88565 P GEN_PVAR_33)). Qed.
Lemma lem3406008 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term104 _88563 _88564 _88565 P) = (term105 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun GEN_PVAR_33 : type1651 _88563 _88564 _88565 => @lem3406007 _88563 _88564 _88565 GEN_PVAR_33 P)). Qed.
Lemma lem3406009 {_88563 _88564 _88565 : Type'} : (@GSPEC (prod (prod _88565 _88564) _88563)) = (@GSPEC (prod (prod _88565 _88564) _88563)).
Proof. exact (eq_refl (@GSPEC (prod (prod _88565 _88564) _88563))). Qed.
Lemma lem3406010 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term106 _88563 _88564 _88565 P) = (term107 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3406009 _88563 _88564 _88565) (@lem3406008 _88563 _88564 _88565 P)). Qed.
Lemma lem3406011 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) : (term108 _88563 _88564 _88565 a b c) = (term108 _88563 _88564 _88565 a b c).
Proof. exact (eq_refl (term108 _88563 _88564 _88565 a b c)). Qed.
Lemma lem3406012 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) : (term98 _88563 _88564 _88565 a b c P) = (term109 _88563 _88564 _88565 a b c P).
Proof. exact (MK_COMB (@lem3406011 _88563 _88564 _88565 a b c) (@lem3406010 _88563 _88564 _88565 P)). Qed.
Lemma lem3406013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406014 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) : (term110 _88563 _88564 _88565 a b c P) = (term111 _88563 _88564 _88565 a b c P).
Proof. exact (MK_COMB (@lem3406013) (@lem3406012 _88563 _88564 _88565 a b c P)). Qed.
Lemma lem3406015 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) : (term99 _88563 _88564 _88565 P a b c) = (term112 _88563 _88564 _88565 a b c P).
Proof. exact (eq_refl (term99 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406016 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) : ((term98 _88563 _88564 _88565 a b c P) = (term99 _88563 _88564 _88565 P a b c)) = ((term109 _88563 _88564 _88565 a b c P) = (term112 _88563 _88564 _88565 a b c P)).
Proof. exact (MK_COMB (@lem3406014 _88563 _88564 _88565 a b c P) (@lem3406015 _88563 _88564 _88565 a b c P)). Qed.
Lemma lem3406017 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) : (term109 _88563 _88564 _88565 a b c P) = (term112 _88563 _88564 _88565 a b c P).
Proof. exact (EQ_MP (@lem3406016 _88563 _88564 _88565 a b c P) (@lem3406006 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406031 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3406032 {_88563 _88564 _88565 : Type'} (f : type1530 _88563 _88564 _88565) (y : Prop) : (term113 _88563 _88564 _88565 f y) = (f y).
Proof. exact (@lem3406031 Prop (type1188 _88563 _88564 _88565) f y). Qed.
Lemma lem3406033 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (term114 _88563 _88564 _88565 a b c P x y z) = (term115 _88563 _88564 _88565 a b c P x y z).
Proof. exact (@lem3406032 _88563 _88564 _88565 (term116 _88563 _88564 _88565 a b c) (P x y z)). Qed.
Lemma lem3406034 {_88563 _88564 _88565 : Type'} (p : Prop) (a : _88565) (b : _88564) (c : _88563) : (term117 _88563 _88564 _88565 a b c p) = (term118 _88563 _88564 _88565 p a b c).
Proof. exact (eq_refl (term117 _88563 _88564 _88565 a b c p)). Qed.
Lemma lem3406035 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) : (term119 _88563 _88564 _88565 a b c) = (term116 _88563 _88564 _88565 a b c).
Proof. exact (fun_ext (fun p : Prop => @lem3406034 _88563 _88564 _88565 p a b c)). Qed.
Lemma lem3406036 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem3406037 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (term114 _88563 _88564 _88565 a b c P x y z) = (term115 _88563 _88564 _88565 a b c P x y z).
Proof. exact (MK_COMB (@lem3406035 _88563 _88564 _88565 a b c) (@lem3406036 _88563 _88564 _88565 P x y z)). Qed.
Lemma lem3406038 {_88563 _88564 _88565 : Type'} : (@eq ((prod (prod _88565 _88564) _88563) -> Prop)) = (@eq ((prod (prod _88565 _88564) _88563) -> Prop)).
Proof. exact (eq_refl (@eq ((prod (prod _88565 _88564) _88563) -> Prop))). Qed.
Lemma lem3406039 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (c : _88563) (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (term120 _88563 _88564 _88565 a b c P x y z) = (term121 _88563 _88564 _88565 a b c P x y z).
Proof. exact (MK_COMB (@lem3406038 _88563 _88564 _88565) (@lem3406037 _88563 _88564 _88565 a b c P x y z)). Qed.
Lemma lem3406040 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) (a : _88565) (b : _88564) (c : _88563) : (term115 _88563 _88564 _88565 a b c P x y z) = (term122 _88563 _88564 _88565 P x y z a b c).
Proof. exact (eq_refl (term115 _88563 _88564 _88565 a b c P x y z)). Qed.
Lemma lem3406041 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) (a : _88565) (b : _88564) (c : _88563) : ((term114 _88563 _88564 _88565 a b c P x y z) = (term115 _88563 _88564 _88565 a b c P x y z)) = ((term115 _88563 _88564 _88565 a b c P x y z) = (term122 _88563 _88564 _88565 P x y z a b c)).
Proof. exact (MK_COMB (@lem3406039 _88563 _88564 _88565 a b c P x y z) (@lem3406040 _88563 _88564 _88565 P x y z a b c)). Qed.
Lemma lem3406042 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) (a : _88565) (b : _88564) (c : _88563) : (term115 _88563 _88564 _88565 a b c P x y z) = (term122 _88563 _88564 _88565 P x y z a b c).
Proof. exact (EQ_MP (@lem3406041 _88563 _88564 _88565 P x y z a b c) (@lem3406033 _88563 _88564 _88565 a b c P x y z)). Qed.
Lemma lem3406047 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) : (term101 _88563 _88564 _88565 x y z) = (term101 _88563 _88564 _88565 x y z).
Proof. exact (eq_refl (term101 _88563 _88564 _88565 x y z)). Qed.
Lemma lem3406048 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term123 _88563 _88564 _88565 a b c P x y z) = (term124 _88563 _88564 _88565 P a b c x y z).
Proof. exact (MK_COMB (@lem3406042 _88563 _88564 _88565 P x y z a b c) (@lem3406047 _88563 _88564 _88565 x y z)). Qed.
Lemma lem3406050 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3406051 {_88563 _88564 _88565 : Type'} (f : type1188 _88563 _88564 _88565) (y : type1651 _88563 _88564 _88565) : (term125 _88563 _88564 _88565 f y) = (f y).
Proof. exact (@lem3406050 (type1651 _88563 _88564 _88565) Prop f y). Qed.
Lemma lem3406052 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term126 _88563 _88564 _88565 P a b c x y z) = (term124 _88563 _88564 _88565 P a b c x y z).
Proof. exact (@lem3406051 _88563 _88564 _88565 (term122 _88563 _88564 _88565 P x y z a b c) (term101 _88563 _88564 _88565 x y z)). Qed.
Lemma lem3406053 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) (a : _88565) (b : _88564) (c : _88563) (t : type1651 _88563 _88564 _88565) : (term127 _88563 _88564 _88565 P x y z a b c t) = (term128 _88563 _88564 _88565 P x y z a b c t).
Proof. exact (eq_refl (term127 _88563 _88564 _88565 P x y z a b c t)). Qed.
Lemma lem3406054 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) (a : _88565) (b : _88564) (c : _88563) : (term129 _88563 _88564 _88565 P x y z a b c) = (term122 _88563 _88564 _88565 P x y z a b c).
Proof. exact (fun_ext (fun t : type1651 _88563 _88564 _88565 => @lem3406053 _88563 _88564 _88565 P x y z a b c t)). Qed.
Lemma lem3406055 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) : (term101 _88563 _88564 _88565 x y z) = (term101 _88563 _88564 _88565 x y z).
Proof. exact (eq_refl (term101 _88563 _88564 _88565 x y z)). Qed.
Lemma lem3406056 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term126 _88563 _88564 _88565 P a b c x y z) = (term124 _88563 _88564 _88565 P a b c x y z).
Proof. exact (MK_COMB (@lem3406054 _88563 _88564 _88565 P x y z a b c) (@lem3406055 _88563 _88564 _88565 x y z)). Qed.
Lemma lem3406057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406058 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term130 _88563 _88564 _88565 P a b c x y z) = (term131 _88563 _88564 _88565 P a b c x y z).
Proof. exact (MK_COMB (@lem3406057) (@lem3406056 _88563 _88564 _88565 P a b c x y z)). Qed.
Lemma lem3406059 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term124 _88563 _88564 _88565 P a b c x y z) = (term132 _88563 _88564 _88565 P a b c x y z).
Proof. exact (eq_refl (term124 _88563 _88564 _88565 P a b c x y z)). Qed.
Lemma lem3406060 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : ((term126 _88563 _88564 _88565 P a b c x y z) = (term124 _88563 _88564 _88565 P a b c x y z)) = ((term124 _88563 _88564 _88565 P a b c x y z) = (term132 _88563 _88564 _88565 P a b c x y z)).
Proof. exact (MK_COMB (@lem3406058 _88563 _88564 _88565 P a b c x y z) (@lem3406059 _88563 _88564 _88565 P a b c x y z)). Qed.
Lemma lem3406061 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) (x : _88565) (y : _88564) (z : _88563) : (term124 _88563 _88564 _88565 P a b c x y z) = (term132 _88563 _88564 _88565 P a b c x y z).
Proof. exact (EQ_MP (@lem3406060 _88563 _88564 _88565 P a b c x y z) (@lem3406052 _88563 _88564 _88565 P a b c x y z)). Qed.
Lemma lem3406065 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b).
Proof. exact (EQ_MP (@lem3405777 A B x a y b) (@lem3405776 A B x a y b)). Qed.
Lemma lem3406066 {_88563 _88564 _88565 : Type'} (x : prod _88565 _88564) (a : prod _88565 _88564) (y : _88563) (b : _88563) : ((@pair (prod _88565 _88564) _88563 x y) = (@pair (prod _88565 _88564) _88563 a b)) = (term133 _88563 _88564 _88565 x a y b).
Proof. exact (@lem3406065 (prod _88565 _88564) _88563 x a y b). Qed.
Lemma lem3406067 {_88563 _88564 _88565 : Type'} (a : _88565) (b : _88564) (x : _88565) (y : _88564) (c : _88563) (z : _88563) : ((term101 _88563 _88564 _88565 a b c) = (term101 _88563 _88564 _88565 x y z)) = (term134 _88563 _88564 _88565 a b x y c z).
Proof. exact (@lem3406066 _88563 _88564 _88565 (@pair _88565 _88564 a b) (@pair _88565 _88564 x y) c z). Qed.
Lemma lem3406071 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term14 A B x a y b).
Proof. exact (EQ_MP (@lem3405777 A B x a y b) (@lem3405776 A B x a y b)). Qed.
Lemma lem3406072 {_88564 _88565 : Type'} (x : _88565) (a : _88565) (y : _88564) (b : _88564) : ((@pair _88565 _88564 x y) = (@pair _88565 _88564 a b)) = (term61 _88564 _88565 x a y b).
Proof. exact (@lem3406071 _88565 _88564 x a y b). Qed.
Lemma lem3406073 {_88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) : ((@pair _88565 _88564 a b) = (@pair _88565 _88564 x y)) = (term61 _88564 _88565 a x b y).
Proof. exact (@lem3406072 _88564 _88565 a x b y). Qed.
Lemma lem3406080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406081 {_88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) : (term135 _88564 _88565 a b x y) = (term136 _88564 _88565 a x b y).
Proof. exact (MK_COMB (@lem3406080) (@lem3406073 _88564 _88565 a x b y)). Qed.
Lemma lem3406084 {_88563 : Type'} (c : _88563) (z : _88563) : (c = z) = (c = z).
Proof. exact (eq_refl (c = z)). Qed.
Lemma lem3406085 {_88563 _88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term134 _88563 _88564 _88565 a b x y c z) = (term137 _88563 _88564 _88565 a x b y c z).
Proof. exact (MK_COMB (@lem3406081 _88564 _88565 a x b y) (@lem3406084 _88563 c z)). Qed.
Lemma lem3406088 {_88563 _88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : ((term101 _88563 _88564 _88565 a b c) = (term101 _88563 _88564 _88565 x y z)) = (term137 _88563 _88564 _88565 a x b y c z).
Proof. exact (TRANS (@lem3406067 _88563 _88564 _88565 a b x y c z) (@lem3406085 _88563 _88564 _88565 a x b y c z)). Qed.
Lemma lem3406089 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (term64 _88563 _88564 _88565 P x y z) = (term64 _88563 _88564 _88565 P x y z).
Proof. exact (eq_refl (term64 _88563 _88564 _88565 P x y z)). Qed.
Lemma lem3406090 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term132 _88563 _88564 _88565 P a b c x y z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (MK_COMB (@lem3406089 _88563 _88564 _88565 P x y z) (@lem3406088 _88563 _88564 _88565 a x b y c z)). Qed.
Lemma lem3406093 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term124 _88563 _88564 _88565 P a b c x y z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (TRANS (@lem3406061 _88563 _88564 _88565 P a b c x y z) (@lem3406090 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406094 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term123 _88563 _88564 _88565 a b c P x y z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (TRANS (@lem3406048 _88563 _88564 _88565 P a b c x y z) (@lem3406093 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406095 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term139 _88563 _88564 _88565 a b c P x y) = (term140 _88563 _88564 _88565 P a x b y c).
Proof. exact (fun_ext (fun z : _88563 => @lem3406094 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406096 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3406097 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term141 _88563 _88564 _88565 a b c P x y) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3406096 _88563) (@lem3406095 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406102 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term143 _88563 _88564 _88565 a b c P x) = (term144 _88563 _88564 _88565 P a x b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3406097 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406103 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3406104 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term145 _88563 _88564 _88565 a b c P x) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3406103 _88564) (@lem3406102 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406109 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term147 _88563 _88564 _88565 a b c P) = (term148 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3406104 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406110 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3406111 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term112 _88563 _88564 _88565 a b c P) = (term149 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406110 _88565) (@lem3406109 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406116 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term109 _88563 _88564 _88565 a b c P) = (term149 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3406017 _88563 _88564 _88565 a b c P) (@lem3406111 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406118 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term111 _88563 _88564 _88565 a b c P) = (term150 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406117) (@lem3406116 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406119 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3406120 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term109 _88563 _88564 _88565 a b c P) = (P a b c)) = ((term149 _88563 _88564 _88565 P a b c) = (P a b c)).
Proof. exact (MK_COMB (@lem3406118 _88563 _88564 _88565 P a b c) (@lem3406119 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406123 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term151 _88563 _88564 _88565 P a b) = (term152 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3406120 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406124 {_88563 : Type'} : (@all _88563) = (@all _88563).
Proof. exact (eq_refl (@all _88563)). Qed.
Lemma lem3406125 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term153 _88563 _88564 _88565 P a b) = (term154 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3406124 _88563) (@lem3406123 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406130 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term155 _88563 _88564 _88565 P a) = (term156 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3406125 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406131 {_88564 : Type'} : (@all _88564) = (@all _88564).
Proof. exact (eq_refl (@all _88564)). Qed.
Lemma lem3406132 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term157 _88563 _88564 _88565 P a) = (term158 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3406131 _88564) (@lem3406130 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406137 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term159 _88563 _88564 _88565 P) = (term160 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3406132 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406138 {_88565 : Type'} : (@all _88565) = (@all _88565).
Proof. exact (eq_refl (@all _88565)). Qed.
Lemma lem3406139 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term161 _88563 _88564 _88565 P) = (term162 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3406138 _88565) (@lem3406137 _88563 _88564 _88565 P)). Qed.
Lemma lem3406144 {_88563 _88564 _88565 : Type'} : (term163 _88563 _88564 _88565) = (term164 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3406139 _88563 _88564 _88565 P)). Qed.
Lemma lem3406145 {_88563 _88564 _88565 : Type'} : (@all (_88565 -> _88564 -> _88563 -> Prop)) = (@all (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@all (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3406146 {_88563 _88564 _88565 : Type'} : (term165 _88563 _88564 _88565) = (term166 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3406145 _88563 _88564 _88565) (@lem3406144 _88563 _88564 _88565)). Qed.
Lemma lem3406151 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term167 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3405984 _88500 _88501 _88502) (@lem3406146 _88563 _88564 _88565)). Qed.
Lemma lem3406154 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term168 _88500 _88501 _88502 _88563 _88564 _88565) = (term167 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (SYM (@lem3406151 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406156 (p : Prop) : p = (term169 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3406157 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term168 _88500 _88501 _88502 _88563 _88564 _88565) = (term170 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem3406156 (term168 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406158 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term170 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (SYM (@lem3406157 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406159 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : term171 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406162 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term170 _88500 _88501 _88502 _88563 _88564 _88565) : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406163 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term170 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3406162 _88500 _88501 _88502 _88563 _88564 _88565 h0). Qed.
Lemma lem3406164 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term172 _88500 _88501 _88502 _88563 _88564 _88565) : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406165 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term170 _88500 _88501 _88502 _88563 _88564 _88565) : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406166 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term170 _88500 _88501 _88502 _88563 _88564 _88565) (h2 : term172 _88500 _88501 _88502 _88563 _88564 _88565) : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (@lem3406164 _88500 _88501 _88502 _88563 _88564 _88565 h2 (@lem3406165 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3406167 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term170 _88500 _88501 _88502 _88563 _88564 _88565) : term173 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term172 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3406166 _88500 _88501 _88502 _88563 _88564 _88565 h1 h0). Qed.
Lemma lem3406168 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term172 _88500 _88501 _88502 _88563 _88564 _88565) : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406169 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term170 _88500 _88501 _88502 _88563 _88564 _88565) (h2 : term172 _88500 _88501 _88502 _88563 _88564 _88565) : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (@lem3406167 _88500 _88501 _88502 _88563 _88564 _88565 h1 (@lem3406168 _88500 _88501 _88502 _88563 _88564 _88565 h2)). Qed.
Lemma lem3406170 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term172 _88500 _88501 _88502 _88563 _88564 _88565) : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term170 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3406169 _88500 _88501 _88502 _88563 _88564 _88565 h0 h1). Qed.
Lemma lem3406171 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term174 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term172 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3406170 _88500 _88501 _88502 _88563 _88564 _88565 h0). Qed.
Lemma lem3406174 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (@lem3406171 _88500 _88501 _88502 _88563 _88564 _88565 (@lem3406163 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406175 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term172 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (@lem3406174 _88500 _88501 _88502 _88563 _88564 _88565). Qed.
Lemma lem3406177 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3406178 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term170 _88500 _88501 _88502 _88563 _88564 _88565) = (term175 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem3406177 (term171 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406180 (t : Prop) : (term176 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3406181 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term175 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem3406180 (term168 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406344 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term170 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3406178 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3406181 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406345 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3406358 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term138 _88563 _88564 _88565 P a x b y c z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (eq_refl (term138 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406359 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term140 _88563 _88564 _88565 P a x b y c) = (term140 _88563 _88564 _88565 P a x b y c).
Proof. exact (fun_ext (fun z : _88563 => @lem3406358 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406360 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3406361 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term142 _88563 _88564 _88565 P a x b y c) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3406360 _88563) (@lem3406359 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406362 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term144 _88563 _88564 _88565 P a x b c) = (term144 _88563 _88564 _88565 P a x b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3406361 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406363 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3406364 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term146 _88563 _88564 _88565 P a x b c) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3406363 _88564) (@lem3406362 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406365 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term148 _88563 _88564 _88565 P a b c) = (term148 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3406364 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406366 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3406367 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term149 _88563 _88564 _88565 P a b c) = (term149 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406366 _88565) (@lem3406365 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406369 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term150 _88563 _88564 _88565 P a b c) = (term150 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406368) (@lem3406367 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406370 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term149 _88563 _88564 _88565 P a b c) = (P a b c)) = ((term149 _88563 _88564 _88565 P a b c) = (P a b c)).
Proof. exact (MK_COMB (@lem3406369 _88563 _88564 _88565 P a b c) (@lem3406345 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406371 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term152 _88563 _88564 _88565 P a b) = (term152 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3406370 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406372 {_88563 : Type'} : (@all _88563) = (@all _88563).
Proof. exact (eq_refl (@all _88563)). Qed.
Lemma lem3406373 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term154 _88563 _88564 _88565 P a b) = (term154 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3406372 _88563) (@lem3406371 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406374 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term156 _88563 _88564 _88565 P a) = (term156 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3406373 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406375 {_88564 : Type'} : (@all _88564) = (@all _88564).
Proof. exact (eq_refl (@all _88564)). Qed.
Lemma lem3406376 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term158 _88563 _88564 _88565 P a) = (term158 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3406375 _88564) (@lem3406374 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406377 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term160 _88563 _88564 _88565 P) = (term160 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3406376 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406378 {_88565 : Type'} : (@all _88565) = (@all _88565).
Proof. exact (eq_refl (@all _88565)). Qed.
Lemma lem3406379 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term162 _88563 _88564 _88565 P) = (term162 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3406378 _88565) (@lem3406377 _88563 _88564 _88565 P)). Qed.
Lemma lem3406380 {_88563 _88564 _88565 : Type'} : (term164 _88563 _88564 _88565) = (term164 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3406379 _88563 _88564 _88565 P)). Qed.
Lemma lem3406381 {_88563 _88564 _88565 : Type'} : (@all (_88565 -> _88564 -> _88563 -> Prop)) = (@all (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@all (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3406382 {_88563 _88564 _88565 : Type'} : (term166 _88563 _88564 _88565) = (term166 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3406381 _88563 _88564 _88565) (@lem3406380 _88563 _88564 _88565)). Qed.
Lemma lem3406383 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3406396 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term65 _88500 _88501 _88502 P a x b y c z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term65 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406397 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term67 _88500 _88501 _88502 P a x b y c) = (term67 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3406396 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406398 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406399 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term69 _88500 _88501 _88502 P a x b y c) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3406398 _88500) (@lem3406397 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406400 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term71 _88500 _88501 _88502 P a x b c) = (term71 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3406399 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406401 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3406402 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term73 _88500 _88501 _88502 P a x b c) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3406401 _88501) (@lem3406400 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406403 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term75 _88500 _88501 _88502 P a b c) = (term75 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3406402 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406404 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3406405 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term76 _88500 _88501 _88502 P a b c) = (term76 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406404 _88502) (@lem3406403 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406407 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term77 _88500 _88501 _88502 P a b c) = (term77 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406406) (@lem3406405 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406408 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term76 _88500 _88501 _88502 P a b c) = (P a b c)) = ((term76 _88500 _88501 _88502 P a b c) = (P a b c)).
Proof. exact (MK_COMB (@lem3406407 _88500 _88501 _88502 P a b c) (@lem3406383 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406409 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term79 _88500 _88501 _88502 P a b) = (term79 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3406408 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406410 {_88500 : Type'} : (@all _88500) = (@all _88500).
Proof. exact (eq_refl (@all _88500)). Qed.
Lemma lem3406411 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term81 _88500 _88501 _88502 P a b) = (term81 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406410 _88500) (@lem3406409 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406412 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term83 _88500 _88501 _88502 P a) = (term83 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3406411 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406413 {_88501 : Type'} : (@all _88501) = (@all _88501).
Proof. exact (eq_refl (@all _88501)). Qed.
Lemma lem3406414 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term85 _88500 _88501 _88502 P a) = (term85 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3406413 _88501) (@lem3406412 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406415 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term87 _88500 _88501 _88502 P) = (term87 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3406414 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406416 {_88502 : Type'} : (@all _88502) = (@all _88502).
Proof. exact (eq_refl (@all _88502)). Qed.
Lemma lem3406417 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term89 _88500 _88501 _88502 P) = (term89 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3406416 _88502) (@lem3406415 _88500 _88501 _88502 P)). Qed.
Lemma lem3406418 {_88500 _88501 _88502 : Type'} : (term91 _88500 _88501 _88502) = (term91 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3406417 _88500 _88501 _88502 P)). Qed.
Lemma lem3406419 {_88500 _88501 _88502 : Type'} : (@all (_88502 -> _88501 -> _88500 -> Prop)) = (@all (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@all (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3406420 {_88500 _88501 _88502 : Type'} : (term93 _88500 _88501 _88502) = (term93 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3406419 _88500 _88501 _88502) (@lem3406418 _88500 _88501 _88502)). Qed.
Lemma lem3406421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406422 {_88500 _88501 _88502 : Type'} : (term95 _88500 _88501 _88502) = (term95 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3406421) (@lem3406420 _88500 _88501 _88502)). Qed.
Lemma lem3406423 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term168 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3406422 _88500 _88501 _88502) (@lem3406382 _88563 _88564 _88565)). Qed.
Lemma lem3406524 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term170 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3406344 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3406423 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406525 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term168 _88500 _88501 _88502 _88563 _88564 _88565) = (term170 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (SYM (@lem3406524 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406527 (p : Prop) : p = (term169 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3406528 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term168 _88500 _88501 _88502 _88563 _88564 _88565) = (term170 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem3406527 (term168 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406529 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term170 _88500 _88501 _88502 _88563 _88564 _88565) = (term168 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (SYM (@lem3406528 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406530 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : term171 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (h1). Qed.
Lemma lem3406543 {_88500 _88501 : Type'} (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term177 _88500 _88501 b y c z) = (term178 _88500 _88501 b y c z).
Proof. exact (@lem17045 (b = y) (c = z)). Qed.
Lemma lem3406548 {_88502 : Type'} (a : _88502) (x : _88502) : (term179 _88502 a x) = (term179 _88502 a x).
Proof. exact (eq_refl (term179 _88502 a x)). Qed.
Lemma lem3406549 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term180 _88500 _88501 _88502 a x b y c z) = (term181 _88500 _88501 _88502 a x b y c z).
Proof. exact (MK_COMB (@lem3406548 _88502 a x) (@lem3406543 _88500 _88501 b y c z)). Qed.
Lemma lem3406550 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term182 _88500 _88501 _88502 a x b y c z) = (term180 _88500 _88501 _88502 a x b y c z).
Proof. exact (@lem17045 (a = x) (term61 _88500 _88501 b y c z)). Qed.
Lemma lem3406551 {_88500 _88501 _88502 : Type'} (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term182 _88500 _88501 _88502 a x b y c z) = (term181 _88500 _88501 _88502 a x b y c z).
Proof. exact (TRANS (@lem3406550 _88500 _88501 _88502 a x b y c z) (@lem3406549 _88500 _88501 _88502 a x b y c z)). Qed.
Lemma lem3406556 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term183 _88500 _88501 _88502 P x y z) = (term183 _88500 _88501 _88502 P x y z).
Proof. exact (eq_refl (term183 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3406557 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term184 _88500 _88501 _88502 P a x b y c z) = (term185 _88500 _88501 _88502 P a x b y c z).
Proof. exact (MK_COMB (@lem3406556 _88500 _88501 _88502 P x y z) (@lem3406551 _88500 _88501 _88502 a x b y c z)). Qed.
Lemma lem3406558 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term186 _88500 _88501 _88502 P a x b y c z) = (term184 _88500 _88501 _88502 P a x b y c z).
Proof. exact (@lem17045 (P x y z) (term63 _88500 _88501 _88502 a x b y c z)). Qed.
Lemma lem3406559 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term186 _88500 _88501 _88502 P a x b y c z) = (term185 _88500 _88501 _88502 P a x b y c z).
Proof. exact (TRANS (@lem3406558 _88500 _88501 _88502 P a x b y c z) (@lem3406557 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406562 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term65 _88500 _88501 _88502 P a x b y c z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term65 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406563 {_88500 : Type'} (P : _88500 -> Prop) : (term187 _88500 P) = (term188 _88500 P).
Proof. exact (@lem18394 _88500 P). Qed.
Lemma lem3406564 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term189 _88500 _88501 _88502 P a x b y c) = (term190 _88500 _88501 _88502 P a x b y c).
Proof. exact (@lem3406563 _88500 (term67 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406565 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term191 _88500 _88501 _88502 P a x b y c z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term191 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406567 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term192 _88500 _88501 _88502 P a x b y c z) = (term186 _88500 _88501 _88502 P a x b y c z).
Proof. exact (MK_COMB (@lem3406566) (@lem3406565 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406568 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term192 _88500 _88501 _88502 P a x b y c z) = (term185 _88500 _88501 _88502 P a x b y c z).
Proof. exact (TRANS (@lem3406567 _88500 _88501 _88502 P a x b y c z) (@lem3406559 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406569 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term193 _88500 _88501 _88502 P a x b y c) = (term194 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3406568 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406570 {_88500 : Type'} : (@all _88500) = (@all _88500).
Proof. exact (eq_refl (@all _88500)). Qed.
Lemma lem3406571 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term190 _88500 _88501 _88502 P a x b y c) = (term195 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3406570 _88500) (@lem3406569 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406572 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term189 _88500 _88501 _88502 P a x b y c) = (term195 _88500 _88501 _88502 P a x b y c).
Proof. exact (TRANS (@lem3406564 _88500 _88501 _88502 P a x b y c) (@lem3406571 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406573 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term67 _88500 _88501 _88502 P a x b y c) = (term67 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3406562 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3406574 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406575 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term69 _88500 _88501 _88502 P a x b y c) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3406574 _88500) (@lem3406573 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406576 {_88501 : Type'} (P : _88501 -> Prop) : (term187 _88501 P) = (term188 _88501 P).
Proof. exact (@lem18394 _88501 P). Qed.
Lemma lem3406577 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term196 _88500 _88501 _88502 P a x b c) = (term197 _88500 _88501 _88502 P a x b c).
Proof. exact (@lem3406576 _88501 (term71 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406578 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term198 _88500 _88501 _88502 P a x b c y) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (eq_refl (term198 _88500 _88501 _88502 P a x b c y)). Qed.
Lemma lem3406579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406580 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term199 _88500 _88501 _88502 P a x b c y) = (term189 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3406579) (@lem3406578 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406581 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term199 _88500 _88501 _88502 P a x b c y) = (term195 _88500 _88501 _88502 P a x b y c).
Proof. exact (TRANS (@lem3406580 _88500 _88501 _88502 P a x b y c) (@lem3406572 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406582 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term200 _88500 _88501 _88502 P a x b c) = (term201 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3406581 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406583 {_88501 : Type'} : (@all _88501) = (@all _88501).
Proof. exact (eq_refl (@all _88501)). Qed.
Lemma lem3406584 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term197 _88500 _88501 _88502 P a x b c) = (term202 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3406583 _88501) (@lem3406582 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406585 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term196 _88500 _88501 _88502 P a x b c) = (term202 _88500 _88501 _88502 P a x b c).
Proof. exact (TRANS (@lem3406577 _88500 _88501 _88502 P a x b c) (@lem3406584 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406586 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term71 _88500 _88501 _88502 P a x b c) = (term71 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3406575 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3406587 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3406588 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term73 _88500 _88501 _88502 P a x b c) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3406587 _88501) (@lem3406586 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406589 {_88502 : Type'} (P : _88502 -> Prop) : (term187 _88502 P) = (term188 _88502 P).
Proof. exact (@lem18394 _88502 P). Qed.
Lemma lem3406590 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term203 _88500 _88501 _88502 P a b c) = (term204 _88500 _88501 _88502 P a b c).
Proof. exact (@lem3406589 _88502 (term75 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406591 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term205 _88500 _88501 _88502 P a b c x) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (eq_refl (term205 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3406592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406593 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term206 _88500 _88501 _88502 P a b c x) = (term196 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3406592) (@lem3406591 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406594 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term206 _88500 _88501 _88502 P a b c x) = (term202 _88500 _88501 _88502 P a x b c).
Proof. exact (TRANS (@lem3406593 _88500 _88501 _88502 P a x b c) (@lem3406585 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406595 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term207 _88500 _88501 _88502 P a b c) = (term208 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3406594 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406596 {_88502 : Type'} : (@all _88502) = (@all _88502).
Proof. exact (eq_refl (@all _88502)). Qed.
Lemma lem3406597 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term204 _88500 _88501 _88502 P a b c) = (term209 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406596 _88502) (@lem3406595 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406598 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term203 _88500 _88501 _88502 P a b c) = (term209 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3406590 _88500 _88501 _88502 P a b c) (@lem3406597 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406599 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term75 _88500 _88501 _88502 P a b c) = (term75 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3406588 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3406600 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3406601 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term76 _88500 _88501 _88502 P a b c) = (term76 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406600 _88502) (@lem3406599 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406602 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406603 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3406604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406605 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term211 _88500 _88501 _88502 P a b c) = (term212 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406604) (@lem3406598 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406606 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term213 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406605 _88500 _88501 _88502 P a b c) (@lem3406603 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406608 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term215 _88500 _88501 _88502 P a b c) = (term215 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406607) (@lem3406601 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406609 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term216 _88500 _88501 _88502 P a b c) = (term216 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406608 _88500 _88501 _88502 P a b c) (@lem3406602 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406611 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term217 _88500 _88501 _88502 P a b c) = (term217 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406610) (@lem3406609 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406612 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term218 _88500 _88501 _88502 P a b c) = (term219 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406611 _88500 _88501 _88502 P a b c) (@lem3406606 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406613 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term220 _88500 _88501 _88502 P a b c) = (term218 _88500 _88501 _88502 P a b c).
Proof. exact (@lem17646 (term76 _88500 _88501 _88502 P a b c) (P a b c)). Qed.
Lemma lem3406614 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term220 _88500 _88501 _88502 P a b c) = (term219 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3406613 _88500 _88501 _88502 P a b c) (@lem3406612 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406615 {_88500 : Type'} (P : _88500 -> Prop) : (term221 _88500 P) = (term222 _88500 P).
Proof. exact (@lem18392 _88500 P). Qed.
Lemma lem3406616 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term223 _88500 _88501 _88502 P a b) = (term224 _88500 _88501 _88502 P a b).
Proof. exact (@lem3406615 _88500 (term79 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406617 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term225 _88500 _88501 _88502 P a b c) = ((term76 _88500 _88501 _88502 P a b c) = (P a b c)).
Proof. exact (eq_refl (term225 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406619 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term226 _88500 _88501 _88502 P a b c) = (term220 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406618) (@lem3406617 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406620 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term226 _88500 _88501 _88502 P a b c) = (term219 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3406619 _88500 _88501 _88502 P a b c) (@lem3406614 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406621 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term227 _88500 _88501 _88502 P a b) = (term228 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3406620 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406622 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406623 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term224 _88500 _88501 _88502 P a b) = (term229 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406622 _88500) (@lem3406621 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406624 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term223 _88500 _88501 _88502 P a b) = (term229 _88500 _88501 _88502 P a b).
Proof. exact (TRANS (@lem3406616 _88500 _88501 _88502 P a b) (@lem3406623 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406625 {_88501 : Type'} (P : _88501 -> Prop) : (term221 _88501 P) = (term222 _88501 P).
Proof. exact (@lem18392 _88501 P). Qed.
Lemma lem3406626 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term230 _88500 _88501 _88502 P a) = (term231 _88500 _88501 _88502 P a).
Proof. exact (@lem3406625 _88501 (term83 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406627 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term232 _88500 _88501 _88502 P a b) = (term81 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term232 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406629 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term233 _88500 _88501 _88502 P a b) = (term223 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406628) (@lem3406627 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406630 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term233 _88500 _88501 _88502 P a b) = (term229 _88500 _88501 _88502 P a b).
Proof. exact (TRANS (@lem3406629 _88500 _88501 _88502 P a b) (@lem3406624 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406631 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term234 _88500 _88501 _88502 P a) = (term235 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3406630 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406632 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3406633 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term231 _88500 _88501 _88502 P a) = (term236 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3406632 _88501) (@lem3406631 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406634 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term230 _88500 _88501 _88502 P a) = (term236 _88500 _88501 _88502 P a).
Proof. exact (TRANS (@lem3406626 _88500 _88501 _88502 P a) (@lem3406633 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406635 {_88502 : Type'} (P : _88502 -> Prop) : (term221 _88502 P) = (term222 _88502 P).
Proof. exact (@lem18392 _88502 P). Qed.
Lemma lem3406636 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term237 _88500 _88501 _88502 P) = (term238 _88500 _88501 _88502 P).
Proof. exact (@lem3406635 _88502 (term87 _88500 _88501 _88502 P)). Qed.
Lemma lem3406637 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term239 _88500 _88501 _88502 P a) = (term85 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term239 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406639 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term240 _88500 _88501 _88502 P a) = (term230 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3406638) (@lem3406637 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406640 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term240 _88500 _88501 _88502 P a) = (term236 _88500 _88501 _88502 P a).
Proof. exact (TRANS (@lem3406639 _88500 _88501 _88502 P a) (@lem3406634 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406641 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term241 _88500 _88501 _88502 P) = (term242 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3406640 _88500 _88501 _88502 P a)). Qed.
Lemma lem3406642 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3406643 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term238 _88500 _88501 _88502 P) = (term243 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3406642 _88502) (@lem3406641 _88500 _88501 _88502 P)). Qed.
Lemma lem3406644 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term237 _88500 _88501 _88502 P) = (term243 _88500 _88501 _88502 P).
Proof. exact (TRANS (@lem3406636 _88500 _88501 _88502 P) (@lem3406643 _88500 _88501 _88502 P)). Qed.
Lemma lem3406645 {_88500 _88501 _88502 : Type'} (P : type871 _88500 _88501 _88502) : (term244 _88500 _88501 _88502 P) = (term245 _88500 _88501 _88502 P).
Proof. exact (@lem18392 (type1517 _88500 _88501 _88502) P). Qed.
Lemma lem3406646 {_88500 _88501 _88502 : Type'} : (term246 _88500 _88501 _88502) = (term247 _88500 _88501 _88502).
Proof. exact (@lem3406645 _88500 _88501 _88502 (term91 _88500 _88501 _88502)). Qed.
Lemma lem3406647 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term248 _88500 _88501 _88502 P) = (term89 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term248 _88500 _88501 _88502 P)). Qed.
Lemma lem3406648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406649 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term249 _88500 _88501 _88502 P) = (term237 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3406648) (@lem3406647 _88500 _88501 _88502 P)). Qed.
Lemma lem3406650 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term249 _88500 _88501 _88502 P) = (term243 _88500 _88501 _88502 P).
Proof. exact (TRANS (@lem3406649 _88500 _88501 _88502 P) (@lem3406644 _88500 _88501 _88502 P)). Qed.
Lemma lem3406651 {_88500 _88501 _88502 : Type'} : (term250 _88500 _88501 _88502) = (term251 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3406650 _88500 _88501 _88502 P)). Qed.
Lemma lem3406652 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3406653 {_88500 _88501 _88502 : Type'} : (term247 _88500 _88501 _88502) = (term252 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3406652 _88500 _88501 _88502) (@lem3406651 _88500 _88501 _88502)). Qed.
Lemma lem3406654 {_88500 _88501 _88502 : Type'} : (term246 _88500 _88501 _88502) = (term252 _88500 _88501 _88502).
Proof. exact (TRANS (@lem3406646 _88500 _88501 _88502) (@lem3406653 _88500 _88501 _88502)). Qed.
Lemma lem3406665 {_88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) : (term177 _88564 _88565 a x b y) = (term178 _88564 _88565 a x b y).
Proof. exact (@lem17045 (a = x) (b = y)). Qed.
Lemma lem3406669 {_88563 : Type'} (c : _88563) (z : _88563) : (term253 _88563 c z) = (term253 _88563 c z).
Proof. exact (eq_refl (term253 _88563 c z)). Qed.
Lemma lem3406671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406672 {_88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) : (term254 _88564 _88565 a x b y) = (term255 _88564 _88565 a x b y).
Proof. exact (MK_COMB (@lem3406671) (@lem3406665 _88564 _88565 a x b y)). Qed.
Lemma lem3406673 {_88563 _88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term256 _88563 _88564 _88565 a x b y c z) = (term257 _88563 _88564 _88565 a x b y c z).
Proof. exact (MK_COMB (@lem3406672 _88564 _88565 a x b y) (@lem3406669 _88563 c z)). Qed.
Lemma lem3406674 {_88563 _88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term258 _88563 _88564 _88565 a x b y c z) = (term256 _88563 _88564 _88565 a x b y c z).
Proof. exact (@lem17045 (term61 _88564 _88565 a x b y) (c = z)). Qed.
Lemma lem3406675 {_88563 _88564 _88565 : Type'} (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term258 _88563 _88564 _88565 a x b y c z) = (term257 _88563 _88564 _88565 a x b y c z).
Proof. exact (TRANS (@lem3406674 _88563 _88564 _88565 a x b y c z) (@lem3406673 _88563 _88564 _88565 a x b y c z)). Qed.
Lemma lem3406680 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (x : _88565) (y : _88564) (z : _88563) : (term183 _88563 _88564 _88565 P x y z) = (term183 _88563 _88564 _88565 P x y z).
Proof. exact (eq_refl (term183 _88563 _88564 _88565 P x y z)). Qed.
Lemma lem3406681 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term259 _88563 _88564 _88565 P a x b y c z) = (term260 _88563 _88564 _88565 P a x b y c z).
Proof. exact (MK_COMB (@lem3406680 _88563 _88564 _88565 P x y z) (@lem3406675 _88563 _88564 _88565 a x b y c z)). Qed.
Lemma lem3406682 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term261 _88563 _88564 _88565 P a x b y c z) = (term259 _88563 _88564 _88565 P a x b y c z).
Proof. exact (@lem17045 (P x y z) (term137 _88563 _88564 _88565 a x b y c z)). Qed.
Lemma lem3406683 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term261 _88563 _88564 _88565 P a x b y c z) = (term260 _88563 _88564 _88565 P a x b y c z).
Proof. exact (TRANS (@lem3406682 _88563 _88564 _88565 P a x b y c z) (@lem3406681 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406686 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term138 _88563 _88564 _88565 P a x b y c z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (eq_refl (term138 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406687 {_88563 : Type'} (P : _88563 -> Prop) : (term187 _88563 P) = (term188 _88563 P).
Proof. exact (@lem18394 _88563 P). Qed.
Lemma lem3406688 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term262 _88563 _88564 _88565 P a x b y c) = (term263 _88563 _88564 _88565 P a x b y c).
Proof. exact (@lem3406687 _88563 (term140 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406689 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term264 _88563 _88564 _88565 P a x b y c z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (eq_refl (term264 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406691 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term265 _88563 _88564 _88565 P a x b y c z) = (term261 _88563 _88564 _88565 P a x b y c z).
Proof. exact (MK_COMB (@lem3406690) (@lem3406689 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406692 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term265 _88563 _88564 _88565 P a x b y c z) = (term260 _88563 _88564 _88565 P a x b y c z).
Proof. exact (TRANS (@lem3406691 _88563 _88564 _88565 P a x b y c z) (@lem3406683 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406693 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term266 _88563 _88564 _88565 P a x b y c) = (term267 _88563 _88564 _88565 P a x b y c).
Proof. exact (fun_ext (fun z : _88563 => @lem3406692 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406694 {_88563 : Type'} : (@all _88563) = (@all _88563).
Proof. exact (eq_refl (@all _88563)). Qed.
Lemma lem3406695 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term263 _88563 _88564 _88565 P a x b y c) = (term268 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3406694 _88563) (@lem3406693 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406696 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term262 _88563 _88564 _88565 P a x b y c) = (term268 _88563 _88564 _88565 P a x b y c).
Proof. exact (TRANS (@lem3406688 _88563 _88564 _88565 P a x b y c) (@lem3406695 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406697 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term140 _88563 _88564 _88565 P a x b y c) = (term140 _88563 _88564 _88565 P a x b y c).
Proof. exact (fun_ext (fun z : _88563 => @lem3406686 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3406698 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3406699 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term142 _88563 _88564 _88565 P a x b y c) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3406698 _88563) (@lem3406697 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406700 {_88564 : Type'} (P : _88564 -> Prop) : (term187 _88564 P) = (term188 _88564 P).
Proof. exact (@lem18394 _88564 P). Qed.
Lemma lem3406701 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term269 _88563 _88564 _88565 P a x b c) = (term270 _88563 _88564 _88565 P a x b c).
Proof. exact (@lem3406700 _88564 (term144 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406702 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term271 _88563 _88564 _88565 P a x b c y) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (eq_refl (term271 _88563 _88564 _88565 P a x b c y)). Qed.
Lemma lem3406703 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406704 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term272 _88563 _88564 _88565 P a x b c y) = (term262 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3406703) (@lem3406702 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406705 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term272 _88563 _88564 _88565 P a x b c y) = (term268 _88563 _88564 _88565 P a x b y c).
Proof. exact (TRANS (@lem3406704 _88563 _88564 _88565 P a x b y c) (@lem3406696 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406706 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term273 _88563 _88564 _88565 P a x b c) = (term274 _88563 _88564 _88565 P a x b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3406705 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406707 {_88564 : Type'} : (@all _88564) = (@all _88564).
Proof. exact (eq_refl (@all _88564)). Qed.
Lemma lem3406708 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term270 _88563 _88564 _88565 P a x b c) = (term275 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3406707 _88564) (@lem3406706 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406709 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term269 _88563 _88564 _88565 P a x b c) = (term275 _88563 _88564 _88565 P a x b c).
Proof. exact (TRANS (@lem3406701 _88563 _88564 _88565 P a x b c) (@lem3406708 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406710 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term144 _88563 _88564 _88565 P a x b c) = (term144 _88563 _88564 _88565 P a x b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3406699 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3406711 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3406712 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term146 _88563 _88564 _88565 P a x b c) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3406711 _88564) (@lem3406710 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406713 {_88565 : Type'} (P : _88565 -> Prop) : (term187 _88565 P) = (term188 _88565 P).
Proof. exact (@lem18394 _88565 P). Qed.
Lemma lem3406714 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term276 _88563 _88564 _88565 P a b c) = (term277 _88563 _88564 _88565 P a b c).
Proof. exact (@lem3406713 _88565 (term148 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406715 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term278 _88563 _88564 _88565 P a b c x) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (eq_refl (term278 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3406716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406717 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term279 _88563 _88564 _88565 P a b c x) = (term269 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3406716) (@lem3406715 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406718 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term279 _88563 _88564 _88565 P a b c x) = (term275 _88563 _88564 _88565 P a x b c).
Proof. exact (TRANS (@lem3406717 _88563 _88564 _88565 P a x b c) (@lem3406709 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406719 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term280 _88563 _88564 _88565 P a b c) = (term281 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3406718 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406720 {_88565 : Type'} : (@all _88565) = (@all _88565).
Proof. exact (eq_refl (@all _88565)). Qed.
Lemma lem3406721 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term277 _88563 _88564 _88565 P a b c) = (term282 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406720 _88565) (@lem3406719 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406722 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term276 _88563 _88564 _88565 P a b c) = (term282 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3406714 _88563 _88564 _88565 P a b c) (@lem3406721 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406723 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term148 _88563 _88564 _88565 P a b c) = (term148 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3406712 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3406724 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3406725 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term149 _88563 _88564 _88565 P a b c) = (term149 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406724 _88565) (@lem3406723 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406726 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406727 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3406728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406729 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term283 _88563 _88564 _88565 P a b c) = (term284 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406728) (@lem3406722 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406730 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term285 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406729 _88563 _88564 _88565 P a b c) (@lem3406727 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3406732 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term287 _88563 _88564 _88565 P a b c) = (term287 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406731) (@lem3406725 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406733 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term288 _88563 _88564 _88565 P a b c) = (term288 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406732 _88563 _88564 _88565 P a b c) (@lem3406726 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406735 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term289 _88563 _88564 _88565 P a b c) = (term289 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406734) (@lem3406733 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406736 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term290 _88563 _88564 _88565 P a b c) = (term291 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406735 _88563 _88564 _88565 P a b c) (@lem3406730 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406737 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term292 _88563 _88564 _88565 P a b c) = (term290 _88563 _88564 _88565 P a b c).
Proof. exact (@lem17646 (term149 _88563 _88564 _88565 P a b c) (P a b c)). Qed.
Lemma lem3406738 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term292 _88563 _88564 _88565 P a b c) = (term291 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3406737 _88563 _88564 _88565 P a b c) (@lem3406736 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406739 {_88563 : Type'} (P : _88563 -> Prop) : (term221 _88563 P) = (term222 _88563 P).
Proof. exact (@lem18392 _88563 P). Qed.
Lemma lem3406740 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term293 _88563 _88564 _88565 P a b) = (term294 _88563 _88564 _88565 P a b).
Proof. exact (@lem3406739 _88563 (term152 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406741 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term295 _88563 _88564 _88565 P a b c) = ((term149 _88563 _88564 _88565 P a b c) = (P a b c)).
Proof. exact (eq_refl (term295 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406743 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term296 _88563 _88564 _88565 P a b c) = (term292 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3406742) (@lem3406741 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406744 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term296 _88563 _88564 _88565 P a b c) = (term291 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3406743 _88563 _88564 _88565 P a b c) (@lem3406738 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406745 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term297 _88563 _88564 _88565 P a b) = (term298 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3406744 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3406746 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3406747 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term294 _88563 _88564 _88565 P a b) = (term299 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3406746 _88563) (@lem3406745 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406748 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term293 _88563 _88564 _88565 P a b) = (term299 _88563 _88564 _88565 P a b).
Proof. exact (TRANS (@lem3406740 _88563 _88564 _88565 P a b) (@lem3406747 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406749 {_88564 : Type'} (P : _88564 -> Prop) : (term221 _88564 P) = (term222 _88564 P).
Proof. exact (@lem18392 _88564 P). Qed.
Lemma lem3406750 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term300 _88563 _88564 _88565 P a) = (term301 _88563 _88564 _88565 P a).
Proof. exact (@lem3406749 _88564 (term156 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406751 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term302 _88563 _88564 _88565 P a b) = (term154 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term302 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406752 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406753 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term303 _88563 _88564 _88565 P a b) = (term293 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3406752) (@lem3406751 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406754 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term303 _88563 _88564 _88565 P a b) = (term299 _88563 _88564 _88565 P a b).
Proof. exact (TRANS (@lem3406753 _88563 _88564 _88565 P a b) (@lem3406748 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406755 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term304 _88563 _88564 _88565 P a) = (term305 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3406754 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3406756 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3406757 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term301 _88563 _88564 _88565 P a) = (term306 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3406756 _88564) (@lem3406755 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406758 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term300 _88563 _88564 _88565 P a) = (term306 _88563 _88564 _88565 P a).
Proof. exact (TRANS (@lem3406750 _88563 _88564 _88565 P a) (@lem3406757 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406759 {_88565 : Type'} (P : _88565 -> Prop) : (term221 _88565 P) = (term222 _88565 P).
Proof. exact (@lem18392 _88565 P). Qed.
Lemma lem3406760 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term307 _88563 _88564 _88565 P) = (term308 _88563 _88564 _88565 P).
Proof. exact (@lem3406759 _88565 (term160 _88563 _88564 _88565 P)). Qed.
Lemma lem3406761 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term309 _88563 _88564 _88565 P a) = (term158 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term309 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406763 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term310 _88563 _88564 _88565 P a) = (term300 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3406762) (@lem3406761 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406764 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term310 _88563 _88564 _88565 P a) = (term306 _88563 _88564 _88565 P a).
Proof. exact (TRANS (@lem3406763 _88563 _88564 _88565 P a) (@lem3406758 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406765 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term311 _88563 _88564 _88565 P) = (term312 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3406764 _88563 _88564 _88565 P a)). Qed.
Lemma lem3406766 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3406767 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term308 _88563 _88564 _88565 P) = (term313 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3406766 _88565) (@lem3406765 _88563 _88564 _88565 P)). Qed.
Lemma lem3406768 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term307 _88563 _88564 _88565 P) = (term313 _88563 _88564 _88565 P).
Proof. exact (TRANS (@lem3406760 _88563 _88564 _88565 P) (@lem3406767 _88563 _88564 _88565 P)). Qed.
Lemma lem3406769 {_88563 _88564 _88565 : Type'} (P : type871 _88563 _88564 _88565) : (term244 _88563 _88564 _88565 P) = (term245 _88563 _88564 _88565 P).
Proof. exact (@lem18392 (type1517 _88563 _88564 _88565) P). Qed.
Lemma lem3406770 {_88563 _88564 _88565 : Type'} : (term314 _88563 _88564 _88565) = (term315 _88563 _88564 _88565).
Proof. exact (@lem3406769 _88563 _88564 _88565 (term164 _88563 _88564 _88565)). Qed.
Lemma lem3406771 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term316 _88563 _88564 _88565 P) = (term162 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term316 _88563 _88564 _88565 P)). Qed.
Lemma lem3406772 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3406773 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term317 _88563 _88564 _88565 P) = (term307 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3406772) (@lem3406771 _88563 _88564 _88565 P)). Qed.
Lemma lem3406774 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term317 _88563 _88564 _88565 P) = (term313 _88563 _88564 _88565 P).
Proof. exact (TRANS (@lem3406773 _88563 _88564 _88565 P) (@lem3406768 _88563 _88564 _88565 P)). Qed.
Lemma lem3406775 {_88563 _88564 _88565 : Type'} : (term318 _88563 _88564 _88565) = (term319 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3406774 _88563 _88564 _88565 P)). Qed.
Lemma lem3406776 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3406777 {_88563 _88564 _88565 : Type'} : (term315 _88563 _88564 _88565) = (term320 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3406776 _88563 _88564 _88565) (@lem3406775 _88563 _88564 _88565)). Qed.
Lemma lem3406778 {_88563 _88564 _88565 : Type'} : (term314 _88563 _88564 _88565) = (term320 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3406770 _88563 _88564 _88565) (@lem3406777 _88563 _88564 _88565)). Qed.
Lemma lem3406779 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406780 {_88500 _88501 _88502 : Type'} : (term321 _88500 _88501 _88502) = (term322 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3406779) (@lem3406654 _88500 _88501 _88502)). Qed.
Lemma lem3406781 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term323 _88500 _88501 _88502 _88563 _88564 _88565) = (term324 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3406780 _88500 _88501 _88502) (@lem3406778 _88563 _88564 _88565)). Qed.
Lemma lem3406782 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term171 _88500 _88501 _88502 _88563 _88564 _88565) = (term323 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem17045 (term93 _88500 _88501 _88502) (term166 _88563 _88564 _88565)). Qed.
Lemma lem3406783 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term171 _88500 _88501 _88502 _88563 _88564 _88565) = (term324 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3406782 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3406781 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3406797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3406798 {_88500 : Type'} (P : _88500 -> Prop) (Q : _88500 -> Prop) : (term325 _88500 P Q) = (term326 _88500 P Q).
Proof. exact (@lem3406797 _88500 P Q). Qed.
Lemma lem3406799 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term327 _88500 _88501 _88502 P a b) = (term328 _88500 _88501 _88502 P a b).
Proof. exact (@lem3406798 _88500 (term329 _88500 _88501 _88502 P a b) (term330 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406800 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term331 _88500 _88501 _88502 P a b c) = (term216 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term331 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406802 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term332 _88500 _88501 _88502 P a b c) = (term217 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406801) (@lem3406800 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406803 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term333 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term333 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406804 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term334 _88500 _88501 _88502 P a b c) = (term219 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3406802 _88500 _88501 _88502 P a b c) (@lem3406803 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406805 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term335 _88500 _88501 _88502 P a b) = (term228 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3406804 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406806 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406807 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term327 _88500 _88501 _88502 P a b) = (term229 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406806 _88500) (@lem3406805 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3406809 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term336 _88500 _88501 _88502 P a b) = (term337 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406808) (@lem3406807 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406810 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term331 _88500 _88501 _88502 P a b c) = (term216 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term331 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406811 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term338 _88500 _88501 _88502 P a b) = (term329 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3406810 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406812 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406813 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term339 _88500 _88501 _88502 P a b) = (term340 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406812 _88500) (@lem3406811 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3406815 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term341 _88500 _88501 _88502 P a b) = (term342 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406814) (@lem3406813 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406816 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term333 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term333 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406817 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term343 _88500 _88501 _88502 P a b) = (term330 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3406816 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3406818 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3406819 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term344 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406818 _88500) (@lem3406817 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406820 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term328 _88500 _88501 _88502 P a b) = (term346 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3406815 _88500 _88501 _88502 P a b) (@lem3406819 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406821 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : ((term327 _88500 _88501 _88502 P a b) = (term328 _88500 _88501 _88502 P a b)) = ((term229 _88500 _88501 _88502 P a b) = (term346 _88500 _88501 _88502 P a b)).
Proof. exact (MK_COMB (@lem3406809 _88500 _88501 _88502 P a b) (@lem3406820 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3406822 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term229 _88500 _88501 _88502 P a b) = (term346 _88500 _88501 _88502 P a b).
Proof. exact (EQ_MP (@lem3406821 _88500 _88501 _88502 P a b) (@lem3406799 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407031 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term235 _88500 _88501 _88502 P a) = (term347 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3406822 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407032 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3407033 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term236 _88500 _88501 _88502 P a) = (term348 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407032 _88501) (@lem3407031 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407035 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3407036 {_88501 : Type'} (P : _88501 -> Prop) (Q : _88501 -> Prop) : (term325 _88501 P Q) = (term326 _88501 P Q).
Proof. exact (@lem3407035 _88501 P Q). Qed.
Lemma lem3407037 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term349 _88500 _88501 _88502 P a) = (term350 _88500 _88501 _88502 P a).
Proof. exact (@lem3407036 _88501 (term351 _88500 _88501 _88502 P a) (term352 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407038 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term353 _88500 _88501 _88502 P a b) = (term340 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term353 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407040 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term354 _88500 _88501 _88502 P a b) = (term342 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3407039) (@lem3407038 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407041 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term355 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term355 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407042 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term356 _88500 _88501 _88502 P a b) = (term346 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3407040 _88500 _88501 _88502 P a b) (@lem3407041 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407043 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term357 _88500 _88501 _88502 P a) = (term347 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3407042 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407044 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3407045 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term349 _88500 _88501 _88502 P a) = (term348 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407044 _88501) (@lem3407043 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3407047 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term358 _88500 _88501 _88502 P a) = (term359 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407046) (@lem3407045 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407048 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term353 _88500 _88501 _88502 P a b) = (term340 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term353 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407049 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term360 _88500 _88501 _88502 P a) = (term351 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3407048 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407050 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3407051 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term361 _88500 _88501 _88502 P a) = (term362 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407050 _88501) (@lem3407049 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407053 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term363 _88500 _88501 _88502 P a) = (term364 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407052) (@lem3407051 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407054 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term355 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term355 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407055 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term365 _88500 _88501 _88502 P a) = (term352 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3407054 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3407056 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3407057 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term366 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407056 _88501) (@lem3407055 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407058 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term350 _88500 _88501 _88502 P a) = (term368 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407053 _88500 _88501 _88502 P a) (@lem3407057 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407059 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : ((term349 _88500 _88501 _88502 P a) = (term350 _88500 _88501 _88502 P a)) = ((term348 _88500 _88501 _88502 P a) = (term368 _88500 _88501 _88502 P a)).
Proof. exact (MK_COMB (@lem3407047 _88500 _88501 _88502 P a) (@lem3407058 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407060 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term348 _88500 _88501 _88502 P a) = (term368 _88500 _88501 _88502 P a).
Proof. exact (EQ_MP (@lem3407059 _88500 _88501 _88502 P a) (@lem3407037 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407277 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term236 _88500 _88501 _88502 P a) = (term368 _88500 _88501 _88502 P a).
Proof. exact (TRANS (@lem3407033 _88500 _88501 _88502 P a) (@lem3407060 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407278 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term242 _88500 _88501 _88502 P) = (term369 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3407277 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407279 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3407280 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term243 _88500 _88501 _88502 P) = (term370 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407279 _88502) (@lem3407278 _88500 _88501 _88502 P)). Qed.
Lemma lem3407282 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3407283 {_88502 : Type'} (P : _88502 -> Prop) (Q : _88502 -> Prop) : (term325 _88502 P Q) = (term326 _88502 P Q).
Proof. exact (@lem3407282 _88502 P Q). Qed.
Lemma lem3407284 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term371 _88500 _88501 _88502 P) = (term372 _88500 _88501 _88502 P).
Proof. exact (@lem3407283 _88502 (term373 _88500 _88501 _88502 P) (term374 _88500 _88501 _88502 P)). Qed.
Lemma lem3407285 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term375 _88500 _88501 _88502 P a) = (term362 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term375 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407287 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term376 _88500 _88501 _88502 P a) = (term364 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407286) (@lem3407285 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407288 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term377 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term377 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407289 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term378 _88500 _88501 _88502 P a) = (term368 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3407287 _88500 _88501 _88502 P a) (@lem3407288 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407290 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term379 _88500 _88501 _88502 P) = (term369 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3407289 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407291 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3407292 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term371 _88500 _88501 _88502 P) = (term370 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407291 _88502) (@lem3407290 _88500 _88501 _88502 P)). Qed.
Lemma lem3407293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3407294 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term380 _88500 _88501 _88502 P) = (term381 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407293) (@lem3407292 _88500 _88501 _88502 P)). Qed.
Lemma lem3407295 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term375 _88500 _88501 _88502 P a) = (term362 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term375 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407296 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term382 _88500 _88501 _88502 P) = (term373 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3407295 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407297 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3407298 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term383 _88500 _88501 _88502 P) = (term384 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407297 _88502) (@lem3407296 _88500 _88501 _88502 P)). Qed.
Lemma lem3407299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407300 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term385 _88500 _88501 _88502 P) = (term386 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407299) (@lem3407298 _88500 _88501 _88502 P)). Qed.
Lemma lem3407301 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term377 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term377 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407302 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term387 _88500 _88501 _88502 P) = (term374 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3407301 _88500 _88501 _88502 P a)). Qed.
Lemma lem3407303 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3407304 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term388 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407303 _88502) (@lem3407302 _88500 _88501 _88502 P)). Qed.
Lemma lem3407305 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term372 _88500 _88501 _88502 P) = (term390 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407300 _88500 _88501 _88502 P) (@lem3407304 _88500 _88501 _88502 P)). Qed.
Lemma lem3407306 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : ((term371 _88500 _88501 _88502 P) = (term372 _88500 _88501 _88502 P)) = ((term370 _88500 _88501 _88502 P) = (term390 _88500 _88501 _88502 P)).
Proof. exact (MK_COMB (@lem3407294 _88500 _88501 _88502 P) (@lem3407305 _88500 _88501 _88502 P)). Qed.
Lemma lem3407307 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term370 _88500 _88501 _88502 P) = (term390 _88500 _88501 _88502 P).
Proof. exact (EQ_MP (@lem3407306 _88500 _88501 _88502 P) (@lem3407284 _88500 _88501 _88502 P)). Qed.
Lemma lem3407532 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term243 _88500 _88501 _88502 P) = (term390 _88500 _88501 _88502 P).
Proof. exact (TRANS (@lem3407280 _88500 _88501 _88502 P) (@lem3407307 _88500 _88501 _88502 P)). Qed.
Lemma lem3407533 {_88500 _88501 _88502 : Type'} : (term251 _88500 _88501 _88502) = (term391 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3407532 _88500 _88501 _88502 P)). Qed.
Lemma lem3407534 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3407535 {_88500 _88501 _88502 : Type'} : (term252 _88500 _88501 _88502) = (term392 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407534 _88500 _88501 _88502) (@lem3407533 _88500 _88501 _88502)). Qed.
Lemma lem3407537 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3407538 {_88500 _88501 _88502 : Type'} (P : type871 _88500 _88501 _88502) (Q : type871 _88500 _88501 _88502) : (term393 _88500 _88501 _88502 P Q) = (term394 _88500 _88501 _88502 P Q).
Proof. exact (@lem3407537 (type1517 _88500 _88501 _88502) P Q). Qed.
Lemma lem3407539 {_88500 _88501 _88502 : Type'} : (term395 _88500 _88501 _88502) = (term396 _88500 _88501 _88502).
Proof. exact (@lem3407538 _88500 _88501 _88502 (term397 _88500 _88501 _88502) (term398 _88500 _88501 _88502)). Qed.
Lemma lem3407540 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term399 _88500 _88501 _88502 P) = (term384 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term399 _88500 _88501 _88502 P)). Qed.
Lemma lem3407541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407542 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term400 _88500 _88501 _88502 P) = (term386 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407541) (@lem3407540 _88500 _88501 _88502 P)). Qed.
Lemma lem3407543 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term401 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term401 _88500 _88501 _88502 P)). Qed.
Lemma lem3407544 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term402 _88500 _88501 _88502 P) = (term390 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3407542 _88500 _88501 _88502 P) (@lem3407543 _88500 _88501 _88502 P)). Qed.
Lemma lem3407545 {_88500 _88501 _88502 : Type'} : (term403 _88500 _88501 _88502) = (term391 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3407544 _88500 _88501 _88502 P)). Qed.
Lemma lem3407546 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3407547 {_88500 _88501 _88502 : Type'} : (term395 _88500 _88501 _88502) = (term392 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407546 _88500 _88501 _88502) (@lem3407545 _88500 _88501 _88502)). Qed.
Lemma lem3407548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3407549 {_88500 _88501 _88502 : Type'} : (term404 _88500 _88501 _88502) = (term405 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407548) (@lem3407547 _88500 _88501 _88502)). Qed.
Lemma lem3407550 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term399 _88500 _88501 _88502 P) = (term384 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term399 _88500 _88501 _88502 P)). Qed.
Lemma lem3407551 {_88500 _88501 _88502 : Type'} : (term406 _88500 _88501 _88502) = (term397 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3407550 _88500 _88501 _88502 P)). Qed.
Lemma lem3407552 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3407553 {_88500 _88501 _88502 : Type'} : (term407 _88500 _88501 _88502) = (term408 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407552 _88500 _88501 _88502) (@lem3407551 _88500 _88501 _88502)). Qed.
Lemma lem3407554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407555 {_88500 _88501 _88502 : Type'} : (term409 _88500 _88501 _88502) = (term410 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407554) (@lem3407553 _88500 _88501 _88502)). Qed.
Lemma lem3407556 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term401 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term401 _88500 _88501 _88502 P)). Qed.
Lemma lem3407557 {_88500 _88501 _88502 : Type'} : (term411 _88500 _88501 _88502) = (term398 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3407556 _88500 _88501 _88502 P)). Qed.
Lemma lem3407558 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3407559 {_88500 _88501 _88502 : Type'} : (term412 _88500 _88501 _88502) = (term413 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407558 _88500 _88501 _88502) (@lem3407557 _88500 _88501 _88502)). Qed.
Lemma lem3407560 {_88500 _88501 _88502 : Type'} : (term396 _88500 _88501 _88502) = (term414 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407555 _88500 _88501 _88502) (@lem3407559 _88500 _88501 _88502)). Qed.
Lemma lem3407561 {_88500 _88501 _88502 : Type'} : ((term395 _88500 _88501 _88502) = (term396 _88500 _88501 _88502)) = ((term392 _88500 _88501 _88502) = (term414 _88500 _88501 _88502)).
Proof. exact (MK_COMB (@lem3407549 _88500 _88501 _88502) (@lem3407560 _88500 _88501 _88502)). Qed.
Lemma lem3407562 {_88500 _88501 _88502 : Type'} : (term392 _88500 _88501 _88502) = (term414 _88500 _88501 _88502).
Proof. exact (EQ_MP (@lem3407561 _88500 _88501 _88502) (@lem3407539 _88500 _88501 _88502)). Qed.
Lemma lem3407795 {_88500 _88501 _88502 : Type'} : (term252 _88500 _88501 _88502) = (term414 _88500 _88501 _88502).
Proof. exact (TRANS (@lem3407535 _88500 _88501 _88502) (@lem3407562 _88500 _88501 _88502)). Qed.
Lemma lem3407796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407797 {_88500 _88501 _88502 : Type'} : (term322 _88500 _88501 _88502) = (term415 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3407796) (@lem3407795 _88500 _88501 _88502)). Qed.
Lemma lem3407811 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3407812 {_88563 : Type'} (P : _88563 -> Prop) (Q : _88563 -> Prop) : (term325 _88563 P Q) = (term326 _88563 P Q).
Proof. exact (@lem3407811 _88563 P Q). Qed.
Lemma lem3407813 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term416 _88563 _88564 _88565 P a b) = (term417 _88563 _88564 _88565 P a b).
Proof. exact (@lem3407812 _88563 (term418 _88563 _88564 _88565 P a b) (term419 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407814 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term420 _88563 _88564 _88565 P a b c) = (term288 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term420 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407816 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term421 _88563 _88564 _88565 P a b c) = (term289 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3407815) (@lem3407814 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407817 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term422 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term422 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407818 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term423 _88563 _88564 _88565 P a b c) = (term291 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3407816 _88563 _88564 _88565 P a b c) (@lem3407817 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407819 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term424 _88563 _88564 _88565 P a b) = (term298 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3407818 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407820 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3407821 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term416 _88563 _88564 _88565 P a b) = (term299 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407820 _88563) (@lem3407819 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3407823 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term425 _88563 _88564 _88565 P a b) = (term426 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407822) (@lem3407821 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407824 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term420 _88563 _88564 _88565 P a b c) = (term288 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term420 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407825 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term427 _88563 _88564 _88565 P a b) = (term418 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3407824 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407826 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3407827 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term428 _88563 _88564 _88565 P a b) = (term429 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407826 _88563) (@lem3407825 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3407829 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term430 _88563 _88564 _88565 P a b) = (term431 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407828) (@lem3407827 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407830 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term422 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term422 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407831 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term432 _88563 _88564 _88565 P a b) = (term419 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3407830 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3407832 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3407833 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term433 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407832 _88563) (@lem3407831 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407834 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term417 _88563 _88564 _88565 P a b) = (term435 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3407829 _88563 _88564 _88565 P a b) (@lem3407833 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407835 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : ((term416 _88563 _88564 _88565 P a b) = (term417 _88563 _88564 _88565 P a b)) = ((term299 _88563 _88564 _88565 P a b) = (term435 _88563 _88564 _88565 P a b)).
Proof. exact (MK_COMB (@lem3407823 _88563 _88564 _88565 P a b) (@lem3407834 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3407836 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term299 _88563 _88564 _88565 P a b) = (term435 _88563 _88564 _88565 P a b).
Proof. exact (EQ_MP (@lem3407835 _88563 _88564 _88565 P a b) (@lem3407813 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408045 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term305 _88563 _88564 _88565 P a) = (term436 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3407836 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408046 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3408047 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term306 _88563 _88564 _88565 P a) = (term437 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408046 _88564) (@lem3408045 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408049 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3408050 {_88564 : Type'} (P : _88564 -> Prop) (Q : _88564 -> Prop) : (term325 _88564 P Q) = (term326 _88564 P Q).
Proof. exact (@lem3408049 _88564 P Q). Qed.
Lemma lem3408051 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term438 _88563 _88564 _88565 P a) = (term439 _88563 _88564 _88565 P a).
Proof. exact (@lem3408050 _88564 (term440 _88563 _88564 _88565 P a) (term441 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408052 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term442 _88563 _88564 _88565 P a b) = (term429 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term442 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408054 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term443 _88563 _88564 _88565 P a b) = (term431 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3408053) (@lem3408052 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408055 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term444 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term444 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408056 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term445 _88563 _88564 _88565 P a b) = (term435 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3408054 _88563 _88564 _88565 P a b) (@lem3408055 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408057 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term446 _88563 _88564 _88565 P a) = (term436 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3408056 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408058 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3408059 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term438 _88563 _88564 _88565 P a) = (term437 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408058 _88564) (@lem3408057 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408061 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term447 _88563 _88564 _88565 P a) = (term448 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408060) (@lem3408059 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408062 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term442 _88563 _88564 _88565 P a b) = (term429 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term442 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408063 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term449 _88563 _88564 _88565 P a) = (term440 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3408062 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408064 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3408065 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term450 _88563 _88564 _88565 P a) = (term451 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408064 _88564) (@lem3408063 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408067 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term452 _88563 _88564 _88565 P a) = (term453 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408066) (@lem3408065 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408068 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term444 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term444 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408069 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term454 _88563 _88564 _88565 P a) = (term441 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3408068 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3408070 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3408071 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term455 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408070 _88564) (@lem3408069 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408072 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term439 _88563 _88564 _88565 P a) = (term457 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408067 _88563 _88564 _88565 P a) (@lem3408071 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408073 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : ((term438 _88563 _88564 _88565 P a) = (term439 _88563 _88564 _88565 P a)) = ((term437 _88563 _88564 _88565 P a) = (term457 _88563 _88564 _88565 P a)).
Proof. exact (MK_COMB (@lem3408061 _88563 _88564 _88565 P a) (@lem3408072 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408074 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term437 _88563 _88564 _88565 P a) = (term457 _88563 _88564 _88565 P a).
Proof. exact (EQ_MP (@lem3408073 _88563 _88564 _88565 P a) (@lem3408051 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408291 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term306 _88563 _88564 _88565 P a) = (term457 _88563 _88564 _88565 P a).
Proof. exact (TRANS (@lem3408047 _88563 _88564 _88565 P a) (@lem3408074 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408292 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term312 _88563 _88564 _88565 P) = (term458 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3408291 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408293 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3408294 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term313 _88563 _88564 _88565 P) = (term459 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408293 _88565) (@lem3408292 _88563 _88564 _88565 P)). Qed.
Lemma lem3408296 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3408297 {_88565 : Type'} (P : _88565 -> Prop) (Q : _88565 -> Prop) : (term325 _88565 P Q) = (term326 _88565 P Q).
Proof. exact (@lem3408296 _88565 P Q). Qed.
Lemma lem3408298 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term460 _88563 _88564 _88565 P) = (term461 _88563 _88564 _88565 P).
Proof. exact (@lem3408297 _88565 (term462 _88563 _88564 _88565 P) (term463 _88563 _88564 _88565 P)). Qed.
Lemma lem3408299 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term464 _88563 _88564 _88565 P a) = (term451 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term464 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408301 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term465 _88563 _88564 _88565 P a) = (term453 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408300) (@lem3408299 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408302 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term466 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term466 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408303 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term467 _88563 _88564 _88565 P a) = (term457 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3408301 _88563 _88564 _88565 P a) (@lem3408302 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408304 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term468 _88563 _88564 _88565 P) = (term458 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3408303 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408305 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3408306 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term460 _88563 _88564 _88565 P) = (term459 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408305 _88565) (@lem3408304 _88563 _88564 _88565 P)). Qed.
Lemma lem3408307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408308 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term469 _88563 _88564 _88565 P) = (term470 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408307) (@lem3408306 _88563 _88564 _88565 P)). Qed.
Lemma lem3408309 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term464 _88563 _88564 _88565 P a) = (term451 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term464 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408310 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term471 _88563 _88564 _88565 P) = (term462 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3408309 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408311 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3408312 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term472 _88563 _88564 _88565 P) = (term473 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408311 _88565) (@lem3408310 _88563 _88564 _88565 P)). Qed.
Lemma lem3408313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408314 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term474 _88563 _88564 _88565 P) = (term475 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408313) (@lem3408312 _88563 _88564 _88565 P)). Qed.
Lemma lem3408315 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term466 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term466 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408316 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term476 _88563 _88564 _88565 P) = (term463 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3408315 _88563 _88564 _88565 P a)). Qed.
Lemma lem3408317 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3408318 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term477 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408317 _88565) (@lem3408316 _88563 _88564 _88565 P)). Qed.
Lemma lem3408319 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term461 _88563 _88564 _88565 P) = (term479 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408314 _88563 _88564 _88565 P) (@lem3408318 _88563 _88564 _88565 P)). Qed.
Lemma lem3408320 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : ((term460 _88563 _88564 _88565 P) = (term461 _88563 _88564 _88565 P)) = ((term459 _88563 _88564 _88565 P) = (term479 _88563 _88564 _88565 P)).
Proof. exact (MK_COMB (@lem3408308 _88563 _88564 _88565 P) (@lem3408319 _88563 _88564 _88565 P)). Qed.
Lemma lem3408321 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term459 _88563 _88564 _88565 P) = (term479 _88563 _88564 _88565 P).
Proof. exact (EQ_MP (@lem3408320 _88563 _88564 _88565 P) (@lem3408298 _88563 _88564 _88565 P)). Qed.
Lemma lem3408546 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term313 _88563 _88564 _88565 P) = (term479 _88563 _88564 _88565 P).
Proof. exact (TRANS (@lem3408294 _88563 _88564 _88565 P) (@lem3408321 _88563 _88564 _88565 P)). Qed.
Lemma lem3408547 {_88563 _88564 _88565 : Type'} : (term319 _88563 _88564 _88565) = (term480 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3408546 _88563 _88564 _88565 P)). Qed.
Lemma lem3408548 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3408549 {_88563 _88564 _88565 : Type'} : (term320 _88563 _88564 _88565) = (term481 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408548 _88563 _88564 _88565) (@lem3408547 _88563 _88564 _88565)). Qed.
Lemma lem3408551 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term325 A P Q) = (term326 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3408552 {_88563 _88564 _88565 : Type'} (P : type871 _88563 _88564 _88565) (Q : type871 _88563 _88564 _88565) : (term393 _88563 _88564 _88565 P Q) = (term394 _88563 _88564 _88565 P Q).
Proof. exact (@lem3408551 (type1517 _88563 _88564 _88565) P Q). Qed.
Lemma lem3408553 {_88563 _88564 _88565 : Type'} : (term482 _88563 _88564 _88565) = (term483 _88563 _88564 _88565).
Proof. exact (@lem3408552 _88563 _88564 _88565 (term484 _88563 _88564 _88565) (term485 _88563 _88564 _88565)). Qed.
Lemma lem3408554 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term486 _88563 _88564 _88565 P) = (term473 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term486 _88563 _88564 _88565 P)). Qed.
Lemma lem3408555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408556 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term487 _88563 _88564 _88565 P) = (term475 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408555) (@lem3408554 _88563 _88564 _88565 P)). Qed.
Lemma lem3408557 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term488 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term488 _88563 _88564 _88565 P)). Qed.
Lemma lem3408558 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term489 _88563 _88564 _88565 P) = (term479 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3408556 _88563 _88564 _88565 P) (@lem3408557 _88563 _88564 _88565 P)). Qed.
Lemma lem3408559 {_88563 _88564 _88565 : Type'} : (term490 _88563 _88564 _88565) = (term480 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3408558 _88563 _88564 _88565 P)). Qed.
Lemma lem3408560 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3408561 {_88563 _88564 _88565 : Type'} : (term482 _88563 _88564 _88565) = (term481 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408560 _88563 _88564 _88565) (@lem3408559 _88563 _88564 _88565)). Qed.
Lemma lem3408562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408563 {_88563 _88564 _88565 : Type'} : (term491 _88563 _88564 _88565) = (term492 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408562) (@lem3408561 _88563 _88564 _88565)). Qed.
Lemma lem3408564 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term486 _88563 _88564 _88565 P) = (term473 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term486 _88563 _88564 _88565 P)). Qed.
Lemma lem3408565 {_88563 _88564 _88565 : Type'} : (term493 _88563 _88564 _88565) = (term484 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3408564 _88563 _88564 _88565 P)). Qed.
Lemma lem3408566 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3408567 {_88563 _88564 _88565 : Type'} : (term494 _88563 _88564 _88565) = (term495 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408566 _88563 _88564 _88565) (@lem3408565 _88563 _88564 _88565)). Qed.
Lemma lem3408568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408569 {_88563 _88564 _88565 : Type'} : (term496 _88563 _88564 _88565) = (term497 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408568) (@lem3408567 _88563 _88564 _88565)). Qed.
Lemma lem3408570 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term488 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term488 _88563 _88564 _88565 P)). Qed.
Lemma lem3408571 {_88563 _88564 _88565 : Type'} : (term498 _88563 _88564 _88565) = (term485 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3408570 _88563 _88564 _88565 P)). Qed.
Lemma lem3408572 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3408573 {_88563 _88564 _88565 : Type'} : (term499 _88563 _88564 _88565) = (term500 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408572 _88563 _88564 _88565) (@lem3408571 _88563 _88564 _88565)). Qed.
Lemma lem3408574 {_88563 _88564 _88565 : Type'} : (term483 _88563 _88564 _88565) = (term501 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3408569 _88563 _88564 _88565) (@lem3408573 _88563 _88564 _88565)). Qed.
Lemma lem3408575 {_88563 _88564 _88565 : Type'} : ((term482 _88563 _88564 _88565) = (term483 _88563 _88564 _88565)) = ((term481 _88563 _88564 _88565) = (term501 _88563 _88564 _88565)).
Proof. exact (MK_COMB (@lem3408563 _88563 _88564 _88565) (@lem3408574 _88563 _88564 _88565)). Qed.
Lemma lem3408576 {_88563 _88564 _88565 : Type'} : (term481 _88563 _88564 _88565) = (term501 _88563 _88564 _88565).
Proof. exact (EQ_MP (@lem3408575 _88563 _88564 _88565) (@lem3408553 _88563 _88564 _88565)). Qed.
Lemma lem3408809 {_88563 _88564 _88565 : Type'} : (term320 _88563 _88564 _88565) = (term501 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3408549 _88563 _88564 _88565) (@lem3408576 _88563 _88564 _88565)). Qed.
Lemma lem3408810 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term324 _88500 _88501 _88502 _88563 _88564 _88565) = (term502 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3407797 _88500 _88501 _88502) (@lem3408809 _88563 _88564 _88565)). Qed.
Lemma lem3408812 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3408813 {_88502 : Type'} (P : _88502 -> Prop) (Q : Prop) : (term503 _88502 P Q) = (term504 _88502 P Q).
Proof. exact (@lem3408812 _88502 P Q). Qed.
Lemma lem3408814 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term505 _88500 _88501 _88502 P a b c) = (term506 _88500 _88501 _88502 P a b c).
Proof. exact (@lem3408813 _88502 (term75 _88500 _88501 _88502 P a b c) (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408815 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term205 _88500 _88501 _88502 P a b c x) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (eq_refl (term205 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3408816 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term507 _88500 _88501 _88502 P a b c) = (term75 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3408815 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3408817 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408818 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term508 _88500 _88501 _88502 P a b c) = (term76 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408817 _88502) (@lem3408816 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408820 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term509 _88500 _88501 _88502 P a b c) = (term215 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408819) (@lem3408818 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408821 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408822 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term505 _88500 _88501 _88502 P a b c) = (term216 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408820 _88500 _88501 _88502 P a b c) (@lem3408821 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408824 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term510 _88500 _88501 _88502 P a b c) = (term511 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408823) (@lem3408822 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408825 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term205 _88500 _88501 _88502 P a b c x) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (eq_refl (term205 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3408826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408827 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term512 _88500 _88501 _88502 P a b c x) = (term513 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3408826) (@lem3408825 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3408828 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408829 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term514 _88500 _88501 _88502 x P a b c) = (term515 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3408827 _88500 _88501 _88502 P a x b c) (@lem3408828 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408830 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term516 _88500 _88501 _88502 P a b c) = (term517 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3408829 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408831 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408832 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term506 _88500 _88501 _88502 P a b c) = (term518 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408831 _88502) (@lem3408830 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408833 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term505 _88500 _88501 _88502 P a b c) = (term506 _88500 _88501 _88502 P a b c)) = ((term216 _88500 _88501 _88502 P a b c) = (term518 _88500 _88501 _88502 P a b c)).
Proof. exact (MK_COMB (@lem3408824 _88500 _88501 _88502 P a b c) (@lem3408832 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408834 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term216 _88500 _88501 _88502 P a b c) = (term518 _88500 _88501 _88502 P a b c).
Proof. exact (EQ_MP (@lem3408833 _88500 _88501 _88502 P a b c) (@lem3408814 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408836 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3408837 {_88501 : Type'} (P : _88501 -> Prop) (Q : Prop) : (term503 _88501 P Q) = (term504 _88501 P Q).
Proof. exact (@lem3408836 _88501 P Q). Qed.
Lemma lem3408838 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term519 _88500 _88501 _88502 x P a b c) = (term520 _88500 _88501 _88502 x P a b c).
Proof. exact (@lem3408837 _88501 (term71 _88500 _88501 _88502 P a x b c) (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408839 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term198 _88500 _88501 _88502 P a x b c y) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (eq_refl (term198 _88500 _88501 _88502 P a x b c y)). Qed.
Lemma lem3408840 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term521 _88500 _88501 _88502 P a x b c) = (term71 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3408839 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3408841 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408842 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term522 _88500 _88501 _88502 P a x b c) = (term73 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3408841 _88501) (@lem3408840 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3408843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408844 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term523 _88500 _88501 _88502 P a x b c) = (term513 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3408843) (@lem3408842 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3408845 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408846 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term519 _88500 _88501 _88502 x P a b c) = (term515 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3408844 _88500 _88501 _88502 P a x b c) (@lem3408845 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408848 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term524 _88500 _88501 _88502 x P a b c) = (term525 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3408847) (@lem3408846 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408849 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term198 _88500 _88501 _88502 P a x b c y) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (eq_refl (term198 _88500 _88501 _88502 P a x b c y)). Qed.
Lemma lem3408850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408851 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term526 _88500 _88501 _88502 P a x b c y) = (term527 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3408850) (@lem3408849 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3408852 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408853 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term528 _88500 _88501 _88502 x y P a b c) = (term529 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3408851 _88500 _88501 _88502 P a x b y c) (@lem3408852 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408854 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term530 _88500 _88501 _88502 x P a b c) = (term531 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3408853 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408855 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408856 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term520 _88500 _88501 _88502 x P a b c) = (term532 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3408855 _88501) (@lem3408854 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408857 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term519 _88500 _88501 _88502 x P a b c) = (term520 _88500 _88501 _88502 x P a b c)) = ((term515 _88500 _88501 _88502 x P a b c) = (term532 _88500 _88501 _88502 x P a b c)).
Proof. exact (MK_COMB (@lem3408848 _88500 _88501 _88502 x P a b c) (@lem3408856 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408858 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term515 _88500 _88501 _88502 x P a b c) = (term532 _88500 _88501 _88502 x P a b c).
Proof. exact (EQ_MP (@lem3408857 _88500 _88501 _88502 x P a b c) (@lem3408838 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408860 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3408861 {_88500 : Type'} (P : _88500 -> Prop) (Q : Prop) : (term503 _88500 P Q) = (term504 _88500 P Q).
Proof. exact (@lem3408860 _88500 P Q). Qed.
Lemma lem3408862 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term533 _88500 _88501 _88502 x y P a b c) = (term534 _88500 _88501 _88502 x y P a b c).
Proof. exact (@lem3408861 _88500 (term67 _88500 _88501 _88502 P a x b y c) (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408863 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term191 _88500 _88501 _88502 P a x b y c z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term191 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3408864 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term535 _88500 _88501 _88502 P a x b y c) = (term67 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3408863 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3408865 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3408866 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term536 _88500 _88501 _88502 P a x b y c) = (term69 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3408865 _88500) (@lem3408864 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3408867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408868 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term537 _88500 _88501 _88502 P a x b y c) = (term527 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3408867) (@lem3408866 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3408869 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408870 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term533 _88500 _88501 _88502 x y P a b c) = (term529 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3408868 _88500 _88501 _88502 P a x b y c) (@lem3408869 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408872 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term538 _88500 _88501 _88502 x y P a b c) = (term539 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3408871) (@lem3408870 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408873 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term191 _88500 _88501 _88502 P a x b y c z) = (term65 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term191 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3408874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3408875 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term540 _88500 _88501 _88502 P a x b y c z) = (term541 _88500 _88501 _88502 P a x b y c z).
Proof. exact (MK_COMB (@lem3408874) (@lem3408873 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3408876 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408877 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term542 _88500 _88501 _88502 x y z P a b c) = (term543 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3408875 _88500 _88501 _88502 P a x b y c z) (@lem3408876 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408878 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term544 _88500 _88501 _88502 x y P a b c) = (term545 _88500 _88501 _88502 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3408877 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3408879 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3408880 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term534 _88500 _88501 _88502 x y P a b c) = (term546 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3408879 _88500) (@lem3408878 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408881 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term533 _88500 _88501 _88502 x y P a b c) = (term534 _88500 _88501 _88502 x y P a b c)) = ((term529 _88500 _88501 _88502 x y P a b c) = (term546 _88500 _88501 _88502 x y P a b c)).
Proof. exact (MK_COMB (@lem3408872 _88500 _88501 _88502 x y P a b c) (@lem3408880 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408882 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term529 _88500 _88501 _88502 x y P a b c) = (term546 _88500 _88501 _88502 x y P a b c).
Proof. exact (EQ_MP (@lem3408881 _88500 _88501 _88502 x y P a b c) (@lem3408862 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408883 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term531 _88500 _88501 _88502 x P a b c) = (term547 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3408882 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3408884 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408885 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term532 _88500 _88501 _88502 x P a b c) = (term548 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3408884 _88501) (@lem3408883 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408886 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term515 _88500 _88501 _88502 x P a b c) = (term548 _88500 _88501 _88502 x P a b c).
Proof. exact (TRANS (@lem3408858 _88500 _88501 _88502 x P a b c) (@lem3408885 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408887 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term517 _88500 _88501 _88502 P a b c) = (term549 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3408886 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3408888 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408889 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term518 _88500 _88501 _88502 P a b c) = (term550 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3408888 _88502) (@lem3408887 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408890 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term216 _88500 _88501 _88502 P a b c) = (term550 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3408834 _88500 _88501 _88502 P a b c) (@lem3408889 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408891 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term329 _88500 _88501 _88502 P a b) = (term551 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3408890 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408892 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3408893 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term340 _88500 _88501 _88502 P a b) = (term552 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408892 _88500) (@lem3408891 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408894 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term351 _88500 _88501 _88502 P a) = (term553 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3408893 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408895 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408896 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term362 _88500 _88501 _88502 P a) = (term554 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408895 _88501) (@lem3408894 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408897 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term373 _88500 _88501 _88502 P) = (term555 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3408896 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408898 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408899 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term384 _88500 _88501 _88502 P) = (term556 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408898 _88502) (@lem3408897 _88500 _88501 _88502 P)). Qed.
Lemma lem3408900 {_88500 _88501 _88502 : Type'} : (term397 _88500 _88501 _88502) = (term557 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3408899 _88500 _88501 _88502 P)). Qed.
Lemma lem3408901 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3408902 {_88500 _88501 _88502 : Type'} : (term408 _88500 _88501 _88502) = (term558 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408901 _88500 _88501 _88502) (@lem3408900 _88500 _88501 _88502)). Qed.
Lemma lem3408903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408904 {_88500 _88501 _88502 : Type'} : (term410 _88500 _88501 _88502) = (term559 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408903) (@lem3408902 _88500 _88501 _88502)). Qed.
Lemma lem3408905 {_88500 _88501 _88502 : Type'} : (term413 _88500 _88501 _88502) = (term413 _88500 _88501 _88502).
Proof. exact (eq_refl (term413 _88500 _88501 _88502)). Qed.
Lemma lem3408906 {_88500 _88501 _88502 : Type'} : (term414 _88500 _88501 _88502) = (term560 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408904 _88500 _88501 _88502) (@lem3408905 _88500 _88501 _88502)). Qed.
Lemma lem3408908 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3408909 {_88500 _88501 _88502 : Type'} (P : type871 _88500 _88501 _88502) (Q : type871 _88500 _88501 _88502) : (term394 _88500 _88501 _88502 P Q) = (term393 _88500 _88501 _88502 P Q).
Proof. exact (@lem3408908 (type1517 _88500 _88501 _88502) P Q). Qed.
Lemma lem3408910 {_88500 _88501 _88502 : Type'} : (term561 _88500 _88501 _88502) = (term562 _88500 _88501 _88502).
Proof. exact (@lem3408909 _88500 _88501 _88502 (term557 _88500 _88501 _88502) (term398 _88500 _88501 _88502)). Qed.
Lemma lem3408911 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term563 _88500 _88501 _88502 P) = (term556 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term563 _88500 _88501 _88502 P)). Qed.
Lemma lem3408912 {_88500 _88501 _88502 : Type'} : (term564 _88500 _88501 _88502) = (term557 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3408911 _88500 _88501 _88502 P)). Qed.
Lemma lem3408913 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3408914 {_88500 _88501 _88502 : Type'} : (term565 _88500 _88501 _88502) = (term558 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408913 _88500 _88501 _88502) (@lem3408912 _88500 _88501 _88502)). Qed.
Lemma lem3408915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408916 {_88500 _88501 _88502 : Type'} : (term566 _88500 _88501 _88502) = (term559 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408915) (@lem3408914 _88500 _88501 _88502)). Qed.
Lemma lem3408917 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term401 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term401 _88500 _88501 _88502 P)). Qed.
Lemma lem3408918 {_88500 _88501 _88502 : Type'} : (term411 _88500 _88501 _88502) = (term398 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3408917 _88500 _88501 _88502 P)). Qed.
Lemma lem3408919 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3408920 {_88500 _88501 _88502 : Type'} : (term412 _88500 _88501 _88502) = (term413 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408919 _88500 _88501 _88502) (@lem3408918 _88500 _88501 _88502)). Qed.
Lemma lem3408921 {_88500 _88501 _88502 : Type'} : (term561 _88500 _88501 _88502) = (term560 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408916 _88500 _88501 _88502) (@lem3408920 _88500 _88501 _88502)). Qed.
Lemma lem3408922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408923 {_88500 _88501 _88502 : Type'} : (term567 _88500 _88501 _88502) = (term568 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408922) (@lem3408921 _88500 _88501 _88502)). Qed.
Lemma lem3408924 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term563 _88500 _88501 _88502 P) = (term556 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term563 _88500 _88501 _88502 P)). Qed.
Lemma lem3408925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408926 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term569 _88500 _88501 _88502 P) = (term570 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408925) (@lem3408924 _88500 _88501 _88502 P)). Qed.
Lemma lem3408927 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term401 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term401 _88500 _88501 _88502 P)). Qed.
Lemma lem3408928 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term571 _88500 _88501 _88502 P) = (term572 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408926 _88500 _88501 _88502 P) (@lem3408927 _88500 _88501 _88502 P)). Qed.
Lemma lem3408929 {_88500 _88501 _88502 : Type'} : (term573 _88500 _88501 _88502) = (term574 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3408928 _88500 _88501 _88502 P)). Qed.
Lemma lem3408930 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3408931 {_88500 _88501 _88502 : Type'} : (term562 _88500 _88501 _88502) = (term575 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3408930 _88500 _88501 _88502) (@lem3408929 _88500 _88501 _88502)). Qed.
Lemma lem3408932 {_88500 _88501 _88502 : Type'} : ((term561 _88500 _88501 _88502) = (term562 _88500 _88501 _88502)) = ((term560 _88500 _88501 _88502) = (term575 _88500 _88501 _88502)).
Proof. exact (MK_COMB (@lem3408923 _88500 _88501 _88502) (@lem3408931 _88500 _88501 _88502)). Qed.
Lemma lem3408933 {_88500 _88501 _88502 : Type'} : (term560 _88500 _88501 _88502) = (term575 _88500 _88501 _88502).
Proof. exact (EQ_MP (@lem3408932 _88500 _88501 _88502) (@lem3408910 _88500 _88501 _88502)). Qed.
Lemma lem3408935 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3408936 {_88502 : Type'} (P : _88502 -> Prop) (Q : _88502 -> Prop) : (term326 _88502 P Q) = (term325 _88502 P Q).
Proof. exact (@lem3408935 _88502 P Q). Qed.
Lemma lem3408937 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term576 _88500 _88501 _88502 P) = (term577 _88500 _88501 _88502 P).
Proof. exact (@lem3408936 _88502 (term555 _88500 _88501 _88502 P) (term374 _88500 _88501 _88502 P)). Qed.
Lemma lem3408938 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term578 _88500 _88501 _88502 P a) = (term554 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term578 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408939 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term579 _88500 _88501 _88502 P) = (term555 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3408938 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408940 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408941 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term580 _88500 _88501 _88502 P) = (term556 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408940 _88502) (@lem3408939 _88500 _88501 _88502 P)). Qed.
Lemma lem3408942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408943 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term581 _88500 _88501 _88502 P) = (term570 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408942) (@lem3408941 _88500 _88501 _88502 P)). Qed.
Lemma lem3408944 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term377 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term377 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408945 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term387 _88500 _88501 _88502 P) = (term374 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3408944 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408946 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408947 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term388 _88500 _88501 _88502 P) = (term389 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408946 _88502) (@lem3408945 _88500 _88501 _88502 P)). Qed.
Lemma lem3408948 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term576 _88500 _88501 _88502 P) = (term572 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408943 _88500 _88501 _88502 P) (@lem3408947 _88500 _88501 _88502 P)). Qed.
Lemma lem3408949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408950 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term582 _88500 _88501 _88502 P) = (term583 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408949) (@lem3408948 _88500 _88501 _88502 P)). Qed.
Lemma lem3408951 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term578 _88500 _88501 _88502 P a) = (term554 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term578 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408953 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term584 _88500 _88501 _88502 P a) = (term585 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408952) (@lem3408951 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408954 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term377 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term377 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408955 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term586 _88500 _88501 _88502 P a) = (term587 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408953 _88500 _88501 _88502 P a) (@lem3408954 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408956 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term588 _88500 _88501 _88502 P) = (term589 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3408955 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408957 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3408958 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term577 _88500 _88501 _88502 P) = (term590 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3408957 _88502) (@lem3408956 _88500 _88501 _88502 P)). Qed.
Lemma lem3408959 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : ((term576 _88500 _88501 _88502 P) = (term577 _88500 _88501 _88502 P)) = ((term572 _88500 _88501 _88502 P) = (term590 _88500 _88501 _88502 P)).
Proof. exact (MK_COMB (@lem3408950 _88500 _88501 _88502 P) (@lem3408958 _88500 _88501 _88502 P)). Qed.
Lemma lem3408960 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term572 _88500 _88501 _88502 P) = (term590 _88500 _88501 _88502 P).
Proof. exact (EQ_MP (@lem3408959 _88500 _88501 _88502 P) (@lem3408937 _88500 _88501 _88502 P)). Qed.
Lemma lem3408962 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3408963 {_88501 : Type'} (P : _88501 -> Prop) (Q : _88501 -> Prop) : (term326 _88501 P Q) = (term325 _88501 P Q).
Proof. exact (@lem3408962 _88501 P Q). Qed.
Lemma lem3408964 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term591 _88500 _88501 _88502 P a) = (term592 _88500 _88501 _88502 P a).
Proof. exact (@lem3408963 _88501 (term553 _88500 _88501 _88502 P a) (term352 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408965 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term593 _88500 _88501 _88502 P a b) = (term552 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term593 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408966 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term594 _88500 _88501 _88502 P a) = (term553 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3408965 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408967 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408968 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term595 _88500 _88501 _88502 P a) = (term554 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408967 _88501) (@lem3408966 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408970 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term596 _88500 _88501 _88502 P a) = (term585 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408969) (@lem3408968 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408971 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term355 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term355 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408972 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term365 _88500 _88501 _88502 P a) = (term352 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3408971 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408973 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408974 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term366 _88500 _88501 _88502 P a) = (term367 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408973 _88501) (@lem3408972 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408975 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term591 _88500 _88501 _88502 P a) = (term587 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408970 _88500 _88501 _88502 P a) (@lem3408974 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3408977 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term597 _88500 _88501 _88502 P a) = (term598 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408976) (@lem3408975 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408978 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term593 _88500 _88501 _88502 P a b) = (term552 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term593 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408980 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term599 _88500 _88501 _88502 P a b) = (term600 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408979) (@lem3408978 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408981 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term355 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term355 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408982 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term601 _88500 _88501 _88502 P a b) = (term602 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408980 _88500 _88501 _88502 P a b) (@lem3408981 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408983 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term603 _88500 _88501 _88502 P a) = (term604 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3408982 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408984 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3408985 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term592 _88500 _88501 _88502 P a) = (term605 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3408984 _88501) (@lem3408983 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408986 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : ((term591 _88500 _88501 _88502 P a) = (term592 _88500 _88501 _88502 P a)) = ((term587 _88500 _88501 _88502 P a) = (term605 _88500 _88501 _88502 P a)).
Proof. exact (MK_COMB (@lem3408977 _88500 _88501 _88502 P a) (@lem3408985 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408987 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term587 _88500 _88501 _88502 P a) = (term605 _88500 _88501 _88502 P a).
Proof. exact (EQ_MP (@lem3408986 _88500 _88501 _88502 P a) (@lem3408964 _88500 _88501 _88502 P a)). Qed.
Lemma lem3408989 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3408990 {_88500 : Type'} (P : _88500 -> Prop) (Q : _88500 -> Prop) : (term326 _88500 P Q) = (term325 _88500 P Q).
Proof. exact (@lem3408989 _88500 P Q). Qed.
Lemma lem3408991 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term606 _88500 _88501 _88502 P a b) = (term607 _88500 _88501 _88502 P a b).
Proof. exact (@lem3408990 _88500 (term551 _88500 _88501 _88502 P a b) (term330 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408992 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term608 _88500 _88501 _88502 P a b c) = (term550 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term608 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408993 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term609 _88500 _88501 _88502 P a b) = (term551 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3408992 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408994 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3408995 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term610 _88500 _88501 _88502 P a b) = (term552 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408994 _88500) (@lem3408993 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3408997 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term611 _88500 _88501 _88502 P a b) = (term600 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408996) (@lem3408995 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3408998 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term333 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term333 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3408999 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term343 _88500 _88501 _88502 P a b) = (term330 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3408998 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409000 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409001 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term344 _88500 _88501 _88502 P a b) = (term345 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409000 _88500) (@lem3408999 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409002 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term606 _88500 _88501 _88502 P a b) = (term602 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3408997 _88500 _88501 _88502 P a b) (@lem3409001 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409004 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term612 _88500 _88501 _88502 P a b) = (term613 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409003) (@lem3409002 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409005 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term608 _88500 _88501 _88502 P a b c) = (term550 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term608 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409007 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term614 _88500 _88501 _88502 P a b c) = (term615 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409006) (@lem3409005 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409008 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term333 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term333 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409009 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term616 _88500 _88501 _88502 P a b c) = (term617 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409007 _88500 _88501 _88502 P a b c) (@lem3409008 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409010 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term618 _88500 _88501 _88502 P a b) = (term619 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3409009 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409011 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409012 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term607 _88500 _88501 _88502 P a b) = (term620 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409011 _88500) (@lem3409010 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409013 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : ((term606 _88500 _88501 _88502 P a b) = (term607 _88500 _88501 _88502 P a b)) = ((term602 _88500 _88501 _88502 P a b) = (term620 _88500 _88501 _88502 P a b)).
Proof. exact (MK_COMB (@lem3409004 _88500 _88501 _88502 P a b) (@lem3409012 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409014 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term602 _88500 _88501 _88502 P a b) = (term620 _88500 _88501 _88502 P a b).
Proof. exact (EQ_MP (@lem3409013 _88500 _88501 _88502 P a b) (@lem3408991 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409016 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409017 {_88502 : Type'} (P : _88502 -> Prop) (Q : Prop) : (term621 _88502 P Q) = (term622 _88502 P Q).
Proof. exact (@lem3409016 _88502 P Q). Qed.
Lemma lem3409018 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term623 _88500 _88501 _88502 P a b c) = (term624 _88500 _88501 _88502 P a b c).
Proof. exact (@lem3409017 _88502 (term549 _88500 _88501 _88502 P a b c) (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409019 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term625 _88500 _88501 _88502 P a b c x) = (term548 _88500 _88501 _88502 x P a b c).
Proof. exact (eq_refl (term625 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3409020 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term626 _88500 _88501 _88502 P a b c) = (term549 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409019 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409021 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409022 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term627 _88500 _88501 _88502 P a b c) = (term550 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409021 _88502) (@lem3409020 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409024 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term628 _88500 _88501 _88502 P a b c) = (term615 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409023) (@lem3409022 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409025 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409026 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term623 _88500 _88501 _88502 P a b c) = (term617 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409024 _88500 _88501 _88502 P a b c) (@lem3409025 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409028 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term629 _88500 _88501 _88502 P a b c) = (term630 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409027) (@lem3409026 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409029 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term625 _88500 _88501 _88502 P a b c x) = (term548 _88500 _88501 _88502 x P a b c).
Proof. exact (eq_refl (term625 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3409030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409031 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term631 _88500 _88501 _88502 P a b c x) = (term632 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409030) (@lem3409029 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409032 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409033 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term633 _88500 _88501 _88502 x P a b c) = (term634 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409031 _88500 _88501 _88502 x P a b c) (@lem3409032 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409034 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term635 _88500 _88501 _88502 P a b c) = (term636 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409033 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409035 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409036 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term624 _88500 _88501 _88502 P a b c) = (term637 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409035 _88502) (@lem3409034 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409037 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term623 _88500 _88501 _88502 P a b c) = (term624 _88500 _88501 _88502 P a b c)) = ((term617 _88500 _88501 _88502 P a b c) = (term637 _88500 _88501 _88502 P a b c)).
Proof. exact (MK_COMB (@lem3409028 _88500 _88501 _88502 P a b c) (@lem3409036 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409038 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term617 _88500 _88501 _88502 P a b c) = (term637 _88500 _88501 _88502 P a b c).
Proof. exact (EQ_MP (@lem3409037 _88500 _88501 _88502 P a b c) (@lem3409018 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409040 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409041 {_88501 : Type'} (P : _88501 -> Prop) (Q : Prop) : (term621 _88501 P Q) = (term622 _88501 P Q).
Proof. exact (@lem3409040 _88501 P Q). Qed.
Lemma lem3409042 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term638 _88500 _88501 _88502 x P a b c) = (term639 _88500 _88501 _88502 x P a b c).
Proof. exact (@lem3409041 _88501 (term547 _88500 _88501 _88502 x P a b c) (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409043 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term640 _88500 _88501 _88502 x P a b c y) = (term546 _88500 _88501 _88502 x y P a b c).
Proof. exact (eq_refl (term640 _88500 _88501 _88502 x P a b c y)). Qed.
Lemma lem3409044 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term641 _88500 _88501 _88502 x P a b c) = (term547 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409043 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409045 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409046 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term642 _88500 _88501 _88502 x P a b c) = (term548 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409045 _88501) (@lem3409044 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409048 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term643 _88500 _88501 _88502 x P a b c) = (term632 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409047) (@lem3409046 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409049 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409050 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term638 _88500 _88501 _88502 x P a b c) = (term634 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409048 _88500 _88501 _88502 x P a b c) (@lem3409049 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409052 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term644 _88500 _88501 _88502 x P a b c) = (term645 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409051) (@lem3409050 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409053 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term640 _88500 _88501 _88502 x P a b c y) = (term546 _88500 _88501 _88502 x y P a b c).
Proof. exact (eq_refl (term640 _88500 _88501 _88502 x P a b c y)). Qed.
Lemma lem3409054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409055 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term646 _88500 _88501 _88502 x P a b c y) = (term647 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409054) (@lem3409053 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409056 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409057 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term648 _88500 _88501 _88502 x y P a b c) = (term649 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409055 _88500 _88501 _88502 x y P a b c) (@lem3409056 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409058 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term650 _88500 _88501 _88502 x P a b c) = (term651 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409057 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409059 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409060 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term639 _88500 _88501 _88502 x P a b c) = (term652 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409059 _88501) (@lem3409058 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409061 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term638 _88500 _88501 _88502 x P a b c) = (term639 _88500 _88501 _88502 x P a b c)) = ((term634 _88500 _88501 _88502 x P a b c) = (term652 _88500 _88501 _88502 x P a b c)).
Proof. exact (MK_COMB (@lem3409052 _88500 _88501 _88502 x P a b c) (@lem3409060 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409062 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term634 _88500 _88501 _88502 x P a b c) = (term652 _88500 _88501 _88502 x P a b c).
Proof. exact (EQ_MP (@lem3409061 _88500 _88501 _88502 x P a b c) (@lem3409042 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409064 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409065 {_88500 : Type'} (P : _88500 -> Prop) (Q : Prop) : (term621 _88500 P Q) = (term622 _88500 P Q).
Proof. exact (@lem3409064 _88500 P Q). Qed.
Lemma lem3409066 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term653 _88500 _88501 _88502 x y P a b c) = (term654 _88500 _88501 _88502 x y P a b c).
Proof. exact (@lem3409065 _88500 (term545 _88500 _88501 _88502 x y P a b c) (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409067 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term655 _88500 _88501 _88502 x y P a b c z) = (term543 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term655 _88500 _88501 _88502 x y P a b c z)). Qed.
Lemma lem3409068 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term656 _88500 _88501 _88502 x y P a b c) = (term545 _88500 _88501 _88502 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409067 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409069 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409070 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term657 _88500 _88501 _88502 x y P a b c) = (term546 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409069 _88500) (@lem3409068 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409072 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term658 _88500 _88501 _88502 x y P a b c) = (term647 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409071) (@lem3409070 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409073 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409074 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term653 _88500 _88501 _88502 x y P a b c) = (term649 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409072 _88500 _88501 _88502 x y P a b c) (@lem3409073 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409076 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term659 _88500 _88501 _88502 x y P a b c) = (term660 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409075) (@lem3409074 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409077 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term655 _88500 _88501 _88502 x y P a b c z) = (term543 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term655 _88500 _88501 _88502 x y P a b c z)). Qed.
Lemma lem3409078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409079 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term661 _88500 _88501 _88502 x y P a b c z) = (term662 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3409078) (@lem3409077 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409080 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term214 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409081 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term663 _88500 _88501 _88502 x y z P a b c) = (term664 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3409079 _88500 _88501 _88502 x y z P a b c) (@lem3409080 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409082 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term665 _88500 _88501 _88502 x y P a b c) = (term666 _88500 _88501 _88502 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409081 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409083 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409084 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term654 _88500 _88501 _88502 x y P a b c) = (term667 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409083 _88500) (@lem3409082 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409085 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term653 _88500 _88501 _88502 x y P a b c) = (term654 _88500 _88501 _88502 x y P a b c)) = ((term649 _88500 _88501 _88502 x y P a b c) = (term667 _88500 _88501 _88502 x y P a b c)).
Proof. exact (MK_COMB (@lem3409076 _88500 _88501 _88502 x y P a b c) (@lem3409084 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409086 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term649 _88500 _88501 _88502 x y P a b c) = (term667 _88500 _88501 _88502 x y P a b c).
Proof. exact (EQ_MP (@lem3409085 _88500 _88501 _88502 x y P a b c) (@lem3409066 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409087 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term651 _88500 _88501 _88502 x P a b c) = (term668 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409086 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409088 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409089 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term652 _88500 _88501 _88502 x P a b c) = (term669 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409088 _88501) (@lem3409087 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409090 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term634 _88500 _88501 _88502 x P a b c) = (term669 _88500 _88501 _88502 x P a b c).
Proof. exact (TRANS (@lem3409062 _88500 _88501 _88502 x P a b c) (@lem3409089 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409091 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term636 _88500 _88501 _88502 P a b c) = (term670 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409090 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409092 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409093 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term637 _88500 _88501 _88502 P a b c) = (term671 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409092 _88502) (@lem3409091 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409094 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term617 _88500 _88501 _88502 P a b c) = (term671 _88500 _88501 _88502 P a b c).
Proof. exact (TRANS (@lem3409038 _88500 _88501 _88502 P a b c) (@lem3409093 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409095 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term619 _88500 _88501 _88502 P a b) = (term672 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3409094 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409096 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409097 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term620 _88500 _88501 _88502 P a b) = (term673 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409096 _88500) (@lem3409095 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409098 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term602 _88500 _88501 _88502 P a b) = (term673 _88500 _88501 _88502 P a b).
Proof. exact (TRANS (@lem3409014 _88500 _88501 _88502 P a b) (@lem3409097 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409099 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term604 _88500 _88501 _88502 P a) = (term674 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3409098 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409100 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409101 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term605 _88500 _88501 _88502 P a) = (term675 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3409100 _88501) (@lem3409099 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409102 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term587 _88500 _88501 _88502 P a) = (term675 _88500 _88501 _88502 P a).
Proof. exact (TRANS (@lem3408987 _88500 _88501 _88502 P a) (@lem3409101 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409103 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term589 _88500 _88501 _88502 P) = (term676 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3409102 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409104 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409105 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term590 _88500 _88501 _88502 P) = (term677 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3409104 _88502) (@lem3409103 _88500 _88501 _88502 P)). Qed.
Lemma lem3409106 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term572 _88500 _88501 _88502 P) = (term677 _88500 _88501 _88502 P).
Proof. exact (TRANS (@lem3408960 _88500 _88501 _88502 P) (@lem3409105 _88500 _88501 _88502 P)). Qed.
Lemma lem3409107 {_88500 _88501 _88502 : Type'} : (term574 _88500 _88501 _88502) = (term678 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3409106 _88500 _88501 _88502 P)). Qed.
Lemma lem3409108 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3409109 {_88500 _88501 _88502 : Type'} : (term575 _88500 _88501 _88502) = (term679 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3409108 _88500 _88501 _88502) (@lem3409107 _88500 _88501 _88502)). Qed.
Lemma lem3409110 {_88500 _88501 _88502 : Type'} : (term560 _88500 _88501 _88502) = (term679 _88500 _88501 _88502).
Proof. exact (TRANS (@lem3408933 _88500 _88501 _88502) (@lem3409109 _88500 _88501 _88502)). Qed.
Lemma lem3409111 {_88500 _88501 _88502 : Type'} : (term414 _88500 _88501 _88502) = (term679 _88500 _88501 _88502).
Proof. exact (TRANS (@lem3408906 _88500 _88501 _88502) (@lem3409110 _88500 _88501 _88502)). Qed.
Lemma lem3409112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409113 {_88500 _88501 _88502 : Type'} : (term415 _88500 _88501 _88502) = (term680 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3409112) (@lem3409111 _88500 _88501 _88502)). Qed.
Lemma lem3409115 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3409116 {_88565 : Type'} (P : _88565 -> Prop) (Q : Prop) : (term503 _88565 P Q) = (term504 _88565 P Q).
Proof. exact (@lem3409115 _88565 P Q). Qed.
Lemma lem3409117 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term681 _88563 _88564 _88565 P a b c) = (term682 _88563 _88564 _88565 P a b c).
Proof. exact (@lem3409116 _88565 (term148 _88563 _88564 _88565 P a b c) (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409118 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term278 _88563 _88564 _88565 P a b c x) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (eq_refl (term278 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409119 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term683 _88563 _88564 _88565 P a b c) = (term148 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409118 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3409120 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409121 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term684 _88563 _88564 _88565 P a b c) = (term149 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409120 _88565) (@lem3409119 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409123 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term685 _88563 _88564 _88565 P a b c) = (term287 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409122) (@lem3409121 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409124 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409125 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term681 _88563 _88564 _88565 P a b c) = (term288 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409123 _88563 _88564 _88565 P a b c) (@lem3409124 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409127 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term686 _88563 _88564 _88565 P a b c) = (term687 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409126) (@lem3409125 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409128 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term278 _88563 _88564 _88565 P a b c x) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (eq_refl (term278 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409130 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term688 _88563 _88564 _88565 P a b c x) = (term689 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3409129) (@lem3409128 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3409131 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409132 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term690 _88563 _88564 _88565 x P a b c) = (term691 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409130 _88563 _88564 _88565 P a x b c) (@lem3409131 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409133 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term692 _88563 _88564 _88565 P a b c) = (term693 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409132 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409134 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409135 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term682 _88563 _88564 _88565 P a b c) = (term694 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409134 _88565) (@lem3409133 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409136 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term681 _88563 _88564 _88565 P a b c) = (term682 _88563 _88564 _88565 P a b c)) = ((term288 _88563 _88564 _88565 P a b c) = (term694 _88563 _88564 _88565 P a b c)).
Proof. exact (MK_COMB (@lem3409127 _88563 _88564 _88565 P a b c) (@lem3409135 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409137 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term288 _88563 _88564 _88565 P a b c) = (term694 _88563 _88564 _88565 P a b c).
Proof. exact (EQ_MP (@lem3409136 _88563 _88564 _88565 P a b c) (@lem3409117 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409139 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3409140 {_88564 : Type'} (P : _88564 -> Prop) (Q : Prop) : (term503 _88564 P Q) = (term504 _88564 P Q).
Proof. exact (@lem3409139 _88564 P Q). Qed.
Lemma lem3409141 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term695 _88563 _88564 _88565 x P a b c) = (term696 _88563 _88564 _88565 x P a b c).
Proof. exact (@lem3409140 _88564 (term144 _88563 _88564 _88565 P a x b c) (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409142 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term271 _88563 _88564 _88565 P a x b c y) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (eq_refl (term271 _88563 _88564 _88565 P a x b c y)). Qed.
Lemma lem3409143 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term697 _88563 _88564 _88565 P a x b c) = (term144 _88563 _88564 _88565 P a x b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409142 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3409144 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409145 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term698 _88563 _88564 _88565 P a x b c) = (term146 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3409144 _88564) (@lem3409143 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3409146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409147 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (c : _88563) : (term699 _88563 _88564 _88565 P a x b c) = (term689 _88563 _88564 _88565 P a x b c).
Proof. exact (MK_COMB (@lem3409146) (@lem3409145 _88563 _88564 _88565 P a x b c)). Qed.
Lemma lem3409148 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409149 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term695 _88563 _88564 _88565 x P a b c) = (term691 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409147 _88563 _88564 _88565 P a x b c) (@lem3409148 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409151 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term700 _88563 _88564 _88565 x P a b c) = (term701 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409150) (@lem3409149 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409152 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term271 _88563 _88564 _88565 P a x b c y) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (eq_refl (term271 _88563 _88564 _88565 P a x b c y)). Qed.
Lemma lem3409153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409154 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term702 _88563 _88564 _88565 P a x b c y) = (term703 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3409153) (@lem3409152 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3409155 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409156 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term704 _88563 _88564 _88565 x y P a b c) = (term705 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409154 _88563 _88564 _88565 P a x b y c) (@lem3409155 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409157 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term706 _88563 _88564 _88565 x P a b c) = (term707 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409156 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409158 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409159 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term696 _88563 _88564 _88565 x P a b c) = (term708 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409158 _88564) (@lem3409157 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409160 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term695 _88563 _88564 _88565 x P a b c) = (term696 _88563 _88564 _88565 x P a b c)) = ((term691 _88563 _88564 _88565 x P a b c) = (term708 _88563 _88564 _88565 x P a b c)).
Proof. exact (MK_COMB (@lem3409151 _88563 _88564 _88565 x P a b c) (@lem3409159 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409161 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term691 _88563 _88564 _88565 x P a b c) = (term708 _88563 _88564 _88565 x P a b c).
Proof. exact (EQ_MP (@lem3409160 _88563 _88564 _88565 x P a b c) (@lem3409141 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409163 {A : Type'} (P : A -> Prop) (Q : Prop) : (term503 A P Q) = (term504 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3409164 {_88563 : Type'} (P : _88563 -> Prop) (Q : Prop) : (term503 _88563 P Q) = (term504 _88563 P Q).
Proof. exact (@lem3409163 _88563 P Q). Qed.
Lemma lem3409165 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term709 _88563 _88564 _88565 x y P a b c) = (term710 _88563 _88564 _88565 x y P a b c).
Proof. exact (@lem3409164 _88563 (term140 _88563 _88564 _88565 P a x b y c) (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409166 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term264 _88563 _88564 _88565 P a x b y c z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (eq_refl (term264 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3409167 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term711 _88563 _88564 _88565 P a x b y c) = (term140 _88563 _88564 _88565 P a x b y c).
Proof. exact (fun_ext (fun z : _88563 => @lem3409166 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3409168 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409169 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term712 _88563 _88564 _88565 P a x b y c) = (term142 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3409168 _88563) (@lem3409167 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3409170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409171 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) : (term713 _88563 _88564 _88565 P a x b y c) = (term703 _88563 _88564 _88565 P a x b y c).
Proof. exact (MK_COMB (@lem3409170) (@lem3409169 _88563 _88564 _88565 P a x b y c)). Qed.
Lemma lem3409172 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409173 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term709 _88563 _88564 _88565 x y P a b c) = (term705 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409171 _88563 _88564 _88565 P a x b y c) (@lem3409172 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409175 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term714 _88563 _88564 _88565 x y P a b c) = (term715 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409174) (@lem3409173 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409176 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term264 _88563 _88564 _88565 P a x b y c z) = (term138 _88563 _88564 _88565 P a x b y c z).
Proof. exact (eq_refl (term264 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3409177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409178 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (x : _88565) (b : _88564) (y : _88564) (c : _88563) (z : _88563) : (term716 _88563 _88564 _88565 P a x b y c z) = (term717 _88563 _88564 _88565 P a x b y c z).
Proof. exact (MK_COMB (@lem3409177) (@lem3409176 _88563 _88564 _88565 P a x b y c z)). Qed.
Lemma lem3409179 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term210 _88563 _88564 _88565 P a b c) = (term210 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409180 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term718 _88563 _88564 _88565 x y z P a b c) = (term719 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409178 _88563 _88564 _88565 P a x b y c z) (@lem3409179 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409181 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term720 _88563 _88564 _88565 x y P a b c) = (term721 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88563 => @lem3409180 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409182 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409183 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term710 _88563 _88564 _88565 x y P a b c) = (term722 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409182 _88563) (@lem3409181 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409184 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term709 _88563 _88564 _88565 x y P a b c) = (term710 _88563 _88564 _88565 x y P a b c)) = ((term705 _88563 _88564 _88565 x y P a b c) = (term722 _88563 _88564 _88565 x y P a b c)).
Proof. exact (MK_COMB (@lem3409175 _88563 _88564 _88565 x y P a b c) (@lem3409183 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409185 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term705 _88563 _88564 _88565 x y P a b c) = (term722 _88563 _88564 _88565 x y P a b c).
Proof. exact (EQ_MP (@lem3409184 _88563 _88564 _88565 x y P a b c) (@lem3409165 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409186 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term707 _88563 _88564 _88565 x P a b c) = (term723 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409185 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409187 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409188 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term708 _88563 _88564 _88565 x P a b c) = (term724 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409187 _88564) (@lem3409186 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409189 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term691 _88563 _88564 _88565 x P a b c) = (term724 _88563 _88564 _88565 x P a b c).
Proof. exact (TRANS (@lem3409161 _88563 _88564 _88565 x P a b c) (@lem3409188 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409190 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term693 _88563 _88564 _88565 P a b c) = (term725 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409189 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409191 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409192 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term694 _88563 _88564 _88565 P a b c) = (term726 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409191 _88565) (@lem3409190 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409193 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term288 _88563 _88564 _88565 P a b c) = (term726 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3409137 _88563 _88564 _88565 P a b c) (@lem3409192 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409194 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term418 _88563 _88564 _88565 P a b) = (term727 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409193 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409195 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409196 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term429 _88563 _88564 _88565 P a b) = (term728 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409195 _88563) (@lem3409194 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409197 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term440 _88563 _88564 _88565 P a) = (term729 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409196 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409198 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409199 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term451 _88563 _88564 _88565 P a) = (term730 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409198 _88564) (@lem3409197 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409200 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term462 _88563 _88564 _88565 P) = (term731 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409199 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409201 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409202 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term473 _88563 _88564 _88565 P) = (term732 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409201 _88565) (@lem3409200 _88563 _88564 _88565 P)). Qed.
Lemma lem3409203 {_88563 _88564 _88565 : Type'} : (term484 _88563 _88564 _88565) = (term733 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409202 _88563 _88564 _88565 P)). Qed.
Lemma lem3409204 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409205 {_88563 _88564 _88565 : Type'} : (term495 _88563 _88564 _88565) = (term734 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409204 _88563 _88564 _88565) (@lem3409203 _88563 _88564 _88565)). Qed.
Lemma lem3409206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409207 {_88563 _88564 _88565 : Type'} : (term497 _88563 _88564 _88565) = (term735 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409206) (@lem3409205 _88563 _88564 _88565)). Qed.
Lemma lem3409208 {_88563 _88564 _88565 : Type'} : (term500 _88563 _88564 _88565) = (term500 _88563 _88564 _88565).
Proof. exact (eq_refl (term500 _88563 _88564 _88565)). Qed.
Lemma lem3409209 {_88563 _88564 _88565 : Type'} : (term501 _88563 _88564 _88565) = (term736 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409207 _88563 _88564 _88565) (@lem3409208 _88563 _88564 _88565)). Qed.
Lemma lem3409211 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3409212 {_88563 _88564 _88565 : Type'} (P : type871 _88563 _88564 _88565) (Q : type871 _88563 _88564 _88565) : (term394 _88563 _88564 _88565 P Q) = (term393 _88563 _88564 _88565 P Q).
Proof. exact (@lem3409211 (type1517 _88563 _88564 _88565) P Q). Qed.
Lemma lem3409213 {_88563 _88564 _88565 : Type'} : (term737 _88563 _88564 _88565) = (term738 _88563 _88564 _88565).
Proof. exact (@lem3409212 _88563 _88564 _88565 (term733 _88563 _88564 _88565) (term485 _88563 _88564 _88565)). Qed.
Lemma lem3409214 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term739 _88563 _88564 _88565 P) = (term732 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term739 _88563 _88564 _88565 P)). Qed.
Lemma lem3409215 {_88563 _88564 _88565 : Type'} : (term740 _88563 _88564 _88565) = (term733 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409214 _88563 _88564 _88565 P)). Qed.
Lemma lem3409216 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409217 {_88563 _88564 _88565 : Type'} : (term741 _88563 _88564 _88565) = (term734 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409216 _88563 _88564 _88565) (@lem3409215 _88563 _88564 _88565)). Qed.
Lemma lem3409218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409219 {_88563 _88564 _88565 : Type'} : (term742 _88563 _88564 _88565) = (term735 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409218) (@lem3409217 _88563 _88564 _88565)). Qed.
Lemma lem3409220 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term488 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term488 _88563 _88564 _88565 P)). Qed.
Lemma lem3409221 {_88563 _88564 _88565 : Type'} : (term498 _88563 _88564 _88565) = (term485 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409220 _88563 _88564 _88565 P)). Qed.
Lemma lem3409222 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409223 {_88563 _88564 _88565 : Type'} : (term499 _88563 _88564 _88565) = (term500 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409222 _88563 _88564 _88565) (@lem3409221 _88563 _88564 _88565)). Qed.
Lemma lem3409224 {_88563 _88564 _88565 : Type'} : (term737 _88563 _88564 _88565) = (term736 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409219 _88563 _88564 _88565) (@lem3409223 _88563 _88564 _88565)). Qed.
Lemma lem3409225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409226 {_88563 _88564 _88565 : Type'} : (term743 _88563 _88564 _88565) = (term744 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409225) (@lem3409224 _88563 _88564 _88565)). Qed.
Lemma lem3409227 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term739 _88563 _88564 _88565 P) = (term732 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term739 _88563 _88564 _88565 P)). Qed.
Lemma lem3409228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409229 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term745 _88563 _88564 _88565 P) = (term746 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409228) (@lem3409227 _88563 _88564 _88565 P)). Qed.
Lemma lem3409230 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term488 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term488 _88563 _88564 _88565 P)). Qed.
Lemma lem3409231 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term747 _88563 _88564 _88565 P) = (term748 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409229 _88563 _88564 _88565 P) (@lem3409230 _88563 _88564 _88565 P)). Qed.
Lemma lem3409232 {_88563 _88564 _88565 : Type'} : (term749 _88563 _88564 _88565) = (term750 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409231 _88563 _88564 _88565 P)). Qed.
Lemma lem3409233 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409234 {_88563 _88564 _88565 : Type'} : (term738 _88563 _88564 _88565) = (term751 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409233 _88563 _88564 _88565) (@lem3409232 _88563 _88564 _88565)). Qed.
Lemma lem3409235 {_88563 _88564 _88565 : Type'} : ((term737 _88563 _88564 _88565) = (term738 _88563 _88564 _88565)) = ((term736 _88563 _88564 _88565) = (term751 _88563 _88564 _88565)).
Proof. exact (MK_COMB (@lem3409226 _88563 _88564 _88565) (@lem3409234 _88563 _88564 _88565)). Qed.
Lemma lem3409236 {_88563 _88564 _88565 : Type'} : (term736 _88563 _88564 _88565) = (term751 _88563 _88564 _88565).
Proof. exact (EQ_MP (@lem3409235 _88563 _88564 _88565) (@lem3409213 _88563 _88564 _88565)). Qed.
Lemma lem3409238 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3409239 {_88565 : Type'} (P : _88565 -> Prop) (Q : _88565 -> Prop) : (term326 _88565 P Q) = (term325 _88565 P Q).
Proof. exact (@lem3409238 _88565 P Q). Qed.
Lemma lem3409240 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term752 _88563 _88564 _88565 P) = (term753 _88563 _88564 _88565 P).
Proof. exact (@lem3409239 _88565 (term731 _88563 _88564 _88565 P) (term463 _88563 _88564 _88565 P)). Qed.
Lemma lem3409241 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term754 _88563 _88564 _88565 P a) = (term730 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term754 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409242 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term755 _88563 _88564 _88565 P) = (term731 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409241 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409243 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409244 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term756 _88563 _88564 _88565 P) = (term732 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409243 _88565) (@lem3409242 _88563 _88564 _88565 P)). Qed.
Lemma lem3409245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409246 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term757 _88563 _88564 _88565 P) = (term746 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409245) (@lem3409244 _88563 _88564 _88565 P)). Qed.
Lemma lem3409247 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term466 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term466 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409248 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term476 _88563 _88564 _88565 P) = (term463 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409247 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409249 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409250 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term477 _88563 _88564 _88565 P) = (term478 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409249 _88565) (@lem3409248 _88563 _88564 _88565 P)). Qed.
Lemma lem3409251 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term752 _88563 _88564 _88565 P) = (term748 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409246 _88563 _88564 _88565 P) (@lem3409250 _88563 _88564 _88565 P)). Qed.
Lemma lem3409252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409253 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term758 _88563 _88564 _88565 P) = (term759 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409252) (@lem3409251 _88563 _88564 _88565 P)). Qed.
Lemma lem3409254 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term754 _88563 _88564 _88565 P a) = (term730 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term754 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409256 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term760 _88563 _88564 _88565 P a) = (term761 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409255) (@lem3409254 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409257 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term466 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term466 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409258 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term762 _88563 _88564 _88565 P a) = (term763 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409256 _88563 _88564 _88565 P a) (@lem3409257 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409259 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term764 _88563 _88564 _88565 P) = (term765 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409258 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409260 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409261 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term753 _88563 _88564 _88565 P) = (term766 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409260 _88565) (@lem3409259 _88563 _88564 _88565 P)). Qed.
Lemma lem3409262 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : ((term752 _88563 _88564 _88565 P) = (term753 _88563 _88564 _88565 P)) = ((term748 _88563 _88564 _88565 P) = (term766 _88563 _88564 _88565 P)).
Proof. exact (MK_COMB (@lem3409253 _88563 _88564 _88565 P) (@lem3409261 _88563 _88564 _88565 P)). Qed.
Lemma lem3409263 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term748 _88563 _88564 _88565 P) = (term766 _88563 _88564 _88565 P).
Proof. exact (EQ_MP (@lem3409262 _88563 _88564 _88565 P) (@lem3409240 _88563 _88564 _88565 P)). Qed.
Lemma lem3409265 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3409266 {_88564 : Type'} (P : _88564 -> Prop) (Q : _88564 -> Prop) : (term326 _88564 P Q) = (term325 _88564 P Q).
Proof. exact (@lem3409265 _88564 P Q). Qed.
Lemma lem3409267 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term767 _88563 _88564 _88565 P a) = (term768 _88563 _88564 _88565 P a).
Proof. exact (@lem3409266 _88564 (term729 _88563 _88564 _88565 P a) (term441 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409268 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term769 _88563 _88564 _88565 P a b) = (term728 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term769 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409269 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term770 _88563 _88564 _88565 P a) = (term729 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409268 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409270 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409271 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term771 _88563 _88564 _88565 P a) = (term730 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409270 _88564) (@lem3409269 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409273 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term772 _88563 _88564 _88565 P a) = (term761 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409272) (@lem3409271 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409274 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term444 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term444 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409275 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term454 _88563 _88564 _88565 P a) = (term441 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409274 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409276 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409277 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term455 _88563 _88564 _88565 P a) = (term456 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409276 _88564) (@lem3409275 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409278 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term767 _88563 _88564 _88565 P a) = (term763 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409273 _88563 _88564 _88565 P a) (@lem3409277 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409280 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term773 _88563 _88564 _88565 P a) = (term774 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409279) (@lem3409278 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409281 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term769 _88563 _88564 _88565 P a b) = (term728 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term769 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409283 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term775 _88563 _88564 _88565 P a b) = (term776 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409282) (@lem3409281 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409284 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term444 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term444 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409285 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term777 _88563 _88564 _88565 P a b) = (term778 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409283 _88563 _88564 _88565 P a b) (@lem3409284 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409286 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term779 _88563 _88564 _88565 P a) = (term780 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409285 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409287 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409288 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term768 _88563 _88564 _88565 P a) = (term781 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409287 _88564) (@lem3409286 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409289 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : ((term767 _88563 _88564 _88565 P a) = (term768 _88563 _88564 _88565 P a)) = ((term763 _88563 _88564 _88565 P a) = (term781 _88563 _88564 _88565 P a)).
Proof. exact (MK_COMB (@lem3409280 _88563 _88564 _88565 P a) (@lem3409288 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409290 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term763 _88563 _88564 _88565 P a) = (term781 _88563 _88564 _88565 P a).
Proof. exact (EQ_MP (@lem3409289 _88563 _88564 _88565 P a) (@lem3409267 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409292 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term326 A P Q) = (term325 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3409293 {_88563 : Type'} (P : _88563 -> Prop) (Q : _88563 -> Prop) : (term326 _88563 P Q) = (term325 _88563 P Q).
Proof. exact (@lem3409292 _88563 P Q). Qed.
Lemma lem3409294 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term782 _88563 _88564 _88565 P a b) = (term783 _88563 _88564 _88565 P a b).
Proof. exact (@lem3409293 _88563 (term727 _88563 _88564 _88565 P a b) (term419 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409295 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term784 _88563 _88564 _88565 P a b c) = (term726 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term784 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409296 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term785 _88563 _88564 _88565 P a b) = (term727 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409295 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409297 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409298 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term786 _88563 _88564 _88565 P a b) = (term728 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409297 _88563) (@lem3409296 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409300 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term787 _88563 _88564 _88565 P a b) = (term776 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409299) (@lem3409298 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409301 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term422 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term422 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409302 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term432 _88563 _88564 _88565 P a b) = (term419 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409301 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409303 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409304 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term433 _88563 _88564 _88565 P a b) = (term434 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409303 _88563) (@lem3409302 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409305 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term782 _88563 _88564 _88565 P a b) = (term778 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409300 _88563 _88564 _88565 P a b) (@lem3409304 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409307 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term788 _88563 _88564 _88565 P a b) = (term789 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409306) (@lem3409305 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409308 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term784 _88563 _88564 _88565 P a b c) = (term726 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term784 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409310 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term790 _88563 _88564 _88565 P a b c) = (term791 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409309) (@lem3409308 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409311 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term422 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term422 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409312 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term792 _88563 _88564 _88565 P a b c) = (term793 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409310 _88563 _88564 _88565 P a b c) (@lem3409311 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409313 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term794 _88563 _88564 _88565 P a b) = (term795 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409312 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409314 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409315 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term783 _88563 _88564 _88565 P a b) = (term796 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409314 _88563) (@lem3409313 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409316 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : ((term782 _88563 _88564 _88565 P a b) = (term783 _88563 _88564 _88565 P a b)) = ((term778 _88563 _88564 _88565 P a b) = (term796 _88563 _88564 _88565 P a b)).
Proof. exact (MK_COMB (@lem3409307 _88563 _88564 _88565 P a b) (@lem3409315 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409317 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term778 _88563 _88564 _88565 P a b) = (term796 _88563 _88564 _88565 P a b).
Proof. exact (EQ_MP (@lem3409316 _88563 _88564 _88565 P a b) (@lem3409294 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409319 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409320 {_88565 : Type'} (P : _88565 -> Prop) (Q : Prop) : (term621 _88565 P Q) = (term622 _88565 P Q).
Proof. exact (@lem3409319 _88565 P Q). Qed.
Lemma lem3409321 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term797 _88563 _88564 _88565 P a b c) = (term798 _88563 _88564 _88565 P a b c).
Proof. exact (@lem3409320 _88565 (term725 _88563 _88564 _88565 P a b c) (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409322 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term799 _88563 _88564 _88565 P a b c x) = (term724 _88563 _88564 _88565 x P a b c).
Proof. exact (eq_refl (term799 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409323 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term800 _88563 _88564 _88565 P a b c) = (term725 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409322 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409324 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409325 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term801 _88563 _88564 _88565 P a b c) = (term726 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409324 _88565) (@lem3409323 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409327 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term802 _88563 _88564 _88565 P a b c) = (term791 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409326) (@lem3409325 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409328 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409329 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term797 _88563 _88564 _88565 P a b c) = (term793 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409327 _88563 _88564 _88565 P a b c) (@lem3409328 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409331 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term803 _88563 _88564 _88565 P a b c) = (term804 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409330) (@lem3409329 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409332 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term799 _88563 _88564 _88565 P a b c x) = (term724 _88563 _88564 _88565 x P a b c).
Proof. exact (eq_refl (term799 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409334 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term805 _88563 _88564 _88565 P a b c x) = (term806 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409333) (@lem3409332 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409335 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409336 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term807 _88563 _88564 _88565 x P a b c) = (term808 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409334 _88563 _88564 _88565 x P a b c) (@lem3409335 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409337 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term809 _88563 _88564 _88565 P a b c) = (term810 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409336 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409338 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409339 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term798 _88563 _88564 _88565 P a b c) = (term811 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409338 _88565) (@lem3409337 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409340 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term797 _88563 _88564 _88565 P a b c) = (term798 _88563 _88564 _88565 P a b c)) = ((term793 _88563 _88564 _88565 P a b c) = (term811 _88563 _88564 _88565 P a b c)).
Proof. exact (MK_COMB (@lem3409331 _88563 _88564 _88565 P a b c) (@lem3409339 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409341 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term793 _88563 _88564 _88565 P a b c) = (term811 _88563 _88564 _88565 P a b c).
Proof. exact (EQ_MP (@lem3409340 _88563 _88564 _88565 P a b c) (@lem3409321 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409343 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409344 {_88564 : Type'} (P : _88564 -> Prop) (Q : Prop) : (term621 _88564 P Q) = (term622 _88564 P Q).
Proof. exact (@lem3409343 _88564 P Q). Qed.
Lemma lem3409345 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term812 _88563 _88564 _88565 x P a b c) = (term813 _88563 _88564 _88565 x P a b c).
Proof. exact (@lem3409344 _88564 (term723 _88563 _88564 _88565 x P a b c) (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409346 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term814 _88563 _88564 _88565 x P a b c y) = (term722 _88563 _88564 _88565 x y P a b c).
Proof. exact (eq_refl (term814 _88563 _88564 _88565 x P a b c y)). Qed.
Lemma lem3409347 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term815 _88563 _88564 _88565 x P a b c) = (term723 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409346 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409348 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409349 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term816 _88563 _88564 _88565 x P a b c) = (term724 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409348 _88564) (@lem3409347 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409351 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term817 _88563 _88564 _88565 x P a b c) = (term806 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409350) (@lem3409349 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409352 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409353 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term812 _88563 _88564 _88565 x P a b c) = (term808 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409351 _88563 _88564 _88565 x P a b c) (@lem3409352 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409355 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term818 _88563 _88564 _88565 x P a b c) = (term819 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409354) (@lem3409353 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409356 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term814 _88563 _88564 _88565 x P a b c y) = (term722 _88563 _88564 _88565 x y P a b c).
Proof. exact (eq_refl (term814 _88563 _88564 _88565 x P a b c y)). Qed.
Lemma lem3409357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409358 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term820 _88563 _88564 _88565 x P a b c y) = (term821 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409357) (@lem3409356 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409359 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409360 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term822 _88563 _88564 _88565 x y P a b c) = (term823 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409358 _88563 _88564 _88565 x y P a b c) (@lem3409359 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409361 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term824 _88563 _88564 _88565 x P a b c) = (term825 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409360 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409362 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409363 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term813 _88563 _88564 _88565 x P a b c) = (term826 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409362 _88564) (@lem3409361 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409364 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term812 _88563 _88564 _88565 x P a b c) = (term813 _88563 _88564 _88565 x P a b c)) = ((term808 _88563 _88564 _88565 x P a b c) = (term826 _88563 _88564 _88565 x P a b c)).
Proof. exact (MK_COMB (@lem3409355 _88563 _88564 _88565 x P a b c) (@lem3409363 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409365 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term808 _88563 _88564 _88565 x P a b c) = (term826 _88563 _88564 _88565 x P a b c).
Proof. exact (EQ_MP (@lem3409364 _88563 _88564 _88565 x P a b c) (@lem3409345 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409367 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409368 {_88563 : Type'} (P : _88563 -> Prop) (Q : Prop) : (term621 _88563 P Q) = (term622 _88563 P Q).
Proof. exact (@lem3409367 _88563 P Q). Qed.
Lemma lem3409369 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term827 _88563 _88564 _88565 x y P a b c) = (term828 _88563 _88564 _88565 x y P a b c).
Proof. exact (@lem3409368 _88563 (term721 _88563 _88564 _88565 x y P a b c) (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409370 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term829 _88563 _88564 _88565 x y P a b c z) = (term719 _88563 _88564 _88565 x y z P a b c).
Proof. exact (eq_refl (term829 _88563 _88564 _88565 x y P a b c z)). Qed.
Lemma lem3409371 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term830 _88563 _88564 _88565 x y P a b c) = (term721 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88563 => @lem3409370 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409372 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409373 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term831 _88563 _88564 _88565 x y P a b c) = (term722 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409372 _88563) (@lem3409371 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409375 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term832 _88563 _88564 _88565 x y P a b c) = (term821 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409374) (@lem3409373 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409376 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409377 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term827 _88563 _88564 _88565 x y P a b c) = (term823 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409375 _88563 _88564 _88565 x y P a b c) (@lem3409376 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409379 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term833 _88563 _88564 _88565 x y P a b c) = (term834 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409378) (@lem3409377 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409380 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term829 _88563 _88564 _88565 x y P a b c z) = (term719 _88563 _88564 _88565 x y z P a b c).
Proof. exact (eq_refl (term829 _88563 _88564 _88565 x y P a b c z)). Qed.
Lemma lem3409381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409382 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term835 _88563 _88564 _88565 x y P a b c z) = (term836 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409381) (@lem3409380 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409383 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term286 _88563 _88564 _88565 P a b c) = (term286 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term286 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409384 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term837 _88563 _88564 _88565 x y z P a b c) = (term838 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409382 _88563 _88564 _88565 x y z P a b c) (@lem3409383 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409385 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term839 _88563 _88564 _88565 x y P a b c) = (term840 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88563 => @lem3409384 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409386 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409387 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term828 _88563 _88564 _88565 x y P a b c) = (term841 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409386 _88563) (@lem3409385 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409388 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : ((term827 _88563 _88564 _88565 x y P a b c) = (term828 _88563 _88564 _88565 x y P a b c)) = ((term823 _88563 _88564 _88565 x y P a b c) = (term841 _88563 _88564 _88565 x y P a b c)).
Proof. exact (MK_COMB (@lem3409379 _88563 _88564 _88565 x y P a b c) (@lem3409387 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409389 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term823 _88563 _88564 _88565 x y P a b c) = (term841 _88563 _88564 _88565 x y P a b c).
Proof. exact (EQ_MP (@lem3409388 _88563 _88564 _88565 x y P a b c) (@lem3409369 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409390 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term825 _88563 _88564 _88565 x P a b c) = (term842 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409389 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409391 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409392 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term826 _88563 _88564 _88565 x P a b c) = (term843 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409391 _88564) (@lem3409390 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409393 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term808 _88563 _88564 _88565 x P a b c) = (term843 _88563 _88564 _88565 x P a b c).
Proof. exact (TRANS (@lem3409365 _88563 _88564 _88565 x P a b c) (@lem3409392 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409394 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term810 _88563 _88564 _88565 P a b c) = (term844 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409393 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409395 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409396 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term811 _88563 _88564 _88565 P a b c) = (term845 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409395 _88565) (@lem3409394 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409397 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term793 _88563 _88564 _88565 P a b c) = (term845 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3409341 _88563 _88564 _88565 P a b c) (@lem3409396 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409398 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term795 _88563 _88564 _88565 P a b) = (term846 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409397 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409399 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409400 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term796 _88563 _88564 _88565 P a b) = (term847 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409399 _88563) (@lem3409398 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409401 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term778 _88563 _88564 _88565 P a b) = (term847 _88563 _88564 _88565 P a b).
Proof. exact (TRANS (@lem3409317 _88563 _88564 _88565 P a b) (@lem3409400 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409402 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term780 _88563 _88564 _88565 P a) = (term848 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409401 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409403 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409404 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term781 _88563 _88564 _88565 P a) = (term849 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409403 _88564) (@lem3409402 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409405 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term763 _88563 _88564 _88565 P a) = (term849 _88563 _88564 _88565 P a).
Proof. exact (TRANS (@lem3409290 _88563 _88564 _88565 P a) (@lem3409404 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409406 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term765 _88563 _88564 _88565 P) = (term850 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409405 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409407 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409408 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term766 _88563 _88564 _88565 P) = (term851 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409407 _88565) (@lem3409406 _88563 _88564 _88565 P)). Qed.
Lemma lem3409409 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term748 _88563 _88564 _88565 P) = (term851 _88563 _88564 _88565 P).
Proof. exact (TRANS (@lem3409263 _88563 _88564 _88565 P) (@lem3409408 _88563 _88564 _88565 P)). Qed.
Lemma lem3409410 {_88563 _88564 _88565 : Type'} : (term750 _88563 _88564 _88565) = (term852 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409409 _88563 _88564 _88565 P)). Qed.
Lemma lem3409411 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409412 {_88563 _88564 _88565 : Type'} : (term751 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409411 _88563 _88564 _88565) (@lem3409410 _88563 _88564 _88565)). Qed.
Lemma lem3409413 {_88563 _88564 _88565 : Type'} : (term736 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3409236 _88563 _88564 _88565) (@lem3409412 _88563 _88564 _88565)). Qed.
Lemma lem3409414 {_88563 _88564 _88565 : Type'} : (term501 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3409209 _88563 _88564 _88565) (@lem3409413 _88563 _88564 _88565)). Qed.
Lemma lem3409415 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term502 _88500 _88501 _88502 _88563 _88564 _88565) = (term854 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409113 _88500 _88501 _88502) (@lem3409414 _88563 _88564 _88565)). Qed.
Lemma lem3409419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409420 {_88500 _88501 _88502 : Type'} (P : type871 _88500 _88501 _88502) (Q : Prop) : (term855 _88500 _88501 _88502 P Q) = (term856 _88500 _88501 _88502 P Q).
Proof. exact (@lem3409419 (type1517 _88500 _88501 _88502) P Q). Qed.
Lemma lem3409421 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term857 _88500 _88501 _88502 _88563 _88564 _88565) = (term858 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (@lem3409420 _88500 _88501 _88502 (term678 _88500 _88501 _88502) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409422 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term859 _88500 _88501 _88502 P) = (term677 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term859 _88500 _88501 _88502 P)). Qed.
Lemma lem3409423 {_88500 _88501 _88502 : Type'} : (term860 _88500 _88501 _88502) = (term678 _88500 _88501 _88502).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3409422 _88500 _88501 _88502 P)). Qed.
Lemma lem3409424 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3409425 {_88500 _88501 _88502 : Type'} : (term861 _88500 _88501 _88502) = (term679 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3409424 _88500 _88501 _88502) (@lem3409423 _88500 _88501 _88502)). Qed.
Lemma lem3409426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409427 {_88500 _88501 _88502 : Type'} : (term862 _88500 _88501 _88502) = (term680 _88500 _88501 _88502).
Proof. exact (MK_COMB (@lem3409426) (@lem3409425 _88500 _88501 _88502)). Qed.
Lemma lem3409428 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409429 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term857 _88500 _88501 _88502 _88563 _88564 _88565) = (term854 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409427 _88500 _88501 _88502) (@lem3409428 _88563 _88564 _88565)). Qed.
Lemma lem3409430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409431 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term863 _88500 _88501 _88502 _88563 _88564 _88565) = (term864 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409430) (@lem3409429 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409432 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term859 _88500 _88501 _88502 P) = (term677 _88500 _88501 _88502 P).
Proof. exact (eq_refl (term859 _88500 _88501 _88502 P)). Qed.
Lemma lem3409433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409434 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term865 _88500 _88501 _88502 P) = (term866 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3409433) (@lem3409432 _88500 _88501 _88502 P)). Qed.
Lemma lem3409435 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409436 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term867 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term868 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409434 _88500 _88501 _88502 P) (@lem3409435 _88563 _88564 _88565)). Qed.
Lemma lem3409437 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term869 _88500 _88501 _88502 _88563 _88564 _88565) = (term870 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3409436 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409438 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3409439 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term858 _88500 _88501 _88502 _88563 _88564 _88565) = (term871 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409438 _88500 _88501 _88502) (@lem3409437 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409440 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : ((term857 _88500 _88501 _88502 _88563 _88564 _88565) = (term858 _88500 _88501 _88502 _88563 _88564 _88565)) = ((term854 _88500 _88501 _88502 _88563 _88564 _88565) = (term871 _88500 _88501 _88502 _88563 _88564 _88565)).
Proof. exact (MK_COMB (@lem3409431 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409439 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409441 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term854 _88500 _88501 _88502 _88563 _88564 _88565) = (term871 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (EQ_MP (@lem3409440 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409421 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409445 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409446 {_88502 : Type'} (P : _88502 -> Prop) (Q : Prop) : (term621 _88502 P Q) = (term622 _88502 P Q).
Proof. exact (@lem3409445 _88502 P Q). Qed.
Lemma lem3409447 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term872 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term873 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (@lem3409446 _88502 (term676 _88500 _88501 _88502 P) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409448 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term874 _88500 _88501 _88502 P a) = (term675 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term874 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409449 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term875 _88500 _88501 _88502 P) = (term676 _88500 _88501 _88502 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3409448 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409450 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409451 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term876 _88500 _88501 _88502 P) = (term677 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3409450 _88502) (@lem3409449 _88500 _88501 _88502 P)). Qed.
Lemma lem3409452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409453 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) : (term877 _88500 _88501 _88502 P) = (term866 _88500 _88501 _88502 P).
Proof. exact (MK_COMB (@lem3409452) (@lem3409451 _88500 _88501 _88502 P)). Qed.
Lemma lem3409454 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409455 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term872 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term868 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409453 _88500 _88501 _88502 P) (@lem3409454 _88563 _88564 _88565)). Qed.
Lemma lem3409456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409457 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term878 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term879 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409456) (@lem3409455 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409458 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term874 _88500 _88501 _88502 P a) = (term675 _88500 _88501 _88502 P a).
Proof. exact (eq_refl (term874 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409460 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term880 _88500 _88501 _88502 P a) = (term881 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3409459) (@lem3409458 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409461 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409462 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term882 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term883 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409460 _88500 _88501 _88502 P a) (@lem3409461 _88563 _88564 _88565)). Qed.
Lemma lem3409463 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term884 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term885 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3409462 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409464 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409465 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term873 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term886 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409464 _88502) (@lem3409463 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409466 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : ((term872 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term873 _88500 _88501 _88502 _88563 _88564 _88565 P)) = ((term868 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term886 _88500 _88501 _88502 _88563 _88564 _88565 P)).
Proof. exact (MK_COMB (@lem3409457 _88500 _88501 _88502 _88563 _88564 _88565 P) (@lem3409465 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409467 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term868 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term886 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (EQ_MP (@lem3409466 _88500 _88501 _88502 _88563 _88564 _88565 P) (@lem3409447 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409471 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409472 {_88501 : Type'} (P : _88501 -> Prop) (Q : Prop) : (term621 _88501 P Q) = (term622 _88501 P Q).
Proof. exact (@lem3409471 _88501 P Q). Qed.
Lemma lem3409473 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term887 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term888 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (@lem3409472 _88501 (term674 _88500 _88501 _88502 P a) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409474 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term889 _88500 _88501 _88502 P a b) = (term673 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term889 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409475 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term890 _88500 _88501 _88502 P a) = (term674 _88500 _88501 _88502 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3409474 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409476 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409477 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term891 _88500 _88501 _88502 P a) = (term675 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3409476 _88501) (@lem3409475 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409479 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term892 _88500 _88501 _88502 P a) = (term881 _88500 _88501 _88502 P a).
Proof. exact (MK_COMB (@lem3409478) (@lem3409477 _88500 _88501 _88502 P a)). Qed.
Lemma lem3409480 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409481 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term887 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term883 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409479 _88500 _88501 _88502 P a) (@lem3409480 _88563 _88564 _88565)). Qed.
Lemma lem3409482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409483 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term893 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term894 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409482) (@lem3409481 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409484 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term889 _88500 _88501 _88502 P a b) = (term673 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term889 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409486 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term895 _88500 _88501 _88502 P a b) = (term896 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409485) (@lem3409484 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409487 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409488 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term897 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term898 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409486 _88500 _88501 _88502 P a b) (@lem3409487 _88563 _88564 _88565)). Qed.
Lemma lem3409489 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term899 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term900 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3409488 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409490 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409491 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term888 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term901 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409490 _88501) (@lem3409489 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409492 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : ((term887 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term888 _88500 _88501 _88502 _88563 _88564 _88565 P a)) = ((term883 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term901 _88500 _88501 _88502 _88563 _88564 _88565 P a)).
Proof. exact (MK_COMB (@lem3409483 _88500 _88501 _88502 _88563 _88564 _88565 P a) (@lem3409491 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409493 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term883 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term901 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (EQ_MP (@lem3409492 _88500 _88501 _88502 _88563 _88564 _88565 P a) (@lem3409473 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409497 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409498 {_88500 : Type'} (P : _88500 -> Prop) (Q : Prop) : (term621 _88500 P Q) = (term622 _88500 P Q).
Proof. exact (@lem3409497 _88500 P Q). Qed.
Lemma lem3409499 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term902 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term903 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (@lem3409498 _88500 (term672 _88500 _88501 _88502 P a b) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409500 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term904 _88500 _88501 _88502 P a b c) = (term671 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term904 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409501 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term905 _88500 _88501 _88502 P a b) = (term672 _88500 _88501 _88502 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3409500 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409502 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409503 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term906 _88500 _88501 _88502 P a b) = (term673 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409502 _88500) (@lem3409501 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409504 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409505 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term907 _88500 _88501 _88502 P a b) = (term896 _88500 _88501 _88502 P a b).
Proof. exact (MK_COMB (@lem3409504) (@lem3409503 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3409506 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409507 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term902 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term898 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409505 _88500 _88501 _88502 P a b) (@lem3409506 _88563 _88564 _88565)). Qed.
Lemma lem3409508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409509 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term908 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term909 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409508) (@lem3409507 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409510 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term904 _88500 _88501 _88502 P a b c) = (term671 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term904 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409512 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term910 _88500 _88501 _88502 P a b c) = (term911 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409511) (@lem3409510 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409513 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409514 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term912 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term913 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409512 _88500 _88501 _88502 P a b c) (@lem3409513 _88563 _88564 _88565)). Qed.
Lemma lem3409515 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term914 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term915 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3409514 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409516 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409517 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term903 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term916 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409516 _88500) (@lem3409515 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409518 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : ((term902 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term903 _88500 _88501 _88502 _88563 _88564 _88565 P a b)) = ((term898 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term916 _88500 _88501 _88502 _88563 _88564 _88565 P a b)).
Proof. exact (MK_COMB (@lem3409509 _88500 _88501 _88502 _88563 _88564 _88565 P a b) (@lem3409517 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409519 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term898 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term916 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (EQ_MP (@lem3409518 _88500 _88501 _88502 _88563 _88564 _88565 P a b) (@lem3409499 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409523 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409524 {_88502 : Type'} (P : _88502 -> Prop) (Q : Prop) : (term621 _88502 P Q) = (term622 _88502 P Q).
Proof. exact (@lem3409523 _88502 P Q). Qed.
Lemma lem3409525 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term917 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term918 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (@lem3409524 _88502 (term670 _88500 _88501 _88502 P a b c) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409526 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term919 _88500 _88501 _88502 P a b c x) = (term669 _88500 _88501 _88502 x P a b c).
Proof. exact (eq_refl (term919 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3409527 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term920 _88500 _88501 _88502 P a b c) = (term670 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409526 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409528 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409529 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term921 _88500 _88501 _88502 P a b c) = (term671 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409528 _88502) (@lem3409527 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409531 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term922 _88500 _88501 _88502 P a b c) = (term911 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409530) (@lem3409529 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409532 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409533 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term917 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term913 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409531 _88500 _88501 _88502 P a b c) (@lem3409532 _88563 _88564 _88565)). Qed.
Lemma lem3409534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409535 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term923 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term924 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409534) (@lem3409533 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409536 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term919 _88500 _88501 _88502 P a b c x) = (term669 _88500 _88501 _88502 x P a b c).
Proof. exact (eq_refl (term919 _88500 _88501 _88502 P a b c x)). Qed.
Lemma lem3409537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409538 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term925 _88500 _88501 _88502 P a b c x) = (term926 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409537) (@lem3409536 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409539 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409540 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term927 _88500 _88501 _88502 _88563 _88564 _88565 P a b c x) = (term928 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409538 _88500 _88501 _88502 x P a b c) (@lem3409539 _88563 _88564 _88565)). Qed.
Lemma lem3409541 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term929 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term930 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409540 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409542 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409543 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term918 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term931 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409542 _88502) (@lem3409541 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409544 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term917 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term918 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)) = ((term913 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term931 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)).
Proof. exact (MK_COMB (@lem3409535 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) (@lem3409543 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409545 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term913 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term931 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (EQ_MP (@lem3409544 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) (@lem3409525 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409549 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409550 {_88501 : Type'} (P : _88501 -> Prop) (Q : Prop) : (term621 _88501 P Q) = (term622 _88501 P Q).
Proof. exact (@lem3409549 _88501 P Q). Qed.
Lemma lem3409551 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term932 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term933 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (@lem3409550 _88501 (term668 _88500 _88501 _88502 x P a b c) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409552 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term934 _88500 _88501 _88502 x P a b c y) = (term667 _88500 _88501 _88502 x y P a b c).
Proof. exact (eq_refl (term934 _88500 _88501 _88502 x P a b c y)). Qed.
Lemma lem3409553 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term935 _88500 _88501 _88502 x P a b c) = (term668 _88500 _88501 _88502 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409552 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409554 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409555 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term936 _88500 _88501 _88502 x P a b c) = (term669 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409554 _88501) (@lem3409553 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409557 {_88500 _88501 _88502 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term937 _88500 _88501 _88502 x P a b c) = (term926 _88500 _88501 _88502 x P a b c).
Proof. exact (MK_COMB (@lem3409556) (@lem3409555 _88500 _88501 _88502 x P a b c)). Qed.
Lemma lem3409558 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409559 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term932 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term928 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409557 _88500 _88501 _88502 x P a b c) (@lem3409558 _88563 _88564 _88565)). Qed.
Lemma lem3409560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409561 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term938 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term939 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409560) (@lem3409559 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409562 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term934 _88500 _88501 _88502 x P a b c y) = (term667 _88500 _88501 _88502 x y P a b c).
Proof. exact (eq_refl (term934 _88500 _88501 _88502 x P a b c y)). Qed.
Lemma lem3409563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409564 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term940 _88500 _88501 _88502 x P a b c y) = (term941 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409563) (@lem3409562 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409565 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409566 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term942 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c y) = (term943 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409564 _88500 _88501 _88502 x y P a b c) (@lem3409565 _88563 _88564 _88565)). Qed.
Lemma lem3409567 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term944 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term945 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409566 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409568 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409569 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term933 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term946 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409568 _88501) (@lem3409567 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409570 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term932 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term933 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)) = ((term928 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term946 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)).
Proof. exact (MK_COMB (@lem3409561 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) (@lem3409569 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409571 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term928 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term946 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (EQ_MP (@lem3409570 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) (@lem3409551 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409575 {A : Type'} (P : A -> Prop) (Q : Prop) : (term621 A P Q) = (term622 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3409576 {_88500 : Type'} (P : _88500 -> Prop) (Q : Prop) : (term621 _88500 P Q) = (term622 _88500 P Q).
Proof. exact (@lem3409575 _88500 P Q). Qed.
Lemma lem3409577 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term947 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term948 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (@lem3409576 _88500 (term666 _88500 _88501 _88502 x y P a b c) (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409578 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term949 _88500 _88501 _88502 x y P a b c z) = (term664 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term949 _88500 _88501 _88502 x y P a b c z)). Qed.
Lemma lem3409579 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term950 _88500 _88501 _88502 x y P a b c) = (term666 _88500 _88501 _88502 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409578 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409580 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409581 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term951 _88500 _88501 _88502 x y P a b c) = (term667 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409580 _88500) (@lem3409579 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409583 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term952 _88500 _88501 _88502 x y P a b c) = (term941 _88500 _88501 _88502 x y P a b c).
Proof. exact (MK_COMB (@lem3409582) (@lem3409581 _88500 _88501 _88502 x y P a b c)). Qed.
Lemma lem3409584 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409585 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term947 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term943 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409583 _88500 _88501 _88502 x y P a b c) (@lem3409584 _88563 _88564 _88565)). Qed.
Lemma lem3409586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409587 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term953 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term954 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409586) (@lem3409585 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409588 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term949 _88500 _88501 _88502 x y P a b c z) = (term664 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term949 _88500 _88501 _88502 x y P a b c z)). Qed.
Lemma lem3409589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3409590 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term955 _88500 _88501 _88502 x y P a b c z) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3409589) (@lem3409588 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409591 {_88563 _88564 _88565 : Type'} : (term853 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (eq_refl (term853 _88563 _88564 _88565)). Qed.
Lemma lem3409592 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term957 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c z) = (term958 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409590 _88500 _88501 _88502 x y z P a b c) (@lem3409591 _88563 _88564 _88565)). Qed.
Lemma lem3409593 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term959 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term960 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409592 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409594 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409595 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term948 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term961 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409594 _88500) (@lem3409593 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409596 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term947 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term948 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)) = ((term943 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term961 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)).
Proof. exact (MK_COMB (@lem3409587 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) (@lem3409595 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409597 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term943 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term961 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (EQ_MP (@lem3409596 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) (@lem3409577 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409599 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409600 {_88563 _88564 _88565 : Type'} (P : Prop) (Q : type871 _88563 _88564 _88565) : (term964 _88563 _88564 _88565 P Q) = (term965 _88563 _88564 _88565 P Q).
Proof. exact (@lem3409599 (type1517 _88563 _88564 _88565) P Q). Qed.
Lemma lem3409601 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term966 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term967 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (@lem3409600 _88563 _88564 _88565 (term664 _88500 _88501 _88502 x y z P a b c) (term852 _88563 _88564 _88565)). Qed.
Lemma lem3409602 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term968 _88563 _88564 _88565 P) = (term851 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term968 _88563 _88564 _88565 P)). Qed.
Lemma lem3409603 {_88563 _88564 _88565 : Type'} : (term969 _88563 _88564 _88565) = (term852 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88563 _88564 _88565 => @lem3409602 _88563 _88564 _88565 P)). Qed.
Lemma lem3409604 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409605 {_88563 _88564 _88565 : Type'} : (term970 _88563 _88564 _88565) = (term853 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409604 _88563 _88564 _88565) (@lem3409603 _88563 _88564 _88565)). Qed.
Lemma lem3409606 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409607 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term966 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term958 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409606 _88500 _88501 _88502 x y z P a b c) (@lem3409605 _88563 _88564 _88565)). Qed.
Lemma lem3409608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409609 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term971 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term972 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409608) (@lem3409607 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409610 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term968 _88563 _88564 _88565 P) = (term851 _88563 _88564 _88565 P).
Proof. exact (eq_refl (term968 _88563 _88564 _88565 P)). Qed.
Lemma lem3409611 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409612 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term973 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term974 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (MK_COMB (@lem3409611 _88500 _88501 _88502 x y z P a b c) (@lem3409610 _88563 _88564 _88565 P')). Qed.
Lemma lem3409613 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term975 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term976 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (fun_ext (fun P' : type1517 _88563 _88564 _88565 => @lem3409612 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409614 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409615 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term967 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term977 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409614 _88563 _88564 _88565) (@lem3409613 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409616 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : ((term966 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term967 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)) = ((term958 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term977 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)).
Proof. exact (MK_COMB (@lem3409609 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) (@lem3409615 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409617 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term958 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term977 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (EQ_MP (@lem3409616 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) (@lem3409601 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409620 {_88565 : Type'} (P : Prop) (Q : _88565 -> Prop) : (term962 _88565 P Q) = (term963 _88565 P Q).
Proof. exact (@lem3409619 _88565 P Q). Qed.
Lemma lem3409621 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term978 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term979 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (@lem3409620 _88565 (term664 _88500 _88501 _88502 x y z P a b c) (term850 _88563 _88564 _88565 P')). Qed.
Lemma lem3409622 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term980 _88563 _88564 _88565 P a) = (term849 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term980 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409623 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term981 _88563 _88564 _88565 P) = (term850 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88565 => @lem3409622 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409624 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409625 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) : (term982 _88563 _88564 _88565 P) = (term851 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409624 _88565) (@lem3409623 _88563 _88564 _88565 P)). Qed.
Lemma lem3409626 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409627 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term978 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term974 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (MK_COMB (@lem3409626 _88500 _88501 _88502 x y z P a b c) (@lem3409625 _88563 _88564 _88565 P')). Qed.
Lemma lem3409628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409629 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term983 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term984 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (MK_COMB (@lem3409628) (@lem3409627 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409630 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term980 _88563 _88564 _88565 P a) = (term849 _88563 _88564 _88565 P a).
Proof. exact (eq_refl (term980 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409631 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409632 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term985 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term986 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (MK_COMB (@lem3409631 _88500 _88501 _88502 x y z P a b c) (@lem3409630 _88563 _88564 _88565 P' a')). Qed.
Lemma lem3409633 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term987 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term988 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (fun_ext (fun a' : _88565 => @lem3409632 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409634 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409635 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term979 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term989 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (MK_COMB (@lem3409634 _88565) (@lem3409633 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409636 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : ((term978 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term979 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')) = ((term974 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term989 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')).
Proof. exact (MK_COMB (@lem3409629 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') (@lem3409635 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409637 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term974 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term989 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (EQ_MP (@lem3409636 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') (@lem3409621 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409639 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409640 {_88564 : Type'} (P : Prop) (Q : _88564 -> Prop) : (term962 _88564 P Q) = (term963 _88564 P Q).
Proof. exact (@lem3409639 _88564 P Q). Qed.
Lemma lem3409641 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term990 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term991 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (@lem3409640 _88564 (term664 _88500 _88501 _88502 x y z P a b c) (term848 _88563 _88564 _88565 P' a')). Qed.
Lemma lem3409642 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term992 _88563 _88564 _88565 P a b) = (term847 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term992 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409643 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term993 _88563 _88564 _88565 P a) = (term848 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88564 => @lem3409642 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409644 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409645 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) : (term994 _88563 _88564 _88565 P a) = (term849 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409644 _88564) (@lem3409643 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409646 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409647 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term990 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term986 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (MK_COMB (@lem3409646 _88500 _88501 _88502 x y z P a b c) (@lem3409645 _88563 _88564 _88565 P' a')). Qed.
Lemma lem3409648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409649 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term995 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term996 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (MK_COMB (@lem3409648) (@lem3409647 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409650 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term992 _88563 _88564 _88565 P a b) = (term847 _88563 _88564 _88565 P a b).
Proof. exact (eq_refl (term992 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409651 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409652 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term997 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term998 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (MK_COMB (@lem3409651 _88500 _88501 _88502 x y z P a b c) (@lem3409650 _88563 _88564 _88565 P' a' b')). Qed.
Lemma lem3409653 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term999 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1000 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (fun_ext (fun b' : _88564 => @lem3409652 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409654 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409655 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term991 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1001 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (MK_COMB (@lem3409654 _88564) (@lem3409653 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409656 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : ((term990 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term991 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')) = ((term986 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1001 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')).
Proof. exact (MK_COMB (@lem3409649 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') (@lem3409655 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409657 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term986 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1001 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (EQ_MP (@lem3409656 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') (@lem3409641 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409659 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409660 {_88563 : Type'} (P : Prop) (Q : _88563 -> Prop) : (term962 _88563 P Q) = (term963 _88563 P Q).
Proof. exact (@lem3409659 _88563 P Q). Qed.
Lemma lem3409661 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1002 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1003 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (@lem3409660 _88563 (term664 _88500 _88501 _88502 x y z P a b c) (term846 _88563 _88564 _88565 P' a' b')). Qed.
Lemma lem3409662 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1004 _88563 _88564 _88565 P a b c) = (term845 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term1004 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409663 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term1005 _88563 _88564 _88565 P a b) = (term846 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88563 => @lem3409662 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409664 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409665 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) : (term1006 _88563 _88564 _88565 P a b) = (term847 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409664 _88563) (@lem3409663 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409666 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409667 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1002 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term998 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (MK_COMB (@lem3409666 _88500 _88501 _88502 x y z P a b c) (@lem3409665 _88563 _88564 _88565 P' a' b')). Qed.
Lemma lem3409668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409669 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1007 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1008 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (MK_COMB (@lem3409668) (@lem3409667 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409670 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1004 _88563 _88564 _88565 P a b c) = (term845 _88563 _88564 _88565 P a b c).
Proof. exact (eq_refl (term1004 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409671 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409672 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1009 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1010 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (MK_COMB (@lem3409671 _88500 _88501 _88502 x y z P a b c) (@lem3409670 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409673 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1011 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1012 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (fun_ext (fun c' : _88563 => @lem3409672 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409674 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409675 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1003 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1013 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (MK_COMB (@lem3409674 _88563) (@lem3409673 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409676 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : ((term1002 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1003 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')) = ((term998 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1013 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')).
Proof. exact (MK_COMB (@lem3409669 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') (@lem3409675 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409677 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term998 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1013 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (EQ_MP (@lem3409676 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') (@lem3409661 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409679 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409680 {_88565 : Type'} (P : Prop) (Q : _88565 -> Prop) : (term962 _88565 P Q) = (term963 _88565 P Q).
Proof. exact (@lem3409679 _88565 P Q). Qed.
Lemma lem3409681 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1014 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1015 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (@lem3409680 _88565 (term664 _88500 _88501 _88502 x y z P a b c) (term844 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409682 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1016 _88563 _88564 _88565 P a b c x) = (term843 _88563 _88564 _88565 x P a b c).
Proof. exact (eq_refl (term1016 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409683 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1017 _88563 _88564 _88565 P a b c) = (term844 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88565 => @lem3409682 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409684 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409685 {_88563 _88564 _88565 : Type'} (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1018 _88563 _88564 _88565 P a b c) = (term845 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409684 _88565) (@lem3409683 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409686 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409687 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1014 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1010 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (MK_COMB (@lem3409686 _88500 _88501 _88502 x y z P a b c) (@lem3409685 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409689 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1019 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1020 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (MK_COMB (@lem3409688) (@lem3409687 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409690 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1016 _88563 _88564 _88565 P a b c x) = (term843 _88563 _88564 _88565 x P a b c).
Proof. exact (eq_refl (term1016 _88563 _88564 _88565 P a b c x)). Qed.
Lemma lem3409691 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409692 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1021 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c' x') = (term1022 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (MK_COMB (@lem3409691 _88500 _88501 _88502 x y z P a b c) (@lem3409690 _88563 _88564 _88565 x' P' a' b' c')). Qed.
Lemma lem3409693 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1023 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1024 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (fun_ext (fun x' : _88565 => @lem3409692 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409694 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409695 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1015 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1025 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (MK_COMB (@lem3409694 _88565) (@lem3409693 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409696 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : ((term1014 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1015 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')) = ((term1010 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1025 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')).
Proof. exact (MK_COMB (@lem3409689 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') (@lem3409695 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409697 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1010 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1025 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (EQ_MP (@lem3409696 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') (@lem3409681 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409699 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409700 {_88564 : Type'} (P : Prop) (Q : _88564 -> Prop) : (term962 _88564 P Q) = (term963 _88564 P Q).
Proof. exact (@lem3409699 _88564 P Q). Qed.
Lemma lem3409701 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1026 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1027 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (@lem3409700 _88564 (term664 _88500 _88501 _88502 x y z P a b c) (term842 _88563 _88564 _88565 x' P' a' b' c')). Qed.
Lemma lem3409702 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1028 _88563 _88564 _88565 x P a b c y) = (term841 _88563 _88564 _88565 x y P a b c).
Proof. exact (eq_refl (term1028 _88563 _88564 _88565 x P a b c y)). Qed.
Lemma lem3409703 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1029 _88563 _88564 _88565 x P a b c) = (term842 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88564 => @lem3409702 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409704 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409705 {_88563 _88564 _88565 : Type'} (x : _88565) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1030 _88563 _88564 _88565 x P a b c) = (term843 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409704 _88564) (@lem3409703 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409706 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409707 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1026 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1022 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (MK_COMB (@lem3409706 _88500 _88501 _88502 x y z P a b c) (@lem3409705 _88563 _88564 _88565 x' P' a' b' c')). Qed.
Lemma lem3409708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409709 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1031 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1032 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (MK_COMB (@lem3409708) (@lem3409707 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409710 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1028 _88563 _88564 _88565 x P a b c y) = (term841 _88563 _88564 _88565 x y P a b c).
Proof. exact (eq_refl (term1028 _88563 _88564 _88565 x P a b c y)). Qed.
Lemma lem3409711 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409712 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1033 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c' y') = (term1034 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (MK_COMB (@lem3409711 _88500 _88501 _88502 x y z P a b c) (@lem3409710 _88563 _88564 _88565 x' y' P' a' b' c')). Qed.
Lemma lem3409713 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1035 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1036 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (fun_ext (fun y' : _88564 => @lem3409712 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409714 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409715 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1027 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1037 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (MK_COMB (@lem3409714 _88564) (@lem3409713 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409716 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : ((term1026 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1027 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')) = ((term1022 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1037 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')).
Proof. exact (MK_COMB (@lem3409709 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') (@lem3409715 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409717 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1022 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1037 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (EQ_MP (@lem3409716 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') (@lem3409701 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409719 {A : Type'} (P : Prop) (Q : A -> Prop) : (term962 A P Q) = (term963 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3409720 {_88563 : Type'} (P : Prop) (Q : _88563 -> Prop) : (term962 _88563 P Q) = (term963 _88563 P Q).
Proof. exact (@lem3409719 _88563 P Q). Qed.
Lemma lem3409721 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1038 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1039 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (@lem3409720 _88563 (term664 _88500 _88501 _88502 x y z P a b c) (term840 _88563 _88564 _88565 x' y' P' a' b' c')). Qed.
Lemma lem3409722 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1040 _88563 _88564 _88565 x y P a b c z) = (term838 _88563 _88564 _88565 x y z P a b c).
Proof. exact (eq_refl (term1040 _88563 _88564 _88565 x y P a b c z)). Qed.
Lemma lem3409723 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1041 _88563 _88564 _88565 x y P a b c) = (term840 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88563 => @lem3409722 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409724 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409725 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1042 _88563 _88564 _88565 x y P a b c) = (term841 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409724 _88563) (@lem3409723 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409726 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409727 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1038 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1034 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (MK_COMB (@lem3409726 _88500 _88501 _88502 x y z P a b c) (@lem3409725 _88563 _88564 _88565 x' y' P' a' b' c')). Qed.
Lemma lem3409728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3409729 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1043 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1044 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (MK_COMB (@lem3409728) (@lem3409727 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409730 {_88563 _88564 _88565 : Type'} (x : _88565) (y : _88564) (z : _88563) (P : type1517 _88563 _88564 _88565) (a : _88565) (b : _88564) (c : _88563) : (term1040 _88563 _88564 _88565 x y P a b c z) = (term838 _88563 _88564 _88565 x y z P a b c).
Proof. exact (eq_refl (term1040 _88563 _88564 _88565 x y P a b c z)). Qed.
Lemma lem3409731 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term956 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3409732 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1045 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c' z') = (term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c').
Proof. exact (MK_COMB (@lem3409731 _88500 _88501 _88502 x y z P a b c) (@lem3409730 _88563 _88564 _88565 x' y' z' P' a' b' c')). Qed.
Lemma lem3409733 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1047 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1048 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (fun_ext (fun z' : _88563 => @lem3409732 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c')). Qed.
Lemma lem3409734 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409735 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1039 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (MK_COMB (@lem3409734 _88563) (@lem3409733 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409736 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : ((term1038 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1039 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')) = ((term1034 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')).
Proof. exact (MK_COMB (@lem3409729 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') (@lem3409735 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409737 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1034 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') = (term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c').
Proof. exact (EQ_MP (@lem3409736 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') (@lem3409721 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409738 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1036 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1050 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (fun_ext (fun y' : _88564 => @lem3409737 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c')). Qed.
Lemma lem3409739 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409740 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1037 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1051 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (MK_COMB (@lem3409739 _88564) (@lem3409738 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409741 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1022 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') = (term1051 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c').
Proof. exact (TRANS (@lem3409717 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') (@lem3409740 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409742 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1024 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1052 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (fun_ext (fun x' : _88565 => @lem3409741 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c')). Qed.
Lemma lem3409743 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409744 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1025 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1053 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (MK_COMB (@lem3409743 _88565) (@lem3409742 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409745 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1010 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') = (term1053 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c').
Proof. exact (TRANS (@lem3409697 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') (@lem3409744 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409746 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1012 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1054 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (fun_ext (fun c' : _88563 => @lem3409745 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c')). Qed.
Lemma lem3409747 {_88563 : Type'} : (@ex _88563) = (@ex _88563).
Proof. exact (eq_refl (@ex _88563)). Qed.
Lemma lem3409748 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term1013 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1055 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (MK_COMB (@lem3409747 _88563) (@lem3409746 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409749 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) : (term998 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') = (term1055 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b').
Proof. exact (TRANS (@lem3409677 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') (@lem3409748 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409750 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term1000 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1056 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (fun_ext (fun b' : _88564 => @lem3409749 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b')). Qed.
Lemma lem3409751 {_88564 : Type'} : (@ex _88564) = (@ex _88564).
Proof. exact (eq_refl (@ex _88564)). Qed.
Lemma lem3409752 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term1001 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1057 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (MK_COMB (@lem3409751 _88564) (@lem3409750 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409753 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) : (term986 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') = (term1057 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a').
Proof. exact (TRANS (@lem3409657 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') (@lem3409752 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409754 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term988 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term1058 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (fun_ext (fun a' : _88565 => @lem3409753 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a')). Qed.
Lemma lem3409755 {_88565 : Type'} : (@ex _88565) = (@ex _88565).
Proof. exact (eq_refl (@ex _88565)). Qed.
Lemma lem3409756 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term989 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term1059 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (MK_COMB (@lem3409755 _88565) (@lem3409754 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409757 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) : (term974 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') = (term1059 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P').
Proof. exact (TRANS (@lem3409637 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') (@lem3409756 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409758 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term976 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term1060 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (fun_ext (fun P' : type1517 _88563 _88564 _88565 => @lem3409757 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P')). Qed.
Lemma lem3409759 {_88563 _88564 _88565 : Type'} : (@ex (_88565 -> _88564 -> _88563 -> Prop)) = (@ex (_88565 -> _88564 -> _88563 -> Prop)).
Proof. exact (eq_refl (@ex (_88565 -> _88564 -> _88563 -> Prop))). Qed.
Lemma lem3409760 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term977 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term1061 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (MK_COMB (@lem3409759 _88563 _88564 _88565) (@lem3409758 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409761 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term958 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) = (term1061 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c).
Proof. exact (TRANS (@lem3409617 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) (@lem3409760 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409762 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term960 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term1062 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409761 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c)). Qed.
Lemma lem3409763 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409764 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term961 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term1063 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (MK_COMB (@lem3409763 _88500) (@lem3409762 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409765 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term943 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) = (term1063 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c).
Proof. exact (TRANS (@lem3409597 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) (@lem3409764 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409766 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term945 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term1064 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409765 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c)). Qed.
Lemma lem3409767 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409768 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term946 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term1065 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (MK_COMB (@lem3409767 _88501) (@lem3409766 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409769 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term928 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) = (term1065 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c).
Proof. exact (TRANS (@lem3409571 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) (@lem3409768 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409770 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term930 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term1066 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409769 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c)). Qed.
Lemma lem3409771 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409772 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term931 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term1067 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (MK_COMB (@lem3409771 _88502) (@lem3409770 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409773 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term913 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) = (term1067 _88500 _88501 _88502 _88563 _88564 _88565 P a b c).
Proof. exact (TRANS (@lem3409545 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) (@lem3409772 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409774 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term915 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term1068 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (fun_ext (fun c : _88500 => @lem3409773 _88500 _88501 _88502 _88563 _88564 _88565 P a b c)). Qed.
Lemma lem3409775 {_88500 : Type'} : (@ex _88500) = (@ex _88500).
Proof. exact (eq_refl (@ex _88500)). Qed.
Lemma lem3409776 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term916 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term1069 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (MK_COMB (@lem3409775 _88500) (@lem3409774 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409777 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term898 _88500 _88501 _88502 _88563 _88564 _88565 P a b) = (term1069 _88500 _88501 _88502 _88563 _88564 _88565 P a b).
Proof. exact (TRANS (@lem3409519 _88500 _88501 _88502 _88563 _88564 _88565 P a b) (@lem3409776 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409778 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term900 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term1070 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (fun_ext (fun b : _88501 => @lem3409777 _88500 _88501 _88502 _88563 _88564 _88565 P a b)). Qed.
Lemma lem3409779 {_88501 : Type'} : (@ex _88501) = (@ex _88501).
Proof. exact (eq_refl (@ex _88501)). Qed.
Lemma lem3409780 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term901 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term1071 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (MK_COMB (@lem3409779 _88501) (@lem3409778 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409781 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) : (term883 _88500 _88501 _88502 _88563 _88564 _88565 P a) = (term1071 _88500 _88501 _88502 _88563 _88564 _88565 P a).
Proof. exact (TRANS (@lem3409493 _88500 _88501 _88502 _88563 _88564 _88565 P a) (@lem3409780 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409782 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term885 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term1072 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (fun_ext (fun a : _88502 => @lem3409781 _88500 _88501 _88502 _88563 _88564 _88565 P a)). Qed.
Lemma lem3409783 {_88502 : Type'} : (@ex _88502) = (@ex _88502).
Proof. exact (eq_refl (@ex _88502)). Qed.
Lemma lem3409784 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term886 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term1073 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (MK_COMB (@lem3409783 _88502) (@lem3409782 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409785 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) : (term868 _88500 _88501 _88502 _88563 _88564 _88565 P) = (term1073 _88500 _88501 _88502 _88563 _88564 _88565 P).
Proof. exact (TRANS (@lem3409467 _88500 _88501 _88502 _88563 _88564 _88565 P) (@lem3409784 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409786 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term870 _88500 _88501 _88502 _88563 _88564 _88565) = (term1074 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (fun_ext (fun P : type1517 _88500 _88501 _88502 => @lem3409785 _88500 _88501 _88502 _88563 _88564 _88565 P)). Qed.
Lemma lem3409787 {_88500 _88501 _88502 : Type'} : (@ex (_88502 -> _88501 -> _88500 -> Prop)) = (@ex (_88502 -> _88501 -> _88500 -> Prop)).
Proof. exact (eq_refl (@ex (_88502 -> _88501 -> _88500 -> Prop))). Qed.
Lemma lem3409788 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term871 _88500 _88501 _88502 _88563 _88564 _88565) = (term1075 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (MK_COMB (@lem3409787 _88500 _88501 _88502) (@lem3409786 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409789 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term854 _88500 _88501 _88502 _88563 _88564 _88565) = (term1075 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3409441 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409788 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409790 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term502 _88500 _88501 _88502 _88563 _88564 _88565) = (term1075 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3409415 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409789 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409791 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term324 _88500 _88501 _88502 _88563 _88564 _88565) = (term1075 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3408810 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409790 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409792 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : (term171 _88500 _88501 _88502 _88563 _88564 _88565) = (term1075 _88500 _88501 _88502 _88563 _88564 _88565).
Proof. exact (TRANS (@lem3406783 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3409791 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3409793 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : term1075 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (EQ_MP (@lem3409792 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3406530 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3409794 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (h1 : term1073 _88500 _88501 _88502 _88563 _88564 _88565 P) : term1073 _88500 _88501 _88502 _88563 _88564 _88565 P.
Proof. exact (h1). Qed.
Lemma lem3409795 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (h1 : term1071 _88500 _88501 _88502 _88563 _88564 _88565 P a) : term1071 _88500 _88501 _88502 _88563 _88564 _88565 P a.
Proof. exact (h1). Qed.
Lemma lem3409796 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (h1 : term1069 _88500 _88501 _88502 _88563 _88564 _88565 P a b) : term1069 _88500 _88501 _88502 _88563 _88564 _88565 P a b.
Proof. exact (h1). Qed.
Lemma lem3409797 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1067 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) : term1067 _88500 _88501 _88502 _88563 _88564 _88565 P a b c.
Proof. exact (h1). Qed.
Lemma lem3409798 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1065 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) : term1065 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c.
Proof. exact (h1). Qed.
Lemma lem3409799 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1063 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) : term1063 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c.
Proof. exact (h1). Qed.
Lemma lem3409800 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1061 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) : term1061 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c.
Proof. exact (h1). Qed.
Lemma lem3409801 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (h1 : term1059 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') : term1059 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P'.
Proof. exact (h1). Qed.
Lemma lem3409802 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (h1 : term1057 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') : term1057 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a'.
Proof. exact (h1). Qed.
Lemma lem3409803 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (h1 : term1055 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') : term1055 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b'.
Proof. exact (h1). Qed.
Lemma lem3409804 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1053 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') : term1053 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3409805 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1051 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') : term1051 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3409806 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') : term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3409807 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3409814 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (P' a' b' c') = (P' a' b' c').
Proof. exact (eq_refl (P' a' b' c')). Qed.
Lemma lem3409853 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) (z : _88563) : (term260 _88563 _88564 _88565 P' a' x b' y c' z) = (term260 _88563 _88564 _88565 P' a' x b' y c' z).
Proof. exact (eq_refl (term260 _88563 _88564 _88565 P' a' x b' y c' z)). Qed.
Lemma lem3409854 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) : (term267 _88563 _88564 _88565 P' a' x b' y c') = (term267 _88563 _88564 _88565 P' a' x b' y c').
Proof. exact (fun_ext (fun z : _88563 => @lem3409853 _88563 _88564 _88565 P' a' x b' y c' z)). Qed.
Lemma lem3409855 {_88563 : Type'} : (@all _88563) = (@all _88563).
Proof. exact (eq_refl (@all _88563)). Qed.
Lemma lem3409856 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) : (term268 _88563 _88564 _88565 P' a' x b' y c') = (term268 _88563 _88564 _88565 P' a' x b' y c').
Proof. exact (MK_COMB (@lem3409855 _88563) (@lem3409854 _88563 _88564 _88565 P' a' x b' y c')). Qed.
Lemma lem3409857 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (c' : _88563) : (term274 _88563 _88564 _88565 P' a' x b' c') = (term274 _88563 _88564 _88565 P' a' x b' c').
Proof. exact (fun_ext (fun y : _88564 => @lem3409856 _88563 _88564 _88565 P' a' x b' y c')). Qed.
Lemma lem3409858 {_88564 : Type'} : (@all _88564) = (@all _88564).
Proof. exact (eq_refl (@all _88564)). Qed.
Lemma lem3409859 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (c' : _88563) : (term275 _88563 _88564 _88565 P' a' x b' c') = (term275 _88563 _88564 _88565 P' a' x b' c').
Proof. exact (MK_COMB (@lem3409858 _88564) (@lem3409857 _88563 _88564 _88565 P' a' x b' c')). Qed.
Lemma lem3409860 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term281 _88563 _88564 _88565 P' a' b' c') = (term281 _88563 _88564 _88565 P' a' b' c').
Proof. exact (fun_ext (fun x : _88565 => @lem3409859 _88563 _88564 _88565 P' a' x b' c')). Qed.
Lemma lem3409861 {_88565 : Type'} : (@all _88565) = (@all _88565).
Proof. exact (eq_refl (@all _88565)). Qed.
Lemma lem3409862 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term282 _88563 _88564 _88565 P' a' b' c') = (term282 _88563 _88564 _88565 P' a' b' c').
Proof. exact (MK_COMB (@lem3409861 _88565) (@lem3409860 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409864 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term284 _88563 _88564 _88565 P' a' b' c') = (term284 _88563 _88564 _88565 P' a' b' c').
Proof. exact (MK_COMB (@lem3409863) (@lem3409862 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409865 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term286 _88563 _88564 _88565 P' a' b' c') = (term286 _88563 _88564 _88565 P' a' b' c').
Proof. exact (MK_COMB (@lem3409864 _88563 _88564 _88565 P' a' b' c') (@lem3409814 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409910 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term836 _88563 _88564 _88565 x' y' z' P' a' b' c') = (term836 _88563 _88564 _88565 x' y' z' P' a' b' c').
Proof. exact (eq_refl (term836 _88563 _88564 _88565 x' y' z' P' a' b' c')). Qed.
Lemma lem3409911 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term838 _88563 _88564 _88565 x' y' z' P' a' b' c') = (term838 _88563 _88564 _88565 x' y' z' P' a' b' c').
Proof. exact (MK_COMB (@lem3409910 _88563 _88564 _88565 x' y' z' P' a' b' c') (@lem3409865 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3409918 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (P a b c) = (P a b c).
Proof. exact (eq_refl (P a b c)). Qed.
Lemma lem3409957 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term185 _88500 _88501 _88502 P a x b y c z) = (term185 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term185 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3409958 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term194 _88500 _88501 _88502 P a x b y c) = (term194 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3409957 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3409959 {_88500 : Type'} : (@all _88500) = (@all _88500).
Proof. exact (eq_refl (@all _88500)). Qed.
Lemma lem3409960 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term195 _88500 _88501 _88502 P a x b y c) = (term195 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3409959 _88500) (@lem3409958 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3409961 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term201 _88500 _88501 _88502 P a x b c) = (term201 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3409960 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3409962 {_88501 : Type'} : (@all _88501) = (@all _88501).
Proof. exact (eq_refl (@all _88501)). Qed.
Lemma lem3409963 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term202 _88500 _88501 _88502 P a x b c) = (term202 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3409962 _88501) (@lem3409961 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3409964 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term208 _88500 _88501 _88502 P a b c) = (term208 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3409963 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3409965 {_88502 : Type'} : (@all _88502) = (@all _88502).
Proof. exact (eq_refl (@all _88502)). Qed.
Lemma lem3409966 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term209 _88500 _88501 _88502 P a b c) = (term209 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409965 _88502) (@lem3409964 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3409968 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term212 _88500 _88501 _88502 P a b c) = (term212 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409967) (@lem3409966 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3409969 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term214 _88500 _88501 _88502 P a b c) = (term214 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3409968 _88500 _88501 _88502 P a b c) (@lem3409918 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410014 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term662 _88500 _88501 _88502 x y z P a b c) = (term662 _88500 _88501 _88502 x y z P a b c).
Proof. exact (eq_refl (term662 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3410015 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term664 _88500 _88501 _88502 x y z P a b c) = (term664 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3410014 _88500 _88501 _88502 x y z P a b c) (@lem3409969 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3410017 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term956 _88500 _88501 _88502 x y z P a b c) = (term956 _88500 _88501 _88502 x y z P a b c).
Proof. exact (MK_COMB (@lem3410016) (@lem3410015 _88500 _88501 _88502 x y z P a b c)). Qed.
Lemma lem3410018 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') = (term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c').
Proof. exact (MK_COMB (@lem3410017 _88500 _88501 _88502 x y z P a b c) (@lem3409911 _88563 _88564 _88565 x' y' z' P' a' b' c')). Qed.
Lemma lem3410019 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c'.
Proof. exact (EQ_MP (@lem3410018 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') (@lem3409807 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410020 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term664 _88500 _88501 _88502 x y z P a b c) : term664 _88500 _88501 _88502 x y z P a b c.
Proof. exact (h1). Qed.
Lemma lem3410021 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term838 _88563 _88564 _88565 x' y' z' P' a' b' c') : term838 _88563 _88564 _88565 x' y' z' P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3410022 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term543 _88500 _88501 _88502 x y z P a b c.
Proof. exact (h1). Qed.
Lemma lem3410023 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term214 _88500 _88501 _88502 P a b c.
Proof. exact (h1). Qed.
Lemma lem3410025 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term65 _88500 _88501 _88502 P a x b y c z.
Proof. exact (proj1 (@lem3410022 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410026 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term63 _88500 _88501 _88502 a x b y c z.
Proof. exact (proj2 (@lem3410025 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410028 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term61 _88500 _88501 b y c z.
Proof. exact (proj2 (@lem3410026 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410033 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term209 _88500 _88501 _88502 P a b c.
Proof. exact (proj1 (@lem3410023 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410034 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term719 _88563 _88564 _88565 x' y' z' P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3410035 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term286 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (h1). Qed.
Lemma lem3410037 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term138 _88563 _88564 _88565 P' a' x' b' y' c' z'.
Proof. exact (proj1 (@lem3410034 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410038 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term137 _88563 _88564 _88565 a' x' b' y' c' z'.
Proof. exact (proj2 (@lem3410037 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410041 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term61 _88564 _88565 a' x' b' y'.
Proof. exact (proj1 (@lem3410038 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410045 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term282 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (proj1 (@lem3410035 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410085 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) (z : _88500) : (term185 _88500 _88501 _88502 P a x b y c z) = (term185 _88500 _88501 _88502 P a x b y c z).
Proof. exact (eq_refl (term185 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3410086 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term194 _88500 _88501 _88502 P a x b y c) = (term194 _88500 _88501 _88502 P a x b y c).
Proof. exact (fun_ext (fun z : _88500 => @lem3410085 _88500 _88501 _88502 P a x b y c z)). Qed.
Lemma lem3410087 {_88500 : Type'} : (@all _88500) = (@all _88500).
Proof. exact (eq_refl (@all _88500)). Qed.
Lemma lem3410088 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (y : _88501) (c : _88500) : (term195 _88500 _88501 _88502 P a x b y c) = (term195 _88500 _88501 _88502 P a x b y c).
Proof. exact (MK_COMB (@lem3410087 _88500) (@lem3410086 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3410089 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term201 _88500 _88501 _88502 P a x b c) = (term201 _88500 _88501 _88502 P a x b c).
Proof. exact (fun_ext (fun y : _88501 => @lem3410088 _88500 _88501 _88502 P a x b y c)). Qed.
Lemma lem3410090 {_88501 : Type'} : (@all _88501) = (@all _88501).
Proof. exact (eq_refl (@all _88501)). Qed.
Lemma lem3410091 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (x : _88502) (b : _88501) (c : _88500) : (term202 _88500 _88501 _88502 P a x b c) = (term202 _88500 _88501 _88502 P a x b c).
Proof. exact (MK_COMB (@lem3410090 _88501) (@lem3410089 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3410092 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term208 _88500 _88501 _88502 P a b c) = (term208 _88500 _88501 _88502 P a b c).
Proof. exact (fun_ext (fun x : _88502 => @lem3410091 _88500 _88501 _88502 P a x b c)). Qed.
Lemma lem3410093 {_88502 : Type'} : (@all _88502) = (@all _88502).
Proof. exact (eq_refl (@all _88502)). Qed.
Lemma lem3410095 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term209 _88500 _88501 _88502 P a b c) = (term209 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3410093 _88502) (@lem3410092 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410096 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term209 _88500 _88501 _88502 P a b c.
Proof. exact (EQ_MP (@lem3410095 _88500 _88501 _88502 P a b c) (@lem3410033 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410140 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) (z : _88563) : (term260 _88563 _88564 _88565 P' a' x b' y c' z) = (term260 _88563 _88564 _88565 P' a' x b' y c' z).
Proof. exact (eq_refl (term260 _88563 _88564 _88565 P' a' x b' y c' z)). Qed.
Lemma lem3410141 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) : (term267 _88563 _88564 _88565 P' a' x b' y c') = (term267 _88563 _88564 _88565 P' a' x b' y c').
Proof. exact (fun_ext (fun z : _88563 => @lem3410140 _88563 _88564 _88565 P' a' x b' y c' z)). Qed.
Lemma lem3410142 {_88563 : Type'} : (@all _88563) = (@all _88563).
Proof. exact (eq_refl (@all _88563)). Qed.
Lemma lem3410143 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (y : _88564) (c' : _88563) : (term268 _88563 _88564 _88565 P' a' x b' y c') = (term268 _88563 _88564 _88565 P' a' x b' y c').
Proof. exact (MK_COMB (@lem3410142 _88563) (@lem3410141 _88563 _88564 _88565 P' a' x b' y c')). Qed.
Lemma lem3410144 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (c' : _88563) : (term274 _88563 _88564 _88565 P' a' x b' c') = (term274 _88563 _88564 _88565 P' a' x b' c').
Proof. exact (fun_ext (fun y : _88564 => @lem3410143 _88563 _88564 _88565 P' a' x b' y c')). Qed.
Lemma lem3410145 {_88564 : Type'} : (@all _88564) = (@all _88564).
Proof. exact (eq_refl (@all _88564)). Qed.
Lemma lem3410146 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (x : _88565) (b' : _88564) (c' : _88563) : (term275 _88563 _88564 _88565 P' a' x b' c') = (term275 _88563 _88564 _88565 P' a' x b' c').
Proof. exact (MK_COMB (@lem3410145 _88564) (@lem3410144 _88563 _88564 _88565 P' a' x b' c')). Qed.
Lemma lem3410147 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term281 _88563 _88564 _88565 P' a' b' c') = (term281 _88563 _88564 _88565 P' a' b' c').
Proof. exact (fun_ext (fun x : _88565 => @lem3410146 _88563 _88564 _88565 P' a' x b' c')). Qed.
Lemma lem3410148 {_88565 : Type'} : (@all _88565) = (@all _88565).
Proof. exact (eq_refl (@all _88565)). Qed.
Lemma lem3410150 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term282 _88563 _88564 _88565 P' a' b' c') = (term282 _88563 _88564 _88565 P' a' b' c').
Proof. exact (MK_COMB (@lem3410148 _88565) (@lem3410147 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3410151 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term282 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (EQ_MP (@lem3410150 _88563 _88564 _88565 P' a' b' c') (@lem3410045 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410156 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1076 _88500 _88501 _88502 P a b c _35934.
Proof. exact (@lem3410096 _88500 _88501 _88502 P a b c h1 _35934). Qed.
Lemma lem3410157 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (c : _88500) : (term1076 _88500 _88501 _88502 P a b c _35934) = (term202 _88500 _88501 _88502 P a _35934 b c).
Proof. exact (eq_refl (term1076 _88500 _88501 _88502 P a b c _35934)). Qed.
Lemma lem3410158 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term202 _88500 _88501 _88502 P a _35934 b c.
Proof. exact (EQ_MP (@lem3410157 _88500 _88501 _88502 P a _35934 b c) (@lem3410156 _88500 _88501 _88502 _35934 P a b c h1)). Qed.
Lemma lem3410159 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1077 _88500 _88501 _88502 P a _35934 b c _35935.
Proof. exact (@lem3410158 _88500 _88501 _88502 _35934 P a b c h1 _35935). Qed.
Lemma lem3410160 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) : (term1077 _88500 _88501 _88502 P a _35934 b c _35935) = (term195 _88500 _88501 _88502 P a _35934 b _35935 c).
Proof. exact (eq_refl (term1077 _88500 _88501 _88502 P a _35934 b c _35935)). Qed.
Lemma lem3410161 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term195 _88500 _88501 _88502 P a _35934 b _35935 c.
Proof. exact (EQ_MP (@lem3410160 _88500 _88501 _88502 P a _35934 b _35935 c) (@lem3410159 _88500 _88501 _88502 _35934 _35935 P a b c h1)). Qed.
Lemma lem3410162 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (_35936 : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1078 _88500 _88501 _88502 P a _35934 b _35935 c _35936.
Proof. exact (@lem3410161 _88500 _88501 _88502 _35934 _35935 P a b c h1 _35936). Qed.
Lemma lem3410163 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term1078 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term185 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (eq_refl (term1078 _88500 _88501 _88502 P a _35934 b _35935 c _35936)). Qed.
Lemma lem3410165 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1079 _88563 _88564 _88565 P' a' b' c' _35937.
Proof. exact (@lem3410151 _88563 _88564 _88565 P' a' b' c' h1 _35937). Qed.
Lemma lem3410166 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (c' : _88563) : (term1079 _88563 _88564 _88565 P' a' b' c' _35937) = (term275 _88563 _88564 _88565 P' a' _35937 b' c').
Proof. exact (eq_refl (term1079 _88563 _88564 _88565 P' a' b' c' _35937)). Qed.
Lemma lem3410167 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term275 _88563 _88564 _88565 P' a' _35937 b' c'.
Proof. exact (EQ_MP (@lem3410166 _88563 _88564 _88565 P' a' _35937 b' c') (@lem3410165 _88563 _88564 _88565 _35937 P' a' b' c' h1)). Qed.
Lemma lem3410168 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1080 _88563 _88564 _88565 P' a' _35937 b' c' _35938.
Proof. exact (@lem3410167 _88563 _88564 _88565 _35937 P' a' b' c' h1 _35938). Qed.
Lemma lem3410169 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) : (term1080 _88563 _88564 _88565 P' a' _35937 b' c' _35938) = (term268 _88563 _88564 _88565 P' a' _35937 b' _35938 c').
Proof. exact (eq_refl (term1080 _88563 _88564 _88565 P' a' _35937 b' c' _35938)). Qed.
Lemma lem3410170 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term268 _88563 _88564 _88565 P' a' _35937 b' _35938 c'.
Proof. exact (EQ_MP (@lem3410169 _88563 _88564 _88565 P' a' _35937 b' _35938 c') (@lem3410168 _88563 _88564 _88565 _35937 _35938 P' a' b' c' h1)). Qed.
Lemma lem3410171 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1081 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939.
Proof. exact (@lem3410170 _88563 _88564 _88565 _35937 _35938 P' a' b' c' h1 _35939). Qed.
Lemma lem3410172 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term1081 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term260 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (eq_refl (term1081 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410173 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term260 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939.
Proof. exact (EQ_MP (@lem3410172 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) (@lem3410171 _88563 _88564 _88565 _35937 _35938 _35939 P' a' b' c' h1)). Qed.
Lemma lem3410175 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term210 _88500 _88501 _88502 P a b c.
Proof. exact (proj2 (@lem3410022 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410183 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : c = z.
Proof. exact (proj2 (@lem3410028 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410197 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (_35936 : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term185 _88500 _88501 _88502 P a _35934 b _35935 c _35936.
Proof. exact (EQ_MP (@lem3410163 _88500 _88501 _88502 P a _35934 b _35935 c _35936) (@lem3410162 _88500 _88501 _88502 _35934 _35935 _35936 P a b c h1)). Qed.
Lemma lem3410201 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term210 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (proj2 (@lem3410034 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410209 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : b' = y'.
Proof. exact (proj2 (@lem3410041 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410220 {_88563 _88564 _88565 : Type'} (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term257 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939) = (term181 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939).
Proof. exact (@lem3405766 (term253 _88565 a' _35937) (term253 _88564 b' _35938) (term253 _88563 c' _35939)). Qed.
Lemma lem3410221 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) : (term183 _88563 _88564 _88565 P' _35937 _35938 _35939) = (term183 _88563 _88564 _88565 P' _35937 _35938 _35939).
Proof. exact (eq_refl (term183 _88563 _88564 _88565 P' _35937 _35938 _35939)). Qed.
Lemma lem3410224 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term260 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term185 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (MK_COMB (@lem3410221 _88563 _88564 _88565 P' _35937 _35938 _35939) (@lem3410220 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410225 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term185 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939.
Proof. exact (EQ_MP (@lem3410224 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) (@lem3410173 _88563 _88564 _88565 _35937 _35938 _35939 P' a' b' c' h1)). Qed.
Lemma lem3410242 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) : (term1082 _88500 _88501 _88502 P a b) = (term1082 _88500 _88501 _88502 P a b).
Proof. exact (eq_refl (term1082 _88500 _88501 _88502 P a b)). Qed.
Lemma lem3410243 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term1083 _88500 _88501 _88502 P a b c) = (term1083 _88500 _88501 _88502 P a b z).
Proof. exact (MK_COMB (@lem3410242 _88500 _88501 _88502 P a b) (@lem3410183 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410244 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : (term1083 _88500 _88501 _88502 P a b z) = (term210 _88500 _88501 _88502 P a b z).
Proof. exact (eq_refl (term1083 _88500 _88501 _88502 P a b z)). Qed.
Lemma lem3410245 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term1084 _88500 _88501 _88502 P a b c) = (term1084 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term1084 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410246 {_88500 _88501 _88502 : Type'} (c : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : ((term1083 _88500 _88501 _88502 P a b c) = (term1083 _88500 _88501 _88502 P a b z)) = ((term1083 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b z)).
Proof. exact (MK_COMB (@lem3410245 _88500 _88501 _88502 P a b c) (@lem3410244 _88500 _88501 _88502 P a b z)). Qed.
Lemma lem3410247 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term1083 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b c).
Proof. exact (eq_refl (term1083 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410249 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term1084 _88500 _88501 _88502 P a b c) = (term1085 _88500 _88501 _88502 P a b c).
Proof. exact (MK_COMB (@lem3410248) (@lem3410247 _88500 _88501 _88502 P a b c)). Qed.
Lemma lem3410250 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : (term210 _88500 _88501 _88502 P a b z) = (term210 _88500 _88501 _88502 P a b z).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a b z)). Qed.
Lemma lem3410251 {_88500 _88501 _88502 : Type'} (c : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : ((term1083 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b z)) = ((term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b z)).
Proof. exact (MK_COMB (@lem3410249 _88500 _88501 _88502 P a b c) (@lem3410250 _88500 _88501 _88502 P a b z)). Qed.
Lemma lem3410252 {_88500 _88501 _88502 : Type'} (c : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : ((term1083 _88500 _88501 _88502 P a b c) = (term1083 _88500 _88501 _88502 P a b z)) = ((term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b z)).
Proof. exact (TRANS (@lem3410246 _88500 _88501 _88502 c P a b z) (@lem3410251 _88500 _88501 _88502 c P a b z)). Qed.
Lemma lem3410253 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term210 _88500 _88501 _88502 P a b c) = (term210 _88500 _88501 _88502 P a b z).
Proof. exact (EQ_MP (@lem3410252 _88500 _88501 _88502 c P a b z) (@lem3410243 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410254 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term210 _88500 _88501 _88502 P a b z.
Proof. exact (EQ_MP (@lem3410253 _88500 _88501 _88502 x y z P a b c h1) (@lem3410175 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410296 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : b = y.
Proof. exact (proj1 (@lem3410028 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410311 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (z : _88500) : (term1086 _88500 _88501 _88502 P a z) = (term1086 _88500 _88501 _88502 P a z).
Proof. exact (eq_refl (term1086 _88500 _88501 _88502 P a z)). Qed.
Lemma lem3410312 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term1087 _88500 _88501 _88502 P a z b) = (term1087 _88500 _88501 _88502 P a z y).
Proof. exact (MK_COMB (@lem3410311 _88500 _88501 _88502 P a z) (@lem3410296 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410313 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : (term1087 _88500 _88501 _88502 P a z y) = (term210 _88500 _88501 _88502 P a y z).
Proof. exact (eq_refl (term1087 _88500 _88501 _88502 P a z y)). Qed.
Lemma lem3410314 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (z : _88500) (b : _88501) : (term1088 _88500 _88501 _88502 P a z b) = (term1088 _88500 _88501 _88502 P a z b).
Proof. exact (eq_refl (term1088 _88500 _88501 _88502 P a z b)). Qed.
Lemma lem3410315 {_88500 _88501 _88502 : Type'} (b : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : ((term1087 _88500 _88501 _88502 P a z b) = (term1087 _88500 _88501 _88502 P a z y)) = ((term1087 _88500 _88501 _88502 P a z b) = (term210 _88500 _88501 _88502 P a y z)).
Proof. exact (MK_COMB (@lem3410314 _88500 _88501 _88502 P a z b) (@lem3410313 _88500 _88501 _88502 P a y z)). Qed.
Lemma lem3410316 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : (term1087 _88500 _88501 _88502 P a z b) = (term210 _88500 _88501 _88502 P a b z).
Proof. exact (eq_refl (term1087 _88500 _88501 _88502 P a z b)). Qed.
Lemma lem3410317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410318 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (z : _88500) : (term1088 _88500 _88501 _88502 P a z b) = (term1085 _88500 _88501 _88502 P a b z).
Proof. exact (MK_COMB (@lem3410317) (@lem3410316 _88500 _88501 _88502 P a b z)). Qed.
Lemma lem3410319 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : (term210 _88500 _88501 _88502 P a y z) = (term210 _88500 _88501 _88502 P a y z).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P a y z)). Qed.
Lemma lem3410320 {_88500 _88501 _88502 : Type'} (b : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : ((term1087 _88500 _88501 _88502 P a z b) = (term210 _88500 _88501 _88502 P a y z)) = ((term210 _88500 _88501 _88502 P a b z) = (term210 _88500 _88501 _88502 P a y z)).
Proof. exact (MK_COMB (@lem3410318 _88500 _88501 _88502 P a b z) (@lem3410319 _88500 _88501 _88502 P a y z)). Qed.
Lemma lem3410321 {_88500 _88501 _88502 : Type'} (b : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : ((term1087 _88500 _88501 _88502 P a z b) = (term1087 _88500 _88501 _88502 P a z y)) = ((term210 _88500 _88501 _88502 P a b z) = (term210 _88500 _88501 _88502 P a y z)).
Proof. exact (TRANS (@lem3410315 _88500 _88501 _88502 b P a y z) (@lem3410320 _88500 _88501 _88502 b P a y z)). Qed.
Lemma lem3410322 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term210 _88500 _88501 _88502 P a b z) = (term210 _88500 _88501 _88502 P a y z).
Proof. exact (EQ_MP (@lem3410321 _88500 _88501 _88502 b P a y z) (@lem3410312 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410323 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term210 _88500 _88501 _88502 P a y z.
Proof. exact (EQ_MP (@lem3410322 _88500 _88501 _88502 x y z P a b c h1) (@lem3410254 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410351 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : a = x.
Proof. exact (proj1 (@lem3410026 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410366 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (y : _88501) (z : _88500) : (term1089 _88500 _88501 _88502 P y z) = (term1089 _88500 _88501 _88502 P y z).
Proof. exact (eq_refl (term1089 _88500 _88501 _88502 P y z)). Qed.
Lemma lem3410367 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term1090 _88500 _88501 _88502 P y z a) = (term1090 _88500 _88501 _88502 P y z x).
Proof. exact (MK_COMB (@lem3410366 _88500 _88501 _88502 P y z) (@lem3410351 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410368 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term1090 _88500 _88501 _88502 P y z x) = (term210 _88500 _88501 _88502 P x y z).
Proof. exact (eq_refl (term1090 _88500 _88501 _88502 P y z x)). Qed.
Lemma lem3410369 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (y : _88501) (z : _88500) (a : _88502) : (term1091 _88500 _88501 _88502 P y z a) = (term1091 _88500 _88501 _88502 P y z a).
Proof. exact (eq_refl (term1091 _88500 _88501 _88502 P y z a)). Qed.
Lemma lem3410370 {_88500 _88501 _88502 : Type'} (a : _88502) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : ((term1090 _88500 _88501 _88502 P y z a) = (term1090 _88500 _88501 _88502 P y z x)) = ((term1090 _88500 _88501 _88502 P y z a) = (term210 _88500 _88501 _88502 P x y z)).
Proof. exact (MK_COMB (@lem3410369 _88500 _88501 _88502 P y z a) (@lem3410368 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3410371 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : (term1090 _88500 _88501 _88502 P y z a) = (term210 _88500 _88501 _88502 P a y z).
Proof. exact (eq_refl (term1090 _88500 _88501 _88502 P y z a)). Qed.
Lemma lem3410372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410373 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (y : _88501) (z : _88500) : (term1091 _88500 _88501 _88502 P y z a) = (term1085 _88500 _88501 _88502 P a y z).
Proof. exact (MK_COMB (@lem3410372) (@lem3410371 _88500 _88501 _88502 P a y z)). Qed.
Lemma lem3410374 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term210 _88500 _88501 _88502 P x y z) = (term210 _88500 _88501 _88502 P x y z).
Proof. exact (eq_refl (term210 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3410375 {_88500 _88501 _88502 : Type'} (a : _88502) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : ((term1090 _88500 _88501 _88502 P y z a) = (term210 _88500 _88501 _88502 P x y z)) = ((term210 _88500 _88501 _88502 P a y z) = (term210 _88500 _88501 _88502 P x y z)).
Proof. exact (MK_COMB (@lem3410373 _88500 _88501 _88502 P a y z) (@lem3410374 _88500 _88501 _88502 P x y z)). Qed.
Lemma lem3410376 {_88500 _88501 _88502 : Type'} (a : _88502) (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : ((term1090 _88500 _88501 _88502 P y z a) = (term1090 _88500 _88501 _88502 P y z x)) = ((term210 _88500 _88501 _88502 P a y z) = (term210 _88500 _88501 _88502 P x y z)).
Proof. exact (TRANS (@lem3410370 _88500 _88501 _88502 a P x y z) (@lem3410375 _88500 _88501 _88502 a P x y z)). Qed.
Lemma lem3410377 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : (term210 _88500 _88501 _88502 P a y z) = (term210 _88500 _88501 _88502 P x y z).
Proof. exact (EQ_MP (@lem3410376 _88500 _88501 _88502 a P x y z) (@lem3410367 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410378 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term210 _88500 _88501 _88502 P x y z.
Proof. exact (EQ_MP (@lem3410377 _88500 _88501 _88502 x y z P a b c h1) (@lem3410323 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410407 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (c' : _88563) : (term1086 _88563 _88564 _88565 P' a' c') = (term1086 _88563 _88564 _88565 P' a' c').
Proof. exact (eq_refl (term1086 _88563 _88564 _88565 P' a' c')). Qed.
Lemma lem3410408 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term1087 _88563 _88564 _88565 P' a' c' b') = (term1087 _88563 _88564 _88565 P' a' c' y').
Proof. exact (MK_COMB (@lem3410407 _88563 _88564 _88565 P' a' c') (@lem3410209 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410409 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : (term1087 _88563 _88564 _88565 P' a' c' y') = (term210 _88563 _88564 _88565 P' a' y' c').
Proof. exact (eq_refl (term1087 _88563 _88564 _88565 P' a' c' y')). Qed.
Lemma lem3410410 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (c' : _88563) (b' : _88564) : (term1088 _88563 _88564 _88565 P' a' c' b') = (term1088 _88563 _88564 _88565 P' a' c' b').
Proof. exact (eq_refl (term1088 _88563 _88564 _88565 P' a' c' b')). Qed.
Lemma lem3410411 {_88563 _88564 _88565 : Type'} (b' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : ((term1087 _88563 _88564 _88565 P' a' c' b') = (term1087 _88563 _88564 _88565 P' a' c' y')) = ((term1087 _88563 _88564 _88565 P' a' c' b') = (term210 _88563 _88564 _88565 P' a' y' c')).
Proof. exact (MK_COMB (@lem3410410 _88563 _88564 _88565 P' a' c' b') (@lem3410409 _88563 _88564 _88565 P' a' y' c')). Qed.
Lemma lem3410412 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1087 _88563 _88564 _88565 P' a' c' b') = (term210 _88563 _88564 _88565 P' a' b' c').
Proof. exact (eq_refl (term1087 _88563 _88564 _88565 P' a' c' b')). Qed.
Lemma lem3410413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410414 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1088 _88563 _88564 _88565 P' a' c' b') = (term1085 _88563 _88564 _88565 P' a' b' c').
Proof. exact (MK_COMB (@lem3410413) (@lem3410412 _88563 _88564 _88565 P' a' b' c')). Qed.
Lemma lem3410415 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : (term210 _88563 _88564 _88565 P' a' y' c') = (term210 _88563 _88564 _88565 P' a' y' c').
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P' a' y' c')). Qed.
Lemma lem3410416 {_88563 _88564 _88565 : Type'} (b' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : ((term1087 _88563 _88564 _88565 P' a' c' b') = (term210 _88563 _88564 _88565 P' a' y' c')) = ((term210 _88563 _88564 _88565 P' a' b' c') = (term210 _88563 _88564 _88565 P' a' y' c')).
Proof. exact (MK_COMB (@lem3410414 _88563 _88564 _88565 P' a' b' c') (@lem3410415 _88563 _88564 _88565 P' a' y' c')). Qed.
Lemma lem3410417 {_88563 _88564 _88565 : Type'} (b' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : ((term1087 _88563 _88564 _88565 P' a' c' b') = (term1087 _88563 _88564 _88565 P' a' c' y')) = ((term210 _88563 _88564 _88565 P' a' b' c') = (term210 _88563 _88564 _88565 P' a' y' c')).
Proof. exact (TRANS (@lem3410411 _88563 _88564 _88565 b' P' a' y' c') (@lem3410416 _88563 _88564 _88565 b' P' a' y' c')). Qed.
Lemma lem3410418 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term210 _88563 _88564 _88565 P' a' b' c') = (term210 _88563 _88564 _88565 P' a' y' c').
Proof. exact (EQ_MP (@lem3410417 _88563 _88564 _88565 b' P' a' y' c') (@lem3410408 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410419 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term210 _88563 _88564 _88565 P' a' y' c'.
Proof. exact (EQ_MP (@lem3410418 _88563 _88564 _88565 x' y' z' P' a' b' c' h1) (@lem3410201 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410461 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : a' = x'.
Proof. exact (proj1 (@lem3410041 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410476 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (y' : _88564) (c' : _88563) : (term1089 _88563 _88564 _88565 P' y' c') = (term1089 _88563 _88564 _88565 P' y' c').
Proof. exact (eq_refl (term1089 _88563 _88564 _88565 P' y' c')). Qed.
Lemma lem3410477 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term1090 _88563 _88564 _88565 P' y' c' a') = (term1090 _88563 _88564 _88565 P' y' c' x').
Proof. exact (MK_COMB (@lem3410476 _88563 _88564 _88565 P' y' c') (@lem3410461 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410478 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : (term1090 _88563 _88564 _88565 P' y' c' x') = (term210 _88563 _88564 _88565 P' x' y' c').
Proof. exact (eq_refl (term1090 _88563 _88564 _88565 P' y' c' x')). Qed.
Lemma lem3410479 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (y' : _88564) (c' : _88563) (a' : _88565) : (term1091 _88563 _88564 _88565 P' y' c' a') = (term1091 _88563 _88564 _88565 P' y' c' a').
Proof. exact (eq_refl (term1091 _88563 _88564 _88565 P' y' c' a')). Qed.
Lemma lem3410480 {_88563 _88564 _88565 : Type'} (a' : _88565) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : ((term1090 _88563 _88564 _88565 P' y' c' a') = (term1090 _88563 _88564 _88565 P' y' c' x')) = ((term1090 _88563 _88564 _88565 P' y' c' a') = (term210 _88563 _88564 _88565 P' x' y' c')).
Proof. exact (MK_COMB (@lem3410479 _88563 _88564 _88565 P' y' c' a') (@lem3410478 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410481 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : (term1090 _88563 _88564 _88565 P' y' c' a') = (term210 _88563 _88564 _88565 P' a' y' c').
Proof. exact (eq_refl (term1090 _88563 _88564 _88565 P' y' c' a')). Qed.
Lemma lem3410482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410483 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (y' : _88564) (c' : _88563) : (term1091 _88563 _88564 _88565 P' y' c' a') = (term1085 _88563 _88564 _88565 P' a' y' c').
Proof. exact (MK_COMB (@lem3410482) (@lem3410481 _88563 _88564 _88565 P' a' y' c')). Qed.
Lemma lem3410484 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : (term210 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' c').
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410485 {_88563 _88564 _88565 : Type'} (a' : _88565) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : ((term1090 _88563 _88564 _88565 P' y' c' a') = (term210 _88563 _88564 _88565 P' x' y' c')) = ((term210 _88563 _88564 _88565 P' a' y' c') = (term210 _88563 _88564 _88565 P' x' y' c')).
Proof. exact (MK_COMB (@lem3410483 _88563 _88564 _88565 P' a' y' c') (@lem3410484 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410486 {_88563 _88564 _88565 : Type'} (a' : _88565) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : ((term1090 _88563 _88564 _88565 P' y' c' a') = (term1090 _88563 _88564 _88565 P' y' c' x')) = ((term210 _88563 _88564 _88565 P' a' y' c') = (term210 _88563 _88564 _88565 P' x' y' c')).
Proof. exact (TRANS (@lem3410480 _88563 _88564 _88565 a' P' x' y' c') (@lem3410485 _88563 _88564 _88565 a' P' x' y' c')). Qed.
Lemma lem3410487 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term210 _88563 _88564 _88565 P' a' y' c') = (term210 _88563 _88564 _88565 P' x' y' c').
Proof. exact (EQ_MP (@lem3410486 _88563 _88564 _88565 a' P' x' y' c') (@lem3410477 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410488 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term210 _88563 _88564 _88565 P' x' y' c'.
Proof. exact (EQ_MP (@lem3410487 _88563 _88564 _88565 x' y' z' P' a' b' c' h1) (@lem3410419 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410516 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : c' = z'.
Proof. exact (proj2 (@lem3410038 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410531 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) : (term1082 _88563 _88564 _88565 P' x' y') = (term1082 _88563 _88564 _88565 P' x' y').
Proof. exact (eq_refl (term1082 _88563 _88564 _88565 P' x' y')). Qed.
Lemma lem3410532 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term1083 _88563 _88564 _88565 P' x' y' c') = (term1083 _88563 _88564 _88565 P' x' y' z').
Proof. exact (MK_COMB (@lem3410531 _88563 _88564 _88565 P' x' y') (@lem3410516 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410533 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : (term1083 _88563 _88564 _88565 P' x' y' z') = (term210 _88563 _88564 _88565 P' x' y' z').
Proof. exact (eq_refl (term1083 _88563 _88564 _88565 P' x' y' z')). Qed.
Lemma lem3410534 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : (term1084 _88563 _88564 _88565 P' x' y' c') = (term1084 _88563 _88564 _88565 P' x' y' c').
Proof. exact (eq_refl (term1084 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410535 {_88563 _88564 _88565 : Type'} (c' : _88563) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : ((term1083 _88563 _88564 _88565 P' x' y' c') = (term1083 _88563 _88564 _88565 P' x' y' z')) = ((term1083 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' z')).
Proof. exact (MK_COMB (@lem3410534 _88563 _88564 _88565 P' x' y' c') (@lem3410533 _88563 _88564 _88565 P' x' y' z')). Qed.
Lemma lem3410536 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : (term1083 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' c').
Proof. exact (eq_refl (term1083 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3410538 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (c' : _88563) : (term1084 _88563 _88564 _88565 P' x' y' c') = (term1085 _88563 _88564 _88565 P' x' y' c').
Proof. exact (MK_COMB (@lem3410537) (@lem3410536 _88563 _88564 _88565 P' x' y' c')). Qed.
Lemma lem3410539 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : (term210 _88563 _88564 _88565 P' x' y' z') = (term210 _88563 _88564 _88565 P' x' y' z').
Proof. exact (eq_refl (term210 _88563 _88564 _88565 P' x' y' z')). Qed.
Lemma lem3410540 {_88563 _88564 _88565 : Type'} (c' : _88563) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : ((term1083 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' z')) = ((term210 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' z')).
Proof. exact (MK_COMB (@lem3410538 _88563 _88564 _88565 P' x' y' c') (@lem3410539 _88563 _88564 _88565 P' x' y' z')). Qed.
Lemma lem3410541 {_88563 _88564 _88565 : Type'} (c' : _88563) (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : ((term1083 _88563 _88564 _88565 P' x' y' c') = (term1083 _88563 _88564 _88565 P' x' y' z')) = ((term210 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' z')).
Proof. exact (TRANS (@lem3410535 _88563 _88564 _88565 c' P' x' y' z') (@lem3410540 _88563 _88564 _88565 c' P' x' y' z')). Qed.
Lemma lem3410542 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : (term210 _88563 _88564 _88565 P' x' y' c') = (term210 _88563 _88564 _88565 P' x' y' z').
Proof. exact (EQ_MP (@lem3410541 _88563 _88564 _88565 c' P' x' y' z') (@lem3410532 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410543 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term210 _88563 _88564 _88565 P' x' y' z'.
Proof. exact (EQ_MP (@lem3410542 _88563 _88564 _88565 x' y' z' P' a' b' c' h1) (@lem3410488 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410559 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : P x y z.
Proof. exact (proj1 (@lem3410025 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410560 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term1092 _88500 _88501 _88502 P x y z.
Proof. exact (fun h0 : term210 _88500 _88501 _88502 P x y z => @lem3410559 _88500 _88501 _88502 x y z P a b c h1). Qed.
Lemma lem3410562 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410563 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term1092 _88500 _88501 _88502 P x y z) = (P x y z).
Proof. exact (@lem3410562 (P x y z)). Qed.
Lemma lem3410564 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : P x y z.
Proof. exact (EQ_MP (@lem3410563 _88500 _88501 _88502 P x y z) (@lem3410560 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3410569 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (x : _88502) (y : _88501) (z : _88500) : (term210 _88500 _88501 _88502 P x y z) = (term1094 _88500 _88501 _88502 P x y z).
Proof. exact (@lem3410567 (P x y z)). Qed.
Lemma lem3410572 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term1094 _88500 _88501 _88502 P x y z.
Proof. exact (EQ_MP (@lem3410569 _88500 _88501 _88502 P x y z) (@lem3410378 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410575 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : False.
Proof. exact (@lem3410572 _88500 _88501 _88502 x y z P a b c h1 (@lem3410564 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410576 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : term1095.
Proof. exact (fun h0 : ~ False => @lem3410575 _88500 _88501 _88502 x y z P a b c h1). Qed.
Lemma lem3410578 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410579 : term1095 = False.
Proof. exact (@lem3410578 False). Qed.
Lemma lem3410614 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : P a b c.
Proof. exact (proj2 (@lem3410023 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410615 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1092 _88500 _88501 _88502 P a b c.
Proof. exact (fun h0 : term210 _88500 _88501 _88502 P a b c => @lem3410614 _88500 _88501 _88502 P a b c h1). Qed.
Lemma lem3410617 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410618 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) : (term1092 _88500 _88501 _88502 P a b c) = (P a b c).
Proof. exact (@lem3410617 (P a b c)). Qed.
Lemma lem3410619 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : P a b c.
Proof. exact (EQ_MP (@lem3410618 _88500 _88501 _88502 P a b c) (@lem3410615 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410621 {_88502 : Type'} (x : _88502) : x = x.
Proof. exact (@lem21386 _88502 x). Qed.
Lemma lem3410622 {_88502 : Type'} (x : _88502) : x = x.
Proof. exact (@lem3410621 _88502 x). Qed.
Lemma lem3410623 {_88502 : Type'} (a : _88502) : a = a.
Proof. exact (@lem3410622 _88502 a). Qed.
Lemma lem3410624 {_88502 : Type'} (a : _88502) : term1096 _88502 a.
Proof. exact (fun h0 : term1097 _88502 a => @lem3410623 _88502 a). Qed.
Lemma lem3410626 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410627 {_88502 : Type'} (a : _88502) : (term1096 _88502 a) = (a = a).
Proof. exact (@lem3410626 (a = a)). Qed.
Lemma lem3410628 {_88502 : Type'} (a : _88502) : a = a.
Proof. exact (EQ_MP (@lem3410627 _88502 a) (@lem3410624 _88502 a)). Qed.
Lemma lem3410630 {_88501 : Type'} (x : _88501) : x = x.
Proof. exact (@lem21386 _88501 x). Qed.
Lemma lem3410631 {_88501 : Type'} (x : _88501) : x = x.
Proof. exact (@lem3410630 _88501 x). Qed.
Lemma lem3410632 {_88501 : Type'} (b : _88501) : b = b.
Proof. exact (@lem3410631 _88501 b). Qed.
Lemma lem3410633 {_88501 : Type'} (b : _88501) : term1096 _88501 b.
Proof. exact (fun h0 : term1097 _88501 b => @lem3410632 _88501 b). Qed.
Lemma lem3410635 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410636 {_88501 : Type'} (b : _88501) : (term1096 _88501 b) = (b = b).
Proof. exact (@lem3410635 (b = b)). Qed.
Lemma lem3410637 {_88501 : Type'} (b : _88501) : b = b.
Proof. exact (EQ_MP (@lem3410636 _88501 b) (@lem3410633 _88501 b)). Qed.
Lemma lem3410639 {_88500 : Type'} (x : _88500) : x = x.
Proof. exact (@lem21386 _88500 x). Qed.
Lemma lem3410640 {_88500 : Type'} (x : _88500) : x = x.
Proof. exact (@lem3410639 _88500 x). Qed.
Lemma lem3410641 {_88500 : Type'} (c : _88500) : c = c.
Proof. exact (@lem3410640 _88500 c). Qed.
Lemma lem3410642 {_88500 : Type'} (c : _88500) : term1096 _88500 c.
Proof. exact (fun h0 : term1097 _88500 c => @lem3410641 _88500 c). Qed.
Lemma lem3410644 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410645 {_88500 : Type'} (c : _88500) : (term1096 _88500 c) = (c = c).
Proof. exact (@lem3410644 (c = c)). Qed.
Lemma lem3410646 {_88500 : Type'} (c : _88500) : c = c.
Proof. exact (EQ_MP (@lem3410645 _88500 c) (@lem3410642 _88500 c)). Qed.
Lemma lem3410648 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410649 {_88500 _88501 : Type'} (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term178 _88500 _88501 b _35935 c _35936) = (term177 _88500 _88501 b _35935 c _35936).
Proof. exact (@lem3410648 (b = _35935) (c = _35936)). Qed.
Lemma lem3410650 {_88502 : Type'} (a : _88502) (_35934 : _88502) : (term179 _88502 a _35934) = (term179 _88502 a _35934).
Proof. exact (eq_refl (term179 _88502 a _35934)). Qed.
Lemma lem3410651 {_88500 _88501 _88502 : Type'} (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term181 _88500 _88501 _88502 a _35934 b _35935 c _35936) = (term180 _88500 _88501 _88502 a _35934 b _35935 c _35936).
Proof. exact (MK_COMB (@lem3410650 _88502 a _35934) (@lem3410649 _88500 _88501 b _35935 c _35936)). Qed.
Lemma lem3410653 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410654 {_88500 _88501 _88502 : Type'} (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term180 _88500 _88501 _88502 a _35934 b _35935 c _35936) = (term182 _88500 _88501 _88502 a _35934 b _35935 c _35936).
Proof. exact (@lem3410653 (a = _35934) (term61 _88500 _88501 b _35935 c _35936)). Qed.
Lemma lem3410655 {_88500 _88501 _88502 : Type'} (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term181 _88500 _88501 _88502 a _35934 b _35935 c _35936) = (term182 _88500 _88501 _88502 a _35934 b _35935 c _35936).
Proof. exact (TRANS (@lem3410651 _88500 _88501 _88502 a _35934 b _35935 c _35936) (@lem3410654 _88500 _88501 _88502 a _35934 b _35935 c _35936)). Qed.
Lemma lem3410656 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (_35934 : _88502) (_35935 : _88501) (_35936 : _88500) : (term183 _88500 _88501 _88502 P _35934 _35935 _35936) = (term183 _88500 _88501 _88502 P _35934 _35935 _35936).
Proof. exact (eq_refl (term183 _88500 _88501 _88502 P _35934 _35935 _35936)). Qed.
Lemma lem3410657 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term185 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term184 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (MK_COMB (@lem3410656 _88500 _88501 _88502 P _35934 _35935 _35936) (@lem3410655 _88500 _88501 _88502 a _35934 b _35935 c _35936)). Qed.
Lemma lem3410659 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410660 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term184 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term186 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (@lem3410659 (P _35934 _35935 _35936) (term63 _88500 _88501 _88502 a _35934 b _35935 c _35936)). Qed.
Lemma lem3410661 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term185 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term186 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (TRANS (@lem3410657 _88500 _88501 _88502 P a _35934 b _35935 c _35936) (@lem3410660 _88500 _88501 _88502 P a _35934 b _35935 c _35936)). Qed.
Lemma lem3410663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3410664 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term186 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term1100 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (@lem3410663 (term65 _88500 _88501 _88502 P a _35934 b _35935 c _35936)). Qed.
Lemma lem3410665 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (_35934 : _88502) (b : _88501) (_35935 : _88501) (c : _88500) (_35936 : _88500) : (term185 _88500 _88501 _88502 P a _35934 b _35935 c _35936) = (term1100 _88500 _88501 _88502 P a _35934 b _35935 c _35936).
Proof. exact (TRANS (@lem3410661 _88500 _88501 _88502 P a _35934 b _35935 c _35936) (@lem3410664 _88500 _88501 _88502 P a _35934 b _35935 c _35936)). Qed.
Lemma lem3410667 {_88500 _88501 : Type'} (b : _88501) (c : _88500) : term1101 _88500 _88501 b c.
Proof. exact (conj (@lem3410637 _88501 b) (@lem3410646 _88500 c)). Qed.
Lemma lem3410668 {_88500 _88501 _88502 : Type'} (a : _88502) (b : _88501) (c : _88500) : term1102 _88500 _88501 _88502 a b c.
Proof. exact (conj (@lem3410628 _88502 a) (@lem3410667 _88500 _88501 b c)). Qed.
Lemma lem3410669 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1103 _88500 _88501 _88502 P a b c.
Proof. exact (conj (@lem3410619 _88500 _88501 _88502 P a b c h1) (@lem3410668 _88500 _88501 _88502 a b c)). Qed.
Lemma lem3410671 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (_35936 : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1100 _88500 _88501 _88502 P a _35934 b _35935 c _35936.
Proof. exact (EQ_MP (@lem3410665 _88500 _88501 _88502 P a _35934 b _35935 c _35936) (@lem3410197 _88500 _88501 _88502 _35934 _35935 _35936 P a b c h1)). Qed.
Lemma lem3410672 {_88500 _88501 _88502 : Type'} (_35934 : _88502) (_35935 : _88501) (_35936 : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1100 _88500 _88501 _88502 P a _35934 b _35935 c _35936.
Proof. exact (@lem3410671 _88500 _88501 _88502 _35934 _35935 _35936 P a b c h1). Qed.
Lemma lem3410673 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1104 _88500 _88501 _88502 P a b c.
Proof. exact (@lem3410672 _88500 _88501 _88502 a b c P a b c h1). Qed.
Lemma lem3410676 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : False.
Proof. exact (@lem3410673 _88500 _88501 _88502 P a b c h1 (@lem3410669 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410677 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : term1095.
Proof. exact (fun h0 : ~ False => @lem3410676 _88500 _88501 _88502 P a b c h1). Qed.
Lemma lem3410679 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410680 : term1095 = False.
Proof. exact (@lem3410679 False). Qed.
Lemma lem3410681 {_88500 _88501 _88502 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term214 _88500 _88501 _88502 P a b c) : False.
Proof. exact (EQ_MP (@lem3410680) (@lem3410677 _88500 _88501 _88502 P a b c h1)). Qed.
Lemma lem3410683 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : P' x' y' z'.
Proof. exact (proj1 (@lem3410037 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410684 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term1092 _88563 _88564 _88565 P' x' y' z'.
Proof. exact (fun h0 : term210 _88563 _88564 _88565 P' x' y' z' => @lem3410683 _88563 _88564 _88565 x' y' z' P' a' b' c' h1). Qed.
Lemma lem3410686 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410687 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : (term1092 _88563 _88564 _88565 P' x' y' z') = (P' x' y' z').
Proof. exact (@lem3410686 (P' x' y' z')). Qed.
Lemma lem3410688 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : P' x' y' z'.
Proof. exact (EQ_MP (@lem3410687 _88563 _88564 _88565 P' x' y' z') (@lem3410684 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410691 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3410693 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (x' : _88565) (y' : _88564) (z' : _88563) : (term210 _88563 _88564 _88565 P' x' y' z') = (term1094 _88563 _88564 _88565 P' x' y' z').
Proof. exact (@lem3410691 (P' x' y' z')). Qed.
Lemma lem3410696 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term1094 _88563 _88564 _88565 P' x' y' z'.
Proof. exact (EQ_MP (@lem3410693 _88563 _88564 _88565 P' x' y' z') (@lem3410543 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410699 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : False.
Proof. exact (@lem3410696 _88563 _88564 _88565 x' y' z' P' a' b' c' h1 (@lem3410688 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410700 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : term1095.
Proof. exact (fun h0 : ~ False => @lem3410699 _88563 _88564 _88565 x' y' z' P' a' b' c' h1). Qed.
Lemma lem3410702 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410703 : term1095 = False.
Proof. exact (@lem3410702 False). Qed.
Lemma lem3410738 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : P' a' b' c'.
Proof. exact (proj2 (@lem3410035 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410739 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1092 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (fun h0 : term210 _88563 _88564 _88565 P' a' b' c' => @lem3410738 _88563 _88564 _88565 P' a' b' c' h1). Qed.
Lemma lem3410741 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410742 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) : (term1092 _88563 _88564 _88565 P' a' b' c') = (P' a' b' c').
Proof. exact (@lem3410741 (P' a' b' c')). Qed.
Lemma lem3410743 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : P' a' b' c'.
Proof. exact (EQ_MP (@lem3410742 _88563 _88564 _88565 P' a' b' c') (@lem3410739 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410745 {_88565 : Type'} (x : _88565) : x = x.
Proof. exact (@lem21386 _88565 x). Qed.
Lemma lem3410746 {_88565 : Type'} (x : _88565) : x = x.
Proof. exact (@lem3410745 _88565 x). Qed.
Lemma lem3410747 {_88565 : Type'} (a' : _88565) : a' = a'.
Proof. exact (@lem3410746 _88565 a'). Qed.
Lemma lem3410748 {_88565 : Type'} (a' : _88565) : term1096 _88565 a'.
Proof. exact (fun h0 : term1097 _88565 a' => @lem3410747 _88565 a'). Qed.
Lemma lem3410750 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410751 {_88565 : Type'} (a' : _88565) : (term1096 _88565 a') = (a' = a').
Proof. exact (@lem3410750 (a' = a')). Qed.
Lemma lem3410752 {_88565 : Type'} (a' : _88565) : a' = a'.
Proof. exact (EQ_MP (@lem3410751 _88565 a') (@lem3410748 _88565 a')). Qed.
Lemma lem3410754 {_88564 : Type'} (x : _88564) : x = x.
Proof. exact (@lem21386 _88564 x). Qed.
Lemma lem3410755 {_88564 : Type'} (x : _88564) : x = x.
Proof. exact (@lem3410754 _88564 x). Qed.
Lemma lem3410756 {_88564 : Type'} (b' : _88564) : b' = b'.
Proof. exact (@lem3410755 _88564 b'). Qed.
Lemma lem3410757 {_88564 : Type'} (b' : _88564) : term1096 _88564 b'.
Proof. exact (fun h0 : term1097 _88564 b' => @lem3410756 _88564 b'). Qed.
Lemma lem3410759 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410760 {_88564 : Type'} (b' : _88564) : (term1096 _88564 b') = (b' = b').
Proof. exact (@lem3410759 (b' = b')). Qed.
Lemma lem3410761 {_88564 : Type'} (b' : _88564) : b' = b'.
Proof. exact (EQ_MP (@lem3410760 _88564 b') (@lem3410757 _88564 b')). Qed.
Lemma lem3410763 {_88563 : Type'} (x : _88563) : x = x.
Proof. exact (@lem21386 _88563 x). Qed.
Lemma lem3410764 {_88563 : Type'} (x : _88563) : x = x.
Proof. exact (@lem3410763 _88563 x). Qed.
Lemma lem3410765 {_88563 : Type'} (c' : _88563) : c' = c'.
Proof. exact (@lem3410764 _88563 c'). Qed.
Lemma lem3410766 {_88563 : Type'} (c' : _88563) : term1096 _88563 c'.
Proof. exact (fun h0 : term1097 _88563 c' => @lem3410765 _88563 c'). Qed.
Lemma lem3410768 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410769 {_88563 : Type'} (c' : _88563) : (term1096 _88563 c') = (c' = c').
Proof. exact (@lem3410768 (c' = c')). Qed.
Lemma lem3410770 {_88563 : Type'} (c' : _88563) : c' = c'.
Proof. exact (EQ_MP (@lem3410769 _88563 c') (@lem3410766 _88563 c')). Qed.
Lemma lem3410772 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410773 {_88563 _88564 : Type'} (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term178 _88563 _88564 b' _35938 c' _35939) = (term177 _88563 _88564 b' _35938 c' _35939).
Proof. exact (@lem3410772 (b' = _35938) (c' = _35939)). Qed.
Lemma lem3410774 {_88565 : Type'} (a' : _88565) (_35937 : _88565) : (term179 _88565 a' _35937) = (term179 _88565 a' _35937).
Proof. exact (eq_refl (term179 _88565 a' _35937)). Qed.
Lemma lem3410775 {_88563 _88564 _88565 : Type'} (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term181 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939) = (term180 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939).
Proof. exact (MK_COMB (@lem3410774 _88565 a' _35937) (@lem3410773 _88563 _88564 b' _35938 c' _35939)). Qed.
Lemma lem3410777 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410778 {_88563 _88564 _88565 : Type'} (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term180 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939) = (term182 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939).
Proof. exact (@lem3410777 (a' = _35937) (term61 _88563 _88564 b' _35938 c' _35939)). Qed.
Lemma lem3410779 {_88563 _88564 _88565 : Type'} (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term181 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939) = (term182 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939).
Proof. exact (TRANS (@lem3410775 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939) (@lem3410778 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410780 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) : (term183 _88563 _88564 _88565 P' _35937 _35938 _35939) = (term183 _88563 _88564 _88565 P' _35937 _35938 _35939).
Proof. exact (eq_refl (term183 _88563 _88564 _88565 P' _35937 _35938 _35939)). Qed.
Lemma lem3410781 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term185 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term184 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (MK_COMB (@lem3410780 _88563 _88564 _88565 P' _35937 _35938 _35939) (@lem3410779 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410783 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3410784 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term184 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term186 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (@lem3410783 (P' _35937 _35938 _35939) (term63 _88563 _88564 _88565 a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410785 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term185 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term186 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (TRANS (@lem3410781 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) (@lem3410784 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410787 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3410788 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term186 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term1100 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (@lem3410787 (term65 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410789 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (_35937 : _88565) (b' : _88564) (_35938 : _88564) (c' : _88563) (_35939 : _88563) : (term185 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) = (term1100 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939).
Proof. exact (TRANS (@lem3410785 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) (@lem3410788 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939)). Qed.
Lemma lem3410791 {_88563 _88564 : Type'} (b' : _88564) (c' : _88563) : term1101 _88563 _88564 b' c'.
Proof. exact (conj (@lem3410761 _88564 b') (@lem3410770 _88563 c')). Qed.
Lemma lem3410792 {_88563 _88564 _88565 : Type'} (a' : _88565) (b' : _88564) (c' : _88563) : term1102 _88563 _88564 _88565 a' b' c'.
Proof. exact (conj (@lem3410752 _88565 a') (@lem3410791 _88563 _88564 b' c')). Qed.
Lemma lem3410793 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1103 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (conj (@lem3410743 _88563 _88564 _88565 P' a' b' c' h1) (@lem3410792 _88563 _88564 _88565 a' b' c')). Qed.
Lemma lem3410795 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1100 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939.
Proof. exact (EQ_MP (@lem3410789 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939) (@lem3410225 _88563 _88564 _88565 _35937 _35938 _35939 P' a' b' c' h1)). Qed.
Lemma lem3410796 {_88563 _88564 _88565 : Type'} (_35937 : _88565) (_35938 : _88564) (_35939 : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1100 _88563 _88564 _88565 P' a' _35937 b' _35938 c' _35939.
Proof. exact (@lem3410795 _88563 _88564 _88565 _35937 _35938 _35939 P' a' b' c' h1). Qed.
Lemma lem3410797 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1104 _88563 _88564 _88565 P' a' b' c'.
Proof. exact (@lem3410796 _88563 _88564 _88565 a' b' c' P' a' b' c' h1). Qed.
Lemma lem3410800 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : False.
Proof. exact (@lem3410797 _88563 _88564 _88565 P' a' b' c' h1 (@lem3410793 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410801 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : term1095.
Proof. exact (fun h0 : ~ False => @lem3410800 _88563 _88564 _88565 P' a' b' c' h1). Qed.
Lemma lem3410803 (p : Prop) : (term1093 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3410804 : term1095 = False.
Proof. exact (@lem3410803 False). Qed.
Lemma lem3410805 {_88563 _88564 _88565 : Type'} (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term286 _88563 _88564 _88565 P' a' b' c') : False.
Proof. exact (EQ_MP (@lem3410804) (@lem3410801 _88563 _88564 _88565 P' a' b' c' h1)). Qed.
Lemma lem3410808 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c') : False.
Proof. exact (EQ_MP (@lem3410703) (@lem3410700 _88563 _88564 _88565 x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410811 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term543 _88500 _88501 _88502 x y z P a b c) : False.
Proof. exact (EQ_MP (@lem3410579) (@lem3410576 _88500 _88501 _88502 x y z P a b c h1)). Qed.
Lemma lem3410812 {_88563 _88564 _88565 : Type'} (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term838 _88563 _88564 _88565 x' y' z' P' a' b' c') : False.
Proof. exact (or_elim (@lem3410021 _88563 _88564 _88565 x' y' z' P' a' b' c' h1) (fun h0 : term719 _88563 _88564 _88565 x' y' z' P' a' b' c' => @lem3410808 _88563 _88564 _88565 x' y' z' P' a' b' c' h0) (fun h0 : term286 _88563 _88564 _88565 P' a' b' c' => @lem3410805 _88563 _88564 _88565 P' a' b' c' h0)). Qed.
Lemma lem3410813 {_88500 _88501 _88502 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term664 _88500 _88501 _88502 x y z P a b c) : False.
Proof. exact (or_elim (@lem3410020 _88500 _88501 _88502 x y z P a b c h1) (fun h0 : term543 _88500 _88501 _88502 x y z P a b c => @lem3410811 _88500 _88501 _88502 x y z P a b c h0) (fun h0 : term214 _88500 _88501 _88502 P a b c => @lem3410681 _88500 _88501 _88502 P a b c h0)). Qed.
Lemma lem3410814 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') : False.
Proof. exact (or_elim (@lem3410019 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1) (fun h0 : term664 _88500 _88501 _88502 x y z P a b c => @lem3410813 _88500 _88501 _88502 x y z P a b c h0) (fun h0 : term838 _88563 _88564 _88565 x' y' z' P' a' b' c' => @lem3410812 _88563 _88564 _88565 x' y' z' P' a' b' c' h0)). Qed.
Lemma lem3410815 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') : (term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') = False.
Proof. exact (prop_ext (fun h2 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' => @lem3410814 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1) (fun h2 : False => @lem3410019 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410816 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (z' : _88563) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1046 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c') : False.
Proof. exact (EQ_MP (@lem3410815 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1) (@lem3410019 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h1)). Qed.
Lemma lem3410817 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (y' : _88564) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1049 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c') : False.
Proof. exact (ex_elim (@lem3409806 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c' h1) (fun z' : _88563 => fun h0 : term1048 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c' z' => @lem3410816 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' z' P' a' b' c' h0)). Qed.
Lemma lem3410818 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (x' : _88565) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1051 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c') : False.
Proof. exact (ex_elim (@lem3409805 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c' h1) (fun y' : _88564 => fun h0 : term1050 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c' y' => @lem3410817 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' y' P' a' b' c' h0)). Qed.
Lemma lem3410819 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (c' : _88563) (h1 : term1053 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c') : False.
Proof. exact (ex_elim (@lem3409804 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c' h1) (fun x' : _88565 => fun h0 : term1052 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c' x' => @lem3410818 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c x' P' a' b' c' h0)). Qed.
Lemma lem3410820 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (b' : _88564) (h1 : term1055 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b') : False.
Proof. exact (ex_elim (@lem3409803 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' h1) (fun c' : _88563 => fun h0 : term1054 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c' => @lem3410819 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' c' h0)). Qed.
Lemma lem3410821 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (a' : _88565) (h1 : term1057 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a') : False.
Proof. exact (ex_elim (@lem3409802 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' h1) (fun b' : _88564 => fun h0 : term1056 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' => @lem3410820 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' b' h0)). Qed.
Lemma lem3410822 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (P' : type1517 _88563 _88564 _88565) (h1 : term1059 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P') : False.
Proof. exact (ex_elim (@lem3409801 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' h1) (fun a' : _88565 => fun h0 : term1058 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' => @lem3410821 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' a' h0)). Qed.
Lemma lem3410823 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (z : _88500) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1061 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c) : False.
Proof. exact (ex_elim (@lem3409800 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c h1) (fun P' : type1517 _88563 _88564 _88565 => fun h0 : term1060 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' => @lem3410822 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c P' h0)). Qed.
Lemma lem3410824 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (y : _88501) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1063 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c) : False.
Proof. exact (ex_elim (@lem3409799 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c h1) (fun z : _88500 => fun h0 : term1062 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c z => @lem3410823 _88500 _88501 _88502 _88563 _88564 _88565 x y z P a b c h0)). Qed.
Lemma lem3410825 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (x : _88502) (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1065 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c) : False.
Proof. exact (ex_elim (@lem3409798 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c h1) (fun y : _88501 => fun h0 : term1064 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c y => @lem3410824 _88500 _88501 _88502 _88563 _88564 _88565 x y P a b c h0)). Qed.
Lemma lem3410826 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (c : _88500) (h1 : term1067 _88500 _88501 _88502 _88563 _88564 _88565 P a b c) : False.
Proof. exact (ex_elim (@lem3409797 _88500 _88501 _88502 _88563 _88564 _88565 P a b c h1) (fun x : _88502 => fun h0 : term1066 _88500 _88501 _88502 _88563 _88564 _88565 P a b c x => @lem3410825 _88500 _88501 _88502 _88563 _88564 _88565 x P a b c h0)). Qed.
Lemma lem3410827 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (b : _88501) (h1 : term1069 _88500 _88501 _88502 _88563 _88564 _88565 P a b) : False.
Proof. exact (ex_elim (@lem3409796 _88500 _88501 _88502 _88563 _88564 _88565 P a b h1) (fun c : _88500 => fun h0 : term1068 _88500 _88501 _88502 _88563 _88564 _88565 P a b c => @lem3410826 _88500 _88501 _88502 _88563 _88564 _88565 P a b c h0)). Qed.
Lemma lem3410828 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (a : _88502) (h1 : term1071 _88500 _88501 _88502 _88563 _88564 _88565 P a) : False.
Proof. exact (ex_elim (@lem3409795 _88500 _88501 _88502 _88563 _88564 _88565 P a h1) (fun b : _88501 => fun h0 : term1070 _88500 _88501 _88502 _88563 _88564 _88565 P a b => @lem3410827 _88500 _88501 _88502 _88563 _88564 _88565 P a b h0)). Qed.
Lemma lem3410829 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (P : type1517 _88500 _88501 _88502) (h1 : term1073 _88500 _88501 _88502 _88563 _88564 _88565 P) : False.
Proof. exact (ex_elim (@lem3409794 _88500 _88501 _88502 _88563 _88564 _88565 P h1) (fun a : _88502 => fun h0 : term1072 _88500 _88501 _88502 _88563 _88564 _88565 P a => @lem3410828 _88500 _88501 _88502 _88563 _88564 _88565 P a h0)). Qed.
Lemma lem3410830 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : False.
Proof. exact (ex_elim (@lem3409793 _88500 _88501 _88502 _88563 _88564 _88565 h1) (fun P : type1517 _88500 _88501 _88502 => fun h0 : term1074 _88500 _88501 _88502 _88563 _88564 _88565 P => @lem3410829 _88500 _88501 _88502 _88563 _88564 _88565 P h0)). Qed.
Lemma lem3410831 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : (term171 _88500 _88501 _88502 _88563 _88564 _88565) = False.
Proof. exact (prop_ext (fun h2 : term171 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3410830 _88500 _88501 _88502 _88563 _88564 _88565 h1) (fun h2 : False => @lem3406530 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3410832 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : False.
Proof. exact (EQ_MP (@lem3410831 _88500 _88501 _88502 _88563 _88564 _88565 h1) (@lem3406530 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3410833 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term171 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3410832 _88500 _88501 _88502 _88563 _88564 _88565 h0). Qed.
Lemma lem3410834 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term168 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (EQ_MP (@lem3406529 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3410833 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3410835 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (EQ_MP (@lem3406525 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3410834 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3410837 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (@lem3406175 _88500 _88501 _88502 _88563 _88564 _88565 (@lem3410835 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3410838 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : False.
Proof. exact (@lem3410837 _88500 _88501 _88502 _88563 _88564 _88565 (@lem3406159 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3410839 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : (term171 _88500 _88501 _88502 _88563 _88564 _88565) = False.
Proof. exact (prop_ext (fun h2 : term171 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3410838 _88500 _88501 _88502 _88563 _88564 _88565 h1) (fun h2 : False => @lem3406159 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3410840 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} (h1 : term171 _88500 _88501 _88502 _88563 _88564 _88565) : False.
Proof. exact (EQ_MP (@lem3410839 _88500 _88501 _88502 _88563 _88564 _88565 h1) (@lem3406159 _88500 _88501 _88502 _88563 _88564 _88565 h1)). Qed.
Lemma lem3410841 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term170 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (fun h0 : term171 _88500 _88501 _88502 _88563 _88564 _88565 => @lem3410840 _88500 _88501 _88502 _88563 _88564 _88565 h0). Qed.
Lemma lem3410842 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term168 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (EQ_MP (@lem3406158 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3410841 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
Lemma lem3410843 {_88500 _88501 _88502 _88563 _88564 _88565 : Type'} : term167 _88500 _88501 _88502 _88563 _88564 _88565.
Proof. exact (EQ_MP (@lem3406154 _88500 _88501 _88502 _88563 _88564 _88565) (@lem3410842 _88500 _88501 _88502 _88563 _88564 _88565)). Qed.
