Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_LZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
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
Require Import thm21385_spec.
Require Import thm69_spec.
Lemma lem1356752 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1356753 : term1 = term2.
Proof. exact (@lem1356752 term1). Qed.
Lemma lem1356754 : term2 = term1.
Proof. exact (SYM (@lem1356753)). Qed.
Lemma lem1356755 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1356758 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1356759 : term5.
Proof. exact (fun h0 : term4 => @lem1356758 h0). Qed.
Lemma lem1356760 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1356761 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1356762 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1356760 h2 (@lem1356761 h1)). Qed.
Lemma lem1356763 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1356762 h1 h0). Qed.
Lemma lem1356764 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1356765 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1356763 h1 (@lem1356764 h2)). Qed.
Lemma lem1356766 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1356765 h0 h1). Qed.
Lemma lem1356767 : term7.
Proof. exact (fun h0 : term5 => @lem1356766 h0). Qed.
Lemma lem1356770 : term5.
Proof. exact (@lem1356767 (@lem1356759)). Qed.
Lemma lem1356784 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1356785 : term8 = term9.
Proof. exact (@lem1356784 term10). Qed.
Lemma lem1356794 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1356795 : term12 = term13.
Proof. exact (MK_COMB (@lem1356794) (@lem1356785)). Qed.
Lemma lem1356798 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1356805 : term4 = term15.
Proof. exact (MK_COMB (@lem1356798) (@lem1356795)). Qed.
Lemma lem1356806 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1356807 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1356806 y x)). Qed.
Lemma lem1356808 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356809 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1356808) (@lem1356807 x)). Qed.
Lemma lem1356810 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1356809 x)). Qed.
Lemma lem1356811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356812 : term10 = term10.
Proof. exact (MK_COMB (@lem1356811) (@lem1356810)). Qed.
Lemma lem1356813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1356814 : term9 = term9.
Proof. exact (MK_COMB (@lem1356813) (@lem1356812)). Qed.
Lemma lem1356815 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1356816 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1356815 x)). Qed.
Lemma lem1356817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356818 : term22 = term22.
Proof. exact (MK_COMB (@lem1356817) (@lem1356816)). Qed.
Lemma lem1356819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356820 : term11 = term11.
Proof. exact (MK_COMB (@lem1356819) (@lem1356818)). Qed.
Lemma lem1356821 : term13 = term13.
Proof. exact (MK_COMB (@lem1356820) (@lem1356814)). Qed.
Lemma lem1356822 (x : real) : ((term23 x) = term20) = ((term23 x) = term20).
Proof. exact (eq_refl ((term23 x) = term20)). Qed.
Lemma lem1356823 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1356822 x)). Qed.
Lemma lem1356824 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356825 : term1 = term1.
Proof. exact (MK_COMB (@lem1356824) (@lem1356823)). Qed.
Lemma lem1356826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1356827 : term3 = term3.
Proof. exact (MK_COMB (@lem1356826) (@lem1356825)). Qed.
Lemma lem1356828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356829 : term14 = term14.
Proof. exact (MK_COMB (@lem1356828) (@lem1356827)). Qed.
Lemma lem1356830 : term15 = term15.
Proof. exact (MK_COMB (@lem1356829) (@lem1356821)). Qed.
Lemma lem1356861 : term4 = term15.
Proof. exact (TRANS (@lem1356805) (@lem1356830)). Qed.
Lemma lem1356862 : term15 = term4.
Proof. exact (SYM (@lem1356861)). Qed.
Lemma lem1356863 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1356864 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1356865 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1356867 (P : real -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1356868 : term3 = term27.
Proof. exact (@lem1356867 term24). Qed.
Lemma lem1356869 (x : real) : (term28 x) = ((term23 x) = term20).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1356870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1356872 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1356870) (@lem1356869 x)). Qed.
Lemma lem1356873 : term31 = term32.
Proof. exact (fun_ext (fun x : real => @lem1356872 x)). Qed.
Lemma lem1356874 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1356875 : term27 = term33.
Proof. exact (MK_COMB (@lem1356874) (@lem1356873)). Qed.
Lemma lem1356884 : term3 = term33.
Proof. exact (TRANS (@lem1356868) (@lem1356875)). Qed.
Lemma lem1356885 (h1 : term3) : term33.
Proof. exact (EQ_MP (@lem1356884) (@lem1356863 h1)). Qed.
Lemma lem1356886 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1356887 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1356886 x)). Qed.
Lemma lem1356888 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356897 : term22 = term22.
Proof. exact (MK_COMB (@lem1356888) (@lem1356887)). Qed.
Lemma lem1356898 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1356897) (@lem1356864 h1)). Qed.
Lemma lem1356899 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1356900 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1356899 y x)). Qed.
Lemma lem1356901 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356902 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1356901) (@lem1356900 x)). Qed.
Lemma lem1356903 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1356902 x)). Qed.
Lemma lem1356904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356917 : term10 = term10.
Proof. exact (MK_COMB (@lem1356904) (@lem1356903)). Qed.
Lemma lem1356918 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1356917) (@lem1356865 h1)). Qed.
Lemma lem1356936 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1356937 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1356936 x)). Qed.
Lemma lem1356938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356939 : term22 = term22.
Proof. exact (MK_COMB (@lem1356938) (@lem1356937)). Qed.
Lemma lem1356940 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1356939) (@lem1356898 h1)). Qed.
Lemma lem1356953 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1356954 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1356953 y x)). Qed.
Lemma lem1356955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356956 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1356955) (@lem1356954 x)). Qed.
Lemma lem1356957 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1356956 x)). Qed.
Lemma lem1356958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356959 : term10 = term10.
Proof. exact (MK_COMB (@lem1356958) (@lem1356957)). Qed.
Lemma lem1356960 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1356959) (@lem1356918 h1)). Qed.
Lemma lem1356980 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1356982 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1356983 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1356982 x)). Qed.
Lemma lem1356984 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356986 : term22 = term22.
Proof. exact (MK_COMB (@lem1356984) (@lem1356983)). Qed.
Lemma lem1356987 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1356986) (@lem1356940 h1)). Qed.
Lemma lem1356989 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1356990 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1356989 y x)). Qed.
Lemma lem1356991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356992 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1356991) (@lem1356990 x)). Qed.
Lemma lem1356993 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1356992 x)). Qed.
Lemma lem1356994 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356996 : term10 = term10.
Proof. exact (MK_COMB (@lem1356994) (@lem1356993)). Qed.
Lemma lem1356997 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1356996) (@lem1356960 h1)). Qed.
Lemma lem1357001 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1357002 (_24140 : real) (h1 : term22) : term34 _24140.
Proof. exact (@lem1356987 h1 _24140). Qed.
Lemma lem1357003 (_24140 : real) : (term34 _24140) = ((term19 _24140) = term20).
Proof. exact (eq_refl (term34 _24140)). Qed.
Lemma lem1357005 (_24141 : real) (h1 : term10) : term35 _24141.
Proof. exact (@lem1356997 h1 _24141). Qed.
Lemma lem1357006 (_24141 : real) : (term35 _24141) = (term17 _24141).
Proof. exact (eq_refl (term35 _24141)). Qed.
Lemma lem1357007 (_24141 : real) (h1 : term10) : term17 _24141.
Proof. exact (EQ_MP (@lem1357006 _24141) (@lem1357005 _24141 h1)). Qed.
Lemma lem1357008 (_24141 : real) (_24142 : real) (h1 : term10) : term36 _24141 _24142.
Proof. exact (@lem1357007 _24141 h1 _24142). Qed.
Lemma lem1357009 (_24142 : real) (_24141 : real) : (term36 _24141 _24142) = ((real_mul _24141 _24142) = (real_mul _24142 _24141)).
Proof. exact (eq_refl (term36 _24141 _24142)). Qed.
Lemma lem1357016 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1357049 (x : real) (y : real) (z : real) : term37 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1357053 (_24142 : real) (_24141 : real) (h1 : term10) : (real_mul _24141 _24142) = (real_mul _24142 _24141).
Proof. exact (EQ_MP (@lem1357009 _24142 _24141) (@lem1357008 _24141 _24142 h1)). Qed.
Lemma lem1357054 (x : real) (h1 : term10) : (term19 x) = (term23 x).
Proof. exact (@lem1357053 term20 x h1). Qed.
Lemma lem1357055 (x : real) (h1 : term10) : term38 x.
Proof. exact (fun h0 : term39 x => @lem1357054 x h1). Qed.
Lemma lem1357057 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1357058 (x : real) : (term38 x) = ((term19 x) = (term23 x)).
Proof. exact (@lem1357057 ((term19 x) = (term23 x))). Qed.
Lemma lem1357059 (x : real) (h1 : term10) : (term19 x) = (term23 x).
Proof. exact (EQ_MP (@lem1357058 x) (@lem1357055 x h1)). Qed.
Lemma lem1357061 (_24140 : real) (h1 : term22) : (term19 _24140) = term20.
Proof. exact (EQ_MP (@lem1357003 _24140) (@lem1357002 _24140 h1)). Qed.
Lemma lem1357062 (x : real) (h1 : term22) : (term19 x) = term20.
Proof. exact (@lem1357061 x h1). Qed.
Lemma lem1357063 (x : real) (h1 : term22) : term41 x.
Proof. exact (fun h0 : term42 x => @lem1357062 x h1). Qed.
Lemma lem1357065 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1357066 (x : real) : (term41 x) = ((term19 x) = term20).
Proof. exact (@lem1357065 ((term19 x) = term20)). Qed.
Lemma lem1357067 (x : real) (h1 : term22) : (term19 x) = term20.
Proof. exact (EQ_MP (@lem1357066 x) (@lem1357063 x h1)). Qed.
Lemma lem1357085 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1357086 (y : real) (x : real) (z : real) : (term43 x y z) = (term44 y x z).
Proof. exact (@lem1357085 (y = z) (term45 x z)). Qed.
Lemma lem1357096 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1357097 (y : real) (x : real) (z : real) : (term37 x y z) = (term47 y x z).
Proof. exact (MK_COMB (@lem1357096 x y) (@lem1357086 y x z)). Qed.
Lemma lem1357101 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1357102 (y : real) (x : real) (z : real) : (term47 y x z) = (term49 y x z).
Proof. exact (@lem1357101 (y = z) (term45 x y) (term45 x z)). Qed.
Lemma lem1357124 (y : real) (x : real) (z : real) : (term37 x y z) = (term49 y x z).
Proof. exact (TRANS (@lem1357097 y x z) (@lem1357102 y x z)). Qed.
Lemma lem1357125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357126 (y : real) (x : real) (z : real) : (term50 x y z) = (term51 y x z).
Proof. exact (MK_COMB (@lem1357125) (@lem1357124 y x z)). Qed.
Lemma lem1357148 (y : real) (x : real) (z : real) : (term49 y x z) = (term49 y x z).
Proof. exact (eq_refl (term49 y x z)). Qed.
Lemma lem1357149 (y : real) (x : real) (z : real) : ((term37 x y z) = (term49 y x z)) = ((term49 y x z) = (term49 y x z)).
Proof. exact (MK_COMB (@lem1357126 y x z) (@lem1357148 y x z)). Qed.
Lemma lem1357151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1357152 (x : Prop) : (x = x) = True.
Proof. exact (@lem1357151 Prop x). Qed.
Lemma lem1357153 (y : real) (x : real) (z : real) : ((term49 y x z) = (term49 y x z)) = True.
Proof. exact (@lem1357152 (term49 y x z)). Qed.
Lemma lem1357154 (y : real) (x : real) (z : real) : ((term37 x y z) = (term49 y x z)) = True.
Proof. exact (TRANS (@lem1357149 y x z) (@lem1357153 y x z)). Qed.
Lemma lem1357155 (y : real) (x : real) (z : real) : True = ((term37 x y z) = (term49 y x z)).
Proof. exact (SYM (@lem1357154 y x z)). Qed.
Lemma lem1357156 (y : real) (x : real) (z : real) : (term37 x y z) = (term49 y x z).
Proof. exact (EQ_MP (@lem1357155 y x z) (@lem0)). Qed.
Lemma lem1357157 (y : real) (x : real) (z : real) : term49 y x z.
Proof. exact (EQ_MP (@lem1357156 y x z) (@lem1357049 x y z)). Qed.
Lemma lem1357159 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1357160 (x : real) (y : real) (z : real) : (term49 y x z) = (term53 x y z).
Proof. exact (@lem1357159 (term54 y x z) (y = z)). Qed.
Lemma lem1357162 (a : Prop) (b : Prop) : (term55 a b) = (term56 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1357163 (y : real) (x : real) (z : real) : (term57 y x z) = (term58 y x z).
Proof. exact (@lem1357162 (term45 x y) (term45 x z)). Qed.
Lemma lem1357165 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1357166 (x : real) (y : real) : (term60 x y) = (x = y).
Proof. exact (@lem1357165 (x = y)). Qed.
Lemma lem1357167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357168 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1357167) (@lem1357166 x y)). Qed.
Lemma lem1357170 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1357171 (x : real) (z : real) : (term60 x z) = (x = z).
Proof. exact (@lem1357170 (x = z)). Qed.
Lemma lem1357172 (y : real) (x : real) (z : real) : (term58 y x z) = (term63 y x z).
Proof. exact (MK_COMB (@lem1357168 x y) (@lem1357171 x z)). Qed.
Lemma lem1357173 (y : real) (x : real) (z : real) : (term57 y x z) = (term63 y x z).
Proof. exact (TRANS (@lem1357163 y x z) (@lem1357172 y x z)). Qed.
Lemma lem1357174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1357175 (y : real) (x : real) (z : real) : (term64 y x z) = (term65 y x z).
Proof. exact (MK_COMB (@lem1357174) (@lem1357173 y x z)). Qed.
Lemma lem1357176 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1357177 (x : real) (y : real) (z : real) : (term53 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1357175 y x z) (@lem1357176 y z)). Qed.
Lemma lem1357178 (x : real) (y : real) (z : real) : (term49 y x z) = (term66 x y z).
Proof. exact (TRANS (@lem1357160 x y z) (@lem1357177 x y z)). Qed.
Lemma lem1357180 (x : real) (h1 : term10) (h2 : term22) : term67 x.
Proof. exact (conj (@lem1357059 x h1) (@lem1357067 x h2)). Qed.
Lemma lem1357182 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (EQ_MP (@lem1357178 x y z) (@lem1357157 y x z)). Qed.
Lemma lem1357183 (x : real) : term68 x.
Proof. exact (@lem1357182 (term19 x) (term23 x) term20). Qed.
Lemma lem1357186 (x : real) (h1 : term10) (h2 : term22) : (term23 x) = term20.
Proof. exact (@lem1357183 x (@lem1357180 x h1 h2)). Qed.
Lemma lem1357187 (x : real) (h1 : term10) (h2 : term22) : term69 x.
Proof. exact (fun h0 : term30 x => @lem1357186 x h1 h2). Qed.
Lemma lem1357189 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1357190 (x : real) : (term69 x) = ((term23 x) = term20).
Proof. exact (@lem1357189 ((term23 x) = term20)). Qed.
Lemma lem1357191 (x : real) (h1 : term10) (h2 : term22) : (term23 x) = term20.
Proof. exact (EQ_MP (@lem1357190 x) (@lem1357187 x h1 h2)). Qed.
Lemma lem1357194 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1357196 (x : real) : (term30 x) = (term70 x).
Proof. exact (@lem1357194 ((term23 x) = term20)). Qed.
Lemma lem1357199 (x : real) (h1 : term30 x) : term70 x.
Proof. exact (EQ_MP (@lem1357196 x) (@lem1357016 x h1)). Qed.
Lemma lem1357202 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (@lem1357199 x h3 (@lem1357191 x h1 h2)). Qed.
Lemma lem1357203 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term71.
Proof. exact (fun h0 : ~ False => @lem1357202 x h1 h2 h3). Qed.
Lemma lem1357205 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1357206 : term71 = False.
Proof. exact (@lem1357205 False). Qed.
Lemma lem1357207 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357206) (@lem1357203 x h1 h2 h3)). Qed.
Lemma lem1357208 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1357207 x h1 h2 h3) (fun h4 : False => @lem1357016 x h3)). Qed.
Lemma lem1357209 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357208 x h1 h2 h3) (@lem1357016 x h3)). Qed.
Lemma lem1357210 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1357209 x h1 h2 h3) (fun h4 : False => @lem1357001 x h3)). Qed.
Lemma lem1357211 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357210 x h1 h2 h3) (@lem1357001 x h3)). Qed.
Lemma lem1357212 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1357211 x h1 h2 h3) (fun h4 : False => @lem1357001 x h3)). Qed.
Lemma lem1357213 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357212 x h1 h2 h3) (@lem1357001 x h3)). Qed.
Lemma lem1357214 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1357213 x h1 h2 h3) (fun h4 : False => @lem1356997 h1)). Qed.
Lemma lem1357215 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357214 x h1 h2 h3) (@lem1356997 h1)). Qed.
Lemma lem1357216 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1357215 x h1 h2 h3) (fun h4 : False => @lem1356987 h2)). Qed.
Lemma lem1357217 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357216 x h1 h2 h3) (@lem1356987 h2)). Qed.
Lemma lem1357218 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1357217 x h1 h2 h3) (fun h4 : False => @lem1356980 x h3)). Qed.
Lemma lem1357219 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357218 x h1 h2 h3) (@lem1356980 x h3)). Qed.
Lemma lem1357220 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1357219 x h1 h2 h3) (fun h4 : False => @lem1356960 h1)). Qed.
Lemma lem1357221 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357220 x h1 h2 h3) (@lem1356960 h1)). Qed.
Lemma lem1357222 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1357221 x h1 h2 h3) (fun h4 : False => @lem1356940 h2)). Qed.
Lemma lem1357223 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1357222 x h1 h2 h3) (@lem1356940 h2)). Qed.
Lemma lem1357224 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1356885 h3) (fun x : real => fun h0 : term32 x => @lem1357223 x h1 h2 h0)). Qed.
Lemma lem1357225 (h1 : term10) (h2 : term22) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1357224 h1 h2 h3) (fun h4 : False => @lem1356918 h1)). Qed.
Lemma lem1357226 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1357225 h1 h2 h3) (@lem1356918 h1)). Qed.
Lemma lem1357227 (h1 : term10) (h2 : term22) (h3 : term3) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1357226 h1 h2 h3) (fun h4 : False => @lem1356898 h2)). Qed.
Lemma lem1357228 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1357227 h1 h2 h3) (@lem1356898 h2)). Qed.
Lemma lem1357229 (h1 : term22) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1357228 h0 h1 h2). Qed.
Lemma lem1357230 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1357231 (h1 : term22) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1357230) (@lem1357229 h1 h2)). Qed.
Lemma lem1357232 (h1 : term3) : term13.
Proof. exact (fun h0 : term22 => @lem1357231 h0 h1). Qed.
Lemma lem1357233 : term15.
Proof. exact (fun h0 : term3 => @lem1357232 h0). Qed.
Lemma lem1357234 : term4.
Proof. exact (EQ_MP (@lem1356862) (@lem1357233)). Qed.
Lemma lem1357236 : term4.
Proof. exact (@lem1356770 (@lem1357234)). Qed.
Lemma lem1357237 (h1 : term3) : term12.
Proof. exact (@lem1357236 (@lem1356755 h1)). Qed.
Lemma lem1357238 (h1 : term3) : term8.
Proof. exact (@lem1357237 h1 (@lem1356740)). Qed.
Lemma lem1357239 (h1 : term3) : False.
Proof. exact (@lem1357238 h1 (@lem1338712)). Qed.
Lemma lem1357240 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1357239 h1) (fun h2 : False => @lem1356755 h1)). Qed.
Lemma lem1357241 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1357240 h1) (@lem1356755 h1)). Qed.
Lemma lem1357242 : term2.
Proof. exact (fun h0 : term3 => @lem1357241 h0). Qed.
Lemma lem1357243 : term1.
Proof. exact (EQ_MP (@lem1356754) (@lem1357242)). Qed.
