Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RMUL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LT_LMUL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1584767 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1584768 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1584769 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1584768 t1) (@lem1584767 t1)). Qed.
Lemma lem1584770 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1584769 t1 t2). Qed.
Lemma lem1584771 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1584772 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1584771 t1 t2) (@lem1584770 t1 t2)). Qed.
Lemma lem1584773 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1584772 t1 t2 t3). Qed.
Lemma lem1584774 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1584775 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1584774 t1 t2 t3) (@lem1584773 t1 t2 t3)). Qed.
Lemma lem1584776 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1584775 t1 t2 t3)). Qed.
Lemma lem1584778 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1584779 : term8 = term9.
Proof. exact (@lem1584778 term8). Qed.
Lemma lem1584780 : term9 = term8.
Proof. exact (SYM (@lem1584779)). Qed.
Lemma lem1584781 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1584784 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1584785 : term12.
Proof. exact (fun h0 : term11 => @lem1584784 h0). Qed.
Lemma lem1584786 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1584787 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1584788 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1584786 h2 (@lem1584787 h1)). Qed.
Lemma lem1584789 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1584788 h1 h0). Qed.
Lemma lem1584790 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1584791 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1584789 h1 (@lem1584790 h2)). Qed.
Lemma lem1584792 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1584791 h0 h1). Qed.
Lemma lem1584793 : term14.
Proof. exact (fun h0 : term12 => @lem1584792 h0). Qed.
Lemma lem1584796 : term12.
Proof. exact (@lem1584793 (@lem1584785)). Qed.
Lemma lem1584834 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1584835 : term15 = term16.
Proof. exact (@lem1584834 term17). Qed.
Lemma lem1584844 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1584845 : term19 = term20.
Proof. exact (MK_COMB (@lem1584844) (@lem1584835)). Qed.
Lemma lem1584848 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1584855 : term11 = term22.
Proof. exact (MK_COMB (@lem1584848) (@lem1584845)). Qed.
Lemma lem1584856 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1584857 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1584856 y x)). Qed.
Lemma lem1584858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584859 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1584858) (@lem1584857 x)). Qed.
Lemma lem1584860 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1584859 x)). Qed.
Lemma lem1584861 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584862 : term17 = term17.
Proof. exact (MK_COMB (@lem1584861) (@lem1584860)). Qed.
Lemma lem1584863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1584864 : term16 = term16.
Proof. exact (MK_COMB (@lem1584863) (@lem1584862)). Qed.
Lemma lem1584873 (y : real) (x : real) (z : real) : (term26 y x z) = (term26 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1584874 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : real => @lem1584873 y x z)). Qed.
Lemma lem1584875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584876 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1584875) (@lem1584874 y x)). Qed.
Lemma lem1584877 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1584876 y x)). Qed.
Lemma lem1584878 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584879 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1584878) (@lem1584877 x)). Qed.
Lemma lem1584880 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1584879 x)). Qed.
Lemma lem1584881 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584882 : term32 = term32.
Proof. exact (MK_COMB (@lem1584881) (@lem1584880)). Qed.
Lemma lem1584883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584884 : term18 = term18.
Proof. exact (MK_COMB (@lem1584883) (@lem1584882)). Qed.
Lemma lem1584885 : term20 = term20.
Proof. exact (MK_COMB (@lem1584884) (@lem1584864)). Qed.
Lemma lem1584894 (x : real) (y : real) (z : real) : (term33 x y z) = (term33 x y z).
Proof. exact (eq_refl (term33 x y z)). Qed.
Lemma lem1584895 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : real => @lem1584894 x y z)). Qed.
Lemma lem1584896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584897 (x : real) (y : real) : (term35 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1584896) (@lem1584895 x y)). Qed.
Lemma lem1584898 (x : real) : (term36 x) = (term36 x).
Proof. exact (fun_ext (fun y : real => @lem1584897 x y)). Qed.
Lemma lem1584899 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584900 (x : real) : (term37 x) = (term37 x).
Proof. exact (MK_COMB (@lem1584899) (@lem1584898 x)). Qed.
Lemma lem1584901 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1584900 x)). Qed.
Lemma lem1584902 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1584903 : term8 = term8.
Proof. exact (MK_COMB (@lem1584902) (@lem1584901)). Qed.
Lemma lem1584904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1584905 : term10 = term10.
Proof. exact (MK_COMB (@lem1584904) (@lem1584903)). Qed.
Lemma lem1584906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584907 : term21 = term21.
Proof. exact (MK_COMB (@lem1584906) (@lem1584905)). Qed.
Lemma lem1584908 : term22 = term22.
Proof. exact (MK_COMB (@lem1584907) (@lem1584885)). Qed.
Lemma lem1584971 : term11 = term22.
Proof. exact (TRANS (@lem1584855) (@lem1584908)). Qed.
Lemma lem1584972 : term22 = term11.
Proof. exact (SYM (@lem1584971)). Qed.
Lemma lem1584973 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1584974 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1584975 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1584986 (x : real) (y : real) (z : real) : (term39 x y z) = (term40 x y z).
Proof. exact (@lem17362 (term41 x y z) (term42 x y z)). Qed.
Lemma lem1584987 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1584988 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (@lem1584987 (term34 x y)). Qed.
Lemma lem1584989 (x : real) (y : real) (z : real) : (term47 x y z) = (term33 x y z).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem1584990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1584991 (x : real) (y : real) (z : real) : (term48 x y z) = (term39 x y z).
Proof. exact (MK_COMB (@lem1584990) (@lem1584989 x y z)). Qed.
Lemma lem1584992 (x : real) (y : real) (z : real) : (term48 x y z) = (term40 x y z).
Proof. exact (TRANS (@lem1584991 x y z) (@lem1584986 x y z)). Qed.
Lemma lem1584993 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : real => @lem1584992 x y z)). Qed.
Lemma lem1584994 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1584995 (x : real) (y : real) : (term46 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1584994) (@lem1584993 x y)). Qed.
Lemma lem1584996 (x : real) (y : real) : (term45 x y) = (term51 x y).
Proof. exact (TRANS (@lem1584988 x y) (@lem1584995 x y)). Qed.
Lemma lem1584997 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1584998 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1584997 (term36 x)). Qed.
Lemma lem1584999 (x : real) (y : real) : (term54 x y) = (term35 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1585000 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1585001 (x : real) (y : real) : (term55 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1585000) (@lem1584999 x y)). Qed.
Lemma lem1585002 (x : real) (y : real) : (term55 x y) = (term51 x y).
Proof. exact (TRANS (@lem1585001 x y) (@lem1584996 x y)). Qed.
Lemma lem1585003 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1585002 x y)). Qed.
Lemma lem1585004 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1585005 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1585004) (@lem1585003 x)). Qed.
Lemma lem1585006 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1584998 x) (@lem1585005 x)). Qed.
Lemma lem1585007 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1585008 : term10 = term59.
Proof. exact (@lem1585007 term38). Qed.
Lemma lem1585009 (x : real) : (term60 x) = (term37 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1585010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1585011 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1585010) (@lem1585009 x)). Qed.
Lemma lem1585012 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1585011 x) (@lem1585006 x)). Qed.
Lemma lem1585013 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1585012 x)). Qed.
Lemma lem1585014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1585015 : term59 = term64.
Proof. exact (MK_COMB (@lem1585014) (@lem1585013)). Qed.
Lemma lem1585076 : term10 = term64.
Proof. exact (TRANS (@lem1585008) (@lem1585015)). Qed.
Lemma lem1585077 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1585076) (@lem1584973 h1)). Qed.
Lemma lem1585084 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (term67 x) (real_lt y z)). Qed.
Lemma lem1585085 (y : real) (x : real) (z : real) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem1585086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1585087 (x : real) (y : real) (z : real) : (term69 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1585086) (@lem1585084 x y z)). Qed.
Lemma lem1585088 (y : real) (x : real) (z : real) : (term71 y x z) = (term72 y x z).
Proof. exact (MK_COMB (@lem1585087 x y z) (@lem1585085 y x z)). Qed.
Lemma lem1585089 (y : real) (x : real) (z : real) : (term26 y x z) = (term71 y x z).
Proof. exact (@lem17265 (term73 x y z) (term68 y x z)). Qed.
Lemma lem1585090 (y : real) (x : real) (z : real) : (term26 y x z) = (term72 y x z).
Proof. exact (TRANS (@lem1585089 y x z) (@lem1585088 y x z)). Qed.
Lemma lem1585091 (y : real) (x : real) : (term27 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1585090 y x z)). Qed.
Lemma lem1585092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585093 (y : real) (x : real) : (term28 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1585092) (@lem1585091 y x)). Qed.
Lemma lem1585094 (x : real) : (term29 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1585093 y x)). Qed.
Lemma lem1585095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585096 (x : real) : (term30 x) = (term77 x).
Proof. exact (MK_COMB (@lem1585095) (@lem1585094 x)). Qed.
Lemma lem1585097 : term31 = term78.
Proof. exact (fun_ext (fun x : real => @lem1585096 x)). Qed.
Lemma lem1585098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585159 : term32 = term79.
Proof. exact (MK_COMB (@lem1585098) (@lem1585097)). Qed.
Lemma lem1585160 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1585159) (@lem1584974 h1)). Qed.
Lemma lem1585161 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1585162 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1585161 y x)). Qed.
Lemma lem1585163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585164 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1585163) (@lem1585162 x)). Qed.
Lemma lem1585165 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1585164 x)). Qed.
Lemma lem1585166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585179 : term17 = term17.
Proof. exact (MK_COMB (@lem1585166) (@lem1585165)). Qed.
Lemma lem1585180 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1585179) (@lem1584975 h1)). Qed.
Lemma lem1585181 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1585182 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1585220 (y : real) (x : real) (z : real) : (term72 y x z) = (term72 y x z).
Proof. exact (eq_refl (term72 y x z)). Qed.
Lemma lem1585221 (y : real) (x : real) : (term74 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1585220 y x z)). Qed.
Lemma lem1585222 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585223 (y : real) (x : real) : (term75 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1585222) (@lem1585221 y x)). Qed.
Lemma lem1585224 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1585223 y x)). Qed.
Lemma lem1585225 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585226 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1585225) (@lem1585224 x)). Qed.
Lemma lem1585227 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1585226 x)). Qed.
Lemma lem1585228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585229 : term79 = term79.
Proof. exact (MK_COMB (@lem1585228) (@lem1585227)). Qed.
Lemma lem1585230 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1585229) (@lem1585160 h1)). Qed.
Lemma lem1585243 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1585244 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1585243 y x)). Qed.
Lemma lem1585245 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585246 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1585245) (@lem1585244 x)). Qed.
Lemma lem1585247 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1585246 x)). Qed.
Lemma lem1585248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585249 : term17 = term17.
Proof. exact (MK_COMB (@lem1585248) (@lem1585247)). Qed.
Lemma lem1585250 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1585249) (@lem1585180 h1)). Qed.
Lemma lem1585286 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term40 x y z.
Proof. exact (h1). Qed.
Lemma lem1585288 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term41 x y z.
Proof. exact (proj1 (@lem1585286 x y z h1)). Qed.
Lemma lem1585304 (y : real) (x : real) (z : real) : (term72 y x z) = (term72 y x z).
Proof. exact (eq_refl (term72 y x z)). Qed.
Lemma lem1585305 (y : real) (x : real) : (term74 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1585304 y x z)). Qed.
Lemma lem1585306 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585307 (y : real) (x : real) : (term75 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1585306) (@lem1585305 y x)). Qed.
Lemma lem1585308 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1585307 y x)). Qed.
Lemma lem1585309 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585310 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1585309) (@lem1585308 x)). Qed.
Lemma lem1585311 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1585310 x)). Qed.
Lemma lem1585312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585314 : term79 = term79.
Proof. exact (MK_COMB (@lem1585312) (@lem1585311)). Qed.
Lemma lem1585315 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1585314) (@lem1585230 h1)). Qed.
Lemma lem1585317 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1585318 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1585317 y x)). Qed.
Lemma lem1585319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585320 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1585319) (@lem1585318 x)). Qed.
Lemma lem1585321 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1585320 x)). Qed.
Lemma lem1585322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1585324 : term17 = term17.
Proof. exact (MK_COMB (@lem1585322) (@lem1585321)). Qed.
Lemma lem1585325 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1585324) (@lem1585250 h1)). Qed.
Lemma lem1585338 (_25026 : real) (h1 : term32) : term80 _25026.
Proof. exact (@lem1585315 h1 _25026). Qed.
Lemma lem1585339 (_25026 : real) : (term80 _25026) = (term77 _25026).
Proof. exact (eq_refl (term80 _25026)). Qed.
Lemma lem1585340 (_25026 : real) (h1 : term32) : term77 _25026.
Proof. exact (EQ_MP (@lem1585339 _25026) (@lem1585338 _25026 h1)). Qed.
Lemma lem1585341 (_25026 : real) (_25027 : real) (h1 : term32) : term81 _25026 _25027.
Proof. exact (@lem1585340 _25026 h1 _25027). Qed.
Lemma lem1585342 (_25027 : real) (_25026 : real) : (term81 _25026 _25027) = (term75 _25027 _25026).
Proof. exact (eq_refl (term81 _25026 _25027)). Qed.
Lemma lem1585343 (_25027 : real) (_25026 : real) (h1 : term32) : term75 _25027 _25026.
Proof. exact (EQ_MP (@lem1585342 _25027 _25026) (@lem1585341 _25026 _25027 h1)). Qed.
Lemma lem1585344 (_25027 : real) (_25026 : real) (_25028 : real) (h1 : term32) : term82 _25027 _25026 _25028.
Proof. exact (@lem1585343 _25027 _25026 h1 _25028). Qed.
Lemma lem1585345 (_25027 : real) (_25026 : real) (_25028 : real) : (term82 _25027 _25026 _25028) = (term72 _25027 _25026 _25028).
Proof. exact (eq_refl (term82 _25027 _25026 _25028)). Qed.
Lemma lem1585346 (_25027 : real) (_25026 : real) (_25028 : real) (h1 : term32) : term72 _25027 _25026 _25028.
Proof. exact (EQ_MP (@lem1585345 _25027 _25026 _25028) (@lem1585344 _25027 _25026 _25028 h1)). Qed.
Lemma lem1585347 (_25029 : real) (h1 : term17) : term83 _25029.
Proof. exact (@lem1585325 h1 _25029). Qed.
Lemma lem1585348 (_25029 : real) : (term83 _25029) = (term24 _25029).
Proof. exact (eq_refl (term83 _25029)). Qed.
Lemma lem1585349 (_25029 : real) (h1 : term17) : term24 _25029.
Proof. exact (EQ_MP (@lem1585348 _25029) (@lem1585347 _25029 h1)). Qed.
Lemma lem1585350 (_25029 : real) (_25030 : real) (h1 : term17) : term84 _25029 _25030.
Proof. exact (@lem1585349 _25029 h1 _25030). Qed.
Lemma lem1585351 (_25030 : real) (_25029 : real) : (term84 _25029 _25030) = ((real_mul _25029 _25030) = (real_mul _25030 _25029)).
Proof. exact (eq_refl (term84 _25029 _25030)). Qed.
Lemma lem1585363 (_25027 : real) (_25026 : real) (_25028 : real) : (term72 _25027 _25026 _25028) = (term85 _25027 _25026 _25028).
Proof. exact (@lem1584776 (term86 _25026) (term87 _25027 _25028) (term68 _25027 _25026 _25028)). Qed.
Lemma lem1585364 (_25027 : real) (_25026 : real) (_25028 : real) (h1 : term32) : term85 _25027 _25026 _25028.
Proof. exact (EQ_MP (@lem1585363 _25027 _25026 _25028) (@lem1585346 _25027 _25026 _25028 h1)). Qed.
Lemma lem1585368 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term88 x y z.
Proof. exact (proj2 (@lem1585286 x y z h1)). Qed.
Lemma lem1585373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1585374 (_25031 : real) (_25033 : real) (h1 : _25031 = _25033) : _25031 = _25033.
Proof. exact (h1). Qed.
Lemma lem1585375 (_25032 : real) (_25034 : real) (h1 : _25032 = _25034) : _25032 = _25034.
Proof. exact (h1). Qed.
Lemma lem1585376 (_25031 : real) (_25033 : real) (h1 : _25031 = _25033) : (real_lt _25031) = (real_lt _25033).
Proof. exact (MK_COMB (@lem1585373) (@lem1585374 _25031 _25033 h1)). Qed.
Lemma lem1585377 (_25031 : real) (_25033 : real) (_25032 : real) (_25034 : real) (h1 : _25031 = _25033) (h2 : _25032 = _25034) : (real_lt _25031 _25032) = (real_lt _25033 _25034).
Proof. exact (MK_COMB (@lem1585376 _25031 _25033 h1) (@lem1585375 _25032 _25034 h2)). Qed.
Lemma lem1585379 (b : Prop) (a : Prop) : term89 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1585380 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : term90 _25033 _25034 _25031 _25032.
Proof. exact (@lem1585379 (real_lt _25033 _25034) (real_lt _25031 _25032)). Qed.
Lemma lem1585381 (_25031 : real) (_25033 : real) (_25032 : real) (_25034 : real) (h1 : _25031 = _25033) (h2 : _25032 = _25034) : term91 _25033 _25034 _25031 _25032.
Proof. exact (@lem1585380 _25033 _25034 _25031 _25032 (@lem1585377 _25031 _25033 _25032 _25034 h1 h2)). Qed.
Lemma lem1585382 (_25034 : real) (_25032 : real) (_25031 : real) (_25033 : real) (h1 : _25031 = _25033) : term92 _25033 _25034 _25031 _25032.
Proof. exact (fun h0 : _25032 = _25034 => @lem1585381 _25031 _25033 _25032 _25034 h1 h0). Qed.
Lemma lem1585384 (a : Prop) (b : Prop) : (a -> b) = (term93 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1585385 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term92 _25033 _25034 _25031 _25032) = (term94 _25033 _25034 _25031 _25032).
Proof. exact (@lem1585384 (_25032 = _25034) (term91 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585386 (_25034 : real) (_25032 : real) (_25031 : real) (_25033 : real) (h1 : _25031 = _25033) : term94 _25033 _25034 _25031 _25032.
Proof. exact (EQ_MP (@lem1585385 _25033 _25034 _25031 _25032) (@lem1585382 _25034 _25032 _25031 _25033 h1)). Qed.
Lemma lem1585387 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : term95 _25033 _25034 _25031 _25032.
Proof. exact (fun h0 : _25031 = _25033 => @lem1585386 _25034 _25032 _25031 _25033 h0). Qed.
Lemma lem1585389 (a : Prop) (b : Prop) : (a -> b) = (term93 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1585390 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term95 _25033 _25034 _25031 _25032) = (term96 _25033 _25034 _25031 _25032).
Proof. exact (@lem1585389 (_25031 = _25033) (term94 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585391 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : term96 _25033 _25034 _25031 _25032.
Proof. exact (EQ_MP (@lem1585390 _25033 _25034 _25031 _25032) (@lem1585387 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585428 (_25030 : real) (_25029 : real) (h1 : term17) : (real_mul _25029 _25030) = (real_mul _25030 _25029).
Proof. exact (EQ_MP (@lem1585351 _25030 _25029) (@lem1585350 _25029 _25030 h1)). Qed.
Lemma lem1585429 (x : real) (z : real) (h1 : term17) : (real_mul z x) = (real_mul x z).
Proof. exact (@lem1585428 x z h1). Qed.
Lemma lem1585430 (x : real) (z : real) (h1 : term17) : term97 x z.
Proof. exact (fun h0 : term98 x z => @lem1585429 x z h1). Qed.
Lemma lem1585432 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585433 (x : real) (z : real) : (term97 x z) = ((real_mul z x) = (real_mul x z)).
Proof. exact (@lem1585432 ((real_mul z x) = (real_mul x z))). Qed.
Lemma lem1585434 (x : real) (z : real) (h1 : term17) : (real_mul z x) = (real_mul x z).
Proof. exact (EQ_MP (@lem1585433 x z) (@lem1585430 x z h1)). Qed.
Lemma lem1585436 (_25030 : real) (_25029 : real) (h1 : term17) : (real_mul _25029 _25030) = (real_mul _25030 _25029).
Proof. exact (EQ_MP (@lem1585351 _25030 _25029) (@lem1585350 _25029 _25030 h1)). Qed.
Lemma lem1585437 (y : real) (z : real) (h1 : term17) : (real_mul z y) = (real_mul y z).
Proof. exact (@lem1585436 y z h1). Qed.
Lemma lem1585438 (y : real) (z : real) (h1 : term17) : term97 y z.
Proof. exact (fun h0 : term98 y z => @lem1585437 y z h1). Qed.
Lemma lem1585440 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585441 (y : real) (z : real) : (term97 y z) = ((real_mul z y) = (real_mul y z)).
Proof. exact (@lem1585440 ((real_mul z y) = (real_mul y z))). Qed.
Lemma lem1585442 (y : real) (z : real) (h1 : term17) : (real_mul z y) = (real_mul y z).
Proof. exact (EQ_MP (@lem1585441 y z) (@lem1585438 y z h1)). Qed.
Lemma lem1585444 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term67 z.
Proof. exact (proj2 (@lem1585288 x y z h1)). Qed.
Lemma lem1585445 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term100 z.
Proof. exact (fun h0 : term86 z => @lem1585444 x y z h1). Qed.
Lemma lem1585447 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585448 (z : real) : (term100 z) = (term67 z).
Proof. exact (@lem1585447 (term67 z)). Qed.
Lemma lem1585449 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term67 z.
Proof. exact (EQ_MP (@lem1585448 z) (@lem1585445 x y z h1)). Qed.
Lemma lem1585451 (x : real) (y : real) (z : real) (h1 : term40 x y z) : real_lt x y.
Proof. exact (proj1 (@lem1585288 x y z h1)). Qed.
Lemma lem1585452 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term101 x y.
Proof. exact (fun h0 : term87 x y => @lem1585451 x y z h1). Qed.
Lemma lem1585454 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585455 (x : real) (y : real) : (term101 x y) = (real_lt x y).
Proof. exact (@lem1585454 (real_lt x y)). Qed.
Lemma lem1585456 (x : real) (y : real) (z : real) (h1 : term40 x y z) : real_lt x y.
Proof. exact (EQ_MP (@lem1585455 x y) (@lem1585452 x y z h1)). Qed.
Lemma lem1585462 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1585463 (_25027 : real) (_25026 : real) (_25028 : real) : (term85 _25027 _25026 _25028) = (term102 _25027 _25026 _25028).
Proof. exact (@lem1585462 (term87 _25027 _25028) (term86 _25026) (term68 _25027 _25026 _25028)). Qed.
Lemma lem1585477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1585478 (_25027 : real) (_25028 : real) (_25026 : real) : (term103 _25027 _25026 _25028) = (term104 _25027 _25028 _25026).
Proof. exact (@lem1585477 (term68 _25027 _25026 _25028) (term86 _25026)). Qed.
Lemma lem1585484 (_25027 : real) (_25028 : real) : (term105 _25027 _25028) = (term105 _25027 _25028).
Proof. exact (eq_refl (term105 _25027 _25028)). Qed.
Lemma lem1585485 (_25027 : real) (_25028 : real) (_25026 : real) : (term102 _25027 _25026 _25028) = (term106 _25027 _25028 _25026).
Proof. exact (MK_COMB (@lem1585484 _25027 _25028) (@lem1585478 _25027 _25028 _25026)). Qed.
Lemma lem1585489 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1585490 (_25027 : real) (_25028 : real) (_25026 : real) : (term106 _25027 _25028 _25026) = (term107 _25027 _25028 _25026).
Proof. exact (@lem1585489 (term68 _25027 _25026 _25028) (term87 _25027 _25028) (term86 _25026)). Qed.
Lemma lem1585506 (_25027 : real) (_25028 : real) (_25026 : real) : (term102 _25027 _25026 _25028) = (term107 _25027 _25028 _25026).
Proof. exact (TRANS (@lem1585485 _25027 _25028 _25026) (@lem1585490 _25027 _25028 _25026)). Qed.
Lemma lem1585507 (_25027 : real) (_25028 : real) (_25026 : real) : (term85 _25027 _25026 _25028) = (term107 _25027 _25028 _25026).
Proof. exact (TRANS (@lem1585463 _25027 _25026 _25028) (@lem1585506 _25027 _25028 _25026)). Qed.
Lemma lem1585508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1585509 (_25027 : real) (_25028 : real) (_25026 : real) : (term108 _25027 _25026 _25028) = (term109 _25027 _25028 _25026).
Proof. exact (MK_COMB (@lem1585508) (@lem1585507 _25027 _25028 _25026)). Qed.
Lemma lem1585523 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1585524 (_25027 : real) (_25028 : real) (_25026 : real) : (term66 _25026 _25027 _25028) = (term110 _25027 _25028 _25026).
Proof. exact (@lem1585523 (term87 _25027 _25028) (term86 _25026)). Qed.
Lemma lem1585530 (_25027 : real) (_25026 : real) (_25028 : real) : (term111 _25027 _25026 _25028) = (term111 _25027 _25026 _25028).
Proof. exact (eq_refl (term111 _25027 _25026 _25028)). Qed.
Lemma lem1585531 (_25027 : real) (_25028 : real) (_25026 : real) : (term112 _25026 _25027 _25028) = (term107 _25027 _25028 _25026).
Proof. exact (MK_COMB (@lem1585530 _25027 _25026 _25028) (@lem1585524 _25027 _25028 _25026)). Qed.
Lemma lem1585542 (_25027 : real) (_25028 : real) (_25026 : real) : ((term85 _25027 _25026 _25028) = (term112 _25026 _25027 _25028)) = ((term107 _25027 _25028 _25026) = (term107 _25027 _25028 _25026)).
Proof. exact (MK_COMB (@lem1585509 _25027 _25028 _25026) (@lem1585531 _25027 _25028 _25026)). Qed.
Lemma lem1585544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1585545 (x : Prop) : (x = x) = True.
Proof. exact (@lem1585544 Prop x). Qed.
Lemma lem1585546 (_25027 : real) (_25028 : real) (_25026 : real) : ((term107 _25027 _25028 _25026) = (term107 _25027 _25028 _25026)) = True.
Proof. exact (@lem1585545 (term107 _25027 _25028 _25026)). Qed.
Lemma lem1585547 (_25026 : real) (_25027 : real) (_25028 : real) : ((term85 _25027 _25026 _25028) = (term112 _25026 _25027 _25028)) = True.
Proof. exact (TRANS (@lem1585542 _25027 _25028 _25026) (@lem1585546 _25027 _25028 _25026)). Qed.
Lemma lem1585548 (_25026 : real) (_25027 : real) (_25028 : real) : True = ((term85 _25027 _25026 _25028) = (term112 _25026 _25027 _25028)).
Proof. exact (SYM (@lem1585547 _25026 _25027 _25028)). Qed.
Lemma lem1585549 (_25026 : real) (_25027 : real) (_25028 : real) : (term85 _25027 _25026 _25028) = (term112 _25026 _25027 _25028).
Proof. exact (EQ_MP (@lem1585548 _25026 _25027 _25028) (@lem0)). Qed.
Lemma lem1585550 (_25026 : real) (_25027 : real) (_25028 : real) (h1 : term32) : term112 _25026 _25027 _25028.
Proof. exact (EQ_MP (@lem1585549 _25026 _25027 _25028) (@lem1585364 _25027 _25026 _25028 h1)). Qed.
Lemma lem1585552 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1585553 (_25027 : real) (_25026 : real) (_25028 : real) : (term112 _25026 _25027 _25028) = (term114 _25027 _25026 _25028).
Proof. exact (@lem1585552 (term66 _25026 _25027 _25028) (term68 _25027 _25026 _25028)). Qed.
Lemma lem1585555 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1585556 (_25026 : real) (_25027 : real) (_25028 : real) : (term117 _25026 _25027 _25028) = (term118 _25026 _25027 _25028).
Proof. exact (@lem1585555 (term86 _25026) (term87 _25027 _25028)). Qed.
Lemma lem1585558 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1585559 (_25026 : real) : (term120 _25026) = (term67 _25026).
Proof. exact (@lem1585558 (term67 _25026)). Qed.
Lemma lem1585560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1585561 (_25026 : real) : (term121 _25026) = (term122 _25026).
Proof. exact (MK_COMB (@lem1585560) (@lem1585559 _25026)). Qed.
Lemma lem1585563 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1585564 (_25027 : real) (_25028 : real) : (term123 _25027 _25028) = (real_lt _25027 _25028).
Proof. exact (@lem1585563 (real_lt _25027 _25028)). Qed.
Lemma lem1585565 (_25026 : real) (_25027 : real) (_25028 : real) : (term118 _25026 _25027 _25028) = (term73 _25026 _25027 _25028).
Proof. exact (MK_COMB (@lem1585561 _25026) (@lem1585564 _25027 _25028)). Qed.
Lemma lem1585566 (_25026 : real) (_25027 : real) (_25028 : real) : (term117 _25026 _25027 _25028) = (term73 _25026 _25027 _25028).
Proof. exact (TRANS (@lem1585556 _25026 _25027 _25028) (@lem1585565 _25026 _25027 _25028)). Qed.
Lemma lem1585567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1585568 (_25026 : real) (_25027 : real) (_25028 : real) : (term124 _25026 _25027 _25028) = (term125 _25026 _25027 _25028).
Proof. exact (MK_COMB (@lem1585567) (@lem1585566 _25026 _25027 _25028)). Qed.
Lemma lem1585569 (_25027 : real) (_25026 : real) (_25028 : real) : (term68 _25027 _25026 _25028) = (term68 _25027 _25026 _25028).
Proof. exact (eq_refl (term68 _25027 _25026 _25028)). Qed.
Lemma lem1585570 (_25027 : real) (_25026 : real) (_25028 : real) : (term114 _25027 _25026 _25028) = (term26 _25027 _25026 _25028).
Proof. exact (MK_COMB (@lem1585568 _25026 _25027 _25028) (@lem1585569 _25027 _25026 _25028)). Qed.
Lemma lem1585571 (_25027 : real) (_25026 : real) (_25028 : real) : (term112 _25026 _25027 _25028) = (term26 _25027 _25026 _25028).
Proof. exact (TRANS (@lem1585553 _25027 _25026 _25028) (@lem1585570 _25027 _25026 _25028)). Qed.
Lemma lem1585573 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term73 z x y.
Proof. exact (conj (@lem1585449 x y z h1) (@lem1585456 x y z h1)). Qed.
Lemma lem1585575 (_25027 : real) (_25026 : real) (_25028 : real) (h1 : term32) : term26 _25027 _25026 _25028.
Proof. exact (EQ_MP (@lem1585571 _25027 _25026 _25028) (@lem1585550 _25026 _25027 _25028 h1)). Qed.
Lemma lem1585576 (x : real) (z : real) (y : real) (h1 : term32) : term26 x z y.
Proof. exact (@lem1585575 x z y h1). Qed.
Lemma lem1585579 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term68 x z y.
Proof. exact (@lem1585576 x z y h1 (@lem1585573 x y z h2)). Qed.
Lemma lem1585580 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term126 x z y.
Proof. exact (fun h0 : term127 x z y => @lem1585579 x y z h1 h2). Qed.
Lemma lem1585582 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585583 (x : real) (z : real) (y : real) : (term126 x z y) = (term68 x z y).
Proof. exact (@lem1585582 (term68 x z y)). Qed.
Lemma lem1585584 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term68 x z y.
Proof. exact (EQ_MP (@lem1585583 x z y) (@lem1585580 x y z h1 h2)). Qed.
Lemma lem1585602 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1585603 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term94 _25033 _25034 _25031 _25032) = (term128 _25033 _25034 _25031 _25032).
Proof. exact (@lem1585602 (real_lt _25033 _25034) (term129 _25032 _25034) (term87 _25031 _25032)). Qed.
Lemma lem1585621 (_25031 : real) (_25033 : real) : (term130 _25031 _25033) = (term130 _25031 _25033).
Proof. exact (eq_refl (term130 _25031 _25033)). Qed.
Lemma lem1585622 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term96 _25033 _25034 _25031 _25032) = (term131 _25033 _25034 _25031 _25032).
Proof. exact (MK_COMB (@lem1585621 _25031 _25033) (@lem1585603 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585626 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1585627 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term131 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032).
Proof. exact (@lem1585626 (real_lt _25033 _25034) (term129 _25031 _25033) (term133 _25034 _25031 _25032)). Qed.
Lemma lem1585657 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term96 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032).
Proof. exact (TRANS (@lem1585622 _25033 _25034 _25031 _25032) (@lem1585627 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1585659 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term134 _25033 _25034 _25031 _25032) = (term135 _25033 _25034 _25031 _25032).
Proof. exact (MK_COMB (@lem1585658) (@lem1585657 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585689 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term132 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032).
Proof. exact (eq_refl (term132 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585690 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : ((term96 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032)) = ((term132 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032)).
Proof. exact (MK_COMB (@lem1585659 _25033 _25034 _25031 _25032) (@lem1585689 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585692 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1585693 (x : Prop) : (x = x) = True.
Proof. exact (@lem1585692 Prop x). Qed.
Lemma lem1585694 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : ((term132 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032)) = True.
Proof. exact (@lem1585693 (term132 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585695 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : ((term96 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032)) = True.
Proof. exact (TRANS (@lem1585690 _25033 _25034 _25031 _25032) (@lem1585694 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585696 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : True = ((term96 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032)).
Proof. exact (SYM (@lem1585695 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585697 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term96 _25033 _25034 _25031 _25032) = (term132 _25033 _25034 _25031 _25032).
Proof. exact (EQ_MP (@lem1585696 _25033 _25034 _25031 _25032) (@lem0)). Qed.
Lemma lem1585698 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : term132 _25033 _25034 _25031 _25032.
Proof. exact (EQ_MP (@lem1585697 _25033 _25034 _25031 _25032) (@lem1585391 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585700 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1585701 (_25031 : real) (_25032 : real) (_25033 : real) (_25034 : real) : (term132 _25033 _25034 _25031 _25032) = (term136 _25031 _25032 _25033 _25034).
Proof. exact (@lem1585700 (term137 _25033 _25034 _25031 _25032) (real_lt _25033 _25034)). Qed.
Lemma lem1585703 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1585704 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term138 _25033 _25034 _25031 _25032) = (term139 _25033 _25034 _25031 _25032).
Proof. exact (@lem1585703 (term129 _25031 _25033) (term133 _25034 _25031 _25032)). Qed.
Lemma lem1585706 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1585707 (_25031 : real) (_25033 : real) : (term140 _25031 _25033) = (_25031 = _25033).
Proof. exact (@lem1585706 (_25031 = _25033)). Qed.
Lemma lem1585708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1585709 (_25031 : real) (_25033 : real) : (term141 _25031 _25033) = (term142 _25031 _25033).
Proof. exact (MK_COMB (@lem1585708) (@lem1585707 _25031 _25033)). Qed.
Lemma lem1585711 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1585712 (_25034 : real) (_25031 : real) (_25032 : real) : (term143 _25034 _25031 _25032) = (term144 _25034 _25031 _25032).
Proof. exact (@lem1585711 (term129 _25032 _25034) (term87 _25031 _25032)). Qed.
Lemma lem1585714 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1585715 (_25032 : real) (_25034 : real) : (term140 _25032 _25034) = (_25032 = _25034).
Proof. exact (@lem1585714 (_25032 = _25034)). Qed.
Lemma lem1585716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1585717 (_25032 : real) (_25034 : real) : (term141 _25032 _25034) = (term142 _25032 _25034).
Proof. exact (MK_COMB (@lem1585716) (@lem1585715 _25032 _25034)). Qed.
Lemma lem1585719 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1585720 (_25031 : real) (_25032 : real) : (term123 _25031 _25032) = (real_lt _25031 _25032).
Proof. exact (@lem1585719 (real_lt _25031 _25032)). Qed.
Lemma lem1585721 (_25034 : real) (_25031 : real) (_25032 : real) : (term144 _25034 _25031 _25032) = (term145 _25034 _25031 _25032).
Proof. exact (MK_COMB (@lem1585717 _25032 _25034) (@lem1585720 _25031 _25032)). Qed.
Lemma lem1585722 (_25034 : real) (_25031 : real) (_25032 : real) : (term143 _25034 _25031 _25032) = (term145 _25034 _25031 _25032).
Proof. exact (TRANS (@lem1585712 _25034 _25031 _25032) (@lem1585721 _25034 _25031 _25032)). Qed.
Lemma lem1585723 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term139 _25033 _25034 _25031 _25032) = (term146 _25033 _25034 _25031 _25032).
Proof. exact (MK_COMB (@lem1585709 _25031 _25033) (@lem1585722 _25034 _25031 _25032)). Qed.
Lemma lem1585724 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term138 _25033 _25034 _25031 _25032) = (term146 _25033 _25034 _25031 _25032).
Proof. exact (TRANS (@lem1585704 _25033 _25034 _25031 _25032) (@lem1585723 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1585726 (_25033 : real) (_25034 : real) (_25031 : real) (_25032 : real) : (term147 _25033 _25034 _25031 _25032) = (term148 _25033 _25034 _25031 _25032).
Proof. exact (MK_COMB (@lem1585725) (@lem1585724 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585727 (_25033 : real) (_25034 : real) : (real_lt _25033 _25034) = (real_lt _25033 _25034).
Proof. exact (eq_refl (real_lt _25033 _25034)). Qed.
Lemma lem1585728 (_25031 : real) (_25032 : real) (_25033 : real) (_25034 : real) : (term136 _25031 _25032 _25033 _25034) = (term149 _25031 _25032 _25033 _25034).
Proof. exact (MK_COMB (@lem1585726 _25033 _25034 _25031 _25032) (@lem1585727 _25033 _25034)). Qed.
Lemma lem1585729 (_25031 : real) (_25032 : real) (_25033 : real) (_25034 : real) : (term132 _25033 _25034 _25031 _25032) = (term149 _25031 _25032 _25033 _25034).
Proof. exact (TRANS (@lem1585701 _25031 _25032 _25033 _25034) (@lem1585728 _25031 _25032 _25033 _25034)). Qed.
Lemma lem1585731 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term150 x z y.
Proof. exact (conj (@lem1585442 y z h2) (@lem1585584 x y z h1 h3)). Qed.
Lemma lem1585732 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term151 x z y.
Proof. exact (conj (@lem1585434 x z h2) (@lem1585731 x y z h1 h2 h3)). Qed.
Lemma lem1585734 (_25031 : real) (_25032 : real) (_25033 : real) (_25034 : real) : term149 _25031 _25032 _25033 _25034.
Proof. exact (EQ_MP (@lem1585729 _25031 _25032 _25033 _25034) (@lem1585698 _25033 _25034 _25031 _25032)). Qed.
Lemma lem1585735 (x : real) (y : real) (z : real) : term152 x y z.
Proof. exact (@lem1585734 (real_mul z x) (real_mul z y) (real_mul x z) (real_mul y z)). Qed.
Lemma lem1585738 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term42 x y z.
Proof. exact (@lem1585735 x y z (@lem1585732 x y z h1 h2 h3)). Qed.
Lemma lem1585739 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term153 x y z.
Proof. exact (fun h0 : term88 x y z => @lem1585738 x y z h1 h2 h3). Qed.
Lemma lem1585741 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585742 (x : real) (y : real) (z : real) : (term153 x y z) = (term42 x y z).
Proof. exact (@lem1585741 (term42 x y z)). Qed.
Lemma lem1585743 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term42 x y z.
Proof. exact (EQ_MP (@lem1585742 x y z) (@lem1585739 x y z h1 h2 h3)). Qed.
Lemma lem1585746 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1585748 (x : real) (y : real) (z : real) : (term88 x y z) = (term154 x y z).
Proof. exact (@lem1585746 (term42 x y z)). Qed.
Lemma lem1585751 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term154 x y z.
Proof. exact (EQ_MP (@lem1585748 x y z) (@lem1585368 x y z h1)). Qed.
Lemma lem1585754 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (@lem1585751 x y z h3 (@lem1585743 x y z h1 h2 h3)). Qed.
Lemma lem1585755 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term155.
Proof. exact (fun h0 : ~ False => @lem1585754 x y z h1 h2 h3). Qed.
Lemma lem1585757 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1585758 : term155 = False.
Proof. exact (@lem1585757 False). Qed.
Lemma lem1585759 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1585758) (@lem1585755 x y z h1 h2 h3)). Qed.
Lemma lem1585760 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1585759 x y z h1 h2 h3) (fun h4 : False => @lem1585325 h2)). Qed.
Lemma lem1585761 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1585760 x y z h1 h2 h3) (@lem1585325 h2)). Qed.
Lemma lem1585762 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1585761 x y z h1 h2 h3) (fun h4 : False => @lem1585286 x y z h3)). Qed.
Lemma lem1585763 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1585762 x y z h1 h2 h3) (@lem1585286 x y z h3)). Qed.
Lemma lem1585764 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1585763 x y z h1 h2 h3) (fun h4 : False => @lem1585250 h2)). Qed.
Lemma lem1585765 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1585764 x y z h1 h2 h3) (@lem1585250 h2)). Qed.
Lemma lem1585766 (x : real) (y : real) (h1 : term32) (h2 : term17) (h3 : term51 x y) : False.
Proof. exact (ex_elim (@lem1585182 x y h3) (fun z : real => fun h0 : term50 x y z => @lem1585765 x y z h1 h2 h0)). Qed.
Lemma lem1585767 (x : real) (h1 : term32) (h2 : term17) (h3 : term58 x) : False.
Proof. exact (ex_elim (@lem1585181 x h3) (fun y : real => fun h0 : term57 x y => @lem1585766 x y h1 h2 h0)). Qed.
Lemma lem1585768 (h1 : term32) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1585077 h3) (fun x : real => fun h0 : term63 x => @lem1585767 x h1 h2 h0)). Qed.
Lemma lem1585769 (h1 : term32) (h2 : term17) (h3 : term10) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1585768 h1 h2 h3) (fun h4 : False => @lem1585180 h2)). Qed.
Lemma lem1585770 (h1 : term32) (h2 : term17) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem1585769 h1 h2 h3) (@lem1585180 h2)). Qed.
Lemma lem1585771 (h1 : term32) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1585770 h1 h0 h2). Qed.
Lemma lem1585772 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1585773 (h1 : term32) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1585772) (@lem1585771 h1 h2)). Qed.
Lemma lem1585774 (h1 : term10) : term20.
Proof. exact (fun h0 : term32 => @lem1585773 h0 h1). Qed.
Lemma lem1585775 : term22.
Proof. exact (fun h0 : term10 => @lem1585774 h0). Qed.
Lemma lem1585776 : term11.
Proof. exact (EQ_MP (@lem1584972) (@lem1585775)). Qed.
Lemma lem1585778 : term11.
Proof. exact (@lem1584796 (@lem1585776)). Qed.
Lemma lem1585779 (h1 : term10) : term19.
Proof. exact (@lem1585778 (@lem1584781 h1)). Qed.
Lemma lem1585780 (h1 : term10) : term15.
Proof. exact (@lem1585779 h1 (@lem1584766)). Qed.
Lemma lem1585781 (h1 : term10) : False.
Proof. exact (@lem1585780 h1 (@lem1338712)). Qed.
Lemma lem1585782 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1585781 h1) (fun h2 : False => @lem1584781 h1)). Qed.
Lemma lem1585783 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1585782 h1) (@lem1584781 h1)). Qed.
Lemma lem1585784 : term9.
Proof. exact (fun h0 : term10 => @lem1585783 h0). Qed.
Lemma lem1585785 : term8.
Proof. exact (EQ_MP (@lem1584780) (@lem1585784)). Qed.
