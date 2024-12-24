Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_WLOG_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LT_TOTAL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1864831 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1864832 (P : type1626) : (term1 P) = (term2 P).
Proof. exact (@lem1864831 (term1 P)). Qed.
Lemma lem1864833 (P : type1626) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem1864832 P)). Qed.
Lemma lem1864834 (P : type1626) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1864837 (P : type1626) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1864838 (P : type1626) : term5 P.
Proof. exact (fun h0 : term4 P => @lem1864837 P h0). Qed.
Lemma lem1864839 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1864840 (P : type1626) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1864841 (P : type1626) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem1864839 P h2 (@lem1864840 P h1)). Qed.
Lemma lem1864842 (P : type1626) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem1864841 P h1 h0). Qed.
Lemma lem1864843 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1864844 (P : type1626) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem1864842 P h1 (@lem1864843 P h2)). Qed.
Lemma lem1864845 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem1864844 P h0 h1). Qed.
Lemma lem1864846 (P : type1626) : term7 P.
Proof. exact (fun h0 : term5 P => @lem1864845 P h0). Qed.
Lemma lem1864849 (P : type1626) : term5 P.
Proof. exact (@lem1864846 P (@lem1864838 P)). Qed.
Lemma lem1864893 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1864894 : term8 = term9.
Proof. exact (@lem1864893 term10). Qed.
Lemma lem1864951 (P : type1626) : (term11 P) = (term11 P).
Proof. exact (eq_refl (term11 P)). Qed.
Lemma lem1864952 (P : type1626) : (term4 P) = (term12 P).
Proof. exact (MK_COMB (@lem1864951 P) (@lem1864894)). Qed.
Lemma lem1864955 : term13 = term14.
Proof. exact (fun_ext (fun P : type1626 => @lem1864952 P)). Qed.
Lemma lem1864956 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem1864965 : term15 = term16.
Proof. exact (MK_COMB (@lem1864956) (@lem1864955)). Qed.
Lemma lem1864974 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1864975 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1864974 y x)). Qed.
Lemma lem1864976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864977 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1864976) (@lem1864975 x)). Qed.
Lemma lem1864978 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1864977 x)). Qed.
Lemma lem1864979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864980 : term10 = term10.
Proof. exact (MK_COMB (@lem1864979) (@lem1864978)). Qed.
Lemma lem1864981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1864982 : term9 = term9.
Proof. exact (MK_COMB (@lem1864981) (@lem1864980)). Qed.
Lemma lem1864983 (P : type1626) (x : real) (y : real) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1864984 (P : type1626) (x : real) : (term21 P x) = (term21 P x).
Proof. exact (fun_ext (fun y : real => @lem1864983 P x y)). Qed.
Lemma lem1864985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864986 (P : type1626) (x : real) : (term22 P x) = (term22 P x).
Proof. exact (MK_COMB (@lem1864985) (@lem1864984 P x)). Qed.
Lemma lem1864987 (P : type1626) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun x : real => @lem1864986 P x)). Qed.
Lemma lem1864988 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864989 (P : type1626) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem1864988) (@lem1864987 P)). Qed.
Lemma lem1864994 (P : type1626) (x : real) (y : real) : (term25 P x y) = (term25 P x y).
Proof. exact (eq_refl (term25 P x y)). Qed.
Lemma lem1864995 (P : type1626) (x : real) : (term26 P x) = (term26 P x).
Proof. exact (fun_ext (fun y : real => @lem1864994 P x y)). Qed.
Lemma lem1864996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864997 (P : type1626) (x : real) : (term27 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem1864996) (@lem1864995 P x)). Qed.
Lemma lem1864998 (P : type1626) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun x : real => @lem1864997 P x)). Qed.
Lemma lem1864999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865000 (P : type1626) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem1864999) (@lem1864998 P)). Qed.
Lemma lem1865005 (P : type1626) (y : real) (x : real) : ((P x y) = (P y x)) = ((P x y) = (P y x)).
Proof. exact (eq_refl ((P x y) = (P y x))). Qed.
Lemma lem1865006 (P : type1626) (x : real) : (term30 P x) = (term30 P x).
Proof. exact (fun_ext (fun y : real => @lem1865005 P y x)). Qed.
Lemma lem1865007 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865008 (P : type1626) (x : real) : (term31 P x) = (term31 P x).
Proof. exact (MK_COMB (@lem1865007) (@lem1865006 P x)). Qed.
Lemma lem1865009 (P : type1626) : (term32 P) = (term32 P).
Proof. exact (fun_ext (fun x : real => @lem1865008 P x)). Qed.
Lemma lem1865010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865011 (P : type1626) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem1865010) (@lem1865009 P)). Qed.
Lemma lem1865012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865013 (P : type1626) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem1865012) (@lem1865011 P)). Qed.
Lemma lem1865014 (P : type1626) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem1865013 P) (@lem1865000 P)). Qed.
Lemma lem1865015 (P : type1626) (x : real) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem1865016 (P : type1626) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : real => @lem1865015 P x)). Qed.
Lemma lem1865017 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865018 (P : type1626) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem1865017) (@lem1865016 P)). Qed.
Lemma lem1865019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865020 (P : type1626) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem1865019) (@lem1865018 P)). Qed.
Lemma lem1865021 (P : type1626) : (term39 P) = (term39 P).
Proof. exact (MK_COMB (@lem1865020 P) (@lem1865014 P)). Qed.
Lemma lem1865022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1865023 (P : type1626) : (term40 P) = (term40 P).
Proof. exact (MK_COMB (@lem1865022) (@lem1865021 P)). Qed.
Lemma lem1865024 (P : type1626) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem1865023 P) (@lem1864989 P)). Qed.
Lemma lem1865025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1865026 (P : type1626) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem1865025) (@lem1865024 P)). Qed.
Lemma lem1865027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1865028 (P : type1626) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem1865027) (@lem1865026 P)). Qed.
Lemma lem1865029 (P : type1626) : (term12 P) = (term12 P).
Proof. exact (MK_COMB (@lem1865028 P) (@lem1864982)). Qed.
Lemma lem1865030 : term14 = term14.
Proof. exact (fun_ext (fun P : type1626 => @lem1865029 P)). Qed.
Lemma lem1865031 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem1865032 : term16 = term16.
Proof. exact (MK_COMB (@lem1865031) (@lem1865030)). Qed.
Lemma lem1865109 : term15 = term16.
Proof. exact (TRANS (@lem1864965) (@lem1865032)). Qed.
Lemma lem1865110 : term16 = term15.
Proof. exact (SYM (@lem1865109)). Qed.
Lemma lem1865111 (P : type1626) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1865112 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1865113 (P : type1626) (x : real) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem1865114 (P : type1626) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : real => @lem1865113 P x)). Qed.
Lemma lem1865115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865116 (P : type1626) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem1865115) (@lem1865114 P)). Qed.
Lemma lem1865131 (P : type1626) (y : real) (x : real) : ((P x y) = (P y x)) = (term41 P y x).
Proof. exact (@lem17784 (P x y) (P y x)). Qed.
Lemma lem1865132 (P : type1626) (x : real) : (term30 P x) = (term42 P x).
Proof. exact (fun_ext (fun y : real => @lem1865131 P y x)). Qed.
Lemma lem1865133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865134 (P : type1626) (x : real) : (term31 P x) = (term43 P x).
Proof. exact (MK_COMB (@lem1865133) (@lem1865132 P x)). Qed.
Lemma lem1865135 (P : type1626) : (term32 P) = (term44 P).
Proof. exact (fun_ext (fun x : real => @lem1865134 P x)). Qed.
Lemma lem1865136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865137 (P : type1626) : (term33 P) = (term45 P).
Proof. exact (MK_COMB (@lem1865136) (@lem1865135 P)). Qed.
Lemma lem1865144 (P : type1626) (x : real) (y : real) : (term25 P x y) = (term46 P x y).
Proof. exact (@lem17265 (real_lt x y) (P x y)). Qed.
Lemma lem1865145 (P : type1626) (x : real) : (term26 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : real => @lem1865144 P x y)). Qed.
Lemma lem1865146 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865147 (P : type1626) (x : real) : (term27 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem1865146) (@lem1865145 P x)). Qed.
Lemma lem1865148 (P : type1626) : (term28 P) = (term49 P).
Proof. exact (fun_ext (fun x : real => @lem1865147 P x)). Qed.
Lemma lem1865149 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865150 (P : type1626) : (term29 P) = (term50 P).
Proof. exact (MK_COMB (@lem1865149) (@lem1865148 P)). Qed.
Lemma lem1865151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865152 (P : type1626) : (term34 P) = (term51 P).
Proof. exact (MK_COMB (@lem1865151) (@lem1865137 P)). Qed.
Lemma lem1865153 (P : type1626) : (term35 P) = (term52 P).
Proof. exact (MK_COMB (@lem1865152 P) (@lem1865150 P)). Qed.
Lemma lem1865154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865155 (P : type1626) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem1865154) (@lem1865116 P)). Qed.
Lemma lem1865156 (P : type1626) : (term39 P) = (term53 P).
Proof. exact (MK_COMB (@lem1865155 P) (@lem1865153 P)). Qed.
Lemma lem1865158 (P : real -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1865159 (P : type1626) (x : real) : (term56 P x) = (term57 P x).
Proof. exact (@lem1865158 (term21 P x)). Qed.
Lemma lem1865160 (P : type1626) (x : real) (y : real) : (term58 P x y) = (P x y).
Proof. exact (eq_refl (term58 P x y)). Qed.
Lemma lem1865161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1865163 (P : type1626) (x : real) (y : real) : (term59 P x y) = (term60 P x y).
Proof. exact (MK_COMB (@lem1865161) (@lem1865160 P x y)). Qed.
Lemma lem1865164 (P : type1626) (x : real) : (term61 P x) = (term62 P x).
Proof. exact (fun_ext (fun y : real => @lem1865163 P x y)). Qed.
Lemma lem1865165 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865166 (P : type1626) (x : real) : (term57 P x) = (term63 P x).
Proof. exact (MK_COMB (@lem1865165) (@lem1865164 P x)). Qed.
Lemma lem1865167 (P : type1626) (x : real) : (term56 P x) = (term63 P x).
Proof. exact (TRANS (@lem1865159 P x) (@lem1865166 P x)). Qed.
Lemma lem1865168 (P : real -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1865169 (P : type1626) : (term64 P) = (term65 P).
Proof. exact (@lem1865168 (term23 P)). Qed.
Lemma lem1865170 (P : type1626) (x : real) : (term66 P x) = (term22 P x).
Proof. exact (eq_refl (term66 P x)). Qed.
Lemma lem1865171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1865172 (P : type1626) (x : real) : (term67 P x) = (term56 P x).
Proof. exact (MK_COMB (@lem1865171) (@lem1865170 P x)). Qed.
Lemma lem1865173 (P : type1626) (x : real) : (term67 P x) = (term63 P x).
Proof. exact (TRANS (@lem1865172 P x) (@lem1865167 P x)). Qed.
Lemma lem1865174 (P : type1626) : (term68 P) = (term69 P).
Proof. exact (fun_ext (fun x : real => @lem1865173 P x)). Qed.
Lemma lem1865175 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865176 (P : type1626) : (term65 P) = (term70 P).
Proof. exact (MK_COMB (@lem1865175) (@lem1865174 P)). Qed.
Lemma lem1865177 (P : type1626) : (term64 P) = (term70 P).
Proof. exact (TRANS (@lem1865169 P) (@lem1865176 P)). Qed.
Lemma lem1865178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865179 (P : type1626) : (term71 P) = (term72 P).
Proof. exact (MK_COMB (@lem1865178) (@lem1865156 P)). Qed.
Lemma lem1865180 (P : type1626) : (term73 P) = (term74 P).
Proof. exact (MK_COMB (@lem1865179 P) (@lem1865177 P)). Qed.
Lemma lem1865181 (P : type1626) : (term3 P) = (term73 P).
Proof. exact (@lem17362 (term39 P) (term24 P)). Qed.
Lemma lem1865182 (P : type1626) : (term3 P) = (term74 P).
Proof. exact (TRANS (@lem1865181 P) (@lem1865180 P)). Qed.
Lemma lem1865192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1865193 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem1865192 real P Q). Qed.
Lemma lem1865194 (P : type1626) (x : real) : (term79 P x) = (term80 P x).
Proof. exact (@lem1865193 (term81 P x) (term82 P x)). Qed.
Lemma lem1865195 (P : type1626) (y : real) (x : real) : (term83 P x y) = (term84 P y x).
Proof. exact (eq_refl (term83 P x y)). Qed.
Lemma lem1865196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865197 (P : type1626) (y : real) (x : real) : (term85 P x y) = (term86 P y x).
Proof. exact (MK_COMB (@lem1865196) (@lem1865195 P y x)). Qed.
Lemma lem1865198 (P : type1626) (y : real) (x : real) : (term87 P x y) = (term88 P y x).
Proof. exact (eq_refl (term87 P x y)). Qed.
Lemma lem1865199 (P : type1626) (y : real) (x : real) : (term89 P x y) = (term41 P y x).
Proof. exact (MK_COMB (@lem1865197 P y x) (@lem1865198 P y x)). Qed.
Lemma lem1865200 (P : type1626) (x : real) : (term90 P x) = (term42 P x).
Proof. exact (fun_ext (fun y : real => @lem1865199 P y x)). Qed.
Lemma lem1865201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865202 (P : type1626) (x : real) : (term79 P x) = (term43 P x).
Proof. exact (MK_COMB (@lem1865201) (@lem1865200 P x)). Qed.
Lemma lem1865203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1865204 (P : type1626) (x : real) : (term91 P x) = (term92 P x).
Proof. exact (MK_COMB (@lem1865203) (@lem1865202 P x)). Qed.
Lemma lem1865205 (P : type1626) (y : real) (x : real) : (term83 P x y) = (term84 P y x).
Proof. exact (eq_refl (term83 P x y)). Qed.
Lemma lem1865206 (P : type1626) (x : real) : (term93 P x) = (term81 P x).
Proof. exact (fun_ext (fun y : real => @lem1865205 P y x)). Qed.
Lemma lem1865207 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865208 (P : type1626) (x : real) : (term94 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem1865207) (@lem1865206 P x)). Qed.
Lemma lem1865209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865210 (P : type1626) (x : real) : (term96 P x) = (term97 P x).
Proof. exact (MK_COMB (@lem1865209) (@lem1865208 P x)). Qed.
Lemma lem1865211 (P : type1626) (y : real) (x : real) : (term87 P x y) = (term88 P y x).
Proof. exact (eq_refl (term87 P x y)). Qed.
Lemma lem1865212 (P : type1626) (x : real) : (term98 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : real => @lem1865211 P y x)). Qed.
Lemma lem1865213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865214 (P : type1626) (x : real) : (term99 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem1865213) (@lem1865212 P x)). Qed.
Lemma lem1865215 (P : type1626) (x : real) : (term80 P x) = (term101 P x).
Proof. exact (MK_COMB (@lem1865210 P x) (@lem1865214 P x)). Qed.
Lemma lem1865216 (P : type1626) (x : real) : ((term79 P x) = (term80 P x)) = ((term43 P x) = (term101 P x)).
Proof. exact (MK_COMB (@lem1865204 P x) (@lem1865215 P x)). Qed.
Lemma lem1865217 (P : type1626) (x : real) : (term43 P x) = (term101 P x).
Proof. exact (EQ_MP (@lem1865216 P x) (@lem1865194 P x)). Qed.
Lemma lem1865314 (P : type1626) : (term44 P) = (term102 P).
Proof. exact (fun_ext (fun x : real => @lem1865217 P x)). Qed.
Lemma lem1865315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865316 (P : type1626) : (term45 P) = (term103 P).
Proof. exact (MK_COMB (@lem1865315) (@lem1865314 P)). Qed.
Lemma lem1865318 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1865319 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem1865318 real P Q). Qed.
Lemma lem1865320 (P : type1626) : (term104 P) = (term105 P).
Proof. exact (@lem1865319 (term106 P) (term107 P)). Qed.
Lemma lem1865321 (P : type1626) (x : real) : (term108 P x) = (term95 P x).
Proof. exact (eq_refl (term108 P x)). Qed.
Lemma lem1865322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865323 (P : type1626) (x : real) : (term109 P x) = (term97 P x).
Proof. exact (MK_COMB (@lem1865322) (@lem1865321 P x)). Qed.
Lemma lem1865324 (P : type1626) (x : real) : (term110 P x) = (term100 P x).
Proof. exact (eq_refl (term110 P x)). Qed.
Lemma lem1865325 (P : type1626) (x : real) : (term111 P x) = (term101 P x).
Proof. exact (MK_COMB (@lem1865323 P x) (@lem1865324 P x)). Qed.
Lemma lem1865326 (P : type1626) : (term112 P) = (term102 P).
Proof. exact (fun_ext (fun x : real => @lem1865325 P x)). Qed.
Lemma lem1865327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865328 (P : type1626) : (term104 P) = (term103 P).
Proof. exact (MK_COMB (@lem1865327) (@lem1865326 P)). Qed.
Lemma lem1865329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1865330 (P : type1626) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem1865329) (@lem1865328 P)). Qed.
Lemma lem1865331 (P : type1626) (x : real) : (term108 P x) = (term95 P x).
Proof. exact (eq_refl (term108 P x)). Qed.
Lemma lem1865332 (P : type1626) : (term115 P) = (term106 P).
Proof. exact (fun_ext (fun x : real => @lem1865331 P x)). Qed.
Lemma lem1865333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865334 (P : type1626) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem1865333) (@lem1865332 P)). Qed.
Lemma lem1865335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865336 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem1865335) (@lem1865334 P)). Qed.
Lemma lem1865337 (P : type1626) (x : real) : (term110 P x) = (term100 P x).
Proof. exact (eq_refl (term110 P x)). Qed.
Lemma lem1865338 (P : type1626) : (term120 P) = (term107 P).
Proof. exact (fun_ext (fun x : real => @lem1865337 P x)). Qed.
Lemma lem1865339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865340 (P : type1626) : (term121 P) = (term122 P).
Proof. exact (MK_COMB (@lem1865339) (@lem1865338 P)). Qed.
Lemma lem1865341 (P : type1626) : (term105 P) = (term123 P).
Proof. exact (MK_COMB (@lem1865336 P) (@lem1865340 P)). Qed.
Lemma lem1865342 (P : type1626) : ((term104 P) = (term105 P)) = ((term103 P) = (term123 P)).
Proof. exact (MK_COMB (@lem1865330 P) (@lem1865341 P)). Qed.
Lemma lem1865343 (P : type1626) : (term103 P) = (term123 P).
Proof. exact (EQ_MP (@lem1865342 P) (@lem1865320 P)). Qed.
Lemma lem1865448 (P : type1626) : (term45 P) = (term123 P).
Proof. exact (TRANS (@lem1865316 P) (@lem1865343 P)). Qed.
Lemma lem1865449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865450 (P : type1626) : (term51 P) = (term124 P).
Proof. exact (MK_COMB (@lem1865449) (@lem1865448 P)). Qed.
Lemma lem1865503 (P : type1626) : (term50 P) = (term50 P).
Proof. exact (eq_refl (term50 P)). Qed.
Lemma lem1865504 (P : type1626) : (term52 P) = (term125 P).
Proof. exact (MK_COMB (@lem1865450 P) (@lem1865503 P)). Qed.
Lemma lem1865505 (P : type1626) : (term38 P) = (term38 P).
Proof. exact (eq_refl (term38 P)). Qed.
Lemma lem1865506 (P : type1626) : (term53 P) = (term126 P).
Proof. exact (MK_COMB (@lem1865505 P) (@lem1865504 P)). Qed.
Lemma lem1865507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865508 (P : type1626) : (term72 P) = (term127 P).
Proof. exact (MK_COMB (@lem1865507) (@lem1865506 P)). Qed.
Lemma lem1865517 (P : type1626) : (term70 P) = (term70 P).
Proof. exact (eq_refl (term70 P)). Qed.
Lemma lem1865518 (P : type1626) : (term74 P) = (term128 P).
Proof. exact (MK_COMB (@lem1865508 P) (@lem1865517 P)). Qed.
Lemma lem1865520 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1865521 (P : Prop) (Q : real -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem1865520 real P Q). Qed.
Lemma lem1865522 (P : type1626) : (term133 P) = (term134 P).
Proof. exact (@lem1865521 (term126 P) (term69 P)). Qed.
Lemma lem1865523 (P : type1626) (x : real) : (term135 P x) = (term63 P x).
Proof. exact (eq_refl (term135 P x)). Qed.
Lemma lem1865524 (P : type1626) : (term136 P) = (term69 P).
Proof. exact (fun_ext (fun x : real => @lem1865523 P x)). Qed.
Lemma lem1865525 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865526 (P : type1626) : (term137 P) = (term70 P).
Proof. exact (MK_COMB (@lem1865525) (@lem1865524 P)). Qed.
Lemma lem1865527 (P : type1626) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem1865528 (P : type1626) : (term133 P) = (term128 P).
Proof. exact (MK_COMB (@lem1865527 P) (@lem1865526 P)). Qed.
Lemma lem1865529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1865530 (P : type1626) : (term138 P) = (term139 P).
Proof. exact (MK_COMB (@lem1865529) (@lem1865528 P)). Qed.
Lemma lem1865531 (P : type1626) (x : real) : (term135 P x) = (term63 P x).
Proof. exact (eq_refl (term135 P x)). Qed.
Lemma lem1865532 (P : type1626) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem1865533 (P : type1626) (x : real) : (term140 P x) = (term141 P x).
Proof. exact (MK_COMB (@lem1865532 P) (@lem1865531 P x)). Qed.
Lemma lem1865534 (P : type1626) : (term142 P) = (term143 P).
Proof. exact (fun_ext (fun x : real => @lem1865533 P x)). Qed.
Lemma lem1865535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865536 (P : type1626) : (term134 P) = (term144 P).
Proof. exact (MK_COMB (@lem1865535) (@lem1865534 P)). Qed.
Lemma lem1865537 (P : type1626) : ((term133 P) = (term134 P)) = ((term128 P) = (term144 P)).
Proof. exact (MK_COMB (@lem1865530 P) (@lem1865536 P)). Qed.
Lemma lem1865538 (P : type1626) : (term128 P) = (term144 P).
Proof. exact (EQ_MP (@lem1865537 P) (@lem1865522 P)). Qed.
Lemma lem1865540 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1865541 (P : Prop) (Q : real -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem1865540 real P Q). Qed.
Lemma lem1865542 (P : type1626) (x : real) : (term145 P x) = (term146 P x).
Proof. exact (@lem1865541 (term126 P) (term62 P x)). Qed.
Lemma lem1865543 (P : type1626) (x : real) (y : real) : (term147 P x y) = (term60 P x y).
Proof. exact (eq_refl (term147 P x y)). Qed.
Lemma lem1865544 (P : type1626) (x : real) : (term148 P x) = (term62 P x).
Proof. exact (fun_ext (fun y : real => @lem1865543 P x y)). Qed.
Lemma lem1865545 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865546 (P : type1626) (x : real) : (term149 P x) = (term63 P x).
Proof. exact (MK_COMB (@lem1865545) (@lem1865544 P x)). Qed.
Lemma lem1865547 (P : type1626) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem1865548 (P : type1626) (x : real) : (term145 P x) = (term141 P x).
Proof. exact (MK_COMB (@lem1865547 P) (@lem1865546 P x)). Qed.
Lemma lem1865549 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1865550 (P : type1626) (x : real) : (term150 P x) = (term151 P x).
Proof. exact (MK_COMB (@lem1865549) (@lem1865548 P x)). Qed.
Lemma lem1865551 (P : type1626) (x : real) (y : real) : (term147 P x y) = (term60 P x y).
Proof. exact (eq_refl (term147 P x y)). Qed.
Lemma lem1865552 (P : type1626) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem1865553 (P : type1626) (x : real) (y : real) : (term152 P x y) = (term153 P x y).
Proof. exact (MK_COMB (@lem1865552 P) (@lem1865551 P x y)). Qed.
Lemma lem1865554 (P : type1626) (x : real) : (term154 P x) = (term155 P x).
Proof. exact (fun_ext (fun y : real => @lem1865553 P x y)). Qed.
Lemma lem1865555 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865556 (P : type1626) (x : real) : (term146 P x) = (term156 P x).
Proof. exact (MK_COMB (@lem1865555) (@lem1865554 P x)). Qed.
Lemma lem1865557 (P : type1626) (x : real) : ((term145 P x) = (term146 P x)) = ((term141 P x) = (term156 P x)).
Proof. exact (MK_COMB (@lem1865550 P x) (@lem1865556 P x)). Qed.
Lemma lem1865558 (P : type1626) (x : real) : (term141 P x) = (term156 P x).
Proof. exact (EQ_MP (@lem1865557 P x) (@lem1865542 P x)). Qed.
Lemma lem1865559 (P : type1626) : (term143 P) = (term157 P).
Proof. exact (fun_ext (fun x : real => @lem1865558 P x)). Qed.
Lemma lem1865560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1865561 (P : type1626) : (term144 P) = (term158 P).
Proof. exact (MK_COMB (@lem1865560) (@lem1865559 P)). Qed.
Lemma lem1865562 (P : type1626) : (term128 P) = (term158 P).
Proof. exact (TRANS (@lem1865538 P) (@lem1865561 P)). Qed.
Lemma lem1865563 (P : type1626) : (term74 P) = (term158 P).
Proof. exact (TRANS (@lem1865518 P) (@lem1865562 P)). Qed.
Lemma lem1865564 (P : type1626) : (term3 P) = (term158 P).
Proof. exact (TRANS (@lem1865182 P) (@lem1865563 P)). Qed.
Lemma lem1865565 (P : type1626) (h1 : term3 P) : term158 P.
Proof. exact (EQ_MP (@lem1865564 P) (@lem1865111 P h1)). Qed.
Lemma lem1865574 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1865575 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1865574 y x)). Qed.
Lemma lem1865576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865577 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1865576) (@lem1865575 x)). Qed.
Lemma lem1865578 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1865577 x)). Qed.
Lemma lem1865579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865636 : term10 = term10.
Proof. exact (MK_COMB (@lem1865579) (@lem1865578)). Qed.
Lemma lem1865637 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1865636) (@lem1865112 h1)). Qed.
Lemma lem1865638 (P : type1626) (x : real) (h1 : term156 P x) : term156 P x.
Proof. exact (h1). Qed.
Lemma lem1865639 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term153 P x y.
Proof. exact (h1). Qed.
Lemma lem1865660 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1865661 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1865660 y x)). Qed.
Lemma lem1865662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865663 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1865662) (@lem1865661 x)). Qed.
Lemma lem1865664 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1865663 x)). Qed.
Lemma lem1865665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865666 : term10 = term10.
Proof. exact (MK_COMB (@lem1865665) (@lem1865664)). Qed.
Lemma lem1865667 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1865666) (@lem1865637 h1)). Qed.
Lemma lem1865674 (P : type1626) (x : real) (y : real) : (term60 P x y) = (term60 P x y).
Proof. exact (eq_refl (term60 P x y)). Qed.
Lemma lem1865689 (P : type1626) (x : real) (y : real) : (term46 P x y) = (term46 P x y).
Proof. exact (eq_refl (term46 P x y)). Qed.
Lemma lem1865690 (P : type1626) (x : real) : (term47 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : real => @lem1865689 P x y)). Qed.
Lemma lem1865691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865692 (P : type1626) (x : real) : (term48 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem1865691) (@lem1865690 P x)). Qed.
Lemma lem1865693 (P : type1626) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun x : real => @lem1865692 P x)). Qed.
Lemma lem1865694 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865695 (P : type1626) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem1865694) (@lem1865693 P)). Qed.
Lemma lem1865710 (P : type1626) (y : real) (x : real) : (term88 P y x) = (term88 P y x).
Proof. exact (eq_refl (term88 P y x)). Qed.
Lemma lem1865711 (P : type1626) (x : real) : (term82 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : real => @lem1865710 P y x)). Qed.
Lemma lem1865712 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865713 (P : type1626) (x : real) : (term100 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem1865712) (@lem1865711 P x)). Qed.
Lemma lem1865714 (P : type1626) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun x : real => @lem1865713 P x)). Qed.
Lemma lem1865715 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865716 (P : type1626) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem1865715) (@lem1865714 P)). Qed.
Lemma lem1865731 (P : type1626) (y : real) (x : real) : (term84 P y x) = (term84 P y x).
Proof. exact (eq_refl (term84 P y x)). Qed.
Lemma lem1865732 (P : type1626) (x : real) : (term81 P x) = (term81 P x).
Proof. exact (fun_ext (fun y : real => @lem1865731 P y x)). Qed.
Lemma lem1865733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865734 (P : type1626) (x : real) : (term95 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem1865733) (@lem1865732 P x)). Qed.
Lemma lem1865735 (P : type1626) : (term106 P) = (term106 P).
Proof. exact (fun_ext (fun x : real => @lem1865734 P x)). Qed.
Lemma lem1865736 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865737 (P : type1626) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem1865736) (@lem1865735 P)). Qed.
Lemma lem1865738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865739 (P : type1626) : (term119 P) = (term119 P).
Proof. exact (MK_COMB (@lem1865738) (@lem1865737 P)). Qed.
Lemma lem1865740 (P : type1626) : (term123 P) = (term123 P).
Proof. exact (MK_COMB (@lem1865739 P) (@lem1865716 P)). Qed.
Lemma lem1865741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865742 (P : type1626) : (term124 P) = (term124 P).
Proof. exact (MK_COMB (@lem1865741) (@lem1865740 P)). Qed.
Lemma lem1865743 (P : type1626) : (term125 P) = (term125 P).
Proof. exact (MK_COMB (@lem1865742 P) (@lem1865695 P)). Qed.
Lemma lem1865748 (P : type1626) (x : real) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem1865749 (P : type1626) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : real => @lem1865748 P x)). Qed.
Lemma lem1865750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865751 (P : type1626) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem1865750) (@lem1865749 P)). Qed.
Lemma lem1865752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865753 (P : type1626) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem1865752) (@lem1865751 P)). Qed.
Lemma lem1865754 (P : type1626) : (term126 P) = (term126 P).
Proof. exact (MK_COMB (@lem1865753 P) (@lem1865743 P)). Qed.
Lemma lem1865755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1865756 (P : type1626) : (term127 P) = (term127 P).
Proof. exact (MK_COMB (@lem1865755) (@lem1865754 P)). Qed.
Lemma lem1865757 (P : type1626) (x : real) (y : real) : (term153 P x y) = (term153 P x y).
Proof. exact (MK_COMB (@lem1865756 P) (@lem1865674 P x y)). Qed.
Lemma lem1865758 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term153 P x y.
Proof. exact (EQ_MP (@lem1865757 P x y) (@lem1865639 P x y h1)). Qed.
Lemma lem1865760 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term126 P.
Proof. exact (proj1 (@lem1865758 P x y h1)). Qed.
Lemma lem1865761 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term125 P.
Proof. exact (proj2 (@lem1865760 P x y h1)). Qed.
Lemma lem1865762 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term37 P.
Proof. exact (proj1 (@lem1865760 P x y h1)). Qed.
Lemma lem1865763 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term50 P.
Proof. exact (proj2 (@lem1865761 P x y h1)). Qed.
Lemma lem1865764 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term123 P.
Proof. exact (proj1 (@lem1865761 P x y h1)). Qed.
Lemma lem1865765 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term122 P.
Proof. exact (proj2 (@lem1865764 P x y h1)). Qed.
Lemma lem1865780 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1865781 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1865780 y x)). Qed.
Lemma lem1865782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865783 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1865782) (@lem1865781 x)). Qed.
Lemma lem1865784 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1865783 x)). Qed.
Lemma lem1865785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865787 : term10 = term10.
Proof. exact (MK_COMB (@lem1865785) (@lem1865784)). Qed.
Lemma lem1865788 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1865787) (@lem1865667 h1)). Qed.
Lemma lem1865794 (P : type1626) (x : real) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem1865795 (P : type1626) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : real => @lem1865794 P x)). Qed.
Lemma lem1865796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865798 (P : type1626) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem1865796) (@lem1865795 P)). Qed.
Lemma lem1865799 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term37 P.
Proof. exact (EQ_MP (@lem1865798 P) (@lem1865762 P x y h1)). Qed.
Lemma lem1865807 (P : type1626) (x : real) (y : real) : (term46 P x y) = (term46 P x y).
Proof. exact (eq_refl (term46 P x y)). Qed.
Lemma lem1865808 (P : type1626) (x : real) : (term47 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : real => @lem1865807 P x y)). Qed.
Lemma lem1865809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865810 (P : type1626) (x : real) : (term48 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem1865809) (@lem1865808 P x)). Qed.
Lemma lem1865811 (P : type1626) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun x : real => @lem1865810 P x)). Qed.
Lemma lem1865812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865814 (P : type1626) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem1865812) (@lem1865811 P)). Qed.
Lemma lem1865815 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term50 P.
Proof. exact (EQ_MP (@lem1865814 P) (@lem1865763 P x y h1)). Qed.
Lemma lem1865839 (P : type1626) (y : real) (x : real) : (term88 P y x) = (term88 P y x).
Proof. exact (eq_refl (term88 P y x)). Qed.
Lemma lem1865840 (P : type1626) (x : real) : (term82 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : real => @lem1865839 P y x)). Qed.
Lemma lem1865841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865842 (P : type1626) (x : real) : (term100 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem1865841) (@lem1865840 P x)). Qed.
Lemma lem1865843 (P : type1626) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun x : real => @lem1865842 P x)). Qed.
Lemma lem1865844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1865846 (P : type1626) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem1865844) (@lem1865843 P)). Qed.
Lemma lem1865847 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term122 P.
Proof. exact (EQ_MP (@lem1865846 P) (@lem1865765 P x y h1)). Qed.
Lemma lem1865848 (_26997 : real) (h1 : term10) : term159 _26997.
Proof. exact (@lem1865788 h1 _26997). Qed.
Lemma lem1865849 (_26997 : real) : (term159 _26997) = (term19 _26997).
Proof. exact (eq_refl (term159 _26997)). Qed.
Lemma lem1865850 (_26997 : real) (h1 : term10) : term19 _26997.
Proof. exact (EQ_MP (@lem1865849 _26997) (@lem1865848 _26997 h1)). Qed.
Lemma lem1865851 (_26997 : real) (_26998 : real) (h1 : term10) : term160 _26997 _26998.
Proof. exact (@lem1865850 _26997 h1 _26998). Qed.
Lemma lem1865852 (_26998 : real) (_26997 : real) : (term160 _26997 _26998) = (term17 _26998 _26997).
Proof. exact (eq_refl (term160 _26997 _26998)). Qed.
Lemma lem1865854 (_26999 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term161 P _26999.
Proof. exact (@lem1865799 P x y h1 _26999). Qed.
Lemma lem1865855 (P : type1626) (_26999 : real) : (term161 P _26999) = (P _26999 _26999).
Proof. exact (eq_refl (term161 P _26999)). Qed.
Lemma lem1865857 (_27000 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term162 P _27000.
Proof. exact (@lem1865815 P x y h1 _27000). Qed.
Lemma lem1865858 (P : type1626) (_27000 : real) : (term162 P _27000) = (term48 P _27000).
Proof. exact (eq_refl (term162 P _27000)). Qed.
Lemma lem1865859 (_27000 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term48 P _27000.
Proof. exact (EQ_MP (@lem1865858 P _27000) (@lem1865857 _27000 P x y h1)). Qed.
Lemma lem1865860 (_27000 : real) (_27001 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term163 P _27000 _27001.
Proof. exact (@lem1865859 _27000 P x y h1 _27001). Qed.
Lemma lem1865861 (P : type1626) (_27000 : real) (_27001 : real) : (term163 P _27000 _27001) = (term46 P _27000 _27001).
Proof. exact (eq_refl (term163 P _27000 _27001)). Qed.
Lemma lem1865869 (_27004 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term110 P _27004.
Proof. exact (@lem1865847 P x y h1 _27004). Qed.
Lemma lem1865870 (P : type1626) (_27004 : real) : (term110 P _27004) = (term100 P _27004).
Proof. exact (eq_refl (term110 P _27004)). Qed.
Lemma lem1865871 (_27004 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term100 P _27004.
Proof. exact (EQ_MP (@lem1865870 P _27004) (@lem1865869 _27004 P x y h1)). Qed.
Lemma lem1865872 (_27004 : real) (_27005 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term87 P _27004 _27005.
Proof. exact (@lem1865871 _27004 P x y h1 _27005). Qed.
Lemma lem1865873 (P : type1626) (_27005 : real) (_27004 : real) : (term87 P _27004 _27005) = (term88 P _27005 _27004).
Proof. exact (eq_refl (term87 P _27004 _27005)). Qed.
Lemma lem1865884 (_26998 : real) (_26997 : real) (h1 : term10) : term17 _26998 _26997.
Proof. exact (EQ_MP (@lem1865852 _26998 _26997) (@lem1865851 _26997 _26998 h1)). Qed.
Lemma lem1865886 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term60 P x y.
Proof. exact (proj2 (@lem1865758 P x y h1)). Qed.
Lemma lem1865894 (_27000 : real) (_27001 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term46 P _27000 _27001.
Proof. exact (EQ_MP (@lem1865861 P _27000 _27001) (@lem1865860 _27000 _27001 P x y h1)). Qed.
Lemma lem1865906 (_27005 : real) (_27004 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term88 P _27005 _27004.
Proof. exact (EQ_MP (@lem1865873 P _27005 _27004) (@lem1865872 _27004 _27005 P x y h1)). Qed.
Lemma lem1865907 (P : type1626) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1865908 (_27006 : real) (_27008 : real) (h1 : _27006 = _27008) : _27006 = _27008.
Proof. exact (h1). Qed.
Lemma lem1865909 (_27007 : real) (_27009 : real) (h1 : _27007 = _27009) : _27007 = _27009.
Proof. exact (h1). Qed.
Lemma lem1865910 (P : type1626) (_27006 : real) (_27008 : real) (h1 : _27006 = _27008) : (P _27006) = (P _27008).
Proof. exact (MK_COMB (@lem1865907 P) (@lem1865908 _27006 _27008 h1)). Qed.
Lemma lem1865911 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) (h1 : _27006 = _27008) (h2 : _27007 = _27009) : (P _27006 _27007) = (P _27008 _27009).
Proof. exact (MK_COMB (@lem1865910 P _27006 _27008 h1) (@lem1865909 _27007 _27009 h2)). Qed.
Lemma lem1865913 (b : Prop) (a : Prop) : term164 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1865914 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : term165 _27008 _27009 P _27006 _27007.
Proof. exact (@lem1865913 (P _27008 _27009) (P _27006 _27007)). Qed.
Lemma lem1865915 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) (h1 : _27006 = _27008) (h2 : _27007 = _27009) : term166 _27008 _27009 P _27006 _27007.
Proof. exact (@lem1865914 _27008 _27009 P _27006 _27007 (@lem1865911 P _27006 _27008 _27007 _27009 h1 h2)). Qed.
Lemma lem1865916 (_27009 : real) (P : type1626) (_27007 : real) (_27006 : real) (_27008 : real) (h1 : _27006 = _27008) : term167 _27008 _27009 P _27006 _27007.
Proof. exact (fun h0 : _27007 = _27009 => @lem1865915 P _27006 _27008 _27007 _27009 h1 h0). Qed.
Lemma lem1865918 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1865919 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term167 _27008 _27009 P _27006 _27007) = (term169 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1865918 (_27007 = _27009) (term166 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1865920 (_27009 : real) (P : type1626) (_27007 : real) (_27006 : real) (_27008 : real) (h1 : _27006 = _27008) : term169 _27008 _27009 P _27006 _27007.
Proof. exact (EQ_MP (@lem1865919 _27008 _27009 P _27006 _27007) (@lem1865916 _27009 P _27007 _27006 _27008 h1)). Qed.
Lemma lem1865921 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : term170 _27008 _27009 P _27006 _27007.
Proof. exact (fun h0 : _27006 = _27008 => @lem1865920 _27009 P _27007 _27006 _27008 h0). Qed.
Lemma lem1865923 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1865924 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term170 _27008 _27009 P _27006 _27007) = (term171 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1865923 (_27006 = _27008) (term169 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1865925 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : term171 _27008 _27009 P _27006 _27007.
Proof. exact (EQ_MP (@lem1865924 _27008 _27009 P _27006 _27007) (@lem1865921 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1865948 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1865949 (x : real) : term172 x.
Proof. exact (fun h0 : term173 x => @lem1865948 x). Qed.
Lemma lem1865951 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1865952 (x : real) : (term172 x) = (x = x).
Proof. exact (@lem1865951 (x = x)). Qed.
Lemma lem1865953 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1865952 x) (@lem1865949 x)). Qed.
Lemma lem1865956 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term60 P x y.
Proof. exact (h1). Qed.
Lemma lem1865957 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term175 P x y.
Proof. exact (fun h0 : P x y => @lem1865956 P x y h1). Qed.
Lemma lem1865959 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1865960 (P : type1626) (x : real) (y : real) : (term175 P x y) = (term60 P x y).
Proof. exact (@lem1865959 (P x y)). Qed.
Lemma lem1865961 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term60 P x y.
Proof. exact (EQ_MP (@lem1865960 P x y) (@lem1865957 P x y h1)). Qed.
Lemma lem1865963 (_26999 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : P _26999 _26999.
Proof. exact (EQ_MP (@lem1865855 P _26999) (@lem1865854 _26999 P x y h1)). Qed.
Lemma lem1865964 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : P x x.
Proof. exact (@lem1865963 x P x y h1). Qed.
Lemma lem1865965 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term177 P x.
Proof. exact (fun h0 : term178 P x => @lem1865964 P x y h1). Qed.
Lemma lem1865967 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1865968 (P : type1626) (x : real) : (term177 P x) = (P x x).
Proof. exact (@lem1865967 (P x x)). Qed.
Lemma lem1865969 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : P x x.
Proof. exact (EQ_MP (@lem1865968 P x) (@lem1865965 P x y h1)). Qed.
Lemma lem1865987 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1865988 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term169 _27008 _27009 P _27006 _27007) = (term180 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1865987 (P _27008 _27009) (term181 _27007 _27009) (term60 P _27006 _27007)). Qed.
Lemma lem1866002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1866003 (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term182 _27009 P _27006 _27007) = (term183 P _27006 _27007 _27009).
Proof. exact (@lem1866002 (term60 P _27006 _27007) (term181 _27007 _27009)). Qed.
Lemma lem1866011 (P : type1626) (_27008 : real) (_27009 : real) : (term184 P _27008 _27009) = (term184 P _27008 _27009).
Proof. exact (eq_refl (term184 P _27008 _27009)). Qed.
Lemma lem1866012 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term180 _27008 _27009 P _27006 _27007) = (term185 _27008 P _27006 _27007 _27009).
Proof. exact (MK_COMB (@lem1866011 P _27008 _27009) (@lem1866003 P _27006 _27007 _27009)). Qed.
Lemma lem1866023 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term169 _27008 _27009 P _27006 _27007) = (term185 _27008 P _27006 _27007 _27009).
Proof. exact (TRANS (@lem1865988 _27008 _27009 P _27006 _27007) (@lem1866012 _27008 P _27006 _27007 _27009)). Qed.
Lemma lem1866024 (_27006 : real) (_27008 : real) : (term186 _27006 _27008) = (term186 _27006 _27008).
Proof. exact (eq_refl (term186 _27006 _27008)). Qed.
Lemma lem1866025 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term171 _27008 _27009 P _27006 _27007) = (term187 _27008 P _27006 _27007 _27009).
Proof. exact (MK_COMB (@lem1866024 _27006 _27008) (@lem1866023 _27008 P _27006 _27007 _27009)). Qed.
Lemma lem1866029 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866030 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term187 _27008 P _27006 _27007 _27009) = (term188 _27008 P _27006 _27007 _27009).
Proof. exact (@lem1866029 (P _27008 _27009) (term181 _27006 _27008) (term183 P _27006 _27007 _27009)). Qed.
Lemma lem1866044 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866045 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term189 _27008 P _27006 _27007 _27009) = (term190 P _27006 _27008 _27007 _27009).
Proof. exact (@lem1866044 (term60 P _27006 _27007) (term181 _27006 _27008) (term181 _27007 _27009)). Qed.
Lemma lem1866065 (P : type1626) (_27008 : real) (_27009 : real) : (term184 P _27008 _27009) = (term184 P _27008 _27009).
Proof. exact (eq_refl (term184 P _27008 _27009)). Qed.
Lemma lem1866066 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term188 _27008 P _27006 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (MK_COMB (@lem1866065 P _27008 _27009) (@lem1866045 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866077 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term187 _27008 P _27006 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (TRANS (@lem1866030 _27008 P _27006 _27007 _27009) (@lem1866066 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866078 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term171 _27008 _27009 P _27006 _27007) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (TRANS (@lem1866025 _27008 P _27006 _27007 _27009) (@lem1866077 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1866080 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term192 _27008 _27009 P _27006 _27007) = (term193 P _27006 _27008 _27007 _27009).
Proof. exact (MK_COMB (@lem1866079) (@lem1866078 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866084 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866085 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term194 _27008 _27009 P _27006 _27007) = (term171 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1866084 (term181 _27006 _27008) (term181 _27007 _27009) (term166 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866101 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866102 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term169 _27008 _27009 P _27006 _27007) = (term180 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1866101 (P _27008 _27009) (term181 _27007 _27009) (term60 P _27006 _27007)). Qed.
Lemma lem1866116 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1866117 (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term182 _27009 P _27006 _27007) = (term183 P _27006 _27007 _27009).
Proof. exact (@lem1866116 (term60 P _27006 _27007) (term181 _27007 _27009)). Qed.
Lemma lem1866125 (P : type1626) (_27008 : real) (_27009 : real) : (term184 P _27008 _27009) = (term184 P _27008 _27009).
Proof. exact (eq_refl (term184 P _27008 _27009)). Qed.
Lemma lem1866126 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term180 _27008 _27009 P _27006 _27007) = (term185 _27008 P _27006 _27007 _27009).
Proof. exact (MK_COMB (@lem1866125 P _27008 _27009) (@lem1866117 P _27006 _27007 _27009)). Qed.
Lemma lem1866137 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term169 _27008 _27009 P _27006 _27007) = (term185 _27008 P _27006 _27007 _27009).
Proof. exact (TRANS (@lem1866102 _27008 _27009 P _27006 _27007) (@lem1866126 _27008 P _27006 _27007 _27009)). Qed.
Lemma lem1866138 (_27006 : real) (_27008 : real) : (term186 _27006 _27008) = (term186 _27006 _27008).
Proof. exact (eq_refl (term186 _27006 _27008)). Qed.
Lemma lem1866139 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term171 _27008 _27009 P _27006 _27007) = (term187 _27008 P _27006 _27007 _27009).
Proof. exact (MK_COMB (@lem1866138 _27006 _27008) (@lem1866137 _27008 P _27006 _27007 _27009)). Qed.
Lemma lem1866143 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866144 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term187 _27008 P _27006 _27007 _27009) = (term188 _27008 P _27006 _27007 _27009).
Proof. exact (@lem1866143 (P _27008 _27009) (term181 _27006 _27008) (term183 P _27006 _27007 _27009)). Qed.
Lemma lem1866158 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866159 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term189 _27008 P _27006 _27007 _27009) = (term190 P _27006 _27008 _27007 _27009).
Proof. exact (@lem1866158 (term60 P _27006 _27007) (term181 _27006 _27008) (term181 _27007 _27009)). Qed.
Lemma lem1866179 (P : type1626) (_27008 : real) (_27009 : real) : (term184 P _27008 _27009) = (term184 P _27008 _27009).
Proof. exact (eq_refl (term184 P _27008 _27009)). Qed.
Lemma lem1866180 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term188 _27008 P _27006 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (MK_COMB (@lem1866179 P _27008 _27009) (@lem1866159 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866191 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term187 _27008 P _27006 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (TRANS (@lem1866144 _27008 P _27006 _27007 _27009) (@lem1866180 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866192 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term171 _27008 _27009 P _27006 _27007) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (TRANS (@lem1866139 _27008 P _27006 _27007 _27009) (@lem1866191 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866193 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : (term194 _27008 _27009 P _27006 _27007) = (term191 P _27006 _27008 _27007 _27009).
Proof. exact (TRANS (@lem1866085 _27008 _27009 P _27006 _27007) (@lem1866192 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866194 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : ((term171 _27008 _27009 P _27006 _27007) = (term194 _27008 _27009 P _27006 _27007)) = ((term191 P _27006 _27008 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009)).
Proof. exact (MK_COMB (@lem1866080 P _27006 _27008 _27007 _27009) (@lem1866193 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866196 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1866197 (x : Prop) : (x = x) = True.
Proof. exact (@lem1866196 Prop x). Qed.
Lemma lem1866198 (P : type1626) (_27006 : real) (_27008 : real) (_27007 : real) (_27009 : real) : ((term191 P _27006 _27008 _27007 _27009) = (term191 P _27006 _27008 _27007 _27009)) = True.
Proof. exact (@lem1866197 (term191 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866199 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : ((term171 _27008 _27009 P _27006 _27007) = (term194 _27008 _27009 P _27006 _27007)) = True.
Proof. exact (TRANS (@lem1866194 P _27006 _27008 _27007 _27009) (@lem1866198 P _27006 _27008 _27007 _27009)). Qed.
Lemma lem1866200 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : True = ((term171 _27008 _27009 P _27006 _27007) = (term194 _27008 _27009 P _27006 _27007)).
Proof. exact (SYM (@lem1866199 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866201 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term171 _27008 _27009 P _27006 _27007) = (term194 _27008 _27009 P _27006 _27007).
Proof. exact (EQ_MP (@lem1866200 _27008 _27009 P _27006 _27007) (@lem0)). Qed.
Lemma lem1866202 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : term194 _27008 _27009 P _27006 _27007.
Proof. exact (EQ_MP (@lem1866201 _27008 _27009 P _27006 _27007) (@lem1865925 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866204 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1866205 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term194 _27008 _27009 P _27006 _27007) = (term196 _27008 P _27006 _27007 _27009).
Proof. exact (@lem1866204 (term197 _27008 _27009 P _27006 _27007) (term181 _27007 _27009)). Qed.
Lemma lem1866207 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1866208 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term200 _27008 _27009 P _27006 _27007) = (term201 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1866207 (term181 _27006 _27008) (term166 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866210 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1866211 (_27006 : real) (_27008 : real) : (term203 _27006 _27008) = (_27006 = _27008).
Proof. exact (@lem1866210 (_27006 = _27008)). Qed.
Lemma lem1866212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1866213 (_27006 : real) (_27008 : real) : (term204 _27006 _27008) = (term205 _27006 _27008).
Proof. exact (MK_COMB (@lem1866212) (@lem1866211 _27006 _27008)). Qed.
Lemma lem1866215 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1866216 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term206 _27008 _27009 P _27006 _27007) = (term207 _27008 _27009 P _27006 _27007).
Proof. exact (@lem1866215 (P _27008 _27009) (term60 P _27006 _27007)). Qed.
Lemma lem1866218 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1866219 (P : type1626) (_27006 : real) (_27007 : real) : (term208 P _27006 _27007) = (P _27006 _27007).
Proof. exact (@lem1866218 (P _27006 _27007)). Qed.
Lemma lem1866220 (P : type1626) (_27008 : real) (_27009 : real) : (term209 P _27008 _27009) = (term209 P _27008 _27009).
Proof. exact (eq_refl (term209 P _27008 _27009)). Qed.
Lemma lem1866221 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term207 _27008 _27009 P _27006 _27007) = (term210 _27008 _27009 P _27006 _27007).
Proof. exact (MK_COMB (@lem1866220 P _27008 _27009) (@lem1866219 P _27006 _27007)). Qed.
Lemma lem1866222 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term206 _27008 _27009 P _27006 _27007) = (term210 _27008 _27009 P _27006 _27007).
Proof. exact (TRANS (@lem1866216 _27008 _27009 P _27006 _27007) (@lem1866221 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866223 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term201 _27008 _27009 P _27006 _27007) = (term211 _27008 _27009 P _27006 _27007).
Proof. exact (MK_COMB (@lem1866213 _27006 _27008) (@lem1866222 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866224 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term200 _27008 _27009 P _27006 _27007) = (term211 _27008 _27009 P _27006 _27007).
Proof. exact (TRANS (@lem1866208 _27008 _27009 P _27006 _27007) (@lem1866223 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866225 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866226 (_27008 : real) (_27009 : real) (P : type1626) (_27006 : real) (_27007 : real) : (term212 _27008 _27009 P _27006 _27007) = (term213 _27008 _27009 P _27006 _27007).
Proof. exact (MK_COMB (@lem1866225) (@lem1866224 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866227 (_27007 : real) (_27009 : real) : (term181 _27007 _27009) = (term181 _27007 _27009).
Proof. exact (eq_refl (term181 _27007 _27009)). Qed.
Lemma lem1866228 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term196 _27008 P _27006 _27007 _27009) = (term214 _27008 P _27006 _27007 _27009).
Proof. exact (MK_COMB (@lem1866226 _27008 _27009 P _27006 _27007) (@lem1866227 _27007 _27009)). Qed.
Lemma lem1866229 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : (term194 _27008 _27009 P _27006 _27007) = (term214 _27008 P _27006 _27007 _27009).
Proof. exact (TRANS (@lem1866205 _27008 P _27006 _27007 _27009) (@lem1866228 _27008 P _27006 _27007 _27009)). Qed.
Lemma lem1866231 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term215 y P x.
Proof. exact (conj (@lem1865961 P x y h1) (@lem1865969 P x y h2)). Qed.
Lemma lem1866232 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term216 y P x.
Proof. exact (conj (@lem1865953 x) (@lem1866231 P x y h1 h2)). Qed.
Lemma lem1866234 (_27008 : real) (P : type1626) (_27006 : real) (_27007 : real) (_27009 : real) : term214 _27008 P _27006 _27007 _27009.
Proof. exact (EQ_MP (@lem1866229 _27008 P _27006 _27007 _27009) (@lem1866202 _27008 _27009 P _27006 _27007)). Qed.
Lemma lem1866235 (P : type1626) (x : real) (y : real) : term217 P x y.
Proof. exact (@lem1866234 x P x x y). Qed.
Lemma lem1866238 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term181 x y.
Proof. exact (@lem1866235 P x y (@lem1866232 P x y h1 h2)). Qed.
Lemma lem1866239 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term218 x y.
Proof. exact (fun h0 : x = y => @lem1866238 P x y h1 h2). Qed.
Lemma lem1866241 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1866242 (x : real) (y : real) : (term218 x y) = (term181 x y).
Proof. exact (@lem1866241 (x = y)). Qed.
Lemma lem1866243 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term181 x y.
Proof. exact (EQ_MP (@lem1866242 x y) (@lem1866239 P x y h1 h2)). Qed.
Lemma lem1866246 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term60 P x y.
Proof. exact (h1). Qed.
Lemma lem1866247 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term175 P x y.
Proof. exact (fun h0 : P x y => @lem1866246 P x y h1). Qed.
Lemma lem1866249 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1866250 (P : type1626) (x : real) (y : real) : (term175 P x y) = (term60 P x y).
Proof. exact (@lem1866249 (P x y)). Qed.
Lemma lem1866251 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) : term60 P x y.
Proof. exact (EQ_MP (@lem1866250 P x y) (@lem1866247 P x y h1)). Qed.
Lemma lem1866253 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1866256 (P : type1626) (_27000 : real) (_27001 : real) : (term46 P _27000 _27001) = (term219 P _27000 _27001).
Proof. exact (@lem1866253 (P _27000 _27001) (term220 _27000 _27001)). Qed.
Lemma lem1866259 (_27000 : real) (_27001 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term219 P _27000 _27001.
Proof. exact (EQ_MP (@lem1866256 P _27000 _27001) (@lem1865894 _27000 _27001 P x y h1)). Qed.
Lemma lem1866260 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term219 P x y.
Proof. exact (@lem1866259 x y P x y h1). Qed.
Lemma lem1866263 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term220 x y.
Proof. exact (@lem1866260 P x y h2 (@lem1866251 P x y h1)). Qed.
Lemma lem1866264 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term221 x y.
Proof. exact (fun h0 : real_lt x y => @lem1866263 P x y h1 h2). Qed.
Lemma lem1866266 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1866267 (x : real) (y : real) : (term221 x y) = (term220 x y).
Proof. exact (@lem1866266 (real_lt x y)). Qed.
Lemma lem1866268 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term220 x y.
Proof. exact (EQ_MP (@lem1866267 x y) (@lem1866264 P x y h1 h2)). Qed.
Lemma lem1866291 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1866292 (_26997 : real) (_26998 : real) : (term222 _26997 _26998) = (term223 _26997 _26998).
Proof. exact (@lem1866291 (_26997 = _26998) (real_lt _26998 _26997) (real_lt _26997 _26998)). Qed.
Lemma lem1866308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1866309 (_26998 : real) (_26997 : real) : (term224 _26997 _26998) = (term224 _26998 _26997).
Proof. exact (@lem1866308 (real_lt _26997 _26998) (real_lt _26998 _26997)). Qed.
Lemma lem1866315 (_26997 : real) (_26998 : real) : (term225 _26997 _26998) = (term225 _26997 _26998).
Proof. exact (eq_refl (term225 _26997 _26998)). Qed.
Lemma lem1866316 (_26998 : real) (_26997 : real) : (term223 _26997 _26998) = (term17 _26998 _26997).
Proof. exact (MK_COMB (@lem1866315 _26997 _26998) (@lem1866309 _26998 _26997)). Qed.
Lemma lem1866327 (_26998 : real) (_26997 : real) : (term222 _26997 _26998) = (term17 _26998 _26997).
Proof. exact (TRANS (@lem1866292 _26997 _26998) (@lem1866316 _26998 _26997)). Qed.
Lemma lem1866328 (_26998 : real) (_26997 : real) : (term226 _26998 _26997) = (term226 _26998 _26997).
Proof. exact (eq_refl (term226 _26998 _26997)). Qed.
Lemma lem1866329 (_26998 : real) (_26997 : real) : ((term17 _26998 _26997) = (term222 _26997 _26998)) = ((term17 _26998 _26997) = (term17 _26998 _26997)).
Proof. exact (MK_COMB (@lem1866328 _26998 _26997) (@lem1866327 _26998 _26997)). Qed.
Lemma lem1866331 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1866332 (x : Prop) : (x = x) = True.
Proof. exact (@lem1866331 Prop x). Qed.
Lemma lem1866333 (_26998 : real) (_26997 : real) : ((term17 _26998 _26997) = (term17 _26998 _26997)) = True.
Proof. exact (@lem1866332 (term17 _26998 _26997)). Qed.
Lemma lem1866334 (_26997 : real) (_26998 : real) : ((term17 _26998 _26997) = (term222 _26997 _26998)) = True.
Proof. exact (TRANS (@lem1866329 _26998 _26997) (@lem1866333 _26998 _26997)). Qed.
Lemma lem1866335 (_26997 : real) (_26998 : real) : True = ((term17 _26998 _26997) = (term222 _26997 _26998)).
Proof. exact (SYM (@lem1866334 _26997 _26998)). Qed.
Lemma lem1866336 (_26997 : real) (_26998 : real) : (term17 _26998 _26997) = (term222 _26997 _26998).
Proof. exact (EQ_MP (@lem1866335 _26997 _26998) (@lem0)). Qed.
Lemma lem1866337 (_26997 : real) (_26998 : real) (h1 : term10) : term222 _26997 _26998.
Proof. exact (EQ_MP (@lem1866336 _26997 _26998) (@lem1865884 _26998 _26997 h1)). Qed.
Lemma lem1866339 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1866340 (_26998 : real) (_26997 : real) : (term222 _26997 _26998) = (term227 _26998 _26997).
Proof. exact (@lem1866339 (term228 _26997 _26998) (real_lt _26998 _26997)). Qed.
Lemma lem1866342 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1866343 (_26997 : real) (_26998 : real) : (term229 _26997 _26998) = (term230 _26997 _26998).
Proof. exact (@lem1866342 (_26997 = _26998) (real_lt _26997 _26998)). Qed.
Lemma lem1866344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866345 (_26997 : real) (_26998 : real) : (term231 _26997 _26998) = (term232 _26997 _26998).
Proof. exact (MK_COMB (@lem1866344) (@lem1866343 _26997 _26998)). Qed.
Lemma lem1866346 (_26998 : real) (_26997 : real) : (real_lt _26998 _26997) = (real_lt _26998 _26997).
Proof. exact (eq_refl (real_lt _26998 _26997)). Qed.
Lemma lem1866347 (_26998 : real) (_26997 : real) : (term227 _26998 _26997) = (term233 _26998 _26997).
Proof. exact (MK_COMB (@lem1866345 _26997 _26998) (@lem1866346 _26998 _26997)). Qed.
Lemma lem1866348 (_26998 : real) (_26997 : real) : (term222 _26997 _26998) = (term233 _26998 _26997).
Proof. exact (TRANS (@lem1866340 _26998 _26997) (@lem1866347 _26998 _26997)). Qed.
Lemma lem1866350 (P : type1626) (x : real) (y : real) (h1 : term60 P x y) (h2 : term153 P x y) : term230 x y.
Proof. exact (conj (@lem1866243 P x y h1 h2) (@lem1866268 P x y h1 h2)). Qed.
Lemma lem1866352 (_26998 : real) (_26997 : real) (h1 : term10) : term233 _26998 _26997.
Proof. exact (EQ_MP (@lem1866348 _26998 _26997) (@lem1866337 _26997 _26998 h1)). Qed.
Lemma lem1866353 (y : real) (x : real) (h1 : term10) : term233 y x.
Proof. exact (@lem1866352 y x h1). Qed.
Lemma lem1866356 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : real_lt y x.
Proof. exact (@lem1866353 y x h1 (@lem1866350 P x y h2 h3)). Qed.
Lemma lem1866357 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : term234 y x.
Proof. exact (fun h0 : term220 y x => @lem1866356 P x y h1 h2 h3). Qed.
Lemma lem1866359 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1866360 (y : real) (x : real) : (term234 y x) = (real_lt y x).
Proof. exact (@lem1866359 (real_lt y x)). Qed.
Lemma lem1866361 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : real_lt y x.
Proof. exact (EQ_MP (@lem1866360 y x) (@lem1866357 P x y h1 h2 h3)). Qed.
Lemma lem1866367 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1866368 (P : type1626) (_27000 : real) (_27001 : real) : (term46 P _27000 _27001) = (term235 P _27000 _27001).
Proof. exact (@lem1866367 (P _27000 _27001) (term220 _27000 _27001)). Qed.
Lemma lem1866374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1866375 (P : type1626) (_27000 : real) (_27001 : real) : (term236 P _27000 _27001) = (term237 P _27000 _27001).
Proof. exact (MK_COMB (@lem1866374) (@lem1866368 P _27000 _27001)). Qed.
Lemma lem1866381 (P : type1626) (_27000 : real) (_27001 : real) : (term235 P _27000 _27001) = (term235 P _27000 _27001).
Proof. exact (eq_refl (term235 P _27000 _27001)). Qed.
Lemma lem1866382 (P : type1626) (_27000 : real) (_27001 : real) : ((term46 P _27000 _27001) = (term235 P _27000 _27001)) = ((term235 P _27000 _27001) = (term235 P _27000 _27001)).
Proof. exact (MK_COMB (@lem1866375 P _27000 _27001) (@lem1866381 P _27000 _27001)). Qed.
Lemma lem1866384 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1866385 (x : Prop) : (x = x) = True.
Proof. exact (@lem1866384 Prop x). Qed.
Lemma lem1866386 (P : type1626) (_27000 : real) (_27001 : real) : ((term235 P _27000 _27001) = (term235 P _27000 _27001)) = True.
Proof. exact (@lem1866385 (term235 P _27000 _27001)). Qed.
Lemma lem1866387 (P : type1626) (_27000 : real) (_27001 : real) : ((term46 P _27000 _27001) = (term235 P _27000 _27001)) = True.
Proof. exact (TRANS (@lem1866382 P _27000 _27001) (@lem1866386 P _27000 _27001)). Qed.
Lemma lem1866388 (P : type1626) (_27000 : real) (_27001 : real) : True = ((term46 P _27000 _27001) = (term235 P _27000 _27001)).
Proof. exact (SYM (@lem1866387 P _27000 _27001)). Qed.
Lemma lem1866389 (P : type1626) (_27000 : real) (_27001 : real) : (term46 P _27000 _27001) = (term235 P _27000 _27001).
Proof. exact (EQ_MP (@lem1866388 P _27000 _27001) (@lem0)). Qed.
Lemma lem1866390 (_27000 : real) (_27001 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term235 P _27000 _27001.
Proof. exact (EQ_MP (@lem1866389 P _27000 _27001) (@lem1865894 _27000 _27001 P x y h1)). Qed.
Lemma lem1866392 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1866393 (P : type1626) (_27000 : real) (_27001 : real) : (term235 P _27000 _27001) = (term238 P _27000 _27001).
Proof. exact (@lem1866392 (term220 _27000 _27001) (P _27000 _27001)). Qed.
Lemma lem1866395 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1866396 (_27000 : real) (_27001 : real) : (term239 _27000 _27001) = (real_lt _27000 _27001).
Proof. exact (@lem1866395 (real_lt _27000 _27001)). Qed.
Lemma lem1866397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866398 (_27000 : real) (_27001 : real) : (term240 _27000 _27001) = (term241 _27000 _27001).
Proof. exact (MK_COMB (@lem1866397) (@lem1866396 _27000 _27001)). Qed.
Lemma lem1866399 (P : type1626) (_27000 : real) (_27001 : real) : (P _27000 _27001) = (P _27000 _27001).
Proof. exact (eq_refl (P _27000 _27001)). Qed.
Lemma lem1866400 (P : type1626) (_27000 : real) (_27001 : real) : (term238 P _27000 _27001) = (term25 P _27000 _27001).
Proof. exact (MK_COMB (@lem1866398 _27000 _27001) (@lem1866399 P _27000 _27001)). Qed.
Lemma lem1866401 (P : type1626) (_27000 : real) (_27001 : real) : (term235 P _27000 _27001) = (term25 P _27000 _27001).
Proof. exact (TRANS (@lem1866393 P _27000 _27001) (@lem1866400 P _27000 _27001)). Qed.
Lemma lem1866404 (_27000 : real) (_27001 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term25 P _27000 _27001.
Proof. exact (EQ_MP (@lem1866401 P _27000 _27001) (@lem1866390 _27000 _27001 P x y h1)). Qed.
Lemma lem1866405 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term25 P y x.
Proof. exact (@lem1866404 y x P x y h1). Qed.
Lemma lem1866408 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P y x.
Proof. exact (@lem1866405 P x y h3 (@lem1866361 P x y h1 h2 h3)). Qed.
Lemma lem1866409 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : term242 P y x.
Proof. exact (fun h0 : term60 P y x => @lem1866408 P x y h1 h2 h3). Qed.
Lemma lem1866411 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1866412 (P : type1626) (y : real) (x : real) : (term242 P y x) = (P y x).
Proof. exact (@lem1866411 (P y x)). Qed.
Lemma lem1866413 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P y x.
Proof. exact (EQ_MP (@lem1866412 P y x) (@lem1866409 P x y h1 h2 h3)). Qed.
Lemma lem1866419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1866420 (P : type1626) (_27004 : real) (_27005 : real) : (term88 P _27005 _27004) = (term84 P _27004 _27005).
Proof. exact (@lem1866419 (P _27005 _27004) (term60 P _27004 _27005)). Qed.
Lemma lem1866426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1866427 (P : type1626) (_27004 : real) (_27005 : real) : (term243 P _27005 _27004) = (term244 P _27004 _27005).
Proof. exact (MK_COMB (@lem1866426) (@lem1866420 P _27004 _27005)). Qed.
Lemma lem1866433 (P : type1626) (_27004 : real) (_27005 : real) : (term84 P _27004 _27005) = (term84 P _27004 _27005).
Proof. exact (eq_refl (term84 P _27004 _27005)). Qed.
Lemma lem1866434 (P : type1626) (_27004 : real) (_27005 : real) : ((term88 P _27005 _27004) = (term84 P _27004 _27005)) = ((term84 P _27004 _27005) = (term84 P _27004 _27005)).
Proof. exact (MK_COMB (@lem1866427 P _27004 _27005) (@lem1866433 P _27004 _27005)). Qed.
Lemma lem1866436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1866437 (x : Prop) : (x = x) = True.
Proof. exact (@lem1866436 Prop x). Qed.
Lemma lem1866438 (P : type1626) (_27004 : real) (_27005 : real) : ((term84 P _27004 _27005) = (term84 P _27004 _27005)) = True.
Proof. exact (@lem1866437 (term84 P _27004 _27005)). Qed.
Lemma lem1866439 (P : type1626) (_27004 : real) (_27005 : real) : ((term88 P _27005 _27004) = (term84 P _27004 _27005)) = True.
Proof. exact (TRANS (@lem1866434 P _27004 _27005) (@lem1866438 P _27004 _27005)). Qed.
Lemma lem1866440 (P : type1626) (_27004 : real) (_27005 : real) : True = ((term88 P _27005 _27004) = (term84 P _27004 _27005)).
Proof. exact (SYM (@lem1866439 P _27004 _27005)). Qed.
Lemma lem1866441 (P : type1626) (_27004 : real) (_27005 : real) : (term88 P _27005 _27004) = (term84 P _27004 _27005).
Proof. exact (EQ_MP (@lem1866440 P _27004 _27005) (@lem0)). Qed.
Lemma lem1866442 (_27004 : real) (_27005 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term84 P _27004 _27005.
Proof. exact (EQ_MP (@lem1866441 P _27004 _27005) (@lem1865906 _27005 _27004 P x y h1)). Qed.
Lemma lem1866444 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1866445 (P : type1626) (_27005 : real) (_27004 : real) : (term84 P _27004 _27005) = (term245 P _27005 _27004).
Proof. exact (@lem1866444 (term60 P _27004 _27005) (P _27005 _27004)). Qed.
Lemma lem1866447 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1866448 (P : type1626) (_27004 : real) (_27005 : real) : (term208 P _27004 _27005) = (P _27004 _27005).
Proof. exact (@lem1866447 (P _27004 _27005)). Qed.
Lemma lem1866449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866450 (P : type1626) (_27004 : real) (_27005 : real) : (term246 P _27004 _27005) = (term247 P _27004 _27005).
Proof. exact (MK_COMB (@lem1866449) (@lem1866448 P _27004 _27005)). Qed.
Lemma lem1866451 (P : type1626) (_27005 : real) (_27004 : real) : (P _27005 _27004) = (P _27005 _27004).
Proof. exact (eq_refl (P _27005 _27004)). Qed.
Lemma lem1866452 (P : type1626) (_27005 : real) (_27004 : real) : (term245 P _27005 _27004) = (term248 P _27005 _27004).
Proof. exact (MK_COMB (@lem1866450 P _27004 _27005) (@lem1866451 P _27005 _27004)). Qed.
Lemma lem1866453 (P : type1626) (_27005 : real) (_27004 : real) : (term84 P _27004 _27005) = (term248 P _27005 _27004).
Proof. exact (TRANS (@lem1866445 P _27005 _27004) (@lem1866452 P _27005 _27004)). Qed.
Lemma lem1866456 (_27005 : real) (_27004 : real) (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term248 P _27005 _27004.
Proof. exact (EQ_MP (@lem1866453 P _27005 _27004) (@lem1866442 _27004 _27005 P x y h1)). Qed.
Lemma lem1866457 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term248 P x y.
Proof. exact (@lem1866456 x y P x y h1). Qed.
Lemma lem1866460 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P x y.
Proof. exact (@lem1866457 P x y h3 (@lem1866413 P x y h1 h2 h3)). Qed.
Lemma lem1866461 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : term242 P x y.
Proof. exact (fun h0 : term60 P x y => @lem1866460 P x y h1 h0 h2). Qed.
Lemma lem1866463 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1866464 (P : type1626) (x : real) (y : real) : (term242 P x y) = (P x y).
Proof. exact (@lem1866463 (P x y)). Qed.
Lemma lem1866465 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : P x y.
Proof. exact (EQ_MP (@lem1866464 P x y) (@lem1866461 P x y h1 h2)). Qed.
Lemma lem1866468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1866470 (P : type1626) (x : real) (y : real) : (term60 P x y) = (term249 P x y).
Proof. exact (@lem1866468 (P x y)). Qed.
Lemma lem1866473 (P : type1626) (x : real) (y : real) (h1 : term153 P x y) : term249 P x y.
Proof. exact (EQ_MP (@lem1866470 P x y) (@lem1865886 P x y h1)). Qed.
Lemma lem1866476 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (@lem1866473 P x y h2 (@lem1866465 P x y h1 h2)). Qed.
Lemma lem1866477 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : term250.
Proof. exact (fun h0 : ~ False => @lem1866476 P x y h1 h2). Qed.
Lemma lem1866479 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1866480 : term250 = False.
Proof. exact (@lem1866479 False). Qed.
Lemma lem1866481 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem1866480) (@lem1866477 P x y h1 h2)). Qed.
Lemma lem1866482 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1866481 P x y h1 h2) (fun h3 : False => @lem1865788 h1)). Qed.
Lemma lem1866483 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem1866482 P x y h1 h2) (@lem1865788 h1)). Qed.
Lemma lem1866484 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : (term153 P x y) = False.
Proof. exact (prop_ext (fun h3 : term153 P x y => @lem1866483 P x y h1 h2) (fun h3 : False => @lem1865758 P x y h2)). Qed.
Lemma lem1866485 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem1866484 P x y h1 h2) (@lem1865758 P x y h2)). Qed.
Lemma lem1866486 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1866485 P x y h1 h2) (fun h3 : False => @lem1865667 h1)). Qed.
Lemma lem1866487 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem1866486 P x y h1 h2) (@lem1865667 h1)). Qed.
Lemma lem1866488 (P : type1626) (x : real) (h1 : term10) (h2 : term156 P x) : False.
Proof. exact (ex_elim (@lem1865638 P x h2) (fun y : real => fun h0 : term155 P x y => @lem1866487 P x y h1 h0)). Qed.
Lemma lem1866489 (P : type1626) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem1865565 P h2) (fun x : real => fun h0 : term157 P x => @lem1866488 P x h1 h0)). Qed.
Lemma lem1866490 (P : type1626) (h1 : term10) (h2 : term3 P) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1866489 P h1 h2) (fun h3 : False => @lem1865637 h1)). Qed.
Lemma lem1866491 (P : type1626) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (EQ_MP (@lem1866490 P h1 h2) (@lem1865637 h1)). Qed.
Lemma lem1866492 (P : type1626) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem1866491 P h0 h1). Qed.
Lemma lem1866493 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1866494 (P : type1626) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem1866493) (@lem1866492 P h1)). Qed.
Lemma lem1866495 (P : type1626) : term12 P.
Proof. exact (fun h0 : term3 P => @lem1866494 P h0). Qed.
Lemma lem1866500 : term16.
Proof. exact (fun P : type1626 => @lem1866495 P). Qed.
Lemma lem1866501 : term15.
Proof. exact (EQ_MP (@lem1865110) (@lem1866500)). Qed.
Lemma lem1866502 (P : type1626) : term251 P.
Proof. exact (@lem1866501 P). Qed.
Lemma lem1866503 (P : type1626) : (term251 P) = (term4 P).
Proof. exact (eq_refl (term251 P)). Qed.
Lemma lem1866504 (P : type1626) : term4 P.
Proof. exact (EQ_MP (@lem1866503 P) (@lem1866502 P)). Qed.
Lemma lem1866506 (P : type1626) : term4 P.
Proof. exact (@lem1864849 P (@lem1866504 P)). Qed.
Lemma lem1866507 (P : type1626) (h1 : term3 P) : term8.
Proof. exact (@lem1866506 P (@lem1864834 P h1)). Qed.
Lemma lem1866508 (P : type1626) (h1 : term3 P) : False.
Proof. exact (@lem1866507 P h1 (@lem1498801)). Qed.
Lemma lem1866509 (P : type1626) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem1866508 P h1) (fun h2 : False => @lem1864834 P h1)). Qed.
Lemma lem1866510 (P : type1626) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem1866509 P h1) (@lem1864834 P h1)). Qed.
Lemma lem1866511 (P : type1626) : term2 P.
Proof. exact (fun h0 : term3 P => @lem1866510 P h0). Qed.
Lemma lem1866512 (P : type1626) : term1 P.
Proof. exact (EQ_MP (@lem1864833 P) (@lem1866511 P)). Qed.
