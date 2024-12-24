Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_RID_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm1338986_spec.
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
Lemma lem1382914 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1382915 : term1 = term2.
Proof. exact (@lem1382914 term1). Qed.
Lemma lem1382916 : term2 = term1.
Proof. exact (SYM (@lem1382915)). Qed.
Lemma lem1382917 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1382920 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1382921 : term5.
Proof. exact (fun h0 : term4 => @lem1382920 h0). Qed.
Lemma lem1382922 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1382923 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1382924 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1382922 h2 (@lem1382923 h1)). Qed.
Lemma lem1382925 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1382924 h1 h0). Qed.
Lemma lem1382926 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1382927 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1382925 h1 (@lem1382926 h2)). Qed.
Lemma lem1382928 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1382927 h0 h1). Qed.
Lemma lem1382929 : term7.
Proof. exact (fun h0 : term5 => @lem1382928 h0). Qed.
Lemma lem1382932 : term5.
Proof. exact (@lem1382929 (@lem1382921)). Qed.
Lemma lem1382950 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1382951 : term8 = term9.
Proof. exact (@lem1382950 term10). Qed.
Lemma lem1382956 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1382957 : term12 = term13.
Proof. exact (MK_COMB (@lem1382956) (@lem1382951)). Qed.
Lemma lem1382960 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1382967 : term4 = term15.
Proof. exact (MK_COMB (@lem1382960) (@lem1382957)). Qed.
Lemma lem1382968 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1382969 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1382968 x)). Qed.
Lemma lem1382970 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382971 : term10 = term10.
Proof. exact (MK_COMB (@lem1382970) (@lem1382969)). Qed.
Lemma lem1382972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1382973 : term9 = term9.
Proof. exact (MK_COMB (@lem1382972) (@lem1382971)). Qed.
Lemma lem1382974 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1382975 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1382974 y x)). Qed.
Lemma lem1382976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382977 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1382976) (@lem1382975 x)). Qed.
Lemma lem1382978 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1382977 x)). Qed.
Lemma lem1382979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382980 : term21 = term21.
Proof. exact (MK_COMB (@lem1382979) (@lem1382978)). Qed.
Lemma lem1382981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382982 : term11 = term11.
Proof. exact (MK_COMB (@lem1382981) (@lem1382980)). Qed.
Lemma lem1382983 : term13 = term13.
Proof. exact (MK_COMB (@lem1382982) (@lem1382973)). Qed.
Lemma lem1382984 (x : real) : ((term22 x) = x) = ((term22 x) = x).
Proof. exact (eq_refl ((term22 x) = x)). Qed.
Lemma lem1382985 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1382984 x)). Qed.
Lemma lem1382986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1382987 : term1 = term1.
Proof. exact (MK_COMB (@lem1382986) (@lem1382985)). Qed.
Lemma lem1382988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1382989 : term3 = term3.
Proof. exact (MK_COMB (@lem1382988) (@lem1382987)). Qed.
Lemma lem1382990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1382991 : term14 = term14.
Proof. exact (MK_COMB (@lem1382990) (@lem1382989)). Qed.
Lemma lem1382992 : term15 = term15.
Proof. exact (MK_COMB (@lem1382991) (@lem1382983)). Qed.
Lemma lem1383023 : term4 = term15.
Proof. exact (TRANS (@lem1382967) (@lem1382992)). Qed.
Lemma lem1383024 : term15 = term4.
Proof. exact (SYM (@lem1383023)). Qed.
Lemma lem1383025 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1383026 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1383027 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1383029 (P : real -> Prop) : (term24 P) = (term25 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1383030 : term3 = term26.
Proof. exact (@lem1383029 term23). Qed.
Lemma lem1383031 (x : real) : (term27 x) = ((term22 x) = x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1383032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1383034 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1383032) (@lem1383031 x)). Qed.
Lemma lem1383035 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1383034 x)). Qed.
Lemma lem1383036 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1383037 : term26 = term32.
Proof. exact (MK_COMB (@lem1383036) (@lem1383035)). Qed.
Lemma lem1383046 : term3 = term32.
Proof. exact (TRANS (@lem1383030) (@lem1383037)). Qed.
Lemma lem1383047 (h1 : term3) : term32.
Proof. exact (EQ_MP (@lem1383046) (@lem1383025 h1)). Qed.
Lemma lem1383048 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1383049 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1383048 y x)). Qed.
Lemma lem1383050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383051 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1383050) (@lem1383049 x)). Qed.
Lemma lem1383052 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1383051 x)). Qed.
Lemma lem1383053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383066 : term21 = term21.
Proof. exact (MK_COMB (@lem1383053) (@lem1383052)). Qed.
Lemma lem1383067 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1383066) (@lem1383026 h1)). Qed.
Lemma lem1383068 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1383069 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1383068 x)). Qed.
Lemma lem1383070 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383079 : term10 = term10.
Proof. exact (MK_COMB (@lem1383070) (@lem1383069)). Qed.
Lemma lem1383080 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1383079) (@lem1383027 h1)). Qed.
Lemma lem1383094 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1383095 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1383094 y x)). Qed.
Lemma lem1383096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383097 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1383096) (@lem1383095 x)). Qed.
Lemma lem1383098 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1383097 x)). Qed.
Lemma lem1383099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383100 : term21 = term21.
Proof. exact (MK_COMB (@lem1383099) (@lem1383098)). Qed.
Lemma lem1383101 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1383100) (@lem1383067 h1)). Qed.
Lemma lem1383116 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1383117 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1383116 x)). Qed.
Lemma lem1383118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383119 : term10 = term10.
Proof. exact (MK_COMB (@lem1383118) (@lem1383117)). Qed.
Lemma lem1383120 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1383119) (@lem1383080 h1)). Qed.
Lemma lem1383138 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1383140 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1383141 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1383140 y x)). Qed.
Lemma lem1383142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383143 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1383142) (@lem1383141 x)). Qed.
Lemma lem1383144 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1383143 x)). Qed.
Lemma lem1383145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383147 : term21 = term21.
Proof. exact (MK_COMB (@lem1383145) (@lem1383144)). Qed.
Lemma lem1383148 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1383147) (@lem1383101 h1)). Qed.
Lemma lem1383150 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1383151 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1383150 x)). Qed.
Lemma lem1383152 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1383154 : term10 = term10.
Proof. exact (MK_COMB (@lem1383152) (@lem1383151)). Qed.
Lemma lem1383155 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1383154) (@lem1383120 h1)). Qed.
Lemma lem1383159 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1383160 (_24495 : real) (h1 : term21) : term33 _24495.
Proof. exact (@lem1383148 h1 _24495). Qed.
Lemma lem1383161 (_24495 : real) : (term33 _24495) = (term19 _24495).
Proof. exact (eq_refl (term33 _24495)). Qed.
Lemma lem1383162 (_24495 : real) (h1 : term21) : term19 _24495.
Proof. exact (EQ_MP (@lem1383161 _24495) (@lem1383160 _24495 h1)). Qed.
Lemma lem1383163 (_24495 : real) (_24496 : real) (h1 : term21) : term34 _24495 _24496.
Proof. exact (@lem1383162 _24495 h1 _24496). Qed.
Lemma lem1383164 (_24496 : real) (_24495 : real) : (term34 _24495 _24496) = ((real_mul _24495 _24496) = (real_mul _24496 _24495)).
Proof. exact (eq_refl (term34 _24495 _24496)). Qed.
Lemma lem1383166 (_24497 : real) (h1 : term10) : term35 _24497.
Proof. exact (@lem1383155 h1 _24497). Qed.
Lemma lem1383167 (_24497 : real) : (term35 _24497) = ((term16 _24497) = _24497).
Proof. exact (eq_refl (term35 _24497)). Qed.
Lemma lem1383174 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1383215 (x : real) (y : real) (z : real) : term36 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1383219 (_24496 : real) (_24495 : real) (h1 : term21) : (real_mul _24495 _24496) = (real_mul _24496 _24495).
Proof. exact (EQ_MP (@lem1383164 _24496 _24495) (@lem1383163 _24495 _24496 h1)). Qed.
Lemma lem1383220 (x : real) (h1 : term21) : (term16 x) = (term22 x).
Proof. exact (@lem1383219 x term37 h1). Qed.
Lemma lem1383221 (x : real) (h1 : term21) : term38 x.
Proof. exact (fun h0 : term39 x => @lem1383220 x h1). Qed.
Lemma lem1383223 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1383224 (x : real) : (term38 x) = ((term16 x) = (term22 x)).
Proof. exact (@lem1383223 ((term16 x) = (term22 x))). Qed.
Lemma lem1383225 (x : real) (h1 : term21) : (term16 x) = (term22 x).
Proof. exact (EQ_MP (@lem1383224 x) (@lem1383221 x h1)). Qed.
Lemma lem1383227 (_24497 : real) (h1 : term10) : (term16 _24497) = _24497.
Proof. exact (EQ_MP (@lem1383167 _24497) (@lem1383166 _24497 h1)). Qed.
Lemma lem1383228 (x : real) (h1 : term10) : (term16 x) = x.
Proof. exact (@lem1383227 x h1). Qed.
Lemma lem1383229 (x : real) (h1 : term10) : term41 x.
Proof. exact (fun h0 : term42 x => @lem1383228 x h1). Qed.
Lemma lem1383231 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1383232 (x : real) : (term41 x) = ((term16 x) = x).
Proof. exact (@lem1383231 ((term16 x) = x)). Qed.
Lemma lem1383233 (x : real) (h1 : term10) : (term16 x) = x.
Proof. exact (EQ_MP (@lem1383232 x) (@lem1383229 x h1)). Qed.
Lemma lem1383251 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1383252 (y : real) (x : real) (z : real) : (term43 x y z) = (term44 y x z).
Proof. exact (@lem1383251 (y = z) (term45 x z)). Qed.
Lemma lem1383262 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1383263 (y : real) (x : real) (z : real) : (term36 x y z) = (term47 y x z).
Proof. exact (MK_COMB (@lem1383262 x y) (@lem1383252 y x z)). Qed.
Lemma lem1383267 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1383268 (y : real) (x : real) (z : real) : (term47 y x z) = (term49 y x z).
Proof. exact (@lem1383267 (y = z) (term45 x y) (term45 x z)). Qed.
Lemma lem1383290 (y : real) (x : real) (z : real) : (term36 x y z) = (term49 y x z).
Proof. exact (TRANS (@lem1383263 y x z) (@lem1383268 y x z)). Qed.
Lemma lem1383291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1383292 (y : real) (x : real) (z : real) : (term50 x y z) = (term51 y x z).
Proof. exact (MK_COMB (@lem1383291) (@lem1383290 y x z)). Qed.
Lemma lem1383314 (y : real) (x : real) (z : real) : (term49 y x z) = (term49 y x z).
Proof. exact (eq_refl (term49 y x z)). Qed.
Lemma lem1383315 (y : real) (x : real) (z : real) : ((term36 x y z) = (term49 y x z)) = ((term49 y x z) = (term49 y x z)).
Proof. exact (MK_COMB (@lem1383292 y x z) (@lem1383314 y x z)). Qed.
Lemma lem1383317 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1383318 (x : Prop) : (x = x) = True.
Proof. exact (@lem1383317 Prop x). Qed.
Lemma lem1383319 (y : real) (x : real) (z : real) : ((term49 y x z) = (term49 y x z)) = True.
Proof. exact (@lem1383318 (term49 y x z)). Qed.
Lemma lem1383320 (y : real) (x : real) (z : real) : ((term36 x y z) = (term49 y x z)) = True.
Proof. exact (TRANS (@lem1383315 y x z) (@lem1383319 y x z)). Qed.
Lemma lem1383321 (y : real) (x : real) (z : real) : True = ((term36 x y z) = (term49 y x z)).
Proof. exact (SYM (@lem1383320 y x z)). Qed.
Lemma lem1383322 (y : real) (x : real) (z : real) : (term36 x y z) = (term49 y x z).
Proof. exact (EQ_MP (@lem1383321 y x z) (@lem0)). Qed.
Lemma lem1383323 (y : real) (x : real) (z : real) : term49 y x z.
Proof. exact (EQ_MP (@lem1383322 y x z) (@lem1383215 x y z)). Qed.
Lemma lem1383325 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1383326 (x : real) (y : real) (z : real) : (term49 y x z) = (term53 x y z).
Proof. exact (@lem1383325 (term54 y x z) (y = z)). Qed.
Lemma lem1383328 (a : Prop) (b : Prop) : (term55 a b) = (term56 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1383329 (y : real) (x : real) (z : real) : (term57 y x z) = (term58 y x z).
Proof. exact (@lem1383328 (term45 x y) (term45 x z)). Qed.
Lemma lem1383331 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1383332 (x : real) (y : real) : (term60 x y) = (x = y).
Proof. exact (@lem1383331 (x = y)). Qed.
Lemma lem1383333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1383334 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1383333) (@lem1383332 x y)). Qed.
Lemma lem1383336 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1383337 (x : real) (z : real) : (term60 x z) = (x = z).
Proof. exact (@lem1383336 (x = z)). Qed.
Lemma lem1383338 (y : real) (x : real) (z : real) : (term58 y x z) = (term63 y x z).
Proof. exact (MK_COMB (@lem1383334 x y) (@lem1383337 x z)). Qed.
Lemma lem1383339 (y : real) (x : real) (z : real) : (term57 y x z) = (term63 y x z).
Proof. exact (TRANS (@lem1383329 y x z) (@lem1383338 y x z)). Qed.
Lemma lem1383340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1383341 (y : real) (x : real) (z : real) : (term64 y x z) = (term65 y x z).
Proof. exact (MK_COMB (@lem1383340) (@lem1383339 y x z)). Qed.
Lemma lem1383342 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1383343 (x : real) (y : real) (z : real) : (term53 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1383341 y x z) (@lem1383342 y z)). Qed.
Lemma lem1383344 (x : real) (y : real) (z : real) : (term49 y x z) = (term66 x y z).
Proof. exact (TRANS (@lem1383326 x y z) (@lem1383343 x y z)). Qed.
Lemma lem1383346 (x : real) (h1 : term21) (h2 : term10) : term67 x.
Proof. exact (conj (@lem1383225 x h1) (@lem1383233 x h2)). Qed.
Lemma lem1383348 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (EQ_MP (@lem1383344 x y z) (@lem1383323 y x z)). Qed.
Lemma lem1383349 (x : real) : term68 x.
Proof. exact (@lem1383348 (term16 x) (term22 x) x). Qed.
Lemma lem1383352 (x : real) (h1 : term21) (h2 : term10) : (term22 x) = x.
Proof. exact (@lem1383349 x (@lem1383346 x h1 h2)). Qed.
Lemma lem1383353 (x : real) (h1 : term21) (h2 : term10) : term69 x.
Proof. exact (fun h0 : term29 x => @lem1383352 x h1 h2). Qed.
Lemma lem1383355 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1383356 (x : real) : (term69 x) = ((term22 x) = x).
Proof. exact (@lem1383355 ((term22 x) = x)). Qed.
Lemma lem1383357 (x : real) (h1 : term21) (h2 : term10) : (term22 x) = x.
Proof. exact (EQ_MP (@lem1383356 x) (@lem1383353 x h1 h2)). Qed.
Lemma lem1383360 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1383362 (x : real) : (term29 x) = (term70 x).
Proof. exact (@lem1383360 ((term22 x) = x)). Qed.
Lemma lem1383365 (x : real) (h1 : term29 x) : term70 x.
Proof. exact (EQ_MP (@lem1383362 x) (@lem1383174 x h1)). Qed.
Lemma lem1383368 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (@lem1383365 x h3 (@lem1383357 x h1 h2)). Qed.
Lemma lem1383369 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : term71.
Proof. exact (fun h0 : ~ False => @lem1383368 x h1 h2 h3). Qed.
Lemma lem1383371 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1383372 : term71 = False.
Proof. exact (@lem1383371 False). Qed.
Lemma lem1383373 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383372) (@lem1383369 x h1 h2 h3)). Qed.
Lemma lem1383374 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1383373 x h1 h2 h3) (fun h4 : False => @lem1383174 x h3)). Qed.
Lemma lem1383375 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383374 x h1 h2 h3) (@lem1383174 x h3)). Qed.
Lemma lem1383376 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1383375 x h1 h2 h3) (fun h4 : False => @lem1383159 x h3)). Qed.
Lemma lem1383377 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383376 x h1 h2 h3) (@lem1383159 x h3)). Qed.
Lemma lem1383378 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1383377 x h1 h2 h3) (fun h4 : False => @lem1383159 x h3)). Qed.
Lemma lem1383379 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383378 x h1 h2 h3) (@lem1383159 x h3)). Qed.
Lemma lem1383380 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1383379 x h1 h2 h3) (fun h4 : False => @lem1383155 h2)). Qed.
Lemma lem1383381 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383380 x h1 h2 h3) (@lem1383155 h2)). Qed.
Lemma lem1383382 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1383381 x h1 h2 h3) (fun h4 : False => @lem1383148 h1)). Qed.
Lemma lem1383383 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383382 x h1 h2 h3) (@lem1383148 h1)). Qed.
Lemma lem1383384 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1383383 x h1 h2 h3) (fun h4 : False => @lem1383138 x h3)). Qed.
Lemma lem1383385 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383384 x h1 h2 h3) (@lem1383138 x h3)). Qed.
Lemma lem1383386 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1383385 x h1 h2 h3) (fun h4 : False => @lem1383120 h2)). Qed.
Lemma lem1383387 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383386 x h1 h2 h3) (@lem1383120 h2)). Qed.
Lemma lem1383388 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1383387 x h1 h2 h3) (fun h4 : False => @lem1383101 h1)). Qed.
Lemma lem1383389 (x : real) (h1 : term21) (h2 : term10) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1383388 x h1 h2 h3) (@lem1383101 h1)). Qed.
Lemma lem1383390 (h1 : term21) (h2 : term10) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1383047 h3) (fun x : real => fun h0 : term31 x => @lem1383389 x h1 h2 h0)). Qed.
Lemma lem1383391 (h1 : term21) (h2 : term10) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1383390 h1 h2 h3) (fun h4 : False => @lem1383080 h2)). Qed.
Lemma lem1383392 (h1 : term21) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1383391 h1 h2 h3) (@lem1383080 h2)). Qed.
Lemma lem1383393 (h1 : term21) (h2 : term10) (h3 : term3) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1383392 h1 h2 h3) (fun h4 : False => @lem1383067 h1)). Qed.
Lemma lem1383394 (h1 : term21) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1383393 h1 h2 h3) (@lem1383067 h1)). Qed.
Lemma lem1383395 (h1 : term21) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1383394 h1 h0 h2). Qed.
Lemma lem1383396 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1383397 (h1 : term21) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1383396) (@lem1383395 h1 h2)). Qed.
Lemma lem1383398 (h1 : term3) : term13.
Proof. exact (fun h0 : term21 => @lem1383397 h0 h1). Qed.
Lemma lem1383399 : term15.
Proof. exact (fun h0 : term3 => @lem1383398 h0). Qed.
Lemma lem1383400 : term4.
Proof. exact (EQ_MP (@lem1383024) (@lem1383399)). Qed.
Lemma lem1383402 : term4.
Proof. exact (@lem1382932 (@lem1383400)). Qed.
Lemma lem1383403 (h1 : term3) : term12.
Proof. exact (@lem1383402 (@lem1382917 h1)). Qed.
Lemma lem1383404 (h1 : term3) : term8.
Proof. exact (@lem1383403 h1 (@lem1338712)). Qed.
Lemma lem1383405 (h1 : term3) : False.
Proof. exact (@lem1383404 h1 (@lem1338986)). Qed.
Lemma lem1383406 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1383405 h1) (fun h2 : False => @lem1382917 h1)). Qed.
Lemma lem1383407 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1383406 h1) (@lem1382917 h1)). Qed.
Lemma lem1383408 : term2.
Proof. exact (fun h0 : term3 => @lem1383407 h0). Qed.
Lemma lem1383409 : term1.
Proof. exact (EQ_MP (@lem1382916) (@lem1383408)). Qed.
