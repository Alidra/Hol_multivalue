Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_NEG_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_MUL_LINV_UNIQ_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import TREAL_INV_0_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm1340174_spec.
Require Import thm1361604_spec.
Require Import thm1362040_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1590038 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1590039 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1590038 h1 x). Qed.
Lemma lem1590040 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1590041 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1590040 x) (@lem1590039 x h1)). Qed.
Lemma lem1590042 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1590043 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1590041 x h1 (@lem1590042 x h2)). Qed.
Lemma lem1590044 (x : real) (h1 : term3 x) : term6 x.
Proof. exact (fun h0 : term0 => @lem1590043 x h0 h1). Qed.
Lemma lem1590045 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1590046 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1590044 x h2 (@lem1590045 h1)). Qed.
Lemma lem1590047 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1590046 x h1 h0). Qed.
Lemma lem1590048 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1590047 x h1). Qed.
Lemma lem1590049 : term7.
Proof. exact (fun h0 : term0 => @lem1590048 h0). Qed.
Lemma lem1590050 : term0.
Proof. exact (@lem1590049 (@lem1340174)). Qed.
Lemma lem1590051 (x : real) : term1 x.
Proof. exact (@lem1590050 x). Qed.
Lemma lem1590052 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1590054 (x : real) : term8 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1590055 (x : real) : (term8 x) = ((term9 x) = x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1590057 (x : real) : term10 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1590058 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1590059 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1590058 x) (@lem1590057 x)). Qed.
Lemma lem1590060 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1590059 x y). Qed.
Lemma lem1590061 (x : real) (y : real) : (term12 x y) = ((term13 x y) = (term14 x y)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1590063 (x : real) : term15 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1590064 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1590065 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem1590064 x) (@lem1590063 x)). Qed.
Lemma lem1590066 (x : real) (y : real) : term17 x y.
Proof. exact (@lem1590065 x y). Qed.
Lemma lem1590067 (x : real) (y : real) : (term17 x y) = ((term18 x y) = (term14 x y)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1590069 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1590070 (x : real) (h1 : term19) : term20 x.
Proof. exact (@lem1590069 h1 x). Qed.
Lemma lem1590071 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1590072 (x : real) (h1 : term19) : term21 x.
Proof. exact (EQ_MP (@lem1590071 x) (@lem1590070 x h1)). Qed.
Lemma lem1590073 (x : real) (y : real) (h1 : term19) : term22 x y.
Proof. exact (@lem1590072 x h1 y). Qed.
Lemma lem1590074 (y : real) (x : real) : (term22 x y) = (term23 y x).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1590075 (y : real) (x : real) (h1 : term19) : term23 y x.
Proof. exact (EQ_MP (@lem1590074 y x) (@lem1590073 x y h1)). Qed.
Lemma lem1590076 (x : real) (y : real) (h1 : (real_mul x y) = term5) : (real_mul x y) = term5.
Proof. exact (h1). Qed.
Lemma lem1590077 (x : real) (y : real) (h1 : term19) (h2 : (real_mul x y) = term5) : (real_inv y) = x.
Proof. exact (@lem1590075 y x h1 (@lem1590076 x y h2)). Qed.
Lemma lem1590078 (x : real) (y : real) (h1 : (real_mul x y) = term5) : term24 y x.
Proof. exact (fun h0 : term19 => @lem1590077 x y h0 h1). Qed.
Lemma lem1590079 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1590080 (x : real) (y : real) (h1 : term19) (h2 : (real_mul x y) = term5) : (real_inv y) = x.
Proof. exact (@lem1590078 x y h2 (@lem1590079 h1)). Qed.
Lemma lem1590081 (y : real) (x : real) (h1 : term19) : term23 y x.
Proof. exact (fun h0 : (real_mul x y) = term5 => @lem1590080 x y h1 h0). Qed.
Lemma lem1590082 (y : real) (h1 : term19) : term25 y.
Proof. exact (fun x : real => @lem1590081 y x h1). Qed.
Lemma lem1590083 (h1 : term19) : term26.
Proof. exact (fun y : real => @lem1590082 y h1). Qed.
Lemma lem1590084 : term27.
Proof. exact (fun h0 : term19 => @lem1590083 h0). Qed.
Lemma lem1590085 : term26.
Proof. exact (@lem1590084 (@lem1587738)). Qed.
Lemma lem1590086 (y : real) : term28 y.
Proof. exact (@lem1590085 y). Qed.
Lemma lem1590087 (y : real) : (term28 y) = (term25 y).
Proof. exact (eq_refl (term28 y)). Qed.
Lemma lem1590088 (y : real) : term25 y.
Proof. exact (EQ_MP (@lem1590087 y) (@lem1590086 y)). Qed.
Lemma lem1590089 (y : real) (x : real) : term29 y x.
Proof. exact (@lem1590088 y x). Qed.
Lemma lem1590090 (y : real) (x : real) : (term29 y x) = (term23 y x).
Proof. exact (eq_refl (term29 y x)). Qed.
Lemma lem1590092 (x : real) : term30 x.
Proof. exact (@lem9784 (x = term31)). Qed.
Lemma lem1590093 (x : real) : (term30 x) = (term32 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1590094 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1590093 x) (@lem1590092 x)). Qed.
Lemma lem1590096 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1590100 (x : real) (h1 : x = term31) : x = term31.
Proof. exact (h1). Qed.
Lemma lem1590101 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1590102 (x : real) (h1 : x = term31) : (real_neg x) = term33.
Proof. exact (MK_COMB (@lem1590101) (@lem1590100 x h1)). Qed.
Lemma lem1590104 : term33 = term31.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
Lemma lem1590105 (x : real) (h1 : x = term31) : (real_neg x) = term31.
Proof. exact (TRANS (@lem1590102 x h1) (@lem1590104)). Qed.
Lemma lem1590106 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1590107 (x : real) (h1 : x = term31) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem1590106) (@lem1590105 x h1)). Qed.
Lemma lem1590109 : term35 = term31.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1590110 (x : real) (h1 : x = term31) : (term34 x) = term31.
Proof. exact (TRANS (@lem1590107 x h1) (@lem1590109)). Qed.
Lemma lem1590111 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1590112 (x : real) (h1 : x = term31) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1590111) (@lem1590110 x h1)). Qed.
Lemma lem1590114 (x : real) (h1 : x = term31) : x = term31.
Proof. exact (h1). Qed.
Lemma lem1590115 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1590116 (x : real) (h1 : x = term31) : (real_inv x) = term35.
Proof. exact (MK_COMB (@lem1590115) (@lem1590114 x h1)). Qed.
Lemma lem1590118 : term35 = term31.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1590119 (x : real) (h1 : x = term31) : (real_inv x) = term31.
Proof. exact (TRANS (@lem1590116 x h1) (@lem1590118)). Qed.
Lemma lem1590120 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1590121 (x : real) (h1 : x = term31) : (term38 x) = term33.
Proof. exact (MK_COMB (@lem1590120) (@lem1590119 x h1)). Qed.
Lemma lem1590123 : term33 = term31.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
Lemma lem1590124 (x : real) (h1 : x = term31) : (term38 x) = term31.
Proof. exact (TRANS (@lem1590121 x h1) (@lem1590123)). Qed.
Lemma lem1590125 (x : real) (h1 : x = term31) : ((term34 x) = (term38 x)) = (term31 = term31).
Proof. exact (MK_COMB (@lem1590112 x h1) (@lem1590124 x h1)). Qed.
Lemma lem1590127 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1590128 (x : real) : (x = x) = True.
Proof. exact (@lem1590127 real x). Qed.
Lemma lem1590129 : (term31 = term31) = True.
Proof. exact (@lem1590128 term31). Qed.
Lemma lem1590130 (x : real) (h1 : x = term31) : ((term34 x) = (term38 x)) = True.
Proof. exact (TRANS (@lem1590125 x h1) (@lem1590129)). Qed.
Lemma lem1590131 (x : real) (h1 : x = term31) : True = ((term34 x) = (term38 x)).
Proof. exact (SYM (@lem1590130 x h1)). Qed.
Lemma lem1590132 (x : real) (h1 : x = term31) : (term34 x) = (term38 x).
Proof. exact (EQ_MP (@lem1590131 x h1) (@lem0)). Qed.
Lemma lem1590151 (y : real) (x : real) : term23 y x.
Proof. exact (EQ_MP (@lem1590090 y x) (@lem1590089 y x)). Qed.
Lemma lem1590152 (x : real) : term39 x.
Proof. exact (@lem1590151 (real_neg x) (term38 x)). Qed.
Lemma lem1590156 (x : real) (y : real) : (term18 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem1590067 x y) (@lem1590066 x y)). Qed.
Lemma lem1590157 (x : real) : (term40 x) = (term41 x).
Proof. exact (@lem1590156 (real_inv x) (real_neg x)). Qed.
Lemma lem1590159 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem1590061 x y) (@lem1590060 x y)). Qed.
Lemma lem1590160 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1590159 (real_inv x) x). Qed.
Lemma lem1590161 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1590162 (x : real) : (term41 x) = (term44 x).
Proof. exact (MK_COMB (@lem1590161) (@lem1590160 x)). Qed.
Lemma lem1590164 (x : real) : (term9 x) = x.
Proof. exact (EQ_MP (@lem1590055 x) (@lem1590054 x)). Qed.
Lemma lem1590165 (x : real) : (term44 x) = (term4 x).
Proof. exact (@lem1590164 (term4 x)). Qed.
Lemma lem1590166 (x : real) : (term41 x) = (term4 x).
Proof. exact (TRANS (@lem1590162 x) (@lem1590165 x)). Qed.
Lemma lem1590167 (x : real) : (term40 x) = (term4 x).
Proof. exact (TRANS (@lem1590157 x) (@lem1590166 x)). Qed.
Lemma lem1590168 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1590169 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1590168) (@lem1590167 x)). Qed.
Lemma lem1590170 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1590171 (x : real) : ((term40 x) = term5) = ((term4 x) = term5).
Proof. exact (MK_COMB (@lem1590169 x) (@lem1590170)). Qed.
Lemma lem1590174 (x : real) : ((term4 x) = term5) = ((term40 x) = term5).
Proof. exact (SYM (@lem1590171 x)). Qed.
Lemma lem1590176 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1590052 x) (@lem1590051 x)). Qed.
Lemma lem1590177 (x : real) : term47 x.
Proof. exact (@lem82 (x = term31)). Qed.
Lemma lem1590191 (x : real) (h1 : term3 x) : (x = term31) = False.
Proof. exact (@lem1590177 x (@lem1590096 x h1)). Qed.
Lemma lem1590192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1590193 (x : real) (h1 : term3 x) : (term3 x) = (~ False).
Proof. exact (MK_COMB (@lem1590192) (@lem1590191 x h1)). Qed.
Lemma lem1590195 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1590196 (x : real) (h1 : term3 x) : (term3 x) = True.
Proof. exact (TRANS (@lem1590193 x h1) (@lem1590195)). Qed.
Lemma lem1590197 (x : real) (h1 : term3 x) : True = (term3 x).
Proof. exact (SYM (@lem1590196 x h1)). Qed.
Lemma lem1590198 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (EQ_MP (@lem1590197 x h1) (@lem0)). Qed.
Lemma lem1590199 (x : real) (h1 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1590176 x (@lem1590198 x h1)). Qed.
Lemma lem1590200 (x : real) (h1 : term3 x) : (term40 x) = term5.
Proof. exact (EQ_MP (@lem1590174 x) (@lem1590199 x h1)). Qed.
Lemma lem1590202 (x : real) (h1 : term3 x) : (term34 x) = (term38 x).
Proof. exact (@lem1590152 x (@lem1590200 x h1)). Qed.
Lemma lem1590203 (x : real) : (term34 x) = (term38 x).
Proof. exact (or_elim (@lem1590094 x) (fun h0 : x = term31 => @lem1590132 x h0) (fun h0 : term3 x => @lem1590202 x h0)). Qed.
Lemma lem1590208 : term48.
Proof. exact (fun x : real => @lem1590203 x). Qed.
