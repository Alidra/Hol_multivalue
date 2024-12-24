Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_WELLDEF_term_abbrevs.
Require Import TREAL_EQ_TRANS_spec.
Require Import TREAL_MUL_SYM_EQ_spec.
Require Import TREAL_MUL_WELLDEFR_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1334048 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1334049 (x1 : prod hreal hreal) (h1 : term0) : term1 x1.
Proof. exact (@lem1334048 h1 x1). Qed.
Lemma lem1334050 (x1 : prod hreal hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1334051 (x1 : prod hreal hreal) (h1 : term0) : term2 x1.
Proof. exact (EQ_MP (@lem1334050 x1) (@lem1334049 x1 h1)). Qed.
Lemma lem1334052 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term3 x1 x2.
Proof. exact (@lem1334051 x1 h1 x2). Qed.
Lemma lem1334053 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term3 x1 x2) = (term4 x1 x2).
Proof. exact (eq_refl (term3 x1 x2)). Qed.
Lemma lem1334054 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term4 x1 x2.
Proof. exact (EQ_MP (@lem1334053 x1 x2) (@lem1334052 x1 x2 h1)). Qed.
Lemma lem1334055 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term5 x1 x2 y.
Proof. exact (@lem1334054 x1 x2 h1 y). Qed.
Lemma lem1334056 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : (term5 x1 x2 y) = (term6 x1 x2 y).
Proof. exact (eq_refl (term5 x1 x2 y)). Qed.
Lemma lem1334057 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1334056 x1 x2 y) (@lem1334055 x1 x2 y h1)). Qed.
Lemma lem1334058 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x1 x2.
Proof. exact (h1). Qed.
Lemma lem1334059 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) (h2 : treal_eq x1 x2) : term7 x1 x2 y.
Proof. exact (@lem1334057 x1 x2 y h1 (@lem1334058 x1 x2 h2)). Qed.
Lemma lem1334060 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : term8 x1 x2 y.
Proof. exact (fun h0 : term0 => @lem1334059 y x1 x2 h0 h1). Qed.
Lemma lem1334061 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1334062 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) (h2 : treal_eq x1 x2) : term7 x1 x2 y.
Proof. exact (@lem1334060 y x1 x2 h2 (@lem1334061 h1)). Qed.
Lemma lem1334063 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term6 x1 x2 y.
Proof. exact (fun h0 : treal_eq x1 x2 => @lem1334062 y x1 x2 h1 h0). Qed.
Lemma lem1334064 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term4 x1 x2.
Proof. exact (fun y : prod hreal hreal => @lem1334063 x1 x2 y h1). Qed.
Lemma lem1334065 (x1 : prod hreal hreal) (h1 : term0) : term2 x1.
Proof. exact (fun x2 : prod hreal hreal => @lem1334064 x1 x2 h1). Qed.
Lemma lem1334066 (h1 : term0) : term0.
Proof. exact (fun x1 : prod hreal hreal => @lem1334065 x1 h1). Qed.
Lemma lem1334067 : term9.
Proof. exact (fun h0 : term0 => @lem1334066 h0). Qed.
Lemma lem1334068 : term0.
Proof. exact (@lem1334067 (@lem1334047)). Qed.
Lemma lem1334069 (x1 : prod hreal hreal) : term1 x1.
Proof. exact (@lem1334068 x1). Qed.
Lemma lem1334070 (x1 : prod hreal hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1334071 (x1 : prod hreal hreal) : term2 x1.
Proof. exact (EQ_MP (@lem1334070 x1) (@lem1334069 x1)). Qed.
Lemma lem1334072 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term3 x1 x2.
Proof. exact (@lem1334071 x1 x2). Qed.
Lemma lem1334073 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term3 x1 x2) = (term4 x1 x2).
Proof. exact (eq_refl (term3 x1 x2)). Qed.
Lemma lem1334074 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term4 x1 x2.
Proof. exact (EQ_MP (@lem1334073 x1 x2) (@lem1334072 x1 x2)). Qed.
Lemma lem1334075 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term5 x1 x2 y.
Proof. exact (@lem1334074 x1 x2 y). Qed.
Lemma lem1334076 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : (term5 x1 x2 y) = (term6 x1 x2 y).
Proof. exact (eq_refl (term5 x1 x2 y)). Qed.
Lemma lem1334078 (x : prod hreal hreal) : term10 x.
Proof. exact (@lem1327751 x). Qed.
Lemma lem1334079 (x : prod hreal hreal) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1334080 (x : prod hreal hreal) : term11 x.
Proof. exact (EQ_MP (@lem1334079 x) (@lem1334078 x)). Qed.
Lemma lem1334081 (x : prod hreal hreal) (y : prod hreal hreal) : term12 x y.
Proof. exact (@lem1334080 x y). Qed.
Lemma lem1334082 (y : prod hreal hreal) (x : prod hreal hreal) : (term12 x y) = ((treal_mul x y) = (treal_mul y x)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1334084 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1334085 (x : prod hreal hreal) (h1 : term13) : term14 x.
Proof. exact (@lem1334084 h1 x). Qed.
Lemma lem1334086 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1334087 (x : prod hreal hreal) (h1 : term13) : term15 x.
Proof. exact (EQ_MP (@lem1334086 x) (@lem1334085 x h1)). Qed.
Lemma lem1334088 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term13) : term16 x y.
Proof. exact (@lem1334087 x h1 y). Qed.
Lemma lem1334089 (y : prod hreal hreal) (x : prod hreal hreal) : (term16 x y) = (term17 y x).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1334090 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term13) : term17 y x.
Proof. exact (EQ_MP (@lem1334089 y x) (@lem1334088 x y h1)). Qed.
Lemma lem1334091 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term18 y x z.
Proof. exact (@lem1334090 y x h1 z). Qed.
Lemma lem1334092 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term18 y x z) = (term19 y x z).
Proof. exact (eq_refl (term18 y x z)). Qed.
Lemma lem1334093 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term19 y x z.
Proof. exact (EQ_MP (@lem1334092 y x z) (@lem1334091 y x z h1)). Qed.
Lemma lem1334094 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term20 x y z) : term20 x y z.
Proof. exact (h1). Qed.
Lemma lem1334095 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) (h2 : term20 x y z) : treal_eq x z.
Proof. exact (@lem1334093 y x z h1 (@lem1334094 x y z h2)). Qed.
Lemma lem1334096 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term20 x y z) : term21 x z.
Proof. exact (fun h0 : term13 => @lem1334095 x y z h0 h1). Qed.
Lemma lem1334097 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term22 x z) : term22 x z.
Proof. exact (h1). Qed.
Lemma lem1334098 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term22 x z) : term21 x z.
Proof. exact (ex_elim (@lem1334097 x z h1) (fun y : prod hreal hreal => fun h0 : term23 x z y => @lem1334096 x y z h0)). Qed.
Lemma lem1334099 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1334100 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) (h2 : term22 x z) : treal_eq x z.
Proof. exact (@lem1334098 x z h2 (@lem1334099 h1)). Qed.
Lemma lem1334101 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term24 x z.
Proof. exact (fun h0 : term22 x z => @lem1334100 x z h1 h0). Qed.
Lemma lem1334102 (x : prod hreal hreal) (h1 : term13) : term25 x.
Proof. exact (fun z : prod hreal hreal => @lem1334101 x z h1). Qed.
Lemma lem1334103 (h1 : term13) : term26.
Proof. exact (fun x : prod hreal hreal => @lem1334102 x h1). Qed.
Lemma lem1334104 : term27.
Proof. exact (fun h0 : term13 => @lem1334103 h0). Qed.
Lemma lem1334105 : term26.
Proof. exact (@lem1334104 (@lem1326778)). Qed.
Lemma lem1334106 (x : prod hreal hreal) : term28 x.
Proof. exact (@lem1334105 x). Qed.
Lemma lem1334107 (x : prod hreal hreal) : (term28 x) = (term25 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1334108 (x : prod hreal hreal) : term25 x.
Proof. exact (EQ_MP (@lem1334107 x) (@lem1334106 x)). Qed.
Lemma lem1334109 (x : prod hreal hreal) (z : prod hreal hreal) : term29 x z.
Proof. exact (@lem1334108 x z). Qed.
Lemma lem1334110 (x : prod hreal hreal) (z : prod hreal hreal) : (term29 x z) = (term24 x z).
Proof. exact (eq_refl (term29 x z)). Qed.
Lemma lem1334112 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term30 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1334114 (x : prod hreal hreal) (z : prod hreal hreal) : term24 x z.
Proof. exact (EQ_MP (@lem1334110 x z) (@lem1334109 x z)). Qed.
Lemma lem1334115 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term31 x1 y1 x2 y2.
Proof. exact (@lem1334114 (treal_mul x1 y1) (treal_mul x2 y2)). Qed.
Lemma lem1334117 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_mul x y) = (treal_mul y x).
Proof. exact (EQ_MP (@lem1334082 y x) (@lem1334081 x y)). Qed.
Lemma lem1334118 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (treal_mul x1 y1) = (treal_mul y1 x1).
Proof. exact (@lem1334117 y1 x1). Qed.
Lemma lem1334119 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1334120 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term32 x1 y1) = (term32 y1 x1).
Proof. exact (MK_COMB (@lem1334119) (@lem1334118 y1 x1)). Qed.
Lemma lem1334122 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_mul x y) = (treal_mul y x).
Proof. exact (EQ_MP (@lem1334082 y x) (@lem1334081 x y)). Qed.
Lemma lem1334123 (y2 : prod hreal hreal) (x1 : prod hreal hreal) : (treal_mul x1 y2) = (treal_mul y2 x1).
Proof. exact (@lem1334122 y2 x1). Qed.
Lemma lem1334124 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) : (term33 y1 x1 y2) = (term7 y1 y2 x1).
Proof. exact (MK_COMB (@lem1334120 y1 x1) (@lem1334123 y2 x1)). Qed.
Lemma lem1334125 (y1 : prod hreal hreal) (x1 : prod hreal hreal) (y2 : prod hreal hreal) : (term7 y1 y2 x1) = (term33 y1 x1 y2).
Proof. exact (SYM (@lem1334124 y1 y2 x1)). Qed.
Lemma lem1334127 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1334076 x1 x2 y) (@lem1334075 x1 x2 y)). Qed.
Lemma lem1334128 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) : term6 y1 y2 x1.
Proof. exact (@lem1334127 y1 y2 x1). Qed.
Lemma lem1334130 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1334076 x1 x2 y) (@lem1334075 x1 x2 y)). Qed.
Lemma lem1334131 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term6 x1 x2 y2.
Proof. exact (@lem1334130 x1 x2 y2). Qed.
Lemma lem1334132 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq y1 y2.
Proof. exact (proj2 (@lem1334112 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334133 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_eq y1 y2) = ((treal_eq y1 y2) = True).
Proof. exact (@lem7 (treal_eq y1 y2)). Qed.
Lemma lem1334139 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : (treal_eq y1 y2) = True.
Proof. exact (EQ_MP (@lem1334133 y1 y2) (@lem1334132 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334140 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : True = (treal_eq y1 y2).
Proof. exact (SYM (@lem1334139 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334141 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq y1 y2.
Proof. exact (EQ_MP (@lem1334140 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1334145 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq x1 x2.
Proof. exact (proj1 (@lem1334112 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334146 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (treal_eq x1 x2) = ((treal_eq x1 x2) = True).
Proof. exact (@lem7 (treal_eq x1 x2)). Qed.
Lemma lem1334149 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : (treal_eq x1 x2) = True.
Proof. exact (EQ_MP (@lem1334146 x1 x2) (@lem1334145 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334150 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : True = (treal_eq x1 x2).
Proof. exact (SYM (@lem1334149 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334151 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq x1 x2.
Proof. exact (EQ_MP (@lem1334150 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1334152 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term7 x1 x2 y2.
Proof. exact (@lem1334131 x1 x2 y2 (@lem1334151 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334153 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term7 y1 y2 x1.
Proof. exact (@lem1334128 y1 y2 x1 (@lem1334141 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334154 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term33 y1 x1 y2.
Proof. exact (EQ_MP (@lem1334125 y1 x1 y2) (@lem1334153 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334155 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term34 y1 x1 x2 y2.
Proof. exact (conj (@lem1334154 x1 x2 y1 y2 h1) (@lem1334152 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334156 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term35 x1 y1 x2 y2.
Proof. exact (ex_intro (term36 x1 y1 x2 y2) (treal_mul x1 y2) (@lem1334155 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334157 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term37 x1 y1 x2 y2.
Proof. exact (@lem1334115 x1 y1 x2 y2 (@lem1334156 x1 x2 y1 y2 h1)). Qed.
Lemma lem1334158 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term38 x1 y1 x2 y2.
Proof. exact (fun h0 : term30 x1 x2 y1 y2 => @lem1334157 x1 x2 y1 y2 h0). Qed.
Lemma lem1334163 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term39 x1 y1 x2.
Proof. exact (fun y2 : prod hreal hreal => @lem1334158 x1 y1 x2 y2). Qed.
Lemma lem1334168 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term40 x1 x2.
Proof. exact (fun y1 : prod hreal hreal => @lem1334163 x1 y1 x2). Qed.
Lemma lem1334173 (x1 : prod hreal hreal) : term41 x1.
Proof. exact (fun x2 : prod hreal hreal => @lem1334168 x1 x2). Qed.
Lemma lem1334178 : term42.
Proof. exact (fun x1 : prod hreal hreal => @lem1334173 x1). Qed.
