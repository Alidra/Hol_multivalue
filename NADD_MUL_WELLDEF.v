Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_WELLDEF_term_abbrevs.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_MUL_SYM_spec.
Require Import NADD_MUL_WELLDEF_LEMMA_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Lemma lem1279060 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1279061 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1279060 h1 x). Qed.
Lemma lem1279062 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1279063 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1279062 x) (@lem1279061 x h1)). Qed.
Lemma lem1279064 (x : nadd) (y : nadd) (h1 : term0) : term3 x y.
Proof. exact (@lem1279063 x h1 y). Qed.
Lemma lem1279065 (y : nadd) (x : nadd) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1279066 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1279065 y x) (@lem1279064 x y h1)). Qed.
Lemma lem1279067 (y : nadd) (x : nadd) (y' : nadd) (h1 : term0) : term5 y x y'.
Proof. exact (@lem1279066 y x h1 y'). Qed.
Lemma lem1279068 (y : nadd) (x : nadd) (y' : nadd) : (term5 y x y') = (term6 y x y').
Proof. exact (eq_refl (term5 y x y')). Qed.
Lemma lem1279069 (y : nadd) (x : nadd) (y' : nadd) (h1 : term0) : term6 y x y'.
Proof. exact (EQ_MP (@lem1279068 y x y') (@lem1279067 y x y' h1)). Qed.
Lemma lem1279070 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : nadd_eq y y'.
Proof. exact (h1). Qed.
Lemma lem1279071 (x : nadd) (y : nadd) (y' : nadd) (h1 : term0) (h2 : nadd_eq y y') : term7 y x y'.
Proof. exact (@lem1279069 y x y' h1 (@lem1279070 y y' h2)). Qed.
Lemma lem1279072 (x : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : term8 y x y'.
Proof. exact (fun h0 : term0 => @lem1279071 x y y' h0 h1). Qed.
Lemma lem1279073 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1279074 (x : nadd) (y : nadd) (y' : nadd) (h1 : term0) (h2 : nadd_eq y y') : term7 y x y'.
Proof. exact (@lem1279072 x y y' h2 (@lem1279073 h1)). Qed.
Lemma lem1279075 (y : nadd) (x : nadd) (y' : nadd) (h1 : term0) : term6 y x y'.
Proof. exact (fun h0 : nadd_eq y y' => @lem1279074 x y y' h1 h0). Qed.
Lemma lem1279076 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (fun y' : nadd => @lem1279075 y x y' h1). Qed.
Lemma lem1279077 (y : nadd) (h1 : term0) : term9 y.
Proof. exact (fun x : nadd => @lem1279076 y x h1). Qed.
Lemma lem1279078 (h1 : term0) : term10.
Proof. exact (fun y : nadd => @lem1279077 y h1). Qed.
Lemma lem1279079 : term11.
Proof. exact (fun h0 : term0 => @lem1279078 h0). Qed.
Lemma lem1279080 : term10.
Proof. exact (@lem1279079 (@lem1279059)). Qed.
Lemma lem1279081 (y : nadd) : term12 y.
Proof. exact (@lem1279080 y). Qed.
Lemma lem1279082 (y : nadd) : (term12 y) = (term9 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem1279083 (y : nadd) : term9 y.
Proof. exact (EQ_MP (@lem1279082 y) (@lem1279081 y)). Qed.
Lemma lem1279084 (y : nadd) (x : nadd) : term13 y x.
Proof. exact (@lem1279083 y x). Qed.
Lemma lem1279085 (y : nadd) (x : nadd) : (term13 y x) = (term4 y x).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1279086 (y : nadd) (x : nadd) : term4 y x.
Proof. exact (EQ_MP (@lem1279085 y x) (@lem1279084 y x)). Qed.
Lemma lem1279087 (y : nadd) (x : nadd) (y' : nadd) : term5 y x y'.
Proof. exact (@lem1279086 y x y'). Qed.
Lemma lem1279088 (y : nadd) (x : nadd) (y' : nadd) : (term5 y x y') = (term6 y x y').
Proof. exact (eq_refl (term5 y x y')). Qed.
Lemma lem1279090 (x : nadd) : term14 x.
Proof. exact (@lem1278399 x). Qed.
Lemma lem1279091 (x : nadd) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1279092 (x : nadd) : term15 x.
Proof. exact (EQ_MP (@lem1279091 x) (@lem1279090 x)). Qed.
Lemma lem1279093 (x : nadd) (y : nadd) : term16 x y.
Proof. exact (@lem1279092 x y). Qed.
Lemma lem1279094 (y : nadd) (x : nadd) : (term16 x y) = (term17 y x).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1279095 (y : nadd) (x : nadd) : term17 y x.
Proof. exact (EQ_MP (@lem1279094 y x) (@lem1279093 x y)). Qed.
Lemma lem1279096 (y : nadd) (x : nadd) : (term17 y x) = ((term17 y x) = True).
Proof. exact (@lem7 (term17 y x)). Qed.
Lemma lem1279098 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279099 (x : nadd) (h1 : term18) : term19 x.
Proof. exact (@lem1279098 h1 x). Qed.
Lemma lem1279100 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1279101 (x : nadd) (h1 : term18) : term20 x.
Proof. exact (EQ_MP (@lem1279100 x) (@lem1279099 x h1)). Qed.
Lemma lem1279102 (x : nadd) (y : nadd) (h1 : term18) : term21 x y.
Proof. exact (@lem1279101 x h1 y). Qed.
Lemma lem1279103 (y : nadd) (x : nadd) : (term21 x y) = (term22 y x).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1279104 (y : nadd) (x : nadd) (h1 : term18) : term22 y x.
Proof. exact (EQ_MP (@lem1279103 y x) (@lem1279102 x y h1)). Qed.
Lemma lem1279105 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term23 y x z.
Proof. exact (@lem1279104 y x h1 z). Qed.
Lemma lem1279106 (y : nadd) (x : nadd) (z : nadd) : (term23 y x z) = (term24 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1279107 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term24 y x z.
Proof. exact (EQ_MP (@lem1279106 y x z) (@lem1279105 y x z h1)). Qed.
Lemma lem1279108 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term25 x y z.
Proof. exact (h1). Qed.
Lemma lem1279109 (x : nadd) (y : nadd) (z : nadd) (h1 : term18) (h2 : term25 x y z) : nadd_eq x z.
Proof. exact (@lem1279107 y x z h1 (@lem1279108 x y z h2)). Qed.
Lemma lem1279110 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term26 x z.
Proof. exact (fun h0 : term18 => @lem1279109 x y z h0 h1). Qed.
Lemma lem1279111 (x : nadd) (z : nadd) (h1 : term27 x z) : term27 x z.
Proof. exact (h1). Qed.
Lemma lem1279112 (x : nadd) (z : nadd) (h1 : term27 x z) : term26 x z.
Proof. exact (ex_elim (@lem1279111 x z h1) (fun y : nadd => fun h0 : term28 x z y => @lem1279110 x y z h0)). Qed.
Lemma lem1279113 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279114 (x : nadd) (z : nadd) (h1 : term18) (h2 : term27 x z) : nadd_eq x z.
Proof. exact (@lem1279112 x z h2 (@lem1279113 h1)). Qed.
Lemma lem1279115 (x : nadd) (z : nadd) (h1 : term18) : term29 x z.
Proof. exact (fun h0 : term27 x z => @lem1279114 x z h1 h0). Qed.
Lemma lem1279116 (x : nadd) (h1 : term18) : term30 x.
Proof. exact (fun z : nadd => @lem1279115 x z h1). Qed.
Lemma lem1279117 (h1 : term18) : term31.
Proof. exact (fun x : nadd => @lem1279116 x h1). Qed.
Lemma lem1279118 : term32.
Proof. exact (fun h0 : term18 => @lem1279117 h0). Qed.
Lemma lem1279119 : term31.
Proof. exact (@lem1279118 (@lem1268295)). Qed.
Lemma lem1279120 (x : nadd) : term33 x.
Proof. exact (@lem1279119 x). Qed.
Lemma lem1279121 (x : nadd) : (term33 x) = (term30 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1279122 (x : nadd) : term30 x.
Proof. exact (EQ_MP (@lem1279121 x) (@lem1279120 x)). Qed.
Lemma lem1279123 (x : nadd) (z : nadd) : term34 x z.
Proof. exact (@lem1279122 x z). Qed.
Lemma lem1279124 (x : nadd) (z : nadd) : (term34 x z) = (term29 x z).
Proof. exact (eq_refl (term34 x z)). Qed.
Lemma lem1279126 (x : nadd) : term14 x.
Proof. exact (@lem1278399 x). Qed.
Lemma lem1279127 (x : nadd) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1279128 (x : nadd) : term15 x.
Proof. exact (EQ_MP (@lem1279127 x) (@lem1279126 x)). Qed.
Lemma lem1279129 (x : nadd) (y : nadd) : term16 x y.
Proof. exact (@lem1279128 x y). Qed.
Lemma lem1279130 (y : nadd) (x : nadd) : (term16 x y) = (term17 y x).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1279131 (y : nadd) (x : nadd) : term17 y x.
Proof. exact (EQ_MP (@lem1279130 y x) (@lem1279129 x y)). Qed.
Lemma lem1279132 (y : nadd) (x : nadd) : (term17 y x) = ((term17 y x) = True).
Proof. exact (@lem7 (term17 y x)). Qed.
Lemma lem1279134 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279135 (x : nadd) (h1 : term18) : term19 x.
Proof. exact (@lem1279134 h1 x). Qed.
Lemma lem1279136 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1279137 (x : nadd) (h1 : term18) : term20 x.
Proof. exact (EQ_MP (@lem1279136 x) (@lem1279135 x h1)). Qed.
Lemma lem1279138 (x : nadd) (y : nadd) (h1 : term18) : term21 x y.
Proof. exact (@lem1279137 x h1 y). Qed.
Lemma lem1279139 (y : nadd) (x : nadd) : (term21 x y) = (term22 y x).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1279140 (y : nadd) (x : nadd) (h1 : term18) : term22 y x.
Proof. exact (EQ_MP (@lem1279139 y x) (@lem1279138 x y h1)). Qed.
Lemma lem1279141 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term23 y x z.
Proof. exact (@lem1279140 y x h1 z). Qed.
Lemma lem1279142 (y : nadd) (x : nadd) (z : nadd) : (term23 y x z) = (term24 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1279143 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term24 y x z.
Proof. exact (EQ_MP (@lem1279142 y x z) (@lem1279141 y x z h1)). Qed.
Lemma lem1279144 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term25 x y z.
Proof. exact (h1). Qed.
Lemma lem1279145 (x : nadd) (y : nadd) (z : nadd) (h1 : term18) (h2 : term25 x y z) : nadd_eq x z.
Proof. exact (@lem1279143 y x z h1 (@lem1279144 x y z h2)). Qed.
Lemma lem1279146 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term26 x z.
Proof. exact (fun h0 : term18 => @lem1279145 x y z h0 h1). Qed.
Lemma lem1279147 (x : nadd) (z : nadd) (h1 : term27 x z) : term27 x z.
Proof. exact (h1). Qed.
Lemma lem1279148 (x : nadd) (z : nadd) (h1 : term27 x z) : term26 x z.
Proof. exact (ex_elim (@lem1279147 x z h1) (fun y : nadd => fun h0 : term28 x z y => @lem1279146 x y z h0)). Qed.
Lemma lem1279149 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279150 (x : nadd) (z : nadd) (h1 : term18) (h2 : term27 x z) : nadd_eq x z.
Proof. exact (@lem1279148 x z h2 (@lem1279149 h1)). Qed.
Lemma lem1279151 (x : nadd) (z : nadd) (h1 : term18) : term29 x z.
Proof. exact (fun h0 : term27 x z => @lem1279150 x z h1 h0). Qed.
Lemma lem1279152 (x : nadd) (h1 : term18) : term30 x.
Proof. exact (fun z : nadd => @lem1279151 x z h1). Qed.
Lemma lem1279153 (h1 : term18) : term31.
Proof. exact (fun x : nadd => @lem1279152 x h1). Qed.
Lemma lem1279154 : term32.
Proof. exact (fun h0 : term18 => @lem1279153 h0). Qed.
Lemma lem1279155 : term31.
Proof. exact (@lem1279154 (@lem1268295)). Qed.
Lemma lem1279156 (x : nadd) : term33 x.
Proof. exact (@lem1279155 x). Qed.
Lemma lem1279157 (x : nadd) : (term33 x) = (term30 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1279158 (x : nadd) : term30 x.
Proof. exact (EQ_MP (@lem1279157 x) (@lem1279156 x)). Qed.
Lemma lem1279159 (x : nadd) (z : nadd) : term34 x z.
Proof. exact (@lem1279158 x z). Qed.
Lemma lem1279160 (x : nadd) (z : nadd) : (term34 x z) = (term29 x z).
Proof. exact (eq_refl (term34 x z)). Qed.
Lemma lem1279162 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279163 (x : nadd) (h1 : term18) : term19 x.
Proof. exact (@lem1279162 h1 x). Qed.
Lemma lem1279164 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1279165 (x : nadd) (h1 : term18) : term20 x.
Proof. exact (EQ_MP (@lem1279164 x) (@lem1279163 x h1)). Qed.
Lemma lem1279166 (x : nadd) (y : nadd) (h1 : term18) : term21 x y.
Proof. exact (@lem1279165 x h1 y). Qed.
Lemma lem1279167 (y : nadd) (x : nadd) : (term21 x y) = (term22 y x).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1279168 (y : nadd) (x : nadd) (h1 : term18) : term22 y x.
Proof. exact (EQ_MP (@lem1279167 y x) (@lem1279166 x y h1)). Qed.
Lemma lem1279169 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term23 y x z.
Proof. exact (@lem1279168 y x h1 z). Qed.
Lemma lem1279170 (y : nadd) (x : nadd) (z : nadd) : (term23 y x z) = (term24 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1279171 (y : nadd) (x : nadd) (z : nadd) (h1 : term18) : term24 y x z.
Proof. exact (EQ_MP (@lem1279170 y x z) (@lem1279169 y x z h1)). Qed.
Lemma lem1279172 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term25 x y z.
Proof. exact (h1). Qed.
Lemma lem1279173 (x : nadd) (y : nadd) (z : nadd) (h1 : term18) (h2 : term25 x y z) : nadd_eq x z.
Proof. exact (@lem1279171 y x z h1 (@lem1279172 x y z h2)). Qed.
Lemma lem1279174 (x : nadd) (y : nadd) (z : nadd) (h1 : term25 x y z) : term26 x z.
Proof. exact (fun h0 : term18 => @lem1279173 x y z h0 h1). Qed.
Lemma lem1279175 (x : nadd) (z : nadd) (h1 : term27 x z) : term27 x z.
Proof. exact (h1). Qed.
Lemma lem1279176 (x : nadd) (z : nadd) (h1 : term27 x z) : term26 x z.
Proof. exact (ex_elim (@lem1279175 x z h1) (fun y : nadd => fun h0 : term28 x z y => @lem1279174 x y z h0)). Qed.
Lemma lem1279177 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1279178 (x : nadd) (z : nadd) (h1 : term18) (h2 : term27 x z) : nadd_eq x z.
Proof. exact (@lem1279176 x z h2 (@lem1279177 h1)). Qed.
Lemma lem1279179 (x : nadd) (z : nadd) (h1 : term18) : term29 x z.
Proof. exact (fun h0 : term27 x z => @lem1279178 x z h1 h0). Qed.
Lemma lem1279180 (x : nadd) (h1 : term18) : term30 x.
Proof. exact (fun z : nadd => @lem1279179 x z h1). Qed.
Lemma lem1279181 (h1 : term18) : term31.
Proof. exact (fun x : nadd => @lem1279180 x h1). Qed.
Lemma lem1279182 : term32.
Proof. exact (fun h0 : term18 => @lem1279181 h0). Qed.
Lemma lem1279183 : term31.
Proof. exact (@lem1279182 (@lem1268295)). Qed.
Lemma lem1279184 (x : nadd) : term33 x.
Proof. exact (@lem1279183 x). Qed.
Lemma lem1279185 (x : nadd) : (term33 x) = (term30 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1279186 (x : nadd) : term30 x.
Proof. exact (EQ_MP (@lem1279185 x) (@lem1279184 x)). Qed.
Lemma lem1279187 (x : nadd) (z : nadd) : term34 x z.
Proof. exact (@lem1279186 x z). Qed.
Lemma lem1279188 (x : nadd) (z : nadd) : (term34 x z) = (term29 x z).
Proof. exact (eq_refl (term34 x z)). Qed.
Lemma lem1279190 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term35 x x' y y') : term35 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1279191 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : nadd_eq y y'.
Proof. exact (h1). Qed.
Lemma lem1279192 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : nadd_eq x x'.
Proof. exact (h1). Qed.
Lemma lem1279194 (x : nadd) (z : nadd) : term29 x z.
Proof. exact (EQ_MP (@lem1279188 x z) (@lem1279187 x z)). Qed.
Lemma lem1279195 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term36 x y x' y'.
Proof. exact (@lem1279194 (nadd_mul x y) (nadd_mul x' y')). Qed.
Lemma lem1279197 (x : nadd) (z : nadd) : term29 x z.
Proof. exact (EQ_MP (@lem1279160 x z) (@lem1279159 x z)). Qed.
Lemma lem1279198 (x : nadd) (x' : nadd) (y : nadd) : term37 x x' y.
Proof. exact (@lem1279197 (nadd_mul x y) (nadd_mul x' y)). Qed.
Lemma lem1279204 (y : nadd) (x : nadd) : (term17 y x) = True.
Proof. exact (EQ_MP (@lem1279132 y x) (@lem1279131 y x)). Qed.
Lemma lem1279205 (x' : nadd) (y : nadd) : (term17 x' y) = True.
Proof. exact (@lem1279204 x' y). Qed.
Lemma lem1279206 (x : nadd) (y : nadd) (x' : nadd) : (term38 x y x') = (term38 x y x').
Proof. exact (eq_refl (term38 x y x')). Qed.
Lemma lem1279207 (x : nadd) (y : nadd) (x' : nadd) : (term39 x x' y) = (term40 x y x').
Proof. exact (MK_COMB (@lem1279206 x y x') (@lem1279205 x' y)). Qed.
Lemma lem1279209 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1279210 (x : nadd) (y : nadd) (x' : nadd) : (term40 x y x') = (term41 x y x').
Proof. exact (@lem1279209 (term41 x y x')). Qed.
Lemma lem1279213 (x : nadd) (y : nadd) (x' : nadd) : (term39 x x' y) = (term41 x y x').
Proof. exact (TRANS (@lem1279207 x y x') (@lem1279210 x y x')). Qed.
Lemma lem1279214 (x : nadd) (x' : nadd) (y : nadd) : (term41 x y x') = (term39 x x' y).
Proof. exact (SYM (@lem1279213 x y x')). Qed.
Lemma lem1279216 (x : nadd) (z : nadd) : term29 x z.
Proof. exact (EQ_MP (@lem1279124 x z) (@lem1279123 x z)). Qed.
Lemma lem1279217 (x : nadd) (y : nadd) (x' : nadd) : term42 x y x'.
Proof. exact (@lem1279216 (nadd_mul x y) (nadd_mul y x')). Qed.
Lemma lem1279221 (y : nadd) (x : nadd) : (term17 y x) = True.
Proof. exact (EQ_MP (@lem1279096 y x) (@lem1279095 y x)). Qed.
Lemma lem1279222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279223 (y : nadd) (x : nadd) : (term43 y x) = (and True).
Proof. exact (MK_COMB (@lem1279222) (@lem1279221 y x)). Qed.
Lemma lem1279226 (x : nadd) (y : nadd) (x' : nadd) : (term7 x y x') = (term7 x y x').
Proof. exact (eq_refl (term7 x y x')). Qed.
Lemma lem1279227 (x : nadd) (y : nadd) (x' : nadd) : (term44 x y x') = (term45 x y x').
Proof. exact (MK_COMB (@lem1279223 y x) (@lem1279226 x y x')). Qed.
Lemma lem1279229 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1279230 (x : nadd) (y : nadd) (x' : nadd) : (term45 x y x') = (term7 x y x').
Proof. exact (@lem1279229 (term7 x y x')). Qed.
Lemma lem1279233 (x : nadd) (y : nadd) (x' : nadd) : (term44 x y x') = (term7 x y x').
Proof. exact (TRANS (@lem1279227 x y x') (@lem1279230 x y x')). Qed.
Lemma lem1279234 (x : nadd) (y : nadd) (x' : nadd) : (term7 x y x') = (term44 x y x').
Proof. exact (SYM (@lem1279233 x y x')). Qed.
Lemma lem1279236 (y : nadd) (x : nadd) (y' : nadd) : term6 y x y'.
Proof. exact (EQ_MP (@lem1279088 y x y') (@lem1279087 y x y')). Qed.
Lemma lem1279237 (x : nadd) (y : nadd) (x' : nadd) : term6 x y x'.
Proof. exact (@lem1279236 x y x'). Qed.
Lemma lem1279239 (y : nadd) (x : nadd) (y' : nadd) : term6 y x y'.
Proof. exact (EQ_MP (@lem1279088 y x y') (@lem1279087 y x y')). Qed.
Lemma lem1279240 (y : nadd) (x' : nadd) (y' : nadd) : term6 y x' y'.
Proof. exact (@lem1279239 y x' y'). Qed.
Lemma lem1279241 (x : nadd) (x' : nadd) : (nadd_eq x x') = ((nadd_eq x x') = True).
Proof. exact (@lem7 (nadd_eq x x')). Qed.
Lemma lem1279246 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : (nadd_eq x x') = True.
Proof. exact (EQ_MP (@lem1279241 x x') (@lem1279192 x x' h1)). Qed.
Lemma lem1279247 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : True = (nadd_eq x x').
Proof. exact (SYM (@lem1279246 x x' h1)). Qed.
Lemma lem1279248 (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : nadd_eq x x'.
Proof. exact (EQ_MP (@lem1279247 x x' h1) (@lem0)). Qed.
Lemma lem1279251 (y : nadd) (y' : nadd) : (nadd_eq y y') = ((nadd_eq y y') = True).
Proof. exact (@lem7 (nadd_eq y y')). Qed.
Lemma lem1279254 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : (nadd_eq y y') = True.
Proof. exact (EQ_MP (@lem1279251 y y') (@lem1279191 y y' h1)). Qed.
Lemma lem1279255 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : True = (nadd_eq y y').
Proof. exact (SYM (@lem1279254 y y' h1)). Qed.
Lemma lem1279256 (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : nadd_eq y y'.
Proof. exact (EQ_MP (@lem1279255 y y' h1) (@lem0)). Qed.
Lemma lem1279257 (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq y y') : term7 y x' y'.
Proof. exact (@lem1279240 y x' y' (@lem1279256 y y' h1)). Qed.
Lemma lem1279258 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term7 x y x'.
Proof. exact (@lem1279237 x y x' (@lem1279248 x x' h1)). Qed.
Lemma lem1279259 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term44 x y x'.
Proof. exact (EQ_MP (@lem1279234 x y x') (@lem1279258 y x x' h1)). Qed.
Lemma lem1279260 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term46 x y x'.
Proof. exact (ex_intro (term47 x y x') (nadd_mul y x) (@lem1279259 y x x' h1)). Qed.
Lemma lem1279261 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term41 x y x'.
Proof. exact (@lem1279217 x y x' (@lem1279260 y x x' h1)). Qed.
Lemma lem1279262 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term39 x x' y.
Proof. exact (EQ_MP (@lem1279214 x x' y) (@lem1279261 y x x' h1)). Qed.
Lemma lem1279263 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term48 x x' y.
Proof. exact (ex_intro (term49 x x' y) (nadd_mul y x') (@lem1279262 y x x' h1)). Qed.
Lemma lem1279264 (y : nadd) (x : nadd) (x' : nadd) (h1 : nadd_eq x x') : term50 x x' y.
Proof. exact (@lem1279198 x x' y (@lem1279263 y x x' h1)). Qed.
Lemma lem1279265 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term51 x y x' y'.
Proof. exact (conj (@lem1279264 y x x' h1) (@lem1279257 x' y y' h2)). Qed.
Lemma lem1279266 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term52 x y x' y'.
Proof. exact (ex_intro (term53 x y x' y') (nadd_mul x' y) (@lem1279265 x x' y y' h1 h2)). Qed.
Lemma lem1279267 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term54 x y x' y'.
Proof. exact (@lem1279195 x y x' y' (@lem1279266 x x' y y' h1 h2)). Qed.
Lemma lem1279268 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term35 x x' y y') : nadd_eq y y'.
Proof. exact (proj2 (@lem1279190 x x' y y' h1)). Qed.
Lemma lem1279269 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term35 x x' y y') : nadd_eq x x'.
Proof. exact (proj1 (@lem1279190 x x' y y' h1)). Qed.
Lemma lem1279270 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_eq y y') = (term54 x y x' y').
Proof. exact (prop_ext (fun h3 : nadd_eq y y' => @lem1279267 x x' y y' h1 h2) (fun h3 : term54 x y x' y' => @lem1279191 y y' h2)). Qed.
Lemma lem1279271 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term54 x y x' y'.
Proof. exact (EQ_MP (@lem1279270 x x' y y' h1 h2) (@lem1279191 y y' h2)). Qed.
Lemma lem1279272 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : (nadd_eq x x') = (term54 x y x' y').
Proof. exact (prop_ext (fun h3 : nadd_eq x x' => @lem1279271 x x' y y' h1 h2) (fun h3 : term54 x y x' y' => @lem1279192 x x' h1)). Qed.
Lemma lem1279273 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : nadd_eq x x') (h2 : nadd_eq y y') : term54 x y x' y'.
Proof. exact (EQ_MP (@lem1279272 x x' y y' h1 h2) (@lem1279192 x x' h1)). Qed.
Lemma lem1279274 (y : nadd) (y' : nadd) (x : nadd) (x' : nadd) (h1 : term35 x x' y y') (h2 : nadd_eq x x') : (nadd_eq y y') = (term54 x y x' y').
Proof. exact (prop_ext (fun h3 : nadd_eq y y' => @lem1279273 x x' y y' h2 h3) (fun h3 : term54 x y x' y' => @lem1279268 x x' y y' h1)). Qed.
Lemma lem1279275 (y : nadd) (y' : nadd) (x : nadd) (x' : nadd) (h1 : term35 x x' y y') (h2 : nadd_eq x x') : term54 x y x' y'.
Proof. exact (EQ_MP (@lem1279274 y y' x x' h1 h2) (@lem1279268 x x' y y' h1)). Qed.
Lemma lem1279276 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term35 x x' y y') : (nadd_eq x x') = (term54 x y x' y').
Proof. exact (prop_ext (fun h2 : nadd_eq x x' => @lem1279275 y y' x x' h1 h2) (fun h2 : term54 x y x' y' => @lem1279269 x x' y y' h1)). Qed.
Lemma lem1279277 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term35 x x' y y') : term54 x y x' y'.
Proof. exact (EQ_MP (@lem1279276 x x' y y' h1) (@lem1279269 x x' y y' h1)). Qed.
Lemma lem1279278 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term55 x y x' y'.
Proof. exact (fun h0 : term35 x x' y y' => @lem1279277 x x' y y' h0). Qed.
Lemma lem1279283 (x : nadd) (y : nadd) (x' : nadd) : term56 x y x'.
Proof. exact (fun y' : nadd => @lem1279278 x y x' y'). Qed.
Lemma lem1279288 (x : nadd) (x' : nadd) : term57 x x'.
Proof. exact (fun y : nadd => @lem1279283 x y x'). Qed.
Lemma lem1279293 (x : nadd) : term58 x.
Proof. exact (fun x' : nadd => @lem1279288 x x'). Qed.
Lemma lem1279298 : term59.
Proof. exact (fun x : nadd => @lem1279293 x). Qed.
