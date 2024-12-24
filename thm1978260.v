Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1978260_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Require Import DE_MORGAN_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RAT_LEMMA1_spec.
Require Import REAL_LT_REFL_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm82_spec.
Lemma lem1978102 (t1 : Prop) : term0 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1978103 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1978104 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1978103 t1) (@lem1978102 t1)). Qed.
Lemma lem1978105 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1978104 t1 t2). Qed.
Lemma lem1978106 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1978107 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1978106 t1 t2) (@lem1978105 t1 t2)). Qed.
Lemma lem1978112 (t2 : Prop) (t1 : Prop) (h1 : (term4 t1 t2) = (t2 -> t1)) : (term4 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem1978113 (t2 : Prop) (t1 : Prop) (h1 : (term4 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term4 t1 t2).
Proof. exact (SYM (@lem1978112 t2 t1 h1)). Qed.
Lemma lem1978114 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term4 t1 t2)) : (t2 -> t1) = (term4 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1978115 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term4 t1 t2)) : (term4 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem1978114 t1 t2 h1)). Qed.
Lemma lem1978116 (t1 : Prop) (t2 : Prop) : ((term4 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term4 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term4 t1 t2) = (t2 -> t1) => @lem1978113 t2 t1 h1) (fun h1 : (t2 -> t1) = (term4 t1 t2) => @lem1978115 t1 t2 h1)). Qed.
Lemma lem1978117 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1978116 t1 t2)). Qed.
Lemma lem1978118 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1978119 (t1 : Prop) : (term7 t1) = (term8 t1).
Proof. exact (MK_COMB (@lem1978118) (@lem1978117 t1)). Qed.
Lemma lem1978120 : term9 = term10.
Proof. exact (fun_ext (fun t1 : Prop => @lem1978119 t1)). Qed.
Lemma lem1978121 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1978122 : term11 = term12.
Proof. exact (MK_COMB (@lem1978121) (@lem1978120)). Qed.
Lemma lem1978123 : term12.
Proof. exact (EQ_MP (@lem1978122) (@lem10414)). Qed.
Lemma lem1978124 (t1 : Prop) : term13 t1.
Proof. exact (@lem1978123 t1). Qed.
Lemma lem1978125 (t1 : Prop) : (term13 t1) = (term8 t1).
Proof. exact (eq_refl (term13 t1)). Qed.
Lemma lem1978126 (t1 : Prop) : term8 t1.
Proof. exact (EQ_MP (@lem1978125 t1) (@lem1978124 t1)). Qed.
Lemma lem1978127 (t1 : Prop) (t2 : Prop) : term14 t1 t2.
Proof. exact (@lem1978126 t1 t2). Qed.
Lemma lem1978128 (t1 : Prop) (t2 : Prop) : (term14 t1 t2) = ((t2 -> t1) = (term4 t1 t2)).
Proof. exact (eq_refl (term14 t1 t2)). Qed.
Lemma lem1978130 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term15 x1 x2 y1 y2) : term15 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978131 (y1 : real) (y2 : real) (h1 : term16 y1 y2) : term16 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978132 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term16 y1 y2) (h2 : term15 x1 x2 y1 y2) : (term17 x1 y1 x2 y2) = (term18 x1 x2 y1 y2).
Proof. exact (@lem1978130 x1 x2 y1 y2 h2 (@lem1978131 y1 y2 h1)). Qed.
Lemma lem1978133 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term16 y1 y2) : term19 x1 x2 y1 y2.
Proof. exact (fun h0 : term15 x1 x2 y1 y2 => @lem1978132 x1 x2 y1 y2 h1 h0). Qed.
Lemma lem1978134 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term15 x1 x2 y1 y2) : term15 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978135 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term16 y1 y2) (h2 : term15 x1 x2 y1 y2) : (term17 x1 y1 x2 y2) = (term18 x1 x2 y1 y2).
Proof. exact (@lem1978133 x1 x2 y1 y2 h1 (@lem1978134 x1 x2 y1 y2 h2)). Qed.
Lemma lem1978136 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term15 x1 x2 y1 y2) : term15 x1 x2 y1 y2.
Proof. exact (fun h0 : term16 y1 y2 => @lem1978135 x1 x2 y1 y2 h0 h1). Qed.
Lemma lem1978137 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term20 x1 x2 y1 y2.
Proof. exact (fun h0 : term15 x1 x2 y1 y2 => @lem1978136 x1 x2 y1 y2 h0). Qed.
Lemma lem1978139 (y1 : real) (y2 : real) (h1 : term21 y1 y2) : term21 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978141 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term15 x1 x2 y1 y2.
Proof. exact (@lem1978137 x1 x2 y1 y2 (@lem1978101 x1 x2 y1 y2)). Qed.
Lemma lem1978145 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term4 t1 t2).
Proof. exact (EQ_MP (@lem1978128 t1 t2) (@lem1978127 t1 t2)). Qed.
Lemma lem1978146 (y1 : real) (y2 : real) : (term22 y1 y2) = (term23 y1 y2).
Proof. exact (@lem1978145 (term16 y1 y2) (term21 y1 y2)). Qed.
Lemma lem1978147 (y1 : real) (y2 : real) : (term23 y1 y2) = (term22 y1 y2).
Proof. exact (SYM (@lem1978146 y1 y2)). Qed.
Lemma lem1978151 (t1 : Prop) (t2 : Prop) : (term24 t1 t2) = (term25 t1 t2).
Proof. exact (proj1 (@lem1978107 t1 t2)). Qed.
Lemma lem1978152 (y1 : real) (y2 : real) : (term26 y1 y2) = (term27 y1 y2).
Proof. exact (@lem1978151 (term28 y1) (term28 y2)). Qed.
Lemma lem1978156 (t : Prop) : (term29 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1978157 (y1 : real) : (term30 y1) = (y1 = term31).
Proof. exact (@lem1978156 (y1 = term31)). Qed.
Lemma lem1978160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1978161 (y1 : real) : (term32 y1) = (term33 y1).
Proof. exact (MK_COMB (@lem1978160) (@lem1978157 y1)). Qed.
Lemma lem1978163 (t : Prop) : (term29 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1978164 (y2 : real) : (term30 y2) = (y2 = term31).
Proof. exact (@lem1978163 (y2 = term31)). Qed.
Lemma lem1978167 (y1 : real) (y2 : real) : (term27 y1 y2) = (term34 y1 y2).
Proof. exact (MK_COMB (@lem1978161 y1) (@lem1978164 y2)). Qed.
Lemma lem1978170 (y1 : real) (y2 : real) : (term26 y1 y2) = (term34 y1 y2).
Proof. exact (TRANS (@lem1978152 y1 y2) (@lem1978167 y1 y2)). Qed.
Lemma lem1978171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1978172 (y1 : real) (y2 : real) : (term35 y1 y2) = (term36 y1 y2).
Proof. exact (MK_COMB (@lem1978171) (@lem1978170 y1 y2)). Qed.
Lemma lem1978174 (t1 : Prop) (t2 : Prop) : (term24 t1 t2) = (term25 t1 t2).
Proof. exact (proj1 (@lem1978107 t1 t2)). Qed.
Lemma lem1978175 (y1 : real) (y2 : real) : (term37 y1 y2) = (term38 y1 y2).
Proof. exact (@lem1978174 (term39 y1) (term39 y2)). Qed.
Lemma lem1978178 (y1 : real) (y2 : real) : (term23 y1 y2) = (term40 y1 y2).
Proof. exact (MK_COMB (@lem1978172 y1 y2) (@lem1978175 y1 y2)). Qed.
Lemma lem1978181 (y1 : real) (y2 : real) : (term40 y1 y2) = (term23 y1 y2).
Proof. exact (SYM (@lem1978178 y1 y2)). Qed.
Lemma lem1978182 (y1 : real) (y2 : real) (h1 : term34 y1 y2) : term34 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1978183 (y1 : real) (h1 : y1 = term31) : y1 = term31.
Proof. exact (h1). Qed.
Lemma lem1978184 (y2 : real) (h1 : y2 = term31) : y2 = term31.
Proof. exact (h1). Qed.
Lemma lem1978185 (x : real) : term41 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1978186 (x : real) : (term41 x) = (term42 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1978187 (x : real) : term42 x.
Proof. exact (EQ_MP (@lem1978186 x) (@lem1978185 x)). Qed.
Lemma lem1978188 (x : real) : term43 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1978195 (y1 : real) (h1 : y1 = term31) : y1 = term31.
Proof. exact (h1). Qed.
Lemma lem1978196 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1978197 (y1 : real) (h1 : y1 = term31) : (term39 y1) = term45.
Proof. exact (MK_COMB (@lem1978196) (@lem1978195 y1 h1)). Qed.
Lemma lem1978199 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1978188 x (@lem1978187 x)). Qed.
Lemma lem1978200 : term45 = False.
Proof. exact (@lem1978199 term31). Qed.
Lemma lem1978201 (y1 : real) (h1 : y1 = term31) : (term39 y1) = False.
Proof. exact (TRANS (@lem1978197 y1 h1) (@lem1978200)). Qed.
Lemma lem1978202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1978203 (y1 : real) (h1 : y1 = term31) : (term46 y1) = (~ False).
Proof. exact (MK_COMB (@lem1978202) (@lem1978201 y1 h1)). Qed.
Lemma lem1978205 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1978206 (y1 : real) (h1 : y1 = term31) : (term46 y1) = True.
Proof. exact (TRANS (@lem1978203 y1 h1) (@lem1978205)). Qed.
Lemma lem1978207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1978208 (y1 : real) (h1 : y1 = term31) : (term47 y1) = (or True).
Proof. exact (MK_COMB (@lem1978207) (@lem1978206 y1 h1)). Qed.
Lemma lem1978211 (y2 : real) : (term46 y2) = (term46 y2).
Proof. exact (eq_refl (term46 y2)). Qed.
Lemma lem1978212 (y2 : real) (y1 : real) (h1 : y1 = term31) : (term38 y1 y2) = (term48 y2).
Proof. exact (MK_COMB (@lem1978208 y1 h1) (@lem1978211 y2)). Qed.
Lemma lem1978214 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1978215 (y2 : real) : (term48 y2) = True.
Proof. exact (@lem1978214 (term46 y2)). Qed.
Lemma lem1978216 (y2 : real) (y1 : real) (h1 : y1 = term31) : (term38 y1 y2) = True.
Proof. exact (TRANS (@lem1978212 y2 y1 h1) (@lem1978215 y2)). Qed.
Lemma lem1978217 (y2 : real) (y1 : real) (h1 : y1 = term31) : True = (term38 y1 y2).
Proof. exact (SYM (@lem1978216 y2 y1 h1)). Qed.
Lemma lem1978218 (y2 : real) (y1 : real) (h1 : y1 = term31) : term38 y1 y2.
Proof. exact (EQ_MP (@lem1978217 y2 y1 h1) (@lem0)). Qed.
Lemma lem1978219 (x : real) : term41 x.
Proof. exact (@lem1379422 x). Qed.
Lemma lem1978220 (x : real) : (term41 x) = (term42 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1978221 (x : real) : term42 x.
Proof. exact (EQ_MP (@lem1978220 x) (@lem1978219 x)). Qed.
Lemma lem1978222 (x : real) : term43 x.
Proof. exact (@lem82 (real_lt x x)). Qed.
Lemma lem1978231 (y2 : real) (h1 : y2 = term31) : y2 = term31.
Proof. exact (h1). Qed.
Lemma lem1978232 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1978233 (y2 : real) (h1 : y2 = term31) : (term39 y2) = term45.
Proof. exact (MK_COMB (@lem1978232) (@lem1978231 y2 h1)). Qed.
Lemma lem1978235 (x : real) : (real_lt x x) = False.
Proof. exact (@lem1978222 x (@lem1978221 x)). Qed.
Lemma lem1978236 : term45 = False.
Proof. exact (@lem1978235 term31). Qed.
Lemma lem1978237 (y2 : real) (h1 : y2 = term31) : (term39 y2) = False.
Proof. exact (TRANS (@lem1978233 y2 h1) (@lem1978236)). Qed.
Lemma lem1978238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1978239 (y2 : real) (h1 : y2 = term31) : (term46 y2) = (~ False).
Proof. exact (MK_COMB (@lem1978238) (@lem1978237 y2 h1)). Qed.
Lemma lem1978241 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1978242 (y2 : real) (h1 : y2 = term31) : (term46 y2) = True.
Proof. exact (TRANS (@lem1978239 y2 h1) (@lem1978241)). Qed.
Lemma lem1978243 (y1 : real) : (term47 y1) = (term47 y1).
Proof. exact (eq_refl (term47 y1)). Qed.
Lemma lem1978244 (y1 : real) (y2 : real) (h1 : y2 = term31) : (term38 y1 y2) = (term49 y1).
Proof. exact (MK_COMB (@lem1978243 y1) (@lem1978242 y2 h1)). Qed.
Lemma lem1978246 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1978247 (y1 : real) : (term49 y1) = True.
Proof. exact (@lem1978246 (term46 y1)). Qed.
Lemma lem1978248 (y1 : real) (y2 : real) (h1 : y2 = term31) : (term38 y1 y2) = True.
Proof. exact (TRANS (@lem1978244 y1 y2 h1) (@lem1978247 y1)). Qed.
Lemma lem1978249 (y1 : real) (y2 : real) (h1 : y2 = term31) : True = (term38 y1 y2).
Proof. exact (SYM (@lem1978248 y1 y2 h1)). Qed.
Lemma lem1978250 (y1 : real) (y2 : real) (h1 : y2 = term31) : term38 y1 y2.
Proof. exact (EQ_MP (@lem1978249 y1 y2 h1) (@lem0)). Qed.
Lemma lem1978251 (y1 : real) (y2 : real) (h1 : y2 = term31) : (y2 = term31) = (term38 y1 y2).
Proof. exact (prop_ext (fun h2 : y2 = term31 => @lem1978250 y1 y2 h1) (fun h2 : term38 y1 y2 => @lem1978184 y2 h1)). Qed.
Lemma lem1978252 (y1 : real) (y2 : real) (h1 : y2 = term31) : term38 y1 y2.
Proof. exact (EQ_MP (@lem1978251 y1 y2 h1) (@lem1978184 y2 h1)). Qed.
Lemma lem1978253 (y2 : real) (y1 : real) (h1 : y1 = term31) : (y1 = term31) = (term38 y1 y2).
Proof. exact (prop_ext (fun h2 : y1 = term31 => @lem1978218 y2 y1 h1) (fun h2 : term38 y1 y2 => @lem1978183 y1 h1)). Qed.
Lemma lem1978254 (y2 : real) (y1 : real) (h1 : y1 = term31) : term38 y1 y2.
Proof. exact (EQ_MP (@lem1978253 y2 y1 h1) (@lem1978183 y1 h1)). Qed.
Lemma lem1978255 (y1 : real) (y2 : real) (h1 : term34 y1 y2) : term38 y1 y2.
Proof. exact (or_elim (@lem1978182 y1 y2 h1) (fun h0 : y1 = term31 => @lem1978254 y2 y1 h0) (fun h0 : y2 = term31 => @lem1978252 y1 y2 h0)). Qed.
Lemma lem1978256 (y1 : real) (y2 : real) : term40 y1 y2.
Proof. exact (fun h0 : term34 y1 y2 => @lem1978255 y1 y2 h0). Qed.
Lemma lem1978257 (y1 : real) (y2 : real) : term23 y1 y2.
Proof. exact (EQ_MP (@lem1978181 y1 y2) (@lem1978256 y1 y2)). Qed.
Lemma lem1978258 (y1 : real) (y2 : real) : term22 y1 y2.
Proof. exact (EQ_MP (@lem1978147 y1 y2) (@lem1978257 y1 y2)). Qed.
Lemma lem1978259 (y1 : real) (y2 : real) (h1 : term21 y1 y2) : term16 y1 y2.
Proof. exact (@lem1978258 y1 y2 (@lem1978139 y1 y2 h1)). Qed.
Lemma lem1978260 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term21 y1 y2) : (term17 x1 y1 x2 y2) = (term18 x1 x2 y1 y2).
Proof. exact (@lem1978141 x1 x2 y1 y2 (@lem1978259 y1 y2 h1)). Qed.
