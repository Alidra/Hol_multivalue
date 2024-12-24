Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm22288_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Lemma lem22038 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem22039 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem22040 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem22039 a) (@lem22038 a)). Qed.
Lemma lem22041 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem22042 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem22055 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem22056 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem22055 b c) (@lem22041 a h1)). Qed.
Lemma lem22057 (b : Prop) (c : Prop) : (term4 b c) = (term5 b c).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem22058 (b : Prop) (c : Prop) (a : Prop) : (term6 b c a) = (term6 b c a).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem22059 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = (term5 b c)).
Proof. exact (MK_COMB (@lem22058 b c a) (@lem22057 b c)). Qed.
Lemma lem22060 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = (term7 a b c).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem22061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22062 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = (term8 a b c).
Proof. exact (MK_COMB (@lem22061) (@lem22060 a b c)). Qed.
Lemma lem22063 (b : Prop) (c : Prop) : (term5 b c) = (term5 b c).
Proof. exact (eq_refl (term5 b c)). Qed.
Lemma lem22064 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term5 b c)) = ((term7 a b c) = (term5 b c)).
Proof. exact (MK_COMB (@lem22062 a b c) (@lem22063 b c)). Qed.
Lemma lem22065 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term7 a b c) = (term5 b c)).
Proof. exact (TRANS (@lem22059 a b c) (@lem22064 a b c)). Qed.
Lemma lem22066 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term7 a b c) = (term5 b c).
Proof. exact (EQ_MP (@lem22065 a b c) (@lem22056 b c a h1)). Qed.
Lemma lem22067 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term5 b c) = (term7 a b c).
Proof. exact (SYM (@lem22066 b c a h1)). Qed.
Lemma lem22068 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem22069 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term9 b c).
Proof. exact (MK_COMB (@lem22068 b c) (@lem22042 a h1)). Qed.
Lemma lem22070 (b : Prop) (c : Prop) : (term9 b c) = (term10 b c).
Proof. exact (eq_refl (term9 b c)). Qed.
Lemma lem22071 (b : Prop) (c : Prop) (a : Prop) : (term6 b c a) = (term6 b c a).
Proof. exact (eq_refl (term6 b c a)). Qed.
Lemma lem22072 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term9 b c)) = ((term3 b c a) = (term10 b c)).
Proof. exact (MK_COMB (@lem22071 b c a) (@lem22070 b c)). Qed.
Lemma lem22073 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = (term7 a b c).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem22074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22075 (a : Prop) (b : Prop) (c : Prop) : (term6 b c a) = (term8 a b c).
Proof. exact (MK_COMB (@lem22074) (@lem22073 a b c)). Qed.
Lemma lem22076 (b : Prop) (c : Prop) : (term10 b c) = (term10 b c).
Proof. exact (eq_refl (term10 b c)). Qed.
Lemma lem22077 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term10 b c)) = ((term7 a b c) = (term10 b c)).
Proof. exact (MK_COMB (@lem22075 a b c) (@lem22076 b c)). Qed.
Lemma lem22078 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term9 b c)) = ((term7 a b c) = (term10 b c)).
Proof. exact (TRANS (@lem22072 a b c) (@lem22077 a b c)). Qed.
Lemma lem22079 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term7 a b c) = (term10 b c).
Proof. exact (EQ_MP (@lem22078 a b c) (@lem22069 b c a h1)). Qed.
Lemma lem22080 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term10 b c) = (term7 a b c).
Proof. exact (SYM (@lem22079 b c a h1)). Qed.
Lemma lem22084 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem22085 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem22084 b). Qed.
Lemma lem22086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22087 (b : Prop) : (term11 b) = (imp True).
Proof. exact (MK_COMB (@lem22086) (@lem22085 b)). Qed.
Lemma lem22093 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem22094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem22095 : term12 = (or False).
Proof. exact (MK_COMB (@lem22094) (@lem22093)). Qed.
Lemma lem22096 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem22097 (c : Prop) : (term13 c) = (False \/ c).
Proof. exact (MK_COMB (@lem22095) (@lem22096 c)). Qed.
Lemma lem22099 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem22100 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem22099 c). Qed.
Lemma lem22101 (c : Prop) : (term13 c) = c.
Proof. exact (TRANS (@lem22097 c) (@lem22100 c)). Qed.
Lemma lem22102 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22103 (c : Prop) : (term14 c) = (imp c).
Proof. exact (MK_COMB (@lem22102) (@lem22101 c)). Qed.
Lemma lem22106 (b : Prop) (c : Prop) : (b \/ c) = (b \/ c).
Proof. exact (eq_refl (b \/ c)). Qed.
Lemma lem22107 (b : Prop) (c : Prop) : (term15 b c) = (term16 b c).
Proof. exact (MK_COMB (@lem22103 c) (@lem22106 b c)). Qed.
Lemma lem22110 (b : Prop) (c : Prop) : (term5 b c) = (term17 b c).
Proof. exact (MK_COMB (@lem22087 b) (@lem22107 b c)). Qed.
Lemma lem22112 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22113 (b : Prop) (c : Prop) : (term17 b c) = (term16 b c).
Proof. exact (@lem22112 (term16 b c)). Qed.
Lemma lem22118 (b : Prop) (c : Prop) : (term5 b c) = (term16 b c).
Proof. exact (TRANS (@lem22110 b c) (@lem22113 b c)). Qed.
Lemma lem22119 (b : Prop) (c : Prop) : (term16 b c) = (term5 b c).
Proof. exact (SYM (@lem22118 b c)). Qed.
Lemma lem22120 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem22121 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem22122 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem22121 c) (@lem22120 c)). Qed.
Lemma lem22123 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem22124 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem22131 (b : Prop) : (term18 b) = (term18 b).
Proof. exact (eq_refl (term18 b)). Qed.
Lemma lem22132 (b : Prop) (c : Prop) (h1 : c = True) : (term19 b c) = (term20 b).
Proof. exact (MK_COMB (@lem22131 b) (@lem22123 c h1)). Qed.
Lemma lem22133 (b : Prop) : (term20 b) = (term21 b).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem22134 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem22135 (c : Prop) (b : Prop) : ((term19 b c) = (term20 b)) = ((term19 b c) = (term21 b)).
Proof. exact (MK_COMB (@lem22134 b c) (@lem22133 b)). Qed.
Lemma lem22136 (b : Prop) (c : Prop) : (term19 b c) = (term16 b c).
Proof. exact (eq_refl (term19 b c)). Qed.
Lemma lem22137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22138 (b : Prop) (c : Prop) : (term22 b c) = (term23 b c).
Proof. exact (MK_COMB (@lem22137) (@lem22136 b c)). Qed.
Lemma lem22139 (b : Prop) : (term21 b) = (term21 b).
Proof. exact (eq_refl (term21 b)). Qed.
Lemma lem22140 (c : Prop) (b : Prop) : ((term19 b c) = (term21 b)) = ((term16 b c) = (term21 b)).
Proof. exact (MK_COMB (@lem22138 b c) (@lem22139 b)). Qed.
Lemma lem22141 (c : Prop) (b : Prop) : ((term19 b c) = (term20 b)) = ((term16 b c) = (term21 b)).
Proof. exact (TRANS (@lem22135 c b) (@lem22140 c b)). Qed.
Lemma lem22142 (b : Prop) (c : Prop) (h1 : c = True) : (term16 b c) = (term21 b).
Proof. exact (EQ_MP (@lem22141 c b) (@lem22132 b c h1)). Qed.
Lemma lem22143 (b : Prop) (c : Prop) (h1 : c = True) : (term21 b) = (term16 b c).
Proof. exact (SYM (@lem22142 b c h1)). Qed.
Lemma lem22144 (b : Prop) : (term18 b) = (term18 b).
Proof. exact (eq_refl (term18 b)). Qed.
Lemma lem22145 (b : Prop) (c : Prop) (h1 : c = False) : (term19 b c) = (term24 b).
Proof. exact (MK_COMB (@lem22144 b) (@lem22124 c h1)). Qed.
Lemma lem22146 (b : Prop) : (term24 b) = (term25 b).
Proof. exact (eq_refl (term24 b)). Qed.
Lemma lem22147 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem22148 (c : Prop) (b : Prop) : ((term19 b c) = (term24 b)) = ((term19 b c) = (term25 b)).
Proof. exact (MK_COMB (@lem22147 b c) (@lem22146 b)). Qed.
Lemma lem22149 (b : Prop) (c : Prop) : (term19 b c) = (term16 b c).
Proof. exact (eq_refl (term19 b c)). Qed.
Lemma lem22150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22151 (b : Prop) (c : Prop) : (term22 b c) = (term23 b c).
Proof. exact (MK_COMB (@lem22150) (@lem22149 b c)). Qed.
Lemma lem22152 (b : Prop) : (term25 b) = (term25 b).
Proof. exact (eq_refl (term25 b)). Qed.
Lemma lem22153 (c : Prop) (b : Prop) : ((term19 b c) = (term25 b)) = ((term16 b c) = (term25 b)).
Proof. exact (MK_COMB (@lem22151 b c) (@lem22152 b)). Qed.
Lemma lem22154 (c : Prop) (b : Prop) : ((term19 b c) = (term24 b)) = ((term16 b c) = (term25 b)).
Proof. exact (TRANS (@lem22148 c b) (@lem22153 c b)). Qed.
Lemma lem22155 (b : Prop) (c : Prop) (h1 : c = False) : (term16 b c) = (term25 b).
Proof. exact (EQ_MP (@lem22154 c b) (@lem22145 b c h1)). Qed.
Lemma lem22156 (b : Prop) (c : Prop) (h1 : c = False) : (term25 b) = (term16 b c).
Proof. exact (SYM (@lem22155 b c h1)). Qed.
Lemma lem22158 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22159 (b : Prop) : (term21 b) = (b \/ True).
Proof. exact (@lem22158 (b \/ True)). Qed.
Lemma lem22161 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem22162 (b : Prop) : (b \/ True) = True.
Proof. exact (@lem22161 b). Qed.
Lemma lem22163 (b : Prop) : (term21 b) = True.
Proof. exact (TRANS (@lem22159 b) (@lem22162 b)). Qed.
Lemma lem22164 (b : Prop) : True = (term21 b).
Proof. exact (SYM (@lem22163 b)). Qed.
Lemma lem22165 (b : Prop) : term21 b.
Proof. exact (EQ_MP (@lem22164 b) (@lem0)). Qed.
Lemma lem22167 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem22168 (b : Prop) : (term25 b) = True.
Proof. exact (@lem22167 (b \/ False)). Qed.
Lemma lem22169 (b : Prop) : True = (term25 b).
Proof. exact (SYM (@lem22168 b)). Qed.
Lemma lem22170 (b : Prop) : term25 b.
Proof. exact (EQ_MP (@lem22169 b) (@lem0)). Qed.
Lemma lem22171 (b : Prop) (c : Prop) (h1 : c = False) : term16 b c.
Proof. exact (EQ_MP (@lem22156 b c h1) (@lem22170 b)). Qed.
Lemma lem22172 (b : Prop) (c : Prop) (h1 : c = True) : term16 b c.
Proof. exact (EQ_MP (@lem22143 b c h1) (@lem22165 b)). Qed.
Lemma lem22174 (b : Prop) (c : Prop) : term16 b c.
Proof. exact (or_elim (@lem22122 c) (fun h0 : c = True => @lem22172 b c h0) (fun h0 : c = False => @lem22171 b c h0)). Qed.
Lemma lem22175 (b : Prop) (c : Prop) : term5 b c.
Proof. exact (EQ_MP (@lem22119 b c) (@lem22174 b c)). Qed.
Lemma lem22179 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem22180 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem22179 b). Qed.
Lemma lem22181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22182 (b : Prop) : (term26 b) = (imp b).
Proof. exact (MK_COMB (@lem22181) (@lem22180 b)). Qed.
Lemma lem22188 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem22189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem22190 : term27 = (or True).
Proof. exact (MK_COMB (@lem22189) (@lem22188)). Qed.
Lemma lem22191 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem22192 (c : Prop) : (term28 c) = (True \/ c).
Proof. exact (MK_COMB (@lem22190) (@lem22191 c)). Qed.
Lemma lem22194 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem22195 (c : Prop) : (True \/ c) = True.
Proof. exact (@lem22194 c). Qed.
Lemma lem22196 (c : Prop) : (term28 c) = True.
Proof. exact (TRANS (@lem22192 c) (@lem22195 c)). Qed.
Lemma lem22197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22198 (c : Prop) : (term29 c) = (imp True).
Proof. exact (MK_COMB (@lem22197) (@lem22196 c)). Qed.
Lemma lem22201 (b : Prop) (c : Prop) : (b \/ c) = (b \/ c).
Proof. exact (eq_refl (b \/ c)). Qed.
Lemma lem22202 (b : Prop) (c : Prop) : (term30 b c) = (term31 b c).
Proof. exact (MK_COMB (@lem22198 c) (@lem22201 b c)). Qed.
Lemma lem22204 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22205 (b : Prop) (c : Prop) : (term31 b c) = (b \/ c).
Proof. exact (@lem22204 (b \/ c)). Qed.
Lemma lem22208 (b : Prop) (c : Prop) : (term30 b c) = (b \/ c).
Proof. exact (TRANS (@lem22202 b c) (@lem22205 b c)). Qed.
Lemma lem22209 (b : Prop) (c : Prop) : (term10 b c) = (term32 b c).
Proof. exact (MK_COMB (@lem22182 b) (@lem22208 b c)). Qed.
Lemma lem22212 (b : Prop) (c : Prop) : (term32 b c) = (term10 b c).
Proof. exact (SYM (@lem22209 b c)). Qed.
Lemma lem22213 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem22214 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem22215 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem22214 b) (@lem22213 b)). Qed.
Lemma lem22216 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem22217 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem22224 (c : Prop) : (term33 c) = (term33 c).
Proof. exact (eq_refl (term33 c)). Qed.
Lemma lem22225 (c : Prop) (b : Prop) (h1 : b = True) : (term34 c b) = (term35 c).
Proof. exact (MK_COMB (@lem22224 c) (@lem22216 b h1)). Qed.
Lemma lem22226 (c : Prop) : (term35 c) = (term36 c).
Proof. exact (eq_refl (term35 c)). Qed.
Lemma lem22227 (c : Prop) (b : Prop) : (term37 c b) = (term37 c b).
Proof. exact (eq_refl (term37 c b)). Qed.
Lemma lem22228 (b : Prop) (c : Prop) : ((term34 c b) = (term35 c)) = ((term34 c b) = (term36 c)).
Proof. exact (MK_COMB (@lem22227 c b) (@lem22226 c)). Qed.
Lemma lem22229 (b : Prop) (c : Prop) : (term34 c b) = (term32 b c).
Proof. exact (eq_refl (term34 c b)). Qed.
Lemma lem22230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22231 (b : Prop) (c : Prop) : (term37 c b) = (term38 b c).
Proof. exact (MK_COMB (@lem22230) (@lem22229 b c)). Qed.
Lemma lem22232 (c : Prop) : (term36 c) = (term36 c).
Proof. exact (eq_refl (term36 c)). Qed.
Lemma lem22233 (b : Prop) (c : Prop) : ((term34 c b) = (term36 c)) = ((term32 b c) = (term36 c)).
Proof. exact (MK_COMB (@lem22231 b c) (@lem22232 c)). Qed.
Lemma lem22234 (b : Prop) (c : Prop) : ((term34 c b) = (term35 c)) = ((term32 b c) = (term36 c)).
Proof. exact (TRANS (@lem22228 b c) (@lem22233 b c)). Qed.
Lemma lem22235 (c : Prop) (b : Prop) (h1 : b = True) : (term32 b c) = (term36 c).
Proof. exact (EQ_MP (@lem22234 b c) (@lem22225 c b h1)). Qed.
Lemma lem22236 (c : Prop) (b : Prop) (h1 : b = True) : (term36 c) = (term32 b c).
Proof. exact (SYM (@lem22235 c b h1)). Qed.
Lemma lem22237 (c : Prop) : (term33 c) = (term33 c).
Proof. exact (eq_refl (term33 c)). Qed.
Lemma lem22238 (c : Prop) (b : Prop) (h1 : b = False) : (term34 c b) = (term39 c).
Proof. exact (MK_COMB (@lem22237 c) (@lem22217 b h1)). Qed.
Lemma lem22239 (c : Prop) : (term39 c) = (term40 c).
Proof. exact (eq_refl (term39 c)). Qed.
Lemma lem22240 (c : Prop) (b : Prop) : (term37 c b) = (term37 c b).
Proof. exact (eq_refl (term37 c b)). Qed.
Lemma lem22241 (b : Prop) (c : Prop) : ((term34 c b) = (term39 c)) = ((term34 c b) = (term40 c)).
Proof. exact (MK_COMB (@lem22240 c b) (@lem22239 c)). Qed.
Lemma lem22242 (b : Prop) (c : Prop) : (term34 c b) = (term32 b c).
Proof. exact (eq_refl (term34 c b)). Qed.
Lemma lem22243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22244 (b : Prop) (c : Prop) : (term37 c b) = (term38 b c).
Proof. exact (MK_COMB (@lem22243) (@lem22242 b c)). Qed.
Lemma lem22245 (c : Prop) : (term40 c) = (term40 c).
Proof. exact (eq_refl (term40 c)). Qed.
Lemma lem22246 (b : Prop) (c : Prop) : ((term34 c b) = (term40 c)) = ((term32 b c) = (term40 c)).
Proof. exact (MK_COMB (@lem22244 b c) (@lem22245 c)). Qed.
Lemma lem22247 (b : Prop) (c : Prop) : ((term34 c b) = (term39 c)) = ((term32 b c) = (term40 c)).
Proof. exact (TRANS (@lem22241 b c) (@lem22246 b c)). Qed.
Lemma lem22248 (c : Prop) (b : Prop) (h1 : b = False) : (term32 b c) = (term40 c).
Proof. exact (EQ_MP (@lem22247 b c) (@lem22238 c b h1)). Qed.
Lemma lem22249 (c : Prop) (b : Prop) (h1 : b = False) : (term40 c) = (term32 b c).
Proof. exact (SYM (@lem22248 c b h1)). Qed.
Lemma lem22251 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22252 (c : Prop) : (term36 c) = (True \/ c).
Proof. exact (@lem22251 (True \/ c)). Qed.
Lemma lem22254 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem22255 (c : Prop) : (True \/ c) = True.
Proof. exact (@lem22254 c). Qed.
Lemma lem22256 (c : Prop) : (term36 c) = True.
Proof. exact (TRANS (@lem22252 c) (@lem22255 c)). Qed.
Lemma lem22257 (c : Prop) : True = (term36 c).
Proof. exact (SYM (@lem22256 c)). Qed.
Lemma lem22258 (c : Prop) : term36 c.
Proof. exact (EQ_MP (@lem22257 c) (@lem0)). Qed.
Lemma lem22260 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem22261 (c : Prop) : (term40 c) = True.
Proof. exact (@lem22260 (False \/ c)). Qed.
Lemma lem22262 (c : Prop) : True = (term40 c).
Proof. exact (SYM (@lem22261 c)). Qed.
Lemma lem22263 (c : Prop) : term40 c.
Proof. exact (EQ_MP (@lem22262 c) (@lem0)). Qed.
Lemma lem22264 (c : Prop) (b : Prop) (h1 : b = False) : term32 b c.
Proof. exact (EQ_MP (@lem22249 c b h1) (@lem22263 c)). Qed.
Lemma lem22265 (c : Prop) (b : Prop) (h1 : b = True) : term32 b c.
Proof. exact (EQ_MP (@lem22236 c b h1) (@lem22258 c)). Qed.
Lemma lem22267 (b : Prop) (c : Prop) : term32 b c.
Proof. exact (or_elim (@lem22215 b) (fun h0 : b = True => @lem22265 c b h0) (fun h0 : b = False => @lem22264 c b h0)). Qed.
Lemma lem22268 (b : Prop) (c : Prop) : term10 b c.
Proof. exact (EQ_MP (@lem22212 b c) (@lem22267 b c)). Qed.
Lemma lem22269 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : term7 a b c.
Proof. exact (EQ_MP (@lem22080 b c a h1) (@lem22268 b c)). Qed.
Lemma lem22270 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : term7 a b c.
Proof. exact (EQ_MP (@lem22067 b c a h1) (@lem22175 b c)). Qed.
Lemma lem22273 (a : Prop) (b : Prop) (c : Prop) : term7 a b c.
Proof. exact (or_elim (@lem22040 a) (fun h0 : a = True => @lem22270 b c a h0) (fun h0 : a = False => @lem22269 b c a h0)). Qed.
Lemma lem22278 (a : Prop) (b : Prop) : term41 a b.
Proof. exact (fun c : Prop => @lem22273 a b c). Qed.
Lemma lem22283 (a : Prop) : term42 a.
Proof. exact (fun b : Prop => @lem22278 a b). Qed.
Lemma lem22288 : term43.
Proof. exact (fun a : Prop => @lem22283 a). Qed.
