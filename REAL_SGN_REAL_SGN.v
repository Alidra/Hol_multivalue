Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_REAL_SGN_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_sgn_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Require Import thm996238_spec.
Lemma lem1760047 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1760048 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1760057 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1760048 x) (@lem1760047 x)). Qed.
Lemma lem1760058 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1760057 (real_sgn x)). Qed.
Lemma lem1760060 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1760048 x) (@lem1760047 x)). Qed.
Lemma lem1760061 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760062 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1760061) (@lem1760060 x)). Qed.
Lemma lem1760063 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760064 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1760063) (@lem1760062 x)). Qed.
Lemma lem1760065 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760066 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1760064 x) (@lem1760065)). Qed.
Lemma lem1760068 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1760048 x) (@lem1760047 x)). Qed.
Lemma lem1760069 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760070 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1760069) (@lem1760068 x)). Qed.
Lemma lem1760071 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760072 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1760070 x) (@lem1760071)). Qed.
Lemma lem1760073 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760074 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1760073) (@lem1760072 x)). Qed.
Lemma lem1760075 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760076 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1760074 x) (@lem1760075)). Qed.
Lemma lem1760077 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760078 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1760076 x) (@lem1760077)). Qed.
Lemma lem1760079 (x : real) : (term3 x) = (term24 x).
Proof. exact (MK_COMB (@lem1760066 x) (@lem1760078 x)). Qed.
Lemma lem1760080 (x : real) : (term2 x) = (term24 x).
Proof. exact (TRANS (@lem1760058 x) (@lem1760079 x)). Qed.
Lemma lem1760081 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760082 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1760081) (@lem1760080 x)). Qed.
Lemma lem1760084 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1760048 x) (@lem1760047 x)). Qed.
Lemma lem1760085 (x : real) : ((term2 x) = (real_sgn x)) = ((term24 x) = (term1 x)).
Proof. exact (MK_COMB (@lem1760082 x) (@lem1760084 x)). Qed.
Lemma lem1760088 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1760085 x)). Qed.
Lemma lem1760089 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1760090 : term29 = term30.
Proof. exact (MK_COMB (@lem1760089) (@lem1760088)). Qed.
Lemma lem1760095 : term30 = term29.
Proof. exact (SYM (@lem1760090)). Qed.
Lemma lem1760104 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1760105 : term33 = term34.
Proof. exact (@lem1760104 term28). Qed.
Lemma lem1760106 (x : real) : (term35 x) = ((term24 x) = (term1 x)).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1760107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760109 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1760107) (@lem1760106 x)). Qed.
Lemma lem1760110 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1760109 x)). Qed.
Lemma lem1760111 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1760112 : term34 = term40.
Proof. exact (MK_COMB (@lem1760111) (@lem1760110)). Qed.
Lemma lem1760114 : term33 = term40.
Proof. exact (TRANS (@lem1760105) (@lem1760112)). Qed.
Lemma lem1760118 (x : real) (h1 : (term6 x) = False) : (term6 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760119 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760120 (x : real) (h1 : (term6 x) = False) : (term8 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760119) (@lem1760118 x h1)). Qed.
Lemma lem1760121 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760122 (x : real) (h1 : (term6 x) = False) : (term11 x) = term41.
Proof. exact (MK_COMB (@lem1760120 x h1) (@lem1760121)). Qed.
Lemma lem1760123 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1760124 (x : real) (h1 : (term6 x) = False) : (term24 x) = (term42 x).
Proof. exact (MK_COMB (@lem1760122 x h1) (@lem1760123 x)). Qed.
Lemma lem1760126 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760127 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760126 real t1 t2). Qed.
Lemma lem1760128 (x : real) : (term42 x) = (term23 x).
Proof. exact (@lem1760127 term9 (term23 x)). Qed.
Lemma lem1760129 (x : real) (h1 : (term6 x) = False) : (term24 x) = (term23 x).
Proof. exact (TRANS (@lem1760124 x h1) (@lem1760128 x)). Qed.
Lemma lem1760130 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760131 (x : real) (h1 : (term6 x) = False) : (term26 x) = (term43 x).
Proof. exact (MK_COMB (@lem1760130) (@lem1760129 x h1)). Qed.
Lemma lem1760132 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1760133 (x : real) (h1 : (term6 x) = False) : ((term24 x) = (term1 x)) = ((term23 x) = (term1 x)).
Proof. exact (MK_COMB (@lem1760131 x h1) (@lem1760132 x)). Qed.
Lemma lem1760136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760137 (x : real) (h1 : (term6 x) = False) : (term37 x) = (term44 x).
Proof. exact (MK_COMB (@lem1760136) (@lem1760133 x h1)). Qed.
Lemma lem1760138 (x : real) : term45 x.
Proof. exact (fun h0 : (term6 x) = False => @lem1760137 x h0). Qed.
Lemma lem1760140 (x : real) (h1 : (term6 x) = True) : (term6 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760141 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760142 (x : real) (h1 : (term6 x) = True) : (term8 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760141) (@lem1760140 x h1)). Qed.
Lemma lem1760143 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760144 (x : real) (h1 : (term6 x) = True) : (term11 x) = term46.
Proof. exact (MK_COMB (@lem1760142 x h1) (@lem1760143)). Qed.
Lemma lem1760145 (x : real) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1760146 (x : real) (h1 : (term6 x) = True) : (term24 x) = (term47 x).
Proof. exact (MK_COMB (@lem1760144 x h1) (@lem1760145 x)). Qed.
Lemma lem1760148 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760149 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760148 real t2 t1). Qed.
Lemma lem1760150 (x : real) : (term47 x) = term9.
Proof. exact (@lem1760149 (term23 x) term9). Qed.
Lemma lem1760151 (x : real) (h1 : (term6 x) = True) : (term24 x) = term9.
Proof. exact (TRANS (@lem1760146 x h1) (@lem1760150 x)). Qed.
Lemma lem1760152 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760153 (x : real) (h1 : (term6 x) = True) : (term26 x) = term48.
Proof. exact (MK_COMB (@lem1760152) (@lem1760151 x h1)). Qed.
Lemma lem1760154 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1760155 (x : real) (h1 : (term6 x) = True) : ((term24 x) = (term1 x)) = (term9 = (term1 x)).
Proof. exact (MK_COMB (@lem1760153 x h1) (@lem1760154 x)). Qed.
Lemma lem1760158 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760159 (x : real) (h1 : (term6 x) = True) : (term37 x) = (term49 x).
Proof. exact (MK_COMB (@lem1760158) (@lem1760155 x h1)). Qed.
Lemma lem1760160 (x : real) : term50 x.
Proof. exact (fun h0 : (term6 x) = True => @lem1760159 x h0). Qed.
Lemma lem1760161 (x : real) : term51 x.
Proof. exact (conj (@lem1760138 x) (@lem1760160 x)). Qed.
Lemma lem1760163 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1760164 (x : real) : term53 x.
Proof. exact (@lem1760163 (term37 x) (term49 x) (term6 x) (term44 x)). Qed.
Lemma lem1760179 (x : real) : (term37 x) = (term54 x).
Proof. exact (@lem1760164 x (@lem1760161 x)). Qed.
Lemma lem1760183 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760184 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760185 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760184) (@lem1760183 x h1)). Qed.
Lemma lem1760186 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760187 (x : real) (h1 : (term55 x) = False) : (term57 x) = term41.
Proof. exact (MK_COMB (@lem1760185 x h1) (@lem1760186)). Qed.
Lemma lem1760188 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760189 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1760187 x h1) (@lem1760188 x)). Qed.
Lemma lem1760191 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760192 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760191 real t1 t2). Qed.
Lemma lem1760193 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1760192 term9 (term58 x)). Qed.
Lemma lem1760194 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term58 x).
Proof. exact (TRANS (@lem1760189 x h1) (@lem1760193 x)). Qed.
Lemma lem1760195 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760196 (x : real) (h1 : (term55 x) = False) : (term6 x) = (term60 x).
Proof. exact (MK_COMB (@lem1760195) (@lem1760194 x h1)). Qed.
Lemma lem1760197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760198 (x : real) (h1 : (term55 x) = False) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1760197) (@lem1760196 x h1)). Qed.
Lemma lem1760200 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760201 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760202 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760201) (@lem1760200 x h1)). Qed.
Lemma lem1760203 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760204 (x : real) (h1 : (term55 x) = False) : (term57 x) = term41.
Proof. exact (MK_COMB (@lem1760202 x h1) (@lem1760203)). Qed.
Lemma lem1760205 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760206 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1760204 x h1) (@lem1760205 x)). Qed.
Lemma lem1760208 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760209 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760208 real t1 t2). Qed.
Lemma lem1760210 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1760209 term9 (term58 x)). Qed.
Lemma lem1760211 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term58 x).
Proof. exact (TRANS (@lem1760206 x h1) (@lem1760210 x)). Qed.
Lemma lem1760212 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760213 (x : real) (h1 : (term55 x) = False) : (term9 = (term1 x)) = (term9 = (term58 x)).
Proof. exact (MK_COMB (@lem1760212) (@lem1760211 x h1)). Qed.
Lemma lem1760216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760217 (x : real) (h1 : (term55 x) = False) : (term49 x) = (term63 x).
Proof. exact (MK_COMB (@lem1760216) (@lem1760213 x h1)). Qed.
Lemma lem1760218 (x : real) (h1 : (term55 x) = False) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1760198 x h1) (@lem1760217 x h1)). Qed.
Lemma lem1760221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760222 (x : real) (h1 : (term55 x) = False) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem1760221) (@lem1760218 x h1)). Qed.
Lemma lem1760224 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760225 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760226 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760225) (@lem1760224 x h1)). Qed.
Lemma lem1760227 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760228 (x : real) (h1 : (term55 x) = False) : (term57 x) = term41.
Proof. exact (MK_COMB (@lem1760226 x h1) (@lem1760227)). Qed.
Lemma lem1760229 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760230 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1760228 x h1) (@lem1760229 x)). Qed.
Lemma lem1760232 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760233 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760232 real t1 t2). Qed.
Lemma lem1760234 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1760233 term9 (term58 x)). Qed.
Lemma lem1760235 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term58 x).
Proof. exact (TRANS (@lem1760230 x h1) (@lem1760234 x)). Qed.
Lemma lem1760236 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760237 (x : real) (h1 : (term55 x) = False) : (term6 x) = (term60 x).
Proof. exact (MK_COMB (@lem1760236) (@lem1760235 x h1)). Qed.
Lemma lem1760238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760239 (x : real) (h1 : (term55 x) = False) : (term68 x) = (term69 x).
Proof. exact (MK_COMB (@lem1760238) (@lem1760237 x h1)). Qed.
Lemma lem1760240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760241 (x : real) (h1 : (term55 x) = False) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1760240) (@lem1760239 x h1)). Qed.
Lemma lem1760243 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760244 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760245 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760244) (@lem1760243 x h1)). Qed.
Lemma lem1760246 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760247 (x : real) (h1 : (term55 x) = False) : (term57 x) = term41.
Proof. exact (MK_COMB (@lem1760245 x h1) (@lem1760246)). Qed.
Lemma lem1760248 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760249 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1760247 x h1) (@lem1760248 x)). Qed.
Lemma lem1760251 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760252 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760251 real t1 t2). Qed.
Lemma lem1760253 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1760252 term9 (term58 x)). Qed.
Lemma lem1760254 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term58 x).
Proof. exact (TRANS (@lem1760249 x h1) (@lem1760253 x)). Qed.
Lemma lem1760255 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760256 (x : real) (h1 : (term55 x) = False) : (term13 x) = (term72 x).
Proof. exact (MK_COMB (@lem1760255) (@lem1760254 x h1)). Qed.
Lemma lem1760257 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760258 (x : real) (h1 : (term55 x) = False) : (term16 x) = (term73 x).
Proof. exact (MK_COMB (@lem1760256 x h1) (@lem1760257)). Qed.
Lemma lem1760259 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760260 (x : real) (h1 : (term55 x) = False) : (term18 x) = (term74 x).
Proof. exact (MK_COMB (@lem1760259) (@lem1760258 x h1)). Qed.
Lemma lem1760261 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760262 (x : real) (h1 : (term55 x) = False) : (term21 x) = (term75 x).
Proof. exact (MK_COMB (@lem1760260 x h1) (@lem1760261)). Qed.
Lemma lem1760263 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760264 (x : real) (h1 : (term55 x) = False) : (term23 x) = (term76 x).
Proof. exact (MK_COMB (@lem1760262 x h1) (@lem1760263)). Qed.
Lemma lem1760265 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760266 (x : real) (h1 : (term55 x) = False) : (term43 x) = (term77 x).
Proof. exact (MK_COMB (@lem1760265) (@lem1760264 x h1)). Qed.
Lemma lem1760268 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760269 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760270 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760269) (@lem1760268 x h1)). Qed.
Lemma lem1760271 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760272 (x : real) (h1 : (term55 x) = False) : (term57 x) = term41.
Proof. exact (MK_COMB (@lem1760270 x h1) (@lem1760271)). Qed.
Lemma lem1760273 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760274 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1760272 x h1) (@lem1760273 x)). Qed.
Lemma lem1760276 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760277 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760276 real t1 t2). Qed.
Lemma lem1760278 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1760277 term9 (term58 x)). Qed.
Lemma lem1760279 (x : real) (h1 : (term55 x) = False) : (term1 x) = (term58 x).
Proof. exact (TRANS (@lem1760274 x h1) (@lem1760278 x)). Qed.
Lemma lem1760280 (x : real) (h1 : (term55 x) = False) : ((term23 x) = (term1 x)) = ((term76 x) = (term58 x)).
Proof. exact (MK_COMB (@lem1760266 x h1) (@lem1760279 x h1)). Qed.
Lemma lem1760283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760284 (x : real) (h1 : (term55 x) = False) : (term44 x) = (term78 x).
Proof. exact (MK_COMB (@lem1760283) (@lem1760280 x h1)). Qed.
Lemma lem1760285 (x : real) (h1 : (term55 x) = False) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1760241 x h1) (@lem1760284 x h1)). Qed.
Lemma lem1760288 (x : real) (h1 : (term55 x) = False) : (term54 x) = (term81 x).
Proof. exact (MK_COMB (@lem1760222 x h1) (@lem1760285 x h1)). Qed.
Lemma lem1760291 (x : real) : term82 x.
Proof. exact (fun h0 : (term55 x) = False => @lem1760288 x h0). Qed.
Lemma lem1760293 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760294 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760295 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760294) (@lem1760293 x h1)). Qed.
Lemma lem1760296 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760297 (x : real) (h1 : (term55 x) = True) : (term57 x) = term46.
Proof. exact (MK_COMB (@lem1760295 x h1) (@lem1760296)). Qed.
Lemma lem1760298 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760299 (x : real) (h1 : (term55 x) = True) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1760297 x h1) (@lem1760298 x)). Qed.
Lemma lem1760301 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760302 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760301 real t2 t1). Qed.
Lemma lem1760303 (x : real) : (term83 x) = term9.
Proof. exact (@lem1760302 (term58 x) term9). Qed.
Lemma lem1760304 (x : real) (h1 : (term55 x) = True) : (term1 x) = term9.
Proof. exact (TRANS (@lem1760299 x h1) (@lem1760303 x)). Qed.
Lemma lem1760305 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760306 (x : real) (h1 : (term55 x) = True) : (term6 x) = term84.
Proof. exact (MK_COMB (@lem1760305) (@lem1760304 x h1)). Qed.
Lemma lem1760307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760308 (x : real) (h1 : (term55 x) = True) : (term61 x) = term85.
Proof. exact (MK_COMB (@lem1760307) (@lem1760306 x h1)). Qed.
Lemma lem1760310 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760311 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760312 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760311) (@lem1760310 x h1)). Qed.
Lemma lem1760313 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760314 (x : real) (h1 : (term55 x) = True) : (term57 x) = term46.
Proof. exact (MK_COMB (@lem1760312 x h1) (@lem1760313)). Qed.
Lemma lem1760315 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760316 (x : real) (h1 : (term55 x) = True) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1760314 x h1) (@lem1760315 x)). Qed.
Lemma lem1760318 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760319 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760318 real t2 t1). Qed.
Lemma lem1760320 (x : real) : (term83 x) = term9.
Proof. exact (@lem1760319 (term58 x) term9). Qed.
Lemma lem1760321 (x : real) (h1 : (term55 x) = True) : (term1 x) = term9.
Proof. exact (TRANS (@lem1760316 x h1) (@lem1760320 x)). Qed.
Lemma lem1760322 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760323 (x : real) (h1 : (term55 x) = True) : (term9 = (term1 x)) = (term9 = term9).
Proof. exact (MK_COMB (@lem1760322) (@lem1760321 x h1)). Qed.
Lemma lem1760325 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1760326 (x : real) : (x = x) = True.
Proof. exact (@lem1760325 real x). Qed.
Lemma lem1760327 : (term9 = term9) = True.
Proof. exact (@lem1760326 term9). Qed.
Lemma lem1760328 (x : real) (h1 : (term55 x) = True) : (term9 = (term1 x)) = True.
Proof. exact (TRANS (@lem1760323 x h1) (@lem1760327)). Qed.
Lemma lem1760329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760330 (x : real) (h1 : (term55 x) = True) : (term49 x) = (~ True).
Proof. exact (MK_COMB (@lem1760329) (@lem1760328 x h1)). Qed.
Lemma lem1760332 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1760333 (x : real) (h1 : (term55 x) = True) : (term49 x) = False.
Proof. exact (TRANS (@lem1760330 x h1) (@lem1760332)). Qed.
Lemma lem1760334 (x : real) (h1 : (term55 x) = True) : (term64 x) = term86.
Proof. exact (MK_COMB (@lem1760308 x h1) (@lem1760333 x h1)). Qed.
Lemma lem1760336 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1760337 : term86 = False.
Proof. exact (@lem1760336 term84). Qed.
Lemma lem1760338 (x : real) (h1 : (term55 x) = True) : (term64 x) = False.
Proof. exact (TRANS (@lem1760334 x h1) (@lem1760337)). Qed.
Lemma lem1760339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760340 (x : real) (h1 : (term55 x) = True) : (term66 x) = (or False).
Proof. exact (MK_COMB (@lem1760339) (@lem1760338 x h1)). Qed.
Lemma lem1760342 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760343 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760344 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760343) (@lem1760342 x h1)). Qed.
Lemma lem1760345 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760346 (x : real) (h1 : (term55 x) = True) : (term57 x) = term46.
Proof. exact (MK_COMB (@lem1760344 x h1) (@lem1760345)). Qed.
Lemma lem1760347 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760348 (x : real) (h1 : (term55 x) = True) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1760346 x h1) (@lem1760347 x)). Qed.
Lemma lem1760350 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760351 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760350 real t2 t1). Qed.
Lemma lem1760352 (x : real) : (term83 x) = term9.
Proof. exact (@lem1760351 (term58 x) term9). Qed.
Lemma lem1760353 (x : real) (h1 : (term55 x) = True) : (term1 x) = term9.
Proof. exact (TRANS (@lem1760348 x h1) (@lem1760352 x)). Qed.
Lemma lem1760354 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760355 (x : real) (h1 : (term55 x) = True) : (term6 x) = term84.
Proof. exact (MK_COMB (@lem1760354) (@lem1760353 x h1)). Qed.
Lemma lem1760356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760357 (x : real) (h1 : (term55 x) = True) : (term68 x) = term87.
Proof. exact (MK_COMB (@lem1760356) (@lem1760355 x h1)). Qed.
Lemma lem1760358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760359 (x : real) (h1 : (term55 x) = True) : (term70 x) = term88.
Proof. exact (MK_COMB (@lem1760358) (@lem1760357 x h1)). Qed.
Lemma lem1760361 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760362 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760363 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760362) (@lem1760361 x h1)). Qed.
Lemma lem1760364 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760365 (x : real) (h1 : (term55 x) = True) : (term57 x) = term46.
Proof. exact (MK_COMB (@lem1760363 x h1) (@lem1760364)). Qed.
Lemma lem1760366 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760367 (x : real) (h1 : (term55 x) = True) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1760365 x h1) (@lem1760366 x)). Qed.
Lemma lem1760369 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760370 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760369 real t2 t1). Qed.
Lemma lem1760371 (x : real) : (term83 x) = term9.
Proof. exact (@lem1760370 (term58 x) term9). Qed.
Lemma lem1760372 (x : real) (h1 : (term55 x) = True) : (term1 x) = term9.
Proof. exact (TRANS (@lem1760367 x h1) (@lem1760371 x)). Qed.
Lemma lem1760373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760374 (x : real) (h1 : (term55 x) = True) : (term13 x) = term89.
Proof. exact (MK_COMB (@lem1760373) (@lem1760372 x h1)). Qed.
Lemma lem1760375 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760376 (x : real) (h1 : (term55 x) = True) : (term16 x) = term90.
Proof. exact (MK_COMB (@lem1760374 x h1) (@lem1760375)). Qed.
Lemma lem1760377 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760378 (x : real) (h1 : (term55 x) = True) : (term18 x) = term91.
Proof. exact (MK_COMB (@lem1760377) (@lem1760376 x h1)). Qed.
Lemma lem1760379 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760380 (x : real) (h1 : (term55 x) = True) : (term21 x) = term92.
Proof. exact (MK_COMB (@lem1760378 x h1) (@lem1760379)). Qed.
Lemma lem1760381 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760382 (x : real) (h1 : (term55 x) = True) : (term23 x) = term93.
Proof. exact (MK_COMB (@lem1760380 x h1) (@lem1760381)). Qed.
Lemma lem1760383 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760384 (x : real) (h1 : (term55 x) = True) : (term43 x) = term94.
Proof. exact (MK_COMB (@lem1760383) (@lem1760382 x h1)). Qed.
Lemma lem1760386 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760387 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760388 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760387) (@lem1760386 x h1)). Qed.
Lemma lem1760389 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760390 (x : real) (h1 : (term55 x) = True) : (term57 x) = term46.
Proof. exact (MK_COMB (@lem1760388 x h1) (@lem1760389)). Qed.
Lemma lem1760391 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1760392 (x : real) (h1 : (term55 x) = True) : (term1 x) = (term83 x).
Proof. exact (MK_COMB (@lem1760390 x h1) (@lem1760391 x)). Qed.
Lemma lem1760394 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760395 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760394 real t2 t1). Qed.
Lemma lem1760396 (x : real) : (term83 x) = term9.
Proof. exact (@lem1760395 (term58 x) term9). Qed.
Lemma lem1760397 (x : real) (h1 : (term55 x) = True) : (term1 x) = term9.
Proof. exact (TRANS (@lem1760392 x h1) (@lem1760396 x)). Qed.
Lemma lem1760398 (x : real) (h1 : (term55 x) = True) : ((term23 x) = (term1 x)) = (term93 = term9).
Proof. exact (MK_COMB (@lem1760384 x h1) (@lem1760397 x h1)). Qed.
Lemma lem1760401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760402 (x : real) (h1 : (term55 x) = True) : (term44 x) = term95.
Proof. exact (MK_COMB (@lem1760401) (@lem1760398 x h1)). Qed.
Lemma lem1760403 (x : real) (h1 : (term55 x) = True) : (term79 x) = term96.
Proof. exact (MK_COMB (@lem1760359 x h1) (@lem1760402 x h1)). Qed.
Lemma lem1760406 (x : real) (h1 : (term55 x) = True) : (term54 x) = term97.
Proof. exact (MK_COMB (@lem1760340 x h1) (@lem1760403 x h1)). Qed.
Lemma lem1760408 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1760409 : term97 = term96.
Proof. exact (@lem1760408 term96). Qed.
Lemma lem1760412 (x : real) (h1 : (term55 x) = True) : (term54 x) = term96.
Proof. exact (TRANS (@lem1760406 x h1) (@lem1760409)). Qed.
Lemma lem1760413 (x : real) : term98 x.
Proof. exact (fun h0 : (term55 x) = True => @lem1760412 x h0). Qed.
Lemma lem1760414 (x : real) : term99 x.
Proof. exact (conj (@lem1760291 x) (@lem1760413 x)). Qed.
Lemma lem1760416 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1760417 (x : real) : term100 x.
Proof. exact (@lem1760416 (term54 x) term96 (term55 x) (term81 x)). Qed.
Lemma lem1760432 (x : real) : (term54 x) = (term101 x).
Proof. exact (@lem1760417 x (@lem1760414 x)). Qed.
Lemma lem1760436 (h1 : term90 = False) : term90 = False.
Proof. exact (h1). Qed.
Lemma lem1760437 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760438 (h1 : term90 = False) : term91 = (@COND real False).
Proof. exact (MK_COMB (@lem1760437) (@lem1760436 h1)). Qed.
Lemma lem1760439 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760440 (h1 : term90 = False) : term92 = term102.
Proof. exact (MK_COMB (@lem1760438 h1) (@lem1760439)). Qed.
Lemma lem1760441 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760442 (h1 : term90 = False) : term93 = term103.
Proof. exact (MK_COMB (@lem1760440 h1) (@lem1760441)). Qed.
Lemma lem1760444 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760445 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760444 real t1 t2). Qed.
Lemma lem1760446 : term103 = term14.
Proof. exact (@lem1760445 term19 term14). Qed.
Lemma lem1760447 (h1 : term90 = False) : term93 = term14.
Proof. exact (TRANS (@lem1760442 h1) (@lem1760446)). Qed.
Lemma lem1760448 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760449 (h1 : term90 = False) : term94 = term104.
Proof. exact (MK_COMB (@lem1760448) (@lem1760447 h1)). Qed.
Lemma lem1760450 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760451 (h1 : term90 = False) : (term93 = term9) = (term14 = term9).
Proof. exact (MK_COMB (@lem1760449 h1) (@lem1760450)). Qed.
Lemma lem1760454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760455 (h1 : term90 = False) : term95 = term105.
Proof. exact (MK_COMB (@lem1760454) (@lem1760451 h1)). Qed.
Lemma lem1760456 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem1760457 (h1 : term90 = False) : term96 = term106.
Proof. exact (MK_COMB (@lem1760456) (@lem1760455 h1)). Qed.
Lemma lem1760460 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1760461 (x : real) (h1 : term90 = False) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1760460 x) (@lem1760457 h1)). Qed.
Lemma lem1760464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760465 (x : real) (h1 : term90 = False) : (term110 x) = (term111 x).
Proof. exact (MK_COMB (@lem1760464) (@lem1760461 x h1)). Qed.
Lemma lem1760478 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1760479 (x : real) (h1 : term90 = False) : (term101 x) = (term113 x).
Proof. exact (MK_COMB (@lem1760465 x h1) (@lem1760478 x)). Qed.
Lemma lem1760482 (x : real) : term114 x.
Proof. exact (fun h0 : term90 = False => @lem1760479 x h0). Qed.
Lemma lem1760484 (h1 : term90 = True) : term90 = True.
Proof. exact (h1). Qed.
Lemma lem1760485 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760486 (h1 : term90 = True) : term91 = (@COND real True).
Proof. exact (MK_COMB (@lem1760485) (@lem1760484 h1)). Qed.
Lemma lem1760487 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760488 (h1 : term90 = True) : term92 = term115.
Proof. exact (MK_COMB (@lem1760486 h1) (@lem1760487)). Qed.
Lemma lem1760489 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760490 (h1 : term90 = True) : term93 = term116.
Proof. exact (MK_COMB (@lem1760488 h1) (@lem1760489)). Qed.
Lemma lem1760492 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760493 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760492 real t2 t1). Qed.
Lemma lem1760494 : term116 = term19.
Proof. exact (@lem1760493 term14 term19). Qed.
Lemma lem1760495 (h1 : term90 = True) : term93 = term19.
Proof. exact (TRANS (@lem1760490 h1) (@lem1760494)). Qed.
Lemma lem1760496 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760497 (h1 : term90 = True) : term94 = term117.
Proof. exact (MK_COMB (@lem1760496) (@lem1760495 h1)). Qed.
Lemma lem1760498 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1760499 (h1 : term90 = True) : (term93 = term9) = (term19 = term9).
Proof. exact (MK_COMB (@lem1760497 h1) (@lem1760498)). Qed.
Lemma lem1760502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760503 (h1 : term90 = True) : term95 = term118.
Proof. exact (MK_COMB (@lem1760502) (@lem1760499 h1)). Qed.
Lemma lem1760504 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem1760505 (h1 : term90 = True) : term96 = term119.
Proof. exact (MK_COMB (@lem1760504) (@lem1760503 h1)). Qed.
Lemma lem1760508 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1760509 (x : real) (h1 : term90 = True) : (term108 x) = (term120 x).
Proof. exact (MK_COMB (@lem1760508 x) (@lem1760505 h1)). Qed.
Lemma lem1760512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760513 (x : real) (h1 : term90 = True) : (term110 x) = (term121 x).
Proof. exact (MK_COMB (@lem1760512) (@lem1760509 x h1)). Qed.
Lemma lem1760526 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1760527 (x : real) (h1 : term90 = True) : (term101 x) = (term122 x).
Proof. exact (MK_COMB (@lem1760513 x h1) (@lem1760526 x)). Qed.
Lemma lem1760530 (x : real) : term123 x.
Proof. exact (fun h0 : term90 = True => @lem1760527 x h0). Qed.
Lemma lem1760531 (x : real) : term124 x.
Proof. exact (conj (@lem1760482 x) (@lem1760530 x)). Qed.
Lemma lem1760533 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1760534 (x : real) : term125 x.
Proof. exact (@lem1760533 (term101 x) (term122 x) term90 (term113 x)). Qed.
Lemma lem1760549 (x : real) : (term101 x) = (term126 x).
Proof. exact (@lem1760534 x (@lem1760531 x)). Qed.
Lemma lem1760559 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760560 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760561 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760560) (@lem1760559 x h1)). Qed.
Lemma lem1760562 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760563 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760561 x h1) (@lem1760562)). Qed.
Lemma lem1760564 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760565 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760563 x h1) (@lem1760564)). Qed.
Lemma lem1760567 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760568 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760567 real t1 t2). Qed.
Lemma lem1760569 : term103 = term14.
Proof. exact (@lem1760568 term19 term14). Qed.
Lemma lem1760570 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760565 x h1) (@lem1760569)). Qed.
Lemma lem1760571 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760572 (x : real) (h1 : (term127 x) = False) : (term60 x) = term130.
Proof. exact (MK_COMB (@lem1760571) (@lem1760570 x h1)). Qed.
Lemma lem1760573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760574 (x : real) (h1 : (term127 x) = False) : (term62 x) = term131.
Proof. exact (MK_COMB (@lem1760573) (@lem1760572 x h1)). Qed.
Lemma lem1760576 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760577 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760578 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760577) (@lem1760576 x h1)). Qed.
Lemma lem1760579 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760580 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760578 x h1) (@lem1760579)). Qed.
Lemma lem1760581 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760582 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760580 x h1) (@lem1760581)). Qed.
Lemma lem1760584 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760585 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760584 real t1 t2). Qed.
Lemma lem1760586 : term103 = term14.
Proof. exact (@lem1760585 term19 term14). Qed.
Lemma lem1760587 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760582 x h1) (@lem1760586)). Qed.
Lemma lem1760588 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760589 (x : real) (h1 : (term127 x) = False) : (term9 = (term58 x)) = (term9 = term14).
Proof. exact (MK_COMB (@lem1760588) (@lem1760587 x h1)). Qed.
Lemma lem1760592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760593 (x : real) (h1 : (term127 x) = False) : (term63 x) = term132.
Proof. exact (MK_COMB (@lem1760592) (@lem1760589 x h1)). Qed.
Lemma lem1760594 (x : real) (h1 : (term127 x) = False) : (term65 x) = term133.
Proof. exact (MK_COMB (@lem1760574 x h1) (@lem1760593 x h1)). Qed.
Lemma lem1760597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760598 (x : real) (h1 : (term127 x) = False) : (term67 x) = term134.
Proof. exact (MK_COMB (@lem1760597) (@lem1760594 x h1)). Qed.
Lemma lem1760600 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760601 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760602 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760601) (@lem1760600 x h1)). Qed.
Lemma lem1760603 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760604 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760602 x h1) (@lem1760603)). Qed.
Lemma lem1760605 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760606 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760604 x h1) (@lem1760605)). Qed.
Lemma lem1760608 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760609 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760608 real t1 t2). Qed.
Lemma lem1760610 : term103 = term14.
Proof. exact (@lem1760609 term19 term14). Qed.
Lemma lem1760611 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760606 x h1) (@lem1760610)). Qed.
Lemma lem1760612 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760613 (x : real) (h1 : (term127 x) = False) : (term60 x) = term130.
Proof. exact (MK_COMB (@lem1760612) (@lem1760611 x h1)). Qed.
Lemma lem1760614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760615 (x : real) (h1 : (term127 x) = False) : (term69 x) = term135.
Proof. exact (MK_COMB (@lem1760614) (@lem1760613 x h1)). Qed.
Lemma lem1760616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760617 (x : real) (h1 : (term127 x) = False) : (term71 x) = term136.
Proof. exact (MK_COMB (@lem1760616) (@lem1760615 x h1)). Qed.
Lemma lem1760619 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760620 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760621 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760620) (@lem1760619 x h1)). Qed.
Lemma lem1760622 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760623 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760621 x h1) (@lem1760622)). Qed.
Lemma lem1760624 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760625 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760623 x h1) (@lem1760624)). Qed.
Lemma lem1760627 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760628 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760627 real t1 t2). Qed.
Lemma lem1760629 : term103 = term14.
Proof. exact (@lem1760628 term19 term14). Qed.
Lemma lem1760630 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760625 x h1) (@lem1760629)). Qed.
Lemma lem1760631 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760632 (x : real) (h1 : (term127 x) = False) : (term72 x) = term4.
Proof. exact (MK_COMB (@lem1760631) (@lem1760630 x h1)). Qed.
Lemma lem1760633 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760634 (x : real) (h1 : (term127 x) = False) : (term73 x) = term130.
Proof. exact (MK_COMB (@lem1760632 x h1) (@lem1760633)). Qed.
Lemma lem1760635 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760636 (x : real) (h1 : (term127 x) = False) : (term74 x) = term137.
Proof. exact (MK_COMB (@lem1760635) (@lem1760634 x h1)). Qed.
Lemma lem1760637 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760638 (x : real) (h1 : (term127 x) = False) : (term75 x) = term138.
Proof. exact (MK_COMB (@lem1760636 x h1) (@lem1760637)). Qed.
Lemma lem1760639 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760640 (x : real) (h1 : (term127 x) = False) : (term76 x) = term139.
Proof. exact (MK_COMB (@lem1760638 x h1) (@lem1760639)). Qed.
Lemma lem1760641 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760642 (x : real) (h1 : (term127 x) = False) : (term77 x) = term140.
Proof. exact (MK_COMB (@lem1760641) (@lem1760640 x h1)). Qed.
Lemma lem1760644 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760645 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760646 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760645) (@lem1760644 x h1)). Qed.
Lemma lem1760647 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760648 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760646 x h1) (@lem1760647)). Qed.
Lemma lem1760649 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760650 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760648 x h1) (@lem1760649)). Qed.
Lemma lem1760652 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760653 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760652 real t1 t2). Qed.
Lemma lem1760654 : term103 = term14.
Proof. exact (@lem1760653 term19 term14). Qed.
Lemma lem1760655 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760650 x h1) (@lem1760654)). Qed.
Lemma lem1760656 (x : real) (h1 : (term127 x) = False) : ((term76 x) = (term58 x)) = (term139 = term14).
Proof. exact (MK_COMB (@lem1760642 x h1) (@lem1760655 x h1)). Qed.
Lemma lem1760659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760660 (x : real) (h1 : (term127 x) = False) : (term78 x) = term141.
Proof. exact (MK_COMB (@lem1760659) (@lem1760656 x h1)). Qed.
Lemma lem1760661 (x : real) (h1 : (term127 x) = False) : (term80 x) = term142.
Proof. exact (MK_COMB (@lem1760617 x h1) (@lem1760660 x h1)). Qed.
Lemma lem1760664 (x : real) (h1 : (term127 x) = False) : (term81 x) = term143.
Proof. exact (MK_COMB (@lem1760598 x h1) (@lem1760661 x h1)). Qed.
Lemma lem1760667 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1760668 (x : real) (h1 : (term127 x) = False) : (term112 x) = (term145 x).
Proof. exact (MK_COMB (@lem1760667 x) (@lem1760664 x h1)). Qed.
Lemma lem1760671 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1760672 (x : real) (h1 : (term127 x) = False) : (term122 x) = (term146 x).
Proof. exact (MK_COMB (@lem1760671 x) (@lem1760668 x h1)). Qed.
Lemma lem1760675 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1760676 (x : real) (h1 : (term127 x) = False) : (term148 x) = (term149 x).
Proof. exact (MK_COMB (@lem1760675) (@lem1760672 x h1)). Qed.
Lemma lem1760679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760680 (x : real) (h1 : (term127 x) = False) : (term150 x) = (term151 x).
Proof. exact (MK_COMB (@lem1760679) (@lem1760676 x h1)). Qed.
Lemma lem1760688 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760689 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760690 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760689) (@lem1760688 x h1)). Qed.
Lemma lem1760691 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760692 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760690 x h1) (@lem1760691)). Qed.
Lemma lem1760693 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760694 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760692 x h1) (@lem1760693)). Qed.
Lemma lem1760696 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760697 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760696 real t1 t2). Qed.
Lemma lem1760698 : term103 = term14.
Proof. exact (@lem1760697 term19 term14). Qed.
Lemma lem1760699 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760694 x h1) (@lem1760698)). Qed.
Lemma lem1760700 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760701 (x : real) (h1 : (term127 x) = False) : (term60 x) = term130.
Proof. exact (MK_COMB (@lem1760700) (@lem1760699 x h1)). Qed.
Lemma lem1760702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760703 (x : real) (h1 : (term127 x) = False) : (term62 x) = term131.
Proof. exact (MK_COMB (@lem1760702) (@lem1760701 x h1)). Qed.
Lemma lem1760705 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760706 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760707 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760706) (@lem1760705 x h1)). Qed.
Lemma lem1760708 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760709 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760707 x h1) (@lem1760708)). Qed.
Lemma lem1760710 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760711 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760709 x h1) (@lem1760710)). Qed.
Lemma lem1760713 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760714 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760713 real t1 t2). Qed.
Lemma lem1760715 : term103 = term14.
Proof. exact (@lem1760714 term19 term14). Qed.
Lemma lem1760716 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760711 x h1) (@lem1760715)). Qed.
Lemma lem1760717 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760718 (x : real) (h1 : (term127 x) = False) : (term9 = (term58 x)) = (term9 = term14).
Proof. exact (MK_COMB (@lem1760717) (@lem1760716 x h1)). Qed.
Lemma lem1760721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760722 (x : real) (h1 : (term127 x) = False) : (term63 x) = term132.
Proof. exact (MK_COMB (@lem1760721) (@lem1760718 x h1)). Qed.
Lemma lem1760723 (x : real) (h1 : (term127 x) = False) : (term65 x) = term133.
Proof. exact (MK_COMB (@lem1760703 x h1) (@lem1760722 x h1)). Qed.
Lemma lem1760726 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760727 (x : real) (h1 : (term127 x) = False) : (term67 x) = term134.
Proof. exact (MK_COMB (@lem1760726) (@lem1760723 x h1)). Qed.
Lemma lem1760729 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760730 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760731 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760730) (@lem1760729 x h1)). Qed.
Lemma lem1760732 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760733 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760731 x h1) (@lem1760732)). Qed.
Lemma lem1760734 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760735 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760733 x h1) (@lem1760734)). Qed.
Lemma lem1760737 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760738 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760737 real t1 t2). Qed.
Lemma lem1760739 : term103 = term14.
Proof. exact (@lem1760738 term19 term14). Qed.
Lemma lem1760740 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760735 x h1) (@lem1760739)). Qed.
Lemma lem1760741 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760742 (x : real) (h1 : (term127 x) = False) : (term60 x) = term130.
Proof. exact (MK_COMB (@lem1760741) (@lem1760740 x h1)). Qed.
Lemma lem1760743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760744 (x : real) (h1 : (term127 x) = False) : (term69 x) = term135.
Proof. exact (MK_COMB (@lem1760743) (@lem1760742 x h1)). Qed.
Lemma lem1760745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760746 (x : real) (h1 : (term127 x) = False) : (term71 x) = term136.
Proof. exact (MK_COMB (@lem1760745) (@lem1760744 x h1)). Qed.
Lemma lem1760748 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760749 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760750 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760749) (@lem1760748 x h1)). Qed.
Lemma lem1760751 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760752 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760750 x h1) (@lem1760751)). Qed.
Lemma lem1760753 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760754 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760752 x h1) (@lem1760753)). Qed.
Lemma lem1760756 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760757 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760756 real t1 t2). Qed.
Lemma lem1760758 : term103 = term14.
Proof. exact (@lem1760757 term19 term14). Qed.
Lemma lem1760759 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760754 x h1) (@lem1760758)). Qed.
Lemma lem1760760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760761 (x : real) (h1 : (term127 x) = False) : (term72 x) = term4.
Proof. exact (MK_COMB (@lem1760760) (@lem1760759 x h1)). Qed.
Lemma lem1760762 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760763 (x : real) (h1 : (term127 x) = False) : (term73 x) = term130.
Proof. exact (MK_COMB (@lem1760761 x h1) (@lem1760762)). Qed.
Lemma lem1760764 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760765 (x : real) (h1 : (term127 x) = False) : (term74 x) = term137.
Proof. exact (MK_COMB (@lem1760764) (@lem1760763 x h1)). Qed.
Lemma lem1760766 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760767 (x : real) (h1 : (term127 x) = False) : (term75 x) = term138.
Proof. exact (MK_COMB (@lem1760765 x h1) (@lem1760766)). Qed.
Lemma lem1760768 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760769 (x : real) (h1 : (term127 x) = False) : (term76 x) = term139.
Proof. exact (MK_COMB (@lem1760767 x h1) (@lem1760768)). Qed.
Lemma lem1760770 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760771 (x : real) (h1 : (term127 x) = False) : (term77 x) = term140.
Proof. exact (MK_COMB (@lem1760770) (@lem1760769 x h1)). Qed.
Lemma lem1760773 (x : real) (h1 : (term127 x) = False) : (term127 x) = False.
Proof. exact (h1). Qed.
Lemma lem1760774 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760775 (x : real) (h1 : (term127 x) = False) : (term128 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1760774) (@lem1760773 x h1)). Qed.
Lemma lem1760776 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760777 (x : real) (h1 : (term127 x) = False) : (term129 x) = term102.
Proof. exact (MK_COMB (@lem1760775 x h1) (@lem1760776)). Qed.
Lemma lem1760778 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760779 (x : real) (h1 : (term127 x) = False) : (term58 x) = term103.
Proof. exact (MK_COMB (@lem1760777 x h1) (@lem1760778)). Qed.
Lemma lem1760781 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1760782 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1760781 real t1 t2). Qed.
Lemma lem1760783 : term103 = term14.
Proof. exact (@lem1760782 term19 term14). Qed.
Lemma lem1760784 (x : real) (h1 : (term127 x) = False) : (term58 x) = term14.
Proof. exact (TRANS (@lem1760779 x h1) (@lem1760783)). Qed.
Lemma lem1760785 (x : real) (h1 : (term127 x) = False) : ((term76 x) = (term58 x)) = (term139 = term14).
Proof. exact (MK_COMB (@lem1760771 x h1) (@lem1760784 x h1)). Qed.
Lemma lem1760788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760789 (x : real) (h1 : (term127 x) = False) : (term78 x) = term141.
Proof. exact (MK_COMB (@lem1760788) (@lem1760785 x h1)). Qed.
Lemma lem1760790 (x : real) (h1 : (term127 x) = False) : (term80 x) = term142.
Proof. exact (MK_COMB (@lem1760746 x h1) (@lem1760789 x h1)). Qed.
Lemma lem1760793 (x : real) (h1 : (term127 x) = False) : (term81 x) = term143.
Proof. exact (MK_COMB (@lem1760727 x h1) (@lem1760790 x h1)). Qed.
Lemma lem1760796 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1760797 (x : real) (h1 : (term127 x) = False) : (term112 x) = (term145 x).
Proof. exact (MK_COMB (@lem1760796 x) (@lem1760793 x h1)). Qed.
Lemma lem1760800 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1760801 (x : real) (h1 : (term127 x) = False) : (term113 x) = (term152 x).
Proof. exact (MK_COMB (@lem1760800 x) (@lem1760797 x h1)). Qed.
Lemma lem1760804 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1760805 (x : real) (h1 : (term127 x) = False) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1760804) (@lem1760801 x h1)). Qed.
Lemma lem1760808 (x : real) (h1 : (term127 x) = False) : (term126 x) = (term156 x).
Proof. exact (MK_COMB (@lem1760680 x h1) (@lem1760805 x h1)). Qed.
Lemma lem1760811 (x : real) : term157 x.
Proof. exact (fun h0 : (term127 x) = False => @lem1760808 x h0). Qed.
Lemma lem1760819 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760820 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760821 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760820) (@lem1760819 x h1)). Qed.
Lemma lem1760822 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760823 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760821 x h1) (@lem1760822)). Qed.
Lemma lem1760824 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760825 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760823 x h1) (@lem1760824)). Qed.
Lemma lem1760827 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760828 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760827 real t2 t1). Qed.
Lemma lem1760829 : term116 = term19.
Proof. exact (@lem1760828 term14 term19). Qed.
Lemma lem1760830 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760825 x h1) (@lem1760829)). Qed.
Lemma lem1760831 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760832 (x : real) (h1 : (term127 x) = True) : (term60 x) = term158.
Proof. exact (MK_COMB (@lem1760831) (@lem1760830 x h1)). Qed.
Lemma lem1760833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760834 (x : real) (h1 : (term127 x) = True) : (term62 x) = term159.
Proof. exact (MK_COMB (@lem1760833) (@lem1760832 x h1)). Qed.
Lemma lem1760836 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760837 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760838 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760837) (@lem1760836 x h1)). Qed.
Lemma lem1760839 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760840 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760838 x h1) (@lem1760839)). Qed.
Lemma lem1760841 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760842 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760840 x h1) (@lem1760841)). Qed.
Lemma lem1760844 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760845 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760844 real t2 t1). Qed.
Lemma lem1760846 : term116 = term19.
Proof. exact (@lem1760845 term14 term19). Qed.
Lemma lem1760847 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760842 x h1) (@lem1760846)). Qed.
Lemma lem1760848 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760849 (x : real) (h1 : (term127 x) = True) : (term9 = (term58 x)) = (term9 = term19).
Proof. exact (MK_COMB (@lem1760848) (@lem1760847 x h1)). Qed.
Lemma lem1760852 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760853 (x : real) (h1 : (term127 x) = True) : (term63 x) = term160.
Proof. exact (MK_COMB (@lem1760852) (@lem1760849 x h1)). Qed.
Lemma lem1760854 (x : real) (h1 : (term127 x) = True) : (term65 x) = term161.
Proof. exact (MK_COMB (@lem1760834 x h1) (@lem1760853 x h1)). Qed.
Lemma lem1760857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760858 (x : real) (h1 : (term127 x) = True) : (term67 x) = term162.
Proof. exact (MK_COMB (@lem1760857) (@lem1760854 x h1)). Qed.
Lemma lem1760860 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760861 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760862 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760861) (@lem1760860 x h1)). Qed.
Lemma lem1760863 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760864 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760862 x h1) (@lem1760863)). Qed.
Lemma lem1760865 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760866 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760864 x h1) (@lem1760865)). Qed.
Lemma lem1760868 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760869 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760868 real t2 t1). Qed.
Lemma lem1760870 : term116 = term19.
Proof. exact (@lem1760869 term14 term19). Qed.
Lemma lem1760871 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760866 x h1) (@lem1760870)). Qed.
Lemma lem1760872 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760873 (x : real) (h1 : (term127 x) = True) : (term60 x) = term158.
Proof. exact (MK_COMB (@lem1760872) (@lem1760871 x h1)). Qed.
Lemma lem1760874 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760875 (x : real) (h1 : (term127 x) = True) : (term69 x) = term163.
Proof. exact (MK_COMB (@lem1760874) (@lem1760873 x h1)). Qed.
Lemma lem1760876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760877 (x : real) (h1 : (term127 x) = True) : (term71 x) = term164.
Proof. exact (MK_COMB (@lem1760876) (@lem1760875 x h1)). Qed.
Lemma lem1760879 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760880 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760881 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760880) (@lem1760879 x h1)). Qed.
Lemma lem1760882 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760883 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760881 x h1) (@lem1760882)). Qed.
Lemma lem1760884 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760885 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760883 x h1) (@lem1760884)). Qed.
Lemma lem1760887 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760888 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760887 real t2 t1). Qed.
Lemma lem1760889 : term116 = term19.
Proof. exact (@lem1760888 term14 term19). Qed.
Lemma lem1760890 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760885 x h1) (@lem1760889)). Qed.
Lemma lem1760891 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1760892 (x : real) (h1 : (term127 x) = True) : (term72 x) = term165.
Proof. exact (MK_COMB (@lem1760891) (@lem1760890 x h1)). Qed.
Lemma lem1760893 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760894 (x : real) (h1 : (term127 x) = True) : (term73 x) = term166.
Proof. exact (MK_COMB (@lem1760892 x h1) (@lem1760893)). Qed.
Lemma lem1760895 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760896 (x : real) (h1 : (term127 x) = True) : (term74 x) = term167.
Proof. exact (MK_COMB (@lem1760895) (@lem1760894 x h1)). Qed.
Lemma lem1760897 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760898 (x : real) (h1 : (term127 x) = True) : (term75 x) = term168.
Proof. exact (MK_COMB (@lem1760896 x h1) (@lem1760897)). Qed.
Lemma lem1760899 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760900 (x : real) (h1 : (term127 x) = True) : (term76 x) = term169.
Proof. exact (MK_COMB (@lem1760898 x h1) (@lem1760899)). Qed.
Lemma lem1760901 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1760902 (x : real) (h1 : (term127 x) = True) : (term77 x) = term170.
Proof. exact (MK_COMB (@lem1760901) (@lem1760900 x h1)). Qed.
Lemma lem1760904 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760905 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760906 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760905) (@lem1760904 x h1)). Qed.
Lemma lem1760907 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760908 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760906 x h1) (@lem1760907)). Qed.
Lemma lem1760909 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760910 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760908 x h1) (@lem1760909)). Qed.
Lemma lem1760912 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760913 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760912 real t2 t1). Qed.
Lemma lem1760914 : term116 = term19.
Proof. exact (@lem1760913 term14 term19). Qed.
Lemma lem1760915 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760910 x h1) (@lem1760914)). Qed.
Lemma lem1760916 (x : real) (h1 : (term127 x) = True) : ((term76 x) = (term58 x)) = (term169 = term19).
Proof. exact (MK_COMB (@lem1760902 x h1) (@lem1760915 x h1)). Qed.
Lemma lem1760919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760920 (x : real) (h1 : (term127 x) = True) : (term78 x) = term171.
Proof. exact (MK_COMB (@lem1760919) (@lem1760916 x h1)). Qed.
Lemma lem1760921 (x : real) (h1 : (term127 x) = True) : (term80 x) = term172.
Proof. exact (MK_COMB (@lem1760877 x h1) (@lem1760920 x h1)). Qed.
Lemma lem1760924 (x : real) (h1 : (term127 x) = True) : (term81 x) = term173.
Proof. exact (MK_COMB (@lem1760858 x h1) (@lem1760921 x h1)). Qed.
Lemma lem1760927 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1760928 (x : real) (h1 : (term127 x) = True) : (term112 x) = (term174 x).
Proof. exact (MK_COMB (@lem1760927 x) (@lem1760924 x h1)). Qed.
Lemma lem1760931 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1760932 (x : real) (h1 : (term127 x) = True) : (term122 x) = (term175 x).
Proof. exact (MK_COMB (@lem1760931 x) (@lem1760928 x h1)). Qed.
Lemma lem1760935 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1760936 (x : real) (h1 : (term127 x) = True) : (term148 x) = (term176 x).
Proof. exact (MK_COMB (@lem1760935) (@lem1760932 x h1)). Qed.
Lemma lem1760939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760940 (x : real) (h1 : (term127 x) = True) : (term150 x) = (term177 x).
Proof. exact (MK_COMB (@lem1760939) (@lem1760936 x h1)). Qed.
Lemma lem1760948 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760949 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760950 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760949) (@lem1760948 x h1)). Qed.
Lemma lem1760951 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760952 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760950 x h1) (@lem1760951)). Qed.
Lemma lem1760953 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760954 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760952 x h1) (@lem1760953)). Qed.
Lemma lem1760956 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760957 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760956 real t2 t1). Qed.
Lemma lem1760958 : term116 = term19.
Proof. exact (@lem1760957 term14 term19). Qed.
Lemma lem1760959 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760954 x h1) (@lem1760958)). Qed.
Lemma lem1760960 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1760961 (x : real) (h1 : (term127 x) = True) : (term60 x) = term158.
Proof. exact (MK_COMB (@lem1760960) (@lem1760959 x h1)). Qed.
Lemma lem1760962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1760963 (x : real) (h1 : (term127 x) = True) : (term62 x) = term159.
Proof. exact (MK_COMB (@lem1760962) (@lem1760961 x h1)). Qed.
Lemma lem1760965 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760966 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760967 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760966) (@lem1760965 x h1)). Qed.
Lemma lem1760968 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760969 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760967 x h1) (@lem1760968)). Qed.
Lemma lem1760970 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760971 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760969 x h1) (@lem1760970)). Qed.
Lemma lem1760973 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760974 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760973 real t2 t1). Qed.
Lemma lem1760975 : term116 = term19.
Proof. exact (@lem1760974 term14 term19). Qed.
Lemma lem1760976 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760971 x h1) (@lem1760975)). Qed.
Lemma lem1760977 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1760978 (x : real) (h1 : (term127 x) = True) : (term9 = (term58 x)) = (term9 = term19).
Proof. exact (MK_COMB (@lem1760977) (@lem1760976 x h1)). Qed.
Lemma lem1760981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1760982 (x : real) (h1 : (term127 x) = True) : (term63 x) = term160.
Proof. exact (MK_COMB (@lem1760981) (@lem1760978 x h1)). Qed.
Lemma lem1760983 (x : real) (h1 : (term127 x) = True) : (term65 x) = term161.
Proof. exact (MK_COMB (@lem1760963 x h1) (@lem1760982 x h1)). Qed.
Lemma lem1760986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1760987 (x : real) (h1 : (term127 x) = True) : (term67 x) = term162.
Proof. exact (MK_COMB (@lem1760986) (@lem1760983 x h1)). Qed.
Lemma lem1760989 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1760990 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1760991 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1760990) (@lem1760989 x h1)). Qed.
Lemma lem1760992 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1760993 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1760991 x h1) (@lem1760992)). Qed.
Lemma lem1760994 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1760995 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1760993 x h1) (@lem1760994)). Qed.
Lemma lem1760997 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1760998 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1760997 real t2 t1). Qed.
Lemma lem1760999 : term116 = term19.
Proof. exact (@lem1760998 term14 term19). Qed.
Lemma lem1761000 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1760995 x h1) (@lem1760999)). Qed.
Lemma lem1761001 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1761002 (x : real) (h1 : (term127 x) = True) : (term60 x) = term158.
Proof. exact (MK_COMB (@lem1761001) (@lem1761000 x h1)). Qed.
Lemma lem1761003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761004 (x : real) (h1 : (term127 x) = True) : (term69 x) = term163.
Proof. exact (MK_COMB (@lem1761003) (@lem1761002 x h1)). Qed.
Lemma lem1761005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761006 (x : real) (h1 : (term127 x) = True) : (term71 x) = term164.
Proof. exact (MK_COMB (@lem1761005) (@lem1761004 x h1)). Qed.
Lemma lem1761008 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1761009 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761010 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1761009) (@lem1761008 x h1)). Qed.
Lemma lem1761011 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761012 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1761010 x h1) (@lem1761011)). Qed.
Lemma lem1761013 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761014 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1761012 x h1) (@lem1761013)). Qed.
Lemma lem1761016 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1761017 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1761016 real t2 t1). Qed.
Lemma lem1761018 : term116 = term19.
Proof. exact (@lem1761017 term14 term19). Qed.
Lemma lem1761019 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1761014 x h1) (@lem1761018)). Qed.
Lemma lem1761020 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1761021 (x : real) (h1 : (term127 x) = True) : (term72 x) = term165.
Proof. exact (MK_COMB (@lem1761020) (@lem1761019 x h1)). Qed.
Lemma lem1761022 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761023 (x : real) (h1 : (term127 x) = True) : (term73 x) = term166.
Proof. exact (MK_COMB (@lem1761021 x h1) (@lem1761022)). Qed.
Lemma lem1761024 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761025 (x : real) (h1 : (term127 x) = True) : (term74 x) = term167.
Proof. exact (MK_COMB (@lem1761024) (@lem1761023 x h1)). Qed.
Lemma lem1761026 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761027 (x : real) (h1 : (term127 x) = True) : (term75 x) = term168.
Proof. exact (MK_COMB (@lem1761025 x h1) (@lem1761026)). Qed.
Lemma lem1761028 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761029 (x : real) (h1 : (term127 x) = True) : (term76 x) = term169.
Proof. exact (MK_COMB (@lem1761027 x h1) (@lem1761028)). Qed.
Lemma lem1761030 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761031 (x : real) (h1 : (term127 x) = True) : (term77 x) = term170.
Proof. exact (MK_COMB (@lem1761030) (@lem1761029 x h1)). Qed.
Lemma lem1761033 (x : real) (h1 : (term127 x) = True) : (term127 x) = True.
Proof. exact (h1). Qed.
Lemma lem1761034 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761035 (x : real) (h1 : (term127 x) = True) : (term128 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1761034) (@lem1761033 x h1)). Qed.
Lemma lem1761036 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761037 (x : real) (h1 : (term127 x) = True) : (term129 x) = term115.
Proof. exact (MK_COMB (@lem1761035 x h1) (@lem1761036)). Qed.
Lemma lem1761038 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761039 (x : real) (h1 : (term127 x) = True) : (term58 x) = term116.
Proof. exact (MK_COMB (@lem1761037 x h1) (@lem1761038)). Qed.
Lemma lem1761041 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1761042 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1761041 real t2 t1). Qed.
Lemma lem1761043 : term116 = term19.
Proof. exact (@lem1761042 term14 term19). Qed.
Lemma lem1761044 (x : real) (h1 : (term127 x) = True) : (term58 x) = term19.
Proof. exact (TRANS (@lem1761039 x h1) (@lem1761043)). Qed.
Lemma lem1761045 (x : real) (h1 : (term127 x) = True) : ((term76 x) = (term58 x)) = (term169 = term19).
Proof. exact (MK_COMB (@lem1761031 x h1) (@lem1761044 x h1)). Qed.
Lemma lem1761048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761049 (x : real) (h1 : (term127 x) = True) : (term78 x) = term171.
Proof. exact (MK_COMB (@lem1761048) (@lem1761045 x h1)). Qed.
Lemma lem1761050 (x : real) (h1 : (term127 x) = True) : (term80 x) = term172.
Proof. exact (MK_COMB (@lem1761006 x h1) (@lem1761049 x h1)). Qed.
Lemma lem1761053 (x : real) (h1 : (term127 x) = True) : (term81 x) = term173.
Proof. exact (MK_COMB (@lem1760987 x h1) (@lem1761050 x h1)). Qed.
Lemma lem1761056 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761057 (x : real) (h1 : (term127 x) = True) : (term112 x) = (term174 x).
Proof. exact (MK_COMB (@lem1761056 x) (@lem1761053 x h1)). Qed.
Lemma lem1761060 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1761061 (x : real) (h1 : (term127 x) = True) : (term113 x) = (term178 x).
Proof. exact (MK_COMB (@lem1761060 x) (@lem1761057 x h1)). Qed.
Lemma lem1761064 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1761065 (x : real) (h1 : (term127 x) = True) : (term154 x) = (term179 x).
Proof. exact (MK_COMB (@lem1761064) (@lem1761061 x h1)). Qed.
Lemma lem1761068 (x : real) (h1 : (term127 x) = True) : (term126 x) = (term180 x).
Proof. exact (MK_COMB (@lem1760940 x h1) (@lem1761065 x h1)). Qed.
Lemma lem1761071 (x : real) : term181 x.
Proof. exact (fun h0 : (term127 x) = True => @lem1761068 x h0). Qed.
Lemma lem1761072 (x : real) : term182 x.
Proof. exact (conj (@lem1760811 x) (@lem1761071 x)). Qed.
Lemma lem1761074 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1761075 (x : real) : term183 x.
Proof. exact (@lem1761074 (term126 x) (term180 x) (term127 x) (term156 x)). Qed.
Lemma lem1761090 (x : real) : (term126 x) = (term184 x).
Proof. exact (@lem1761075 x (@lem1761072 x)). Qed.
Lemma lem1761104 (h1 : term166 = False) : term166 = False.
Proof. exact (h1). Qed.
Lemma lem1761105 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761106 (h1 : term166 = False) : term167 = (@COND real False).
Proof. exact (MK_COMB (@lem1761105) (@lem1761104 h1)). Qed.
Lemma lem1761107 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761108 (h1 : term166 = False) : term168 = term102.
Proof. exact (MK_COMB (@lem1761106 h1) (@lem1761107)). Qed.
Lemma lem1761109 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761110 (h1 : term166 = False) : term169 = term103.
Proof. exact (MK_COMB (@lem1761108 h1) (@lem1761109)). Qed.
Lemma lem1761112 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761113 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761112 real t1 t2). Qed.
Lemma lem1761114 : term103 = term14.
Proof. exact (@lem1761113 term19 term14). Qed.
Lemma lem1761115 (h1 : term166 = False) : term169 = term14.
Proof. exact (TRANS (@lem1761110 h1) (@lem1761114)). Qed.
Lemma lem1761116 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761117 (h1 : term166 = False) : term170 = term104.
Proof. exact (MK_COMB (@lem1761116) (@lem1761115 h1)). Qed.
Lemma lem1761118 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761119 (h1 : term166 = False) : (term169 = term19) = (term14 = term19).
Proof. exact (MK_COMB (@lem1761117 h1) (@lem1761118)). Qed.
Lemma lem1761122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761123 (h1 : term166 = False) : term171 = term185.
Proof. exact (MK_COMB (@lem1761122) (@lem1761119 h1)). Qed.
Lemma lem1761124 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1761125 (h1 : term166 = False) : term172 = term186.
Proof. exact (MK_COMB (@lem1761124) (@lem1761123 h1)). Qed.
Lemma lem1761128 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1761129 (h1 : term166 = False) : term173 = term187.
Proof. exact (MK_COMB (@lem1761128) (@lem1761125 h1)). Qed.
Lemma lem1761132 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761133 (x : real) (h1 : term166 = False) : (term174 x) = (term188 x).
Proof. exact (MK_COMB (@lem1761132 x) (@lem1761129 h1)). Qed.
Lemma lem1761136 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1761137 (x : real) (h1 : term166 = False) : (term175 x) = (term189 x).
Proof. exact (MK_COMB (@lem1761136 x) (@lem1761133 x h1)). Qed.
Lemma lem1761140 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1761141 (x : real) (h1 : term166 = False) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1761140) (@lem1761137 x h1)). Qed.
Lemma lem1761144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761145 (x : real) (h1 : term166 = False) : (term177 x) = (term191 x).
Proof. exact (MK_COMB (@lem1761144) (@lem1761141 x h1)). Qed.
Lemma lem1761157 (h1 : term166 = False) : term166 = False.
Proof. exact (h1). Qed.
Lemma lem1761158 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761159 (h1 : term166 = False) : term167 = (@COND real False).
Proof. exact (MK_COMB (@lem1761158) (@lem1761157 h1)). Qed.
Lemma lem1761160 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761161 (h1 : term166 = False) : term168 = term102.
Proof. exact (MK_COMB (@lem1761159 h1) (@lem1761160)). Qed.
Lemma lem1761162 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761163 (h1 : term166 = False) : term169 = term103.
Proof. exact (MK_COMB (@lem1761161 h1) (@lem1761162)). Qed.
Lemma lem1761165 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761166 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761165 real t1 t2). Qed.
Lemma lem1761167 : term103 = term14.
Proof. exact (@lem1761166 term19 term14). Qed.
Lemma lem1761168 (h1 : term166 = False) : term169 = term14.
Proof. exact (TRANS (@lem1761163 h1) (@lem1761167)). Qed.
Lemma lem1761169 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761170 (h1 : term166 = False) : term170 = term104.
Proof. exact (MK_COMB (@lem1761169) (@lem1761168 h1)). Qed.
Lemma lem1761171 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761172 (h1 : term166 = False) : (term169 = term19) = (term14 = term19).
Proof. exact (MK_COMB (@lem1761170 h1) (@lem1761171)). Qed.
Lemma lem1761175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761176 (h1 : term166 = False) : term171 = term185.
Proof. exact (MK_COMB (@lem1761175) (@lem1761172 h1)). Qed.
Lemma lem1761177 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1761178 (h1 : term166 = False) : term172 = term186.
Proof. exact (MK_COMB (@lem1761177) (@lem1761176 h1)). Qed.
Lemma lem1761181 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1761182 (h1 : term166 = False) : term173 = term187.
Proof. exact (MK_COMB (@lem1761181) (@lem1761178 h1)). Qed.
Lemma lem1761185 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761186 (x : real) (h1 : term166 = False) : (term174 x) = (term188 x).
Proof. exact (MK_COMB (@lem1761185 x) (@lem1761182 h1)). Qed.
Lemma lem1761189 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1761190 (x : real) (h1 : term166 = False) : (term178 x) = (term192 x).
Proof. exact (MK_COMB (@lem1761189 x) (@lem1761186 x h1)). Qed.
Lemma lem1761193 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1761194 (x : real) (h1 : term166 = False) : (term179 x) = (term193 x).
Proof. exact (MK_COMB (@lem1761193) (@lem1761190 x h1)). Qed.
Lemma lem1761197 (x : real) (h1 : term166 = False) : (term180 x) = (term194 x).
Proof. exact (MK_COMB (@lem1761145 x h1) (@lem1761194 x h1)). Qed.
Lemma lem1761200 (x : real) : (term195 x) = (term195 x).
Proof. exact (eq_refl (term195 x)). Qed.
Lemma lem1761201 (x : real) (h1 : term166 = False) : (term196 x) = (term197 x).
Proof. exact (MK_COMB (@lem1761200 x) (@lem1761197 x h1)). Qed.
Lemma lem1761204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761205 (x : real) (h1 : term166 = False) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1761204) (@lem1761201 x h1)). Qed.
Lemma lem1761254 (x : real) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem1761255 (x : real) (h1 : term166 = False) : (term184 x) = (term201 x).
Proof. exact (MK_COMB (@lem1761205 x h1) (@lem1761254 x)). Qed.
Lemma lem1761258 (x : real) : term202 x.
Proof. exact (fun h0 : term166 = False => @lem1761255 x h0). Qed.
Lemma lem1761270 (h1 : term166 = True) : term166 = True.
Proof. exact (h1). Qed.
Lemma lem1761271 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761272 (h1 : term166 = True) : term167 = (@COND real True).
Proof. exact (MK_COMB (@lem1761271) (@lem1761270 h1)). Qed.
Lemma lem1761273 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761274 (h1 : term166 = True) : term168 = term115.
Proof. exact (MK_COMB (@lem1761272 h1) (@lem1761273)). Qed.
Lemma lem1761275 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761276 (h1 : term166 = True) : term169 = term116.
Proof. exact (MK_COMB (@lem1761274 h1) (@lem1761275)). Qed.
Lemma lem1761278 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1761279 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1761278 real t2 t1). Qed.
Lemma lem1761280 : term116 = term19.
Proof. exact (@lem1761279 term14 term19). Qed.
Lemma lem1761281 (h1 : term166 = True) : term169 = term19.
Proof. exact (TRANS (@lem1761276 h1) (@lem1761280)). Qed.
Lemma lem1761282 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761283 (h1 : term166 = True) : term170 = term117.
Proof. exact (MK_COMB (@lem1761282) (@lem1761281 h1)). Qed.
Lemma lem1761284 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761285 (h1 : term166 = True) : (term169 = term19) = (term19 = term19).
Proof. exact (MK_COMB (@lem1761283 h1) (@lem1761284)). Qed.
Lemma lem1761287 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761288 (x : real) : (x = x) = True.
Proof. exact (@lem1761287 real x). Qed.
Lemma lem1761289 : (term19 = term19) = True.
Proof. exact (@lem1761288 term19). Qed.
Lemma lem1761290 (h1 : term166 = True) : (term169 = term19) = True.
Proof. exact (TRANS (@lem1761285 h1) (@lem1761289)). Qed.
Lemma lem1761291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761292 (h1 : term166 = True) : term171 = (~ True).
Proof. exact (MK_COMB (@lem1761291) (@lem1761290 h1)). Qed.
Lemma lem1761294 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761295 (h1 : term166 = True) : term171 = False.
Proof. exact (TRANS (@lem1761292 h1) (@lem1761294)). Qed.
Lemma lem1761296 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1761297 (h1 : term166 = True) : term172 = term203.
Proof. exact (MK_COMB (@lem1761296) (@lem1761295 h1)). Qed.
Lemma lem1761299 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761300 : term203 = False.
Proof. exact (@lem1761299 term163). Qed.
Lemma lem1761301 (h1 : term166 = True) : term172 = False.
Proof. exact (TRANS (@lem1761297 h1) (@lem1761300)). Qed.
Lemma lem1761302 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1761303 (h1 : term166 = True) : term173 = term204.
Proof. exact (MK_COMB (@lem1761302) (@lem1761301 h1)). Qed.
Lemma lem1761305 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761306 : term204 = term161.
Proof. exact (@lem1761305 term161). Qed.
Lemma lem1761309 (h1 : term166 = True) : term173 = term161.
Proof. exact (TRANS (@lem1761303 h1) (@lem1761306)). Qed.
Lemma lem1761310 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761311 (x : real) (h1 : term166 = True) : (term174 x) = (term205 x).
Proof. exact (MK_COMB (@lem1761310 x) (@lem1761309 h1)). Qed.
Lemma lem1761314 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1761315 (x : real) (h1 : term166 = True) : (term175 x) = (term206 x).
Proof. exact (MK_COMB (@lem1761314 x) (@lem1761311 x h1)). Qed.
Lemma lem1761318 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1761319 (x : real) (h1 : term166 = True) : (term176 x) = (term207 x).
Proof. exact (MK_COMB (@lem1761318) (@lem1761315 x h1)). Qed.
Lemma lem1761322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761323 (x : real) (h1 : term166 = True) : (term177 x) = (term208 x).
Proof. exact (MK_COMB (@lem1761322) (@lem1761319 x h1)). Qed.
Lemma lem1761335 (h1 : term166 = True) : term166 = True.
Proof. exact (h1). Qed.
Lemma lem1761336 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761337 (h1 : term166 = True) : term167 = (@COND real True).
Proof. exact (MK_COMB (@lem1761336) (@lem1761335 h1)). Qed.
Lemma lem1761338 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761339 (h1 : term166 = True) : term168 = term115.
Proof. exact (MK_COMB (@lem1761337 h1) (@lem1761338)). Qed.
Lemma lem1761340 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761341 (h1 : term166 = True) : term169 = term116.
Proof. exact (MK_COMB (@lem1761339 h1) (@lem1761340)). Qed.
Lemma lem1761343 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1761344 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1761343 real t2 t1). Qed.
Lemma lem1761345 : term116 = term19.
Proof. exact (@lem1761344 term14 term19). Qed.
Lemma lem1761346 (h1 : term166 = True) : term169 = term19.
Proof. exact (TRANS (@lem1761341 h1) (@lem1761345)). Qed.
Lemma lem1761347 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761348 (h1 : term166 = True) : term170 = term117.
Proof. exact (MK_COMB (@lem1761347) (@lem1761346 h1)). Qed.
Lemma lem1761349 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761350 (h1 : term166 = True) : (term169 = term19) = (term19 = term19).
Proof. exact (MK_COMB (@lem1761348 h1) (@lem1761349)). Qed.
Lemma lem1761352 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761353 (x : real) : (x = x) = True.
Proof. exact (@lem1761352 real x). Qed.
Lemma lem1761354 : (term19 = term19) = True.
Proof. exact (@lem1761353 term19). Qed.
Lemma lem1761355 (h1 : term166 = True) : (term169 = term19) = True.
Proof. exact (TRANS (@lem1761350 h1) (@lem1761354)). Qed.
Lemma lem1761356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761357 (h1 : term166 = True) : term171 = (~ True).
Proof. exact (MK_COMB (@lem1761356) (@lem1761355 h1)). Qed.
Lemma lem1761359 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761360 (h1 : term166 = True) : term171 = False.
Proof. exact (TRANS (@lem1761357 h1) (@lem1761359)). Qed.
Lemma lem1761361 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem1761362 (h1 : term166 = True) : term172 = term203.
Proof. exact (MK_COMB (@lem1761361) (@lem1761360 h1)). Qed.
Lemma lem1761364 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761365 : term203 = False.
Proof. exact (@lem1761364 term163). Qed.
Lemma lem1761366 (h1 : term166 = True) : term172 = False.
Proof. exact (TRANS (@lem1761362 h1) (@lem1761365)). Qed.
Lemma lem1761367 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1761368 (h1 : term166 = True) : term173 = term204.
Proof. exact (MK_COMB (@lem1761367) (@lem1761366 h1)). Qed.
Lemma lem1761370 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761371 : term204 = term161.
Proof. exact (@lem1761370 term161). Qed.
Lemma lem1761374 (h1 : term166 = True) : term173 = term161.
Proof. exact (TRANS (@lem1761368 h1) (@lem1761371)). Qed.
Lemma lem1761375 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761376 (x : real) (h1 : term166 = True) : (term174 x) = (term205 x).
Proof. exact (MK_COMB (@lem1761375 x) (@lem1761374 h1)). Qed.
Lemma lem1761379 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1761380 (x : real) (h1 : term166 = True) : (term178 x) = (term209 x).
Proof. exact (MK_COMB (@lem1761379 x) (@lem1761376 x h1)). Qed.
Lemma lem1761383 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1761384 (x : real) (h1 : term166 = True) : (term179 x) = (term210 x).
Proof. exact (MK_COMB (@lem1761383) (@lem1761380 x h1)). Qed.
Lemma lem1761387 (x : real) (h1 : term166 = True) : (term180 x) = (term211 x).
Proof. exact (MK_COMB (@lem1761323 x h1) (@lem1761384 x h1)). Qed.
Lemma lem1761390 (x : real) : (term195 x) = (term195 x).
Proof. exact (eq_refl (term195 x)). Qed.
Lemma lem1761391 (x : real) (h1 : term166 = True) : (term196 x) = (term212 x).
Proof. exact (MK_COMB (@lem1761390 x) (@lem1761387 x h1)). Qed.
Lemma lem1761394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761395 (x : real) (h1 : term166 = True) : (term198 x) = (term213 x).
Proof. exact (MK_COMB (@lem1761394) (@lem1761391 x h1)). Qed.
Lemma lem1761444 (x : real) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem1761445 (x : real) (h1 : term166 = True) : (term184 x) = (term214 x).
Proof. exact (MK_COMB (@lem1761395 x h1) (@lem1761444 x)). Qed.
Lemma lem1761448 (x : real) : term215 x.
Proof. exact (fun h0 : term166 = True => @lem1761445 x h0). Qed.
Lemma lem1761449 (x : real) : term216 x.
Proof. exact (conj (@lem1761258 x) (@lem1761448 x)). Qed.
Lemma lem1761451 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1761452 (x : real) : term217 x.
Proof. exact (@lem1761451 (term184 x) (term214 x) term166 (term201 x)). Qed.
Lemma lem1761467 (x : real) : (term184 x) = (term218 x).
Proof. exact (@lem1761452 x (@lem1761449 x)). Qed.
Lemma lem1761513 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761515 (h1 : term130 = False) : term131 = (and False).
Proof. exact (MK_COMB (@lem1761514) (@lem1761513 h1)). Qed.
Lemma lem1761518 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1761519 (h1 : term130 = False) : term133 = term219.
Proof. exact (MK_COMB (@lem1761515 h1) (@lem1761518)). Qed.
Lemma lem1761521 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1761522 : term219 = False.
Proof. exact (@lem1761521 term132). Qed.
Lemma lem1761523 (h1 : term130 = False) : term133 = False.
Proof. exact (TRANS (@lem1761519 h1) (@lem1761522)). Qed.
Lemma lem1761524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761525 (h1 : term130 = False) : term134 = (or False).
Proof. exact (MK_COMB (@lem1761524) (@lem1761523 h1)). Qed.
Lemma lem1761527 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761528 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761529 (h1 : term130 = False) : term135 = (~ False).
Proof. exact (MK_COMB (@lem1761528) (@lem1761527 h1)). Qed.
Lemma lem1761531 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1761532 (h1 : term130 = False) : term135 = True.
Proof. exact (TRANS (@lem1761529 h1) (@lem1761531)). Qed.
Lemma lem1761533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761534 (h1 : term130 = False) : term136 = (and True).
Proof. exact (MK_COMB (@lem1761533) (@lem1761532 h1)). Qed.
Lemma lem1761536 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761537 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761538 (h1 : term130 = False) : term137 = (@COND real False).
Proof. exact (MK_COMB (@lem1761537) (@lem1761536 h1)). Qed.
Lemma lem1761539 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761540 (h1 : term130 = False) : term138 = term102.
Proof. exact (MK_COMB (@lem1761538 h1) (@lem1761539)). Qed.
Lemma lem1761541 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761542 (h1 : term130 = False) : term139 = term103.
Proof. exact (MK_COMB (@lem1761540 h1) (@lem1761541)). Qed.
Lemma lem1761544 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761545 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761544 real t1 t2). Qed.
Lemma lem1761546 : term103 = term14.
Proof. exact (@lem1761545 term19 term14). Qed.
Lemma lem1761547 (h1 : term130 = False) : term139 = term14.
Proof. exact (TRANS (@lem1761542 h1) (@lem1761546)). Qed.
Lemma lem1761548 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761549 (h1 : term130 = False) : term140 = term104.
Proof. exact (MK_COMB (@lem1761548) (@lem1761547 h1)). Qed.
Lemma lem1761550 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761551 (h1 : term130 = False) : (term139 = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem1761549 h1) (@lem1761550)). Qed.
Lemma lem1761553 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761554 (x : real) : (x = x) = True.
Proof. exact (@lem1761553 real x). Qed.
Lemma lem1761555 : (term14 = term14) = True.
Proof. exact (@lem1761554 term14). Qed.
Lemma lem1761556 (h1 : term130 = False) : (term139 = term14) = True.
Proof. exact (TRANS (@lem1761551 h1) (@lem1761555)). Qed.
Lemma lem1761557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761558 (h1 : term130 = False) : term141 = (~ True).
Proof. exact (MK_COMB (@lem1761557) (@lem1761556 h1)). Qed.
Lemma lem1761560 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761561 (h1 : term130 = False) : term141 = False.
Proof. exact (TRANS (@lem1761558 h1) (@lem1761560)). Qed.
Lemma lem1761562 (h1 : term130 = False) : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem1761534 h1) (@lem1761561 h1)). Qed.
Lemma lem1761564 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1761565 : (True /\ False) = False.
Proof. exact (@lem1761564 False). Qed.
Lemma lem1761566 (h1 : term130 = False) : term142 = False.
Proof. exact (TRANS (@lem1761562 h1) (@lem1761565)). Qed.
Lemma lem1761567 (h1 : term130 = False) : term143 = (False \/ False).
Proof. exact (MK_COMB (@lem1761525 h1) (@lem1761566 h1)). Qed.
Lemma lem1761569 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1761570 : (False \/ False) = False.
Proof. exact (@lem1761569 False). Qed.
Lemma lem1761571 (h1 : term130 = False) : term143 = False.
Proof. exact (TRANS (@lem1761567 h1) (@lem1761570)). Qed.
Lemma lem1761572 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761573 (x : real) (h1 : term130 = False) : (term145 x) = (term220 x).
Proof. exact (MK_COMB (@lem1761572 x) (@lem1761571 h1)). Qed.
Lemma lem1761575 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761576 (x : real) : (term220 x) = False.
Proof. exact (@lem1761575 (term221 x)). Qed.
Lemma lem1761577 (x : real) (h1 : term130 = False) : (term145 x) = False.
Proof. exact (TRANS (@lem1761573 x h1) (@lem1761576 x)). Qed.
Lemma lem1761578 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1761579 (x : real) (h1 : term130 = False) : (term146 x) = (term222 x).
Proof. exact (MK_COMB (@lem1761578 x) (@lem1761577 x h1)). Qed.
Lemma lem1761581 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761582 (x : real) : (term222 x) = (term120 x).
Proof. exact (@lem1761581 (term120 x)). Qed.
Lemma lem1761585 (x : real) (h1 : term130 = False) : (term146 x) = (term120 x).
Proof. exact (TRANS (@lem1761579 x h1) (@lem1761582 x)). Qed.
Lemma lem1761586 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1761587 (x : real) (h1 : term130 = False) : (term149 x) = (term223 x).
Proof. exact (MK_COMB (@lem1761586) (@lem1761585 x h1)). Qed.
Lemma lem1761590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761591 (x : real) (h1 : term130 = False) : (term151 x) = (term224 x).
Proof. exact (MK_COMB (@lem1761590) (@lem1761587 x h1)). Qed.
Lemma lem1761599 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761601 (h1 : term130 = False) : term131 = (and False).
Proof. exact (MK_COMB (@lem1761600) (@lem1761599 h1)). Qed.
Lemma lem1761604 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1761605 (h1 : term130 = False) : term133 = term219.
Proof. exact (MK_COMB (@lem1761601 h1) (@lem1761604)). Qed.
Lemma lem1761607 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1761608 : term219 = False.
Proof. exact (@lem1761607 term132). Qed.
Lemma lem1761609 (h1 : term130 = False) : term133 = False.
Proof. exact (TRANS (@lem1761605 h1) (@lem1761608)). Qed.
Lemma lem1761610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761611 (h1 : term130 = False) : term134 = (or False).
Proof. exact (MK_COMB (@lem1761610) (@lem1761609 h1)). Qed.
Lemma lem1761613 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761615 (h1 : term130 = False) : term135 = (~ False).
Proof. exact (MK_COMB (@lem1761614) (@lem1761613 h1)). Qed.
Lemma lem1761617 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1761618 (h1 : term130 = False) : term135 = True.
Proof. exact (TRANS (@lem1761615 h1) (@lem1761617)). Qed.
Lemma lem1761619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761620 (h1 : term130 = False) : term136 = (and True).
Proof. exact (MK_COMB (@lem1761619) (@lem1761618 h1)). Qed.
Lemma lem1761622 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761623 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761624 (h1 : term130 = False) : term137 = (@COND real False).
Proof. exact (MK_COMB (@lem1761623) (@lem1761622 h1)). Qed.
Lemma lem1761625 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761626 (h1 : term130 = False) : term138 = term102.
Proof. exact (MK_COMB (@lem1761624 h1) (@lem1761625)). Qed.
Lemma lem1761627 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761628 (h1 : term130 = False) : term139 = term103.
Proof. exact (MK_COMB (@lem1761626 h1) (@lem1761627)). Qed.
Lemma lem1761630 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761631 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761630 real t1 t2). Qed.
Lemma lem1761632 : term103 = term14.
Proof. exact (@lem1761631 term19 term14). Qed.
Lemma lem1761633 (h1 : term130 = False) : term139 = term14.
Proof. exact (TRANS (@lem1761628 h1) (@lem1761632)). Qed.
Lemma lem1761634 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761635 (h1 : term130 = False) : term140 = term104.
Proof. exact (MK_COMB (@lem1761634) (@lem1761633 h1)). Qed.
Lemma lem1761636 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761637 (h1 : term130 = False) : (term139 = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem1761635 h1) (@lem1761636)). Qed.
Lemma lem1761639 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761640 (x : real) : (x = x) = True.
Proof. exact (@lem1761639 real x). Qed.
Lemma lem1761641 : (term14 = term14) = True.
Proof. exact (@lem1761640 term14). Qed.
Lemma lem1761642 (h1 : term130 = False) : (term139 = term14) = True.
Proof. exact (TRANS (@lem1761637 h1) (@lem1761641)). Qed.
Lemma lem1761643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761644 (h1 : term130 = False) : term141 = (~ True).
Proof. exact (MK_COMB (@lem1761643) (@lem1761642 h1)). Qed.
Lemma lem1761646 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761647 (h1 : term130 = False) : term141 = False.
Proof. exact (TRANS (@lem1761644 h1) (@lem1761646)). Qed.
Lemma lem1761648 (h1 : term130 = False) : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem1761620 h1) (@lem1761647 h1)). Qed.
Lemma lem1761650 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1761651 : (True /\ False) = False.
Proof. exact (@lem1761650 False). Qed.
Lemma lem1761652 (h1 : term130 = False) : term142 = False.
Proof. exact (TRANS (@lem1761648 h1) (@lem1761651)). Qed.
Lemma lem1761653 (h1 : term130 = False) : term143 = (False \/ False).
Proof. exact (MK_COMB (@lem1761611 h1) (@lem1761652 h1)). Qed.
Lemma lem1761655 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1761656 : (False \/ False) = False.
Proof. exact (@lem1761655 False). Qed.
Lemma lem1761657 (h1 : term130 = False) : term143 = False.
Proof. exact (TRANS (@lem1761653 h1) (@lem1761656)). Qed.
Lemma lem1761658 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761659 (x : real) (h1 : term130 = False) : (term145 x) = (term220 x).
Proof. exact (MK_COMB (@lem1761658 x) (@lem1761657 h1)). Qed.
Lemma lem1761661 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761662 (x : real) : (term220 x) = False.
Proof. exact (@lem1761661 (term221 x)). Qed.
Lemma lem1761663 (x : real) (h1 : term130 = False) : (term145 x) = False.
Proof. exact (TRANS (@lem1761659 x h1) (@lem1761662 x)). Qed.
Lemma lem1761664 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1761665 (x : real) (h1 : term130 = False) : (term152 x) = (term225 x).
Proof. exact (MK_COMB (@lem1761664 x) (@lem1761663 x h1)). Qed.
Lemma lem1761667 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761668 (x : real) : (term225 x) = (term109 x).
Proof. exact (@lem1761667 (term109 x)). Qed.
Lemma lem1761671 (x : real) (h1 : term130 = False) : (term152 x) = (term109 x).
Proof. exact (TRANS (@lem1761665 x h1) (@lem1761668 x)). Qed.
Lemma lem1761672 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1761673 (x : real) (h1 : term130 = False) : (term155 x) = (term226 x).
Proof. exact (MK_COMB (@lem1761672) (@lem1761671 x h1)). Qed.
Lemma lem1761676 (x : real) (h1 : term130 = False) : (term156 x) = (term227 x).
Proof. exact (MK_COMB (@lem1761591 x h1) (@lem1761673 x h1)). Qed.
Lemma lem1761679 (x : real) : (term228 x) = (term228 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem1761680 (x : real) (h1 : term130 = False) : (term200 x) = (term229 x).
Proof. exact (MK_COMB (@lem1761679 x) (@lem1761676 x h1)). Qed.
Lemma lem1761683 (x : real) : (term213 x) = (term213 x).
Proof. exact (eq_refl (term213 x)). Qed.
Lemma lem1761684 (x : real) (h1 : term130 = False) : (term214 x) = (term230 x).
Proof. exact (MK_COMB (@lem1761683 x) (@lem1761680 x h1)). Qed.
Lemma lem1761687 : term231 = term231.
Proof. exact (eq_refl term231). Qed.
Lemma lem1761688 (x : real) (h1 : term130 = False) : (term232 x) = (term233 x).
Proof. exact (MK_COMB (@lem1761687) (@lem1761684 x h1)). Qed.
Lemma lem1761691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761692 (x : real) (h1 : term130 = False) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem1761691) (@lem1761688 x h1)). Qed.
Lemma lem1761748 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761750 (h1 : term130 = False) : term131 = (and False).
Proof. exact (MK_COMB (@lem1761749) (@lem1761748 h1)). Qed.
Lemma lem1761753 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1761754 (h1 : term130 = False) : term133 = term219.
Proof. exact (MK_COMB (@lem1761750 h1) (@lem1761753)). Qed.
Lemma lem1761756 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1761757 : term219 = False.
Proof. exact (@lem1761756 term132). Qed.
Lemma lem1761758 (h1 : term130 = False) : term133 = False.
Proof. exact (TRANS (@lem1761754 h1) (@lem1761757)). Qed.
Lemma lem1761759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761760 (h1 : term130 = False) : term134 = (or False).
Proof. exact (MK_COMB (@lem1761759) (@lem1761758 h1)). Qed.
Lemma lem1761762 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761763 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761764 (h1 : term130 = False) : term135 = (~ False).
Proof. exact (MK_COMB (@lem1761763) (@lem1761762 h1)). Qed.
Lemma lem1761766 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1761767 (h1 : term130 = False) : term135 = True.
Proof. exact (TRANS (@lem1761764 h1) (@lem1761766)). Qed.
Lemma lem1761768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761769 (h1 : term130 = False) : term136 = (and True).
Proof. exact (MK_COMB (@lem1761768) (@lem1761767 h1)). Qed.
Lemma lem1761771 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761772 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761773 (h1 : term130 = False) : term137 = (@COND real False).
Proof. exact (MK_COMB (@lem1761772) (@lem1761771 h1)). Qed.
Lemma lem1761774 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761775 (h1 : term130 = False) : term138 = term102.
Proof. exact (MK_COMB (@lem1761773 h1) (@lem1761774)). Qed.
Lemma lem1761776 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761777 (h1 : term130 = False) : term139 = term103.
Proof. exact (MK_COMB (@lem1761775 h1) (@lem1761776)). Qed.
Lemma lem1761779 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761780 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761779 real t1 t2). Qed.
Lemma lem1761781 : term103 = term14.
Proof. exact (@lem1761780 term19 term14). Qed.
Lemma lem1761782 (h1 : term130 = False) : term139 = term14.
Proof. exact (TRANS (@lem1761777 h1) (@lem1761781)). Qed.
Lemma lem1761783 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761784 (h1 : term130 = False) : term140 = term104.
Proof. exact (MK_COMB (@lem1761783) (@lem1761782 h1)). Qed.
Lemma lem1761785 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761786 (h1 : term130 = False) : (term139 = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem1761784 h1) (@lem1761785)). Qed.
Lemma lem1761788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761789 (x : real) : (x = x) = True.
Proof. exact (@lem1761788 real x). Qed.
Lemma lem1761790 : (term14 = term14) = True.
Proof. exact (@lem1761789 term14). Qed.
Lemma lem1761791 (h1 : term130 = False) : (term139 = term14) = True.
Proof. exact (TRANS (@lem1761786 h1) (@lem1761790)). Qed.
Lemma lem1761792 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761793 (h1 : term130 = False) : term141 = (~ True).
Proof. exact (MK_COMB (@lem1761792) (@lem1761791 h1)). Qed.
Lemma lem1761795 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761796 (h1 : term130 = False) : term141 = False.
Proof. exact (TRANS (@lem1761793 h1) (@lem1761795)). Qed.
Lemma lem1761797 (h1 : term130 = False) : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem1761769 h1) (@lem1761796 h1)). Qed.
Lemma lem1761799 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1761800 : (True /\ False) = False.
Proof. exact (@lem1761799 False). Qed.
Lemma lem1761801 (h1 : term130 = False) : term142 = False.
Proof. exact (TRANS (@lem1761797 h1) (@lem1761800)). Qed.
Lemma lem1761802 (h1 : term130 = False) : term143 = (False \/ False).
Proof. exact (MK_COMB (@lem1761760 h1) (@lem1761801 h1)). Qed.
Lemma lem1761804 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1761805 : (False \/ False) = False.
Proof. exact (@lem1761804 False). Qed.
Lemma lem1761806 (h1 : term130 = False) : term143 = False.
Proof. exact (TRANS (@lem1761802 h1) (@lem1761805)). Qed.
Lemma lem1761807 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761808 (x : real) (h1 : term130 = False) : (term145 x) = (term220 x).
Proof. exact (MK_COMB (@lem1761807 x) (@lem1761806 h1)). Qed.
Lemma lem1761810 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761811 (x : real) : (term220 x) = False.
Proof. exact (@lem1761810 (term221 x)). Qed.
Lemma lem1761812 (x : real) (h1 : term130 = False) : (term145 x) = False.
Proof. exact (TRANS (@lem1761808 x h1) (@lem1761811 x)). Qed.
Lemma lem1761813 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1761814 (x : real) (h1 : term130 = False) : (term146 x) = (term222 x).
Proof. exact (MK_COMB (@lem1761813 x) (@lem1761812 x h1)). Qed.
Lemma lem1761816 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761817 (x : real) : (term222 x) = (term120 x).
Proof. exact (@lem1761816 (term120 x)). Qed.
Lemma lem1761820 (x : real) (h1 : term130 = False) : (term146 x) = (term120 x).
Proof. exact (TRANS (@lem1761814 x h1) (@lem1761817 x)). Qed.
Lemma lem1761821 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1761822 (x : real) (h1 : term130 = False) : (term149 x) = (term223 x).
Proof. exact (MK_COMB (@lem1761821) (@lem1761820 x h1)). Qed.
Lemma lem1761825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761826 (x : real) (h1 : term130 = False) : (term151 x) = (term224 x).
Proof. exact (MK_COMB (@lem1761825) (@lem1761822 x h1)). Qed.
Lemma lem1761834 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761836 (h1 : term130 = False) : term131 = (and False).
Proof. exact (MK_COMB (@lem1761835) (@lem1761834 h1)). Qed.
Lemma lem1761839 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1761840 (h1 : term130 = False) : term133 = term219.
Proof. exact (MK_COMB (@lem1761836 h1) (@lem1761839)). Qed.
Lemma lem1761842 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1761843 : term219 = False.
Proof. exact (@lem1761842 term132). Qed.
Lemma lem1761844 (h1 : term130 = False) : term133 = False.
Proof. exact (TRANS (@lem1761840 h1) (@lem1761843)). Qed.
Lemma lem1761845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761846 (h1 : term130 = False) : term134 = (or False).
Proof. exact (MK_COMB (@lem1761845) (@lem1761844 h1)). Qed.
Lemma lem1761848 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761850 (h1 : term130 = False) : term135 = (~ False).
Proof. exact (MK_COMB (@lem1761849) (@lem1761848 h1)). Qed.
Lemma lem1761852 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1761853 (h1 : term130 = False) : term135 = True.
Proof. exact (TRANS (@lem1761850 h1) (@lem1761852)). Qed.
Lemma lem1761854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761855 (h1 : term130 = False) : term136 = (and True).
Proof. exact (MK_COMB (@lem1761854) (@lem1761853 h1)). Qed.
Lemma lem1761857 (h1 : term130 = False) : term130 = False.
Proof. exact (h1). Qed.
Lemma lem1761858 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761859 (h1 : term130 = False) : term137 = (@COND real False).
Proof. exact (MK_COMB (@lem1761858) (@lem1761857 h1)). Qed.
Lemma lem1761860 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1761861 (h1 : term130 = False) : term138 = term102.
Proof. exact (MK_COMB (@lem1761859 h1) (@lem1761860)). Qed.
Lemma lem1761862 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761863 (h1 : term130 = False) : term139 = term103.
Proof. exact (MK_COMB (@lem1761861 h1) (@lem1761862)). Qed.
Lemma lem1761865 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1761866 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1761865 real t1 t2). Qed.
Lemma lem1761867 : term103 = term14.
Proof. exact (@lem1761866 term19 term14). Qed.
Lemma lem1761868 (h1 : term130 = False) : term139 = term14.
Proof. exact (TRANS (@lem1761863 h1) (@lem1761867)). Qed.
Lemma lem1761869 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1761870 (h1 : term130 = False) : term140 = term104.
Proof. exact (MK_COMB (@lem1761869) (@lem1761868 h1)). Qed.
Lemma lem1761871 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1761872 (h1 : term130 = False) : (term139 = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem1761870 h1) (@lem1761871)). Qed.
Lemma lem1761874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1761875 (x : real) : (x = x) = True.
Proof. exact (@lem1761874 real x). Qed.
Lemma lem1761876 : (term14 = term14) = True.
Proof. exact (@lem1761875 term14). Qed.
Lemma lem1761877 (h1 : term130 = False) : (term139 = term14) = True.
Proof. exact (TRANS (@lem1761872 h1) (@lem1761876)). Qed.
Lemma lem1761878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761879 (h1 : term130 = False) : term141 = (~ True).
Proof. exact (MK_COMB (@lem1761878) (@lem1761877 h1)). Qed.
Lemma lem1761881 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761882 (h1 : term130 = False) : term141 = False.
Proof. exact (TRANS (@lem1761879 h1) (@lem1761881)). Qed.
Lemma lem1761883 (h1 : term130 = False) : term142 = (True /\ False).
Proof. exact (MK_COMB (@lem1761855 h1) (@lem1761882 h1)). Qed.
Lemma lem1761885 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1761886 : (True /\ False) = False.
Proof. exact (@lem1761885 False). Qed.
Lemma lem1761887 (h1 : term130 = False) : term142 = False.
Proof. exact (TRANS (@lem1761883 h1) (@lem1761886)). Qed.
Lemma lem1761888 (h1 : term130 = False) : term143 = (False \/ False).
Proof. exact (MK_COMB (@lem1761846 h1) (@lem1761887 h1)). Qed.
Lemma lem1761890 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1761891 : (False \/ False) = False.
Proof. exact (@lem1761890 False). Qed.
Lemma lem1761892 (h1 : term130 = False) : term143 = False.
Proof. exact (TRANS (@lem1761888 h1) (@lem1761891)). Qed.
Lemma lem1761893 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1761894 (x : real) (h1 : term130 = False) : (term145 x) = (term220 x).
Proof. exact (MK_COMB (@lem1761893 x) (@lem1761892 h1)). Qed.
Lemma lem1761896 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1761897 (x : real) : (term220 x) = False.
Proof. exact (@lem1761896 (term221 x)). Qed.
Lemma lem1761898 (x : real) (h1 : term130 = False) : (term145 x) = False.
Proof. exact (TRANS (@lem1761894 x h1) (@lem1761897 x)). Qed.
Lemma lem1761899 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1761900 (x : real) (h1 : term130 = False) : (term152 x) = (term225 x).
Proof. exact (MK_COMB (@lem1761899 x) (@lem1761898 x h1)). Qed.
Lemma lem1761902 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1761903 (x : real) : (term225 x) = (term109 x).
Proof. exact (@lem1761902 (term109 x)). Qed.
Lemma lem1761906 (x : real) (h1 : term130 = False) : (term152 x) = (term109 x).
Proof. exact (TRANS (@lem1761900 x h1) (@lem1761903 x)). Qed.
Lemma lem1761907 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1761908 (x : real) (h1 : term130 = False) : (term155 x) = (term226 x).
Proof. exact (MK_COMB (@lem1761907) (@lem1761906 x h1)). Qed.
Lemma lem1761911 (x : real) (h1 : term130 = False) : (term156 x) = (term227 x).
Proof. exact (MK_COMB (@lem1761826 x h1) (@lem1761908 x h1)). Qed.
Lemma lem1761914 (x : real) : (term228 x) = (term228 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem1761915 (x : real) (h1 : term130 = False) : (term200 x) = (term229 x).
Proof. exact (MK_COMB (@lem1761914 x) (@lem1761911 x h1)). Qed.
Lemma lem1761918 (x : real) : (term199 x) = (term199 x).
Proof. exact (eq_refl (term199 x)). Qed.
Lemma lem1761919 (x : real) (h1 : term130 = False) : (term201 x) = (term236 x).
Proof. exact (MK_COMB (@lem1761918 x) (@lem1761915 x h1)). Qed.
Lemma lem1761922 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem1761923 (x : real) (h1 : term130 = False) : (term238 x) = (term239 x).
Proof. exact (MK_COMB (@lem1761922) (@lem1761919 x h1)). Qed.
Lemma lem1761926 (x : real) (h1 : term130 = False) : (term218 x) = (term240 x).
Proof. exact (MK_COMB (@lem1761692 x h1) (@lem1761923 x h1)). Qed.
Lemma lem1761929 (x : real) : term241 x.
Proof. exact (fun h0 : term130 = False => @lem1761926 x h0). Qed.
Lemma lem1761973 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1761974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761975 (h1 : term130 = True) : term131 = (and True).
Proof. exact (MK_COMB (@lem1761974) (@lem1761973 h1)). Qed.
Lemma lem1761978 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1761979 (h1 : term130 = True) : term133 = term242.
Proof. exact (MK_COMB (@lem1761975 h1) (@lem1761978)). Qed.
Lemma lem1761981 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1761982 : term242 = term132.
Proof. exact (@lem1761981 term132). Qed.
Lemma lem1761983 (h1 : term130 = True) : term133 = term132.
Proof. exact (TRANS (@lem1761979 h1) (@lem1761982)). Qed.
Lemma lem1761984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1761985 (h1 : term130 = True) : term134 = term243.
Proof. exact (MK_COMB (@lem1761984) (@lem1761983 h1)). Qed.
Lemma lem1761987 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1761988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1761989 (h1 : term130 = True) : term135 = (~ True).
Proof. exact (MK_COMB (@lem1761988) (@lem1761987 h1)). Qed.
Lemma lem1761991 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1761992 (h1 : term130 = True) : term135 = False.
Proof. exact (TRANS (@lem1761989 h1) (@lem1761991)). Qed.
Lemma lem1761993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1761994 (h1 : term130 = True) : term136 = (and False).
Proof. exact (MK_COMB (@lem1761993) (@lem1761992 h1)). Qed.
Lemma lem1761996 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1761997 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1761998 (h1 : term130 = True) : term137 = (@COND real True).
Proof. exact (MK_COMB (@lem1761997) (@lem1761996 h1)). Qed.
Lemma lem1761999 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1762000 (h1 : term130 = True) : term138 = term115.
Proof. exact (MK_COMB (@lem1761998 h1) (@lem1761999)). Qed.
Lemma lem1762001 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762002 (h1 : term130 = True) : term139 = term116.
Proof. exact (MK_COMB (@lem1762000 h1) (@lem1762001)). Qed.
Lemma lem1762004 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1762005 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1762004 real t2 t1). Qed.
Lemma lem1762006 : term116 = term19.
Proof. exact (@lem1762005 term14 term19). Qed.
Lemma lem1762007 (h1 : term130 = True) : term139 = term19.
Proof. exact (TRANS (@lem1762002 h1) (@lem1762006)). Qed.
Lemma lem1762008 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1762009 (h1 : term130 = True) : term140 = term117.
Proof. exact (MK_COMB (@lem1762008) (@lem1762007 h1)). Qed.
Lemma lem1762010 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762011 (h1 : term130 = True) : (term139 = term14) = (term19 = term14).
Proof. exact (MK_COMB (@lem1762009 h1) (@lem1762010)). Qed.
Lemma lem1762014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762015 (h1 : term130 = True) : term141 = term244.
Proof. exact (MK_COMB (@lem1762014) (@lem1762011 h1)). Qed.
Lemma lem1762016 (h1 : term130 = True) : term142 = term245.
Proof. exact (MK_COMB (@lem1761994 h1) (@lem1762015 h1)). Qed.
Lemma lem1762018 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1762019 : term245 = False.
Proof. exact (@lem1762018 term244). Qed.
Lemma lem1762020 (h1 : term130 = True) : term142 = False.
Proof. exact (TRANS (@lem1762016 h1) (@lem1762019)). Qed.
Lemma lem1762021 (h1 : term130 = True) : term143 = term246.
Proof. exact (MK_COMB (@lem1761985 h1) (@lem1762020 h1)). Qed.
Lemma lem1762023 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1762024 : term246 = term132.
Proof. exact (@lem1762023 term132). Qed.
Lemma lem1762025 (h1 : term130 = True) : term143 = term132.
Proof. exact (TRANS (@lem1762021 h1) (@lem1762024)). Qed.
Lemma lem1762026 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1762027 (x : real) (h1 : term130 = True) : (term145 x) = (term247 x).
Proof. exact (MK_COMB (@lem1762026 x) (@lem1762025 h1)). Qed.
Lemma lem1762030 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1762031 (x : real) (h1 : term130 = True) : (term146 x) = (term248 x).
Proof. exact (MK_COMB (@lem1762030 x) (@lem1762027 x h1)). Qed.
Lemma lem1762034 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1762035 (x : real) (h1 : term130 = True) : (term149 x) = (term249 x).
Proof. exact (MK_COMB (@lem1762034) (@lem1762031 x h1)). Qed.
Lemma lem1762038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762039 (x : real) (h1 : term130 = True) : (term151 x) = (term250 x).
Proof. exact (MK_COMB (@lem1762038) (@lem1762035 x h1)). Qed.
Lemma lem1762047 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762049 (h1 : term130 = True) : term131 = (and True).
Proof. exact (MK_COMB (@lem1762048) (@lem1762047 h1)). Qed.
Lemma lem1762052 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1762053 (h1 : term130 = True) : term133 = term242.
Proof. exact (MK_COMB (@lem1762049 h1) (@lem1762052)). Qed.
Lemma lem1762055 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1762056 : term242 = term132.
Proof. exact (@lem1762055 term132). Qed.
Lemma lem1762057 (h1 : term130 = True) : term133 = term132.
Proof. exact (TRANS (@lem1762053 h1) (@lem1762056)). Qed.
Lemma lem1762058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762059 (h1 : term130 = True) : term134 = term243.
Proof. exact (MK_COMB (@lem1762058) (@lem1762057 h1)). Qed.
Lemma lem1762061 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762062 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762063 (h1 : term130 = True) : term135 = (~ True).
Proof. exact (MK_COMB (@lem1762062) (@lem1762061 h1)). Qed.
Lemma lem1762065 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1762066 (h1 : term130 = True) : term135 = False.
Proof. exact (TRANS (@lem1762063 h1) (@lem1762065)). Qed.
Lemma lem1762067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762068 (h1 : term130 = True) : term136 = (and False).
Proof. exact (MK_COMB (@lem1762067) (@lem1762066 h1)). Qed.
Lemma lem1762070 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762071 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1762072 (h1 : term130 = True) : term137 = (@COND real True).
Proof. exact (MK_COMB (@lem1762071) (@lem1762070 h1)). Qed.
Lemma lem1762073 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1762074 (h1 : term130 = True) : term138 = term115.
Proof. exact (MK_COMB (@lem1762072 h1) (@lem1762073)). Qed.
Lemma lem1762075 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762076 (h1 : term130 = True) : term139 = term116.
Proof. exact (MK_COMB (@lem1762074 h1) (@lem1762075)). Qed.
Lemma lem1762078 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1762079 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1762078 real t2 t1). Qed.
Lemma lem1762080 : term116 = term19.
Proof. exact (@lem1762079 term14 term19). Qed.
Lemma lem1762081 (h1 : term130 = True) : term139 = term19.
Proof. exact (TRANS (@lem1762076 h1) (@lem1762080)). Qed.
Lemma lem1762082 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1762083 (h1 : term130 = True) : term140 = term117.
Proof. exact (MK_COMB (@lem1762082) (@lem1762081 h1)). Qed.
Lemma lem1762084 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762085 (h1 : term130 = True) : (term139 = term14) = (term19 = term14).
Proof. exact (MK_COMB (@lem1762083 h1) (@lem1762084)). Qed.
Lemma lem1762088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762089 (h1 : term130 = True) : term141 = term244.
Proof. exact (MK_COMB (@lem1762088) (@lem1762085 h1)). Qed.
Lemma lem1762090 (h1 : term130 = True) : term142 = term245.
Proof. exact (MK_COMB (@lem1762068 h1) (@lem1762089 h1)). Qed.
Lemma lem1762092 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1762093 : term245 = False.
Proof. exact (@lem1762092 term244). Qed.
Lemma lem1762094 (h1 : term130 = True) : term142 = False.
Proof. exact (TRANS (@lem1762090 h1) (@lem1762093)). Qed.
Lemma lem1762095 (h1 : term130 = True) : term143 = term246.
Proof. exact (MK_COMB (@lem1762059 h1) (@lem1762094 h1)). Qed.
Lemma lem1762097 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1762098 : term246 = term132.
Proof. exact (@lem1762097 term132). Qed.
Lemma lem1762099 (h1 : term130 = True) : term143 = term132.
Proof. exact (TRANS (@lem1762095 h1) (@lem1762098)). Qed.
Lemma lem1762100 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1762101 (x : real) (h1 : term130 = True) : (term145 x) = (term247 x).
Proof. exact (MK_COMB (@lem1762100 x) (@lem1762099 h1)). Qed.
Lemma lem1762104 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1762105 (x : real) (h1 : term130 = True) : (term152 x) = (term251 x).
Proof. exact (MK_COMB (@lem1762104 x) (@lem1762101 x h1)). Qed.
Lemma lem1762108 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1762109 (x : real) (h1 : term130 = True) : (term155 x) = (term252 x).
Proof. exact (MK_COMB (@lem1762108) (@lem1762105 x h1)). Qed.
Lemma lem1762112 (x : real) (h1 : term130 = True) : (term156 x) = (term253 x).
Proof. exact (MK_COMB (@lem1762039 x h1) (@lem1762109 x h1)). Qed.
Lemma lem1762115 (x : real) : (term228 x) = (term228 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem1762116 (x : real) (h1 : term130 = True) : (term200 x) = (term254 x).
Proof. exact (MK_COMB (@lem1762115 x) (@lem1762112 x h1)). Qed.
Lemma lem1762119 (x : real) : (term213 x) = (term213 x).
Proof. exact (eq_refl (term213 x)). Qed.
Lemma lem1762120 (x : real) (h1 : term130 = True) : (term214 x) = (term255 x).
Proof. exact (MK_COMB (@lem1762119 x) (@lem1762116 x h1)). Qed.
Lemma lem1762123 : term231 = term231.
Proof. exact (eq_refl term231). Qed.
Lemma lem1762124 (x : real) (h1 : term130 = True) : (term232 x) = (term256 x).
Proof. exact (MK_COMB (@lem1762123) (@lem1762120 x h1)). Qed.
Lemma lem1762127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762128 (x : real) (h1 : term130 = True) : (term234 x) = (term257 x).
Proof. exact (MK_COMB (@lem1762127) (@lem1762124 x h1)). Qed.
Lemma lem1762184 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762186 (h1 : term130 = True) : term131 = (and True).
Proof. exact (MK_COMB (@lem1762185) (@lem1762184 h1)). Qed.
Lemma lem1762189 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1762190 (h1 : term130 = True) : term133 = term242.
Proof. exact (MK_COMB (@lem1762186 h1) (@lem1762189)). Qed.
Lemma lem1762192 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1762193 : term242 = term132.
Proof. exact (@lem1762192 term132). Qed.
Lemma lem1762194 (h1 : term130 = True) : term133 = term132.
Proof. exact (TRANS (@lem1762190 h1) (@lem1762193)). Qed.
Lemma lem1762195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762196 (h1 : term130 = True) : term134 = term243.
Proof. exact (MK_COMB (@lem1762195) (@lem1762194 h1)). Qed.
Lemma lem1762198 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762199 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762200 (h1 : term130 = True) : term135 = (~ True).
Proof. exact (MK_COMB (@lem1762199) (@lem1762198 h1)). Qed.
Lemma lem1762202 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1762203 (h1 : term130 = True) : term135 = False.
Proof. exact (TRANS (@lem1762200 h1) (@lem1762202)). Qed.
Lemma lem1762204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762205 (h1 : term130 = True) : term136 = (and False).
Proof. exact (MK_COMB (@lem1762204) (@lem1762203 h1)). Qed.
Lemma lem1762207 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762208 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1762209 (h1 : term130 = True) : term137 = (@COND real True).
Proof. exact (MK_COMB (@lem1762208) (@lem1762207 h1)). Qed.
Lemma lem1762210 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1762211 (h1 : term130 = True) : term138 = term115.
Proof. exact (MK_COMB (@lem1762209 h1) (@lem1762210)). Qed.
Lemma lem1762212 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762213 (h1 : term130 = True) : term139 = term116.
Proof. exact (MK_COMB (@lem1762211 h1) (@lem1762212)). Qed.
Lemma lem1762215 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1762216 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1762215 real t2 t1). Qed.
Lemma lem1762217 : term116 = term19.
Proof. exact (@lem1762216 term14 term19). Qed.
Lemma lem1762218 (h1 : term130 = True) : term139 = term19.
Proof. exact (TRANS (@lem1762213 h1) (@lem1762217)). Qed.
Lemma lem1762219 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1762220 (h1 : term130 = True) : term140 = term117.
Proof. exact (MK_COMB (@lem1762219) (@lem1762218 h1)). Qed.
Lemma lem1762221 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762222 (h1 : term130 = True) : (term139 = term14) = (term19 = term14).
Proof. exact (MK_COMB (@lem1762220 h1) (@lem1762221)). Qed.
Lemma lem1762225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762226 (h1 : term130 = True) : term141 = term244.
Proof. exact (MK_COMB (@lem1762225) (@lem1762222 h1)). Qed.
Lemma lem1762227 (h1 : term130 = True) : term142 = term245.
Proof. exact (MK_COMB (@lem1762205 h1) (@lem1762226 h1)). Qed.
Lemma lem1762229 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1762230 : term245 = False.
Proof. exact (@lem1762229 term244). Qed.
Lemma lem1762231 (h1 : term130 = True) : term142 = False.
Proof. exact (TRANS (@lem1762227 h1) (@lem1762230)). Qed.
Lemma lem1762232 (h1 : term130 = True) : term143 = term246.
Proof. exact (MK_COMB (@lem1762196 h1) (@lem1762231 h1)). Qed.
Lemma lem1762234 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1762235 : term246 = term132.
Proof. exact (@lem1762234 term132). Qed.
Lemma lem1762236 (h1 : term130 = True) : term143 = term132.
Proof. exact (TRANS (@lem1762232 h1) (@lem1762235)). Qed.
Lemma lem1762237 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1762238 (x : real) (h1 : term130 = True) : (term145 x) = (term247 x).
Proof. exact (MK_COMB (@lem1762237 x) (@lem1762236 h1)). Qed.
Lemma lem1762241 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1762242 (x : real) (h1 : term130 = True) : (term146 x) = (term248 x).
Proof. exact (MK_COMB (@lem1762241 x) (@lem1762238 x h1)). Qed.
Lemma lem1762245 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1762246 (x : real) (h1 : term130 = True) : (term149 x) = (term249 x).
Proof. exact (MK_COMB (@lem1762245) (@lem1762242 x h1)). Qed.
Lemma lem1762249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762250 (x : real) (h1 : term130 = True) : (term151 x) = (term250 x).
Proof. exact (MK_COMB (@lem1762249) (@lem1762246 x h1)). Qed.
Lemma lem1762258 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762260 (h1 : term130 = True) : term131 = (and True).
Proof. exact (MK_COMB (@lem1762259) (@lem1762258 h1)). Qed.
Lemma lem1762263 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1762264 (h1 : term130 = True) : term133 = term242.
Proof. exact (MK_COMB (@lem1762260 h1) (@lem1762263)). Qed.
Lemma lem1762266 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1762267 : term242 = term132.
Proof. exact (@lem1762266 term132). Qed.
Lemma lem1762268 (h1 : term130 = True) : term133 = term132.
Proof. exact (TRANS (@lem1762264 h1) (@lem1762267)). Qed.
Lemma lem1762269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1762270 (h1 : term130 = True) : term134 = term243.
Proof. exact (MK_COMB (@lem1762269) (@lem1762268 h1)). Qed.
Lemma lem1762272 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762273 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762274 (h1 : term130 = True) : term135 = (~ True).
Proof. exact (MK_COMB (@lem1762273) (@lem1762272 h1)). Qed.
Lemma lem1762276 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1762277 (h1 : term130 = True) : term135 = False.
Proof. exact (TRANS (@lem1762274 h1) (@lem1762276)). Qed.
Lemma lem1762278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1762279 (h1 : term130 = True) : term136 = (and False).
Proof. exact (MK_COMB (@lem1762278) (@lem1762277 h1)). Qed.
Lemma lem1762281 (h1 : term130 = True) : term130 = True.
Proof. exact (h1). Qed.
Lemma lem1762282 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1762283 (h1 : term130 = True) : term137 = (@COND real True).
Proof. exact (MK_COMB (@lem1762282) (@lem1762281 h1)). Qed.
Lemma lem1762284 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1762285 (h1 : term130 = True) : term138 = term115.
Proof. exact (MK_COMB (@lem1762283 h1) (@lem1762284)). Qed.
Lemma lem1762286 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762287 (h1 : term130 = True) : term139 = term116.
Proof. exact (MK_COMB (@lem1762285 h1) (@lem1762286)). Qed.
Lemma lem1762289 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1762290 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1762289 real t2 t1). Qed.
Lemma lem1762291 : term116 = term19.
Proof. exact (@lem1762290 term14 term19). Qed.
Lemma lem1762292 (h1 : term130 = True) : term139 = term19.
Proof. exact (TRANS (@lem1762287 h1) (@lem1762291)). Qed.
Lemma lem1762293 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1762294 (h1 : term130 = True) : term140 = term117.
Proof. exact (MK_COMB (@lem1762293) (@lem1762292 h1)). Qed.
Lemma lem1762295 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1762296 (h1 : term130 = True) : (term139 = term14) = (term19 = term14).
Proof. exact (MK_COMB (@lem1762294 h1) (@lem1762295)). Qed.
Lemma lem1762299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1762300 (h1 : term130 = True) : term141 = term244.
Proof. exact (MK_COMB (@lem1762299) (@lem1762296 h1)). Qed.
Lemma lem1762301 (h1 : term130 = True) : term142 = term245.
Proof. exact (MK_COMB (@lem1762279 h1) (@lem1762300 h1)). Qed.
Lemma lem1762303 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1762304 : term245 = False.
Proof. exact (@lem1762303 term244). Qed.
Lemma lem1762305 (h1 : term130 = True) : term142 = False.
Proof. exact (TRANS (@lem1762301 h1) (@lem1762304)). Qed.
Lemma lem1762306 (h1 : term130 = True) : term143 = term246.
Proof. exact (MK_COMB (@lem1762270 h1) (@lem1762305 h1)). Qed.
Lemma lem1762308 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1762309 : term246 = term132.
Proof. exact (@lem1762308 term132). Qed.
Lemma lem1762310 (h1 : term130 = True) : term143 = term132.
Proof. exact (TRANS (@lem1762306 h1) (@lem1762309)). Qed.
Lemma lem1762311 (x : real) : (term144 x) = (term144 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1762312 (x : real) (h1 : term130 = True) : (term145 x) = (term247 x).
Proof. exact (MK_COMB (@lem1762311 x) (@lem1762310 h1)). Qed.
Lemma lem1762315 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1762316 (x : real) (h1 : term130 = True) : (term152 x) = (term251 x).
Proof. exact (MK_COMB (@lem1762315 x) (@lem1762312 x h1)). Qed.
Lemma lem1762319 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem1762320 (x : real) (h1 : term130 = True) : (term155 x) = (term252 x).
Proof. exact (MK_COMB (@lem1762319) (@lem1762316 x h1)). Qed.
Lemma lem1762323 (x : real) (h1 : term130 = True) : (term156 x) = (term253 x).
Proof. exact (MK_COMB (@lem1762250 x h1) (@lem1762320 x h1)). Qed.
Lemma lem1762326 (x : real) : (term228 x) = (term228 x).
Proof. exact (eq_refl (term228 x)). Qed.
Lemma lem1762327 (x : real) (h1 : term130 = True) : (term200 x) = (term254 x).
Proof. exact (MK_COMB (@lem1762326 x) (@lem1762323 x h1)). Qed.
Lemma lem1762330 (x : real) : (term199 x) = (term199 x).
Proof. exact (eq_refl (term199 x)). Qed.
Lemma lem1762331 (x : real) (h1 : term130 = True) : (term201 x) = (term258 x).
Proof. exact (MK_COMB (@lem1762330 x) (@lem1762327 x h1)). Qed.
Lemma lem1762334 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem1762335 (x : real) (h1 : term130 = True) : (term238 x) = (term259 x).
Proof. exact (MK_COMB (@lem1762334) (@lem1762331 x h1)). Qed.
Lemma lem1762338 (x : real) (h1 : term130 = True) : (term218 x) = (term260 x).
Proof. exact (MK_COMB (@lem1762128 x h1) (@lem1762335 x h1)). Qed.
Lemma lem1762341 (x : real) : term261 x.
Proof. exact (fun h0 : term130 = True => @lem1762338 x h0). Qed.
Lemma lem1762342 (x : real) : term262 x.
Proof. exact (conj (@lem1761929 x) (@lem1762341 x)). Qed.
Lemma lem1762344 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term52 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1762345 (x : real) : term263 x.
Proof. exact (@lem1762344 (term218 x) (term260 x) term130 (term240 x)). Qed.
Lemma lem1762990 (x : real) : (term218 x) = (term264 x).
Proof. exact (@lem1762345 x (@lem1762342 x)). Qed.
Lemma lem1762991 (x : real) : (term265 x) = (term265 x).
Proof. exact (eq_refl (term265 x)). Qed.
Lemma lem1762992 (x : real) : ((term184 x) = (term218 x)) = ((term184 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1762991 x) (@lem1762990 x)). Qed.
Lemma lem1762993 (x : real) : (term184 x) = (term264 x).
Proof. exact (EQ_MP (@lem1762992 x) (@lem1761467 x)). Qed.
Lemma lem1762994 (x : real) : (term266 x) = (term266 x).
Proof. exact (eq_refl (term266 x)). Qed.
Lemma lem1762995 (x : real) : ((term126 x) = (term184 x)) = ((term126 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1762994 x) (@lem1762993 x)). Qed.
Lemma lem1762996 (x : real) : (term126 x) = (term264 x).
Proof. exact (EQ_MP (@lem1762995 x) (@lem1761090 x)). Qed.
Lemma lem1762997 (x : real) : (term267 x) = (term267 x).
Proof. exact (eq_refl (term267 x)). Qed.
Lemma lem1762998 (x : real) : ((term101 x) = (term126 x)) = ((term101 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1762997 x) (@lem1762996 x)). Qed.
Lemma lem1762999 (x : real) : (term101 x) = (term264 x).
Proof. exact (EQ_MP (@lem1762998 x) (@lem1760549 x)). Qed.
Lemma lem1763000 (x : real) : (term268 x) = (term268 x).
Proof. exact (eq_refl (term268 x)). Qed.
Lemma lem1763001 (x : real) : ((term54 x) = (term101 x)) = ((term54 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1763000 x) (@lem1762999 x)). Qed.
Lemma lem1763002 (x : real) : (term54 x) = (term264 x).
Proof. exact (EQ_MP (@lem1763001 x) (@lem1760432 x)). Qed.
Lemma lem1763003 (x : real) : (term269 x) = (term269 x).
Proof. exact (eq_refl (term269 x)). Qed.
Lemma lem1763004 (x : real) : ((term37 x) = (term54 x)) = ((term37 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1763003 x) (@lem1763002 x)). Qed.
Lemma lem1763005 (x : real) : (term37 x) = (term264 x).
Proof. exact (EQ_MP (@lem1763004 x) (@lem1760179 x)). Qed.
Lemma lem1763006 : term39 = term270.
Proof. exact (fun_ext (fun x : real => @lem1763005 x)). Qed.
Lemma lem1763007 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1763008 : term40 = term271.
Proof. exact (MK_COMB (@lem1763007) (@lem1763006)). Qed.
Lemma lem1763009 : term33 = term271.
Proof. exact (TRANS (@lem1760114) (@lem1763008)). Qed.
Lemma lem1763010 : term130 = term272.
Proof. exact (@lem1483521 term14 term14). Qed.
Lemma lem1763016 : term273 = term274.
Proof. exact (@lem1483519 term14 term14). Qed.
Lemma lem1763018 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763019 : term276 = term14.
Proof. exact (@lem1763018 term277). Qed.
Lemma lem1763020 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763021 : term274 = term279.
Proof. exact (MK_COMB (@lem1763020) (@lem1763019)). Qed.
Lemma lem1763022 : term279 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1763023 : term274 = term14.
Proof. exact (TRANS (@lem1763021) (@lem1763022)). Qed.
Lemma lem1763025 : term273 = term14.
Proof. exact (TRANS (@lem1763016) (@lem1763023)). Qed.
Lemma lem1763026 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763027 : term280 = term281.
Proof. exact (MK_COMB (@lem1763026) (@lem1763025)). Qed.
Lemma lem1763028 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763029 : term272 = term282.
Proof. exact (MK_COMB (@lem1763027) (@lem1763028)). Qed.
Lemma lem1763030 : term130 = term282.
Proof. exact (TRANS (@lem1763010) (@lem1763029)). Qed.
Lemma lem1763031 : term166 = term283.
Proof. exact (@lem1483521 term14 term19). Qed.
Lemma lem1763037 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1763039 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763040 : term288 = term289.
Proof. exact (@lem1763039 term277 term277). Qed.
Lemma lem1763041 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763042 : term291 = term277.
Proof. exact (EQ_MP (@lem1763041) (@lem940073)). Qed.
Lemma lem1763043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763044 : term289 = term9.
Proof. exact (MK_COMB (@lem1763043) (@lem1763042)). Qed.
Lemma lem1763045 : term288 = term9.
Proof. exact (TRANS (@lem1763040) (@lem1763044)). Qed.
Lemma lem1763046 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763047 : term285 = term292.
Proof. exact (MK_COMB (@lem1763046) (@lem1763045)). Qed.
Lemma lem1763048 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1763049 : term285 = term9.
Proof. exact (TRANS (@lem1763047) (@lem1763048)). Qed.
Lemma lem1763051 : term284 = term9.
Proof. exact (TRANS (@lem1763037) (@lem1763049)). Qed.
Lemma lem1763052 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763053 : term293 = term294.
Proof. exact (MK_COMB (@lem1763052) (@lem1763051)). Qed.
Lemma lem1763054 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763055 : term283 = term295.
Proof. exact (MK_COMB (@lem1763053) (@lem1763054)). Qed.
Lemma lem1763056 : term166 = term295.
Proof. exact (TRANS (@lem1763031) (@lem1763055)). Qed.
Lemma lem1763057 (x : real) : (term127 x) = (term296 x).
Proof. exact (@lem1483521 term14 x). Qed.
Lemma lem1763063 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1763068 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1763070 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1763063 x) (@lem1763068 x)). Qed.
Lemma lem1763071 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763072 (x : real) : (term300 x) = (term301 x).
Proof. exact (MK_COMB (@lem1763071) (@lem1763070 x)). Qed.
Lemma lem1763073 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763074 (x : real) : (term296 x) = (term302 x).
Proof. exact (MK_COMB (@lem1763072 x) (@lem1763073)). Qed.
Lemma lem1763075 (x : real) : (term127 x) = (term302 x).
Proof. exact (TRANS (@lem1763057 x) (@lem1763074 x)). Qed.
Lemma lem1763076 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1763082 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763084 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763085 : term308 = term309.
Proof. exact (@lem1763084 term277 term277). Qed.
Lemma lem1763086 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763087 : term291 = term277.
Proof. exact (EQ_MP (@lem1763086) (@lem940073)). Qed.
Lemma lem1763088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763089 : term289 = term9.
Proof. exact (MK_COMB (@lem1763088) (@lem1763087)). Qed.
Lemma lem1763090 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763091 : term309 = term19.
Proof. exact (MK_COMB (@lem1763090) (@lem1763089)). Qed.
Lemma lem1763092 : term308 = term19.
Proof. exact (TRANS (@lem1763085) (@lem1763091)). Qed.
Lemma lem1763093 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763094 : term305 = term310.
Proof. exact (MK_COMB (@lem1763093) (@lem1763092)). Qed.
Lemma lem1763095 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763096 : term305 = term19.
Proof. exact (TRANS (@lem1763094) (@lem1763095)). Qed.
Lemma lem1763098 : term304 = term19.
Proof. exact (TRANS (@lem1763082) (@lem1763096)). Qed.
Lemma lem1763099 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763100 : term311 = term312.
Proof. exact (MK_COMB (@lem1763099) (@lem1763098)). Qed.
Lemma lem1763101 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763102 : term303 = term313.
Proof. exact (MK_COMB (@lem1763100) (@lem1763101)). Qed.
Lemma lem1763103 : term90 = term313.
Proof. exact (TRANS (@lem1763076) (@lem1763102)). Qed.
Lemma lem1763104 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1763110 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1763112 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763113 : term276 = term14.
Proof. exact (@lem1763112 term277). Qed.
Lemma lem1763114 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1763115 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1763114 x) (@lem1763113)). Qed.
Lemma lem1763116 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1763117 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1763115 x) (@lem1763116 x)). Qed.
Lemma lem1763119 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1763110 x) (@lem1763117 x)). Qed.
Lemma lem1763120 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763121 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1763120) (@lem1763119 x)). Qed.
Lemma lem1763122 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763123 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1763121 x) (@lem1763122)). Qed.
Lemma lem1763124 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1763104 x) (@lem1763123 x)). Qed.
Lemma lem1763125 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1763131 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763133 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763134 : term308 = term309.
Proof. exact (@lem1763133 term277 term277). Qed.
Lemma lem1763135 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763136 : term291 = term277.
Proof. exact (EQ_MP (@lem1763135) (@lem940073)). Qed.
Lemma lem1763137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763138 : term289 = term9.
Proof. exact (MK_COMB (@lem1763137) (@lem1763136)). Qed.
Lemma lem1763139 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763140 : term309 = term19.
Proof. exact (MK_COMB (@lem1763139) (@lem1763138)). Qed.
Lemma lem1763141 : term308 = term19.
Proof. exact (TRANS (@lem1763134) (@lem1763140)). Qed.
Lemma lem1763142 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763143 : term305 = term310.
Proof. exact (MK_COMB (@lem1763142) (@lem1763141)). Qed.
Lemma lem1763144 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763145 : term305 = term19.
Proof. exact (TRANS (@lem1763143) (@lem1763144)). Qed.
Lemma lem1763147 : term304 = term19.
Proof. exact (TRANS (@lem1763131) (@lem1763145)). Qed.
Lemma lem1763148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763149 : term321 = term322.
Proof. exact (MK_COMB (@lem1763148) (@lem1763147)). Qed.
Lemma lem1763150 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763151 : term320 = term323.
Proof. exact (MK_COMB (@lem1763149) (@lem1763150)). Qed.
Lemma lem1763152 : term87 = term323.
Proof. exact (TRANS (@lem1763125) (@lem1763151)). Qed.
Lemma lem1763153 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1763159 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1763161 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763162 : term308 = term309.
Proof. exact (@lem1763161 term277 term277). Qed.
Lemma lem1763163 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763164 : term291 = term277.
Proof. exact (EQ_MP (@lem1763163) (@lem940073)). Qed.
Lemma lem1763165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763166 : term289 = term9.
Proof. exact (MK_COMB (@lem1763165) (@lem1763164)). Qed.
Lemma lem1763167 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763168 : term309 = term19.
Proof. exact (MK_COMB (@lem1763167) (@lem1763166)). Qed.
Lemma lem1763169 : term308 = term19.
Proof. exact (TRANS (@lem1763162) (@lem1763168)). Qed.
Lemma lem1763170 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1763171 : term326 = term328.
Proof. exact (MK_COMB (@lem1763170) (@lem1763169)). Qed.
Lemma lem1763172 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1763173 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1763174 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1763175 : term332 = term333.
Proof. exact (EQ_MP (@lem1763174) (@lem1763173)). Qed.
Lemma lem1763176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763177 : term334 = term335.
Proof. exact (MK_COMB (@lem1763176) (@lem1763175)). Qed.
Lemma lem1763178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763179 : term329 = term336.
Proof. exact (MK_COMB (@lem1763178) (@lem1763177)). Qed.
Lemma lem1763180 : term328 = term336.
Proof. exact (TRANS (@lem1763172) (@lem1763179)). Qed.
Lemma lem1763181 : term326 = term336.
Proof. exact (TRANS (@lem1763171) (@lem1763180)). Qed.
Lemma lem1763183 : term325 = term336.
Proof. exact (TRANS (@lem1763159) (@lem1763181)). Qed.
Lemma lem1763184 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763185 : term337 = term338.
Proof. exact (MK_COMB (@lem1763184) (@lem1763183)). Qed.
Lemma lem1763186 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1763188 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763189 : term339 = term340.
Proof. exact (@lem1763188 term277 term333). Qed.
Lemma lem1763190 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1763191 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1763192 : term342 = term333.
Proof. exact (EQ_MP (@lem1763191) (@lem1763190)). Qed.
Lemma lem1763193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763194 : term340 = term335.
Proof. exact (MK_COMB (@lem1763193) (@lem1763192)). Qed.
Lemma lem1763195 : term339 = term335.
Proof. exact (TRANS (@lem1763189) (@lem1763194)). Qed.
Lemma lem1763196 : term338 = term335.
Proof. exact (TRANS (@lem1763186) (@lem1763195)). Qed.
Lemma lem1763197 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1763198 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1763197) (@lem1763196)). Qed.
Lemma lem1763199 : term337 = term335.
Proof. exact (EQ_MP (@lem1763198) (@lem1763185)). Qed.
Lemma lem1763200 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763201 : term344 = term345.
Proof. exact (MK_COMB (@lem1763200) (@lem1763199)). Qed.
Lemma lem1763202 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763203 : term346 = term347.
Proof. exact (MK_COMB (@lem1763201) (@lem1763202)). Qed.
Lemma lem1763204 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763205 : term348 = term349.
Proof. exact (MK_COMB (@lem1763204) (@lem1763183)). Qed.
Lemma lem1763206 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763207 : term350 = term351.
Proof. exact (MK_COMB (@lem1763205) (@lem1763206)). Qed.
Lemma lem1763208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763209 : term352 = term353.
Proof. exact (MK_COMB (@lem1763208) (@lem1763207)). Qed.
Lemma lem1763210 : term324 = term354.
Proof. exact (MK_COMB (@lem1763209) (@lem1763203)). Qed.
Lemma lem1763211 : term118 = term354.
Proof. exact (TRANS (@lem1763153) (@lem1763210)). Qed.
Lemma lem1763212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763213 : term88 = term355.
Proof. exact (MK_COMB (@lem1763212) (@lem1763152)). Qed.
Lemma lem1763214 : term119 = term356.
Proof. exact (MK_COMB (@lem1763213) (@lem1763211)). Qed.
Lemma lem1763215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763216 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1763215) (@lem1763124 x)). Qed.
Lemma lem1763217 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1763216 x) (@lem1763214)). Qed.
Lemma lem1763218 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1763224 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1763229 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1763231 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1763224 x) (@lem1763229 x)). Qed.
Lemma lem1763232 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763233 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1763232) (@lem1763231 x)). Qed.
Lemma lem1763234 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763235 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1763233 x) (@lem1763234)). Qed.
Lemma lem1763236 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1763218 x) (@lem1763235 x)). Qed.
Lemma lem1763237 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1763243 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1763245 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763246 : term276 = term14.
Proof. exact (@lem1763245 term277). Qed.
Lemma lem1763247 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1763248 : term365 = term366.
Proof. exact (MK_COMB (@lem1763247) (@lem1763246)). Qed.
Lemma lem1763249 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1763250 : term365 = term19.
Proof. exact (TRANS (@lem1763248) (@lem1763249)). Qed.
Lemma lem1763252 : term364 = term19.
Proof. exact (TRANS (@lem1763243) (@lem1763250)). Qed.
Lemma lem1763253 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763254 : term367 = term312.
Proof. exact (MK_COMB (@lem1763253) (@lem1763252)). Qed.
Lemma lem1763255 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763256 : term363 = term313.
Proof. exact (MK_COMB (@lem1763254) (@lem1763255)). Qed.
Lemma lem1763257 : term158 = term313.
Proof. exact (TRANS (@lem1763237) (@lem1763256)). Qed.
Lemma lem1763258 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1763264 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1763266 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763267 : term288 = term289.
Proof. exact (@lem1763266 term277 term277). Qed.
Lemma lem1763268 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763269 : term291 = term277.
Proof. exact (EQ_MP (@lem1763268) (@lem940073)). Qed.
Lemma lem1763270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763271 : term289 = term9.
Proof. exact (MK_COMB (@lem1763270) (@lem1763269)). Qed.
Lemma lem1763272 : term288 = term9.
Proof. exact (TRANS (@lem1763267) (@lem1763271)). Qed.
Lemma lem1763273 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763274 : term370 = term372.
Proof. exact (MK_COMB (@lem1763273) (@lem1763272)). Qed.
Lemma lem1763275 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1763276 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1763277 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1763278 : term332 = term333.
Proof. exact (EQ_MP (@lem1763277) (@lem1763276)). Qed.
Lemma lem1763279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763280 : term334 = term335.
Proof. exact (MK_COMB (@lem1763279) (@lem1763278)). Qed.
Lemma lem1763281 : term372 = term335.
Proof. exact (TRANS (@lem1763275) (@lem1763280)). Qed.
Lemma lem1763282 : term370 = term335.
Proof. exact (TRANS (@lem1763274) (@lem1763281)). Qed.
Lemma lem1763284 : term369 = term335.
Proof. exact (TRANS (@lem1763264) (@lem1763282)). Qed.
Lemma lem1763285 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763286 : term373 = term336.
Proof. exact (MK_COMB (@lem1763285) (@lem1763284)). Qed.
Lemma lem1763287 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1763289 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763290 : term374 = term375.
Proof. exact (@lem1763289 term277 term333). Qed.
Lemma lem1763291 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1763292 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1763293 : term342 = term333.
Proof. exact (EQ_MP (@lem1763292) (@lem1763291)). Qed.
Lemma lem1763294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763295 : term340 = term335.
Proof. exact (MK_COMB (@lem1763294) (@lem1763293)). Qed.
Lemma lem1763296 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763297 : term375 = term336.
Proof. exact (MK_COMB (@lem1763296) (@lem1763295)). Qed.
Lemma lem1763298 : term374 = term336.
Proof. exact (TRANS (@lem1763290) (@lem1763297)). Qed.
Lemma lem1763299 : term336 = term336.
Proof. exact (TRANS (@lem1763287) (@lem1763298)). Qed.
Lemma lem1763300 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1763301 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1763300) (@lem1763299)). Qed.
Lemma lem1763302 : term373 = term336.
Proof. exact (EQ_MP (@lem1763301) (@lem1763286)). Qed.
Lemma lem1763303 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763304 : term377 = term349.
Proof. exact (MK_COMB (@lem1763303) (@lem1763302)). Qed.
Lemma lem1763305 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763306 : term378 = term351.
Proof. exact (MK_COMB (@lem1763304) (@lem1763305)). Qed.
Lemma lem1763307 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763308 : term379 = term345.
Proof. exact (MK_COMB (@lem1763307) (@lem1763284)). Qed.
Lemma lem1763309 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763310 : term380 = term347.
Proof. exact (MK_COMB (@lem1763308) (@lem1763309)). Qed.
Lemma lem1763311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763312 : term381 = term382.
Proof. exact (MK_COMB (@lem1763311) (@lem1763310)). Qed.
Lemma lem1763313 : term368 = term383.
Proof. exact (MK_COMB (@lem1763312) (@lem1763306)). Qed.
Lemma lem1763314 : term160 = term383.
Proof. exact (TRANS (@lem1763258) (@lem1763313)). Qed.
Lemma lem1763315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763316 : term159 = term384.
Proof. exact (MK_COMB (@lem1763315) (@lem1763257)). Qed.
Lemma lem1763317 : term161 = term385.
Proof. exact (MK_COMB (@lem1763316) (@lem1763314)). Qed.
Lemma lem1763318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763319 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1763318) (@lem1763236 x)). Qed.
Lemma lem1763320 (x : real) : (term205 x) = (term387 x).
Proof. exact (MK_COMB (@lem1763319 x) (@lem1763317)). Qed.
Lemma lem1763321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763322 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1763321) (@lem1763217 x)). Qed.
Lemma lem1763323 (x : real) : (term206 x) = (term389 x).
Proof. exact (MK_COMB (@lem1763322 x) (@lem1763320 x)). Qed.
Lemma lem1763324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763325 : term147 = term384.
Proof. exact (MK_COMB (@lem1763324) (@lem1763103)). Qed.
Lemma lem1763326 (x : real) : (term207 x) = (term390 x).
Proof. exact (MK_COMB (@lem1763325) (@lem1763323 x)). Qed.
Lemma lem1763327 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1763333 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1763335 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763336 : term276 = term14.
Proof. exact (@lem1763335 term277). Qed.
Lemma lem1763337 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763338 : term394 = term395.
Proof. exact (MK_COMB (@lem1763337) (@lem1763336)). Qed.
Lemma lem1763339 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1763340 : term394 = term9.
Proof. exact (TRANS (@lem1763338) (@lem1763339)). Qed.
Lemma lem1763342 : term393 = term9.
Proof. exact (TRANS (@lem1763333) (@lem1763340)). Qed.
Lemma lem1763343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763344 : term396 = term397.
Proof. exact (MK_COMB (@lem1763343) (@lem1763342)). Qed.
Lemma lem1763345 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763346 : term392 = term398.
Proof. exact (MK_COMB (@lem1763344) (@lem1763345)). Qed.
Lemma lem1763347 : term391 = term398.
Proof. exact (TRANS (@lem1763327) (@lem1763346)). Qed.
Lemma lem1763348 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1763354 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1763356 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763357 : term276 = term14.
Proof. exact (@lem1763356 term277). Qed.
Lemma lem1763358 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1763359 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1763358 x) (@lem1763357)). Qed.
Lemma lem1763360 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1763361 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1763359 x) (@lem1763360 x)). Qed.
Lemma lem1763363 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1763354 x) (@lem1763361 x)). Qed.
Lemma lem1763364 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763365 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1763364) (@lem1763363 x)). Qed.
Lemma lem1763366 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763367 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1763365 x) (@lem1763366)). Qed.
Lemma lem1763368 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1763348 x) (@lem1763367 x)). Qed.
Lemma lem1763369 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1763375 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763377 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763378 : term308 = term309.
Proof. exact (@lem1763377 term277 term277). Qed.
Lemma lem1763379 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763380 : term291 = term277.
Proof. exact (EQ_MP (@lem1763379) (@lem940073)). Qed.
Lemma lem1763381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763382 : term289 = term9.
Proof. exact (MK_COMB (@lem1763381) (@lem1763380)). Qed.
Lemma lem1763383 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763384 : term309 = term19.
Proof. exact (MK_COMB (@lem1763383) (@lem1763382)). Qed.
Lemma lem1763385 : term308 = term19.
Proof. exact (TRANS (@lem1763378) (@lem1763384)). Qed.
Lemma lem1763386 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763387 : term305 = term310.
Proof. exact (MK_COMB (@lem1763386) (@lem1763385)). Qed.
Lemma lem1763388 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763389 : term305 = term19.
Proof. exact (TRANS (@lem1763387) (@lem1763388)). Qed.
Lemma lem1763391 : term304 = term19.
Proof. exact (TRANS (@lem1763375) (@lem1763389)). Qed.
Lemma lem1763392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763393 : term321 = term322.
Proof. exact (MK_COMB (@lem1763392) (@lem1763391)). Qed.
Lemma lem1763394 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763395 : term320 = term323.
Proof. exact (MK_COMB (@lem1763393) (@lem1763394)). Qed.
Lemma lem1763396 : term87 = term323.
Proof. exact (TRANS (@lem1763369) (@lem1763395)). Qed.
Lemma lem1763397 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1763403 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763405 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763406 : term308 = term309.
Proof. exact (@lem1763405 term277 term277). Qed.
Lemma lem1763407 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763408 : term291 = term277.
Proof. exact (EQ_MP (@lem1763407) (@lem940073)). Qed.
Lemma lem1763409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763410 : term289 = term9.
Proof. exact (MK_COMB (@lem1763409) (@lem1763408)). Qed.
Lemma lem1763411 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763412 : term309 = term19.
Proof. exact (MK_COMB (@lem1763411) (@lem1763410)). Qed.
Lemma lem1763413 : term308 = term19.
Proof. exact (TRANS (@lem1763406) (@lem1763412)). Qed.
Lemma lem1763414 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763415 : term305 = term310.
Proof. exact (MK_COMB (@lem1763414) (@lem1763413)). Qed.
Lemma lem1763416 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763417 : term305 = term19.
Proof. exact (TRANS (@lem1763415) (@lem1763416)). Qed.
Lemma lem1763419 : term304 = term19.
Proof. exact (TRANS (@lem1763403) (@lem1763417)). Qed.
Lemma lem1763420 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763421 : term400 = term401.
Proof. exact (MK_COMB (@lem1763420) (@lem1763419)). Qed.
Lemma lem1763422 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1763424 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763425 : term288 = term289.
Proof. exact (@lem1763424 term277 term277). Qed.
Lemma lem1763426 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763427 : term291 = term277.
Proof. exact (EQ_MP (@lem1763426) (@lem940073)). Qed.
Lemma lem1763428 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763429 : term289 = term9.
Proof. exact (MK_COMB (@lem1763428) (@lem1763427)). Qed.
Lemma lem1763430 : term288 = term9.
Proof. exact (TRANS (@lem1763425) (@lem1763429)). Qed.
Lemma lem1763431 : term401 = term9.
Proof. exact (TRANS (@lem1763422) (@lem1763430)). Qed.
Lemma lem1763432 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1763433 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1763432) (@lem1763431)). Qed.
Lemma lem1763434 : term400 = term9.
Proof. exact (EQ_MP (@lem1763433) (@lem1763421)). Qed.
Lemma lem1763435 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763436 : term403 = term294.
Proof. exact (MK_COMB (@lem1763435) (@lem1763434)). Qed.
Lemma lem1763437 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763438 : term404 = term295.
Proof. exact (MK_COMB (@lem1763436) (@lem1763437)). Qed.
Lemma lem1763439 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763440 : term311 = term312.
Proof. exact (MK_COMB (@lem1763439) (@lem1763419)). Qed.
Lemma lem1763441 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763442 : term303 = term313.
Proof. exact (MK_COMB (@lem1763440) (@lem1763441)). Qed.
Lemma lem1763443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763444 : term405 = term406.
Proof. exact (MK_COMB (@lem1763443) (@lem1763442)). Qed.
Lemma lem1763445 : term399 = term407.
Proof. exact (MK_COMB (@lem1763444) (@lem1763438)). Qed.
Lemma lem1763446 : term105 = term407.
Proof. exact (TRANS (@lem1763397) (@lem1763445)). Qed.
Lemma lem1763447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763448 : term88 = term355.
Proof. exact (MK_COMB (@lem1763447) (@lem1763396)). Qed.
Lemma lem1763449 : term106 = term408.
Proof. exact (MK_COMB (@lem1763448) (@lem1763446)). Qed.
Lemma lem1763450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763451 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1763450) (@lem1763368 x)). Qed.
Lemma lem1763452 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1763451 x) (@lem1763449)). Qed.
Lemma lem1763453 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1763459 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1763464 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1763466 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1763459 x) (@lem1763464 x)). Qed.
Lemma lem1763467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763468 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1763467) (@lem1763466 x)). Qed.
Lemma lem1763469 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763470 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1763468 x) (@lem1763469)). Qed.
Lemma lem1763471 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1763453 x) (@lem1763470 x)). Qed.
Lemma lem1763472 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1763478 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1763480 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763481 : term276 = term14.
Proof. exact (@lem1763480 term277). Qed.
Lemma lem1763482 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1763483 : term365 = term366.
Proof. exact (MK_COMB (@lem1763482) (@lem1763481)). Qed.
Lemma lem1763484 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1763485 : term365 = term19.
Proof. exact (TRANS (@lem1763483) (@lem1763484)). Qed.
Lemma lem1763487 : term364 = term19.
Proof. exact (TRANS (@lem1763478) (@lem1763485)). Qed.
Lemma lem1763488 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763489 : term367 = term312.
Proof. exact (MK_COMB (@lem1763488) (@lem1763487)). Qed.
Lemma lem1763490 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763491 : term363 = term313.
Proof. exact (MK_COMB (@lem1763489) (@lem1763490)). Qed.
Lemma lem1763492 : term158 = term313.
Proof. exact (TRANS (@lem1763472) (@lem1763491)). Qed.
Lemma lem1763493 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1763499 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1763501 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763502 : term288 = term289.
Proof. exact (@lem1763501 term277 term277). Qed.
Lemma lem1763503 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763504 : term291 = term277.
Proof. exact (EQ_MP (@lem1763503) (@lem940073)). Qed.
Lemma lem1763505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763506 : term289 = term9.
Proof. exact (MK_COMB (@lem1763505) (@lem1763504)). Qed.
Lemma lem1763507 : term288 = term9.
Proof. exact (TRANS (@lem1763502) (@lem1763506)). Qed.
Lemma lem1763508 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763509 : term370 = term372.
Proof. exact (MK_COMB (@lem1763508) (@lem1763507)). Qed.
Lemma lem1763510 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1763511 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1763512 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1763513 : term332 = term333.
Proof. exact (EQ_MP (@lem1763512) (@lem1763511)). Qed.
Lemma lem1763514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763515 : term334 = term335.
Proof. exact (MK_COMB (@lem1763514) (@lem1763513)). Qed.
Lemma lem1763516 : term372 = term335.
Proof. exact (TRANS (@lem1763510) (@lem1763515)). Qed.
Lemma lem1763517 : term370 = term335.
Proof. exact (TRANS (@lem1763509) (@lem1763516)). Qed.
Lemma lem1763519 : term369 = term335.
Proof. exact (TRANS (@lem1763499) (@lem1763517)). Qed.
Lemma lem1763520 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763521 : term373 = term336.
Proof. exact (MK_COMB (@lem1763520) (@lem1763519)). Qed.
Lemma lem1763522 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1763524 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763525 : term374 = term375.
Proof. exact (@lem1763524 term277 term333). Qed.
Lemma lem1763526 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1763527 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1763528 : term342 = term333.
Proof. exact (EQ_MP (@lem1763527) (@lem1763526)). Qed.
Lemma lem1763529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763530 : term340 = term335.
Proof. exact (MK_COMB (@lem1763529) (@lem1763528)). Qed.
Lemma lem1763531 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763532 : term375 = term336.
Proof. exact (MK_COMB (@lem1763531) (@lem1763530)). Qed.
Lemma lem1763533 : term374 = term336.
Proof. exact (TRANS (@lem1763525) (@lem1763532)). Qed.
Lemma lem1763534 : term336 = term336.
Proof. exact (TRANS (@lem1763522) (@lem1763533)). Qed.
Lemma lem1763535 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1763536 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1763535) (@lem1763534)). Qed.
Lemma lem1763537 : term373 = term336.
Proof. exact (EQ_MP (@lem1763536) (@lem1763521)). Qed.
Lemma lem1763538 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763539 : term377 = term349.
Proof. exact (MK_COMB (@lem1763538) (@lem1763537)). Qed.
Lemma lem1763540 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763541 : term378 = term351.
Proof. exact (MK_COMB (@lem1763539) (@lem1763540)). Qed.
Lemma lem1763542 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763543 : term379 = term345.
Proof. exact (MK_COMB (@lem1763542) (@lem1763519)). Qed.
Lemma lem1763544 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763545 : term380 = term347.
Proof. exact (MK_COMB (@lem1763543) (@lem1763544)). Qed.
Lemma lem1763546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763547 : term381 = term382.
Proof. exact (MK_COMB (@lem1763546) (@lem1763545)). Qed.
Lemma lem1763548 : term368 = term383.
Proof. exact (MK_COMB (@lem1763547) (@lem1763541)). Qed.
Lemma lem1763549 : term160 = term383.
Proof. exact (TRANS (@lem1763493) (@lem1763548)). Qed.
Lemma lem1763550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763551 : term159 = term384.
Proof. exact (MK_COMB (@lem1763550) (@lem1763492)). Qed.
Lemma lem1763552 : term161 = term385.
Proof. exact (MK_COMB (@lem1763551) (@lem1763549)). Qed.
Lemma lem1763553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763554 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1763553) (@lem1763471 x)). Qed.
Lemma lem1763555 (x : real) : (term205 x) = (term387 x).
Proof. exact (MK_COMB (@lem1763554 x) (@lem1763552)). Qed.
Lemma lem1763556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763557 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1763556) (@lem1763452 x)). Qed.
Lemma lem1763558 (x : real) : (term209 x) = (term411 x).
Proof. exact (MK_COMB (@lem1763557 x) (@lem1763555 x)). Qed.
Lemma lem1763559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763560 : term153 = term412.
Proof. exact (MK_COMB (@lem1763559) (@lem1763347)). Qed.
Lemma lem1763561 (x : real) : (term210 x) = (term413 x).
Proof. exact (MK_COMB (@lem1763560) (@lem1763558 x)). Qed.
Lemma lem1763562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763563 (x : real) : (term208 x) = (term414 x).
Proof. exact (MK_COMB (@lem1763562) (@lem1763326 x)). Qed.
Lemma lem1763564 (x : real) : (term211 x) = (term415 x).
Proof. exact (MK_COMB (@lem1763563 x) (@lem1763561 x)). Qed.
Lemma lem1763565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763566 (x : real) : (term195 x) = (term416 x).
Proof. exact (MK_COMB (@lem1763565) (@lem1763075 x)). Qed.
Lemma lem1763567 (x : real) : (term212 x) = (term417 x).
Proof. exact (MK_COMB (@lem1763566 x) (@lem1763564 x)). Qed.
Lemma lem1763568 (x : real) : (term418 x) = (term419 x).
Proof. exact (@lem1483531 x term14). Qed.
Lemma lem1763574 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1763576 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763577 : term276 = term14.
Proof. exact (@lem1763576 term277). Qed.
Lemma lem1763578 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1763579 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1763578 x) (@lem1763577)). Qed.
Lemma lem1763580 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1763581 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1763579 x) (@lem1763580 x)). Qed.
Lemma lem1763583 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1763574 x) (@lem1763581 x)). Qed.
Lemma lem1763584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763585 (x : real) : (term420 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1763584) (@lem1763583 x)). Qed.
Lemma lem1763586 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763587 (x : real) : (term419 x) = (term421 x).
Proof. exact (MK_COMB (@lem1763585 x) (@lem1763586)). Qed.
Lemma lem1763588 (x : real) : (term418 x) = (term421 x).
Proof. exact (TRANS (@lem1763568 x) (@lem1763587 x)). Qed.
Lemma lem1763589 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1763595 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763597 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763598 : term308 = term309.
Proof. exact (@lem1763597 term277 term277). Qed.
Lemma lem1763599 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763600 : term291 = term277.
Proof. exact (EQ_MP (@lem1763599) (@lem940073)). Qed.
Lemma lem1763601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763602 : term289 = term9.
Proof. exact (MK_COMB (@lem1763601) (@lem1763600)). Qed.
Lemma lem1763603 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763604 : term309 = term19.
Proof. exact (MK_COMB (@lem1763603) (@lem1763602)). Qed.
Lemma lem1763605 : term308 = term19.
Proof. exact (TRANS (@lem1763598) (@lem1763604)). Qed.
Lemma lem1763606 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763607 : term305 = term310.
Proof. exact (MK_COMB (@lem1763606) (@lem1763605)). Qed.
Lemma lem1763608 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763609 : term305 = term19.
Proof. exact (TRANS (@lem1763607) (@lem1763608)). Qed.
Lemma lem1763611 : term304 = term19.
Proof. exact (TRANS (@lem1763595) (@lem1763609)). Qed.
Lemma lem1763612 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763613 : term311 = term312.
Proof. exact (MK_COMB (@lem1763612) (@lem1763611)). Qed.
Lemma lem1763614 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763615 : term303 = term313.
Proof. exact (MK_COMB (@lem1763613) (@lem1763614)). Qed.
Lemma lem1763616 : term90 = term313.
Proof. exact (TRANS (@lem1763589) (@lem1763615)). Qed.
Lemma lem1763617 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1763623 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1763625 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763626 : term276 = term14.
Proof. exact (@lem1763625 term277). Qed.
Lemma lem1763627 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1763628 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1763627 x) (@lem1763626)). Qed.
Lemma lem1763629 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1763630 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1763628 x) (@lem1763629 x)). Qed.
Lemma lem1763632 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1763623 x) (@lem1763630 x)). Qed.
Lemma lem1763633 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763634 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1763633) (@lem1763632 x)). Qed.
Lemma lem1763635 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763636 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1763634 x) (@lem1763635)). Qed.
Lemma lem1763637 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1763617 x) (@lem1763636 x)). Qed.
Lemma lem1763638 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1763644 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763646 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763647 : term308 = term309.
Proof. exact (@lem1763646 term277 term277). Qed.
Lemma lem1763648 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763649 : term291 = term277.
Proof. exact (EQ_MP (@lem1763648) (@lem940073)). Qed.
Lemma lem1763650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763651 : term289 = term9.
Proof. exact (MK_COMB (@lem1763650) (@lem1763649)). Qed.
Lemma lem1763652 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763653 : term309 = term19.
Proof. exact (MK_COMB (@lem1763652) (@lem1763651)). Qed.
Lemma lem1763654 : term308 = term19.
Proof. exact (TRANS (@lem1763647) (@lem1763653)). Qed.
Lemma lem1763655 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763656 : term305 = term310.
Proof. exact (MK_COMB (@lem1763655) (@lem1763654)). Qed.
Lemma lem1763657 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763658 : term305 = term19.
Proof. exact (TRANS (@lem1763656) (@lem1763657)). Qed.
Lemma lem1763660 : term304 = term19.
Proof. exact (TRANS (@lem1763644) (@lem1763658)). Qed.
Lemma lem1763661 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763662 : term321 = term322.
Proof. exact (MK_COMB (@lem1763661) (@lem1763660)). Qed.
Lemma lem1763663 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763664 : term320 = term323.
Proof. exact (MK_COMB (@lem1763662) (@lem1763663)). Qed.
Lemma lem1763665 : term87 = term323.
Proof. exact (TRANS (@lem1763638) (@lem1763664)). Qed.
Lemma lem1763666 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1763672 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1763674 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763675 : term308 = term309.
Proof. exact (@lem1763674 term277 term277). Qed.
Lemma lem1763676 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763677 : term291 = term277.
Proof. exact (EQ_MP (@lem1763676) (@lem940073)). Qed.
Lemma lem1763678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763679 : term289 = term9.
Proof. exact (MK_COMB (@lem1763678) (@lem1763677)). Qed.
Lemma lem1763680 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763681 : term309 = term19.
Proof. exact (MK_COMB (@lem1763680) (@lem1763679)). Qed.
Lemma lem1763682 : term308 = term19.
Proof. exact (TRANS (@lem1763675) (@lem1763681)). Qed.
Lemma lem1763683 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1763684 : term326 = term328.
Proof. exact (MK_COMB (@lem1763683) (@lem1763682)). Qed.
Lemma lem1763685 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1763686 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1763687 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1763688 : term332 = term333.
Proof. exact (EQ_MP (@lem1763687) (@lem1763686)). Qed.
Lemma lem1763689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763690 : term334 = term335.
Proof. exact (MK_COMB (@lem1763689) (@lem1763688)). Qed.
Lemma lem1763691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763692 : term329 = term336.
Proof. exact (MK_COMB (@lem1763691) (@lem1763690)). Qed.
Lemma lem1763693 : term328 = term336.
Proof. exact (TRANS (@lem1763685) (@lem1763692)). Qed.
Lemma lem1763694 : term326 = term336.
Proof. exact (TRANS (@lem1763684) (@lem1763693)). Qed.
Lemma lem1763696 : term325 = term336.
Proof. exact (TRANS (@lem1763672) (@lem1763694)). Qed.
Lemma lem1763697 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763698 : term337 = term338.
Proof. exact (MK_COMB (@lem1763697) (@lem1763696)). Qed.
Lemma lem1763699 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1763701 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763702 : term339 = term340.
Proof. exact (@lem1763701 term277 term333). Qed.
Lemma lem1763703 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1763704 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1763705 : term342 = term333.
Proof. exact (EQ_MP (@lem1763704) (@lem1763703)). Qed.
Lemma lem1763706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763707 : term340 = term335.
Proof. exact (MK_COMB (@lem1763706) (@lem1763705)). Qed.
Lemma lem1763708 : term339 = term335.
Proof. exact (TRANS (@lem1763702) (@lem1763707)). Qed.
Lemma lem1763709 : term338 = term335.
Proof. exact (TRANS (@lem1763699) (@lem1763708)). Qed.
Lemma lem1763710 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1763711 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1763710) (@lem1763709)). Qed.
Lemma lem1763712 : term337 = term335.
Proof. exact (EQ_MP (@lem1763711) (@lem1763698)). Qed.
Lemma lem1763713 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763714 : term344 = term345.
Proof. exact (MK_COMB (@lem1763713) (@lem1763712)). Qed.
Lemma lem1763715 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763716 : term346 = term347.
Proof. exact (MK_COMB (@lem1763714) (@lem1763715)). Qed.
Lemma lem1763717 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763718 : term348 = term349.
Proof. exact (MK_COMB (@lem1763717) (@lem1763696)). Qed.
Lemma lem1763719 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763720 : term350 = term351.
Proof. exact (MK_COMB (@lem1763718) (@lem1763719)). Qed.
Lemma lem1763721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763722 : term352 = term353.
Proof. exact (MK_COMB (@lem1763721) (@lem1763720)). Qed.
Lemma lem1763723 : term324 = term354.
Proof. exact (MK_COMB (@lem1763722) (@lem1763716)). Qed.
Lemma lem1763724 : term118 = term354.
Proof. exact (TRANS (@lem1763666) (@lem1763723)). Qed.
Lemma lem1763725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763726 : term88 = term355.
Proof. exact (MK_COMB (@lem1763725) (@lem1763665)). Qed.
Lemma lem1763727 : term119 = term356.
Proof. exact (MK_COMB (@lem1763726) (@lem1763724)). Qed.
Lemma lem1763728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763729 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1763728) (@lem1763637 x)). Qed.
Lemma lem1763730 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1763729 x) (@lem1763727)). Qed.
Lemma lem1763731 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1763737 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1763742 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1763744 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1763737 x) (@lem1763742 x)). Qed.
Lemma lem1763745 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763746 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1763745) (@lem1763744 x)). Qed.
Lemma lem1763747 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763748 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1763746 x) (@lem1763747)). Qed.
Lemma lem1763749 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1763731 x) (@lem1763748 x)). Qed.
Lemma lem1763750 : term132 = term422.
Proof. exact (@lem1483554 term9 term14). Qed.
Lemma lem1763756 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1763758 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763759 : term276 = term14.
Proof. exact (@lem1763758 term277). Qed.
Lemma lem1763760 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763761 : term394 = term395.
Proof. exact (MK_COMB (@lem1763760) (@lem1763759)). Qed.
Lemma lem1763762 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1763763 : term394 = term9.
Proof. exact (TRANS (@lem1763761) (@lem1763762)). Qed.
Lemma lem1763765 : term393 = term9.
Proof. exact (TRANS (@lem1763756) (@lem1763763)). Qed.
Lemma lem1763766 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763767 : term423 = term19.
Proof. exact (MK_COMB (@lem1763766) (@lem1763765)). Qed.
Lemma lem1763768 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1763770 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763771 : term308 = term309.
Proof. exact (@lem1763770 term277 term277). Qed.
Lemma lem1763772 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763773 : term291 = term277.
Proof. exact (EQ_MP (@lem1763772) (@lem940073)). Qed.
Lemma lem1763774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763775 : term289 = term9.
Proof. exact (MK_COMB (@lem1763774) (@lem1763773)). Qed.
Lemma lem1763776 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763777 : term309 = term19.
Proof. exact (MK_COMB (@lem1763776) (@lem1763775)). Qed.
Lemma lem1763778 : term308 = term19.
Proof. exact (TRANS (@lem1763771) (@lem1763777)). Qed.
Lemma lem1763779 : term19 = term19.
Proof. exact (TRANS (@lem1763768) (@lem1763778)). Qed.
Lemma lem1763780 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem1763781 : (term423 = term19) = (term423 = term19).
Proof. exact (MK_COMB (@lem1763780) (@lem1763779)). Qed.
Lemma lem1763782 : term423 = term19.
Proof. exact (EQ_MP (@lem1763781) (@lem1763767)). Qed.
Lemma lem1763783 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763784 : term425 = term312.
Proof. exact (MK_COMB (@lem1763783) (@lem1763782)). Qed.
Lemma lem1763785 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763786 : term426 = term313.
Proof. exact (MK_COMB (@lem1763784) (@lem1763785)). Qed.
Lemma lem1763787 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763788 : term427 = term294.
Proof. exact (MK_COMB (@lem1763787) (@lem1763765)). Qed.
Lemma lem1763789 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763790 : term428 = term295.
Proof. exact (MK_COMB (@lem1763788) (@lem1763789)). Qed.
Lemma lem1763791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763792 : term429 = term430.
Proof. exact (MK_COMB (@lem1763791) (@lem1763790)). Qed.
Lemma lem1763793 : term422 = term431.
Proof. exact (MK_COMB (@lem1763792) (@lem1763786)). Qed.
Lemma lem1763794 : term132 = term431.
Proof. exact (TRANS (@lem1763750) (@lem1763793)). Qed.
Lemma lem1763795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763796 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1763795) (@lem1763749 x)). Qed.
Lemma lem1763797 (x : real) : (term247 x) = (term432 x).
Proof. exact (MK_COMB (@lem1763796 x) (@lem1763794)). Qed.
Lemma lem1763798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763799 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1763798) (@lem1763730 x)). Qed.
Lemma lem1763800 (x : real) : (term248 x) = (term433 x).
Proof. exact (MK_COMB (@lem1763799 x) (@lem1763797 x)). Qed.
Lemma lem1763801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763802 : term147 = term384.
Proof. exact (MK_COMB (@lem1763801) (@lem1763616)). Qed.
Lemma lem1763803 (x : real) : (term249 x) = (term434 x).
Proof. exact (MK_COMB (@lem1763802) (@lem1763800 x)). Qed.
Lemma lem1763804 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1763810 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1763812 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763813 : term276 = term14.
Proof. exact (@lem1763812 term277). Qed.
Lemma lem1763814 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763815 : term394 = term395.
Proof. exact (MK_COMB (@lem1763814) (@lem1763813)). Qed.
Lemma lem1763816 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1763817 : term394 = term9.
Proof. exact (TRANS (@lem1763815) (@lem1763816)). Qed.
Lemma lem1763819 : term393 = term9.
Proof. exact (TRANS (@lem1763810) (@lem1763817)). Qed.
Lemma lem1763820 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763821 : term396 = term397.
Proof. exact (MK_COMB (@lem1763820) (@lem1763819)). Qed.
Lemma lem1763822 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763823 : term392 = term398.
Proof. exact (MK_COMB (@lem1763821) (@lem1763822)). Qed.
Lemma lem1763824 : term391 = term398.
Proof. exact (TRANS (@lem1763804) (@lem1763823)). Qed.
Lemma lem1763825 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1763831 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1763833 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763834 : term276 = term14.
Proof. exact (@lem1763833 term277). Qed.
Lemma lem1763835 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1763836 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1763835 x) (@lem1763834)). Qed.
Lemma lem1763837 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1763838 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1763836 x) (@lem1763837 x)). Qed.
Lemma lem1763840 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1763831 x) (@lem1763838 x)). Qed.
Lemma lem1763841 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763842 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1763841) (@lem1763840 x)). Qed.
Lemma lem1763843 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763844 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1763842 x) (@lem1763843)). Qed.
Lemma lem1763845 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1763825 x) (@lem1763844 x)). Qed.
Lemma lem1763846 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1763852 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763854 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763855 : term308 = term309.
Proof. exact (@lem1763854 term277 term277). Qed.
Lemma lem1763856 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763857 : term291 = term277.
Proof. exact (EQ_MP (@lem1763856) (@lem940073)). Qed.
Lemma lem1763858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763859 : term289 = term9.
Proof. exact (MK_COMB (@lem1763858) (@lem1763857)). Qed.
Lemma lem1763860 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763861 : term309 = term19.
Proof. exact (MK_COMB (@lem1763860) (@lem1763859)). Qed.
Lemma lem1763862 : term308 = term19.
Proof. exact (TRANS (@lem1763855) (@lem1763861)). Qed.
Lemma lem1763863 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763864 : term305 = term310.
Proof. exact (MK_COMB (@lem1763863) (@lem1763862)). Qed.
Lemma lem1763865 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763866 : term305 = term19.
Proof. exact (TRANS (@lem1763864) (@lem1763865)). Qed.
Lemma lem1763868 : term304 = term19.
Proof. exact (TRANS (@lem1763852) (@lem1763866)). Qed.
Lemma lem1763869 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763870 : term321 = term322.
Proof. exact (MK_COMB (@lem1763869) (@lem1763868)). Qed.
Lemma lem1763871 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763872 : term320 = term323.
Proof. exact (MK_COMB (@lem1763870) (@lem1763871)). Qed.
Lemma lem1763873 : term87 = term323.
Proof. exact (TRANS (@lem1763846) (@lem1763872)). Qed.
Lemma lem1763874 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1763880 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1763882 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763883 : term308 = term309.
Proof. exact (@lem1763882 term277 term277). Qed.
Lemma lem1763884 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763885 : term291 = term277.
Proof. exact (EQ_MP (@lem1763884) (@lem940073)). Qed.
Lemma lem1763886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763887 : term289 = term9.
Proof. exact (MK_COMB (@lem1763886) (@lem1763885)). Qed.
Lemma lem1763888 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763889 : term309 = term19.
Proof. exact (MK_COMB (@lem1763888) (@lem1763887)). Qed.
Lemma lem1763890 : term308 = term19.
Proof. exact (TRANS (@lem1763883) (@lem1763889)). Qed.
Lemma lem1763891 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1763892 : term305 = term310.
Proof. exact (MK_COMB (@lem1763891) (@lem1763890)). Qed.
Lemma lem1763893 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1763894 : term305 = term19.
Proof. exact (TRANS (@lem1763892) (@lem1763893)). Qed.
Lemma lem1763896 : term304 = term19.
Proof. exact (TRANS (@lem1763880) (@lem1763894)). Qed.
Lemma lem1763897 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763898 : term400 = term401.
Proof. exact (MK_COMB (@lem1763897) (@lem1763896)). Qed.
Lemma lem1763899 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1763901 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1763902 : term288 = term289.
Proof. exact (@lem1763901 term277 term277). Qed.
Lemma lem1763903 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763904 : term291 = term277.
Proof. exact (EQ_MP (@lem1763903) (@lem940073)). Qed.
Lemma lem1763905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763906 : term289 = term9.
Proof. exact (MK_COMB (@lem1763905) (@lem1763904)). Qed.
Lemma lem1763907 : term288 = term9.
Proof. exact (TRANS (@lem1763902) (@lem1763906)). Qed.
Lemma lem1763908 : term401 = term9.
Proof. exact (TRANS (@lem1763899) (@lem1763907)). Qed.
Lemma lem1763909 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1763910 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1763909) (@lem1763908)). Qed.
Lemma lem1763911 : term400 = term9.
Proof. exact (EQ_MP (@lem1763910) (@lem1763898)). Qed.
Lemma lem1763912 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763913 : term403 = term294.
Proof. exact (MK_COMB (@lem1763912) (@lem1763911)). Qed.
Lemma lem1763914 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763915 : term404 = term295.
Proof. exact (MK_COMB (@lem1763913) (@lem1763914)). Qed.
Lemma lem1763916 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763917 : term311 = term312.
Proof. exact (MK_COMB (@lem1763916) (@lem1763896)). Qed.
Lemma lem1763918 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763919 : term303 = term313.
Proof. exact (MK_COMB (@lem1763917) (@lem1763918)). Qed.
Lemma lem1763920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763921 : term405 = term406.
Proof. exact (MK_COMB (@lem1763920) (@lem1763919)). Qed.
Lemma lem1763922 : term399 = term407.
Proof. exact (MK_COMB (@lem1763921) (@lem1763915)). Qed.
Lemma lem1763923 : term105 = term407.
Proof. exact (TRANS (@lem1763874) (@lem1763922)). Qed.
Lemma lem1763924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763925 : term88 = term355.
Proof. exact (MK_COMB (@lem1763924) (@lem1763873)). Qed.
Lemma lem1763926 : term106 = term408.
Proof. exact (MK_COMB (@lem1763925) (@lem1763923)). Qed.
Lemma lem1763927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763928 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1763927) (@lem1763845 x)). Qed.
Lemma lem1763929 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1763928 x) (@lem1763926)). Qed.
Lemma lem1763930 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1763936 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1763941 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1763943 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1763936 x) (@lem1763941 x)). Qed.
Lemma lem1763944 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1763945 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1763944) (@lem1763943 x)). Qed.
Lemma lem1763946 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763947 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1763945 x) (@lem1763946)). Qed.
Lemma lem1763948 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1763930 x) (@lem1763947 x)). Qed.
Lemma lem1763949 : term132 = term422.
Proof. exact (@lem1483554 term9 term14). Qed.
Lemma lem1763955 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1763957 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1763958 : term276 = term14.
Proof. exact (@lem1763957 term277). Qed.
Lemma lem1763959 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1763960 : term394 = term395.
Proof. exact (MK_COMB (@lem1763959) (@lem1763958)). Qed.
Lemma lem1763961 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1763962 : term394 = term9.
Proof. exact (TRANS (@lem1763960) (@lem1763961)). Qed.
Lemma lem1763964 : term393 = term9.
Proof. exact (TRANS (@lem1763955) (@lem1763962)). Qed.
Lemma lem1763965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763966 : term423 = term19.
Proof. exact (MK_COMB (@lem1763965) (@lem1763964)). Qed.
Lemma lem1763967 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1763969 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1763970 : term308 = term309.
Proof. exact (@lem1763969 term277 term277). Qed.
Lemma lem1763971 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1763972 : term291 = term277.
Proof. exact (EQ_MP (@lem1763971) (@lem940073)). Qed.
Lemma lem1763973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1763974 : term289 = term9.
Proof. exact (MK_COMB (@lem1763973) (@lem1763972)). Qed.
Lemma lem1763975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1763976 : term309 = term19.
Proof. exact (MK_COMB (@lem1763975) (@lem1763974)). Qed.
Lemma lem1763977 : term308 = term19.
Proof. exact (TRANS (@lem1763970) (@lem1763976)). Qed.
Lemma lem1763978 : term19 = term19.
Proof. exact (TRANS (@lem1763967) (@lem1763977)). Qed.
Lemma lem1763979 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem1763980 : (term423 = term19) = (term423 = term19).
Proof. exact (MK_COMB (@lem1763979) (@lem1763978)). Qed.
Lemma lem1763981 : term423 = term19.
Proof. exact (EQ_MP (@lem1763980) (@lem1763966)). Qed.
Lemma lem1763982 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763983 : term425 = term312.
Proof. exact (MK_COMB (@lem1763982) (@lem1763981)). Qed.
Lemma lem1763984 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763985 : term426 = term313.
Proof. exact (MK_COMB (@lem1763983) (@lem1763984)). Qed.
Lemma lem1763986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1763987 : term427 = term294.
Proof. exact (MK_COMB (@lem1763986) (@lem1763964)). Qed.
Lemma lem1763988 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1763989 : term428 = term295.
Proof. exact (MK_COMB (@lem1763987) (@lem1763988)). Qed.
Lemma lem1763990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763991 : term429 = term430.
Proof. exact (MK_COMB (@lem1763990) (@lem1763989)). Qed.
Lemma lem1763992 : term422 = term431.
Proof. exact (MK_COMB (@lem1763991) (@lem1763985)). Qed.
Lemma lem1763993 : term132 = term431.
Proof. exact (TRANS (@lem1763949) (@lem1763992)). Qed.
Lemma lem1763994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1763995 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1763994) (@lem1763948 x)). Qed.
Lemma lem1763996 (x : real) : (term247 x) = (term432 x).
Proof. exact (MK_COMB (@lem1763995 x) (@lem1763993)). Qed.
Lemma lem1763997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1763998 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1763997) (@lem1763929 x)). Qed.
Lemma lem1763999 (x : real) : (term251 x) = (term435 x).
Proof. exact (MK_COMB (@lem1763998 x) (@lem1763996 x)). Qed.
Lemma lem1764000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764001 : term153 = term412.
Proof. exact (MK_COMB (@lem1764000) (@lem1763824)). Qed.
Lemma lem1764002 (x : real) : (term252 x) = (term436 x).
Proof. exact (MK_COMB (@lem1764001) (@lem1763999 x)). Qed.
Lemma lem1764003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764004 (x : real) : (term250 x) = (term437 x).
Proof. exact (MK_COMB (@lem1764003) (@lem1763803 x)). Qed.
Lemma lem1764005 (x : real) : (term253 x) = (term438 x).
Proof. exact (MK_COMB (@lem1764004 x) (@lem1764002 x)). Qed.
Lemma lem1764006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764007 (x : real) : (term228 x) = (term439 x).
Proof. exact (MK_COMB (@lem1764006) (@lem1763588 x)). Qed.
Lemma lem1764008 (x : real) : (term254 x) = (term440 x).
Proof. exact (MK_COMB (@lem1764007 x) (@lem1764005 x)). Qed.
Lemma lem1764009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764010 (x : real) : (term213 x) = (term441 x).
Proof. exact (MK_COMB (@lem1764009) (@lem1763567 x)). Qed.
Lemma lem1764011 (x : real) : (term255 x) = (term442 x).
Proof. exact (MK_COMB (@lem1764010 x) (@lem1764008 x)). Qed.
Lemma lem1764012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764013 : term231 = term443.
Proof. exact (MK_COMB (@lem1764012) (@lem1763056)). Qed.
Lemma lem1764014 (x : real) : (term256 x) = (term444 x).
Proof. exact (MK_COMB (@lem1764013) (@lem1764011 x)). Qed.
Lemma lem1764015 : term445 = term446.
Proof. exact (@lem1483531 term19 term14). Qed.
Lemma lem1764021 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1764023 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764024 : term276 = term14.
Proof. exact (@lem1764023 term277). Qed.
Lemma lem1764025 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1764026 : term365 = term366.
Proof. exact (MK_COMB (@lem1764025) (@lem1764024)). Qed.
Lemma lem1764027 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1764028 : term365 = term19.
Proof. exact (TRANS (@lem1764026) (@lem1764027)). Qed.
Lemma lem1764030 : term364 = term19.
Proof. exact (TRANS (@lem1764021) (@lem1764028)). Qed.
Lemma lem1764031 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764032 : term447 = term322.
Proof. exact (MK_COMB (@lem1764031) (@lem1764030)). Qed.
Lemma lem1764033 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764034 : term446 = term323.
Proof. exact (MK_COMB (@lem1764032) (@lem1764033)). Qed.
Lemma lem1764035 : term445 = term323.
Proof. exact (TRANS (@lem1764015) (@lem1764034)). Qed.
Lemma lem1764036 (x : real) : (term127 x) = (term296 x).
Proof. exact (@lem1483521 term14 x). Qed.
Lemma lem1764042 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1764047 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1764049 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1764042 x) (@lem1764047 x)). Qed.
Lemma lem1764050 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764051 (x : real) : (term300 x) = (term301 x).
Proof. exact (MK_COMB (@lem1764050) (@lem1764049 x)). Qed.
Lemma lem1764052 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764053 (x : real) : (term296 x) = (term302 x).
Proof. exact (MK_COMB (@lem1764051 x) (@lem1764052)). Qed.
Lemma lem1764054 (x : real) : (term127 x) = (term302 x).
Proof. exact (TRANS (@lem1764036 x) (@lem1764053 x)). Qed.
Lemma lem1764055 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1764061 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764063 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764064 : term308 = term309.
Proof. exact (@lem1764063 term277 term277). Qed.
Lemma lem1764065 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764066 : term291 = term277.
Proof. exact (EQ_MP (@lem1764065) (@lem940073)). Qed.
Lemma lem1764067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764068 : term289 = term9.
Proof. exact (MK_COMB (@lem1764067) (@lem1764066)). Qed.
Lemma lem1764069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764070 : term309 = term19.
Proof. exact (MK_COMB (@lem1764069) (@lem1764068)). Qed.
Lemma lem1764071 : term308 = term19.
Proof. exact (TRANS (@lem1764064) (@lem1764070)). Qed.
Lemma lem1764072 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764073 : term305 = term310.
Proof. exact (MK_COMB (@lem1764072) (@lem1764071)). Qed.
Lemma lem1764074 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764075 : term305 = term19.
Proof. exact (TRANS (@lem1764073) (@lem1764074)). Qed.
Lemma lem1764077 : term304 = term19.
Proof. exact (TRANS (@lem1764061) (@lem1764075)). Qed.
Lemma lem1764078 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764079 : term311 = term312.
Proof. exact (MK_COMB (@lem1764078) (@lem1764077)). Qed.
Lemma lem1764080 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764081 : term303 = term313.
Proof. exact (MK_COMB (@lem1764079) (@lem1764080)). Qed.
Lemma lem1764082 : term90 = term313.
Proof. exact (TRANS (@lem1764055) (@lem1764081)). Qed.
Lemma lem1764083 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1764089 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1764091 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764092 : term276 = term14.
Proof. exact (@lem1764091 term277). Qed.
Lemma lem1764093 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1764094 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1764093 x) (@lem1764092)). Qed.
Lemma lem1764095 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1764096 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1764094 x) (@lem1764095 x)). Qed.
Lemma lem1764098 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1764089 x) (@lem1764096 x)). Qed.
Lemma lem1764099 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764100 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1764099) (@lem1764098 x)). Qed.
Lemma lem1764101 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764102 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1764100 x) (@lem1764101)). Qed.
Lemma lem1764103 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1764083 x) (@lem1764102 x)). Qed.
Lemma lem1764104 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1764110 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764112 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764113 : term308 = term309.
Proof. exact (@lem1764112 term277 term277). Qed.
Lemma lem1764114 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764115 : term291 = term277.
Proof. exact (EQ_MP (@lem1764114) (@lem940073)). Qed.
Lemma lem1764116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764117 : term289 = term9.
Proof. exact (MK_COMB (@lem1764116) (@lem1764115)). Qed.
Lemma lem1764118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764119 : term309 = term19.
Proof. exact (MK_COMB (@lem1764118) (@lem1764117)). Qed.
Lemma lem1764120 : term308 = term19.
Proof. exact (TRANS (@lem1764113) (@lem1764119)). Qed.
Lemma lem1764121 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764122 : term305 = term310.
Proof. exact (MK_COMB (@lem1764121) (@lem1764120)). Qed.
Lemma lem1764123 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764124 : term305 = term19.
Proof. exact (TRANS (@lem1764122) (@lem1764123)). Qed.
Lemma lem1764126 : term304 = term19.
Proof. exact (TRANS (@lem1764110) (@lem1764124)). Qed.
Lemma lem1764127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764128 : term321 = term322.
Proof. exact (MK_COMB (@lem1764127) (@lem1764126)). Qed.
Lemma lem1764129 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764130 : term320 = term323.
Proof. exact (MK_COMB (@lem1764128) (@lem1764129)). Qed.
Lemma lem1764131 : term87 = term323.
Proof. exact (TRANS (@lem1764104) (@lem1764130)). Qed.
Lemma lem1764132 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1764138 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1764140 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764141 : term308 = term309.
Proof. exact (@lem1764140 term277 term277). Qed.
Lemma lem1764142 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764143 : term291 = term277.
Proof. exact (EQ_MP (@lem1764142) (@lem940073)). Qed.
Lemma lem1764144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764145 : term289 = term9.
Proof. exact (MK_COMB (@lem1764144) (@lem1764143)). Qed.
Lemma lem1764146 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764147 : term309 = term19.
Proof. exact (MK_COMB (@lem1764146) (@lem1764145)). Qed.
Lemma lem1764148 : term308 = term19.
Proof. exact (TRANS (@lem1764141) (@lem1764147)). Qed.
Lemma lem1764149 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1764150 : term326 = term328.
Proof. exact (MK_COMB (@lem1764149) (@lem1764148)). Qed.
Lemma lem1764151 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1764152 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1764153 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1764154 : term332 = term333.
Proof. exact (EQ_MP (@lem1764153) (@lem1764152)). Qed.
Lemma lem1764155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764156 : term334 = term335.
Proof. exact (MK_COMB (@lem1764155) (@lem1764154)). Qed.
Lemma lem1764157 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764158 : term329 = term336.
Proof. exact (MK_COMB (@lem1764157) (@lem1764156)). Qed.
Lemma lem1764159 : term328 = term336.
Proof. exact (TRANS (@lem1764151) (@lem1764158)). Qed.
Lemma lem1764160 : term326 = term336.
Proof. exact (TRANS (@lem1764150) (@lem1764159)). Qed.
Lemma lem1764162 : term325 = term336.
Proof. exact (TRANS (@lem1764138) (@lem1764160)). Qed.
Lemma lem1764163 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764164 : term337 = term338.
Proof. exact (MK_COMB (@lem1764163) (@lem1764162)). Qed.
Lemma lem1764165 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1764167 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764168 : term339 = term340.
Proof. exact (@lem1764167 term277 term333). Qed.
Lemma lem1764169 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1764170 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1764171 : term342 = term333.
Proof. exact (EQ_MP (@lem1764170) (@lem1764169)). Qed.
Lemma lem1764172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764173 : term340 = term335.
Proof. exact (MK_COMB (@lem1764172) (@lem1764171)). Qed.
Lemma lem1764174 : term339 = term335.
Proof. exact (TRANS (@lem1764168) (@lem1764173)). Qed.
Lemma lem1764175 : term338 = term335.
Proof. exact (TRANS (@lem1764165) (@lem1764174)). Qed.
Lemma lem1764176 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1764177 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1764176) (@lem1764175)). Qed.
Lemma lem1764178 : term337 = term335.
Proof. exact (EQ_MP (@lem1764177) (@lem1764164)). Qed.
Lemma lem1764179 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764180 : term344 = term345.
Proof. exact (MK_COMB (@lem1764179) (@lem1764178)). Qed.
Lemma lem1764181 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764182 : term346 = term347.
Proof. exact (MK_COMB (@lem1764180) (@lem1764181)). Qed.
Lemma lem1764183 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764184 : term348 = term349.
Proof. exact (MK_COMB (@lem1764183) (@lem1764162)). Qed.
Lemma lem1764185 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764186 : term350 = term351.
Proof. exact (MK_COMB (@lem1764184) (@lem1764185)). Qed.
Lemma lem1764187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764188 : term352 = term353.
Proof. exact (MK_COMB (@lem1764187) (@lem1764186)). Qed.
Lemma lem1764189 : term324 = term354.
Proof. exact (MK_COMB (@lem1764188) (@lem1764182)). Qed.
Lemma lem1764190 : term118 = term354.
Proof. exact (TRANS (@lem1764132) (@lem1764189)). Qed.
Lemma lem1764191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764192 : term88 = term355.
Proof. exact (MK_COMB (@lem1764191) (@lem1764131)). Qed.
Lemma lem1764193 : term119 = term356.
Proof. exact (MK_COMB (@lem1764192) (@lem1764190)). Qed.
Lemma lem1764194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764195 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1764194) (@lem1764103 x)). Qed.
Lemma lem1764196 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1764195 x) (@lem1764193)). Qed.
Lemma lem1764197 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1764203 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1764208 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1764210 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1764203 x) (@lem1764208 x)). Qed.
Lemma lem1764211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764212 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1764211) (@lem1764210 x)). Qed.
Lemma lem1764213 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764214 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1764212 x) (@lem1764213)). Qed.
Lemma lem1764215 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1764197 x) (@lem1764214 x)). Qed.
Lemma lem1764216 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1764222 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1764224 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764225 : term276 = term14.
Proof. exact (@lem1764224 term277). Qed.
Lemma lem1764226 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1764227 : term365 = term366.
Proof. exact (MK_COMB (@lem1764226) (@lem1764225)). Qed.
Lemma lem1764228 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1764229 : term365 = term19.
Proof. exact (TRANS (@lem1764227) (@lem1764228)). Qed.
Lemma lem1764231 : term364 = term19.
Proof. exact (TRANS (@lem1764222) (@lem1764229)). Qed.
Lemma lem1764232 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764233 : term367 = term312.
Proof. exact (MK_COMB (@lem1764232) (@lem1764231)). Qed.
Lemma lem1764234 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764235 : term363 = term313.
Proof. exact (MK_COMB (@lem1764233) (@lem1764234)). Qed.
Lemma lem1764236 : term158 = term313.
Proof. exact (TRANS (@lem1764216) (@lem1764235)). Qed.
Lemma lem1764237 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1764243 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1764245 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764246 : term288 = term289.
Proof. exact (@lem1764245 term277 term277). Qed.
Lemma lem1764247 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764248 : term291 = term277.
Proof. exact (EQ_MP (@lem1764247) (@lem940073)). Qed.
Lemma lem1764249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764250 : term289 = term9.
Proof. exact (MK_COMB (@lem1764249) (@lem1764248)). Qed.
Lemma lem1764251 : term288 = term9.
Proof. exact (TRANS (@lem1764246) (@lem1764250)). Qed.
Lemma lem1764252 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1764253 : term370 = term372.
Proof. exact (MK_COMB (@lem1764252) (@lem1764251)). Qed.
Lemma lem1764254 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1764255 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1764256 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1764257 : term332 = term333.
Proof. exact (EQ_MP (@lem1764256) (@lem1764255)). Qed.
Lemma lem1764258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764259 : term334 = term335.
Proof. exact (MK_COMB (@lem1764258) (@lem1764257)). Qed.
Lemma lem1764260 : term372 = term335.
Proof. exact (TRANS (@lem1764254) (@lem1764259)). Qed.
Lemma lem1764261 : term370 = term335.
Proof. exact (TRANS (@lem1764253) (@lem1764260)). Qed.
Lemma lem1764263 : term369 = term335.
Proof. exact (TRANS (@lem1764243) (@lem1764261)). Qed.
Lemma lem1764264 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764265 : term373 = term336.
Proof. exact (MK_COMB (@lem1764264) (@lem1764263)). Qed.
Lemma lem1764266 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1764268 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764269 : term374 = term375.
Proof. exact (@lem1764268 term277 term333). Qed.
Lemma lem1764270 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1764271 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1764272 : term342 = term333.
Proof. exact (EQ_MP (@lem1764271) (@lem1764270)). Qed.
Lemma lem1764273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764274 : term340 = term335.
Proof. exact (MK_COMB (@lem1764273) (@lem1764272)). Qed.
Lemma lem1764275 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764276 : term375 = term336.
Proof. exact (MK_COMB (@lem1764275) (@lem1764274)). Qed.
Lemma lem1764277 : term374 = term336.
Proof. exact (TRANS (@lem1764269) (@lem1764276)). Qed.
Lemma lem1764278 : term336 = term336.
Proof. exact (TRANS (@lem1764266) (@lem1764277)). Qed.
Lemma lem1764279 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1764280 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1764279) (@lem1764278)). Qed.
Lemma lem1764281 : term373 = term336.
Proof. exact (EQ_MP (@lem1764280) (@lem1764265)). Qed.
Lemma lem1764282 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764283 : term377 = term349.
Proof. exact (MK_COMB (@lem1764282) (@lem1764281)). Qed.
Lemma lem1764284 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764285 : term378 = term351.
Proof. exact (MK_COMB (@lem1764283) (@lem1764284)). Qed.
Lemma lem1764286 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764287 : term379 = term345.
Proof. exact (MK_COMB (@lem1764286) (@lem1764263)). Qed.
Lemma lem1764288 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764289 : term380 = term347.
Proof. exact (MK_COMB (@lem1764287) (@lem1764288)). Qed.
Lemma lem1764290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764291 : term381 = term382.
Proof. exact (MK_COMB (@lem1764290) (@lem1764289)). Qed.
Lemma lem1764292 : term368 = term383.
Proof. exact (MK_COMB (@lem1764291) (@lem1764285)). Qed.
Lemma lem1764293 : term160 = term383.
Proof. exact (TRANS (@lem1764237) (@lem1764292)). Qed.
Lemma lem1764294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764295 : term159 = term384.
Proof. exact (MK_COMB (@lem1764294) (@lem1764236)). Qed.
Lemma lem1764296 : term161 = term385.
Proof. exact (MK_COMB (@lem1764295) (@lem1764293)). Qed.
Lemma lem1764297 : term163 = term448.
Proof. exact (@lem1483531 term14 term19). Qed.
Lemma lem1764303 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1764305 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764306 : term288 = term289.
Proof. exact (@lem1764305 term277 term277). Qed.
Lemma lem1764307 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764308 : term291 = term277.
Proof. exact (EQ_MP (@lem1764307) (@lem940073)). Qed.
Lemma lem1764309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764310 : term289 = term9.
Proof. exact (MK_COMB (@lem1764309) (@lem1764308)). Qed.
Lemma lem1764311 : term288 = term9.
Proof. exact (TRANS (@lem1764306) (@lem1764310)). Qed.
Lemma lem1764312 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764313 : term285 = term292.
Proof. exact (MK_COMB (@lem1764312) (@lem1764311)). Qed.
Lemma lem1764314 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1764315 : term285 = term9.
Proof. exact (TRANS (@lem1764313) (@lem1764314)). Qed.
Lemma lem1764317 : term284 = term9.
Proof. exact (TRANS (@lem1764303) (@lem1764315)). Qed.
Lemma lem1764318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764319 : term449 = term397.
Proof. exact (MK_COMB (@lem1764318) (@lem1764317)). Qed.
Lemma lem1764320 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764321 : term448 = term398.
Proof. exact (MK_COMB (@lem1764319) (@lem1764320)). Qed.
Lemma lem1764322 : term163 = term398.
Proof. exact (TRANS (@lem1764297) (@lem1764321)). Qed.
Lemma lem1764323 : term185 = term450.
Proof. exact (@lem1483554 term14 term19). Qed.
Lemma lem1764329 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1764331 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764332 : term288 = term289.
Proof. exact (@lem1764331 term277 term277). Qed.
Lemma lem1764333 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764334 : term291 = term277.
Proof. exact (EQ_MP (@lem1764333) (@lem940073)). Qed.
Lemma lem1764335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764336 : term289 = term9.
Proof. exact (MK_COMB (@lem1764335) (@lem1764334)). Qed.
Lemma lem1764337 : term288 = term9.
Proof. exact (TRANS (@lem1764332) (@lem1764336)). Qed.
Lemma lem1764338 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764339 : term285 = term292.
Proof. exact (MK_COMB (@lem1764338) (@lem1764337)). Qed.
Lemma lem1764340 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1764341 : term285 = term9.
Proof. exact (TRANS (@lem1764339) (@lem1764340)). Qed.
Lemma lem1764343 : term284 = term9.
Proof. exact (TRANS (@lem1764329) (@lem1764341)). Qed.
Lemma lem1764344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764345 : term451 = term19.
Proof. exact (MK_COMB (@lem1764344) (@lem1764343)). Qed.
Lemma lem1764346 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1764348 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764349 : term308 = term309.
Proof. exact (@lem1764348 term277 term277). Qed.
Lemma lem1764350 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764351 : term291 = term277.
Proof. exact (EQ_MP (@lem1764350) (@lem940073)). Qed.
Lemma lem1764352 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764353 : term289 = term9.
Proof. exact (MK_COMB (@lem1764352) (@lem1764351)). Qed.
Lemma lem1764354 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764355 : term309 = term19.
Proof. exact (MK_COMB (@lem1764354) (@lem1764353)). Qed.
Lemma lem1764356 : term308 = term19.
Proof. exact (TRANS (@lem1764349) (@lem1764355)). Qed.
Lemma lem1764357 : term19 = term19.
Proof. exact (TRANS (@lem1764346) (@lem1764356)). Qed.
Lemma lem1764358 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem1764359 : (term451 = term19) = (term451 = term19).
Proof. exact (MK_COMB (@lem1764358) (@lem1764357)). Qed.
Lemma lem1764360 : term451 = term19.
Proof. exact (EQ_MP (@lem1764359) (@lem1764345)). Qed.
Lemma lem1764361 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764362 : term453 = term312.
Proof. exact (MK_COMB (@lem1764361) (@lem1764360)). Qed.
Lemma lem1764363 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764364 : term454 = term313.
Proof. exact (MK_COMB (@lem1764362) (@lem1764363)). Qed.
Lemma lem1764365 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764366 : term293 = term294.
Proof. exact (MK_COMB (@lem1764365) (@lem1764343)). Qed.
Lemma lem1764367 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764368 : term283 = term295.
Proof. exact (MK_COMB (@lem1764366) (@lem1764367)). Qed.
Lemma lem1764369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764370 : term455 = term430.
Proof. exact (MK_COMB (@lem1764369) (@lem1764368)). Qed.
Lemma lem1764371 : term450 = term431.
Proof. exact (MK_COMB (@lem1764370) (@lem1764364)). Qed.
Lemma lem1764372 : term185 = term431.
Proof. exact (TRANS (@lem1764323) (@lem1764371)). Qed.
Lemma lem1764373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764374 : term164 = term412.
Proof. exact (MK_COMB (@lem1764373) (@lem1764322)). Qed.
Lemma lem1764375 : term186 = term456.
Proof. exact (MK_COMB (@lem1764374) (@lem1764372)). Qed.
Lemma lem1764376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764377 : term162 = term457.
Proof. exact (MK_COMB (@lem1764376) (@lem1764296)). Qed.
Lemma lem1764378 : term187 = term458.
Proof. exact (MK_COMB (@lem1764377) (@lem1764375)). Qed.
Lemma lem1764379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764380 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1764379) (@lem1764215 x)). Qed.
Lemma lem1764381 (x : real) : (term188 x) = (term459 x).
Proof. exact (MK_COMB (@lem1764380 x) (@lem1764378)). Qed.
Lemma lem1764382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764383 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1764382) (@lem1764196 x)). Qed.
Lemma lem1764384 (x : real) : (term189 x) = (term460 x).
Proof. exact (MK_COMB (@lem1764383 x) (@lem1764381 x)). Qed.
Lemma lem1764385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764386 : term147 = term384.
Proof. exact (MK_COMB (@lem1764385) (@lem1764082)). Qed.
Lemma lem1764387 (x : real) : (term190 x) = (term461 x).
Proof. exact (MK_COMB (@lem1764386) (@lem1764384 x)). Qed.
Lemma lem1764388 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1764394 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1764396 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764397 : term276 = term14.
Proof. exact (@lem1764396 term277). Qed.
Lemma lem1764398 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1764399 : term394 = term395.
Proof. exact (MK_COMB (@lem1764398) (@lem1764397)). Qed.
Lemma lem1764400 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1764401 : term394 = term9.
Proof. exact (TRANS (@lem1764399) (@lem1764400)). Qed.
Lemma lem1764403 : term393 = term9.
Proof. exact (TRANS (@lem1764394) (@lem1764401)). Qed.
Lemma lem1764404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764405 : term396 = term397.
Proof. exact (MK_COMB (@lem1764404) (@lem1764403)). Qed.
Lemma lem1764406 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764407 : term392 = term398.
Proof. exact (MK_COMB (@lem1764405) (@lem1764406)). Qed.
Lemma lem1764408 : term391 = term398.
Proof. exact (TRANS (@lem1764388) (@lem1764407)). Qed.
Lemma lem1764409 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1764415 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1764417 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764418 : term276 = term14.
Proof. exact (@lem1764417 term277). Qed.
Lemma lem1764419 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1764420 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1764419 x) (@lem1764418)). Qed.
Lemma lem1764421 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1764422 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1764420 x) (@lem1764421 x)). Qed.
Lemma lem1764424 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1764415 x) (@lem1764422 x)). Qed.
Lemma lem1764425 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764426 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1764425) (@lem1764424 x)). Qed.
Lemma lem1764427 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764428 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1764426 x) (@lem1764427)). Qed.
Lemma lem1764429 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1764409 x) (@lem1764428 x)). Qed.
Lemma lem1764430 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1764436 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764438 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764439 : term308 = term309.
Proof. exact (@lem1764438 term277 term277). Qed.
Lemma lem1764440 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764441 : term291 = term277.
Proof. exact (EQ_MP (@lem1764440) (@lem940073)). Qed.
Lemma lem1764442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764443 : term289 = term9.
Proof. exact (MK_COMB (@lem1764442) (@lem1764441)). Qed.
Lemma lem1764444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764445 : term309 = term19.
Proof. exact (MK_COMB (@lem1764444) (@lem1764443)). Qed.
Lemma lem1764446 : term308 = term19.
Proof. exact (TRANS (@lem1764439) (@lem1764445)). Qed.
Lemma lem1764447 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764448 : term305 = term310.
Proof. exact (MK_COMB (@lem1764447) (@lem1764446)). Qed.
Lemma lem1764449 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764450 : term305 = term19.
Proof. exact (TRANS (@lem1764448) (@lem1764449)). Qed.
Lemma lem1764452 : term304 = term19.
Proof. exact (TRANS (@lem1764436) (@lem1764450)). Qed.
Lemma lem1764453 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764454 : term321 = term322.
Proof. exact (MK_COMB (@lem1764453) (@lem1764452)). Qed.
Lemma lem1764455 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764456 : term320 = term323.
Proof. exact (MK_COMB (@lem1764454) (@lem1764455)). Qed.
Lemma lem1764457 : term87 = term323.
Proof. exact (TRANS (@lem1764430) (@lem1764456)). Qed.
Lemma lem1764458 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1764464 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764466 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764467 : term308 = term309.
Proof. exact (@lem1764466 term277 term277). Qed.
Lemma lem1764468 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764469 : term291 = term277.
Proof. exact (EQ_MP (@lem1764468) (@lem940073)). Qed.
Lemma lem1764470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764471 : term289 = term9.
Proof. exact (MK_COMB (@lem1764470) (@lem1764469)). Qed.
Lemma lem1764472 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764473 : term309 = term19.
Proof. exact (MK_COMB (@lem1764472) (@lem1764471)). Qed.
Lemma lem1764474 : term308 = term19.
Proof. exact (TRANS (@lem1764467) (@lem1764473)). Qed.
Lemma lem1764475 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764476 : term305 = term310.
Proof. exact (MK_COMB (@lem1764475) (@lem1764474)). Qed.
Lemma lem1764477 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764478 : term305 = term19.
Proof. exact (TRANS (@lem1764476) (@lem1764477)). Qed.
Lemma lem1764480 : term304 = term19.
Proof. exact (TRANS (@lem1764464) (@lem1764478)). Qed.
Lemma lem1764481 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764482 : term400 = term401.
Proof. exact (MK_COMB (@lem1764481) (@lem1764480)). Qed.
Lemma lem1764483 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1764485 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764486 : term288 = term289.
Proof. exact (@lem1764485 term277 term277). Qed.
Lemma lem1764487 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764488 : term291 = term277.
Proof. exact (EQ_MP (@lem1764487) (@lem940073)). Qed.
Lemma lem1764489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764490 : term289 = term9.
Proof. exact (MK_COMB (@lem1764489) (@lem1764488)). Qed.
Lemma lem1764491 : term288 = term9.
Proof. exact (TRANS (@lem1764486) (@lem1764490)). Qed.
Lemma lem1764492 : term401 = term9.
Proof. exact (TRANS (@lem1764483) (@lem1764491)). Qed.
Lemma lem1764493 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1764494 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1764493) (@lem1764492)). Qed.
Lemma lem1764495 : term400 = term9.
Proof. exact (EQ_MP (@lem1764494) (@lem1764482)). Qed.
Lemma lem1764496 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764497 : term403 = term294.
Proof. exact (MK_COMB (@lem1764496) (@lem1764495)). Qed.
Lemma lem1764498 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764499 : term404 = term295.
Proof. exact (MK_COMB (@lem1764497) (@lem1764498)). Qed.
Lemma lem1764500 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764501 : term311 = term312.
Proof. exact (MK_COMB (@lem1764500) (@lem1764480)). Qed.
Lemma lem1764502 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764503 : term303 = term313.
Proof. exact (MK_COMB (@lem1764501) (@lem1764502)). Qed.
Lemma lem1764504 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764505 : term405 = term406.
Proof. exact (MK_COMB (@lem1764504) (@lem1764503)). Qed.
Lemma lem1764506 : term399 = term407.
Proof. exact (MK_COMB (@lem1764505) (@lem1764499)). Qed.
Lemma lem1764507 : term105 = term407.
Proof. exact (TRANS (@lem1764458) (@lem1764506)). Qed.
Lemma lem1764508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764509 : term88 = term355.
Proof. exact (MK_COMB (@lem1764508) (@lem1764457)). Qed.
Lemma lem1764510 : term106 = term408.
Proof. exact (MK_COMB (@lem1764509) (@lem1764507)). Qed.
Lemma lem1764511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764512 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1764511) (@lem1764429 x)). Qed.
Lemma lem1764513 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1764512 x) (@lem1764510)). Qed.
Lemma lem1764514 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1764520 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1764525 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1764527 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1764520 x) (@lem1764525 x)). Qed.
Lemma lem1764528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764529 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1764528) (@lem1764527 x)). Qed.
Lemma lem1764530 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764531 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1764529 x) (@lem1764530)). Qed.
Lemma lem1764532 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1764514 x) (@lem1764531 x)). Qed.
Lemma lem1764533 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1764539 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1764541 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764542 : term276 = term14.
Proof. exact (@lem1764541 term277). Qed.
Lemma lem1764543 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1764544 : term365 = term366.
Proof. exact (MK_COMB (@lem1764543) (@lem1764542)). Qed.
Lemma lem1764545 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1764546 : term365 = term19.
Proof. exact (TRANS (@lem1764544) (@lem1764545)). Qed.
Lemma lem1764548 : term364 = term19.
Proof. exact (TRANS (@lem1764539) (@lem1764546)). Qed.
Lemma lem1764549 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764550 : term367 = term312.
Proof. exact (MK_COMB (@lem1764549) (@lem1764548)). Qed.
Lemma lem1764551 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764552 : term363 = term313.
Proof. exact (MK_COMB (@lem1764550) (@lem1764551)). Qed.
Lemma lem1764553 : term158 = term313.
Proof. exact (TRANS (@lem1764533) (@lem1764552)). Qed.
Lemma lem1764554 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1764560 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1764562 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764563 : term288 = term289.
Proof. exact (@lem1764562 term277 term277). Qed.
Lemma lem1764564 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764565 : term291 = term277.
Proof. exact (EQ_MP (@lem1764564) (@lem940073)). Qed.
Lemma lem1764566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764567 : term289 = term9.
Proof. exact (MK_COMB (@lem1764566) (@lem1764565)). Qed.
Lemma lem1764568 : term288 = term9.
Proof. exact (TRANS (@lem1764563) (@lem1764567)). Qed.
Lemma lem1764569 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1764570 : term370 = term372.
Proof. exact (MK_COMB (@lem1764569) (@lem1764568)). Qed.
Lemma lem1764571 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1764572 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1764573 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1764574 : term332 = term333.
Proof. exact (EQ_MP (@lem1764573) (@lem1764572)). Qed.
Lemma lem1764575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764576 : term334 = term335.
Proof. exact (MK_COMB (@lem1764575) (@lem1764574)). Qed.
Lemma lem1764577 : term372 = term335.
Proof. exact (TRANS (@lem1764571) (@lem1764576)). Qed.
Lemma lem1764578 : term370 = term335.
Proof. exact (TRANS (@lem1764570) (@lem1764577)). Qed.
Lemma lem1764580 : term369 = term335.
Proof. exact (TRANS (@lem1764560) (@lem1764578)). Qed.
Lemma lem1764581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764582 : term373 = term336.
Proof. exact (MK_COMB (@lem1764581) (@lem1764580)). Qed.
Lemma lem1764583 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1764585 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764586 : term374 = term375.
Proof. exact (@lem1764585 term277 term333). Qed.
Lemma lem1764587 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1764588 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1764589 : term342 = term333.
Proof. exact (EQ_MP (@lem1764588) (@lem1764587)). Qed.
Lemma lem1764590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764591 : term340 = term335.
Proof. exact (MK_COMB (@lem1764590) (@lem1764589)). Qed.
Lemma lem1764592 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764593 : term375 = term336.
Proof. exact (MK_COMB (@lem1764592) (@lem1764591)). Qed.
Lemma lem1764594 : term374 = term336.
Proof. exact (TRANS (@lem1764586) (@lem1764593)). Qed.
Lemma lem1764595 : term336 = term336.
Proof. exact (TRANS (@lem1764583) (@lem1764594)). Qed.
Lemma lem1764596 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1764597 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1764596) (@lem1764595)). Qed.
Lemma lem1764598 : term373 = term336.
Proof. exact (EQ_MP (@lem1764597) (@lem1764582)). Qed.
Lemma lem1764599 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764600 : term377 = term349.
Proof. exact (MK_COMB (@lem1764599) (@lem1764598)). Qed.
Lemma lem1764601 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764602 : term378 = term351.
Proof. exact (MK_COMB (@lem1764600) (@lem1764601)). Qed.
Lemma lem1764603 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764604 : term379 = term345.
Proof. exact (MK_COMB (@lem1764603) (@lem1764580)). Qed.
Lemma lem1764605 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764606 : term380 = term347.
Proof. exact (MK_COMB (@lem1764604) (@lem1764605)). Qed.
Lemma lem1764607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764608 : term381 = term382.
Proof. exact (MK_COMB (@lem1764607) (@lem1764606)). Qed.
Lemma lem1764609 : term368 = term383.
Proof. exact (MK_COMB (@lem1764608) (@lem1764602)). Qed.
Lemma lem1764610 : term160 = term383.
Proof. exact (TRANS (@lem1764554) (@lem1764609)). Qed.
Lemma lem1764611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764612 : term159 = term384.
Proof. exact (MK_COMB (@lem1764611) (@lem1764553)). Qed.
Lemma lem1764613 : term161 = term385.
Proof. exact (MK_COMB (@lem1764612) (@lem1764610)). Qed.
Lemma lem1764614 : term163 = term448.
Proof. exact (@lem1483531 term14 term19). Qed.
Lemma lem1764620 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1764622 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764623 : term288 = term289.
Proof. exact (@lem1764622 term277 term277). Qed.
Lemma lem1764624 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764625 : term291 = term277.
Proof. exact (EQ_MP (@lem1764624) (@lem940073)). Qed.
Lemma lem1764626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764627 : term289 = term9.
Proof. exact (MK_COMB (@lem1764626) (@lem1764625)). Qed.
Lemma lem1764628 : term288 = term9.
Proof. exact (TRANS (@lem1764623) (@lem1764627)). Qed.
Lemma lem1764629 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764630 : term285 = term292.
Proof. exact (MK_COMB (@lem1764629) (@lem1764628)). Qed.
Lemma lem1764631 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1764632 : term285 = term9.
Proof. exact (TRANS (@lem1764630) (@lem1764631)). Qed.
Lemma lem1764634 : term284 = term9.
Proof. exact (TRANS (@lem1764620) (@lem1764632)). Qed.
Lemma lem1764635 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764636 : term449 = term397.
Proof. exact (MK_COMB (@lem1764635) (@lem1764634)). Qed.
Lemma lem1764637 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764638 : term448 = term398.
Proof. exact (MK_COMB (@lem1764636) (@lem1764637)). Qed.
Lemma lem1764639 : term163 = term398.
Proof. exact (TRANS (@lem1764614) (@lem1764638)). Qed.
Lemma lem1764640 : term185 = term450.
Proof. exact (@lem1483554 term14 term19). Qed.
Lemma lem1764646 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1764648 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764649 : term288 = term289.
Proof. exact (@lem1764648 term277 term277). Qed.
Lemma lem1764650 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764651 : term291 = term277.
Proof. exact (EQ_MP (@lem1764650) (@lem940073)). Qed.
Lemma lem1764652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764653 : term289 = term9.
Proof. exact (MK_COMB (@lem1764652) (@lem1764651)). Qed.
Lemma lem1764654 : term288 = term9.
Proof. exact (TRANS (@lem1764649) (@lem1764653)). Qed.
Lemma lem1764655 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764656 : term285 = term292.
Proof. exact (MK_COMB (@lem1764655) (@lem1764654)). Qed.
Lemma lem1764657 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1764658 : term285 = term9.
Proof. exact (TRANS (@lem1764656) (@lem1764657)). Qed.
Lemma lem1764660 : term284 = term9.
Proof. exact (TRANS (@lem1764646) (@lem1764658)). Qed.
Lemma lem1764661 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764662 : term451 = term19.
Proof. exact (MK_COMB (@lem1764661) (@lem1764660)). Qed.
Lemma lem1764663 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1764665 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764666 : term308 = term309.
Proof. exact (@lem1764665 term277 term277). Qed.
Lemma lem1764667 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764668 : term291 = term277.
Proof. exact (EQ_MP (@lem1764667) (@lem940073)). Qed.
Lemma lem1764669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764670 : term289 = term9.
Proof. exact (MK_COMB (@lem1764669) (@lem1764668)). Qed.
Lemma lem1764671 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764672 : term309 = term19.
Proof. exact (MK_COMB (@lem1764671) (@lem1764670)). Qed.
Lemma lem1764673 : term308 = term19.
Proof. exact (TRANS (@lem1764666) (@lem1764672)). Qed.
Lemma lem1764674 : term19 = term19.
Proof. exact (TRANS (@lem1764663) (@lem1764673)). Qed.
Lemma lem1764675 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem1764676 : (term451 = term19) = (term451 = term19).
Proof. exact (MK_COMB (@lem1764675) (@lem1764674)). Qed.
Lemma lem1764677 : term451 = term19.
Proof. exact (EQ_MP (@lem1764676) (@lem1764662)). Qed.
Lemma lem1764678 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764679 : term453 = term312.
Proof. exact (MK_COMB (@lem1764678) (@lem1764677)). Qed.
Lemma lem1764680 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764681 : term454 = term313.
Proof. exact (MK_COMB (@lem1764679) (@lem1764680)). Qed.
Lemma lem1764682 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764683 : term293 = term294.
Proof. exact (MK_COMB (@lem1764682) (@lem1764660)). Qed.
Lemma lem1764684 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764685 : term283 = term295.
Proof. exact (MK_COMB (@lem1764683) (@lem1764684)). Qed.
Lemma lem1764686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764687 : term455 = term430.
Proof. exact (MK_COMB (@lem1764686) (@lem1764685)). Qed.
Lemma lem1764688 : term450 = term431.
Proof. exact (MK_COMB (@lem1764687) (@lem1764681)). Qed.
Lemma lem1764689 : term185 = term431.
Proof. exact (TRANS (@lem1764640) (@lem1764688)). Qed.
Lemma lem1764690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764691 : term164 = term412.
Proof. exact (MK_COMB (@lem1764690) (@lem1764639)). Qed.
Lemma lem1764692 : term186 = term456.
Proof. exact (MK_COMB (@lem1764691) (@lem1764689)). Qed.
Lemma lem1764693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764694 : term162 = term457.
Proof. exact (MK_COMB (@lem1764693) (@lem1764613)). Qed.
Lemma lem1764695 : term187 = term458.
Proof. exact (MK_COMB (@lem1764694) (@lem1764692)). Qed.
Lemma lem1764696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764697 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1764696) (@lem1764532 x)). Qed.
Lemma lem1764698 (x : real) : (term188 x) = (term459 x).
Proof. exact (MK_COMB (@lem1764697 x) (@lem1764695)). Qed.
Lemma lem1764699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764700 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1764699) (@lem1764513 x)). Qed.
Lemma lem1764701 (x : real) : (term192 x) = (term462 x).
Proof. exact (MK_COMB (@lem1764700 x) (@lem1764698 x)). Qed.
Lemma lem1764702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764703 : term153 = term412.
Proof. exact (MK_COMB (@lem1764702) (@lem1764408)). Qed.
Lemma lem1764704 (x : real) : (term193 x) = (term463 x).
Proof. exact (MK_COMB (@lem1764703) (@lem1764701 x)). Qed.
Lemma lem1764705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764706 (x : real) : (term191 x) = (term464 x).
Proof. exact (MK_COMB (@lem1764705) (@lem1764387 x)). Qed.
Lemma lem1764707 (x : real) : (term194 x) = (term465 x).
Proof. exact (MK_COMB (@lem1764706 x) (@lem1764704 x)). Qed.
Lemma lem1764708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764709 (x : real) : (term195 x) = (term416 x).
Proof. exact (MK_COMB (@lem1764708) (@lem1764054 x)). Qed.
Lemma lem1764710 (x : real) : (term197 x) = (term466 x).
Proof. exact (MK_COMB (@lem1764709 x) (@lem1764707 x)). Qed.
Lemma lem1764711 (x : real) : (term418 x) = (term419 x).
Proof. exact (@lem1483531 x term14). Qed.
Lemma lem1764717 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1764719 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764720 : term276 = term14.
Proof. exact (@lem1764719 term277). Qed.
Lemma lem1764721 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1764722 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1764721 x) (@lem1764720)). Qed.
Lemma lem1764723 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1764724 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1764722 x) (@lem1764723 x)). Qed.
Lemma lem1764726 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1764717 x) (@lem1764724 x)). Qed.
Lemma lem1764727 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764728 (x : real) : (term420 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1764727) (@lem1764726 x)). Qed.
Lemma lem1764729 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764730 (x : real) : (term419 x) = (term421 x).
Proof. exact (MK_COMB (@lem1764728 x) (@lem1764729)). Qed.
Lemma lem1764731 (x : real) : (term418 x) = (term421 x).
Proof. exact (TRANS (@lem1764711 x) (@lem1764730 x)). Qed.
Lemma lem1764732 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1764738 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764740 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764741 : term308 = term309.
Proof. exact (@lem1764740 term277 term277). Qed.
Lemma lem1764742 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764743 : term291 = term277.
Proof. exact (EQ_MP (@lem1764742) (@lem940073)). Qed.
Lemma lem1764744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764745 : term289 = term9.
Proof. exact (MK_COMB (@lem1764744) (@lem1764743)). Qed.
Lemma lem1764746 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764747 : term309 = term19.
Proof. exact (MK_COMB (@lem1764746) (@lem1764745)). Qed.
Lemma lem1764748 : term308 = term19.
Proof. exact (TRANS (@lem1764741) (@lem1764747)). Qed.
Lemma lem1764749 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764750 : term305 = term310.
Proof. exact (MK_COMB (@lem1764749) (@lem1764748)). Qed.
Lemma lem1764751 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764752 : term305 = term19.
Proof. exact (TRANS (@lem1764750) (@lem1764751)). Qed.
Lemma lem1764754 : term304 = term19.
Proof. exact (TRANS (@lem1764738) (@lem1764752)). Qed.
Lemma lem1764755 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764756 : term311 = term312.
Proof. exact (MK_COMB (@lem1764755) (@lem1764754)). Qed.
Lemma lem1764757 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764758 : term303 = term313.
Proof. exact (MK_COMB (@lem1764756) (@lem1764757)). Qed.
Lemma lem1764759 : term90 = term313.
Proof. exact (TRANS (@lem1764732) (@lem1764758)). Qed.
Lemma lem1764760 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1764766 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1764768 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764769 : term276 = term14.
Proof. exact (@lem1764768 term277). Qed.
Lemma lem1764770 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1764771 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1764770 x) (@lem1764769)). Qed.
Lemma lem1764772 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1764773 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1764771 x) (@lem1764772 x)). Qed.
Lemma lem1764775 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1764766 x) (@lem1764773 x)). Qed.
Lemma lem1764776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764777 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1764776) (@lem1764775 x)). Qed.
Lemma lem1764778 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764779 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1764777 x) (@lem1764778)). Qed.
Lemma lem1764780 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1764760 x) (@lem1764779 x)). Qed.
Lemma lem1764781 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1764787 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764789 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764790 : term308 = term309.
Proof. exact (@lem1764789 term277 term277). Qed.
Lemma lem1764791 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764792 : term291 = term277.
Proof. exact (EQ_MP (@lem1764791) (@lem940073)). Qed.
Lemma lem1764793 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764794 : term289 = term9.
Proof. exact (MK_COMB (@lem1764793) (@lem1764792)). Qed.
Lemma lem1764795 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764796 : term309 = term19.
Proof. exact (MK_COMB (@lem1764795) (@lem1764794)). Qed.
Lemma lem1764797 : term308 = term19.
Proof. exact (TRANS (@lem1764790) (@lem1764796)). Qed.
Lemma lem1764798 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1764799 : term305 = term310.
Proof. exact (MK_COMB (@lem1764798) (@lem1764797)). Qed.
Lemma lem1764800 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1764801 : term305 = term19.
Proof. exact (TRANS (@lem1764799) (@lem1764800)). Qed.
Lemma lem1764803 : term304 = term19.
Proof. exact (TRANS (@lem1764787) (@lem1764801)). Qed.
Lemma lem1764804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764805 : term321 = term322.
Proof. exact (MK_COMB (@lem1764804) (@lem1764803)). Qed.
Lemma lem1764806 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764807 : term320 = term323.
Proof. exact (MK_COMB (@lem1764805) (@lem1764806)). Qed.
Lemma lem1764808 : term87 = term323.
Proof. exact (TRANS (@lem1764781) (@lem1764807)). Qed.
Lemma lem1764809 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1764815 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1764817 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764818 : term308 = term309.
Proof. exact (@lem1764817 term277 term277). Qed.
Lemma lem1764819 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764820 : term291 = term277.
Proof. exact (EQ_MP (@lem1764819) (@lem940073)). Qed.
Lemma lem1764821 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764822 : term289 = term9.
Proof. exact (MK_COMB (@lem1764821) (@lem1764820)). Qed.
Lemma lem1764823 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764824 : term309 = term19.
Proof. exact (MK_COMB (@lem1764823) (@lem1764822)). Qed.
Lemma lem1764825 : term308 = term19.
Proof. exact (TRANS (@lem1764818) (@lem1764824)). Qed.
Lemma lem1764826 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1764827 : term326 = term328.
Proof. exact (MK_COMB (@lem1764826) (@lem1764825)). Qed.
Lemma lem1764828 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1764829 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1764830 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1764831 : term332 = term333.
Proof. exact (EQ_MP (@lem1764830) (@lem1764829)). Qed.
Lemma lem1764832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764833 : term334 = term335.
Proof. exact (MK_COMB (@lem1764832) (@lem1764831)). Qed.
Lemma lem1764834 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764835 : term329 = term336.
Proof. exact (MK_COMB (@lem1764834) (@lem1764833)). Qed.
Lemma lem1764836 : term328 = term336.
Proof. exact (TRANS (@lem1764828) (@lem1764835)). Qed.
Lemma lem1764837 : term326 = term336.
Proof. exact (TRANS (@lem1764827) (@lem1764836)). Qed.
Lemma lem1764839 : term325 = term336.
Proof. exact (TRANS (@lem1764815) (@lem1764837)). Qed.
Lemma lem1764840 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764841 : term337 = term338.
Proof. exact (MK_COMB (@lem1764840) (@lem1764839)). Qed.
Lemma lem1764842 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1764844 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1764845 : term339 = term340.
Proof. exact (@lem1764844 term277 term333). Qed.
Lemma lem1764846 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1764847 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1764848 : term342 = term333.
Proof. exact (EQ_MP (@lem1764847) (@lem1764846)). Qed.
Lemma lem1764849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764850 : term340 = term335.
Proof. exact (MK_COMB (@lem1764849) (@lem1764848)). Qed.
Lemma lem1764851 : term339 = term335.
Proof. exact (TRANS (@lem1764845) (@lem1764850)). Qed.
Lemma lem1764852 : term338 = term335.
Proof. exact (TRANS (@lem1764842) (@lem1764851)). Qed.
Lemma lem1764853 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1764854 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1764853) (@lem1764852)). Qed.
Lemma lem1764855 : term337 = term335.
Proof. exact (EQ_MP (@lem1764854) (@lem1764841)). Qed.
Lemma lem1764856 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764857 : term344 = term345.
Proof. exact (MK_COMB (@lem1764856) (@lem1764855)). Qed.
Lemma lem1764858 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764859 : term346 = term347.
Proof. exact (MK_COMB (@lem1764857) (@lem1764858)). Qed.
Lemma lem1764860 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764861 : term348 = term349.
Proof. exact (MK_COMB (@lem1764860) (@lem1764839)). Qed.
Lemma lem1764862 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764863 : term350 = term351.
Proof. exact (MK_COMB (@lem1764861) (@lem1764862)). Qed.
Lemma lem1764864 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764865 : term352 = term353.
Proof. exact (MK_COMB (@lem1764864) (@lem1764863)). Qed.
Lemma lem1764866 : term324 = term354.
Proof. exact (MK_COMB (@lem1764865) (@lem1764859)). Qed.
Lemma lem1764867 : term118 = term354.
Proof. exact (TRANS (@lem1764809) (@lem1764866)). Qed.
Lemma lem1764868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764869 : term88 = term355.
Proof. exact (MK_COMB (@lem1764868) (@lem1764808)). Qed.
Lemma lem1764870 : term119 = term356.
Proof. exact (MK_COMB (@lem1764869) (@lem1764867)). Qed.
Lemma lem1764871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764872 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1764871) (@lem1764780 x)). Qed.
Lemma lem1764873 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1764872 x) (@lem1764870)). Qed.
Lemma lem1764874 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1764880 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1764885 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1764887 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1764880 x) (@lem1764885 x)). Qed.
Lemma lem1764888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764889 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1764888) (@lem1764887 x)). Qed.
Lemma lem1764890 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764891 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1764889 x) (@lem1764890)). Qed.
Lemma lem1764892 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1764874 x) (@lem1764891 x)). Qed.
Lemma lem1764893 : term132 = term422.
Proof. exact (@lem1483554 term9 term14). Qed.
Lemma lem1764899 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1764901 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764902 : term276 = term14.
Proof. exact (@lem1764901 term277). Qed.
Lemma lem1764903 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1764904 : term394 = term395.
Proof. exact (MK_COMB (@lem1764903) (@lem1764902)). Qed.
Lemma lem1764905 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1764906 : term394 = term9.
Proof. exact (TRANS (@lem1764904) (@lem1764905)). Qed.
Lemma lem1764908 : term393 = term9.
Proof. exact (TRANS (@lem1764899) (@lem1764906)). Qed.
Lemma lem1764909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764910 : term423 = term19.
Proof. exact (MK_COMB (@lem1764909) (@lem1764908)). Qed.
Lemma lem1764911 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1764913 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764914 : term308 = term309.
Proof. exact (@lem1764913 term277 term277). Qed.
Lemma lem1764915 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1764916 : term291 = term277.
Proof. exact (EQ_MP (@lem1764915) (@lem940073)). Qed.
Lemma lem1764917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1764918 : term289 = term9.
Proof. exact (MK_COMB (@lem1764917) (@lem1764916)). Qed.
Lemma lem1764919 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1764920 : term309 = term19.
Proof. exact (MK_COMB (@lem1764919) (@lem1764918)). Qed.
Lemma lem1764921 : term308 = term19.
Proof. exact (TRANS (@lem1764914) (@lem1764920)). Qed.
Lemma lem1764922 : term19 = term19.
Proof. exact (TRANS (@lem1764911) (@lem1764921)). Qed.
Lemma lem1764923 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem1764924 : (term423 = term19) = (term423 = term19).
Proof. exact (MK_COMB (@lem1764923) (@lem1764922)). Qed.
Lemma lem1764925 : term423 = term19.
Proof. exact (EQ_MP (@lem1764924) (@lem1764910)). Qed.
Lemma lem1764926 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764927 : term425 = term312.
Proof. exact (MK_COMB (@lem1764926) (@lem1764925)). Qed.
Lemma lem1764928 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764929 : term426 = term313.
Proof. exact (MK_COMB (@lem1764927) (@lem1764928)). Qed.
Lemma lem1764930 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764931 : term427 = term294.
Proof. exact (MK_COMB (@lem1764930) (@lem1764908)). Qed.
Lemma lem1764932 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764933 : term428 = term295.
Proof. exact (MK_COMB (@lem1764931) (@lem1764932)). Qed.
Lemma lem1764934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764935 : term429 = term430.
Proof. exact (MK_COMB (@lem1764934) (@lem1764933)). Qed.
Lemma lem1764936 : term422 = term431.
Proof. exact (MK_COMB (@lem1764935) (@lem1764929)). Qed.
Lemma lem1764937 : term132 = term431.
Proof. exact (TRANS (@lem1764893) (@lem1764936)). Qed.
Lemma lem1764938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764939 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1764938) (@lem1764892 x)). Qed.
Lemma lem1764940 (x : real) : (term247 x) = (term432 x).
Proof. exact (MK_COMB (@lem1764939 x) (@lem1764937)). Qed.
Lemma lem1764941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1764942 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1764941) (@lem1764873 x)). Qed.
Lemma lem1764943 (x : real) : (term248 x) = (term433 x).
Proof. exact (MK_COMB (@lem1764942 x) (@lem1764940 x)). Qed.
Lemma lem1764944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1764945 : term147 = term384.
Proof. exact (MK_COMB (@lem1764944) (@lem1764759)). Qed.
Lemma lem1764946 (x : real) : (term249 x) = (term434 x).
Proof. exact (MK_COMB (@lem1764945) (@lem1764943 x)). Qed.
Lemma lem1764947 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1764953 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1764955 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764956 : term276 = term14.
Proof. exact (@lem1764955 term277). Qed.
Lemma lem1764957 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1764958 : term394 = term395.
Proof. exact (MK_COMB (@lem1764957) (@lem1764956)). Qed.
Lemma lem1764959 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1764960 : term394 = term9.
Proof. exact (TRANS (@lem1764958) (@lem1764959)). Qed.
Lemma lem1764962 : term393 = term9.
Proof. exact (TRANS (@lem1764953) (@lem1764960)). Qed.
Lemma lem1764963 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1764964 : term396 = term397.
Proof. exact (MK_COMB (@lem1764963) (@lem1764962)). Qed.
Lemma lem1764965 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764966 : term392 = term398.
Proof. exact (MK_COMB (@lem1764964) (@lem1764965)). Qed.
Lemma lem1764967 : term391 = term398.
Proof. exact (TRANS (@lem1764947) (@lem1764966)). Qed.
Lemma lem1764968 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1764974 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1764976 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1764977 : term276 = term14.
Proof. exact (@lem1764976 term277). Qed.
Lemma lem1764978 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1764979 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1764978 x) (@lem1764977)). Qed.
Lemma lem1764980 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1764981 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1764979 x) (@lem1764980 x)). Qed.
Lemma lem1764983 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1764974 x) (@lem1764981 x)). Qed.
Lemma lem1764984 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1764985 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1764984) (@lem1764983 x)). Qed.
Lemma lem1764986 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1764987 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1764985 x) (@lem1764986)). Qed.
Lemma lem1764988 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1764968 x) (@lem1764987 x)). Qed.
Lemma lem1764989 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1764995 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1764997 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1764998 : term308 = term309.
Proof. exact (@lem1764997 term277 term277). Qed.
Lemma lem1764999 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765000 : term291 = term277.
Proof. exact (EQ_MP (@lem1764999) (@lem940073)). Qed.
Lemma lem1765001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765002 : term289 = term9.
Proof. exact (MK_COMB (@lem1765001) (@lem1765000)). Qed.
Lemma lem1765003 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765004 : term309 = term19.
Proof. exact (MK_COMB (@lem1765003) (@lem1765002)). Qed.
Lemma lem1765005 : term308 = term19.
Proof. exact (TRANS (@lem1764998) (@lem1765004)). Qed.
Lemma lem1765006 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765007 : term305 = term310.
Proof. exact (MK_COMB (@lem1765006) (@lem1765005)). Qed.
Lemma lem1765008 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765009 : term305 = term19.
Proof. exact (TRANS (@lem1765007) (@lem1765008)). Qed.
Lemma lem1765011 : term304 = term19.
Proof. exact (TRANS (@lem1764995) (@lem1765009)). Qed.
Lemma lem1765012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765013 : term321 = term322.
Proof. exact (MK_COMB (@lem1765012) (@lem1765011)). Qed.
Lemma lem1765014 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765015 : term320 = term323.
Proof. exact (MK_COMB (@lem1765013) (@lem1765014)). Qed.
Lemma lem1765016 : term87 = term323.
Proof. exact (TRANS (@lem1764989) (@lem1765015)). Qed.
Lemma lem1765017 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1765023 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765025 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765026 : term308 = term309.
Proof. exact (@lem1765025 term277 term277). Qed.
Lemma lem1765027 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765028 : term291 = term277.
Proof. exact (EQ_MP (@lem1765027) (@lem940073)). Qed.
Lemma lem1765029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765030 : term289 = term9.
Proof. exact (MK_COMB (@lem1765029) (@lem1765028)). Qed.
Lemma lem1765031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765032 : term309 = term19.
Proof. exact (MK_COMB (@lem1765031) (@lem1765030)). Qed.
Lemma lem1765033 : term308 = term19.
Proof. exact (TRANS (@lem1765026) (@lem1765032)). Qed.
Lemma lem1765034 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765035 : term305 = term310.
Proof. exact (MK_COMB (@lem1765034) (@lem1765033)). Qed.
Lemma lem1765036 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765037 : term305 = term19.
Proof. exact (TRANS (@lem1765035) (@lem1765036)). Qed.
Lemma lem1765039 : term304 = term19.
Proof. exact (TRANS (@lem1765023) (@lem1765037)). Qed.
Lemma lem1765040 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765041 : term400 = term401.
Proof. exact (MK_COMB (@lem1765040) (@lem1765039)). Qed.
Lemma lem1765042 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1765044 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765045 : term288 = term289.
Proof. exact (@lem1765044 term277 term277). Qed.
Lemma lem1765046 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765047 : term291 = term277.
Proof. exact (EQ_MP (@lem1765046) (@lem940073)). Qed.
Lemma lem1765048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765049 : term289 = term9.
Proof. exact (MK_COMB (@lem1765048) (@lem1765047)). Qed.
Lemma lem1765050 : term288 = term9.
Proof. exact (TRANS (@lem1765045) (@lem1765049)). Qed.
Lemma lem1765051 : term401 = term9.
Proof. exact (TRANS (@lem1765042) (@lem1765050)). Qed.
Lemma lem1765052 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1765053 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1765052) (@lem1765051)). Qed.
Lemma lem1765054 : term400 = term9.
Proof. exact (EQ_MP (@lem1765053) (@lem1765041)). Qed.
Lemma lem1765055 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765056 : term403 = term294.
Proof. exact (MK_COMB (@lem1765055) (@lem1765054)). Qed.
Lemma lem1765057 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765058 : term404 = term295.
Proof. exact (MK_COMB (@lem1765056) (@lem1765057)). Qed.
Lemma lem1765059 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765060 : term311 = term312.
Proof. exact (MK_COMB (@lem1765059) (@lem1765039)). Qed.
Lemma lem1765061 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765062 : term303 = term313.
Proof. exact (MK_COMB (@lem1765060) (@lem1765061)). Qed.
Lemma lem1765063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765064 : term405 = term406.
Proof. exact (MK_COMB (@lem1765063) (@lem1765062)). Qed.
Lemma lem1765065 : term399 = term407.
Proof. exact (MK_COMB (@lem1765064) (@lem1765058)). Qed.
Lemma lem1765066 : term105 = term407.
Proof. exact (TRANS (@lem1765017) (@lem1765065)). Qed.
Lemma lem1765067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765068 : term88 = term355.
Proof. exact (MK_COMB (@lem1765067) (@lem1765016)). Qed.
Lemma lem1765069 : term106 = term408.
Proof. exact (MK_COMB (@lem1765068) (@lem1765066)). Qed.
Lemma lem1765070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765071 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1765070) (@lem1764988 x)). Qed.
Lemma lem1765072 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1765071 x) (@lem1765069)). Qed.
Lemma lem1765073 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1765079 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1765084 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1765086 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1765079 x) (@lem1765084 x)). Qed.
Lemma lem1765087 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765088 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1765087) (@lem1765086 x)). Qed.
Lemma lem1765089 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765090 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1765088 x) (@lem1765089)). Qed.
Lemma lem1765091 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1765073 x) (@lem1765090 x)). Qed.
Lemma lem1765092 : term132 = term422.
Proof. exact (@lem1483554 term9 term14). Qed.
Lemma lem1765098 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1765100 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765101 : term276 = term14.
Proof. exact (@lem1765100 term277). Qed.
Lemma lem1765102 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1765103 : term394 = term395.
Proof. exact (MK_COMB (@lem1765102) (@lem1765101)). Qed.
Lemma lem1765104 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1765105 : term394 = term9.
Proof. exact (TRANS (@lem1765103) (@lem1765104)). Qed.
Lemma lem1765107 : term393 = term9.
Proof. exact (TRANS (@lem1765098) (@lem1765105)). Qed.
Lemma lem1765108 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765109 : term423 = term19.
Proof. exact (MK_COMB (@lem1765108) (@lem1765107)). Qed.
Lemma lem1765110 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1765112 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765113 : term308 = term309.
Proof. exact (@lem1765112 term277 term277). Qed.
Lemma lem1765114 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765115 : term291 = term277.
Proof. exact (EQ_MP (@lem1765114) (@lem940073)). Qed.
Lemma lem1765116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765117 : term289 = term9.
Proof. exact (MK_COMB (@lem1765116) (@lem1765115)). Qed.
Lemma lem1765118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765119 : term309 = term19.
Proof. exact (MK_COMB (@lem1765118) (@lem1765117)). Qed.
Lemma lem1765120 : term308 = term19.
Proof. exact (TRANS (@lem1765113) (@lem1765119)). Qed.
Lemma lem1765121 : term19 = term19.
Proof. exact (TRANS (@lem1765110) (@lem1765120)). Qed.
Lemma lem1765122 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem1765123 : (term423 = term19) = (term423 = term19).
Proof. exact (MK_COMB (@lem1765122) (@lem1765121)). Qed.
Lemma lem1765124 : term423 = term19.
Proof. exact (EQ_MP (@lem1765123) (@lem1765109)). Qed.
Lemma lem1765125 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765126 : term425 = term312.
Proof. exact (MK_COMB (@lem1765125) (@lem1765124)). Qed.
Lemma lem1765127 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765128 : term426 = term313.
Proof. exact (MK_COMB (@lem1765126) (@lem1765127)). Qed.
Lemma lem1765129 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765130 : term427 = term294.
Proof. exact (MK_COMB (@lem1765129) (@lem1765107)). Qed.
Lemma lem1765131 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765132 : term428 = term295.
Proof. exact (MK_COMB (@lem1765130) (@lem1765131)). Qed.
Lemma lem1765133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765134 : term429 = term430.
Proof. exact (MK_COMB (@lem1765133) (@lem1765132)). Qed.
Lemma lem1765135 : term422 = term431.
Proof. exact (MK_COMB (@lem1765134) (@lem1765128)). Qed.
Lemma lem1765136 : term132 = term431.
Proof. exact (TRANS (@lem1765092) (@lem1765135)). Qed.
Lemma lem1765137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765138 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1765137) (@lem1765091 x)). Qed.
Lemma lem1765139 (x : real) : (term247 x) = (term432 x).
Proof. exact (MK_COMB (@lem1765138 x) (@lem1765136)). Qed.
Lemma lem1765140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765141 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1765140) (@lem1765072 x)). Qed.
Lemma lem1765142 (x : real) : (term251 x) = (term435 x).
Proof. exact (MK_COMB (@lem1765141 x) (@lem1765139 x)). Qed.
Lemma lem1765143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765144 : term153 = term412.
Proof. exact (MK_COMB (@lem1765143) (@lem1764967)). Qed.
Lemma lem1765145 (x : real) : (term252 x) = (term436 x).
Proof. exact (MK_COMB (@lem1765144) (@lem1765142 x)). Qed.
Lemma lem1765146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765147 (x : real) : (term250 x) = (term437 x).
Proof. exact (MK_COMB (@lem1765146) (@lem1764946 x)). Qed.
Lemma lem1765148 (x : real) : (term253 x) = (term438 x).
Proof. exact (MK_COMB (@lem1765147 x) (@lem1765145 x)). Qed.
Lemma lem1765149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765150 (x : real) : (term228 x) = (term439 x).
Proof. exact (MK_COMB (@lem1765149) (@lem1764731 x)). Qed.
Lemma lem1765151 (x : real) : (term254 x) = (term440 x).
Proof. exact (MK_COMB (@lem1765150 x) (@lem1765148 x)). Qed.
Lemma lem1765152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765153 (x : real) : (term199 x) = (term467 x).
Proof. exact (MK_COMB (@lem1765152) (@lem1764710 x)). Qed.
Lemma lem1765154 (x : real) : (term258 x) = (term468 x).
Proof. exact (MK_COMB (@lem1765153 x) (@lem1765151 x)). Qed.
Lemma lem1765155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765156 : term237 = term355.
Proof. exact (MK_COMB (@lem1765155) (@lem1764035)). Qed.
Lemma lem1765157 (x : real) : (term259 x) = (term469 x).
Proof. exact (MK_COMB (@lem1765156) (@lem1765154 x)). Qed.
Lemma lem1765158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765159 (x : real) : (term257 x) = (term470 x).
Proof. exact (MK_COMB (@lem1765158) (@lem1764014 x)). Qed.
Lemma lem1765160 (x : real) : (term260 x) = (term471 x).
Proof. exact (MK_COMB (@lem1765159 x) (@lem1765157 x)). Qed.
Lemma lem1765161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765162 : term131 = term472.
Proof. exact (MK_COMB (@lem1765161) (@lem1763030)). Qed.
Lemma lem1765163 (x : real) : (term473 x) = (term474 x).
Proof. exact (MK_COMB (@lem1765162) (@lem1765160 x)). Qed.
Lemma lem1765164 : term135 = term475.
Proof. exact (@lem1483531 term14 term14). Qed.
Lemma lem1765170 : term273 = term274.
Proof. exact (@lem1483519 term14 term14). Qed.
Lemma lem1765172 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765173 : term276 = term14.
Proof. exact (@lem1765172 term277). Qed.
Lemma lem1765174 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765175 : term274 = term279.
Proof. exact (MK_COMB (@lem1765174) (@lem1765173)). Qed.
Lemma lem1765176 : term279 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1765177 : term274 = term14.
Proof. exact (TRANS (@lem1765175) (@lem1765176)). Qed.
Lemma lem1765179 : term273 = term14.
Proof. exact (TRANS (@lem1765170) (@lem1765177)). Qed.
Lemma lem1765180 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765181 : term476 = term477.
Proof. exact (MK_COMB (@lem1765180) (@lem1765179)). Qed.
Lemma lem1765182 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765183 : term475 = term478.
Proof. exact (MK_COMB (@lem1765181) (@lem1765182)). Qed.
Lemma lem1765184 : term135 = term478.
Proof. exact (TRANS (@lem1765164) (@lem1765183)). Qed.
Lemma lem1765185 : term166 = term283.
Proof. exact (@lem1483521 term14 term19). Qed.
Lemma lem1765191 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1765193 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765194 : term288 = term289.
Proof. exact (@lem1765193 term277 term277). Qed.
Lemma lem1765195 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765196 : term291 = term277.
Proof. exact (EQ_MP (@lem1765195) (@lem940073)). Qed.
Lemma lem1765197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765198 : term289 = term9.
Proof. exact (MK_COMB (@lem1765197) (@lem1765196)). Qed.
Lemma lem1765199 : term288 = term9.
Proof. exact (TRANS (@lem1765194) (@lem1765198)). Qed.
Lemma lem1765200 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765201 : term285 = term292.
Proof. exact (MK_COMB (@lem1765200) (@lem1765199)). Qed.
Lemma lem1765202 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1765203 : term285 = term9.
Proof. exact (TRANS (@lem1765201) (@lem1765202)). Qed.
Lemma lem1765205 : term284 = term9.
Proof. exact (TRANS (@lem1765191) (@lem1765203)). Qed.
Lemma lem1765206 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765207 : term293 = term294.
Proof. exact (MK_COMB (@lem1765206) (@lem1765205)). Qed.
Lemma lem1765208 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765209 : term283 = term295.
Proof. exact (MK_COMB (@lem1765207) (@lem1765208)). Qed.
Lemma lem1765210 : term166 = term295.
Proof. exact (TRANS (@lem1765185) (@lem1765209)). Qed.
Lemma lem1765211 (x : real) : (term127 x) = (term296 x).
Proof. exact (@lem1483521 term14 x). Qed.
Lemma lem1765217 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1765222 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1765224 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1765217 x) (@lem1765222 x)). Qed.
Lemma lem1765225 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765226 (x : real) : (term300 x) = (term301 x).
Proof. exact (MK_COMB (@lem1765225) (@lem1765224 x)). Qed.
Lemma lem1765227 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765228 (x : real) : (term296 x) = (term302 x).
Proof. exact (MK_COMB (@lem1765226 x) (@lem1765227)). Qed.
Lemma lem1765229 (x : real) : (term127 x) = (term302 x).
Proof. exact (TRANS (@lem1765211 x) (@lem1765228 x)). Qed.
Lemma lem1765230 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1765236 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765238 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765239 : term308 = term309.
Proof. exact (@lem1765238 term277 term277). Qed.
Lemma lem1765240 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765241 : term291 = term277.
Proof. exact (EQ_MP (@lem1765240) (@lem940073)). Qed.
Lemma lem1765242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765243 : term289 = term9.
Proof. exact (MK_COMB (@lem1765242) (@lem1765241)). Qed.
Lemma lem1765244 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765245 : term309 = term19.
Proof. exact (MK_COMB (@lem1765244) (@lem1765243)). Qed.
Lemma lem1765246 : term308 = term19.
Proof. exact (TRANS (@lem1765239) (@lem1765245)). Qed.
Lemma lem1765247 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765248 : term305 = term310.
Proof. exact (MK_COMB (@lem1765247) (@lem1765246)). Qed.
Lemma lem1765249 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765250 : term305 = term19.
Proof. exact (TRANS (@lem1765248) (@lem1765249)). Qed.
Lemma lem1765252 : term304 = term19.
Proof. exact (TRANS (@lem1765236) (@lem1765250)). Qed.
Lemma lem1765253 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765254 : term311 = term312.
Proof. exact (MK_COMB (@lem1765253) (@lem1765252)). Qed.
Lemma lem1765255 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765256 : term303 = term313.
Proof. exact (MK_COMB (@lem1765254) (@lem1765255)). Qed.
Lemma lem1765257 : term90 = term313.
Proof. exact (TRANS (@lem1765230) (@lem1765256)). Qed.
Lemma lem1765258 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1765264 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1765266 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765267 : term276 = term14.
Proof. exact (@lem1765266 term277). Qed.
Lemma lem1765268 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1765269 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1765268 x) (@lem1765267)). Qed.
Lemma lem1765270 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1765271 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1765269 x) (@lem1765270 x)). Qed.
Lemma lem1765273 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1765264 x) (@lem1765271 x)). Qed.
Lemma lem1765274 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765275 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1765274) (@lem1765273 x)). Qed.
Lemma lem1765276 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765277 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1765275 x) (@lem1765276)). Qed.
Lemma lem1765278 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1765258 x) (@lem1765277 x)). Qed.
Lemma lem1765279 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1765285 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765287 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765288 : term308 = term309.
Proof. exact (@lem1765287 term277 term277). Qed.
Lemma lem1765289 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765290 : term291 = term277.
Proof. exact (EQ_MP (@lem1765289) (@lem940073)). Qed.
Lemma lem1765291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765292 : term289 = term9.
Proof. exact (MK_COMB (@lem1765291) (@lem1765290)). Qed.
Lemma lem1765293 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765294 : term309 = term19.
Proof. exact (MK_COMB (@lem1765293) (@lem1765292)). Qed.
Lemma lem1765295 : term308 = term19.
Proof. exact (TRANS (@lem1765288) (@lem1765294)). Qed.
Lemma lem1765296 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765297 : term305 = term310.
Proof. exact (MK_COMB (@lem1765296) (@lem1765295)). Qed.
Lemma lem1765298 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765299 : term305 = term19.
Proof. exact (TRANS (@lem1765297) (@lem1765298)). Qed.
Lemma lem1765301 : term304 = term19.
Proof. exact (TRANS (@lem1765285) (@lem1765299)). Qed.
Lemma lem1765302 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765303 : term321 = term322.
Proof. exact (MK_COMB (@lem1765302) (@lem1765301)). Qed.
Lemma lem1765304 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765305 : term320 = term323.
Proof. exact (MK_COMB (@lem1765303) (@lem1765304)). Qed.
Lemma lem1765306 : term87 = term323.
Proof. exact (TRANS (@lem1765279) (@lem1765305)). Qed.
Lemma lem1765307 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1765313 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1765315 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765316 : term308 = term309.
Proof. exact (@lem1765315 term277 term277). Qed.
Lemma lem1765317 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765318 : term291 = term277.
Proof. exact (EQ_MP (@lem1765317) (@lem940073)). Qed.
Lemma lem1765319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765320 : term289 = term9.
Proof. exact (MK_COMB (@lem1765319) (@lem1765318)). Qed.
Lemma lem1765321 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765322 : term309 = term19.
Proof. exact (MK_COMB (@lem1765321) (@lem1765320)). Qed.
Lemma lem1765323 : term308 = term19.
Proof. exact (TRANS (@lem1765316) (@lem1765322)). Qed.
Lemma lem1765324 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1765325 : term326 = term328.
Proof. exact (MK_COMB (@lem1765324) (@lem1765323)). Qed.
Lemma lem1765326 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1765327 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1765328 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1765329 : term332 = term333.
Proof. exact (EQ_MP (@lem1765328) (@lem1765327)). Qed.
Lemma lem1765330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765331 : term334 = term335.
Proof. exact (MK_COMB (@lem1765330) (@lem1765329)). Qed.
Lemma lem1765332 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765333 : term329 = term336.
Proof. exact (MK_COMB (@lem1765332) (@lem1765331)). Qed.
Lemma lem1765334 : term328 = term336.
Proof. exact (TRANS (@lem1765326) (@lem1765333)). Qed.
Lemma lem1765335 : term326 = term336.
Proof. exact (TRANS (@lem1765325) (@lem1765334)). Qed.
Lemma lem1765337 : term325 = term336.
Proof. exact (TRANS (@lem1765313) (@lem1765335)). Qed.
Lemma lem1765338 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765339 : term337 = term338.
Proof. exact (MK_COMB (@lem1765338) (@lem1765337)). Qed.
Lemma lem1765340 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1765342 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765343 : term339 = term340.
Proof. exact (@lem1765342 term277 term333). Qed.
Lemma lem1765344 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1765345 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1765346 : term342 = term333.
Proof. exact (EQ_MP (@lem1765345) (@lem1765344)). Qed.
Lemma lem1765347 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765348 : term340 = term335.
Proof. exact (MK_COMB (@lem1765347) (@lem1765346)). Qed.
Lemma lem1765349 : term339 = term335.
Proof. exact (TRANS (@lem1765343) (@lem1765348)). Qed.
Lemma lem1765350 : term338 = term335.
Proof. exact (TRANS (@lem1765340) (@lem1765349)). Qed.
Lemma lem1765351 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1765352 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1765351) (@lem1765350)). Qed.
Lemma lem1765353 : term337 = term335.
Proof. exact (EQ_MP (@lem1765352) (@lem1765339)). Qed.
Lemma lem1765354 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765355 : term344 = term345.
Proof. exact (MK_COMB (@lem1765354) (@lem1765353)). Qed.
Lemma lem1765356 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765357 : term346 = term347.
Proof. exact (MK_COMB (@lem1765355) (@lem1765356)). Qed.
Lemma lem1765358 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765359 : term348 = term349.
Proof. exact (MK_COMB (@lem1765358) (@lem1765337)). Qed.
Lemma lem1765360 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765361 : term350 = term351.
Proof. exact (MK_COMB (@lem1765359) (@lem1765360)). Qed.
Lemma lem1765362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765363 : term352 = term353.
Proof. exact (MK_COMB (@lem1765362) (@lem1765361)). Qed.
Lemma lem1765364 : term324 = term354.
Proof. exact (MK_COMB (@lem1765363) (@lem1765357)). Qed.
Lemma lem1765365 : term118 = term354.
Proof. exact (TRANS (@lem1765307) (@lem1765364)). Qed.
Lemma lem1765366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765367 : term88 = term355.
Proof. exact (MK_COMB (@lem1765366) (@lem1765306)). Qed.
Lemma lem1765368 : term119 = term356.
Proof. exact (MK_COMB (@lem1765367) (@lem1765365)). Qed.
Lemma lem1765369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765370 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1765369) (@lem1765278 x)). Qed.
Lemma lem1765371 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1765370 x) (@lem1765368)). Qed.
Lemma lem1765372 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1765378 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1765383 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1765385 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1765378 x) (@lem1765383 x)). Qed.
Lemma lem1765386 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765387 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1765386) (@lem1765385 x)). Qed.
Lemma lem1765388 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765389 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1765387 x) (@lem1765388)). Qed.
Lemma lem1765390 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1765372 x) (@lem1765389 x)). Qed.
Lemma lem1765391 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1765397 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1765399 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765400 : term276 = term14.
Proof. exact (@lem1765399 term277). Qed.
Lemma lem1765401 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1765402 : term365 = term366.
Proof. exact (MK_COMB (@lem1765401) (@lem1765400)). Qed.
Lemma lem1765403 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1765404 : term365 = term19.
Proof. exact (TRANS (@lem1765402) (@lem1765403)). Qed.
Lemma lem1765406 : term364 = term19.
Proof. exact (TRANS (@lem1765397) (@lem1765404)). Qed.
Lemma lem1765407 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765408 : term367 = term312.
Proof. exact (MK_COMB (@lem1765407) (@lem1765406)). Qed.
Lemma lem1765409 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765410 : term363 = term313.
Proof. exact (MK_COMB (@lem1765408) (@lem1765409)). Qed.
Lemma lem1765411 : term158 = term313.
Proof. exact (TRANS (@lem1765391) (@lem1765410)). Qed.
Lemma lem1765412 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1765418 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1765420 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765421 : term288 = term289.
Proof. exact (@lem1765420 term277 term277). Qed.
Lemma lem1765422 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765423 : term291 = term277.
Proof. exact (EQ_MP (@lem1765422) (@lem940073)). Qed.
Lemma lem1765424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765425 : term289 = term9.
Proof. exact (MK_COMB (@lem1765424) (@lem1765423)). Qed.
Lemma lem1765426 : term288 = term9.
Proof. exact (TRANS (@lem1765421) (@lem1765425)). Qed.
Lemma lem1765427 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1765428 : term370 = term372.
Proof. exact (MK_COMB (@lem1765427) (@lem1765426)). Qed.
Lemma lem1765429 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1765430 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1765431 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1765432 : term332 = term333.
Proof. exact (EQ_MP (@lem1765431) (@lem1765430)). Qed.
Lemma lem1765433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765434 : term334 = term335.
Proof. exact (MK_COMB (@lem1765433) (@lem1765432)). Qed.
Lemma lem1765435 : term372 = term335.
Proof. exact (TRANS (@lem1765429) (@lem1765434)). Qed.
Lemma lem1765436 : term370 = term335.
Proof. exact (TRANS (@lem1765428) (@lem1765435)). Qed.
Lemma lem1765438 : term369 = term335.
Proof. exact (TRANS (@lem1765418) (@lem1765436)). Qed.
Lemma lem1765439 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765440 : term373 = term336.
Proof. exact (MK_COMB (@lem1765439) (@lem1765438)). Qed.
Lemma lem1765441 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1765443 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765444 : term374 = term375.
Proof. exact (@lem1765443 term277 term333). Qed.
Lemma lem1765445 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1765446 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1765447 : term342 = term333.
Proof. exact (EQ_MP (@lem1765446) (@lem1765445)). Qed.
Lemma lem1765448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765449 : term340 = term335.
Proof. exact (MK_COMB (@lem1765448) (@lem1765447)). Qed.
Lemma lem1765450 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765451 : term375 = term336.
Proof. exact (MK_COMB (@lem1765450) (@lem1765449)). Qed.
Lemma lem1765452 : term374 = term336.
Proof. exact (TRANS (@lem1765444) (@lem1765451)). Qed.
Lemma lem1765453 : term336 = term336.
Proof. exact (TRANS (@lem1765441) (@lem1765452)). Qed.
Lemma lem1765454 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1765455 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1765454) (@lem1765453)). Qed.
Lemma lem1765456 : term373 = term336.
Proof. exact (EQ_MP (@lem1765455) (@lem1765440)). Qed.
Lemma lem1765457 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765458 : term377 = term349.
Proof. exact (MK_COMB (@lem1765457) (@lem1765456)). Qed.
Lemma lem1765459 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765460 : term378 = term351.
Proof. exact (MK_COMB (@lem1765458) (@lem1765459)). Qed.
Lemma lem1765461 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765462 : term379 = term345.
Proof. exact (MK_COMB (@lem1765461) (@lem1765438)). Qed.
Lemma lem1765463 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765464 : term380 = term347.
Proof. exact (MK_COMB (@lem1765462) (@lem1765463)). Qed.
Lemma lem1765465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765466 : term381 = term382.
Proof. exact (MK_COMB (@lem1765465) (@lem1765464)). Qed.
Lemma lem1765467 : term368 = term383.
Proof. exact (MK_COMB (@lem1765466) (@lem1765460)). Qed.
Lemma lem1765468 : term160 = term383.
Proof. exact (TRANS (@lem1765412) (@lem1765467)). Qed.
Lemma lem1765469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765470 : term159 = term384.
Proof. exact (MK_COMB (@lem1765469) (@lem1765411)). Qed.
Lemma lem1765471 : term161 = term385.
Proof. exact (MK_COMB (@lem1765470) (@lem1765468)). Qed.
Lemma lem1765472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765473 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1765472) (@lem1765390 x)). Qed.
Lemma lem1765474 (x : real) : (term205 x) = (term387 x).
Proof. exact (MK_COMB (@lem1765473 x) (@lem1765471)). Qed.
Lemma lem1765475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765476 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1765475) (@lem1765371 x)). Qed.
Lemma lem1765477 (x : real) : (term206 x) = (term389 x).
Proof. exact (MK_COMB (@lem1765476 x) (@lem1765474 x)). Qed.
Lemma lem1765478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765479 : term147 = term384.
Proof. exact (MK_COMB (@lem1765478) (@lem1765257)). Qed.
Lemma lem1765480 (x : real) : (term207 x) = (term390 x).
Proof. exact (MK_COMB (@lem1765479) (@lem1765477 x)). Qed.
Lemma lem1765481 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1765487 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1765489 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765490 : term276 = term14.
Proof. exact (@lem1765489 term277). Qed.
Lemma lem1765491 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1765492 : term394 = term395.
Proof. exact (MK_COMB (@lem1765491) (@lem1765490)). Qed.
Lemma lem1765493 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1765494 : term394 = term9.
Proof. exact (TRANS (@lem1765492) (@lem1765493)). Qed.
Lemma lem1765496 : term393 = term9.
Proof. exact (TRANS (@lem1765487) (@lem1765494)). Qed.
Lemma lem1765497 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765498 : term396 = term397.
Proof. exact (MK_COMB (@lem1765497) (@lem1765496)). Qed.
Lemma lem1765499 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765500 : term392 = term398.
Proof. exact (MK_COMB (@lem1765498) (@lem1765499)). Qed.
Lemma lem1765501 : term391 = term398.
Proof. exact (TRANS (@lem1765481) (@lem1765500)). Qed.
Lemma lem1765502 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1765508 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1765510 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765511 : term276 = term14.
Proof. exact (@lem1765510 term277). Qed.
Lemma lem1765512 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1765513 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1765512 x) (@lem1765511)). Qed.
Lemma lem1765514 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1765515 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1765513 x) (@lem1765514 x)). Qed.
Lemma lem1765517 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1765508 x) (@lem1765515 x)). Qed.
Lemma lem1765518 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765519 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1765518) (@lem1765517 x)). Qed.
Lemma lem1765520 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765521 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1765519 x) (@lem1765520)). Qed.
Lemma lem1765522 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1765502 x) (@lem1765521 x)). Qed.
Lemma lem1765523 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1765529 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765531 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765532 : term308 = term309.
Proof. exact (@lem1765531 term277 term277). Qed.
Lemma lem1765533 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765534 : term291 = term277.
Proof. exact (EQ_MP (@lem1765533) (@lem940073)). Qed.
Lemma lem1765535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765536 : term289 = term9.
Proof. exact (MK_COMB (@lem1765535) (@lem1765534)). Qed.
Lemma lem1765537 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765538 : term309 = term19.
Proof. exact (MK_COMB (@lem1765537) (@lem1765536)). Qed.
Lemma lem1765539 : term308 = term19.
Proof. exact (TRANS (@lem1765532) (@lem1765538)). Qed.
Lemma lem1765540 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765541 : term305 = term310.
Proof. exact (MK_COMB (@lem1765540) (@lem1765539)). Qed.
Lemma lem1765542 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765543 : term305 = term19.
Proof. exact (TRANS (@lem1765541) (@lem1765542)). Qed.
Lemma lem1765545 : term304 = term19.
Proof. exact (TRANS (@lem1765529) (@lem1765543)). Qed.
Lemma lem1765546 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765547 : term321 = term322.
Proof. exact (MK_COMB (@lem1765546) (@lem1765545)). Qed.
Lemma lem1765548 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765549 : term320 = term323.
Proof. exact (MK_COMB (@lem1765547) (@lem1765548)). Qed.
Lemma lem1765550 : term87 = term323.
Proof. exact (TRANS (@lem1765523) (@lem1765549)). Qed.
Lemma lem1765551 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1765557 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765559 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765560 : term308 = term309.
Proof. exact (@lem1765559 term277 term277). Qed.
Lemma lem1765561 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765562 : term291 = term277.
Proof. exact (EQ_MP (@lem1765561) (@lem940073)). Qed.
Lemma lem1765563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765564 : term289 = term9.
Proof. exact (MK_COMB (@lem1765563) (@lem1765562)). Qed.
Lemma lem1765565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765566 : term309 = term19.
Proof. exact (MK_COMB (@lem1765565) (@lem1765564)). Qed.
Lemma lem1765567 : term308 = term19.
Proof. exact (TRANS (@lem1765560) (@lem1765566)). Qed.
Lemma lem1765568 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765569 : term305 = term310.
Proof. exact (MK_COMB (@lem1765568) (@lem1765567)). Qed.
Lemma lem1765570 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765571 : term305 = term19.
Proof. exact (TRANS (@lem1765569) (@lem1765570)). Qed.
Lemma lem1765573 : term304 = term19.
Proof. exact (TRANS (@lem1765557) (@lem1765571)). Qed.
Lemma lem1765574 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765575 : term400 = term401.
Proof. exact (MK_COMB (@lem1765574) (@lem1765573)). Qed.
Lemma lem1765576 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1765578 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765579 : term288 = term289.
Proof. exact (@lem1765578 term277 term277). Qed.
Lemma lem1765580 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765581 : term291 = term277.
Proof. exact (EQ_MP (@lem1765580) (@lem940073)). Qed.
Lemma lem1765582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765583 : term289 = term9.
Proof. exact (MK_COMB (@lem1765582) (@lem1765581)). Qed.
Lemma lem1765584 : term288 = term9.
Proof. exact (TRANS (@lem1765579) (@lem1765583)). Qed.
Lemma lem1765585 : term401 = term9.
Proof. exact (TRANS (@lem1765576) (@lem1765584)). Qed.
Lemma lem1765586 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1765587 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1765586) (@lem1765585)). Qed.
Lemma lem1765588 : term400 = term9.
Proof. exact (EQ_MP (@lem1765587) (@lem1765575)). Qed.
Lemma lem1765589 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765590 : term403 = term294.
Proof. exact (MK_COMB (@lem1765589) (@lem1765588)). Qed.
Lemma lem1765591 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765592 : term404 = term295.
Proof. exact (MK_COMB (@lem1765590) (@lem1765591)). Qed.
Lemma lem1765593 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765594 : term311 = term312.
Proof. exact (MK_COMB (@lem1765593) (@lem1765573)). Qed.
Lemma lem1765595 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765596 : term303 = term313.
Proof. exact (MK_COMB (@lem1765594) (@lem1765595)). Qed.
Lemma lem1765597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765598 : term405 = term406.
Proof. exact (MK_COMB (@lem1765597) (@lem1765596)). Qed.
Lemma lem1765599 : term399 = term407.
Proof. exact (MK_COMB (@lem1765598) (@lem1765592)). Qed.
Lemma lem1765600 : term105 = term407.
Proof. exact (TRANS (@lem1765551) (@lem1765599)). Qed.
Lemma lem1765601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765602 : term88 = term355.
Proof. exact (MK_COMB (@lem1765601) (@lem1765550)). Qed.
Lemma lem1765603 : term106 = term408.
Proof. exact (MK_COMB (@lem1765602) (@lem1765600)). Qed.
Lemma lem1765604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765605 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1765604) (@lem1765522 x)). Qed.
Lemma lem1765606 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1765605 x) (@lem1765603)). Qed.
Lemma lem1765607 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1765613 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1765618 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1765620 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1765613 x) (@lem1765618 x)). Qed.
Lemma lem1765621 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765622 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1765621) (@lem1765620 x)). Qed.
Lemma lem1765623 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765624 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1765622 x) (@lem1765623)). Qed.
Lemma lem1765625 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1765607 x) (@lem1765624 x)). Qed.
Lemma lem1765626 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1765632 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1765634 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765635 : term276 = term14.
Proof. exact (@lem1765634 term277). Qed.
Lemma lem1765636 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1765637 : term365 = term366.
Proof. exact (MK_COMB (@lem1765636) (@lem1765635)). Qed.
Lemma lem1765638 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1765639 : term365 = term19.
Proof. exact (TRANS (@lem1765637) (@lem1765638)). Qed.
Lemma lem1765641 : term364 = term19.
Proof. exact (TRANS (@lem1765632) (@lem1765639)). Qed.
Lemma lem1765642 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765643 : term367 = term312.
Proof. exact (MK_COMB (@lem1765642) (@lem1765641)). Qed.
Lemma lem1765644 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765645 : term363 = term313.
Proof. exact (MK_COMB (@lem1765643) (@lem1765644)). Qed.
Lemma lem1765646 : term158 = term313.
Proof. exact (TRANS (@lem1765626) (@lem1765645)). Qed.
Lemma lem1765647 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1765653 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1765655 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765656 : term288 = term289.
Proof. exact (@lem1765655 term277 term277). Qed.
Lemma lem1765657 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765658 : term291 = term277.
Proof. exact (EQ_MP (@lem1765657) (@lem940073)). Qed.
Lemma lem1765659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765660 : term289 = term9.
Proof. exact (MK_COMB (@lem1765659) (@lem1765658)). Qed.
Lemma lem1765661 : term288 = term9.
Proof. exact (TRANS (@lem1765656) (@lem1765660)). Qed.
Lemma lem1765662 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1765663 : term370 = term372.
Proof. exact (MK_COMB (@lem1765662) (@lem1765661)). Qed.
Lemma lem1765664 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1765665 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1765666 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1765667 : term332 = term333.
Proof. exact (EQ_MP (@lem1765666) (@lem1765665)). Qed.
Lemma lem1765668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765669 : term334 = term335.
Proof. exact (MK_COMB (@lem1765668) (@lem1765667)). Qed.
Lemma lem1765670 : term372 = term335.
Proof. exact (TRANS (@lem1765664) (@lem1765669)). Qed.
Lemma lem1765671 : term370 = term335.
Proof. exact (TRANS (@lem1765663) (@lem1765670)). Qed.
Lemma lem1765673 : term369 = term335.
Proof. exact (TRANS (@lem1765653) (@lem1765671)). Qed.
Lemma lem1765674 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765675 : term373 = term336.
Proof. exact (MK_COMB (@lem1765674) (@lem1765673)). Qed.
Lemma lem1765676 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1765678 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765679 : term374 = term375.
Proof. exact (@lem1765678 term277 term333). Qed.
Lemma lem1765680 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1765681 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1765682 : term342 = term333.
Proof. exact (EQ_MP (@lem1765681) (@lem1765680)). Qed.
Lemma lem1765683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765684 : term340 = term335.
Proof. exact (MK_COMB (@lem1765683) (@lem1765682)). Qed.
Lemma lem1765685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765686 : term375 = term336.
Proof. exact (MK_COMB (@lem1765685) (@lem1765684)). Qed.
Lemma lem1765687 : term374 = term336.
Proof. exact (TRANS (@lem1765679) (@lem1765686)). Qed.
Lemma lem1765688 : term336 = term336.
Proof. exact (TRANS (@lem1765676) (@lem1765687)). Qed.
Lemma lem1765689 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1765690 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1765689) (@lem1765688)). Qed.
Lemma lem1765691 : term373 = term336.
Proof. exact (EQ_MP (@lem1765690) (@lem1765675)). Qed.
Lemma lem1765692 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765693 : term377 = term349.
Proof. exact (MK_COMB (@lem1765692) (@lem1765691)). Qed.
Lemma lem1765694 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765695 : term378 = term351.
Proof. exact (MK_COMB (@lem1765693) (@lem1765694)). Qed.
Lemma lem1765696 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765697 : term379 = term345.
Proof. exact (MK_COMB (@lem1765696) (@lem1765673)). Qed.
Lemma lem1765698 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765699 : term380 = term347.
Proof. exact (MK_COMB (@lem1765697) (@lem1765698)). Qed.
Lemma lem1765700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765701 : term381 = term382.
Proof. exact (MK_COMB (@lem1765700) (@lem1765699)). Qed.
Lemma lem1765702 : term368 = term383.
Proof. exact (MK_COMB (@lem1765701) (@lem1765695)). Qed.
Lemma lem1765703 : term160 = term383.
Proof. exact (TRANS (@lem1765647) (@lem1765702)). Qed.
Lemma lem1765704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765705 : term159 = term384.
Proof. exact (MK_COMB (@lem1765704) (@lem1765646)). Qed.
Lemma lem1765706 : term161 = term385.
Proof. exact (MK_COMB (@lem1765705) (@lem1765703)). Qed.
Lemma lem1765707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765708 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1765707) (@lem1765625 x)). Qed.
Lemma lem1765709 (x : real) : (term205 x) = (term387 x).
Proof. exact (MK_COMB (@lem1765708 x) (@lem1765706)). Qed.
Lemma lem1765710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765711 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1765710) (@lem1765606 x)). Qed.
Lemma lem1765712 (x : real) : (term209 x) = (term411 x).
Proof. exact (MK_COMB (@lem1765711 x) (@lem1765709 x)). Qed.
Lemma lem1765713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765714 : term153 = term412.
Proof. exact (MK_COMB (@lem1765713) (@lem1765501)). Qed.
Lemma lem1765715 (x : real) : (term210 x) = (term413 x).
Proof. exact (MK_COMB (@lem1765714) (@lem1765712 x)). Qed.
Lemma lem1765716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765717 (x : real) : (term208 x) = (term414 x).
Proof. exact (MK_COMB (@lem1765716) (@lem1765480 x)). Qed.
Lemma lem1765718 (x : real) : (term211 x) = (term415 x).
Proof. exact (MK_COMB (@lem1765717 x) (@lem1765715 x)). Qed.
Lemma lem1765719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765720 (x : real) : (term195 x) = (term416 x).
Proof. exact (MK_COMB (@lem1765719) (@lem1765229 x)). Qed.
Lemma lem1765721 (x : real) : (term212 x) = (term417 x).
Proof. exact (MK_COMB (@lem1765720 x) (@lem1765718 x)). Qed.
Lemma lem1765722 (x : real) : (term418 x) = (term419 x).
Proof. exact (@lem1483531 x term14). Qed.
Lemma lem1765728 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1765730 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765731 : term276 = term14.
Proof. exact (@lem1765730 term277). Qed.
Lemma lem1765732 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1765733 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1765732 x) (@lem1765731)). Qed.
Lemma lem1765734 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1765735 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1765733 x) (@lem1765734 x)). Qed.
Lemma lem1765737 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1765728 x) (@lem1765735 x)). Qed.
Lemma lem1765738 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765739 (x : real) : (term420 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1765738) (@lem1765737 x)). Qed.
Lemma lem1765740 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765741 (x : real) : (term419 x) = (term421 x).
Proof. exact (MK_COMB (@lem1765739 x) (@lem1765740)). Qed.
Lemma lem1765742 (x : real) : (term418 x) = (term421 x).
Proof. exact (TRANS (@lem1765722 x) (@lem1765741 x)). Qed.
Lemma lem1765743 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1765749 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765751 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765752 : term308 = term309.
Proof. exact (@lem1765751 term277 term277). Qed.
Lemma lem1765753 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765754 : term291 = term277.
Proof. exact (EQ_MP (@lem1765753) (@lem940073)). Qed.
Lemma lem1765755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765756 : term289 = term9.
Proof. exact (MK_COMB (@lem1765755) (@lem1765754)). Qed.
Lemma lem1765757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765758 : term309 = term19.
Proof. exact (MK_COMB (@lem1765757) (@lem1765756)). Qed.
Lemma lem1765759 : term308 = term19.
Proof. exact (TRANS (@lem1765752) (@lem1765758)). Qed.
Lemma lem1765760 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765761 : term305 = term310.
Proof. exact (MK_COMB (@lem1765760) (@lem1765759)). Qed.
Lemma lem1765762 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765763 : term305 = term19.
Proof. exact (TRANS (@lem1765761) (@lem1765762)). Qed.
Lemma lem1765765 : term304 = term19.
Proof. exact (TRANS (@lem1765749) (@lem1765763)). Qed.
Lemma lem1765766 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765767 : term311 = term312.
Proof. exact (MK_COMB (@lem1765766) (@lem1765765)). Qed.
Lemma lem1765768 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765769 : term303 = term313.
Proof. exact (MK_COMB (@lem1765767) (@lem1765768)). Qed.
Lemma lem1765770 : term90 = term313.
Proof. exact (TRANS (@lem1765743) (@lem1765769)). Qed.
Lemma lem1765771 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1765777 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1765779 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765780 : term276 = term14.
Proof. exact (@lem1765779 term277). Qed.
Lemma lem1765781 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1765782 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1765781 x) (@lem1765780)). Qed.
Lemma lem1765783 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1765784 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1765782 x) (@lem1765783 x)). Qed.
Lemma lem1765786 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1765777 x) (@lem1765784 x)). Qed.
Lemma lem1765787 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765788 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1765787) (@lem1765786 x)). Qed.
Lemma lem1765789 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765790 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1765788 x) (@lem1765789)). Qed.
Lemma lem1765791 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1765771 x) (@lem1765790 x)). Qed.
Lemma lem1765792 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1765798 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765800 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765801 : term308 = term309.
Proof. exact (@lem1765800 term277 term277). Qed.
Lemma lem1765802 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765803 : term291 = term277.
Proof. exact (EQ_MP (@lem1765802) (@lem940073)). Qed.
Lemma lem1765804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765805 : term289 = term9.
Proof. exact (MK_COMB (@lem1765804) (@lem1765803)). Qed.
Lemma lem1765806 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765807 : term309 = term19.
Proof. exact (MK_COMB (@lem1765806) (@lem1765805)). Qed.
Lemma lem1765808 : term308 = term19.
Proof. exact (TRANS (@lem1765801) (@lem1765807)). Qed.
Lemma lem1765809 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765810 : term305 = term310.
Proof. exact (MK_COMB (@lem1765809) (@lem1765808)). Qed.
Lemma lem1765811 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765812 : term305 = term19.
Proof. exact (TRANS (@lem1765810) (@lem1765811)). Qed.
Lemma lem1765814 : term304 = term19.
Proof. exact (TRANS (@lem1765798) (@lem1765812)). Qed.
Lemma lem1765815 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765816 : term321 = term322.
Proof. exact (MK_COMB (@lem1765815) (@lem1765814)). Qed.
Lemma lem1765817 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765818 : term320 = term323.
Proof. exact (MK_COMB (@lem1765816) (@lem1765817)). Qed.
Lemma lem1765819 : term87 = term323.
Proof. exact (TRANS (@lem1765792) (@lem1765818)). Qed.
Lemma lem1765820 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1765826 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1765828 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765829 : term308 = term309.
Proof. exact (@lem1765828 term277 term277). Qed.
Lemma lem1765830 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765831 : term291 = term277.
Proof. exact (EQ_MP (@lem1765830) (@lem940073)). Qed.
Lemma lem1765832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765833 : term289 = term9.
Proof. exact (MK_COMB (@lem1765832) (@lem1765831)). Qed.
Lemma lem1765834 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765835 : term309 = term19.
Proof. exact (MK_COMB (@lem1765834) (@lem1765833)). Qed.
Lemma lem1765836 : term308 = term19.
Proof. exact (TRANS (@lem1765829) (@lem1765835)). Qed.
Lemma lem1765837 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1765838 : term326 = term328.
Proof. exact (MK_COMB (@lem1765837) (@lem1765836)). Qed.
Lemma lem1765839 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1765840 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1765841 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1765842 : term332 = term333.
Proof. exact (EQ_MP (@lem1765841) (@lem1765840)). Qed.
Lemma lem1765843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765844 : term334 = term335.
Proof. exact (MK_COMB (@lem1765843) (@lem1765842)). Qed.
Lemma lem1765845 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765846 : term329 = term336.
Proof. exact (MK_COMB (@lem1765845) (@lem1765844)). Qed.
Lemma lem1765847 : term328 = term336.
Proof. exact (TRANS (@lem1765839) (@lem1765846)). Qed.
Lemma lem1765848 : term326 = term336.
Proof. exact (TRANS (@lem1765838) (@lem1765847)). Qed.
Lemma lem1765850 : term325 = term336.
Proof. exact (TRANS (@lem1765826) (@lem1765848)). Qed.
Lemma lem1765851 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765852 : term337 = term338.
Proof. exact (MK_COMB (@lem1765851) (@lem1765850)). Qed.
Lemma lem1765853 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1765855 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765856 : term339 = term340.
Proof. exact (@lem1765855 term277 term333). Qed.
Lemma lem1765857 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1765858 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1765859 : term342 = term333.
Proof. exact (EQ_MP (@lem1765858) (@lem1765857)). Qed.
Lemma lem1765860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765861 : term340 = term335.
Proof. exact (MK_COMB (@lem1765860) (@lem1765859)). Qed.
Lemma lem1765862 : term339 = term335.
Proof. exact (TRANS (@lem1765856) (@lem1765861)). Qed.
Lemma lem1765863 : term338 = term335.
Proof. exact (TRANS (@lem1765853) (@lem1765862)). Qed.
Lemma lem1765864 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1765865 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1765864) (@lem1765863)). Qed.
Lemma lem1765866 : term337 = term335.
Proof. exact (EQ_MP (@lem1765865) (@lem1765852)). Qed.
Lemma lem1765867 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765868 : term344 = term345.
Proof. exact (MK_COMB (@lem1765867) (@lem1765866)). Qed.
Lemma lem1765869 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765870 : term346 = term347.
Proof. exact (MK_COMB (@lem1765868) (@lem1765869)). Qed.
Lemma lem1765871 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765872 : term348 = term349.
Proof. exact (MK_COMB (@lem1765871) (@lem1765850)). Qed.
Lemma lem1765873 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765874 : term350 = term351.
Proof. exact (MK_COMB (@lem1765872) (@lem1765873)). Qed.
Lemma lem1765875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1765876 : term352 = term353.
Proof. exact (MK_COMB (@lem1765875) (@lem1765874)). Qed.
Lemma lem1765877 : term324 = term354.
Proof. exact (MK_COMB (@lem1765876) (@lem1765870)). Qed.
Lemma lem1765878 : term118 = term354.
Proof. exact (TRANS (@lem1765820) (@lem1765877)). Qed.
Lemma lem1765879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765880 : term88 = term355.
Proof. exact (MK_COMB (@lem1765879) (@lem1765819)). Qed.
Lemma lem1765881 : term119 = term356.
Proof. exact (MK_COMB (@lem1765880) (@lem1765878)). Qed.
Lemma lem1765882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765883 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1765882) (@lem1765791 x)). Qed.
Lemma lem1765884 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1765883 x) (@lem1765881)). Qed.
Lemma lem1765885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1765886 : term147 = term384.
Proof. exact (MK_COMB (@lem1765885) (@lem1765770)). Qed.
Lemma lem1765887 (x : real) : (term223 x) = (term479 x).
Proof. exact (MK_COMB (@lem1765886) (@lem1765884 x)). Qed.
Lemma lem1765888 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1765894 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1765896 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765897 : term276 = term14.
Proof. exact (@lem1765896 term277). Qed.
Lemma lem1765898 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1765899 : term394 = term395.
Proof. exact (MK_COMB (@lem1765898) (@lem1765897)). Qed.
Lemma lem1765900 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1765901 : term394 = term9.
Proof. exact (TRANS (@lem1765899) (@lem1765900)). Qed.
Lemma lem1765903 : term393 = term9.
Proof. exact (TRANS (@lem1765894) (@lem1765901)). Qed.
Lemma lem1765904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765905 : term396 = term397.
Proof. exact (MK_COMB (@lem1765904) (@lem1765903)). Qed.
Lemma lem1765906 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765907 : term392 = term398.
Proof. exact (MK_COMB (@lem1765905) (@lem1765906)). Qed.
Lemma lem1765908 : term391 = term398.
Proof. exact (TRANS (@lem1765888) (@lem1765907)). Qed.
Lemma lem1765909 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1765915 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1765917 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1765918 : term276 = term14.
Proof. exact (@lem1765917 term277). Qed.
Lemma lem1765919 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1765920 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1765919 x) (@lem1765918)). Qed.
Lemma lem1765921 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1765922 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1765920 x) (@lem1765921 x)). Qed.
Lemma lem1765924 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1765915 x) (@lem1765922 x)). Qed.
Lemma lem1765925 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765926 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1765925) (@lem1765924 x)). Qed.
Lemma lem1765927 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765928 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1765926 x) (@lem1765927)). Qed.
Lemma lem1765929 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1765909 x) (@lem1765928 x)). Qed.
Lemma lem1765930 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1765936 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765938 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765939 : term308 = term309.
Proof. exact (@lem1765938 term277 term277). Qed.
Lemma lem1765940 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765941 : term291 = term277.
Proof. exact (EQ_MP (@lem1765940) (@lem940073)). Qed.
Lemma lem1765942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765943 : term289 = term9.
Proof. exact (MK_COMB (@lem1765942) (@lem1765941)). Qed.
Lemma lem1765944 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765945 : term309 = term19.
Proof. exact (MK_COMB (@lem1765944) (@lem1765943)). Qed.
Lemma lem1765946 : term308 = term19.
Proof. exact (TRANS (@lem1765939) (@lem1765945)). Qed.
Lemma lem1765947 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765948 : term305 = term310.
Proof. exact (MK_COMB (@lem1765947) (@lem1765946)). Qed.
Lemma lem1765949 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765950 : term305 = term19.
Proof. exact (TRANS (@lem1765948) (@lem1765949)). Qed.
Lemma lem1765952 : term304 = term19.
Proof. exact (TRANS (@lem1765936) (@lem1765950)). Qed.
Lemma lem1765953 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1765954 : term321 = term322.
Proof. exact (MK_COMB (@lem1765953) (@lem1765952)). Qed.
Lemma lem1765955 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765956 : term320 = term323.
Proof. exact (MK_COMB (@lem1765954) (@lem1765955)). Qed.
Lemma lem1765957 : term87 = term323.
Proof. exact (TRANS (@lem1765930) (@lem1765956)). Qed.
Lemma lem1765958 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1765964 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1765966 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1765967 : term308 = term309.
Proof. exact (@lem1765966 term277 term277). Qed.
Lemma lem1765968 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765969 : term291 = term277.
Proof. exact (EQ_MP (@lem1765968) (@lem940073)). Qed.
Lemma lem1765970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765971 : term289 = term9.
Proof. exact (MK_COMB (@lem1765970) (@lem1765969)). Qed.
Lemma lem1765972 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765973 : term309 = term19.
Proof. exact (MK_COMB (@lem1765972) (@lem1765971)). Qed.
Lemma lem1765974 : term308 = term19.
Proof. exact (TRANS (@lem1765967) (@lem1765973)). Qed.
Lemma lem1765975 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1765976 : term305 = term310.
Proof. exact (MK_COMB (@lem1765975) (@lem1765974)). Qed.
Lemma lem1765977 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1765978 : term305 = term19.
Proof. exact (TRANS (@lem1765976) (@lem1765977)). Qed.
Lemma lem1765980 : term304 = term19.
Proof. exact (TRANS (@lem1765964) (@lem1765978)). Qed.
Lemma lem1765981 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1765982 : term400 = term401.
Proof. exact (MK_COMB (@lem1765981) (@lem1765980)). Qed.
Lemma lem1765983 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1765985 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1765986 : term288 = term289.
Proof. exact (@lem1765985 term277 term277). Qed.
Lemma lem1765987 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1765988 : term291 = term277.
Proof. exact (EQ_MP (@lem1765987) (@lem940073)). Qed.
Lemma lem1765989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1765990 : term289 = term9.
Proof. exact (MK_COMB (@lem1765989) (@lem1765988)). Qed.
Lemma lem1765991 : term288 = term9.
Proof. exact (TRANS (@lem1765986) (@lem1765990)). Qed.
Lemma lem1765992 : term401 = term9.
Proof. exact (TRANS (@lem1765983) (@lem1765991)). Qed.
Lemma lem1765993 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1765994 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1765993) (@lem1765992)). Qed.
Lemma lem1765995 : term400 = term9.
Proof. exact (EQ_MP (@lem1765994) (@lem1765982)). Qed.
Lemma lem1765996 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1765997 : term403 = term294.
Proof. exact (MK_COMB (@lem1765996) (@lem1765995)). Qed.
Lemma lem1765998 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1765999 : term404 = term295.
Proof. exact (MK_COMB (@lem1765997) (@lem1765998)). Qed.
Lemma lem1766000 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766001 : term311 = term312.
Proof. exact (MK_COMB (@lem1766000) (@lem1765980)). Qed.
Lemma lem1766002 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766003 : term303 = term313.
Proof. exact (MK_COMB (@lem1766001) (@lem1766002)). Qed.
Lemma lem1766004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766005 : term405 = term406.
Proof. exact (MK_COMB (@lem1766004) (@lem1766003)). Qed.
Lemma lem1766006 : term399 = term407.
Proof. exact (MK_COMB (@lem1766005) (@lem1765999)). Qed.
Lemma lem1766007 : term105 = term407.
Proof. exact (TRANS (@lem1765958) (@lem1766006)). Qed.
Lemma lem1766008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766009 : term88 = term355.
Proof. exact (MK_COMB (@lem1766008) (@lem1765957)). Qed.
Lemma lem1766010 : term106 = term408.
Proof. exact (MK_COMB (@lem1766009) (@lem1766007)). Qed.
Lemma lem1766011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766012 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1766011) (@lem1765929 x)). Qed.
Lemma lem1766013 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1766012 x) (@lem1766010)). Qed.
Lemma lem1766014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766015 : term153 = term412.
Proof. exact (MK_COMB (@lem1766014) (@lem1765908)). Qed.
Lemma lem1766016 (x : real) : (term226 x) = (term480 x).
Proof. exact (MK_COMB (@lem1766015) (@lem1766013 x)). Qed.
Lemma lem1766017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766018 (x : real) : (term224 x) = (term481 x).
Proof. exact (MK_COMB (@lem1766017) (@lem1765887 x)). Qed.
Lemma lem1766019 (x : real) : (term227 x) = (term482 x).
Proof. exact (MK_COMB (@lem1766018 x) (@lem1766016 x)). Qed.
Lemma lem1766020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766021 (x : real) : (term228 x) = (term439 x).
Proof. exact (MK_COMB (@lem1766020) (@lem1765742 x)). Qed.
Lemma lem1766022 (x : real) : (term229 x) = (term483 x).
Proof. exact (MK_COMB (@lem1766021 x) (@lem1766019 x)). Qed.
Lemma lem1766023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766024 (x : real) : (term213 x) = (term441 x).
Proof. exact (MK_COMB (@lem1766023) (@lem1765721 x)). Qed.
Lemma lem1766025 (x : real) : (term230 x) = (term484 x).
Proof. exact (MK_COMB (@lem1766024 x) (@lem1766022 x)). Qed.
Lemma lem1766026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766027 : term231 = term443.
Proof. exact (MK_COMB (@lem1766026) (@lem1765210)). Qed.
Lemma lem1766028 (x : real) : (term233 x) = (term485 x).
Proof. exact (MK_COMB (@lem1766027) (@lem1766025 x)). Qed.
Lemma lem1766029 : term445 = term446.
Proof. exact (@lem1483531 term19 term14). Qed.
Lemma lem1766035 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1766037 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766038 : term276 = term14.
Proof. exact (@lem1766037 term277). Qed.
Lemma lem1766039 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1766040 : term365 = term366.
Proof. exact (MK_COMB (@lem1766039) (@lem1766038)). Qed.
Lemma lem1766041 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1766042 : term365 = term19.
Proof. exact (TRANS (@lem1766040) (@lem1766041)). Qed.
Lemma lem1766044 : term364 = term19.
Proof. exact (TRANS (@lem1766035) (@lem1766042)). Qed.
Lemma lem1766045 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766046 : term447 = term322.
Proof. exact (MK_COMB (@lem1766045) (@lem1766044)). Qed.
Lemma lem1766047 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766048 : term446 = term323.
Proof. exact (MK_COMB (@lem1766046) (@lem1766047)). Qed.
Lemma lem1766049 : term445 = term323.
Proof. exact (TRANS (@lem1766029) (@lem1766048)). Qed.
Lemma lem1766050 (x : real) : (term127 x) = (term296 x).
Proof. exact (@lem1483521 term14 x). Qed.
Lemma lem1766056 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1766061 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1766063 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1766056 x) (@lem1766061 x)). Qed.
Lemma lem1766064 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766065 (x : real) : (term300 x) = (term301 x).
Proof. exact (MK_COMB (@lem1766064) (@lem1766063 x)). Qed.
Lemma lem1766066 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766067 (x : real) : (term296 x) = (term302 x).
Proof. exact (MK_COMB (@lem1766065 x) (@lem1766066)). Qed.
Lemma lem1766068 (x : real) : (term127 x) = (term302 x).
Proof. exact (TRANS (@lem1766050 x) (@lem1766067 x)). Qed.
Lemma lem1766069 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1766075 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766077 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766078 : term308 = term309.
Proof. exact (@lem1766077 term277 term277). Qed.
Lemma lem1766079 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766080 : term291 = term277.
Proof. exact (EQ_MP (@lem1766079) (@lem940073)). Qed.
Lemma lem1766081 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766082 : term289 = term9.
Proof. exact (MK_COMB (@lem1766081) (@lem1766080)). Qed.
Lemma lem1766083 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766084 : term309 = term19.
Proof. exact (MK_COMB (@lem1766083) (@lem1766082)). Qed.
Lemma lem1766085 : term308 = term19.
Proof. exact (TRANS (@lem1766078) (@lem1766084)). Qed.
Lemma lem1766086 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766087 : term305 = term310.
Proof. exact (MK_COMB (@lem1766086) (@lem1766085)). Qed.
Lemma lem1766088 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766089 : term305 = term19.
Proof. exact (TRANS (@lem1766087) (@lem1766088)). Qed.
Lemma lem1766091 : term304 = term19.
Proof. exact (TRANS (@lem1766075) (@lem1766089)). Qed.
Lemma lem1766092 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766093 : term311 = term312.
Proof. exact (MK_COMB (@lem1766092) (@lem1766091)). Qed.
Lemma lem1766094 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766095 : term303 = term313.
Proof. exact (MK_COMB (@lem1766093) (@lem1766094)). Qed.
Lemma lem1766096 : term90 = term313.
Proof. exact (TRANS (@lem1766069) (@lem1766095)). Qed.
Lemma lem1766097 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1766103 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1766105 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766106 : term276 = term14.
Proof. exact (@lem1766105 term277). Qed.
Lemma lem1766107 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1766108 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1766107 x) (@lem1766106)). Qed.
Lemma lem1766109 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1766110 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1766108 x) (@lem1766109 x)). Qed.
Lemma lem1766112 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1766103 x) (@lem1766110 x)). Qed.
Lemma lem1766113 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766114 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1766113) (@lem1766112 x)). Qed.
Lemma lem1766115 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766116 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1766114 x) (@lem1766115)). Qed.
Lemma lem1766117 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1766097 x) (@lem1766116 x)). Qed.
Lemma lem1766118 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1766124 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766126 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766127 : term308 = term309.
Proof. exact (@lem1766126 term277 term277). Qed.
Lemma lem1766128 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766129 : term291 = term277.
Proof. exact (EQ_MP (@lem1766128) (@lem940073)). Qed.
Lemma lem1766130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766131 : term289 = term9.
Proof. exact (MK_COMB (@lem1766130) (@lem1766129)). Qed.
Lemma lem1766132 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766133 : term309 = term19.
Proof. exact (MK_COMB (@lem1766132) (@lem1766131)). Qed.
Lemma lem1766134 : term308 = term19.
Proof. exact (TRANS (@lem1766127) (@lem1766133)). Qed.
Lemma lem1766135 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766136 : term305 = term310.
Proof. exact (MK_COMB (@lem1766135) (@lem1766134)). Qed.
Lemma lem1766137 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766138 : term305 = term19.
Proof. exact (TRANS (@lem1766136) (@lem1766137)). Qed.
Lemma lem1766140 : term304 = term19.
Proof. exact (TRANS (@lem1766124) (@lem1766138)). Qed.
Lemma lem1766141 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766142 : term321 = term322.
Proof. exact (MK_COMB (@lem1766141) (@lem1766140)). Qed.
Lemma lem1766143 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766144 : term320 = term323.
Proof. exact (MK_COMB (@lem1766142) (@lem1766143)). Qed.
Lemma lem1766145 : term87 = term323.
Proof. exact (TRANS (@lem1766118) (@lem1766144)). Qed.
Lemma lem1766146 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1766152 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1766154 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766155 : term308 = term309.
Proof. exact (@lem1766154 term277 term277). Qed.
Lemma lem1766156 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766157 : term291 = term277.
Proof. exact (EQ_MP (@lem1766156) (@lem940073)). Qed.
Lemma lem1766158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766159 : term289 = term9.
Proof. exact (MK_COMB (@lem1766158) (@lem1766157)). Qed.
Lemma lem1766160 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766161 : term309 = term19.
Proof. exact (MK_COMB (@lem1766160) (@lem1766159)). Qed.
Lemma lem1766162 : term308 = term19.
Proof. exact (TRANS (@lem1766155) (@lem1766161)). Qed.
Lemma lem1766163 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1766164 : term326 = term328.
Proof. exact (MK_COMB (@lem1766163) (@lem1766162)). Qed.
Lemma lem1766165 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1766166 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1766167 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1766168 : term332 = term333.
Proof. exact (EQ_MP (@lem1766167) (@lem1766166)). Qed.
Lemma lem1766169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766170 : term334 = term335.
Proof. exact (MK_COMB (@lem1766169) (@lem1766168)). Qed.
Lemma lem1766171 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766172 : term329 = term336.
Proof. exact (MK_COMB (@lem1766171) (@lem1766170)). Qed.
Lemma lem1766173 : term328 = term336.
Proof. exact (TRANS (@lem1766165) (@lem1766172)). Qed.
Lemma lem1766174 : term326 = term336.
Proof. exact (TRANS (@lem1766164) (@lem1766173)). Qed.
Lemma lem1766176 : term325 = term336.
Proof. exact (TRANS (@lem1766152) (@lem1766174)). Qed.
Lemma lem1766177 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766178 : term337 = term338.
Proof. exact (MK_COMB (@lem1766177) (@lem1766176)). Qed.
Lemma lem1766179 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1766181 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766182 : term339 = term340.
Proof. exact (@lem1766181 term277 term333). Qed.
Lemma lem1766183 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1766184 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1766185 : term342 = term333.
Proof. exact (EQ_MP (@lem1766184) (@lem1766183)). Qed.
Lemma lem1766186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766187 : term340 = term335.
Proof. exact (MK_COMB (@lem1766186) (@lem1766185)). Qed.
Lemma lem1766188 : term339 = term335.
Proof. exact (TRANS (@lem1766182) (@lem1766187)). Qed.
Lemma lem1766189 : term338 = term335.
Proof. exact (TRANS (@lem1766179) (@lem1766188)). Qed.
Lemma lem1766190 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1766191 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1766190) (@lem1766189)). Qed.
Lemma lem1766192 : term337 = term335.
Proof. exact (EQ_MP (@lem1766191) (@lem1766178)). Qed.
Lemma lem1766193 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766194 : term344 = term345.
Proof. exact (MK_COMB (@lem1766193) (@lem1766192)). Qed.
Lemma lem1766195 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766196 : term346 = term347.
Proof. exact (MK_COMB (@lem1766194) (@lem1766195)). Qed.
Lemma lem1766197 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766198 : term348 = term349.
Proof. exact (MK_COMB (@lem1766197) (@lem1766176)). Qed.
Lemma lem1766199 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766200 : term350 = term351.
Proof. exact (MK_COMB (@lem1766198) (@lem1766199)). Qed.
Lemma lem1766201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766202 : term352 = term353.
Proof. exact (MK_COMB (@lem1766201) (@lem1766200)). Qed.
Lemma lem1766203 : term324 = term354.
Proof. exact (MK_COMB (@lem1766202) (@lem1766196)). Qed.
Lemma lem1766204 : term118 = term354.
Proof. exact (TRANS (@lem1766146) (@lem1766203)). Qed.
Lemma lem1766205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766206 : term88 = term355.
Proof. exact (MK_COMB (@lem1766205) (@lem1766145)). Qed.
Lemma lem1766207 : term119 = term356.
Proof. exact (MK_COMB (@lem1766206) (@lem1766204)). Qed.
Lemma lem1766208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766209 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1766208) (@lem1766117 x)). Qed.
Lemma lem1766210 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1766209 x) (@lem1766207)). Qed.
Lemma lem1766211 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1766217 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1766222 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1766224 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1766217 x) (@lem1766222 x)). Qed.
Lemma lem1766225 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766226 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1766225) (@lem1766224 x)). Qed.
Lemma lem1766227 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766228 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1766226 x) (@lem1766227)). Qed.
Lemma lem1766229 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1766211 x) (@lem1766228 x)). Qed.
Lemma lem1766230 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1766236 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1766238 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766239 : term276 = term14.
Proof. exact (@lem1766238 term277). Qed.
Lemma lem1766240 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1766241 : term365 = term366.
Proof. exact (MK_COMB (@lem1766240) (@lem1766239)). Qed.
Lemma lem1766242 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1766243 : term365 = term19.
Proof. exact (TRANS (@lem1766241) (@lem1766242)). Qed.
Lemma lem1766245 : term364 = term19.
Proof. exact (TRANS (@lem1766236) (@lem1766243)). Qed.
Lemma lem1766246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766247 : term367 = term312.
Proof. exact (MK_COMB (@lem1766246) (@lem1766245)). Qed.
Lemma lem1766248 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766249 : term363 = term313.
Proof. exact (MK_COMB (@lem1766247) (@lem1766248)). Qed.
Lemma lem1766250 : term158 = term313.
Proof. exact (TRANS (@lem1766230) (@lem1766249)). Qed.
Lemma lem1766251 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1766257 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1766259 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766260 : term288 = term289.
Proof. exact (@lem1766259 term277 term277). Qed.
Lemma lem1766261 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766262 : term291 = term277.
Proof. exact (EQ_MP (@lem1766261) (@lem940073)). Qed.
Lemma lem1766263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766264 : term289 = term9.
Proof. exact (MK_COMB (@lem1766263) (@lem1766262)). Qed.
Lemma lem1766265 : term288 = term9.
Proof. exact (TRANS (@lem1766260) (@lem1766264)). Qed.
Lemma lem1766266 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1766267 : term370 = term372.
Proof. exact (MK_COMB (@lem1766266) (@lem1766265)). Qed.
Lemma lem1766268 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1766269 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1766270 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1766271 : term332 = term333.
Proof. exact (EQ_MP (@lem1766270) (@lem1766269)). Qed.
Lemma lem1766272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766273 : term334 = term335.
Proof. exact (MK_COMB (@lem1766272) (@lem1766271)). Qed.
Lemma lem1766274 : term372 = term335.
Proof. exact (TRANS (@lem1766268) (@lem1766273)). Qed.
Lemma lem1766275 : term370 = term335.
Proof. exact (TRANS (@lem1766267) (@lem1766274)). Qed.
Lemma lem1766277 : term369 = term335.
Proof. exact (TRANS (@lem1766257) (@lem1766275)). Qed.
Lemma lem1766278 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766279 : term373 = term336.
Proof. exact (MK_COMB (@lem1766278) (@lem1766277)). Qed.
Lemma lem1766280 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1766282 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766283 : term374 = term375.
Proof. exact (@lem1766282 term277 term333). Qed.
Lemma lem1766284 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1766285 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1766286 : term342 = term333.
Proof. exact (EQ_MP (@lem1766285) (@lem1766284)). Qed.
Lemma lem1766287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766288 : term340 = term335.
Proof. exact (MK_COMB (@lem1766287) (@lem1766286)). Qed.
Lemma lem1766289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766290 : term375 = term336.
Proof. exact (MK_COMB (@lem1766289) (@lem1766288)). Qed.
Lemma lem1766291 : term374 = term336.
Proof. exact (TRANS (@lem1766283) (@lem1766290)). Qed.
Lemma lem1766292 : term336 = term336.
Proof. exact (TRANS (@lem1766280) (@lem1766291)). Qed.
Lemma lem1766293 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1766294 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1766293) (@lem1766292)). Qed.
Lemma lem1766295 : term373 = term336.
Proof. exact (EQ_MP (@lem1766294) (@lem1766279)). Qed.
Lemma lem1766296 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766297 : term377 = term349.
Proof. exact (MK_COMB (@lem1766296) (@lem1766295)). Qed.
Lemma lem1766298 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766299 : term378 = term351.
Proof. exact (MK_COMB (@lem1766297) (@lem1766298)). Qed.
Lemma lem1766300 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766301 : term379 = term345.
Proof. exact (MK_COMB (@lem1766300) (@lem1766277)). Qed.
Lemma lem1766302 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766303 : term380 = term347.
Proof. exact (MK_COMB (@lem1766301) (@lem1766302)). Qed.
Lemma lem1766304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766305 : term381 = term382.
Proof. exact (MK_COMB (@lem1766304) (@lem1766303)). Qed.
Lemma lem1766306 : term368 = term383.
Proof. exact (MK_COMB (@lem1766305) (@lem1766299)). Qed.
Lemma lem1766307 : term160 = term383.
Proof. exact (TRANS (@lem1766251) (@lem1766306)). Qed.
Lemma lem1766308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766309 : term159 = term384.
Proof. exact (MK_COMB (@lem1766308) (@lem1766250)). Qed.
Lemma lem1766310 : term161 = term385.
Proof. exact (MK_COMB (@lem1766309) (@lem1766307)). Qed.
Lemma lem1766311 : term163 = term448.
Proof. exact (@lem1483531 term14 term19). Qed.
Lemma lem1766317 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1766319 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766320 : term288 = term289.
Proof. exact (@lem1766319 term277 term277). Qed.
Lemma lem1766321 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766322 : term291 = term277.
Proof. exact (EQ_MP (@lem1766321) (@lem940073)). Qed.
Lemma lem1766323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766324 : term289 = term9.
Proof. exact (MK_COMB (@lem1766323) (@lem1766322)). Qed.
Lemma lem1766325 : term288 = term9.
Proof. exact (TRANS (@lem1766320) (@lem1766324)). Qed.
Lemma lem1766326 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766327 : term285 = term292.
Proof. exact (MK_COMB (@lem1766326) (@lem1766325)). Qed.
Lemma lem1766328 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1766329 : term285 = term9.
Proof. exact (TRANS (@lem1766327) (@lem1766328)). Qed.
Lemma lem1766331 : term284 = term9.
Proof. exact (TRANS (@lem1766317) (@lem1766329)). Qed.
Lemma lem1766332 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766333 : term449 = term397.
Proof. exact (MK_COMB (@lem1766332) (@lem1766331)). Qed.
Lemma lem1766334 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766335 : term448 = term398.
Proof. exact (MK_COMB (@lem1766333) (@lem1766334)). Qed.
Lemma lem1766336 : term163 = term398.
Proof. exact (TRANS (@lem1766311) (@lem1766335)). Qed.
Lemma lem1766337 : term185 = term450.
Proof. exact (@lem1483554 term14 term19). Qed.
Lemma lem1766343 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1766345 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766346 : term288 = term289.
Proof. exact (@lem1766345 term277 term277). Qed.
Lemma lem1766347 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766348 : term291 = term277.
Proof. exact (EQ_MP (@lem1766347) (@lem940073)). Qed.
Lemma lem1766349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766350 : term289 = term9.
Proof. exact (MK_COMB (@lem1766349) (@lem1766348)). Qed.
Lemma lem1766351 : term288 = term9.
Proof. exact (TRANS (@lem1766346) (@lem1766350)). Qed.
Lemma lem1766352 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766353 : term285 = term292.
Proof. exact (MK_COMB (@lem1766352) (@lem1766351)). Qed.
Lemma lem1766354 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1766355 : term285 = term9.
Proof. exact (TRANS (@lem1766353) (@lem1766354)). Qed.
Lemma lem1766357 : term284 = term9.
Proof. exact (TRANS (@lem1766343) (@lem1766355)). Qed.
Lemma lem1766358 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766359 : term451 = term19.
Proof. exact (MK_COMB (@lem1766358) (@lem1766357)). Qed.
Lemma lem1766360 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1766362 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766363 : term308 = term309.
Proof. exact (@lem1766362 term277 term277). Qed.
Lemma lem1766364 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766365 : term291 = term277.
Proof. exact (EQ_MP (@lem1766364) (@lem940073)). Qed.
Lemma lem1766366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766367 : term289 = term9.
Proof. exact (MK_COMB (@lem1766366) (@lem1766365)). Qed.
Lemma lem1766368 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766369 : term309 = term19.
Proof. exact (MK_COMB (@lem1766368) (@lem1766367)). Qed.
Lemma lem1766370 : term308 = term19.
Proof. exact (TRANS (@lem1766363) (@lem1766369)). Qed.
Lemma lem1766371 : term19 = term19.
Proof. exact (TRANS (@lem1766360) (@lem1766370)). Qed.
Lemma lem1766372 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem1766373 : (term451 = term19) = (term451 = term19).
Proof. exact (MK_COMB (@lem1766372) (@lem1766371)). Qed.
Lemma lem1766374 : term451 = term19.
Proof. exact (EQ_MP (@lem1766373) (@lem1766359)). Qed.
Lemma lem1766375 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766376 : term453 = term312.
Proof. exact (MK_COMB (@lem1766375) (@lem1766374)). Qed.
Lemma lem1766377 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766378 : term454 = term313.
Proof. exact (MK_COMB (@lem1766376) (@lem1766377)). Qed.
Lemma lem1766379 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766380 : term293 = term294.
Proof. exact (MK_COMB (@lem1766379) (@lem1766357)). Qed.
Lemma lem1766381 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766382 : term283 = term295.
Proof. exact (MK_COMB (@lem1766380) (@lem1766381)). Qed.
Lemma lem1766383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766384 : term455 = term430.
Proof. exact (MK_COMB (@lem1766383) (@lem1766382)). Qed.
Lemma lem1766385 : term450 = term431.
Proof. exact (MK_COMB (@lem1766384) (@lem1766378)). Qed.
Lemma lem1766386 : term185 = term431.
Proof. exact (TRANS (@lem1766337) (@lem1766385)). Qed.
Lemma lem1766387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766388 : term164 = term412.
Proof. exact (MK_COMB (@lem1766387) (@lem1766336)). Qed.
Lemma lem1766389 : term186 = term456.
Proof. exact (MK_COMB (@lem1766388) (@lem1766386)). Qed.
Lemma lem1766390 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766391 : term162 = term457.
Proof. exact (MK_COMB (@lem1766390) (@lem1766310)). Qed.
Lemma lem1766392 : term187 = term458.
Proof. exact (MK_COMB (@lem1766391) (@lem1766389)). Qed.
Lemma lem1766393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766394 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1766393) (@lem1766229 x)). Qed.
Lemma lem1766395 (x : real) : (term188 x) = (term459 x).
Proof. exact (MK_COMB (@lem1766394 x) (@lem1766392)). Qed.
Lemma lem1766396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766397 (x : real) : (term121 x) = (term388 x).
Proof. exact (MK_COMB (@lem1766396) (@lem1766210 x)). Qed.
Lemma lem1766398 (x : real) : (term189 x) = (term460 x).
Proof. exact (MK_COMB (@lem1766397 x) (@lem1766395 x)). Qed.
Lemma lem1766399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766400 : term147 = term384.
Proof. exact (MK_COMB (@lem1766399) (@lem1766096)). Qed.
Lemma lem1766401 (x : real) : (term190 x) = (term461 x).
Proof. exact (MK_COMB (@lem1766400) (@lem1766398 x)). Qed.
Lemma lem1766402 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1766408 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1766410 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766411 : term276 = term14.
Proof. exact (@lem1766410 term277). Qed.
Lemma lem1766412 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1766413 : term394 = term395.
Proof. exact (MK_COMB (@lem1766412) (@lem1766411)). Qed.
Lemma lem1766414 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1766415 : term394 = term9.
Proof. exact (TRANS (@lem1766413) (@lem1766414)). Qed.
Lemma lem1766417 : term393 = term9.
Proof. exact (TRANS (@lem1766408) (@lem1766415)). Qed.
Lemma lem1766418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766419 : term396 = term397.
Proof. exact (MK_COMB (@lem1766418) (@lem1766417)). Qed.
Lemma lem1766420 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766421 : term392 = term398.
Proof. exact (MK_COMB (@lem1766419) (@lem1766420)). Qed.
Lemma lem1766422 : term391 = term398.
Proof. exact (TRANS (@lem1766402) (@lem1766421)). Qed.
Lemma lem1766423 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1766429 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1766431 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766432 : term276 = term14.
Proof. exact (@lem1766431 term277). Qed.
Lemma lem1766433 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1766434 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1766433 x) (@lem1766432)). Qed.
Lemma lem1766435 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1766436 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1766434 x) (@lem1766435 x)). Qed.
Lemma lem1766438 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1766429 x) (@lem1766436 x)). Qed.
Lemma lem1766439 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766440 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1766439) (@lem1766438 x)). Qed.
Lemma lem1766441 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766442 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1766440 x) (@lem1766441)). Qed.
Lemma lem1766443 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1766423 x) (@lem1766442 x)). Qed.
Lemma lem1766444 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1766450 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766452 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766453 : term308 = term309.
Proof. exact (@lem1766452 term277 term277). Qed.
Lemma lem1766454 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766455 : term291 = term277.
Proof. exact (EQ_MP (@lem1766454) (@lem940073)). Qed.
Lemma lem1766456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766457 : term289 = term9.
Proof. exact (MK_COMB (@lem1766456) (@lem1766455)). Qed.
Lemma lem1766458 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766459 : term309 = term19.
Proof. exact (MK_COMB (@lem1766458) (@lem1766457)). Qed.
Lemma lem1766460 : term308 = term19.
Proof. exact (TRANS (@lem1766453) (@lem1766459)). Qed.
Lemma lem1766461 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766462 : term305 = term310.
Proof. exact (MK_COMB (@lem1766461) (@lem1766460)). Qed.
Lemma lem1766463 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766464 : term305 = term19.
Proof. exact (TRANS (@lem1766462) (@lem1766463)). Qed.
Lemma lem1766466 : term304 = term19.
Proof. exact (TRANS (@lem1766450) (@lem1766464)). Qed.
Lemma lem1766467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766468 : term321 = term322.
Proof. exact (MK_COMB (@lem1766467) (@lem1766466)). Qed.
Lemma lem1766469 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766470 : term320 = term323.
Proof. exact (MK_COMB (@lem1766468) (@lem1766469)). Qed.
Lemma lem1766471 : term87 = term323.
Proof. exact (TRANS (@lem1766444) (@lem1766470)). Qed.
Lemma lem1766472 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1766478 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766480 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766481 : term308 = term309.
Proof. exact (@lem1766480 term277 term277). Qed.
Lemma lem1766482 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766483 : term291 = term277.
Proof. exact (EQ_MP (@lem1766482) (@lem940073)). Qed.
Lemma lem1766484 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766485 : term289 = term9.
Proof. exact (MK_COMB (@lem1766484) (@lem1766483)). Qed.
Lemma lem1766486 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766487 : term309 = term19.
Proof. exact (MK_COMB (@lem1766486) (@lem1766485)). Qed.
Lemma lem1766488 : term308 = term19.
Proof. exact (TRANS (@lem1766481) (@lem1766487)). Qed.
Lemma lem1766489 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766490 : term305 = term310.
Proof. exact (MK_COMB (@lem1766489) (@lem1766488)). Qed.
Lemma lem1766491 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766492 : term305 = term19.
Proof. exact (TRANS (@lem1766490) (@lem1766491)). Qed.
Lemma lem1766494 : term304 = term19.
Proof. exact (TRANS (@lem1766478) (@lem1766492)). Qed.
Lemma lem1766495 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766496 : term400 = term401.
Proof. exact (MK_COMB (@lem1766495) (@lem1766494)). Qed.
Lemma lem1766497 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1766499 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766500 : term288 = term289.
Proof. exact (@lem1766499 term277 term277). Qed.
Lemma lem1766501 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766502 : term291 = term277.
Proof. exact (EQ_MP (@lem1766501) (@lem940073)). Qed.
Lemma lem1766503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766504 : term289 = term9.
Proof. exact (MK_COMB (@lem1766503) (@lem1766502)). Qed.
Lemma lem1766505 : term288 = term9.
Proof. exact (TRANS (@lem1766500) (@lem1766504)). Qed.
Lemma lem1766506 : term401 = term9.
Proof. exact (TRANS (@lem1766497) (@lem1766505)). Qed.
Lemma lem1766507 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1766508 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1766507) (@lem1766506)). Qed.
Lemma lem1766509 : term400 = term9.
Proof. exact (EQ_MP (@lem1766508) (@lem1766496)). Qed.
Lemma lem1766510 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766511 : term403 = term294.
Proof. exact (MK_COMB (@lem1766510) (@lem1766509)). Qed.
Lemma lem1766512 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766513 : term404 = term295.
Proof. exact (MK_COMB (@lem1766511) (@lem1766512)). Qed.
Lemma lem1766514 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766515 : term311 = term312.
Proof. exact (MK_COMB (@lem1766514) (@lem1766494)). Qed.
Lemma lem1766516 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766517 : term303 = term313.
Proof. exact (MK_COMB (@lem1766515) (@lem1766516)). Qed.
Lemma lem1766518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766519 : term405 = term406.
Proof. exact (MK_COMB (@lem1766518) (@lem1766517)). Qed.
Lemma lem1766520 : term399 = term407.
Proof. exact (MK_COMB (@lem1766519) (@lem1766513)). Qed.
Lemma lem1766521 : term105 = term407.
Proof. exact (TRANS (@lem1766472) (@lem1766520)). Qed.
Lemma lem1766522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766523 : term88 = term355.
Proof. exact (MK_COMB (@lem1766522) (@lem1766471)). Qed.
Lemma lem1766524 : term106 = term408.
Proof. exact (MK_COMB (@lem1766523) (@lem1766521)). Qed.
Lemma lem1766525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766526 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1766525) (@lem1766443 x)). Qed.
Lemma lem1766527 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1766526 x) (@lem1766524)). Qed.
Lemma lem1766528 (x : real) : (term221 x) = (term359 x).
Proof. exact (@lem1483531 term14 x). Qed.
Lemma lem1766534 (x : real) : (term297 x) = (term298 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1766539 (x : real) : (term298 x) = (term299 x).
Proof. exact (@lem1483448 (term299 x)). Qed.
Lemma lem1766541 (x : real) : (term297 x) = (term299 x).
Proof. exact (TRANS (@lem1766534 x) (@lem1766539 x)). Qed.
Lemma lem1766542 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766543 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1766542) (@lem1766541 x)). Qed.
Lemma lem1766544 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766545 (x : real) : (term359 x) = (term362 x).
Proof. exact (MK_COMB (@lem1766543 x) (@lem1766544)). Qed.
Lemma lem1766546 (x : real) : (term221 x) = (term362 x).
Proof. exact (TRANS (@lem1766528 x) (@lem1766545 x)). Qed.
Lemma lem1766547 : term158 = term363.
Proof. exact (@lem1483521 term19 term14). Qed.
Lemma lem1766553 : term364 = term365.
Proof. exact (@lem1483519 term19 term14). Qed.
Lemma lem1766555 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766556 : term276 = term14.
Proof. exact (@lem1766555 term277). Qed.
Lemma lem1766557 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1766558 : term365 = term366.
Proof. exact (MK_COMB (@lem1766557) (@lem1766556)). Qed.
Lemma lem1766559 : term366 = term19.
Proof. exact (@lem1483450 term19). Qed.
Lemma lem1766560 : term365 = term19.
Proof. exact (TRANS (@lem1766558) (@lem1766559)). Qed.
Lemma lem1766562 : term364 = term19.
Proof. exact (TRANS (@lem1766553) (@lem1766560)). Qed.
Lemma lem1766563 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766564 : term367 = term312.
Proof. exact (MK_COMB (@lem1766563) (@lem1766562)). Qed.
Lemma lem1766565 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766566 : term363 = term313.
Proof. exact (MK_COMB (@lem1766564) (@lem1766565)). Qed.
Lemma lem1766567 : term158 = term313.
Proof. exact (TRANS (@lem1766547) (@lem1766566)). Qed.
Lemma lem1766568 : term160 = term368.
Proof. exact (@lem1483554 term9 term19). Qed.
Lemma lem1766574 : term369 = term370.
Proof. exact (@lem1483519 term9 term19). Qed.
Lemma lem1766576 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766577 : term288 = term289.
Proof. exact (@lem1766576 term277 term277). Qed.
Lemma lem1766578 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766579 : term291 = term277.
Proof. exact (EQ_MP (@lem1766578) (@lem940073)). Qed.
Lemma lem1766580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766581 : term289 = term9.
Proof. exact (MK_COMB (@lem1766580) (@lem1766579)). Qed.
Lemma lem1766582 : term288 = term9.
Proof. exact (TRANS (@lem1766577) (@lem1766581)). Qed.
Lemma lem1766583 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1766584 : term370 = term372.
Proof. exact (MK_COMB (@lem1766583) (@lem1766582)). Qed.
Lemma lem1766585 : term372 = term334.
Proof. exact (@lem1367770 term277 term277). Qed.
Lemma lem1766586 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1766587 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1766588 : term332 = term333.
Proof. exact (EQ_MP (@lem1766587) (@lem1766586)). Qed.
Lemma lem1766589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766590 : term334 = term335.
Proof. exact (MK_COMB (@lem1766589) (@lem1766588)). Qed.
Lemma lem1766591 : term372 = term335.
Proof. exact (TRANS (@lem1766585) (@lem1766590)). Qed.
Lemma lem1766592 : term370 = term335.
Proof. exact (TRANS (@lem1766584) (@lem1766591)). Qed.
Lemma lem1766594 : term369 = term335.
Proof. exact (TRANS (@lem1766574) (@lem1766592)). Qed.
Lemma lem1766595 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766596 : term373 = term336.
Proof. exact (MK_COMB (@lem1766595) (@lem1766594)). Qed.
Lemma lem1766597 : term336 = term374.
Proof. exact (@lem1483512 term335). Qed.
Lemma lem1766599 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766600 : term374 = term375.
Proof. exact (@lem1766599 term277 term333). Qed.
Lemma lem1766601 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1766602 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1766603 : term342 = term333.
Proof. exact (EQ_MP (@lem1766602) (@lem1766601)). Qed.
Lemma lem1766604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766605 : term340 = term335.
Proof. exact (MK_COMB (@lem1766604) (@lem1766603)). Qed.
Lemma lem1766606 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766607 : term375 = term336.
Proof. exact (MK_COMB (@lem1766606) (@lem1766605)). Qed.
Lemma lem1766608 : term374 = term336.
Proof. exact (TRANS (@lem1766600) (@lem1766607)). Qed.
Lemma lem1766609 : term336 = term336.
Proof. exact (TRANS (@lem1766597) (@lem1766608)). Qed.
Lemma lem1766610 : term376 = term376.
Proof. exact (eq_refl term376). Qed.
Lemma lem1766611 : (term373 = term336) = (term373 = term336).
Proof. exact (MK_COMB (@lem1766610) (@lem1766609)). Qed.
Lemma lem1766612 : term373 = term336.
Proof. exact (EQ_MP (@lem1766611) (@lem1766596)). Qed.
Lemma lem1766613 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766614 : term377 = term349.
Proof. exact (MK_COMB (@lem1766613) (@lem1766612)). Qed.
Lemma lem1766615 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766616 : term378 = term351.
Proof. exact (MK_COMB (@lem1766614) (@lem1766615)). Qed.
Lemma lem1766617 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766618 : term379 = term345.
Proof. exact (MK_COMB (@lem1766617) (@lem1766594)). Qed.
Lemma lem1766619 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766620 : term380 = term347.
Proof. exact (MK_COMB (@lem1766618) (@lem1766619)). Qed.
Lemma lem1766621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766622 : term381 = term382.
Proof. exact (MK_COMB (@lem1766621) (@lem1766620)). Qed.
Lemma lem1766623 : term368 = term383.
Proof. exact (MK_COMB (@lem1766622) (@lem1766616)). Qed.
Lemma lem1766624 : term160 = term383.
Proof. exact (TRANS (@lem1766568) (@lem1766623)). Qed.
Lemma lem1766625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766626 : term159 = term384.
Proof. exact (MK_COMB (@lem1766625) (@lem1766567)). Qed.
Lemma lem1766627 : term161 = term385.
Proof. exact (MK_COMB (@lem1766626) (@lem1766624)). Qed.
Lemma lem1766628 : term163 = term448.
Proof. exact (@lem1483531 term14 term19). Qed.
Lemma lem1766634 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1766636 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766637 : term288 = term289.
Proof. exact (@lem1766636 term277 term277). Qed.
Lemma lem1766638 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766639 : term291 = term277.
Proof. exact (EQ_MP (@lem1766638) (@lem940073)). Qed.
Lemma lem1766640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766641 : term289 = term9.
Proof. exact (MK_COMB (@lem1766640) (@lem1766639)). Qed.
Lemma lem1766642 : term288 = term9.
Proof. exact (TRANS (@lem1766637) (@lem1766641)). Qed.
Lemma lem1766643 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766644 : term285 = term292.
Proof. exact (MK_COMB (@lem1766643) (@lem1766642)). Qed.
Lemma lem1766645 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1766646 : term285 = term9.
Proof. exact (TRANS (@lem1766644) (@lem1766645)). Qed.
Lemma lem1766648 : term284 = term9.
Proof. exact (TRANS (@lem1766634) (@lem1766646)). Qed.
Lemma lem1766649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766650 : term449 = term397.
Proof. exact (MK_COMB (@lem1766649) (@lem1766648)). Qed.
Lemma lem1766651 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766652 : term448 = term398.
Proof. exact (MK_COMB (@lem1766650) (@lem1766651)). Qed.
Lemma lem1766653 : term163 = term398.
Proof. exact (TRANS (@lem1766628) (@lem1766652)). Qed.
Lemma lem1766654 : term185 = term450.
Proof. exact (@lem1483554 term14 term19). Qed.
Lemma lem1766660 : term284 = term285.
Proof. exact (@lem1483519 term14 term19). Qed.
Lemma lem1766662 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766663 : term288 = term289.
Proof. exact (@lem1766662 term277 term277). Qed.
Lemma lem1766664 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766665 : term291 = term277.
Proof. exact (EQ_MP (@lem1766664) (@lem940073)). Qed.
Lemma lem1766666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766667 : term289 = term9.
Proof. exact (MK_COMB (@lem1766666) (@lem1766665)). Qed.
Lemma lem1766668 : term288 = term9.
Proof. exact (TRANS (@lem1766663) (@lem1766667)). Qed.
Lemma lem1766669 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766670 : term285 = term292.
Proof. exact (MK_COMB (@lem1766669) (@lem1766668)). Qed.
Lemma lem1766671 : term292 = term9.
Proof. exact (@lem1483448 term9). Qed.
Lemma lem1766672 : term285 = term9.
Proof. exact (TRANS (@lem1766670) (@lem1766671)). Qed.
Lemma lem1766674 : term284 = term9.
Proof. exact (TRANS (@lem1766660) (@lem1766672)). Qed.
Lemma lem1766675 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766676 : term451 = term19.
Proof. exact (MK_COMB (@lem1766675) (@lem1766674)). Qed.
Lemma lem1766677 : term19 = term308.
Proof. exact (@lem1483512 term9). Qed.
Lemma lem1766679 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766680 : term308 = term309.
Proof. exact (@lem1766679 term277 term277). Qed.
Lemma lem1766681 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766682 : term291 = term277.
Proof. exact (EQ_MP (@lem1766681) (@lem940073)). Qed.
Lemma lem1766683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766684 : term289 = term9.
Proof. exact (MK_COMB (@lem1766683) (@lem1766682)). Qed.
Lemma lem1766685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766686 : term309 = term19.
Proof. exact (MK_COMB (@lem1766685) (@lem1766684)). Qed.
Lemma lem1766687 : term308 = term19.
Proof. exact (TRANS (@lem1766680) (@lem1766686)). Qed.
Lemma lem1766688 : term19 = term19.
Proof. exact (TRANS (@lem1766677) (@lem1766687)). Qed.
Lemma lem1766689 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem1766690 : (term451 = term19) = (term451 = term19).
Proof. exact (MK_COMB (@lem1766689) (@lem1766688)). Qed.
Lemma lem1766691 : term451 = term19.
Proof. exact (EQ_MP (@lem1766690) (@lem1766676)). Qed.
Lemma lem1766692 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766693 : term453 = term312.
Proof. exact (MK_COMB (@lem1766692) (@lem1766691)). Qed.
Lemma lem1766694 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766695 : term454 = term313.
Proof. exact (MK_COMB (@lem1766693) (@lem1766694)). Qed.
Lemma lem1766696 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766697 : term293 = term294.
Proof. exact (MK_COMB (@lem1766696) (@lem1766674)). Qed.
Lemma lem1766698 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766699 : term283 = term295.
Proof. exact (MK_COMB (@lem1766697) (@lem1766698)). Qed.
Lemma lem1766700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766701 : term455 = term430.
Proof. exact (MK_COMB (@lem1766700) (@lem1766699)). Qed.
Lemma lem1766702 : term450 = term431.
Proof. exact (MK_COMB (@lem1766701) (@lem1766695)). Qed.
Lemma lem1766703 : term185 = term431.
Proof. exact (TRANS (@lem1766654) (@lem1766702)). Qed.
Lemma lem1766704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766705 : term164 = term412.
Proof. exact (MK_COMB (@lem1766704) (@lem1766653)). Qed.
Lemma lem1766706 : term186 = term456.
Proof. exact (MK_COMB (@lem1766705) (@lem1766703)). Qed.
Lemma lem1766707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766708 : term162 = term457.
Proof. exact (MK_COMB (@lem1766707) (@lem1766627)). Qed.
Lemma lem1766709 : term187 = term458.
Proof. exact (MK_COMB (@lem1766708) (@lem1766706)). Qed.
Lemma lem1766710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766711 (x : real) : (term144 x) = (term386 x).
Proof. exact (MK_COMB (@lem1766710) (@lem1766546 x)). Qed.
Lemma lem1766712 (x : real) : (term188 x) = (term459 x).
Proof. exact (MK_COMB (@lem1766711 x) (@lem1766709)). Qed.
Lemma lem1766713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766714 (x : real) : (term111 x) = (term410 x).
Proof. exact (MK_COMB (@lem1766713) (@lem1766527 x)). Qed.
Lemma lem1766715 (x : real) : (term192 x) = (term462 x).
Proof. exact (MK_COMB (@lem1766714 x) (@lem1766712 x)). Qed.
Lemma lem1766716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766717 : term153 = term412.
Proof. exact (MK_COMB (@lem1766716) (@lem1766422)). Qed.
Lemma lem1766718 (x : real) : (term193 x) = (term463 x).
Proof. exact (MK_COMB (@lem1766717) (@lem1766715 x)). Qed.
Lemma lem1766719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766720 (x : real) : (term191 x) = (term464 x).
Proof. exact (MK_COMB (@lem1766719) (@lem1766401 x)). Qed.
Lemma lem1766721 (x : real) : (term194 x) = (term465 x).
Proof. exact (MK_COMB (@lem1766720 x) (@lem1766718 x)). Qed.
Lemma lem1766722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766723 (x : real) : (term195 x) = (term416 x).
Proof. exact (MK_COMB (@lem1766722) (@lem1766068 x)). Qed.
Lemma lem1766724 (x : real) : (term197 x) = (term466 x).
Proof. exact (MK_COMB (@lem1766723 x) (@lem1766721 x)). Qed.
Lemma lem1766725 (x : real) : (term418 x) = (term419 x).
Proof. exact (@lem1483531 x term14). Qed.
Lemma lem1766731 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1766733 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766734 : term276 = term14.
Proof. exact (@lem1766733 term277). Qed.
Lemma lem1766735 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1766736 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1766735 x) (@lem1766734)). Qed.
Lemma lem1766737 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1766738 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1766736 x) (@lem1766737 x)). Qed.
Lemma lem1766740 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1766731 x) (@lem1766738 x)). Qed.
Lemma lem1766741 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766742 (x : real) : (term420 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1766741) (@lem1766740 x)). Qed.
Lemma lem1766743 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766744 (x : real) : (term419 x) = (term421 x).
Proof. exact (MK_COMB (@lem1766742 x) (@lem1766743)). Qed.
Lemma lem1766745 (x : real) : (term418 x) = (term421 x).
Proof. exact (TRANS (@lem1766725 x) (@lem1766744 x)). Qed.
Lemma lem1766746 : term90 = term303.
Proof. exact (@lem1483521 term14 term9). Qed.
Lemma lem1766752 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766754 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766755 : term308 = term309.
Proof. exact (@lem1766754 term277 term277). Qed.
Lemma lem1766756 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766757 : term291 = term277.
Proof. exact (EQ_MP (@lem1766756) (@lem940073)). Qed.
Lemma lem1766758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766759 : term289 = term9.
Proof. exact (MK_COMB (@lem1766758) (@lem1766757)). Qed.
Lemma lem1766760 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766761 : term309 = term19.
Proof. exact (MK_COMB (@lem1766760) (@lem1766759)). Qed.
Lemma lem1766762 : term308 = term19.
Proof. exact (TRANS (@lem1766755) (@lem1766761)). Qed.
Lemma lem1766763 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766764 : term305 = term310.
Proof. exact (MK_COMB (@lem1766763) (@lem1766762)). Qed.
Lemma lem1766765 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766766 : term305 = term19.
Proof. exact (TRANS (@lem1766764) (@lem1766765)). Qed.
Lemma lem1766768 : term304 = term19.
Proof. exact (TRANS (@lem1766752) (@lem1766766)). Qed.
Lemma lem1766769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766770 : term311 = term312.
Proof. exact (MK_COMB (@lem1766769) (@lem1766768)). Qed.
Lemma lem1766771 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766772 : term303 = term313.
Proof. exact (MK_COMB (@lem1766770) (@lem1766771)). Qed.
Lemma lem1766773 : term90 = term313.
Proof. exact (TRANS (@lem1766746) (@lem1766772)). Qed.
Lemma lem1766774 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1766780 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1766782 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766783 : term276 = term14.
Proof. exact (@lem1766782 term277). Qed.
Lemma lem1766784 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1766785 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1766784 x) (@lem1766783)). Qed.
Lemma lem1766786 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1766787 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1766785 x) (@lem1766786 x)). Qed.
Lemma lem1766789 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1766780 x) (@lem1766787 x)). Qed.
Lemma lem1766790 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766791 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1766790) (@lem1766789 x)). Qed.
Lemma lem1766792 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766793 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1766791 x) (@lem1766792)). Qed.
Lemma lem1766794 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1766774 x) (@lem1766793 x)). Qed.
Lemma lem1766795 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1766801 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766803 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766804 : term308 = term309.
Proof. exact (@lem1766803 term277 term277). Qed.
Lemma lem1766805 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766806 : term291 = term277.
Proof. exact (EQ_MP (@lem1766805) (@lem940073)). Qed.
Lemma lem1766807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766808 : term289 = term9.
Proof. exact (MK_COMB (@lem1766807) (@lem1766806)). Qed.
Lemma lem1766809 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766810 : term309 = term19.
Proof. exact (MK_COMB (@lem1766809) (@lem1766808)). Qed.
Lemma lem1766811 : term308 = term19.
Proof. exact (TRANS (@lem1766804) (@lem1766810)). Qed.
Lemma lem1766812 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766813 : term305 = term310.
Proof. exact (MK_COMB (@lem1766812) (@lem1766811)). Qed.
Lemma lem1766814 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766815 : term305 = term19.
Proof. exact (TRANS (@lem1766813) (@lem1766814)). Qed.
Lemma lem1766817 : term304 = term19.
Proof. exact (TRANS (@lem1766801) (@lem1766815)). Qed.
Lemma lem1766818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766819 : term321 = term322.
Proof. exact (MK_COMB (@lem1766818) (@lem1766817)). Qed.
Lemma lem1766820 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766821 : term320 = term323.
Proof. exact (MK_COMB (@lem1766819) (@lem1766820)). Qed.
Lemma lem1766822 : term87 = term323.
Proof. exact (TRANS (@lem1766795) (@lem1766821)). Qed.
Lemma lem1766823 : term118 = term324.
Proof. exact (@lem1483554 term19 term9). Qed.
Lemma lem1766829 : term325 = term326.
Proof. exact (@lem1483519 term19 term9). Qed.
Lemma lem1766831 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766832 : term308 = term309.
Proof. exact (@lem1766831 term277 term277). Qed.
Lemma lem1766833 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766834 : term291 = term277.
Proof. exact (EQ_MP (@lem1766833) (@lem940073)). Qed.
Lemma lem1766835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766836 : term289 = term9.
Proof. exact (MK_COMB (@lem1766835) (@lem1766834)). Qed.
Lemma lem1766837 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766838 : term309 = term19.
Proof. exact (MK_COMB (@lem1766837) (@lem1766836)). Qed.
Lemma lem1766839 : term308 = term19.
Proof. exact (TRANS (@lem1766832) (@lem1766838)). Qed.
Lemma lem1766840 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem1766841 : term326 = term328.
Proof. exact (MK_COMB (@lem1766840) (@lem1766839)). Qed.
Lemma lem1766842 : term328 = term329.
Proof. exact (@lem1367763 term277 term277). Qed.
Lemma lem1766843 : term330 = term331.
Proof. exact (@lem706885). Qed.
Lemma lem1766844 : (term330 = term331) = (term332 = term333).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term331). Qed.
Lemma lem1766845 : term332 = term333.
Proof. exact (EQ_MP (@lem1766844) (@lem1766843)). Qed.
Lemma lem1766846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766847 : term334 = term335.
Proof. exact (MK_COMB (@lem1766846) (@lem1766845)). Qed.
Lemma lem1766848 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766849 : term329 = term336.
Proof. exact (MK_COMB (@lem1766848) (@lem1766847)). Qed.
Lemma lem1766850 : term328 = term336.
Proof. exact (TRANS (@lem1766842) (@lem1766849)). Qed.
Lemma lem1766851 : term326 = term336.
Proof. exact (TRANS (@lem1766841) (@lem1766850)). Qed.
Lemma lem1766853 : term325 = term336.
Proof. exact (TRANS (@lem1766829) (@lem1766851)). Qed.
Lemma lem1766854 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766855 : term337 = term338.
Proof. exact (MK_COMB (@lem1766854) (@lem1766853)). Qed.
Lemma lem1766856 : term338 = term339.
Proof. exact (@lem1483512 term336). Qed.
Lemma lem1766858 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766859 : term339 = term340.
Proof. exact (@lem1766858 term277 term333). Qed.
Lemma lem1766860 : term341 = term331.
Proof. exact (@lem996238 term331). Qed.
Lemma lem1766861 : (term341 = term331) = (term342 = term333).
Proof. exact (@lem1007663 (BIT1 0) term331 term331). Qed.
Lemma lem1766862 : term342 = term333.
Proof. exact (EQ_MP (@lem1766861) (@lem1766860)). Qed.
Lemma lem1766863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766864 : term340 = term335.
Proof. exact (MK_COMB (@lem1766863) (@lem1766862)). Qed.
Lemma lem1766865 : term339 = term335.
Proof. exact (TRANS (@lem1766859) (@lem1766864)). Qed.
Lemma lem1766866 : term338 = term335.
Proof. exact (TRANS (@lem1766856) (@lem1766865)). Qed.
Lemma lem1766867 : term343 = term343.
Proof. exact (eq_refl term343). Qed.
Lemma lem1766868 : (term337 = term338) = (term337 = term335).
Proof. exact (MK_COMB (@lem1766867) (@lem1766866)). Qed.
Lemma lem1766869 : term337 = term335.
Proof. exact (EQ_MP (@lem1766868) (@lem1766855)). Qed.
Lemma lem1766870 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766871 : term344 = term345.
Proof. exact (MK_COMB (@lem1766870) (@lem1766869)). Qed.
Lemma lem1766872 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766873 : term346 = term347.
Proof. exact (MK_COMB (@lem1766871) (@lem1766872)). Qed.
Lemma lem1766874 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766875 : term348 = term349.
Proof. exact (MK_COMB (@lem1766874) (@lem1766853)). Qed.
Lemma lem1766876 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766877 : term350 = term351.
Proof. exact (MK_COMB (@lem1766875) (@lem1766876)). Qed.
Lemma lem1766878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1766879 : term352 = term353.
Proof. exact (MK_COMB (@lem1766878) (@lem1766877)). Qed.
Lemma lem1766880 : term324 = term354.
Proof. exact (MK_COMB (@lem1766879) (@lem1766873)). Qed.
Lemma lem1766881 : term118 = term354.
Proof. exact (TRANS (@lem1766823) (@lem1766880)). Qed.
Lemma lem1766882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766883 : term88 = term355.
Proof. exact (MK_COMB (@lem1766882) (@lem1766822)). Qed.
Lemma lem1766884 : term119 = term356.
Proof. exact (MK_COMB (@lem1766883) (@lem1766881)). Qed.
Lemma lem1766885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766886 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1766885) (@lem1766794 x)). Qed.
Lemma lem1766887 (x : real) : (term120 x) = (term358 x).
Proof. exact (MK_COMB (@lem1766886 x) (@lem1766884)). Qed.
Lemma lem1766888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1766889 : term147 = term384.
Proof. exact (MK_COMB (@lem1766888) (@lem1766773)). Qed.
Lemma lem1766890 (x : real) : (term223 x) = (term479 x).
Proof. exact (MK_COMB (@lem1766889) (@lem1766887 x)). Qed.
Lemma lem1766891 : term391 = term392.
Proof. exact (@lem1483531 term9 term14). Qed.
Lemma lem1766897 : term393 = term394.
Proof. exact (@lem1483519 term9 term14). Qed.
Lemma lem1766899 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766900 : term276 = term14.
Proof. exact (@lem1766899 term277). Qed.
Lemma lem1766901 : term371 = term371.
Proof. exact (eq_refl term371). Qed.
Lemma lem1766902 : term394 = term395.
Proof. exact (MK_COMB (@lem1766901) (@lem1766900)). Qed.
Lemma lem1766903 : term395 = term9.
Proof. exact (@lem1483450 term9). Qed.
Lemma lem1766904 : term394 = term9.
Proof. exact (TRANS (@lem1766902) (@lem1766903)). Qed.
Lemma lem1766906 : term393 = term9.
Proof. exact (TRANS (@lem1766897) (@lem1766904)). Qed.
Lemma lem1766907 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766908 : term396 = term397.
Proof. exact (MK_COMB (@lem1766907) (@lem1766906)). Qed.
Lemma lem1766909 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766910 : term392 = term398.
Proof. exact (MK_COMB (@lem1766908) (@lem1766909)). Qed.
Lemma lem1766911 : term391 = term398.
Proof. exact (TRANS (@lem1766891) (@lem1766910)). Qed.
Lemma lem1766912 (x : real) : (term55 x) = (term314 x).
Proof. exact (@lem1483521 x term14). Qed.
Lemma lem1766918 (x : real) : (term315 x) = (term316 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1766920 (x : nat) : (term275 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1766921 : term276 = term14.
Proof. exact (@lem1766920 term277). Qed.
Lemma lem1766922 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1766923 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1766922 x) (@lem1766921)). Qed.
Lemma lem1766924 (x : real) : (term317 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1766925 (x : real) : (term316 x) = x.
Proof. exact (TRANS (@lem1766923 x) (@lem1766924 x)). Qed.
Lemma lem1766927 (x : real) : (term315 x) = x.
Proof. exact (TRANS (@lem1766918 x) (@lem1766925 x)). Qed.
Lemma lem1766928 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1766929 (x : real) : (term318 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1766928) (@lem1766927 x)). Qed.
Lemma lem1766930 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766931 (x : real) : (term314 x) = (term319 x).
Proof. exact (MK_COMB (@lem1766929 x) (@lem1766930)). Qed.
Lemma lem1766932 (x : real) : (term55 x) = (term319 x).
Proof. exact (TRANS (@lem1766912 x) (@lem1766931 x)). Qed.
Lemma lem1766933 : term87 = term320.
Proof. exact (@lem1483531 term14 term9). Qed.
Lemma lem1766939 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766941 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766942 : term308 = term309.
Proof. exact (@lem1766941 term277 term277). Qed.
Lemma lem1766943 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766944 : term291 = term277.
Proof. exact (EQ_MP (@lem1766943) (@lem940073)). Qed.
Lemma lem1766945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766946 : term289 = term9.
Proof. exact (MK_COMB (@lem1766945) (@lem1766944)). Qed.
Lemma lem1766947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766948 : term309 = term19.
Proof. exact (MK_COMB (@lem1766947) (@lem1766946)). Qed.
Lemma lem1766949 : term308 = term19.
Proof. exact (TRANS (@lem1766942) (@lem1766948)). Qed.
Lemma lem1766950 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766951 : term305 = term310.
Proof. exact (MK_COMB (@lem1766950) (@lem1766949)). Qed.
Lemma lem1766952 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766953 : term305 = term19.
Proof. exact (TRANS (@lem1766951) (@lem1766952)). Qed.
Lemma lem1766955 : term304 = term19.
Proof. exact (TRANS (@lem1766939) (@lem1766953)). Qed.
Lemma lem1766956 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1766957 : term321 = term322.
Proof. exact (MK_COMB (@lem1766956) (@lem1766955)). Qed.
Lemma lem1766958 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1766959 : term320 = term323.
Proof. exact (MK_COMB (@lem1766957) (@lem1766958)). Qed.
Lemma lem1766960 : term87 = term323.
Proof. exact (TRANS (@lem1766933) (@lem1766959)). Qed.
Lemma lem1766961 : term105 = term399.
Proof. exact (@lem1483554 term14 term9). Qed.
Lemma lem1766967 : term304 = term305.
Proof. exact (@lem1483519 term14 term9). Qed.
Lemma lem1766969 (m : nat) (n : nat) : (term306 m n) = (term307 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1766970 : term308 = term309.
Proof. exact (@lem1766969 term277 term277). Qed.
Lemma lem1766971 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766972 : term291 = term277.
Proof. exact (EQ_MP (@lem1766971) (@lem940073)). Qed.
Lemma lem1766973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766974 : term289 = term9.
Proof. exact (MK_COMB (@lem1766973) (@lem1766972)). Qed.
Lemma lem1766975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766976 : term309 = term19.
Proof. exact (MK_COMB (@lem1766975) (@lem1766974)). Qed.
Lemma lem1766977 : term308 = term19.
Proof. exact (TRANS (@lem1766970) (@lem1766976)). Qed.
Lemma lem1766978 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1766979 : term305 = term310.
Proof. exact (MK_COMB (@lem1766978) (@lem1766977)). Qed.
Lemma lem1766980 : term310 = term19.
Proof. exact (@lem1483448 term19). Qed.
Lemma lem1766981 : term305 = term19.
Proof. exact (TRANS (@lem1766979) (@lem1766980)). Qed.
Lemma lem1766983 : term304 = term19.
Proof. exact (TRANS (@lem1766967) (@lem1766981)). Qed.
Lemma lem1766984 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1766985 : term400 = term401.
Proof. exact (MK_COMB (@lem1766984) (@lem1766983)). Qed.
Lemma lem1766986 : term401 = term288.
Proof. exact (@lem1483512 term19). Qed.
Lemma lem1766988 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1766989 : term288 = term289.
Proof. exact (@lem1766988 term277 term277). Qed.
Lemma lem1766990 : (term290 = (BIT1 0)) = (term291 = term277).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1766991 : term291 = term277.
Proof. exact (EQ_MP (@lem1766990) (@lem940073)). Qed.
Lemma lem1766992 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1766993 : term289 = term9.
Proof. exact (MK_COMB (@lem1766992) (@lem1766991)). Qed.
Lemma lem1766994 : term288 = term9.
Proof. exact (TRANS (@lem1766989) (@lem1766993)). Qed.
Lemma lem1766995 : term401 = term9.
Proof. exact (TRANS (@lem1766986) (@lem1766994)). Qed.
Lemma lem1766996 : term402 = term402.
Proof. exact (eq_refl term402). Qed.
Lemma lem1766997 : (term400 = term401) = (term400 = term9).
Proof. exact (MK_COMB (@lem1766996) (@lem1766995)). Qed.
Lemma lem1766998 : term400 = term9.
Proof. exact (EQ_MP (@lem1766997) (@lem1766985)). Qed.
Lemma lem1766999 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1767000 : term403 = term294.
Proof. exact (MK_COMB (@lem1766999) (@lem1766998)). Qed.
Lemma lem1767001 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1767002 : term404 = term295.
Proof. exact (MK_COMB (@lem1767000) (@lem1767001)). Qed.
Lemma lem1767003 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1767004 : term311 = term312.
Proof. exact (MK_COMB (@lem1767003) (@lem1766983)). Qed.
Lemma lem1767005 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1767006 : term303 = term313.
Proof. exact (MK_COMB (@lem1767004) (@lem1767005)). Qed.
Lemma lem1767007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767008 : term405 = term406.
Proof. exact (MK_COMB (@lem1767007) (@lem1767006)). Qed.
Lemma lem1767009 : term399 = term407.
Proof. exact (MK_COMB (@lem1767008) (@lem1767002)). Qed.
Lemma lem1767010 : term105 = term407.
Proof. exact (TRANS (@lem1766961) (@lem1767009)). Qed.
Lemma lem1767011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767012 : term88 = term355.
Proof. exact (MK_COMB (@lem1767011) (@lem1766960)). Qed.
Lemma lem1767013 : term106 = term408.
Proof. exact (MK_COMB (@lem1767012) (@lem1767010)). Qed.
Lemma lem1767014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767015 (x : real) : (term107 x) = (term357 x).
Proof. exact (MK_COMB (@lem1767014) (@lem1766932 x)). Qed.
Lemma lem1767016 (x : real) : (term109 x) = (term409 x).
Proof. exact (MK_COMB (@lem1767015 x) (@lem1767013)). Qed.
Lemma lem1767017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767018 : term153 = term412.
Proof. exact (MK_COMB (@lem1767017) (@lem1766911)). Qed.
Lemma lem1767019 (x : real) : (term226 x) = (term480 x).
Proof. exact (MK_COMB (@lem1767018) (@lem1767016 x)). Qed.
Lemma lem1767020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767021 (x : real) : (term224 x) = (term481 x).
Proof. exact (MK_COMB (@lem1767020) (@lem1766890 x)). Qed.
Lemma lem1767022 (x : real) : (term227 x) = (term482 x).
Proof. exact (MK_COMB (@lem1767021 x) (@lem1767019 x)). Qed.
Lemma lem1767023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767024 (x : real) : (term228 x) = (term439 x).
Proof. exact (MK_COMB (@lem1767023) (@lem1766745 x)). Qed.
Lemma lem1767025 (x : real) : (term229 x) = (term483 x).
Proof. exact (MK_COMB (@lem1767024 x) (@lem1767022 x)). Qed.
Lemma lem1767026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767027 (x : real) : (term199 x) = (term467 x).
Proof. exact (MK_COMB (@lem1767026) (@lem1766724 x)). Qed.
Lemma lem1767028 (x : real) : (term236 x) = (term486 x).
Proof. exact (MK_COMB (@lem1767027 x) (@lem1767025 x)). Qed.
Lemma lem1767029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767030 : term237 = term355.
Proof. exact (MK_COMB (@lem1767029) (@lem1766049)). Qed.
Lemma lem1767031 (x : real) : (term239 x) = (term487 x).
Proof. exact (MK_COMB (@lem1767030) (@lem1767028 x)). Qed.
Lemma lem1767032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767033 (x : real) : (term235 x) = (term488 x).
Proof. exact (MK_COMB (@lem1767032) (@lem1766028 x)). Qed.
Lemma lem1767034 (x : real) : (term240 x) = (term489 x).
Proof. exact (MK_COMB (@lem1767033 x) (@lem1767031 x)). Qed.
Lemma lem1767035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1767036 : term136 = term490.
Proof. exact (MK_COMB (@lem1767035) (@lem1765184)). Qed.
Lemma lem1767037 (x : real) : (term491 x) = (term492 x).
Proof. exact (MK_COMB (@lem1767036) (@lem1767034 x)). Qed.
Lemma lem1767038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767039 (x : real) : (term493 x) = (term494 x).
Proof. exact (MK_COMB (@lem1767038) (@lem1765163 x)). Qed.
Lemma lem1767040 (x : real) : (term264 x) = (term495 x).
Proof. exact (MK_COMB (@lem1767039 x) (@lem1767037 x)). Qed.
Lemma lem1767041 : term270 = term496.
Proof. exact (fun_ext (fun x : real => @lem1767040 x)). Qed.
Lemma lem1767042 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767043 : term271 = term497.
Proof. exact (MK_COMB (@lem1767042) (@lem1767041)). Qed.
Lemma lem1767044 : term33 = term497.
Proof. exact (TRANS (@lem1763009) (@lem1767043)). Qed.
Lemma lem1767046 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767047 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767046 real P Q). Qed.
Lemma lem1767048 : term502 = term503.
Proof. exact (@lem1767047 term504 term505). Qed.
Lemma lem1767049 (x : real) : (term506 x) = (term474 x).
Proof. exact (eq_refl (term506 x)). Qed.
Lemma lem1767050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767051 (x : real) : (term507 x) = (term494 x).
Proof. exact (MK_COMB (@lem1767050) (@lem1767049 x)). Qed.
Lemma lem1767052 (x : real) : (term508 x) = (term492 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1767053 (x : real) : (term509 x) = (term495 x).
Proof. exact (MK_COMB (@lem1767051 x) (@lem1767052 x)). Qed.
Lemma lem1767054 : term510 = term496.
Proof. exact (fun_ext (fun x : real => @lem1767053 x)). Qed.
Lemma lem1767055 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767056 : term502 = term497.
Proof. exact (MK_COMB (@lem1767055) (@lem1767054)). Qed.
Lemma lem1767057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767058 : term511 = term512.
Proof. exact (MK_COMB (@lem1767057) (@lem1767056)). Qed.
Lemma lem1767059 (x : real) : (term506 x) = (term474 x).
Proof. exact (eq_refl (term506 x)). Qed.
Lemma lem1767060 : term513 = term504.
Proof. exact (fun_ext (fun x : real => @lem1767059 x)). Qed.
Lemma lem1767061 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767062 : term514 = term515.
Proof. exact (MK_COMB (@lem1767061) (@lem1767060)). Qed.
Lemma lem1767063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767064 : term516 = term517.
Proof. exact (MK_COMB (@lem1767063) (@lem1767062)). Qed.
Lemma lem1767065 (x : real) : (term508 x) = (term492 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1767066 : term518 = term505.
Proof. exact (fun_ext (fun x : real => @lem1767065 x)). Qed.
Lemma lem1767067 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767068 : term519 = term520.
Proof. exact (MK_COMB (@lem1767067) (@lem1767066)). Qed.
Lemma lem1767069 : term503 = term521.
Proof. exact (MK_COMB (@lem1767064) (@lem1767068)). Qed.
Lemma lem1767070 : (term502 = term503) = (term497 = term521).
Proof. exact (MK_COMB (@lem1767058) (@lem1767069)). Qed.
Lemma lem1767071 : term497 = term521.
Proof. exact (EQ_MP (@lem1767070) (@lem1767048)). Qed.
Lemma lem1767073 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767074 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767073 real P Q). Qed.
Lemma lem1767075 : term526 = term527.
Proof. exact (@lem1767074 term282 term528). Qed.
Lemma lem1767076 (x : real) : (term529 x) = (term471 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1767077 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767078 (x : real) : (term530 x) = (term474 x).
Proof. exact (MK_COMB (@lem1767077) (@lem1767076 x)). Qed.
Lemma lem1767079 : term531 = term504.
Proof. exact (fun_ext (fun x : real => @lem1767078 x)). Qed.
Lemma lem1767080 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767081 : term526 = term515.
Proof. exact (MK_COMB (@lem1767080) (@lem1767079)). Qed.
Lemma lem1767082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767083 : term532 = term533.
Proof. exact (MK_COMB (@lem1767082) (@lem1767081)). Qed.
Lemma lem1767084 (x : real) : (term529 x) = (term471 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1767085 : term534 = term528.
Proof. exact (fun_ext (fun x : real => @lem1767084 x)). Qed.
Lemma lem1767086 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767087 : term535 = term536.
Proof. exact (MK_COMB (@lem1767086) (@lem1767085)). Qed.
Lemma lem1767088 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767089 : term527 = term537.
Proof. exact (MK_COMB (@lem1767088) (@lem1767087)). Qed.
Lemma lem1767090 : (term526 = term527) = (term515 = term537).
Proof. exact (MK_COMB (@lem1767083) (@lem1767089)). Qed.
Lemma lem1767091 : term515 = term537.
Proof. exact (EQ_MP (@lem1767090) (@lem1767075)). Qed.
Lemma lem1767093 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767094 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767093 real P Q). Qed.
Lemma lem1767095 : term538 = term539.
Proof. exact (@lem1767094 term540 term541). Qed.
Lemma lem1767096 (x : real) : (term542 x) = (term444 x).
Proof. exact (eq_refl (term542 x)). Qed.
Lemma lem1767097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767098 (x : real) : (term543 x) = (term470 x).
Proof. exact (MK_COMB (@lem1767097) (@lem1767096 x)). Qed.
Lemma lem1767099 (x : real) : (term544 x) = (term469 x).
Proof. exact (eq_refl (term544 x)). Qed.
Lemma lem1767100 (x : real) : (term545 x) = (term471 x).
Proof. exact (MK_COMB (@lem1767098 x) (@lem1767099 x)). Qed.
Lemma lem1767101 : term546 = term528.
Proof. exact (fun_ext (fun x : real => @lem1767100 x)). Qed.
Lemma lem1767102 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767103 : term538 = term536.
Proof. exact (MK_COMB (@lem1767102) (@lem1767101)). Qed.
Lemma lem1767104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767105 : term547 = term548.
Proof. exact (MK_COMB (@lem1767104) (@lem1767103)). Qed.
Lemma lem1767106 (x : real) : (term542 x) = (term444 x).
Proof. exact (eq_refl (term542 x)). Qed.
Lemma lem1767107 : term549 = term540.
Proof. exact (fun_ext (fun x : real => @lem1767106 x)). Qed.
Lemma lem1767108 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767109 : term550 = term551.
Proof. exact (MK_COMB (@lem1767108) (@lem1767107)). Qed.
Lemma lem1767110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767111 : term552 = term553.
Proof. exact (MK_COMB (@lem1767110) (@lem1767109)). Qed.
Lemma lem1767112 (x : real) : (term544 x) = (term469 x).
Proof. exact (eq_refl (term544 x)). Qed.
Lemma lem1767113 : term554 = term541.
Proof. exact (fun_ext (fun x : real => @lem1767112 x)). Qed.
Lemma lem1767114 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767115 : term555 = term556.
Proof. exact (MK_COMB (@lem1767114) (@lem1767113)). Qed.
Lemma lem1767116 : term539 = term557.
Proof. exact (MK_COMB (@lem1767111) (@lem1767115)). Qed.
Lemma lem1767117 : (term538 = term539) = (term536 = term557).
Proof. exact (MK_COMB (@lem1767105) (@lem1767116)). Qed.
Lemma lem1767118 : term536 = term557.
Proof. exact (EQ_MP (@lem1767117) (@lem1767095)). Qed.
Lemma lem1767120 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767121 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767120 real P Q). Qed.
Lemma lem1767122 : term558 = term559.
Proof. exact (@lem1767121 term295 term560). Qed.
Lemma lem1767123 (x : real) : (term561 x) = (term442 x).
Proof. exact (eq_refl (term561 x)). Qed.
Lemma lem1767124 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767125 (x : real) : (term562 x) = (term444 x).
Proof. exact (MK_COMB (@lem1767124) (@lem1767123 x)). Qed.
Lemma lem1767126 : term563 = term540.
Proof. exact (fun_ext (fun x : real => @lem1767125 x)). Qed.
Lemma lem1767127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767128 : term558 = term551.
Proof. exact (MK_COMB (@lem1767127) (@lem1767126)). Qed.
Lemma lem1767129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767130 : term564 = term565.
Proof. exact (MK_COMB (@lem1767129) (@lem1767128)). Qed.
Lemma lem1767131 (x : real) : (term561 x) = (term442 x).
Proof. exact (eq_refl (term561 x)). Qed.
Lemma lem1767132 : term566 = term560.
Proof. exact (fun_ext (fun x : real => @lem1767131 x)). Qed.
Lemma lem1767133 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767134 : term567 = term568.
Proof. exact (MK_COMB (@lem1767133) (@lem1767132)). Qed.
Lemma lem1767135 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767136 : term559 = term569.
Proof. exact (MK_COMB (@lem1767135) (@lem1767134)). Qed.
Lemma lem1767137 : (term558 = term559) = (term551 = term569).
Proof. exact (MK_COMB (@lem1767130) (@lem1767136)). Qed.
Lemma lem1767138 : term551 = term569.
Proof. exact (EQ_MP (@lem1767137) (@lem1767122)). Qed.
Lemma lem1767140 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767141 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767140 real P Q). Qed.
Lemma lem1767142 : term570 = term571.
Proof. exact (@lem1767141 term572 term573). Qed.
Lemma lem1767143 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767145 (x : real) : (term575 x) = (term441 x).
Proof. exact (MK_COMB (@lem1767144) (@lem1767143 x)). Qed.
Lemma lem1767146 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767147 (x : real) : (term577 x) = (term442 x).
Proof. exact (MK_COMB (@lem1767145 x) (@lem1767146 x)). Qed.
Lemma lem1767148 : term578 = term560.
Proof. exact (fun_ext (fun x : real => @lem1767147 x)). Qed.
Lemma lem1767149 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767150 : term570 = term568.
Proof. exact (MK_COMB (@lem1767149) (@lem1767148)). Qed.
Lemma lem1767151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767152 : term579 = term580.
Proof. exact (MK_COMB (@lem1767151) (@lem1767150)). Qed.
Lemma lem1767153 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767154 : term581 = term572.
Proof. exact (fun_ext (fun x : real => @lem1767153 x)). Qed.
Lemma lem1767155 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767156 : term582 = term583.
Proof. exact (MK_COMB (@lem1767155) (@lem1767154)). Qed.
Lemma lem1767157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767158 : term584 = term585.
Proof. exact (MK_COMB (@lem1767157) (@lem1767156)). Qed.
Lemma lem1767159 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767160 : term586 = term573.
Proof. exact (fun_ext (fun x : real => @lem1767159 x)). Qed.
Lemma lem1767161 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767162 : term587 = term588.
Proof. exact (MK_COMB (@lem1767161) (@lem1767160)). Qed.
Lemma lem1767163 : term571 = term589.
Proof. exact (MK_COMB (@lem1767158) (@lem1767162)). Qed.
Lemma lem1767164 : (term570 = term571) = (term568 = term589).
Proof. exact (MK_COMB (@lem1767152) (@lem1767163)). Qed.
Lemma lem1767165 : term568 = term589.
Proof. exact (EQ_MP (@lem1767164) (@lem1767142)). Qed.
Lemma lem1767262 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767263 : term569 = term590.
Proof. exact (MK_COMB (@lem1767262) (@lem1767165)). Qed.
Lemma lem1767264 : term551 = term590.
Proof. exact (TRANS (@lem1767138) (@lem1767263)). Qed.
Lemma lem1767265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767266 : term553 = term591.
Proof. exact (MK_COMB (@lem1767265) (@lem1767264)). Qed.
Lemma lem1767268 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767269 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767268 real P Q). Qed.
Lemma lem1767270 : term592 = term593.
Proof. exact (@lem1767269 term323 term594). Qed.
Lemma lem1767271 (x : real) : (term595 x) = (term468 x).
Proof. exact (eq_refl (term595 x)). Qed.
Lemma lem1767272 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767273 (x : real) : (term596 x) = (term469 x).
Proof. exact (MK_COMB (@lem1767272) (@lem1767271 x)). Qed.
Lemma lem1767274 : term597 = term541.
Proof. exact (fun_ext (fun x : real => @lem1767273 x)). Qed.
Lemma lem1767275 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767276 : term592 = term556.
Proof. exact (MK_COMB (@lem1767275) (@lem1767274)). Qed.
Lemma lem1767277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767278 : term598 = term599.
Proof. exact (MK_COMB (@lem1767277) (@lem1767276)). Qed.
Lemma lem1767279 (x : real) : (term595 x) = (term468 x).
Proof. exact (eq_refl (term595 x)). Qed.
Lemma lem1767280 : term600 = term594.
Proof. exact (fun_ext (fun x : real => @lem1767279 x)). Qed.
Lemma lem1767281 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767282 : term601 = term602.
Proof. exact (MK_COMB (@lem1767281) (@lem1767280)). Qed.
Lemma lem1767283 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767284 : term593 = term603.
Proof. exact (MK_COMB (@lem1767283) (@lem1767282)). Qed.
Lemma lem1767285 : (term592 = term593) = (term556 = term603).
Proof. exact (MK_COMB (@lem1767278) (@lem1767284)). Qed.
Lemma lem1767286 : term556 = term603.
Proof. exact (EQ_MP (@lem1767285) (@lem1767270)). Qed.
Lemma lem1767288 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767289 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767288 real P Q). Qed.
Lemma lem1767290 : term604 = term605.
Proof. exact (@lem1767289 term606 term573). Qed.
Lemma lem1767291 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767293 (x : real) : (term608 x) = (term467 x).
Proof. exact (MK_COMB (@lem1767292) (@lem1767291 x)). Qed.
Lemma lem1767294 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767295 (x : real) : (term609 x) = (term468 x).
Proof. exact (MK_COMB (@lem1767293 x) (@lem1767294 x)). Qed.
Lemma lem1767296 : term610 = term594.
Proof. exact (fun_ext (fun x : real => @lem1767295 x)). Qed.
Lemma lem1767297 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767298 : term604 = term602.
Proof. exact (MK_COMB (@lem1767297) (@lem1767296)). Qed.
Lemma lem1767299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767300 : term611 = term612.
Proof. exact (MK_COMB (@lem1767299) (@lem1767298)). Qed.
Lemma lem1767301 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767302 : term613 = term606.
Proof. exact (fun_ext (fun x : real => @lem1767301 x)). Qed.
Lemma lem1767303 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767304 : term614 = term615.
Proof. exact (MK_COMB (@lem1767303) (@lem1767302)). Qed.
Lemma lem1767305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767306 : term616 = term617.
Proof. exact (MK_COMB (@lem1767305) (@lem1767304)). Qed.
Lemma lem1767307 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767308 : term586 = term573.
Proof. exact (fun_ext (fun x : real => @lem1767307 x)). Qed.
Lemma lem1767309 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767310 : term587 = term588.
Proof. exact (MK_COMB (@lem1767309) (@lem1767308)). Qed.
Lemma lem1767311 : term605 = term618.
Proof. exact (MK_COMB (@lem1767306) (@lem1767310)). Qed.
Lemma lem1767312 : (term604 = term605) = (term602 = term618).
Proof. exact (MK_COMB (@lem1767300) (@lem1767311)). Qed.
Lemma lem1767313 : term602 = term618.
Proof. exact (EQ_MP (@lem1767312) (@lem1767290)). Qed.
Lemma lem1767410 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767411 : term603 = term619.
Proof. exact (MK_COMB (@lem1767410) (@lem1767313)). Qed.
Lemma lem1767412 : term556 = term619.
Proof. exact (TRANS (@lem1767286) (@lem1767411)). Qed.
Lemma lem1767413 : term557 = term620.
Proof. exact (MK_COMB (@lem1767266) (@lem1767412)). Qed.
Lemma lem1767414 : term536 = term620.
Proof. exact (TRANS (@lem1767118) (@lem1767413)). Qed.
Lemma lem1767415 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767416 : term537 = term621.
Proof. exact (MK_COMB (@lem1767415) (@lem1767414)). Qed.
Lemma lem1767417 : term515 = term621.
Proof. exact (TRANS (@lem1767091) (@lem1767416)). Qed.
Lemma lem1767418 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767419 : term517 = term622.
Proof. exact (MK_COMB (@lem1767418) (@lem1767417)). Qed.
Lemma lem1767421 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767422 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767421 real P Q). Qed.
Lemma lem1767423 : term623 = term624.
Proof. exact (@lem1767422 term478 term625). Qed.
Lemma lem1767424 (x : real) : (term626 x) = (term489 x).
Proof. exact (eq_refl (term626 x)). Qed.
Lemma lem1767425 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1767426 (x : real) : (term627 x) = (term492 x).
Proof. exact (MK_COMB (@lem1767425) (@lem1767424 x)). Qed.
Lemma lem1767427 : term628 = term505.
Proof. exact (fun_ext (fun x : real => @lem1767426 x)). Qed.
Lemma lem1767428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767429 : term623 = term520.
Proof. exact (MK_COMB (@lem1767428) (@lem1767427)). Qed.
Lemma lem1767430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767431 : term629 = term630.
Proof. exact (MK_COMB (@lem1767430) (@lem1767429)). Qed.
Lemma lem1767432 (x : real) : (term626 x) = (term489 x).
Proof. exact (eq_refl (term626 x)). Qed.
Lemma lem1767433 : term631 = term625.
Proof. exact (fun_ext (fun x : real => @lem1767432 x)). Qed.
Lemma lem1767434 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767435 : term632 = term633.
Proof. exact (MK_COMB (@lem1767434) (@lem1767433)). Qed.
Lemma lem1767436 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1767437 : term624 = term634.
Proof. exact (MK_COMB (@lem1767436) (@lem1767435)). Qed.
Lemma lem1767438 : (term623 = term624) = (term520 = term634).
Proof. exact (MK_COMB (@lem1767431) (@lem1767437)). Qed.
Lemma lem1767439 : term520 = term634.
Proof. exact (EQ_MP (@lem1767438) (@lem1767423)). Qed.
Lemma lem1767441 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767442 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767441 real P Q). Qed.
Lemma lem1767443 : term635 = term636.
Proof. exact (@lem1767442 term637 term638). Qed.
Lemma lem1767444 (x : real) : (term639 x) = (term485 x).
Proof. exact (eq_refl (term639 x)). Qed.
Lemma lem1767445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767446 (x : real) : (term640 x) = (term488 x).
Proof. exact (MK_COMB (@lem1767445) (@lem1767444 x)). Qed.
Lemma lem1767447 (x : real) : (term641 x) = (term487 x).
Proof. exact (eq_refl (term641 x)). Qed.
Lemma lem1767448 (x : real) : (term642 x) = (term489 x).
Proof. exact (MK_COMB (@lem1767446 x) (@lem1767447 x)). Qed.
Lemma lem1767449 : term643 = term625.
Proof. exact (fun_ext (fun x : real => @lem1767448 x)). Qed.
Lemma lem1767450 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767451 : term635 = term633.
Proof. exact (MK_COMB (@lem1767450) (@lem1767449)). Qed.
Lemma lem1767452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767453 : term644 = term645.
Proof. exact (MK_COMB (@lem1767452) (@lem1767451)). Qed.
Lemma lem1767454 (x : real) : (term639 x) = (term485 x).
Proof. exact (eq_refl (term639 x)). Qed.
Lemma lem1767455 : term646 = term637.
Proof. exact (fun_ext (fun x : real => @lem1767454 x)). Qed.
Lemma lem1767456 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767457 : term647 = term648.
Proof. exact (MK_COMB (@lem1767456) (@lem1767455)). Qed.
Lemma lem1767458 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767459 : term649 = term650.
Proof. exact (MK_COMB (@lem1767458) (@lem1767457)). Qed.
Lemma lem1767460 (x : real) : (term641 x) = (term487 x).
Proof. exact (eq_refl (term641 x)). Qed.
Lemma lem1767461 : term651 = term638.
Proof. exact (fun_ext (fun x : real => @lem1767460 x)). Qed.
Lemma lem1767462 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767463 : term652 = term653.
Proof. exact (MK_COMB (@lem1767462) (@lem1767461)). Qed.
Lemma lem1767464 : term636 = term654.
Proof. exact (MK_COMB (@lem1767459) (@lem1767463)). Qed.
Lemma lem1767465 : (term635 = term636) = (term633 = term654).
Proof. exact (MK_COMB (@lem1767453) (@lem1767464)). Qed.
Lemma lem1767466 : term633 = term654.
Proof. exact (EQ_MP (@lem1767465) (@lem1767443)). Qed.
Lemma lem1767468 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767469 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767468 real P Q). Qed.
Lemma lem1767470 : term655 = term656.
Proof. exact (@lem1767469 term295 term657). Qed.
Lemma lem1767471 (x : real) : (term658 x) = (term484 x).
Proof. exact (eq_refl (term658 x)). Qed.
Lemma lem1767472 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767473 (x : real) : (term659 x) = (term485 x).
Proof. exact (MK_COMB (@lem1767472) (@lem1767471 x)). Qed.
Lemma lem1767474 : term660 = term637.
Proof. exact (fun_ext (fun x : real => @lem1767473 x)). Qed.
Lemma lem1767475 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767476 : term655 = term648.
Proof. exact (MK_COMB (@lem1767475) (@lem1767474)). Qed.
Lemma lem1767477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767478 : term661 = term662.
Proof. exact (MK_COMB (@lem1767477) (@lem1767476)). Qed.
Lemma lem1767479 (x : real) : (term658 x) = (term484 x).
Proof. exact (eq_refl (term658 x)). Qed.
Lemma lem1767480 : term663 = term657.
Proof. exact (fun_ext (fun x : real => @lem1767479 x)). Qed.
Lemma lem1767481 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767482 : term664 = term665.
Proof. exact (MK_COMB (@lem1767481) (@lem1767480)). Qed.
Lemma lem1767483 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767484 : term656 = term666.
Proof. exact (MK_COMB (@lem1767483) (@lem1767482)). Qed.
Lemma lem1767485 : (term655 = term656) = (term648 = term666).
Proof. exact (MK_COMB (@lem1767478) (@lem1767484)). Qed.
Lemma lem1767486 : term648 = term666.
Proof. exact (EQ_MP (@lem1767485) (@lem1767470)). Qed.
Lemma lem1767488 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767489 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767488 real P Q). Qed.
Lemma lem1767490 : term667 = term668.
Proof. exact (@lem1767489 term572 term669). Qed.
Lemma lem1767491 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767493 (x : real) : (term575 x) = (term441 x).
Proof. exact (MK_COMB (@lem1767492) (@lem1767491 x)). Qed.
Lemma lem1767494 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767495 (x : real) : (term671 x) = (term484 x).
Proof. exact (MK_COMB (@lem1767493 x) (@lem1767494 x)). Qed.
Lemma lem1767496 : term672 = term657.
Proof. exact (fun_ext (fun x : real => @lem1767495 x)). Qed.
Lemma lem1767497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767498 : term667 = term665.
Proof. exact (MK_COMB (@lem1767497) (@lem1767496)). Qed.
Lemma lem1767499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767500 : term673 = term674.
Proof. exact (MK_COMB (@lem1767499) (@lem1767498)). Qed.
Lemma lem1767501 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767502 : term581 = term572.
Proof. exact (fun_ext (fun x : real => @lem1767501 x)). Qed.
Lemma lem1767503 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767504 : term582 = term583.
Proof. exact (MK_COMB (@lem1767503) (@lem1767502)). Qed.
Lemma lem1767505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767506 : term584 = term585.
Proof. exact (MK_COMB (@lem1767505) (@lem1767504)). Qed.
Lemma lem1767507 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767508 : term675 = term669.
Proof. exact (fun_ext (fun x : real => @lem1767507 x)). Qed.
Lemma lem1767509 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767510 : term676 = term677.
Proof. exact (MK_COMB (@lem1767509) (@lem1767508)). Qed.
Lemma lem1767511 : term668 = term678.
Proof. exact (MK_COMB (@lem1767506) (@lem1767510)). Qed.
Lemma lem1767512 : (term667 = term668) = (term665 = term678).
Proof. exact (MK_COMB (@lem1767500) (@lem1767511)). Qed.
Lemma lem1767513 : term665 = term678.
Proof. exact (EQ_MP (@lem1767512) (@lem1767490)). Qed.
Lemma lem1767610 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767611 : term666 = term679.
Proof. exact (MK_COMB (@lem1767610) (@lem1767513)). Qed.
Lemma lem1767612 : term648 = term679.
Proof. exact (TRANS (@lem1767486) (@lem1767611)). Qed.
Lemma lem1767613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767614 : term650 = term680.
Proof. exact (MK_COMB (@lem1767613) (@lem1767612)). Qed.
Lemma lem1767616 {A : Type'} (P : Prop) (Q : A -> Prop) : (term522 A P Q) = (term523 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1767617 (P : Prop) (Q : real -> Prop) : (term524 P Q) = (term525 P Q).
Proof. exact (@lem1767616 real P Q). Qed.
Lemma lem1767618 : term681 = term682.
Proof. exact (@lem1767617 term323 term683). Qed.
Lemma lem1767619 (x : real) : (term684 x) = (term486 x).
Proof. exact (eq_refl (term684 x)). Qed.
Lemma lem1767620 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767621 (x : real) : (term685 x) = (term487 x).
Proof. exact (MK_COMB (@lem1767620) (@lem1767619 x)). Qed.
Lemma lem1767622 : term686 = term638.
Proof. exact (fun_ext (fun x : real => @lem1767621 x)). Qed.
Lemma lem1767623 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767624 : term681 = term653.
Proof. exact (MK_COMB (@lem1767623) (@lem1767622)). Qed.
Lemma lem1767625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767626 : term687 = term688.
Proof. exact (MK_COMB (@lem1767625) (@lem1767624)). Qed.
Lemma lem1767627 (x : real) : (term684 x) = (term486 x).
Proof. exact (eq_refl (term684 x)). Qed.
Lemma lem1767628 : term689 = term683.
Proof. exact (fun_ext (fun x : real => @lem1767627 x)). Qed.
Lemma lem1767629 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767630 : term690 = term691.
Proof. exact (MK_COMB (@lem1767629) (@lem1767628)). Qed.
Lemma lem1767631 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767632 : term682 = term692.
Proof. exact (MK_COMB (@lem1767631) (@lem1767630)). Qed.
Lemma lem1767633 : (term681 = term682) = (term653 = term692).
Proof. exact (MK_COMB (@lem1767626) (@lem1767632)). Qed.
Lemma lem1767634 : term653 = term692.
Proof. exact (EQ_MP (@lem1767633) (@lem1767618)). Qed.
Lemma lem1767636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1767637 (P : real -> Prop) (Q : real -> Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem1767636 real P Q). Qed.
Lemma lem1767638 : term693 = term694.
Proof. exact (@lem1767637 term606 term669). Qed.
Lemma lem1767639 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767641 (x : real) : (term608 x) = (term467 x).
Proof. exact (MK_COMB (@lem1767640) (@lem1767639 x)). Qed.
Lemma lem1767642 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767643 (x : real) : (term695 x) = (term486 x).
Proof. exact (MK_COMB (@lem1767641 x) (@lem1767642 x)). Qed.
Lemma lem1767644 : term696 = term683.
Proof. exact (fun_ext (fun x : real => @lem1767643 x)). Qed.
Lemma lem1767645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767646 : term693 = term691.
Proof. exact (MK_COMB (@lem1767645) (@lem1767644)). Qed.
Lemma lem1767647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767648 : term697 = term698.
Proof. exact (MK_COMB (@lem1767647) (@lem1767646)). Qed.
Lemma lem1767649 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767650 : term613 = term606.
Proof. exact (fun_ext (fun x : real => @lem1767649 x)). Qed.
Lemma lem1767651 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767652 : term614 = term615.
Proof. exact (MK_COMB (@lem1767651) (@lem1767650)). Qed.
Lemma lem1767653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767654 : term616 = term617.
Proof. exact (MK_COMB (@lem1767653) (@lem1767652)). Qed.
Lemma lem1767655 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767656 : term675 = term669.
Proof. exact (fun_ext (fun x : real => @lem1767655 x)). Qed.
Lemma lem1767657 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767658 : term676 = term677.
Proof. exact (MK_COMB (@lem1767657) (@lem1767656)). Qed.
Lemma lem1767659 : term694 = term699.
Proof. exact (MK_COMB (@lem1767654) (@lem1767658)). Qed.
Lemma lem1767660 : (term693 = term694) = (term691 = term699).
Proof. exact (MK_COMB (@lem1767648) (@lem1767659)). Qed.
Lemma lem1767661 : term691 = term699.
Proof. exact (EQ_MP (@lem1767660) (@lem1767638)). Qed.
Lemma lem1767758 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767759 : term692 = term700.
Proof. exact (MK_COMB (@lem1767758) (@lem1767661)). Qed.
Lemma lem1767760 : term653 = term700.
Proof. exact (TRANS (@lem1767634) (@lem1767759)). Qed.
Lemma lem1767761 : term654 = term701.
Proof. exact (MK_COMB (@lem1767614) (@lem1767760)). Qed.
Lemma lem1767762 : term633 = term701.
Proof. exact (TRANS (@lem1767466) (@lem1767761)). Qed.
Lemma lem1767763 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1767764 : term634 = term702.
Proof. exact (MK_COMB (@lem1767763) (@lem1767762)). Qed.
Lemma lem1767765 : term520 = term702.
Proof. exact (TRANS (@lem1767439) (@lem1767764)). Qed.
Lemma lem1767766 : term521 = term703.
Proof. exact (MK_COMB (@lem1767419) (@lem1767765)). Qed.
Lemma lem1767767 : term497 = term703.
Proof. exact (TRANS (@lem1767071) (@lem1767766)). Qed.
Lemma lem1767769 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1767770 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1767769 real P Q). Qed.
Lemma lem1767771 : term571 = term570.
Proof. exact (@lem1767770 term572 term573). Qed.
Lemma lem1767772 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767773 : term581 = term572.
Proof. exact (fun_ext (fun x : real => @lem1767772 x)). Qed.
Lemma lem1767774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767775 : term582 = term583.
Proof. exact (MK_COMB (@lem1767774) (@lem1767773)). Qed.
Lemma lem1767776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767777 : term584 = term585.
Proof. exact (MK_COMB (@lem1767776) (@lem1767775)). Qed.
Lemma lem1767778 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767779 : term586 = term573.
Proof. exact (fun_ext (fun x : real => @lem1767778 x)). Qed.
Lemma lem1767780 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767781 : term587 = term588.
Proof. exact (MK_COMB (@lem1767780) (@lem1767779)). Qed.
Lemma lem1767782 : term571 = term589.
Proof. exact (MK_COMB (@lem1767777) (@lem1767781)). Qed.
Lemma lem1767783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767784 : term704 = term705.
Proof. exact (MK_COMB (@lem1767783) (@lem1767782)). Qed.
Lemma lem1767785 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767787 (x : real) : (term575 x) = (term441 x).
Proof. exact (MK_COMB (@lem1767786) (@lem1767785 x)). Qed.
Lemma lem1767788 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767789 (x : real) : (term577 x) = (term442 x).
Proof. exact (MK_COMB (@lem1767787 x) (@lem1767788 x)). Qed.
Lemma lem1767790 : term578 = term560.
Proof. exact (fun_ext (fun x : real => @lem1767789 x)). Qed.
Lemma lem1767791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767792 : term570 = term568.
Proof. exact (MK_COMB (@lem1767791) (@lem1767790)). Qed.
Lemma lem1767793 : (term571 = term570) = (term589 = term568).
Proof. exact (MK_COMB (@lem1767784) (@lem1767792)). Qed.
Lemma lem1767794 : term589 = term568.
Proof. exact (EQ_MP (@lem1767793) (@lem1767771)). Qed.
Lemma lem1767795 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767796 : term590 = term569.
Proof. exact (MK_COMB (@lem1767795) (@lem1767794)). Qed.
Lemma lem1767798 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1767799 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1767798 real P Q). Qed.
Lemma lem1767800 : term559 = term558.
Proof. exact (@lem1767799 term295 term560). Qed.
Lemma lem1767801 (x : real) : (term561 x) = (term442 x).
Proof. exact (eq_refl (term561 x)). Qed.
Lemma lem1767802 : term566 = term560.
Proof. exact (fun_ext (fun x : real => @lem1767801 x)). Qed.
Lemma lem1767803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767804 : term567 = term568.
Proof. exact (MK_COMB (@lem1767803) (@lem1767802)). Qed.
Lemma lem1767805 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767806 : term559 = term569.
Proof. exact (MK_COMB (@lem1767805) (@lem1767804)). Qed.
Lemma lem1767807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767808 : term706 = term707.
Proof. exact (MK_COMB (@lem1767807) (@lem1767806)). Qed.
Lemma lem1767809 (x : real) : (term561 x) = (term442 x).
Proof. exact (eq_refl (term561 x)). Qed.
Lemma lem1767810 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767811 (x : real) : (term562 x) = (term444 x).
Proof. exact (MK_COMB (@lem1767810) (@lem1767809 x)). Qed.
Lemma lem1767812 : term563 = term540.
Proof. exact (fun_ext (fun x : real => @lem1767811 x)). Qed.
Lemma lem1767813 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767814 : term558 = term551.
Proof. exact (MK_COMB (@lem1767813) (@lem1767812)). Qed.
Lemma lem1767815 : (term559 = term558) = (term569 = term551).
Proof. exact (MK_COMB (@lem1767808) (@lem1767814)). Qed.
Lemma lem1767816 : term569 = term551.
Proof. exact (EQ_MP (@lem1767815) (@lem1767800)). Qed.
Lemma lem1767817 : term590 = term551.
Proof. exact (TRANS (@lem1767796) (@lem1767816)). Qed.
Lemma lem1767818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767819 : term591 = term553.
Proof. exact (MK_COMB (@lem1767818) (@lem1767817)). Qed.
Lemma lem1767821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1767822 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1767821 real P Q). Qed.
Lemma lem1767823 : term605 = term604.
Proof. exact (@lem1767822 term606 term573). Qed.
Lemma lem1767824 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767825 : term613 = term606.
Proof. exact (fun_ext (fun x : real => @lem1767824 x)). Qed.
Lemma lem1767826 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767827 : term614 = term615.
Proof. exact (MK_COMB (@lem1767826) (@lem1767825)). Qed.
Lemma lem1767828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767829 : term616 = term617.
Proof. exact (MK_COMB (@lem1767828) (@lem1767827)). Qed.
Lemma lem1767830 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767831 : term586 = term573.
Proof. exact (fun_ext (fun x : real => @lem1767830 x)). Qed.
Lemma lem1767832 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767833 : term587 = term588.
Proof. exact (MK_COMB (@lem1767832) (@lem1767831)). Qed.
Lemma lem1767834 : term605 = term618.
Proof. exact (MK_COMB (@lem1767829) (@lem1767833)). Qed.
Lemma lem1767835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767836 : term708 = term709.
Proof. exact (MK_COMB (@lem1767835) (@lem1767834)). Qed.
Lemma lem1767837 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767839 (x : real) : (term608 x) = (term467 x).
Proof. exact (MK_COMB (@lem1767838) (@lem1767837 x)). Qed.
Lemma lem1767840 (x : real) : (term576 x) = (term440 x).
Proof. exact (eq_refl (term576 x)). Qed.
Lemma lem1767841 (x : real) : (term609 x) = (term468 x).
Proof. exact (MK_COMB (@lem1767839 x) (@lem1767840 x)). Qed.
Lemma lem1767842 : term610 = term594.
Proof. exact (fun_ext (fun x : real => @lem1767841 x)). Qed.
Lemma lem1767843 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767844 : term604 = term602.
Proof. exact (MK_COMB (@lem1767843) (@lem1767842)). Qed.
Lemma lem1767845 : (term605 = term604) = (term618 = term602).
Proof. exact (MK_COMB (@lem1767836) (@lem1767844)). Qed.
Lemma lem1767846 : term618 = term602.
Proof. exact (EQ_MP (@lem1767845) (@lem1767823)). Qed.
Lemma lem1767847 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767848 : term619 = term603.
Proof. exact (MK_COMB (@lem1767847) (@lem1767846)). Qed.
Lemma lem1767850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1767851 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1767850 real P Q). Qed.
Lemma lem1767852 : term593 = term592.
Proof. exact (@lem1767851 term323 term594). Qed.
Lemma lem1767853 (x : real) : (term595 x) = (term468 x).
Proof. exact (eq_refl (term595 x)). Qed.
Lemma lem1767854 : term600 = term594.
Proof. exact (fun_ext (fun x : real => @lem1767853 x)). Qed.
Lemma lem1767855 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767856 : term601 = term602.
Proof. exact (MK_COMB (@lem1767855) (@lem1767854)). Qed.
Lemma lem1767857 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767858 : term593 = term603.
Proof. exact (MK_COMB (@lem1767857) (@lem1767856)). Qed.
Lemma lem1767859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767860 : term710 = term711.
Proof. exact (MK_COMB (@lem1767859) (@lem1767858)). Qed.
Lemma lem1767861 (x : real) : (term595 x) = (term468 x).
Proof. exact (eq_refl (term595 x)). Qed.
Lemma lem1767862 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1767863 (x : real) : (term596 x) = (term469 x).
Proof. exact (MK_COMB (@lem1767862) (@lem1767861 x)). Qed.
Lemma lem1767864 : term597 = term541.
Proof. exact (fun_ext (fun x : real => @lem1767863 x)). Qed.
Lemma lem1767865 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767866 : term592 = term556.
Proof. exact (MK_COMB (@lem1767865) (@lem1767864)). Qed.
Lemma lem1767867 : (term593 = term592) = (term603 = term556).
Proof. exact (MK_COMB (@lem1767860) (@lem1767866)). Qed.
Lemma lem1767868 : term603 = term556.
Proof. exact (EQ_MP (@lem1767867) (@lem1767852)). Qed.
Lemma lem1767869 : term619 = term556.
Proof. exact (TRANS (@lem1767848) (@lem1767868)). Qed.
Lemma lem1767870 : term620 = term557.
Proof. exact (MK_COMB (@lem1767819) (@lem1767869)). Qed.
Lemma lem1767872 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1767873 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1767872 real P Q). Qed.
Lemma lem1767874 : term539 = term538.
Proof. exact (@lem1767873 term540 term541). Qed.
Lemma lem1767875 (x : real) : (term542 x) = (term444 x).
Proof. exact (eq_refl (term542 x)). Qed.
Lemma lem1767876 : term549 = term540.
Proof. exact (fun_ext (fun x : real => @lem1767875 x)). Qed.
Lemma lem1767877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767878 : term550 = term551.
Proof. exact (MK_COMB (@lem1767877) (@lem1767876)). Qed.
Lemma lem1767879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767880 : term552 = term553.
Proof. exact (MK_COMB (@lem1767879) (@lem1767878)). Qed.
Lemma lem1767881 (x : real) : (term544 x) = (term469 x).
Proof. exact (eq_refl (term544 x)). Qed.
Lemma lem1767882 : term554 = term541.
Proof. exact (fun_ext (fun x : real => @lem1767881 x)). Qed.
Lemma lem1767883 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767884 : term555 = term556.
Proof. exact (MK_COMB (@lem1767883) (@lem1767882)). Qed.
Lemma lem1767885 : term539 = term557.
Proof. exact (MK_COMB (@lem1767880) (@lem1767884)). Qed.
Lemma lem1767886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767887 : term712 = term713.
Proof. exact (MK_COMB (@lem1767886) (@lem1767885)). Qed.
Lemma lem1767888 (x : real) : (term542 x) = (term444 x).
Proof. exact (eq_refl (term542 x)). Qed.
Lemma lem1767889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767890 (x : real) : (term543 x) = (term470 x).
Proof. exact (MK_COMB (@lem1767889) (@lem1767888 x)). Qed.
Lemma lem1767891 (x : real) : (term544 x) = (term469 x).
Proof. exact (eq_refl (term544 x)). Qed.
Lemma lem1767892 (x : real) : (term545 x) = (term471 x).
Proof. exact (MK_COMB (@lem1767890 x) (@lem1767891 x)). Qed.
Lemma lem1767893 : term546 = term528.
Proof. exact (fun_ext (fun x : real => @lem1767892 x)). Qed.
Lemma lem1767894 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767895 : term538 = term536.
Proof. exact (MK_COMB (@lem1767894) (@lem1767893)). Qed.
Lemma lem1767896 : (term539 = term538) = (term557 = term536).
Proof. exact (MK_COMB (@lem1767887) (@lem1767895)). Qed.
Lemma lem1767897 : term557 = term536.
Proof. exact (EQ_MP (@lem1767896) (@lem1767874)). Qed.
Lemma lem1767898 : term620 = term536.
Proof. exact (TRANS (@lem1767870) (@lem1767897)). Qed.
Lemma lem1767899 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767900 : term621 = term537.
Proof. exact (MK_COMB (@lem1767899) (@lem1767898)). Qed.
Lemma lem1767902 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1767903 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1767902 real P Q). Qed.
Lemma lem1767904 : term527 = term526.
Proof. exact (@lem1767903 term282 term528). Qed.
Lemma lem1767905 (x : real) : (term529 x) = (term471 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1767906 : term534 = term528.
Proof. exact (fun_ext (fun x : real => @lem1767905 x)). Qed.
Lemma lem1767907 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767908 : term535 = term536.
Proof. exact (MK_COMB (@lem1767907) (@lem1767906)). Qed.
Lemma lem1767909 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767910 : term527 = term537.
Proof. exact (MK_COMB (@lem1767909) (@lem1767908)). Qed.
Lemma lem1767911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767912 : term714 = term715.
Proof. exact (MK_COMB (@lem1767911) (@lem1767910)). Qed.
Lemma lem1767913 (x : real) : (term529 x) = (term471 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1767914 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1767915 (x : real) : (term530 x) = (term474 x).
Proof. exact (MK_COMB (@lem1767914) (@lem1767913 x)). Qed.
Lemma lem1767916 : term531 = term504.
Proof. exact (fun_ext (fun x : real => @lem1767915 x)). Qed.
Lemma lem1767917 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767918 : term526 = term515.
Proof. exact (MK_COMB (@lem1767917) (@lem1767916)). Qed.
Lemma lem1767919 : (term527 = term526) = (term537 = term515).
Proof. exact (MK_COMB (@lem1767912) (@lem1767918)). Qed.
Lemma lem1767920 : term537 = term515.
Proof. exact (EQ_MP (@lem1767919) (@lem1767904)). Qed.
Lemma lem1767921 : term621 = term515.
Proof. exact (TRANS (@lem1767900) (@lem1767920)). Qed.
Lemma lem1767922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767923 : term622 = term517.
Proof. exact (MK_COMB (@lem1767922) (@lem1767921)). Qed.
Lemma lem1767925 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1767926 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1767925 real P Q). Qed.
Lemma lem1767927 : term668 = term667.
Proof. exact (@lem1767926 term572 term669). Qed.
Lemma lem1767928 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767929 : term581 = term572.
Proof. exact (fun_ext (fun x : real => @lem1767928 x)). Qed.
Lemma lem1767930 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767931 : term582 = term583.
Proof. exact (MK_COMB (@lem1767930) (@lem1767929)). Qed.
Lemma lem1767932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767933 : term584 = term585.
Proof. exact (MK_COMB (@lem1767932) (@lem1767931)). Qed.
Lemma lem1767934 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767935 : term675 = term669.
Proof. exact (fun_ext (fun x : real => @lem1767934 x)). Qed.
Lemma lem1767936 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767937 : term676 = term677.
Proof. exact (MK_COMB (@lem1767936) (@lem1767935)). Qed.
Lemma lem1767938 : term668 = term678.
Proof. exact (MK_COMB (@lem1767933) (@lem1767937)). Qed.
Lemma lem1767939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767940 : term716 = term717.
Proof. exact (MK_COMB (@lem1767939) (@lem1767938)). Qed.
Lemma lem1767941 (x : real) : (term574 x) = (term417 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1767942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767943 (x : real) : (term575 x) = (term441 x).
Proof. exact (MK_COMB (@lem1767942) (@lem1767941 x)). Qed.
Lemma lem1767944 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767945 (x : real) : (term671 x) = (term484 x).
Proof. exact (MK_COMB (@lem1767943 x) (@lem1767944 x)). Qed.
Lemma lem1767946 : term672 = term657.
Proof. exact (fun_ext (fun x : real => @lem1767945 x)). Qed.
Lemma lem1767947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767948 : term667 = term665.
Proof. exact (MK_COMB (@lem1767947) (@lem1767946)). Qed.
Lemma lem1767949 : (term668 = term667) = (term678 = term665).
Proof. exact (MK_COMB (@lem1767940) (@lem1767948)). Qed.
Lemma lem1767950 : term678 = term665.
Proof. exact (EQ_MP (@lem1767949) (@lem1767927)). Qed.
Lemma lem1767951 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767952 : term679 = term666.
Proof. exact (MK_COMB (@lem1767951) (@lem1767950)). Qed.
Lemma lem1767954 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1767955 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1767954 real P Q). Qed.
Lemma lem1767956 : term656 = term655.
Proof. exact (@lem1767955 term295 term657). Qed.
Lemma lem1767957 (x : real) : (term658 x) = (term484 x).
Proof. exact (eq_refl (term658 x)). Qed.
Lemma lem1767958 : term663 = term657.
Proof. exact (fun_ext (fun x : real => @lem1767957 x)). Qed.
Lemma lem1767959 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767960 : term664 = term665.
Proof. exact (MK_COMB (@lem1767959) (@lem1767958)). Qed.
Lemma lem1767961 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767962 : term656 = term666.
Proof. exact (MK_COMB (@lem1767961) (@lem1767960)). Qed.
Lemma lem1767963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767964 : term718 = term719.
Proof. exact (MK_COMB (@lem1767963) (@lem1767962)). Qed.
Lemma lem1767965 (x : real) : (term658 x) = (term484 x).
Proof. exact (eq_refl (term658 x)). Qed.
Lemma lem1767966 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1767967 (x : real) : (term659 x) = (term485 x).
Proof. exact (MK_COMB (@lem1767966) (@lem1767965 x)). Qed.
Lemma lem1767968 : term660 = term637.
Proof. exact (fun_ext (fun x : real => @lem1767967 x)). Qed.
Lemma lem1767969 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767970 : term655 = term648.
Proof. exact (MK_COMB (@lem1767969) (@lem1767968)). Qed.
Lemma lem1767971 : (term656 = term655) = (term666 = term648).
Proof. exact (MK_COMB (@lem1767964) (@lem1767970)). Qed.
Lemma lem1767972 : term666 = term648.
Proof. exact (EQ_MP (@lem1767971) (@lem1767956)). Qed.
Lemma lem1767973 : term679 = term648.
Proof. exact (TRANS (@lem1767952) (@lem1767972)). Qed.
Lemma lem1767974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767975 : term680 = term650.
Proof. exact (MK_COMB (@lem1767974) (@lem1767973)). Qed.
Lemma lem1767977 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1767978 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1767977 real P Q). Qed.
Lemma lem1767979 : term694 = term693.
Proof. exact (@lem1767978 term606 term669). Qed.
Lemma lem1767980 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767981 : term613 = term606.
Proof. exact (fun_ext (fun x : real => @lem1767980 x)). Qed.
Lemma lem1767982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767983 : term614 = term615.
Proof. exact (MK_COMB (@lem1767982) (@lem1767981)). Qed.
Lemma lem1767984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767985 : term616 = term617.
Proof. exact (MK_COMB (@lem1767984) (@lem1767983)). Qed.
Lemma lem1767986 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767987 : term675 = term669.
Proof. exact (fun_ext (fun x : real => @lem1767986 x)). Qed.
Lemma lem1767988 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1767989 : term676 = term677.
Proof. exact (MK_COMB (@lem1767988) (@lem1767987)). Qed.
Lemma lem1767990 : term694 = term699.
Proof. exact (MK_COMB (@lem1767985) (@lem1767989)). Qed.
Lemma lem1767991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1767992 : term720 = term721.
Proof. exact (MK_COMB (@lem1767991) (@lem1767990)). Qed.
Lemma lem1767993 (x : real) : (term607 x) = (term466 x).
Proof. exact (eq_refl (term607 x)). Qed.
Lemma lem1767994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1767995 (x : real) : (term608 x) = (term467 x).
Proof. exact (MK_COMB (@lem1767994) (@lem1767993 x)). Qed.
Lemma lem1767996 (x : real) : (term670 x) = (term483 x).
Proof. exact (eq_refl (term670 x)). Qed.
Lemma lem1767997 (x : real) : (term695 x) = (term486 x).
Proof. exact (MK_COMB (@lem1767995 x) (@lem1767996 x)). Qed.
Lemma lem1767998 : term696 = term683.
Proof. exact (fun_ext (fun x : real => @lem1767997 x)). Qed.
Lemma lem1767999 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768000 : term693 = term691.
Proof. exact (MK_COMB (@lem1767999) (@lem1767998)). Qed.
Lemma lem1768001 : (term694 = term693) = (term699 = term691).
Proof. exact (MK_COMB (@lem1767992) (@lem1768000)). Qed.
Lemma lem1768002 : term699 = term691.
Proof. exact (EQ_MP (@lem1768001) (@lem1767979)). Qed.
Lemma lem1768003 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1768004 : term700 = term692.
Proof. exact (MK_COMB (@lem1768003) (@lem1768002)). Qed.
Lemma lem1768006 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1768007 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1768006 real P Q). Qed.
Lemma lem1768008 : term682 = term681.
Proof. exact (@lem1768007 term323 term683). Qed.
Lemma lem1768009 (x : real) : (term684 x) = (term486 x).
Proof. exact (eq_refl (term684 x)). Qed.
Lemma lem1768010 : term689 = term683.
Proof. exact (fun_ext (fun x : real => @lem1768009 x)). Qed.
Lemma lem1768011 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768012 : term690 = term691.
Proof. exact (MK_COMB (@lem1768011) (@lem1768010)). Qed.
Lemma lem1768013 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1768014 : term682 = term692.
Proof. exact (MK_COMB (@lem1768013) (@lem1768012)). Qed.
Lemma lem1768015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1768016 : term722 = term723.
Proof. exact (MK_COMB (@lem1768015) (@lem1768014)). Qed.
Lemma lem1768017 (x : real) : (term684 x) = (term486 x).
Proof. exact (eq_refl (term684 x)). Qed.
Lemma lem1768018 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1768019 (x : real) : (term685 x) = (term487 x).
Proof. exact (MK_COMB (@lem1768018) (@lem1768017 x)). Qed.
Lemma lem1768020 : term686 = term638.
Proof. exact (fun_ext (fun x : real => @lem1768019 x)). Qed.
Lemma lem1768021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768022 : term681 = term653.
Proof. exact (MK_COMB (@lem1768021) (@lem1768020)). Qed.
Lemma lem1768023 : (term682 = term681) = (term692 = term653).
Proof. exact (MK_COMB (@lem1768016) (@lem1768022)). Qed.
Lemma lem1768024 : term692 = term653.
Proof. exact (EQ_MP (@lem1768023) (@lem1768008)). Qed.
Lemma lem1768025 : term700 = term653.
Proof. exact (TRANS (@lem1768004) (@lem1768024)). Qed.
Lemma lem1768026 : term701 = term654.
Proof. exact (MK_COMB (@lem1767975) (@lem1768025)). Qed.
Lemma lem1768028 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1768029 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1768028 real P Q). Qed.
Lemma lem1768030 : term636 = term635.
Proof. exact (@lem1768029 term637 term638). Qed.
Lemma lem1768031 (x : real) : (term639 x) = (term485 x).
Proof. exact (eq_refl (term639 x)). Qed.
Lemma lem1768032 : term646 = term637.
Proof. exact (fun_ext (fun x : real => @lem1768031 x)). Qed.
Lemma lem1768033 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768034 : term647 = term648.
Proof. exact (MK_COMB (@lem1768033) (@lem1768032)). Qed.
Lemma lem1768035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768036 : term649 = term650.
Proof. exact (MK_COMB (@lem1768035) (@lem1768034)). Qed.
Lemma lem1768037 (x : real) : (term641 x) = (term487 x).
Proof. exact (eq_refl (term641 x)). Qed.
Lemma lem1768038 : term651 = term638.
Proof. exact (fun_ext (fun x : real => @lem1768037 x)). Qed.
Lemma lem1768039 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768040 : term652 = term653.
Proof. exact (MK_COMB (@lem1768039) (@lem1768038)). Qed.
Lemma lem1768041 : term636 = term654.
Proof. exact (MK_COMB (@lem1768036) (@lem1768040)). Qed.
Lemma lem1768042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1768043 : term724 = term725.
Proof. exact (MK_COMB (@lem1768042) (@lem1768041)). Qed.
Lemma lem1768044 (x : real) : (term639 x) = (term485 x).
Proof. exact (eq_refl (term639 x)). Qed.
Lemma lem1768045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768046 (x : real) : (term640 x) = (term488 x).
Proof. exact (MK_COMB (@lem1768045) (@lem1768044 x)). Qed.
Lemma lem1768047 (x : real) : (term641 x) = (term487 x).
Proof. exact (eq_refl (term641 x)). Qed.
Lemma lem1768048 (x : real) : (term642 x) = (term489 x).
Proof. exact (MK_COMB (@lem1768046 x) (@lem1768047 x)). Qed.
Lemma lem1768049 : term643 = term625.
Proof. exact (fun_ext (fun x : real => @lem1768048 x)). Qed.
Lemma lem1768050 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768051 : term635 = term633.
Proof. exact (MK_COMB (@lem1768050) (@lem1768049)). Qed.
Lemma lem1768052 : (term636 = term635) = (term654 = term633).
Proof. exact (MK_COMB (@lem1768043) (@lem1768051)). Qed.
Lemma lem1768053 : term654 = term633.
Proof. exact (EQ_MP (@lem1768052) (@lem1768030)). Qed.
Lemma lem1768054 : term701 = term633.
Proof. exact (TRANS (@lem1768026) (@lem1768053)). Qed.
Lemma lem1768055 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1768056 : term702 = term634.
Proof. exact (MK_COMB (@lem1768055) (@lem1768054)). Qed.
Lemma lem1768058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term523 A P Q) = (term522 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1768059 (P : Prop) (Q : real -> Prop) : (term525 P Q) = (term524 P Q).
Proof. exact (@lem1768058 real P Q). Qed.
Lemma lem1768060 : term624 = term623.
Proof. exact (@lem1768059 term478 term625). Qed.
Lemma lem1768061 (x : real) : (term626 x) = (term489 x).
Proof. exact (eq_refl (term626 x)). Qed.
Lemma lem1768062 : term631 = term625.
Proof. exact (fun_ext (fun x : real => @lem1768061 x)). Qed.
Lemma lem1768063 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768064 : term632 = term633.
Proof. exact (MK_COMB (@lem1768063) (@lem1768062)). Qed.
Lemma lem1768065 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1768066 : term624 = term634.
Proof. exact (MK_COMB (@lem1768065) (@lem1768064)). Qed.
Lemma lem1768067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1768068 : term726 = term727.
Proof. exact (MK_COMB (@lem1768067) (@lem1768066)). Qed.
Lemma lem1768069 (x : real) : (term626 x) = (term489 x).
Proof. exact (eq_refl (term626 x)). Qed.
Lemma lem1768070 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1768071 (x : real) : (term627 x) = (term492 x).
Proof. exact (MK_COMB (@lem1768070) (@lem1768069 x)). Qed.
Lemma lem1768072 : term628 = term505.
Proof. exact (fun_ext (fun x : real => @lem1768071 x)). Qed.
Lemma lem1768073 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768074 : term623 = term520.
Proof. exact (MK_COMB (@lem1768073) (@lem1768072)). Qed.
Lemma lem1768075 : (term624 = term623) = (term634 = term520).
Proof. exact (MK_COMB (@lem1768068) (@lem1768074)). Qed.
Lemma lem1768076 : term634 = term520.
Proof. exact (EQ_MP (@lem1768075) (@lem1768060)). Qed.
Lemma lem1768077 : term702 = term520.
Proof. exact (TRANS (@lem1768056) (@lem1768076)). Qed.
Lemma lem1768078 : term703 = term521.
Proof. exact (MK_COMB (@lem1767923) (@lem1768077)). Qed.
Lemma lem1768080 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term499 A P Q) = (term498 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1768081 (P : real -> Prop) (Q : real -> Prop) : (term501 P Q) = (term500 P Q).
Proof. exact (@lem1768080 real P Q). Qed.
Lemma lem1768082 : term503 = term502.
Proof. exact (@lem1768081 term504 term505). Qed.
Lemma lem1768083 (x : real) : (term506 x) = (term474 x).
Proof. exact (eq_refl (term506 x)). Qed.
Lemma lem1768084 : term513 = term504.
Proof. exact (fun_ext (fun x : real => @lem1768083 x)). Qed.
Lemma lem1768085 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768086 : term514 = term515.
Proof. exact (MK_COMB (@lem1768085) (@lem1768084)). Qed.
Lemma lem1768087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768088 : term516 = term517.
Proof. exact (MK_COMB (@lem1768087) (@lem1768086)). Qed.
Lemma lem1768089 (x : real) : (term508 x) = (term492 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1768090 : term518 = term505.
Proof. exact (fun_ext (fun x : real => @lem1768089 x)). Qed.
Lemma lem1768091 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768092 : term519 = term520.
Proof. exact (MK_COMB (@lem1768091) (@lem1768090)). Qed.
Lemma lem1768093 : term503 = term521.
Proof. exact (MK_COMB (@lem1768088) (@lem1768092)). Qed.
Lemma lem1768094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1768095 : term728 = term729.
Proof. exact (MK_COMB (@lem1768094) (@lem1768093)). Qed.
Lemma lem1768096 (x : real) : (term506 x) = (term474 x).
Proof. exact (eq_refl (term506 x)). Qed.
Lemma lem1768097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768098 (x : real) : (term507 x) = (term494 x).
Proof. exact (MK_COMB (@lem1768097) (@lem1768096 x)). Qed.
Lemma lem1768099 (x : real) : (term508 x) = (term492 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1768100 (x : real) : (term509 x) = (term495 x).
Proof. exact (MK_COMB (@lem1768098 x) (@lem1768099 x)). Qed.
Lemma lem1768101 : term510 = term496.
Proof. exact (fun_ext (fun x : real => @lem1768100 x)). Qed.
Lemma lem1768102 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1768103 : term502 = term497.
Proof. exact (MK_COMB (@lem1768102) (@lem1768101)). Qed.
Lemma lem1768104 : (term503 = term502) = (term521 = term497).
Proof. exact (MK_COMB (@lem1768095) (@lem1768103)). Qed.
Lemma lem1768105 : term521 = term497.
Proof. exact (EQ_MP (@lem1768104) (@lem1768082)). Qed.
Lemma lem1768106 : term703 = term497.
Proof. exact (TRANS (@lem1768078) (@lem1768105)). Qed.
Lemma lem1768107 : term497 = term497.
Proof. exact (TRANS (@lem1767767) (@lem1768106)). Qed.
Lemma lem1768110 : term33 = term497.
Proof. exact (TRANS (@lem1767044) (@lem1768107)). Qed.
Lemma lem1768127 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1768130 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768131 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1768130 x) (@lem1768127)). Qed.
Lemma lem1768138 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1768139 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1768131 x) (@lem1768138 x)). Qed.
Lemma lem1768142 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1768143 (x : real) : (term480 x) = (term735 x).
Proof. exact (MK_COMB (@lem1768142) (@lem1768139 x)). Qed.
Lemma lem1768150 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1768151 (x : real) : (term480 x) = (term736 x).
Proof. exact (TRANS (@lem1768143 x) (@lem1768150 x)). Qed.
Lemma lem1768168 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1768171 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768172 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1768171 x) (@lem1768168)). Qed.
Lemma lem1768179 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1768180 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1768172 x) (@lem1768179 x)). Qed.
Lemma lem1768183 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1768184 (x : real) : (term479 x) = (term744 x).
Proof. exact (MK_COMB (@lem1768183) (@lem1768180 x)). Qed.
Lemma lem1768191 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1768192 (x : real) : (term479 x) = (term745 x).
Proof. exact (TRANS (@lem1768184 x) (@lem1768191 x)). Qed.
Lemma lem1768193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768194 (x : real) : (term481 x) = (term748 x).
Proof. exact (MK_COMB (@lem1768193) (@lem1768192 x)). Qed.
Lemma lem1768195 (x : real) : (term482 x) = (term749 x).
Proof. exact (MK_COMB (@lem1768194 x) (@lem1768151 x)). Qed.
Lemma lem1768198 (x : real) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem1768199 (x : real) : (term483 x) = (term750 x).
Proof. exact (MK_COMB (@lem1768198 x) (@lem1768195 x)). Qed.
Lemma lem1768200 (x : real) : (term750 x) = (term751 x).
Proof. exact (@lem19158 (term745 x) (term421 x) (term736 x)). Qed.
Lemma lem1768207 (x : real) : (term752 x) = (term753 x).
Proof. exact (@lem19158 (term754 x) (term421 x) (term755 x)). Qed.
Lemma lem1768214 (x : real) : (term756 x) = (term757 x).
Proof. exact (@lem19158 (term758 x) (term421 x) (term759 x)). Qed.
Lemma lem1768215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768216 (x : real) : (term760 x) = (term761 x).
Proof. exact (MK_COMB (@lem1768215) (@lem1768214 x)). Qed.
Lemma lem1768217 (x : real) : (term751 x) = (term762 x).
Proof. exact (MK_COMB (@lem1768216 x) (@lem1768207 x)). Qed.
Lemma lem1768218 (x : real) : (term750 x) = (term762 x).
Proof. exact (TRANS (@lem1768200 x) (@lem1768217 x)). Qed.
Lemma lem1768219 (x : real) : (term483 x) = (term762 x).
Proof. exact (TRANS (@lem1768199 x) (@lem1768218 x)). Qed.
Lemma lem1768236 : term456 = term763.
Proof. exact (@lem19158 term295 term398 term313). Qed.
Lemma lem1768253 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1768254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768255 : term457 = term765.
Proof. exact (MK_COMB (@lem1768254) (@lem1768253)). Qed.
Lemma lem1768256 : term458 = term766.
Proof. exact (MK_COMB (@lem1768255) (@lem1768236)). Qed.
Lemma lem1768259 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1768260 (x : real) : (term459 x) = (term767 x).
Proof. exact (MK_COMB (@lem1768259 x) (@lem1768256)). Qed.
Lemma lem1768261 (x : real) : (term767 x) = (term768 x).
Proof. exact (@lem19158 term764 (term362 x) term763). Qed.
Lemma lem1768268 (x : real) : (term769 x) = (term770 x).
Proof. exact (@lem19158 term771 (term362 x) term772). Qed.
Lemma lem1768275 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1768276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768277 (x : real) : (term777 x) = (term778 x).
Proof. exact (MK_COMB (@lem1768276) (@lem1768275 x)). Qed.
Lemma lem1768278 (x : real) : (term768 x) = (term779 x).
Proof. exact (MK_COMB (@lem1768277 x) (@lem1768268 x)). Qed.
Lemma lem1768279 (x : real) : (term767 x) = (term779 x).
Proof. exact (TRANS (@lem1768261 x) (@lem1768278 x)). Qed.
Lemma lem1768280 (x : real) : (term459 x) = (term779 x).
Proof. exact (TRANS (@lem1768260 x) (@lem1768279 x)). Qed.
Lemma lem1768297 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1768300 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768301 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1768300 x) (@lem1768297)). Qed.
Lemma lem1768308 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1768309 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1768301 x) (@lem1768308 x)). Qed.
Lemma lem1768310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768311 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1768310) (@lem1768309 x)). Qed.
Lemma lem1768312 (x : real) : (term462 x) = (term781 x).
Proof. exact (MK_COMB (@lem1768311 x) (@lem1768280 x)). Qed.
Lemma lem1768315 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1768316 (x : real) : (term463 x) = (term782 x).
Proof. exact (MK_COMB (@lem1768315) (@lem1768312 x)). Qed.
Lemma lem1768317 (x : real) : (term782 x) = (term783 x).
Proof. exact (@lem19158 (term732 x) term398 (term779 x)). Qed.
Lemma lem1768318 (x : real) : (term784 x) = (term785 x).
Proof. exact (@lem19158 (term774 x) term398 (term770 x)). Qed.
Lemma lem1768325 (x : real) : (term786 x) = (term787 x).
Proof. exact (@lem19158 (term788 x) term398 (term789 x)). Qed.
Lemma lem1768332 (x : real) : (term790 x) = (term791 x).
Proof. exact (@lem19158 (term792 x) term398 (term793 x)). Qed.
Lemma lem1768333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768334 (x : real) : (term794 x) = (term795 x).
Proof. exact (MK_COMB (@lem1768333) (@lem1768332 x)). Qed.
Lemma lem1768335 (x : real) : (term785 x) = (term796 x).
Proof. exact (MK_COMB (@lem1768334 x) (@lem1768325 x)). Qed.
Lemma lem1768336 (x : real) : (term784 x) = (term796 x).
Proof. exact (TRANS (@lem1768318 x) (@lem1768335 x)). Qed.
Lemma lem1768343 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1768344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768345 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1768344) (@lem1768343 x)). Qed.
Lemma lem1768346 (x : real) : (term783 x) = (term799 x).
Proof. exact (MK_COMB (@lem1768345 x) (@lem1768336 x)). Qed.
Lemma lem1768347 (x : real) : (term782 x) = (term799 x).
Proof. exact (TRANS (@lem1768317 x) (@lem1768346 x)). Qed.
Lemma lem1768348 (x : real) : (term463 x) = (term799 x).
Proof. exact (TRANS (@lem1768316 x) (@lem1768347 x)). Qed.
Lemma lem1768365 : term456 = term763.
Proof. exact (@lem19158 term295 term398 term313). Qed.
Lemma lem1768382 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1768383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768384 : term457 = term765.
Proof. exact (MK_COMB (@lem1768383) (@lem1768382)). Qed.
Lemma lem1768385 : term458 = term766.
Proof. exact (MK_COMB (@lem1768384) (@lem1768365)). Qed.
Lemma lem1768388 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1768389 (x : real) : (term459 x) = (term767 x).
Proof. exact (MK_COMB (@lem1768388 x) (@lem1768385)). Qed.
Lemma lem1768390 (x : real) : (term767 x) = (term768 x).
Proof. exact (@lem19158 term764 (term362 x) term763). Qed.
Lemma lem1768397 (x : real) : (term769 x) = (term770 x).
Proof. exact (@lem19158 term771 (term362 x) term772). Qed.
Lemma lem1768404 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1768405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768406 (x : real) : (term777 x) = (term778 x).
Proof. exact (MK_COMB (@lem1768405) (@lem1768404 x)). Qed.
Lemma lem1768407 (x : real) : (term768 x) = (term779 x).
Proof. exact (MK_COMB (@lem1768406 x) (@lem1768397 x)). Qed.
Lemma lem1768408 (x : real) : (term767 x) = (term779 x).
Proof. exact (TRANS (@lem1768390 x) (@lem1768407 x)). Qed.
Lemma lem1768409 (x : real) : (term459 x) = (term779 x).
Proof. exact (TRANS (@lem1768389 x) (@lem1768408 x)). Qed.
Lemma lem1768426 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1768429 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768430 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1768429 x) (@lem1768426)). Qed.
Lemma lem1768437 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1768438 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1768430 x) (@lem1768437 x)). Qed.
Lemma lem1768439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768440 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1768439) (@lem1768438 x)). Qed.
Lemma lem1768441 (x : real) : (term460 x) = (term801 x).
Proof. exact (MK_COMB (@lem1768440 x) (@lem1768409 x)). Qed.
Lemma lem1768444 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1768445 (x : real) : (term461 x) = (term802 x).
Proof. exact (MK_COMB (@lem1768444) (@lem1768441 x)). Qed.
Lemma lem1768446 (x : real) : (term802 x) = (term803 x).
Proof. exact (@lem19158 (term741 x) term313 (term779 x)). Qed.
Lemma lem1768447 (x : real) : (term804 x) = (term805 x).
Proof. exact (@lem19158 (term774 x) term313 (term770 x)). Qed.
Lemma lem1768454 (x : real) : (term806 x) = (term807 x).
Proof. exact (@lem19158 (term788 x) term313 (term789 x)). Qed.
Lemma lem1768461 (x : real) : (term808 x) = (term809 x).
Proof. exact (@lem19158 (term792 x) term313 (term793 x)). Qed.
Lemma lem1768462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768463 (x : real) : (term810 x) = (term811 x).
Proof. exact (MK_COMB (@lem1768462) (@lem1768461 x)). Qed.
Lemma lem1768464 (x : real) : (term805 x) = (term812 x).
Proof. exact (MK_COMB (@lem1768463 x) (@lem1768454 x)). Qed.
Lemma lem1768465 (x : real) : (term804 x) = (term812 x).
Proof. exact (TRANS (@lem1768447 x) (@lem1768464 x)). Qed.
Lemma lem1768472 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1768473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768474 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1768473) (@lem1768472 x)). Qed.
Lemma lem1768475 (x : real) : (term803 x) = (term814 x).
Proof. exact (MK_COMB (@lem1768474 x) (@lem1768465 x)). Qed.
Lemma lem1768476 (x : real) : (term802 x) = (term814 x).
Proof. exact (TRANS (@lem1768446 x) (@lem1768475 x)). Qed.
Lemma lem1768477 (x : real) : (term461 x) = (term814 x).
Proof. exact (TRANS (@lem1768445 x) (@lem1768476 x)). Qed.
Lemma lem1768478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768479 (x : real) : (term464 x) = (term815 x).
Proof. exact (MK_COMB (@lem1768478) (@lem1768477 x)). Qed.
Lemma lem1768480 (x : real) : (term465 x) = (term816 x).
Proof. exact (MK_COMB (@lem1768479 x) (@lem1768348 x)). Qed.
Lemma lem1768483 (x : real) : (term416 x) = (term416 x).
Proof. exact (eq_refl (term416 x)). Qed.
Lemma lem1768484 (x : real) : (term466 x) = (term817 x).
Proof. exact (MK_COMB (@lem1768483 x) (@lem1768480 x)). Qed.
Lemma lem1768485 (x : real) : (term817 x) = (term818 x).
Proof. exact (@lem19158 (term814 x) (term302 x) (term799 x)). Qed.
Lemma lem1768486 (x : real) : (term819 x) = (term820 x).
Proof. exact (@lem19158 (term736 x) (term302 x) (term796 x)). Qed.
Lemma lem1768487 (x : real) : (term821 x) = (term822 x).
Proof. exact (@lem19158 (term791 x) (term302 x) (term787 x)). Qed.
Lemma lem1768494 (x : real) : (term823 x) = (term824 x).
Proof. exact (@lem19158 (term825 x) (term302 x) (term826 x)). Qed.
Lemma lem1768501 (x : real) : (term827 x) = (term828 x).
Proof. exact (@lem19158 (term829 x) (term302 x) (term830 x)). Qed.
Lemma lem1768502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768503 (x : real) : (term831 x) = (term832 x).
Proof. exact (MK_COMB (@lem1768502) (@lem1768501 x)). Qed.
Lemma lem1768504 (x : real) : (term822 x) = (term833 x).
Proof. exact (MK_COMB (@lem1768503 x) (@lem1768494 x)). Qed.
Lemma lem1768505 (x : real) : (term821 x) = (term833 x).
Proof. exact (TRANS (@lem1768487 x) (@lem1768504 x)). Qed.
Lemma lem1768512 (x : real) : (term834 x) = (term835 x).
Proof. exact (@lem19158 (term754 x) (term302 x) (term755 x)). Qed.
Lemma lem1768513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768514 (x : real) : (term836 x) = (term837 x).
Proof. exact (MK_COMB (@lem1768513) (@lem1768512 x)). Qed.
Lemma lem1768515 (x : real) : (term820 x) = (term838 x).
Proof. exact (MK_COMB (@lem1768514 x) (@lem1768505 x)). Qed.
Lemma lem1768516 (x : real) : (term819 x) = (term838 x).
Proof. exact (TRANS (@lem1768486 x) (@lem1768515 x)). Qed.
Lemma lem1768517 (x : real) : (term839 x) = (term840 x).
Proof. exact (@lem19158 (term745 x) (term302 x) (term812 x)). Qed.
Lemma lem1768518 (x : real) : (term841 x) = (term842 x).
Proof. exact (@lem19158 (term809 x) (term302 x) (term807 x)). Qed.
Lemma lem1768525 (x : real) : (term843 x) = (term844 x).
Proof. exact (@lem19158 (term845 x) (term302 x) (term846 x)). Qed.
Lemma lem1768532 (x : real) : (term847 x) = (term848 x).
Proof. exact (@lem19158 (term849 x) (term302 x) (term850 x)). Qed.
Lemma lem1768533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768534 (x : real) : (term851 x) = (term852 x).
Proof. exact (MK_COMB (@lem1768533) (@lem1768532 x)). Qed.
Lemma lem1768535 (x : real) : (term842 x) = (term853 x).
Proof. exact (MK_COMB (@lem1768534 x) (@lem1768525 x)). Qed.
Lemma lem1768536 (x : real) : (term841 x) = (term853 x).
Proof. exact (TRANS (@lem1768518 x) (@lem1768535 x)). Qed.
Lemma lem1768543 (x : real) : (term854 x) = (term855 x).
Proof. exact (@lem19158 (term758 x) (term302 x) (term759 x)). Qed.
Lemma lem1768544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768545 (x : real) : (term856 x) = (term857 x).
Proof. exact (MK_COMB (@lem1768544) (@lem1768543 x)). Qed.
Lemma lem1768546 (x : real) : (term840 x) = (term858 x).
Proof. exact (MK_COMB (@lem1768545 x) (@lem1768536 x)). Qed.
Lemma lem1768547 (x : real) : (term839 x) = (term858 x).
Proof. exact (TRANS (@lem1768517 x) (@lem1768546 x)). Qed.
Lemma lem1768548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768549 (x : real) : (term859 x) = (term860 x).
Proof. exact (MK_COMB (@lem1768548) (@lem1768547 x)). Qed.
Lemma lem1768550 (x : real) : (term818 x) = (term861 x).
Proof. exact (MK_COMB (@lem1768549 x) (@lem1768516 x)). Qed.
Lemma lem1768551 (x : real) : (term817 x) = (term861 x).
Proof. exact (TRANS (@lem1768485 x) (@lem1768550 x)). Qed.
Lemma lem1768552 (x : real) : (term466 x) = (term861 x).
Proof. exact (TRANS (@lem1768484 x) (@lem1768551 x)). Qed.
Lemma lem1768553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768554 (x : real) : (term467 x) = (term862 x).
Proof. exact (MK_COMB (@lem1768553) (@lem1768552 x)). Qed.
Lemma lem1768555 (x : real) : (term486 x) = (term863 x).
Proof. exact (MK_COMB (@lem1768554 x) (@lem1768219 x)). Qed.
Lemma lem1768558 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1768559 (x : real) : (term487 x) = (term864 x).
Proof. exact (MK_COMB (@lem1768558) (@lem1768555 x)). Qed.
Lemma lem1768560 (x : real) : (term864 x) = (term865 x).
Proof. exact (@lem19158 (term861 x) term323 (term762 x)). Qed.
Lemma lem1768561 (x : real) : (term866 x) = (term867 x).
Proof. exact (@lem19158 (term757 x) term323 (term753 x)). Qed.
Lemma lem1768568 (x : real) : (term868 x) = (term869 x).
Proof. exact (@lem19158 (term870 x) term323 (term871 x)). Qed.
Lemma lem1768575 (x : real) : (term872 x) = (term873 x).
Proof. exact (@lem19158 (term874 x) term323 (term875 x)). Qed.
Lemma lem1768576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768577 (x : real) : (term876 x) = (term877 x).
Proof. exact (MK_COMB (@lem1768576) (@lem1768575 x)). Qed.
Lemma lem1768578 (x : real) : (term867 x) = (term878 x).
Proof. exact (MK_COMB (@lem1768577 x) (@lem1768568 x)). Qed.
Lemma lem1768579 (x : real) : (term866 x) = (term878 x).
Proof. exact (TRANS (@lem1768561 x) (@lem1768578 x)). Qed.
Lemma lem1768580 (x : real) : (term879 x) = (term880 x).
Proof. exact (@lem19158 (term858 x) term323 (term838 x)). Qed.
Lemma lem1768581 (x : real) : (term881 x) = (term882 x).
Proof. exact (@lem19158 (term835 x) term323 (term833 x)). Qed.
Lemma lem1768582 (x : real) : (term883 x) = (term884 x).
Proof. exact (@lem19158 (term828 x) term323 (term824 x)). Qed.
Lemma lem1768589 (x : real) : (term885 x) = (term886 x).
Proof. exact (@lem19158 (term887 x) term323 (term888 x)). Qed.
Lemma lem1768596 (x : real) : (term889 x) = (term890 x).
Proof. exact (@lem19158 (term891 x) term323 (term892 x)). Qed.
Lemma lem1768597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768598 (x : real) : (term893 x) = (term894 x).
Proof. exact (MK_COMB (@lem1768597) (@lem1768596 x)). Qed.
Lemma lem1768599 (x : real) : (term884 x) = (term895 x).
Proof. exact (MK_COMB (@lem1768598 x) (@lem1768589 x)). Qed.
Lemma lem1768600 (x : real) : (term883 x) = (term895 x).
Proof. exact (TRANS (@lem1768582 x) (@lem1768599 x)). Qed.
Lemma lem1768607 (x : real) : (term896 x) = (term897 x).
Proof. exact (@lem19158 (term898 x) term323 (term899 x)). Qed.
Lemma lem1768608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768609 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1768608) (@lem1768607 x)). Qed.
Lemma lem1768610 (x : real) : (term882 x) = (term902 x).
Proof. exact (MK_COMB (@lem1768609 x) (@lem1768600 x)). Qed.
Lemma lem1768611 (x : real) : (term881 x) = (term902 x).
Proof. exact (TRANS (@lem1768581 x) (@lem1768610 x)). Qed.
Lemma lem1768612 (x : real) : (term903 x) = (term904 x).
Proof. exact (@lem19158 (term855 x) term323 (term853 x)). Qed.
Lemma lem1768613 (x : real) : (term905 x) = (term906 x).
Proof. exact (@lem19158 (term848 x) term323 (term844 x)). Qed.
Lemma lem1768620 (x : real) : (term907 x) = (term908 x).
Proof. exact (@lem19158 (term909 x) term323 (term910 x)). Qed.
Lemma lem1768627 (x : real) : (term911 x) = (term912 x).
Proof. exact (@lem19158 (term913 x) term323 (term914 x)). Qed.
Lemma lem1768628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768629 (x : real) : (term915 x) = (term916 x).
Proof. exact (MK_COMB (@lem1768628) (@lem1768627 x)). Qed.
Lemma lem1768630 (x : real) : (term906 x) = (term917 x).
Proof. exact (MK_COMB (@lem1768629 x) (@lem1768620 x)). Qed.
Lemma lem1768631 (x : real) : (term905 x) = (term917 x).
Proof. exact (TRANS (@lem1768613 x) (@lem1768630 x)). Qed.
Lemma lem1768638 (x : real) : (term918 x) = (term919 x).
Proof. exact (@lem19158 (term920 x) term323 (term921 x)). Qed.
Lemma lem1768639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768640 (x : real) : (term922 x) = (term923 x).
Proof. exact (MK_COMB (@lem1768639) (@lem1768638 x)). Qed.
Lemma lem1768641 (x : real) : (term904 x) = (term924 x).
Proof. exact (MK_COMB (@lem1768640 x) (@lem1768631 x)). Qed.
Lemma lem1768642 (x : real) : (term903 x) = (term924 x).
Proof. exact (TRANS (@lem1768612 x) (@lem1768641 x)). Qed.
Lemma lem1768643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768644 (x : real) : (term925 x) = (term926 x).
Proof. exact (MK_COMB (@lem1768643) (@lem1768642 x)). Qed.
Lemma lem1768645 (x : real) : (term880 x) = (term927 x).
Proof. exact (MK_COMB (@lem1768644 x) (@lem1768611 x)). Qed.
Lemma lem1768646 (x : real) : (term879 x) = (term927 x).
Proof. exact (TRANS (@lem1768580 x) (@lem1768645 x)). Qed.
Lemma lem1768647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768648 (x : real) : (term928 x) = (term929 x).
Proof. exact (MK_COMB (@lem1768647) (@lem1768646 x)). Qed.
Lemma lem1768649 (x : real) : (term865 x) = (term930 x).
Proof. exact (MK_COMB (@lem1768648 x) (@lem1768579 x)). Qed.
Lemma lem1768650 (x : real) : (term864 x) = (term930 x).
Proof. exact (TRANS (@lem1768560 x) (@lem1768649 x)). Qed.
Lemma lem1768651 (x : real) : (term487 x) = (term930 x).
Proof. exact (TRANS (@lem1768559 x) (@lem1768650 x)). Qed.
Lemma lem1768668 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1768671 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768672 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1768671 x) (@lem1768668)). Qed.
Lemma lem1768679 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1768680 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1768672 x) (@lem1768679 x)). Qed.
Lemma lem1768683 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1768684 (x : real) : (term480 x) = (term735 x).
Proof. exact (MK_COMB (@lem1768683) (@lem1768680 x)). Qed.
Lemma lem1768691 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1768692 (x : real) : (term480 x) = (term736 x).
Proof. exact (TRANS (@lem1768684 x) (@lem1768691 x)). Qed.
Lemma lem1768709 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1768712 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768713 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1768712 x) (@lem1768709)). Qed.
Lemma lem1768720 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1768721 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1768713 x) (@lem1768720 x)). Qed.
Lemma lem1768724 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1768725 (x : real) : (term479 x) = (term744 x).
Proof. exact (MK_COMB (@lem1768724) (@lem1768721 x)). Qed.
Lemma lem1768732 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1768733 (x : real) : (term479 x) = (term745 x).
Proof. exact (TRANS (@lem1768725 x) (@lem1768732 x)). Qed.
Lemma lem1768734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768735 (x : real) : (term481 x) = (term748 x).
Proof. exact (MK_COMB (@lem1768734) (@lem1768733 x)). Qed.
Lemma lem1768736 (x : real) : (term482 x) = (term749 x).
Proof. exact (MK_COMB (@lem1768735 x) (@lem1768692 x)). Qed.
Lemma lem1768739 (x : real) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem1768740 (x : real) : (term483 x) = (term750 x).
Proof. exact (MK_COMB (@lem1768739 x) (@lem1768736 x)). Qed.
Lemma lem1768741 (x : real) : (term750 x) = (term751 x).
Proof. exact (@lem19158 (term745 x) (term421 x) (term736 x)). Qed.
Lemma lem1768748 (x : real) : (term752 x) = (term753 x).
Proof. exact (@lem19158 (term754 x) (term421 x) (term755 x)). Qed.
Lemma lem1768755 (x : real) : (term756 x) = (term757 x).
Proof. exact (@lem19158 (term758 x) (term421 x) (term759 x)). Qed.
Lemma lem1768756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768757 (x : real) : (term760 x) = (term761 x).
Proof. exact (MK_COMB (@lem1768756) (@lem1768755 x)). Qed.
Lemma lem1768758 (x : real) : (term751 x) = (term762 x).
Proof. exact (MK_COMB (@lem1768757 x) (@lem1768748 x)). Qed.
Lemma lem1768759 (x : real) : (term750 x) = (term762 x).
Proof. exact (TRANS (@lem1768741 x) (@lem1768758 x)). Qed.
Lemma lem1768760 (x : real) : (term483 x) = (term762 x).
Proof. exact (TRANS (@lem1768740 x) (@lem1768759 x)). Qed.
Lemma lem1768777 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1768780 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1768781 (x : real) : (term387 x) = (term773 x).
Proof. exact (MK_COMB (@lem1768780 x) (@lem1768777)). Qed.
Lemma lem1768788 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1768789 (x : real) : (term387 x) = (term774 x).
Proof. exact (TRANS (@lem1768781 x) (@lem1768788 x)). Qed.
Lemma lem1768806 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1768809 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768810 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1768809 x) (@lem1768806)). Qed.
Lemma lem1768817 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1768818 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1768810 x) (@lem1768817 x)). Qed.
Lemma lem1768819 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768820 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1768819) (@lem1768818 x)). Qed.
Lemma lem1768821 (x : real) : (term411 x) = (term931 x).
Proof. exact (MK_COMB (@lem1768820 x) (@lem1768789 x)). Qed.
Lemma lem1768824 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1768825 (x : real) : (term413 x) = (term932 x).
Proof. exact (MK_COMB (@lem1768824) (@lem1768821 x)). Qed.
Lemma lem1768826 (x : real) : (term932 x) = (term933 x).
Proof. exact (@lem19158 (term732 x) term398 (term774 x)). Qed.
Lemma lem1768833 (x : real) : (term790 x) = (term791 x).
Proof. exact (@lem19158 (term792 x) term398 (term793 x)). Qed.
Lemma lem1768840 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1768841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768842 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1768841) (@lem1768840 x)). Qed.
Lemma lem1768843 (x : real) : (term933 x) = (term934 x).
Proof. exact (MK_COMB (@lem1768842 x) (@lem1768833 x)). Qed.
Lemma lem1768844 (x : real) : (term932 x) = (term934 x).
Proof. exact (TRANS (@lem1768826 x) (@lem1768843 x)). Qed.
Lemma lem1768845 (x : real) : (term413 x) = (term934 x).
Proof. exact (TRANS (@lem1768825 x) (@lem1768844 x)). Qed.
Lemma lem1768862 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1768865 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1768866 (x : real) : (term387 x) = (term773 x).
Proof. exact (MK_COMB (@lem1768865 x) (@lem1768862)). Qed.
Lemma lem1768873 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1768874 (x : real) : (term387 x) = (term774 x).
Proof. exact (TRANS (@lem1768866 x) (@lem1768873 x)). Qed.
Lemma lem1768891 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1768894 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1768895 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1768894 x) (@lem1768891)). Qed.
Lemma lem1768902 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1768903 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1768895 x) (@lem1768902 x)). Qed.
Lemma lem1768904 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768905 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1768904) (@lem1768903 x)). Qed.
Lemma lem1768906 (x : real) : (term389 x) = (term935 x).
Proof. exact (MK_COMB (@lem1768905 x) (@lem1768874 x)). Qed.
Lemma lem1768909 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1768910 (x : real) : (term390 x) = (term936 x).
Proof. exact (MK_COMB (@lem1768909) (@lem1768906 x)). Qed.
Lemma lem1768911 (x : real) : (term936 x) = (term937 x).
Proof. exact (@lem19158 (term741 x) term313 (term774 x)). Qed.
Lemma lem1768918 (x : real) : (term808 x) = (term809 x).
Proof. exact (@lem19158 (term792 x) term313 (term793 x)). Qed.
Lemma lem1768925 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1768926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768927 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1768926) (@lem1768925 x)). Qed.
Lemma lem1768928 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1768927 x) (@lem1768918 x)). Qed.
Lemma lem1768929 (x : real) : (term936 x) = (term938 x).
Proof. exact (TRANS (@lem1768911 x) (@lem1768928 x)). Qed.
Lemma lem1768930 (x : real) : (term390 x) = (term938 x).
Proof. exact (TRANS (@lem1768910 x) (@lem1768929 x)). Qed.
Lemma lem1768931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768932 (x : real) : (term414 x) = (term939 x).
Proof. exact (MK_COMB (@lem1768931) (@lem1768930 x)). Qed.
Lemma lem1768933 (x : real) : (term415 x) = (term940 x).
Proof. exact (MK_COMB (@lem1768932 x) (@lem1768845 x)). Qed.
Lemma lem1768936 (x : real) : (term416 x) = (term416 x).
Proof. exact (eq_refl (term416 x)). Qed.
Lemma lem1768937 (x : real) : (term417 x) = (term941 x).
Proof. exact (MK_COMB (@lem1768936 x) (@lem1768933 x)). Qed.
Lemma lem1768938 (x : real) : (term941 x) = (term942 x).
Proof. exact (@lem19158 (term938 x) (term302 x) (term934 x)). Qed.
Lemma lem1768939 (x : real) : (term943 x) = (term944 x).
Proof. exact (@lem19158 (term736 x) (term302 x) (term791 x)). Qed.
Lemma lem1768946 (x : real) : (term827 x) = (term828 x).
Proof. exact (@lem19158 (term829 x) (term302 x) (term830 x)). Qed.
Lemma lem1768953 (x : real) : (term834 x) = (term835 x).
Proof. exact (@lem19158 (term754 x) (term302 x) (term755 x)). Qed.
Lemma lem1768954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768955 (x : real) : (term836 x) = (term837 x).
Proof. exact (MK_COMB (@lem1768954) (@lem1768953 x)). Qed.
Lemma lem1768956 (x : real) : (term944 x) = (term945 x).
Proof. exact (MK_COMB (@lem1768955 x) (@lem1768946 x)). Qed.
Lemma lem1768957 (x : real) : (term943 x) = (term945 x).
Proof. exact (TRANS (@lem1768939 x) (@lem1768956 x)). Qed.
Lemma lem1768958 (x : real) : (term946 x) = (term947 x).
Proof. exact (@lem19158 (term745 x) (term302 x) (term809 x)). Qed.
Lemma lem1768965 (x : real) : (term847 x) = (term848 x).
Proof. exact (@lem19158 (term849 x) (term302 x) (term850 x)). Qed.
Lemma lem1768972 (x : real) : (term854 x) = (term855 x).
Proof. exact (@lem19158 (term758 x) (term302 x) (term759 x)). Qed.
Lemma lem1768973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768974 (x : real) : (term856 x) = (term857 x).
Proof. exact (MK_COMB (@lem1768973) (@lem1768972 x)). Qed.
Lemma lem1768975 (x : real) : (term947 x) = (term948 x).
Proof. exact (MK_COMB (@lem1768974 x) (@lem1768965 x)). Qed.
Lemma lem1768976 (x : real) : (term946 x) = (term948 x).
Proof. exact (TRANS (@lem1768958 x) (@lem1768975 x)). Qed.
Lemma lem1768977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768978 (x : real) : (term949 x) = (term950 x).
Proof. exact (MK_COMB (@lem1768977) (@lem1768976 x)). Qed.
Lemma lem1768979 (x : real) : (term942 x) = (term951 x).
Proof. exact (MK_COMB (@lem1768978 x) (@lem1768957 x)). Qed.
Lemma lem1768980 (x : real) : (term941 x) = (term951 x).
Proof. exact (TRANS (@lem1768938 x) (@lem1768979 x)). Qed.
Lemma lem1768981 (x : real) : (term417 x) = (term951 x).
Proof. exact (TRANS (@lem1768937 x) (@lem1768980 x)). Qed.
Lemma lem1768982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1768983 (x : real) : (term441 x) = (term952 x).
Proof. exact (MK_COMB (@lem1768982) (@lem1768981 x)). Qed.
Lemma lem1768984 (x : real) : (term484 x) = (term953 x).
Proof. exact (MK_COMB (@lem1768983 x) (@lem1768760 x)). Qed.
Lemma lem1768987 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1768988 (x : real) : (term485 x) = (term954 x).
Proof. exact (MK_COMB (@lem1768987) (@lem1768984 x)). Qed.
Lemma lem1768989 (x : real) : (term954 x) = (term955 x).
Proof. exact (@lem19158 (term951 x) term295 (term762 x)). Qed.
Lemma lem1768990 (x : real) : (term956 x) = (term957 x).
Proof. exact (@lem19158 (term757 x) term295 (term753 x)). Qed.
Lemma lem1768997 (x : real) : (term958 x) = (term959 x).
Proof. exact (@lem19158 (term870 x) term295 (term871 x)). Qed.
Lemma lem1769004 (x : real) : (term960 x) = (term961 x).
Proof. exact (@lem19158 (term874 x) term295 (term875 x)). Qed.
Lemma lem1769005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769006 (x : real) : (term962 x) = (term963 x).
Proof. exact (MK_COMB (@lem1769005) (@lem1769004 x)). Qed.
Lemma lem1769007 (x : real) : (term957 x) = (term964 x).
Proof. exact (MK_COMB (@lem1769006 x) (@lem1768997 x)). Qed.
Lemma lem1769008 (x : real) : (term956 x) = (term964 x).
Proof. exact (TRANS (@lem1768990 x) (@lem1769007 x)). Qed.
Lemma lem1769009 (x : real) : (term965 x) = (term966 x).
Proof. exact (@lem19158 (term948 x) term295 (term945 x)). Qed.
Lemma lem1769010 (x : real) : (term967 x) = (term968 x).
Proof. exact (@lem19158 (term835 x) term295 (term828 x)). Qed.
Lemma lem1769017 (x : real) : (term969 x) = (term970 x).
Proof. exact (@lem19158 (term891 x) term295 (term892 x)). Qed.
Lemma lem1769024 (x : real) : (term971 x) = (term972 x).
Proof. exact (@lem19158 (term898 x) term295 (term899 x)). Qed.
Lemma lem1769025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769026 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1769025) (@lem1769024 x)). Qed.
Lemma lem1769027 (x : real) : (term968 x) = (term975 x).
Proof. exact (MK_COMB (@lem1769026 x) (@lem1769017 x)). Qed.
Lemma lem1769028 (x : real) : (term967 x) = (term975 x).
Proof. exact (TRANS (@lem1769010 x) (@lem1769027 x)). Qed.
Lemma lem1769029 (x : real) : (term976 x) = (term977 x).
Proof. exact (@lem19158 (term855 x) term295 (term848 x)). Qed.
Lemma lem1769036 (x : real) : (term978 x) = (term979 x).
Proof. exact (@lem19158 (term913 x) term295 (term914 x)). Qed.
Lemma lem1769043 (x : real) : (term980 x) = (term981 x).
Proof. exact (@lem19158 (term920 x) term295 (term921 x)). Qed.
Lemma lem1769044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769045 (x : real) : (term982 x) = (term983 x).
Proof. exact (MK_COMB (@lem1769044) (@lem1769043 x)). Qed.
Lemma lem1769046 (x : real) : (term977 x) = (term984 x).
Proof. exact (MK_COMB (@lem1769045 x) (@lem1769036 x)). Qed.
Lemma lem1769047 (x : real) : (term976 x) = (term984 x).
Proof. exact (TRANS (@lem1769029 x) (@lem1769046 x)). Qed.
Lemma lem1769048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769049 (x : real) : (term985 x) = (term986 x).
Proof. exact (MK_COMB (@lem1769048) (@lem1769047 x)). Qed.
Lemma lem1769050 (x : real) : (term966 x) = (term987 x).
Proof. exact (MK_COMB (@lem1769049 x) (@lem1769028 x)). Qed.
Lemma lem1769051 (x : real) : (term965 x) = (term987 x).
Proof. exact (TRANS (@lem1769009 x) (@lem1769050 x)). Qed.
Lemma lem1769052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769053 (x : real) : (term988 x) = (term989 x).
Proof. exact (MK_COMB (@lem1769052) (@lem1769051 x)). Qed.
Lemma lem1769054 (x : real) : (term955 x) = (term990 x).
Proof. exact (MK_COMB (@lem1769053 x) (@lem1769008 x)). Qed.
Lemma lem1769055 (x : real) : (term954 x) = (term990 x).
Proof. exact (TRANS (@lem1768989 x) (@lem1769054 x)). Qed.
Lemma lem1769056 (x : real) : (term485 x) = (term990 x).
Proof. exact (TRANS (@lem1768988 x) (@lem1769055 x)). Qed.
Lemma lem1769057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769058 (x : real) : (term488 x) = (term991 x).
Proof. exact (MK_COMB (@lem1769057) (@lem1769056 x)). Qed.
Lemma lem1769059 (x : real) : (term489 x) = (term992 x).
Proof. exact (MK_COMB (@lem1769058 x) (@lem1768651 x)). Qed.
Lemma lem1769062 : term490 = term490.
Proof. exact (eq_refl term490). Qed.
Lemma lem1769063 (x : real) : (term492 x) = (term993 x).
Proof. exact (MK_COMB (@lem1769062) (@lem1769059 x)). Qed.
Lemma lem1769064 (x : real) : (term993 x) = (term994 x).
Proof. exact (@lem19158 (term990 x) term478 (term930 x)). Qed.
Lemma lem1769065 (x : real) : (term995 x) = (term996 x).
Proof. exact (@lem19158 (term927 x) term478 (term878 x)). Qed.
Lemma lem1769066 (x : real) : (term997 x) = (term998 x).
Proof. exact (@lem19158 (term873 x) term478 (term869 x)). Qed.
Lemma lem1769073 (x : real) : (term999 x) = (term1000 x).
Proof. exact (@lem19158 (term1001 x) term478 (term1002 x)). Qed.
Lemma lem1769080 (x : real) : (term1003 x) = (term1004 x).
Proof. exact (@lem19158 (term1005 x) term478 (term1006 x)). Qed.
Lemma lem1769081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769082 (x : real) : (term1007 x) = (term1008 x).
Proof. exact (MK_COMB (@lem1769081) (@lem1769080 x)). Qed.
Lemma lem1769083 (x : real) : (term998 x) = (term1009 x).
Proof. exact (MK_COMB (@lem1769082 x) (@lem1769073 x)). Qed.
Lemma lem1769084 (x : real) : (term997 x) = (term1009 x).
Proof. exact (TRANS (@lem1769066 x) (@lem1769083 x)). Qed.
Lemma lem1769085 (x : real) : (term1010 x) = (term1011 x).
Proof. exact (@lem19158 (term924 x) term478 (term902 x)). Qed.
Lemma lem1769086 (x : real) : (term1012 x) = (term1013 x).
Proof. exact (@lem19158 (term897 x) term478 (term895 x)). Qed.
Lemma lem1769087 (x : real) : (term1014 x) = (term1015 x).
Proof. exact (@lem19158 (term890 x) term478 (term886 x)). Qed.
Lemma lem1769094 (x : real) : (term1016 x) = (term1017 x).
Proof. exact (@lem19158 (term1018 x) term478 (term1019 x)). Qed.
Lemma lem1769101 (x : real) : (term1020 x) = (term1021 x).
Proof. exact (@lem19158 (term1022 x) term478 (term1023 x)). Qed.
Lemma lem1769102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769103 (x : real) : (term1024 x) = (term1025 x).
Proof. exact (MK_COMB (@lem1769102) (@lem1769101 x)). Qed.
Lemma lem1769104 (x : real) : (term1015 x) = (term1026 x).
Proof. exact (MK_COMB (@lem1769103 x) (@lem1769094 x)). Qed.
Lemma lem1769105 (x : real) : (term1014 x) = (term1026 x).
Proof. exact (TRANS (@lem1769087 x) (@lem1769104 x)). Qed.
Lemma lem1769112 (x : real) : (term1027 x) = (term1028 x).
Proof. exact (@lem19158 (term1029 x) term478 (term1030 x)). Qed.
Lemma lem1769113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769114 (x : real) : (term1031 x) = (term1032 x).
Proof. exact (MK_COMB (@lem1769113) (@lem1769112 x)). Qed.
Lemma lem1769115 (x : real) : (term1013 x) = (term1033 x).
Proof. exact (MK_COMB (@lem1769114 x) (@lem1769105 x)). Qed.
Lemma lem1769116 (x : real) : (term1012 x) = (term1033 x).
Proof. exact (TRANS (@lem1769086 x) (@lem1769115 x)). Qed.
Lemma lem1769117 (x : real) : (term1034 x) = (term1035 x).
Proof. exact (@lem19158 (term919 x) term478 (term917 x)). Qed.
Lemma lem1769118 (x : real) : (term1036 x) = (term1037 x).
Proof. exact (@lem19158 (term912 x) term478 (term908 x)). Qed.
Lemma lem1769125 (x : real) : (term1038 x) = (term1039 x).
Proof. exact (@lem19158 (term1040 x) term478 (term1041 x)). Qed.
Lemma lem1769132 (x : real) : (term1042 x) = (term1043 x).
Proof. exact (@lem19158 (term1044 x) term478 (term1045 x)). Qed.
Lemma lem1769133 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769134 (x : real) : (term1046 x) = (term1047 x).
Proof. exact (MK_COMB (@lem1769133) (@lem1769132 x)). Qed.
Lemma lem1769135 (x : real) : (term1037 x) = (term1048 x).
Proof. exact (MK_COMB (@lem1769134 x) (@lem1769125 x)). Qed.
Lemma lem1769136 (x : real) : (term1036 x) = (term1048 x).
Proof. exact (TRANS (@lem1769118 x) (@lem1769135 x)). Qed.
Lemma lem1769143 (x : real) : (term1049 x) = (term1050 x).
Proof. exact (@lem19158 (term1051 x) term478 (term1052 x)). Qed.
Lemma lem1769144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769145 (x : real) : (term1053 x) = (term1054 x).
Proof. exact (MK_COMB (@lem1769144) (@lem1769143 x)). Qed.
Lemma lem1769146 (x : real) : (term1035 x) = (term1055 x).
Proof. exact (MK_COMB (@lem1769145 x) (@lem1769136 x)). Qed.
Lemma lem1769147 (x : real) : (term1034 x) = (term1055 x).
Proof. exact (TRANS (@lem1769117 x) (@lem1769146 x)). Qed.
Lemma lem1769148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769149 (x : real) : (term1056 x) = (term1057 x).
Proof. exact (MK_COMB (@lem1769148) (@lem1769147 x)). Qed.
Lemma lem1769150 (x : real) : (term1011 x) = (term1058 x).
Proof. exact (MK_COMB (@lem1769149 x) (@lem1769116 x)). Qed.
Lemma lem1769151 (x : real) : (term1010 x) = (term1058 x).
Proof. exact (TRANS (@lem1769085 x) (@lem1769150 x)). Qed.
Lemma lem1769152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769153 (x : real) : (term1059 x) = (term1060 x).
Proof. exact (MK_COMB (@lem1769152) (@lem1769151 x)). Qed.
Lemma lem1769154 (x : real) : (term996 x) = (term1061 x).
Proof. exact (MK_COMB (@lem1769153 x) (@lem1769084 x)). Qed.
Lemma lem1769155 (x : real) : (term995 x) = (term1061 x).
Proof. exact (TRANS (@lem1769065 x) (@lem1769154 x)). Qed.
Lemma lem1769156 (x : real) : (term1062 x) = (term1063 x).
Proof. exact (@lem19158 (term987 x) term478 (term964 x)). Qed.
Lemma lem1769157 (x : real) : (term1064 x) = (term1065 x).
Proof. exact (@lem19158 (term961 x) term478 (term959 x)). Qed.
Lemma lem1769164 (x : real) : (term1066 x) = (term1067 x).
Proof. exact (@lem19158 (term1068 x) term478 (term1069 x)). Qed.
Lemma lem1769171 (x : real) : (term1070 x) = (term1071 x).
Proof. exact (@lem19158 (term1072 x) term478 (term1073 x)). Qed.
Lemma lem1769172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769173 (x : real) : (term1074 x) = (term1075 x).
Proof. exact (MK_COMB (@lem1769172) (@lem1769171 x)). Qed.
Lemma lem1769174 (x : real) : (term1065 x) = (term1076 x).
Proof. exact (MK_COMB (@lem1769173 x) (@lem1769164 x)). Qed.
Lemma lem1769175 (x : real) : (term1064 x) = (term1076 x).
Proof. exact (TRANS (@lem1769157 x) (@lem1769174 x)). Qed.
Lemma lem1769176 (x : real) : (term1077 x) = (term1078 x).
Proof. exact (@lem19158 (term984 x) term478 (term975 x)). Qed.
Lemma lem1769177 (x : real) : (term1079 x) = (term1080 x).
Proof. exact (@lem19158 (term972 x) term478 (term970 x)). Qed.
Lemma lem1769184 (x : real) : (term1081 x) = (term1082 x).
Proof. exact (@lem19158 (term1083 x) term478 (term1084 x)). Qed.
Lemma lem1769191 (x : real) : (term1085 x) = (term1086 x).
Proof. exact (@lem19158 (term1087 x) term478 (term1088 x)). Qed.
Lemma lem1769192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769193 (x : real) : (term1089 x) = (term1090 x).
Proof. exact (MK_COMB (@lem1769192) (@lem1769191 x)). Qed.
Lemma lem1769194 (x : real) : (term1080 x) = (term1091 x).
Proof. exact (MK_COMB (@lem1769193 x) (@lem1769184 x)). Qed.
Lemma lem1769195 (x : real) : (term1079 x) = (term1091 x).
Proof. exact (TRANS (@lem1769177 x) (@lem1769194 x)). Qed.
Lemma lem1769196 (x : real) : (term1092 x) = (term1093 x).
Proof. exact (@lem19158 (term981 x) term478 (term979 x)). Qed.
Lemma lem1769203 (x : real) : (term1094 x) = (term1095 x).
Proof. exact (@lem19158 (term1096 x) term478 (term1097 x)). Qed.
Lemma lem1769210 (x : real) : (term1098 x) = (term1099 x).
Proof. exact (@lem19158 (term1100 x) term478 (term1101 x)). Qed.
Lemma lem1769211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769212 (x : real) : (term1102 x) = (term1103 x).
Proof. exact (MK_COMB (@lem1769211) (@lem1769210 x)). Qed.
Lemma lem1769213 (x : real) : (term1093 x) = (term1104 x).
Proof. exact (MK_COMB (@lem1769212 x) (@lem1769203 x)). Qed.
Lemma lem1769214 (x : real) : (term1092 x) = (term1104 x).
Proof. exact (TRANS (@lem1769196 x) (@lem1769213 x)). Qed.
Lemma lem1769215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769216 (x : real) : (term1105 x) = (term1106 x).
Proof. exact (MK_COMB (@lem1769215) (@lem1769214 x)). Qed.
Lemma lem1769217 (x : real) : (term1078 x) = (term1107 x).
Proof. exact (MK_COMB (@lem1769216 x) (@lem1769195 x)). Qed.
Lemma lem1769218 (x : real) : (term1077 x) = (term1107 x).
Proof. exact (TRANS (@lem1769176 x) (@lem1769217 x)). Qed.
Lemma lem1769219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769220 (x : real) : (term1108 x) = (term1109 x).
Proof. exact (MK_COMB (@lem1769219) (@lem1769218 x)). Qed.
Lemma lem1769221 (x : real) : (term1063 x) = (term1110 x).
Proof. exact (MK_COMB (@lem1769220 x) (@lem1769175 x)). Qed.
Lemma lem1769222 (x : real) : (term1062 x) = (term1110 x).
Proof. exact (TRANS (@lem1769156 x) (@lem1769221 x)). Qed.
Lemma lem1769223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769224 (x : real) : (term1111 x) = (term1112 x).
Proof. exact (MK_COMB (@lem1769223) (@lem1769222 x)). Qed.
Lemma lem1769225 (x : real) : (term994 x) = (term1113 x).
Proof. exact (MK_COMB (@lem1769224 x) (@lem1769155 x)). Qed.
Lemma lem1769226 (x : real) : (term993 x) = (term1113 x).
Proof. exact (TRANS (@lem1769064 x) (@lem1769225 x)). Qed.
Lemma lem1769227 (x : real) : (term492 x) = (term1113 x).
Proof. exact (TRANS (@lem1769063 x) (@lem1769226 x)). Qed.
Lemma lem1769244 (x : real) : (term432 x) = (term1114 x).
Proof. exact (@lem19158 term295 (term362 x) term313). Qed.
Lemma lem1769261 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1769264 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769265 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1769264 x) (@lem1769261)). Qed.
Lemma lem1769272 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1769273 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1769265 x) (@lem1769272 x)). Qed.
Lemma lem1769274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769275 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1769274) (@lem1769273 x)). Qed.
Lemma lem1769276 (x : real) : (term435 x) = (term1115 x).
Proof. exact (MK_COMB (@lem1769275 x) (@lem1769244 x)). Qed.
Lemma lem1769279 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1769280 (x : real) : (term436 x) = (term1116 x).
Proof. exact (MK_COMB (@lem1769279) (@lem1769276 x)). Qed.
Lemma lem1769281 (x : real) : (term1116 x) = (term1117 x).
Proof. exact (@lem19158 (term732 x) term398 (term1114 x)). Qed.
Lemma lem1769288 (x : real) : (term1118 x) = (term1119 x).
Proof. exact (@lem19158 (term1120 x) term398 (term1121 x)). Qed.
Lemma lem1769295 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1769296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769297 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1769296) (@lem1769295 x)). Qed.
Lemma lem1769298 (x : real) : (term1117 x) = (term1122 x).
Proof. exact (MK_COMB (@lem1769297 x) (@lem1769288 x)). Qed.
Lemma lem1769299 (x : real) : (term1116 x) = (term1122 x).
Proof. exact (TRANS (@lem1769281 x) (@lem1769298 x)). Qed.
Lemma lem1769300 (x : real) : (term436 x) = (term1122 x).
Proof. exact (TRANS (@lem1769280 x) (@lem1769299 x)). Qed.
Lemma lem1769317 (x : real) : (term432 x) = (term1114 x).
Proof. exact (@lem19158 term295 (term362 x) term313). Qed.
Lemma lem1769334 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1769337 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769338 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1769337 x) (@lem1769334)). Qed.
Lemma lem1769345 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1769346 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1769338 x) (@lem1769345 x)). Qed.
Lemma lem1769347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769348 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1769347) (@lem1769346 x)). Qed.
Lemma lem1769349 (x : real) : (term433 x) = (term1123 x).
Proof. exact (MK_COMB (@lem1769348 x) (@lem1769317 x)). Qed.
Lemma lem1769352 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1769353 (x : real) : (term434 x) = (term1124 x).
Proof. exact (MK_COMB (@lem1769352) (@lem1769349 x)). Qed.
Lemma lem1769354 (x : real) : (term1124 x) = (term1125 x).
Proof. exact (@lem19158 (term741 x) term313 (term1114 x)). Qed.
Lemma lem1769361 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (@lem19158 (term1120 x) term313 (term1121 x)). Qed.
Lemma lem1769368 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1769369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769370 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1769369) (@lem1769368 x)). Qed.
Lemma lem1769371 (x : real) : (term1125 x) = (term1128 x).
Proof. exact (MK_COMB (@lem1769370 x) (@lem1769361 x)). Qed.
Lemma lem1769372 (x : real) : (term1124 x) = (term1128 x).
Proof. exact (TRANS (@lem1769354 x) (@lem1769371 x)). Qed.
Lemma lem1769373 (x : real) : (term434 x) = (term1128 x).
Proof. exact (TRANS (@lem1769353 x) (@lem1769372 x)). Qed.
Lemma lem1769374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769375 (x : real) : (term437 x) = (term1129 x).
Proof. exact (MK_COMB (@lem1769374) (@lem1769373 x)). Qed.
Lemma lem1769376 (x : real) : (term438 x) = (term1130 x).
Proof. exact (MK_COMB (@lem1769375 x) (@lem1769300 x)). Qed.
Lemma lem1769379 (x : real) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem1769380 (x : real) : (term440 x) = (term1131 x).
Proof. exact (MK_COMB (@lem1769379 x) (@lem1769376 x)). Qed.
Lemma lem1769381 (x : real) : (term1131 x) = (term1132 x).
Proof. exact (@lem19158 (term1128 x) (term421 x) (term1122 x)). Qed.
Lemma lem1769382 (x : real) : (term1133 x) = (term1134 x).
Proof. exact (@lem19158 (term736 x) (term421 x) (term1119 x)). Qed.
Lemma lem1769389 (x : real) : (term1135 x) = (term1136 x).
Proof. exact (@lem19158 (term1137 x) (term421 x) (term1138 x)). Qed.
Lemma lem1769396 (x : real) : (term752 x) = (term753 x).
Proof. exact (@lem19158 (term754 x) (term421 x) (term755 x)). Qed.
Lemma lem1769397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769398 (x : real) : (term1139 x) = (term1140 x).
Proof. exact (MK_COMB (@lem1769397) (@lem1769396 x)). Qed.
Lemma lem1769399 (x : real) : (term1134 x) = (term1141 x).
Proof. exact (MK_COMB (@lem1769398 x) (@lem1769389 x)). Qed.
Lemma lem1769400 (x : real) : (term1133 x) = (term1141 x).
Proof. exact (TRANS (@lem1769382 x) (@lem1769399 x)). Qed.
Lemma lem1769401 (x : real) : (term1142 x) = (term1143 x).
Proof. exact (@lem19158 (term745 x) (term421 x) (term1127 x)). Qed.
Lemma lem1769408 (x : real) : (term1144 x) = (term1145 x).
Proof. exact (@lem19158 (term1146 x) (term421 x) (term1147 x)). Qed.
Lemma lem1769415 (x : real) : (term756 x) = (term757 x).
Proof. exact (@lem19158 (term758 x) (term421 x) (term759 x)). Qed.
Lemma lem1769416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769417 (x : real) : (term760 x) = (term761 x).
Proof. exact (MK_COMB (@lem1769416) (@lem1769415 x)). Qed.
Lemma lem1769418 (x : real) : (term1143 x) = (term1148 x).
Proof. exact (MK_COMB (@lem1769417 x) (@lem1769408 x)). Qed.
Lemma lem1769419 (x : real) : (term1142 x) = (term1148 x).
Proof. exact (TRANS (@lem1769401 x) (@lem1769418 x)). Qed.
Lemma lem1769420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769421 (x : real) : (term1149 x) = (term1150 x).
Proof. exact (MK_COMB (@lem1769420) (@lem1769419 x)). Qed.
Lemma lem1769422 (x : real) : (term1132 x) = (term1151 x).
Proof. exact (MK_COMB (@lem1769421 x) (@lem1769400 x)). Qed.
Lemma lem1769423 (x : real) : (term1131 x) = (term1151 x).
Proof. exact (TRANS (@lem1769381 x) (@lem1769422 x)). Qed.
Lemma lem1769424 (x : real) : (term440 x) = (term1151 x).
Proof. exact (TRANS (@lem1769380 x) (@lem1769423 x)). Qed.
Lemma lem1769441 : term456 = term763.
Proof. exact (@lem19158 term295 term398 term313). Qed.
Lemma lem1769458 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1769459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769460 : term457 = term765.
Proof. exact (MK_COMB (@lem1769459) (@lem1769458)). Qed.
Lemma lem1769461 : term458 = term766.
Proof. exact (MK_COMB (@lem1769460) (@lem1769441)). Qed.
Lemma lem1769464 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1769465 (x : real) : (term459 x) = (term767 x).
Proof. exact (MK_COMB (@lem1769464 x) (@lem1769461)). Qed.
Lemma lem1769466 (x : real) : (term767 x) = (term768 x).
Proof. exact (@lem19158 term764 (term362 x) term763). Qed.
Lemma lem1769473 (x : real) : (term769 x) = (term770 x).
Proof. exact (@lem19158 term771 (term362 x) term772). Qed.
Lemma lem1769480 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1769481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769482 (x : real) : (term777 x) = (term778 x).
Proof. exact (MK_COMB (@lem1769481) (@lem1769480 x)). Qed.
Lemma lem1769483 (x : real) : (term768 x) = (term779 x).
Proof. exact (MK_COMB (@lem1769482 x) (@lem1769473 x)). Qed.
Lemma lem1769484 (x : real) : (term767 x) = (term779 x).
Proof. exact (TRANS (@lem1769466 x) (@lem1769483 x)). Qed.
Lemma lem1769485 (x : real) : (term459 x) = (term779 x).
Proof. exact (TRANS (@lem1769465 x) (@lem1769484 x)). Qed.
Lemma lem1769502 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1769505 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769506 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1769505 x) (@lem1769502)). Qed.
Lemma lem1769513 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1769514 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1769506 x) (@lem1769513 x)). Qed.
Lemma lem1769515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769516 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1769515) (@lem1769514 x)). Qed.
Lemma lem1769517 (x : real) : (term462 x) = (term781 x).
Proof. exact (MK_COMB (@lem1769516 x) (@lem1769485 x)). Qed.
Lemma lem1769520 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1769521 (x : real) : (term463 x) = (term782 x).
Proof. exact (MK_COMB (@lem1769520) (@lem1769517 x)). Qed.
Lemma lem1769522 (x : real) : (term782 x) = (term783 x).
Proof. exact (@lem19158 (term732 x) term398 (term779 x)). Qed.
Lemma lem1769523 (x : real) : (term784 x) = (term785 x).
Proof. exact (@lem19158 (term774 x) term398 (term770 x)). Qed.
Lemma lem1769530 (x : real) : (term786 x) = (term787 x).
Proof. exact (@lem19158 (term788 x) term398 (term789 x)). Qed.
Lemma lem1769537 (x : real) : (term790 x) = (term791 x).
Proof. exact (@lem19158 (term792 x) term398 (term793 x)). Qed.
Lemma lem1769538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769539 (x : real) : (term794 x) = (term795 x).
Proof. exact (MK_COMB (@lem1769538) (@lem1769537 x)). Qed.
Lemma lem1769540 (x : real) : (term785 x) = (term796 x).
Proof. exact (MK_COMB (@lem1769539 x) (@lem1769530 x)). Qed.
Lemma lem1769541 (x : real) : (term784 x) = (term796 x).
Proof. exact (TRANS (@lem1769523 x) (@lem1769540 x)). Qed.
Lemma lem1769548 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1769549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769550 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1769549) (@lem1769548 x)). Qed.
Lemma lem1769551 (x : real) : (term783 x) = (term799 x).
Proof. exact (MK_COMB (@lem1769550 x) (@lem1769541 x)). Qed.
Lemma lem1769552 (x : real) : (term782 x) = (term799 x).
Proof. exact (TRANS (@lem1769522 x) (@lem1769551 x)). Qed.
Lemma lem1769553 (x : real) : (term463 x) = (term799 x).
Proof. exact (TRANS (@lem1769521 x) (@lem1769552 x)). Qed.
Lemma lem1769570 : term456 = term763.
Proof. exact (@lem19158 term295 term398 term313). Qed.
Lemma lem1769587 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1769588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769589 : term457 = term765.
Proof. exact (MK_COMB (@lem1769588) (@lem1769587)). Qed.
Lemma lem1769590 : term458 = term766.
Proof. exact (MK_COMB (@lem1769589) (@lem1769570)). Qed.
Lemma lem1769593 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1769594 (x : real) : (term459 x) = (term767 x).
Proof. exact (MK_COMB (@lem1769593 x) (@lem1769590)). Qed.
Lemma lem1769595 (x : real) : (term767 x) = (term768 x).
Proof. exact (@lem19158 term764 (term362 x) term763). Qed.
Lemma lem1769602 (x : real) : (term769 x) = (term770 x).
Proof. exact (@lem19158 term771 (term362 x) term772). Qed.
Lemma lem1769609 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1769610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769611 (x : real) : (term777 x) = (term778 x).
Proof. exact (MK_COMB (@lem1769610) (@lem1769609 x)). Qed.
Lemma lem1769612 (x : real) : (term768 x) = (term779 x).
Proof. exact (MK_COMB (@lem1769611 x) (@lem1769602 x)). Qed.
Lemma lem1769613 (x : real) : (term767 x) = (term779 x).
Proof. exact (TRANS (@lem1769595 x) (@lem1769612 x)). Qed.
Lemma lem1769614 (x : real) : (term459 x) = (term779 x).
Proof. exact (TRANS (@lem1769594 x) (@lem1769613 x)). Qed.
Lemma lem1769631 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1769634 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769635 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1769634 x) (@lem1769631)). Qed.
Lemma lem1769642 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1769643 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1769635 x) (@lem1769642 x)). Qed.
Lemma lem1769644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769645 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1769644) (@lem1769643 x)). Qed.
Lemma lem1769646 (x : real) : (term460 x) = (term801 x).
Proof. exact (MK_COMB (@lem1769645 x) (@lem1769614 x)). Qed.
Lemma lem1769649 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1769650 (x : real) : (term461 x) = (term802 x).
Proof. exact (MK_COMB (@lem1769649) (@lem1769646 x)). Qed.
Lemma lem1769651 (x : real) : (term802 x) = (term803 x).
Proof. exact (@lem19158 (term741 x) term313 (term779 x)). Qed.
Lemma lem1769652 (x : real) : (term804 x) = (term805 x).
Proof. exact (@lem19158 (term774 x) term313 (term770 x)). Qed.
Lemma lem1769659 (x : real) : (term806 x) = (term807 x).
Proof. exact (@lem19158 (term788 x) term313 (term789 x)). Qed.
Lemma lem1769666 (x : real) : (term808 x) = (term809 x).
Proof. exact (@lem19158 (term792 x) term313 (term793 x)). Qed.
Lemma lem1769667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769668 (x : real) : (term810 x) = (term811 x).
Proof. exact (MK_COMB (@lem1769667) (@lem1769666 x)). Qed.
Lemma lem1769669 (x : real) : (term805 x) = (term812 x).
Proof. exact (MK_COMB (@lem1769668 x) (@lem1769659 x)). Qed.
Lemma lem1769670 (x : real) : (term804 x) = (term812 x).
Proof. exact (TRANS (@lem1769652 x) (@lem1769669 x)). Qed.
Lemma lem1769677 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1769678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769679 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1769678) (@lem1769677 x)). Qed.
Lemma lem1769680 (x : real) : (term803 x) = (term814 x).
Proof. exact (MK_COMB (@lem1769679 x) (@lem1769670 x)). Qed.
Lemma lem1769681 (x : real) : (term802 x) = (term814 x).
Proof. exact (TRANS (@lem1769651 x) (@lem1769680 x)). Qed.
Lemma lem1769682 (x : real) : (term461 x) = (term814 x).
Proof. exact (TRANS (@lem1769650 x) (@lem1769681 x)). Qed.
Lemma lem1769683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769684 (x : real) : (term464 x) = (term815 x).
Proof. exact (MK_COMB (@lem1769683) (@lem1769682 x)). Qed.
Lemma lem1769685 (x : real) : (term465 x) = (term816 x).
Proof. exact (MK_COMB (@lem1769684 x) (@lem1769553 x)). Qed.
Lemma lem1769688 (x : real) : (term416 x) = (term416 x).
Proof. exact (eq_refl (term416 x)). Qed.
Lemma lem1769689 (x : real) : (term466 x) = (term817 x).
Proof. exact (MK_COMB (@lem1769688 x) (@lem1769685 x)). Qed.
Lemma lem1769690 (x : real) : (term817 x) = (term818 x).
Proof. exact (@lem19158 (term814 x) (term302 x) (term799 x)). Qed.
Lemma lem1769691 (x : real) : (term819 x) = (term820 x).
Proof. exact (@lem19158 (term736 x) (term302 x) (term796 x)). Qed.
Lemma lem1769692 (x : real) : (term821 x) = (term822 x).
Proof. exact (@lem19158 (term791 x) (term302 x) (term787 x)). Qed.
Lemma lem1769699 (x : real) : (term823 x) = (term824 x).
Proof. exact (@lem19158 (term825 x) (term302 x) (term826 x)). Qed.
Lemma lem1769706 (x : real) : (term827 x) = (term828 x).
Proof. exact (@lem19158 (term829 x) (term302 x) (term830 x)). Qed.
Lemma lem1769707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769708 (x : real) : (term831 x) = (term832 x).
Proof. exact (MK_COMB (@lem1769707) (@lem1769706 x)). Qed.
Lemma lem1769709 (x : real) : (term822 x) = (term833 x).
Proof. exact (MK_COMB (@lem1769708 x) (@lem1769699 x)). Qed.
Lemma lem1769710 (x : real) : (term821 x) = (term833 x).
Proof. exact (TRANS (@lem1769692 x) (@lem1769709 x)). Qed.
Lemma lem1769717 (x : real) : (term834 x) = (term835 x).
Proof. exact (@lem19158 (term754 x) (term302 x) (term755 x)). Qed.
Lemma lem1769718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769719 (x : real) : (term836 x) = (term837 x).
Proof. exact (MK_COMB (@lem1769718) (@lem1769717 x)). Qed.
Lemma lem1769720 (x : real) : (term820 x) = (term838 x).
Proof. exact (MK_COMB (@lem1769719 x) (@lem1769710 x)). Qed.
Lemma lem1769721 (x : real) : (term819 x) = (term838 x).
Proof. exact (TRANS (@lem1769691 x) (@lem1769720 x)). Qed.
Lemma lem1769722 (x : real) : (term839 x) = (term840 x).
Proof. exact (@lem19158 (term745 x) (term302 x) (term812 x)). Qed.
Lemma lem1769723 (x : real) : (term841 x) = (term842 x).
Proof. exact (@lem19158 (term809 x) (term302 x) (term807 x)). Qed.
Lemma lem1769730 (x : real) : (term843 x) = (term844 x).
Proof. exact (@lem19158 (term845 x) (term302 x) (term846 x)). Qed.
Lemma lem1769737 (x : real) : (term847 x) = (term848 x).
Proof. exact (@lem19158 (term849 x) (term302 x) (term850 x)). Qed.
Lemma lem1769738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769739 (x : real) : (term851 x) = (term852 x).
Proof. exact (MK_COMB (@lem1769738) (@lem1769737 x)). Qed.
Lemma lem1769740 (x : real) : (term842 x) = (term853 x).
Proof. exact (MK_COMB (@lem1769739 x) (@lem1769730 x)). Qed.
Lemma lem1769741 (x : real) : (term841 x) = (term853 x).
Proof. exact (TRANS (@lem1769723 x) (@lem1769740 x)). Qed.
Lemma lem1769748 (x : real) : (term854 x) = (term855 x).
Proof. exact (@lem19158 (term758 x) (term302 x) (term759 x)). Qed.
Lemma lem1769749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769750 (x : real) : (term856 x) = (term857 x).
Proof. exact (MK_COMB (@lem1769749) (@lem1769748 x)). Qed.
Lemma lem1769751 (x : real) : (term840 x) = (term858 x).
Proof. exact (MK_COMB (@lem1769750 x) (@lem1769741 x)). Qed.
Lemma lem1769752 (x : real) : (term839 x) = (term858 x).
Proof. exact (TRANS (@lem1769722 x) (@lem1769751 x)). Qed.
Lemma lem1769753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769754 (x : real) : (term859 x) = (term860 x).
Proof. exact (MK_COMB (@lem1769753) (@lem1769752 x)). Qed.
Lemma lem1769755 (x : real) : (term818 x) = (term861 x).
Proof. exact (MK_COMB (@lem1769754 x) (@lem1769721 x)). Qed.
Lemma lem1769756 (x : real) : (term817 x) = (term861 x).
Proof. exact (TRANS (@lem1769690 x) (@lem1769755 x)). Qed.
Lemma lem1769757 (x : real) : (term466 x) = (term861 x).
Proof. exact (TRANS (@lem1769689 x) (@lem1769756 x)). Qed.
Lemma lem1769758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769759 (x : real) : (term467 x) = (term862 x).
Proof. exact (MK_COMB (@lem1769758) (@lem1769757 x)). Qed.
Lemma lem1769760 (x : real) : (term468 x) = (term1152 x).
Proof. exact (MK_COMB (@lem1769759 x) (@lem1769424 x)). Qed.
Lemma lem1769763 : term355 = term355.
Proof. exact (eq_refl term355). Qed.
Lemma lem1769764 (x : real) : (term469 x) = (term1153 x).
Proof. exact (MK_COMB (@lem1769763) (@lem1769760 x)). Qed.
Lemma lem1769765 (x : real) : (term1153 x) = (term1154 x).
Proof. exact (@lem19158 (term861 x) term323 (term1151 x)). Qed.
Lemma lem1769766 (x : real) : (term1155 x) = (term1156 x).
Proof. exact (@lem19158 (term1148 x) term323 (term1141 x)). Qed.
Lemma lem1769767 (x : real) : (term1157 x) = (term1158 x).
Proof. exact (@lem19158 (term753 x) term323 (term1136 x)). Qed.
Lemma lem1769774 (x : real) : (term1159 x) = (term1160 x).
Proof. exact (@lem19158 (term1161 x) term323 (term1162 x)). Qed.
Lemma lem1769781 (x : real) : (term868 x) = (term869 x).
Proof. exact (@lem19158 (term870 x) term323 (term871 x)). Qed.
Lemma lem1769782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769783 (x : real) : (term1163 x) = (term1164 x).
Proof. exact (MK_COMB (@lem1769782) (@lem1769781 x)). Qed.
Lemma lem1769784 (x : real) : (term1158 x) = (term1165 x).
Proof. exact (MK_COMB (@lem1769783 x) (@lem1769774 x)). Qed.
Lemma lem1769785 (x : real) : (term1157 x) = (term1165 x).
Proof. exact (TRANS (@lem1769767 x) (@lem1769784 x)). Qed.
Lemma lem1769786 (x : real) : (term1166 x) = (term1167 x).
Proof. exact (@lem19158 (term757 x) term323 (term1145 x)). Qed.
Lemma lem1769793 (x : real) : (term1168 x) = (term1169 x).
Proof. exact (@lem19158 (term1170 x) term323 (term1171 x)). Qed.
Lemma lem1769800 (x : real) : (term872 x) = (term873 x).
Proof. exact (@lem19158 (term874 x) term323 (term875 x)). Qed.
Lemma lem1769801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769802 (x : real) : (term876 x) = (term877 x).
Proof. exact (MK_COMB (@lem1769801) (@lem1769800 x)). Qed.
Lemma lem1769803 (x : real) : (term1167 x) = (term1172 x).
Proof. exact (MK_COMB (@lem1769802 x) (@lem1769793 x)). Qed.
Lemma lem1769804 (x : real) : (term1166 x) = (term1172 x).
Proof. exact (TRANS (@lem1769786 x) (@lem1769803 x)). Qed.
Lemma lem1769805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769806 (x : real) : (term1173 x) = (term1174 x).
Proof. exact (MK_COMB (@lem1769805) (@lem1769804 x)). Qed.
Lemma lem1769807 (x : real) : (term1156 x) = (term1175 x).
Proof. exact (MK_COMB (@lem1769806 x) (@lem1769785 x)). Qed.
Lemma lem1769808 (x : real) : (term1155 x) = (term1175 x).
Proof. exact (TRANS (@lem1769766 x) (@lem1769807 x)). Qed.
Lemma lem1769809 (x : real) : (term879 x) = (term880 x).
Proof. exact (@lem19158 (term858 x) term323 (term838 x)). Qed.
Lemma lem1769810 (x : real) : (term881 x) = (term882 x).
Proof. exact (@lem19158 (term835 x) term323 (term833 x)). Qed.
Lemma lem1769811 (x : real) : (term883 x) = (term884 x).
Proof. exact (@lem19158 (term828 x) term323 (term824 x)). Qed.
Lemma lem1769818 (x : real) : (term885 x) = (term886 x).
Proof. exact (@lem19158 (term887 x) term323 (term888 x)). Qed.
Lemma lem1769825 (x : real) : (term889 x) = (term890 x).
Proof. exact (@lem19158 (term891 x) term323 (term892 x)). Qed.
Lemma lem1769826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769827 (x : real) : (term893 x) = (term894 x).
Proof. exact (MK_COMB (@lem1769826) (@lem1769825 x)). Qed.
Lemma lem1769828 (x : real) : (term884 x) = (term895 x).
Proof. exact (MK_COMB (@lem1769827 x) (@lem1769818 x)). Qed.
Lemma lem1769829 (x : real) : (term883 x) = (term895 x).
Proof. exact (TRANS (@lem1769811 x) (@lem1769828 x)). Qed.
Lemma lem1769836 (x : real) : (term896 x) = (term897 x).
Proof. exact (@lem19158 (term898 x) term323 (term899 x)). Qed.
Lemma lem1769837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769838 (x : real) : (term900 x) = (term901 x).
Proof. exact (MK_COMB (@lem1769837) (@lem1769836 x)). Qed.
Lemma lem1769839 (x : real) : (term882 x) = (term902 x).
Proof. exact (MK_COMB (@lem1769838 x) (@lem1769829 x)). Qed.
Lemma lem1769840 (x : real) : (term881 x) = (term902 x).
Proof. exact (TRANS (@lem1769810 x) (@lem1769839 x)). Qed.
Lemma lem1769841 (x : real) : (term903 x) = (term904 x).
Proof. exact (@lem19158 (term855 x) term323 (term853 x)). Qed.
Lemma lem1769842 (x : real) : (term905 x) = (term906 x).
Proof. exact (@lem19158 (term848 x) term323 (term844 x)). Qed.
Lemma lem1769849 (x : real) : (term907 x) = (term908 x).
Proof. exact (@lem19158 (term909 x) term323 (term910 x)). Qed.
Lemma lem1769856 (x : real) : (term911 x) = (term912 x).
Proof. exact (@lem19158 (term913 x) term323 (term914 x)). Qed.
Lemma lem1769857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769858 (x : real) : (term915 x) = (term916 x).
Proof. exact (MK_COMB (@lem1769857) (@lem1769856 x)). Qed.
Lemma lem1769859 (x : real) : (term906 x) = (term917 x).
Proof. exact (MK_COMB (@lem1769858 x) (@lem1769849 x)). Qed.
Lemma lem1769860 (x : real) : (term905 x) = (term917 x).
Proof. exact (TRANS (@lem1769842 x) (@lem1769859 x)). Qed.
Lemma lem1769867 (x : real) : (term918 x) = (term919 x).
Proof. exact (@lem19158 (term920 x) term323 (term921 x)). Qed.
Lemma lem1769868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769869 (x : real) : (term922 x) = (term923 x).
Proof. exact (MK_COMB (@lem1769868) (@lem1769867 x)). Qed.
Lemma lem1769870 (x : real) : (term904 x) = (term924 x).
Proof. exact (MK_COMB (@lem1769869 x) (@lem1769860 x)). Qed.
Lemma lem1769871 (x : real) : (term903 x) = (term924 x).
Proof. exact (TRANS (@lem1769841 x) (@lem1769870 x)). Qed.
Lemma lem1769872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769873 (x : real) : (term925 x) = (term926 x).
Proof. exact (MK_COMB (@lem1769872) (@lem1769871 x)). Qed.
Lemma lem1769874 (x : real) : (term880 x) = (term927 x).
Proof. exact (MK_COMB (@lem1769873 x) (@lem1769840 x)). Qed.
Lemma lem1769875 (x : real) : (term879 x) = (term927 x).
Proof. exact (TRANS (@lem1769809 x) (@lem1769874 x)). Qed.
Lemma lem1769876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769877 (x : real) : (term928 x) = (term929 x).
Proof. exact (MK_COMB (@lem1769876) (@lem1769875 x)). Qed.
Lemma lem1769878 (x : real) : (term1154 x) = (term1176 x).
Proof. exact (MK_COMB (@lem1769877 x) (@lem1769808 x)). Qed.
Lemma lem1769879 (x : real) : (term1153 x) = (term1176 x).
Proof. exact (TRANS (@lem1769765 x) (@lem1769878 x)). Qed.
Lemma lem1769880 (x : real) : (term469 x) = (term1176 x).
Proof. exact (TRANS (@lem1769764 x) (@lem1769879 x)). Qed.
Lemma lem1769897 (x : real) : (term432 x) = (term1114 x).
Proof. exact (@lem19158 term295 (term362 x) term313). Qed.
Lemma lem1769914 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1769917 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769918 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1769917 x) (@lem1769914)). Qed.
Lemma lem1769925 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1769926 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1769918 x) (@lem1769925 x)). Qed.
Lemma lem1769927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769928 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1769927) (@lem1769926 x)). Qed.
Lemma lem1769929 (x : real) : (term435 x) = (term1115 x).
Proof. exact (MK_COMB (@lem1769928 x) (@lem1769897 x)). Qed.
Lemma lem1769932 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1769933 (x : real) : (term436 x) = (term1116 x).
Proof. exact (MK_COMB (@lem1769932) (@lem1769929 x)). Qed.
Lemma lem1769934 (x : real) : (term1116 x) = (term1117 x).
Proof. exact (@lem19158 (term732 x) term398 (term1114 x)). Qed.
Lemma lem1769941 (x : real) : (term1118 x) = (term1119 x).
Proof. exact (@lem19158 (term1120 x) term398 (term1121 x)). Qed.
Lemma lem1769948 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1769949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1769950 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1769949) (@lem1769948 x)). Qed.
Lemma lem1769951 (x : real) : (term1117 x) = (term1122 x).
Proof. exact (MK_COMB (@lem1769950 x) (@lem1769941 x)). Qed.
Lemma lem1769952 (x : real) : (term1116 x) = (term1122 x).
Proof. exact (TRANS (@lem1769934 x) (@lem1769951 x)). Qed.
Lemma lem1769953 (x : real) : (term436 x) = (term1122 x).
Proof. exact (TRANS (@lem1769933 x) (@lem1769952 x)). Qed.
Lemma lem1769970 (x : real) : (term432 x) = (term1114 x).
Proof. exact (@lem19158 term295 (term362 x) term313). Qed.
Lemma lem1769987 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1769990 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1769991 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1769990 x) (@lem1769987)). Qed.
Lemma lem1769998 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1769999 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1769991 x) (@lem1769998 x)). Qed.
Lemma lem1770000 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770001 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1770000) (@lem1769999 x)). Qed.
Lemma lem1770002 (x : real) : (term433 x) = (term1123 x).
Proof. exact (MK_COMB (@lem1770001 x) (@lem1769970 x)). Qed.
Lemma lem1770005 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1770006 (x : real) : (term434 x) = (term1124 x).
Proof. exact (MK_COMB (@lem1770005) (@lem1770002 x)). Qed.
Lemma lem1770007 (x : real) : (term1124 x) = (term1125 x).
Proof. exact (@lem19158 (term741 x) term313 (term1114 x)). Qed.
Lemma lem1770014 (x : real) : (term1126 x) = (term1127 x).
Proof. exact (@lem19158 (term1120 x) term313 (term1121 x)). Qed.
Lemma lem1770021 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1770022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770023 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1770022) (@lem1770021 x)). Qed.
Lemma lem1770024 (x : real) : (term1125 x) = (term1128 x).
Proof. exact (MK_COMB (@lem1770023 x) (@lem1770014 x)). Qed.
Lemma lem1770025 (x : real) : (term1124 x) = (term1128 x).
Proof. exact (TRANS (@lem1770007 x) (@lem1770024 x)). Qed.
Lemma lem1770026 (x : real) : (term434 x) = (term1128 x).
Proof. exact (TRANS (@lem1770006 x) (@lem1770025 x)). Qed.
Lemma lem1770027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770028 (x : real) : (term437 x) = (term1129 x).
Proof. exact (MK_COMB (@lem1770027) (@lem1770026 x)). Qed.
Lemma lem1770029 (x : real) : (term438 x) = (term1130 x).
Proof. exact (MK_COMB (@lem1770028 x) (@lem1769953 x)). Qed.
Lemma lem1770032 (x : real) : (term439 x) = (term439 x).
Proof. exact (eq_refl (term439 x)). Qed.
Lemma lem1770033 (x : real) : (term440 x) = (term1131 x).
Proof. exact (MK_COMB (@lem1770032 x) (@lem1770029 x)). Qed.
Lemma lem1770034 (x : real) : (term1131 x) = (term1132 x).
Proof. exact (@lem19158 (term1128 x) (term421 x) (term1122 x)). Qed.
Lemma lem1770035 (x : real) : (term1133 x) = (term1134 x).
Proof. exact (@lem19158 (term736 x) (term421 x) (term1119 x)). Qed.
Lemma lem1770042 (x : real) : (term1135 x) = (term1136 x).
Proof. exact (@lem19158 (term1137 x) (term421 x) (term1138 x)). Qed.
Lemma lem1770049 (x : real) : (term752 x) = (term753 x).
Proof. exact (@lem19158 (term754 x) (term421 x) (term755 x)). Qed.
Lemma lem1770050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770051 (x : real) : (term1139 x) = (term1140 x).
Proof. exact (MK_COMB (@lem1770050) (@lem1770049 x)). Qed.
Lemma lem1770052 (x : real) : (term1134 x) = (term1141 x).
Proof. exact (MK_COMB (@lem1770051 x) (@lem1770042 x)). Qed.
Lemma lem1770053 (x : real) : (term1133 x) = (term1141 x).
Proof. exact (TRANS (@lem1770035 x) (@lem1770052 x)). Qed.
Lemma lem1770054 (x : real) : (term1142 x) = (term1143 x).
Proof. exact (@lem19158 (term745 x) (term421 x) (term1127 x)). Qed.
Lemma lem1770061 (x : real) : (term1144 x) = (term1145 x).
Proof. exact (@lem19158 (term1146 x) (term421 x) (term1147 x)). Qed.
Lemma lem1770068 (x : real) : (term756 x) = (term757 x).
Proof. exact (@lem19158 (term758 x) (term421 x) (term759 x)). Qed.
Lemma lem1770069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770070 (x : real) : (term760 x) = (term761 x).
Proof. exact (MK_COMB (@lem1770069) (@lem1770068 x)). Qed.
Lemma lem1770071 (x : real) : (term1143 x) = (term1148 x).
Proof. exact (MK_COMB (@lem1770070 x) (@lem1770061 x)). Qed.
Lemma lem1770072 (x : real) : (term1142 x) = (term1148 x).
Proof. exact (TRANS (@lem1770054 x) (@lem1770071 x)). Qed.
Lemma lem1770073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770074 (x : real) : (term1149 x) = (term1150 x).
Proof. exact (MK_COMB (@lem1770073) (@lem1770072 x)). Qed.
Lemma lem1770075 (x : real) : (term1132 x) = (term1151 x).
Proof. exact (MK_COMB (@lem1770074 x) (@lem1770053 x)). Qed.
Lemma lem1770076 (x : real) : (term1131 x) = (term1151 x).
Proof. exact (TRANS (@lem1770034 x) (@lem1770075 x)). Qed.
Lemma lem1770077 (x : real) : (term440 x) = (term1151 x).
Proof. exact (TRANS (@lem1770033 x) (@lem1770076 x)). Qed.
Lemma lem1770094 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1770097 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1770098 (x : real) : (term387 x) = (term773 x).
Proof. exact (MK_COMB (@lem1770097 x) (@lem1770094)). Qed.
Lemma lem1770105 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1770106 (x : real) : (term387 x) = (term774 x).
Proof. exact (TRANS (@lem1770098 x) (@lem1770105 x)). Qed.
Lemma lem1770123 : term408 = term730.
Proof. exact (@lem19158 term313 term323 term295). Qed.
Lemma lem1770126 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1770127 (x : real) : (term409 x) = (term731 x).
Proof. exact (MK_COMB (@lem1770126 x) (@lem1770123)). Qed.
Lemma lem1770134 (x : real) : (term731 x) = (term732 x).
Proof. exact (@lem19158 term733 (term319 x) term734). Qed.
Lemma lem1770135 (x : real) : (term409 x) = (term732 x).
Proof. exact (TRANS (@lem1770127 x) (@lem1770134 x)). Qed.
Lemma lem1770136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770137 (x : real) : (term410 x) = (term780 x).
Proof. exact (MK_COMB (@lem1770136) (@lem1770135 x)). Qed.
Lemma lem1770138 (x : real) : (term411 x) = (term931 x).
Proof. exact (MK_COMB (@lem1770137 x) (@lem1770106 x)). Qed.
Lemma lem1770141 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem1770142 (x : real) : (term413 x) = (term932 x).
Proof. exact (MK_COMB (@lem1770141) (@lem1770138 x)). Qed.
Lemma lem1770143 (x : real) : (term932 x) = (term933 x).
Proof. exact (@lem19158 (term732 x) term398 (term774 x)). Qed.
Lemma lem1770150 (x : real) : (term790 x) = (term791 x).
Proof. exact (@lem19158 (term792 x) term398 (term793 x)). Qed.
Lemma lem1770157 (x : real) : (term735 x) = (term736 x).
Proof. exact (@lem19158 (term737 x) term398 (term738 x)). Qed.
Lemma lem1770158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770159 (x : real) : (term797 x) = (term798 x).
Proof. exact (MK_COMB (@lem1770158) (@lem1770157 x)). Qed.
Lemma lem1770160 (x : real) : (term933 x) = (term934 x).
Proof. exact (MK_COMB (@lem1770159 x) (@lem1770150 x)). Qed.
Lemma lem1770161 (x : real) : (term932 x) = (term934 x).
Proof. exact (TRANS (@lem1770143 x) (@lem1770160 x)). Qed.
Lemma lem1770162 (x : real) : (term413 x) = (term934 x).
Proof. exact (TRANS (@lem1770142 x) (@lem1770161 x)). Qed.
Lemma lem1770179 : term385 = term764.
Proof. exact (@lem19158 term347 term313 term351). Qed.
Lemma lem1770182 (x : real) : (term386 x) = (term386 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem1770183 (x : real) : (term387 x) = (term773 x).
Proof. exact (MK_COMB (@lem1770182 x) (@lem1770179)). Qed.
Lemma lem1770190 (x : real) : (term773 x) = (term774 x).
Proof. exact (@lem19158 term775 (term362 x) term776). Qed.
Lemma lem1770191 (x : real) : (term387 x) = (term774 x).
Proof. exact (TRANS (@lem1770183 x) (@lem1770190 x)). Qed.
Lemma lem1770208 : term356 = term739.
Proof. exact (@lem19158 term351 term323 term347). Qed.
Lemma lem1770211 (x : real) : (term357 x) = (term357 x).
Proof. exact (eq_refl (term357 x)). Qed.
Lemma lem1770212 (x : real) : (term358 x) = (term740 x).
Proof. exact (MK_COMB (@lem1770211 x) (@lem1770208)). Qed.
Lemma lem1770219 (x : real) : (term740 x) = (term741 x).
Proof. exact (@lem19158 term742 (term319 x) term743). Qed.
Lemma lem1770220 (x : real) : (term358 x) = (term741 x).
Proof. exact (TRANS (@lem1770212 x) (@lem1770219 x)). Qed.
Lemma lem1770221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770222 (x : real) : (term388 x) = (term800 x).
Proof. exact (MK_COMB (@lem1770221) (@lem1770220 x)). Qed.
Lemma lem1770223 (x : real) : (term389 x) = (term935 x).
Proof. exact (MK_COMB (@lem1770222 x) (@lem1770191 x)). Qed.
Lemma lem1770226 : term384 = term384.
Proof. exact (eq_refl term384). Qed.
Lemma lem1770227 (x : real) : (term390 x) = (term936 x).
Proof. exact (MK_COMB (@lem1770226) (@lem1770223 x)). Qed.
Lemma lem1770228 (x : real) : (term936 x) = (term937 x).
Proof. exact (@lem19158 (term741 x) term313 (term774 x)). Qed.
Lemma lem1770235 (x : real) : (term808 x) = (term809 x).
Proof. exact (@lem19158 (term792 x) term313 (term793 x)). Qed.
Lemma lem1770242 (x : real) : (term744 x) = (term745 x).
Proof. exact (@lem19158 (term746 x) term313 (term747 x)). Qed.
Lemma lem1770243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770244 (x : real) : (term813 x) = (term748 x).
Proof. exact (MK_COMB (@lem1770243) (@lem1770242 x)). Qed.
Lemma lem1770245 (x : real) : (term937 x) = (term938 x).
Proof. exact (MK_COMB (@lem1770244 x) (@lem1770235 x)). Qed.
Lemma lem1770246 (x : real) : (term936 x) = (term938 x).
Proof. exact (TRANS (@lem1770228 x) (@lem1770245 x)). Qed.
Lemma lem1770247 (x : real) : (term390 x) = (term938 x).
Proof. exact (TRANS (@lem1770227 x) (@lem1770246 x)). Qed.
Lemma lem1770248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770249 (x : real) : (term414 x) = (term939 x).
Proof. exact (MK_COMB (@lem1770248) (@lem1770247 x)). Qed.
Lemma lem1770250 (x : real) : (term415 x) = (term940 x).
Proof. exact (MK_COMB (@lem1770249 x) (@lem1770162 x)). Qed.
Lemma lem1770253 (x : real) : (term416 x) = (term416 x).
Proof. exact (eq_refl (term416 x)). Qed.
Lemma lem1770254 (x : real) : (term417 x) = (term941 x).
Proof. exact (MK_COMB (@lem1770253 x) (@lem1770250 x)). Qed.
Lemma lem1770255 (x : real) : (term941 x) = (term942 x).
Proof. exact (@lem19158 (term938 x) (term302 x) (term934 x)). Qed.
Lemma lem1770256 (x : real) : (term943 x) = (term944 x).
Proof. exact (@lem19158 (term736 x) (term302 x) (term791 x)). Qed.
Lemma lem1770263 (x : real) : (term827 x) = (term828 x).
Proof. exact (@lem19158 (term829 x) (term302 x) (term830 x)). Qed.
Lemma lem1770270 (x : real) : (term834 x) = (term835 x).
Proof. exact (@lem19158 (term754 x) (term302 x) (term755 x)). Qed.
Lemma lem1770271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770272 (x : real) : (term836 x) = (term837 x).
Proof. exact (MK_COMB (@lem1770271) (@lem1770270 x)). Qed.
Lemma lem1770273 (x : real) : (term944 x) = (term945 x).
Proof. exact (MK_COMB (@lem1770272 x) (@lem1770263 x)). Qed.
Lemma lem1770274 (x : real) : (term943 x) = (term945 x).
Proof. exact (TRANS (@lem1770256 x) (@lem1770273 x)). Qed.
Lemma lem1770275 (x : real) : (term946 x) = (term947 x).
Proof. exact (@lem19158 (term745 x) (term302 x) (term809 x)). Qed.
Lemma lem1770282 (x : real) : (term847 x) = (term848 x).
Proof. exact (@lem19158 (term849 x) (term302 x) (term850 x)). Qed.
Lemma lem1770289 (x : real) : (term854 x) = (term855 x).
Proof. exact (@lem19158 (term758 x) (term302 x) (term759 x)). Qed.
Lemma lem1770290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770291 (x : real) : (term856 x) = (term857 x).
Proof. exact (MK_COMB (@lem1770290) (@lem1770289 x)). Qed.
Lemma lem1770292 (x : real) : (term947 x) = (term948 x).
Proof. exact (MK_COMB (@lem1770291 x) (@lem1770282 x)). Qed.
Lemma lem1770293 (x : real) : (term946 x) = (term948 x).
Proof. exact (TRANS (@lem1770275 x) (@lem1770292 x)). Qed.
Lemma lem1770294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770295 (x : real) : (term949 x) = (term950 x).
Proof. exact (MK_COMB (@lem1770294) (@lem1770293 x)). Qed.
Lemma lem1770296 (x : real) : (term942 x) = (term951 x).
Proof. exact (MK_COMB (@lem1770295 x) (@lem1770274 x)). Qed.
Lemma lem1770297 (x : real) : (term941 x) = (term951 x).
Proof. exact (TRANS (@lem1770255 x) (@lem1770296 x)). Qed.
Lemma lem1770298 (x : real) : (term417 x) = (term951 x).
Proof. exact (TRANS (@lem1770254 x) (@lem1770297 x)). Qed.
Lemma lem1770299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770300 (x : real) : (term441 x) = (term952 x).
Proof. exact (MK_COMB (@lem1770299) (@lem1770298 x)). Qed.
Lemma lem1770301 (x : real) : (term442 x) = (term1177 x).
Proof. exact (MK_COMB (@lem1770300 x) (@lem1770077 x)). Qed.
Lemma lem1770304 : term443 = term443.
Proof. exact (eq_refl term443). Qed.
Lemma lem1770305 (x : real) : (term444 x) = (term1178 x).
Proof. exact (MK_COMB (@lem1770304) (@lem1770301 x)). Qed.
Lemma lem1770306 (x : real) : (term1178 x) = (term1179 x).
Proof. exact (@lem19158 (term951 x) term295 (term1151 x)). Qed.
Lemma lem1770307 (x : real) : (term1180 x) = (term1181 x).
Proof. exact (@lem19158 (term1148 x) term295 (term1141 x)). Qed.
Lemma lem1770308 (x : real) : (term1182 x) = (term1183 x).
Proof. exact (@lem19158 (term753 x) term295 (term1136 x)). Qed.
Lemma lem1770315 (x : real) : (term1184 x) = (term1185 x).
Proof. exact (@lem19158 (term1161 x) term295 (term1162 x)). Qed.
Lemma lem1770322 (x : real) : (term958 x) = (term959 x).
Proof. exact (@lem19158 (term870 x) term295 (term871 x)). Qed.
Lemma lem1770323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770324 (x : real) : (term1186 x) = (term1187 x).
Proof. exact (MK_COMB (@lem1770323) (@lem1770322 x)). Qed.
Lemma lem1770325 (x : real) : (term1183 x) = (term1188 x).
Proof. exact (MK_COMB (@lem1770324 x) (@lem1770315 x)). Qed.
Lemma lem1770326 (x : real) : (term1182 x) = (term1188 x).
Proof. exact (TRANS (@lem1770308 x) (@lem1770325 x)). Qed.
Lemma lem1770327 (x : real) : (term1189 x) = (term1190 x).
Proof. exact (@lem19158 (term757 x) term295 (term1145 x)). Qed.
Lemma lem1770334 (x : real) : (term1191 x) = (term1192 x).
Proof. exact (@lem19158 (term1170 x) term295 (term1171 x)). Qed.
Lemma lem1770341 (x : real) : (term960 x) = (term961 x).
Proof. exact (@lem19158 (term874 x) term295 (term875 x)). Qed.
Lemma lem1770342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770343 (x : real) : (term962 x) = (term963 x).
Proof. exact (MK_COMB (@lem1770342) (@lem1770341 x)). Qed.
Lemma lem1770344 (x : real) : (term1190 x) = (term1193 x).
Proof. exact (MK_COMB (@lem1770343 x) (@lem1770334 x)). Qed.
Lemma lem1770345 (x : real) : (term1189 x) = (term1193 x).
Proof. exact (TRANS (@lem1770327 x) (@lem1770344 x)). Qed.
Lemma lem1770346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770347 (x : real) : (term1194 x) = (term1195 x).
Proof. exact (MK_COMB (@lem1770346) (@lem1770345 x)). Qed.
Lemma lem1770348 (x : real) : (term1181 x) = (term1196 x).
Proof. exact (MK_COMB (@lem1770347 x) (@lem1770326 x)). Qed.
Lemma lem1770349 (x : real) : (term1180 x) = (term1196 x).
Proof. exact (TRANS (@lem1770307 x) (@lem1770348 x)). Qed.
Lemma lem1770350 (x : real) : (term965 x) = (term966 x).
Proof. exact (@lem19158 (term948 x) term295 (term945 x)). Qed.
Lemma lem1770351 (x : real) : (term967 x) = (term968 x).
Proof. exact (@lem19158 (term835 x) term295 (term828 x)). Qed.
Lemma lem1770358 (x : real) : (term969 x) = (term970 x).
Proof. exact (@lem19158 (term891 x) term295 (term892 x)). Qed.
Lemma lem1770365 (x : real) : (term971 x) = (term972 x).
Proof. exact (@lem19158 (term898 x) term295 (term899 x)). Qed.
Lemma lem1770366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770367 (x : real) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem1770366) (@lem1770365 x)). Qed.
Lemma lem1770368 (x : real) : (term968 x) = (term975 x).
Proof. exact (MK_COMB (@lem1770367 x) (@lem1770358 x)). Qed.
Lemma lem1770369 (x : real) : (term967 x) = (term975 x).
Proof. exact (TRANS (@lem1770351 x) (@lem1770368 x)). Qed.
Lemma lem1770370 (x : real) : (term976 x) = (term977 x).
Proof. exact (@lem19158 (term855 x) term295 (term848 x)). Qed.
Lemma lem1770377 (x : real) : (term978 x) = (term979 x).
Proof. exact (@lem19158 (term913 x) term295 (term914 x)). Qed.
Lemma lem1770384 (x : real) : (term980 x) = (term981 x).
Proof. exact (@lem19158 (term920 x) term295 (term921 x)). Qed.
Lemma lem1770385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770386 (x : real) : (term982 x) = (term983 x).
Proof. exact (MK_COMB (@lem1770385) (@lem1770384 x)). Qed.
Lemma lem1770387 (x : real) : (term977 x) = (term984 x).
Proof. exact (MK_COMB (@lem1770386 x) (@lem1770377 x)). Qed.
Lemma lem1770388 (x : real) : (term976 x) = (term984 x).
Proof. exact (TRANS (@lem1770370 x) (@lem1770387 x)). Qed.
Lemma lem1770389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770390 (x : real) : (term985 x) = (term986 x).
Proof. exact (MK_COMB (@lem1770389) (@lem1770388 x)). Qed.
Lemma lem1770391 (x : real) : (term966 x) = (term987 x).
Proof. exact (MK_COMB (@lem1770390 x) (@lem1770369 x)). Qed.
Lemma lem1770392 (x : real) : (term965 x) = (term987 x).
Proof. exact (TRANS (@lem1770350 x) (@lem1770391 x)). Qed.
Lemma lem1770393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770394 (x : real) : (term988 x) = (term989 x).
Proof. exact (MK_COMB (@lem1770393) (@lem1770392 x)). Qed.
Lemma lem1770395 (x : real) : (term1179 x) = (term1197 x).
Proof. exact (MK_COMB (@lem1770394 x) (@lem1770349 x)). Qed.
Lemma lem1770396 (x : real) : (term1178 x) = (term1197 x).
Proof. exact (TRANS (@lem1770306 x) (@lem1770395 x)). Qed.
Lemma lem1770397 (x : real) : (term444 x) = (term1197 x).
Proof. exact (TRANS (@lem1770305 x) (@lem1770396 x)). Qed.
Lemma lem1770398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770399 (x : real) : (term470 x) = (term1198 x).
Proof. exact (MK_COMB (@lem1770398) (@lem1770397 x)). Qed.
Lemma lem1770400 (x : real) : (term471 x) = (term1199 x).
Proof. exact (MK_COMB (@lem1770399 x) (@lem1769880 x)). Qed.
Lemma lem1770403 : term472 = term472.
Proof. exact (eq_refl term472). Qed.
Lemma lem1770404 (x : real) : (term474 x) = (term1200 x).
Proof. exact (MK_COMB (@lem1770403) (@lem1770400 x)). Qed.
Lemma lem1770405 (x : real) : (term1200 x) = (term1201 x).
Proof. exact (@lem19158 (term1197 x) term282 (term1176 x)). Qed.
Lemma lem1770406 (x : real) : (term1202 x) = (term1203 x).
Proof. exact (@lem19158 (term927 x) term282 (term1175 x)). Qed.
Lemma lem1770407 (x : real) : (term1204 x) = (term1205 x).
Proof. exact (@lem19158 (term1172 x) term282 (term1165 x)). Qed.
Lemma lem1770408 (x : real) : (term1206 x) = (term1207 x).
Proof. exact (@lem19158 (term869 x) term282 (term1160 x)). Qed.
Lemma lem1770415 (x : real) : (term1208 x) = (term1209 x).
Proof. exact (@lem19158 (term1210 x) term282 (term1211 x)). Qed.
Lemma lem1770422 (x : real) : (term1212 x) = (term1213 x).
Proof. exact (@lem19158 (term1001 x) term282 (term1002 x)). Qed.
Lemma lem1770423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770424 (x : real) : (term1214 x) = (term1215 x).
Proof. exact (MK_COMB (@lem1770423) (@lem1770422 x)). Qed.
Lemma lem1770425 (x : real) : (term1207 x) = (term1216 x).
Proof. exact (MK_COMB (@lem1770424 x) (@lem1770415 x)). Qed.
Lemma lem1770426 (x : real) : (term1206 x) = (term1216 x).
Proof. exact (TRANS (@lem1770408 x) (@lem1770425 x)). Qed.
Lemma lem1770427 (x : real) : (term1217 x) = (term1218 x).
Proof. exact (@lem19158 (term873 x) term282 (term1169 x)). Qed.
Lemma lem1770434 (x : real) : (term1219 x) = (term1220 x).
Proof. exact (@lem19158 (term1221 x) term282 (term1222 x)). Qed.
Lemma lem1770441 (x : real) : (term1223 x) = (term1224 x).
Proof. exact (@lem19158 (term1005 x) term282 (term1006 x)). Qed.
Lemma lem1770442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770443 (x : real) : (term1225 x) = (term1226 x).
Proof. exact (MK_COMB (@lem1770442) (@lem1770441 x)). Qed.
Lemma lem1770444 (x : real) : (term1218 x) = (term1227 x).
Proof. exact (MK_COMB (@lem1770443 x) (@lem1770434 x)). Qed.
Lemma lem1770445 (x : real) : (term1217 x) = (term1227 x).
Proof. exact (TRANS (@lem1770427 x) (@lem1770444 x)). Qed.
Lemma lem1770446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770447 (x : real) : (term1228 x) = (term1229 x).
Proof. exact (MK_COMB (@lem1770446) (@lem1770445 x)). Qed.
Lemma lem1770448 (x : real) : (term1205 x) = (term1230 x).
Proof. exact (MK_COMB (@lem1770447 x) (@lem1770426 x)). Qed.
Lemma lem1770449 (x : real) : (term1204 x) = (term1230 x).
Proof. exact (TRANS (@lem1770407 x) (@lem1770448 x)). Qed.
Lemma lem1770450 (x : real) : (term1231 x) = (term1232 x).
Proof. exact (@lem19158 (term924 x) term282 (term902 x)). Qed.
Lemma lem1770451 (x : real) : (term1233 x) = (term1234 x).
Proof. exact (@lem19158 (term897 x) term282 (term895 x)). Qed.
Lemma lem1770452 (x : real) : (term1235 x) = (term1236 x).
Proof. exact (@lem19158 (term890 x) term282 (term886 x)). Qed.
Lemma lem1770459 (x : real) : (term1237 x) = (term1238 x).
Proof. exact (@lem19158 (term1018 x) term282 (term1019 x)). Qed.
Lemma lem1770466 (x : real) : (term1239 x) = (term1240 x).
Proof. exact (@lem19158 (term1022 x) term282 (term1023 x)). Qed.
Lemma lem1770467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770468 (x : real) : (term1241 x) = (term1242 x).
Proof. exact (MK_COMB (@lem1770467) (@lem1770466 x)). Qed.
Lemma lem1770469 (x : real) : (term1236 x) = (term1243 x).
Proof. exact (MK_COMB (@lem1770468 x) (@lem1770459 x)). Qed.
Lemma lem1770470 (x : real) : (term1235 x) = (term1243 x).
Proof. exact (TRANS (@lem1770452 x) (@lem1770469 x)). Qed.
Lemma lem1770477 (x : real) : (term1244 x) = (term1245 x).
Proof. exact (@lem19158 (term1029 x) term282 (term1030 x)). Qed.
Lemma lem1770478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770479 (x : real) : (term1246 x) = (term1247 x).
Proof. exact (MK_COMB (@lem1770478) (@lem1770477 x)). Qed.
Lemma lem1770480 (x : real) : (term1234 x) = (term1248 x).
Proof. exact (MK_COMB (@lem1770479 x) (@lem1770470 x)). Qed.
Lemma lem1770481 (x : real) : (term1233 x) = (term1248 x).
Proof. exact (TRANS (@lem1770451 x) (@lem1770480 x)). Qed.
Lemma lem1770482 (x : real) : (term1249 x) = (term1250 x).
Proof. exact (@lem19158 (term919 x) term282 (term917 x)). Qed.
Lemma lem1770483 (x : real) : (term1251 x) = (term1252 x).
Proof. exact (@lem19158 (term912 x) term282 (term908 x)). Qed.
Lemma lem1770490 (x : real) : (term1253 x) = (term1254 x).
Proof. exact (@lem19158 (term1040 x) term282 (term1041 x)). Qed.
Lemma lem1770497 (x : real) : (term1255 x) = (term1256 x).
Proof. exact (@lem19158 (term1044 x) term282 (term1045 x)). Qed.
Lemma lem1770498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770499 (x : real) : (term1257 x) = (term1258 x).
Proof. exact (MK_COMB (@lem1770498) (@lem1770497 x)). Qed.
Lemma lem1770500 (x : real) : (term1252 x) = (term1259 x).
Proof. exact (MK_COMB (@lem1770499 x) (@lem1770490 x)). Qed.
Lemma lem1770501 (x : real) : (term1251 x) = (term1259 x).
Proof. exact (TRANS (@lem1770483 x) (@lem1770500 x)). Qed.
Lemma lem1770508 (x : real) : (term1260 x) = (term1261 x).
Proof. exact (@lem19158 (term1051 x) term282 (term1052 x)). Qed.
Lemma lem1770509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770510 (x : real) : (term1262 x) = (term1263 x).
Proof. exact (MK_COMB (@lem1770509) (@lem1770508 x)). Qed.
Lemma lem1770511 (x : real) : (term1250 x) = (term1264 x).
Proof. exact (MK_COMB (@lem1770510 x) (@lem1770501 x)). Qed.
Lemma lem1770512 (x : real) : (term1249 x) = (term1264 x).
Proof. exact (TRANS (@lem1770482 x) (@lem1770511 x)). Qed.
Lemma lem1770513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770514 (x : real) : (term1265 x) = (term1266 x).
Proof. exact (MK_COMB (@lem1770513) (@lem1770512 x)). Qed.
Lemma lem1770515 (x : real) : (term1232 x) = (term1267 x).
Proof. exact (MK_COMB (@lem1770514 x) (@lem1770481 x)). Qed.
Lemma lem1770516 (x : real) : (term1231 x) = (term1267 x).
Proof. exact (TRANS (@lem1770450 x) (@lem1770515 x)). Qed.
Lemma lem1770517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770518 (x : real) : (term1268 x) = (term1269 x).
Proof. exact (MK_COMB (@lem1770517) (@lem1770516 x)). Qed.
Lemma lem1770519 (x : real) : (term1203 x) = (term1270 x).
Proof. exact (MK_COMB (@lem1770518 x) (@lem1770449 x)). Qed.
Lemma lem1770520 (x : real) : (term1202 x) = (term1270 x).
Proof. exact (TRANS (@lem1770406 x) (@lem1770519 x)). Qed.
Lemma lem1770521 (x : real) : (term1271 x) = (term1272 x).
Proof. exact (@lem19158 (term987 x) term282 (term1196 x)). Qed.
Lemma lem1770522 (x : real) : (term1273 x) = (term1274 x).
Proof. exact (@lem19158 (term1193 x) term282 (term1188 x)). Qed.
Lemma lem1770523 (x : real) : (term1275 x) = (term1276 x).
Proof. exact (@lem19158 (term959 x) term282 (term1185 x)). Qed.
Lemma lem1770530 (x : real) : (term1277 x) = (term1278 x).
Proof. exact (@lem19158 (term1279 x) term282 (term1280 x)). Qed.
Lemma lem1770537 (x : real) : (term1281 x) = (term1282 x).
Proof. exact (@lem19158 (term1068 x) term282 (term1069 x)). Qed.
Lemma lem1770538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770539 (x : real) : (term1283 x) = (term1284 x).
Proof. exact (MK_COMB (@lem1770538) (@lem1770537 x)). Qed.
Lemma lem1770540 (x : real) : (term1276 x) = (term1285 x).
Proof. exact (MK_COMB (@lem1770539 x) (@lem1770530 x)). Qed.
Lemma lem1770541 (x : real) : (term1275 x) = (term1285 x).
Proof. exact (TRANS (@lem1770523 x) (@lem1770540 x)). Qed.
Lemma lem1770542 (x : real) : (term1286 x) = (term1287 x).
Proof. exact (@lem19158 (term961 x) term282 (term1192 x)). Qed.
Lemma lem1770549 (x : real) : (term1288 x) = (term1289 x).
Proof. exact (@lem19158 (term1290 x) term282 (term1291 x)). Qed.
Lemma lem1770556 (x : real) : (term1292 x) = (term1293 x).
Proof. exact (@lem19158 (term1072 x) term282 (term1073 x)). Qed.
Lemma lem1770557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770558 (x : real) : (term1294 x) = (term1295 x).
Proof. exact (MK_COMB (@lem1770557) (@lem1770556 x)). Qed.
Lemma lem1770559 (x : real) : (term1287 x) = (term1296 x).
Proof. exact (MK_COMB (@lem1770558 x) (@lem1770549 x)). Qed.
Lemma lem1770560 (x : real) : (term1286 x) = (term1296 x).
Proof. exact (TRANS (@lem1770542 x) (@lem1770559 x)). Qed.
Lemma lem1770561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770562 (x : real) : (term1297 x) = (term1298 x).
Proof. exact (MK_COMB (@lem1770561) (@lem1770560 x)). Qed.
Lemma lem1770563 (x : real) : (term1274 x) = (term1299 x).
Proof. exact (MK_COMB (@lem1770562 x) (@lem1770541 x)). Qed.
Lemma lem1770564 (x : real) : (term1273 x) = (term1299 x).
Proof. exact (TRANS (@lem1770522 x) (@lem1770563 x)). Qed.
Lemma lem1770565 (x : real) : (term1300 x) = (term1301 x).
Proof. exact (@lem19158 (term984 x) term282 (term975 x)). Qed.
Lemma lem1770566 (x : real) : (term1302 x) = (term1303 x).
Proof. exact (@lem19158 (term972 x) term282 (term970 x)). Qed.
Lemma lem1770573 (x : real) : (term1304 x) = (term1305 x).
Proof. exact (@lem19158 (term1083 x) term282 (term1084 x)). Qed.
Lemma lem1770580 (x : real) : (term1306 x) = (term1307 x).
Proof. exact (@lem19158 (term1087 x) term282 (term1088 x)). Qed.
Lemma lem1770581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770582 (x : real) : (term1308 x) = (term1309 x).
Proof. exact (MK_COMB (@lem1770581) (@lem1770580 x)). Qed.
Lemma lem1770583 (x : real) : (term1303 x) = (term1310 x).
Proof. exact (MK_COMB (@lem1770582 x) (@lem1770573 x)). Qed.
Lemma lem1770584 (x : real) : (term1302 x) = (term1310 x).
Proof. exact (TRANS (@lem1770566 x) (@lem1770583 x)). Qed.
Lemma lem1770585 (x : real) : (term1311 x) = (term1312 x).
Proof. exact (@lem19158 (term981 x) term282 (term979 x)). Qed.
Lemma lem1770592 (x : real) : (term1313 x) = (term1314 x).
Proof. exact (@lem19158 (term1096 x) term282 (term1097 x)). Qed.
Lemma lem1770599 (x : real) : (term1315 x) = (term1316 x).
Proof. exact (@lem19158 (term1100 x) term282 (term1101 x)). Qed.
Lemma lem1770600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770601 (x : real) : (term1317 x) = (term1318 x).
Proof. exact (MK_COMB (@lem1770600) (@lem1770599 x)). Qed.
Lemma lem1770602 (x : real) : (term1312 x) = (term1319 x).
Proof. exact (MK_COMB (@lem1770601 x) (@lem1770592 x)). Qed.
Lemma lem1770603 (x : real) : (term1311 x) = (term1319 x).
Proof. exact (TRANS (@lem1770585 x) (@lem1770602 x)). Qed.
Lemma lem1770604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770605 (x : real) : (term1320 x) = (term1321 x).
Proof. exact (MK_COMB (@lem1770604) (@lem1770603 x)). Qed.
Lemma lem1770606 (x : real) : (term1301 x) = (term1322 x).
Proof. exact (MK_COMB (@lem1770605 x) (@lem1770584 x)). Qed.
Lemma lem1770607 (x : real) : (term1300 x) = (term1322 x).
Proof. exact (TRANS (@lem1770565 x) (@lem1770606 x)). Qed.
Lemma lem1770608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770609 (x : real) : (term1323 x) = (term1324 x).
Proof. exact (MK_COMB (@lem1770608) (@lem1770607 x)). Qed.
Lemma lem1770610 (x : real) : (term1272 x) = (term1325 x).
Proof. exact (MK_COMB (@lem1770609 x) (@lem1770564 x)). Qed.
Lemma lem1770611 (x : real) : (term1271 x) = (term1325 x).
Proof. exact (TRANS (@lem1770521 x) (@lem1770610 x)). Qed.
Lemma lem1770612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770613 (x : real) : (term1326 x) = (term1327 x).
Proof. exact (MK_COMB (@lem1770612) (@lem1770611 x)). Qed.
Lemma lem1770614 (x : real) : (term1201 x) = (term1328 x).
Proof. exact (MK_COMB (@lem1770613 x) (@lem1770520 x)). Qed.
Lemma lem1770615 (x : real) : (term1200 x) = (term1328 x).
Proof. exact (TRANS (@lem1770405 x) (@lem1770614 x)). Qed.
Lemma lem1770616 (x : real) : (term474 x) = (term1328 x).
Proof. exact (TRANS (@lem1770404 x) (@lem1770615 x)). Qed.
Lemma lem1770617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1770618 (x : real) : (term494 x) = (term1329 x).
Proof. exact (MK_COMB (@lem1770617) (@lem1770616 x)). Qed.
Lemma lem1770619 (x : real) : (term495 x) = (term1330 x).
Proof. exact (MK_COMB (@lem1770618 x) (@lem1769227 x)). Qed.
Lemma lem1770620 : term496 = term1331.
Proof. exact (fun_ext (fun x : real => @lem1770619 x)). Qed.
Lemma lem1770621 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1770622 : term497 = term1332.
Proof. exact (MK_COMB (@lem1770621) (@lem1770620)). Qed.
Lemma lem1770623 : term33 = term1332.
Proof. exact (TRANS (@lem1768110) (@lem1770622)). Qed.
Lemma lem1771005 (x : real) (h1 : term1330 x) : term1330 x.
Proof. exact (h1). Qed.
Lemma lem1771006 (x : real) (h1 : term1328 x) : term1328 x.
Proof. exact (h1). Qed.
Lemma lem1771007 (x : real) (h1 : term1325 x) : term1325 x.
Proof. exact (h1). Qed.
Lemma lem1771008 (x : real) (h1 : term1322 x) : term1322 x.
Proof. exact (h1). Qed.
Lemma lem1771009 (x : real) (h1 : term1319 x) : term1319 x.
Proof. exact (h1). Qed.
Lemma lem1771010 (x : real) (h1 : term1316 x) : term1316 x.
Proof. exact (h1). Qed.
Lemma lem1771011 (x : real) (h1 : term1333 x) : term1333 x.
Proof. exact (h1). Qed.
Lemma lem1771012 (x : real) (h1 : term1333 x) : term1100 x.
Proof. exact (proj2 (@lem1771011 x h1)). Qed.
Lemma lem1771014 (x : real) (h1 : term1333 x) : term920 x.
Proof. exact (proj2 (@lem1771012 x h1)). Qed.
Lemma lem1771016 (x : real) (h1 : term1333 x) : term758 x.
Proof. exact (proj2 (@lem1771014 x h1)). Qed.
Lemma lem1771018 (x : real) (h1 : term1333 x) : term746 x.
Proof. exact (proj2 (@lem1771016 x h1)). Qed.
Lemma lem1771020 (x : real) (h1 : term1333 x) : term742.
Proof. exact (proj2 (@lem1771018 x h1)). Qed.
Lemma lem1771022 (x : real) (h1 : term1333 x) : term351.
Proof. exact (proj2 (@lem1771020 x h1)). Qed.
Lemma lem1771025 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771026 : term351 = False.
Proof. exact (@lem1771025 term333 (NUMERAL 0)). Qed.
Lemma lem1771027 (x : real) (h1 : term1333 x) : False.
Proof. exact (EQ_MP (@lem1771026) (@lem1771022 x h1)). Qed.
Lemma lem1771028 (x : real) (h1 : term1335 x) : term1335 x.
Proof. exact (h1). Qed.
Lemma lem1771029 (x : real) (h1 : term1335 x) : term1101 x.
Proof. exact (proj2 (@lem1771028 x h1)). Qed.
Lemma lem1771031 (x : real) (h1 : term1335 x) : term921 x.
Proof. exact (proj2 (@lem1771029 x h1)). Qed.
Lemma lem1771033 (x : real) (h1 : term1335 x) : term759 x.
Proof. exact (proj2 (@lem1771031 x h1)). Qed.
Lemma lem1771036 (x : real) (h1 : term1335 x) : term313.
Proof. exact (proj1 (@lem1771033 x h1)). Qed.
Lemma lem1771042 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771043 : term313 = False.
Proof. exact (@lem1771042 term277 (NUMERAL 0)). Qed.
Lemma lem1771044 (x : real) (h1 : term1335 x) : False.
Proof. exact (EQ_MP (@lem1771043) (@lem1771036 x h1)). Qed.
Lemma lem1771045 (x : real) (h1 : term1316 x) : False.
Proof. exact (or_elim (@lem1771010 x h1) (fun h0 : term1333 x => @lem1771027 x h0) (fun h0 : term1335 x => @lem1771044 x h0)). Qed.
Lemma lem1771046 (x : real) (h1 : term1314 x) : term1314 x.
Proof. exact (h1). Qed.
Lemma lem1771047 (x : real) (h1 : term1336 x) : term1336 x.
Proof. exact (h1). Qed.
Lemma lem1771048 (x : real) (h1 : term1336 x) : term1096 x.
Proof. exact (proj2 (@lem1771047 x h1)). Qed.
Lemma lem1771050 (x : real) (h1 : term1336 x) : term913 x.
Proof. exact (proj2 (@lem1771048 x h1)). Qed.
Lemma lem1771052 (x : real) (h1 : term1336 x) : term849 x.
Proof. exact (proj2 (@lem1771050 x h1)). Qed.
Lemma lem1771054 (x : real) (h1 : term1336 x) : term792 x.
Proof. exact (proj2 (@lem1771052 x h1)). Qed.
Lemma lem1771056 (x : real) (h1 : term1336 x) : term775.
Proof. exact (proj2 (@lem1771054 x h1)). Qed.
Lemma lem1771059 (x : real) (h1 : term1336 x) : term313.
Proof. exact (proj1 (@lem1771056 x h1)). Qed.
Lemma lem1771061 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771062 : term313 = False.
Proof. exact (@lem1771061 term277 (NUMERAL 0)). Qed.
Lemma lem1771063 (x : real) (h1 : term1336 x) : False.
Proof. exact (EQ_MP (@lem1771062) (@lem1771059 x h1)). Qed.
Lemma lem1771064 (x : real) (h1 : term1337 x) : term1337 x.
Proof. exact (h1). Qed.
Lemma lem1771065 (x : real) (h1 : term1337 x) : term1097 x.
Proof. exact (proj2 (@lem1771064 x h1)). Qed.
Lemma lem1771067 (x : real) (h1 : term1337 x) : term914 x.
Proof. exact (proj2 (@lem1771065 x h1)). Qed.
Lemma lem1771069 (x : real) (h1 : term1337 x) : term850 x.
Proof. exact (proj2 (@lem1771067 x h1)). Qed.
Lemma lem1771071 (x : real) (h1 : term1337 x) : term793 x.
Proof. exact (proj2 (@lem1771069 x h1)). Qed.
Lemma lem1771073 (x : real) (h1 : term1337 x) : term776.
Proof. exact (proj2 (@lem1771071 x h1)). Qed.
Lemma lem1771075 (x : real) (h1 : term1337 x) : term351.
Proof. exact (proj2 (@lem1771073 x h1)). Qed.
Lemma lem1771078 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771079 : term351 = False.
Proof. exact (@lem1771078 term333 (NUMERAL 0)). Qed.
Lemma lem1771080 (x : real) (h1 : term1337 x) : False.
Proof. exact (EQ_MP (@lem1771079) (@lem1771075 x h1)). Qed.
Lemma lem1771081 (x : real) (h1 : term1314 x) : False.
Proof. exact (or_elim (@lem1771046 x h1) (fun h0 : term1336 x => @lem1771063 x h0) (fun h0 : term1337 x => @lem1771080 x h0)). Qed.
Lemma lem1771082 (x : real) (h1 : term1319 x) : False.
Proof. exact (or_elim (@lem1771009 x h1) (fun h0 : term1316 x => @lem1771045 x h0) (fun h0 : term1314 x => @lem1771081 x h0)). Qed.
Lemma lem1771083 (x : real) (h1 : term1310 x) : term1310 x.
Proof. exact (h1). Qed.
Lemma lem1771084 (x : real) (h1 : term1307 x) : term1307 x.
Proof. exact (h1). Qed.
Lemma lem1771085 (x : real) (h1 : term1338 x) : term1338 x.
Proof. exact (h1). Qed.
Lemma lem1771086 (x : real) (h1 : term1338 x) : term1087 x.
Proof. exact (proj2 (@lem1771085 x h1)). Qed.
Lemma lem1771088 (x : real) (h1 : term1338 x) : term898 x.
Proof. exact (proj2 (@lem1771086 x h1)). Qed.
Lemma lem1771090 (x : real) (h1 : term1338 x) : term754 x.
Proof. exact (proj2 (@lem1771088 x h1)). Qed.
Lemma lem1771092 (x : real) (h1 : term1338 x) : term737 x.
Proof. exact (proj2 (@lem1771090 x h1)). Qed.
Lemma lem1771094 (x : real) (h1 : term1338 x) : term733.
Proof. exact (proj2 (@lem1771092 x h1)). Qed.
Lemma lem1771096 (x : real) (h1 : term1338 x) : term313.
Proof. exact (proj2 (@lem1771094 x h1)). Qed.
Lemma lem1771099 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771100 : term313 = False.
Proof. exact (@lem1771099 term277 (NUMERAL 0)). Qed.
Lemma lem1771101 (x : real) (h1 : term1338 x) : False.
Proof. exact (EQ_MP (@lem1771100) (@lem1771096 x h1)). Qed.
Lemma lem1771102 (x : real) (h1 : term1339 x) : term1339 x.
Proof. exact (h1). Qed.
Lemma lem1771104 (x : real) (h1 : term1339 x) : term282.
Proof. exact (proj1 (@lem1771102 x h1)). Qed.
Lemma lem1771116 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771117 : term282 = term1341.
Proof. exact (@lem1771116 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771118 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771119 : term282 = False.
Proof. exact (TRANS (@lem1771117) (@lem1771118)). Qed.
Lemma lem1771120 (x : real) (h1 : term1339 x) : False.
Proof. exact (EQ_MP (@lem1771119) (@lem1771104 x h1)). Qed.
Lemma lem1771121 (x : real) (h1 : term1307 x) : False.
Proof. exact (or_elim (@lem1771084 x h1) (fun h0 : term1338 x => @lem1771101 x h0) (fun h0 : term1339 x => @lem1771120 x h0)). Qed.
Lemma lem1771122 (x : real) (h1 : term1305 x) : term1305 x.
Proof. exact (h1). Qed.
Lemma lem1771123 (x : real) (h1 : term1342 x) : term1342 x.
Proof. exact (h1). Qed.
Lemma lem1771124 (x : real) (h1 : term1342 x) : term1083 x.
Proof. exact (proj2 (@lem1771123 x h1)). Qed.
Lemma lem1771126 (x : real) (h1 : term1342 x) : term891 x.
Proof. exact (proj2 (@lem1771124 x h1)). Qed.
Lemma lem1771128 (x : real) (h1 : term1342 x) : term829 x.
Proof. exact (proj2 (@lem1771126 x h1)). Qed.
Lemma lem1771130 (x : real) (h1 : term1342 x) : term792 x.
Proof. exact (proj2 (@lem1771128 x h1)). Qed.
Lemma lem1771132 (x : real) (h1 : term1342 x) : term775.
Proof. exact (proj2 (@lem1771130 x h1)). Qed.
Lemma lem1771135 (x : real) (h1 : term1342 x) : term313.
Proof. exact (proj1 (@lem1771132 x h1)). Qed.
Lemma lem1771137 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771138 : term313 = False.
Proof. exact (@lem1771137 term277 (NUMERAL 0)). Qed.
Lemma lem1771139 (x : real) (h1 : term1342 x) : False.
Proof. exact (EQ_MP (@lem1771138) (@lem1771135 x h1)). Qed.
Lemma lem1771140 (x : real) (h1 : term1343 x) : term1343 x.
Proof. exact (h1). Qed.
Lemma lem1771141 (x : real) (h1 : term1343 x) : term1084 x.
Proof. exact (proj2 (@lem1771140 x h1)). Qed.
Lemma lem1771143 (x : real) (h1 : term1343 x) : term892 x.
Proof. exact (proj2 (@lem1771141 x h1)). Qed.
Lemma lem1771145 (x : real) (h1 : term1343 x) : term830 x.
Proof. exact (proj2 (@lem1771143 x h1)). Qed.
Lemma lem1771147 (x : real) (h1 : term1343 x) : term793 x.
Proof. exact (proj2 (@lem1771145 x h1)). Qed.
Lemma lem1771149 (x : real) (h1 : term1343 x) : term776.
Proof. exact (proj2 (@lem1771147 x h1)). Qed.
Lemma lem1771151 (x : real) (h1 : term1343 x) : term351.
Proof. exact (proj2 (@lem1771149 x h1)). Qed.
Lemma lem1771154 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771155 : term351 = False.
Proof. exact (@lem1771154 term333 (NUMERAL 0)). Qed.
Lemma lem1771156 (x : real) (h1 : term1343 x) : False.
Proof. exact (EQ_MP (@lem1771155) (@lem1771151 x h1)). Qed.
Lemma lem1771157 (x : real) (h1 : term1305 x) : False.
Proof. exact (or_elim (@lem1771122 x h1) (fun h0 : term1342 x => @lem1771139 x h0) (fun h0 : term1343 x => @lem1771156 x h0)). Qed.
Lemma lem1771158 (x : real) (h1 : term1310 x) : False.
Proof. exact (or_elim (@lem1771083 x h1) (fun h0 : term1307 x => @lem1771121 x h0) (fun h0 : term1305 x => @lem1771157 x h0)). Qed.
Lemma lem1771159 (x : real) (h1 : term1322 x) : False.
Proof. exact (or_elim (@lem1771008 x h1) (fun h0 : term1319 x => @lem1771082 x h0) (fun h0 : term1310 x => @lem1771158 x h0)). Qed.
Lemma lem1771160 (x : real) (h1 : term1299 x) : term1299 x.
Proof. exact (h1). Qed.
Lemma lem1771161 (x : real) (h1 : term1296 x) : term1296 x.
Proof. exact (h1). Qed.
Lemma lem1771162 (x : real) (h1 : term1293 x) : term1293 x.
Proof. exact (h1). Qed.
Lemma lem1771163 (x : real) (h1 : term1344 x) : term1344 x.
Proof. exact (h1). Qed.
Lemma lem1771164 (x : real) (h1 : term1344 x) : term1072 x.
Proof. exact (proj2 (@lem1771163 x h1)). Qed.
Lemma lem1771166 (x : real) (h1 : term1344 x) : term874 x.
Proof. exact (proj2 (@lem1771164 x h1)). Qed.
Lemma lem1771168 (x : real) (h1 : term1344 x) : term758 x.
Proof. exact (proj2 (@lem1771166 x h1)). Qed.
Lemma lem1771170 (x : real) (h1 : term1344 x) : term746 x.
Proof. exact (proj2 (@lem1771168 x h1)). Qed.
Lemma lem1771172 (x : real) (h1 : term1344 x) : term742.
Proof. exact (proj2 (@lem1771170 x h1)). Qed.
Lemma lem1771174 (x : real) (h1 : term1344 x) : term351.
Proof. exact (proj2 (@lem1771172 x h1)). Qed.
Lemma lem1771177 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771178 : term351 = False.
Proof. exact (@lem1771177 term333 (NUMERAL 0)). Qed.
Lemma lem1771179 (x : real) (h1 : term1344 x) : False.
Proof. exact (EQ_MP (@lem1771178) (@lem1771174 x h1)). Qed.
Lemma lem1771180 (x : real) (h1 : term1345 x) : term1345 x.
Proof. exact (h1). Qed.
Lemma lem1771181 (x : real) (h1 : term1345 x) : term1073 x.
Proof. exact (proj2 (@lem1771180 x h1)). Qed.
Lemma lem1771183 (x : real) (h1 : term1345 x) : term875 x.
Proof. exact (proj2 (@lem1771181 x h1)). Qed.
Lemma lem1771185 (x : real) (h1 : term1345 x) : term759 x.
Proof. exact (proj2 (@lem1771183 x h1)). Qed.
Lemma lem1771188 (x : real) (h1 : term1345 x) : term313.
Proof. exact (proj1 (@lem1771185 x h1)). Qed.
Lemma lem1771194 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771195 : term313 = False.
Proof. exact (@lem1771194 term277 (NUMERAL 0)). Qed.
Lemma lem1771196 (x : real) (h1 : term1345 x) : False.
Proof. exact (EQ_MP (@lem1771195) (@lem1771188 x h1)). Qed.
Lemma lem1771197 (x : real) (h1 : term1293 x) : False.
Proof. exact (or_elim (@lem1771162 x h1) (fun h0 : term1344 x => @lem1771179 x h0) (fun h0 : term1345 x => @lem1771196 x h0)). Qed.
Lemma lem1771198 (x : real) (h1 : term1289 x) : term1289 x.
Proof. exact (h1). Qed.
Lemma lem1771199 (x : real) (h1 : term1346 x) : term1346 x.
Proof. exact (h1). Qed.
Lemma lem1771200 (x : real) (h1 : term1346 x) : term1290 x.
Proof. exact (proj2 (@lem1771199 x h1)). Qed.
Lemma lem1771202 (x : real) (h1 : term1346 x) : term1170 x.
Proof. exact (proj2 (@lem1771200 x h1)). Qed.
Lemma lem1771204 (x : real) (h1 : term1346 x) : term1146 x.
Proof. exact (proj2 (@lem1771202 x h1)). Qed.
Lemma lem1771207 (x : real) (h1 : term1346 x) : term313.
Proof. exact (proj1 (@lem1771204 x h1)). Qed.
Lemma lem1771211 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771212 : term313 = False.
Proof. exact (@lem1771211 term277 (NUMERAL 0)). Qed.
Lemma lem1771213 (x : real) (h1 : term1346 x) : False.
Proof. exact (EQ_MP (@lem1771212) (@lem1771207 x h1)). Qed.
Lemma lem1771214 (x : real) (h1 : term1347 x) : term1347 x.
Proof. exact (h1). Qed.
Lemma lem1771215 (x : real) (h1 : term1347 x) : term1291 x.
Proof. exact (proj2 (@lem1771214 x h1)). Qed.
Lemma lem1771217 (x : real) (h1 : term1347 x) : term1171 x.
Proof. exact (proj2 (@lem1771215 x h1)). Qed.
Lemma lem1771219 (x : real) (h1 : term1347 x) : term1147 x.
Proof. exact (proj2 (@lem1771217 x h1)). Qed.
Lemma lem1771221 (x : real) (h1 : term1347 x) : term1121 x.
Proof. exact (proj2 (@lem1771219 x h1)). Qed.
Lemma lem1771223 (x : real) (h1 : term1347 x) : term313.
Proof. exact (proj2 (@lem1771221 x h1)). Qed.
Lemma lem1771226 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771227 : term313 = False.
Proof. exact (@lem1771226 term277 (NUMERAL 0)). Qed.
Lemma lem1771228 (x : real) (h1 : term1347 x) : False.
Proof. exact (EQ_MP (@lem1771227) (@lem1771223 x h1)). Qed.
Lemma lem1771229 (x : real) (h1 : term1289 x) : False.
Proof. exact (or_elim (@lem1771198 x h1) (fun h0 : term1346 x => @lem1771213 x h0) (fun h0 : term1347 x => @lem1771228 x h0)). Qed.
Lemma lem1771230 (x : real) (h1 : term1296 x) : False.
Proof. exact (or_elim (@lem1771161 x h1) (fun h0 : term1293 x => @lem1771197 x h0) (fun h0 : term1289 x => @lem1771229 x h0)). Qed.
Lemma lem1771231 (x : real) (h1 : term1285 x) : term1285 x.
Proof. exact (h1). Qed.
Lemma lem1771232 (x : real) (h1 : term1282 x) : term1282 x.
Proof. exact (h1). Qed.
Lemma lem1771233 (x : real) (h1 : term1348 x) : term1348 x.
Proof. exact (h1). Qed.
Lemma lem1771234 (x : real) (h1 : term1348 x) : term1068 x.
Proof. exact (proj2 (@lem1771233 x h1)). Qed.
Lemma lem1771236 (x : real) (h1 : term1348 x) : term870 x.
Proof. exact (proj2 (@lem1771234 x h1)). Qed.
Lemma lem1771238 (x : real) (h1 : term1348 x) : term754 x.
Proof. exact (proj2 (@lem1771236 x h1)). Qed.
Lemma lem1771240 (x : real) (h1 : term1348 x) : term737 x.
Proof. exact (proj2 (@lem1771238 x h1)). Qed.
Lemma lem1771242 (x : real) (h1 : term1348 x) : term733.
Proof. exact (proj2 (@lem1771240 x h1)). Qed.
Lemma lem1771244 (x : real) (h1 : term1348 x) : term313.
Proof. exact (proj2 (@lem1771242 x h1)). Qed.
Lemma lem1771247 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771248 : term313 = False.
Proof. exact (@lem1771247 term277 (NUMERAL 0)). Qed.
Lemma lem1771249 (x : real) (h1 : term1348 x) : False.
Proof. exact (EQ_MP (@lem1771248) (@lem1771244 x h1)). Qed.
Lemma lem1771250 (x : real) (h1 : term1349 x) : term1349 x.
Proof. exact (h1). Qed.
Lemma lem1771252 (x : real) (h1 : term1349 x) : term282.
Proof. exact (proj1 (@lem1771250 x h1)). Qed.
Lemma lem1771264 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771265 : term282 = term1341.
Proof. exact (@lem1771264 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771266 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771267 : term282 = False.
Proof. exact (TRANS (@lem1771265) (@lem1771266)). Qed.
Lemma lem1771268 (x : real) (h1 : term1349 x) : False.
Proof. exact (EQ_MP (@lem1771267) (@lem1771252 x h1)). Qed.
Lemma lem1771269 (x : real) (h1 : term1282 x) : False.
Proof. exact (or_elim (@lem1771232 x h1) (fun h0 : term1348 x => @lem1771249 x h0) (fun h0 : term1349 x => @lem1771268 x h0)). Qed.
Lemma lem1771270 (x : real) (h1 : term1278 x) : term1278 x.
Proof. exact (h1). Qed.
Lemma lem1771271 (x : real) (h1 : term1350 x) : term1350 x.
Proof. exact (h1). Qed.
Lemma lem1771273 (x : real) (h1 : term1350 x) : term282.
Proof. exact (proj1 (@lem1771271 x h1)). Qed.
Lemma lem1771283 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771284 : term282 = term1341.
Proof. exact (@lem1771283 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771285 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771286 : term282 = False.
Proof. exact (TRANS (@lem1771284) (@lem1771285)). Qed.
Lemma lem1771287 (x : real) (h1 : term1350 x) : False.
Proof. exact (EQ_MP (@lem1771286) (@lem1771273 x h1)). Qed.
Lemma lem1771288 (x : real) (h1 : term1351 x) : term1351 x.
Proof. exact (h1). Qed.
Lemma lem1771289 (x : real) (h1 : term1351 x) : term1280 x.
Proof. exact (proj2 (@lem1771288 x h1)). Qed.
Lemma lem1771291 (x : real) (h1 : term1351 x) : term1162 x.
Proof. exact (proj2 (@lem1771289 x h1)). Qed.
Lemma lem1771293 (x : real) (h1 : term1351 x) : term1138 x.
Proof. exact (proj2 (@lem1771291 x h1)). Qed.
Lemma lem1771295 (x : real) (h1 : term1351 x) : term1121 x.
Proof. exact (proj2 (@lem1771293 x h1)). Qed.
Lemma lem1771297 (x : real) (h1 : term1351 x) : term313.
Proof. exact (proj2 (@lem1771295 x h1)). Qed.
Lemma lem1771300 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771301 : term313 = False.
Proof. exact (@lem1771300 term277 (NUMERAL 0)). Qed.
Lemma lem1771302 (x : real) (h1 : term1351 x) : False.
Proof. exact (EQ_MP (@lem1771301) (@lem1771297 x h1)). Qed.
Lemma lem1771303 (x : real) (h1 : term1278 x) : False.
Proof. exact (or_elim (@lem1771270 x h1) (fun h0 : term1350 x => @lem1771287 x h0) (fun h0 : term1351 x => @lem1771302 x h0)). Qed.
Lemma lem1771304 (x : real) (h1 : term1285 x) : False.
Proof. exact (or_elim (@lem1771231 x h1) (fun h0 : term1282 x => @lem1771269 x h0) (fun h0 : term1278 x => @lem1771303 x h0)). Qed.
Lemma lem1771305 (x : real) (h1 : term1299 x) : False.
Proof. exact (or_elim (@lem1771160 x h1) (fun h0 : term1296 x => @lem1771230 x h0) (fun h0 : term1285 x => @lem1771304 x h0)). Qed.
Lemma lem1771306 (x : real) (h1 : term1325 x) : False.
Proof. exact (or_elim (@lem1771007 x h1) (fun h0 : term1322 x => @lem1771159 x h0) (fun h0 : term1299 x => @lem1771305 x h0)). Qed.
Lemma lem1771307 (x : real) (h1 : term1270 x) : term1270 x.
Proof. exact (h1). Qed.
Lemma lem1771308 (x : real) (h1 : term1267 x) : term1267 x.
Proof. exact (h1). Qed.
Lemma lem1771309 (x : real) (h1 : term1264 x) : term1264 x.
Proof. exact (h1). Qed.
Lemma lem1771310 (x : real) (h1 : term1261 x) : term1261 x.
Proof. exact (h1). Qed.
Lemma lem1771311 (x : real) (h1 : term1352 x) : term1352 x.
Proof. exact (h1). Qed.
Lemma lem1771312 (x : real) (h1 : term1352 x) : term1051 x.
Proof. exact (proj2 (@lem1771311 x h1)). Qed.
Lemma lem1771314 (x : real) (h1 : term1352 x) : term920 x.
Proof. exact (proj2 (@lem1771312 x h1)). Qed.
Lemma lem1771316 (x : real) (h1 : term1352 x) : term758 x.
Proof. exact (proj2 (@lem1771314 x h1)). Qed.
Lemma lem1771318 (x : real) (h1 : term1352 x) : term746 x.
Proof. exact (proj2 (@lem1771316 x h1)). Qed.
Lemma lem1771320 (x : real) (h1 : term1352 x) : term742.
Proof. exact (proj2 (@lem1771318 x h1)). Qed.
Lemma lem1771322 (x : real) (h1 : term1352 x) : term351.
Proof. exact (proj2 (@lem1771320 x h1)). Qed.
Lemma lem1771325 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771326 : term351 = False.
Proof. exact (@lem1771325 term333 (NUMERAL 0)). Qed.
Lemma lem1771327 (x : real) (h1 : term1352 x) : False.
Proof. exact (EQ_MP (@lem1771326) (@lem1771322 x h1)). Qed.
Lemma lem1771328 (x : real) (h1 : term1353 x) : term1353 x.
Proof. exact (h1). Qed.
Lemma lem1771329 (x : real) (h1 : term1353 x) : term1052 x.
Proof. exact (proj2 (@lem1771328 x h1)). Qed.
Lemma lem1771331 (x : real) (h1 : term1353 x) : term921 x.
Proof. exact (proj2 (@lem1771329 x h1)). Qed.
Lemma lem1771333 (x : real) (h1 : term1353 x) : term759 x.
Proof. exact (proj2 (@lem1771331 x h1)). Qed.
Lemma lem1771336 (x : real) (h1 : term1353 x) : term313.
Proof. exact (proj1 (@lem1771333 x h1)). Qed.
Lemma lem1771342 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771343 : term313 = False.
Proof. exact (@lem1771342 term277 (NUMERAL 0)). Qed.
Lemma lem1771344 (x : real) (h1 : term1353 x) : False.
Proof. exact (EQ_MP (@lem1771343) (@lem1771336 x h1)). Qed.
Lemma lem1771345 (x : real) (h1 : term1261 x) : False.
Proof. exact (or_elim (@lem1771310 x h1) (fun h0 : term1352 x => @lem1771327 x h0) (fun h0 : term1353 x => @lem1771344 x h0)). Qed.
Lemma lem1771346 (x : real) (h1 : term1259 x) : term1259 x.
Proof. exact (h1). Qed.
Lemma lem1771347 (x : real) (h1 : term1256 x) : term1256 x.
Proof. exact (h1). Qed.
Lemma lem1771348 (x : real) (h1 : term1354 x) : term1354 x.
Proof. exact (h1). Qed.
Lemma lem1771349 (x : real) (h1 : term1354 x) : term1044 x.
Proof. exact (proj2 (@lem1771348 x h1)). Qed.
Lemma lem1771351 (x : real) (h1 : term1354 x) : term913 x.
Proof. exact (proj2 (@lem1771349 x h1)). Qed.
Lemma lem1771353 (x : real) (h1 : term1354 x) : term849 x.
Proof. exact (proj2 (@lem1771351 x h1)). Qed.
Lemma lem1771355 (x : real) (h1 : term1354 x) : term792 x.
Proof. exact (proj2 (@lem1771353 x h1)). Qed.
Lemma lem1771357 (x : real) (h1 : term1354 x) : term775.
Proof. exact (proj2 (@lem1771355 x h1)). Qed.
Lemma lem1771360 (x : real) (h1 : term1354 x) : term313.
Proof. exact (proj1 (@lem1771357 x h1)). Qed.
Lemma lem1771362 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771363 : term313 = False.
Proof. exact (@lem1771362 term277 (NUMERAL 0)). Qed.
Lemma lem1771364 (x : real) (h1 : term1354 x) : False.
Proof. exact (EQ_MP (@lem1771363) (@lem1771360 x h1)). Qed.
Lemma lem1771365 (x : real) (h1 : term1355 x) : term1355 x.
Proof. exact (h1). Qed.
Lemma lem1771366 (x : real) (h1 : term1355 x) : term1045 x.
Proof. exact (proj2 (@lem1771365 x h1)). Qed.
Lemma lem1771368 (x : real) (h1 : term1355 x) : term914 x.
Proof. exact (proj2 (@lem1771366 x h1)). Qed.
Lemma lem1771370 (x : real) (h1 : term1355 x) : term850 x.
Proof. exact (proj2 (@lem1771368 x h1)). Qed.
Lemma lem1771372 (x : real) (h1 : term1355 x) : term793 x.
Proof. exact (proj2 (@lem1771370 x h1)). Qed.
Lemma lem1771374 (x : real) (h1 : term1355 x) : term776.
Proof. exact (proj2 (@lem1771372 x h1)). Qed.
Lemma lem1771376 (x : real) (h1 : term1355 x) : term351.
Proof. exact (proj2 (@lem1771374 x h1)). Qed.
Lemma lem1771379 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771380 : term351 = False.
Proof. exact (@lem1771379 term333 (NUMERAL 0)). Qed.
Lemma lem1771381 (x : real) (h1 : term1355 x) : False.
Proof. exact (EQ_MP (@lem1771380) (@lem1771376 x h1)). Qed.
Lemma lem1771382 (x : real) (h1 : term1256 x) : False.
Proof. exact (or_elim (@lem1771347 x h1) (fun h0 : term1354 x => @lem1771364 x h0) (fun h0 : term1355 x => @lem1771381 x h0)). Qed.
Lemma lem1771383 (x : real) (h1 : term1254 x) : term1254 x.
Proof. exact (h1). Qed.
Lemma lem1771384 (x : real) (h1 : term1356 x) : term1356 x.
Proof. exact (h1). Qed.
Lemma lem1771385 (x : real) (h1 : term1356 x) : term1040 x.
Proof. exact (proj2 (@lem1771384 x h1)). Qed.
Lemma lem1771387 (x : real) (h1 : term1356 x) : term909 x.
Proof. exact (proj2 (@lem1771385 x h1)). Qed.
Lemma lem1771389 (x : real) (h1 : term1356 x) : term845 x.
Proof. exact (proj2 (@lem1771387 x h1)). Qed.
Lemma lem1771392 (x : real) (h1 : term1356 x) : term313.
Proof. exact (proj1 (@lem1771389 x h1)). Qed.
Lemma lem1771398 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771399 : term313 = False.
Proof. exact (@lem1771398 term277 (NUMERAL 0)). Qed.
Lemma lem1771400 (x : real) (h1 : term1356 x) : False.
Proof. exact (EQ_MP (@lem1771399) (@lem1771392 x h1)). Qed.
Lemma lem1771401 (x : real) (h1 : term1357 x) : term1357 x.
Proof. exact (h1). Qed.
Lemma lem1771402 (x : real) (h1 : term1357 x) : term1041 x.
Proof. exact (proj2 (@lem1771401 x h1)). Qed.
Lemma lem1771404 (x : real) (h1 : term1357 x) : term910 x.
Proof. exact (proj2 (@lem1771402 x h1)). Qed.
Lemma lem1771406 (x : real) (h1 : term1357 x) : term846 x.
Proof. exact (proj2 (@lem1771404 x h1)). Qed.
Lemma lem1771408 (x : real) (h1 : term1357 x) : term789 x.
Proof. exact (proj2 (@lem1771406 x h1)). Qed.
Lemma lem1771410 (x : real) (h1 : term1357 x) : term772.
Proof. exact (proj2 (@lem1771408 x h1)). Qed.
Lemma lem1771412 (x : real) (h1 : term1357 x) : term313.
Proof. exact (proj2 (@lem1771410 x h1)). Qed.
Lemma lem1771415 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771416 : term313 = False.
Proof. exact (@lem1771415 term277 (NUMERAL 0)). Qed.
Lemma lem1771417 (x : real) (h1 : term1357 x) : False.
Proof. exact (EQ_MP (@lem1771416) (@lem1771412 x h1)). Qed.
Lemma lem1771418 (x : real) (h1 : term1254 x) : False.
Proof. exact (or_elim (@lem1771383 x h1) (fun h0 : term1356 x => @lem1771400 x h0) (fun h0 : term1357 x => @lem1771417 x h0)). Qed.
Lemma lem1771419 (x : real) (h1 : term1259 x) : False.
Proof. exact (or_elim (@lem1771346 x h1) (fun h0 : term1256 x => @lem1771382 x h0) (fun h0 : term1254 x => @lem1771418 x h0)). Qed.
Lemma lem1771420 (x : real) (h1 : term1264 x) : False.
Proof. exact (or_elim (@lem1771309 x h1) (fun h0 : term1261 x => @lem1771345 x h0) (fun h0 : term1259 x => @lem1771419 x h0)). Qed.
Lemma lem1771421 (x : real) (h1 : term1248 x) : term1248 x.
Proof. exact (h1). Qed.
Lemma lem1771422 (x : real) (h1 : term1245 x) : term1245 x.
Proof. exact (h1). Qed.
Lemma lem1771423 (x : real) (h1 : term1358 x) : term1358 x.
Proof. exact (h1). Qed.
Lemma lem1771424 (x : real) (h1 : term1358 x) : term1029 x.
Proof. exact (proj2 (@lem1771423 x h1)). Qed.
Lemma lem1771426 (x : real) (h1 : term1358 x) : term898 x.
Proof. exact (proj2 (@lem1771424 x h1)). Qed.
Lemma lem1771428 (x : real) (h1 : term1358 x) : term754 x.
Proof. exact (proj2 (@lem1771426 x h1)). Qed.
Lemma lem1771430 (x : real) (h1 : term1358 x) : term737 x.
Proof. exact (proj2 (@lem1771428 x h1)). Qed.
Lemma lem1771432 (x : real) (h1 : term1358 x) : term733.
Proof. exact (proj2 (@lem1771430 x h1)). Qed.
Lemma lem1771434 (x : real) (h1 : term1358 x) : term313.
Proof. exact (proj2 (@lem1771432 x h1)). Qed.
Lemma lem1771437 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771438 : term313 = False.
Proof. exact (@lem1771437 term277 (NUMERAL 0)). Qed.
Lemma lem1771439 (x : real) (h1 : term1358 x) : False.
Proof. exact (EQ_MP (@lem1771438) (@lem1771434 x h1)). Qed.
Lemma lem1771440 (x : real) (h1 : term1359 x) : term1359 x.
Proof. exact (h1). Qed.
Lemma lem1771442 (x : real) (h1 : term1359 x) : term282.
Proof. exact (proj1 (@lem1771440 x h1)). Qed.
Lemma lem1771454 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771455 : term282 = term1341.
Proof. exact (@lem1771454 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771456 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771457 : term282 = False.
Proof. exact (TRANS (@lem1771455) (@lem1771456)). Qed.
Lemma lem1771458 (x : real) (h1 : term1359 x) : False.
Proof. exact (EQ_MP (@lem1771457) (@lem1771442 x h1)). Qed.
Lemma lem1771459 (x : real) (h1 : term1245 x) : False.
Proof. exact (or_elim (@lem1771422 x h1) (fun h0 : term1358 x => @lem1771439 x h0) (fun h0 : term1359 x => @lem1771458 x h0)). Qed.
Lemma lem1771460 (x : real) (h1 : term1243 x) : term1243 x.
Proof. exact (h1). Qed.
Lemma lem1771461 (x : real) (h1 : term1240 x) : term1240 x.
Proof. exact (h1). Qed.
Lemma lem1771462 (x : real) (h1 : term1360 x) : term1360 x.
Proof. exact (h1). Qed.
Lemma lem1771463 (x : real) (h1 : term1360 x) : term1022 x.
Proof. exact (proj2 (@lem1771462 x h1)). Qed.
Lemma lem1771465 (x : real) (h1 : term1360 x) : term891 x.
Proof. exact (proj2 (@lem1771463 x h1)). Qed.
Lemma lem1771467 (x : real) (h1 : term1360 x) : term829 x.
Proof. exact (proj2 (@lem1771465 x h1)). Qed.
Lemma lem1771469 (x : real) (h1 : term1360 x) : term792 x.
Proof. exact (proj2 (@lem1771467 x h1)). Qed.
Lemma lem1771471 (x : real) (h1 : term1360 x) : term775.
Proof. exact (proj2 (@lem1771469 x h1)). Qed.
Lemma lem1771474 (x : real) (h1 : term1360 x) : term313.
Proof. exact (proj1 (@lem1771471 x h1)). Qed.
Lemma lem1771476 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771477 : term313 = False.
Proof. exact (@lem1771476 term277 (NUMERAL 0)). Qed.
Lemma lem1771478 (x : real) (h1 : term1360 x) : False.
Proof. exact (EQ_MP (@lem1771477) (@lem1771474 x h1)). Qed.
Lemma lem1771479 (x : real) (h1 : term1361 x) : term1361 x.
Proof. exact (h1). Qed.
Lemma lem1771480 (x : real) (h1 : term1361 x) : term1023 x.
Proof. exact (proj2 (@lem1771479 x h1)). Qed.
Lemma lem1771482 (x : real) (h1 : term1361 x) : term892 x.
Proof. exact (proj2 (@lem1771480 x h1)). Qed.
Lemma lem1771484 (x : real) (h1 : term1361 x) : term830 x.
Proof. exact (proj2 (@lem1771482 x h1)). Qed.
Lemma lem1771486 (x : real) (h1 : term1361 x) : term793 x.
Proof. exact (proj2 (@lem1771484 x h1)). Qed.
Lemma lem1771488 (x : real) (h1 : term1361 x) : term776.
Proof. exact (proj2 (@lem1771486 x h1)). Qed.
Lemma lem1771490 (x : real) (h1 : term1361 x) : term351.
Proof. exact (proj2 (@lem1771488 x h1)). Qed.
Lemma lem1771493 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771494 : term351 = False.
Proof. exact (@lem1771493 term333 (NUMERAL 0)). Qed.
Lemma lem1771495 (x : real) (h1 : term1361 x) : False.
Proof. exact (EQ_MP (@lem1771494) (@lem1771490 x h1)). Qed.
Lemma lem1771496 (x : real) (h1 : term1240 x) : False.
Proof. exact (or_elim (@lem1771461 x h1) (fun h0 : term1360 x => @lem1771478 x h0) (fun h0 : term1361 x => @lem1771495 x h0)). Qed.
Lemma lem1771497 (x : real) (h1 : term1238 x) : term1238 x.
Proof. exact (h1). Qed.
Lemma lem1771498 (x : real) (h1 : term1362 x) : term1362 x.
Proof. exact (h1). Qed.
Lemma lem1771500 (x : real) (h1 : term1362 x) : term282.
Proof. exact (proj1 (@lem1771498 x h1)). Qed.
Lemma lem1771512 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771513 : term282 = term1341.
Proof. exact (@lem1771512 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771514 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771515 : term282 = False.
Proof. exact (TRANS (@lem1771513) (@lem1771514)). Qed.
Lemma lem1771516 (x : real) (h1 : term1362 x) : False.
Proof. exact (EQ_MP (@lem1771515) (@lem1771500 x h1)). Qed.
Lemma lem1771517 (x : real) (h1 : term1363 x) : term1363 x.
Proof. exact (h1). Qed.
Lemma lem1771518 (x : real) (h1 : term1363 x) : term1019 x.
Proof. exact (proj2 (@lem1771517 x h1)). Qed.
Lemma lem1771520 (x : real) (h1 : term1363 x) : term888 x.
Proof. exact (proj2 (@lem1771518 x h1)). Qed.
Lemma lem1771522 (x : real) (h1 : term1363 x) : term826 x.
Proof. exact (proj2 (@lem1771520 x h1)). Qed.
Lemma lem1771524 (x : real) (h1 : term1363 x) : term789 x.
Proof. exact (proj2 (@lem1771522 x h1)). Qed.
Lemma lem1771526 (x : real) (h1 : term1363 x) : term772.
Proof. exact (proj2 (@lem1771524 x h1)). Qed.
Lemma lem1771528 (x : real) (h1 : term1363 x) : term313.
Proof. exact (proj2 (@lem1771526 x h1)). Qed.
Lemma lem1771531 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771532 : term313 = False.
Proof. exact (@lem1771531 term277 (NUMERAL 0)). Qed.
Lemma lem1771533 (x : real) (h1 : term1363 x) : False.
Proof. exact (EQ_MP (@lem1771532) (@lem1771528 x h1)). Qed.
Lemma lem1771534 (x : real) (h1 : term1238 x) : False.
Proof. exact (or_elim (@lem1771497 x h1) (fun h0 : term1362 x => @lem1771516 x h0) (fun h0 : term1363 x => @lem1771533 x h0)). Qed.
Lemma lem1771535 (x : real) (h1 : term1243 x) : False.
Proof. exact (or_elim (@lem1771460 x h1) (fun h0 : term1240 x => @lem1771496 x h0) (fun h0 : term1238 x => @lem1771534 x h0)). Qed.
Lemma lem1771536 (x : real) (h1 : term1248 x) : False.
Proof. exact (or_elim (@lem1771421 x h1) (fun h0 : term1245 x => @lem1771459 x h0) (fun h0 : term1243 x => @lem1771535 x h0)). Qed.
Lemma lem1771537 (x : real) (h1 : term1267 x) : False.
Proof. exact (or_elim (@lem1771308 x h1) (fun h0 : term1264 x => @lem1771420 x h0) (fun h0 : term1248 x => @lem1771536 x h0)). Qed.
Lemma lem1771538 (x : real) (h1 : term1230 x) : term1230 x.
Proof. exact (h1). Qed.
Lemma lem1771539 (x : real) (h1 : term1227 x) : term1227 x.
Proof. exact (h1). Qed.
Lemma lem1771540 (x : real) (h1 : term1224 x) : term1224 x.
Proof. exact (h1). Qed.
Lemma lem1771541 (x : real) (h1 : term1364 x) : term1364 x.
Proof. exact (h1). Qed.
Lemma lem1771542 (x : real) (h1 : term1364 x) : term1005 x.
Proof. exact (proj2 (@lem1771541 x h1)). Qed.
Lemma lem1771544 (x : real) (h1 : term1364 x) : term874 x.
Proof. exact (proj2 (@lem1771542 x h1)). Qed.
Lemma lem1771546 (x : real) (h1 : term1364 x) : term758 x.
Proof. exact (proj2 (@lem1771544 x h1)). Qed.
Lemma lem1771548 (x : real) (h1 : term1364 x) : term746 x.
Proof. exact (proj2 (@lem1771546 x h1)). Qed.
Lemma lem1771550 (x : real) (h1 : term1364 x) : term742.
Proof. exact (proj2 (@lem1771548 x h1)). Qed.
Lemma lem1771552 (x : real) (h1 : term1364 x) : term351.
Proof. exact (proj2 (@lem1771550 x h1)). Qed.
Lemma lem1771555 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771556 : term351 = False.
Proof. exact (@lem1771555 term333 (NUMERAL 0)). Qed.
Lemma lem1771557 (x : real) (h1 : term1364 x) : False.
Proof. exact (EQ_MP (@lem1771556) (@lem1771552 x h1)). Qed.
Lemma lem1771558 (x : real) (h1 : term1365 x) : term1365 x.
Proof. exact (h1). Qed.
Lemma lem1771559 (x : real) (h1 : term1365 x) : term1006 x.
Proof. exact (proj2 (@lem1771558 x h1)). Qed.
Lemma lem1771561 (x : real) (h1 : term1365 x) : term875 x.
Proof. exact (proj2 (@lem1771559 x h1)). Qed.
Lemma lem1771563 (x : real) (h1 : term1365 x) : term759 x.
Proof. exact (proj2 (@lem1771561 x h1)). Qed.
Lemma lem1771566 (x : real) (h1 : term1365 x) : term313.
Proof. exact (proj1 (@lem1771563 x h1)). Qed.
Lemma lem1771572 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771573 : term313 = False.
Proof. exact (@lem1771572 term277 (NUMERAL 0)). Qed.
Lemma lem1771574 (x : real) (h1 : term1365 x) : False.
Proof. exact (EQ_MP (@lem1771573) (@lem1771566 x h1)). Qed.
Lemma lem1771575 (x : real) (h1 : term1224 x) : False.
Proof. exact (or_elim (@lem1771540 x h1) (fun h0 : term1364 x => @lem1771557 x h0) (fun h0 : term1365 x => @lem1771574 x h0)). Qed.
Lemma lem1771576 (x : real) (h1 : term1220 x) : term1220 x.
Proof. exact (h1). Qed.
Lemma lem1771577 (x : real) (h1 : term1366 x) : term1366 x.
Proof. exact (h1). Qed.
Lemma lem1771578 (x : real) (h1 : term1366 x) : term1221 x.
Proof. exact (proj2 (@lem1771577 x h1)). Qed.
Lemma lem1771580 (x : real) (h1 : term1366 x) : term1170 x.
Proof. exact (proj2 (@lem1771578 x h1)). Qed.
Lemma lem1771582 (x : real) (h1 : term1366 x) : term1146 x.
Proof. exact (proj2 (@lem1771580 x h1)). Qed.
Lemma lem1771585 (x : real) (h1 : term1366 x) : term313.
Proof. exact (proj1 (@lem1771582 x h1)). Qed.
Lemma lem1771589 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771590 : term313 = False.
Proof. exact (@lem1771589 term277 (NUMERAL 0)). Qed.
Lemma lem1771591 (x : real) (h1 : term1366 x) : False.
Proof. exact (EQ_MP (@lem1771590) (@lem1771585 x h1)). Qed.
Lemma lem1771592 (x : real) (h1 : term1367 x) : term1367 x.
Proof. exact (h1). Qed.
Lemma lem1771593 (x : real) (h1 : term1367 x) : term1222 x.
Proof. exact (proj2 (@lem1771592 x h1)). Qed.
Lemma lem1771595 (x : real) (h1 : term1367 x) : term1171 x.
Proof. exact (proj2 (@lem1771593 x h1)). Qed.
Lemma lem1771597 (x : real) (h1 : term1367 x) : term1147 x.
Proof. exact (proj2 (@lem1771595 x h1)). Qed.
Lemma lem1771599 (x : real) (h1 : term1367 x) : term1121 x.
Proof. exact (proj2 (@lem1771597 x h1)). Qed.
Lemma lem1771601 (x : real) (h1 : term1367 x) : term313.
Proof. exact (proj2 (@lem1771599 x h1)). Qed.
Lemma lem1771604 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771605 : term313 = False.
Proof. exact (@lem1771604 term277 (NUMERAL 0)). Qed.
Lemma lem1771606 (x : real) (h1 : term1367 x) : False.
Proof. exact (EQ_MP (@lem1771605) (@lem1771601 x h1)). Qed.
Lemma lem1771607 (x : real) (h1 : term1220 x) : False.
Proof. exact (or_elim (@lem1771576 x h1) (fun h0 : term1366 x => @lem1771591 x h0) (fun h0 : term1367 x => @lem1771606 x h0)). Qed.
Lemma lem1771608 (x : real) (h1 : term1227 x) : False.
Proof. exact (or_elim (@lem1771539 x h1) (fun h0 : term1224 x => @lem1771575 x h0) (fun h0 : term1220 x => @lem1771607 x h0)). Qed.
Lemma lem1771609 (x : real) (h1 : term1216 x) : term1216 x.
Proof. exact (h1). Qed.
Lemma lem1771610 (x : real) (h1 : term1213 x) : term1213 x.
Proof. exact (h1). Qed.
Lemma lem1771611 (x : real) (h1 : term1368 x) : term1368 x.
Proof. exact (h1). Qed.
Lemma lem1771612 (x : real) (h1 : term1368 x) : term1001 x.
Proof. exact (proj2 (@lem1771611 x h1)). Qed.
Lemma lem1771614 (x : real) (h1 : term1368 x) : term870 x.
Proof. exact (proj2 (@lem1771612 x h1)). Qed.
Lemma lem1771616 (x : real) (h1 : term1368 x) : term754 x.
Proof. exact (proj2 (@lem1771614 x h1)). Qed.
Lemma lem1771618 (x : real) (h1 : term1368 x) : term737 x.
Proof. exact (proj2 (@lem1771616 x h1)). Qed.
Lemma lem1771620 (x : real) (h1 : term1368 x) : term733.
Proof. exact (proj2 (@lem1771618 x h1)). Qed.
Lemma lem1771622 (x : real) (h1 : term1368 x) : term313.
Proof. exact (proj2 (@lem1771620 x h1)). Qed.
Lemma lem1771625 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771626 : term313 = False.
Proof. exact (@lem1771625 term277 (NUMERAL 0)). Qed.
Lemma lem1771627 (x : real) (h1 : term1368 x) : False.
Proof. exact (EQ_MP (@lem1771626) (@lem1771622 x h1)). Qed.
Lemma lem1771628 (x : real) (h1 : term1369 x) : term1369 x.
Proof. exact (h1). Qed.
Lemma lem1771630 (x : real) (h1 : term1369 x) : term282.
Proof. exact (proj1 (@lem1771628 x h1)). Qed.
Lemma lem1771642 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771643 : term282 = term1341.
Proof. exact (@lem1771642 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771644 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771645 : term282 = False.
Proof. exact (TRANS (@lem1771643) (@lem1771644)). Qed.
Lemma lem1771646 (x : real) (h1 : term1369 x) : False.
Proof. exact (EQ_MP (@lem1771645) (@lem1771630 x h1)). Qed.
Lemma lem1771647 (x : real) (h1 : term1213 x) : False.
Proof. exact (or_elim (@lem1771610 x h1) (fun h0 : term1368 x => @lem1771627 x h0) (fun h0 : term1369 x => @lem1771646 x h0)). Qed.
Lemma lem1771648 (x : real) (h1 : term1209 x) : term1209 x.
Proof. exact (h1). Qed.
Lemma lem1771649 (x : real) (h1 : term1370 x) : term1370 x.
Proof. exact (h1). Qed.
Lemma lem1771651 (x : real) (h1 : term1370 x) : term282.
Proof. exact (proj1 (@lem1771649 x h1)). Qed.
Lemma lem1771661 (n : nat) (m : nat) : (term1340 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1771662 : term282 = term1341.
Proof. exact (@lem1771661 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1771663 : term1341 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1771664 : term282 = False.
Proof. exact (TRANS (@lem1771662) (@lem1771663)). Qed.
Lemma lem1771665 (x : real) (h1 : term1370 x) : False.
Proof. exact (EQ_MP (@lem1771664) (@lem1771651 x h1)). Qed.
Lemma lem1771666 (x : real) (h1 : term1371 x) : term1371 x.
Proof. exact (h1). Qed.
Lemma lem1771667 (x : real) (h1 : term1371 x) : term1211 x.
Proof. exact (proj2 (@lem1771666 x h1)). Qed.
Lemma lem1771669 (x : real) (h1 : term1371 x) : term1162 x.
Proof. exact (proj2 (@lem1771667 x h1)). Qed.
Lemma lem1771671 (x : real) (h1 : term1371 x) : term1138 x.
Proof. exact (proj2 (@lem1771669 x h1)). Qed.
Lemma lem1771673 (x : real) (h1 : term1371 x) : term1121 x.
Proof. exact (proj2 (@lem1771671 x h1)). Qed.
Lemma lem1771675 (x : real) (h1 : term1371 x) : term313.
Proof. exact (proj2 (@lem1771673 x h1)). Qed.
Lemma lem1771678 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771679 : term313 = False.
Proof. exact (@lem1771678 term277 (NUMERAL 0)). Qed.
Lemma lem1771680 (x : real) (h1 : term1371 x) : False.
Proof. exact (EQ_MP (@lem1771679) (@lem1771675 x h1)). Qed.
Lemma lem1771681 (x : real) (h1 : term1209 x) : False.
Proof. exact (or_elim (@lem1771648 x h1) (fun h0 : term1370 x => @lem1771665 x h0) (fun h0 : term1371 x => @lem1771680 x h0)). Qed.
Lemma lem1771682 (x : real) (h1 : term1216 x) : False.
Proof. exact (or_elim (@lem1771609 x h1) (fun h0 : term1213 x => @lem1771647 x h0) (fun h0 : term1209 x => @lem1771681 x h0)). Qed.
Lemma lem1771683 (x : real) (h1 : term1230 x) : False.
Proof. exact (or_elim (@lem1771538 x h1) (fun h0 : term1227 x => @lem1771608 x h0) (fun h0 : term1216 x => @lem1771682 x h0)). Qed.
Lemma lem1771684 (x : real) (h1 : term1270 x) : False.
Proof. exact (or_elim (@lem1771307 x h1) (fun h0 : term1267 x => @lem1771537 x h0) (fun h0 : term1230 x => @lem1771683 x h0)). Qed.
Lemma lem1771685 (x : real) (h1 : term1328 x) : False.
Proof. exact (or_elim (@lem1771006 x h1) (fun h0 : term1325 x => @lem1771306 x h0) (fun h0 : term1270 x => @lem1771684 x h0)). Qed.
Lemma lem1771686 (x : real) (h1 : term1113 x) : term1113 x.
Proof. exact (h1). Qed.
Lemma lem1771687 (x : real) (h1 : term1110 x) : term1110 x.
Proof. exact (h1). Qed.
Lemma lem1771688 (x : real) (h1 : term1107 x) : term1107 x.
Proof. exact (h1). Qed.
Lemma lem1771689 (x : real) (h1 : term1104 x) : term1104 x.
Proof. exact (h1). Qed.
Lemma lem1771690 (x : real) (h1 : term1099 x) : term1099 x.
Proof. exact (h1). Qed.
Lemma lem1771691 (x : real) (h1 : term1372 x) : term1372 x.
Proof. exact (h1). Qed.
Lemma lem1771692 (x : real) (h1 : term1372 x) : term1100 x.
Proof. exact (proj2 (@lem1771691 x h1)). Qed.
Lemma lem1771694 (x : real) (h1 : term1372 x) : term920 x.
Proof. exact (proj2 (@lem1771692 x h1)). Qed.
Lemma lem1771696 (x : real) (h1 : term1372 x) : term758 x.
Proof. exact (proj2 (@lem1771694 x h1)). Qed.
Lemma lem1771698 (x : real) (h1 : term1372 x) : term746 x.
Proof. exact (proj2 (@lem1771696 x h1)). Qed.
Lemma lem1771700 (x : real) (h1 : term1372 x) : term742.
Proof. exact (proj2 (@lem1771698 x h1)). Qed.
Lemma lem1771702 (x : real) (h1 : term1372 x) : term351.
Proof. exact (proj2 (@lem1771700 x h1)). Qed.
Lemma lem1771705 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771706 : term351 = False.
Proof. exact (@lem1771705 term333 (NUMERAL 0)). Qed.
Lemma lem1771707 (x : real) (h1 : term1372 x) : False.
Proof. exact (EQ_MP (@lem1771706) (@lem1771702 x h1)). Qed.
Lemma lem1771708 (x : real) (h1 : term1373 x) : term1373 x.
Proof. exact (h1). Qed.
Lemma lem1771709 (x : real) (h1 : term1373 x) : term1101 x.
Proof. exact (proj2 (@lem1771708 x h1)). Qed.
Lemma lem1771711 (x : real) (h1 : term1373 x) : term921 x.
Proof. exact (proj2 (@lem1771709 x h1)). Qed.
Lemma lem1771713 (x : real) (h1 : term1373 x) : term759 x.
Proof. exact (proj2 (@lem1771711 x h1)). Qed.
Lemma lem1771716 (x : real) (h1 : term1373 x) : term313.
Proof. exact (proj1 (@lem1771713 x h1)). Qed.
Lemma lem1771722 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771723 : term313 = False.
Proof. exact (@lem1771722 term277 (NUMERAL 0)). Qed.
Lemma lem1771724 (x : real) (h1 : term1373 x) : False.
Proof. exact (EQ_MP (@lem1771723) (@lem1771716 x h1)). Qed.
Lemma lem1771725 (x : real) (h1 : term1099 x) : False.
Proof. exact (or_elim (@lem1771690 x h1) (fun h0 : term1372 x => @lem1771707 x h0) (fun h0 : term1373 x => @lem1771724 x h0)). Qed.
Lemma lem1771726 (x : real) (h1 : term1095 x) : term1095 x.
Proof. exact (h1). Qed.
Lemma lem1771727 (x : real) (h1 : term1374 x) : term1374 x.
Proof. exact (h1). Qed.
Lemma lem1771728 (x : real) (h1 : term1374 x) : term1096 x.
Proof. exact (proj2 (@lem1771727 x h1)). Qed.
Lemma lem1771730 (x : real) (h1 : term1374 x) : term913 x.
Proof. exact (proj2 (@lem1771728 x h1)). Qed.
Lemma lem1771732 (x : real) (h1 : term1374 x) : term849 x.
Proof. exact (proj2 (@lem1771730 x h1)). Qed.
Lemma lem1771734 (x : real) (h1 : term1374 x) : term792 x.
Proof. exact (proj2 (@lem1771732 x h1)). Qed.
Lemma lem1771736 (x : real) (h1 : term1374 x) : term775.
Proof. exact (proj2 (@lem1771734 x h1)). Qed.
Lemma lem1771739 (x : real) (h1 : term1374 x) : term313.
Proof. exact (proj1 (@lem1771736 x h1)). Qed.
Lemma lem1771741 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771742 : term313 = False.
Proof. exact (@lem1771741 term277 (NUMERAL 0)). Qed.
Lemma lem1771743 (x : real) (h1 : term1374 x) : False.
Proof. exact (EQ_MP (@lem1771742) (@lem1771739 x h1)). Qed.
Lemma lem1771744 (x : real) (h1 : term1375 x) : term1375 x.
Proof. exact (h1). Qed.
Lemma lem1771745 (x : real) (h1 : term1375 x) : term1097 x.
Proof. exact (proj2 (@lem1771744 x h1)). Qed.
Lemma lem1771747 (x : real) (h1 : term1375 x) : term914 x.
Proof. exact (proj2 (@lem1771745 x h1)). Qed.
Lemma lem1771749 (x : real) (h1 : term1375 x) : term850 x.
Proof. exact (proj2 (@lem1771747 x h1)). Qed.
Lemma lem1771751 (x : real) (h1 : term1375 x) : term793 x.
Proof. exact (proj2 (@lem1771749 x h1)). Qed.
Lemma lem1771753 (x : real) (h1 : term1375 x) : term776.
Proof. exact (proj2 (@lem1771751 x h1)). Qed.
Lemma lem1771755 (x : real) (h1 : term1375 x) : term351.
Proof. exact (proj2 (@lem1771753 x h1)). Qed.
Lemma lem1771758 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771759 : term351 = False.
Proof. exact (@lem1771758 term333 (NUMERAL 0)). Qed.
Lemma lem1771760 (x : real) (h1 : term1375 x) : False.
Proof. exact (EQ_MP (@lem1771759) (@lem1771755 x h1)). Qed.
Lemma lem1771761 (x : real) (h1 : term1095 x) : False.
Proof. exact (or_elim (@lem1771726 x h1) (fun h0 : term1374 x => @lem1771743 x h0) (fun h0 : term1375 x => @lem1771760 x h0)). Qed.
Lemma lem1771762 (x : real) (h1 : term1104 x) : False.
Proof. exact (or_elim (@lem1771689 x h1) (fun h0 : term1099 x => @lem1771725 x h0) (fun h0 : term1095 x => @lem1771761 x h0)). Qed.
Lemma lem1771763 (x : real) (h1 : term1091 x) : term1091 x.
Proof. exact (h1). Qed.
Lemma lem1771764 (x : real) (h1 : term1086 x) : term1086 x.
Proof. exact (h1). Qed.
Lemma lem1771765 (x : real) (h1 : term1376 x) : term1376 x.
Proof. exact (h1). Qed.
Lemma lem1771766 (x : real) (h1 : term1376 x) : term1087 x.
Proof. exact (proj2 (@lem1771765 x h1)). Qed.
Lemma lem1771768 (x : real) (h1 : term1376 x) : term898 x.
Proof. exact (proj2 (@lem1771766 x h1)). Qed.
Lemma lem1771770 (x : real) (h1 : term1376 x) : term754 x.
Proof. exact (proj2 (@lem1771768 x h1)). Qed.
Lemma lem1771772 (x : real) (h1 : term1376 x) : term737 x.
Proof. exact (proj2 (@lem1771770 x h1)). Qed.
Lemma lem1771774 (x : real) (h1 : term1376 x) : term733.
Proof. exact (proj2 (@lem1771772 x h1)). Qed.
Lemma lem1771776 (x : real) (h1 : term1376 x) : term313.
Proof. exact (proj2 (@lem1771774 x h1)). Qed.
Lemma lem1771779 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771780 : term313 = False.
Proof. exact (@lem1771779 term277 (NUMERAL 0)). Qed.
Lemma lem1771781 (x : real) (h1 : term1376 x) : False.
Proof. exact (EQ_MP (@lem1771780) (@lem1771776 x h1)). Qed.
Lemma lem1771782 (x : real) (h1 : term1377 x) : term1377 x.
Proof. exact (h1). Qed.
Lemma lem1771783 (x : real) (h1 : term1377 x) : term1088 x.
Proof. exact (proj2 (@lem1771782 x h1)). Qed.
Lemma lem1771785 (x : real) (h1 : term1377 x) : term899 x.
Proof. exact (proj2 (@lem1771783 x h1)). Qed.
Lemma lem1771787 (x : real) (h1 : term1377 x) : term755 x.
Proof. exact (proj2 (@lem1771785 x h1)). Qed.
Lemma lem1771789 (x : real) (h1 : term1377 x) : term738 x.
Proof. exact (proj2 (@lem1771787 x h1)). Qed.
Lemma lem1771791 (x : real) (h1 : term1377 x) : term734.
Proof. exact (proj2 (@lem1771789 x h1)). Qed.
Lemma lem1771794 (x : real) (h1 : term1377 x) : term323.
Proof. exact (proj1 (@lem1771791 x h1)). Qed.
Lemma lem1771796 (m : nat) (n : nat) : (term1378 m n) = (term1379 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1771797 : term323 = term1380.
Proof. exact (@lem1771796 term277 (NUMERAL 0)). Qed.
Lemma lem1771798 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1771799 : term1381 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1771800 (h1 : term1381 = (BIT1 0)) : (term277 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1771801 : (term1381 = (BIT1 0)) = ((term277 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1381 = (BIT1 0) => @lem1771800 h1) (fun h1 : (term277 = (NUMERAL 0)) = False => @lem1771799)). Qed.
Lemma lem1771802 : (term277 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1771801) (@lem1771799)). Qed.
Lemma lem1771803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1771804 : term1382 = (and False).
Proof. exact (MK_COMB (@lem1771803) (@lem1771802)). Qed.
Lemma lem1771805 : term1380 = (False /\ True).
Proof. exact (MK_COMB (@lem1771804) (@lem1771798)). Qed.
Lemma lem1771807 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1771808 : term1380 = False.
Proof. exact (TRANS (@lem1771805) (@lem1771807)). Qed.
Lemma lem1771809 : term323 = False.
Proof. exact (TRANS (@lem1771797) (@lem1771808)). Qed.
Lemma lem1771810 (x : real) (h1 : term1377 x) : False.
Proof. exact (EQ_MP (@lem1771809) (@lem1771794 x h1)). Qed.
Lemma lem1771811 (x : real) (h1 : term1086 x) : False.
Proof. exact (or_elim (@lem1771764 x h1) (fun h0 : term1376 x => @lem1771781 x h0) (fun h0 : term1377 x => @lem1771810 x h0)). Qed.
Lemma lem1771812 (x : real) (h1 : term1082 x) : term1082 x.
Proof. exact (h1). Qed.
Lemma lem1771813 (x : real) (h1 : term1383 x) : term1383 x.
Proof. exact (h1). Qed.
Lemma lem1771814 (x : real) (h1 : term1383 x) : term1083 x.
Proof. exact (proj2 (@lem1771813 x h1)). Qed.
Lemma lem1771816 (x : real) (h1 : term1383 x) : term891 x.
Proof. exact (proj2 (@lem1771814 x h1)). Qed.
Lemma lem1771818 (x : real) (h1 : term1383 x) : term829 x.
Proof. exact (proj2 (@lem1771816 x h1)). Qed.
Lemma lem1771820 (x : real) (h1 : term1383 x) : term792 x.
Proof. exact (proj2 (@lem1771818 x h1)). Qed.
Lemma lem1771822 (x : real) (h1 : term1383 x) : term775.
Proof. exact (proj2 (@lem1771820 x h1)). Qed.
Lemma lem1771825 (x : real) (h1 : term1383 x) : term313.
Proof. exact (proj1 (@lem1771822 x h1)). Qed.
Lemma lem1771827 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771828 : term313 = False.
Proof. exact (@lem1771827 term277 (NUMERAL 0)). Qed.
Lemma lem1771829 (x : real) (h1 : term1383 x) : False.
Proof. exact (EQ_MP (@lem1771828) (@lem1771825 x h1)). Qed.
Lemma lem1771830 (x : real) (h1 : term1384 x) : term1384 x.
Proof. exact (h1). Qed.
Lemma lem1771831 (x : real) (h1 : term1384 x) : term1084 x.
Proof. exact (proj2 (@lem1771830 x h1)). Qed.
Lemma lem1771833 (x : real) (h1 : term1384 x) : term892 x.
Proof. exact (proj2 (@lem1771831 x h1)). Qed.
Lemma lem1771835 (x : real) (h1 : term1384 x) : term830 x.
Proof. exact (proj2 (@lem1771833 x h1)). Qed.
Lemma lem1771837 (x : real) (h1 : term1384 x) : term793 x.
Proof. exact (proj2 (@lem1771835 x h1)). Qed.
Lemma lem1771839 (x : real) (h1 : term1384 x) : term776.
Proof. exact (proj2 (@lem1771837 x h1)). Qed.
Lemma lem1771841 (x : real) (h1 : term1384 x) : term351.
Proof. exact (proj2 (@lem1771839 x h1)). Qed.
Lemma lem1771844 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771845 : term351 = False.
Proof. exact (@lem1771844 term333 (NUMERAL 0)). Qed.
Lemma lem1771846 (x : real) (h1 : term1384 x) : False.
Proof. exact (EQ_MP (@lem1771845) (@lem1771841 x h1)). Qed.
Lemma lem1771847 (x : real) (h1 : term1082 x) : False.
Proof. exact (or_elim (@lem1771812 x h1) (fun h0 : term1383 x => @lem1771829 x h0) (fun h0 : term1384 x => @lem1771846 x h0)). Qed.
Lemma lem1771848 (x : real) (h1 : term1091 x) : False.
Proof. exact (or_elim (@lem1771763 x h1) (fun h0 : term1086 x => @lem1771811 x h0) (fun h0 : term1082 x => @lem1771847 x h0)). Qed.
Lemma lem1771849 (x : real) (h1 : term1107 x) : False.
Proof. exact (or_elim (@lem1771688 x h1) (fun h0 : term1104 x => @lem1771762 x h0) (fun h0 : term1091 x => @lem1771848 x h0)). Qed.
Lemma lem1771850 (x : real) (h1 : term1076 x) : term1076 x.
Proof. exact (h1). Qed.
Lemma lem1771851 (x : real) (h1 : term1071 x) : term1071 x.
Proof. exact (h1). Qed.
Lemma lem1771852 (x : real) (h1 : term1385 x) : term1385 x.
Proof. exact (h1). Qed.
Lemma lem1771853 (x : real) (h1 : term1385 x) : term1072 x.
Proof. exact (proj2 (@lem1771852 x h1)). Qed.
Lemma lem1771855 (x : real) (h1 : term1385 x) : term874 x.
Proof. exact (proj2 (@lem1771853 x h1)). Qed.
Lemma lem1771857 (x : real) (h1 : term1385 x) : term758 x.
Proof. exact (proj2 (@lem1771855 x h1)). Qed.
Lemma lem1771859 (x : real) (h1 : term1385 x) : term746 x.
Proof. exact (proj2 (@lem1771857 x h1)). Qed.
Lemma lem1771861 (x : real) (h1 : term1385 x) : term742.
Proof. exact (proj2 (@lem1771859 x h1)). Qed.
Lemma lem1771863 (x : real) (h1 : term1385 x) : term351.
Proof. exact (proj2 (@lem1771861 x h1)). Qed.
Lemma lem1771866 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771867 : term351 = False.
Proof. exact (@lem1771866 term333 (NUMERAL 0)). Qed.
Lemma lem1771868 (x : real) (h1 : term1385 x) : False.
Proof. exact (EQ_MP (@lem1771867) (@lem1771863 x h1)). Qed.
Lemma lem1771869 (x : real) (h1 : term1386 x) : term1386 x.
Proof. exact (h1). Qed.
Lemma lem1771870 (x : real) (h1 : term1386 x) : term1073 x.
Proof. exact (proj2 (@lem1771869 x h1)). Qed.
Lemma lem1771872 (x : real) (h1 : term1386 x) : term875 x.
Proof. exact (proj2 (@lem1771870 x h1)). Qed.
Lemma lem1771874 (x : real) (h1 : term1386 x) : term759 x.
Proof. exact (proj2 (@lem1771872 x h1)). Qed.
Lemma lem1771877 (x : real) (h1 : term1386 x) : term313.
Proof. exact (proj1 (@lem1771874 x h1)). Qed.
Lemma lem1771883 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771884 : term313 = False.
Proof. exact (@lem1771883 term277 (NUMERAL 0)). Qed.
Lemma lem1771885 (x : real) (h1 : term1386 x) : False.
Proof. exact (EQ_MP (@lem1771884) (@lem1771877 x h1)). Qed.
Lemma lem1771886 (x : real) (h1 : term1071 x) : False.
Proof. exact (or_elim (@lem1771851 x h1) (fun h0 : term1385 x => @lem1771868 x h0) (fun h0 : term1386 x => @lem1771885 x h0)). Qed.
Lemma lem1771887 (x : real) (h1 : term1067 x) : term1067 x.
Proof. exact (h1). Qed.
Lemma lem1771888 (x : real) (h1 : term1387 x) : term1387 x.
Proof. exact (h1). Qed.
Lemma lem1771889 (x : real) (h1 : term1387 x) : term1068 x.
Proof. exact (proj2 (@lem1771888 x h1)). Qed.
Lemma lem1771891 (x : real) (h1 : term1387 x) : term870 x.
Proof. exact (proj2 (@lem1771889 x h1)). Qed.
Lemma lem1771893 (x : real) (h1 : term1387 x) : term754 x.
Proof. exact (proj2 (@lem1771891 x h1)). Qed.
Lemma lem1771895 (x : real) (h1 : term1387 x) : term737 x.
Proof. exact (proj2 (@lem1771893 x h1)). Qed.
Lemma lem1771897 (x : real) (h1 : term1387 x) : term733.
Proof. exact (proj2 (@lem1771895 x h1)). Qed.
Lemma lem1771899 (x : real) (h1 : term1387 x) : term313.
Proof. exact (proj2 (@lem1771897 x h1)). Qed.
Lemma lem1771902 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771903 : term313 = False.
Proof. exact (@lem1771902 term277 (NUMERAL 0)). Qed.
Lemma lem1771904 (x : real) (h1 : term1387 x) : False.
Proof. exact (EQ_MP (@lem1771903) (@lem1771899 x h1)). Qed.
Lemma lem1771905 (x : real) (h1 : term1388 x) : term1388 x.
Proof. exact (h1). Qed.
Lemma lem1771906 (x : real) (h1 : term1388 x) : term1069 x.
Proof. exact (proj2 (@lem1771905 x h1)). Qed.
Lemma lem1771908 (x : real) (h1 : term1388 x) : term871 x.
Proof. exact (proj2 (@lem1771906 x h1)). Qed.
Lemma lem1771910 (x : real) (h1 : term1388 x) : term755 x.
Proof. exact (proj2 (@lem1771908 x h1)). Qed.
Lemma lem1771912 (x : real) (h1 : term1388 x) : term738 x.
Proof. exact (proj2 (@lem1771910 x h1)). Qed.
Lemma lem1771914 (x : real) (h1 : term1388 x) : term734.
Proof. exact (proj2 (@lem1771912 x h1)). Qed.
Lemma lem1771917 (x : real) (h1 : term1388 x) : term323.
Proof. exact (proj1 (@lem1771914 x h1)). Qed.
Lemma lem1771919 (m : nat) (n : nat) : (term1378 m n) = (term1379 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1771920 : term323 = term1380.
Proof. exact (@lem1771919 term277 (NUMERAL 0)). Qed.
Lemma lem1771921 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1771922 : term1381 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1771923 (h1 : term1381 = (BIT1 0)) : (term277 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1771924 : (term1381 = (BIT1 0)) = ((term277 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1381 = (BIT1 0) => @lem1771923 h1) (fun h1 : (term277 = (NUMERAL 0)) = False => @lem1771922)). Qed.
Lemma lem1771925 : (term277 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1771924) (@lem1771922)). Qed.
Lemma lem1771926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1771927 : term1382 = (and False).
Proof. exact (MK_COMB (@lem1771926) (@lem1771925)). Qed.
Lemma lem1771928 : term1380 = (False /\ True).
Proof. exact (MK_COMB (@lem1771927) (@lem1771921)). Qed.
Lemma lem1771930 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1771931 : term1380 = False.
Proof. exact (TRANS (@lem1771928) (@lem1771930)). Qed.
Lemma lem1771932 : term323 = False.
Proof. exact (TRANS (@lem1771920) (@lem1771931)). Qed.
Lemma lem1771933 (x : real) (h1 : term1388 x) : False.
Proof. exact (EQ_MP (@lem1771932) (@lem1771917 x h1)). Qed.
Lemma lem1771934 (x : real) (h1 : term1067 x) : False.
Proof. exact (or_elim (@lem1771887 x h1) (fun h0 : term1387 x => @lem1771904 x h0) (fun h0 : term1388 x => @lem1771933 x h0)). Qed.
Lemma lem1771935 (x : real) (h1 : term1076 x) : False.
Proof. exact (or_elim (@lem1771850 x h1) (fun h0 : term1071 x => @lem1771886 x h0) (fun h0 : term1067 x => @lem1771934 x h0)). Qed.
Lemma lem1771936 (x : real) (h1 : term1110 x) : False.
Proof. exact (or_elim (@lem1771687 x h1) (fun h0 : term1107 x => @lem1771849 x h0) (fun h0 : term1076 x => @lem1771935 x h0)). Qed.
Lemma lem1771937 (x : real) (h1 : term1061 x) : term1061 x.
Proof. exact (h1). Qed.
Lemma lem1771938 (x : real) (h1 : term1058 x) : term1058 x.
Proof. exact (h1). Qed.
Lemma lem1771939 (x : real) (h1 : term1055 x) : term1055 x.
Proof. exact (h1). Qed.
Lemma lem1771940 (x : real) (h1 : term1050 x) : term1050 x.
Proof. exact (h1). Qed.
Lemma lem1771941 (x : real) (h1 : term1389 x) : term1389 x.
Proof. exact (h1). Qed.
Lemma lem1771942 (x : real) (h1 : term1389 x) : term1051 x.
Proof. exact (proj2 (@lem1771941 x h1)). Qed.
Lemma lem1771944 (x : real) (h1 : term1389 x) : term920 x.
Proof. exact (proj2 (@lem1771942 x h1)). Qed.
Lemma lem1771946 (x : real) (h1 : term1389 x) : term758 x.
Proof. exact (proj2 (@lem1771944 x h1)). Qed.
Lemma lem1771948 (x : real) (h1 : term1389 x) : term746 x.
Proof. exact (proj2 (@lem1771946 x h1)). Qed.
Lemma lem1771950 (x : real) (h1 : term1389 x) : term742.
Proof. exact (proj2 (@lem1771948 x h1)). Qed.
Lemma lem1771952 (x : real) (h1 : term1389 x) : term351.
Proof. exact (proj2 (@lem1771950 x h1)). Qed.
Lemma lem1771955 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771956 : term351 = False.
Proof. exact (@lem1771955 term333 (NUMERAL 0)). Qed.
Lemma lem1771957 (x : real) (h1 : term1389 x) : False.
Proof. exact (EQ_MP (@lem1771956) (@lem1771952 x h1)). Qed.
Lemma lem1771958 (x : real) (h1 : term1390 x) : term1390 x.
Proof. exact (h1). Qed.
Lemma lem1771959 (x : real) (h1 : term1390 x) : term1052 x.
Proof. exact (proj2 (@lem1771958 x h1)). Qed.
Lemma lem1771961 (x : real) (h1 : term1390 x) : term921 x.
Proof. exact (proj2 (@lem1771959 x h1)). Qed.
Lemma lem1771963 (x : real) (h1 : term1390 x) : term759 x.
Proof. exact (proj2 (@lem1771961 x h1)). Qed.
Lemma lem1771966 (x : real) (h1 : term1390 x) : term313.
Proof. exact (proj1 (@lem1771963 x h1)). Qed.
Lemma lem1771972 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771973 : term313 = False.
Proof. exact (@lem1771972 term277 (NUMERAL 0)). Qed.
Lemma lem1771974 (x : real) (h1 : term1390 x) : False.
Proof. exact (EQ_MP (@lem1771973) (@lem1771966 x h1)). Qed.
Lemma lem1771975 (x : real) (h1 : term1050 x) : False.
Proof. exact (or_elim (@lem1771940 x h1) (fun h0 : term1389 x => @lem1771957 x h0) (fun h0 : term1390 x => @lem1771974 x h0)). Qed.
Lemma lem1771976 (x : real) (h1 : term1048 x) : term1048 x.
Proof. exact (h1). Qed.
Lemma lem1771977 (x : real) (h1 : term1043 x) : term1043 x.
Proof. exact (h1). Qed.
Lemma lem1771978 (x : real) (h1 : term1391 x) : term1391 x.
Proof. exact (h1). Qed.
Lemma lem1771979 (x : real) (h1 : term1391 x) : term1044 x.
Proof. exact (proj2 (@lem1771978 x h1)). Qed.
Lemma lem1771981 (x : real) (h1 : term1391 x) : term913 x.
Proof. exact (proj2 (@lem1771979 x h1)). Qed.
Lemma lem1771983 (x : real) (h1 : term1391 x) : term849 x.
Proof. exact (proj2 (@lem1771981 x h1)). Qed.
Lemma lem1771985 (x : real) (h1 : term1391 x) : term792 x.
Proof. exact (proj2 (@lem1771983 x h1)). Qed.
Lemma lem1771987 (x : real) (h1 : term1391 x) : term775.
Proof. exact (proj2 (@lem1771985 x h1)). Qed.
Lemma lem1771990 (x : real) (h1 : term1391 x) : term313.
Proof. exact (proj1 (@lem1771987 x h1)). Qed.
Lemma lem1771992 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1771993 : term313 = False.
Proof. exact (@lem1771992 term277 (NUMERAL 0)). Qed.
Lemma lem1771994 (x : real) (h1 : term1391 x) : False.
Proof. exact (EQ_MP (@lem1771993) (@lem1771990 x h1)). Qed.
Lemma lem1771995 (x : real) (h1 : term1392 x) : term1392 x.
Proof. exact (h1). Qed.
Lemma lem1771996 (x : real) (h1 : term1392 x) : term1045 x.
Proof. exact (proj2 (@lem1771995 x h1)). Qed.
Lemma lem1771998 (x : real) (h1 : term1392 x) : term914 x.
Proof. exact (proj2 (@lem1771996 x h1)). Qed.
Lemma lem1772000 (x : real) (h1 : term1392 x) : term850 x.
Proof. exact (proj2 (@lem1771998 x h1)). Qed.
Lemma lem1772002 (x : real) (h1 : term1392 x) : term793 x.
Proof. exact (proj2 (@lem1772000 x h1)). Qed.
Lemma lem1772004 (x : real) (h1 : term1392 x) : term776.
Proof. exact (proj2 (@lem1772002 x h1)). Qed.
Lemma lem1772006 (x : real) (h1 : term1392 x) : term351.
Proof. exact (proj2 (@lem1772004 x h1)). Qed.
Lemma lem1772009 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772010 : term351 = False.
Proof. exact (@lem1772009 term333 (NUMERAL 0)). Qed.
Lemma lem1772011 (x : real) (h1 : term1392 x) : False.
Proof. exact (EQ_MP (@lem1772010) (@lem1772006 x h1)). Qed.
Lemma lem1772012 (x : real) (h1 : term1043 x) : False.
Proof. exact (or_elim (@lem1771977 x h1) (fun h0 : term1391 x => @lem1771994 x h0) (fun h0 : term1392 x => @lem1772011 x h0)). Qed.
Lemma lem1772013 (x : real) (h1 : term1039 x) : term1039 x.
Proof. exact (h1). Qed.
Lemma lem1772014 (x : real) (h1 : term1393 x) : term1393 x.
Proof. exact (h1). Qed.
Lemma lem1772015 (x : real) (h1 : term1393 x) : term1040 x.
Proof. exact (proj2 (@lem1772014 x h1)). Qed.
Lemma lem1772017 (x : real) (h1 : term1393 x) : term909 x.
Proof. exact (proj2 (@lem1772015 x h1)). Qed.
Lemma lem1772019 (x : real) (h1 : term1393 x) : term845 x.
Proof. exact (proj2 (@lem1772017 x h1)). Qed.
Lemma lem1772022 (x : real) (h1 : term1393 x) : term313.
Proof. exact (proj1 (@lem1772019 x h1)). Qed.
Lemma lem1772028 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772029 : term313 = False.
Proof. exact (@lem1772028 term277 (NUMERAL 0)). Qed.
Lemma lem1772030 (x : real) (h1 : term1393 x) : False.
Proof. exact (EQ_MP (@lem1772029) (@lem1772022 x h1)). Qed.
Lemma lem1772031 (x : real) (h1 : term1394 x) : term1394 x.
Proof. exact (h1). Qed.
Lemma lem1772032 (x : real) (h1 : term1394 x) : term1041 x.
Proof. exact (proj2 (@lem1772031 x h1)). Qed.
Lemma lem1772034 (x : real) (h1 : term1394 x) : term910 x.
Proof. exact (proj2 (@lem1772032 x h1)). Qed.
Lemma lem1772036 (x : real) (h1 : term1394 x) : term846 x.
Proof. exact (proj2 (@lem1772034 x h1)). Qed.
Lemma lem1772038 (x : real) (h1 : term1394 x) : term789 x.
Proof. exact (proj2 (@lem1772036 x h1)). Qed.
Lemma lem1772040 (x : real) (h1 : term1394 x) : term772.
Proof. exact (proj2 (@lem1772038 x h1)). Qed.
Lemma lem1772042 (x : real) (h1 : term1394 x) : term313.
Proof. exact (proj2 (@lem1772040 x h1)). Qed.
Lemma lem1772045 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772046 : term313 = False.
Proof. exact (@lem1772045 term277 (NUMERAL 0)). Qed.
Lemma lem1772047 (x : real) (h1 : term1394 x) : False.
Proof. exact (EQ_MP (@lem1772046) (@lem1772042 x h1)). Qed.
Lemma lem1772048 (x : real) (h1 : term1039 x) : False.
Proof. exact (or_elim (@lem1772013 x h1) (fun h0 : term1393 x => @lem1772030 x h0) (fun h0 : term1394 x => @lem1772047 x h0)). Qed.
Lemma lem1772049 (x : real) (h1 : term1048 x) : False.
Proof. exact (or_elim (@lem1771976 x h1) (fun h0 : term1043 x => @lem1772012 x h0) (fun h0 : term1039 x => @lem1772048 x h0)). Qed.
Lemma lem1772050 (x : real) (h1 : term1055 x) : False.
Proof. exact (or_elim (@lem1771939 x h1) (fun h0 : term1050 x => @lem1771975 x h0) (fun h0 : term1048 x => @lem1772049 x h0)). Qed.
Lemma lem1772051 (x : real) (h1 : term1033 x) : term1033 x.
Proof. exact (h1). Qed.
Lemma lem1772052 (x : real) (h1 : term1028 x) : term1028 x.
Proof. exact (h1). Qed.
Lemma lem1772053 (x : real) (h1 : term1395 x) : term1395 x.
Proof. exact (h1). Qed.
Lemma lem1772054 (x : real) (h1 : term1395 x) : term1029 x.
Proof. exact (proj2 (@lem1772053 x h1)). Qed.
Lemma lem1772056 (x : real) (h1 : term1395 x) : term898 x.
Proof. exact (proj2 (@lem1772054 x h1)). Qed.
Lemma lem1772058 (x : real) (h1 : term1395 x) : term754 x.
Proof. exact (proj2 (@lem1772056 x h1)). Qed.
Lemma lem1772060 (x : real) (h1 : term1395 x) : term737 x.
Proof. exact (proj2 (@lem1772058 x h1)). Qed.
Lemma lem1772062 (x : real) (h1 : term1395 x) : term733.
Proof. exact (proj2 (@lem1772060 x h1)). Qed.
Lemma lem1772064 (x : real) (h1 : term1395 x) : term313.
Proof. exact (proj2 (@lem1772062 x h1)). Qed.
Lemma lem1772067 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772068 : term313 = False.
Proof. exact (@lem1772067 term277 (NUMERAL 0)). Qed.
Lemma lem1772069 (x : real) (h1 : term1395 x) : False.
Proof. exact (EQ_MP (@lem1772068) (@lem1772064 x h1)). Qed.
Lemma lem1772070 (x : real) (h1 : term1396 x) : term1396 x.
Proof. exact (h1). Qed.
Lemma lem1772071 (x : real) (h1 : term1396 x) : term1030 x.
Proof. exact (proj2 (@lem1772070 x h1)). Qed.
Lemma lem1772073 (x : real) (h1 : term1396 x) : term899 x.
Proof. exact (proj2 (@lem1772071 x h1)). Qed.
Lemma lem1772075 (x : real) (h1 : term1396 x) : term755 x.
Proof. exact (proj2 (@lem1772073 x h1)). Qed.
Lemma lem1772077 (x : real) (h1 : term1396 x) : term738 x.
Proof. exact (proj2 (@lem1772075 x h1)). Qed.
Lemma lem1772079 (x : real) (h1 : term1396 x) : term734.
Proof. exact (proj2 (@lem1772077 x h1)). Qed.
Lemma lem1772082 (x : real) (h1 : term1396 x) : term323.
Proof. exact (proj1 (@lem1772079 x h1)). Qed.
Lemma lem1772084 (m : nat) (n : nat) : (term1378 m n) = (term1379 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1772085 : term323 = term1380.
Proof. exact (@lem1772084 term277 (NUMERAL 0)). Qed.
Lemma lem1772086 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1772087 : term1381 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1772088 (h1 : term1381 = (BIT1 0)) : (term277 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1772089 : (term1381 = (BIT1 0)) = ((term277 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1381 = (BIT1 0) => @lem1772088 h1) (fun h1 : (term277 = (NUMERAL 0)) = False => @lem1772087)). Qed.
Lemma lem1772090 : (term277 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1772089) (@lem1772087)). Qed.
Lemma lem1772091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1772092 : term1382 = (and False).
Proof. exact (MK_COMB (@lem1772091) (@lem1772090)). Qed.
Lemma lem1772093 : term1380 = (False /\ True).
Proof. exact (MK_COMB (@lem1772092) (@lem1772086)). Qed.
Lemma lem1772095 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1772096 : term1380 = False.
Proof. exact (TRANS (@lem1772093) (@lem1772095)). Qed.
Lemma lem1772097 : term323 = False.
Proof. exact (TRANS (@lem1772085) (@lem1772096)). Qed.
Lemma lem1772098 (x : real) (h1 : term1396 x) : False.
Proof. exact (EQ_MP (@lem1772097) (@lem1772082 x h1)). Qed.
Lemma lem1772099 (x : real) (h1 : term1028 x) : False.
Proof. exact (or_elim (@lem1772052 x h1) (fun h0 : term1395 x => @lem1772069 x h0) (fun h0 : term1396 x => @lem1772098 x h0)). Qed.
Lemma lem1772100 (x : real) (h1 : term1026 x) : term1026 x.
Proof. exact (h1). Qed.
Lemma lem1772101 (x : real) (h1 : term1021 x) : term1021 x.
Proof. exact (h1). Qed.
Lemma lem1772102 (x : real) (h1 : term1397 x) : term1397 x.
Proof. exact (h1). Qed.
Lemma lem1772103 (x : real) (h1 : term1397 x) : term1022 x.
Proof. exact (proj2 (@lem1772102 x h1)). Qed.
Lemma lem1772105 (x : real) (h1 : term1397 x) : term891 x.
Proof. exact (proj2 (@lem1772103 x h1)). Qed.
Lemma lem1772107 (x : real) (h1 : term1397 x) : term829 x.
Proof. exact (proj2 (@lem1772105 x h1)). Qed.
Lemma lem1772109 (x : real) (h1 : term1397 x) : term792 x.
Proof. exact (proj2 (@lem1772107 x h1)). Qed.
Lemma lem1772111 (x : real) (h1 : term1397 x) : term775.
Proof. exact (proj2 (@lem1772109 x h1)). Qed.
Lemma lem1772114 (x : real) (h1 : term1397 x) : term313.
Proof. exact (proj1 (@lem1772111 x h1)). Qed.
Lemma lem1772116 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772117 : term313 = False.
Proof. exact (@lem1772116 term277 (NUMERAL 0)). Qed.
Lemma lem1772118 (x : real) (h1 : term1397 x) : False.
Proof. exact (EQ_MP (@lem1772117) (@lem1772114 x h1)). Qed.
Lemma lem1772119 (x : real) (h1 : term1398 x) : term1398 x.
Proof. exact (h1). Qed.
Lemma lem1772120 (x : real) (h1 : term1398 x) : term1023 x.
Proof. exact (proj2 (@lem1772119 x h1)). Qed.
Lemma lem1772122 (x : real) (h1 : term1398 x) : term892 x.
Proof. exact (proj2 (@lem1772120 x h1)). Qed.
Lemma lem1772124 (x : real) (h1 : term1398 x) : term830 x.
Proof. exact (proj2 (@lem1772122 x h1)). Qed.
Lemma lem1772126 (x : real) (h1 : term1398 x) : term793 x.
Proof. exact (proj2 (@lem1772124 x h1)). Qed.
Lemma lem1772128 (x : real) (h1 : term1398 x) : term776.
Proof. exact (proj2 (@lem1772126 x h1)). Qed.
Lemma lem1772130 (x : real) (h1 : term1398 x) : term351.
Proof. exact (proj2 (@lem1772128 x h1)). Qed.
Lemma lem1772133 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772134 : term351 = False.
Proof. exact (@lem1772133 term333 (NUMERAL 0)). Qed.
Lemma lem1772135 (x : real) (h1 : term1398 x) : False.
Proof. exact (EQ_MP (@lem1772134) (@lem1772130 x h1)). Qed.
Lemma lem1772136 (x : real) (h1 : term1021 x) : False.
Proof. exact (or_elim (@lem1772101 x h1) (fun h0 : term1397 x => @lem1772118 x h0) (fun h0 : term1398 x => @lem1772135 x h0)). Qed.
Lemma lem1772137 (x : real) (h1 : term1017 x) : term1017 x.
Proof. exact (h1). Qed.
Lemma lem1772138 (x : real) (h1 : term1399 x) : term1399 x.
Proof. exact (h1). Qed.
Lemma lem1772139 (x : real) (h1 : term1399 x) : term1018 x.
Proof. exact (proj2 (@lem1772138 x h1)). Qed.
Lemma lem1772142 (x : real) (h1 : term1399 x) : term323.
Proof. exact (proj1 (@lem1772139 x h1)). Qed.
Lemma lem1772152 (m : nat) (n : nat) : (term1378 m n) = (term1379 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1772153 : term323 = term1380.
Proof. exact (@lem1772152 term277 (NUMERAL 0)). Qed.
Lemma lem1772154 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1772155 : term1381 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1772156 (h1 : term1381 = (BIT1 0)) : (term277 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1772157 : (term1381 = (BIT1 0)) = ((term277 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1381 = (BIT1 0) => @lem1772156 h1) (fun h1 : (term277 = (NUMERAL 0)) = False => @lem1772155)). Qed.
Lemma lem1772158 : (term277 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1772157) (@lem1772155)). Qed.
Lemma lem1772159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1772160 : term1382 = (and False).
Proof. exact (MK_COMB (@lem1772159) (@lem1772158)). Qed.
Lemma lem1772161 : term1380 = (False /\ True).
Proof. exact (MK_COMB (@lem1772160) (@lem1772154)). Qed.
Lemma lem1772163 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1772164 : term1380 = False.
Proof. exact (TRANS (@lem1772161) (@lem1772163)). Qed.
Lemma lem1772165 : term323 = False.
Proof. exact (TRANS (@lem1772153) (@lem1772164)). Qed.
Lemma lem1772166 (x : real) (h1 : term1399 x) : False.
Proof. exact (EQ_MP (@lem1772165) (@lem1772142 x h1)). Qed.
Lemma lem1772167 (x : real) (h1 : term1400 x) : term1400 x.
Proof. exact (h1). Qed.
Lemma lem1772168 (x : real) (h1 : term1400 x) : term1019 x.
Proof. exact (proj2 (@lem1772167 x h1)). Qed.
Lemma lem1772170 (x : real) (h1 : term1400 x) : term888 x.
Proof. exact (proj2 (@lem1772168 x h1)). Qed.
Lemma lem1772172 (x : real) (h1 : term1400 x) : term826 x.
Proof. exact (proj2 (@lem1772170 x h1)). Qed.
Lemma lem1772174 (x : real) (h1 : term1400 x) : term789 x.
Proof. exact (proj2 (@lem1772172 x h1)). Qed.
Lemma lem1772176 (x : real) (h1 : term1400 x) : term772.
Proof. exact (proj2 (@lem1772174 x h1)). Qed.
Lemma lem1772178 (x : real) (h1 : term1400 x) : term313.
Proof. exact (proj2 (@lem1772176 x h1)). Qed.
Lemma lem1772181 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772182 : term313 = False.
Proof. exact (@lem1772181 term277 (NUMERAL 0)). Qed.
Lemma lem1772183 (x : real) (h1 : term1400 x) : False.
Proof. exact (EQ_MP (@lem1772182) (@lem1772178 x h1)). Qed.
Lemma lem1772184 (x : real) (h1 : term1017 x) : False.
Proof. exact (or_elim (@lem1772137 x h1) (fun h0 : term1399 x => @lem1772166 x h0) (fun h0 : term1400 x => @lem1772183 x h0)). Qed.
Lemma lem1772185 (x : real) (h1 : term1026 x) : False.
Proof. exact (or_elim (@lem1772100 x h1) (fun h0 : term1021 x => @lem1772136 x h0) (fun h0 : term1017 x => @lem1772184 x h0)). Qed.
Lemma lem1772186 (x : real) (h1 : term1033 x) : False.
Proof. exact (or_elim (@lem1772051 x h1) (fun h0 : term1028 x => @lem1772099 x h0) (fun h0 : term1026 x => @lem1772185 x h0)). Qed.
Lemma lem1772187 (x : real) (h1 : term1058 x) : False.
Proof. exact (or_elim (@lem1771938 x h1) (fun h0 : term1055 x => @lem1772050 x h0) (fun h0 : term1033 x => @lem1772186 x h0)). Qed.
Lemma lem1772188 (x : real) (h1 : term1009 x) : term1009 x.
Proof. exact (h1). Qed.
Lemma lem1772189 (x : real) (h1 : term1004 x) : term1004 x.
Proof. exact (h1). Qed.
Lemma lem1772190 (x : real) (h1 : term1401 x) : term1401 x.
Proof. exact (h1). Qed.
Lemma lem1772191 (x : real) (h1 : term1401 x) : term1005 x.
Proof. exact (proj2 (@lem1772190 x h1)). Qed.
Lemma lem1772193 (x : real) (h1 : term1401 x) : term874 x.
Proof. exact (proj2 (@lem1772191 x h1)). Qed.
Lemma lem1772195 (x : real) (h1 : term1401 x) : term758 x.
Proof. exact (proj2 (@lem1772193 x h1)). Qed.
Lemma lem1772197 (x : real) (h1 : term1401 x) : term746 x.
Proof. exact (proj2 (@lem1772195 x h1)). Qed.
Lemma lem1772199 (x : real) (h1 : term1401 x) : term742.
Proof. exact (proj2 (@lem1772197 x h1)). Qed.
Lemma lem1772201 (x : real) (h1 : term1401 x) : term351.
Proof. exact (proj2 (@lem1772199 x h1)). Qed.
Lemma lem1772204 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772205 : term351 = False.
Proof. exact (@lem1772204 term333 (NUMERAL 0)). Qed.
Lemma lem1772206 (x : real) (h1 : term1401 x) : False.
Proof. exact (EQ_MP (@lem1772205) (@lem1772201 x h1)). Qed.
Lemma lem1772207 (x : real) (h1 : term1402 x) : term1402 x.
Proof. exact (h1). Qed.
Lemma lem1772208 (x : real) (h1 : term1402 x) : term1006 x.
Proof. exact (proj2 (@lem1772207 x h1)). Qed.
Lemma lem1772210 (x : real) (h1 : term1402 x) : term875 x.
Proof. exact (proj2 (@lem1772208 x h1)). Qed.
Lemma lem1772212 (x : real) (h1 : term1402 x) : term759 x.
Proof. exact (proj2 (@lem1772210 x h1)). Qed.
Lemma lem1772215 (x : real) (h1 : term1402 x) : term313.
Proof. exact (proj1 (@lem1772212 x h1)). Qed.
Lemma lem1772221 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772222 : term313 = False.
Proof. exact (@lem1772221 term277 (NUMERAL 0)). Qed.
Lemma lem1772223 (x : real) (h1 : term1402 x) : False.
Proof. exact (EQ_MP (@lem1772222) (@lem1772215 x h1)). Qed.
Lemma lem1772224 (x : real) (h1 : term1004 x) : False.
Proof. exact (or_elim (@lem1772189 x h1) (fun h0 : term1401 x => @lem1772206 x h0) (fun h0 : term1402 x => @lem1772223 x h0)). Qed.
Lemma lem1772225 (x : real) (h1 : term1000 x) : term1000 x.
Proof. exact (h1). Qed.
Lemma lem1772226 (x : real) (h1 : term1403 x) : term1403 x.
Proof. exact (h1). Qed.
Lemma lem1772227 (x : real) (h1 : term1403 x) : term1001 x.
Proof. exact (proj2 (@lem1772226 x h1)). Qed.
Lemma lem1772229 (x : real) (h1 : term1403 x) : term870 x.
Proof. exact (proj2 (@lem1772227 x h1)). Qed.
Lemma lem1772231 (x : real) (h1 : term1403 x) : term754 x.
Proof. exact (proj2 (@lem1772229 x h1)). Qed.
Lemma lem1772233 (x : real) (h1 : term1403 x) : term737 x.
Proof. exact (proj2 (@lem1772231 x h1)). Qed.
Lemma lem1772235 (x : real) (h1 : term1403 x) : term733.
Proof. exact (proj2 (@lem1772233 x h1)). Qed.
Lemma lem1772237 (x : real) (h1 : term1403 x) : term313.
Proof. exact (proj2 (@lem1772235 x h1)). Qed.
Lemma lem1772240 (m : nat) (n : nat) : (term1334 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1772241 : term313 = False.
Proof. exact (@lem1772240 term277 (NUMERAL 0)). Qed.
Lemma lem1772242 (x : real) (h1 : term1403 x) : False.
Proof. exact (EQ_MP (@lem1772241) (@lem1772237 x h1)). Qed.
Lemma lem1772243 (x : real) (h1 : term1404 x) : term1404 x.
Proof. exact (h1). Qed.
Lemma lem1772244 (x : real) (h1 : term1404 x) : term1002 x.
Proof. exact (proj2 (@lem1772243 x h1)). Qed.
Lemma lem1772246 (x : real) (h1 : term1404 x) : term871 x.
Proof. exact (proj2 (@lem1772244 x h1)). Qed.
Lemma lem1772248 (x : real) (h1 : term1404 x) : term755 x.
Proof. exact (proj2 (@lem1772246 x h1)). Qed.
Lemma lem1772250 (x : real) (h1 : term1404 x) : term738 x.
Proof. exact (proj2 (@lem1772248 x h1)). Qed.
Lemma lem1772252 (x : real) (h1 : term1404 x) : term734.
Proof. exact (proj2 (@lem1772250 x h1)). Qed.
Lemma lem1772255 (x : real) (h1 : term1404 x) : term323.
Proof. exact (proj1 (@lem1772252 x h1)). Qed.
Lemma lem1772257 (m : nat) (n : nat) : (term1378 m n) = (term1379 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1772258 : term323 = term1380.
Proof. exact (@lem1772257 term277 (NUMERAL 0)). Qed.
Lemma lem1772259 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1772260 : term1381 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1772261 (h1 : term1381 = (BIT1 0)) : (term277 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1772262 : (term1381 = (BIT1 0)) = ((term277 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term1381 = (BIT1 0) => @lem1772261 h1) (fun h1 : (term277 = (NUMERAL 0)) = False => @lem1772260)). Qed.
Lemma lem1772263 : (term277 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1772262) (@lem1772260)). Qed.
Lemma lem1772264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1772265 : term1382 = (and False).
Proof. exact (MK_COMB (@lem1772264) (@lem1772263)). Qed.
Lemma lem1772266 : term1380 = (False /\ True).
Proof. exact (MK_COMB (@lem1772265) (@lem1772259)). Qed.
Lemma lem1772268 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1772269 : term1380 = False.
Proof. exact (TRANS (@lem1772266) (@lem1772268)). Qed.
Lemma lem1772270 : term323 = False.
Proof. exact (TRANS (@lem1772258) (@lem1772269)). Qed.
Lemma lem1772271 (x : real) (h1 : term1404 x) : False.
Proof. exact (EQ_MP (@lem1772270) (@lem1772255 x h1)). Qed.
Lemma lem1772272 (x : real) (h1 : term1000 x) : False.
Proof. exact (or_elim (@lem1772225 x h1) (fun h0 : term1403 x => @lem1772242 x h0) (fun h0 : term1404 x => @lem1772271 x h0)). Qed.
Lemma lem1772273 (x : real) (h1 : term1009 x) : False.
Proof. exact (or_elim (@lem1772188 x h1) (fun h0 : term1004 x => @lem1772224 x h0) (fun h0 : term1000 x => @lem1772272 x h0)). Qed.
Lemma lem1772274 (x : real) (h1 : term1061 x) : False.
Proof. exact (or_elim (@lem1771937 x h1) (fun h0 : term1058 x => @lem1772187 x h0) (fun h0 : term1009 x => @lem1772273 x h0)). Qed.
Lemma lem1772275 (x : real) (h1 : term1113 x) : False.
Proof. exact (or_elim (@lem1771686 x h1) (fun h0 : term1110 x => @lem1771936 x h0) (fun h0 : term1061 x => @lem1772274 x h0)). Qed.
Lemma lem1772276 (x : real) (h1 : term1330 x) : False.
Proof. exact (or_elim (@lem1771005 x h1) (fun h0 : term1328 x => @lem1771685 x h0) (fun h0 : term1113 x => @lem1772275 x h0)). Qed.
Lemma lem1772278 (x : real) (h1 : term1330 x) : term1330 x.
Proof. exact (h1). Qed.
Lemma lem1772279 (x : real) (h1 : term1330 x) : (term1330 x) = False.
Proof. exact (prop_ext (fun h2 : term1330 x => @lem1772276 x h1) (fun h2 : False => @lem1772278 x h1)). Qed.
Lemma lem1772280 (x : real) (h1 : term1330 x) : False.
Proof. exact (EQ_MP (@lem1772279 x h1) (@lem1772278 x h1)). Qed.
Lemma lem1772281 (h1 : term1332) : term1332.
Proof. exact (h1). Qed.
Lemma lem1772282 (h1 : term1332) : False.
Proof. exact (ex_elim (@lem1772281 h1) (fun x : real => fun h0 : term1331 x => @lem1772280 x h0)). Qed.
Lemma lem1772283 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1772284 (h1 : term33) : term1332.
Proof. exact (EQ_MP (@lem1770623) (@lem1772283 h1)). Qed.
Lemma lem1772285 (h1 : term33) : term1332 = False.
Proof. exact (prop_ext (fun h2 : term1332 => @lem1772282 h2) (fun h2 : False => @lem1772284 h1)). Qed.
Lemma lem1772286 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem1772285 h1) (@lem1772284 h1)). Qed.
Lemma lem1772287 : term1405.
Proof. exact (fun h0 : term33 => @lem1772286 h0). Qed.
Lemma lem1772288 : term1406.
Proof. exact (@lem1386578 term30). Qed.
Lemma lem1772289 : term30.
Proof. exact (@lem1772288 (@lem1772287)). Qed.
Lemma lem1772290 : term29.
Proof. exact (EQ_MP (@lem1760095) (@lem1772289)). Qed.
