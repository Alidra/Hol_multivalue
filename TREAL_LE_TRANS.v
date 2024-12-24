Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_TRANS_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_LE_ADD2_spec.
Require Import HREAL_LE_ADD_LCANCEL_spec.
Require Import HREAL_LE_ADD_RCANCEL_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import treal_le_spec.
Lemma lem1330143 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1330144 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1330145 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1330144 x) (@lem1330143 x)). Qed.
Lemma lem1330146 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1330145 x y). Qed.
Lemma lem1330147 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1330149 (m : hreal) : term3 m.
Proof. exact (@lem1321659 m). Qed.
Lemma lem1330150 (m : hreal) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1330151 (m : hreal) : term4 m.
Proof. exact (EQ_MP (@lem1330150 m) (@lem1330149 m)). Qed.
Lemma lem1330152 (m : hreal) (n : hreal) : term5 m n.
Proof. exact (@lem1330151 m n). Qed.
Lemma lem1330153 (m : hreal) (n : hreal) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1330154 (m : hreal) (n : hreal) : term6 m n.
Proof. exact (EQ_MP (@lem1330153 m n) (@lem1330152 m n)). Qed.
Lemma lem1330155 (m : hreal) (n : hreal) (p : hreal) : term7 m n p.
Proof. exact (@lem1330154 m n p). Qed.
Lemma lem1330156 (p : hreal) (m : hreal) (n : hreal) : (term7 m n p) = ((term8 m n p) = (hreal_le m n)).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem1330158 (x : hreal) : term9 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1330159 (x : hreal) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1330160 (x : hreal) : term10 x.
Proof. exact (EQ_MP (@lem1330159 x) (@lem1330158 x)). Qed.
Lemma lem1330161 (x : hreal) (y : hreal) : term11 x y.
Proof. exact (@lem1330160 x y). Qed.
Lemma lem1330162 (x : hreal) (y : hreal) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1330163 (x : hreal) (y : hreal) : term12 x y.
Proof. exact (EQ_MP (@lem1330162 x y) (@lem1330161 x y)). Qed.
Lemma lem1330164 (x : hreal) (y : hreal) (z : hreal) : term13 x y z.
Proof. exact (@lem1330163 x y z). Qed.
Lemma lem1330165 (x : hreal) (y : hreal) (z : hreal) : (term13 x y z) = ((term14 x y z) = (term15 x y z)).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1330170 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term15 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (h1). Qed.
Lemma lem1330171 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term15 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (SYM (@lem1330170 x y z h1)). Qed.
Lemma lem1330172 (x : hreal) (y : hreal) (z : hreal) (h1 : (term15 x y z) = (term14 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (h1). Qed.
Lemma lem1330173 (x : hreal) (y : hreal) (z : hreal) (h1 : (term15 x y z) = (term14 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (SYM (@lem1330172 x y z h1)). Qed.
Lemma lem1330174 (x : hreal) (y : hreal) (z : hreal) : ((term14 x y z) = (term15 x y z)) = ((term15 x y z) = (term14 x y z)).
Proof. exact (prop_ext (fun h1 : (term14 x y z) = (term15 x y z) => @lem1330171 x y z h1) (fun h1 : (term15 x y z) = (term14 x y z) => @lem1330173 x y z h1)). Qed.
Lemma lem1330175 (x : hreal) (y : hreal) : (term16 x y) = (term17 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1330174 x y z)). Qed.
Lemma lem1330176 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330177 (x : hreal) (y : hreal) : (term12 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1330176) (@lem1330175 x y)). Qed.
Lemma lem1330178 (x : hreal) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : hreal => @lem1330177 x y)). Qed.
Lemma lem1330179 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330180 (x : hreal) : (term10 x) = (term21 x).
Proof. exact (MK_COMB (@lem1330179) (@lem1330178 x)). Qed.
Lemma lem1330181 : term22 = term23.
Proof. exact (fun_ext (fun x : hreal => @lem1330180 x)). Qed.
Lemma lem1330182 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330183 : term24 = term25.
Proof. exact (MK_COMB (@lem1330182) (@lem1330181)). Qed.
Lemma lem1330184 : term25.
Proof. exact (EQ_MP (@lem1330183) (@lem1320203)). Qed.
Lemma lem1330185 (m : hreal) : term26 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1330186 (m : hreal) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1330187 (m : hreal) : term27 m.
Proof. exact (EQ_MP (@lem1330186 m) (@lem1330185 m)). Qed.
Lemma lem1330188 (m : hreal) (n : hreal) : term28 m n.
Proof. exact (@lem1330187 m n). Qed.
Lemma lem1330189 (m : hreal) (n : hreal) : (term28 m n) = (term29 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem1330190 (m : hreal) (n : hreal) : term29 m n.
Proof. exact (EQ_MP (@lem1330189 m n) (@lem1330188 m n)). Qed.
Lemma lem1330191 (m : hreal) (n : hreal) (p : hreal) : term30 m n p.
Proof. exact (@lem1330190 m n p). Qed.
Lemma lem1330192 (m : hreal) (n : hreal) (p : hreal) : (term30 m n p) = ((term31 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem1330194 (x : hreal) : term32 x.
Proof. exact (@lem1330184 x). Qed.
Lemma lem1330195 (x : hreal) : (term32 x) = (term21 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1330196 (x : hreal) : term21 x.
Proof. exact (EQ_MP (@lem1330195 x) (@lem1330194 x)). Qed.
Lemma lem1330197 (x : hreal) (y : hreal) : term33 x y.
Proof. exact (@lem1330196 x y). Qed.
Lemma lem1330198 (x : hreal) (y : hreal) : (term33 x y) = (term18 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1330199 (x : hreal) (y : hreal) : term18 x y.
Proof. exact (EQ_MP (@lem1330198 x y) (@lem1330197 x y)). Qed.
Lemma lem1330200 (x : hreal) (y : hreal) (z : hreal) : term34 x y z.
Proof. exact (@lem1330199 x y z). Qed.
Lemma lem1330201 (x : hreal) (y : hreal) (z : hreal) : (term34 x y z) = ((term15 x y z) = (term14 x y z)).
Proof. exact (eq_refl (term34 x y z)). Qed.
Lemma lem1330203 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1330204 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1330205 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1330204 x) (@lem1330203 x)). Qed.
Lemma lem1330206 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1330205 x y). Qed.
Lemma lem1330207 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1330209 (a : hreal) : term35 a.
Proof. exact (@lem1322168 a). Qed.
Lemma lem1330210 (a : hreal) : (term35 a) = (term36 a).
Proof. exact (eq_refl (term35 a)). Qed.
Lemma lem1330211 (a : hreal) : term36 a.
Proof. exact (EQ_MP (@lem1330210 a) (@lem1330209 a)). Qed.
Lemma lem1330212 (a : hreal) (b : hreal) : term37 a b.
Proof. exact (@lem1330211 a b). Qed.
Lemma lem1330213 (a : hreal) (b : hreal) : (term37 a b) = (term38 a b).
Proof. exact (eq_refl (term37 a b)). Qed.
Lemma lem1330214 (a : hreal) (b : hreal) : term38 a b.
Proof. exact (EQ_MP (@lem1330213 a b) (@lem1330212 a b)). Qed.
Lemma lem1330215 (a : hreal) (b : hreal) (c : hreal) : term39 a b c.
Proof. exact (@lem1330214 a b c). Qed.
Lemma lem1330216 (a : hreal) (c : hreal) (b : hreal) : (term39 a b c) = (term40 a c b).
Proof. exact (eq_refl (term39 a b c)). Qed.
Lemma lem1330217 (a : hreal) (c : hreal) (b : hreal) : term40 a c b.
Proof. exact (EQ_MP (@lem1330216 a c b) (@lem1330215 a b c)). Qed.
Lemma lem1330218 (a : hreal) (c : hreal) (b : hreal) (d : hreal) : term41 a c b d.
Proof. exact (@lem1330217 a c b d). Qed.
Lemma lem1330219 (a : hreal) (c : hreal) (b : hreal) (d : hreal) : (term41 a c b d) = (term42 a c b d).
Proof. exact (eq_refl (term41 a c b d)). Qed.
Lemma lem1330221 (x1 : hreal) : term43 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1330222 (x1 : hreal) : (term43 x1) = (term44 x1).
Proof. exact (eq_refl (term43 x1)). Qed.
Lemma lem1330223 (x1 : hreal) : term44 x1.
Proof. exact (EQ_MP (@lem1330222 x1) (@lem1330221 x1)). Qed.
Lemma lem1330224 (x1 : hreal) (y2 : hreal) : term45 x1 y2.
Proof. exact (@lem1330223 x1 y2). Qed.
Lemma lem1330225 (x1 : hreal) (y2 : hreal) : (term45 x1 y2) = (term46 x1 y2).
Proof. exact (eq_refl (term45 x1 y2)). Qed.
Lemma lem1330226 (x1 : hreal) (y2 : hreal) : term46 x1 y2.
Proof. exact (EQ_MP (@lem1330225 x1 y2) (@lem1330224 x1 y2)). Qed.
Lemma lem1330227 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term47 x1 y2 x2.
Proof. exact (@lem1330226 x1 y2 x2). Qed.
Lemma lem1330228 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term47 x1 y2 x2) = (term48 x1 y2 x2).
Proof. exact (eq_refl (term47 x1 y2 x2)). Qed.
Lemma lem1330229 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term48 x1 y2 x2.
Proof. exact (EQ_MP (@lem1330228 x1 y2 x2) (@lem1330227 x1 y2 x2)). Qed.
Lemma lem1330230 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term49 x1 y2 x2 y1.
Proof. exact (@lem1330229 x1 y2 x2 y1). Qed.
Lemma lem1330231 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term49 x1 y2 x2 y1) = ((term50 x1 y1 x2 y2) = (term51 x1 y2 x2 y1)).
Proof. exact (eq_refl (term49 x1 y2 x2 y1)). Qed.
Lemma lem1330233 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term52 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1330234 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term52 _5106 _5107 P) = ((term53 _5106 _5107 P) = (term54 _5106 _5107 P)).
Proof. exact (eq_refl (term52 _5106 _5107 P)). Qed.
Lemma lem1330241 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term53 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330234 _5106 _5107 P) (@lem1330233 _5106 _5107 P)). Qed.
Lemma lem1330242 (P : type1233) : (term55 P) = (term56 P).
Proof. exact (@lem1330241 hreal hreal P). Qed.
Lemma lem1330243 : term57 = term58.
Proof. exact (@lem1330242 term59). Qed.
Lemma lem1330244 (x : prod hreal hreal) : (term60 x) = (term61 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1330245 : term62 = term59.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1330244 x)). Qed.
Lemma lem1330246 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330247 : term57 = term63.
Proof. exact (MK_COMB (@lem1330246) (@lem1330245)). Qed.
Lemma lem1330248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330249 : term64 = term65.
Proof. exact (MK_COMB (@lem1330248) (@lem1330247)). Qed.
Lemma lem1330250 (p1 : hreal) (p2 : hreal) : (term66 p1 p2) = (term67 p1 p2).
Proof. exact (eq_refl (term66 p1 p2)). Qed.
Lemma lem1330251 (p1 : hreal) : (term68 p1) = (term69 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330250 p1 p2)). Qed.
Lemma lem1330252 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330253 (p1 : hreal) : (term70 p1) = (term71 p1).
Proof. exact (MK_COMB (@lem1330252) (@lem1330251 p1)). Qed.
Lemma lem1330254 : term72 = term73.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330253 p1)). Qed.
Lemma lem1330255 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330256 : term58 = term74.
Proof. exact (MK_COMB (@lem1330255) (@lem1330254)). Qed.
Lemma lem1330257 : (term57 = term58) = (term63 = term74).
Proof. exact (MK_COMB (@lem1330249) (@lem1330256)). Qed.
Lemma lem1330258 : term63 = term74.
Proof. exact (EQ_MP (@lem1330257) (@lem1330243)). Qed.
Lemma lem1330276 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term53 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330234 _5106 _5107 P) (@lem1330233 _5106 _5107 P)). Qed.
Lemma lem1330277 (P : type1233) : (term55 P) = (term56 P).
Proof. exact (@lem1330276 hreal hreal P). Qed.
Lemma lem1330278 (p1 : hreal) (p2 : hreal) : (term75 p1 p2) = (term76 p1 p2).
Proof. exact (@lem1330277 (term77 p1 p2)). Qed.
Lemma lem1330279 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term78 p1 p2 y) = (term79 y p1 p2).
Proof. exact (eq_refl (term78 p1 p2 y)). Qed.
Lemma lem1330280 (p1 : hreal) (p2 : hreal) : (term80 p1 p2) = (term77 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1330279 y p1 p2)). Qed.
Lemma lem1330281 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330282 (p1 : hreal) (p2 : hreal) : (term75 p1 p2) = (term67 p1 p2).
Proof. exact (MK_COMB (@lem1330281) (@lem1330280 p1 p2)). Qed.
Lemma lem1330283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330284 (p1 : hreal) (p2 : hreal) : (term81 p1 p2) = (term82 p1 p2).
Proof. exact (MK_COMB (@lem1330283) (@lem1330282 p1 p2)). Qed.
Lemma lem1330285 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term83 p1 p2 p1' p2') = (term84 p1' p2' p1 p2).
Proof. exact (eq_refl (term83 p1 p2 p1' p2')). Qed.
Lemma lem1330286 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term85 p1 p2 p1') = (term86 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1330285 p1' p2' p1 p2)). Qed.
Lemma lem1330287 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330288 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term87 p1 p2 p1') = (term88 p1' p1 p2).
Proof. exact (MK_COMB (@lem1330287) (@lem1330286 p1' p1 p2)). Qed.
Lemma lem1330289 (p1 : hreal) (p2 : hreal) : (term89 p1 p2) = (term90 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330288 p1' p1 p2)). Qed.
Lemma lem1330290 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330291 (p1 : hreal) (p2 : hreal) : (term76 p1 p2) = (term91 p1 p2).
Proof. exact (MK_COMB (@lem1330290) (@lem1330289 p1 p2)). Qed.
Lemma lem1330292 (p1 : hreal) (p2 : hreal) : ((term75 p1 p2) = (term76 p1 p2)) = ((term67 p1 p2) = (term91 p1 p2)).
Proof. exact (MK_COMB (@lem1330284 p1 p2) (@lem1330291 p1 p2)). Qed.
Lemma lem1330293 (p1 : hreal) (p2 : hreal) : (term67 p1 p2) = (term91 p1 p2).
Proof. exact (EQ_MP (@lem1330292 p1 p2) (@lem1330278 p1 p2)). Qed.
Lemma lem1330311 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term53 _5106 _5107 P) = (term54 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330234 _5106 _5107 P) (@lem1330233 _5106 _5107 P)). Qed.
Lemma lem1330312 (P : type1233) : (term55 P) = (term56 P).
Proof. exact (@lem1330311 hreal hreal P). Qed.
Lemma lem1330313 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term92 p1' p2' p1 p2) = (term93 p1' p2' p1 p2).
Proof. exact (@lem1330312 (term94 p1' p2' p1 p2)). Qed.
Lemma lem1330314 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (z : prod hreal hreal) : (term95 p1' p2' p1 p2 z) = (term96 p1' p2' p1 p2 z).
Proof. exact (eq_refl (term95 p1' p2' p1 p2 z)). Qed.
Lemma lem1330315 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term97 p1' p2' p1 p2) = (term94 p1' p2' p1 p2).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1330314 p1' p2' p1 p2 z)). Qed.
Lemma lem1330316 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330317 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term92 p1' p2' p1 p2) = (term84 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330316) (@lem1330315 p1' p2' p1 p2)). Qed.
Lemma lem1330318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330319 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term98 p1' p2' p1 p2) = (term99 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330318) (@lem1330317 p1' p2' p1 p2)). Qed.
Lemma lem1330320 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term100 p1' p2' p1 p2 p1'' p2'') = (term101 p1' p2' p1 p2 p1'' p2'').
Proof. exact (eq_refl (term100 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1330321 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term102 p1' p2' p1 p2 p1'') = (term103 p1' p2' p1 p2 p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1330320 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1330322 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330323 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term104 p1' p2' p1 p2 p1'') = (term105 p1' p2' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1330322) (@lem1330321 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1330324 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term106 p1' p2' p1 p2) = (term107 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1330323 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1330325 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330326 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term93 p1' p2' p1 p2) = (term108 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330325) (@lem1330324 p1' p2' p1 p2)). Qed.
Lemma lem1330327 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term92 p1' p2' p1 p2) = (term93 p1' p2' p1 p2)) = ((term84 p1' p2' p1 p2) = (term108 p1' p2' p1 p2)).
Proof. exact (MK_COMB (@lem1330319 p1' p2' p1 p2) (@lem1330326 p1' p2' p1 p2)). Qed.
Lemma lem1330328 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term84 p1' p2' p1 p2) = (term108 p1' p2' p1 p2).
Proof. exact (EQ_MP (@lem1330327 p1' p2' p1 p2) (@lem1330313 p1' p2' p1 p2)). Qed.
Lemma lem1330346 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term50 x1 y1 x2 y2) = (term51 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330231 x1 y2 x2 y1) (@lem1330230 x1 y2 x2 y1)). Qed.
Lemma lem1330347 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term50 p1 p2 p1' p2') = (term51 p1 p2' p1' p2).
Proof. exact (@lem1330346 p1 p2' p1' p2). Qed.
Lemma lem1330348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1330349 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term109 p1 p2 p1' p2') = (term110 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1330348) (@lem1330347 p1 p2' p1' p2)). Qed.
Lemma lem1330351 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term50 x1 y1 x2 y2) = (term51 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330231 x1 y2 x2 y1) (@lem1330230 x1 y2 x2 y1)). Qed.
Lemma lem1330352 (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term50 p1' p2' p1'' p2'') = (term51 p1' p2'' p1'' p2').
Proof. exact (@lem1330351 p1' p2'' p1'' p2'). Qed.
Lemma lem1330353 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term111 p1 p2 p1' p2' p1'' p2'') = (term112 p1 p2 p1' p2'' p1'' p2').
Proof. exact (MK_COMB (@lem1330349 p1 p2' p1' p2) (@lem1330352 p1' p2'' p1'' p2')). Qed.
Lemma lem1330356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1330357 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term113 p1 p2 p1' p2' p1'' p2'') = (term114 p1 p2 p1' p2'' p1'' p2').
Proof. exact (MK_COMB (@lem1330356) (@lem1330353 p1 p2 p1' p2'' p1'' p2')). Qed.
Lemma lem1330359 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term50 x1 y1 x2 y2) = (term51 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330231 x1 y2 x2 y1) (@lem1330230 x1 y2 x2 y1)). Qed.
Lemma lem1330360 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term50 p1 p2 p1'' p2'') = (term51 p1 p2'' p1'' p2).
Proof. exact (@lem1330359 p1 p2'' p1'' p2). Qed.
Lemma lem1330361 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term101 p1' p2' p1 p2 p1'' p2'') = (term115 p1' p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1330357 p1 p2 p1' p2'' p1'' p2') (@lem1330360 p1 p2'' p1'' p2)). Qed.
Lemma lem1330364 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : (term103 p1' p2' p1 p2 p1'') = (term116 p1' p2' p1 p1'' p2).
Proof. exact (fun_ext (fun p2'' : hreal => @lem1330361 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330365 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330366 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : (term105 p1' p2' p1 p2 p1'') = (term117 p1' p2' p1 p1'' p2).
Proof. exact (MK_COMB (@lem1330365) (@lem1330364 p1' p2' p1 p1'' p2)). Qed.
Lemma lem1330373 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term107 p1' p2' p1 p2) = (term118 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1330366 p1' p2' p1 p1'' p2)). Qed.
Lemma lem1330374 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330375 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term108 p1' p2' p1 p2) = (term119 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330374) (@lem1330373 p1' p2' p1 p2)). Qed.
Lemma lem1330382 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term84 p1' p2' p1 p2) = (term119 p1' p2' p1 p2).
Proof. exact (TRANS (@lem1330328 p1' p2' p1 p2) (@lem1330375 p1' p2' p1 p2)). Qed.
Lemma lem1330383 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term86 p1' p1 p2) = (term120 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1330382 p1' p2' p1 p2)). Qed.
Lemma lem1330384 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330385 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term88 p1' p1 p2) = (term121 p1' p1 p2).
Proof. exact (MK_COMB (@lem1330384) (@lem1330383 p1' p1 p2)). Qed.
Lemma lem1330392 (p1 : hreal) (p2 : hreal) : (term90 p1 p2) = (term122 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330385 p1' p1 p2)). Qed.
Lemma lem1330393 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330394 (p1 : hreal) (p2 : hreal) : (term91 p1 p2) = (term123 p1 p2).
Proof. exact (MK_COMB (@lem1330393) (@lem1330392 p1 p2)). Qed.
Lemma lem1330401 (p1 : hreal) (p2 : hreal) : (term67 p1 p2) = (term123 p1 p2).
Proof. exact (TRANS (@lem1330293 p1 p2) (@lem1330394 p1 p2)). Qed.
Lemma lem1330402 (p1 : hreal) : (term69 p1) = (term124 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330401 p1 p2)). Qed.
Lemma lem1330403 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330404 (p1 : hreal) : (term71 p1) = (term125 p1).
Proof. exact (MK_COMB (@lem1330403) (@lem1330402 p1)). Qed.
Lemma lem1330411 : term73 = term126.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330404 p1)). Qed.
Lemma lem1330412 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330413 : term74 = term127.
Proof. exact (MK_COMB (@lem1330412) (@lem1330411)). Qed.
Lemma lem1330420 : term63 = term127.
Proof. exact (TRANS (@lem1330258) (@lem1330413)). Qed.
Lemma lem1330421 : term127 = term63.
Proof. exact (SYM (@lem1330420)). Qed.
Lemma lem1330422 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term112 p1 p2 p1' p2'' p1'' p2') : term112 p1 p2 p1' p2'' p1'' p2'.
Proof. exact (h1). Qed.
Lemma lem1330424 (a : hreal) (c : hreal) (b : hreal) (d : hreal) : term42 a c b d.
Proof. exact (EQ_MP (@lem1330219 a c b d) (@lem1330218 a c b d)). Qed.
Lemma lem1330425 (p1 : hreal) (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : term128 p1 p2'' p1' p2 p1'' p2'.
Proof. exact (@lem1330424 (hreal_add p1 p2') (hreal_add p1' p2'') (hreal_add p1' p2) (hreal_add p1'' p2')). Qed.
Lemma lem1330426 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term112 p1 p2 p1' p2'' p1'' p2') : term129 p1 p2'' p1' p2 p1'' p2'.
Proof. exact (@lem1330425 p1 p2'' p1' p2 p1'' p2' (@lem1330422 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1330428 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330207 y x) (@lem1330206 x y)). Qed.
Lemma lem1330429 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term130 p1 p2' p1' p2'') = (term130 p1' p2'' p1 p2').
Proof. exact (@lem1330428 (hreal_add p1' p2'') (hreal_add p1 p2')). Qed.
Lemma lem1330430 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1330431 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term131 p1 p2' p1' p2'') = (term131 p1' p2'' p1 p2').
Proof. exact (MK_COMB (@lem1330430) (@lem1330429 p1' p2'' p1 p2')). Qed.
Lemma lem1330432 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term130 p1' p2 p1'' p2') = (term130 p1' p2 p1'' p2').
Proof. exact (eq_refl (term130 p1' p2 p1'' p2')). Qed.
Lemma lem1330433 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term129 p1 p2'' p1' p2 p1'' p2') = (term132 p2'' p1 p1' p2 p1'' p2').
Proof. exact (MK_COMB (@lem1330431 p1' p2'' p1 p2') (@lem1330432 p1' p2 p1'' p2')). Qed.
Lemma lem1330434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1330435 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term133 p1 p2'' p1' p2 p1'' p2') = (term134 p2'' p1 p1' p2 p1'' p2').
Proof. exact (MK_COMB (@lem1330434) (@lem1330433 p2'' p1 p1' p2 p1'' p2')). Qed.
Lemma lem1330436 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term51 p1 p2'' p1'' p2) = (term51 p1 p2'' p1'' p2).
Proof. exact (eq_refl (term51 p1 p2'' p1'' p2)). Qed.
Lemma lem1330437 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term135 p1' p2' p1 p2'' p1'' p2) = (term136 p1' p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1330435 p2'' p1 p1' p2 p1'' p2') (@lem1330436 p1 p2'' p1'' p2)). Qed.
Lemma lem1330438 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term136 p1' p2' p1 p2'' p1'' p2) = (term135 p1' p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1330437 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330444 (x : hreal) (y : hreal) (z : hreal) : (term15 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1330201 x y z) (@lem1330200 x y z)). Qed.
Lemma lem1330445 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term130 p1' p2'' p1 p2') = (term137 p1' p2'' p1 p2').
Proof. exact (@lem1330444 p1' p2'' (hreal_add p1 p2')). Qed.
Lemma lem1330446 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1330447 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term131 p1' p2'' p1 p2') = (term138 p1' p2'' p1 p2').
Proof. exact (MK_COMB (@lem1330446) (@lem1330445 p1' p2'' p1 p2')). Qed.
Lemma lem1330449 (x : hreal) (y : hreal) (z : hreal) : (term15 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1330201 x y z) (@lem1330200 x y z)). Qed.
Lemma lem1330450 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term130 p1' p2 p1'' p2') = (term137 p1' p2 p1'' p2').
Proof. exact (@lem1330449 p1' p2 (hreal_add p1'' p2')). Qed.
Lemma lem1330451 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term132 p2'' p1 p1' p2 p1'' p2') = (term139 p2'' p1 p1' p2 p1'' p2').
Proof. exact (MK_COMB (@lem1330447 p1' p2'' p1 p2') (@lem1330450 p1' p2 p1'' p2')). Qed.
Lemma lem1330453 (m : hreal) (n : hreal) (p : hreal) : (term31 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1330192 m n p) (@lem1330191 m n p)). Qed.
Lemma lem1330454 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term139 p2'' p1 p1' p2 p1'' p2') = (term140 p2'' p1 p2 p1'' p2').
Proof. exact (@lem1330453 p1' (term14 p2'' p1 p2') (term14 p2 p1'' p2')). Qed.
Lemma lem1330457 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term132 p2'' p1 p1' p2 p1'' p2') = (term140 p2'' p1 p2 p1'' p2').
Proof. exact (TRANS (@lem1330451 p2'' p1 p1' p2 p1'' p2') (@lem1330454 p1' p2'' p1 p2 p1'' p2')). Qed.
Lemma lem1330458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1330459 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term134 p2'' p1 p1' p2 p1'' p2') = (term141 p2'' p1 p2 p1'' p2').
Proof. exact (MK_COMB (@lem1330458) (@lem1330457 p1' p2'' p1 p2 p1'' p2')). Qed.
Lemma lem1330462 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term51 p1 p2'' p1'' p2) = (term51 p1 p2'' p1'' p2).
Proof. exact (eq_refl (term51 p1 p2'' p1'' p2)). Qed.
Lemma lem1330463 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term136 p1' p2' p1 p2'' p1'' p2) = (term142 p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1330459 p1' p2'' p1 p2 p1'' p2') (@lem1330462 p1 p2'' p1'' p2)). Qed.
Lemma lem1330466 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term142 p2' p1 p2'' p1'' p2) = (term136 p1' p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1330463 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330472 (x : hreal) (y : hreal) (z : hreal) : (term14 x y z) = (term15 x y z).
Proof. exact (EQ_MP (@lem1330165 x y z) (@lem1330164 x y z)). Qed.
Lemma lem1330473 (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term14 p2'' p1 p2') = (term15 p2'' p1 p2').
Proof. exact (@lem1330472 p2'' p1 p2'). Qed.
Lemma lem1330474 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1330475 (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term143 p2'' p1 p2') = (term144 p2'' p1 p2').
Proof. exact (MK_COMB (@lem1330474) (@lem1330473 p2'' p1 p2')). Qed.
Lemma lem1330477 (x : hreal) (y : hreal) (z : hreal) : (term14 x y z) = (term15 x y z).
Proof. exact (EQ_MP (@lem1330165 x y z) (@lem1330164 x y z)). Qed.
Lemma lem1330478 (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term14 p2 p1'' p2') = (term15 p2 p1'' p2').
Proof. exact (@lem1330477 p2 p1'' p2'). Qed.
Lemma lem1330479 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term140 p2'' p1 p2 p1'' p2') = (term145 p2'' p1 p2 p1'' p2').
Proof. exact (MK_COMB (@lem1330475 p2'' p1 p2') (@lem1330478 p2 p1'' p2')). Qed.
Lemma lem1330481 (p : hreal) (m : hreal) (n : hreal) : (term8 m n p) = (hreal_le m n).
Proof. exact (EQ_MP (@lem1330156 p m n) (@lem1330155 m n p)). Qed.
Lemma lem1330482 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term145 p2'' p1 p2 p1'' p2') = (term51 p2'' p1 p2 p1'').
Proof. exact (@lem1330481 p2' (hreal_add p2'' p1) (hreal_add p2 p1'')). Qed.
Lemma lem1330485 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term140 p2'' p1 p2 p1'' p2') = (term51 p2'' p1 p2 p1'').
Proof. exact (TRANS (@lem1330479 p2'' p1 p2 p1'' p2') (@lem1330482 p2' p2'' p1 p2 p1'')). Qed.
Lemma lem1330486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1330487 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term141 p2'' p1 p2 p1'' p2') = (term146 p2'' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1330486) (@lem1330485 p2' p2'' p1 p2 p1'')). Qed.
Lemma lem1330490 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term51 p1 p2'' p1'' p2) = (term51 p1 p2'' p1'' p2).
Proof. exact (eq_refl (term51 p1 p2'' p1'' p2)). Qed.
Lemma lem1330491 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term142 p2' p1 p2'' p1'' p2) = (term147 p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1330487 p2' p2'' p1 p2 p1'') (@lem1330490 p1 p2'' p1'' p2)). Qed.
Lemma lem1330494 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term147 p1 p2'' p1'' p2) = (term142 p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1330491 p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330495 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (h1 : term51 p2'' p1 p2 p1'') : term51 p2'' p1 p2 p1''.
Proof. exact (h1). Qed.
Lemma lem1330497 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330147 y x) (@lem1330146 x y)). Qed.
Lemma lem1330498 (p1 : hreal) (p2'' : hreal) : (hreal_add p2'' p1) = (hreal_add p1 p2'').
Proof. exact (@lem1330497 p1 p2''). Qed.
Lemma lem1330499 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1330500 (p1 : hreal) (p2'' : hreal) : (term148 p2'' p1) = (term148 p1 p2'').
Proof. exact (MK_COMB (@lem1330499) (@lem1330498 p1 p2'')). Qed.
Lemma lem1330502 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330147 y x) (@lem1330146 x y)). Qed.
Lemma lem1330503 (p1'' : hreal) (p2 : hreal) : (hreal_add p2 p1'') = (hreal_add p1'' p2).
Proof. exact (@lem1330502 p1'' p2). Qed.
Lemma lem1330504 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term51 p2'' p1 p2 p1'') = (term51 p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1330500 p1 p2'') (@lem1330503 p1'' p2)). Qed.
Lemma lem1330507 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (h1 : term51 p2'' p1 p2 p1'') : term51 p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1330504 p1 p2'' p1'' p2) (@lem1330495 p2'' p1 p2 p1'' h1)). Qed.
Lemma lem1330508 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term147 p1 p2'' p1'' p2.
Proof. exact (fun h0 : term51 p2'' p1 p2 p1'' => @lem1330507 p2'' p1 p2 p1'' h0). Qed.
Lemma lem1330509 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term142 p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1330494 p2' p1 p2'' p1'' p2) (@lem1330508 p1 p2'' p1'' p2)). Qed.
Lemma lem1330510 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term136 p1' p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1330466 p1' p2' p1 p2'' p1'' p2) (@lem1330509 p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330511 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term135 p1' p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1330438 p1' p2' p1 p2'' p1'' p2) (@lem1330510 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1330512 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term112 p1 p2 p1' p2'' p1'' p2') : term51 p1 p2'' p1'' p2.
Proof. exact (@lem1330511 p1' p2' p1 p2'' p1'' p2 (@lem1330426 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1330513 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term115 p1' p2' p1 p2'' p1'' p2.
Proof. exact (fun h0 : term112 p1 p2 p1' p2'' p1'' p2' => @lem1330512 p1 p2 p1' p2'' p1'' p2' h0). Qed.
Lemma lem1330518 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : term117 p1' p2' p1 p1'' p2.
Proof. exact (fun p2'' : hreal => @lem1330513 p1' p2' p1 p2'' p1'' p2). Qed.
Lemma lem1330523 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : term119 p1' p2' p1 p2.
Proof. exact (fun p1'' : hreal => @lem1330518 p1' p2' p1 p1'' p2). Qed.
Lemma lem1330528 (p1' : hreal) (p1 : hreal) (p2 : hreal) : term121 p1' p1 p2.
Proof. exact (fun p2' : hreal => @lem1330523 p1' p2' p1 p2). Qed.
Lemma lem1330533 (p1 : hreal) (p2 : hreal) : term123 p1 p2.
Proof. exact (fun p1' : hreal => @lem1330528 p1' p1 p2). Qed.
Lemma lem1330538 (p1 : hreal) : term125 p1.
Proof. exact (fun p2 : hreal => @lem1330533 p1 p2). Qed.
Lemma lem1330543 : term127.
Proof. exact (fun p1 : hreal => @lem1330538 p1). Qed.
Lemma lem1330544 : term63.
Proof. exact (EQ_MP (@lem1330421) (@lem1330543)). Qed.
