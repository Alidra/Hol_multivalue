Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_LINV_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1320277_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_add_spec.
Require Import treal_eq_spec.
Require Import treal_neg_spec.
Require Import treal_of_num_spec.
Lemma lem1328161 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1328162 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1328163 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1328162 x) (@lem1328161 x)). Qed.
Lemma lem1328164 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1328163 x y). Qed.
Lemma lem1328165 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1328167 (n : hreal) : term3 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1328168 (n : hreal) : (term3 n) = ((term4 n) = n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1328170 (x : hreal) : term5 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1328171 (x : hreal) : (term5 x) = ((term6 x) = x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1328173 (n : nat) : term7 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1328174 (n : nat) : (term7 n) = ((treal_of_num n) = (term8 n)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1328176 (x1 : hreal) : term9 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1328177 (x1 : hreal) : (term9 x1) = (term10 x1).
Proof. exact (eq_refl (term9 x1)). Qed.
Lemma lem1328178 (x1 : hreal) : term10 x1.
Proof. exact (EQ_MP (@lem1328177 x1) (@lem1328176 x1)). Qed.
Lemma lem1328179 (x1 : hreal) (y2 : hreal) : term11 x1 y2.
Proof. exact (@lem1328178 x1 y2). Qed.
Lemma lem1328180 (x1 : hreal) (y2 : hreal) : (term11 x1 y2) = (term12 x1 y2).
Proof. exact (eq_refl (term11 x1 y2)). Qed.
Lemma lem1328181 (x1 : hreal) (y2 : hreal) : term12 x1 y2.
Proof. exact (EQ_MP (@lem1328180 x1 y2) (@lem1328179 x1 y2)). Qed.
Lemma lem1328182 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term13 x1 y2 x2.
Proof. exact (@lem1328181 x1 y2 x2). Qed.
Lemma lem1328183 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term13 x1 y2 x2) = (term14 x1 y2 x2).
Proof. exact (eq_refl (term13 x1 y2 x2)). Qed.
Lemma lem1328184 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term14 x1 y2 x2.
Proof. exact (EQ_MP (@lem1328183 x1 y2 x2) (@lem1328182 x1 y2 x2)). Qed.
Lemma lem1328185 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term15 x1 y2 x2 y1.
Proof. exact (@lem1328184 x1 y2 x2 y1). Qed.
Lemma lem1328186 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term15 x1 y2 x2 y1) = ((term16 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term15 x1 y2 x2 y1)). Qed.
Lemma lem1328188 (x1 : hreal) : term17 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1328189 (x1 : hreal) : (term17 x1) = (term18 x1).
Proof. exact (eq_refl (term17 x1)). Qed.
Lemma lem1328190 (x1 : hreal) : term18 x1.
Proof. exact (EQ_MP (@lem1328189 x1) (@lem1328188 x1)). Qed.
Lemma lem1328191 (x1 : hreal) (x2 : hreal) : term19 x1 x2.
Proof. exact (@lem1328190 x1 x2). Qed.
Lemma lem1328192 (x1 : hreal) (x2 : hreal) : (term19 x1 x2) = (term20 x1 x2).
Proof. exact (eq_refl (term19 x1 x2)). Qed.
Lemma lem1328193 (x1 : hreal) (x2 : hreal) : term20 x1 x2.
Proof. exact (EQ_MP (@lem1328192 x1 x2) (@lem1328191 x1 x2)). Qed.
Lemma lem1328194 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term21 x1 x2 y1.
Proof. exact (@lem1328193 x1 x2 y1). Qed.
Lemma lem1328195 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term21 x1 x2 y1) = (term22 x1 x2 y1).
Proof. exact (eq_refl (term21 x1 x2 y1)). Qed.
Lemma lem1328196 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term22 x1 x2 y1.
Proof. exact (EQ_MP (@lem1328195 x1 x2 y1) (@lem1328194 x1 x2 y1)). Qed.
Lemma lem1328197 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term23 x1 x2 y1 y2.
Proof. exact (@lem1328196 x1 x2 y1 y2). Qed.
Lemma lem1328198 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term23 x1 x2 y1 y2) = ((term24 x1 y1 x2 y2) = (term25 x1 x2 y1 y2)).
Proof. exact (eq_refl (term23 x1 x2 y1 y2)). Qed.
Lemma lem1328200 (y : hreal) : term26 y.
Proof. exact (@lem1323246 y). Qed.
Lemma lem1328201 (y : hreal) : (term26 y) = (term27 y).
Proof. exact (eq_refl (term26 y)). Qed.
Lemma lem1328202 (y : hreal) : term27 y.
Proof. exact (EQ_MP (@lem1328201 y) (@lem1328200 y)). Qed.
Lemma lem1328203 (y : hreal) (x : hreal) : term28 y x.
Proof. exact (@lem1328202 y x). Qed.
Lemma lem1328204 (y : hreal) (x : hreal) : (term28 y x) = ((term29 x y) = (@pair hreal hreal y x)).
Proof. exact (eq_refl (term28 y x)). Qed.
Lemma lem1328206 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term30 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1328207 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term30 _5106 _5107 P) = ((term31 _5106 _5107 P) = (term32 _5106 _5107 P)).
Proof. exact (eq_refl (term30 _5106 _5107 P)). Qed.
Lemma lem1328214 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term31 _5106 _5107 P) = (term32 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1328207 _5106 _5107 P) (@lem1328206 _5106 _5107 P)). Qed.
Lemma lem1328215 (P : type1233) : (term33 P) = (term34 P).
Proof. exact (@lem1328214 hreal hreal P). Qed.
Lemma lem1328216 : term35 = term36.
Proof. exact (@lem1328215 term37). Qed.
Lemma lem1328217 (x : prod hreal hreal) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1328218 : term40 = term37.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1328217 x)). Qed.
Lemma lem1328219 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328220 : term35 = term41.
Proof. exact (MK_COMB (@lem1328219) (@lem1328218)). Qed.
Lemma lem1328221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1328222 : term42 = term43.
Proof. exact (MK_COMB (@lem1328221) (@lem1328220)). Qed.
Lemma lem1328223 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term45 p1 p2).
Proof. exact (eq_refl (term44 p1 p2)). Qed.
Lemma lem1328224 (p1 : hreal) : (term46 p1) = (term47 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1328223 p1 p2)). Qed.
Lemma lem1328225 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328226 (p1 : hreal) : (term48 p1) = (term49 p1).
Proof. exact (MK_COMB (@lem1328225) (@lem1328224 p1)). Qed.
Lemma lem1328227 : term50 = term51.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328226 p1)). Qed.
Lemma lem1328228 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328229 : term36 = term52.
Proof. exact (MK_COMB (@lem1328228) (@lem1328227)). Qed.
Lemma lem1328230 : (term35 = term36) = (term41 = term52).
Proof. exact (MK_COMB (@lem1328222) (@lem1328229)). Qed.
Lemma lem1328231 : term41 = term52.
Proof. exact (EQ_MP (@lem1328230) (@lem1328216)). Qed.
Lemma lem1328245 (y : hreal) (x : hreal) : (term29 x y) = (@pair hreal hreal y x).
Proof. exact (EQ_MP (@lem1328204 y x) (@lem1328203 y x)). Qed.
Lemma lem1328246 (p2 : hreal) (p1 : hreal) : (term29 p1 p2) = (@pair hreal hreal p2 p1).
Proof. exact (@lem1328245 p2 p1). Qed.
Lemma lem1328247 : treal_add = treal_add.
Proof. exact (eq_refl treal_add). Qed.
Lemma lem1328248 (p2 : hreal) (p1 : hreal) : (term53 p1 p2) = (term54 p2 p1).
Proof. exact (MK_COMB (@lem1328247) (@lem1328246 p2 p1)). Qed.
Lemma lem1328249 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1328250 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term56 p1 p2).
Proof. exact (MK_COMB (@lem1328248 p2 p1) (@lem1328249 p1 p2)). Qed.
Lemma lem1328252 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term24 x1 y1 x2 y2) = (term25 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1328198 x1 x2 y1 y2) (@lem1328197 x1 x2 y1 y2)). Qed.
Lemma lem1328253 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = (term57 p1 p2).
Proof. exact (@lem1328252 p2 p1 p1 p2). Qed.
Lemma lem1328255 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1328165 y x) (@lem1328164 x y)). Qed.
Lemma lem1328256 (p1 : hreal) (p2 : hreal) : (hreal_add p2 p1) = (hreal_add p1 p2).
Proof. exact (@lem1328255 p1 p2). Qed.
Lemma lem1328260 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1328261 (p1 : hreal) (p2 : hreal) : (term58 p2 p1) = (term58 p1 p2).
Proof. exact (MK_COMB (@lem1328260) (@lem1328256 p1 p2)). Qed.
Lemma lem1328265 (p1 : hreal) (p2 : hreal) : (hreal_add p1 p2) = (hreal_add p1 p2).
Proof. exact (eq_refl (hreal_add p1 p2)). Qed.
Lemma lem1328266 (p1 : hreal) (p2 : hreal) : (term57 p1 p2) = (term59 p1 p2).
Proof. exact (MK_COMB (@lem1328261 p1 p2) (@lem1328265 p1 p2)). Qed.
Lemma lem1328267 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = (term59 p1 p2).
Proof. exact (TRANS (@lem1328253 p1 p2) (@lem1328266 p1 p2)). Qed.
Lemma lem1328268 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term59 p1 p2).
Proof. exact (TRANS (@lem1328250 p1 p2) (@lem1328267 p1 p2)). Qed.
Lemma lem1328269 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1328270 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = (term61 p1 p2).
Proof. exact (MK_COMB (@lem1328269) (@lem1328268 p1 p2)). Qed.
Lemma lem1328272 (n : nat) : (treal_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem1328174 n) (@lem1328173 n)). Qed.
Lemma lem1328273 : term62 = term63.
Proof. exact (@lem1328272 (NUMERAL 0)). Qed.
Lemma lem1328274 (p1 : hreal) (p2 : hreal) : (term45 p1 p2) = (term64 p1 p2).
Proof. exact (MK_COMB (@lem1328270 p1 p2) (@lem1328273)). Qed.
Lemma lem1328276 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term16 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1328186 x1 y2 x2 y1) (@lem1328185 x1 y2 x2 y1)). Qed.
Lemma lem1328277 (p1 : hreal) (p2 : hreal) : (term64 p1 p2) = ((term65 p1 p2) = (term66 p1 p2)).
Proof. exact (@lem1328276 (hreal_add p1 p2) term67 term67 (hreal_add p1 p2)). Qed.
Lemma lem1328281 (n : hreal) : (term4 n) = n.
Proof. exact (EQ_MP (@lem1328168 n) (@lem1328167 n)). Qed.
Lemma lem1328282 (p1 : hreal) (p2 : hreal) : (term65 p1 p2) = (hreal_add p1 p2).
Proof. exact (@lem1328281 (hreal_add p1 p2)). Qed.
Lemma lem1328286 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1328287 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term69 p1 p2).
Proof. exact (MK_COMB (@lem1328286) (@lem1328282 p1 p2)). Qed.
Lemma lem1328289 (x : hreal) : (term6 x) = x.
Proof. exact (EQ_MP (@lem1328171 x) (@lem1328170 x)). Qed.
Lemma lem1328290 (p1 : hreal) (p2 : hreal) : (term66 p1 p2) = (hreal_add p1 p2).
Proof. exact (@lem1328289 (hreal_add p1 p2)). Qed.
Lemma lem1328294 (p1 : hreal) (p2 : hreal) : ((term65 p1 p2) = (term66 p1 p2)) = ((hreal_add p1 p2) = (hreal_add p1 p2)).
Proof. exact (MK_COMB (@lem1328287 p1 p2) (@lem1328290 p1 p2)). Qed.
Lemma lem1328296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1328297 (x : hreal) : (x = x) = True.
Proof. exact (@lem1328296 hreal x). Qed.
Lemma lem1328298 (p1 : hreal) (p2 : hreal) : ((hreal_add p1 p2) = (hreal_add p1 p2)) = True.
Proof. exact (@lem1328297 (hreal_add p1 p2)). Qed.
Lemma lem1328299 (p1 : hreal) (p2 : hreal) : ((term65 p1 p2) = (term66 p1 p2)) = True.
Proof. exact (TRANS (@lem1328294 p1 p2) (@lem1328298 p1 p2)). Qed.
Lemma lem1328300 (p1 : hreal) (p2 : hreal) : (term64 p1 p2) = True.
Proof. exact (TRANS (@lem1328277 p1 p2) (@lem1328299 p1 p2)). Qed.
Lemma lem1328301 (p1 : hreal) (p2 : hreal) : (term45 p1 p2) = True.
Proof. exact (TRANS (@lem1328274 p1 p2) (@lem1328300 p1 p2)). Qed.
Lemma lem1328302 (p1 : hreal) : (term47 p1) = term70.
Proof. exact (fun_ext (fun p2 : hreal => @lem1328301 p1 p2)). Qed.
Lemma lem1328303 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328304 (p1 : hreal) : (term49 p1) = term71.
Proof. exact (MK_COMB (@lem1328303) (@lem1328302 p1)). Qed.
Lemma lem1328306 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328307 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1328306 hreal t). Qed.
Lemma lem1328308 : term71 = True.
Proof. exact (@lem1328307 True). Qed.
Lemma lem1328309 (p1 : hreal) : (term49 p1) = True.
Proof. exact (TRANS (@lem1328304 p1) (@lem1328308)). Qed.
Lemma lem1328310 : term51 = term70.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328309 p1)). Qed.
Lemma lem1328311 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328312 : term52 = term71.
Proof. exact (MK_COMB (@lem1328311) (@lem1328310)). Qed.
Lemma lem1328314 {A : Type'} (t : Prop) : (term72 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328315 (t : Prop) : (term73 t) = t.
Proof. exact (@lem1328314 hreal t). Qed.
Lemma lem1328316 : term71 = True.
Proof. exact (@lem1328315 True). Qed.
Lemma lem1328317 : term52 = True.
Proof. exact (TRANS (@lem1328312) (@lem1328316)). Qed.
Lemma lem1328318 : term41 = True.
Proof. exact (TRANS (@lem1328231) (@lem1328317)). Qed.
Lemma lem1328319 : True = term41.
Proof. exact (SYM (@lem1328318)). Qed.
Lemma lem1328320 : term41.
Proof. exact (EQ_MP (@lem1328319) (@lem0)). Qed.
