Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_EQ_SYM_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Lemma lem1326194 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem1326195 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem1326196 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem1326195 A x) (@lem1326194 A x)). Qed.
Lemma lem1326197 {A : Type'} (x : A) (y : A) : term2 A x y.
Proof. exact (@lem1326196 A x y). Qed.
Lemma lem1326198 {A : Type'} (y : A) (x : A) : (term2 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem1326200 (x1 : hreal) : term3 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1326201 (x1 : hreal) : (term3 x1) = (term4 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1326202 (x1 : hreal) : term4 x1.
Proof. exact (EQ_MP (@lem1326201 x1) (@lem1326200 x1)). Qed.
Lemma lem1326203 (x1 : hreal) (y2 : hreal) : term5 x1 y2.
Proof. exact (@lem1326202 x1 y2). Qed.
Lemma lem1326204 (x1 : hreal) (y2 : hreal) : (term5 x1 y2) = (term6 x1 y2).
Proof. exact (eq_refl (term5 x1 y2)). Qed.
Lemma lem1326205 (x1 : hreal) (y2 : hreal) : term6 x1 y2.
Proof. exact (EQ_MP (@lem1326204 x1 y2) (@lem1326203 x1 y2)). Qed.
Lemma lem1326206 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term7 x1 y2 x2.
Proof. exact (@lem1326205 x1 y2 x2). Qed.
Lemma lem1326207 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term7 x1 y2 x2) = (term8 x1 y2 x2).
Proof. exact (eq_refl (term7 x1 y2 x2)). Qed.
Lemma lem1326208 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term8 x1 y2 x2.
Proof. exact (EQ_MP (@lem1326207 x1 y2 x2) (@lem1326206 x1 y2 x2)). Qed.
Lemma lem1326209 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term9 x1 y2 x2 y1.
Proof. exact (@lem1326208 x1 y2 x2 y1). Qed.
Lemma lem1326210 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y2 x2 y1) = ((term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term9 x1 y2 x2 y1)). Qed.
Lemma lem1326212 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term11 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1326213 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term11 _5106 _5107 P) = ((term12 _5106 _5107 P) = (term13 _5106 _5107 P)).
Proof. exact (eq_refl (term11 _5106 _5107 P)). Qed.
Lemma lem1326220 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term12 _5106 _5107 P) = (term13 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326213 _5106 _5107 P) (@lem1326212 _5106 _5107 P)). Qed.
Lemma lem1326221 (P : type1233) : (term14 P) = (term15 P).
Proof. exact (@lem1326220 hreal hreal P). Qed.
Lemma lem1326222 : term16 = term17.
Proof. exact (@lem1326221 term18). Qed.
Lemma lem1326223 (x : prod hreal hreal) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1326224 : term21 = term18.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1326223 x)). Qed.
Lemma lem1326225 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326226 : term16 = term22.
Proof. exact (MK_COMB (@lem1326225) (@lem1326224)). Qed.
Lemma lem1326227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326228 : term23 = term24.
Proof. exact (MK_COMB (@lem1326227) (@lem1326226)). Qed.
Lemma lem1326229 (p1 : hreal) (p2 : hreal) : (term25 p1 p2) = (term26 p1 p2).
Proof. exact (eq_refl (term25 p1 p2)). Qed.
Lemma lem1326230 (p1 : hreal) : (term27 p1) = (term28 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1326229 p1 p2)). Qed.
Lemma lem1326231 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326232 (p1 : hreal) : (term29 p1) = (term30 p1).
Proof. exact (MK_COMB (@lem1326231) (@lem1326230 p1)). Qed.
Lemma lem1326233 : term31 = term32.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326232 p1)). Qed.
Lemma lem1326234 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326235 : term17 = term33.
Proof. exact (MK_COMB (@lem1326234) (@lem1326233)). Qed.
Lemma lem1326236 : (term16 = term17) = (term22 = term33).
Proof. exact (MK_COMB (@lem1326228) (@lem1326235)). Qed.
Lemma lem1326237 : term22 = term33.
Proof. exact (EQ_MP (@lem1326236) (@lem1326222)). Qed.
Lemma lem1326255 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term12 _5106 _5107 P) = (term13 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326213 _5106 _5107 P) (@lem1326212 _5106 _5107 P)). Qed.
Lemma lem1326256 (P : type1233) : (term14 P) = (term15 P).
Proof. exact (@lem1326255 hreal hreal P). Qed.
Lemma lem1326257 (p1 : hreal) (p2 : hreal) : (term34 p1 p2) = (term35 p1 p2).
Proof. exact (@lem1326256 (term36 p1 p2)). Qed.
Lemma lem1326258 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term37 p1 p2 y) = ((term38 p1 p2 y) = (term39 y p1 p2)).
Proof. exact (eq_refl (term37 p1 p2 y)). Qed.
Lemma lem1326259 (p1 : hreal) (p2 : hreal) : (term40 p1 p2) = (term36 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1326258 y p1 p2)). Qed.
Lemma lem1326260 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326261 (p1 : hreal) (p2 : hreal) : (term34 p1 p2) = (term26 p1 p2).
Proof. exact (MK_COMB (@lem1326260) (@lem1326259 p1 p2)). Qed.
Lemma lem1326262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326263 (p1 : hreal) (p2 : hreal) : (term41 p1 p2) = (term42 p1 p2).
Proof. exact (MK_COMB (@lem1326262) (@lem1326261 p1 p2)). Qed.
Lemma lem1326264 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term43 p1 p2 p1' p2') = ((term10 p1 p2 p1' p2') = (term10 p1' p2' p1 p2)).
Proof. exact (eq_refl (term43 p1 p2 p1' p2')). Qed.
Lemma lem1326265 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term44 p1 p2 p1') = (term45 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1326264 p1' p2' p1 p2)). Qed.
Lemma lem1326266 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326267 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term46 p1 p2 p1') = (term47 p1' p1 p2).
Proof. exact (MK_COMB (@lem1326266) (@lem1326265 p1' p1 p2)). Qed.
Lemma lem1326268 (p1 : hreal) (p2 : hreal) : (term48 p1 p2) = (term49 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1326267 p1' p1 p2)). Qed.
Lemma lem1326269 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326270 (p1 : hreal) (p2 : hreal) : (term35 p1 p2) = (term50 p1 p2).
Proof. exact (MK_COMB (@lem1326269) (@lem1326268 p1 p2)). Qed.
Lemma lem1326271 (p1 : hreal) (p2 : hreal) : ((term34 p1 p2) = (term35 p1 p2)) = ((term26 p1 p2) = (term50 p1 p2)).
Proof. exact (MK_COMB (@lem1326263 p1 p2) (@lem1326270 p1 p2)). Qed.
Lemma lem1326272 (p1 : hreal) (p2 : hreal) : (term26 p1 p2) = (term50 p1 p2).
Proof. exact (EQ_MP (@lem1326271 p1 p2) (@lem1326257 p1 p2)). Qed.
Lemma lem1326292 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326210 x1 y2 x2 y1) (@lem1326209 x1 y2 x2 y1)). Qed.
Lemma lem1326293 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term10 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1326292 p1 p2' p1' p2). Qed.
Lemma lem1326300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326301 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term51 p1 p2 p1' p2') = (term52 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1326300) (@lem1326293 p1 p2' p1' p2)). Qed.
Lemma lem1326303 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326210 x1 y2 x2 y1) (@lem1326209 x1 y2 x2 y1)). Qed.
Lemma lem1326304 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term10 p1' p2' p1 p2) = ((hreal_add p1' p2) = (hreal_add p1 p2')).
Proof. exact (@lem1326303 p1' p2 p1 p2'). Qed.
Lemma lem1326308 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1326198 A y x) (@lem1326197 A x y)). Qed.
Lemma lem1326309 (y : hreal) (x : hreal) : (x = y) = (y = x).
Proof. exact (@lem1326308 hreal y x). Qed.
Lemma lem1326310 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : ((hreal_add p1' p2) = (hreal_add p1 p2')) = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1326309 (hreal_add p1 p2') (hreal_add p1' p2)). Qed.
Lemma lem1326317 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term10 p1' p2' p1 p2) = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (TRANS (@lem1326304 p1' p2 p1 p2') (@lem1326310 p1 p2' p1' p2)). Qed.
Lemma lem1326318 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : ((term10 p1 p2 p1' p2') = (term10 p1' p2' p1 p2)) = (((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p1 p2') = (hreal_add p1' p2))).
Proof. exact (MK_COMB (@lem1326301 p1 p2' p1' p2) (@lem1326317 p1 p2' p1' p2)). Qed.
Lemma lem1326320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1326321 (x : Prop) : (x = x) = True.
Proof. exact (@lem1326320 Prop x). Qed.
Lemma lem1326322 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p1 p2') = (hreal_add p1' p2))) = True.
Proof. exact (@lem1326321 ((hreal_add p1 p2') = (hreal_add p1' p2))). Qed.
Lemma lem1326323 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term10 p1 p2 p1' p2') = (term10 p1' p2' p1 p2)) = True.
Proof. exact (TRANS (@lem1326318 p1 p2' p1' p2) (@lem1326322 p1 p2' p1' p2)). Qed.
Lemma lem1326324 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term45 p1' p1 p2) = term53.
Proof. exact (fun_ext (fun p2' : hreal => @lem1326323 p1' p2' p1 p2)). Qed.
Lemma lem1326325 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326326 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term47 p1' p1 p2) = term54.
Proof. exact (MK_COMB (@lem1326325) (@lem1326324 p1' p1 p2)). Qed.
Lemma lem1326328 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326329 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1326328 hreal t). Qed.
Lemma lem1326330 : term54 = True.
Proof. exact (@lem1326329 True). Qed.
Lemma lem1326331 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term47 p1' p1 p2) = True.
Proof. exact (TRANS (@lem1326326 p1' p1 p2) (@lem1326330)). Qed.
Lemma lem1326332 (p1 : hreal) (p2 : hreal) : (term49 p1 p2) = term53.
Proof. exact (fun_ext (fun p1' : hreal => @lem1326331 p1' p1 p2)). Qed.
Lemma lem1326333 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326334 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = term54.
Proof. exact (MK_COMB (@lem1326333) (@lem1326332 p1 p2)). Qed.
Lemma lem1326336 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326337 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1326336 hreal t). Qed.
Lemma lem1326338 : term54 = True.
Proof. exact (@lem1326337 True). Qed.
Lemma lem1326339 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = True.
Proof. exact (TRANS (@lem1326334 p1 p2) (@lem1326338)). Qed.
Lemma lem1326340 (p1 : hreal) (p2 : hreal) : (term26 p1 p2) = True.
Proof. exact (TRANS (@lem1326272 p1 p2) (@lem1326339 p1 p2)). Qed.
Lemma lem1326341 (p1 : hreal) : (term28 p1) = term53.
Proof. exact (fun_ext (fun p2 : hreal => @lem1326340 p1 p2)). Qed.
Lemma lem1326342 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326343 (p1 : hreal) : (term30 p1) = term54.
Proof. exact (MK_COMB (@lem1326342) (@lem1326341 p1)). Qed.
Lemma lem1326345 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326346 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1326345 hreal t). Qed.
Lemma lem1326347 : term54 = True.
Proof. exact (@lem1326346 True). Qed.
Lemma lem1326348 (p1 : hreal) : (term30 p1) = True.
Proof. exact (TRANS (@lem1326343 p1) (@lem1326347)). Qed.
Lemma lem1326349 : term32 = term53.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326348 p1)). Qed.
Lemma lem1326350 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326351 : term33 = term54.
Proof. exact (MK_COMB (@lem1326350) (@lem1326349)). Qed.
Lemma lem1326353 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326354 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1326353 hreal t). Qed.
Lemma lem1326355 : term54 = True.
Proof. exact (@lem1326354 True). Qed.
Lemma lem1326356 : term33 = True.
Proof. exact (TRANS (@lem1326351) (@lem1326355)). Qed.
Lemma lem1326357 : term22 = True.
Proof. exact (TRANS (@lem1326237) (@lem1326356)). Qed.
Lemma lem1326358 : True = term22.
Proof. exact (SYM (@lem1326357)). Qed.
Lemma lem1326359 : term22.
Proof. exact (EQ_MP (@lem1326358) (@lem0)). Qed.
