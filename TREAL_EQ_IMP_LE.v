Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_EQ_IMP_LE_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1319042_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import treal_eq_spec.
Require Import treal_le_spec.
Lemma lem1334179 (x : hreal) : term0 x.
Proof. exact (@lem1319042 x). Qed.
Lemma lem1334180 (x : hreal) : (term0 x) = (hreal_le x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1334181 (x : hreal) : hreal_le x x.
Proof. exact (EQ_MP (@lem1334180 x) (@lem1334179 x)). Qed.
Lemma lem1334182 (x : hreal) : (hreal_le x x) = ((hreal_le x x) = True).
Proof. exact (@lem7 (hreal_le x x)). Qed.
Lemma lem1334184 (x1 : hreal) : term1 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1334185 (x1 : hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1334186 (x1 : hreal) : term2 x1.
Proof. exact (EQ_MP (@lem1334185 x1) (@lem1334184 x1)). Qed.
Lemma lem1334187 (x1 : hreal) (y2 : hreal) : term3 x1 y2.
Proof. exact (@lem1334186 x1 y2). Qed.
Lemma lem1334188 (x1 : hreal) (y2 : hreal) : (term3 x1 y2) = (term4 x1 y2).
Proof. exact (eq_refl (term3 x1 y2)). Qed.
Lemma lem1334189 (x1 : hreal) (y2 : hreal) : term4 x1 y2.
Proof. exact (EQ_MP (@lem1334188 x1 y2) (@lem1334187 x1 y2)). Qed.
Lemma lem1334190 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term5 x1 y2 x2.
Proof. exact (@lem1334189 x1 y2 x2). Qed.
Lemma lem1334191 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term5 x1 y2 x2) = (term6 x1 y2 x2).
Proof. exact (eq_refl (term5 x1 y2 x2)). Qed.
Lemma lem1334192 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term6 x1 y2 x2.
Proof. exact (EQ_MP (@lem1334191 x1 y2 x2) (@lem1334190 x1 y2 x2)). Qed.
Lemma lem1334193 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term7 x1 y2 x2 y1.
Proof. exact (@lem1334192 x1 y2 x2 y1). Qed.
Lemma lem1334194 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term7 x1 y2 x2 y1) = ((term8 x1 y1 x2 y2) = (term9 x1 y2 x2 y1)).
Proof. exact (eq_refl (term7 x1 y2 x2 y1)). Qed.
Lemma lem1334196 (x1 : hreal) : term10 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1334197 (x1 : hreal) : (term10 x1) = (term11 x1).
Proof. exact (eq_refl (term10 x1)). Qed.
Lemma lem1334198 (x1 : hreal) : term11 x1.
Proof. exact (EQ_MP (@lem1334197 x1) (@lem1334196 x1)). Qed.
Lemma lem1334199 (x1 : hreal) (y2 : hreal) : term12 x1 y2.
Proof. exact (@lem1334198 x1 y2). Qed.
Lemma lem1334200 (x1 : hreal) (y2 : hreal) : (term12 x1 y2) = (term13 x1 y2).
Proof. exact (eq_refl (term12 x1 y2)). Qed.
Lemma lem1334201 (x1 : hreal) (y2 : hreal) : term13 x1 y2.
Proof. exact (EQ_MP (@lem1334200 x1 y2) (@lem1334199 x1 y2)). Qed.
Lemma lem1334202 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term14 x1 y2 x2.
Proof. exact (@lem1334201 x1 y2 x2). Qed.
Lemma lem1334203 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term14 x1 y2 x2) = (term15 x1 y2 x2).
Proof. exact (eq_refl (term14 x1 y2 x2)). Qed.
Lemma lem1334204 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term15 x1 y2 x2.
Proof. exact (EQ_MP (@lem1334203 x1 y2 x2) (@lem1334202 x1 y2 x2)). Qed.
Lemma lem1334205 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term16 x1 y2 x2 y1.
Proof. exact (@lem1334204 x1 y2 x2 y1). Qed.
Lemma lem1334206 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term16 x1 y2 x2 y1) = ((term17 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term16 x1 y2 x2 y1)). Qed.
Lemma lem1334208 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term18 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1334209 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term18 _5106 _5107 P) = ((term19 _5106 _5107 P) = (term20 _5106 _5107 P)).
Proof. exact (eq_refl (term18 _5106 _5107 P)). Qed.
Lemma lem1334216 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1334209 _5106 _5107 P) (@lem1334208 _5106 _5107 P)). Qed.
Lemma lem1334217 (P : type1233) : (term21 P) = (term22 P).
Proof. exact (@lem1334216 hreal hreal P). Qed.
Lemma lem1334218 : term23 = term24.
Proof. exact (@lem1334217 term25). Qed.
Lemma lem1334219 (x : prod hreal hreal) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1334220 : term28 = term25.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1334219 x)). Qed.
Lemma lem1334221 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1334222 : term23 = term29.
Proof. exact (MK_COMB (@lem1334221) (@lem1334220)). Qed.
Lemma lem1334223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334224 : term30 = term31.
Proof. exact (MK_COMB (@lem1334223) (@lem1334222)). Qed.
Lemma lem1334225 (p1 : hreal) (p2 : hreal) : (term32 p1 p2) = (term33 p1 p2).
Proof. exact (eq_refl (term32 p1 p2)). Qed.
Lemma lem1334226 (p1 : hreal) : (term34 p1) = (term35 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1334225 p1 p2)). Qed.
Lemma lem1334227 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334228 (p1 : hreal) : (term36 p1) = (term37 p1).
Proof. exact (MK_COMB (@lem1334227) (@lem1334226 p1)). Qed.
Lemma lem1334229 : term38 = term39.
Proof. exact (fun_ext (fun p1 : hreal => @lem1334228 p1)). Qed.
Lemma lem1334230 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334231 : term24 = term40.
Proof. exact (MK_COMB (@lem1334230) (@lem1334229)). Qed.
Lemma lem1334232 : (term23 = term24) = (term29 = term40).
Proof. exact (MK_COMB (@lem1334224) (@lem1334231)). Qed.
Lemma lem1334233 : term29 = term40.
Proof. exact (EQ_MP (@lem1334232) (@lem1334218)). Qed.
Lemma lem1334251 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term19 _5106 _5107 P) = (term20 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1334209 _5106 _5107 P) (@lem1334208 _5106 _5107 P)). Qed.
Lemma lem1334252 (P : type1233) : (term21 P) = (term22 P).
Proof. exact (@lem1334251 hreal hreal P). Qed.
Lemma lem1334253 (p1 : hreal) (p2 : hreal) : (term41 p1 p2) = (term42 p1 p2).
Proof. exact (@lem1334252 (term43 p1 p2)). Qed.
Lemma lem1334254 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term44 p1 p2 y) = (term45 p1 p2 y).
Proof. exact (eq_refl (term44 p1 p2 y)). Qed.
Lemma lem1334255 (p1 : hreal) (p2 : hreal) : (term46 p1 p2) = (term43 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1334254 p1 p2 y)). Qed.
Lemma lem1334256 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1334257 (p1 : hreal) (p2 : hreal) : (term41 p1 p2) = (term33 p1 p2).
Proof. exact (MK_COMB (@lem1334256) (@lem1334255 p1 p2)). Qed.
Lemma lem1334258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1334259 (p1 : hreal) (p2 : hreal) : (term47 p1 p2) = (term48 p1 p2).
Proof. exact (MK_COMB (@lem1334258) (@lem1334257 p1 p2)). Qed.
Lemma lem1334260 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term49 p1 p2 p1' p2') = (term50 p1 p2 p1' p2').
Proof. exact (eq_refl (term49 p1 p2 p1' p2')). Qed.
Lemma lem1334261 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term51 p1 p2 p1') = (term52 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1334260 p1 p2 p1' p2')). Qed.
Lemma lem1334262 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334263 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term53 p1 p2 p1') = (term54 p1 p2 p1').
Proof. exact (MK_COMB (@lem1334262) (@lem1334261 p1 p2 p1')). Qed.
Lemma lem1334264 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term56 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1334263 p1 p2 p1')). Qed.
Lemma lem1334265 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334266 (p1 : hreal) (p2 : hreal) : (term42 p1 p2) = (term57 p1 p2).
Proof. exact (MK_COMB (@lem1334265) (@lem1334264 p1 p2)). Qed.
Lemma lem1334267 (p1 : hreal) (p2 : hreal) : ((term41 p1 p2) = (term42 p1 p2)) = ((term33 p1 p2) = (term57 p1 p2)).
Proof. exact (MK_COMB (@lem1334259 p1 p2) (@lem1334266 p1 p2)). Qed.
Lemma lem1334268 (p1 : hreal) (p2 : hreal) : (term33 p1 p2) = (term57 p1 p2).
Proof. exact (EQ_MP (@lem1334267 p1 p2) (@lem1334253 p1 p2)). Qed.
Lemma lem1334284 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term58 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1334285 (p : Prop) (q : Prop) (p' : Prop) : term59 p q p'.
Proof. exact (fun q' : Prop => @lem1334284 p q p' q'). Qed.
Lemma lem1334286 (p : Prop) (q : Prop) : term60 p q.
Proof. exact (fun p' : Prop => @lem1334285 p q p'). Qed.
Lemma lem1334287 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : term61 p1 p2 p1' p2'.
Proof. exact (@lem1334286 (term17 p1 p2 p1' p2') (term8 p1 p2 p1' p2')). Qed.
Lemma lem1334288 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) : term62 p1 p2 p1' p2' p'.
Proof. exact (@lem1334287 p1 p2 p1' p2' p'). Qed.
Lemma lem1334289 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) : (term62 p1 p2 p1' p2' p') = (term63 p1 p2 p1' p2' p').
Proof. exact (eq_refl (term62 p1 p2 p1' p2' p')). Qed.
Lemma lem1334290 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) : term63 p1 p2 p1' p2' p'.
Proof. exact (EQ_MP (@lem1334289 p1 p2 p1' p2' p') (@lem1334288 p1 p2 p1' p2' p')). Qed.
Lemma lem1334291 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) (q' : Prop) : term64 p1 p2 p1' p2' p' q'.
Proof. exact (@lem1334290 p1 p2 p1' p2' p' q'). Qed.
Lemma lem1334292 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) (q' : Prop) : (term64 p1 p2 p1' p2' p' q') = (term65 p1 p2 p1' p2' p' q').
Proof. exact (eq_refl (term64 p1 p2 p1' p2' p' q')). Qed.
Lemma lem1334293 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p' : Prop) (q' : Prop) : term65 p1 p2 p1' p2' p' q'.
Proof. exact (EQ_MP (@lem1334292 p1 p2 p1' p2' p' q') (@lem1334291 p1 p2 p1' p2' p' q')). Qed.
Lemma lem1334295 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term17 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1334206 x1 y2 x2 y1) (@lem1334205 x1 y2 x2 y1)). Qed.
Lemma lem1334296 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term17 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1334295 p1 p2' p1' p2). Qed.
Lemma lem1334299 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (q' : Prop) : term66 p1 p2' p1' p2 q'.
Proof. exact (@lem1334293 p1 p2 p1' p2' ((hreal_add p1 p2') = (hreal_add p1' p2)) q'). Qed.
Lemma lem1334300 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (q' : Prop) : term67 p1 p2' p1' p2 q'.
Proof. exact (@lem1334299 p1 p2' p1' p2 q' (@lem1334296 p1 p2' p1' p2)). Qed.
Lemma lem1334303 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term8 x1 y1 x2 y2) = (term9 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1334194 x1 y2 x2 y1) (@lem1334193 x1 y2 x2 y1)). Qed.
Lemma lem1334304 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term8 p1 p2 p1' p2') = (term9 p1 p2' p1' p2).
Proof. exact (@lem1334303 p1 p2' p1' p2). Qed.
Lemma lem1334308 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (h1). Qed.
Lemma lem1334309 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1334310 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term68 p1 p2') = (term68 p1' p2).
Proof. exact (MK_COMB (@lem1334309) (@lem1334308 p1 p2' p1' p2 h1)). Qed.
Lemma lem1334311 (p1' : hreal) (p2 : hreal) : (hreal_add p1' p2) = (hreal_add p1' p2).
Proof. exact (eq_refl (hreal_add p1' p2)). Qed.
Lemma lem1334312 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term9 p1 p2' p1' p2) = (term69 p1' p2).
Proof. exact (MK_COMB (@lem1334310 p1 p2' p1' p2 h1) (@lem1334311 p1' p2)). Qed.
Lemma lem1334314 (x : hreal) : (hreal_le x x) = True.
Proof. exact (EQ_MP (@lem1334182 x) (@lem1334181 x)). Qed.
Lemma lem1334315 (p1' : hreal) (p2 : hreal) : (term69 p1' p2) = True.
Proof. exact (@lem1334314 (hreal_add p1' p2)). Qed.
Lemma lem1334316 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term9 p1 p2' p1' p2) = True.
Proof. exact (TRANS (@lem1334312 p1 p2' p1' p2 h1) (@lem1334315 p1' p2)). Qed.
Lemma lem1334317 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (term8 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1334304 p1 p2' p1' p2) (@lem1334316 p1 p2' p1' p2 h1)). Qed.
Lemma lem1334318 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : term70 p1 p2 p1' p2'.
Proof. exact (fun h0 : (hreal_add p1 p2') = (hreal_add p1' p2) => @lem1334317 p1 p2' p1' p2 h0). Qed.
Lemma lem1334319 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : term71 p1 p2' p1' p2.
Proof. exact (@lem1334300 p1 p2' p1' p2 True). Qed.
Lemma lem1334320 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term50 p1 p2 p1' p2') = (term72 p1 p2' p1' p2).
Proof. exact (@lem1334319 p1 p2' p1' p2 (@lem1334318 p1 p2 p1' p2')). Qed.
Lemma lem1334324 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1334325 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term72 p1 p2' p1' p2) = True.
Proof. exact (@lem1334324 ((hreal_add p1 p2') = (hreal_add p1' p2))). Qed.
Lemma lem1334326 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term50 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1334320 p1 p2' p1' p2) (@lem1334325 p1 p2' p1' p2)). Qed.
Lemma lem1334327 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term52 p1 p2 p1') = term73.
Proof. exact (fun_ext (fun p2' : hreal => @lem1334326 p1 p2 p1' p2')). Qed.
Lemma lem1334328 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334329 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term54 p1 p2 p1') = term74.
Proof. exact (MK_COMB (@lem1334328) (@lem1334327 p1 p2 p1')). Qed.
Lemma lem1334331 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1334332 (t : Prop) : (term76 t) = t.
Proof. exact (@lem1334331 hreal t). Qed.
Lemma lem1334333 : term74 = True.
Proof. exact (@lem1334332 True). Qed.
Lemma lem1334334 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term54 p1 p2 p1') = True.
Proof. exact (TRANS (@lem1334329 p1 p2 p1') (@lem1334333)). Qed.
Lemma lem1334335 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = term73.
Proof. exact (fun_ext (fun p1' : hreal => @lem1334334 p1 p2 p1')). Qed.
Lemma lem1334336 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334337 (p1 : hreal) (p2 : hreal) : (term57 p1 p2) = term74.
Proof. exact (MK_COMB (@lem1334336) (@lem1334335 p1 p2)). Qed.
Lemma lem1334339 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1334340 (t : Prop) : (term76 t) = t.
Proof. exact (@lem1334339 hreal t). Qed.
Lemma lem1334341 : term74 = True.
Proof. exact (@lem1334340 True). Qed.
Lemma lem1334342 (p1 : hreal) (p2 : hreal) : (term57 p1 p2) = True.
Proof. exact (TRANS (@lem1334337 p1 p2) (@lem1334341)). Qed.
Lemma lem1334343 (p1 : hreal) (p2 : hreal) : (term33 p1 p2) = True.
Proof. exact (TRANS (@lem1334268 p1 p2) (@lem1334342 p1 p2)). Qed.
Lemma lem1334344 (p1 : hreal) : (term35 p1) = term73.
Proof. exact (fun_ext (fun p2 : hreal => @lem1334343 p1 p2)). Qed.
Lemma lem1334345 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334346 (p1 : hreal) : (term37 p1) = term74.
Proof. exact (MK_COMB (@lem1334345) (@lem1334344 p1)). Qed.
Lemma lem1334348 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1334349 (t : Prop) : (term76 t) = t.
Proof. exact (@lem1334348 hreal t). Qed.
Lemma lem1334350 : term74 = True.
Proof. exact (@lem1334349 True). Qed.
Lemma lem1334351 (p1 : hreal) : (term37 p1) = True.
Proof. exact (TRANS (@lem1334346 p1) (@lem1334350)). Qed.
Lemma lem1334352 : term39 = term73.
Proof. exact (fun_ext (fun p1 : hreal => @lem1334351 p1)). Qed.
Lemma lem1334353 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1334354 : term40 = term74.
Proof. exact (MK_COMB (@lem1334353) (@lem1334352)). Qed.
Lemma lem1334356 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1334357 (t : Prop) : (term76 t) = t.
Proof. exact (@lem1334356 hreal t). Qed.
Lemma lem1334358 : term74 = True.
Proof. exact (@lem1334357 True). Qed.
Lemma lem1334359 : term40 = True.
Proof. exact (TRANS (@lem1334354) (@lem1334358)). Qed.
Lemma lem1334360 : term29 = True.
Proof. exact (TRANS (@lem1334233) (@lem1334359)). Qed.
Lemma lem1334361 : True = term29.
Proof. exact (SYM (@lem1334360)). Qed.
Lemma lem1334362 : term29.
Proof. exact (EQ_MP (@lem1334361) (@lem0)). Qed.
