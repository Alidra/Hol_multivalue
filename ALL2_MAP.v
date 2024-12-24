Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_MAP_term_abbrevs.
Require Import ALL2_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1128213 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1128214 {_26529 : Type'} (P : type1143 _26529) : term0 _26529 P.
Proof. exact (@lem1128213 _26529 P). Qed.
Lemma lem1128215 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : term1 _26528 _26529 P f.
Proof. exact (@lem1128214 _26529 (term2 _26528 _26529 P f)). Qed.
Lemma lem1128216 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term3 _26528 _26529 P f) = ((term4 _26528 _26529 P f) = (term5 _26528 _26529 P f)).
Proof. exact (eq_refl (term3 _26528 _26529 P f)). Qed.
Lemma lem1128217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128218 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term6 _26528 _26529 P f) = (term7 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128217) (@lem1128216 _26528 _26529 P f)). Qed.
Lemma lem1128219 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term8 _26528 _26529 P f t) = ((term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)).
Proof. exact (eq_refl (term8 _26528 _26529 P f t)). Qed.
Lemma lem1128220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128221 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term11 _26528 _26529 P f t) = (term12 _26528 _26529 P f t).
Proof. exact (MK_COMB (@lem1128220) (@lem1128219 _26528 _26529 P f t)). Qed.
Lemma lem1128222 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) (t : list _26529) : (term13 _26528 _26529 P f h t) = ((term14 _26528 _26529 P f h t) = (term15 _26528 _26529 P f h t)).
Proof. exact (eq_refl (term13 _26528 _26529 P f h t)). Qed.
Lemma lem1128223 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) (t : list _26529) : (term16 _26528 _26529 P f h t) = (term17 _26528 _26529 P f h t).
Proof. exact (MK_COMB (@lem1128221 _26528 _26529 P f t) (@lem1128222 _26528 _26529 P f h t)). Qed.
Lemma lem1128224 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term18 _26528 _26529 P f h) = (term19 _26528 _26529 P f h).
Proof. exact (fun_ext (fun t : list _26529 => @lem1128223 _26528 _26529 P f h t)). Qed.
Lemma lem1128225 {_26529 : Type'} : (@all (list _26529)) = (@all (list _26529)).
Proof. exact (eq_refl (@all (list _26529))). Qed.
Lemma lem1128226 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term20 _26528 _26529 P f h) = (term21 _26528 _26529 P f h).
Proof. exact (MK_COMB (@lem1128225 _26529) (@lem1128224 _26528 _26529 P f h)). Qed.
Lemma lem1128227 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term22 _26528 _26529 P f) = (term23 _26528 _26529 P f).
Proof. exact (fun_ext (fun h : _26529 => @lem1128226 _26528 _26529 P f h)). Qed.
Lemma lem1128228 {_26529 : Type'} : (@all _26529) = (@all _26529).
Proof. exact (eq_refl (@all _26529)). Qed.
Lemma lem1128229 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term24 _26528 _26529 P f) = (term25 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128228 _26529) (@lem1128227 _26528 _26529 P f)). Qed.
Lemma lem1128230 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term26 _26528 _26529 P f) = (term27 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128218 _26528 _26529 P f) (@lem1128229 _26528 _26529 P f)). Qed.
Lemma lem1128231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128232 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term28 _26528 _26529 P f) = (term29 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128231) (@lem1128230 _26528 _26529 P f)). Qed.
Lemma lem1128233 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (l : list _26529) : (term8 _26528 _26529 P f l) = ((term9 _26528 _26529 P f l) = (term10 _26528 _26529 P f l)).
Proof. exact (eq_refl (term8 _26528 _26529 P f l)). Qed.
Lemma lem1128234 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term30 _26528 _26529 P f) = (term2 _26528 _26529 P f).
Proof. exact (fun_ext (fun l : list _26529 => @lem1128233 _26528 _26529 P f l)). Qed.
Lemma lem1128235 {_26529 : Type'} : (@all (list _26529)) = (@all (list _26529)).
Proof. exact (eq_refl (@all (list _26529))). Qed.
Lemma lem1128236 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term31 _26528 _26529 P f) = (term32 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128235 _26529) (@lem1128234 _26528 _26529 P f)). Qed.
Lemma lem1128237 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term1 _26528 _26529 P f) = (term33 _26528 _26529 P f).
Proof. exact (MK_COMB (@lem1128232 _26528 _26529 P f) (@lem1128236 _26528 _26529 P f)). Qed.
Lemma lem1128238 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : term33 _26528 _26529 P f.
Proof. exact (EQ_MP (@lem1128237 _26528 _26529 P f) (@lem1128215 _26528 _26529 P f)). Qed.
Lemma lem1128252 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1128253 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1128252 A B f). Qed.
Lemma lem1128254 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1128265 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1128254 A B f) (@lem1128253 A B f)). Qed.
Lemma lem1128266 {_26528 _26529 : Type'} (f : _26529 -> _26528) : (@List.map _26529 _26528 f (@nil _26529)) = (@nil _26528).
Proof. exact (@lem1128265 _26529 _26528 f). Qed.
Lemma lem1128267 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) : (@ALL2 _26528 _26529 P) = (@ALL2 _26528 _26529 P).
Proof. exact (eq_refl (@ALL2 _26528 _26529 P)). Qed.
Lemma lem1128268 {_26528 _26529 : Type'} (f : _26529 -> _26528) (P : type1413 _26528 _26529) : (term36 _26528 _26529 P f) = (@ALL2 _26528 _26529 P (@nil _26528)).
Proof. exact (MK_COMB (@lem1128267 _26528 _26529 P) (@lem1128266 _26528 _26529 f)). Qed.
Lemma lem1128269 {_26529 : Type'} : (@nil _26529) = (@nil _26529).
Proof. exact (eq_refl (@nil _26529)). Qed.
Lemma lem1128270 {_26528 _26529 : Type'} (f : _26529 -> _26528) (P : type1413 _26528 _26529) : (term4 _26528 _26529 P f) = (@ALL2 _26528 _26529 P (@nil _26528) (@nil _26529)).
Proof. exact (MK_COMB (@lem1128268 _26528 _26529 f P) (@lem1128269 _26529)). Qed.
Lemma lem1128272 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1128273 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) : (@ALL2 _26528 _26529 P (@nil _26528) (@nil _26529)) = True.
Proof. exact (@lem1128272 _26529 _26528 P). Qed.
Lemma lem1128274 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term4 _26528 _26529 P f) = True.
Proof. exact (TRANS (@lem1128270 _26528 _26529 f P) (@lem1128273 _26528 _26529 P)). Qed.
Lemma lem1128275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128276 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term37 _26528 _26529 P f) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1128275) (@lem1128274 _26528 _26529 P f)). Qed.
Lemma lem1128278 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1128279 {_26529 : Type'} (P : _26529 -> Prop) : (@List.Forall _26529 P (@nil _26529)) = True.
Proof. exact (@lem1128278 _26529 P). Qed.
Lemma lem1128280 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term5 _26528 _26529 P f) = True.
Proof. exact (@lem1128279 _26529 (term38 _26528 _26529 P f)). Qed.
Lemma lem1128281 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : ((term4 _26528 _26529 P f) = (term5 _26528 _26529 P f)) = (True = True).
Proof. exact (MK_COMB (@lem1128276 _26528 _26529 P f) (@lem1128280 _26528 _26529 P f)). Qed.
Lemma lem1128283 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1128284 : (True = True) = True.
Proof. exact (@lem1128283 True). Qed.
Lemma lem1128285 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : ((term4 _26528 _26529 P f) = (term5 _26528 _26529 P f)) = True.
Proof. exact (TRANS (@lem1128281 _26528 _26529 P f) (@lem1128284)). Qed.
Lemma lem1128286 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : True = ((term4 _26528 _26529 P f) = (term5 _26528 _26529 P f)).
Proof. exact (SYM (@lem1128285 _26528 _26529 P f)). Qed.
Lemma lem1128287 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term4 _26528 _26529 P f) = (term5 _26528 _26529 P f).
Proof. exact (EQ_MP (@lem1128286 _26528 _26529 P f) (@lem0)). Qed.
Lemma lem1128290 {A B : Type'} : term39 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1128291 {A B : Type'} (f : A -> B) : term40 A B f.
Proof. exact (@lem1128290 A B f). Qed.
Lemma lem1128292 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (eq_refl (term40 A B f)). Qed.
Lemma lem1128293 {A B : Type'} (f : A -> B) : term41 A B f.
Proof. exact (EQ_MP (@lem1128292 A B f) (@lem1128291 A B f)). Qed.
Lemma lem1128294 {A B : Type'} (f : A -> B) (h : A) : term42 A B f h.
Proof. exact (@lem1128293 A B f h). Qed.
Lemma lem1128295 {A B : Type'} (h : A) (f : A -> B) : (term42 A B f h) = (term43 A B h f).
Proof. exact (eq_refl (term42 A B f h)). Qed.
Lemma lem1128296 {A B : Type'} (h : A) (f : A -> B) : term43 A B h f.
Proof. exact (EQ_MP (@lem1128295 A B h f) (@lem1128294 A B f h)). Qed.
Lemma lem1128297 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term44 A B h f t.
Proof. exact (@lem1128296 A B h f t). Qed.
Lemma lem1128298 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term44 A B h f t) = ((term45 A B f h t) = (term46 A B h f t)).
Proof. exact (eq_refl (term44 A B h f t)). Qed.
Lemma lem1128304 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term47 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1128305 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term48 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1128304 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1128313 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term45 A B f h t) = (term46 A B h f t).
Proof. exact (EQ_MP (@lem1128298 A B h f t) (@lem1128297 A B h f t)). Qed.
Lemma lem1128314 {_26528 _26529 : Type'} (h : _26529) (f : _26529 -> _26528) (t : list _26529) : (term49 _26528 _26529 f h t) = (term50 _26528 _26529 h f t).
Proof. exact (@lem1128313 _26529 _26528 h f t). Qed.
Lemma lem1128315 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) : (@ALL2 _26528 _26529 P) = (@ALL2 _26528 _26529 P).
Proof. exact (eq_refl (@ALL2 _26528 _26529 P)). Qed.
Lemma lem1128316 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (h : _26529) (f : _26529 -> _26528) (t : list _26529) : (term51 _26528 _26529 P f h t) = (term52 _26528 _26529 P h f t).
Proof. exact (MK_COMB (@lem1128315 _26528 _26529 P) (@lem1128314 _26528 _26529 h f t)). Qed.
Lemma lem1128317 {_26529 : Type'} (h : _26529) (t : list _26529) : (@cons _26529 h t) = (@cons _26529 h t).
Proof. exact (eq_refl (@cons _26529 h t)). Qed.
Lemma lem1128318 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) (t : list _26529) : (term14 _26528 _26529 P f h t) = (term53 _26528 _26529 P f h t).
Proof. exact (MK_COMB (@lem1128316 _26528 _26529 P h f t) (@lem1128317 _26529 h t)). Qed.
Lemma lem1128320 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term54 _25470 _25471 P h1' t1 h2' t2) = (term55 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1128305 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1128321 {_26528 _26529 : Type'} (h1' : _26528) (h2' : _26529) (P : type1413 _26528 _26529) (t1 : list _26528) (t2 : list _26529) : (term56 _26528 _26529 P h1' t1 h2' t2) = (term57 _26528 _26529 h1' h2' P t1 t2).
Proof. exact (@lem1128320 _26529 _26528 h1' h2' P t1 t2). Qed.
Lemma lem1128322 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term53 _26528 _26529 P f h t) = (term58 _26528 _26529 h P f t).
Proof. exact (@lem1128321 _26528 _26529 (f h) h P (@List.map _26529 _26528 f t) t). Qed.
Lemma lem1128326 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t).
Proof. exact (h1). Qed.
Lemma lem1128327 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term59 _26528 _26529 P f h) = (term59 _26528 _26529 P f h).
Proof. exact (eq_refl (term59 _26528 _26529 P f h)). Qed.
Lemma lem1128328 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term58 _26528 _26529 h P f t) = (term60 _26528 _26529 h P f t).
Proof. exact (MK_COMB (@lem1128327 _26528 _26529 P f h) (@lem1128326 _26528 _26529 P f t h1)). Qed.
Lemma lem1128331 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term53 _26528 _26529 P f h t) = (term60 _26528 _26529 h P f t).
Proof. exact (TRANS (@lem1128322 _26528 _26529 h P f t) (@lem1128328 _26528 _26529 h P f t h1)). Qed.
Lemma lem1128332 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term14 _26528 _26529 P f h t) = (term60 _26528 _26529 h P f t).
Proof. exact (TRANS (@lem1128318 _26528 _26529 P f h t) (@lem1128331 _26528 _26529 h P f t h1)). Qed.
Lemma lem1128333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128334 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term61 _26528 _26529 P f h t) = (term62 _26528 _26529 h P f t).
Proof. exact (MK_COMB (@lem1128333) (@lem1128332 _26528 _26529 h P f t h1)). Qed.
Lemma lem1128336 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term63 _25307 P h t) = (term64 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1128337 {_26529 : Type'} (h : _26529) (P : _26529 -> Prop) (t : list _26529) : (term63 _26529 P h t) = (term64 _26529 h P t).
Proof. exact (@lem1128336 _26529 h P t). Qed.
Lemma lem1128338 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term15 _26528 _26529 P f h t) = (term65 _26528 _26529 h P f t).
Proof. exact (@lem1128337 _26529 h (term38 _26528 _26529 P f) t). Qed.
Lemma lem1128342 {A B : Type'} (f : A -> B) (y : A) : (term66 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1128343 {_26529 : Type'} (f : _26529 -> Prop) (y : _26529) : (term67 _26529 f y) = (f y).
Proof. exact (@lem1128342 _26529 Prop f y). Qed.
Lemma lem1128344 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term68 _26528 _26529 P f h) = (term69 _26528 _26529 P f h).
Proof. exact (@lem1128343 _26529 (term38 _26528 _26529 P f) h). Qed.
Lemma lem1128345 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (a : _26529) : (term69 _26528 _26529 P f a) = (term70 _26528 _26529 P f a).
Proof. exact (eq_refl (term69 _26528 _26529 P f a)). Qed.
Lemma lem1128346 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : (term71 _26528 _26529 P f) = (term38 _26528 _26529 P f).
Proof. exact (fun_ext (fun a : _26529 => @lem1128345 _26528 _26529 P f a)). Qed.
Lemma lem1128347 {_26529 : Type'} (h : _26529) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1128348 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term68 _26528 _26529 P f h) = (term69 _26528 _26529 P f h).
Proof. exact (MK_COMB (@lem1128346 _26528 _26529 P f) (@lem1128347 _26529 h)). Qed.
Lemma lem1128349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128350 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term72 _26528 _26529 P f h) = (term73 _26528 _26529 P f h).
Proof. exact (MK_COMB (@lem1128349) (@lem1128348 _26528 _26529 P f h)). Qed.
Lemma lem1128351 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term69 _26528 _26529 P f h) = (term70 _26528 _26529 P f h).
Proof. exact (eq_refl (term69 _26528 _26529 P f h)). Qed.
Lemma lem1128352 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : ((term68 _26528 _26529 P f h) = (term69 _26528 _26529 P f h)) = ((term69 _26528 _26529 P f h) = (term70 _26528 _26529 P f h)).
Proof. exact (MK_COMB (@lem1128350 _26528 _26529 P f h) (@lem1128351 _26528 _26529 P f h)). Qed.
Lemma lem1128353 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term69 _26528 _26529 P f h) = (term70 _26528 _26529 P f h).
Proof. exact (EQ_MP (@lem1128352 _26528 _26529 P f h) (@lem1128344 _26528 _26529 P f h)). Qed.
Lemma lem1128354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128355 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : (term74 _26528 _26529 P f h) = (term59 _26528 _26529 P f h).
Proof. exact (MK_COMB (@lem1128354) (@lem1128353 _26528 _26529 P f h)). Qed.
Lemma lem1128356 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term10 _26528 _26529 P f t) = (term10 _26528 _26529 P f t).
Proof. exact (eq_refl (term10 _26528 _26529 P f t)). Qed.
Lemma lem1128357 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term65 _26528 _26529 h P f t) = (term60 _26528 _26529 h P f t).
Proof. exact (MK_COMB (@lem1128355 _26528 _26529 P f h) (@lem1128356 _26528 _26529 P f t)). Qed.
Lemma lem1128360 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : (term15 _26528 _26529 P f h t) = (term60 _26528 _26529 h P f t).
Proof. exact (TRANS (@lem1128338 _26528 _26529 h P f t) (@lem1128357 _26528 _26529 h P f t)). Qed.
Lemma lem1128361 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : ((term14 _26528 _26529 P f h t) = (term15 _26528 _26529 P f h t)) = ((term60 _26528 _26529 h P f t) = (term60 _26528 _26529 h P f t)).
Proof. exact (MK_COMB (@lem1128334 _26528 _26529 h P f t h1) (@lem1128360 _26528 _26529 h P f t)). Qed.
Lemma lem1128363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1128364 (x : Prop) : (x = x) = True.
Proof. exact (@lem1128363 Prop x). Qed.
Lemma lem1128365 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) : ((term60 _26528 _26529 h P f t) = (term60 _26528 _26529 h P f t)) = True.
Proof. exact (@lem1128364 (term60 _26528 _26529 h P f t)). Qed.
Lemma lem1128366 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : ((term14 _26528 _26529 P f h t) = (term15 _26528 _26529 P f h t)) = True.
Proof. exact (TRANS (@lem1128361 _26528 _26529 h P f t h1) (@lem1128365 _26528 _26529 h P f t)). Qed.
Lemma lem1128367 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : True = ((term14 _26528 _26529 P f h t) = (term15 _26528 _26529 P f h t)).
Proof. exact (SYM (@lem1128366 _26528 _26529 h P f t h1)). Qed.
Lemma lem1128368 {_26528 _26529 : Type'} (h : _26529) (P : type1413 _26528 _26529) (f : _26529 -> _26528) (t : list _26529) (h1 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t)) : (term14 _26528 _26529 P f h t) = (term15 _26528 _26529 P f h t).
Proof. exact (EQ_MP (@lem1128367 _26528 _26529 h P f t h1) (@lem0)). Qed.
Lemma lem1128369 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) (t : list _26529) : term17 _26528 _26529 P f h t.
Proof. exact (fun h0 : (term9 _26528 _26529 P f t) = (term10 _26528 _26529 P f t) => @lem1128368 _26528 _26529 h P f t h0). Qed.
Lemma lem1128374 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) (h : _26529) : term21 _26528 _26529 P f h.
Proof. exact (fun t : list _26529 => @lem1128369 _26528 _26529 P f h t). Qed.
Lemma lem1128379 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : term25 _26528 _26529 P f.
Proof. exact (fun h : _26529 => @lem1128374 _26528 _26529 P f h). Qed.
Lemma lem1128380 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : term27 _26528 _26529 P f.
Proof. exact (conj (@lem1128287 _26528 _26529 P f) (@lem1128379 _26528 _26529 P f)). Qed.
Lemma lem1128381 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) (f : _26529 -> _26528) : term32 _26528 _26529 P f.
Proof. exact (@lem1128238 _26528 _26529 P f (@lem1128380 _26528 _26529 P f)). Qed.
Lemma lem1128386 {_26528 _26529 : Type'} (P : type1413 _26528 _26529) : term75 _26528 _26529 P.
Proof. exact (fun f : _26529 -> _26528 => @lem1128381 _26528 _26529 P f). Qed.
Lemma lem1128391 {_26528 _26529 : Type'} : term76 _26528 _26529.
Proof. exact (fun P : type1413 _26528 _26529 => @lem1128386 _26528 _26529 P). Qed.
