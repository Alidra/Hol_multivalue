Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_ALL_term_abbrevs.
Require Import ALL2_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1187165 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1187166 {_27624 : Type'} (P : type1143 _27624) : term0 _27624 P.
Proof. exact (@lem1187165 _27624 P). Qed.
Lemma lem1187167 {_27624 : Type'} (P : type1402 _27624) : term1 _27624 P.
Proof. exact (@lem1187166 _27624 (term2 _27624 P)). Qed.
Lemma lem1187168 {_27624 : Type'} (P : type1402 _27624) : (term3 _27624 P) = ((@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = (term4 _27624 P)).
Proof. exact (eq_refl (term3 _27624 P)). Qed.
Lemma lem1187169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187170 {_27624 : Type'} (P : type1402 _27624) : (term5 _27624 P) = (term6 _27624 P).
Proof. exact (MK_COMB (@lem1187169) (@lem1187168 _27624 P)). Qed.
Lemma lem1187171 {_27624 : Type'} (P : type1402 _27624) (t : list _27624) : (term7 _27624 P t) = ((@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)).
Proof. exact (eq_refl (term7 _27624 P t)). Qed.
Lemma lem1187172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1187173 {_27624 : Type'} (P : type1402 _27624) (t : list _27624) : (term9 _27624 P t) = (term10 _27624 P t).
Proof. exact (MK_COMB (@lem1187172) (@lem1187171 _27624 P t)). Qed.
Lemma lem1187174 {_27624 : Type'} (P : type1402 _27624) (h : _27624) (t : list _27624) : (term11 _27624 P h t) = ((term12 _27624 P h t) = (term13 _27624 P h t)).
Proof. exact (eq_refl (term11 _27624 P h t)). Qed.
Lemma lem1187175 {_27624 : Type'} (P : type1402 _27624) (h : _27624) (t : list _27624) : (term14 _27624 P h t) = (term15 _27624 P h t).
Proof. exact (MK_COMB (@lem1187173 _27624 P t) (@lem1187174 _27624 P h t)). Qed.
Lemma lem1187176 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term16 _27624 P h) = (term17 _27624 P h).
Proof. exact (fun_ext (fun t : list _27624 => @lem1187175 _27624 P h t)). Qed.
Lemma lem1187177 {_27624 : Type'} : (@all (list _27624)) = (@all (list _27624)).
Proof. exact (eq_refl (@all (list _27624))). Qed.
Lemma lem1187178 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term18 _27624 P h) = (term19 _27624 P h).
Proof. exact (MK_COMB (@lem1187177 _27624) (@lem1187176 _27624 P h)). Qed.
Lemma lem1187179 {_27624 : Type'} (P : type1402 _27624) : (term20 _27624 P) = (term21 _27624 P).
Proof. exact (fun_ext (fun h : _27624 => @lem1187178 _27624 P h)). Qed.
Lemma lem1187180 {_27624 : Type'} : (@all _27624) = (@all _27624).
Proof. exact (eq_refl (@all _27624)). Qed.
Lemma lem1187181 {_27624 : Type'} (P : type1402 _27624) : (term22 _27624 P) = (term23 _27624 P).
Proof. exact (MK_COMB (@lem1187180 _27624) (@lem1187179 _27624 P)). Qed.
Lemma lem1187182 {_27624 : Type'} (P : type1402 _27624) : (term24 _27624 P) = (term25 _27624 P).
Proof. exact (MK_COMB (@lem1187170 _27624 P) (@lem1187181 _27624 P)). Qed.
Lemma lem1187183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1187184 {_27624 : Type'} (P : type1402 _27624) : (term26 _27624 P) = (term27 _27624 P).
Proof. exact (MK_COMB (@lem1187183) (@lem1187182 _27624 P)). Qed.
Lemma lem1187185 {_27624 : Type'} (P : type1402 _27624) (l : list _27624) : (term7 _27624 P l) = ((@ALL2 _27624 _27624 P l l) = (term8 _27624 P l)).
Proof. exact (eq_refl (term7 _27624 P l)). Qed.
Lemma lem1187186 {_27624 : Type'} (P : type1402 _27624) : (term28 _27624 P) = (term2 _27624 P).
Proof. exact (fun_ext (fun l : list _27624 => @lem1187185 _27624 P l)). Qed.
Lemma lem1187187 {_27624 : Type'} : (@all (list _27624)) = (@all (list _27624)).
Proof. exact (eq_refl (@all (list _27624))). Qed.
Lemma lem1187188 {_27624 : Type'} (P : type1402 _27624) : (term29 _27624 P) = (term30 _27624 P).
Proof. exact (MK_COMB (@lem1187187 _27624) (@lem1187186 _27624 P)). Qed.
Lemma lem1187189 {_27624 : Type'} (P : type1402 _27624) : (term1 _27624 P) = (term31 _27624 P).
Proof. exact (MK_COMB (@lem1187184 _27624 P) (@lem1187188 _27624 P)). Qed.
Lemma lem1187190 {_27624 : Type'} (P : type1402 _27624) : term31 _27624 P.
Proof. exact (EQ_MP (@lem1187189 _27624 P) (@lem1187167 _27624 P)). Qed.
Lemma lem1187203 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1187204 {_27624 : Type'} (P : type1402 _27624) : (@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = True.
Proof. exact (@lem1187203 _27624 _27624 P). Qed.
Lemma lem1187205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187206 {_27624 : Type'} (P : type1402 _27624) : (term32 _27624 P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1187205) (@lem1187204 _27624 P)). Qed.
Lemma lem1187208 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1187209 {_27624 : Type'} (P : _27624 -> Prop) : (@List.Forall _27624 P (@nil _27624)) = True.
Proof. exact (@lem1187208 _27624 P). Qed.
Lemma lem1187210 {_27624 : Type'} (P : type1402 _27624) : (term4 _27624 P) = True.
Proof. exact (@lem1187209 _27624 (term33 _27624 P)). Qed.
Lemma lem1187211 {_27624 : Type'} (P : type1402 _27624) : ((@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = (term4 _27624 P)) = (True = True).
Proof. exact (MK_COMB (@lem1187206 _27624 P) (@lem1187210 _27624 P)). Qed.
Lemma lem1187213 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1187214 : (True = True) = True.
Proof. exact (@lem1187213 True). Qed.
Lemma lem1187215 {_27624 : Type'} (P : type1402 _27624) : ((@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = (term4 _27624 P)) = True.
Proof. exact (TRANS (@lem1187211 _27624 P) (@lem1187214)). Qed.
Lemma lem1187216 {_27624 : Type'} (P : type1402 _27624) : True = ((@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = (term4 _27624 P)).
Proof. exact (SYM (@lem1187215 _27624 P)). Qed.
Lemma lem1187217 {_27624 : Type'} (P : type1402 _27624) : (@ALL2 _27624 _27624 P (@nil _27624) (@nil _27624)) = (term4 _27624 P).
Proof. exact (EQ_MP (@lem1187216 _27624 P) (@lem0)). Qed.
Lemma lem1187220 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term34 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1187221 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term35 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1187220 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1187229 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term36 _25470 _25471 P h1' t1 h2' t2) = (term37 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1187221 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1187230 {_27624 : Type'} (h1' : _27624) (h2' : _27624) (P : type1402 _27624) (t1 : list _27624) (t2 : list _27624) : (term38 _27624 P h1' t1 h2' t2) = (term39 _27624 h1' h2' P t1 t2).
Proof. exact (@lem1187229 _27624 _27624 h1' h2' P t1 t2). Qed.
Lemma lem1187231 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) : (term12 _27624 P h t) = (term40 _27624 h P t).
Proof. exact (@lem1187230 _27624 h h P t t). Qed.
Lemma lem1187235 {_27624 : Type'} (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t).
Proof. exact (h1). Qed.
Lemma lem1187236 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term41 _27624 P h) = (term41 _27624 P h).
Proof. exact (eq_refl (term41 _27624 P h)). Qed.
Lemma lem1187237 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : (term40 _27624 h P t) = (term42 _27624 h P t).
Proof. exact (MK_COMB (@lem1187236 _27624 P h) (@lem1187235 _27624 P t h1)). Qed.
Lemma lem1187240 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : (term12 _27624 P h t) = (term42 _27624 h P t).
Proof. exact (TRANS (@lem1187231 _27624 h P t) (@lem1187237 _27624 h P t h1)). Qed.
Lemma lem1187241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187242 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : (term43 _27624 P h t) = (term44 _27624 h P t).
Proof. exact (MK_COMB (@lem1187241) (@lem1187240 _27624 h P t h1)). Qed.
Lemma lem1187244 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term45 _25307 P h t) = (term46 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1187245 {_27624 : Type'} (h : _27624) (P : _27624 -> Prop) (t : list _27624) : (term45 _27624 P h t) = (term46 _27624 h P t).
Proof. exact (@lem1187244 _27624 h P t). Qed.
Lemma lem1187246 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) : (term13 _27624 P h t) = (term47 _27624 h P t).
Proof. exact (@lem1187245 _27624 h (term33 _27624 P) t). Qed.
Lemma lem1187250 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1187251 {_27624 : Type'} (f : _27624 -> Prop) (y : _27624) : (term49 _27624 f y) = (f y).
Proof. exact (@lem1187250 _27624 Prop f y). Qed.
Lemma lem1187252 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term50 _27624 P h) = (term51 _27624 P h).
Proof. exact (@lem1187251 _27624 (term33 _27624 P) h). Qed.
Lemma lem1187253 {_27624 : Type'} (P : type1402 _27624) (x : _27624) : (term51 _27624 P x) = (P x x).
Proof. exact (eq_refl (term51 _27624 P x)). Qed.
Lemma lem1187254 {_27624 : Type'} (P : type1402 _27624) : (term52 _27624 P) = (term33 _27624 P).
Proof. exact (fun_ext (fun x : _27624 => @lem1187253 _27624 P x)). Qed.
Lemma lem1187255 {_27624 : Type'} (h : _27624) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1187256 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term50 _27624 P h) = (term51 _27624 P h).
Proof. exact (MK_COMB (@lem1187254 _27624 P) (@lem1187255 _27624 h)). Qed.
Lemma lem1187257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1187258 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term53 _27624 P h) = (term54 _27624 P h).
Proof. exact (MK_COMB (@lem1187257) (@lem1187256 _27624 P h)). Qed.
Lemma lem1187259 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term51 _27624 P h) = (P h h).
Proof. exact (eq_refl (term51 _27624 P h)). Qed.
Lemma lem1187260 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : ((term50 _27624 P h) = (term51 _27624 P h)) = ((term51 _27624 P h) = (P h h)).
Proof. exact (MK_COMB (@lem1187258 _27624 P h) (@lem1187259 _27624 P h)). Qed.
Lemma lem1187261 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term51 _27624 P h) = (P h h).
Proof. exact (EQ_MP (@lem1187260 _27624 P h) (@lem1187252 _27624 P h)). Qed.
Lemma lem1187262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1187263 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : (term55 _27624 P h) = (term41 _27624 P h).
Proof. exact (MK_COMB (@lem1187262) (@lem1187261 _27624 P h)). Qed.
Lemma lem1187264 {_27624 : Type'} (P : type1402 _27624) (t : list _27624) : (term8 _27624 P t) = (term8 _27624 P t).
Proof. exact (eq_refl (term8 _27624 P t)). Qed.
Lemma lem1187265 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) : (term47 _27624 h P t) = (term42 _27624 h P t).
Proof. exact (MK_COMB (@lem1187263 _27624 P h) (@lem1187264 _27624 P t)). Qed.
Lemma lem1187268 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) : (term13 _27624 P h t) = (term42 _27624 h P t).
Proof. exact (TRANS (@lem1187246 _27624 h P t) (@lem1187265 _27624 h P t)). Qed.
Lemma lem1187269 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : ((term12 _27624 P h t) = (term13 _27624 P h t)) = ((term42 _27624 h P t) = (term42 _27624 h P t)).
Proof. exact (MK_COMB (@lem1187242 _27624 h P t h1) (@lem1187268 _27624 h P t)). Qed.
Lemma lem1187271 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1187272 (x : Prop) : (x = x) = True.
Proof. exact (@lem1187271 Prop x). Qed.
Lemma lem1187273 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) : ((term42 _27624 h P t) = (term42 _27624 h P t)) = True.
Proof. exact (@lem1187272 (term42 _27624 h P t)). Qed.
Lemma lem1187274 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : ((term12 _27624 P h t) = (term13 _27624 P h t)) = True.
Proof. exact (TRANS (@lem1187269 _27624 h P t h1) (@lem1187273 _27624 h P t)). Qed.
Lemma lem1187275 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : True = ((term12 _27624 P h t) = (term13 _27624 P h t)).
Proof. exact (SYM (@lem1187274 _27624 h P t h1)). Qed.
Lemma lem1187276 {_27624 : Type'} (h : _27624) (P : type1402 _27624) (t : list _27624) (h1 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t)) : (term12 _27624 P h t) = (term13 _27624 P h t).
Proof. exact (EQ_MP (@lem1187275 _27624 h P t h1) (@lem0)). Qed.
Lemma lem1187277 {_27624 : Type'} (P : type1402 _27624) (h : _27624) (t : list _27624) : term15 _27624 P h t.
Proof. exact (fun h0 : (@ALL2 _27624 _27624 P t t) = (term8 _27624 P t) => @lem1187276 _27624 h P t h0). Qed.
Lemma lem1187282 {_27624 : Type'} (P : type1402 _27624) (h : _27624) : term19 _27624 P h.
Proof. exact (fun t : list _27624 => @lem1187277 _27624 P h t). Qed.
Lemma lem1187287 {_27624 : Type'} (P : type1402 _27624) : term23 _27624 P.
Proof. exact (fun h : _27624 => @lem1187282 _27624 P h). Qed.
Lemma lem1187288 {_27624 : Type'} (P : type1402 _27624) : term25 _27624 P.
Proof. exact (conj (@lem1187217 _27624 P) (@lem1187287 _27624 P)). Qed.
Lemma lem1187289 {_27624 : Type'} (P : type1402 _27624) : term30 _27624 P.
Proof. exact (@lem1187190 _27624 P (@lem1187288 _27624 P)). Qed.
Lemma lem1187294 {_27624 : Type'} : term56 _27624.
Proof. exact (fun P : type1402 _27624 => @lem1187289 _27624 P). Qed.
