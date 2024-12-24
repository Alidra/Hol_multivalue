Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_APPEND_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1160195 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1160196 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem1160195 t1 t2 t3 h1)). Qed.
Lemma lem1160197 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1160198 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem1160197 t1 t2 t3 h1)). Qed.
Lemma lem1160199 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem1160196 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem1160198 t1 t2 t3 h1)). Qed.
Lemma lem1160200 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem1160199 t1 t2 t3)). Qed.
Lemma lem1160201 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1160202 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem1160201) (@lem1160200 t1 t2)). Qed.
Lemma lem1160203 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1160202 t1 t2)). Qed.
Lemma lem1160204 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1160205 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem1160204) (@lem1160203 t1)). Qed.
Lemma lem1160206 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem1160205 t1)). Qed.
Lemma lem1160207 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1160208 : term12 = term13.
Proof. exact (MK_COMB (@lem1160207) (@lem1160206)). Qed.
Lemma lem1160209 : term13.
Proof. exact (EQ_MP (@lem1160208) (@lem512)). Qed.
Lemma lem1160211 {A : Type'} (P : type1143 A) : term14 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1160212 {_27241 : Type'} (P : type1143 _27241) : term14 _27241 P.
Proof. exact (@lem1160211 _27241 P). Qed.
Lemma lem1160213 {_27241 : Type'} (P : _27241 -> Prop) : term15 _27241 P.
Proof. exact (@lem1160212 _27241 (term16 _27241 P)). Qed.
Lemma lem1160214 {_27241 : Type'} (P : _27241 -> Prop) : (term17 _27241 P) = (term18 _27241 P).
Proof. exact (eq_refl (term17 _27241 P)). Qed.
Lemma lem1160215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1160216 {_27241 : Type'} (P : _27241 -> Prop) : (term19 _27241 P) = (term20 _27241 P).
Proof. exact (MK_COMB (@lem1160215) (@lem1160214 _27241 P)). Qed.
Lemma lem1160217 {_27241 : Type'} (t : list _27241) (P : _27241 -> Prop) : (term21 _27241 P t) = (term22 _27241 t P).
Proof. exact (eq_refl (term21 _27241 P t)). Qed.
Lemma lem1160218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160219 {_27241 : Type'} (t : list _27241) (P : _27241 -> Prop) : (term23 _27241 P t) = (term24 _27241 t P).
Proof. exact (MK_COMB (@lem1160218) (@lem1160217 _27241 t P)). Qed.
Lemma lem1160220 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) : (term25 _27241 P h t) = (term26 _27241 h t P).
Proof. exact (eq_refl (term25 _27241 P h t)). Qed.
Lemma lem1160221 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) : (term27 _27241 P h t) = (term28 _27241 h t P).
Proof. exact (MK_COMB (@lem1160219 _27241 t P) (@lem1160220 _27241 h t P)). Qed.
Lemma lem1160222 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) : (term29 _27241 P h) = (term30 _27241 h P).
Proof. exact (fun_ext (fun t : list _27241 => @lem1160221 _27241 h t P)). Qed.
Lemma lem1160223 {_27241 : Type'} : (@all (list _27241)) = (@all (list _27241)).
Proof. exact (eq_refl (@all (list _27241))). Qed.
Lemma lem1160224 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) : (term31 _27241 P h) = (term32 _27241 h P).
Proof. exact (MK_COMB (@lem1160223 _27241) (@lem1160222 _27241 h P)). Qed.
Lemma lem1160225 {_27241 : Type'} (P : _27241 -> Prop) : (term33 _27241 P) = (term34 _27241 P).
Proof. exact (fun_ext (fun h : _27241 => @lem1160224 _27241 h P)). Qed.
Lemma lem1160226 {_27241 : Type'} : (@all _27241) = (@all _27241).
Proof. exact (eq_refl (@all _27241)). Qed.
Lemma lem1160227 {_27241 : Type'} (P : _27241 -> Prop) : (term35 _27241 P) = (term36 _27241 P).
Proof. exact (MK_COMB (@lem1160226 _27241) (@lem1160225 _27241 P)). Qed.
Lemma lem1160228 {_27241 : Type'} (P : _27241 -> Prop) : (term37 _27241 P) = (term38 _27241 P).
Proof. exact (MK_COMB (@lem1160216 _27241 P) (@lem1160227 _27241 P)). Qed.
Lemma lem1160229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1160230 {_27241 : Type'} (P : _27241 -> Prop) : (term39 _27241 P) = (term40 _27241 P).
Proof. exact (MK_COMB (@lem1160229) (@lem1160228 _27241 P)). Qed.
Lemma lem1160231 {_27241 : Type'} (l1 : list _27241) (P : _27241 -> Prop) : (term21 _27241 P l1) = (term22 _27241 l1 P).
Proof. exact (eq_refl (term21 _27241 P l1)). Qed.
Lemma lem1160232 {_27241 : Type'} (P : _27241 -> Prop) : (term41 _27241 P) = (term16 _27241 P).
Proof. exact (fun_ext (fun l1 : list _27241 => @lem1160231 _27241 l1 P)). Qed.
Lemma lem1160233 {_27241 : Type'} : (@all (list _27241)) = (@all (list _27241)).
Proof. exact (eq_refl (@all (list _27241))). Qed.
Lemma lem1160234 {_27241 : Type'} (P : _27241 -> Prop) : (term42 _27241 P) = (term43 _27241 P).
Proof. exact (MK_COMB (@lem1160233 _27241) (@lem1160232 _27241 P)). Qed.
Lemma lem1160235 {_27241 : Type'} (P : _27241 -> Prop) : (term15 _27241 P) = (term44 _27241 P).
Proof. exact (MK_COMB (@lem1160230 _27241 P) (@lem1160234 _27241 P)). Qed.
Lemma lem1160236 {_27241 : Type'} (P : _27241 -> Prop) : term44 _27241 P.
Proof. exact (EQ_MP (@lem1160235 _27241 P) (@lem1160213 _27241 P)). Qed.
Lemma lem1160237 {_27241 : Type'} (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : term22 _27241 t P.
Proof. exact (h1). Qed.
Lemma lem1160257 {A : Type'} : term45 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1160258 {A : Type'} (l : list A) : term46 A l.
Proof. exact (@lem1160257 A l). Qed.
Lemma lem1160259 {A : Type'} (l : list A) : (term46 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term46 A l)). Qed.
Lemma lem1160270 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1160259 A l) (@lem1160258 A l)). Qed.
Lemma lem1160271 {_27241 : Type'} (l : list _27241) : (@List.app _27241 (@nil _27241) l) = l.
Proof. exact (@lem1160270 _27241 l). Qed.
Lemma lem1160272 {_27241 : Type'} (l2 : list _27241) : (@List.app _27241 (@nil _27241) l2) = l2.
Proof. exact (@lem1160271 _27241 l2). Qed.
Lemma lem1160273 {_27241 : Type'} (P : _27241 -> Prop) : (@List.Forall _27241 P) = (@List.Forall _27241 P).
Proof. exact (eq_refl (@List.Forall _27241 P)). Qed.
Lemma lem1160274 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (term47 _27241 P l2) = (@List.Forall _27241 P l2).
Proof. exact (MK_COMB (@lem1160273 _27241 P) (@lem1160272 _27241 l2)). Qed.
Lemma lem1160275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1160276 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (term48 _27241 P l2) = (term49 _27241 P l2).
Proof. exact (MK_COMB (@lem1160275) (@lem1160274 _27241 P l2)). Qed.
Lemma lem1160280 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1160281 {_27241 : Type'} (P : _27241 -> Prop) : (@List.Forall _27241 P (@nil _27241)) = True.
Proof. exact (@lem1160280 _27241 P). Qed.
Lemma lem1160282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1160283 {_27241 : Type'} (P : _27241 -> Prop) : (term50 _27241 P) = (and True).
Proof. exact (MK_COMB (@lem1160282) (@lem1160281 _27241 P)). Qed.
Lemma lem1160284 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (@List.Forall _27241 P l2) = (@List.Forall _27241 P l2).
Proof. exact (eq_refl (@List.Forall _27241 P l2)). Qed.
Lemma lem1160285 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (term51 _27241 P l2) = (term52 _27241 P l2).
Proof. exact (MK_COMB (@lem1160283 _27241 P) (@lem1160284 _27241 P l2)). Qed.
Lemma lem1160287 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1160288 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (term52 _27241 P l2) = (@List.Forall _27241 P l2).
Proof. exact (@lem1160287 (@List.Forall _27241 P l2)). Qed.
Lemma lem1160289 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (term51 _27241 P l2) = (@List.Forall _27241 P l2).
Proof. exact (TRANS (@lem1160285 _27241 P l2) (@lem1160288 _27241 P l2)). Qed.
Lemma lem1160290 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : ((term47 _27241 P l2) = (term51 _27241 P l2)) = ((@List.Forall _27241 P l2) = (@List.Forall _27241 P l2)).
Proof. exact (MK_COMB (@lem1160276 _27241 P l2) (@lem1160289 _27241 P l2)). Qed.
Lemma lem1160292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1160293 (x : Prop) : (x = x) = True.
Proof. exact (@lem1160292 Prop x). Qed.
Lemma lem1160294 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : ((@List.Forall _27241 P l2) = (@List.Forall _27241 P l2)) = True.
Proof. exact (@lem1160293 (@List.Forall _27241 P l2)). Qed.
Lemma lem1160295 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : ((term47 _27241 P l2) = (term51 _27241 P l2)) = True.
Proof. exact (TRANS (@lem1160290 _27241 P l2) (@lem1160294 _27241 P l2)). Qed.
Lemma lem1160296 {_27241 : Type'} (P : _27241 -> Prop) : (term53 _27241 P) = (term54 _27241).
Proof. exact (fun_ext (fun l2 : list _27241 => @lem1160295 _27241 P l2)). Qed.
Lemma lem1160297 {_27241 : Type'} : (@all (list _27241)) = (@all (list _27241)).
Proof. exact (eq_refl (@all (list _27241))). Qed.
Lemma lem1160298 {_27241 : Type'} (P : _27241 -> Prop) : (term18 _27241 P) = (term55 _27241).
Proof. exact (MK_COMB (@lem1160297 _27241) (@lem1160296 _27241 P)). Qed.
Lemma lem1160300 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1160301 {_27241 : Type'} (t : Prop) : (term57 _27241 t) = t.
Proof. exact (@lem1160300 (list _27241) t). Qed.
Lemma lem1160302 {_27241 : Type'} : (term55 _27241) = True.
Proof. exact (@lem1160301 _27241 True). Qed.
Lemma lem1160303 {_27241 : Type'} (P : _27241 -> Prop) : (term18 _27241 P) = True.
Proof. exact (TRANS (@lem1160298 _27241 P) (@lem1160302 _27241)). Qed.
Lemma lem1160304 {_27241 : Type'} (P : _27241 -> Prop) : True = (term18 _27241 P).
Proof. exact (SYM (@lem1160303 _27241 P)). Qed.
Lemma lem1160305 {_27241 : Type'} (P : _27241 -> Prop) : term18 _27241 P.
Proof. exact (EQ_MP (@lem1160304 _27241 P) (@lem0)). Qed.
Lemma lem1160306 (t1 : Prop) : term58 t1.
Proof. exact (@lem1160209 t1). Qed.
Lemma lem1160307 (t1 : Prop) : (term58 t1) = (term9 t1).
Proof. exact (eq_refl (term58 t1)). Qed.
Lemma lem1160308 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem1160307 t1) (@lem1160306 t1)). Qed.
Lemma lem1160309 (t1 : Prop) (t2 : Prop) : term59 t1 t2.
Proof. exact (@lem1160308 t1 t2). Qed.
Lemma lem1160310 (t1 : Prop) (t2 : Prop) : (term59 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term59 t1 t2)). Qed.
Lemma lem1160311 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem1160310 t1 t2) (@lem1160309 t1 t2)). Qed.
Lemma lem1160312 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term60 t1 t2 t3.
Proof. exact (@lem1160311 t1 t2 t3). Qed.
Lemma lem1160313 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term60 t1 t2 t3)). Qed.
Lemma lem1160315 {A : Type'} : term61 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1160316 {A : Type'} (h : A) : term62 A h.
Proof. exact (@lem1160315 A h). Qed.
Lemma lem1160317 {A : Type'} (h : A) : (term62 A h) = (term63 A h).
Proof. exact (eq_refl (term62 A h)). Qed.
Lemma lem1160318 {A : Type'} (h : A) : term63 A h.
Proof. exact (EQ_MP (@lem1160317 A h) (@lem1160316 A h)). Qed.
Lemma lem1160319 {A : Type'} (h : A) (t : list A) : term64 A h t.
Proof. exact (@lem1160318 A h t). Qed.
Lemma lem1160320 {A : Type'} (h : A) (t : list A) : (term64 A h t) = (term65 A h t).
Proof. exact (eq_refl (term64 A h t)). Qed.
Lemma lem1160321 {A : Type'} (h : A) (t : list A) : term65 A h t.
Proof. exact (EQ_MP (@lem1160320 A h t) (@lem1160319 A h t)). Qed.
Lemma lem1160322 {A : Type'} (h : A) (t : list A) (l : list A) : term66 A h t l.
Proof. exact (@lem1160321 A h t l). Qed.
Lemma lem1160323 {A : Type'} (h : A) (t : list A) (l : list A) : (term66 A h t l) = ((term67 A h t l) = (term68 A h t l)).
Proof. exact (eq_refl (term66 A h t l)). Qed.
Lemma lem1160331 {_27241 : Type'} (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : term69 _27241 t P l2.
Proof. exact (@lem1160237 _27241 t P h1 l2). Qed.
Lemma lem1160332 {_27241 : Type'} (t : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term69 _27241 t P l2) = ((term70 _27241 P t l2) = (term71 _27241 t P l2)).
Proof. exact (eq_refl (term69 _27241 t P l2)). Qed.
Lemma lem1160341 {A : Type'} (h : A) (t : list A) (l : list A) : (term67 A h t l) = (term68 A h t l).
Proof. exact (EQ_MP (@lem1160323 A h t l) (@lem1160322 A h t l)). Qed.
Lemma lem1160342 {_27241 : Type'} (h : _27241) (t : list _27241) (l : list _27241) : (term67 _27241 h t l) = (term68 _27241 h t l).
Proof. exact (@lem1160341 _27241 h t l). Qed.
Lemma lem1160343 {_27241 : Type'} (h : _27241) (t : list _27241) (l2 : list _27241) : (term67 _27241 h t l2) = (term68 _27241 h t l2).
Proof. exact (@lem1160342 _27241 h t l2). Qed.
Lemma lem1160344 {_27241 : Type'} (P : _27241 -> Prop) : (@List.Forall _27241 P) = (@List.Forall _27241 P).
Proof. exact (eq_refl (@List.Forall _27241 P)). Qed.
Lemma lem1160345 {_27241 : Type'} (P : _27241 -> Prop) (h : _27241) (t : list _27241) (l2 : list _27241) : (term72 _27241 P h t l2) = (term73 _27241 P h t l2).
Proof. exact (MK_COMB (@lem1160344 _27241 P) (@lem1160343 _27241 h t l2)). Qed.
Lemma lem1160347 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term74 _25307 P h t) = (term75 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1160348 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) (t : list _27241) : (term74 _27241 P h t) = (term75 _27241 h P t).
Proof. exact (@lem1160347 _27241 h P t). Qed.
Lemma lem1160349 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) (t : list _27241) (l2 : list _27241) : (term73 _27241 P h t l2) = (term76 _27241 h P t l2).
Proof. exact (@lem1160348 _27241 h P (@List.app _27241 t l2)). Qed.
Lemma lem1160353 {_27241 : Type'} (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term70 _27241 P t l2) = (term71 _27241 t P l2).
Proof. exact (EQ_MP (@lem1160332 _27241 t P l2) (@lem1160331 _27241 l2 t P h1)). Qed.
Lemma lem1160354 {_27241 : Type'} (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term70 _27241 P t l2) = (term71 _27241 t P l2).
Proof. exact (@lem1160353 _27241 l2 t P h1). Qed.
Lemma lem1160357 {_27241 : Type'} (P : _27241 -> Prop) (h : _27241) : (term77 _27241 P h) = (term77 _27241 P h).
Proof. exact (eq_refl (term77 _27241 P h)). Qed.
Lemma lem1160358 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term76 _27241 h P t l2) = (term78 _27241 h t P l2).
Proof. exact (MK_COMB (@lem1160357 _27241 P h) (@lem1160354 _27241 l2 t P h1)). Qed.
Lemma lem1160361 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term73 _27241 P h t l2) = (term78 _27241 h t P l2).
Proof. exact (TRANS (@lem1160349 _27241 h P t l2) (@lem1160358 _27241 h l2 t P h1)). Qed.
Lemma lem1160362 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term72 _27241 P h t l2) = (term78 _27241 h t P l2).
Proof. exact (TRANS (@lem1160345 _27241 P h t l2) (@lem1160361 _27241 h l2 t P h1)). Qed.
Lemma lem1160363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1160364 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term79 _27241 P h t l2) = (term80 _27241 h t P l2).
Proof. exact (MK_COMB (@lem1160363) (@lem1160362 _27241 h l2 t P h1)). Qed.
Lemma lem1160368 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term74 _25307 P h t) = (term75 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1160369 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) (t : list _27241) : (term74 _27241 P h t) = (term75 _27241 h P t).
Proof. exact (@lem1160368 _27241 h P t). Qed.
Lemma lem1160372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1160373 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) (t : list _27241) : (term81 _27241 P h t) = (term82 _27241 h P t).
Proof. exact (MK_COMB (@lem1160372) (@lem1160369 _27241 h P t)). Qed.
Lemma lem1160374 {_27241 : Type'} (P : _27241 -> Prop) (l2 : list _27241) : (@List.Forall _27241 P l2) = (@List.Forall _27241 P l2).
Proof. exact (eq_refl (@List.Forall _27241 P l2)). Qed.
Lemma lem1160375 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term83 _27241 h t P l2) = (term84 _27241 h t P l2).
Proof. exact (MK_COMB (@lem1160373 _27241 h P t) (@lem1160374 _27241 P l2)). Qed.
Lemma lem1160377 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem1160313 t1 t2 t3) (@lem1160312 t1 t2 t3)). Qed.
Lemma lem1160378 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term84 _27241 h t P l2) = (term78 _27241 h t P l2).
Proof. exact (@lem1160377 (P h) (@List.Forall _27241 P t) (@List.Forall _27241 P l2)). Qed.
Lemma lem1160383 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : (term83 _27241 h t P l2) = (term78 _27241 h t P l2).
Proof. exact (TRANS (@lem1160375 _27241 h t P l2) (@lem1160378 _27241 h t P l2)). Qed.
Lemma lem1160384 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : ((term72 _27241 P h t l2) = (term83 _27241 h t P l2)) = ((term78 _27241 h t P l2) = (term78 _27241 h t P l2)).
Proof. exact (MK_COMB (@lem1160364 _27241 h l2 t P h1) (@lem1160383 _27241 h t P l2)). Qed.
Lemma lem1160386 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1160387 (x : Prop) : (x = x) = True.
Proof. exact (@lem1160386 Prop x). Qed.
Lemma lem1160388 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (l2 : list _27241) : ((term78 _27241 h t P l2) = (term78 _27241 h t P l2)) = True.
Proof. exact (@lem1160387 (term78 _27241 h t P l2)). Qed.
Lemma lem1160389 {_27241 : Type'} (h : _27241) (l2 : list _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : ((term72 _27241 P h t l2) = (term83 _27241 h t P l2)) = True.
Proof. exact (TRANS (@lem1160384 _27241 h l2 t P h1) (@lem1160388 _27241 h t P l2)). Qed.
Lemma lem1160390 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term85 _27241 h t P) = (term54 _27241).
Proof. exact (fun_ext (fun l2 : list _27241 => @lem1160389 _27241 h l2 t P h1)). Qed.
Lemma lem1160391 {_27241 : Type'} : (@all (list _27241)) = (@all (list _27241)).
Proof. exact (eq_refl (@all (list _27241))). Qed.
Lemma lem1160392 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term26 _27241 h t P) = (term55 _27241).
Proof. exact (MK_COMB (@lem1160391 _27241) (@lem1160390 _27241 h t P h1)). Qed.
Lemma lem1160394 {A : Type'} (t : Prop) : (term56 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1160395 {_27241 : Type'} (t : Prop) : (term57 _27241 t) = t.
Proof. exact (@lem1160394 (list _27241) t). Qed.
Lemma lem1160396 {_27241 : Type'} : (term55 _27241) = True.
Proof. exact (@lem1160395 _27241 True). Qed.
Lemma lem1160397 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : (term26 _27241 h t P) = True.
Proof. exact (TRANS (@lem1160392 _27241 h t P h1) (@lem1160396 _27241)). Qed.
Lemma lem1160398 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : True = (term26 _27241 h t P).
Proof. exact (SYM (@lem1160397 _27241 h t P h1)). Qed.
Lemma lem1160399 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) (h1 : term22 _27241 t P) : term26 _27241 h t P.
Proof. exact (EQ_MP (@lem1160398 _27241 h t P h1) (@lem0)). Qed.
Lemma lem1160400 {_27241 : Type'} (h : _27241) (t : list _27241) (P : _27241 -> Prop) : term28 _27241 h t P.
Proof. exact (fun h0 : term22 _27241 t P => @lem1160399 _27241 h t P h0). Qed.
Lemma lem1160405 {_27241 : Type'} (h : _27241) (P : _27241 -> Prop) : term32 _27241 h P.
Proof. exact (fun t : list _27241 => @lem1160400 _27241 h t P). Qed.
Lemma lem1160410 {_27241 : Type'} (P : _27241 -> Prop) : term36 _27241 P.
Proof. exact (fun h : _27241 => @lem1160405 _27241 h P). Qed.
Lemma lem1160411 {_27241 : Type'} (P : _27241 -> Prop) : term38 _27241 P.
Proof. exact (conj (@lem1160305 _27241 P) (@lem1160410 _27241 P)). Qed.
Lemma lem1160412 {_27241 : Type'} (P : _27241 -> Prop) : term43 _27241 P.
Proof. exact (@lem1160236 _27241 P (@lem1160411 _27241 P)). Qed.
Lemma lem1160417 {_27241 : Type'} : term86 _27241.
Proof. exact (fun P : _27241 -> Prop => @lem1160412 _27241 P). Qed.
