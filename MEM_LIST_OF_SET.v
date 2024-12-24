Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_LIST_OF_SET_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SET_OF_LIST_OF_SET_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm82_spec.
Lemma lem4788176 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4788177 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4788178 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4788177 A x) (@lem4788176 A x)). Qed.
Lemma lem4788179 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4788185 {_110305 : Type'} (s : _110305 -> Prop) : term3 _110305 s.
Proof. exact (@lem4787453 _110305 s). Qed.
Lemma lem4788186 {_110305 : Type'} (s : _110305 -> Prop) : (term3 _110305 s) = (term4 _110305 s).
Proof. exact (eq_refl (term3 _110305 s)). Qed.
Lemma lem4788188 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4788190 {_110305 : Type'} (s : _110305 -> Prop) : term4 _110305 s.
Proof. exact (EQ_MP (@lem4788186 _110305 s) (@lem4788185 _110305 s)). Qed.
Lemma lem4788191 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (@lem4788190 A s). Qed.
Lemma lem4788192 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term5 A s) = s.
Proof. exact (@lem4788191 A s (@lem4788188 A s h1)). Qed.
Lemma lem4788193 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : (term5 A s) = s.
Proof. exact (h1). Qed.
Lemma lem4788194 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : (term5 A s) = s.
Proof. exact (h1). Qed.
Lemma lem4788195 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : s = (term5 A s).
Proof. exact (SYM (@lem4788194 A s h1)). Qed.
Lemma lem4788196 {A : Type'} (s : A -> Prop) (h1 : s = (term5 A s)) : s = (term5 A s).
Proof. exact (h1). Qed.
Lemma lem4788197 {A : Type'} (s : A -> Prop) (h1 : s = (term5 A s)) : (term5 A s) = s.
Proof. exact (SYM (@lem4788196 A s h1)). Qed.
Lemma lem4788198 {A : Type'} (s : A -> Prop) : ((term5 A s) = s) = (s = (term5 A s)).
Proof. exact (prop_ext (fun h1 : (term5 A s) = s => @lem4788195 A s h1) (fun h1 : s = (term5 A s) => @lem4788197 A s h1)). Qed.
Lemma lem4788201 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : s = (term5 A s).
Proof. exact (EQ_MP (@lem4788198 A s) (@lem4788193 A s h1)). Qed.
Lemma lem4788202 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4788203 {A : Type'} (x : A) (s : A -> Prop) (h1 : (term5 A s) = s) : (@IN A x s) = (term6 A x s).
Proof. exact (MK_COMB (@lem4788202 A x) (@lem4788201 A s h1)). Qed.
Lemma lem4788204 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term7 A x s).
Proof. exact (eq_refl (term7 A x s)). Qed.
Lemma lem4788205 {A : Type'} (x : A) (s : A -> Prop) (h1 : (term5 A s) = s) : ((term8 A x s) = (@IN A x s)) = ((term8 A x s) = (term6 A x s)).
Proof. exact (MK_COMB (@lem4788204 A x s) (@lem4788203 A x s h1)). Qed.
Lemma lem4788206 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : (term9 A s) = (term10 A s).
Proof. exact (fun_ext (fun x : A => @lem4788205 A x s h1)). Qed.
Lemma lem4788207 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4788208 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem4788207 A) (@lem4788206 A s h1)). Qed.
Lemma lem4788209 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : (term12 A s) = (term11 A s).
Proof. exact (SYM (@lem4788208 A s h1)). Qed.
Lemma lem4788211 {A : Type'} (P : type1143 A) : term13 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4788212 {A : Type'} (P : type1143 A) : term13 A P.
Proof. exact (@lem4788211 A P). Qed.
Lemma lem4788213 {A : Type'} : term14 A.
Proof. exact (@lem4788212 A (term15 A)). Qed.
Lemma lem4788214 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem4788215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4788216 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem4788215) (@lem4788214 A)). Qed.
Lemma lem4788217 {A : Type'} (t : list A) : (term20 A t) = (term21 A t).
Proof. exact (eq_refl (term20 A t)). Qed.
Lemma lem4788218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788219 {A : Type'} (t : list A) : (term22 A t) = (term23 A t).
Proof. exact (MK_COMB (@lem4788218) (@lem4788217 A t)). Qed.
Lemma lem4788220 {A : Type'} (h : A) (t : list A) : (term24 A h t) = (term25 A h t).
Proof. exact (eq_refl (term24 A h t)). Qed.
Lemma lem4788221 {A : Type'} (h : A) (t : list A) : (term26 A h t) = (term27 A h t).
Proof. exact (MK_COMB (@lem4788219 A t) (@lem4788220 A h t)). Qed.
Lemma lem4788222 {A : Type'} (h : A) : (term28 A h) = (term29 A h).
Proof. exact (fun_ext (fun t : list A => @lem4788221 A h t)). Qed.
Lemma lem4788223 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4788224 {A : Type'} (h : A) : (term30 A h) = (term31 A h).
Proof. exact (MK_COMB (@lem4788223 A) (@lem4788222 A h)). Qed.
Lemma lem4788225 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (fun_ext (fun h : A => @lem4788224 A h)). Qed.
Lemma lem4788226 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4788227 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem4788226 A) (@lem4788225 A)). Qed.
Lemma lem4788228 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem4788216 A) (@lem4788227 A)). Qed.
Lemma lem4788229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4788230 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem4788229) (@lem4788228 A)). Qed.
Lemma lem4788231 {A : Type'} (l : list A) : (term20 A l) = (term21 A l).
Proof. exact (eq_refl (term20 A l)). Qed.
Lemma lem4788232 {A : Type'} : (term40 A) = (term15 A).
Proof. exact (fun_ext (fun l : list A => @lem4788231 A l)). Qed.
Lemma lem4788233 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem4788234 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (MK_COMB (@lem4788233 A) (@lem4788232 A)). Qed.
Lemma lem4788235 {A : Type'} : (term14 A) = (term43 A).
Proof. exact (MK_COMB (@lem4788230 A) (@lem4788234 A)). Qed.
Lemma lem4788236 {A : Type'} : term43 A.
Proof. exact (EQ_MP (@lem4788235 A) (@lem4788213 A)). Qed.
Lemma lem4788237 {A : Type'} (t : list A) (h1 : term21 A t) : term21 A t.
Proof. exact (h1). Qed.
Lemma lem4788245 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem4788246 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem4788245 A x). Qed.
Lemma lem4788247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788248 {A : Type'} (x : A) : (term44 A x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4788247) (@lem4788246 A x)). Qed.
Lemma lem4788250 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4788251 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4788252 {A : Type'} (x : A) : (term45 A x) = (@IN A x (@EMPTY A)).
Proof. exact (MK_COMB (@lem4788251 A x) (@lem4788250 A)). Qed.
Lemma lem4788254 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4788179 A x (@lem4788178 A x)). Qed.
Lemma lem4788255 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4788254 A x). Qed.
Lemma lem4788256 {A : Type'} (x : A) : (term45 A x) = False.
Proof. exact (TRANS (@lem4788252 A x) (@lem4788255 A x)). Qed.
Lemma lem4788257 {A : Type'} (x : A) : ((@List.In A x (@nil A)) = (term45 A x)) = (False = False).
Proof. exact (MK_COMB (@lem4788248 A x) (@lem4788256 A x)). Qed.
Lemma lem4788259 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4788260 : (False = False) = (~ False).
Proof. exact (@lem4788259 False). Qed.
Lemma lem4788262 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4788263 : (False = False) = True.
Proof. exact (TRANS (@lem4788260) (@lem4788262)). Qed.
Lemma lem4788264 {A : Type'} (x : A) : ((@List.In A x (@nil A)) = (term45 A x)) = True.
Proof. exact (TRANS (@lem4788257 A x) (@lem4788263)). Qed.
Lemma lem4788265 {A : Type'} : (term46 A) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem4788264 A x)). Qed.
Lemma lem4788266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4788267 {A : Type'} : (term17 A) = (term48 A).
Proof. exact (MK_COMB (@lem4788266 A) (@lem4788265 A)). Qed.
Lemma lem4788269 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4788270 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (@lem4788269 A t). Qed.
Lemma lem4788271 {A : Type'} : (term48 A) = True.
Proof. exact (@lem4788270 A True). Qed.
Lemma lem4788272 {A : Type'} : (term17 A) = True.
Proof. exact (TRANS (@lem4788267 A) (@lem4788271 A)). Qed.
Lemma lem4788273 {A : Type'} : True = (term17 A).
Proof. exact (SYM (@lem4788272 A)). Qed.
Lemma lem4788274 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem4788273 A) (@lem0)). Qed.
Lemma lem4788282 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term50 _25376 x h t) = (term51 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem4788283 {A : Type'} (h : A) (x : A) (t : list A) : (term50 A x h t) = (term51 A h x t).
Proof. exact (@lem4788282 A h x t). Qed.
Lemma lem4788288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788289 {A : Type'} (h : A) (x : A) (t : list A) : (term52 A x h t) = (term53 A h x t).
Proof. exact (MK_COMB (@lem4788288) (@lem4788283 A h x t)). Qed.
Lemma lem4788291 {A : Type'} (h : A) (t : list A) : (term54 A h t) = (term55 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4788292 {A : Type'} (h : A) (t : list A) : (term54 A h t) = (term55 A h t).
Proof. exact (@lem4788291 A h t). Qed.
Lemma lem4788293 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4788294 {A : Type'} (x : A) (h : A) (t : list A) : (term56 A x h t) = (term57 A x h t).
Proof. exact (MK_COMB (@lem4788293 A x) (@lem4788292 A h t)). Qed.
Lemma lem4788295 {A : Type'} (x : A) (h : A) (t : list A) : ((term50 A x h t) = (term56 A x h t)) = ((term51 A h x t) = (term57 A x h t)).
Proof. exact (MK_COMB (@lem4788289 A h x t) (@lem4788294 A x h t)). Qed.
Lemma lem4788298 {A : Type'} (h : A) (t : list A) : (term58 A h t) = (term59 A h t).
Proof. exact (fun_ext (fun x : A => @lem4788295 A x h t)). Qed.
Lemma lem4788299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4788300 {A : Type'} (h : A) (t : list A) : (term25 A h t) = (term60 A h t).
Proof. exact (MK_COMB (@lem4788299 A) (@lem4788298 A h t)). Qed.
Lemma lem4788305 {A : Type'} (h : A) (t : list A) : (term60 A h t) = (term25 A h t).
Proof. exact (SYM (@lem4788300 A h t)). Qed.
Lemma lem4788306 {A : Type'} (x : A) : term61 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4788307 {A : Type'} (x : A) : (term61 A x) = (term62 A x).
Proof. exact (eq_refl (term61 A x)). Qed.
Lemma lem4788308 {A : Type'} (x : A) : term62 A x.
Proof. exact (EQ_MP (@lem4788307 A x) (@lem4788306 A x)). Qed.
Lemma lem4788309 {A : Type'} (x : A) (y : A) : term63 A x y.
Proof. exact (@lem4788308 A x y). Qed.
Lemma lem4788310 {A : Type'} (y : A) (x : A) : (term63 A x y) = (term64 A y x).
Proof. exact (eq_refl (term63 A x y)). Qed.
Lemma lem4788311 {A : Type'} (y : A) (x : A) : term64 A y x.
Proof. exact (EQ_MP (@lem4788310 A y x) (@lem4788309 A x y)). Qed.
Lemma lem4788312 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term65 A y x s.
Proof. exact (@lem4788311 A y x s). Qed.
Lemma lem4788313 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term65 A y x s) = ((term66 A x y s) = (term67 A y x s)).
Proof. exact (eq_refl (term65 A y x s)). Qed.
Lemma lem4788315 {A : Type'} (x : A) (t : list A) (h1 : term21 A t) : term68 A t x.
Proof. exact (@lem4788237 A t h1 x). Qed.
Lemma lem4788316 {A : Type'} (x : A) (t : list A) : (term68 A t x) = ((@List.In A x t) = (term69 A x t)).
Proof. exact (eq_refl (term68 A t x)). Qed.
Lemma lem4788329 {A : Type'} (x : A) (t : list A) (h1 : term21 A t) : (@List.In A x t) = (term69 A x t).
Proof. exact (EQ_MP (@lem4788316 A x t) (@lem4788315 A x t h1)). Qed.
Lemma lem4788330 {A : Type'} (x : A) (t : list A) (h1 : term21 A t) : (@List.In A x t) = (term69 A x t).
Proof. exact (@lem4788329 A x t h1). Qed.
Lemma lem4788331 {A : Type'} (x : A) (h : A) : (term70 A x h) = (term70 A x h).
Proof. exact (eq_refl (term70 A x h)). Qed.
Lemma lem4788332 {A : Type'} (h : A) (x : A) (t : list A) (h1 : term21 A t) : (term51 A h x t) = (term71 A h x t).
Proof. exact (MK_COMB (@lem4788331 A x h) (@lem4788330 A x t h1)). Qed.
Lemma lem4788335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4788336 {A : Type'} (h : A) (x : A) (t : list A) (h1 : term21 A t) : (term53 A h x t) = (term72 A h x t).
Proof. exact (MK_COMB (@lem4788335) (@lem4788332 A h x t h1)). Qed.
Lemma lem4788338 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term66 A x y s) = (term67 A y x s).
Proof. exact (EQ_MP (@lem4788313 A y x s) (@lem4788312 A y x s)). Qed.
Lemma lem4788339 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term66 A x y s) = (term67 A y x s).
Proof. exact (@lem4788338 A y x s). Qed.
Lemma lem4788340 {A : Type'} (h : A) (x : A) (t : list A) : (term57 A x h t) = (term71 A h x t).
Proof. exact (@lem4788339 A h x (@set_of_list A t)). Qed.
Lemma lem4788345 {A : Type'} (h : A) (x : A) (t : list A) (h1 : term21 A t) : ((term51 A h x t) = (term57 A x h t)) = ((term71 A h x t) = (term71 A h x t)).
Proof. exact (MK_COMB (@lem4788336 A h x t h1) (@lem4788340 A h x t)). Qed.
Lemma lem4788347 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4788348 (x : Prop) : (x = x) = True.
Proof. exact (@lem4788347 Prop x). Qed.
Lemma lem4788349 {A : Type'} (h : A) (x : A) (t : list A) : ((term71 A h x t) = (term71 A h x t)) = True.
Proof. exact (@lem4788348 (term71 A h x t)). Qed.
Lemma lem4788350 {A : Type'} (x : A) (h : A) (t : list A) (h1 : term21 A t) : ((term51 A h x t) = (term57 A x h t)) = True.
Proof. exact (TRANS (@lem4788345 A h x t h1) (@lem4788349 A h x t)). Qed.
Lemma lem4788351 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : (term59 A h t) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem4788350 A x h t h1)). Qed.
Lemma lem4788352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4788353 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : (term60 A h t) = (term48 A).
Proof. exact (MK_COMB (@lem4788352 A) (@lem4788351 A h t h1)). Qed.
Lemma lem4788355 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4788356 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (@lem4788355 A t). Qed.
Lemma lem4788357 {A : Type'} : (term48 A) = True.
Proof. exact (@lem4788356 A True). Qed.
Lemma lem4788358 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : (term60 A h t) = True.
Proof. exact (TRANS (@lem4788353 A h t h1) (@lem4788357 A)). Qed.
Lemma lem4788359 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : True = (term60 A h t).
Proof. exact (SYM (@lem4788358 A h t h1)). Qed.
Lemma lem4788360 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : term60 A h t.
Proof. exact (EQ_MP (@lem4788359 A h t h1) (@lem0)). Qed.
Lemma lem4788361 {A : Type'} (h : A) (t : list A) (h1 : term21 A t) : term25 A h t.
Proof. exact (EQ_MP (@lem4788305 A h t) (@lem4788360 A h t h1)). Qed.
Lemma lem4788362 {A : Type'} (h : A) (t : list A) : term27 A h t.
Proof. exact (fun h0 : term21 A t => @lem4788361 A h t h0). Qed.
Lemma lem4788367 {A : Type'} (h : A) : term31 A h.
Proof. exact (fun t : list A => @lem4788362 A h t). Qed.
Lemma lem4788372 {A : Type'} : term35 A.
Proof. exact (fun h : A => @lem4788367 A h). Qed.
Lemma lem4788373 {A : Type'} : term37 A.
Proof. exact (conj (@lem4788274 A) (@lem4788372 A)). Qed.
Lemma lem4788374 {A : Type'} : term42 A.
Proof. exact (@lem4788236 A (@lem4788373 A)). Qed.
Lemma lem4788375 {A : Type'} (s : A -> Prop) : term73 A s.
Proof. exact (@lem4788374 A (@list_of_set A s)). Qed.
Lemma lem4788376 {A : Type'} (s : A -> Prop) : (term73 A s) = (term12 A s).
Proof. exact (eq_refl (term73 A s)). Qed.
Lemma lem4788377 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem4788376 A s) (@lem4788375 A s)). Qed.
Lemma lem4788378 {A : Type'} (s : A -> Prop) (h1 : (term5 A s) = s) : term11 A s.
Proof. exact (EQ_MP (@lem4788209 A s h1) (@lem4788377 A s)). Qed.
Lemma lem4788379 {A : Type'} (s : A -> Prop) : term74 A s.
Proof. exact (fun h0 : (term5 A s) = s => @lem4788378 A s h0). Qed.
Lemma lem4788380 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term11 A s.
Proof. exact (@lem4788379 A s (@lem4788192 A s h1)). Qed.
Lemma lem4788381 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (fun h0 : @FINITE A s => @lem4788380 A s h0). Qed.
Lemma lem4788386 {A : Type'} : term76 A.
Proof. exact (fun s : A -> Prop => @lem4788381 A s). Qed.
