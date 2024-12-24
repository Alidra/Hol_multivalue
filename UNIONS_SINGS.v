Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_SINGS_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem3465207 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem3465208 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term1 _89520 _89534 P.
Proof. exact (@lem3465207 _89520 _89534 P). Qed.
Lemma lem3465209 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term1 _89520 _89534 P) = (term2 _89520 _89534 P).
Proof. exact (eq_refl (term1 _89520 _89534 P)). Qed.
Lemma lem3465210 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term2 _89520 _89534 P.
Proof. exact (EQ_MP (@lem3465209 _89520 _89534 P) (@lem3465208 _89520 _89534 P)). Qed.
Lemma lem3465211 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term3 _89520 _89534 P f.
Proof. exact (@lem3465210 _89520 _89534 P f). Qed.
Lemma lem3465212 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term3 _89520 _89534 P f) = ((term4 _89520 _89534 P f) = (term5 _89520 _89534 P f)).
Proof. exact (eq_refl (term3 _89520 _89534 P f)). Qed.
Lemma lem3465221 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term4 _89520 _89534 P f) = (term5 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem3465212 _89520 _89534 P f) (@lem3465211 _89520 _89534 P f)). Qed.
Lemma lem3465222 {A : Type'} (P : A -> Prop) (f : type1402 A) : (term6 A P f) = (term7 A P f).
Proof. exact (@lem3465221 A A P f). Qed.
Lemma lem3465223 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (@lem3465222 A (term10 A s) (term11 A)). Qed.
Lemma lem3465224 {A : Type'} (x : A) (s : A -> Prop) : (term12 A s x) = (@IN A x s).
Proof. exact (eq_refl (term12 A s x)). Qed.
Lemma lem3465225 {A : Type'} (GEN_PVAR_63 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_63) = (@SETSPEC (A -> Prop) GEN_PVAR_63).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_63)). Qed.
Lemma lem3465226 {A : Type'} (GEN_PVAR_63 : A -> Prop) (x : A) (s : A -> Prop) : (term13 A GEN_PVAR_63 s x) = (term14 A GEN_PVAR_63 x s).
Proof. exact (MK_COMB (@lem3465225 A GEN_PVAR_63) (@lem3465224 A x s)). Qed.
Lemma lem3465227 {A : Type'} (x : A) : (term15 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term15 A x)). Qed.
Lemma lem3465228 {A : Type'} (GEN_PVAR_63 : A -> Prop) (s : A -> Prop) (x : A) : (term16 A GEN_PVAR_63 s x) = (term17 A GEN_PVAR_63 s x).
Proof. exact (MK_COMB (@lem3465226 A GEN_PVAR_63 x s) (@lem3465227 A x)). Qed.
Lemma lem3465229 {A : Type'} (GEN_PVAR_63 : A -> Prop) (s : A -> Prop) : (term18 A GEN_PVAR_63 s) = (term19 A GEN_PVAR_63 s).
Proof. exact (fun_ext (fun x : A => @lem3465228 A GEN_PVAR_63 s x)). Qed.
Lemma lem3465230 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465231 {A : Type'} (GEN_PVAR_63 : A -> Prop) (s : A -> Prop) : (term20 A GEN_PVAR_63 s) = (term21 A GEN_PVAR_63 s).
Proof. exact (MK_COMB (@lem3465230 A) (@lem3465229 A GEN_PVAR_63 s)). Qed.
Lemma lem3465232 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (fun_ext (fun GEN_PVAR_63 : A -> Prop => @lem3465231 A GEN_PVAR_63 s)). Qed.
Lemma lem3465233 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem3465234 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem3465233 A) (@lem3465232 A s)). Qed.
Lemma lem3465235 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3465236 {A : Type'} (s : A -> Prop) : (term8 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3465235 A) (@lem3465234 A s)). Qed.
Lemma lem3465237 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3465238 {A : Type'} (s : A -> Prop) : (term27 A s) = (term28 A s).
Proof. exact (MK_COMB (@lem3465237 A) (@lem3465236 A s)). Qed.
Lemma lem3465239 {A : Type'} (x : A) (s : A -> Prop) : (term12 A s x) = (@IN A x s).
Proof. exact (eq_refl (term12 A s x)). Qed.
Lemma lem3465240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465241 {A : Type'} (x : A) (s : A -> Prop) : (term29 A s x) = (term30 A x s).
Proof. exact (MK_COMB (@lem3465240) (@lem3465239 A x s)). Qed.
Lemma lem3465242 {A : Type'} (x : A) : (term15 A x) = (@INSERT A x (@EMPTY A)).
Proof. exact (eq_refl (term15 A x)). Qed.
Lemma lem3465243 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem3465244 {A : Type'} (a : A) (x : A) : (term31 A a x) = (term32 A a x).
Proof. exact (MK_COMB (@lem3465243 A a) (@lem3465242 A x)). Qed.
Lemma lem3465245 {A : Type'} (s : A -> Prop) (a : A) (x : A) : (term33 A s a x) = (term34 A s a x).
Proof. exact (MK_COMB (@lem3465241 A x s) (@lem3465244 A a x)). Qed.
Lemma lem3465246 {A : Type'} (s : A -> Prop) (a : A) : (term35 A s a) = (term36 A s a).
Proof. exact (fun_ext (fun x : A => @lem3465245 A s a x)). Qed.
Lemma lem3465247 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465248 {A : Type'} (s : A -> Prop) (a : A) : (term37 A s a) = (term38 A s a).
Proof. exact (MK_COMB (@lem3465247 A) (@lem3465246 A s a)). Qed.
Lemma lem3465249 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem3465250 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (a : A) : (term39 A GEN_PVAR_50 s a) = (term40 A GEN_PVAR_50 s a).
Proof. exact (MK_COMB (@lem3465249 A GEN_PVAR_50) (@lem3465248 A s a)). Qed.
Lemma lem3465251 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3465252 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (a : A) : (term41 A GEN_PVAR_50 s a) = (term42 A GEN_PVAR_50 s a).
Proof. exact (MK_COMB (@lem3465250 A GEN_PVAR_50 s a) (@lem3465251 A a)). Qed.
Lemma lem3465253 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) : (term43 A GEN_PVAR_50 s) = (term44 A GEN_PVAR_50 s).
Proof. exact (fun_ext (fun a : A => @lem3465252 A GEN_PVAR_50 s a)). Qed.
Lemma lem3465254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465255 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) : (term45 A GEN_PVAR_50 s) = (term46 A GEN_PVAR_50 s).
Proof. exact (MK_COMB (@lem3465254 A) (@lem3465253 A GEN_PVAR_50 s)). Qed.
Lemma lem3465256 {A : Type'} (s : A -> Prop) : (term47 A s) = (term48 A s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem3465255 A GEN_PVAR_50 s)). Qed.
Lemma lem3465257 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3465258 {A : Type'} (s : A -> Prop) : (term9 A s) = (term49 A s).
Proof. exact (MK_COMB (@lem3465257 A) (@lem3465256 A s)). Qed.
Lemma lem3465259 {A : Type'} (s : A -> Prop) : ((term8 A s) = (term9 A s)) = ((term26 A s) = (term49 A s)).
Proof. exact (MK_COMB (@lem3465238 A s) (@lem3465258 A s)). Qed.
Lemma lem3465260 {A : Type'} (s : A -> Prop) : (term26 A s) = (term49 A s).
Proof. exact (EQ_MP (@lem3465259 A s) (@lem3465223 A s)). Qed.
Lemma lem3465271 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3465272 {A : Type'} (s : A -> Prop) : (term28 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3465271 A) (@lem3465260 A s)). Qed.
Lemma lem3465273 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3465274 {A : Type'} (s : A -> Prop) : ((term26 A s) = s) = ((term49 A s) = s).
Proof. exact (MK_COMB (@lem3465272 A s) (@lem3465273 A s)). Qed.
Lemma lem3465277 {A : Type'} : (term51 A) = (term52 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3465274 A s)). Qed.
Lemma lem3465278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3465279 {A : Type'} : (term53 A) = (term54 A).
Proof. exact (MK_COMB (@lem3465278 A) (@lem3465277 A)). Qed.
Lemma lem3465284 {A : Type'} : (term54 A) = (term53 A).
Proof. exact (SYM (@lem3465279 A)). Qed.
Lemma lem3465292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term55 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3465293 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term55 A s t).
Proof. exact (@lem3465292 A s t). Qed.
Lemma lem3465294 {A : Type'} (s : A -> Prop) : ((term49 A s) = s) = (term56 A s).
Proof. exact (@lem3465293 A (term49 A s) s). Qed.
Lemma lem3465313 {A : Type'} : (term52 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3465294 A s)). Qed.
Lemma lem3465314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3465315 {A : Type'} : (term54 A) = (term58 A).
Proof. exact (MK_COMB (@lem3465314 A) (@lem3465313 A)). Qed.
Lemma lem3465320 {A : Type'} : (term58 A) = (term54 A).
Proof. exact (SYM (@lem3465315 A)). Qed.
Lemma lem3465332 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term59 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3465333 {A : Type'} (p : A -> Prop) (x : A) : (term59 A x p) = (p x).
Proof. exact (@lem3465332 A p x). Qed.
Lemma lem3465334 {A : Type'} (s : A -> Prop) (x : A) : (term60 A x s) = (term61 A s x).
Proof. exact (@lem3465333 A (term62 A s) x). Qed.
Lemma lem3465335 {A : Type'} (s : A -> Prop) (a : A) : (term61 A s a) = (term38 A s a).
Proof. exact (eq_refl (term61 A s a)). Qed.
Lemma lem3465336 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem3465337 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (a : A) : (term63 A GEN_PVAR_50 s a) = (term40 A GEN_PVAR_50 s a).
Proof. exact (MK_COMB (@lem3465336 A GEN_PVAR_50) (@lem3465335 A s a)). Qed.
Lemma lem3465338 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3465339 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (a : A) : (term64 A GEN_PVAR_50 s a) = (term42 A GEN_PVAR_50 s a).
Proof. exact (MK_COMB (@lem3465337 A GEN_PVAR_50 s a) (@lem3465338 A a)). Qed.
Lemma lem3465340 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) : (term65 A GEN_PVAR_50 s) = (term44 A GEN_PVAR_50 s).
Proof. exact (fun_ext (fun a : A => @lem3465339 A GEN_PVAR_50 s a)). Qed.
Lemma lem3465341 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465342 {A : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) : (term66 A GEN_PVAR_50 s) = (term46 A GEN_PVAR_50 s).
Proof. exact (MK_COMB (@lem3465341 A) (@lem3465340 A GEN_PVAR_50 s)). Qed.
Lemma lem3465343 {A : Type'} (s : A -> Prop) : (term67 A s) = (term48 A s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem3465342 A GEN_PVAR_50 s)). Qed.
Lemma lem3465344 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3465345 {A : Type'} (s : A -> Prop) : (term68 A s) = (term49 A s).
Proof. exact (MK_COMB (@lem3465344 A) (@lem3465343 A s)). Qed.
Lemma lem3465346 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3465347 {A : Type'} (x : A) (s : A -> Prop) : (term60 A x s) = (term69 A x s).
Proof. exact (MK_COMB (@lem3465346 A x) (@lem3465345 A s)). Qed.
Lemma lem3465348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465349 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem3465348) (@lem3465347 A x s)). Qed.
Lemma lem3465350 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term38 A s x).
Proof. exact (eq_refl (term61 A s x)). Qed.
Lemma lem3465351 {A : Type'} (s : A -> Prop) (x : A) : ((term60 A x s) = (term61 A s x)) = ((term69 A x s) = (term38 A s x)).
Proof. exact (MK_COMB (@lem3465349 A x s) (@lem3465350 A s x)). Qed.
Lemma lem3465352 {A : Type'} (s : A -> Prop) (x : A) : (term69 A x s) = (term38 A s x).
Proof. exact (EQ_MP (@lem3465351 A s x) (@lem3465334 A s x)). Qed.
Lemma lem3465360 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3465361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3465360 A P x). Qed.
Lemma lem3465362 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3465361 A s x'). Qed.
Lemma lem3465363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465364 {A : Type'} (s : A -> Prop) (x' : A) : (term30 A x' s) = (term72 A s x').
Proof. exact (MK_COMB (@lem3465363) (@lem3465362 A s x')). Qed.
Lemma lem3465366 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term73 A x y s) = (term74 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3465367 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term73 A x y s) = (term74 A y x s).
Proof. exact (@lem3465366 A y x s). Qed.
Lemma lem3465368 {A : Type'} (x' : A) (x : A) : (term32 A x x') = (term75 A x' x).
Proof. exact (@lem3465367 A x' x (@EMPTY A)). Qed.
Lemma lem3465374 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3465375 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3465374 A x). Qed.
Lemma lem3465376 {A : Type'} (x : A) (x' : A) : (term76 A x x') = (term76 A x x').
Proof. exact (eq_refl (term76 A x x')). Qed.
Lemma lem3465377 {A : Type'} (x : A) (x' : A) : (term75 A x' x) = (term77 A x x').
Proof. exact (MK_COMB (@lem3465376 A x x') (@lem3465375 A x)). Qed.
Lemma lem3465379 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3465380 {A : Type'} (x : A) (x' : A) : (term77 A x x') = (x = x').
Proof. exact (@lem3465379 (x = x')). Qed.
Lemma lem3465383 {A : Type'} (x : A) (x' : A) : (term75 A x' x) = (x = x').
Proof. exact (TRANS (@lem3465377 A x x') (@lem3465380 A x x')). Qed.
Lemma lem3465384 {A : Type'} (x : A) (x' : A) : (term32 A x x') = (x = x').
Proof. exact (TRANS (@lem3465368 A x' x) (@lem3465383 A x x')). Qed.
Lemma lem3465385 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term34 A s x x') = (term78 A s x x').
Proof. exact (MK_COMB (@lem3465364 A s x') (@lem3465384 A x x')). Qed.
Lemma lem3465388 {A : Type'} (s : A -> Prop) (x : A) : (term36 A s x) = (term79 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465385 A s x x')). Qed.
Lemma lem3465389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465390 {A : Type'} (s : A -> Prop) (x : A) : (term38 A s x) = (term80 A s x).
Proof. exact (MK_COMB (@lem3465389 A) (@lem3465388 A s x)). Qed.
Lemma lem3465395 {A : Type'} (s : A -> Prop) (x : A) : (term69 A x s) = (term80 A s x).
Proof. exact (TRANS (@lem3465352 A s x) (@lem3465390 A s x)). Qed.
Lemma lem3465396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465397 {A : Type'} (s : A -> Prop) (x : A) : (term71 A x s) = (term81 A s x).
Proof. exact (MK_COMB (@lem3465396) (@lem3465395 A s x)). Qed.
Lemma lem3465399 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3465400 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3465399 A P x). Qed.
Lemma lem3465401 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3465400 A s x). Qed.
Lemma lem3465402 {A : Type'} (s : A -> Prop) (x : A) : ((term69 A x s) = (@IN A x s)) = ((term80 A s x) = (s x)).
Proof. exact (MK_COMB (@lem3465397 A s x) (@lem3465401 A s x)). Qed.
Lemma lem3465405 {A : Type'} (s : A -> Prop) : (term82 A s) = (term83 A s).
Proof. exact (fun_ext (fun x : A => @lem3465402 A s x)). Qed.
Lemma lem3465406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465407 {A : Type'} (s : A -> Prop) : (term56 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem3465406 A) (@lem3465405 A s)). Qed.
Lemma lem3465412 {A : Type'} : (term57 A) = (term85 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3465407 A s)). Qed.
Lemma lem3465413 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3465414 {A : Type'} : (term58 A) = (term86 A).
Proof. exact (MK_COMB (@lem3465413 A) (@lem3465412 A)). Qed.
Lemma lem3465419 {A : Type'} : (term86 A) = (term58 A).
Proof. exact (SYM (@lem3465414 A)). Qed.
Lemma lem3465421 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3465422 {A : Type'} : (term86 A) = (term88 A).
Proof. exact (@lem3465421 (term86 A)). Qed.
Lemma lem3465423 {A : Type'} : (term88 A) = (term86 A).
Proof. exact (SYM (@lem3465422 A)). Qed.
Lemma lem3465424 {A : Type'} (h1 : term89 A) : term89 A.
Proof. exact (h1). Qed.
Lemma lem3465427 {A : Type'} (h1 : term88 A) : term88 A.
Proof. exact (h1). Qed.
Lemma lem3465428 {A : Type'} : term90 A.
Proof. exact (fun h0 : term88 A => @lem3465427 A h0). Qed.
Lemma lem3465429 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (h1). Qed.
Lemma lem3465430 {A : Type'} (h1 : term88 A) : term88 A.
Proof. exact (h1). Qed.
Lemma lem3465431 {A : Type'} (h1 : term88 A) (h2 : term90 A) : term88 A.
Proof. exact (@lem3465429 A h2 (@lem3465430 A h1)). Qed.
Lemma lem3465432 {A : Type'} (h1 : term88 A) : term91 A.
Proof. exact (fun h0 : term90 A => @lem3465431 A h1 h0). Qed.
Lemma lem3465433 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (h1). Qed.
Lemma lem3465434 {A : Type'} (h1 : term88 A) (h2 : term90 A) : term88 A.
Proof. exact (@lem3465432 A h1 (@lem3465433 A h2)). Qed.
Lemma lem3465435 {A : Type'} (h1 : term90 A) : term90 A.
Proof. exact (fun h0 : term88 A => @lem3465434 A h0 h1). Qed.
Lemma lem3465436 {A : Type'} : term92 A.
Proof. exact (fun h0 : term90 A => @lem3465435 A h0). Qed.
Lemma lem3465439 {A : Type'} : term90 A.
Proof. exact (@lem3465436 A (@lem3465428 A)). Qed.
Lemma lem3465440 {A : Type'} : term90 A.
Proof. exact (@lem3465439 A). Qed.
Lemma lem3465442 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3465443 {A : Type'} : (term88 A) = (term93 A).
Proof. exact (@lem3465442 (term89 A)). Qed.
Lemma lem3465445 (t : Prop) : (term94 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3465446 {A : Type'} : (term93 A) = (term86 A).
Proof. exact (@lem3465445 (term86 A)). Qed.
Lemma lem3465489 {A : Type'} : (term88 A) = (term86 A).
Proof. exact (TRANS (@lem3465443 A) (@lem3465446 A)). Qed.
Lemma lem3465490 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3465495 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term78 A s x x') = (term78 A s x x').
Proof. exact (eq_refl (term78 A s x x')). Qed.
Lemma lem3465496 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term79 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465495 A s x x')). Qed.
Lemma lem3465497 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465498 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (term80 A s x).
Proof. exact (MK_COMB (@lem3465497 A) (@lem3465496 A s x)). Qed.
Lemma lem3465499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465500 {A : Type'} (s : A -> Prop) (x : A) : (term81 A s x) = (term81 A s x).
Proof. exact (MK_COMB (@lem3465499) (@lem3465498 A s x)). Qed.
Lemma lem3465501 {A : Type'} (s : A -> Prop) (x : A) : ((term80 A s x) = (s x)) = ((term80 A s x) = (s x)).
Proof. exact (MK_COMB (@lem3465500 A s x) (@lem3465490 A s x)). Qed.
Lemma lem3465502 {A : Type'} (s : A -> Prop) : (term83 A s) = (term83 A s).
Proof. exact (fun_ext (fun x : A => @lem3465501 A s x)). Qed.
Lemma lem3465503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465504 {A : Type'} (s : A -> Prop) : (term84 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem3465503 A) (@lem3465502 A s)). Qed.
Lemma lem3465505 {A : Type'} : (term85 A) = (term85 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3465504 A s)). Qed.
Lemma lem3465506 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3465507 {A : Type'} : (term86 A) = (term86 A).
Proof. exact (MK_COMB (@lem3465506 A) (@lem3465505 A)). Qed.
Lemma lem3465530 {A : Type'} : (term88 A) = (term86 A).
Proof. exact (TRANS (@lem3465489 A) (@lem3465507 A)). Qed.
Lemma lem3465531 {A : Type'} : (term86 A) = (term88 A).
Proof. exact (SYM (@lem3465530 A)). Qed.
Lemma lem3465533 (p : Prop) : p = (term87 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3465534 {A : Type'} (s : A -> Prop) (x : A) : ((term80 A s x) = (s x)) = (term95 A s x).
Proof. exact (@lem3465533 ((term80 A s x) = (s x))). Qed.
Lemma lem3465535 {A : Type'} (s : A -> Prop) (x : A) : (term95 A s x) = ((term80 A s x) = (s x)).
Proof. exact (SYM (@lem3465534 A s x)). Qed.
Lemma lem3465536 {A : Type'} (s : A -> Prop) (x : A) (h1 : term96 A s x) : term96 A s x.
Proof. exact (h1). Qed.
Lemma lem3465545 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term97 A s x x') = (term98 A s x x').
Proof. exact (@lem17045 (s x') (x = x')). Qed.
Lemma lem3465548 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term78 A s x x') = (term78 A s x x').
Proof. exact (eq_refl (term78 A s x x')). Qed.
Lemma lem3465549 {A : Type'} (P : A -> Prop) : (term99 A P) = (term100 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3465550 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term102 A s x).
Proof. exact (@lem3465549 A (term79 A s x)). Qed.
Lemma lem3465551 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term103 A s x x') = (term78 A s x x').
Proof. exact (eq_refl (term103 A s x x')). Qed.
Lemma lem3465552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3465553 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term104 A s x x') = (term97 A s x x').
Proof. exact (MK_COMB (@lem3465552) (@lem3465551 A s x x')). Qed.
Lemma lem3465554 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term104 A s x x') = (term98 A s x x').
Proof. exact (TRANS (@lem3465553 A s x x') (@lem3465545 A s x x')). Qed.
Lemma lem3465555 {A : Type'} (s : A -> Prop) (x : A) : (term105 A s x) = (term106 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465554 A s x x')). Qed.
Lemma lem3465556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465557 {A : Type'} (s : A -> Prop) (x : A) : (term102 A s x) = (term107 A s x).
Proof. exact (MK_COMB (@lem3465556 A) (@lem3465555 A s x)). Qed.
Lemma lem3465558 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term107 A s x).
Proof. exact (TRANS (@lem3465550 A s x) (@lem3465557 A s x)). Qed.
Lemma lem3465559 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term79 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465548 A s x x')). Qed.
Lemma lem3465560 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465561 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (term80 A s x).
Proof. exact (MK_COMB (@lem3465560 A) (@lem3465559 A s x)). Qed.
Lemma lem3465562 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3465563 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3465564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465565 {A : Type'} (s : A -> Prop) (x : A) : (term109 A s x) = (term110 A s x).
Proof. exact (MK_COMB (@lem3465564) (@lem3465558 A s x)). Qed.
Lemma lem3465566 {A : Type'} (s : A -> Prop) (x : A) : (term111 A s x) = (term112 A s x).
Proof. exact (MK_COMB (@lem3465565 A s x) (@lem3465563 A s x)). Qed.
Lemma lem3465567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465568 {A : Type'} (s : A -> Prop) (x : A) : (term113 A s x) = (term113 A s x).
Proof. exact (MK_COMB (@lem3465567) (@lem3465561 A s x)). Qed.
Lemma lem3465569 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term114 A s x).
Proof. exact (MK_COMB (@lem3465568 A s x) (@lem3465562 A s x)). Qed.
Lemma lem3465570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3465571 {A : Type'} (s : A -> Prop) (x : A) : (term115 A s x) = (term115 A s x).
Proof. exact (MK_COMB (@lem3465570) (@lem3465569 A s x)). Qed.
Lemma lem3465572 {A : Type'} (s : A -> Prop) (x : A) : (term116 A s x) = (term117 A s x).
Proof. exact (MK_COMB (@lem3465571 A s x) (@lem3465566 A s x)). Qed.
Lemma lem3465573 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term116 A s x).
Proof. exact (@lem17646 (term80 A s x) (s x)). Qed.
Lemma lem3465574 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term117 A s x).
Proof. exact (TRANS (@lem3465573 A s x) (@lem3465572 A s x)). Qed.
Lemma lem3465653 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3465654 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (@lem3465653 A P Q). Qed.
Lemma lem3465655 {A : Type'} (s : A -> Prop) (x : A) : (term120 A s x) = (term121 A s x).
Proof. exact (@lem3465654 A (term79 A s x) (term108 A s x)). Qed.
Lemma lem3465656 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term103 A s x x') = (term78 A s x x').
Proof. exact (eq_refl (term103 A s x x')). Qed.
Lemma lem3465657 {A : Type'} (s : A -> Prop) (x : A) : (term122 A s x) = (term79 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465656 A s x x')). Qed.
Lemma lem3465658 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465659 {A : Type'} (s : A -> Prop) (x : A) : (term123 A s x) = (term80 A s x).
Proof. exact (MK_COMB (@lem3465658 A) (@lem3465657 A s x)). Qed.
Lemma lem3465660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465661 {A : Type'} (s : A -> Prop) (x : A) : (term124 A s x) = (term113 A s x).
Proof. exact (MK_COMB (@lem3465660) (@lem3465659 A s x)). Qed.
Lemma lem3465662 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3465663 {A : Type'} (s : A -> Prop) (x : A) : (term120 A s x) = (term114 A s x).
Proof. exact (MK_COMB (@lem3465661 A s x) (@lem3465662 A s x)). Qed.
Lemma lem3465664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465665 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term126 A s x).
Proof. exact (MK_COMB (@lem3465664) (@lem3465663 A s x)). Qed.
Lemma lem3465666 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term103 A s x x') = (term78 A s x x').
Proof. exact (eq_refl (term103 A s x x')). Qed.
Lemma lem3465667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465668 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term127 A s x x') = (term128 A s x x').
Proof. exact (MK_COMB (@lem3465667) (@lem3465666 A s x x')). Qed.
Lemma lem3465669 {A : Type'} (s : A -> Prop) (x : A) : (term108 A s x) = (term108 A s x).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem3465670 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term129 A x' s x) = (term130 A x' s x).
Proof. exact (MK_COMB (@lem3465668 A s x x') (@lem3465669 A s x)). Qed.
Lemma lem3465671 {A : Type'} (s : A -> Prop) (x : A) : (term131 A s x) = (term132 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465670 A x' s x)). Qed.
Lemma lem3465672 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465673 {A : Type'} (s : A -> Prop) (x : A) : (term121 A s x) = (term133 A s x).
Proof. exact (MK_COMB (@lem3465672 A) (@lem3465671 A s x)). Qed.
Lemma lem3465674 {A : Type'} (s : A -> Prop) (x : A) : ((term120 A s x) = (term121 A s x)) = ((term114 A s x) = (term133 A s x)).
Proof. exact (MK_COMB (@lem3465665 A s x) (@lem3465673 A s x)). Qed.
Lemma lem3465675 {A : Type'} (s : A -> Prop) (x : A) : (term114 A s x) = (term133 A s x).
Proof. exact (EQ_MP (@lem3465674 A s x) (@lem3465655 A s x)). Qed.
Lemma lem3465676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3465677 {A : Type'} (s : A -> Prop) (x : A) : (term115 A s x) = (term134 A s x).
Proof. exact (MK_COMB (@lem3465676) (@lem3465675 A s x)). Qed.
Lemma lem3465678 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem3465679 {A : Type'} (s : A -> Prop) (x : A) : (term117 A s x) = (term135 A s x).
Proof. exact (MK_COMB (@lem3465677 A s x) (@lem3465678 A s x)). Qed.
Lemma lem3465681 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3465682 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem3465681 A P Q). Qed.
Lemma lem3465683 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (term139 A s x).
Proof. exact (@lem3465682 A (term132 A s x) (term112 A s x)). Qed.
Lemma lem3465684 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term140 A s x x') = (term130 A x' s x).
Proof. exact (eq_refl (term140 A s x x')). Qed.
Lemma lem3465685 {A : Type'} (s : A -> Prop) (x : A) : (term141 A s x) = (term132 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465684 A x' s x)). Qed.
Lemma lem3465686 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465687 {A : Type'} (s : A -> Prop) (x : A) : (term142 A s x) = (term133 A s x).
Proof. exact (MK_COMB (@lem3465686 A) (@lem3465685 A s x)). Qed.
Lemma lem3465688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3465689 {A : Type'} (s : A -> Prop) (x : A) : (term143 A s x) = (term134 A s x).
Proof. exact (MK_COMB (@lem3465688) (@lem3465687 A s x)). Qed.
Lemma lem3465690 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem3465691 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (term135 A s x).
Proof. exact (MK_COMB (@lem3465689 A s x) (@lem3465690 A s x)). Qed.
Lemma lem3465692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465693 {A : Type'} (s : A -> Prop) (x : A) : (term144 A s x) = (term145 A s x).
Proof. exact (MK_COMB (@lem3465692) (@lem3465691 A s x)). Qed.
Lemma lem3465694 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term140 A s x x') = (term130 A x' s x).
Proof. exact (eq_refl (term140 A s x x')). Qed.
Lemma lem3465695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3465696 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term146 A s x x') = (term147 A x' s x).
Proof. exact (MK_COMB (@lem3465695) (@lem3465694 A x' s x)). Qed.
Lemma lem3465697 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (eq_refl (term112 A s x)). Qed.
Lemma lem3465698 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term148 A x' s x) = (term149 A x' s x).
Proof. exact (MK_COMB (@lem3465696 A x' s x) (@lem3465697 A s x)). Qed.
Lemma lem3465699 {A : Type'} (s : A -> Prop) (x : A) : (term150 A s x) = (term151 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465698 A x' s x)). Qed.
Lemma lem3465700 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3465701 {A : Type'} (s : A -> Prop) (x : A) : (term139 A s x) = (term152 A s x).
Proof. exact (MK_COMB (@lem3465700 A) (@lem3465699 A s x)). Qed.
Lemma lem3465702 {A : Type'} (s : A -> Prop) (x : A) : ((term138 A s x) = (term139 A s x)) = ((term135 A s x) = (term152 A s x)).
Proof. exact (MK_COMB (@lem3465693 A s x) (@lem3465701 A s x)). Qed.
Lemma lem3465703 {A : Type'} (s : A -> Prop) (x : A) : (term135 A s x) = (term152 A s x).
Proof. exact (EQ_MP (@lem3465702 A s x) (@lem3465683 A s x)). Qed.
Lemma lem3465705 {A : Type'} (s : A -> Prop) (x : A) : (term117 A s x) = (term152 A s x).
Proof. exact (TRANS (@lem3465679 A s x) (@lem3465703 A s x)). Qed.
Lemma lem3465706 {A : Type'} (s : A -> Prop) (x : A) : (term96 A s x) = (term152 A s x).
Proof. exact (TRANS (@lem3465574 A s x) (@lem3465705 A s x)). Qed.
Lemma lem3465707 {A : Type'} (s : A -> Prop) (x : A) (h1 : term96 A s x) : term152 A s x.
Proof. exact (EQ_MP (@lem3465706 A s x) (@lem3465536 A s x h1)). Qed.
Lemma lem3465708 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term149 A x' s x) : term149 A x' s x.
Proof. exact (h1). Qed.
Lemma lem3465711 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3465726 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term98 A s x x') = (term98 A s x x').
Proof. exact (eq_refl (term98 A s x x')). Qed.
Lemma lem3465727 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465726 A s x x')). Qed.
Lemma lem3465728 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465729 {A : Type'} (s : A -> Prop) (x : A) : (term107 A s x) = (term107 A s x).
Proof. exact (MK_COMB (@lem3465728 A) (@lem3465727 A s x)). Qed.
Lemma lem3465730 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3465731 {A : Type'} (s : A -> Prop) (x : A) : (term110 A s x) = (term110 A s x).
Proof. exact (MK_COMB (@lem3465730) (@lem3465729 A s x)). Qed.
Lemma lem3465732 {A : Type'} (s : A -> Prop) (x : A) : (term112 A s x) = (term112 A s x).
Proof. exact (MK_COMB (@lem3465731 A s x) (@lem3465711 A s x)). Qed.
Lemma lem3465753 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term147 A x' s x) = (term147 A x' s x).
Proof. exact (eq_refl (term147 A x' s x)). Qed.
Lemma lem3465754 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term149 A x' s x) = (term149 A x' s x).
Proof. exact (MK_COMB (@lem3465753 A x' s x) (@lem3465732 A s x)). Qed.
Lemma lem3465755 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term149 A x' s x) : term149 A x' s x.
Proof. exact (EQ_MP (@lem3465754 A x' s x) (@lem3465708 A x' s x h1)). Qed.
Lemma lem3465756 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term130 A x' s x.
Proof. exact (h1). Qed.
Lemma lem3465757 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term112 A s x.
Proof. exact (h1). Qed.
Lemma lem3465759 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term78 A s x x'.
Proof. exact (proj1 (@lem3465756 A x' s x h1)). Qed.
Lemma lem3465763 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term107 A s x.
Proof. exact (proj1 (@lem3465757 A s x h1)). Qed.
Lemma lem3465783 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term98 A s x x') = (term98 A s x x').
Proof. exact (eq_refl (term98 A s x x')). Qed.
Lemma lem3465784 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term106 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3465783 A s x x')). Qed.
Lemma lem3465785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3465787 {A : Type'} (s : A -> Prop) (x : A) : (term107 A s x) = (term107 A s x).
Proof. exact (MK_COMB (@lem3465785 A) (@lem3465784 A s x)). Qed.
Lemma lem3465788 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term107 A s x.
Proof. exact (EQ_MP (@lem3465787 A s x) (@lem3465763 A s x h1)). Qed.
Lemma lem3465793 {A : Type'} (_36604 : A) (s : A -> Prop) (x : A) (h1 : term112 A s x) : term153 A s x _36604.
Proof. exact (@lem3465788 A s x h1 _36604). Qed.
Lemma lem3465794 {A : Type'} (s : A -> Prop) (x : A) (_36604 : A) : (term153 A s x _36604) = (term98 A s x _36604).
Proof. exact (eq_refl (term153 A s x _36604)). Qed.
Lemma lem3465797 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term108 A s x.
Proof. exact (proj2 (@lem3465756 A x' s x h1)). Qed.
Lemma lem3465801 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : x = x'.
Proof. exact (proj2 (@lem3465759 A x' s x h1)). Qed.
Lemma lem3465807 {A : Type'} (_36604 : A) (s : A -> Prop) (x : A) (h1 : term112 A s x) : term98 A s x _36604.
Proof. exact (EQ_MP (@lem3465794 A s x _36604) (@lem3465793 A _36604 s x h1)). Qed.
Lemma lem3465824 {A : Type'} (s : A -> Prop) : (term154 A s) = (term154 A s).
Proof. exact (eq_refl (term154 A s)). Qed.
Lemma lem3465825 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : (term155 A s x) = (term155 A s x').
Proof. exact (MK_COMB (@lem3465824 A s) (@lem3465801 A x' s x h1)). Qed.
Lemma lem3465826 {A : Type'} (s : A -> Prop) (x' : A) : (term155 A s x') = (term108 A s x').
Proof. exact (eq_refl (term155 A s x')). Qed.
Lemma lem3465827 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (term156 A s x).
Proof. exact (eq_refl (term156 A s x)). Qed.
Lemma lem3465828 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term155 A s x) = (term155 A s x')) = ((term155 A s x) = (term108 A s x')).
Proof. exact (MK_COMB (@lem3465827 A s x) (@lem3465826 A s x')). Qed.
Lemma lem3465829 {A : Type'} (s : A -> Prop) (x : A) : (term155 A s x) = (term108 A s x).
Proof. exact (eq_refl (term155 A s x)). Qed.
Lemma lem3465830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3465831 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (term157 A s x).
Proof. exact (MK_COMB (@lem3465830) (@lem3465829 A s x)). Qed.
Lemma lem3465832 {A : Type'} (s : A -> Prop) (x' : A) : (term108 A s x') = (term108 A s x').
Proof. exact (eq_refl (term108 A s x')). Qed.
Lemma lem3465833 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term155 A s x) = (term108 A s x')) = ((term108 A s x) = (term108 A s x')).
Proof. exact (MK_COMB (@lem3465831 A s x) (@lem3465832 A s x')). Qed.
Lemma lem3465834 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term155 A s x) = (term155 A s x')) = ((term108 A s x) = (term108 A s x')).
Proof. exact (TRANS (@lem3465828 A x s x') (@lem3465833 A x s x')). Qed.
Lemma lem3465835 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : (term108 A s x) = (term108 A s x').
Proof. exact (EQ_MP (@lem3465834 A x s x') (@lem3465825 A x' s x h1)). Qed.
Lemma lem3465836 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term108 A s x'.
Proof. exact (EQ_MP (@lem3465835 A x' s x h1) (@lem3465797 A x' s x h1)). Qed.
Lemma lem3465852 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : s x'.
Proof. exact (proj1 (@lem3465759 A x' s x h1)). Qed.
Lemma lem3465853 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term158 A s x'.
Proof. exact (fun h0 : term108 A s x' => @lem3465852 A x' s x h1). Qed.
Lemma lem3465855 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465856 {A : Type'} (s : A -> Prop) (x' : A) : (term158 A s x') = (s x').
Proof. exact (@lem3465855 (s x')). Qed.
Lemma lem3465857 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : s x'.
Proof. exact (EQ_MP (@lem3465856 A s x') (@lem3465853 A x' s x h1)). Qed.
Lemma lem3465860 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3465862 {A : Type'} (s : A -> Prop) (x' : A) : (term108 A s x') = (term160 A s x').
Proof. exact (@lem3465860 (s x')). Qed.
Lemma lem3465865 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term160 A s x'.
Proof. exact (EQ_MP (@lem3465862 A s x') (@lem3465836 A x' s x h1)). Qed.
Lemma lem3465868 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : False.
Proof. exact (@lem3465865 A x' s x h1 (@lem3465857 A x' s x h1)). Qed.
Lemma lem3465869 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : term161.
Proof. exact (fun h0 : ~ False => @lem3465868 A x' s x h1). Qed.
Lemma lem3465871 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465872 : term161 = False.
Proof. exact (@lem3465871 False). Qed.
Lemma lem3465889 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : s x.
Proof. exact (proj2 (@lem3465757 A s x h1)). Qed.
Lemma lem3465890 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term158 A s x.
Proof. exact (fun h0 : term108 A s x => @lem3465889 A s x h1). Qed.
Lemma lem3465892 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465893 {A : Type'} (s : A -> Prop) (x : A) : (term158 A s x) = (s x).
Proof. exact (@lem3465892 (s x)). Qed.
Lemma lem3465894 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : s x.
Proof. exact (EQ_MP (@lem3465893 A s x) (@lem3465890 A s x h1)). Qed.
Lemma lem3465896 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3465897 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3465896 A x). Qed.
Lemma lem3465898 {A : Type'} (x : A) : term162 A x.
Proof. exact (fun h0 : term163 A x => @lem3465897 A x). Qed.
Lemma lem3465900 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465901 {A : Type'} (x : A) : (term162 A x) = (x = x).
Proof. exact (@lem3465900 (x = x)). Qed.
Lemma lem3465902 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3465901 A x) (@lem3465898 A x)). Qed.
Lemma lem3465904 (a : Prop) (b : Prop) : (term164 a b) = (term165 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3465905 {A : Type'} (s : A -> Prop) (x : A) (_36604 : A) : (term98 A s x _36604) = (term97 A s x _36604).
Proof. exact (@lem3465904 (s _36604) (x = _36604)). Qed.
Lemma lem3465907 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3465908 {A : Type'} (s : A -> Prop) (x : A) (_36604 : A) : (term97 A s x _36604) = (term166 A s x _36604).
Proof. exact (@lem3465907 (term78 A s x _36604)). Qed.
Lemma lem3465909 {A : Type'} (s : A -> Prop) (x : A) (_36604 : A) : (term98 A s x _36604) = (term166 A s x _36604).
Proof. exact (TRANS (@lem3465905 A s x _36604) (@lem3465908 A s x _36604)). Qed.
Lemma lem3465911 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term167 A s x.
Proof. exact (conj (@lem3465894 A s x h1) (@lem3465902 A x)). Qed.
Lemma lem3465913 {A : Type'} (_36604 : A) (s : A -> Prop) (x : A) (h1 : term112 A s x) : term166 A s x _36604.
Proof. exact (EQ_MP (@lem3465909 A s x _36604) (@lem3465807 A _36604 s x h1)). Qed.
Lemma lem3465914 {A : Type'} (_36604 : A) (s : A -> Prop) (x : A) (h1 : term112 A s x) : term166 A s x _36604.
Proof. exact (@lem3465913 A _36604 s x h1). Qed.
Lemma lem3465915 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term168 A s x.
Proof. exact (@lem3465914 A x s x h1). Qed.
Lemma lem3465918 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : False.
Proof. exact (@lem3465915 A s x h1 (@lem3465911 A s x h1)). Qed.
Lemma lem3465919 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : term161.
Proof. exact (fun h0 : ~ False => @lem3465918 A s x h1). Qed.
Lemma lem3465921 (p : Prop) : (term159 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3465922 : term161 = False.
Proof. exact (@lem3465921 False). Qed.
Lemma lem3465923 {A : Type'} (s : A -> Prop) (x : A) (h1 : term112 A s x) : False.
Proof. exact (EQ_MP (@lem3465922) (@lem3465919 A s x h1)). Qed.
Lemma lem3465924 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term130 A x' s x) : False.
Proof. exact (EQ_MP (@lem3465872) (@lem3465869 A x' s x h1)). Qed.
Lemma lem3465925 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term149 A x' s x) : False.
Proof. exact (or_elim (@lem3465755 A x' s x h1) (fun h0 : term130 A x' s x => @lem3465924 A x' s x h0) (fun h0 : term112 A s x => @lem3465923 A s x h0)). Qed.
Lemma lem3465926 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term149 A x' s x) : (term149 A x' s x) = False.
Proof. exact (prop_ext (fun h2 : term149 A x' s x => @lem3465925 A x' s x h1) (fun h2 : False => @lem3465755 A x' s x h1)). Qed.
Lemma lem3465927 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term149 A x' s x) : False.
Proof. exact (EQ_MP (@lem3465926 A x' s x h1) (@lem3465755 A x' s x h1)). Qed.
Lemma lem3465928 {A : Type'} (s : A -> Prop) (x : A) (h1 : term96 A s x) : False.
Proof. exact (ex_elim (@lem3465707 A s x h1) (fun x' : A => fun h0 : term151 A s x x' => @lem3465927 A x' s x h0)). Qed.
Lemma lem3465929 {A : Type'} (s : A -> Prop) (x : A) (h1 : term96 A s x) : (term96 A s x) = False.
Proof. exact (prop_ext (fun h2 : term96 A s x => @lem3465928 A s x h1) (fun h2 : False => @lem3465536 A s x h1)). Qed.
Lemma lem3465930 {A : Type'} (s : A -> Prop) (x : A) (h1 : term96 A s x) : False.
Proof. exact (EQ_MP (@lem3465929 A s x h1) (@lem3465536 A s x h1)). Qed.
Lemma lem3465931 {A : Type'} (s : A -> Prop) (x : A) : term95 A s x.
Proof. exact (fun h0 : term96 A s x => @lem3465930 A s x h0). Qed.
Lemma lem3465932 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (EQ_MP (@lem3465535 A s x) (@lem3465931 A s x)). Qed.
Lemma lem3465937 {A : Type'} (s : A -> Prop) : term84 A s.
Proof. exact (fun x : A => @lem3465932 A s x). Qed.
Lemma lem3465942 {A : Type'} : term86 A.
Proof. exact (fun s : A -> Prop => @lem3465937 A s). Qed.
Lemma lem3465943 {A : Type'} : term88 A.
Proof. exact (EQ_MP (@lem3465531 A) (@lem3465942 A)). Qed.
Lemma lem3465945 {A : Type'} : term88 A.
Proof. exact (@lem3465440 A (@lem3465943 A)). Qed.
Lemma lem3465946 {A : Type'} (h1 : term89 A) : False.
Proof. exact (@lem3465945 A (@lem3465424 A h1)). Qed.
Lemma lem3465947 {A : Type'} (h1 : term89 A) : (term89 A) = False.
Proof. exact (prop_ext (fun h2 : term89 A => @lem3465946 A h1) (fun h2 : False => @lem3465424 A h1)). Qed.
Lemma lem3465948 {A : Type'} (h1 : term89 A) : False.
Proof. exact (EQ_MP (@lem3465947 A h1) (@lem3465424 A h1)). Qed.
Lemma lem3465949 {A : Type'} : term88 A.
Proof. exact (fun h0 : term89 A => @lem3465948 A h0). Qed.
Lemma lem3465950 {A : Type'} : term86 A.
Proof. exact (EQ_MP (@lem3465423 A) (@lem3465949 A)). Qed.
Lemma lem3465951 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem3465419 A) (@lem3465950 A)). Qed.
Lemma lem3465952 {A : Type'} : term54 A.
Proof. exact (EQ_MP (@lem3465320 A) (@lem3465951 A)). Qed.
Lemma lem3465953 {A : Type'} : term53 A.
Proof. exact (EQ_MP (@lem3465284 A) (@lem3465952 A)). Qed.
